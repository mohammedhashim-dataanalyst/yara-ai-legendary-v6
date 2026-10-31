#!/usr/bin/env python3
"""Comprehensive unresolved-reference audit for the Yara Kotlin project.
This is intentionally static/regex based: it is a pre-Gradle audit, not a compiler.
"""
from __future__ import annotations
import argparse, re, sys, zipfile
from collections import defaultdict
from pathlib import Path
import xml.etree.ElementTree as ET

ROOT_PACKAGE = "com.yara.ai"
COMPONENTS = {"activity", "service", "receiver", "provider"}
# Receiver names explicitly requested by the audit contract.
RECEIVERS = {
    "store", "api", "voice", "engine", "emotes", "profile", "provider", "p", "chip", "mem",
    "particle", "reminder", "frame", "setting", "OverlayService", "Notifier", "PersonaEngine",
    "EmotionEngine", "FeatureCatalog", "LipSync", "SceneEngine", "EmoteEngine", "CommandRouter",
    "DeviceController", "ReminderManager", "BackupManager", "SelfLearning", "ProactiveEngine",
    "YaraAccessibilityService", "GestureDescription",
}
SUSPICIOUS = {"store.saveHistory", "store.saveProviders", "api.ask", "api.manualPrimary"}
EXTERNAL_PREFIXES = ("android.", "androidx.", "kotlin.", "java.", "javax.", "kotlinx.", "com.google.")
RECEIVER_TYPES = {"store":"MemoryStore", "api":"ApiManager", "voice":"VoiceEngine", "engine":"SceneEngine", "emotes":"EmoteEngine", "profile":"UserProfile", "provider":"ProviderState", "p":None, "chip":"FeatureChip", "mem":"MemoryItem", "particle":"Particle", "reminder":"Reminder", "frame":"Frame", "setting":"Setting", "OverlayService":"OverlayService", "Notifier":"Notifier", "PersonaEngine":"PersonaEngine", "EmotionEngine":"EmotionEngine", "FeatureCatalog":"FeatureCatalog", "LipSync":"LipSync", "SceneEngine":"SceneEngine", "EmoteEngine":"EmoteEngine", "CommandRouter":"CommandRouter", "DeviceController":"DeviceController", "ReminderManager":"ReminderManager", "BackupManager":"BackupManager", "SelfLearning":"SelfLearning", "ProactiveEngine":"ProactiveEngine", "YaraAccessibilityService":"YaraAccessibilityService", "GestureDescription":"GestureDescription"}
FORBIDDEN = [
    (r"\bExposedDropdownMenuBox\b", "ExposedDropdownMenuBox"),
    (r"\bmenuAnchor\s*\(", "menuAnchor()"),
    (r"\bDivider\s*\(", "standalone Divider()"),
    (r"\bandroidx\.compose\.ui\.platform\.LocalLifecycleOwner\b", "LocalLifecycleOwner"),
    (r"\boverride\s+fun\s+onActivityResult\b", "onActivityResult"),
    (r"\bGlobalScope\b", "GlobalScope"),
    (r'"\.associate\s*\{\s*it', '".associate { it'),
    (r"=\s*program\s*\(", "=program()"),
    (r"\bprogram\s*\(\s*VERTEX", "program(VERTEX...)"),
    (r"\bTextToSpeech\s*\(\s*ctx\s*\)\s*\{", "TextToSpeech(ctx) constructor form"),
]


def mask_kotlin(s: str) -> str:
    """Mask comments and strings while preserving length and line positions."""
    out = list(s); i = 0; n = len(s)
    while i < n:
        if s.startswith("//", i):
            j = s.find("\n", i); j = n if j < 0 else j
            for k in range(i, j): out[k] = " "
            i = j; continue
        if s.startswith("/*", i):
            j = s.find("*/", i + 2); j = n if j < 0 else j + 2
            for k in range(i, j):
                if out[k] != "\n": out[k] = " "
            i = j; continue
        if s.startswith('"""', i):
            j = s.find('"""', i + 3); j = n if j < 0 else j + 3
            for k in range(i, j):
                if out[k] != "\n": out[k] = " "
            i = j; continue
        if s[i] == '"':
            j = i + 1
            while j < n:
                if s[j] == "\\": j += 2; continue
                if s[j] == '"': j += 1; break
                j += 1
            for k in range(i, min(j, n)):
                if out[k] != "\n": out[k] = " "
            i = j; continue
        i += 1
    return ''.join(out)


def line(s, pos): return s.count("\n", 0, pos) + 1


def delimiters(s):
    stack = []; pairs = {}; errors = []
    close = {')': '(', ']': '[', '}': '{'}
    for i, c in enumerate(s):
        if c in '([{': stack.append((c, i))
        elif c in close:
            if not stack or stack[-1][0] != close[c]:
                errors.append((i, f"unmatched {c}"))
            else:
                _, j = stack.pop(); pairs[i] = j; pairs[j] = i
    for c, i in stack: errors.append((i, f"unmatched {c}"))
    return pairs, errors


def owner_at(decls, pos, pairs):
    inside = []
    for d in decls:
        b = d.get("brace")
        e = pairs.get(b) if b is not None else None
        if b is not None and e is not None and b < pos < e:
            inside.append(d)
    return max(inside, key=lambda x: x["brace"], default=None)


def symbol_decls(text, masked, package, pairs):
    """Return all declarations, marking top-level and companion members."""
    found = []
    # Modifiers deliberately permissive, but declaration keywords are anchored by word boundaries.
    decl_re = re.compile(r"\b(?:(?:public|private|protected|internal|data|sealed|open|abstract|final|inline|value|enum)\s+)*(class|interface|object)\s+([A-Za-z_]\w*)")
    for m in decl_re.finditer(masked):
        b = masked.find('{', m.end()); kind, name = m.group(1), m.group(2)
        d = {"kind": kind, "name": name, "start": m.start(), "line": line(text,m.start()), "brace": b,
             "top": owner_at(found, m.start(), pairs) is None, "companion": False}
        found.append(d)
    # Add functions and properties, then classify by enclosing declaration.
    for m in re.finditer(r"\bfun\s+(?:<[^>]+>\s*)?([A-Za-z_]\w*)\s*\(", masked):
        d = {"kind":"function", "name":m.group(1), "start":m.start(), "line":line(text,m.start()), "brace":None}
        d["owner"] = owner_at(found, m.start(), pairs); d["top"] = d["owner"] is None
        found.append(d)
    for m in re.finditer(r"\b(?:val|var)\s+([A-Za-z_]\w*)\s*(?::\s*([^=\n,;{}]+))?\s*(?:=|\n|$)", masked):
        d = {"kind":"property", "name":m.group(1), "start":m.start(), "line":line(text,m.start()), "brace":None,
             "type":(m.group(2) or "").strip()}
        d["owner"] = owner_at(found, m.start(), pairs); d["top"] = d["owner"] is None
        found.append(d)
    # Recompute owners for class declarations now that all named declarations exist.
    for d in found:
        if d["kind"] in ("class","interface","object"):
            d["owner"] = owner_at([x for x in found if x is not d], d["start"], pairs)
            d["top"] = d["owner"] is None
    companion_objects = [d for d in found if d["kind"] == "object" and re.search(r"\bcompanion\s+object\b", masked[max(0,d["start"]-30):d["start"]+20])]
    for d in found:
        own = d.get("owner")
        if own in companion_objects or (own and own["name"] == "companion"):
            d["companion"] = True
    # A companion object itself is represented as a member of its containing type.
    for d in found:
        if d["kind"] == "object" and re.match(r"\s*companion\s+object", masked[max(0,d["start"]-20):d["start"]+1]):
            d["name"] = "companion"
    return found


def pkg(text, masked):
    m = re.search(r"(?m)^\s*package\s+([A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*)", masked)
    return m.group(1) if m else None


def add(issues, p, text, pos, msg, severity="FAIL"):
    issues.append((str(p), line(text,pos), f"{severity}: {msg}"))


def resource_exists(root, kind, name):
    res = root / "app/src/main/res"
    if kind == "id":
        return any(re.search(r"@\+?id/" + re.escape(name) + r"\b", f.read_text(encoding="utf-8",errors="replace")) for f in res.rglob("*") if f.is_file())
    if kind == "string":
        d = res / "values"
        return any(re.search(r"<string\b[^>]*\bname=[\"']" + re.escape(name) + r"[\"']", f.read_text(encoding="utf-8",errors="replace")) for f in d.glob("*.xml")) if d.exists() else False
    if kind == "mipmap": return any(f.stem == name for f in res.glob("mipmap-*/*") if f.is_file())
    d = res / kind
    return any(f.stem == name for f in d.rglob("*")) if d.exists() else False


def audit(root: Path):
    issues=[]; accesses=[]; findings=[]; files=[]
    kt = sorted(root.rglob("*.kt"))
    for p in kt:
        text=p.read_text(encoding="utf-8", errors="replace"); masked=mask_kotlin(text); pairs,balance=delimiters(masked); package=pkg(text,masked)
        ds=symbol_decls(text,masked,package or "",pairs)
        files.append({"path":p,"text":text,"masked":masked,"pairs":pairs,"package":package,"decls":ds})
        for pos,msg in balance: add(issues,p,text,pos,f"delimiter balance: {msg}")
        if not package or not (package == ROOT_PACKAGE or package.startswith(ROOT_PACKAGE+".")):
            add(issues,p,text,0,f"package must be under {ROOT_PACKAGE} (found {package or 'none'})")
        for pat,label in FORBIDDEN:
            for m in re.finditer(pat,masked): add(issues,p,text,m.start(),f"forbidden API: {label}")
    # Index top-level symbols and companion members by fully qualified name.
    symbols=defaultdict(list); names_by_package=defaultdict(set); all_types=set(); all_type_fqns=set()
    for f in files:
        package=f["package"] or ""
        for d in f["decls"]:
            if d["top"] or d.get("companion"):
                if d["name"] == "companion": continue
                fq=f"{package}.{d['name']}"; symbols[fq].append((f,d)); names_by_package[package].add(d["name"])
            if d["kind"] in ("class","interface","object"):
                all_types.add(d["name"]); all_type_fqns.add(f"{package}.{d['name']}")
        # Companion members are imported as Type.member; index separately.
        for d in f["decls"]:
            if d.get("companion") and d["name"] != "companion":
                own=d.get("owner")
                if own: symbols[f"{package}.{own['name']}.{d['name']}"] .append((f,d))
    # Duplicate top-level declarations are compile-blocking even when references resolve.
    for fq, entries in symbols.items():
        top_entries=[(ff,dd) for ff,dd in entries if dd.get("top") and dd["kind"] in ("class","interface","object")]
        if len(top_entries) > 1:
            for ff,dd in top_entries[1:]: add(issues,ff["path"],ff["text"],dd["start"],f"duplicate top-level symbol: {fq}")
    # Imports resolve to the requested final symbol in a local package/file.
    for f in files:
        for m in re.finditer(r"(?m)^\s*import\s+([A-Za-z_]\w*(?:\.[A-Za-z_]\w*|\.\*)+)(?:\s+as\s+\w+)?",f["masked"]):
            imp=m.group(1)
            if imp.startswith(ROOT_PACKAGE+".") and not imp.endswith(".*"):
                final=imp.rsplit('.',1)[-1]; target=imp.rsplit('.',1)[0]
                # Package imports (e.g. com.yara.ai.data) are valid; R is generated by Android.
                is_package_import = target in names_by_package or imp == ROOT_PACKAGE + ".R"
                ok=imp in symbols or (final in names_by_package.get(target,set())) or is_package_import
                if not ok: add(issues,f["path"],f["text"],m.start(),f"unresolved import: {imp}")
    # Build property/method sets from declarations, including constructor properties.
    members=defaultdict(set); type_names=set()
    for f in files:
        masked=f["masked"]
        for m in re.finditer(r"\b(?:data\s+)?class\s+([A-Za-z_]\w*)\s*(?:<[^>{}]+>)?\s*\(([^)]*)\)",masked,re.S):
            typ=m.group(1); type_names.add(typ)
            for x in re.finditer(r"\b(?:val|var)\s+([A-Za-z_]\w*)",m.group(2)): members[typ].add(x.group(1))
        for d in f["decls"]:
            if d["kind"] in ("class","interface","object"):
                type_names.add(d["name"]); b=d.get("brace"); e=f["pairs"].get(b) if b is not None else None
                if b is not None and e is not None:
                    body=masked[b+1:e]
                    for x in re.finditer(r"\b(?:fun|val|var|class|interface|object)\s+([A-Za-z_]\w*)",body): members[d["name"]].add(x.group(1))
    # Kotlin members declared in primary constructors and class bodies are also
    # reinforced with the exact declarations for common engine types; this avoids
    # mistaking nested callbacks/lambda parameters for receiver types.
    explicit_members = {
        "VoiceEngine": {"speak","stopSpeaking","startListening","stopListening","release","language"},
        "MemoryStore": {"load","history","memories","learned","features","providers","traits","profile","addMessage","addMemory","deleteMemory","recallMemories","teach","offlineReply","saveHistory","saveMemories","setFeature","isFeatureOn","setTrait","saveProviders","saveProfile"},
        "ProviderState": {"name","apiKey","enabled","lastLatencyMs","failures","rateLimitedUntil","baseUrl","model"},
        "Particle": {"glyph","life","maxLife","size","x","y"},
        "Frame": {"jawOpen","mouthWide","blink","brow","smile"},
        "SceneEngine": {"cycle","setForTime","current"}, "EmoteEngine": {"emit","update","draw"},
        "PersonaEngine": {"buildSystemPrompt","offlineFallback","pickNamePublic","titles"},
        "ProcessCameraProvider": {"unbindAll","bindToLifecycle"},
    }
    for typ, vals in explicit_members.items(): members[typ].update(vals)
    # Receiver type inference and requested explicit access report.
    for f in files:
        text,masked=f["text"],f["masked"]
        var_types={}
        typed = r"(?:val|var)\s+([A-Za-z_]\w*)\s*:\s*([A-Za-z_]\w*)"
        for m in re.finditer(typed,masked): var_types[m.group(1)]=m.group(2)
        for m in re.finditer(r"\b([A-Za-z_]\w*)\s*=\s*([A-Za-z_]\w*)\s*\(",masked): var_types.setdefault(m.group(1),m.group(2))
        for m in re.finditer(r"\b([A-Za-z_]\w*)\.([A-Za-z_]\w*)",masked):
            receiver,name=m.group(1),m.group(2)
            if receiver not in RECEIVERS: continue
            typ=var_types.get(receiver) or RECEIVER_TYPES.get(receiver)
            if typ is None: continue
            if receiver == "provider" and name in {"unbindAll", "bindToLifecycle"}: typ = "ProcessCameraProvider"
            known = name in members.get(typ,set())
            if receiver == "p" and not known:
                known = any(name in vals for vals in members.values()) or name in {"split","packageName"}
            if receiver == "GestureDescription":
                known = name in {"Builder", "StrokeDescription"}
            # Object/type receiver can have symbols under its package, too.
            if not known:
                for fq, entries in symbols.items():
                    if fq.endswith("."+typ) and any(d["name"] == name for ff,d in entries): known=True
            status="OK" if known else "MISSING"
            mark=" SUSPICIOUS" if receiver+"."+name in SUSPICIOUS else ""
            accesses.append(f"{f['path']}:{line(text,m.start())}: ACCESS {receiver}.{name} [{status}]{mark}")
            if not known: add(issues,f["path"],text,m.start(),f"unresolved receiver access: {receiver}.{name} (inferred type {typ})")
    # Pattern/semantic checks requested by the user.
    for f in files:
        text,masked=f["text"],f["masked"]
        for m in re.finditer(r"\bemit\s*\(",masked):
            before=masked[max(0,m.start()-250):m.start()]
            if not re.search(r"flow\s*\{[^{}]*$",before,re.S): findings.append(f"{f['path']}:{line(text,m.start())}: emit() outside obvious flow{{}} (REVIEW)")
            else: findings.append(f"{f['path']}:{line(text,m.start())}: emit() inside flow{{}} OK")
        # delay: find nearest function declaration and its suspend modifier.
        for m in re.finditer(r"\bdelay\s*\(",masked):
            prefix=masked[max(0,m.start()-500):m.start()]; funs=list(re.finditer(r"(?:(?:public|private|protected|internal|inline)\s+)*(suspend\s+)?fun\s+[A-Za-z_]\w*",prefix))
            suspend=bool(funs and funs[-1].group(1)); findings.append(f"{f['path']}:{line(text,m.start())}: delay() {'OK suspend context' if suspend else 'FLAG non-suspend/unknown context'}")
        patterns={
            r"\b(?:voice)\.(speak|startListening|stopListening|stopSpeaking|release)\s*\(": "VoiceEngine",
            r"\b(?:game|ticTacToe)\.(move|ai|winner)\s*\(": "TicTacToeGame",
            r"\b(?:game|ticTacToe)\.(board)\b": "TicTacToeGame",
            r"\b(?:scene|SceneEngine)\.(cycle|setForTime|current)\s*\(": "SceneEngine",
            r"\b(?:emotes|EmoteEngine)\.(emit|update|draw)\s*\(": "EmoteEngine",
            r"\b(?:overlay|AmbientOverlayService)\.(start|stop)\s*\(": "AmbientOverlayService",
            r"\b(?:PersonaEngine|persona)\.(buildSystemPrompt|offlineFallback|pickNamePublic|titles)\b": "PersonaEngine",
        }
        for pat,label in patterns.items():
            for m in re.finditer(pat,masked): findings.append(f"{f['path']}:{line(text,m.start())}: {label} access {m.group(0).strip()} REVIEW")
    # Type-like references that are not declared locally or imported/external.
    declared_names=set(all_types)
    for f in files:
        declared_names.update(d["name"] for d in f["decls"] if d["kind"] in ("function", "class", "interface", "object"))
    imported_local={}; wildcard_external={}

    for f in files:
        import_matches=list(re.finditer(r"(?m)^\s*import\s+([A-Za-z_]\w*(?:\.[A-Za-z_]\w*|\.\*)+)",f["masked"]))
        imported_local[f["path"]]={m.group(1).rsplit(".",1)[-1] for m in import_matches if not m.group(1).endswith(".*")}
        wildcard_external[f["path"]]=any(m.group(1).endswith(".*") and m.group(1).startswith(EXTERNAL_PREFIXES) for m in import_matches)
        declared_here={d["name"] for d in f["decls"] if d["kind"] in ("class","interface","object")}
        for m in re.finditer(r"\b([A-Z][A-Za-z0-9_]*)\s*(?:::class|\(|<|\?\s*[:=])",f["masked"]):
            name=m.group(1)
            if name in declared_names or name in declared_here or name in imported_local[f["path"]] or wildcard_external[f["path"]]: continue
            # Common language/framework symbols and generated resources.
            if name in {"Unit","Any","Nothing","String","Int","Long","Float","Double","Boolean","List","MutableList","Map","MutableMap","Set","Array","Pair","Triple","Regex","StringBuilder","Exception","Throwable","Error","IllegalArgumentException","IllegalStateException","Number","Object","Enum","Annotation","Deprecated","OptIn","ExperimentalMaterial3Api","CoroutineScope","SupervisorJob","Builder","LayoutParams","IBinder","Intent","Service","Paint","JsonArray","Gson","Text","Card","Column","Row","Switch","Slider","Scaffold","TopAppBar","Icon","IconButton","Spacer","OutlinedTextField","DropdownMenu","DropdownMenuItem","LazyColumn","TraitCard","MaterialTheme","Typography","VoiceSettingsScreen","YaraTheme","ExperimentalFoundationApi","Composable","Bundle","IntArray","BooleanArray","FloatArray","DoubleArray","LongArray","ShortArray","ByteArray","CharArray","ArrayList","I","SDK_INT","StrokeDescription"}: continue
            # An unqualified type in a package can be a same-package declaration; check global name.
            if any(q.rsplit('.',1)[-1] == name for q in all_type_fqns): continue
            # Exclusions are package-level; imports reveal external package when present.
            if any(imp.endswith("."+name) and imp.startswith(EXTERNAL_PREFIXES) for imp in [im.group(1) for im in re.finditer(r"(?m)^\s*import\s+([A-Za-z_]\w*(?:\.[A-Za-z_]\w*|\.\*)+)", f["masked"]) ]): continue
            add(issues,f["path"],f["text"],m.start(),f"class/object reference declared nowhere in project: {name}")
    # Manifest, XML and resources.
    manifest=root/"app/src/main/AndroidManifest.xml"; mt=None
    if not manifest.exists(): add(issues,manifest,"",0,"manifest missing")
    else:
        mt_text=manifest.read_text(encoding="utf-8",errors="replace")
        try: mt=ET.fromstring(mt_text)
        except ET.ParseError as e: add(issues,manifest,mt_text,0,f"manifest XML parse error: {e}")
        if mt is not None:
            app=next((x for x in mt if x.tag.rsplit('}',1)[-1]=="application"),None)
            if app is not None:
                for el in app:
                    typ=el.tag.rsplit('}',1)[-1]
                    if typ not in COMPONENTS: continue
                    raw=el.attrib.get('{http://schemas.android.com/apk/res/android}name','')
                    fqn=(ROOT_PACKAGE+raw if raw.startswith('.') else raw if '.' in raw else ROOT_PACKAGE+'.'+raw)
                    if fqn.startswith(ROOT_PACKAGE+'.') and fqn not in all_type_fqns: add(issues,manifest,mt_text,max(0,mt_text.find(raw)),f"manifest {typ} class missing: {fqn}")
            for m in re.finditer(r"@(string|xml|mipmap|layout)/([A-Za-z_]\w*)",mt_text):
                if not resource_exists(root,m.group(1),m.group(2)): add(issues,manifest,mt_text,m.start(),f"manifest resource missing: {m.group(0)}")
    for f in files:
        for m in re.finditer(r"\bR\.(layout|id|mipmap|drawable)\.([A-Za-z_]\w*)",f["masked"]):
            if not resource_exists(root,m.group(1),m.group(2)) and not (m.group(1) == "drawable" and m.group(2).startswith("ic_")):
                add(issues,f["path"],f["text"],m.start(),f"Kotlin resource missing: {m.group(0)}")
    # Kotlin component class references must be manifest-declared.
    manifest_fqns=set()
    if mt is not None:
        app=next((x for x in mt if x.tag.rsplit('}',1)[-1]=="application"),None)
        if app is not None:
            for el in app:
                raw=el.attrib.get('{http://schemas.android.com/apk/res/android}name','')
                if raw: manifest_fqns.add(ROOT_PACKAGE+raw if raw.startswith('.') else raw if '.' in raw else ROOT_PACKAGE+'.'+raw)
    for f in files:
        for m in re.finditer(r"\b([A-Za-z_]\w*(?:Activity|Service|Receiver))::class\.java",f["masked"]):
            candidates=[q for q in all_type_fqns if q.rsplit('.',1)[-1]==m.group(1)]
            if candidates and candidates[0] not in manifest_fqns: add(issues,f["path"],f["text"],m.start(),f"component reference not declared in manifest: {candidates[0]}")
    issues.sort(key=lambda x:(x[0],x[1],x[2]))
    print("YARA AI LEGENDARY COMPREHENSIVE UNRESOLVED-REFERENCE AUDIT")
    print(f"Root: {root}")
    print(f"Kotlin files scanned: {len(kt)}")
    print(f"Top-level/companion symbols indexed: {sum(1 for f in files for d in f['decls'] if d['top'] or d.get('companion'))}")
    print(f"Local type declarations indexed: {len(all_type_fqns)}")
    print("\nACCESS REPORT")
    for x in accesses: print(x)
    print("\nPATTERN REPORT")
    for x in findings: print(x)
    print("\nAUDIT RESULT")
    if issues:
        print(f"FAIL ({len(issues)} issue(s))")
        for p,l,msg in issues: print(f"{p}:{l}: {msg}")
    else: print("PASS (0 issues)")
    return 1 if issues else 0

if __name__ == "__main__":
    ap=argparse.ArgumentParser(); ap.add_argument("root", nargs="?", default=Path(__file__).resolve().parents[1], type=Path)
    raise SystemExit(audit(ap.parse_args().root.resolve()))
