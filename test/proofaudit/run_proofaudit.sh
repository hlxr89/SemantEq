#!/usr/bin/env bash
# Public ProofChecker corpus. One command: build, audit every fixture, score
# against manifest.jsonl expectations (the expected verdicts hold in both modes).
#   STRICT=1  run the checker in --strict mode; records go to results.strict.jsonl
set -euo pipefail
cd "$(dirname "$0")/../.."   # repo root
lake build semanteq >/dev/null
if [ -n "${STRICT:-}" ]; then SFLAG=--strict; OUT=test/proofaudit/results.strict.jsonl; else SFLAG=""; OUT=test/proofaudit/results.jsonl; fi
: > "$OUT"
for d in test/proofaudit/pairs/*/; do
  lake env .lake/build/bin/semanteq --raw $SFLAG --proof "$d" >> "$OUT" 2>/dev/null
done
OUT_FILE="$OUT" python3 - <<'PY'
import json, os
exp={(m['dir'],m['file']):m['expected'] for m in map(json.loads,open('test/proofaudit/manifest.jsonl'))}
ok=bad=0; wrong=[]
for l in open(os.environ.get('OUT_FILE','test/proofaudit/results.jsonl')):
    l=l.strip()
    if not l: continue
    try: o=json.loads(l)
    except Exception: continue
    f=o.get('file','')
    key=(os.path.basename(os.path.dirname(f)), os.path.basename(f))
    want=exp.get(key)
    if want is None: continue
    hit=o.get('verdict')==want
    ok+=hit; bad+=not hit
    if not hit: wrong.append((key,want,o.get('verdict')))
print(f"{ok}/{ok+bad} fixtures as expected" + (" (strict mode)" if "strict" in os.environ.get("OUT_FILE","") else ""))
for w in wrong: print("  UNEXPECTED:", w)
PY
