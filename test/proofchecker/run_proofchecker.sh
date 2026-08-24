#!/usr/bin/env bash
# Public ProofChecker corpus. One command: build, audit every fixture, score
# against manifest.jsonl expectations.
set -euo pipefail
cd "$(dirname "$0")/../.."   # repo root
lake build static_eval >/dev/null
OUT=test/proofchecker/results.jsonl
: > "$OUT"
for d in test/proofchecker/pairs/*/; do
  lake env .lake/build/bin/static_eval --proof "$d" >> "$OUT" 2>/dev/null
done
python3 - <<'PY'
import json, os
exp={(m['dir'],m['file']):m['expected'] for m in map(json.loads,open('test/proofchecker/manifest.jsonl'))}
ok=bad=0; wrong=[]
for l in open('test/proofchecker/results.jsonl'):
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
print(f"{ok}/{ok+bad} fixtures as expected")
for w in wrong: print("  UNEXPECTED:", w)
PY
