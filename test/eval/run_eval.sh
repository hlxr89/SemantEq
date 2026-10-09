#!/usr/bin/env bash
# Public eval suites for SemantEq. One command: build, run, score.
#   ./run_eval.sh [recall|ablation|all]     (default: all)
set -euo pipefail
cd "$(dirname "$0")/../.."   # repo root
SUITES="${1:-all}"; [ "$SUITES" = all ] && SUITES="recall ablation"
lake build semanteq >/dev/null
for s in $SUITES; do
  D=test/eval/$s
  echo "== $s ($(grep -c . $D/suite.jsonl) pairs) =="
  lake env .lake/build/bin/semanteq --timeout 0 "$D/suite.jsonl" "$D/results.jsonl" >/dev/null
  python3 - "$D" <<'PY'
import json, sys
d=sys.argv[1]
ACC=('ExactMatch','DefEq','EquivalentRestricted')
NORM={'accept':'accept','equivalent':'accept','reject':'reject','not_equivalent':'reject'}
exp={o['id']:('accept' if o['default_search_accepts'] else 'reject') if 'default_search_accepts' in o else NORM.get(o.get('expected','reject'),'reject') for o in map(json.loads,open(f'{d}/manifest.jsonl'))}
ok=bad=0; wrong=[]
for l in open(f'{d}/results.jsonl'):
    o=json.loads(l)
    if not o.get('id'): continue
    acc=any(o['verdict'].startswith(a) for a in ACC)
    want=exp.get(o['id'],'reject')
    hit=(acc and want=='accept') or ((not acc) and want=='reject')
    ok+=hit; bad+=not hit
    if not hit: wrong.append((o['id'],want,o['verdict']))
print(f"  {ok}/{ok+bad} as expected")
for w in wrong[:10]: print("   UNEXPECTED:", *w)
PY
done
