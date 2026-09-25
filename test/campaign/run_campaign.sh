#!/usr/bin/env bash
# Re-check the model-written proofs of one prompt style (or all four) with
# SemantEq-ProofAudit and print the paper's scoring.
#   ./test/campaign/run_campaign.sh [unrestricted|faithful|rewrite|expedient|all]
#   LIMIT=N   only the first N pairs (smoke test)
#   STRICT=1  run the checker in --strict mode (the paper's strict reading); records go to results/<style>.strict.jsonl
set -euo pipefail
cd "$(dirname "$0")/../.."   # repository root
STYLES="${1:-all}"; [ "$STYLES" = all ] && STYLES="unrestricted faithful rewrite expedient"
D=test/campaign; mkdir -p "$D/results"
lake build semanteq >/dev/null
for s in $STYLES; do
  dirs=$(ls -d "$D/proofs/$s"/* | sort)
  [ -n "${LIMIT:-}" ] && dirs=$(echo "$dirs" | head -n "$LIMIT")
  echo "== $s: $(echo "$dirs" | wc -l) pairs =="
  # shellcheck disable=SC2086
  if [ -n "${STRICT:-}" ]; then SFLAG=--strict; SUF=.strict; else SFLAG=""; SUF=""; fi
  # shellcheck disable=SC2086
  lake env .lake/build/bin/semanteq --raw $SFLAG --proof $dirs > "$D/results/$s$SUF.jsonl" 2> "$D/results/$s$SUF.err"
  python3 - "$D" "$s" "$SUF" <<'PY'
import json, sys, os, re
D, s, suf = sys.argv[1], sys.argv[2], sys.argv[3]
man = {r['pair']: r for r in map(json.loads, open(f'{D}/manifest.jsonl'))}
rec = {}
for l in open(f'{D}/results/{s}{suf}.jsonl'):
    l = l.strip()
    if not l: continue
    r = json.loads(l)
    m = re.search(r'proofs/[^/]+/([^/]+)/+(ref_imp_cand|cand_imp_ref)\.lean$', r['file'])
    if m: rec[(m.group(1), m.group(2))] = r
pairs = sorted({p for p, _ in rec})
STATUS = {'PASS': 'accepted', 'FAIL': 'rejected', 'SKIP_SORRY': 'skipped', 'ERROR': 'error'}
def ok(r, strict):
    if r['verdict'] != 'PASS': return False
    return not (strict and any(x.startswith('severe:') for x in (r.get('flagDetails') or [])))
agree = total = 0
for lab in ('equivalent', 'non_equivalent'):
    pop = [p for p in pairs if man[p]['label'] == lab]
    line = f"  {lab:15s} ({len(pop):3d} pairs)"
    for strict in (False, True):
        both = one = nei = 0
        for p in pop:
            n = sum(1 for d in ('ref_imp_cand', 'cand_imp_ref') if (p, d) in rec and ok(rec[(p, d)], strict))
            both += n == 2; one += n == 1; nei += n == 0
        line += f"   {'strict' if strict else 'tolerant'} both/one/neither {both}/{one}/{nei}"
    print(line)
for (p, d), r in rec.items():
    total += 1; agree += STATUS.get(r['verdict']) == man[p][s][d]['status']
print(f"  directions agreeing with the manifest: {agree}/{total}")
PY
done
