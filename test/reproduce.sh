#!/usr/bin/env bash
# Reproduce the paper's results FROM SCRATCH: every stage re-runs the programs on the
# released statements and proofs; `tables` distils the fresh records to one line per pair
# and prints Tables 1-5 from them (test/reproduce_tables.py). Nothing here reads test/results/
# except for the BEq+ rows (see below).
#
#   test/reproduce.sh corpus      proof-audit corpus, default and strict mode        (~10 min)
#   test/reproduce.sh suites      recall suite + the constructed half of the ablation set (~30 min)
#   test/reproduce.sh ablation    the six ablation arms -> Table 2                     (~2 h; +6 h with the ProofNetVerif half)
#   test/reproduce.sh campaign    the checker over the campaign proofs -> Tables 4, 5  (~4 h, ~1.5 h with LANES=3)
#   test/reproduce.sh pnv         SemantEq-Eval over the ProofNetVerif test split -> Table 1 (~12 h, ~4 h with LANES=3)
#   test/reproduce.sh tiers       the eleven search configurations over the equivalent set -> Table 3 (days; see below)
#   test/reproduce.sh tables      assemble the fresh verdict tables and print Tables 1-5
#
# ProofNetVerif is not redistributed: `python3 test/pnv_fetch.py` downloads it and writes
# test/data/{pnv_test.jsonl, ablation_pnv.jsonl, equivalent_set.jsonl}; the stages that need
# them look there (override with PNV=, ABL_PNV=, EQSET=). The BEq+ rows of the tables come
# from our port of its released implementation, which is not part of this repository; the
# fresh tables print them from test/results when that file is present, marked as such.
#
# Knobs: LANES=n runs n processes on disjoint chunks (each process holds ~8 GB with Mathlib);
# CHUNK=n pairs per process (default 40); STALL_SECS=s kills a chunk whose output has not
# grown for s seconds and sets its first unfinished pair aside (default 900); LIMIT=n runs
# only the first n pairs of every input (smoke test). Every stage is resumable: a finished
# chunk is skipped on re-run.
set -euo pipefail
cd "$(dirname "$0")/.."
STAGE="${1:-}"; [ -n "$STAGE" ] || { sed -n 2,22p "$0"; exit 1; }
OUT=test/reproduce_out; mkdir -p "$OUT"
LANES="${LANES:-1}"; CHUNK="${CHUNK:-40}"; STALL_SECS="${STALL_SECS:-900}"; LIMIT="${LIMIT:-}"
PNV="${PNV:-test/data/pnv_test.jsonl}"; ABL_PNV="${ABL_PNV:-test/data/ablation_pnv.jsonl}"; EQSET="${EQSET:-test/data/equivalent_set.jsonl}"
lake build semanteq >/dev/null
BIN=.lake/build/bin/semanteq

# run_pairs <pairs.jsonl> <out.jsonl> [env assignments...]: chunked, resumable, LANES-parallel
run_pairs () {
  local input=$1 out=$2; shift 2
  local wd="$out.chunks"; mkdir -p "$wd"
  local src="$input"
  if [ -n "$LIMIT" ]; then head -n "$LIMIT" "$input" > "$wd/input.jsonl"; src="$wd/input.jsonl"; fi
  split -l "$CHUNK" -d -a 4 "$src" "$wd/chunk_"
  local chunks=("$wd"/chunk_[0-9][0-9][0-9][0-9])
  run_chunk () { # one process per chunk; watchdog on the streamed stdout
    local c=$1; shift; [ -f "$c.out.jsonl" ] && return 0
    ( env "$@" lake env "$BIN" --raw "$c" "$c.out.jsonl" > "$c.stream" 2> "$c.err" ) &
    local pid=$! last=0 same=0
    while kill -0 $pid 2>/dev/null; do
      sleep 15; local n; n=$(grep -c '"id"' "$c.stream" 2>/dev/null || echo 0)
      if [ "$n" = "$last" ]; then same=$((same+15)); else same=0; last=$n; fi
      if [ $same -ge "$STALL_SECS" ]; then
        pkill -P $pid 2>/dev/null; kill $pid 2>/dev/null; wait $pid 2>/dev/null
        local done_ids; done_ids=$(grep -o '"id":"[^"]*"' "$c.stream" | cut -d'"' -f4)
        python3 - "$c" "$c.stream" >> "$wd/QUARANTINE.jsonl" <<'PY'
import json,sys
c,stream=sys.argv[1],sys.argv[2]
done={json.loads(l)['id'] for l in open(stream) if l.startswith('{') and '"id"' in l}
rows=[l for l in open(c) if l.strip()]
todo=[l for l in rows if json.loads(l)['id'] not in done]
sys.stdout.write(todo[0])                      # the stalled pair, set aside
open(c,'w').writelines([l for l in rows if l!=todo[0]])
PY
        echo "stall: one pair of $(basename $c) set aside (see $wd/QUARANTINE.jsonl); chunk restarted" >&2
        run_chunk "$c" "$@"; return
      fi
    done
    wait $pid 2>/dev/null || true
    # the streamed records are the result even if the batch's own out-file was not written
    [ -f "$c.out.jsonl" ] || grep '"id"' "$c.stream" > "$c.out.jsonl" || true
  }
  export -f run_chunk; export BIN STALL_SECS wd
  printf '%s\n' "${chunks[@]}" | xargs -P "$LANES" -I{} bash -c 'run_chunk "$@"' _ {} "$@"
  cat "$wd"/chunk_[0-9][0-9][0-9][0-9].out.jsonl 2>/dev/null | grep '"id"' > "$out" || true
  echo "$out: $(grep -c . "$out") records (stall-quarantined: $(grep -c . "$wd/QUARANTINE.jsonl" 2>/dev/null || echo 0))"
}

need () { [ -f "$1" ] || { echo "missing $1 — run: python3 test/pnv_fetch.py" >&2; exit 2; }; }

case "$STAGE" in
  corpus)
    bash test/proofaudit/run_proofaudit.sh; STRICT=1 bash test/proofaudit/run_proofaudit.sh ;;
  suites)
    bash test/eval/run_eval.sh ;;
  ablation)
    ARMS=("all_audits:" "no_relevance:SEMANTEQ_NO_ESSENTIAL=1 SEMANTEQ_NO_PREGATE=1" "no_proof_term_grading:SEMANTEQ_NO_PROOFAUDIT=1"
          "no_explosion_check:SEMANTEQ_NO_P0=1" "no_replay:SEMANTEQ_NO_REPLAY=1"
          "no_audits:SEMANTEQ_NO_ESSENTIAL=1 SEMANTEQ_NO_PREGATE=1 SEMANTEQ_NO_PROOFAUDIT=1 SEMANTEQ_NO_P0=1 SEMANTEQ_NO_REPLAY=1")
    inputs=(test/eval/ablation/suite.jsonl); [ -f "$ABL_PNV" ] && inputs+=("$ABL_PNV") || echo "note: $ABL_PNV absent, constructed half only" >&2
    cat "${inputs[@]}" > "$OUT/ablation_input.jsonl"
    for a in "${ARMS[@]}"; do name=${a%%:*}; envs=${a#*:}; echo "== arm $name"; run_pairs "$OUT/ablation_input.jsonl" "$OUT/ablation_$name.jsonl" $envs; done ;;
  campaign)
    # one checker process per lane and mode; a style whose output file exists is skipped
    for s in unrestricted faithful rewrite expedient; do
      mapfile -t dirs < <(ls -d test/campaign/proofs/$s/* | sort); [ -n "$LIMIT" ] && dirs=("${dirs[@]:0:$LIMIT}")
      for mode in default strict; do
        if [ $mode = strict ]; then SFLAG=--strict; suf=_strict; else SFLAG=""; suf=""; fi
        out="$OUT/campaign_$s$suf.jsonl"
        if [ -s "$out" ]; then echo "== $s $mode: $out present, skipped"; continue; fi
        wd="$out.lanes"; mkdir -p "$wd"; rm -f "$wd"/lane_*
        printf '%s\n' "${dirs[@]}" | split -n r/"$LANES" -d -a 2 - "$wd/lane_"
        echo "== $s $mode (${#dirs[@]} pairs, $LANES lanes)"
        for f in "$wd"/lane_??; do ( xargs -a "$f" lake env "$BIN" --raw $SFLAG --proof > "$f.out" 2> "$f.err" ) & done; wait
        cat "$wd"/lane_??.out > "$out"
        echo "$out: $(grep -c '"verdict"' "$out") direction records"
      done
    done ;;
  pnv)
    need "$PNV"; run_pairs "$PNV" "$OUT/pnv_test.jsonl" ;;
  tiers)
    # the residual chain of the paper: each configuration runs on the pairs no cheaper
    # configuration closed; the fold in reproduce_tables.py charges pairs as in the paper.
    need "$EQSET"
    W1="SEMANTEQ_ARM_BUDGET=160 SEMANTEQ_DISCOVERY_BUDGET=128"; W2="SEMANTEQ_ARM_BUDGET=320 SEMANTEQ_DISCOVERY_BUDGET=256"
    DW1="SEMANTEQ_LEMMA_CAP=48 SEMANTEQ_STATE_CAP=48 SEMANTEQ_DEEP_LEVEL_BUDGET=4000000"; DW2="SEMANTEQ_LEMMA_CAP=96 SEMANTEQ_STATE_CAP=96 SEMANTEQ_DEEP_LEVEL_BUDGET=16000000"
    TIERS=("T0:SEMANTEQ_DEPTH=1" "d1w1:SEMANTEQ_DEPTH=1 $W1" "T1:SEMANTEQ_DEPTH=2" "T3:SEMANTEQ_DEPTH=2 $W1" "T6:SEMANTEQ_DEPTH=2 $W1 $DW1"
           "T2:SEMANTEQ_DEPTH=4" "T4:SEMANTEQ_DEPTH=4 $W1" "T7:SEMANTEQ_DEPTH=4 $W1 $DW1" "T5:SEMANTEQ_DEPTH=8 $W1" "T8:SEMANTEQ_DEPTH=4 $W2 $DW2" "T9:SEMANTEQ_DEPTH=8 $W2 $DW2")
    if [ -n "${TIER_ONLY:-}" ]; then mapfile -t TIERS < <(printf '%s\n' "${TIERS[@]}" | grep -E "^(${TIER_ONLY}):"); fi
    for t in "${TIERS[@]}"; do
      name=${t%%:*}; envs=${t#*:}
      python3 - "$EQSET" "$OUT/tier_${name}_input.jsonl" "$OUT"/tier_*.jsonl <<'PY'
import json,sys,glob,os
src,nxt=sys.argv[1],sys.argv[2]
ACC=('ExactMatch','DefEq','EquivalentRestricted'); acc=set()
for f in sys.argv[3:]:
    if os.path.exists(f) and '_input' not in f:
        for l in open(f):
            if l.startswith('{'):
                o=json.loads(l)
                if o.get('id') and any(str(o.get('verdict','')).startswith(a) for a in ACC): acc.add(o['id'])
rows=[l for l in open(src) if json.loads(l)['id'] not in acc]; open(nxt,'w').writelines(rows)
print(f"{nxt}: {len(rows)} pairs to run ({len(acc)} already closed by a cheaper configuration)")
PY
      echo "== tier $name ($envs)"; run_pairs "$OUT/tier_${name}_input.jsonl" "$OUT/tier_$name.jsonl" $envs
    done ;;
  tables)
    python3 test/reproduce_tables.py "$OUT" ;;
  *) echo "unknown stage: $STAGE" >&2; exit 1 ;;
esac
