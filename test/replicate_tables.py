#!/usr/bin/env python3
"""Recompute the paper's result tables from the tracked verdict tables in this repository.

    python3 test/replicate_tables.py            # all tables
    python3 test/replicate_tables.py 1 2 4 5    # a selection

Inputs (all tracked):
  test/results/pnv_test_verdicts.jsonl    Table 1  (ProofNetVerif test split, both label sets)
  test/results/ablation_verdicts.jsonl    Table 2  (the ablation set: six arms + BEq+)
  test/results/capability_verdicts.jsonl  Table 3  (search-strength tiers on the 407 equivalent pairs)
  test/campaign/manifest.jsonl            Table 4  (model-written proofs, default mode) and
                                          Table 5  (the strict mode)
The verdict tables are the per-pair outcomes of the runs behind the paper (SemantEq-Eval at
each search configuration, our BEq+ port, and the six ablation arms), distilled to one line per
pair; the raw records are not tracked. test/campaign/manifest.jsonl carries the checker's
verdict for every model-written proof in default mode (`status`) and in strict mode
(`strict_status`).
"""
import json, sys, statistics, collections, os
HERE = os.path.dirname(os.path.abspath(__file__))
def jl(p):
    with open(os.path.join(HERE, p)) as fh:
        for l in fh:
            l = l.strip()
            if l:
                yield json.loads(l)
def prf(tp, fp, fn):
    p = 100 * tp / (tp + fp) if tp + fp else 0.0
    r = 100 * tp / (tp + fn) if tp + fn else 0.0
    f = 2 * p * r / (p + r) if p + r else 0.0
    return p, r, f

def table1():
    rows = list(jl('results/pnv_test_verdicts.jsonl'))
    print(f"\nTable 1 — ProofNetVerif test split, {len(rows)} compilable pairs")
    print(f"  {'labels':12s} {'system':12s} {'TP':>4s} {'FP':>4s} {'FN':>4s} {'TN':>5s} {'P':>6s} {'R':>6s} {'F1':>6s}")
    for lab_name, key in (('published', 'published_equivalent'), ('adjudicated', 'adjudicated_equivalent')):
        for sys_name, acc in (('Ours', 'semanteq_accept'), ('BEq+ v4.30', 'beqplus_v430_accept')):
            tp = sum(1 for r in rows if r[acc] and r[key]); fp = sum(1 for r in rows if r[acc] and not r[key])
            fn = sum(1 for r in rows if not r[acc] and r[key]); tn = sum(1 for r in rows if not r[acc] and not r[key])
            p, rc, f = prf(tp, fp, fn)
            print(f"  {lab_name:12s} {sys_name:12s} {tp:4d} {fp:4d} {fn:4d} {tn:5d} {p:6.1f} {rc:6.1f} {f:6.1f}")

ORDER = ['pnv', 'added_claim', 'neighbouring_theorem', 'unrelated_true_fact', 'vacuous_hypotheses']
ARMS = [('all audits', 'semanteq_all_audits_accept'), ('- relevance', 'semanteq_no_relevance_accept'),
        ('- proof-term grading', 'semanteq_no_proof_term_grading_accept'), ('- explosion check', 'semanteq_no_explosion_check_accept'),
        ('- antecedent-free replay', 'semanteq_no_replay_accept'), ('all four removed', 'semanteq_no_audits_accept'),
        ('BEq+ v4.30 (our toolchain)', 'beqplus_v430_accept'), ('BEq+ v4.8 (original)', 'beqplus_v48_accept')]
def table2():
    rows = list(jl('results/ablation_verdicts.jsonl'))
    sizes = collections.Counter(r['class'] for r in rows)
    print(f"\nTable 2 — erroneous acceptances on the ablation set ({len(rows)} non-equivalent pairs)")
    print("  " + " ".join(f"{c}({sizes[c]})" for c in ORDER))
    for name, key in ARMS:
        c = collections.Counter(r['class'] for r in rows if r[key])
        print(f"  {name:28s} " + " ".join(f"{c[o]:4d}" for o in ORDER) + f"   total {sum(c.values()):3d}")

def table3():
    rows = list(jl('results/capability_verdicts.jsonl'))
    meta = json.load(open(os.path.join(HERE, 'results/capability_meta.json')))
    tiers = meta['tiers']
    ids = [r['id'] for r in rows]; N = len(ids)
    print(f"\nTable 3 — search strength on the {N} adjudicated-equivalent pairs (369 test + 38 recall)")
    print("  a pair keeps the cost of the tier that first accepted it; an unaccepted pair is charged its")
    print("  re-run time at the tier, or the tier's mean re-run time when it was not re-run")
    base = {r['id']: (r['base_elapsed_s'], r['base_accept']) for r in rows}
    runs = {tag: {r['id']: (r[f'{tag}_elapsed_s'], r[f'{tag}_accept']) for r in rows if r[f'{tag}_accept'] is not None} for tag, _ in tiers}
    t0 = dict(base)
    for i, (el, acc) in runs['T0'].items():
        if el is not None: t0[i] = (el, acc)
    res0 = [t0[i][0] for i in ids if i in t0 and t0[i][0] is not None and not t0[i][1]]
    mean_res0 = statistics.mean(res0)
    acc_at = {i: (0, t0[i][0]) for i in ids if i in t0 and t0[i][1]}
    print(f"  {'configuration':14s} {'median s':>9s} {'mean s':>8s} {'max s':>8s} {'total h':>8s} {'accepts':>8s} {'recall':>7s}")
    for k, (tag, lbl) in enumerate(tiers):
        run = runs[tag]
        if k > 0:
            for i in ids:
                if i not in acc_at and i in run and run[i][1]: acc_at[i] = (k, run[i][0])
        vals = [run[i][0] for i in ids if i in run and run[i][0] is not None and not (i in acc_at and acc_at[i][0] <= k)]
        res_mean = statistics.mean(vals) if vals else mean_res0
        costs = []
        for i in ids:
            if i in acc_at and acc_at[i][0] <= k: costs.append(acc_at[i][1])
            elif k == 0: costs.append(t0[i][0] if i in t0 and t0[i][0] is not None else mean_res0)
            elif i in run and run[i][0] is not None: costs.append(run[i][0])
            else: costs.append(res_mean)
        n_acc = sum(1 for i in ids if i in acc_at and acc_at[i][0] <= k)
        print(f"  {lbl:14s} {statistics.median(costs):9.1f} {statistics.mean(costs):8.1f} {max(costs):8.0f} {sum(costs)/3600:8.2f} {n_acc:8d} {100*n_acc/N:6.1f}%")
    for name, ek, ak in (('BEq+ v4.8', 'beqplus_v48_elapsed_s', 'beqplus_v48_accept'), ('BEq+ v4.30', 'beqplus_v430_elapsed_s', 'beqplus_v430_accept')):
        el = [r[ek] for r in rows if r[ek] is not None]; acc = sum(1 for r in rows if r[ak])
        miss = sum(1 for r in rows if r[ek] is None)
        print(f"  {name:14s} {statistics.median(el):9.1f} {statistics.mean(el):8.1f} {max(el):8.0f} {sum(el)/3600:8.2f} {acc:8d} {100*acc/N:6.1f}%" + (f"   ({miss} pairs without a run, counted as rejected)" if miss else ""))

STYLES = ['expedient', 'unrestricted', 'faithful', 'rewrite']
def campaign(status_key, title):
    rows = list(jl('campaign/manifest.jsonl'))
    print(f"\n{title}")
    print(f"  {'style':13s} {'equivalent both/one/neither':>30s} {'non-equivalent both/one/neither':>34s}")
    for s in STYLES:
        out = []
        for lab in ('equivalent', 'non_equivalent'):
            c = collections.Counter()
            for r in rows:
                if r['label'] != lab: continue
                n = sum(1 for d in ('ref_imp_cand', 'cand_imp_ref') if r[s][d].get(status_key) == 'accepted'); c[n] += 1
            out.append(f"{c[2]}/{c[1]}/{c[0]}")
        print(f"  {s:13s} {out[0]:>30s} {out[1]:>34s}")

if __name__ == '__main__':
    want = set(sys.argv[1:]) or {'1', '2', '3', '4', '5'}
    if '1' in want: table1()
    if '2' in want:
        if os.path.exists(os.path.join(HERE, 'results/ablation_verdicts.jsonl')): table2()
        else: print("\nTable 2 — results/ablation_verdicts.jsonl not present")
    if '3' in want: table3()
    if '4' in want: campaign('status', "Table 4 — model-written proofs, default mode (pairs both/one/neither)")
    if '5' in want: campaign('strict_status', "Table 5 — model-written proofs, strict mode (pairs both/one/neither)")
