#!/usr/bin/env python3
"""Print the paper's tables from the raw records that test/reproduce.sh wrote (`test/reproduce.sh
tables` calls this). Every number comes from those fresh runs: the records are first distilled
to one line per pair under <out>/results/ (the same schema as test/results/), then the tables are
computed from that. The only rows taken from test/results/ are the BEq+ rows, since our port of
its released implementation is not part of this repository; they are marked as such.

    python3 test/reproduce_tables.py test/reproduce_out

Table 3 charges a pair the running time of the first configuration that accepted it, and an
unaccepted pair its re-run time at the configuration (or the configuration's mean re-run time
when it was not re-run), as in the paper.
"""
import json, os, re, sys, statistics, collections
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'reproduce_out')
RES = os.path.join(OUT, 'results'); os.makedirs(RES, exist_ok=True)
ACCEPT = {"EquivalentRestricted", "ExactMatch", "DefEq"}
BAD = {"CandidateCompileError", "BothCompileError", "ReferenceCompileError"}
def jl(p):
    if not os.path.exists(p): return
    with open(p) as fh:
        for l in fh:
            l = l.strip()
            if l.startswith('{'):
                try: yield json.loads(l)
                except Exception: pass
def recs(p): return {o['id']: o for o in jl(p) if 'id' in o}
prior = {r['id']: r for r in jl(os.path.join(HERE, 'results', 'pnv_test_verdicts.jsonl'))}
prior_abl = {r['id']: r for r in jl(os.path.join(HERE, 'results', 'ablation_verdicts.jsonl'))}
prior_cap = {r['id']: r for r in jl(os.path.join(HERE, 'results', 'capability_verdicts.jsonl'))}
made = []

# ---------------------------------------------------------------- the tables
def prf(tp, fp, fn):
    p = 100 * tp / (tp + fp) if tp + fp else 0.0
    r = 100 * tp / (tp + fn) if tp + fn else 0.0
    f = 2 * p * r / (p + r) if p + r else 0.0
    return p, r, f

def table1():
    rows = list(jl(os.path.join(RES, 'pnv_test_verdicts.jsonl')))
    print(f"\nTable 1 — ProofNetVerif test split, {len(rows)} compilable pairs")
    print(f"  {'labels':12s} {'system':12s} {'TP':>4s} {'FP':>4s} {'FN':>4s} {'TN':>5s} {'P':>6s} {'R':>6s} {'F1':>6s}")
    for lab_name, key in (('published', 'published_equivalent'), ('adjudicated', 'adjudicated_equivalent')):
        for sys_name, acc in (('Ours', 'semanteq_accept'), ('BEq+ v4.30', 'beqplus_v430_accept')):
            if any(acc not in r for r in rows):
                print(f"  {lab_name:12s} {sys_name:12s} (not in this results set)"); continue
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
    rows = list(jl(os.path.join(RES, 'ablation_verdicts.jsonl')))
    sizes = collections.Counter(r['class'] for r in rows)
    print(f"\nTable 2 — erroneous acceptances on the ablation set ({len(rows)} non-equivalent pairs)")
    print("  " + " ".join(f"{c}({sizes[c]})" for c in ORDER))
    for name, key in ARMS:
        if any(key not in r for r in rows):
            print(f"  {name:28s} (not in this results set)"); continue
        c = collections.Counter(r['class'] for r in rows if r[key])
        print(f"  {name:28s} " + " ".join(f"{c[o]:4d}" for o in ORDER) + f"   total {sum(c.values()):3d}")

def table3():
    rows = list(jl(os.path.join(RES, 'capability_verdicts.jsonl')))
    meta = json.load(open(os.path.join(RES, 'capability_meta.json')))
    tiers = meta['tiers']
    ids = [r['id'] for r in rows]; N = len(ids)
    print(f"\nTables 5 and 6 — search strength on the {N} pairs of the equivalent set")
    print("  a pair keeps the cost of the tier that first accepted it; an unaccepted pair is charged its")
    print("  re-run time at the tier, or the tier's mean re-run time when it was not re-run")
    base = {r['id']: (r['base_elapsed_s'], r['base_accept']) for r in rows}
    runs = {tag: {r['id']: (r[f'{tag}_elapsed_s'], r[f'{tag}_accept']) for r in rows if r[f'{tag}_accept'] is not None} for tag, _ in tiers}
    t0 = dict(base)
    for i, (el, acc) in runs['T0'].items():
        if el is not None: t0[i] = (el, acc)
    res0 = [t0[i][0] for i in ids if i in t0 and t0[i][0] is not None and not t0[i][1]]
    mean_res0 = statistics.mean(res0) if res0 else 0.0
    acc_at = {i: (0, t0[i][0]) for i in ids if i in t0 and t0[i][1]}
    print(f"  {'configuration':14s} {'median s':>9s} {'mean s':>8s} {'max s':>8s} {'total h':>8s} {'accepts':>8s} {'recall':>7s}")
    for k, (tag, lbl) in enumerate(tiers):
        run = runs[tag]
        if k > 0 and not run:
            print(f"  {lbl:14s} (not run)"); continue
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
        if any(ek not in r for r in rows):
            print(f"  {name:14s} (not in this results set)"); continue
        el = [r[ek] for r in rows if r[ek] is not None]; acc = sum(1 for r in rows if r[ak])
        miss = sum(1 for r in rows if r[ek] is None)
        print(f"  {name:14s} {statistics.median(el):9.1f} {statistics.mean(el):8.1f} {max(el):8.0f} {sum(el)/3600:8.2f} {acc:8d} {100*acc/N:6.1f}%" + (f"   ({miss} pairs without a run, counted as rejected)" if miss else ""))

CAMPAIGN_ORDER = ['expedient', 'unrestricted', 'faithful', 'rewrite']
def campaign(status_key, title):
    rows = list(jl(os.path.join(RES, 'campaign_manifest.jsonl')))
    print(f"\n{title}")
    print(f"  {'style':13s} {'equivalent both/one/neither':>30s} {'non-equivalent both/one/neither':>34s}")
    for s in CAMPAIGN_ORDER:
        out = []
        for lab in ('equivalent', 'non_equivalent'):
            c = collections.Counter()
            for r in rows:
                if r['label'] != lab: continue
                n = sum(1 for d in ('ref_imp_cand', 'cand_imp_ref') if r[s][d].get(status_key) == 'accepted'); c[n] += 1
            out.append(f"{c[2]}/{c[1]}/{c[0]}")
        print(f"  {s:13s} {out[0]:>30s} {out[1]:>34s}")

# ------------------------------------------- distil the raw records to one line per pair
# Table 1
pnv = recs(os.path.join(OUT, 'pnv_test.jsonl'))
if pnv:
    adj = {r['id']: r for r in jl(os.path.join(HERE, 'pnv_test_adjudicated_labels.jsonl'))}
    rows = []
    for i, o in pnv.items():
        if o.get('verdict') in BAD or i not in adj: continue
        a = adj[i]; row = dict(id=i, published_equivalent=bool(a['correct']) or a['provenance'] != 'unchanged',
                              adjudicated_equivalent=bool(a['correct']), relabel_provenance=a['provenance'],
                              semanteq_verdict=o['verdict'], semanteq_accept=o['verdict'] in ACCEPT)
        if i in prior: row['beqplus_v430_accept'] = prior[i]['beqplus_v430_accept']
        rows.append(row)
    open(os.path.join(RES, 'pnv_test_verdicts.jsonl'), 'w').write('\n'.join(json.dumps(r) for r in rows) + '\n')
    made.append(f"Table 1: {len(rows)} compilable test pairs from fresh runs" + (" (BEq+ column from test/results)" if prior else ""))

# Table 2
ARM_NAMES = ['all_audits', 'no_relevance', 'no_proof_term_grading', 'no_explosion_check', 'no_replay', 'no_audits']
arm = {a: recs(os.path.join(OUT, f'ablation_{a}.jsonl')) for a in ARM_NAMES}
if any(arm.values()):
    cls = {m['id']: m['class'] for m in jl(os.path.join(HERE, 'eval', 'ablation', 'manifest.jsonl'))}
    ids = [i for i in (arm['all_audits'] or next(v for v in arm.values() if v))]
    rows = []
    for i in ids:
        row = dict(id=i, **{'class': cls.get(i, 'pnv')})
        for a in ARM_NAMES:
            if i in arm[a]: row[f'semanteq_{a}_accept'] = arm[a][i].get('verdict') in ACCEPT
        if i in prior_abl: row['beqplus_v430_accept'] = prior_abl[i]['beqplus_v430_accept']; row['beqplus_v48_accept'] = prior_abl[i]['beqplus_v48_accept']
        rows.append(row)
    open(os.path.join(RES, 'ablation_verdicts.jsonl'), 'w').write('\n'.join(json.dumps(r) for r in rows) + '\n')
    made.append(f"Table 2: {len(rows)} pairs, arms present: {[a for a in ARM_NAMES if arm[a]]}" + (" (BEq+ rows from test/results)" if prior_abl else ""))

# Table 3
meta = json.load(open(os.path.join(HERE, 'results', 'capability_meta.json')))
tier = {tag: recs(os.path.join(OUT, f'tier_{tag}.jsonl')) for tag, _ in meta['tiers']}
if tier.get('T0'):
    eq = [json.loads(l)['id'] for l in open(os.path.join(OUT, 'tier_T0_input.jsonl')) if l.strip()]
    rows = []
    for i in eq:
        row = dict(id=i, base_elapsed_s=None, base_accept=False)
        for tag, _ in meta['tiers']:
            o = tier[tag].get(i)
            row[f'{tag}_elapsed_s'] = None if o is None else (o.get('elapsedMs') or 0) / 1000.0
            row[f'{tag}_accept'] = None if o is None else (o.get('verdict') in ACCEPT)
        if row['T0_accept'] is not None: row['base_elapsed_s'], row['base_accept'] = row['T0_elapsed_s'], row['T0_accept']
        if i in prior_cap:
            for k in ('beqplus_v48_elapsed_s', 'beqplus_v48_accept', 'beqplus_v430_elapsed_s', 'beqplus_v430_accept'): row[k] = prior_cap[i][k]
        rows.append(row)
    open(os.path.join(RES, 'capability_verdicts.jsonl'), 'w').write('\n'.join(json.dumps(r) for r in rows) + '\n')
    json.dump(meta, open(os.path.join(RES, 'capability_meta.json'), 'w'), indent=1)
    made.append(f"Tables 5/6: {len(rows)} pairs, tiers present: {[t for t, _ in meta['tiers'] if tier[t]]}" + (" (BEq+ rows from test/results)" if prior_cap else ""))

# Tables 4 and 5
STATUS = {'PASS': 'accepted', 'FAIL': 'rejected', 'SKIP_SORRY': 'skipped', 'ERROR': 'error'}
man = [json.loads(l) for l in open(os.path.join(HERE, 'campaign', 'manifest.jsonl')) if l.strip()]
STYLES = ['unrestricted', 'faithful', 'rewrite', 'expedient']
got = {}
for s in STYLES:
    for mode, suf, key in (('default', '', 'status'), ('strict', '_strict', 'strict_status')):
        for o in jl(os.path.join(OUT, f'campaign_{s}{suf}.jsonl')):
            m = re.search(r'proofs/[^/]+/([^/]+)/+(ref_imp_cand|cand_imp_ref)\.lean$', o.get('file', ''))
            if m: got[(s, m.group(1), m.group(2), key)] = STATUS.get(o.get('verdict'), 'error')
if got:
    rows = []; complete = 0
    for r in man:
        row = {'pair': r['pair'], 'label': r['label'], 'source': r['source']}; ok = True
        for s in STYLES:
            row[s] = {}
            for d in ('ref_imp_cand', 'cand_imp_ref'):
                e = {}
                for key in ('status', 'strict_status'):
                    v = got.get((s, r['pair'], d, key))
                    if v is None: ok = False
                    else: e[key] = v
                row[s][d] = e
        complete += ok; rows.append(row)
    open(os.path.join(RES, 'campaign_manifest.jsonl'), 'w').write('\n'.join(json.dumps(r, ensure_ascii=False) for r in rows) + '\n')
    made.append(f"Tables 3/4: {complete} of {len(rows)} pairs complete in every style and mode (others counted as not accepted)")

print("fresh verdict tables in", RES); [print("  " + m) for m in made]
if not made: print("  nothing found under", OUT); sys.exit(0)
if pnv: table1()
if any(arm.values()): table2()
if tier.get('T0'): table3()
if got:
    campaign('status', "Table 3 — model-written proofs, default mode (pairs both/one/neither)")
    campaign('strict_status', "Table 4 — model-written proofs, strict mode (pairs both/one/neither)")
