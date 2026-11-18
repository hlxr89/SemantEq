#!/usr/bin/env python3
"""Print the paper's tables from the raw records that test/reproduce.sh wrote (`test/reproduce.sh
tables` calls this). Every number comes from those fresh runs: the records are first distilled
to one line per pair under <out>/results/ (the same schema as test/results/), then the tables are
computed from that. The only rows taken from test/results/ are the BEq+ rows, since our port of
its released implementation is not part of this repository; they are marked as such.

    python3 test/reproduce_tables.py test/reproduce_out
    python3 test/reproduce_tables.py released

With `released` nothing is run and nothing is written: the tables are computed from the records
released in this repository, test/results/ and the manifests of test/campaign/,
test/campaign_neg832/ and test/semanteq_verif/.

The search-strength tables charge a pair the running time of the first configuration that
accepted it, and an unaccepted pair its re-run time at the configuration (or the configuration's
mean re-run time when it was not re-run), as in the paper.
"""
import json, os, re, sys, statistics, collections
HERE = os.path.dirname(os.path.abspath(__file__))
RELEASED = len(sys.argv) > 1 and sys.argv[1] == 'released'
OUT = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'reproduce_out')
RES = os.path.join(HERE, 'results') if RELEASED else os.path.join(OUT, 'results')
if not RELEASED: os.makedirs(RES, exist_ok=True)
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
    print(f"\nTables 10 and 11 — search strength on the {N} equivalent pairs of the certification set")
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
DIRS = ('ref_imp_cand', 'cand_imp_ref')
SETS = {'campaign': 'campaign', 'neg832': 'campaign_neg832', 'verif': 'semanteq_verif'}   # record prefix -> folder
def manifest(name):
    """One row per pair with the checker's verdicts: the released manifest, or the one distilled from fresh records."""
    p = os.path.join(HERE, SETS[name], 'manifest.jsonl') if RELEASED else os.path.join(RES, f'{name}_manifest.jsonl')
    return list(jl(p))
def certified(key):          # directions the checker certifies (key: status = default policy, strict_status = stricter)
    return lambda r, s: sum(1 for d in DIRS if r[s][d].get(key) == 'accepted')
def written(r, s):           # directions whose proof compiled when the model wrote it
    return sum(1 for d in DIRS if r[s][d].get('compiled_when_written', r[s][d].get('status') in ('accepted', 'rejected', 'error')))
def compiles(r, s):          # directions whose proof compiles on this toolchain
    return sum(1 for d in DIRS if r[s][d].get('status') in ('accepted', 'rejected'))
def head(title):
    print(f"\n{title}")
    print(f"  {'':28s} " + " ".join(f"{x:>8s}" for x in ('eq both', 'one', 'neither', 'neq both', 'one', 'neither')) + f"  {'P':>6s} {'R':>6s}")
def line(name, rows, n, both_only=False):
    c = collections.Counter((r['label'], n(r)) for r in rows)
    pos = sum(1 for r in rows if r['label'] == 'equivalent')
    tp, fp = c[('equivalent', 2)], c[('non_equivalent', 2)]
    p, rc, _ = prf(tp, fp, pos - tp)
    cells = [str(c[(lab, k)]) for lab in ('equivalent', 'non_equivalent') for k in (2, 1, 0)]
    if both_only: cells = [cells[0], 'n/a', 'n/a', cells[3], 'n/a', 'n/a']
    print(f"  {name:28s} " + " ".join(f"{x:>8s}" for x in cells) + (f"  {p:6.1f}" if tp + fp else f"  {'n/a':>6s}") + f" {rc:6.1f}")
def styles(rows, n, prefix=''):
    for s in CAMPAIGN_ORDER: line(prefix + s, rows, lambda r, s=s: n(r, s))

def campaign_tables():
    rows = manifest('campaign')
    if not rows: return
    head(f"Table 3, top panel — certification set ({len(rows)} pairs), default policy"); styles(rows, certified('status'))
    head("Table 8, top panel — certification set, stricter policy"); styles(rows, certified('strict_status'))

def full_split_tables():
    first = [r for r in manifest('campaign') if r['source'] == 'ProofNetVerif test split']; rest = manifest('neg832')
    if not first or not rest:
        if not RELEASED: print("\nTables 15, 8 (bottom) and 9 need both the `campaign` and the `neg832` stage")
        return
    rows = first + rest
    judged = list(jl(os.path.join(RES, 'pnv_test_verdicts.jsonl'))) or list(prior.values())
    jr = [dict(label='equivalent' if r['adjudicated_equivalent'] else 'non_equivalent', beq=r.get('beqplus_v430_accept'),
               n=2 if r['semanteq_accept'] else int(str(r['semanteq_verdict']).startswith('LikelyToo'))) for r in judged]
    pos = sum(1 for r in rows if r['label'] == 'equivalent')
    head(f"Table 15 — full ProofNetVerif test split, adjudicated labels ({pos} equivalent, {len(rows) - pos} non-equivalent pairs)")
    line('BEq+ (from test/results)', jr, lambda r: 2 if r['beq'] else 0, both_only=True)
    line('SemantEq-Eval', jr, lambda r: r['n'])
    styles(rows, certified('status'))
    head("Table 8, bottom panel — full test split, stricter policy"); styles(rows, certified('strict_status'))
    pub = [dict(r, label='equivalent') for r in first] + rest
    def pr(rs, n, s):
        tp = sum(1 for r in rs if r['label'] == 'equivalent' and n(r, s) == 2); fp = sum(1 for r in rs if r['label'] != 'equivalent' and n(r, s) == 2)
        return prf(tp, fp, sum(1 for r in rs if r['label'] == 'equivalent') - tp)
    print(f"\nTable 9 — full test split under the published labels ({len(first)} equivalent, {len(rest)} non-equivalent pairs)")
    print(f"  {'':13s} {'prover alone P':>15s} {'P default / strict':>20s} {'R default / strict':>20s} {'prover alone P, adjudicated':>29s}")
    for s in CAMPAIGN_ORDER:
        a, d, st, adj = pr(pub, written, s), pr(pub, certified('status'), s), pr(pub, certified('strict_status'), s), pr(rows, written, s)
        print(f"  {s:13s} {a[0]:15.1f} {d[0]:11.1f} / {st[0]:5.1f} {d[1]:12.1f} / {st[1]:5.1f} {adj[0]:29.1f}")

def verif_tables():
    rows = manifest('verif')
    judged = list(jl(os.path.join(RES, 'semanteq_verif_verdicts.jsonl'))) or list(jl(os.path.join(HERE, 'results', 'semanteq_verif_verdicts.jsonl')))
    if judged:
        print(f"\nTable 1, second section — SemantEq-Verif, {len(judged)} pairs")
        print(f"  {'system':12s} {'TP':>4s} {'FP':>4s} {'FN':>4s} {'TN':>5s} {'P':>6s} {'R':>6s} {'F1':>6s}")
        for sys_name, acc in (('Ours', 'semanteq_accept'), ('BEq+ v4.30', 'beqplus_v430_accept')):
            tp = sum(1 for r in judged if r[acc] and r['correct']); fp = sum(1 for r in judged if r[acc] and not r['correct'])
            fn = sum(1 for r in judged if not r[acc] and r['correct']); tn = len(judged) - tp - fp - fn
            p, rc, f = prf(tp, fp, fn)
            print(f"  {sys_name:12s} {tp:4d} {fp:4d} {fn:4d} {tn:5d} {p:6.1f} {rc:6.1f} {f:6.1f}")
    if not rows: return
    for title, parts in (("Table 17 (its first two groups are the bottom panel of Table 3) — SemantEq-Verif, all pairs", None),
                         ("Table 18 — SemantEq-Verif, IMO and Putnam part", ('IMO', 'Putnam')), ("Table 19 — SemantEq-Verif, Erdős part", ('Erdős',))):
        sub = [r for r in rows if parts is None or r['source'] in parts]
        jr = [dict(label='equivalent' if r['correct'] else 'non_equivalent', beq=r['beqplus_v430_accept'], n=r['semanteq_directions'])
              for r in judged if parts is None or r['part'] in parts]
        pos = sum(1 for r in sub if r['label'] == 'equivalent')
        head(f"{title} ({pos} equivalent, {len(sub) - pos} non-equivalent)")
        if jr:
            line('BEq+ (from test/results)', jr, lambda r: 2 if r['beq'] else 0, both_only=True)
            line('SemantEq-Eval', jr, lambda r: r['n'])
        styles(sub, certified('status'), 'default, '); styles(sub, certified('strict_status'), 'stricter, '); styles(sub, compiles, 'prover alone, ')

if RELEASED:
    table1(); table2(); table3(); campaign_tables(); full_split_tables(); verif_tables(); sys.exit(0)

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

# Tables 10 and 11
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
    made.append(f"Tables 10/11: {len(rows)} pairs, tiers present: {[t for t, _ in meta['tiers'] if tier[t]]}" + (" (BEq+ rows from test/results)" if prior_cap else ""))

# The model-proof tables: one manifest per proof set, in the schema of the released ones
STATUS = {'PASS': 'accepted', 'FAIL': 'rejected', 'SKIP_SORRY': 'skipped', 'ERROR': 'error'}
STYLES = ['unrestricted', 'faithful', 'rewrite', 'expedient']
def distil(name, keep=()):
    """Fresh checker records of one proof set -> <out>/results/<name>_manifest.jsonl. `keep` names the fields
    copied from the released manifest because a re-run cannot produce them."""
    man = list(jl(os.path.join(HERE, SETS[name], 'manifest.jsonl')))
    got = {}
    for s in STYLES:
        for suf, key in (('', 'status'), ('_strict', 'strict_status')):
            for o in jl(os.path.join(OUT, f'{name}_{s}{suf}.jsonl')):
                m = re.search(r'proofs/[^/]+/([^/]+)/+(ref_imp_cand|cand_imp_ref)\.lean$', o.get('file', ''))
                if m: got[(s, m.group(1), m.group(2), key)] = STATUS.get(o.get('verdict'), 'error')
    if not got: return False
    rows = []; complete = withheld = 0
    for r in man:
        row = {'pair': r['pair'], 'label': r['label'], 'source': r['source']}; ok = True
        for s in STYLES:
            row[s] = {}
            for d in DIRS:
                if r.get('proofs_released') is False:      # proofs not redistributed: the released verdicts stand
                    e = {k: r[s][d][k] for k in ('status', 'strict_status')}
                else:
                    e = {}
                    for key in ('status', 'strict_status'):
                        v = got.get((s, r['pair'], d, key))
                        if v is None: ok = False
                        else: e[key] = v
                for k in keep:
                    if k in r[s][d]: e[k] = r[s][d][k]
                row[s][d] = e
        withheld += r.get('proofs_released') is False; complete += ok; rows.append(row)
    open(os.path.join(RES, f'{name}_manifest.jsonl'), 'w').write('\n'.join(json.dumps(r, ensure_ascii=False) for r in rows) + '\n')
    made.append(f"proof set {SETS[name]}: {complete} of {len(rows)} pairs complete in every style and mode (others counted as not accepted)"
                + (f"; {withheld} pairs without redistributed proofs keep their released verdicts" if withheld else ""))
    return True
got = distil('campaign')
got_neg = distil('neg832', keep=('compiled_when_written',))
got_verif = distil('verif')

# SemantEq-Verif, the two judges
verif_eval = recs(os.path.join(OUT, 'verif_eval.jsonl'))
if verif_eval:
    rel = {r['id']: r for r in jl(os.path.join(HERE, 'results', 'semanteq_verif_verdicts.jsonl'))}
    rows = []; kept = 0
    for i, r in rel.items():
        o = verif_eval.get(i)
        if o is None: rows.append(r); kept += 1; continue        # not run here (candidate not fetched, or set aside)
        v = o.get('verdict'); n = 2 if v in ('ExactMatch', 'DefEq') else sum(1 for d in (o.get('directions') or {}).values() if d.get('closed'))
        rows.append(dict(id=i, part=r['part'], correct=r['correct'], semanteq_verdict=v, semanteq_directions=n,
                         semanteq_accept=v in ACCEPT, beqplus_v430_accept=r['beqplus_v430_accept']))
    open(os.path.join(RES, 'semanteq_verif_verdicts.jsonl'), 'w').write('\n'.join(json.dumps(r, ensure_ascii=False) for r in rows) + '\n')
    made.append(f"SemantEq-Verif: {len(rows) - kept} pairs from fresh runs (BEq+ column from test/results)" + (f"; {kept} pairs not run here keep their released verdict" if kept else ""))

print("fresh verdict tables in", RES); [print("  " + m) for m in made]
if not made: print("  nothing found under", OUT); sys.exit(0)
if pnv: table1()
if any(arm.values()): table2()
if tier.get('T0'): table3()
if got: campaign_tables()
if got or got_neg: full_split_tables()
if got_verif or verif_eval: verif_tables()
