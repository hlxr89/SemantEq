# SemantEq

Semantic equivalence of **Lean 4 formal statements**, for judging
autoformalization: given a *reference* statement and a *candidate* statement,
decide whether they say the same thing — semantically, not syntactically.

**SemantEq** is an equivalence relation on formal statements that is strictly
finer than logical equivalence: two statements are SemantEq when each turns
into the other by a chain of four meaning-preserving actions (logical
rearrangement, rewriting along the library's own equations and
biconditionals, change of variables, and structural weakening), so that no
step proves anything and no library theorem can supply a conclusion. This
repository realises the relation in two programs:

- **SemantEq-Eval** (`lake exe semanteq pairs.jsonl`) searches for such
  chains. Every "equivalent" verdict is backed by machine-checked proofs of
  both implications, and every proof is *audited*: it must genuinely use the
  other statement, and may otherwise use only pure logic and equality/iff-grade
  rewriting. A proof that closes any other way (a decision procedure, an
  unrelated library theorem, a vacuous goal) is rejected rather than counted.
- **SemantEq-ProofAudit** (`lake exe semanteq --proof`) applies the same
  standard to an implication proof written by anyone — e.g. an LLM prover —
  so a model's search can be used without trusting the model.

## Setup

Requirements: `git`, a C toolchain (`xcode-select --install` on macOS,
`build-essential` on Linux), and [elan](https://github.com/leanprover/elan)
(the Lean version manager). There are two ways to install.

**As its own project**, when the statements you want to judge import only
Mathlib:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
git clone <this repo> && cd SemantEq
lake exe cache get     # prebuilt Mathlib (~5 GB download)
lake build semanteq # a few minutes
```

**As a dependency of your own Lean project**, when the statements or proofs
mention your project's definitions. Add to your `lakefile.toml`:

```toml
[[require]]
name = "SemantEq"
git = "<this repo>"
rev = "v1.4.2"
```

then `lake build` in your project (and `lake exe cache get` if your project
does not already have Mathlib built). Both programs then run from your
project root, `lake exe semanteq ref.lean cand.lean` and `lake exe semanteq
--proof file.lean`, and the files may import your own modules next to
Mathlib:

```lean
import Mathlib
import MyProject.Basic

theorem r (n : ℕ) : MyProject.myPred n ↔ Even n := sorry
```

Your project must use the same Lean toolchain and Mathlib commit as this
one (Lake builds SemantEq against your project's Mathlib). This route was
checked with a small project that defines its own predicate and judges a
pair of statements over it.

The Lean toolchain and Mathlib versions are pinned (`lean-toolchain` pins
Lean v4.30.0-rc1; `lake-manifest.json` pins the Mathlib commit, which is the
`v4.30.0-rc1` tag); elan installs the right toolchain automatically and
`lake exe cache get` downloads the prebuilt Mathlib for exactly that commit.
Do not run `lake update`, which would move the pins.
**Earlier Lean toolchains are not supported** — the code targets the pinned
toolchain's APIs, and judgments are only meaningful against the pinned
Mathlib. Linux and macOS are supported. Expect ~9 GB of RAM per running
evaluation process with `import Mathlib`; statements that import only the
Mathlib modules they need run in a correspondingly smaller environment (a few
GB, seconds of start-up). Note that bridge lemmas outside the imported modules
are then not available to the search.

## Usage

**Evaluate statement pairs** (JSONL in, JSONL out; results stream as they
finish):

```bash
lake exe semanteq pairs.jsonl results.jsonl
```

By default stdout shows a readable summary per pair, the verdict and, for
each direction, the proof that closed it, or one line on why it did not
close (the last proof an audit refused, or how many attempts found no proof). The out-file is always
the machine-readable JSONL. Each pair gets 20 seconds of wall-clock time by
default; a pair that runs over reports `Timeout` instead of a judgement
(`--timeout N` sets the limit in seconds, `--timeout 0` removes it; most pairs
finish in a few seconds, the long tail is what the limit cuts). The limit is
enforced during the search; compiling the two statements is not interrupted,
so a pair can overrun by its compile time. Add `--raw` to
print the JSONL records on stdout instead (what the batch scripts consume):

```bash
lake exe semanteq --raw pairs.jsonl results.jsonl
```

For a single pair, two raw Lean files can be given instead of a JSONL file
(exactly two arguments, both ending in `.lean`); each file is read as one
side, judged through the same pipeline, and the result is printed to stdout:

```bash
lake exe semanteq ref.lean cand.lean
```

Input, one pair per line:

```json
{"id": "my-pair", "reference": "import Mathlib\ntheorem r : ... := sorry",
                  "candidate": "import Mathlib\ntheorem c : ... := sorry"}
```

**What a side must look like.** Each of `reference` and `candidate` (or each
of the two `.lean` files) is the full text of one Lean file:

1. an import header (`import Mathlib`, plus your own modules when installed
   as a dependency);
2. an optional preamble: `open`, `variable`, `set_option`, and any helper
   `def`, `abbrev` or `notation` the statement needs. Helper definitions are
   unfolded for the comparison, so two sides that package the same claim
   behind different local definitions still match;
3. **the statement, which is the last declaration in the file.** Its type is
   what gets judged; its proof is ignored, so `:= sorry` is fine and usual.
   Anything after it is not allowed, and a file whose last declaration is a
   `def` reports `NotAProposition`.

Names are free: the theorem can be called anything, and the two sides may
use the same name, since each side is elaborated in its own namespace and the
two preambles are merged into one environment. A side that does not compile
reports a `*CompileError` with Lean's messages.

Verdicts:

| verdict | meaning |
|---|---|
| `ExactMatch`, `DefEq` | identical up to alpha-equivalence / definitional unfolding |
| `EquivalentRestricted` | both implications proved **and audited** — the headline verdict |
| `LikelyTooStrong` / `LikelyTooWeak` | only one direction holds |
| `Inconclusive` | neither direction closed |
| `Timeout` | the pair ran past the wall-clock limit before being accepted (`--timeout`) |
| `*CompileError`, `NotAProposition` | the input itself is the problem |
| `MalformedInput`, `*NoStatement`, `ContextMergeError`, `InternalError` | a line is not pair JSON; a side has no final declaration; the two sides' headers or preambles cannot be merged into one environment (details under `context`); an internal invariant failed (details under `errors`) |

Search strength is adjustable via CLI flags (equivalently, `SEMANTEQ_*`
environment variables; a flag overrides the variable). An on/off switch
(`SEMANTEQ_STRICT`, `SEMANTEQ_TRACE`, the `SEMANTEQ_NO_*` ablation switches) is
on when set to anything but an empty string, `0` or `false`:

| flag | default | what it alters |
|---|---|---|
| `--depth N` | 1 | maximum length of multi-step bridge sequences; 1 = single-lemma arms only |
| `--arm-budget N` | 80 | how many top-ranked discovered lemmas become proof arms (each yields a simp arm and a rw arm) |
| `--discovery-budget N` | 64 | lemma-discovery yield per probe site (statement bodies; subterm probes get a quarter) |
| `--lemma-cap N` | 24 | how many pool lemmas the multi-step search may use as steps |
| `--state-cap N` | 24 | frontier width of the multi-step search (states kept per level) |
| `--deep-level-budget N` | 1000000 | work budget (heartbeats) each multi-step level may spend |
| `--heartbeats N` | 100000 | heartbeat cap per proof attempt in the search/closer phase; raise for very large statements (research-grade formalizations), where honest unification can exceed the default |
| `--timeout N` | 20 | wall-clock limit per pair in seconds; a pair over it reports `Timeout`; 0 disables. The paper's runs and the reproduction scripts use 0 |

```bash
lake exe semanteq --depth 2 --arm-budget 160 --discovery-budget 128 \
  --lemma-cap 48 --state-cap 48 --deep-level-budget 4000000 pairs.jsonl out.jsonl
```

Raising these buys additional recall on specific pair classes at increased
runtime; the defaults favor precision and speed.

Two further variables: `SEMANTEQ_MAX_ENVS` (default 4) caps the number of
distinct import environments one process may build (each costs gigabytes),
and `SEMANTEQ_TRACE=1` prints the search's progress on stderr. The ablation
switches turn one audit off, for the paper's ablation only: for the
evaluator `SEMANTEQ_NO_PREGATE`, `SEMANTEQ_NO_ESSENTIAL` (relevance),
`SEMANTEQ_NO_P0` (explosion check), `SEMANTEQ_NO_PROOFAUDIT` (proof-term
grading), `SEMANTEQ_NO_REPLAY` (antecedent-free replay); for the checker
`SEMANTEQ_NO_REPLAY_LOCAL_FACTS`, `SEMANTEQ_NO_WITNESS_CHECK`,
`SEMANTEQ_NO_CONJUNCT_ABLATION`, `SEMANTEQ_NO_CONJUNCT_SURFACE`,
`SEMANTEQ_NO_SIMPLIFY` (judge the use of the antecedent on the proof as
written), `SEMANTEQ_NO_HALVES` and `SEMANTEQ_NO_HALF_CONTENT` (the reading of
the two halves of an equivalence), `SEMANTEQ_NO_FROZEN_SPINE` (the check on a
proof converted along the antecedent), `SEMANTEQ_NO_NE_CLASS_RECORD`,
`SEMANTEQ_NO_SKIP_STATEMENTS`, `SEMANTEQ_NO_TRANSPARENT_RECORD`,
`SEMANTEQ_NO_LOCAL_FACT_READ`, `SEMANTEQ_NO_PREMISE_RULE` (the check on
the premises of every lemma inside a justification),
`SEMANTEQ_NO_HALF_EQUATION_FACT` (a library equation used as a fact counts
as a library fact in the reading of halves), `SEMANTEQ_NO_LIBRARY_PRODUCTS`
(a library fact taken apart is not a hypothesis), `SEMANTEQ_NO_NEG_POLARITY`
(the argument of a negated hypothesis is judged one negation lower), and
`SEMANTEQ_AUDIT_TRACE=1` for its per-decision trace.

**Audit an externally written implication proof** (the ProofChecker):

```bash
lake exe semanteq [--strict] --proof <fixture.lean | directory> ...
```

A fixture is a single file, written like this:

```lean
import Mathlib

-- the antecedent: the statement being assumed, closed with sorry
theorem cand_assumed (n : ℕ) : 2 ∣ n ↔ Even n := by
  sorry

-- the goal: the statement to be derived, with the proof to be audited
theorem ref (n : ℕ) : Even n ↔ 2 ∣ n := by
  exact (cand_assumed n).symm
```

The rules that pick the two roles:

- **The goal is the last `theorem` or `lemma` in the file that is not closed
  with `sorry`.** Its proof is what gets audited.
- **The antecedent is the last `sorry`-closed `theorem` or `lemma` declared
  before the goal.** Names are free; `_assumed` is only a convention.
- **The file has two parts.** Everything up to and including the antecedent
  is the formalization. A `sorry`-closed theorem declared there, other than
  the antecedent, is an assumed statement: a lemma the formalization itself
  leaves open, which the proof may use and which is judged by the shape of
  its statement. Everything after the antecedent is the proof, and its last
  theorem with a real proof is the goal. Keep `sorry` out of that part: a
  `sorry` inside the goal's proof gives `SKIP_SORRY`, and a `sorry`-closed
  theorem placed between the intended antecedent and the goal is read as
  the antecedent.
- The roles are read from the elaborated file, so a theorem may sit inside a
  `namespace` or `section` and may carry attributes or `private`. An import
  header, `open` lines and helper definitions are fine, and in-file helper
  lemmas with real proofs are allowed and are audited at the place they are
  used.
- One fixture checks one implication. A pair needs two fixtures, one with the
  reference assumed and the candidate as the goal, one the other way round,
  and the pair counts as certified only when both pass.

A directory argument audits every `.lean` file in it except `ref.lean` and
`cand.lean` (not recursively); `test/proofaudit/pairs/` and
`test/campaign/proofs/` are full examples of this layout. The checker prints the verdict, the reasons of
a `FAIL`, the tolerated uses counted by kind and every severe warning in
full; `--raw` prints the full JSON record with every recorded flag instead.
A proof that depends on an axiom beyond `propext`, `Classical.choice` and
`Quot.sound` (a local `axiom`, or the one `native_decide` introduces) fails,
and the axiom is named; the `sorryAx` of the assumed statements is expected. A *severe* warning marks a library
fact that was used to meet a hypothesis of the antecedent while drawing on
nothing local (no hypothesis of the goal); such uses are tolerated, not
failed. The proof of every local restatement admitted on the shape of its
statement (`have h : A ↔ B := …`, or an in-file lemma) is read at the place
it is used, and so is every equation or biconditional a proof converts
along. Inside them, the two implications an equivalence is assembled from
are read as implication proofs of their own: where they stand as arguments
of a lemma that concludes `=` or `↔`, each an implication from one side of
that conclusion to the other (`Iff.intro`, an antisymmetry lemma),
and where a biconditional handed to such a lemma (`propext`) or converted
along reduces to such a pair. A half that proves a part of the goal without
its hypothesis, or that is proved from a library fact (a library equation
used as a fact included) using neither its hypothesis nor any hypothesis in
scope, fails the proof. So does a premise handed to any lemma inside such a
justification when it proves, without the antecedent, a part the goal
states outright. Whether a part of
the proof uses the antecedent is judged after its logical detours are
removed, so a wrapper that takes the antecedent and hands back its other
input does not count as a use. The reduction has a work limit, and a proof
that exhausts it fails with that reason. A local fact (`have h : P := …`)
used on the way to the goal is read by its own proof when it is a
hypothesis in scope in another form (a projection, an application, or the
hypothesis rewritten with library equations), and a library fact inside
that proof fails; any other local fact is refused where it is used. A
library fact taken apart (`obtain ⟨t⟩ := …`, a `match`) stays the
library's fact: its pieces are not hypotheses of the goal. A library
fact whose conclusion is a disequality or a typeclass is accepted as a step
and recorded; one that meets a hypothesis of the antecedent is recorded like
any other, a fact taken out of a typeclass instance included. `--strict` (or `SEMANTEQ_STRICT=1`) is
the strict reading of the definition as a mode: every severe use fails the
proof, at the top level and inside such local proofs alike. The paper's
strict table is the output of this mode.

**Case studies.** `case_studies/` holds the pairs and proofs discussed in the
paper's appendices, one folder each with the statements, the quoted proof or
recorded output, and a `NOTES.md` with the reproduction command and the
expected verdict.

**Run the bundled test suites** (data + expected outcomes + scoring, one
command each):

```bash
./test/eval/run_eval.sh              # recall / ablation suites
./test/proofaudit/run_proofaudit.sh
```

See [`test/README.md`](test/README.md) for what each suite contains.

## Results

Headline numbers from the accompanying paper, all on this toolchain. The
baseline BEq+ is its released implementation ported to the same Lean and
Mathlib versions with no change of method.

| | SemantEq-Eval | BEq+ (v4.30 port) |
|---|---|---|
| **ProofNetVerif test split**, 1,303 compilable pairs, published labels | precision **100.0**, recall **51.4** | precision 96.6, recall 48.8 |
| same pairs, adjudicated labels¹ | precision **100.0**, recall **65.6** | precision 95.8, recall 61.8 |
| **Ablation set**, 100 non-equivalent pairs² (false accepts) | **0** | 54 |
| **SemantEq-Verif**, 226 pairs³ | precision **100.0**, recall **25.0** | precision 100.0, recall 22.8 |

| | SemantEq-ProofAudit |
|---|---|
| model-written proofs, 407 equivalent pairs, certified in both directions | **336** under the best of four prompts (329 in `--strict` mode) |
| model-written proofs, 104 non-equivalent pairs, certified in both directions | **0** |
| model-written proofs for the full ProofNetVerif test split, 1,303 pairs, by prompt | precision 89.7 to 96.3, recall 77.5 to 82.9 (93.2 to 97.6 and 76.2 to 81.3 in `--strict` mode) |
| model-written proofs for SemantEq-Verif³, by prompt | precision 85.7 to 92.9, recall 47.8 to 56.5 (95.5 to 100.0 and 42.4 to 48.9 in `--strict` mode) |

¹ We audited every label of the benchmark's test split and changed 102, every
one from equivalent to non-equivalent; the adjudicated labels are released in
`test/pnv_test_adjudicated_labels.jsonl`. Both systems are scored on both
label sets.

² Fifty ProofNetVerif test-split pairs labelled non-equivalent after
adjudication, including every pair BEq+ accepts on that split, and fifty
constructed pairs, one class for each failure mode of the paper's Section 2
(`test/eval/ablation/`). Removing all four audits from SemantEq-Eval admits
35 of the 100; the restricted move vocabulary alone still rejects 20 of the
54 pairs BEq+ accepts.

³ A second benchmark of 226 labelled pairs on IMO, Putnam and Erdős problems,
with one label set (`test/semanteq_verif/`).

The bundled suites reproduce their expected outcomes on the current build:
the ProofChecker corpus 31/31 in both modes, the 50 constructed pairs of the ablation
suite all rejected, the recall suite at its recorded verdicts (24 of its 38
equivalent pairs accepted by the default search, its 2 non-equivalent pairs
rejected).

Design overview: [`ARCHITECTURE.md`](ARCHITECTURE.md).

## Paper

The accompanying paper defines the SemantEq relation, describes both
programs against it, and reports the evaluation above. `case_studies/`
reproduces the case studies discussed in its appendices.

## Released data

- `test/pnv_test_adjudicated_labels.jsonl` — the adjudicated labels of the
  ProofNetVerif test split, marking which labels were changed.
- `test/` — the public evaluation suites and the proof-audit corpus.
- `case_studies/` — the case studies discussed in the paper's appendices.
- `test/campaign/` — every model-written implication proof of the campaign
  (four prompt styles, 511 pairs, both directions), the prompts, a manifest
  with the checker's verdict and marks for each in default and in strict
  mode, and a runner that re-checks a style and prints the paper's table;
  see its README.
- `test/campaign_neg832/` — the same for the 832 test pairs that
  ProofNetVerif labels not equivalent, so that the two folders cover the full
  test split.
- `test/semanteq_verif/` — SemantEq-Verif: the 226 pairs, how they were
  built, the model-written proofs and the checker's verdicts. Thirty-eight
  candidates come from a repository without a licence and are rebuilt by a
  fetch script; see its README.
- `test/results/` — the per-pair record behind the paper's tables, one line per
  pair: the verdict of SemantEq-Eval and of the BEq+ port on the
  ProofNetVerif test split under both label sets, of the six ablation arms
  on the ablation set, of every search configuration on the equivalent
  pairs of the certification set with its running time, and of both judges
  on SemantEq-Verif. The BEq+ verdicts are the only part of the paper's
  numbers that the reproduction below cannot regenerate.

**Reproducing the tables from scratch.** `test/reproduce.sh` re-runs the
programs on the released statements and proofs, stage by stage, and
`test/reproduce.sh tables` prints the paper's tables from the fresh records:

```bash
python3 test/pnv_fetch.py                  # ProofNetVerif from Hugging Face (needs `datasets`)
test/reproduce.sh corpus                   # both modes, ~10 min
test/reproduce.sh suites                   # ~30 min
LANES=3 test/reproduce.sh ablation         # Table 2,  ~2 h (+6 h for the ProofNetVerif half)
LANES=3 test/reproduce.sh campaign         # top panels of Tables 3 and 8, ~1.5 h
LANES=3 test/reproduce.sh neg832           # Tables 15, 8 (bottom panel) and 9
python3 test/semanteq_verif/fetch_second_formalizations.py   # the 38 candidates that are not redistributed
LANES=3 test/reproduce.sh verif            # Tables 1 (second section), 3 (bottom panel), 17 to 19
LANES=3 test/reproduce.sh pnv              # Table 1,  ~4 h
LANES=3 test/reproduce.sh tiers            # Tables 10 and 11, days (TIER_ONLY='T0|d1w1|T1' for the excerpt rows)
test/reproduce.sh tables
```

`python3 test/reproduce_tables.py released` prints the same tables from the
records released in this repository, without running anything. The scripts
cover Tables 1 to 3, 8 to 11, 15 and 17 to 19 of the paper.

Each lane holds about 8 GB; every stage is chunked and resumable, and a
pair that stalls a chunk is set aside and reported. The scripts run the
evaluator with its per-pair time limit off (`--timeout 0`), as the paper's
runs did; with the default 20-second limit, ten of the 266 pairs the search
accepts on the equivalent pairs of the certification set would report `Timeout` instead. The ProofNetVerif
statements themselves are not redistributed; `test/pnv_fetch.py` rebuilds
the pair files from the public dataset under the ids used here. The BEq+
rows come from our port of its released implementation, which is not part
of this repository; the fresh tables copy them from `test/results/` and
mark them as copied.

## License

The code is released under the Apache License 2.0 (see `LICENSE`).
Statements derived from public benchmarks (ProofNetVerif, ProofNet,
PutnamBench, Compfiles) remain under their sources' licences; our labels,
curated pairs and case studies carry no separate licence yet.
