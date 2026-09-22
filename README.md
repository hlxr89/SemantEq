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
(the Lean version manager):

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
git clone <this repo> && cd SemantEq
lake exe cache get     # prebuilt Mathlib (~5 GB download)
lake build semanteq # a few minutes
```

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
each direction, the proof that closed it or `null`. The out-file is always
the machine-readable JSONL. Add `--raw` to print the JSONL records on stdout
instead (what the batch scripts consume):

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

Verdicts:

| verdict | meaning |
|---|---|
| `ExactMatch`, `DefEq` | identical up to alpha-equivalence / definitional unfolding |
| `EquivalentRestricted` | both implications proved **and audited** — the headline verdict |
| `LikelyTooStrong` / `LikelyTooWeak` | only one direction holds |
| `Inconclusive` | neither direction closed |
| `*CompileError`, `NotAProposition` | the input itself is the problem |

Search strength is adjustable via CLI flags (equivalently, `SEMANTEQ_*`
environment variables; the pre-rename `STATIC_EVAL_*` names are still honoured):

| flag | default | what it alters |
|---|---|---|
| `--depth N` | 1 | maximum length of multi-step bridge sequences; 1 = single-lemma arms only |
| `--arm-budget N` | 80 | how many top-ranked discovered lemmas become proof arms (each yields a simp arm and a rw arm) |
| `--discovery-budget N` | 64 | lemma-discovery yield per probe site (statement bodies; subterm probes get a quarter) |
| `--lemma-cap N` | 24 | how many pool lemmas the multi-step search may use as steps |
| `--state-cap N` | 24 | frontier width of the multi-step search (states kept per level) |
| `--deep-level-budget N` | 1000000 | work budget (heartbeats) each multi-step level may spend |
| `--heartbeats N` | 100000 | heartbeat cap per proof attempt in the search/closer phase; raise for very large statements (research-grade formalizations), where honest unification can exceed the default |

```bash
lake exe semanteq --depth 2 --arm-budget 160 --discovery-budget 128 \
  --lemma-cap 48 --state-cap 48 --deep-level-budget 4000000 pairs.jsonl out.jsonl
```

Raising these buys additional recall on specific pair classes at increased
runtime; the defaults favor precision and speed.

**Audit an externally written implication proof** (the ProofChecker):

```bash
lake exe semanteq --proof <fixture.lean | directory> ...
```

A fixture is a single file: the assumed statement(s) proved by `sorry`, then
the goal statement with a real proof. The goal is the last theorem that is
not `sorry`-proved; the antecedent is the last `sorry`-proved theorem declared
before it, and any other `sorry`-proved theorem joins the assumed set. A
directory argument audits every `.lean` file in it except `ref.lean` and
`cand.lean` (not recursively). The checker prints the verdict, the reasons of
a `FAIL`, or the severe warnings of a `PASS`; `--raw` prints the full JSON
record with every recorded flag instead. A *severe* warning marks a library
fact that was used to meet a hypothesis of the antecedent while drawing on
nothing local (no hypothesis of the goal); such uses are tolerated, not
failed, and can be counted as failures by the reader.

**Case studies.** `case_studies/` holds the pairs and proofs discussed in the
paper's appendices, one folder each with the statements, the quoted proof or
recorded output, and a `NOTES.md` with the reproduction command and the
expected verdict.

**Run the bundled test suites** (data + expected outcomes + scoring, one
command each):

```bash
./test/eval/run_eval.sh              # recall / pollution / trap suites
./test/proofaudit/run_proofaudit.sh
```

See [`test/README.md`](test/README.md) for what each suite contains.

## Results

Headline numbers from the accompanying paper, all on this toolchain. The
baseline BEq+ is its released implementation ported to the same Lean and
Mathlib versions with no change of method.

| | SemantEq-Eval | BEq+ |
|---|---|---|
| **ProofNetVerif**, 3,100 compilable pairs, test split at adjudicated labels¹ | precision **99.8**, recall **60.1** | precision 96.4, recall 54.1 |
| **100 adversarial non-equivalent pairs** (false accepts) | **0** | 51 |

| | SemantEq-ProofAudit |
|---|---|
| model-written proofs, 410 equivalent pairs, certified in both directions | **332** (326 with severe uses counted as failures) |
| model-written proofs, 101 non-equivalent pairs, certified in both directions | **0** |

¹ We audited the benchmark's test split and corrected 100 labels, every one
from equivalent to non-equivalent; the adjudicated labels are released in
`test/pnv_test_adjudicated_labels.jsonl`. The single false positive of
SemantEq-Eval is a candidate carrying an unused but derivable structure
assumption (`case_studies/H4_munkres_18_8b_evaluator_false_positive`).

The bundled suites reproduce their expected outcomes on the current build:
the ProofChecker corpus 19/19, the trap suite 29/29 rejected, the pollution
suite with its six genuine controls accepted.

Design overview: [`ARCHITECTURE.md`](ARCHITECTURE.md).

## Paper

The accompanying paper defines the SemantEq relation, describes both
programs against it, and reports the evaluation above. `case_studies/`
reproduces every example discussed in its appendices.

## Released data

- `test/pnv_test_adjudicated_labels.jsonl` — the adjudicated labels of the
  ProofNetVerif test split, with the provenance of every changed label.
- `test/` — the public evaluation suites and the proof-audit corpus.
- `case_studies/` — every example discussed in the paper's appendices.
- `test/campaign/` — every model-written implication proof of the campaign
  (four prompt styles, 511 pairs, both directions), the prompts, a manifest
  with the checker's verdict and marks for each, and a runner that re-checks
  a style and prints the paper's table; see its README.

## License

The code is released under the Apache License 2.0 (see `LICENSE`).
Statements derived from public benchmarks (ProofNetVerif, ProofNet,
PutnamBench, Compfiles) remain under their sources' licences; our labels,
curated pairs and case studies carry no separate licence yet.
