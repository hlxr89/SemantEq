# StaticEval

A static evaluator for **Lean 4 autoformalization**: given a *reference*
statement and a *candidate* statement, it decides whether they say the same
thing — semantically, not syntactically.

What sets it apart is **evidence quality**. Every "equivalent" verdict is
backed by machine-checked proofs of both implications, and every proof is
*audited*: it must genuinely use the other statement, and may otherwise use
only pure logic and equality/iff-grade rewriting. A proof that closes any
other way (a decision procedure, an unrelated library theorem, a vacuous
goal) is rejected rather than counted. The same audit is available standalone
as a **ProofChecker** for externally written implication proofs — e.g. proofs
produced by an LLM.

## Setup

Requirements: `git`, a C toolchain (`xcode-select --install` on macOS,
`build-essential` on Linux), and [elan](https://github.com/leanprover/elan)
(the Lean version manager):

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
git clone <this repo> && cd StaticEval
lake exe cache get     # prebuilt Mathlib (~5 GB download)
lake build static_eval # a few minutes
```

The Lean toolchain and Mathlib versions are pinned (`lean-toolchain`,
`lake-manifest.json`); elan installs the right toolchain automatically.
**Earlier Lean toolchains are not supported** — the code targets the pinned
toolchain's APIs, and judgments are only meaningful against the pinned
Mathlib. Linux and macOS are supported. Expect ~9 GB of RAM per running
evaluation process.

## Usage

**Evaluate statement pairs** (JSONL in, JSONL out; results stream as they
finish):

```bash
lake exe static_eval pairs.jsonl results.jsonl
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

Search strength is adjustable via CLI flags (equivalently, `STATIC_EVAL_*`
environment variables):

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
lake exe static_eval --depth 2 --arm-budget 160 --discovery-budget 128 \
  --lemma-cap 48 --state-cap 48 --deep-level-budget 4000000 pairs.jsonl out.jsonl
```

Raising these buys additional recall on specific pair classes at increased
runtime; the defaults favor precision and speed.

**Audit an externally written implication proof** (the ProofChecker):

```bash
lake exe static_eval --proof <fixture.lean | directory> ...
```

A fixture is a single file: the assumed statement(s) proved by `sorry`, then
the goal statement with a real proof. The checker reports `PASS`/`FAIL` with
reasons.

**Run the bundled test suites** (data + expected outcomes + scoring, one
command each):

```bash
./test/eval/run_eval.sh              # recall / pollution / trap suites
./test/proofchecker/run_proofchecker.sh
```

See [`test/README.md`](test/README.md) for what each suite contains.

## Results

All StaticEval numbers are strict-tier (audited proofs of both directions).
BEq+ is the strongest published baseline, run by us on identical inputs in
its own paper-era environment (Lean v4.8); the "on v4.30" column counts only
its accepts whose proofs still elaborate on the current toolchain (after
sympathetic repair of retired tactic syntax) — cross-toolchain evidence
decays, which is itself an argument for checking proofs rather than trusting
past runs.

| benchmark | StaticEval | BEq+ (v4.8) | BEq+ (on v4.30) |
|---|---|---|---|
| **ProofNetVerif** (compilable, label-audited¹: 1047 equivalent / 2017 not) | P **99.8** / R **54.7** | P 99.2 / R 49.1 | P 99.2 / R 45.1 |
| **Recall suite** (40 equivalent pairs, must accept) | **24**/40 | 17/40 | 15/40 |
| **Trap suite** (29 non-equivalent, false accepts) | **0** | 20 | 20 |
| **Pollution suite** (29 laundering attacks, false accepts) | **0** | 22 | 20 |
| Pollution controls (6 genuine pairs, must accept) | 6/6 | 6/6 | — |

¹ Five StaticEval accepts carried a "not equivalent" benchmark label; on
manual audit four are label errors (the pairs are genuinely equivalent —
e.g. `[Nonempty I]` vs an explicit witness argument), counted here as
correct for every system; BEq+ accepts none of them. The single remaining
false positive is a candidate carrying an unused, synthesizable typeclass
assumption. Under the raw labels: StaticEval P 99.1 / R 54.6.

BEq+'s recall-suite accepts are a strict subset of StaticEval's. The
ProofChecker reproduces its expected verdict on 19/19 bundled proof
fixtures — faithful proofs pass; each named deception fails.

Design overview: [`ARCHITECTURE.md`](ARCHITECTURE.md).
