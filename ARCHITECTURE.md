# SemantEq — architecture

How the evaluator decides that two Lean statements say the same thing, module
by module. This is a design overview; the source files carry the details.

## Pipeline at a glance

```
pair (ref, cand)
  → compile gate            (each side must elaborate on its own)
  → branched environments   (shared base; each side's statement in its own branch)
  → statement comparison    (α-equivalence, definitional equality)
  → implication search ×2   (ref→cand and cand→ref, in isolated proving envs)
  → audits                  (every accepted proof is judged, not just checked)
  → verdict
```

## Modules

### `SemantEq/Compile.lean` — the compile gate
Each side of the pair is elaborated in isolation first. A side that fails to
compile short-circuits the pair with a `*CompileError` verdict — nothing
downstream ever guesses at malformed input. Compilation states are kept so
later stages can resume them instead of re-elaborating.

### `SemantEq/Context.lean` — branched environments
Both sides' imports are unioned into one base environment; each side's local
definitions (its *preamble*) are elaborated exactly once; each side's final
statement is then added in its own branch by resuming that side's elaboration
state. The result: a comparison environment where both statements coexist
(namespaced, so same-named locals cannot clash), and two *proving*
environments — each containing one side's statement as a genuine named
theorem plus only the *preamble* of the other side. The statement being
proved is structurally absent from its own proving environment, so
self-reference is impossible by construction rather than by policy.

### `SemantEq/Statement.lean` — extraction and comparison
Extracts each side's final statement, canonicalizes it (local definitions
unfolded, derivable duplicate instance binders dropped), and compares:
α-equivalence yields `ExactMatch`, definitional equality yields `DefEq`, and
anything past that goes to the implication search.

### `SemantEq/Search.lean` — the search ladder (SemantEq-Eval)
Each direction proves "target follows from the other statement" through a
tiered ladder:

1. **Cheap closers** — apply the antecedent directly; a structural
   intro/elim/reassembly closer (`solveByElim`-based); a normalization pass;
   an instance-tolerant application that turns unsatisfied typeclass
   arguments into goals and closes them structurally.
2. **Lemma discovery** — a rewrite-index search over both statements (their
   bodies and the domains of their binders) collects candidate *bridge*
   lemmas: equality/iff-shaped facts that can carry one statement's phrasing
   into the other's. Candidates concluding anything else are excluded, and
   both statements' own constants are forbidden — the pool is vocabulary,
   never content.
3. **Single-bridge arms** — each discovered lemma is tried as a targeted
   `simp` arm and as a `rw` arm over hypotheses and target, followed by the
   structural closer.
4. **Bounded multi-step search** — sequences of bridge applications explored
   breadth-first with strict caps on depth, vocabulary, frontier width, and
   per-level budget. Optionally, each intermediate state can be re-probed for
   fresh bridge lemmas, letting the vocabulary grow along the path.

Search strength (depth, arm and discovery budgets, deep-search caps) is
exposed as CLI flags; the defaults favor precision and speed.

### `SemantEq/RestrictedSearch.lean` — closers and audits
The engine room: the structural closer, the rewrite/normalization arms, the
instance-packaging machinery (constructing missing typeclass instances from
material already in context), and the audit stack that judges every accepted
proof:

- **Relevance audit** (essential-use gate) — the antecedent must do semantic work for *every
  part* of the goal. A candidate that is the real statement conjoined with
  independently-true padding is rejected even though a proof exists; shared
  content carried by *both* statements is explicitly legal. Runs before the
  ladder, so polluted directions are refused instead of searched.
- **Proof-term grading** (proof audit) — the accepted proof term's constants are graded
  categorically: the antecedent must be reached, and everything else must be
  data, an eliminator, logically schematic plumbing, or an
  equality/iff-grade bridge. A proof that imports an unrelated library
  theorem fails, whatever it proves.
- **Explosion check** (polarity-aware ex falso) — proofs that manufacture `False` in
  positive position (deriving the goal from a contradiction rather than a
  correspondence) are rejected; honest proofs of negated goals are not.
- **Antecedent-free replay** (counterfactual replay) — every accepting transform is replayed *without*
  the antecedent; if it still closes, the "correspondence" was vacuous and
  the accept is discarded.

### `SemantEq/ProofAudit.lean` — the ProofChecker (SemantEq-ProofAudit)
The same judgment, packaged for externally written proofs (`--proof`). A
fixture provides the assumed statement(s) as `sorry`-proved theorems and the
goal with a real proof; the checker walks the proof with role- and
polarity-aware constant grading, ablates local subproofs to confirm the
antecedent carries the spine (the dependency test ignores dead mentions of
the antecedent — a discarded argument, a proof of `True`, an unused binder),
reads in-file helper lemmas inline at the place they are called, and walks
the equation or biconditional a rewrite is justified by at the role of the
rewrite: a fact used there to meet a side condition is recorded, while a
part of the goal's conclusion equated to `True` there without the antecedent
fails the proof. Eliminating an empty type or discriminating an absurd
equation counts as ex falso like `False.elim`. It finishes with an
adversarial reproof: the
proof's own ante-free constructions and ante-free local facts, wherever they
sit in the proof (inside case splits and lambdas included), are granted, and
if the goal then closes without the antecedent, the proof is rejected as
evidence. At every application of the antecedent the arguments are audited:
a witness supplied for an existential hypothesis of the antecedent must be
built from the goal's own variables or be a closed term the goal statement
mentions; a witness conjured from nowhere (`n := 0` when the goal's own
hypothesis already provides the object) fails the proof. Verdicts are
`PASS`/`FAIL` with the failing reason, the tolerated uses by kind, the severe
warnings, and any axiom beyond the three standard ones that the proof depends
on. One tolerance is deliberate: a library
fact that meets a hypothesis of the antecedent is recorded as a warning
rather than failed (marked *severe* when it draws on nothing local), because
Mathlib states many identifications in one direction only. The proof of every
local restatement admitted on the shape of its statement is read as well, each
direction as an implication proof of its own with its hypothesis in the
antecedent's role, so a direction proved without its hypothesis fails.
`--strict` turns the tolerance off (every severe use fails, inside such proofs
too).

### `SemantEq/Driver.lean`, `Main.lean` — orchestration
Batch processing with per-pair streaming (each result is flushed the moment
its pair finishes, so interrupted runs lose at most the pair in flight),
verdict assembly from the two directions, and the CLI (batch mode, `--proof`
mode, strength flags).

## Design principles

- **Acceptance is faithfulness, not provability.** Both sides being true is
  not evidence they say the same thing; every audit exists to break some way
  of exploiting that gap.
- **Restriction over recovery.** The move vocabulary is small and
  equality-shaped by design; power is added as new, separately-audited
  attempts rather than by loosening existing ones.
- **Structural impossibility over policing.** Where possible, illegitimate
  proofs are made unrepresentable (the target statement is absent from its
  own proving environment) rather than detected after the fact.
