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

### `SemantEq/Config.lean`, `SemantEq/Logic.lean` — shared ground
`Config` holds everything read from the environment or the command line, once
at start-up. `Logic` holds the vocabulary both programs grade constants by
(core-logic names, the schematic test, the eliminator test, the bridge-grade
conclusion test), the exception-safe wrappers and the heartbeat scoping.

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
   per-level budget.

Search strength (depth, arm and discovery budgets, deep-search caps) is
exposed as CLI flags; the defaults favor precision and speed.

### `SemantEq/Structural.lean`, `SemantEq/InstancePack.lean` — the structural closer
The antecedent is asserted into the context, its replumbing variants added,
quantified hypotheses forward-instantiated against the locals, the context
saturated, and `solveByElim` run over an explicit lemma list. Instance
packaging constructs a typeclass instance the context does not hold from the
material it does hold (curated moves plus a generated index of Mathlib's
packaging lemmas).

### `SemantEq/Repackage.lean` — the structure-repackaging arm
For pairs whose preambles declare different-but-isomorphic structures: each
side's structure values are rebuilt from the other side's fields (any atom of
the facts pool by definitional equality, nested constructors, one audited
rewrite bridge per field), the antecedent is applied to the repackaged
hypotheses and the conclusion rebuilt. A no-op unless a pair-local structure
occurs in the goal or the antecedent.

### `SemantEq/Arms.lean` — the ladder's arms
Normalization with the restricted simp set, the single-bridge `simp` and `rw`
arms, the bounded multi-step deep search, and the restricted library search.
Every accepting arm replays its transform without the antecedent:
- **Antecedent-free replay** (counterfactual replay) — if the same transform
  still closes the goal without the antecedent, the "correspondence" was
  vacuous and the accept is discarded.

### `SemantEq/Gate.lean` — the relevance audit
- **Relevance audit** (essential-use gate) — the antecedent must do semantic work for *every
  part* of the goal. A candidate that is the real statement conjoined with
  independently-true padding is rejected even though a proof exists; shared
  content carried by *both* statements is explicitly legal. Runs before the
  ladder, so polluted directions are refused instead of searched.

### `SemantEq/Audit.lean` — what an accepted proof may contain
- **Proof-term grading** (proof audit) — the accepted proof term's constants are graded
  categorically: the antecedent must be reached, and everything else must be
  data, an eliminator, logically schematic plumbing, or an
  equality/iff-grade bridge. A proof that imports an unrelated library
  theorem fails, whatever it proves.
- **Explosion check** (polarity-aware ex falso) — proofs that manufacture `False` in
  positive position (deriving the goal from a contradiction rather than a
  correspondence) are rejected; honest proofs of negated goals are not.

### `SemantEq/ProofAudit/` — the ProofChecker (SemantEq-ProofAudit)
The same judgment, packaged for externally written proofs (`--proof`): the
context and constant grading (`Ctx`), the node-level rules (`Rules`), the
proof-term walk (`Walk`), the confiscated-instances reproof (`Reproof`) and the
fixture protocol (`Fixture`). A
fixture provides the assumed statement(s) as `sorry`-proved theorems and the
goal with a real proof (the roles are read from the elaborated file: the
formalization runs up to the antecedent, the proof comes after it); the checker walks the proof with role- and
polarity-aware constant grading, ablates local subproofs to confirm the
antecedent carries the spine (the dependency test is asked of the proof with
its logical detours removed: a function applied to its argument, a `have`, a
lemma of pure logic, the field of a structure that was just built are
reduced first, so a wrapper that takes the antecedent and hands back its
other input is not a use of it; a discarded argument, a proof of `True`, an
unused binder are dead mentions as well),
reads in-file helper lemmas inline at the place they are called, and walks
the equation or biconditional a rewrite is justified by at the role of the
rewrite: a fact used there to meet a side condition is recorded, while a
part of the goal's conclusion equated to `True` there without the antecedent
fails the proof. An equation or a biconditional that the proof assembles
from two implications is read half by half, wherever it stands (a
biconditional used as a justification is brought to head form first, so a
pair of implications packed some other way is read too): each half is an
implication proof of its own, with
its hypothesis in the antecedent's role, and a half proved from a library
fact with neither its hypothesis nor a hypothesis in scope behind it, or
closing a part of the goal without its hypothesis, fails the proof. A
premise handed to any lemma inside a justification fails likewise when it
proves, without the antecedent, a part the goal states outright. The proof that a conversion along the antecedent carries is checked
too: a part the goal states, closed there by a library fact or a
computation, fails, unless that proof is a hypothesis of the goal or a
projection, an application or a rewriting with library equations of one;
a conversion nested in the converted proof is judged the same way, and the
pieces of a library fact taken apart are not hypotheses. A local
fact on the goal's derivation is read by its own proof when it is a
hypothesis in scope in another form (a projection, an application, or the
hypothesis rewritten with library equations); a library fact inside that
proof fails. A statement, or a family of statements, is not a
derivation, so nothing inside a type is graded; a structure assembled on the
spot and handed to the antecedent is read through its fields. Eliminating an empty type or discriminating an absurd
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
`PASS`/`FAIL` with the failing reason, the tolerated uses by kind and the
severe warnings. A proof that depends on an axiom beyond the three standard
ones fails. A library fact whose conclusion is a disequality or a typeclass
is accepted as a step and recorded. One tolerance is deliberate: a library
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
verdict assembly from the two directions, the per-pair wall-clock limit (a
watchdog sets a cancel token that every `runMetaM` hands to Lean's interrupt
check; the pair then reports `Timeout`), and the CLI (batch mode, `--proof`
mode, strength flags).

## The four steps in the two programs

The relation is defined by four kinds of step (Definition 1 of the paper).
The table says where each step appears in the two programs, as Table 4 of
the paper does. The stages are those of the search ladder: 1 direct use, 2
normalisation, 3 logical rearrangement, 4 restricted lemma discovery, 5
bridge rewriting.

| Step | SemantEq-Eval | SemantEq-ProofAudit, what is accepted in the proof term |
|---|---|---|
| Logical rearrangement | Stage 3, which matches the logical components of the two statements, and the logical identities of stage 2 | Introduction and elimination rules of the connectives |
| Bridge rewriting | Stages 4 and 5, which rewrite along library equations and biconditionals | A conversion along a library equation or biconditional |
| Change of variables | Applying the antecedent at objects of the goal, in stages 1 and 3 | An application of the antecedent whose arguments are the goal's own objects |
| Structural weakening | Dropping conjuncts, giving witnesses and adding hypotheses, in stage 3 | The same logical rules as rearrangement |

The audits perform no step. They refuse proofs that are valid in Lean but do
not follow these steps, and the few uses that SemantEq-ProofAudit tolerates
outside them are recorded with each verdict.

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
