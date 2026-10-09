import SemantEq.ProofAudit.Ctx
import SemantEq.ProofAudit.Rules
import SemantEq.ProofAudit.Walk
import SemantEq.ProofAudit.Reproof
import SemantEq.ProofAudit.Fixture

/-!
# The proof checker: `semanteq --proof <fixture>`

Audits a written implication proof for faithfulness. A fixture names the
assumed statement(s) as `sorry`-proved theorems and the goal with a real
proof (`Fixture.lean`). The modules build the judgment up in this order:

* `Ctx.lean`: the roles (goal, antecedent argument, side), the per-fixture
  context, and the categorical grading of global constants and in-file
  lemmas. A sorried in-file theorem is an outside lemma with a licensed
  sorry; a proven antecedent-free in-file lemma is graded on its statement
  and, when bridge-shaped, its proof is read once at the use role; an
  antecedent-involved one is expanded.
* `Rules.lean`: the node-level rules: polarity, bindings, the transition,
  record and collapse heads, load-bearing involvement of the antecedent, the
  pair-aligned surface and carrier tests, the goal's propositional spine,
  the closed-witness audit (`SEMANTEQ_NO_WITNESS_CHECK=1` disables it) and
  the severe tier.
* `Walk.lean`: the role- and polarity-aware walk of the proof term, with the
  goal-part ablations (a part that closes without the antecedent fails the
  proof; the conjunct-level ablation covers the components of `And.intro`
  and `Iff.intro`, `SEMANTEQ_NO_CONJUNCT_ABLATION=1` disables it) and the
  reading of every local bridge's proof direction by direction.
* `Reproof.lean`: the confiscated-instances reproof, which re-asserts the
  proof's own antecedent-free bindings wherever they sit and refuses a proof
  whose goal then closes without the antecedent
  (`SEMANTEQ_NO_REPLAY_LOCAL_FACTS=1` restricts the collection to the
  leading `have`/`let` chain).

Verdict per fixture: `PASS` (with warnings), `FAIL` (with reasons),
`SKIP_SORRY` (the goal proof itself is sorried) or `ERROR`.
-/
