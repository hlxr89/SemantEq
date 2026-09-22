# H3 — not using the antecedent at all (Appendix H)

The reference states an isomorphism between the centre of a product and the
product of the centres; the candidate states an equality of subgroups. The
model extracts the antecedent, never uses it (its own comment says the
equivalence cannot identify the carriers), and closes the goal with the
library theorem `Set.center_prod`. Both the relevance requirement and
proof-term grading refuse this.

Source: campaign, rewrite style, pair `pnv_test_1233_Artin_exercise_2_8_6`,
direction reference ⇒ candidate.

Reproduce with SemantEq-ProofAudit (the proof must be rejected):

    lake exe semanteq --proof case_studies/H3_artin_2_8_6_antecedent_unused/ref_imp_cand.lean

Expected: `FAIL`, with the reasons naming the violated clause.
