# J3 — not using the antecedent at all (Appendix J)

The reference states an isomorphism between the centre of a product group and
the product of the centres; the candidate states that the centre of the
product, as a set, equals the product of the two centres as sets. The model
proves the candidate from the reference in two lines: it extracts the
antecedent and binds it to a name that never appears again, then closes the
goal with the library theorem `Set.center_prod`. The first line can be
deleted and the proof still compiles. Both the relevance requirement and
proof-term grading refuse this.

Source: campaign, faithful style, pair `pnv_test_0546_Artin_exercise_2_8_6`,
direction reference ⇒ candidate (label: non-equivalent).

Reproduce with SemantEq-ProofAudit (the proof must be rejected):

    lake exe semanteq --proof case_studies/J3_artin_2_8_6_antecedent_unused/ref_imp_cand.lean

Expected: `FAIL`, with two reasons, the goal closing without the antecedent
and a library theorem asserted as content on the goal derivation.
