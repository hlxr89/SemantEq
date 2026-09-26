# H2 — instantiating the antecedent at a foreign object (Appendix J)

The candidate states only that the image of one open set is open; the model
proves the reference (the restriction is an open map) by feeding the
antecedent the set `Subtype.val '' U`, which exists only after the goal's own
conclusion is unfolded. The antecedent is used as a schema rather than as the
corresponding statement, and the instantiation check refuses it.

Source: campaign, faithful style, pair `pnv_test_0485_Munkres_exercise_22_5`,
direction candidate ⇒ reference.

Reproduce with SemantEq-ProofAudit (the proof must be rejected):

    lake exe semanteq --proof case_studies/H2_munkres_22_5_foreign_object/cand_imp_ref.lean

Expected: `FAIL`, with the reasons naming the violated clause.
