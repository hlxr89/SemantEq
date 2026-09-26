# Case studies

The statement pairs and proofs discussed in the paper's appendices, each in
its own folder with the two statements (`ref.lean`, `cand.lean`), the proof or
recorded output the appendix quotes, and a `NOTES.md` giving the point of the
example, its source, the command that reproduces it, and the expected verdict.

Every command runs from the repository root after `lake build semanteq`.
Pairs go through SemantEq-Eval (`lake exe semanteq ref.lean cand.lean`),
proofs through SemantEq-ProofAudit (`lake exe semanteq --proof file.lean`);
add `--raw` for the full JSON record.

| folder | appendix | what it shows |
|---|---|---|
| `D1_munkres_29_10_rearrangement/` | Appendix D | rearrangement alone; EquivalentRestricted |
| `D2_usamo_1996_p1_two_bridges/` | Appendix D | two bridges; needs --depth 2 |
| `E1_beqplus_dummit_foote_1_1_4/` | Appendix E | BEq+ false positive; must be rejected |
| `E2_beqplus_rudin_2_19a/` | Appendix E | BEq+ false positive; must be rejected |
| `F1_ex_falso_pair/` | Appendix F | ex falso audit; rejected both ways |
| `F2_relevance_pair/` | Appendix F | relevance audit; LikelyTooStrong |
| `J1_rudin_1_4_foreign_structure/` | Appendix J | model proof refused (cand_imp_ref) |
| `J2_munkres_22_5_foreign_object/` | Appendix J | model proof refused (cand_imp_ref) |
| `J3_artin_2_8_6_antecedent_unused/` | Appendix J | model proof refused (ref_imp_cand) |
| `J4_imo_1983_p1_checker_loop/` | Appendix J | checker-in-the-loop overturns a label (pair ruled non-equivalent) |

The campaign proofs (H1–H3) are verbatim model output from the four-style
campaign; the pair statements are verbatim benchmark or suite entries.
