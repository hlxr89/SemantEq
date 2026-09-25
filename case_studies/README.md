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
| `B1_munkres_29_10_rearrangement/` | Appendix B | rearrangement alone; EquivalentRestricted |
| `B2_usamo_1996_p1_two_bridges/` | Appendix B | two bridges; needs --depth 2 |
| `C1_beqplus_dummit_foote_1_1_4/` | Appendix C | BEq+ false positive; must be rejected |
| `C2_beqplus_rudin_2_19a/` | Appendix C | BEq+ false positive; must be rejected |
| `D1_ex_falso_pair/` | Appendix D | ex falso audit; rejected both ways |
| `D2_relevance_pair/` | Appendix D | relevance audit; LikelyTooStrong |
| `H1_rudin_1_4_foreign_structure/` | Appendix H | model proof refused (cand_imp_ref) |
| `H2_munkres_22_5_foreign_object/` | Appendix H | model proof refused (cand_imp_ref) |
| `H3_artin_2_8_6_antecedent_unused/` | Appendix H | model proof refused (ref_imp_cand) |
| `H5_imo_1983_p1_checker_loop/` | Appendix H | checker-in-the-loop overturns a label (pair ruled non-equivalent) |

The campaign proofs (H1–H3) are verbatim model output from the four-style
campaign; the pair statements are verbatim benchmark or suite entries.
