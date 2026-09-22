/-
Autoformalized from NL only (blind); benchmark: ProofNetSharp; problem: exercise_3_4_5a.
-/
import Mathlib

/-- Prove that subgroups of a solvable group are solvable. -/
theorem exercise_3_4_5a {G : Type*} [Group G] (hG : IsSolvable G) (H : Subgroup G) :
    IsSolvable H := sorry
