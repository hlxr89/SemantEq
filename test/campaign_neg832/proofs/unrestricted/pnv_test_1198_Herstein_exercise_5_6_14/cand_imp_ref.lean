import Mathlib

open Fintype Set Real Ideal Polynomial
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {F : Type*} [Field F] [hF : CharP F p] (m : ℕ) (h : m = p^n) : (X : Fin m → F) -> (∀ i j : Fin m, i ≠ j -> X i ≠ X j) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_6_14 {p m n: ℕ} (hp : p ≠ 0) (hn : n > 0)
  {F : Type*} [Field F] [CharP F p] (hm : m = p ^ n) :
  (X ^ m - X : Polynomial F).Separable := by
  have hne : (0 : ZMod 2) ≠ 0 :=
    dummy_assumed (F := ZMod 2) (p := 2) (n := 1) 2 (by norm_num)
      (fun _ => 0) 0 1 (by decide)
  exact (hne rfl).elim
