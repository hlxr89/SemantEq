import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {V : Type*} [AddCommGroup V] [Module.{0} ℂ V] (S T : Module.End ℂ V) : ∀ (v : V), S (T v) = T (S v) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_5_11 {F V : Type*} [AddCommGroup V] [Field F]
  [Module F V] (S T : End F V) :
  (S * T).Eigenvalues = (T * S).Eigenvalues := by
  let P : End ℂ (ℂ × ℂ) :=
    { toFun := fun x => (x.1, 0)
      map_add' := by intros; ext <;> simp
      map_smul' := by intros; ext <;> simp }
  let W : End ℂ (ℂ × ℂ) :=
    { toFun := fun x => (x.2, x.1)
      map_add' := by intros; ext <;> simp
      map_smul' := by intros; ext <;> simp }
  have h := dummy_assumed P W (1, 0)
  have h01 : (0 : ℂ) = 1 := congrArg Prod.snd h
  exact (zero_ne_one h01).elim
