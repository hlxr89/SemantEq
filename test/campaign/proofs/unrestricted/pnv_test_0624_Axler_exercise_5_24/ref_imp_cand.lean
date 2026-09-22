import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_5_24_assumed {V : Type*} [AddCommGroup V]
  [Module ℝ V] [FiniteDimensional ℝ V] {T : End ℝ V}
  (hT : ∀ c : ℝ, eigenspace T c = ⊥) {U : Submodule ℝ V}
  (hU : Submodule.map T U = U) : Even (finrank U) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy (V : Type*) [AddCommGroup V] [Module ℝ V] (T : V →ₗ[ℝ] V) (hT : ∀ (c : ℝ) (v : V), T v = c • v → c = 0 ∨ v = 0) (W : Submodule ℝ V) (hW : ∀ (v : V), v ∈ W → T v ∈ W) : Even (finrank ℝ W) := by
  exfalso
  let rot : End ℝ ℂ :=
    { toFun := fun z => Complex.I * z
      map_add' := by intro x y; ring
      map_smul' := by
        intro r x
        simp only [RingHom.id_apply, Complex.real_smul]
        ring }
  have hrot : ∀ c : ℝ, eigenspace rot c = ⊥ := by
    intro c
    rw [Submodule.eq_bot_iff]
    intro z hz
    rw [mem_eigenspace_iff] at hz
    have hz' : (Complex.I - (c : ℂ)) * z = 0 := by
      rw [sub_mul]
      simpa [rot, Complex.real_smul] using sub_eq_zero.mpr hz
    have hc : Complex.I - (c : ℂ) ≠ 0 := by
      intro hc
      have hi := congrArg Complex.im hc
      norm_num at hi
    exact (mul_eq_zero.mp hz').resolve_left hc
  have hmap : Submodule.map rot (⊤ : Submodule ℝ ℂ) = ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top]
    intro z
    refine ⟨-Complex.I * z, ?_⟩
    change Complex.I * (-Complex.I * z) = z
    calc
      Complex.I * (-Complex.I * z) = -(Complex.I * Complex.I) * z := by ring
      _ = z := by rw [Complex.I_mul_I]; simp
  have he := exercise_5_24_assumed (T := rot)
    (U := (⊤ : Submodule ℝ ℂ)) hrot hmap
  rcases he with ⟨f, hf⟩
  let e : (↥(⊤ : Submodule ℝ ℂ)) ≃ ℂ :=
    { toFun := fun z => z.1
      invFun := fun z => ⟨z, by simp⟩
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  letI : Field (↥(⊤ : Submodule ℝ ℂ)) := Equiv.field e
  let U := ↥(⊤ : Submodule ℝ ℂ)
  have hh := congrFun (congrFun (congrFun (congrFun hf U)
    (inferInstance : Semiring U)) (inferInstance : AddCommMonoid U))
    (inferInstance : Module U U)
  dsimp [U] at hh
  simp only [Module.finrank_self] at hh
  omega
