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
  let S : End ℝ ℂ := LinearMap.mulLeft ℝ Complex.I
  have hS : ∀ c : ℝ, eigenspace S c = ⊥ := by
    intro c
    ext z
    simp only [mem_eigenspace_iff, Submodule.mem_bot]
    constructor
    · intro hz
      have hre := congrArg Complex.re hz
      have him := congrArg Complex.im hz
      simp [S, Complex.I_mul] at hre him
      have heq : (c * c + 1) * z.im = 0 := by
        calc
          _ = c * (c * z.im) + z.im := by ring
          _ = c * z.re + z.im := by rw [him]
          _ = 0 := by linarith
      have hc : c * c + 1 ≠ 0 := by nlinarith [sq_nonneg c]
      have hzi : z.im = 0 := (mul_eq_zero.mp heq).resolve_left hc
      apply Complex.ext <;> simp [hzi] at him ⊢
      exact him
    · rintro rfl
      simp
  have htop : Submodule.map S (⊤ : Submodule ℝ ℂ) = ⊤ := by
    rw [Submodule.map_top]
    apply LinearMap.range_eq_top.mpr
    intro z
    use -Complex.I * z
    change Complex.I * (-Complex.I * z) = z
    rw [← mul_assoc]
    norm_num
  obtain ⟨f, hf⟩ := exercise_5_24_assumed hS htop
  let U := (⊤ : Submodule ℝ ℂ)
  let e : U ≃ ℂ := Submodule.topEquiv.toEquiv
  letI : Field U := Equiv.field e
  let instS : Semiring U := inferInstance
  let instA : AddCommMonoid U := inferInstance
  let instM : Module U U := @Semiring.toModule U instS
  have hh := congrArg (fun g => @g U instS instA instM) hf
  change @finrank U U instS instA instM = _ at hh
  have hone : @finrank U U instS instA instM = 1 := Module.finrank_self U
  rw [hone] at hh
  change 1 = @f U instS instA instM + @f U instS instA instM at hh
  omega
