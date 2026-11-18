import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_21_6b_assumed
  (f : ℕ → Icc 0 1 → ℝ)
  (h : ∀ x n, f n x = ↑x ^ n) :
  ¬ ∃ f₀, TendstoUniformly f f₀ atTop := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {n : ℕ} : ¬ TendstoUniformlyOn (fun (n : ℕ) (x : ℝ) => x ^ n) (fun x => x) atTop (Set.Icc 0 1) := by
  exfalso
  apply exercise_21_6b_assumed
    (fun n (x : Icc (0 : ℕ) 1) ↦ (↑x : ℝ) ^ n) (by intros; rfl)
  refine ⟨fun x ↦ (↑x : ℝ), ?_⟩
  have heq :
      (fun n (x : Icc (0 : ℕ) 1) ↦ (↑x : ℝ) ^ n) =ᶠ[atTop]
        (fun _ (x : Icc (0 : ℕ) 1) ↦ (↑x : ℝ)) := by
    filter_upwards [eventually_atTop.2 ⟨1, fun b hb ↦ hb⟩] with k hk
    funext x
    have hxle : x.1 ≤ 1 := x.property.2
    have hx : x.1 = 0 ∨ x.1 = 1 := by omega
    rcases hx with hx | hx <;> simp [hx, Nat.one_le_iff_ne_zero.mp hk]
  apply (tendstoUniformly_congr heq).mpr
  intro u hu
  exact Filter.Eventually.of_forall fun _ x ↦ refl_mem_uniformity hu
