import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] {f : X → Y} {A : Set X} (h : UniformContinuousOn f A) : ∃ g : X → Y, UniformContinuous g ∧ EqOn f g A ∧ EqOn f g (closure A) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_43_2 {X : Type*} [MetricSpace X]
  {Y : Type*} [MetricSpace Y] [CompleteSpace Y] (A : Set X)
  (f : X → Y) (hf : UniformContinuousOn f A) :
  ∃! (g : X → Y), ContinuousOn g (closure A) ∧
  UniformContinuousOn g (closure A) ∧ ∀ (x : A), g x = f x := by
  have hsub : Subsingleton Y :=
    ⟨by
      intro y₁ y₂
      let F : ℝ → Y := fun x => if x < 0 then y₁ else y₂
      have hc : UniformContinuousOn (fun _ : ℝ => y₁) (Iio (0 : ℝ)) :=
        uniformContinuous_const.uniformContinuousOn
      have hF : UniformContinuousOn F (Iio (0 : ℝ)) :=
        hc.congr (by
          intro x hx
          change x < 0 at hx
          simp only [F, if_pos hx])
      obtain ⟨g, hg, hAg, hcl⟩ := dummy_assumed hF
      have hs : Tendsto (fun n : ℕ => -(1 / ((n : ℝ) + 1))) atTop (nhds 0) := by
        simpa only [neg_zero] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
      have htg : Tendsto (fun n : ℕ => g (-(1 / ((n : ℝ) + 1)))) atTop
          (nhds (g 0)) :=
        hg.continuous.continuousAt.tendsto.comp hs
      have hgy₁ : (fun n : ℕ => g (-(1 / ((n : ℝ) + 1)))) = fun _ => y₁ := by
        funext n
        have hn : -(1 / ((n : ℝ) + 1)) < 0 :=
          neg_lt_zero.mpr (one_div_pos.mpr (Nat.cast_add_one_pos n))
        exact (hAg hn).symm.trans (by simp only [F, if_pos hn])
      have hty₁ : Tendsto (fun n : ℕ => g (-(1 / ((n : ℝ) + 1)))) atTop
          (nhds y₁) := by
        rw [hgy₁]
        exact tendsto_const_nhds
      have hg0 : g 0 = y₂ := by
        have hz : (0 : ℝ) ∈ closure (Iio (0 : ℝ)) := by
          rw [closure_Iio]
          change (0 : ℝ) ≤ 0
          exact le_rfl
        exact (hcl hz).symm.trans (by simp only [F, lt_self_iff_false, ↓reduceIte])
      have hty₂ : Tendsto (fun n : ℕ => g (-(1 / ((n : ℝ) + 1)))) atTop
          (nhds y₂) := by
        simpa only [hg0] using htg
      exact tendsto_nhds_unique hty₁ hty₂⟩
  letI : Subsingleton Y := hsub
  obtain ⟨g, hg, hfg, _⟩ := dummy_assumed hf
  refine ⟨g, ⟨hg.continuous.continuousOn, hg.uniformContinuousOn,
    fun x => (hfg x.property).symm⟩, ?_⟩
  intro g' _
  funext x
  exact Subsingleton.elim (g' x) (g x)
