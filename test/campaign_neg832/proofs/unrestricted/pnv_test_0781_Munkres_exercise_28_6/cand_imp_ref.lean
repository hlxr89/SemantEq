import Mathlib

open Filter Set TopologicalSpace Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type u} [MetricSpace X] [CompactSpace X] {f : X → X} (h : ∀ x y : X, dist (f x) (f y) = dist x y) : Isometry f := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_28_6 {X : Type*} [MetricSpace X]
  [CompactSpace X] {f : X → X} (hf : Isometry f) :
  Continuous f ∧ Bijective f ∧ IsOpenMap f := by
  have hiter : ∀ n : ℕ, Isometry (f^[n]) := by
    intro n
    induction n with
    | zero => simpa using isometry_id
    | succ n ih => simpa [Function.iterate_succ_apply] using ih.comp hf
  have hsurj : Surjective f := by
    intro x
    obtain ⟨a, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq (fun n ↦ (f^[n]) x)
    have hlim' : Tendsto (fun n ↦ (f^[φ (n + 1)]) x) atTop (𝓝 a) := by
      simpa [Function.comp_def] using hlim.comp (tendsto_add_atTop_nat 1)
    have hdist : Tendsto (fun n ↦ dist ((f^[φ n]) x) ((f^[φ (n + 1)]) x)) atTop (𝓝 0) := by
      simpa [Function.comp_def] using hlim.dist hlim'
    let d : ℕ → ℕ := fun n ↦ φ (n + 1) - φ n
    have hdpos (n : ℕ) : 0 < d n := Nat.sub_pos_of_lt (hφ (Nat.lt_succ_self n))
    have hdeq (n : ℕ) : φ n + d n = φ (n + 1) :=
      Nat.add_sub_of_le (Nat.le_of_lt (hφ (Nat.lt_succ_self n)))
    have hvdist (n : ℕ) : dist ((f^[d n]) x) x =
        dist ((f^[φ (n + 1)]) x) ((f^[φ n]) x) := by
      rw [← (hiter (φ n)).dist_eq]
      rw [← Function.iterate_add_apply, hdeq]
    have hvlim : Tendsto (fun n ↦ (f^[d n]) x) atTop (𝓝 x) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hevent : ∀ᶠ n in atTop,
          dist ((f^[φ n]) x) ((f^[φ (n + 1)]) x) < ε :=
        by simpa [Real.dist_eq] using Metric.tendsto_nhds.1 hdist ε hε
      filter_upwards [hevent] with n hn
      simpa [hvdist n, dist_comm] using hn
    have hrange : IsClosed (range f) :=
      (isCompact_range hf.continuous).isClosed
    apply hrange.mem_of_tendsto hvlim
    filter_upwards [] with n
    refine ⟨(f^[d n - 1]) x, ?_⟩
    rw [← Function.iterate_succ_apply' f (d n - 1) x]
    congr 2
    exact Nat.succ_pred_eq_of_pos (hdpos n)
  have hbij : Bijective f := ⟨hf.injective, hsurj⟩
  have hhome : IsHomeomorph f :=
    isHomeomorph_iff_continuous_bijective.2 ⟨hf.continuous, hbij⟩
  exact ⟨hf.continuous, hbij, hhome.isOpenMap⟩
