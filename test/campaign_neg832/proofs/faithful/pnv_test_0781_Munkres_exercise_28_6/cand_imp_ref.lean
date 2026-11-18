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
  have hIso : Isometry f := dummy_assumed hf.dist_eq
  have hIter : ∀ n : ℕ, Isometry (f^[n]) := by
    intro n
    induction n with
    | zero =>
        simp only [Function.iterate_zero]
        exact Isometry.of_dist_eq fun _ _ => rfl
    | succ n ih =>
        apply Isometry.of_dist_eq
        intro x y
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
          hIso.dist_eq, ih.dist_eq]
  have hsurj : Surjective f := by
    intro y
    by_contra hy
    have hrange : IsClosed (range f) :=
      (isCompact_range hIso.continuous).isClosed
    have hnhds : (range f)ᶜ ∈ 𝓝 y :=
      hrange.isOpen_compl.mem_nhds (by simpa using hy)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    obtain ⟨z, φ, hφ, hlim⟩ :=
      CompactSpace.tendsto_subseq (fun n : ℕ => (f^[n]) y)
    have hevent : ∀ᶠ n : ℕ in atTop,
        (f^[φ n]) y ∈ Metric.ball z (ε / 2) := by
      simpa only [Function.comp_apply] using
        hlim.eventually (Metric.ball_mem_nhds z (half_pos hε))
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.1 hevent
    have hn' := hn (n + 1) (Nat.le_add_right n 1)
    have hn := hn n le_rfl
    have hclose : dist ((f^[φ n]) y) ((f^[φ (n + 1)]) y) < ε := by
      calc
        dist ((f^[φ n]) y) ((f^[φ (n + 1)]) y) ≤
            dist ((f^[φ n]) y) z + dist z ((f^[φ (n + 1)]) y) := dist_triangle _ _ _
        _ < ε / 2 + ε / 2 := by
          exact add_lt_add (by simpa [Metric.mem_ball] using hn)
            (by simpa [Metric.mem_ball, dist_comm] using hn')
        _ = ε := by ring
    let q := φ (n + 1) - φ n
    have hφlt : φ n < φ (n + 1) := hφ (Nat.lt_succ_self n)
    have hqpos : 0 < q := Nat.sub_pos_of_lt hφlt
    have hindex : φ (n + 1) = φ n + q := by
      exact (Nat.add_sub_of_le (Nat.le_of_lt hφlt)).symm
    have hcancel :
        dist ((f^[φ n]) y) ((f^[φ (n + 1)]) y) = dist y ((f^[q]) y) := by
      rw [hindex, Function.iterate_add_apply]
      exact (hIter (φ n)).dist_eq y ((f^[q]) y)
    have hqclose : dist y ((f^[q]) y) < ε := by
      rwa [hcancel] at hclose
    have hqinball : (f^[q]) y ∈ Metric.ball y ε := by
      simpa [Metric.mem_ball, dist_comm] using hqclose
    have hqrange : (f^[q]) y ∈ range f := by
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hqpos)
      rw [hk, Function.iterate_succ_apply']
      exact ⟨(f^[k]) y, rfl⟩
    exact (hball hqinball) hqrange
  exact ⟨hIso.continuous, ⟨hIso.injective, hsurj⟩,
    (hIso.isEmbedding.isOpenEmbedding_of_surjective hsurj).isOpenMap⟩
