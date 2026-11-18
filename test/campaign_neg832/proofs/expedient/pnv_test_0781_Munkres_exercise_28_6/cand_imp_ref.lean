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
  have hi : ∀ n : ℕ, Isometry (f^[n]) := by
    intro n
    induction n with
    | zero => exact isometry_id
    | succ n hn => simpa [Function.iterate_succ] using hn.comp hf
  have hsurj : Surjective f := by
    intro x
    obtain ⟨a, -, φ, hφ, ha⟩ := isSeqCompact_univ
      (x := fun n => (f^[n]) x) (by simp)
    let g : ℕ → X := fun n => (f^[φ n.succ - φ n]) x
    have hg_range : ∀ n, g n ∈ range f := by
      intro n
      refine ⟨(f^[φ n.succ - φ n - 1]) x, ?_⟩
      change f ((f^[φ n.succ - φ n - 1]) x) =
        (f^[φ n.succ - φ n]) x
      calc
        f ((f^[φ n.succ - φ n - 1]) x) =
            (f^[Nat.succ (φ n.succ - φ n - 1)]) x :=
          (Function.iterate_succ_apply' f _ x).symm
        _ = (f^[φ n.succ - φ n]) x := by
          congr 1
          have := hφ (Nat.lt_succ_self n)
          omega
    have hdist : ∀ n, dist (g n) x =
        dist ((f^[φ n.succ]) x) ((f^[φ n]) x) := by
      intro n
      rw [← (hi (φ n)).dist_eq]
      simp only [g]
      rw [← Function.iterate_add_apply]
      have := hφ (Nat.lt_succ_self n)
      congr 2 <;> omega
    have ha' : Tendsto (fun n : ℕ => (f^[φ n.succ]) x) atTop (𝓝 a) := by
      exact (tendsto_add_atTop_iff_nat 1).2 ha
    have hdist0 : Tendsto (fun n => dist (g n) x) atTop (𝓝 0) := by
      simpa [hdist, dist_self] using ha'.dist ha
    have hg : Tendsto g atTop (𝓝 x) := by
      rw [tendsto_iff_dist_tendsto_zero]
      simpa [dist_comm] using hdist0
    have hx : x ∈ range f :=
      (isCompact_range hf.continuous).isClosed.mem_of_tendsto hg
        (Filter.Eventually.of_forall hg_range)
    exact hx
  refine ⟨hf.continuous, ⟨hf.injective, hsurj⟩, ?_⟩
  exact hf.isEmbedding.isInducing.isOpenMap (by simpa [hsurj.range_eq] using isOpen_univ)
