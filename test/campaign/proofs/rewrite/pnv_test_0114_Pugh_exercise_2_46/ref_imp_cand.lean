import Mathlib

open Filter Real Function
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_2_46_assumed {M : Type*} [MetricSpace M]
  {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
  (hAB : Disjoint A B) (hA₀ : A ≠ ∅) (hB₀ : B ≠ ∅) :
  ∃ a₀ b₀, a₀ ∈ A ∧ b₀ ∈ B ∧ ∀ (a : M) (b : M),
  a ∈ A → b ∈ B → dist a₀ b₀ ≤ dist a b := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem dummy {M : Type*} [PseudoMetricSpace M] {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) (hA0 : A.Nonempty) (hB0 : B.Nonempty) : ∃ a ∈ A, ∃ b ∈ B, ∀ a' ∈ A, ∀ b' ∈ B, dist a b ≤ dist a' b' := by
  let D : Set ℝ := (fun p : M × M => dist p.1 p.2) '' (A ×ˢ B)
  have hD : IsCompact D :=
    (hA.prod hB).image (continuous_fst.dist continuous_snd)
  have hD0 : D.Nonempty := by
    obtain ⟨a, ha⟩ := hA0
    obtain ⟨b, hb⟩ := hB0
    exact ⟨dist a b, ⟨(a, b), ⟨ha, hb⟩, rfl⟩⟩
  have hD_nonneg : ∀ x ∈ D, 0 ≤ x := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact dist_nonneg
  have hdisj : Disjoint D ({-1} : Set ℝ) := by
    rw [Set.disjoint_singleton_right]
    intro hneg
    exact (not_le_of_gt neg_one_lt_zero) (hD_nonneg (-1) hneg)
  obtain ⟨d, e, hd, he, hmin⟩ :=
    exercise_2_46_assumed hD isCompact_singleton hdisj hD0.ne_empty
      (Set.singleton_ne_empty (-1))
  have hdD := hd
  obtain ⟨p, hp, hpd⟩ := hd
  change dist p.1 p.2 = d at hpd
  obtain ⟨hpA, hpB⟩ := hp
  have heq : e = -1 := Set.mem_singleton_iff.mp he
  refine ⟨p.1, hpA, p.2, hpB, ?_⟩
  intro a' ha' b' hb'
  have h := hmin (dist a' b') (-1)
    ⟨(a', b'), ⟨ha', hb'⟩, rfl⟩ (Set.mem_singleton (-1))
  rw [heq] at h
  simp only [Real.dist_eq, sub_neg_eq_add] at h
  rw [abs_of_nonneg (add_nonneg (hD_nonneg d hdD) zero_le_one),
    abs_of_nonneg (add_nonneg dist_nonneg zero_le_one)] at h
  rw [hpd]
  exact (add_le_add_iff_right 1).mp h
