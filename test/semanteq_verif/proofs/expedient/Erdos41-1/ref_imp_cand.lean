import Mathlib

open Filter Set

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos41

variable {α : Type} [AddCommMonoid α]

def NtupleCondition (A : Set α) (n : ℕ) : Prop :=
  ∀ I J : Multiset α,
    (∀ i ∈ I, i ∈ A) →
    (∀ j ∈ J, j ∈ A) →
    I.card = n →
    J.card = n →
    I.sum = J.sum →
    I = J

-- ===== assumed statement (antecedent) =====
theorem erdos_41_assumed (A : Set ℕ) (h_triple : NtupleCondition A 3) (h_infinite : A.Infinite) :
    Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3 : ℝ)) = 0 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_41_goal (A : Set ℕ) (h_triple : NtupleCondition A 3) (h_infinite : A.Infinite) :
    Filter.atTop.liminf (fun N => (A ∩ Icc 1 N).ncard / (N : ℝ)^(1/3)) = 0 := by
  simp only [Nat.div_eq_of_lt (by omega : 1 < 3), pow_zero, div_one]
  apply Real.liminf_of_not_isCoboundedUnder
  simp only [Filter.IsCoboundedUnder, Filter.IsCobounded, eventually_map]
  rintro ⟨b, hb⟩
  obtain ⟨k : ℕ, hbk⟩ := exists_nat_gt (b + 1)
  obtain ⟨s, hs, hsfin, hscard⟩ :=
    (h_infinite.diff (Set.finite_singleton 0)).exists_subset_ncard_eq k
  obtain ⟨N, hN⟩ := hsfin.bddAbove
  have hev : ∀ᶠ M : ℕ in Filter.atTop, b + 1 ≤ ((A ∩ Icc 1 M).ncard : ℝ) := by
    filter_upwards [eventually_ge_atTop N] with M hNM
    have hsub : s ⊆ A ∩ Icc 1 M := by
      intro x hx
      have hx' := hs hx
      exact ⟨hx'.1, Nat.one_le_iff_ne_zero.2 (by simpa using hx'.2), (hN hx).trans hNM⟩
    have hcard : k ≤ (A ∩ Icc 1 M).ncard := by
      rw [← hscard]
      exact Set.ncard_le_ncard hsub
    have hkreal : (k : ℝ) ≤ ((A ∩ Icc 1 M).ncard : ℝ) := by
      exact_mod_cast hcard
    exact (le_of_lt hbk).trans hkreal
  exact (not_le_of_gt (lt_add_one b)) (hb (b + 1) hev)

end Erdos41
