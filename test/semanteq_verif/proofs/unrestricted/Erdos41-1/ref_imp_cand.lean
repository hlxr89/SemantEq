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
  norm_num
  have h_pos : (A \ {0}).Infinite := h_infinite.diff (Set.finite_singleton 0)
  have h_lower (k : ℕ) :
      ∀ᶠ N in Filter.atTop, (k : ℝ) ≤ ((A ∩ Icc 1 N).ncard : ℝ) := by
    obtain ⟨t, ht_sub, ht_fin, ht_card⟩ := h_pos.exists_subset_ncard_eq k
    let B := ∑ x ∈ ht_fin.toFinset, x
    filter_upwards [eventually_ge_atTop B] with N hN
    have ht_inter : t ⊆ A ∩ Icc 1 N := by
      intro x hx
      have hx_pos : 1 ≤ x := by
        have hx0 : x ≠ 0 := by
          exact fun hx0 => (ht_sub hx).2 (by simp [hx0])
        exact Nat.one_le_iff_ne_zero.mpr hx0
      have hxB : x ≤ B := by
        dsimp [B]
        exact Finset.single_le_sum (fun y _ => Nat.zero_le y) (ht_fin.mem_toFinset.mpr hx)
      exact ⟨(ht_sub hx).1, hx_pos, hxB.trans hN⟩
    have hk : k ≤ (A ∩ Icc 1 N).ncard := by
      rw [← ht_card]
      exact ncard_le_ncard ht_inter
    exact_mod_cast hk
  have h_unbounded :
      ¬ BddAbove {b : ℝ | ∀ᶠ N in Filter.atTop, b ≤ ((A ∩ Icc 1 N).ncard : ℝ)} := by
    rw [bddAbove_def]
    push_neg
    intro b
    obtain ⟨k, hbk⟩ := exists_nat_gt b
    exact ⟨k, h_lower k, hbk⟩
  rw [Filter.liminf_eq, csSup_of_not_bddAbove h_unbounded]
  simp

end Erdos41
