import Mathlib

open Filter Finset

open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos143

def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ (Set.Ioi (1 : ℝ))) ∧ Set.Infinite A ∧ Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |k * x - y|))

end Erdos143

def WellSeparatedSet (A : Set ℝ) : Prop :=
  (A ⊆ (Set.Ioi (1 : ℝ))) ∧ Set.Infinite A ∧ Set.Countable A ∧
  (∀ x ∈ A, ∀ y ∈ A, x ≠ y → (∀ k ≥ (1 : ℕ), 1 ≤ |k * x - y|))

-- ===== assumed statement (antecedent) =====
theorem erdos_143.parts.ii_assumed (A : Set ℝ) (h : WellSeparatedSet A):
    ∃ (s : ℝ),
      Tendsto (fun n ↦ ∑ x ∈ range n, 1 / (x * Real.log x)) atTop (𝓝 s) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
namespace Erdos143

set_option maxHeartbeats 4000000 in
theorem erdos_143.parts.ii (A : Set ℝ) (h : WellSeparatedSet A) :
    Summable fun (x : A) ↦ 1 / (x * Real.log x) := by
  exfalso
  rcases _root_.erdos_143.parts.ii_assumed A h with ⟨s, hs⟩
  let f : ℕ → ℝ := fun n ↦ 1 / (n * Real.log n)
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    positivity
  have hf : Summable f := by
    refine ⟨s, (hasSum_iff_tendsto_nat_of_nonneg hf_nonneg s).2 ?_⟩
    simpa [f] using hs
  let e : (Σ k : ℕ, Fin (2 ^ k)) → ℕ := fun p ↦ 2 ^ p.1 + p.2
  have he : Function.Injective e := by
    intro p q hpq
    obtain ⟨k, i⟩ := p
    obtain ⟨l, j⟩ := q
    simp only [e] at hpq ⊢
    have hi : (i : ℕ) < 2 ^ k := i.isLt
    have hj : (j : ℕ) < 2 ^ l := j.isLt
    have hkl : k = l := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hpow : 2 ^ (k + 1) ≤ 2 ^ l := Nat.pow_le_pow_right (by omega) (by omega)
        have : 2 ^ k + (i : ℕ) < 2 ^ l := by
          calc
            2 ^ k + (i : ℕ) < 2 ^ k + 2 ^ k := Nat.add_lt_add_left hi _
            _ = 2 ^ (k + 1) := by ring
            _ ≤ 2 ^ l := hpow
        omega
      · have hpow : 2 ^ (l + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
        have : 2 ^ l + (j : ℕ) < 2 ^ k := by
          calc
            2 ^ l + (j : ℕ) < 2 ^ l + 2 ^ l := Nat.add_lt_add_left hj _
            _ = 2 ^ (l + 1) := by ring
            _ ≤ 2 ^ k := hpow
        omega
    subst l
    have hij : (i : ℕ) = (j : ℕ) := by omega
    rw [Fin.ext hij]
  have hfe : Summable (fun p ↦ f (e p)) := hf.comp_injective he
  have hblocks : Summable (fun k ↦ ∑' i : Fin (2 ^ k), f (2 ^ k + i)) := by
    exact (summable_sigma_of_nonneg (fun p ↦ hf_nonneg (e p))).1 hfe |>.2
  have hblocks' : Summable (fun k ↦ ∑' i : Fin (2 ^ (k + 1)), f (2 ^ (k + 1) + i)) :=
    hblocks.comp_injective (add_left_injective 1)
  have hlog_two : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hblock_lower : ∀ k : ℕ,
      1 / (2 * (k + 2 : ℝ)) ≤ ∑' i : Fin (2 ^ (k + 1)), f (2 ^ (k + 1) + i) := by
    intro k
    rw [tsum_fintype]
    have hterm : ∀ i : Fin (2 ^ (k + 1)),
        1 / ((2 : ℝ) ^ (k + 2) * (k + 2 : ℝ)) ≤ f (2 ^ (k + 1) + i) := by
      intro i
      have hnpos : 1 < (2 ^ (k + 1) + (i : ℕ) : ℕ) := by
        exact (one_lt_pow' (by norm_num) (by omega)).trans_le (Nat.le_add_right _ _)
      have hnle : (2 ^ (k + 1) + (i : ℕ) : ℕ) ≤ 2 ^ (k + 2) := by
        have hi := i.isLt
        exact (calc
          2 ^ (k + 1) + (i : ℕ) < 2 ^ (k + 1) + 2 ^ (k + 1) := Nat.add_lt_add_left hi _
          _ = 2 ^ (k + 2) := by ring).le
      have hlog_nonneg : 0 ≤ Real.log (2 ^ (k + 1) + (i : ℕ) : ℕ) :=
        Real.log_nonneg (by exact_mod_cast hnpos.le)
      have hlog_pos : 0 < Real.log (2 ^ (k + 1) + (i : ℕ) : ℕ) :=
        Real.log_pos (by exact_mod_cast hnpos)
      have hlog_le : Real.log (2 ^ (k + 1) + (i : ℕ) : ℕ) ≤ (k + 2 : ℝ) := by
        calc
          Real.log (2 ^ (k + 1) + (i : ℕ) : ℕ) ≤ Real.log ((2 : ℝ) ^ (k + 2)) :=
            Real.log_le_log (by positivity) (by exact_mod_cast hnle)
          _ = (k + 2 : ℝ) * Real.log 2 := by rw [Real.log_pow]; norm_num
          _ ≤ (k + 2 : ℝ) * 1 := by gcongr
          _ = (k + 2 : ℝ) := mul_one _
      have hden : ((2 ^ (k + 1) + (i : ℕ) : ℕ) : ℝ) * Real.log (2 ^ (k + 1) + (i : ℕ) : ℕ) ≤
          (2 : ℝ) ^ (k + 2) * (k + 2 : ℝ) := by
        gcongr
        exact_mod_cast hnle
      dsimp [f]
      exact one_div_le_one_div_of_le (mul_pos (by positivity) (by positivity)) hden
    calc
      1 / (2 * (k + 2 : ℝ)) = ∑ _i : Fin (2 ^ (k + 1)),
          1 / ((2 : ℝ) ^ (k + 2) * (k + 2 : ℝ)) := by
            simp [div_eq_mul_inv]
            field_simp
            ring
      _ ≤ ∑ i : Fin (2 ^ (k + 1)), f (2 ^ (k + 1) + i) :=
        Finset.sum_le_sum fun i _ ↦ hterm i
  have hharm : Summable (fun k : ℕ ↦ 1 / (k + 2 : ℝ)) := by
    have := hblocks'.mul_left 2
    apply this.of_nonneg_of_le
    · intro k
      positivity
    · intro k
      calc
        1 / (k + 2 : ℝ) = 2 * (1 / (2 * (k + 2 : ℝ))) := by
          field_simp
        _ ≤ 2 * ∑' i : Fin (2 ^ (k + 1)), f (2 ^ (k + 1) + i) := by
          gcongr
          exact hblock_lower k
  apply Real.not_summable_one_div_natCast
  apply (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ)) 2).1
  simpa [Nat.cast_add] using hharm

end Erdos143
