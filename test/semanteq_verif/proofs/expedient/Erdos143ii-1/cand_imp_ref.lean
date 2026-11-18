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

theorem erdos_143.parts.ii (A : Set ℝ) (h : WellSeparatedSet A) :
    Summable fun (x : A) ↦ 1 / (x * Real.log x) := by
  exfalso
  obtain ⟨s, hs⟩ := _root_.erdos_143.parts.ii_assumed A h
  have hnonneg : ∀ n : ℕ, 0 ≤ (1 / (n * Real.log n) : ℝ) := by
    intro n
    by_cases hn : n ≤ 1
    · interval_cases n <;> simp
    · positivity
  have hb : BddAbove
      (Set.range (fun n ↦ (∑ x ∈ range n, 1 / (x * Real.log x) : ℝ))) :=
    hs.bddAbove_range
  obtain ⟨c, hc⟩ := hb
  have hsum : Summable (fun n : ℕ ↦ (1 / (n * Real.log n) : ℝ)) :=
    _root_.summable_of_sum_range_le hnonneg (fun n ↦ hc ⟨n, rfl⟩)
  have hn : ∀ᶠ n : ℕ in atTop, 0 ≤ (1 / (n * Real.log n) : ℝ) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    positivity
  have hm : ∀ᶠ n : ℕ in atTop,
      (1 / ((↑(n + 1) : ℝ) * Real.log (↑(n + 1) : ℝ)) : ℝ) ≤
        1 / (n * Real.log n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    apply one_div_le_one_div_of_le
    · have : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
      positivity
    · have hcast : (n : ℝ) ≤ (n + 1 : ℕ) := by
        exact_mod_cast Nat.le_add_right n 1
      have hlogle := _root_.Real.strictMonoOn_log.monotoneOn
        (show (n : ℝ) ∈ Set.Ioi 0 by
          change (0 : ℝ) < n
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn))
        (show ((n + 1 : ℕ) : ℝ) ∈ Set.Ioi 0 by
          change (0 : ℝ) < (n + 1 : ℕ)
          exact_mod_cast Nat.zero_lt_succ n) hcast
      exact mul_le_mul hcast hlogle (by positivity) (by positivity)
  have hcondensed := (summable_condensed_iff_of_eventually_nonneg hn hm).2 hsum
  apply _root_.Real.not_summable_one_div_natCast
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (_root_.Real.log_pos (by norm_num))
  have hh := hcondensed.mul_left (Real.log 2)
  convert hh using 1 <;> funext k
  by_cases hk : k = 0
  · simp [hk]
  · rw [Nat.cast_pow, Nat.cast_ofNat, _root_.Real.log_pow]
    field_simp

end Erdos143
