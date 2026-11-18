import Mathlib

open Nat Filter Finset

open scoped Topology Asymptotics

-- ===== unified context (both sides' local defs, merged) =====
-- Empty: neither preamble contains local definitions or structures.

namespace Erdos726

-- ===== assumed statement (antecedent) =====
theorem erdos_726_assumed :
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
          (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < (n % p : ℝ)),
        (1 : ℝ) / (p : ℝ))
      ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_726_goal :
    (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
        (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < ((n % p : ℕ) : ℝ)),
      (1 : ℝ) / (p : ℝ))
    ~[atTop] (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) := by
  exfalso
  have hzero :
      (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
          (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < (n % p : ℝ)),
        (1 : ℝ) / (p : ℝ)) = fun _ ↦ 0 := by
    funext n
    have hempty :
        (range (n + 1)).filter
            (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < (n % p : ℝ)) = ∅ := by
      ext p
      constructor
      · simp only [mem_filter, mem_range]
        rintro ⟨-, hp, hineq⟩
        have hp0 : (p : ℝ) ≠ 0 := by
          exact_mod_cast hp.ne_zero
        have hmod : (n : ℝ) % (p : ℝ) = 0 := by
          simp [Field.mod_eq, hp0]
        rw [hmod] at hineq
        have hp_pos : (0 : ℝ) < p := by
          exact_mod_cast hp.pos
        linarith
      · simp
    rw [hempty]
    simp
  have hg : Tendsto (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) atTop atTop := by
    apply Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    exact Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hleft := erdos_726_assumed.symm.tendsto_atTop hg
  rw [hzero] at hleft
  exact (Filter.not_tendsto_const_atTop (0 : ℝ) atTop) hleft

end Erdos726
