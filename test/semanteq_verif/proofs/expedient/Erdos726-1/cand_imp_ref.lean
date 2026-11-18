import Mathlib

open Nat Filter Finset

open scoped Topology Asymptotics

-- ===== unified context (both sides' local defs, merged) =====
-- empty

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
      (fun _ : ℕ ↦ (0 : ℝ)) ~[atTop]
        (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) := by
    have hleft :
        (fun n : ℕ ↦ ∑ p ∈ (range (n + 1)).filter
            (fun p : ℕ ↦ p.Prime ∧ (p : ℝ) / 2 < (n % p : ℝ)),
          (1 : ℝ) / (p : ℝ)) = (fun _ : ℕ ↦ (0 : ℝ)) := by
      funext n
      apply Finset.sum_eq_zero
      intro p hp
      have hp' := (Finset.mem_filter.mp hp).2
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp'.1.ne_zero
      have hmod : (n % p : ℝ) = 0 := by simp [hp0]
      rw [hmod] at hp'
      have hppos : (0 : ℝ) < p := by exact_mod_cast hp'.1.pos
      exfalso
      linarith [hp'.2]
    rw [← hleft]
    exact erdos_726_assumed
  have heq :
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) =ᶠ[atTop]
        (fun _ : ℕ ↦ (0 : ℝ)) :=
    Asymptotics.isEquivalent_zero_iff_eventually_zero.mp hzero.symm
  have ht : Tendsto
      (fun n : ℕ ↦ Real.log (Real.log (n : ℝ)) / 2) atTop atTop :=
    Tendsto.atTop_div_const (by norm_num : (0 : ℝ) < 2)
      (Real.tendsto_log_atTop.comp
        (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 < Real.log (Real.log (n : ℝ)) / 2 :=
    ht.eventually (eventually_gt_atTop 0)
  obtain ⟨n, hn, hpn⟩ := (heq.and hpos).exists
  linarith

end Erdos726
