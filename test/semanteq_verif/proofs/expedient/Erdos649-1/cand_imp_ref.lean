import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
namespace Nat

def maxPrimeFac (n : ℕ) : ℕ := if n = 1 then 1 else n.primeFactorsList.getLastI

end Nat

namespace Erdos649

-- ===== assumed statement (antecedent) =====
theorem erdos_649_assumed :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime →
      ∃ n : ℕ, n.maxPrimeFac = p ∧ (n + 1).maxPrimeFac = q := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_649_goal :
    ¬ ∀ p q : ℕ, p.Prime → q.Prime → p ≠ q →
      ∃ n : ℕ, n.maxPrimeFac = p ∧ (n + 1).maxPrimeFac = q := by
  intro h
  obtain ⟨n, hn, hn7⟩ := h 2 7 (by norm_num) (by norm_num) (by norm_num)
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num [Nat.maxPrimeFac, Nat.primeFactorsList_zero, List.getLastI] at hn
  have hn1 : n ≠ 1 := by
    rintro rfl
    norm_num [Nat.maxPrimeFac] at hn
  rw [Nat.maxPrimeFac, if_neg hn1] at hn
  have hu : ∀ {d : ℕ}, d.Prime → d ∣ n → d = 2 := by
    intro d hd hdvd
    have hm : d ∈ n.primeFactorsList := (Nat.mem_primeFactorsList hn0).2 ⟨hd, hdvd⟩
    have hl := (Nat.primeFactorsList_sorted n).pairwise.rel_getLast hm
    have hle : d ≤ n.primeFactorsList.getLastI := by
      rw [List.getLastI_eq_getLast?_getD,
        List.getLast?_eq_getLast_of_ne_nil (List.ne_nil_of_mem hm)]
      exact hl
    rw [hn] at hle
    exact Nat.le_antisymm hle hd.two_le
  have hpow : ∃ k, n = 2 ^ k :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn0 hu⟩
  obtain ⟨k, rfl⟩ := hpow
  have hne : (2 ^ k + 1).primeFactorsList ≠ [] := by
    intro he
    rw [Nat.maxPrimeFac,
      if_neg (by have := pow_pos (by omega : 0 < 2) k; omega), he] at hn7
    norm_num [List.getLastI] at hn7
  have heq : (2 ^ k + 1).primeFactorsList.getLast hne = 7 := by
    rw [Nat.maxPrimeFac,
      if_neg (by have := pow_pos (by omega : 0 < 2) k; omega)] at hn7
    rw [← hn7, List.getLastI_eq_getLast?_getD,
      List.getLast?_eq_getLast_of_ne_nil hne]
    simp
  have hdvd : 7 ∣ 2 ^ k + 1 := by
    apply Nat.dvd_of_mem_primeFactorsList
    rw [← heq]
    exact List.getLast_mem hne
  have hcycle_all : ∀ j : ℕ, 2 ^ j % 7 = 1 ∨ 2 ^ j % 7 = 2 ∨ 2 ^ j % 7 = 4 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ, Nat.mul_mod]
      rcases ih with h | h | h <;> rw [h] <;> norm_num
  have hcycle := hcycle_all k
  rcases hdvd with ⟨a, ha⟩
  omega

end Erdos649
