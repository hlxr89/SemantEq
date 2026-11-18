import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a n : ℕ} (ha : 0 < a) (hn : 0 < n) (ha_le : a ≤ n + 1) : a ^ (n + 1) - (a + 1) ^ n = 2001 ↔ a = 2001 ∧ n = 2 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  have add_one_pow_mod_base (a n : ℕ) : (a + 1) ^ n % a = 1 % a := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Nat.mul_mod, ih, ← Nat.mul_mod]
      simp [Nat.add_mod]
  have add_one_pow_mod (a n : ℕ) : (a + 1) ^ n % (a * a) = (1 + n * a) % (a * a) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Nat.mul_mod, ih]
      rw [← Nat.mul_mod]
      have hid : (1 + n * a) * (a + 1) = 1 + (n + 1) * a + n * (a * a) := by ring
      rw [hid, Nat.add_mod]
      simp
  refine ⟨(13, 2), by norm_num, ?_⟩
  intro p hp
  have ha : 0 < p.1 := hp.1
  have hn : 0 < p.2 := hp.2.1
  have heq : p.1 ^ (p.2 + 1) - (p.1 + 1) ^ p.2 = 2001 := hp.2.2
  have hlt : p.2 + 1 < p.1 := by
    by_contra h
    have hle : p.1 ≤ p.2 + 1 := by omega
    have hbad := (dummy_assumed ha hn hle).mp heq
    omega
  have hfull : p.1 ^ (p.2 + 1) = 2001 + (p.1 + 1) ^ p.2 := by omega
  have hmoda := congrArg (fun x : ℕ => x % p.1) hfull
  dsimp at hmoda
  have hzeroa : p.1 ^ (p.2 + 1) % p.1 = 0 := by
    rw [pow_succ]
    simp [Nat.mul_mod]
  have honea : (p.1 + 1) ^ p.2 % p.1 = 1 % p.1 := by
    exact add_one_pow_mod_base p.1 p.2
  rw [hzeroa, Nat.add_mod, honea] at hmoda
  have hdiv : p.1 ∣ 2002 := by
    apply Nat.dvd_of_mod_eq_zero
    rw [show 2002 = 2001 + 1 by omega, Nat.add_mod]
    exact hmoda.symm
  have hle2002 : p.1 ≤ 2002 := Nat.le_of_dvd (by norm_num) hdiv
  have hleft : p.1 ^ (p.2 + 1) % (p.1 * p.1) = 0 := by
    rw [show p.2 + 1 = (p.2 - 1) + 2 by omega, pow_add]
    simp [pow_two, Nat.mul_mod]
  have hmodsq := congrArg (fun x : ℕ => x % (p.1 * p.1)) hfull
  dsimp at hmodsq
  rw [hleft, Nat.add_mod, add_one_pow_mod] at hmodsq
  have hsq : (2002 + p.2 * p.1) % (p.1 * p.1) = 0 := by
    rw [show 2002 + p.2 * p.1 = 2001 + (1 + p.2 * p.1) by omega]
    simpa [Nat.add_mod] using hmodsq.symm
  have hcases :
      (p.1 = 7 ∧ p.2 = 1) ∨ (p.1 = 11 ∧ p.2 = 5) ∨
      (p.1 = 13 ∧ p.2 = 2) ∨ (p.1 = 14 ∧ p.2 = 11) ∨
      (p.1 = 22 ∧ p.2 = 19) ∨ (p.1 = 26 ∧ p.2 = 1) ∨
      (p.1 = 77 ∧ p.2 = 51) ∨ (p.1 = 91 ∧ p.2 = 69) ∨
      (p.1 = 143 ∧ p.2 = 129) ∨ (p.1 = 154 ∧ p.2 = 141) ∨
      (p.1 = 182 ∧ p.2 = 171) ∨ (p.1 = 286 ∧ p.2 = 279) ∨
      (p.1 = 1001 ∧ p.2 = 999) := by
    have ha_mem : p.1 ∈ Nat.divisors 2002 := Nat.mem_divisors.mpr ⟨hdiv, by norm_num⟩
    have hd : Nat.divisors 2002 = {1, 2, 7, 11, 13, 14, 22, 26, 77, 91, 143, 154, 182, 286, 1001, 2002} := by
      native_decide
    rw [hd] at ha_mem
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha_mem
    rcases ha_mem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals norm_num [h] at hsq ⊢ <;> omega
  have hmod3 := congrArg (fun x : ℕ => x % 3) hfull
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨h1, h2⟩
  all_goals first | exact Prod.ext h1 h2 | (set_option maxRecDepth 5000 in norm_num [h1, h2, Nat.add_mod, Nat.pow_mod, pow_succ] at hmod3)
