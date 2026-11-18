import Mathlib

open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- The unified context is empty.

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {a n : ℕ} (h : a^(n+1) - (a+1)^n = 2001) : ∃! (a : ℕ), ∃ (n : ℕ), a^(n+1) - (a+1)^n = 2001 := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_2001_a5 :
  ∃! p : ℕ × ℕ, p.1 > 0 ∧ p.2 > 0 ∧ p.1^(p.2 + 1) - (p.1 + 1)^(p.2) = 2001 := by
  have pow14_mod (n : ℕ) : 14^n % 169 = (1 + 13*n) % 169 := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ, Nat.mul_mod, ih]
      omega
  have classify_n {n : ℕ} (h : 13^(n+1) - 14^n = 2001) : n = 2 := by
    have hn : 0 < n := by
      by_contra hn
      simp_all
    have hle : 14^n ≤ 13^(n+1) := by omega
    have heq : 13^(n+1) = 2001 + 14^n := by omega
    have hnlt : n < 156 := by
      have hb := one_add_mul_le_pow (R := ℚ) (a := (1/13 : ℚ)) (H := by norm_num) n
      have hp : (0 : ℚ) < 13^n := by positivity
      have hratio : (14/13 : ℚ)^n < 13 := by
        rw [div_pow]
        apply (div_lt_iff₀' hp).2
        exact_mod_cast (show 14^n < 13^(n+1) by omega)
      norm_num [div_eq_mul_inv] at hb hratio
      by_contra hnlt
      have hnq : (156 : ℚ) ≤ n := by
        exact_mod_cast (show 156 ≤ n by omega)
      nlinarith
    have hn2 : 2 ≤ n := by
      by_contra hn2
      have hn1 : n = 1 := by omega
      subst n
      norm_num at h
    have hmodleft : 13^(n+1) % 169 = 0 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn2
      simp [pow_add, pow_succ, Nat.mul_mod]
    have hm : (2001 + 14^n) % 169 = 0 := by omega
    rw [Nat.add_mod, pow14_mod] at hm
    interval_cases n <;> norm_num at hm
    all_goals first | rfl | norm_num at h
  have hseed : 13^(2+1) - (13+1)^2 = 2001 := by norm_num
  obtain ⟨a, ⟨n, hn⟩, ha⟩ := dummy_assumed hseed
  have ha13 : a = 13 := (ha 13 ⟨2, hseed⟩).symm
  subst a
  have hn2 : n = 2 := by
    apply classify_n
    norm_num at hn ⊢
    exact hn
  subst n
  refine ⟨(13, 2), by norm_num, ?_⟩
  intro p hp
  have hp13 : p.1 = 13 := ha p.1 ⟨p.2, hp.2.2⟩
  have hpn2 : p.2 = 2 := by
    apply classify_n
    simpa [hp13] using hp.2.2
  exact Prod.ext hp13 hpn2
