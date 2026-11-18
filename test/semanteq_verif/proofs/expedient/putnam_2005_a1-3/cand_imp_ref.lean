import Mathlib

open Nat

-- ===== unified context (both sides' local defs, merged) =====
def is_power_of_2_3 (n : ℕ) : Prop := ∃ r s : ℕ, n = 2^r * 3^s

def no_divides_in_list (l : List ℕ) : Prop :=
  ∀ a₁ a₂, a₁ ∈ l → a₂ ∈ l → a₁ ≠ a₂ → ¬(a₁ ∣ a₂)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (n : ℕ) (hn : 0 < n) :
  ∃ l : List ℕ, 
    (∀ x ∈ l, is_power_of_2_3 x) ∧
    (l.sum = n) ∧
    (no_divides_in_list l) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2005_a1
: ∀ n : ℤ, n > 0 → (∃ k : ℕ, ∃ a : Fin k → Fin 2 → ℕ, n = ∑ i : Fin k, 2^(a i 0)*3^(a i 1) ∧
(∀ i j : Fin k, i ≠ j → ¬(2^(a i 0)*3^(a i 1) ∣ 2^(a j 0)*3^(a j 1)))) :=
by
  have hrep : ∀ n : ℕ, ∃ k : ℕ, ∃ a : Fin k → Fin 2 → ℕ,
      n = ∑ i : Fin k, 2 ^ (a i 0) * 3 ^ (a i 1) ∧
      ∀ i j : Fin k, i ≠ j → ¬(2 ^ (a i 0) * 3 ^ (a i 1) ∣
        2 ^ (a j 0) * 3 ^ (a j 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n = 0
      · subst n
        exact ⟨0, Fin.elim0, by simp, by simp⟩
      · by_cases hn_even : Even n
        · rcases hn_even with ⟨q, hq⟩
          let m := n / 2
          have hm_lt : m < n := by
            dsimp [m]
            omega
          obtain ⟨k, a, hsum, hanti⟩ := ih m hm_lt
          let b : Fin k → Fin 2 → ℕ := fun i => ![a i 0 + 1, a i 1]
          refine ⟨k, b, ?_, ?_⟩
          · have hdouble : (∑ i : Fin k, 2 ^ (b i 0) * 3 ^ (b i 1)) =
                2 * ∑ i : Fin k, 2 ^ (a i 0) * 3 ^ (a i 1) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              simp [b, pow_succ]
              ring
            rw [hdouble, ← hsum]
            dsimp [m]
            omega
          · intro i j hij hdvd
            apply hanti i j hij
            exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp (by
              simpa [b, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdvd)
        · have hn_odd : Odd n := (Nat.not_even_iff_odd.mp hn_even)
          let s := Nat.log 3 n
          let p := 3 ^ s
          let m := (n - p) / 2
          have hp_le : p ≤ n := by
            exact Nat.pow_log_le_self 3 hn
          have hp_pos : 0 < p := pow_pos (by omega) _
          have hp_odd : Odd p := by
            exact Odd.pow (by norm_num)
          have hsub_even : Even (n - p) := by
            rcases hn_odd with ⟨u, hu⟩
            rcases hp_odd with ⟨v, hv⟩
            refine ⟨u - v, ?_⟩
            omega
          have hm_lt : m < n := by
            dsimp [m]
            omega
          obtain ⟨k, a, hsum, hanti⟩ := ih m hm_lt
          let b : Fin (k + 1) → Fin 2 → ℕ := fun i =>
            Fin.cases ![0, s] (fun j => ![a j 0 + 1, a j 1]) i
          refine ⟨k + 1, b, ?_, ?_⟩
          · have hdouble : (∑ i : Fin k, 2 ^ (b i.succ 0) * 3 ^ (b i.succ 1)) =
                2 * ∑ i : Fin k, 2 ^ (a i 0) * 3 ^ (a i 1) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro i _
              simp [b, pow_succ]
              ring
            rw [Fin.sum_univ_succ, hdouble, ← hsum]
            simp [b]
            change n = p + 2 * m
            rcases hsub_even with ⟨w, hw⟩
            have hdiv : 2 ∣ n - p := ⟨w, by omega⟩
            have hcancel := Nat.div_mul_cancel hdiv
            dsimp [m] at hcancel ⊢
            omega
          · intro i j
            revert j
            refine Fin.cases ?_ (fun i => ?_) i
            · intro j
              refine Fin.cases ?_ (fun j => ?_) j
              · intro hij
                exact (hij rfl).elim
              · intro hij
                simp [b, pow_succ]
                intro hdvd
                have hx_le : 2 ^ (a j 0) * 3 ^ (a j 1) ≤ m := by
                  rw [hsum]
                  exact Finset.single_le_sum (s := Finset.univ)
                    (fun i _ => Nat.zero_le (2 ^ (a i 0) * 3 ^ (a i 1))) (Finset.mem_univ j)
                have hp_lt : m < p := by
                  dsimp [m, p, s]
                  have hn_lt := Nat.lt_pow_succ_log_self (by omega : 1 < 3) n
                  omega
                have hp_dvd : p ∣ 2 * (2 ^ (a j 0) * 3 ^ (a j 1)) := by
                  simpa [p, s, pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdvd
                have hp_coprime : Nat.Coprime p 2 := hp_odd.coprime_two_right
                have : p ∣ 2 ^ (a j 0) * 3 ^ (a j 1) :=
                  hp_coprime.dvd_of_dvd_mul_left hp_dvd
                exact (Nat.not_dvd_of_pos_of_lt (by positivity) (lt_of_le_of_lt hx_le hp_lt)) this
            · intro j
              refine Fin.cases ?_ (fun j => ?_) j
              · intro hij
                simp [b, pow_succ]
                intro hdvd
                have htwo : 2 ∣ p := by
                  apply dvd_trans (show 2 ∣ 2 * (2 ^ (a i 0) * 3 ^ (a i 1)) from dvd_mul_right 2 _) (by
                    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdvd)
                exact hp_odd.not_two_dvd_nat htwo
              · intro hij
                simp [b, pow_succ]
                intro hdvd
                apply hanti i j
                · intro h
                  subst j
                  exact hij rfl
                exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < 2)).mp (by
                  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hdvd)
  intro n hn
  have hn_nat : ((n.toNat : ℕ) : ℤ) = n := by omega
  obtain ⟨k, a, hsum, hanti⟩ := hrep n.toNat
  refine ⟨k, a, ?_, ?_⟩
  · rw [← hn_nat]
    exact_mod_cast hsum
  · intro i j hij hdvd
    apply hanti i j hij
    exact_mod_cast hdvd
