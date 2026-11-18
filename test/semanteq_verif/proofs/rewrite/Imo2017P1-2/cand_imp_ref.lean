import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution_set : Set ℕ := {x | 0 < x ∧ 3 ∣ x}

def is_perfect_square (n : ℕ) : Prop := ∃ k : ℕ, k * k = n

def seq (a₀ : ℕ) : ℕ → ℕ
| 0 => a₀
| n + 1 =>
  let a := seq a₀ n
  if Nat.sqrt a * Nat.sqrt a = a then
    Nat.sqrt a
  else
    a + 3

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a₀ : ℕ) (h : a₀ > 1) :
  (∃ A : ℕ, ∀ N : ℕ, ∃ n ≥ N, seq a₀ n = A) ↔ 3 ∣ a₀ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2017_p1
    (a : ℕ → ℕ → ℕ)
    (ha₀: ∀ x, a x 0 = x)
    (ha₁: ∀ x i, 1 < x → if IsSquare (a x i)
                         then a x (i + 1) = Nat.sqrt (a x i)
                         else a x (i + 1) = a x i + 3) :
    ∀ x > 1, (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set := by
  have hsquare (n : ℕ) : IsSquare n ↔ Nat.sqrt n * Nat.sqrt n = n := by
    constructor
    · rintro ⟨k, rfl⟩
      rw [Nat.sqrt_eq]
    · intro hn
      exact ⟨Nat.sqrt n, hn.symm⟩
  intro x hx
  have ha_seq : ∀ i, a x i = seq x i := by
    intro i
    induction i with
    | zero =>
        rw [ha₀, seq]
    | succ i ih =>
        have hrec : a x (i + 1) = if IsSquare (a x i)
            then Nat.sqrt (a x i) else a x i + 3 := by
          -- non-rewrite step
          by_cases hs : IsSquare (a x i)
          · rw [if_pos hs]
            simpa only [if_pos hs] using ha₁ x i hx
          · rw [if_neg hs]
            simpa only [if_neg hs] using ha₁ x i hx
        simp only [ih, hsquare] at hrec
        rw [seq]
        exact hrec
  have hinf (A : ℕ) : {n | a x n = A}.Infinite ↔
      (∀ N : ℕ, ∃ n ≥ N, seq x n = A) := by
    have hset : {n | a x n = A} = {n | seq x n = A} := by
      ext n
      change a x n = A ↔ seq x n = A
      rw [ha_seq]
    rw [hset, Set.infinite_iff_exists_gt]
    constructor
    · intro hu N
      obtain ⟨n, hn, heq⟩ := hu N
      exact ⟨n, Nat.le_of_lt heq, hn⟩
    · intro hu N
      obtain ⟨n, hn, heq⟩ := hu (N + 1)
      exact ⟨n, heq, lt_of_lt_of_le (Nat.lt_succ_self N) hn⟩
  have hexists : (∃ A, {n | a x n = A}.Infinite) ↔
      (∃ A : ℕ, ∀ N : ℕ, ∃ n ≥ N, seq x n = A) := by
    exact exists_congr hinf
  have hmem : x ∈ solution_set ↔ 3 ∣ x := by
    exact and_iff_right (lt_trans Nat.zero_lt_one hx)
  exact hexists.trans ((problem_statement_assumed x hx).trans hmem.symm)
