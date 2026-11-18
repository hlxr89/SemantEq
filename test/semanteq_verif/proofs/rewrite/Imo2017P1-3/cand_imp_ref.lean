import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution_set : Set ℕ := {x | 0 < x ∧ 3 ∣ x}

def is_perfect_square (n : ℕ) : Prop := ∃ k : ℕ, n = k * k

def a_seq (a₀ : ℕ) : ℕ → ℕ
| 0 => a₀
| n + 1 =>
  let aₙ := a_seq a₀ n
  let k := Nat.sqrt aₙ
  if k * k = aₙ then
    k
  else
    aₙ + 3

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ a₀ : ℕ, a₀ > 1 → 
  (∃ A : ℕ, Set.Infinite {n : ℕ | a_seq a₀ n = A}) ↔ 
  3 ∣ a₀ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2017_p1
    (a : ℕ → ℕ → ℕ)
    (ha₀: ∀ x, a x 0 = x)
    (ha₁: ∀ x i, 1 < x → if IsSquare (a x i)
                         then a x (i + 1) = Nat.sqrt (a x i)
                         else a x (i + 1) = a x i + 3) :
    ∀ x > 1, (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set := by
  intro x hx
  have hsquare : ∀ n : ℕ, IsSquare n ↔ Nat.sqrt n * Nat.sqrt n = n := by
    intro n
    constructor
    · rintro ⟨k, rfl⟩
      simp only [Nat.sqrt_eq]
    · intro h
      exact ⟨Nat.sqrt n, h.symm⟩
  have haeq : ∀ n : ℕ, a x n = a_seq x n := by
    intro n
    induction n with
    | zero =>
        exact ha₀ x
    | succ n ih =>
        have hstep := ha₁ x n hx
        simp only [hsquare] at hstep
        simp only [a_seq]
        rw [← ih]
        by_cases hs : Nat.sqrt (a x n) * Nat.sqrt (a x n) = a x n
        · simpa only [hs, if_true] using hstep
        · simpa only [hs, if_false] using hstep
  have h := problem_statement_assumed x
  have hcanon : (∃ A : ℕ, Set.Infinite {n : ℕ | a_seq x n = A}) ↔ 3 ∣ x := by
    constructor
    · intro hinfinite
      exact h.mp (fun _ => hinfinite)
    · intro hdiv
      exact (h.mpr hdiv) hx
  simp only [haeq]
  rw [hcanon]
  change (3 ∣ x) ↔ 0 < x ∧ 3 ∣ x
  exact (and_iff_right (Nat.zero_lt_of_lt hx)).symm
