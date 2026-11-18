import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution_set : Set ℕ := {x | 0 < x ∧ 3 ∣ x}

def is_perfect_square (n : ℕ) : Bool :=
  let k := Nat.sqrt n
  k^2 = n

noncomputable def seq (a₀ : ℕ) : ℕ → ℕ
| 0 => a₀
| n + 1 =>
  let prev := seq a₀ n
  if is_perfect_square prev then
    Nat.sqrt prev
  else
    prev + 3

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ a₀ : ℕ, a₀ > 1 →
  (∃ A : ℕ, Set.Infinite {n : ℕ | seq a₀ n = A}) ↔
  (3 ∣ a₀) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2017_p1
    (a : ℕ → ℕ → ℕ)
    (ha₀: ∀ x, a x 0 = x)
    (ha₁: ∀ x i, 1 < x → if IsSquare (a x i)
                         then a x (i + 1) = Nat.sqrt (a x i)
                         else a x (i + 1) = a x i + 3) :
    ∀ x > 1, (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set := by
  have square_iff (n : ℕ) : is_perfect_square n = true ↔ IsSquare n := by
    constructor
    · intro h
      have hs : Nat.sqrt n ^ 2 = n := of_decide_eq_true h
      exact ⟨Nat.sqrt n, by simpa only [pow_two] using hs.symm⟩
    · rintro ⟨r, hr⟩
      apply decide_eq_true
      rw [hr, Nat.sqrt_eq]
      exact pow_two r
  intro x hx
  have hseq : ∀ n, a x n = seq x n := by
    intro n
    induction n with -- non-rewrite step: uniqueness of the recursive sequence
    | zero =>
        exact ha₀ x
    | succ n ih =>
        have hrec := ha₁ x n hx
        rw [ih] at hrec
        rw [seq]
        by_cases hs : IsSquare (seq x n)
        · rw [if_pos hs] at hrec
          simp only [(square_iff _).mpr hs, if_true]
          exact hrec
        · rw [if_neg hs] at hrec
          have hb : is_perfect_square (seq x n) = false := by
            cases h : is_perfect_square (seq x n) with
            | false => rfl
            | true => exact (hs ((square_iff _).mp h)).elim
          simp only [hb, Bool.false_eq_true, if_false]
          exact hrec
  simp only [hseq]
  rw [show x ∈ solution_set ↔ 3 ∣ x by
    simp only [solution_set, Set.mem_setOf_eq, and_iff_right (Nat.zero_lt_of_lt hx)]]
  have hc := problem_statement_assumed x
  constructor
  · intro hInf
    exact hc.mp (fun _ => hInf)
  · intro hdiv
    exact hc.mpr hdiv hx
