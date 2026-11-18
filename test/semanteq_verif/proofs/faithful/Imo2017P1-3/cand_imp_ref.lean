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
  have hsquare (n : ℕ) : IsSquare n ↔ Nat.sqrt n * Nat.sqrt n = n := by
    constructor
    · rintro ⟨k, rfl⟩
      simp
    · intro h
      exact ⟨Nat.sqrt n, by simpa [pow_two] using h.symm⟩
  have hseq : ∀ n, a x n = a_seq x n := by
    intro n
    induction n with
    | zero => simpa [a_seq] using ha₀ x
    | succ n ih =>
        rw [a_seq]
        have hstep := ha₁ x n hx
        by_cases hs : IsSquare (a x n)
        · rw [if_pos hs] at hstep
          rw [hstep, ih]
          simp [(hsquare _).mp (ih ▸ hs)]
        · rw [if_neg hs] at hstep
          rw [hstep, ih]
          simp [mt (hsquare _).mpr (ih ▸ hs)]
  have hcand : (∃ A : ℕ, Set.Infinite {n : ℕ | a_seq x n = A}) ↔ 3 ∣ x := by
    constructor
    · intro h
      exact (problem_statement_assumed x).mp (fun _ => h)
    · intro h
      exact (problem_statement_assumed x).mpr h hx
  have hevents : (∃ A, {n | a x n = A}.Infinite) ↔
      (∃ A : ℕ, Set.Infinite {n : ℕ | a_seq x n = A}) := by
    simp only [hseq]
  have hpos : 0 < x := by omega
  rw [hevents, hcand]
  simp [solution_set, hpos]
