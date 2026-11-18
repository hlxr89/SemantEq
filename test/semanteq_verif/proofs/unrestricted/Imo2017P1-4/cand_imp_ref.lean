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
  exfalso
  have hbad : 3 ∣ (1 : ℕ) := (problem_statement_assumed 1).mp (by
    intro h
    omega)
  omega
