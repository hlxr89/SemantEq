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
    simp only [is_perfect_square, isSquare_iff_exists_sq]
    simpa [eq_comm] using (Nat.exists_mul_self' n).symm
  intro x hx
  have hseq : ∀ n, a x n = seq x n := by
    intro n
    induction n with
    | zero => simpa [seq] using ha₀ x
    | succ n ih =>
      have hrec := ha₁ x n hx
      by_cases hs : IsSquare (a x n)
      · have hb : is_perfect_square (seq x n) = true :=
          (square_iff _).2 (ih ▸ hs)
        calc
          a x (n + 1) = Nat.sqrt (a x n) := by simpa [hs] using hrec
          _ = Nat.sqrt (seq x n) := congrArg Nat.sqrt ih
          _ = seq x (n + 1) := by simp [seq, hb]
      · have hb : is_perfect_square (seq x n) = false := by
          apply Bool.eq_false_iff.mpr
          intro ht
          apply hs
          exact ih.symm ▸ (square_iff _).1 ht
        calc
          a x (n + 1) = a x n + 3 := by simpa [hs] using hrec
          _ = seq x n + 3 := congrArg (· + 3) ih
          _ = seq x (n + 1) := by simp [seq, hb]
  have hsets (A : ℕ) : {n : ℕ | a x n = A} = {n : ℕ | seq x n = A} := by
    ext n
    simp only [Set.mem_setOf_eq, hseq n]
  have hcand := problem_statement_assumed x
  constructor
  · rintro ⟨A, hA⟩
    have hA' : Set.Infinite {n : ℕ | seq x n = A} := by
      rw [← hsets A]
      exact hA
    exact ⟨Nat.zero_lt_of_lt hx, hcand.mp (fun _ => ⟨A, hA'⟩)⟩
  · rintro ⟨_, hdvd⟩
    rcases hcand.mpr hdvd hx with ⟨A, hA⟩
    refine ⟨A, ?_⟩
    rw [hsets A]
    exact hA
