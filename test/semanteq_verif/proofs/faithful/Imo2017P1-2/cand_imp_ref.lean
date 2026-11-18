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
  intro x hx
  have square_iff (n : ℕ) :
      IsSquare n ↔ Nat.sqrt n * Nat.sqrt n = n := by
    constructor
    · rintro ⟨r, rfl⟩
      simp
    · intro hn
      exact ⟨Nat.sqrt n, hn.symm⟩
  have hseq : ∀ n, a x n = seq x n := by
    intro n
    induction n with
    | zero => simpa [seq] using ha₀ x
    | succ n ih =>
        have hstep := ha₁ x n hx
        simp only [square_iff] at hstep
        rw [seq]
        simp only [ih] at hstep
        by_cases hs : Nat.sqrt (seq x n) * Nat.sqrt (seq x n) = seq x n
        · simpa [hs] using hstep
        · simpa [hs] using hstep
  have hcand := problem_statement_assumed x hx
  constructor
  · rintro ⟨A, hA⟩
    apply And.intro (by omega)
    apply hcand.mp
    refine ⟨A, ?_⟩
    intro N
    obtain ⟨n, han, hn⟩ := hA.exists_gt N
    refine ⟨n, by omega, ?_⟩
    exact (hseq n).symm.trans han
  · intro hmem
    obtain ⟨A, hA⟩ := hcand.mpr hmem.2
    refine ⟨A, ?_⟩
    apply Set.infinite_of_forall_exists_gt
    intro N
    obtain ⟨n, hn, han⟩ := hA (N + 1)
    refine ⟨n, ?_, by omega⟩
    change a x n = A
    exact (hseq n).trans han
