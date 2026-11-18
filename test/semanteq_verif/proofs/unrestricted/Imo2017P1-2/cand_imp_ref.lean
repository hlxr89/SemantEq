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
  have square_iff (n : ℕ) : IsSquare n ↔ Nat.sqrt n * Nat.sqrt n = n := by
    constructor
    · rintro ⟨k, rfl⟩
      simp
    · intro hn
      exact ⟨Nat.sqrt n, hn.symm⟩
  have ha_seq : ∀ n, a x n = seq x n := by
    intro n
    induction n with
    | zero => exact ha₀ x
    | succ n ih =>
      rw [seq]
      have hr := ha₁ x n hx
      by_cases hs : IsSquare (a x n)
      · have hr' : a x (n + 1) = Nat.sqrt (a x n) := by simpa [hs] using hr
        have hs' : Nat.sqrt (seq x n) * Nat.sqrt (seq x n) = seq x n := by
          rw [← ih]
          exact (square_iff (a x n)).mp hs
        rw [if_pos hs', ← ih]
        exact hr'
      · have hr' : a x (n + 1) = a x n + 3 := by simpa [hs] using hr
        have hs' : Nat.sqrt (seq x n) * Nat.sqrt (seq x n) ≠ seq x n := by
          intro he
          apply hs
          apply (square_iff (a x n)).mpr
          simpa [ih] using he
        rw [if_neg hs', ← ih]
        exact hr'
  have hcand := problem_statement_assumed x hx
  constructor
  · rintro ⟨A, hA⟩
    have heventual : ∃ A : ℕ, ∀ N : ℕ, ∃ n ≥ N, seq x n = A := by
      refine ⟨A, ?_⟩
      intro N
      obtain ⟨n, hnmem, hnlarge⟩ := (Set.infinite_iff_exists_gt.mp hA) N
      exact ⟨n, Nat.le_of_lt hnlarge, by simpa [ha_seq] using hnmem⟩
    exact ⟨by omega, hcand.mp heventual⟩
  · intro hxsol
    obtain ⟨A, hA⟩ := hcand.mpr hxsol.2
    refine ⟨A, Set.infinite_iff_exists_gt.mpr ?_⟩
    intro N
    obtain ⟨n, hnlarge, hnA⟩ := hA (N + 1)
    exact ⟨n, by simpa [ha_seq] using hnA, by omega⟩
