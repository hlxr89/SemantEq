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
  have hsquare (n : ℕ) : IsSquare n ↔ Nat.sqrt n * Nat.sqrt n = n := by
    rw [← Nat.exists_mul_self]
    simp only [IsSquare, pow_two]
    aesop
  have hseq : ∀ n, a x n = seq x n := by
    intro n
    induction n with
    | zero => simpa [seq] using ha₀ x
    | succ n ih =>
      rw [seq, ← ih]
      have hr := ha₁ x n hx
      by_cases hs : Nat.sqrt (a x n) * Nat.sqrt (a x n) = a x n <;>
        simp [hs, hsquare] at hr ⊢
      all_goals exact hr
  have hinf (A : ℕ) : {n | seq x n = A}.Infinite ↔
      ∀ N : ℕ, ∃ n ≥ N, seq x n = A := by
    constructor
    · intro hi N
      obtain ⟨n, hn, hN⟩ := hi.exists_gt N
      exact ⟨n, hN.le, hn⟩
    · intro hu
      by_contra hi
      rw [Set.not_infinite] at hi
      obtain ⟨B, hB⟩ := bddAbove_def.mp hi.bddAbove
      obtain ⟨n, hn, hna⟩ := hu (B + 1)
      have := hB n hna
      omega
  have hcand := problem_statement_assumed x hx
  constructor
  · rintro ⟨A, hA⟩
    have hAs : {n | seq x n = A}.Infinite := by
      simpa only [← hseq] using hA
    exact ⟨by omega, hcand.mp ⟨A, (hinf A).mp hAs⟩⟩
  · rintro ⟨hpos, hd⟩
    obtain ⟨A, hA⟩ := hcand.mpr hd
    have hAs := (hinf A).mpr hA
    refine ⟨A, ?_⟩
    simpa only [← hseq] using hAs
