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
theorem imo2017_p1_assumed
    (a : ℕ → ℕ → ℕ)
    (ha₀: ∀ x, a x 0 = x)
    (ha₁: ∀ x i, 1 < x → if IsSquare (a x i)
                         then a x (i + 1) = Nat.sqrt (a x i)
                         else a x (i + 1) = a x i + 3) :
    ∀ x > 1, (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (a₀ : ℕ) (h : a₀ > 1) :
  (∃ A : ℕ, ∀ N : ℕ, ∃ n ≥ N, seq a₀ n = A) ↔ 3 ∣ a₀ := by
  have hsquare (n : ℕ) : IsSquare n ↔ Nat.sqrt n * Nat.sqrt n = n := by
    rw [← Nat.exists_mul_self]
    simp only [IsSquare, pow_two]
    aesop
  have ha₀ : ∀ x, seq x 0 = x := by
    intro x
    rfl
  have ha₁ : ∀ x i, 1 < x → if IsSquare (seq x i)
      then seq x (i + 1) = Nat.sqrt (seq x i)
      else seq x (i + 1) = seq x i + 3 := by
    intro x i hx
    rw [seq]
    by_cases hs : Nat.sqrt (seq x i) * Nat.sqrt (seq x i) = seq x i <;>
      simp [hs, hsquare]
  have hinf (A : ℕ) : {n | seq a₀ n = A}.Infinite ↔
      ∀ N : ℕ, ∃ n ≥ N, seq a₀ n = A := by
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
  have href := imo2017_p1_assumed seq ha₀ ha₁ a₀ h
  constructor
  · rintro ⟨A, hA⟩
    exact (href.mp ⟨A, (hinf A).mpr hA⟩).2
  · intro hd
    obtain ⟨A, hA⟩ := href.mpr ⟨by omega, hd⟩
    exact ⟨A, (hinf A).mp hA⟩
