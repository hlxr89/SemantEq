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
  have square_iff (n : ℕ) :
      IsSquare n ↔ Nat.sqrt n * Nat.sqrt n = n := by
    constructor
    · rintro ⟨r, rfl⟩
      simp
    · intro hn
      exact ⟨Nat.sqrt n, hn.symm⟩
  have hrec : ∀ x i, 1 < x → if IsSquare (seq x i)
      then seq x (i + 1) = Nat.sqrt (seq x i)
      else seq x (i + 1) = seq x i + 3 := by
    intro x i _
    simp only [square_iff]
    simp only [seq]
    split <;> simp_all
  have href := imo2017_p1_assumed (fun x n ↦ seq x n)
    (by intro x; rfl) hrec a₀ h
  constructor
  · rintro ⟨A, hA⟩
    have hinf : {n | seq a₀ n = A}.Infinite := by
      apply Set.infinite_of_forall_exists_gt
      intro N
      obtain ⟨n, hn, han⟩ := hA (N + 1)
      exact ⟨n, han, by omega⟩
    exact (href.mp ⟨A, hinf⟩).2
  · intro hdvd
    obtain ⟨A, hA⟩ := href.mpr ⟨by omega, hdvd⟩
    refine ⟨A, ?_⟩
    intro N
    obtain ⟨n, han, hn⟩ := hA.exists_gt N
    exact ⟨n, by omega, han⟩
