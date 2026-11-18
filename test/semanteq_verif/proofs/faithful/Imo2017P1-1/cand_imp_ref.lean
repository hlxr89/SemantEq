import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev solution_set : Set ℕ := {x | 0 < x ∧ 3 ∣ x}

def is_perfect_square (n : ℕ) : Prop :=
  ∃ k : ℕ, k * k = n

def dec_is_perfect_square (n : ℕ) : Bool :=
  Nat.sqrt n * Nat.sqrt n = n

def infinitely_many_eq (f : ℕ → ℕ) (A : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n ≥ N, f n = A

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (a₀ : ℕ) (ha₀ : a₀ > 1) :
  let sequence : ℕ → ℕ := Nat.rec a₀ (fun n aₙ =>
    if dec_is_perfect_square aₙ then Nat.sqrt aₙ else aₙ + 3)
  (∃ A : ℕ, infinitely_many_eq sequence A) ↔ (3 ∣ a₀) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2017_p1
    (a : ℕ → ℕ → ℕ)
    (ha₀: ∀ x, a x 0 = x)
    (ha₁: ∀ x i, 1 < x → if IsSquare (a x i)
                         then a x (i + 1) = Nat.sqrt (a x i)
                         else a x (i + 1) = a x i + 3) :
    ∀ x > 1, (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set := by
  classical
  letI : DecidablePred (fun n : ℕ => IsSquare n) := fun _ => Classical.propDecidable _
  have square_test (n : ℕ) : dec_is_perfect_square n = true ↔ IsSquare n := by
    constructor
    · intro h
      have hn : Nat.sqrt n * Nat.sqrt n = n :=
        of_decide_eq_true (by simpa [dec_is_perfect_square] using h)
      exact ⟨Nat.sqrt n, hn.symm⟩
    · rintro ⟨r, rfl⟩
      simp [dec_is_perfect_square, Nat.sqrt_eq]
  intro x hx
  let sequence : ℕ → ℕ := Nat.rec x (fun _ aₙ =>
    if dec_is_perfect_square aₙ then Nat.sqrt aₙ else aₙ + 3)
  have hcand : (∃ A : ℕ, infinitely_many_eq sequence A) ↔ (3 ∣ x) := by
    simpa [sequence] using problem_statement_assumed x hx
  have hsequence : ∀ n, sequence n = a x n := by
    intro n
    induction n with
    | zero => exact (ha₀ x).symm
    | succ n ih =>
      rw [show sequence (n + 1) =
          (if dec_is_perfect_square (sequence n)
           then Nat.sqrt (sequence n) else sequence n + 3) by rfl, ih]
      by_cases h : IsSquare (a x n)
      · have ht := (square_test _).mpr h
        have hrec := ha₁ x n hx
        rw [if_pos h] at hrec
        simpa [ht] using hrec.symm
      · have ht : dec_is_perfect_square (a x n) = false := by
          apply Bool.eq_false_iff.mpr
          exact fun htrue => h ((square_test _).mp htrue)
        have hrec := ha₁ x n hx
        rw [if_neg h] at hrec
        simpa [ht] using hrec.symm
  change (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set
  constructor
  · rintro ⟨A, hA⟩
    have hfrequent : infinitely_many_eq sequence A := by
      intro N
      rcases hA.exists_gt N with ⟨n, heq, hn⟩
      exact ⟨n, hn.le, by simpa [hsequence n] using heq⟩
    exact ⟨by omega, hcand.mp ⟨A, hfrequent⟩⟩
  · rintro ⟨_, hdiv⟩
    rcases hcand.mpr hdiv with ⟨A, hA⟩
    refine ⟨A, Set.infinite_of_forall_exists_gt ?_⟩
    intro N
    rcases hA (N + 1) with ⟨n, hn, heq⟩
    exact ⟨n, by simpa [hsequence n] using heq, by omega⟩
