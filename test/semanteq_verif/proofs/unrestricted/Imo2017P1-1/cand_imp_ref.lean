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
  intro x hx
  let sequence : ℕ → ℕ := Nat.rec x (fun _ aₙ =>
    if dec_is_perfect_square aₙ then Nat.sqrt aₙ else aₙ + 3)
  have hsq (n : ℕ) : dec_is_perfect_square n = true ↔ IsSquare n := by
    simp only [dec_is_perfect_square, decide_eq_true_eq]
    constructor
    · intro h
      exact ⟨Nat.sqrt n, h⟩
    · rintro ⟨k, rfl⟩
      simp [Nat.sqrt_eq]
  have hsequence (n : ℕ) : a x n = sequence n := by
    induction n with
    | zero =>
        simpa [sequence] using ha₀ x
    | succ n ih =>
        have hr := ha₁ x n hx
        by_cases h : IsSquare (a x n)
        · have hd : dec_is_perfect_square (sequence n) = true :=
            (hsq _).2 (ih ▸ h)
          simpa [h, ih, sequence, hd] using hr
        · have hd : dec_is_perfect_square (sequence n) = false := by
            apply Bool.eq_false_of_not_eq_true
            intro ht
            exact h (ih.symm ▸ (hsq _).1 ht)
          simpa [h, ih, sequence, hd] using hr
  have hcand := problem_statement_assumed x hx
  change (∃ A, {n | a x n = A}.Infinite) ↔ 0 < x ∧ 3 ∣ x
  rw [and_iff_right (show 0 < x by omega)]
  rw [← hcand]
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨A, ?_⟩
    intro N
    by_contra h
    push_neg at h
    apply hA
    apply Set.Finite.subset (Set.finite_Iio N)
    intro n hn
    by_contra hlt
    exact h n (by omega) (by simpa [hsequence n] using hn)
  · rintro ⟨A, hA⟩
    refine ⟨A, ?_⟩
    intro hf
    rcases hf.bddAbove with ⟨B, hB⟩
    rcases hA (B + 1) with ⟨n, hn, heq⟩
    have hle := hB (by simpa [hsequence n] using heq)
    omega
