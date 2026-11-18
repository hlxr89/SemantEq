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
  intro x hx
  let sequence : ℕ → ℕ := Nat.rec x (fun n aₙ =>
    if dec_is_perfect_square aₙ then Nat.sqrt aₙ else aₙ + 3)
  have hsquare (n : ℕ) : IsSquare n ↔ Nat.sqrt n * Nat.sqrt n = n := by
    rw [isSquare_iff_exists_mul_self]
    constructor
    · rintro ⟨k, rfl⟩
      simp
    · intro h
      exact ⟨Nat.sqrt n, h.symm⟩
  have hseq : ∀ (n : ℕ), a x n = sequence n := by
    intro n
    induction n with
    | zero => simpa [sequence] using ha₀ x
    | succ n ih =>
      have hstep := ha₁ x n hx
      rw [ih] at hstep
      change a x (n + 1) = if dec_is_perfect_square (sequence n)
        then Nat.sqrt (sequence n) else sequence n + 3
      split <;> rename_i hb
      · have he : Nat.sqrt (sequence n) * Nat.sqrt (sequence n) = sequence n := by
          simpa [dec_is_perfect_square] using hb
        have h := (hsquare (sequence n)).mpr he
        simp [h] at hstep
        exact hstep
      · have he : Nat.sqrt (sequence n) * Nat.sqrt (sequence n) ≠ sequence n := by
          intro he
          apply hb
          simp [dec_is_perfect_square, he]
        have h : ¬IsSquare (sequence n) := fun h => he ((hsquare (sequence n)).mp h)
        simp [h] at hstep
        exact hstep
  have hinf (f : ℕ → ℕ) (A : ℕ) :
      {n | f n = A}.Infinite ↔ infinitely_many_eq f A := by
    constructor
    · intro h N
      by_contra! hn
      apply h
      apply (Set.finite_Iio N).subset
      intro n hnA
      simp only [Set.mem_setOf_eq] at hnA
      simp only [Set.mem_Iio]
      by_contra hnot
      exact hn n (le_of_not_gt hnot) hnA
    · intro h
      apply Set.infinite_of_forall_exists_gt
      intro N
      obtain ⟨n, hn, hfn⟩ := h (N + 1)
      exact ⟨n, hfn, by omega⟩
  have hmain := problem_statement_assumed x hx
  simpa only [hseq, hinf, solution_set, Set.mem_setOf_eq,
    and_iff_right (by omega : 0 < x)] using hmain
