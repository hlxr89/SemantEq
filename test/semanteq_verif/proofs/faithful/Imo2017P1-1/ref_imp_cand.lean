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
theorem imo2017_p1_assumed
    (a : ℕ → ℕ → ℕ)
    (ha₀: ∀ x, a x 0 = x)
    (ha₁: ∀ x i, 1 < x → if IsSquare (a x i)
                         then a x (i + 1) = Nat.sqrt (a x i)
                         else a x (i + 1) = a x i + 3) :
    ∀ x > 1, (∃ A, {n | a x n = A}.Infinite) ↔ x ∈ solution_set := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (a₀ : ℕ) (ha₀ : a₀ > 1) :
  let sequence : ℕ → ℕ := Nat.rec a₀ (fun n aₙ =>
    if dec_is_perfect_square aₙ then Nat.sqrt aₙ else aₙ + 3)
  (∃ A : ℕ, infinitely_many_eq sequence A) ↔ (3 ∣ a₀) := by
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
  let b : ℕ → ℕ → ℕ := fun x => Nat.rec x (fun _ aₙ =>
    if dec_is_perfect_square aₙ then Nat.sqrt aₙ else aₙ + 3)
  have hb₀ : ∀ x, b x 0 = x := by
    intro x
    rfl
  have href := imo2017_p1_assumed b hb₀ (by
    intro x i _
    simp only [b, Nat.rec_add_one]
    generalize (@Nat.rec (fun _ => ℕ) x (fun (_n : ℕ) (aₙ : ℕ) =>
      if dec_is_perfect_square aₙ then Nat.sqrt aₙ else aₙ + 3) i) = y
    simp only [← square_test]
    cases h : dec_is_perfect_square y <;> simp_all) a₀ ha₀
  change (∃ A : ℕ, infinitely_many_eq (b a₀) A) ↔ (3 ∣ a₀)
  constructor
  · rintro ⟨A, hA⟩
    have hinfinite : {n | b a₀ n = A}.Infinite := by
      apply Set.infinite_of_forall_exists_gt
      intro N
      rcases hA (N + 1) with ⟨n, hn, heq⟩
      exact ⟨n, heq, by omega⟩
    exact (href.mp ⟨A, hinfinite⟩).2
  · intro hdiv
    rcases href.mpr ⟨by omega, hdiv⟩ with ⟨A, hA⟩
    refine ⟨A, ?_⟩
    intro N
    rcases hA.exists_gt N with ⟨n, heq, hn⟩
    exact ⟨n, hn.le, heq⟩
