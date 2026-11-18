import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem imo2010_p3_assumed (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ g : ℕ+ → ℕ+,
    (∀ m n : ℕ+, ∃ k : ℕ+, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  intro g
  let toZ : ℕ+ → ℤ>0 := fun n => ⟨(n : ℕ), by exact_mod_cast n.pos⟩
  let toN : ℤ>0 → ℕ+ := fun z => ⟨z.1.toNat, by omega⟩
  have toN_toZ (n : ℕ+) : toN (toZ n) = n := by
    apply PNat.eq
    simp [toN, toZ]
  have toZ_toN (z : ℤ>0) : toZ (toN z) = z := by
    apply Subtype.ext
    simp [toN, toZ, Int.toNat_of_nonneg (le_of_lt z.2)]
  have cast_toN (z : ℤ>0) : ((toN z : ℕ) : ℤ) = z.1 := by
    exact Int.toNat_of_nonneg (le_of_lt z.2)
  let gz : ℤ>0 → ℤ>0 := fun z => toZ (g (toN z))
  constructor
  · intro hs
    have hzsq : ∀ m n, IsSquare ((gz m + n) * (gz n + m)) := by
      intro m n
      obtain ⟨k, hk⟩ := hs (toN m) (toN n)
      refine ⟨toZ k, ?_⟩
      apply Subtype.ext
      dsimp [gz, toZ]
      change (((g (toN m) : ℕ) : ℤ) + n.1) *
          (((g (toN n) : ℕ) : ℤ) + m.1) = ((k : ℕ) : ℤ) * ((k : ℕ) : ℤ)
      rw [← cast_toN m, ← cast_toN n]
      exact_mod_cast (show (g (toN m) + toN n) * (g (toN n) + toN m) = k * k by
        simpa [pow_two] using hk)
    have hsol := (imo2010_p3_assumed gz).2 hzsq
    change gz = id ∨ ∃ c, ∀ x, gz x = x + c at hsol
    rcases hsol with hid | ⟨c, hc⟩
    · refine ⟨0, ?_⟩
      intro n
      have h := congrFun hid (toZ n)
      have hv := congrArg (fun z : ℤ>0 => z.1) h
      dsimp [gz, toZ] at hv
      rw [toN_toZ] at hv
      have hv' : (g n : ℕ) = (n : ℕ) := by exact_mod_cast hv
      simpa using hv'
    · refine ⟨c.1.toNat, ?_⟩
      intro n
      have h := hc (toZ n)
      have hv := congrArg (fun z : ℤ>0 => z.1) h
      dsimp [gz, toZ] at hv
      rw [toN_toZ] at hv
      have hc' := cast_toN c
      omega
  · rintro ⟨c, hc⟩
    have hsol : gz ∈ SolutionSet := by
      change gz = id ∨ ∃ d, ∀ x, gz x = x + d
      by_cases hzero : c = 0
      · left
        funext z
        change toZ (g (toN z)) = z
        rw [← toZ_toN z]
        congr 1
        apply PNat.eq
        simpa [hzero] using hc (toN z)
      · right
        let d : ℤ>0 := ⟨c, by exact_mod_cast (Nat.pos_of_ne_zero hzero)⟩
        refine ⟨d, ?_⟩
        intro z
        apply Subtype.ext
        have h := hc (toN z)
        dsimp [gz, toZ, d]
        have hz := cast_toN z
        omega
    have hzsq := (imo2010_p3_assumed gz).1 hsol
    intro m n
    rcases hzsq (toZ m) (toZ n) with ⟨r, hr⟩
    refine ⟨toN r, ?_⟩
    have hv := congrArg (fun z : ℤ>0 => z.1) hr
    dsimp [gz, toZ] at hv
    rw [toN_toZ, toN_toZ] at hv
    apply PNat.eq
    simp only [PNat.mul_coe, PNat.add_coe, PNat.pow_coe]
    apply (Nat.cast_inj (R := ℤ)).mp
    push_cast
    rw [pow_two]
    change (((g m : ℕ) : ℤ) + (n : ℕ)) * (((g n : ℕ) : ℤ) + (m : ℕ)) =
      ((toN r : ℕ) : ℤ) * ((toN r : ℕ) : ℤ)
    rw [cast_toN r]
    exact hv
