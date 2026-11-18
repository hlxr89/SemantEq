import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ g : ℕ+ → ℕ+, 
    (∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) →
    ∃ c : ℕ, ∀ n : ℕ+, g n = n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  constructor
  · rintro (rfl | ⟨c, hc⟩) m n
    · refine ⟨m + n, ?_⟩
      apply Subtype.ext
      dsimp
      ring
    · refine ⟨m + c + n, ?_⟩
      rw [hc m, hc n]
      apply Subtype.ext
      dsimp
      ring
  · intro h
    let e : ℕ+ ≃ ℤ>0 :=
      { toFun := fun n => ⟨n, by exact_mod_cast n.property⟩
        invFun := fun z => ⟨z.val.toNat, by omega⟩
        left_inv := by
          intro n
          apply Subtype.eq
          rfl
        right_inv := by
          intro z
          ext
          simp [Int.toNat_of_nonneg (le_of_lt z.property)] }
    let f : ℕ+ → ℕ+ := fun n => e.symm (g (e n))
    have hf : ∀ m n : ℕ+, ∃ k : ℕ,
        (f m + n) * (f n + m) = k^2 := by
      intro m n
      rcases h (e m) (e n) with ⟨z, hz⟩
      refine ⟨z.val.toNat, ?_⟩
      have hzi := congrArg Subtype.val hz
      simp only [f, Equiv.symm_apply_apply] at hzi
      have hzi' :
          (((g (e m) : ℤ) + (e n : ℤ)) *
            ((g (e n) : ℤ) + (e m : ℤ))) = z.val * z.val := by
        simpa using hzi
      change
        ((f m : ℕ) + (n : ℕ)) * ((f n : ℕ) + (m : ℕ)) = z.val.toNat ^ 2
      simp only [f]
      change
        ((g (e m)).val.toNat + (n : ℕ)) *
          ((g (e n)).val.toNat + (m : ℕ)) = z.val.toNat ^ 2
      have hgm : (g (e m)).val = ((g (e m)).val.toNat : ℤ) :=
        (Int.toNat_of_nonneg (le_of_lt (g (e m)).property)).symm
      have hgn : (g (e n)).val = ((g (e n)).val.toNat : ℤ) :=
        (Int.toNat_of_nonneg (le_of_lt (g (e n)).property)).symm
      have hzv : z.val = (z.val.toNat : ℤ) :=
        (Int.toNat_of_nonneg (le_of_lt z.property)).symm
      rw [hgm, hgn, hzv] at hzi'
      dsimp [e] at hzi'
      simp only [pow_two]
      exact_mod_cast hzi'
    rcases problem_statement_assumed f hf with ⟨c, hc⟩
    by_cases hc0 : c = 0
    · left
      funext z
      have hz := hc (e.symm z)
      have hz' : f (e.symm z) = e.symm z := by
        simpa [hc0] using hz
      have := congrArg e hz'
      simpa [f] using this
    · right
      have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
      refine ⟨e ⟨c, hcpos⟩, fun z => ?_⟩
      apply Subtype.ext
      change (g z).val = z.val + (c : ℤ)
      have hz := hc (e.symm z)
      have hz' : (g z).val.toNat = z.val.toNat + c := by
        simpa [f] using hz
      have hz'' := congrArg (fun x : ℕ => (x : ℤ)) hz'
      push_cast at hz''
      omega
