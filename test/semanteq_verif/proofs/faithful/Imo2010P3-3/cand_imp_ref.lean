import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ g : ℕ+ → ℕ+,
    (∀ m n : ℕ+, ∃ k : ℕ+, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
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
  let gn : ℕ+ → ℕ+ := fun n => toN (g (toZ n))
  constructor
  · intro hsol
    have haff : ∃ c : ℕ, ∀ n : ℕ+, gn n = n + c := by
      change g = id ∨ ∃ c, ∀ x, g x = x + c at hsol
      rcases hsol with hid | ⟨c, hc⟩
      · refine ⟨0, ?_⟩
        intro n
        have h := congrFun hid (toZ n)
        have hv := congrArg (fun z : ℤ>0 => z.1) h
        apply (Nat.cast_inj (R := ℤ)).mp
        dsimp [gn]
        rw [cast_toN (g (toZ n))]
        simpa [toZ] using hv
      · refine ⟨c.1.toNat, ?_⟩
        intro n
        have h := congrArg (fun z : ℤ>0 => z.1) (hc (toZ n))
        apply (Nat.cast_inj (R := ℤ)).mp
        dsimp [gn]
        rw [cast_toN (g (toZ n)), Int.toNat_of_nonneg (le_of_lt c.2)]
        simpa [toZ] using h
    have hsq := (problem_statement_assumed gn).2 haff
    intro m n
    obtain ⟨k, hk⟩ := hsq (toN m) (toN n)
    refine ⟨toZ k, ?_⟩
    apply Subtype.ext
    dsimp [toZ]
    change ((g m).1 + n.1) * ((g n).1 + m.1) = ((k : ℕ) : ℤ) * ((k : ℕ) : ℤ)
    have hgm := cast_toN (g m)
    have hgn := cast_toN (g n)
    have hm := cast_toN m
    have hn := cast_toN n
    rw [← hgm, ← hgn, ← hm, ← hn]
    have hk' : (toN (g m) + toN n) * (toN (g n) + toN m) = k ^ 2 := by
      simpa [gn, toZ_toN] using hk
    exact_mod_cast (show (toN (g m) + toN n) * (toN (g n) + toN m) = k * k by
      simpa [pow_two] using hk')
  · intro hzsq
    have hsq : ∀ m n : ℕ+, ∃ k : ℕ+, (gn m + n) * (gn n + m) = k^2 := by
      intro m n
      rcases hzsq (toZ m) (toZ n) with ⟨r, hr⟩
      refine ⟨toN r, ?_⟩
      have hv := congrArg (fun z : ℤ>0 => z.1) hr
      dsimp [toZ] at hv
      apply PNat.eq
      simp only [PNat.mul_coe, PNat.add_coe, PNat.pow_coe]
      apply (Nat.cast_inj (R := ℤ)).mp
      push_cast
      rw [pow_two]
      change (((gn m : ℕ) : ℤ) + (n : ℕ)) * (((gn n : ℕ) : ℤ) + (m : ℕ)) =
        ((toN r : ℕ) : ℤ) * ((toN r : ℕ) : ℤ)
      rw [cast_toN r]
      have hgm := cast_toN (g (toZ m))
      have hgn := cast_toN (g (toZ n))
      simp only [gn]
      rw [hgm, hgn]
      exact hv
    obtain ⟨c, hc⟩ := (problem_statement_assumed gn).1 hsq
    change g = id ∨ ∃ d, ∀ x, g x = x + d
    by_cases hzero : c = 0
    · left
      funext z
      simp only [id_eq]
      apply Subtype.ext
      have h := hc (toN z)
      simp [hzero] at h
      dsimp [gn] at h
      rw [toZ_toN] at h
      have h' : ((toN (g z) : ℕ) : ℤ) = ((toN z : ℕ) : ℤ) := by exact_mod_cast h
      rw [cast_toN (g z), cast_toN z] at h'
      exact h'
    · right
      let d : ℤ>0 := ⟨c, by exact_mod_cast (Nat.pos_of_ne_zero hzero)⟩
      refine ⟨d, ?_⟩
      intro z
      apply Subtype.ext
      have h := hc (toN z)
      dsimp [d]
      dsimp [gn] at h
      rw [toZ_toN] at h
      have h' : ((toN (g z) : ℕ) : ℤ) = ((toN z : ℕ) : ℤ) + (c : ℤ) := by
        exact_mod_cast h
      rw [cast_toN (g z), cast_toN z] at h'
      exact h'
