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
    (∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  intro g
  let e : ℕ+ ≃ ℤ>0 :=
    { toFun := fun n => ⟨n, by exact_mod_cast n.prop⟩
      invFun := fun z => ⟨z.val.toNat, by omega⟩
      left_inv := by
        intro n
        apply Subtype.ext
        change (Int.ofNat n.val).toNat = n.val
        simp
      right_inv := by
        intro z
        ext
        simp [Int.toNat_of_nonneg (le_of_lt z.prop)] }
  let gz : ℤ>0 → ℤ>0 := fun z => e (g (e.symm z))
  constructor
  · intro hsquare
    have hzsquare : ∀ m n, IsSquare ((gz m + n) * (gz n + m)) := by
      intro m n
      rcases hsquare (e.symm m) (e.symm n) with ⟨k, hk⟩
      have hkpos : 0 < k := by
        by_contra h
        have hkzero : k = 0 := Nat.eq_zero_of_not_pos h
        subst k
        norm_num at hk
      refine ⟨(⟨(k : ℤ), by exact_mod_cast hkpos⟩ : ℤ>0), ?_⟩
      apply Subtype.ext
      calc
        (((gz m + n) * (gz n + m) : ℤ>0).val) =
            ((gz m).val + n.val) * ((gz n).val + m.val) := rfl
        _ = (k : ℤ) * (k : ℤ) := by
          simpa [gz, e, pow_two, Int.toNat_of_nonneg (le_of_lt m.prop),
            Int.toNat_of_nonneg (le_of_lt n.prop)] using
              congrArg (fun x : ℕ => (x : ℤ)) hk
        _ = ((⟨(k : ℤ), by exact_mod_cast hkpos⟩ : ℤ>0) *
            (⟨(k : ℤ), by exact_mod_cast hkpos⟩ : ℤ>0)).val := rfl
    rcases (imo2010_p3_assumed gz).2 hzsquare with h_id | ⟨c, hc⟩
    · refine ⟨0, ?_⟩
      intro n
      have h := congrFun h_id (e n)
      simpa [gz, e] using congrArg Subtype.val h
    · refine ⟨c.val.toNat, ?_⟩
      intro n
      have h := hc (e n)
      have hc_nonneg : 0 ≤ c.val := le_of_lt c.prop
      have hc_cast : (c.val.toNat : ℤ) = c.val := Int.toNat_of_nonneg hc_nonneg
      have h' := congrArg Subtype.val h
      change ((g (e.symm (e n))).val : ℤ) = (n.val : ℤ) + c.val at h'
      rw [e.symm_apply_apply] at h'
      rw [← hc_cast] at h'
      exact_mod_cast h'
  · rintro ⟨c, hc⟩ m n
    use (g m).val + n.val
    rw [hc m, hc n]
    simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, pow_two]
