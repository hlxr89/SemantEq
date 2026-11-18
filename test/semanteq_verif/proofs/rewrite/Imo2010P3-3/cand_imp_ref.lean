import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

def posIntEquivPNat : ℤ>0 ≃ ℕ+ where
  toFun x := ⟨x.1.natAbs, Int.natAbs_pos.mpr (ne_of_gt x.2)⟩
  invFun n := ⟨n.1, Int.natCast_pos.mpr n.2⟩
  left_inv x := Subtype.ext (Int.natAbs_of_nonneg (le_of_lt x.2))
  right_inv n := rfl

theorem posIntEquivPNat_coe (x : ℤ>0) :
    ((posIntEquivPNat x).1 : ℤ) = x.1 :=
  Int.natAbs_of_nonneg (le_of_lt x.2)

theorem posIntEquivPNat_symm_coe (n : ℕ+) :
    (posIntEquivPNat.symm n).1 = (n.1 : ℤ) := rfl

theorem posIntEquivPNat_add (x y : ℤ>0) :
    posIntEquivPNat (x + y) = posIntEquivPNat x + posIntEquivPNat y := by
  apply Subtype.ext
  change (x.1 + y.1).natAbs = x.1.natAbs + y.1.natAbs
  apply Int.ofNat_inj.mp
  rw [Int.natCast_add, Int.natAbs_of_nonneg (le_of_lt x.2),
    Int.natAbs_of_nonneg (le_of_lt y.2),
    Int.natAbs_of_nonneg (le_of_lt (add_pos x.2 y.2))]

theorem posIntEquivPNat_mul (x y : ℤ>0) :
    posIntEquivPNat (x * y) = posIntEquivPNat x * posIntEquivPNat y := by
  apply Subtype.ext
  change (x.1 * y.1).natAbs = x.1.natAbs * y.1.natAbs
  apply Int.ofNat_inj.mp
  rw [Int.natCast_mul, Int.natAbs_of_nonneg (le_of_lt x.2),
    Int.natAbs_of_nonneg (le_of_lt y.2),
    Int.natAbs_of_nonneg (le_of_lt (mul_pos x.2 y.2))]

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ g : ℕ+ → ℕ+,
    (∀ m n : ℕ+, ∃ k : ℕ+, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  let e := posIntEquivPNat
  let gn : ℕ+ → ℕ+ := fun n => e (g (e.symm n))
  have hc := problem_statement_assumed gn
  constructor
  · intro hg
    have hchar : ∃ c : ℕ, ∀ n : ℕ+, gn n = n + c := by
      rcases hg with hid | ⟨c, hc'⟩
      · refine ⟨0, ?_⟩
        intro n
        change (e (g (e.symm n))).1 = n.1 + 0
        rw [hid]
        exact congrArg Subtype.val (e.apply_symm_apply n)
      · refine ⟨c.1.natAbs, ?_⟩
        intro n
        change (e (g (e.symm n))).1 = n.1 + (e c).1
        rw [hc']
        rw [posIntEquivPNat_add, e.apply_symm_apply]
        rfl
    have hsquares := hc.mpr hchar
    intro m n
    obtain ⟨k, hk⟩ := hsquares (e m) (e n)
    rw [isSquare_iff_exists_sq]
    refine ⟨e.symm k, ?_⟩
    apply e.injective
    rw [posIntEquivPNat_mul, posIntEquivPNat_add, posIntEquivPNat_add,
      pow_two, posIntEquivPNat_mul, e.apply_symm_apply]
    simpa only [gn, e, pow_two, Equiv.symm_apply_apply] using hk
  · intro hsquare
    have hnatsquare : ∀ m n : ℕ+, ∃ k : ℕ+, (gn m + n) * (gn n + m) = k^2 := by
      intro m n
      have hsk := hsquare (e.symm m) (e.symm n)
      rw [isSquare_iff_exists_sq] at hsk
      obtain ⟨k, hk⟩ := hsk
      refine ⟨e k, ?_⟩
      have heq := congrArg e hk
      rw [posIntEquivPNat_mul, posIntEquivPNat_add,
        posIntEquivPNat_add, pow_two, posIntEquivPNat_mul] at heq
      change (e (g (e.symm m)) + e (e.symm n)) *
        (e (g (e.symm n)) + e (e.symm m)) = e k * e k at heq
      rw [e.apply_symm_apply, e.apply_symm_apply] at heq
      rw [pow_two]
      exact heq
    obtain ⟨c, hc'⟩ := hc.mp hnatsquare
    change g = id ∨ ∃ c, ∀ x, g x = x + c
    rcases eq_or_ne c 0 with rfl | hc0
    · left
      funext x
      have h := hc' (e x)
      dsimp [gn] at h
      rw [e.symm_apply_apply] at h
      apply Subtype.ext
      have hz := congrArg (fun z : ℕ => (z : ℤ)) h
      change (((e (g x)).1 : ℕ) : ℤ) = (((e x).1 : ℕ) : ℤ) at hz
      rw [posIntEquivPNat_coe, posIntEquivPNat_coe] at hz
      exact hz
    · right
      have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
      let cz : ℤ>0 := ⟨c, Int.natCast_pos.mpr hcpos⟩
      refine ⟨cz, ?_⟩
      intro x
      have h := hc' (e x)
      dsimp [gn] at h
      rw [e.symm_apply_apply] at h
      apply Subtype.ext
      have hz := congrArg (fun z : ℕ => (z : ℤ)) h
      change (((e (g x)).1 : ℕ) : ℤ) = ((((e x).1 + c : ℕ)) : ℤ) at hz
      rw [Int.natCast_add, posIntEquivPNat_coe, posIntEquivPNat_coe] at hz
      exact hz
