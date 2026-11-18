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
theorem imo2010_p3_assumed (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ g : ℕ+ → ℕ+,
    (∀ m n : ℕ+, ∃ k : ℕ+, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  intro g
  let e := posIntEquivPNat
  let gz : ℤ>0 → ℤ>0 := fun x => e.symm (g (e x))
  have hr := imo2010_p3_assumed gz
  constructor
  · intro hsquare
    have hzsquare : ∀ m n, IsSquare ((gz m + n) * (gz n + m)) := by
      intro m n
      obtain ⟨k, hk⟩ := hsquare (e m) (e n)
      rw [isSquare_iff_exists_sq]
      refine ⟨e.symm k, ?_⟩
      apply e.injective
      rw [posIntEquivPNat_mul, posIntEquivPNat_add, posIntEquivPNat_add,
        pow_two, posIntEquivPNat_mul, e.apply_symm_apply]
      simpa only [gz, e, pow_two, Equiv.apply_symm_apply] using hk
    have hzchar := hr.mpr hzsquare
    rcases hzchar with hid | ⟨c, hc⟩
    · refine ⟨0, ?_⟩
      intro n
      have h := congrArg e (congrFun hid (e.symm n))
      simpa only [gz, e, Equiv.apply_symm_apply, Equiv.symm_apply_apply,
        Nat.add_zero] using congrArg Subtype.val h
    · refine ⟨c.1.natAbs, ?_⟩
      intro n
      have h := congrArg e (hc (e.symm n))
      change (g n).1 = n.1 + (e c).1
      rw [posIntEquivPNat_add, e.apply_symm_apply] at h
      exact congrArg Subtype.val h
  · rintro ⟨c, hc⟩
    have hzchar : gz ∈ SolutionSet := by
      change gz = id ∨ ∃ c, ∀ x, gz x = x + c
      rcases eq_or_ne c 0 with rfl | hc0
      · left
        funext x
        apply e.injective
        have h := hc (e x)
        change (g (e x)).1 = (e x).1 + 0 at h
        apply Subtype.ext
        simpa only [gz, e, Equiv.symm_apply_apply, Nat.add_zero] using h
      · right
        have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
        let cz : ℤ>0 := ⟨c, Int.natCast_pos.mpr hcpos⟩
        refine ⟨cz, ?_⟩
        intro x
        apply e.injective
        have h := hc (e x)
        change (g (e x)).1 = (e x).1 + c at h
        have hp : g (e x) = e x + e cz := Subtype.ext h
        rw [posIntEquivPNat_add]
        simpa only [gz, e, Equiv.symm_apply_apply, cz] using hp
    have hzsquare := hr.mp hzchar
    intro m n
    have hsk := hzsquare (e.symm m) (e.symm n)
    rw [isSquare_iff_exists_sq] at hsk
    obtain ⟨k, hk⟩ := hsk
    refine ⟨e k, ?_⟩
    have heq := congrArg e hk
    rw [posIntEquivPNat_mul, posIntEquivPNat_add,
      posIntEquivPNat_add, pow_two, posIntEquivPNat_mul] at heq
    change (g m + e (e.symm n)) * (g n + e (e.symm m)) = e k * e k at heq
    rw [e.apply_symm_apply, e.apply_symm_apply] at heq
    simpa only [pow_two] using heq
