import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

def posIntToPNat (z : PosInt) : ℕ+ := ⟨z.1.toNat, by omega⟩

def pnatToPosInt (n : ℕ+) : PosInt := ⟨n.1, by exact_mod_cast n.2⟩

@[simp] theorem posIntToPNat_pnatToPosInt (n : ℕ+) :
    posIntToPNat (pnatToPosInt n) = n := by
  apply Subtype.ext
  simp [posIntToPNat, pnatToPosInt]

@[simp] theorem pnatToPosInt_posIntToPNat (z : PosInt) :
    pnatToPosInt (posIntToPNat z) = z := by
  apply Subtype.ext
  exact Int.toNat_of_nonneg (le_of_lt z.2)

@[simp] theorem posInt_cast_toNat (z : PosInt) : (z.1.toNat : ℤ) = z.1 :=
  Int.toNat_of_nonneg (le_of_lt z.2)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ g : ℕ+ → ℕ+,
    (∀ m n : ℕ+, ∃ k : ℕ+, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  let gn : ℕ+ → ℕ+ := fun n => posIntToPNat (g (pnatToPosInt n))
  constructor
  · intro hmem
    have hsol : ∃ c : ℕ, ∀ n : ℕ+, gn n = n + c := by
      rcases hmem with hident | ⟨c, hc⟩
      · refine ⟨0, ?_⟩
        intro n
        have h := congrFun hident (pnatToPosInt n)
        change (gn n).1 = n.1 + 0
        dsimp [gn, posIntToPNat]
        rw [h]
        simp [pnatToPosInt]
      · refine ⟨c.1.toNat, ?_⟩
        intro n
        have h := hc (pnatToPosInt n)
        change (gn n).1 = n.1 + c.1.toNat
        dsimp [gn, posIntToPNat]
        rw [h]
        change (n.1 + c.1).toNat = n.1 + c.1.toNat
        have hn := n.2
        have hcpos := c.2
        omega
    have hnsquare := (problem_statement_assumed gn).2 hsol
    intro m n
    rcases hnsquare (posIntToPNat m) (posIntToPNat n) with ⟨k, hk⟩
    rw [isSquare_iff_exists_sq]
    refine ⟨pnatToPosInt k, ?_⟩
    apply Subtype.ext
    have hkNat :
        ((posIntToPNat (g m)).1 + (posIntToPNat n).1) *
          ((posIntToPNat (g n)).1 + (posIntToPNat m).1) = k.1 ^ 2 := by
      have hk' := congrArg Subtype.val hk
      simpa [gn] using hk'
    change ((g m).1 + n.1) * ((g n).1 + m.1) = (k.1 : ℤ) ^ 2
    rw [← posInt_cast_toNat (g m), ← posInt_cast_toNat n,
      ← posInt_cast_toNat (g n), ← posInt_cast_toNat m]
    norm_cast
  · intro hsquare
    have hnsquare : ∀ m n : ℕ+, ∃ k : ℕ+, (gn m + n) * (gn n + m) = k^2 := by
      intro m n
      have h := hsquare (pnatToPosInt m) (pnatToPosInt n)
      rw [isSquare_iff_exists_sq] at h
      rcases h with ⟨k, hk⟩
      refine ⟨posIntToPNat k, ?_⟩
      apply Subtype.ext
      have hk' := congrArg Subtype.val hk
      change ((g (pnatToPosInt m)).1.toNat + n.1) *
        ((g (pnatToPosInt n)).1.toNat + m.1) = k.1.toNat ^ 2
      change ((g (pnatToPosInt m)).1 + (pnatToPosInt n).1) *
        ((g (pnatToPosInt n)).1 + (pnatToPosInt m).1) = k.1 ^ 2 at hk'
      rw [← posInt_cast_toNat (g (pnatToPosInt m)),
        ← posInt_cast_toNat (pnatToPosInt n),
        ← posInt_cast_toNat (g (pnatToPosInt n)),
        ← posInt_cast_toNat (pnatToPosInt m), ← posInt_cast_toNat k] at hk'
      norm_cast at hk'
    rcases (problem_statement_assumed gn).1 hnsquare with ⟨c, hc⟩
    rcases eq_or_ne c 0 with rfl | hc0
    · left
      funext z
      apply Subtype.ext
      change (g z).1 = z.1
      have h := hc (posIntToPNat z)
      have h' : ((gn (posIntToPNat z)).1 : ℤ) =
          ((posIntToPNat z).1 + 0 : ℕ) := by exact_mod_cast h
      dsimp [gn, posIntToPNat] at h'
      change (((g (pnatToPosInt (posIntToPNat z))).1.toNat : ℕ) : ℤ) =
        ((z.1.toNat : ℕ) : ℤ) at h'
      rw [pnatToPosInt_posIntToPNat, posInt_cast_toNat (g z),
        posInt_cast_toNat z] at h'
      omega
    · right
      let cz : PosInt := ⟨c, by exact_mod_cast Nat.pos_of_ne_zero hc0⟩
      refine ⟨cz, ?_⟩
      intro z
      apply Subtype.ext
      change (g z).1 = z.1 + c
      have h := hc (posIntToPNat z)
      have h' : ((gn (posIntToPNat z)).1 : ℤ) =
          ((posIntToPNat z).1 + c : ℕ) := by exact_mod_cast h
      dsimp [gn, posIntToPNat] at h'
      change (((g (pnatToPosInt (posIntToPNat z))).1.toNat : ℕ) : ℤ) =
        ((z.1.toNat : ℕ) : ℤ) + c at h'
      rw [pnatToPosInt_posIntToPNat, posInt_cast_toNat (g z),
        posInt_cast_toNat z] at h'
      exact h'
