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
  let gz : PosInt → PosInt := fun z => pnatToPosInt (g (posIntToPNat z))
  constructor
  · intro hsquare
    have hgzsquare : ∀ m n, IsSquare ((gz m + n) * (gz n + m)) := by
      intro m n
      rcases hsquare (posIntToPNat m) (posIntToPNat n) with ⟨k, hk⟩
      rw [isSquare_iff_exists_sq]
      refine ⟨pnatToPosInt k, ?_⟩
      apply Subtype.ext
      have hk' := congrArg Subtype.val hk
      dsimp [gz, pnatToPosInt] at ⊢
      rw [← Int.toNat_of_nonneg (le_of_lt m.2),
        ← Int.toNat_of_nonneg (le_of_lt n.2)]
      norm_cast
    have hmem : gz ∈ SolutionSet := (imo2010_p3_assumed gz).2 hgzsquare
    rcases hmem with hident | ⟨c, hc⟩
    · refine ⟨0, ?_⟩
      intro n
      have h := congrFun hident (pnatToPosInt n)
      have h' := congrArg Subtype.val h
      have hZ : ((g n).1 : ℤ) = n.1 := by
        simpa [gz, pnatToPosInt] using h'
      change (g n).1 = n.1 + 0
      exact_mod_cast hZ
    · refine ⟨c.1.toNat, ?_⟩
      intro n
      have h := hc (pnatToPosInt n)
      have h' := congrArg Subtype.val h
      change (g n).1 = n.1 + c.1.toNat
      dsimp [gz, pnatToPosInt] at h'
      have hcval : (c.1.toNat : ℤ) = c.1 :=
        Int.toNat_of_nonneg (le_of_lt c.2)
      rw [← hcval] at h'
      exact_mod_cast h'
  · rintro ⟨c, hc⟩ m n
    let k : ℕ+ := ⟨m.1 + n.1 + c, by have := m.2; omega⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    change ((g m).1 + n.1) * ((g n).1 + m.1) = (m.1 + n.1 + c) ^ 2
    have hm : (g m).1 = m.1 + c := hc m
    have hn : (g n).1 = n.1 + c := hc n
    rw [hm, hn]
    ring
