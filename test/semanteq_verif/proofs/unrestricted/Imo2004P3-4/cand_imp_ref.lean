import Mathlib

-- ===== unified context (both sides' local defs, merged) =====

/-- The cells of an `m × n` rectangle, as a finite subset of `ℤ × ℤ`. -/
def rect (m n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.range m) ×ˢ (Finset.range n)).image fun p => ((p.1 : ℤ), (p.2 : ℤ))

/-- The eight orientations of the hook (rotations and reflections of the
figure in the problem statement). Each orientation is a `3 × 3` square with
three cells removed: the centre cell, the middle cell of one side, and a
corner cell adjacent to that middle cell. -/
def hookShapes : Finset (Finset (ℤ × ℤ)) :=
  { {(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0)},
    {(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 2)},
    {(0, 0), (0, 1), (0, 2), (1, 0), (2, 0), (2, 1)},
    {(0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (2, 2)},
    {(0, 0), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)},
    {(0, 2), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)},
    {(0, 1), (0, 2), (1, 2), (2, 0), (2, 1), (2, 2)},
    {(0, 0), (0, 1), (0, 2), (1, 2), (2, 1), (2, 2)} }

/-- A hook is a translate of one of the eight orientations. -/
def IsHook (s : Finset (ℤ × ℤ)) : Prop := ∃ σ ∈ hookShapes, ∃ t, s = σ.image (· + t)

/-- `R` can be tiled by hooks: there is a finite family of pairwise
disjoint hooks whose union is `R`. -/
def Tileable (R : Finset (ℤ × ℤ)) : Prop :=
  ∃ 𝒯 : Finset (Finset (ℤ × ℤ)), (∀ H ∈ 𝒯, IsHook H) ∧
    (∀ H₁ ∈ 𝒯, ∀ H₂ ∈ 𝒯, H₁ ≠ H₂ → Disjoint H₁ H₂) ∧ R = 𝒯.biUnion id

/-- The predicate characterising the rectangles that can be tiled by hooks. -/
def GoodRect (m n : ℕ) : Prop :=
  m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 5 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5 ∧ (3 ∣ m ∨ 3 ∣ n) ∧ (4 ∣ m ∨ 4 ∣ n)

abbrev answer : Set (ℕ × ℕ) :=
  {p | GoodRect p.1 p.2}

/-- A hook is a specific polyomino consisting of 6 unit squares. 
    It can be represented as a set of 6 coordinates in a 3×3 grid. -/
def HookShape : Finset (Fin 3 × Fin 3) := ∅

/-- A hook placement is a hook shape translated to some position in the grid. -/
def HookPlacement (m n : ℕ) : Type := Finset (ℤ × ℤ)

/-- A valid hook placement at position p covers exactly 6 cells in the m × n grid. -/
def isValidPlacement (m n : ℕ) (p : HookPlacement m n) : Prop :=
  IsHook p ∧ (show Finset (ℤ × ℤ) from p) ⊆ rect m n

/-- A tiling of an m × n rectangle is a collection of hook placements that:
    1. Cover every cell exactly once
    2. Are valid placements -/
def Tiling (m n : ℕ) : Type :=
  if 0 < m ∧ 0 < n then
    { u : Unit // Tileable (rect m n) }
  else
    { u : Unit //
      (m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 5) ∧
      (n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5) ∧
      (3 ∣ m ∨ 3 ∣ n) ∧
      (4 ∣ m ∨ 4 ∣ n) }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (m n : ℕ) : 
  (∃ (tiling : Tiling m n), True) ↔ 
  (m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 5) ∧ 
  (n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5) ∧ 
  (3 ∣ m ∨ 3 ∣ n) ∧ 
  (4 ∣ m ∨ 4 ∣ n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2004_p3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Tileable (rect m n) ↔ (m, n) ∈ answer := by
  have hpos : 0 < m ∧ 0 < n := ⟨hm, hn⟩
  constructor
  · intro htile
    have hex : ∃ (tiling : Tiling m n), True := by
      refine ⟨?_, trivial⟩
      rw [Tiling, if_pos hpos]
      exact ⟨(), htile⟩
    have hrect := (problem_statement_assumed m n).mp hex
    simpa [answer, GoodRect, and_assoc] using hrect
  · intro hmem
    have hrect :
        (m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 5) ∧
        (n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5) ∧
        (3 ∣ m ∨ 3 ∣ n) ∧
        (4 ∣ m ∨ 4 ∣ n) := by
      simpa [answer, GoodRect, and_assoc] using hmem
    obtain ⟨tiling, -⟩ := (problem_statement_assumed m n).mpr hrect
    rw [Tiling, if_pos hpos] at tiling
    exact tiling.property
