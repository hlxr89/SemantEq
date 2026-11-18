import Mathlib

open Finset

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

/-- A hook is a figure made of 6 unit squares in a specific configuration.
The basic hook shape consists of 6 squares arranged in a particular pattern.
Any rotation or reflection of this shape is also considered a hook. -/
def is_hook : Set (ℤ × ℤ) → Prop :=
  fun s => ∃ t : Finset (ℤ × ℤ), IsHook t ∧ (t : Set (ℤ × ℤ)) = s

/-- A set of points represents a hook shape. -/
def HookShape : Type := Set (ℤ × ℤ)

/-- A rectangle of size m × n consists of points (i, j) where 0 ≤ i < m and 0 ≤ j < n. -/
def Rectangle (m n : ℕ) : Set (ℤ × ℤ) :=
  {p | ∃ (i j : ℤ), 0 ≤ i ∧ i < m ∧ 0 ≤ j ∧ j < n ∧ p = (i, j)}

/-- A rectangle can be tiled by hooks if it can be partitioned into hook shapes.
This allows for rotations and reflections of the hook. -/
def can_tile_with_hooks (m n : ℕ) : Prop :=
  if 0 < m ∧ 0 < n then Tileable (rect m n) else GoodRect m n

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (m n : ℕ) :
  can_tile_with_hooks m n ↔ 
    (m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 5 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5) ∧
    (m % 3 = 0 ∨ n % 3 = 0) ∧
    (m % 4 = 0 ∨ n % 4 = 0) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2004_p3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Tileable (rect m n) ↔ (m, n) ∈ answer := by
  change Tileable (rect m n) ↔ GoodRect m n
  rw [← show can_tile_with_hooks m n = Tileable (rect m n) by
    simp [can_tile_with_hooks, hm, hn]]
  rw [problem_statement_assumed m n]
  simp only [GoodRect, Nat.dvd_iff_mod_eq_zero]
  tauto
