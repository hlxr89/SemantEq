import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
def rect (m n : ℕ) : Finset (ℤ × ℤ) :=
  ((Finset.range m) ×ˢ (Finset.range n)).image fun p => ((p.1 : ℤ), (p.2 : ℤ))

def hookShapes : Finset (Finset (ℤ × ℤ)) :=
  { {(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 0)},
    {(0, 0), (0, 1), (0, 2), (1, 0), (1, 2), (2, 2)},
    {(0, 0), (0, 1), (0, 2), (1, 0), (2, 0), (2, 1)},
    {(0, 0), (0, 1), (1, 0), (2, 0), (2, 1), (2, 2)},
    {(0, 0), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)},
    {(0, 2), (1, 0), (1, 2), (2, 0), (2, 1), (2, 2)},
    {(0, 1), (0, 2), (1, 2), (2, 0), (2, 1), (2, 2)},
    {(0, 0), (0, 1), (0, 2), (1, 2), (2, 1), (2, 2)} }

def IsHook (s : Finset (ℤ × ℤ)) : Prop := ∃ σ ∈ hookShapes, ∃ t, s = σ.image (· + t)

def Tileable (R : Finset (ℤ × ℤ)) : Prop :=
  ∃ 𝒯 : Finset (Finset (ℤ × ℤ)), (∀ H ∈ 𝒯, IsHook H) ∧
    (∀ H₁ ∈ 𝒯, ∀ H₂ ∈ 𝒯, H₁ ≠ H₂ → Disjoint H₁ H₂) ∧ R = 𝒯.biUnion id

def GoodRect (m n : ℕ) : Prop :=
  m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 5 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5 ∧ (3 ∣ m ∨ 3 ∣ n) ∧ (4 ∣ m ∨ 4 ∣ n)

abbrev answer : Set (ℕ × ℕ) :=
  {p | GoodRect p.1 p.2}

def canonical_hook : Set (ℤ × ℤ) :=
  {(0, 0), (1, 0), (2, 0), (0, 1), (1, 1), (2, 1)}

def is_hook (s : Set (ℤ × ℤ)) : Prop :=
  ∃ (a b : ℤ), s = canonical_hook.image (fun (x, y) => (x + a, y + b))

def rect_points (m n : ℕ) : Set (ℤ × ℤ) :=
  {p : ℤ × ℤ | 0 ≤ p.1 ∧ p.1 < m ∧ 0 ≤ p.2 ∧ p.2 < n}

def can_tile_hooks (m n : ℕ) : Prop :=
  ∃ (tiles : Finset (Set (ℤ × ℤ))),
    (∀ t ∈ tiles, is_hook t) ∧
    (∀ t ∈ tiles, t ⊆ rect_points m n) ∧
    (⋃ t ∈ tiles, t) = rect_points m n

-- ===== assumed statement (antecedent) =====
theorem imo2004_p3_assumed (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Tileable (rect m n) ↔ (m, n) ∈ answer := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ (m n : ℕ),
    (m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 5 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5) ∧
    (3 ∣ m ∨ 3 ∣ n) ∧
    (4 ∣ m ∨ 4 ∣ n) ↔
    can_tile_hooks m n := by
  -- not proved: the candidate statement is false (its "hook" is a fixed 3 × 2 rectangle)
  sorry
