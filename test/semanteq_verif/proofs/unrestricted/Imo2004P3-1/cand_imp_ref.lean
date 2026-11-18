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
theorem problem_statement_assumed :
  ∀ (m n : ℕ),
    (m ≠ 1 ∧ m ≠ 2 ∧ m ≠ 5 ∧ n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 5) ∧
    (3 ∣ m ∨ 3 ∣ n) ∧
    (4 ∣ m ∨ 4 ∣ n) ↔
    can_tile_hooks m n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2004_p3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    Tileable (rect m n) ↔ (m, n) ∈ answer := by
  exfalso
  have htile : can_tile_hooks 3 2 := by
    refine ⟨{canonical_hook}, ?_, ?_, ?_⟩
    · intro t ht
      simp only [Finset.mem_singleton] at ht
      subst t
      refine ⟨0, 0, ?_⟩
      ext p
      simp
    · intro t ht
      simp only [Finset.mem_singleton] at ht
      subst t
      intro p hp
      simp only [canonical_hook, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
        norm_num [rect_points]
    · simp only [Finset.set_biUnion_singleton]
      ext p
      rcases p with ⟨x, y⟩
      simp only [canonical_hook, Set.mem_insert_iff, Set.mem_singleton_iff, rect_points,
        Set.mem_setOf_eq, Prod.fst, Prod.snd]
      constructor
      · intro h
        rcases h with h | h | h | h | h | h <;> simp_all
      · intro h
        rcases h with ⟨hx0, hx3, hy0, hy2⟩
        interval_cases x <;> interval_cases y <;> simp_all
  have hbad := (problem_statement_assumed 3 2).mpr htile
  exact hbad.1.2.2.2.2.1 rfl
