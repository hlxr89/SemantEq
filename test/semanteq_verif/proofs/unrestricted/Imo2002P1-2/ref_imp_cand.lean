import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
inductive Color : Type where
| red : Color
| blue : Color
deriving DecidableEq

instance : Fintype Color where
  elems := ⟨↑[Color.red, Color.blue], by decide⟩
  complete := fun x => by cases x <;> decide

/-- The points (x, y) with nonnegative integer coordinates and x + y < n. -/
def T (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter fun p ↦ p.1 + p.2 < n

/-- The sets of n blue points in T whose coordinates are distinct in
the dimension selected by `coord`. -/
def ChoiceCount (n : ℕ) (color : ℕ × ℕ → Color) (coord : ℕ × ℕ → ℕ) : ℕ :=
  (((T n).powersetCard n).filter fun s ↦
    (∀ p ∈ s, color p = .blue) ∧
    ∀ p ∈ s, ∀ q ∈ s, coord p = coord q → p = q).card

-- The candidate's set-valued `T`, renamed to avoid the collision above.
def T_set (n : ℕ) : Set (ℕ × ℕ) :=
  {p | p.1 + p.2 < n}

def ValidColoring (n : ℕ) (B : Set (ℕ × ℕ)) : Prop :=
  B ⊆ T_set n ∧
  ∀ p q : ℕ × ℕ, p ∈ B → q ∈ T_set n → p.1 ≤ q.1 → p.2 ≤ q.2 → q ∈ B

noncomputable def A (n : ℕ) : ℕ :=
  Nat.card {B : Set (ℕ × ℕ) | ValidColoring n B ∧ 
    ∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ B) ∧ 
    (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.1 ≠ q.1)}

noncomputable def B (n : ℕ) : ℕ :=
  Nat.card {B : Set (ℕ × ℕ) | ValidColoring n B ∧ 
    ∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ B) ∧ 
    (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.2 ≠ q.2)}

-- ===== assumed statement (antecedent) =====
theorem imo2002_p1_assumed (n : ℕ) (_hn : 0 < n) (color : ℕ × ℕ → Color)
    (hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red) :
    ChoiceCount n color Prod.fst = ChoiceCount n color Prod.snd := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : n > 0) : A n = B n := by
  classical
  let e : (ℕ × ℕ) ≃ (ℕ × ℕ) := Equiv.prodComm ℕ ℕ
  let swapSet (C : Set (ℕ × ℕ)) : Set (ℕ × ℕ) := e ⁻¹' C
  have valid_swap (C : Set (ℕ × ℕ)) (hC : ValidColoring n C) :
      ValidColoring n (swapSet C) := by
    constructor
    · intro p hp
      have := hC.1 hp
      change p.1 + p.2 < n
      change p.2 + p.1 < n at this
      omega
    · intro p q hp hq hpq1 hpq2
      exact hC.2 (e p) (e q) hp (by
        change q.2 + q.1 < n
        change q.1 + q.2 < n at hq
        omega) hpq2 hpq1
  have witness_swap (C : Set (ℕ × ℕ))
      (hs : ∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ C) ∧
        (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.1 ≠ q.1)) :
      ∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ swapSet C) ∧
        (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.2 ≠ q.2) := by
    rcases hs with ⟨s, hcard, hmem, hdistinct⟩
    refine ⟨s.map e.toEmbedding, ?_, ?_, ?_⟩
    · simpa using hcard
    · intro p hp
      rcases Finset.mem_map.1 hp with ⟨q, hq, rfl⟩
      exact hmem q hq
    · intro p q hp hq hpq
      rcases Finset.mem_map.1 hp with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.1 hq with ⟨b, hb, rfl⟩
      exact hdistinct a b ha hb (by
        intro hab
        apply hpq
        simpa [hab])
  apply Nat.card_congr
  let f : {C : Set (ℕ × ℕ) | ValidColoring n C ∧
      ∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ C) ∧
      (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.1 ≠ q.1)} →
      {C : Set (ℕ × ℕ) | ValidColoring n C ∧
      ∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ C) ∧
      (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.2 ≠ q.2)} := fun C ↦
    ⟨swapSet C, valid_swap C C.property.1, witness_swap C C.property.2⟩
  refine ⟨f, ?_, ?_, ?_⟩
  · intro C
    refine ⟨swapSet C, valid_swap C C.property.1, ?_⟩
    rcases C.property.2 with ⟨s, hcard, hmem, hdistinct⟩
    refine ⟨s.map e.toEmbedding, by simpa using hcard, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_map.1 hp with ⟨q, hq, rfl⟩
      exact hmem q hq
    · intro p q hp hq hpq
      rcases Finset.mem_map.1 hp with ⟨a, ha, rfl⟩
      rcases Finset.mem_map.1 hq with ⟨b, hb, rfl⟩
      exact hdistinct a b ha hb (by
        intro hab
        apply hpq
        simpa [hab])
  · intro C
    apply Subtype.ext
    ext p
    rfl
  · intro C
    apply Subtype.ext
    ext p
    rfl
