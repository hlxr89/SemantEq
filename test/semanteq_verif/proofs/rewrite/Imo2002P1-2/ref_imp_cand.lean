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

-- Renamed from the candidate's `T` because that name conflicts with the
-- reference's definition above.
def TSet (n : ℕ) : Set (ℕ × ℕ) :=
  {p | p.1 + p.2 < n}

def ValidColoring (n : ℕ) (B : Set (ℕ × ℕ)) : Prop :=
  B ⊆ TSet n ∧
  ∀ p q : ℕ × ℕ, p ∈ B → q ∈ TSet n → p.1 ≤ q.1 → p.2 ≤ q.2 → q ∈ B

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
  let colorOf (S : Set (ℕ × ℕ)) (p : ℕ × ℕ) : Color :=
    if p ∈ S then .blue else .red
  have hcount (S : Set (ℕ × ℕ)) (hS : ValidColoring n S) :
      ChoiceCount n (colorOf S) Prod.fst = ChoiceCount n (colorOf S) Prod.snd := by
    apply imo2002_p1_assumed n hn (colorOf S)
    intro x' y' x y hx hy hxy hred
    have hnot : (x, y) ∉ S := by
      intro hmem
      have : colorOf S (x, y) = .blue := by
        simp only [colorOf, if_pos hmem]
      rw [this] at hred
      exact Color.noConfusion hred
    have hlower : (x', y') ∉ S := by
      intro hmem
      exact hnot (hS.2 (x', y') (x, y) hmem hxy hx hy)
    simp only [colorOf, if_neg hlower]
  have hex_iff (S : Set (ℕ × ℕ)) (hS : ValidColoring n S) :
      (∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ S) ∧
        (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.1 ≠ q.1)) ↔
      (∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ S) ∧
        (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.2 ≠ q.2)) := by
    have hpos_iff (coord : ℕ × ℕ → ℕ) :
        0 < ChoiceCount n (colorOf S) coord ↔
        ∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ S) ∧
          (∀ p q, p ∈ s → q ∈ s → p ≠ q → coord p ≠ coord q) := by
      rw [ChoiceCount, Finset.card_pos]
      constructor
      · intro h
        obtain ⟨s, hs⟩ := h
        simp only [Finset.mem_filter, Finset.mem_powersetCard] at hs
        refine ⟨s, hs.1.2, ?_, ?_⟩
        · intro p hp
          have := hs.2.1 p hp
          simp only [colorOf, ite_eq_left_iff, reduceCtorEq, imp_false,
            Classical.not_not] at this
          exact this
        · intro p q hp hq hpq heq
          exact hpq (hs.2.2 p hp q hq heq)
      · rintro ⟨s, hcard, hblue, hinj⟩
        refine ⟨s, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_powersetCard]
        refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
        · intro p hp
          have hpS := hblue p hp
          have hpT := hS.1 hpS
          simp only [TSet, Set.mem_setOf_eq] at hpT
          simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨Nat.lt_of_le_of_lt (Nat.le_add_right p.1 p.2) hpT,
            Nat.lt_of_le_of_lt (Nat.le_add_left p.2 p.1) hpT⟩, hpT⟩
        · intro p hp
          simp only [colorOf, if_pos (hblue p hp)]
        · intro p hp q hq heq
          by_contra hpq
          exact hinj p q hp hq hpq heq
    rw [← hpos_iff Prod.fst, ← hpos_iff Prod.snd, hcount S hS]
  apply Nat.card_congr
  let f : {S : Set (ℕ × ℕ) | ValidColoring n S ∧
      ∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ S) ∧
      (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.1 ≠ q.1)} →
      {S : Set (ℕ × ℕ) | ValidColoring n S ∧
      ∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ S) ∧
      (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.2 ≠ q.2)} :=
    fun S => ⟨S.1, S.2.1, (hex_iff S.1 S.2.1).mp S.2.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro S₁ S₂ h
    apply Subtype.ext
    exact congrArg (fun S => S.1) h
  · intro S
    refine ⟨⟨S.1, S.2.1, (hex_iff S.1 S.2.1).mpr S.2.2⟩, ?_⟩
    exact Subtype.ext rfl
