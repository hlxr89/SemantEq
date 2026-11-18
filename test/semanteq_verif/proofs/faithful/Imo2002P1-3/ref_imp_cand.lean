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

def T_set (n : ℕ) : Set (ℕ × ℕ) := {p : ℕ × ℕ | p.1 + p.2 < n}

def satisfies_condition (n : ℕ) (coloring : ℕ × ℕ → Bool) : Prop :=
  ∀ (p : ℕ × ℕ), p ∈ T_set n → coloring p = true → 
    ∀ (q : ℕ × ℕ), q ∈ T_set n → q.1 ≤ p.1 → q.2 ≤ p.2 → coloring q = true

def blue_points (n : ℕ) (coloring : ℕ × ℕ → Bool) : Set (ℕ × ℕ) :=
  {p : ℕ × ℕ | p ∈ T_set n ∧ coloring p = false}

def A_subsets (n : ℕ) (coloring : ℕ × ℕ → Bool) : Set (Finset (ℕ × ℕ)) :=
  {s | s.card = n ∧ 
    (∀ p ∈ s, p ∈ blue_points n coloring) ∧
    (∀ p ∈ s, ∀ q ∈ s, p ≠ q → p.1 ≠ q.1)}

def B_subsets (n : ℕ) (coloring : ℕ × ℕ → Bool) : Set (Finset (ℕ × ℕ)) :=
  {s | s.card = n ∧ 
    (∀ p ∈ s, p ∈ blue_points n coloring) ∧
    (∀ p ∈ s, ∀ q ∈ s, p ≠ q → p.2 ≠ q.2)}

noncomputable def count_A (n : ℕ) (coloring : ℕ × ℕ → Bool) : ℕ :=
  Set.ncard (A_subsets n coloring)

noncomputable def count_B (n : ℕ) (coloring : ℕ × ℕ → Bool) : ℕ :=
  Set.ncard (B_subsets n coloring)

-- ===== assumed statement (antecedent) =====
theorem imo2002_p1_assumed (n : ℕ) (_hn : 0 < n) (color : ℕ × ℕ → Color)
    (hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red) :
    ChoiceCount n color Prod.fst = ChoiceCount n color Prod.snd := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : 0 < n) (coloring : ℕ × ℕ → Bool) 
    (h : satisfies_condition n coloring) :
  count_A n coloring = count_B n coloring := by
  let color : ℕ × ℕ → Color := fun p => if coloring p then .red else .blue
  have hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red := by
    intro x' y' x y hx hy hp hred
    have hp' : (x, y) ∈ T_set n := hp
    have hq' : (x', y') ∈ T_set n := by
      change x' + y' < n
      omega
    have hp_red : coloring (x, y) = true := by
      simpa [color] using hred
    have := h (x, y) hp' hp_red (x', y') hq' hx hy
    simp [color, this]
  have hA : count_A n coloring = ChoiceCount n color Prod.fst := by
    rw [count_A, ChoiceCount]
    rw [← Set.ncard_coe_finset]
    apply congrArg Set.ncard
    ext s
    simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_powersetCard,
      A_subsets, blue_points, T_set, Finset.mem_coe]
    constructor
    · rintro ⟨hcard, hblue, hdistinct⟩
      refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
      · intro p hp
        have ht := (hblue p hp).1
        simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        constructor
        · constructor <;> omega
        · exact ht
      · intro p hp
        simpa [color] using (hblue p hp).2
      · intro p hp q hq heq
        by_contra hpq
        exact (hdistinct p hp q hq hpq) heq
    · rintro ⟨⟨hsub, hcard⟩, hblue, hdistinct⟩
      refine ⟨hcard, ?_, ?_⟩
      · intro p hp
        have ht := hsub hp
        refine ⟨?_, ?_⟩
        · have ht' : (p.1 < n ∧ p.2 < n) ∧ p.1 + p.2 < n := by
            simpa [T] using ht
          exact ht'.2
        · have := hblue p hp
          simpa [color] using this
      · intro p hp q hq hpq heq
        exact hpq (hdistinct p hp q hq heq)
  have hB : count_B n coloring = ChoiceCount n color Prod.snd := by
    rw [count_B, ChoiceCount]
    rw [← Set.ncard_coe_finset]
    apply congrArg Set.ncard
    ext s
    simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_powersetCard,
      B_subsets, blue_points, T_set, Finset.mem_coe]
    constructor
    · rintro ⟨hcard, hblue, hdistinct⟩
      refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
      · intro p hp
        have ht := (hblue p hp).1
        simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        constructor
        · constructor <;> omega
        · exact ht
      · intro p hp
        simpa [color] using (hblue p hp).2
      · intro p hp q hq heq
        by_contra hpq
        exact (hdistinct p hp q hq hpq) heq
    · rintro ⟨⟨hsub, hcard⟩, hblue, hdistinct⟩
      refine ⟨hcard, ?_, ?_⟩
      · intro p hp
        have ht := hsub hp
        refine ⟨?_, ?_⟩
        · have ht' : (p.1 < n ∧ p.2 < n) ∧ p.1 + p.2 < n := by
            simpa [T] using ht
          exact ht'.2
        · have := hblue p hp
          simpa [color] using this
      · intro p hp q hq hpq heq
        exact hpq (hdistinct p hp q hq heq)
  rw [hA, hB]
  exact imo2002_p1_assumed n hn color hcolor
