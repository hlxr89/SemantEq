import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
inductive Color : Type where
| red : Color
| blue : Color
deriving DecidableEq

instance : Fintype Color where
  elems := ⟨↑[Color.red, Color.blue], by decide⟩
  complete := fun x => by cases x <;> decide

def T (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range n ×ˢ Finset.range n).filter fun p ↦ p.1 + p.2 < n

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
  let color : ℕ × ℕ → Color := fun p ↦ if coloring p then .red else .blue
  have hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red := by
    intro x' y' x y hx hy hxy hp
    have hp' : coloring (x, y) = true := by
      cases hc : coloring (x, y) with
      | false =>
          simp only [color, hc, Bool.false_eq_true, ↓reduceIte] at hp
          cases hp
      | true => rfl
    have hq_mem : (x', y') ∈ T_set n := by
      exact lt_of_le_of_lt (Nat.add_le_add hx hy) hxy
    have hq := h (x, y) hxy hp' (x', y') hq_mem hx hy
    simp only [color, hq, ↓reduceIte]
  have hAset : A_subsets n coloring =
      ↑(((T n).powersetCard n).filter fun s ↦
        (∀ p ∈ s, color p = .blue) ∧
        ∀ p ∈ s, ∀ q ∈ s, Prod.fst p = Prod.fst q → p = q) := by
    ext s
    simp only [A_subsets, blue_points, T_set, Set.mem_setOf_eq, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_powersetCard, color]
    constructor
    · rintro ⟨hcard, hblue, hdistinct⟩
      refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
      · intro p hp
        obtain ⟨hpT, _⟩ := hblue p hp
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, hpT⟩
        · exact lt_of_le_of_lt (Nat.le_add_right _ _) hpT
        · exact lt_of_le_of_lt (Nat.le_add_left _ _) hpT
      · intro p hp
        obtain ⟨_, hpblue⟩ := hblue p hp
        simp only [hpblue, Bool.false_eq_true, ↓reduceIte]
      · intro p hp q hq heq
        by_contra hpq
        exact (hdistinct p hp q hq hpq) heq
    · rintro ⟨⟨hsub, hcard⟩, hblue, hdistinct⟩
      refine ⟨hcard, ?_, ?_⟩
      · intro p hp
        have hpT := hsub hp
        have hpblue := hblue p hp
        refine ⟨(Finset.mem_filter.mp hpT).2, ?_⟩
        cases hc : coloring p with
        | false => rfl
        | true =>
            simp only [hc, ↓reduceIte] at hpblue
            cases hpblue
      · intro p hp q hq hpq heq
        exact hpq (hdistinct p hp q hq heq)
  have hBset : B_subsets n coloring =
      ↑(((T n).powersetCard n).filter fun s ↦
        (∀ p ∈ s, color p = .blue) ∧
        ∀ p ∈ s, ∀ q ∈ s, Prod.snd p = Prod.snd q → p = q) := by
    ext s
    simp only [B_subsets, blue_points, T_set, Set.mem_setOf_eq, Finset.mem_coe,
      Finset.mem_filter, Finset.mem_powersetCard, color]
    constructor
    · rintro ⟨hcard, hblue, hdistinct⟩
      refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
      · intro p hp
        obtain ⟨hpT, _⟩ := hblue p hp
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_, Finset.mem_range.mpr ?_⟩, hpT⟩
        · exact lt_of_le_of_lt (Nat.le_add_right _ _) hpT
        · exact lt_of_le_of_lt (Nat.le_add_left _ _) hpT
      · intro p hp
        obtain ⟨_, hpblue⟩ := hblue p hp
        simp only [hpblue, Bool.false_eq_true, ↓reduceIte]
      · intro p hp q hq heq
        by_contra hpq
        exact (hdistinct p hp q hq hpq) heq
    · rintro ⟨⟨hsub, hcard⟩, hblue, hdistinct⟩
      refine ⟨hcard, ?_, ?_⟩
      · intro p hp
        have hpT := hsub hp
        have hpblue := hblue p hp
        refine ⟨(Finset.mem_filter.mp hpT).2, ?_⟩
        cases hc : coloring p with
        | false => rfl
        | true =>
            simp only [hc, ↓reduceIte] at hpblue
            cases hpblue
      · intro p hp q hq hpq heq
        exact hpq (hdistinct p hp q hq heq)
  rw [count_A, count_B, hAset, hBset]
  rw [Set.ncard_coe_finset, Set.ncard_coe_finset]
  exact imo2002_p1_assumed n hn color hcolor
