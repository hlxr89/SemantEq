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

-- ===== assumed statement (antecedent) =====
theorem imo2002_p1_assumed (n : ℕ) (_hn : 0 < n) (color : ℕ × ℕ → Color)
    (hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red) :
    ChoiceCount n color Prod.fst = ChoiceCount n color Prod.snd := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : 0 < n) (coloring : ℕ × ℕ → Bool) :
  (∀ (p : ℕ × ℕ), p ∈ T_set n → (coloring p = true → ∀ (p' : ℕ × ℕ), p' ∈ T_set n → p'.1 ≤ p.1 → p'.2 ≤ p.2 → coloring p' = true)) →
  let blue_points_set := {p : ℕ × ℕ | p ∈ T_set n ∧ coloring p = false}
  let A := Nat.card {S : Finset (ℕ × ℕ) | (S : Set (ℕ × ℕ)) ⊆ blue_points_set ∧ S.card = n ∧ ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → p.1 ≠ q.1}
  let B := Nat.card {S : Finset (ℕ × ℕ) | (S : Set (ℕ × ℕ)) ⊆ blue_points_set ∧ S.card = n ∧ ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → p.2 ≠ q.2}
  A = B := by
  intro hmono
  let color : ℕ × ℕ → Color := fun p => if coloring p then .red else .blue
  have hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red := by
    intro x' y' x y hx hy hxy hred
    have htrue : coloring (x, y) = true := by
      simp only [color] at hred
      split at hred
      · assumption
      · contradiction
    have hp_mem : (x, y) ∈ T_set n := hxy
    have hp'_mem : (x', y') ∈ T_set n := by
      simp only [T_set, Set.mem_setOf_eq]
      omega
    have := hmono (x, y) hp_mem htrue (x', y') hp'_mem hx hy
    simp [color, this]
  have href := imo2002_p1_assumed n hn color hcolor
  let blue_points_set := {p : ℕ × ℕ | p ∈ T_set n ∧ coloring p = false}
  let C (coord : ℕ × ℕ → ℕ) :=
    {S : Finset (ℕ × ℕ) | (S : Set (ℕ × ℕ)) ⊆ blue_points_set ∧ S.card = n ∧
      ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → coord p ≠ coord q}
  have hcount (coord : ℕ × ℕ → ℕ) : Nat.card (C coord) = ChoiceCount n color coord := by
    let F := ((T n).powersetCard n).filter fun s ↦
      (∀ p ∈ s, color p = .blue) ∧
      ∀ p ∈ s, ∀ q ∈ s, coord p = coord q → p = q
    let e : C coord ≃ ↥F :=
      { toFun := fun S => ⟨S.1, by
          rcases S.2 with ⟨hsub, hcard, hdistinct⟩
          simp only [F, Finset.mem_filter, Finset.mem_powersetCard]
          refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
          · intro p hp
            have hbp := hsub hp
            simp only [blue_points_set, Set.mem_setOf_eq, T_set] at hbp
            simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            omega
          · intro p hp
            have hbp := hsub hp
            simp only [blue_points_set, Set.mem_setOf_eq] at hbp
            simp [color, hbp.2]
          · intro p hp q hq heq
            by_contra hpq
            exact (hdistinct p q hp hq hpq) heq⟩
        invFun := fun S => ⟨S.1, by
          have hS := S.2
          simp only [F, Finset.mem_filter] at hS
          rcases hS with ⟨hpow, hblue, hdistinct⟩
          rcases (Finset.mem_powersetCard.mp hpow) with ⟨hsubT, hcard⟩
          refine ⟨?_, hcard, ?_⟩
          · intro p hp
            have hpT := hsubT hp
            have hpblue := hblue p hp
            constructor
            · simp only [T, Finset.mem_filter, Finset.mem_product,
                Finset.mem_range] at hpT
              exact hpT.2
            · simp only [color] at hpblue
              split at hpblue
              · contradiction
              · simpa using ‹¬coloring p = true›
          · intro p q hp hq hpq heq
            exact hpq (hdistinct p hp q hq heq)⟩
        left_inv := fun S => by cases S; rfl
        right_inv := fun S => by cases S; rfl }
    calc
      Nat.card (C coord) = Nat.card ↥F := Nat.card_congr e
      _ = F.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ = ChoiceCount n color coord := rfl
  dsimp only
  change Nat.card (C Prod.fst) = Nat.card (C Prod.snd)
  rw [hcount, hcount, href]
