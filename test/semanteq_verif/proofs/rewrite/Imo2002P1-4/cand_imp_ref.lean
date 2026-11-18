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
theorem problem_statement_assumed (n : ℕ) (hn : 0 < n) (coloring : ℕ × ℕ → Bool) :
  (∀ (p : ℕ × ℕ), p ∈ T_set n → (coloring p = true → ∀ (p' : ℕ × ℕ), p' ∈ T_set n → p'.1 ≤ p.1 → p'.2 ≤ p.2 → coloring p' = true)) →
  let blue_points_set := {p : ℕ × ℕ | p ∈ T_set n ∧ coloring p = false}
  let A := Nat.card {S : Finset (ℕ × ℕ) | (S : Set (ℕ × ℕ)) ⊆ blue_points_set ∧ S.card = n ∧ ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → p.1 ≠ q.1}
  let B := Nat.card {S : Finset (ℕ × ℕ) | (S : Set (ℕ × ℕ)) ⊆ blue_points_set ∧ S.card = n ∧ ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → p.2 ≠ q.2}
  A = B := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2002_p1 (n : ℕ) (_hn : 0 < n) (color : ℕ × ℕ → Color)
    (hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red) :
    ChoiceCount n color Prod.fst = ChoiceCount n color Prod.snd := by
  let coloring : ℕ × ℕ → Bool := fun p => match color p with
    | .red => true
    | .blue => false
  have hcoloring : ∀ (p : ℕ × ℕ), p ∈ T_set n →
      (coloring p = true → ∀ (p' : ℕ × ℕ), p' ∈ T_set n →
        p'.1 ≤ p.1 → p'.2 ≤ p.2 → coloring p' = true) := by
    intro p hp hp_red p' hp' hx hy
    have hp_color : color p = .red := by
      cases h : color p with
      | red => rfl
      | blue => simp only [coloring, h, Bool.false_eq_true] at hp_red
    have hp'_color := hcolor p'.1 p'.2 p.1 p.2 hx hy hp hp_color
    simp only [coloring, hp'_color]
  have hmain := problem_statement_assumed n _hn coloring hcoloring
  have count_bridge (coord : ℕ × ℕ → ℕ) :
      Nat.card {S : Finset (ℕ × ℕ) |
        (S : Set (ℕ × ℕ)) ⊆ {p : ℕ × ℕ | p ∈ T_set n ∧ coloring p = false} ∧
        S.card = n ∧ ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → coord p ≠ coord q} =
      ChoiceCount n color coord := by
    let counted := ((T n).powersetCard n).filter fun s ↦
      (∀ p ∈ s, color p = .blue) ∧
      ∀ p ∈ s, ∀ q ∈ s, coord p = coord q → p = q
    have pred_iff (S : Finset (ℕ × ℕ)) :
        ((S : Set (ℕ × ℕ)) ⊆ {p : ℕ × ℕ | p ∈ T_set n ∧ coloring p = false} ∧
          S.card = n ∧ ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → coord p ≠ coord q) ↔
        S ∈ counted := by
      simp only [counted, Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨hsub, hcard, hdistinct⟩
        refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
        · intro p hp
          have hpn := (hsub hp).1
          simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
          exact ⟨⟨lt_of_le_of_lt (Nat.le_add_right p.1 p.2) hpn,
            lt_of_le_of_lt (Nat.le_add_left p.2 p.1) hpn⟩, hpn⟩
        · intro p hp
          have hblue := (hsub hp).2
          cases h : color p with
          | red => simp only [coloring, h, Bool.true_eq_false] at hblue
          | blue => rfl
        · intro p hp q hq heq
          exact not_ne_iff.mp fun hpq => (hdistinct p q hp hq hpq) heq
      · rintro ⟨⟨hsub, hcard⟩, hblue, hdistinct⟩
        refine ⟨?_, hcard, ?_⟩
        · intro p hp
          have hpT := hsub hp
          have hpblue := hblue p hp
          constructor
          · have hpT' : (p.1 < n ∧ p.2 < n) ∧ p.1 + p.2 < n := by
              simpa only [T, Finset.mem_filter, Finset.mem_product,
                Finset.mem_range] using hpT
            exact hpT'.2
          · simp only [coloring, hpblue]
        · intro p q hp hq hpq heq
          exact hpq (hdistinct p hp q hq heq)
    change Nat.card {S : Finset (ℕ × ℕ) //
      (S : Set (ℕ × ℕ)) ⊆ {p : ℕ × ℕ | p ∈ T_set n ∧ coloring p = false} ∧
      S.card = n ∧ ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → coord p ≠ coord q} = _
    rw [Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) pred_iff)]
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    rfl
  dsimp only at hmain
  rw [← count_bridge Prod.fst, ← count_bridge Prod.snd]
  exact hmain
