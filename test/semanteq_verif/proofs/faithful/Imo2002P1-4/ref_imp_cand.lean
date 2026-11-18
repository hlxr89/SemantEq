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
  classical
  intro hcoloring
  let color : ℕ × ℕ → Color := fun p => if coloring p then .red else .blue
  have hred : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red := by
    intro x' y' x y hx hy hxy hr
    have hc : coloring (x, y) = true := by
      simpa [color] using hr
    have hc' := hcoloring (x, y) (by simpa [T_set]) hc (x', y')
      (by simp [T_set]; omega) hx hy
    simpa [color] using hc'
  have href := imo2002_p1_assumed n hn color hred
  let blue_points_set := {p : ℕ × ℕ | p ∈ T_set n ∧ coloring p = false}
  let PA := {S : Finset (ℕ × ℕ) | (S : Set (ℕ × ℕ)) ⊆ blue_points_set ∧ S.card = n ∧ ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → p.1 ≠ q.1}
  let PB := {S : Finset (ℕ × ℕ) | (S : Set (ℕ × ℕ)) ⊆ blue_points_set ∧ S.card = n ∧ ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → p.2 ≠ q.2}
  let FA := ((T n).powersetCard n).filter fun s ↦
    (∀ p ∈ s, color p = .blue) ∧
    ∀ p ∈ s, ∀ q ∈ s, Prod.fst p = Prod.fst q → p = q
  let FB := ((T n).powersetCard n).filter fun s ↦
    (∀ p ∈ s, color p = .blue) ∧
    ∀ p ∈ s, ∀ q ∈ s, Prod.snd p = Prod.snd q → p = q
  have bridgeA : Nat.card PA = FA.card := by
    let e : PA ≃ ↥FA :=
      { toFun := fun ⟨S, hS⟩ => ⟨S, by
          rcases hS with ⟨hsub, hcard, huniq⟩
          simp only [FA, Finset.mem_filter, Finset.mem_powersetCard]
          refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
          · intro p hp
            have hsum := (hsub hp).1
            change p.1 + p.2 < n at hsum
            simp only [T, Finset.mem_filter, Finset.mem_product,
              Finset.mem_range, Prod.fst, Prod.snd]
            exact ⟨⟨by omega, by omega⟩, hsum⟩
          · intro p hp
            have := (hsub hp).2
            simpa [color] using this
          · intro p hp q hq heq
            by_contra hne
            exact (huniq p q hp hq hne) heq⟩
        invFun := fun ⟨S, hS⟩ => ⟨S, by
          simp only [FA, Finset.mem_filter, Finset.mem_powersetCard] at hS
          rcases hS with ⟨⟨hsub, hcard⟩, hblue, huniq⟩
          refine ⟨?_, hcard, ?_⟩
          · intro p hp
            refine ⟨?_, ?_⟩
            · have ht := hsub hp
              simp only [T, Finset.mem_filter, Finset.mem_product,
                Finset.mem_range, Prod.fst, Prod.snd] at ht
              exact ht.2
            · simpa [color] using hblue p hp
          · intro p q hp hq hpq heq
            exact hpq (huniq p hp q hq heq)⟩
        left_inv := by intro x; cases x; rfl
        right_inv := by intro x; cases x; rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  have bridgeB : Nat.card PB = FB.card := by
    let e : PB ≃ ↥FB :=
      { toFun := fun ⟨S, hS⟩ => ⟨S, by
          rcases hS with ⟨hsub, hcard, huniq⟩
          simp only [FB, Finset.mem_filter, Finset.mem_powersetCard]
          refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
          · intro p hp
            have hsum := (hsub hp).1
            change p.1 + p.2 < n at hsum
            simp only [T, Finset.mem_filter, Finset.mem_product,
              Finset.mem_range, Prod.fst, Prod.snd]
            exact ⟨⟨by omega, by omega⟩, hsum⟩
          · intro p hp
            simpa [color] using (hsub hp).2
          · intro p hp q hq heq
            by_contra hne
            exact (huniq p q hp hq hne) heq⟩
        invFun := fun ⟨S, hS⟩ => ⟨S, by
          simp only [FB, Finset.mem_filter, Finset.mem_powersetCard] at hS
          rcases hS with ⟨⟨hsub, hcard⟩, hblue, huniq⟩
          refine ⟨?_, hcard, ?_⟩
          · intro p hp
            have ht := hsub hp
            simp only [T, Finset.mem_filter, Finset.mem_product,
              Finset.mem_range, Prod.fst, Prod.snd] at ht
            exact ⟨ht.2, by simpa [color] using hblue p hp⟩
          · intro p q hp hq hpq heq
            exact hpq (huniq p hp q hq heq)⟩
        left_inv := by intro x; cases x; rfl
        right_inv := by intro x; cases x; rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  simpa [ChoiceCount, FA, FB, PA, PB, blue_points_set] using
    bridgeA.trans (href.trans bridgeB.symm)
