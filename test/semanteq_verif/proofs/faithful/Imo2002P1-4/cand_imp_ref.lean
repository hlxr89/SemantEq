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
  classical
  let coloring : ℕ × ℕ → Bool := fun p => color p == .red
  have hcoloring : ∀ (p : ℕ × ℕ), p ∈ T_set n →
      (coloring p = true → ∀ (p' : ℕ × ℕ), p' ∈ T_set n →
        p'.1 ≤ p.1 → p'.2 ≤ p.2 → coloring p' = true) := by
    intro p hp hred p' hp' hx hy
    have hred' : color p = .red := by simpa [coloring] using hred
    have hp_sum : p.1 + p.2 < n := hp
    have := hcolor p'.1 p'.2 p.1 p.2 hx hy hp_sum hred'
    simpa [coloring] using this
  have hcand := problem_statement_assumed n _hn coloring hcoloring
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
            simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            exact ⟨⟨by omega, by omega⟩, hsum⟩
          · intro p hp
            have hb := (hsub hp).2
            change (color p == .red) = false at hb
            cases hcp : color p <;> simp_all
          · intro p hp q hq heq
            by_contra hne
            exact (huniq p q hp hq hne) heq⟩
        invFun := fun ⟨S, hS⟩ => ⟨S, by
          simp only [FA, Finset.mem_filter, Finset.mem_powersetCard] at hS
          rcases hS with ⟨⟨hsub, hcard⟩, hblue, huniq⟩
          refine ⟨?_, hcard, ?_⟩
          · intro p hp
            have ht := hsub hp
            simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht
            refine ⟨ht.2, ?_⟩
            change (color p == .red) = false
            simpa [hblue p hp]
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
            simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
            exact ⟨⟨by omega, by omega⟩, hsum⟩
          · intro p hp
            have hb := (hsub hp).2
            change (color p == .red) = false at hb
            cases hcp : color p <;> simp_all
          · intro p hp q hq heq
            by_contra hne
            exact (huniq p q hp hq hne) heq⟩
        invFun := fun ⟨S, hS⟩ => ⟨S, by
          simp only [FB, Finset.mem_filter, Finset.mem_powersetCard] at hS
          rcases hS with ⟨⟨hsub, hcard⟩, hblue, huniq⟩
          refine ⟨?_, hcard, ?_⟩
          · intro p hp
            have ht := hsub hp
            simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ht
            refine ⟨ht.2, ?_⟩
            change (color p == .red) = false
            simpa [hblue p hp]
          · intro p q hp hq hpq heq
            exact hpq (huniq p hp q hq heq)⟩
        left_inv := by intro x; cases x; rfl
        right_inv := by intro x; cases x; rfl }
    rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  simpa [ChoiceCount, FA, FB, PA, PB, blue_points_set, coloring] using
    bridgeA.symm.trans (hcand.trans bridgeB)
