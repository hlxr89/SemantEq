import Mathlib

set_option maxHeartbeats 800000

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

def T_cand (n : ℕ) : Set (ℕ × ℕ) := {p : ℕ × ℕ | p.1 + p.2 < n}

private theorem choiceCount_eq_card (n : ℕ) (color : ℕ × ℕ → Color)
    (coord : ℕ × ℕ → ℕ) :
    ChoiceCount n color coord =
      Nat.card {S : Finset (ℕ × ℕ) |
        (S : Set (ℕ × ℕ)) ⊆ {p | p ∈ T_cand n ∧ color p = .blue} ∧
        S.card = n ∧ ∀ p q, p ∈ S → q ∈ S → p ≠ q → coord p ≠ coord q} := by
  classical
  let F := ((T n).powersetCard n).filter fun s ↦
    (∀ p ∈ s, color p = .blue) ∧
    ∀ p ∈ s, ∀ q ∈ s, coord p = coord q → p = q
  let P := fun S : Finset (ℕ × ℕ) ↦
    (S : Set (ℕ × ℕ)) ⊆ {p | p ∈ T_cand n ∧ color p = .blue} ∧
    S.card = n ∧ ∀ p q, p ∈ S → q ∈ S → p ≠ q → coord p ≠ coord q
  have hmem (S : Finset (ℕ × ℕ)) : S ∈ F ↔ P S := by
    simp only [F, P, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hsub, hcard⟩, hblue, hinj⟩
      refine ⟨?_, hcard, ?_⟩
      · intro p hp
        have hsum : p.1 + p.2 < n := by
          have ht := hsub hp
          have ht' : (p.1 < n ∧ p.2 < n) ∧ p.1 + p.2 < n := by
            simpa [T] using ht
          exact ht'.2
        exact ⟨by simpa [T_cand] using hsum, hblue p hp⟩
      · intro p q hp hq hpq heq
        exact hpq (hinj p hp q hq heq)
    · rintro ⟨hsub, hcard, hcoord⟩
      refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
      · intro p hp
        have hsum : p.1 + p.2 < n := by simpa [T_cand] using (hsub hp).1
        simp only [T, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨lt_of_le_of_lt (Nat.le_add_right _ _) hsum,
          lt_of_le_of_lt (Nat.le_add_left _ _) hsum⟩, hsum⟩
      · intro p hp
        exact (hsub hp).2
      · intro p hp q hq heq
        by_contra hpq
        exact hcoord p q hp hq hpq heq
  let e : {S : Finset (ℕ × ℕ) // P S} ≃ ↑F :=
    Equiv.ofBijective
      (fun S ↦ ⟨S.1, (hmem S.1).2 S.2⟩)
      ⟨fun a b h ↦ Subtype.ext (congrArg (fun x ↦ x.1) h),
       fun S ↦ ⟨⟨S.1, (hmem S.1).1 S.2⟩, rfl⟩⟩
  unfold ChoiceCount
  calc
    _ = Nat.card (↑F) := by
      have hf := Nat.card_congr (Finset.equivFin F)
      simpa [F] using hf.symm
    _ = Nat.card {S : Finset (ℕ × ℕ) // P S} := (Nat.card_congr e).symm
    _ = _ := by rfl

-- ===== assumed statement (antecedent) =====
theorem imo2002_p1_assumed (n : ℕ) (_hn : 0 < n) (color : ℕ × ℕ → Color)
    (hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red) :
    ChoiceCount n color Prod.fst = ChoiceCount n color Prod.snd := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : 0 < n) (coloring : ℕ × ℕ → Bool) :
  (∀ (p : ℕ × ℕ), p ∈ T_cand n → (coloring p = true → ∀ (p' : ℕ × ℕ), p' ∈ T_cand n → p'.1 ≤ p.1 → p'.2 ≤ p.2 → coloring p' = true)) →
  let blue_points_set := {p : ℕ × ℕ | p ∈ T_cand n ∧ coloring p = false}
  let A := Nat.card {S : Finset (ℕ × ℕ) | (S : Set (ℕ × ℕ)) ⊆ blue_points_set ∧ S.card = n ∧ ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → p.1 ≠ q.1}
  let B := Nat.card {S : Finset (ℕ × ℕ) | (S : Set (ℕ × ℕ)) ⊆ blue_points_set ∧ S.card = n ∧ ∀ (p q : ℕ × ℕ), p ∈ S → q ∈ S → p ≠ q → p.2 ≠ q.2}
  A = B := by
  intro hmono
  let color : ℕ × ℕ → Color := fun p ↦ if coloring p then .red else .blue
  have hred : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red := by
    intro x' y' x y hx hy hxy hr
    have hc : coloring (x, y) = true := by
      simpa [color] using hr
    have hlower : x' + y' < n := lt_of_le_of_lt (Nat.add_le_add hx hy) hxy
    have hc' := hmono (x, y) (by simpa [T_cand] using hxy) hc (x', y')
      (by simpa [T_cand] using hlower) hx hy
    simp [color, hc']
  have h := imo2002_p1_assumed n hn color hred
  dsimp only
  have hc :
      Nat.card {S : Finset (ℕ × ℕ) |
        (S : Set (ℕ × ℕ)) ⊆ {p | p ∈ T_cand n ∧ color p = .blue} ∧
        S.card = n ∧ ∀ p q, p ∈ S → q ∈ S → p ≠ q → p.1 ≠ q.1} =
      Nat.card {S : Finset (ℕ × ℕ) |
        (S : Set (ℕ × ℕ)) ⊆ {p | p ∈ T_cand n ∧ color p = .blue} ∧
        S.card = n ∧ ∀ p q, p ∈ S → q ∈ S → p ≠ q → p.2 ≠ q.2} := by
    rw [← choiceCount_eq_card n color Prod.fst, ← choiceCount_eq_card n color Prod.snd]
    exact h
  simpa [color] using hc
