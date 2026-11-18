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
theorem problem_statement_assumed (n : ℕ) (hn : 0 < n) (coloring : ℕ × ℕ → Bool) 
    (h : satisfies_condition n coloring) :
  count_A n coloring = count_B n coloring := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2002_p1 (n : ℕ) (_hn : 0 < n) (color : ℕ × ℕ → Color)
    (hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red) :
    ChoiceCount n color Prod.fst = ChoiceCount n color Prod.snd := by
  classical
  let coloring : ℕ × ℕ → Bool := fun p => decide (color p = .red)
  have hc : satisfies_condition n coloring := by
    intro p hp hred q _hq hx hy
    have hpred : color p = .red := by
      simpa [coloring] using hred
    have hqred := hcolor q.1 q.2 p.1 p.2 hx hy hp hpred
    simp [coloring, hqred]
  have count_eq (coord : ℕ × ℕ → ℕ) :
      Set.ncard {s : Finset (ℕ × ℕ) | s.card = n ∧
        (∀ p ∈ s, p ∈ blue_points n coloring) ∧
        (∀ p ∈ s, ∀ q ∈ s, p ≠ q → coord p ≠ coord q)} =
      ChoiceCount n color coord := by
    let F := ((T n).powersetCard n).filter fun s ↦
      (∀ p ∈ s, color p = .blue) ∧
      ∀ p ∈ s, ∀ q ∈ s, coord p = coord q → p = q
    have hs : {s : Finset (ℕ × ℕ) | s.card = n ∧
        (∀ p ∈ s, p ∈ blue_points n coloring) ∧
        (∀ p ∈ s, ∀ q ∈ s, p ≠ q → coord p ≠ coord q)} =
        (↑F : Set (Finset (ℕ × ℕ))) := by
      ext s
      change (s.card = n ∧
        (∀ p ∈ s, p ∈ blue_points n coloring) ∧
        (∀ p ∈ s, ∀ q ∈ s, p ≠ q → coord p ≠ coord q)) ↔ s ∈ F
      simp only [F, Finset.mem_filter, Finset.mem_powersetCard, Set.mem_setOf_eq,
        blue_points, T_set, Set.mem_setOf_eq, T, Finset.mem_filter, coloring]
      constructor
      · rintro ⟨hcard, hblue, hinj⟩
        refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
        · intro p hp
          apply Finset.mem_filter.2
          exact ⟨Finset.mem_product.2 ⟨
              Finset.mem_range.2 (lt_of_le_of_lt (Nat.le_add_right _ _) (hblue p hp).1),
              Finset.mem_range.2 (lt_of_le_of_lt (Nat.le_add_left _ _) (hblue p hp).1)⟩,
            (hblue p hp).1⟩
        · intro p hp
          have hf := (hblue p hp).2
          cases he : color p with
          | red => simp [he] at hf
          | blue => rfl
        · intro p hp q hq heq
          by_contra hne
          exact (hinj p hp q hq hne) heq
      · rintro ⟨⟨hsub, hcard⟩, hblue, hinj⟩
        refine ⟨hcard, ?_, ?_⟩
        · intro p hp
          have ht := (Finset.mem_filter.1 (hsub hp)).2
          have hb := hblue p hp
          have hf : decide (color p = Color.red) = false := by simp [hb]
          exact ⟨ht, hf⟩
        · intro p hp q hq hne heq
          exact hne (hinj p hp q hq heq)
    rw [hs]
    rw [Set.ncard_coe_finset]
    unfold ChoiceCount
    simp only [F]
    congr 1
    ext s
    simp only [Finset.mem_filter]
  have hab := problem_statement_assumed n _hn coloring hc
  rw [count_A, count_B] at hab
  change Set.ncard {s : Finset (ℕ × ℕ) | s.card = n ∧
      (∀ p ∈ s, p ∈ blue_points n coloring) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → p.1 ≠ q.1)} =
    Set.ncard {s : Finset (ℕ × ℕ) | s.card = n ∧
      (∀ p ∈ s, p ∈ blue_points n coloring) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → p.2 ≠ q.2)} at hab
  rw [count_eq Prod.fst, count_eq Prod.snd] at hab
  exact hab
