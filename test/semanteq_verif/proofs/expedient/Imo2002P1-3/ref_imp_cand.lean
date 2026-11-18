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
theorem imo2002_p1_assumed (n : ℕ) (_hn : 0 < n) (color : ℕ × ℕ → Color)
    (hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red) :
    ChoiceCount n color Prod.fst = ChoiceCount n color Prod.snd := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : 0 < n) (coloring : ℕ × ℕ → Bool) 
    (h : satisfies_condition n coloring) :
  count_A n coloring = count_B n coloring := by
  classical
  let color : ℕ × ℕ → Color := fun p => if coloring p then .red else .blue
  have hc : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red := by
    intro x' y' x y hx hy hp hr
    have hp' : (x, y) ∈ T_set n := hp
    have hq' : (x', y') ∈ T_set n := by
      exact lt_of_le_of_lt (Nat.add_le_add hx hy) hp
    have htrue : coloring (x, y) = true := by
      simp only [color] at hr
      split at hr <;> simp_all
    have := h (x, y) hp' htrue (x', y') hq' hx hy
    simp [color, this]
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
        blue_points, T_set, Set.mem_setOf_eq, T, Finset.mem_filter,
        Finset.mem_product, Finset.mem_range, color]
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
          simp [hf]
        · intro p hp q hq heq
          by_contra hne
          exact (hinj p hp q hq hne) heq
      · rintro ⟨⟨hsub, hcard⟩, hblue, hinj⟩
        refine ⟨hcard, ?_, ?_⟩
        · intro p hp
          have ht := (Finset.mem_filter.1 (hsub hp)).2
          have hb := hblue p hp
          simp only [color] at hb
          have hf : coloring p = false := by
            split at hb <;> simp_all
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
  rw [count_A, count_B]
  change Set.ncard {s : Finset (ℕ × ℕ) | s.card = n ∧
      (∀ p ∈ s, p ∈ blue_points n coloring) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → p.1 ≠ q.1)} =
    Set.ncard {s : Finset (ℕ × ℕ) | s.card = n ∧
      (∀ p ∈ s, p ∈ blue_points n coloring) ∧
      (∀ p ∈ s, ∀ q ∈ s, p ≠ q → p.2 ≠ q.2)}
  rw [count_eq Prod.fst, count_eq Prod.snd]
  exact imo2002_p1_assumed n hn color hc
