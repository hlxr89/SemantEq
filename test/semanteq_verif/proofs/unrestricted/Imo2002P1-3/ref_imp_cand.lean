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
  let color : ℕ × ℕ → Color := fun p => if coloring p then .red else .blue
  have hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red := by
    intro x' y' x y hx hy hxy hp
    have hp' : coloring (x, y) = true := by
      by_contra hf
      have : coloring (x, y) = false := Bool.eq_false_of_not_eq_true hf
      simp [color, this] at hp
    have hqT : (x', y') ∈ T_set n := by
      simp [T_set]
      omega
    have hq := h (x, y) (by simp [T_set, hxy]) hp' (x', y') hqT hx hy
    simp [color, hq]
  have bridge (coord : ℕ × ℕ → ℕ) :
      Set.ncard {s : Finset (ℕ × ℕ) | s.card = n ∧
        (∀ p ∈ s, p ∈ blue_points n coloring) ∧
        (∀ p ∈ s, ∀ q ∈ s, p ≠ q → coord p ≠ coord q)} =
        ChoiceCount n color coord := by
    let F := ((T n).powersetCard n).filter fun s ↦
      (∀ p ∈ s, color p = .blue) ∧
      ∀ p ∈ s, ∀ q ∈ s, coord p = coord q → p = q
    have heq : {s : Finset (ℕ × ℕ) | s.card = n ∧
        (∀ p ∈ s, p ∈ blue_points n coloring) ∧
        (∀ p ∈ s, ∀ q ∈ s, p ≠ q → coord p ≠ coord q)} = (F : Set _) := by
      ext s
      change (s.card = n ∧
        (∀ p ∈ s, p ∈ blue_points n coloring) ∧
        (∀ p ∈ s, ∀ q ∈ s, p ≠ q → coord p ≠ coord q)) ↔ s ∈ F
      simp only [F, Finset.mem_filter, Finset.mem_powersetCard]
      constructor
      · rintro ⟨hcard, hblue, hdist⟩
        refine ⟨⟨?_, hcard⟩, ?_, ?_⟩
        · intro p hp
          have := hblue p hp
          have hsum : p.1 + p.2 < n := by
            simpa [blue_points, T_set] using this.1
          simp [T]
          omega
        · intro p hp
          have hb := (hblue p hp).2
          simp [color, hb]
        · intro p hp q hq hc
          by_contra hpq
          exact (hdist p hp q hq hpq) hc
      · intro hs
        rcases hs with ⟨⟨hsub, hcard⟩, hblue, hdist⟩
        refine ⟨hcard, ?_, ?_⟩
        · intro p hp
          have hpt := hsub hp
          have hb := hblue p hp
          constructor
          · simp [T] at hpt
            simpa [T_set] using hpt.2
          · simp only [color] at hb
            split at hb <;> simp_all
        · intro p hp q hq hpq hc
          exact hpq (hdist p hp q hq hc)
    rw [heq, Set.ncard_coe_finset]
    rfl
  rw [count_A, count_B, A_subsets, B_subsets]
  rw [bridge Prod.fst, bridge Prod.snd]
  exact imo2002_p1_assumed n hn color hcolor
