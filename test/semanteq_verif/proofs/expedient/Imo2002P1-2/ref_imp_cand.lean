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

-- Renamed from the candidate's `T` because the reference defines a different `T`.
def TSet (n : ℕ) : Set (ℕ × ℕ) :=
  {p | p.1 + p.2 < n}

def ValidColoring (n : ℕ) (B : Set (ℕ × ℕ)) : Prop :=
  B ⊆ TSet n ∧
  ∀ p q : ℕ × ℕ, p ∈ B → q ∈ TSet n → p.1 ≤ q.1 → p.2 ≤ q.2 → q ∈ B

noncomputable def A (n : ℕ) : ℕ :=
  Nat.card {B : Set (ℕ × ℕ) | ValidColoring n B ∧ 
    ∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ B) ∧ 
    (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.1 ≠ q.1)}

noncomputable def B (n : ℕ) : ℕ :=
  Nat.card {B : Set (ℕ × ℕ) | ValidColoring n B ∧ 
    ∃ s : Finset (ℕ × ℕ), s.card = n ∧ (∀ p ∈ s, p ∈ B) ∧ 
    (∀ p q, p ∈ s → q ∈ s → p ≠ q → p.2 ≠ q.2)}

-- ===== assumed statement (antecedent) =====
theorem imo2002_p1_assumed (n : ℕ) (_hn : 0 < n) (color : ℕ × ℕ → Color)
    (hcolor : ∀ x' y' x y, x' ≤ x → y' ≤ y → x + y < n →
      color (x, y) = .red → color (x', y') = .red) :
    ChoiceCount n color Prod.fst = ChoiceCount n color Prod.snd := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (n : ℕ) (hn : n > 0) : A n = B n := by
  unfold A B
  apply Nat.card_congr
  let e : ℕ × ℕ ≃ ℕ × ℕ := Equiv.prodComm ℕ ℕ
  let swap : Set (ℕ × ℕ) → Set (ℕ × ℕ) := fun S => {p | e p ∈ S}
  refine
    { toFun := fun S => ⟨swap S.1, ?_⟩
      invFun := fun S => ⟨swap S.1, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rcases S.2 with ⟨⟨hsub, hup⟩, s, hcard, hs, hdistinct⟩
    constructor
    · constructor
      · intro p hp
        simpa [swap, e, TSet, Nat.add_comm] using hsub hp
      · intro p q hp hq hpq₁ hpq₂
        change e q ∈ S.1
        apply hup (e p) (e q) hp
        · simpa [e, TSet, Nat.add_comm] using hq
        · exact hpq₂
        · exact hpq₁
    · refine ⟨s.map e.toEmbedding, by simpa, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_map.1 hp with ⟨q, hq, rfl⟩
        exact hs q hq
      · intro p q hp hq hpq
        rcases Finset.mem_map.1 hp with ⟨p, hp_mem, rfl⟩
        rcases Finset.mem_map.1 hq with ⟨q, hq_mem, rfl⟩
        change p.1 ≠ q.1
        apply hdistinct p q hp_mem hq_mem
        intro h
        apply hpq
        simp [h]
  · rcases S.2 with ⟨⟨hsub, hup⟩, s, hcard, hs, hdistinct⟩
    constructor
    · constructor
      · intro p hp
        simpa [swap, e, TSet, Nat.add_comm] using hsub hp
      · intro p q hp hq hpq₁ hpq₂
        change e q ∈ S.1
        apply hup (e p) (e q) hp
        · simpa [e, TSet, Nat.add_comm] using hq
        · exact hpq₂
        · exact hpq₁
    · refine ⟨s.map e.toEmbedding, by simpa, ?_, ?_⟩
      · intro p hp
        rcases Finset.mem_map.1 hp with ⟨q, hq, rfl⟩
        exact hs q hq
      · intro p q hp hq hpq
        rcases Finset.mem_map.1 hp with ⟨p, hp_mem, rfl⟩
        rcases Finset.mem_map.1 hq with ⟨q, hq_mem, rfl⟩
        change p.2 ≠ q.2
        apply hdistinct p q hp_mem hq_mem
        intro h
        apply hpq
        simp [h]
  · intro S
    apply Subtype.ext
    ext p
    rfl
  · intro S
    apply Subtype.ext
    ext p
    rfl
