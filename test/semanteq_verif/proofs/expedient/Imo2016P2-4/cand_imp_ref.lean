import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
namespace Imo2016P2

/-- The three letters `I`, `M`, `O`. -/
abbrev Letter := Fin 3

variable {n : ℕ}

/-- A finite set of cells is *balanced* under the coloring `f` if each of the
three letters occurs on exactly one third of its cells. -/
def Balanced (f : Fin n → Fin n → Letter) (cells : Finset (Fin n × Fin n)) : Prop :=
  ∀ c : Letter, (cells.filter (fun p ↦ f p.1 p.2 = c)).card = cells.card / 3

/-- The cells of row `r`. -/
def row (r : Fin n) : Finset (Fin n × Fin n) := Finset.univ.filter (fun p ↦ p.1 = r)

/-- The cells of column `k`. -/
def col (k : Fin n) : Finset (Fin n × Fin n) := Finset.univ.filter (fun p ↦ p.2 = k)

/-- A diagonal of the first type: the cells `(i, j)` with `i + j = s`. -/
def diagSum (s : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p ↦ (p.1 : ℕ) + (p.2 : ℕ) = s)

/-- A diagonal of the second type: the cells `(i, j)` with `i - j = d`. -/
def diagDiff (d : ℤ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p ↦ ((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ) = d)

/-- The coloring `f` of the `n × n` table satisfies all the required conditions:
every row and column is balanced, and every diagonal whose length is a multiple
of three is balanced. -/
def MODTable (f : Fin n → Fin n → Letter) : Prop :=
  (∀ r : Fin n, Balanced f (row r)) ∧
  (∀ k : Fin n, Balanced f (col k)) ∧
  (∀ s : ℕ, 3 ∣ (diagSum (n := n) s).card → Balanced f (diagSum s)) ∧
  (∀ d : ℤ, 3 ∣ (diagDiff (n := n) d).card → Balanced f (diagDiff d))

abbrev solution : Set ℕ := { n | 9 ∣ n }

end Imo2016P2

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed : 
  ∀ n : ℕ, n > 0 → 
  (∃ (table : Fin n → Fin n → Fin 3), 
    (∀ i : Fin n, 
      (Finset.univ.filter (fun j => table i j = 0)).card = n / 3 ∧
      (Finset.univ.filter (fun j => table i j = 1)).card = n / 3 ∧
      (Finset.univ.filter (fun j => table i j = 2)).card = n / 3) ∧
    (∀ j : Fin n, 
      (Finset.univ.filter (fun i => table i j = 0)).card = n / 3 ∧
      (Finset.univ.filter (fun i => table i j = 1)).card = n / 3 ∧
      (Finset.univ.filter (fun i => table i j = 2)).card = n / 3) ∧
    (∀ (k : ℤ), 
      let diag1 := Finset.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = k) (Finset.univ : Finset (Fin n × Fin n))
      if 3 ∣ diag1.card then
        (Finset.filter (fun p => table p.1 p.2 = 0) diag1).card = diag1.card / 3 ∧
        (Finset.filter (fun p => table p.1 p.2 = 1) diag1).card = diag1.card / 3 ∧
        (Finset.filter (fun p => table p.1 p.2 = 2) diag1).card = diag1.card / 3
      else True) ∧
    (∀ (k : ℤ), 
      let diag2 := Finset.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = k) (Finset.univ : Finset (Fin n × Fin n))
      if 3 ∣ diag2.card then
        (Finset.filter (fun p => table p.1 p.2 = 0) diag2).card = diag2.card / 3 ∧
        (Finset.filter (fun p => table p.1 p.2 = 1) diag2).card = diag2.card / 3 ∧
        (Finset.filter (fun p => table p.1 p.2 = 2) diag2).card = diag2.card / 3
      else True)
  ) ↔ 9 ∣ n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
namespace Imo2016P2

set_option maxHeartbeats 800000 in
theorem imo2016_p2 (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  let Good := fun table : Fin n → Fin n → Fin 3 =>
    (∀ i : Fin n,
      (Finset.univ.filter (fun j => table i j = 0)).card = n / 3 ∧
      (Finset.univ.filter (fun j => table i j = 1)).card = n / 3 ∧
      (Finset.univ.filter (fun j => table i j = 2)).card = n / 3) ∧
    (∀ j : Fin n,
      (Finset.univ.filter (fun i => table i j = 0)).card = n / 3 ∧
      (Finset.univ.filter (fun i => table i j = 1)).card = n / 3 ∧
      (Finset.univ.filter (fun i => table i j = 2)).card = n / 3) ∧
    (∀ k : ℤ,
      let diag1 := Finset.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = k) Finset.univ
      if 3 ∣ diag1.card then
        (diag1.filter (fun p => table p.1 p.2 = 0)).card = diag1.card / 3 ∧
        (diag1.filter (fun p => table p.1 p.2 = 1)).card = diag1.card / 3 ∧
        (diag1.filter (fun p => table p.1 p.2 = 2)).card = diag1.card / 3
      else True) ∧
    (∀ k : ℤ,
      let diag2 := Finset.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = k) Finset.univ
      if 3 ∣ diag2.card then
        (diag2.filter (fun p => table p.1 p.2 = 0)).card = diag2.card / 3 ∧
        (diag2.filter (fun p => table p.1 p.2 = 1)).card = diag2.card / 3 ∧
        (diag2.filter (fun p => table p.1 p.2 = 2)).card = diag2.card / 3
      else True)
  have rowCard (f : Fin n → Fin n → Fin 3) (i : Fin n) (c : Fin 3) :
      (Finset.univ.filter (fun j => f i j = c)).card =
        ((Imo2016P2.row i).filter (fun p => f p.1 p.2 = c)).card := by
    apply Finset.card_bij (fun j _ => (i, j))
    · simp [Imo2016P2.row]
    · simp
    · rintro ⟨a, b⟩ hp
      simp [Imo2016P2.row] at hp
      rcases hp with ⟨rfl, hf⟩
      exact ⟨b, by simpa using hf, rfl⟩
  have rowSize (i : Fin n) : (Imo2016P2.row i).card = n := by
    let e : Fin n ↪ Fin n × Fin n := ⟨fun j => (i, j), by
      intro a b hab
      simpa using congrArg Prod.snd hab⟩
    have hr : Imo2016P2.row i = Finset.univ.map e := by
      ext ⟨a, b⟩
      simp [Imo2016P2.row, e, eq_comm]
    rw [hr]
    simp
  have colCard (f : Fin n → Fin n → Fin 3) (j : Fin n) (c : Fin 3) :
      (Finset.univ.filter (fun i => f i j = c)).card =
        ((Imo2016P2.col j).filter (fun p => f p.1 p.2 = c)).card := by
    apply Finset.card_bij (fun i _ => (i, j))
    · simp [Imo2016P2.col]
    · simp
    · rintro ⟨a, b⟩ hp
      simp [Imo2016P2.col] at hp
      rcases hp with ⟨rfl, hf⟩
      exact ⟨a, by simpa using hf, rfl⟩
  have colSize (j : Fin n) : (Imo2016P2.col j).card = n := by
    let e : Fin n ↪ Fin n × Fin n := ⟨fun i => (i, j), by
      intro a b hab
      simpa using congrArg Prod.fst hab⟩
    have hc : Imo2016P2.col j = Finset.univ.map e := by
      ext ⟨a, b⟩
      simp [Imo2016P2.col, e, eq_comm]
    rw [hc]
    simp
  have bridge (f : Fin n → Fin n → Fin 3) : Imo2016P2.MODTable f ↔ Good f := by
    constructor
    · rintro ⟨hr, hc, hs, hd⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i
        refine ⟨?_, ?_, ?_⟩
        · rw [rowCard]
          simpa [Imo2016P2.Balanced, rowSize] using hr i (0 : Fin 3)
        · rw [rowCard]
          simpa [Imo2016P2.Balanced, rowSize] using hr i (1 : Fin 3)
        · rw [rowCard]
          simpa [Imo2016P2.Balanced, rowSize] using hr i (2 : Fin 3)
      · intro j
        refine ⟨?_, ?_, ?_⟩
        · rw [colCard]
          simpa [Imo2016P2.Balanced, colSize] using hc j (0 : Fin 3)
        · rw [colCard]
          simpa [Imo2016P2.Balanced, colSize] using hc j (1 : Fin 3)
        · rw [colCard]
          simpa [Imo2016P2.Balanced, colSize] using hc j (2 : Fin 3)
      · intro k
        dsimp
        split_ifs with hk
        · by_cases hk0 : 0 ≤ k
          · have heq : Finset.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = k) Finset.univ =
                Imo2016P2.diagSum k.toNat := by
              ext p
              simp [Imo2016P2.diagSum]
              omega
            have hb := hs k.toNat (by simpa [heq] using hk)
            rw [heq]
            exact ⟨hb 0, hb 1, hb 2⟩
          · have heq : Finset.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = k) Finset.univ = ∅ := by
              ext p
              simp
              omega
            simp [heq]
      · intro k
        dsimp
        split_ifs with hk
        · have hb := hd k (by simpa [Imo2016P2.diagDiff] using hk)
          exact ⟨hb 0, hb 1, hb 2⟩
    · rintro ⟨hr, hc, hs, hd⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i c
        fin_cases c <;> rw [← rowCard, rowSize] <;> aesop
      · intro j c
        fin_cases c <;> rw [← colCard, colSize] <;> aesop
      · intro s hdiv c
        have heq : Finset.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = (s : ℤ)) Finset.univ =
            Imo2016P2.diagSum s := by
          ext p
          simp [Imo2016P2.diagSum]
          omega
        have h := hs (s : ℤ)
        dsimp at h
        rw [if_pos (by simpa [heq] using hdiv)] at h
        fin_cases c
        · simpa [heq] using h.1
        · simpa [heq] using h.2.1
        · simpa [heq] using h.2.2
      · intro d hdiv c
        have h := hd d
        dsimp at h
        rw [if_pos (by simpa [Imo2016P2.diagDiff] using hdiv)] at h
        fin_cases c
        · simpa [Imo2016P2.diagDiff] using h.1
        · simpa [Imo2016P2.diagDiff] using h.2.1
        · simpa [Imo2016P2.diagDiff] using h.2.2
  have hcand : (∃ f, Good f) ↔ 9 ∣ n := by
    simpa only [hn, true_implies] using (problem_statement_assumed n)
  constructor
  · intro h
    obtain ⟨f, hf⟩ := hcand.mpr h
    exact ⟨f, (bridge f).mpr hf⟩
  · rintro ⟨f, hf⟩
    exact hcand.mp ⟨f, (bridge f).mp hf⟩

end Imo2016P2

