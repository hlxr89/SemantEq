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

theorem imo2016_p2 (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  have row_color_card (table : Fin n → Fin n → Fin 3) (i : Fin n) (c : Fin 3) :
      ((row i).filter (fun p => table p.1 p.2 = c)).card =
        (Finset.univ.filter (fun j => table i j = c)).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · simp_all [row]
    · simp_all [row, Prod.ext_iff]
    · intro b hb
      refine ⟨(i, b), ?_, rfl⟩
      simp_all [row]
  have row_card (i : Fin n) : (row i).card = n := by
    calc
      _ = (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_bij (fun p _ => p.2)
        · simp
        · simp_all [row, Prod.ext_iff]
        · intro b hb
          refine ⟨(i, b), ?_, rfl⟩
          simp [row]
      _ = n := Finset.card_fin n
  have col_color_card (table : Fin n → Fin n → Fin 3) (j : Fin n) (c : Fin 3) :
      ((col j).filter (fun p => table p.1 p.2 = c)).card =
        (Finset.univ.filter (fun i => table i j = c)).card := by
    apply Finset.card_bij (fun p _ => p.1)
    · simp_all [col]
    · simp_all [col, Prod.ext_iff]
    · intro a ha
      refine ⟨(a, j), ?_, rfl⟩
      simp_all [col]
  have col_card (j : Fin n) : (col j).card = n := by
    calc
      _ = (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_bij (fun p _ => p.1)
        · simp
        · simp_all [col, Prod.ext_iff]
        · intro a ha
          refine ⟨(a, j), ?_, rfl⟩
          simp [col]
      _ = n := Finset.card_fin n
  constructor
  · intro hdiv
    have hcand := (problem_statement_assumed n).mpr hdiv hn
    rcases hcand with ⟨table, hrow, hcol, hsum, hdiff⟩
    refine ⟨table, ?_, ?_, ?_, ?_⟩
    · intro i c
      fin_cases c
      · simpa [row_color_card, row_card] using (hrow i).1
      · simpa [row_color_card, row_card] using (hrow i).2.1
      · simpa [row_color_card, row_card] using (hrow i).2.2
    · intro j c
      fin_cases c
      · simpa [col_color_card, col_card] using (hcol j).1
      · simpa [col_color_card, col_card] using (hcol j).2.1
      · simpa [col_color_card, col_card] using (hcol j).2.2
    · intro s hthree c
      have hs := hsum (s : ℤ)
      dsimp at hs
      have heq :
          (Finset.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = (s : ℤ)) Finset.univ) =
            diagSum (n := n) s := by
            ext p
            simp [diagSum]
            omega
      rw [heq] at hs
      simp [hthree] at hs
      fin_cases c
      · exact hs.1
      · exact hs.2.1
      · exact hs.2.2
    · intro d hthree c
      have hd := hdiff d
      dsimp at hd
      change (if h : 3 ∣ (diagDiff (n := n) d).card then _ else True) at hd
      simp [hthree] at hd
      fin_cases c
      · exact hd.1
      · exact hd.2.1
      · exact hd.2.2
  · rintro ⟨table, hrow, hcol, hsum, hdiff⟩
    apply (problem_statement_assumed n).mp
    intro _hn
    refine ⟨table, ?_, ?_, ?_, ?_⟩
    · intro i
      have h0 := hrow i 0
      have h1 := hrow i 1
      have h2 := hrow i 2
      rw [row_color_card, row_card] at h0 h1 h2
      exact ⟨h0, h1, h2⟩
    · intro j
      have h0 := hcol j 0
      have h1 := hcol j 1
      have h2 := hcol j 2
      rw [col_color_card, col_card] at h0 h1 h2
      exact ⟨h0, h1, h2⟩
    · intro k
      dsimp
      by_cases hk : 0 ≤ k
      · have heq :
          (Finset.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = k) Finset.univ) =
            diagSum (n := n) k.toNat := by
            ext p
            simp [diagSum]
            omega
        rw [heq]
        split
        next hthree => exact ⟨hsum k.toNat hthree 0, hsum k.toNat hthree 1, hsum k.toNat hthree 2⟩
        next => trivial
      · have hempty :
          (Finset.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = k) Finset.univ) = ∅ := by
            ext p
            simp
            omega
        simp [hempty]
    · intro k
      dsimp
      change if h : 3 ∣ (diagDiff (n := n) k).card then _ else True
      split
      next hthree => exact ⟨hdiff k hthree 0, hdiff k hthree 1, hdiff k hthree 2⟩
      next => trivial

end Imo2016P2
