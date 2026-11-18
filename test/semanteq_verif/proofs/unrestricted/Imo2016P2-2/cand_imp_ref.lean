import Mathlib

set_option maxHeartbeats 1000000

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
  (∃ table : Fin n → Fin n → Fin 3, 
    -- Each row has n/3 of each letter
    (∀ i : Fin n, 
      (Finset.univ.filter (fun j => table i j = 0)).card = n / 3 ∧
      (Finset.univ.filter (fun j => table i j = 1)).card = n / 3 ∧
      (Finset.univ.filter (fun j => table i j = 2)).card = n / 3) ∧
    -- Each column has n/3 of each letter
    (∀ j : Fin n, 
      (Finset.univ.filter (fun i => table i j = 0)).card = n / 3 ∧
      (Finset.univ.filter (fun i => table i j = 1)).card = n / 3 ∧
      (Finset.univ.filter (fun i => table i j = 2)).card = n / 3) ∧
    -- Type 1 diagonals: i + j = constant
    (∀ s : ℕ, 2 ≤ s ∧ s ≤ 2 * n → 
      let diagonal := Finset.filter (fun p : Fin n × Fin n => p.1.val + p.2.val + 2 = s) (Finset.univ.product Finset.univ)
      diagonal.card % 3 = 0 →
        (diagonal.filter (fun p => table p.1 p.2 = 0)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => table p.1 p.2 = 1)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => table p.1 p.2 = 2)).card = diagonal.card / 3) ∧
    -- Type 2 diagonals: i - j = constant
    (∀ d : ℤ, -(n - 1) ≤ d ∧ d ≤ n - 1 → 
      let diagonal := Finset.filter (fun p : Fin n × Fin n => (p.1.val : ℤ) - (p.2.val : ℤ) = d) (Finset.univ.product Finset.univ)
      diagonal.card % 3 = 0 →
        (diagonal.filter (fun p => table p.1 p.2 = 0)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => table p.1 p.2 = 1)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => table p.1 p.2 = 2)).card = diagonal.card / 3)
  ) ↔ 
  9 ∣ n := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
namespace Imo2016P2

theorem imo2016_p2 (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  let E : Prop := ∃ table : Fin n → Fin n → Fin 3,
    (∀ i : Fin n,
      (Finset.univ.filter (fun j => table i j = 0)).card = n / 3 ∧
      (Finset.univ.filter (fun j => table i j = 1)).card = n / 3 ∧
      (Finset.univ.filter (fun j => table i j = 2)).card = n / 3) ∧
    (∀ j : Fin n,
      (Finset.univ.filter (fun i => table i j = 0)).card = n / 3 ∧
      (Finset.univ.filter (fun i => table i j = 1)).card = n / 3 ∧
      (Finset.univ.filter (fun i => table i j = 2)).card = n / 3) ∧
    (∀ s : ℕ, 2 ≤ s ∧ s ≤ 2 * n →
      let diagonal := Finset.filter (fun p : Fin n × Fin n => p.1.val + p.2.val + 2 = s) (Finset.univ.product Finset.univ)
      diagonal.card % 3 = 0 →
        (diagonal.filter (fun p => table p.1 p.2 = 0)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => table p.1 p.2 = 1)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => table p.1 p.2 = 2)).card = diagonal.card / 3) ∧
    (∀ d : ℤ, -(n - 1) ≤ d ∧ d ≤ n - 1 →
      let diagonal := Finset.filter (fun p : Fin n × Fin n => (p.1.val : ℤ) - (p.2.val : ℤ) = d) (Finset.univ.product Finset.univ)
      diagonal.card % 3 = 0 →
        (diagonal.filter (fun p => table p.1 p.2 = 0)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => table p.1 p.2 = 1)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => table p.1 p.2 = 2)).card = diagonal.card / 3)
  have bridge : E ↔ ∃ f : Fin n → Fin n → Imo2016P2.Letter, Imo2016P2.MODTable f := by
    have row_filter_card (f : Fin n → Fin n → Fin 3) (i : Fin n) (c : Fin 3) :
        ((Imo2016P2.row i).filter (fun p => f p.1 p.2 = c)).card =
          (Finset.univ.filter (fun j => f i j = c)).card := by
      apply Finset.card_bij (fun p _ => p.2)
      · simp_all [Imo2016P2.row]
      · intro a ha b hb hab
        apply Prod.ext
        · simp_all [Imo2016P2.row]
        · exact hab
      · intro b hb
        refine ⟨(i, b), ?_, rfl⟩
        simp_all [Imo2016P2.row]
    have row_card (i : Fin n) : (Imo2016P2.row i).card = n := by
      have hcard : (Imo2016P2.row i).card = (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_bij (fun p _ => p.2)
        · simp
        · intro a ha b hb hab
          apply Prod.ext
          · simp_all [Imo2016P2.row]
          · exact hab
        · intro b hb
          refine ⟨(i, b), ?_, rfl⟩
          simp [Imo2016P2.row]
      simpa using hcard
    have col_filter_card (f : Fin n → Fin n → Fin 3) (j : Fin n) (c : Fin 3) :
        ((Imo2016P2.col j).filter (fun p => f p.1 p.2 = c)).card =
          (Finset.univ.filter (fun i => f i j = c)).card := by
      apply Finset.card_bij (fun p _ => p.1)
      · simp_all [Imo2016P2.col]
      · intro a ha b hb hab
        apply Prod.ext
        · exact hab
        · simp_all [Imo2016P2.col]
      · intro i hi
        refine ⟨(i, j), ?_, rfl⟩
        simp_all [Imo2016P2.col]
    have col_card (j : Fin n) : (Imo2016P2.col j).card = n := by
      have hcard : (Imo2016P2.col j).card = (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_bij (fun p _ => p.1)
        · simp
        · intro a ha b hb hab
          apply Prod.ext
          · exact hab
          · simp_all [Imo2016P2.col]
        · intro i hi
          refine ⟨(i, j), ?_, rfl⟩
          simp [Imo2016P2.col]
      simpa using hcard
    constructor
    · rintro ⟨f, hrow, hcol, hsum, hdiff⟩
      refine ⟨f, ?_⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i c
        calc
          _ = (Finset.univ.filter (fun j => f i j = c)).card := row_filter_card f i c
          _ = n / 3 := by fin_cases c <;> simp_all
          _ = (Imo2016P2.row i).card / 3 := by rw [row_card]
      · intro j c
        calc
          _ = (Finset.univ.filter (fun i => f i j = c)).card := col_filter_card f j c
          _ = n / 3 := by fin_cases c <;> simp_all
          _ = (Imo2016P2.col j).card / 3 := by rw [col_card]
      · intro s hsdiv
        by_cases hs : s + 2 ≤ 2 * n
        · have hd := hsum (s + 2) ⟨by omega, hs⟩
          have heq :
              Finset.filter (fun p : Fin n × Fin n => p.1.val + p.2.val + 2 = s + 2)
                  (Finset.univ.product Finset.univ) = Imo2016P2.diagSum s := by
            ext p
            simp [Imo2016P2.diagSum]
          have hmod : (Finset.filter (fun p : Fin n × Fin n =>
              p.1.val + p.2.val + 2 = s + 2)
              (Finset.univ.product Finset.univ)).card % 3 = 0 := by
            rw [heq]
            exact Nat.mod_eq_zero_of_dvd hsdiv
          specialize hd hmod
          rw [heq] at hd
          intro c
          fin_cases c <;> simp_all [Imo2016P2.Balanced]
        · have he : Imo2016P2.diagSum (n := n) s = ∅ := by
            ext p
            simp [Imo2016P2.diagSum]
            omega
          simp [Imo2016P2.Balanced, he]
      · intro d hddiv
        by_cases hrange : -(n - 1) ≤ d ∧ d ≤ n - 1
        · have hd := hdiff d hrange
          have heq :
              Finset.filter (fun p : Fin n × Fin n =>
                (p.1.val : ℤ) - (p.2.val : ℤ) = d)
                (Finset.univ.product Finset.univ) = Imo2016P2.diagDiff d := by
            ext p
            simp [Imo2016P2.diagDiff]
          have hmod : (Finset.filter (fun p : Fin n × Fin n =>
              (p.1.val : ℤ) - (p.2.val : ℤ) = d)
              (Finset.univ.product Finset.univ)).card % 3 = 0 := by
            rw [heq]
            exact Nat.mod_eq_zero_of_dvd hddiv
          specialize hd hmod
          rw [heq] at hd
          intro c
          fin_cases c <;> simp_all [Imo2016P2.Balanced]
        · have he : Imo2016P2.diagDiff (n := n) d = ∅ := by
            ext p
            simp [Imo2016P2.diagDiff]
            omega
          simp [Imo2016P2.Balanced, he]
    · rintro ⟨f, hrow, hcol, hsum, hdiff⟩
      refine ⟨f, ?_, ?_, ?_, ?_⟩
      · intro i
        have h := hrow i
        exact ⟨by calc
            _ = ((Imo2016P2.row i).filter (fun p => f p.1 p.2 = 0)).card := (row_filter_card f i 0).symm
            _ = (Imo2016P2.row i).card / 3 := h 0
            _ = n / 3 := by rw [row_card],
          by calc
            _ = ((Imo2016P2.row i).filter (fun p => f p.1 p.2 = 1)).card := (row_filter_card f i 1).symm
            _ = (Imo2016P2.row i).card / 3 := h 1
            _ = n / 3 := by rw [row_card],
          by calc
            _ = ((Imo2016P2.row i).filter (fun p => f p.1 p.2 = 2)).card := (row_filter_card f i 2).symm
            _ = (Imo2016P2.row i).card / 3 := h 2
            _ = n / 3 := by rw [row_card]⟩
      · intro j
        have h := hcol j
        exact ⟨by calc
            _ = ((Imo2016P2.col j).filter (fun p => f p.1 p.2 = 0)).card := (col_filter_card f j 0).symm
            _ = (Imo2016P2.col j).card / 3 := h 0
            _ = n / 3 := by rw [col_card],
          by calc
            _ = ((Imo2016P2.col j).filter (fun p => f p.1 p.2 = 1)).card := (col_filter_card f j 1).symm
            _ = (Imo2016P2.col j).card / 3 := h 1
            _ = n / 3 := by rw [col_card],
          by calc
            _ = ((Imo2016P2.col j).filter (fun p => f p.1 p.2 = 2)).card := (col_filter_card f j 2).symm
            _ = (Imo2016P2.col j).card / 3 := h 2
            _ = n / 3 := by rw [col_card]⟩
      · intro s hs
        dsimp
        intro hmod
        have heq :
            Finset.filter (fun p : Fin n × Fin n => p.1.val + p.2.val + 2 = s)
                (Finset.univ.product Finset.univ) = Imo2016P2.diagSum (s - 2) := by
          ext p
          simp [Imo2016P2.diagSum]
          omega
        have hdiv : 3 ∣ (Imo2016P2.diagSum (n := n) (s - 2)).card := by
          rw [← heq]
          exact Nat.dvd_of_mod_eq_zero hmod
        have h := hsum (s - 2) hdiv
        rw [← heq] at h
        exact ⟨h (0 : Fin 3), h (1 : Fin 3), h (2 : Fin 3)⟩
      · intro d hd
        dsimp
        intro hmod
        have heq :
            Finset.filter (fun p : Fin n × Fin n =>
              (p.1.val : ℤ) - (p.2.val : ℤ) = d)
              (Finset.univ.product Finset.univ) = Imo2016P2.diagDiff d := by
          ext p
          simp [Imo2016P2.diagDiff]
        have hdiv : 3 ∣ (Imo2016P2.diagDiff (n := n) d).card := by
          rw [← heq]
          exact Nat.dvd_of_mod_eq_zero hmod
        have h := hdiff d hdiv
        rw [← heq] at h
        exact ⟨h (0 : Fin 3), h (1 : Fin 3), h (2 : Fin 3)⟩
  constructor
  · intro hdiv
    exact bridge.mp ((problem_statement_assumed n).mpr hdiv hn)
  · intro hmod
    exact (problem_statement_assumed n).mp (fun _ => bridge.mpr hmod)

end Imo2016P2

