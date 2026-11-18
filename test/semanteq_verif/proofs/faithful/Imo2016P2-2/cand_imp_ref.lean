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
theorem imo2016_p2 (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  classical
  have bridge :
      (∃ table : Fin n → Fin n → Fin 3,
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
            (diagonal.filter (fun p => table p.1 p.2 = 2)).card = diagonal.card / 3))
        ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
    have row_card (f : Fin n → Fin n → Fin 3) (i : Fin n) (c : Fin 3) :
        ((row i).filter (fun p => f p.1 p.2 = c)).card =
          (Finset.univ.filter (fun j => f i j = c)).card := by
      apply Finset.card_bij (fun p _ => p.2)
      · intro a ha
        simp [row] at ha ⊢
        aesop
      · intro a ha b hb hab
        simp [row] at ha hb
        apply Prod.ext <;> simp_all
      · intro j hj
        refine ⟨(i, j), ?_, rfl⟩
        simpa [row] using hj
    have row_total (i : Fin n) : (row i).card = n := by
      calc
        (row i).card = (Finset.univ : Finset (Fin n)).card := by
          apply Finset.card_bij (fun p _ => p.2)
          · simp
          · intro a ha b hb hab
            simp [row] at ha hb
            apply Prod.ext <;> simp_all
          · intro j hj
            exact ⟨(i, j), by simp [row], rfl⟩
        _ = n := Finset.card_fin n
    have col_card (f : Fin n → Fin n → Fin 3) (j : Fin n) (c : Fin 3) :
        ((col j).filter (fun p => f p.1 p.2 = c)).card =
          (Finset.univ.filter (fun i => f i j = c)).card := by
      apply Finset.card_bij (fun p _ => p.1)
      · intro a ha
        simp [col] at ha ⊢
        aesop
      · intro a ha b hb hab
        simp [col] at ha hb
        apply Prod.ext <;> simp_all
      · intro i hi
        refine ⟨(i, j), ?_, rfl⟩
        simpa [col] using hi
    have col_total (j : Fin n) : (col j).card = n := by
      calc
        (col j).card = (Finset.univ : Finset (Fin n)).card := by
          apply Finset.card_bij (fun p _ => p.1)
          · simp
          · intro a ha b hb hab
            simp [col] at ha hb
            apply Prod.ext <;> simp_all
          · intro i hi
            exact ⟨(i, j), by simp [col], rfl⟩
        _ = n := Finset.card_fin n
    constructor
    · rintro ⟨f, hrow, hcol, hsum, hdiff⟩
      refine ⟨f, ?_, ?_, ?_, ?_⟩
      · intro i c
        rw [row_card, row_total]
        fin_cases c
        · exact (hrow i).1
        · exact (hrow i).2.1
        · exact (hrow i).2.2
      · intro j c
        rw [col_card, col_total]
        fin_cases c
        · exact (hcol j).1
        · exact (hcol j).2.1
        · exact (hcol j).2.2
      · intro s hdiv c
        by_cases hrange : s + 2 ≤ 2 * n
        · have heq : diagSum (n := n) s =
              Finset.filter (fun p : Fin n × Fin n => p.1.val + p.2.val + 2 = s + 2)
                (Finset.univ.product Finset.univ) := by
            ext p
            simp [diagSum]
          have h := hsum (s + 2) ⟨by omega, hrange⟩
          rw [heq]
          have hc := h (by simpa [heq, Nat.dvd_iff_mod_eq_zero] using hdiv)
          fin_cases c
          · exact hc.1
          · exact hc.2.1
          · exact hc.2.2
        · have hempty : diagSum (n := n) s = ∅ := by
            ext p
            simp [diagSum]
            omega
          simp [hempty]
      · intro d hdiv c
        by_cases hrange : (-((n : ℤ) - 1) ≤ d ∧ d ≤ (n : ℤ) - 1)
        · have heq : diagDiff (n := n) d =
              Finset.filter (fun p : Fin n × Fin n => (p.1.val : ℤ) - (p.2.val : ℤ) = d)
                (Finset.univ.product Finset.univ) := by
            ext p
            simp [diagDiff]
          rw [heq]
          have hc := hdiff d hrange (by simpa [heq, Nat.dvd_iff_mod_eq_zero] using hdiv)
          fin_cases c
          · exact hc.1
          · exact hc.2.1
          · exact hc.2.2
        · have hempty : diagDiff (n := n) d = ∅ := by
            ext p
            simp [diagDiff]
            omega
          simp [hempty]
    · rintro ⟨f, hrow, hcol, hsum, hdiff⟩
      refine ⟨f, ?_, ?_, ?_, ?_⟩
      · intro i
        have h := hrow i
        unfold Balanced at h
        have h0 := h 0
        have h1 := h 1
        have h2 := h 2
        rw [row_card, row_total] at h0 h1 h2
        exact ⟨h0, h1, h2⟩
      · intro j
        have h := hcol j
        unfold Balanced at h
        have h0 := h 0
        have h1 := h 1
        have h2 := h 2
        rw [col_card, col_total] at h0 h1 h2
        exact ⟨h0, h1, h2⟩
      · intro s hs
        dsimp
        have heq :
            Finset.filter (fun p : Fin n × Fin n => p.1.val + p.2.val + 2 = s)
                Finset.univ = diagSum (n := n) (s - 2) := by
          ext p
          simp [diagSum]
          omega
        rw [heq]
        intro hmod
        have h := hsum (s - 2) (by simpa [Nat.dvd_iff_mod_eq_zero] using hmod)
        exact ⟨h 0, h 1, h 2⟩
      · intro d hd
        dsimp
        have heq :
            Finset.filter (fun p : Fin n × Fin n => (p.1.val : ℤ) - (p.2.val : ℤ) = d)
                Finset.univ = diagDiff (n := n) d := by
          ext p
          simp [diagDiff]
        rw [heq]
        intro hmod
        have h := hdiff d (by simpa [Nat.dvd_iff_mod_eq_zero] using hmod)
        exact ⟨h 0, h 1, h 2⟩
  constructor
  · intro hdiv
    exact bridge.mp (((problem_statement_assumed n).mpr hdiv) hn)
  · intro hf
    exact (problem_statement_assumed n).mp (fun _ => bridge.mpr hf)

end Imo2016P2

