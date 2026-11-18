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
    (∃ (f : Fin n → Fin n → Fin 3), 
      (∀ i : Fin n, 
        (Finset.univ.filter (fun j => f i j = 0)).card = n / 3 ∧
        (Finset.univ.filter (fun j => f i j = 1)).card = n / 3 ∧
        (Finset.univ.filter (fun j => f i j = 2)).card = n / 3) ∧
      (∀ j : Fin n, 
        (Finset.univ.filter (fun i => f i j = 0)).card = n / 3 ∧
        (Finset.univ.filter (fun i => f i j = 1)).card = n / 3 ∧
        (Finset.univ.filter (fun i => f i j = 2)).card = n / 3) ∧
      (∀ s : ℤ, 
        (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s)).card % 3 = 0 →
        (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = 0)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s)).card / 3 ∧
        (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = 1)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s)).card / 3 ∧
        (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = 2)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s)).card / 3) ∧
      (∀ d : ℤ, 
        (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d)).card % 3 = 0 →
        (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d ∧ f p.1 p.2 = 0)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d)).card / 3 ∧
        (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d ∧ f p.1 p.2 = 1)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d)).card / 3 ∧
        (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d ∧ f p.1 p.2 = 2)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d)).card / 3)
    ) ↔ 9 ∣ n := by
  sorry


-- ===== goal statement, PROVED from the antecedent =====
namespace Imo2016P2

theorem imo2016_p2 (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by

  have row_size (i : Fin n) : (Imo2016P2.row i).card = n := by
    calc
      (Imo2016P2.row i).card = (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_bij (fun p _ => p.2)
        · simp
        · intro a ha b hb hab
          simp [Imo2016P2.row] at ha hb
          exact Prod.ext (ha.trans hb.symm) hab
        · intro j hj
          exact ⟨(i, j), by simp [Imo2016P2.row], rfl⟩
      _ = n := by simp
  have col_size (j : Fin n) : (Imo2016P2.col j).card = n := by
    calc
      (Imo2016P2.col j).card = (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_bij (fun p _ => p.1)
        · simp
        · intro a ha b hb hab
          simp [Imo2016P2.col] at ha hb
          exact Prod.ext hab (ha.trans hb.symm)
        · intro i hi
          exact ⟨(i, j), by simp [Imo2016P2.col], rfl⟩
      _ = n := by simp
  have row_card (f : Fin n → Fin n → Fin 3) (i : Fin n) (c : Fin 3) :
      ((Imo2016P2.row i).filter (fun p => f p.1 p.2 = c)).card =
        (Finset.univ.filter (fun j => f i j = c)).card := by
    apply Finset.card_bij (fun p _ => p.2)
    · rintro ⟨a, b⟩ ha
      simp [Imo2016P2.row] at ha ⊢
      simpa [ha.1] using ha.2
    · intro a ha b hb hab
      simp [Imo2016P2.row] at ha hb
      exact Prod.ext (ha.1.trans hb.1.symm) hab
    · intro j hj
      refine ⟨(i, j), ?_, rfl⟩
      simp [Imo2016P2.row]
      simpa using hj
  have col_card (f : Fin n → Fin n → Fin 3) (j : Fin n) (c : Fin 3) :
      ((Imo2016P2.col j).filter (fun p => f p.1 p.2 = c)).card =
        (Finset.univ.filter (fun i => f i j = c)).card := by
    apply Finset.card_bij (fun p _ => p.1)
    · rintro ⟨a, b⟩ ha
      simp [Imo2016P2.col] at ha ⊢
      simpa [ha.1] using ha.2
    · intro a ha b hb hab
      simp [Imo2016P2.col] at ha hb
      exact Prod.ext hab (ha.1.trans hb.1.symm)
    · intro i hi
      refine ⟨(i, j), ?_, rfl⟩
      simp [Imo2016P2.col]
      simpa using hi
  have sum_base (s : ℕ) :
      (Imo2016P2.diagSum (n := n) s).card =
        (Finset.univ.filter (fun p : Fin n × Fin n =>
          (p.1.val + p.2.val : ℤ) = (s : ℤ))).card := by
    apply congrArg Finset.card
    ext p
    simp only [Imo2016P2.diagSum, Finset.mem_filter, Finset.mem_univ, true_and]
    norm_cast
  have sum_card (f : Fin n → Fin n → Fin 3) (s : ℕ) (c : Fin 3) :
      ((Imo2016P2.diagSum (n := n) s).filter
        (fun p : Fin n × Fin n => f p.1 p.2 = c)).card =
        (Finset.univ.filter (fun p : Fin n × Fin n =>
          (p.1.val + p.2.val : ℤ) = (s : ℤ) ∧ f p.1 p.2 = c)).card := by
    apply congrArg Finset.card
    ext p
    simp only [Imo2016P2.diagSum, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h, hc⟩
      norm_cast at h ⊢
    · rintro ⟨h, hc⟩
      norm_cast at h ⊢
  have diff_base (d : ℤ) :
      (Imo2016P2.diagDiff (n := n) d).card =
        (Finset.univ.filter (fun p : Fin n × Fin n =>
          (p.1.val - p.2.val : ℤ) = d)).card := by
    apply congrArg Finset.card
    ext p
    simp only [Imo2016P2.diagDiff, Finset.mem_filter, Finset.mem_univ, true_and]
  have diff_card (f : Fin n → Fin n → Fin 3) (d : ℤ) (c : Fin 3) :
      ((Imo2016P2.diagDiff (n := n) d).filter
        (fun p : Fin n × Fin n => f p.1 p.2 = c)).card =
        (Finset.univ.filter (fun p : Fin n × Fin n =>
          (p.1.val - p.2.val : ℤ) = d ∧ f p.1 p.2 = c)).card := by
    apply congrArg Finset.card
    ext p
    simp only [Imo2016P2.diagDiff, Finset.mem_filter, Finset.mem_univ, true_and]
  apply Iff.intro
  · intro h9
    have hcand := (problem_statement_assumed n).mpr h9 hn
    rcases hcand with ⟨f, hrow, hcol, hsum, hdiff⟩
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · intro i c
      rw [row_card, row_size]
      fin_cases c
      · exact (hrow i).1
      · exact (hrow i).2.1
      · exact (hrow i).2.2
    · intro j c
      rw [col_card, col_size]
      fin_cases c
      · exact (hcol j).1
      · exact (hcol j).2.1
      · exact (hcol j).2.2
    · intro s hs c
      have hs' : (Finset.univ.filter (fun p : Fin n × Fin n =>
          (p.1.val + p.2.val : ℤ) = (s : ℤ))).card % 3 = 0 := by
        rw [← sum_base]
        exact Nat.dvd_iff_mod_eq_zero.mp hs
      have hbal := hsum (s : ℤ) hs'
      rw [sum_card, sum_base]
      fin_cases c
      · exact hbal.1
      · exact hbal.2.1
      · exact hbal.2.2
    · intro d hd c
      have hd' : (Finset.univ.filter (fun p : Fin n × Fin n =>
          (p.1.val - p.2.val : ℤ) = d)).card % 3 = 0 := by
        rw [← diff_base]
        exact Nat.dvd_iff_mod_eq_zero.mp hd
      have hbal := hdiff d hd'
      rw [diff_card, diff_base]
      fin_cases c
      · exact hbal.1
      · exact hbal.2.1
      · exact hbal.2.2
  · rintro ⟨f, hrow, hcol, hsum, hdiff⟩
    apply (problem_statement_assumed n).mp
    intro _
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · intro i
      constructor
      · calc
          _ = ((Imo2016P2.row i).filter (fun p => f p.1 p.2 = 0)).card :=
            (row_card f i 0).symm
          _ = (Imo2016P2.row i).card / 3 := hrow i 0
          _ = n / 3 := congrArg (fun x => x / 3) (row_size i)
      constructor
      · calc
          _ = ((Imo2016P2.row i).filter (fun p => f p.1 p.2 = 1)).card :=
            (row_card f i 1).symm
          _ = (Imo2016P2.row i).card / 3 := hrow i 1
          _ = n / 3 := congrArg (fun x => x / 3) (row_size i)
      · calc
          _ = ((Imo2016P2.row i).filter (fun p => f p.1 p.2 = 2)).card :=
            (row_card f i 2).symm
          _ = (Imo2016P2.row i).card / 3 := hrow i 2
          _ = n / 3 := congrArg (fun x => x / 3) (row_size i)
    · intro j
      constructor
      · calc
          _ = ((Imo2016P2.col j).filter (fun p => f p.1 p.2 = 0)).card :=
            (col_card f j 0).symm
          _ = (Imo2016P2.col j).card / 3 := hcol j 0
          _ = n / 3 := congrArg (fun x => x / 3) (col_size j)
      constructor
      · calc
          _ = ((Imo2016P2.col j).filter (fun p => f p.1 p.2 = 1)).card :=
            (col_card f j 1).symm
          _ = (Imo2016P2.col j).card / 3 := hcol j 1
          _ = n / 3 := congrArg (fun x => x / 3) (col_size j)
      · calc
          _ = ((Imo2016P2.col j).filter (fun p => f p.1 p.2 = 2)).card :=
            (col_card f j 2).symm
          _ = (Imo2016P2.col j).card / 3 := hcol j 2
          _ = n / 3 := congrArg (fun x => x / 3) (col_size j)
    · intro s hs
      by_cases hs0 : 0 ≤ s
      · have hst : (s.toNat : ℤ) = s := Int.toNat_of_nonneg hs0
        have hcard : 3 ∣ (Imo2016P2.diagSum (n := n) s.toNat).card := by
          rw [Nat.dvd_iff_mod_eq_zero, sum_base, hst]
          exact hs
        have h := hsum s.toNat hcard
        constructor
        · rw [← hst, ← sum_card, ← sum_base]
          exact h 0
        constructor
        · rw [← hst, ← sum_card, ← sum_base]
          exact h 1
        · rw [← hst, ← sum_card, ← sum_base]
          exact h 2
      · have hempty : (Finset.univ.filter (fun p : Fin n × Fin n =>
            (p.1.val + p.2.val : ℤ) = s)) = ∅ := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hp
            have hp0 : 0 ≤ (p.1.val + p.2.val : ℤ) := by positivity
            omega
          · intro hp
            simpa using hp
        have hempty_c (c : Fin 3) : (Finset.univ.filter (fun p : Fin n × Fin n =>
            (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = c)) = ∅ := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hp, -⟩
            have hp0 : 0 ≤ (p.1.val + p.2.val : ℤ) := by positivity
            omega
          · intro hp
            simpa using hp
        rw [hempty, hempty_c 0, hempty_c 1, hempty_c 2]
        simp
    · intro d hd
      have hcard : 3 ∣ (Imo2016P2.diagDiff (n := n) d).card := by
        rw [Nat.dvd_iff_mod_eq_zero, diff_base]
        exact hd
      have h := hdiff d hcard
      constructor
      · rw [← diff_card, ← diff_base]
        exact h 0
      constructor
      · rw [← diff_card, ← diff_base]
        exact h 1
      · rw [← diff_card, ← diff_base]
        exact h 2


end Imo2016P2

