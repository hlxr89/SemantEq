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
theorem imo2016_p2_assumed (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  sorry

end Imo2016P2

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement : 
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
  intro n
  have bridge : (∃ (table : Fin n → Fin n → Fin 3), 
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
      else True)) ↔
      ∃ f : Fin n → Fin n → Imo2016P2.Letter, Imo2016P2.MODTable f := by
    have row_card (table : Fin n → Fin n → Fin 3) (i : Fin n) (c : Fin 3) :
        ((Imo2016P2.row i).filter (fun p => table p.1 p.2 = c)).card =
          (Finset.univ.filter (fun j => table i j = c)).card := by
      apply Finset.card_bij (fun p _ => p.2)
      all_goals simp [Imo2016P2.row] at * <;> aesop
    have row_size (i : Fin n) : (Imo2016P2.row i).card = n := by
      simpa using row_card (fun _ _ => (0 : Fin 3)) i 0
    have col_card (table : Fin n → Fin n → Fin 3) (j : Fin n) (c : Fin 3) :
        ((Imo2016P2.col j).filter (fun p => table p.1 p.2 = c)).card =
          (Finset.univ.filter (fun i => table i j = c)).card := by
      apply Finset.card_bij (fun p _ => p.1)
      all_goals simp [Imo2016P2.col] at * <;> aesop
    have col_size (j : Fin n) : (Imo2016P2.col j).card = n := by
      simpa using col_card (fun _ _ => (0 : Fin 3)) j 0
    have diagSum_eq (s : ℕ) : Imo2016P2.diagSum (n := n) s =
        Finset.filter
          (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = (s : ℤ))
          (Finset.univ : Finset (Fin n × Fin n)) := by
      ext p
      simp [Imo2016P2.diagSum]
      norm_cast
    constructor
    · rintro ⟨table, hrow, hcol, hsum, hdiff⟩
      refine ⟨table, ?_⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro i c
        fin_cases c
        · exact (row_card table i 0).trans ((hrow i).1.trans (congrArg (· / 3) (row_size i).symm))
        · exact (row_card table i 1).trans ((hrow i).2.1.trans (congrArg (· / 3) (row_size i).symm))
        · exact (row_card table i 2).trans ((hrow i).2.2.trans (congrArg (· / 3) (row_size i).symm))
      · intro j c
        fin_cases c
        · exact (col_card table j 0).trans ((hcol j).1.trans (congrArg (· / 3) (col_size j).symm))
        · exact (col_card table j 1).trans ((hcol j).2.1.trans (congrArg (· / 3) (col_size j).symm))
        · exact (col_card table j 2).trans ((hcol j).2.2.trans (congrArg (· / 3) (col_size j).symm))
      · intro s hs c
        have h := hsum (s : ℤ)
        have hdiv : 3 ∣ (Finset.filter
            (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = (s : ℤ))
            (Finset.univ : Finset (Fin n × Fin n))).card := by
          rw [← diagSum_eq]
          exact hs
        simp [hdiv] at h
        rw [diagSum_eq]
        fin_cases c
        · exact h.1
        · exact h.2.1
        · exact h.2.2
      · intro d hd c
        have h := hdiff d
        have hdiv : 3 ∣ (Finset.filter
            (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d)
            (Finset.univ : Finset (Fin n × Fin n))).card := by
          simpa [Imo2016P2.diagDiff] using hd
        simp [hdiv] at h
        fin_cases c
        · exact h.1
        · exact h.2.1
        · exact h.2.2
    · rintro ⟨table, hrow, hcol, hsum, hdiff⟩
      refine ⟨table, ?_, ?_, ?_, ?_⟩
      · intro i
        exact ⟨(row_card table i 0).symm.trans ((hrow i 0).trans (congrArg (· / 3) (row_size i))),
          (row_card table i 1).symm.trans ((hrow i 1).trans (congrArg (· / 3) (row_size i))),
          (row_card table i 2).symm.trans ((hrow i 2).trans (congrArg (· / 3) (row_size i)))⟩
      · intro j
        exact ⟨(col_card table j 0).symm.trans ((hcol j 0).trans (congrArg (· / 3) (col_size j))),
          (col_card table j 1).symm.trans ((hcol j 1).trans (congrArg (· / 3) (col_size j))),
          (col_card table j 2).symm.trans ((hcol j 2).trans (congrArg (· / 3) (col_size j)))⟩
      · intro k
        dsimp
        by_cases hk0 : 0 ≤ k
        · have hk_cast : (k.toNat : ℤ) = k := Int.toNat_of_nonneg hk0
          rw [← hk_cast]
          split_ifs with hk
          · rw [← diagSum_eq] at hk ⊢
            exact ⟨hsum k.toNat hk 0, hsum k.toNat hk 1, hsum k.toNat hk 2⟩
        · have hempty : Finset.filter
              (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = k)
              (Finset.univ : Finset (Fin n × Fin n)) = ∅ := by
            ext p
            simp
            omega
          rw [hempty]
          simp
      · intro k
        dsimp
        split_ifs with hk
        · exact ⟨by simpa [Imo2016P2.diagDiff] using hdiff k hk 0,
            by simpa [Imo2016P2.diagDiff] using hdiff k hk 1,
            by simpa [Imo2016P2.diagDiff] using hdiff k hk 2⟩
  constructor
  · intro h
    by_cases hn : 0 < n
    · exact (Imo2016P2.imo2016_p2_assumed n hn).2 (bridge.mp (h hn))
    · have : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp
  · intro hn hpos
    exact bridge.mpr ((Imo2016P2.imo2016_p2_assumed n hpos).1 hn)
