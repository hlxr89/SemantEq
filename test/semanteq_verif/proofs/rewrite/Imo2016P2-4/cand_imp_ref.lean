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
  have row_color_card (table : Fin n → Fin n → Fin 3) (r : Fin n) (c : Fin 3) :
      ((row r).filter (fun p => table p.1 p.2 = c)).card =
        (Finset.univ.filter (fun j => table r j = c)).card := by
    apply Finset.card_bij' (fun p _ => p.2) (fun j _ => (r, j))
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, row, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨ha, hc⟩
      subst a
      exact hc
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, row, Finset.mem_univ, true_and] at hp
      rcases hp with ⟨ha, hc⟩
      exact Prod.ext ha.symm rfl
    · intro j hj
      rfl
    · intro j hj
      simpa [row] using hj
  have row_card (r : Fin n) : (row r).card = n := by
    have h : (row r).card = (Finset.univ : Finset (Fin n)).card := by
      apply Finset.card_bij' (fun p _ => p.2) (fun j _ => (r, j))
      all_goals simp [row]
    simpa using h
  have col_color_card (table : Fin n → Fin n → Fin 3) (k : Fin n) (c : Fin 3) :
      ((col k).filter (fun p => table p.1 p.2 = c)).card =
        (Finset.univ.filter (fun i => table i k = c)).card := by
    apply Finset.card_bij' (fun p _ => p.1) (fun i _ => (i, k))
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, col, Finset.mem_univ, true_and] at hp ⊢
      rcases hp with ⟨hb, hc⟩
      subst b
      exact hc
    · rintro ⟨a, b⟩ hp
      simp only [Finset.mem_filter, col, Finset.mem_univ, true_and] at hp
      rcases hp with ⟨hb, hc⟩
      exact Prod.ext rfl hb.symm
    · intro i hi
      rfl
    · intro i hi
      simpa [col] using hi
  have col_card (k : Fin n) : (col k).card = n := by
    have h : (col k).card = (Finset.univ : Finset (Fin n)).card := by
      apply Finset.card_bij' (fun p _ => p.1) (fun i _ => (i, k))
      all_goals simp [col]
    simpa using h
  have sum_diag_eq (s : ℕ) :
      Finset.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = (s : ℤ)) Finset.univ =
        diagSum (n := n) s := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, diagSum]
    norm_cast
  constructor
  · intro hdiv
    have hcand := (problem_statement_assumed n).mpr hdiv
    rcases hcand hn with ⟨table, hrow, hcol, hsum, hdiff⟩
    refine ⟨table, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r c
      fin_cases c
      · rw [row_color_card, row_card]
        exact (hrow r).1
      · rw [row_color_card, row_card]
        exact (hrow r).2.1
      · rw [row_color_card, row_card]
        exact (hrow r).2.2
    · intro k c
      fin_cases c
      · rw [col_color_card, col_card]
        exact (hcol k).1
      · rw [col_color_card, col_card]
        exact (hcol k).2.1
      · rw [col_color_card, col_card]
        exact (hcol k).2.2
    · intro s hs c
      have h := hsum (s : ℤ)
      rw [if_pos] at h
      · fin_cases c
        · rw [sum_diag_eq] at h
          exact h.1
        · rw [sum_diag_eq] at h
          exact h.2.1
        · rw [sum_diag_eq] at h
          exact h.2.2
      · rw [sum_diag_eq]
        exact hs
    · intro d hd c
      have h := hdiff d
      rw [if_pos] at h
      · fin_cases c
        · simpa [diagDiff] using h.1
        · simpa [diagDiff] using h.2.1
        · simpa [diagDiff] using h.2.2
      · simpa [diagDiff] using hd
  · rintro ⟨table, hrow, hcol, hsum, hdiff⟩
    apply (problem_statement_assumed n).mp
    intro _
    refine ⟨table, ?_⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r
      refine ⟨?_, ?_, ?_⟩
      · have hb := hrow r (0 : Fin 3)
        rw [row_color_card, row_card] at hb
        exact hb
      · have hb := hrow r (1 : Fin 3)
        rw [row_color_card, row_card] at hb
        exact hb
      · have hb := hrow r (2 : Fin 3)
        rw [row_color_card, row_card] at hb
        exact hb
    · intro k
      refine ⟨?_, ?_, ?_⟩
      · have hb := hcol k (0 : Fin 3)
        rw [col_color_card, col_card] at hb
        exact hb
      · have hb := hcol k (1 : Fin 3)
        rw [col_color_card, col_card] at hb
        exact hb
      · have hb := hcol k (2 : Fin 3)
        rw [col_color_card, col_card] at hb
        exact hb
    · intro k
      dsimp only
      by_cases hk : 0 ≤ k
      · have hdiag :
            Finset.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = k) Finset.univ =
              diagSum (n := n) k.toNat := by
          simpa only [Int.toNat_of_nonneg hk] using sum_diag_eq k.toNat
        rw [hdiag]
        by_cases hd : 3 ∣ (diagSum (n := n) k.toNat).card
        · rw [if_pos hd]
          refine ⟨?_, ?_, ?_⟩
          · exact hsum k.toNat hd (0 : Fin 3)
          · exact hsum k.toNat hd (1 : Fin 3)
          · exact hsum k.toNat hd (2 : Fin 3)
        · rw [if_neg hd]
          trivial
      · have hk' : k < 0 := lt_of_not_ge hk
        have hdiag :
            Finset.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = k) Finset.univ = ∅ := by
          ext p
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · intro hp
            exact ((not_le_of_gt hk') (hp ▸ Int.natCast_nonneg _)).elim
          · intro hp
            simpa using hp
        rw [hdiag]
        simp only [Finset.card_empty, dvd_zero, if_pos, Finset.filter_empty, Nat.zero_div]
        exact ⟨trivial, trivial, trivial⟩
    · intro d
      dsimp only
      by_cases hd : 3 ∣ (diagDiff (n := n) d).card
      · rw [if_pos]
        · refine ⟨?_, ?_, ?_⟩
          · exact hdiff d hd (0 : Fin 3)
          · exact hdiff d hd (1 : Fin 3)
          · exact hdiff d hd (2 : Fin 3)
        · simpa [diagDiff] using hd
      · rw [if_neg]
        · trivial
        · simpa [diagDiff] using hd

end Imo2016P2
