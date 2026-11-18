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

-- Define the alphabet of letters
inductive Letter : Type
| I : Letter
| M : Letter
| O : Letter
deriving BEq

-- Helper function to count occurrences of a letter in a list
def countLetter (l : List Letter) (letter : Letter) : ℕ :=
  l.count letter

-- A table is represented as a function from (Fin n) × (Fin n) to Letter
structure Table (n : ℕ) where
  cells : Fin n → Fin n → Letter

-- Get the row i of a table
def row (t : Table n) (i : Fin n) : Fin n → Letter :=
  fun j => t.cells i j

-- Get the column j of a table
def col (t : Table n) (j : Fin n) : Fin n → Letter :=
  fun i => t.cells i j

-- Check if a table satisfies the row condition (each row has 1/3 of each letter)
def rowCondition (t : Table n) : Prop :=
  ∀ i : Fin n,
    countLetter (List.ofFn (row t i)) Letter.I = n / 3 ∧
    countLetter (List.ofFn (row t i)) Letter.M = n / 3 ∧
    countLetter (List.ofFn (row t i)) Letter.O = n / 3

-- Check if a table satisfies the column condition (each column has 1/3 of each letter)
def colCondition (t : Table n) : Prop :=
  ∀ j : Fin n,
    countLetter (List.ofFn (col t j)) Letter.I = n / 3 ∧
    countLetter (List.ofFn (col t j)) Letter.M = n / 3 ∧
    countLetter (List.ofFn (col t j)) Letter.O = n / 3

-- First type diagonals: cells (i, j) where i + j = constant
def diagType1 (t : Table n) (s : ℕ) : List Letter :=
  List.filter (fun p : Fin n × Fin n => (p.1 : ℕ) + (p.2 : ℕ) = s)
    (List.product (List.ofFn (fun i : Fin n => i)) (List.ofFn (fun j : Fin n => j)))
    |>.map (fun p => t.cells p.1 p.2)

-- Second type diagonals: cells (i, j) where i - j = constant
def diagType2 (t : Table n) (d : ℤ) : List Letter :=
  List.filter (fun p : Fin n × Fin n => (p.1 : ℤ) - (p.2 : ℤ) = d)
    (List.product (List.ofFn (fun i : Fin n => i)) (List.ofFn (fun j : Fin n => j)))
    |>.map (fun p => t.cells p.1 p.2)

-- Check if a diagonal has the right distribution
def diagCondition (l : List Letter) : Prop :=
  l.length % 3 = 0 →
    countLetter l Letter.I = l.length / 3 ∧
    countLetter l Letter.M = l.length / 3 ∧
    countLetter l Letter.O = l.length / 3

-- The main condition: all rows, columns, and diagonals satisfy the distribution
def allConditions (t : Table n) : Prop :=
  rowCondition t ∧ colCondition t ∧
  (∀ s : ℕ, diagCondition (diagType1 t s)) ∧
  (∀ d : ℤ, diagCondition (diagType2 t d))

def letterEquiv : Letter ≃ Imo2016P2.Letter where
  toFun
    | Letter.I => 0
    | Letter.M => 1
    | Letter.O => 2
  invFun c := Fin.cases Letter.I (Fin.cases Letter.M (fun _ => Letter.O)) c
  left_inv x := by cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

theorem count_ofFn_eq (f : Fin n → Letter) (a : Letter) :
    countLetter (List.ofFn f) a = (Finset.univ.filter (fun i => f i == a)).card := by
  rw [countLetter, List.count_eq_length_filter]
  conv_lhs =>
    rw [List.ofFn_eq_map]
  rw [List.filter_map, List.length_map]
  rw [← List.toFinset_card_of_nodup]
  · rw [List.toFinset_filter]
    have hid : (List.finRange n).toFinset = Finset.univ := by
      ext i
      simp
    rw [hid]
    rfl
  · exact (List.nodup_ofFn.mpr fun _ _ h => h).filter _

theorem test_row_count (t : Table n) (i : Fin n) (a : Letter) :
    countLetter (List.ofFn (row t i)) a =
      ((Imo2016P2.row i).filter (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv a)).card := by
  have hbeq (x y : Letter) : (x == y) = true ↔ x = y := by
    cases x <;> cases y <;> constructor <;> intro h
    all_goals first | rfl | cases h
  rw [count_ofFn_eq]
  refine Finset.card_bij (fun j _ => (i, j)) ?_ ?_ ?_
  · intro j hj
    have hj' : (t.cells i j == a) = true := by simpa [row] using hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Imo2016P2.row]
    exact congrArg letterEquiv ((hbeq _ _).mp hj')
  · intro j₁ hj₁ j₂ hj₂ h
    exact congrArg Prod.snd h
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Imo2016P2.row] at hp
    refine ⟨p.2, ?_, ?_⟩
    · simpa [row, hp.1] using (hbeq _ _).mpr (letterEquiv.injective hp.2)
    exact Prod.ext hp.1.symm rfl

theorem test_diag_len (t : Table n) (s : ℕ) :
    (diagType1 t s).length = (Imo2016P2.diagSum (n := n) s).card := by
  have hfilter (p : Fin n × Fin n → Bool) :
      (List.filter p ((List.finRange n).product (List.finRange n))).length =
        (Finset.univ.filter (fun x => p x)).card := by
    have hbase : ((List.finRange n).product (List.finRange n)).toFinset = Finset.univ := by
      ext x
      rcases x with ⟨a, b⟩
      simp [List.mem_product]
    rw [← List.toFinset_card_of_nodup]
    · rw [List.toFinset_filter]
      rw [hbase]
    · exact ((List.nodup_finRange n).product (List.nodup_finRange n)).filter _
  simp only [diagType1, List.length_map, List.ofFn_eq_map, Imo2016P2.diagSum]
  simp only [show (fun i : Fin n => i) = id by rfl, List.map_id_fun, id_eq]
  rw [hfilter]
  congr 1
  ext p
  simp

theorem test_count_map [DecidableEq α] (l : List α) (hl : l.Nodup) (f : α → Letter) (a : Letter) :
    countLetter (l.map f) a =
      (l.toFinset.filter (fun x => letterEquiv (f x) = letterEquiv a)).card := by
  have hbeq (x y : Letter) : (x == y) = true ↔ x = y := by
    cases x <;> cases y <;> constructor <;> intro h
    all_goals first | rfl | cases h
  rw [countLetter, List.count_eq_length_filter, List.filter_map, List.length_map]
  rw [← List.toFinset_card_of_nodup (hl.filter _), List.toFinset_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, List.mem_toFinset, Function.comp_apply]
  rw [hbeq]
  apply and_congr_right
  intro _
  constructor
  · exact fun h => congrArg letterEquiv h
  · exact fun h => letterEquiv.injective h

theorem test_diag_count (t : Table n) (s : ℕ) (a : Letter) :
    countLetter (diagType1 t s) a =
      ((Imo2016P2.diagSum (n := n) s).filter
        (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv a)).card := by
  unfold diagType1
  rw [test_count_map]
  · apply congrArg Finset.card
    ext p
    rcases p with ⟨i, j⟩
    simp [Imo2016P2.diagSum]
  · exact ((List.nodup_ofFn.mpr fun _ _ h => h).product
      (List.nodup_ofFn.mpr fun _ _ h => h)).filter _

theorem test_col_count (t : Table n) (j : Fin n) (a : Letter) :
    countLetter (List.ofFn (col t j)) a =
      ((Imo2016P2.col j).filter (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv a)).card := by
  have hbeq (x y : Letter) : (x == y) = true ↔ x = y := by
    cases x <;> cases y <;> constructor <;> intro h
    all_goals first | rfl | cases h
  rw [count_ofFn_eq]
  refine Finset.card_bij (fun i _ => (i, j)) ?_ ?_ ?_
  · intro i hi
    have hi' : (t.cells i j == a) = true := by simpa [col] using hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Imo2016P2.col]
    exact congrArg letterEquiv ((hbeq _ _).mp hi')
  · intro i₁ hi₁ i₂ hi₂ h
    exact congrArg Prod.fst h
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Imo2016P2.col] at hp
    refine ⟨p.1, ?_, ?_⟩
    · simpa [col, hp.1] using (hbeq _ _).mpr (letterEquiv.injective hp.2)
    exact Prod.ext rfl hp.1.symm

theorem test_diag2_len (t : Table n) (d : ℤ) :
    (diagType2 t d).length = (Imo2016P2.diagDiff (n := n) d).card := by
  have hfilter (p : Fin n × Fin n → Bool) :
      (List.filter p ((List.finRange n).product (List.finRange n))).length =
        (Finset.univ.filter (fun x => p x)).card := by
    have hbase : ((List.finRange n).product (List.finRange n)).toFinset = Finset.univ := by
      ext x
      rcases x with ⟨a, b⟩
      simp
    rw [← List.toFinset_card_of_nodup]
    · rw [List.toFinset_filter, hbase]
    · exact ((List.nodup_finRange n).product (List.nodup_finRange n)).filter _
  simp only [diagType2, List.length_map, List.ofFn_eq_map, Imo2016P2.diagDiff]
  simp only [show (fun i : Fin n => i) = id by rfl, List.map_id_fun, id_eq]
  rw [hfilter]
  congr 1
  ext p
  simp

theorem test_diag2_count (t : Table n) (d : ℤ) (a : Letter) :
    countLetter (diagType2 t d) a =
      ((Imo2016P2.diagDiff (n := n) d).filter
        (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv a)).card := by
  unfold diagType2
  rw [test_count_map]
  · apply congrArg Finset.card
    ext p
    rcases p with ⟨i, j⟩
    simp [Imo2016P2.diagDiff]
  · exact ((List.nodup_ofFn.mpr fun _ _ h => h).product
      (List.nodup_ofFn.mpr fun _ _ h => h)).filter _

theorem test_bridge (t : Table n) :
    allConditions t ↔ Imo2016P2.MODTable (fun i j => letterEquiv (t.cells i j)) := by
  have hrowcard (r : Fin n) : (Imo2016P2.row r).card = n := by
    have h : (Finset.univ : Finset (Fin n)).card = (Imo2016P2.row r).card := by
      refine Finset.card_bij (fun j _ => (r, j)) ?_ ?_ ?_
      · simp [Imo2016P2.row]
      · intro a ha b hb hab
        exact congrArg Prod.snd hab
      · intro p hp
        simp only [Imo2016P2.row, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact ⟨p.2, by simp [Imo2016P2.row], Prod.ext hp.symm rfl⟩
    exact h.symm.trans (Finset.card_fin n)
  have hcolcard (c : Fin n) : (Imo2016P2.col c).card = n := by
    have h : (Finset.univ : Finset (Fin n)).card = (Imo2016P2.col c).card := by
      refine Finset.card_bij (fun i _ => (i, c)) ?_ ?_ ?_
      · simp [Imo2016P2.col]
      · intro a ha b hb hab
        exact congrArg Prod.fst hab
      · intro p hp
        simp only [Imo2016P2.col, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact ⟨p.1, by simp [Imo2016P2.col], Prod.ext rfl hp.symm⟩
    exact h.symm.trans (Finset.card_fin n)
  rw [allConditions, rowCondition, colCondition, Imo2016P2.MODTable]
  constructor
  · rintro ⟨hr, hc, hs, hd⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r
      rw [Imo2016P2.Balanced]
      intro c
      fin_cases c
      · change ((Imo2016P2.row r).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.I)).card = _
        rw [← test_row_count t r Letter.I, hrowcard]
        exact (hr r).1
      · change ((Imo2016P2.row r).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.M)).card = _
        rw [← test_row_count t r Letter.M, hrowcard]
        exact (hr r).2.1
      · change ((Imo2016P2.row r).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.O)).card = _
        rw [← test_row_count t r Letter.O, hrowcard]
        exact (hr r).2.2
    · intro c
      rw [Imo2016P2.Balanced]
      intro x
      fin_cases x
      · change ((Imo2016P2.col c).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.I)).card = _
        rw [← test_col_count t c Letter.I, hcolcard]
        exact (hc c).1
      · change ((Imo2016P2.col c).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.M)).card = _
        rw [← test_col_count t c Letter.M, hcolcard]
        exact (hc c).2.1
      · change ((Imo2016P2.col c).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.O)).card = _
        rw [← test_col_count t c Letter.O, hcolcard]
        exact (hc c).2.2
    · intro s hdiv
      rw [Imo2016P2.Balanced]
      have hm : (diagType1 t s).length % 3 = 0 := by
        rw [test_diag_len]
        exact Nat.dvd_iff_mod_eq_zero.mp hdiv
      have h := hs s hm
      intro c
      fin_cases c
      · change ((Imo2016P2.diagSum s).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.I)).card = _
        rw [← test_diag_count t s Letter.I, ← test_diag_len]
        exact h.1
      · change ((Imo2016P2.diagSum s).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.M)).card = _
        rw [← test_diag_count t s Letter.M, ← test_diag_len]
        exact h.2.1
      · change ((Imo2016P2.diagSum s).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.O)).card = _
        rw [← test_diag_count t s Letter.O, ← test_diag_len]
        exact h.2.2
    · intro d hdiv
      rw [Imo2016P2.Balanced]
      have hm : (diagType2 t d).length % 3 = 0 := by
        rw [test_diag2_len]
        exact Nat.dvd_iff_mod_eq_zero.mp hdiv
      have h := hd d hm
      intro c
      fin_cases c
      · change ((Imo2016P2.diagDiff d).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.I)).card = _
        rw [← test_diag2_count t d Letter.I, ← test_diag2_len]
        exact h.1
      · change ((Imo2016P2.diagDiff d).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.M)).card = _
        rw [← test_diag2_count t d Letter.M, ← test_diag2_len]
        exact h.2.1
      · change ((Imo2016P2.diagDiff d).filter
          (fun p => letterEquiv (t.cells p.1 p.2) = letterEquiv Letter.O)).card = _
        rw [← test_diag2_count t d Letter.O, ← test_diag2_len]
        exact h.2.2
  · rintro ⟨hr, hc, hs, hd⟩
    simp only [Imo2016P2.Balanced] at hr hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r
      refine ⟨?_, ?_, ?_⟩
      · rw [test_row_count]
        simpa [hrowcard] using hr r (letterEquiv Letter.I)
      · rw [test_row_count]
        simpa [hrowcard] using hr r (letterEquiv Letter.M)
      · rw [test_row_count]
        simpa [hrowcard] using hr r (letterEquiv Letter.O)
    · intro c
      refine ⟨?_, ?_, ?_⟩
      · rw [test_col_count]
        simpa [hcolcard] using hc c (letterEquiv Letter.I)
      · rw [test_col_count]
        simpa [hcolcard] using hc c (letterEquiv Letter.M)
      · rw [test_col_count]
        simpa [hcolcard] using hc c (letterEquiv Letter.O)
    · intro s hm
      have hdiv : 3 ∣ (Imo2016P2.diagSum (n := n) s).card := by
        rw [Nat.dvd_iff_mod_eq_zero, ← test_diag_len]
        exact hm
      have h := hs s hdiv
      rw [Imo2016P2.Balanced] at h
      refine ⟨?_, ?_, ?_⟩
      · rw [test_diag_count, test_diag_len]
        exact h (letterEquiv Letter.I)
      · rw [test_diag_count, test_diag_len]
        exact h (letterEquiv Letter.M)
      · rw [test_diag_count, test_diag_len]
        exact h (letterEquiv Letter.O)
    · intro d hm
      have hdiv : 3 ∣ (Imo2016P2.diagDiff (n := n) d).card := by
        rw [Nat.dvd_iff_mod_eq_zero, ← test_diag2_len]
        exact hm
      have h := hd d hdiv
      rw [Imo2016P2.Balanced] at h
      refine ⟨?_, ?_, ?_⟩
      · rw [test_diag2_count, test_diag2_len]
        exact h (letterEquiv Letter.I)
      · rw [test_diag2_count, test_diag2_len]
        exact h (letterEquiv Letter.M)
      · rw [test_diag2_count, test_diag2_len]
        exact h (letterEquiv Letter.O)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  (∃ (t : Table n), allConditions t) ↔ (9 ∣ n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
namespace Imo2016P2
theorem imo2016_p2 (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  constructor
  · intro hnine
    obtain ⟨t, ht⟩ := problem_statement_assumed.mpr hnine
    exact ⟨fun i j => letterEquiv (t.cells i j), (test_bridge t).mp ht⟩
  · rintro ⟨f, hf⟩
    let t : Table n := ⟨fun i j => letterEquiv.symm (f i j)⟩
    apply problem_statement_assumed.mp
    refine ⟨t, (test_bridge t).mpr ?_⟩
    simpa [t] using hf
end Imo2016P2

