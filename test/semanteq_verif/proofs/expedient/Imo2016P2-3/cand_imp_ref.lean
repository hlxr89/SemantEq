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

deriving instance DecidableEq for Letter

instance : LawfulBEq Letter where
  rfl {a} := by cases a <;> rfl
  eq_of_beq {a b} h := by cases a <;> cases b <;> cases h <;> rfl

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

private def toCand (c : Fin 3) : Letter :=
  match c.1 with
  | 0 => Letter.I
  | 1 => Letter.M
  | _ => Letter.O

private def toRef : Letter → Fin 3
  | Letter.I => 0
  | Letter.M => 1
  | Letter.O => 2

private lemma toRef_toCand (c : Fin 3) : toRef (toCand c) = c := by
  fin_cases c <;> rfl

private lemma toCand_toRef (c : Letter) : toCand (toRef c) = c := by
  cases c <;> rfl

private lemma toCand_eq_iff (c : Fin 3) (a : Letter) :
    toCand c = a ↔ c = toRef a := by
  constructor
  · intro h
    rw [← h, toRef_toCand]
  · rintro rfl
    exact toCand_toRef a

private lemma count_map_filter_eq_card {α β : Type} [DecidableEq α] [BEq β]
    [LawfulBEq β] [DecidableEq β] (l : List α) (hl : l.Nodup)
    (p : α → Prop) [DecidablePred p] (g : α → β) (a : β) :
    ((l.filter p).map g).count a =
      (l.toFinset.filter fun x ↦ p x ∧ g x = a).card := by
  rw [List.count_eq_length_filter, List.filter_map, List.length_map]
  calc
    (List.filter ((fun x ↦ x == a) ∘ g) (List.filter (fun b ↦ decide (p b)) l)).length =
        (List.filter ((fun x ↦ x == a) ∘ g)
          (List.filter (fun b ↦ decide (p b)) l)).toFinset.card :=
      (List.toFinset_card_of_nodup ((hl.filter _).filter _)).symm
    _ = (l.toFinset.filter fun x ↦ p x ∧ g x = a).card := by
      congr 1
      ext x
      simp [and_comm]

private lemma length_filter_eq_card {α : Type} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (p : α → Prop) [DecidablePred p] :
    (l.filter p).length = (l.toFinset.filter fun x ↦ p x).card := by
  calc
    (l.filter p).length = (l.filter p).toFinset.card :=
      (List.toFinset_card_of_nodup (hl.filter _)).symm
    _ = (l.toFinset.filter fun x ↦ p x).card := by
      congr 1
      ext x
      simp

private def cellList (n : ℕ) : List (Fin n × Fin n) :=
  List.product (List.ofFn (fun i : Fin n => i)) (List.ofFn (fun j : Fin n => j))

private lemma cellList_nodup (n : ℕ) : (cellList n).Nodup := by
  exact (List.nodup_ofFn.mpr fun _ _ h ↦ h).product
    (List.nodup_ofFn.mpr fun _ _ h ↦ h)

private lemma cellList_toFinset (n : ℕ) : (cellList n).toFinset = Finset.univ := by
  apply Finset.eq_univ_of_forall
  rintro ⟨i, j⟩
  rw [List.mem_toFinset, cellList]
  apply List.mem_product.mpr
  exact ⟨List.mem_ofFn.mpr ⟨i, rfl⟩, List.mem_ofFn.mpr ⟨j, rfl⟩⟩

private lemma indexList_toFinset (n : ℕ) :
    (List.ofFn (fun i : Fin n ↦ i)).toFinset = Finset.univ := by
  apply Finset.eq_univ_of_forall
  intro i
  exact List.mem_toFinset.mpr (List.mem_ofFn.mpr ⟨i, rfl⟩)

private lemma test_row {n : ℕ} (f : Fin n → Fin n → Fin 3) (i : Fin n) (c : Fin 3) :
    (Finset.univ.filter fun j ↦ f i j = c).card =
      ((Imo2016P2.row i).filter fun p ↦ f p.1 p.2 = c).card := by
  apply Finset.card_bij' (fun j _ ↦ (i, j)) (fun p _ ↦ p.2)
  · simp [Imo2016P2.row]
  · intro p hp
    simp [Imo2016P2.row] at hp ⊢
    simpa [hp.1] using hp.2
  · simp
  · intro p hp
    simp [Imo2016P2.row] at hp
    exact Prod.ext hp.1.symm rfl

private lemma test_col {n : ℕ} (f : Fin n → Fin n → Fin 3) (j : Fin n) (c : Fin 3) :
    (Finset.univ.filter fun i ↦ f i j = c).card =
      ((Imo2016P2.col j).filter fun p ↦ f p.1 p.2 = c).card := by
  apply Finset.card_bij' (fun i _ ↦ (i, j)) (fun p _ ↦ p.1)
  · simp [Imo2016P2.col]
  · simp [Imo2016P2.col] at *
  · simp
  · intro p hp
    simp [Imo2016P2.col] at hp
    exact Prod.ext rfl hp.1.symm

private lemma ref_row_card {n : ℕ} (i : Fin n) :
    (Imo2016P2.row i).card = n := by
  have h := test_row (fun _ _ ↦ (0 : Fin 3)) i 0
  simpa using h.symm

private lemma ref_col_card {n : ℕ} (j : Fin n) :
    (Imo2016P2.col j).card = n := by
  have h := test_col (fun _ _ ↦ (0 : Fin 3)) j 0
  simpa using h.symm

private lemma row_count {n : ℕ} (f : Fin n → Fin n → Fin 3) (i : Fin n) (a : Letter) :
    countLetter (List.ofFn (fun j ↦ toCand (f i j))) a =
      ((Imo2016P2.row i).filter fun p ↦ f p.1 p.2 = toRef a).card := by
  rw [countLetter]
  have h := count_map_filter_eq_card
    (List.ofFn (fun j : Fin n ↦ j))
    (List.nodup_ofFn.mpr fun _ _ h ↦ h)
    (fun _ ↦ True) (fun j ↦ toCand (f i j)) a
  simp at h
  rw [indexList_toFinset] at h
  rw [show (List.ofFn fun j ↦ toCand (f i j)) =
      List.ofFn ((fun j ↦ toCand (f i j)) ∘ fun j ↦ j) by rfl, h, ← test_row]
  congr 1
  ext j
  simp [toCand_eq_iff]

private lemma col_count {n : ℕ} (f : Fin n → Fin n → Fin 3) (j : Fin n) (a : Letter) :
    countLetter (List.ofFn (fun i ↦ toCand (f i j))) a =
      ((Imo2016P2.col j).filter fun p ↦ f p.1 p.2 = toRef a).card := by
  rw [countLetter]
  have h := count_map_filter_eq_card
    (List.ofFn (fun i : Fin n ↦ i))
    (List.nodup_ofFn.mpr fun _ _ h ↦ h)
    (fun _ ↦ True) (fun i ↦ toCand (f i j)) a
  simp at h
  rw [indexList_toFinset] at h
  rw [show (List.ofFn fun i ↦ toCand (f i j)) =
      List.ofFn ((fun i ↦ toCand (f i j)) ∘ fun i ↦ i) by rfl, h, ← test_col]
  congr 1
  ext i
  simp [toCand_eq_iff]

private lemma diagonal_length {n : ℕ} (p : Fin n × Fin n → Prop) [DecidablePred p] :
    ((cellList n).filter p).length = (Finset.univ.filter p).card := by
  rw [length_filter_eq_card _ (cellList_nodup n), cellList_toFinset]

private lemma diagonal_count {n : ℕ} (f : Fin n → Fin n → Fin 3)
    (p : Fin n × Fin n → Prop) [DecidablePred p] (a : Letter) :
    (((cellList n).filter p).map fun q ↦ toCand (f q.1 q.2)).count a =
      ((Finset.univ.filter p).filter fun q ↦ f q.1 q.2 = toRef a).card := by
  rw [count_map_filter_eq_card _ (cellList_nodup n), cellList_toFinset]
  congr 1
  ext q
  simp [toCand_eq_iff]

private lemma diag1_length {n : ℕ} (f : Fin n → Fin n → Fin 3) (s : ℕ) :
    (diagType1 ⟨fun i j ↦ toCand (f i j)⟩ s).length =
      (Imo2016P2.diagSum (n := n) s).card := by
  simpa [diagType1, cellList, Imo2016P2.diagSum] using
    (diagonal_length (n := n) (fun q ↦ (q.1 : ℕ) + (q.2 : ℕ) = s))

private lemma diag2_length {n : ℕ} (f : Fin n → Fin n → Fin 3) (d : ℤ) :
    (diagType2 ⟨fun i j ↦ toCand (f i j)⟩ d).length =
      (Imo2016P2.diagDiff (n := n) d).card := by
  simpa [diagType2, cellList, Imo2016P2.diagDiff] using
    (diagonal_length (n := n)
      (fun q ↦ ((q.1 : ℕ) : ℤ) - ((q.2 : ℕ) : ℤ) = d))

private lemma diag1_count {n : ℕ} (f : Fin n → Fin n → Fin 3) (s : ℕ) (a : Letter) :
    countLetter (diagType1 ⟨fun i j ↦ toCand (f i j)⟩ s) a =
      ((Imo2016P2.diagSum (n := n) s).filter
        fun q ↦ f q.1 q.2 = toRef a).card := by
  rw [countLetter]
  simpa [diagType1, cellList, Imo2016P2.diagSum] using
    (diagonal_count f (fun q ↦ (q.1 : ℕ) + (q.2 : ℕ) = s) a)

private lemma diag2_count {n : ℕ} (f : Fin n → Fin n → Fin 3) (d : ℤ) (a : Letter) :
    countLetter (diagType2 ⟨fun i j ↦ toCand (f i j)⟩ d) a =
      ((Imo2016P2.diagDiff (n := n) d).filter
        fun q ↦ f q.1 q.2 = toRef a).card := by
  rw [countLetter]
  simpa [diagType2, cellList, Imo2016P2.diagDiff] using
    (diagonal_count f
      (fun q ↦ ((q.1 : ℕ) : ℤ) - ((q.2 : ℕ) : ℤ) = d) a)

private lemma conditions_iff {n : ℕ} (f : Fin n → Fin n → Fin 3) :
    allConditions ⟨fun i j ↦ toCand (f i j)⟩ ↔ Imo2016P2.MODTable f := by
  constructor
  · rintro ⟨hr, hc, hs, hd⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i c
      rcases hr i with ⟨hI, hM, hO⟩
      have h := row_count f i (toCand c)
      rw [toRef_toCand] at h
      rw [← h, ref_row_card]
      fin_cases c
      · simpa [row, toCand] using hI
      · simpa [row, toCand] using hM
      · simpa [row, toCand] using hO
    · intro j c
      rcases hc j with ⟨hI, hM, hO⟩
      have h := col_count f j (toCand c)
      rw [toRef_toCand] at h
      rw [← h, ref_col_card]
      fin_cases c
      · simpa [col, toCand] using hI
      · simpa [col, toCand] using hM
      · simpa [col, toCand] using hO
    · intro s hdiv c
      have hlen := diag1_length f s
      have hdist := hs s (by
        rw [hlen]
        exact Nat.mod_eq_zero_of_dvd hdiv)
      have hcount := diag1_count f s (toCand c)
      rw [toRef_toCand] at hcount
      rw [← hcount]
      rw [← hlen]
      fin_cases c
      · simpa [toCand] using hdist.1
      · simpa [toCand] using hdist.2.1
      · simpa [toCand] using hdist.2.2
    · intro d hdiv c
      have hlen := diag2_length f d
      have hdist := hd d (by
        rw [hlen]
        exact Nat.mod_eq_zero_of_dvd hdiv)
      have hcount := diag2_count f d (toCand c)
      rw [toRef_toCand] at hcount
      rw [← hcount]
      rw [← hlen]
      fin_cases c
      · simpa [toCand] using hdist.1
      · simpa [toCand] using hdist.2.1
      · simpa [toCand] using hdist.2.2
  · rintro ⟨hr, hc, hs, hd⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      refine ⟨?_, ?_, ?_⟩
      · change countLetter (List.ofFn fun j ↦ toCand (f i j)) Letter.I = n / 3
        rw [row_count]
        simpa only [ref_row_card] using hr i (toRef Letter.I)
      · change countLetter (List.ofFn fun j ↦ toCand (f i j)) Letter.M = n / 3
        rw [row_count]
        simpa only [ref_row_card] using hr i (toRef Letter.M)
      · change countLetter (List.ofFn fun j ↦ toCand (f i j)) Letter.O = n / 3
        rw [row_count]
        simpa only [ref_row_card] using hr i (toRef Letter.O)
    · intro j
      refine ⟨?_, ?_, ?_⟩
      · change countLetter (List.ofFn fun i ↦ toCand (f i j)) Letter.I = n / 3
        rw [col_count]
        simpa only [ref_col_card] using hc j (toRef Letter.I)
      · change countLetter (List.ofFn fun i ↦ toCand (f i j)) Letter.M = n / 3
        rw [col_count]
        simpa only [ref_col_card] using hc j (toRef Letter.M)
      · change countLetter (List.ofFn fun i ↦ toCand (f i j)) Letter.O = n / 3
        rw [col_count]
        simpa only [ref_col_card] using hc j (toRef Letter.O)
    · intro s
      rw [diagCondition]
      intro hmod
      have hlen := diag1_length f s
      have hdist := hs s (by
        rw [← hlen]
        exact Nat.dvd_of_mod_eq_zero hmod)
      refine ⟨?_, ?_, ?_⟩
      · rw [diag1_count, hlen]
        simpa using hdist (toRef Letter.I)
      · rw [diag1_count, hlen]
        simpa using hdist (toRef Letter.M)
      · rw [diag1_count, hlen]
        simpa using hdist (toRef Letter.O)
    · intro d
      rw [diagCondition]
      intro hmod
      have hlen := diag2_length f d
      have hdist := hd d (by
        rw [← hlen]
        exact Nat.dvd_of_mod_eq_zero hmod)
      refine ⟨?_, ?_, ?_⟩
      · rw [diag2_count, hlen]
        simpa using hdist (toRef Letter.I)
      · rw [diag2_count, hlen]
        simpa using hdist (toRef Letter.M)
      · rw [diag2_count, hlen]
        simpa using hdist (toRef Letter.O)

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  (∃ (t : Table n), allConditions t) ↔ (9 ∣ n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
namespace Imo2016P2

theorem imo2016_p2 (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  constructor
  · intro hdiv
    obtain ⟨t, ht⟩ := problem_statement_assumed.mpr hdiv
    let f : Fin n → Fin n → Fin 3 := fun i j ↦ toRef (t.cells i j)
    refine ⟨f, (conditions_iff f).mp ?_⟩
    simpa [f, toCand_toRef] using ht
  · rintro ⟨f, hf⟩
    exact problem_statement_assumed.mp
      ⟨⟨fun i j ↦ toCand (f i j)⟩, (conditions_iff f).mpr hf⟩

end Imo2016P2
