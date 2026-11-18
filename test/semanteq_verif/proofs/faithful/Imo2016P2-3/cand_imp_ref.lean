import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- The reference definitions remain in their original namespace; the candidate definitions are global.

namespace Imo2016P2
abbrev Letter := Fin 3
variable {n : ℕ}
def Balanced (f : Fin n → Fin n → Letter) (cells : Finset (Fin n × Fin n)) : Prop :=
  ∀ c : Letter, (cells.filter (fun p ↦ f p.1 p.2 = c)).card = cells.card / 3
def row (r : Fin n) : Finset (Fin n × Fin n) := Finset.univ.filter (fun p ↦ p.1 = r)
def col (k : Fin n) : Finset (Fin n × Fin n) := Finset.univ.filter (fun p ↦ p.2 = k)
def diagSum (s : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p ↦ (p.1 : ℕ) + (p.2 : ℕ) = s)
def diagDiff (d : ℤ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p ↦ ((p.1 : ℕ) : ℤ) - ((p.2 : ℕ) : ℤ) = d)
def MODTable (f : Fin n → Fin n → Letter) : Prop :=
  (∀ r : Fin n, Balanced f (row r)) ∧
  (∀ k : Fin n, Balanced f (col k)) ∧
  (∀ s : ℕ, 3 ∣ (diagSum (n := n) s).card → Balanced f (diagSum s)) ∧
  (∀ d : ℤ, 3 ∣ (diagDiff (n := n) d).card → Balanced f (diagDiff d))
abbrev solution : Set ℕ := { n | 9 ∣ n }
end Imo2016P2

inductive Letter : Type | I | M | O deriving BEq
def countLetter (l : List Letter) (letter : Letter) : ℕ := l.count letter
structure Table (n : ℕ) where cells : Fin n → Fin n → Letter
def row (t : Table n) (i : Fin n) : Fin n → Letter := fun j => t.cells i j
def col (t : Table n) (j : Fin n) : Fin n → Letter := fun i => t.cells i j
def rowCondition (t : Table n) : Prop :=
  ∀ i : Fin n, countLetter (List.ofFn (row t i)) Letter.I = n / 3 ∧
    countLetter (List.ofFn (row t i)) Letter.M = n / 3 ∧
    countLetter (List.ofFn (row t i)) Letter.O = n / 3
def colCondition (t : Table n) : Prop :=
  ∀ j : Fin n, countLetter (List.ofFn (col t j)) Letter.I = n / 3 ∧
    countLetter (List.ofFn (col t j)) Letter.M = n / 3 ∧
    countLetter (List.ofFn (col t j)) Letter.O = n / 3
def diagType1 (t : Table n) (s : ℕ) : List Letter :=
  List.filter (fun p : Fin n × Fin n => (p.1 : ℕ) + (p.2 : ℕ) = s)
    (List.product (List.ofFn (fun i : Fin n => i)) (List.ofFn (fun j : Fin n => j)))
    |>.map (fun p => t.cells p.1 p.2)
def diagType2 (t : Table n) (d : ℤ) : List Letter :=
  List.filter (fun p : Fin n × Fin n => (p.1 : ℤ) - (p.2 : ℤ) = d)
    (List.product (List.ofFn (fun i : Fin n => i)) (List.ofFn (fun j : Fin n => j)))
    |>.map (fun p => t.cells p.1 p.2)
def diagCondition (l : List Letter) : Prop := l.length % 3 = 0 →
  countLetter l Letter.I = l.length / 3 ∧ countLetter l Letter.M = l.length / 3 ∧
  countLetter l Letter.O = l.length / 3
def allConditions (t : Table n) : Prop := rowCondition t ∧ colCondition t ∧
  (∀ s : ℕ, diagCondition (diagType1 t s)) ∧ (∀ d : ℤ, diagCondition (diagType2 t d))

def enc : Letter → Fin 3
  | .I => 0 | .M => 1 | .O => 2
def dec (c : Fin 3) : Letter := if c = 0 then .I else if c = 1 then .M else .O

theorem dec_I (c : Fin 3) : (dec c == Letter.I) = true ↔ c = 0 := by
  fin_cases c <;> decide
theorem enc_I (c : Letter) : (c == Letter.I) = true ↔ enc c = 0 := by
  cases c <;> decide
theorem dec_M (c : Fin 3) : (dec c == Letter.M) = true ↔ c = 1 := by
  fin_cases c <;> decide
theorem dec_O (c : Fin 3) : (dec c == Letter.O) = true ↔ c = 2 := by
  fin_cases c <;> decide
theorem enc_M (c : Letter) : (c == Letter.M) = true ↔ enc c = 1 := by
  cases c <;> decide
theorem enc_O (c : Letter) : (c == Letter.O) = true ↔ enc c = 2 := by
  cases c <;> decide


theorem card_filter_ofFn (p : Fin n → Prop) [DecidablePred p] :
    ((List.ofFn fun i : Fin n => i).filter fun i => decide (p i)).length =
      (Finset.univ.filter p).card := by
  classical
  have hn : (List.ofFn fun i : Fin n => i).Nodup :=
    List.nodup_ofFn.mpr Function.injective_id
  rw [← List.toFinset_card_of_nodup (hn.filter _), List.toFinset_filter]
  congr 1
  ext i
  simp [List.mem_ofFn]

theorem card_filter_pairs (p : Fin n × Fin n → Prop) [DecidablePred p] :
    (((List.ofFn fun i : Fin n => i).product (List.ofFn fun j : Fin n => j)).filter
      fun x => decide (p x)).length = (Finset.univ.filter p).card := by
  classical
  have hone : (List.ofFn fun i : Fin n => i).Nodup :=
    List.nodup_ofFn.mpr Function.injective_id
  have hn : ((List.ofFn fun i : Fin n => i).product
      (List.ofFn fun j : Fin n => j)).Nodup := hone.product hone
  rw [← List.toFinset_card_of_nodup (hn.filter _), List.toFinset_filter]
  congr 1
  ext x
  rcases x with ⟨i, j⟩
  simp [List.mem_ofFn]

theorem count_ofFn (g : Fin n → Letter) (a : Letter) :
    countLetter (List.ofFn g) a =
      (Finset.univ.filter fun x => (g x == a) = true).card := by
  have hmap : List.ofFn g = (List.ofFn fun i : Fin n => i).map g := by
    apply List.ext_get
    · simp
    · intro k h₁ h₂
      simp
  rw [hmap, countLetter, List.count_eq_length_filter]
  have hfilter (l : List (Fin n)) :
      (List.filter (fun x => x == a) (l.map g)).length =
        (l.filter fun x => g x == a).length := by
    induction l with
    | nil => simp
    | cons x xs ih => cases h : g x == a <;> simp [h, ih]
  rw [hfilter]
  simpa using (card_filter_ofFn (fun x => (g x == a) = true))

theorem card_row (i : Fin n) (q : Fin n → Prop) [DecidablePred q] :
    (Finset.univ.filter q).card =
      ((Imo2016P2.row i).filter fun p => q p.2).card := by
  apply Finset.card_bij (fun j _ => (i, j))
  · intro j hj
    simp [Imo2016P2.row]
    exact (Finset.mem_filter.mp hj).2
  · intro a₁ h₁ a₂ h₂ h
    exact congrArg Prod.snd h
  · intro p hp
    simp [Imo2016P2.row] at hp
    exact ⟨p.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩,
      Prod.ext hp.1.symm rfl⟩

theorem card_col (j : Fin n) (q : Fin n → Prop) [DecidablePred q] :
    (Finset.univ.filter q).card =
      ((Imo2016P2.col j).filter fun p => q p.1).card := by
  apply Finset.card_bij (fun i _ => (i, j))
  · intro i hi
    simp [Imo2016P2.col]
    exact (Finset.mem_filter.mp hi).2
  · intro a₁ h₁ a₂ h₂ h
    exact congrArg Prod.fst h
  · intro p hp
    simp [Imo2016P2.col] at hp
    exact ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.2⟩,
      Prod.ext rfl hp.1.symm⟩

theorem row_card (i : Fin n) : (Imo2016P2.row i).card = n := by
  simpa using (card_row i (fun _ => True)).symm

theorem col_card (j : Fin n) : (Imo2016P2.col j).card = n := by
  simpa using (card_col j (fun _ => True)).symm

theorem count_row_dec (f : Fin n → Fin n → Fin 3) (i : Fin n)
    (a : Letter) (c : Fin 3)
    (h : ∀ x, (dec x == a) = true ↔ x = c) :
    countLetter (List.ofFn fun j => dec (f i j)) a =
      ((Imo2016P2.row i).filter fun p => f p.1 p.2 = c).card := by
  rw [count_ofFn, card_row i]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, Imo2016P2.row, true_and]
  constructor <;> rintro ⟨hp, hc⟩
  · exact ⟨hp, hp ▸ (h _).mp hc⟩
  · exact ⟨hp, (h _).mpr (hp.symm ▸ hc)⟩

theorem count_col_dec (f : Fin n → Fin n → Fin 3) (j : Fin n)
    (a : Letter) (c : Fin 3)
    (h : ∀ x, (dec x == a) = true ↔ x = c) :
    countLetter (List.ofFn fun i => dec (f i j)) a =
      ((Imo2016P2.col j).filter fun p => f p.1 p.2 = c).card := by
  rw [count_ofFn, card_col j]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, Imo2016P2.col, true_and]
  constructor <;> rintro ⟨hp, hc⟩
  · exact ⟨hp, hp ▸ (h _).mp hc⟩
  · exact ⟨hp, (h _).mpr (hp.symm ▸ hc)⟩

theorem count_map_filter_pairs_pre (g : Fin n × Fin n → Letter) (a : Letter)
    (p : Fin n × Fin n → Prop) [DecidablePred p] :
    countLetter ((((List.ofFn fun i : Fin n => i).product
      (List.ofFn fun j : Fin n => j)).filter fun x => decide (p x)).map g) a =
      (Finset.univ.filter fun x => p x ∧ (g x == a) = true).card := by
  classical
  rw [countLetter, List.count_eq_length_filter]
  have hfilter (l : List (Fin n × Fin n)) :
      (List.filter (fun x => x == a) (l.map g)).length =
        (l.filter fun x => g x == a).length := by
    induction l with
    | nil => simp
    | cons x xs ih => cases h : g x == a <;> simp [h, ih]
  rw [hfilter, List.filter_filter]
  simpa [Bool.and_comm] using
    (card_filter_pairs (fun x => p x ∧ (g x == a) = true))

theorem count_diag1 (g : Fin n → Fin n → Letter) (s : ℕ) (a : Letter) :
    countLetter (diagType1 ⟨g⟩ s) a =
      ((Imo2016P2.diagSum s).filter fun p => (g p.1 p.2 == a) = true).card := by
  simp only [diagType1]
  rw [count_map_filter_pairs_pre]
  simp [Imo2016P2.diagSum, Finset.filter_filter]

theorem count_diag2 (g : Fin n → Fin n → Letter) (d : ℤ) (a : Letter) :
    countLetter (diagType2 ⟨g⟩ d) a =
      ((Imo2016P2.diagDiff d).filter fun p => (g p.1 p.2 == a) = true).card := by
  simp only [diagType2]
  rw [count_map_filter_pairs_pre]
  simp [Imo2016P2.diagDiff, Finset.filter_filter]

theorem len_diag1 (t : Table n) (s : ℕ) :
    (diagType1 t s).length = (Imo2016P2.diagSum (n := n) s).card := by
  simp only [diagType1, List.length_map]
  apply card_filter_pairs

theorem len_diag2 (t : Table n) (d : ℤ) :
    (diagType2 t d).length = (Imo2016P2.diagDiff (n := n) d).card := by
  simp only [diagType2, List.length_map]
  apply card_filter_pairs

theorem count_row_g (g : Fin n → Fin n → Letter) (i : Fin n) (a : Letter)
    (q : Fin n → Fin n → Prop) [∀ i j, Decidable (q i j)]
    (h : ∀ i j, (g i j == a) = true ↔ q i j) :
    countLetter (List.ofFn fun j => g i j) a =
      ((Imo2016P2.row i).filter fun p => q p.1 p.2).card := by
  rw [count_ofFn, card_row i]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, Imo2016P2.row, true_and]
  constructor <;> rintro ⟨hp, hc⟩
  · exact ⟨hp, hp ▸ (h _ _).mp hc⟩
  · exact ⟨hp, (h _ _).mpr (hp.symm ▸ hc)⟩

theorem count_col_g (g : Fin n → Fin n → Letter) (j : Fin n) (a : Letter)
    (q : Fin n → Fin n → Prop) [∀ i j, Decidable (q i j)]
    (h : ∀ i j, (g i j == a) = true ↔ q i j) :
    countLetter (List.ofFn fun i => g i j) a =
      ((Imo2016P2.col j).filter fun p => q p.1 p.2).card := by
  rw [count_ofFn, card_col j]
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, Imo2016P2.col, true_and]
  constructor <;> rintro ⟨hp, hc⟩
  · exact ⟨hp, hp ▸ (h _ _).mp hc⟩
  · exact ⟨hp, (h _ _).mpr (hp.symm ▸ hc)⟩

theorem count_diag1_g (g : Fin n → Fin n → Letter) (s : ℕ) (a : Letter)
    (q : Fin n → Fin n → Prop) [∀ i j, Decidable (q i j)]
    (h : ∀ i j, (g i j == a) = true ↔ q i j) :
    countLetter (diagType1 ⟨g⟩ s) a =
      ((Imo2016P2.diagSum s).filter fun p => q p.1 p.2).card := by
  rw [count_diag1]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => h _ _

theorem count_diag2_g (g : Fin n → Fin n → Letter) (d : ℤ) (a : Letter)
    (q : Fin n → Fin n → Prop) [∀ i j, Decidable (q i j)]
    (h : ∀ i j, (g i j == a) = true ↔ q i j) :
    countLetter (diagType2 ⟨g⟩ d) a =
      ((Imo2016P2.diagDiff d).filter fun p => q p.1 p.2).card := by
  rw [count_diag2]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact and_congr_right fun _ => h _ _

theorem count_map_filter_pairs (g : Fin n × Fin n → Letter) (a : Letter)
    (p : Fin n × Fin n → Prop) [DecidablePred p] :
    countLetter ((((List.ofFn fun i : Fin n => i).product
      (List.ofFn fun j : Fin n => j)).filter fun x => decide (p x)).map g) a =
      (Finset.univ.filter fun x => p x ∧ (g x == a) = true).card := by
  classical
  rw [countLetter, List.count_eq_length_filter]
  have hfilter (l : List (Fin n × Fin n)) :
      (List.filter (fun x => x == a) (l.map g)).length =
        (l.filter fun x => g x == a).length := by
    induction l with
    | nil => simp
    | cons x xs ih => cases h : g x == a <;> simp [h, ih]
  rw [hfilter]
  rw [List.filter_filter]
  simpa [Bool.and_comm] using
    (card_filter_pairs (fun x => p x ∧ (g x == a) = true))


theorem exists_bridge :
    (∃ (t : Table n), allConditions t) ↔
      ∃ f : Fin n → Fin n → Imo2016P2.Letter, Imo2016P2.MODTable f := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨fun i j => enc (t.cells i j), ?_⟩
    rcases ht with ⟨hr, hc, hs, hd⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i c
      fin_cases c
      · change ((Imo2016P2.row i).filter fun p => enc (t.cells p.1 p.2) = 0).card = _
        rw [← count_row_g t.cells i Letter.I (fun i j => enc (t.cells i j) = 0)
          (fun i j => enc_I (t.cells i j))]
        simpa [row, row_card] using (hr i).1
      · change ((Imo2016P2.row i).filter fun p => enc (t.cells p.1 p.2) = 1).card = _
        rw [← count_row_g t.cells i Letter.M (fun i j => enc (t.cells i j) = 1)
          (fun i j => enc_M (t.cells i j))]
        simpa [row, row_card] using (hr i).2.1
      · change ((Imo2016P2.row i).filter fun p => enc (t.cells p.1 p.2) = 2).card = _
        rw [← count_row_g t.cells i Letter.O (fun i j => enc (t.cells i j) = 2)
          (fun i j => enc_O (t.cells i j))]
        simpa [row, row_card] using (hr i).2.2
    · intro j c
      fin_cases c
      · change ((Imo2016P2.col j).filter fun p => enc (t.cells p.1 p.2) = 0).card = _
        rw [← count_col_g t.cells j Letter.I (fun i j => enc (t.cells i j) = 0)
          (fun i j => enc_I (t.cells i j))]
        simpa [col, col_card] using (hc j).1
      · change ((Imo2016P2.col j).filter fun p => enc (t.cells p.1 p.2) = 1).card = _
        rw [← count_col_g t.cells j Letter.M (fun i j => enc (t.cells i j) = 1)
          (fun i j => enc_M (t.cells i j))]
        simpa [col, col_card] using (hc j).2.1
      · change ((Imo2016P2.col j).filter fun p => enc (t.cells p.1 p.2) = 2).card = _
        rw [← count_col_g t.cells j Letter.O (fun i j => enc (t.cells i j) = 2)
          (fun i j => enc_O (t.cells i j))]
        simpa [col, col_card] using (hc j).2.2
    · intro s hdiv c
      have hdiv' : 3 ∣ (diagType1 t s).length := by rwa [len_diag1 t s]
      have hs' := hs s (Nat.dvd_iff_mod_eq_zero.mp hdiv')
      fin_cases c
      · exact (count_diag1_g t.cells s Letter.I (fun i j => enc (t.cells i j) = 0)
          (fun i j => enc_I (t.cells i j))).symm.trans
          (hs'.1.trans (congrArg (fun x => x / 3) (len_diag1 t s)))
      · exact (count_diag1_g t.cells s Letter.M (fun i j => enc (t.cells i j) = 1)
          (fun i j => enc_M (t.cells i j))).symm.trans
          (hs'.2.1.trans (congrArg (fun x => x / 3) (len_diag1 t s)))
      · exact (count_diag1_g t.cells s Letter.O (fun i j => enc (t.cells i j) = 2)
          (fun i j => enc_O (t.cells i j))).symm.trans
          (hs'.2.2.trans (congrArg (fun x => x / 3) (len_diag1 t s)))
    · intro d hdiv c
      have hdiv' : 3 ∣ (diagType2 t d).length := by rwa [len_diag2 t d]
      have hd' := hd d (Nat.dvd_iff_mod_eq_zero.mp hdiv')
      fin_cases c
      · exact (count_diag2_g t.cells d Letter.I (fun i j => enc (t.cells i j) = 0)
          (fun i j => enc_I (t.cells i j))).symm.trans
          (hd'.1.trans (congrArg (fun x => x / 3) (len_diag2 t d)))
      · exact (count_diag2_g t.cells d Letter.M (fun i j => enc (t.cells i j) = 1)
          (fun i j => enc_M (t.cells i j))).symm.trans
          (hd'.2.1.trans (congrArg (fun x => x / 3) (len_diag2 t d)))
      · exact (count_diag2_g t.cells d Letter.O (fun i j => enc (t.cells i j) = 2)
          (fun i j => enc_O (t.cells i j))).symm.trans
          (hd'.2.2.trans (congrArg (fun x => x / 3) (len_diag2 t d)))
  · rintro ⟨f, hf⟩
    refine ⟨⟨fun i j => dec (f i j)⟩, ?_⟩
    rcases hf with ⟨hr, hc, hs, hd⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      exact ⟨(count_row_g (fun i j => dec (f i j)) i Letter.I (fun i j => f i j = 0)
          (fun i j => dec_I (f i j))).trans (by simpa [row_card] using hr i 0),
        (count_row_g (fun i j => dec (f i j)) i Letter.M (fun i j => f i j = 1)
          (fun i j => dec_M (f i j))).trans (by simpa [row_card] using hr i 1),
        (count_row_g (fun i j => dec (f i j)) i Letter.O (fun i j => f i j = 2)
          (fun i j => dec_O (f i j))).trans (by simpa [row_card] using hr i 2)⟩
    · intro j
      exact ⟨(count_col_g (fun i j => dec (f i j)) j Letter.I (fun i j => f i j = 0)
          (fun i j => dec_I (f i j))).trans (by simpa [col_card] using hc j 0),
        (count_col_g (fun i j => dec (f i j)) j Letter.M (fun i j => f i j = 1)
          (fun i j => dec_M (f i j))).trans (by simpa [col_card] using hc j 1),
        (count_col_g (fun i j => dec (f i j)) j Letter.O (fun i j => f i j = 2)
          (fun i j => dec_O (f i j))).trans (by simpa [col_card] using hc j 2)⟩
    · intro s hmod
      have hdiv : 3 ∣ (Imo2016P2.diagSum (n := n) s).card := by
        rw [← len_diag1 ⟨fun i j => dec (f i j)⟩ s]
        exact Nat.dvd_iff_mod_eq_zero.mpr hmod
      have hb := hs s hdiv
      exact ⟨(count_diag1_g (fun i j => dec (f i j)) s Letter.I (fun i j => f i j = 0)
          (fun i j => dec_I (f i j))).trans
          ((hb 0).trans (congrArg (fun x => x / 3) (len_diag1 ⟨fun i j => dec (f i j)⟩ s).symm)),
        (count_diag1_g (fun i j => dec (f i j)) s Letter.M (fun i j => f i j = 1)
          (fun i j => dec_M (f i j))).trans
          ((hb 1).trans (congrArg (fun x => x / 3) (len_diag1 ⟨fun i j => dec (f i j)⟩ s).symm)),
        (count_diag1_g (fun i j => dec (f i j)) s Letter.O (fun i j => f i j = 2)
          (fun i j => dec_O (f i j))).trans
          ((hb 2).trans (congrArg (fun x => x / 3) (len_diag1 ⟨fun i j => dec (f i j)⟩ s).symm))⟩
    · intro d hmod
      have hdiv : 3 ∣ (Imo2016P2.diagDiff (n := n) d).card := by
        rw [← len_diag2 ⟨fun i j => dec (f i j)⟩ d]
        exact Nat.dvd_iff_mod_eq_zero.mpr hmod
      have hb := hd d hdiv
      exact ⟨(count_diag2_g (fun i j => dec (f i j)) d Letter.I (fun i j => f i j = 0)
          (fun i j => dec_I (f i j))).trans
          ((hb 0).trans (congrArg (fun x => x / 3) (len_diag2 ⟨fun i j => dec (f i j)⟩ d).symm)),
        (count_diag2_g (fun i j => dec (f i j)) d Letter.M (fun i j => f i j = 1)
          (fun i j => dec_M (f i j))).trans
          ((hb 1).trans (congrArg (fun x => x / 3) (len_diag2 ⟨fun i j => dec (f i j)⟩ d).symm)),
        (count_diag2_g (fun i j => dec (f i j)) d Letter.O (fun i j => f i j = 2)
          (fun i j => dec_O (f i j))).trans
          ((hb 2).trans (congrArg (fun x => x / 3) (len_diag2 ⟨fun i j => dec (f i j)⟩ d).symm))⟩

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  (∃ (t : Table n), allConditions t) ↔ (9 ∣ n) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
namespace Imo2016P2

theorem imo2016_p2 (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  constructor
  · intro h9
    exact exists_bridge.mp (problem_statement_assumed.mpr h9)
  · intro hf
    exact problem_statement_assumed.mp (exists_bridge.mpr hf)

end Imo2016P2

