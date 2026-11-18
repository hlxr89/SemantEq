import Mathlib

-- No `open` or `open scoped` lines occur in either input.

-- ===== unified context (both sides' local defs, merged) =====
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

inductive Letter : Type
| I : Letter
| M : Letter
| O : Letter
deriving BEq

def countLetter (l : List Letter) (letter : Letter) : ℕ :=
  l.count letter

structure Table (n : ℕ) where
  cells : Fin n → Fin n → Letter

def row (t : Table n) (i : Fin n) : Fin n → Letter :=
  fun j => t.cells i j

def col (t : Table n) (j : Fin n) : Fin n → Letter :=
  fun i => t.cells i j

def rowCondition (t : Table n) : Prop :=
  ∀ i : Fin n,
    countLetter (List.ofFn (row t i)) Letter.I = n / 3 ∧
    countLetter (List.ofFn (row t i)) Letter.M = n / 3 ∧
    countLetter (List.ofFn (row t i)) Letter.O = n / 3

def colCondition (t : Table n) : Prop :=
  ∀ j : Fin n,
    countLetter (List.ofFn (col t j)) Letter.I = n / 3 ∧
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

def diagCondition (l : List Letter) : Prop :=
  l.length % 3 = 0 →
    countLetter l Letter.I = l.length / 3 ∧
    countLetter l Letter.M = l.length / 3 ∧
    countLetter l Letter.O = l.length / 3

def allConditions (t : Table n) : Prop :=
  rowCondition t ∧ colCondition t ∧
  (∀ s : ℕ, diagCondition (diagType1 t s)) ∧
  (∀ d : ℤ, diagCondition (diagType2 t d))

def letterEquiv : Letter ≃ Fin 3 where
  toFun
    | Letter.I => 0
    | Letter.M => 1
    | Letter.O => 2
  invFun c := ![Letter.I, Letter.M, Letter.O] c
  left_inv x := by cases x <;> rfl
  right_inv x := by fin_cases x <;> rfl

lemma letterEquiv_eq (x : Letter) (c : Fin 3) :
    letterEquiv x = c ↔ x = letterEquiv.symm c := by
  constructor
  · intro h
    exact letterEquiv.injective (h.trans (letterEquiv.apply_symm_apply c).symm)
  · intro h
    simpa [h]

@[simp] lemma letterEquiv_symm_zero : letterEquiv.symm (0 : Fin 3) = Letter.I := by rfl
@[simp] lemma letterEquiv_symm_one : letterEquiv.symm (1 : Fin 3) = Letter.M := by rfl
@[simp] lemma letterEquiv_symm_two : letterEquiv.symm (2 : Fin 3) = Letter.O := by rfl

lemma letter_beq_eq (a b : Letter) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> simp [instBEqLetter, instBEqLetter.beq] <;> decide

instance : LawfulBEq Letter where
  rfl := (letter_beq_eq _ _).2 rfl
  eq_of_beq h := (letter_beq_eq _ _).1 h

noncomputable instance : DecidableEq Letter := Classical.decEq _

def indexPairs (n : ℕ) : List (Fin n × Fin n) :=
  List.product (List.ofFn (fun i : Fin n => i)) (List.ofFn (fun j : Fin n => j))

lemma indexPairs_nodup (n : ℕ) : (indexPairs n).Nodup := by
  apply List.Nodup.product
  · exact (List.nodup_ofFn.mpr fun _ _ h => h)
  · exact (List.nodup_ofFn.mpr fun _ _ h => h)

lemma indexPairs_toFinset (n : ℕ) : (indexPairs n).toFinset = Finset.univ := by
  ext ⟨i, j⟩
  simp [indexPairs]

lemma count_map_filter_eq_card {α : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (p : α → Bool) (g : α → Letter) (c : Letter) :
    countLetter ((l.filter p).map g) c =
      ((l.toFinset.filter (fun x => p x = true)).filter (fun x => g x = c)).card := by
  classical
  rw [countLetter, List.count_eq_length_filter, List.filter_map]
  simp only [List.length_map]
  rw [← List.toFinset_card_of_nodup ((hl.filter _).filter _)]
  congr 1
  ext x
  simp [and_left_comm, and_assoc, and_comm]

lemma length_filter_eq_card {α : Type*} [DecidableEq α]
    (l : List α) (hl : l.Nodup) (p : α → Bool) :
    (l.filter p).length = (l.toFinset.filter (fun x => p x = true)).card := by
  rw [← List.toFinset_card_of_nodup (hl.filter p), List.toFinset_filter]

lemma count_ofFn_equiv {n : ℕ} (f : Fin n → Fin 3) (c : Fin 3) :
    countLetter (List.ofFn (fun i => letterEquiv.symm (f i))) (letterEquiv.symm c) =
      (Finset.univ.filter (fun i => f i = c)).card := by
  induction n with
  | zero => simp [countLetter]
  | succ n ih =>
      rw [List.ofFn_succ, countLetter, List.count_cons]
      rw [Finset.card_filter, Fin.sum_univ_succ]
      have h := ih (fun i => f i.succ)
      rw [countLetter, Finset.card_filter] at h
      rw [h]
      generalize f 0 = x
      fin_cases c <;> fin_cases x <;>
        simp [instBEqLetter, instBEqLetter.beq, add_comm] <;> decide

lemma count_ofFn_equiv' {n : ℕ} (f : Fin n → Letter) (c : Letter) :
    (Finset.univ.filter (fun i => letterEquiv (f i) = letterEquiv c)).card =
      countLetter (List.ofFn f) c := by
  induction n with
  | zero => simp [countLetter]
  | succ n ih =>
      rw [Finset.card_filter, Fin.sum_univ_succ]
      rw [List.ofFn_succ, countLetter, List.count_cons]
      have h := ih (fun i => f i.succ)
      rw [Finset.card_filter, countLetter] at h
      rw [h]
      generalize f 0 = x
      cases c <;> cases x <;>
        simp [instBEqLetter, instBEqLetter.beq, add_comm] <;> decide

lemma count_ofFn_letter {n : ℕ} (f : Fin n → Letter) (c : Letter) :
    (Finset.univ.filter (fun i => f i = c)).card = countLetter (List.ofFn f) c := by
  simpa only [Equiv.apply_eq_iff_eq] using count_ofFn_equiv' f c

lemma row_card_bridge {n : ℕ} {α : Type*} [DecidableEq α]
    (f : Fin n → Fin n → α) (i : Fin n) (c : α) :
    ((Imo2016P2.row i).filter (fun p => f p.1 p.2 = c)).card =
      (Finset.univ.filter (fun j => f i j = c)).card := by
  classical
  refine Finset.card_bij' (fun p _ => p.2) (fun j _ => (i, j)) ?_ ?_ ?_ ?_
  all_goals simp [Imo2016P2.row] at *
  all_goals aesop

lemma row_size_bridge {n : ℕ} (i : Fin n) : (Imo2016P2.row i).card = n := by
  classical
  simpa using row_card_bridge (fun _ _ => (0 : Fin 3)) i (0 : Fin 3)

lemma col_card_bridge {n : ℕ} {α : Type*} [DecidableEq α]
    (f : Fin n → Fin n → α) (j : Fin n) (c : α) :
    ((Imo2016P2.col j).filter (fun p => f p.1 p.2 = c)).card =
      (Finset.univ.filter (fun i => f i j = c)).card := by
  classical
  refine Finset.card_bij' (fun p _ => p.1) (fun i _ => (i, j)) ?_ ?_ ?_ ?_
  all_goals simp [Imo2016P2.col] at *
  all_goals aesop

lemma col_size_bridge {n : ℕ} (j : Fin n) : (Imo2016P2.col j).card = n := by
  classical
  simpa using col_card_bridge (fun _ _ => (0 : Fin 3)) j (0 : Fin 3)

lemma diag1_length_bridge {n : ℕ} (t : Table n) (s : ℕ) :
    (diagType1 t s).length = (Imo2016P2.diagSum (n := n) s).card := by
  have h := length_filter_eq_card (indexPairs n) (indexPairs_nodup n)
    (fun p : Fin n × Fin n => (p.1 : ℕ) + (p.2 : ℕ) = s)
  rw [indexPairs_toFinset] at h
  simpa [diagType1, indexPairs, Imo2016P2.diagSum] using h

lemma diag2_length_bridge {n : ℕ} (t : Table n) (d : ℤ) :
    (diagType2 t d).length = (Imo2016P2.diagDiff (n := n) d).card := by
  have h := length_filter_eq_card (indexPairs n) (indexPairs_nodup n)
    (fun p : Fin n × Fin n => (p.1 : ℤ) - (p.2 : ℤ) = d)
  rw [indexPairs_toFinset] at h
  simpa [diagType2, indexPairs, Imo2016P2.diagDiff] using h

lemma diag1_count_bridge {n : ℕ} (t : Table n) (s : ℕ) (c : Letter) :
    countLetter (diagType1 t s) c =
      ((Imo2016P2.diagSum (n := n) s).filter (fun p => t.cells p.1 p.2 = c)).card := by
  have h := count_map_filter_eq_card (indexPairs n) (indexPairs_nodup n)
    (fun p : Fin n × Fin n => (p.1 : ℕ) + (p.2 : ℕ) = s)
    (fun p => t.cells p.1 p.2) c
  rw [indexPairs_toFinset] at h
  simpa [diagType1, indexPairs, Imo2016P2.diagSum] using h

lemma diag2_count_bridge {n : ℕ} (t : Table n) (d : ℤ) (c : Letter) :
    countLetter (diagType2 t d) c =
      ((Imo2016P2.diagDiff (n := n) d).filter (fun p => t.cells p.1 p.2 = c)).card := by
  have h := count_map_filter_eq_card (indexPairs n) (indexPairs_nodup n)
    (fun p : Fin n × Fin n => (p.1 : ℤ) - (p.2 : ℤ) = d)
    (fun p => t.cells p.1 p.2) c
  rw [indexPairs_toFinset] at h
  simpa [diagType2, indexPairs, Imo2016P2.diagDiff] using h

lemma ref_to_cand_conditions {n : ℕ} (f : Fin n → Fin n → Fin 3)
    (hf : Imo2016P2.MODTable f) :
    allConditions ⟨fun i j => letterEquiv.symm (f i j)⟩ := by
  classical
  rcases hf with ⟨hrow, hcol, hsum, hdiff⟩
  constructor
  · intro i
    have h := hrow i
    refine ⟨?_, ?_, ?_⟩
    · change countLetter (List.ofFn (fun j => letterEquiv.symm (f i j))) Letter.I = n / 3
      rw [show Letter.I = letterEquiv.symm (0 : Fin 3) by rfl, count_ofFn_equiv,
        ← row_card_bridge, h (0 : Fin 3), row_size_bridge]
    · change countLetter (List.ofFn (fun j => letterEquiv.symm (f i j))) Letter.M = n / 3
      rw [show Letter.M = letterEquiv.symm (1 : Fin 3) by rfl, count_ofFn_equiv,
        ← row_card_bridge, h (1 : Fin 3), row_size_bridge]
    · change countLetter (List.ofFn (fun j => letterEquiv.symm (f i j))) Letter.O = n / 3
      rw [show Letter.O = letterEquiv.symm (2 : Fin 3) by rfl, count_ofFn_equiv,
        ← row_card_bridge, h (2 : Fin 3), row_size_bridge]
  constructor
  · intro j
    have h := hcol j
    refine ⟨?_, ?_, ?_⟩
    · change countLetter (List.ofFn (fun i => letterEquiv.symm (f i j))) Letter.I = n / 3
      rw [show Letter.I = letterEquiv.symm (0 : Fin 3) by rfl, count_ofFn_equiv,
        ← col_card_bridge, h (0 : Fin 3), col_size_bridge]
    · change countLetter (List.ofFn (fun i => letterEquiv.symm (f i j))) Letter.M = n / 3
      rw [show Letter.M = letterEquiv.symm (1 : Fin 3) by rfl, count_ofFn_equiv,
        ← col_card_bridge, h (1 : Fin 3), col_size_bridge]
    · change countLetter (List.ofFn (fun i => letterEquiv.symm (f i j))) Letter.O = n / 3
      rw [show Letter.O = letterEquiv.symm (2 : Fin 3) by rfl, count_ofFn_equiv,
        ← col_card_bridge, h (2 : Fin 3), col_size_bridge]
  constructor
  · intro s hsmod
    have hlen := diag1_length_bridge ⟨fun i j => letterEquiv.symm (f i j)⟩ s
    have hbal := hsum s ((Nat.dvd_iff_mod_eq_zero).2 (by simpa [hlen] using hsmod))
    refine ⟨?_, ?_, ?_⟩
    · rw [diag1_count_bridge, hlen]
      simpa only [Equiv.symm_apply_eq] using hbal (0 : Fin 3)
    · rw [diag1_count_bridge, hlen]
      simpa only [Equiv.symm_apply_eq] using hbal (1 : Fin 3)
    · rw [diag1_count_bridge, hlen]
      simpa only [Equiv.symm_apply_eq] using hbal (2 : Fin 3)
  · intro d hdmod
    have hlen := diag2_length_bridge ⟨fun i j => letterEquiv.symm (f i j)⟩ d
    have hbal := hdiff d ((Nat.dvd_iff_mod_eq_zero).2 (by simpa [hlen] using hdmod))
    refine ⟨?_, ?_, ?_⟩
    · rw [diag2_count_bridge, hlen]
      simpa only [Equiv.symm_apply_eq] using hbal (0 : Fin 3)
    · rw [diag2_count_bridge, hlen]
      simpa only [Equiv.symm_apply_eq] using hbal (1 : Fin 3)
    · rw [diag2_count_bridge, hlen]
      simpa only [Equiv.symm_apply_eq] using hbal (2 : Fin 3)

lemma cand_to_ref_conditions {n : ℕ} (t : Table n) (ht : allConditions t) :
    Imo2016P2.MODTable (fun i j => letterEquiv (t.cells i j)) := by
  classical
  rcases ht with ⟨hrow, hcol, hsum, hdiff⟩
  constructor
  · intro i c
    fin_cases c
    · simp only [letterEquiv_eq, letterEquiv_symm_zero]
      rw [row_card_bridge, row_size_bridge, count_ofFn_letter]
      exact (hrow i).1
    · simp only [letterEquiv_eq, letterEquiv_symm_one]
      rw [row_card_bridge, row_size_bridge, count_ofFn_letter]
      exact (hrow i).2.1
    · simp only [letterEquiv_eq, letterEquiv_symm_two]
      rw [row_card_bridge, row_size_bridge, count_ofFn_letter]
      exact (hrow i).2.2
  constructor
  · intro j c
    fin_cases c
    · simp only [letterEquiv_eq, letterEquiv_symm_zero]
      rw [col_card_bridge, col_size_bridge, count_ofFn_letter]
      exact (hcol j).1
    · simp only [letterEquiv_eq, letterEquiv_symm_one]
      rw [col_card_bridge, col_size_bridge, count_ofFn_letter]
      exact (hcol j).2.1
    · simp only [letterEquiv_eq, letterEquiv_symm_two]
      rw [col_card_bridge, col_size_bridge, count_ofFn_letter]
      exact (hcol j).2.2
  constructor
  · intro s hs c
    have hlen := diag1_length_bridge t s
    have hcand := hsum s ((Nat.dvd_iff_mod_eq_zero).1 hs |> (by simpa [hlen] using ·))
    have hc_lt := c.isLt
    have hc : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
    rcases hc with hc | hc | hc
    · have : c = 0 := Fin.ext hc
      subst c
      simp only [letterEquiv_eq, letterEquiv_symm_zero]
      rw [← diag1_count_bridge t s Letter.I, ← hlen]
      exact hcand.1
    · have : c = 1 := Fin.ext hc
      subst c
      simp only [letterEquiv_eq, letterEquiv_symm_one]
      rw [← diag1_count_bridge t s Letter.M, ← hlen]
      exact hcand.2.1
    · have : c = 2 := Fin.ext hc
      subst c
      simp only [letterEquiv_eq, letterEquiv_symm_two]
      rw [← diag1_count_bridge t s Letter.O, ← hlen]
      exact hcand.2.2
  · intro d hd c
    have hlen := diag2_length_bridge t d
    have hcand := hdiff d ((Nat.dvd_iff_mod_eq_zero).1 hd |> (by simpa [hlen] using ·))
    have hc_lt := c.isLt
    have hc : c.val = 0 ∨ c.val = 1 ∨ c.val = 2 := by omega
    rcases hc with hc | hc | hc
    · have : c = 0 := Fin.ext hc
      subst c
      simp only [letterEquiv_eq, letterEquiv_symm_zero]
      rw [← diag2_count_bridge t d Letter.I, ← hlen]
      exact hcand.1
    · have : c = 1 := Fin.ext hc
      subst c
      simp only [letterEquiv_eq, letterEquiv_symm_one]
      rw [← diag2_count_bridge t d Letter.M, ← hlen]
      exact hcand.2.1
    · have : c = 2 := Fin.ext hc
      subst c
      simp only [letterEquiv_eq, letterEquiv_symm_two]
      rw [← diag2_count_bridge t d Letter.O, ← hlen]
      exact hcand.2.2

-- ===== assumed statement (antecedent) =====
namespace Imo2016P2

theorem imo2016_p2_assumed (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  sorry

end Imo2016P2

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  (∃ (t : Table n), allConditions t) ↔ (9 ∣ n) := by
  constructor
  · intro ht
    by_cases hn : n = 0
    · simp [hn]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      rcases ht with ⟨t, ht⟩
      exact (Imo2016P2.imo2016_p2_assumed n hnpos).2
        ⟨fun i j => letterEquiv (t.cells i j), cand_to_ref_conditions t ht⟩
  · intro hn
    by_cases hz : n = 0
    · subst n
      refine ⟨⟨fun i => Fin.elim0 i⟩, ?_⟩
      constructor
      · intro i
        exact Fin.elim0 i
      constructor
      · intro j
        exact Fin.elim0 j
      constructor
      · intro s _
        have hlen := diag1_length_bridge (⟨fun i => Fin.elim0 i⟩ : Table 0) s
        refine ⟨?_, ?_, ?_⟩ <;>
          rw [diag1_count_bridge, hlen] <;>
          simp [Imo2016P2.diagSum]
      · intro d _
        have hlen := diag2_length_bridge (⟨fun i => Fin.elim0 i⟩ : Table 0) d
        refine ⟨?_, ?_, ?_⟩ <;>
          rw [diag2_count_bridge, hlen] <;>
          simp [Imo2016P2.diagDiff]
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hz
      have hex := (Imo2016P2.imo2016_p2_assumed n hnpos).1 hn
      rcases hex with ⟨f, hf⟩
      exact ⟨⟨fun i j => letterEquiv.symm (f i j)⟩, ref_to_cand_conditions f hf⟩
