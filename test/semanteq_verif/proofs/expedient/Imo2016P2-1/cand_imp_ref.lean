import Mathlib

set_option maxHeartbeats 800000

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

namespace Imo2016P2

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2016_p2 (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  classical
  change 9 ∣ n ↔ ∃ f : Fin n → Fin n → Letter, MODTable f
  have hc := _root_.problem_statement_assumed n
  simp only [hn, true_implies] at hc
  rw [← hc]
  have rowCard (i : Fin n) : (Imo2016P2.row i).card = n := by
    calc
      _ = (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_bij (fun (p : Fin n × Fin n) _ => p.2)
        · simp
        · intro p hp q hq heq
          have hp1 : p.1 = i := by simpa [Imo2016P2.row] using hp
          have hq1 : q.1 = i := by simpa [Imo2016P2.row] using hq
          exact Prod.ext (hp1.trans hq1.symm) heq
        · intro j hj
          exact ⟨(i, j), by simp [Imo2016P2.row]⟩
      _ = n := by simp
  have rowColor (f : Fin n → Fin n → Fin 3) (i : Fin n) (c : Fin 3) :
      ((Imo2016P2.row i).filter (fun p ↦ f p.1 p.2 = c)).card =
        (Finset.univ.filter (fun j => f i j = c)).card := by
    apply Finset.card_bij (fun (p : Fin n × Fin n) _ => p.2)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have hp1 : p.1 = i := by simpa [Imo2016P2.row] using hp.1
      simpa [hp1] using hp.2
    · intro p hp q hq heq
      simp only [Finset.mem_filter] at hp hq
      have hp1 : p.1 = i := by simpa [Imo2016P2.row] using hp.1
      have hq1 : q.1 = i := by simpa [Imo2016P2.row] using hq.1
      exact Prod.ext (hp1.trans hq1.symm) heq
    · intro j hj
      exact ⟨(i, j), by simpa [Imo2016P2.row] using hj⟩
  have colCard (j : Fin n) : (Imo2016P2.col j).card = n := by
    calc
      _ = (Finset.univ : Finset (Fin n)).card := by
        apply Finset.card_bij (fun (p : Fin n × Fin n) _ => p.1)
        · simp
        · intro p hp q hq heq
          have hp2 : p.2 = j := by simpa [Imo2016P2.col] using hp
          have hq2 : q.2 = j := by simpa [Imo2016P2.col] using hq
          exact Prod.ext heq (hp2.trans hq2.symm)
        · intro i hi
          exact ⟨(i, j), by simp [Imo2016P2.col]⟩
      _ = n := by simp
  have colColor (f : Fin n → Fin n → Fin 3) (j : Fin n) (c : Fin 3) :
      ((Imo2016P2.col j).filter (fun p ↦ f p.1 p.2 = c)).card =
        (Finset.univ.filter (fun i => f i j = c)).card := by
    apply Finset.card_bij (fun (p : Fin n × Fin n) _ => p.1)
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have hp2 : p.2 = j := by simpa [Imo2016P2.col] using hp.1
      simpa [hp2] using hp.2
    · intro p hp q hq heq
      simp only [Finset.mem_filter] at hp hq
      have hp2 : p.2 = j := by simpa [Imo2016P2.col] using hp.1
      have hq2 : q.2 = j := by simpa [Imo2016P2.col] using hq.1
      exact Prod.ext heq (hp2.trans hq2.symm)
    · intro i hi
      exact ⟨(i, j), by simpa [Imo2016P2.col] using hi⟩
  have sumCells (s : ℕ) :
      Finset.univ.filter (fun p : Fin n × Fin n =>
        (p.1.val + p.2.val : ℤ) = (s : ℤ)) = Imo2016P2.diagSum s := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Imo2016P2.diagSum]
    norm_cast
  constructor
  · rintro ⟨f, hr, hc, hs, hd⟩
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · intro i c
      rw [rowColor, rowCard]
      fin_cases c <;> simp_all
    · intro j c
      rw [colColor, colCard]
      fin_cases c <;> simp_all
    · intro s hdiv c
      have hmod :
          (Finset.univ.filter (fun p : Fin n × Fin n =>
            (p.1.val + p.2.val : ℤ) = (s : ℤ))).card % 3 = 0 := by
        rw [← Nat.dvd_iff_mod_eq_zero]
        simpa [sumCells s] using hdiv
      have h := hs (s : ℤ) hmod
      fin_cases c
      · simpa [← sumCells s, Finset.filter_filter, and_comm] using h.1
      · simpa [← sumCells s, Finset.filter_filter, and_comm] using h.2.1
      · simpa [← sumCells s, Finset.filter_filter, and_comm] using h.2.2
    · intro d hdiv c
      have hmod :
          (Finset.univ.filter (fun p : Fin n × Fin n =>
            (p.1.val - p.2.val : ℤ) = d)).card % 3 = 0 := by
        rw [← Nat.dvd_iff_mod_eq_zero]
        simpa [Imo2016P2.diagDiff] using hdiv
      have h := hd d hmod
      fin_cases c
      · simpa [Imo2016P2.diagDiff, Finset.filter_filter, and_comm] using h.1
      · simpa [Imo2016P2.diagDiff, Finset.filter_filter, and_comm] using h.2.1
      · simpa [Imo2016P2.diagDiff, Finset.filter_filter, and_comm] using h.2.2
  · rintro ⟨f, hr, hc, hs, hd⟩
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · intro i
      have h := hr i
      constructor
      · simpa [rowColor f i 0, rowCard i] using h 0
      constructor
      · simpa [rowColor f i 1, rowCard i] using h 1
      · simpa [rowColor f i 2, rowCard i] using h 2
    · intro j
      have h := hc j
      constructor
      · simpa [colColor f j 0, colCard j] using h 0
      constructor
      · simpa [colColor f j 1, colCard j] using h 1
      · simpa [colColor f j 2, colCard j] using h 2
    · intro s hmod
      by_cases hsnonneg : 0 ≤ s
      · have cellsEq :
            Finset.univ.filter (fun p : Fin n × Fin n =>
              (p.1.val + p.2.val : ℤ) = s) =
              Imo2016P2.diagSum s.toNat := by
          rw [← Int.toNat_of_nonneg hsnonneg]
          exact sumCells s.toNat
        have hdiv : 3 ∣ (Imo2016P2.diagSum (n := n) s.toNat).card := by
          rw [Nat.dvd_iff_mod_eq_zero, ← cellsEq]
          exact hmod
        have h := hs s.toNat hdiv
        constructor
        · simpa [← cellsEq, Finset.filter_filter, and_comm] using h 0
        constructor
        · simpa [← cellsEq, Finset.filter_filter, and_comm] using h 1
        · simpa [← cellsEq, Finset.filter_filter, and_comm] using h 2
      · have hsneg : s < 0 := lt_of_not_ge hsnonneg
        have cellsEmpty :
            Finset.univ.filter (fun p : Fin n × Fin n =>
              (p.1.val + p.2.val : ℤ) = s) = ∅ := by
          ext p
          simp
          omega
        have colorEmpty (c : Fin 3) :
            Finset.univ.filter (fun p : Fin n × Fin n =>
              (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = c) = ∅ := by
          ext p
          simp
          omega
        simp [cellsEmpty, colorEmpty]
    · intro d hmod
      have hdiv : 3 ∣ (Imo2016P2.diagDiff (n := n) d).card := by
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa [Imo2016P2.diagDiff] using hmod
      have h := hd d hdiv
      constructor
      · simpa [Imo2016P2.diagDiff, Finset.filter_filter, and_comm] using h 0
      constructor
      · simpa [Imo2016P2.diagDiff, Finset.filter_filter, and_comm] using h 1
      · simpa [Imo2016P2.diagDiff, Finset.filter_filter, and_comm] using h 2

end Imo2016P2

