import Mathlib

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

-- ===== assumed statement (antecedent) =====
theorem _root_.problem_statement_assumed :
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
theorem imo2016_p2 (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := by
  have row_bridge {n : ℕ} (f : Fin n → Fin n → Fin 3) (i : Fin n) :
      Balanced f (row i) ↔
        (Finset.univ.filter (fun j => f i j = 0)).card = n / 3 ∧
        (Finset.univ.filter (fun j => f i j = 1)).card = n / 3 ∧
        (Finset.univ.filter (fun j => f i j = 2)).card = n / 3 := by
    have hcard : (row i).card = n := by
      calc
        (row i).card = (Finset.univ : Finset (Fin n)).card := by
          apply Finset.card_bij (fun p _ => p.2) -- non-rewrite step
          · intro p hp
            exact Finset.mem_univ p.2
          · intro p hp q hq he
            apply Prod.ext
            · simp only [row, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
              exact hp.trans hq.symm
            · exact he
          · intro j hj
            refine ⟨(i, j), ?_, rfl⟩
            simp only [row, Finset.mem_filter, Finset.mem_univ, true_and]
        _ = n := Finset.card_fin n
    have heq (c : Fin 3) : ((row i).filter (fun p => f p.1 p.2 = c)).card =
        (Finset.univ.filter (fun j => f i j = c)).card := by
      apply Finset.card_bij (fun p _ => p.2) -- non-rewrite step
      · intro p hp
        simp only [row, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        simpa only [hp.1] using hp.2
      · intro p hp q hq he
        apply Prod.ext
        · simp only [row, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
          exact hp.1.trans hq.1.symm
        · exact he
      · intro j hj
        refine ⟨(i, j), ?_, rfl⟩
        simp only [row, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hj
    constructor
    · intro h
      exact ⟨(heq 0).symm.trans ((h 0).trans (congrArg (fun x => x / 3) hcard)),
        (heq 1).symm.trans ((h 1).trans (congrArg (fun x => x / 3) hcard)),
        (heq 2).symm.trans ((h 2).trans (congrArg (fun x => x / 3) hcard))⟩
    · rintro ⟨h0, h1, h2⟩ c
      fin_cases c
      · exact (heq 0).trans (h0.trans (congrArg (fun x => x / 3) hcard.symm))
      · exact (heq 1).trans (h1.trans (congrArg (fun x => x / 3) hcard.symm))
      · exact (heq 2).trans (h2.trans (congrArg (fun x => x / 3) hcard.symm))
  have col_bridge {n : ℕ} (f : Fin n → Fin n → Fin 3) (j : Fin n) :
      Balanced f (col j) ↔
        (Finset.univ.filter (fun i => f i j = 0)).card = n / 3 ∧
        (Finset.univ.filter (fun i => f i j = 1)).card = n / 3 ∧
        (Finset.univ.filter (fun i => f i j = 2)).card = n / 3 := by
    have hcard : (col j).card = n := by
      calc
        (col j).card = (Finset.univ : Finset (Fin n)).card := by
          apply Finset.card_bij (fun p _ => p.1) -- non-rewrite step
          · intro p hp
            exact Finset.mem_univ p.1
          · intro p hp q hq he
            apply Prod.ext
            · exact he
            · simp only [col, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
              exact hp.trans hq.symm
          · intro i hi
            refine ⟨(i, j), ?_, rfl⟩
            simp only [col, Finset.mem_filter, Finset.mem_univ, true_and]
        _ = n := Finset.card_fin n
    have heq (c : Fin 3) : ((col j).filter (fun p => f p.1 p.2 = c)).card =
        (Finset.univ.filter (fun i => f i j = c)).card := by
      apply Finset.card_bij (fun p _ => p.1) -- non-rewrite step
      · intro p hp
        simp only [col, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
        simpa only [hp.1] using hp.2
      · intro p hp q hq he
        apply Prod.ext
        · exact he
        · simp only [col, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
          exact hp.1.trans hq.1.symm
      · intro i hi
        refine ⟨(i, j), ?_, rfl⟩
        simp only [col, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hi
    constructor
    · intro h
      exact ⟨(heq 0).symm.trans ((h 0).trans (congrArg (fun x => x / 3) hcard)),
        (heq 1).symm.trans ((h 1).trans (congrArg (fun x => x / 3) hcard)),
        (heq 2).symm.trans ((h 2).trans (congrArg (fun x => x / 3) hcard))⟩
    · rintro ⟨h0, h1, h2⟩ c
      fin_cases c
      · exact (heq 0).trans (h0.trans (congrArg (fun x => x / 3) hcard.symm))
      · exact (heq 1).trans (h1.trans (congrArg (fun x => x / 3) hcard.symm))
      · exact (heq 2).trans (h2.trans (congrArg (fun x => x / 3) hcard.symm))
  have diff_bridge {n : ℕ} (f : Fin n → Fin n → Fin 3) :
      (∀ d : ℤ,
          (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d)).card % 3 = 0 →
          (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d ∧ f p.1 p.2 = 0)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d)).card / 3 ∧
          (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d ∧ f p.1 p.2 = 1)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d)).card / 3 ∧
          (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d ∧ f p.1 p.2 = 2)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val - p.2.val : ℤ) = d)).card / 3) ↔
        (∀ d : ℤ, 3 ∣ (diagDiff (n := n) d).card → Balanced f (diagDiff d)) := by
    constructor
    · intro h d hd c
      have h' := h d (Nat.dvd_iff_mod_eq_zero.mp hd)
      simp only [diagDiff, Finset.filter_filter]
      fin_cases c
      · exact h'.1
      · exact h'.2.1
      · exact h'.2.2
    · intro h d hd
      have h' := h d (Nat.dvd_iff_mod_eq_zero.mpr hd)
      exact ⟨by simpa only [diagDiff, Finset.filter_filter] using h' 0,
        by simpa only [diagDiff, Finset.filter_filter] using h' 1,
        by simpa only [diagDiff, Finset.filter_filter] using h' 2⟩
  have sum_bridge {n : ℕ} (f : Fin n → Fin n → Fin 3) :
      (∀ s : ℤ,
          (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s)).card % 3 = 0 →
          (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = 0)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s)).card / 3 ∧
          (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = 1)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s)).card / 3 ∧
          (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = 2)).card = (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s)).card / 3) ↔
        (∀ s : ℕ, 3 ∣ (diagSum (n := n) s).card → Balanced f (diagSum s)) := by
    have base_eq (s : ℕ) :
        (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = (s : ℤ))) = diagSum s := by
      ext p
      simp only [diagSum, Finset.mem_filter, Finset.mem_univ, true_and]
      norm_cast
    have color_eq (s : ℕ) (c : Fin 3) :
        (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = (s : ℤ) ∧ f p.1 p.2 = c)) =
          (diagSum s).filter (fun p => f p.1 p.2 = c) := by
      ext p
      simp only [diagSum, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hp
        exact ⟨by norm_cast at hp ⊢; exact hp.1, hp.2⟩
      · intro hp
        exact ⟨by norm_cast at hp ⊢; exact hp.1, hp.2⟩
    constructor
    · intro h s hs c
      have h' := h (s : ℤ) (by rw [base_eq]; exact Nat.dvd_iff_mod_eq_zero.mp hs)
      fin_cases c
      · rw [← color_eq, ← base_eq]
        exact h'.1
      · rw [← color_eq, ← base_eq]
        exact h'.2.1
      · rw [← color_eq, ← base_eq]
        exact h'.2.2
    · intro h s hs
      by_cases hnonneg : 0 ≤ s
      · have hcast : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hnonneg
        have hbase :
            (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s)) = diagSum s.toNat := by
          rw [← hcast]
          exact base_eq s.toNat
        have hdiv : 3 ∣ (diagSum (n := n) s.toNat).card := by
          apply Nat.dvd_iff_mod_eq_zero.mpr
          rw [← hbase]
          exact hs
        have h' := h s.toNat hdiv
        rw [hbase]
        rw [show (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = 0)) =
            (diagSum s.toNat).filter (fun p => f p.1 p.2 = 0) by rw [← hcast]; exact color_eq s.toNat 0]
        rw [show (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = 1)) =
            (diagSum s.toNat).filter (fun p => f p.1 p.2 = 1) by rw [← hcast]; exact color_eq s.toNat 1]
        rw [show (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = 2)) =
            (diagSum s.toNat).filter (fun p => f p.1 p.2 = 2) by rw [← hcast]; exact color_eq s.toNat 2]
        exact ⟨h' 0, h' 1, h' 2⟩
      · have hempty : (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s)) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro p hp heq
          have hpnonneg : 0 ≤ (p.1.val + p.2.val : ℤ) := by positivity
          exact hnonneg (heq ▸ hpnonneg)
        have hcolor (c : Fin 3) :
            (Finset.univ.filter (fun p : Fin n × Fin n => (p.1.val + p.2.val : ℤ) = s ∧ f p.1 p.2 = c)) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro p hp heq
          have hpnonneg : 0 ≤ (p.1.val + p.2.val : ℤ) := by positivity
          exact hnonneg (heq.1 ▸ hpnonneg)
        rw [hempty, hcolor 0, hcolor 1, hcolor 2]
        exact ⟨(Nat.zero_div 3).symm, (Nat.zero_div 3).symm, (Nat.zero_div 3).symm⟩
  constructor
  · intro hnine
    obtain ⟨f, hrow, hcol, hsum, hdiff⟩ := (problem_statement_assumed n).mpr hnine hn
    refine ⟨f, ?_⟩
    exact ⟨fun i => (row_bridge f i).mpr (hrow i),
      fun j => (col_bridge f j).mpr (hcol j),
      (sum_bridge f).mp hsum, (diff_bridge f).mp hdiff⟩
  · rintro ⟨f, hrow, hcol, hsum, hdiff⟩
    apply (problem_statement_assumed n).mp
    intro _
    refine ⟨f, ?_, ?_, ?_, ?_⟩
    · exact fun i => (row_bridge f i).mp (hrow i)
    · exact fun j => (col_bridge f j).mp (hcol j)
    · exact (sum_bridge f).mpr hsum
    · exact (diff_bridge f).mpr hdiff


end Imo2016P2
