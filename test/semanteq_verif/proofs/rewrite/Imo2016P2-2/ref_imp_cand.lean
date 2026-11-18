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
  intro n
  let CTable (f : Fin n → Fin n → Fin 3) : Prop :=
    (∀ i : Fin n,
      (Finset.univ.filter (fun j => f i j = 0)).card = n / 3 ∧
      (Finset.univ.filter (fun j => f i j = 1)).card = n / 3 ∧
      (Finset.univ.filter (fun j => f i j = 2)).card = n / 3) ∧
    (∀ j : Fin n,
      (Finset.univ.filter (fun i => f i j = 0)).card = n / 3 ∧
      (Finset.univ.filter (fun i => f i j = 1)).card = n / 3 ∧
      (Finset.univ.filter (fun i => f i j = 2)).card = n / 3) ∧
    (∀ s : ℕ, 2 ≤ s ∧ s ≤ 2 * n →
      let diagonal := Finset.filter (fun p : Fin n × Fin n => p.1.val + p.2.val + 2 = s) (Finset.univ.product Finset.univ)
      diagonal.card % 3 = 0 →
        (diagonal.filter (fun p => f p.1 p.2 = 0)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => f p.1 p.2 = 1)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => f p.1 p.2 = 2)).card = diagonal.card / 3) ∧
    (∀ d : ℤ, -(n - 1) ≤ d ∧ d ≤ n - 1 →
      let diagonal := Finset.filter (fun p : Fin n × Fin n => (p.1.val : ℤ) - (p.2.val : ℤ) = d) (Finset.univ.product Finset.univ)
      diagonal.card % 3 = 0 →
        (diagonal.filter (fun p => f p.1 p.2 = 0)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => f p.1 p.2 = 1)).card = diagonal.card / 3 ∧
        (diagonal.filter (fun p => f p.1 p.2 = 2)).card = diagonal.card / 3)
  have balanced_iff (f : Fin n → Fin n → Fin 3) (cells : Finset (Fin n × Fin n)) :
      Imo2016P2.Balanced f cells ↔
        (cells.filter (fun p => f p.1 p.2 = 0)).card = cells.card / 3 ∧
        (cells.filter (fun p => f p.1 p.2 = 1)).card = cells.card / 3 ∧
        (cells.filter (fun p => f p.1 p.2 = 2)).card = cells.card / 3 := by
    rw [Imo2016P2.Balanced]
    constructor
    · intro h
      exact ⟨h 0, h 1, h 2⟩
    · rintro ⟨h0, h1, h2⟩ c
      fin_cases c
      · exact h0
      · exact h1
      · exact h2
  have row_iff (f : Fin n → Fin n → Fin 3) (r : Fin n) :
      Imo2016P2.Balanced f (Imo2016P2.row r) ↔
        (Finset.univ.filter (fun j => f r j = 0)).card = n / 3 ∧
        (Finset.univ.filter (fun j => f r j = 1)).card = n / 3 ∧
        (Finset.univ.filter (fun j => f r j = 2)).card = n / 3 := by
    rw [balanced_iff]
    have hr : Imo2016P2.row r = {r} ×ˢ Finset.univ := by
      ext p
      simp only [Imo2016P2.row, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton, eq_comm, and_true]
    have hf (c : Fin 3) :
        (Imo2016P2.row r).filter (fun p => f p.1 p.2 = c) =
          {r} ×ˢ (Finset.univ.filter (fun j => f r j = c)) := by
      ext p
      simp only [Imo2016P2.row, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton]
      constructor <;> rintro ⟨hp, hc⟩ <;> subst hp <;> exact ⟨rfl, hc⟩
    rw [hf 0, hf 1, hf 2, hr]
    simp only [Finset.card_product, Finset.card_singleton, one_mul,
      Finset.card_univ, Fintype.card_fin]
  have col_iff (f : Fin n → Fin n → Fin 3) (k : Fin n) :
      Imo2016P2.Balanced f (Imo2016P2.col k) ↔
        (Finset.univ.filter (fun i => f i k = 0)).card = n / 3 ∧
        (Finset.univ.filter (fun i => f i k = 1)).card = n / 3 ∧
        (Finset.univ.filter (fun i => f i k = 2)).card = n / 3 := by
    rw [balanced_iff]
    have hk : Imo2016P2.col k = Finset.univ ×ˢ {k} := by
      ext p
      simp only [Imo2016P2.col, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton, true_and]
    have hf (c : Fin 3) :
        (Imo2016P2.col k).filter (fun p => f p.1 p.2 = c) =
          (Finset.univ.filter (fun i => f i k = c)) ×ˢ {k} := by
      ext p
      simp only [Imo2016P2.col, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_product, Finset.mem_singleton]
      constructor
      · rintro ⟨hp, hc⟩
        subst k
        exact ⟨hc, rfl⟩
      · rintro ⟨hc, hp⟩
        subst k
        exact ⟨rfl, hc⟩
    rw [hf 0, hf 1, hf 2, hk]
    simp only [Finset.card_product, Finset.card_singleton, mul_one,
      Finset.card_univ, Fintype.card_fin]
  have sum_set (s : ℕ) (hs : 2 ≤ s) :
      Finset.filter (fun p : Fin n × Fin n => p.1.val + p.2.val + 2 = s)
          (Finset.univ.product Finset.univ) =
        Imo2016P2.diagSum (n := n) (s - 2) := by
    ext p
    rw [Imo2016P2.diagSum, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨Finset.mem_univ p, Nat.eq_sub_of_add_eq h⟩
    · rintro ⟨_, h⟩
      refine ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, ?_⟩
      rw [h, Nat.sub_add_cancel hs]
  have diff_set (d : ℤ) :
      Finset.filter (fun p : Fin n × Fin n => (p.1.val : ℤ) - (p.2.val : ℤ) = d)
          (Finset.univ.product Finset.univ) =
        Imo2016P2.diagDiff (n := n) d := by
    ext p
    rw [Imo2016P2.diagDiff, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨Finset.mem_univ p, h⟩
    · rintro ⟨_, h⟩
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩, h⟩
  have table_iff (f : Fin n → Fin n → Fin 3) :
      CTable f ↔ Imo2016P2.MODTable f := by
    constructor
    · rintro ⟨hrow, hcol, hsum, hdiff⟩
      refine ⟨fun r => (row_iff f r).mpr (hrow r),
        fun k => (col_iff f k).mpr (hcol k), ?_, ?_⟩
      · intro s hsdiv
        by_cases hs : s + 2 ≤ 2 * n
        · have hthree := hsum (s + 2) ⟨by omega, hs⟩
          rw [sum_set (s + 2) (by omega)] at hthree
          exact (balanced_iff f (Imo2016P2.diagSum s)).mpr
            (hthree (Nat.mod_eq_zero_of_dvd hsdiv))
        · have hempty : Imo2016P2.diagSum (n := n) s = ∅ := by
            ext p
            constructor
            · intro hp
              exfalso
              rw [Imo2016P2.diagSum, Finset.mem_filter] at hp
              have hi := p.1.isLt
              have hj := p.2.isLt
              omega -- non-rewrite step: the candidate omits empty out-of-range diagonals
            · intro hp
              exfalso
              simpa using hp -- non-rewrite step: eliminate membership in the empty finset
          rw [hempty]
          apply (balanced_iff f ∅).mpr
          simp only [Finset.filter_empty, Finset.card_empty, Nat.zero_div, and_self]
      · intro d hddiv
        by_cases hd : -((n : ℤ) - 1) ≤ d ∧ d ≤ (n : ℤ) - 1
        · have hthree := hdiff d hd
          rw [diff_set d] at hthree
          exact (balanced_iff f (Imo2016P2.diagDiff d)).mpr
            (hthree (Nat.mod_eq_zero_of_dvd hddiv))
        · have hempty : Imo2016P2.diagDiff (n := n) d = ∅ := by
            ext p
            constructor
            · intro hp
              exfalso
              rw [Imo2016P2.diagDiff, Finset.mem_filter] at hp
              have hi := p.1.isLt
              have hj := p.2.isLt
              omega -- non-rewrite step: the candidate omits empty out-of-range diagonals
            · intro hp
              exfalso
              simpa using hp -- non-rewrite step: eliminate membership in the empty finset
          rw [hempty]
          apply (balanced_iff f ∅).mpr
          simp only [Finset.filter_empty, Finset.card_empty, Nat.zero_div, and_self]
    · rintro ⟨hrow, hcol, hsum, hdiff⟩
      refine ⟨fun r => (row_iff f r).mp (hrow r),
        fun k => (col_iff f k).mp (hcol k), ?_, ?_⟩
      · intro s hs
        dsimp only
        rw [sum_set s hs.1]
        intro hmod
        exact (balanced_iff f (Imo2016P2.diagSum (s - 2))).mp
          (hsum (s - 2) (Nat.dvd_of_mod_eq_zero hmod))
      · intro d _
        dsimp only
        rw [diff_set d]
        intro hmod
        exact (balanced_iff f (Imo2016P2.diagDiff d)).mp
          (hdiff d (Nat.dvd_of_mod_eq_zero hmod))
  change (0 < n → ∃ f, CTable f) ↔ 9 ∣ n
  constructor
  · intro hex
    cases n with
    | zero => exact dvd_zero 9 -- non-rewrite step: the candidate's implication is vacuous at zero
    | succ n =>
      have hn : 0 < n + 1 := Nat.zero_lt_succ n
      obtain ⟨f, hf⟩ := hex hn
      have hm : n + 1 ∈ Imo2016P2.solution :=
        (Imo2016P2.imo2016_p2_assumed (n + 1) hn).mpr ⟨f, (table_iff f).mp hf⟩
      exact hm
  · intro hnine
    intro hn
    obtain ⟨f, hf⟩ :=
      (Imo2016P2.imo2016_p2_assumed n hn).mp (show n ∈ Imo2016P2.solution from hnine)
    exact ⟨f, (table_iff f).mpr hf⟩
