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


def ExplicitTable (n : ℕ) (table : Fin n → Fin n → Fin 3) : Prop :=
    (∀ i : Fin n, (Finset.univ.filter (fun j => table i j = 0)).card = n / 3 ∧ (Finset.univ.filter (fun j => table i j = 1)).card = n / 3 ∧ (Finset.univ.filter (fun j => table i j = 2)).card = n / 3) ∧
    (∀ j : Fin n, (Finset.univ.filter (fun i => table i j = 0)).card = n / 3 ∧ (Finset.univ.filter (fun i => table i j = 1)).card = n / 3 ∧ (Finset.univ.filter (fun i => table i j = 2)).card = n / 3) ∧
    (∀ s : ℕ, 2 ≤ s ∧ s ≤ 2 * n → let diagonal := Finset.filter (fun p : Fin n × Fin n => p.1.val + p.2.val + 2 = s) (Finset.univ.product Finset.univ); diagonal.card % 3 = 0 → (diagonal.filter (fun p => table p.1 p.2 = 0)).card = diagonal.card / 3 ∧ (diagonal.filter (fun p => table p.1 p.2 = 1)).card = diagonal.card / 3 ∧ (diagonal.filter (fun p => table p.1 p.2 = 2)).card = diagonal.card / 3) ∧
    (∀ d : ℤ, -(n - 1) ≤ d ∧ d ≤ n - 1 → let diagonal := Finset.filter (fun p : Fin n × Fin n => (p.1.val : ℤ) - (p.2.val : ℤ) = d) (Finset.univ.product Finset.univ); diagonal.card % 3 = 0 → (diagonal.filter (fun p => table p.1 p.2 = 0)).card = diagonal.card / 3 ∧ (diagonal.filter (fun p => table p.1 p.2 = 1)).card = diagonal.card / 3 ∧ (diagonal.filter (fun p => table p.1 p.2 = 2)).card = diagonal.card / 3)

set_option maxHeartbeats 800000 in
theorem bridge (hn : 0 < n) (f : Fin n → Fin n → Fin 3) : ExplicitTable n f ↔ MODTable f := by
  have bal (cells : Finset (Fin n × Fin n)) : Balanced f cells ↔ (cells.filter (fun p => f p.1 p.2 = 0)).card = cells.card / 3 ∧ (cells.filter (fun p => f p.1 p.2 = 1)).card = cells.card / 3 ∧ (cells.filter (fun p => f p.1 p.2 = 2)).card = cells.card / 3 := by
    constructor
    · intro h; exact ⟨h 0, h 1, h 2⟩
    · rintro ⟨h0, h1, h2⟩ c; fin_cases c <;> assumption
  have row_iff (r : Fin n) : Balanced f (row r) ↔ ∀ c, (Finset.univ.filter (fun j => f r j = c)).card = n / 3 := by
    have hr : (row r).card = n := by
      rw [show row r = Finset.univ.map ⟨(fun j : Fin n => (r, j)), by intro a b h; exact congrArg Prod.snd h⟩ by
        ext p; simp [row]; constructor
        · intro h; refine ⟨p.2, ?_⟩; cases p; simpa using h.symm
        · rintro ⟨a, ha⟩; simpa [← ha]]
      simp
    have hc (c : Letter) : ((row r).filter (fun p => f p.1 p.2 = c)).card = (Finset.univ.filter (fun j => f r j = c)).card := by
      apply Finset.card_bij (fun p _ => p.2)
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hp, hpc⟩
        have hpr : p.1 = r := by simpa [row] using hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [hpr] using hpc
      · intro p hp q hq h; apply Prod.ext
        · have hpr : p.1 = r := by simpa [row] using (Finset.mem_filter.mp hp).1
          have hqr : q.1 = r := by simpa [row] using (Finset.mem_filter.mp hq).1
          exact hpr.trans hqr.symm
        · exact h
      · intro j hj; refine ⟨(r, j), ?_, rfl⟩; simpa [row] using hj
    simp only [Balanced, hr, hc]
  have col_iff (k : Fin n) : Balanced f (col k) ↔ ∀ c, (Finset.univ.filter (fun i => f i k = c)).card = n / 3 := by
    have hk : (col k).card = n := by
      rw [show col k = Finset.univ.map ⟨(fun i : Fin n => (i, k)), by intro a b h; exact congrArg Prod.fst h⟩ by
        ext p; simp [col]; constructor
        · intro h; refine ⟨p.1, ?_⟩; cases p; simpa using h.symm
        · rintro ⟨a, ha⟩; simpa [← ha]]
      simp
    have hc (c : Letter) : ((col k).filter (fun p => f p.1 p.2 = c)).card = (Finset.univ.filter (fun i => f i k = c)).card := by
      apply Finset.card_bij (fun p _ => p.1)
      · intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hp, hpc⟩
        have hpk : p.2 = k := by simpa [col] using hp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [hpk] using hpc
      · intro p hp q hq h; apply Prod.ext
        · exact h
        · have hpk : p.2 = k := by simpa [col] using (Finset.mem_filter.mp hp).1
          have hqk : q.2 = k := by simpa [col] using (Finset.mem_filter.mp hq).1
          exact hpk.trans hqk.symm
      · intro i hi; refine ⟨(i, k), ?_, rfl⟩; simpa [col] using hi
    simp only [Balanced, hk, hc]
  constructor
  · rintro ⟨hrow, hcol, hsum, hdiff⟩; refine ⟨?_, ?_, ?_, ?_⟩
    · intro r; rw [row_iff]; intro c; fin_cases c
      · exact (hrow r).1
      · exact (hrow r).2.1
      · exact (hrow r).2.2
    · intro k; rw [col_iff]; intro c; fin_cases c
      · exact (hcol k).1
      · exact (hcol k).2.1
      · exact (hcol k).2.2
    · intro s hdiv
      by_cases hle : s + 2 ≤ 2 * n
      · have hc := hsum (s + 2) ⟨by omega, hle⟩; dsimp at hc
        have heq : Finset.filter (fun p : Fin n × Fin n => p.1.val + p.2.val + 2 = s + 2) Finset.univ = diagSum (n := n) s := by ext p; simp [diagSum]
        rw [heq] at hc
        exact (bal _).mpr (hc (Nat.dvd_iff_mod_eq_zero.mp hdiv))
      · have he : diagSum (n := n) s = ∅ := by ext p; simp [diagSum]; omega
        simp [he, Balanced]
    · intro d hdiv
      by_cases hd : (-(n - 1) : ℤ) ≤ d ∧ d ≤ n - 1
      · have hc := hdiff d hd; dsimp at hc
        have heq : Finset.filter (fun p : Fin n × Fin n => (p.1.val : ℤ) - (p.2.val : ℤ) = d) Finset.univ = diagDiff (n := n) d := by ext p; simp [diagDiff]
        rw [heq] at hc
        exact (bal _).mpr (hc (Nat.dvd_iff_mod_eq_zero.mp hdiv))
      · have he : diagDiff (n := n) d = ∅ := by ext p; simp [diagDiff]; omega
        simp [he, Balanced]
  · rintro ⟨hrow, hcol, hsum, hdiff⟩; refine ⟨?_, ?_, ?_, ?_⟩
    · intro i; have h := (row_iff i).mp (hrow i); exact ⟨h 0, h 1, h 2⟩
    · intro j; have h := (col_iff j).mp (hcol j); exact ⟨h 0, h 1, h 2⟩
    · intro s hs; dsimp; intro hmod
      have heq : Finset.filter (fun p : Fin n × Fin n => p.1.val + p.2.val + 2 = s) Finset.univ = diagSum (n := n) (s - 2) := by ext p; simp [diagSum]; omega
      rw [heq] at hmod ⊢
      exact (bal _).mp (hsum (s - 2) (Nat.dvd_iff_mod_eq_zero.mpr hmod))
    · intro d hd; dsimp; intro hmod
      have heq : Finset.filter (fun p : Fin n × Fin n => (p.1.val : ℤ) - (p.2.val : ℤ) = d) Finset.univ = diagDiff (n := n) d := by ext p; simp [diagDiff]
      rw [heq] at hmod ⊢
      exact (bal _).mp (hdiff d (Nat.dvd_iff_mod_eq_zero.mpr hmod))

-- ===== assumed statement (antecedent) =====
theorem imo2016_p2_assumed (n : ℕ) (hn : 0 < n) :
    n ∈ solution ↔ ∃ f : Fin n → Fin n → Letter, MODTable f := sorry

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
  constructor
  · intro h
    by_contra hd
    have hn : 0 < n := Nat.pos_of_ne_zero (by
      intro hn
      subst n
      simp at hd)
    have he := h hn
    change ∃ f, Imo2016P2.ExplicitTable n f at he
    have hm : ∃ f : Fin n → Fin n → Imo2016P2.Letter,
        Imo2016P2.MODTable (n := n) f := by
      simpa only [Imo2016P2.bridge hn] using he
    exact hd ((Imo2016P2.imo2016_p2_assumed n hn).mpr hm)
  · intro hdiv hn
    change ∃ f, Imo2016P2.ExplicitTable n f
    simpa only [Imo2016P2.bridge hn] using
      (Imo2016P2.imo2016_p2_assumed n hn).mp hdiv

