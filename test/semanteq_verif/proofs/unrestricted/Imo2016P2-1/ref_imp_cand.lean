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
  intro n
  rcases n with _ | n
  · simp
  have hn : 0 < n + 1 := by omega
  simp only [hn, true_implies]
  have href := Imo2016P2.imo2016_p2_assumed (n + 1) hn
  change (9 ∣ n + 1 ↔ ∃ f : Fin (n + 1) → Fin (n + 1) → Fin 3,
    Imo2016P2.MODTable f) at href
  rw [href]
  apply exists_congr
  intro f
  classical
  have hrow (i : Fin (n + 1)) (c : Fin 3) :
      (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
        p.1 = i ∧ f p.1 p.2 = c)).card =
      (Finset.univ.filter (fun j : Fin (n + 1) => f i j = c)).card := by
    rw [show Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
      p.1 = i ∧ f p.1 p.2 = c) = {i} ×ˢ Finset.univ.filter (fun j => f i j = c) by
        ext ⟨a, b⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_product, Finset.mem_singleton]
        aesop]
    simp
  have hrowTotal (i : Fin (n + 1)) :
      (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 = i)).card = n + 1 := by
    rw [show Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1 = i) =
      {i} ×ˢ Finset.univ by ext ⟨a, b⟩; simp [eq_comm]]
    simp
  have hcol (j : Fin (n + 1)) (c : Fin 3) :
      (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
        p.2 = j ∧ f p.1 p.2 = c)).card =
      (Finset.univ.filter (fun i : Fin (n + 1) => f i j = c)).card := by
    rw [show Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
      p.2 = j ∧ f p.1 p.2 = c) =
        (Finset.univ.filter (fun i => f i j = c)) ×ˢ {j} by
          ext ⟨a, b⟩
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.mem_product, Finset.mem_singleton]
          constructor
          · rintro ⟨h1, h2⟩
            subst b
            exact ⟨h2, rfl⟩
          · rintro ⟨h2, h1⟩
            subst b
            exact ⟨rfl, h2⟩]
    simp
  have hcolTotal (j : Fin (n + 1)) :
      (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.2 = j)).card = n + 1 := by
    rw [show Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.2 = j) =
      Finset.univ ×ˢ {j} by ext ⟨a, b⟩; simp [eq_comm]]
    simp
  have hsum (s : ℕ) :
      Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
        (p.1.val + p.2.val : ℤ) = (s : ℤ)) =
      Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) => p.1.val + p.2.val = s) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have hsumColor (s : ℕ) (c : Fin 3) :
      Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
        (p.1.val + p.2.val : ℤ) = (s : ℤ) ∧ f p.1 p.2 = c) =
      Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
        p.1.val + p.2.val = s ∧ f p.1 p.2 = c) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  simp only [Imo2016P2.MODTable, Imo2016P2.Balanced, Imo2016P2.row,
    Imo2016P2.col, Imo2016P2.diagSum, Imo2016P2.diagDiff,
    Finset.filter_filter, Nat.dvd_iff_mod_eq_zero]
  constructor
  · rintro ⟨hr, hc, hs, hd⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro r c
      fin_cases c
      · simpa only [hrow, hrowTotal] using (hr r).1
      · simpa only [hrow, hrowTotal] using (hr r).2.1
      · simpa only [hrow, hrowTotal] using (hr r).2.2
    · intro k c
      fin_cases c
      · simpa only [hcol, hcolTotal] using (hc k).1
      · simpa only [hcol, hcolTotal] using (hc k).2.1
      · simpa only [hcol, hcolTotal] using (hc k).2.2
    · intro s hmod c
      have h := hs (s : ℤ)
      rw [hsum] at h
      specialize h hmod
      fin_cases c
      · simpa only [hsumColor] using h.1
      · simpa only [hsumColor] using h.2.1
      · simpa only [hsumColor] using h.2.2
    · intro d hmod c
      have h := hd d hmod
      fin_cases c
      · exact h.1
      · exact h.2.1
      · exact h.2.2
  · rintro ⟨hr, hc, hs, hd⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have h0 := hr i (0 : Fin 3)
      have h1 := hr i (1 : Fin 3)
      have h2 := hr i (2 : Fin 3)
      simp only [hrow, hrowTotal] at h0 h1 h2
      exact ⟨h0, h1, h2⟩
    · intro j
      have h0 := hc j (0 : Fin 3)
      have h1 := hc j (1 : Fin 3)
      have h2 := hc j (2 : Fin 3)
      simp only [hcol, hcolTotal] at h0 h1 h2
      exact ⟨h0, h1, h2⟩
    · intro z hmod
      cases z with
      | ofNat s =>
          change (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
            (p.1.val + p.2.val : ℤ) = (s : ℤ))).card % 3 = 0 at hmod
          change
            (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
              (p.1.val + p.2.val : ℤ) = (s : ℤ) ∧ f p.1 p.2 = 0)).card =
                (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
                  (p.1.val + p.2.val : ℤ) = (s : ℤ))).card / 3 ∧
            (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
              (p.1.val + p.2.val : ℤ) = (s : ℤ) ∧ f p.1 p.2 = 1)).card =
                (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
                  (p.1.val + p.2.val : ℤ) = (s : ℤ))).card / 3 ∧
            (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
              (p.1.val + p.2.val : ℤ) = (s : ℤ) ∧ f p.1 p.2 = 2)).card =
                (Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
                  (p.1.val + p.2.val : ℤ) = (s : ℤ))).card / 3
          rw [hsum] at hmod ⊢
          have h0 := hs s hmod (0 : Fin 3)
          have h1 := hs s hmod (1 : Fin 3)
          have h2 := hs s hmod (2 : Fin 3)
          simp only [hsumColor] at h0 h1 h2 ⊢
          exact ⟨h0, h1, h2⟩
      | negSucc s =>
          have he : Finset.univ.filter (fun p : Fin (n + 1) × Fin (n + 1) =>
              (p.1.val + p.2.val : ℤ) = Int.negSucc s) = ∅ := by
            ext p
            constructor
            · intro hp
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
              omega
            · intro hp
              simp at hp
          have hec (c : Fin 3) : Finset.univ.filter
              (fun p : Fin (n + 1) × Fin (n + 1) =>
                (p.1.val + p.2.val : ℤ) = Int.negSucc s ∧ f p.1 p.2 = c) = ∅ := by
            ext p
            constructor
            · intro hp
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
              omega
            · intro hp
              simp at hp
          simp only [he, hec, Finset.card_empty, Nat.zero_div]
          exact ⟨trivial, trivial, trivial⟩
    · intro d hmod
      have h0 := hd d hmod (0 : Fin 3)
      have h1 := hd d hmod (1 : Fin 3)
      have h2 := hd d hmod (2 : Fin 3)
      exact ⟨h0, h1, h2⟩
