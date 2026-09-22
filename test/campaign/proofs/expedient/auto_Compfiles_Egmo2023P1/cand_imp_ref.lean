import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem Egmo2023P1_assumed (n : ℕ) (hn : 3 ≤ n) (a b : ZMod n → ℝ)
    (ha : ∀ i, 0 < a i)
    (hb : ∀ i, b i = (a (i - 1) + a (i + 1)) / a i)
    (hab : ∀ i j, a i ≤ a j ↔ b i ≤ b j) :
    ∀ i j, a i = a j := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Egmo2023P1_refs (n : ℕ) [NeZero n] (_ : n ≥ 3) (a : Fin n → ℝ) (ha : ∀ i, a i > 0)
    (b : Fin n → ℝ) (hb : ∀ i, b i = (a (i - 1) + a (i + 1)) / (a i))
    (h : ∀ i j, a i ≤ a j ↔ b i ≤ b j) : ∀ i j, a i = a j := by
  let e := ZMod.finEquiv n
  have hz := Egmo2023P1_assumed n ‹n ≥ 3› (fun i => a (e.symm i))
    (fun i => b (e.symm i)) (by intro i; exact ha (e.symm i))
    (by intro i; simpa [e] using hb (e.symm i))
    (by intro i j; exact h (e.symm i) (e.symm j))
  intro i j
  simpa using hz (e i) (e j)
