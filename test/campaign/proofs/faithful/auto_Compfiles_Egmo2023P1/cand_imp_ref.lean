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
  let e : Fin n ≃+* ZMod n := ZMod.finEquiv n
  have hc := Egmo2023P1_assumed n ‹n ≥ 3› (a ∘ e.symm) (b ∘ e.symm)
    (fun i => ha (e.symm i))
    (fun i => by simpa [Function.comp_def] using hb (e.symm i))
    (fun i j => h (e.symm i) (e.symm j))
  intro i j
  simpa using hc (e i) (e j)
