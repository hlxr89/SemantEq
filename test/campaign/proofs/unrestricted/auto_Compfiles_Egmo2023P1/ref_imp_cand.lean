import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem Egmo2023P1_refs_assumed (n : ℕ) [NeZero n] (_ : n ≥ 3) (a : Fin n → ℝ) (ha : ∀ i, a i > 0)
    (b : Fin n → ℝ) (hb : ∀ i, b i = (a (i - 1) + a (i + 1)) / (a i))
    (h : ∀ i j, a i ≤ a j ↔ b i ≤ b j) : ∀ i j, a i = a j := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem Egmo2023P1 (n : ℕ) (hn : 3 ≤ n) (a b : ZMod n → ℝ)
    (ha : ∀ i, 0 < a i)
    (hb : ∀ i, b i = (a (i - 1) + a (i + 1)) / a i)
    (hab : ∀ i j, a i ≤ a j ↔ b i ≤ b j) :
    ∀ i j, a i = a j := by
  letI : NeZero n := ⟨by omega⟩
  let e : Fin n ≃+* ZMod n := ZMod.finEquiv n
  have hfin : ∀ i j : Fin n, a (e i) = a (e j) :=
    Egmo2023P1_refs_assumed n hn (fun i => a (e i)) (fun i => ha (e i))
      (fun i => b (e i)) (by
        intro i
        simpa only [map_sub, map_one, map_add] using hb (e i))
      (fun i j => hab (e i) (e j))
  intro i j
  simpa only [e.apply_symm_apply] using hfin (e.symm i) (e.symm j)
