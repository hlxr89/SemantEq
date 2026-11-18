import Mathlib

open Set Nat Polynomial Filter Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1974_b4_assumed
(f : ℝ × ℝ → ℝ)
(hfcontx : ∀ y : ℝ, Continuous (fun x => f ⟨x, y⟩))
(hfconty : ∀ x : ℝ, Continuous (fun y => f ⟨x, y⟩))
: ∃ g : ℕ → (ℝ × ℝ → ℝ), (∀ n : ℕ, Continuous (g n)) ∧ (∀ x y : ℝ, Tendsto (fun n => g n ⟨x, y⟩) atTop (𝓝 (f ⟨x, y⟩))) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (f : ℝ × ℝ → ℝ) 
  (h1 : ∀ y, Continuous (fun p : ℝ × ℝ => f (p.1, y)))
  (h2 : ∀ x, Continuous (fun p : ℝ × ℝ => f (x, p.2))) :
  ∃ g : ℕ → (ℝ × ℝ → ℝ), 
    (∀ n, Continuous (g n)) ∧ 
    (∀ x y, Filter.Tendsto (fun n => g n (x, y)) Filter.atTop (nhds (f (x, y)))) := by
  apply putnam_1974_b4_assumed f
  · intro y
    have hemb : Continuous (fun x : ℝ => (x, (0 : ℝ))) :=
      continuous_id.prodMk continuous_const
    simpa using (h1 y).comp hemb
  · intro x
    have hemb : Continuous (fun y : ℝ => ((0 : ℝ), y)) :=
      continuous_const.prodMk continuous_id
    simpa using (h2 x).comp hemb
