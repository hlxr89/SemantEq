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
  (h1 : ∀ x, Continuous (fun y => f (x, y)))
  (h2 : ∀ y, Continuous (fun x => f (x, y))) :
  ∃ (g : ℕ → ℝ × ℝ → ℝ), (∀ n, Continuous (g n)) ∧
    (∀ x y, Filter.Tendsto (fun n => g n (x, y)) Filter.atTop (nhds (f (x, y)))) := by
  simpa only using (putnam_1974_b4_assumed f h2 h1)
