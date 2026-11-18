import Mathlib

open Filter

-- ===== unified context (both sides' local defs, merged) =====
namespace Erdos454

noncomputable def f (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else ⨅ i : {i : Fin n // 0 < (i : ℕ)}, (n + i).nth Prime + (n - i).nth Prime

noncomputable def f_cand (n : ℕ) : ℕ := ⨅ i : Fin n, (n + i).nth Prime + (n - i).nth Prime

-- ===== assumed statement (antecedent) =====
theorem erdos_454_assumed :
    limsup (fun n => (f n - 2 * n.nth Prime : ℕ∞)) atTop = ⊤ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem erdos_454 :
    limsup (fun n => f_cand n - 2 * (n.nth Prime : ℕ∞)) atTop = ⊤ := by
  -- not proved: the candidate infimum includes i = 0, forcing every subtracted term to be zero
  sorry

end Erdos454
