import Mathlib

theorem Usa1996P1_alt :
    ∑ n ∈ Finset.range 90,
      (2 * (n+1)) * Real.sin ((2 * (n+1)) * Real.pi / 180) / 90
    = 1 / Real.tan (Real.pi / 180) := by
  sorry
