import Mathlib

open Filter Topology Set Nat

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_2008_b4_refs_assumed
(p : ℕ)
(hp : Nat.Prime p)
(h : Polynomial ℤ)
(hh : ∀ i j : Finset.range (p ^ 2), h.eval i ≡ h.eval j [ZMOD p ^ 2] → i = j)
: (∀ i j : Finset.range (p ^ 3), h.eval i ≡ h.eval j [ZMOD p ^ 3] → i = j) :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2008_b4 (p : ℕ) (hp : p.Prime) (h : Polynomial ℤ)
    (hh : ∀ i j : ℕ, i < p ^ 2 → j < p ^ 2 →
      h.eval (i : ℤ) ≡ h.eval (j : ℤ) [ZMOD (p : ℤ) ^ 2] → i = j) :
    ∀ i j : ℕ, i < p ^ 3 → j < p ^ 3 →
      h.eval (i : ℤ) ≡ h.eval (j : ℤ) [ZMOD (p : ℤ) ^ 3] → i = j := by
  have href := putnam_2008_b4_refs_assumed p hp h (fun i j hij =>
    Subtype.ext (hh i j (Finset.mem_range.mp i.property)
      (Finset.mem_range.mp j.property) hij))
  intro i j hi hj hij
  exact congrArg Subtype.val
    (href ⟨i, Finset.mem_range.mpr hi⟩ ⟨j, Finset.mem_range.mpr hj⟩ hij)
