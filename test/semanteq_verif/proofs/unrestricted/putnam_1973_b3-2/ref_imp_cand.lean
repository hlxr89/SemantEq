import Mathlib

open Nat Set MeasureTheory Topology Filter

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem putnam_1973_b3_assumed
(p : ℕ)
(pgt1 : p > 1)
(hprime : ∀ x ∈ Set.Ico 0 p, Nat.Prime (x^2 - x + p))
: ∃! triple : ℤ × ℤ × ℤ, let (a,b,c) := triple; b^2 - 4*a*c = 1 - 4*p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (p : ℤ) (hp : p > 1) 
  (h_prime : ∀ x : ℤ, 0 < x ∧ x < p → Nat.Prime (Int.natAbs (x^2 - x + p))) :
  ∃! triple : ℤ × ℤ × ℤ, 
    let (a, b, c) := triple
    b^2 - 4*a*c = 1 - 4*p ∧ 0 < a ∧ a ≤ c ∧ -a ≤ b ∧ b < a := by
  have hp0 : 0 ≤ p := by omega
  have habs : (p.natAbs : ℤ) = p := by
    simp [Int.natAbs_of_nonneg hp0]
  have hpNat : p.natAbs > 1 := by
    exact_mod_cast (show (p.natAbs : ℤ) > 1 by simpa [habs] using hp)
  have hPrimeNat : ∀ x ∈ Set.Ico 0 p.natAbs,
      Nat.Prime (x^2 - x + p.natAbs) := by
    intro x hx
    by_cases hxzero : x = 0
    · subst x
      have h := h_prime 1 (by omega)
      norm_num at h
      simpa using h
    · have hxpos : 0 < x := Nat.pos_of_ne_zero hxzero
      have hxle : x ≤ x ^ 2 := by nlinarith
      have hxltp : (x : ℤ) < p := by
        rw [← habs]
        exact_mod_cast hx.2
      have h := h_prime (x : ℤ) (by exact ⟨by exact_mod_cast hxpos, hxltp⟩)
      have hnonneg : 0 ≤ (x : ℤ)^2 - (x : ℤ) + p := by
        nlinarith
      have heq : Int.natAbs ((x : ℤ)^2 - (x : ℤ) + p) =
          x^2 - x + p.natAbs := by
        apply Int.ofNat_injective
        calc
          Int.ofNat (Int.natAbs ((x : ℤ)^2 - (x : ℤ) + p)) =
              (x : ℤ)^2 - (x : ℤ) + p := Int.natAbs_of_nonneg hnonneg
          _ = Int.ofNat (x^2 - x + p.natAbs) := by
            change (x : ℤ)^2 - (x : ℤ) + p =
              ((x^2 - x + p.natAbs : ℕ) : ℤ)
            push_cast [Nat.cast_sub hxle]
            rw [abs_of_nonneg hp0]
      simpa [heq] using h
  have h := putnam_1973_b3_assumed p.natAbs hpNat hPrimeNat
  simpa [habs] using h
