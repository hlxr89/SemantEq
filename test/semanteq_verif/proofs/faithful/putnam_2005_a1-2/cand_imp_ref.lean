import Mathlib

open Nat

-- ===== unified context (both sides' local defs, merged) =====
def IsPow23 (n : ℕ) : Prop :=
  ∃ r s : ℕ, n = 2^r * 3^s

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (n : ℕ) (hn : 0 < n) :
  ∃ S : Finset ℕ,
    (∀ x ∈ S, IsPow23 x) ∧
    (∀ x y : ℕ, x ∈ S → y ∈ S → x ≠ y → ¬(x ∣ y)) ∧
    S.sum id = n :=
by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2005_a1
: ∀ n : ℤ, n > 0 → (∃ k : ℕ, ∃ a : Fin k → Fin 2 → ℕ, n = ∑ i : Fin k, 2^(a i 0)*3^(a i 1) ∧
(∀ i j : Fin k, i ≠ j → ¬(2^(a i 0)*3^(a i 1) ∣ 2^(a j 0)*3^(a j 1)))) :=
by
  intro n hn
  have hn0 : 0 ≤ n := le_of_lt hn
  have hnt : 0 < n.toNat := by omega
  obtain ⟨S, hpow, hndiv, hsum⟩ := problem_statement_assumed n.toNat hnt
  let e : Fin S.card ≃o ↥S := S.orderIsoOfFin rfl
  choose r s hrs using fun i : Fin S.card => hpow (e i) (e i).property
  let a : Fin S.card → Fin 2 → ℕ := fun i j => if j = 0 then r i else s i
  refine ⟨S.card, a, ?_, ?_⟩
  · have hsum' : (∑ i : Fin S.card, 2^(r i)*3^(s i)) = n.toNat := by
      calc
        (∑ i : Fin S.card, 2^(r i)*3^(s i)) = ∑ i : Fin S.card, (e i).val :=
          Finset.sum_congr rfl (fun i _ => (hrs i).symm)
        _ = ∑ x : ↥S, x.val := Equiv.sum_comp e.toEquiv (fun x : ↥S => x.val)
        _ = S.sum id := Finset.sum_coe_sort S id
        _ = n.toNat := hsum
    change n = (↑(∑ i : Fin S.card, 2^(r i)*3^(s i)) : ℤ)
    calc
      n = (n.toNat : ℤ) := (Int.toNat_of_nonneg hn0).symm
      _ = (↑(∑ i : Fin S.card, 2^(r i)*3^(s i)) : ℤ) := by exact_mod_cast hsum'.symm
  · intro i j hij
    have hval : (e i).val ≠ (e j).val := by
      intro h
      apply hij
      exact e.injective (Subtype.ext h)
    have hd := hndiv (e i).val (e j).val (e i).property (e j).property hval
    simpa [a, hrs i, hrs j] using hd
