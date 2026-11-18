import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {G : Type*} [Group G] (h : Nat.card G = 2907) : ∃ H : Subgroup G, H.Normal ∧ H ≠ ⊥ := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_4_5_21 {G : Type*} [Fintype G] [Group G]
  (hG : card G = 2907) : ¬ IsSimpleGroup G := by
  classical
  intro hs
  letI : IsSimpleGroup G := hs
  letI : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  let P : Sylow 19 G := default
  have hcardG : Nat.card G = 2907 := by simpa using hG
  have hcardP : Nat.card P = 19 := by
    rw [P.card_eq_multiplicity, hcardG]
    native_decide
  have hPbot : (P : Subgroup G) ≠ ⊥ := by
    intro heq
    have : Nat.card P = 1 := by rw [heq]; simp
    omega
  have hPtop : (P : Subgroup G) ≠ ⊤ := by
    intro heq
    have : Nat.card P = Nat.card G := by rw [heq]; simp
    omega
  have hPnormal : ¬ (P : Subgroup G).Normal := by
    intro hn
    rcases hn.eq_bot_or_eq_top with h | h
    · exact hPbot h
    · exact hPtop h
  have hn_ne_one : Nat.card (Sylow 19 G) ≠ 1 := by
    intro hn
    letI : Subsingleton (Sylow 19 G) := (Nat.card_eq_one_iff_unique.mp hn).1
    exact hPnormal P.normal_of_subsingleton
  have hindexP : P.index = 153 := by
    have hm := P.card_mul_index
    rw [hcardP, hcardG] at hm
    omega
  have hdvd : Nat.card (Sylow 19 G) ∣ 153 := by
    simpa [hindexP] using P.card_dvd_index
  have hmod : Nat.card (Sylow 19 G) % 19 = 1 := by
    have hm := card_sylow_modEq_one 19 G
    change Nat.card (Sylow 19 G) % 19 = 1 % 19 at hm
    simpa using hm
  have hone_le : 1 ≤ Nat.card (Sylow 19 G) := by omega
  have hmoddvd : 19 ∣ Nat.card (Sylow 19 G) - 1 := by
    apply (Nat.modEq_iff_dvd' hone_le).mp
    exact (card_sylow_modEq_one 19 G).symm
  have hcardSylow : Nat.card (Sylow 19 G) = 153 := by
    have hnmem : Nat.card (Sylow 19 G) ∈ Nat.divisors 153 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    have hdivisors : Nat.divisors 153 =
        ({1, 3, 9, 17, 51, 153} : Finset ℕ) := by native_decide
    rw [hdivisors] at hnmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hnmem
    rcases hnmem with h | h | h | h | h | h <;> omega
  have hindexN : (P : Subgroup G).normalizer.index = 153 := by
    rw [← P.card_eq_index_normalizer]
    exact hcardSylow
  have hcardN : Nat.card (P : Subgroup G).normalizer = 19 := by
    have hm := (P : Subgroup G).normalizer.card_mul_index
    rw [hindexN, hcardG] at hm
    omega
  have hnormalizer : (P : Subgroup G).normalizer = P := by
    symm
    apply Subgroup.eq_of_le_of_card_ge P.le_normalizer
    omega
  letI : IsCyclic P := isCyclic_of_prime_card hcardP
  letI : CommGroup P := IsCyclic.commGroup
  have hcent : (P : Subgroup G).normalizer ≤ Subgroup.centralizer (P : Set G) := by
    rw [hnormalizer]
    intro x hx y hy
    simpa using congrArg Subtype.val
      (mul_comm (⟨y, hy⟩ : P) (⟨x, hx⟩ : P))
  let K : Subgroup G := (MonoidHom.transferSylow P hcent).ker
  have hcomp : IsComplement' K P := MonoidHom.ker_transferSylow_isComplement' P hcent
  have hKnormal : K.Normal := MonoidHom.normal_ker _
  rcases hKnormal.eq_bot_or_eq_top with hK | hK
  · have : (P : Subgroup G) = ⊤ := by
      simpa [K, hK] using hcomp.sup_eq_top
    exact hPtop this
  · have : (P : Subgroup G) = ⊥ := by
      have hd := hcomp.disjoint
      rw [hK] at hd
      simpa using hd
    exact hPbot this
