import Mathlib

open Topology Filter Nat Set Function

-- ===== unified context (both sides' local defs, merged) =====
def S_seq (S₀ : Set ℕ) : ℕ → Set ℕ
  | 0 => S₀
  | n + 1 => {a : ℕ | a > 0 ∧ (a - 1 ∈ S_seq S₀ n ∧ a ∉ S_seq S₀ n) ∨ (a - 1 ∉ S_seq S₀ n ∧ a ∈ S_seq S₀ n)}

-- ===== assumed statement (antecedent) =====
theorem putnam_2000_b5_assumed
(S : ℕ → Set ℤ)
(hSfin : ∀ n, Set.Finite (S n))
(hSpos : ∀ n, ∀ s ∈ S n, s > 0)
(hSdef : ∀ n, ∀ a, a ∈ S (n + 1) ↔ Xor' (a - 1 ∈ S n) (a ∈ S n))
: (∀ n, ∃ N ≥ n, S N = S 0 ∪ {M : ℤ | M - N ∈ S 0}) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (S₀ : Set ℕ) (hS₀ : S₀.Finite) (hS₀_pos : ∀ x ∈ S₀, x > 0) :
  Set.Infinite {N : ℕ | S_seq S₀ N = S₀ ∪ {N + a | a ∈ S₀}} := by
  classical
  have hseqfin : ∀ n, (S_seq S₀ n).Finite := by
    intro n
    induction n with
    | zero => exact hS₀
    | succ n ih =>
        rw [S_seq]
        apply ((ih.image fun a : ℕ => a + 1).union ih).subset
        intro a ha
        simp only [Set.mem_setOf_eq] at ha
        rcases ha with ⟨ha_pos, ha_prev, ha_not⟩ | ⟨ha_prev, ha⟩
        · left
          refine ⟨a - 1, ha_prev, ?_⟩
          change (a - 1) + 1 = a
          omega
        · exact Or.inr ha
  have hseqpos : ∀ n a, a ∈ S_seq S₀ n → a > 0 := by
    intro n
    induction n with
    | zero => exact hS₀_pos
    | succ n ih =>
        intro a ha
        simp only [S_seq, Set.mem_setOf_eq] at ha
        rcases ha with ha | ⟨_, ha⟩
        · exact ha.1
        · exact ih a ha
  let T : ℕ → Set ℤ := fun n => (fun a : ℕ => (a : ℤ)) '' S_seq S₀ n
  have hTmem : ∀ n (a : ℕ), (a : ℤ) ∈ T n ↔ a ∈ S_seq S₀ n := by
    intro n a
    simp [T]
  have hTfin : ∀ n, (T n).Finite := by
    intro n
    exact (hseqfin n).image (fun a : ℕ => (a : ℤ))
  have hTpos : ∀ n, ∀ z ∈ T n, z > 0 := by
    intro n z hz
    rcases hz with ⟨a, ha, rfl⟩
    have h := hseqpos n a ha
    change (a : ℤ) > 0
    exact_mod_cast h
  have hTdef : ∀ n, ∀ z, z ∈ T (n + 1) ↔ Xor' (z - 1 ∈ T n) (z ∈ T n) := by
    intro n z
    by_cases hz : z ≤ 0
    · have hz0 : z ∉ T n := by
        intro h
        have := hTpos n z h
        omega
      have hz1 : z - 1 ∉ T n := by
        intro h
        have := hTpos n (z - 1) h
        omega
      have hznext : z ∉ T (n + 1) := by
        intro h
        have := hTpos (n + 1) z h
        omega
      simp [hz0, hz1, hznext, Xor']
    · have hzpos : 0 < z := by omega
      lift z to ℕ using le_of_lt hzpos with a
      have hapos : 0 < a := by exact_mod_cast hzpos
      rw [hTmem]
      simp only [S_seq, Set.mem_setOf_eq, hapos, true_and]
      have hpred : ((a : ℤ) - 1 ∈ T n) ↔ a - 1 ∈ S_seq S₀ n := by
        have heq : (a : ℤ) - 1 = ((a - 1 : ℕ) : ℤ) := by omega
        rw [heq, hTmem]
      rw [hpred, hTmem]
      simp [Xor']
      tauto
  have href := putnam_2000_b5_assumed T hTfin hTpos hTdef
  apply Set.infinite_of_forall_exists_gt
  intro n
  obtain ⟨N, hN, hreturn⟩ := href (n + 1)
  refine ⟨N, ?_, by omega⟩
  change S_seq S₀ N = S₀ ∪ {N + a | a ∈ S₀}
  ext a
  have heq := Set.ext_iff.mp hreturn (a : ℤ)
  rw [hTmem] at heq
  change (a ∈ S_seq S₀ N) ↔ _
  constructor
  · intro ha
    have hrhs := heq.mp ha
    rcases hrhs with ha0 | hashift
    · left
      simpa [T, S_seq] using ha0
    · right
      change (a : ℤ) - N ∈ T 0 at hashift
      rcases hashift with ⟨b, hb, hba⟩
      have hashift' : ∃ b ∈ S₀, (a : ℤ) - N = (b : ℤ) :=
        ⟨b, hb, hba.symm⟩
      rcases hashift' with ⟨b, hb, hab⟩
      refine ⟨b, hb, ?_⟩
      omega
  · intro ha
    apply heq.mpr
    rcases ha with ha | ⟨b, hb, hab⟩
    · left
      simpa [T, S_seq] using ha
    · right
      have hab' : (a : ℤ) - N = (b : ℤ) := by omega
      simp only [T, S_seq, Set.mem_image]
      exact ⟨b, hb, hab'.symm⟩
