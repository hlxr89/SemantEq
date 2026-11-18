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
: (∀ n, ∃ N ≥ n, S N = S 0 ∪ {M : ℤ | M - N ∈ S 0}) :=
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (S₀ : Set ℕ) (hS₀ : S₀.Finite) (hS₀_pos : ∀ x ∈ S₀, x > 0) :
  Set.Infinite {N : ℕ | S_seq S₀ N = S₀ ∪ {N + a | a ∈ S₀}} := by
  have hfin : ∀ n, (S_seq S₀ n).Finite := by
    intro n
    induction n with
    | zero => simpa [S_seq] using hS₀
    | succ n ih =>
        apply (ih.union (ih.image fun x : ℕ => x + 1)).subset
        intro a ha
        simp only [S_seq, Set.mem_setOf_eq] at ha
        rcases ha with ha | ha
        · right
          exact ⟨a - 1, ha.2.1, Nat.sub_add_cancel (by omega)⟩
        · left
          exact ha.2
  have hpos : ∀ n, ∀ a ∈ S_seq S₀ n, a > 0 := by
    intro n
    induction n with
    | zero => simpa [S_seq] using hS₀_pos
    | succ n ih =>
        intro a ha
        simp only [S_seq, Set.mem_setOf_eq] at ha
        rcases ha with ha | ha
        · exact ha.1
        · exact ih a ha.2
  let T : ℕ → Set ℤ := fun n => (fun a : ℕ => (a : ℤ)) '' S_seq S₀ n
  have hTfin : ∀ n, (T n).Finite := fun n => (hfin n).image fun a : ℕ => (a : ℤ)
  have hTpos : ∀ n, ∀ z ∈ T n, z > 0 := by
    intro n z hz
    rcases hz with ⟨a, ha, rfl⟩
    change (a : ℤ) > 0
    exact_mod_cast hpos n a ha
  have hTmem : ∀ n (a : ℕ), (a : ℤ) ∈ T n ↔ a ∈ S_seq S₀ n := by
    intro n a
    simp [T]
  have hTdef : ∀ n, ∀ z, z ∈ T (n + 1) ↔ Xor' (z - 1 ∈ T n) (z ∈ T n) := by
    intro n z
    rcases z with (a | a)
    · cases a with
      | zero =>
          have hz0 : ∀ k, (0 : ℤ) ∉ T k := by
            intro k hk
            have := hTpos k 0 hk
            omega
          have hzm1 : (-1 : ℤ) ∉ T n := by
            intro hk
            have := hTpos n (-1) hk
            omega
          simp [hz0, hzm1, Xor']
      | succ a =>
          have heq : (Int.ofNat (Nat.succ a) - 1) = (a : ℤ) := by
            change ((a : ℤ) + 1) - 1 = (a : ℤ)
            omega
          rw [heq, hTmem]
          change ((a + 1 : ℕ) : ℤ) ∈ T (n + 1) ↔
            Xor' (a ∈ S_seq S₀ n) (((a + 1 : ℕ) : ℤ) ∈ T n)
          rw [hTmem, hTmem]
          simp [S_seq, Xor']
          tauto
    · have hneg : ∀ k, Int.negSucc a ∉ T k := by
        intro k hk
        have := hTpos k (Int.negSucc a) hk
        omega
      have hneg' : Int.negSucc a - 1 ∉ T n := by
        intro hk
        have := hTpos n (Int.negSucc a - 1) hk
        omega
      have hneg2 : Int.negSucc (a + 1) ∉ T n := by
        intro hk
        have := hTpos n (Int.negSucc (a + 1)) hk
        omega
      simp [hneg, hneg', hneg2, Xor']
  have href := putnam_2000_b5_assumed T hTfin hTpos hTdef
  rw [Set.infinite_iff_exists_gt]
  intro n
  obtain ⟨N, hN, hEq⟩ := href (n + 1)
  refine ⟨N, ?_, by omega⟩
  ext a
  have hm := Set.ext_iff.mp hEq (a : ℤ)
  simp only [T, Set.mem_image, Nat.cast_inj, exists_eq_right,
    Set.mem_union, Set.mem_setOf_eq] at hm
  simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf, S_seq]
  rw [hm]
  change (a ∈ S₀ ∨ ∃ x ∈ S₀, (x : ℤ) = (a : ℤ) - (N : ℤ)) ↔
    a ∈ S₀ ∨ ∃ x ∈ S₀, N + x = a
  constructor
  · rintro (ha | ⟨x, hx, heq⟩)
    · exact Or.inl ha
    · right
      refine ⟨x, hx, ?_⟩
      have hz : (x : ℤ) + (N : ℤ) = (a : ℤ) := eq_sub_iff_add_eq.mp heq
      have hn : x + N = a := by exact_mod_cast hz
      simpa [add_comm] using hn
  · rintro (ha | ⟨x, hx, heq⟩)
    · exact Or.inl ha
    · right
      refine ⟨x, hx, ?_⟩
      have hz : (N : ℤ) + (x : ℤ) = (a : ℤ) := by exact_mod_cast heq
      omega
