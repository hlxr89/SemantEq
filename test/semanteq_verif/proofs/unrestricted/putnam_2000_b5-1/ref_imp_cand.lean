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
  by
    sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement (S₀ : Set ℕ) (hS₀ : S₀.Finite) (hS₀_pos : ∀ x ∈ S₀, x > 0) :
  Set.Infinite {N : ℕ | S_seq S₀ N = S₀ ∪ {N + a | a ∈ S₀}} := by
  have hpos : ∀ n x, x ∈ S_seq S₀ n → x > 0 := by
    intro n
    induction n with
    | zero => exact hS₀_pos
    | succ n ih =>
        intro x hx
        simp only [S_seq, Set.mem_setOf_eq] at hx
        rcases hx with hx | hx
        · exact hx.1
        · rcases hx with ⟨_, hxin⟩
          exact ih x hxin
  have hfin : ∀ n, (S_seq S₀ n).Finite := by
    intro n
    induction n with
    | zero => exact hS₀
    | succ n ih =>
        apply (ih.union (ih.image (fun x : ℕ => x + 1))).subset
        intro x hx
        simp only [S_seq, Set.mem_setOf_eq] at hx
        rcases hx with hx | hx
        · right
          refine ⟨x - 1, hx.2.1, ?_⟩
          exact Nat.sub_add_cancel (by omega : 1 ≤ x)
        · left
          exact hx.2
  let T : ℕ → Set ℤ := fun n => {z : ℤ | 0 < z ∧ z.toNat ∈ S_seq S₀ n}
  have hTfin : ∀ n, (T n).Finite := by
    intro n
    apply (hfin n).image (fun x : ℕ => (x : ℤ)) |>.subset
    intro z hz
    change 0 < z ∧ z.toNat ∈ S_seq S₀ n at hz
    refine ⟨z.toNat, hz.2, ?_⟩
    exact Int.toNat_of_nonneg (by omega)
  have hTpos : ∀ n, ∀ z ∈ T n, z > 0 := by
    intro n z hz
    exact hz.1
  have hTdef : ∀ n, ∀ z, z ∈ T (n + 1) ↔ Xor' (z - 1 ∈ T n) (z ∈ T n) := by
    intro n z
    change (0 < z ∧ z.toNat ∈ S_seq S₀ (n + 1)) ↔
      Xor' (0 < z - 1 ∧ (z - 1).toNat ∈ S_seq S₀ n)
        (0 < z ∧ z.toNat ∈ S_seq S₀ n)
    by_cases hz : 0 < z
    · have hsub : (z - 1).toNat = z.toNat - 1 := by omega
      simp only [S_seq, Set.mem_setOf_eq, hsub]
      constructor
      · intro h
        rcases h with ⟨_, h⟩
        rcases h with h | h
        · have hmpos := hpos n (z.toNat - 1) h.2.1
          exact Or.inl ⟨⟨by omega, h.2.1⟩, fun hp => h.2.2 hp.2⟩
        · exact Or.inr ⟨⟨hz, h.2⟩, fun hp => h.1 hp.2⟩
      · intro h
        refine ⟨hz, ?_⟩
        rcases h with h | h
        · exact Or.inl ⟨by omega, h.1.2, fun hp => h.2 ⟨hz, hp⟩⟩
        · exact Or.inr ⟨(fun hp => h.2 ⟨by have := hpos n _ hp; omega, hp⟩), h.1.2⟩
    · have hsub : ¬ 0 < z - 1 := by omega
      have hone : ¬ 1 < z := by omega
      simp [hz, hsub, hone]
  have hmain := putnam_2000_b5_assumed T hTfin hTpos hTdef
  apply Set.infinite_of_forall_exists_gt
  intro n
  obtain ⟨N, hN, heq⟩ := hmain (n + 1)
  refine ⟨N, ?_, Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hN⟩
  ext x
  have hxcast : (0 : ℤ) < (x : ℤ) ↔ 0 < x := by omega
  have hto : ((x : ℤ).toNat) = x := by omega
  have hxT : (x : ℤ) ∈ T N ↔ x ∈ S_seq S₀ N := by
    change (0 < (x : ℤ) ∧ (x : ℤ).toNat ∈ S_seq S₀ N) ↔ _
    simp only [hxcast, hto]
    exact ⟨fun h => h.2, fun h => ⟨hpos N x h, h⟩⟩
  rw [← hxT, heq]
  change ((x : ℤ) ∈ T 0 ∪ {M : ℤ | M - N ∈ T 0}) ↔ _
  simp only [Set.mem_union, Set.mem_setOf_eq, T, S_seq, hxcast, hto]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h.2
    · right
      have hdiff : ((x : ℤ) - (N : ℤ)).toNat = x - N := by omega
      refine ⟨x - N, ?_, by omega⟩
      simpa only [hdiff] using h.2
  · intro h
    rcases h with h | ⟨a, ha, hxa⟩
    · exact Or.inl ⟨hS₀_pos x h, h⟩
    · right
      subst x
      constructor
      · have hapos := hS₀_pos a ha
        omega
      · have hdiff : (((N + a : ℕ) : ℤ) - (N : ℤ)).toNat = a := by omega
        simpa only [hdiff] using ha
