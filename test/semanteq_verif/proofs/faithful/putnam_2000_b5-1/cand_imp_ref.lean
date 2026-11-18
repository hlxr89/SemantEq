import Mathlib

open Topology Filter Nat Set Function

-- ===== unified context (both sides' local defs, merged) =====
def S_seq (S₀ : Set ℕ) : ℕ → Set ℕ
  | 0 => S₀
  | n + 1 => {a : ℕ | a > 0 ∧ (a - 1 ∈ S_seq S₀ n ∧ a ∉ S_seq S₀ n) ∨ (a - 1 ∉ S_seq S₀ n ∧ a ∈ S_seq S₀ n)}

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed (S₀ : Set ℕ) (hS₀ : S₀.Finite) (hS₀_pos : ∀ x ∈ S₀, x > 0) :
  Set.Infinite {N : ℕ | S_seq S₀ N = S₀ ∪ {N + a | a ∈ S₀}} := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem putnam_2000_b5
(S : ℕ → Set ℤ)
(hSfin : ∀ n, Set.Finite (S n))
(hSpos : ∀ n, ∀ s ∈ S n, s > 0)
(hSdef : ∀ n, ∀ a, a ∈ S (n + 1) ↔ Xor' (a - 1 ∈ S n) (a ∈ S n))
: (∀ n, ∃ N ≥ n, S N = S 0 ∪ {M : ℤ | M - N ∈ S 0}) := by
  let S₀ : Set ℕ := {a : ℕ | (a : ℤ) ∈ S 0}
  have hS₀fin : S₀.Finite := by
    apply ((hSfin 0).image Int.toNat).subset
    intro a ha
    exact ⟨(a : ℤ), ha, by simp⟩
  have hS₀pos : ∀ a ∈ S₀, a > 0 := by
    intro a ha
    have hz := hSpos 0 (a : ℤ) ha
    exact_mod_cast hz
  have hseqpos : ∀ n, ∀ a ∈ S_seq S₀ n, a > 0 := by
    intro n
    induction n with
    | zero => simpa [S_seq] using hS₀pos
    | succ n ih =>
        intro a ha
        simp only [S_seq, Set.mem_setOf_eq] at ha
        rcases ha with ha | ha
        · exact ha.1
        · exact ih a ha.2
  let T : ℕ → Set ℤ := fun n => (fun a : ℕ => (a : ℤ)) '' S_seq S₀ n
  have hTpos : ∀ n, ∀ z ∈ T n, z > 0 := by
    intro n z hz
    rcases hz with ⟨a, ha, rfl⟩
    change (a : ℤ) > 0
    exact_mod_cast hseqpos n a ha
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
      have hneg2 : Int.negSucc (a + 1) ∉ T n := by
        intro hk
        have := hTpos n (Int.negSucc (a + 1)) hk
        omega
      simp [hneg, hneg2, Xor']
  have hST : ∀ n, S n = T n := by
    intro n
    induction n with
    | zero =>
        ext z
        constructor
        · intro hz
          refine ⟨z.toNat, ?_, ?_⟩
          · change ((z.toNat : ℕ) : ℤ) ∈ S 0
            rw [Int.toNat_of_nonneg (le_of_lt (hSpos 0 z hz))]
            exact hz
          · exact Int.toNat_of_nonneg (le_of_lt (hSpos 0 z hz))
        · rintro ⟨a, ha, rfl⟩
          exact ha
    | succ n ih =>
        ext z
        rw [hSdef, hTdef, ih]
  have hcand := problem_statement_assumed S₀ hS₀fin hS₀pos
  intro n
  obtain ⟨N, hNgood, hN⟩ := hcand.exists_gt n
  refine ⟨N, by omega, ?_⟩
  rw [hST N, hST 0]
  change S_seq S₀ N = S₀ ∪ {N + a | a ∈ S₀} at hNgood
  ext z
  simp only [T, Set.mem_image, hNgood, Set.mem_union, Set.mem_setOf_eq]
  change (∃ x : ℕ, (x ∈ S₀ ∨ ∃ a ∈ S₀, N + a = x) ∧ (x : ℤ) = z) ↔
    (∃ x ∈ S₀, (x : ℤ) = z) ∨ ∃ x ∈ S₀, (x : ℤ) = z - (N : ℤ)
  constructor
  · rintro ⟨x, (hx | ⟨a, ha, hax⟩), hcast⟩
    · exact Or.inl ⟨x, hx, hcast⟩
    · exact Or.inr ⟨a, ha, by
        have haxz : ((N + a : ℕ) : ℤ) = z := by simpa [hax] using hcast
        omega⟩
  · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, haz⟩)
    · exact ⟨a, Or.inl ha, rfl⟩
    · refine ⟨N + a, Or.inr ⟨a, ha, rfl⟩, ?_⟩
      omega
