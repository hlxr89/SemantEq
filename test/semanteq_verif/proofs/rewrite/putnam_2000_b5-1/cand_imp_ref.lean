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
  let A : Set ℕ := {a | (a : ℤ) ∈ S 0}
  have hAfin : A.Finite := by
    exact Set.Finite.preimage_embedding (Nat.castEmbedding (R := ℤ)) (hSfin 0)
  have hApos : ∀ a ∈ A, a > 0 := by
    intro a ha
    change (a : ℤ) ∈ S 0 at ha
    exact_mod_cast hSpos 0 a ha
  have hInf := problem_statement_assumed A hAfin hApos
  let T : ℕ → Set ℤ := fun n => (Nat.castEmbedding (R := ℤ)) '' S_seq A n
  have hpos : ∀ n x, x ∈ S_seq A n → x > 0 := by
    intro n
    induction n with
    | zero => exact hApos
    | succ n ih =>
        intro x hx
        change (x > 0 ∧ _) ∨ (_ ∧ x ∈ S_seq A n) at hx
        rcases hx with hx | hx
        · exact hx.1
        · exact ih x hx.2
  have hmem : ∀ n (a : ℕ), (a : ℤ) ∈ T n ↔ a ∈ S_seq A n := by
    intro n a
    constructor
    · rintro ⟨b, hb, hab⟩
      change (b : ℤ) = (a : ℤ) at hab
      have : b = a := by exact_mod_cast hab
      simpa only [this] using hb
    · intro ha
      exact ⟨a, ha, rfl⟩
  have hTpos : ∀ n z, z ∈ T n → z > 0 := by
    rintro n z ⟨a, ha, rfl⟩
    change (a : ℤ) > 0
    exact_mod_cast hpos n a ha
  have hTdef : ∀ n z, z ∈ T (n + 1) ↔ Xor' (z - 1 ∈ T n) (z ∈ T n) := by
    intro n z
    by_cases hz : 0 ≤ z
    · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hz
      by_cases ha : a = 0
      · subst a
        constructor
        · intro h
          exact False.elim ((Int.not_lt_of_ge le_rfl) (hTpos (n + 1) 0 h))
        · rintro (h | h)
          · exact False.elim ((Int.not_lt_of_ge (sub_nonpos.mpr zero_le_one))
              (hTpos n (0 - 1) h.1))
          · exact False.elim ((Int.not_lt_of_ge le_rfl) (hTpos n 0 h.1))
      · have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr ha
        have hpred : ((a : ℤ) - 1 ∈ T n) ↔ a - 1 ∈ S_seq A n := by
          have heq : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
            simpa only [Nat.cast_one] using Int.ofNat_sub ha1
          rw [← heq]
          exact hmem n (a - 1)
        rw [hmem (n + 1) a, hmem n a, hpred]
        change ((a > 0 ∧ (a - 1 ∈ S_seq A n ∧ a ∉ S_seq A n)) ∨
          (a - 1 ∉ S_seq A n ∧ a ∈ S_seq A n)) ↔
          Xor' (a - 1 ∈ S_seq A n) (a ∈ S_seq A n)
        constructor
        · rintro (⟨_, hp, hnq⟩ | ⟨hnp, hq⟩)
          · exact Or.inl ⟨hp, hnq⟩
          · exact Or.inr ⟨hq, hnp⟩
        · rintro (⟨hp, hnq⟩ | ⟨hq, hnp⟩)
          · exact Or.inl ⟨ha1, hp, hnq⟩
          · exact Or.inr ⟨hnp, hq⟩
    · have hzlt : z < 0 := lt_of_not_ge hz
      constructor
      · intro h
        exact False.elim ((not_lt_of_ge (le_of_lt hzlt)) (hTpos (n + 1) z h))
      · rintro (h | h)
        · exact False.elim ((not_lt_of_ge
              (sub_nonpos.mpr (le_trans (le_of_lt hzlt) zero_le_one)))
            (hTpos n (z - 1) h.1))
        · exact False.elim ((not_lt_of_ge (le_of_lt hzlt)) (hTpos n z h.1))
  have hST : ∀ n, S n = T n := by
    intro n
    induction n with
    | zero =>
        ext z
        constructor
        · intro hz
          obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (le_of_lt (hSpos 0 z hz))
          subst z
          exact ⟨a, hz, rfl⟩
        · rintro ⟨a, ha, rfl⟩
          exact ha
    | succ n ih =>
        ext z
        rw [hSdef n z, hTdef n z, ← ih]
  intro n
  obtain ⟨N, hgood, hnN⟩ := hInf.exists_gt n
  have hN : N ≥ n := le_of_lt hnN
  refine ⟨N, hN, ?_⟩
  rw [hST N, hST 0]
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    have ha' := ha
    rw [hgood] at ha'
    rcases ha' with ha' | ⟨b, hb, hab⟩
    · exact Or.inl ⟨a, ha', rfl⟩
    · right
      refine ⟨b, hb, ?_⟩
      change (b : ℤ) = (a : ℤ) - (N : ℤ)
      subst a
      push_cast
      exact (add_sub_cancel_left (N : ℤ) b).symm
  · intro hz
    rcases hz with hz | hz
    · rcases hz with ⟨a, ha, rfl⟩
      refine ⟨a, ?_, rfl⟩
      rw [hgood]
      exact Or.inl ha
    · rcases hz with ⟨b, hb, hab⟩
      change (b : ℤ) = z - (N : ℤ) at hab
      have hab' : z = (b : ℤ) + (N : ℤ) := by
        simpa only [sub_add_cancel] using
          congrArg (fun w : ℤ => w + (N : ℤ)) hab.symm
      subst z
      refine ⟨N + b, ?_, ?_⟩
      · rw [hgood]
        right
        exact ⟨b, hb, rfl⟩
      · exact add_comm (N : ℤ) b
