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
  let T : ℕ → Set ℤ := fun n => (Nat.castEmbedding (R := ℤ)) '' S_seq S₀ n
  have hpos : ∀ n x, x ∈ S_seq S₀ n → x > 0 := by
    intro n
    induction n with
    | zero => exact hS₀_pos
    | succ n ih =>
        intro x hx
        change (x > 0 ∧ _) ∨ (_ ∧ x ∈ S_seq S₀ n) at hx
        rcases hx with hx | hx
        · exact hx.1
        · exact ih x hx.2
  have hmem : ∀ n (a : ℕ), (a : ℤ) ∈ T n ↔ a ∈ S_seq S₀ n := by
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
  have hTfin : ∀ n, Set.Finite (T n) := by
    intro n
    apply Set.Finite.image
    induction n with
    | zero => exact hS₀
    | succ n ih =>
        apply Set.Finite.subset (ih.union (ih.image fun x => x + 1))
        intro a ha
        change (a > 0 ∧ (a - 1 ∈ S_seq S₀ n ∧ a ∉ S_seq S₀ n)) ∨
          (a - 1 ∉ S_seq S₀ n ∧ a ∈ S_seq S₀ n) at ha
        rcases ha with ha | ha
        · right
          exact ⟨a - 1, ha.2.1, Nat.sub_add_cancel ha.1⟩
        · exact Or.inl ha.2
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
        have hpred : ((a : ℤ) - 1 ∈ T n) ↔ a - 1 ∈ S_seq S₀ n := by
          have heq : ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 := by
            simpa only [Nat.cast_one] using Int.ofNat_sub ha1
          rw [← heq]
          exact hmem n (a - 1)
        rw [hmem (n + 1) a, hmem n a, hpred]
        change ((a > 0 ∧ (a - 1 ∈ S_seq S₀ n ∧ a ∉ S_seq S₀ n)) ∨
          (a - 1 ∉ S_seq S₀ n ∧ a ∈ S_seq S₀ n)) ↔
          Xor' (a - 1 ∈ S_seq S₀ n) (a ∈ S_seq S₀ n)
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
  have hlarge := putnam_2000_b5_assumed T hTfin hTpos hTdef
  have htransport : ∀ n, ∃ N ≥ n,
      S_seq S₀ N = S₀ ∪ {N + a | a ∈ S₀} := by
    intro n
    obtain ⟨N, hN, hEq⟩ := hlarge n
    refine ⟨N, hN, ?_⟩
    ext a
    rw [← hmem N a, hEq]
    constructor
    · intro ha
      rcases ha with ha | ha
      · exact Or.inl ((hmem 0 a).mp ha)
      · rcases ha with ⟨b, hb, hab⟩
        right
        change b ∈ S₀ at hb
        refine ⟨b, hb, ?_⟩
        change (b : ℤ) = (a : ℤ) - (N : ℤ) at hab
        have hab' : (a : ℤ) = (b : ℤ) + (N : ℤ) := by
          simpa only [sub_add_cancel] using
            congrArg (fun z : ℤ => z + (N : ℤ)) hab.symm
        have hab'' : (a : ℤ) = (N : ℤ) + (b : ℤ) := by
          simpa only [add_comm] using hab'
        have : a = N + b := by exact_mod_cast hab''
        exact this.symm
    · intro ha
      rcases ha with ha | ⟨b, hb, rfl⟩
      · exact Or.inl ((hmem 0 a).mpr ha)
      · right
        refine ⟨b, ?_, ?_⟩
        · change b ∈ S₀
          exact hb
        · change (b : ℤ) = ((N + b : ℕ) : ℤ) - (N : ℤ)
          push_cast
          exact (add_sub_cancel_left (N : ℤ) b).symm
  intro hfinite
  obtain ⟨B, hB⟩ := hfinite.exists_le
  obtain ⟨N, hN, hgood⟩ := htransport (B + 1)
  have hNB : N ≤ B := hB N hgood
  exact (Nat.not_succ_le_self B) (le_trans hN hNB)
