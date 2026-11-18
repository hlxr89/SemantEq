import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ g : ℕ+ → ℕ+, 
    (∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) →
    ∃ c : ℕ, ∀ n : ℕ+, g n = n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  constructor
  · intro hg m n
    rcases hg with h_id | ⟨c, hc⟩
    · rw [h_id]
      refine ⟨m + n, ?_⟩
      change (m + n) * (n + m) = (m + n) * (m + n)
      rw [add_comm n m]
    · refine ⟨m + n + c, ?_⟩
      rw [hc m, hc n]
      apply congrArg₂ (· * ·)
      · simp only [add_comm, add_left_comm]
      · simp only [add_comm, add_left_comm]
  · intro hsquare
    let toZ : ℕ+ → ℤ>0 := fun n => ⟨n, by exact_mod_cast n.2⟩
    let toN : ℤ>0 → ℕ+ := fun z => ⟨z.1.natAbs, Int.natAbs_pos.mpr z.2.ne'⟩
    have toN_toZ (n : ℕ+) : toN (toZ n) = n := by
      apply Subtype.ext
      rfl
    have toZ_toN (z : ℤ>0) : toZ (toN z) = z := by
      apply Subtype.ext
      exact Int.natAbs_of_nonneg z.2.le
    let gn : ℕ+ → ℕ+ := fun n => toN (g (toZ n))
    have hnatsquare : ∀ m n : ℕ+, ∃ k : ℕ,
        (gn m + n) * (gn n + m) = k^2 := by
      intro m n
      obtain ⟨k, hk⟩ := hsquare (toZ m) (toZ n)
      refine ⟨k.1.natAbs, ?_⟩
      have h := congrArg Subtype.val hk
      change ((g (toZ m)).1 + (n : ℕ)) * ((g (toZ n)).1 + (m : ℕ)) =
          k.1 * k.1 at h
      change ((g (toZ m)).1.natAbs + (n : ℕ)) *
          ((g (toZ n)).1.natAbs + (m : ℕ)) = k.1.natAbs ^ 2
      rw [pow_two]
      rw [← Int.natAbs_of_nonneg (g (toZ m)).2.le,
        ← Int.natAbs_of_nonneg (g (toZ n)).2.le,
        ← Int.natAbs_of_nonneg k.2.le] at h
      exact_mod_cast h
    obtain ⟨c, hc⟩ := problem_statement_assumed gn hnatsquare
    by_cases hc0 : c = 0
    · left
      funext x
      have h := hc (toN x)
      change (g (toZ (toN x))).1.natAbs = x.1.natAbs + c at h
      rw [toZ_toN, hc0, Nat.add_zero] at h
      apply Subtype.ext
      change (g x).1 = x.1
      rw [← Int.natAbs_of_nonneg (g x).2.le, ← Int.natAbs_of_nonneg x.2.le]
      exact_mod_cast h
    · right
      have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
      refine ⟨⟨c, by exact_mod_cast hcpos⟩, fun x => ?_⟩
      have h := hc (toN x)
      change (g (toZ (toN x))).1.natAbs = x.1.natAbs + c at h
      rw [toZ_toN] at h
      apply Subtype.ext
      change (g x).1 = x.1 + (c : ℤ)
      rw [← Int.natAbs_of_nonneg (g x).2.le, ← Int.natAbs_of_nonneg x.2.le]
      exact_mod_cast h
