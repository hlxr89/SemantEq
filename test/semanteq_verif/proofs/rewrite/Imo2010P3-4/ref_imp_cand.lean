import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem imo2010_p3_assumed (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem problem_statement :
  ∀ g : ℕ+ → ℕ+, 
    (∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) →
    ∃ c : ℕ, ∀ n : ℕ+, g n = n + c := by
  intro g hg
  let toZ : ℕ+ → ℤ>0 := fun n => ⟨n, by exact_mod_cast n.2⟩
  let toN : ℤ>0 → ℕ+ := fun z => ⟨z.1.natAbs, Int.natAbs_pos.mpr z.2.ne'⟩
  have toN_toZ (n : ℕ+) : toN (toZ n) = n := by
    apply Subtype.ext
    rfl
  have toZ_toN (z : ℤ>0) : toZ (toN z) = z := by
    apply Subtype.ext
    exact Int.natAbs_of_nonneg z.2.le
  let gz : ℤ>0 → ℤ>0 := fun z => toZ (g (toN z))
  have hsquare : ∀ m n, IsSquare ((gz m + n) * (gz n + m)) := by
    intro m n
    obtain ⟨k, hk⟩ := hg (toN m) (toN n)
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hkzero
      subst k
      have hp : 0 < ((g (toN m) : ℕ) + (toN n : ℕ)) *
          ((g (toN n) : ℕ) + (toN m : ℕ)) :=
        Nat.mul_pos (Nat.add_pos_left (g (toN m)).2 _) (Nat.add_pos_left (g (toN n)).2 _)
      exact (Nat.ne_of_gt hp) hk
    refine ⟨⟨k, by exact_mod_cast hkpos⟩, ?_⟩
    rw [← toZ_toN m, ← toZ_toN n]
    simp only [gz, toN_toZ]
    apply Subtype.ext
    change ((↑(g (toN m)) : ℤ) + ↑(toN n)) *
        ((↑(g (toN n)) : ℤ) + ↑(toN m)) = (k : ℤ) * k
    rw [← pow_two]
    exact_mod_cast hk
  rcases (imo2010_p3_assumed gz).2 hsquare with h_id | ⟨c, hc⟩
  · refine ⟨0, fun n => ?_⟩
    have h := congrArg Subtype.val (congrFun h_id (toZ n))
    change (↑(g (toN (toZ n))) : ℤ) = (↑n : ℤ) at h
    rw [toN_toZ] at h
    change (g n : ℕ) = (n : ℕ) + 0
    rw [Nat.add_zero]
    exact_mod_cast h
  · refine ⟨c.1.natAbs, fun n => ?_⟩
    have h := congrArg Subtype.val (hc (toZ n))
    change (↑(g (toN (toZ n))) : ℤ) = (↑n : ℤ) + c.1 at h
    rw [toN_toZ, ← Int.natAbs_of_nonneg c.2.le] at h
    exact_mod_cast h
