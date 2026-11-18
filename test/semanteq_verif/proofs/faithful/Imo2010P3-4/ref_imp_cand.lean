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
  intro g h
  let gz : ℤ>0 → ℤ>0 := fun x =>
    ⟨g ⟨x.1.toNat, by omega⟩, by exact_mod_cast (g ⟨x.1.toNat, by omega⟩).2⟩
  have hz : ∀ m n, IsSquare ((gz m + n) * (gz n + m)) := by
    intro m n
    let mp : ℕ+ := ⟨m.1.toNat, by omega⟩
    let np : ℕ+ := ⟨n.1.toNat, by omega⟩
    obtain ⟨k, hk⟩ := h mp np
    rw [isSquare_iff_exists_sq]
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hk0
      have hleft : (g mp).1 + np.1 ≠ 0 := by
        have hg := (g mp).2
        omega
      have hright : (g np).1 + mp.1 ≠ 0 := by
        have hg := (g np).2
        omega
      apply Nat.mul_ne_zero hleft hright
      simpa [hk0] using hk
    refine ⟨⟨(k : ℤ), by exact_mod_cast hkpos⟩, ?_⟩
    apply Subtype.ext
    change
      (((g mp).1 : ℤ) + n.1) * (((g np).1 : ℤ) + m.1) = (k : ℤ) ^ 2
    have hmp : (mp.1 : ℤ) = m.1 := by
      dsimp [mp]
      exact Int.toNat_of_nonneg (le_of_lt m.2)
    have hnp : (np.1 : ℤ) = n.1 := by
      dsimp [np]
      exact Int.toNat_of_nonneg (le_of_lt n.2)
    rw [← hmp, ← hnp]
    exact_mod_cast hk
  rcases (imo2010_p3_assumed gz).2 hz with hid | ⟨c, hc⟩
  · refine ⟨0, fun n => ?_⟩
    have hn := congrArg Subtype.val (congrFun hid ⟨(n.1 : ℤ), by exact_mod_cast n.2⟩)
    change (g n).1 = n.1 + 0
    simpa [gz] using hn
  · refine ⟨c.1.toNat, fun n => ?_⟩
    have hn := congrArg Subtype.val (hc ⟨(n.1 : ℤ), by exact_mod_cast n.2⟩)
    dsimp [gz] at hn
    change (g n).1 = n.1 + c.1.toNat
    have hcval := Int.toNat_of_nonneg (le_of_lt c.2)
    apply Nat.cast_injective (R := ℤ)
    push_cast
    rw [hcval]
    simpa using hn
