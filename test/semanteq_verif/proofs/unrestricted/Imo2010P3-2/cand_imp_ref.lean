import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ g : ℕ+ → ℕ+,
    (∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  let e : ℕ+ ≃ ℤ>0 :=
    { toFun := fun n => ⟨n, by exact_mod_cast n.prop⟩
      invFun := fun z => ⟨z.val.toNat, by omega⟩
      left_inv := by
        intro n
        apply Subtype.ext
        change (Int.ofNat n.val).toNat = n.val
        simp
      right_inv := by
        intro z
        ext
        simp [Int.toNat_of_nonneg (le_of_lt z.prop)] }
  let gn : ℕ+ → ℕ+ := fun n => e.symm (g (e n))
  constructor
  · rintro (h_id | ⟨c, hc⟩) m n
    · refine ⟨m + n, ?_⟩
      rw [h_id]
      apply Subtype.ext
      change (m.val + n.val) * (n.val + m.val) =
        (m.val + n.val) * (m.val + n.val)
      rw [add_comm n.val m.val]
    · refine ⟨g m + n, ?_⟩
      rw [hc m, hc n]
      apply Subtype.ext
      change (m.val + c.val + n.val) * (n.val + c.val + m.val) =
        (m.val + c.val + n.val) * (m.val + c.val + n.val)
      ring
  · intro hsquare
    have hnsquare : ∀ m n : ℕ+, ∃ k : ℕ,
        (gn m + n) * (gn n + m) = k^2 := by
      intro m n
      rcases hsquare (e m) (e n) with ⟨r, hr⟩
      refine ⟨r.val.toNat, ?_⟩
      have hr_nonneg : 0 ≤ r.val := le_of_lt r.prop
      have hr' := congrArg Subtype.val hr
      change (((g (e m)).val + (e n).val) *
        ((g (e n)).val + (e m).val) : ℤ) = r.val * r.val at hr'
      change ((gn m).val + n.val) * ((gn n).val + m.val) = r.val.toNat ^ 2
      have hm_nonneg : 0 ≤ (g (e m)).val := le_of_lt (g (e m)).prop
      have hn_nonneg : 0 ≤ (g (e n)).val := le_of_lt (g (e n)).prop
      have hrnat := congrArg Int.toNat hr'
      rw [Int.toNat_mul
          (add_nonneg hm_nonneg (le_of_lt (e n).prop))
          (add_nonneg hn_nonneg (le_of_lt (e m).prop)),
        Int.toNat_add hm_nonneg (le_of_lt (e n).prop),
        Int.toNat_add hn_nonneg (le_of_lt (e m).prop),
        Int.toNat_mul hr_nonneg hr_nonneg] at hrnat
      simpa [gn, e, pow_two] using hrnat
    rcases (problem_statement_assumed gn).1 hnsquare with ⟨c, hc⟩
    by_cases hzero : c = 0
    · left
      funext z
      let n : ℕ+ := e.symm z
      have hnval := hc n
      rw [hzero] at hnval
      have hn : gn n = n := by simpa using hnval
      have he := congrArg e hn
      simpa [gn, n] using he
    · right
      have hcpos : 0 < c := Nat.pos_of_ne_zero hzero
      let cp : ℕ+ := ⟨c, hcpos⟩
      let cz : ℤ>0 := e cp
      refine ⟨cz, ?_⟩
      intro z
      let n : ℕ+ := e.symm z
      have hnval := hc n
      have hn : gn n = n + cp := by
        apply Subtype.ext
        simpa [cp] using hnval
      have he := congrArg e hn
      have hadd : e (n + cp) = e n + e cp := by
        apply Subtype.ext
        rfl
      rw [hadd] at he
      simpa [gn, n, cz, cp] using he
