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
  let e : ℕ+ ≃ ℤ>0 :=
    { toFun := fun n => ⟨n, by exact_mod_cast n.property⟩
      invFun := fun z => ⟨z.val.toNat, by omega⟩
      left_inv := by
        intro n
        apply Subtype.eq
        rfl
      right_inv := by
        intro z
        ext
        simp [Int.toNat_of_nonneg (le_of_lt z.property)] }
  let G : ℤ>0 → ℤ>0 := fun z => e (g (e.symm z))
  have hs : ∀ m n, IsSquare ((G m + n) * (G n + m)) := by
    intro m n
    rcases h (e.symm m) (e.symm n) with ⟨k, hk⟩
    have hkpos : 0 < k := by
      have hp : 0 < k ^ 2 := by
        rw [← hk]
        have hp' := PNat.pos ((g (e.symm m) + e.symm n) *
          (g (e.symm n) + e.symm m))
        exact_mod_cast hp'
      nlinarith
    refine ⟨e ⟨k, hkpos⟩, ?_⟩
    apply Subtype.ext
    change
      ((G m : ℤ) + (n : ℤ)) * ((G n : ℤ) + (m : ℤ)) =
        (e ⟨k, hkpos⟩ : ℤ) * (e ⟨k, hkpos⟩ : ℤ)
    have hkz := congrArg (fun x : ℕ => (x : ℤ)) hk
    simpa [G, e, Int.toNat_of_nonneg (le_of_lt m.property),
      Int.toNat_of_nonneg (le_of_lt n.property), pow_two] using hkz
  rcases (imo2010_p3_assumed G).2 hs with hG | ⟨c, hG⟩
  · refine ⟨0, fun n => ?_⟩
    have hn := congrFun hG (e n)
    have hn' : e (g n) = e n := by simpa [G] using hn
    have := e.injective hn'
    change (g n : ℕ) = (n : ℕ) + 0
    simpa only [Nat.add_zero] using congrArg PNat.val this
  · refine ⟨c.val.toNat, fun n => ?_⟩
    have hn := hG (e n)
    have hn' : ((g n : ℕ) : ℤ) = (n : ℤ) + c.val := by
      have := congrArg Subtype.val hn
      simpa [G] using this
    change (g n : ℕ) = (n : ℕ) + c.val.toNat
    omega
