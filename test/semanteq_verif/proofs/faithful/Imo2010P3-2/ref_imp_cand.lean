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
    (∀ m n : ℕ+, ∃ k : ℕ, (g m + n) * (g n + m) = k^2) ↔
    (∃ c : ℕ, ∀ n : ℕ+, g n = n + c) := by
  intro g
  let toPos (n : ℕ+) : ℤ>0 := ⟨n, by exact_mod_cast n.prop⟩
  let toPNat (z : ℤ>0) : ℕ+ := ⟨z.1.toNat, by omega⟩
  let G : ℤ>0 → ℤ>0 := fun z => toPos (g (toPNat z))
  have toPNat_toPos (n : ℕ+) : toPNat (toPos n) = n := by
    apply Subtype.ext
    simp [toPNat, toPos]
    rfl
  have toPos_toPNat (z : ℤ>0) : toPos (toPNat z) = z := by
    ext
    simp [toPNat, toPos, Int.toNat_of_nonneg (le_of_lt z.2)]
  constructor
  · intro hsquare
    have hGsq : ∀ m n, IsSquare ((G m + n) * (G n + m)) := by
      intro m n
      obtain ⟨k, hk⟩ := hsquare (toPNat m) (toPNat n)
      have hkpos : 0 < k := by
        have hp : 0 < (↑((g (toPNat m) + toPNat n) * (g (toPNat n) + toPNat m)) : ℕ) :=
          ((g (toPNat m) + toPNat n) * (g (toPNat n) + toPNat m)).prop
        change (0 : ℕ) < ((↑(g (toPNat m)) : ℕ) + (↑(toPNat n) : ℕ)) *
          ((↑(g (toPNat n)) : ℕ) + (↑(toPNat m) : ℕ)) at hp
        rw [hk] at hp
        by_contra h
        have : k = 0 := Nat.eq_zero_of_not_pos h
        subst k
        simp at hp
      refine ⟨toPos ⟨k, hkpos⟩, ?_⟩
      apply Subtype.ext
      have hkZ := congrArg Int.ofNat hk
      have hmcast : (m.1.toNat : ℤ) = m.1 := by
        simp [Int.toNat_of_nonneg (le_of_lt m.2)]
      have hncast : (n.1.toNat : ℤ) = n.1 := by
        simp [Int.toNat_of_nonneg (le_of_lt n.2)]
      simp [G, toPos, toPNat, pow_two] at hkZ ⊢
      simp [max_eq_left (le_of_lt m.2), max_eq_left (le_of_lt n.2)] at hkZ
      exact hkZ
    rcases (imo2010_p3_assumed G).2 hGsq with hId | ⟨c, hc⟩
    · refine ⟨0, ?_⟩
      intro n
      have hn := congrArg toPNat (congrFun hId (toPos n))
      simp only [G, Function.comp_apply, id_eq, toPNat_toPos, toPos_toPNat] at hn
      simpa using hn
    · refine ⟨c.1.toNat, ?_⟩
      intro n
      have hn := congrArg toPNat (hc (toPos n))
      have hv := congrArg Subtype.val hn
      simp [G, toPNat_toPos, toPNat, toPos,
        Int.toNat_of_nonneg (le_of_lt c.2)] at hv ⊢
      omega
  · rintro ⟨c, hc⟩
    have hmem : G ∈ SolutionSet := by
      rcases c with _ | c
      · left
        funext z
        apply Subtype.ext
        have h := hc (toPNat z)
        simp [G, toPos, toPNat, toPos_toPNat] at h ⊢
        omega
      · right
        let C : ℤ>0 := ⟨Int.ofNat (c + 1), by norm_num⟩
        refine ⟨C, ?_⟩
        intro z
        apply Subtype.ext
        have h := hc (toPNat z)
        simp [G, C, toPos, toPNat, toPos_toPNat] at h ⊢
        omega
    have hGsq := (imo2010_p3_assumed G).1 hmem
    intro m n
    rcases hGsq (toPos m) (toPos n) with ⟨k, hk⟩
    refine ⟨k.1.toNat, ?_⟩
    have hv := congrArg Subtype.val hk
    simp [G, toPNat_toPos, toPos, Int.toNat_of_nonneg (le_of_lt k.2)] at hv ⊢
    norm_num at hv ⊢
    have hkcast : (k.1.toNat : ℤ) = k.1 := by
      simp [Int.toNat_of_nonneg (le_of_lt k.2)]
    rw [← hkcast] at hv
    have hvN : (↑((g m + n) * (g n + m)) : ℕ) = k.1.toNat * k.1.toNat := by
      exact_mod_cast hv
    simpa [pow_two] using hvN
