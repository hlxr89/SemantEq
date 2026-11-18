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
  let toPos (n : ℕ+) : ℤ>0 := ⟨n, by exact_mod_cast n.prop⟩
  let toPNat (z : ℤ>0) : ℕ+ := ⟨z.1.toNat, by omega⟩
  let G : ℕ+ → ℕ+ := fun n => toPNat (g (toPos n))
  have toPNat_toPos (n : ℕ+) : toPNat (toPos n) = n := by
    apply Subtype.ext
    simp [toPNat, toPos]
    rfl
  have toPos_toPNat (z : ℤ>0) : toPos (toPNat z) = z := by
    ext
    simp [toPNat, toPos, Int.toNat_of_nonneg (le_of_lt z.2)]
  constructor
  · intro hg
    have hGc : ∃ c : ℕ, ∀ n : ℕ+, G n = n + c := by
      rcases hg with hId | ⟨c, hc⟩
      · refine ⟨0, ?_⟩
        intro n
        have h := congrArg toPNat (congrFun hId (toPos n))
        simpa [G, toPNat_toPos, toPos_toPNat] using h
      · refine ⟨c.1.toNat, ?_⟩
        intro n
        have h := congrArg Subtype.val (congrArg toPNat (hc (toPos n)))
        simp [G, toPNat, toPos, toPNat_toPos,
          Int.toNat_of_nonneg (le_of_lt c.2)] at h ⊢
        omega
    have hGsq := (problem_statement_assumed G).2 hGc
    intro m n
    obtain ⟨k, hk⟩ := hGsq (toPNat m) (toPNat n)
    have hkpos : 0 < k := by
      have hp : (0 : ℕ) < ((↑(G (toPNat m)) : ℕ) + (↑(toPNat n) : ℕ)) *
          ((↑(G (toPNat n)) : ℕ) + (↑(toPNat m) : ℕ)) := by
        exact Nat.mul_pos (Nat.add_pos_left (G (toPNat m)).prop _)
          (Nat.add_pos_left (G (toPNat n)).prop _)
      rw [hk] at hp
      by_contra h
      have : k = 0 := Nat.eq_zero_of_not_pos h
      subst k
      simp at hp
    refine ⟨toPos ⟨k, hkpos⟩, ?_⟩
    apply Subtype.ext
    have hkZ := congrArg Int.ofNat hk
    simp [G, toPNat, toPos, toPos_toPNat, pow_two] at hkZ ⊢
    simp [max_eq_left (le_of_lt m.2), max_eq_left (le_of_lt n.2),
      max_eq_left (le_of_lt (g m).2), max_eq_left (le_of_lt (g n).2)] at hkZ
    exact hkZ
  · intro hsquare
    have hGsq : ∀ m n : ℕ+, ∃ k : ℕ, (G m + n) * (G n + m) = k^2 := by
      intro m n
      rcases hsquare (toPos m) (toPos n) with ⟨k, hk⟩
      refine ⟨k.1.toNat, ?_⟩
      have hv := congrArg Subtype.val hk
      simp [G, toPNat, toPos, toPNat_toPos, toPos_toPNat,
        Int.toNat_of_nonneg (le_of_lt k.2)] at hv ⊢
      have hkcast : (k.1.toNat : ℤ) = k.1 := by
        simp [Int.toNat_of_nonneg (le_of_lt k.2)]
      rw [← hkcast] at hv
      have gmcast : ((g (toPos m)).1.toNat : ℤ) = (g (toPos m)).1 := by
        simp [Int.toNat_of_nonneg (le_of_lt (g (toPos m)).2)]
      have gncast : ((g (toPos n)).1.toNat : ℤ) = (g (toPos n)).1 := by
        simp [Int.toNat_of_nonneg (le_of_lt (g (toPos n)).2)]
      rw [← gmcast, ← gncast] at hv
      have hvN : (↑((G m + n) * (G n + m)) : ℕ) = k.1.toNat * k.1.toNat := by
        simp [G, toPNat, toPos]
        exact_mod_cast hv
      simpa [pow_two] using hvN
    rcases (problem_statement_assumed G).1 hGsq with ⟨c, hc⟩
    rcases c with _ | c
    · left
      funext z
      apply Subtype.ext
      have h := hc (toPNat z)
      simp only [G] at h
      rw [toPos_toPNat z] at h
      simp [G, toPNat, toPos, toPos_toPNat] at h ⊢
      omega
    · right
      let C : ℤ>0 := ⟨Int.ofNat (c + 1), by norm_num⟩
      refine ⟨C, ?_⟩
      intro z
      apply Subtype.ext
      have h := hc (toPNat z)
      simp only [G] at h
      rw [toPos_toPNat z] at h
      simp [G, C, toPNat, toPos, toPNat_toPos, toPos_toPNat] at h ⊢
      omega
