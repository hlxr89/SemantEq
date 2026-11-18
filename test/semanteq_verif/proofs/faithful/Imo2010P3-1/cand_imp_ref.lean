import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev PosInt : Type := { x : ℤ // 0 < x }

notation "ℤ>0" => PosInt

abbrev SolutionSet : Set (ℤ>0 → ℤ>0) := { f | f = id ∨ ∃ c, ∀ x, f x = x + c }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ g : ℕ → ℕ,
    (∀ n : ℕ, g n > 0) →
    (∀ m n : ℕ, m > 0 → n > 0 → ∃ k : ℕ, (g m + n) * (g n + m) = k^2) ↔ 
    ∃ c : ℕ, ∀ n : ℕ, n > 0 → g n = n + c := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2010_p3 (g : ℤ>0 → ℤ>0) :
    g ∈ SolutionSet ↔ ∀ m n, IsSquare ((g m + n) * (g n + m)) := by
  let f : ℕ → ℕ := fun n => if hn : 0 < n then (g ⟨(n : ℤ), by exact_mod_cast hn⟩).val.toNat else 1
  have hfpos : ∀ n, f n > 0 := by
    intro n
    simp only [f]
    split_ifs with hn
    · have := (g ⟨(n : ℤ), by exact_mod_cast hn⟩).property
      omega
    · omega
  have hf_eq (x : ℤ>0) : f x.val.toNat = (g x).val.toNat := by
    have hx : (⟨(x.val.toNat : ℤ), by omega⟩ : ℤ>0) = x := by
      apply Subtype.ext
      exact Int.toNat_of_nonneg (le_of_lt x.property)
    simp only [f, show 0 < x.val.toNat by omega, ↓reduceDIte]
    rw [hx]
  constructor
  · intro hg
    have hftrans : ∃ c : ℕ, ∀ n : ℕ, n > 0 → f n = n + c := by
      rcases hg with rfl | ⟨c, hc⟩
      · refine ⟨0, ?_⟩
        intro n hn
        simp [f, hn]
      · refine ⟨c.val.toNat, ?_⟩
        intro n hn
        have heq := congrArg Subtype.val (hc (⟨(n : ℤ), by exact_mod_cast hn⟩ : ℤ>0))
        have hcval : (c.val.toNat : ℤ) = c.val := by omega
        change (g ⟨(n : ℤ), _⟩).val = (n : ℤ) + c.val at heq
        simp only [f, hn, ↓reduceDIte]
        omega
    have hfsquare := (problem_statement_assumed f).2 hftrans hfpos
    intro m n
    obtain ⟨k, hk⟩ := hfsquare m.val.toNat n.val.toNat (by omega) (by omega)
    have hkpos : 0 < k := by
      apply Nat.pos_of_ne_zero
      intro hkzero
      subst k
      simp only [pow_two, mul_zero] at hk
      rcases Nat.mul_eq_zero.mp hk with hk | hk <;> omega
    refine ⟨(⟨(k : ℤ), by exact_mod_cast hkpos⟩ : ℤ>0), ?_⟩
    apply Subtype.ext
    simp only [Positive.val_mul, Positive.coe_add]
    have hmval : (m.val.toNat : ℤ) = m.val := Int.toNat_of_nonneg (le_of_lt m.property)
    have hnval : (n.val.toNat : ℤ) = n.val := Int.toNat_of_nonneg (le_of_lt n.property)
    rw [hf_eq m, hf_eq n] at hk
    have hgmval : ((g m).val.toNat : ℤ) = (g m).val :=
      Int.toNat_of_nonneg (le_of_lt (g m).property)
    have hgnval : ((g n).val.toNat : ℤ) = (g n).val :=
      Int.toNat_of_nonneg (le_of_lt (g n).property)
    have hk' := congrArg (fun z : ℕ => (z : ℤ)) hk
    push_cast at hk'
    rw [hgmval, hgnval, hmval, hnval] at hk'
    simpa [Positive.coe_add, pow_two] using hk'
  · intro hsquare
    have hfsquare : ∀ m n : ℕ, m > 0 → n > 0 → ∃ k : ℕ,
        (f m + n) * (f n + m) = k^2 := by
      intro m n hm hn
      obtain ⟨k, hk⟩ := hsquare (⟨(m : ℤ), by exact_mod_cast hm⟩ : ℤ>0)
        (⟨(n : ℤ), by exact_mod_cast hn⟩ : ℤ>0)
      refine ⟨k.val.toNat, ?_⟩
      have hk' := congrArg Subtype.val hk
      simp only [Positive.val_mul, Positive.coe_add] at hk'
      have hkval : (k.val.toNat : ℤ) = k.val := by omega
      simp only [f, hm, hn, ↓reduceDIte]
      have gmpos := (g (⟨(m : ℤ), by exact_mod_cast hm⟩ : ℤ>0)).property
      have gnpos := (g (⟨(n : ℤ), by exact_mod_cast hn⟩ : ℤ>0)).property
      apply Nat.cast_injective (R := ℤ)
      push_cast
      rw [Int.toNat_of_nonneg (le_of_lt gmpos), Int.toNat_of_nonneg (le_of_lt gnpos),
        hkval]
      simpa [pow_two] using hk'
    obtain ⟨c, hc⟩ := (problem_statement_assumed f).1 (fun _ => hfsquare)
    by_cases hc0 : c = 0
    · left
      funext x
      apply Subtype.ext
      have hx := hc x.val.toNat (by omega)
      rw [hf_eq x] at hx
      simp only [hc0, add_zero] at hx
      change (g x).val = x.val
      have hgx := Int.toNat_of_nonneg (le_of_lt (g x).property)
      have hxx := Int.toNat_of_nonneg (le_of_lt x.property)
      omega
    · right
      have hcpos : 0 < c := Nat.pos_of_ne_zero hc0
      refine ⟨(⟨(c : ℤ), by exact_mod_cast hcpos⟩ : ℤ>0), ?_⟩
      intro x
      apply Subtype.ext
      have hx := hc x.val.toNat (by omega)
      rw [hf_eq x] at hx
      change (g x).val = x.val + (c : ℤ)
      have hgx := Int.toNat_of_nonneg (le_of_lt (g x).property)
      have hxx := Int.toNat_of_nonneg (le_of_lt x.property)
      omega
