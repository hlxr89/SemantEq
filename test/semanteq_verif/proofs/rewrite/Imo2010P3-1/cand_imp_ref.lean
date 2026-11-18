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
  let G : ℕ → ℕ := fun n =>
    if hn : 0 < n then (g ⟨(n : ℤ), by exact_mod_cast hn⟩).val.toNat else 1
  have hGpos (n : ℕ) : 0 < G n := by
    unfold G
    split
    · exact Nat.pos_of_ne_zero fun hz =>
        (not_le_of_gt (g _).property) (Int.toNat_eq_zero.mp hz)
    · exact Nat.zero_lt_one
  have hGval (n : ℕ) (hn : 0 < n) :
      (G n : ℤ) = (g ⟨(n : ℤ), by exact_mod_cast hn⟩).val := by
    simp only [G, dif_pos hn]
    exact Int.toNat_of_nonneg (le_of_lt (g _).property)
  have htoNatPos (x : ℤ>0) : 0 < x.val.toNat :=
    Nat.pos_of_ne_zero fun hz =>
      (not_le_of_gt x.property) (Int.toNat_eq_zero.mp hz)
  have hcand := problem_statement_assumed G
  constructor
  · intro hclass
    have hex : ∃ c : ℕ, ∀ n : ℕ, n > 0 → G n = n + c := by
      change g = id ∨ ∃ c, ∀ x, g x = x + c at hclass
      rcases hclass with hId | ⟨c, hc⟩
      · refine ⟨0, fun n hn => ?_⟩
        have hx := congrArg Subtype.val (congrFun hId ⟨(n : ℤ), by exact_mod_cast hn⟩)
        simp only [G, dif_pos hn, add_zero]
        have hxt := congrArg Int.toNat hx
        simpa only [id_eq] using hxt
      · refine ⟨c.val.toNat, fun n hn => ?_⟩
        have hx := congrArg Subtype.val (hc ⟨(n : ℤ), by exact_mod_cast hn⟩)
        apply Int.ofNat_inj.mp
        change (G n : ℤ) = (n : ℤ) + (c.val.toNat : ℤ)
        rw [hGval n hn, Int.toNat_of_nonneg (le_of_lt c.property)]
        exact hx
    have hnat := (hcand.mpr hex) hGpos
    intro m n
    obtain ⟨k, hk⟩ := hnat m.val.toNat n.val.toNat
      (htoNatPos m) (htoNatPos n)
    have hkpos : 0 < k := by
      -- non-rewrite step: the natural witness is positive because its square is.
      by_contra hk0
      have hkzero : k = 0 := Nat.eq_zero_of_not_pos hk0
      have hleft : 0 < (G m.val.toNat + m.val.toNat) *
          (G n.val.toNat + n.val.toNat) :=
        Nat.mul_pos (Nat.add_pos_left (hGpos _) _) (Nat.add_pos_left (hGpos _) _)
      have hleft' : 0 < (G m.val.toNat + n.val.toNat) *
          (G n.val.toNat + m.val.toNat) :=
        Nat.mul_pos (Nat.add_pos_left (hGpos _) _) (Nat.add_pos_left (hGpos _) _)
      rw [hk, hkzero] at hleft'
      simp only [pow_two, mul_zero, lt_self_iff_false] at hleft'
    refine ⟨⟨(k : ℤ), by exact_mod_cast hkpos⟩, ?_⟩
    apply Subtype.ext
    have hmval := hGval m.val.toNat (htoNatPos m)
    have hnval := hGval n.val.toNat (htoNatPos n)
    have hmnat := Int.toNat_of_nonneg (le_of_lt m.property)
    have hnnat := Int.toNat_of_nonneg (le_of_lt n.property)
    have hmeq : (⟨(m.val.toNat : ℤ), by exact_mod_cast htoNatPos m⟩ : ℤ>0) = m :=
      Subtype.ext hmnat
    have hneq : (⟨(n.val.toNat : ℤ), by exact_mod_cast htoNatPos n⟩ : ℤ>0) = n :=
      Subtype.ext hnnat
    rw [hmeq] at hmval
    rw [hneq] at hnval
    change ((g m).val + n.val) * ((g n).val + m.val) = (k : ℤ) * k
    rw [← hmval, ← hnval, ← hmnat, ← hnnat]
    have hk' : (G m.val.toNat + n.val.toNat) *
        (G n.val.toNat + m.val.toNat) = k * k := by
      simpa only [pow_two] using hk
    exact_mod_cast hk'
  · intro hsquares
    have hnat : ∀ m n : ℕ, m > 0 → n > 0 →
        ∃ k : ℕ, (G m + n) * (G n + m) = k^2 := by
      intro m n hm hn
      obtain ⟨k, hk⟩ := hsquares
        ⟨(m : ℤ), by exact_mod_cast hm⟩ ⟨(n : ℤ), by exact_mod_cast hn⟩
      refine ⟨k.val.toNat, ?_⟩
      have hkval := Int.toNat_of_nonneg (le_of_lt k.property)
      have hkeq := congrArg Subtype.val hk
      change ((g ⟨(m : ℤ), by exact_mod_cast hm⟩).val + n) *
        ((g ⟨(n : ℤ), by exact_mod_cast hn⟩).val + m) = k.val * k.val at hkeq
      apply Int.ofNat_inj.mp
      push_cast
      rw [hGval m hm, hGval n hn, hkval]
      simpa only [pow_two] using hkeq
    have hex := hcand.mp (fun _ => hnat)
    rcases hex with ⟨c, hc⟩
    change g = id ∨ ∃ d, ∀ x, g x = x + d
    by_cases hc0 : c = 0
    · left
      funext x
      apply Subtype.ext
      have hx := hc x.val.toNat (htoNatPos x)
      rw [hc0, add_zero] at hx
      have hGx := hGval x.val.toNat (htoNatPos x)
      rw [hx] at hGx
      have hxn : (⟨(x.val.toNat : ℤ), by exact_mod_cast htoNatPos x⟩ : ℤ>0) = x :=
        Subtype.ext (Int.toNat_of_nonneg (le_of_lt x.property))
      rw [hxn] at hGx
      rw [Int.toNat_of_nonneg (le_of_lt x.property)] at hGx
      simpa only [id_eq] using hGx.symm
    · right
      let d : ℤ>0 := ⟨(c : ℤ), by exact_mod_cast (Nat.pos_of_ne_zero hc0)⟩
      refine ⟨d, fun x => ?_⟩
      apply Subtype.ext
      have hx := hc x.val.toNat (htoNatPos x)
      have hGx := hGval x.val.toNat (htoNatPos x)
      rw [hx] at hGx
      have hxn : (⟨(x.val.toNat : ℤ), by exact_mod_cast htoNatPos x⟩ : ℤ>0) = x :=
        Subtype.ext (Int.toNat_of_nonneg (le_of_lt x.property))
      rw [hxn] at hGx
      change (g x).val = x.val + (c : ℤ)
      rw [← Int.toNat_of_nonneg (le_of_lt x.property)]
      exact_mod_cast hGx.symm
