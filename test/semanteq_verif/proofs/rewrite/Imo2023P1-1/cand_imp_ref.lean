import Mathlib

-- ===== unified context (both sides' local defs, merged) =====
abbrev ConsecutiveFactors (n a b : ℕ) :=
  a ∣ n ∧ b ∣ n ∧ a < b ∧ ¬∃ c, (c ∣ n ∧ a < c ∧ c < b)

abbrev Dividable (n : ℕ) :=
  ∀ {a b c : ℕ},
    ConsecutiveFactors n a b ∧ ConsecutiveFactors n b c
    → a ∣ b + c

abbrev solution_set : Set ℕ := { n | ¬n.Prime ∧ IsPrimePow n }

-- ===== assumed statement (antecedent) =====
theorem problem_statement_assumed :
  ∀ n : ℕ, n > 1 →
    (∃ p : ℕ, Nat.Prime p ∧ ∃ k : ℕ, k ≥ 2 ∧ n = p ^ k) ↔
    (∃ (d : ℕ → ℕ),
      (∀ i : ℕ, i < n.divisors.card → d i ∈ n.divisors) ∧
      (∀ i j : ℕ, i < j ∧ j < n.divisors.card → d i < d j) ∧
      (∀ d' : ℕ, d' ∈ n.divisors → ∃ i : ℕ, i < n.divisors.card ∧ d i = d') ∧
      d 0 = 1 ∧
      d (n.divisors.card - 1) = n ∧
      (∀ i : ℕ, i < n.divisors.card - 2 → d i ∣ d (i + 1) + d (i + 2))) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2023_p1 : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ Dividable n } := by
  classical
  ext n
  simp only [solution_set, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hnPrime, hnPow⟩
    obtain ⟨p, k, hp, hk, hpk⟩ := (isPrimePow_nat_iff n).mp hnPow
    have hk2 : 2 ≤ k := by
      exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨Nat.ne_of_gt hk, fun hk1 =>
        hnPrime (by rw [← hpk, hk1, pow_one]; exact hp)⟩
    have hn : 1 < n := by
      rw [← hpk]
      exact one_lt_pow₀ hp.one_lt (Nat.ne_of_gt hk)
    have henum := (problem_statement_assumed n).mp (fun _ => ⟨p, hp, k, hk2, hpk.symm⟩)
    rcases henum with ⟨d, hmem, hinc, hsurj, _hd0, _hdlast, hdiv⟩
    refine ⟨hn, hnPrime, ?_⟩
    intro a b c habc
    have hn0 : n ≠ 0 := ne_of_gt (lt_trans Nat.zero_lt_one hn)
    obtain ⟨ia, hia, hiaVal⟩ := hsurj a (Nat.mem_divisors.mpr ⟨habc.1.1, hn0⟩)
    obtain ⟨ib, hib, hibVal⟩ := hsurj b (Nat.mem_divisors.mpr ⟨habc.1.2.1, hn0⟩)
    obtain ⟨ic, hic, hicVal⟩ := hsurj c (Nat.mem_divisors.mpr ⟨habc.2.2.1, hn0⟩)
    have index_lt {i j : ℕ} (hi : i < n.divisors.card) (hj : j < n.divisors.card)
        (hv : d i < d j) : i < j := by
      apply lt_of_not_ge
      intro hji
      rcases hji.eq_or_lt with heq | hlt
      · subst j
        exact (Nat.lt_irrefl _ hv)
      · exact (Nat.not_lt_of_ge hv.le) (hinc j i ⟨hlt, hi⟩)
    have hiab : ia < ib := index_lt hia hib (by simpa only [hiaVal, hibVal] using habc.1.2.2.1)
    have hibc : ib < ic := index_lt hib hic (by simpa only [hibVal, hicVal] using habc.2.2.2.1)
    have hibEq : ib = ia + 1 := by
      apply Nat.le_antisymm
      · apply le_of_not_gt
        intro hgap
        have hmidmem := hmem (ia + 1) (hgap.trans hib)
        exact habc.1.2.2.2 ⟨d (ia + 1), (Nat.mem_divisors.mp hmidmem).1,
          by simpa only [hiaVal] using hinc ia (ia + 1) ⟨Nat.lt_succ_self ia, hgap.trans hib⟩,
          by simpa only [hibVal] using hinc (ia + 1) ib ⟨hgap, hib⟩⟩
      · exact Nat.succ_le_iff.mpr hiab
    have hicEq : ic = ib + 1 := by
      apply Nat.le_antisymm
      · apply le_of_not_gt
        intro hgap
        have hmidmem := hmem (ib + 1) (hgap.trans hic)
        exact habc.2.2.2.2 ⟨d (ib + 1), (Nat.mem_divisors.mp hmidmem).1,
          by simpa only [hibVal] using hinc ib (ib + 1) ⟨Nat.lt_succ_self ib, hgap.trans hic⟩,
          by simpa only [hicVal] using hinc (ib + 1) ic ⟨hgap, hic⟩⟩
      · exact Nat.succ_le_iff.mpr hibc
    have hi2 : ia + 2 < n.divisors.card := by
      simpa only [hicEq, hibEq, Nat.add_assoc, one_add_one_eq_two] using hic
    have hd := hdiv ia (Nat.lt_sub_iff_add_lt.mpr hi2)
    have hs1 : d (ia + 1) = b := by simpa only [← hibEq] using hibVal
    have hs2 : d (ia + 2) = c := by
      simpa only [hicEq, hibEq, Nat.add_assoc, one_add_one_eq_two] using hicVal
    simpa only [hiaVal, hs1, hs2] using hd
  · rintro ⟨hn, hnPrime, hDiv⟩
    have hn0 : n ≠ 0 := ne_of_gt (lt_trans Nat.zero_lt_one hn)
    let e := n.divisors.orderIsoOfFin rfl
    let d : ℕ → ℕ := fun i => if hi : i < n.divisors.card then (e ⟨i, hi⟩ : ℕ) else 0
    have hmem : ∀ i : ℕ, i < n.divisors.card → d i ∈ n.divisors := by
      intro i hi
      simp only [d, hi, ↓reduceDIte]
      exact (e ⟨i, hi⟩).property
    have hinc : ∀ i j : ℕ, i < j ∧ j < n.divisors.card → d i < d j := by
      intro i j hij
      have hi : i < n.divisors.card := hij.1.trans hij.2
      simp only [d, hi, hij.2, ↓reduceDIte]
      exact e.lt_iff_lt.mpr hij.1
    have hsurj : ∀ d' : ℕ, d' ∈ n.divisors →
        ∃ i : ℕ, i < n.divisors.card ∧ d i = d' := by
      intro d' hd'
      obtain ⟨i, hi⟩ := e.surjective ⟨d', hd'⟩
      exact ⟨i, i.isLt, by simpa only [d, i.isLt, ↓reduceDIte] using congrArg Subtype.val hi⟩
    have h1mem : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr hn0
    have hcard : 0 < n.divisors.card := Finset.card_pos.mpr ⟨1, h1mem⟩
    have hd0 : d 0 = 1 := by
      simp only [d, hcard, ↓reduceDIte]
      apply Nat.le_antisymm
      · have hfin : (⟨0, hcard⟩ : Fin n.divisors.card) ≤ e.symm ⟨1, h1mem⟩ :=
          Nat.zero_le _
        simpa only [e.apply_symm_apply] using e.le_iff_le.mpr hfin
      · apply Nat.one_le_iff_ne_zero.mpr
        intro hz
        have hzdiv : (0 : ℕ) ∣ n := by
          simpa only [hz] using (Nat.mem_divisors.mp (e ⟨0, hcard⟩).property).1
        exact hn0 (zero_dvd_iff.mp hzdiv)
    have hlastlt : n.divisors.card - 1 < n.divisors.card := Nat.sub_lt hcard Nat.zero_lt_one
    have hnmem : n ∈ n.divisors := Nat.mem_divisors_self n hn0
    have hdlast : d (n.divisors.card - 1) = n := by
      simp only [d, hlastlt, ↓reduceDIte]
      apply Nat.le_antisymm
      · exact Nat.le_of_dvd (Nat.zero_lt_of_lt hn) (Nat.mem_divisors.mp (e ⟨_, hlastlt⟩).property).1
      · have hle : e.symm ⟨n, hnmem⟩ ≤ (⟨n.divisors.card - 1, hlastlt⟩ : Fin n.divisors.card) :=
          Nat.le_sub_one_of_lt (e.symm ⟨n, hnmem⟩).isLt
        have hle' := e.le_iff_le.mpr hle
        change n ≤ (e ⟨n.divisors.card - 1, hlastlt⟩ : ℕ)
        simpa only [e.apply_symm_apply] using hle'
    have hadj (i : ℕ) (hi : i + 1 < n.divisors.card) :
        ConsecutiveFactors n (d i) (d (i + 1)) := by
      have hi0 : i < n.divisors.card := (Nat.lt_succ_self i).trans hi
      refine ⟨(Nat.mem_divisors.mp (hmem i hi0)).1,
        (Nat.mem_divisors.mp (hmem (i + 1) hi)).1, hinc i (i + 1) ⟨Nat.lt_succ_self i, hi⟩, ?_⟩
      rintro ⟨x, hxdiv, hix, hxi⟩
      have hxmem : x ∈ n.divisors := Nat.mem_divisors.mpr ⟨hxdiv, hn0⟩
      let j := e.symm ⟨x, hxmem⟩
      have hd_i : d i = (e ⟨i, hi0⟩ : ℕ) := by simp only [d, hi0, ↓reduceDIte]
      have hd_succ : d (i + 1) = (e ⟨i + 1, hi⟩ : ℕ) := by simp only [d, hi, ↓reduceDIte]
      have hej : (e j : ℕ) = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hxmem⟩)
      have hij : (⟨i, hi0⟩ : Fin n.divisors.card) < j := by
        apply e.lt_iff_lt.mp
        change (e ⟨i, hi0⟩ : ℕ) < (e j : ℕ)
        rw [← hd_i, hej]
        exact hix
      have hji : j < (⟨i + 1, hi⟩ : Fin n.divisors.card) := by
        apply e.lt_iff_lt.mp
        change (e j : ℕ) < (e ⟨i + 1, hi⟩ : ℕ)
        rw [hej, ← hd_succ]
        exact hxi
      exact (Nat.not_lt_of_ge (Nat.succ_le_iff.mpr hij)) hji
    have htail : ∀ i : ℕ, i < n.divisors.card - 2 →
        d i ∣ d (i + 1) + d (i + 2) := by
      intro i hi
      have hi2 : i + 2 < n.divisors.card := Nat.lt_sub_iff_add_lt.mp hi
      have hi1 : i + 1 < n.divisors.card := (Nat.lt_succ_self (i + 1)).trans hi2
      have hnext : i + 1 + 1 < n.divisors.card := by
        simpa only [Nat.add_assoc, one_add_one_eq_two] using hi2
      simpa only [Nat.add_assoc, one_add_one_eq_two] using hDiv ⟨hadj i hi1, hadj (i + 1) hnext⟩
    have hpows := (problem_statement_assumed n).mpr ⟨d, hmem, hinc, hsurj, hd0, hdlast, htail⟩ hn
    obtain ⟨p, hp, k, hk, hpk⟩ := hpows
    exact ⟨hnPrime, (isPrimePow_nat_iff n).mpr ⟨p, k, hp, Nat.zero_lt_of_lt hk, hpk.symm⟩⟩
