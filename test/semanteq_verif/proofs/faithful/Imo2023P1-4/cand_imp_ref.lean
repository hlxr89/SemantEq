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
  ∀ n : ℕ, n > 1 ∧ ¬ Nat.Prime n → 
  (∃ (d : List ℕ), 
    (∀ x ∈ d, x ∣ n) ∧ 
    (∀ x : ℕ, x ∣ n → x ∈ d) ∧
    d.Sorted (· < ·) ∧
    d.head? = some 1 ∧
    d.getLast? = some n ∧
    (∀ i : ℕ, i + 1 < d.length → d[i]! ∣ d[i+1]! + d[i+2]!)) ↔
  (∃ (p : ℕ) (k : ℕ), Nat.Prime p ∧ k ≥ 2 ∧ n = p ^ k) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem imo2023_p1 : solution_set = { n | 1 < n ∧ ¬n.Prime ∧ Dividable n } := by
  have fromList (n : ℕ) :
      (∃ (d : List ℕ),
        (∀ x ∈ d, x ∣ n) ∧
        (∀ x : ℕ, x ∣ n → x ∈ d) ∧
        d.Sorted (· < ·) ∧
        d.head? = some 1 ∧
        d.getLast? = some n ∧
        (∀ i : ℕ, i + 1 < d.length → d[i]! ∣ d[i+1]! + d[i+2]!)) →
      Dividable n := by
    rintro ⟨d, hdvd, hcomplete, hsorted, -, -, hstep⟩ a b c ⟨hab, hbc⟩
    rcases hab with ⟨ha, hb, hab, hnab⟩
    rcases hbc with ⟨-, hc, hbc, hnbc⟩
    obtain ⟨ia, hia, eia⟩ := List.getElem_of_mem (hcomplete a ha)
    obtain ⟨ib, hib, eib⟩ := List.getElem_of_mem (hcomplete b hb)
    obtain ⟨ic, hic, eic⟩ := List.getElem_of_mem (hcomplete c hc)
    have hiab : ia < ib := by
      by_contra h
      have hle : ib ≤ ia := Nat.le_of_not_gt h
      rcases hle.eq_or_lt with heq | hlt
      · subst ib
        omega
      · have hba := List.Pairwise.rel_get_of_lt hsorted (a := ⟨ib, hib⟩) (b := ⟨ia, hia⟩) hlt
        simp only [List.get_eq_getElem, eia, eib] at hba
        omega
    have hibc : ib < ic := by
      by_contra h
      have hle : ic ≤ ib := Nat.le_of_not_gt h
      rcases hle.eq_or_lt with heq | hlt
      · subst ic
        omega
      · have hcb := List.Pairwise.rel_get_of_lt hsorted (a := ⟨ic, hic⟩) (b := ⟨ib, hib⟩) hlt
        simp only [List.get_eq_getElem, eib, eic] at hcb
        omega
    have eiab : ib = ia + 1 := by
      by_contra hne
      have hgap : ia + 1 < ib := by omega
      have hi1 : ia + 1 < d.length := lt_trans hgap hib
      have hal := List.Pairwise.rel_get_of_lt hsorted (a := ⟨ia, hia⟩) (b := ⟨ia + 1, hi1⟩)
        (show ia < ia + 1 by omega)
      have hlb := List.Pairwise.rel_get_of_lt hsorted (a := ⟨ia + 1, hi1⟩) (b := ⟨ib, hib⟩) hgap
      apply hnab
      refine ⟨d[ia + 1], hdvd _ (List.getElem_mem hi1), ?_, ?_⟩
      · simpa only [List.get_eq_getElem, eia] using hal
      · simpa only [List.get_eq_getElem, eib] using hlb
    have eibc : ic = ib + 1 := by
      by_contra hne
      have hgap : ib + 1 < ic := by omega
      have hi1 : ib + 1 < d.length := lt_trans hgap hic
      have hbl := List.Pairwise.rel_get_of_lt hsorted (a := ⟨ib, hib⟩) (b := ⟨ib + 1, hi1⟩)
        (show ib < ib + 1 by omega)
      have hlc := List.Pairwise.rel_get_of_lt hsorted (a := ⟨ib + 1, hi1⟩) (b := ⟨ic, hic⟩) hgap
      apply hnbc
      refine ⟨d[ib + 1], hdvd _ (List.getElem_mem hi1), ?_, ?_⟩
      · simpa only [List.get_eq_getElem, eib] using hbl
      · simpa only [List.get_eq_getElem, eic] using hlc
    have ha' : d[ia]! = a := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hia, eia]
    have hb' : d[ia + 1]! = b := by
      rw [← eiab]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hib, eib]
    have hc' : d[ia + 2]! = c := by
      have he : ic = ia + 2 := by omega
      rw [← he]
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hic, eic]
    simpa only [ha', hb', hc'] using hstep ia (by omega)
  have toList (n : ℕ) (hn : 0 < n) (hdiv : Dividable n) :
      ∃ (d : List ℕ),
        (∀ x ∈ d, x ∣ n) ∧
        (∀ x : ℕ, x ∣ n → x ∈ d) ∧
        d.Sorted (· < ·) ∧
        d.head? = some 1 ∧
        d.getLast? = some n ∧
        (∀ i : ℕ, i + 1 < d.length → d[i]! ∣ d[i+1]! + d[i+2]!) := by
    let d := n.divisors.sort (· ≤ ·)
    have hmem (x : ℕ) : x ∈ d ↔ x ∣ n := by
      simp [d, Finset.mem_sort, Nat.mem_divisors, hn.ne']
    have hsorted : d.Sorted (· < ·) := by
      simpa [d] using (Finset.sortedLT_sort n.divisors).pairwise
    have hone : 1 ∈ d := (hmem 1).2 (one_dvd n)
    have hnmem : n ∈ d := (hmem n).2 (dvd_refl n)
    have hdne : d ≠ [] := by
      intro he
      simpa [he] using hone
    have hdpos : 0 < d.length := List.length_pos_iff.mpr hdne
    have hhead : d.head? = some 1 := by
      have hi := (List.idxOf_lt_length_iff).2 hone
      have helem := List.getElem_idxOf hi
      have hiz : d.idxOf 1 = 0 := by
        by_contra hz
        have hzpos : 0 < d.idxOf 1 := Nat.pos_of_ne_zero hz
        have hlt := List.Pairwise.rel_get_of_lt hsorted
          (a := ⟨0, lt_of_lt_of_le hzpos (Nat.le_of_lt hi)⟩)
          (b := ⟨d.idxOf 1, hi⟩) hzpos
        have hpos := Nat.pos_of_dvd_of_pos ((hmem d[0]).1 (List.getElem_mem _)) hn
        simp only [List.get_eq_getElem, helem] at hlt
        omega
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hdpos]
      simpa [hiz] using congrArg some helem
    have hlast : d.getLast? = some n := by
      have hi := (List.idxOf_lt_length_iff).2 hnmem
      have helem := List.getElem_idxOf hi
      have hilast : d.idxOf n = d.length - 1 := by
        have hs : d.idxOf n + 1 = d.length := by
          by_contra hne
          have hnext : d.idxOf n + 1 < d.length := by omega
          have hlt := List.Pairwise.rel_get_of_lt hsorted
            (a := ⟨d.idxOf n, hi⟩) (b := ⟨d.idxOf n + 1, hnext⟩)
            (show d.idxOf n < d.idxOf n + 1 by omega)
          have hle := Nat.le_of_dvd hn ((hmem d[d.idxOf n + 1]).1 (List.getElem_mem hnext))
          simp only [List.get_eq_getElem, helem] at hlt
          omega
        omega
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
      simpa [hilast] using congrArg some helem
    refine ⟨d, fun x hx => (hmem x).1 hx, fun x hx => (hmem x).2 hx,
      hsorted, hhead, hlast, ?_⟩
    intro i hi
    have hi0 : i < d.length := by omega
    have hi1 : i + 1 < d.length := hi
    have hdvd0 : d[i] ∣ n := (hmem d[i]).1 (List.getElem_mem hi0)
    have hdvd1 : d[i + 1] ∣ n := (hmem d[i + 1]).1 (List.getElem_mem hi1)
    have bang0 : d[i]! = d[i] := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi0]
    have bang1 : d[i + 1]! = d[i + 1] := by
      simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi1]
    by_cases hi2 : i + 2 < d.length
    · have hdvd2 : d[i + 2] ∣ n := (hmem d[i + 2]).1 (List.getElem_mem hi2)
      have bang2 : d[i + 2]! = d[i + 2] := by
        simp [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi2]
      rw [bang0, bang1, bang2]
      apply hdiv
      constructor
      · refine ⟨hdvd0, hdvd1, ?_, ?_⟩
        · exact List.Pairwise.rel_get_of_lt hsorted (a := ⟨i, hi0⟩) (b := ⟨i + 1, hi1⟩)
            (show i < i + 1 by omega)
        · rintro ⟨x, hx, hl, hr⟩
          obtain ⟨j, hj, ej⟩ := List.getElem_of_mem ((hmem x).2 hx)
          have hij : i < j := by
            by_contra h
            have hji : j ≤ i := Nat.le_of_not_gt h
            rcases hji.eq_or_lt with he | hlt
            · subst j
              omega
            · have := List.Pairwise.rel_get_of_lt hsorted (a := ⟨j, hj⟩) (b := ⟨i, hi0⟩) hlt
              simp only [List.get_eq_getElem, ej] at this
              omega
          have hji1 : j < i + 1 := by
            by_contra h
            have hij1 : i + 1 ≤ j := Nat.le_of_not_gt h
            rcases hij1.eq_or_lt with he | hlt
            · subst j
              omega
            · have := List.Pairwise.rel_get_of_lt hsorted (a := ⟨i + 1, hi1⟩) (b := ⟨j, hj⟩) hlt
              simp only [List.get_eq_getElem, ej] at this
              omega
          omega
      · refine ⟨hdvd1, hdvd2, ?_, ?_⟩
        · exact List.Pairwise.rel_get_of_lt hsorted (a := ⟨i + 1, hi1⟩) (b := ⟨i + 2, hi2⟩)
            (show i + 1 < i + 2 by omega)
        · rintro ⟨x, hx, hl, hr⟩
          obtain ⟨j, hj, ej⟩ := List.getElem_of_mem ((hmem x).2 hx)
          have hij : i + 1 < j := by
            by_contra h
            have hji : j ≤ i + 1 := Nat.le_of_not_gt h
            rcases hji.eq_or_lt with he | hlt
            · subst j
              omega
            · have := List.Pairwise.rel_get_of_lt hsorted (a := ⟨j, hj⟩) (b := ⟨i + 1, hi1⟩) hlt
              simp only [List.get_eq_getElem, ej] at this
              omega
          have hji2 : j < i + 2 := by
            by_contra h
            have hij2 : i + 2 ≤ j := Nat.le_of_not_gt h
            rcases hij2.eq_or_lt with he | hlt
            · subst j
              omega
            · have := List.Pairwise.rel_get_of_lt hsorted (a := ⟨i + 2, hi2⟩) (b := ⟨j, hj⟩) hlt
              simp only [List.get_eq_getElem, ej] at this
              omega
          omega
    · have bang2 : d[i + 2]! = 0 := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi2)]
        rfl
      have eilast : i + 1 = d.length - 1 := by omega
      have elast : d[i + 1] = n := by
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
        injection hlast with he
        simpa [eilast] using he
      rw [bang0, bang1, bang2, elast, Nat.add_zero]
      exact hdvd0
  apply Set.ext
  intro n
  constructor
  · rintro ⟨hnprime, hpow⟩
    rcases hpow with ⟨p, k, hp, hk, hpn⟩
    have hn : 1 < n := by
      rw [← hpn]
      exact one_lt_pow₀ (Nat.Prime.one_lt (Nat.prime_iff.mpr hp)) hk.ne'
    have hk2 : k ≥ 2 := by
      by_contra h
      have : k = 1 := by omega
      subst k
      apply hnprime
      rw [← hpn]
      simpa using (Nat.prime_iff.mpr hp)
    have hrepr : ∃ (p : ℕ) (k : ℕ), Nat.Prime p ∧ k ≥ 2 ∧ n = p ^ k :=
      ⟨p, k, Nat.prime_iff.mpr hp, hk2, hpn.symm⟩
    have hlist := (problem_statement_assumed n).2 hrepr ⟨hn, hnprime⟩
    exact ⟨hn, hnprime, fromList n hlist⟩
  · rintro ⟨hn, hnprime, hdiv⟩
    have hlist := toList n (by omega) hdiv
    rcases (problem_statement_assumed n).1 (fun _ => hlist) with ⟨p, k, hp, hk, hpn⟩
    refine ⟨hnprime, p, k, hp.prime, by omega, ?_⟩
    exact hpn.symm
