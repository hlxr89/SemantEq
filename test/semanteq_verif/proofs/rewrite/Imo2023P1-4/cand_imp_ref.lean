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
  let P : ℕ → Prop := fun n =>
    ∃ (d : List ℕ),
      (∀ x ∈ d, x ∣ n) ∧
      (∀ x : ℕ, x ∣ n → x ∈ d) ∧
      d.Sorted (· < ·) ∧
      d.head? = some 1 ∧
      d.getLast? = some n ∧
      (∀ i : ℕ, i + 1 < d.length → d[i]! ∣ d[i+1]! + d[i+2]!)
  have bridge : ∀ m : ℕ, 1 < m → (P m ↔ Dividable m) := by
    intro m hm
    have hm0 : m ≠ 0 := Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one hm)
    constructor
    · rintro ⟨d, hdvd, hcomplete, hsorted, _, _, hstep⟩
      have hmono := List.sortedLT_iff_getElem_lt_getElem_of_lt.mp hsorted.sortedLT
      intro a b c habc
      rcases habc with ⟨⟨ha, hb, hab, hnab⟩, ⟨_, hc, hbc, hnbc⟩⟩
      have ha_mem := hcomplete a ha
      have hb_mem := hcomplete b hb
      have hc_mem := hcomplete c hc
      let ia := d.idxOf a
      let ib := d.idxOf b
      let ic := d.idxOf c
      have hia : ia < d.length := List.idxOf_lt_length_iff.mpr ha_mem
      have hib : ib < d.length := List.idxOf_lt_length_iff.mpr hb_mem
      have hic : ic < d.length := List.idxOf_lt_length_iff.mpr hc_mem
      have ha_at : d[ia] = a := List.getElem_idxOf hia
      have hb_at : d[ib] = b := List.getElem_idxOf hib
      have hc_at : d[ic] = c := List.getElem_idxOf hic
      have ia_lt_ib : ia < ib := by
        by_contra h
        have hib_le : ib ≤ ia := Nat.le_of_not_gt h
        rcases Nat.eq_or_lt_of_le hib_le with heq | hlt
        · apply (Nat.ne_of_lt hab)
          rw [← ha_at, ← hb_at]
          exact getElem_congr rfl heq.symm hia
        · have hba : b < a := by
            rw [← hb_at, ← ha_at]
            exact hmono hlt
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hab)) hba
      have ib_eq : ib = ia + 1 := by
        apply Nat.le_antisymm
        · apply Nat.le_of_not_gt
          intro hgap
          have hi1 : ia + 1 < d.length := Nat.lt_trans hgap hib
          apply hnab
          refine ⟨d[ia + 1], hdvd _ (List.getElem_mem hi1), ?_, ?_⟩
          · rw [← ha_at]
            exact hmono (Nat.lt_add_one ia)
          · rw [← hb_at]
            exact hmono hgap
        · exact Nat.lt_iff_add_one_le.mp ia_lt_ib
      have ib_lt_ic : ib < ic := by
        by_contra h
        have hic_le : ic ≤ ib := Nat.le_of_not_gt h
        rcases Nat.eq_or_lt_of_le hic_le with heq | hlt
        · apply (Nat.ne_of_lt hbc)
          rw [← hb_at, ← hc_at]
          exact getElem_congr rfl heq.symm hib
        · have hcb : c < b := by
            rw [← hc_at, ← hb_at]
            exact hmono hlt
          exact (Nat.not_lt_of_ge (Nat.le_of_lt hbc)) hcb
      have ic_eq : ic = ib + 1 := by
        apply Nat.le_antisymm
        · apply Nat.le_of_not_gt
          intro hgap
          have hi1 : ib + 1 < d.length := Nat.lt_trans hgap hic
          apply hnbc
          refine ⟨d[ib + 1], hdvd _ (List.getElem_mem hi1), ?_, ?_⟩
          · rw [← hb_at]
            exact hmono (Nat.lt_add_one ib)
          · rw [← hc_at]
            exact hmono hgap
        · exact Nat.lt_iff_add_one_le.mp ib_lt_ic
      have hi_step : ia + 1 < d.length := by simpa only [ib_eq] using hib
      have hi2 : ia + 2 < d.length := by
        have : ia + 2 = ic := by
          rw [ic_eq, ib_eq]
        rw [this]
        exact hic
      have hb_succ : d[ia + 1] = b := by
        simpa only [ib_eq] using hb_at
      have hc_two : d[ia + 2] = c := by
        have heq : ia + 2 = ic := by
          rw [ic_eq, ib_eq]
        simpa only [← heq] using hc_at
      have hs := hstep ia hi_step
      simp only [List.getElem!_eq_getElem?_getD, List.getD_getElem?,
        dif_pos hia, dif_pos hi_step, dif_pos hi2] at hs
      simpa only [ha_at, hb_succ, hc_two] using hs
    · intro hdiv
      let d := m.divisors.sort
      have hone_fin : 1 ∈ m.divisors := Nat.one_mem_divisors.mpr hm0
      have hm_fin : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_refl m, hm0⟩
      have hne : m.divisors.Nonempty := ⟨1, hone_fin⟩
      have hd_ne : d ≠ [] := by
        intro he
        have hone : 1 ∈ d := Finset.mem_sort (· ≤ ·) |>.mpr hone_fin
        simpa only [he, List.not_mem_nil] using hone
      have hmin : m.divisors.min' hne = 1 := by
        apply Nat.le_antisymm
        · exact m.divisors.min'_le 1 hone_fin
        · have hdivisor : m.divisors.min' hne ∣ m :=
            (Nat.mem_divisors.mp (m.divisors.min'_mem hne)).1
          exact Nat.one_le_iff_ne_zero.mpr (fun hz => hm0 (by simpa only [hz, zero_dvd_iff] using hdivisor))
      have hmax : m.divisors.max' hne = m := by
        apply Nat.le_antisymm
        · exact Nat.le_of_dvd (Nat.lt_trans Nat.zero_lt_one hm)
            (Nat.mem_divisors.mp (m.divisors.max'_mem hne)).1
        · exact m.divisors.le_max' m hm_fin
      have hsorted : d.Sorted (· < ·) := by
        dsimp [d]
        exact (Finset.sortedLT_sort _).pairwise
      have hmono := List.sortedLT_iff_getElem_lt_getElem_of_lt.mp hsorted.sortedLT
      have hhead : d.head? = some 1 := by
        rw [List.head?_eq_some_head hd_ne, List.head_eq_getElem]
        rw [Finset.sorted_zero_eq_min', hmin]
      have hlast : d.getLast? = some m := by
        rw [List.getLast?_eq_some_getLast hd_ne, List.getLast_eq_getElem]
        rw [Finset.sorted_last_eq_max', hmax]
      refine ⟨d, ?_, ?_, hsorted, hhead, hlast, ?_⟩
      · intro x hx
        exact (Nat.mem_divisors.mp (Finset.mem_sort (· ≤ ·) |>.mp hx)).1
      · intro x hx
        exact Finset.mem_sort (· ≤ ·) |>.mpr (Nat.mem_divisors.mpr ⟨hx, hm0⟩)
      · intro i hi
        have hi0 : i < d.length := Nat.lt_trans (Nat.lt_add_one i) hi
        by_cases hi2 : i + 2 < d.length
        · have adjacent (j : ℕ) (hj : j + 1 < d.length) :
              ConsecutiveFactors m d[j] d[j + 1] := by
            have hj0 : j < d.length := Nat.lt_trans (Nat.lt_add_one j) hj
            refine ⟨?_, ?_, hmono (Nat.lt_add_one j), ?_⟩
            · exact (Nat.mem_divisors.mp (Finset.mem_sort (· ≤ ·) |>.mp
                (List.getElem_mem hj0))).1
            · exact (Nat.mem_divisors.mp (Finset.mem_sort (· ≤ ·) |>.mp
                (List.getElem_mem hj))).1
            · rintro ⟨x, hx, hjx, hxj⟩
              have hxmem : x ∈ d := Finset.mem_sort (· ≤ ·) |>.mpr
                (Nat.mem_divisors.mpr ⟨hx, hm0⟩)
              obtain ⟨k, hk, hxk⟩ := List.mem_iff_getElem.mp hxmem
              rcases Nat.lt_or_ge k (j + 1) with hleft | hright
              · have hkj : k ≤ j := Nat.le_of_lt_succ hleft
                rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
                · exact (Nat.ne_of_lt hjx) hxk
                · have hxa : x < d[j] := by
                    rw [← hxk]
                    exact hmono hlt
                  exact (Nat.not_lt_of_ge (Nat.le_of_lt hjx)) hxa
              · rcases Nat.eq_or_lt_of_le hright with heq | hlt
                · subst k
                  exact (Nat.ne_of_lt hxj) hxk.symm
                · have hbx : d[j + 1] < x := by
                    rw [← hxk]
                    exact hmono hlt
                  exact (Nat.not_lt_of_ge (Nat.le_of_lt hxj)) hbx
          have hs := hdiv ⟨adjacent i hi, adjacent (i + 1) hi2⟩
          simp only [List.getElem!_eq_getElem?_getD, List.getD_getElem?,
            dif_pos hi0, dif_pos hi, dif_pos hi2]
          simpa only [Nat.add_assoc] using hs
        · have hlen_le : d.length ≤ i + 2 := Nat.le_of_not_gt hi2
          have hlen_ge : i + 2 ≤ d.length := by
            simpa only [Nat.add_assoc] using Nat.lt_iff_add_one_le.mp hi
          have hlength : d.length = i + 2 := Nat.le_antisymm hlen_le hlen_ge
          have hm_last : d[i + 1] = m := by
            have hlast_elem : d[d.length - 1] = m := by
              rw [Finset.sorted_last_eq_max', hmax]
            have heq : d.length - 1 = i + 1 := by
              rw [hlength]
              rw [show i + 2 = (i + 1) + 1 by simp only [Nat.add_assoc]]
              exact Nat.add_sub_cancel (i + 1) 1
            simpa only [heq] using hlast_elem
          simp only [List.getElem!_eq_getElem?_getD, List.getD_getElem?,
            dif_pos hi0, dif_pos hi, dif_neg hi2, hm_last]
          exact (Nat.mem_divisors.mp (Finset.mem_sort (· ≤ ·) |>.mp
            (List.getElem_mem hi0))).1
  apply Set.ext
  intro n
  change (¬n.Prime ∧ IsPrimePow n) ↔ (1 < n ∧ ¬n.Prime ∧ Dividable n)
  have hcand := problem_statement_assumed n
  change ((1 < n ∧ ¬n.Prime → P n) ↔
    ∃ (p : ℕ) (k : ℕ), Nat.Prime p ∧ k ≥ 2 ∧ n = p ^ k) at hcand
  constructor
  · rintro ⟨hnprime, hnpp⟩
    have hn : 1 < n := hnpp.one_lt
    obtain ⟨p, k, hp, hk, hpow⟩ := (isPrimePow_nat_iff n).mp hnpp
    have hk2 : 2 ≤ k := by
      cases k with
      | zero => exact (Nat.not_lt_zero 0 hk).elim
      | succ k =>
          cases k with
          | zero =>
              exfalso
              apply hnprime
              rw [← hpow]
              simpa only [zero_add, pow_one] using hp
          | succ k => exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le k))
    have hP : P n := hcand.mpr ⟨p, k, hp, hk2, hpow.symm⟩ ⟨hn, hnprime⟩
    exact ⟨hn, hnprime, (bridge n hn).mp hP⟩
  · rintro ⟨hn, hnprime, hdiv⟩
    have hP : P n := (bridge n hn).mpr hdiv
    obtain ⟨p, k, hp, hk, hpow⟩ := hcand.mp (fun _ => hP)
    refine ⟨hnprime, (isPrimePow_nat_iff n).mpr ?_⟩
    exact ⟨p, k, hp, Nat.lt_of_lt_of_le Nat.zero_lt_two hk, hpow.symm⟩
