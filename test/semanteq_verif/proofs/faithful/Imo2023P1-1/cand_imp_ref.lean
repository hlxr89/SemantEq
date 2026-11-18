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
  ext n
  have bridge : 1 < n → (Dividable n ↔
      (∃ (d : ℕ → ℕ),
        (∀ i : ℕ, i < n.divisors.card → d i ∈ n.divisors) ∧
        (∀ i j : ℕ, i < j ∧ j < n.divisors.card → d i < d j) ∧
        (∀ d' : ℕ, d' ∈ n.divisors → ∃ i : ℕ, i < n.divisors.card ∧ d i = d') ∧
        d 0 = 1 ∧ d (n.divisors.card - 1) = n ∧
        (∀ i : ℕ, i < n.divisors.card - 2 → d i ∣ d (i + 1) + d (i + 2)))) := by
    intro hn
    have hn0 : n ≠ 0 := by omega
    constructor
    · intro hdiv
      let e : Fin n.divisors.card ≃o n.divisors := Finset.orderIsoOfFin n.divisors rfl
      let d : ℕ → ℕ := fun i => if hi : i < n.divisors.card then (e ⟨i, hi⟩ : ℕ) else 0
      have hcard : 0 < n.divisors.card :=
        Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn0⟩
      have hmem : ∀ i, i < n.divisors.card → d i ∈ n.divisors := by
        intro i hi
        simp [d, hi]
      have hlt : ∀ i j, i < j ∧ j < n.divisors.card → d i < d j := by
        intro i j hij
        simp only [d, hij.2, show i < n.divisors.card by omega, dite_true]
        exact e.strictMono (by simpa using hij.1)
      have hsurj : ∀ d', d' ∈ n.divisors → ∃ i, i < n.divisors.card ∧ d i = d' := by
        intro d' hd'
        obtain ⟨i, hi⟩ := e.surjective ⟨d', hd'⟩
        refine ⟨i, i.isLt, ?_⟩
        simp [d, i.isLt, hi]
      have hd0 : d 0 = 1 := by
        obtain ⟨j, hj, hdj⟩ := hsurj 1 (Nat.one_mem_divisors.mpr hn0)
        have hle : d 0 ≤ d j := by
          by_cases hj0 : j = 0
          · simp [hj0]
          · exact (hlt 0 j ⟨Nat.pos_of_ne_zero hj0, hj⟩).le
        have hpos : 0 < d 0 := by
          exact Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp (hmem 0 hcard)).1 (by omega)
        omega
      have hdlast : d (n.divisors.card - 1) = n := by
        obtain ⟨j, hj, hdj⟩ := hsurj n (Nat.mem_divisors_self n hn0)
        have hjle : j ≤ n.divisors.card - 1 := by omega
        have hle : d j ≤ d (n.divisors.card - 1) := by
          rcases hjle.eq_or_lt with h | h
          · simp [h]
          · exact (hlt j (n.divisors.card - 1) ⟨h, by omega⟩).le
        have hlastdvd : d (n.divisors.card - 1) ∣ n :=
          (Nat.mem_divisors.mp (hmem _ (by omega))).1
        have hlastle : d (n.divisors.card - 1) ≤ n := Nat.le_of_dvd (by omega) hlastdvd
        omega
      refine ⟨d, hmem, hlt, hsurj, hd0, hdlast, ?_⟩
      intro i hi
      have hi0 : i < n.divisors.card := by omega
      have hi1 : i + 1 < n.divisors.card := by omega
      have hi2 : i + 2 < n.divisors.card := by omega
      apply hdiv
      constructor
      · refine ⟨(Nat.mem_divisors.mp (hmem i hi0)).1,
          (Nat.mem_divisors.mp (hmem (i + 1) hi1)).1,
          hlt i (i + 1) ⟨by omega, hi1⟩, ?_⟩
        rintro ⟨c, hcdiv, hic, hci⟩
        obtain ⟨j, hj, hdj⟩ := hsurj c (Nat.mem_divisors.mpr ⟨hcdiv, hn0⟩)
        rw [← hdj] at hic hci
        have hij : i < j := by
          by_contra h
          have hji : j ≤ i := by omega
          rcases hji.eq_or_lt with hji | hji
          · subst j
            omega
          · have := hlt j i ⟨hji, hi0⟩; omega
        have hji1 : j < i + 1 := by
          by_contra h
          have hi1j : i + 1 ≤ j := by omega
          rcases hi1j.eq_or_lt with hji | hji
          · subst j
            omega
          · have := hlt (i + 1) j ⟨hji, hj⟩; omega
        omega
      · refine ⟨(Nat.mem_divisors.mp (hmem (i + 1) hi1)).1,
          (Nat.mem_divisors.mp (hmem (i + 2) hi2)).1,
          hlt (i + 1) (i + 2) ⟨by omega, hi2⟩, ?_⟩
        rintro ⟨c, hcdiv, hic, hci⟩
        obtain ⟨j, hj, hdj⟩ := hsurj c (Nat.mem_divisors.mpr ⟨hcdiv, hn0⟩)
        rw [← hdj] at hic hci
        have hij : i + 1 < j := by
          by_contra h
          have hji : j ≤ i + 1 := by omega
          rcases hji.eq_or_lt with hji | hji
          · subst j
            omega
          · have := hlt j (i + 1) ⟨hji, hi1⟩; omega
        have hji2 : j < i + 2 := by
          by_contra h
          have hi2j : i + 2 ≤ j := by omega
          rcases hi2j.eq_or_lt with hji | hji
          · subst j
            omega
          · have := hlt (i + 2) j ⟨hji, hj⟩; omega
        omega
    · rintro ⟨d, hmem, hlt, hsurj, hd0, hdlast, hadj⟩ a b c ⟨hab, hbc⟩
      obtain ⟨ia, hia, hda⟩ := hsurj a (Nat.mem_divisors.mpr ⟨hab.1, hn0⟩)
      obtain ⟨ib, hib, hdb⟩ := hsurj b (Nat.mem_divisors.mpr ⟨hab.2.1, hn0⟩)
      obtain ⟨ic, hic, hdc⟩ := hsurj c (Nat.mem_divisors.mpr ⟨hbc.2.1, hn0⟩)
      have hablt : d ia < d ib := by simpa [hda, hdb] using hab.2.2.1
      have hbclt : d ib < d ic := by simpa [hdb, hdc] using hbc.2.2.1
      have hiab : ia < ib := by
        by_contra h
        have hba : ib ≤ ia := by omega
        rcases hba.eq_or_lt with hba | hba
        · subst ib
          omega
        · have := hlt ib ia ⟨hba, hia⟩; omega
      have hibc : ib < ic := by
        by_contra h
        have hcb : ic ≤ ib := by omega
        rcases hcb.eq_or_lt with hcb | hcb
        · subst ic
          omega
        · have := hlt ic ib ⟨hcb, hib⟩; omega
      have hib_eq : ib = ia + 1 := by
        by_contra h
        have hgap : ia + 1 < ib := by omega
        apply hab.2.2.2
        refine ⟨d (ia + 1), (Nat.mem_divisors.mp (hmem _ (by omega))).1, ?_, ?_⟩
        · have := hlt ia (ia + 1) ⟨by omega, by omega⟩; omega
        · have := hlt (ia + 1) ib ⟨hgap, hib⟩; omega
      have hic_eq : ic = ib + 1 := by
        by_contra h
        have hgap : ib + 1 < ic := by omega
        apply hbc.2.2.2
        refine ⟨d (ib + 1), (Nat.mem_divisors.mp (hmem _ (by omega))).1, ?_, ?_⟩
        · have := hlt ib (ib + 1) ⟨by omega, by omega⟩; omega
        · have := hlt (ib + 1) ic ⟨hgap, hic⟩; omega
      have ha := hadj ia (by omega)
      rw [hda] at ha
      rw [← hib_eq, hdb] at ha
      have hic_eq' : ic = ia + 2 := by omega
      rw [← hic_eq', hdc] at ha
      exact ha
  constructor
  · rintro ⟨hnprime, hispp⟩
    rcases (isPrimePow_nat_iff n).mp hispp with ⟨p, k, hp, hk, hpk⟩
    have hk2 : 2 ≤ k := by
      have hk1 : k ≠ 1 := by
        intro h
        apply hnprime
        have hpn : p = n := by simpa [h] using hpk
        rw [← hpn]
        exact hp
      omega
    have hn : 1 < n := by
      rw [← hpk]
      exact one_lt_pow₀ hp.one_lt (by omega)
    have henum := (problem_statement_assumed n).mp (by
      intro _
      exact ⟨p, hp, k, hk2, hpk.symm⟩)
    exact ⟨hn, hnprime, (bridge hn).mpr henum⟩
  · rintro ⟨hn, hnprime, hdiv⟩
    have henum := (bridge hn).mp hdiv
    have hpp := (problem_statement_assumed n).mpr henum
    rcases hpp hn with ⟨p, hp, k, hk, hpk⟩
    exact ⟨hnprime, (isPrimePow_nat_iff n).mpr ⟨p, k, hp, by omega, hpk.symm⟩⟩
