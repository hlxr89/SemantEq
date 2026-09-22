import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem exercise_23_3_refs_assumed {X : Type*} [TopologicalSpace X]
  [TopologicalSpace X] {A : ℕ → Set X}
  (hAn : ∀ n, IsConnected (A n))
  (A₀ : Set X)
  (hA : IsConnected A₀)
  (h : ∀ n, A₀ ∩ A n ≠ ∅) :
  IsConnected (A₀ ∪ (⋃ n, A n)) := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_23_3 {X : Type*} [TopologicalSpace X] {ι : Type*}
    (A : Set X) (Aa : ι → Set X)
    (hA : IsConnected A) (hAa : ∀ α, IsConnected (Aa α))
    (hmeet : ∀ α, (A ∩ Aa α).Nonempty) :
    IsConnected (A ∪ ⋃ α, Aa α) := by
  have htwo (B C : Set X) (hB : IsConnected B) (hC : IsConnected C)
      (hAB : (A ∩ B).Nonempty) (hAC : (A ∩ C).Nonempty) :
      IsConnected (A ∪ (B ∪ C)) := by
    have hiUnion : (⋃ n : ℕ, if n = 0 then B else C) = B ∪ C := by
      ext z
      constructor
      · simp only [mem_iUnion]
        rintro ⟨n, hn⟩
        by_cases hn0 : n = 0
        · exact Or.inl (by simpa [hn0] using hn)
        · exact Or.inr (by simpa [hn0] using hn)
      · rintro (hzB | hzC)
        · exact mem_iUnion.2 ⟨0, by simpa using hzB⟩
        · exact mem_iUnion.2 ⟨1, by simpa using hzC⟩
    have hassumed := exercise_23_3_refs_assumed
        (A := fun n : ℕ => if n = 0 then B else C)
        (fun n => by simp only; split <;> assumption) A hA
        (fun n => by
          simp only
          split
          · exact Set.nonempty_iff_ne_empty.1 hAB
          · exact Set.nonempty_iff_ne_empty.1 hAC)
    rwa [hiUnion] at hassumed
  obtain ⟨a, ha⟩ := hA.nonempty
  have hAA : (A ∩ A).Nonempty := ⟨a, ha, ha⟩
  have hbase := htwo A A hA hA hAA hAA
  refine ⟨hbase.nonempty.mono (fun z hz => Or.inl (hz.elim id (fun hz' => hz'.elim id id))), ?_⟩
  intro u v hu hv huv
  rintro ⟨x, hx, hxu⟩ ⟨y, hy, hyv⟩
  rcases hx with hxA | hxAa
  · rcases hy with hyA | hyAa
    ·
      have hconn := htwo A A hA hA hAA hAA
      have hinter := hconn.isPreconnected u v hu hv
        (by intro z hz; exact huv (Or.inl (hz.elim id (fun hz' => hz'.elim id id))))
        ⟨x, Or.inl hxA, hxu⟩ ⟨y, Or.inl hyA, hyv⟩
      exact hinter.mono (fun z hz => ⟨Or.inl (hz.1.elim id (fun hz' => hz'.elim id id)), hz.2⟩)
    · simp only [mem_iUnion] at hyAa
      obtain ⟨β, hyβ⟩ := hyAa
      have hconn := htwo A (Aa β) hA (hAa β) hAA (hmeet β)
      have hinter := hconn.isPreconnected u v hu hv
        (by intro z hz; exact huv (hz.elim Or.inl (fun hz' => hz'.elim Or.inl (fun hzβ => Or.inr (mem_iUnion.2 ⟨β, hzβ⟩)))))
        ⟨x, Or.inl hxA, hxu⟩ ⟨y, Or.inr (Or.inr hyβ), hyv⟩
      exact hinter.mono (fun z hz => ⟨hz.1.elim Or.inl (fun hz' => hz'.elim Or.inl
        (fun hzβ => Or.inr (mem_iUnion.2 ⟨β, hzβ⟩))), hz.2⟩)
  · simp only [mem_iUnion] at hxAa
    obtain ⟨α, hxα⟩ := hxAa
    rcases hy with hyA | hyAa
    ·
      have hconn := htwo (Aa α) A (hAa α) hA (hmeet α) hAA
      have hinter := hconn.isPreconnected u v hu hv
        (by intro z hz; exact huv (hz.elim Or.inl (fun hz' => hz'.elim (fun hzα => Or.inr (mem_iUnion.2 ⟨α, hzα⟩)) Or.inl)))
        ⟨x, Or.inr (Or.inl hxα), hxu⟩ ⟨y, Or.inl hyA, hyv⟩
      exact hinter.mono (fun z hz => ⟨hz.1.elim Or.inl (fun hz' => hz'.elim
        (fun hzα => Or.inr (mem_iUnion.2 ⟨α, hzα⟩)) Or.inl), hz.2⟩)
    · simp only [mem_iUnion] at hyAa
      obtain ⟨β, hyβ⟩ := hyAa
      have hconn := htwo (Aa α) (Aa β) (hAa α) (hAa β) (hmeet α) (hmeet β)
      have hinter := hconn.isPreconnected u v hu hv
        (by
          intro z hz
          exact huv (hz.elim Or.inl (fun hz' => hz'.elim
            (fun hzα => Or.inr (mem_iUnion.2 ⟨α, hzα⟩))
            (fun hzβ => Or.inr (mem_iUnion.2 ⟨β, hzβ⟩)))))
        ⟨x, Or.inr (Or.inl hxα), hxu⟩ ⟨y, Or.inr (Or.inr hyβ), hyv⟩
      exact hinter.mono (fun z hz => ⟨hz.1.elim Or.inl (fun hz' => hz'.elim
        (fun hzα => Or.inr (mem_iUnion.2 ⟨α, hzα⟩))
        (fun hzβ => Or.inr (mem_iUnion.2 ⟨β, hzβ⟩))), hz.2⟩)
