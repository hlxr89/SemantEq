import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

-- ===== unified context (both sides' local defs, merged) =====
-- empty

-- ===== assumed statement (antecedent) =====
theorem dummy_assumed {X : Type*} [MetricSpace X] [CompactSpace X] [T2Space X] {X1 X2 : Set X} (hX1 : IsClosed X1) (hX2 : IsClosed X2) (h1 : MetrizableSpace X1) (h2 : MetrizableSpace X2) (hX : X1 ∪ X2 = Set.univ) : MetrizableSpace X := by
  sorry

-- ===== goal statement, PROVED from the antecedent =====
theorem exercise_34_9
  (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
  (X1 X2 : Set X) (hX1 : IsClosed X1) (hX2 : IsClosed X2)
  (hX : X1 ∪ X2 = univ) (hX1m : MetrizableSpace X1)
  (hX2m : MetrizableSpace X2) : MetrizableSpace X := by
  letI : MetrizableSpace X1 := hX1m
  letI : MetrizableSpace X2 := hX2m
  letI : CompactSpace X1 := isCompact_iff_compactSpace.mp hX1.isCompact
  letI : CompactSpace X2 := isCompact_iff_compactSpace.mp hX2.isCompact
  letI : SecondCountableTopology X1 := inferInstance
  letI : SecondCountableTopology X2 := inferInstance
  let N : Set (Set X) :=
    (fun s : Set X1 ↦ ((↑) '' s : Set X)) '' countableBasis X1 ∪
      (fun s : Set X2 ↦ ((↑) '' s : Set X)) '' countableBasis X2
  have hNc : N.Countable :=
    (countable_countableBasis X1).image _ |>.union ((countable_countableBasis X2).image _)
  have hN : ∀ (x : X) (U : Set X), x ∈ U → IsOpen U → ∃ V ∈ N, x ∈ V ∧ V ⊆ U := by
    intro x U hxU hU
    have hx : x ∈ X1 ∨ x ∈ X2 := by
      simpa only [← mem_union, hX, mem_univ]
    rcases hx with hx | hx
    · obtain ⟨V, hV, hxV, hVU⟩ := (isBasis_countableBasis X1).exists_subset_of_mem_open
        (a := ⟨x, hx⟩) (u := Subtype.val ⁻¹' U) hxU (hU.preimage continuous_subtype_val)
      refine ⟨(↑) '' V, Or.inl ⟨V, hV, rfl⟩, ⟨⟨x, hx⟩, hxV, rfl⟩, ?_⟩
      rintro y ⟨z, hz, rfl⟩
      exact hVU hz
    · obtain ⟨V, hV, hxV, hVU⟩ := (isBasis_countableBasis X2).exists_subset_of_mem_open
        (a := ⟨x, hx⟩) (u := Subtype.val ⁻¹' U) hxU (hU.preimage continuous_subtype_val)
      refine ⟨(↑) '' V, Or.inr ⟨V, hV, rfl⟩, ⟨⟨x, hx⟩, hxV, rfl⟩, ?_⟩
      rintro y ⟨z, hz, rfl⟩
      exact hVU hz
  let P := {p : N × N | ∃ W : Set X, IsOpen W ∧ (p.2.1 : Set X) ⊆ W ∧
    Disjoint (closure W) (p.1.1 : Set X)}
  let W : P → Set X := fun p ↦ Classical.choose p.2
  have hWo (p : P) : IsOpen (W p) := (Classical.choose_spec p.2).1
  have hpW (p : P) : (p.1.2.1 : Set X) ⊆ W p := (Classical.choose_spec p.2).2.1
  have hWd (p : P) : Disjoint (closure (W p)) (p.1.1.1 : Set X) :=
    (Classical.choose_spec p.2).2.2
  let B : Set (Set X) := Set.range fun F : Finset P ↦ (⋃ p ∈ F, closure (W p))ᶜ
  have hPc : Countable P := by
    letI : Countable N := hNc
    infer_instance
  have hBc : B.Countable := by
    letI : Countable P := hPc
    exact Set.countable_range _
  have hBo : ∀ U ∈ B, IsOpen U := by
    rintro U ⟨F, rfl⟩
    exact isClosed_biUnion_finset (fun p _ ↦ isClosed_closure) |>.isOpen_compl
  have hBbasis : IsTopologicalBasis B := isTopologicalBasis_of_isOpen_of_nhds hBo (by
    intro x U hxU hU
    obtain ⟨V, hVo, hxV, hVU⟩ :=
      (isCompact_singleton.exists_isOpen_closure_subset (by simpa using hU.mem_nhds hxU))
    obtain ⟨A, hAN, hxA, hAV⟩ := hN x V (hxV (mem_singleton x)) hVo
    let Q := {p : P | p.1.1.1 = A}
    have hcover : Uᶜ ⊆ ⋃ q : Q, W q.1 := by
      intro y hy
      have hyc : y ∈ (closure V)ᶜ := fun hyV ↦ hy (hVU hyV)
      obtain ⟨O, hOo, hyO, hOc⟩ :=
        isCompact_singleton.exists_isOpen_closure_subset (by
          simpa using (isOpen_compl_iff.mpr isClosed_closure |>.mem_nhds hyc))
      obtain ⟨C, hCN, hyC, hCO⟩ := hN y O (hyO (mem_singleton y)) hOo
      have hd : Disjoint (closure O) A := Set.disjoint_left.2 fun z hzO hzA ↦
        hOc hzO (subset_closure (hAV hzA))
      let p : P := ⟨⟨⟨A, hAN⟩, ⟨C, hCN⟩⟩, ⟨O, hOo, hCO, hd⟩⟩
      let q : Q := ⟨p, rfl⟩
      exact mem_iUnion.2 ⟨q, hpW q.1 hyC⟩
    obtain ⟨G, hG⟩ := (isClosed_compl_iff.mpr hU).isCompact.elim_finite_subcover
      (fun q : Q ↦ W q.1) (fun q ↦ hWo q.1) hcover
    let e : Q ↪ P := ⟨Subtype.val, Subtype.val_injective⟩
    let F : Finset P := G.map e
    refine ⟨(⋃ p ∈ F, closure (W p))ᶜ, ⟨F, rfl⟩, ?_, ?_⟩
    · intro hxF
      simp only [mem_iUnion, exists_prop, mem_compl_iff] at hxF
      rcases hxF with ⟨p, hpF, hxp⟩
      rw [Finset.mem_map] at hpF
      obtain ⟨q, -, rfl⟩ := hpF
      exact Set.disjoint_left.1 (hWd q.1) hxp (q.2 ▸ hxA)
    · apply compl_subset_comm.2
      intro y hy
      have hGy := hG hy
      change y ∈ ⋃ q ∈ G, W q.1 at hGy
      obtain ⟨q, hGy⟩ := Set.mem_iUnion.mp hGy
      obtain ⟨hqG, hyq⟩ := Set.mem_iUnion.mp hGy
      exact mem_iUnion.2 ⟨q.1, mem_iUnion.2 ⟨Finset.mem_map.2 ⟨q, hqG, rfl⟩,
        subset_closure hyq⟩⟩)
  letI : SecondCountableTopology X := hBbasis.secondCountableTopology hBc
  exact inferInstance
