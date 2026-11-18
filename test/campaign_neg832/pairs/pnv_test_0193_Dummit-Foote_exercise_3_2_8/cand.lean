import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ⊓ K = ⊥) : Subgroup.comap ((H ⊔ K).subtype : (H ⊔ K : Subgroup G) →* G) H = ⊥ := sorry
