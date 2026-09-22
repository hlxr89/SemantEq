import Mathlib

open Fintype Subgroup Set Polynomial Ideal
open scoped BigOperators

theorem dummy {G : Type*} [Group G] {H K : Subgroup G} (hHK : H ≤ K) [hKG : K.Normal] [hHKchar : (comap (Subgroup.subtype K) H).Characteristic] : H.Normal := sorry
