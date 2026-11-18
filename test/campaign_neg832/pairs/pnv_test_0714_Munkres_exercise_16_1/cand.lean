import Mathlib

open Filter Set TopologicalSpace
open scoped Topology

theorem dummy {X Y : Type*} (f : Y → X) (hf : Function.Injective f) (Y_top : TopologicalSpace Y) : @TopologicalSpace.induced Y X f (@TopologicalSpace.coinduced Y X f Y_top) ≤ Y_top := sorry
