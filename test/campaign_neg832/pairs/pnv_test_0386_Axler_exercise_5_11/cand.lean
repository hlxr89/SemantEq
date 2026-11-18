import Mathlib

open Fintype Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem dummy {V : Type*} [AddCommGroup V] [Module.{0} ℂ V] (S T : Module.End ℂ V) : ∀ (v : V), S (T v) = T (S v) := sorry
