import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem exercise_3_21
  {X : Type*} [MetricSpace X] [CompleteSpace X]
  (E : ℕ → Set X)
  (hEcl : ∀ n, IsClosed (E n))
  (hEne : ∀ n, (E n).Nonempty)
  (hEbdd : ∀ n, Bornology.IsBounded (E n))
  (hE : ∀ n, E n ⊇ E (n + 1))
  (hE' : Tendsto (λ n => Metric.diam (E n)) atTop (𝓝 0)) :
  ∃ a, Set.iInter E = {a} := sorry
