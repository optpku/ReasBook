/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_10.ch2_sec2_10_2_definition_2_48.Flow
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Image

public section

open scoped BigOperators

noncomputable section

universe u v w

/-- The fixed-charge multicommodity network design problem on a directed network with arc-opening
costs, shared capacities, and commodity source-sink demands. -/
structure FixedChargeMulticommodityNetworkDesign
    (N : Type u) (A : Type v) (K : Type w) where
  tail : A → N
  head : A → N
  fixedCost : A → ℝ
  capacity : A → ℝ
  source : K → N
  sink : K → N
  demand : K → ℝ
  fixedCost_nonneg : ∀ a, 0 ≤ fixedCost a
  capacity_nonneg : ∀ a, 0 ≤ capacity a
  demand_nonneg : ∀ k, 0 ≤ demand k

namespace FixedChargeMulticommodityNetworkDesign

variable {N : Type u} {A : Type v} {K : Type w}

/-- Construct a fixed-charge multicommodity network design problem from its endpoint, cost,
capacity, and demand data. -/
def ofNetworkData
    (tail : A → N)
    (head : A → N)
    (fixedCost : A → ℝ)
    (capacity : A → ℝ)
    (source : K → N)
    (sink : K → N)
    (demand : K → ℝ)
    (h_fixedCost_nonneg : ∀ a, 0 ≤ fixedCost a)
    (h_capacity_nonneg : ∀ a, 0 ≤ capacity a)
    (h_demand_nonneg : ∀ k, 0 ≤ demand k) :
    FixedChargeMulticommodityNetworkDesign N A K :=
  { tail := tail
    head := head
    fixedCost := fixedCost
    capacity := capacity
    source := source
    sink := sink
    demand := demand
    fixedCost_nonneg := h_fixedCost_nonneg
    capacity_nonneg := h_capacity_nonneg
    demand_nonneg := h_demand_nonneg }

/-- The right-hand side of the commodity flow-balance equation: demand at the source, negated
demand at the sink, and `0` elsewhere, encoded as source indicator minus sink indicator. -/
def commodityBalanceRhs
    (P : FixedChargeMulticommodityNetworkDesign N A K)
    (k : K) (i : N) : ℝ :=
  let _ : DecidableEq N := Classical.decEq N
  (if i = P.source k then P.demand k else 0) - (if i = P.sink k then P.demand k else 0)

/-- The feasible points `(x, y)` of `P`: binary arc-opening variables `x`, nonnegative commodity
flows `y`, commodity-wise flow-balance equations, and shared arc-capacity inequalities. -/
@[expose]
def feasibleSet
    (P : FixedChargeMulticommodityNetworkDesign N A K)
    [Fintype A] [Fintype K] :
    Set ((A → ℝ) × (K → A → ℝ)) :=
  { xy |
      (∀ k i,
        NetworkFlow.outgoing P.tail (xy.2 k) i - NetworkFlow.incoming P.head (xy.2 k) i =
          P.commodityBalanceRhs k i) ∧
      (∀ a, ∑ k, xy.2 k a ≤ P.capacity a * xy.1 a) ∧
      (∀ k a, 0 ≤ xy.2 k a) ∧
      (∀ a, xy.1 a = 0 ∨ xy.1 a = 1) }

/-- The fixed-charge objective value of a candidate solution `(x, y)`: the sum of arc opening
costs `f_a x_a`. -/
@[expose]
def objectiveValue
    (P : FixedChargeMulticommodityNetworkDesign N A K)
    [Fintype A] :
    ((A → ℝ) × (K → A → ℝ)) → ℝ :=
  fun xy ↦ ∑ a, P.fixedCost a * xy.1 a

/-- Membership in `P.feasibleSet` is exactly the source constraint system: flow balance, shared
capacities, nonnegative commodity flows, and binary arc-opening variables. -/
theorem mem_feasibleSet_iff
    (P : FixedChargeMulticommodityNetworkDesign N A K)
    [Fintype A] [Fintype K]
    (xy : (A → ℝ) × (K → A → ℝ)) :
    xy ∈ P.feasibleSet ↔
      (∀ k i,
        NetworkFlow.outgoing P.tail (xy.2 k) i - NetworkFlow.incoming P.head (xy.2 k) i =
          P.commodityBalanceRhs k i) ∧
      (∀ a, ∑ k, xy.2 k a ≤ P.capacity a * xy.1 a) ∧
      (∀ k a, 0 ≤ xy.2 k a) ∧
      (∀ a, xy.1 a = 0 ∨ xy.1 a = 1) := Iff.rfl

/-- Unfolding equation for the fixed-charge objective of `P`. -/
theorem objectiveValue_def
    (P : FixedChargeMulticommodityNetworkDesign N A K)
    [Fintype A]
    (xy : (A → ℝ) × (K → A → ℝ)) :
    P.objectiveValue xy = ∑ a, P.fixedCost a * xy.1 a := rfl

/-- The objective values attained by feasible solutions of `P`. -/
def objectiveValues
    (P : FixedChargeMulticommodityNetworkDesign N A K)
    [Fintype A] [Fintype K] :
    Set ℝ :=
  P.objectiveValue '' P.feasibleSet

/-- Membership in `P.objectiveValues` means that the value is attained by some feasible pair of
arc-opening and commodity-flow variables. -/
theorem mem_objectiveValues_iff_exists_feasible
    (P : FixedChargeMulticommodityNetworkDesign N A K)
    [Fintype A] [Fintype K]
    (r : ℝ) :
    r ∈ P.objectiveValues ↔
      ∃ xy : (A → ℝ) × (K → A → ℝ), xy ∈ P.feasibleSet ∧ P.objectiveValue xy = r :=
  Iff.rfl

end FixedChargeMulticommodityNetworkDesign
