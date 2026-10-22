/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Topology.MetricSpace.Holder

open scoped Topology NNReal ENNReal

-- Semantic recall: `HolderOnWith`, `holderOnWith_one`, and
-- `HolderOnWith.continuousOn` are the canonical mathlib Hölder owners for fixed parameters.
-- The textbook definition below is source-facing and existential in those parameters, so it is
-- kept as a thin bridge on top of that owner. The local-at-a-point notion is also phrased through
-- `HolderOnWith` on a neighborhood within the set, rather than re-stating the same inequality
-- entrywise.

variable {X Y : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y]

/-- Chapter01 Definition 1.2.20 (1): in the textbook special case `F : D ⊆ ℝⁿ → ℝᵐ`,
`F` is Hölder continuous on `D` if there exist `γ ≥ 0` and `p ∈ (0, 1]` such that `F`
is `(γ, p)`-Hölder on `D`. The formalization is stated for arbitrary pseudoemetric spaces,
since only the metric structure is used. -/
class HolderContinuousOn (D : Set X) (F : X → Y) : Prop where
  /-- There exist Hölder parameters witnessing that `F` is Hölder on `D`. -/
  exists_holderOnWith :
    ∃ γ : ℝ≥0, ∃ p : ℝ≥0, p ∈ Set.Ioc (0 : ℝ≥0) 1 ∧ HolderOnWith γ p F D

/-- Hölder continuity on a set is classically decidable. -/
noncomputable instance instDecidableHolderContinuousOn (D : Set X) (F : X → Y) :
    Decidable (HolderContinuousOn D F) :=
  Classical.propDecidable _

/-- Unfolding formula for `HolderContinuousOn`. -/
theorem holderContinuousOn_iff {D : Set X} {F : X → Y} :
    HolderContinuousOn D F ↔
      ∃ γ : ℝ≥0, ∃ p : ℝ≥0, p ∈ Set.Ioc (0 : ℝ≥0) 1 ∧ HolderOnWith γ p F D := by
  constructor
  · intro hF
    exact hF.exists_holderOnWith
  · intro hF
    exact ⟨hF⟩

/-- A Lipschitz map on `D` is Hölder continuous on `D` with exponent `1`. -/
theorem LipschitzOnWith.holderContinuousOn {D : Set X} {F : X → Y} {γ : ℝ≥0}
    (hF : LipschitzOnWith γ F D) :
    HolderContinuousOn D F := by
  refine ⟨γ, 1, ?_, hF.holderOnWith⟩
  simp [Set.mem_Ioc]

/-- Hölder continuity on `D` implies continuity on `D`. -/
theorem HolderContinuousOn.continuousOn {D : Set X} {F : X → Y} (hF : HolderContinuousOn D F) :
    ContinuousOn F D := by
  rcases hF.exists_holderOnWith with ⟨γ, p, hp, hholder⟩
  exact hholder.continuousOn hp.1

/- When `p = 1`, the Hölder condition is exactly the usual `γ`-Lipschitz condition on `D`; this
is the existing mathlib theorem `holderOnWith_one`. -/
#check holderOnWith_one

/-- Chapter01 Definition 1.2.20 (2): in the textbook special case `F : D ⊆ ℝⁿ → ℝᵐ`,
`F` is Hölder continuous at `x ∈ D` if there exist `γ ≥ 0`, `p ∈ (0, 1]`, and a neighborhood of
`x` within `D` on which `F` is `(γ, p)`-Hölder. The formalization is stated for arbitrary
pseudoemetric spaces, since only the metric structure is used. -/
class HolderContinuousWithinAt (D : Set X) (F : X → Y) (x : X) : Prop where
  /-- Local Hölder continuity within `D` is a property at a point of `D`. -/
  mem : x ∈ D
  /-- There exist Hölder parameters and a neighborhood within `D` on which `F` is Hölder. -/
  exists_holderOnWith :
    ∃ γ : ℝ≥0, ∃ p : ℝ≥0, p ∈ Set.Ioc (0 : ℝ≥0) 1 ∧
      ∃ s : Set X, s ∈ 𝓝[D] x ∧ HolderOnWith γ p F s

/-- Hölder continuity within a set at a point is classically decidable. -/
noncomputable instance instDecidableHolderContinuousWithinAt
    (D : Set X) (F : X → Y) (x : X) :
    Decidable (HolderContinuousWithinAt D F x) :=
  Classical.propDecidable _

/-- Unfolding formula for `HolderContinuousWithinAt`. -/
theorem holderContinuousWithinAt_iff {D : Set X} {F : X → Y} {x : X} :
    HolderContinuousWithinAt D F x ↔
      x ∈ D ∧
        ∃ γ : ℝ≥0, ∃ p : ℝ≥0, p ∈ Set.Ioc (0 : ℝ≥0) 1 ∧
          ∃ s : Set X, s ∈ 𝓝[D] x ∧ HolderOnWith γ p F s := by
  constructor
  · intro hF
    exact ⟨hF.mem, hF.exists_holderOnWith⟩
  · rintro ⟨hx, hF⟩
    exact ⟨hx, hF⟩

/-- Hölder continuity within `D` at `x` implies continuity within `D` at `x`. -/
theorem HolderContinuousWithinAt.continuousWithinAt
    {D : Set X} {F : X → Y} {x : X} (hF : HolderContinuousWithinAt D F x) :
    ContinuousWithinAt F D x := by
  rcases hF.exists_holderOnWith with ⟨γ, p, hp, s, hs, hholder⟩
  have hxs : x ∈ s := mem_of_mem_nhdsWithin hF.mem hs
  exact ((hholder.continuousOn hp.1) x hxs).mono_of_mem_nhdsWithin hs

/-- A Hölder continuous map on `D` is Hölder continuous within `D` at each point of `D`. -/
theorem HolderContinuousOn.holderContinuousWithinAt
    {D : Set X} {F : X → Y} {x : X} (hF : HolderContinuousOn D F) (hx : x ∈ D) :
    HolderContinuousWithinAt D F x := by
  rcases hF.exists_holderOnWith with ⟨γ, p, hp, hholder⟩
  exact ⟨hx, ⟨γ, p, hp, D, self_mem_nhdsWithin, hholder⟩⟩
