/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Module.Basic

section Chapter08Definition821

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

-- Semantic recall hits verified for this item: mathlib's canonical infinitesimal-set owner is
-- `tangentConeAt`, and `mem_tangentConeAt_of_segment_subset` shows the expected bridge from small
-- feasible segments. This source item is kept as the faithful ray-based predicate and its
-- associated set of directions.

/-- Chapter08 Definition 8.2.1 (1): a vector `d` is a feasible direction of `X` at `xStar` when
`d ≠ 0` and there exists `δ > 0` such that `xStar + t • d ∈ X` for every `t ∈ Set.Icc (0 : ℝ) δ`.
The source-side condition `xStar ∈ X` is then automatic by taking `t = 0`. -/
class IsFeasibleDirectionAt (X : Set E) (xStar d : E) : Prop where
  ne : d ≠ 0
  small_segment_mem : ∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) δ, xStar + t • d ∈ X

/-- Unfolding formula for `IsFeasibleDirectionAt`. -/
theorem isFeasibleDirectionAt_iff
    (X : Set E) (xStar d : E) :
    IsFeasibleDirectionAt X xStar d ↔
      d ≠ 0 ∧
        ∃ δ > 0, ∀ t ∈ Set.Icc (0 : ℝ) δ, xStar + t • d ∈ X := by
  constructor
  · intro h
    exact ⟨h.ne, h.small_segment_mem⟩
  · rintro ⟨hne, hsmall_segment_mem⟩
    exact ⟨hne, hsmall_segment_mem⟩

/-- A feasible direction is based at a feasible point. -/
theorem IsFeasibleDirectionAt.mem
    {X : Set E} {xStar d : E}
    (h : IsFeasibleDirectionAt X xStar d) :
    xStar ∈ X :=
  let ⟨δ, hδ, hsmall_segment_mem⟩ := h.small_segment_mem
  by simpa using hsmall_segment_mem 0 ⟨le_rfl, hδ.le⟩

/-- A feasible direction stays in `X` for all sufficiently small nonnegative parameters. -/
theorem IsFeasibleDirectionAt.eventually_mem_nhdsWithin
    {X : Set E} {xStar d : E}
    (h : IsFeasibleDirectionAt X xStar d) :
    ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ici 0), xStar + t • d ∈ X := by
  rcases h.small_segment_mem with ⟨δ, hδ, hsmall_segment_mem⟩
  -- The witness interval `[0, δ]` is a right-neighborhood of `0` inside `Set.Ici 0`.
  filter_upwards [Icc_mem_nhdsGE hδ] with t ht
  -- Every point of that interval satisfies the source feasible-ray condition.
  exact hsmall_segment_mem t ht

/-- Chapter08 Definition 8.2.1 (2): `feasibleDirections xStar X` is the set of all feasible
directions of `X` at `xStar`. -/
def feasibleDirections (xStar : E) (X : Set E) : Set E :=
  { d | IsFeasibleDirectionAt X xStar d }

/-- Membership in `feasibleDirections xStar X` is exactly the feasible-direction predicate. -/
theorem mem_feasibleDirections_iff
    (xStar d : E) (X : Set E) :
    d ∈ feasibleDirections xStar X ↔ IsFeasibleDirectionAt X xStar d :=
  Iff.rfl

variable [TopologicalSpace E] [ContinuousSMul ℝ E]

/-- Every source-facing feasible direction is a direction in the canonical tangent cone. -/
theorem IsFeasibleDirectionAt.mem_tangentConeAt
    {X : Set E} {xStar d : E}
    (h : IsFeasibleDirectionAt X xStar d) :
    d ∈ tangentConeAt ℝ X xStar := by
  -- Use the source feasible ray with positive parameters to match the tangent-cone API.
  refine mem_tangentConeAt_of_add_smul_mem (Filter.tendsto_id'.2 <| nhdsGT_le_nhdsNE 0) ?_
  -- Restrict the nonnegative-neighborhood statement to the punctured right neighborhood.
  exact h.eventually_mem_nhdsWithin.filter_mono (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)

/-- The source-facing feasible-direction set is contained in the canonical tangent cone. -/
theorem feasibleDirections_subset_tangentConeAt
    (xStar : E) (X : Set E) :
    feasibleDirections xStar X ⊆ tangentConeAt ℝ X xStar := by
  intro d hd
  exact (mem_feasibleDirections_iff xStar d X).mp hd |>.mem_tangentConeAt

end Chapter08Definition821
