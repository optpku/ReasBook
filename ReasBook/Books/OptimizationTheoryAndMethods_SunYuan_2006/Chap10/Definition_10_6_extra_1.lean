/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_1_extra_1
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr

noncomputable section

open Filter
open scoped BigOperators

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Domain sampling:
-- * `sunYuanL1Norm` and the notation `‖·‖₁` in `Chapter01.Definition_1_2_1` are the chapter's
--   canonical `ℓ₁` owners on finite coordinate spaces.
-- * `StandardPenaltyProblem` in `Definition_10_1_extra_1` is the chapter's source-facing owner
--   for mixed equality/inequality constrained problems.
-- * `PenaltyFunction` in the same file is the canonical penalty-layer owner above that problem
--   data.
-- * `ConvexOn` remains the core/canonical convex-analysis owner for the new kernel property in
--   this file.
-- This file therefore adds only the Section 10.6 kernel property and exact-penalty constructor,
-- reusing the upstream problem and penalty owners directly.

namespace EuclideanSpace

/-- The Chapter 1 `ℓ^∞` norm transported to the Euclidean-space model
`EuclideanSpace ℝ (Fin m)`. -/
abbrev linftyNorm (c : EuclideanSpace ℝ (Fin m)) : ℝ := ‖c.ofLp‖∞

/-- On `EuclideanSpace ℝ (Fin m)`, the chapter notation `‖c‖∞` is computed by the transported
bridge `c.linftyNorm`. -/
@[simp] theorem linftyNorm_eq (c : EuclideanSpace ℝ (Fin m)) :
    c.linftyNorm = ‖c‖∞ :=
  rfl

/-- The Chapter 1 `ℓ₁` norm transported to the Euclidean-space model `EuclideanSpace ℝ (Fin m)`. -/
abbrev sunYuanL1Norm (c : EuclideanSpace ℝ (Fin m)) : ℝ := ‖c.ofLp‖₁

/-- On `EuclideanSpace ℝ (Fin m)`, the chapter notation `‖c‖₁` is computed by the transported
bridge `c.sunYuanL1Norm`. -/
@[simp] theorem l1Norm_eq (c : EuclideanSpace ℝ (Fin m)) :
    c.sunYuanL1Norm = ‖c‖₁ :=
  rfl

/-- On `ConstraintPoint = ℝ^m`, `‖c‖₁` is the sum of the absolute values of the coordinates. -/
theorem sunYuanL1Norm_eq_sum_abs (c : EuclideanSpace ℝ (Fin m)) :
    ‖c‖₁ = ∑ i, |c i| := by
  simpa using (_root_.l1Norm_eq_sum_abs c.ofLp)

end EuclideanSpace

-- Semantic recall and owner triage:
-- * source-facing layer: the exact-penalty objective `x ↦ f(x) + σ * h(c⁽-⁾(x))` and its
--   penalty-violation sublevel sets;
-- * core/canonical layer: `StandardPenaltyProblem`, `PenaltyFunction`, and mathlib's `ConvexOn`;
-- * bridge/view layer: `PenaltyFunction.nonsmoothExact`, bundling the source objective into the
--   chapter's canonical penalty owner once `σ > 0` supplies the growth axiom.
-- This file therefore keeps `IsStrongDistanceFunction` as the kernel property on
-- `ConstraintPoint → ℝ`, adds the source-facing exact-penalty owner under
-- `StandardPenaltyProblem`, and derives the bundled penalty object from it.

/-- Chapter10 Definition 10.6-extra-1 (1): a function `h : ConstraintPoint → ℝ` is a strong
distance function when it is convex on `ℝ^m`, satisfies `h 0 = 0`, and dominates the `ℓ₁`
norm by a positive constant `δ`, meaning `δ * ‖c‖₁ ≤ h c` for every `c`. -/
@[mk_iff isStrongDistanceFunction_iff]
class IsStrongDistanceFunction (h : ConstraintPoint → ℝ) : Prop where
  convexOn_univ : ConvexOn ℝ Set.univ h
  map_zero : h 0 = 0
  exists_pos_le_mul_l1Norm :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ConstraintPoint, δ * ‖c‖₁ ≤ h c

namespace IsStrongDistanceFunction

/-- A strong distance function vanishes at the origin. This is the callable/simp companion form of
the class field `map_zero`. -/
theorem apply_zero (h : ConstraintPoint → ℝ) [hh : IsStrongDistanceFunction h] :
    h 0 = 0 :=
  hh.map_zero

/-- A strong distance function admits a positive global lower `ℓ₁` bound. This names the source
growth condition in downstream-callable form without choosing a noncanonical witness. -/
theorem exists_pos_mul_l1Norm_le (h : ConstraintPoint → ℝ) [hh : IsStrongDistanceFunction h] :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c : ConstraintPoint, δ * ‖c‖₁ ≤ h c :=
  hh.exists_pos_le_mul_l1Norm

end IsStrongDistanceFunction

/-- Helper for Chapter10 Definition 10.6-extra-1: on `ConstraintPoint = ℝ^m`, the Euclidean norm
is bounded above by the transported `ℓ₁` norm. -/
theorem EuclideanSpace.norm_le_l1Norm (c : ConstraintPoint) :
    ‖c‖ ≤ ‖c‖₁ := by
  -- Compare the squared norms in coordinate form before removing the square root.
  have hsq : ‖c‖ ^ 2 ≤ ‖c‖₁ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.sunYuanL1Norm_eq_sum_abs]
    simpa [pow_two] using
      (Finset.sum_sq_le_sq_sum_of_nonneg
        (s := Finset.univ) (f := fun i : Fin m ↦ |c i|)
        (fun i _ ↦ abs_nonneg (c i)))
  -- The right-hand side is nonnegative, so the squared comparison descends to the norms.
  have hl1_nonneg : 0 ≤ ‖c‖₁ := by
    rw [EuclideanSpace.sunYuanL1Norm_eq_sum_abs]
    exact Finset.sum_nonneg fun i _ ↦ abs_nonneg (c i)
  exact le_of_sq_le_sq hsq hl1_nonneg

/-- Helper for Chapter10 Definition 10.6-extra-1: along cocompact escape in `ConstraintPoint`,
the transported `ℓ₁` norm tends to `+∞`. -/
theorem EuclideanSpace.tendsto_l1Norm_cocompact_atTop :
    Tendsto (fun c : ConstraintPoint ↦ ‖c‖₁) (cocompact ConstraintPoint) atTop := by
  -- Cocompact escape already forces the Euclidean norm to diverge.
  have hnorm :
      Tendsto (fun c : ConstraintPoint ↦ ‖c‖) (cocompact ConstraintPoint) atTop := by
    simpa [dist_eq_norm] using
      (tendsto_dist_right_cocompact_atTop (0 : ConstraintPoint))
  -- Then the pointwise bound `‖c‖ ≤ ‖c‖₁` upgrades the same escape growth to the `ℓ₁` norm.
  exact Filter.tendsto_atTop_mono (fun c ↦ EuclideanSpace.norm_le_l1Norm c) hnorm

/-- A strong distance function is coercive, hence tends to `+∞` along the cocompact filter on
`ℝ^m`. -/
theorem strongDistanceFunction_tendsto_atTop (h : ConstraintPoint → ℝ)
    [hh : IsStrongDistanceFunction h] :
    Tendsto h (cocompact ConstraintPoint) atTop := by
  -- Extract the source lower bound `δ * ‖c‖₁ ≤ h c` from the strong-distance hypothesis.
  obtain ⟨δ, hδ, hbound⟩ := IsStrongDistanceFunction.exists_pos_mul_l1Norm_le h
  -- The `ℓ₁` norm diverges along cocompact escape, and positive scaling preserves `atTop`.
  have hscaled :
      Tendsto (fun c : ConstraintPoint ↦ δ * ‖c‖₁) (cocompact ConstraintPoint) atTop := by
    exact Tendsto.const_mul_atTop hδ EuclideanSpace.tendsto_l1Norm_cocompact_atTop
  -- The pointwise lower bound now transfers the `atTop` growth from `δ * ‖c‖₁` to `h`.
  exact Filter.tendsto_atTop_mono (fun c ↦ hbound c) hscaled

/-- Scaling a strong distance function by a penalty parameter preserves its value at `0`. -/
theorem strongDistanceFunction_smul_zero (h : ConstraintPoint → ℝ)
    [hh : IsStrongDistanceFunction h] (σ : ℝ) :
    (fun c : ConstraintPoint ↦ σ * h c) 0 = 0 := by
  simp [IsStrongDistanceFunction.apply_zero]

/-- Scaling a strong distance function by a positive penalty parameter preserves the
cocompact-to-`atTop` growth needed for a penalty term. -/
theorem strongDistanceFunction_smul_tendsto_atTop
    (h : ConstraintPoint → ℝ) [hh : IsStrongDistanceFunction h] (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun c : ConstraintPoint ↦ σ * h c) (cocompact ConstraintPoint) atTop := by
  -- Positive scaling preserves the coercive `atTop` growth established for `h`.
  exact Tendsto.const_mul_atTop hσ (strongDistanceFunction_tendsto_atTop h)

namespace StandardPenaltyProblem

variable {problem : StandardPenaltyProblem n m}

/-- Chapter10 Definition 10.6-extra-1 (2): the nonsmooth exact penalty objective attached to
`problem`, strong-distance kernel `h`, and penalty parameter `σ` is
`x ↦ problem.objective x + σ * h (c⁽-⁾[problem] x)`. -/
def nonsmoothExactPenalty
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ) (σ : ℝ) :
    Point → ℝ :=
  fun x ↦ problem.objective x + σ * h (c⁽-⁾[problem] x)

/-- Evaluating `problem.nonsmoothExactPenalty h σ` expands to the source exact-penalty
formula `problem.objective x + σ * h (c⁽-⁾[problem] x)`. -/
@[simp] theorem nonsmoothExactPenalty_apply
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ) (σ : ℝ) (x : Point) :
    problem.nonsmoothExactPenalty h σ x =
      problem.objective x + σ * h (c⁽-⁾[problem] x) :=
  rfl

/-- The exact-penalty violation sublevel set with kernel `h` and level `η`. -/
def nonsmoothExactPenaltySublevelSet
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ) (η : ℝ) : Set Point :=
  {x | h (c⁽-⁾[problem] x) ≤ η}

/-- Membership in `problem.nonsmoothExactPenaltySublevelSet h η` is exactly the source
inequality `h (c⁽-⁾[problem] x) ≤ η`. -/
@[simp] theorem mem_nonsmoothExactPenaltySublevelSet
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ) (η : ℝ) (x : Point) :
    x ∈ problem.nonsmoothExactPenaltySublevelSet h η ↔ h (c⁽-⁾[problem] x) ≤ η :=
  Iff.rfl

end StandardPenaltyProblem

namespace PenaltyFunction

variable {problem : StandardPenaltyProblem n m}

/-- Chapter10 Definition 10.6-extra-1 (2): for a strong distance function `h` and a positive
penalty parameter `σ`, the nonsmooth exact penalty function is
`problem.nonsmoothExactPenalty h σ`. -/
def nonsmoothExact
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ)
    [IsStrongDistanceFunction h] (σ : ℝ) (hσ : 0 < σ) :
    PenaltyFunction problem where
  penaltyTerm := fun c ↦ σ * h c
  penaltyTerm_zero := strongDistanceFunction_smul_zero h σ
  penaltyTerm_tendsto_atTop := strongDistanceFunction_smul_tendsto_atTop h σ hσ

/-- Evaluating `PenaltyFunction.nonsmoothExact problem h σ hσ` expands to
`problem.nonsmoothExactPenalty h σ x`. -/
@[simp] theorem nonsmoothExact_apply
    (problem : StandardPenaltyProblem n m) (h : ConstraintPoint → ℝ)
    [IsStrongDistanceFunction h] (σ : ℝ) (hσ : 0 < σ) (x : Point) :
    nonsmoothExact problem h σ hσ x = problem.nonsmoothExactPenalty h σ x :=
  rfl

end PenaltyFunction

#print axioms StandardPenaltyProblem.constraintViolation
#print axioms PenaltyFunction.toFun
#print axioms PenaltyFunction.nonsmoothExact

end
