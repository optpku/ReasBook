/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Text_6_1_4_2_Population_Interpretation

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u v

variable {ι : Type u}

/- Definition 6.16 lies in the continuous-location smoothing domain.

Sampled owner-style declarations:
- `ContinuousLocationWeights`, `continuousLocationDualAdmissibleSet`,
  `continuousLocationDualTupleNorm`, and `continuousLocationDualProxFunction` in
  `Text_6_1_4_2_Population_Interpretation`, the chapter owners of the weights, dual feasible set,
  weighted tuple geometry, and prox-function;
- `smoothedPrimalObjectiveMaximand` and `smoothedPrimalObjective` in `Definition_6_30`, the
  chapter's canonical regularized-max owners;
- `continuousLocationSmoothingMap` in `Proposition_6_17`, the later source-facing bridge that
  rewrites the same tuple geometry through the chapter's smoothing-map owner.

Best owner abstraction:
- source-facing: the continuous-location smoothing specialization and its Huber-sum formula;
- core/canonical: `smoothedPrimalObjectiveMaximand` and `smoothedPrimalObjective`;
- bridge/view: the continuous-location specialization data fed into those owners.

Primitive data:
- the finite population index type `ι`;
- the population weights `weights`;
- the centers `c_j`.

Derived API:
- the dual feasible set `Q₂`;
- the weighted tuple norm and prox-function `d₂`;
- the continuous-location specialization of the regularized maximand and its smoothed supremum;
- the scalar Huber companion description.

Source/core/bridge triage:
- source-facing: `continuousLocationSmoothApproximation` and the Huber-sum companion theorem;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: `continuousLocationSmoothingMap`, together with the internal weighted
  center-penalty term fed to `smoothedPrimalObjective`.

The previous version rebuilt a second public maximand/supremum owner specialized to
`EuclideanSpace ℝ (Fin n)` and `Fin p`. This refinement reuses the chapter's canonical
regularized-max owner directly, keeps the Huber expansion as the real source-facing companion, and
lowers the public ambient data to an arbitrary finite index family in a real inner-product space.
-/

section Geometry

variable {E : Type v} [NormedAddCommGroup E]

-- Proof sketch: unfold `continuousLocationDualAdmissibleSet`; membership is exactly the defining
-- coordinatewise unit-ball condition on the tuple `u`.
/-- A tuple belongs to `Q₂` exactly when each coordinate has norm at most `1`. -/
theorem mem_continuousLocationDualAdmissibleSet_iff (u : ι → E) :
    u ∈ continuousLocationDualAdmissibleSet E ↔ ∀ j, ‖u j‖ ≤ 1 :=
by
  -- The owner is definitionally the coordinatewise unit ball.
  rfl

variable [Fintype ι]

-- Proof sketch: unfold `continuousLocationDualTupleNorm`.
/-- Evaluating the weighted dual tuple norm expands to the formula
`(∑_j m_j ‖u_j‖²)^(1/2)`. -/
theorem continuousLocationDualTupleNorm_def
    (weights : ContinuousLocationWeights ι) (u : ι → E) :
    continuousLocationDualTupleNorm E weights u =
      Real.sqrt (∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ)) :=
by
  -- The tuple norm already uses the displayed weighted square-sum formula.
  rfl

-- Proof sketch: unfold `continuousLocationDualProxFunction`; the right-hand side is exactly the
-- defining quadratic expression in `continuousLocationDualTupleNorm`.
/-- Expanding `continuousLocationDualProxFunction` recovers the quadratic formula
`d₂(u) = (1 / 2) ‖u‖²`. -/
theorem continuousLocationDualProxFunction_def
    (weights : ContinuousLocationWeights ι) (u : ι → E) :
    continuousLocationDualProxFunction E weights u =
      (1 / 2 : ℝ) * (continuousLocationDualTupleNorm E weights u) ^ (2 : ℕ) :=
by
  -- The prox-function is defined by the quadratic expression in the tuple norm.
  rfl

end Geometry

section Huber

/-- The scalar Huber regularization term `ψ_μ(τ)` for a positive smoothing parameter `μ`,
defined as the supremum of `γ ↦ γ τ - (μ / 2) γ²` on the interval `[0, 1]`. -/
def continuousLocationHuberLoss (μ : {μ : ℝ // 0 < μ}) : ℝ → ℝ :=
  fun τ ↦
    sSup ((fun γ : ℝ ↦ γ * τ - ((μ : ℝ) / 2 : ℝ) * γ ^ (2 : ℕ)) '' Set.Icc (0 : ℝ) 1)

-- Proof sketch: unfold `continuousLocationHuberLoss`; the displayed supremum over `Set.Icc 0 1`
-- is exactly the defining scalar maximization problem.
/-- Evaluating the scalar Huber loss recovers the regularized maximization over `γ ∈ [0, 1]`. -/
theorem continuousLocationHuberLoss_def
    (μ : {μ : ℝ // 0 < μ}) (τ : ℝ) :
    continuousLocationHuberLoss μ τ =
      sSup ((fun γ : ℝ ↦ γ * τ - (((μ : ℝ) / 2 : ℝ) * γ ^ (2 : ℕ))) '' Set.Icc (0 : ℝ) 1) :=
by
  -- This is the defining supremum formula.
  rfl

/-- Helper for Definition 6.16: the scalar maximand rewrites into a completed-square normal
form. -/
private theorem continuousLocationHuberQuadratic_eq_completedSquare
    (μ : {μ : ℝ // 0 < μ}) (τ γ : ℝ) :
    γ * τ - (((μ : ℝ) / 2 : ℝ) * γ ^ (2 : ℕ)) =
      τ ^ (2 : ℕ) / (2 * (μ : ℝ)) -
        (((μ : ℝ) / 2 : ℝ) * (γ - τ / (μ : ℝ)) ^ (2 : ℕ)) := by
  have hμne : (μ : ℝ) ≠ 0 := ne_of_gt μ.2
  field_simp [hμne]
  ring

-- Proof sketch: maximize the concave quadratic `γ ↦ γ τ - (μ / 2) γ²` on `[0, 1]`; the critical
-- point is `γ = τ / μ`, which lies in `[0, 1]` exactly when `τ ≤ μ`, yielding the two branches.
/-- For `μ > 0` and `τ ≥ 0`, the scalar Huber loss is the usual quadratic-linear piecewise
function. -/
theorem continuousLocationHuberLoss_eq_piecewise
    (μ : {μ : ℝ // 0 < μ}) {τ : ℝ} (hτ : 0 ≤ τ) :
    continuousLocationHuberLoss μ τ =
      if τ ≤ (μ : ℝ) then τ ^ (2 : ℕ) / (2 * (μ : ℝ)) else τ - (μ : ℝ) / 2 := by
  let s : Set ℝ :=
    (fun γ : ℝ ↦ γ * τ - (((μ : ℝ) / 2 : ℝ) * γ ^ (2 : ℕ))) '' Set.Icc (0 : ℝ) 1
  have hs_nonempty : s.Nonempty := by
    -- The interval contains `0`, so the image set is nonempty.
    refine ⟨(fun γ : ℝ ↦ γ * τ - (((μ : ℝ) / 2 : ℝ) * γ ^ (2 : ℕ))) 0, ?_⟩
    exact ⟨0, by simp, rfl⟩
  rw [continuousLocationHuberLoss_def]
  change sSup s = if τ ≤ (μ : ℝ) then τ ^ (2 : ℕ) / (2 * (μ : ℝ)) else τ - (μ : ℝ) / 2
  by_cases hτμ : τ ≤ (μ : ℝ)
  · rw [if_pos hτμ]
    have hs_upper : ∀ y ∈ s, y ≤ τ ^ (2 : ℕ) / (2 * (μ : ℝ)) := by
      intro y hy
      rcases hy with ⟨γ, hγ, rfl⟩
      -- The completed-square form is maximized when the square term vanishes.
      calc
        (fun γ : ℝ ↦ γ * τ - (((μ : ℝ) / 2 : ℝ) * γ ^ (2 : ℕ))) γ
            = τ ^ (2 : ℕ) / (2 * (μ : ℝ)) -
                (((μ : ℝ) / 2 : ℝ) * (γ - τ / (μ : ℝ)) ^ (2 : ℕ)) := by
                  simpa using continuousLocationHuberQuadratic_eq_completedSquare μ τ γ
        _ ≤ τ ^ (2 : ℕ) / (2 * (μ : ℝ)) := by
              nlinarith [sq_nonneg (γ - τ / (μ : ℝ)), μ.2]
    have hs_bdd : BddAbove s := ⟨τ ^ (2 : ℕ) / (2 * (μ : ℝ)), hs_upper⟩
    have hopt_mem :
        τ ^ (2 : ℕ) / (2 * (μ : ℝ)) ∈ s := by
      -- In the quadratic branch the critical point `γ = τ / μ` lies inside `[0, 1]`.
      refine ⟨τ / (μ : ℝ), ?_, ?_⟩
      constructor
      · exact div_nonneg hτ (le_of_lt μ.2)
      · exact (_root_.div_le_iff₀ μ.2).2 (by simpa using hτμ)
      calc
        (fun γ : ℝ ↦ γ * τ - (((μ : ℝ) / 2 : ℝ) * γ ^ (2 : ℕ))) (τ / (μ : ℝ))
            = τ ^ (2 : ℕ) / (2 * (μ : ℝ)) -
                (((μ : ℝ) / 2 : ℝ) * ((τ / (μ : ℝ)) - τ / (μ : ℝ)) ^ (2 : ℕ)) := by
                  simpa using continuousLocationHuberQuadratic_eq_completedSquare μ τ (τ / (μ : ℝ))
        _ = τ ^ (2 : ℕ) / (2 * (μ : ℝ)) := by simp
    refine le_antisymm ?_ ?_
    · exact csSup_le hs_nonempty hs_upper
    · exact le_csSup_of_le hs_bdd hopt_mem le_rfl
  · rw [if_neg hτμ]
    have hμ_le_τ : (μ : ℝ) ≤ τ := le_of_lt (lt_of_not_ge hτμ)
    have hs_upper : ∀ y ∈ s, y ≤ τ - (μ : ℝ) / 2 := by
      intro y hy
      rcases hy with ⟨γ, hγ, rfl⟩
      have hcritical_ge_one : 1 ≤ τ / (μ : ℝ) := by
        exact (one_le_div μ.2).2 hμ_le_τ
      have hsq_compare :
          (1 - τ / (μ : ℝ)) ^ (2 : ℕ) ≤ (γ - τ / (μ : ℝ)) ^ (2 : ℕ) := by
        let a : ℝ := τ / (μ : ℝ)
        have hleft_nonneg : 0 ≤ a - 1 := by
          linarith
        have hright_nonneg : 0 ≤ a - γ := by
          linarith [hcritical_ge_one, hγ.2]
        have hmono : a - 1 ≤ a - γ := by
          linarith [hγ.2]
        have hsquare : (a - 1) ^ (2 : ℕ) ≤ (a - γ) ^ (2 : ℕ) := by
          nlinarith
        have hleft : (1 - a) ^ (2 : ℕ) = (a - 1) ^ (2 : ℕ) := by
          ring
        have hright : (γ - a) ^ (2 : ℕ) = (a - γ) ^ (2 : ℕ) := by
          ring
        simpa [a, hleft, hright] using hsquare
      have hone_value :
          τ ^ (2 : ℕ) / (2 * (μ : ℝ)) -
              (((μ : ℝ) / 2 : ℝ) * (1 - τ / (μ : ℝ)) ^ (2 : ℕ)) =
            τ - (μ : ℝ) / 2 := by
        simpa using (continuousLocationHuberQuadratic_eq_completedSquare μ τ 1).symm
      -- When `τ / μ ≥ 1`, the closest point of `[0, 1]` to the critical point is `γ = 1`.
      calc
        γ * τ - (((μ : ℝ) / 2 : ℝ) * γ ^ (2 : ℕ))
            = τ ^ (2 : ℕ) / (2 * (μ : ℝ)) -
                (((μ : ℝ) / 2 : ℝ) * (γ - τ / (μ : ℝ)) ^ (2 : ℕ)) := by
                  simpa using continuousLocationHuberQuadratic_eq_completedSquare μ τ γ
        _ ≤ τ ^ (2 : ℕ) / (2 * (μ : ℝ)) -
              (((μ : ℝ) / 2 : ℝ) * (1 - τ / (μ : ℝ)) ^ (2 : ℕ)) := by
              nlinarith [hsq_compare, μ.2]
        _ = τ - (μ : ℝ) / 2 := hone_value
    have hs_bdd : BddAbove s := ⟨τ - (μ : ℝ) / 2, hs_upper⟩
    have hone_mem : τ - (μ : ℝ) / 2 ∈ s := by
      -- In the linear branch the endpoint `γ = 1` attains the supremum.
      refine ⟨1, by simp, ?_⟩
      ring
    refine le_antisymm ?_ ?_
    · exact csSup_le hs_nonempty hs_upper
    · exact le_csSup_of_le hs_bdd hone_mem le_rfl

end Huber

section Smoothing

variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The `j`-th coordinate contribution to the continuous-location smoothing operator. -/
private def continuousLocationCoordinateMap (E : Type v) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (j : ι) :
    E →L[ℝ] StrongDual ℝ (ι → E) :=
  ((ContinuousLinearMap.proj j : (ι → E) →L[ℝ] E).precomp ℝ).comp (innerSL ℝ)

/-- The `j`-th coordinate contribution evaluates to the pairing `u ↦ ⟪u_j, x⟫`. -/
-- Proof sketch: unfold `continuousLocationCoordinateMap`; evaluation reduces to the `j`-th
-- projection followed by the real inner-product functional.
private theorem continuousLocationCoordinateMap_apply
    (j : ι) (x : E) (u : ι → E) :
    continuousLocationCoordinateMap E j x u = inner ℝ (u j) x :=
by
  -- Unfold the coordinate map and evaluate the projection followed by `innerSL`.
  simp [continuousLocationCoordinateMap, real_inner_comm]

variable [Fintype ι]

/-- The continuous-location specialization of the generic smoothing operator
`x ↦ (u ↦ ∑_j m_j ⟪u_j, x⟫)`. -/
def continuousLocationSmoothingMap (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weights : ContinuousLocationWeights ι) :
    E →L[ℝ] StrongDual ℝ (ι → E) :=
  ∑ j, (weights j : ℝ) • continuousLocationCoordinateMap E j

-- Proof sketch: expand the finite weighted sum of the coordinate dual functionals.
/-- The continuous-location smoothing operator acts by the weighted pairing
`u ↦ ∑_j m_j ⟪u_j, x⟫`. -/
theorem continuousLocationSmoothingMap_apply
    (weights : ContinuousLocationWeights ι) (x : E) (u : ι → E) :
    continuousLocationSmoothingMap E weights x u =
      ∑ j, (weights j : ℝ) * inner ℝ (u j) x :=
by
  -- Evaluate the finite weighted sum of coordinate functionals coordinatewise.
  simp [continuousLocationSmoothingMap, continuousLocationCoordinateMap_apply]

-- Internal helper for the center-dependent dual penalty
-- `u ↦ ∑_j m_j ⟪u_j, c_j⟫` used by the continuous-location specialization.
/-- The weighted center-evaluation term
`u ↦ ∑_j m_j ⟪u_j, c_j⟫` appearing in the continuous-location specialization. -/
private def continuousLocationCenterPenalty
    (weights : ContinuousLocationWeights ι) (centers : ι → E) : (ι → E) → ℝ :=
  fun u ↦ ∑ j, (weights j : ℝ) * inner ℝ (u j) (centers j)

-- Proof sketch: unfold the generic owner, evaluate `continuousLocationSmoothingMap`, and combine
-- the two weighted pairing sums into the pairing with `x - c_j`.
/-- Evaluating the chapter-owner maximand in the continuous-location specialization recovers the
displayed weighted-pairing formula `u ↦ ∑_j m_j ⟪u_j, x - c_j⟫ - μ d₂(u)`. -/
theorem smoothedPrimalObjectiveMaximand_continuousLocation_apply
    (weights : ContinuousLocationWeights ι) (centers : ι → E)
    (μ : {μ : ℝ // 0 < μ}) (x : E) (u : ι → E) :
    smoothedPrimalObjectiveMaximand
        (continuousLocationSmoothingMap E weights)
        (continuousLocationCenterPenalty weights centers)
        (continuousLocationDualProxFunction E weights)
        (μ : ℝ) x u =
      (∑ j, (weights j : ℝ) * inner ℝ (u j) (x - centers j)) -
        (μ : ℝ) * continuousLocationDualProxFunction E weights u :=
by
  -- Expand the owner maximand into the smoothing term, center term, and prox penalty.
  calc
    smoothedPrimalObjectiveMaximand
        (continuousLocationSmoothingMap E weights)
        (continuousLocationCenterPenalty weights centers)
        (continuousLocationDualProxFunction E weights)
        (μ : ℝ) x u =
      (∑ j, (weights j : ℝ) * inner ℝ (u j) x) -
        (∑ j, (weights j : ℝ) * inner ℝ (u j) (centers j)) -
        (μ : ℝ) * continuousLocationDualProxFunction E weights u := by
          simp [smoothedPrimalObjectiveMaximand, continuousLocationSmoothingMap_apply,
            continuousLocationCenterPenalty]
    _ =
      (∑ j, (weights j : ℝ) * inner ℝ (u j) (x - centers j)) -
        (μ : ℝ) * continuousLocationDualProxFunction E weights u := by
          have hsum :
              ∑ j, (weights j : ℝ) * inner ℝ (u j) (x - centers j) =
                ∑ j, (weights j : ℝ) * inner ℝ (u j) x -
                  ∑ j, (weights j : ℝ) * inner ℝ (u j) (centers j) := by
            calc
              ∑ j, (weights j : ℝ) * inner ℝ (u j) (x - centers j)
                  = ∑ j, ((weights j : ℝ) * inner ℝ (u j) x -
                      (weights j : ℝ) * inner ℝ (u j) (centers j)) := by
                        refine Finset.sum_congr rfl ?_
                        intro j hj
                        rw [inner_sub_right]
                        ring
              _ = ∑ j, (weights j : ℝ) * inner ℝ (u j) x -
                    ∑ j, (weights j : ℝ) * inner ℝ (u j) (centers j) := by
                      rw [Finset.sum_sub_distrib]
          rw [← hsum]

/-- The Definition 6.16 smooth approximation `f_μ` for the continuous
location objective is the continuous-location specialization of the chapter owner
`smoothedPrimalObjective`, with dual feasible set `Q₂`, weighted quadratic prox-function
`d₂(u) = (1 / 2) ‖u‖²`, and center term `u ↦ ∑_j m_j ⟪u_j, c_j⟫`; the accompanying Huber-loss
description is recorded in the companion declarations below. -/
abbrev continuousLocationSmoothApproximation
    (weights : ContinuousLocationWeights ι) (centers : ι → E)
    (μ : {μ : ℝ // 0 < μ}) : E → ℝ :=
  smoothedPrimalObjective
    (continuousLocationSmoothingMap E weights)
    (continuousLocationDualAdmissibleSet E)
    0
    (continuousLocationCenterPenalty weights centers)
    (continuousLocationDualProxFunction E weights)
    (μ : ℝ)

-- Proof sketch: apply `smoothedPrimalObjective_apply` to the continuous-location specialization of
-- the generic smoothing owner.
/-- Evaluating the smooth approximation recovers the defining supremum over the dual set `Q₂`. -/
theorem continuousLocationSmoothApproximation_apply
    (weights : ContinuousLocationWeights ι) (centers : ι → E)
    (μ : {μ : ℝ // 0 < μ}) (x : E) :
    continuousLocationSmoothApproximation weights centers μ x =
      sSup
        (smoothedPrimalObjectiveMaximand
            (continuousLocationSmoothingMap E weights)
            (continuousLocationCenterPenalty weights centers)
            (continuousLocationDualProxFunction E weights)
            (μ : ℝ) x ''
          continuousLocationDualAdmissibleSet E) :=
by
  -- The continuous-location objective is the chapter owner with zero base term.
  rw [continuousLocationSmoothApproximation, smoothedPrimalObjective_apply]
  simp

/-- Helper for Definition 6.16: after expanding the prox term, the continuous-location maximand
separates into a weighted sum of coordinate contributions. -/
private theorem smoothedPrimalObjectiveMaximand_continuousLocation_eq_coordinateSum
    (weights : ContinuousLocationWeights ι) (centers : ι → E)
    (μ : {μ : ℝ // 0 < μ}) (x : E) (u : ι → E) :
    smoothedPrimalObjectiveMaximand
        (continuousLocationSmoothingMap E weights)
        (continuousLocationCenterPenalty weights centers)
        (continuousLocationDualProxFunction E weights)
        (μ : ℝ) x u =
      ∑ j, (weights j : ℝ) *
        (inner ℝ (u j) (x - centers j) - ((μ : ℝ) / 2) * ‖u j‖ ^ (2 : ℕ)) := by
  -- Rewrite the owner maximand and distribute the scalar prox penalty across the sum.
  rw [smoothedPrimalObjectiveMaximand_continuousLocation_apply,
    continuousLocationDualProxFunction_eq_half_weighted_sum_sq_norm]
  have hpenalty :
      (μ : ℝ) * ((1 / 2 : ℝ) * ∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ)) =
        ∑ j, (μ : ℝ) * ((1 / 2 : ℝ) * ((weights j : ℝ) * ‖u j‖ ^ (2 : ℕ))) := by
    calc
      (μ : ℝ) * ((1 / 2 : ℝ) * ∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ))
          = (((μ : ℝ) * (1 / 2 : ℝ)) * ∑ j, (weights j : ℝ) * ‖u j‖ ^ (2 : ℕ)) := by
              ring
      _ = ∑ j, (((μ : ℝ) * (1 / 2 : ℝ)) * ((weights j : ℝ) * ‖u j‖ ^ (2 : ℕ))) := by
            rw [Finset.mul_sum]
      _ = ∑ j, (μ : ℝ) * ((1 / 2 : ℝ) * ((weights j : ℝ) * ‖u j‖ ^ (2 : ℕ))) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            ring
  rw [hpenalty]
  calc
    ∑ j, (weights j : ℝ) * inner ℝ (u j) (x - centers j) -
        ∑ j, (μ : ℝ) * ((1 / 2 : ℝ) * ((weights j : ℝ) * ‖u j‖ ^ (2 : ℕ))) =
      ∑ j, ((weights j : ℝ) * inner ℝ (u j) (x - centers j) -
        (μ : ℝ) * ((1 / 2 : ℝ) * ((weights j : ℝ) * ‖u j‖ ^ (2 : ℕ))) ) := by
          rw [Finset.sum_sub_distrib]
    _ = ∑ j, (weights j : ℝ) *
        (inner ℝ (u j) (x - centers j) - ((μ : ℝ) / 2) * ‖u j‖ ^ (2 : ℕ)) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring

/-- Helper for Definition 6.16: every admissible coordinate contribution is bounded above by the
scalar Huber loss at the corresponding distance. -/
private theorem continuousLocationCoordinateContribution_le_huberLoss
    (μ : {μ : ℝ // 0 < μ}) (z u : E) (hu : ‖u‖ ≤ 1) :
    inner ℝ u z - ((μ : ℝ) / 2) * ‖u‖ ^ (2 : ℕ) ≤
      continuousLocationHuberLoss μ ‖z‖ := by
  have hinner : inner ℝ u z ≤ ‖u‖ * ‖z‖ := real_inner_le_norm _ _
  have hu_nonneg : 0 ≤ ‖u‖ := norm_nonneg u
  have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  rw [continuousLocationHuberLoss_eq_piecewise μ hz_nonneg]
  by_cases hzμ : ‖z‖ ≤ (μ : ℝ)
  · rw [if_pos hzμ]
    -- In the quadratic branch the completed-square upper bound controls every `γ ∈ [0, 1]`.
    have hnorm_bound :
        inner ℝ u z - ((μ : ℝ) / 2) * ‖u‖ ^ (2 : ℕ) ≤
          ‖u‖ * ‖z‖ - ((μ : ℝ) / 2) * ‖u‖ ^ (2 : ℕ) :=
      sub_le_sub_right hinner _
    have hquad_bound :
        ‖u‖ * ‖z‖ - ((μ : ℝ) / 2) * ‖u‖ ^ (2 : ℕ) ≤
          ‖z‖ ^ (2 : ℕ) / (2 * (μ : ℝ)) := by
      calc
        ‖u‖ * ‖z‖ - ((μ : ℝ) / 2) * ‖u‖ ^ (2 : ℕ)
            = ‖z‖ ^ (2 : ℕ) / (2 * (μ : ℝ)) -
                (((μ : ℝ) / 2 : ℝ) * (‖u‖ - ‖z‖ / (μ : ℝ)) ^ (2 : ℕ)) := by
                  simpa using continuousLocationHuberQuadratic_eq_completedSquare μ ‖z‖ ‖u‖
        _ ≤ ‖z‖ ^ (2 : ℕ) / (2 * (μ : ℝ)) := by
              nlinarith [sq_nonneg (‖u‖ - ‖z‖ / (μ : ℝ)), μ.2]
    exact le_trans hnorm_bound hquad_bound
  · rw [if_neg hzμ]
    have hμ_le_z : (μ : ℝ) ≤ ‖z‖ := le_of_lt (lt_of_not_ge hzμ)
    have hfactor1 : 0 ≤ 1 - ‖u‖ := by
      linarith
    have hfactor2 : 0 ≤ ‖z‖ - (((μ : ℝ) / 2 : ℝ) * (1 + ‖u‖)) := by
      have hone_plus_le_two : 1 + ‖u‖ ≤ (2 : ℝ) := by
        linarith
      have hhalf_le : (((μ : ℝ) / 2 : ℝ) * (1 + ‖u‖)) ≤ (μ : ℝ) := by
        nlinarith [μ.2, hone_plus_le_two]
      linarith
    have hnorm_bound :
        ‖u‖ * ‖z‖ - (((μ : ℝ) / 2 : ℝ) * ‖u‖ ^ (2 : ℕ)) ≤ ‖z‖ - (μ : ℝ) / 2 := by
      -- The endpoint `γ = 1` dominates the linear branch on `[0, 1]`.
      have hprod :
          0 ≤ (1 - ‖u‖) * (‖z‖ - (((μ : ℝ) / 2 : ℝ) * (1 + ‖u‖))) :=
        mul_nonneg hfactor1 hfactor2
      nlinarith
    have hinner_bound :
        inner ℝ u z - ((μ : ℝ) / 2) * ‖u‖ ^ (2 : ℕ) ≤
          ‖u‖ * ‖z‖ - ((μ : ℝ) / 2) * ‖u‖ ^ (2 : ℕ) :=
      sub_le_sub_right hinner _
    exact le_trans hinner_bound hnorm_bound

/-- Helper for Definition 6.16: each coordinate admits an admissible dual vector that attains the
scalar Huber value. -/
private theorem continuousLocationCoordinateContribution_exists_eq_huberLoss
    (μ : {μ : ℝ // 0 < μ}) (z : E) :
    ∃ u : E, ‖u‖ ≤ 1 ∧
      inner ℝ u z - ((μ : ℝ) / 2) * ‖u‖ ^ (2 : ℕ) =
        continuousLocationHuberLoss μ ‖z‖ := by
  have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  by_cases hzμ : ‖z‖ ≤ (μ : ℝ)
  · refine ⟨(μ : ℝ)⁻¹ • z, ?_, ?_⟩
    · -- In the quadratic branch the scaled vector has norm `‖z‖ / μ ≤ 1`.
      have hnorm_le_one : ‖z‖ / (μ : ℝ) ≤ 1 := (_root_.div_le_iff₀ μ.2).2 (by simpa using hzμ)
      simpa [div_eq_mul_inv, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt μ.2)), mul_comm, mul_left_comm,
        mul_assoc] using hnorm_le_one
    · -- This witness realizes the quadratic branch value exactly.
      rw [continuousLocationHuberLoss_eq_piecewise μ hz_nonneg, if_pos hzμ]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr (le_of_lt μ.2))]
      have hμne : (μ : ℝ) ≠ 0 := ne_of_gt μ.2
      field_simp [hμne]
      ring
  · have hz_ne : z ≠ 0 := by
      intro hz
      apply hzμ
      simpa [hz] using (show (0 : ℝ) ≤ (μ : ℝ) from le_of_lt μ.2)
    refine ⟨‖z‖⁻¹ • z, ?_, ?_⟩
    · -- In the linear branch the normalized direction has unit norm.
      simpa using (norm_smul_inv_norm (𝕜 := ℝ) (x := z) hz_ne).le
    · -- The normalized direction attains the endpoint value `‖z‖ - μ / 2`.
      rw [continuousLocationHuberLoss_eq_piecewise μ hz_nonneg, if_neg hzμ]
      have hnorm_ne : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz_ne
      have hinner :
          inner ℝ (‖z‖⁻¹ • z) z = ‖z‖ := by
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp [hnorm_ne]
      have hunit : ‖‖z‖⁻¹ • z‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) (x := z) hz_ne
      rw [hinner, hunit]
      ring

-- Proof sketch: separate the dual maximization into the independent coordinate problems indexed
-- by `j`, identify each scalar maximization with `continuousLocationHuberLoss μ ‖x - c_j‖`, and
-- sum the resulting contributions with the weights `m_j`.
/-- Definition 6.16 [Chapter6_2.json:42]: the smooth approximation splits as the weighted sum of
scalar Huber losses evaluated at the
distances `‖x - c_j‖`. -/
theorem continuousLocationSmoothApproximation_eq_sum_huberLoss
    (weights : ContinuousLocationWeights ι) (centers : ι → E)
    (μ : {μ : ℝ // 0 < μ}) (x : E) :
    continuousLocationSmoothApproximation weights centers μ x =
      ∑ j, (weights j : ℝ) * continuousLocationHuberLoss μ ‖x - centers j‖ :=
by
  classical
  let s : Set ℝ :=
    smoothedPrimalObjectiveMaximand
        (continuousLocationSmoothingMap E weights)
        (continuousLocationCenterPenalty weights centers)
        (continuousLocationDualProxFunction E weights)
        (μ : ℝ) x '' continuousLocationDualAdmissibleSet E
  rw [continuousLocationSmoothApproximation_apply]
  change sSup s = ∑ j, (weights j : ℝ) * continuousLocationHuberLoss μ ‖x - centers j‖
  have hs_nonempty : s.Nonempty := by
    -- The zero tuple is always feasible, so the image set is nonempty.
    let u0 : ι → E := fun _ ↦ 0
    refine ⟨smoothedPrimalObjectiveMaximand
      (continuousLocationSmoothingMap E weights)
      (continuousLocationCenterPenalty weights centers)
      (continuousLocationDualProxFunction E weights)
      (μ : ℝ) x u0, ?_⟩
    refine ⟨u0, ?_, rfl⟩
    intro j
    simp [u0]
  have hs_upper :
      ∀ y ∈ s, y ≤ ∑ j, (weights j : ℝ) * continuousLocationHuberLoss μ ‖x - centers j‖ := by
    intro y hy
    rcases hy with ⟨u, hu, rfl⟩
    have hu_norm : ∀ j, ‖u j‖ ≤ 1 := (mem_continuousLocationDualAdmissibleSet_iff u).1 hu
    -- The objective separates by coordinates, and each coordinate is bounded by its Huber value.
    rw [smoothedPrimalObjectiveMaximand_continuousLocation_eq_coordinateSum]
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_left
      (continuousLocationCoordinateContribution_le_huberLoss μ (x - centers j) (u j) (hu_norm j))
      (le_of_lt (ContinuousLocationWeights.weights_pos weights j))
  have hs_bdd : BddAbove s := ⟨_, hs_upper⟩
  choose uStar huStar_norm huStar_value using
    fun j : ι ↦ continuousLocationCoordinateContribution_exists_eq_huberLoss
      (μ := μ) (x - centers j)
  have huStar_mem : uStar ∈ continuousLocationDualAdmissibleSet E := by
    -- The chosen coordinate witnesses are feasible in every coordinate.
    exact (mem_continuousLocationDualAdmissibleSet_iff uStar).2 huStar_norm
  have huStar_image :
      smoothedPrimalObjectiveMaximand
          (continuousLocationSmoothingMap E weights)
          (continuousLocationCenterPenalty weights centers)
          (continuousLocationDualProxFunction E weights)
          (μ : ℝ) x uStar ∈ s := by
    exact ⟨uStar, huStar_mem, rfl⟩
  have huStar_eq :
      smoothedPrimalObjectiveMaximand
          (continuousLocationSmoothingMap E weights)
          (continuousLocationCenterPenalty weights centers)
          (continuousLocationDualProxFunction E weights)
          (μ : ℝ) x uStar =
        ∑ j, (weights j : ℝ) * continuousLocationHuberLoss μ ‖x - centers j‖ := by
    -- The chosen witnesses attain the scalar Huber value in every coordinate.
    rw [smoothedPrimalObjectiveMaximand_continuousLocation_eq_coordinateSum]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [huStar_value j]
  refine le_antisymm ?_ ?_
  · exact csSup_le hs_nonempty hs_upper
  · exact le_csSup_of_le hs_bdd huStar_image (le_of_eq huStar_eq.symm)

end Smoothing

end
