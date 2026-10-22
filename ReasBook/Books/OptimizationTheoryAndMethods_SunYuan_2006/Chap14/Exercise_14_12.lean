/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_7_1

noncomputable section

open scoped BigOperators CompositeNonsmooth

section

variable {n m : ℕ}
variable {ρ : (Fin n → ℝ) → ℝ} [IsVectorNorm ρ]

local notation "Point" => Chapter14.Point n
local notation "ValuePoint" => Chapter14.Point m
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling:
-- * primary domain: Section 14.7 composite nonsmooth trust-region methods;
-- * inspected owner declarations in the minimal Chapter 14 closure:
--   `CompositeNonsmoothTrustRegion.hessianApproximationAt`,
--   `CompositeNonsmoothTrustRegion.modelAt`,
--   `CompositeNonsmoothTrustRegion.reductionRatioAt`,
--   `CompositeNonsmoothTrustRegionMethod`;
-- * inspected project finite-window-max owners for the new source-facing `R_k`:
--   `nonmonotoneArmijoWindow`,
--   `nonmonotoneArmijoReferenceValue`;
-- * source/core/bridge triage:
--   - source-facing here: the bounded reference-value recursion and the resulting
--     nonmonotone trust-region update rule;
--   - core/canonical reused here: the norm-parametric Chapter 14.7 trust-region stage owners,
--     the trust-region method subproblem predicate, the accepted-step multiplier relation, and
--     the Chapter 2 bounded recent-index window owner;
--   - bridge/view here: the Euclidean Hessian-matrix realization provided by `hessianMatrixAt`.
-- * primitive data vs derived API:
--   - primitive data here are the reference-window recursion and the stage data
--     `iterate`, `multiplier`, `direction`, and `trustRegionRadius`;
--   - the Jacobian transpose, component Hessians, trust-region model, and accepted-step
--     relation are derived from the Chapter 14.6/14.7 owners and are not stored again.

/-- The bounded nonmonotone reference value `R_k = max {objective (iterate (k - j)) | 0 ≤ j ≤
min (k - 1) mk}` used to replace the monotone numerator `objective (iterate k)` in the
acceptance test at stage `k`. -/
def nonmonotoneTrustRegionReferenceValue
    (objective : Point → ℝ) (iterate : ℕ → Point) (k mk : ℕ) : ℝ :=
  (nonmonotoneArmijoWindow (k - 1) mk).sup'
    (nonmonotoneArmijoWindow_nonempty (k - 1) mk)
    (fun j ↦ objective (iterate (k - j)))

/-- The source-facing owner `nonmonotoneTrustRegionReferenceValue objective iterate k mk`
is the bounded-window maximum over the recent objective values entering the nonmonotone
trust-region acceptance test. -/
theorem nonmonotoneTrustRegionReferenceValue_eq
    (objective : Point → ℝ) (iterate : ℕ → Point) (k mk : ℕ) :
    nonmonotoneTrustRegionReferenceValue objective iterate k mk =
      (nonmonotoneArmijoWindow (k - 1) mk).sup'
        (nonmonotoneArmijoWindow_nonempty (k - 1) mk)
        (fun j ↦ objective (iterate (k - j))) :=
  rfl

/-- For stages `k ≥ 1`, the Chapter 14 reference value `R_k` is the Chapter 2 nonmonotone
Armijo reference-value owner applied to the shifted iterate sequence `j ↦ iterate (j + 1)`. -/
theorem nonmonotoneTrustRegionReferenceValue_eq_nonmonotoneArmijoReferenceValue
    (objective : Point → ℝ) (iterate : ℕ → Point) {k mk : ℕ} (hk : 1 ≤ k) :
    nonmonotoneTrustRegionReferenceValue objective iterate k mk =
      nonmonotoneArmijoReferenceValue objective (fun j ↦ iterate (j + 1)) (k - 1) mk := by
  rw [nonmonotoneTrustRegionReferenceValue_eq, nonmonotoneArmijoReferenceValue_eq]
  let s := nonmonotoneArmijoWindow (k - 1) mk
  let hs : s.Nonempty := nonmonotoneArmijoWindow_nonempty (k - 1) mk
  simpa [s, hs] using
    (Finset.sup'_congr hs rfl fun j hj ↦ by
      rcases mem_nonmonotoneArmijoWindow.mp hj with ⟨hjk, _⟩
      have hindex : ((k - 1) - j) + 1 = k - j := by
        have hk' : k - 1 + 1 = k := Nat.sub_add_cancel hk
        simpa [Nat.succ_eq_add_one, hk'] using
          (Nat.succ_sub hjk).symm
      simp [hindex])

/-- The nonmonotone ratio obtained by replacing `objective (iterate k)` in `(14.7.8)` with the
reference value `nonmonotoneTrustRegionReferenceValue objective iterate k mk`. -/
def nonmonotoneTrustRegionReductionRatio
    (objective : Point → ℝ) (iterate : ℕ → Point) (k mk : ℕ)
    (d : Point) (φ : Point → ℝ) : ℝ :=
  (nonmonotoneTrustRegionReferenceValue objective iterate k mk -
      objective (iterate k + d)) /
    trustRegionPredictedReduction φ d

/-- Unfolding `nonmonotoneTrustRegionReductionRatio objective iterate k mk d φ` gives the
nonmonotone variant of the source ratio `(14.7.8)`. -/
theorem nonmonotoneTrustRegionReductionRatio_eq
    (objective : Point → ℝ) (iterate : ℕ → Point) (k mk : ℕ)
    (d : Point) (φ : Point → ℝ) :
    nonmonotoneTrustRegionReductionRatio objective iterate k mk d φ =
      (nonmonotoneTrustRegionReferenceValue objective iterate k mk -
          objective (iterate k + d)) /
        trustRegionPredictedReduction φ d :=
  rfl

private abbrev componentHessianMatrix
    (problem : CompositeNonsmoothOptimizationProblem n m) :
    Fin m → Point → MatrixN :=
  fun i x ↦ hessianMatrixAt (fun y : Point ↦ problem.smoothMap y i) x

private def stageReductionRatio
    (problem : CompositeNonsmoothOptimizationProblem n m)
    (iterate : ℕ → Point) (multiplier : ℕ → ValuePoint)
    (direction : ℕ → Point) (referenceWindowSize : ℕ → ℕ) (k : ℕ) : ℝ :=
  nonmonotoneTrustRegionReductionRatio
    problem
    iterate
    k
    (referenceWindowSize k)
    (direction k)
    (CompositeNonsmoothTrustRegion.modelAt problem iterate multiplier k)

/-- Chapter14 Exercise 14.12: a nonmonotone modification of Algorithm 14.7.1, still organized
around the chosen trust-region norm `ρ`, keeps the same trust-region subproblem, stopping test,
and radius-update thresholds as Algorithm 14.7.1, but replaces the monotone actual-reduction
numerator `h (f(x_k)) - h (f(x_k + d_k))` by the bounded-window nonmonotone numerator
`R_k - h (f(x_k + d_k))`, where `R_k` is the reference value over the most recent objective
values determined by `referenceWindowSize k`. The primitive data are the composite problem, the
`C²` regularity of the component functions, the bounded reference-window recursion, and the
recorded stage data. The Jacobian transpose, component Hessians, trust-region model, and
accepted-step multiplier relation are reused canonically from the norm-parametric Chapter 14.7
owners rather than stored as parallel fields. -/
structure NonmonotoneCompositeNonsmoothTrustRegionMethod
    (n m : ℕ) (ρ : (Fin n → ℝ) → ℝ) [IsVectorNorm ρ] where
  problem : CompositeNonsmoothOptimizationProblem n m
  componentContDiff :
    ∀ i : Fin m, ContDiff ℝ 2 (fun y : Chapter14.Point n ↦ problem.smoothMap y i)
  initialPoint : Chapter14.Point n
  initialMultiplier : Chapter14.Point m
  initialRadius : ℝ
  epsilon : ℝ
  referenceWindowBound : ℕ
  referenceWindowSize : ℕ → ℕ
  iterate : ℕ → Chapter14.Point n
  multiplier : ℕ → Chapter14.Point m
  direction : ℕ → Chapter14.Point n
  trustRegionRadius : ℕ → ℝ
  initialRadius_pos : 0 < initialRadius
  epsilon_nonneg : 0 ≤ epsilon
  iterate_one : iterate 1 = initialPoint
  multiplier_zero : multiplier 0 = initialMultiplier
  trustRegionRadius_one : trustRegionRadius 1 = initialRadius
  referenceWindowSize_one : referenceWindowSize 1 = 0
  referenceWindowSize_succ_le
      (k : ℕ) (_hk : 1 ≤ k) :
      referenceWindowSize (k + 1) ≤
        Nat.min (referenceWindowSize k + 1) referenceWindowBound
  direction_subproblem_solution
      (k : ℕ) (_hk : 1 ≤ k) :
      IsCompositeNonsmoothTrustRegionSolution
        ρ
        problem
        (iterate k)
        (CompositeNonsmoothTrustRegion.hessianApproximationAt problem iterate multiplier k)
        (trustRegionRadius k)
        (direction k)
  predictedReduction_pos
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp) :
      0 <
        trustRegionPredictedReduction
          (CompositeNonsmoothTrustRegion.modelAt problem iterate multiplier k)
          (direction k)
  trustRegionRadius_succ
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp) :
      trustRegionRadius (k + 1) =
        if stageReductionRatio
              problem
              iterate
              multiplier
              direction
              referenceWindowSize
              k <
            (1 / 4 : ℝ) then
          ρ (direction k).ofLp / 4
        else if (3 / 4 : ℝ) <
              stageReductionRatio
                problem
                iterate
                multiplier
                direction
                referenceWindowSize
                k ∧
              ρ (direction k).ofLp = trustRegionRadius k then
          2 * trustRegionRadius k
        else
          trustRegionRadius k
  iterate_succ_of_positive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        0 <
          stageReductionRatio
            problem
            iterate
            multiplier
            direction
            referenceWindowSize
            k) :
      iterate (k + 1) = CompositeNonsmoothTrustRegion.trialPoint iterate direction k
  multiplier_of_positive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        0 <
          stageReductionRatio
            problem
            iterate
            multiplier
            direction
            referenceWindowSize
            k) :
      IsCompositeNonsmoothAcceptedStepMultiplier
        problem
        (CompositeNonsmoothTrustRegion.trialPoint iterate direction k)
        (direction k)
        (multiplier k)
  iterate_succ_of_nonpositive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        stageReductionRatio
            problem
            iterate
            multiplier
            direction
            referenceWindowSize
            k ≤
          0) :
      iterate (k + 1) = iterate k
  multiplier_of_nonpositive_ratio
      (k : ℕ) (_hk : 1 ≤ k) (_hContinue : epsilon < ρ (direction k).ofLp)
      (_hrk :
        stageReductionRatio
            problem
            iterate
            multiplier
            direction
            referenceWindowSize
            k ≤
          0) :
      multiplier k = multiplier (k - 1)

namespace NonmonotoneCompositeNonsmoothTrustRegionMethod

variable {ρ : (Fin n → ℝ) → ℝ} [IsVectorNorm ρ]

local notation "Method" => @_root_.NonmonotoneCompositeNonsmoothTrustRegionMethod n m ρ _

/-- A nonmonotone composite nonsmooth trust-region method can be evaluated at stage `k` as its
iterate `x_k`. -/
instance : CoeFun Method (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply (method : Method) (k : ℕ) :
    method k = method.iterate k :=
  rfl

/-- Each scalar component `x ↦ f_i(x)` of the smooth map in Exercise 14.12 is globally `C²`. -/
theorem component_contDiff
    (method : Method) (i : Fin m) :
    ContDiff ℝ 2 (fun y : Point ↦ method.problem.smoothMap y i) :=
  method.componentContDiff i

/-- The matrix `B_k` from `(14.7.7)`, built from the current iterate `x_k` and the previous
multiplier vector `λ_(k - 1)`. -/
def hessianApproximationAt
    (method : Method) (k : ℕ) : MatrixN :=
  CompositeNonsmoothTrustRegion.hessianApproximationAt
    method.problem
    method.iterate
    method.multiplier
    k

/-- Unfolding `method.hessianApproximationAt k` gives the source matrix `B_k` from `(14.7.7)`. -/
theorem hessianApproximationAt_eq
    (method : Method) (k : ℕ) :
    method.hessianApproximationAt k =
      ∑ i : Fin m,
        (method.multiplier (k - 1)) i •
          hessianMatrixAt (fun y : Point ↦ method.problem.smoothMap y i) (method.iterate k) :=
  trustRegionHessianApproximation_eq
    (componentHessianMatrix method.problem)
    (method.iterate k)
    (method.multiplier (k - 1))

/-- The stage model `φ_k` is the Chapter 14.7 trust-region model derived from the current
iterate, the previous multiplier, and the resulting Hessian approximation `B_k`. -/
def modelFunction
    (method : Method) (k : ℕ) : Point → ℝ :=
  CompositeNonsmoothTrustRegion.modelAt
    method.problem
    method.iterate
    method.multiplier
    k

/-- At stage `k`, the recorded model function agrees with the canonical trust-region model. -/
theorem modelFunction_eq
    (method : Method) (k : ℕ) :
    method.modelFunction k =
      compositeNonsmoothTrustRegionModel method.problem (method.iterate k)
        (method.hessianApproximationAt k) :=
  rfl

/-- The trial point `x_k + d_k` used in the acceptance test. -/
def trialPointAt (method : Method) (k : ℕ) : Point :=
  CompositeNonsmoothTrustRegion.trialPoint method.iterate method.direction k

/-- Unfolding `method.trialPointAt k` gives the Step-5 trial point `x_k + d_k`. -/
theorem trialPointAt_eq
    (method : Method) (k : ℕ) :
    method.trialPointAt k = method.iterate k + method.direction k :=
  rfl

/-- The nonmonotone reference value `R_k` formed from the recent objective values of `method`. -/
def referenceValueAt
    (method : Method) (k : ℕ) : ℝ :=
  nonmonotoneTrustRegionReferenceValue
    method.problem
    method.iterate
    k
    (method.referenceWindowSize k)

/-- `method.referenceValueAt k` is the bounded-window maximum over the recent objective values
used as the nonmonotone reference value `R_k`. -/
theorem referenceValueAt_eq
    (method : Method) (k : ℕ) :
    method.referenceValueAt k =
      (nonmonotoneArmijoWindow (k - 1) (method.referenceWindowSize k)).sup'
        (nonmonotoneArmijoWindow_nonempty (k - 1) (method.referenceWindowSize k))
        (fun j ↦ method.problem (method.iterate (k - j))) := by
  rw [referenceValueAt, nonmonotoneTrustRegionReferenceValue_eq]

/-- The predicted reduction `φ_k(0) - φ_k(d_k)` at stage `k`. -/
def predictedReductionAt
    (method : Method) (k : ℕ) : ℝ :=
  trustRegionPredictedReduction (method.modelFunction k) (method.direction k)

/-- Unfolding `method.predictedReductionAt k` gives the denominator of the nonmonotone ratio. -/
theorem predictedReductionAt_eq
    (method : Method) (k : ℕ) :
    method.predictedReductionAt k =
      trustRegionPredictedReduction (method.modelFunction k) (method.direction k) :=
  rfl

/-- The nonmonotone ratio at stage `k`, obtained by replacing `objective (iterate k)` with the
reference value `R_k` in the source ratio `(14.7.8)`. -/
def reductionRatioAt
    (method : Method) (k : ℕ) : ℝ :=
  stageReductionRatio
    method.problem
    method.iterate
    method.multiplier
    method.direction
    method.referenceWindowSize
    k

/-- Unfolding `method.reductionRatioAt k` gives the nonmonotone trust-region ratio used in the
acceptance test at stage `k`. -/
theorem reductionRatioAt_eq
    (method : Method) (k : ℕ) :
    method.reductionRatioAt k =
      (method.referenceValueAt k - method.problem (method.trialPointAt k)) /
        method.predictedReductionAt k :=
  rfl

/-- If the reference window at stage `k` collapses to `{0}`, then the nonmonotone reference
value is the current objective value `h (f(x_k))`. -/
theorem referenceValueAt_eq_objective
    (method : Method) {k : ℕ} (hk : method.referenceWindowSize k = 0) :
    method.referenceValueAt k = method.problem (method.iterate k) := by
  rw [referenceValueAt, nonmonotoneTrustRegionReferenceValue_eq, hk]
  simp [nonmonotoneArmijoWindow]

/-- Under the zero-window specialization, the nonmonotone ratio reduces to the monotone
trust-region ratio from Algorithm 14.7.1. -/
theorem reductionRatioAt_eq_monotone
    (method : Method) {k : ℕ} (hk : method.referenceWindowSize k = 0) :
    method.reductionRatioAt k =
      (method.problem (method.iterate k) - method.problem (method.trialPointAt k)) /
        method.predictedReductionAt k := by
  rw [reductionRatioAt_eq, referenceValueAt_eq_objective method hk]

/-- Under the zero-window specialization, the stage ratio entering the nonmonotone update rule
is exactly the Chapter 14.7 monotone stage ratio. -/
theorem stageReductionRatio_eq_monotone
    (method : Method) {k : ℕ} (hk : method.referenceWindowSize k = 0) :
    stageReductionRatio
        method.problem
        method.iterate
        method.multiplier
        method.direction
        method.referenceWindowSize
        k =
      CompositeNonsmoothTrustRegion.reductionRatioAt
        method.problem
        method.iterate
        method.multiplier
        method.direction
        k := by
  rw [stageReductionRatio, CompositeNonsmoothTrustRegion.reductionRatioAt,
    nonmonotoneTrustRegionReductionRatio, nonmonotoneTrustRegionReferenceValue_eq, hk]
  simp [CompositeNonsmoothTrustRegion.trialPoint, CompositeNonsmoothTrustRegion.modelAt,
    nonmonotoneArmijoWindow, trustRegionPredictedReduction]

/-- `method.stopsAt k` is the Step-2 stopping test `ρ(d_k) ≤ ε`. -/
def stopsAt (method : Method) (k : ℕ) : Prop :=
  ρ (method.direction k).ofLp ≤ method.epsilon

/-- Unfolding `method.stopsAt k` gives the Step-2 stopping condition `ρ(d_k) ≤ ε`. -/
theorem stopsAt_iff
    (method : Method) (k : ℕ) :
    method.stopsAt k ↔ ρ (method.direction k).ofLp ≤ method.epsilon :=
  Iff.rfl

/-- `method.continuesAt k` is the Step-2 continuation branch `ε < ρ(d_k)`. -/
def continuesAt (method : Method) (k : ℕ) : Prop :=
  method.epsilon < ρ (method.direction k).ofLp

/-- Unfolding `method.continuesAt k` gives the Step-2 continuation condition `ε < ρ(d_k)`. -/
theorem continuesAt_iff
    (method : Method) (k : ℕ) :
    method.continuesAt k ↔ method.epsilon < ρ (method.direction k).ofLp :=
  Iff.rfl

/-- Every stage either stops or continues after the Step-2 norm test. -/
theorem stop_or_continue
    (method : Method) (k : ℕ) :
    method.stopsAt k ∨ method.continuesAt k := by
  rcases lt_or_ge method.epsilon (ρ (method.direction k).ofLp) with hContinue | hStop
  · exact Or.inr hContinue
  · exact Or.inl hStop

/-- The recorded iterate sequence starts from the given initial point `x₁`. -/
theorem iterate_one_eq_initialPoint (method : Method) :
    method.iterate 1 = method.initialPoint :=
  method.iterate_one

/-- The recorded multiplier sequence starts from the given initial value `λ₀`. -/
theorem multiplier_zero_eq_initialMultiplier
    (method : Method) :
    method.multiplier 0 = method.initialMultiplier :=
  method.multiplier_zero

/-- The recorded trust-region radii start from the given initial radius `Δ₁`. -/
theorem trustRegionRadius_one_eq_initialRadius
    (method : Method) :
    method.trustRegionRadius 1 = method.initialRadius :=
  method.trustRegionRadius_one

/-- At each recorded stage `k ≥ 1`, the direction `d_k` solves the source subproblem
`(14.7.1)`-`(14.7.2)` built from `A(x_k)` and `B_k`. -/
theorem direction_subproblem_solution_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k) :
    IsCompositeNonsmoothTrustRegionSolution
      ρ
      method.problem
      (method.iterate k)
      (method.hessianApproximationAt k)
      (method.trustRegionRadius k)
      (method.direction k) := by
  simpa [hessianApproximationAt, CompositeNonsmoothTrustRegion.hessianApproximationAt] using
    method.direction_subproblem_solution k hk

/-- Every continuing stage `k ≥ 1` has strictly positive predicted reduction
`φ_k(0) - φ_k(d_k)`. -/
theorem predictedReduction_pos_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (hContinue : method.continuesAt k) :
    0 < method.predictedReductionAt k := by
  simpa [continuesAt, predictedReductionAt, modelFunction, CompositeNonsmoothTrustRegion.modelAt,
    trustRegionPredictedReduction] using
    method.predictedReduction_pos k hk hContinue

/-- At each continuing stage `k ≥ 1`, the next trust-region radius is updated by the Step-3
branching rule based on the nonmonotone ratio. -/
theorem trustRegionRadius_succ_eq
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (hContinue : method.continuesAt k) :
    method.trustRegionRadius (k + 1) =
      if method.reductionRatioAt k < (1 / 4 : ℝ) then
        ρ (method.direction k).ofLp / 4
      else if (3 / 4 : ℝ) < method.reductionRatioAt k ∧
            ρ (method.direction k).ofLp = method.trustRegionRadius k then
        2 * method.trustRegionRadius k
      else
        method.trustRegionRadius k := by
  change method.trustRegionRadius (k + 1) =
    if stageReductionRatio
          method.problem
          method.iterate
          method.multiplier
          method.direction
          method.referenceWindowSize
          k <
        (1 / 4 : ℝ) then
      ρ (method.direction k).ofLp / 4
    else if (3 / 4 : ℝ) < stageReductionRatio
            method.problem
            method.iterate
            method.multiplier
            method.direction
            method.referenceWindowSize
            k ∧
          ρ (method.direction k).ofLp = method.trustRegionRadius k then
      2 * method.trustRegionRadius k
    else
      method.trustRegionRadius k
  exact method.trustRegionRadius_succ k hk hContinue

/-- If a continuing stage has positive nonmonotone ratio, Step 5 accepts the trial point as the
next iterate. -/
theorem iterate_succ_eq_trialPointAt_of_positive_ratio
    (method : Method) {k : ℕ}
    (hk : 1 ≤ k) (hContinue : method.continuesAt k) (hrk : 0 < method.reductionRatioAt k) :
    method.iterate (k + 1) = method.trialPointAt k :=
  method.iterate_succ_of_positive_ratio k hk hContinue
    (show
      0 <
        stageReductionRatio
          method.problem
          method.iterate
          method.multiplier
          method.direction
          method.referenceWindowSize
          k from hrk)

/-- If a continuing stage has positive nonmonotone ratio, the accepted multiplier satisfies the
Step-5 relation at the accepted point `x_k + d_k`. -/
theorem acceptedStepMultiplier_at
    (method : Method) {k : ℕ}
    (hk : 1 ≤ k) (hContinue : method.continuesAt k) (hrk : 0 < method.reductionRatioAt k) :
    IsCompositeNonsmoothAcceptedStepMultiplier
      method.problem
      (method.trialPointAt k)
      (method.direction k)
      (method.multiplier k) :=
  method.multiplier_of_positive_ratio k hk hContinue
    (show
      0 <
        stageReductionRatio
          method.problem
          method.iterate
          method.multiplier
          method.direction
          method.referenceWindowSize
          k from hrk)

/-- If a continuing stage has nonpositive nonmonotone ratio, Step 4 keeps the current iterate
unchanged. -/
theorem iterate_succ_eq_self_of_nonpositive_ratio
    (method : Method) {k : ℕ}
    (hk : 1 ≤ k) (hContinue : method.continuesAt k) (hrk : method.reductionRatioAt k ≤ 0) :
    method.iterate (k + 1) = method.iterate k :=
  method.iterate_succ_of_nonpositive_ratio k hk hContinue
    (by simpa [reductionRatioAt] using hrk)

/-- If a continuing stage has nonpositive nonmonotone ratio, Step 4 also keeps the multiplier
vector unchanged. -/
theorem multiplier_eq_prev_of_nonpositive_ratio
    (method : Method) {k : ℕ}
    (hk : 1 ≤ k) (hContinue : method.continuesAt k) (hrk : method.reductionRatioAt k ≤ 0) :
    method.multiplier k = method.multiplier (k - 1) :=
  method.multiplier_of_nonpositive_ratio k hk hContinue
    (show
      stageReductionRatio
          method.problem
          method.iterate
          method.multiplier
          method.direction
          method.referenceWindowSize
          k ≤
        0 from hrk)

private theorem zeroWindow_trustRegionRadius_succ
    (method : Method) (hzero : ∀ k : ℕ, method.referenceWindowSize k = 0)
    (k : ℕ) (hk : 1 ≤ k) (hContinue : method.continuesAt k) :
    method.trustRegionRadius (k + 1) =
      if CompositeNonsmoothTrustRegion.reductionRatioAt
            method.problem
            method.iterate
            method.multiplier
            method.direction
            k <
          (1 / 4 : ℝ) then
        ρ (method.direction k).ofLp / 4
      else if (3 / 4 : ℝ) <
            CompositeNonsmoothTrustRegion.reductionRatioAt
              method.problem
              method.iterate
              method.multiplier
              method.direction
              k ∧
            ρ (method.direction k).ofLp = method.trustRegionRadius k then
        2 * method.trustRegionRadius k
      else
        method.trustRegionRadius k := by
  have hratio := stageReductionRatio_eq_monotone method (hzero k)
  simpa [hratio] using method.trustRegionRadius_succ k hk hContinue

private theorem zeroWindow_iterate_succ_of_positive_ratio
    (method : Method) (hzero : ∀ k : ℕ, method.referenceWindowSize k = 0)
    (k : ℕ) (hk : 1 ≤ k) (hContinue : method.continuesAt k)
    (hrk :
      0 <
        CompositeNonsmoothTrustRegion.reductionRatioAt
          method.problem
          method.iterate
          method.multiplier
          method.direction
          k) :
    method.iterate (k + 1) =
      CompositeNonsmoothTrustRegion.trialPoint method.iterate method.direction k := by
  have hratio := stageReductionRatio_eq_monotone method (hzero k)
  exact method.iterate_succ_of_positive_ratio k hk hContinue <| by
    simpa [hratio] using hrk

private theorem zeroWindow_multiplier_of_positive_ratio
    (method : Method) (hzero : ∀ k : ℕ, method.referenceWindowSize k = 0)
    (k : ℕ) (hk : 1 ≤ k) (hContinue : method.continuesAt k)
    (hrk :
      0 <
        CompositeNonsmoothTrustRegion.reductionRatioAt
          method.problem
          method.iterate
          method.multiplier
          method.direction
          k) :
    IsCompositeNonsmoothAcceptedStepMultiplier
      method.problem
      (CompositeNonsmoothTrustRegion.trialPoint method.iterate method.direction k)
      (method.direction k)
      (method.multiplier k) := by
  have hratio := stageReductionRatio_eq_monotone method (hzero k)
  exact method.multiplier_of_positive_ratio k hk hContinue <| by
    simpa [hratio] using hrk

private theorem zeroWindow_iterate_succ_of_nonpositive_ratio
    (method : Method) (hzero : ∀ k : ℕ, method.referenceWindowSize k = 0)
    (k : ℕ) (hk : 1 ≤ k) (hContinue : method.continuesAt k)
    (hrk :
      CompositeNonsmoothTrustRegion.reductionRatioAt
          method.problem
          method.iterate
          method.multiplier
          method.direction
          k ≤
        0) :
    method.iterate (k + 1) = method.iterate k := by
  have hratio := stageReductionRatio_eq_monotone method (hzero k)
  exact method.iterate_succ_of_nonpositive_ratio k hk hContinue <| by
    simpa [hratio] using hrk

private theorem zeroWindow_multiplier_of_nonpositive_ratio
    (method : Method) (hzero : ∀ k : ℕ, method.referenceWindowSize k = 0)
    (k : ℕ) (hk : 1 ≤ k) (hContinue : method.continuesAt k)
    (hrk :
      CompositeNonsmoothTrustRegion.reductionRatioAt
          method.problem
          method.iterate
          method.multiplier
          method.direction
          k ≤
        0) :
    method.multiplier k = method.multiplier (k - 1) := by
  have hratio := stageReductionRatio_eq_monotone method (hzero k)
  exact method.multiplier_of_nonpositive_ratio k hk hContinue <| by
    simpa [hratio] using hrk

/-- If every reference window has size `0`, the nonmonotone method specializes to the monotone
Chapter 14.7 trust-region method with the same stage data. -/
def toCompositeNonsmoothTrustRegionMethod
    (method : Method) (hzero : ∀ k : ℕ, method.referenceWindowSize k = 0) :
    CompositeNonsmoothTrustRegionMethod n m ρ :=
  { problem := method.problem
    componentContDiff := method.componentContDiff,
    initialPoint := method.initialPoint,
    initialMultiplier := method.initialMultiplier,
    initialRadius := method.initialRadius,
    epsilon := method.epsilon,
    iterate := method.iterate,
    multiplier := method.multiplier,
    direction := method.direction,
    trustRegionRadius := method.trustRegionRadius,
    initialRadius_pos := method.initialRadius_pos,
    epsilon_nonneg := method.epsilon_nonneg,
    iterate_one := method.iterate_one,
    multiplier_zero := method.multiplier_zero,
    trustRegionRadius_one := method.trustRegionRadius_one,
    direction_subproblem_solution := method.direction_subproblem_solution,
    predictedReduction_pos := method.predictedReduction_pos,
    trustRegionRadius_succ := zeroWindow_trustRegionRadius_succ method hzero,
    iterate_succ_of_positive_ratio := zeroWindow_iterate_succ_of_positive_ratio method hzero,
    multiplier_of_positive_ratio := zeroWindow_multiplier_of_positive_ratio method hzero,
    iterate_succ_of_nonpositive_ratio := zeroWindow_iterate_succ_of_nonpositive_ratio method hzero,
    multiplier_of_nonpositive_ratio := zeroWindow_multiplier_of_nonpositive_ratio method hzero }

end NonmonotoneCompositeNonsmoothTrustRegionMethod

end
