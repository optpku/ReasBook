/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Real.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Lemma_6_1_5

-- Domain-style sampling for Algorithm `6.1.1`:
-- * primary domain: trust-region subproblems and trust-region radius control;
-- * inspected owner declarations:
--   `TrustRegionSubproblem.feasibleSet`,
--   `TrustRegionSubproblem.isApproximateSolution`,
--   `TrustRegionSubproblem.reductionRatio`,
--   `TrustRegionLevenbergMarquardtAlgorithm.radius_update`,
--   `LinearConstraintTrustRegionMethod.nextRadiusAt`;
-- * best owner abstraction here: `TrustRegionAlgorithm` should store the primitive iteration
--   data together with one total source-faithful radius-update rule, while the stage-`k`
--   subproblem and the branchwise radius consequences remain derived API;
-- * primitive data: the iterate, step, model, ratio, and radius sequences together with the
--   stagewise approximate-solution and total radius-update conditions;
-- * derived API: `subproblem`, feasibility/predicted-reduction consequences, and the separate
--   shrink/keep/expand lemmas extracted from the total radius rule.

noncomputable section

open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- The source admissible set for the next trust-region radius in Algorithm `6.1.1`: shrink when
`r < η₁`, expand when `η₂ ≤ r` and the trial step reaches the trust-region boundary, and
otherwise keep the next radius in `[γ₁ Δ, Δ]`. -/
def trustRegionRadiusUpdateSet
    (η1 η2 γ1 γ2 ΔMax Δ r stepNorm : ℝ) : Set ℝ :=
  if r < η1 then
    Set.Ioc (0 : ℝ) (γ1 * Δ)
  else if η2 ≤ r ∧ stepNorm = Δ then
    Set.Icc Δ (min (γ2 * Δ) ΔMax)
  else
    Set.Icc (γ1 * Δ) Δ

/-- Chapter06 Algorithm 6.1.1: a trust-region algorithm on `ℝ^n` consists of an
objective `f`, an initial point `x₀`, an overall radius bound `ΔMax`, an initial
trust-region radius `Δ0 ∈ (0, ΔMax)`, parameters `ε ≥ 0`, `0 < η1 ≤ η2 < 1`, and
`0 < γ1 < 1 < γ2`, together with a uniform `β₂ ∈ Set.Ioc (0 : ℝ) 1`, explicit sequences
of iterates `x k`, trial steps `s k`, gradients `g k`, model matrices `B k`, ratios
`r k`, and radii `Δ k`. At every active iteration with `ε < ‖g k‖`, the structure
records the source-faithful Step 3 condition `(subproblem k).isApproximateSolution β₂
(s k)` for the trust-region subproblem built from `f (x k)`, `g k`, `B k`, and `Δ k`,
and fixes `r k` to be the usual actual-to-predicted reduction ratio. Positivity of the
predicted reduction on active iterations is derived later from Lemma `6.1.5` on the
canonical subproblem owner. The quadratic model `q^(k)` is treated as the derived
function view of `(subproblem k)`, while `x k` enters the ratio only through the
actual-reduction bridge. The stopping test `‖g k‖ ≤ ε`, accepted-iterate update, and the
total source radius-update rule are primitive algorithm data; the separate shrink/keep/expand
cases are derived later from that single owner-level rule. -/
structure TrustRegionAlgorithm (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) where
  ε : ℝ
  η1 : ℝ
  η2 : ℝ
  γ1 : ℝ
  γ2 : ℝ
  β₂ : ℝ
  x0 : EuclideanSpace ℝ (Fin n)
  ΔMax : ℝ
  Δ0 : ℝ
  x : ℕ → EuclideanSpace ℝ (Fin n)
  s : ℕ → EuclideanSpace ℝ (Fin n)
  g : ℕ → EuclideanSpace ℝ (Fin n)
  B : ℕ → Matrix (Fin n) (Fin n) ℝ
  r : ℕ → ℝ
  Δ : ℕ → ℝ
  epsilon_nonneg : 0 ≤ ε
  eta1_pos : 0 < η1
  eta1_le_eta2 : η1 ≤ η2
  eta2_lt_one : η2 < 1
  gamma1_mem : γ1 ∈ Set.Ioo (0 : ℝ) 1
  gamma2_gt_one : 1 < γ2
  beta2_mem : β₂ ∈ Set.Ioc (0 : ℝ) 1
  deltaMax_pos : 0 < ΔMax
  delta0_mem : Δ0 ∈ Set.Ioo (0 : ℝ) ΔMax
  x_zero : x 0 = x0
  delta_zero : Δ 0 = Δ0
  delta_mem (k : ℕ) : Δ k ∈ Set.Ioc (0 : ℝ) ΔMax
  hasGradientAt (k : ℕ) : HasGradientAt f (g k) (x k)
  B_symm (k : ℕ) : (B k).IsSymm
  step_isApproximateSolution (k : ℕ) (_ : ε < ‖g k‖) :
      ({
        fAtCenter := f (x k)
        gradient := g k
        hessianApprox := B k
        hessianApprox_symm := B_symm k
        radius := Δ k
        radius_pos := (delta_mem k).1
      } : TrustRegionSubproblem n).isApproximateSolution β₂ (s k)
  ratio_eq (k : ℕ) (_ : ε < ‖g k‖) :
      r k =
        ({
          fAtCenter := f (x k)
          gradient := g k
          hessianApprox := B k
          hessianApprox_symm := B_symm k
          radius := Δ k
          radius_pos := (delta_mem k).1
        } : TrustRegionSubproblem n).reductionRatio (x k) f (s k)
  iterate_update (k : ℕ) (_ : ε < ‖g k‖) :
      x (k + 1) = if η1 ≤ r k then x k + s k else x k
  radius_update (k : ℕ) (_ : ε < ‖g k‖) :
      Δ (k + 1) ∈
        trustRegionRadiusUpdateSet η1 η2 γ1 γ2 ΔMax (Δ k) (r k) ‖s k‖

/-- A trust-region algorithm can be used as its sequence of iterates. -/
instance {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} :
    CoeFun (TrustRegionAlgorithm n f) (fun _ ↦ ℕ → EuclideanSpace ℝ (Fin n)) where
  coe A := A.x

namespace TrustRegionAlgorithm

/-- The source admissible set for `Δ (k + 1)` at active iteration `k`. -/
def nextRadiusSet {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) : Set ℝ :=
  trustRegionRadiusUpdateSet A.η1 A.η2 A.γ1 A.γ2 A.ΔMax (A.Δ k) (A.r k) ‖A.s k‖

/-- The stage-`k` trust-region subproblem canonically determined by the iteration data. -/
def subproblem {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (k : ℕ) : TrustRegionSubproblem n where
  fAtCenter := f (A.x k)
  gradient := A.g k
  hessianApprox := A.B k
  hessianApprox_symm := A.B_symm k
  radius := A.Δ k
  radius_pos := (A.delta_mem k).1

/-- Evaluating the stage-`k` subproblem as a function gives the standard trust-region quadratic
model formula for the source `q^(k)`. -/
theorem subproblem_apply_eq {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (k : ℕ) (sStep : Point) :
    A.subproblem k sStep =
      f (A.x k) + dotProduct (A.g k) sStep +
        ((1 : ℝ) / 2) * dotProduct sStep ((A.B k).mulVec sStep) := by
  simpa [TrustRegionSubproblem.coeFn_apply, subproblem] using
    (TrustRegionSubproblem.quadraticModel_eq (A.subproblem k) sStep)

/-- Expanding the packaged subproblem shows that its predicted reduction is `q^(k) 0 - q^(k) s_k`.
-/
theorem subproblem_predictedReduction_eq {f : Point → ℝ}
    (A : TrustRegionAlgorithm n f) (k : ℕ) :
    (A.subproblem k).predictedReduction (A.s k) =
      A.subproblem k 0 - A.subproblem k (A.s k) :=
  TrustRegionSubproblem.predictedReduction_eq (A.subproblem k) (A.s k)

/-- The scalar gradient norm `‖g_k‖` at stage `k`. -/
def gradientNormAt {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) : ℝ :=
  ‖A.g k‖

/-- Unfolding `A.gradientNormAt k` gives the source gradient norm `‖g_k‖`. -/
@[simp] theorem gradientNormAt_eq {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) :
    A.gradientNormAt k = ‖A.g k‖ :=
  rfl

/-- The stopping condition in the trust-region algorithm is `‖g k‖ ≤ ε`. -/
def terminatedAt {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) : Prop :=
  A.gradientNormAt k ≤ A.ε

/-- An iteration is active when the stopping test has not yet fired, i.e. `ε < ‖g k‖`. -/
def activeAt {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) : Prop :=
  A.ε < A.gradientNormAt k

/-- Expanding `activeAt` gives the active-iteration inequality used in Steps 3-6. -/
theorem activeAt_iff {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) :
    A.activeAt k ↔ A.ε < A.gradientNormAt k :=
  Iff.rfl

/-- At every active iteration, the trial step satisfies the canonical Step 3 approximate-solution
condition for the packaged trust-region subproblem. -/
theorem step_isApproximateSolution_of_activeAt
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ)
    (hk : A.activeAt k) : (A.subproblem k).isApproximateSolution A.β₂ (A.s k) :=
  A.step_isApproximateSolution k hk

/-- Lemma `6.1.5` implies that every active Step 3 iterate has strictly positive predicted
reduction for the canonical stage subproblem. -/
theorem predictedReduction_pos_of_activeAt
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ)
    (hk : A.activeAt k) : 0 < (A.subproblem k).predictedReduction (A.s k) := by
  have hgrad_pos : 0 < ‖(A.subproblem k).gradient‖ := by
    simpa [subproblem] using lt_of_le_of_lt A.epsilon_nonneg hk
  exact (A.subproblem k).predictedReduction_pos_of_isApproximateSolution
    A.β₂ (A.s k) A.beta2_mem hgrad_pos
    (A.step_isApproximateSolution_of_activeAt k hk)

/-- Every active Step 3 iterate is feasible for the canonical stage subproblem. -/
theorem step_feasible_of_activeAt
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ)
    (hk : A.activeAt k) : ‖A.s k‖ ≤ A.Δ k := by
  rcases (TrustRegionSubproblem.isApproximateSolution_iff
      (A.subproblem k) A.β₂ (A.s k)).1 (A.step_isApproximateSolution_of_activeAt k hk) with
    ⟨hfeasible, _⟩
  simpa [subproblem] using
    (TrustRegionSubproblem.mem_feasibleSet_iff (A.subproblem k) (A.s k)).1 hfeasible

/-- An iteration is successful when `η1 ≤ r k`, so the algorithm accepts the trial step. -/
def successfulAt {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) : Prop :=
  A.η1 ≤ A.r k

/-- An iteration is very successful when `η2 ≤ r k`. -/
def verySuccessfulAt {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) : Prop :=
  A.η2 ≤ A.r k

/-- An iteration is unsuccessful when `r k < η1`, so the algorithm rejects the trial step. -/
def unsuccessfulAt {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) : Prop :=
  A.r k < A.η1

/-- An iteration is active-successful when it is both active and successful. -/
def activeSuccessfulAt {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) : Prop :=
  A.activeAt k ∧ A.successfulAt k

/-- Expanding `activeSuccessfulAt` gives the active-and-successful condition on iteration `k`. -/
theorem activeSuccessfulAt_iff {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) :
    A.activeSuccessfulAt k ↔ A.activeAt k ∧ A.successfulAt k :=
  Iff.rfl

/-- Unfolding `A.nextRadiusSet k` gives the source piecewise admissible set for `Δ (k + 1)`. -/
theorem nextRadiusSet_eq {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ) :
    A.nextRadiusSet k =
      trustRegionRadiusUpdateSet A.η1 A.η2 A.γ1 A.γ2 A.ΔMax (A.Δ k) (A.r k) ‖A.s k‖ :=
  rfl

/-- On an active iteration with `r k < η1`, the radius-update rule records the source shrink
branch `Δ (k + 1) ∈ (0, γ1 * Δ k]`. -/
theorem radius_shrink {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ)
    (hk : A.activeAt k) (hr : A.r k < A.η1) :
    A.Δ (k + 1) ∈ Set.Ioc (0 : ℝ) (A.γ1 * A.Δ k) := by
  simpa [nextRadiusSet, trustRegionRadiusUpdateSet, hr] using A.radius_update k hk

/-- On an active iteration with `η1 ≤ r k < η2`, the radius-update rule records the source keep
branch `Δ (k + 1) ∈ [γ1 * Δ k, Δ k]`. -/
theorem radius_keep {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ)
    (hk : A.activeAt k) (hη1 : A.η1 ≤ A.r k) (hr : A.r k < A.η2) :
    A.Δ (k + 1) ∈ Set.Icc (A.γ1 * A.Δ k) (A.Δ k) := by
  have hnot_shrink : ¬ A.r k < A.η1 := not_lt.mpr hη1
  have hnot_expand : ¬ (A.η2 ≤ A.r k ∧ ‖A.s k‖ = A.Δ k) := by
    intro h
    exact not_lt_of_ge h.1 hr
  simpa [nextRadiusSet, trustRegionRadiusUpdateSet, hnot_shrink, hnot_expand] using
    A.radius_update k hk

/-- On an active iteration with `η2 ≤ r k` but `‖s k‖ < Δ k`, the source radius-update rule
still falls in the keep branch, so `Δ (k + 1) ∈ [γ1 * Δ k, Δ k]`. -/
theorem radius_keep_of_verySuccessfulInterior {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    (k : ℕ) (hk : A.activeAt k) (hη2 : A.η2 ≤ A.r k) (hInterior : ‖A.s k‖ < A.Δ k) :
    A.Δ (k + 1) ∈ Set.Icc (A.γ1 * A.Δ k) (A.Δ k) := by
  have hnot_shrink : ¬ A.r k < A.η1 := by
    exact not_lt.mpr (le_trans A.eta1_le_eta2 hη2)
  have hnot_expand : ¬ (A.η2 ≤ A.r k ∧ ‖A.s k‖ = A.Δ k) := by
    intro h
    exact ne_of_lt hInterior h.2
  simpa [nextRadiusSet, trustRegionRadiusUpdateSet, hnot_shrink, hnot_expand] using
    A.radius_update k hk

/-- On an active iteration with `η2 ≤ r k` and `‖s k‖ = Δ k`, the radius-update rule records the
source expansion branch `Δ (k + 1) ∈ [Δ k, min (γ2 * Δ k) ΔMax]`. -/
theorem radius_expand {f : Point → ℝ} (A : TrustRegionAlgorithm n f) (k : ℕ)
    (hk : A.activeAt k) (hη2 : A.η2 ≤ A.r k) (hBoundary : ‖A.s k‖ = A.Δ k) :
    A.Δ (k + 1) ∈ Set.Icc (A.Δ k) (min (A.γ2 * A.Δ k) A.ΔMax) := by
  have hnot_shrink : ¬ A.r k < A.η1 := by
    exact not_lt.mpr (le_trans A.eta1_le_eta2 hη2)
  simpa [nextRadiusSet, trustRegionRadiusUpdateSet, hnot_shrink, hη2, hBoundary] using
    A.radius_update k hk

/-- A trust-region algorithm has infinitely many successful iterations when the set of active
successful indices is infinite. -/
def hasInfinitelyManySuccessfulIterations {f : Point → ℝ}
    (A : TrustRegionAlgorithm n f) : Prop :=
  Set.Infinite {k : ℕ | A.activeSuccessfulAt k}

/-- Expanding `hasInfinitelyManySuccessfulIterations` gives the source quantification over the
successful active-iteration index set. -/
theorem hasInfinitelyManySuccessfulIterations_iff {f : Point → ℝ}
    (A : TrustRegionAlgorithm n f) :
    A.hasInfinitelyManySuccessfulIterations ↔
      Set.Infinite {k : ℕ | A.activeSuccessfulAt k} :=
  Iff.rfl

end TrustRegionAlgorithm

section Interpolation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Quadratic interpolation chooses
`λ = -(⟪gk, sk⟫) / (2 * (fTrial - fXk - ⟪gk, sk⟫))`. -/
def trustRegionQuadraticInterpolationFactor
    (gk sk : E) (fXk fTrial : ℝ) : ℝ :=
  -(inner ℝ gk sk) / (2 * (fTrial - fXk - inner ℝ gk sk))

/-- Expanding `trustRegionQuadraticInterpolationFactor` gives the source formula for `λ`. -/
theorem trustRegionQuadraticInterpolationFactor_eq
    (gk sk : E) (fXk fTrial : ℝ) :
    trustRegionQuadraticInterpolationFactor gk sk fXk fTrial =
      -(inner ℝ gk sk) / (2 * (fTrial - fXk - inner ℝ gk sk)) :=
  rfl

/-- After quadratic interpolation, the next trust-region
radius is `Δₖ₊₁ = trustRegionQuadraticInterpolationFactor gk sk fXk fTrial * ‖sk‖`. -/
def trustRegionQuadraticInterpolationRadius
    (gk sk : E) (fXk fTrial : ℝ) : ℝ :=
  trustRegionQuadraticInterpolationFactor gk sk fXk fTrial * ‖sk‖

/-- Expanding the interpolation radius gives the interpolation factor times `‖sk‖`. -/
theorem trustRegionQuadraticInterpolationRadius_eq
    (gk sk : E) (fXk fTrial : ℝ) :
    trustRegionQuadraticInterpolationRadius gk sk fXk fTrial =
      trustRegionQuadraticInterpolationFactor gk sk fXk fTrial * ‖sk‖ :=
  rfl

end Interpolation

end
