/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_4_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_4_6
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_3_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.ChosenPseudoInverse
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Lemma_5_7_6

open scoped BigOperators

noncomputable section

section Chapter10Definition105Extra1

variable {n m : ℕ}

-- Source/core/bridge triage:
-- * source-facing layer here: Fletcher's equality-constrained smooth exact penalty data and the
--   source theorems attached to `(10.5.3)`-`(10.5.5)`.
-- * reused canonical owners: `IsStrictLocalMinOn` from Chapter 8 together with its unconstrained
--   specialization `IsStrictLocalMin`, `isMinOn_univ_iff` for whole-space global minimizers, and
--   the Euclidean matrix action `Matrix.toEuclideanLin`.
-- * item-local foundation imports: `constraintJacobian`,
--   `isConstraintJacobianPseudoInverseField`, `fletcherMultiplierEstimate1023`,
--   `equalitySmoothExactPenaltyFunction`, `simpleSmoothExactPenaltyFunction`, and
--   `constantConstraintPoint`.
-- * local chapter-specific owners retained here: the equality-feasible set, linearized feasible
--   directions, and the labeled Fletcher source-facing declarations/theorems.

/-- Helper for Chapter10 Definition 10.5-extra-1: the equality-constraint Jacobian matrix whose
`i`th column is `∇ c_i(x)`. -/
def constraintJacobian
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin m) ℝ :=
  fun j i ↦ gradient (fun y : EuclideanSpace ℝ (Fin n) ↦ c y i) x j

/-- Helper for Chapter10 Definition 10.5-extra-1: evaluating `constraintJacobian c x` recovers
the matrix whose columns are the equality-constraint gradients at `x`. -/
theorem constraintJacobian_apply
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    constraintJacobian c x =
      fun j i ↦ gradient (fun y : EuclideanSpace ℝ (Fin n) ↦ c y i) x j := by
  -- The Jacobian owner is defined by this coordinate formula.
  rfl

/-- Helper for Chapter10 Definition 10.5-extra-1: `Aplus` is the chosen pseudoinverse field for
the equality-constraint Jacobian used in `(10.1.23)`. -/
abbrev isConstraintJacobianPseudoInverseField
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n), isChosenPseudoInverseAt (constraintJacobian c) Aplus x

/-- Helper for Chapter10 Definition 10.5-extra-1: the pseudoinverse-field owner unfolds to the
pointwise chosen-pseudoinverse condition. -/
theorem isConstraintJacobianPseudoInverseField_iff
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ) :
    isConstraintJacobianPseudoInverseField c Aplus ↔
      ∀ x : EuclideanSpace ℝ (Fin n),
        isChosenPseudoInverseAt (constraintJacobian c) Aplus x := by
  -- This is exactly the abbreviation defining the chosen pseudoinverse field.
  rfl

/-- Helper for Chapter10 Definition 10.5-extra-1: Fletcher's Section 10.1 multiplier estimate
`λ(x) = Aplus x (gradient f x)`. -/
def fletcherMultiplierEstimate1023
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin m) :=
  Matrix.toEuclideanLin (Aplus x) (gradient f x)

/-- Helper for Chapter10 Definition 10.5-extra-1: evaluating the multiplier owner recovers the
Section 10.1 formula `λ(x) = Aplus x (gradient f x)`. -/
theorem fletcherMultiplierEstimate1023_apply
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    fletcherMultiplierEstimate1023 f Aplus x =
      Matrix.toEuclideanLin (Aplus x) (gradient f x) := by
  -- The multiplier estimate owner is defined by the matrix action on `gradient f x`.
  rfl

/-- Helper for Chapter10 Definition 10.5-extra-1: the generic equality-constrained smooth exact
penalty formula attached to a multiplier map and diagonal penalty vector. -/
def equalitySmoothExactPenaltyFunction
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (σ : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x - dotProduct (multiplierEstimate x) (c x) +
    (1 / 2 : ℝ) * ∑ i : Fin m, σ i * (c x i) ^ (2 : ℕ)

/-- Helper for Chapter10 Definition 10.5-extra-1: evaluating the generic smooth exact penalty
unfolds to the explicit formula `(10.5.3)`. -/
theorem equalitySmoothExactPenaltyFunction_apply
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (σ : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    equalitySmoothExactPenaltyFunction f multiplierEstimate c σ x =
      f x - dotProduct (multiplierEstimate x) (c x) +
        (1 / 2 : ℝ) * ∑ i : Fin m, σ i * (c x i) ^ (2 : ℕ) := by
  -- The generic penalty owner is defined by this explicit expression.
  rfl

/-- Helper for Chapter10 Definition 10.5-extra-1: the constant diagonal penalty vector with every
entry equal to the same scalar `σ`. -/
def constantConstraintPoint (σ : ℝ) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (fun _ : Fin m ↦ σ)

/-- Helper for Chapter10 Definition 10.5-extra-1: `constantConstraintPoint σ` unfolds to the
constant penalty vector with value `σ` in every component. -/
theorem constantConstraintPoint_def (σ : ℝ) :
    constantConstraintPoint σ = WithLp.toLp 2 (fun _ : Fin m ↦ σ) := by
  -- The constant penalty vector owner is defined by this constant function.
  rfl

/-- Helper for Chapter10 Definition 10.5-extra-1: the simple equal-parameter smooth exact penalty
obtained by taking all diagonal entries equal to the same scalar `σ`. -/
def simpleSmoothExactPenaltyFunction
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (σ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x - dotProduct (multiplierEstimate x) (c x) + ((1 / 2 : ℝ) * σ) * ‖c x‖ ^ (2 : ℕ)

/-- Helper for Chapter10 Definition 10.5-extra-1: evaluating the simple equal-parameter penalty
unfolds to the source formula `(10.5.4)`. -/
theorem simpleSmoothExactPenaltyFunction_apply
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (σ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    simpleSmoothExactPenaltyFunction f multiplierEstimate c σ x =
      f x - dotProduct (multiplierEstimate x) (c x) +
        ((1 / 2 : ℝ) * σ) * ‖c x‖ ^ (2 : ℕ) := by
  -- The simple penalty owner is defined by this explicit formula.
  rfl

/-- The equality-feasible set `c(x) = 0` for an equality-constrained problem on `ℝ^n`. -/
def equalityFeasibleSet
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | c x = 0}

/-- Membership in `equalityFeasibleSet c` is exactly the source equality constraint `c x = 0`. -/
theorem mem_equalityFeasibleSet
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    x ∈ equalityFeasibleSet c ↔ c x = 0 := by
  -- The feasible set is defined by the equality constraint itself.
  rfl

/-- The equality-constrained linearized feasible-direction set at `xStar` consists of the
directions whose first-order variation annihilates each equality constraint. -/
def equalityLinearizedFeasibleDirectionSet
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {d | ∀ i : Fin m,
      dotProduct d
        ((@gradient ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ _
          (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) xStar)) = 0}

/-- Membership in `equalityLinearizedFeasibleDirectionSet c xStar` is exactly the vanishing of
each equality-constraint linearization at `xStar`. -/
theorem mem_equalityLinearizedFeasibleDirectionSet_iff
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar d : EuclideanSpace ℝ (Fin n)) :
    d ∈ equalityLinearizedFeasibleDirectionSet c xStar ↔
      ∀ i : Fin m,
        dotProduct d
          ((@gradient ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ _
            (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) xStar)) = 0 := by
  -- The linearized feasible-direction set was introduced by this exact predicate.
  rfl

/-- Helper for Chapter10 Definition 10.5-extra-1: the gradient of the `i`th equality
constraint at `xStar`. -/
def equalityConstraintGradient
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar : EuclideanSpace ℝ (Fin n)) (i : Fin m) :
    EuclideanSpace ℝ (Fin n) :=
  @gradient ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ _
    (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) xStar

/-- The equality-constrained Lagrangian at `xStar` attached to a chosen multiplier map. -/
def equalityLagrangian
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  f x - dotProduct (multiplierEstimate xStar) (c x)

/-- Evaluating `equalityLagrangian f multiplierEstimate c xStar x` unfolds to the source
equality-constrained Lagrangian formula. -/
theorem equalityLagrangian_apply
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar x : EuclideanSpace ℝ (Fin n)) :
    equalityLagrangian f multiplierEstimate c xStar x =
      f x - dotProduct (multiplierEstimate xStar) (c x) := by
  -- Unfold the owner once to recover the source Lagrangian formula.
  rfl

/-- The quadratic form `dᵀ ∇²_xx L(xStar, multiplierEstimate xStar) d` for the equality-constrained
Lagrangian attached to `f`, `c`, and a chosen multiplier map. -/
def equalityLagrangianHessianQuadratic
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar d : EuclideanSpace ℝ (Fin n)) : ℝ :=
  dotProduct d
    ((@gradient ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ _
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        dotProduct d
          ((@gradient ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ _
            (fun y : EuclideanSpace ℝ (Fin n) ↦
              equalityLagrangian f multiplierEstimate c xStar y) x)))
      xStar))

/-- Unfolding `equalityLagrangianHessianQuadratic` gives the source Hessian quadratic form of the
equality-constrained Lagrangian. -/
theorem equalityLagrangianHessianQuadratic_eq
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar d : EuclideanSpace ℝ (Fin n)) :
    equalityLagrangianHessianQuadratic f multiplierEstimate c xStar d =
      dotProduct d
        ((@gradient ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ _
          (fun x : EuclideanSpace ℝ (Fin n) ↦
            dotProduct d
              ((@gradient ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ _
                (fun y : EuclideanSpace ℝ (Fin n) ↦
                  equalityLagrangian f multiplierEstimate c xStar y) x)))
          xStar)) := by
  -- This theorem is just the definitional expansion of the quadratic-form owner.
  rfl

/-- `SecondOrderSufficientCondition f multiplierEstimate c xStar` is the equality-constrained
Chapter 10 second-order sufficient condition at `xStar` for a fixed multiplier map:
`xStar` is feasible, the corresponding Lagrangian is stationary at `xStar`, `f` and each
component of `c` are `C²` at `xStar`, and the Lagrangian Hessian quadratic form is positive on
every nonzero linearized feasible direction. -/
def SecondOrderSufficientCondition
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar : EuclideanSpace ℝ (Fin n)) : Prop :=
  xStar ∈ equalityFeasibleSet c ∧
    (@gradient ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ _
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        equalityLagrangian f multiplierEstimate c xStar x) xStar) = 0 ∧
      ContDiffAt ℝ 2 f xStar ∧
        (∀ i : Fin m,
          ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) xStar) ∧
        ∀ d ∈ equalityLinearizedFeasibleDirectionSet c xStar,
          d ≠ 0 → 0 < equalityLagrangianHessianQuadratic f multiplierEstimate c xStar d

/-- Unfolding `SecondOrderSufficientCondition f multiplierEstimate c xStar` gives the explicit
equality-constrained Chapter 10 second-order sufficient condition. -/
theorem secondOrderSufficientCondition_iff
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar : EuclideanSpace ℝ (Fin n)) :
    SecondOrderSufficientCondition f multiplierEstimate c xStar ↔
      xStar ∈ equalityFeasibleSet c ∧
        (@gradient ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ _
          (fun x : EuclideanSpace ℝ (Fin n) ↦
            equalityLagrangian f multiplierEstimate c xStar x) xStar) = 0 ∧
          ContDiffAt ℝ 2 f xStar ∧
            (∀ i : Fin m,
              ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) xStar) ∧
            ∀ d ∈ equalityLinearizedFeasibleDirectionSet c xStar,
              d ≠ 0 →
                0 < equalityLagrangianHessianQuadratic f multiplierEstimate c xStar d := by
  -- The packaged SOSC proposition unfolds to the textbook list of hypotheses.
  rfl

namespace equalitySmoothExactPenaltyFunction

/-- On the equality-feasible set `c x = 0`, `equalitySmoothExactPenaltyFunction` agrees with the
original objective `f`. -/
theorem eq_objective
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (σ : EuclideanSpace ℝ (Fin m))
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ equalityFeasibleSet c) :
    equalitySmoothExactPenaltyFunction f multiplierEstimate c σ x = f x := by
  -- Feasibility kills both the multiplier term and the quadratic penalty term.
  have hc : c x = 0 := (mem_equalityFeasibleSet c x).mp hx
  rw [equalitySmoothExactPenaltyFunction_apply]
  simp [hc]

end equalitySmoothExactPenaltyFunction

/-- Fletcher's equality-constrained smooth exact penalty from
Chapter10 Definition 10.5-extra-1 is
function `(10.5.3)` is
`x ↦ f x - dotProduct (fletcherMultiplierEstimate1023 f Aplus x) (c x) +
  (1 / 2) * ∑ i, σ i * (c x i)^2`,
where the source theorems additionally assume that `Aplus` is the chosen pseudoinverse field for
the equality-constraint Jacobian used in the Section 10.1 multiplier estimate `(10.1.23)`, and
`σ` records the diagonal entries of `D = diag(σ₁, ..., σ_m)`. -/
def fletcherEqualitySmoothExactPenaltyFunction
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (σ : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  equalitySmoothExactPenaltyFunction f (fletcherMultiplierEstimate1023 f Aplus) c σ

/-- Evaluating `fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ x` unfolds the
source formula `(10.5.3)` with `λ(x)` specialized to `(10.1.23)`. -/
theorem fletcherEqualitySmoothExactPenaltyFunction_apply
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (σ : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) :
    fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ x =
      f x - dotProduct (fletcherMultiplierEstimate1023 f Aplus x) (c x) +
        (1 / 2 : ℝ) * ∑ i : Fin m, σ i * (c x i) ^ (2 : ℕ) := by
  -- The Fletcher owner is the generic equality penalty with the Section 10.1 multiplier field.
  simpa [fletcherEqualitySmoothExactPenaltyFunction] using
    (equalitySmoothExactPenaltyFunction_apply
      f (fletcherMultiplierEstimate1023 f Aplus) c σ x)

/-- If all diagonal entries `σᵢ` in `(10.5.3)` are equal
to the same scalar `σ`, Fletcher's simple smooth exact penalty function `(10.5.4)` is
`x ↦ f x - dotProduct (fletcherMultiplierEstimate1023 f Aplus x) (c x) +
  (1 / 2) * σ * ‖c x‖^2`,
where the source theorems additionally assume that `Aplus` is the chosen pseudoinverse field for
the equality-constraint Jacobian used in `(10.1.23)`. -/
def fletcherSimpleSmoothExactPenaltyFunction
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (σ : ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  simpleSmoothExactPenaltyFunction f (fletcherMultiplierEstimate1023 f Aplus) c σ

/-- Evaluating `fletcherSimpleSmoothExactPenaltyFunction f c Aplus σ x` unfolds the
source formula `(10.5.4)` with `λ(x)` specialized to `(10.1.23)`. -/
theorem fletcherSimpleSmoothExactPenaltyFunction_apply
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (σ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    fletcherSimpleSmoothExactPenaltyFunction f c Aplus σ x =
      f x - dotProduct (fletcherMultiplierEstimate1023 f Aplus x) (c x) +
        ((1 / 2 : ℝ) * σ) * ‖c x‖ ^ (2 : ℕ) := by
  -- The simple Fletcher owner is the equal-parameter specialization of the generic owner.
  simpa [fletcherSimpleSmoothExactPenaltyFunction] using
    (simpleSmoothExactPenaltyFunction_apply
      f (fletcherMultiplierEstimate1023 f Aplus) c σ x)

/-- Helper for Chapter10 Definition 10.5-extra-1: strict local minimality transfers across an
eventual lower bound when the two objectives agree at the base point. -/
lemma isStrictLocalMin_of_eq_at_base_of_eventually_ge
    {X : Type*} [TopologicalSpace X]
    {F G : X → ℝ} {xStar : X}
    (hG : IsStrictLocalMin G xStar)
    (hEq : F xStar = G xStar)
    (hGe : ∀ᶠ x in nhdsWithin xStar {xStar}ᶜ, G x ≤ F x) :
    IsStrictLocalMin F xStar := by
  -- Intersect the strict inequality for `G` with the eventual comparison `G ≤ F`.
  filter_upwards [hG, hGe] with x hxG hxGe
  calc
    F xStar = G xStar := hEq
    _ < G x := hxG
    _ ≤ F x := hxGe

/-- Helper for Chapter10 Definition 10.5-extra-1: once the diagonal penalty dominates
`τ + 2K` componentwise, the full Fletcher penalty eventually dominates the frozen-multiplier
scalar penalty near `xStar`. -/
lemma eventually_fletcherEqualityPenalty_ge_frozenSimplePenalty
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (xStar : EuclideanSpace ℝ (Fin n))
    (τ K : ℝ)
    (σ : EuclideanSpace ℝ (Fin m))
    (hσ : ∀ i : Fin m, τ + 2 * K ≤ σ i)
    (h_multiplierQuadratic :
      ∀ᶠ x in nhds xStar,
        ‖dotProduct
            (fletcherMultiplierEstimate1023 f Aplus x -
              fletcherMultiplierEstimate1023 f Aplus xStar)
            (c x)‖ ≤ K * ‖c x‖ ^ (2 : ℕ)) :
    ∀ᶠ x in nhdsWithin xStar {xStar}ᶜ,
      (f x - dotProduct (fletcherMultiplierEstimate1023 f Aplus xStar) (c x) +
          ((1 / 2 : ℝ) * τ) * ‖c x‖ ^ (2 : ℕ)) ≤
        fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ x := by
  have hCompareNhds :
      ∀ᶠ x in nhds xStar,
        (f x - dotProduct (fletcherMultiplierEstimate1023 f Aplus xStar) (c x) +
            ((1 / 2 : ℝ) * τ) * ‖c x‖ ^ (2 : ℕ)) ≤
          fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ x := by
    -- At each nearby point, the extra diagonal penalty absorbs the multiplier-variation error.
    filter_upwards [h_multiplierQuadratic] with x hx
    have hxabs :
        |dotProduct
            (fletcherMultiplierEstimate1023 f Aplus x -
              fletcherMultiplierEstimate1023 f Aplus xStar)
            (c x)| ≤ K * ‖c x‖ ^ (2 : ℕ) := by
      simpa using hx
    have hdotUpper :
        dotProduct
            (fletcherMultiplierEstimate1023 f Aplus x -
              fletcherMultiplierEstimate1023 f Aplus xStar)
            (c x) ≤ K * ‖c x‖ ^ (2 : ℕ) :=
      (abs_le.mp hxabs).2
    have hcoeff :
        ∀ i : Fin m, 2 * K ≤ σ i - τ := by
      intro i
      linarith [hσ i]
    have hsum :
        (2 * K) * ∑ i : Fin m, (c x i) ^ (2 : ℕ) ≤
          ∑ i : Fin m, (σ i - τ) * (c x i) ^ (2 : ℕ) := by
      calc
        (2 * K) * ∑ i : Fin m, (c x i) ^ (2 : ℕ) =
            ∑ i : Fin m, (2 * K) * (c x i) ^ (2 : ℕ) := by
              rw [Finset.mul_sum]
        _ ≤ ∑ i : Fin m, (σ i - τ) * (c x i) ^ (2 : ℕ) := by
          refine Finset.sum_le_sum ?_
          intro i _
          exact mul_le_mul_of_nonneg_right (hcoeff i) (sq_nonneg (c x i))
    have hpenalty :
        K * ‖c x‖ ^ (2 : ℕ) ≤
          (1 / 2 : ℝ) * ∑ i : Fin m, (σ i - τ) * (c x i) ^ (2 : ℕ) := by
      have hsum' :
          (2 * K) * ‖c x‖ ^ (2 : ℕ) ≤
            ∑ i : Fin m, (σ i - τ) * (c x i) ^ (2 : ℕ) := by
        simpa [EuclideanSpace.real_norm_sq_eq] using hsum
      nlinarith
    have hdotExpand :
        dotProduct (fletcherMultiplierEstimate1023 f Aplus x) (c x) =
          dotProduct (fletcherMultiplierEstimate1023 f Aplus xStar) (c x) +
            dotProduct
              (fletcherMultiplierEstimate1023 f Aplus x -
                fletcherMultiplierEstimate1023 f Aplus xStar)
              (c x) := by
      have hsub :
          dotProduct
              (fletcherMultiplierEstimate1023 f Aplus x -
                fletcherMultiplierEstimate1023 f Aplus xStar)
              (c x) =
            dotProduct (fletcherMultiplierEstimate1023 f Aplus x) (c x) -
              dotProduct (fletcherMultiplierEstimate1023 f Aplus xStar) (c x) := by
        exact
          sub_dotProduct
            (fletcherMultiplierEstimate1023 f Aplus x)
            (fletcherMultiplierEstimate1023 f Aplus xStar)
            (c x)
      rw [hsub]
      ring
    have hdiagExpand :
        (1 / 2 : ℝ) * ∑ i : Fin m, σ i * (c x i) ^ (2 : ℕ) =
          ((1 / 2 : ℝ) * τ) * ‖c x‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) * ∑ i : Fin m, (σ i - τ) * (c x i) ^ (2 : ℕ) := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc
        (1 / 2 : ℝ) * ∑ i : Fin m, σ i * (c x i) ^ (2 : ℕ) =
            (1 / 2 : ℝ) *
              ∑ i : Fin m, (τ * (c x i) ^ (2 : ℕ) + (σ i - τ) * (c x i) ^ (2 : ℕ)) := by
                congr 1
                refine Finset.sum_congr rfl ?_
                intro i _
                ring
        _ = (1 / 2 : ℝ) *
              (τ * ∑ i : Fin m, (c x i) ^ (2 : ℕ) +
                ∑ i : Fin m, (σ i - τ) * (c x i) ^ (2 : ℕ)) := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ = ((1 / 2 : ℝ) * τ) * ∑ i : Fin m, (c x i) ^ (2 : ℕ) +
              (1 / 2 : ℝ) * ∑ i : Fin m, (σ i - τ) * (c x i) ^ (2 : ℕ) := by
              ring
    -- After normalizing both the multiplier term and the diagonal penalty, linear arithmetic
    -- closes the comparison.
    rw [fletcherEqualitySmoothExactPenaltyFunction_apply, hdotExpand, hdiagExpand]
    linarith
  -- Restrict the neighborhood comparison to the punctured neighborhood used by `IsStrictLocalMin`.
  simpa using hCompareNhds.filter_mono nhdsWithin_le_nhds

/-- Helper for Chapter10 Definition 10.5-extra-1: the frozen equality Lagrangian is `C²` at
`xStar` as soon as the objective and each equality constraint are `C²` there. -/
lemma equalityLagrangian_contDiffAt
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar : EuclideanSpace ℝ (Fin n))
    (hF : ContDiffAt ℝ 2 f xStar)
    (hC : ∀ i : Fin m,
      ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) xStar) :
    ContDiffAt ℝ 2
      (fun x : EuclideanSpace ℝ (Fin n) ↦
        equalityLagrangian f multiplierEstimate c xStar x)
      xStar := by
  -- Expand the frozen multiplier term into a finite sum of scalar equality constraints.
  have hMultiplier :
      ContDiffAt ℝ 2
        (fun x : EuclideanSpace ℝ (Fin n) ↦
          ∑ i : Fin m, multiplierEstimate xStar i * c x i)
        xStar := by
    refine ContDiffAt.sum ?_
    intro i _
    exact contDiffAt_const.mul (hC i)
  simpa [equalityLagrangian, dotProduct] using hF.sub hMultiplier

/-- Helper for Chapter10 Definition 10.5-extra-1: on real Euclidean space, `dotProduct u v`
is the inner product with the right slot fixed at `u`. -/
lemma dotProduct_eq_inner_right
    (u v : EuclideanSpace ℝ (Fin n)) :
    dotProduct u v = inner ℝ v u := by
  -- Normalize the coordinate `dotProduct` owner to the canonical inner-product owner once.
  simpa using (EuclideanSpace.inner_eq_star_dotProduct v u).symm

/-- Helper for Chapter10 Definition 10.5-extra-1: the source Hessian quadratic owner for the
frozen equality Lagrangian agrees with the canonical Hessian quadratic form at a `C²` point. -/
lemma equalityLagrangianHessianQuadratic_eq_hessianQuadraticAt
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (multiplierEstimate :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar d : EuclideanSpace ℝ (Fin n))
    (hC2 :
      ContDiffAt ℝ 2
        (fun x : EuclideanSpace ℝ (Fin n) ↦
          equalityLagrangian f multiplierEstimate c xStar x)
        xStar) :
    equalityLagrangianHessianQuadratic f multiplierEstimate c xStar d =
      hessianQuadraticAt
        (fun x : EuclideanSpace ℝ (Fin n) ↦
          equalityLagrangian f multiplierEstimate c xStar x)
        xStar d := by
  let L : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    equalityLagrangian f multiplierEstimate c xStar x
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    dotProduct d ((@gradient ℝ (EuclideanSpace ℝ (Fin n)) _ _ _ _ L x))
  have hq_eq : q = fun x : EuclideanSpace ℝ (Fin n) ↦ (fderiv ℝ L x) d := by
    -- Route correction: rewrite the nested scalar owner through the first derivative of `L`.
    funext x
    dsimp [q]
    rw [dotProduct_eq_inner_right]
    exact inner_gradient_left (f := L) (x := x) (y := d)
  have hfd_eval :
      HasFDerivAt (fun x : EuclideanSpace ℝ (Fin n) ↦ (fderiv ℝ L x) d)
        (((ContinuousLinearMap.apply ℝ ℝ) d).comp (fderiv ℝ (fderiv ℝ L) xStar)) xStar := by
    -- Differentiate the evaluation map after the first-derivative field of `L`.
    exact (((ContinuousLinearMap.apply ℝ ℝ) d).hasFDerivAt.comp xStar
      (((hC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt))
  calc
    equalityLagrangianHessianQuadratic f multiplierEstimate c xStar d
        = (fderiv ℝ q xStar) d := by
          -- The source quadratic owner is the directional derivative of the scalar field `q`.
          dsimp [q, L, equalityLagrangianHessianQuadratic]
          rw [dotProduct_eq_inner_right]
          exact inner_gradient_left (f := q) (x := xStar) (y := d)
    _ = (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) ↦ (fderiv ℝ L x) d) xStar) d := by
          -- Replace the nested-gradient spelling by the first-derivative spelling from `hq_eq`.
          rw [hq_eq]
    _ = ((fderiv ℝ (fderiv ℝ L) xStar) d) d := by
          -- Evaluating the derivative of the derivative field peels off one linear slot.
          simp [hfd_eval.fderiv, ContinuousLinearMap.comp_apply]
    _ = (iteratedFDeriv ℝ 2 L xStar) ![d, d] := by
          -- `iteratedFDeriv ℝ 2` is the canonical owner for the second directional derivative.
          symm
          exact iteratedFDeriv_two_apply L xStar ![d, d]
    _ = hessianQuadraticAt L xStar d := by
          -- Finally return from the Chapter 1 owner to the canonical Hessian quadratic owner.
          symm
          exact inner_hessianAt_apply_eq_iteratedFDeriv_of_contDiffAt (f := L) hC2

/-- Helper for Chapter10 Definition 10.5-extra-1: the scalar penalty term
`x ↦ (1 / 2) * ‖c x‖²` is `C²` at `xStar` when every scalar constraint component is `C²`
there. -/
lemma halfNormSqPenalty_contDiffAt
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar : EuclideanSpace ℝ (Fin n))
    (hC : ∀ i : Fin m,
      ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) xStar) :
    ContDiffAt ℝ 2
      (fun x : EuclideanSpace ℝ (Fin n) ↦ ((1 / 2 : ℝ) * ‖c x‖ ^ (2 : ℕ)))
      xStar := by
  -- Expand the scalar penalty into a finite sum of squared equality constraints.
  have hsum :
      ContDiffAt ℝ 2
        (fun x : EuclideanSpace ℝ (Fin n) ↦
          ∑ i : Fin m, (c x i) ^ (2 : ℕ))
        xStar := by
    refine ContDiffAt.sum ?_
    intro i _
    simpa [pow_two] using (hC i).mul (hC i)
  simpa [EuclideanSpace.real_norm_sq_eq] using
    (show ContDiffAt ℝ 2
      (fun x : EuclideanSpace ℝ (Fin n) ↦ ((1 / 2 : ℝ) * ∑ i : Fin m, (c x i) ^ (2 : ℕ)))
      xStar from contDiffAt_const.mul hsum)

/-- Helper for Chapter10 Definition 10.5-extra-1: along a scalar `C²` profile vanishing at the
base point, the second derivative of the half-square is the square of the first derivative. -/
lemma deriv2_halfSquare_eq_sq_deriv_of_zero
    {g : ℝ → ℝ}
    (hg0 : g 0 = 0)
    (hC2 : ContDiffAt ℝ 2 g 0) :
    (deriv^[2]) (fun t : ℝ ↦ ((1 / 2 : ℝ) * (g t) ^ (2 : ℕ))) 0 =
      (deriv g 0) ^ (2 : ℕ) := by
  let F : ℝ → ℝ := fun s ↦ ((1 / 2 : ℝ) * s ^ (2 : ℕ))
  have hF2 : ContDiffAt ℝ 2 F (g 0) := by
    -- The outer half-square profile is polynomial, so the composition formula applies at `g 0`.
    fun_prop
  have hFDeriv :
      HasDerivAt F (g 0) (g 0) := by
    -- The first derivative of `(1 / 2) * s²` is `s`.
    have hRaw :
        HasDerivAt F (((1 / 2 : ℝ) * (g 0 + g 0))) (g 0) := by
      simpa [F, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (((hasDerivAt_id (g 0)).mul (hasDerivAt_id (g 0))).const_mul (1 / 2 : ℝ))
    convert hRaw using 1
    ring
  have hFSecond :
      iteratedDeriv 2 F (g 0) = 1 := by
    -- The outer half-square has constant second derivative `1`.
    rw [iteratedDeriv_eq_iterate]
    convert deriv2_half_mul_sq (1 : ℝ) (g 0) using 1
  rw [← iteratedDeriv_eq_iterate]
  calc
    iteratedDeriv 2 (fun t : ℝ ↦ ((1 / 2 : ℝ) * (g t) ^ (2 : ℕ))) 0
        = iteratedDeriv 2 (F ∘ g) 0 := by
            rfl
    _ = (iteratedFDeriv ℝ 2 F (g 0)) (fun _ : Fin 2 ↦ deriv g 0) +
          fderiv ℝ F (g 0) (iteratedDeriv 2 g 0) := by
            -- Route correction: use the one-dimensional composition formula instead of reopening
            -- the multivariable Hessian transport for the half-square term.
            simpa [F, Function.comp] using iteratedDeriv_vcomp_two (g := F) (f := g) hF2 hC2
    _ = (deriv g 0) ^ (2 : ℕ) + 0 := by
          congr 1
          · -- Multilinearity of the outer second derivative turns the constant direction into a
            -- square factor.
            calc
              (iteratedFDeriv ℝ 2 F (g 0)) (fun _ : Fin 2 ↦ deriv g 0)
                  = (∏ _ : Fin 2, deriv g 0) * iteratedDeriv 2 F (g 0) := by
                      simpa [smul_eq_mul] using
                        (iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod
                          (𝕜 := ℝ) (n := 2) (f := F) (x := g 0)
                          (m := fun _ : Fin 2 ↦ deriv g 0))
              _ = (deriv g 0) ^ (2 : ℕ) := by
                    rw [hFSecond]
                    simp [pow_two]
          · -- The mixed composition term vanishes because `g 0 = 0`.
            rw [fderiv_eq_deriv_mul, hFDeriv.deriv, hg0]
            simp
    _ = (deriv g 0) ^ (2 : ℕ) := by
          simp

/-- Helper for Chapter10 Definition 10.5-extra-1: the derivative of the `i`th equality
constraint along the affine line `xStar + t • d` is the gradient pairing with `d`. -/
lemma deriv_lineConstraintComponent_eq_dotGradient
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar d : EuclideanSpace ℝ (Fin n))
    (i : Fin m)
    (hC : ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) xStar) :
    deriv (fun t : ℝ ↦ c (xStar + t • d) i) 0 =
      dotProduct d (equalityConstraintGradient c xStar i) := by
  let φ : ℝ → EuclideanSpace ℝ (Fin n) := AffineMap.lineMap xStar (xStar + d)
  have hLine :
      HasDerivAt φ d 0 := by
    -- The affine line through `xStar` with endpoint `xStar + d` has constant derivative `d`.
    simpa [φ, AffineMap.lineMap_apply_module', sub_eq_add_neg, add_assoc, add_comm,
      add_left_comm] using
      (AffineMap.hasDerivAt_lineMap (a := xStar) (b := xStar + d) (x := 0))
  have hComp :
      HasDerivAt (fun t : ℝ ↦ c (φ t) i)
        (inner ℝ (equalityConstraintGradient c xStar i) d) 0 := by
    have hGrad :
        HasGradientAt (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i)
          (equalityConstraintGradient c xStar i) xStar :=
      (hC.differentiableAt (by norm_num)).hasGradientAt
    -- Compose the scalar constraint component with the affine trace through `xStar`.
    change HasDerivAt ((fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) ∘ φ)
      (inner ℝ (equalityConstraintGradient c xStar i) d) 0
    simpa [φ] using
      (hGrad.hasFDerivAt.comp_hasDerivAt_of_eq
        (hf := hLine) (hy := (AffineMap.lineMap_apply_zero xStar (xStar + d)).symm))
  -- Read the line derivative as the coordinate `dotProduct` pairing used in the linearized
  -- feasibility owner.
  simpa [dotProduct_eq_inner_right, φ, AffineMap.lineMap_apply_module', sub_eq_add_neg,
    add_assoc, add_comm, add_left_comm] using hComp.deriv

/-- Helper for Chapter10 Definition 10.5-extra-1: at a feasible point, the scalar penalty term
contributes exactly the squared linearized equality-constraint violations to the Hessian
quadratic form. -/
lemma hessianQuadraticAt_halfNormSqPenalty_eq_sumSquares
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (xStar d : EuclideanSpace ℝ (Fin n))
    (hcStar : c xStar = 0)
    (hC : ∀ i : Fin m,
      ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) xStar) :
    hessianQuadraticAt
      (fun x : EuclideanSpace ℝ (Fin n) ↦ ((1 / 2 : ℝ) * ‖c x‖ ^ (2 : ℕ)))
      xStar d =
      ∑ i : Fin m,
        (dotProduct d
          (equalityConstraintGradient c xStar i)) ^ (2 : ℕ) := by
  let penalty : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ ((1 / 2 : ℝ) * ‖c x‖ ^ (2 : ℕ))
  let φ : ℝ → EuclideanSpace ℝ (Fin n) := AffineMap.lineMap xStar (xStar + d)
  let I : Set ℝ := {0}
  have hPenaltyC2 : ContDiffAt ℝ 2 penalty xStar :=
    halfNormSqPenalty_contDiffAt c xStar hC
  rcases hPenaltyC2.contDiffOn' (m := 2) le_rfl (by simp) with
    ⟨u, hu_open, hxu, hPenaltyOn_raw⟩
  have hPenaltyOn : ContDiffOn ℝ 2 penalty u := by
    simpa using hPenaltyOn_raw
  have h0I : (0 : ℝ) ∈ I := by
    simp [I]
  have hmem : ∀ t ∈ I, φ t ∈ u := by
    intro t ht
    have ht0 : t = 0 := by
      simpa [I] using ht
    simpa [φ, ht0] using hxu
  have hLinePenalty :
      (deriv^[2]) (fun t : ℝ ↦ penalty (φ t)) 0 =
        (iteratedFDeriv ℝ 2 penalty xStar) ![d, d] := by
    -- The line restriction reduces the multivariable Hessian diagonal to a scalar second
    -- derivative at the base point.
    simpa [penalty, φ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_module',
      sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      deriv2_lineMap_eq_iteratedFDeriv_diag hu_open hPenaltyOn hmem h0I
  have hTermC2 :
      ∀ i : Fin m,
        ContDiffAt ℝ 2 (fun t : ℝ ↦ ((1 / 2 : ℝ) * (c (φ t) i) ^ (2 : ℕ))) 0 := by
    intro i
    have hLineC2 : ContDiffAt ℝ 2 (fun t : ℝ ↦ c (φ t) i) 0 := by
      have hCiAt : ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) (φ 0) := by
        simpa [φ, AffineMap.lineMap_apply_zero] using hC i
      have hφC2 : ContDiffAt ℝ 2 φ 0 := by
        simpa [φ] using
          (AffineMap.contDiff_lineMap xStar (xStar + d) : ContDiff ℝ 2 φ).contDiffAt
      -- Each scalar constraint component stays `C²` along the affine trace.
      exact ContDiffAt.comp 0 hCiAt hφC2
    simpa [pow_two] using contDiffAt_const.mul (hLineC2.mul hLineC2)
  have hPenaltyTraceEq :
      (fun t : ℝ ↦ penalty (φ t)) =
        fun t : ℝ ↦
          ∑ i : Fin m, ((1 / 2 : ℝ) * (c (φ t) i) ^ (2 : ℕ)) := by
    funext t
    simp [penalty, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  have hLineExpand :
      (deriv^[2]) (fun t : ℝ ↦ penalty (φ t)) 0 =
        ∑ i : Fin m,
          (deriv^[2]) (fun t : ℝ ↦ ((1 / 2 : ℝ) * (c (φ t) i) ^ (2 : ℕ))) 0 := by
    -- Expand the squared norm into a finite sum of scalar half-squares before differentiating.
    rw [← iteratedDeriv_eq_iterate]
    calc
      iteratedDeriv 2 (fun t : ℝ ↦ penalty (φ t)) 0
          = iteratedDeriv 2
              (fun t : ℝ ↦
                ∑ i : Fin m, ((1 / 2 : ℝ) * (c (φ t) i) ^ (2 : ℕ))) 0 := by
              rw [hPenaltyTraceEq]
      _ = ∑ i : Fin m,
            iteratedDeriv 2 (fun t : ℝ ↦ ((1 / 2 : ℝ) * (c (φ t) i) ^ (2 : ℕ))) 0 := by
            have hSumDeriv :
                iteratedDeriv 2
                    (∑ i : Fin m, fun t : ℝ ↦ ((1 / 2 : ℝ) * (c (φ t) i) ^ (2 : ℕ))) 0 =
                  ∑ i : Fin m,
                    iteratedDeriv 2 (fun t : ℝ ↦ ((1 / 2 : ℝ) * (c (φ t) i) ^ (2 : ℕ))) 0 :=
              iteratedDeriv_sum (fun i _ ↦ hTermC2 i)
            convert hSumDeriv using 1
            congr 1
            funext t
            simp
      _ = ∑ i : Fin m,
            (deriv^[2]) (fun t : ℝ ↦ ((1 / 2 : ℝ) * (c (φ t) i) ^ (2 : ℕ))) 0 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [iteratedDeriv_eq_iterate]
  have hTermEq :
      ∀ i : Fin m,
        (deriv^[2]) (fun t : ℝ ↦ ((1 / 2 : ℝ) * (c (φ t) i) ^ (2 : ℕ))) 0 =
          (dotProduct d (equalityConstraintGradient c xStar i)) ^ (2 : ℕ) := by
    intro i
    have hcStar_i : c xStar i = 0 := by
      simpa using congrArg (fun v : EuclideanSpace ℝ (Fin m) ↦ v i) hcStar
    have hLineC2 : ContDiffAt ℝ 2 (fun t : ℝ ↦ c (φ t) i) 0 := by
      have hCiAt : ContDiffAt ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) ↦ c x i) (φ 0) := by
        simpa [φ, AffineMap.lineMap_apply_zero] using hC i
      have hφC2 : ContDiffAt ℝ 2 φ 0 := by
        simpa [φ] using
          (AffineMap.contDiff_lineMap xStar (xStar + d) : ContDiff ℝ 2 φ).contDiffAt
      -- The scalar line restriction inherits the local `C²` regularity of `c_i`.
      exact ContDiffAt.comp 0 hCiAt hφC2
    -- Feasibility kills the mixed term, leaving only the squared directional derivative.
    rw [deriv2_halfSquare_eq_sq_deriv_of_zero
      (g := fun t : ℝ ↦ c (φ t) i)
      (by simpa [φ, AffineMap.lineMap_apply_zero] using hcStar_i)
      hLineC2]
    exact congrArg (fun z : ℝ ↦ z ^ (2 : ℕ)) <|
      (by
        simpa [φ, AffineMap.lineMap_apply_module', sub_eq_add_neg, add_assoc, add_comm,
          add_left_comm] using
          deriv_lineConstraintComponent_eq_dotGradient c xStar d i (hC i))
  calc
    hessianQuadraticAt penalty xStar d = (iteratedFDeriv ℝ 2 penalty xStar) ![d, d] := by
      -- Return to the canonical Hessian owner at the base point.
      exact ConstrainedOptimizationProblem.hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt
        (f := penalty) (x := xStar) (y := d) hPenaltyC2
    _ = (deriv^[2]) (fun t : ℝ ↦ penalty (φ t)) 0 := by
      exact hLinePenalty.symm
    _ = ∑ i : Fin m,
          (deriv^[2]) (fun t : ℝ ↦ ((1 / 2 : ℝ) * (c (φ t) i) ^ (2 : ℕ))) 0 := by
            exact hLineExpand
    _ = ∑ i : Fin m,
          (dotProduct d (equalityConstraintGradient c xStar i)) ^ (2 : ℕ) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact hTermEq i

/-- Helper for Chapter10 Definition 10.5-extra-1: a sufficiently large scalar penalty shift
makes the frozen equality-penalty Hessian positive on every unit direction. -/
lemma exists_penaltyShift_pos_on_unitSphere_of_sosc
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (xStar : EuclideanSpace ℝ (Fin n))
    (h_sosc :
      SecondOrderSufficientCondition f (fletcherMultiplierEstimate1023 f Aplus) c xStar)
    [Nontrivial (EuclideanSpace ℝ (Fin n))] :
    ∃ τ : ℝ, 0 ≤ τ ∧
      ∀ d : EuclideanSpace ℝ (Fin n), ‖d‖ = 1 →
        0 <
          equalityLagrangianHessianQuadratic
            f (fletcherMultiplierEstimate1023 f Aplus) c xStar d +
          τ * ∑ i : Fin m,
            (dotProduct d
              (equalityConstraintGradient c xStar i)) ^ (2 : ℕ) := by
  classical
  let L : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    equalityLagrangian f (fletcherMultiplierEstimate1023 f Aplus) c xStar x
  let q : EuclideanSpace ℝ (Fin n) → ℝ := fun d ↦ hessianQuadraticAt L xStar d
  let p : EuclideanSpace ℝ (Fin n) → ℝ := fun d ↦
    ∑ i : Fin m, (dotProduct d (equalityConstraintGradient c xStar i)) ^ (2 : ℕ)
  let K : Set (EuclideanSpace ℝ (Fin n)) :=
    Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ∩ {d | q d ≤ 0}
  have h_sosc' := (secondOrderSufficientCondition_iff
    f (fletcherMultiplierEstimate1023 f Aplus) c xStar).mp h_sosc
  have hxStarFeasible : xStar ∈ equalityFeasibleSet c := h_sosc'.1
  have hcStar : c xStar = 0 := (mem_equalityFeasibleSet c xStar).mp hxStarFeasible
  have hLC2 :
      ContDiffAt ℝ 2 L xStar :=
    equalityLagrangian_contDiffAt f (fletcherMultiplierEstimate1023 f Aplus) c xStar
      h_sosc'.2.2.1 h_sosc'.2.2.2.1
  have hLagEq :
      ∀ d : EuclideanSpace ℝ (Fin n),
        equalityLagrangianHessianQuadratic f (fletcherMultiplierEstimate1023 f Aplus) c xStar d =
          q d := by
    intro d
    simpa [q, L] using
      equalityLagrangianHessianQuadratic_eq_hessianQuadraticAt
        f (fletcherMultiplierEstimate1023 f Aplus) c xStar d hLC2
  have hq_cont : Continuous q := by
    -- The frozen Lagrangian Hessian defines a fixed quadratic form in the direction variable.
    simpa [q, hessianQuadraticAt, hessianAt] using
      (show Continuous fun d : EuclideanSpace ℝ (Fin n) ↦
        inner ℝ d ((fderiv ℝ (gradient L) xStar) d) by
          fun_prop)
  have hp_cont : Continuous p := by
    -- The penalty side is the finite sum of squared linearized equality-constraint violations.
    simpa [p] using
      (show Continuous fun d : EuclideanSpace ℝ (Fin n) ↦
        ∑ i : Fin m, (dotProduct d (equalityConstraintGradient c xStar i)) ^ (2 : ℕ) by
          fun_prop)
  have hp_nonneg : ∀ d : EuclideanSpace ℝ (Fin n), 0 ≤ p d := by
    intro d
    dsimp [p]
    exact Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hpos :
      ∀ d : EuclideanSpace ℝ (Fin n), d ≠ 0 → p d = 0 → 0 < q d := by
    intro d hd hp0
    have hterms :
        ∀ i : Fin m,
          (dotProduct d (equalityConstraintGradient c xStar i)) ^ (2 : ℕ) = 0 := by
      intro i
      exact
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun j _ ↦ sq_nonneg (dotProduct d (equalityConstraintGradient c xStar j)))).mp
          (by simpa [p] using hp0) i (Finset.mem_univ _)
    have hdLinearized : d ∈ equalityLinearizedFeasibleDirectionSet c xStar := by
      -- Vanishing of the penalty quadratic forces every linearized equality constraint to vanish.
      rw [mem_equalityLinearizedFeasibleDirectionSet_iff]
      intro i
      have hi_mul_zero :
          dotProduct d (equalityConstraintGradient c xStar i) *
            dotProduct d (equalityConstraintGradient c xStar i) = 0 := by
        simpa [pow_two] using hterms i
      exact mul_self_eq_zero.mp hi_mul_zero
    have hqpos :
        0 <
          equalityLagrangianHessianQuadratic
            f (fletcherMultiplierEstimate1023 f Aplus) c xStar d :=
      h_sosc'.2.2.2.2 d hdLinearized hd
    exact hLagEq d ▸ hqpos
  have hsphere_compact :
      IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isCompact_sphere _ _
  have hsphere_nonempty :
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  by_cases hK_empty : K = ∅
  · refine ⟨0, le_rfl, ?_⟩
    intro d hd_norm
    have hd_sphere : d ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hd_norm
    have hq_pos : 0 < q d := by
      by_contra hq_nonpos
      have hk : d ∈ K := ⟨hd_sphere, le_of_not_gt hq_nonpos⟩
      have hK_not_nonempty : ¬ K.Nonempty := by
        simp [hK_empty]
      exact hK_not_nonempty ⟨d, hk⟩
    -- If the bad set is empty, the unshifted quadratic form is already positive on the sphere.
    simpa [hLagEq d] using hq_pos
  · have hK_compact : IsCompact K := by
      -- The bad set is the compact sphere intersected with the closed nonpositive sublevel of `q`.
      dsimp [K]
      exact hsphere_compact.inter_right (isClosed_le hq_cont continuous_const)
    have hK_nonempty : K.Nonempty := Set.nonempty_iff_ne_empty.mpr hK_empty
    obtain ⟨d0, hd0K, hd0min⟩ := hK_compact.exists_isMinOn hK_nonempty hp_cont.continuousOn
    have hd0_norm : ‖d0‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hd0K.1
    have hd0_ne : d0 ≠ 0 := by
      intro hd0_zero
      have : ‖d0‖ = 0 := by
        simp [hd0_zero]
      linarith
    have hp_d0_ne : p d0 ≠ 0 := by
      intro hp_zero
      have hq_d0_pos : 0 < q d0 := hpos d0 hd0_ne hp_zero
      exact (not_lt_of_ge hd0K.2) hq_d0_pos
    let δ : ℝ := p d0
    have hδ_nonneg : 0 ≤ δ := hp_nonneg d0
    have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (Ne.symm hp_d0_ne)
    obtain ⟨d1, hd1sphere, hd1min⟩ :=
      hsphere_compact.exists_isMinOn hsphere_nonempty hq_cont.continuousOn
    let m0 : ℝ := q d1
    have hm0_nonpos : m0 ≤ 0 := by
      have hm0_le_d0 : m0 ≤ q d0 := hd1min hd0K.1
      exact le_trans hm0_le_d0 hd0K.2
    let τ : ℝ := (1 - m0) / δ
    have hτ_nonneg : 0 ≤ τ := by
      -- The chosen penalty shift is nonnegative because `m0 ≤ 0 < δ`.
      dsimp [τ]
      apply div_nonneg
      · linarith
      · exact hδ_nonneg
    refine ⟨τ, hτ_nonneg, ?_⟩
    intro d hd_norm
    have hd_sphere : d ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm] using hd_norm
    by_cases hqd : q d ≤ 0
    · have hδ_le : δ ≤ p d := hd0min ⟨hd_sphere, hqd⟩
      have hm0_le_d : m0 ≤ q d := hd1min hd_sphere
      have hτ_mul_eq : τ * δ = 1 - m0 := by
        have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
        calc
          τ * δ = ((1 - m0) / δ) * δ := by
            rfl
          _ = 1 - m0 := by
            field_simp [hδ_ne]
      have hτ_mul_le : τ * δ ≤ τ * p d :=
        mul_le_mul_of_nonneg_left hδ_le hτ_nonneg
      have hbound : 1 ≤ q d + τ * p d := by
        calc
          1 = m0 + τ * δ := by
                linarith [hτ_mul_eq]
          _ ≤ q d + τ * p d := by
                linarith [hm0_le_d, hτ_mul_le]
      have hpenalty : 0 < q d + τ * p d := by
        linarith
      -- On the bad set, the compactness gap forces strict positivity after the shift.
      simpa [p, hLagEq d] using hpenalty
    · have hq_pos : 0 < q d := lt_of_not_ge hqd
      have hextra_nonneg : 0 ≤ τ * p d := mul_nonneg hτ_nonneg (hp_nonneg d)
      have hpenalty : 0 < q d + τ * p d := by
        linarith
      -- Outside the bad set, the unshifted quadratic form is already strictly positive.
      simpa [p, hLagEq d] using hpenalty

/-- Helper for Chapter10 Definition 10.5-extra-1: the equality-constrained SOSC should yield a
strict local minimum for the frozen-multiplier scalar penalty after adding a sufficiently large
quadratic infeasibility term. -/
lemma exists_scalarPenaltyThreshold_for_isStrictLocalMin_frozenSimplePenalty
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (xStar : EuclideanSpace ℝ (Fin n))
    (h_sosc :
      SecondOrderSufficientCondition f (fletcherMultiplierEstimate1023 f Aplus) c xStar) :
    ∃ τ : ℝ,
      0 ≤ τ ∧
        IsStrictLocalMin
          (fun x ↦
            f x - dotProduct (fletcherMultiplierEstimate1023 f Aplus xStar) (c x) +
              ((1 / 2 : ℝ) * τ) * ‖c x‖ ^ (2 : ℕ))
          xStar := by
  let L : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    equalityLagrangian f (fletcherMultiplierEstimate1023 f Aplus) c xStar x
  let penaltyHalf : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    ((1 / 2 : ℝ) * ‖c x‖ ^ (2 : ℕ))
  have h_sosc' := (secondOrderSufficientCondition_iff
    f (fletcherMultiplierEstimate1023 f Aplus) c xStar).mp h_sosc
  have hxStarFeasible : xStar ∈ equalityFeasibleSet c := h_sosc'.1
  have hcStar : c xStar = 0 := (mem_equalityFeasibleSet c xStar).mp hxStarFeasible
  have hLC2 :
      ContDiffAt ℝ 2 L xStar :=
    equalityLagrangian_contDiffAt f (fletcherMultiplierEstimate1023 f Aplus) c xStar
      h_sosc'.2.2.1 h_sosc'.2.2.2.1
  have hPenaltyHalfC2 :
      ContDiffAt ℝ 2 penaltyHalf xStar :=
    halfNormSqPenalty_contDiffAt c xStar h_sosc'.2.2.2.1
  rcases subsingleton_or_nontrivial (EuclideanSpace ℝ (Fin n)) with hSub | hNontriv
  · refine ⟨0, le_rfl, ?_⟩
    rw [isStrictLocalMin_iff_exists_forall_mem_ball]
    refine ⟨1, zero_lt_one, ?_⟩
    intro y hy hy_ne
    exact (hy_ne (hSub.elim _ _)).elim
  · letI : Nontrivial (EuclideanSpace ℝ (Fin n)) := hNontriv
    rcases exists_penaltyShift_pos_on_unitSphere_of_sosc
        f c Aplus xStar h_sosc with ⟨τ, hτ, hSpherePos⟩
    let scaledPenalty : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ τ • penaltyHalf x
    let frozenPenalty : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦ L x + scaledPenalty x
    have hScaledC2 :
        ContDiffAt ℝ 2 scaledPenalty xStar := by
      -- Scalar multiplication preserves the local `C²` regularity of the penalty term.
      simpa [scaledPenalty] using hPenaltyHalfC2.const_smul τ
    have hFrozenC2 :
        ContDiffAt ℝ 2 frozenPenalty xStar := by
      -- The frozen penalty is the sum of the frozen Lagrangian and the scaled half-norm square.
      simpa [frozenPenalty] using hLC2.add hScaledC2
    have hPenaltyHalfMin : IsLocalMin penaltyHalf xStar := by
      have hPenaltyHalfGlobal :
          IsMinOn penaltyHalf Set.univ xStar := by
        rw [isMinOn_iff]
        intro x hx
        have hx_nonneg : 0 ≤ penaltyHalf x := by
          dsimp [penaltyHalf]
          positivity
        have hxStar_zero : penaltyHalf xStar = 0 := by
          simp [penaltyHalf, hcStar]
        simpa [hxStar_zero] using hx_nonneg
      -- Feasibility makes the half-norm-square penalty globally minimized at `xStar`.
      simpa [isLocalMinOn_univ_iff] using hPenaltyHalfGlobal.localize
    have hLFDeriv0 :
        fderiv ℝ L xStar = 0 := by
      -- Convert the SOSC stationarity clause from the gradient owner back to the Fréchet owner.
      simpa [L, gradient] using
        congrArg
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)))
          h_sosc'.2.1
    have hPenaltyHalfFDeriv0 :
        fderiv ℝ penaltyHalf xStar = 0 :=
      IsLocalMin.fderiv_eq_zero hPenaltyHalfMin
    have hScaledFDeriv0 :
        fderiv ℝ scaledPenalty xStar = 0 := by
      -- The scaled penalty keeps zero first derivative because the base half-square already does.
      change fderiv ℝ (τ • penaltyHalf) xStar = 0
      rw [fderiv_const_smul (hPenaltyHalfC2.differentiableAt (by norm_num)) τ,
        hPenaltyHalfFDeriv0, smul_zero]
    have hFrozenFDeriv0 :
        fderiv ℝ frozenPenalty xStar = 0 := by
      -- The frozen penalty is first-order stationary because both summands are.
      change fderiv ℝ (L + scaledPenalty) xStar = 0
      rw [fderiv_add (hLC2.differentiableAt (by norm_num))
          (hScaledC2.differentiableAt (by norm_num)),
        hLFDeriv0, hScaledFDeriv0, zero_add]
    have hFrozenGrad0 :
        gradient frozenPenalty xStar = 0 := by
      -- Translate the vanishing Fréchet derivative back to the gradient owner used in Chapter 1.
      simpa [frozenPenalty, gradient] using
        congrArg
          ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm)
          hFrozenFDeriv0
    have hFrozenHessEq :
        ∀ y : EuclideanSpace ℝ (Fin n),
          hessianQuadraticAt frozenPenalty xStar y =
            equalityLagrangianHessianQuadratic
              f (fletcherMultiplierEstimate1023 f Aplus) c xStar y +
              τ * ∑ i : Fin m,
                (dotProduct y (equalityConstraintGradient c xStar i)) ^ (2 : ℕ) := by
      intro y
      have hLDiag :
          (iteratedFDeriv ℝ 2 L xStar) ![y, y] = hessianQuadraticAt L xStar y :=
        (ConstrainedOptimizationProblem.hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt
          (f := L) (x := xStar) (y := y) hLC2).symm
      have hPenaltyDiag :
          (iteratedFDeriv ℝ 2 penaltyHalf xStar) ![y, y] =
            hessianQuadraticAt penaltyHalf xStar y :=
        (ConstrainedOptimizationProblem.hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt
          (f := penaltyHalf) (x := xStar) (y := y) hPenaltyHalfC2).symm
      have hScaledDiag :
          (iteratedFDeriv ℝ 2 scaledPenalty xStar) ![y, y] =
            τ * (iteratedFDeriv ℝ 2 penaltyHalf xStar) ![y, y] := by
        -- The scaled penalty contributes a scalar multiple of the base half-square Hessian.
        change (iteratedFDeriv ℝ 2 (τ • penaltyHalf) xStar) ![y, y] =
          τ * (iteratedFDeriv ℝ 2 penaltyHalf xStar) ![y, y]
        simpa [scaledPenalty] using
          congrArg (fun T ↦ T ![y, y])
            (iteratedFDeriv_const_smul_apply
              (a := τ) (f := penaltyHalf) (i := 2) (x := xStar) hPenaltyHalfC2)
      have hFrozenDiag :
          hessianQuadraticAt frozenPenalty xStar y =
            (iteratedFDeriv ℝ 2 frozenPenalty xStar) ![y, y] :=
        ConstrainedOptimizationProblem.hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt
          (f := frozenPenalty) (x := xStar) (y := y) hFrozenC2
      calc
        hessianQuadraticAt frozenPenalty xStar y
            = (iteratedFDeriv ℝ 2 frozenPenalty xStar) ![y, y] := by
                exact hFrozenDiag
        _ = (iteratedFDeriv ℝ 2 L xStar) ![y, y] +
              (iteratedFDeriv ℝ 2 scaledPenalty xStar) ![y, y] := by
                -- Split the second derivative across the frozen Lagrangian and penalty parts.
                exact congrArg (fun T ↦ T ![y, y]) (iteratedFDeriv_add_apply hLC2 hScaledC2)
        _ = hessianQuadraticAt L xStar y +
              τ * hessianQuadraticAt penaltyHalf xStar y := by
                rw [hLDiag, hScaledDiag, hPenaltyDiag]
        _ = equalityLagrangianHessianQuadratic
              f (fletcherMultiplierEstimate1023 f Aplus) c xStar y +
              τ * ∑ i : Fin m,
                (dotProduct y (equalityConstraintGradient c xStar i)) ^ (2 : ℕ) := by
                rw [← equalityLagrangianHessianQuadratic_eq_hessianQuadraticAt
                      f (fletcherMultiplierEstimate1023 f Aplus) c xStar y hLC2,
                  hessianQuadraticAt_halfNormSqPenalty_eq_sumSquares
                    c xStar y hcStar h_sosc'.2.2.2.1]
    have hPosDef :
        ∀ y : EuclideanSpace ℝ (Fin n), y ≠ 0 →
          0 < (iteratedFDeriv ℝ 2 frozenPenalty xStar) ![y, y] := by
      intro y hy
      let u : EuclideanSpace ℝ (Fin n) := ‖y‖⁻¹ • y
      have hy_norm_pos : 0 < ‖y‖ := norm_pos_iff.mpr hy
      have hu_norm : ‖u‖ = 1 := by
        -- Normalize the nonzero direction onto the unit sphere used by the compactness shift.
        dsimp [u]
        calc
          ‖‖y‖⁻¹ • y‖ = |‖y‖⁻¹| * ‖y‖ := norm_smul _ _
          _ = ‖y‖⁻¹ * ‖y‖ := by rw [abs_of_pos (inv_pos.mpr hy_norm_pos)]
          _ = 1 := by field_simp [hy_norm_pos.ne']
      have hu_pos : 0 < hessianQuadraticAt frozenPenalty xStar u := by
        -- The unit-sphere positivity transfers to the frozen penalty Hessian through the
        -- normalized Hessian identity.
        simpa [hFrozenHessEq u] using hSpherePos u hu_norm
      have hy_eq : y = ‖y‖ • u := by
        -- Recover `y` from its norm and normalized direction.
        dsimp [u]
        have hscale :
            ‖y‖ • (‖y‖⁻¹ • y) = y := by
          calc
            ‖y‖ • (‖y‖⁻¹ • y) = (‖y‖ * ‖y‖⁻¹) • y := by rw [smul_smul]
            _ = (1 : ℝ) • y := by
                  congr 1
                  exact mul_inv_cancel₀ hy_norm_pos.ne'
            _ = y := by simp
        exact hscale.symm
      have hy_hess_pos :
          0 < hessianQuadraticAt frozenPenalty xStar y := by
        have hscaled :
            0 < ‖y‖ ^ (2 : ℕ) * hessianQuadraticAt frozenPenalty xStar u := by
          exact mul_pos (pow_pos hy_norm_pos 2) hu_pos
        -- Homogeneity upgrades the unit-sphere positivity to all nonzero directions.
        have hy_smul_pos :
            0 < hessianQuadraticAt frozenPenalty xStar (‖y‖ • u) := by
          rw [hessianQuadraticAt_smul]
          exact hscaled
        exact hy_eq ▸ hy_smul_pos
      exact (ConstrainedOptimizationProblem.hessianQuadraticAt_eq_iteratedFDeriv_diag_of_contDiffAt
        (f := frozenPenalty) (x := xStar) (y := y) hFrozenC2).symm ▸ hy_hess_pos
    refine ⟨τ, hτ, ?_⟩
    -- Chapter 1 now closes the strict local minimum from local `C²`, stationarity, and the
    -- positive definite frozen penalty Hessian.
    have hFrozenMin :
        IsStrictLocalMin frozenPenalty xStar :=
      isStrictLocalMin_of_gradient_eq_zero_of_iteratedFDeriv_pos
        frozenPenalty xStar hFrozenC2 hFrozenGrad0 hPosDef
    convert hFrozenMin using 1
    funext x
    dsimp [frozenPenalty, scaledPenalty, penaltyHalf, L, equalityLagrangian]
    ring

/-- Chapter10 Definition 10.5-extra-1: if `xStar` is a local minimizer of the
equality-constrained problem `(10.5.1)`-`(10.5.2)`, the equality-constrained second-order
sufficient condition from `§10.1` holds at `xStar` for the multiplier estimate `(10.1.23)`, and
the varying multiplier term satisfies the local quadratic control on infeasibility used in the
earlier `§10.1`/`§10.4` discussions, then sufficiently large diagonal penalty entries make
`xStar` a strict local minimizer of Fletcher's smooth exact penalty function `(10.5.3)`. Here
`Aplus` is assumed to be the chosen pseudoinverse field for the equality-constraint Jacobian, as
required by the source definition of `(10.1.23)`. -/
theorem isStrictLocalMinOn_fletcherEqualitySmoothExactPenaltyFunction_of_sosc
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (hAplus : isConstraintJacobianPseudoInverseField c Aplus)
    (xStar : EuclideanSpace ℝ (Fin n))
    (h_multiplierQuadratic :
      ∃ K : ℝ,
        0 ≤ K ∧
          ∀ᶠ x in nhds xStar,
            ‖dotProduct
                (fletcherMultiplierEstimate1023 f Aplus x -
                  fletcherMultiplierEstimate1023 f Aplus xStar)
                (c x)‖ ≤ K * ‖c x‖ ^ (2 : ℕ))
    (h_localMin : IsLocalMinOn f (equalityFeasibleSet c) xStar)
    (h_sosc :
      SecondOrderSufficientCondition f (fletcherMultiplierEstimate1023 f Aplus) c xStar) :
    ∃ σBar : EuclideanSpace ℝ (Fin m),
      ∀ σ : EuclideanSpace ℝ (Fin m),
        (∀ i : Fin m, σBar i ≤ σ i) →
          IsStrictLocalMin
            (fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ) xStar :=
  -- TODO: First obtain strict local minimality for the frozen-multiplier quadratic penalty from
  -- the equality SOSC at `xStar`, then use `h_multiplierQuadratic` to absorb the varying
  -- multiplier error by choosing `σ` componentwise large enough.
  by
  let _ := hAplus
  let _ := h_localMin
  rcases h_multiplierQuadratic with ⟨K, hK, hEvent⟩
  rcases exists_scalarPenaltyThreshold_for_isStrictLocalMin_frozenSimplePenalty
      f c Aplus xStar h_sosc with ⟨τ, hτ, hFrozen⟩
  let frozenPenalty : EuclideanSpace ℝ (Fin n) → ℝ := fun x ↦
    f x - dotProduct (fletcherMultiplierEstimate1023 f Aplus xStar) (c x) +
      ((1 / 2 : ℝ) * τ) * ‖c x‖ ^ (2 : ℕ)
  let σBar : EuclideanSpace ℝ (Fin m) := constantConstraintPoint (τ + 2 * K)
  refine ⟨σBar, ?_⟩
  intro σ hσ
  have hxStarFeasible : xStar ∈ equalityFeasibleSet c := h_sosc.1
  have hcStar : c xStar = 0 := (mem_equalityFeasibleSet c xStar).mp hxStarFeasible
  have hσLower : ∀ i : Fin m, τ + 2 * K ≤ σ i := by
    intro i
    simpa [σBar, constantConstraintPoint_def] using hσ i
  have hCompare :
      ∀ᶠ x in nhdsWithin xStar {xStar}ᶜ,
        frozenPenalty x ≤ fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ x :=
    eventually_fletcherEqualityPenalty_ge_frozenSimplePenalty
      f c Aplus xStar τ K σ hσLower hEvent
  have hEqAtBase :
      fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ xStar = frozenPenalty xStar := by
    -- Feasibility makes both penalty functions agree with `f` at `xStar`.
    calc
      fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ xStar = f xStar := by
        simpa [fletcherEqualitySmoothExactPenaltyFunction] using
          equalitySmoothExactPenaltyFunction.eq_objective
            f (fletcherMultiplierEstimate1023 f Aplus) c σ hxStarFeasible
      _ = frozenPenalty xStar := by
        simp [frozenPenalty, hcStar]
  -- Transfer strict local minimality from the frozen penalty to the full Fletcher penalty.
  exact isStrictLocalMin_of_eq_at_base_of_eventually_ge hFrozen hEqAtBase hCompare

/-- If `xBar` minimizes Fletcher's smooth exact penalty
function `(10.5.3)` and satisfies the equality constraint `c xBar = 0`, then `xBar` is also a
minimizer of the original equality-constrained problem `(10.5.1)`-`(10.5.2)`. The chosen
pseudoinverse-field hypothesis on `Aplus` is redundant for this implication and is omitted from
the public Lean statement. -/
theorem isMinOn_objective_of_isMinOn_fletcherEqualitySmoothExactPenaltyFunction
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (σ : EuclideanSpace ℝ (Fin m))
    (xBar : EuclideanSpace ℝ (Fin n))
    (hxBar :
      IsMinOn (fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ) Set.univ xBar)
    (hc : c xBar = 0) :
    IsMinOn f (equalityFeasibleSet c) xBar := by
  -- Evaluate the global penalty minimizer on an arbitrary feasible competitor.
  rw [isMinOn_iff]
  intro x hx
  have hpenalty :
      fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ xBar ≤
        fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ x :=
    (isMinOn_univ_iff.mp hxBar) x
  have hxBarFeasible : xBar ∈ equalityFeasibleSet c := (mem_equalityFeasibleSet c xBar).2 hc
  have hxBarEq :
      fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ xBar = f xBar := by
    simpa [fletcherEqualitySmoothExactPenaltyFunction] using
      equalitySmoothExactPenaltyFunction.eq_objective
        f (fletcherMultiplierEstimate1023 f Aplus) c σ hxBarFeasible
  have hxEq :
      fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ x = f x := by
    simpa [fletcherEqualitySmoothExactPenaltyFunction] using
      equalitySmoothExactPenaltyFunction.eq_objective
        f (fletcherMultiplierEstimate1023 f Aplus) c σ hx
  calc
    f xBar = fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ xBar := hxBarEq.symm
    _ ≤ fletcherEqualitySmoothExactPenaltyFunction f c Aplus σ x := hpenalty
    _ = f x := hxEq

/-- Helper for Chapter10 Definition 10.5-extra-1: along global minimizers of Fletcher's simple
smooth exact penalty subproblems, the squared constraint residual is antitone in the penalty
parameter. -/
lemma constraintResidualSqAntitoneOfFletcherSimpleStageMinimizers
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hx :
      ∀ σ : ℝ, 0 < σ →
        IsMinOn (fletcherSimpleSmoothExactPenaltyFunction f c Aplus σ) Set.univ (x σ))
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    ‖c (x σ₂)‖ ^ (2 : ℕ) ≤ ‖c (x σ₁)‖ ^ (2 : ℕ) := by
  have hσ₂ : 0 < σ₂ := lt_trans hσ₁ hσ₁₂
  -- Compare the `σ₁`- and `σ₂`-stage minimizers against the opposite-stage competitors.
  have hmin₁₂ :
      fletcherSimpleSmoothExactPenaltyFunction f c Aplus σ₁ (x σ₁) ≤
        fletcherSimpleSmoothExactPenaltyFunction f c Aplus σ₁ (x σ₂) :=
    (isMinOn_univ_iff.mp (hx σ₁ hσ₁)) (x σ₂)
  have hmin₂₁ :
      fletcherSimpleSmoothExactPenaltyFunction f c Aplus σ₂ (x σ₂) ≤
        fletcherSimpleSmoothExactPenaltyFunction f c Aplus σ₂ (x σ₁) :=
    (isMinOn_univ_iff.mp (hx σ₂ hσ₂)) (x σ₁)
  set b₁ : ℝ :=
    f (x σ₁) - dotProduct (fletcherMultiplierEstimate1023 f Aplus (x σ₁)) (c (x σ₁))
  set b₂ : ℝ :=
    f (x σ₂) - dotProduct (fletcherMultiplierEstimate1023 f Aplus (x σ₂)) (c (x σ₂))
  set v₁ : ℝ := ‖c (x σ₁)‖ ^ (2 : ℕ)
  set v₂ : ℝ := ‖c (x σ₂)‖ ^ (2 : ℕ)
  -- Normalize both inequalities to the common `base + ((1 / 2) * σ) * residual²` shape.
  have hmin₁₂' : b₁ + ((1 / 2 : ℝ) * σ₁) * v₁ ≤ b₂ + ((1 / 2 : ℝ) * σ₁) * v₂ := by
    simpa [b₁, b₂, v₁, v₂, fletcherSimpleSmoothExactPenaltyFunction_apply] using hmin₁₂
  have hmin₂₁' : b₂ + ((1 / 2 : ℝ) * σ₂) * v₂ ≤ b₁ + ((1 / 2 : ℝ) * σ₂) * v₁ := by
    simpa [b₁, b₂, v₁, v₂, fletcherSimpleSmoothExactPenaltyFunction_apply] using hmin₂₁
  -- Eliminating the base terms isolates the residual-square comparison.
  nlinarith

/-- If `x(σ)` solves the simple smooth exact penalty
subproblem `(10.5.5)` for every positive `σ`, then the constraint residual is monotone in the
penalty parameter:
`‖c (x σ₂)‖ ≤ ‖c (x σ₁)‖` whenever `0 < σ₁ ≤ σ₂`. The chosen pseudoinverse-field hypothesis on
`Aplus` is redundant for this monotonicity statement and is omitted from the public Lean
statement. -/
theorem norm_constraint_le_of_isMinOn_fletcherSimpleSmoothExactPenaltyFunction
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (Aplus : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ)
    (x : ℝ → EuclideanSpace ℝ (Fin n))
    (hx :
      ∀ σ : ℝ, 0 < σ →
        IsMinOn (fletcherSimpleSmoothExactPenaltyFunction f c Aplus σ) Set.univ (x σ))
    (σ₁ σ₂ : ℝ) (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ ≤ σ₂) :
    ‖c (x σ₂)‖ ≤ ‖c (x σ₁)‖ := by
  rcases hσ₁₂.eq_or_lt with rfl | hσ₁₂lt
  · -- Equal parameters give identical residual norms.
    rfl
  · -- First compare squared norms, then use nonnegativity of norms to remove the square.
    have hsq :
        ‖c (x σ₂)‖ ^ (2 : ℕ) ≤ ‖c (x σ₁)‖ ^ (2 : ℕ) :=
      constraintResidualSqAntitoneOfFletcherSimpleStageMinimizers
        f c Aplus x hx hσ₁ hσ₁₂lt
    nlinarith [norm_nonneg (c (x σ₁)), norm_nonneg (c (x σ₂)), hsq]

#print axioms equalitySmoothExactPenaltyFunction
#print axioms simpleSmoothExactPenaltyFunction
#print axioms fletcherMultiplierEstimate1023
#print axioms fletcherEqualitySmoothExactPenaltyFunction
#print axioms fletcherSimpleSmoothExactPenaltyFunction

end Chapter10Definition105Extra1
