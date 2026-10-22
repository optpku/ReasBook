/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.AtTopBot.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap11.Definition_11_2_extra_1

noncomputable section

open Filter
open scoped Matrix.Norms.Frobenius

section Chapter11Algorithm1131

variable {basicDim nonbasicDim : ℕ}

local notation "BasicPoint" => EuclideanSpace ℝ (Fin basicDim)
local notation "NonbasicPoint" => EuclideanSpace ℝ (Fin nonbasicDim)
local notation "Point" => BasicPoint × NonbasicPoint

-- Semantic recall: `lean_leansearch` surfaced no reusable mathlib owner for the generalized
-- reduced-gradient method. Following the neighboring Chapter 11 algorithm files, this item is
-- formalized as explicit split-coordinate iteration data with concrete Step 4 and Step 5 updates.

/-- The Step 6 backtracking rule in Algorithm 11.3.1 sends the initial steplength `αₖ⁽⁰⁾` to
`αₖ⁽⁰⁾ / 2ˡ` after `l` halvings. -/
def generalizedReducedGradientTrialStepSize (α0 : ℝ) (l : ℕ) : ℝ :=
  α0 / ((2 : ℝ) ^ l)

/-- The Step 4 nonbasic update in Algorithm 11.3.1 is
`x_N = (x_k)_N - α * g̃_k`. -/
def generalizedReducedGradientTrialNonbasic
    (xN gTilde : NonbasicPoint) (α : ℝ) : NonbasicPoint :=
  xN - α • gTilde

/-- The Step 5 feasibility-restoration update in Algorithm 11.3.1 is
`x_B = x_B - A_B⁻ᵀ c(x_B, x_N)`. -/
def generalizedReducedGradientCorrection
    (constraint : Point → BasicPoint)
    (AB : Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (xB : BasicPoint) (xN : NonbasicPoint) : BasicPoint :=
  xB - Matrix.toEuclideanLin (AB⁻¹).transpose (constraint (xB, xN))

/-- The trial point at outer stage `k`, backtracking count `l`, and Step 5 correction count `j`
is `(x_B, x_N) = (trialBasic k l j, trialNonbasic k l)`. -/
def generalizedReducedGradientTrialPoint
    (trialBasic : ℕ → ℕ → ℕ → BasicPoint)
    (trialNonbasic : ℕ → ℕ → NonbasicPoint)
    (k l j : ℕ) : Point :=
  (trialBasic k l j, trialNonbasic k l)

/-- A Step 5 correction is accepted by the source residual test when
`‖c(x_B, x_N)‖ ≤ ε̄`. -/
def generalizedReducedGradientResidualAccepts
    (constraint : Point → BasicPoint) (εBar : ℝ)
    (trialBasic : ℕ → ℕ → ℕ → BasicPoint)
    (trialNonbasic : ℕ → ℕ → NonbasicPoint)
    (k l j : ℕ) : Prop :=
  ‖constraint (generalizedReducedGradientTrialPoint trialBasic trialNonbasic k l j)‖ ≤ εBar

/-- A residual-acceptable trial point is accepted by Step 7 when it strictly decreases the
objective value relative to the current iterate `x_k`. -/
def generalizedReducedGradientObjectiveAccepts
    (objective : Point → ℝ) (iterate : ℕ → Point)
    (trialBasic : ℕ → ℕ → ℕ → BasicPoint)
    (trialNonbasic : ℕ → ℕ → NonbasicPoint)
    (k l j : ℕ) : Prop :=
  objective (generalizedReducedGradientTrialPoint trialBasic trialNonbasic k l j) <
    objective (iterate k)

/-- `GeneralizedReducedGradientStepTwoSpec objective constraint x A_B A_N λ g̃` states that the
four Step 2 partial maps are differentiable at `x = (x_B, x_N)`; `A_B`, `A_N` are the
transpose Jacobian blocks; `λ` satisfies `(11.2.12)`; `g̃` is the reduced-gradient quantity from
`(11.2.11)` in split coordinates. The Jacobian-block and partial-gradient formulas are written
using the canonical split-coordinate API from `Definition_11_2_extra_1`. -/
structure GeneralizedReducedGradientStepTwoSpec
    (objective : Point → ℝ) (constraint : Point → BasicPoint) (x : Point)
    (AB : Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (AN : Matrix (Fin nonbasicDim) (Fin basicDim) ℝ)
    (lam : BasicPoint) (gTilde : NonbasicPoint) : Prop where
  constraintBasic_hasFDerivAt :
    HasFDerivAt
      (fun xB : BasicPoint ↦ constraint (xB, x.2))
      (fderiv ℝ (fun xB : BasicPoint ↦ constraint (xB, x.2)) x.1)
      x.1
  constraintNonbasic_hasFDerivAt :
    HasFDerivAt
      (fun xN : NonbasicPoint ↦ constraint (x.1, xN))
      (fderiv ℝ (fun xN : NonbasicPoint ↦ constraint (x.1, xN)) x.2)
      x.2
  objectiveBasic_hasGradientAt :
    HasGradientAt
      (fun xB : BasicPoint ↦ objective (xB, x.2))
      (gradient (fun xB : BasicPoint ↦ objective (xB, x.2)) x.1)
      x.1
  objectiveNonbasic_hasGradientAt :
    HasGradientAt
      (fun xN : NonbasicPoint ↦ objective (x.1, xN))
      (gradient (fun xN : NonbasicPoint ↦ objective (x.1, xN)) x.2)
      x.2
  basicJacobian_eq :
    AB = (constraintJacobianB (fun xB xN ↦ constraint (xB, xN)) x.1 x.2).transpose
  nonbasicJacobian_eq :
    AN = (constraintJacobianN (fun xB xN ↦ constraint (xB, xN)) x.1 x.2).transpose
  multiplier_eq :
    partialGradientB (fun xB xN ↦ objective (xB, xN)) x.1 x.2 =
      Matrix.toEuclideanLin AB lam
  reducedGradient_eq :
    gTilde =
      partialGradientN (fun xB xN ↦ objective (xB, xN)) x.1 x.2 -
        Matrix.toEuclideanLin AN lam

/-- Unfolding `GeneralizedReducedGradientStepTwoSpec` gives the four differentiability
hypotheses together with the Step 2 matrix identities and reduced-gradient formula. -/
theorem generalizedReducedGradientStepTwoSpec_iff
    (objective : Point → ℝ) (constraint : Point → BasicPoint) (x : Point)
    (AB : Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (AN : Matrix (Fin nonbasicDim) (Fin basicDim) ℝ)
    (lam : BasicPoint) (gTilde : NonbasicPoint) :
    GeneralizedReducedGradientStepTwoSpec objective constraint x AB AN lam gTilde ↔
      HasFDerivAt
          (fun xB : BasicPoint ↦ constraint (xB, x.2))
          (fderiv ℝ (fun xB : BasicPoint ↦ constraint (xB, x.2)) x.1)
          x.1 ∧
        HasFDerivAt
          (fun xN : NonbasicPoint ↦ constraint (x.1, xN))
          (fderiv ℝ (fun xN : NonbasicPoint ↦ constraint (x.1, xN)) x.2)
          x.2 ∧
        HasGradientAt
          (fun xB : BasicPoint ↦ objective (xB, x.2))
          (gradient (fun xB : BasicPoint ↦ objective (xB, x.2)) x.1)
          x.1 ∧
        HasGradientAt
          (fun xN : NonbasicPoint ↦ objective (x.1, xN))
          (gradient (fun xN : NonbasicPoint ↦ objective (x.1, xN)) x.2)
          x.2 ∧
        AB = (constraintJacobianB (fun xB xN ↦ constraint (xB, xN)) x.1 x.2).transpose ∧
        AN = (constraintJacobianN (fun xB xN ↦ constraint (xB, xN)) x.1 x.2).transpose ∧
        partialGradientB (fun xB xN ↦ objective (xB, xN)) x.1 x.2 =
          Matrix.toEuclideanLin AB lam ∧
        gTilde =
          partialGradientN (fun xB xN ↦ objective (xB, xN)) x.1 x.2 -
            Matrix.toEuclideanLin AN lam := by
  constructor
  · intro h
    exact ⟨
      h.constraintBasic_hasFDerivAt,
      h.constraintNonbasic_hasFDerivAt,
      h.objectiveBasic_hasGradientAt,
      h.objectiveNonbasic_hasGradientAt,
      h.basicJacobian_eq,
      h.nonbasicJacobian_eq,
      h.multiplier_eq,
      h.reducedGradient_eq⟩
  · rintro ⟨hConstraintBasic, hConstraintNonbasic, hObjectiveBasic, hObjectiveNonbasic,
      hBasicJacobian, hNonbasicJacobian, hMultiplier, hReducedGradient⟩
    exact ⟨
      hConstraintBasic,
      hConstraintNonbasic,
      hObjectiveBasic,
      hObjectiveNonbasic,
      hBasicJacobian,
      hNonbasicJacobian,
      hMultiplier,
      hReducedGradient⟩

/-- An earlier Step 6 backtracking trial is rejected either because no Step 5 correction count
passes the residual test, or because the first residual-acceptable correction fails the Step 7
objective-decrease test. -/
inductive GeneralizedReducedGradientEarlierBacktrackRejection
    (objective : Point → ℝ) (iterate : ℕ → Point)
    (constraint : Point → BasicPoint) (εBar : ℝ) (maxCorrections : ℕ)
    (trialBasic : ℕ → ℕ → ℕ → BasicPoint)
    (trialNonbasic : ℕ → ℕ → NonbasicPoint)
    (k l : ℕ) : Prop where
  | noResidualAccepts
      (hnone : ∀ j, 1 ≤ j → j ≤ maxCorrections →
        ¬ generalizedReducedGradientResidualAccepts
            constraint
            εBar
            trialBasic
            trialNonbasic
            k
            l
            j) :
      GeneralizedReducedGradientEarlierBacktrackRejection
        objective
        iterate
        constraint
        εBar
        maxCorrections
        trialBasic
        trialNonbasic
        k
        l
  | firstResidualAcceptsFailsObjective
      (j : ℕ)
      (hj_lower : 1 ≤ j)
      (hj_upper : j ≤ maxCorrections)
      (hresidual :
        generalizedReducedGradientResidualAccepts
          constraint
          εBar
          trialBasic
          trialNonbasic
          k
          l
          j)
      (hfirst : ∀ i, 1 ≤ i → i < j →
        ¬ generalizedReducedGradientResidualAccepts
            constraint
            εBar
            trialBasic
            trialNonbasic
            k
            l
            i)
      (hobjective :
        ¬ generalizedReducedGradientObjectiveAccepts
            objective
            iterate
            trialBasic
            trialNonbasic
            k
            l
            j) :
      GeneralizedReducedGradientEarlierBacktrackRejection
        objective
        iterate
        constraint
        εBar
        maxCorrections
        trialBasic
        trialNonbasic
        k
        l

/-- The Step 4 nonbasic trial attached to the current split point `x = (x_B, x_N)` and a
backtracking count `l` is
`x_N = x.2 - α_l • g̃(x)`, where `α_l = α⁽⁰⁾(x) / 2^l`. -/
def generalizedReducedGradientTrialNonbasicAt
    (reducedGradient : Point → NonbasicPoint)
    (initialStepSize : Point → ℝ)
    (x : Point) (l : ℕ) : NonbasicPoint :=
  generalizedReducedGradientTrialNonbasic
    x.2
    (reducedGradient x)
    (generalizedReducedGradientTrialStepSize (initialStepSize x) l)

/-- The Step 5 basic correction iteration attached to the current split point `x = (x_B, x_N)`
and backtracking count `l` starts from `x.1` and repeatedly applies
`x_B := x_B - A_B(x)⁻ᵀ c(x_B, x_N)`. -/
def generalizedReducedGradientTrialBasicAt
    (constraint : Point → BasicPoint)
    (basicJacobian : Point → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : Point → NonbasicPoint)
    (initialStepSize : Point → ℝ)
    (x : Point) (l : ℕ) : ℕ → BasicPoint
  | 0 => x.1
  | j + 1 =>
      generalizedReducedGradientCorrection
        constraint
        (basicJacobian x)
        (generalizedReducedGradientTrialBasicAt
          constraint
          basicJacobian
          reducedGradient
          initialStepSize
          x
          l
          j)
        (generalizedReducedGradientTrialNonbasicAt reducedGradient initialStepSize x l)

/-- The Step 4/Step 5 trial point attached to the current split point `x = (x_B, x_N)`,
backtracking count `l`, and correction count `j` is the pair formed from the `j`-th Step 5
basic correction and the Step 4 nonbasic trial. -/
def generalizedReducedGradientTrialPointAt
    (constraint : Point → BasicPoint)
    (basicJacobian : Point → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : Point → NonbasicPoint)
    (initialStepSize : Point → ℝ)
    (x : Point) (l j : ℕ) : Point :=
  ( generalizedReducedGradientTrialBasicAt
      constraint
      basicJacobian
      reducedGradient
      initialStepSize
      x
      l
      j
  , generalizedReducedGradientTrialNonbasicAt reducedGradient initialStepSize x l )

/-- The residual test at the current split point `x` accepts the Step 5 correction count `j`
and Step 6 backtracking count `l` exactly when the resulting trial point satisfies
`‖c(x_B, x_N)‖ ≤ ε̄`. -/
def generalizedReducedGradientResidualAcceptsAt
    (constraint : Point → BasicPoint) (εBar : ℝ)
    (basicJacobian : Point → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : Point → NonbasicPoint)
    (initialStepSize : Point → ℝ)
    (x : Point) (l j : ℕ) : Prop :=
  ‖constraint
      (generalizedReducedGradientTrialPointAt
        constraint
        basicJacobian
        reducedGradient
        initialStepSize
        x
        l
        j)‖ ≤ εBar

/-- The Step 7 acceptance test at the current split point `x` accepts the Step 5 correction
count `j` and Step 6 backtracking count `l` exactly when the resulting trial point strictly
decreases the objective value relative to `x`. -/
def generalizedReducedGradientObjectiveAcceptsAt
    (objective : Point → ℝ)
    (constraint : Point → BasicPoint)
    (basicJacobian : Point → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : Point → NonbasicPoint)
    (initialStepSize : Point → ℝ)
    (x : Point) (l j : ℕ) : Prop :=
  objective
      (generalizedReducedGradientTrialPointAt
        constraint
        basicJacobian
        reducedGradient
        initialStepSize
        x
        l
        j) <
    objective x

/-- The recursive Step 5 search over the correction window `j, ..., j + remaining - 1` returns
the first correction count whose trial point satisfies the residual test, or `none` if no such
correction occurs in that window. -/
def generalizedReducedGradientFirstResidualAcceptedCorrectionAux
    (constraint : Point → BasicPoint) (εBar : ℝ)
    (basicJacobian : Point → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : Point → NonbasicPoint)
    (initialStepSize : Point → ℝ)
    (x : Point) (l : ℕ) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | j, remaining + 1 =>
      let _ : Decidable
          (generalizedReducedGradientResidualAcceptsAt
            constraint
            εBar
            basicJacobian
            reducedGradient
            initialStepSize
            x
            l
            j) :=
        Classical.decPred
          (fun j' ↦
            generalizedReducedGradientResidualAcceptsAt
              constraint
              εBar
              basicJacobian
              reducedGradient
              initialStepSize
              x
              l
              j')
          j
      if generalizedReducedGradientResidualAcceptsAt
          constraint
          εBar
          basicJacobian
          reducedGradient
          initialStepSize
          x
          l
          j then
        some j
      else
        generalizedReducedGradientFirstResidualAcceptedCorrectionAux
          constraint
          εBar
          basicJacobian
          reducedGradient
          initialStepSize
          x
          l
          (j + 1)
          remaining

/-- The Step 5 search attached to `x` and the backtracking count `l` inspects the positive
correction counts `1, ..., M` and returns the first one satisfying the residual test. -/
def generalizedReducedGradientFirstResidualAcceptedCorrection
    (constraint : Point → BasicPoint) (εBar : ℝ)
    (basicJacobian : Point → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : Point → NonbasicPoint)
    (initialStepSize : Point → ℝ)
    (maxCorrections : ℕ)
    (x : Point) (l : ℕ) : Option ℕ :=
  generalizedReducedGradientFirstResidualAcceptedCorrectionAux
    constraint
    εBar
    basicJacobian
    reducedGradient
    initialStepSize
    x
    l
    1
    maxCorrections

/-- The accepted correction search attached to `x` and the backtracking count `l` returns the
first residual-acceptable Step 5 correction when that first residual-acceptable correction also
passes the Step 7 decrease test; otherwise it returns `none`. -/
def generalizedReducedGradientAcceptedCorrectionAt
    (objective : Point → ℝ)
    (constraint : Point → BasicPoint)
    (basicJacobian : Point → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : Point → NonbasicPoint)
    (initialStepSize : Point → ℝ)
    (εBar : ℝ) (maxCorrections : ℕ)
    (x : Point) (l : ℕ) : Option ℕ :=
  match generalizedReducedGradientFirstResidualAcceptedCorrection
      constraint
      εBar
      basicJacobian
      reducedGradient
      initialStepSize
      maxCorrections
      x
      l with
  | some j =>
      let _ : Decidable
          (generalizedReducedGradientObjectiveAcceptsAt
            objective
            constraint
            basicJacobian
            reducedGradient
            initialStepSize
            x
            l
            j) :=
        Classical.decPred
          (fun j' ↦
            generalizedReducedGradientObjectiveAcceptsAt
              objective
              constraint
              basicJacobian
              reducedGradient
              initialStepSize
              x
              l
              j')
          j
      if generalizedReducedGradientObjectiveAcceptsAt
          objective
          constraint
          basicJacobian
          reducedGradient
          initialStepSize
          x
          l
          j then
        some j
      else
        none
  | none => none

/-- Helper for Chapter11 Algorithm 11.3.1: if the auxiliary Step 5 search returns a correction
count, that returned correction count satisfies the Step 5 residual test. -/
theorem firstResidualAcceptedCorrectionAux_eq_some_implies_residualAcceptsAt
    (constraint : Point → BasicPoint) (εBar : ℝ)
    (basicJacobian : Point → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : Point → NonbasicPoint)
    (initialStepSize : Point → ℝ)
    (x : Point) (l : ℕ) {jStart remaining j : ℕ}
    (hfound :
      generalizedReducedGradientFirstResidualAcceptedCorrectionAux
          constraint
          εBar
          basicJacobian
          reducedGradient
          initialStepSize
          x
          l
          jStart
          remaining =
        some j) :
    generalizedReducedGradientResidualAcceptsAt
      constraint
      εBar
      basicJacobian
      reducedGradient
      initialStepSize
      x
      l
      j := by
  induction remaining generalizing jStart with
  | zero =>
      -- The empty Step 5 search window cannot return an accepted correction count.
      simp [generalizedReducedGradientFirstResidualAcceptedCorrectionAux] at hfound
  | succ remaining ih =>
      classical
      -- Inspect whether the current correction count already passes the residual test.
      by_cases hAccept :
          generalizedReducedGradientResidualAcceptsAt
            constraint
            εBar
            basicJacobian
            reducedGradient
            initialStepSize
            x
            l
            jStart
      · -- If it does, the auxiliary search returns the current correction count immediately.
        have hjStart : jStart = j := by
          simpa [generalizedReducedGradientFirstResidualAcceptedCorrectionAux, hAccept] using
            hfound
        simpa [hjStart] using hAccept
      · -- Otherwise the search recurses to the next correction count.
        have hnextFound :
            generalizedReducedGradientFirstResidualAcceptedCorrectionAux
                constraint
                εBar
                basicJacobian
                reducedGradient
                initialStepSize
                x
                l
                (jStart + 1)
                remaining =
              some j := by
          simpa [generalizedReducedGradientFirstResidualAcceptedCorrectionAux, hAccept] using
            hfound
        exact ih (jStart := jStart + 1) hnextFound

/-- Helper for Chapter11 Algorithm 11.3.1: the public Step 5 search returns only correction
counts satisfying the Step 5 residual test. -/
theorem firstResidualAcceptedCorrection_eq_some_implies_residualAcceptsAt
    (constraint : Point → BasicPoint) (εBar : ℝ)
    (basicJacobian : Point → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : Point → NonbasicPoint)
    (initialStepSize : Point → ℝ)
    (maxCorrections : ℕ)
    (x : Point) (l : ℕ) {j : ℕ}
    (hfound :
      generalizedReducedGradientFirstResidualAcceptedCorrection
          constraint
          εBar
          basicJacobian
          reducedGradient
          initialStepSize
          maxCorrections
          x
          l =
        some j) :
    generalizedReducedGradientResidualAcceptsAt
      constraint
      εBar
      basicJacobian
      reducedGradient
      initialStepSize
      x
      l
      j := by
  -- The public Step 5 search is the auxiliary search started at correction count `1`.
  simpa [generalizedReducedGradientFirstResidualAcceptedCorrection] using
    firstResidualAcceptedCorrectionAux_eq_some_implies_residualAcceptsAt
      (constraint := constraint)
      (εBar := εBar)
      (basicJacobian := basicJacobian)
      (reducedGradient := reducedGradient)
      (initialStepSize := initialStepSize)
      (x := x)
      (l := l)
      (jStart := 1)
      (remaining := maxCorrections)
      hfound

/-- Helper for Chapter11 Algorithm 11.3.1: if the accepted Step 6/Step 7 search returns a
correction count, that correction count satisfies both the Step 5 residual test and the Step 7
objective-decrease test. -/
theorem acceptedCorrectionAt_eq_some_implies_tests
    (objective : Point → ℝ)
    (constraint : Point → BasicPoint)
    (basicJacobian : Point → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : Point → NonbasicPoint)
    (initialStepSize : Point → ℝ)
    (εBar : ℝ) (maxCorrections : ℕ)
    (x : Point) (l : ℕ) {j : ℕ}
    (haccepted :
      generalizedReducedGradientAcceptedCorrectionAt
          objective
          constraint
          basicJacobian
          reducedGradient
          initialStepSize
          εBar
          maxCorrections
          x
          l =
        some j) :
    generalizedReducedGradientResidualAcceptsAt
        constraint
        εBar
        basicJacobian
        reducedGradient
        initialStepSize
        x
        l
        j ∧
      generalizedReducedGradientObjectiveAcceptsAt
        objective
        constraint
        basicJacobian
        reducedGradient
        initialStepSize
        x
        l
        j := by
  classical
  -- Inspect the first residual-acceptable correction returned by the Step 5 search.
  cases
      hFirst :
        generalizedReducedGradientFirstResidualAcceptedCorrection
          constraint
          εBar
          basicJacobian
          reducedGradient
          initialStepSize
          maxCorrections
          x
          l
    with
  | none =>
      simp [generalizedReducedGradientAcceptedCorrectionAt, hFirst] at haccepted
  | some j0 =>
      -- The accepted search succeeds exactly when the Step 7 objective test also succeeds.
      by_cases hObjective :
          generalizedReducedGradientObjectiveAcceptsAt
            objective
            constraint
            basicJacobian
            reducedGradient
            initialStepSize
            x
            l
            j0
      · have hAcceptedValue :
            (if generalizedReducedGradientObjectiveAcceptsAt
                  objective
                  constraint
                  basicJacobian
                  reducedGradient
                  initialStepSize
                  x
                  l
                  j0 then
                some j0
              else
                none) =
              some j := by
          simpa [generalizedReducedGradientAcceptedCorrectionAt, hFirst] using haccepted
        have hj0some : some j0 = some j := by
          simpa [hObjective] using hAcceptedValue
        have hj0 : j0 = j := by
          injection hj0some
        subst j
        exact ⟨
          firstResidualAcceptedCorrection_eq_some_implies_residualAcceptsAt
            (constraint := constraint)
            (εBar := εBar)
            (basicJacobian := basicJacobian)
            (reducedGradient := reducedGradient)
            (initialStepSize := initialStepSize)
            (maxCorrections := maxCorrections)
            (x := x)
            (l := l)
            hFirst,
          hObjective⟩
      · have : False := by
          have hAcceptedValue :
              (if generalizedReducedGradientObjectiveAcceptsAt
                    objective
                    constraint
                    basicJacobian
                    reducedGradient
                    initialStepSize
                    x
                    l
                    j0 then
                  some j0
                else
                  none) =
                some j := by
            simpa [generalizedReducedGradientAcceptedCorrectionAt, hFirst] using haccepted
          simp [hObjective] at hAcceptedValue
        exact this.elim

/-- The Step 4 nonbasic trial attached to stage `k` and backtracking count `l` uses the stage
data `x_k`, `g̃_k`, and `α_k⁽⁰⁾`. -/
def generalizedReducedGradientStageTrialNonbasic
    (iterate : ℕ → Point)
    (reducedGradient : ℕ → NonbasicPoint)
    (initialStepSize : ℕ → ℝ)
    (k l : ℕ) : NonbasicPoint :=
  generalizedReducedGradientTrialNonbasic
    (iterate k).2
    (reducedGradient k)
    (generalizedReducedGradientTrialStepSize (initialStepSize k) l)

/-- The Step 5 basic correction iteration attached to stage `k` and backtracking count `l`
starts from `(x_k)_B` and uses the stage data `A_B`, `g̃_k`, and `α_k⁽⁰⁾`. -/
def generalizedReducedGradientStageTrialBasic
    (constraint : Point → BasicPoint)
    (basicJacobian : ℕ → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : ℕ → NonbasicPoint)
    (initialStepSize : ℕ → ℝ)
    (iterate : ℕ → Point)
    (k l : ℕ) : ℕ → BasicPoint :=
  generalizedReducedGradientTrialBasicAt
    constraint
    (fun _ ↦ basicJacobian k)
    (fun _ ↦ reducedGradient k)
    (fun _ ↦ initialStepSize k)
    (iterate k)
    l

/-- The Step 4/Step 5 trial point attached to stage `k`, backtracking count `l`, and correction
count `j` is the pair formed from the `j`-th Step 5 basic correction and the Step 4 nonbasic
trial at stage `k`. -/
def generalizedReducedGradientStageTrialPoint
    (constraint : Point → BasicPoint)
    (basicJacobian : ℕ → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : ℕ → NonbasicPoint)
    (initialStepSize : ℕ → ℝ)
    (iterate : ℕ → Point)
    (k l j : ℕ) : Point :=
  generalizedReducedGradientTrialPoint
    (generalizedReducedGradientStageTrialBasic
      constraint
      basicJacobian
      reducedGradient
      initialStepSize
      iterate)
    (generalizedReducedGradientStageTrialNonbasic
      iterate
      reducedGradient
      initialStepSize)
    k
    l
    j

/-- The Step 5 search at stage `k` and backtracking count `l` returns the first residual-
acceptable correction count among `1, ..., M`, if one exists. -/
def generalizedReducedGradientStageFirstResidualAcceptedCorrection
    (constraint : Point → BasicPoint) (εBar : ℝ)
    (basicJacobian : ℕ → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : ℕ → NonbasicPoint)
    (initialStepSize : ℕ → ℝ)
    (maxCorrections : ℕ)
    (iterate : ℕ → Point)
    (k l : ℕ) : Option ℕ :=
  generalizedReducedGradientFirstResidualAcceptedCorrection
    constraint
    εBar
    (fun _ ↦ basicJacobian k)
    (fun _ ↦ reducedGradient k)
    (fun _ ↦ initialStepSize k)
    maxCorrections
    (iterate k)
    l

/-- The Step 6/Step 7 search at stage `k` and backtracking count `l` returns the first
residual-acceptable correction count when that first residual-acceptable correction also
decreases the objective; otherwise it returns `none`. -/
def generalizedReducedGradientStageAcceptedCorrectionAt
    (objective : Point → ℝ)
    (constraint : Point → BasicPoint)
    (basicJacobian : ℕ → Matrix (Fin basicDim) (Fin basicDim) ℝ)
    (reducedGradient : ℕ → NonbasicPoint)
    (initialStepSize : ℕ → ℝ)
    (εBar : ℝ) (maxCorrections : ℕ)
    (iterate : ℕ → Point)
    (k l : ℕ) : Option ℕ :=
  generalizedReducedGradientAcceptedCorrectionAt
    objective
    constraint
    (fun _ ↦ basicJacobian k)
    (fun _ ↦ reducedGradient k)
    (fun _ ↦ initialStepSize k)
    εBar
    maxCorrections
    (iterate k)
    l

/-- Data for Chapter11 Algorithm 11.3.1: the generalized reduced-gradient method on the split
space records a feasible initial point `x₁ ∈ X`, tolerances `ε ≥ 0` and `ε̄ > 0`, a positive
integer correction bound `M`, and stagewise data `x_k`, `A_B`, `A_N`, `λ_k`, `g̃_k`,
`α_k⁽⁰⁾`, the accepted Step 6 backtracking count, and the accepted Step 5 correction count.
The Step 4 nonbasic trial, the Step 5 basic correction loop, and the accepted Step 4/Step 5
trial point are defined below from this stage-indexed data. Step 2 is required only at active
stages `k`, the continuation rule is recorded by `active (k + 1) ↔ active k ∧ ε < ‖g̃_k‖`,
and the Step 6/Step 7 acceptance data are required only when the algorithm continues from
stage `k` to stage `k + 1`. -/
structure GeneralizedReducedGradientMethod where
  feasibleSet : Set Point
  objective : Point → ℝ
  constraint : Point → BasicPoint
  ε : ℝ
  εBar : ℝ
  maxCorrections : ℕ
  initialPoint : Point
  active : ℕ → Prop
  iterate : ℕ → Point
  basicJacobian : ℕ → Matrix (Fin basicDim) (Fin basicDim) ℝ
  nonbasicJacobian : ℕ → Matrix (Fin nonbasicDim) (Fin basicDim) ℝ
  multiplier : ℕ → BasicPoint
  reducedGradient : ℕ → NonbasicPoint
  initialStepSize : ℕ → ℝ
  acceptedBacktrack : ℕ → ℕ
  acceptedCorrection : ℕ → ℕ
  epsilon_nonneg : 0 ≤ ε
  epsilonBar_pos : 0 < εBar
  maxCorrections_pos : 0 < maxCorrections
  initialPoint_mem : initialPoint ∈ feasibleSet
  active_one : active 1
  iterate_one_eq : iterate 1 = initialPoint
  iterate_mem_feasibleSet :
    ∀ k, 1 ≤ k → active k → iterate k ∈ feasibleSet
  basicJacobian_nonsingular :
    ∀ k, 1 ≤ k → active k → IsUnit (Matrix.det (basicJacobian k))
  stepTwoSpec :
    ∀ k, 1 ≤ k → active k →
      GeneralizedReducedGradientStepTwoSpec
        objective
        constraint
        (iterate k)
        (basicJacobian k)
        (nonbasicJacobian k)
        (multiplier k)
        (reducedGradient k)
  active_succ_iff :
    ∀ k, 1 ≤ k →
      active (k + 1) ↔ active k ∧ ε < ‖reducedGradient k‖
  initialStepSize_pos :
    ∀ k, 1 ≤ k → active (k + 1) → 0 < initialStepSize k
  earlierBacktrackingRejected :
    ∀ k, 1 ≤ k → active (k + 1) →
      ∀ l, l < acceptedBacktrack k →
        GeneralizedReducedGradientEarlierBacktrackRejection
          objective
          iterate
          constraint
          εBar
          maxCorrections
          (generalizedReducedGradientStageTrialBasic
            constraint
            basicJacobian
            reducedGradient
            initialStepSize
            iterate)
          (generalizedReducedGradientStageTrialNonbasic
            iterate
            reducedGradient
            initialStepSize)
          k
          l
  acceptedCorrectionAt_eq_some :
    ∀ k, 1 ≤ k → active (k + 1) →
      generalizedReducedGradientStageAcceptedCorrectionAt
          objective
          constraint
          basicJacobian
          reducedGradient
          initialStepSize
          εBar
          maxCorrections
          iterate
          k
          (acceptedBacktrack k) =
        some (acceptedCorrection k)
  iterate_succ_eq_acceptedTrialPoint :
    ∀ k, 1 ≤ k → active (k + 1) →
      iterate (k + 1) =
        generalizedReducedGradientStageTrialPoint
          constraint
          basicJacobian
          reducedGradient
          initialStepSize
          iterate
          k
          (acceptedBacktrack k)
          (acceptedCorrection k)

namespace GeneralizedReducedGradientMethod

local notation "Method" =>
  @_root_.GeneralizedReducedGradientMethod basicDim nonbasicDim

/-- The Step 4 nonbasic trial attached to stage `k` and backtracking count `l`. -/
def trialNonbasic (method : Method) (k l : ℕ) : NonbasicPoint :=
  generalizedReducedGradientStageTrialNonbasic
    method.iterate
    method.reducedGradient
    method.initialStepSize
    k
    l

/-- The Step 5 basic correction iteration attached to stage `k` and backtracking count `l`. -/
def trialBasic (method : Method) (k l : ℕ) : ℕ → BasicPoint :=
  generalizedReducedGradientStageTrialBasic
    method.constraint
    method.basicJacobian
    method.reducedGradient
    method.initialStepSize
    method.iterate
    k
    l

/-- The Step 4/Step 5 trial point attached to stage `k`, backtracking count `l`, and correction
count `j`. -/
def trialPoint (method : Method) (k l j : ℕ) : Point :=
  generalizedReducedGradientStageTrialPoint
    method.constraint
    method.basicJacobian
    method.reducedGradient
    method.initialStepSize
    method.iterate
    k
    l
    j

/-- The Step 5 search attached to stage `k` and a fixed backtracking count `l` returns the first
residual-acceptable correction count if one exists among `1, ..., M`. -/
def firstResidualAcceptedCorrection
    (method : Method) (k l : ℕ) : Option ℕ :=
  generalizedReducedGradientStageFirstResidualAcceptedCorrection
    method.constraint
    method.εBar
    method.basicJacobian
    method.reducedGradient
    method.initialStepSize
    method.maxCorrections
    method.iterate
    k
    l

/-- The Step 6/Step 7 search attached to stage `k` and a fixed backtracking count `l`
returns the first residual-acceptable correction count when that first residual-acceptable
correction also decreases the objective; otherwise it returns `none`. -/
def acceptedCorrectionAt
    (method : Method) (k l : ℕ) : Option ℕ :=
  generalizedReducedGradientStageAcceptedCorrectionAt
    method.objective
    method.constraint
    method.basicJacobian
    method.reducedGradient
    method.initialStepSize
    method.εBar
    method.maxCorrections
    method.iterate
    k
    l

/-- The accepted Step 6 steplength at a continuing stage is the initial steplength `α_k⁽⁰⁾`
after the recorded number of halvings. -/
def acceptedTrialStepSize (method : Method) (k : ℕ) : ℝ :=
  generalizedReducedGradientTrialStepSize
    (method.initialStepSize k)
    (method.acceptedBacktrack k)

/-- The accepted Step 4/Step 5 trial point at a continuing stage is obtained from the accepted
backtracking count and accepted correction count recorded at that stage. -/
def acceptedTrialPoint (method : Method) (k : ℕ) : Point :=
  method.trialPoint
    k
    (method.acceptedBacktrack k)
    (method.acceptedCorrection k)

/-- The accepted correction count is exactly the value returned by
`method.acceptedCorrectionAt k (method.acceptedBacktrack k)`. -/
theorem acceptedCorrection_spec
    (method : Method)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hnext : method.active (k + 1)) :
    method.acceptedCorrectionAt k (method.acceptedBacktrack k) =
      some (method.acceptedCorrection k) := by
  -- This is the stored Step 6/Step 7 acceptance datum for stage `k`.
  simpa [acceptedCorrectionAt] using method.acceptedCorrectionAt_eq_some k hk hnext

/-- `method` can be evaluated as its iterate sequence `x_k`. -/
instance : CoeFun Method (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- Evaluating `method` as a function returns its iterate sequence. -/
theorem coe_apply (method : Method) (k : ℕ) :
    method k = method.iterate k := by
  -- Coercing `method` to a function exposes its iterate sequence.
  rfl

/-- The stage `k = 1` iterate of `method` is the Step 1 initial point `x₁`. -/
theorem iterate_one (method : Method) :
    method.iterate 1 = method.initialPoint := by
  -- Step 1 stores the initial iterate as the initial point.
  exact method.iterate_one_eq

/-- The stage `k = 1` iterate of `method` is feasible because it is the source initial point
`x₁ ∈ X`. -/
theorem iterate_one_mem_feasibleSet (method : Method) :
    method.iterate 1 ∈ method.feasibleSet := by
  -- The initial iterate is feasible because it is exactly the recorded initial point.
  simpa [method.iterate_one] using method.initialPoint_mem

/-- Algorithm 11.3.1 is terminated at stage `k` when the Step 3 stopping test
`‖g̃_k‖ ≤ ε` holds at `x_k`. -/
def terminatedAt (method : Method) (k : ℕ) : Prop :=
  ‖method.reducedGradient k‖ ≤ method.ε

/-- Unfolding `method.terminatedAt k` gives the Step 3 stopping test `‖g̃_k‖ ≤ ε`. -/
theorem terminatedAt_iff (method : Method) (k : ℕ) :
    method.terminatedAt k ↔ ‖method.reducedGradient k‖ ≤ method.ε := by
  -- `terminatedAt` is defined by the Step 3 norm test.
  rfl

/-- At an active stage, the algorithm continues to stage `k + 1` exactly when stage `k` is not
terminated. -/
theorem active_succ_iff_not_terminatedAt (method : Method) {k : ℕ} (hk : 1 ≤ k) :
    method.active (k + 1) ↔ method.active k ∧ ¬ method.terminatedAt k := by
  -- Route correction: the stored field is parsed as an `↔` whose left side is
  -- `1 ≤ k → method.active (k + 1)`, so we first rewrite that proposition explicitly.
  have hActiveSucc :
      (1 ≤ k → method.active (k + 1)) ↔
        method.active k ∧ method.ε < ‖method.reducedGradient k‖ := by
    simpa using method.active_succ_iff k
  constructor
  · -- Any active next stage yields the left side of the stored continuation equivalence.
    intro hnext
    have hContinue := hActiveSucc.mp (fun _ ↦ hnext)
    simpa [terminatedAt, not_le] using hContinue
  · -- Conversely, the stored continuation equivalence returns `active (k + 1)` once `hk` is fixed.
    intro hContinue
    have hContinue' : method.active k ∧ method.ε < ‖method.reducedGradient k‖ := by
      simpa [terminatedAt, not_le] using hContinue
    exact hActiveSucc.mpr hContinue' hk

/-- The accepted Step 6 steplength at a continuing stage is positive. -/
theorem acceptedTrialStepSize_pos
    (method : Method)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hnext : method.active (k + 1)) :
    0 < method.acceptedTrialStepSize k := by
  -- The accepted Step 6 steplength is the positive initial steplength divided by `2^l`.
  change
    0 <
      method.initialStepSize k / ((2 : ℝ) ^ method.acceptedBacktrack k)
  exact div_pos
    (method.initialStepSize_pos k hk hnext)
    (pow_pos (by norm_num) _)

/-- Chapter11 Algorithm 11.3.1: at a continuing stage, the accepted trial point satisfies the
Step 5 residual test `‖c(x_B, x_N)‖ ≤ ε̄`. -/
theorem acceptedTrialPoint_residual_small
    (method : Method)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hnext : method.active (k + 1)) :
    generalizedReducedGradientResidualAccepts
      method.constraint
      method.εBar
      method.trialBasic
      method.trialNonbasic
      k
      (method.acceptedBacktrack k)
      (method.acceptedCorrection k) := by
  -- Extract the Step 5 residual test from the accepted Step 6/Step 7 search result.
  have htests :=
    acceptedCorrectionAt_eq_some_implies_tests
      (objective := method.objective)
      (constraint := method.constraint)
      (basicJacobian := fun _ ↦ method.basicJacobian k)
      (reducedGradient := fun _ ↦ method.reducedGradient k)
      (initialStepSize := fun _ ↦ method.initialStepSize k)
      (εBar := method.εBar)
      (maxCorrections := method.maxCorrections)
      (x := method.iterate k)
      (l := method.acceptedBacktrack k)
      (j := method.acceptedCorrection k)
      (by
        simpa [acceptedCorrectionAt, generalizedReducedGradientStageAcceptedCorrectionAt] using
          method.acceptedCorrection_spec hk hnext)
  -- Reinterpret the extracted Step 5 fact through the stage-specific trial-point aliases.
  simpa [GeneralizedReducedGradientMethod.trialBasic,
    GeneralizedReducedGradientMethod.trialNonbasic, generalizedReducedGradientResidualAccepts,
    generalizedReducedGradientResidualAcceptsAt, generalizedReducedGradientTrialPointAt,
    generalizedReducedGradientStageTrialPoint, generalizedReducedGradientTrialPoint,
    generalizedReducedGradientStageTrialBasic, generalizedReducedGradientStageTrialNonbasic,
    generalizedReducedGradientTrialNonbasicAt, generalizedReducedGradientTrialStepSize] using
    htests.1

/-- At a continuing stage, the accepted trial point strictly decreases the objective value. -/
theorem acceptedTrialPoint_objectiveDecrease
    (method : Method)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hnext : method.active (k + 1)) :
    generalizedReducedGradientObjectiveAccepts
      method.objective
      method.iterate
      method.trialBasic
      method.trialNonbasic
      k
      (method.acceptedBacktrack k)
      (method.acceptedCorrection k) := by
  -- Extract the Step 7 objective-decrease test from the accepted Step 6/Step 7 search result.
  have htests :=
    acceptedCorrectionAt_eq_some_implies_tests
      (objective := method.objective)
      (constraint := method.constraint)
      (basicJacobian := fun _ ↦ method.basicJacobian k)
      (reducedGradient := fun _ ↦ method.reducedGradient k)
      (initialStepSize := fun _ ↦ method.initialStepSize k)
      (εBar := method.εBar)
      (maxCorrections := method.maxCorrections)
      (x := method.iterate k)
      (l := method.acceptedBacktrack k)
      (j := method.acceptedCorrection k)
      (by
        simpa [acceptedCorrectionAt, generalizedReducedGradientStageAcceptedCorrectionAt] using
          method.acceptedCorrection_spec hk hnext)
  -- Reinterpret the extracted Step 7 fact through the stage-specific trial-point aliases.
  simpa [GeneralizedReducedGradientMethod.trialBasic,
    GeneralizedReducedGradientMethod.trialNonbasic, generalizedReducedGradientObjectiveAccepts,
    generalizedReducedGradientObjectiveAcceptsAt, generalizedReducedGradientTrialPointAt,
    generalizedReducedGradientStageTrialPoint, generalizedReducedGradientTrialPoint,
    generalizedReducedGradientStageTrialBasic, generalizedReducedGradientStageTrialNonbasic,
    generalizedReducedGradientTrialNonbasicAt, generalizedReducedGradientTrialStepSize] using
    htests.2

/-- At a continuing stage, the accepted trial point is feasible. -/
theorem acceptedTrialPoint_mem_feasibleSet
    (method : Method)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hnext : method.active (k + 1)) :
    method.acceptedTrialPoint k ∈ method.feasibleSet := by
  -- The next iterate is feasible at every continuing stage.
  have hmem : method.iterate (k + 1) ∈ method.feasibleSet :=
    method.iterate_mem_feasibleSet (k + 1) (Nat.succ_le_succ (Nat.zero_le k)) hnext
  -- Step 7 records that this next iterate is exactly the accepted trial point.
  have hEq : method.iterate (k + 1) = method.acceptedTrialPoint k := by
    simpa [acceptedTrialPoint, trialPoint] using
      method.iterate_succ_eq_acceptedTrialPoint k hk hnext
  simpa [hEq] using hmem

/-- If the Step 3 stopping test already holds at an active stage `k`, the algorithm does not
continue to stage `k + 1`. -/
theorem nextState_eq_self_of_terminatedAtState
    (method : Method)
    {k : ℕ}
    (hk : 1 ≤ k)
    (_hactive : method.active k)
    (hstop : method.terminatedAt k) :
    ¬ method.active (k + 1) := by
  -- A terminated active stage cannot satisfy the continuation criterion.
  intro hnext
  exact ((method.active_succ_iff_not_terminatedAt hk).1 hnext).2 hstop

/-- If the Step 3 stopping test fails and the algorithm continues, then the next iterate
`x_(k + 1)` is the accepted Step 4/Step 5 trial point. -/
theorem nextState_eq_acceptedTrialPoint_of_not_terminatedAtState
    (method : Method)
    {k : ℕ}
    (hk : 1 ≤ k)
    (hnext : method.active (k + 1)) :
    method.iterate (k + 1) = method.acceptedTrialPoint k := by
  -- The recorded next iterate is the accepted Step 4/Step 5 trial point.
  simpa [acceptedTrialPoint, trialPoint] using
    method.iterate_succ_eq_acceptedTrialPoint k hk hnext

end GeneralizedReducedGradientMethod

/-- The convergence-relevant data of a generalized reduced-gradient run: objective and
constraint maps, the Step 2 Jacobian and reduced-gradient data along the active iterate
sequence, and the Step 3 steplength data. This owner omits the Step 5/Step 6 control counters
used to construct accepted trial points in Algorithm 11.3.1. -/
structure GeneralizedReducedGradientRun where
  feasibleSet : Set Point
  objective : Point → ℝ
  constraint : Point → BasicPoint
  ε : ℝ
  active : ℕ → Prop
  iterate : ℕ → Point
  basicJacobian : ℕ → Matrix (Fin basicDim) (Fin basicDim) ℝ
  nonbasicJacobian : ℕ → Matrix (Fin nonbasicDim) (Fin basicDim) ℝ
  multiplier : ℕ → BasicPoint
  reducedGradient : ℕ → NonbasicPoint
  initialStepSize : ℕ → ℝ
  iterate_mem_feasibleSet :
    ∀ k, 1 ≤ k → active k → iterate k ∈ feasibleSet
  basicJacobian_nonsingular :
    ∀ k, 1 ≤ k → active k → IsUnit (Matrix.det (basicJacobian k))
  stepTwoSpec :
    ∀ k, 1 ≤ k → active k →
      GeneralizedReducedGradientStepTwoSpec
        objective
        constraint
        (iterate k)
        (basicJacobian k)
        (nonbasicJacobian k)
        (multiplier k)
        (reducedGradient k)
  active_succ_iff :
    ∀ k, 1 ≤ k →
      active (k + 1) ↔ active k ∧ ε < ‖reducedGradient k‖

/-- A generalized reduced-gradient run together with the accepted Step 4/Step 5 trial point and
accepted Step 6 steplength at each continuing stage. This owner keeps the accepted objects
themselves together with the residual-small and objective-decrease conditions that make them the
accepted Step 5/Step 7 outputs, rather than the bookkeeping counters used to generate them. -/
local notation "BaseRun" =>
  @_root_.GeneralizedReducedGradientRun basicDim nonbasicDim

structure GeneralizedReducedGradientAcceptedStepRun extends
    BaseRun where
  εBar : ℝ
  acceptedTrialPoint : ℕ → Point
  acceptedTrialStepSize : ℕ → ℝ
  epsilonBar_pos : 0 < εBar
  acceptedTrialStepSize_pos :
    ∀ k, 1 ≤ k → active (k + 1) → 0 < acceptedTrialStepSize k
  acceptedTrialPoint_residual_small :
    ∀ k, 1 ≤ k → active (k + 1) →
      ‖constraint (acceptedTrialPoint k)‖ ≤ εBar
  acceptedTrialPoint_objectiveDecrease :
    ∀ k, 1 ≤ k → active (k + 1) →
      objective (acceptedTrialPoint k) < objective (iterate k)
  iterate_succ_eq_acceptedTrialPoint :
    ∀ k, 1 ≤ k → active (k + 1) → iterate (k + 1) = acceptedTrialPoint k

namespace GeneralizedReducedGradientRun

local notation "Run" =>
  @_root_.GeneralizedReducedGradientRun basicDim nonbasicDim

/-- The Step 2 inverse blocks `A_B(x_k)⁻¹` are uniformly bounded above along the active stages
of the run. -/
def uniformlyBoundedBasicJacobianInverse (run : Run) : Prop :=
  ∃ C ∈ Set.Ici (0 : ℝ),
    ∀ k, 1 ≤ k → run.active k → ‖(run.basicJacobian k)⁻¹‖ ≤ C

/-- The Step 3 initial trial steplengths satisfy the source lower-bound condition `(11.3.6)`:
there is a constant `δ₀ > 0` with `δ₀ * ‖g̃_k‖ ≤ α_k⁽⁰⁾` at every continuing stage. -/
def initialStepSizeLowerBoundByReducedGradient (run : Run) : Prop :=
  ∃ δ0 ∈ Set.Ioi (0 : ℝ),
    ∀ k, 1 ≤ k → run.active (k + 1) →
      δ0 * ‖run.reducedGradient k‖ ≤ run.initialStepSize k

/-- The Step 3 initial trial steplengths satisfy the source divergence condition `(11.3.7)`:
the partial sums `∑_{k=1}^N α_k⁽⁰⁾ / ‖g̃_k‖` diverge to `+∞`. -/
def initialStepSizeOverReducedGradientNormPartialSumsDiverge
    (run : Run) : Prop :=
  Tendsto
    (fun N : ℕ ↦
      Finset.sum (Finset.Icc 1 N) fun k ↦
        run.initialStepSize k / ‖run.reducedGradient k‖)
    atTop
    atTop

end GeneralizedReducedGradientRun

namespace GeneralizedReducedGradientMethod

local notation "Method" =>
  @_root_.GeneralizedReducedGradientMethod basicDim nonbasicDim
local notation "Run" =>
  @_root_.GeneralizedReducedGradientRun basicDim nonbasicDim
local notation "AcceptedStepRun" =>
  @_root_.GeneralizedReducedGradientAcceptedStepRun basicDim nonbasicDim

/-- Forget the Step 5/Step 6 search bookkeeping and retain the convergence-relevant run data. -/
def toRun (method : Method) : Run where
  feasibleSet := method.feasibleSet
  objective := method.objective
  constraint := method.constraint
  ε := method.ε
  active := method.active
  iterate := method.iterate
  basicJacobian := method.basicJacobian
  nonbasicJacobian := method.nonbasicJacobian
  multiplier := method.multiplier
  reducedGradient := method.reducedGradient
  initialStepSize := method.initialStepSize
  iterate_mem_feasibleSet := method.iterate_mem_feasibleSet
  basicJacobian_nonsingular := method.basicJacobian_nonsingular
  stepTwoSpec := method.stepTwoSpec
  active_succ_iff := method.active_succ_iff

/-- Forget the Step 5/Step 6 search bookkeeping and retain only the accepted point and accepted
steplength attached to each continuing stage, together with the Step 5 residual test and Step 7
objective-decrease facts that justify those accepted objects. -/
def toAcceptedStepRun
    (method : Method) : AcceptedStepRun where
  toGeneralizedReducedGradientRun := method.toRun
  εBar := method.εBar
  acceptedTrialPoint := method.acceptedTrialPoint
  acceptedTrialStepSize := method.acceptedTrialStepSize
  epsilonBar_pos := method.epsilonBar_pos
  acceptedTrialStepSize_pos := fun k hk hnext ↦ by
    simpa [toRun] using method.acceptedTrialStepSize_pos hk hnext
  acceptedTrialPoint_residual_small := fun k hk hnext ↦ by
    simpa [toRun, GeneralizedReducedGradientMethod.acceptedTrialPoint,
      GeneralizedReducedGradientMethod.trialPoint, GeneralizedReducedGradientMethod.trialBasic,
      GeneralizedReducedGradientMethod.trialNonbasic, generalizedReducedGradientResidualAccepts,
      generalizedReducedGradientStageTrialPoint, generalizedReducedGradientTrialPoint,
      generalizedReducedGradientStageTrialBasic, generalizedReducedGradientStageTrialNonbasic] using
      method.acceptedTrialPoint_residual_small hk hnext
  acceptedTrialPoint_objectiveDecrease := fun k hk hnext ↦ by
    simpa [toRun, GeneralizedReducedGradientMethod.acceptedTrialPoint,
      GeneralizedReducedGradientMethod.trialPoint, GeneralizedReducedGradientMethod.trialBasic,
      GeneralizedReducedGradientMethod.trialNonbasic, generalizedReducedGradientObjectiveAccepts,
      generalizedReducedGradientStageTrialPoint, generalizedReducedGradientTrialPoint,
      generalizedReducedGradientStageTrialBasic, generalizedReducedGradientStageTrialNonbasic] using
      method.acceptedTrialPoint_objectiveDecrease hk hnext
  iterate_succ_eq_acceptedTrialPoint := fun k hk hnext ↦ by
    simpa [toRun] using method.nextState_eq_acceptedTrialPoint_of_not_terminatedAtState hk hnext

end GeneralizedReducedGradientMethod

end Chapter11Algorithm1131
