/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Definition_4_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_2_extra_1
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

-- Source/core/bridge triage for this file:
-- * source-facing: the Chapter 5.1 DFP exact-line-search theorem statements.
-- * core/canonical: `DfpMethod` from Algorithm 5.1.4, together with its source-facing stage
--   predicate `A.GeneratedThrough`.
-- * bridge/view: the theorem-specific exact-line-search predicate below adds only the
--   zero-tolerance and Hessian hypotheses on top of the upstream exact-line-search owner on the
--   nonnegative ray.
-- Semantic recall note: `lean_leansearch` did not surface a reusable quadratic-termination
-- owner for exact-line-search DFP, so this file keeps the local `DfpMethod`-based statement API.

section

variable {n : ℕ}

section ExactLineSearchDfpMethod

variable {G : Matrix (Fin n) (Fin n) ℝ} {b : EuclideanSpace ℝ (Fin n)} {c : ℝ}

-- This file only needs the explicit quadratic objective, not the broader Chapter 4 theorem
-- package that also owns its gradient and conjugate-direction API.
def dfpQuadraticObjective
    (G : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * dotProduct x (Matrix.toEuclideanLin G x) + dotProduct b x + c

namespace DfpMethod

/-- An exact-line-search DFP method for the quadratic objective
`x ↦ 1 / 2 * xᵀ G x + bᵀ x + c` is a DFP run with zero stopping tolerance and
positive-definite quadratic Hessian `G`, reusing the upstream exact-line-search owner on the
nonnegative ray. The DFP denominator and matrix-update data are already owned by `DfpMethod`
itself. -/
def IsExactLineSearchOnQuadratic
    (G : Matrix (Fin n) (Fin n) ℝ) (b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (A : DfpMethod (dfpQuadraticObjective G b c)) : Prop :=
  A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay ∧ A.ε = 0 ∧ G.PosDef

namespace IsExactLineSearchOnQuadratic

/-- Unfolding `A.IsExactLineSearchOnQuadratic G b c` gives exact line search, zero stopping
tolerance, and positive-definite quadratic Hessian data. -/
theorem iff
    {A : DfpMethod (dfpQuadraticObjective G b c)} :
    A.IsExactLineSearchOnQuadratic G b c ↔
      A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay ∧ A.ε = 0 ∧ G.PosDef :=
  Iff.rfl

/-- Exact-line-search DFP quadratic data include exact line search on the nonnegative ray. -/
theorem toHasExactLineSearchOnNonnegativeRay
    {A : DfpMethod (dfpQuadraticObjective G b c)} (hDFP : A.IsExactLineSearchOnQuadratic G b c) :
    A.toGeneralQuasiNewtonMethod.HasExactLineSearchOnNonnegativeRay :=
  hDFP.1

/-- Exact-line-search DFP quadratic data force zero stopping tolerance. -/
@[simp] theorem epsilon_eq_zero
    {A : DfpMethod (dfpQuadraticObjective G b c)} (hDFP : A.IsExactLineSearchOnQuadratic G b c) :
    A.ε = 0 :=
  hDFP.2.1

/-- Exact-line-search DFP quadratic data include the positive-definite quadratic Hessian. -/
theorem posDef
    {A : DfpMethod (dfpQuadraticObjective G b c)} (hDFP : A.IsExactLineSearchOnQuadratic G b c) :
    G.PosDef :=
  hDFP.2.2

/-- A nonterminal exact-line-search DFP step has exact line search, admissible secant
denominators, and the explicit DFP inverse update formula. -/
theorem stepSpec
    {A : DfpMethod (dfpQuadraticObjective G b c)} (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {k : ℕ}
    (hk : A.ε < ‖A.g k‖) :
    IsMinOn (lineSearchObjective (dfpQuadraticObjective G b c) (A k) (A.d k)) (Set.Ici 0) (A.α k) ∧
      dotProduct (A (k + 1) - A k) (A.g (k + 1) - A.g k) ≠ 0 ∧
      dotProduct (A.g (k + 1) - A.g k) ((A.matrix k).mulVec (A.g (k + 1) - A.g k)) ≠ 0 ∧
      A.matrix (k + 1) =
        dfpInverseUpdate (A.matrix k) (A (k + 1) - A k) (A.g (k + 1) - A.g k) :=
  let hStep := DfpMethod.stepSpec A hk
  ⟨hDFP.toHasExactLineSearchOnNonnegativeRay.isMinOn k,
    hStep.2.2.2.2.1, hStep.2.2.2.2.2.1, hStep.2.2.2.2.2.2⟩

end IsExactLineSearchOnQuadratic

/-- The predicate `IsExactLineSearchOnQuadratic` is proof-irrelevant. -/
instance isExactLineSearchOnQuadratic_subsingleton
    {A : DfpMethod (dfpQuadraticObjective G b c)} :
    Subsingleton (A.IsExactLineSearchOnQuadratic G b c) := inferInstance

end DfpMethod

open DfpMethod
open DfpMethod.IsExactLineSearchOnQuadratic

namespace DfpMethod

/-- Helper for Chapter05 Theorem 5.1.7: pairing a matrix action against a second vector moves
the matrix to the transpose side of the Euclidean dot product. -/
theorem dotProduct_toEuclideanLin_eq_transpose
    (A : Matrix (Fin n) (Fin n) ℝ)
    (u v : EuclideanSpace ℝ (Fin n)) :
    dotProduct (Matrix.toEuclideanLin A u) v =
      dotProduct u (Matrix.toEuclideanLin A.transpose v) := by
  -- Rewrite the Euclidean pairings to the matrix `dotProduct` identity with `Aᵀ`.
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, dotProduct_comm] using
    (Matrix.dotProduct_transpose_mulVec (A := A) (x := u.ofLp) (y := v.ofLp)).symm

/-- Helper for Chapter05 Theorem 5.1.7: a symmetric matrix acts symmetrically inside the
Euclidean dot product. -/
theorem dotProduct_toEuclideanLin_of_isSymm
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (u v : EuclideanSpace ℝ (Fin n)) :
    dotProduct (Matrix.toEuclideanLin A u) v =
      dotProduct u (Matrix.toEuclideanLin A v) := by
  -- Rewrite the transpose action away once and stay at the matrix-action layer.
  simpa [hA.eq] using dotProduct_toEuclideanLin_eq_transpose A u v

/-- Helper for Chapter05 Theorem 5.1.7: along the quadratic objective, each secant vector is
the Hessian action on the corresponding DFP step. -/
theorem quadraticSecant_eq_hessianStep
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    (k : ℕ) :
    A.g (k + 1) - A.g k = Matrix.toEuclideanLin G (A (k + 1) - A k) := by
  have hGsymm : G.IsSymm := posDef_isSymm hDFP.posDef
  have hgk1 : A.g (k + 1) = Matrix.toEuclideanLin G (A (k + 1)) + b := by
    -- Identify the recorded gradient at stage `k + 1` with the quadratic gradient formula.
    calc
      A.g (k + 1) = gradient (quadraticObjective G b c) (A (k + 1)) := by
        symm
        exact A.toGeneralQuasiNewtonMethod.gradient_eq (k + 1)
      _ = Matrix.toEuclideanLin G (A (k + 1)) + b := by
        simpa [dfpQuadraticObjective, quadraticObjective] using
          gradient_quadraticObjective G b c hGsymm (A (k + 1))
  have hgk : A.g k = Matrix.toEuclideanLin G (A k) + b := by
    -- The same quadratic gradient identification holds at stage `k`.
    calc
      A.g k = gradient (quadraticObjective G b c) (A k) := by
        symm
        exact A.toGeneralQuasiNewtonMethod.gradient_eq k
      _ = Matrix.toEuclideanLin G (A k) + b := by
        simpa [dfpQuadraticObjective, quadraticObjective] using
          gradient_quadraticObjective G b c hGsymm (A k)
  -- Subtract the two explicit quadratic gradients.
  calc
    A.g (k + 1) - A.g k
        = (Matrix.toEuclideanLin G (A (k + 1)) + b) - (Matrix.toEuclideanLin G (A k) + b) := by
            rw [hgk1, hgk]
    _ = Matrix.toEuclideanLin G (A (k + 1) - A k) := by
          simp

/-- Helper for Chapter05 Theorem 5.1.7: on a nonterminal quadratic DFP stage, the realized step
cannot vanish. Otherwise both DFP update denominators would collapse. -/
theorem step_ne_zero
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {k : ℕ} (hk : A.ε < ‖A.g k‖) :
    A (k + 1) - A k ≠ 0 := by
  intro hs
  rcases hDFP.stepSpec hk with ⟨_, hsy, _, _⟩
  have hy : A.g (k + 1) - A.g k = 0 := by
    simpa [hs] using quadraticSecant_eq_hessianStep (A := A) hDFP k
  exact hsy <| by simp [hs]

/-- Helper for Chapter05 Theorem 5.1.7: exact line search along the recorded DFP direction
reparameterizes to exact line search along the realized displacement with step length `1`. -/
theorem exactLineSearch_onRealizedStep
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    (k : ℕ) :
    IsExactLineSearchStepOnNonnegativeRay
      (dfpQuadraticObjective G b c) (A k) (A (k + 1) - A k) 1 := by
  by_cases hTerm : A.terminatedAt k
  · rw [isExactLineSearchStepOnNonnegativeRay_iff]
    constructor
    · norm_num
    -- After termination the iterate is frozen, so the realized-step profile is constant.
    intro α hα
    have hx : A (k + 1) = A k := A.x_eq_succ_of_terminatedAt hTerm
    simp [hx, lineSearchObjective_apply]
  · have hk : A.ε < ‖A.g k‖ := lt_of_not_ge hTerm
    have hα_pos : 0 < A.α k := (A.stepSpec hk).2.1
    have hStep : A (k + 1) - A k = A.α k • A.d k := by
      have hUpdate : A (k + 1) = A k + A.α k • A.d k := (A.stepSpec hk).2.2.1
      -- Rewrite the realized displacement through the recorded iterate update.
      calc
        A (k + 1) - A k = (A k + A.α k • A.d k) - A k := by rw [hUpdate]
        _ = A.α k • A.d k := by abel
    rw [isExactLineSearchStepOnNonnegativeRay_iff]
    constructor
    · norm_num
    -- Reparameterize the original line-search ray by the positive scalar `A.α k`.
    intro α hα
    have hOpt :
        lineSearchObjective (dfpQuadraticObjective G b c) (A k) (A.d k) (A.α k) ≤
          lineSearchObjective (dfpQuadraticObjective G b c) (A k) (A.d k) (A.α k * α) := by
      exact (isMinOn_iff.mp (hDFP.toHasExactLineSearchOnNonnegativeRay.isMinOn k)) _
        (mul_nonneg hα_pos.le hα)
    simpa [hStep, lineSearchObjective_apply, one_smul, smul_smul, mul_assoc, mul_left_comm,
      mul_comm] using hOpt

/-- Helper for Chapter05 Theorem 5.1.7: exact line search on the realized DFP step makes the
next gradient orthogonal to that realized displacement. -/
theorem exactLineSearch_nextGradient_orthogonalToStep
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {k : ℕ} (_hGenerated : A.GeneratedThrough (k + 1)) :
    dotProduct (A.g (k + 1)) (A (k + 1) - A k) = 0 := by
  have hDerivZero :
      deriv (lineSearchObjective (dfpQuadraticObjective G b c) (A k) (A (k + 1) - A k)) 1 = 0 := by
    have hRealized :
        IsExactLineSearchStepOnNonnegativeRay
          (dfpQuadraticObjective G b c) (A k) (A (k + 1) - A k) 1 :=
      exactLineSearch_onRealizedStep (A := A) hDFP k
    have hlocal :
        IsLocalMin
          (lineSearchObjective (dfpQuadraticObjective G b c) (A k) (A (k + 1) - A k)) 1 :=
      hRealized.isMinOn.isLocalMin (Ici_mem_nhds (by norm_num : (0 : ℝ) < 1))
    -- The realized step length `1` lies in the interior of the nonnegative ray.
    exact hlocal.deriv_eq_zero
  have hGradAt :
      HasGradientAt
        (dfpQuadraticObjective G b c)
        (A.g (k + 1))
        (A k + (1 : ℝ) • (A (k + 1) - A k)) := by
    -- Rewrite the next iterate as the base point plus the realized displacement.
    simpa [broydenStep, one_smul, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      A.hasGradientAt (k + 1)
  have hDeriv :
      deriv (lineSearchObjective (dfpQuadraticObjective G b c) (A k) (A (k + 1) - A k)) 1 =
        dotProduct (A.g (k + 1)) (A (k + 1) - A k) := by
    -- The line-search derivative is the gradient pairing with the realized displacement.
    simpa [PiLp.inner_apply, dotProduct, mul_comm] using
      hGradAt.deriv_lineSearchObjective_apply
        (x := A k) (d := A (k + 1) - A k) (t := (1 : ℝ))
  rw [hDeriv] at hDerivZero
  exact hDerivZero

/-- Helper for Chapter05 Theorem 5.1.7: if a symmetric DFP inverse update has both cross terms
vanishing on `z`, then the rank-two correction acts trivially on `z`. -/
theorem dfpInverseUpdate_mulVec_of_crossOrthogonal
    (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsSymm)
    (s y z : EuclideanSpace ℝ (Fin n))
    (hsz : dotProduct s z = 0)
    (hyHz : dotProduct y (H.mulVec z) = 0) :
    (dfpInverseUpdate H s y).mulVec z = H.mulVec z := by
  have hHy :
      dotProduct (H.mulVec y) z = dotProduct y (H.mulVec z) := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
      dotProduct_toEuclideanLin_of_isSymm hH y z
  -- Expand the DFP update and kill each rank-one correction by the two orthogonality hypotheses.
  calc
    (dfpInverseUpdate H s y).mulVec z
        = H.mulVec z
            + ((dotProduct s y)⁻¹ • Matrix.vecMulVec s s).mulVec z
            - ((dotProduct y (H.mulVec y))⁻¹ •
                Matrix.vecMulVec (H.mulVec y) (H.mulVec y)).mulVec z := by
              simp [dfpInverseUpdate, sub_eq_add_neg, Matrix.add_mulVec, Matrix.neg_mulVec]
    _ = H.mulVec z + 0 - 0 := by
          simp [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hsz, hyHz, hHy]
    _ = H.mulVec z := by
          abel

/-- Helper for Chapter05 Theorem 5.1.7: every generated DFP matrix is symmetric, because the
earlier DFP positivity theorem upgrades directly to symmetry. -/
theorem matrix_isSymm_of_generated
    (A : DfpMethod (dfpQuadraticObjective G b c))
    {k : ℕ} (hGenerated : A.GeneratedThrough k) :
    (A.matrix k).IsSymm := by
  induction k with
  | zero =>
      simpa using A.matrix0_isSymm
  | succ k ih =>
      have hPrev : (A.matrix k).IsSymm :=
        ih (hGenerated.of_le (Nat.le_succ k))
      have hk : A.ε < ‖A.g k‖ := hGenerated.notStopped (Nat.lt_succ_self k)
      rw [A.matrix_update_eq hk]
      simpa [broydenClassInverseUpdate_zero] using
        broydenClassInverseUpdate_isSymm
          hPrev (A (k + 1) - A k) (A.g (k + 1) - A.g k) (0 : ℝ)

/-- Helper for Chapter05 Theorem 5.1.7: at each nonterminal stage, the realized DFP step is the
negative step size times the current inverse-Hessian action on the current gradient. -/
theorem realizedStep_eq_negAlpha_matrixGradient
    (A : DfpMethod (dfpQuadraticObjective G b c))
    {k : ℕ} (hk : A.ε < ‖A.g k‖) :
    A (k + 1) - A k = -(A.α k) • Matrix.toEuclideanLin (A.matrix k) (A.g k) := by
  rcases A.stepSpec hk with ⟨_, _, hx, _, _, _, _⟩
  -- Rewrite the realized displacement through the step update and then substitute the
  -- matrix-model expression for the search direction.
  calc
    A (k + 1) - A k = A.α k • A.d k := by
      rw [hx]
      abel
    _ = A.α k • (-(Matrix.toEuclideanLin (A.matrix k) (A.g k))) := by
      rw [A.direction_eq_matrix hk]
    _ = -(A.α k) • Matrix.toEuclideanLin (A.matrix k) (A.g k) := by
      simp [smul_neg]

/-- Helper for Chapter05 Theorem 5.1.7: once the current matrix is exact on an earlier secant
and the current gradient is orthogonal to the corresponding earlier step, the fresh realized DFP
step is orthogonal to that earlier secant. -/
theorem nextStepDotOldSecant_eq_zero
    (A : DfpMethod (dfpQuadraticObjective G b c)) (_hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {i j : ℕ} (hGenerated : A.GeneratedThrough (i + 2)) (_hj : j ≤ i)
    (hHer :
      Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (j + 1) - A.g j) = A (j + 1) - A j)
    (hOrth : dotProduct (A.g (i + 1)) (A (j + 1) - A j) = 0) :
    dotProduct (A (i + 2) - A (i + 1)) (A.g (j + 1) - A.g j) = 0 := by
  have hk : A.ε < ‖A.g (i + 1)‖ := hGenerated.notStopped (Nat.lt_succ_self (i + 1))
  have hPrefixGen : A.GeneratedThrough (i + 1) := hGenerated.of_le (Nat.le_succ (i + 1))
  have hHsymm : (A.matrix (i + 1)).IsSymm := matrix_isSymm_of_generated (A := A) hPrefixGen
  have hSmul :
      dotProduct (-(A.α (i + 1)) • Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (i + 1)))
        (A.g (j + 1) - A.g j)
        =
          -(A.α (i + 1)) *
            dotProduct (Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (i + 1)))
              (A.g (j + 1) - A.g j) := by
    simpa [dotProduct] using
      smul_dotProduct
        (-(A.α (i + 1)))
        ((Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (i + 1))).ofLp)
        ((A.g (j + 1) - A.g j).ofLp)
  have hSymmDot :
      dotProduct (Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (i + 1)))
        (A.g (j + 1) - A.g j)
        =
          dotProduct (A.g (i + 1))
            (Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (j + 1) - A.g j)) :=
    dotProduct_toEuclideanLin_of_isSymm hHsymm (A.g (i + 1)) (A.g (j + 1) - A.g j)
  have hHerDot :
      dotProduct (A.g (i + 1))
        (Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (j + 1) - A.g j))
        =
          dotProduct (A.g (i + 1)) (A (j + 1) - A j) := by
    simpa [dotProduct] using
      congrArg
        (fun v : Fin n → ℝ ↦ (A.g (i + 1)).ofLp ⬝ᵥ v)
        (congrArg WithLp.ofLp hHer)
  have hOrth' : dotProduct (A.g (i + 1)) (A (j + 1) - A j) = 0 := by
    simpa [dotProduct] using hOrth
  -- Rewrite the fresh step through the current inverse-Hessian action and then move that action
  -- onto the old secant, where the prefix hereditary clause closes the calculation.
  calc
    dotProduct (A (i + 2) - A (i + 1)) (A.g (j + 1) - A.g j)
        =
          dotProduct (-(A.α (i + 1)) • Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (i + 1)))
            (A.g (j + 1) - A.g j) := by
              rw [realizedStep_eq_negAlpha_matrixGradient (A := A) hk]
    _ =
        -(A.α (i + 1)) *
          dotProduct (Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (i + 1)))
            (A.g (j + 1) - A.g j) := by
              exact hSmul
    _ =
        -(A.α (i + 1)) *
          dotProduct (A.g (i + 1))
            (Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (j + 1) - A.g j)) := by
              rw [hSymmDot]
    _ = -(A.α (i + 1)) * dotProduct (A.g (i + 1)) (A (j + 1) - A j) := by
          rw [hHerDot]
    _ = -(A.α (i + 1)) * 0 := by
          rw [hOrth']
    _ = 0 := by
          ring

/-- Helper for Chapter05 Theorem 5.1.7: once the current matrix is exact on an earlier secant
and the current gradient is orthogonal to the corresponding earlier step, the fresh realized DFP
step is `G`-conjugate to that earlier step. -/
theorem nextStepConjugateOfPrefix
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {i j : ℕ} (hGenerated : A.GeneratedThrough (i + 2)) (hj : j ≤ i)
    (hHer :
      Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (j + 1) - A.g j) = A (j + 1) - A j)
    (hOrth : dotProduct (A.g (i + 1)) (A (j + 1) - A j) = 0) :
    dotProduct (A (i + 2) - A (i + 1))
      (Matrix.toEuclideanLin G (A (j + 1) - A j)) = 0 := by
  have hOldSecantDot :
      dotProduct (A (i + 2) - A (i + 1))
        (Matrix.toEuclideanLin G (A (j + 1) - A j))
        =
          dotProduct (A (i + 2) - A (i + 1)) (A.g (j + 1) - A.g j) := by
    simpa [dotProduct] using
      congrArg
        (fun v : Fin n → ℝ ↦ (A (i + 2) - A (i + 1)).ofLp ⬝ᵥ v)
        (congrArg WithLp.ofLp (quadraticSecant_eq_hessianStep (A := A) hDFP j)).symm
  -- First close the source-shaped secant orthogonality, then rewrite that secant once into the
  -- public `G`-conjugacy surface.
  calc
    dotProduct (A (i + 2) - A (i + 1))
      (Matrix.toEuclideanLin G (A (j + 1) - A j))
        = dotProduct (A (i + 2) - A (i + 1)) (A.g (j + 1) - A.g j) := hOldSecantDot
    _ = 0 :=
      nextStepDotOldSecant_eq_zero (A := A) hDFP hGenerated hj hHer hOrth

/-- Helper for Chapter05 Theorem 5.1.7: the fresh secant is orthogonal to each earlier step once
the fresh realized step is orthogonal to the corresponding earlier secant. -/
theorem nextSecantDotOldStep_eq_zero
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {i j : ℕ}
    (hCross :
      dotProduct (A (i + 2) - A (i + 1)) (A.g (j + 1) - A.g j) = 0) :
    dotProduct (A.g (i + 2) - A.g (i + 1)) (A (j + 1) - A j) = 0 := by
  have hGsymm : G.IsSymm := posDef_isSymm hDFP.posDef
  have hOldSecantDot :
      dotProduct (A (i + 2) - A (i + 1))
        (Matrix.toEuclideanLin G (A (j + 1) - A j))
        =
          dotProduct (A (i + 2) - A (i + 1)) (A.g (j + 1) - A.g j) := by
    simpa [dotProduct] using
      congrArg
        (fun v : Fin n → ℝ ↦ (A (i + 2) - A (i + 1)).ofLp ⬝ᵥ v)
        (congrArg WithLp.ofLp (quadraticSecant_eq_hessianStep (A := A) hDFP j)).symm
  -- Rewrite the fresh secant through the quadratic Hessian action and then swap `G` across the
  -- Euclidean pairing before returning to the source-shaped old secant.
  calc
    dotProduct (A.g (i + 2) - A.g (i + 1)) (A (j + 1) - A j)
        =
          dotProduct (Matrix.toEuclideanLin G (A (i + 2) - A (i + 1))) (A (j + 1) - A j) := by
            rw [quadraticSecant_eq_hessianStep (A := A) hDFP (i + 1)]
    _ =
        dotProduct (A (i + 2) - A (i + 1))
          (Matrix.toEuclideanLin G (A (j + 1) - A j)) := by
            simpa [dotProduct, sub_eq_add_neg] using
              dotProduct_toEuclideanLin_of_isSymm
                hGsymm (A (i + 2) - A (i + 1)) (A (j + 1) - A j)
    _ = dotProduct (A (i + 2) - A (i + 1)) (A.g (j + 1) - A.g j) := hOldSecantDot
    _ = 0 := hCross

/-- Helper for Chapter05 Theorem 5.1.7: the generated prefix carries the three coupled textbook
invariants simultaneously, namely exact old secants, pairwise `G`-conjugacy, and orthogonality
of the current gradient to every earlier step. -/
theorem generatedPrefixInvariants
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {m : ℕ} (hGenerated : A.GeneratedThrough (m + 1)) :
    (∀ ⦃i j : ℕ⦄, i ≤ m → j ≤ i →
      Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (j + 1) - A.g j) = A (j + 1) - A j) ∧
    (∀ ⦃i j : ℕ⦄, i ≤ m → j < i →
      dotProduct (A (i + 1) - A i)
        (Matrix.toEuclideanLin G (A (j + 1) - A j)) = 0) ∧
    (∀ ⦃i j : ℕ⦄, i ≤ m → j ≤ i →
      dotProduct (A.g (i + 1)) (A (j + 1) - A j) = 0) := by
  -- Route correction: the coupled induction is now stated entirely in the owner-level
  -- Euclidean matrix-action normal form, rather than mixing `.ofLp`/`mulVec` spellings.
  induction m with
  | zero =>
      have hk : A.ε < ‖A.g 0‖ := hGenerated.notStopped (Nat.lt_succ_self 0)
      refine ⟨?_, ?_, ?_⟩
      · intro i j hi hj
        have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero (hi0 ▸ hj)
        subst i
        subst j
        rcases hDFP.stepSpec hk with ⟨_, hsy, hyHy, _⟩
        -- The base DFP update is exact on its own fresh secant by the inverse-update formula.
        have hMul :
            (A.matrix 1).mulVec (A.g 1 - A.g 0) = A 1 - A 0 := by
          rw [A.matrix_update_eq hk]
          exact dfpInverseUpdate_mulVec
            (A.matrix 0) (A 1 - A 0) (A.g 1 - A.g 0) hsy hyHy
        have hQN :
            satisfiesQuasiNewtonEquation (A.matrix 1).toEuclideanLin (A.g 1 - A.g 0) (A 1 - A 0) :=
          satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mpr hMul
        simpa [satisfiesQuasiNewtonEquation] using hQN
      · intro i j hi hj
        have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
        subst i
        exact (Nat.not_lt_zero _ hj).elim
      · intro i j hi hj
        have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
        have hj0 : j = 0 := Nat.eq_zero_of_le_zero (hi0 ▸ hj)
        subst i
        subst j
        -- Exact line search makes the next recorded gradient orthogonal to the realized step.
        simpa using exactLineSearch_nextGradient_orthogonalToStep (A := A) hDFP hGenerated
  | succ m ih =>
      have hPrefixGen : A.GeneratedThrough (m + 1) := hGenerated.of_le (Nat.le_succ (m + 1))
      have hPrefix := ih hPrefixGen
      have hk : A.ε < ‖A.g (m + 1)‖ := hGenerated.notStopped (Nat.lt_succ_self (m + 1))
      have hHsymm : (A.matrix (m + 1)).IsSymm := matrix_isSymm_of_generated (A := A) hPrefixGen
      refine ⟨?_, ?_, ?_⟩
      · intro i j hi hj
        rcases Nat.eq_or_lt_of_le hi with rfl | hi'
        · rcases Nat.eq_or_lt_of_le hj with rfl | hj'
          · rcases hDFP.stepSpec hk with ⟨_, hsy, hyHy, _⟩
            -- The fresh hereditary clause is the DFP inverse secant equation at the new stage.
            have hMul :
                (A.matrix (m + 2)).mulVec (A.g (m + 2) - A.g (m + 1)) =
                  A (m + 2) - A (m + 1) := by
              rw [A.matrix_update_eq hk]
              exact dfpInverseUpdate_mulVec
                (A.matrix (m + 1)) (A (m + 2) - A (m + 1))
                (A.g (m + 2) - A.g (m + 1)) hsy hyHy
            have hQN :
                satisfiesQuasiNewtonEquation
                  (A.matrix (m + 2)).toEuclideanLin
                  (A.g (m + 2) - A.g (m + 1))
                  (A (m + 2) - A (m + 1)) :=
              satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mpr hMul
            simpa [satisfiesQuasiNewtonEquation] using hQN
          · have hjm : j ≤ m := Nat.le_of_lt_succ hj'
            have hHerOld :
                Matrix.toEuclideanLin (A.matrix (m + 1)) (A.g (j + 1) - A.g j) =
                  A (j + 1) - A j :=
              hPrefix.1 (i := m) (j := j) le_rfl hjm
            have hMulOld :
                (A.matrix (m + 1)).mulVec (A.g (j + 1) - A.g j) = A (j + 1) - A j := by
              have hQN :
                  satisfiesQuasiNewtonEquation
                    (A.matrix (m + 1)).toEuclideanLin
                    (A.g (j + 1) - A.g j)
                    (A (j + 1) - A j) := by
                simpa [satisfiesQuasiNewtonEquation] using hHerOld
              exact satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mp hQN
            have hCrossStep :
                dotProduct (A (m + 2) - A (m + 1)) (A.g (j + 1) - A.g j) = 0 :=
              nextStepDotOldSecant_eq_zero (A := A) hDFP hGenerated hjm hHerOld
                (hPrefix.2.2 (i := m) (j := j) le_rfl hjm)
            have hCrossSecant :
                dotProduct (A.g (m + 2) - A.g (m + 1)) (A (j + 1) - A j) = 0 :=
              nextSecantDotOldStep_eq_zero (A := A) hDFP (i := m) (j := j) hCrossStep
            have hyHz :
                dotProduct (A.g (m + 2) - A.g (m + 1))
                  ((A.matrix (m + 1)).mulVec (A.g (j + 1) - A.g j)) = 0 := by
              rw [hMulOld]
              exact hCrossSecant
            -- The rank-two correction vanishes on old secants because both fresh cross terms are
            -- zero, so the old hereditary clause is preserved.
            have hMulPreserved :
                (A.matrix (m + 2)).mulVec (A.g (j + 1) - A.g j) =
                  (A.matrix (m + 1)).mulVec (A.g (j + 1) - A.g j) := by
              rw [A.matrix_update_eq hk]
              exact dfpInverseUpdate_mulVec_of_crossOrthogonal
                (A.matrix (m + 1)) hHsymm
                (A (m + 2) - A (m + 1)) (A.g (m + 2) - A.g (m + 1))
                (A.g (j + 1) - A.g j) hCrossStep hyHz
            have hEuclideanPreserved :
                Matrix.toEuclideanLin (A.matrix (m + 2)) (A.g (j + 1) - A.g j) =
                  Matrix.toEuclideanLin (A.matrix (m + 1)) (A.g (j + 1) - A.g j) := by
              have hQN :
                  satisfiesQuasiNewtonEquation
                    (A.matrix (m + 2)).toEuclideanLin
                    (A.g (j + 1) - A.g j)
                    (Matrix.toEuclideanLin (A.matrix (m + 1)) (A.g (j + 1) - A.g j)) :=
                satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mpr hMulPreserved
              simpa [satisfiesQuasiNewtonEquation] using hQN
            calc
              Matrix.toEuclideanLin (A.matrix (m + 2)) (A.g (j + 1) - A.g j)
                  = Matrix.toEuclideanLin (A.matrix (m + 1)) (A.g (j + 1) - A.g j) :=
                      hEuclideanPreserved
              _ = A (j + 1) - A j := hHerOld
        · exact hPrefix.1 (i := i) (j := j) (Nat.le_of_lt_succ hi') hj
      · intro i j hi hj
        rcases Nat.eq_or_lt_of_le hi with rfl | hi'
        · have hjm : j ≤ m := Nat.le_of_lt_succ hj
          -- The fresh conjugacy clause is a one-boundary transport of the source-shaped cross term.
          exact nextStepConjugateOfPrefix (A := A) hDFP hGenerated hjm
            (hPrefix.1 (i := m) (j := j) le_rfl hjm)
            (hPrefix.2.2 (i := m) (j := j) le_rfl hjm)
        · exact hPrefix.2.1 (i := i) (j := j) (Nat.le_of_lt_succ hi') hj
      · intro i j hi hj
        rcases Nat.eq_or_lt_of_le hi with rfl | hi'
        · rcases Nat.eq_or_lt_of_le hj with rfl | hj'
          · -- Exact line search supplies the fresh gradient orthogonality on the newest step.
            simpa using exactLineSearch_nextGradient_orthogonalToStep (A := A) hDFP hGenerated
          · have hjm : j ≤ m := Nat.le_of_lt_succ hj'
            have hOrthOld :
                dotProduct (A.g (m + 1)) (A (j + 1) - A j) = 0 :=
              hPrefix.2.2 (i := m) (j := j) le_rfl hjm
            have hCrossStep :
                dotProduct (A (m + 2) - A (m + 1)) (A.g (j + 1) - A.g j) = 0 :=
              nextStepDotOldSecant_eq_zero (A := A) hDFP hGenerated hjm
                (hPrefix.1 (i := m) (j := j) le_rfl hjm) hOrthOld
            have hCrossSecant :
                dotProduct (A.g (m + 2) - A.g (m + 1)) (A (j + 1) - A j) = 0 :=
              nextSecantDotOldStep_eq_zero (A := A) hDFP (i := m) (j := j) hCrossStep
            have hSecantSplit :
                dotProduct (A.g (m + 2) - A.g (m + 1)) (A (j + 1) - A j)
                  =
                    dotProduct (A.g (m + 2)) (A (j + 1) - A j) -
                      dotProduct (A.g (m + 1)) (A (j + 1) - A j) := by
              simpa [dotProduct] using
                sub_dotProduct
                  (A.g (m + 2)).ofLp
                  (A.g (m + 1)).ofLp
                  ((A (j + 1) - A j).ofLp)
            linarith
        · exact hPrefix.2.2 (i := i) (j := j) (Nat.le_of_lt_succ hi') hj

/-- Helper for Chapter05 Theorem 5.1.7: every generated DFP prefix yields a `G`-conjugate family
of nonzero steps indexed by that prefix length. -/
theorem generatedStepFamily_isConjugateFamily
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {k : ℕ} (hGenerated : A.GeneratedThrough k) :
    G.IsConjugateFamily (fun i : Fin k ↦ (A (i + 1) - A i).ofLp) := by
  cases k with
  | zero =>
      rw [Matrix.isConjugateFamily_iff]
      constructor
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ m =>
      rw [Matrix.isConjugateFamily_iff]
      refine ⟨?_, ?_⟩
      · intro i
        -- Each generated step is nonzero because the current generated stage is nonterminal.
        have hi : (i : ℕ) < m + 1 := i.is_lt
        have hNotStopped : A.ε < ‖A.g i‖ := hGenerated.notStopped hi
        intro hZero
        have hStep : A (i + 1) - A i ≠ 0 := step_ne_zero (A := A) hDFP hNotStopped
        apply hStep
        ext p
        simpa using congrArg (fun v : Fin n → ℝ ↦ v p) hZero
      · intro i j hij
        have hPrefix := generatedPrefixInvariants (A := A) hDFP (m := m) hGenerated
        have hGsymm : G.IsSymm := posDef_isSymm hDFP.posDef
        -- Symmetry of `G` lets us swap the order when the larger index is on the right.
        have hSwap :
            dotProduct (A (i + 1) - A i)
                (Matrix.toEuclideanLin G (A (j + 1) - A j)) =
              dotProduct (A (j + 1) - A j)
                (Matrix.toEuclideanLin G (A (i + 1) - A i)) := by
          simpa [dotProduct_comm] using
            dotProduct_toEuclideanLin_of_isSymm hGsymm
              (A (j + 1) - A j) (A (i + 1) - A i)
        have hTarget :
            dotProduct (A (i + 1) - A i)
              (Matrix.toEuclideanLin G (A (j + 1) - A j)) = 0 := by
          rcases lt_or_gt_of_ne hij with hij' | hij'
          · rw [hSwap]
            exact hPrefix.2.1 (i := j) (j := i) (Nat.le_of_lt_succ j.is_lt) hij'
          · exact hPrefix.2.1 (i := i) (j := j) (Nat.le_of_lt_succ i.is_lt) hij'
        simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hTarget

/-- Helper for Chapter05 Theorem 5.1.7: the current generated DFP matrix is exact on every
earlier secant in that same generated prefix. -/
theorem hereditaryAtCurrent
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {k : ℕ} (hGenerated : A.GeneratedThrough k) :
    ∀ j : Fin k, (A.matrix k).mulVec (A.g (j + 1) - A.g j) = A (j + 1) - A j := by
  cases k with
  | zero =>
      intro j
      exact Fin.elim0 j
  | succ m =>
      intro j
      -- Project the last-stage hereditary clause out of the coupled prefix invariant.
      have hHer :
          Matrix.toEuclideanLin (A.matrix (m + 1)) (A.g (j + 1) - A.g j) =
            A (j + 1) - A j :=
        (generatedPrefixInvariants (A := A) hDFP (m := m) hGenerated).1
          (i := m) (j := j) le_rfl (Nat.le_of_lt_succ j.is_lt)
      have hQN :
          satisfiesQuasiNewtonEquation
            (A.matrix (m + 1)).toEuclideanLin
            (A.g (j + 1) - A.g j)
            (A (j + 1) - A j) := by
        simpa [satisfiesQuasiNewtonEquation] using hHer
      exact satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mp hQN

/-- Helper for Chapter05 Theorem 5.1.7: if every positive stage before `t` is nonterminal, then
the exact-line-search quadratic DFP run is generated through stage `t`. -/
theorem generatedThrough_of_strictPrefixNonterminal
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    (hStart : A.GeneratedThrough 1)
    {t : ℕ}
    (hNoTerm : ∀ i : ℕ, 1 ≤ i → i < t → ¬ A.terminatedAt i) :
    A.GeneratedThrough t := by
  refine ⟨?_, ?_⟩
  · intro i hi
    cases i with
    | zero =>
        exact hStart.notStopped (by simp)
    | succ i =>
        exact lt_of_not_ge (hNoTerm (i + 1) (Nat.succ_le_succ (Nat.zero_le i)) hi)
  · intro i hi
    have hiNot : A.ε < ‖A.g i‖ := by
      cases i with
      | zero =>
          exact hStart.notStopped (by simp)
      | succ i =>
          exact lt_of_not_ge (hNoTerm (i + 1) (Nat.succ_le_succ (Nat.zero_le i)) hi)
    have hStepNonzero : A (i + 1) - A i ≠ 0 := step_ne_zero (A := A) hDFP hiNot
    have hStepNonzero' : ((A (i + 1) - A i).ofLp : Fin n → ℝ) ≠ 0 := by
      intro hZero
      apply hStepNonzero
      ext j
      simpa using congrArg (fun v : Fin n → ℝ ↦ v j) hZero
    have hQuad :
        0 < dotProduct (A (i + 1) - A i) (G.mulVec (A (i + 1) - A i)) := by
      simpa using hDFP.posDef.dotProduct_mulVec_pos hStepNonzero'
    exact satisfiesCurvatureCondition_iff_dotProduct_pos.mpr <| by
      simpa [quadraticSecant_eq_hessianStep (A := A) hDFP i,
        Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hQuad

/-- Hereditary conclusion of Theorem 5.1.7: if an exact-line-search DFP run on the positive-
definite quadratic objective is generated through stage `m + 1`, then
`H (i + 1) y j = s j` for every `j ≤ i ≤ m`. -/
theorem hereditary
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {m : ℕ}
    (hGenerated : A.GeneratedThrough (m + 1)) :
    ∀ ⦃i j : ℕ⦄, i ≤ m → j ≤ i →
      (A.matrix (i + 1)).mulVec (A.g (j + 1) - A.g j) = A (j + 1) - A j := by
  -- Project the hereditary part from the coupled prefix invariant.
  intro i j hi hj
  have hHer :
      Matrix.toEuclideanLin (A.matrix (i + 1)) (A.g (j + 1) - A.g j) =
        A (j + 1) - A j :=
    (generatedPrefixInvariants (A := A) hDFP hGenerated).1 hi hj
  have hQN :
      satisfiesQuasiNewtonEquation
        (A.matrix (i + 1)).toEuclideanLin
        (A.g (j + 1) - A.g j)
        (A (j + 1) - A j) := by
    simpa [satisfiesQuasiNewtonEquation] using hHer
  exact satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mp hQN

/-- Conjugate-direction conclusion of Theorem 5.1.7: if an exact-line-search DFP run on the
positive-definite quadratic objective is generated through stage `m + 1`, then the generated
steps are pairwise `G`-conjugate up to `m`, namely `s iᵀ G s j = 0` whenever `j < i ≤ m`. -/
theorem conjugateDirections
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {m : ℕ}
    (hGenerated : A.GeneratedThrough (m + 1)) :
    ∀ ⦃i j : ℕ⦄, i ≤ m → j < i →
      dotProduct (A (i + 1) - A i) (G.mulVec (A (j + 1) - A j)) = 0 := by
  -- Project the conjugacy part from the same coupled prefix invariant.
  intro i j hi hj
  have hPair :
      dotProduct (A (i + 1) - A i)
        (Matrix.toEuclideanLin G (A (j + 1) - A j)) = 0 :=
    (generatedPrefixInvariants (A := A) hDFP hGenerated).2.1 hi hj
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hPair

/-- Termination-index bound from Theorem 5.1.7: if an exact-line-search DFP run on the
positive-definite quadratic objective is generated through stage `m + 1` and terminates there,
then the textbook bound `m + 1 ≤ n` holds. -/
theorem terminationBound
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    {m : ℕ}
    (hGenerated : A.GeneratedThrough (m + 1))
    (_hTerm : A.terminatedAt (m + 1)) :
    m + 1 ≤ n := by
  let d : Fin (m + 1) → Fin n → ℝ := fun i ↦ (A (i + 1) - A i).ofLp
  have hFamily : G.IsConjugateFamily d := by
    simpa [d] using generatedStepFamily_isConjugateFamily (A := A) hDFP hGenerated
  have hLin : LinearIndependent ℝ d :=
    Matrix.linearIndependent_of_isConjugateFamily hDFP.posDef hFamily
  have hCard :
      Fintype.card (Fin (m + 1)) ≤ Module.finrank ℝ (Fin n → ℝ) :=
    hLin.fintype_card_le_finrank
  -- The ambient Euclidean space has dimension `n`, so the generated prefix cannot be longer.
  simpa using hCard

/-- Final inverse-Hessian conclusion of Theorem 5.1.7: if an exact-line-search DFP run on the
positive-definite quadratic objective remains generated through the first `n` directions and
terminates at stage `n`, then the final DFP inverse-Hessian approximation equals `G⁻¹`. -/
theorem finalInverse
    (A : DfpMethod (dfpQuadraticObjective G b c)) (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    (hGenerated : A.GeneratedThrough n)
    (hTerm : A.terminatedAt n) :
    A.matrix n = G⁻¹ := by
  have hFamily :
      G.IsConjugateFamily (fun j : Fin n ↦ (A (j + 1) - A j).ofLp) :=
    generatedStepFamily_isConjugateFamily (A := A) hDFP hGenerated
  have hLin :
      LinearIndependent ℝ (fun j : Fin n ↦ (A (j + 1) - A j).ofLp) :=
    Matrix.linearIndependent_of_isConjugateFamily hDFP.posDef hFamily
  have hcard :
      Fintype.card (Fin n) = Module.finrank ℝ (Fin n → ℝ) := by
    simp
  have hspan :
      Submodule.span ℝ (Set.range fun j : Fin n ↦ (A (j + 1) - A j).ofLp) = ⊤ := by
    exact hLin.span_eq_top_of_card_eq_finrank' hcard
  let stepBasis : Module.Basis (Fin n) ℝ (Fin n → ℝ) :=
    Module.Basis.mk hLin hspan.ge
  have hExact :
      ∀ j : Fin n,
        (A.matrix n * G).mulVec ((A (j + 1) - A j).ofLp) =
          (A (j + 1) - A j).ofLp := by
    intro j
    have hSecant :
        G.mulVec ((A (j + 1) - A j).ofLp) = (A.g (j + 1) - A.g j).ofLp := by
      ext p
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using
        congrArg (fun v : EuclideanSpace ℝ (Fin n) ↦ v p)
          (quadraticSecant_eq_hessianStep (A := A) hDFP j).symm
    -- Combine the quadratic secant identity with hereditary exactness at the current stage.
    calc
      (A.matrix n * G).mulVec ((A (j + 1) - A j).ofLp)
          = (A.matrix n).mulVec (G.mulVec ((A (j + 1) - A j).ofLp)) := by
              rw [Matrix.mulVec_mulVec]
      _ = (A.matrix n).mulVec ((A.g (j + 1) - A.g j).ofLp) := by
            rw [hSecant]
      _ = (A (j + 1) - A j).ofLp := hereditaryAtCurrent (A := A) hDFP hGenerated j
  have hmul : A.matrix n * G = 1 := by
    -- Compare `A.matrix n * G` with the identity on the basis formed by the generated steps.
    apply Matrix.toLin'.injective
    exact stepBasis.ext fun j ↦ by
      have hExactStep :
          (A.matrix n * G).mulVec ((A (j + 1) - A j).ofLp) =
            (A (j + 1) - A j).ofLp :=
        hExact j
      simpa [stepBasis, Module.Basis.mk_apply, Matrix.toLin'_apply] using hExactStep
  let _ := hDFP.posDef.isUnit.invertible
  have _hTerm := hTerm
  -- Cancel the positive-definite Hessian at the matrix level once exactness on the step basis
  -- shows `A.matrix n * G = 1`.
  calc
    A.matrix n = A.matrix n * 1 := by simp
    _ = A.matrix n * (G * G⁻¹) := by rw [Matrix.mul_inv_of_invertible]
    _ = (A.matrix n * G) * G⁻¹ := by rw [Matrix.mul_assoc]
    _ = 1 * G⁻¹ := by rw [hmul]
    _ = G⁻¹ := by simp

end DfpMethod

/-- Chapter05 Theorem 5.1.7 (Quadratic Termination Theorem of DFP Method): for a
positive-definite quadratic objective with exact line search whose first DFP step is generated,
there is an index `m` such that the DFP run is generated through stage `m + 1`,
the hereditary property
`H (i + 1) y j = s j` holds for every `j ≤ i ≤ m`, the conjugate-direction property
`s iᵀ G s j = 0` holds for every `j < i ≤ m`, the method terminates at stage `m + 1 ≤ n`, and,
in the full-length case `m + 1 = n`, the final identity `H n = G⁻¹` holds. -/
theorem dfpPrefixInvariants
    (A : DfpMethod (dfpQuadraticObjective G b c))
    (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    (hStart : A.GeneratedThrough 1) :
    ∃ m : ℕ,
      And (A.GeneratedThrough (m + 1))
        (And (A.terminatedAt (m + 1))
          (And (m + 1 ≤ n)
            (And
              (∀ ⦃i j : ℕ⦄, i ≤ m → j ≤ i →
                (A.matrix (i + 1)).mulVec (A.g (j + 1) - A.g j) = A (j + 1) - A j)
              (And
                (∀ ⦃i j : ℕ⦄, i ≤ m → j < i →
                  dotProduct (A (i + 1) - A i) (G.mulVec (A (j + 1) - A j)) = 0)
                (m + 1 = n → A.matrix n = G⁻¹))))) := by
  classical
  have hExistsTerm :
      ∃ t : ℕ, 1 ≤ t ∧ t ≤ n ∧ A.terminatedAt t := by
    by_contra hNo
    have hNoTerm :
        ∀ i : ℕ, 1 ≤ i → i < n + 1 → ¬ A.terminatedAt i := by
      intro i hi1 hi hTerm
      exact hNo ⟨i, hi1, Nat.lt_succ_iff.mp hi, hTerm⟩
    have hGeneratedAll : A.GeneratedThrough (n + 1) :=
      generatedThrough_of_strictPrefixNonterminal (A := A) hDFP hStart hNoTerm
    have hFamily :
        G.IsConjugateFamily (fun i : Fin (n + 1) ↦ (A (i + 1) - A i).ofLp) :=
      generatedStepFamily_isConjugateFamily (A := A) hDFP hGeneratedAll
    have hLin :
        LinearIndependent ℝ (fun i : Fin (n + 1) ↦ (A (i + 1) - A i).ofLp) :=
      Matrix.linearIndependent_of_isConjugateFamily hDFP.posDef hFamily
    have hCard :
        Fintype.card (Fin (n + 1)) ≤ Module.finrank ℝ (Fin n → ℝ) :=
      hLin.fintype_card_le_finrank
    have hImpossible : n + 1 ≤ n := by
      simp at hCard
    exact Nat.not_succ_le_self n hImpossible
  let t := Nat.find hExistsTerm
  have ht1 : 1 ≤ t := (Nat.find_spec hExistsTerm).1
  have htn : t ≤ n := (Nat.find_spec hExistsTerm).2.1
  have hTerm : A.terminatedAt t := (Nat.find_spec hExistsTerm).2.2
  have hNoTermBefore :
      ∀ i : ℕ, 1 ≤ i → i < t → ¬ A.terminatedAt i := by
    intro i hi1 hi hTermI
    have hWitness : 1 ≤ i ∧ i ≤ n ∧ A.terminatedAt i :=
      ⟨hi1, Nat.le_trans (Nat.le_of_lt hi) htn, hTermI⟩
    exact Nat.not_le_of_lt hi (Nat.find_min' hExistsTerm hWitness)
  have hGenerated : A.GeneratedThrough t :=
    generatedThrough_of_strictPrefixNonterminal (A := A) hDFP hStart hNoTermBefore
  have ht_eq : t - 1 + 1 = t := Nat.sub_add_cancel ht1
  have hGeneratedPred : A.GeneratedThrough (t - 1 + 1) := by
    simpa [ht_eq] using hGenerated
  have hTermPred : A.terminatedAt (t - 1 + 1) := by
    simpa [ht_eq] using hTerm
  refine ⟨t - 1, ?_⟩
  refine ⟨?_, ?_⟩
  · -- Reindex the generated prefix by `m = t - 1`.
    exact hGeneratedPred
  · refine ⟨?_, ?_⟩
    · -- The chosen index is the least terminating stage.
      exact hTermPred
    · refine ⟨?_, ?_⟩
      · -- Finite-dimensional conjugacy bounds the number of generated stages by `n`.
        simpa [ht_eq] using htn
      · refine ⟨?_, ?_⟩
        · -- Export the hereditary projection at the least terminating stage.
          exact hereditary (A := A) hDFP hGeneratedPred
        · refine ⟨?_, ?_⟩
          · -- Export the conjugacy projection at the same stage.
            exact conjugateDirections (A := A) hDFP hGeneratedPred
          · intro hm
            have ht_eq_n : t = n := by
              simpa [ht_eq] using hm
            have hGeneratedN : A.GeneratedThrough n := by
              simpa [ht_eq_n] using hGenerated
            have hTermN : A.terminatedAt n := by
              simpa [ht_eq_n] using hTerm
            -- In the full-length case, the terminal matrix coincides with `G⁻¹`.
            exact finalInverse (A := A) hDFP hGeneratedN hTermN

/-- Helper for Chapter05 Theorem 5.1.7: `dfpPrefixInvariants` is the main labeled theorem for
this item, and `dfpMethod_quadraticTermination` remains as a source-facing compatibility alias. -/
theorem dfpMethod_quadraticTermination
    (A : DfpMethod (dfpQuadraticObjective G b c))
    (hDFP : A.IsExactLineSearchOnQuadratic G b c)
    (hStart : A.GeneratedThrough 1) :
    ∃ m : ℕ,
      And (A.GeneratedThrough (m + 1))
        (And (A.terminatedAt (m + 1))
          (And (m + 1 ≤ n)
            (And
              (∀ ⦃i j : ℕ⦄, i ≤ m → j ≤ i →
                (A.matrix (i + 1)).mulVec (A.g (j + 1) - A.g j) = A (j + 1) - A j)
              (And
                (∀ ⦃i j : ℕ⦄, i ≤ m → j < i →
                  dotProduct (A (i + 1) - A i) (G.mulVec (A (j + 1) - A j)) = 0)
                (m + 1 = n → A.matrix n = G⁻¹))))) :=
  dfpPrefixInvariants A hDFP hStart

end ExactLineSearchDfpMethod
end
