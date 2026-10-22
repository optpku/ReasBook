/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

open scoped Gradient

-- Domain sampling:
-- * `HasFDerivAt (∇ f)` together with `Matrix.toEuclideanCLM` is the Chapter 3 canonical owner
--   for Hessian matrix data at a point.
-- * `NewtonMethod.linearSystem` and `IsNewtonMethodSequence.newtonEq` record Newton steps by
--   the linear system `(G k).mulVec (s k) = -g k` together with explicit invertibility.
-- * `Matrix.PosDef.isUnit` is the bridge from the source positivity hypothesis to the
--   invertibility needed by the theorems connecting the inverse-Hessian bridge to the Newton
--   linear system.
-- Source/core/bridge triage:
-- * source-facing: the quadratic model, Newton direction, and Newton update at one iterate.
-- * core/canonical: the direct Hessian condition `∀ x, HasFDerivAt (∇ f) ... x` and the
--   Newton linear system.
-- * bridge/view: the inverse-Hessian formulas; invertibility remains on theorems that prove
--   those formulas satisfy the Newton-system owner.

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Hessian" => Matrix (Fin n) (Fin n) ℝ

/-- Chapter03 Definition 3.2-extra-1 (1): if `G` represents the Hessian of `f`,
the quadratic model at the current iterate `x_k` is
`q^(k) (s) = f(x_k) + (∇ f x_k)ᵀ s + (1 / 2) sᵀ (G x_k) s`. -/
def newtonQuadraticModel (f : Point → ℝ) (xk : Point) (G : Point → Hessian) (s : Point) : ℝ :=
  f xk + inner ℝ (gradient f xk) s +
    (1 / 2 : ℝ) * inner ℝ s (Matrix.toEuclideanLin (G xk) s)

/-- Evaluating the Newton quadratic model at the zero step returns `f(x_k)`. -/
theorem newtonQuadraticModel_zeroStep
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian) :
    newtonQuadraticModel f xk G 0 = f xk := by
  simp [newtonQuadraticModel]

/-- Chapter03 Definition 3.2-extra-1 (2): a vector `s` is a Newton direction at `x_k` when
`G x_k` is invertible and `s` solves the Newton linear system. -/
def IsNewtonDirectionAt (f : Point → ℝ) (xk : Point) (G : Point → Hessian) (s : Point) : Prop :=
  IsUnit (G xk) ∧ (G xk).mulVec s = -gradient f xk

/-- Unfolding formula for `IsNewtonDirectionAt`. -/
theorem isNewtonDirectionAt_iff
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian) (s : Point) :
    IsNewtonDirectionAt f xk G s ↔
      IsUnit (G xk) ∧ (G xk).mulVec s = -gradient f xk := Iff.rfl

/-- The inverse-form Newton direction is the negative inverse-Hessian applied to the gradient. -/
def newtonDirection (f : Point → ℝ) (xk : Point) (G : Point → Hessian) : Point :=
  -(Matrix.toEuclideanLin ((G xk)⁻¹) (gradient f xk))

/-- Unfolding `newtonDirection` gives the inverse-Hessian Newton formula. -/
theorem newtonDirection_eq_neg_inv_apply
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian) :
    newtonDirection f xk G =
      -(Matrix.toEuclideanLin ((G xk)⁻¹) (gradient f xk)) := rfl

/-- Helper for Chapter03 Definition 3.2-extra-1: converting the Newton direction back to
coordinates gives the textbook vector formula `-G_k⁻¹ g_k`. -/
theorem ofLp_newtonDirection_eq_neg_mulVec_inv
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian) (hGk : IsUnit (G xk)) :
    (newtonDirection f xk G).ofLp =
      -((G xk)⁻¹).mulVec (gradient f xk).ofLp := by
  letI := hGk.invertible
  -- Evaluate the inverse-Hessian linear map on coordinates once so later proofs can stay stable.
  rw [newtonDirection_eq_neg_inv_apply]
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

/-- The inverse-form Newton direction solves the Newton linear system. -/
theorem newtonDirection_newtonEq
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian) (hGk : IsUnit (G xk)) :
    (G xk).mulVec (newtonDirection f xk G) = -gradient f xk := by
  letI := hGk.invertible
  -- First solve the Newton equation in coordinates, where inverse cancellation is direct.
  have hcoord :
      (G xk).mulVec ((newtonDirection f xk G).ofLp) = -(gradient f xk).ofLp := by
    calc
      (G xk).mulVec ((newtonDirection f xk G).ofLp)
          = (G xk).mulVec (-((G xk)⁻¹).mulVec (gradient f xk).ofLp) := by
              rw [ofLp_newtonDirection_eq_neg_mulVec_inv f xk G hGk]
      _ = -((G xk).mulVec (((G xk)⁻¹).mulVec (gradient f xk).ofLp)) := by
            rw [Matrix.mulVec_neg]
      _ = -(((G xk) * (G xk)⁻¹).mulVec (gradient f xk).ofLp) := by
            rw [Matrix.mulVec_mulVec]
      _ = -((1 : Hessian).mulVec (gradient f xk).ofLp) := by
            rw [Matrix.mul_inv_of_invertible (A := G xk)]
      _ = -(gradient f xk).ofLp := by
            rw [Matrix.one_mulVec]
  -- The Newton equation in this file is already recorded in coordinate-vector form.
  exact hcoord

/-- The inverse-form Newton direction is a Newton direction in the linear-system sense. -/
theorem newtonDirection_isNewtonDirectionAt
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian) (hGk : IsUnit (G xk)) :
    IsNewtonDirectionAt f xk G (newtonDirection f xk G) := by
  exact ⟨hGk, newtonDirection_newtonEq f xk G hGk⟩

/-- Helper for Chapter03 Definition 3.2-extra-1: an invertible Hessian matrix makes the Newton
linear system have the unique solution given by the inverse-Hessian formula. -/
theorem isNewtonDirectionAt_iff_eq_newtonDirection
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian)
    (hGk : IsUnit (G xk)) (s : Point) :
    IsNewtonDirectionAt f xk G s ↔ s = newtonDirection f xk G := by
  constructor
  · intro hs
    -- Both sides solve the same invertible linear system, so injectivity of `mulVec` gives equality.
    have hEq :
        (G xk).mulVec s = (G xk).mulVec (newtonDirection f xk G) := by
      rw [hs.2, newtonDirection_newtonEq f xk G hGk]
    have hEq' := (Matrix.mulVec_injective_of_isUnit hGk) hEq
    ext i
    exact congrFun hEq' i
  · intro hs
    -- Rewriting by the canonical inverse-Hessian step recovers the Newton-system witness.
    rw [hs]
    exact newtonDirection_isNewtonDirectionAt f xk G hGk

/-- Helper for Chapter03 Definition 3.2-extra-1: the Newton quadratic model equals its value at
the Newton direction plus the curvature term in the displacement from that direction. -/
lemma newtonQuadraticModel_eq_at_newtonDirection_add_curvature
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian)
    (hGk : (G xk).PosDef) (s : Point) :
    newtonQuadraticModel f xk G s =
      newtonQuadraticModel f xk G (newtonDirection f xk G) +
        (1 / 2 : ℝ) * inner ℝ (s - newtonDirection f xk G)
          (Matrix.toEuclideanLin (G xk) (s - newtonDirection f xk G)) := by
  let g : Point := gradient f xk
  let sN : Point := newtonDirection f xk G
  let A : Point →ₗ[ℝ] Point := Matrix.toEuclideanLin (G xk)
  let d : Point := s - sN
  have hA_symm : A.IsSymmetric := by
    intro u v
    have htranspose : (G xk).transpose = G xk := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hGk.1.eq
    rw [real_inner_comm]
    change inner ℝ v ((Matrix.toEuclideanCLM (𝕜 := ℝ) (G xk)) u) =
      inner ℝ u ((Matrix.toEuclideanCLM (𝕜 := ℝ) (G xk)) v)
    rw [Matrix.inner_toEuclideanCLM, Matrix.inner_toEuclideanCLM]
    simpa [htranspose] using
      (Matrix.dotProduct_transpose_mulVec (A := G xk) (x := v.ofLp) (y := u.ofLp))
  have hsN : A sN = -g := by
    ext i
    simpa [A, g, sN, Matrix.toEuclideanLin_apply] using
      congrFun (newtonDirection_newtonEq f xk G hGk.isUnit) i
  have hs : s = sN + d := by
    simp [d, sN, sub_eq_add_neg, add_left_comm]
  have hCrossLeft : inner ℝ sN (A d) = -inner ℝ g d := by
    calc
      inner ℝ sN (A d) = inner ℝ (A sN) d := by
        simpa [A] using (hA_symm sN d).symm
      _ = inner ℝ (-g) d := by rw [hsN]
      _ = -inner ℝ g d := by simp
  have hCrossRight : inner ℝ d (A sN) = -inner ℝ g d := by
    calc
      inner ℝ d (A sN) = inner ℝ d (-g) := by rw [hsN]
      _ = -inner ℝ d g := by simp
      _ = -inner ℝ g d := by rw [real_inner_comm]
  -- Expand the quadratic model around `sN` and cancel the mixed terms using the Newton equation.
  calc
    newtonQuadraticModel f xk G s
        = f xk + inner ℝ g (sN + d) +
            (1 / 2 : ℝ) * inner ℝ (sN + d) (A (sN + d)) := by
          rw [hs, newtonQuadraticModel]
    _ = f xk + inner ℝ g sN + inner ℝ g d +
          (1 / 2 : ℝ) * inner ℝ (sN + d) (A sN + A d) := by
          rw [inner_add_right, map_add]
          ring
    _ = f xk + inner ℝ g sN + inner ℝ g d +
          (1 / 2 : ℝ) *
            (inner ℝ sN (A sN) + inner ℝ sN (A d) +
              inner ℝ d (A sN) + inner ℝ d (A d)) := by
          simp [inner_add_left, inner_add_right]
          ring
    _ = f xk + inner ℝ g sN + (1 / 2 : ℝ) * inner ℝ sN (A sN) +
          (1 / 2 : ℝ) * inner ℝ d (A d) := by
          rw [hCrossLeft, hCrossRight]
          ring
    _ = newtonQuadraticModel f xk G sN +
          (1 / 2 : ℝ) * inner ℝ d (A d) := by
          simp [newtonQuadraticModel, g, sN, A]
    _ = newtonQuadraticModel f xk G (newtonDirection f xk G) +
          (1 / 2 : ℝ) * inner ℝ (s - newtonDirection f xk G)
            (Matrix.toEuclideanLin (G xk) (s - newtonDirection f xk G)) := by
          simp [g, sN, A, d]

/-- Under positive definiteness, minimizing the Newton quadratic model is equivalent to solving
the Newton linear system. -/
theorem isMinOn_newtonQuadraticModel_iff_isNewtonDirectionAt
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian)
    (hGk : (G xk).PosDef)
    (s : Point) :
    IsMinOn (newtonQuadraticModel f xk G) Set.univ s ↔
      IsNewtonDirectionAt f xk G s := by
  rw [isNewtonDirectionAt_iff_eq_newtonDirection f xk G hGk.isUnit s]
  let sN : Point := newtonDirection f xk G
  constructor
  · intro hsMin
    -- A global minimizer must make the positive-definite remainder vanish, hence equal `sN`.
    by_contra hs_ne
    have hs_le :
        newtonQuadraticModel f xk G s ≤ newtonQuadraticModel f xk G sN :=
      (isMinOn_univ_iff.mp hsMin) sN
    have hdiff_ne : (s - sN).1 ≠ 0 := by
      intro hzero
      apply hs_ne
      apply sub_eq_zero.mp
      ext i
      exact congrFun hzero i
    have hcurv_pos :
        0 < inner ℝ (s - sN) (Matrix.toEuclideanLin (G xk) (s - sN)) := by
      have hcurv_pos' :
          0 < dotProduct (s - sN).1 ((G xk).mulVec (s - sN).1) := by
        simpa using hGk.dotProduct_mulVec_pos hdiff_ne
      simpa [Matrix.toEuclideanLin_apply, PiLp.inner_apply, dotProduct, mul_comm] using hcurv_pos'
    have hstrict :
        newtonQuadraticModel f xk G sN < newtonQuadraticModel f xk G s := by
      have hhalf_pos :
          0 < (1 / 2 : ℝ) * inner ℝ (s - sN) (Matrix.toEuclideanLin (G xk) (s - sN)) := by
        nlinarith
      linarith [newtonQuadraticModel_eq_at_newtonDirection_add_curvature f xk G hGk s]
    exact (not_lt_of_ge hs_le) hstrict
  · intro hs_eq
    subst s
    rw [isMinOn_univ_iff]
    intro y
    -- The remainder term is nonnegative by positive semidefiniteness of the Hessian matrix.
    have hcurv_nonneg :
        0 ≤ inner ℝ (y - sN) (Matrix.toEuclideanLin (G xk) (y - sN)) := by
      have hcurv_nonneg' :
          0 ≤ dotProduct (y - sN).1 ((G xk).mulVec (y - sN).1) := by
        simpa using hGk.posSemidef.dotProduct_mulVec_nonneg (y - sN).1
      simpa [Matrix.toEuclideanLin_apply, PiLp.inner_apply, dotProduct, mul_comm] using
        hcurv_nonneg'
    have hhalf_nonneg :
        0 ≤ (1 / 2 : ℝ) * inner ℝ (y - sN) (Matrix.toEuclideanLin (G xk) (y - sN)) := by
      nlinarith
    linarith [newtonQuadraticModel_eq_at_newtonDirection_add_curvature f xk G hGk y]

/-- Under the source positivity hypothesis on `G x_k`, minimizing the Newton quadratic
model yields exactly the Newton direction. -/
theorem isMinOn_newtonQuadraticModel_iff_eq_newtonDirection
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian)
    (hGk : (G xk).PosDef)
    (s : Point) :
    IsMinOn (newtonQuadraticModel f xk G) Set.univ s ↔
      s = newtonDirection f xk G := by
  -- Rewrite the source-facing Newton-system predicate by uniqueness of the invertible linear system.
  rw [← isNewtonDirectionAt_iff_eq_newtonDirection f xk G hGk.isUnit s]
  exact isMinOn_newtonQuadraticModel_iff_isNewtonDirectionAt f xk G hGk s

/-- Chapter03 Definition 3.2-extra-1 (3): Newton's formula is
`x_(k + 1) = x_k + s_k = x_k - (G x_k)⁻¹ (∇ f x_k)`. -/
def newtonNextIterate (f : Point → ℝ) (xk : Point) (G : Point → Hessian) : Point :=
  xk + newtonDirection f xk G

/-- The Newton update is the current iterate plus the Newton direction. -/
theorem newtonNextIterate_eq_add_direction
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian) :
    newtonNextIterate f xk G = xk + newtonDirection f xk G := rfl

/-- The Newton update can be written directly with the inverse Hessian and gradient. -/
theorem newtonNextIterate_eq_sub_inv_apply
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian) :
    newtonNextIterate f xk G =
      xk - Matrix.toEuclideanLin ((G xk)⁻¹) (gradient f xk) := rfl

/-- Chapter03 Definition 3.2-extra-1 (4): if `G x_k` is positive definite and
`∇ f x_k ≠ 0`, then the Newton direction is a descent direction, i.e.
`⟪∇ f x_k, s_k⟫ < 0`. -/
theorem newtonDirection_isDescentDirection
    (f : Point → ℝ) (xk : Point) (G : Point → Hessian)
    (hGk : (G xk).PosDef) (hgk : gradient f xk ≠ 0) :
    inner ℝ (gradient f xk) (newtonDirection f xk G) < 0 := by
  have hgk' : (gradient f xk).ofLp ≠ 0 := by
    simpa using hgk
  have hquad :
      0 < dotProduct (gradient f xk).ofLp (((G xk)⁻¹).mulVec (gradient f xk).ofLp) := by
    -- Positive definiteness passes to the inverse Hessian, so the inverse quadratic form is positive.
    simpa using hGk.inv.dotProduct_mulVec_pos hgk'
  -- Rewrite the Euclidean inner product as the negative inverse-Hessian quadratic form.
  calc
    inner ℝ (gradient f xk) (newtonDirection f xk G)
        = -dotProduct (gradient f xk).ofLp (((G xk)⁻¹).mulVec (gradient f xk).ofLp) := by
            rw [newtonDirection_eq_neg_inv_apply, PiLp.inner_apply, Matrix.toEuclideanLin_apply]
            simp [dotProduct, mul_comm]
    _ < 0 := by
          exact neg_neg_of_pos hquad

/-
Chapter03 Definition 3.2-extra-1 (5): in the remainder of the source, the first derivative
is denoted by `g(x) = ∇ f(x)`, represented in Lean by `∇ f x`, and a matrix field
`G` stands for the Hessian data through the direct condition
`∀ x, HasFDerivAt (∇ f) ((Matrix.toEuclideanCLM : Hessian ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (G x)) x`.
-/
#check fun (f : Point → ℝ) (G : Point → Hessian) (x : Point) ↦
  (((∇ f) x),
    G x,
    HasFDerivAt (∇ f)
      ((Matrix.toEuclideanCLM : Hessian ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (G x))
      x)
