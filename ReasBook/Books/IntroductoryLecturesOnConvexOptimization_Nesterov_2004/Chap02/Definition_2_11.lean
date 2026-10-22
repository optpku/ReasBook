/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_9_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_5_7

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped Gradient

noncomputable section

/- Definition 2.11 lies in finite-dimensional quadratic lower-bound constructions on Euclidean
coordinate spaces.

Source/core/bridge triage:
* source-facing: the textbook tridiagonal matrix `A_k` and the corresponding lower-bound function
  `f_k`
* core/canonical: the Chapter 1 owner `quadraticObjective`
* bridge/view: the explicit coordinate formula for `f_k` and the Hessian matrix identity

Sampled owner-style declarations in this domain:
* `quadraticObjective` in `Definition_1_9_1`
* `hessianMatrix` in `Definition_1_4_16`
* `EuclideanSpace.single` in mathlib for the canonical first basis vector

Best owner abstraction:
* `quadraticObjective`

Primitive data:
* `pathTridiagonalMatrix k`

Derived API:
* `smoothLowerBoundFunction L k` as the specific owner quadratic with Hessian data
  `(L / 4) • pathTridiagonalMatrix k` and first-coordinate linear term
* the explicit textbook expansion `smoothLowerBoundFunction_apply`
* the canonical affine-profile point `smoothLowerBoundFunctionStationaryPoint k`
* the coordinate formula `smoothLowerBoundFunctionStationaryPoint_apply`
* the Hessian identity `smoothLowerBoundFunction_hessian_eq_tridiagonal`
-/

/-- The tridiagonal matrix `A_k` with diagonal entries `2` and first off-diagonal entries `-1`. -/
def pathTridiagonalMatrix (k : ℕ+) : Matrix (Fin k) (Fin k) ℝ :=
  fun i j ↦
    if i = j then
      2
    else if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then
      -1
    else
      0

/-- The entries of `pathTridiagonalMatrix k` are `2` on the diagonal, `-1` on the first
sub- and super-diagonals, and `0` elsewhere. -/
-- Proof sketch: unfold `pathTridiagonalMatrix` and read off the three cases in the piecewise
-- definition of the tridiagonal entries.
theorem pathTridiagonalMatrix_apply (k : ℕ+) (i j : Fin k) :
    pathTridiagonalMatrix k i j =
      if i = j then 2 else if (i : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (i : ℕ) then -1 else 0 :=
  rfl

/-- The tridiagonal matrix `A_k` is symmetric. -/
theorem pathTridiagonalMatrix_isSymm (k : ℕ+) :
    (pathTridiagonalMatrix k).IsSymm := by
  refine Matrix.IsSymm.ext fun i j ↦ ?_
  by_cases hij : i = j
  · subst hij
    simp [pathTridiagonalMatrix]
  · have hji : j ≠ i := by simpa [eq_comm] using hij
    simp [pathTridiagonalMatrix, hij, hji, or_comm]

/-- The quadratic test function used for the lower-bound construction; this is the textbook
function `f_k`, presented through the Chapter 1 owner `quadraticObjective`. -/
def smoothLowerBoundFunction (L : ℝ) (k : ℕ+) :
    EuclideanSpace ℝ (Fin k) → ℝ :=
  quadraticObjective 0
    (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ))
    ((L / 4) • pathTridiagonalMatrix k)

/-- The gradient of `smoothLowerBoundFunction L k` is the affine map
`x ↦ (L / 4) A_k x - (L / 4) e₁`. -/
theorem smoothLowerBoundFunction_gradient_eq (L : ℝ) (k : ℕ+) :
    ∇ (smoothLowerBoundFunction L k) =
      fun x ↦
        -(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ) +
          (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin x) := by
  simpa [smoothLowerBoundFunction] using
    (quadraticObjective_gradient_eq 0
      (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ))
      ((L / 4) • pathTridiagonalMatrix k)
      ((pathTridiagonalMatrix_isSymm k).smul (L / 4)))

/-- Helper for Definition 2.11: the Euclidean quadratic form of the path tridiagonal matrix agrees
with the matrix quadratic form `xᵀ A_k x`. -/
private lemma pathTridiagonal_inner_eq_dotProduct_mulVec (k : ℕ+)
    (x : EuclideanSpace ℝ (Fin k)) :
    inner ℝ ((pathTridiagonalMatrix k).toEuclideanLin x) x =
      dotProduct x (pathTridiagonalMatrix k *ᵥ x) := by
  -- First rewrite the Euclidean inner product as a dot product on coordinates.
  calc
    inner ℝ ((pathTridiagonalMatrix k).toEuclideanLin x) x =
        dotProduct x ((pathTridiagonalMatrix k).toEuclideanLin x) := by
          simpa [dotProduct_comm] using
            (EuclideanSpace.inner_eq_star_dotProduct ((pathTridiagonalMatrix k).toEuclideanLin x) x)
    _ = dotProduct x (pathTridiagonalMatrix k *ᵥ x) := by
          simp [Matrix.toEuclideanLin_apply, Matrix.toLin'_apply]

-- Proof sketch: unfold `smoothLowerBoundFunction` and `quadraticObjective`, then rewrite the
-- quadratic term in coordinates.
/-- The lower-bound quadratic function is the quadratic form associated to `A_k` together with the
linear term `-(L / 4) x₁`. -/
theorem smoothLowerBoundFunction_apply (L : ℝ) (k : ℕ+)
    (x : EuclideanSpace ℝ (Fin k)) :
    smoothLowerBoundFunction L k x =
      (L / 8) * dotProduct x (pathTridiagonalMatrix k *ᵥ x) -
        (L / 4) * x 0 := by
  -- Rewrite the owner quadratic objective into its linear and quadratic coordinate pieces.
  rw [smoothLowerBoundFunction, quadraticObjective]
  have hlinear :
      inner ℝ (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ)) x =
        -(L / 4) * x 0 := by
    -- Evaluate the first-coordinate basis vector against `x`.
    calc
      inner ℝ (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ)) x =
          -(L / 4) * inner ℝ (EuclideanSpace.single (0 : Fin k) (1 : ℝ)) x := by
            rw [real_inner_smul_left]
      _ = -(L / 4) * ((1 : ℝ) * x 0) := by
            congr 1
            exact EuclideanSpace.inner_single_left (0 : Fin k) (1 : ℝ) x
      _ = -(L / 4) * x 0 := by
            ring
  have hquadratic :
      inner ℝ (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin x) x =
        (L / 4) * dotProduct x (pathTridiagonalMatrix k *ᵥ x) := by
    -- Rewrite the scaled matrix action in coordinates, then factor out the scalar `(L / 4)`.
    calc
      inner ℝ (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin x) x =
          dotProduct x (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin x) := by
            simpa [dotProduct_comm] using
              (EuclideanSpace.inner_eq_star_dotProduct
                (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin x) x)
      _ = dotProduct x ((L / 4) • (pathTridiagonalMatrix k *ᵥ x)) := by
            simp [Matrix.toEuclideanLin_apply, Matrix.toLin'_apply]
      _ = (L / 4) * dotProduct x (pathTridiagonalMatrix k *ᵥ x) := by
            simp
  rw [hlinear, hquadratic]
  ring

/-- The canonical affine-profile point for the lower-bound quadratic on `ℝᵏ`. It is the source
point later extended by zero tails to the ambient hard-instance stationary point in Text 2.13. -/
def smoothLowerBoundFunctionStationaryPoint (k : ℕ+) : EuclideanSpace ℝ (Fin k) :=
  (EuclideanSpace.equiv (Fin k) ℝ).symm
    (fun i : Fin k ↦ 1 - (((i : ℕ) + 1 : ℝ) / ((k : ℕ) + 1 : ℝ)))

/-- Evaluating the canonical affine-profile point of `smoothLowerBoundFunction` returns the
displayed coordinate formula. -/
@[simp] theorem smoothLowerBoundFunctionStationaryPoint_apply (k : ℕ+) (i : Fin k) :
    smoothLowerBoundFunctionStationaryPoint k i =
      1 - (((i : ℕ) + 1 : ℝ) / ((k : ℕ) + 1 : ℝ)) := rfl

/-- Helper for Definition 2.11: differentiating the affine gradient formula shows that the
Hessian operator of `smoothLowerBoundFunction L k` is the constant linear map
`((L / 4) • A_k).toEuclideanLin`. -/
private lemma smoothLowerBoundFunction_hessian_eq_toEuclideanLin (L : ℝ) (k : ℕ+)
    (x : EuclideanSpace ℝ (Fin k)) :
    hessian (smoothLowerBoundFunction L k) x =
      ((((L / 4) • pathTridiagonalMatrix k).toEuclideanLin).toContinuousLinearMap :
        EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin k)) := by
  let A :
      EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
    ((L / 4) • pathTridiagonalMatrix k).toEuclideanLin
  have hgrad :
      ∇ (smoothLowerBoundFunction L k) =
        fun y : EuclideanSpace ℝ (Fin k) ↦
          -(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ) + A y := by
    simpa [A] using smoothLowerBoundFunction_gradient_eq L k
  -- Rewrite the gradient as a constant plus a linear map and differentiate that affine map.
  change fderiv ℝ (∇ (smoothLowerBoundFunction L k)) x = A.toContinuousLinearMap
  rw [hgrad]
  simpa [hessian, A] using
    (((A.toContinuousLinearMap.hasFDerivAt).const_add
      (-(L / 4) • EuclideanSpace.single (0 : Fin k) (1 : ℝ))).fderiv)

-- Proof sketch: rewrite `smoothLowerBoundFunction L k` through the owner `quadraticObjective`,
-- differentiate the quadratic form
-- `x ↦ (L / 8) * ⟪x, A_k x⟫ - (L / 4) * x₁`; the linear term contributes zero to the Hessian,
-- and the quadratic term has constant Hessian `(L / 4) • A_k`.
/-- Definition 2.11: for the textbook lower-bound quadratic `f_k`, the Chapter 1 Hessian matrix is
the constant tridiagonal matrix `(L / 4) A_k`. -/
theorem smoothLowerBoundFunction_hessian_eq_tridiagonal (L : ℝ) (k : ℕ+)
    (x : EuclideanSpace ℝ (Fin k)) :
    ∇² (smoothLowerBoundFunction L k) x =
      (L / 4) • pathTridiagonalMatrix k :=
    by
  -- Compare the Hessian matrix with the intrinsic Hessian operator, then identify that operator.
  apply Matrix.toEuclideanLin.injective
  calc
    (∇² (smoothLowerBoundFunction L k) x).toEuclideanLin =
        hessian (smoothLowerBoundFunction L k) x := by
          simpa using hessianMatrix_toEuclideanLin (smoothLowerBoundFunction L k) x
    _ =
        (((L / 4) • pathTridiagonalMatrix k).toEuclideanLin :
          EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin k)) := by
            exact congrArg ContinuousLinearMap.toLinearMap
              (smoothLowerBoundFunction_hessian_eq_toEuclideanLin L k x)
