/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 7.23 lies in the positive-definite matrix / induced-norm domain.

Sampled owner-style declarations:
- `LinearMap.BilinForm.primalSeminorm` in `Chap04/Definition_4_3_4`
- `LinearMap.BilinForm.dualNorm` in `Chap04/Definition_4_3_4`
- `Matrix.toEuclideanLin` in mathlib
- `Matrix.toBilin'` in mathlib, for the coordinate-space matrix bilinear-form owner
- `Matrix.PosDef.toQuadraticForm'` in mathlib

Best owner abstraction:
- source-facing: the norm induced on `ℝⁿ` by a positive-definite matrix `G`
- core/canonical: the Chapter 4 bilinear-form owner
  `LinearMap.BilinForm.primalSeminorm B`
- bridge/view: the canonical Euclidean-space bilinear form induced by `Matrix.toEuclideanLin G`

Primitive data:
- a matrix `G : Matrix (Fin n) (Fin n) ℝ`
- its positive-definiteness proof `hG : G.PosDef`

Derived API:
- the source-facing seminorm owner `positiveDefMatrixNorm G hG`
- the source-facing notation `‖x‖[⟨G, hG⟩]`
- the canonical dual notation `‖s‖[⟨G, hG⟩,*]`
- the inverse-matrix formula `√⟪s, G⁻¹ s⟫`

Source/core/bridge triage:
- source-facing: Definition 7.23's matrix-induced norm
- core/canonical: `LinearMap.BilinForm.primalSeminorm` and `Seminorm.dualNorm`
- bridge/view: the bilinear form attached to `Matrix.toEuclideanLin`

This refinement removes the duplicate public matrix-to-bilinear-form owner and the notation-only
wrapper abbrevs. The source-facing matrix object remains a `Seminorm`, defined directly from the
canonical Euclidean linear operator attached to the matrix, and the dual norm is reused from the
Chapter 2 owner
`Seminorm.dualNorm`.
-/

private def matrixBilin (G : Matrix (Fin n) (Fin n) ℝ) : LinearMap.BilinForm ℝ E :=
  ((innerSL ℝ).comp (Matrix.toEuclideanLin G).toContinuousLinearMap).toBilinForm

private theorem matrixToBilinForm_isSymm_of_posDef
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    (matrixBilin G).IsSymm := by
  -- A positive semidefinite Euclidean operator is self-adjoint, so the induced bilinear form is
  -- symmetric.
  rw [LinearMap.BilinForm.isSymm_def]
  intro x y
  change inner ℝ ((Matrix.toEuclideanLin G) x) y = inner ℝ ((Matrix.toEuclideanLin G) y) x
  have hPosLin : (Matrix.toEuclideanLin G).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hG.posSemidef
  simpa [real_inner_comm] using hPosLin.isSymmetric x y

private theorem matrixToBilinForm_posDef_of_posDef
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    (matrixBilin G).toQuadraticMap.PosDef := by
  -- The quadratic form attached to `matrixBilin G` is nonnegative by positivity, and it vanishes
  -- only at `0` by the strict positivity of a positive-definite matrix.
  rw [QuadraticMap.posDef_iff_nonneg]
  refine ⟨?_, ?_⟩
  · intro x
    change 0 ≤ inner ℝ ((Matrix.toEuclideanLin G) x) x
    have hPosLin : (Matrix.toEuclideanLin G).IsPositive :=
      Matrix.isPositive_toEuclideanLin_iff.mpr hG.posSemidef
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right x
  · intro x hx
    by_contra hx0
    have hx' : x.ofLp ≠ 0 := by
      intro h0
      apply hx0
      ext i
      exact congrArg (fun y : Fin n → ℝ ↦ y i) h0
    have hdot : 0 < dotProduct x.ofLp (G.mulVec x.ofLp) := by
      simpa using hG.dotProduct_mulVec_pos hx'
    have hdot_eq :
        inner ℝ ((Matrix.toEuclideanLin G) x) x =
          dotProduct x.ofLp (G.mulVec x.ofLp) := by
      have hinner := EuclideanSpace.inner_eq_star_dotProduct ((Matrix.toEuclideanLin G) x) x
      simp only [Matrix.ofLp_toLpLin] at hinner
      simpa [dotProduct_comm] using hinner
    have hx_inner : inner ℝ ((Matrix.toEuclideanLin G) x) x = 0 := by
      simpa [matrixBilin] using hx
    rw [hdot_eq] at hx_inner
    exact hdot.ne' hx_inner

/-- Definition 7.23 in owner form: a positive-definite matrix `G` induces the canonical seminorm
`x ↦ √⟪Gx, x⟫` on `ℝⁿ`. -/
def positiveDefMatrixNorm
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    Seminorm ℝ E :=
  LinearMap.BilinForm.primalSeminorm
    (matrixBilin G)
    (matrixToBilinForm_posDef_of_posDef G hG)

instance positiveDefMatrixNorm_isNorm
    (G : Matrix (Fin n) (Fin n) ℝ) (hG : G.PosDef) :
    (positiveDefMatrixNorm G hG).IsNorm :=
  by
    simpa [positiveDefMatrixNorm] using
      (LinearMap.BilinForm.primalSeminorm_isNorm
        (matrixBilin G)
        (matrixToBilinForm_posDef_of_posDef G hG))

namespace PositiveDefMatrixNorm

/- Lean notation for the primal norm induced by a positive-definite matrix. -/
scoped notation:max "‖" x "‖[" G "]" =>
  positiveDefMatrixNorm (Subtype.val G) (Subtype.property G) x

/- Lean notation for the dual norm induced by a positive-definite matrix. -/
scoped notation:max "‖" s "‖[" G ",*]" =>
  Seminorm.dualNorm (positiveDefMatrixNorm (Subtype.val G) (Subtype.property G)) s

end PositiveDefMatrixNorm

open scoped PositiveDefMatrixNorm

-- Proof sketch: `positiveDefMatrixNorm G hG` is the Chapter 4 bilinear-form-induced seminorm for
-- the Euclidean bilinear form associated with `Matrix.toEuclideanLin G`, whose pointwise formula
-- is exactly `√⟪Gx, x⟫`.
/-- Evaluating `positiveDefMatrixNorm G hG` recovers the textbook formula `√⟪Gx, x⟫`. -/
theorem positiveDefMatrixNorm_def
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (x : E) :
    ‖x‖[G] =
      Real.sqrt (inner ℝ ((Matrix.toEuclideanLin G.1) x) x) := by
  -- Unfold the source-facing owner and evaluate the underlying Chapter 4 primal seminorm.
  rw [positiveDefMatrixNorm]
  rw [LinearMap.BilinForm.primalSeminorm_apply]
  rfl

-- Proof sketch: the dual norm is the chapter owner `Seminorm.dualNorm`, so its defining
-- support-function formula is the canonical theorem `Seminorm.dualNorm_apply`.
/-- The dual norm of `positiveDefMatrixNorm G hG` is the support function of the `G`-unit ball. -/
theorem positiveDefMatrixNorm_dualNorm_apply
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (s : E) :
    ‖s‖[G,*] =
      sSup ((fun x : E ↦ inner ℝ s x) '' {x | ‖x‖[G] ≤ 1}) := by
  -- Expand the Chapter 2 dual norm owner on the seminorm induced by `G`.
  rw [Seminorm.dualNorm_apply]

/-- Helper for Definition 7.23: the canonical `matrixBilin G` dual preimage of `s` is the vector
obtained by applying the inverse matrix `G⁻¹` to `s`. -/
private theorem posDef_toEuclideanLin_inv_comp
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (s : E) :
    (Matrix.toEuclideanLin G.1) ((Matrix.toEuclideanLin G.1⁻¹) s) = s := by
  have hdet : IsUnit G.1.det := G.1.isUnit_iff_isUnit_det.mp G.2.isUnit
  letI : Invertible G.1 := Matrix.invertibleOfIsUnitDet _ hdet
  -- Move to coordinates so that `G * G⁻¹ = 1` cancels directly.
  ext i
  simp [Matrix.ofLp_toLpLin, Matrix.mulVec_mulVec,
    Matrix.mul_inv_of_invertible]

/-- Helper for Definition 7.23: the canonical `matrixBilin G` dual preimage of `s` is the vector
obtained by applying the inverse matrix `G⁻¹` to `s`. -/
private theorem matrixBilinDualPreimage_eq_inv_toEuclideanLin
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (s : E) :
    (matrixBilin G.1).dualPreimage
        (matrixToBilinForm_posDef_of_posDef G.1 G.2)
        ((InnerProductSpace.toDual ℝ E s).toLinearMap) =
      (Matrix.toEuclideanLin G.1⁻¹) s := by
  let B : LinearMap.BilinForm ℝ E := matrixBilin G.1
  let hPos : B.toQuadraticMap.PosDef := matrixToBilinForm_posDef_of_posDef G.1 G.2
  let hnd : B.Nondegenerate := B.nondegenerate_of_posDef hPos
  -- Compare the two candidates after applying the `B.toDual` equivalence once.
  apply (B.toDual hnd).injective
  ext y
  calc
    B (B.dualPreimage hPos ((InnerProductSpace.toDual ℝ E s).toLinearMap)) y =
        (InnerProductSpace.toDual ℝ E s).toLinearMap y := by
      exact B.dualPreimage_apply hPos ((InnerProductSpace.toDual ℝ E s).toLinearMap) y
    _ = ((B.toDual hnd) ((Matrix.toEuclideanLin G.1⁻¹) s)) y := by
      rw [LinearMap.BilinForm.toDual_def]
      change inner ℝ s y =
        inner ℝ ((Matrix.toEuclideanLin G.1) ((Matrix.toEuclideanLin G.1⁻¹) s)) y
      rw [posDef_toEuclideanLin_inv_comp G s]

-- Proof sketch: compare the Chapter 2 support-function definition of
-- `(positiveDefMatrixNorm G hG).dualNorm` with the Chapter 4 strong-dual owner for the bilinear
-- form induced by `Matrix.toEuclideanLin G`, then evaluate that owner by the inverse-matrix
-- formula.
/-- The dual norm of `positiveDefMatrixNorm G hG` is `√⟪s, G⁻¹ s⟫`. -/
theorem positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv
    (G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef}) (s : E) :
    ‖s‖[G,*] =
      Real.sqrt (inner ℝ s ((Matrix.toEuclideanLin G.1⁻¹) s)) := by
  let B : LinearMap.BilinForm ℝ E := matrixBilin G.1
  let hSymm : B.IsSymm := matrixToBilinForm_isSymm_of_posDef G.1 G.2
  let hPos : B.toQuadraticMap.PosDef := matrixToBilinForm_posDef_of_posDef G.1 G.2
  -- Rewrite the source-facing dual norm through the Chapter 4 bilinear-form owner.
  calc
    ‖s‖[G,*] = B.dualNorm hPos (InnerProductSpace.toDual ℝ E s).toLinearMap := by
      simpa [B, hPos, positiveDefMatrixNorm] using
        (LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hPos s)
    _ =
        Real.sqrt
          ((InnerProductSpace.toDual ℝ E s)
            (B.dualPreimage hPos (InnerProductSpace.toDual ℝ E s).toLinearMap)) := by
      simpa [B, hSymm, hPos] using
        (LinearMap.BilinForm.dualNorm_apply_strongDual
          B hSymm hPos (InnerProductSpace.toDual ℝ E s))
    _ = Real.sqrt (inner ℝ s ((Matrix.toEuclideanLin G.1⁻¹) s)) := by
      rw [matrixBilinDualPreimage_eq_inv_toEuclideanLin G s]
      simp [InnerProductSpace.toDual_apply_apply]

end
