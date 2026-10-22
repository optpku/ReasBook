/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_3_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open Seminorm
open scoped BigOperators

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/- Definition 7.12 lies in the chapter's dual-norm / pullback-seminorm domain.

Sampled owner-style declarations:
- project `Seminorm.dualNorm`
- project `Seminorm.dualNorm_apply`
- mathlib `Seminorm.comp`
- mathlib `normSeminorm`

Best owner abstraction:
- source-facing: `matrixInducedEuclideanSeminorm A`
- core/canonical: `Seminorm.comp (normSeminorm ℝ Eₘ) A.toEuclideanLin`
- bridge/view: `matrixInducedEuclideanSeminorm_apply`,
  `matrixInducedEuclideanSeminorm_isNorm`

Primitive data:
- a matrix `A : Matrix (Fin m) (Fin n) ℝ`

Derived API:
- pointwise evaluation as `x ↦ ‖A x‖`
- the `Seminorm.IsNorm` instance under injectivity of `A.toEuclideanLin`
- the dual norm formula under an explicit full-column-rank hypothesis, through the chapter owner
  `Seminorm.dualNorm`

Source/core/bridge triage:
- source-facing: the seminorm induced on `ℝⁿ` by the Euclidean norm on `ℝᵐ`
- core/canonical: pullback of `normSeminorm` along `A.toEuclideanLin`
- bridge/view: Gram-form and row-pairing formulas, plus the dual-norm formula

This refinement removes the duplicate local `vectorDualNorm` owner and exposes the matrix-induced
object at the canonical seminorm layer. The textbook function `x ↦ ‖A x‖` is now the evaluation
surface of that owner, while duality uses the existing project owner `Seminorm.dualNorm`.
-/

/-- The Euclidean seminorm from Definition 7.12 on `ℝⁿ` induced by a matrix `A ∈ ℝ^(m × n)`,
namely the pullback of the Euclidean norm on `ℝᵐ` along `A.toEuclideanLin`. When `A` has full
column rank, the derived theorem `matrixInducedEuclideanSeminorm_isNorm` upgrades this seminorm
to the textbook norm `x ↦ ‖A x‖`. -/
def matrixInducedEuclideanSeminorm (A : Matrix (Fin m) (Fin n) ℝ) : Seminorm ℝ Eₙ :=
  Seminorm.comp (normSeminorm ℝ Eₘ) A.toEuclideanLin

/-- Evaluating the induced seminorm recovers the textbook formula `x ↦ ‖A x‖`. -/
theorem matrixInducedEuclideanSeminorm_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Eₙ) :
    matrixInducedEuclideanSeminorm A x = ‖A.toEuclideanLin x‖ :=
  rfl

/-- If `A` has full column rank, the induced Euclidean seminorm is a genuine norm. -/
theorem matrixInducedEuclideanSeminorm_isNorm
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) :
    Seminorm.IsNorm (matrixInducedEuclideanSeminorm A : Seminorm ℝ Eₙ) := by
  refine ⟨?_⟩
  intro x hx
  apply hA
  simpa using norm_eq_zero.mp (by
    simpa [matrixInducedEuclideanSeminorm_apply] using hx)

/-- If `A` has full column rank, then the induced Euclidean seminorm vanishes only at the
origin. -/
theorem matrixInducedEuclideanSeminorm_eq_zero_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) {x : Eₙ} :
    matrixInducedEuclideanSeminorm A x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    exact (matrixInducedEuclideanSeminorm_isNorm A hA).eq_zero_of_map_eq_zero hx
  · rintro rfl
    simp [matrixInducedEuclideanSeminorm_apply]

-- Proof sketch: unfold `matrixInducedEuclideanSeminorm`, rewrite `‖A x‖^2` as
-- `⟪A x, A x⟫`, and identify this with the Gram quadratic form for `Aᵀ A`.
/-- The induced Euclidean seminorm is the square root of the quadratic form associated to the
Gram matrix `G = Aᵀ A`. -/
theorem matrixInducedEuclideanSeminorm_eq_sqrt_gram
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Eₙ) :
    matrixInducedEuclideanSeminorm A x =
      Real.sqrt (inner ℝ ((A.transpose * A).toEuclideanLin x) x) := by
  -- Rewrite `‖A x‖` as `√⟪A x, A x⟫`, then move one copy of `A` across the inner product.
  rw [matrixInducedEuclideanSeminorm_apply, norm_eq_sqrt_real_inner]
  have hquad :
      inner ℝ (A.toEuclideanLin x) (A.toEuclideanLin x) =
        inner ℝ ((A.transpose * A).toEuclideanLin x) x := by
    calc
      inner ℝ (A.toEuclideanLin x) (A.toEuclideanLin x)
          = inner ℝ x (A.toEuclideanLin.adjoint (A.toEuclideanLin x)) := by
              rw [A.toEuclideanLin.adjoint_inner_right]
      _ = inner ℝ x (A.transpose.toEuclideanLin (A.toEuclideanLin x)) := by
            simpa using congrArg
              (fun T : Eₘ →ₗ[ℝ] Eₙ ↦ inner ℝ x (T (A.toEuclideanLin x)))
              (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
      _ = inner ℝ x ((A.transpose * A).toEuclideanLin x) := by
            simp
      _ = inner ℝ ((A.transpose * A).toEuclideanLin x) x := by
            rw [real_inner_comm]
  rw [hquad]

/-- Helper for Definition 7.12: the Gram bilinear form attached to `A` evaluates to
`(x, y) ↦ ⟪(Aᵀ A) x, y⟫`. -/
private def gramBilin (A : Matrix (Fin m) (Fin n) ℝ) : LinearMap.BilinForm ℝ Eₙ :=
  (innerₗ Eₙ).compl₁₂ ((A.transpose * A).toEuclideanLin) LinearMap.id

/-- Helper for Definition 7.12: evaluating the Gram bilinear form gives the expected matrix-inner
formula. -/
@[simp] private theorem gramBilin_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (x y : Eₙ) :
    gramBilin A x y = inner ℝ ((A.transpose * A).toEuclideanLin x) y :=
  rfl

/-- Helper for Definition 7.12: injectivity of `A.toEuclideanLin` implies injectivity of the raw
matrix action `A.mulVec`. -/
private theorem mulVec_injective_of_toEuclideanLin_injective
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) :
    Function.Injective A.mulVec := by
  intro x y hxy
  have hxy' : A.toEuclideanLin (WithLp.toLp 2 x) = A.toEuclideanLin (WithLp.toLp 2 y) := by
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin] using congrArg (WithLp.toLp 2) hxy
  have hEq := hA hxy'
  simpa using congrArg WithLp.ofLp hEq

/-- Helper for Definition 7.12: the Gram operator attached to `Aᵀ A` is self-adjoint. -/
private theorem gramMatrix_toEuclideanLin_adjoint_eq
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ((A.transpose * A).toEuclideanLin).adjoint = (A.transpose * A).toEuclideanLin := by
  have hGramTranspose :
      (A.transpose * A).transpose = A.transpose * A := by
    -- The Gram matrix is fixed by transpose, so its Euclidean operator is self-adjoint.
    simp [Matrix.transpose_mul]
  calc
    ((A.transpose * A).toEuclideanLin).adjoint
        = ((A.transpose * A).transpose).toEuclideanLin := by
            simpa using (Matrix.toEuclideanLin_conjTranspose_eq_adjoint (A.transpose * A)).symm
    _ = (A.transpose * A).toEuclideanLin := by
          simp [hGramTranspose]

/-- Helper for Definition 7.12: the Gram bilinear form is symmetric because `Aᵀ A` is a
symmetric matrix. -/
private theorem gramBilin_isSymm
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (gramBilin A).IsSymm := by
  refine ⟨fun x y => ?_⟩
  let G : Matrix (Fin n) (Fin n) ℝ := A.transpose * A
  -- Route correction: package symmetry as self-adjointness of the Gram operator before rewriting
  -- the bilinear form, rather than expanding matrix entries.
  have hGadj : G.toEuclideanLin.adjoint = G.toEuclideanLin := by
    simpa [G] using gramMatrix_toEuclideanLin_adjoint_eq A
  -- Move the Gram operator across the inner product, then use self-adjointness.
  calc
    gramBilin A x y = inner ℝ x (G.toEuclideanLin.adjoint y) := by
      rw [gramBilin_apply]
      simpa [G] using (G.toEuclideanLin.adjoint_inner_right x y).symm
    _ = inner ℝ x (G.toEuclideanLin y) := by rw [hGadj]
    _ = inner ℝ (G.toEuclideanLin y) x := by rw [real_inner_comm]
    _ = gramBilin A y x := by
      rw [gramBilin_apply]

/-- Helper for Definition 7.12: full column rank makes the Gram bilinear form positive
definite. -/
private theorem gramBilin_posDef
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) :
    (gramBilin A).toQuadraticMap.PosDef := by
  let _ : Seminorm.IsNorm (matrixInducedEuclideanSeminorm A : Seminorm ℝ Eₙ) :=
    matrixInducedEuclideanSeminorm_isNorm A hA
  intro x hx
  have hxNorm : 0 < matrixInducedEuclideanSeminorm A x :=
    Seminorm.map_pos_of_ne_zero (matrixInducedEuclideanSeminorm A) hx
  -- Rewrite positivity of the induced norm as positivity of the Gram quadratic form.
  rw [matrixInducedEuclideanSeminorm_eq_sqrt_gram] at hxNorm
  simpa [gramBilin, LinearMap.BilinMap.toQuadraticMap_apply] using Real.sqrt_pos.1 hxNorm

/-- Helper for Definition 7.12: full column rank makes the Gram matrix `Aᵀ A` positive
definite. -/
private theorem gramMatrix_posDef_of_toEuclideanLin_injective
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) :
    (A.transpose * A).PosDef := by
  -- Transport full column rank from `toEuclideanLin` to the raw matrix action.
  simpa using
    Matrix.PosDef.conjTranspose_mul_self A
      (mulVec_injective_of_toEuclideanLin_injective A hA)

/-- Helper for Definition 7.12: after identifying `G = Aᵀ A`, the induced Euclidean operator of
`G` composed with that of `G⁻¹` is the identity. -/
private theorem gramMatrix_toEuclideanLin_inv_apply
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin)
    (g : Eₙ) :
    let G : Matrix (Fin n) (Fin n) ℝ := A.transpose * A
    let _ : Invertible G := (gramMatrix_posDef_of_toEuclideanLin_injective A hA).isUnit.invertible
    G.toEuclideanLin (G⁻¹.toEuclideanLin g) = g := by
  let G : Matrix (Fin n) (Fin n) ℝ := A.transpose * A
  let _ : Invertible G := (gramMatrix_posDef_of_toEuclideanLin_injective A hA).isUnit.invertible
  have hInvOfLp : (G⁻¹.toEuclideanLin g).ofLp = G⁻¹ *ᵥ g.ofLp := by
    -- Unfold one application of `toEuclideanLin` to expose the inverse matrix action.
    rw [Matrix.toEuclideanLin]
    simp [Matrix.ofLp_toLpLin]
  have hoflp : (G.toEuclideanLin (G⁻¹.toEuclideanLin g)).ofLp = g.ofLp := by
    -- Collapse the matrix-side composition `G * G⁻¹` before returning to `EuclideanSpace`.
    calc
      (G.toEuclideanLin (G⁻¹.toEuclideanLin g)).ofLp
          = G *ᵥ (G⁻¹.toEuclideanLin g).ofLp := by
              rw [Matrix.toEuclideanLin]
              simp [Matrix.ofLp_toLpLin]
      _ = G *ᵥ (G⁻¹ *ᵥ g.ofLp) := by
            rw [hInvOfLp]
      _ = (G * G⁻¹) *ᵥ g.ofLp := by
            rw [Matrix.mulVec_mulVec]
      _ = g.ofLp := by
            rw [Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  ext i
  exact congrArg (fun v : Fin n → ℝ ↦ v i) hoflp

/-- Helper for Definition 7.12: the pullback seminorm coincides with the Chapter 4 seminorm
induced by the Gram bilinear form. -/
private theorem matrixInducedEuclideanSeminorm_eq_gramBilin_primal
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hPos : (gramBilin A).toQuadraticMap.PosDef) :
    matrixInducedEuclideanSeminorm A = (gramBilin A).primalSeminorm hPos := by
  ext x
  -- Both seminorms are defined by the same Gram quadratic form.
  rw [LinearMap.BilinForm.primalSeminorm_apply]
  simpa [gramBilin, LinearMap.BilinMap.toQuadraticMap_apply] using
    matrixInducedEuclideanSeminorm_eq_sqrt_gram A x

/-- Helper for Definition 7.12: the inverse Gram vector represents evaluation against `g`
through the Gram bilinear form. -/
private theorem gramBilin_inverseGram_apply
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin)
    (g x : Eₙ) :
    gramBilin A (((A.transpose * A)⁻¹).toEuclideanLin g) x = inner ℝ g x := by
  let G : Matrix (Fin n) (Fin n) ℝ := A.transpose * A
  let _ : Invertible G := (gramMatrix_posDef_of_toEuclideanLin_injective A hA).isUnit.invertible
  -- Collapse `G ∘ G⁻¹` on the matrix side before comparing inner products.
  have hGramInv : G.toEuclideanLin (G⁻¹.toEuclideanLin g) = g := by
    simpa [G] using gramMatrix_toEuclideanLin_inv_apply A hA g
  change inner ℝ (G.toEuclideanLin (G⁻¹.toEuclideanLin g)) x = inner ℝ g x
  rw [hGramInv]

/-- Helper for Definition 7.12: the Chapter 4 dual preimage for the Gram bilinear form pairs
with `g` as the inverse-Gram quadratic form. -/
private theorem gramBilin_dualPreimage_eval_eq_inverseGram
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin)
    (g : Eₙ) :
    let B : LinearMap.BilinForm ℝ Eₙ := gramBilin A
    let hPos : B.toQuadraticMap.PosDef := gramBilin_posDef A hA
    let G : Matrix (Fin n) (Fin n) ℝ := A.transpose * A
    let _ : Invertible G := (gramMatrix_posDef_of_toEuclideanLin_injective A hA).isUnit.invertible
    let φ : Module.Dual ℝ Eₙ := (InnerProductSpace.toDual ℝ Eₙ g).toLinearMap
    φ (B.dualPreimage hPos φ) = inner ℝ g (G⁻¹.toEuclideanLin g) := by
  let B : LinearMap.BilinForm ℝ Eₙ := gramBilin A
  let hPos : B.toQuadraticMap.PosDef := gramBilin_posDef A hA
  let hSymm : B.IsSymm := gramBilin_isSymm A
  let G : Matrix (Fin n) (Fin n) ℝ := A.transpose * A
  let _ : Invertible G := (gramMatrix_posDef_of_toEuclideanLin_injective A hA).isUnit.invertible
  let φ : Module.Dual ℝ Eₙ := (InnerProductSpace.toDual ℝ Eₙ g).toLinearMap
  -- Compare the dual-preimage evaluation with the inverse-Gram vector through symmetry of `B`.
  calc
    φ (B.dualPreimage hPos φ)
        = B (G⁻¹.toEuclideanLin g) (B.dualPreimage hPos φ) := by
            simpa [B, G, φ] using
              (gramBilin_inverseGram_apply A hA g (B.dualPreimage hPos φ)).symm
    _ = B (B.dualPreimage hPos φ) (G⁻¹.toEuclideanLin g) := by
          exact hSymm.eq _ _
    _ = φ (G⁻¹.toEuclideanLin g) := by
          exact B.dualPreimage_apply hPos φ (G⁻¹.toEuclideanLin g)
    _ = inner ℝ g (G⁻¹.toEuclideanLin g) := by
          rfl

-- Proof sketch: expand the Euclidean norm of `A x` as the sum of the squares of its coordinates;
-- these coordinates are the pairings with the rows of `A`, equivalently the columns of `Aᵀ`.
/-- The induced Euclidean seminorm is the square root of the sum of the squared pairings with the
columns of `Aᵀ`, i.e. the rows of `A`. -/
theorem matrixInducedEuclideanSeminorm_eq_sqrt_sum_row_pairings
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Eₙ) :
    matrixInducedEuclideanSeminorm A x =
      Real.sqrt (∑ i : Fin m, (A i ⬝ᵥ x.ofLp) ^ (2 : ℕ)) := by
  -- Expand the Euclidean norm of `A x` coordinatewise and rewrite each coordinate as a row pairing.
  rw [matrixInducedEuclideanSeminorm_apply]
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Real.norm_eq_abs] using
    (EuclideanSpace.norm_eq (A.toEuclideanLin x))

/-- Definition 7.12: if `A` has full column rank, then the dual norm of the induced Euclidean
seminorm is `g ↦ √⟪g, (Aᵀ A)⁻¹ g⟫`. -/
theorem dualNorm_matrixInducedEuclideanSeminorm_eq_sqrt_inverse_gram
    (A : Matrix (Fin m) (Fin n) ℝ)
    (hA : Function.Injective A.toEuclideanLin) (g : Eₙ) :
    by
      let _ : Seminorm.IsNorm (matrixInducedEuclideanSeminorm A : Seminorm ℝ Eₙ) :=
        matrixInducedEuclideanSeminorm_isNorm A hA
      exact (matrixInducedEuclideanSeminorm A).dualNorm g =
        Real.sqrt (inner ℝ g (((A.transpose * A)⁻¹).toEuclideanLin g)) := by
  let _ : Seminorm.IsNorm (matrixInducedEuclideanSeminorm A : Seminorm ℝ Eₙ) :=
    matrixInducedEuclideanSeminorm_isNorm A hA
  let B : LinearMap.BilinForm ℝ Eₙ := gramBilin A
  let hPos : B.toQuadraticMap.PosDef := gramBilin_posDef A hA
  let hSymm : B.IsSymm := gramBilin_isSymm A
  let G : Matrix (Fin n) (Fin n) ℝ := A.transpose * A
  let _ : Invertible G := (gramMatrix_posDef_of_toEuclideanLin_injective A hA).isUnit.invertible
  let φ : Module.Dual ℝ Eₙ := (InnerProductSpace.toDual ℝ Eₙ g).toLinearMap
  have hPrimal :
      matrixInducedEuclideanSeminorm A = B.primalSeminorm hPos :=
    matrixInducedEuclideanSeminorm_eq_gramBilin_primal A hPos
  have hDualValue :
      φ (B.dualPreimage hPos φ) = inner ℝ g (G⁻¹.toEuclideanLin g) := by
    simpa [B, hPos, hSymm, G, φ] using gramBilin_dualPreimage_eval_eq_inverseGram A hA g
  -- Rewrite the pullback seminorm as the Gram bilinear-form seminorm and invoke the
  -- existing bilinear-form dual-norm formula.
  calc
    (matrixInducedEuclideanSeminorm A).dualNorm g =
        B.dualNorm hPos φ := by
          simpa [hPrimal] using
            LinearMap.BilinForm.seminormDualNorm_eq_dualNorm_toDual B hPos g
    _ =
        Real.sqrt (φ (B.dualPreimage hPos φ)) := by
          simpa [φ] using LinearMap.BilinForm.dualNorm_apply B hSymm hPos φ
    _ = Real.sqrt (inner ℝ g (G⁻¹.toEuclideanLin g)) := by
          rw [hDualValue]

end
