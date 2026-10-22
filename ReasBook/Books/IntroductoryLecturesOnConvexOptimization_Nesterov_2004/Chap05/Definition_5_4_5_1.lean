/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_56
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 5.4.5.1 lies in the minimum-volume enclosing-ellipsoid / constrained-optimization
domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
* `𝕊^n₊₊` and `strictPositiveSemidefiniteCone_posDef` in `Chap05/Definition_5_4_4_5`, the
  chapter owner and matrix-level bridge for positive-definite symmetric shapes;
* `minimumVolumeEnclosingEllipsoidBarrierDomain` in `Chap05/Definition_5_4_5_2`, the immediate
  downstream MVEE barrier domain already written on `𝕊^n₊₊ × Eₙ × ℝ`;
* `circumscribedEllipsoidBarrierDomain` in `Chap05/Definition_5_4_5_5`, the nearby ellipsoid
  barrier file that uses the same strict-cone owner level rather than a raw positive-definite
  subtype.

Best owner abstraction:
* source-facing data: the finite point family `a`, the enclosing-ellipsoid set `W(H, v)` with shape
  `H : 𝕊^n₊₊`, and the epigraph variable `τ`;
* core/canonical: `SetConstrainedMinimizationProblem` on the ambient decision-variable type
  `𝕊^n₊₊ × Eₙ × ℝ`;
* bridge/view: the canonical coercion from `H : 𝕊^n₊₊` to its ambient symmetric matrix in `𝕊^n`,
  followed by the matrix view in `Matrix (Fin n) (Fin n) ℝ`.

Primitive data:
* the feasible set of strict-cone shapes, centers, and epigraph variables satisfying the
  enclosing inequalities;
* the objective `τ`.

Derived API:
* the source-facing image-form notation `W(H, v)`;
* its bridge to the Chapter 3 ellipsoid owner `E(H, x̄)`;
* the membership and objective-expansion lemmas below.

Source/core/bridge triage:
* source-facing: the notation `W(H, v)` and the textbook feasible inequalities for
  `(H, v, τ) ∈ 𝕊^n₊₊ × Eₙ × ℝ`;
* core/canonical: `SetConstrainedMinimizationProblem`;
* bridge/view: the matrix-action coercion `H ↦ ((H : 𝕊^n) : Matrix (Fin n) (Fin n) ℝ)`,
  followed by the Chapter 3 ellipsoid owner `E(H, x̄)`. -/

noncomputable section

open Matrix
open StrictPositiveSemidefiniteCone
open scoped EllipsoidNotation RealSymmetricMatrixSpace

variable {ι : Type*} {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- Definition 5.4.5.1: the source-facing image-form ellipsoid `W(H, v)` is the set of points
`x` satisfying the textbook constraint `‖H x - v‖ ≤ 1`. -/
def enclosingEllipsoid
    (H : 𝕊^n₊₊) (v : Eₙ) : Set Eₙ :=
  {x | ‖(toMatrix H).toEuclideanLin x - v‖ ≤ 1}

namespace EnclosingEllipsoidNotation

/-- The source-facing image-form ellipsoid `W(H, v)`. -/
scoped notation:max "W(" H ", " v ")" =>
  enclosingEllipsoid H v

end EnclosingEllipsoidNotation

open scoped EnclosingEllipsoidNotation

/-- Helper for Definition 5.4.5.1: applying `toMatrix H` after its inverse action gives back the
original Euclidean vector. -/
private theorem toEuclideanLin_inv_cancel
    (H : 𝕊^n₊₊) (z : Eₙ) :
    (toMatrix H).toEuclideanLin (((toMatrix H)⁻¹).toEuclideanLin z) = z := by
  have hM : (((H : 𝕊^n) : Mat)).PosDef := strictPositiveSemidefiniteCone_posDef H
  have hMdet : IsUnit (((H : 𝕊^n) : Mat).det) := isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  have hmul : (((H : 𝕊^n) : Mat)) * ((((H : 𝕊^n) : Mat))⁻¹) = 1 :=
    Matrix.mul_nonsing_inv (A := ((H : 𝕊^n) : Mat)) hMdet
  -- Convert the Euclidean action to matrix multiplication and cancel the inverse.
  ext i
  simpa [StrictPositiveSemidefiniteCone.toMatrix_def, Matrix.ofLp_toEuclideanLin_apply,
    Matrix.mulVec_mulVec, hmul]

/-- Helper for Definition 5.4.5.1: the inverse of `(H⁻¹)^2` is `H^2` at the matrix level. -/
private theorem inverse_square_inv_eq_mul_self
    (H : 𝕊^n₊₊) :
    (((toMatrix H)⁻¹ * (toMatrix H)⁻¹)⁻¹) = toMatrix H * toMatrix H := by
  let M : Mat := toMatrix H
  have hM : M.PosDef := by
    simpa [M] using strictPositiveSemidefiniteCone_posDef H
  have hMdet : IsUnit M.det := isUnit_iff_ne_zero.mpr (ne_of_gt hM.det_pos)
  -- Reverse the inverse of a product and then collapse the double inverse of `M`.
  calc
    ((M⁻¹ * M⁻¹)⁻¹) = (M⁻¹)⁻¹ * (M⁻¹)⁻¹ := by
      rw [Matrix.mul_inv_rev]
    _ = M⁻¹⁻¹ * M := by
      rw [Matrix.nonsing_inv_nonsing_inv (A := M) hMdet]
    _ = M * M := by
      rw [Matrix.nonsing_inv_nonsing_inv (A := M) hMdet]

/-- Helper for Definition 5.4.5.1: the quadratic form defined by `((H⁻¹)^2)⁻¹` is the squared
norm of the Euclidean action of `H`. -/
private theorem inverse_square_quadratic_eq_norm_sq
    (H : 𝕊^n₊₊) (y : Eₙ) :
    inner ℝ ((((toMatrix H)⁻¹ * (toMatrix H)⁻¹)⁻¹).toEuclideanLin y) y =
      ‖(toMatrix H).toEuclideanLin y‖ ^ (2 : ℕ) := by
  let M : Mat := toMatrix H
  have hMsymm : M.IsSymm := by
    simpa [M] using strictPositiveSemidefiniteCone_isSymm H
  have hmul :
      ((M * M).toEuclideanLin y) = M.toEuclideanLin (M.toEuclideanLin y) := by
    -- This is the Euclidean-space version of `mulVec_mulVec`.
    ext i
    simp [M, Matrix.mulVec_mulVec]
  -- Rewrite the quadratic form through `M * M`, then use transpose-adjointness and symmetry.
  calc
    inner ℝ ((((M⁻¹ * M⁻¹)⁻¹).toEuclideanLin y)) y =
        inner ℝ ((M * M).toEuclideanLin y) y := by
          rw [inverse_square_inv_eq_mul_self (H := H)]
    _ = inner ℝ (M.toEuclideanLin (M.toEuclideanLin y)) y := by
      rw [hmul]
    _ = inner ℝ (M.toEuclideanLin y) (Mᵀ.toEuclideanLin y) := by
      rw [← M.toEuclideanLin.adjoint_inner_right]
      exact congrArg
        (fun z : Eₙ ↦ inner ℝ (M.toEuclideanLin y) z)
        (congrArg
          (fun T : Eₙ →ₗ[ℝ] Eₙ ↦ T y)
          (Matrix.toEuclideanLin_conjTranspose_eq_adjoint M).symm)
    _ = inner ℝ (M.toEuclideanLin y) (M.toEuclideanLin y) := by
      rw [hMsymm.eq]
    _ = ‖M.toEuclideanLin y‖ ^ (2 : ℕ) := by
      rw [real_inner_self_eq_norm_sq]

/-- The image-form ellipsoid `W(H, v)` is the Chapter 3 affine ellipsoid with shape
`(H⁻¹)^2` and center `H⁻¹ v`. -/
theorem enclosingEllipsoid_eq_affineEllipsoid
    (H : 𝕊^n₊₊) (v : Eₙ) :
    W(H, v) = E((toMatrix H)⁻¹ * (toMatrix H)⁻¹, ((toMatrix H)⁻¹).toEuclideanLin v) := by
  ext x
  let M : Mat := toMatrix H
  let c : Eₙ := M⁻¹.toEuclideanLin v
  have hcenter :
      M.toEuclideanLin c = v := by
    -- Push the affine center `H⁻¹ v` back through `H`.
    simpa [M, c] using toEuclideanLin_inv_cancel (H := H) v
  have hshift :
      M.toEuclideanLin (x - c) = M.toEuclideanLin x - v := by
    -- The affine ellipsoid is centered at `c`, so translate the norm constraint by linearity.
    calc
      M.toEuclideanLin (x - c) = M.toEuclideanLin x - M.toEuclideanLin c := by
        simp [c]
      _ = M.toEuclideanLin x - v := by
        rw [hcenter]
  have hnorm_sq_iff (u : Eₙ) :
      ‖u‖ ^ (2 : ℕ) ≤ 1 ↔ ‖u‖ ≤ 1 := by
    constructor
    · intro hu
      nlinarith [norm_nonneg u]
    · intro hu
      nlinarith [norm_nonneg u]
  -- Rewrite the Chapter 3 quadratic predicate into the textbook norm inequality.
  change ‖M.toEuclideanLin x - v‖ ≤ 1 ↔ x ∈ E(M⁻¹ * M⁻¹, c)
  rw [mem_affineEllipsoid_iff]
  have hquad :
      inner ℝ ((((M⁻¹ * M⁻¹)⁻¹).toEuclideanLin (x - c))) (x - c) =
        ‖M.toEuclideanLin (x - c)‖ ^ (2 : ℕ) := by
    simpa [M, c] using inverse_square_quadratic_eq_norm_sq (H := H) (y := x - c)
  have hquad_sub :
      inner ℝ (((M⁻¹ * M⁻¹)⁻¹).toEuclideanLin x -
          ((M⁻¹ * M⁻¹)⁻¹).toEuclideanLin c) (x - c) =
        ‖M.toEuclideanLin (x - c)‖ ^ (2 : ℕ) := by
    calc
      inner ℝ (((M⁻¹ * M⁻¹)⁻¹).toEuclideanLin x -
          ((M⁻¹ * M⁻¹)⁻¹).toEuclideanLin c) (x - c) =
          inner ℝ ((((M⁻¹ * M⁻¹)⁻¹).toEuclideanLin (x - c))) (x - c) := by
            simp
      _ = ‖M.toEuclideanLin (x - c)‖ ^ (2 : ℕ) := hquad
  constructor
  · intro hx
    have htranslated : ‖M.toEuclideanLin (x - c)‖ ≤ 1 := by
      simpa [hshift] using hx
    have hsq : ‖M.toEuclideanLin (x - c)‖ ^ (2 : ℕ) ≤ 1 :=
      (hnorm_sq_iff _).2 htranslated
    rw [hquad]
    exact hsq
  · intro hx
    have hsq : ‖M.toEuclideanLin (x - c)‖ ^ (2 : ℕ) ≤ 1 := by
      simpa [hquad_sub] using hx
    have htranslated : ‖M.toEuclideanLin (x - c)‖ ≤ 1 :=
      (hnorm_sq_iff _).1 hsq
    simpa [hshift] using htranslated

-- Proof sketch: rewrite `W(H, v)` through `enclosingEllipsoid_eq_affineEllipsoid`, expand
-- `mem_affineEllipsoid_iff`, and simplify the resulting quadratic form.
/-- Membership in `W(H, v)` is exactly the constraint `‖H x - v‖ ≤ 1`. -/
@[simp] theorem mem_enclosingEllipsoid_iff
    {H : 𝕊^n₊₊} {v x : Eₙ} :
    x ∈ W(H, v) ↔ ‖(toMatrix H).toEuclideanLin x - v‖ ≤ 1 :=
  Iff.rfl

/-- Definition 5.4.5.1: the minimum-volume enclosing ellipsoid problem for a finite family of
points `a i` minimizes the scalar upper bound `τ` over strict-cone shapes `H : 𝕊ⁿ₊₊`, offsets
`v`, and `τ`, subject to `logDetBarrier n H ≤ τ` and the enclosing constraints
`a_i ∈ W(H, v)` for every index `i`. The raw `-log det H ≤ τ` and `‖H a_i - v‖ ≤ 1` formulas are
companion bridge views. -/
def minimumVolumeEnclosingEllipsoidProblem
    (a : ι → Eₙ) :
    SetConstrainedMinimizationProblem
      (𝕊^n₊₊ × Eₙ × ℝ) where
  feasibleSet := {Hvτ | logDetBarrier n Hvτ.1 ≤ Hvτ.2.2 ∧
    ∀ i, a i ∈ W(Hvτ.1, Hvτ.2.1)}
  objective := Prod.snd ∘ Prod.snd

-- Proof sketch: unfold `minimumVolumeEnclosingEllipsoidProblem`; the feasible set is
-- definitionally the conjunction of the owner determinant barrier bound and the source-facing
-- enclosing-ellipsoid constraints.
/-- A triple `(H, v, τ)` is feasible for the minimum-volume enclosing ellipsoid problem exactly
when `logDetBarrier n H ≤ τ` and every point `a i` belongs to the enclosing ellipsoid
`W(H, v)`. -/
@[simp] theorem mem_minimumVolumeEnclosingEllipsoidProblem_feasibleSet_iff
    (a : ι → Eₙ)
    (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ (minimumVolumeEnclosingEllipsoidProblem a).feasibleSet ↔
      logDetBarrier n H ≤ τ ∧
        ∀ i, a i ∈ W(H, v) :=
  Iff.rfl

-- Proof sketch: expand the owner determinant barrier with `logDetBarrier_apply` and rewrite the
-- source-facing ellipsoid constraints using `mem_enclosingEllipsoid_iff`.
/-- Expanding the owner feasible-set description rewrites MVEE feasibility back to the textbook
formula `-log det H ≤ τ` together with the norm constraints `‖H a_i - v‖ ≤ 1`. -/
theorem mem_minimumVolumeEnclosingEllipsoidProblem_feasibleSet_iff_formula
    (a : ι → Eₙ)
    (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (H, v, τ) ∈ (minimumVolumeEnclosingEllipsoidProblem a).feasibleSet ↔
      -Real.log (toMatrix H).det ≤ τ ∧
        ∀ i, ‖(toMatrix H).toEuclideanLin (a i) - v‖ ≤ 1 := by
  simp [mem_minimumVolumeEnclosingEllipsoidProblem_feasibleSet_iff, logDetBarrier_apply,
    mem_enclosingEllipsoid_iff]

-- Proof sketch: unfold `minimumVolumeEnclosingEllipsoidProblem`; the objective field is exactly
-- the third coordinate `τ`.
/-- Evaluating the objective of the minimum-volume enclosing ellipsoid problem returns the
auxiliary variable `τ`. -/
@[simp] theorem minimumVolumeEnclosingEllipsoidProblem_objective_apply
    (a : ι → Eₙ)
    (H : 𝕊^n₊₊) (v : Eₙ) (τ : ℝ) :
    (minimumVolumeEnclosingEllipsoidProblem a) (H, v, τ) = τ :=
  rfl

end
