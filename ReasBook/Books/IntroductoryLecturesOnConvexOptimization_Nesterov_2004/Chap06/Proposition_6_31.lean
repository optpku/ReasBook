/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConstrainedArgmin

/- Proposition 6.31 lies in the Euclidean linear-algebra / unconstrained argmin domain.

Sampled owner-style declarations:
* `constrainedArgmin` with notation `argmin[Q]` in `Chap01/Definition_1_3_3`, the project owner
  for global minimizers on a set;
* `IsMinOn`, the canonical minimizer predicate underlying `argmin[Q]`;
* `Matrix.toEuclideanLin`, the canonical linear-map owner attached to a real matrix acting on
  Euclidean spaces;
* `Matrix.toEuclideanLin_conjTranspose_eq_adjoint`, the mathlib bridge identifying transpose with
  the adjoint on Euclidean spaces.

Best owner abstraction:
* source-facing: the affine-quadratic minimand
  `x ↦ ⟪A x, uHat⟫ + (1 / 2) ‖x‖²` on `ℝⁿ`;
* core/canonical: `Matrix.toEuclideanLin A` together with the project argmin owner
  `argmin[Set.univ]`;
* bridge/view: the Euclidean transpose formula `-Aᵀ uHat` for a chosen minimizer.

Primitive data:
* the matrix `A : ℝ^{m × n}`;
* the dual vector `uHat : ℝ^m`.

Derived API:
* the minimand `euclideanLinearQuadraticMinimand A uHat`;
* the pointwise formula for that minimand;
* the canonical argmin identity `x0 = -Aᵀ uHat` for any chosen minimizer;
* the resulting uniqueness of global minimizers.

No parallel wrapper around matrices, transpose maps, or argmin witnesses is introduced here; the
file stays on the canonical matrix and argmin owners already present in mathlib and the project.
-/

variable {m n : ℕ}

local notation "E₁" => EuclideanSpace ℝ (Fin n)
local notation "E₂" => EuclideanSpace ℝ (Fin m)

/-- The affine-quadratic minimand `x ↦ ⟪A x, uHat⟫ + (1 / 2) ‖x‖²` from Proposition 6.31. -/
def euclideanLinearQuadraticMinimand
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) : E₁ → ℝ :=
  fun x ↦ inner ℝ (A.toEuclideanLin x) uHat + (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ)

-- Proof sketch: unfold `euclideanLinearQuadraticMinimand`.
/-- Evaluating `euclideanLinearQuadraticMinimand` recovers the defining expression
`⟪A x, uHat⟫ + (1 / 2) ‖x‖²`. -/
@[simp] theorem euclideanLinearQuadraticMinimand_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) (x : E₁) :
    euclideanLinearQuadraticMinimand A uHat x =
      inner ℝ (A.toEuclideanLin x) uHat + (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
  -- This is exactly the defining formula of the minimand.
  rfl

/-- Helper for Proposition 6.31: completing the square centers the affine-quadratic minimand at
`-(Aᵀ uHat)`. -/
theorem euclideanLinearQuadraticMinimand_complete_square
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) (x : E₁) :
    let xStar : E₁ := -(A.transpose.toEuclideanLin uHat)
    euclideanLinearQuadraticMinimand A uHat x =
      euclideanLinearQuadraticMinimand A uHat xStar + (1 / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
  let v : E₁ := A.transpose.toEuclideanLin uHat
  let xStar : E₁ := -v
  have hAdj : inner ℝ (A.toEuclideanLin x) uHat = inner ℝ x v := by
    -- Rewrite the affine term through the Euclidean adjoint `Aᵀ`.
    rw [← A.toEuclideanLin.adjoint_inner_right]
    simpa [v] using congrArg
      (fun T : E₂ →ₗ[ℝ] E₁ ↦ inner ℝ x (T uHat))
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
  calc
    euclideanLinearQuadraticMinimand A uHat x
        = inner ℝ x v + (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
            rw [euclideanLinearQuadraticMinimand_apply, hAdj]
    _ = euclideanLinearQuadraticMinimand A uHat xStar + (1 / 2 : ℝ) * ‖x - xStar‖ ^ (2 : ℕ) := by
          have hAdjStar : inner ℝ (A.toEuclideanLin xStar) uHat = inner ℝ xStar v := by
            -- The same adjoint rewrite identifies the objective value at the center.
            rw [← A.toEuclideanLin.adjoint_inner_right]
            simpa [v, xStar] using congrArg
              (fun T : E₂ →ₗ[ℝ] E₁ ↦ inner ℝ xStar (T uHat))
              (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
          have hnorm_add :
              ‖x + A.transpose.toEuclideanLin uHat‖ ^ (2 : ℕ) =
                inner ℝ x x + inner ℝ x (A.transpose.toEuclideanLin uHat) +
                  inner ℝ (A.transpose.toEuclideanLin uHat) x +
                  inner ℝ (A.transpose.toEuclideanLin uHat)
                    (A.transpose.toEuclideanLin uHat) := by
            -- This is the quadratic expansion of the centered norm term.
            calc
              ‖x + A.transpose.toEuclideanLin uHat‖ ^ (2 : ℕ)
                  = inner ℝ (x + A.transpose.toEuclideanLin uHat)
                      (x + A.transpose.toEuclideanLin uHat) := by
                        symm
                        exact real_inner_self_eq_norm_sq (x + A.transpose.toEuclideanLin uHat)
              _ = inner ℝ x x + inner ℝ x (A.transpose.toEuclideanLin uHat) +
                    inner ℝ (A.transpose.toEuclideanLin uHat) x +
                    inner ℝ (A.transpose.toEuclideanLin uHat)
                      (A.transpose.toEuclideanLin uHat) := by
                        rw [inner_add_left, inner_add_right, inner_add_right]
                        ring_nf
          rw [euclideanLinearQuadraticMinimand_apply, hAdjStar]
          -- Expand the centered square and normalize both sides to the same scalar polynomial.
          simp only [xStar, v, sub_eq_add_neg, one_div, neg_neg, norm_neg, inner_neg_left]
          rw [hnorm_add, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
            real_inner_comm x (A.transpose.toEuclideanLin uHat)]
          ring_nf

-- Proof sketch: rewrite the affine term using the Euclidean adjoint of
-- `A.toEuclideanLin`, identify that adjoint with `(Aᵀ).toEuclideanLin`, and apply the
-- first-order condition for a global minimizer of the strongly convex function
-- `x ↦ ⟪A x, uHat⟫ + (1 / 2) ‖x‖²`.
/-- Proposition 6.31 [Chapter6_1.json:100]: if `x0(uHat)` is chosen in
`argmin_x {⟪A x, uHat⟫ + (1 / 2) ‖x‖²}`, then `x0(uHat) = -Aᵀ uHat`. -/
theorem euclideanLinearQuadraticMinimizer_eq_neg_transpose_apply
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) {x0 : E₁}
    (hx0 : x0 ∈ argmin[Set.univ] (euclideanLinearQuadraticMinimand A uHat)) :
    x0 = -(A.transpose.toEuclideanLin uHat) := by
  let xStar : E₁ := -(A.transpose.toEuclideanLin uHat)
  rcases mem_constrainedArgmin_iff.mp hx0 with ⟨_, hx0min⟩
  have hle :
      euclideanLinearQuadraticMinimand A uHat x0 ≤ euclideanLinearQuadraticMinimand A uHat xStar :=
    (isMinOn_univ_iff.mp hx0min) xStar
  have hcomplete := euclideanLinearQuadraticMinimand_complete_square A uHat x0
  have hgap_nonpos : (1 / 2 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤ 0 := by
    -- Evaluating minimality at the completed-square center isolates the quadratic gap.
    rw [hcomplete, add_le_iff_nonpos_right] at hle
    exact hle
  have hgap_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    -- The remaining gap is a nonnegative squared norm.
    positivity
  have hgap_eq_zero : (1 / 2 : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) = 0 :=
    le_antisymm hgap_nonpos hgap_nonneg
  have hnorm_sq_zero : ‖x0 - xStar‖ ^ (2 : ℕ) = 0 := by
    rcases mul_eq_zero.mp hgap_eq_zero with hhalf | hsq
    · norm_num at hhalf
    · exact hsq
  have hsub_eq_zero : x0 - xStar = 0 := by
    exact norm_eq_zero.mp ((sq_eq_zero_iff).mp hnorm_sq_zero)
  exact sub_eq_zero.mp hsub_eq_zero

-- Proof sketch: apply
-- `euclideanLinearQuadraticMinimizer_eq_neg_transpose_apply` to both minimizers and compare
-- their common value `-Aᵀ uHat`.
/-- Any two global minimizers of `euclideanLinearQuadraticMinimand A uHat` are equal. -/
theorem euclideanLinearQuadraticMinimizer_unique
    (A : Matrix (Fin m) (Fin n) ℝ) (uHat : E₂) {x y : E₁}
    (hx : x ∈ argmin[Set.univ] (euclideanLinearQuadraticMinimand A uHat))
    (hy : y ∈ argmin[Set.univ] (euclideanLinearQuadraticMinimand A uHat)) :
    x = y := by
  -- Both argmin witnesses are forced to be the same explicit center `-Aᵀ uHat`.
  rw [euclideanLinearQuadraticMinimizer_eq_neg_transpose_apply A uHat hx,
    euclideanLinearQuadraticMinimizer_eq_neg_transpose_apply A uHat hy]
