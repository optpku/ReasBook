/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped RealInnerProductSpace

noncomputable section

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "E" => EuclideanSpace ℝ ι

/- Proposition 6.2.3 is `source-facing` in the Euclidean proximal domain.

- `core/canonical`: the Chapter 6 proximal owner `prox[...]`;
- `bridge/view`: the Chapter 5 coordinate owner `quadratic_affine_function_on_lp (2 : ENNReal)`
  and mathlib's Euclidean matrix action `Matrix.toEuclideanLin`;
- primitive data: the matrix `A`, the Euclidean linear coefficient `b`, and the base point `x`.

The coordinate model from Chapter 5 remains the canonical construction of the quadratic-affine
function, but the public proposition should expose only the intrinsic Euclidean surface.
The bridge lemma `quadratic_affine_function_on_lp_two_apply_eq` keeps the coordinate realization
internal by rewriting
`quadratic_affine_function_on_lp (2 : ENNReal) A b.ofLp 0` as the Euclidean quadratic
`y ↦ (1 / 2) ⟪A.toEuclideanLin y, y⟫ + ⟪b, y⟫`. -/

/-- Helper for Proposition 6.2.3: the candidate proximal point obtained by solving the shifted
normal equation `(A + I) u = x - b`. -/
noncomputable def quadratic_prox_center (A : Matrix ι ι ℝ) (b x : E) : E :=
  ((A + 1)⁻¹).toEuclideanLin (x - b)

/-- Helper for Proposition 6.2.3: the real-valued proximal objective of the quadratic
`y ↦ (1 / 2) ⟪A y, y⟫ + ⟪b, y⟫` at the base point `x`. -/
def quadratic_penalized_value (A : Matrix ι ι ℝ) (b x y : E) : ℝ :=
  (1 / 2 : ℝ) * ⟪A.toEuclideanLin y, y⟫ + ⟪b, y⟫ + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ)

/-- Helper for Proposition 6.2.3: the nonnegative quadratic error term produced by recentering the
proximal objective at the canonical point `quadratic_prox_center A b x`. -/
def quadratic_prox_error (A : Matrix ι ι ℝ) (z : E) : ℝ :=
  (1 / 2 : ℝ) * ⟪A.toEuclideanLin z, z⟫ + (1 / 2 : ℝ) * ‖z‖ ^ (2 : ℕ)

-- The inverse formula is the textbook normal equation `(A + I) u = x - b`, transported through
-- `Matrix.toEuclideanLin`.
/-- Helper for Proposition 6.2.3: the shifted inverse point solves the normal equation
`(A + I) u = x - b`. -/
lemma shifted_inverse_solves_quadratic_normal_equation
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (b x : E) :
    (A + 1).toEuclideanLin (quadratic_prox_center A b x) = x - b := by
  -- Positive semidefiniteness of `A` makes `A + I` positive definite, hence invertible.
  have hpd : (A + 1).PosDef := by
    simpa [add_comm] using
      (Matrix.PosDef.add_posSemidef (A := (1 : Matrix ι ι ℝ)) (B := A) Matrix.PosDef.one hA)
  letI := hpd.isUnit.invertible
  -- Push the Euclidean equality to coordinates, where it is the standard matrix identity
  -- `(A + I) (A + I)⁻¹ = I`.
  ext i
  have hEq :
      (((A + 1).toEuclideanLin (quadratic_prox_center A b x)).ofLp) i = ((x - b).ofLp) i := by
    rw [quadratic_prox_center, Matrix.ofLp_toLpLin 2 2 (A + 1),
      Matrix.ofLp_toLpLin 2 2 ((A + 1)⁻¹), ← Matrix.toLin'_mul_apply,
      Matrix.mul_inv_of_invertible, Matrix.toLin'_one]
    rfl
  simpa using hEq

-- Completing the square around the normal-equation solution rewrites the proximal objective as
-- its center value plus a purely quadratic error term.
/-- Helper for Proposition 6.2.3: recentering the quadratic proximal objective at
`quadratic_prox_center A b x` produces the center value plus the quadratic error
`quadratic_prox_error A z`. -/
lemma quadratic_penalized_value_center_add_error
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (b x z : E) :
    quadratic_penalized_value A b x (quadratic_prox_center A b x + z) =
      quadratic_penalized_value A b x (quadratic_prox_center A b x) + quadratic_prox_error A z := by
  let u : E := quadratic_prox_center A b x
  -- Rewrite the linear term using the normal equation satisfied by `u`.
  have hu : (A + 1).toEuclideanLin u = x - b := by
    simpa [u] using shifted_inverse_solves_quadratic_normal_equation A hA b x
  have hu' : A.toEuclideanLin u + u = x - b := by
    simpa [Matrix.toEuclideanLin.map_add, u] using hu
  -- Symmetry of `A` identifies the two mixed quadratic terms.
  have hsymmetric : (A.toEuclideanLin).IsSymmetric :=
    (Matrix.isSymmetric_toEuclideanLin_iff).2 hA.1
  have hzsymm : ⟪A.toEuclideanLin z, u⟫ = ⟪A.toEuclideanLin u, z⟫ := by
    calc
      ⟪A.toEuclideanLin z, u⟫ = ⟪z, A.toEuclideanLin u⟫ := hsymmetric z u
      _ = ⟪A.toEuclideanLin u, z⟫ := by simp [real_inner_comm]
  have hu_inner : ⟪A.toEuclideanLin u, z⟫ + ⟪u, z⟫ = ⟪x - b, z⟫ := by
    simpa [inner_add_left] using congrArg (fun w : E => ⟪w, z⟫) hu'
  have hu_inner' : ⟪A.toEuclideanLin u, z⟫ + ⟪u, z⟫ = ⟪x, z⟫ - ⟪b, z⟫ := by
    simpa [inner_sub_left] using hu_inner
  have hsub : u + z - x = (u - x) + z := by
    abel_nf
  unfold quadratic_penalized_value quadratic_prox_error
  rw [LinearMap.map_add, inner_add_left, inner_add_right, inner_add_right, inner_add_right, hsub,
    norm_add_sq_real]
  have hcross :
      ⟪A.toEuclideanLin u, z⟫ + ⟪A.toEuclideanLin z, u⟫ + 2 * ⟪u - x, z⟫ + 2 * ⟪b, z⟫ = 0 := by
    -- After the symmetry rewrite, the mixed terms cancel exactly by the normal equation.
    rw [inner_sub_left]
    nlinarith [hu_inner', hzsymm]
  nlinarith [hcross]

-- Positive semidefiniteness of `A` makes the recentered error term nonnegative.
/-- Helper for Proposition 6.2.3: the quadratic error term from the completed-square identity is
always nonnegative. -/
lemma quadratic_prox_error_nonneg
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (z : E) :
    0 ≤ quadratic_prox_error A z := by
  have hpositive : (A.toEuclideanLin).IsPositive :=
    (Matrix.isPositive_toEuclideanLin_iff).2 hA
  unfold quadratic_prox_error
  -- Each summand is nonnegative: the first by positivity of `A`, the second by being a norm
  -- square.
  have hquad : 0 ≤ ⟪A.toEuclideanLin z, z⟫ := by
    simpa [real_inner_comm] using hpositive.inner_nonneg_right z
  have hnorm : 0 ≤ ‖z‖ ^ (2 : ℕ) := sq_nonneg ‖z‖
  nlinarith

-- Proof sketch: first pass from the Chapter 5 coordinate owner to the intrinsic Euclidean formula
-- using `quadratic_affine_function_on_lp_two_apply_eq`. Completing the square then centers the
-- proximal objective at `((A + 1)⁻¹).toEuclideanLin (x - b)`. Since `hA` is positive semidefinite,
-- `A + 1` is positive definite and therefore invertible, so this Euclidean point is well-defined
-- and yields the unique minimizer.
/-- Proposition 6.2.3: for the Euclidean quadratic
`y ↦ (1 / 2) ⟪A.toEuclideanLin y, y⟫ + ⟪b, y⟫` on `EuclideanSpace ℝ ι`, hence on `ℝ^n` when
`ι = Fin n`, the proximal mapping at `x` is the singleton obtained by applying the inverse
Euclidean linear map `((A + 1)⁻¹).toEuclideanLin` to `x - b`. -/
theorem prox_quadratic_affine_function_eq_singleton
    (A : Matrix ι ι ℝ) (hA : A.PosSemidef) (b x : E) :
    prox[fun y : E ↦ (((1 / 2 : ℝ) * ⟪A.toEuclideanLin y, y⟫ + ⟪b, y⟫ : ℝ) : EReal)] x =
      {((A + 1)⁻¹).toEuclideanLin (x - b)} := by
  let f : E → EReal :=
    fun y : E ↦ (((1 / 2 : ℝ) * ⟪A.toEuclideanLin y, y⟫ + ⟪b, y⟫ : ℝ) : EReal)
  let u : E := quadratic_prox_center A b x
  have hu_min : u ∈ prox[f] x := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff]
    intro y
    change ((quadratic_penalized_value A b x u : ℝ) : EReal) ≤
      ((quadratic_penalized_value A b x y : ℝ) : EReal)
    -- Recenter the objective at `u`; the remaining error term is nonnegative.
    have hz : y = u + (y - u) := by
      abel_nf
    rw [hz, quadratic_penalized_value_center_add_error A hA b x (y - u)]
    have hnonneg : 0 ≤ quadratic_prox_error A (y - u) :=
      quadratic_prox_error_nonneg A hA (y - u)
    exact_mod_cast le_add_of_nonneg_right hnonneg
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · simpa [f, u, quadratic_prox_center] using hu_min
  · intro y hy
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hy
    -- Compare the minimizing inequalities in both directions to force the quadratic error to
    -- vanish.
    have hyuE := hy u
    change ((quadratic_penalized_value A b x y : ℝ) : EReal) ≤
      ((quadratic_penalized_value A b x u : ℝ) : EReal) at hyuE
    have hyu : quadratic_penalized_value A b x y ≤ quadratic_penalized_value A b x u := by
      exact_mod_cast hyuE
    have huy : quadratic_penalized_value A b x u ≤ quadratic_penalized_value A b x y := by
      have hz : y = u + (y - u) := by
        abel_nf
      rw [hz, quadratic_penalized_value_center_add_error A hA b x (y - u)]
      have hnonneg : 0 ≤ quadratic_prox_error A (y - u) :=
        quadratic_prox_error_nonneg A hA (y - u)
      exact le_add_of_nonneg_right hnonneg
    have hEq : quadratic_penalized_value A b x y = quadratic_penalized_value A b x u :=
      le_antisymm hyu huy
    have hz : y = u + (y - u) := by
      abel_nf
    rw [hz, quadratic_penalized_value_center_add_error A hA b x (y - u)] at hEq
    have herror_zero : quadratic_prox_error A (y - u) = 0 := by
      linarith
    have hnorm_sq : ‖y - u‖ ^ (2 : ℕ) = 0 := by
      have hnonneg : 0 ≤ ⟪A.toEuclideanLin (y - u), y - u⟫ := by
        have hpositive : (A.toEuclideanLin).IsPositive :=
          (Matrix.isPositive_toEuclideanLin_iff).2 hA
        simpa [real_inner_comm] using hpositive.inner_nonneg_right (y - u)
      unfold quadratic_prox_error at herror_zero
      nlinarith
    have hzero : y - u = 0 := by
      exact norm_eq_zero.mp (eq_zero_of_pow_eq_zero hnorm_sq)
    have hy_eq_u : y = u := sub_eq_zero.mp hzero
    simpa [u, quadratic_prox_center] using hy_eq_u

end
