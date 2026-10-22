/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_4
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

/- Remark 5.9 is `source-facing`: the textbook fixes the concrete quadratic
`x ↦ -(1 / 2) * ‖x‖²` on `ℝ^n`. Domain sampling points to the existing owners already used in this
chapter: Chapter 4's `quadratic_affine_function` for concrete quadratics on `Fin n → ℝ`, Chapter
5's `is_l_smooth_on` for global smoothness, mathlib's `ConcaveOn` for concavity, and the ambient
gradient `∇`. The primitive data is only the quadratic itself, so the file keeps the source-facing
owner `negative_half_squared_norm` as a thin bridge to the Chapter 4 quadratic owner. The
remaining declarations are the source-facing derived views: gradient, least smoothness parameter,
concavity, tangent-plane inequality, and failure of `0`-smoothness. -/

/-- The quadratic `x ↦ -(1 / 2) * ‖x‖²` on `ℝ^n`, written as a thin source-facing alias of
Chapter 4's concrete quadratic-affine owner on `Fin n → ℝ`. -/
abbrev negative_half_squared_norm (n : ℕ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x ↦ quadratic_affine_function (-1) 0 0 x

/-- Evaluating `negative_half_squared_norm n` uses the Chapter 4 quadratic owner with matrix
`-1`, zero linear term, and zero constant term. -/
@[simp] theorem negative_half_squared_norm_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    negative_half_squared_norm n x = quadratic_affine_function (-1) 0 0 x :=
  rfl

section

variable (n : ℕ)

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Helper for Remark 5.9: the source-facing quadratic `negative_half_squared_norm n` is exactly
`x ↦ (-(1 / 2 : ℝ)) * ‖x‖ ^ 2`. -/
private theorem negativeHalfSquaredNorm_eq_neg_half_normSq (x : E) :
    negative_half_squared_norm n x = (-(1 / 2 : ℝ)) * ‖x‖ ^ 2 := by
  -- Expand the quadratic owner and identify the matrix action with negation.
  rw [negative_half_squared_norm_apply, quadratic_affine_function_apply, Matrix.neg_mulVec,
    Matrix.one_mulVec]
  -- Convert the coordinate dot product into the Euclidean squared norm.
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct]
  ring_nf

/-- Helper for Remark 5.9: the quadratic `negative_half_squared_norm n` has gradient witness
`-x` at every point `x`. -/
private theorem hasGradientAt_negativeHalfSquaredNorm (x : E) :
    HasGradientAt (negative_half_squared_norm n) (-x) x := by
  -- Differentiate the explicit scalar multiple of `‖x‖ ^ 2`.
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (-(1 / 2 : ℝ)) using 1
  · ext y
    rw [negativeHalfSquaredNorm_eq_neg_half_normSq]
    simp
  · ext y
    simp [InnerProductSpace.toDual_apply_apply]

-- Proof sketch: differentiate `x ↦ ‖x‖²` using `hasStrictFDerivAt_norm_sq`, scale by `-(1 / 2)`,
-- and identify the resulting Fréchet derivative with the inner product against `-x`; the canonical
-- gradient is then obtained from `HasGradientAt.gradient`.
/-- The gradient of `x ↦ -(1 / 2) * ‖x‖²` is the linear vector field `x ↦ -x`. -/
theorem gradient_negative_half_squared_norm (x : E) :
    ∇ (negative_half_squared_norm n) x = -x :=
  -- The canonical gradient is the vector extracted from the `HasGradientAt` witness.
  (hasGradientAt_negativeHalfSquaredNorm n x).gradient

/-- Helper for Remark 5.9: the quadratic `negative_half_squared_norm n` is globally `1`-smooth on
`Set.univ`. -/
private theorem negativeHalfSquaredNorm_oneSmooth :
    is_l_smooth_on (negative_half_squared_norm n) Set.univ 1 := by
  -- Rewrite smoothness in terms of differentiability and the Lipschitz gradient estimate.
  rw [is_l_smooth_on_iff_forall_norm_sub_le]
  refine ⟨?_, ?_⟩
  · intro x _
    exact (hasGradientAt_negativeHalfSquaredNorm n x).differentiableAt
  · intro x _ y _
    -- The gradient field is `x ↦ -x`, whose difference preserves the Euclidean norm.
    rw [gradient_negative_half_squared_norm, gradient_negative_half_squared_norm]
    have hnorm : ‖(-x) - (-y)‖ = ‖x - y‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_neg (x - y)
    rw [hnorm]
    simp

/-- Helper for Remark 5.9: on `ℝ^n` with `0 < n`, any global smoothness constant for
`negative_half_squared_norm n` is at least `1`. -/
private theorem one_le_of_negativeHalfSquaredNorm_smooth (hn : 0 < n) {L : NNReal}
    (hL : is_l_smooth_on (negative_half_squared_norm n) Set.univ L) :
    1 ≤ L := by
  -- Evaluate the gradient Lipschitz estimate at the points `1` and `0`.
  rw [is_l_smooth_on_iff_forall_norm_sub_le] at hL
  let i0 : Fin n := ⟨0, hn⟩
  let e : E := PiLp.single 2 i0 (1 : ℝ)
  have he_ne_zero : e ≠ 0 := by
    intro hzero
    have hcoord := congrArg (fun v : E ↦ v i0) hzero
    simp [e, i0] at hcoord
  have hnorm_pos : 0 < ‖e‖ := norm_pos_iff.mpr he_ne_zero
  have hineq := hL.2 e (by simp) 0 (by simp)
  rw [gradient_negative_half_squared_norm, gradient_negative_half_squared_norm] at hineq
  have hLreal : (1 : ℝ) ≤ (L : ℝ) := by
    have hnorm_le : ‖e‖ ≤ (L : ℝ) * ‖e‖ := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hineq
    nlinarith
  exact_mod_cast hLreal

-- Proof sketch: compute `∇ (negative_half_squared_norm n) x = -x`, so the gradient difference is
-- `-(x - y)` and has norm `‖x - y‖`. This gives global `1`-smoothness. When `0 < n`, choose
-- distinct `x,y`; if `is_l_smooth_on (negative_half_squared_norm n) Set.univ L`, evaluating the
-- gradient Lipschitz inequality on those points gives `1 ≤ L`, so `1` is the least smoothness
-- parameter.
/-- Remark 5.9 (1): on nontrivial Euclidean spaces `ℝ^n`, the quadratic
`x ↦ -(1 / 2) * ‖x‖²` has least global smoothness parameter `1`; equivalently, it is `1`-smooth
and it is not `L`-smooth for any `L < 1`. -/
theorem negative_half_squared_norm_isLeast_smoothness_parameter (hn : 0 < n) :
    IsLeast {L : NNReal | is_l_smooth_on (negative_half_squared_norm n) Set.univ L} 1 := by
  -- Combine the explicit `1`-smooth witness with the lower bound on all admissible parameters.
  refine ⟨negativeHalfSquaredNorm_oneSmooth n, ?_⟩
  intro L hL
  exact one_le_of_negativeHalfSquaredNorm_smooth n hn hL

-- Proof sketch: `x ↦ ‖x‖²` is convex on `Set.univ`, and multiplying by the nonpositive scalar
-- `-(1 / 2)` turns that convex quadratic into a concave function on the whole space.
/-- Remark 5.9 (2): the quadratic `x ↦ -(1 / 2) * ‖x‖²` is concave on `ℝ^n`. -/
theorem negative_half_squared_norm_concaveOn :
    ConcaveOn ℝ Set.univ (negative_half_squared_norm n) := by
  -- Start from convexity of the squared norm on the whole Euclidean space.
  have hnormSq : ConvexOn ℝ Set.univ (fun z : E ↦ ‖z‖ ^ 2) :=
    (convexOn_univ_norm : ConvexOn ℝ Set.univ (fun z : E ↦ ‖z‖)).pow
      (fun _ _ ↦ norm_nonneg _) 2
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- The negative half of a convex quadratic is concave because the scalar is nonpositive.
  have hconv : ‖a • x + b • y‖ ^ 2 ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 := by
    simpa [smul_eq_mul] using hnormSq.2 (by simp) (by simp) ha hb hab
  rw [negativeHalfSquaredNorm_eq_neg_half_normSq, negativeHalfSquaredNorm_eq_neg_half_normSq,
    negativeHalfSquaredNorm_eq_neg_half_normSq]
  simp [smul_eq_mul]
  nlinarith

/-- Helper for Remark 5.9: the quadratic `negative_half_squared_norm n` differs from its tangent
plane at `x` by the exact remainder `-(1 / 2 : ℝ) * ‖y - x‖ ^ 2`. -/
private theorem negativeHalfSquaredNorm_tangentPlane_remainder (x y : E) :
    negative_half_squared_norm n y =
      negative_half_squared_norm n x + inner ℝ (-x) (y - x) - (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by
  -- Rewrite the quadratic in norm form and expand the remainder with `‖y - x‖ ^ 2`.
  rw [negativeHalfSquaredNorm_eq_neg_half_normSq, negativeHalfSquaredNorm_eq_neg_half_normSq]
  have hsq : ‖y - x‖ ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := by
    calc
      ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ y x + ‖x‖ ^ 2 := norm_sub_sq_real y x
      _ = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := by
        rw [real_inner_comm]
        ring_nf
  rw [hsq]
  simp [inner_sub_right, inner_neg_left, inner_self_eq_norm_sq_to_K]
  ring_nf

-- Proof sketch: apply the first-order support inequality for concave differentiable functions to
-- `negative_half_squared_norm n`, using the concavity statement above and the gradient formula
-- `∇ (negative_half_squared_norm n) x = -x`. This is exactly Theorem 5.8(ii) specialized to
-- `L = 0`.
/-- Remark 5.9 (3): for all `x, y ∈ ℝ^n`, the quadratic `x ↦ -(1 / 2) * ‖x‖²` satisfies the
first-order upper bound
`negative_half_squared_norm n y ≤
negative_half_squared_norm n x + ⟪∇(negative_half_squared_norm n) x, y - x⟫`,
so the quadratic upper-model clause from Theorem 5.8 holds with `L = 0`. -/
theorem negative_half_squared_norm_le_tangent_plane (x y : E) :
    negative_half_squared_norm n y ≤
      negative_half_squared_norm n x + inner ℝ (∇ (negative_half_squared_norm n) x) (y - x) :=
    by
  -- Replace the function value by the exact quadratic remainder identity.
  rw [gradient_negative_half_squared_norm]
  have hremainder := negativeHalfSquaredNorm_tangentPlane_remainder n x y
  have hnonneg : 0 ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ 2 := by positivity
  nlinarith [hremainder, hnonneg]

-- Proof sketch: if `negative_half_squared_norm n` were `0`-smooth, its gradient field would be
-- `0`-Lipschitz and hence constant on `Set.univ`. When `0 < n`,
-- `gradient_negative_half_squared_norm` identifies the gradient with `x ↦ -x`, whose values differ
-- at distinct points.
/-- Remark 5.9 (4): on nontrivial Euclidean spaces `ℝ^n`, although the first-order upper-model
inequality holds with `L = 0`, the quadratic `x ↦ -(1 / 2) * ‖x‖²` is not globally `0`-smooth. -/
theorem negative_half_squared_norm_not_zero_smooth (hn : 0 < n) :
    ¬ is_l_smooth_on (negative_half_squared_norm n) Set.univ 0 := by
  -- The least smoothness parameter theorem rules out `0` as an admissible constant.
  intro hzero
  rcases negative_half_squared_norm_isLeast_smoothness_parameter n hn with ⟨_, hmin⟩
  have hone_le_zero : (1 : NNReal) ≤ (0 : NNReal) := hmin hzero
  exact not_le_of_gt zero_lt_one hone_le_zero

end
