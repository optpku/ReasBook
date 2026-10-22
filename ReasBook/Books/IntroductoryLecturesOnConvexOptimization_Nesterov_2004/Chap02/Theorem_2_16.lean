/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_5_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_6_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_19

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "p" => normSeminorm ℝ E

/- Primary domain: smooth-convex accelerated first-order methods on real Hilbert spaces.

Owner declarations sampled before refining this file:
* `gradientMethod` in `Algorithm_2_1`, the chapter's basic recursive owner for first-order
  trajectories;
* `constantStepSchemeIII` in `Algorithm_2_5`, the source-facing recursive owner pattern for a
  fixed-momentum accelerated gradient method;
* `ConstantStepSchemeIIRecurrence.objective_gap_le_quadratic_rate` in `Proposition_2_10`, the
  nearby quadratic-rate theorem for the chapter's type-II accelerated owner;
* `optimalMinimaxMethod` in `Algorithm_2_10`, which confirms the chapter style of keeping the
  recursive source-facing trajectory as the public owner and deriving the coordinate recurrences.

Best owner abstraction:
* `source-facing`: the recursive textbook trajectory with updates
  `x_{k+1} = y_k - (1 / L) ∇ f(y_k)` and
  `y_{k+1} = x_{k+1} + (k / (k + 3)) (x_{k+1} - x_k)`;
* `core/canonical`: the primitive smooth-convex objective data
  `ConvexOn ℝ Set.univ f`, `∀ x, HasGradientAt f (∇ f x) x`, and `LipschitzWith L (∇ f)`,
  together with the minimizer predicate `hxStar : IsMinOn f Set.univ xStar`;
* `bridge/view`: the finite-dimensional chapter notation `f ∈ 𝓕[L, p]¹¹` and the projection
  lemmas for the recursive owner trajectory below. The type-II owner ecosystem from
  `Algorithm_2_4` and `Proposition_2_10` is only a nearby comparison layer, since the fixed
  source coefficient `k / (k + 3)` is not the same scalar recurrence.

Primitive data in this file are therefore only the intrinsic smooth-convex owner hypotheses and
the initial point `x0`; the textbook sequences `x_k` and `y_k` are derived from the recursive
owner trajectory rather than exposed as arbitrary public sequence data. The chapter notation
`f ∈ 𝓕[L, p]¹¹` is retained only as a finite-dimensional bridge companion theorem. -/

section

variable {L : NNReal} {f : E → ℝ}

/-- The one-step state update of Theorem 2.16 on pairs `(x_k, y_k)`. -/
noncomputable def nesterovAcceleratedGradientStep
    (f : E → ℝ) (L : NNReal) (k : ℕ) :
    E × E → E × E :=
  fun state ↦
    let xk := state.1
    let yk := state.2
    let xNext := yk - (1 / (L : ℝ)) • ∇ f yk
    let yNext :=
      xNext + ((k : ℝ) / (k + 3 : ℝ)) • (xNext - xk)
    (xNext, yNext)

/-- The recursive textbook accelerated-gradient trajectory of Theorem 2.16, started from
`(x₀, y₀) = (x0, x0)` and updated by the exact gradient step
`x_{k+1} = y_k - (1 / L) ∇ f(y_k)` together with the source momentum coefficient
`k / (k + 3)`. -/
noncomputable def nesterovAcceleratedGradient
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E × E
  | 0 => (x0, x0)
  | k + 1 =>
      nesterovAcceleratedGradientStep f L k
        (nesterovAcceleratedGradient f L x0 k)

/-- The main iterate sequence `x_k` of the recursive textbook accelerated trajectory. -/
noncomputable def nesterovAcceleratedGradientX
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ (nesterovAcceleratedGradient f L x0 k).1

/-- The extrapolated sequence `y_k` of the recursive textbook accelerated trajectory. -/
noncomputable def nesterovAcceleratedGradientY
    (f : E → ℝ) (L : NNReal) (x0 : E) :
    ℕ → E :=
  fun k ↦ (nesterovAcceleratedGradient f L x0 k).2

section Trajectory

variable (f : E → ℝ) (L : NNReal) (x0 : E)

local notation "state" => nesterovAcceleratedGradient f L x0
local notation "xSeq" => nesterovAcceleratedGradientX f L x0
local notation "ySeq" => nesterovAcceleratedGradientY f L x0

@[simp] theorem nesterovAcceleratedGradient_zero :
    state 0 = (x0, x0) :=
  rfl

/-- The recursive state satisfies the one-step update law of Theorem 2.16. -/
@[simp] theorem nesterovAcceleratedGradient_succ
    (k : ℕ) :
    state (k + 1) =
      nesterovAcceleratedGradientStep f L k (state k) :=
  rfl

/-- The recursive trajectory starts from `x₀ = x0`. -/
@[simp] theorem nesterovAcceleratedGradientX_zero :
    xSeq 0 = x0 :=
  rfl

/-- The recursive trajectory starts from `y₀ = x0`. -/
@[simp] theorem nesterovAcceleratedGradientY_zero :
    ySeq 0 = x0 :=
  rfl

/-- The recursive iterates satisfy the textbook gradient-step update. -/
@[simp] theorem nesterovAcceleratedGradientX_succ
    (k : ℕ) :
    xSeq (k + 1) = ySeq k - (1 / (L : ℝ)) • ∇ f (ySeq k) :=
  rfl

/-- The recursive extrapolated points satisfy the textbook varying-momentum update. -/
@[simp] theorem nesterovAcceleratedGradientY_succ
    (k : ℕ) :
    ySeq (k + 1) =
      xSeq (k + 1) + ((k : ℝ) / (k + 3 : ℝ)) • (xSeq (k + 1) - xSeq k) :=
  rfl

end Trajectory

section QuadraticRateHelpers

variable (f : E → ℝ) (L : NNReal) (x0 : E)

local notation "xSeq" => nesterovAcceleratedGradientX f L x0
local notation "ySeq" => nesterovAcceleratedGradientY f L x0

/-- Helper for Theorem 2.16: the affine scalar parameter `t_k = (k + 2) / 2` used by the
estimate-sequence proof of the accelerated rate. -/
private def acceleratedGradientScalar
    (k : ℕ) : ℝ :=
  (((k + 2 : ℕ) : ℝ) / 2)

/-- Helper for Theorem 2.16: the affine auxiliary point
`z_k = t_k y_k - (t_k - 1) x_k` that linearizes the momentum recursion. -/
private def acceleratedGradientAuxPoint
    (k : ℕ) : E :=
  acceleratedGradientScalar k • ySeq k -
    (acceleratedGradientScalar k - 1) • xSeq k

local notation "t" => acceleratedGradientScalar
local notation "z" => acceleratedGradientAuxPoint f L x0

/-- Helper for Theorem 2.16: the affine scalar starts at `t₀ = 1`. -/
private lemma accelerated_gradient_scalar_zero :
    t 0 = 1 := by
  norm_num [acceleratedGradientScalar]

/-- Helper for Theorem 2.16: the affine scalar stays nonnegative. -/
private lemma accelerated_gradient_scalar_nonneg
    (k : ℕ) :
    0 ≤ t k := by
  change 0 ≤ (((k + 2 : ℕ) : ℝ) / 2)
  positivity

/-- Helper for Theorem 2.16: the affine scalar is strictly positive. -/
private lemma accelerated_gradient_scalar_pos
    (k : ℕ) :
    0 < t k := by
  change 0 < (((k + 2 : ℕ) : ℝ) / 2)
  positivity

/-- Helper for Theorem 2.16: the affine parameter satisfies `t_k - 1 = k / 2`. -/
private lemma accelerated_gradient_scalar_sub_one_eq
    (k : ℕ) :
    t k - 1 = (k : ℝ) / 2 := by
  change (((k + 2 : ℕ) : ℝ) / 2) - 1 = (k : ℝ) / 2
  norm_num [Nat.cast_add]
  ring

/-- Helper for Theorem 2.16: the affine coefficient on the predecessor gap is bounded by the
displayed potential weight `((k + 1)²) / 4`. -/
private lemma accelerated_gradient_scalar_sq_sub_le_prev_coeff
    (k : ℕ) :
    (t k) ^ (2 : ℕ) - t k ≤ (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4 := by
  change ((((k + 2 : ℕ) : ℝ) / 2) ^ (2 : ℕ) - (((k + 2 : ℕ) : ℝ) / 2)) ≤
      (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4
  have hEq :
      ((((k + 2 : ℕ) : ℝ) / 2) ^ (2 : ℕ) - (((k + 2 : ℕ) : ℝ) / 2)) =
        (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4 - 1 / 4 := by
    norm_num [Nat.cast_add]
    ring
  rw [hEq]
  norm_num

/-- Helper for Theorem 2.16: the affine scalar recovers the displayed momentum coefficient
`k / (k + 3) = (t_k - 1) / t_{k+1}`. -/
private lemma accelerated_gradient_momentum_coefficient_eq
    (k : ℕ) :
    ((k : ℝ) / (k + 3 : ℝ)) = (t k - 1) / t (k + 1) := by
  -- Expand `t_k = (k + 2) / 2` and simplify the resulting rational expression.
  have hk3_ne : ((k + 3 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [accelerated_gradient_scalar_sub_one_eq]
  change (k : ℝ) / (k + 3 : ℝ) = ((k : ℝ) / 2) / ((((k + 3 : ℕ) : ℝ) / 2))
  field_simp [hk3_ne]
  norm_num [Nat.cast_add]

/-- Helper for Theorem 2.16: multiplying the textbook momentum term by `t_{k+1}` cancels the
explicit denominator. -/
private lemma accelerated_gradient_scaled_momentum_coefficient_smul
    (k : ℕ)
    (v : E) :
    (t (k + 1)) • (((t k - 1) / t (k + 1)) • v) = (t k - 1) • v := by
  -- Cancel the scalar denominator before returning to the module expression.
  have ht_ne : t (k + 1) ≠ 0 := by
    exact (accelerated_gradient_scalar_pos (k + 1)).ne'
  calc
    (t (k + 1)) • (((t k - 1) / t (k + 1)) • v)
        = (t (k + 1) * ((t k - 1) / t (k + 1))) • v := by
            rw [smul_smul]
    _ = ((t k - 1) * (t (k + 1) * (t (k + 1))⁻¹)) • v := by
          rw [div_eq_mul_inv]
          ring
    _ = (t k - 1) • v := by
          rw [mul_inv_cancel₀ ht_ne, mul_one]

/-- Helper for Theorem 2.16: the auxiliary point starts from the initial iterate `x₀`. -/
private lemma accelerated_gradient_aux_point_zero :
    z 0 = x0 := by
  -- At time `0`, both owner trajectories equal `x₀` and `t₀ = 1`.
  simp [acceleratedGradientAuxPoint, acceleratedGradientScalar]

/-- Helper for Theorem 2.16: the auxiliary point relative to the minimizer splits into the base
displacement and the momentum correction. -/
private lemma accelerated_gradient_aux_point_affine_identity
    (xStar : E)
    (k : ℕ) :
    z k - xStar =
      (ySeq k - xStar) + (t k - 1) • (ySeq k - xSeq k) := by
  -- Separate the `1 • y_k` part from `t_k • y_k` and regroup the affine terms.
  have ht :
      (t k) • ySeq k = ySeq k + (t k - 1) • ySeq k := by
    calc
      (t k) • ySeq k = (1 + (t k - 1)) • ySeq k := by
        congr 1
        ring
      _ = ySeq k + (t k - 1) • ySeq k := by
        rw [add_smul, one_smul]
  rw [acceleratedGradientAuxPoint, ht, smul_sub, sub_eq_add_neg]
  abel

/-- Helper for Theorem 2.16: the transformed auxiliary point satisfies the exact gradient-step
update `z_{k+1} = z_k - (t_k / L) ∇ f(y_k)`. -/
private lemma accelerated_gradient_aux_point_step
    (k : ℕ) :
    z (k + 1) =
      z k - ((t k) / (L : ℝ)) • ∇ f (ySeq k) := by
  -- Rewrite `z_{k+1}` using the textbook momentum formula and substitute the exact gradient step.
  have hx_succ :
      (xSeq (k + 1) : E) = ySeq k - (1 / (L : ℝ)) • ∇ f (ySeq k) := by
    simpa using nesterovAcceleratedGradientX_succ (f := f) (L := L) (x0 := x0) k
  calc
    z (k + 1)
        = (t (k + 1)) •
            (xSeq (k + 1) +
              ((t k - 1) / t (k + 1)) • (xSeq (k + 1) - xSeq k)) -
            (t (k + 1) - 1) • xSeq (k + 1) := by
              rw [acceleratedGradientAuxPoint]
              rw [nesterovAcceleratedGradientY_succ (f := f) (L := L) (x0 := x0) k]
              rw [accelerated_gradient_momentum_coefficient_eq k]
    _ = (t (k + 1)) • xSeq (k + 1) +
          (t k - 1) • (xSeq (k + 1) - xSeq k) -
          (t (k + 1) - 1) • xSeq (k + 1) := by
            rw [smul_add]
            rw [accelerated_gradient_scaled_momentum_coefficient_smul k]
    _ = (t k) • xSeq (k + 1) - (t k - 1) • xSeq k := by
          rw [smul_sub]
          module
    _ = (t k) • (ySeq k - (1 / (L : ℝ)) • ∇ f (ySeq k)) -
          (t k - 1) • xSeq k := by
            change
              (t k) • (xSeq (k + 1) : E) - (t k - 1) • (xSeq k : E) =
                (t k) • (ySeq k - (1 / (L : ℝ)) • ∇ f (ySeq k)) -
                  (t k - 1) • (xSeq k : E)
            rw [hx_succ]
    _ = z k - ((t k) / (L : ℝ)) • ∇ f (ySeq k) := by
          rw [acceleratedGradientAuxPoint, smul_sub, smul_smul]
          module

/-- Helper for Theorem 2.16: the convexity inequalities at `y_k` combine into the weighted
bridge
`t_k (f(y_k) - f*) - (t_k - 1) (f(x_k) - f*) ≤ ⟪∇ f(y_k), z_k - x*⟫`. -/
private lemma accelerated_gradient_weighted_convexity_bridge
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (xStar : E)
    (k : ℕ) :
    (t k) * (f (ySeq k) - f xStar) -
        (t k - 1) * (f (xSeq k) - f xStar) ≤
      inner ℝ (∇ f (ySeq k)) (z k - xStar) := by
  let gk : E := ∇ f (ySeq k)
  have lower_tangent_plane_gap (y : E) :
      f (ySeq k) - f y ≤ inner ℝ gk (ySeq k - y) := by
    have hsupport :
        f y ≥ f (ySeq k) + inner ℝ gk (y - ySeq k) := by
      simpa [gk, gradientWithin, gradient, fderivWithin_univ] using
        hconvex.lower_tangent_plane
          (ySeq k) (by simp)
          ((hcontDiff.differentiable_one (ySeq k)).differentiableWithinAt)
          y (by simp)
    have hinner :
        inner ℝ gk (y - ySeq k) = -inner ℝ gk (ySeq k - y) := by
      calc
        inner ℝ gk (y - ySeq k) = inner ℝ gk (-(ySeq k - y)) := by
          congr 2
          abel
        _ = -inner ℝ gk (ySeq k - y) := by
          rw [inner_neg_right]
    rw [hinner] at hsupport
    linarith
  have hy_star :
      f (ySeq k) - f xStar ≤ inner ℝ gk (ySeq k - xStar) :=
    lower_tangent_plane_gap xStar
  have hy_x :
      f (ySeq k) - f (xSeq k) ≤ inner ℝ gk (ySeq k - xSeq k) :=
    lower_tangent_plane_gap (xSeq k)
  have hweight : 0 ≤ t k - 1 := by
    -- The explicit affine parameter satisfies `t_k - 1 = k / 2`.
    have hk_nonneg : (0 : ℝ) ≤ k := by
      exact_mod_cast Nat.zero_le k
    rw [accelerated_gradient_scalar_sub_one_eq]
    nlinarith
  have hy_x_scaled :
      (t k - 1) * (f (ySeq k) - f (xSeq k)) ≤
        inner ℝ gk ((t k - 1) • (ySeq k - xSeq k)) := by
    -- Scale the second tangent-plane inequality by the nonnegative weight `t_k - 1`.
    have hscaled := mul_le_mul_of_nonneg_left hy_x hweight
    simpa [gk, real_inner_smul_right] using hscaled
  have hsum :
      (f (ySeq k) - f xStar) + (t k - 1) * (f (ySeq k) - f (xSeq k)) ≤
        inner ℝ gk ((ySeq k - xStar) + (t k - 1) • (ySeq k - xSeq k)) := by
    -- Add the two convexity inequalities and regroup the right-hand side as a single inner
    -- product.
    have hadd := add_le_add hy_star hy_x_scaled
    simpa [gk, inner_add_right] using hadd
  have hlhs :
      (t k) * (f (ySeq k) - f xStar) -
          (t k - 1) * (f (xSeq k) - f xStar) =
        (f (ySeq k) - f xStar) +
          (t k - 1) * (f (ySeq k) - f (xSeq k)) := by
    ring
  have haux :
      z k - xStar =
        (ySeq k - xStar) + (t k - 1) • (ySeq k - xSeq k) :=
    accelerated_gradient_aux_point_affine_identity (f := f) (L := L) (x0 := x0) xStar k
  rw [hlhs]
  simpa [haux] using hsum

/-- Helper for Theorem 2.16: the initial objective gap is bounded by the quadratic Taylor model
at the minimizer. -/
private lemma accelerated_gradient_initial_gap_le_half_lipschitz_sqdist
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar) :
    f (xSeq 0) - f xStar ≤ ((L : ℝ) / 2) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ) := by
  have hgrad_zero : ∇ f xStar = 0 :=
    isMinOn_gradient_eq_zero hxStar
  -- Apply the smooth Taylor upper bound at the minimizer and remove the vanishing linear term.
  calc
    f (xSeq 0) - f xStar
        ≤ firstOrderTaylorModelAt f xStar (xSeq 0) - f xStar +
            ((L : ℝ) / 2) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ) := by
          have hupper :=
            taylor_upper_bound_of_contDiffOne_withLipschitzGradient
              hcontDiff hgrad_lipschitz xStar (xSeq 0)
          simpa [firstOrderTaylorModelAt_apply, hgrad_zero, add_comm, add_left_comm, add_assoc]
            using hupper
    _ = ((L : ℝ) / 2) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ) := by
          simp [hgrad_zero]

/-- Helper for Theorem 2.16: the raw one-step inequality obtained by combining descent,
convexity, and the exact `z`-update before the affine scalar inequality is applied. -/
private lemma accelerated_gradient_raw_potential_step
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hL : 0 < L)
    (xStar : E)
    (k : ℕ) :
    (t k) ^ (2 : ℕ) * (f (xSeq (k + 1)) - f xStar) +
        ((L : ℝ) / 2) * ‖z (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      ((t k) ^ (2 : ℕ) - t k) * (f (xSeq k) - f xStar) +
        ((L : ℝ) / 2) * ‖z k - xStar‖ ^ (2 : ℕ) := by
  let gk : E := ∇ f (ySeq k)
  have hdescent :
      f (xSeq (k + 1)) ≤
        f (ySeq k) - (1 / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
    -- Use the smooth descent estimate at the extrapolated point `y_k`.
    have hcoeff :
        (1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2) =
          1 / (2 * (L : ℝ)) := by
      have hL_ne : (L : ℝ) ≠ 0 := by
        exact_mod_cast hL.ne'
      field_simp [hL_ne]
      ring
    have hx_succ :
        (xSeq (k + 1) : E) = ySeq k - (1 / (L : ℝ)) • ∇ f (ySeq k) := by
      simpa using nesterovAcceleratedGradientX_succ (f := f) (L := L) (x0 := x0) k
    have hstep :
        f (ySeq k - (1 / (L : ℝ)) • ∇ f (ySeq k)) ≤
          f (ySeq k) -
            ((1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) * ‖gk‖ ^ (2 : ℕ) := by
      simpa [gk] using
        gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
          hcontDiff hgrad_lipschitz (ySeq k) (1 / (L : ℝ))
    have hstep' :
        f (xSeq (k + 1)) ≤
          f (ySeq k) -
            ((1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) * ‖gk‖ ^ (2 : ℕ) := by
      simpa [hx_succ] using hstep
    calc
      f (xSeq (k + 1)) ≤
          f (ySeq k) -
            ((1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) * ‖gk‖ ^ (2 : ℕ) := hstep'
      _ = f (ySeq k) - (1 / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
          rw [hcoeff]
  have hdescent_scaled :
      (t k) ^ (2 : ℕ) * (f (xSeq (k + 1)) - f xStar) ≤
        (t k) ^ (2 : ℕ) * (f (ySeq k) - f xStar) -
          ((t k) ^ (2 : ℕ) / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
    -- Multiply the one-step descent estimate by `t_k²`.
    have ht_sq_nonneg : 0 ≤ (t k) ^ (2 : ℕ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hdescent ht_sq_nonneg
    ring_nf at hscaled ⊢
    linarith
  have ht_nonneg : 0 ≤ t k :=
    accelerated_gradient_scalar_nonneg k
  have hbridge_scaled :
      (t k) ^ (2 : ℕ) * (f (ySeq k) - f xStar) -
          (t k) * (t k - 1) * (f (xSeq k) - f xStar) ≤
        (t k) * inner ℝ gk (z k - xStar) := by
    -- Multiply the weighted convexity bridge by the nonnegative factor `t_k`.
    have hbridge :
        (t k) * (f (ySeq k) - f xStar) -
            (t k - 1) * (f (xSeq k) - f xStar) ≤
          inner ℝ (∇ f (ySeq k)) (z k - xStar) :=
      accelerated_gradient_weighted_convexity_bridge
        (f := f) (L := L) (x0 := x0) hconvex hcontDiff xStar k
    have hscaled := mul_le_mul_of_nonneg_left hbridge ht_nonneg
    nlinarith
  have hquad :
      ((L : ℝ) / 2) * ‖z (k + 1) - xStar‖ ^ (2 : ℕ) =
        ((L : ℝ) / 2) * ‖z k - xStar‖ ^ (2 : ℕ) -
          (t k) * inner ℝ gk (z k - xStar) +
          ((t k) ^ (2 : ℕ) / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
    -- Expand the norm square after rewriting `z_{k+1}` as one gradient step from `z_k`.
    have hz :
        z (k + 1) - xStar =
          (z k - xStar) - ((t k) / (L : ℝ)) • gk := by
      calc
        z (k + 1) - xStar = (z k - ((t k) / (L : ℝ)) • gk) - xStar := by
          rw [accelerated_gradient_aux_point_step (f := f) (L := L) (x0 := x0) k]
        _ = (z k - xStar) - ((t k) / (L : ℝ)) • gk := by
          abel
    have hL_ne : (L : ℝ) ≠ 0 := by
      exact_mod_cast hL.ne'
    rw [hz, norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [real_inner_comm (z k - xStar) gk]
    field_simp [hL_ne]
  -- Add the scaled descent inequality to the norm-square identity and cancel the bridge term.
  nlinarith [hdescent_scaled, hbridge_scaled, hquad]

/-- Helper for Theorem 2.16: the affine Lyapunov potential
`Φ_k = ((k + 1)^2 / 4) (f(x_k) - f*) + (L / 2) ‖z_k - x*‖²`. -/
private def acceleratedGradientPotential
    (xStar : E)
    (k : ℕ) : ℝ :=
  ((((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4) * (f (xSeq k) - f xStar) +
    ((L : ℝ) / 2) * ‖z k - xStar‖ ^ (2 : ℕ)

local notation "Φ" => acceleratedGradientPotential f L x0

/-- Helper for Theorem 2.16: the affine Lyapunov potential decreases at every step. -/
private lemma accelerated_gradient_affine_potential_drop
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hL : 0 < L)
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    Φ xStar (k + 1) ≤ Φ xStar k := by
  have hraw :=
    accelerated_gradient_raw_potential_step
      (f := f) (L := L) (x0 := x0) hconvex hcontDiff hgrad_lipschitz hL xStar k
  have hgap_nonneg : 0 ≤ f (xSeq k) - f xStar := by
    exact sub_nonneg.mpr ((isMinOn_iff.mp hxStar) (xSeq k) (by simp))
  have hcoeff :
      (t k) ^ (2 : ℕ) - t k ≤ (((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4 :=
    accelerated_gradient_scalar_sq_sub_le_prev_coeff k
  have ht_sq :
      (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) / 4 = (t k) ^ (2 : ℕ) := by
    change (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) / 4 = ((((k + 2 : ℕ) : ℝ) / 2) ^ (2 : ℕ))
    ring
  have hstep :
      ((((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) / 4) * (f (xSeq (k + 1)) - f xStar) +
          ((L : ℝ) / 2) * ‖z (k + 1) - xStar‖ ^ (2 : ℕ) ≤
        ((((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4) * (f (xSeq k) - f xStar) +
          ((L : ℝ) / 2) * ‖z k - xStar‖ ^ (2 : ℕ) := by
    have hraw' :
        ((((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) / 4) * (f (xSeq (k + 1)) - f xStar) +
            ((L : ℝ) / 2) * ‖z (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          ((t k) ^ (2 : ℕ) - t k) * (f (xSeq k) - f xStar) +
            ((L : ℝ) / 2) * ‖z k - xStar‖ ^ (2 : ℕ) := by
      simpa only [ht_sq] using hraw
    have hright :
        ((t k) ^ (2 : ℕ) - t k) * (f (xSeq k) - f xStar) +
            ((L : ℝ) / 2) * ‖z k - xStar‖ ^ (2 : ℕ) ≤
          ((((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4) * (f (xSeq k) - f xStar) +
            ((L : ℝ) / 2) * ‖z k - xStar‖ ^ (2 : ℕ) := by
      have hmul := mul_le_mul_of_nonneg_right hcoeff hgap_nonneg
      linarith
    exact hraw'.trans hright
  simpa only [acceleratedGradientPotential] using hstep

/-- Helper for Theorem 2.16: the affine Lyapunov quantity is bounded by its initial value along
the whole trajectory. -/
private lemma accelerated_gradient_potential_le_initial
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hL : 0 < L)
    (xStar : E)
    (hxStar : IsMinOn f Set.univ xStar) :
    ∀ k : ℕ,
      Φ xStar k ≤ Φ xStar 0 := by
  intro k
  induction k with
  | zero =>
      -- The induction starts at the initial potential itself.
      exact le_rfl
  | succ k hk =>
      -- Combine the one-step decrease with the induction hypothesis.
      exact
        (accelerated_gradient_affine_potential_drop
          (f := f) (L := L) (x0 := x0) hconvex hcontDiff hgrad_lipschitz hL xStar hxStar k).trans hk

end QuadraticRateHelpers

/-- Theorem 2.16: if `f` is convex on `E`, admits the ambient gradient `∇ f` everywhere, that
gradient is `L`-Lipschitz in the ambient norm, `xStar` is a global minimizer of `f`, `L > 0`,
and `x_k` is the recursive textbook accelerated-gradient trajectory with
`x₀ = y₀ = x0`,
`x_{k+1} = y_k - (1 / L) ∇ f(y_k)`,
`y_{k+1} = x_{k+1} + (k / (k + 3)) • (x_{k+1} - x_k)`,
then the objective gap satisfies the quadratic rate
`f(x_k) - f(x*) ≤ 8 L ‖x₀ - x*‖² / (3 (k + 1)²)`.

This keeps the textbook accelerated scheme as a recursive source-facing owner on the intrinsic
real-Hilbert-space layer, rather than quantifying over arbitrary sequence data. The chapter
notation `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` is a finite-dimensional bridge to this intrinsic
statement, not the main owner surface. -/
-- Proof sketch: use the standard estimate-sequence / Lyapunov argument for the affine scalar
-- sequence `t_k = (k + 2) / 2`, together with the smooth-convex owner consequences extracted
-- from the convexity / gradient / Lipschitz hypotheses and the minimizer inequality from
-- `hxStar`.
theorem nesterovAcceleratedGradient_objective_gap_le_quadratic_rate
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgrad : ∀ x : E, HasGradientAt f (∇ f x) x)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (hL : 0 < L)
    (x0 : E)
    (k : ℕ) :
    f (nesterovAcceleratedGradientX f L x0 k) - f xStar ≤
      (8 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  let xSeq := nesterovAcceleratedGradientX f L x0
  let z := acceleratedGradientAuxPoint f L x0
  -- Route correction: keep the source-faithful affine estimate-sequence proof for the explicit
  -- coefficient `k / (k + 3)` instead of reducing to the distinct scheme-II scalar recurrence.
  have hfC1 : ContDiff ℝ 1 f := by
    rw [contDiff_one_iff_hasFDerivAt]
    refine ⟨fun x ↦ (InnerProductSpace.toDual ℝ E) (∇ f x), ?_, ?_⟩
    · exact (LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E)).comp
        hgrad_lipschitz.continuous
    · intro x
      simpa using (hgrad x).hasFDerivAt
  have hpot :
      acceleratedGradientPotential f L x0 xStar k ≤
        acceleratedGradientPotential f L x0 xStar 0 :=
    accelerated_gradient_potential_le_initial
      (f := f) (L := L) (x0 := x0) hconvex hfC1 hgrad_lipschitz hL xStar hxStar k
  have hdisplay :
      ((((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4) * (f (xSeq k) - f xStar) +
          ((L : ℝ) / 2) * ‖z k - xStar‖ ^ (2 : ℕ) ≤
        acceleratedGradientPotential f L x0 xStar 0 := by
    simpa only [acceleratedGradientPotential] using hpot
  have hquad_nonneg :
      0 ≤ ((L : ℝ) / 2) * ‖z k - xStar‖ ^ (2 : ℕ) := by
    positivity
  have hgap_coeff :
      ((((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4) * (f (xSeq k) - f xStar) ≤
        acceleratedGradientPotential f L x0 xStar 0 := by
    linarith
  have hinit :=
    accelerated_gradient_initial_gap_le_half_lipschitz_sqdist
      (f := f) (L := L) (x0 := x0) hfC1 hgrad_lipschitz xStar hxStar
  have hinit0 :
      f x0 - f xStar ≤ ((L : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    simpa [xSeq] using hinit
  have hpot0 :
      acceleratedGradientPotential f L x0 xStar 0 ≤
        (2 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / 3 := by
    -- Bound the initial potential using the initial smooth upper model at the minimizer.
    have hΦ0 :
        acceleratedGradientPotential f L x0 xStar 0 =
          (1 / 4 : ℝ) * (f x0 - f xStar) +
            ((L : ℝ) / 2) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
      simp [acceleratedGradientPotential, accelerated_gradient_aux_point_zero, xSeq]
    rw [hΦ0]
    nlinarith [hinit0, L.2, sq_nonneg ‖x0 - xStar‖]
  have hrate_target_mul :
      (f (xSeq k) - f xStar) * (3 * (k + 1 : ℝ) ^ (2 : ℕ)) ≤
        8 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ) := by
    have hgap_mul :
        (k + 1 : ℝ) ^ (2 : ℕ) * (f (xSeq k) - f xStar) ≤
          4 * acceleratedGradientPotential f L x0 xStar 0 := by
      have hmul :=
        mul_le_mul_of_nonneg_left hgap_coeff (by norm_num : (0 : ℝ) ≤ 4)
      have hsq :
          (k + 1 : ℝ) ^ (2 : ℕ) =
            4 * ((((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4) := by
        norm_num [pow_two, Nat.cast_add]
        ring
      calc
        (k + 1 : ℝ) ^ (2 : ℕ) * (f (xSeq k) - f xStar)
            = (4 * ((((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4)) * (f (xSeq k) - f xStar) := by
                rw [hsq]
        _ = 4 * ((((k + 1 : ℕ) : ℝ) ^ (2 : ℕ)) / 4 * (f (xSeq k) - f xStar)) := by
              ring
        _ ≤ 4 * acceleratedGradientPotential f L x0 xStar 0 := hmul
    have hpot0_mul :
        4 * acceleratedGradientPotential f L x0 xStar 0 ≤
          (8 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / 3 := by
      nlinarith [hpot0]
    have hgap_mul' :
        (k + 1 : ℝ) ^ (2 : ℕ) * (f (xSeq k) - f xStar) ≤
          (8 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) / 3 := by
      exact hgap_mul.trans hpot0_mul
    nlinarith [hgap_mul']
  have hden_pos : 0 < 3 * (k + 1 : ℝ) ^ (2 : ℕ) := by
    positivity
  refine (le_div_iff₀ hden_pos).2 ?_
  simpa [xSeq, mul_assoc, mul_left_comm, mul_comm] using hrate_target_mul

/-- Finite-dimensional bridge form of Theorem 2.16 using the chapter notation
`f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`. -/
theorem nesterovAcceleratedGradient_objective_gap_le_quadratic_rate_of_mem_F11
    [FiniteDimensional ℝ E]
    (hf : f ∈ 𝓕[L, p]¹¹)
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar)
    (hL : 0 < L)
    (x0 : E)
    (k : ℕ) :
    f (nesterovAcceleratedGradientX f L x0 k) - f xStar ≤
      (8 * (L : ℝ) * ‖x0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  simpa using
    nesterovAcceleratedGradient_objective_gap_le_quadratic_rate
      hf.convexOn hf.hasGradientAt hf.gradient_lipschitz
      xStar hxStar hL x0 k

end
