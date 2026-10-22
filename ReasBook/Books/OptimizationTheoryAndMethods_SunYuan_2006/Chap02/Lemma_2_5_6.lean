/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

open scoped Gradient

section Lemma256

variable {Point : Type*} [NormedAddCommGroup Point] [InnerProductSpace ℝ Point]
  [CompleteSpace Point]

-- Domain sampling: this is a source-facing single-step Wolfe-Powell decrease estimate in smooth
-- line search. The owner abstractions in this domain are the Chapter 2 ray profile
-- `lineSearchObjective`, the Chapter 2 one-dimensional Wolfe owner `WolfePowellCondition`,
-- mathlib's gradient predicate `HasGradientAt`, and mathlib's setwise Lipschitz owner
-- `LipschitzOnWith`. Primitive data for the present statement are the endpoint memberships in `D`,
-- the genuine-gradient witness for `∇ f` on `D`, the Lipschitz bound on `∇ f`, and the
-- descent/Wolfe inequalities; the derivative profile
-- `α ↦ inner ℝ (∇ f (xk + α • dk)) dk` is the bridge layer from the ambient function `f` to the
-- one-dimensional Wolfe condition.

/-- Helper for Chapter02 Lemma 2.5.6: the Lipschitz control of `∇ f` along the accepted trial
segment bounds the directional derivative change by `M * αk * ‖dk‖^2`. -/
lemma directionalGradientChange_le_stepNormSq
    (D : Set Point) (f : Point → ℝ)
    (xk dk : Point) (αk M : ℝ)
    (hxk : xk ∈ D)
    (hxαk : xk + αk • dk ∈ D)
    (hM : 0 < M)
    (h_gradLipschitz : LipschitzOnWith ⟨M, le_of_lt hM⟩ (∇ f) D)
    (hαk : 0 < αk) :
    inner ℝ (∇ f (xk + αk • dk) - ∇ f xk) dk ≤ M * αk * ‖dk‖ ^ (2 : ℕ) := by
  -- First convert the setwise Lipschitz bound into a norm estimate on the gradient change.
  have h_lipschitz :
      ‖∇ f (xk + αk • dk) - ∇ f xk‖ ≤ M * (αk * ‖dk‖) := by
    let K : NNReal := ⟨M, le_of_lt hM⟩
    have h_dist :=
      h_gradLipschitz.dist_le_mul (xk + αk • dk) hxαk xk hxk
    have h_dist' :
        ‖∇ f (xk + αk • dk) - ∇ f xk‖ ≤
          (K : ℝ) * (αk * ‖dk‖) := by
      simpa [K, dist_eq_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hαk.le,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h_dist
    have hK : (K : ℝ) = M := by
      rfl
    rw [← hK]
    exact h_dist'
  -- Then pair the gradient change with `dk` and close with Cauchy-Schwarz plus scalar algebra.
  have h_inner :
      inner ℝ (∇ f (xk + αk • dk) - ∇ f xk) dk ≤
        ‖∇ f (xk + αk • dk) - ∇ f xk‖ * ‖dk‖ :=
    real_inner_le_norm _ _
  nlinarith [h_inner, h_lipschitz, norm_nonneg dk]

/-- Helper for Chapter02 Lemma 2.5.6: the Wolfe curvature inequality and the Lipschitz estimate
force a uniform lower bound on the accepted step length. -/
lemma wolfeStep_lowerBound_from_curvature
    (D : Set Point) (f : Point → ℝ)
    (xk dk : Point) (αk ρ σ M : ℝ)
    (hxk : xk ∈ D)
    (hxαk : xk + αk • dk ∈ D)
    (hM : 0 < M)
    (h_gradLipschitz : LipschitzOnWith ⟨M, le_of_lt hM⟩ (∇ f) D)
    (h_descent : inner ℝ (∇ f xk) dk < 0)
    (h_wolfe :
      WolfePowellCondition
        (lineSearchObjective f xk dk)
        (fun α ↦ inner ℝ (∇ f (xk + α • dk)) dk)
        ρ σ αk) :
    ((1 - σ) / M) * (-(inner ℝ (∇ f xk) dk) / ‖dk‖ ^ (2 : ℕ)) ≤ αk := by
  rcases wolfePowellCondition_iff.mp h_wolfe with ⟨_, hαk, _, h_curvature⟩
  have hdk : dk ≠ 0 := by
    intro hdk
    simp [hdk] at h_descent
  have hnormsq_pos : 0 < ‖dk‖ ^ (2 : ℕ) :=
    sq_pos_of_pos (norm_pos_iff.mpr hdk)
  -- The curvature condition controls the directional derivative gain by `(1 - σ) * (-⟪∇f xk, dk⟫)`.
  have h_curvature_diff :
      (1 - σ) * (-(inner ℝ (∇ f xk) dk)) ≤
        inner ℝ (∇ f (xk + αk • dk) - ∇ f xk) dk := by
    have h_curv :
        σ * inner ℝ (∇ f xk) dk ≤ inner ℝ (∇ f (xk + αk • dk)) dk := by
      simpa using h_curvature
    calc
      (1 - σ) * (-(inner ℝ (∇ f xk) dk)) = (σ - 1) * inner ℝ (∇ f xk) dk := by
        ring
      _ ≤ inner ℝ (∇ f (xk + αk • dk)) dk - inner ℝ (∇ f xk) dk := by
        linarith
      _ = inner ℝ (∇ f (xk + αk • dk) - ∇ f xk) dk := by
        rw [inner_sub_left]
  have h_gradient_change :
      inner ℝ (∇ f (xk + αk • dk) - ∇ f xk) dk ≤ M * αk * ‖dk‖ ^ (2 : ℕ) :=
    directionalGradientChange_le_stepNormSq
      D f xk dk αk M hxk hxαk hM h_gradLipschitz hαk
  have h_main :
      (1 - σ) * (-(inner ℝ (∇ f xk) dk)) ≤ M * αk * ‖dk‖ ^ (2 : ℕ) := by
    exact le_trans h_curvature_diff h_gradient_change
  have hMnormsq_pos : 0 < M * ‖dk‖ ^ (2 : ℕ) :=
    mul_pos hM hnormsq_pos
  have h_div :
      ((1 - σ) * (-(inner ℝ (∇ f xk) dk))) / (M * ‖dk‖ ^ (2 : ℕ)) ≤ αk := by
    refine (div_le_iff₀ hMnormsq_pos).2 ?_
    nlinarith [h_main]
  -- Finally rewrite the scalar division into the source-facing factorized form.
  calc
    ((1 - σ) / M) * (-(inner ℝ (∇ f xk) dk) / ‖dk‖ ^ (2 : ℕ)) =
        ((1 - σ) * (-(inner ℝ (∇ f xk) dk))) / (M * ‖dk‖ ^ (2 : ℕ)) := by
          field_simp [ne_of_gt hM, ne_of_gt hnormsq_pos]
    _ ≤ αk := h_div

/-- Helper for Chapter02 Lemma 2.5.6: squaring the Chapter 2 cosine bridge rewrites the
normalized directional derivative into the source-facing cosine-square factor. -/
lemma negGradientInner_div_searchDirectionNorm_sq_eq_gradientNormSq_mul_cosSq
    (f : Point → ℝ) (xk dk : Point) :
    (-(inner ℝ (∇ f xk) dk) / ‖dk‖) ^ (2 : ℕ) =
      ‖∇ f xk‖ ^ (2 : ℕ) *
        (Real.cos (InnerProductGeometry.angle dk (-(∇ f xk)))) ^ (2 : ℕ) := by
  -- Square the Chapter 2 cosine bridge once and normalize the resulting scalar products.
  have h_cos :=
    gradientNorm_mul_cos_angle_searchDirection_negGradient_eq_neg_gradientInner_div_norm f xk dk
  have h_sq := congrArg (fun t : ℝ ↦ t ^ (2 : ℕ)) h_cos
  calc
    (-(inner ℝ (∇ f xk) dk) / ‖dk‖) ^ (2 : ℕ) =
        (-(inner ℝ (∇ f xk) dk / ‖dk‖)) ^ (2 : ℕ) := by
          ring_nf
    _ = ‖∇ f xk‖ ^ (2 : ℕ) *
          (Real.cos (InnerProductGeometry.angle dk (-(∇ f xk)))) ^ (2 : ℕ) := by
            simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using h_sq.symm

/-- Chapter02 Lemma 2.5.6: let `f : Point → ℝ` be defined on a domain `D`, continuously
differentiable on `D`, meaning that `∇ f y` is the genuine gradient of `f` at each `y ∈ D`, and
suppose this gradient is `M`-Lipschitz on `D` with `M > 0`. If `xk ∈ D`, the accepted trial point
`xk + αk • dk` also lies in `D`, and `αk` satisfies the Wolfe-Powell rule `(2.5.3), (2.5.7)`
along the descent direction `dk`, then
`f xk - f (xk + αk • dk) ≥ ((ρ * (1 - σ)) / M) * ‖gradient f xk‖^2 *
  (Real.cos (InnerProductGeometry.angle dk (-gradient f xk)))^2`. -/
theorem wolfePowellDecrease_ge_gradientNormSq_mul_cosSq
    (D : Set Point) (f : Point → ℝ)
    (xk dk : Point) (αk ρ σ M : ℝ)
    (hxk : xk ∈ D)
    (hxαk : xk + αk • dk ∈ D)
    (hM : 0 < M)
    (h_hasGradientOnD : ∀ y ∈ D, HasGradientAt f (∇ f y) y)
    (h_gradLipschitz : LipschitzOnWith ⟨M, le_of_lt hM⟩ (∇ f) D)
    (h_descent : inner ℝ (∇ f xk) dk < 0)
    (h_wolfe :
      WolfePowellCondition
        (lineSearchObjective f xk dk)
        (fun α ↦ inner ℝ (∇ f (xk + α • dk)) dk)
        ρ σ αk) :
    f xk - f (xk + αk • dk) ≥
      ((ρ * (1 - σ)) / M) * ‖∇ f xk‖ ^ (2 : ℕ) *
        (Real.cos (InnerProductGeometry.angle dk (-(∇ f xk)))) ^ (2 : ℕ) := by
  have _ : HasGradientAt f (∇ f xk) xk :=
    h_hasGradientOnD xk hxk
  rcases wolfePowellCondition_iff.mp h_wolfe with ⟨hparams, hαk, h_sufficientDecrease, _⟩
  rcases wolfePowellParameters_iff.mp hparams with ⟨hρ, _, _⟩
  have hdk : dk ≠ 0 := by
    intro hdk
    simp [hdk] at h_descent
  have h_nonneg_factor : 0 ≤ ρ * (-(inner ℝ (∇ f xk) dk)) := by
    nlinarith
  -- Rewrite Armijo sufficient decrease as a lower bound on the actual decrease in `f`.
  have h_armijo :
      ρ * αk * (-(inner ℝ (∇ f xk) dk)) ≤
        f xk - f (xk + αk • dk) := by
    have h_decrease :
        f (xk + αk • dk) ≤ f xk + ρ * αk * inner ℝ (∇ f xk) dk := by
      simpa [lineSearchObjective_apply, lineSearchObjective_zero] using h_sufficientDecrease
    linarith
  have h_stepLower :
      ((1 - σ) / M) * (-(inner ℝ (∇ f xk) dk) / ‖dk‖ ^ (2 : ℕ)) ≤ αk :=
    wolfeStep_lowerBound_from_curvature
      D f xk dk αk ρ σ M hxk hxαk hM h_gradLipschitz h_descent h_wolfe
  have h_ratio :
      ((ρ * (1 - σ)) / M) * (-(inner ℝ (∇ f xk) dk) / ‖dk‖) ^ (2 : ℕ) ≤
        ρ * αk * (-(inner ℝ (∇ f xk) dk)) := by
    have h_mul :
        (((1 - σ) / M) * (-(inner ℝ (∇ f xk) dk) / ‖dk‖ ^ (2 : ℕ))) *
            (ρ * (-(inner ℝ (∇ f xk) dk))) ≤
          αk * (ρ * (-(inner ℝ (∇ f xk) dk))) := by
      exact mul_le_mul_of_nonneg_right h_stepLower h_nonneg_factor
    -- Normalize the product of the step lower bound with the positive directional factor.
    calc
      ((ρ * (1 - σ)) / M) * (-(inner ℝ (∇ f xk) dk) / ‖dk‖) ^ (2 : ℕ) =
          (((1 - σ) / M) * (-(inner ℝ (∇ f xk) dk) / ‖dk‖ ^ (2 : ℕ))) *
            (ρ * (-(inner ℝ (∇ f xk) dk))) := by
              field_simp [pow_two, ne_of_gt hM, norm_ne_zero_iff.mpr hdk]
      _ ≤ αk * (ρ * (-(inner ℝ (∇ f xk) dk))) := h_mul
      _ = ρ * αk * (-(inner ℝ (∇ f xk) dk)) := by
        ring
  have h_final :
      ((ρ * (1 - σ)) / M) * (-(inner ℝ (∇ f xk) dk) / ‖dk‖) ^ (2 : ℕ) ≤
        f xk - f (xk + αk • dk) := by
    exact le_trans h_ratio h_armijo
  -- Replace the normalized directional derivative by the canonical cosine-square surface.
  rw [negGradientInner_div_searchDirectionNorm_sq_eq_gradientNormSq_mul_cosSq] at h_final
  simpa [mul_assoc] using h_final

end Lemma256
