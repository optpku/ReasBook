/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_33
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient CubicRegularizationModelNotation

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Theorem 4.2.3 lies in the chapter accelerated cubic-Newton / estimating-sequence domain.

Sampled owner declarations:
* `HasLipschitzContinuousHessian`, written on theorem surfaces as `f ∈ C22[L3]`, in
  `Definition_4_2_7`, the chapter owner for `C²` regularity plus global Hessian-Lipschitz
  control;
* `AcceleratedCubicNewtonMethod` in `Algorithm_4_2_2`, the chapter owner for the iterate
  sequence, estimating-function minimizers, accumulated weights, and the standing
  `C22[L3]` smoothness hypothesis;
* `AcceleratedCubicNewtonMethod.psi`, `psi_one`, and `psi_succ` in `Algorithm_4_2_2`, the
  canonical derived estimating-function surface replacing a primitive family `ψ_k`;
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner for the
  cubic model minimized at each accelerated step.

Best owner abstraction:
* source-facing: the inverse-cubic objective-gap estimate for an accelerated cubic Newton method;
* core/canonical: `AcceleratedCubicNewtonMethod`, `cubicRegularizationQuadraticApproximation`,
  and `f ∈ C22[L3]`;
* bridge/view: the owner theorems `method.x_one_isMinOn` and `method.x_succ_isMinOn` recovering
  the textbook minimizing facts for the actual cubic steps used by the algorithm.

Primitive data:
* the objective `f`;
* the accelerated method owner `method`;
* convexity of `f`;
* a global minimizer `xStar`.

Derived API:
* `ContDiff ℝ 2 f` and global `L₃`-Lipschitz control of `hessian f`, both supplied by
  `method.objective_mem`;
* the iterate sequence `x_k`, minimizing sequence `v_k`, estimating functions `ψ_k`, and weights
  `A_k`;
* the initialization `x₁ = T_{L₃}(x₀)`;
* the recursive interpolation and estimating-function update formulas.

The previous statement stored `x`, `v`, `psi`, and `A` as primitive theorem inputs even though
Chapter 4 already owns exactly that data in `AcceleratedCubicNewtonMethod`. This refinement moves
the public surface to that owner, keeps the chapter smoothness hypothesis on the owner itself
instead of splitting it off as a parallel theorem argument, makes the iterate index explicit, and
derives the two actual model-minimization facts from the method's cubic-step owner instead of
keeping them as redundant external assumptions.
-/

-- Proof sketch: prove by induction on `k` the estimating-sequence relations
-- `method.A k * f (method k) ≤ sInf (Set.range (method.psi k))` and
-- `method.psi k z ≤ method.A k * f z + (4 / 3) * L₃ * ‖z - x₀‖^3`.
-- The base step uses the initialization `method 1 = T_{L₃}(x₀)`, `method.psi_one`, and
-- `method.x_one_isMinOn`.
-- For the inductive step, combine convexity of `f`, the minimizing property of `method.v k`, the
-- recursion for `method (k + 1)` and `method.psi (k + 1)`, and the fact that the two actual
-- cubic models used by the algorithm are globally minimized at the chosen iterates via
-- `method.x_succ_isMinOn hk`. Evaluating
-- the upper bound at `xStar`, using `method.A k = k (k + 1) (k + 2) / 6`, and rearranging gives
-- the stated
-- `O(1 / k^3)` estimate.
/-- Helper for Text 4.2.3: pairing the cubic-model stationarity equation with the trial
displacement rewrites the linear term into the Hessian quadratic term plus the cubic penalty. -/
private lemma acceleratedCubicRegularization_stationarityPairing
    {f : E → ℝ} {L3 : NNReal} {M : ℝ} {x T : E}
    (hf : f ∈ C22[L3]) (hT : IsMinOn (m[f; M](x)) Set.univ T) :
    -inner ℝ (∇ f x) (T - x) =
      inner ℝ (hessian f x (T - x)) (T - x) +
        ((M / 2 : ℝ) * ‖T - x‖ ^ (3 : ℕ)) := by
  let d : E := T - x
  have hstationary :=
    cubicRegularization_firstOrderOptimalityCondition_of_isMinOn
      (f := f) (M := M) (x := x) (y := T)
      (hf.contDiff.contDiffAt (x := x)) hT
  have hinner := congrArg (fun v : E ↦ inner ℝ v d) hstationary
  have hinner' :
      inner ℝ (∇ f x) d + inner ℝ (hessian f x d) d +
        ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ)) = 0 := by
    -- Pairing the vector stationarity identity with the trial displacement exposes the cubic term.
    simpa [d, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, pow_succ, pow_two,
      mul_assoc, mul_left_comm, mul_comm] using hinner
  have hlinear :
      -inner ℝ (∇ f x) d =
        inner ℝ (hessian f x d) d + ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ)) := by
    -- Solve the paired identity for the linear Taylor contribution.
    linarith
  simpa [d] using hlinear

/-- Helper for Text 4.2.3: convexity plus the minimizing property of a cubic model yields the
standard cubic objective decrease. -/
private lemma acceleratedCubicRegularization_convexDropOfCubicModelMinimizer
    {f : E → ℝ} {L3 : NNReal} {M : ℝ} {x T : E}
    (hf : f ∈ C22[L3]) (hf_conv : ConvexOn ℝ Set.univ f) (hML : (L3 : ℝ) ≤ M)
    (hT : IsMinOn (m[f; M](x)) Set.univ T) :
    f x - f T ≥ (M / 3 : ℝ) * ‖x - T‖ ^ (3 : ℕ) := by
  let d : E := T - x
  have htrial_le_model : f T ≤ m[f; M](x; T) := by
    -- The whole-space Hessian-Lipschitz owner bounds the objective by the cubic model at `T`.
    exact
      objective_le_cubicRegularizationQuadraticApproximation_of_mem_of_le_hessianLipschitz
        (𝓕 := Set.univ) (f := f) (L := L3) (M := M) (x := x) (y := T)
        (hf := hf.toHessianLipschitzOn isOpen_univ convex_univ)
        (by simp)
        (by simp)
        hML
  have hlinear :
      -inner ℝ (∇ f x) d =
        inner ℝ (hessian f x d) d + ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ)) := by
    -- Re-express the linear term through cubic-model stationarity at the minimizer.
    simpa [d] using
      acceleratedCubicRegularization_stationarityPairing
        (f := f) (L3 := L3) (M := M) (x := x) (T := T) hf hT
  have htrial_le_model_expanded :
      f T ≤
        f x + inner ℝ (∇ f x) d + (1 / 2 : ℝ) * inner ℝ (hessian f x d) d +
          (M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- Expand the cubic model at the minimizing trial point.
    rw [cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply] at htrial_le_model
    simpa [d, add_assoc, add_left_comm, add_comm] using htrial_le_model
  have hmodel_gap :
      f x - f T ≥
        (1 / 2 : ℝ) * inner ℝ (hessian f x d) d + (M / 3 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- Substitute the stationarity identity into the expanded model comparison.
    linarith
  have hessian_nonneg :
      0 ≤ inner ℝ (hessian f x d) d := by
    -- Convexity makes the frozen Hessian quadratic form nonnegative on the whole space.
    exact
      ((convexOn_iff_hessian_quadratic_form_nonneg
        (Q := Set.univ) (f := f) isOpen_univ convex_univ hf.contDiff.contDiffOn).1 hf_conv)
        x
        (by simp)
        d
  have hmain_d : f x - f T ≥ (M / 3 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    -- Dropping the nonnegative Hessian term leaves the cubic decrease term.
    linarith
  simpa [d, norm_sub_rev] using hmain_d

/-- Helper for Text 4.2.3: the accumulated weights of the accelerated cubic Newton method have
the closed form `A_k = k (k + 1) (k + 2) / 6` for every `k ≥ 1`. -/
private lemma acceleratedCubicRegularization_A_closed_form
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ) (hk : 1 ≤ k) :
    method.A k = (k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2) / 6 := by
  refine Nat.le_induction ?_ ?_ k hk
  · -- The initial accumulated weight is exactly `A₁ = 1`.
    norm_num [method.A_one]
  · intro n hn ih
    -- The recursive update adds the textbook coefficient `a_k`.
    rw [method.A_succ n hn, ih, acceleratedCubicNewtonWeight_def]
    norm_num [Nat.cast_add, Nat.cast_one]
    ring_nf

/-- Helper for Text 4.2.3: multiplying the interpolation point `y_k` by `A_{k+1}` recovers the
affine combination `A_k x_k + a_k v_k`. -/
private lemma acceleratedCubicRegularization_interpolation_weight_identity
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ) (hk : 1 ≤ k) :
    (method.A (k + 1)) • acceleratedCubicNewtonInterpolationPoint method method.v k =
      (method.A k) • method k + acceleratedCubicNewtonWeight k • method.v k := by
  have hk_succ : 1 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  have hk3_ne : (k : ℝ) + 3 ≠ 0 := by
    positivity
  have hA_k := acceleratedCubicRegularization_A_closed_form method k hk
  have hA_succ := acceleratedCubicRegularization_A_closed_form method (k + 1) hk_succ
  have hxcoeff :
      method.A (k + 1) * ((k : ℝ) / ((k : ℝ) + 3)) = method.A k := by
    -- Route correction: after multiplying by `A_{k+1}`, the `x_k` coefficient is `A_k`.
    rw [hA_succ, hA_k]
    norm_num [Nat.cast_add, Nat.cast_one]
    field_simp [hk3_ne]
    ring_nf
  have hvcoeff :
      method.A (k + 1) * (3 / ((k : ℝ) + 3)) = acceleratedCubicNewtonWeight k := by
    -- The `v_k` coefficient is exactly `a_k`, not `3 a_k`.
    rw [hA_succ, acceleratedCubicNewtonWeight_def]
    norm_num [Nat.cast_add, Nat.cast_one]
    field_simp [hk3_ne]
    ring_nf
  -- Expand the interpolation point and rewrite both scalar coefficients separately.
  rw [acceleratedCubicNewtonInterpolationPoint_def, smul_add, smul_smul, smul_smul, hxcoeff,
    hvcoeff]

/-- Helper for Text 4.2.3: the update weight satisfies
`a_k = (3 / (k + 3)) A_{k+1}`. -/
private lemma acceleratedCubicRegularization_weight_eq_threeDiv_A_succ
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ) (hk : 1 ≤ k) :
    acceleratedCubicNewtonWeight k =
      (3 / ((k : ℝ) + 3)) * method.A (k + 1) := by
  have hk_succ : 1 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  have hk3_ne : (k : ℝ) + 3 ≠ 0 := by
    positivity
  -- Rewrite both sides through the closed form of `A_{k+1}`.
  rw [acceleratedCubicNewtonWeight_def,
    acceleratedCubicRegularization_A_closed_form method (k + 1) hk_succ]
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [hk3_ne]
  ring_nf

/-- Helper for Text 4.2.3: every estimating function is majorized by
`A_k f(z) + (4 / 3) L₃ ‖z - x₀‖^3`. -/
private lemma acceleratedCubicRegularization_psi_upper_bound
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) (hk : 1 ≤ k) (z : E) :
    method.psi k z ≤
      method.A k * f z + ((4 / 3 : ℝ) * (L3 : ℝ)) * ‖z - x0‖ ^ (3 : ℕ) := by
  refine Nat.le_induction ?_ ?_ k hk
  · have htrial_model :
        f (method 1) ≤
          cubicRegularizationQuadraticApproximation f (L3 : ℝ) x0 (method 1) := by
      -- The Taylor error upper bound places the objective below the cubic model at `x₁`.
      have herror :=
        HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le
          method.objective_mem x0 (method 1)
      rw [cubicRegularizationQuadraticApproximation_apply]
      linarith [(abs_le.mp herror).2]
    have hmin_model :
        cubicRegularizationQuadraticApproximation f (L3 : ℝ) x0 (method 1) ≤
          cubicRegularizationQuadraticApproximation f (L3 : ℝ) x0 z :=
      method.x_one_isMinOn (by simp)
    have hz_model :
        cubicRegularizationQuadraticApproximation f (L3 : ℝ) x0 z ≤
          f z + (((L3 : ℝ) + (L3 : ℝ)) / 6 : ℝ) * ‖z - x0‖ ^ (3 : ℕ) := by
      -- The same Taylor error estimate bounds the comparison model at `z`.
      have herror :=
        HasLipschitzContinuousHessian.secondOrderTaylorModel_error_le
          method.objective_mem x0 z
      rw [cubicRegularizationQuadraticApproximation_apply]
      linarith [(abs_le.mp herror).1]
    rw [method.psi_one, method.A_one]
    have hcompare :
        f (method 1) ≤
          f z + (((L3 : ℝ) + (L3 : ℝ)) / 6 : ℝ) * ‖z - x0‖ ^ (3 : ℕ) :=
      le_trans htrial_model (le_trans hmin_model hz_model)
    linarith
  · intro n hn ih
    have hdiff :
        DifferentiableWithinAt ℝ f Set.univ (method (n + 1)) := by
      exact
        ((method.contDiff.contDiffAt (x := method (n + 1))).differentiableAt (by norm_num)).differentiableWithinAt
    have hsupport :
        f (method (n + 1)) +
            inner ℝ (∇ f (method (n + 1))) (z - method (n + 1)) ≤
          f z := by
      -- Convexity bounds the affine minorant at `x_{k+1}` by the target value `f z`.
      have hplane :=
        hf_conv.lower_tangent_plane (method (n + 1)) (by simp) hdiff z (by simp)
      simpa [gradientWithin, gradient, fderivWithin_univ] using hplane
    have hweight_nonneg : 0 ≤ acceleratedCubicNewtonWeight n := by
      rw [acceleratedCubicNewtonWeight_def]
      positivity
    have hmodel :
        acceleratedCubicNewtonWeight n *
            (f (method (n + 1)) +
              inner ℝ (∇ f (method (n + 1))) (z - method (n + 1))) ≤
          acceleratedCubicNewtonWeight n * f z := by
      exact mul_le_mul_of_nonneg_left hsupport hweight_nonneg
    -- Insert the induction hypothesis into the recursive formula for `ψ_{k+1}`.
    calc
      method.psi (n + 1) z
          = method.psi n z +
              acceleratedCubicNewtonWeight n *
                (f (method (n + 1)) +
                  inner ℝ (∇ f (method (n + 1))) (z - method (n + 1))) := by
            rw [method.psi_succ hn]
      _ ≤
          (method.A n * f z +
              ((4 / 3 : ℝ) * (L3 : ℝ)) * ‖z - x0‖ ^ (3 : ℕ)) +
            acceleratedCubicNewtonWeight n * f z :=
            add_le_add ih hmodel
      _ = method.A (n + 1) * f z +
            ((4 / 3 : ℝ) * (L3 : ℝ)) * ‖z - x0‖ ^ (3 : ℕ) := by
            rw [method.A_succ n hn]
            ring

/-- Helper for Text 4.2.3: the estimating-function minimum controls the objective value by
`A_k f(x_k) ≤ ψ_k(v_k)`. -/
private lemma acceleratedCubicRegularization_value_lower_one
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0) :
    method.A 1 * f (method 1) ≤ method.psi 1 (method.v 1) := by
  -- At the first stage, `ψ₁` is `f(x₁)` plus a nonnegative cubic penalty.
  rw [method.psi_one, method.A_one]
  have hpenalty_nonneg : 0 ≤ (L3 : ℝ) * ‖method.v 1 - x0‖ ^ (3 : ℕ) := by
    positivity
  linarith

/-- Helper for Text 4.2.3: the recursive iterate gains the standard cubic-model decrease from the
interpolation point `y_k`. -/
private lemma acceleratedCubicRegularization_interpolation_drop
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) (hk : 1 ≤ k) :
    f (acceleratedCubicNewtonInterpolationPoint method method.v k) - f (method (k + 1)) ≥
      (((2 : ℝ) * (L3 : ℝ)) / 3) *
        ‖acceleratedCubicNewtonInterpolationPoint method method.v k - method (k + 1)‖ ^ (3 : ℕ) := by
  have hL3_nonneg : 0 ≤ (L3 : ℝ) := by
    positivity
  -- The recursive iterate is the global minimizer of the `2L₃` cubic model at `y_k`.
  simpa using
    (acceleratedCubicRegularization_convexDropOfCubicModelMinimizer
      (f := f)
      (L3 := L3)
      (M := 2 * (L3 : ℝ))
      (x := acceleratedCubicNewtonInterpolationPoint method method.v k)
      (T := method (k + 1))
      method.objective_mem
      hf_conv
      (by linarith)
      (method.x_succ_isMinOn hk))

/-- Helper for Text 4.2.3: convexity at `x_{k+1}` bounds the affine lower model used in the
estimating-function update by the objective value at any comparison point `z`. -/
private lemma acceleratedCubicRegularization_support_at_next_iterate
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) (z : E) :
    f (method (k + 1)) +
        inner ℝ (∇ f (method (k + 1))) (z - method (k + 1)) ≤
      f z := by
  have hdiff :
      DifferentiableWithinAt ℝ f Set.univ (method (k + 1)) := by
    exact
      ((method.contDiff.contDiffAt (x := method (k + 1))).differentiableAt (by norm_num)).differentiableWithinAt
  -- Convexity compares `f z` against the tangent plane at `x_{k+1}`.
  simpa [gradientWithin, gradient, fderivWithin_univ] using
    hf_conv.lower_tangent_plane
      (method (k + 1))
      (by simp)
      hdiff
      z
      (by simp)

/-- Helper for Text 4.2.3: convexity at the interpolation point `y_k` gives the weighted
comparison `A_{k+1} f(y_k) ≤ A_k f(x_k) + a_k f(v_k)`. -/
private lemma acceleratedCubicRegularization_weightedConvexityAtInterpolationPoint
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) (hk : 1 ≤ k) :
    method.A (k + 1) * f (acceleratedCubicNewtonInterpolationPoint method method.v k) ≤
      method.A k * f (method k) +
        acceleratedCubicNewtonWeight k * f (method.v k) := by
  have hk_succ : 1 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  have hA_pos : 0 < method.A (k + 1) := by
    rw [acceleratedCubicRegularization_A_closed_form method (k + 1) hk_succ]
    positivity
  have hk3_pos : 0 < (k : ℝ) + 3 := by
    positivity
  have hconv :
      f (acceleratedCubicNewtonInterpolationPoint method method.v k) ≤
        ((k : ℝ) / ((k : ℝ) + 3)) * f (method k) +
          (3 / ((k : ℝ) + 3)) * f (method.v k) := by
    -- Apply two-point convexity exactly at the interpolation-point coefficients.
    simpa [acceleratedCubicNewtonInterpolationPoint_def, smul_eq_mul] using
      hf_conv.2
        (by simp : method k ∈ Set.univ)
        (by simp : method.v k ∈ Set.univ)
        (by positivity : 0 ≤ (k : ℝ) / ((k : ℝ) + 3))
        (by positivity : 0 ≤ (3 : ℝ) / ((k : ℝ) + 3))
        (by field_simp [hk3_pos.ne'])
  have hscaled := mul_le_mul_of_nonneg_left hconv hA_pos.le
  have hxcoeff :
      method.A (k + 1) * ((k : ℝ) / ((k : ℝ) + 3)) = method.A k := by
    -- The interpolation weight in front of `x_k` is `A_k / A_{k+1}`.
    rw [acceleratedCubicRegularization_A_closed_form method (k + 1) hk_succ,
      acceleratedCubicRegularization_A_closed_form method k hk]
    norm_num [Nat.cast_add, Nat.cast_one]
    field_simp [hk3_pos.ne']
    ring_nf
  have hvcoeff :
      method.A (k + 1) * (3 / ((k : ℝ) + 3)) = acceleratedCubicNewtonWeight k := by
    -- The interpolation weight in front of `v_k` is exactly `a_k / A_{k+1}`.
    rw [acceleratedCubicRegularization_A_closed_form method (k + 1) hk_succ,
      acceleratedCubicNewtonWeight_def]
    norm_num [Nat.cast_add, Nat.cast_one]
    field_simp [hk3_pos.ne']
    ring_nf
  -- Multiply the convexity inequality by `A_{k+1}` and rewrite the coefficients.
  calc
    method.A (k + 1) * f (acceleratedCubicNewtonInterpolationPoint method method.v k) ≤
        method.A (k + 1) *
          ((((k : ℝ) / ((k : ℝ) + 3)) * f (method k)) +
            ((3 / ((k : ℝ) + 3)) * f (method.v k))) :=
      hscaled
    _ =
        (method.A (k + 1) * ((k : ℝ) / ((k : ℝ) + 3))) * f (method k) +
          (method.A (k + 1) * (3 / ((k : ℝ) + 3))) * f (method.v k) := by
      ring
    _ = method.A k * f (method k) +
          acceleratedCubicNewtonWeight k * f (method.v k) := by
      rw [hxcoeff, hvcoeff]

/-- Helper for Text 4.2.3: once `A_k f(x_k) ≤ ψ_k(v_k)` is known, the same lower bound holds at
every comparison point because `v_k` minimizes `ψ_k`. -/
private lemma acceleratedCubicRegularization_value_lower_at
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ) (hk : 1 ≤ k)
    (hprev : method.A k * f (method k) ≤ method.psi k (method.v k))
    (z : E) :
    method.A k * f (method k) ≤ method.psi k z := by
  -- The stage-`k` minimizer gives the pointwise lower bound needed in the next step.
  exact le_trans hprev (method.psi_isMin hk (by simp))

/-- Helper for Text 4.2.3: the doubled cubic step at `y_k` satisfies the standard feasible
comparison inequality against any point `z`. -/
private lemma acceleratedCubicRegularization_doubleStepFeasibleComparison
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ) (hk : 1 ≤ k) (z : E) :
    f (method (k + 1)) ≤
      f z + (((2 : ℝ) * (L3 : ℝ)) / 3) *
        ‖z - acceleratedCubicNewtonInterpolationPoint method method.v k‖ ^ (3 : ℕ) := by
  have hf_hess : HessianLipschitzOn L3 Set.univ f :=
    method.objective_mem.toHessianLipschitzOn isOpen_univ convex_univ
  have hL3_le_double : (L3 : ℝ) ≤ 2 * (L3 : ℝ) := by
    have hL3_nonneg : 0 ≤ (L3 : ℝ) := by
      positivity
    nlinarith
  have htrial :
      f (method (k + 1)) ≤
        EReal.toReal
          (SetConstrainedMinimizationProblem.optimalValue
            (cubicRegularizationProblem f (2 * (L3 : ℝ))
              (acceleratedCubicNewtonInterpolationPoint method method.v k))) := by
    -- The accepted successor iterate is the global minimizer of the doubled cubic model at `y_k`.
    exact
      objective_cubicTrialPoint_le_cubicRegularizationValue_of_le_hessianLipschitz
        hf_hess
        (method.x_succ_isMinOn hk)
        (by simp)
        (by simp)
        hL3_le_double
  have hcomparison :
      EReal.toReal
        (SetConstrainedMinimizationProblem.optimalValue
          (cubicRegularizationProblem f (2 * (L3 : ℝ))
            (acceleratedCubicNewtonInterpolationPoint method method.v k))) ≤
        f z + ((((L3 : ℝ) + (2 * (L3 : ℝ))) / 6 : ℝ)) *
          ‖z - acceleratedCubicNewtonInterpolationPoint method method.v k‖ ^ (3 : ℕ) := by
    -- Compare the doubled cubic model value at `y_k` with the arbitrary feasible point `z`.
    exact
      cubicRegularizationValue_le_feasibleComparison_of_mem
        hf_hess
        (method.x_succ_isMinOn hk)
        (by simp)
        (by simp)
  -- Collapse the cubic coefficient `((L₃ + 2L₃) / 6)` to `(2L₃ / 3)`.
  calc
    f (method (k + 1)) ≤
        EReal.toReal
          (SetConstrainedMinimizationProblem.optimalValue
            (cubicRegularizationProblem f (2 * (L3 : ℝ))
              (acceleratedCubicNewtonInterpolationPoint method method.v k))) :=
      htrial
    _ ≤
        f z + ((((L3 : ℝ) + (2 * (L3 : ℝ))) / 6 : ℝ)) *
          ‖z - acceleratedCubicNewtonInterpolationPoint method method.v k‖ ^ (3 : ℕ) :=
      hcomparison
    _ ≤
        f z + (((2 : ℝ) * (L3 : ℝ)) / 3) *
          ‖z - acceleratedCubicNewtonInterpolationPoint method method.v k‖ ^ (3 : ℕ) := by
      have hpow_nonneg :
          0 ≤ ‖z - acceleratedCubicNewtonInterpolationPoint method method.v k‖ ^ (3 : ℕ) := by
        positivity
      have hcoeff :
          ((((L3 : ℝ) + (2 * (L3 : ℝ))) / 6 : ℝ)) ≤ (((2 : ℝ) * (L3 : ℝ)) / 3) := by
        have hL3_nonneg : 0 ≤ (L3 : ℝ) := by
          positivity
        nlinarith
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (mul_le_mul_of_nonneg_right hcoeff hpow_nonneg) (f z)

/-- Helper for Text 4.2.3: the induction step for the lower estimating-sequence bound is the
direct stage-`k` comparison on the `ψ_{k+1}` surface. -/
private lemma acceleratedCubicRegularization_valueLowerStep_residualForm
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ) (hk : 1 ≤ k) :
    method.psi (k + 1) (method.v (k + 1)) - method.A (k + 1) * f (method (k + 1)) =
      (method.psi k (method.v (k + 1)) - method.A k * f (method k)) -
        (method.A (k + 1) * f (method (k + 1)) -
          (method.A k * f (method k) +
            acceleratedCubicNewtonWeight k *
              (f (method (k + 1)) +
                inner ℝ (∇ f (method (k + 1)))
                  (method.v (k + 1) - method (k + 1))))) := by
  -- Rewrite the successor formulas once so the remaining work is a single residual-vs-slack term.
  rw [method.psi_succ hk, method.A_succ k hk]
  ring

/-- Helper for Text 4.2.3: the stage-`k` slack at the next minimizer is nonnegative because the
known stage-`k` lower bound holds pointwise. -/
private lemma acceleratedCubicRegularization_stageSlackAtNext_nonneg
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ)
    (hprev_at_next : method.A k * f (method k) ≤ method.psi k (method.v (k + 1))) :
    0 ≤ method.psi k (method.v (k + 1)) - method.A k * f (method k) := by
  -- Package the pointwise lower bound as a nonnegative slack for the final linear-arithmetic step.
  exact sub_nonneg.mpr hprev_at_next

/-- Helper for Text 4.2.3: the stage-`k` slack at `v_{k+1}` is the previous minimizing slack plus
the explicit affine-part and cubic-regularizer changes from `v_k` to `v_{k+1}`. -/
private lemma acceleratedCubicRegularization_stageSlackAtNext_split
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ) :
    method.psi k (method.v (k + 1)) - method.A k * f (method k) =
      (method.psi k (method.v k) - method.A k * f (method k)) +
        (method.affinePart k (method.v (k + 1)) - method.affinePart k (method.v k)) +
        (L3 : ℝ) *
          (‖method.v (k + 1) - x0‖ ^ (3 : ℕ) - ‖method.v k - x0‖ ^ (3 : ℕ)) := by
  -- Open `ψ_k` at the two comparison points and collect the affine and cubic increments.
  rw [method.psi_apply, method.psi_apply]
  ring

/-- Helper for Text 4.2.3: evaluating the stage-`k` estimating function at `v_{k+1}` can only
increase its value relative to the stage minimizer `v_k`, so the explicit affine-plus-cubic
increment is nonnegative. -/
private lemma acceleratedCubicRegularization_stageIncrement_nonneg
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ) (hk : 1 ≤ k) :
    0 ≤
      (method.affinePart k (method.v (k + 1)) - method.affinePart k (method.v k)) +
        (L3 : ℝ) *
          (‖method.v (k + 1) - x0‖ ^ (3 : ℕ) - ‖method.v k - x0‖ ^ (3 : ℕ)) := by
  have hmin : method.psi k (method.v k) ≤ method.psi k (method.v (k + 1)) := by
    -- The stage minimizer `v_k` minimizes `ψ_k` over the whole space.
    exact method.psi_isMin hk (by simp)
  -- Expanding `ψ_k` at the two points isolates exactly the displayed increment.
  rw [method.psi_apply, method.psi_apply] at hmin
  linarith

/-- Helper for Text 4.2.3: the explicit affine-plus-cubic increment from `v_k` to `v_{k+1}` is
exactly the change in the stage-`k` estimating function. -/
private lemma acceleratedCubicRegularization_stageIncrement_eq_psiDifference
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ) :
    (method.affinePart k (method.v (k + 1)) - method.affinePart k (method.v k)) +
        (L3 : ℝ) *
          (‖method.v (k + 1) - x0‖ ^ (3 : ℕ) - ‖method.v k - x0‖ ^ (3 : ℕ)) =
      method.psi k (method.v (k + 1)) - method.psi k (method.v k) := by
  -- Expand `ψ_k` at the two comparison points and collect the affine and cubic increments.
  rw [method.psi_apply, method.psi_apply]
  ring

/-- Helper for Text 4.2.3: rewriting the stage-`k` estimating-function increment through the
successor stage isolates the common linear displacement term and leaves only the successor
minimizer slack. -/
private lemma acceleratedCubicRegularization_stageDifference_eq_linearDisplacement_add_successorPsiDrop
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ) (hk : 1 ≤ k) :
    method.psi k (method.v (k + 1)) - method.psi k (method.v k) =
      acceleratedCubicNewtonWeight k *
          inner ℝ (∇ f (method (k + 1))) (method.v k - method.v (k + 1)) +
        (method.psi (k + 1) (method.v (k + 1)) - method.psi (k + 1) (method.v k)) := by
  have hsuccNext :
      method.psi (k + 1) (method.v (k + 1)) =
        method.psi k (method.v (k + 1)) +
          acceleratedCubicNewtonWeight k *
            (f (method (k + 1)) +
              inner ℝ (∇ f (method (k + 1))) (method.v (k + 1) - method (k + 1))) := by
    -- Expand `ψ_{k+1}` at `v_{k+1}` using the owner recursion.
    rw [method.psi_succ hk]
  have hsuccCurr :
      method.psi (k + 1) (method.v k) =
        method.psi k (method.v k) +
          acceleratedCubicNewtonWeight k *
            (f (method (k + 1)) +
              inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1))) := by
    -- Expand `ψ_{k+1}` at `v_k` using the same recursion.
    rw [method.psi_succ hk]
  -- Cancel the shared affine support term and keep only the linear displacement difference.
  rw [hsuccNext, hsuccCurr]
  simp [inner_sub_right]
  ring

/-- Helper for Text 4.2.3: weighted convexity at `y_k` and the cubic decrease from `y_k` to
`x_{k+1}` reduce the successor residual to the remaining stage-`k` surface gap at `v_k`. -/
private lemma acceleratedCubicRegularization_successorResidual_le_surfaceGap
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) (hk : 1 ≤ k) :
    method.A (k + 1) * f (method (k + 1)) -
      (method.A k * f (method k) +
        acceleratedCubicNewtonWeight k *
          (f (method (k + 1)) +
            inner ℝ (∇ f (method (k + 1)))
              (method.v (k + 1) - method (k + 1)))) ≤
      acceleratedCubicNewtonWeight k *
        (f (method.v k) -
          (f (method (k + 1)) +
            inner ℝ (∇ f (method (k + 1)))
              (method.v (k + 1) - method (k + 1)))) -
        method.A (k + 1) *
          ((((2 : ℝ) * (L3 : ℝ)) / 3) *
            ‖acceleratedCubicNewtonInterpolationPoint method method.v k - method (k + 1)‖ ^
              (3 : ℕ)) := by
  let y := acceleratedCubicNewtonInterpolationPoint method method.v k
  have hweighted :
      method.A (k + 1) * f y ≤
        method.A k * f (method k) +
          acceleratedCubicNewtonWeight k * f (method.v k) := by
    -- This is the weighted convexity comparison at the interpolation point.
    simpa [y] using
      acceleratedCubicRegularization_weightedConvexityAtInterpolationPoint method hf_conv k hk
  have hdrop :
      f y - f (method (k + 1)) ≥
        (((2 : ℝ) * (L3 : ℝ)) / 3) * ‖y - method (k + 1)‖ ^ (3 : ℕ) := by
    -- The accepted successor iterate gains the standard cubic decrease from `y_k`.
    simpa [y] using acceleratedCubicRegularization_interpolation_drop method hf_conv k hk
  have hk_succ : 1 ≤ k + 1 := Nat.le_trans hk (Nat.le_succ k)
  have hA_nonneg : 0 ≤ method.A (k + 1) := by
    -- The accumulated weights are positive from their closed form.
    rw [acceleratedCubicRegularization_A_closed_form method (k + 1) hk_succ]
    positivity
  have hdrop_scaled :
      method.A (k + 1) *
          ((((2 : ℝ) * (L3 : ℝ)) / 3) * ‖y - method (k + 1)‖ ^ (3 : ℕ)) ≤
        method.A (k + 1) * (f y - f (method (k + 1))) := by
    -- Scale the cubic drop by the positive coefficient `A_{k+1}`.
    exact mul_le_mul_of_nonneg_left hdrop hA_nonneg
  -- Subtract the same affine support term from both sides of the weighted comparison.
  linarith

/-- Helper for Text 4.2.3: splitting the residual surface term at `v_k` exposes the same linear
displacement term that appears in the successor-stage `ψ` difference. -/
private lemma acceleratedCubicRegularization_surfaceGap_splitAtVk
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (k : ℕ) :
    acceleratedCubicNewtonWeight k *
        (f (method.v k) -
          (f (method (k + 1)) +
            inner ℝ (∇ f (method (k + 1)))
              (method.v (k + 1) - method (k + 1)))) -
      method.A (k + 1) *
        ((((2 : ℝ) * (L3 : ℝ)) / 3) *
          ‖acceleratedCubicNewtonInterpolationPoint method method.v k - method (k + 1)‖ ^ (3 : ℕ)) =
      acceleratedCubicNewtonWeight k *
          inner ℝ (∇ f (method (k + 1))) (method.v k - method.v (k + 1)) +
        (acceleratedCubicNewtonWeight k *
            (f (method.v k) -
              (f (method (k + 1)) +
                inner ℝ (∇ f (method (k + 1))) (method.v k - method (k + 1)))) -
          method.A (k + 1) *
            ((((2 : ℝ) * (L3 : ℝ)) / 3) *
              ‖acceleratedCubicNewtonInterpolationPoint method method.v k - method (k + 1)‖ ^
                (3 : ℕ))) := by
  -- Separate the support term at `v_k` from the explicit displacement to `v_{k+1}`.
  simp [inner_sub_right]
  ring

/-- Helper for Text 4.2.3: the normalized surface residual is controlled directly by the
stage-`k` estimating-function increment. -/
private lemma acceleratedCubicRegularization_surfaceResidual_le_stageDifference
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) (hk : 1 ≤ k) :
    acceleratedCubicNewtonWeight k *
        (f (method.v k) -
          (f (method (k + 1)) +
            inner ℝ (∇ f (method (k + 1)))
              (method.v (k + 1) - method (k + 1)))) -
      method.A (k + 1) *
        ((((2 : ℝ) * (L3 : ℝ)) / 3) *
          ‖acceleratedCubicNewtonInterpolationPoint method method.v k - method (k + 1)‖ ^ (3 : ℕ)) ≤
      method.psi k (method.v (k + 1)) - method.psi k (method.v k) := by
  -- Route correction: the old successor-stage comparison had the wrong sign for `method.psi_isMin`.
  -- Normalize the target to the exact stage-`k` increment, then combine the coefficient rewrite
  -- with the interpolation-point convexity and cubic-drop package already proved above.
  have hweight :=
    acceleratedCubicRegularization_weight_eq_threeDiv_A_succ method k hk
  let _ := hf_conv
  let _ := hk
  let _ := hweight
  -- TODO: after rewriting with
  -- `acceleratedCubicRegularization_surfaceGap_splitAtVk` and
  -- `acceleratedCubicRegularization_stageDifference_eq_linearDisplacement_add_successorPsiDrop`,
  -- the remaining blocker is the normalized goal
  -- `a_k * (f(v_k) - support_{x_{k+1}}(v_k)) - A_{k+1} * cubicDrop
  --    ≤ ψ_{k+1}(v_{k+1}) - ψ_{k+1}(v_k)`.
  -- The current file does not yet expose the cubic Bregman interface needed to compare these two
  -- quantities directly, so this bridge stays as the single scoped proof placeholder.
  sorry

/-- Helper for Text 4.2.3: the normalized successor residual is controlled by the explicit
stage-`k` affine-plus-cubic increment from `v_k` to `v_{k+1}`. -/
private lemma acceleratedCubicRegularization_successorResidual_le_stageIncrement
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) (hk : 1 ≤ k) :
    method.A (k + 1) * f (method (k + 1)) -
      (method.A k * f (method k) +
        acceleratedCubicNewtonWeight k *
              (f (method (k + 1)) +
                inner ℝ (∇ f (method (k + 1)))
                  (method.v (k + 1) - method (k + 1)))) ≤
      method.psi k (method.v (k + 1)) - method.psi k (method.v k) := by
  have hsurface :=
    acceleratedCubicRegularization_successorResidual_le_surfaceGap method hf_conv k hk
  have hbridge :=
    acceleratedCubicRegularization_surfaceResidual_le_stageDifference method hf_conv k hk
  -- Route correction: `successorResidual_le_surfaceGap` already places the support at `v_{k+1}`,
  -- so the closing step is now a direct transitivity onto the stage-`k` `ψ` increment.
  exact le_trans hsurface hbridge

private lemma acceleratedCubicRegularization_value_lower_step
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) (hk : 1 ≤ k)
    (hprev : method.A k * f (method k) ≤ method.psi k (method.v k)) :
    method.A (k + 1) * f (method (k + 1)) ≤ method.psi (k + 1) (method.v (k + 1)) := by
  have hsupport :=
    acceleratedCubicRegularization_successorResidual_le_stageIncrement method hf_conv k hk
  have hresidualForm :=
    acceleratedCubicRegularization_valueLowerStep_residualForm method k hk
  have hstageSplit :=
    acceleratedCubicRegularization_stageSlackAtNext_split method k
  let _ := hsupport
  let _ := hresidualForm
  let _ := hstageSplit
  have hprevSlack_nonneg : 0 ≤ method.psi k (method.v k) - method.A k * f (method k) := by
    -- The induction hypothesis is exactly the nonnegativity of the previous stage slack.
    exact sub_nonneg.mpr hprev
  have hresidual_le_slack :
      method.A (k + 1) * f (method (k + 1)) -
        (method.A k * f (method k) +
          acceleratedCubicNewtonWeight k *
            (f (method (k + 1)) +
              inner ℝ (∇ f (method (k + 1)))
                (method.v (k + 1) - method (k + 1)))) ≤
        method.psi k (method.v (k + 1)) - method.A k * f (method k) := by
    -- The stage slack splits into the previous slack plus the explicit increment, so the new
    -- residual bridge is enough once we discard the nonnegative previous slack.
    rw [hstageSplit]
    linarith
  have hgap_nonneg :
      0 ≤ method.psi (k + 1) (method.v (k + 1)) - method.A (k + 1) * f (method (k + 1)) := by
    -- Rewrite the successor gap into the residual form and use the stage-`k` slack bound.
    rw [hresidualForm]
    linarith
  exact sub_nonneg.mp hgap_nonneg

/-- Helper for Text 4.2.3: the estimating-function minimum controls the objective value by
`A_k f(x_k) ≤ ψ_k(v_k)`. -/
private lemma acceleratedCubicRegularization_value_lower
    {f : E → ℝ} {L3 : NNReal} {x0 : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (k : ℕ) (hk : 1 ≤ k) :
    method.A k * f (method k) ≤ method.psi k (method.v k) := by
  refine Nat.le_induction ?_ ?_ k hk
  · -- The initial stage is exactly the nonnegative cubic penalty in `ψ₁`.
    simpa using acceleratedCubicRegularization_value_lower_one method
  · intro n hn ih
    -- The recursive step now consumes the induction hypothesis directly.
    simpa using acceleratedCubicRegularization_value_lower_step method hf_conv n hn ih

/-- Text 4.2.3: let `method` be the accelerated cubic Newton method. If `f ∈ C22[L3]` is
convex, then every iterate with index `k ≥ 1` satisfies
`f(x_k) - f(x^*) ≤ 8 L₃ ‖x₀ - x^*‖^3 / (k (k + 1) (k + 2))`. -/
theorem acceleratedCubicRegularization_gap_le_inverse_cubic_rate
    {f : E → ℝ} {L3 : NNReal} {x0 xStar : E}
    (method : AcceleratedCubicNewtonMethod f L3 x0)
    (hf_conv : ConvexOn ℝ Set.univ f)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) (hk : 1 ≤ k) :
      f (method k) - f xStar ≤
        (8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
  let _ := hxStar
  have hupper :
      method.psi k xStar ≤
        method.A k * f xStar +
          ((4 / 3 : ℝ) * (L3 : ℝ)) * ‖x0 - xStar‖ ^ (3 : ℕ) := by
    -- Evaluate the estimating-sequence majorization at the minimizer `xStar`.
    simpa [norm_sub_rev] using
      acceleratedCubicRegularization_psi_upper_bound method hf_conv k hk xStar
  have hmin :
      method.psi k (method.v k) ≤ method.psi k xStar := by
    -- The distinguished point `v_k` is the global minimizer of `ψ_k`.
    exact method.psi_isMin hk (by simp)
  have hvalue :
      method.A k * f (method k) ≤ method.A k * f xStar +
        ((4 / 3 : ℝ) * (L3 : ℝ)) * ‖x0 - xStar‖ ^ (3 : ℕ) := by
    exact le_trans (le_trans (acceleratedCubicRegularization_value_lower method hf_conv k hk) hmin) hupper
  have hgap_mul :
      method.A k * (f (method k) - f xStar) ≤
        ((4 / 3 : ℝ) * (L3 : ℝ)) * ‖x0 - xStar‖ ^ (3 : ℕ) := by
    linarith
  have hk_pos_nat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast hk_pos_nat
  have hk1_ne : (k : ℝ) + 1 ≠ 0 := by positivity
  have hk2_ne : (k : ℝ) + 2 ≠ 0 := by positivity
  have hA_pos : 0 < method.A k := by
    rw [acceleratedCubicRegularization_A_closed_form method k hk]
    positivity
  have hdivide :
      f (method k) - f xStar ≤
        (((4 / 3 : ℝ) * (L3 : ℝ)) * ‖x0 - xStar‖ ^ (3 : ℕ)) / method.A k := by
    -- Divide the scaled gap estimate by the positive weight `A_k`.
    refine (le_div_iff₀ hA_pos).2 ?_
    simpa [mul_comm, mul_left_comm, mul_assoc] using hgap_mul
  calc
    f (method k) - f xStar ≤
        (((4 / 3 : ℝ) * (L3 : ℝ)) * ‖x0 - xStar‖ ^ (3 : ℕ)) / method.A k := hdivide
    _ =
        (8 * (L3 : ℝ) * ‖x0 - xStar‖ ^ (3 : ℕ)) /
          ((k : ℝ) * ((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
          rw [acceleratedCubicRegularization_A_closed_form method k hk]
          field_simp [hk_pos.ne', hk1_ne, hk2_ne]
          ring
