/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_4_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Assumption_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open SmoothNonlinearEquationProblem
open scoped InnerProduct LevelSetNotation Manifold MinimalSingularValue
open scoped ModifiedGaussNewtonLocalModelNotation
open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u v

variable {E₁ : Type u} {E₂ : Type v}
variable [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁]
variable [CompleteSpace E₁]
variable [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂]
variable [CompleteSpace E₂]

/- Theorem 4.4.2 lies in the local modified Gauss--Newton / nondegenerate-solution domain.

Sampled owner-style declarations:
* `ModifiedGaussNewtonMethod` in `Algorithm_4_4_1`, the chapter owner for the iterate dynamics
  and accepted trial points;
* `SmoothNonlinearEquationProblem.solutionSet` in `Definition_4_4_8`, the chapter owner for the
  exact-solution locus `problem x = 0`;
* `minimalSingularValue` / `σ_min(_)` in `Definition_4_4_5`, the chapter owner for the primal
  nondegeneracy quantity;
* the sharpness witness packaged by `IsSharpMeritFunction` from `Definition_4_4_9`;
* the complete-inner-product-space ambient layer already used by nearby Chapter 4 owners.

Best owner abstraction:
* source-facing: the one-step local contraction of the modified Gauss--Newton iteration near a
  nondegenerate exact solution;
* core/canonical: the method `method`, an exact solution owner `xStar ∈ solutionSet problem`,
  the explicit sublevel-set premises `xStar ∈ 𝓛[f]((f x0))` and `x_k ∈ 𝓛[f]((f x0))`, and the
  displayed sharpness witness `γφ`;
* bridge/view: the direct source conclusion from `(4.4.20)`, split across the main theorem-level
  pair of facts and the companion theorem `local_contraction_bound_le_current_error`, which
  isolates the final scalar comparison for downstream reuse.

Primitive data:
* the method `method`;
* the exact solution point `xStar`;
* the iterate index `k`;
* the sharpness witness `γφ`.

Derived API:
* the source-facing next-iterate sublevel membership;
* the explicit quadratic error bound from `(4.4.20)`;
* the final comparison of that explicit bound with the current error.

This repair follows the fallback source text directly: the main theorem now carries the explicit
sublevel-set premises on `x*` and `x_k`, keeps the chapter owner `solutionSet problem` for the
equation `F(x*) = 0`, and reinstates the convex feasible-domain route needed by the chapter
comparison lemmas: a convex set `𝓕`, Jacobian-Lipschitz control of `problem` on `𝓕`, and the
source-facing Assumption 4.4.2 owner `IsSufficientlyLargeFeasibleSetAt f 𝓕 x₀` supplying the
containment bridge `𝓛[f]((f x₀)) ⊆ 𝓕`. The main labeled theorem now exposes the next-iterate
membership and explicit quadratic estimate on the theorem surface, while the companion theorem
isolates the final scalar inequality in the same nondegenerate regime for downstream reuse.
-/

local notation "SmoothMap" =>
  C^⊤⟮𝓘(ℝ, E₁), E₁; 𝓘(ℝ, E₂), E₂⟯

section

variable {problem : SmoothMap}
variable {φ : E₂ → ℝ} [IsSharpMeritFunction φ]
variable {L0 : ℝ} {L : NNReal} {γφ : ℝ} {x0 xStar : E₁}

local notation "f" => meritFunctionReformulation problem φ
local notation "𝓛0" => (𝓛[f]((f x0)) : Set E₁)

/-- Helper for Theorem 4.4.2: regroup the affine correction on the segment remainder into the
left-associated subtraction form used by the Taylor bound. -/
private theorem segmentCorrectedRemainder_sub_sub
    (x y : E₁) (v : E₂) :
    (fun u : ℝ ↦ problem (AffineMap.lineMap x y u) - (problem x + u • v)) =
      (fun u : ℝ ↦ problem (AffineMap.lineMap x y u) - problem x - u • v) := by
  -- Regroup the affine correction so the segment remainder matches the later Taylor expression.
  ext u
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 4.4.2: the corrected segment remainder has derivative given by the
Jacobian increment applied to the segment direction. -/
private theorem segmentCorrectedRemainder_hasDerivAt
    (x y : E₁) (t : ℝ) :
    HasDerivAt
      (fun u : ℝ ↦
        problem (AffineMap.lineMap x y u) - problem x -
          u • (fderiv ℝ problem x (y - x)))
      ((fderiv ℝ problem (AffineMap.lineMap x y t)) (y - x) -
        fderiv ℝ problem x (y - x))
      t := by
  -- Differentiate the restriction of `problem` to the affine segment from `x` to `y`.
  have hdiff : DifferentiableAt ℝ problem (AffineMap.lineMap x y t) := by
    exact
      (problem.contMDiff.contDiff.contDiffAt (x := AffineMap.lineMap x y t)).differentiableAt
        (by simp)
  have hseg :
      HasDerivAt
        (fun u : ℝ ↦ problem (AffineMap.lineMap x y u))
        ((fderiv ℝ problem (AffineMap.lineMap x y t)) (y - x))
        t := by
    simpa [Function.comp] using
      ((hdiff.hasFDerivAt.comp t
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)).hasFDerivAt)).hasDerivAt
  have hlin :
      HasDerivAt
        (fun u : ℝ ↦ u • (fderiv ℝ problem x (y - x)))
        (fderiv ℝ problem x (y - x))
        t := by
    -- The affine correction contributes the constant Jacobian term at the base point.
    simpa [one_smul] using
      ((hasDerivAt_id t).smul_const (fderiv ℝ problem x (y - x)))
  have hconstAddLin :
      HasDerivAt
        (fun u : ℝ ↦ problem x + u • (fderiv ℝ problem x (y - x)))
        (0 + fderiv ℝ problem x (y - x))
        t := by
    -- Package the constant and linear parts into the exact affine correction shape.
    exact (hasDerivAt_const t (problem x)).add hlin
  have hmainParenthesized :
      HasDerivAt
        (fun u : ℝ ↦
          problem (AffineMap.lineMap x y u) -
            (problem x + u • (fderiv ℝ problem x (y - x))))
        ((fderiv ℝ problem (AffineMap.lineMap x y t)) (y - x) -
          (0 + fderiv ℝ problem x (y - x)))
        t := by
    -- Subtract the affine model before normalizing the function expression itself.
    exact hseg.sub hconstAddLin
  have hmain :
      HasDerivAt
        (fun u : ℝ ↦
          problem (AffineMap.lineMap x y u) - problem x -
            u • (fderiv ℝ problem x (y - x)))
        ((fderiv ℝ problem (AffineMap.lineMap x y t)) (y - x) -
          fderiv ℝ problem x (y - x))
        t := by
    -- Rewrite the parenthesized subtraction into the exact remainder shape used downstream.
    simpa [zero_add, segmentCorrectedRemainder_sub_sub (problem := problem)] using
      hmainParenthesized
  exact hmain

/-- Helper for Theorem 4.4.2: the corrected segment remainder vanishes at `0` and evaluates to
the Taylor remainder at `1`. -/
private theorem segmentCorrectedRemainder_endpoints
    (x y : E₁) :
    let R : ℝ → E₂ := fun t ↦
      problem (AffineMap.lineMap x y t) - problem x -
        t • (fderiv ℝ problem x (y - x))
    R 0 = 0 ∧ R 1 = problem y - problem x - fderiv ℝ problem x (y - x) := by
  -- Evaluate the segment remainder at the two endpoints.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 4.4.2: the Jacobian-Lipschitz bound controls the derivative of the
corrected segment remainder. -/
private theorem segmentCorrectedRemainder_deriv_norm_le
    {𝓕 : Set E₁} {L : NNReal}
    (h𝓕 : Convex ℝ 𝓕)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (x y : E₁) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕)
    {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ‖deriv
        (fun u : ℝ ↦
          problem (AffineMap.lineMap x y u) - problem x -
            u • (fderiv ℝ problem x (y - x)))
        t‖ ≤
      (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := by
  -- Start from the explicit derivative formula for the corrected segment remainder.
  have hderivAt := segmentCorrectedRemainder_hasDerivAt (problem := problem) x y t
  rw [hderivAt.deriv]
  have hlineMem : AffineMap.lineMap x y t ∈ 𝓕 :=
    h𝓕.lineMap_mem hx hy (Set.mem_Icc_of_Ioo ht)
  have hJacobianBound :
      ‖fderiv ℝ problem (AffineMap.lineMap x y t) - fderiv ℝ problem x‖ ≤
        (L : ℝ) * ‖AffineMap.lineMap x y t - x‖ := by
    simpa [dist_eq_norm] using
      hJacobianLipschitz.dist_le_mul (AffineMap.lineMap x y t) hlineMem x hx
  have hsegmentNorm :
      ‖AffineMap.lineMap x y t - x‖ = t * ‖y - x‖ := by
    calc
      ‖AffineMap.lineMap x y t - x‖ = ‖t • (y - x)‖ := by
        simp [AffineMap.lineMap_apply_module']
      _ = |t| * ‖y - x‖ := norm_smul t (y - x)
      _ = t * ‖y - x‖ := by
        simp [abs_of_pos ht.1]
  -- Move from operator norm control to the pointwise derivative estimate.
  calc
    ‖((fderiv ℝ problem (AffineMap.lineMap x y t)) - fderiv ℝ problem x) (y - x)‖ ≤
        ‖fderiv ℝ problem (AffineMap.lineMap x y t) - fderiv ℝ problem x‖ * ‖y - x‖ :=
      (fderiv ℝ problem (AffineMap.lineMap x y t) - fderiv ℝ problem x).le_opNorm (y - x)
    _ ≤ ((L : ℝ) * ‖AffineMap.lineMap x y t - x‖) * ‖y - x‖ := by
      gcongr
    _ = ((L : ℝ) * (t * ‖y - x‖)) * ‖y - x‖ := by
      rw [hsegmentNorm]
    _ = (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := by
      ring

/-- Helper for Theorem 4.4.2: on a convex feasible set with Jacobian-Lipschitz residual map, the
first-order Taylor remainder is bounded by `((L : ℝ) / 2) * ‖y - x‖²`. -/
private theorem localJacobianLipschitzTaylorRemainder_le
    {𝓕 : Set E₁} {L : NNReal}
    (h𝓕 : Convex ℝ 𝓕)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (x y : E₁) (hx : x ∈ 𝓕) (hy : y ∈ 𝓕) :
    ‖problem y - problem x - fderiv ℝ problem x (y - x)‖ ≤
      ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  -- Restrict `problem` to the segment from `x` to `y` and subtract its affine approximation at
  -- `x`, so the one-variable remainder vanishes at `0` and equals the target Taylor remainder at
  -- `1`.
  let R : ℝ → E₂ := fun t ↦
    problem (AffineMap.lineMap x y t) - problem x -
      t • (fderiv ℝ problem x (y - x))
  have hcont : ContinuousOn R (Set.Icc (0 : ℝ) 1) := by
    intro t ht
    exact
      (segmentCorrectedRemainder_hasDerivAt (problem := problem) x y t).continuousAt
        .continuousWithinAt
  have hdiff : DifferentiableOn ℝ R (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    exact
      (segmentCorrectedRemainder_hasDerivAt (problem := problem) x y t).differentiableAt
        .differentiableWithinAt
  have hbound :
      ‖R 1 - R 0‖ ≤ ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := by
    have hboundAux :=
      norm_sub_le_integral_of_norm_deriv_le_of_le
        (B := fun t : ℝ ↦ (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ))
        (a := (0 : ℝ)) (b := 1)
        (by norm_num)
        hcont
        hdiff
        (Filter.Eventually.of_forall fun t ht_mem ↦
          segmentCorrectedRemainder_deriv_norm_le
            (problem := problem) h𝓕 hJacobianLipschitz x y hx hy ht_mem)
        (by
          simpa [mul_assoc] using
            (show IntervalIntegrable
                (fun t : ℝ ↦ t)
                MeasureTheory.volume
                0
                1 from
              intervalIntegrable_id).const_mul ((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)))
    simpa using hboundAux
  have hendpoint := segmentCorrectedRemainder_endpoints (problem := problem) x y
  have hR0 : R 0 = 0 := by
    simpa [R] using hendpoint.1
  have hR1 : R 1 = problem y - problem x - fderiv ℝ problem x (y - x) := by
    simpa [R] using hendpoint.2
  rw [hR1, hR0, sub_zero] at hbound
  calc
    ‖problem y - problem x - fderiv ℝ problem x (y - x)‖ ≤
        ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) := hbound
    _ = ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
      -- Compute the scalar factor `∫_0^1 t dt = 1 / 2`.
      calc
        ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖y - x‖ ^ (2 : ℕ) =
            ∫ t in (0 : ℝ)..1, ((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) * t := by
              congr with t
              ring
        _ = ((L : ℝ) * ‖y - x‖ ^ (2 : ℕ)) * ∫ t in (0 : ℝ)..1, t := by
              rw [intervalIntegral.integral_const_mul]
        _ = ((L : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
              rw [integral_id]
              norm_num
              ring

/-- Helper for Theorem 4.4.2: the Jacobian near `xStar` keeps the lower bound
`σ_min(F'(xStar)) - L ‖x - xStar‖` on image norms. -/
private theorem nearbyJacobian_mul_norm_ge_shiftedSigma
    {𝓕 : Set E₁} {L : NNReal}
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (x : E₁)
    (hx : x ∈ 𝓕)
    (hxStar_mem : xStar ∈ 𝓕)
    (v : E₁) :
    (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖x - xStar‖) * ‖v‖ ≤
      ‖fderiv ℝ problem x v‖ := by
  -- Compare `F'(x)` with `F'(xStar)` in operator norm and transport the singular-value lower
  -- bound through the perturbation estimate.
  have hσ :
      σ_min(fderiv ℝ problem xStar) * ‖v‖ ≤ ‖fderiv ℝ problem xStar v‖ := by
    simpa using (fderiv ℝ problem xStar).minimalSingularValue_mul_norm_le v
  have hJacobianBound :
      ‖fderiv ℝ problem xStar - fderiv ℝ problem x‖ ≤ (L : ℝ) * ‖x - xStar‖ := by
    simpa [dist_eq_norm, dist_comm] using
      hJacobianLipschitz.dist_le_mul x hx xStar hxStar_mem
  have hPerturb :
      ‖(fderiv ℝ problem xStar - fderiv ℝ problem x) v‖ ≤
        ((L : ℝ) * ‖x - xStar‖) * ‖v‖ := by
    calc
      ‖(fderiv ℝ problem xStar - fderiv ℝ problem x) v‖ ≤
          ‖fderiv ℝ problem xStar - fderiv ℝ problem x‖ * ‖v‖ :=
        (fderiv ℝ problem xStar - fderiv ℝ problem x).le_opNorm v
      _ ≤ ((L : ℝ) * ‖x - xStar‖) * ‖v‖ := by
        gcongr
  have hTriangle :
      ‖fderiv ℝ problem xStar v‖ ≤
        ‖fderiv ℝ problem x v‖ +
          ‖(fderiv ℝ problem xStar - fderiv ℝ problem x) v‖ := by
    have hsplit :
        fderiv ℝ problem xStar v =
          fderiv ℝ problem x v + (fderiv ℝ problem xStar - fderiv ℝ problem x) v := by
      simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    rw [hsplit]
    exact norm_add_le _ _
  have hcore :
      σ_min(fderiv ℝ problem xStar) * ‖v‖ ≤
        ‖fderiv ℝ problem x v‖ + ((L : ℝ) * ‖x - xStar‖) * ‖v‖ := by
    exact hσ.trans <| hTriangle.trans <| by gcongr
  nlinarith

/-- Helper for Theorem 4.4.2: comparing the accepted model value with the exact solution
competitor `xStar` yields the upper bound `(3 / 2) L ‖x_k - xStar‖²`. -/
private theorem acceptedModelValue_le_threeHalvesLipSq
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    {𝓕 : Set E₁}
    {k : ℕ}
    (h𝓕 : Convex ℝ 𝓕)
    (hxStar_level : xStar ∈ 𝓛0)
    (hxStar : xStar ∈ solutionSet problem)
    (hk_level : method k ∈ 𝓛0)
    (hlarge : IsSufficientlyLargeFeasibleSetAt f 𝓕 x0)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕) :
    f[(method.step k)] (method k) ≤
      (3 / 2 : ℝ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
  -- Compare the accepted model value with the feasible competitor `xStar`.
  have hxStar_mem : xStar ∈ 𝓕 := hlarge.levelSet_subset hxStar_level
  have hxk_mem : method k ∈ 𝓕 := hlarge.levelSet_subset hk_level
  have hFxStar : problem xStar = 0 := by
    rw [mem_solutionSet_iff] at hxStar
    exact hxStar
  have hφ_zero : φ 0 = 0 := by
    simpa using (IsMeritFunction.eq_zero_iff (φ := φ) (0 : E₂)).2 rfl
  have hφ_le_norm (u : E₂) : φ u ≤ ‖u‖ := by
    -- Route correction: use the one-sided Lipschitz inequality `φ u ≤ φ 0 + dist u 0`.
    simpa [hφ_zero, dist_eq_norm] using
      (IsSharpMeritFunction.lipschitz_one (φ := φ)).le_add_mul u 0
  have hcompare :
      f[(method.step k)] (method k) ≤
        quadraticallyRegularizedObjective
          (ψ[problem; φ; fun x ↦ fderiv ℝ problem x] (method k))
          (method.regularization k)
          (method k)
          xStar := by
    -- The chosen step globally minimizes the current quadratic-regularized local model.
    simpa [ModifiedGaussNewtonStep.modelValueAtUniv_def,
      ModifiedGaussNewtonStep.residualAtUniv_def, quadraticallyRegularizedObjective_apply] using
      (isMinOn_univ_iff.mp (method.step_isMinOn k)) xStar
  have hremainder :
      ‖problem (method k) + fderiv ℝ problem (method k) (xStar - method k)‖ ≤
        ((L : ℝ) / 2) * ‖method k - xStar‖ ^ (2 : ℕ) := by
    have hTaylor :=
      localJacobianLipschitzTaylorRemainder_le
        (problem := problem) h𝓕 hJacobianLipschitz (method k) xStar hxk_mem hxStar_mem
    have hresidual :
        problem (method k) + fderiv ℝ problem (method k) (xStar - method k) =
          -(problem xStar - problem (method k) -
            fderiv ℝ problem (method k) (xStar - method k)) := by
      simp [hFxStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    simpa [hresidual, norm_sub_rev] using hTaylor
  have hreg :
      (method.regularization k / 2 : ℝ) * ‖xStar - method k‖ ^ (2 : ℕ) ≤
        (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
    have hcoef : (method.regularization k / 2 : ℝ) ≤ (L : ℝ) := by
      linarith [method.regularization_le_two_mul_L k]
    have hsq_nonneg : 0 ≤ ‖method k - xStar‖ ^ (2 : ℕ) := by
      positivity
    calc
      (method.regularization k / 2 : ℝ) * ‖xStar - method k‖ ^ (2 : ℕ) =
          (method.regularization k / 2 : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
            simp [norm_sub_rev]
      _ ≤ (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_right hcoef hsq_nonneg
  calc
    f[(method.step k)] (method k) ≤
        quadraticallyRegularizedObjective
          (ψ[problem; φ; fun x ↦ fderiv ℝ problem x] (method k))
          (method.regularization k)
          (method k)
          xStar := hcompare
    _ =
        φ (problem (method k) + fderiv ℝ problem (method k) (xStar - method k)) +
          (method.regularization k / 2 : ℝ) * ‖xStar - method k‖ ^ (2 : ℕ) := by
            simp [quadraticallyRegularizedObjective_apply, modifiedGaussNewtonLocalModel_apply]
    _ ≤
        ‖problem (method k) + fderiv ℝ problem (method k) (xStar - method k)‖ +
          (method.regularization k / 2 : ℝ) * ‖xStar - method k‖ ^ (2 : ℕ) := by
            gcongr
            exact hφ_le_norm _
    _ ≤
        ((L : ℝ) / 2) * ‖method k - xStar‖ ^ (2 : ℕ) +
          (method.regularization k / 2 : ℝ) * ‖xStar - method k‖ ^ (2 : ℕ) := by
            gcongr
    _ ≤
        ((L : ℝ) / 2) * ‖method k - xStar‖ ^ (2 : ℕ) +
          (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
            exact add_le_add_left hreg _
    _ = (3 / 2 : ℝ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
            ring

/-- Helper for Theorem 4.4.2: the accepted local-model residual dominates the shifted singular
value times the next distance to `xStar`, up to the Taylor remainder at `(method k, xStar)`. -/
private theorem acceptedModelValue_add_gammaHalfLipSq_ge_shiftedSigmaDistance
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    {𝓕 : Set E₁}
    {k : ℕ}
    (h𝓕 : Convex ℝ 𝓕)
    (hxStar_level : xStar ∈ 𝓛0)
    (hxStar : xStar ∈ solutionSet problem)
    (hk_level : method k ∈ 𝓛0)
    (hlarge : IsSufficientlyLargeFeasibleSetAt f 𝓕 x0)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (hγφ_mem : γφ ∈ Set.Ioc (0 : ℝ) 1)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u) :
    γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖method k - xStar‖) *
        ‖method (k + 1) - xStar‖ ≤
      f[(method.step k)] (method k) +
        (γφ * ((L : ℝ) / 2)) * ‖method k - xStar‖ ^ (2 : ℕ) := by
  -- Lower-bound the accepted residual by its linearized part at `xStar`, then absorb the Taylor
  -- remainder coming from `(method k, xStar)`.
  have hγ_pos : 0 < γφ := hγφ_mem.1
  have hxStar_mem : xStar ∈ 𝓕 := hlarge.levelSet_subset hxStar_level
  have hxk_mem : method k ∈ 𝓕 := hlarge.levelSet_subset hk_level
  have hFxStar : problem xStar = 0 := by
    rw [mem_solutionSet_iff] at hxStar
    exact hxStar
  let residual : E₂ :=
    problem (method k) + fderiv ℝ problem (method k) (method (k + 1) - method k)
  let linearPart : E₂ := fderiv ℝ problem (method k) (method (k + 1) - xStar)
  let remainder : E₂ :=
    problem xStar - problem (method k) - fderiv ℝ problem (method k) (xStar - method k)
  have hlinear :
      (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖method k - xStar‖) *
          ‖method (k + 1) - xStar‖ ≤
        ‖linearPart‖ := by
    simpa [linearPart] using
      nearbyJacobian_mul_norm_ge_shiftedSigma
        (problem := problem) (xStar := xStar) hJacobianLipschitz (method k) hxk_mem hxStar_mem
          (method (k + 1) - xStar)
  have hdecomp :
      linearPart = residual + remainder := by
    -- Rewrite the accepted residual as the desired linear term plus the base-point remainder.
    dsimp [linearPart, residual, remainder]
    rw [show method (k + 1) - xStar = (method (k + 1) - method k) + (method k - xStar) by abel]
    rw [map_add]
    simp [hFxStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have htriangle :
      ‖linearPart‖ ≤ ‖residual‖ + ‖remainder‖ := by
    rw [hdecomp]
    exact norm_add_le _ _
  have hmodel :
      γφ * ‖residual‖ ≤ f[(method.step k)] (method k) := by
    have hresidual :
        γφ * ‖residual‖ ≤
          φ residual + (method.regularization k / 2 : ℝ) *
            ‖method (k + 1) - method k‖ ^ (2 : ℕ) := by
      have hpen_nonneg :
          0 ≤ (method.regularization k / 2 : ℝ) * ‖method (k + 1) - method k‖ ^ (2 : ℕ) := by
        positivity
      have hcore : γφ * ‖residual‖ ≤ φ residual := hγφ_lower residual
      linarith
    simpa [residual, method.x_succ k, quadraticallyRegularizedObjective_apply,
      modifiedGaussNewtonLocalModel_apply, meritFunctionReformulation_apply] using hresidual
  have hTaylor :
      ‖remainder‖ ≤ ((L : ℝ) / 2) * ‖method k - xStar‖ ^ (2 : ℕ) := by
    simpa [remainder, norm_sub_rev] using
      localJacobianLipschitzTaylorRemainder_le
        (problem := problem) h𝓕 hJacobianLipschitz (method k) xStar hxk_mem hxStar_mem
  have hscaledTaylor :
      γφ * ‖remainder‖ ≤
        (γφ * ((L : ℝ) / 2)) * ‖method k - xStar‖ ^ (2 : ℕ) := by
    have hγ_nonneg : 0 ≤ γφ := hγ_pos.le
    have hbound :=
      mul_le_mul_of_nonneg_left hTaylor hγ_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hbound
  have hleft :
      γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖method k - xStar‖) *
          ‖method (k + 1) - xStar‖ ≤
        γφ * ‖linearPart‖ := by
    exact mul_le_mul_of_nonneg_left hlinear hγ_pos.le
  have hsplit :
      γφ * ‖linearPart‖ ≤ γφ * ‖residual‖ + γφ * ‖remainder‖ := by
    nlinarith
  calc
    γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖method k - xStar‖) *
        ‖method (k + 1) - xStar‖ ≤
      γφ * ‖linearPart‖ := hleft
    _ ≤ γφ * ‖residual‖ + γφ * ‖remainder‖ := hsplit
    _ ≤ f[(method.step k)] (method k) +
          (γφ * ((L : ℝ) / 2)) * ‖method k - xStar‖ ^ (2 : ℕ) := by
            exact add_le_add hmodel hscaledTaylor

/-- Helper for Theorem 4.4.2: the accepted model value controls the next distance to `xStar`
after transporting nondegeneracy from `xStar` to the current iterate. -/
private theorem acceptedStepDistance_mul_shiftedSigma_le_rhs
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    {𝓕 : Set E₁}
    {k : ℕ}
    (h𝓕 : Convex ℝ 𝓕)
    (hxStar_level : xStar ∈ 𝓛0)
    (hxStar : xStar ∈ solutionSet problem)
    (hk_level : method k ∈ 𝓛0)
    (hlarge : IsSufficientlyLargeFeasibleSetAt f 𝓕 x0)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (hσ_pos : 0 < σ_min(fderiv ℝ problem xStar))
    (hγφ_mem : γφ ∈ Set.Ioc (0 : ℝ) 1)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u) :
    γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖method k - xStar‖) *
        ‖method (k + 1) - xStar‖ ≤
      (3 * (1 + γφ) / 2 : ℝ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
  -- Combine the upper comparison at `xStar` with the lower bridge for the accepted residual.
  have hγ_nonneg : 0 ≤ γφ := hγφ_mem.1.le
  have hupper :=
    acceptedModelValue_le_threeHalvesLipSq
      (problem := problem) (φ := φ) (L0 := L0) (L := L) (x0 := x0) (xStar := xStar)
      method h𝓕 hxStar_level hxStar hk_level hlarge hJacobianLipschitz
  have hbridge :=
    acceptedModelValue_add_gammaHalfLipSq_ge_shiftedSigmaDistance
      (problem := problem) (φ := φ) (L0 := L0) (L := L) (γφ := γφ) (x0 := x0) (xStar := xStar)
      method h𝓕 hxStar_level hxStar hk_level hlarge hJacobianLipschitz hγφ_mem hγφ_lower
  have hcoef :
      ((3 + γφ) / 2 : ℝ) ≤ (3 * (1 + γφ) / 2 : ℝ) := by
    nlinarith
  have hterm_nonneg : 0 ≤ (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
    positivity
  calc
    γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖method k - xStar‖) *
        ‖method (k + 1) - xStar‖ ≤
      f[(method.step k)] (method k) +
        (γφ * ((L : ℝ) / 2)) * ‖method k - xStar‖ ^ (2 : ℕ) := hbridge
    _ ≤
        (3 / 2 : ℝ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ) +
          (γφ * ((L : ℝ) / 2)) * ‖method k - xStar‖ ^ (2 : ℕ) := by
            exact add_le_add_right hupper _
    _ = ((3 + γφ) / 2 : ℝ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
            ring
    _ ≤ (3 * (1 + γφ) / 2 : ℝ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_right hcoef hterm_nonneg

/-- Helper for Theorem 4.4.2: the closeness hypothesis forces the denominator
`σ_min(F'(xStar)) - L ‖x_k - xStar‖` to stay positive. -/
private theorem shiftedSigma_pos_of_close
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    {k : ℕ}
    (hσ_pos : 0 < σ_min(fderiv ℝ problem xStar))
    (hγφ_mem : γφ ∈ Set.Ioc (0 : ℝ) 1)
    (hclose :
      ‖method k - xStar‖ ≤
        (2 / (L : ℝ)) * (σ_min(fderiv ℝ problem xStar) * γφ / (3 + 5 * γφ))) :
    0 < σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖method k - xStar‖ := by
  have hL_pos : 0 < (L : ℝ) := lt_of_lt_of_le method.L0_pos method.L0_le_L
  have hγ_pos : 0 < γφ := hγφ_mem.1
  have hden_pos : 0 < 3 + 5 * γφ := by
    nlinarith
  have hscaled :
      (L : ℝ) * ‖method k - xStar‖ ≤ 2 * (σ_min(fderiv ℝ problem xStar) * γφ / (3 + 5 * γφ)) := by
    nlinarith
  have hupper :
      2 * (σ_min(fderiv ℝ problem xStar) * γφ / (3 + 5 * γφ)) <
        σ_min(fderiv ℝ problem xStar) := by
    field_simp [hden_pos.ne']
    nlinarith
  exact sub_pos.mpr (lt_of_le_of_lt hscaled hupper)

-- Semantic recall note: `ContractingWith.dist_le_of_fixedPoint` and
-- `ContractingWith.apriori_dist_iterate_fixedPoint_le` keep contraction estimates as theorem-level
-- API over an existing iteration owner, so this file preserves the source theorem on
-- `ModifiedGaussNewtonMethod` and keeps the displayed inequalities on theorem surfaces.

-- Proof sketch: combine the source assumptions `xStar ∈ 𝓛[f]((f x₀))`, `method k ∈ 𝓛[f]((f x₀))`,
-- `xStar ∈ solutionSet problem`, the convex feasible-domain geometry `Convex ℝ 𝓕`, Assumption
-- 4.4.2 encoded as `IsSufficientlyLargeFeasibleSetAt f 𝓕 x₀`, the Jacobian-Lipschitz control of
-- `problem` on `𝓕` with constant `L`, the sharp lower bound with constant `γφ`, and the primal
-- nondegeneracy owner `0 < σ_min(F'(x*))` to obtain both displayed inequalities in `(4.4.20)`,
-- together with the source conclusion that the next iterate remains in the same initial sublevel
-- set.
/-- Theorem 4.4.2: let `x*` be a nondegenerate exact solution with
`x* ∈ 𝓛[f]((f x₀))` and `x* ∈ solutionSet problem`, let `γφ` be a sharpness witness from
Definition 4.4.9, assume the current iterate `x_k` lies in `𝓛[f]((f x₀))`, and assume the same
displayed constant `L` is a Jacobian-Lipschitz constant for `problem` on a convex feasible set
`𝓕` satisfying Assumption 4.4.2 for the initial merit sublevel set `𝓛[f]((f x₀))`. If
`‖x_k - x*‖ ≤ (2 / L) * (σ γφ / (3 + 5 γφ))`, then the next iterate stays in
`𝓛[f]((f x₀))` and satisfies the explicit quadratic estimate in `(4.4.20)`. The final comparison
of that bound with `‖x_k - x*‖` is recorded separately below. -/
theorem local_contraction_near_nondegenerate_solution
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    {𝓕 : Set E₁}
    {k : ℕ}
    (h𝓕 : Convex ℝ 𝓕)
    (hxStar_level : xStar ∈ 𝓛0)
    (hxStar : xStar ∈ solutionSet problem)
    (hk_level : method k ∈ 𝓛0)
    (hlarge : IsSufficientlyLargeFeasibleSetAt f 𝓕 x0)
    (hJacobianLipschitz : LipschitzOnWith L (fderiv ℝ problem) 𝓕)
    (hσ_pos : 0 < σ_min(fderiv ℝ problem xStar))
    (hγφ_mem : γφ ∈ Set.Ioc (0 : ℝ) 1)
    (hγφ_lower : ∀ u : E₂, γφ * ‖u‖ ≤ φ u)
    (hclose :
      ‖method k - xStar‖ ≤
        (2 / (L : ℝ)) * (σ_min(fderiv ℝ problem xStar) * γφ / (3 + 5 * γφ))) :
    method (k + 1) ∈ 𝓛0 ∧
      ‖method (k + 1) - xStar‖ ≤
        (3 * (1 + γφ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ)) /
          (2 * γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖method k - xStar‖)) := by
  constructor
  · -- The accepted step never increases the merit value, so it stays in the initial sublevel set.
    rw [mem_levelSet_iff]
    rw [mem_levelSet_iff] at hk_level
    exact le_trans
      (le_trans (by simpa [method.x_succ k] using method.step_value_le_modelValue k)
        (method.step_modelValue_le_merit k))
      hk_level
  · have hshift_pos :=
        shiftedSigma_pos_of_close
          (problem := problem) (φ := φ) (L0 := L0) (L := L) (γφ := γφ) (x0 := x0)
          (xStar := xStar) method hσ_pos hγφ_mem hclose
    have hγ_pos : 0 < γφ := hγφ_mem.1
    have hprod :=
      acceptedStepDistance_mul_shiftedSigma_le_rhs
        (problem := problem) (φ := φ) (L0 := L0) (L := L) (γφ := γφ) (x0 := x0) (xStar := xStar)
        method h𝓕 hxStar_level hxStar hk_level hlarge hJacobianLipschitz hσ_pos hγφ_mem hγφ_lower
    have hdivide :
        ‖method (k + 1) - xStar‖ ≤
          ((3 * (1 + γφ) / 2 : ℝ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ)) /
            (γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖method k - xStar‖)) := by
      exact (le_div_iff₀ (mul_pos hγ_pos hshift_pos)).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
    -- Rewrite the coefficient into the textbook denominator shape.
    have hrepack :
        ((3 * (1 + γφ) / 2 : ℝ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ)) /
            (γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖method k - xStar‖)) =
          (3 * (1 + γφ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ)) /
            (2 * γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * ‖method k - xStar‖)) := by
      field_simp [hγ_pos.ne', hshift_pos.ne']
      ring
    simpa [hrepack] using hdivide

-- Proof sketch: starting from the smallness assumption on `‖x_k - x*‖`, rearrange the scalar
-- inequality exactly as in the textbook estimate to show that the fraction appearing in
-- `(4.4.20)` is bounded above by `‖x_k - x*‖`.
/-- Companion to Theorem 4.4.2: under the same nondegenerate smallness regime, the explicit
quadratic error bound from `(4.4.20)` is itself at most the current error `‖x_k - x*‖`. -/
theorem local_contraction_bound_le_current_error
    (method : ModifiedGaussNewtonMethod problem φ L0 (L : ℝ) x0)
    {k : ℕ}
    (hσ_pos : 0 < σ_min(fderiv ℝ problem xStar))
    (hγφ_mem : γφ ∈ Set.Ioc (0 : ℝ) 1)
    (hclose :
      ‖method k - xStar‖ ≤
        (2 / (L : ℝ)) * (σ_min(fderiv ℝ problem xStar) * γφ / (3 + 5 * γφ))) :
    ((3 * (1 + γφ) * (L : ℝ) * ‖method k - xStar‖ ^ (2 : ℕ)) /
        (2 * γφ *
          (σ_min(fderiv ℝ problem xStar) -
            (L : ℝ) * ‖method k - xStar‖)) ≤
      ‖method k - xStar‖) := by
  let r : ℝ := ‖method k - xStar‖
  have hr_nonneg : 0 ≤ r := norm_nonneg _
  have hγ_pos : 0 < γφ := hγφ_mem.1
  have hL_pos : 0 < (L : ℝ) := lt_of_lt_of_le method.L0_pos method.L0_le_L
  have hden_pos : 0 < 3 + 5 * γφ := by
    nlinarith
  have hshift_pos :=
    shiftedSigma_pos_of_close
      (problem := problem) (φ := φ) (L0 := L0) (L := L) (γφ := γφ) (x0 := x0)
      (xStar := xStar) method hσ_pos hγφ_mem hclose
  have hscaled :
      (L : ℝ) * r ≤ 2 * (σ_min(fderiv ℝ problem xStar) * γφ / (3 + 5 * γφ)) := by
    dsimp [r]
    nlinarith
  have hprod :
      (3 + 5 * γφ) * ((L : ℝ) * r) ≤ 2 * σ_min(fderiv ℝ problem xStar) * γφ := by
    have hscaled' :
        (L : ℝ) * r ≤
          (2 * σ_min(fderiv ℝ problem xStar) * γφ) / (3 + 5 * γφ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hscaled
    exact (le_div_iff₀ hden_pos).mp hscaled'
  have hmain :
      3 * (1 + γφ) * (L : ℝ) * r ≤
        2 * γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * r) := by
    nlinarith
  have hnum :
      3 * (1 + γφ) * (L : ℝ) * r ^ (2 : ℕ) ≤
        r * (2 * γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * r)) := by
    exact mul_le_mul_of_nonneg_right hmain hr_nonneg
  have hdiv :
      (3 * (1 + γφ) * (L : ℝ) * r ^ (2 : ℕ)) /
          (2 * γφ * (σ_min(fderiv ℝ problem xStar) - (L : ℝ) * r)) ≤
        r := by
    exact (div_le_iff₀ (mul_pos (show 0 < 2 * γφ by positivity) hshift_pos)).2 <| by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hnum
  simpa [r]
    using hdiv

end
