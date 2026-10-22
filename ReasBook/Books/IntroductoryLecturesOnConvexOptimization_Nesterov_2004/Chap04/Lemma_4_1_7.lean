/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_16
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin CubicRegularizationModelNotation
open scoped Gradient

noncomputable section

universe u

/- Lemma 4.1.7 lies in the chapter's local negative-curvature / cubic-regularization domain on
finite-dimensional real inner-product spaces.

Sampled owner declarations:
* `hessianLeastEigenvalue` and the notation `λ_min(∇² f x)` in `Definition_4_1_6`, the chapter
  owner for the least Hessian spectral value;
* `hessian f x` in `Chap01/Definition_1_4_16`, the intrinsic Hessian operator owner;
* `HessianLipschitzOn` in `Definition_4_1_2`, the chapter owner for local `C²` Hessian-Lipschitz
  regularity on an open convex set;
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the source-facing owner for the accepted
  cubic-regularization iterates.

Source/core/bridge triage:
* source-facing: the local cubic-regularization escape statement near a critical point with
  strictly negative curvature;
* core/canonical: `HessianLipschitzOn L 𝓕 f`, `CubicRegularizationMethod ...`, and the intrinsic
  Hessian operator `hessian f xBar`;
* bridge/view: the negative-curvature witness theorem relating `λ_min(∇² f xBar) < 0` to a unit
  direction with negative Hessian quadratic form.

Primitive data:
* the ambient finite-dimensional real inner-product space `E`;
* the objective `f : E → ℝ`;
* the cubic-regularization method `method`;
* the local regularity owner `HessianLipschitzOn L 𝓕 f`;
* the criticality, domain-membership, and strict negative-curvature hypotheses at `xBar`.

Derived API:
* the unit negative-curvature direction supplied by the least-Hessian-eigenvalue hypothesis;
* the local objective-drop conclusion for iterates inside the upper-level set around `xBar`.

This file therefore keeps the source-facing negative-curvature statement, but moves it from the
textbook coordinate model `ℝⁿ` to the same intrinsic owner layer already used by the adjacent
chapter lemmas instead of preserving a parallel Euclidean-only copy. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Lemma 4.1.7: for a self-adjoint operator, the quadratic form at any unit vector is
bounded below by the bottom of the real spectrum. -/
theorem sInf_spectrum_le_reApplyInnerSelf_of_unit
    {T : E →L[ℝ] E} (hT : IsSelfAdjoint T) {d : E} (hd : ‖d‖ = 1) :
    sInf (spectrum ℝ T) ≤ inner ℝ (T d) d := by
  have hd_mem : d ∈ Metric.sphere (0 : E) 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hd
  have hcompact : IsCompact (Metric.sphere (0 : E) 1) :=
    isCompact_sphere (0 : E) 1
  obtain ⟨x0, hx0, hmin⟩ :=
    hcompact.exists_isMinOn ⟨d, hd_mem⟩ T.reApplyInnerSelf_continuous.continuousOn
  have hx0_norm : ‖x0‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hx0
  have hx0_ne : x0 ≠ 0 := by
    intro hx0_zero
    simp [hx0_zero] at hx0_norm
  have hspec :
      T.rayleighQuotient x0 ∈ spectrum ℝ T := by
    have hmin' : IsMinOn T.reApplyInnerSelf (Metric.sphere (0 : E) ‖x0‖) x0 := by
      simpa [hx0_norm] using hmin
    have hvec :=
      hT.hasEigenvector_of_isLocalExtrOn hx0_ne (Or.inl hmin'.localize)
    have hspec_lin :
        T.rayleighQuotient x0 ∈ spectrum ℝ (T : E →ₗ[ℝ] E) := by
      exact (Module.End.hasEigenvalue_of_hasEigenvector hvec).mem_spectrum
    simpa [ContinuousLinearMap.spectrum_eq] using hspec_lin
  have hsInf_le :
      sInf (spectrum ℝ T) ≤ T.rayleighQuotient x0 :=
    csInf_le (spectrum.isCompact T).bddBelow hspec
  have hrayleigh_le :
      T.rayleighQuotient x0 ≤ inner ℝ (T d) d := by
    calc
      T.rayleighQuotient x0 = T.reApplyInnerSelf x0 := by
        rw [ContinuousLinearMap.rayleighQuotient, ContinuousLinearMap.reApplyInnerSelf_apply,
          hx0_norm]
        ring
      _ = inner ℝ (T x0) x0 := by
        simpa using ContinuousLinearMap.reApplyInnerSelf_apply T x0
      _ ≤ inner ℝ (T d) d := by
        simpa using hmin hd_mem
  exact hsInf_le.trans hrayleigh_le

/-- If `f` is `C²` at `xBar`, then the textbook condition
`λ_min(∇² f(xBar)) < 0` is equivalent to the existence of a unit direction with strictly negative
Hessian quadratic form at `xBar`. -/
theorem hessianLeastEigenvalue_neg_iff_exists_unit_direction
    (f : E → ℝ) (xBar : E) (hf : ContDiffAt ℝ 2 f xBar) :
    λ_min(∇² f xBar) < 0 ↔
      ∃ d : E, ‖d‖ = 1 ∧ inner ℝ (hessian f xBar d) d < 0 := by
  constructor
  · intro hneg
    -- Convert the spectral negativity hypothesis into a contradiction with positivity.
    by_contra hnot
    have hselfAdjoint : IsSelfAdjoint (hessian f xBar) := by
      simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
    have hs_nonempty : (spectrum ℝ (hessian f xBar)).Nonempty := by
      by_contra hs
      have hs' : spectrum ℝ (hessian f xBar) = ∅ := Set.not_nonempty_iff_eq_empty.mp hs
      simp [hessianLeastEigenvalue, hs'] at hneg
    have hquad_nonneg : ∀ z : E, 0 ≤ inner ℝ (hessian f xBar z) z := by
      intro z
      by_cases hz : z = 0
      · simp [hz]
      · let u : E := ‖z‖⁻¹ • z
        have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
        have hu_unit : ‖u‖ = 1 := by
          simp [u, norm_smul, hnorm_pos.ne']
        have hu_nonneg : 0 ≤ inner ℝ (hessian f xBar u) u := by
          by_contra hu_neg
          exact hnot ⟨u, hu_unit, lt_of_not_ge hu_neg⟩
        have hu_eq :
            inner ℝ (hessian f xBar u) u =
              (‖z‖⁻¹ : ℝ) * ((‖z‖⁻¹ : ℝ) * inner ℝ (hessian f xBar z) z) := by
          simp [u, inner_smul_left, inner_smul_right]
        rw [hu_eq] at hu_nonneg
        have hfactor_pos : 0 < (‖z‖⁻¹ : ℝ) * ‖z‖⁻¹ := by
          positivity
        nlinarith
    have hpositive : (hessian f xBar).IsPositive := by
      exact (ContinuousLinearMap.isPositive_iff' _).2 ⟨hselfAdjoint, hquad_nonneg⟩
    have hsInf_nonneg : 0 ≤ sInf (spectrum ℝ (hessian f xBar)) := by
      refine le_csInf hs_nonempty ?_
      intro μ hμ
      have hhess_nonneg : 0 ≤ hessian f xBar := by
        exact (ContinuousLinearMap.nonneg_iff_isPositive _).2 hpositive
      exact spectrum_nonneg_of_nonneg hhess_nonneg hμ
    linarith [hneg, hsInf_nonneg]
  · rintro ⟨d, hd, hdneg⟩
    -- A negative quadratic value at a unit vector bounds the bottom of the spectrum above by a
    -- negative number.
    have hselfAdjoint : IsSelfAdjoint (hessian f xBar) := by
      simpa using (fderiv_gradient_isSymmetric_of_contDiffAt hf).isSelfAdjoint
    have hsInf_le :
        sInf (spectrum ℝ (hessian f xBar)) ≤ inner ℝ (hessian f xBar d) d :=
      sInf_spectrum_le_reApplyInnerSelf_of_unit hselfAdjoint hd
    simpa [hessianLeastEigenvalue] using lt_of_le_of_lt hsInf_le hdneg

/-- Helper for Lemma 4.1.7: along a unit direction whose Hessian quadratic form at `xBar` equals
`-2σ`, the local second-order Taylor model yields a quadratic decrease dominated by the cubic
Taylor remainder. -/
lemma objective_le_along_negative_curvature_direction
    {f : E → ℝ} {𝓕 : Set E} {L : NNReal} {xBar d : E} {τ σ : ℝ}
    (hreg : HessianLipschitzOn L 𝓕 f)
    (hxBar : xBar ∈ 𝓕)
    (hy : xBar + τ • d ∈ 𝓕)
    (hgrad : ∇ f xBar = 0)
    (hd : ‖d‖ = 1)
    (hτ : 0 ≤ τ)
    (hcurv : inner ℝ (hessian f xBar d) d = -2 * σ) :
    f (xBar + τ • d) ≤
      f xBar - σ * τ ^ (2 : ℕ) + ((L : ℝ) / 6) * τ ^ (3 : ℕ) := by
  -- First bound the objective by the quadratic Taylor model plus the cubic Lipschitz remainder.
  have herror := hreg.secondOrderTaylorModel_error_le xBar (xBar + τ • d) hxBar hy
  have hupper :
      f (xBar + τ • d) ≤
        secondOrderTaylorModelAt f xBar (xBar + τ • d) +
          ((L : ℝ) / 6) * ‖(xBar + τ • d) - xBar‖ ^ (3 : ℕ) := by
    have hright := (abs_le.mp herror).2
    linarith
  have hmodel :
      secondOrderTaylorModelAt f xBar (xBar + τ • d) =
        f xBar - σ * τ ^ (2 : ℕ) := by
    -- Stationarity removes the linear term, and the Hessian quadratic term is `-σ τ²`.
    rw [secondOrderTaylorModelAt_apply, hgrad]
    simp [hcurv, inner_smul_left, inner_smul_right, mul_assoc, mul_comm]
    ring
  have hnorm : ‖(xBar + τ • d) - xBar‖ = τ := by
    -- The chosen direction is a unit vector, so the displacement norm is exactly `τ`.
    calc
      ‖(xBar + τ • d) - xBar‖ = ‖τ • d‖ := by
        abel_nf
      _ = τ := by
        rw [norm_smul, Real.norm_of_nonneg hτ, hd, mul_one]
  calc
    f (xBar + τ • d)
        ≤ secondOrderTaylorModelAt f xBar (xBar + τ • d) +
            ((L : ℝ) / 6) * ‖(xBar + τ • d) - xBar‖ ^ (3 : ℕ) := hupper
    _ = f xBar - σ * τ ^ (2 : ℕ) + ((L : ℝ) / 6) * τ ^ (3 : ℕ) := by
      rw [hmodel, hnorm]

/-- Helper for Lemma 4.1.7: the accepted next iterate is bounded above by every feasible
comparison point through the owner-level cubic-model comparison. -/
lemma CubicRegularizationMethod.objective_succ_le_feasible_comparison
    {f : E → ℝ} {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal} {x0 y : E} {𝓕 : Set E}
    (method : CubicRegularizationMethod f stepMap L0 (L : ℝ) x0)
    (hreg : HessianLipschitzOn L 𝓕 f)
    {i : ℕ}
    (hxi : method i ∈ 𝓕)
    (hy : y ∈ 𝓕) :
    f (method (i + 1)) ≤
      f y + ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ) := by
  -- The accepted step controls the next objective value by the cubic model value.
  have hstep :
      f (method (i + 1)) ≤ f̄[f; (method.regularization i)]((method i)) := by
    simpa [method.x_succ i, method.step_apply_eq_stepMap i (method i)] using
      method.objective_step_le_value i
  have hcomp :
      f̄[f; (method.regularization i)]((method i)) ≤
        f y + ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ) := by
    -- Then compare the same cubic model value to the feasible trial point `y`.
    simpa using
      cubicRegularizationValue_le_feasibleComparison_of_mem
        (trialPoint := stepMap (method.regularization i) (method i))
        hreg
        (method.stepMap_isMinOn i)
        hxi
        hy
  exact hstep.trans hcomp

-- Proof sketch: choose a unit negative-curvature direction from `hneg` and use the open convex
-- regularity neighborhood `𝓕` from `hreg` together with `hxBar` to shrink to a ball around
-- `xBar` on which the local Hessian-Lipschitz owner hypotheses hold, derive
-- the needed cubic Taylor upper bound from `hreg.contDiffOn` and `hreg.lipschitz` via
-- Lemma 4.1.1, and for a point `x_i` in the upper level set around `xBar` compare the accepted
-- cubic-regularization step to the trial points `xBar ± ε d`. Choose the sign so that the
-- distance to `x_i` is controlled, use the Taylor upper bound at the moving base point `x_i`
-- together with the owner-level bound
-- `cubicRegularizationValue_le_quadraticApproximation`, and then shrink `ε` so the quadratic
-- decrease dominates the cubic remainder.
/-- Lemma 4.1.7: near a critical point with strictly negative Hessian curvature, a cubic
regularization method admits constants `ε > 0` and `δ > 0` such that, if `xBar` is an interior
point of an open convex neighborhood `𝓕` on which the Hessian is `L`-Lipschitz, then any
iterate in the local upper-level set
`Q = {x | ‖x - xBar‖ ≤ ε ∧ f xBar ≤ f x}` has its next iterate strictly below the level
`f xBar - δ`. Since `HessianLipschitzOn L 𝓕 f` already records that `𝓕` is open, this uses the
same single local domain for both regularity and interior feasibility. -/
theorem exists_objective_drop_below_negative_curvature_level
    {f : E → ℝ} {stepMap : ℝ → E → E} {L0 : ℝ} {L : NNReal} {x0 xBar : E} {𝓕 : Set E}
    (method :
      CubicRegularizationMethod
        f
        stepMap
        L0 (L : ℝ) x0)
    (hgrad : ∇ f xBar = 0)
    (hxBar : xBar ∈ 𝓕)
    (hreg : HessianLipschitzOn L 𝓕 f)
    (hneg : λ_min(∇²f xBar) < 0) :
    ∃ ε > 0, ∃ δ > 0, ∀ i : ℕ,
      method i ∈ Metric.closedBall xBar ε ∩ {x | f xBar ≤ f x} →
        f (method (i + 1)) ≤ f xBar - δ := by
  -- Extract a unit direction with negative Hessian quadratic form at the saddle/maximizer.
  rcases (hessianLeastEigenvalue_neg_iff_exists_unit_direction f xBar (hreg.contDiffAt hxBar)).mp
      hneg with ⟨d, hd, hdneg⟩
  -- Use openness of `𝓕` to choose a ball around `xBar` contained in the regularity region.
  obtain ⟨r, hrpos, hrball⟩ := Metric.isOpen_iff.mp hreg.isOpen xBar hxBar
  let σ : ℝ := -(inner ℝ (hessian f xBar d) d) / 2
  have hσpos : 0 < σ := by
    dsimp [σ]
    linarith
  have hcurv : inner ℝ (hessian f xBar d) d = -2 * σ := by
    dsimp [σ]
    ring
  let ε : ℝ := min (r / 2) (3 * σ / (25 * ((L : ℝ) + 1)))
  have hεpos : 0 < ε := by
    refine lt_min ?_ ?_
    · linarith
    · positivity
  have hε_lt_r : ε < r := by
    have hrhalf_lt : r / 2 < r := by
      linarith
    exact lt_of_le_of_lt (min_le_left _ _) hrhalf_lt
  let δ : ℝ := (σ / 2) * ε ^ (2 : ℕ)
  refine ⟨ε, hεpos, δ, ?_, ?_⟩
  · -- The final objective drop is strictly positive because both `σ` and `ε` are positive.
    dsimp [δ]
    positivity
  · intro i hi
    let y : E := xBar + ε • d
    have hxi_norm : ‖method i - xBar‖ ≤ ε := by
      simpa [Metric.mem_closedBall, dist_eq_norm, dist_comm] using hi.1
    have hxi_mem : method i ∈ 𝓕 := by
      exact hrball (lt_of_le_of_lt (by simpa [dist_eq_norm, dist_comm] using hxi_norm) hε_lt_r)
    have hy_mem : y ∈ 𝓕 := by
      refine hrball ?_
      dsimp [y]
      calc
        dist (xBar + ε • d) xBar = ‖(xBar + ε • d) - xBar‖ := by
          rw [dist_eq_norm]
        _ = ε := by
          calc
            ‖(xBar + ε • d) - xBar‖ = ‖ε • d‖ := by
              abel_nf
            _ = ε := by
              rw [norm_smul, Real.norm_of_nonneg hεpos.le, hd, mul_one]
        _ < r := hε_lt_r
    have hstep := method.objective_succ_le_feasible_comparison hreg hxi_mem hy_mem
    have hdir := objective_le_along_negative_curvature_direction
      hreg hxBar hy_mem hgrad hd hεpos.le hcurv
    have hy_dist : ‖y - xBar‖ = ε := by
      dsimp [y]
      calc
        ‖(xBar + ε • d) - xBar‖ = ‖ε • d‖ := by
          abel_nf
        _ = ε := by
          rw [norm_smul, Real.norm_of_nonneg hεpos.le, hd, mul_one]
    have hdist_yi : ‖y - method i‖ ≤ 2 * ε := by
      -- Both `y` and `method i` lie in the `ε`-ball around `xBar`, so their distance is at most
      -- `2ε`.
      calc
        ‖y - method i‖ = ‖(y - xBar) + (xBar - method i)‖ := by
          abel_nf
        _ ≤ ‖y - xBar‖ + ‖xBar - method i‖ := norm_add_le _ _
        _ ≤ ε + ε := by
          gcongr
          · exact le_of_eq hy_dist
          · simpa [norm_sub_rev] using hxi_norm
        _ = 2 * ε := by
          ring
    have hcoeff_le : ((((L : ℝ) + method.regularization i) / 6) : ℝ) ≤ (L : ℝ) / 2 := by
      nlinarith [method.regularization_le_two_mul_L i]
    have hcoeff_nonneg : 0 ≤ ((((L : ℝ) + method.regularization i) / 6) : ℝ) := by
      nlinarith [method.regularization_pos i, show 0 ≤ (L : ℝ) by exact_mod_cast L.2]
    have hcube_le :
        ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ) ≤
          4 * (L : ℝ) * ε ^ (3 : ℕ) := by
      have hpow_le : ‖y - method i‖ ^ (3 : ℕ) ≤ (2 * ε) ^ (3 : ℕ) := by
        gcongr
      -- The one-step comparison term is controlled by the coarse radius bound `‖y - x_i‖ ≤ 2ε`.
      have hfirst :
          ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ) ≤
            ((((L : ℝ) + method.regularization i) / 6) : ℝ) * (2 * ε) ^ (3 : ℕ) := by
        nlinarith
      calc
        ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ)
            ≤ ((((L : ℝ) + method.regularization i) / 6) : ℝ) * (2 * ε) ^ (3 : ℕ) := hfirst
        _ ≤ ((L : ℝ) / 2) * (2 * ε) ^ (3 : ℕ) := by
              gcongr
        _ = 4 * (L : ℝ) * ε ^ (3 : ℕ) := by
              ring
    have hsmall : ((25 : ℝ) / 6) * (L : ℝ) * ε ≤ σ / 2 := by
      have hε_small : ε ≤ 3 * σ / (25 * ((L : ℝ) + 1)) := min_le_right _ _
      have hdenom_pos : 0 < 25 * ((L : ℝ) + 1) := by
        positivity
      have hsmall_aux : (25 * ((L : ℝ) + 1)) * ε ≤ 3 * σ := by
        simpa [mul_assoc, mul_comm, mul_left_comm] using (le_div_iff₀ hdenom_pos).mp hε_small
      have hL_le : (L : ℝ) ≤ (L : ℝ) + 1 := by
        linarith
      nlinarith
    have hsmall_cube :
        ((25 : ℝ) / 6) * (L : ℝ) * ε ^ (3 : ℕ) ≤ (σ / 2) * ε ^ (2 : ℕ) := by
      nlinarith [hsmall, show 0 ≤ ε by linarith]
    -- Combine the feasible-comparison inequality with the negative-curvature Taylor estimate and
    -- the smallness choice of `ε`.
    calc
      f (method (i + 1))
          ≤ f y + ((((L : ℝ) + method.regularization i) / 6) : ℝ) * ‖y - method i‖ ^ (3 : ℕ) :=
            hstep
      _ ≤ (f xBar - σ * ε ^ (2 : ℕ) + ((L : ℝ) / 6) * ε ^ (3 : ℕ)) +
            4 * (L : ℝ) * ε ^ (3 : ℕ) := by
              gcongr
      _ = f xBar - σ * ε ^ (2 : ℕ) + ((25 : ℝ) / 6) * (L : ℝ) * ε ^ (3 : ℕ) := by
              ring
      _ ≤ f xBar - δ := by
              dsimp [δ]
              nlinarith
