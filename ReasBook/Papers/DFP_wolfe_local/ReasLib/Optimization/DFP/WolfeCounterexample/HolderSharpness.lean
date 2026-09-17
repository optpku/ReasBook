/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.WolfeCounterexample.Holder
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.StepDescent.StepNorm
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleAsymptotics

/-!
# Sharpness of the one-half Hölder Hessian exponent

The even secant residual is first order in the small orbit parameter, whereas
the physical step is quadratic in that parameter. A Hölder Taylor remainder
with exponent greater than one half is incompatible with these two facts.
-/

public section

open Filter
open scoped Topology

namespace DFP.PlanarConvergence

/-- Helper for eq:counterexample-nonlipschitz: a residual of size `εₖ ℓₖ`
with positive steps `ℓₖ ≤ D εₖ²` rules out a remainder of order `1 + β`
when `β > 1/2`. Only an upper step bound is needed. -/
theorem not_holderRemainder_of_quadraticStepBound
    {ε ell : ℕ → ℝ} {β C D : ℝ}
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ k, 0 < ε k)
    (hellpos : ∀ k, 0 < ell k) (hD : 0 < D) (hC : 0 < C)
    (hβ : 1 / 2 < β) (hstep : ∀ k, ell k ≤ D * (ε k) ^ 2)
    (hresidual : ∀ k, ε k * ell k ≤ C * (ell k) ^ (1 + β)) : False := by
  have hβpos : 0 < β := by linarith
  have hδ : 0 < 2 * β - 1 := by linarith
  have hlimit : Tendsto (fun k ↦ C * D ^ β * (ε k) ^ (2 * β - 1)) atTop (𝓝 0) := by
    have hpower := hε.rpow tendsto_const_nhds (Or.inr hδ)
    simpa only [Real.zero_rpow hδ.ne', mul_zero] using hpower.const_mul (C * D ^ β)
  have hlower (k : ℕ) : 1 ≤ C * D ^ β * (ε k) ^ (2 * β - 1) := by
    have hcancel : ε k ≤ C * (ell k) ^ β := by
      have h := hresidual k
      rw [Real.rpow_add (hellpos k), Real.rpow_one] at h
      apply le_of_mul_le_mul_right _ (hellpos k)
      nlinarith only [h]
    have hpow : (D * (ε k) ^ 2) ^ β = D ^ β * (ε k) ^ (2 * β) := by
      rw [Real.mul_rpow hD.le (sq_nonneg _), ← Real.rpow_natCast,
        ← Real.rpow_mul (hεpos k).le]
      norm_num
    have hupper : ε k ≤ C * (D ^ β * (ε k) ^ (2 * β)) := by
      rw [← hpow]
      exact hcancel.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hellpos k).le (hstep k) hβpos.le) hC.le)
    have hsplit : (ε k) ^ (2 * β) = ε k * (ε k) ^ (2 * β - 1) := by
      rw [Real.rpow_sub (hεpos k), Real.rpow_one]
      field_simp [(hεpos k).ne']
    rw [hsplit] at hupper
    apply le_of_mul_le_mul_left _ (hεpos k)
    nlinarith only [hupper]
  have hbad : (1 : ℝ) ≤ 0 := ge_of_tendsto hlimit (Eventually.of_forall hlower)
  norm_num at hbad

/-- Helper for eq:counterexample-nonlipschitz: exact secant residuals of the
counterexample prohibit a Hölder Hessian of exponent greater than one half
on any convex set containing the secant endpoints. -/
theorem not_hessianHolderOn_of_secantResidual
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) {K : Set E} (hK : Convex ℝ K)
    {x y : ℕ → E} {ε : ℕ → ℝ} {D β : ℝ}
    (hx : ∀ k, x k ∈ K) (hy : ∀ k, y k ∈ K)
    (hε : Tendsto ε atTop (𝓝 0)) (hεpos : ∀ k, 0 < ε k)
    (hstepPos : ∀ k, 0 < ‖y k - x k‖) (hD : 0 < D)
    (hstep : ∀ k, ‖y k - x k‖ ≤ D * (ε k) ^ 2)
    (hresidual : ∀ k,
      ‖gradient f (y k) - gradient f (x k) - hessian f (x k) (y k - x k)‖ =
        ε k * ‖y k - x k‖) (hβ : 1 / 2 < β) :
    ¬ ∃ C > 0, ∀ u ∈ K, ∀ v ∈ K,
      ‖hessian f u - hessian f v‖ ≤ C * ‖u - v‖ ^ β := by
  rintro ⟨C, hC, hHolder⟩
  have hdiff : Differentiable ℝ (gradient f) :=
    (hf.gradient_succ (n := 1)).differentiable_one
  have hβnonneg : 0 ≤ β := by linarith
  apply not_holderRemainder_of_quadraticStepBound hε hεpos hstepPos hD hC hβ hstep
  intro k
  have hderiv (z : E) (hz : z ∈ segment ℝ (x k) (y k)) :
      ‖fderiv ℝ (gradient f) z - fderiv ℝ (gradient f) (x k)‖ ≤
        C * ‖z - x k‖ ^ β := by
    simpa only [hessian_def] using hHolder z (hK.segment_subset (hx k) (hy k) hz) (x k) (hx k)
  have hdifferentiable (z : E) (_hz : z ∈ segment ℝ (x k) (y k)) := hdiff z
  have hbound := norm_firstOrderRemainder_le_of_holderDerivative
    hC.le hβnonneg hdifferentiable hderiv
  rw [← hessian_def, hresidual k] at hbound
  exact hbound

end DFP.PlanarConvergence

namespace AffineBump

/-- Helper for eq:endpoint-data: an affine linear function has zero Hessian. -/
theorem hessian_affineInner {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (a x z : E) :
    hessian (fun y ↦ inner ℝ a (y - x)) z = 0 := by
  have hderiv : fderiv ℝ (fun y ↦ inner ℝ a (y - x)) = fun _ ↦ innerSL ℝ a := by
    funext y
    have h := (innerSL ℝ a).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x)
    simpa only [ContinuousLinearMap.comp_id, Function.comp_def, id_eq,
      innerSL_apply_apply] using h.fderiv
  rw [hessian_def]
  unfold gradient
  rw [hderiv]
  simp only [fderiv_fun_const]
  rfl

/-- Helper for eq:endpoint-data: a scaled bump whose cutoff is locally one
agrees with its linear part near the center. -/
theorem scaledLinearBump_eventuallyEq_affineInner
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (χ : E → ℝ) (hχ : χ =ᶠ[𝓝 0] fun _ ↦ 1) (x a : E) (ρ : ℝ) :
    scaledLinearBump χ x ρ a =ᶠ[𝓝 x] fun y ↦ inner ℝ a (y - x) := by
  have hlim : Tendsto (fun y : E ↦ ρ⁻¹ • (y - x)) (𝓝 x) (𝓝 0) := by
    have hcont : Continuous (fun y : E ↦ ρ⁻¹ • (y - x)) := by fun_prop
    simpa only [sub_self, smul_zero] using hcont.tendsto x
  filter_upwards [hlim.eventually hχ] with y hy
  rw [scaledLinearBump_apply, hy, one_mul]

end AffineBump

namespace DFP.TwoPhaseOrbit

/-- Helper for eq:endpoint-data: disjoint interpolation bumps have zero Hessian
at every interpolation center, since their cutoff is locally constant there. -/
theorem bumpCorrection_hessian_endpoint (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (hρ : ∀ k, 0 < orbit.interpolationRadius C G k)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k))) (k : ℕ) :
    hessian (orbit.bumpCorrection C G) (orbit.endpoint k) = 0 := by
  have hlocal := DisjointFinsum.finsum_eq_eventuallyEq_at_center_of_pairwiseDisjoint_closedBall
    orbit.endpoint (orbit.interpolationRadius C G) (orbit.endpointBump C G)
    hρ hballs (orbit.endpointBump_tsupport_subset_interpolationClosedBall C G hρ) k
  have hcutoff : EuclideanPlane.smoothCutoff =ᶠ[𝓝 0] fun _ ↦ 1 := by
    have hthird : (0 : ℝ) < 1 / 3 := by norm_num
    filter_upwards [Metric.closedBall_mem_nhds (0 : EuclideanSpace ℝ (Fin 2)) hthird] with z hz
    exact EuclideanPlane.smoothCutoff_eq_one z hz
  have hbump := AffineBump.scaledLinearBump_eventuallyEq_affineInner
    EuclideanPlane.smoothCutoff hcutoff (orbit.endpoint k) (orbit.endpointCorrection C k)
    (orbit.interpolationRadius C G k)
  rw [← orbit.endpointBump_eq_scaledLinearBump C G k] at hbump
  have hcorrection : orbit.bumpCorrection C G =ᶠ[𝓝 (orbit.endpoint k)]
      fun y ↦ inner ℝ (orbit.endpointCorrection C k) (y - orbit.endpoint k) := by
    have heq : orbit.bumpCorrection C G = fun y ↦ ∑ᶠ j, orbit.endpointBump C G j y := by
      funext y
      exact orbit.bumpCorrection_apply C G y
    rw [heq]
    exact hlocal.trans hbump
  rw [hessian_def, hcorrection.gradient.fderiv_eq, ← hessian_def]
  exact AffineBump.hessian_affineInner _ _ _

/-- Helper for eq:endpoint-data: the Hessian of the realized objective at an
interpolation endpoint is exactly the identity operator. -/
theorem realizedObjective_hessian_endpoint (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (hΨ : ContDiff ℝ 2 (orbit.bumpCorrection C G))
    (hρ : ∀ k, 0 < orbit.interpolationRadius C G k)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k))) (k : ℕ) :
    hessian (orbit.realizedObjective C G) (orbit.endpoint k) = 1 := by
  have heq : orbit.realizedObjective C G =
      fun z ↦ (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + orbit.bumpCorrection C G z := by
    funext z
    exact orbit.realizedObjective_apply C G z
  rw [heq, hessian_def, HessianPerturbation.fderiv_gradient_halfNormSq_sub_add
    C (orbit.bumpCorrection C G) _ hΨ, ← hessian_def,
    orbit.bumpCorrection_hessian_endpoint C G hρ hballs k, add_zero]

/-- Helper for eq:counterexample-nonlipschitz: the physical even-step secant
residual has norm exactly `εⱼ` times the physical step norm. -/
theorem evenSecantResidualNorm (orbit : DFP.TwoPhaseOrbit) (j : ℕ)
    (h : State.ExactCycle (orbit.state j)) :
    ‖orbit.endpointGradient (2 * j + 1) - orbit.endpointGradient (2 * j) -
        (orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j))‖ =
      (orbit.state j).ε * ‖orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j)‖ := by
  have hA : (h.step 0).secantMatrix =
      !![1, (orbit.state j).ε; (orbit.state j).ε, 1] := by
    rw [h.step_secantMatrix_eq_phase, TwoPhaseControls.phase_zero, TwoPhaseControls.first_matrix]
  have hgradient := orbit.endpointGradient_eq_exactStepTransport j 0 h
  have hnext := orbit.endpointGradient_succ_eq_exactStepTransport j 0 h
  have hstep := orbit.endpointStep_eq_exactStepTransport j 0 h
  simp only [Fin.val_zero, Nat.add_zero] at hgradient hnext hstep
  rw [hgradient, hnext, hstep, ← WithLp.toLp_sub, ← WithLp.toLp_sub,
    ← Matrix.mulVec_sub, ← Matrix.mulVec_sub]
  rw [Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    _ (h.valid.phaseFrame_mem_specialOrthogonal 0),
    Matrix.norm_toLp_mulVec_eq_of_mem_specialOrthogonalGroup
    _ (h.valid.phaseFrame_mem_specialOrthogonal 0)]
  have hnextSub : (h.step 0).nextGradient - (h.step 0).gradient =
      (h.step 0).gradientChange := by
    rw [(h.step 0).nextGradient_def]
    abel
  rw [hnextSub, PlanarConvergence.abstractSecantResidualNorm _ hA,
    abs_of_pos h.valid.ε_pos]

/-- Helper for eq:counterexample-nonlipschitz: the concrete realized objective
cannot have a Hölder Hessian of exponent greater than one half on a convex
set containing its endpoints, whenever the physical steps are bounded by
a constant times the squares of the vanishing orbit scales. -/
theorem realizedObjective_not_hessianHolderOn (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (G : ℝ)
    (hΨ : ContDiff ℝ 2 (orbit.bumpCorrection C G))
    (hρ : ∀ k, 0 < orbit.interpolationRadius C G k)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦
      Metric.closedBall (orbit.endpoint k) (orbit.interpolationRadius C G k)))
    (hExact : ∀ j, State.ExactCycle (orbit.state j))
    (hScale : Tendsto (fun j ↦ (orbit.state j).ε) atTop (𝓝 0))
    {D β : ℝ} (hD : 0 < D)
    (hStep : ∀ j, 0 < ‖orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j)‖ ∧
      ‖orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j)‖ ≤ D * (orbit.state j).ε ^ 2)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : Convex ℝ K)
    (hmem : ∀ k, orbit.endpoint k ∈ K) (hβ : 1 / 2 < β) :
    ¬ ∃ L > 0, ∀ u ∈ K, ∀ v ∈ K,
      ‖hessian (orbit.realizedObjective C G) u - hessian (orbit.realizedObjective C G) v‖ ≤
        L * ‖u - v‖ ^ β := by
  have hf : ContDiff ℝ 2 (orbit.realizedObjective C G) := by
    have heq : orbit.realizedObjective C G =
        fun z ↦ (1 / 2 : ℝ) * ‖z - C‖ ^ 2 + orbit.bumpCorrection C G z := by
      funext z
      exact orbit.realizedObjective_apply C G z
    rw [heq]
    have hquad : ContDiff ℝ 2 (fun z : EuclideanSpace ℝ (Fin 2) ↦ ‖z - C‖ ^ 2) :=
      (contDiff_id.sub contDiff_const).norm_sq ℝ
    exact (contDiff_const.mul hquad).add hΨ
  have hεpos (j : ℕ) : 0 < (orbit.state j).ε := (hExact j).valid.ε_pos
  have hresidual (j : ℕ) :
      ‖gradient (orbit.realizedObjective C G) (orbit.endpoint (2 * j + 1)) -
          gradient (orbit.realizedObjective C G) (orbit.endpoint (2 * j)) -
          hessian (orbit.realizedObjective C G) (orbit.endpoint (2 * j))
            (orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j))‖ =
        (orbit.state j).ε * ‖orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j)‖ := by
    rw [(orbit.realizedObjective_hasEndpointGradientAt C G hρ hballs (2 * j + 1)).gradient,
      (orbit.realizedObjective_hasEndpointGradientAt C G hρ hballs (2 * j)).gradient,
      orbit.realizedObjective_hessian_endpoint C G hΨ hρ hballs (2 * j), one_apply_eq_self]
    exact orbit.evenSecantResidualNorm j (hExact j)
  exact PlanarConvergence.not_hessianHolderOn_of_secantResidual hf hK
    (fun j ↦ hmem (2 * j)) (fun j ↦ hmem (2 * j + 1)) hScale hεpos
    (fun j ↦ (hStep j).1) hD (fun j ↦ (hStep j).2) hresidual hβ

end DFP.TwoPhaseOrbit

namespace DFP.TwoLeg.SlowCurve

/-- Helper for eq:counterexample-nonlipschitz: sufficiently small realizations
of an invariant slow curve have a globally one-half Hölder Hessian and no
larger Hölder exponent on any convex set containing their endpoints. -/
theorem realizedObjectiveHolderSharp (curve : DFP.TwoLeg.SlowCurve) :
    ∃ η ∈ Set.Ioo (0 : ℝ) (1 / 4), ∀ ε₀ ∈ Set.Ioc 0 η,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
      ∀ Clim, Tendsto (fun j : ℕ ↦ (orbit.state j).center) atTop (𝓝 Clim) →
        ∀ Glim > 0, Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) →
          (∃ L > 0, ∀ u v,
            ‖hessian (orbit.realizedObjective Clim Glim) u -
                hessian (orbit.realizedObjective Clim Glim) v‖ ≤ L * ‖u - v‖ ^ (1 / 2 : ℝ)) ∧
          ∀ K : Set (EuclideanSpace ℝ (Fin 2)), Convex ℝ K →
            (∀ k, orbit.endpoint k ∈ K) → ∀ β : ℝ, 1 / 2 < β →
              ¬ ∃ L > 0, ∀ u ∈ K, ∀ v ∈ K,
                ‖hessian (orbit.realizedObjective Clim Glim) u -
                    hessian (orbit.realizedObjective Clim Glim) v‖ ≤ L * ‖u - v‖ ^ β := by
  obtain ⟨ηH, hηH, L, hL, hHolder⟩ := DFP.PlanarConvergence.realizedObjectiveHessianHolder curve
  obtain ⟨ηΨ, hηΨ, hSmooth⟩ := curve.bumpCorrectionContDiffTwoAndZeroJets
  obtain ⟨ηρ, hηρ, hRadius⟩ := curve.interpolationRadius_pos
  obtain ⟨ηB, hηB, hBalls⟩ := curve.pairwiseDisjointInterpolationClosedBalls
  have heighth : (1 / 8 : ℝ) ∈ Set.Ioo 0 (1 / 4) := by norm_num
  obtain ⟨ηE, hηE, hExact⟩ := DFP.TwoPhaseOrbit.ofSlowCurveExact curve.shape curve.high
    curve.isInvariant curve.shapeRemainder curve.highRemainder (1 / 8) heighth
  obtain ⟨ηS, hηS, hScale⟩ := curve.stateScaleTendstoZero
  obtain ⟨ηStep, hηStep, c, hc, D, hD, hStep⟩ := curve.phaseStepNormUniformBounds
  let η := min ηH (min ηΨ (min ηρ (min ηB (min ηE (min ηS ηStep)))))
  have hηpos : 0 < η :=
    lt_min hηH.1 (lt_min hηΨ.1 (lt_min hηρ.1
      (lt_min hηB.1 (lt_min hηE.1 (lt_min hηS.1 hηStep.1)))))
  have hηlt : η < 1 / 4 := (min_le_left _ _).trans_lt hηH.2
  refine ⟨η, ⟨hηpos, hηlt⟩, ?_⟩
  intro ε₀ hε₀
  dsimp only
  intro Clim hClim Glim hGlim hGlimLimit
  have hle := hε₀.2
  simp only [η, le_min_iff] at hle
  obtain ⟨hεH, hεΨ, hερ, hεB, hεE, hεS, hεStep⟩ := hle
  let orbit := DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀
  have hΨ : ContDiff ℝ 2 (orbit.bumpCorrection Clim Glim) :=
    (hSmooth ε₀ ⟨hε₀.1, hεΨ⟩ Clim hClim Glim hGlim hGlimLimit).1
  have hρ := hRadius ε₀ ⟨hε₀.1, hερ⟩ Clim hClim Glim hGlim hGlimLimit
  have hballs := hBalls ε₀ ⟨hε₀.1, hεB⟩ Clim hClim Glim hGlim hGlimLimit
  have hexact := hExact ε₀ ⟨hε₀.1, hεE⟩
  have hscale := hScale ε₀ ⟨hε₀.1, hεS⟩
  have hsteps (j : ℕ) :
      0 < ‖orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j)‖ ∧
        ‖orbit.endpoint (2 * j + 1) - orbit.endpoint (2 * j)‖ ≤ D * (orbit.state j).ε ^ 2 := by
    have hraw := hStep ε₀ ⟨hε₀.1, hεStep⟩ j 0
    simp only [Fin.val_zero, Nat.add_zero, DFP.TwoPhaseOrbit.endpointRadius_even] at hraw
    have hlower : 0 < c * (orbit.state j).ε ^ 2 :=
      mul_pos hc (sq_pos_of_pos (hexact j).valid.ε_pos)
    exact ⟨hlower.trans_le hraw.1, hraw.2⟩
  constructor
  · refine ⟨L, hL, ?_⟩
    simpa only [hessian_def, EuclideanPlane.hessian_def] using
      hHolder ε₀ ⟨hε₀.1, hεH⟩ Clim hClim Glim hGlim hGlimLimit
  · intro K hK hmem β hβ
    exact orbit.realizedObjective_not_hessianHolderOn Clim Glim hΨ hρ hballs
      hexact hscale hD hsteps hK hmem hβ

end DFP.TwoLeg.SlowCurve

namespace DFP

/-- Helper for thm:main: the planar strong-Wolfe counterexample has exact
Hölder exponent one half, already on its initial objective sublevel. -/
theorem existsPlanarStrongWolfeCounterexampleHolderSharp
    {c₁ c₂ : ℝ} (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ∃ c : StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) c₁ c₂,
      (∃ L > 0, ∀ u v,
        ‖hessian c.iteration.objective u - hessian c.iteration.objective v‖ ≤
          L * ‖u - v‖ ^ (1 / 2 : ℝ)) ∧
      ∀ β : ℝ, 1 / 2 < β → ¬ ∃ L > 0,
        ∀ u ∈ objectiveSublevel c.iteration, ∀ v ∈ objectiveSublevel c.iteration,
          ‖hessian c.iteration.objective u - hessian c.iteration.objective v‖ ≤
            L * ‖u - v‖ ^ β := by
  obtain ⟨c, hHolder, hSharp⟩ := existsPlanarStrongWolfeCounterexampleWithProperty
    (fun f x ↦
      (∃ L > 0, ∀ u v, ‖hessian f u - hessian f v‖ ≤ L * ‖u - v‖ ^ (1 / 2 : ℝ)) ∧
      ∀ K : Set (EuclideanSpace ℝ (Fin 2)), Convex ℝ K → (∀ k, x k ∈ K) →
        ∀ β : ℝ, 1 / 2 < β → ¬ ∃ L > 0, ∀ u ∈ K, ∀ v ∈ K,
          ‖hessian f u - hessian f v‖ ≤ L * ‖u - v‖ ^ β)
    TwoLeg.SlowCurve.realizedObjectiveHolderSharp
    hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hHessian (z v : EuclideanSpace ℝ (Fin 2)) :
      (1 / 2 : ℝ) * ‖v‖ ^ 2 ≤
        inner ℝ (fderiv ℝ (gradient c.iteration.objective) z v) v := by
    simpa only [hessian_def] using (c.hessianBounds.at z).quadraticForm v |>.1
  have hlevel : objectiveSublevel c.iteration =
      {x | c.iteration.objective x ≤ c.iteration.objective (c.iteration.point 0)} := by
    ext x
    exact mem_objectiveSublevel_iff c.iteration x
  have hconvex : Convex ℝ (objectiveSublevel c.iteration) := by
    rw [hlevel]
    exact PlanarConvergence.convexInitialSublevel c.objectiveContDiff hhalf hHessian
      (c.iteration.point 0)
  have hmem (k : ℕ) : c.iteration.point k ∈ objectiveSublevel c.iteration :=
    c.iteration.pointMemObjectiveSublevelOfWeakWolfe c.stepLengthPos c.weakWolfe k
  exact ⟨c, hHolder, hSharp _ hconvex hmem⟩

/-- Helper for eq:counterexample-nonlipschitz: a Hölder Hessian bound on an
initial sublevel pulls back through an invertible linear coordinate change. -/
theorem hessianHolderOn_sublevel_of_comp
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (L : E ≃L[ℝ] F) (x₀ : F)
    {β : ℝ} (hβ : 0 ≤ β)
    (h : ∃ C > 0, ∀ x, (f ∘ L) x ≤ f x₀ → ∀ y, (f ∘ L) y ≤ f x₀ →
      ‖hessian (f ∘ L) x - hessian (f ∘ L) y‖ ≤ C * ‖x - y‖ ^ β) :
    ∃ C > 0, ∀ x, f x ≤ f x₀ → ∀ y, f y ≤ f x₀ →
      ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ β := by
  obtain ⟨C, hC, h⟩ := h
  let D := ‖L.symm.toContinuousLinearMap‖ ^ 2 * C *
    ‖L.symm.toContinuousLinearMap‖ ^ β
  have hD : 0 ≤ D := by positivity
  have heq : (f ∘ L) ∘ L.symm = f := by
    funext x
    simp only [Function.comp_apply, L.apply_symm_apply]
  have hset : ∀ x ∈ {z | (f ∘ L) z ≤ f x₀},
      ∀ y ∈ {z | (f ∘ L) z ≤ f x₀},
      ‖hessian (f ∘ L) x - hessian (f ∘ L) y‖ ≤ C * ‖x - y‖ ^ β := h
  have hDpos : 0 < D + 1 := by positivity
  refine ⟨D + 1, hDpos, ?_⟩
  intro x hx y hy
  have hx' : L.symm x ∈ {z | (f ∘ L) z ≤ f x₀} := by
    simpa only [Set.mem_setOf_eq, Function.comp_apply, L.apply_symm_apply] using hx
  have hy' : L.symm y ∈ {z | (f ∘ L) z ≤ f x₀} := by
    simpa only [Set.mem_setOf_eq, Function.comp_apply, L.apply_symm_apply] using hy
  have hbound := hessianHolderOn_comp_continuousLinearEquiv (hf.comp L.contDiff)
    L.symm hC.le hβ hset x hx' y hy'
  rw [heq] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right zero_le_one) (Real.rpow_nonneg (norm_nonneg _) _))

/-- Helper for eq:counterexample-nonlipschitz: the DFP embedding is the
canonical left orthogonal-sum inclusion. -/
theorem OrthogonalSum.embed_eq_inl {ι κ : Type*} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ ι) :
    (OrthogonalSum.embed z : EuclideanSpace ℝ (ι ⊕ κ)) =
      EuclideanSpace.OrthogonalSum.inl z := by
  ext i
  cases i with
  | inl i =>
    exact (OrthogonalSum.embed_apply_inl z i).trans
      (EuclideanSpace.OrthogonalSum.inl_apply_inl z i).symm
  | inr i =>
    exact (OrthogonalSum.embed_apply_inr z i).trans
      (EuclideanSpace.OrthogonalSum.inl_apply_inr z i).symm

/-- thm:main and eq:counterexample-nonlipschitz: in every dimension at least
two, the same strong-Wolfe counterexample has a globally one-half Hölder
Hessian and admits no larger exponent even on its initial sublevel. -/
theorem existsStrongWolfeCounterexampleHolderSharp_of_dimension_ge_two
    (n : ℕ) (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    ∃ c : StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2) c₁ c₂,
      (∃ L > 0, ∀ u v,
        ‖hessian c.iteration.objective u - hessian c.iteration.objective v‖ ≤
          L * ‖u - v‖ ^ (1 / 2 : ℝ)) ∧
      ∀ β : ℝ, 1 / 2 < β → ¬ ∃ L > 0,
        ∀ u ∈ objectiveSublevel c.iteration, ∀ v ∈ objectiveSublevel c.iteration,
          ‖hessian c.iteration.objective u - hessian c.iteration.objective v‖ ≤
            L * ‖u - v‖ ^ β := by
  classical
  obtain ⟨c, ⟨C, hC, hHolder⟩, hSharp⟩ := existsPlanarStrongWolfeCounterexampleHolderSharp
    hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  have hlower : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hupper : (1 : ℝ) ≤ 3 / 2 := by norm_num
  obtain ⟨d, hd, hdpoint⟩ := c.orthogonalSumWithObjective (κ := Fin (n - 2)) hlower hupper
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hDHolder : ∀ x y,
      ‖hessian d.iteration.objective x - hessian d.iteration.objective y‖ ≤
        C * ‖x - y‖ ^ (1 / 2 : ℝ) := by
    rw [hd, OrthogonalSum.objective_eq]
    exact EuclideanSpace.OrthogonalSum.Gradient.hessianHolder_objective
      c.objectiveContDiff hC.le hhalf hHolder
  have hDSharp (β : ℝ) (hβ : 1 / 2 < β) : ¬ ∃ L > 0,
      ∀ u, d.iteration.objective u ≤ d.iteration.objective (d.iteration.point 0) →
      ∀ v, d.iteration.objective v ≤ d.iteration.objective (d.iteration.point 0) →
        ‖hessian d.iteration.objective u - hessian d.iteration.objective v‖ ≤
          L * ‖u - v‖ ^ β := by
    rintro ⟨L, hL, hbound⟩
    apply hSharp β hβ
    refine ⟨L, hL, ?_⟩
    intro x hx y hy
    have hmem (z) (hz : z ∈ objectiveSublevel c.iteration) :
        d.iteration.objective (OrthogonalSum.embed z) ≤
          d.iteration.objective (d.iteration.point 0) := by
      rw [hd, hdpoint,
        OrthogonalSum.objective_embed, OrthogonalSum.objective_embed]
      exact (mem_objectiveSublevel_iff c.iteration z).mp hz
    have hbig := hbound _ (hmem x hx) _ (hmem y hy)
    rw [← map_sub, OrthogonalSum.norm_embed] at hbig
    rw [hd, OrthogonalSum.objective_eq,
      OrthogonalSum.embed_eq_inl, OrthogonalSum.embed_eq_inl] at hbig
    exact (EuclideanSpace.OrthogonalSum.Gradient.norm_hessian_sub_le_objective
      c.objectiveContDiff x y).trans hbig
  have hdim : 2 + (n - 2) = n := by omega
  let e : Fin n ≃ Fin 2 ⊕ Fin (n - 2) :=
    (finCongr hdim.symm).trans finSumFinEquiv.symm
  let Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2 ⊕ Fin (n - 2)) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hupperPos : (0 : ℝ) ≤ 3 / 2 := by norm_num
  obtain ⟨result, hresult, hpoint⟩ := d.pullbackWithObjective Q hhalf hupperPos
  refine ⟨result, ?_, ?_⟩
  · rw [hresult]
    exact existsHessianHolderPullback d.objectiveContDiff Q.toContinuousLinearEquiv
      ⟨C, hC, hDHolder⟩
  · intro β hβ hbound
    have hβpos : 0 ≤ β := hhalf.trans hβ.le
    have htransport : ∃ L > 0,
        ∀ x, (d.iteration.objective ∘ Q) x ≤ d.iteration.objective (d.iteration.point 0) →
        ∀ y, (d.iteration.objective ∘ Q) y ≤ d.iteration.objective (d.iteration.point 0) →
          ‖hessian (d.iteration.objective ∘ Q) x -
              hessian (d.iteration.objective ∘ Q) y‖ ≤ L * ‖x - y‖ ^ β := by
      obtain ⟨L, hL, hbound⟩ := hbound
      refine ⟨L, hL, ?_⟩
      intro x hx y hy
      have hmem (z) (hz : (d.iteration.objective ∘ Q) z ≤
          d.iteration.objective (d.iteration.point 0)) :
          z ∈ objectiveSublevel result.iteration := by
        rw [mem_objectiveSublevel_iff, hresult, hpoint]
        simpa only [Function.comp_apply, Q.apply_symm_apply] using hz
      simpa only [hresult] using hbound x (hmem x hx) y (hmem y hy)
    obtain ⟨L, hL, hbound⟩ := hessianHolderOn_sublevel_of_comp d.objectiveContDiff
      Q.toContinuousLinearEquiv (d.iteration.point 0) hβpos htransport
    apply hDSharp β hβ
    refine ⟨L, hL, ?_⟩
    intro x hx y hy
    exact hbound x hx y hy

end DFP
