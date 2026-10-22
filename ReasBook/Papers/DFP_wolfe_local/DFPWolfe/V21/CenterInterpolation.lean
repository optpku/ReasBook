/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import DFPWolfe.V21.CenterManifold
public import ReasLib.Optimization.DFP.Polar.AffineInterpolation

/-!
# Conditional interpolation of the actual Section 6 trajectory

The source C⁷ graph is selected once by the C⁸ graph-transform bounds and
Arzelà–Ascoli construction. A common initialization threshold then supplies the
literal spectral recurrence, its positive gradient limit and its full limiting
circle. The endpoint correction is the prescribed gradient minus the gradient
of the quadratic centered at that same limiting center.

Section 6.3 leaves the support-ball separation conditional. The interpolation
assembly below retains that condition and the eventual quadratic support scale.
-/

public section

noncomputable section

open Filter
open scoped Asymptotics BigOperators EuclideanSpace Matrix Topology

namespace DFPWolfe.V21.CenterInterpolation

/-- Helper for cm-limiting-scales: the literal orbit initialized on the selected
source graph, with no change of its recurrence or initial state. -/
def sourceOrbit (curve : DFP.TwoLeg.SlowCurve) (ε₀ : ℝ) : DFP.TwoPhaseOrbit :=
  DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀

/-- Helper for cm-limiting-scales: the source orbit is exactly `ofSlowCurve`
for the same graph and initial scale. -/
theorem sourceOrbit_def (curve : DFP.TwoLeg.SlowCurve) (ε₀ : ℝ) :
    sourceOrbit curve ε₀ = DFP.TwoPhaseOrbit.ofSlowCurve curve.shape curve.high ε₀ := by
  rfl

/-- Helper for cm-limiting-scales: the actual source initialization is
`x₀ = g₀ = (1,p(ε₀)ε₀²)` and `H₀ = diag(h(ε₀)p(ε₀)ε₀⁴,h(ε₀))`. -/
theorem sourceOrbitInitialization (curve : DFP.TwoLeg.SlowCurve) (ε₀ : ℝ) :
    ((sourceOrbit curve ε₀).state 0).point =
        WithLp.toLp 2 ![(1 : ℝ), curve.shape ε₀ * ε₀ ^ 2] ∧
      ((sourceOrbit curve ε₀).state 0).gradient =
        WithLp.toLp 2 ![(1 : ℝ), curve.shape ε₀ * ε₀ ^ 2] ∧
      ((sourceOrbit curve ε₀).state 0).metric =
        Matrix.diagonal ![curve.high ε₀ * curve.shape ε₀ * ε₀ ^ 4, curve.high ε₀] := by
  rw [sourceOrbit_def, DFP.TwoPhaseOrbit.ofSlowCurve_zero]
  exact CenterManifold.prescribedInitialization curve.shape curve.high ε₀

/-- Helper for cm-limiting-scales: adding the exact source correction to the
centered quadratic gradient gives the actual prescribed endpoint gradient. -/
theorem correctedEndpointGradient (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    orbit.endpoint k - C + orbit.endpointCorrection C k = orbit.endpointGradient k := by
  rw [DFP.TwoPhaseOrbit.endpointCorrection_def]
  abel

/-- Helper for cm-limiting-scales: joint estimates for one actual source orbit
and the SAME positive amplitude limit and limiting center. -/
structure TrajectoryEstimates (curve : DFP.TwoLeg.SlowCurve) (ε₀ G : ℝ)
    (C : EuclideanSpace ℝ (Fin 2)) (cR CR Ca : ℝ) : Prop where
  /-- Helper for cm-limiting-scales and cm-center-proposition: the source point,
  gradient and diagonal matrix are initialized on this same graph and initial scale. -/
  initialization :
    ((sourceOrbit curve ε₀).state 0).point =
        WithLp.toLp 2 ![(1 : ℝ), curve.shape ε₀ * ε₀ ^ 2] ∧
      ((sourceOrbit curve ε₀).state 0).gradient =
        WithLp.toLp 2 ![(1 : ℝ), curve.shape ε₀ * ε₀ ^ 2] ∧
      ((sourceOrbit curve ε₀).state 0).metric =
        Matrix.diagonal ![curve.high ε₀ * curve.shape ε₀ * ε₀ ^ 4, curve.high ε₀]
  /-- Helper for cm-limiting-scales and cm-center-proposition: every cycle is the exact physical
  positive-definite two-stage spectral recurrence. -/
  exactCycles : ∀ j, DFP.TwoPhaseOrbit.State.ExactCycle ((sourceOrbit curve ε₀).state j)
  /-- Helper for cm-limiting-scales: the actual source amplitude tends to G. -/
  amplitudeLimit : Tendsto (fun j ↦ ((sourceOrbit curve ε₀).state j).amplitude)
    atTop (𝓝 G)
  /-- Helper for cm-limiting-scales: the prescribed gradient norms in both
  phases tend to that same G. -/
  gradientNormLimit : Tendsto (fun k ↦ ‖(sourceOrbit curve ε₀).endpointGradient k‖)
    atTop (𝓝 G)
  /-- Helper for cm-limiting-scales: the actual cycle centers tend to C. -/
  centerLimit : Tendsto (fun j ↦ ((sourceOrbit curve ε₀).state j).center)
    atTop (𝓝 C)
  /-- Helper for cm-limiting-scales: every flattened source scale is positive. -/
  scalePositive : ∀ k, 0 < ((sourceOrbit curve ε₀).state (k / 2)).ε
  /-- Helper for cm-limiting-scales: the flattened source scale tends to zero. -/
  scaleLimit : Tendsto (fun k ↦ ((sourceOrbit curve ε₀).state (k / 2)).ε)
    atTop (𝓝 0)
  /-- Helper for cm-limiting-scales: the full actual endpoint cluster set is
  the circle with the SAME C and G. -/
  clusterSet : {z : EuclideanSpace ℝ (Fin 2) |
      MapClusterPt z atTop (sourceOrbit curve ε₀).endpoint} =
    DFP.TwoPhaseOrbit.limitCircle C G
  /-- Helper for cm-limiting-scales: the actual radial excess has a uniform
  positive linear lower bound in the flattened cycle scale. -/
  radialLower : ∀ k, cR * ((sourceOrbit curve ε₀).state (k / 2)).ε ≤
    ‖(sourceOrbit curve ε₀).endpoint k - C‖ - G
  /-- Helper for cm-limiting-scales: the actual radial excess has a uniform
  linear upper bound in that same scale. -/
  radialUpper : ∀ k, ‖(sourceOrbit curve ε₀).endpoint k - C‖ - G ≤
    CR * ((sourceOrbit curve ε₀).state (k / 2)).ε
  /-- Helper for cm-limiting-scales: the exact correction to the centered
  quadratic is uniformly cubic in the actual flattened scale. -/
  correctionBound : ∀ k, ‖(sourceOrbit curve ε₀).endpointCorrection C k‖ ≤
    Ca * ((sourceOrbit curve ε₀).state (k / 2)).ε ^ 3
  /-- Helper for cm-limiting-scales: the actual first endpoint displacement
  has leading norm `2Gⱼεⱼ²`. -/
  firstStep : (fun j ↦ ‖(sourceOrbit curve ε₀).endpoint (2 * j + 1) -
      (sourceOrbit curve ε₀).endpoint (2 * j)‖) ~[atTop]
    (fun j ↦ 2 * ((sourceOrbit curve ε₀).state j).amplitude *
      ((sourceOrbit curve ε₀).state j).ε ^ 2)
  /-- Helper for cm-limiting-scales: the actual second endpoint displacement
  has leading norm `Gⱼεⱼ²`. -/
  secondStep : (fun j ↦ ‖(sourceOrbit curve ε₀).endpoint (2 * j + 2) -
      (sourceOrbit curve ε₀).endpoint (2 * j + 1)‖) ~[atTop]
    (fun j ↦ ((sourceOrbit curve ε₀).state j).amplitude *
      ((sourceOrbit curve ε₀).state j).ε ^ 2)

/-- Helper for cm-limiting-scales: the source graph is fixed before one common
threshold, and all later initializations have joint actual recurrence, limit,
circle, radial, coefficient and step estimates. -/
theorem sourceTrajectoryFamily :
    ∃ curve : DFP.TwoLeg.SlowCurve,
      ContDiffAt ℝ 7 (fun ε ↦ (curve.shape ε, curve.high ε)) 0 ∧
      (curve.shape 0, curve.high 0) = (2, 1) ∧
      ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cR > 0, ∃ CR > 0, ∃ Ca > 0,
        ∀ ε₀ ∈ Set.Ioc 0 εbar, ∃ G > 0, ∃ C : EuclideanSpace ℝ (Fin 2),
          TrajectoryEstimates curve ε₀ G C cR CR Ca := by
  obtain ⟨curve, hsmooth, hbase, ηGeometry, hηGeometry,
    cR, hcR, CR, hCR, Ca, hCa, hgeometry⟩ :=
    CenterManifold.centerManifoldInterpolationGeometry
  obtain ⟨ηExact, hηExact, hexact⟩ := DFP.TwoPhaseOrbit.ofSlowCurveExact
    curve.shape curve.high curve.isInvariant curve.shapeRemainder curve.highRemainder
    ηGeometry hηGeometry
  obtain ⟨ηGradient, hηGradient, hgradient⟩ := CenterManifold.slowCurveFullGradientLimit curve
  obtain ⟨ηStep, hηStep, hstep⟩ := CenterManifold.slowCurveStepAsymptotics curve
  let εbar := min ηExact (min ηGradient ηStep)
  have hεbarPos : 0 < εbar := lt_min hηExact.1 (lt_min hηGradient.1 hηStep.1)
  have hεbarLt : εbar < 1 / 4 :=
    ((min_le_left _ _).trans hηExact.2).trans_lt hηGeometry.2
  refine ⟨curve, hsmooth, hbase, εbar, ⟨hεbarPos, hεbarLt⟩,
    cR, hcR, CR, hCR, Ca, hCa, ?_⟩
  intro ε₀ hε₀
  have hsmall : ε₀ ≤ ηExact ∧ ε₀ ≤ ηGradient ∧ ε₀ ≤ ηStep := by
    simpa only [εbar, le_min_iff] using hε₀.2
  have hεExact : ε₀ ∈ Set.Ioc 0 ηExact := ⟨hε₀.1, hsmall.1⟩
  have hεGeometry : ε₀ ∈ Set.Ioc 0 ηGeometry := ⟨hε₀.1, hsmall.1.trans hηExact.2⟩
  have hεGradient : ε₀ ∈ Set.Ioc 0 ηGradient := ⟨hε₀.1, hsmall.2.1⟩
  have hεStep : ε₀ ∈ Set.Ioc 0 ηStep := ⟨hε₀.1, hsmall.2.2⟩
  obtain ⟨G, hG, C, hamplitude, hcenter, hscale, hcluster, horders⟩ :=
    hgeometry ε₀ hεGeometry
  obtain ⟨hfirst, hsecond⟩ := hstep ε₀ hεStep
  have hfirstEndpoint : (fun j ↦ ‖(sourceOrbit curve ε₀).endpoint (2 * j + 1) -
      (sourceOrbit curve ε₀).endpoint (2 * j)‖) =
      (fun j ↦ ‖((sourceOrbit curve ε₀).state j).firstDisplacement‖) := by
    funext j
    rw [(CenterManifold.endpointDisplacements (sourceOrbit curve ε₀) j).1]
  have hsecondEndpoint : (fun j ↦ ‖(sourceOrbit curve ε₀).endpoint (2 * j + 2) -
      (sourceOrbit curve ε₀).endpoint (2 * j + 1)‖) =
      (fun j ↦ ‖((sourceOrbit curve ε₀).state j).secondDisplacement‖) := by
    funext j
    rw [(CenterManifold.endpointDisplacements (sourceOrbit curve ε₀) j).2]
  refine ⟨G, hG, C, ?_⟩
  constructor
  · exact sourceOrbitInitialization curve ε₀
  · simpa only [sourceOrbit_def] using hexact ε₀ hεExact
  · exact hamplitude
  · exact hgradient ε₀ hεGradient G hG hamplitude
  · exact hcenter
  · exact fun k ↦ (horders k).1
  · exact hscale
  · exact hcluster
  · exact fun k ↦ (horders k).2.1
  · exact fun k ↦ (horders k).2.2.1
  · exact fun k ↦ (horders k).2.2.2
  · rw [hfirstEndpoint]
    exact hfirst
  · rw [hsecondEndpoint]
    exact hsecond


open DFP.Polar

/-- Helper for cm-limiting-scales and eq:polar-objective: the FULL original χ
correction sum for the actual hatted endpoints and the SAME limiting center. -/
def endpointPerturbation (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (ρ : ℕ → ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  InterpolationSum.perturbation orbit.endpoint ρ (orbit.endpointCorrection C)

/-- Helper for cm-limiting-scales: the endpoint perturbation uses the original
centers, radii and exact prescribed-gradient corrections. -/
theorem endpointPerturbation_def (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (ρ : ℕ → ℝ) :
    endpointPerturbation orbit C ρ =
      InterpolationSum.perturbation orbit.endpoint ρ (orbit.endpointCorrection C) := by
  rfl

/-- Helper for cm-limiting-scales and eq:polar-objective: the centered quadratic
plus the unchanged original full correction sum. -/
def endpointObjective (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (ρ : ℕ → ℝ) : EuclideanSpace ℝ (Fin 2) → ℝ :=
  AffineInterpolation.shiftedObjective C (endpointPerturbation orbit C ρ)

/-- Helper for cm-limiting-scales: the actual objective is the accepted shifted
quadratic construction applied to the original endpoint perturbation. -/
theorem endpointObjective_def (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (ρ : ℕ → ℝ) :
    endpointObjective orbit C ρ =
      AffineInterpolation.shiftedObjective C (endpointPerturbation orbit C ρ) := by
  rfl

/-- Helper for cm-limiting-scales: evaluation retains the centered quadratic
and every original bump, including the finitely many early bumps. -/
theorem endpointObjective_apply (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (ρ : ℕ → ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    endpointObjective orbit C ρ x = (1 / 2 : ℝ) * ‖x - C‖ ^ 2 +
      endpointPerturbation orbit C ρ x := by
  rw [endpointObjective_def, AffineInterpolation.shiftedObjective_apply]

/-- Helper for cm-limiting-scales and eq:polar-objective: disjoint positive
OPEN endpoint balls make the full sum the literal infinite sum of the SAME χ
bumps, with coefficient `gₖ − (xₖ − C)`. -/
theorem endpointPerturbation_eq_tsum (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (ρ : ℕ → ℝ) (hρ : ∀ k, 0 < ρ k)
    (hballs : Set.univ.PairwiseDisjoint (fun k ↦ Metric.ball (orbit.endpoint k) (ρ k)))
    (x : EuclideanSpace ℝ (Fin 2)) :
    endpointPerturbation orbit C ρ x = ∑' k,
      ExplicitCutoff.chi ((ρ k)⁻¹ • (x - orbit.endpoint k)) *
        inner ℝ (orbit.endpointGradient k - (orbit.endpoint k - C))
          (x - orbit.endpoint k) := by
  rw [endpointPerturbation_def,
    AffineInterpolation.perturbation_eq_tsum_of_disjoint _ _ _ hρ hballs]
  apply tsum_congr
  intro k
  rw [InterpolationSum.bump_apply, DFP.TwoPhaseOrbit.endpointCorrection_def]

/-- Helper for cm-limiting-scales: proved regularity, exact endpoint jets and
quantitative eventual derivative envelopes of the original source interpolant. -/
structure InterpolationEstimates (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (ρ : ℕ → ℝ) (κ Ca : ℝ) : Prop where
  /-- Helper for cm-limiting-scales: the full original χ sum is C². -/
  perturbationC2 : ContDiff ℝ 2 (endpointPerturbation orbit C ρ)
  /-- Helper for cm-limiting-scales: the shifted quadratic objective is C². -/
  objectiveC2 : ContDiff ℝ 2 (endpointObjective orbit C ρ)
  /-- Helper for cm-limiting-scales: one positive global constant gives the
  half-Hölder Hessian bounds for both full sum and objective. -/
  hessianHolder : ∃ H : ℝ, 0 < H ∧
    (∀ x y, ‖hessian (endpointPerturbation orbit C ρ) x -
      hessian (endpointPerturbation orbit C ρ) y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ)) ∧
    (∀ x y, ‖hessian (endpointObjective orbit C ρ) x -
      hessian (endpointObjective orbit C ρ) y‖ ≤ H * ‖x - y‖ ^ (1 / 2 : ℝ))
  /-- Helper for cm-limiting-scales: every endpoint has the full correction
  jet `(0,aₖ,0)`, including all early endpoints. -/
  perturbationJets : ∀ k, endpointPerturbation orbit C ρ (orbit.endpoint k) = 0 ∧
    gradient (endpointPerturbation orbit C ρ) (orbit.endpoint k) =
      orbit.endpointCorrection C k ∧
    hessian (endpointPerturbation orbit C ρ) (orbit.endpoint k) = 0
  /-- Helper for cm-limiting-scales: every endpoint has the exact quadratic
  value, the ACTUAL prescribed gradient and Hessian I. -/
  objectiveJets : ∀ k, endpointObjective orbit C ρ (orbit.endpoint k) =
      (1 / 2 : ℝ) * ‖orbit.endpoint k - C‖ ^ 2 ∧
    gradient (endpointObjective orbit C ρ) (orbit.endpoint k) = orbit.endpointGradient k ∧
    hessian (endpointObjective orbit C ρ) (orbit.endpoint k) = 1
  /-- Helper for cm-limiting-scales: a constant precedes the eventual bump
  index in the source O(ε), O(ε⁻¹) and uniform half-Hölder envelopes; the
  coefficient factor `‖aₖ‖ρₖ^(-3/2)` is eventually bounded as well. -/
  bumpOrders : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ k in atTop,
    (∀ x, ‖hessian (InterpolationSum.bump orbit.endpoint ρ
      (orbit.endpointCorrection C) k) x‖ ≤
        K * (Ca / κ) * (orbit.state (k / 2)).ε) ∧
    (∀ x y, ‖hessian (InterpolationSum.bump orbit.endpoint ρ
      (orbit.endpointCorrection C) k) x -
      hessian (InterpolationSum.bump orbit.endpoint ρ
        (orbit.endpointCorrection C) k) y‖ ≤
        K * (Ca / κ ^ 2) * ((orbit.state (k / 2)).ε)⁻¹ * ‖x - y‖) ∧
    (∀ x y, ‖hessian (InterpolationSum.bump orbit.endpoint ρ
      (orbit.endpointCorrection C) k) x -
      hessian (InterpolationSum.bump orbit.endpoint ρ
        (orbit.endpointCorrection C) k) y‖ ≤
        K * (Ca * κ ^ (-3 / 2 : ℝ)) * ‖x - y‖ ^ (1 / 2 : ℝ)) ∧
    ‖orbit.endpointCorrection C k‖ * (ρ k) ^ (-3 / 2 : ℝ) ≤
      Ca * κ ^ (-3 / 2 : ℝ)

/-- Helper for cm-limiting-scales: actual trajectory estimates and ONLY the
source eventual support comparison and open-ball disjointness imply all full-sum
regularity and jets. No regularity conclusion is assumed as a premise. -/
theorem interpolateSourceTrajectory {curve : DFP.TwoLeg.SlowCurve} {ε₀ G : ℝ}
    {C : EuclideanSpace ℝ (Fin 2)} {cR CR Ca : ℝ}
    (htrajectory : TrajectoryEstimates curve ε₀ G C cR CR Ca)
    (hG : 0 < G) (hcR : 0 < cR) (hCR : 0 < CR) (hCa : 0 < Ca)
    (ρ : ℕ → ℝ) (κLow κHigh : ℝ) (hκLow : 0 < κLow) (hκHigh : 0 < κHigh)
    (hρ : ∀ k, 0 < ρ k)
    (hradii : ∀ᶠ k in atTop,
      κLow * ((sourceOrbit curve ε₀).state (k / 2)).ε ^ 2 ≤ ρ k ∧
      ρ k ≤ κHigh * ((sourceOrbit curve ε₀).state (k / 2)).ε ^ 2)
    (hballs : Set.univ.PairwiseDisjoint
      (fun k ↦ Metric.ball ((sourceOrbit curve ε₀).endpoint k) (ρ k))) :
    InterpolationEstimates (sourceOrbit curve ε₀) C ρ κLow Ca := by
  let orbit := sourceOrbit curve ε₀
  have horders : ∀ᶠ k in atTop,
      cR * (orbit.state (k / 2)).ε ≤ ‖orbit.endpoint k - C‖ - G ∧
      ‖orbit.endpoint k - C‖ - G ≤ CR * (orbit.state (k / 2)).ε ∧
      κLow * (orbit.state (k / 2)).ε ^ 2 ≤ ρ k ∧
      ρ k ≤ κHigh * (orbit.state (k / 2)).ε ^ 2 ∧
      ‖orbit.endpointCorrection C k‖ ≤ Ca * (orbit.state (k / 2)).ε ^ 3 := by
    filter_upwards [hradii] with k hk
    exact ⟨htrajectory.radialLower k, htrajectory.radialUpper k, hk.1, hk.2,
      htrajectory.correctionBound k⟩
  obtain ⟨hsmooth, hobjective, hholder, hjets, hobjjets⟩ :=
    AffineInterpolation.interpolateCircle_of_eventualBounds C hG
      orbit.endpoint ρ (orbit.endpointCorrection C) (fun k ↦ (orbit.state (k / 2)).ε)
      cR CR κLow κHigh Ca hcR hCR hκLow hκHigh hCa
      htrajectory.scalePositive htrajectory.scaleLimit hρ horders hballs
  have hcoefficientOrders : ∀ᶠ k in atTop,
      κLow * (orbit.state (k / 2)).ε ^ 2 ≤ ρ k ∧
      ‖orbit.endpointCorrection C k‖ ≤ Ca * (orbit.state (k / 2)).ε ^ 3 := by
    filter_upwards [hradii] with k hk
    exact ⟨hk.1, htrajectory.correctionBound k⟩
  have hbump := AffineInterpolation.bump_hessian_orders_of_eventualBounds
    orbit.endpoint ρ (orbit.endpointCorrection C) (fun k ↦ (orbit.state (k / 2)).ε)
    hκLow hCa.le htrajectory.scalePositive hcoefficientOrders
  constructor
  · exact hsmooth
  · exact hobjective
  · exact hholder
  · exact hjets
  · intro k
    obtain ⟨hvalue, hgradient, hhessian⟩ := hobjjets k
    rw [correctedEndpointGradient] at hgradient
    exact ⟨hvalue, hgradient, hhessian⟩
  · exact hbump

/-- cm-limiting-scales (conditional Section 6.3 interpolation assembly).
One ACTUAL C⁷ Arzelà–Ascoli-selected source graph is fixed first, then one
initialization threshold and uniform radial/correction constants. Every positive
initial scale below it generates the literal initialized exact recurrence, a
positive gradient limit G, limiting center C and EXACT full circle cluster set.
For ANY positive radii eventually comparable to ε⌊k/2⌋² whose OPEN endpoint balls
are pairwise disjoint, the FULL original sum of the same explicit χ bumps and
the quadratic centered at this SAME C are C² with globally half-Hölder Hessians.
Their endpoint jets and eventual per-bump O(ε), O(ε⁻¹) bounds are exact projections
of the result records. The support separation remains the manuscript's explicit
condition; the theorem is not a hatted Wolfe-counterexample assertion. -/
theorem centerManifoldConditionalInterpolation :
    ∃ curve : DFP.TwoLeg.SlowCurve,
      ContDiffAt ℝ 7 (fun ε ↦ (curve.shape ε, curve.high ε)) 0 ∧
      (curve.shape 0, curve.high 0) = (2, 1) ∧
      ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ cR > 0, ∃ CR > 0, ∃ Ca > 0,
        ∀ ε₀ ∈ Set.Ioc 0 εbar, ∃ G > 0, ∃ C : EuclideanSpace ℝ (Fin 2),
          TrajectoryEstimates curve ε₀ G C cR CR Ca ∧
          ∀ (ρ : ℕ → ℝ) (κLow κHigh : ℝ), 0 < κLow → 0 < κHigh →
            (∀ k, 0 < ρ k) →
            (∀ᶠ k in atTop,
              κLow * ((sourceOrbit curve ε₀).state (k / 2)).ε ^ 2 ≤ ρ k ∧
              ρ k ≤ κHigh * ((sourceOrbit curve ε₀).state (k / 2)).ε ^ 2) →
            Set.univ.PairwiseDisjoint
              (fun k ↦ Metric.ball ((sourceOrbit curve ε₀).endpoint k) (ρ k)) →
            InterpolationEstimates (sourceOrbit curve ε₀) C ρ κLow Ca := by
  obtain ⟨curve, hsmooth, hbase, εbar, hεbar, cR, hcR, CR, hCR, Ca, hCa, hfamily⟩ :=
    sourceTrajectoryFamily
  refine ⟨curve, hsmooth, hbase, εbar, hεbar, cR, hcR, CR, hCR, Ca, hCa, ?_⟩
  intro ε₀ hε₀
  obtain ⟨G, hG, C, htrajectory⟩ := hfamily ε₀ hε₀
  refine ⟨G, hG, C, htrajectory, ?_⟩
  intro ρ κLow κHigh hκLow hκHigh hρ hradii hballs
  exact interpolateSourceTrajectory htrajectory hG hcR hCR hCa
    ρ κLow κHigh hκLow hκHigh hρ hradii hballs

end DFPWolfe.V21.CenterInterpolation
