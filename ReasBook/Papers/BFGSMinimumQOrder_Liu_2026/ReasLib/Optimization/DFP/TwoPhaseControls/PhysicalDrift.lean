module

public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusJetCertificates
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondFactorGerm
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusSecondGradientGermTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusQuadraticGermTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ObservableMirror
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.ObservableGermTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawObservableZero
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameSlopeCoefficientBridge
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualRawFrameBridge
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawFrameCertificateAdapter
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketRegularityAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap.Observables
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusNormalForm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualAdapter
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.RawObservableZero
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterResidualRawFrameBridge
import all ReasLib.Geometry.Euclidean.Plane.SignedAngle
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketScaleGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterSecondScaleGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.WeightedCenterBracketGerm
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.CenterBracketTransport

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.TwoLeg.Mixed

/-- The displayed amplitude coefficient array evaluates to its constant plus
    quadratic polynomial. -/
lemma mixedAmplitudeCoefficientPolynomial (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    ∑ n : Fin 3,
        (![1, 0,
          (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n * r ^ (n : ℕ) =
      1 + ((θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18) * r ^ 2 := by
  simp [Fin.sum_univ_succ]

/-- The displayed frame-angle coefficient array evaluates to the linear polynomial
    `-3 * r`. -/
lemma mixedFrameAngleCoefficientPolynomial (r : ℝ) :
    ∑ n : Fin 2, (![0, -3] : Fin 2 → ℝ) n * r ^ (n : ℕ) = -3 * r := by
  simp [Fin.sum_univ_succ]

/-- A natural power of an absolute value agrees with its real-power notation. -/
lemma absPow_nat_eq_realRpow (r : ℝ) (n : ℕ) :
    |r| ^ n = |r| ^ (n : ℝ) := by
  -- The real-power API gives the same identity in the opposite orientation.
  exact (Real.rpow_natCast |r| n).symm

/-- The metric and gradient projections of a physical raw step are the corresponding
    independent raw-step projections; only the third displacement component is extra. -/
lemma mixedRawObservableStep_pair_eq
    (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) :
    ((rawObservableStep H g control).1, (rawObservableStep H g control).2.1) =
      independentRawStep H g control := by
  -- Both evaluators use the same inverse-update and gradient formulas; the physical
  -- evaluator merely stores the additional displacement as a third component.
  apply Prod.ext
  · rfl
  · rfl

/- The component projections below are the stable rewrite interface for the
   physical evaluator.  Keeping these equalities separate avoids reopening the
   nested product whenever one scalar observable is transported. -/

/-- The physical raw-step metric is the independent raw-step metric. -/
lemma mixedRawObservableStep_metric_eq
    (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) :
    (rawObservableStep H g control).1 =
      (independentRawStep H g control).1 := by
  -- Project the already established pair equality to its metric component.
  exact congrArg Prod.fst (mixedRawObservableStep_pair_eq H g control)

/-- The physical raw-step gradient is the independent raw-step gradient. -/
lemma mixedRawObservableStep_gradient_eq
    (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) :
    (rawObservableStep H g control).2.1 =
      (independentRawStep H g control).2 := by
  -- Project the pair equality to the updated gradient component.
  simpa only using congrArg Prod.snd (mixedRawObservableStep_pair_eq H g control)

/-- The independent raw evaluator's final low-gradient coordinate. -/
def mixedIndependentRawAmplitude (b r p h : ℝ) : ℝ :=
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * r ^ 2, h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), p * r]
  let firstStep := independentRawStep H₀ g₀ (TwoPhaseControls.first b)
  let firstFrame := OrientedEigenframe.frame
    (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
    (WithLp.toLp 2 firstStep.2)
  let H₁ := firstFrame.transpose * firstStep.1 * firstFrame
  let g₁ := firstFrame.transpose *ᵥ firstStep.2
  let secondStep := independentRawStep H₁ g₁ (TwoPhaseControls.second b)
  let secondFrame := OrientedEigenframe.frame
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
    (WithLp.toLp 2 secondStep.2)
  (secondFrame.transpose *ᵥ secondStep.2) 0

/-- The independent raw evaluator's relative-frame signed coordinate. -/
def mixedIndependentRawFrameAngle (b r p h : ℝ) : ℝ :=
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * r ^ 2, h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), p * r]
  let firstStep := independentRawStep H₀ g₀ (TwoPhaseControls.first b)
  let firstFrame := OrientedEigenframe.frame
    (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
    (WithLp.toLp 2 firstStep.2)
  let H₁ := firstFrame.transpose * firstStep.1 * firstFrame
  let g₁ := firstFrame.transpose *ᵥ firstStep.2
  let secondStep := independentRawStep H₁ g₁ (TwoPhaseControls.second b)
  let secondFrame := OrientedEigenframe.frame
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
    (WithLp.toLp 2 secondStep.2)
  EuclideanPlane.SignedAngle.coordinate (firstFrame * secondFrame)

/-- The physical amplitude equals the independent raw final low coordinate. -/
lemma mixedObservable_amplitude_eq_independentRaw
    (b r p h : ℝ) :
    (observableMap b (r, p, h)).amplitudeRatio =
      mixedIndependentRawAmplitude b r p h := by
  -- Rewrite each raw-step metric/gradient projection through the scalar bridge.
  unfold observableMap mixedIndependentRawAmplitude
  dsimp only
  simp_rw [mixedRawObservableStep_metric_eq, mixedRawObservableStep_gradient_eq]

/-- The physical frame increment equals the independent raw relative-frame coordinate. -/
lemma mixedObservable_frameAngle_eq_independentRaw
    (b r p h : ℝ) :
    (observableMap b (r, p, h)).frameAngleIncrement =
      mixedIndependentRawFrameAngle b r p h := by
  -- The frame product depends only on the metric and gradient projections.
  unfold observableMap mixedIndependentRawFrameAngle
  dsimp only
  simp_rw [mixedRawObservableStep_metric_eq, mixedRawObservableStep_gradient_eq]

/-- The zero-radius independent raw step is stationary at the diagonal base. -/
lemma independentRawStep_zeroRadius_base (control : PlanarDFPControl) :
    independentRawStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0] control =
      (Matrix.diagonal ![(0 : ℝ), 1], ![(1 : ℝ), 0]) := by
  simpa [rawObservableStep_zeroRadius_base] using
    (mixedRawObservableStep_pair_eq
      (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0] control)
      |>.symm

/-- The zero-radius independent raw frame is the identity. -/
lemma independentRawStep_zeroRadius_frame (control : PlanarDFPControl) :
    OrientedEigenframe.frame
        ((independentRawStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0] control).1 0 0)
        ((independentRawStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0] control).1 0 1)
        ((independentRawStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0] control).1 1 1)
        (WithLp.toLp 2
          (independentRawStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0] control).2) = 1 := by
  rw [independentRawStep_zeroRadius_base]
  exact orientedEigenframe_zeroRadius_frame

/-- Conjugating the zero-radius step by the stationary first frame changes nothing. -/
lemma independentRawStep_zeroRadius_conjugated (control : PlanarDFPControl) :
    independentRawStep
        ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose *
          Matrix.diagonal ![(0 : ℝ), 1] * 1)
        ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose *ᵥ ![(1 : ℝ), 0]) control =
      (Matrix.diagonal ![(0 : ℝ), 1], ![(1 : ℝ), 0]) := by
  simpa using independentRawStep_zeroRadius_base control

/- The center cancellation at zero control scale only uses that the control
   matrix is the identity; recording this projection avoids unfolding the DFP
   inverse update in the residual proof. -/

/-- An identity secant matrix makes the raw gradient change equal its displacement. -/
lemma rawObservableStep_gradientSub_eq_displacement_of_identity
    (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ) (τ : ℝ) :
    (rawObservableStep H g ⟨1, τ⟩).2.1 - g =
      (rawObservableStep H g ⟨1, τ⟩).2.2 := by
  unfold rawObservableStep
  dsimp
  ext i
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The identity step exposes its updated gradient as input plus displacement. -/
lemma rawObservableStep_gradient_eq_add_displacement_of_identity
    (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ) (τ : ℝ) :
    (rawObservableStep H g ⟨1, τ⟩).2.1 =
      g + (rawObservableStep H g ⟨1, τ⟩).2.2 := by
  have h := rawObservableStep_gradientSub_eq_displacement_of_identity H g τ
  ext i
  have hi := congrArg (fun v : Fin 2 → ℝ ↦ v i) h
  simpa only [Pi.sub_apply, Pi.add_apply, add_comm] using (sub_eq_iff_eq_add.mp hi)

/-- A positive fixed-frame low coordinate is preserved by gradient orientation. -/
lemma orientedLowCoordinate_eq_of_fixedFrameCoordinates
    (a b d q u : ℝ) (v : Fin 2 → ℝ)
    (hcoords :
      (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
        ![q, u]) (hq : 0 < q) :
    (OrientedEigenframe.frame a b d (WithLp.toLp 2 v)).transpose.mulVec v 0 = q := by
  -- The first fixed-frame coordinate is the orientation test itself.
  have hinner : inner ℝ (RealSymmetric2.lowVector a b d)
      (WithLp.toLp 2 v) = q := by
    have hzero := congrArg (fun w : Fin 2 → ℝ ↦ w 0) hcoords
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
      EuclideanPlane.frame, PiLp.inner_apply, mul_comm] using hzero
  have hinnerPos : 0 < inner ℝ (RealSymmetric2.lowVector a b d)
      (WithLp.toLp 2 v) := by
    rwa [hinner]
  unfold OrientedEigenframe.frame OrientedEigenframe.lowVector
  rw [if_pos hinnerPos]
  exact congrArg (fun w : Fin 2 → ℝ ↦ w 0) hcoords

/-- Simultaneous negation preserves a positive fixed-frame low coordinate. -/
lemma orientedLowCoordinate_eq_of_fixedFrameCoordinates_neg
    (a b d q u : ℝ) (v : Fin 2 → ℝ)
    (hcoords :
      (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose.mulVec v =
        ![q, u]) (hq : 0 < q) :
    (OrientedEigenframe.frame a b d (WithLp.toLp 2 (-v))).transpose.mulVec (-v) 0 = q := by
  -- Negating the input flips the oriented frame and the updated coordinates together.
  have hinner : inner ℝ (RealSymmetric2.lowVector a b d)
      (WithLp.toLp 2 v) = q := by
    have hzero := congrArg (fun w : Fin 2 → ℝ ↦ w 0) hcoords
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
      EuclideanPlane.frame, PiLp.inner_apply, mul_comm] using hzero
  have hinnerNe : inner ℝ (RealSymmetric2.lowVector a b d)
      (WithLp.toLp 2 v) ≠ 0 := by
    rw [hinner]
    exact ne_of_gt hq
  rw [WithLp.toLp_neg,
    orientedEigenframe_frame_negate_gradient_of_inner_ne_zero a b d
      (WithLp.toLp 2 v) hinnerNe]
  simp only [Matrix.transpose_neg, Matrix.neg_mulVec, Matrix.mulVec_neg, neg_neg]
  exact orientedLowCoordinate_eq_of_fixedFrameCoordinates a b d q u v hcoords hq

/-- Under the usual secant-step side conditions, the physical raw displacement is the
    displacement field of the canonical abstract secant step. -/
lemma mixedRawObservableStep_displacement_eq
    (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) (hH : H.PosDef)
    (hcontrol : control.matrix.PosDef) (htau : 0 < control.tau) (hg : g ≠ 0) :
    (rawObservableStep H g control).2.2 =
      (DFP.AbstractSecantStep.ofMatrices H g control.matrix control.tau
        hH hcontrol htau hg).displacement := by
  -- The displacement field is the shared scalar-step formula after packaging the
  -- metric, control, and nonzero-gradient certificates in `ofMatrices`.
  rfl

/- The physical evaluator has the same simultaneous-negation symmetry as the
   independent raw-step mirror.  Isolating it here keeps the later frame branch
   from reopening the scalar-step algebra. -/

/-- Negating an incoming raw gradient preserves the metric update and negates both
    the updated gradient and the displacement. -/
lemma rawObservableStep_negate_gradient
    (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) :
    rawObservableStep H (-g) control =
      ((rawObservableStep H g control).1,
        -(rawObservableStep H g control).2.1,
        -(rawObservableStep H g control).2.2) := by
  -- The preconditioned gradient changes sign, so the scalar step length is
  -- unchanged while both vector-valued outputs change sign.
  let v : Fin 2 → ℝ := H *ᵥ g
  let α : ℝ := control.tau * (g ⬝ᵥ v) / (v ⬝ᵥ (control.matrix *ᵥ v))
  let s : Fin 2 → ℝ := -(α • v)
  let y : Fin 2 → ℝ := control.matrix *ᵥ s
  have hraw : rawObservableStep H g control =
      (Matrix.inverseDFPUpdate H s y, g + y, s) := by
    simp only [rawObservableStep, v, α, s, y]
  have hnegv : H *ᵥ (-g) = -v := by
    simp only [v, Matrix.mulVec_neg]
  have hdotg : (-g) ⬝ᵥ (-v) = g ⬝ᵥ v := by
    rw [neg_dotProduct, dotProduct_neg]
    ring
  have hdotv : (-v) ⬝ᵥ (control.matrix *ᵥ (-v)) =
      v ⬝ᵥ (control.matrix *ᵥ v) := by
    rw [Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg]
    ring
  have halpha' : control.tau * ((-g) ⬝ᵥ (-v)) /
      ((-v) ⬝ᵥ (control.matrix *ᵥ (-v))) = α := by
    rw [hdotg, hdotv]
  have hs : -(α • (-v)) = -s := by
    simp [s]
  have hmulneg (w : Fin 2 → ℝ) : control.matrix *ᵥ (-w) =
      -(control.matrix *ᵥ w) := by
    exact Matrix.mulVec_neg w control.matrix
  have hy : control.matrix *ᵥ (-(α • (-v))) = -y := by
    rw [hs]
    simpa only [y] using hmulneg s
  have halpha'' : control.tau * ((-g) ⬝ᵥ (-v)) /
      ((-v) ⬝ᵥ (-(control.matrix *ᵥ v))) = α := by
    rw [← Matrix.mulVec_neg v control.matrix]
    exact halpha'
  have hy' : -(control.matrix *ᵥ (α • (-v))) = -y := by
    rw [← Matrix.mulVec_neg (α • (-v)) control.matrix]
    exact hy
  have hnegraw : rawObservableStep H (-g) control =
      (Matrix.inverseDFPUpdate H (-s) (-y), -g + (-y), -s) := by
    simp only [rawObservableStep, hnegv, Matrix.mulVec_neg]
    rw [halpha'', hs, hy']
  rw [hnegraw, hraw]
  have hupdate : Matrix.inverseDFPUpdate H (-s) (-y) =
      Matrix.inverseDFPUpdate H s y := by
    have hnegone : (-1 : ℝ) ≠ 0 := by norm_num
    have hscaled := Matrix.inverseDFPUpdate_smul_pair H s y
      (c := (-1 : ℝ)) hnegone
    have hsneg : (-1 : ℝ) • s = -s := by
      ext i
      simp
    have hyneg : (-1 : ℝ) • y = -y := by
      ext i
      simp
    rw [hsneg, hyneg] at hscaled
    exact hscaled
  rw [hupdate]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · ext i
      simp [add_comm]
    · rfl

/- The punctured physical-to-normal-form comparisons use the same local positivity
   data.  Package it once so each observable bridge can consume one stable condition. -/

/-- The local domain on which both normalized raw steps have their canonical
    positive metric factors and a nonzero low-gradient factor. -/
def mixedRawProjectionDomain (θ : ℝ × ℝ × ℝ) (r : ℝ) : Prop :=
  r ≠ 0 ∧ |θ.1| < (1 / 4 : ℝ) ∧
    0 < (input θ r).2.1 ∧ 0 < (input θ r).2.2 ∧
    0 < (independentRadiusFirstSpectral (θ, r)).1 ∧
    0 < (independentRadiusFirstSpectral (θ, r)).2 ∧
    (independentRadiusFirstGradient (θ, r)).1 ≠ 0

/-- Near every bounded mixed parameter, either the radius is zero or all canonical
    raw-projection side conditions hold simultaneously. -/
lemma mixedRawProjectionDomain_eventually (β B : ℝ) (hβ_small : β < 1 / 4)
    {θ : ℝ × ℝ × ℝ} (hθ : θ ∈ parameterSet β B) :
    ∀ᶠ z in 𝓝 (θ, (0 : ℝ)), z.2 = 0 ∨ mixedRawProjectionDomain z.1 z.2 := by
  -- The parameter-set bound persists under a small perturbation of the base point.
  have hcontrol : |θ.1| < (1 / 4 : ℝ) :=
    parameterSetControlAbsLt β B hβ_small hθ
  have hstrip : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, (0 : ℝ)),
      |z.1.1| < (1 / 4 : ℝ) := by
    have hc : ContinuousAt
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ |z.1.1|) (θ, 0) := by
      fun_prop
    exact hc.eventually (Iio_mem_nhds hcontrol)
  -- Both physical input coordinates remain positive because their base values are two and one.
  have hinput : ContinuousAt
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ input z.1 z.2) (θ, 0) :=
    (input_uncurry_contDiffAt 0 θ).continuousAt
  have hpcont : ContinuousAt
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.1) (θ, 0) :=
    continuousAt_fst.comp (continuousAt_snd.comp hinput)
  have hhcont : ContinuousAt
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.2) (θ, 0) :=
    continuousAt_snd.comp (continuousAt_snd.comp hinput)
  have hp : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      0 < (input z.1 z.2).2.1 := by
    apply hpcont.eventually
    have hbase :
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.1) (θ, 0) = 2 := by
      change (input θ 0).2.1 = 2
      rw [mixedInput_zero]
    rw [hbase]
    exact Ioi_mem_nhds (by norm_num)
  have hh : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      0 < (input z.1 z.2).2.2 := by
    apply hhcont.eventually
    have hbase :
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.2) (θ, 0) = 1 := by
      change (input θ 0).2.2 = 1
      rw [mixedInput_zero]
    rw [hbase]
    exact Ioi_mem_nhds (by norm_num)
  -- Analyticity of the normalized first-step factors keeps both spectral entries positive.
  have hspectral := (independentRadiusFirstSpectral_analyticAt θ).continuousAt
  have hlowCont : ContinuousAt
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusFirstSpectral z).1) (θ, 0) :=
    continuousAt_fst.comp hspectral
  have hhighCont : ContinuousAt
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusFirstSpectral z).2) (θ, 0) :=
    continuousAt_snd.comp hspectral
  have hlow : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      0 < (independentRadiusFirstSpectral z).1 := by
    apply hlowCont.eventually
    have hbase :
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstSpectral z).1) (θ, 0) = 2 := by
      exact congrArg Prod.fst (independentRadiusFirstSpectral_zero θ)
    rw [hbase]
    exact Ioi_mem_nhds (by norm_num)
  have hhigh : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      0 < (independentRadiusFirstSpectral z).2 := by
    apply hhighCont.eventually
    have hbase :
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstSpectral z).2) (θ, 0) = 1 := by
      exact congrArg Prod.snd (independentRadiusFirstSpectral_zero θ)
    rw [hbase]
    exact Ioi_mem_nhds (by norm_num)
  -- The normalized low-gradient factor stays nonzero around its unit base value.
  have hgradient := (independentRadiusFirstGradient_analyticAt θ).continuousAt
  have hgradientLow : ContinuousAt
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        (independentRadiusFirstGradient z).1) (θ, 0) :=
    continuousAt_fst.comp hgradient
  have hnonzero : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      (independentRadiusFirstGradient z).1 ≠ 0 := by
    have hbase :
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstGradient z).1) (θ, 0) = 1 := by
      simp only [independentRadiusFirstGradient_zero]
    have hnear : ∀ᶠ y : ℝ in 𝓝
        ((fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstGradient z).1) (θ, 0)), y ≠ 0 := by
      simpa only [hbase] using eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)
    exact hgradientLow.eventually hnear
  -- Assemble the common certificate, retaining zero as the removable branch.
  filter_upwards [hstrip, hp, hh, hlow, hhigh, hnonzero]
    with z hzstrip hpz hhz hlowz hhighz hnonzeroz
  by_cases hr : z.2 = 0
  · exact Or.inl hr
  · exact Or.inr ⟨hr, hzstrip, hpz, hhz, hlowz, hhighz, hnonzeroz⟩

/-- The first oriented raw frame is orthogonal throughout the punctured normalized
    projection domain. -/
private lemma mixedRawFirstFrame_mul_transpose_of_projectionDomain
    (θ : ℝ × ℝ × ℝ) (r : ℝ) (hdomain : mixedRawProjectionDomain θ r) :
    let H₀ : Matrix (Fin 2) (Fin 2) ℝ :=
      Matrix.diagonal ![(input θ r).2.2 * (input θ r).2.1 * r ^ 2,
        (input θ r).2.2]
    let g₀ : Fin 2 → ℝ := ![(1 : ℝ), (input θ r).2.1 * r]
    let firstStep := rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)
    let firstFrame := OrientedEigenframe.frame
      (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
      (WithLp.toLp 2 firstStep.2.1)
    firstFrame * firstFrame.transpose = 1 := by
  -- Identify the punctured physical step with its normalized first-step data.
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  let p : ℝ := (input θ r).2.1
  let h : ℝ := (input θ r).2.2
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * r ^ 2, h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), p * r]
  have hinitial : H₀.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (mul_pos hh hp) (sq_pos_of_ne_zero hr)
    · exact hh
  have hcontrols := independentRadiusControlMatricesPosDef θ.1 hθ
  have hgradient : g₀ ≠ 0 := by
    intro hzero
    have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
    norm_num [g₀] at hzeroFirst
  have hfirstRaw := independentRawStep_first_eq θ.1 r p h hinitial hcontrols.1
    (TwoPhaseControls.tau_pos θ.1 0) hgradient hr
  let t₁ := independentFirstResiduals θ.1 r p h
  let M₁ := independentFirstMetric θ.1 r p h
  let v₁ := independentFirstGradient θ.1 r p
  let F₁ := EuclideanPlane.frame
    (RealSymmetric2.lowVector (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)
  have hgradientFactors : independentRadiusFirstGradient (θ, r) =
      independentFirstGradientFactors θ.1 r p h := by
    rfl
  have hdenom : RealSymmetric2.lowDenom
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    intro hzero
    apply hQ
    rw [hgradientFactors]
    unfold independentFirstGradientFactors
    dsimp only
    rw [hzero]
    simp
  have hspecial : F₁ ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    exact RealSymmetric2.frame_mem_specialOrthogonalGroup_of_lowDenom_ne_zero
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 hdenom
  have hfixedOrth : F₁ * F₁.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp
      (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hmetric : (rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)).1 = M₁ := by
    calc
      (rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)).1 =
          (independentRawStep H₀ g₀ (TwoPhaseControls.first θ.1)).1 :=
        mixedRawObservableStep_metric_eq H₀ g₀ (TwoPhaseControls.first θ.1)
      _ = M₁ := congrArg Prod.fst hfirstRaw
  have hupdatedGradient :
      (rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)).2.1 = v₁ := by
    calc
      (rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)).2.1 =
          (independentRawStep H₀ g₀ (TwoPhaseControls.first θ.1)).2 :=
        mixedRawObservableStep_gradient_eq H₀ g₀ (TwoPhaseControls.first θ.1)
      _ = v₁ := congrArg Prod.snd hfirstRaw
  -- Orientation changes the fixed unit frame by at most one global sign.
  have hframe :
      OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1)
          (WithLp.toLp 2 v₁) = F₁ ∨
        OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1)
          (WithLp.toLp 2 v₁) = -F₁ := by
    rcases orientedEigenframe_eq_fixed_or_neg (M₁ 0 0) (M₁ 0 1) (M₁ 1 1)
      (WithLp.toLp 2 v₁) with hframe | hframe
    · left
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
    · right
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
  dsimp only
  change
    let firstStep := rawObservableStep H₀ g₀ (TwoPhaseControls.first θ.1)
    let firstFrame := OrientedEigenframe.frame
      (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
      (WithLp.toLp 2 firstStep.2.1)
    firstFrame * firstFrame.transpose = 1
  dsimp only
  rw [hmetric, hupdatedGradient]
  rcases hframe with hframe | hframe
  · rwa [hframe]
  · rw [hframe]
    simpa only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
      hfixedOrth

/- The canonical low-gradient path is already analytic and has the required quadratic
   coefficient.  Record its coefficient germ separately so the remaining physical
   projection obligation is isolated to an eventual equality. -/

/-- The canonical second-leg low-gradient coordinate has the displayed uniform truncated germ. -/
lemma mixedIndependentSecondGradientLow_truncatedGerm
    {K : Set (ℝ × ℝ × ℝ)} :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ (independentRadiusSecondGradient (θ, r)).1)
      K 3
      (fun n θ ↦
        (![1, 0,
          (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) := by
  -- Reuse the parent-independent generic germ interface; the physical bridge is
  -- deliberately kept separate from this canonical analytic calculation.
  exact independentRadiusSecondGradientLow_truncatedGerm_generic

/- The center residual uses the same normalized displacement factors as the
   independent-radius evaluator.  Naming this scalar bracket gives the
   quotient-bound infrastructure a stable, division-free interface. -/

/-- The normalized mixed center bracket built from the canonical first frame and the
    two radius-normalized displacements. -/
def mixedCenterBracket (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  let b := θ.1
  let p := (input θ r).2.1
  let m := independentRadiusFirstMetricTriple (θ, r)
  let F := EuclideanPlane.frame (RealSymmetric2.lowVector m.1 m.2.1 m.2.2)
  let L := (independentRadiusFirstSpectral (θ, r)).1
  let H := (independentRadiusFirstSpectral (θ, r)).2
  let Q := (independentRadiusFirstGradient (θ, r)).1
  let U := (independentRadiusFirstGradient (θ, r)).2
  let β₂ := r * L * Q * (r * L * Q - 2 * b * H * U) +
    H * U * (H * U - 2 * b * r * L * Q)
  let u₀ : Fin 2 → ℝ :=
    (-(2 / 3 : ℝ) * (p + 1) / (1 + 2 * b * r + r ^ 2)) •
      (![r, 1] : Fin 2 → ℝ)
  let u₁ : Fin 2 → ℝ :=
    (-(1 / 3 : ℝ) * (L * Q ^ 2 + H * U ^ 2) / β₂) •
      (![r * L * Q, H * U] : Fin 2 → ℝ)
  (-(u₀ 1) + 2 * (F 0 0 * u₁ 1 + F 0 1 * u₁ 0))

/-- The normalized mixed center bracket vanishes at the removable zero-radius base. -/
lemma mixedCenterBracket_zero (θ : ℝ × ℝ × ℝ) :
    mixedCenterBracket θ 0 = 0 := by
  simp [mixedCenterBracket, independentRadiusFirstMetricTriple_zero,
    independentRadiusFirstSpectral_zero, independentRadiusFirstGradient_zero,
    input, EuclideanPlane.frame, RealSymmetric2.lowVector, RealSymmetric2.lowRaw,
    RealSymmetric2.low, RealSymmetric2.lowDenom, RealSymmetric2.lowRaw,
    RealSymmetric2.gap]
  ring

/-- Simultaneously negating an oriented frame and its second displacement leaves the
    weighted center bracket unchanged. -/
lemma weightedCenterBracket_neg_neg
    (F : Matrix (Fin 2) (Fin 2) ℝ) (u₀ u₁ : Fin 2 → ℝ) :
    weightedCenterBracket (-F) u₀ (-u₁) = weightedCenterBracket F u₀ u₁ := by
  -- The first summand is unchanged, while both matrix and vector signs cancel
  -- in the transported second summand.
  ext i
  fin_cases i <;>
    simp [weightedCenterBracket, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    <;> ring

/- The pointwise projection neighborhoods are uniformized over the compact parameter
   set before any raw certificate is assembled. -/

/-- A bounded mixed parameter set admits one common radius tube for the raw projection
    side conditions. -/
lemma mixedRawProjectionDomain_uniformTube
    (β B : ℝ) (hβ_small : β < 1 / 4) (_hB : 0 ≤ B) :
    ∃ δ₀ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ₀ →
      r = 0 ∨ mixedRawProjectionDomain θ r := by
  -- Swap the product coordinates so the compactness lemma controls the radius.
  have hpointwise : ∀ θ ∈ parameterSet β B,
      ∀ᶠ z : ℝ × (ℝ × ℝ × ℝ) in 𝓝 (0, θ),
        z.1 = 0 ∨ mixedRawProjectionDomain z.2 z.1 := by
    intro θ hθ
    have hlocal := mixedRawProjectionDomain_eventually β B hβ_small hθ
    rw [nhds_swap]
    change ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
      z.2 = 0 ∨ mixedRawProjectionDomain z.1 z.2
    exact hlocal
  obtain ⟨δ₀, hδ₀, htube⟩ :=
    FiniteTaylorJet.compactFiberNormRadius
      (X := ℝ) (Y := ℝ × ℝ × ℝ)
      (P := fun r θ ↦ r = 0 ∨ mixedRawProjectionDomain θ r)
      (parameterSet_isCompact β B) hpointwise
  refine ⟨δ₀, hδ₀, ?_⟩
  intro θ hθ r hr
  simpa only [Real.norm_eq_abs] using htube θ hθ r hr

/-- The first raw-step denominator is strictly positive on the punctured projection
    domain, so the first normalized displacement can be used without a removable
    denominator branch. -/
lemma mixedFirstDisplacement_denominator_pos
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hdomain : mixedRawProjectionDomain θ r) :
    0 < 1 + 2 * θ.1 * r + r ^ 2 := by
  rcases hdomain with ⟨_, hb, _, _, _, _, _⟩
  rcases (abs_lt.mp hb) with ⟨hbneg, hbpos⟩
  nlinarith [sq_nonneg (r + θ.1)]

/-- The explicit second-leg denominator is positive on the punctured projection
    domain, by the abstract secant-step preconditioned energy. -/
private lemma mixedSecondDisplacement_denominator_pos
    {θ : ℝ × ℝ × ℝ} {r : ℝ}
    (hdomain : mixedRawProjectionDomain θ r) :
    0 < r * (independentRadiusFirstSpectral (θ, r)).1 *
          (independentRadiusFirstGradient (θ, r)).1 *
          (r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1 -
            2 * θ.1 * (independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2) +
        (independentRadiusFirstSpectral (θ, r)).2 *
          (independentRadiusFirstGradient (θ, r)).2 *
          ((independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2 -
            2 * θ.1 * r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1) := by
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  let L := (independentRadiusFirstSpectral (θ, r)).1
  let H := (independentRadiusFirstSpectral (θ, r)).2
  let Q := (independentRadiusFirstGradient (θ, r)).1
  let U := (independentRadiusFirstGradient (θ, r)).2
  have hdiag : (Matrix.diagonal ![r ^ 2 * L, H] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (sq_pos_of_ne_zero hr) hL
    · exact hH
  have hg : (![Q, r * U] : Fin 2 → ℝ) ≠ 0 := by
    intro hz
    have hz0 := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hz
    exact hQ (by simpa [Q] using hz0)
  have hcontrols := independentRadiusControlMatricesPosDef θ.1 hθ
  let z := DFP.AbstractSecantStep.ofMatrices
    (Matrix.diagonal ![r ^ 2 * L, H]) (![Q, r * U] : Fin 2 → ℝ)
    (TwoPhaseControls.second θ.1).matrix (TwoPhaseControls.second θ.1).tau
    hdiag hcontrols.2 (TwoPhaseControls.tau_pos θ.1 1) hg
  have henergy := z.preconditionedEnergy_pos
  have hidentity :
      z.preconditionedGradient ⬝ᵥ
          (z.secantMatrix *ᵥ z.preconditionedGradient) =
        r ^ 2 * (r * L * Q * (r * L * Q - 2 * θ.1 * H * U) +
          H * U * (H * U - 2 * θ.1 * r * L * Q)) := by
    rw [z.preconditionedGradient_def]
    simp [z, DFP.AbstractSecantStep.ofMatrices, TwoPhaseControls.second_matrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hβ : 0 < r * L * Q * (r * L * Q - 2 * θ.1 * H * U) +
      H * U * (H * U - 2 * θ.1 * r * L * Q) := by
    rw [hidentity] at henergy
    exact pos_of_mul_pos_right henergy (sq_nonneg r)
  dsimp [L, H, Q, U] at hβ ⊢
  exact hβ

/- The removable observable base is recorded locally because the physical-drift file
   cannot import its downstream zero-radius companion without creating a cycle. -/

/-- The mixed physical projection tuple at radius zero is `(1, 0, 0)`. -/
private lemma mixedObservable_zeroRadiusProjectionData (b : ℝ) :
    ((observableMap b (0, 2, 1)).amplitudeRatio,
      (observableMap b (0, 2, 1)).frameAngleIncrement,
      (observableMap b (0, 2, 1)).fullCenterDisplacement) = (1, 0, 0) := by
  -- Both raw steps are stationary at the diagonal base; the frame then reduces to identity.
  dsimp [observableMap]
  norm_num
  have hstep₁ :
      rawObservableStep (Matrix.diagonal ![(0 : ℝ), 1]) ![(1 : ℝ), 0]
          (TwoPhaseControls.first b) =
        (Matrix.diagonal ![(0 : ℝ), 1], ![(1 : ℝ), 0], 0) := by
    simpa using rawObservableStep_zeroRadius_scaled 1 1 2 (TwoPhaseControls.first b)
  simp_rw [hstep₁]
  have hframe₁ :
      OrientedEigenframe.frame
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 0)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 1)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 1 1)
          (WithLp.toLp 2 ![(1 : ℝ), 0]) = 1 := by
    simpa [Matrix.diagonal_apply, Fin.isValue] using orientedEigenframe_zeroRadius_frame
  simp_rw [hframe₁]
  have hstep₂ :
      rawObservableStep
          ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose *
            Matrix.diagonal ![(0 : ℝ), 1] * 1)
          ((1 : Matrix (Fin 2) (Fin 2) ℝ).transpose *ᵥ ![(1 : ℝ), 0])
          (TwoPhaseControls.second b) =
        (Matrix.diagonal ![(0 : ℝ), 1], ![(1 : ℝ), 0], 0) := by
    rw [rawObservableStep_identity_conjugation]
    exact rawObservableStep_zeroRadius_base (TwoPhaseControls.second b)
  simp_rw [hstep₂, hframe₁]
  simp [EuclideanPlane.SignedAngle.coordinate_one]

/-- The independent raw amplitude has its unit removable value at radius zero. -/
private lemma mixedIndependentRawAmplitude_zeroRadius (b : ℝ) :
    mixedIndependentRawAmplitude b 0 2 1 = 1 := by
  have hprojection := mixedObservable_zeroRadiusProjectionData b
  have hamp : (observableMap b (0, 2, 1)).amplitudeRatio = 1 := by
    exact congrArg Prod.fst hprojection
  have hraw := mixedObservable_amplitude_eq_independentRaw b 0 2 1
  calc
    mixedIndependentRawAmplitude b 0 2 1 =
        (observableMap b (0, 2, 1)).amplitudeRatio := hraw.symm
    _ = 1 := hamp

/-- The physical center residual vanishes at zero radius. -/
private lemma mixedObservable_zeroRadiusCenterResidual (θ : ℝ × ℝ × ℝ) :
    (observableMap θ.1 (input θ 0)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * (0 : ℝ) ^ 2 = 0 := by
  -- Reduce the canonical input to the stationary base and project the stored tuple.
  have hinput : input θ 0 = (0, 2, 1) := by
    simp [input]
  have hprojection := mixedObservable_zeroRadiusProjectionData θ.1
  have hcenter :
      (observableMap θ.1 (0, 2, 1)).fullCenterDisplacement 0 = 0 :=
    congrArg (fun t : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) ↦ t.2.2 0)
      hprojection
  rw [hinput, hcenter]
  simp

/- The denominator-cleared factorization is purely branch algebra once the two
   removable identities and the punctured formula are supplied. -/

/-- Zero-control, zero-radius, and punctured residual identities imply an
    unconditional cubic factorization. -/
lemma centerResidual_factorization_of_removable_branches
    {Q : (ℝ × ℝ × ℝ) → ℝ → ℝ}
    (hscale : ∀ θ r, θ.1 = 0 →
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2 = 0)
    (hradius : ∀ θ,
      (observableMap θ.1 (input θ 0)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * (0 : ℝ) ^ 2 = 0)
    (hpunctured : ∀ θ r, θ.1 ≠ 0 → r ≠ 0 →
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        centerDriftCoefficient θ * r ^ 2 =
      (θ.1 * r ^ (3 : ℕ)) • Q θ r) :
    ∀ θ r,
      (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2 =
        (θ.1 * r ^ (3 : ℕ)) • Q θ r := by
  intro θ r
  by_cases hθ : θ.1 = 0
  · rw [hscale θ r hθ, hθ]
    simp
  · by_cases hr : r = 0
    · subst r
      rw [hradius θ]
      simp
    · exact hpunctured θ r hθ hr

/- The remaining physical projection bridge is not supplied by the imported normal-form API. -/

/-- The scalar tangent quotient of the fixed low-frame product obtained from the two
    normalized metric triples. -/
private def mixedCanonicalFrameSlope (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  let z := (θ, r)
  let m₁ := independentRadiusFirstMetricTriple z
  let m₂ := independentRadiusSecondMetricTriple z
  let e₁ := m₁.2.1
  let x₁ := m₁.2.2 - z.2 ^ 2 * (independentRadiusFirstSpectral z).1
  let e₂ := m₂.2.1
  let x₂ := m₂.2.2 - z.2 ^ 2 * (independentRadiusSecondSpectral z).1
  (-(e₁ * x₂ + x₁ * e₂) / (x₁ * x₂ - e₁ * e₂))

/-- The tangent quotient of two fixed low-vector frames is expressed by their
    off-diagonal entries and low-frame gaps. -/
private lemma mixedCanonicalFrameSlope_eq_lowVectorQuotient
    (a₁ b₁ d₁ a₂ b₂ d₂ : ℝ)
    (h₁ : RealSymmetric2.lowDenom a₁ b₁ d₁ ≠ 0)
    (h₂ : RealSymmetric2.lowDenom a₂ b₂ d₂ ≠ 0) :
    (EuclideanPlane.frame (RealSymmetric2.lowVector a₁ b₁ d₁) *
        EuclideanPlane.frame (RealSymmetric2.lowVector a₂ b₂ d₂)) 1 0 /
      (EuclideanPlane.frame (RealSymmetric2.lowVector a₁ b₁ d₁) *
        EuclideanPlane.frame (RealSymmetric2.lowVector a₂ b₂ d₂)) 0 0 =
      (-(b₁ * (d₂ - RealSymmetric2.low a₂ b₂ d₂) +
          (d₁ - RealSymmetric2.low a₁ b₁ d₁) * b₂) /
        ((d₁ - RealSymmetric2.low a₁ b₁ d₁) *
            (d₂ - RealSymmetric2.low a₂ b₂ d₂) - b₁ * b₂)) := by
  -- Expand the two low-vector frames only at this small algebraic interface.
  unfold EuclideanPlane.frame
  simp only [Matrix.mul_apply, Fin.sum_univ_two, EuclideanPlane.perp_apply,
    RealSymmetric2.lowVector, RealSymmetric2.lowRaw, PiLp.smul_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  field_simp [h₁, h₂]
  ring

/-- The lower-left/upper-left slope is unchanged by a nonzero global scalar sign. -/
private lemma mixedFrameSlope_smul_invariant
    (σ : ℝ) (hσ : σ ≠ 0) (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : M 0 0 ≠ 0) :
    (σ • M) 1 0 / (σ • M) 0 0 = M 1 0 / M 0 0 := by
  -- Cancel the common nonzero scalar after exposing matrix scalar application.
  simp only [smul_eq_mul, Matrix.smul_apply]
  field_simp [hσ, hM]

/-- The raw relative-frame matrix is the product of the two oriented frames used by
    the independent evaluator. -/
private def mixedRawFrameAngleMatrix (b r p h : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * r ^ 2, h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), p * r]
  let firstStep := independentRawStep H₀ g₀ (TwoPhaseControls.first b)
  let firstFrame := OrientedEigenframe.frame
    (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
    (WithLp.toLp 2 firstStep.2)
  let H₁ := firstFrame.transpose * firstStep.1 * firstFrame
  let g₁ := firstFrame.transpose *ᵥ firstStep.2
  let secondStep := independentRawStep H₁ g₁ (TwoPhaseControls.second b)
  let secondFrame := OrientedEigenframe.frame
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
    (WithLp.toLp 2 secondStep.2)
  firstFrame * secondFrame

/-- The raw relative-frame slope is its lower-left entry divided by its upper-left
    entry. -/
private def mixedRawFrameAngleSlope (b r p h : ℝ) : ℝ :=
  let M := mixedRawFrameAngleMatrix b r p h
  M 1 0 / M 0 0

/-- The signed raw frame angle is the arctangent of the scalar relative-frame slope. -/
private lemma mixedRawFrameAngle_eq_arctan_slope (b r p h : ℝ) :
    mixedIndependentRawFrameAngle b r p h =
      Real.arctan (mixedRawFrameAngleSlope b r p h) := by
  simp only [mixedIndependentRawFrameAngle, mixedRawFrameAngleSlope,
    mixedRawFrameAngleMatrix, EuclideanPlane.SignedAngle.coordinate]

/-- The raw relative-frame slope along the canonical mixed input path is the scalar
    chart used by the angle germ. -/
private def mixedRawFrameAngleSlopeAlongInput
    (θ : ℝ × ℝ × ℝ) (r : ℝ) : ℝ :=
  mixedRawFrameAngleSlope θ.1 r
    (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)

/-- The canonical raw frame angle is the arctangent of the pathwise relative-frame
    slope. -/
private lemma mixedRawFrameAngleAlongInput_eq_arctan_slope
    (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    mixedIndependentRawFrameAngle θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r) =
      Real.arctan (mixedRawFrameAngleSlopeAlongInput θ r) := by
  exact mixedRawFrameAngle_eq_arctan_slope θ.1 r
    (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)

/-- The raw relative-frame angle vanishes at the removable zero-radius base. -/
private lemma mixedRawFrameAngle_zero (b : ℝ) :
    mixedIndependentRawFrameAngle b 0 2 1 = 0 := by
  unfold mixedIndependentRawFrameAngle
  dsimp only
  have hH :
      Matrix.diagonal ![(1 : ℝ) * 2 * (0 : ℝ) ^ 2, 1] =
        Matrix.diagonal ![(0 : ℝ), 1] := by
    simp
  have hg : (![1, (2 : ℝ) * 0] : Fin 2 → ℝ) = ![(1 : ℝ), 0] := by
    ext i
    fin_cases i <;> simp
  rw [hH, hg, independentRawStep_zeroRadius_base]
  have hframe :
      OrientedEigenframe.frame
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 0)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 0 1)
          ((Matrix.diagonal ![(0 : ℝ), 1]) 1 1)
          (WithLp.toLp 2 ![(1 : ℝ), 0]) = 1 := by
    simpa [Matrix.diagonal_apply, Fin.isValue] using orientedEigenframe_zeroRadius_frame
  rw [hframe, independentRawStep_zeroRadius_conjugated, hframe]
  simp [EuclideanPlane.SignedAngle.coordinate_one]

/-- The pathwise raw relative-frame slope vanishes at radius zero. -/
private lemma mixedRawFrameAngleSlopeAlongInput_zero
    (θ : ℝ × ℝ × ℝ) :
    mixedRawFrameAngleSlopeAlongInput θ 0 = 0 := by
  have hangle := mixedRawFrameAngle_zero θ.1
  have hangleSlope := mixedRawFrameAngle_eq_arctan_slope θ.1 0 2 1
  have hslope : mixedRawFrameAngleSlope θ.1 0 2 1 = 0 := by
    have harctan : Real.arctan (mixedRawFrameAngleSlope θ.1 0 2 1) = 0 := by
      rw [← hangleSlope]
      exact hangle
    exact Real.arctan_eq_zero_iff.mp harctan
  simpa [mixedRawFrameAngleSlopeAlongInput] using hslope

/-- An analytic independent-radius path restricts to a twice continuously differentiable
    radius slice at each fixed parameter. -/
private theorem mixedRadiusSlice_contDiffAt_of_analyticAt
    {F : ((ℝ × ℝ × ℝ) × ℝ) → ℝ}
    (θ : ℝ × ℝ × ℝ) (hF : AnalyticAt ℝ F (θ, 0)) :
    ContDiffAt ℝ 2 (fun r : ℝ ↦ F (θ, r)) 0 := by
  have hpath : AnalyticAt ℝ
      (fun r : ℝ ↦ (θ, r)) 0 := by
    fun_prop
  exact (hF.comp hpath).contDiffAt (n := 2)

/- The raw frame quotient is compared to the canonical quotient only after both
   raw steps have been rewritten in their normalized fixed-frame coordinates. -/

/-- The raw relative-frame slope agrees with the normalized fixed-frame quotient
    on the punctured projection domain. -/
private lemma mixedRawFrameAngleSlope_eq_canonical_of_projectionDomain
    (θ : ℝ × ℝ × ℝ) (r : ℝ) (hdomain : mixedRawProjectionDomain θ r)
    (hGlo : 0 < (independentRadiusSecondGradient (θ, r)).1) :
    mixedRawFrameAngleSlopeAlongInput θ r = mixedCanonicalFrameSlope θ r := by
  -- The domain certificate supplies the nonzero radius, positive input metric,
  -- first-step spectral data, and the first low-gradient denominator.
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  let p : ℝ := (input θ r).2.1
  let h : ℝ := (input θ r).2.2
  have hrSq : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hinitial : (Matrix.diagonal ![h * p * r ^ 2, h] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (mul_pos hh hp) hrSq
    · exact hh
  have hcontrols := independentRadiusControlMatricesPosDef θ.1 hθ
  have htauFirst : 0 < (TwoPhaseControls.first θ.1).tau :=
    TwoPhaseControls.tau_pos θ.1 0
  have hgradientFirst : (![(1 : ℝ), p * r] : Fin 2 → ℝ) ≠ 0 := by
    intro hzero
    have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
    norm_num at hzeroFirst
  have hfirstRaw := independentRawStep_first_eq θ.1 r p h hinitial hcontrols.1
    htauFirst hgradientFirst hr
  let t₁ := independentFirstResiduals θ.1 r p h
  let M₁ := independentFirstMetric θ.1 r p h
  let v₁ := independentFirstGradient θ.1 r p
  let F₁ := EuclideanPlane.frame
    (RealSymmetric2.lowVector (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)
  let L := (independentRadiusFirstSpectral (θ, r)).1
  let H := (independentRadiusFirstSpectral (θ, r)).2
  let Q := (independentRadiusFirstGradient (θ, r)).1
  let U := (independentRadiusFirstGradient (θ, r)).2
  have hspectralFirst : independentRadiusFirstSpectral (θ, r) =
      independentFirstSpectralFactors θ.1 r p h := by
    rfl
  have hgradientFactorsFirst : independentRadiusFirstGradient (θ, r) =
      independentFirstGradientFactors θ.1 r p h := by
    rfl
  have hdenomFirst : RealSymmetric2.lowDenom
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    intro hzero
    apply hQ
    rw [hgradientFactorsFirst]
    unfold independentFirstGradientFactors
    dsimp only
    rw [hzero]
    simp
  have hhighFirst : RealSymmetric2.high
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    have hpositive : 0 < RealSymmetric2.high
        (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 := by
      simpa [H, hspectralFirst, independentFirstSpectralFactors, t₁] using hH
    exact ne_of_gt hpositive
  have hlowFirst : RealSymmetric2.low
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 = r ^ 2 * L := by
    rw [low_eq_radiusSq_mul_detFactor r t₁.1 t₁.2.1 t₁.2.2 hhighFirst]
    simp [L, hspectralFirst, independentFirstSpectralFactors, t₁]
  have hdiagFixedFirst : F₁.transpose * M₁ * F₁ =
      Matrix.diagonal ![r ^ 2 * L, H] := by
    have hmetricFirst : M₁ = RealSymmetric2.matrix
        (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hdiag := RealSymmetric2.frame_diagonalizes_of_lowDenom_ne_zero
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 hdenomFirst
    rw [hmetricFirst, hdiag]
    simp [L, H, hspectralFirst, independentFirstSpectralFactors, t₁, hlowFirst]
  have hgradFixedFirst : F₁.transpose.mulVec v₁ = ![Q, r * U] := by
    have hcoords := lowFrame_transpose_mulVec
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2
      (independentFirstGradientResiduals θ.1 r p).1
      (r * (independentFirstGradientResiduals θ.1 r p).2)
    rw [show F₁.transpose.mulVec v₁ =
        (EuclideanPlane.frame (RealSymmetric2.lowVector
          (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)).transpose.mulVec
          ![(independentFirstGradientResiduals θ.1 r p).1,
            r * (independentFirstGradientResiduals θ.1 r p).2] by rfl]
    rw [hcoords]
    ext i
    fin_cases i <;>
      simp [Q, U, hgradientFactorsFirst, independentFirstGradientFactors, t₁] <;>
      ring
  have hframeFirst :
      OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1) (WithLp.toLp 2 v₁) = F₁ ∨
        OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1) (WithLp.toLp 2 v₁) = -F₁ := by
    rcases orientedEigenframe_eq_fixed_or_neg (M₁ 0 0) (M₁ 0 1) (M₁ 1 1)
      (WithLp.toLp 2 v₁) with hframe | hframe
    · left
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
    · right
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
  -- The second raw step is canonical after the first-frame sign is accounted for.
  let t₂ := independentSecondResiduals θ.1 r L H Q U
  let M₂ := independentSecondMetric θ.1 r L H Q U
  let v₂ := independentSecondGradient θ.1 r L H Q U
  let S := (independentRadiusSecondSpectral (θ, r)).1
  let T := (independentRadiusSecondSpectral (θ, r)).2
  let Glo := (independentRadiusSecondGradient (θ, r)).1
  let Ghi := (independentRadiusSecondGradient (θ, r)).2
  have hdiagSecond : (Matrix.diagonal ![r ^ 2 * L, H] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos hrSq hL
    · exact hH
  have hgradientSecond : (![(1 : ℝ) • Q, (1 : ℝ) • (r * U)] : Fin 2 → ℝ) ≠ 0 := by
    intro hzero
    have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
    apply hQ
    simpa [Q] using hzeroFirst
  have hsecondRawPos := independentRawStep_second_eq θ.1 r L H Q U 1
    hdiagSecond hcontrols.2 (TwoPhaseControls.tau_pos θ.1 1)
    (by simpa using hgradientSecond) hr
  have hsecondRawCanonical :
      independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
          (![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1) = (M₂, v₂) := by
    simpa [M₂, v₂] using hsecondRawPos
  have hmetricSecond : M₂ = RealSymmetric2.matrix
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hgradFixedSecond :
      (EuclideanPlane.frame (RealSymmetric2.lowVector
        (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)).transpose.mulVec v₂ =
          ![Glo, r * Ghi] := by
    have hcoords := lowFrame_transpose_mulVec
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2
      (independentSecondGradientResiduals θ.1 r L H Q U).1
      (r * (independentSecondGradientResiduals θ.1 r L H Q U).2)
    rw [show (EuclideanPlane.frame (RealSymmetric2.lowVector
        (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)).transpose.mulVec v₂ =
        (EuclideanPlane.frame (RealSymmetric2.lowVector
        (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)).transpose.mulVec
          ![(independentSecondGradientResiduals θ.1 r L H Q U).1,
            r * (independentSecondGradientResiduals θ.1 r L H Q U).2] by rfl]
    rw [hcoords]
    ext i
    fin_cases i <;>
      simp [Glo, Ghi, independentRadiusSecondGradient,
        independentSecondGradientFactors, t₂] <;> ring
  have hgradientFactorsSecond : independentRadiusSecondGradient (θ, r) =
      independentSecondGradientFactors θ.1 r L H Q U := by
    rfl
  have hdenomSecond : RealSymmetric2.lowDenom
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 ≠ 0 := by
    intro hzero
    have hGloEq : Glo = 0 := by
      change (independentRadiusSecondGradient (θ, r)).1 = 0
      rw [hgradientFactorsSecond]
      unfold independentSecondGradientFactors
      dsimp only
      rw [hzero]
      simp
    exact (ne_of_gt hGlo) hGloEq
  have hM₂pos : M₂.PosDef := by
    have hrawPos := independentRawStep_metric_posDef
      (Matrix.diagonal ![r ^ 2 * L, H]) (![Q, r * U] : Fin 2 → ℝ)
      (TwoPhaseControls.second θ.1) hdiagSecond hcontrols.2
      (TwoPhaseControls.tau_pos θ.1 1) (by simpa using hgradientSecond)
    have hmetricRaw :
        (independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
          (![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1)).1 = M₂ := by
      simpa using congrArg Prod.fst hsecondRawCanonical
    rw [← hmetricRaw]
    exact hrawPos
  have hhighSecondPos : 0 < RealSymmetric2.high
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 := by
    have hmatrixSecond : M₂ = RealSymmetric2.matrix
        (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 := by
      exact hmetricSecond
    apply realSymmetric2_high_pos_of_posDef
    rw [← hmatrixSecond]
    simpa [M₂, independentSecondMetric, t₂]
  have hhighSecond : RealSymmetric2.high
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 ≠ 0 := ne_of_gt hhighSecondPos
  have hspectralSecond : independentRadiusSecondSpectral (θ, r) =
      independentSecondSpectralFactors θ.1 r L H Q U := by
    rfl
  have hlowSecond : RealSymmetric2.low
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 = r ^ 2 * S := by
    rw [low_eq_radiusSq_mul_detFactor r t₂.1 t₂.2.1 t₂.2.2 hhighSecond]
    simp [S, hspectralSecond, independentSecondSpectralFactors, t₂]
  let F₂ := EuclideanPlane.frame (RealSymmetric2.lowVector
    (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)
  have hframeSecond :
      OrientedEigenframe.frame (M₂ 0 0) (M₂ 0 1) (M₂ 1 1) (WithLp.toLp 2 v₂) =
          F₂ ∨
      OrientedEigenframe.frame (M₂ 0 0) (M₂ 0 1) (M₂ 1 1) (WithLp.toLp 2 v₂) =
          -F₂ := by
    rcases orientedEigenframe_eq_fixed_or_neg (M₂ 0 0) (M₂ 0 1) (M₂ 1 1)
      (WithLp.toLp 2 v₂) with hframe | hframe
    · left
      simpa [F₂, M₂, independentSecondMetric, t₂] using hframe
    · right
      simpa [F₂, M₂, independentSecondMetric, t₂] using hframe
  have hframeSecondNeg :
      OrientedEigenframe.frame (M₂ 0 0) (M₂ 0 1) (M₂ 1 1)
          (WithLp.toLp 2 (-v₂)) = F₂ ∨
      OrientedEigenframe.frame (M₂ 0 0) (M₂ 0 1) (M₂ 1 1)
          (WithLp.toLp 2 (-v₂)) = -F₂ := by
    rcases orientedEigenframe_eq_fixed_or_neg (M₂ 0 0) (M₂ 0 1) (M₂ 1 1)
      (WithLp.toLp 2 (-v₂)) with hframe | hframe
    · left
      simpa [F₂, M₂, independentSecondMetric, t₂] using hframe
    · right
      simpa [F₂, M₂, independentSecondMetric, t₂] using hframe
  have hfixed := mixedCanonicalFrameSlope_eq_lowVectorQuotient
    (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2
    (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 hdenomFirst hdenomSecond
  have hfixed' :
      (F₁ * F₂) 1 0 / (F₁ * F₂) 0 0 = mixedCanonicalFrameSlope θ r := by
    have hm1 : independentRadiusFirstMetricTriple (θ, r) =
        (r ^ 2 * t₁.1, r * t₁.2.1, t₁.2.2) := by
      rfl
    unfold mixedCanonicalFrameSlope
    dsimp only
    rw [hm1]
    rw [independentRadiusSecondMetricTriple_eq]
    rw [hlowFirst, hlowSecond] at hfixed
    simpa [F₁, F₂, t₁, t₂, L, H, Q, U, S, T, Glo, Ghi] using hfixed
  change mixedRawFrameAngleSlope θ.1 r p h = mixedCanonicalFrameSlope θ r
  unfold mixedRawFrameAngleSlope mixedRawFrameAngleMatrix
  dsimp only
  rw [hfirstRaw]
  rcases hframeFirst with hfirst | hfirst
  · rw [hfirst, hdiagFixedFirst, hgradFixedFirst, hsecondRawCanonical]
    rcases hframeSecond with hsecond | hsecond
    · rw [hsecond]
      exact hfixed'
    · rw [hsecond]
      have hsign :
          (F₁ * -F₂) =
            (-1 : ℝ) •
              (F₁ * F₂) := by
        ext i j
        simp [Matrix.smul_apply]
      rw [hsign]
      by_cases h00 :
          (F₁ * F₂) 0 0 = 0
      · simpa [h00] using hfixed'
      · exact mixedFrameSlope_smul_invariant (-1) (by norm_num) _ h00 |>.trans hfixed'
  · have hdiagNeg :
        (-F₁).transpose * M₁ * (-F₁) = Matrix.diagonal ![r ^ 2 * L, H] := by
      simpa only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
        hdiagFixedFirst
    have hgradNeg : (-F₁).transpose.mulVec v₁ = -![Q, r * U] := by
      rw [Matrix.transpose_neg, Matrix.neg_mulVec, hgradFixedFirst]
    have hgradientSecondNeg :
        ((-1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ) ≠ 0 := by
      intro hzero
      have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
      apply hQ
      simpa [Q] using hzeroFirst
    have hsecondRawNeg := independentRawStep_second_eq θ.1 r L H Q U (-1)
      hdiagSecond hcontrols.2 (TwoPhaseControls.tau_pos θ.1 1)
      hgradientSecondNeg hr
    have hsecondRawNeg' :
        independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
            (-![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1) =
          (M₂, -v₂) := by
      simpa [M₂, v₂] using hsecondRawNeg
    rw [hfirst, hdiagNeg, hgradNeg, hsecondRawNeg']
    rcases hframeSecondNeg with hsecond | hsecond
    · rw [hsecond]
      have hsign :
          ((-F₁) * F₂) =
            (-1 : ℝ) • (F₁ * F₂) := by
        ext i j
        simp
      rw [hsign]
      by_cases h00 :
          (F₁ * F₂) 0 0 = 0
      · simpa [h00] using hfixed'
      · exact mixedFrameSlope_smul_invariant (-1) (by norm_num) _ h00 |>.trans hfixed'
    · rw [hsecond]
      have hsign : (-F₁ * -F₂) = F₁ * F₂ := by
        ext i j
        simp
      rw [hsign]
      exact hfixed'

/-- The raw relative-frame slope is twice continuously differentiable at the
    removable base and has radius derivative `-3`. -/
private lemma mixedRawFrameAngleSlopeJet
    (β B : ℝ) (hβ_small : β < 1 / 4) :
    ∀ θ, θ ∈ parameterSet β B →
      ContDiffAt ℝ 2
          (Function.uncurry mixedRawFrameAngleSlopeAlongInput) (θ, 0) ∧
        deriv (mixedRawFrameAngleSlopeAlongInput θ) 0 = -3 := by
  intro θ hθ
  -- Build the joint analytic quotient before restricting to a radius slice.
  have hfirstMetric := independentRadiusFirstMetricTriple_analyticAt θ
  have hfirstMetricE : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusFirstMetricTriple z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hfirstMetric)
  have hfirstMetricD : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusFirstMetricTriple z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hfirstMetric)
  have hfirstSpectral := independentRadiusFirstSpectral_analyticAt θ
  have hfirstSpectralLow : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusFirstSpectral z).1) (θ, 0) :=
    analyticAt_fst.comp hfirstSpectral
  have hsecondMetric := independentRadiusSecondMetricTriple_analyticAt θ
  have hsecondMetricE : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusSecondMetricTriple z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hsecondMetric)
  have hsecondMetricD : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusSecondMetricTriple z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hsecondMetric)
  have hsecondSpectral := independentRadiusSecondSpectral_analyticAt θ
  have hsecondSpectralLow : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusSecondSpectral z).1) (θ, 0) :=
    analyticAt_fst.comp hsecondSpectral
  have hradius : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦ z.2) (θ, 0) := analyticAt_snd
  have hfirstX : AnalyticAt ℝ
      (fun z ↦ (independentRadiusFirstMetricTriple z).2.2 -
        z.2 ^ 2 * (independentRadiusFirstSpectral z).1) (θ, 0) := by
    exact hfirstMetricD.sub ((hradius.pow 2).mul hfirstSpectralLow)
  have hsecondX : AnalyticAt ℝ
      (fun z ↦ (independentRadiusSecondMetricTriple z).2.2 -
        z.2 ^ 2 * (independentRadiusSecondSpectral z).1) (θ, 0) := by
    exact hsecondMetricD.sub ((hradius.pow 2).mul hsecondSpectralLow)
  have hnum : AnalyticAt ℝ (fun z ↦ -(
      (independentRadiusFirstMetricTriple z).2.1 *
          ((independentRadiusSecondMetricTriple z).2.2 -
            z.2 ^ 2 * (independentRadiusSecondSpectral z).1) +
        ((independentRadiusFirstMetricTriple z).2.2 -
          z.2 ^ 2 * (independentRadiusFirstSpectral z).1) *
          (independentRadiusSecondMetricTriple z).2.1)) (θ, 0) := by
    exact (hfirstMetricE.mul hsecondX).add (hfirstX.mul hsecondMetricE) |>.neg
  have hden : AnalyticAt ℝ (fun z ↦
      ((independentRadiusFirstMetricTriple z).2.2 -
          z.2 ^ 2 * (independentRadiusFirstSpectral z).1) *
        ((independentRadiusSecondMetricTriple z).2.2 -
          z.2 ^ 2 * (independentRadiusSecondSpectral z).1) -
      (independentRadiusFirstMetricTriple z).2.1 *
        (independentRadiusSecondMetricTriple z).2.1) (θ, 0) := by
    exact (hfirstX.mul hsecondX).sub (hfirstMetricE.mul hsecondMetricE)
  have hden0 :
      (((independentRadiusFirstMetricTriple (θ, 0)).2.2 -
          (0 : ℝ) ^ 2 * (independentRadiusFirstSpectral (θ, 0)).1) *
        ((independentRadiusSecondMetricTriple (θ, 0)).2.2 -
          (0 : ℝ) ^ 2 * (independentRadiusSecondSpectral (θ, 0)).1) -
      (independentRadiusFirstMetricTriple (θ, 0)).2.1 *
        (independentRadiusSecondMetricTriple (θ, 0)).2.1) ≠ 0 := by
    simp [independentRadiusFirstMetricTriple_zero,
      independentRadiusSecondMetricTriple_zero]
  have hcanonicalRegular : ContDiffAt ℝ 2
      (Function.uncurry mixedCanonicalFrameSlope) (θ, 0) := by
    unfold mixedCanonicalFrameSlope
    dsimp only
    apply AnalyticAt.contDiffAt
    exact hnum.div hden hden0
  -- The canonical quotient has the required first radius coefficient.
  have hcanonicalDerivative : deriv (mixedCanonicalFrameSlope θ) 0 = -3 := by
    let E₁ : ℝ → ℝ := fun r ↦
      (independentRadiusFirstMetricTriple (θ, r)).2.1
    let X₁ : ℝ → ℝ := fun r ↦
      (independentRadiusFirstMetricTriple (θ, r)).2.2 -
        r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1
    let E₂ : ℝ → ℝ := fun r ↦
      (independentRadiusSecondMetricTriple (θ, r)).2.1
    let X₂ : ℝ → ℝ := fun r ↦
      (independentRadiusSecondMetricTriple (θ, r)).2.2 -
        r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1
    obtain ⟨_, hC₁, hD₁, _, _⟩ :=
      independentFirstResidualQuadraticGerms θ.1 θ.2.1 θ.2.2
    obtain ⟨hL₂, _, _, _⟩ := independentRadiusSecondFactorQuadraticGerms θ
    obtain ⟨_, hC₂, hD₂, _, _⟩ := independentRadiusSecondComponentQuadraticGerms θ
    obtain ⟨hL₁, _, _, _⟩ := independentRadiusFirstFactorQuadraticGerms θ
    have hR : HasQuadraticGerm (fun r : ℝ ↦ r) 0 1 0 := by
      apply (HasQuadraticGerm.model 0 1 0).congrFunction
      intro r
      simp [quadraticModel]
    have hE₁' : HasQuadraticGerm E₁ 0 1 (-4 * θ.1) := by
      have hraw := hR.mul hC₁
      have hcoeff : HasQuadraticGerm
          (fun r ↦ r *
            (independentFirstResiduals θ.1 r (2 + θ.2.1 * θ.1 * r)
              (1 + θ.2.2 * θ.1 * r)).2.1) 0 1 (-4 * θ.1) := by
        exact hraw.congrCoefficients (by ring) (by ring) (by ring)
      apply hcoeff.congrFunction
      intro r
      rfl
    have hR2 : HasQuadraticGerm (fun r : ℝ ↦ r ^ 2) 0 0 1 := by
      have hraw := hR.mul hR
      have hcoeff : HasQuadraticGerm (fun r : ℝ ↦ r * r) 0 0 1 := by
        exact hraw.congrCoefficients (by ring) (by ring) (by ring)
      apply hcoeff.congrFunction
      intro r
      simp [pow_two]
    have hX₁' : HasQuadraticGerm X₁ 1 (-2 * θ.1)
        (6 * θ.1 ^ 2 - 3) := by
      have hraw := hD₁.sub (hR2.mul hL₁)
      have hcoeff : HasQuadraticGerm
          (fun r ↦
            (independentFirstResiduals θ.1 r (2 + θ.2.1 * θ.1 * r)
              (1 + θ.2.2 * θ.1 * r)).2.2 -
              r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1)
            1 (-2 * θ.1) (6 * θ.1 ^ 2 - 3) := by
        exact hraw.congrCoefficients (by ring) (by ring) (by ring)
      apply hcoeff.congrFunction
      intro r
      rfl
    have hE₂' : HasQuadraticGerm E₂ 0 2
        (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) := by
      have hraw := hR.mul hC₂
      have hcoeff : HasQuadraticGerm
          (fun r ↦ r *
            (independentSecondResiduals θ.1 r
              (independentRadiusFirstSpectral (θ, r)).1
              (independentRadiusFirstSpectral (θ, r)).2
              (independentRadiusFirstGradient (θ, r)).1
              (independentRadiusFirstGradient (θ, r)).2).2.1)
            0 2 (θ.1 * (6 * θ.2.2 + θ.2.1 + 84) / 3) := by
        exact hraw.congrCoefficients (by ring) (by ring) (by ring)
      apply hcoeff.congrFunction
      intro r
      rfl
    have hX₂' : HasQuadraticGerm X₂ 1 (8 * θ.1)
        (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
          78 * θ.1 ^ 2 - 3) / 3 - 2) := by
      have hraw := hD₂.sub (hR2.mul hL₂)
      have hcoeff : HasQuadraticGerm
          (fun r ↦
            (independentSecondResiduals θ.1 r
              (independentRadiusFirstSpectral (θ, r)).1
              (independentRadiusFirstSpectral (θ, r)).2
              (independentRadiusFirstGradient (θ, r)).1
              (independentRadiusFirstGradient (θ, r)).2).2.2 -
              r ^ 2 * (independentRadiusSecondSpectral (θ, r)).1)
            1 (8 * θ.1)
              (4 * (6 * θ.2.2 * θ.1 ^ 2 + θ.2.1 * θ.1 ^ 2 +
                78 * θ.1 ^ 2 - 3) / 3 - 2) := by
        exact hraw.congrCoefficients (by ring) (by ring) (by ring)
      apply hcoeff.congrFunction
      intro r
      rfl
    have hE₁Regular : ContDiffAt ℝ 2 E₁ 0 := by
      simpa [E₁] using mixedRadiusSlice_contDiffAt_of_analyticAt θ hfirstMetricE
    have hX₁Regular : ContDiffAt ℝ 2 X₁ 0 := by
      simpa [X₁] using mixedRadiusSlice_contDiffAt_of_analyticAt θ hfirstX
    have hE₂Regular : ContDiffAt ℝ 2 E₂ 0 := by
      simpa [E₂] using mixedRadiusSlice_contDiffAt_of_analyticAt θ hsecondMetricE
    have hX₂Regular : ContDiffAt ℝ 2 X₂ 0 := by
      simpa [X₂] using mixedRadiusSlice_contDiffAt_of_analyticAt θ hsecondX
    have hdenEntries : X₁ 0 * X₂ 0 - E₁ 0 * E₂ 0 ≠ 0 := by
      simp [E₁, X₁, E₂, X₂, independentRadiusFirstMetricTriple_zero,
        independentRadiusSecondMetricTriple_zero]
    have hresult := mixedRawFrameSlope_contDiffAt_and_deriv_of_entryCertificates
      hE₁Regular hX₁Regular hE₂Regular hX₂Regular
      hE₁' hX₁' hE₂' hX₂' hdenEntries (by norm_num : (1 : ℝ) + 2 = 3)
    have hformula :
        (fun r ↦ -(E₁ r * X₂ r + X₁ r * E₂ r) /
          (X₁ r * X₂ r - E₁ r * E₂ r)) = mixedCanonicalFrameSlope θ := by
      funext r
      simp [E₁, X₁, E₂, X₂, mixedCanonicalFrameSlope,
        independentRadiusSecondMetricTriple_eq]
    rw [hformula] at hresult
    exact hresult.2
  -- The positive second low coordinate makes the raw orientation bridge valid
  -- throughout a neighborhood of the removable base.
  have hdomain := mixedRawProjectionDomain_eventually β B hβ_small hθ
  have hGloCont : ContinuousAt
      (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
        (independentRadiusSecondGradient z).1) (θ, 0) :=
    continuousAt_fst.comp (independentRadiusSecondGradient_analyticAt θ).continuousAt
  have hGlo : ∀ᶠ z : ((ℝ × ℝ × ℝ) × ℝ) in 𝓝 (θ, 0),
      0 < (independentRadiusSecondGradient z).1 := by
    apply hGloCont.eventually
    have hbase :
        (fun z : ((ℝ × ℝ × ℝ) × ℝ) ↦
          (independentRadiusSecondGradient z).1) (θ, 0) = 1 := by
      exact congrArg Prod.fst (independentRadiusSecondGradient_zero θ)
    rw [hbase]
    exact Ioi_mem_nhds (by norm_num)
  have hrawCanonical :
      Function.uncurry mixedRawFrameAngleSlopeAlongInput =ᶠ[𝓝 (θ, 0)]
        Function.uncurry mixedCanonicalFrameSlope := by
    filter_upwards [hdomain, hGlo] with z hz hGloz
    change mixedRawFrameAngleSlopeAlongInput z.1 z.2 =
      mixedCanonicalFrameSlope z.1 z.2
    by_cases hz0 : z.2 = 0
    · rw [hz0, mixedRawFrameAngleSlopeAlongInput_zero]
      simp [mixedCanonicalFrameSlope,
        independentRadiusFirstMetricTriple_zero,
        independentRadiusSecondMetricTriple_zero]
    · rcases hz with hz | hz
      · exact False.elim (hz0 hz)
      · exact mixedRawFrameAngleSlope_eq_canonical_of_projectionDomain
          z.1 z.2 hz hGloz
  have hregular := hcanonicalRegular.congr_of_eventuallyEq hrawCanonical
  have hpath : Tendsto (fun r : ℝ ↦ (θ, r)) (𝓝 0) (𝓝 (θ, 0)) := by
    exact continuousAt_const.prodMk continuousAt_id
  have hsliceEq :
      mixedRawFrameAngleSlopeAlongInput θ =ᶠ[𝓝 0] mixedCanonicalFrameSlope θ := by
    have hcomp := hrawCanonical.comp_tendsto hpath
    filter_upwards [hcomp] with r hr
    exact hr
  have hderiv : deriv (mixedRawFrameAngleSlopeAlongInput θ) 0 = -3 := by
    rw [hsliceEq.deriv_eq, hcanonicalDerivative]
  exact ⟨hregular, hderiv⟩

/- The signed second-frame coordinate is the missing pointwise interface between
   the raw evaluator and the canonical second-gradient factors. -/

/-- On the punctured raw chart, the physical second-leg low coordinate equals the
    canonical second-gradient low factor. -/
private lemma mixedIndependentRawAmplitude_eq_secondGradientLow_of_signedFrame
    (θ : ℝ × ℝ × ℝ) (r : ℝ) (hr : r ≠ 0)
    (hθ : |θ.1| < (1 / 4 : ℝ))
    (hp : 0 < (input θ r).2.1) (hh : 0 < (input θ r).2.2)
    (hL : 0 < (independentRadiusFirstSpectral (θ, r)).1)
    (hH : 0 < (independentRadiusFirstSpectral (θ, r)).2)
    (hQ : (independentRadiusFirstGradient (θ, r)).1 ≠ 0)
    (hGlo : 0 < (independentRadiusSecondGradient (θ, r)).1) :
    mixedIndependentRawAmplitude θ.1 r (input θ r).2.1 (input θ r).2.2 =
      (independentRadiusSecondGradient (θ, r)).1 := by
  let p : ℝ := (input θ r).2.1
  let h : ℝ := (input θ r).2.2
  have hrSq : 0 < r ^ 2 := sq_pos_of_ne_zero hr
  have hinitial : (Matrix.diagonal ![h * p * r ^ 2, h] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (mul_pos hh hp) hrSq
    · exact hh
  have hcontrols := independentRadiusControlMatricesPosDef θ.1 hθ
  have htauFirst : 0 < (TwoPhaseControls.first θ.1).tau :=
    TwoPhaseControls.tau_pos θ.1 0
  have hgradientFirst : (![(1 : ℝ), p * r] : Fin 2 → ℝ) ≠ 0 := by
    intro hzero
    have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
    norm_num at hzeroFirst
  have hfirstRaw := independentRawStep_first_eq θ.1 r p h hinitial hcontrols.1
    htauFirst hgradientFirst hr
  let t₁ := independentFirstResiduals θ.1 r p h
  let M₁ := independentFirstMetric θ.1 r p h
  let v₁ := independentFirstGradient θ.1 r p
  let F₁ := EuclideanPlane.frame
    (RealSymmetric2.lowVector (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)
  let L := (independentRadiusFirstSpectral (θ, r)).1
  let H := (independentRadiusFirstSpectral (θ, r)).2
  let Q := (independentRadiusFirstGradient (θ, r)).1
  let U := (independentRadiusFirstGradient (θ, r)).2
  have hspectralFirst : independentRadiusFirstSpectral (θ, r) =
      independentFirstSpectralFactors θ.1 r p h := by
    rfl
  have hgradientFactorsFirst : independentRadiusFirstGradient (θ, r) =
      independentFirstGradientFactors θ.1 r p h := by
    rfl
  have hdenomFirst : RealSymmetric2.lowDenom
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    intro hzero
    apply hQ
    rw [hgradientFactorsFirst]
    unfold independentFirstGradientFactors
    dsimp only
    rw [hzero]
    simp
  have hhighFirst : RealSymmetric2.high
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    have hpositive : 0 < RealSymmetric2.high
        (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 := by
      simpa [H, hspectralFirst, independentFirstSpectralFactors, t₁] using hH
    exact ne_of_gt hpositive
  have hlowFirst : RealSymmetric2.low
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 = r ^ 2 * L := by
    rw [low_eq_radiusSq_mul_detFactor r t₁.1 t₁.2.1 t₁.2.2 hhighFirst]
    simp [L, hspectralFirst, independentFirstSpectralFactors, t₁]
  have hdiagFixedFirst : F₁.transpose * M₁ * F₁ =
      Matrix.diagonal ![r ^ 2 * L, H] := by
    have hmetricFirst : M₁ = RealSymmetric2.matrix
        (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    have hdiag := RealSymmetric2.frame_diagonalizes_of_lowDenom_ne_zero
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 hdenomFirst
    rw [hmetricFirst, hdiag]
    simp [L, H, hspectralFirst, independentFirstSpectralFactors, t₁, hlowFirst]
  have hgradFixedFirst : F₁.transpose.mulVec v₁ = ![Q, r * U] := by
    have hcoords := lowFrame_transpose_mulVec
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2
      (independentFirstGradientResiduals θ.1 r p).1
      (r * (independentFirstGradientResiduals θ.1 r p).2)
    rw [show F₁.transpose.mulVec v₁ =
        (EuclideanPlane.frame (RealSymmetric2.lowVector
          (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)).transpose.mulVec
          ![(independentFirstGradientResiduals θ.1 r p).1,
            r * (independentFirstGradientResiduals θ.1 r p).2] by rfl]
    rw [hcoords]
    ext i
    fin_cases i <;>
      simp [Q, U, hgradientFactorsFirst, independentFirstGradientFactors, t₁] <;>
      ring
  have hframeFirst :
      OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1) (WithLp.toLp 2 v₁) = F₁ ∨
        OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1) (WithLp.toLp 2 v₁) = -F₁ := by
    rcases orientedEigenframe_eq_fixed_or_neg (M₁ 0 0) (M₁ 0 1) (M₁ 1 1)
      (WithLp.toLp 2 v₁) with hframe | hframe
    · left
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
    · right
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
  let t₂ := independentSecondResiduals θ.1 r L H Q U
  let M₂ := independentSecondMetric θ.1 r L H Q U
  let v₂ := independentSecondGradient θ.1 r L H Q U
  let S := (independentRadiusSecondSpectral (θ, r)).1
  let T := (independentRadiusSecondSpectral (θ, r)).2
  let Glo := (independentRadiusSecondGradient (θ, r)).1
  let Ghi := (independentRadiusSecondGradient (θ, r)).2
  have hdiagSecond : (Matrix.diagonal ![r ^ 2 * L, H] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (sq_pos_of_ne_zero hr) hL
    · exact hH
  have hgradientSecond : (![(1 : ℝ) • Q, (1 : ℝ) • (r * U)] : Fin 2 → ℝ) ≠ 0 := by
    intro hzero
    have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
    apply hQ
    simpa [Q] using hzeroFirst
  have hsecondRawPos := independentRawStep_second_eq θ.1 r L H Q U 1
    hdiagSecond hcontrols.2 (TwoPhaseControls.tau_pos θ.1 1)
    (by simpa using hgradientSecond) hr
  have hsecondRawCanonical :
      independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
          (![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1) =
        (M₂, v₂) := by
    simpa [M₂, v₂] using hsecondRawPos
  have hmetricSecond : M₂ = RealSymmetric2.matrix
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hgradFixedSecond :
      (EuclideanPlane.frame (RealSymmetric2.lowVector
        (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)).transpose.mulVec v₂ =
          ![Glo, r * Ghi] := by
    have hcoords := lowFrame_transpose_mulVec
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2
      (independentSecondGradientResiduals θ.1 r L H Q U).1
      (r * (independentSecondGradientResiduals θ.1 r L H Q U).2)
    rw [show (EuclideanPlane.frame (RealSymmetric2.lowVector
        (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)).transpose.mulVec v₂ =
        (EuclideanPlane.frame (RealSymmetric2.lowVector
          (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)).transpose.mulVec
          ![(independentSecondGradientResiduals θ.1 r L H Q U).1,
            r * (independentSecondGradientResiduals θ.1 r L H Q U).2] by rfl]
    rw [hcoords]
    ext i
    fin_cases i <;>
      simp [Glo, Ghi, independentRadiusSecondGradient, independentSecondGradientFactors, t₂] <;>
      ring
  unfold mixedIndependentRawAmplitude
  dsimp only
  rw [hfirstRaw]
  rcases hframeFirst with hframeFirst | hframeFirst
  · rw [hframeFirst, hdiagFixedFirst, hgradFixedFirst, hsecondRawCanonical]
    have hcoord := orientedLowCoordinate_eq_of_fixedFrameCoordinates
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 Glo (r * Ghi) v₂ hgradFixedSecond hGlo
    simpa [hmetricSecond, M₂, t₂, v₂, Glo, Ghi, RealSymmetric2.matrix] using hcoord
  · have hdiagNeg :
        (-F₁).transpose * M₁ * (-F₁) = Matrix.diagonal ![r ^ 2 * L, H] := by
      simpa only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using
        hdiagFixedFirst
    have hgradNeg : (-F₁).transpose.mulVec v₁ = -![Q, r * U] := by
      rw [Matrix.transpose_neg, Matrix.neg_mulVec, hgradFixedFirst]
    have hgradientSecondNeg :
        ((-1 : ℝ) • ![Q, r * U] : Fin 2 → ℝ) ≠ 0 := by
      intro hzero
      have hzeroFirst := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hzero
      apply hQ
      simpa [Q] using hzeroFirst
    have hsecondRawNeg := independentRawStep_second_eq θ.1 r L H Q U (-1)
      hdiagSecond hcontrols.2 (TwoPhaseControls.tau_pos θ.1 1)
      hgradientSecondNeg hr
    have hsecondRawNeg' :
        independentRawStep (Matrix.diagonal ![r ^ 2 * L, H])
            (-![Q, r * U] : Fin 2 → ℝ) (TwoPhaseControls.second θ.1) =
          (M₂, -v₂) := by
      simpa [M₂, v₂] using hsecondRawNeg
    rw [hframeFirst, hdiagNeg, hgradNeg, hsecondRawNeg']
    have hgradFixedSecondNeg :
        (EuclideanPlane.frame (RealSymmetric2.lowVector
          (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2)).transpose.mulVec (-v₂) =
            ![-Glo, r * (-Ghi)] := by
      rw [Matrix.mulVec_neg, hgradFixedSecond]
      ext i
      fin_cases i <;> simp
    have hcoord := orientedLowCoordinate_eq_of_fixedFrameCoordinates_neg
      (r ^ 2 * t₂.1) (r * t₂.2.1) t₂.2.2 Glo (r * Ghi) v₂
      hgradFixedSecond hGlo
    simpa [hmetricSecond, M₂, t₂, v₂, Glo, Ghi, RealSymmetric2.matrix] using hcoord

/-- The physical amplitude and frame-angle projections inherit their canonical
    independent-radius coefficient germs. -/
lemma mixedObservableTruncatedGerms (β B : ℝ) (_hβ : 0 < β) (hβ_small : β < 1 / 4)
    (_hB : 0 ≤ B) :
    IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).amplitudeRatio)
        (parameterSet β B) 3
        (fun n θ ↦
          (![1, 0,
            (θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18] : Fin 3 → ℝ) n) ∧
      IndependentRadiusTruncatedGerm
        (fun θ r ↦ (observableMap θ.1 (input θ r)).frameAngleIncrement)
        (parameterSet β B) 2
        (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) :=
  by
    -- Route correction: pointwise raw-domain facts alone do not identify the final
    -- oriented coordinates.  Separate the physical/raw equality, the raw/canonical
    -- bridge, and the canonical germ before assembling the two observables.
    let amplitudeNormalForm : (ℝ × ℝ × ℝ) → ℝ → ℝ := fun θ r ↦
      mixedIndependentRawAmplitude θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)
    let angleNormalForm : (ℝ × ℝ × ℝ) → ℝ → ℝ := fun θ r ↦
      mixedIndependentRawFrameAngle θ.1 r
        (2 + θ.2.1 * θ.1 * r) (1 + θ.2.2 * θ.1 * r)
    -- The physical evaluator agrees pointwise with the raw scalar projections.
    have hphysicalAmplitudeRaw : ∀ θ, θ ∈ parameterSet β B →
        Function.uncurry
            (fun η r ↦ (observableMap η.1 (input η r)).amplitudeRatio) =ᶠ[𝓝 (θ, 0)]
          (Function.uncurry amplitudeNormalForm) := by
      intro θ hθ
      filter_upwards [] with z
      exact mixedObservable_amplitude_eq_independentRaw z.1.1 z.2
        (2 + z.1.2.1 * z.1.1 * z.2) (1 + z.1.2.2 * z.1.1 * z.2)
    -- The raw evaluator is transported to the canonical second-gradient coordinate
    -- by separating the removable radius branch from the punctured normal form.
    have hrawAmplitudeCanonical : ∀ θ, θ ∈ parameterSet β B →
        Function.uncurry amplitudeNormalForm =ᶠ[𝓝 (θ, 0)]
          (Function.uncurry
            (fun η r ↦ (independentRadiusSecondGradient (η, r)).1)) := by
      intro θ hθ
      -- The common certificate separates the removable radius branch from the
      -- punctured raw calculation, so the remaining gap is a single coordinate
      -- identity rather than repeated denominator bookkeeping.
      have hdomain := mixedRawProjectionDomain_eventually β B hβ_small hθ
      have hGloCont : ContinuousAt
          (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
            (independentRadiusSecondGradient z).1) (θ, 0) :=
        continuousAt_fst.comp (independentRadiusSecondGradient_analyticAt θ).continuousAt
      have hGlo : ∀ᶠ z : (ℝ × ℝ × ℝ) × ℝ in 𝓝 (θ, 0),
          0 < (independentRadiusSecondGradient z).1 := by
        apply hGloCont.eventually
        have hbase :
            (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
              (independentRadiusSecondGradient z).1) (θ, 0) = 1 := by
          exact congrArg Prod.fst (independentRadiusSecondGradient_zero θ)
        rw [hbase]
        exact Ioi_mem_nhds (by norm_num)
      filter_upwards [hdomain, hGlo] with z hz hGloz
      change amplitudeNormalForm z.1 z.2 =
        (independentRadiusSecondGradient z).1
      by_cases hz0 : z.2 = 0
      · rw [hz0]
        -- At zero radius both raw steps are stationary and both oriented frames
        -- reduce to the identity, so the final low coordinate is exactly one.
        dsimp [amplitudeNormalForm]
        norm_num
        rw [mixedIndependentRawAmplitude_zeroRadius]
        have hzpair : z = (z.1, 0) := by
          ext <;> simp [hz0]
        rw [hzpair]
        exact (congrArg Prod.fst (independentRadiusSecondGradient_zero z.1)).symm
      · rcases hz with hz | hz
        · exact False.elim (hz0 hz)
        · rcases hz with ⟨hz_ne, hz_small, hp, hh, hL, hH, hQ⟩
          exact mixedIndependentRawAmplitude_eq_secondGradientLow_of_signedFrame
            z.1 z.2 hz_ne hz_small hp hh hL hH hQ hGloz
    have hphysicalAmplitude : ∀ θ, θ ∈ parameterSet β B →
        Function.uncurry
            (fun η r ↦ (observableMap η.1 (input η r)).amplitudeRatio) =ᶠ[𝓝 (θ, 0)]
          (Function.uncurry
            (fun η r ↦ (independentRadiusSecondGradient (η, r)).1)) := by
      intro θ hθ
      exact (hphysicalAmplitudeRaw θ hθ).trans (hrawAmplitudeCanonical θ hθ)
    -- The frame-angle projection is likewise reduced pointwise to the raw relative frame.
    have hphysicalAngleRaw : ∀ θ, θ ∈ parameterSet β B →
        Function.uncurry
            (fun η r ↦ (observableMap η.1 (input η r)).frameAngleIncrement) =ᶠ[𝓝 (θ, 0)]
          (Function.uncurry angleNormalForm) := by
      intro θ hθ
      filter_upwards [] with z
      exact mixedObservable_frameAngle_eq_independentRaw z.1.1 z.2
        (2 + z.1.2.1 * z.1.1 * z.2) (1 + z.1.2.2 * z.1.1 * z.2)
    -- The raw relative-frame coordinate is regular at the removable base; its
    -- value and first radius derivative give the required `[0, -3]` germ.
    have hangleGerm : IndependentRadiusTruncatedGerm angleNormalForm
        (parameterSet β B) 2 (fun n _θ ↦ (![0, -3] : Fin 2 → ℝ) n) := by
      have hslopeJet := mixedRawFrameAngleSlopeJet β B hβ_small
      -- Compose the scalar slope with the arctangent chart without reopening the
      -- nested raw evaluator in the coefficient calculation.
      have hregular : ∀ θ, θ ∈ parameterSet β B →
          ContDiffAt ℝ 2 (Function.uncurry angleNormalForm) (θ, 0) := by
        intro θ hθ
        have hcomp := Real.contDiff_arctan.contDiffAt.comp (θ, 0) (hslopeJet θ hθ).1
        have hfun :
            (Real.arctan ∘ Function.uncurry mixedRawFrameAngleSlopeAlongInput) =
              Function.uncurry angleNormalForm := by
          funext z
          exact (mixedRawFrameAngleAlongInput_eq_arctan_slope z.1 z.2).symm
        rw [hfun] at hcomp
        exact hcomp
      have hzero : ∀ θ, θ ∈ parameterSet β B → angleNormalForm θ 0 = 0 := by
        intro θ hθ
        dsimp only [angleNormalForm]
        norm_num
        exact mixedRawFrameAngle_zero θ.1
      have hlinear : ∀ θ, θ ∈ parameterSet β B →
          iteratedDeriv 1 (angleNormalForm θ) 0 = -3 := by
        intro θ hθ
        have htwo_ne_zero : (2 : WithTop ENat) ≠ 0 := by
          norm_num
        have hsliceMap : ContDiffAt ℝ 2 (fun r : ℝ ↦ (θ, r)) 0 := by
          fun_prop
        have hslopeRegular : ContDiffAt ℝ 2
            (mixedRawFrameAngleSlopeAlongInput θ) 0 := by
          have hcomp := (hslopeJet θ hθ).1.comp 0 hsliceMap
          have hfun :
              Function.uncurry mixedRawFrameAngleSlopeAlongInput ∘ Prod.mk θ =
                mixedRawFrameAngleSlopeAlongInput θ := by
            funext r
            rfl
          rw [hfun] at hcomp
          exact hcomp
        have hslopeDeriv : HasDerivAt (mixedRawFrameAngleSlopeAlongInput θ)
            (deriv (mixedRawFrameAngleSlopeAlongInput θ) 0) 0 :=
          (hslopeRegular.differentiableAt htwo_ne_zero).hasDerivAt
        have hatan :=
          (Real.hasDerivAt_arctan (mixedRawFrameAngleSlopeAlongInput θ 0)).comp
            0 hslopeDeriv
        have hangleFun : angleNormalForm θ =
            Real.arctan ∘ mixedRawFrameAngleSlopeAlongInput θ := by
          funext r
          exact mixedRawFrameAngleAlongInput_eq_arctan_slope θ r
        rw [hangleFun]
        simp only [iteratedDeriv_succ, iteratedDeriv_zero]
        rw [hatan.deriv, mixedRawFrameAngleSlopeAlongInput_zero,
          (hslopeJet θ hθ).2]
        norm_num
      exact independentRadiusTruncatedGerm_of_twoDerivativeData
        hregular hzero hlinear
    have hcanonicalAmplitude := mixedIndependentSecondGradientLow_truncatedGerm
      (K := parameterSet β B)
    exact pairedObservableGerms_of_uncurry_eventuallyEq
      hphysicalAmplitude hphysicalAngleRaw hcanonicalAmplitude hangleGerm

/-- A local cubic factorization and a bounded quotient imply the corresponding
    estimate on the same radius tube. -/
lemma localScalarCubicBound
    {R Q : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)}
    (δ : ℝ)
    (hfactor : ∀ θ r, |r| < δ → R θ r = (θ.1 * r ^ (3 : ℕ)) • Q θ r)
    (hQ : ∃ C > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ → ‖Q θ r‖ ≤ C) :
    ∃ C > 0, ∀ θ ∈ K, ∀ r : ℝ, |r| < δ →
      ‖R θ r‖ ≤ C * |θ.1| * |r| ^ (3 : ℝ) := by
  obtain ⟨C, hC, hQ⟩ := hQ
  refine ⟨C, hC, ?_⟩
  intro θ hθ r hr
  rw [hfactor θ r hr, norm_smul, Real.norm_eq_abs, abs_mul, abs_pow]
  have hnonneg : 0 ≤ |θ.1| * |r| ^ (3 : ℕ) := by positivity
  calc
    |θ.1| * |r| ^ (3 : ℕ) * ‖Q θ r‖ ≤
        |θ.1| * |r| ^ (3 : ℕ) * C :=
      mul_le_mul_of_nonneg_left (hQ θ hθ r hr) hnonneg
    _ = C * |θ.1| * |r| ^ (3 : ℕ) := by ring
    _ = C * |θ.1| * |r| ^ (3 : ℝ) := by
      norm_num [Real.rpow_natCast]

/- Route correction: the earlier full second-metric transport enlarged the quotient
   proof; the current route transports only the signed displacement certificate. -/
/- The center certificate needs only the first-frame normalization and the second
   displacement.  These two bridges keep the full physical evaluator out of the
   quotient endgame. -/

/-- The physical first raw step has the canonical diagonal representation, up to
    the global orientation sign selected by the updated gradient. -/
private lemma mixedRawFirstCanonicalFrameData
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r) :
    let L := (independentRadiusFirstSpectral (θ, r)).1
    let H := (independentRadiusFirstSpectral (θ, r)).2
    let Q := (independentRadiusFirstGradient (θ, r)).1
    let U := (independentRadiusFirstGradient (θ, r)).2
    let F := EuclideanPlane.frame
      (RealSymmetric2.lowVector
        (independentRadiusFirstMetricTriple (θ, r)).1
        (independentRadiusFirstMetricTriple (θ, r)).2.1
        (independentRadiusFirstMetricTriple (θ, r)).2.2)
    (CenterRaw.firstFrame θ.1 (input θ r) = F ∧
        F.transpose * (CenterRaw.firstStep θ.1 (input θ r)).1 * F =
          Matrix.diagonal ![r ^ 2 * L, H] ∧
        F.transpose.mulVec (CenterRaw.firstStep θ.1 (input θ r)).2.1 =
          ![Q, r * U]) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -F ∧
        (-F).transpose * (CenterRaw.firstStep θ.1 (input θ r)).1 * (-F) =
          Matrix.diagonal ![r ^ 2 * L, H] ∧
        (-F).transpose.mulVec (CenterRaw.firstStep θ.1 (input θ r)).2.1 =
          -![Q, r * U]) := by
  -- Normalize the physical first step once, then diagonalize its independent form.
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  let p : ℝ := (input θ r).2.1
  let h : ℝ := (input θ r).2.2
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * r ^ 2, h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), p * r]
  let t₁ := independentFirstResiduals θ.1 r p h
  let M₁ := independentFirstMetric θ.1 r p h
  let v₁ := independentFirstGradient θ.1 r p
  let F₁ := EuclideanPlane.frame
    (RealSymmetric2.lowVector (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)
  have hinitial : H₀.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · exact mul_pos (mul_pos hh hp) (sq_pos_of_ne_zero hr)
    · exact hh
  have hcontrols := independentRadiusControlMatricesPosDef θ.1 hθ
  have hgradient : g₀ ≠ 0 := by
    intro hz
    have hz0 := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hz
    norm_num [g₀] at hz0
  have hfirstRaw := independentRawStep_first_eq θ.1 r p h hinitial hcontrols.1
    (TwoPhaseControls.tau_pos θ.1 0) hgradient hr
  have hmetric : (CenterRaw.firstStep θ.1 (input θ r)).1 = M₁ := by
    calc
      (CenterRaw.firstStep θ.1 (input θ r)).1 =
          (independentRawStep H₀ g₀ (TwoPhaseControls.first θ.1)).1 := by
        rfl
      _ = M₁ := by simpa [M₁] using congrArg Prod.fst hfirstRaw
  have hupdatedGradient :
      (CenterRaw.firstStep θ.1 (input θ r)).2.1 = v₁ := by
    calc
      (CenterRaw.firstStep θ.1 (input θ r)).2.1 =
          (independentRawStep H₀ g₀ (TwoPhaseControls.first θ.1)).2 := by
        rfl
      _ = v₁ := by simpa [v₁] using congrArg Prod.snd hfirstRaw
  have hspectral : independentRadiusFirstSpectral (θ, r) =
      independentFirstSpectralFactors θ.1 r p h := by rfl
  have hgradientFactors : independentRadiusFirstGradient (θ, r) =
      independentFirstGradientFactors θ.1 r p h := by rfl
  have hdenom : RealSymmetric2.lowDenom
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    intro hz
    apply hQ
    rw [hgradientFactors]
    unfold independentFirstGradientFactors
    dsimp only
    rw [hz]
    simp
  have hhigh : RealSymmetric2.high
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 ≠ 0 := by
    have hpos : 0 < RealSymmetric2.high
        (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 := by
      simpa [hH, hspectral, independentFirstSpectralFactors, t₁] using hH
    exact ne_of_gt hpos
  have hlow : RealSymmetric2.low
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 =
      r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1 := by
    rw [low_eq_radiusSq_mul_detFactor r t₁.1 t₁.2.1 t₁.2.2 hhigh]
    simp [hspectral, independentFirstSpectralFactors, t₁]
  have hdiag : F₁.transpose * M₁ * F₁ =
      Matrix.diagonal ![r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1,
        (independentRadiusFirstSpectral (θ, r)).2] := by
    have hmetric' : M₁ = RealSymmetric2.matrix
        (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
    rw [hmetric', RealSymmetric2.frame_diagonalizes_of_lowDenom_ne_zero
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2 hdenom]
    simp [hspectral, independentFirstSpectralFactors, t₁, hlow]
  have hcoords : F₁.transpose.mulVec v₁ =
      ![(independentRadiusFirstGradient (θ, r)).1,
        r * (independentRadiusFirstGradient (θ, r)).2] := by
    have hraw := lowFrame_transpose_mulVec
      (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2
      (independentFirstGradientResiduals θ.1 r p).1
      (r * (independentFirstGradientResiduals θ.1 r p).2)
    rw [show F₁.transpose.mulVec v₁ =
        (EuclideanPlane.frame (RealSymmetric2.lowVector
          (r ^ 2 * t₁.1) (r * t₁.2.1) t₁.2.2)).transpose.mulVec
          ![(independentFirstGradientResiduals θ.1 r p).1,
            r * (independentFirstGradientResiduals θ.1 r p).2] by rfl]
    rw [hraw]
    ext i
    fin_cases i <;>
      simp [hgradientFactors, independentFirstGradientFactors, t₁] <;> ring
  have hframe :
      OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1) (WithLp.toLp 2 v₁) = F₁ ∨
      OrientedEigenframe.frame (M₁ 0 0) (M₁ 0 1) (M₁ 1 1) (WithLp.toLp 2 v₁) = -F₁ := by
    rcases orientedEigenframe_eq_fixed_or_neg (M₁ 0 0) (M₁ 0 1) (M₁ 1 1)
      (WithLp.toLp 2 v₁) with hframe | hframe
    · left
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
    · right
      simpa [F₁, M₁, independentFirstMetric, t₁] using hframe
  dsimp only
  have hframe' := hframe
  rw [← hmetric, ← hupdatedGradient] at hframe'
  have hframe'' :
      CenterRaw.firstFrame θ.1 (input θ r) = F₁ ∨
        CenterRaw.firstFrame θ.1 (input θ r) = -F₁ := by
    simpa [CenterRaw.firstFrame, CenterRaw.firstStep] using hframe'
  have hdiag' : F₁.transpose *
      (CenterRaw.firstStep θ.1 (input θ r)).1 * F₁ =
      Matrix.diagonal ![r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1,
        (independentRadiusFirstSpectral (θ, r)).2] := by
    simpa [hmetric] using hdiag
  have hcoords' : F₁.transpose.mulVec
      (CenterRaw.firstStep θ.1 (input θ r)).2.1 =
      ![(independentRadiusFirstGradient (θ, r)).1,
        r * (independentRadiusFirstGradient (θ, r)).2] := by
    simpa [hupdatedGradient] using hcoords
  have hF₁ : F₁ = EuclideanPlane.frame
      (RealSymmetric2.lowVector
        (independentRadiusFirstMetricTriple (θ, r)).1
        (independentRadiusFirstMetricTriple (θ, r)).2.1
        (independentRadiusFirstMetricTriple (θ, r)).2.2) := by
    rfl
  rcases hframe'' with hframe | hframe
  · left
    refine ⟨?_, ?_, ?_⟩
    · rw [← hF₁]
      exact hframe
    · rw [← hF₁]
      exact hdiag'
    · rw [← hF₁]
      exact hcoords'
  · right
    refine ⟨?_, ?_, ?_⟩
    · rw [← hF₁]
      exact hframe
    · rw [← hF₁]
      simpa only [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using hdiag'
    · have hcoordsCanonical := hcoords'
      rw [hF₁] at hcoordsCanonical
      rw [Matrix.transpose_neg, Matrix.neg_mulVec, hcoordsCanonical]

/-- The physical second displacement follows the same canonical formula, with the
    first-frame orientation determining whether both signs are negated. -/
private lemma mixedRawSecondDisplacement_eq_signedCanonical
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hdomain : mixedRawProjectionDomain θ r) :
    let L := (independentRadiusFirstSpectral (θ, r)).1
    let H := (independentRadiusFirstSpectral (θ, r)).2
    let Q := (independentRadiusFirstGradient (θ, r)).1
    let U := (independentRadiusFirstGradient (θ, r)).2
    let F := EuclideanPlane.frame
      (RealSymmetric2.lowVector
        (independentRadiusFirstMetricTriple (θ, r)).1
        (independentRadiusFirstMetricTriple (θ, r)).2.1
        (independentRadiusFirstMetricTriple (θ, r)).2.2)
    (CenterRaw.firstFrame θ.1 (input θ r) = F ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • CenterRaw.secondNormalizedDisplacement θ.1 r L H Q U) ∨
      (CenterRaw.firstFrame θ.1 (input θ r) = -F ∧
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
          r • (-CenterRaw.secondNormalizedDisplacement θ.1 r L H Q U)) := by
  -- Consume the first-frame bridge and apply the raw second-step displacement API.
  have hfirst := mixedRawFirstCanonicalFrameData θ r hdomain
  dsimp only at hfirst ⊢
  rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
  rcases hfirst with ⟨hframe, hdiag, hgrad⟩ | ⟨hframe, hdiag, hgrad⟩
  · have hβpos := mixedSecondDisplacement_denominator_pos
      (θ := θ) (r := r) ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
    have hβne :
        r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1 *
              (r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1 -
                2 * θ.1 * (independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2) +
            (independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2 *
              ((independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2 -
                2 * θ.1 * r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1) ≠ 0 := ne_of_gt hβpos
    have hden : (1 : ℝ) ^ 2 * r ^ 2 *
        (r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1 *
              (r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1 -
                2 * θ.1 * (independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2) +
            (independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2 *
              ((independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2 -
                2 * θ.1 * r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1)) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hr)) hβne
    have hmetricSecond : CenterRaw.secondMetric θ.1 (input θ r) =
        Matrix.diagonal ![r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1,
          (independentRadiusFirstSpectral (θ, r)).2] := by
      simpa [CenterRaw.secondMetric, hframe] using hdiag
    have hgradientSecond : CenterRaw.secondGradient θ.1 (input θ r) =
        (1 : ℝ) • ![(independentRadiusFirstGradient (θ, r)).1,
          r * (independentRadiusFirstGradient (θ, r)).2] := by
      simpa [CenterRaw.secondGradient, hframe] using hgrad
    have hdisp := CenterRaw.secondStep_displacement_eq_radius_smul
      θ.1 r (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2 1 (input θ r)
      hmetricSecond hgradientSecond hden
    exact Or.inl ⟨hframe, by simpa only [one_smul] using hdisp⟩
  · have hβpos := mixedSecondDisplacement_denominator_pos
      (θ := θ) (r := r) ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
    have hβne :
        r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1 *
              (r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1 -
                2 * θ.1 * (independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2) +
            (independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2 *
              ((independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2 -
                2 * θ.1 * r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1) ≠ 0 := ne_of_gt hβpos
    have hden : (-1 : ℝ) ^ 2 * r ^ 2 *
        (r * (independentRadiusFirstSpectral (θ, r)).1 *
              (independentRadiusFirstGradient (θ, r)).1 *
              (r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1 -
                2 * θ.1 * (independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2) +
            (independentRadiusFirstSpectral (θ, r)).2 *
              (independentRadiusFirstGradient (θ, r)).2 *
              ((independentRadiusFirstSpectral (θ, r)).2 *
                  (independentRadiusFirstGradient (θ, r)).2 -
                2 * θ.1 * r * (independentRadiusFirstSpectral (θ, r)).1 *
                  (independentRadiusFirstGradient (θ, r)).1)) ≠ 0 := by
      simpa using mul_ne_zero (pow_ne_zero 2 hr) hβne
    have hmetricSecond : CenterRaw.secondMetric θ.1 (input θ r) =
        Matrix.diagonal ![r ^ 2 * (independentRadiusFirstSpectral (θ, r)).1,
          (independentRadiusFirstSpectral (θ, r)).2] := by
      simpa [CenterRaw.secondMetric, hframe] using hdiag
    have hgradientSecond : CenterRaw.secondGradient θ.1 (input θ r) =
        (-1 : ℝ) • ![(independentRadiusFirstGradient (θ, r)).1,
          r * (independentRadiusFirstGradient (θ, r)).2] := by
      simpa [CenterRaw.secondGradient, hframe, neg_smul] using hgrad
    have hdisp := CenterRaw.secondStep_displacement_eq_radius_smul
      θ.1 r (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2 (-1) (input θ r)
      hmetricSecond hgradientSecond hden
    exact Or.inr ⟨hframe, by
      calc
        (CenterRaw.secondStep θ.1 (input θ r)).2.2 =
            (-1 : ℝ) • (r •
              CenterRaw.secondNormalizedDisplacement θ.1 r
                (independentRadiusFirstSpectral (θ, r)).1
                (independentRadiusFirstSpectral (θ, r)).2
                (independentRadiusFirstGradient (θ, r)).1
                (independentRadiusFirstGradient (θ, r)).2) := hdisp
        _ = r • (-CenterRaw.secondNormalizedDisplacement θ.1 r
                (independentRadiusFirstSpectral (θ, r)).1
                (independentRadiusFirstSpectral (θ, r)).2
                (independentRadiusFirstGradient (θ, r)).1
                (independentRadiusFirstGradient (θ, r)).2) := by
          rw [smul_smul]
          simp⟩

/-- A zero-radius or punctured projection point admits a raw-frame bracket
    certificate whose bracket is the canonical mixed center bracket. -/
private lemma mixedRawBracketCertificate_of_projectionTube
    (θ : ℝ × ℝ × ℝ) (r : ℝ)
    (hbranch : r = 0 ∨ mixedRawProjectionDomain θ r) :
    ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
      certificate.bracket 0 = mixedCenterBracket θ r := by
  -- The removable branch uses the stationary raw-step identities directly.
  rcases hbranch with rfl | hdomain
  · let u₀ : Fin 2 → ℝ := CenterRaw.firstNormalizedDisplacement θ.1 0 2
    let u₁ : Fin 2 → ℝ := CenterRaw.secondNormalizedDisplacement θ.1 0 2 1 1 1
    have hinput : input θ 0 = (0, 2, 1) := by simp [input]
    have hframe : CenterRaw.firstFrame θ.1 (input θ 0) = 1 := by
      simpa [CenterRaw.firstFrame, CenterRaw.firstStep,
        CenterRaw.initialMetric, CenterRaw.initialGradient, hinput] using
        (rawObservableStep_zeroRadius_frame (TwoPhaseControls.first θ.1))
    have horth : CenterRaw.firstFrame θ.1 (input θ 0) *
        (CenterRaw.firstFrame θ.1 (input θ 0)).transpose = 1 := by
      rw [hframe]
      simp
    have hfirst : (CenterRaw.firstStep θ.1 (input θ 0)).2.2 = (0 : ℝ) • u₀ := by
      simp [u₀, CenterRaw.firstStep, CenterRaw.initialMetric,
        CenterRaw.initialGradient, hinput, rawObservableStep_zeroRadius_base]
    have hsecond : (CenterRaw.secondStep θ.1 (input θ 0)).2.2 = (0 : ℝ) • u₁ := by
      have hstep₁ := rawObservableStep_zeroRadius_scaled (1 * 2) 1 2
        (TwoPhaseControls.first θ.1)
      have hframe₁ := rawObservableStep_zeroRadius_scaled_frame (1 * 2) 2
        (TwoPhaseControls.first θ.1)
      rw [hinput]
      simp only [CenterRaw.secondStep, CenterRaw.secondMetric,
        CenterRaw.secondGradient, CenterRaw.firstFrame, CenterRaw.firstStep,
        CenterRaw.initialMetric, CenterRaw.initialGradient]
      rw [hframe₁, hstep₁]
      simp [u₁, rawObservableStep_zeroRadius_base]
    let certificate : CenterRaw.BracketCertificate θ.1 0 (input θ 0) :=
      { firstNormalized := u₀
        secondNormalized := u₁
        frame_orthogonal := horth
        first_displacement := hfirst
        second_displacement := hsecond }
    refine ⟨certificate, ?_⟩
    have hbracket : certificate.bracket 0 = 0 := by
        simp [certificate, CenterRaw.BracketCertificate.bracket, hframe, u₀, u₁,
        weightedCenterBracket, CenterRaw.firstNormalizedDisplacement,
        CenterRaw.secondNormalizedDisplacement]
        norm_num [div_eq_mul_inv]
    rw [hbracket]
    exact (mixedCenterBracket_zero θ).symm
  · -- On the punctured branch, the frame sign and second displacement sign are paired.
    rcases hdomain with ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
    have hdomain' : mixedRawProjectionDomain θ r :=
      ⟨hr, hθ, hp, hh, hL, hH, hQ⟩
    let p : ℝ := (input θ r).2.1
    let h : ℝ := (input θ r).2.2
    let u₀ : Fin 2 → ℝ := CenterRaw.firstNormalizedDisplacement θ.1 r p
    let u₁ : Fin 2 → ℝ := CenterRaw.secondNormalizedDisplacement θ.1 r
      (independentRadiusFirstSpectral (θ, r)).1
      (independentRadiusFirstSpectral (θ, r)).2
      (independentRadiusFirstGradient (θ, r)).1
      (independentRadiusFirstGradient (θ, r)).2
    have hden : h ^ 2 * p ^ 2 * r ^ 2 *
        (1 + 2 * θ.1 * r + r ^ 2) ≠ 0 := by
      have hdenom : 0 < 1 + 2 * θ.1 * r + r ^ 2 :=
        mixedFirstDisplacement_denominator_pos hdomain'
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (ne_of_gt hh))
          (pow_ne_zero 2 (ne_of_gt hp))) (pow_ne_zero 2 hr))
        (ne_of_gt hdenom)
    have horth : CenterRaw.firstFrame θ.1 (input θ r) *
        (CenterRaw.firstFrame θ.1 (input θ r)).transpose = 1 :=
      mixedRawFirstFrame_mul_transpose_of_projectionDomain θ r hdomain'
    have hfirst : (CenterRaw.firstStep θ.1 (input θ r)).2.2 = r • u₀ := by
      simpa [u₀, p, h, input, CenterRaw.firstStep, CenterRaw.initialMetric,
        CenterRaw.initialGradient] using
        CenterRaw.firstStep_displacement_eq_radius_smul θ.1 r p h hden
    rcases mixedRawSecondDisplacement_eq_signedCanonical θ r hdomain' with
      hplus | hminus
    · let certificate : CenterRaw.BracketCertificate θ.1 r (input θ r) :=
        { firstNormalized := u₀
          secondNormalized := u₁
          frame_orthogonal := horth
          first_displacement := hfirst
          second_displacement := by simpa [u₁] using hplus.2 }
      refine ⟨certificate, ?_⟩
      have hbracket : certificate.bracket 0 = mixedCenterBracket θ r := by
        simp only [certificate, CenterRaw.BracketCertificate.bracket]
        rw [hplus.1]
        simp [u₀, u₁,
          p, mixedCenterBracket, CenterRaw.firstNormalizedDisplacement,
          CenterRaw.secondNormalizedDisplacement, weightedCenterBracket,
          Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        ring
      exact hbracket
    · let certificate : CenterRaw.BracketCertificate θ.1 r (input θ r) :=
        { firstNormalized := u₀
          secondNormalized := -u₁
          frame_orthogonal := horth
          first_displacement := hfirst
          second_displacement := by simpa [u₁] using hminus.2 }
      refine ⟨certificate, ?_⟩
      have hbracket : certificate.bracket 0 = mixedCenterBracket θ r := by
        rw [CenterRaw.BracketCertificate.bracket, hminus.1]
        have hcanonical : weightedCenterBracket
            (EuclideanPlane.frame
              (RealSymmetric2.lowVector
                (independentRadiusFirstMetricTriple (θ, r)).1
                (independentRadiusFirstMetricTriple (θ, r)).2.1
                (independentRadiusFirstMetricTriple (θ, r)).2.2)) u₀ u₁ 0 =
            mixedCenterBracket θ r := by
          simp [u₀, u₁, p, mixedCenterBracket,
            CenterRaw.firstNormalizedDisplacement,
            CenterRaw.secondNormalizedDisplacement, weightedCenterBracket,
            Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          ring
        rw [weightedCenterBracket_neg_neg]
        exact hcanonical
      exact hbracket

/-- The explicit mixed bracket is definitionally the canonical weighted bracket. -/
private lemma mixedCenterBracket_eq_canonicalCenterBracket
    (θ : ℝ × ℝ × ℝ) (r : ℝ) :
    mixedCenterBracket θ r = canonicalCenterBracket θ r := by
  unfold mixedCenterBracket canonicalCenterBracket canonicalFirstFrame
    canonicalFirstNormalizedDisplacement canonicalSecondNormalizedDisplacement
    centerSecondDisplacementLow centerSecondDisplacementHigh
    centerSecondDisplacementGradientLow centerSecondDisplacementGradientHigh
  rw [WeightedCenterBracket.coord_zero_apply]
  simp [CenterRaw.firstNormalizedDisplacement,
    CenterRaw.secondNormalizedDisplacement,
    input]

/-- The zero-filled mixed cubic quotient of the physical center residual is uniformly
    bounded on a common parameter-radius tube. -/
private lemma mixedCenterResidual_zeroFilledQuotient_uniformBound
    (β B : ℝ) (_hβ : 0 < β) (hβ_small : β < 1 / 4) (hB : 0 ≤ B) :
    let Q : (ℝ × ℝ × ℝ) → ℝ → ℝ := fun θ r ↦
      if θ.1 * r ^ (3 : ℕ) = 0 then 0 else
        ((observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2) / (θ.1 * r ^ (3 : ℕ))
    ∃ δ > 0, ∃ C > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      ‖Q θ r‖ ≤ C := by
  dsimp only
  let K : Set (ℝ × ℝ × ℝ) := parameterSet β B
  have hK : IsCompact K := by
    exact parameterSet_isCompact β B
  have hWregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3 (Function.uncurry mixedCenterBracket) (θ, 0) := by
    intro θ hθ
    have hm := independentRadiusFirstMetricTriple_analyticAt θ
    have hframe (i j : Fin 2) : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (EuclideanPlane.frame
            (RealSymmetric2.lowVector
              (independentRadiusFirstMetricTriple z).1
              (independentRadiusFirstMetricTriple z).2.1
              (independentRadiusFirstMetricTriple z).2.2)) i j) (θ, 0) := by
      have houter := RealSymmetric2.analyticOnNhd_frame i j
        ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
      rw [← independentRadiusFirstMetricTriple_zero θ] at houter
      have hcomp := houter.comp hm
      apply hcomp.congr
      filter_upwards [] with z
      rfl
    have hF00 := hframe 0 0
    have hF01 := hframe 0 1
    have hb : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.1) (θ, 0) :=
      analyticAt_fst.comp analyticAt_fst
    have hr : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.2) (θ, 0) := analyticAt_snd
    have hp : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.1) (θ, 0) := by
      change AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          2 + z.1.2.1 * z.1.1 * z.2) (θ, 0)
      have hp' : AnalyticAt ℝ
          (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.2.1) (θ, 0) :=
        analyticAt_fst.comp (analyticAt_snd.comp analyticAt_fst)
      have hb' : AnalyticAt ℝ
          (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ z.1.1) (θ, 0) :=
        analyticAt_fst.comp analyticAt_fst
      have hpoly : AnalyticAt ℝ
          (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
            2 + z.1.2.1 * z.1.1 * z.2) (θ, 0) := by
        have hconst : AnalyticAt ℝ
            (fun _ : (ℝ × ℝ × ℝ) × ℝ ↦ (2 : ℝ)) (θ, 0) := analyticAt_const
        have h := hconst.add ((hp'.mul hb').mul analyticAt_snd)
        apply h.congr
        filter_upwards [] with z
        rfl
      exact hpoly
    have hL : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstSpectral z).1) (θ, 0) :=
      analyticAt_fst.comp (independentRadiusFirstSpectral_analyticAt θ)
    have hH : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstSpectral z).2) (θ, 0) :=
      analyticAt_snd.comp (independentRadiusFirstSpectral_analyticAt θ)
    have hQ : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstGradient z).1) (θ, 0) :=
      analyticAt_fst.comp (independentRadiusFirstGradient_analyticAt θ)
    have hU : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          (independentRadiusFirstGradient z).2) (θ, 0) :=
      analyticAt_snd.comp (independentRadiusFirstGradient_analyticAt θ)
    let den : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
      1 + 2 * z.1.1 * z.2 + z.2 ^ 2
    let beta' : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
      z.2 * (independentRadiusFirstSpectral z).1 *
          (independentRadiusFirstGradient z).1 *
          (z.2 * (independentRadiusFirstSpectral z).1 *
              (independentRadiusFirstGradient z).1 -
            2 * z.1.1 * (independentRadiusFirstSpectral z).2 *
              (independentRadiusFirstGradient z).2) +
        (independentRadiusFirstSpectral z).2 *
          (independentRadiusFirstGradient z).2 *
          ((independentRadiusFirstSpectral z).2 *
              (independentRadiusFirstGradient z).2 -
            2 * z.1.1 * z.2 * (independentRadiusFirstSpectral z).1 *
              (independentRadiusFirstGradient z).1)
    have hden : AnalyticAt ℝ den (θ, 0) := by
      dsimp [den]
      fun_prop
    have hbeta : AnalyticAt ℝ beta' (θ, 0) := by
      dsimp [beta']
      fun_prop
    have hden0 : den (θ, 0) ≠ 0 := by
      simp [den]
    have hbeta0 : beta' (θ, 0) ≠ 0 := by
      simp [beta', independentRadiusFirstSpectral_zero θ,
        independentRadiusFirstGradient_zero θ]
    let alpha : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
      (-(1 / 3 : ℝ)) *
        ((independentRadiusFirstSpectral z).1 *
            (independentRadiusFirstGradient z).1 ^ 2 +
          (independentRadiusFirstSpectral z).2 *
            (independentRadiusFirstGradient z).2 ^ 2) / beta' z
    have halpha : AnalyticAt ℝ alpha (θ, 0) := by
      dsimp [alpha]
      have hnum := (hL.mul (hQ.pow 2)).add (hH.mul (hU.pow 2))
      exact (analyticAt_const.mul hnum).div hbeta hbeta0
    let u0 : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
      (-(2 / 3 : ℝ) * ((input z.1 z.2).2.1 + 1)) / den z
    have hu0 : AnalyticAt ℝ u0 (θ, 0) := by
      dsimp [u0]
      have hplus : AnalyticAt ℝ
          (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ (input z.1 z.2).2.1 + 1) (θ, 0) :=
        hp.add analyticAt_const
      have hscale : AnalyticAt ℝ
          (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
            (-(2 / 3 : ℝ)) * ((input z.1 z.2).2.1 + 1)) (θ, 0) := by
        have hconst : AnalyticAt ℝ
            (fun _ : (ℝ × ℝ × ℝ) × ℝ ↦ (-(2 / 3 : ℝ))) (θ, 0) :=
          analyticAt_const
        have h := hconst.mul hplus
        exact h
      exact hscale.div hden hden0
    let u10 : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
      alpha z * (z.2 * (independentRadiusFirstSpectral z).1 *
        (independentRadiusFirstGradient z).1)
    let u11 : ((ℝ × ℝ × ℝ) × ℝ) → ℝ := fun z ↦
      alpha z * ((independentRadiusFirstSpectral z).2 *
        (independentRadiusFirstGradient z).2)
    have hu10 : AnalyticAt ℝ u10 (θ, 0) := by
      dsimp [u10]
      exact halpha.mul (((hr.mul hL).mul hQ))
    have hu11 : AnalyticAt ℝ u11 (θ, 0) := by
      dsimp [u11]
      exact halpha.mul (hH.mul hU)
    have hsum := (hF00.mul hu11).add (hF01.mul hu10)
    have hscaled : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
          2 * ((EuclideanPlane.frame
            (RealSymmetric2.lowVector
              (independentRadiusFirstMetricTriple z).1
              (independentRadiusFirstMetricTriple z).2.1
              (independentRadiusFirstMetricTriple z).2.2)) 0 0 * u11 z +
            (EuclideanPlane.frame
              (RealSymmetric2.lowVector
                (independentRadiusFirstMetricTriple z).1
                (independentRadiusFirstMetricTriple z).2.1
                (independentRadiusFirstMetricTriple z).2.2)) 0 1 * u10 z)) (θ, 0) := by
      exact analyticAt_const.mul hsum
    have hbracket := hu0.neg.add hscaled
    have hbracket' : AnalyticAt ℝ
        (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ mixedCenterBracket z.1 z.2) (θ, 0) := by
      apply hbracket.congr
      filter_upwards [] with z
      simp [u0, u10, u11, mixedCenterBracket, input]
      ring
    exact hbracket'.contDiffAt (n := 3)
  have hquadratic : ∀ θ, θ ∈ K →
      HasQuadraticGerm (mixedCenterBracket θ) 0
        (centerBracketCoefficient θ)
        (canonicalCenterBracketQuadraticCoeff θ
          (centerSecondDisplacementScaleLinearCoeff θ)
          (centerSecondDisplacementScaleQuadraticCoeff θ)) := by
    intro θ hθ
    have h := canonicalCenterBracket_quadraticGerm_of_centerScale θ
    have heq : mixedCenterBracket θ = canonicalCenterBracket θ := by
      funext r
      exact mixedCenterBracket_eq_canonicalCenterBracket θ r
    rw [heq]
    exact h
  have hW : IndependentRadiusTruncatedGerm mixedCenterBracket K 2
      (fun n θ ↦ (![0, centerBracketCoefficient θ] : Fin 2 → ℝ) n) := by
    exact WeightedCenterBracket.truncatedGerm_of_coordZero_quadraticGerm
      hWregular hquadratic
  obtain ⟨δ₀, hδ₀, htube⟩ :=
    mixedRawProjectionDomain_uniformTube β B hβ_small hB
  have hcertificate : ∀ θ, θ ∈ K → ∀ r : ℝ, |r| < δ₀ →
      ∃ certificate : CenterRaw.BracketCertificate θ.1 r (input θ r),
        certificate.bracket 0 = mixedCenterBracket θ r := by
    intro θ hθ r hr
    exact mixedRawBracketCertificate_of_projectionTube θ r (htube θ hθ r hr)
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    centerResidual_zeroFilledQuotient_uniformBound_of_bracketGerm
      hK hW δ₀ hδ₀ hcertificate
  refine ⟨δ, hδ, C, hC, ?_⟩
  intro θ hθ r hr
  simpa [centerBracketZeroFilledQuotient, physicalCenterResidual] using
    hbound θ hθ r hr

/-- The unscaled physical center residual has the prescribed mixed-variable cubic
    bound. -/
lemma unscaledCenterResidual_uniformBound (β B : ℝ) (hβ : 0 < β)
    (hβ_small : β < 1 / 4) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ δ > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
      ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        (-(2 * θ.1 ^ 2 * (6 * θ.2.2 - θ.2.1 + 96) / 9) * r ^ 2)‖ ≤
      C * |θ.1| * |r| ^ (3 : ℝ) :=
  by
    -- Divide the center residual by its mixed cubic weight on the generic branch;
    -- the two zero branches are handled before invoking the factorization adapter.
    let Q : (ℝ × ℝ × ℝ) → ℝ → ℝ := fun θ r ↦
      if θ.1 * r ^ (3 : ℕ) = 0 then 0 else
        ((observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          centerDriftCoefficient θ * r ^ 2) / (θ.1 * r ^ (3 : ℕ))
    have hQ : ∃ δ > 0, ∃ C > 0, ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ →
        ‖Q θ r‖ ≤ C := by
      simpa only [Q] using
        mixedCenterResidual_zeroFilledQuotient_uniformBound β B hβ hβ_small hB
    -- Specialize the common projection domain at zero control scale.  Its radius
    -- tube is intersected with the quotient tube before the branch assembly.
    let θzero : ℝ × ℝ × ℝ := (0, 0, 0)
    have hθzero : θzero ∈ parameterSet β B := by
      unfold θzero parameterSet
      constructor
      · exact ⟨by linarith, by linarith⟩
      · simpa [Metric.mem_closedBall] using hB
    have hprojection := mixedRawProjectionDomain_eventually β B hβ_small hθzero
    have hpath : Tendsto (fun r : ℝ ↦ (θzero, r)) (𝓝 0) (𝓝 (θzero, 0)) := by
      have hpathRaw : Tendsto (fun r : ℝ ↦ (θzero, id r)) (𝓝 0)
          (𝓝 θzero ×ˢ 𝓝 0) := tendsto_const_nhds.prodMk tendsto_id
      have hfun : (fun r : ℝ ↦ (θzero, id r)) = (fun r : ℝ ↦ (θzero, r)) := by
        funext r
        rfl
      rw [hfun] at hpathRaw
      simpa only [nhds_prod_eq] using hpathRaw
    have hprojectionRadius : ∀ᶠ r : ℝ in 𝓝 0,
        r = 0 ∨ mixedRawProjectionDomain θzero r :=
      hpath.eventually hprojection
    obtain ⟨δframe, hδframe, hframeRule⟩ :=
      Metric.eventually_nhds_iff.mp hprojectionRadius
    obtain ⟨δQ, hδQ, C, hC, hQ⟩ := hQ
    let δ := min δQ δframe
    have hδ : 0 < δ := lt_min hδQ hδframe
    have hQsmall : ∀ θ ∈ parameterSet β B, ∀ r : ℝ, |r| < δ → ‖Q θ r‖ ≤ C := by
      intro θ hθ r hr
      exact hQ θ hθ r (lt_of_lt_of_le hr (min_le_left δQ δframe))
    have hfactor : ∀ θ r, |r| < δ →
        (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
            centerDriftCoefficient θ * r ^ 2 =
          (θ.1 * r ^ (3 : ℕ)) • Q θ r := by
      have hscale : ∀ θ r, |r| < δ → θ.1 = 0 →
          (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
            centerDriftCoefficient θ * r ^ 2 = 0 := by
        -- The zero control matrices are identities, so the two gradient increments
        -- telescope after transport through the locally orthogonal first frame.
        intro θ r hr hθ
        have hcoefficient : centerDriftCoefficient θ = 0 := by
          simp [centerDriftCoefficient, hθ]
        rw [hcoefficient]
        simp only [zero_mul, sub_zero]
        have hinput : input θ r = input θzero r := by
          simp [input, θzero, hθ]
        rw [hθ, hinput]
        have hrframe : |r| < δframe :=
          lt_of_lt_of_le hr (min_le_right δQ δframe)
        have hbranch := hframeRule (by simpa [Real.dist_eq] using hrframe)
        rcases hbranch with hrzero | hdomain
        · subst r
          have hprojection := mixedObservable_zeroRadiusProjectionData 0
          simpa [θzero, input] using congrArg
            (fun t : ℝ × ℝ × EuclideanSpace ℝ (Fin 2) ↦ t.2.2 0) hprojection
        · let H₀ : Matrix (Fin 2) (Fin 2) ℝ :=
            Matrix.diagonal ![(input θzero r).2.2 * (input θzero r).2.1 * r ^ 2,
              (input θzero r).2.2]
          let g₀ : Fin 2 → ℝ := ![(1 : ℝ), (input θzero r).2.1 * r]
          let firstStep := rawObservableStep H₀ g₀ (TwoPhaseControls.first 0)
          let firstFrame := OrientedEigenframe.frame
            (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
            (WithLp.toLp 2 firstStep.2.1)
          let H₁ := firstFrame.transpose * firstStep.1 * firstFrame
          let g₁ := firstFrame.transpose *ᵥ firstStep.2.1
          let secondStep := rawObservableStep H₁ g₁ (TwoPhaseControls.second 0)
          have horth : firstFrame * firstFrame.transpose = 1 := by
            simpa only [H₀, g₀, firstStep, firstFrame] using
              mixedRawFirstFrame_mul_transpose_of_projectionDomain θzero r hdomain
          have hfirstControl :
              TwoPhaseControls.first 0 = ⟨1, (2 / 3 : ℝ)⟩ := by
            unfold TwoPhaseControls.first
            congr 1
            ext i j
            fin_cases i <;> fin_cases j <;> simp [RealSymmetric2.matrix]
          have hsecondControl :
              TwoPhaseControls.second 0 = ⟨1, (1 / 3 : ℝ)⟩ := by
            unfold TwoPhaseControls.second
            congr 1
            ext i j
            fin_cases i <;> fin_cases j <;> simp [RealSymmetric2.matrix]
          have hfirst : firstStep.2.1 = g₀ + firstStep.2.2 := by
            simpa [firstStep, hfirstControl] using
              rawObservableStep_gradient_eq_add_displacement_of_identity H₀ g₀ (2 / 3)
          have hsecond : secondStep.2.1 = g₁ + secondStep.2.2 := by
            simpa [secondStep, hsecondControl] using
              rawObservableStep_gradient_eq_add_displacement_of_identity H₁ g₁ (1 / 3)
          have hcenter := centerDisplacement_zero_of_identityGradientIncrements
            firstFrame g₀ firstStep.2.1 secondStep.2.1 firstStep.2.2
            secondStep.2.2 horth hfirst hsecond
          have hcenterLow := congrArg
            (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) hcenter
          simpa [observableMap, input, θzero, H₀, g₀, firstStep, firstFrame,
            H₁, g₁, secondStep] using hcenterLow
      have hradius : ∀ θ,
          (observableMap θ.1 (input θ 0)).fullCenterDisplacement 0 -
            centerDriftCoefficient θ * (0 : ℝ) ^ 2 = 0 :=
        mixedObservable_zeroRadiusCenterResidual
      have hpunctured : ∀ θ r, |r| < δ → θ.1 ≠ 0 → r ≠ 0 →
          (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
            centerDriftCoefficient θ * r ^ 2 =
          (θ.1 * r ^ (3 : ℕ)) • Q θ r := by
        intro θ r hr hθ hr0
        have hzero : θ.1 * r ^ (3 : ℕ) ≠ 0 :=
          mul_ne_zero hθ (pow_ne_zero 3 hr0)
        simp only [Q, hzero, if_false, smul_eq_mul]
        rw [mul_div_cancel₀ _ hzero]
      intro θ r hr
      by_cases hθ : θ.1 = 0
      · rw [hscale θ r hr hθ, hθ]
        simp
      · by_cases hr0 : r = 0
        · subst r
          rw [hradius θ]
          simp
        · exact hpunctured θ r hr hθ hr0
    obtain ⟨C', hC', hbound⟩ := localScalarCubicBound δ hfactor ⟨C, hC, hQsmall⟩
    refine ⟨C', hC', δ, hδ, ?_⟩
    intro θ hθ r hr
    simpa only [centerDriftCoefficient] using hbound θ hθ r hr

/-- Appendix Lemma A.6 (Mixed-variable physical drift expansion) (1): uniformly
    on a bounded mixed-parameter region, the amplitude ratio has its specified
    quadratic term with an order-three remainder in the independent radius. -/
theorem amplitudeExpansion (β B : ℝ) (hβ : 0 < β) (hβ_small : β < 1 / 4)
    (hB : 0 ≤ B) :
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦
        let observable := observableMap θ.1 (input θ r)
        observable.amplitudeRatio - 1 -
          ((θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18) * r ^ 2)
      (parameterSet β B) C 3 := by
  -- Consume the transported coefficient germ, then normalize its finite sum.
  have hthree : 0 < (3 : ℕ) := by norm_num
  have hK : IsCompact (parameterSet β B) := parameterSet_isCompact β B
  have hGerms := mixedObservableTruncatedGerms β B hβ hβ_small hB
  obtain ⟨C, hC, hraw⟩ :=
    uniformRemainderOn_of_independentRadiusTruncatedGerm hthree hK hGerms.1
  refine ⟨C, hC, ?_⟩
  obtain ⟨δ, hδ, hbound⟩ := Asymptotics.IsUniformRemainderOn.exists_bound hraw
  refine Asymptotics.IsUniformRemainderOn.of_bound hδ ?_
  intro θ hθ r hr
  have hbound' := hbound θ hθ r hr
  dsimp only at hbound' ⊢
  rw [mixedAmplitudeCoefficientPolynomial] at hbound'
  calc
    ‖(observableMap θ.1 (input θ r)).amplitudeRatio - 1 -
        ((θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18) * r ^ 2‖ =
        ‖(observableMap θ.1 (input θ r)).amplitudeRatio -
          (1 + ((θ.1 ^ 2 * (24 * θ.2.2 - 4 * θ.2.1 + 384) - 117) / 18) * r ^ 2)‖ := by
      congr 1
      ring
    _ ≤ C * |r| ^ (3 : ℝ) := by
      convert hbound' using 1
      norm_num [Real.norm_eq_abs, Real.rpow_natCast]

/- The angle assembly is identical after the two-term coefficient polynomial is reduced. -/

/-- Appendix Lemma A.6 (Mixed-variable physical drift expansion) (2): uniformly
    on a bounded mixed-parameter region, the real signed frame-angle increment
    is `-3 * r` up to an order-two remainder. -/
theorem frameAngleExpansion (β B : ℝ) (hβ : 0 < β) (hβ_small : β < 1 / 4)
    (hB : 0 ≤ B) :
    ∃ C > 0, Asymptotics.IsUniformRemainderOn
      (fun θ r ↦
        let observable := observableMap θ.1 (input θ r)
        observable.frameAngleIncrement - (-3 * r))
      (parameterSet β B) C 2 := by
  -- The transported angle germ supplies the compact uniform radius bound.
  have htwo : 0 < (2 : ℕ) := by norm_num
  have hK : IsCompact (parameterSet β B) := parameterSet_isCompact β B
  have hGerms := mixedObservableTruncatedGerms β B hβ hβ_small hB
  obtain ⟨C, hC, hraw⟩ :=
    uniformRemainderOn_of_independentRadiusTruncatedGerm htwo hK hGerms.2
  refine ⟨C, hC, ?_⟩
  obtain ⟨δ, hδ, hbound⟩ := Asymptotics.IsUniformRemainderOn.exists_bound hraw
  refine Asymptotics.IsUniformRemainderOn.of_bound hδ ?_
  intro θ hθ r hr
  have hbound' := hbound θ hθ r hr
  dsimp only at hbound' ⊢
  rw [mixedFrameAngleCoefficientPolynomial] at hbound'
  convert hbound' using 1
  norm_num [Real.norm_eq_abs, Real.rpow_natCast]

/-- A positive real scale factors out of a reassociated scalar residual norm. -/
private lemma norm_scale_sub_reassociated_of_pos
    (G x a q : ℝ) (hG : 0 < G) :
    ‖G * x - a * G * q‖ = G * ‖x - a * q‖ := by
  -- First reassociate the residual algebraically, then evaluate the norm of the
  -- positive scalar factor.
  have hfactor : G * x - a * G * q = G * (x - a * q) := by
    ring
  rw [hfactor, norm_mul, Real.norm_eq_abs, abs_of_pos hG]

/-- Appendix Lemma A.6 (Mixed-variable physical drift expansion) (3): uniformly
    on a bounded mixed-parameter region, the incoming-low-frame center
    displacement has its specified quadratic drift with a joint
    `G * |b| * |r| ^ 3` bound. -/
theorem centerDisplacementExpansion (G β B : ℝ) (hG : 0 < G) (hβ : 0 < β)
    (hβ_small : β < 1 / 4) (hB : 0 ≤ B) :
    ∃ C > 0, Asymptotics.IsBigOWith C
      (principal (parameterSet β B) ×ˢ 𝓝 0)
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦
        let θ := z.1
        let r := z.2
        let observable := observableMap θ.1 (input θ r)
        G * observable.fullCenterDisplacement 0 -
          (-(2 * θ.1 ^ 2 * (6 * θ.2.2 - θ.2.1 + 96) / 9) * G * r ^ 2))
      (fun z : (ℝ × ℝ × ℝ) × ℝ ↦ G * |z.1.1| * |z.2| ^ 3) := by
  -- Scale the unscaled residual estimate by the positive constant `G`.
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    unscaledCenterResidual_uniformBound β B hβ hβ_small hB
  refine ⟨C, hC, ?_⟩
  apply Asymptotics.IsBigOWith.of_bound
  refine Metric.eventually_prod_nhds_iff.mpr
    ⟨fun θ ↦ θ ∈ parameterSet β B,
      Filter.eventually_principal.mpr (fun θ hθ ↦ hθ), δ, hδ, ?_⟩
  intro θ hθ r hr
  dsimp only
  have hr' : |r| < δ := by
    simpa only [Real.dist_0_eq_abs] using hr
  have hres := hbound θ hθ r hr'
  let a := -(2 * θ.1 ^ 2 * (6 * θ.2.2 - θ.2.1 + 96) / 9)
  calc
    ‖G * (observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
        (a * G * r ^ 2)‖ =
        G * ‖(observableMap θ.1 (input θ r)).fullCenterDisplacement 0 -
          a * r ^ 2‖ := by
      exact norm_scale_sub_reassociated_of_pos G
        ((observableMap θ.1 (input θ r)).fullCenterDisplacement 0) a (r ^ 2) hG
    _ ≤ G * (C * |θ.1| * |r| ^ (3 : ℝ)) := by
      have hscaled := mul_le_mul_of_nonneg_left hres hG.le
      dsimp [a]
      exact hscaled
    _ ≤ C * ‖G * |θ.1| * |r| ^ (3 : ℝ)‖ := by
      have hnonneg : 0 ≤ G * |θ.1| * |r| ^ (3 : ℝ) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      exact le_of_eq (by ring)
  all_goals
    have hp : |r| ^ (3 : ℝ) = |r| ^ (3 : ℕ) :=
      (absPow_nat_eq_realRpow r 3).symm
    rw [hp]

end DFP.TwoLeg.Mixed
