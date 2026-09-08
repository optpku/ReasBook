module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedMap
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables
import all ReasLib.LinearAlgebra.Matrix.OrientedEigenframe
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2
import all ReasLib.Optimization.DFP.AbstractSecantStep
import all ReasLib.Optimization.DFP.InverseUpdate
import all ReasLib.Optimization.DFP.TwoPhaseControls
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

public section

noncomputable section

open scoped EuclideanSpace Matrix Topology

namespace DFP.TwoLeg.Mixed

/-- One inverse-form DFP step together with its updated gradient and displacement. -/
def rawObservableStep (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Fin 2 → ℝ)
    (control : PlanarDFPControl) :
    Matrix (Fin 2) (Fin 2) ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  let v := H *ᵥ g
  let α := control.tau * (g ⬝ᵥ v) / (v ⬝ᵥ (control.matrix *ᵥ v))
  let s := -(α • v)
  let y := control.matrix *ᵥ s
  (Matrix.inverseDFPUpdate H s y, g + y, s)

/-- Evaluate every normalized two-leg observable with independent control scale `b`
and canonical-state radius `r`. -/
def observableMap (b : ℝ) (state : ℝ × ℝ × ℝ) : CompleteTwoLegObservables :=
  let r := state.1
  let p := state.2.1
  let h := state.2.2
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h * p * r ^ 2, h]
  let g₀Raw : Fin 2 → ℝ := ![(1 : ℝ), p * r]
  let firstStep := rawObservableStep H₀ g₀Raw (TwoPhaseControls.first b)
  let F₁ := OrientedEigenframe.frame
    (firstStep.1 0 0) (firstStep.1 0 1) (firstStep.1 1 1)
    (WithLp.toLp 2 firstStep.2.1)
  let H₁ := F₁.transpose * firstStep.1 * F₁
  let g₁Raw := F₁.transpose *ᵥ firstStep.2.1
  let secondStep := rawObservableStep H₁ g₁Raw (TwoPhaseControls.second b)
  let F₂ := OrientedEigenframe.frame
    (secondStep.1 0 0) (secondStep.1 0 1) (secondStep.1 1 1)
    (WithLp.toLp 2 secondStep.2.1)
  let g₂Frame := F₂.transpose *ᵥ secondStep.2.1
  let s₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 firstStep.2.2
  let s₁ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (F₁ *ᵥ secondStep.2.2)
  let g₀ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 g₀Raw
  let g₁ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 firstStep.2.1
  let g₂ : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 (F₁ *ᵥ secondStep.2.1)
  { amplitudeRatio := g₂Frame 0
    frameAngleIncrement := EuclideanPlane.SignedAngle.coordinate (F₁ * F₂)
    halfCenterDisplacement := s₀ - (g₁ - g₀)
    fullCenterDisplacement := s₀ + s₁ - (g₂ - g₀)
    firstEndpointAngleIncrement := EuclideanPlane.orientation.oangle g₀ g₁
    secondEndpointAngleIncrement := EuclideanPlane.orientation.oangle g₁ g₂
    firstStepNorm := ‖s₀‖
    secondStepNorm := ‖s₁‖
    initialGradientNorm := ‖g₀‖
    intermediateGradientNorm := ‖g₁‖
    finalGradientNorm := ‖g₂‖ }

/- The three scalar/vector projections used by the mixed physical drift are kept at
   the owner boundary so downstream normal-form proofs consume one canonical evaluator. -/

/-- The amplitude, relative-frame angle, and full-center projections of the mixed evaluator. -/
def observableMap_projectionData (b : ℝ) (state : ℝ × ℝ × ℝ) :
    ℝ × ℝ × EuclideanSpace ℝ (Fin 2) :=
  let observable := observableMap b state
  (observable.amplitudeRatio, observable.frameAngleIncrement,
    observable.fullCenterDisplacement)

/-- The projection tuple is exactly the corresponding fields of `observableMap`. -/
lemma observableMap_projectionData_eq_fields (b : ℝ) (state : ℝ × ℝ × ℝ) :
    observableMap_projectionData b state =
      ((observableMap b state).amplitudeRatio,
        (observableMap b state).frameAngleIncrement,
        (observableMap b state).fullCenterDisplacement) := by
  rfl

/-- Helper for Appendix Lemma A.6: the first control is positive definite for every
signed scale of absolute value less than `1 / 4`. -/
private lemma firstControl_signedScale_posDef (ε : ℝ) (hε : |ε| < (1 / 4 : ℝ)) :
    (TwoPhaseControls.first ε).matrix.PosDef := by
  rw [TwoPhaseControls.first_matrix]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro x hx
    have hleft : -(1 / 4 : ℝ) < ε := (abs_lt.mp hε).1
    have hright : ε < (1 / 4 : ℝ) := (abs_lt.mp hε).2
    have hs : 0 < x 0 ^ 2 + x 1 ^ 2 := by
      have hc : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra hn
        apply hx
        funext i
        fin_cases i
        · exact not_ne_iff.mp (not_or.mp hn).1
        · exact not_ne_iff.mp (not_or.mp hn).2
      rcases hc with h0 | h1
      · nlinarith [sq_pos_of_ne_zero h0]
      · nlinarith [sq_pos_of_ne_zero h1]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]

/-- Helper for Appendix Lemma A.6: the second control is positive definite for every
signed scale of absolute value less than `1 / 4`. -/
private lemma secondControl_signedScale_posDef (ε : ℝ) (hε : |ε| < (1 / 4 : ℝ)) :
    (TwoPhaseControls.second ε).matrix.PosDef := by
  rw [TwoPhaseControls.second_matrix]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> simp
  · intro x hx
    have hleft : -(1 / 4 : ℝ) < ε := (abs_lt.mp hε).1
    have hright : ε < (1 / 4 : ℝ) := (abs_lt.mp hε).2
    have hs : 0 < x 0 ^ 2 + x 1 ^ 2 := by
      have hc : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
        by_contra hn
        apply hx
        funext i
        fin_cases i
        · exact not_ne_iff.mp (not_or.mp hn).1
        · exact not_ne_iff.mp (not_or.mp hn).2
      rcases hc with h0 | h1
      · nlinarith [sq_pos_of_ne_zero h0]
      · nlinarith [sq_pos_of_ne_zero h1]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0 - x 1)]

/-- Helper for Appendix Lemma A.6: gradient orientation selects the canonical first-leg
eigenframe when the low frame coordinate is positive. -/
private lemma orientedFirstOutputFrame_eq (ε p h : ℝ)
    (hcoord : 0 < (DFP.FirstLeg.coordinates ε p h).1) :
    OrientedEigenframe.frame
        (DFP.FirstLeg.outputMetric ε p h 0 0)
        (DFP.FirstLeg.outputMetric ε p h 0 1)
        (DFP.FirstLeg.outputMetric ε p h 1 1)
        (WithLp.toLp 2 (DFP.FirstLeg.outputGradient ε p h)) =
      DFP.FirstLeg.frame ε p h := by
  unfold OrientedEigenframe.frame OrientedEigenframe.lowVector
  split_ifs with hif
  · rfl
  · exfalso
    have hinner : inner ℝ
        (RealSymmetric2.lowVector
          (DFP.FirstLeg.outputMetric ε p h 0 0)
          (DFP.FirstLeg.outputMetric ε p h 0 1)
          (DFP.FirstLeg.outputMetric ε p h 1 1))
        (WithLp.toLp 2 (DFP.FirstLeg.outputGradient ε p h)) =
        (DFP.FirstLeg.coordinates ε p h).1 := by
      simp [DFP.FirstLeg.coordinates, DFP.FirstLeg.frame,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
        EuclideanPlane.frame, PiLp.inner_apply]
      ring
    apply (not_lt_of_ge (le_of_not_gt hif))
    rw [hinner]
    exact hcoord

/-- Helper for Appendix Lemma A.6: gradient orientation selects the canonical second-leg
eigenframe when the low frame coordinate is positive. -/
private lemma orientedSecondOutputFrame_eq (ε p h : ℝ)
    (hcoord : 0 < (DFP.SecondLeg.coordinates ε p h).1) :
    OrientedEigenframe.frame
        (DFP.SecondLeg.outputMetric ε p h 0 0)
        (DFP.SecondLeg.outputMetric ε p h 0 1)
        (DFP.SecondLeg.outputMetric ε p h 1 1)
        (WithLp.toLp 2 (DFP.SecondLeg.outputGradient ε p h)) =
      DFP.SecondLeg.frame ε p h := by
  unfold OrientedEigenframe.frame OrientedEigenframe.lowVector
  split_ifs with hif
  · rfl
  · exfalso
    have hinner : inner ℝ
        (RealSymmetric2.lowVector
          (DFP.SecondLeg.outputMetric ε p h 0 0)
          (DFP.SecondLeg.outputMetric ε p h 0 1)
          (DFP.SecondLeg.outputMetric ε p h 1 1))
        (WithLp.toLp 2 (DFP.SecondLeg.outputGradient ε p h)) =
        (DFP.SecondLeg.coordinates ε p h).1 := by
      simp [DFP.SecondLeg.coordinates, DFP.SecondLeg.frame,
        Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.transpose_apply,
        EuclideanPlane.frame, PiLp.inner_apply]
      ring
    apply (not_lt_of_ge (le_of_not_gt hif))
    rw [hinner]
    exact hcoord

/-- Helper for Appendix Lemma A.6: under the local positivity and frame interfaces,
the mixed observable evaluator at radius `ε ^ 2` equals the fixed-scale evaluator. -/
private lemma observableMap_fixedScale_of_localData
    (ε p h : ℝ) (hε : ε ≠ 0) (hsmall : |ε| < (1 / 4 : ℝ))
    (hp : 0 < p) (hh : 0 < h)
    (hcoord1 : 0 < (DFP.FirstLeg.coordinates ε p h).1)
    (hcoord2 : 0 < (DFP.SecondLeg.coordinates ε p h).1)
    (hL : 0 < (DFP.FirstLeg.spectralFactors ε p h).1)
    (hH : 0 < (DFP.FirstLeg.spectralFactors ε p h).2)
    (hQ : 0 < (DFP.FirstLeg.gradientFactors ε p h).1)
    (hdiag1 : (DFP.FirstLeg.frame ε p h).transpose *
        DFP.FirstLeg.outputMetric ε p h * DFP.FirstLeg.frame ε p h =
      Matrix.diagonal ![ε ^ 4 * (DFP.FirstLeg.spectralFactors ε p h).1,
        (DFP.FirstLeg.spectralFactors ε p h).2])
    (hgrad1 : ∀ G : ℝ,
      (DFP.FirstLeg.frame ε p h).transpose *ᵥ
          (G • DFP.FirstLeg.outputGradient ε p h) =
        G • ![(DFP.FirstLeg.gradientFactors ε p h).1,
          ε ^ 2 * (DFP.FirstLeg.gradientFactors ε p h).2]) :
    observableMap ε (ε ^ 2, p, h) = DFP.TwoLeg.observableMap (ε, p, h) := by
  have hε4 : 0 < ε ^ 4 := by
    rw [show ε ^ 4 = (ε ^ 2) ^ 2 by ring]
    exact pow_pos (sq_pos_of_ne_zero hε) 2
  let H₀ : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.diagonal ![h * p * ε ^ 4, h]
  let g₀ : Fin 2 → ℝ := ![(1 : ℝ), p * ε ^ 2]
  have hH₀ : H₀.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · dsimp [H₀]
      exact mul_pos (mul_pos hh hp) hε4
    · dsimp [H₀]
      exact hh
  have hA₀ : (TwoPhaseControls.first ε).matrix.PosDef :=
    firstControl_signedScale_posDef ε hsmall
  have hτ₀ : 0 < (TwoPhaseControls.first ε).tau := by
    rw [← TwoPhaseControls.phase_zero]
    exact TwoPhaseControls.tau_pos ε 0
  have hg₀ : g₀ ≠ 0 := by
    intro hz
    have hz0 := congrArg (fun q : Fin 2 → ℝ ↦ q 0) hz
    change (1 : ℝ) = 0 at hz0
    norm_num at hz0
  let z₀ := DFP.AbstractSecantStep.ofMatrices H₀ g₀
    (TwoPhaseControls.first ε).matrix (TwoPhaseControls.first ε).tau
    hH₀ hA₀ hτ₀ hg₀
  have hrawz₀ : rawObservableStep H₀ g₀ (TwoPhaseControls.first ε) =
      (z₀.nextInverseHessian, z₀.nextGradient, z₀.displacement) := by
    rfl
  have hout₀ : (z₀.nextInverseHessian, z₀.nextGradient) =
      (DFP.FirstLeg.outputMetric ε p h, DFP.FirstLeg.outputGradient ε p h) := by
    have hHspec : z₀.inverseHessian = Matrix.diagonal ![h * p * ε ^ 4, h] := by
      rfl
    have hgspec : z₀.gradient = (1 : ℝ) • ![(1 : ℝ), p * ε ^ 2] := by
      dsimp [z₀, DFP.AbstractSecantStep.ofMatrices, g₀]
      simp
    have hAspec : z₀.secantMatrix = (TwoPhaseControls.first ε).matrix := by
      rfl
    have hτspec : z₀.tau = (TwoPhaseControls.first ε).tau := by
      rfl
    simpa using DFP.FirstLeg.outputEqStep z₀ ε p h 1
      hHspec hgspec hAspec hτspec
  have hmetric₀ : z₀.nextInverseHessian = DFP.FirstLeg.outputMetric ε p h :=
    congrArg Prod.fst hout₀
  have hgradient₀ : z₀.nextGradient = DFP.FirstLeg.outputGradient ε p h :=
    congrArg Prod.snd hout₀
  have hstep₀ : rawObservableStep H₀ g₀ (TwoPhaseControls.first ε) =
      (DFP.FirstLeg.outputMetric ε p h,
        DFP.FirstLeg.outputGradient ε p h, z₀.displacement) := by
    rw [hrawz₀, hmetric₀, hgradient₀]
  have hframe₁ := orientedFirstOutputFrame_eq ε p h hcoord1
  have hgrad₁ : (DFP.FirstLeg.frame ε p h).transpose *ᵥ
      DFP.FirstLeg.outputGradient ε p h =
      ![(DFP.FirstLeg.gradientFactors ε p h).1,
        ε ^ 2 * (DFP.FirstLeg.gradientFactors ε p h).2] := by
    simpa using hgrad1 1
  let H₁ : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal
    ![ε ^ 4 * (DFP.FirstLeg.spectralFactors ε p h).1,
      (DFP.FirstLeg.spectralFactors ε p h).2]
  let g₁ : Fin 2 → ℝ := ![(DFP.FirstLeg.gradientFactors ε p h).1,
    ε ^ 2 * (DFP.FirstLeg.gradientFactors ε p h).2]
  have hH₁ : H₁.PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    fin_cases i
    · dsimp [H₁]
      exact mul_pos hε4 hL
    · dsimp [H₁]
      exact hH
  have hA₁ : (TwoPhaseControls.second ε).matrix.PosDef :=
    secondControl_signedScale_posDef ε hsmall
  have hτ₁ : 0 < (TwoPhaseControls.second ε).tau := by
    rw [← TwoPhaseControls.phase_one]
    exact TwoPhaseControls.tau_pos ε 1
  have hg₁ : g₁ ≠ 0 := by
    intro hz
    have hz0 := congrArg (fun q : Fin 2 → ℝ ↦ q 0) hz
    exact (ne_of_gt hQ) (by simpa [g₁] using hz0)
  let z₁ := DFP.AbstractSecantStep.ofMatrices H₁ g₁
    (TwoPhaseControls.second ε).matrix (TwoPhaseControls.second ε).tau
    hH₁ hA₁ hτ₁ hg₁
  have hrawz₁ : rawObservableStep H₁ g₁ (TwoPhaseControls.second ε) =
      (z₁.nextInverseHessian, z₁.nextGradient, z₁.displacement) := by
    rfl
  have hout₁ : (z₁.nextInverseHessian, z₁.nextGradient) =
      (DFP.SecondLeg.outputMetric ε p h, DFP.SecondLeg.outputGradient ε p h) := by
    have hHspec : z₁.inverseHessian = Matrix.diagonal
        ![ε ^ 4 * (DFP.FirstLeg.spectralFactors ε p h).1,
          (DFP.FirstLeg.spectralFactors ε p h).2] := by
      rfl
    have hgspec : z₁.gradient = (1 : ℝ) • ![
        (DFP.FirstLeg.gradientFactors ε p h).1,
        ε ^ 2 * (DFP.FirstLeg.gradientFactors ε p h).2] := by
      dsimp [z₁, DFP.AbstractSecantStep.ofMatrices, g₁]
      simp
    have hAspec : z₁.secantMatrix = (TwoPhaseControls.second ε).matrix := by
      rfl
    have hτspec : z₁.tau = (TwoPhaseControls.second ε).tau := by
      rfl
    simpa using DFP.SecondLeg.outputEqStep z₁ ε p h 1
      hHspec hgspec hAspec hτspec
  have hmetric₁ : z₁.nextInverseHessian = DFP.SecondLeg.outputMetric ε p h :=
    congrArg Prod.fst hout₁
  have hgradient₁ : z₁.nextGradient = DFP.SecondLeg.outputGradient ε p h :=
    congrArg Prod.snd hout₁
  have hstep₁ : rawObservableStep H₁ g₁ (TwoPhaseControls.second ε) =
      (DFP.SecondLeg.outputMetric ε p h,
        DFP.SecondLeg.outputGradient ε p h, z₁.displacement) := by
    rw [hrawz₁, hmetric₁, hgradient₁]
  have hframe₂ := orientedSecondOutputFrame_eq ε p h hcoord2
  have hpow : (ε ^ 2) ^ 2 = ε ^ 4 := by ring
  unfold observableMap
  dsimp only
  rw [hpow, hstep₀, hframe₁, hdiag1, hgrad₁, hstep₁, hframe₂]
  unfold DFP.TwoLeg.observableMap
  rfl

/-- Away from zero signed scale and near the canonical base state, specializing
the independent radius to the squared scale recovers the fixed-scale complete
observable evaluator. -/
theorem observableMap_fixedScale :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      x.1 ≠ 0 →
        observableMap x.1 (x.1 ^ 2, x.2.1, x.2.2) = DFP.TwoLeg.observableMap x := by
  have hsmall : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      |x.1| < (1 / 4 : ℝ) := by
    have hc : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ |x.1|) (0, 2, 1) :=
      continuousAt_fst.abs
    exact hc.eventually (Iio_mem_nhds (by norm_num))
  have hp : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < x.2.1 := by
    have hc : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) :=
      continuousAt_fst.comp continuousAt_snd
    exact hc.eventually (Ioi_mem_nhds (by norm_num))
  have hh : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ), 0 < x.2.2 := by
    have hc : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ x.2.2) (0, 2, 1) :=
      continuousAt_snd.comp continuousAt_snd
    exact hc.eventually (Ioi_mem_nhds (by norm_num))
  have hspectralAnalytic : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
    apply (analyticAt_fst.comp DFP.FirstLeg.factorsAnalytic).congr
    filter_upwards [] with x
    rfl
  have hgradientAnalytic : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ ↦ DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2)
      (0, 2, 1) := by
    apply ((analyticAt_fst.comp analyticAt_snd).comp
      DFP.FirstLeg.factorsAnalytic).congr
    filter_upwards [] with x
    rfl
  have hspectralBase : DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradientBase : DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y ↦ y.2.1) DFP.FirstLeg.factorsBase
  have hL : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1 := by
    have hc := (analyticAt_fst.comp hspectralAnalytic).continuousAt
    apply hc.eventually
    change Set.Ioi 0 ∈ 𝓝 (DFP.FirstLeg.spectralFactors 0 2 1).1
    rw [hspectralBase]
    exact Ioi_mem_nhds (by norm_num)
  have hH : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2 := by
    have hc := (analyticAt_snd.comp hspectralAnalytic).continuousAt
    apply hc.eventually
    change Set.Ioi 0 ∈ 𝓝 (DFP.FirstLeg.spectralFactors 0 2 1).2
    rw [hspectralBase]
    exact Ioi_mem_nhds (by norm_num)
  have hQ : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      0 < (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1 := by
    have hc := (analyticAt_fst.comp hgradientAnalytic).continuousAt
    apply hc.eventually
    change Set.Ioi 0 ∈ 𝓝 (DFP.FirstLeg.gradientFactors 0 2 1).1
    rw [hgradientBase]
    exact Ioi_mem_nhds (by norm_num)
  filter_upwards [hsmall, hp, hh, DFP.FirstLeg.frameOriented,
    DFP.SecondLeg.frameOriented, hL, hH, hQ,
    DFP.FirstLeg.frameDiagonalization, DFP.FirstLeg.gradientFactorization]
    with x hsmall hp hh hcoord1 hcoord2 hL hH hQ hdiag1 hgrad1
  intro hε
  exact observableMap_fixedScale_of_localData x.1 x.2.1 x.2.2 hε hsmall hp hh
    hcoord1 hcoord2 hL hH hQ hdiag1 hgrad1

end DFP.TwoLeg.Mixed
