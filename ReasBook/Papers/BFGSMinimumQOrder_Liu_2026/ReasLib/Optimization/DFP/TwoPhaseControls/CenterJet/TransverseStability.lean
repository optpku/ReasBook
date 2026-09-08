module

public import ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterCancellationBridge
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.CenterCancellationBridge

/-! # Transverse stability of the full-center observable -/

public section
noncomputable section
open Filter
open scoped EuclideanSpace Matrix Topology
namespace DFP.TwoLeg.CenterCancellation

/-- The first-leg metric off-diagonal entry after removing its exact factor ε². -/
private def firstFrameOffDiagonalResidual (x : ℝ × ℝ × ℝ) : ℝ :=
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let B := 1 + 2 * ε ^ 3 + ε ^ 4
  let C := (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2
  1 / B - h * p * ε ^ 3 * (1 + ε) * (1 + ε ^ 3) / C

/-- The first-frame transverse entry after removing its exact factor ε². -/
private def firstFrameTiltFactor (x : ℝ × ℝ × ℝ) : ℝ :=
  let H := DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2
  (-firstFrameOffDiagonalResidual x) * DFP.FirstLeg.frame x.1 x.2.1 x.2.2 0 0 /
    (H 1 1 - RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1))

/-- The common scalar coefficient of the first canceled center displacement. -/
private def firstCenterCoefficient (x : ℝ × ℝ × ℝ) : ℝ :=
  2 * (x.2.1 + 1) / (3 * (1 + 2 * x.1 ^ 3 + x.1 ^ 4))

/-- Smooth factor left after extracting ε³ from the canceled full-center low coordinate. -/
def fullCenterLowTransverseFactor (x : ℝ × ℝ × ℝ) : ℝ :=
  let ε := x.1
  let spectral := DFP.FirstLeg.spectralFactors ε x.2.1 x.2.2
  let gradient := DFP.FirstLeg.gradientFactors ε x.2.1 x.2.2
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let delta := L * Q ^ 2 + H * U ^ 2
  let beta := secondEnergyFactor ε x.2.1 x.2.2
  let C := DFP.FirstLeg.frame ε x.2.1 x.2.2 0 0
  let T := firstFrameTiltFactor x
  firstCenterCoefficient x - 2 * C * delta * H * U / (3 * beta) +
    2 * ε ^ 4 * T * delta * L * Q / (3 * beta)

/-- Smooth factor left after extracting ε⁴ from the canceled full-center high coordinate. -/
def fullCenterHighTransverseFactor (x : ℝ × ℝ × ℝ) : ℝ :=
  let ε := x.1
  let spectral := DFP.FirstLeg.spectralFactors ε x.2.1 x.2.2
  let gradient := DFP.FirstLeg.gradientFactors ε x.2.1 x.2.2
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let delta := L * Q ^ 2 + H * U ^ 2
  let beta := secondEnergyFactor ε x.2.1 x.2.2
  let C := DFP.FirstLeg.frame ε x.2.1 x.2.2 0 0
  let T := firstFrameTiltFactor x
  ε * (firstCenterCoefficient x -
    2 * delta * (T * H * U + C * L * Q) / (3 * beta))

/-- The normalized first-leg off-diagonal residual is analytic at the canceled base. -/
private theorem firstFrameOffDiagonalResidual_analyticAt :
    AnalyticAt ℝ firstFrameOffDiagonalResidual (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.1) (0, 2, 1) := analyticAt_fst
  have hp : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.2.1) (0, 2, 1) :=
    analyticAt_fst.comp analyticAt_snd
  have hh : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦ x.2.2) (0, 2, 1) :=
    analyticAt_snd.comp analyticAt_snd
  let B : ℝ × ℝ × ℝ → ℝ := fun x ↦ 1 + 2 * x.1 ^ 3 + x.1 ^ 4
  let C : ℝ × ℝ × ℝ → ℝ :=
    fun x ↦ (1 + x.1 ^ 3) ^ 2 + x.2.1 * x.1 ^ 6 * (1 + x.1) ^ 2
  have hB : AnalyticAt ℝ B (0, 2, 1) := by
    dsimp only [B]
    fun_prop
  have hC : AnalyticAt ℝ C (0, 2, 1) := by
    dsimp only [C]
    fun_prop
  have hBne : B (0, 2, 1) ≠ 0 := by norm_num [B]
  have hCne : C (0, 2, 1) ≠ 0 := by norm_num [C]
  have hone : AnalyticAt ℝ (fun _ : ℝ × ℝ × ℝ ↦ (1 : ℝ)) (0, 2, 1) :=
    analyticAt_const
  have hformula := (hone.div hB hBne).sub
    (((((hh.mul hp).mul (hε.pow 3)).mul (hone.add hε)).mul
      (hone.add (hε.pow 3))).div hC hCne)
  apply hformula.congr
  filter_upwards [] with x
  rfl

/-- The first-frame tilt with its ε² factor removed is analytic at the canceled base. -/
private theorem firstFrameTiltFactor_analyticAt :
    AnalyticAt ℝ firstFrameTiltFactor (0, 2, 1) := by
  let entries : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ := fun x ↦
    (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0,
      DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1,
      DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1)
  have hzero := DFP.FirstLeg.outputMetricEntry_analyticAt 0 0
  have hone := DFP.FirstLeg.outputMetricEntry_analyticAt 0 1
  have htwo := DFP.FirstLeg.outputMetricEntry_analyticAt 1 1
  have hentries : AnalyticAt ℝ entries (0, 2, 1) := hzero.prod (hone.prod htwo)
  have hentriesBase : entries (0, 2, 1) = ((0, 0, 1) : ℝ × ℝ × ℝ) := by
    norm_num [entries, DFP.FirstLeg.outputMetric]
  have hlowOuter := RealSymmetric2.analyticOnNhd_low
    ((0, 0, 1) : ℝ × ℝ × ℝ) RealSymmetric2.diag_mem_lowChart
  rw [← hentriesBase] at hlowOuter
  have hlowComposed := hlowOuter.comp hentries
  have hlow : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ ↦
      let H := DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2
      RealSymmetric2.low (H 0 0) (H 0 1) (H 1 1)) (0, 2, 1) := by
    apply hlowComposed.congr
    filter_upwards [] with x
    rfl
  have hgap := htwo.sub hlow
  have hgapNe : DFP.FirstLeg.outputMetric 0 2 1 1 1 -
      RealSymmetric2.low (DFP.FirstLeg.outputMetric 0 2 1 0 0)
        (DFP.FirstLeg.outputMetric 0 2 1 0 1)
        (DFP.FirstLeg.outputMetric 0 2 1 1 1) ≠ 0 := by
    norm_num [DFP.FirstLeg.outputMetric, RealSymmetric2.low, RealSymmetric2.gap]
  have hformula := (firstFrameOffDiagonalResidual_analyticAt.neg.mul
    (DFP.FirstLeg.frameEntry_analyticAt 0 0)).div hgap hgapNe
  apply hformula.congr
  filter_upwards [] with x
  simp only [firstFrameTiltFactor, Pi.neg_apply, Pi.mul_apply, Pi.div_apply,
    Pi.sub_apply]

/-- The low-coordinate transverse factor is C¹ at the canceled base state. -/
theorem fullCenterLowTransverseFactor_contDiffAt :
    ContDiffAt ℝ 1 fullCenterLowTransverseFactor (0, 2, 1) := by
  have hspectral :=
    (analyticAt_fst.comp DFP.FirstLeg.factorsAnalytic).contDiffAt (n := 1)
  have hgradient :=
    ((analyticAt_fst.comp analyticAt_snd).comp
      DFP.FirstLeg.factorsAnalytic).contDiffAt (n := 1)
  have hL := contDiffAt_fst.comp (0, 2, 1) hspectral
  have hH := contDiffAt_snd.comp (0, 2, 1) hspectral
  have hQ := contDiffAt_fst.comp (0, 2, 1) hgradient
  have hU := contDiffAt_snd.comp (0, 2, 1) hgradient
  have hbeta := secondEnergyFactor_contDiffAt 1
  have hC := (DFP.FirstLeg.frameEntry_analyticAt 0 0).contDiffAt (n := 1)
  have hT := firstFrameTiltFactor_analyticAt.contDiffAt (n := 1)
  unfold fullCenterLowTransverseFactor firstCenterCoefficient
  dsimp
  fun_prop (disch := norm_num [secondEnergyFactor_base])

/-- The high-coordinate transverse factor is C¹ at the canceled base state. -/
theorem fullCenterHighTransverseFactor_contDiffAt :
    ContDiffAt ℝ 1 fullCenterHighTransverseFactor (0, 2, 1) := by
  have hspectral :=
    (analyticAt_fst.comp DFP.FirstLeg.factorsAnalytic).contDiffAt (n := 1)
  have hgradient :=
    ((analyticAt_fst.comp analyticAt_snd).comp
      DFP.FirstLeg.factorsAnalytic).contDiffAt (n := 1)
  have hL := contDiffAt_fst.comp (0, 2, 1) hspectral
  have hH := contDiffAt_snd.comp (0, 2, 1) hspectral
  have hQ := contDiffAt_fst.comp (0, 2, 1) hgradient
  have hU := contDiffAt_snd.comp (0, 2, 1) hgradient
  have hbeta := secondEnergyFactor_contDiffAt 1
  have hC := (DFP.FirstLeg.frameEntry_analyticAt 0 0).contDiffAt (n := 1)
  have hT := firstFrameTiltFactor_analyticAt.contDiffAt (n := 1)
  unfold fullCenterHighTransverseFactor firstCenterCoefficient
  dsimp
  fun_prop (disch := norm_num [secondEnergyFactor_base])

/-- The first metric off-diagonal entry has the displayed exact scale factor. -/
private theorem firstOutputMetric_offDiagonal_eq (x : ℝ × ℝ × ℝ) :
    DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1 =
      x.1 ^ 2 * firstFrameOffDiagonalResidual x := by
  rcases x with ⟨ε, p, h⟩
  rfl

/-- Away from the low-eigenvector gap, the transverse frame entry has factor ε². -/
private theorem firstFrame_transverse_eq (x : ℝ × ℝ × ℝ)
    (hgap : DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1 -
      RealSymmetric2.low (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0)
        (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1)
        (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1) ≠ 0) :
    DFP.FirstLeg.frame x.1 x.2.1 x.2.2 1 0 =
      x.1 ^ 2 * firstFrameTiltFactor x := by
  unfold DFP.FirstLeg.frame
  simp only [EuclideanPlane.frame, Matrix.cons_val_zero, RealSymmetric2.lowVector,
    PiLp.smul_apply, RealSymmetric2.lowRaw, Matrix.cons_val_one, smul_eq_mul]
  rw [firstOutputMetric_offDiagonal_eq]
  rw [firstOutputMetric_offDiagonal_eq] at hgap
  unfold firstFrameTiltFactor DFP.FirstLeg.frame
  simp only [EuclideanPlane.frame, Matrix.cons_val_zero, RealSymmetric2.lowVector,
    PiLp.smul_apply, RealSymmetric2.lowRaw, smul_eq_mul]
  rw [firstOutputMetric_offDiagonal_eq]
  field_simp [hgap]

/-- Local orthogonality reconstructs the raw first output gradient. -/
private theorem reconstructFirstGradient_of_localData
    (x : ℝ × ℝ × ℝ)
    (hchart : DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0 <
      DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1)
    (hgrad : (DFP.FirstLeg.frame x.1 x.2.1 x.2.2).transpose *ᵥ
        DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 =
      ![(DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1,
        x.1 ^ 2 * (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2]) :
    DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *ᵥ
        ![(DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1,
          x.1 ^ 2 * (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2] =
      DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 := by
  let H := DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2
  let F := DFP.FirstLeg.frame x.1 x.2.1 x.2.2
  have hspecial : F ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
    exact RealSymmetric2.frame_mem_specialOrthogonalGroup
      (H 0 0) (H 0 1) (H 1 1) hchart
  have horthogonal : F ∈ Matrix.orthogonalGroup (Fin 2) ℝ :=
    (Matrix.mem_specialOrthogonalGroup_iff.mp hspecial).1
  have hcancel : F * F.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp horthogonal
  rw [← hgrad]
  change F *ᵥ F.transpose *ᵥ DFP.FirstLeg.outputGradient x.1 x.2.1 x.2.2 = _
  rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec]

/-- Locally, the canceled center coordinates expose transverse weights ε³ and ε⁴. -/
theorem canceledFullCenterDisplacement_eq_weightedFactors :
    ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      canceledFullCenterDisplacement x 0 =
          x.1 ^ 3 * fullCenterLowTransverseFactor x ∧
        canceledFullCenterDisplacement x 1 =
          x.1 ^ 4 * fullCenterHighTransverseFactor x := by
  have hleft := (DFP.FirstLeg.outputMetricEntry_analyticAt 0 0).continuousAt
  have hright := (DFP.FirstLeg.outputMetricEntry_analyticAt 1 1).continuousAt
  have hbaseChart :
      DFP.FirstLeg.outputMetric 0 2 1 0 0 <
        DFP.FirstLeg.outputMetric 0 2 1 1 1 := by
    norm_num [DFP.FirstLeg.outputMetric]
  have hchart : ∀ᶠ x in 𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ),
      DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0 <
        DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1 :=
    hleft.eventually_lt hright hbaseChart
  filter_upwards [hchart, DFP.FirstLeg.gradientFactorization] with x hxchart hxgrad
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let F := DFP.FirstLeg.frame ε p h
  let spectral := DFP.FirstLeg.spectralFactors ε p h
  let gradient := DFP.FirstLeg.gradientFactors ε p h
  let L := spectral.1
  let H := spectral.2
  let Q := gradient.1
  let U := gradient.2
  let delta := L * Q ^ 2 + H * U ^ 2
  let beta := secondEnergyFactor ε p h
  let C := F 0 0
  let T := firstFrameTiltFactor x
  have hgap : DFP.FirstLeg.outputMetric ε p h 1 1 -
      RealSymmetric2.low (DFP.FirstLeg.outputMetric ε p h 0 0)
        (DFP.FirstLeg.outputMetric ε p h 0 1)
        (DFP.FirstLeg.outputMetric ε p h 1 1) ≠ 0 := by
    apply ne_of_gt
    unfold RealSymmetric2.low
    rw [RealSymmetric2.gap]
    have hsqrt := Real.sqrt_nonneg
      ((DFP.FirstLeg.outputMetric ε p h 1 1 -
          DFP.FirstLeg.outputMetric ε p h 0 0) ^ 2 +
        4 * DFP.FirstLeg.outputMetric ε p h 0 1 ^ 2)
    have hxchart' : DFP.FirstLeg.outputMetric ε p h 0 0 <
        DFP.FirstLeg.outputMetric ε p h 1 1 := by
      simpa only [ε, p, h] using hxchart
    linarith
  have htilt : F 1 0 = ε ^ 2 * T := by
    simpa only [F, ε, p, h, T] using firstFrame_transverse_eq x hgap
  have hF01 : F 0 1 = -F 1 0 := by
    simp [F, DFP.FirstLeg.frame, EuclideanPlane.frame,
      EuclideanPlane.perp_apply]
  have hF11 : F 1 1 = F 0 0 := by
    simp [F, DFP.FirstLeg.frame, EuclideanPlane.frame,
      EuclideanPlane.perp_apply]
  have hgradOne :
      F.transpose *ᵥ DFP.FirstLeg.outputGradient ε p h =
        ![Q, ε ^ 2 * U] := by
    simpa [F, ε, p, h, Q, U, gradient] using hxgrad 1
  have hreconstruct :
      F *ᵥ ![Q, ε ^ 2 * U] = DFP.FirstLeg.outputGradient ε p h := by
    simpa only [F, ε, p, h, Q, U, gradient] using
      reconstructFirstGradient_of_localData x hxchart hgradOne
  have hraw0 : C * Q - ε ^ 4 * T * U =
      1 - 2 * (p + 1) * ε ^ 3 * (1 + ε) /
        (3 * (1 + 2 * ε ^ 3 + ε ^ 4)) := by
    have hcoord := congrArg (fun v : Fin 2 → ℝ ↦ v 0) hreconstruct
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hcoord
    rw [hF01, htilt] at hcoord
    simp only [DFP.FirstLeg.outputGradient] at hcoord
    norm_num at hcoord
    convert hcoord using 1
    ring
  have hz0 :
      secondDisplacement ε p h 0 - DFP.SecondLeg.outputGradient ε p h 0 =
        -Q - 2 * ε ^ 3 * delta * H * U / (3 * beta) := by
    simp [secondDisplacement, DFP.SecondLeg.outputGradient, secondEnergyFactor,
      Q, U, L, H, delta, beta, spectral, gradient]
    ring
  have hz1 :
      secondDisplacement ε p h 1 - DFP.SecondLeg.outputGradient ε p h 1 =
        -ε ^ 2 * U - 2 * ε ^ 5 * delta * L * Q / (3 * beta) := by
    simp [secondDisplacement, DFP.SecondLeg.outputGradient, secondEnergyFactor,
      Q, U, L, H, delta, beta, spectral, gradient]
    ring
  have hcanceled0 : canceledFullCenterDisplacement x 0 =
      firstDisplacement ε p 0 +
        F 0 0 * (secondDisplacement ε p h 0 -
          DFP.SecondLeg.outputGradient ε p h 0) +
        F 0 1 * (secondDisplacement ε p h 1 -
          DFP.SecondLeg.outputGradient ε p h 1) + 1 := by
    unfold canceledFullCenterDisplacement
    dsimp
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  have hcanceled1 : canceledFullCenterDisplacement x 1 =
      firstDisplacement ε p 1 +
        F 1 0 * (secondDisplacement ε p h 0 -
          DFP.SecondLeg.outputGradient ε p h 0) +
        F 1 1 * (secondDisplacement ε p h 1 -
          DFP.SecondLeg.outputGradient ε p h 1) + p * ε ^ 2 := by
    unfold canceledFullCenterDisplacement
    dsimp
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  constructor
  · rw [hcanceled0, hz0, hz1, hF01, htilt]
    unfold firstDisplacement
    dsimp
    unfold fullCenterLowTransverseFactor firstCenterCoefficient
    dsimp only [ε, p, h, F, spectral, gradient, L, H, Q, U, delta, beta, C, T]
    linear_combination -hraw0
  · by_cases hε : ε = 0
    · rw [hcanceled1, hz0, hz1, htilt]
      dsimp only [firstDisplacement]
      norm_num [ε, hε]
    · have hraw1 : T * Q + C * U =
          p - 2 * (p + 1) * (1 + ε ^ 3) /
            (3 * (1 + 2 * ε ^ 3 + ε ^ 4)) := by
        have hcoord := congrArg (fun v : Fin 2 → ℝ ↦ v 1) hreconstruct
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at hcoord
        rw [htilt, hF11] at hcoord
        simp only [DFP.FirstLeg.outputGradient] at hcoord
        norm_num at hcoord
        have hεsq : 0 < ε ^ 2 := sq_pos_of_ne_zero hε
        have hcoord' := hcoord
        nlinarith
      rw [hcanceled1, hz0, hz1, htilt, hF11]
      unfold firstDisplacement
      dsimp
      unfold fullCenterHighTransverseFactor firstCenterCoefficient
      dsimp only [ε, p, h, F, spectral, gradient, L, H, Q, U, delta, beta, C, T]
      linear_combination -ε ^ 2 * hraw1

/-- A C¹ scalar factor preserves fifth-order closeness to the slow-graph path. -/
private theorem smoothFactorStabilityUnderGraphJets
    (G : ℝ × ℝ × ℝ → ℝ)
    (hG : ContDiffAt ℝ 1 G ((0, 2, 1) : ℝ × ℝ × ℝ))
    (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦
      h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦ G (ε, p ε, h ε) - G (slowGraphJetPath ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
  let p0 : ℝ → ℝ :=
    fun ε ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h0 : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  let x : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p ε, h ε)
  let x0 : ℝ → ℝ × ℝ × ℝ := fun ε ↦ (ε, p0 ε, h0 ε)
  have hpDiff :
      (fun ε ↦ p ε - p0 ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [p0] using hp
  have hhDiff :
      (fun ε ↦ h ε - h0 ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [h0] using hh
  have hpowFiveTendsto :
      Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by fun_prop
    convert hc.tendsto using 1
    norm_num
  have hpTendsto : Tendsto p (𝓝 0) (𝓝 2) := by
    have hp0Tendsto : Tendsto p0 (𝓝 0) (𝓝 2) := by
      have hc : ContinuousAt p0 0 := by
        dsimp only [p0]
        fun_prop
      convert hc.tendsto using 1
      norm_num [p0]
    simpa only [sub_add_cancel, zero_add] using
      (hpDiff.trans_tendsto hpowFiveTendsto).add hp0Tendsto
  have hhTendsto : Tendsto h (𝓝 0) (𝓝 1) := by
    have hh0Tendsto : Tendsto h0 (𝓝 0) (𝓝 1) := by
      have hc : ContinuousAt h0 0 := by
        dsimp only [h0]
        fun_prop
      convert hc.tendsto using 1
      norm_num [h0]
    simpa only [sub_add_cancel, zero_add] using
      (hhDiff.trans_tendsto hpowFiveTendsto).add hh0Tendsto
  have hxTendsto :
      Tendsto x (𝓝 0) (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [x, id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hpTendsto.prodMk hhTendsto)
  have hx0Tendsto :
      Tendsto x0 (𝓝 0) (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    have hc : ContinuousAt x0 0 := by
      dsimp only [x0, p0, h0]
      fun_prop
    convert hc.tendsto using 1
    norm_num [x0, p0, h0]
  have hpathDiff :
      (fun ε ↦ x ε - x0 ε) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5) := by
    have hzero : (fun _ : ℝ ↦ (0 : ℝ)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) :=
      Asymptotics.isBigO_zero _ _
    simpa [x, x0] using hzero.prod_left (hpDiff.prod_left hhDiff)
  have houter := hG.hasStrictFDerivAt one_ne_zero |>.isBigO_sub
  have hpairs :
      Tendsto (fun ε ↦ (x ε, x0 ε)) (𝓝 0)
        (𝓝 (((0, 2, 1), (0, 2, 1)) :
          (ℝ × ℝ × ℝ) × (ℝ × ℝ × ℝ))) := by
    simpa only [nhds_prod_eq] using hxTendsto.prodMk hx0Tendsto
  have hcomposed := houter.comp_tendsto hpairs
  have hcomposed' :
      (fun ε ↦ G (x ε) - G (x0 ε)) =O[𝓝 0]
        (fun ε ↦ x ε - x0 ε) := by
    simpa only [Function.comp_def] using hcomposed
  have hstability := hcomposed'.trans hpathDiff
  simpa only [x, x0, p0, h0, slowGraphJetPath_apply] using hstability

/-- Fifth-order graph errors change the canceled low center only at order eight
and the canceled high center only at order nine. -/
theorem canceledFullCenterDisplacement_stabilityUnderGraphJets
    (p h : ℝ → ℝ)
    (hp : (fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦
      h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦ canceledFullCenterDisplacement (ε, p ε, h ε) 0 -
      canceledFullCenterDisplacement (slowGraphJetPath ε) 0) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 8) ∧
    (fun ε : ℝ ↦ canceledFullCenterDisplacement (ε, p ε, h ε) 1 -
      canceledFullCenterDisplacement (slowGraphJetPath ε) 1) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 9) := by
  let p0 : ℝ → ℝ :=
    fun ε ↦ 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4
  let h0 : ℝ → ℝ := fun ε ↦ 1 + 8 * ε ^ 3
  have hpow : Tendsto (fun ε : ℝ ↦ ε ^ 5) (𝓝 0) (𝓝 0) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ ε ^ 5) 0 := by fun_prop
    convert hc.tendsto using 1
    norm_num
  have hp0 : Tendsto p0 (𝓝 0) (𝓝 2) := by
    have hc : ContinuousAt p0 0 := by
      dsimp only [p0]
      fun_prop
    convert hc.tendsto using 1
    norm_num [p0]
  have hh0 : Tendsto h0 (𝓝 0) (𝓝 1) := by
    have hc : ContinuousAt h0 0 := by
      dsimp only [h0]
      fun_prop
    convert hc.tendsto using 1
    norm_num [h0]
  have hp' : Tendsto p (𝓝 0) (𝓝 2) := by
    simpa only [p0, sub_add_cancel, zero_add] using
      (hp.trans_tendsto hpow).add hp0
  have hh' : Tendsto h (𝓝 0) (𝓝 1) := by
    simpa only [h0, sub_add_cancel, zero_add] using
      (hh.trans_tendsto hpow).add hh0
  have hpath :
      Tendsto (fun ε : ℝ ↦ (ε, p ε, h ε)) (𝓝 0)
        (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    simpa only [id_eq, nhds_prod_eq] using
      tendsto_id.prodMk (hp'.prodMk hh')
  have hslow :
      Tendsto slowGraphJetPath (𝓝 0)
        (𝓝 ((0, 2, 1) : ℝ × ℝ × ℝ)) := by
    rw [show slowGraphJetPath =
      (fun ε : ℝ ↦
        (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
          1 + 8 * ε ^ 3)) by
      funext ε
      exact slowGraphJetPath_apply ε]
    have hc : ContinuousAt
        (fun ε : ℝ ↦
          (ε, 2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4,
            1 + 8 * ε ^ 3)) 0 := by
      fun_prop
    convert hc.tendsto using 1
    norm_num
  have hfactorActual :=
    hpath.eventually canceledFullCenterDisplacement_eq_weightedFactors
  have hfactorSlow :=
    hslow.eventually canceledFullCenterDisplacement_eq_weightedFactors
  have hlow := smoothFactorStabilityUnderGraphJets
    fullCenterLowTransverseFactor fullCenterLowTransverseFactor_contDiffAt
      p h hp hh
  have hhigh := smoothFactorStabilityUnderGraphJets
    fullCenterHighTransverseFactor fullCenterHighTransverseFactor_contDiffAt
      p h hp hh
  constructor
  · have hproduct :=
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0)).mul hlow
    apply hproduct.congr'
    · filter_upwards [hfactorActual, hfactorSlow] with ε hactual hslowEq
      rw [hactual.1, hslowEq.1]
      simp only [slowGraphJetPath_apply]
      ring
    · filter_upwards [] with ε
      rw [← pow_add]
  · have hproduct :=
      (Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 4) (𝓝 0)).mul hhigh
    apply hproduct.congr'
    · filter_upwards [hfactorActual, hfactorSlow] with ε hactual hslowEq
      rw [hactual.2, hslowEq.2]
      simp only [slowGraphJetPath_apply]
      ring
    · filter_upwards [] with ε
      rw [← pow_add]

end DFP.TwoLeg.CenterCancellation
