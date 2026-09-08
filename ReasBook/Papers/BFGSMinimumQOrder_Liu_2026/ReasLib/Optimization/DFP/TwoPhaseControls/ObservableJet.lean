module

public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.FrameAngleJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.CenterJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.NormJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables.Continuity
public import ReasLib.Topology.MetricSpace.CompactUniformPositivity
public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Uniform
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables
import all ReasLib.Optimization.DFP.TwoPhaseControls.Observables.GraphJetSmoothness

public section

noncomputable section

open scoped EuclideanSpace Matrix

namespace DFP.TwoLeg.ObservableJet

/-- The thirteen real coordinates of the complete two-leg observable, ordered as the
amplitude, frame angle, center coordinates, endpoint angles, step norms, and gradient norms. -/
def coordinates (observable : CompleteTwoLegObservables) : Fin 13 → ℝ :=
  ![observable.amplitudeRatio, observable.frameAngleIncrement,
    observable.halfCenterDisplacement 0, observable.halfCenterDisplacement 1,
    observable.fullCenterDisplacement 0, observable.fullCenterDisplacement 1,
    observable.firstEndpointAngleIncrement.toReal,
    observable.secondEndpointAngleIncrement.toReal,
    observable.firstStepNorm, observable.secondStepNorm,
    observable.initialGradientNorm, observable.intermediateGradientNorm,
    observable.finalGradientNorm]

/-- Evaluation of the ordered vector of thirteen complete two-leg observables. -/
theorem coordinates_apply (observable : CompleteTwoLegObservables) (i : Fin 13) :
    coordinates observable i =
      ![observable.amplitudeRatio, observable.frameAngleIncrement,
        observable.halfCenterDisplacement 0, observable.halfCenterDisplacement 1,
        observable.fullCenterDisplacement 0, observable.fullCenterDisplacement 1,
        observable.firstEndpointAngleIncrement.toReal,
        observable.secondEndpointAngleIncrement.toReal,
        observable.firstStepNorm, observable.secondStepNorm,
        observable.initialGradientNorm, observable.intermediateGradientNorm,
        observable.finalGradientNorm] i := by
  rfl

/-- The five scalar margins selecting the two oriented spectral coordinates, the
relative-frame signed-angle chart, and the two endpoint-angle branches of a two-leg state. -/
def branchFactors (x : ℝ × ℝ × ℝ) : Fin 5 → ℝ :=
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let F₁ := DFP.FirstLeg.frame ε p h
  let F₂ := DFP.SecondLeg.frame ε p h
  let observable := DFP.TwoLeg.observableMap x
  ![(DFP.FirstLeg.coordinates ε p h).1,
    (DFP.SecondLeg.coordinates ε p h).1,
    (F₁ * F₂) 0 0,
    Real.pi / 2 - |observable.firstEndpointAngleIncrement.toReal|,
    Real.pi / 2 - |observable.secondEndpointAngleIncrement.toReal|]

/-- Evaluation of the five branch-selection margins of a two-leg state. -/
theorem branchFactors_apply (x : ℝ × ℝ × ℝ) (i : Fin 5) :
    branchFactors x i =
      (let ε := x.1
       let p := x.2.1
       let h := x.2.2
       let F₁ := DFP.FirstLeg.frame ε p h
       let F₂ := DFP.SecondLeg.frame ε p h
       let observable := DFP.TwoLeg.observableMap x
       ![(DFP.FirstLeg.coordinates ε p h).1,
         (DFP.SecondLeg.coordinates ε p h).1,
         (F₁ * F₂) 0 0,
         Real.pi / 2 - |observable.firstEndpointAngleIncrement.toReal|,
         Real.pi / 2 - |observable.secondEndpointAngleIncrement.toReal|] i) := by
  rfl

/-- The canonical oriented spectral coordinates and signed-angle representatives of a
two-leg state lie in their coherent positive local branches. -/
def BranchConditions (x : ℝ × ℝ × ℝ) : Prop :=
  let ε := x.1
  let p := x.2.1
  let h := x.2.2
  let F₁ := DFP.FirstLeg.frame ε p h
  let F₂ := DFP.SecondLeg.frame ε p h
  let observable := DFP.TwoLeg.observableMap x
  0 < (DFP.FirstLeg.coordinates ε p h).1 ∧
    0 < (DFP.SecondLeg.coordinates ε p h).1 ∧
    F₁ * F₂ ∈ EuclideanPlane.SignedAngle.chart ∧
    observable.firstEndpointAngleIncrement.toReal ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) ∧
    observable.secondEndpointAngleIncrement.toReal ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)

/-- Coherent canonical branch conditions are equivalent to positivity of all five
branch-selection margins. -/
theorem branchConditions_iff (x : ℝ × ℝ × ℝ) :
    BranchConditions x ↔ ∀ i : Fin 5, 0 < branchFactors x i := by
  constructor
  · rintro ⟨hfirst, hsecond, hchart, hfirstAngle, hsecondAngle⟩ i
    fin_cases i
    · simpa [branchFactors] using hfirst
    · simpa [branchFactors] using hsecond
    · simpa [branchFactors] using (EuclideanPlane.SignedAngle.mem_chart _).1 hchart
    · have habs : |(DFP.TwoLeg.observableMap x).firstEndpointAngleIncrement.toReal| <
          Real.pi / 2 := abs_lt.mpr ⟨hfirstAngle.1, hfirstAngle.2⟩
      simpa [branchFactors] using sub_pos.mpr habs
    · have habs : |(DFP.TwoLeg.observableMap x).secondEndpointAngleIncrement.toReal| <
          Real.pi / 2 := abs_lt.mpr ⟨hsecondAngle.1, hsecondAngle.2⟩
      simpa [branchFactors] using sub_pos.mpr habs
  · intro hpos
    have hfirst : 0 < (DFP.FirstLeg.coordinates x.1 x.2.1 x.2.2).1 := by
      simpa [branchFactors] using hpos (0 : Fin 5)
    have hsecond : 0 < (DFP.SecondLeg.coordinates x.1 x.2.1 x.2.2).1 := by
      simpa [branchFactors] using hpos (1 : Fin 5)
    have hchart : DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *
        DFP.SecondLeg.frame x.1 x.2.1 x.2.2 ∈ EuclideanPlane.SignedAngle.chart := by
      apply (EuclideanPlane.SignedAngle.mem_chart _).2
      simpa [branchFactors] using hpos (2 : Fin 5)
    have hfirstAngleAbs :
        |(DFP.TwoLeg.observableMap x).firstEndpointAngleIncrement.toReal| <
          Real.pi / 2 := by
      apply sub_pos.mp
      simpa [branchFactors] using hpos (3 : Fin 5)
    have hsecondAngleAbs :
        |(DFP.TwoLeg.observableMap x).secondEndpointAngleIncrement.toReal| <
          Real.pi / 2 := by
      apply sub_pos.mp
      simpa [branchFactors] using hpos (4 : Fin 5)
    exact ⟨hfirst, hsecond, hchart, abs_lt.mp hfirstAngleAbs,
      abs_lt.mp hsecondAngleAbs⟩

/-- Positivity of every branch-selection margin supplies all canonical branch conditions. -/
theorem branchConditions_of_branchFactors_pos (x : ℝ × ℝ × ℝ)
    (hpos : ∀ i : Fin 5, 0 < branchFactors x i) :
    BranchConditions x := by
  exact (branchConditions_iff x).2 hpos

/-- Each branch-selection margin is continuous at the common zero-scale base state. -/
theorem branchFactors_continuousAt (i : Fin 5) :
    ContinuousAt (fun x : ℝ × ℝ × ℝ ↦ branchFactors x i) (0, 2, 1) := by
  have hcoord1 := DFP.FirstLeg.coordinates_continuousAt
  have hcoord2 := DFP.SecondLeg.coordinates_continuousAt
  have hprod : ContinuousAt (fun x : ℝ × ℝ × ℝ ↦
      (DFP.FirstLeg.frame x.1 x.2.1 x.2.2 *
        DFP.SecondLeg.frame x.1 x.2.1 x.2.2) 0 0) (0, 2, 1) := by
    have h := ((DFP.FirstLeg.frameEntry_continuousAt 0 0).mul
      (DFP.SecondLeg.frameEntry_continuousAt 0 0)).add
      ((DFP.FirstLeg.frameEntry_continuousAt 0 1).mul
        (DFP.SecondLeg.frameEntry_continuousAt 1 0))
    apply h.congr
    filter_upwards [] with x
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hangle1 := DFP.TwoLeg.firstEndpointAngleMargin_continuousAt
  have hangle2 := DFP.TwoLeg.secondEndpointAngleMargin_continuousAt
  fin_cases i
  · have h := continuousAt_fst.comp hcoord1
    apply h.congr
    exact Filter.Eventually.of_forall (fun x => rfl)
  · have h := continuousAt_fst.comp hcoord2
    apply h.congr
    exact Filter.Eventually.of_forall (fun x => rfl)
  · exact hprod
  · exact hangle1
  · exact hangle2

/-- Every canonical branch-selection margin is strictly positive at the common
zero-scale base state. -/
theorem branchFactors_base (i : Fin 5) :
    0 < branchFactors (0, 2, 1) i := by
  fin_cases i
  all_goals
    norm_num [branchFactors, DFP.TwoLeg.observableMap,
      DFP.FirstLeg.coordinates, DFP.FirstLeg.frame, DFP.FirstLeg.outputMetric,
      DFP.FirstLeg.outputGradient, DFP.FirstLeg.spectralFactors,
      DFP.FirstLeg.gradientFactors, DFP.SecondLeg.coordinates,
      DFP.SecondLeg.frame, DFP.SecondLeg.outputMetric, DFP.SecondLeg.outputGradient,
      DFP.SecondLeg.spectralFactors, DFP.SecondLeg.gradientFactors,
      EuclideanPlane.frame, EuclideanPlane.perp_apply, RealSymmetric2.lowVector,
      RealSymmetric2.lowRaw, RealSymmetric2.low, RealSymmetric2.high,
      RealSymmetric2.gap, RealSymmetric2.lowDenom, Matrix.mulVec, dotProduct,
      Matrix.mul_apply, Fin.sum_univ_two, EuclideanPlane.frame_mulVec]
  · exact Real.pi_pos
  · have hvector :
        WithLp.toLp 2 ((EuclideanSpace.equiv (Fin 2) ℝ)
          (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2))) =
            (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) := by
      rfl
    rw [hvector, EuclideanPlane.orientation.oangle_self]
    simp only [Real.Angle.toReal_zero, abs_zero, Nat.ofNat_pos,
      div_pos_iff_of_pos_right, gt_iff_lt]
    exact Real.pi_pos

/-- The eighteen quantitative common-domain factors consist of the thirteen
factored-state margins followed by the five canonical branch-selection margins. -/
def domainFactors (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) : Fin 18 → ℝ :=
  Fin.append (DFP.TwoLeg.StateJet.domainFactors θ ε)
    (branchFactors (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε))

/-- The first thirteen common-domain factors are the factored-state margins. -/
theorem domainFactors_state
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) (i : Fin 13) :
      domainFactors θ ε (Fin.castAdd 5 i) =
      DFP.TwoLeg.StateJet.domainFactors θ ε i := by
  unfold domainFactors
  rw [Fin.append_left]

/-- The final five common-domain factors are the canonical branch-selection margins. -/
theorem domainFactors_branch
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) (i : Fin 5) :
    domainFactors θ ε (Fin.natAdd 13 i) =
      branchFactors
        (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε) i := by
  unfold domainFactors
  rw [Fin.append_right]

/-- Evaluation of the ordered vector of eighteen factored-state and branch margins. -/
theorem domainFactors_apply
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) (i : Fin 18) :
    domainFactors θ ε i =
      (let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
       let p := x.2.1
       let h := x.2.2
       let B₁ := 1 + 2 * ε ^ 3 + ε ^ 4
       let C₁ := (1 + ε ^ 3) ^ 2 + p * ε ^ 6 * (1 + ε) ^ 2
       let metric₁ := DFP.FirstLeg.outputMetric ε p h
       let spectral₁ := DFP.FirstLeg.spectralFactors ε p h
       let gradient₁ := DFP.FirstLeg.gradientFactors ε p h
       let L := spectral₁.1
       let H := spectral₁.2
       let Q := gradient₁.1
       let U := gradient₁.2
       let w₁ := ε * L * Q - 2 * H * U
       let w₂ := H * U - 2 * ε ^ 3 * L * Q
       let beta := ε ^ 3 * L * Q * w₁ + H * U * w₂
       let gamma := ε ^ 6 * L * w₁ ^ 2 + H * w₂ ^ 2
       let metric₂ := DFP.SecondLeg.outputMetric ε p h
       let spectral₂ := DFP.SecondLeg.spectralFactors ε p h
       let gradient₂ := DFP.SecondLeg.gradientFactors ε p h
       let F₁ := DFP.FirstLeg.frame ε p h
       let F₂ := DFP.SecondLeg.frame ε p h
       let observable := DFP.TwoLeg.observableMap x
       ![B₁, C₁,
         RealSymmetric2.high (metric₁ 0 0) (metric₁ 0 1) (metric₁ 1 1),
         RealSymmetric2.lowDenom (metric₁ 0 0) (metric₁ 0 1) (metric₁ 1 1),
         spectral₁.2 * gradient₁.2, spectral₁.1 * gradient₁.1 ^ 2,
         beta, gamma,
         RealSymmetric2.high (metric₂ 0 0) (metric₂ 0 1) (metric₂ 1 1),
         RealSymmetric2.lowDenom (metric₂ 0 0) (metric₂ 0 1) (metric₂ 1 1),
         spectral₂.2 * gradient₂.2, spectral₂.1 * gradient₂.1 ^ 2,
         (DFP.SecondLeg.canonicalFactors ε p h).1,
         (DFP.FirstLeg.coordinates ε p h).1,
         (DFP.SecondLeg.coordinates ε p h).1,
         (F₁ * F₂) 0 0,
         Real.pi / 2 - |observable.firstEndpointAngleIncrement.toReal|,
         Real.pi / 2 - |observable.secondEndpointAngleIncrement.toReal|] i) := by
  refine Fin.addCases (m := 13) (n := 5) (fun j => ?_) (fun j => ?_) i
  · rw [domainFactors_state]
    have h := DFP.TwoLeg.StateJet.domainFactors_apply θ ε j
    simp only [DFP.TwoLeg.graphJetPath_apply, DFP.TwoLeg.radiusFactor,
      DFP.SecondLeg.canonicalFactors] at h ⊢
    fin_cases j
    all_goals simpa using h
  · rw [domainFactors_branch]
    have h := branchFactors_apply
      (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε) j
    simp only [DFP.TwoLeg.graphJetPath_apply] at h ⊢
    fin_cases j
    all_goals simpa using h

/-- The complete observable coordinate family along the graph path is jointly
`C^9` at every point of the zero-scale coefficient fiber. -/
theorem contDiffAt_coordinatesAlongGraphJetPath
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    ContDiffAt ℝ 9
      (Function.uncurry
        (fun η : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
          coordinates (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.graphJetPath η.1.1 η.1.2 η.2.1 η.2.2 ε))))
      (θ, 0) := by
  have hfamily :
      (fun η : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
        coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.graphJetPath η.1.1 η.1.2 η.2.1 η.2.2 ε))) =
        DFP.TwoLeg.graphObservableFamily := by
    funext η ε
    rfl
  have hsmooth := DFP.TwoLeg.graphObservableFamily_contDiffAt 9 θ
  rw [hfamily]
  exact hsmooth

/-- On a bounded closed coefficient ball, the five branch-selection margins have
one positive lower bound throughout one common zero-scale neighborhood. -/
theorem branchFactorsCommonDomain (B : ℝ) (hB : 0 ≤ B) :
    ∃ m > 0, ∃ δ > 0,
      ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
        ∀ i : Fin 5, ∀ ε : ℝ, |ε| < δ →
          m ≤ branchFactors
            (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε) i := by
  let K : Set ((ℝ × ℝ) × (ℝ × ℝ)) := Metric.closedBall 0 B
  letI : CompactSpace K := by
    apply isCompact_iff_compactSpace.mp
    dsimp only [K]
    exact isCompact_closedBall _ _
  have hneK : Nonempty K := by
    have hzero : (0 : (ℝ × ℝ) × (ℝ × ℝ)) ∈ Metric.closedBall 0 B := by
      rw [Metric.mem_closedBall]
      simpa only [dist_self] using hB
    exact ⟨⟨0, by simpa only [K] using hzero⟩⟩
  have hcontinuous : ∀ θ : K, ∀ i : Fin 5,
      ContinuousAt
        (fun p : ℝ × K ↦
          branchFactors (DFP.TwoLeg.graphJetPath
            (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
            (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
            (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
            (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 p.1) i)
        (0, θ) := by
    intro θ i
    have hpath : ContinuousAt
        (fun p : ℝ × K ↦ DFP.TwoLeg.graphJetPath
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
          (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 p.1)
        (0, θ) := by
      dsimp only [DFP.TwoLeg.graphJetPath]
      fun_prop
    have hbase : DFP.TwoLeg.graphJetPath
        (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
        (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
        (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
        (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 0 = (0, 2, 1) := by
      simp [DFP.TwoLeg.graphJetPath]
    have houter := branchFactors_continuousAt i
    rw [← hbase] at houter
    have hcomp := ContinuousAt.comp
      (f := fun p : ℝ × K ↦ DFP.TwoLeg.graphJetPath
        (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
        (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
        (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
        (p.2 : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 p.1)
      (g := fun x : ℝ × ℝ × ℝ ↦ branchFactors x i)
      (x := (0, θ)) houter hpath
    simpa only [Function.comp_def] using hcomp
  have hpositive : ∀ θ : K, ∀ i : Fin 5,
      0 < branchFactors
        (DFP.TwoLeg.graphJetPath
          (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
          (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
          (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
          (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 0) i := by
    intro θ i
    simpa [DFP.TwoLeg.graphJetPath] using branchFactors_base i
  obtain ⟨m, hm, δ, hδ, hbound⟩ :=
    CompactUniformPositivity.exists_uniform_lower_bound_finite_of_continuousAt
      (fun ε (θ : K) (i : Fin 5) ↦
        branchFactors
          (DFP.TwoLeg.graphJetPath
            (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.1
            (θ : ((ℝ × ℝ) × (ℝ × ℝ))).1.2
            (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.1
            (θ : ((ℝ × ℝ) × (ℝ × ℝ))).2.2 ε) i)
      hcontinuous hneK (inferInstance : Nonempty (Fin 5)) hpositive
  refine ⟨m, hm, δ, hδ, ?_⟩
  intro θ hθ i ε hε
  let θK : K := ⟨θ, by simpa only [K] using hθ⟩
  exact hbound θK i ε hε

/-- The order-nine derivative-constructed jets of all thirteen observable coordinates
are uniform on every bounded closed ball of graph coefficients. -/
theorem uniformOn (B : ℝ) (hB : 0 ≤ B) :
    let f := fun θ : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
      coordinates (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε))
    FiniteTaylorJet.IsUniformOn f
      (fun θ ↦ FiniteTaylorJet.ofFunction ℝ 9 (f θ) 0) 0
      (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B) := by
  have _hB := hB
  have hfamily :
      (fun θ : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
        coordinates (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε))) =
        DFP.TwoLeg.graphObservableFamily := by
    funext θ ε
    rfl
  have huniform := DFP.TwoLeg.graphObservableFamily_uniformOn B
  rw [hfamily]
  exact huniform

/-- On every bounded graph-coefficient set, one neighborhood simultaneously preserves
all factored-state and canonical branch margins and controls the common order-nine
remainder of the thirteen complete observable coordinates. -/
theorem observableJetsCommonDomain (B : ℝ) (hB : 0 ≤ B) :
    let f := fun θ : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
      coordinates (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε))
    let J := fun θ ↦ FiniteTaylorJet.ofFunction ℝ 9 (f θ) 0
    ∃ m > 0, ∀ C > 0, ∃ δ ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
        ∀ ε : ℝ, |ε| < δ →
          (∀ i : Fin 18, m ≤ domainFactors θ ε i) ∧
            ‖(J θ).remainder (f θ) 0 ε‖ ≤ C * |ε| ^ 9 := by
  let f := fun θ : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
    coordinates (DFP.TwoLeg.observableMap
      (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε))
  let J := fun θ ↦ FiniteTaylorJet.ofFunction ℝ 9 (f θ) 0
  have huniform : FiniteTaylorJet.IsUniformOn f J 0
      (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B) := by
    simpa only [f, J] using uniformOn B hB
  obtain ⟨_, _, mState, hmState, δState, hδState, hState⟩ :=
    DFP.TwoLeg.StateJet.stateJetsCommonDomain B hB
  obtain ⟨mBranch, hmBranch, δBranch, hδBranch, hBranch⟩ :=
    branchFactorsCommonDomain B hB
  let m := min mState mBranch
  have hm : 0 < m := by
    dsimp only [m]
    exact lt_min hmState hmBranch
  refine ⟨m, hm, ?_⟩
  intro C hC
  obtain ⟨δRemainder, hδRemainder, hRemainder⟩ :=
    FiniteTaylorJet.IsUniformRemainderOn.bound (huniform.remainder C hC)
  let δ := min δState (min δBranch (min δRemainder (1 / 8)))
  have hδPos : 0 < δ := by
    dsimp only [δ]
    have hEighth : (0 : ℝ) < 1 / 8 := by
      norm_num
    exact lt_min hδState.1
      (lt_min hδBranch (lt_min hδRemainder hEighth))
  have hδLt : δ < 1 / 4 := by
    have hδEighth : δ ≤ 1 / 8 := by
      dsimp only [δ]
      exact (min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _))
    linarith
  refine ⟨δ, ⟨hδPos, hδLt⟩, ?_⟩
  intro θ hθ ε hε
  have hεState : |ε| < δState :=
    hε.trans_le (min_le_left _ _)
  have hεBranch : |ε| < δBranch :=
    hε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεRemainder : ‖ε‖ < δRemainder := by
    rw [Real.norm_eq_abs]
    exact hε.trans_le ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hStatePoint := hState θ hθ ε hεState
  have hBranchPoint (i : Fin 5) :
      mBranch ≤ branchFactors
        (DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε) i :=
    hBranch θ hθ i ε hεBranch
  constructor
  · intro i
    refine Fin.addCases (m := 13) (n := 5) ?_ ?_ i
    · intro k
      rw [domainFactors_state]
      exact (min_le_left _ _).trans (hStatePoint.2 k)
    · intro k
      rw [domainFactors_branch]
      exact (min_le_right _ _).trans (hBranchPoint k)
  · have hTaylor := hRemainder θ hθ ε hεRemainder
    simpa only [f, J, Real.norm_eq_abs, Real.rpow_natCast] using hTaylor

end DFP.TwoLeg.ObservableJet
