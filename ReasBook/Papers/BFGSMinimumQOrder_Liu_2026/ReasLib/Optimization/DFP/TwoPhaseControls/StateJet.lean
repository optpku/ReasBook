module

public import ReasLib.Optimization.DFP.TwoPhaseControls.TransverseJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.StateJetAssembly
public import ReasLib.Analysis.Asymptotics.UniformRemainder
public import ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg.Analyticity
public import ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg.Analyticity
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.UniformZeroJet
public import ReasLib.Topology.MetricSpace.CompactUniformPositivity.Pointwise
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2
import all ReasLib.Analysis.Asymptotics.UniformRemainder
import all ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg

public section

noncomputable section

open scoped Matrix

namespace DFP.TwoLeg.StateJet

/-- The joint residual of the normalized-radius jet and the two transverse
graph-invariance jets through degree four. -/
def remainder (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) : ℝ × ℝ × ℝ :=
  let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
  let y := DFP.TwoLeg.stateMap x
  let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
  (DFP.TwoLeg.radiusFactor x.1 x.2.1 x.2.2 -
      (1 + ((6 * θ.1.2 + 5 * θ.1.1 - 300) / 18) * ε ^ 3 +
        ((6 * θ.2.2 + 5 * θ.2.1 + 54) / 18) * ε ^ 4),
    y.2.1 - nextGraph.2.1 -
      (((6 * θ.1.2 - 10 * θ.1.1 + 348) / 9) * ε ^ 3 +
        ((6 * θ.2.2 - 10 * θ.2.1 - 18) / 9) * ε ^ 4),
    y.2.2 - nextGraph.2.2 - ((8 - θ.1.2) * ε ^ 3 - θ.2.2 * ε ^ 4))

/-- Evaluation of the joint state-jet residual in its three coordinates. -/
theorem remainder_apply (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) :
    remainder θ ε =
      let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
      let y := DFP.TwoLeg.stateMap x
      let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
      (DFP.TwoLeg.radiusFactor x.1 x.2.1 x.2.2 -
          (1 + ((6 * θ.1.2 + 5 * θ.1.1 - 300) / 18) * ε ^ 3 +
            ((6 * θ.2.2 + 5 * θ.2.1 + 54) / 18) * ε ^ 4),
        y.2.1 - nextGraph.2.1 -
          (((6 * θ.1.2 - 10 * θ.1.1 + 348) / 9) * ε ^ 3 +
            ((6 * θ.2.2 - 10 * θ.2.1 - 18) / 9) * ε ^ 4),
        y.2.2 - nextGraph.2.2 -
          ((8 - θ.1.2) * ε ^ 3 - θ.2.2 * ε ^ 4)) := by
  rfl

/-- The joint normalized-radius and transverse residual has zero Taylor jet
through order four at the origin. -/
theorem weightedStateJet (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    FiniteTaylorJet.ofFunction ℝ 4 (remainder θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun _ : ℝ ↦ ((0, 0, 0) : ℝ × ℝ × ℝ)) 0 := by
  have hremainder : remainder θ = DFP.TwoLeg.StateJetAssembly.jointResidual θ := by
    funext ε
    rw [remainder_apply, DFP.TwoLeg.StateJetAssembly.jointResidual_apply]
  rw [hremainder]
  exact DFP.TwoLeg.StateJetAssembly.weightedJointResidualJet θ

/-- The thirteen scalar factors whose positivity gives a common regularity
domain for both factored legs and the signed square-root update. -/
def domainFactors (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) : Fin 13 → ℝ :=
  let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
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
  ![B₁, C₁,
    RealSymmetric2.high (metric₁ 0 0) (metric₁ 0 1) (metric₁ 1 1),
    RealSymmetric2.lowDenom (metric₁ 0 0) (metric₁ 0 1) (metric₁ 1 1),
    spectral₁.2 * gradient₁.2, spectral₁.1 * gradient₁.1 ^ 2,
    beta, gamma,
    RealSymmetric2.high (metric₂ 0 0) (metric₂ 0 1) (metric₂ 1 1),
    RealSymmetric2.lowDenom (metric₂ 0 0) (metric₂ 0 1) (metric₂ 1 1),
    spectral₂.2 * gradient₂.2, spectral₂.1 * gradient₂.1 ^ 2,
    DFP.TwoLeg.radiusFactor ε p h]

/-- Evaluation of the ordered vector of regularity factors. -/
theorem domainFactors_apply (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) (i : Fin 13) :
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
       ![B₁, C₁,
         RealSymmetric2.high (metric₁ 0 0) (metric₁ 0 1) (metric₁ 1 1),
         RealSymmetric2.lowDenom (metric₁ 0 0) (metric₁ 0 1) (metric₁ 1 1),
         spectral₁.2 * gradient₁.2, spectral₁.1 * gradient₁.1 ^ 2,
         beta, gamma,
         RealSymmetric2.high (metric₂ 0 0) (metric₂ 0 1) (metric₂ 1 1),
         RealSymmetric2.lowDenom (metric₂ 0 0) (metric₂ 0 1) (metric₂ 1 1),
         spectral₂.2 * gradient₂.2, spectral₂.1 * gradient₂.1 ^ 2,
         DFP.TwoLeg.radiusFactor ε p h] i) := by
  rfl

/-- The coefficient space for the cubic and quartic graph parameters. -/
private abbrev stateJetGraphCoeffs := (ℝ × ℝ) × (ℝ × ℝ)

/-- The polynomial graph path with parameter coefficients carried as an analytic input. -/
private def stateJetRemainderJointPath
    (z : stateJetGraphCoeffs × ℝ) : ℝ × ℝ × ℝ :=
  DFP.TwoLeg.graphJetPath
    z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2

/-- The graph path rebuilt at the signed scale returned by the state map. -/
private def stateJetRemainderNextPath
    (z : stateJetGraphCoeffs × ℝ) : ℝ × ℝ × ℝ :=
  let y := DFP.TwoLeg.stateMap (stateJetRemainderJointPath z)
  DFP.TwoLeg.graphJetPath
    z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 y.1

/-- The graph path is analytic at its zero-scale base point for every coefficient tuple. -/
private theorem stateJetRemainderJointPath_analyticAt
    (θ : stateJetGraphCoeffs) :
    AnalyticAt ℝ stateJetRemainderJointPath (θ, 0) := by
  have hθ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1) (θ, 0) :=
    analyticAt_fst
  have hθ₁ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ
  have hθ₂ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ
  have hP₃ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ₁
  have hH₃ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ₁
  have hP₄ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.2.1) (θ, 0) :=
    analyticAt_fst.comp hθ₂
  have hH₄ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.2.2) (θ, 0) :=
    analyticAt_snd.comp hθ₂
  have hε : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.2) (θ, 0) :=
    analyticAt_snd
  have hp : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        2 + z.1.1.1 * z.2 ^ 3 + z.1.2.1 * z.2 ^ 4) (θ, 0) := by
    fun_prop
  have hh : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        1 + z.1.1.2 * z.2 ^ 3 + z.1.2.2 * z.2 ^ 4) (θ, 0) := by
    fun_prop
  apply (hε.prod (hp.prod hh)).congr
  filter_upwards [] with z
  rfl

/-- The graph path takes the distinguished base value at zero scale. -/
private theorem stateJetRemainderJointPath_base
    (θ : stateJetGraphCoeffs) :
    stateJetRemainderJointPath (θ, 0) = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
  simp [stateJetRemainderJointPath, DFP.TwoLeg.graphJetPath]

/-- Composing the analytic state map with the graph path remains analytic. -/
private theorem stateJetRemainderState_analyticAt
    (θ : stateJetGraphCoeffs) :
    AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ =>
      DFP.TwoLeg.stateMap (stateJetRemainderJointPath z)) (θ, 0) := by
  have houter := DFP.TwoLeg.stateMapAnalytic
  rw [← stateJetRemainderJointPath_base θ] at houter
  simpa only [Function.comp_def] using houter.comp
    (stateJetRemainderJointPath_analyticAt θ)

/-- Rebuilding the graph at the updated scale is analytic. -/
private theorem stateJetRemainderNextPath_analyticAt
    (θ : stateJetGraphCoeffs) :
    AnalyticAt ℝ stateJetRemainderNextPath (θ, 0) := by
  have hθ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1) (θ, 0) :=
    analyticAt_fst
  have hθ₁ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ
  have hθ₂ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ
  have hP₃ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ₁
  have hH₃ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ₁
  have hP₄ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.2.1) (θ, 0) :=
    analyticAt_fst.comp hθ₂
  have hH₄ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.2.2) (θ, 0) :=
    analyticAt_snd.comp hθ₂
  have hstate := stateJetRemainderState_analyticAt θ
  have hε : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        (DFP.TwoLeg.stateMap (stateJetRemainderJointPath z)).1) (θ, 0) :=
    analyticAt_fst.comp hstate
  have hp : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        2 + z.1.1.1 *
            (DFP.TwoLeg.stateMap (stateJetRemainderJointPath z)).1 ^ 3 +
          z.1.2.1 *
            (DFP.TwoLeg.stateMap (stateJetRemainderJointPath z)).1 ^ 4) (θ, 0) := by
    fun_prop
  have hh : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        1 + z.1.1.2 *
            (DFP.TwoLeg.stateMap (stateJetRemainderJointPath z)).1 ^ 3 +
          z.1.2.2 *
            (DFP.TwoLeg.stateMap (stateJetRemainderJointPath z)).1 ^ 4) (θ, 0) := by
    fun_prop
  apply (hε.prod (hp.prod hh)).congr
  filter_upwards [] with z
  rfl

/-- The full residual is analytic jointly in graph coefficients and signed scale. -/
private theorem stateJetRemainder_analyticAt
    (θ : stateJetGraphCoeffs) :
    AnalyticAt ℝ (Function.uncurry remainder) (θ, 0) := by
  have hpath := stateJetRemainderJointPath_analyticAt θ
  have hstate := stateJetRemainderState_analyticAt θ
  have hnext := stateJetRemainderNextPath_analyticAt θ
  have hradius : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        DFP.TwoLeg.radiusFactor
          (stateJetRemainderJointPath z).1
          (stateJetRemainderJointPath z).2.1
          (stateJetRemainderJointPath z).2.2) (θ, 0) := by
    have houter := DFP.TwoLeg.analyticAt_radiusFactor
    rw [← stateJetRemainderJointPath_base θ] at houter
    simpa only [Function.comp_def] using houter.comp hpath
  have hstateP : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        (DFP.TwoLeg.stateMap (stateJetRemainderJointPath z)).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hstate)
  have hstateH : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        (DFP.TwoLeg.stateMap (stateJetRemainderJointPath z)).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hstate)
  have hnextP : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        (stateJetRemainderNextPath z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hnext)
  have hnextH : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        (stateJetRemainderNextPath z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hnext)
  have hθ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1) (θ, 0) :=
    analyticAt_fst
  have hθ₁ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ
  have hθ₂ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ
  have hP₃ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ₁
  have hH₃ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ₁
  have hP₄ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.2.1) (θ, 0) :=
    analyticAt_fst.comp hθ₂
  have hH₄ : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.1.2.2) (θ, 0) :=
    analyticAt_snd.comp hθ₂
  have hε : AnalyticAt ℝ (fun z : stateJetGraphCoeffs × ℝ => z.2) (θ, 0) :=
    analyticAt_snd
  have htargetR : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        1 + ((6 * z.1.1.2 + 5 * z.1.1.1 - 300) / 18) * z.2 ^ 3 +
          ((6 * z.1.2.2 + 5 * z.1.2.1 + 54) / 18) * z.2 ^ 4) (θ, 0) := by
    fun_prop
  have htargetP : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        ((6 * z.1.1.2 - 10 * z.1.1.1 + 348) / 9) * z.2 ^ 3 +
          ((6 * z.1.2.2 - 10 * z.1.2.1 - 18) / 9) * z.2 ^ 4) (θ, 0) := by
    fun_prop
  have htargetH : AnalyticAt ℝ
      (fun z : stateJetGraphCoeffs × ℝ =>
        (8 - z.1.1.2) * z.2 ^ 3 - z.1.2.2 * z.2 ^ 4) (θ, 0) := by
    fun_prop
  have hassembled :=
    (hradius.sub htargetR).prod
      ((hstateP.sub hnextP).sub htargetP |>.prod
        ((hstateH.sub hnextH).sub htargetH))
  apply hassembled.congr
  filter_upwards [] with z
  rfl

/-- The residual has five continuous derivatives at every coefficient tuple and zero scale. -/
private theorem stateJetRemainder_contDiffAt_five
    (θ : stateJetGraphCoeffs) :
    ContDiffAt ℝ 5 (Function.uncurry remainder) (θ, 0) :=
  (stateJetRemainder_analyticAt θ).contDiffAt

/-- The joint residual has a uniform fifth-order bound on every compact coefficient ball. -/
private theorem stateJetRemainder_uniform_orderFive (B : ℝ) :
    ∃ C > 0, ∃ δ > 0,
      ∀ θ ∈ Metric.closedBall (0 : stateJetGraphCoeffs) B,
        ∀ ε : ℝ, |ε| < δ →
          ‖remainder θ ε‖ ≤ C * |ε| ^ (5 : ℕ) := by
  apply FiniteTaylorJet.uniform_orderFive_bound_of_zero_fourJet
    remainder (Metric.closedBall (0 : stateJetGraphCoeffs) B)
    (isCompact_closedBall _ _)
  · intro θ hθ
    exact stateJetRemainder_contDiffAt_five θ
  · intro θ hθ
    exact weightedStateJet θ

/-- The high eigenvalue expression is continuous in the three independent symmetric-matrix
entries. -/
private theorem stateJetHigh_continuous :
    Continuous (fun x : ℝ × ℝ × ℝ =>
      RealSymmetric2.high x.1 x.2.1 x.2.2) := by
  unfold RealSymmetric2.high RealSymmetric2.gap
  fun_prop

/-- The low-eigenvalue denominator is continuous in the three independent symmetric-matrix
entries. -/
private theorem stateJetLowDenom_continuous :
    Continuous (fun x : ℝ × ℝ × ℝ =>
      RealSymmetric2.lowDenom x.1 x.2.1 x.2.2) := by
  unfold RealSymmetric2.lowDenom RealSymmetric2.low RealSymmetric2.gap
  fun_prop

/-- Low-eigenvalue denominators remain continuous after composition with a continuous
three-entry symmetric-matrix path. -/
private theorem stateJetLowDenom_comp_continuousAt
    {α : Type*} [TopologicalSpace α] (f : α → ℝ × ℝ × ℝ) {x : α}
    (hf : ContinuousAt f x) :
    ContinuousAt (fun y => RealSymmetric2.lowDenom (f y).1 (f y).2.1 (f y).2.2) x :=
  stateJetLowDenom_continuous.continuousAt.comp hf

/-- Every output-metric entry stays continuous after composition with a graph coefficient path. -/
private theorem stateJetMetricEntry_continuousAt
    (θ : stateJetGraphCoeffs) (first : Bool) (i j : Fin 2) :
    ContinuousAt
      (fun z : stateJetGraphCoeffs × ℝ =>
        if first then
          DFP.FirstLeg.outputMetric (stateJetRemainderJointPath z).1
            (stateJetRemainderJointPath z).2.1
            (stateJetRemainderJointPath z).2.2 i j
        else
          DFP.SecondLeg.outputMetric (stateJetRemainderJointPath z).1
            (stateJetRemainderJointPath z).2.1
            (stateJetRemainderJointPath z).2.2 i j) (θ, 0) := by
  classical
  by_cases hfirst : first
  · subst hfirst
    have houter := DFP.FirstLeg.outputMetricEntry_analyticAt i j
    rw [← stateJetRemainderJointPath_base θ] at houter
    have h := houter.comp (stateJetRemainderJointPath_analyticAt θ)
    simpa [Function.comp_def] using h.continuousAt
  · simp only [Bool.not_eq_true] at hfirst
    have houter := DFP.SecondLeg.outputMetricEntry_analyticAt i j
    rw [← stateJetRemainderJointPath_base θ] at houter
    have h := houter.comp (stateJetRemainderJointPath_analyticAt θ)
    simpa [Function.comp_def, hfirst] using h.continuousAt

/-- The first-leg factor triple varies continuously along every graph-jet path at zero scale. -/
private theorem stateJetFirstFactors_continuousAt
    (θ : stateJetGraphCoeffs) :
    ContinuousAt
      (fun z : stateJetGraphCoeffs × ℝ => DFP.FirstLeg.factors
        (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1
        (stateJetRemainderJointPath z).2.2) (θ, 0) := by
  have houter := DFP.FirstLeg.factorsAnalytic
  rw [← stateJetRemainderJointPath_base θ] at houter
  exact (houter.comp (stateJetRemainderJointPath_analyticAt θ)).continuousAt

/-- The second-leg factor triple varies continuously along every graph-jet path at zero scale. -/
private theorem stateJetSecondFactors_continuousAt
    (θ : stateJetGraphCoeffs) :
    ContinuousAt
      (fun z : stateJetGraphCoeffs × ℝ => DFP.SecondLeg.factors
        (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1
        (stateJetRemainderJointPath z).2.2) (θ, 0) := by
  have houter := DFP.SecondLeg.factorsAnalytic
  rw [← stateJetRemainderJointPath_base θ] at houter
  exact (houter.comp (stateJetRemainderJointPath_analyticAt θ)).continuousAt

/-- The first-leg high eigenvalue factor is continuous along every graph-jet path at zero scale. -/
private theorem stateJetFirstHigh_continuousAt
    (θ : stateJetGraphCoeffs) :
    ContinuousAt (fun z : stateJetGraphCoeffs × ℝ => RealSymmetric2.high
      (DFP.FirstLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 0)
      (DFP.FirstLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 1)
      (DFP.FirstLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 1 1)) (θ, 0) := by
  exact stateJetHigh_continuous.continuousAt.comp
    ((stateJetMetricEntry_continuousAt θ true 0 0).prodMk
      ((stateJetMetricEntry_continuousAt θ true 0 1).prodMk
        (stateJetMetricEntry_continuousAt θ true 1 1)))

/-- The first-leg low-eigenvalue denominator is continuous along every graph-jet path at zero scale. -/
private theorem stateJetFirstLowDenom_continuousAt
    (θ : stateJetGraphCoeffs) :
    ContinuousAt (fun z : stateJetGraphCoeffs × ℝ => RealSymmetric2.lowDenom
      (DFP.FirstLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 0)
      (DFP.FirstLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 1)
      (DFP.FirstLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 1 1)) (θ, 0) := by
  let f : stateJetGraphCoeffs × ℝ → ℝ × ℝ × ℝ := fun z =>
    (DFP.FirstLeg.outputMetric (stateJetRemainderJointPath z).1
      (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 0,
      DFP.FirstLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 1,
      DFP.FirstLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 1 1)
  have hf : ContinuousAt f (θ, 0) :=
    (stateJetMetricEntry_continuousAt θ true 0 0).prodMk
      ((stateJetMetricEntry_continuousAt θ true 0 1).prodMk
        (stateJetMetricEntry_continuousAt θ true 1 1))
  simpa only [f] using stateJetLowDenom_comp_continuousAt f hf

/-- The second-leg high eigenvalue factor is continuous along every graph-jet path at zero scale. -/
private theorem stateJetSecondHigh_continuousAt
    (θ : stateJetGraphCoeffs) :
    ContinuousAt (fun z : stateJetGraphCoeffs × ℝ => RealSymmetric2.high
      (DFP.SecondLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 0)
      (DFP.SecondLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 1)
      (DFP.SecondLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 1 1)) (θ, 0) := by
  exact stateJetHigh_continuous.continuousAt.comp
    ((stateJetMetricEntry_continuousAt θ false 0 0).prodMk
      ((stateJetMetricEntry_continuousAt θ false 0 1).prodMk
        (stateJetMetricEntry_continuousAt θ false 1 1)))

/-- The second-leg low-eigenvalue denominator is continuous along every graph-jet path at zero scale. -/
private theorem stateJetSecondLowDenom_continuousAt
    (θ : stateJetGraphCoeffs) :
    ContinuousAt (fun z : stateJetGraphCoeffs × ℝ => RealSymmetric2.lowDenom
      (DFP.SecondLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 0)
      (DFP.SecondLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 1)
      (DFP.SecondLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 1 1)) (θ, 0) := by
  let f : stateJetGraphCoeffs × ℝ → ℝ × ℝ × ℝ := fun z =>
    (DFP.SecondLeg.outputMetric (stateJetRemainderJointPath z).1
      (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 0,
      DFP.SecondLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 0 1,
      DFP.SecondLeg.outputMetric (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1 (stateJetRemainderJointPath z).2.2 1 1)
  have hf : ContinuousAt f (θ, 0) :=
    (stateJetMetricEntry_continuousAt θ false 0 0).prodMk
      ((stateJetMetricEntry_continuousAt θ false 0 1).prodMk
        (stateJetMetricEntry_continuousAt θ false 1 1))
  simpa only [f] using stateJetLowDenom_comp_continuousAt f hf

/-- The radius factor is continuous along every graph-jet path at zero scale. -/
private theorem stateJetRadiusFactor_continuousAt
    (θ : stateJetGraphCoeffs) :
    ContinuousAt (fun z : stateJetGraphCoeffs × ℝ =>
      DFP.TwoLeg.radiusFactor (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1
        (stateJetRemainderJointPath z).2.2) (θ, 0) := by
  have houter := DFP.TwoLeg.analyticAt_radiusFactor
  rw [← stateJetRemainderJointPath_base θ] at houter
  exact (houter.comp (stateJetRemainderJointPath_analyticAt θ)).continuousAt

/-- Every one of the thirteen regularity factors is continuous along the joint graph path at
zero scale. -/
private theorem stateJetDomainFactors_continuousAt
    (θ : stateJetGraphCoeffs) (i : Fin 13) :
    ContinuousAt
      (fun z : stateJetGraphCoeffs × ℝ => domainFactors z.1 z.2 i)
      (θ, 0) := by
  have hfirst := stateJetFirstFactors_continuousAt θ
  have hsecond := stateJetSecondFactors_continuousAt θ
  have hhigh₁ := stateJetFirstHigh_continuousAt θ
  have hlow₁ := stateJetFirstLowDenom_continuousAt θ
  have hhigh₂ := stateJetSecondHigh_continuousAt θ
  have hlow₂ := stateJetSecondLowDenom_continuousAt θ
  have hradius := stateJetRadiusFactor_continuousAt θ
  have hL₁ : ContinuousAt (fun z : stateJetGraphCoeffs × ℝ =>
      (DFP.FirstLeg.spectralFactors (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1
        (stateJetRemainderJointPath z).2.2).1) (θ, 0) := by
    have hfac := hfirst
    have hspectral := continuousAt_fst.comp hfac
    have h := continuousAt_fst.comp hspectral
    simpa only [DFP.FirstLeg.factors, Function.comp_def] using h
  have hH₁ : ContinuousAt (fun z : stateJetGraphCoeffs × ℝ =>
      (DFP.FirstLeg.spectralFactors (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1
        (stateJetRemainderJointPath z).2.2).2) (θ, 0) := by
    have hfac := hfirst
    have hspectral := continuousAt_fst.comp hfac
    have h := continuousAt_snd.comp hspectral
    simpa only [DFP.FirstLeg.factors, Function.comp_def] using h
  have hQ₁ : ContinuousAt (fun z : stateJetGraphCoeffs × ℝ =>
      (DFP.FirstLeg.gradientFactors (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1
        (stateJetRemainderJointPath z).2.2).1) (θ, 0) := by
    have hfac := hfirst
    have hgradient := continuousAt_fst.comp (continuousAt_snd.comp hfac)
    have h := continuousAt_fst.comp hgradient
    simpa only [DFP.FirstLeg.factors, Function.comp_def] using h
  have hU₁ : ContinuousAt (fun z : stateJetGraphCoeffs × ℝ =>
      (DFP.FirstLeg.gradientFactors (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1
        (stateJetRemainderJointPath z).2.2).2) (θ, 0) := by
    have hfac := hfirst
    have hgradient := continuousAt_fst.comp (continuousAt_snd.comp hfac)
    have h := continuousAt_snd.comp hgradient
    simpa only [DFP.FirstLeg.factors, Function.comp_def] using h
  have hL₂ : ContinuousAt (fun z : stateJetGraphCoeffs × ℝ =>
      (DFP.SecondLeg.spectralFactors (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1
        (stateJetRemainderJointPath z).2.2).1) (θ, 0) := by
    have hfac := hsecond
    have hspectral := continuousAt_fst.comp hfac
    have h := continuousAt_fst.comp hspectral
    simpa only [DFP.SecondLeg.factors, Function.comp_def] using h
  have hH₂ : ContinuousAt (fun z : stateJetGraphCoeffs × ℝ =>
      (DFP.SecondLeg.spectralFactors (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1
        (stateJetRemainderJointPath z).2.2).2) (θ, 0) := by
    have hfac := hsecond
    have hspectral := continuousAt_fst.comp hfac
    have h := continuousAt_snd.comp hspectral
    simpa only [DFP.SecondLeg.factors, Function.comp_def] using h
  have hQ₂ : ContinuousAt (fun z : stateJetGraphCoeffs × ℝ =>
      (DFP.SecondLeg.gradientFactors (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1
        (stateJetRemainderJointPath z).2.2).1) (θ, 0) := by
    have hfac := hsecond
    have hgradient := continuousAt_fst.comp (continuousAt_snd.comp hfac)
    have h := continuousAt_fst.comp hgradient
    simpa only [DFP.SecondLeg.factors, Function.comp_def] using h
  have hU₂ : ContinuousAt (fun z : stateJetGraphCoeffs × ℝ =>
      (DFP.SecondLeg.gradientFactors (stateJetRemainderJointPath z).1
        (stateJetRemainderJointPath z).2.1
        (stateJetRemainderJointPath z).2.2).2) (θ, 0) := by
    have hfac := hsecond
    have hgradient := continuousAt_fst.comp (continuousAt_snd.comp hfac)
    have h := continuousAt_snd.comp hgradient
    simpa only [DFP.SecondLeg.factors, Function.comp_def] using h
  have hε : ContinuousAt (fun z : stateJetGraphCoeffs × ℝ => z.2) (θ, 0) :=
    continuousAt_snd
  fin_cases i <;>
    simp only [domainFactors, DFP.TwoLeg.graphJetPath] <;>
    dsimp [stateJetRemainderJointPath]
  · fun_prop
  · fun_prop
  · simpa only [Function.comp_apply, stateJetRemainderJointPath,
      DFP.TwoLeg.graphJetPath] using hhigh₁
  · simpa only [Function.comp_apply, stateJetRemainderJointPath,
      DFP.TwoLeg.graphJetPath] using hlow₁
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop
  · simpa only [Function.comp_apply, stateJetRemainderJointPath,
      DFP.TwoLeg.graphJetPath] using hhigh₂
  · simpa only [Function.comp_apply, stateJetRemainderJointPath,
      DFP.TwoLeg.graphJetPath] using hlow₂
  · fun_prop
  · fun_prop
  · simpa only [Function.comp_apply, stateJetRemainderJointPath,
      DFP.TwoLeg.graphJetPath] using hradius

/-- Compact coefficient balls give a uniform positive lower bound for all thirteen regularity
factors. -/
private theorem stateJetDomainFactors_uniform_lower_bound
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ m > 0, ∃ δ > 0,
      ∀ θ ∈ Metric.closedBall (0 : stateJetGraphCoeffs) B,
        ∀ i : Fin 13, ∀ ε : ℝ, |ε| < δ → m ≤ domainFactors θ ε i := by
  let K : Set stateJetGraphCoeffs := Metric.closedBall 0 B
  -- The closed-ball subtype needs its compact-space instance for the finite
  -- compact-uniform positivity theorem applied to all thirteen factors.
  letI : CompactSpace K := by
    apply isCompact_iff_compactSpace.mp
    dsimp only [K]
    exact isCompact_closedBall _ _
  have hneK : Nonempty K := by
    have hzero : (0 : stateJetGraphCoeffs) ∈ Metric.closedBall 0 B := by
      rw [Metric.mem_closedBall]
      simpa only [dist_self] using hB
    exact ⟨⟨0, by simpa only [K] using hzero⟩⟩
  have hcontinuous : ∀ θ : K, ∀ i : Fin 13,
      ContinuousAt
        (fun p : ℝ × K => domainFactors p.2.1 p.1 i) (0, θ) := by
    intro θ i
    have hmap : ContinuousAt
        (fun p : ℝ × K => ((p.2.1, p.1) : stateJetGraphCoeffs × ℝ)) (0, θ) := by
      fun_prop
    have hcomp := ContinuousAt.comp
      (f := fun p : ℝ × K => ((p.2.1, p.1) : stateJetGraphCoeffs × ℝ))
      (g := fun z : stateJetGraphCoeffs × ℝ => domainFactors z.1 z.2 i)
      (x := ((0, θ) : ℝ × K))
      (stateJetDomainFactors_continuousAt θ.1 i) hmap
    simpa only [Function.comp_def] using hcomp
  have hpositive : ∀ θ : K, ∀ i : Fin 13,
      0 < domainFactors θ.1 0 i := by
    intro θ i
    fin_cases i <;>
      norm_num [domainFactors, DFP.TwoLeg.graphJetPath,
        DFP.FirstLeg.outputMetric, DFP.FirstLeg.spectralFactors,
        DFP.FirstLeg.gradientFactors, DFP.SecondLeg.outputMetric,
        DFP.SecondLeg.spectralFactors, DFP.SecondLeg.gradientFactors,
        DFP.TwoLeg.radiusFactor, DFP.SecondLeg.canonicalFactors,
        RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
        RealSymmetric2.lowDenom]
  obtain ⟨m, hm, δ, hδ, hbound⟩ :=
    CompactUniformPositivity.exists_uniform_lower_bound_finite_of_pointwise_continuousAt
      (fun ε (θ : K) (i : Fin 13) => domainFactors θ.1 ε i)
      hcontinuous hneK (inferInstance : Nonempty (Fin 13)) hpositive
  refine ⟨m, hm, δ, hδ, ?_⟩
  intro θ hθ i ε hε
  let θK : K := ⟨θ, by simpa only [K] using hθ⟩
  exact hbound θK i ε hε


/-- On every bounded coefficient ball, one radius simultaneously controls all
three order-five residuals and keeps every regularity factor uniformly positive. -/
theorem stateJetsCommonDomain (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > 0, ∃ m > 0, ∃ δ ∈ Set.Ioo (0 : ℝ) (1 / 4),
      ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
        ∀ ε : ℝ, |ε| < δ →
          ‖remainder θ ε‖ ≤ C * |ε| ^ 5 ∧
            ∀ i : Fin 13, m ≤ domainFactors θ ε i := by
  obtain ⟨C, hC, δr, hδr, hr⟩ := stateJetRemainder_uniform_orderFive B
  obtain ⟨m, hm, δp, hδp, hp⟩ :=
    stateJetDomainFactors_uniform_lower_bound B hB
  let δ : ℝ := min δr (min δp (1 / 8))
  have hδ : 0 < δ := by
    dsimp only [δ]
    exact lt_min hδr (lt_min hδp (by norm_num))
  have hδquarter : δ < 1 / 4 := by
    have hδeighth : δ ≤ 1 / 8 := by
      dsimp only [δ]
      exact (min_le_right _ _).trans (min_le_right _ _)
    linarith
  refine ⟨C, hC, m, hm, δ, ⟨hδ, hδquarter⟩, ?_⟩
  intro θ hθ ε hε
  have hεr : |ε| < δr := lt_of_lt_of_le hε (by
    dsimp only [δ]
    exact min_le_left _ _)
  have hεp : |ε| < δp := lt_of_lt_of_le hε (by
    dsimp only [δ]
    exact (min_le_right _ _).trans (min_le_left _ _))
  exact ⟨hr θ hθ ε hεr, fun i => hp θ hθ i ε hεp⟩

/-- The joint state-jet residual has a uniform order-five remainder on every
closed ball of graph coefficients. -/
theorem uniformRemainderOn (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > 0,
      Asymptotics.IsUniformRemainderOn remainder
        (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B) C 5 := by
  obtain ⟨C, hC, m, hm, δ, hδ, hcommon⟩ := stateJetsCommonDomain B hB
  refine ⟨C, hC, ?_⟩
  unfold Asymptotics.IsUniformRemainderOn
  refine ⟨δ, hδ.1, ?_⟩
  intro θ hθ ε hε
  have hpow : |ε| ^ (5 : ℝ) = |ε| ^ (5 : ℕ) :=
    Real.rpow_natCast |ε| 5
  rw [hpow]
  exact (hcommon θ hθ ε hε).1

end DFP.TwoLeg.StateJet
