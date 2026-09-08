module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.UniformZeroJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.StateJetClosure
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.TwoLeg.StateJet

abbrev RemainderGraphCoeffs := (ℝ × ℝ) × (ℝ × ℝ)

def remainderJointPath (z : RemainderGraphCoeffs × ℝ) : ℝ × ℝ × ℝ :=
  DFP.TwoLeg.graphJetPath
    z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2

def remainderNextPath (z : RemainderGraphCoeffs × ℝ) : ℝ × ℝ × ℝ :=
  let y := DFP.TwoLeg.stateMap (remainderJointPath z)
  DFP.TwoLeg.graphJetPath
    z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 y.1

theorem remainderJointPath_analyticAt (θ : RemainderGraphCoeffs) :
    AnalyticAt ℝ remainderJointPath (θ, 0) := by
  have hθ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1) (θ, 0) :=
    analyticAt_fst
  have hθ₁ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ
  have hθ₂ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ
  have hP₃ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ₁
  have hH₃ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ₁
  have hP₄ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.2.1) (θ, 0) :=
    analyticAt_fst.comp hθ₂
  have hH₄ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.2.2) (θ, 0) :=
    analyticAt_snd.comp hθ₂
  have hε : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.2) (θ, 0) :=
    analyticAt_snd
  have hp : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ =>
        2 + z.1.1.1 * z.2 ^ 3 + z.1.2.1 * z.2 ^ 4) (θ, 0) := by
    fun_prop
  have hh : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ =>
        1 + z.1.1.2 * z.2 ^ 3 + z.1.2.2 * z.2 ^ 4) (θ, 0) := by
    fun_prop
  apply (hε.prod (hp.prod hh)).congr
  filter_upwards [] with z
  rfl

theorem remainderJointPath_base (θ : RemainderGraphCoeffs) :
    remainderJointPath (θ, 0) = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
  simp [remainderJointPath, DFP.TwoLeg.graphJetPath]

theorem remainderState_analyticAt (θ : RemainderGraphCoeffs) :
    AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ =>
      DFP.TwoLeg.stateMap (remainderJointPath z)) (θ, 0) := by
  have houter := DFP.TwoLeg.stateMapAnalytic
  rw [← remainderJointPath_base θ] at houter
  simpa only [Function.comp_def] using houter.comp (remainderJointPath_analyticAt θ)

theorem remainderNextPath_analyticAt (θ : RemainderGraphCoeffs) :
    AnalyticAt ℝ remainderNextPath (θ, 0) := by
  have hθ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1) (θ, 0) :=
    analyticAt_fst
  have hθ₁ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ
  have hθ₂ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ
  have hP₃ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ₁
  have hH₃ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ₁
  have hP₄ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.2.1) (θ, 0) :=
    analyticAt_fst.comp hθ₂
  have hH₄ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.2.2) (θ, 0) :=
    analyticAt_snd.comp hθ₂
  have hstate := remainderState_analyticAt θ
  have hε : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ =>
        (DFP.TwoLeg.stateMap (remainderJointPath z)).1) (θ, 0) :=
    analyticAt_fst.comp hstate
  have hp : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ =>
        2 + z.1.1.1 * (DFP.TwoLeg.stateMap (remainderJointPath z)).1 ^ 3 +
          z.1.2.1 * (DFP.TwoLeg.stateMap (remainderJointPath z)).1 ^ 4) (θ, 0) := by
    fun_prop
  have hh : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ =>
        1 + z.1.1.2 * (DFP.TwoLeg.stateMap (remainderJointPath z)).1 ^ 3 +
          z.1.2.2 * (DFP.TwoLeg.stateMap (remainderJointPath z)).1 ^ 4) (θ, 0) := by
    fun_prop
  apply (hε.prod (hp.prod hh)).congr
  filter_upwards [] with z
  rfl

theorem remainder_analyticAt (θ : RemainderGraphCoeffs) :
    AnalyticAt ℝ (Function.uncurry remainder) (θ, 0) := by
  have hpath := remainderJointPath_analyticAt θ
  have hstate := remainderState_analyticAt θ
  have hnext := remainderNextPath_analyticAt θ
  have hradius : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ =>
        DFP.TwoLeg.radiusFactor
          (remainderJointPath z).1 (remainderJointPath z).2.1 (remainderJointPath z).2.2)
      (θ, 0) := by
    have houter := DFP.TwoLeg.analyticAt_radiusFactor
    rw [← remainderJointPath_base θ] at houter
    simpa only [Function.comp_def] using houter.comp hpath
  have hstateP : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ =>
        (DFP.TwoLeg.stateMap (remainderJointPath z)).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hstate)
  have hstateH : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ =>
        (DFP.TwoLeg.stateMap (remainderJointPath z)).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hstate)
  have hnextP : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ => (remainderNextPath z).2.1) (θ, 0) :=
    analyticAt_fst.comp (analyticAt_snd.comp hnext)
  have hnextH : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ => (remainderNextPath z).2.2) (θ, 0) :=
    analyticAt_snd.comp (analyticAt_snd.comp hnext)
  have hθ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1) (θ, 0) :=
    analyticAt_fst
  have hθ₁ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ
  have hθ₂ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ
  have hP₃ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ₁
  have hH₃ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ₁
  have hP₄ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.2.1) (θ, 0) :=
    analyticAt_fst.comp hθ₂
  have hH₄ : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.1.2.2) (θ, 0) :=
    analyticAt_snd.comp hθ₂
  have hε : AnalyticAt ℝ (fun z : RemainderGraphCoeffs × ℝ => z.2) (θ, 0) :=
    analyticAt_snd
  have htargetR : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ =>
        1 + ((6 * z.1.1.2 + 5 * z.1.1.1 - 300) / 18) * z.2 ^ 3 +
          ((6 * z.1.2.2 + 5 * z.1.2.1 + 54) / 18) * z.2 ^ 4)
      (θ, 0) := by
    fun_prop
  have htargetP : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ =>
        ((6 * z.1.1.2 - 10 * z.1.1.1 + 348) / 9) * z.2 ^ 3 +
          ((6 * z.1.2.2 - 10 * z.1.2.1 - 18) / 9) * z.2 ^ 4)
      (θ, 0) := by
    fun_prop
  have htargetH : AnalyticAt ℝ
      (fun z : RemainderGraphCoeffs × ℝ =>
        (8 - z.1.1.2) * z.2 ^ 3 - z.1.2.2 * z.2 ^ 4)
      (θ, 0) := by
    fun_prop
  have hassembled :=
    (hradius.sub htargetR).prod
      ((hstateP.sub hnextP).sub htargetP |>.prod
        ((hstateH.sub hnextH).sub htargetH))
  apply hassembled.congr
  filter_upwards [] with z
  rfl

theorem remainder_contDiffAt_five (θ : RemainderGraphCoeffs) :
    ContDiffAt ℝ 5 (Function.uncurry remainder) (θ, 0) :=
  (remainder_analyticAt θ).contDiffAt

theorem remainder_uniform_orderFive (B : ℝ) :
    ∃ C > 0, ∃ δ > 0,
      ∀ θ ∈ Metric.closedBall (0 : RemainderGraphCoeffs) B,
        ∀ ε : ℝ, |ε| < δ →
          ‖remainder θ ε‖ ≤ C * |ε| ^ (5 : ℕ) := by
  apply FiniteTaylorJet.uniform_orderFive_bound_of_zero_fourJet
    remainder (Metric.closedBall (0 : RemainderGraphCoeffs) B)
    (isCompact_closedBall _ _)
  · intro θ hθ
    exact remainder_contDiffAt_five θ
  · intro θ hθ
    have hremainder : remainder θ =
        DFP.TwoLeg.StateJetAssembly.jointResidual θ := by
      funext ε
      rw [remainder_apply,
        DFP.TwoLeg.StateJetAssembly.jointResidual_apply]
    rw [hremainder]
    exact
      DFP.TwoLeg.StateJetAssembly.weightedJointResidualJet_via_scaleStationarity θ

end DFP.TwoLeg.StateJet


