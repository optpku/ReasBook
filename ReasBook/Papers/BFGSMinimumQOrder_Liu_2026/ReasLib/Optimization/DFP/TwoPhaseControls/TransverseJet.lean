module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.Uniform
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.UniformZeroJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.WeightedDefectJets
public import ReasLib.Optimization.DFP.TwoPhaseControls.RadiusJet
import all ReasLib.Analysis.Asymptotics.UniformRemainder

public section

noncomputable section

namespace DFP.TwoLeg

/-- Along a polynomial graph with arbitrary cubic and quartic coefficients,
the updated shape coordinate has the displayed order-four finite Taylor jet. -/
theorem weightedTransversePJet (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          let x := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε
          (DFP.TwoLeg.stateMap x).2.1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          2 + ((6 * H₃ - P₃ + 348) / 9) * ε ^ 3 +
            ((6 * H₄ - P₄ - 18) / 9) * ε ^ 4) 0 := by
  simpa only [graphJetPath_apply] using
    weightedTransversePJet_via_scaleStationarity P₃ H₃ P₄ H₄

/-- Along a polynomial graph with arbitrary cubic and quartic coefficients,
the updated high-eigenvalue coordinate has the displayed order-four finite Taylor jet. -/
theorem weightedTransverseHJet (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          let x := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε
          (DFP.TwoLeg.stateMap x).2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦ 1 + 8 * ε ^ 3) 0 := by
  simpa only [graphJetPath_apply] using
    weightedTransverseHJet_via_scaleStationarity P₃ H₃ P₄ H₄

/-- The shape-coordinate graph-invariance defect, evaluated at the updated signed
scale, has the displayed cubic and quartic coefficients. -/
theorem weightedTransversePDefectJet (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          let x := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε
          let y := DFP.TwoLeg.stateMap x
          let nextGraph := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ y.1
          y.2.1 - nextGraph.2.1) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          ((6 * H₃ - 10 * P₃ + 348) / 9) * ε ^ 3 +
            ((6 * H₄ - 10 * P₄ - 18) / 9) * ε ^ 4) 0 := by
  exact weightedTransversePDefectJet_via_scaleStationarity P₃ H₃ P₄ H₄

/-- The high-coordinate graph-invariance defect, evaluated at the updated signed
scale, has the displayed cubic and quartic coefficients. -/
theorem weightedTransverseHDefectJet (P₃ H₃ P₄ H₄ : ℝ) :
    FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦
          let x := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ ε
          let y := DFP.TwoLeg.stateMap x
          let nextGraph := DFP.TwoLeg.graphJetPath P₃ H₃ P₄ H₄ y.1
          y.2.2 - nextGraph.2.2) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun ε : ℝ ↦ (8 - H₃) * ε ^ 3 - H₄ * ε ^ 4) 0 := by
  exact weightedTransverseHDefectJet_via_scaleStationarity P₃ H₃ P₄ H₄

/-- Helper for Appendix Proposition A.5c (Weighted transverse shape jet): the two
updated transverse coordinates relative to the graph at the updated signed scale. -/
private def weightedTransverseActual
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) : ℝ × ℝ :=
  let x := graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
  let y := stateMap x
  let nextGraph := graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
  (y.2.1 - nextGraph.2.1, y.2.2 - nextGraph.2.2)

/-- Helper for Appendix Proposition A.5c (Weighted transverse shape jet): the
cubic-quartic model for the two transverse graph defects. -/
private def weightedTransversePolynomial
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) : ℝ × ℝ :=
  (((6 * θ.1.2 - 10 * θ.1.1 + 348) / 9) * ε ^ 3 +
      ((6 * θ.2.2 - 10 * θ.2.1 - 18) / 9) * ε ^ 4,
    (8 - θ.1.2) * ε ^ 3 - θ.2.2 * ε ^ 4)

/-- Helper for Appendix Proposition A.5c (Weighted transverse shape jet): the
paired difference between the actual transverse defect and its order-four model. -/
private def weightedTransverseResidual
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) (ε : ℝ) : ℝ × ℝ :=
  weightedTransverseActual θ ε - weightedTransversePolynomial θ ε

/-- Helper for Appendix Proposition A.5c (Weighted transverse shape jet): the
actual transverse defect family is jointly analytic at the zero-scale fiber. -/
private theorem weightedTransverseActual_analyticAt
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    AnalyticAt ℝ (Function.uncurry weightedTransverseActual) (θ, 0) := by
  have hθ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1) (θ, 0) :=
    analyticAt_fst
  have hθ₁ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ
  have hθ₂ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ
  have hP₃ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ₁
  have hH₃ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ₁
  have hP₄ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.2.1) (θ, 0) :=
    analyticAt_fst.comp hθ₂
  have hH₄ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.2.2) (θ, 0) :=
    analyticAt_snd.comp hθ₂
  have hε : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.2) (θ, 0) :=
    analyticAt_snd
  have hp : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦
        2 + z.1.1.1 * z.2 ^ 3 + z.1.2.1 * z.2 ^ 4) (θ, 0) := by
    fun_prop
  have hh : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦
        1 + z.1.1.2 * z.2 ^ 3 + z.1.2.2 * z.2 ^ 4) (θ, 0) := by
    fun_prop
  have hpath : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦
        graphJetPath z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2) (θ, 0) := by
    simpa only [graphJetPath_apply] using hε.prod (hp.prod hh)
  have hbase : graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 0 =
      ((0, 2, 1) : ℝ × ℝ × ℝ) := by
    rw [graphJetPath_apply]
    norm_num
  have houter := stateMapAnalytic
  rw [← hbase] at houter
  have hstate : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦
        stateMap (graphJetPath z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2)) (θ, 0) := by
    have hcomp := houter.comp
      (x := (θ, (0 : ℝ)))
      (f := fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦
        graphJetPath z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2) hpath
    simpa only [Function.comp_def] using hcomp
  have hscale : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦
        (stateMap (graphJetPath z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2)).1) (θ, 0) :=
    analyticAt_fst.comp hstate
  have hnextP : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦
        2 + z.1.1.1 *
            (stateMap (graphJetPath z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2)).1 ^ 3 +
          z.1.2.1 *
            (stateMap (graphJetPath z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2)).1 ^ 4)
        (θ, 0) := by
    fun_prop
  have hnextH : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦
        1 + z.1.1.2 *
            (stateMap (graphJetPath z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2)).1 ^ 3 +
          z.1.2.2 *
            (stateMap (graphJetPath z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2)).1 ^ 4)
        (θ, 0) := by
    fun_prop
  have hnext : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦
        graphJetPath z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2
          (stateMap (graphJetPath z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2)).1)
        (θ, 0) := by
    simpa only [graphJetPath_apply] using hscale.prod (hnextP.prod hnextH)
  have hstateP := analyticAt_fst.comp (analyticAt_snd.comp hstate)
  have hstateH := analyticAt_snd.comp (analyticAt_snd.comp hstate)
  have hnextP' := analyticAt_fst.comp (analyticAt_snd.comp hnext)
  have hnextH' := analyticAt_snd.comp (analyticAt_snd.comp hnext)
  have hassembled := (hstateP.sub hnextP').prod (hstateH.sub hnextH')
  apply hassembled.congr
  filter_upwards [] with z
  rfl

/-- Helper for Appendix Proposition A.5c (Weighted transverse shape jet): the
paired model-subtracted defect is jointly analytic at the zero-scale fiber. -/
private theorem weightedTransverseResidual_analyticAt
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    AnalyticAt ℝ (Function.uncurry weightedTransverseResidual) (θ, 0) := by
  have hθ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1) (θ, 0) :=
    analyticAt_fst
  have hθ₁ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ
  have hθ₂ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ
  have hP₃ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ₁
  have hH₃ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ₁
  have hP₄ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.2.1) (θ, 0) :=
    analyticAt_fst.comp hθ₂
  have hH₄ : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.1.2.2) (θ, 0) :=
    analyticAt_snd.comp hθ₂
  have hε : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦ z.2) (θ, 0) :=
    analyticAt_snd
  have hp : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦
        ((6 * z.1.1.2 - 10 * z.1.1.1 + 348) / 9) * z.2 ^ 3 +
          ((6 * z.1.2.2 - 10 * z.1.2.1 - 18) / 9) * z.2 ^ 4) (θ, 0) := by
    fun_prop
  have hh : AnalyticAt ℝ
      (fun z : ((ℝ × ℝ) × (ℝ × ℝ)) × ℝ ↦
        (8 - z.1.1.2) * z.2 ^ 3 - z.1.2.2 * z.2 ^ 4) (θ, 0) := by
    fun_prop
  have hpolynomial : AnalyticAt ℝ
      (Function.uncurry weightedTransversePolynomial) (θ, 0) := by
    apply (hp.prod hh).congr
    filter_upwards [] with z
    rfl
  have hsub := (weightedTransverseActual_analyticAt θ).sub hpolynomial
  apply hsub.congr
  filter_upwards [] with z
  rfl

/-- Helper for Appendix Proposition A.5c (Weighted transverse shape jet): the
paired model-subtracted transverse defect has zero finite Taylor jet through order four. -/
private theorem weightedTransverseResidual_zero_fourJet
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    FiniteTaylorJet.ofFunction ℝ 4 (weightedTransverseResidual θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4 (fun _ : ℝ ↦ ((0, 0) : ℝ × ℝ)) 0 := by
  have hsection : AnalyticAt ℝ
      (fun ε : ℝ ↦ (θ, ε)) (0 : ℝ) := by
    fun_prop
  have hactual : AnalyticAt ℝ (weightedTransverseActual θ) 0 := by
    have hcomp := (weightedTransverseActual_analyticAt θ).comp hsection
    simpa only [Function.comp_def, Function.uncurry_apply_pair] using hcomp
  have hpolynomial : AnalyticAt ℝ (weightedTransversePolynomial θ) 0 := by
    unfold weightedTransversePolynomial
    fun_prop
  have hactualP := analyticAt_fst.comp hactual
  have hactualH := analyticAt_snd.comp hactual
  have hpolynomialP := analyticAt_fst.comp hpolynomial
  have hpolynomialH := analyticAt_snd.comp hpolynomial
  have hpJet :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦ (weightedTransverseActual θ ε).1) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦ (weightedTransversePolynomial θ ε).1) 0 := by
    simpa only [weightedTransverseActual, weightedTransversePolynomial] using
      weightedTransversePDefectJet θ.1.1 θ.1.2 θ.2.1 θ.2.2
  have hhJet :
      FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦ (weightedTransverseActual θ ε).2) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun ε : ℝ ↦ (weightedTransversePolynomial θ ε).2) 0 := by
    simpa only [weightedTransverseActual, weightedTransversePolynomial] using
      weightedTransverseHDefectJet θ.1.1 θ.1.2 θ.2.1 θ.2.2
  have hpZero := FiniteTaylorJet.ofFunction_sub_eq_zero_of_eq
    hactualP.contDiffAt hpolynomialP.contDiffAt hpJet
  have hhZero := FiniteTaylorJet.ofFunction_sub_eq_zero_of_eq
    hactualH.contDiffAt hpolynomialH.contDiffAt hhJet
  have hpair := FiniteTaylorJet.ofFunction_prodMk_eq_zero
    (hactualP.sub hpolynomialP).contDiffAt
    (hactualH.sub hpolynomialH).contDiffAt hpZero hhZero
  have hresidual : weightedTransverseResidual θ = fun ε : ℝ ↦
      ((weightedTransverseActual θ ε).1 - (weightedTransversePolynomial θ ε).1,
        (weightedTransverseActual θ ε).2 -
          (weightedTransversePolynomial θ ε).2) := by
    funext ε
    apply Prod.ext
    · rfl
    · rfl
  rw [hresidual]
  exact hpair

/-- On every closed ball of graph coefficients with nonnegative radius, both
transverse graph-invariance defects have one joint uniform remainder of order five. -/
theorem weightedTransverseRemainder (B : ℝ) (hB : 0 ≤ B) :
    ∃ C > 0,
      Asymptotics.IsUniformRemainderOn
        (fun θ : (ℝ × ℝ) × (ℝ × ℝ) ↦ fun ε : ℝ ↦
          let x := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 ε
          let y := DFP.TwoLeg.stateMap x
          let nextGraph := DFP.TwoLeg.graphJetPath θ.1.1 θ.1.2 θ.2.1 θ.2.2 y.1
          (y.2.1 - nextGraph.2.1 -
              (((6 * θ.1.2 - 10 * θ.1.1 + 348) / 9) * ε ^ 3 +
                ((6 * θ.2.2 - 10 * θ.2.1 - 18) / 9) * ε ^ 4),
            y.2.2 - nextGraph.2.2 -
              ((8 - θ.1.2) * ε ^ 3 - θ.2.2 * ε ^ 4)))
        (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B) C 5 := by
  have hzeroInBall : (0 : (ℝ × ℝ) × (ℝ × ℝ)) ∈
      Metric.closedBall 0 B := by
    rw [Metric.mem_closedBall]
    simpa only [dist_self] using hB
  change ∃ C > 0,
    Asymptotics.IsUniformRemainderOn weightedTransverseResidual
      (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B) C 5
  have hsmooth : ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
      ContDiffAt ℝ 5 (Function.uncurry weightedTransverseResidual) (θ, 0) := by
    intro θ hθ
    exact (weightedTransverseResidual_analyticAt θ).contDiffAt
  have hzero : ∀ θ ∈ Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B,
      FiniteTaylorJet.ofFunction ℝ 4 (weightedTransverseResidual θ) 0 =
        FiniteTaylorJet.ofFunction ℝ 4
          (fun _ : ℝ ↦ ((0, 0) : ℝ × ℝ)) 0 := by
    intro θ hθ
    exact weightedTransverseResidual_zero_fourJet θ
  obtain ⟨C, hC, δ, hδ, hbound⟩ :=
    FiniteTaylorJet.uniform_orderFive_bound_of_zero_fourJet
      weightedTransverseResidual
      (Metric.closedBall (0 : (ℝ × ℝ) × (ℝ × ℝ)) B)
      (isCompact_closedBall _ _) hsmooth hzero
  refine ⟨C, hC, ?_⟩
  unfold Asymptotics.IsUniformRemainderOn
  refine ⟨δ, hδ, ?_⟩
  intro θ hθ ε hε
  have h := hbound θ hθ ε hε
  have hpow : |ε| ^ (5 : ℝ) = |ε| ^ (5 : ℕ) :=
    Real.rpow_natCast |ε| 5
  rw [hpow]
  exact h

end DFP.TwoLeg
