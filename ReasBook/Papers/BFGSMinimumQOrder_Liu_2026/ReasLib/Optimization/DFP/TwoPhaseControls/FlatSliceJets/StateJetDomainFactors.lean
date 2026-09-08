module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets
import all ReasLib.Optimization.DFP.TwoPhaseControls.StateMap
import all ReasLib.Optimization.DFP.TwoPhaseControls.FirstLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.SecondLeg
import all ReasLib.Optimization.DFP.TwoPhaseControls.GraphJet
import all ReasLib.LinearAlgebra.Matrix.RealSymmetric2
import ReasLib.Topology.MetricSpace.CompactUniformPositivity.Pointwise

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.SecondLeg

theorem domain_secondMetricTriple_analyticAt :
    AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ =>
        (outputMetric x.1 x.2.1 x.2.2 0 0,
          outputMetric x.1 x.2.1 x.2.2 0 1,
          outputMetric x.1 x.2.1 x.2.2 1 1))
      (0, 2, 1) := by
  have hall := DFP.FirstLeg.factorsAnalytic
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ => x.1) (0, 2, 1) :=
    analyticAt_fst
  have hspectral : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ =>
        DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2) (0, 2, 1) := by
    apply (analyticAt_fst.comp hall).congr
    filter_upwards [] with x
    rfl
  have hgradient : AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ =>
        DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2) (0, 2, 1) := by
    apply (analyticAt_fst.comp (analyticAt_snd.comp hall)).congr
    filter_upwards [] with x
    rfl
  have hL := analyticAt_fst.comp hspectral
  have hH := analyticAt_snd.comp hspectral
  have hQ := analyticAt_fst.comp hgradient
  have hU := analyticAt_snd.comp hgradient
  have hspectralBase :
      DFP.FirstLeg.spectralFactors 0 2 1 = (2, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg Prod.fst DFP.FirstLeg.factorsBase
  have hgradientBase :
      DFP.FirstLeg.gradientFactors 0 2 1 = (1, 1) := by
    simpa only [DFP.FirstLeg.factors] using
      congrArg (fun y => y.2.1) DFP.FirstLeg.factorsBase
  let εf : ℝ × ℝ × ℝ → ℝ := fun x => x.1
  let Lf : ℝ × ℝ × ℝ → ℝ := fun x =>
    (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).1
  let Hf : ℝ × ℝ × ℝ → ℝ := fun x =>
    (DFP.FirstLeg.spectralFactors x.1 x.2.1 x.2.2).2
  let Qf : ℝ × ℝ × ℝ → ℝ := fun x =>
    (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).1
  let Uf : ℝ × ℝ × ℝ → ℝ := fun x =>
    (DFP.FirstLeg.gradientFactors x.1 x.2.1 x.2.2).2
  let w₁ : ℝ × ℝ × ℝ → ℝ := fun x =>
    εf x * Lf x * Qf x - 2 * Hf x * Uf x
  let w₂ : ℝ × ℝ × ℝ → ℝ := fun x =>
    Hf x * Uf x - 2 * εf x ^ 3 * Lf x * Qf x
  let beta : ℝ × ℝ × ℝ → ℝ := fun x =>
    εf x ^ 3 * Lf x * Qf x * w₁ x + Hf x * Uf x * w₂ x
  let gamma : ℝ × ℝ × ℝ → ℝ := fun x =>
    εf x ^ 6 * Lf x * w₁ x ^ 2 + Hf x * w₂ x ^ 2
  have hεf : AnalyticAt ℝ εf (0, 2, 1) := hε
  have hLf : AnalyticAt ℝ Lf (0, 2, 1) := hL
  have hHf : AnalyticAt ℝ Hf (0, 2, 1) := hH
  have hQf : AnalyticAt ℝ Qf (0, 2, 1) := hQ
  have hUf : AnalyticAt ℝ Uf (0, 2, 1) := hU
  have hw₁ : AnalyticAt ℝ w₁ (0, 2, 1) := by
    dsimp [w₁]
    fun_prop
  have hw₂ : AnalyticAt ℝ w₂ (0, 2, 1) := by
    dsimp [w₂]
    fun_prop
  have hbeta : AnalyticAt ℝ beta (0, 2, 1) := by
    dsimp [beta]
    fun_prop
  have hgamma : AnalyticAt ℝ gamma (0, 2, 1) := by
    dsimp [gamma]
    fun_prop
  have hbeta_ne : beta (0, 2, 1) ≠ 0 := by
    norm_num [beta, w₁, w₂, εf, Lf, Hf, Qf, Uf,
      hspectralBase, hgradientBase]
  have hgamma_ne : gamma (0, 2, 1) ≠ 0 := by
    norm_num [gamma, w₁, w₂, εf, Lf, Hf, Qf, Uf,
      hspectralBase, hgradientBase]
  let a : ℝ × ℝ × ℝ → ℝ := fun x =>
    Lf x - εf x ^ 6 * Lf x ^ 2 * w₁ x ^ 2 / gamma x +
      Lf x ^ 2 * Qf x ^ 2 / beta x
  let b : ℝ × ℝ × ℝ → ℝ := fun x =>
    -(εf x ^ 3 * Lf x * Hf x * w₁ x * w₂ x / gamma x) +
      Lf x * Qf x * Hf x * Uf x / beta x
  let d : ℝ × ℝ × ℝ → ℝ := fun x =>
    Hf x - Hf x ^ 2 * w₂ x ^ 2 / gamma x +
      Hf x ^ 2 * Uf x ^ 2 / beta x
  have ha : AnalyticAt ℝ a (0, 2, 1) := by
    dsimp [a]
    fun_prop
  have hb : AnalyticAt ℝ b (0, 2, 1) := by
    dsimp [b]
    fun_prop
  have hd : AnalyticAt ℝ d (0, 2, 1) := by
    dsimp [d]
    fun_prop
  have htriple :=
    ((hε.pow 4).mul ha).prod (((hε.pow 2).mul hb).prod hd)
  apply htriple.congr
  filter_upwards [] with x
  rfl

end DFP.SecondLeg

namespace DFP.TwoLeg.StateJet

abbrev DomainGraphCoeffs := (ℝ × ℝ) × (ℝ × ℝ)

def domainJointPath (z : DomainGraphCoeffs × ℝ) : ℝ × ℝ × ℝ :=
  DFP.TwoLeg.graphJetPath
    z.1.1.1 z.1.1.2 z.1.2.1 z.1.2.2 z.2

theorem domainJointPath_analyticAt (θ : DomainGraphCoeffs) :
    AnalyticAt ℝ domainJointPath (θ, 0) := by
  have hθ : AnalyticAt ℝ (fun z : DomainGraphCoeffs × ℝ => z.1) (θ, 0) :=
    analyticAt_fst
  have hθ₁ : AnalyticAt ℝ (fun z : DomainGraphCoeffs × ℝ => z.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ
  have hθ₂ : AnalyticAt ℝ (fun z : DomainGraphCoeffs × ℝ => z.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ
  have hP₃ : AnalyticAt ℝ (fun z : DomainGraphCoeffs × ℝ => z.1.1.1) (θ, 0) :=
    analyticAt_fst.comp hθ₁
  have hH₃ : AnalyticAt ℝ (fun z : DomainGraphCoeffs × ℝ => z.1.1.2) (θ, 0) :=
    analyticAt_snd.comp hθ₁
  have hP₄ : AnalyticAt ℝ (fun z : DomainGraphCoeffs × ℝ => z.1.2.1) (θ, 0) :=
    analyticAt_fst.comp hθ₂
  have hH₄ : AnalyticAt ℝ (fun z : DomainGraphCoeffs × ℝ => z.1.2.2) (θ, 0) :=
    analyticAt_snd.comp hθ₂
  have hε : AnalyticAt ℝ (fun z : DomainGraphCoeffs × ℝ => z.2) (θ, 0) :=
    analyticAt_snd
  have htwo :
      AnalyticAt ℝ (fun _ : DomainGraphCoeffs × ℝ => (2 : ℝ)) (θ, 0) :=
    analyticAt_const
  have hone :
      AnalyticAt ℝ (fun _ : DomainGraphCoeffs × ℝ => (1 : ℝ)) (θ, 0) :=
    analyticAt_const
  have hp : AnalyticAt ℝ
      (fun z : DomainGraphCoeffs × ℝ =>
        2 + z.1.1.1 * z.2 ^ 3 + z.1.2.1 * z.2 ^ 4) (θ, 0) :=
    (htwo.add (hP₃.mul (hε.pow 3))).add (hP₄.mul (hε.pow 4))
  have hh : AnalyticAt ℝ
      (fun z : DomainGraphCoeffs × ℝ =>
        1 + z.1.1.2 * z.2 ^ 3 + z.1.2.2 * z.2 ^ 4) (θ, 0) :=
    (hone.add (hH₃.mul (hε.pow 3))).add (hH₄.mul (hε.pow 4))
  apply (hε.prod (hp.prod hh)).congr
  filter_upwards [] with z
  rfl

theorem domainJointPath_base (θ : DomainGraphCoeffs) :
    domainJointPath (θ, 0) = ((0, 2, 1) : ℝ × ℝ × ℝ) := by
  simp [domainJointPath, DFP.TwoLeg.graphJetPath]

theorem domain_firstMetricTriple_analyticAt :
    AnalyticAt ℝ
      (fun x : ℝ × ℝ × ℝ =>
        (DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 0,
          DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 0 1,
          DFP.FirstLeg.outputMetric x.1 x.2.1 x.2.2 1 1))
      (0, 2, 1) := by
  have hε : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ => x.1) (0, 2, 1) :=
    analyticAt_fst
  have hp : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ => x.2.1) (0, 2, 1) :=
    analyticAt_fst.comp analyticAt_snd
  have hh : AnalyticAt ℝ (fun x : ℝ × ℝ × ℝ => x.2.2) (0, 2, 1) :=
    analyticAt_snd.comp analyticAt_snd
  unfold DFP.FirstLeg.outputMetric
  dsimp
  fun_prop (disch := norm_num) [Prod.fst, Prod.snd]

theorem domain_high_continuous :
    Continuous (fun x : ℝ × ℝ × ℝ =>
      RealSymmetric2.high x.1 x.2.1 x.2.2) := by
  unfold RealSymmetric2.high RealSymmetric2.gap
  fun_prop

theorem domain_lowDenom_continuous :
    Continuous (fun x : ℝ × ℝ × ℝ =>
      RealSymmetric2.lowDenom x.1 x.2.1 x.2.2) := by
  unfold RealSymmetric2.lowDenom RealSymmetric2.low RealSymmetric2.gap
  fun_prop


theorem domainFactors_continuousAt
    (θ : DomainGraphCoeffs) (i : Fin 13) :
    ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ => domainFactors z.1 z.2 i)
      (θ, 0) := by
  have hpath := domainJointPath_analyticAt θ
  have hpathBase := domainJointPath_base θ
  have hfirst :
      AnalyticAt ℝ
        (fun z : DomainGraphCoeffs × ℝ =>
          DFP.FirstLeg.factors
            (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2)
        (θ, 0) := by
    have houter := DFP.FirstLeg.factorsAnalytic
    rw [← hpathBase] at houter
    simpa only [Function.comp_def] using houter.comp hpath
  have hsecond :
      AnalyticAt ℝ
        (fun z : DomainGraphCoeffs × ℝ =>
          DFP.SecondLeg.factors
            (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2)
        (θ, 0) := by
    have houter := DFP.SecondLeg.factorsAnalytic
    rw [← hpathBase] at houter
    simpa only [Function.comp_def] using houter.comp hpath
  have hmetric₁ :
      AnalyticAt ℝ
        (fun z : DomainGraphCoeffs × ℝ =>
          (DFP.FirstLeg.outputMetric
              (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2 0 0,
            DFP.FirstLeg.outputMetric
              (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2 0 1,
            DFP.FirstLeg.outputMetric
              (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2 1 1))
        (θ, 0) := by
    have houter := domain_firstMetricTriple_analyticAt
    rw [← hpathBase] at houter
    simpa only [Function.comp_def] using houter.comp hpath
  have hmetric₂ :
      AnalyticAt ℝ
        (fun z : DomainGraphCoeffs × ℝ =>
          (DFP.SecondLeg.outputMetric
              (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2 0 0,
            DFP.SecondLeg.outputMetric
              (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2 0 1,
            DFP.SecondLeg.outputMetric
              (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2 1 1))
        (θ, 0) := by
    have houter := DFP.SecondLeg.domain_secondMetricTriple_analyticAt
    rw [← hpathBase] at houter
    simpa only [Function.comp_def] using houter.comp hpath
  have hradius :
      AnalyticAt ℝ
        (fun z : DomainGraphCoeffs × ℝ =>
          DFP.TwoLeg.radiusFactor
            (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2)
        (θ, 0) := by
    have houter := DFP.TwoLeg.analyticAt_radiusFactor
    rw [← hpathBase] at houter
    simpa only [Function.comp_def] using houter.comp hpath
  have hspectral₁ :
      AnalyticAt ℝ
        (fun z : DomainGraphCoeffs × ℝ =>
          DFP.FirstLeg.spectralFactors
            (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2)
        (θ, 0) := by
    apply (analyticAt_fst.comp hfirst).congr
    filter_upwards [] with z
    rfl
  have hgradient₁ :
      AnalyticAt ℝ
        (fun z : DomainGraphCoeffs × ℝ =>
          DFP.FirstLeg.gradientFactors
            (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2)
        (θ, 0) := by
    apply (analyticAt_fst.comp (analyticAt_snd.comp hfirst)).congr
    filter_upwards [] with z
    rfl
  have hspectral₂ :
      AnalyticAt ℝ
        (fun z : DomainGraphCoeffs × ℝ =>
          DFP.SecondLeg.spectralFactors
            (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2)
        (θ, 0) := by
    apply (analyticAt_fst.comp hsecond).congr
    filter_upwards [] with z
    rfl
  have hgradient₂ :
      AnalyticAt ℝ
        (fun z : DomainGraphCoeffs × ℝ =>
          DFP.SecondLeg.gradientFactors
            (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2)
        (θ, 0) := by
    apply (analyticAt_fst.comp (analyticAt_snd.comp hsecond)).congr
    filter_upwards [] with z
    rfl
  have hL₁ : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        (DFP.FirstLeg.spectralFactors
          (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1) (θ, 0) :=
    (analyticAt_fst.comp hspectral₁).continuousAt
  have hH₁ : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        (DFP.FirstLeg.spectralFactors
          (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2) (θ, 0) :=
    (analyticAt_snd.comp hspectral₁).continuousAt
  have hQ₁ : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        (DFP.FirstLeg.gradientFactors
          (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1) (θ, 0) :=
    (analyticAt_fst.comp hgradient₁).continuousAt
  have hU₁ : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        (DFP.FirstLeg.gradientFactors
          (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2) (θ, 0) :=
    (analyticAt_snd.comp hgradient₁).continuousAt
  have hL₂ : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        (DFP.SecondLeg.spectralFactors
          (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1) (θ, 0) :=
    (analyticAt_fst.comp hspectral₂).continuousAt
  have hH₂ : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        (DFP.SecondLeg.spectralFactors
          (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2) (θ, 0) :=
    (analyticAt_snd.comp hspectral₂).continuousAt
  have hQ₂ : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        (DFP.SecondLeg.gradientFactors
          (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1) (θ, 0) :=
    (analyticAt_fst.comp hgradient₂).continuousAt
  have hU₂ : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        (DFP.SecondLeg.gradientFactors
          (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2) (θ, 0) :=
    (analyticAt_snd.comp hgradient₂).continuousAt
  have hε : ContinuousAt (fun z : DomainGraphCoeffs × ℝ => z.2) (θ, 0) :=
    continuousAt_snd
  have htwo : ContinuousAt
      (fun _ : DomainGraphCoeffs × ℝ => (2 : ℝ)) (θ, 0) :=
    continuousAt_const
  have hw₁ : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        z.2 *
              (DFP.FirstLeg.spectralFactors
                (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 *
            (DFP.FirstLeg.gradientFactors
                (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 -
          2 *
              (DFP.FirstLeg.spectralFactors
                (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 *
            (DFP.FirstLeg.gradientFactors
                (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2)
      (θ, 0) :=
    ((hε.mul hL₁).mul hQ₁).sub ((htwo.mul hH₁).mul hU₁)
  have hw₂ : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        (DFP.FirstLeg.spectralFactors
              (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 *
            (DFP.FirstLeg.gradientFactors
              (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 -
          2 * z.2 ^ 3 *
              (DFP.FirstLeg.spectralFactors
                (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 *
            (DFP.FirstLeg.gradientFactors
                (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1)
      (θ, 0) :=
    (hH₁.mul hU₁).sub ((((htwo.mul (hε.pow 3)).mul hL₁).mul hQ₁))
  have hbeta : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        z.2 ^ 3 *
                (DFP.FirstLeg.spectralFactors
                  (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 *
              (DFP.FirstLeg.gradientFactors
                  (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 *
            (z.2 *
                  (DFP.FirstLeg.spectralFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 *
                (DFP.FirstLeg.gradientFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 -
              2 *
                  (DFP.FirstLeg.spectralFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 *
                (DFP.FirstLeg.gradientFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2) +
          (DFP.FirstLeg.spectralFactors
                (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 *
              (DFP.FirstLeg.gradientFactors
                (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 *
            ((DFP.FirstLeg.spectralFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 *
                  (DFP.FirstLeg.gradientFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 -
              2 * z.2 ^ 3 *
                  (DFP.FirstLeg.spectralFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 *
                (DFP.FirstLeg.gradientFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1))
      (θ, 0) :=
    ((((hε.pow 3).mul hL₁).mul hQ₁).mul hw₁).add
      (((hH₁.mul hU₁).mul hw₂))
  have hgamma : ContinuousAt
      (fun z : DomainGraphCoeffs × ℝ =>
        z.2 ^ 6 *
              (DFP.FirstLeg.spectralFactors
                (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 *
            (z.2 *
                  (DFP.FirstLeg.spectralFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 *
                (DFP.FirstLeg.gradientFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 -
              2 *
                  (DFP.FirstLeg.spectralFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 *
                (DFP.FirstLeg.gradientFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2) ^ 2 +
          (DFP.FirstLeg.spectralFactors
                (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 *
            ((DFP.FirstLeg.spectralFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 *
                  (DFP.FirstLeg.gradientFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).2 -
              2 * z.2 ^ 3 *
                  (DFP.FirstLeg.spectralFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1 *
                (DFP.FirstLeg.gradientFactors
                    (domainJointPath z).1 (domainJointPath z).2.1 (domainJointPath z).2.2).1) ^ 2)
      (θ, 0) :=
    (((hε.pow 6).mul hL₁).mul (hw₁.pow 2)).add
      (hH₁.mul (hw₂.pow 2))
  fin_cases i <;>
    simp only [domainFactors, DFP.TwoLeg.graphJetPath] <;>
    dsimp [domainJointPath]
  · fun_prop
  · fun_prop
  · simpa only [Function.comp_def, domainJointPath, DFP.TwoLeg.graphJetPath] using
      domain_high_continuous.continuousAt.comp hmetric₁.continuousAt
  · simpa only [Function.comp_def, domainJointPath, DFP.TwoLeg.graphJetPath] using
      domain_lowDenom_continuous.continuousAt.comp hmetric₁.continuousAt
  · fun_prop
  · fun_prop
  · simpa only [Function.comp_def, domainJointPath, DFP.TwoLeg.graphJetPath] using hbeta
  · simpa only [Function.comp_def, domainJointPath, DFP.TwoLeg.graphJetPath] using hgamma
  · simpa only [Function.comp_def, domainJointPath, DFP.TwoLeg.graphJetPath] using
      domain_high_continuous.continuousAt.comp hmetric₂.continuousAt
  · simpa only [Function.comp_def, domainJointPath, DFP.TwoLeg.graphJetPath] using
      domain_lowDenom_continuous.continuousAt.comp hmetric₂.continuousAt
  · fun_prop
  · fun_prop
  · simpa only [Function.comp_def, domainJointPath,
      DFP.TwoLeg.graphJetPath] using hradius.continuousAt

theorem domainFactors_pos_zero
    (θ : DomainGraphCoeffs) (i : Fin 13) :
    0 < domainFactors θ 0 i := by
  fin_cases i <;>
    norm_num [domainFactors, DFP.TwoLeg.graphJetPath,
      DFP.FirstLeg.outputMetric, DFP.FirstLeg.spectralFactors,
      DFP.FirstLeg.gradientFactors, DFP.SecondLeg.outputMetric,
      DFP.SecondLeg.spectralFactors, DFP.SecondLeg.gradientFactors,
      DFP.TwoLeg.radiusFactor, DFP.SecondLeg.canonicalFactors,
      RealSymmetric2.low, RealSymmetric2.high, RealSymmetric2.gap,
      RealSymmetric2.lowDenom]

theorem domainFactors_uniform_lower_bound
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ m > 0, ∃ δ > 0,
      ∀ θ ∈ Metric.closedBall (0 : DomainGraphCoeffs) B,
        ∀ i : Fin 13, ∀ ε : ℝ, |ε| < δ →
          m ≤ domainFactors θ ε i := by
  let K : Set DomainGraphCoeffs := Metric.closedBall 0 B
  letI : CompactSpace K := by
    apply isCompact_iff_compactSpace.mp
    dsimp only [K]
    exact isCompact_closedBall _ _
  have hneK : Nonempty K := by
    have hzero : (0 : DomainGraphCoeffs) ∈ Metric.closedBall 0 B := by
      rw [Metric.mem_closedBall]
      simpa only [dist_self] using hB
    exact ⟨⟨0, by simpa only [K] using hzero⟩⟩
  have hcontinuous : ∀ θ : K, ∀ i : Fin 13,
      ContinuousAt
        (fun p : ℝ × K => domainFactors p.2.1 p.1 i)
        (0, θ) := by
    intro θ i
    have hmap : ContinuousAt
        (fun p : ℝ × K => ((p.2.1, p.1) : DomainGraphCoeffs × ℝ))
        (0, θ) := by
      fun_prop
    have hcomp := ContinuousAt.comp
      (f := fun p : ℝ × K => ((p.2.1, p.1) : DomainGraphCoeffs × ℝ))
      (g := fun z : DomainGraphCoeffs × ℝ => domainFactors z.1 z.2 i)
      (x := ((0, θ) : ℝ × K))
      (domainFactors_continuousAt θ.1 i)
      hmap
    simpa only [Function.comp_def] using hcomp
  have hpositive : ∀ θ : K, ∀ i : Fin 13,
      0 < domainFactors θ.1 0 i := by
    intro θ i
    exact domainFactors_pos_zero θ.1 i
  obtain ⟨m, hm, δ, hδ, hbound⟩ :=
    CompactUniformPositivity.exists_uniform_lower_bound_finite_of_pointwise_continuousAt
      (fun ε (θ : K) (i : Fin 13) => domainFactors θ.1 ε i)
      hcontinuous hneK (inferInstance : Nonempty (Fin 13)) hpositive
  refine ⟨m, hm, δ, hδ, ?_⟩
  intro θ hθ i ε hε
  let θK : K := ⟨θ, by simpa only [K] using hθ⟩
  exact hbound θK i ε hε

end DFP.TwoLeg.StateJet

