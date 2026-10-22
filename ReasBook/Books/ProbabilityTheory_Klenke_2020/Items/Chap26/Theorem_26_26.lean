/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.GeneralizedStrongSolutionAPI
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_8.StrongMarkovAtStart
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.Coefficients
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.Evaluation
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.Growth

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.AnalyticFrontiers

open MeasureTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {n m : ℕ}


/-- Helper for Theorem 26.26: the zero-time slice hypotheses package the local martingale
problem coefficients into the Chapter 26 time-independence predicate. -/
private theorem stroockVaradhan_timeIndependentLocalMartingaleProblemCoefficients
    (a : StroockVaradhanDiffusionMatrixCoeff n)
    (b : StroockVaradhanDriftCoeff n)
    (ha_time : ∀ t x i j, a t x i j = a 0 x i j)
    (hb_time : ∀ t x i, b t x i = b 0 x i) :
    TimeIndependentLocalMartingaleProblemCoefficients a b := by
  constructor
  · intro t₁ t₂ x
    funext i
    funext j
    rw [ha_time t₁ x i j, ha_time t₂ x i j]
  · intro t₁ t₂ x
    funext i
    rw [hb_time t₁ x i, hb_time t₂ x i]

/-- Helper for Theorem 26.26: deterministic-time evaluation against a path law is exactly
integration against the pushed-forward deterministic-time marginal. -/
private theorem stroockVaradhan_integral_eval_eq_integral_timeMarginal_support
    (μ : Measure (StroockVaradhanPathSpace n))
    (t : NNReal)
    {f : StroockVaradhanState n → ℝ}
    (hf : Measurable f) :
    ∫ γ, f (γ t) ∂μ =
      ∫ y, f y ∂ μ.map (ContinuousMap.evalCLM ℝ t) := by
  symm
  simpa using
    (MeasureTheory.integral_map
      ((measurable_path_eval (n := n) t).aemeasurable)
      hf.aestronglyMeasurable :
        ∫ y, f y ∂ μ.map (ContinuousMap.evalCLM ℝ t) =
          ∫ γ, f ((ContinuousMap.evalCLM ℝ t) γ) ∂μ)

/-- Helper for Theorem 26.26: deterministic-time marginal expectations along a path-law family are
the same row as the corresponding path-integral expectations. -/
private theorem stroockVaradhan_transitionExpectationRow_eq_pathIntegralRow_support
    (P : StroockVaradhanState n → ProbabilityMeasure (StroockVaradhanPathSpace n))
    (t : NNReal)
    {f : StroockVaradhanState n → ℝ}
    (hf : Measurable f) :
    (fun x : StroockVaradhanState n ↦
      ∫ y, f y ∂
        (P x : Measure (StroockVaradhanPathSpace n)).map
          (ContinuousMap.evalCLM ℝ t)) =
      fun x : StroockVaradhanState n ↦
        ∫ γ, f (γ t) ∂ (P x : Measure (StroockVaradhanPathSpace n)) := by
  funext x
  symm
  exact
    stroockVaradhan_integral_eval_eq_integral_timeMarginal_support
      (n := n)
      (μ := (P x : Measure (StroockVaradhanPathSpace n)))
      t
      hf

/-- Helper for Theorem 26.26: on a time-homogeneous Markov path-law family, the deterministic-time
marginal equals the corresponding transition-kernel row. -/
private theorem stroockVaradhan_canonicalTimeMarginal_eq_transitionKernel_support
    (Pref : StroockVaradhanState n → ProbabilityMeasure (StroockVaradhanPathSpace n))
    (κ : Kernel (StroockVaradhanState n) (NNReal → StroockVaradhanState n))
    (hMarkov :
      IsTimeHomogeneousMarkovProcess
        (fun t ↦
          (ContinuousMap.evalCLM ℝ t :
            StroockVaradhanPathSpace n → StroockVaradhanState n))
        Pref
        κ)
    (x : StroockVaradhanState n)
    (t : NNReal) :
    (Pref x : Measure (StroockVaradhanPathSpace n)).map (ContinuousMap.evalCLM ℝ t) =
      transitionKernel κ t x := by
  letI :
      IsTimeHomogeneousMarkovProcess
        (fun t ↦
          (ContinuousMap.evalCLM ℝ t :
            StroockVaradhanPathSpace n → StroockVaradhanState n))
        Pref
        κ := hMarkov
  simpa using
    (IsTimeHomogeneousMarkovProcess.timeMarginal_eq_transitionKernel
      (X := fun t ↦
        (ContinuousMap.evalCLM ℝ t :
          StroockVaradhanPathSpace n → StroockVaradhanState n))
      (P := Pref)
      (κ := κ)
      x
      t)

/-- Helper for Theorem 26.26: on the extracted Markov family, the transition-kernel expectation
row is exactly the deterministic-time path-integral row. -/
private theorem stroockVaradhan_transitionKernelExpectationRow_eq_canonicalPathIntegralRow_support
    (Pref : StroockVaradhanState n → ProbabilityMeasure (StroockVaradhanPathSpace n))
    (κ : Kernel (StroockVaradhanState n) (NNReal → StroockVaradhanState n))
    (hMarkov :
      IsTimeHomogeneousMarkovProcess
        (fun t ↦
          (ContinuousMap.evalCLM ℝ t :
            StroockVaradhanPathSpace n → StroockVaradhanState n))
        Pref
        κ)
    (t : NNReal)
    {f : StroockVaradhanState n → ℝ}
    (hf : Measurable f) :
    (fun x : StroockVaradhanState n ↦
      ∫ y, f y ∂ transitionKernel κ t x) =
        fun x : StroockVaradhanState n ↦
          ∫ γ, f (γ t) ∂ (Pref x : Measure (StroockVaradhanPathSpace n)) := by
  funext x
  rw [←
    stroockVaradhan_canonicalTimeMarginal_eq_transitionKernel_support
      (n := n)
      Pref
      κ
      hMarkov
      x
      t]
  exact
    congrFun
      (stroockVaradhan_transitionExpectationRow_eq_pathIntegralRow_support
        (n := n)
        Pref
        t
        hf)
      x

/-- Helper for Theorem 26.26: continuity of the transition-kernel expectation row transports
directly to continuity of the corresponding path-integral row on the same Markov family. -/
private theorem stroockVaradhan_referencePathIntegralContinuousFrontierSupport
    (Pref : StroockVaradhanState n → ProbabilityMeasure (StroockVaradhanPathSpace n))
    (κ : Kernel (StroockVaradhanState n) (NNReal → StroockVaradhanState n))
    (hMarkov :
      IsTimeHomogeneousMarkovProcess
        (fun t ↦
          (ContinuousMap.evalCLM ℝ t :
            StroockVaradhanPathSpace n → StroockVaradhanState n))
        Pref
        κ)
    (t : NNReal)
    (f : StroockVaradhanState n → ℝ)
    (hf : Measurable f)
    (hKernelCont :
      Continuous (fun x : StroockVaradhanState n ↦
        ∫ y, f y ∂ transitionKernel κ t x)) :
    Continuous (fun x : StroockVaradhanState n ↦
      ∫ γ, f (γ t) ∂ (Pref x : Measure (StroockVaradhanPathSpace n))) := by
  have hRewrite :=
    stroockVaradhan_transitionKernelExpectationRow_eq_canonicalPathIntegralRow_support
      (n := n)
      Pref
      κ
      hMarkov
      t
      hf
  simpa [hRewrite] using hKernelCont

/-- Helper for Theorem 26.26: well-posedness identifies any canonical path-law family with the
reference canonical family rowwise. -/
private theorem stroockVaradhan_pathLaw_eq_reference
    {a : StroockVaradhanDiffusionMatrixCoeff n}
    {b : StroockVaradhanDriftCoeff n}
    {Pref P : StroockVaradhanState n → ProbabilityMeasure (StroockVaradhanPathSpace n)}
    (hPref :
      ∀ x : StroockVaradhanState n,
        IsLocalMartingaleProblemSolution
          (Measure.dirac x)
          a
          b
          (canonicalCoordinateFiltration (n := n))
          (Pref x : Measure (StroockVaradhanPathSpace n))
          id)
    (hP :
      ∀ x : StroockVaradhanState n,
        IsLocalMartingaleProblemSolution
          (Measure.dirac x)
          a
          b
          (canonicalCoordinateFiltration (n := n))
          (P x : Measure (StroockVaradhanPathSpace n))
          id)
    (hWellPosed : LocalMartingaleProblemWellPosed.{0, 0} a b) :
    ∀ x : StroockVaradhanState n,
      (P x : Measure (StroockVaradhanPathSpace n)) =
        (Pref x : Measure (StroockVaradhanPathSpace n)) := by
  intro x
  have hUniqueLaw :
      LocalMartingaleProblemHasUniqueLaw.{0, 0} (Measure.dirac x) a b :=
    (localMartingaleProblemWellPosed_iff.mp hWellPosed x).2
  simpa using
    hUniqueLaw
      (ℱ := canonicalCoordinateFiltration (n := n))
      (μ := (P x : Measure (StroockVaradhanPathSpace n)))
      (X := id)
      (ℱ' := canonicalCoordinateFiltration (n := n))
      (μ' := (Pref x : Measure (StroockVaradhanPathSpace n)))
      (X' := id)
      (hP x)
      (hPref x)

/-- Helper for Theorem 26.26: an a.e.-measurable path-valued random variable has a.e.-measurable
deterministic-time evaluations. -/
private theorem stroockVaradhan_aemeasurable_stateEval_of_aemeasurable_path
    {Ω : Type _} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → StroockVaradhanPathSpace n}
    (hX : AEMeasurable X μ) (T : NNReal) :
    AEMeasurable (fun ω ↦ X ω T) μ := by
  -- Proof comment: fixed-time evaluation is measurable on continuous path space, so composing it
  -- with an a.e.-measurable path map preserves a.e. measurability.
  exact (measurable_path_eval (n := n) T).aemeasurable.comp_aemeasurable hX

/-- Helper for Theorem 26.26: unique path law for Dirac-start local-martingale solutions forces
equality of the deterministic-time marginals after pushing both path laws forward by evaluation. -/
private theorem stroockVaradhan_timeMarginal_eq_of_diracUniqueLaw
    {a : StroockVaradhanDiffusionMatrixCoeff n}
    {b : StroockVaradhanDriftCoeff n}
    {x : StroockVaradhanState n}
    {Ω : Type u} [MeasurableSpace Ω]
    (ℱ : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (μ : Measure Ω)
    (X : Ω → StroockVaradhanPathSpace n)
    {Ω' : Type v} [MeasurableSpace Ω']
    (ℱ' : Filtration NNReal (inferInstance : MeasurableSpace Ω'))
    (μ' : Measure Ω')
    (X' : Ω' → StroockVaradhanPathSpace n)
    (hUniqueLaw : LocalMartingaleProblemHasUniqueLaw.{u, v} (Measure.dirac x) a b)
    (hX : IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ μ X)
    (hX' : IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ' μ' X')
    (T : NNReal) :
    μ.map (fun ω ↦ X ω T) = μ'.map (fun ω ↦ X' ω T) := by
  let evalT : StroockVaradhanPathSpace n → StroockVaradhanState n :=
    ContinuousMap.evalCLM ℝ T
  have hLaw : μ.map X = μ'.map X' := hUniqueLaw ℱ μ X ℱ' μ' X' hX hX'
  have hEvalT : Measurable evalT := measurable_path_eval (n := n) T
  calc
    μ.map (fun ω ↦ X ω T) = (μ.map X).map evalT := by
      -- Proof comment: collapse the realization-space time marginal into a single pushforward of
      -- the path law along deterministic-time evaluation.
      rw [AEMeasurable.map_map_of_aemeasurable
        hEvalT.aemeasurable hX.aemeasurable_path]
      rfl
    _ = (μ'.map X').map evalT := by
      -- Proof comment: unique law identifies the two path laws, so their evaluated marginals
      -- coincide after applying the same deterministic-time evaluation map.
      exact congrArg (fun ν : Measure (StroockVaradhanPathSpace n) ↦ ν.map evalT) hLaw
    _ = μ'.map (fun ω ↦ X' ω T) := by
      -- Proof comment: rewrite the second evaluated path law back to the original realization
      -- space so the final equality has the deterministic-time-marginal shape required by
      -- `HasDeterministicTimeMarginalUniqueness`.
      rw [AEMeasurable.map_map_of_aemeasurable
        hEvalT.aemeasurable hX'.aemeasurable_path]
      rfl

/-- Helper for Theorem 26.26: once deterministic-start existence and deterministic-time marginal
unique law are bundled in the support frontier, the target file only needs a thin projection
wrapper. -/
private theorem stroockVaradhan_diracLocalMartingaleProblemDataSupport
    (a : StroockVaradhanDiffusionMatrixCoeff n)
    (b : StroockVaradhanDriftCoeff n)
    (hTimeIndependent : TimeIndependentLocalMartingaleProblemCoefficients a b)
    (ha_cont : ∀ i j : Fin n, Continuous (fun x : StroockVaradhanState n ↦ a 0 x i j))
    (hb_meas : ∀ i : Fin n, Measurable (fun x : StroockVaradhanState n ↦ b 0 x i))
    (ha_symm : ∀ x : StroockVaradhanState n, ∀ i j : Fin n, a 0 x i j = a 0 x j i)
    (ha_pos :
      ∀ x v : StroockVaradhanState n, v ≠ 0 →
        0 < ∑ i, v i * ∑ j, a 0 x i j * v j)
    (hgrowth : StroockVaradhanGrowthCondition a b) :
    ∀ x : StroockVaradhanState n,
      (∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
        (P : ProbabilityMeasure Ω) (X : Ω → StroockVaradhanPathSpace n),
        IsLocalMartingaleProblemSolution
          (Measure.dirac x)
          a
          b
          ℱ
          (P : Measure Ω)
          X) ∧
        LocalMartingaleProblemHasUniqueLaw.{u, v}
          (Measure.dirac x)
          a
          b := by
  -- Route correction: the earlier split into separate existence and marginal-uniqueness frontiers
  -- duplicated clause-(1). The canonical owner is the bundled support theorem imported above.
  -- Proof comment: this wrapper simply exposes the support-file frontier on the exact local
  -- theorem surface used by the public clause-(1) and clause-(4) statements.
  simpa using
    ProbabilityTheory.stroockVaradhan_diracLocalMartingaleProblemDataFrontier.{u, v}
      (n := n)
      a
      b
      hTimeIndependent
      ha_cont
      hb_meas
      ha_symm
      ha_pos
      hgrowth

/-- Helper for Theorem 26.26: uniqueness in law for Dirac-start solutions implies deterministic-time
marginal uniqueness by pushing path laws forward along deterministic-time evaluation. -/
private theorem stroockVaradhan_diracDeterministicTimeMarginalUniqueness
    (a : StroockVaradhanDiffusionMatrixCoeff n)
    (b : StroockVaradhanDriftCoeff n)
    (ha_time : ∀ t x i j, a t x i j = a 0 x i j)
    (hb_time : ∀ t x i, b t x i = b 0 x i)
    (ha_cont : ∀ i j : Fin n, Continuous (fun x : StroockVaradhanState n ↦ a 0 x i j))
    (hb_meas : ∀ i : Fin n, Measurable (fun x : StroockVaradhanState n ↦ b 0 x i))
    (ha_symm : ∀ x : StroockVaradhanState n, ∀ i j : Fin n, a 0 x i j = a 0 x j i)
    (ha_pos :
      ∀ x v : StroockVaradhanState n, v ≠ 0 →
        0 < ∑ i, v i * ∑ j, a 0 x i j * v j)
    (hgrowth : StroockVaradhanGrowthCondition a b) :
    HasDeterministicTimeMarginalUniqueness.{u, v} a b := by
  let hTimeIndependent :=
    stroockVaradhan_timeIndependentLocalMartingaleProblemCoefficients
      a
      b
      ha_time
      hb_time
  -- Proof comment: deterministic-time uniqueness is now a direct transport of the bundled
  -- unique-law output from the support frontier along deterministic-time evaluation.
  intro x Ω _ ℱ μ X Ω' _ ℱ' μ' X' hX hX'
  have hUniqueLaw :
      LocalMartingaleProblemHasUniqueLaw.{u, v} (Measure.dirac x) a b :=
    (stroockVaradhan_diracLocalMartingaleProblemDataSupport.{u, v}
      (n := n)
      a
      b
      hTimeIndependent
      ha_cont
      hb_meas
      ha_symm
      ha_pos
      hgrowth
      x).2
  intro T
  -- Proof comment: feed the frontier's unique path law directly into the local pushforward
  -- transport lemma to recover the required deterministic-time marginal equality.
  exact
    stroockVaradhan_timeMarginal_eq_of_diracUniqueLaw
      (n := n)
      ℱ
      μ
      X
      ℱ'
      μ'
      X'
      hUniqueLaw
      hX
      hX'
      T

/-- Theorem 26.26 (1): under the Stroock--Varadhan hypotheses, the local martingale problem is
well-posed. -/
theorem stroockVaradhan_localMartingaleProblemWellPosed
    (a : StroockVaradhanDiffusionMatrixCoeff n)
    (b : StroockVaradhanDriftCoeff n)
    (ha_time : ∀ t x i j, a t x i j = a 0 x i j)
    (hb_time : ∀ t x i, b t x i = b 0 x i)
    (ha_cont : ∀ i j : Fin n, Continuous (fun x : StroockVaradhanState n ↦ a 0 x i j))
    (hb_meas : ∀ i : Fin n, Measurable (fun x : StroockVaradhanState n ↦ b 0 x i))
    (ha_symm : ∀ x : StroockVaradhanState n, ∀ i j : Fin n, a 0 x i j = a 0 x j i)
    (ha_pos :
      ∀ x v : StroockVaradhanState n, v ≠ 0 →
        0 < ∑ i, v i * ∑ j, a 0 x i j * v j)
    (hgrowth : StroockVaradhanGrowthCondition a b) :
    LocalMartingaleProblemWellPosed.{u, v} a b := by
  let hTimeIndependent :=
    stroockVaradhan_timeIndependentLocalMartingaleProblemCoefficients
      a
      b
      ha_time
      hb_time
  refine (localMartingaleProblemWellPosed_iff).2 ?_
  intro x
  exact
    stroockVaradhan_diracLocalMartingaleProblemDataSupport.{u, v}
      (n := n)
      a
      b
      hTimeIndependent
      ha_cont
      hb_meas
      ha_symm
      ha_pos
      hgrowth
      x

/-- Clause (3) of Theorem 26.26: under the Stroock--Varadhan hypotheses, each deterministic
start admits a pathwise strong realization with the fixed-start strong-Markov property. -/
theorem stroockVaradhan_strongMarkovRealizationAtStart
    (a : StroockVaradhanDiffusionMatrixCoeff n)
    (b : StroockVaradhanDriftCoeff n)
    (σ : NNReal → StroockVaradhanState n → Fin n → Fin m → ℝ)
    (haσ : a = diffusionMatrixOfCoefficient σ)
    (hcoeff : TimeIndependentCoefficients σ b)
    (ha_cont : ∀ i j : Fin n, Continuous (fun x : StroockVaradhanState n ↦ a 0 x i j))
    (hb_meas : ∀ i : Fin n, Measurable (fun x : StroockVaradhanState n ↦ b 0 x i))
    (ha_symm : ∀ x : StroockVaradhanState n, ∀ i j : Fin n, a 0 x i j = a 0 x j i)
    (ha_pos :
      ∀ x v : StroockVaradhanState n, v ≠ 0 →
        0 < ∑ i, v i * ∑ j, a 0 x i j * v j)
    (hgrowth : StroockVaradhanGrowthCondition a b)
    (x : StroockVaradhanState n) :
    ∃ (Ω : Type u) (_mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal inferInstance)
      (P : ProbabilityMeasure Ω) (W : NNReal → Ω → Fin m → ℝ)
      (X : NNReal → Ω → StroockVaradhanState n)
      (κ : Kernel (StroockVaradhanState n) (NNReal → StroockVaradhanState n)),
      HasPathwiseStrongSolutionRealization
          (IsBrownianMotionWithFiltration ℱ (P : Measure Ω))
          (fun ξ W' X' ↦ IsGeneralizedNDimensionalDiffusion ℱ (P : Measure Ω) ξ W' σ b X')
          ℱ
          (fun _ ↦ x)
          W
          X ∧
        HasStrongMarkovPropertyAtStartNDim P X κ := by
  exact
    ProbabilityTheory.stroockVaradhan_diracStrongMarkovRealizationFrontier
      (n := n)
      (m := m)
      a
      b
      σ
      haσ
      hcoeff
      ha_cont
      hb_meas
      ha_symm
      ha_pos
      hgrowth
      x

/-- Clause (4) of Theorem 26.26: every deterministic-start path-law family arising from the
Stroock--Varadhan hypotheses satisfies the Feller continuity statement. -/
theorem stroockVaradhan_fellerPathLawFamily
    (a : StroockVaradhanDiffusionMatrixCoeff n)
    (b : StroockVaradhanDriftCoeff n)
    (ha_time : ∀ t x i j, a t x i j = a 0 x i j)
    (hb_time : ∀ t x i, b t x i = b 0 x i)
    (ha_cont : ∀ i j : Fin n, Continuous (fun x : StroockVaradhanState n ↦ a 0 x i j))
    (hb_meas : ∀ i : Fin n, Measurable (fun x : StroockVaradhanState n ↦ b 0 x i))
    (ha_symm : ∀ x : StroockVaradhanState n, ∀ i j : Fin n, a 0 x i j = a 0 x j i)
    (ha_pos :
      ∀ x v : StroockVaradhanState n, v ≠ 0 →
        0 < ∑ i, v i * ∑ j, a 0 x i j * v j)
    (hgrowth : StroockVaradhanGrowthCondition a b)
    (P : StroockVaradhanState n → ProbabilityMeasure (StroockVaradhanPathSpace n))
    (hP :
      ∀ x : StroockVaradhanState n,
        IsLocalMartingaleProblemSolution
          (Measure.dirac x)
          a
          b
          (canonicalCoordinateFiltration (n := n))
          (P x : Measure (StroockVaradhanPathSpace n))
          id)
    (t : NNReal) :
    0 < t →
      ∀ f : StroockVaradhanState n → ℝ,
        Measurable f →
          (∃ C : ℝ, ∀ y : StroockVaradhanState n, |f y| ≤ C) →
            Continuous (fun x : StroockVaradhanState n ↦
              ∫ γ, f (γ t) ∂ (P x : Measure (StroockVaradhanPathSpace n))) := by
  intro ht f hf hf_bdd
  let hTimeIndependent :=
    stroockVaradhan_timeIndependentLocalMartingaleProblemCoefficients
      a
      b
      ha_time
      hb_time
  have hExist :
      ∀ x : StroockVaradhanState n,
        ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
          (P' : ProbabilityMeasure Ω) (X : Ω → StroockVaradhanPathSpace n),
          IsLocalMartingaleProblemSolution
            (Measure.dirac x)
            a
            b
            ℱ
            (P' : Measure Ω)
            X := by
    intro x
    exact
      (stroockVaradhan_diracLocalMartingaleProblemDataSupport.{0, 0}
        (n := n)
        a
        b
        hTimeIndependent
        ha_cont
        hb_meas
        ha_symm
        ha_pos
        hgrowth
        x).1
  have hMarg :
      HasDeterministicTimeMarginalUniqueness.{0, 0} a b :=
    stroockVaradhan_diracDeterministicTimeMarginalUniqueness.{0, 0}
      (n := n)
      a
      b
      ha_time
      hb_time
      ha_cont
      hb_meas
      ha_symm
      ha_pos
      hgrowth
  have hWellPosed0 : LocalMartingaleProblemWellPosed.{0, 0} a b :=
    stroockVaradhan_localMartingaleProblemWellPosed.{0, 0}
      (n := n)
      a
      b
      ha_time
      hb_time
      ha_cont
      hb_meas
      ha_symm
      ha_pos
      hgrowth
  rcases
      (uniquenessInMartingaleProblem
        a
        b
        hTimeIndependent
        hExist
        hMarg :
        ∃ Pref : StroockVaradhanState n → ProbabilityMeasure (StroockVaradhanPathSpace n),
          (∀ x : StroockVaradhanState n,
              IsLocalMartingaleProblemSolution
                (Measure.dirac x)
                a
                b
                (generatedFiltration
                  (fun t ↦
                    (ContinuousMap.evalCLM ℝ t :
                      StroockVaradhanPathSpace n → StroockVaradhanState n))
                  (measurable_path_eval (n := n)))
                (Pref x : Measure (StroockVaradhanPathSpace n))
                id) ∧
            LocalMartingaleProblemWellPosed.{0, 0} a b ∧
              CanonicalPathLawHasStrongMarkovAndUniqueWeakSolution Pref) with
    ⟨Pref, hPrefGenerated, _hWellPosed, hPackage⟩
  have hPref :
      ∀ x : StroockVaradhanState n,
        IsLocalMartingaleProblemSolution
          (Measure.dirac x)
          a
          b
          (canonicalCoordinateFiltration (n := n))
          (Pref x : Measure (StroockVaradhanPathSpace n))
          id := by
    intro x
    simpa [canonicalCoordinateFiltration] using hPrefGenerated x
  rcases hPackage.strongMarkov with ⟨κ, hMarkov, _hStrongMarkov⟩
  have hKernelCont :=
    ProbabilityTheory.stroockVaradhan_positiveTimeTransitionKernelExpectationContinuousFrontier
      (n := n)
      a
      b
      hTimeIndependent
      ha_cont
      hb_meas
      ha_symm
      ha_pos
      hgrowth
      Pref
      κ
      hPrefGenerated
      hMarkov
      t
      ht
      f
      hf
      hf_bdd
  have hPrefCont :=
    stroockVaradhan_referencePathIntegralContinuousFrontierSupport
      (n := n)
      Pref
      κ
      hMarkov
      t
      f
      hf
      hKernelCont
  have hRowEq :=
    stroockVaradhan_pathLaw_eq_reference
      (n := n)
      hPref
      hP
      hWellPosed0
  have hRewrite :
      (fun x : StroockVaradhanState n ↦
        ∫ γ, f (γ t) ∂ (P x : Measure (StroockVaradhanPathSpace n))) =
        fun x : StroockVaradhanState n ↦
          ∫ γ, f (γ t) ∂ (Pref x : Measure (StroockVaradhanPathSpace n)) := by
    funext x
    rw [hRowEq x]
  simpa [hRewrite] using hPrefCont

end ProbabilityTheory
