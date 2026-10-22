/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_22
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_26.Evaluation

open MeasureTheory ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

universe u

variable {n : ℕ}

/-- Helper for Theorem 26.26: deterministic-time evaluation against a path law is exactly
integration against the pushed-forward deterministic-time marginal. -/
private theorem stroockVaradhan_integral_eval_eq_integral_timeMarginal_support
    (μ : Measure (StroockVaradhanPathSpace n))
    (t : NNReal)
    {f : StroockVaradhanState n → ℝ}
    (hf : Measurable f) :
    ∫ γ, f (γ t) ∂μ =
      ∫ y, f y ∂ μ.map (ContinuousMap.evalCLM ℝ t) := by
  -- Proof comment: deterministic-time evaluation is measurable on path space, so the usual
  -- `integral_map` identity rewrites the path integral as a time-marginal integral.
  symm
  simpa using
    (MeasureTheory.integral_map
      ((measurable_path_eval t).aemeasurable)
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
  -- Proof comment: each row is the same evaluation-pushforward identity specialized at `P x`.
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
  -- Local instance justification (typeclass bridge): the Markov API is stated through an
  -- instance argument, and `hMarkov` is the extracted witness for this chosen reference family.
  letI :
      IsTimeHomogeneousMarkovProcess
        (fun t ↦
          (ContinuousMap.evalCLM ℝ t :
            StroockVaradhanPathSpace n → StroockVaradhanState n))
        Pref
        κ := hMarkov
  -- Proof comment: the Chapter 17 Markov-process interface already identifies time marginals with
  -- the transition kernel of the extracted family.
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
  -- Proof comment: first rewrite the kernel row as the deterministic-time marginal, then rewrite
  -- that marginal as the same path integral against `Pref x`.
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
private theorem stroockVaradhan_pathIntegralContinuous_of_transitionKernelRow_support
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
  -- Proof comment: once the two rows are definitionally the same after rewriting, continuity is
  -- exactly the continuity already known for the kernel row.
  simpa [hRewrite] using hKernelCont

/-- Helper for Theorem 26.26: theorem-local support interface reducing the reference-family
path-integral row to the same family's transition-kernel expectation row. -/
theorem stroockVaradhan_referencePathIntegralContinuousFrontierSupport
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
  -- Proof comment: the theorem-local support layer now isolates only the stable rewrite from the
  -- Markov-kernel row to the path-integral row; the analytic kernel continuity is supplied by the
  -- caller as the actual remaining frontier.
  exact
    stroockVaradhan_pathIntegralContinuous_of_transitionKernelRow_support
      (n := n)
      Pref
      κ
      hMarkov
      t
      hf
      hKernelCont

end ProbabilityTheory
