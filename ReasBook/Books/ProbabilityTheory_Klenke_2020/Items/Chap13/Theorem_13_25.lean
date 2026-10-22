/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_17
import Books.ProbabilityTheory_Klenke_2020.Items.Chap13.Theorem_13_16

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.FiniteMeasure
open scoped Topology BoundedContinuousFunction

universe u v w

section

variable {E₁ : Type u} {E₂ : Type v}
variable [MeasurableSpace E₁] [MetricSpace E₁] [BorelSpace E₁]
variable [MeasurableSpace E₂] [MetricSpace E₂] [BorelSpace E₂]

/-- Helper for Theorem 13.25: composing a bounded continuous test function with `φ` cannot create
new discontinuity points beyond the discontinuity set of `φ`. -/
private lemma compDiscontinuitySet_subset (φ : E₁ → E₂) (f : E₂ →ᵇ ℝ) :
    {x : E₁ | ¬ ContinuousAt (fun y ↦ f (φ y)) x} ⊆ {x : E₁ | ¬ ContinuousAt φ x} := by
  intro x hx
  -- Proof comment: continuity of `φ` at `x` and continuity of `f` at `φ x` combine by
  -- composition.
  by_contra hcont
  have hcont' : ContinuousAt φ x := by
    simpa using hcont
  exact hx (f.continuous.continuousAt.comp hcont')

/-- Helper for Theorem 13.25: Theorem 13.16 applied to `f ∘ φ` yields convergence of the
corresponding source integrals under the `μ`-null discontinuity hypothesis on `φ`. -/
private lemma tendstoIntegralComp_ofNullDiscontinuitySet
    (μs : ℕ → FiniteMeasure E₁) (μ : FiniteMeasure E₁) (φ : E₁ → E₂) (hφ : Measurable φ)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1)
    (hdisc : μ {x : E₁ | ¬ ContinuousAt φ x} = 0) (hweak : Tendsto μs atTop (𝓝 μ))
    (f : E₂ →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ x, f (φ x) ∂(μs n : Measure E₁)) atTop
      (𝓝 (∫ x, f (φ x) ∂(μ : Measure E₁))) := by
  have hnullCriterion :
      ∀ g : E₁ → ℝ, Bornology.IsBounded (Set.range g) → Measurable g →
        μ {x : E₁ | ¬ ContinuousAt g x} = 0 →
          Tendsto (fun n ↦ ∫ x, g x ∂(μs n : Measure E₁)) atTop
            (𝓝 (∫ x, g x ∂(μ : Measure E₁))) := by
    exact (((FiniteMeasure.portmanteau_subprobability_tfae μs μ hμ hμs).1.out 0 2).mp hweak)
  have hbounded : Bornology.IsBounded (Set.range fun x ↦ f (φ x)) := by
    refine f.isBounded_range.subset ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨φ x, rfl⟩
  have hdiscMeasure : (μ : Measure E₁) {x : E₁ | ¬ ContinuousAt φ x} = 0 := by
    simpa using hdisc
  have hdiscCompMeasure :
      (μ : Measure E₁) {x : E₁ | ¬ ContinuousAt (fun y ↦ f (φ y)) x} = 0 := by
    -- Proof comment: the composed discontinuity set sits inside the original one.
    exact measure_mono_null (compDiscontinuitySet_subset (φ := φ) (f := f)) hdiscMeasure
  have hdiscComp : μ {x : E₁ | ¬ ContinuousAt (fun y ↦ f (φ y)) x} = 0 := by
    simpa using hdiscCompMeasure
  -- Proof comment: specialize the Portmanteau null-discontinuity clause to the composed test
  -- function.
  simpa using
    hnullCriterion (fun x ↦ f (φ x)) hbounded (f.continuous.measurable.comp hφ) hdiscComp

-- Proof sketch: use the bounded-measurable test-function clause of
-- `FiniteMeasure.portmanteau_subprobability_tfae`; for each bounded continuous `f` on `E₂`, the
-- composition `f ∘ φ` is bounded and measurable on `E₁`, and its discontinuity set is contained in
-- the discontinuity set of `φ`.
/-- Theorem 13.25 (1): if subprobability finite measures on `E₁` converge weakly to `μ` and the
discontinuity set of the measurable map `φ` is `μ`-null, then their pushforwards by `φ` converge
weakly to the pushforward of `μ`. -/
theorem finiteMeasure_tendsto_map_of_null_discontinuitySet
    (μs : ℕ → FiniteMeasure E₁) (μ : FiniteMeasure E₁) (φ : E₁ → E₂) (hφ : Measurable φ)
    (hμ : μ.mass ≤ 1) (hμs : ∀ n, (μs n).mass ≤ 1)
    (hdisc : μ {x : E₁ | ¬ ContinuousAt φ x} = 0) (hweak : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n ↦ (μs n).map φ) atTop (𝓝 (μ.map φ)) := by
  rw [FiniteMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hcomp :
      Tendsto (fun n ↦ ∫ x, f (φ x) ∂(μs n : Measure E₁)) atTop
        (𝓝 (∫ x, f (φ x) ∂(μ : Measure E₁))) :=
    tendstoIntegralComp_ofNullDiscontinuitySet
      (μs := μs) (μ := μ) (φ := φ) hφ hμ hμs hdisc hweak f
  have hcompMap :
      Tendsto (fun n ↦ ∫ x, f x ∂((μs n).map φ : Measure E₂)) atTop
        (𝓝 (∫ x, f (φ x) ∂(μ : Measure E₁))) := by
    refine (tendsto_congr' ?_).2 hcomp
    exact Filter.Eventually.of_forall fun n ↦ by
      -- Proof comment: rewrite each sequence integral through the pushforward.
      simpa using
        (MeasureTheory.integral_map (μ := (μs n : Measure E₁)) hφ.aemeasurable
          f.continuous.aestronglyMeasurable)
  have hmapLimit :
      ∫ x, f x ∂(μ.map φ : Measure E₂) = ∫ x, f (φ x) ∂(μ : Measure E₁) := by
    -- Proof comment: the same `integral_map` rewrite identifies the limit integral.
    simpa using
      (MeasureTheory.integral_map (μ := (μ : Measure E₁)) hφ.aemeasurable
        f.continuous.aestronglyMeasurable)
  exact hmapLimit.symm ▸ hcompMap

end

section

variable {Ω : Type u} {E₁ : Type v} {E₂ : Type w}
variable [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable [MeasurableSpace E₁] [MetricSpace E₁] [BorelSpace E₁]
variable [MeasurableSpace E₂] [MetricSpace E₂] [BorelSpace E₂]

/-- Helper for Theorem 13.25: if the event `X ∈ U` is `P`-null, then the law of `X` gives mass
zero to `U`. -/
private lemma lawNullDiscontinuitySet_ofPreimageNull
    {X : Ω → E₁} {ν : ProbabilityMeasure E₁} {U : Set E₁}
    (hXlaw : HasLaw X (ν : Measure E₁) P) (hU : MeasurableSet U)
    (hnull : P (X ⁻¹' U) = 0) :
    ν.toFiniteMeasure U = 0 := by
  have hMapProb : ProbabilityMeasure.map ⟨P, inferInstance⟩ hXlaw.aemeasurable = ν := by
    apply ProbabilityMeasure.toMeasure_injective
    simpa using hXlaw.map_eq
  have hSet : ν U = 0 := by
    rw [← hMapProb]
    -- Proof comment: on the probability-measure owner, `map_apply` turns the set mass into the
    -- original preimage event.
    rw [ProbabilityMeasure.map_apply_of_aemeasurable ⟨P, inferInstance⟩ hXlaw.aemeasurable hU]
    simpa [hnull]
  simpa using hSet

/-- Helper for Theorem 13.25: mapping a probability measure and then forgetting to the finite
measure owner agrees with first forgetting and then mapping. -/
private lemma probabilityMeasureMap_toFiniteMeasure
    (ν : ProbabilityMeasure E₁) (φ : E₁ → E₂) (hφ : Measurable φ) :
    (ProbabilityMeasure.map ν hφ.aemeasurable).toFiniteMeasure = ν.toFiniteMeasure.map φ := by
  -- Proof comment: both sides are the same pushforward measure, viewed through different owners.
  apply FiniteMeasure.toMeasure_injective
  simp

-- Proof sketch: pass to the laws of `X n` and `X`, apply the finite-measure statement of the
-- continuous mapping theorem to those laws, and rewrite the resulting pushed-forward laws as the
-- laws of `φ ∘ X n` and `φ ∘ X`.
/-- Theorem 13.25 (2): if `X n` converges in distribution to `X` and `X` hits the discontinuity
set of the measurable map `φ` only on a `P`-null event, then `φ ∘ X n` converges in distribution
to `φ ∘ X`. -/
theorem tendstoInDistribution_comp_of_preimage_null_discontinuitySet
    {Xn : ℕ → Ω → E₁} {X : Ω → E₁} {φ : E₁ → E₂} (hφ : Measurable φ)
    (hdisc : P (X ⁻¹' {x : E₁ | ¬ ContinuousAt φ x}) = 0)
    (hX : TendstoInDistribution Xn atTop X (fun _ ↦ P) P) :
    TendstoInDistribution (fun n ↦ φ ∘ Xn n) atTop (φ ∘ X) (fun _ ↦ P) P := by
  let ν : ProbabilityMeasure E₁ :=
    ⟨P.map X, Measure.isProbabilityMeasure_map hX.aemeasurable_limit⟩
  let νs : ℕ → ProbabilityMeasure E₁ :=
    fun n ↦ ⟨P.map (Xn n), Measure.isProbabilityMeasure_map (hX.forall_aemeasurable n)⟩
  have hXlaw : HasLaw X (ν : Measure E₁) P := by
    exact ⟨hX.aemeasurable_limit, rfl⟩
  have hXnLaw : ∀ n, HasLaw (Xn n) ((νs n : ProbabilityMeasure E₁) : Measure E₁) P := by
    intro n
    exact ⟨hX.forall_aemeasurable n, rfl⟩
  have hν : Tendsto νs atTop (𝓝 ν) :=
    (tendstoInDistribution_iff_tendsto_limit_law hX.forall_aemeasurable hXlaw).1 hX
  have hsubν : ν.toFiniteMeasure.mass ≤ 1 := by
    simpa using ν.mass_toFiniteMeasure.le
  have hsubνs : ∀ n, (νs n).toFiniteMeasure.mass ≤ 1 := by
    intro n
    simpa using (νs n).mass_toFiniteMeasure.le
  have hdiscMeas : MeasurableSet {x : E₁ | ¬ ContinuousAt φ x} := by
    -- Proof comment: the continuity set is `Gδ`, hence its complement is measurable.
    exact (IsGδ.setOf_continuousAt φ).measurableSet.compl
  have hdiscν : ν.toFiniteMeasure {x : E₁ | ¬ ContinuousAt φ x} = 0 :=
    lawNullDiscontinuitySet_ofPreimageNull
      (hXlaw := hXlaw) (hU := hdiscMeas) (hnull := hdisc)
  have hνFinite :
      Tendsto (fun n ↦ (νs n).toFiniteMeasure) atTop (𝓝 ν.toFiniteMeasure) := by
    -- Proof comment: weak convergence on `ProbabilityMeasure` is the same topology transported
    -- through `toFiniteMeasure`.
    simpa [Function.comp] using
      (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds
        (F := atTop) (μs := νs) (μ₀ := ν)).mp hν
  have hMapFinite :
      Tendsto (fun n ↦ (νs n).toFiniteMeasure.map φ) atTop (𝓝 (ν.toFiniteMeasure.map φ)) :=
    finiteMeasure_tendsto_map_of_null_discontinuitySet
      (μs := fun n ↦ (νs n).toFiniteMeasure) (μ := ν.toFiniteMeasure) (φ := φ)
      hφ hsubν hsubνs hdiscν hνFinite
  have hMapProb :
      Tendsto (fun n ↦ ProbabilityMeasure.map (νs n) hφ.aemeasurable) atTop
        (𝓝 (ProbabilityMeasure.map ν hφ.aemeasurable)) := by
    rw [ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds]
    simpa [Function.comp, probabilityMeasureMap_toFiniteMeasure (φ := φ) (hφ := hφ)] using
      hMapFinite
  have hφlaw :
      HasLaw φ ((ProbabilityMeasure.map ν hφ.aemeasurable : ProbabilityMeasure E₂) : Measure E₂)
        (ν : Measure E₁) := by
    exact ⟨hφ.aemeasurable, rfl⟩
  have hφlawSeq :
      ∀ n,
        HasLaw φ
          ((ProbabilityMeasure.map (νs n) hφ.aemeasurable : ProbabilityMeasure E₂) : Measure E₂)
          ((νs n : ProbabilityMeasure E₁) : Measure E₁) := by
    intro n
    exact ⟨hφ.aemeasurable, rfl⟩
  have hCompLaw :
      HasLaw (φ ∘ X) ((ProbabilityMeasure.map ν hφ.aemeasurable : ProbabilityMeasure E₂) :
        Measure E₂) P := by
    -- Proof comment: the law of the limit composition is the pushforward of the limit law by `φ`.
    simpa [Function.comp] using HasLaw.comp hφlaw hXlaw
  have hCompMeas : ∀ n, AEMeasurable (φ ∘ Xn n) P := by
    intro n
    exact hφ.aemeasurable.comp_aemeasurable (hX.forall_aemeasurable n)
  have hMapProbComp :
      Tendsto
        (fun n ↦ ⟨P.map (φ ∘ Xn n), Measure.isProbabilityMeasure_map (hCompMeas n)⟩)
        atTop (𝓝 (ProbabilityMeasure.map ν hφ.aemeasurable)) := by
    have hSeqLaw :
        (fun n ↦ ⟨P.map (φ ∘ Xn n), Measure.isProbabilityMeasure_map (hCompMeas n)⟩) =
          fun n ↦ ProbabilityMeasure.map (νs n) hφ.aemeasurable := by
      funext n
      apply ProbabilityMeasure.toMeasure_injective
      simpa [Function.comp] using (HasLaw.comp (hφlawSeq n) (hXnLaw n)).map_eq
    simpa [hSeqLaw] using hMapProb
  exact
    (tendstoInDistribution_iff_tendsto_limit_law hCompMeas hCompLaw).2 hMapProbComp

end
