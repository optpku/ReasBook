/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_8.StrongMarkovAtStart
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_10.OneDimensional

open MeasureTheory ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

/-- Shared support API for Theorem 26.10: for time-inhomogeneous one-dimensional coefficients,
the fixed-start strong-Markov property records that after an almost surely finite stopping time
the future law depends on the stopped time together with the stopped state. -/
def HasTimeInhomogeneousStrongMarkovPropertyAtStartNDim
    {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω)
    (X : NNReal → Ω → SDEState 1)
    (κ : Kernel (WithTop NNReal × SDEState 1) (NNReal → SDEState 1)) : Prop :=
  ∀ (τ : Ω → WithTop NNReal)
    (hτ : IsStoppingTime (processFiltration X) τ),
    (∀ᵐ ω ∂(P : Measure Ω), τ ω ≠ ⊤) →
    ∀ (f : (NNReal → SDEState 1) → ℝ),
      Measurable f →
      (∃ C : ℝ, ∀ y, |f y| ≤ C) →
      (P : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) | hτ.measurableSpace] =ᵐ[
        (P : Measure Ω)] fun ω ↦ ∫ y, f y ∂ κ (τ ω, stoppedValue X τ ω)

/-- Shared support API for Theorem 26.10: package a measurable raw restart solver into a restart
kernel by pairing each future-noise sample with the deterministic stopped time and stopped state. -/
private noncomputable def restartKernelOfRaw
    {β : Type*} [MeasurableSpace β]
    (noiseKernel : Kernel (WithTop NNReal × SDEState 1) β)
    (restartRaw : ((WithTop NNReal × SDEState 1) × β) → (NNReal → SDEState 1))
    (hRestartRaw : Measurable restartRaw) :
    Kernel (WithTop NNReal × SDEState 1) (NNReal → SDEState 1) :=
  Kernel.deterministic restartRaw hRestartRaw ∘ₖ (Kernel.id ×ₖ noiseKernel)

/-- Shared support API for Theorem 26.10: the row of `restartKernelOfRaw` is the pushforward of
the corresponding future-noise row along the raw restart solver at the stopped time/state pair. -/
private theorem integral_restartKernelOfRaw_apply
    {β : Type*} [MeasurableSpace β]
    (noiseKernel : Kernel (WithTop NNReal × SDEState 1) β)
    [IsSFiniteKernel noiseKernel]
    (restartRaw : ((WithTop NNReal × SDEState 1) × β) → (NNReal → SDEState 1))
    (hRestartRaw : Measurable restartRaw)
    (x : WithTop NNReal × SDEState 1)
    {f : (NNReal → SDEState 1) → ℝ}
    (hf : Measurable f) :
    ∫ y, f y ∂ restartKernelOfRaw noiseKernel restartRaw hRestartRaw x =
      ∫ z, f (restartRaw (x, z)) ∂ noiseKernel x := by
  have hMap :
      restartKernelOfRaw noiseKernel restartRaw hRestartRaw =
        (Kernel.id ×ₖ noiseKernel).map restartRaw := by
    simpa [restartKernelOfRaw] using
      (Kernel.deterministic_comp_eq_map hRestartRaw (Kernel.id ×ₖ noiseKernel))
  have hProdMap :
      (Kernel.id ×ₖ noiseKernel) x = Measure.map (Prod.mk x) (noiseKernel x) := by
    ext s hs
    rw [Kernel.id_prod_apply' noiseKernel x hs, Measure.map_apply (by fun_prop) hs]
  rw [hMap, Kernel.map_apply _ hRestartRaw x]
  rw [MeasureTheory.integral_map hRestartRaw.aemeasurable
    hf.stronglyMeasurable.aestronglyMeasurable]
  rw [hProdMap]
  exact
    MeasureTheory.integral_map
      ((by
        have hMeas : Measurable (Prod.mk x : β → (WithTop NNReal × SDEState 1) × β) := by
          fun_prop
        exact hMeas.aemeasurable))
      ((hf.comp hRestartRaw).stronglyMeasurable.aestronglyMeasurable)

/-- Shared support API for Theorem 26.10: once the restart identity is normalized to a measurable
raw restart solver, the fixed-start strong-Markov kernel is obtained by packaging that solver with
`restartKernelOfRaw`. -/
theorem existsRestartKernel_of_measurableRestartRaw
    {β : Type*} [MeasurableSpace β]
    (noiseKernel : Kernel (WithTop NNReal × SDEState 1) β)
    [IsSFiniteKernel noiseKernel]
    (restartRaw : ((WithTop NNReal × SDEState 1) × β) → (NNReal → SDEState 1))
    (hRestartRaw : Measurable restartRaw)
    {Ω : Type u} [MeasurableSpace Ω]
    {X : NNReal → Ω → SDEState 1}
    {P : ProbabilityMeasure Ω}
    (hRestart :
      ∀ (τ : Ω → WithTop NNReal)
        (hτ : IsStoppingTime (processFiltration X) τ),
        (∀ᵐ ω ∂(P : Measure Ω), τ ω ≠ ⊤) →
        ∀ (f : (NNReal → SDEState 1) → ℝ),
          Measurable f →
          (∃ C : ℝ, ∀ y, |f y| ≤ C) →
          ((P : Measure Ω)[fun ω ↦ f (futurePathAfterStoppingTime X τ ω) |
            hτ.measurableSpace]) =ᵐ[(P : Measure Ω)] fun ω ↦
              ∫ z, f (restartRaw ((τ ω, stoppedValue X τ ω), z)) ∂noiseKernel
                (τ ω, stoppedValue X τ ω)) :
    ∃ κ : Kernel (WithTop NNReal × SDEState 1) (NNReal → SDEState 1),
      HasTimeInhomogeneousStrongMarkovPropertyAtStartNDim P X κ := by
  let κ : Kernel (WithTop NNReal × SDEState 1) (NNReal → SDEState 1) :=
    restartKernelOfRaw noiseKernel restartRaw hRestartRaw
  refine ⟨κ, ?_⟩
  intro τ hτ hτfinite f hf hbounded
  have hRow :
      (fun ω ↦
        ∫ z, f (restartRaw ((τ ω, stoppedValue X τ ω), z)) ∂
          noiseKernel (τ ω, stoppedValue X τ ω)) =
        fun ω ↦
          ∫ y, f y ∂ κ (τ ω, stoppedValue X τ ω) := by
    funext ω
    symm
    exact
      integral_restartKernelOfRaw_apply
        noiseKernel
        restartRaw
        hRestartRaw
        (τ ω, stoppedValue X τ ω)
        hf
  simpa [κ, hRow] using hRestart τ hτ hτfinite f hf hbounded

end ProbabilityTheory
