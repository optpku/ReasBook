/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap22.Theorem_22_5

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Remark 22.6: the process filtration of the pair process `(0, B)` agrees with the
natural filtration of `B`. -/
private lemma constantAuxProcessFiltration_eq_natural
    {law : ProbabilityMeasure Ω} {B : NNReal → Ω → ℝ}
    (hB : IsBrownianMotion (law : Measure Ω) B) :
    processFiltration (fun s ω ↦ ((0 : ℝ), B s ω)) =
      Filtration.natural B hB.stronglyMeasurable := by
  refine Filtration.ext ?_
  funext t
  -- Proof comment: the extra constant coordinate contributes only the trivial sigma-algebra.
  have hle : (⨆ s ≤ t, MeasurableSpace.comap (B s) inferInstance) ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun s hs ↦ ?_
    exact (hB.stronglyMeasurable s).measurable.comap_le
  calc
    (processFiltration (fun s ω ↦ ((0 : ℝ), B s ω))) t
        = ‹MeasurableSpace Ω› ⊓
            (⨆ s ≤ t, MeasurableSpace.comap (fun ω ↦ ((0 : ℝ), B s ω)) inferInstance) := rfl
    _ = ‹MeasurableSpace Ω› ⊓
          (⨆ s ≤ t,
            MeasurableSpace.comap (fun _ : Ω ↦ (0 : ℝ)) inferInstance ⊔
              MeasurableSpace.comap (B s) inferInstance) := by
          congr 1
          exact biSup_congr fun s hs ↦ by
            simpa using
              (MeasurableSpace.comap_prodMk
                (mβ := borel ℝ) (mγ := borel ℝ) (fun _ : Ω ↦ (0 : ℝ)) (B s))
    _ = ‹MeasurableSpace Ω› ⊓ (⨆ s ≤ t, MeasurableSpace.comap (B s) inferInstance) := by
          simp [MeasurableSpace.comap_const]
    _ = ⨆ s ≤ t, MeasurableSpace.comap (B s) inferInstance := inf_eq_right.mpr hle
    _ = (Filtration.natural B hB.stronglyMeasurable) t := rfl

/-- Helper for Remark 22.6: if the auxiliary variable in a Skorohod embedding is constant, then
the same clock is already a stopping time for the Brownian natural filtration `σ(B)`. -/
private theorem stopping_natural
    {law : ProbabilityMeasure Ω} {B : NNReal → Ω → ℝ} {τ : Ω → NNReal}
    (hB : IsBrownianMotion (law : Measure Ω) B)
    (hτ : IsStoppingTime (processFiltration (fun s ω ↦ ((0 : ℝ), B s ω)))
      (fun ω ↦ (τ ω : ENNReal))) :
    IsStoppingTime (Filtration.natural B hB.stronglyMeasurable)
      (fun ω ↦ (τ ω : ENNReal)) := by
  -- Proof comment: rewrite the constant-auxiliary process filtration to the natural filtration.
  simpa [constantAuxProcessFiltration_eq_natural hB] using hτ

/-- Remark 22.6: if the auxiliary variable in a Skorohod embedding is constant, then the same
clock is already a stopping time for the Brownian natural filtration `σ(B)`. -/
theorem existsNaturalFiltrationEmbeddingOfBinaryLimitLaw
    {law : ProbabilityMeasure Ω} {B : NNReal → Ω → ℝ} {τ : Ω → NNReal}
    (hB : IsBrownianMotion (law : Measure Ω) B)
    (hτ : IsStoppingTime (processFiltration (fun s ω ↦ ((0 : ℝ), B s ω)))
      (fun ω ↦ (τ ω : ENNReal))) :
    IsStoppingTime (Filtration.natural B hB.stronglyMeasurable)
      (fun ω ↦ (τ ω : ENNReal)) := by
  -- Proof comment: this is exactly the constant-auxiliary filtration reduction proved above.
  exact stopping_natural hB hτ

end ProbabilityTheory
