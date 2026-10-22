/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {β : Type v} [PseudoMetricSpace β]

-- Proof sketch: fix a finite-measure set `A`, view `μ.restrict A` as a finite measure,
-- and apply the canonical finite-measure implication from almost-everywhere convergence to
-- convergence in measure. This is exactly the local textbook notion
-- `TendstoInMeasureOnFiniteMeasureSets`.
/-- Remark 6.4: for almost everywhere convergent measurable maps, `μ`-almost-everywhere
convergence implies convergence in `μ`-measure on every set of finite `μ`-measure, i.e. in the
local sense of `TendstoInMeasureOnFiniteMeasureSets`. -/
theorem tendstoInMeasureOnFiniteMeasureSets_of_tendsto_ae
    [MeasurableSpace β] [BorelSpace β]
    (μ : Measure Ω) {fSeq : ℕ → Ω → β} {f : Ω → β}
    (h_meas : ∀ n, AEStronglyMeasurable (fSeq n) μ)
    (h_ae : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) :
    TendstoInMeasureOnFiniteMeasureSets μ fSeq f := by
  rw [tendstoInMeasureOnFiniteMeasureSets_iff_forall_measurable]
  intro A hA hA_fin
  haveI : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hA_fin.ne
  have h_ae_restrict :
      ∀ᵐ ω ∂μ.restrict A, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) := ae_restrict_of_ae h_ae
  exact tendstoInMeasure_of_tendsto_ae (fun n ↦ (h_meas n).restrict) h_ae_restrict
