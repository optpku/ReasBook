/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Definition_6_2

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {β : Type v} [MetricSpace β]

-- Proof sketch: on each finite-measure set `s`, apply the canonical finite-measure
-- uniqueness theorem `tendstoInMeasure_ae_unique` to the restricted measure `μ.restrict s`. The
-- canonical sigma-finite globalization theorem `ae_of_forall_measure_lt_top_ae_restrict` then
-- promotes these restricted almost-everywhere equalities to `f = g` almost everywhere on `Ω`.
/-- Remark 6.5: Let `β` be a metric space. On a `σ`-finite measure space, if a sequence converges
in `μ`-measure on every set of finite `μ`-measure to both `f` and `g`, then `f` and
`g` are equal `μ`-almost everywhere. Equivalently, in a separated metric codomain, local
convergence in measure `TendstoInMeasureOnFiniteMeasureSets` determines the limit up to a.e.
equality. -/
theorem ae_eq_of_tendstoInMeasureOnFiniteMeasureSets
    (μ : Measure Ω) [SigmaFinite μ] {fSeq : ℕ → Ω → β} {f g : Ω → β}
    (hf : TendstoInMeasureOnFiniteMeasureSets μ fSeq f)
    (hg : TendstoInMeasureOnFiniteMeasureSets μ fSeq g) :
    f =ᵐ[μ] g := by
  change ∀ᵐ ω ∂μ, f ω = g ω
  refine ae_of_forall_measure_lt_top_ae_restrict (fun ω ↦ f ω = g ω) ?_
  intro s hs hμs
  haveI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  exact tendstoInMeasure_ae_unique (hf s hμs) (hg s hμs)
