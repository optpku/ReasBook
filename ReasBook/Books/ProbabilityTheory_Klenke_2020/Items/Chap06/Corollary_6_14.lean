/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Corollary_6_13

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
variable [TopologicalSpace.SeparableSpace E]

local notation "MeasurableMap" => {f : Ω → E // Measurable f}

/-- A topology on the subtype of measurable maps `Ω → E` induces almost-everywhere convergence if
its sequential convergence is equivalent to `μ`-almost-everywhere convergence for every measurable
sequence and measurable limit. -/
def TopologyInducesAlmostEverywhereConvergence
    (μ : Measure Ω) (τ : TopologicalSpace MeasurableMap) : Prop :=
  letI := τ
  ∀ {fSeq : ℕ → Ω → E} {f : Ω → E}, (hf : Measurable f) → (hSeq : ∀ n, Measurable (fSeq n)) →
    Tendsto
      (fun n ↦ (⟨fSeq n, hSeq n⟩ : MeasurableMap))
      atTop
      (𝓝 ⟨f, hf⟩) ↔
        ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))

-- Proof sketch: assume such a topology `τ` exists. Choose a witness to the failure of almost-
-- everywhere convergence despite convergence in measure. By the right-to-left direction of the
-- induced-convergence hypothesis, the sequence does not converge to its limit in `τ`, so some
-- open neighborhood of the limit misses infinitely many terms. A subsequence outside that
-- neighborhood still converges in measure; Corollary 6.13 yields a further subsequence converging
-- almost everywhere, hence by the left-to-right direction it converges to the limit in `τ`,
-- contradicting eventual membership in every neighborhood.
/-- Corollary 6.14: On a sigma-finite measure space, if convergence in `μ`-measure on every
measurable set of finite `μ`-measure does not coincide with `μ`-almost-everywhere convergence for
measurable maps into a separable metric space, then no topology on the set of measurable maps
`Ω → E` induces almost-everywhere convergence. -/
theorem no_topology_on_measurable_maps_induces_almostEverywhereConvergence
    (μ : Measure Ω)
    [SigmaFinite μ]
    (h_not_coincide :
      ∃ fSeq : ℕ → Ω → E, ∃ f : Ω → E,
        Measurable f ∧
          (∀ n, Measurable (fSeq n)) ∧
          TendstoInMeasureOnFiniteMeasureSets μ fSeq f ∧
          ¬ ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω))) :
    ¬ ∃ τ : TopologicalSpace MeasurableMap,
      TopologyInducesAlmostEverywhereConvergence μ τ := by
  rintro ⟨τ, hτ⟩
  letI := τ
  rcases h_not_coincide with ⟨fSeq, f, hf, hSeq, h_local, h_not_ae⟩
  have h_iff :
      Tendsto (fun n ↦ (⟨fSeq n, hSeq n⟩ : MeasurableMap)) atTop (𝓝 ⟨f, hf⟩) ↔
        ∀ᵐ ω ∂μ, Tendsto (fun n ↦ fSeq n ω) atTop (𝓝 (f ω)) :=
    hτ hf hSeq
  have h_not_tendsto :
      ¬ Tendsto (fun n ↦ (⟨fSeq n, hSeq n⟩ : MeasurableMap)) atTop (𝓝 ⟨f, hf⟩) := by
    intro h_tendsto
    exact h_not_ae (h_iff.1 h_tendsto)
  obtain ⟨s, hs, hs_frequently⟩ :=
    not_tendsto_iff_exists_frequently_notMem.1 h_not_tendsto
  obtain ⟨ns, hns, hns_not_mem⟩ := extraction_of_frequently_atTop hs_frequently
  have h_subseq :
      ∀ ns : ℕ → ℕ, StrictMono ns → ∃ ns' : ℕ → ℕ, StrictMono ns' ∧
        ∀ᵐ ω ∂μ, Tendsto (fun i ↦ fSeq (ns (ns' i)) ω) atTop (𝓝 (f ω)) :=
    (tendstoInMeasureOnFiniteMeasureSets_iff_every_subsequence_has_ae_subsubsequence μ hSeq).1
      h_local
  obtain ⟨ns', _, h_ae⟩ := h_subseq ns hns
  have h_subseq_iff :
      Tendsto
        (fun i ↦ (⟨fSeq (ns (ns' i)), hSeq (ns (ns' i))⟩ : MeasurableMap))
        atTop
        (𝓝 ⟨f, hf⟩) ↔
        ∀ᵐ ω ∂μ, Tendsto (fun i ↦ fSeq (ns (ns' i)) ω) atTop (𝓝 (f ω)) :=
    hτ hf fun i ↦ hSeq _
  have h_tendsto :
      Tendsto
        (fun i ↦ (⟨fSeq (ns (ns' i)), hSeq (ns (ns' i))⟩ : MeasurableMap))
        atTop
        (𝓝 ⟨f, hf⟩) :=
    h_subseq_iff.2 h_ae
  have h_mem : ∀ᶠ i in atTop, (⟨fSeq (ns (ns' i)), hSeq (ns (ns' i))⟩ : MeasurableMap) ∈ s :=
    h_tendsto.eventually hs
  have h_not_mem :
      ∀ᶠ i in atTop, (⟨fSeq (ns (ns' i)), hSeq (ns (ns' i))⟩ : MeasurableMap) ∉ s :=
    .of_forall fun i ↦ hns_not_mem (ns' i)
  have : ∀ᶠ i in atTop, False :=
    (h_not_mem.and h_mem).mono fun _ hi ↦ hi.1 hi.2
  obtain ⟨N, hN⟩ := eventually_atTop.1 this
  exact (hN N le_rfl).elim
