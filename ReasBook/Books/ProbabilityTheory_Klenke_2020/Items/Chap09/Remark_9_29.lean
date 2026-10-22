/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Remark_9_11

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u v

variable {ι : Type u} [Preorder ι]
variable {Ω : Type v} {m0 : MeasurableSpace Ω}
variable {ℱ 𝒢 : Filtration ι m0} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {X : ι → Ω → ℝ}

-- Proof sketch: combine the tower property
-- `μ[μ[X t | 𝒢 s] | ℱ s] = μ[X t | ℱ s]` with the martingale identity for `𝒢`, and use the
-- `ℱ s`-measurability of `X s` coming from the assumed adaptation to `ℱ`.
/-- Remark 9.29 (1): If `ℱ ≤ 𝒢`, a process is a martingale for the larger filtration `𝒢`, and it
is adapted to the smaller filtration `ℱ`, then it is already a martingale for `ℱ`. -/
theorem martingale_of_le_filtration (hℱ𝒢 : ℱ ≤ 𝒢) (hX : Martingale X 𝒢 μ)
    (hXad : Adapted ℱ X) :
    Martingale X ℱ μ := by
  refine ⟨hXad.stronglyAdapted, ?_⟩
  intro s t hst
  -- Rewrite the smaller conditional expectation through the larger filtration.
  have htower : μ[X t | ℱ s] =ᵐ[μ] μ[μ[X t | 𝒢 s] | ℱ s] :=
    (condExp_condExp_of_le (hℱ𝒢 s) (𝒢.le s)).symm
  -- Replace the inner conditional expectation using the martingale property for `𝒢`.
  have hlarge : μ[μ[X t | 𝒢 s] | ℱ s] =ᵐ[μ] μ[X s | ℱ s] :=
    condExp_congr_ae (hX.condExp_ae_eq hst)
  -- Collapse the self-conditioning term because `X s` is already `ℱ s`-measurable.
  have hself : μ[X s | ℱ s] =ᵐ[μ] X s :=
    Filter.EventuallyEq.of_eq <|
      condExp_of_stronglyMeasurable (ℱ.le s) (hXad.stronglyAdapted s) (hX.integrable s)
  exact htower.trans (hlarge.trans hself)

-- Proof sketch: apply the tower property to rewrite `μ[X t | ℱ s]` as
-- `μ[μ[X t | 𝒢 s] | ℱ s]`, use the `𝒢`-submartingale inequality inside the inner conditional
-- expectation, then collapse `μ[X s | ℱ s]` to `X s` using adaptation to `ℱ`.
/-- Remark 9.29 (2): If `ℱ ≤ 𝒢`, a process is a submartingale for the larger filtration `𝒢`, and
it is adapted to the smaller filtration `ℱ`, then it is already a submartingale for `ℱ`. -/
theorem submartingale_of_le_filtration (hℱ𝒢 : ℱ ≤ 𝒢) (hX : Submartingale X 𝒢 μ)
    (hXad : Adapted ℱ X) :
    Submartingale X ℱ μ := by
  refine ⟨hXad.stronglyAdapted, ?_, hX.integrable⟩
  intro s t hst
  -- Rewrite the target conditional expectation through the larger filtration.
  have htower : μ[μ[X t | 𝒢 s] | ℱ s] =ᵐ[μ] μ[X t | ℱ s] :=
    condExp_condExp_of_le (hℱ𝒢 s) (𝒢.le s)
  -- Condition the large-filtration inequality down to `ℱ s`.
  have hmono : μ[X s | ℱ s] ≤ᵐ[μ] μ[μ[X t | 𝒢 s] | ℱ s] :=
    condExp_mono (hX.integrable s) integrable_condExp (hX.ae_le_condExp hst)
  -- Identify `X s` with its conditional expectation because the process is `ℱ`-adapted.
  have hself : μ[X s | ℱ s] =ᵐ[μ] X s :=
    Filter.EventuallyEq.of_eq <|
      condExp_of_stronglyMeasurable (ℱ.le s) (hXad.stronglyAdapted s) (hX.integrable s)
  exact hself.symm.le.trans (hmono.trans_eq htower)

-- Proof sketch: rewrite `μ[X t | ℱ s]` by conditioning first with respect to `𝒢 s`, use the
-- `𝒢`-supermartingale inequality, and then identify `μ[X s | ℱ s]` with `X s` from the
-- adaptation hypothesis.
/-- Remark 9.29 (3): If `ℱ ≤ 𝒢`, a process is a supermartingale for the larger filtration `𝒢`,
and it is adapted to the smaller filtration `ℱ`, then it is already a supermartingale for `ℱ`. -/
theorem supermartingale_of_le_filtration (hℱ𝒢 : ℱ ≤ 𝒢) (hX : Supermartingale X 𝒢 μ)
    (hXad : Adapted ℱ X) :
    Supermartingale X ℱ μ := by
  refine ⟨hXad.stronglyAdapted, ?_, hX.integrable⟩
  intro s t hst
  -- Rewrite the smaller conditional expectation through the larger filtration.
  have htower : μ[X t | ℱ s] =ᵐ[μ] μ[μ[X t | 𝒢 s] | ℱ s] :=
    (condExp_condExp_of_le (hℱ𝒢 s) (𝒢.le s)).symm
  -- Condition the large-filtration supermartingale inequality down to `ℱ s`.
  have hmono : μ[μ[X t | 𝒢 s] | ℱ s] ≤ᵐ[μ] μ[X s | ℱ s] :=
    condExp_mono integrable_condExp (hX.integrable s) (hX.condExp_ae_le hst)
  -- Collapse the self-conditioning term using the small-filtration adaptation.
  have hself : μ[X s | ℱ s] =ᵐ[μ] X s :=
    Filter.EventuallyEq.of_eq <|
      condExp_of_stronglyMeasurable (ℱ.le s) (hXad.stronglyAdapted s) (hX.integrable s)
  exact htower.le.trans (hmono.trans_eq hself)

-- Proof sketch: the natural filtration of `X` is contained in `ℱ` by
-- `adapted_iff_natural_le`, using the strong measurability obtained from `hX.stronglyAdapted`;
-- then apply
-- `martingale_of_le_filtration`.
/-- A martingale is also a martingale with respect to its own natural filtration. -/
theorem martingale_natural_filtration (hX : Martingale X ℱ μ) :
    Martingale X
      (Filtration.natural X (fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i))) μ := by
  let hXm : ∀ i, StronglyMeasurable (X i) := fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i)
  let hXmeas : ∀ i, Measurable (X i) := fun i ↦ (hXm i).measurable
  have hgen : generatedFiltration X hXmeas ≤ ℱ :=
    (adapted_iff_generatedFiltration_le hXmeas).mp hX.stronglyAdapted.adapted
  have hnat : Filtration.natural X hXm ≤ ℱ := by
    simpa [generatedFiltration_eq_natural X hXm] using hgen
  refine martingale_of_le_filtration
    hnat hX (Filtration.stronglyAdapted_natural hXm).adapted

-- Proof sketch: use the containment of the natural filtration in `ℱ` coming from the
-- strong measurability of the submartingale via `adapted_iff_natural_le`, then apply
-- `submartingale_of_le_filtration`.
/-- A submartingale is also a submartingale with respect to its own natural filtration. -/
theorem submartingale_natural_filtration (hX : Submartingale X ℱ μ) :
    Submartingale X
      (Filtration.natural X (fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i))) μ := by
  let hXm : ∀ i, StronglyMeasurable (X i) := fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i)
  let hXmeas : ∀ i, Measurable (X i) := fun i ↦ (hXm i).measurable
  have hgen : generatedFiltration X hXmeas ≤ ℱ :=
    (adapted_iff_generatedFiltration_le hXmeas).mp hX.stronglyAdapted.adapted
  have hnat : Filtration.natural X hXm ≤ ℱ := by
    simpa [generatedFiltration_eq_natural X hXm] using hgen
  refine submartingale_of_le_filtration
    hnat hX (Filtration.stronglyAdapted_natural hXm).adapted

-- Proof sketch: the natural filtration is smaller than `ℱ` by `adapted_iff_natural_le`, and the
-- supermartingale statement then follows from `supermartingale_of_le_filtration`.
/-- A supermartingale is also a supermartingale with respect to its own natural filtration. -/
theorem supermartingale_natural_filtration (hX : Supermartingale X ℱ μ) :
    Supermartingale X
      (Filtration.natural X (fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i))) μ := by
  let hXm : ∀ i, StronglyMeasurable (X i) := fun i ↦ (hX.stronglyAdapted i).mono (ℱ.le i)
  let hXmeas : ∀ i, Measurable (X i) := fun i ↦ (hXm i).measurable
  have hgen : generatedFiltration X hXmeas ≤ ℱ :=
    (adapted_iff_generatedFiltration_le hXmeas).mp hX.stronglyAdapted.adapted
  have hnat : Filtration.natural X hXm ≤ ℱ := by
    simpa [generatedFiltration_eq_natural X hXm] using hgen
  refine supermartingale_of_le_filtration
    hnat hX (Filtration.stronglyAdapted_natural hXm).adapted
