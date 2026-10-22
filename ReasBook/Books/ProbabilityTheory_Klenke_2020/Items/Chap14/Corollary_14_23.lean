/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Theorem_14_22

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u v

section

variable {Ω₁ : Type u} {Ω₂ : Type v}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/- Source-facing layer: under the rowwise-finite hypothesis `IsFiniteTransitionKernel κ`, the
canonical chapter-level owner is the product kernel from Theorem 14.22 specialized to the
constant first-step kernel `Kernel.const Unit μ` and `Kernel.prodMkLeft Unit κ`. The stronger
mathlib owner `μ ⊗ₘ κ` requires `IsSFiniteKernel κ`, so it is used only for the Markov corollary
below, not for this theorem. -/
-- Proof sketch: specialize Theorem 14.22 to `Kernel.const Unit μ` and `Kernel.prodMkLeft Unit κ`;
-- this gives the witness measure on `Ω₁ × Ω₂`, its σ-finiteness, and the rectangle formula.
-- Uniqueness is then the source-facing rectangle uniqueness statement for that specialized
-- product-kernel construction.
/-- Helper for Corollary 14.23: viewing `κ : Ω₁ → Ω₂` as a kernel on `Unit × Ω₁` independent of
the `Unit` coordinate preserves rowwise finiteness. -/
private theorem isFiniteTransitionKernel_prodMkLeft_unit
    (κ : Kernel Ω₁ Ω₂) (hκ : IsFiniteTransitionKernel κ) :
    IsFiniteTransitionKernel (Kernel.prodMkLeft Unit κ) := by
  -- Proof comment: `Kernel.prodMkLeft` only inserts a dummy `Unit` coordinate into the source.
  intro ω
  simpa [Kernel.prodMkLeft_apply] using hκ ω.2

/-- Helper for Corollary 14.23: any measure satisfying the rectangle formula is finite on the
truncation rectangles `{ω₁ | κ ω₁ Set.univ < n + 1} ×ˢ Set.univ`. -/
private theorem rectangleFormula_coverSlice_ltTop
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)
    {ν : Measure (Ω₁ × Ω₂)}
    (hrect : ∀ A₁ : Set Ω₁, ∀ A₂ : Set Ω₂,
      MeasurableSet A₁ → MeasurableSet A₂ →
        ν (A₁ ×ˢ A₂) = ∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ)
    (n : ℕ) :
    ν ({ω₁ | κ ω₁ Set.univ < n + 1} ×ˢ (Set.univ : Set Ω₂)) < ∞ := by
  let B : Set Ω₁ := {ω₁ | κ ω₁ Set.univ < n + 1}
  have hBMeas : MeasurableSet B := by
    -- Proof comment: the truncation slice is measurable because `ω₁ ↦ κ ω₁ univ` is measurable.
    refine measurableSet_lt ?_ measurable_const
    simpa [B] using Kernel.measurable_coe κ MeasurableSet.univ
  have hpointwise :
      ∀ ω₁,
        B.indicator (fun ω₁ ↦ κ ω₁ Set.univ) ω₁ ≤
          B.indicator (fun _ ↦ (n + 1 : ℝ≥0∞)) ω₁ := by
    intro ω₁
    by_cases hω₁ : ω₁ ∈ B
    · simpa [B, hω₁] using le_of_lt hω₁
    · simp [B, hω₁]
  have hbound :
      ν (B ×ˢ Set.univ) ≤ (n + 1 : ℝ≥0∞) * μ B := by
    rw [hrect B Set.univ hBMeas MeasurableSet.univ, ← lintegral_indicator hBMeas]
    calc
      ∫⁻ ω₁, B.indicator (fun ω₁ ↦ κ ω₁ Set.univ) ω₁ ∂μ
          ≤ ∫⁻ ω₁, B.indicator (fun _ ↦ (n + 1 : ℝ≥0∞)) ω₁ ∂μ := by
            exact lintegral_mono fun ω₁ ↦ hpointwise ω₁
      _ = (n + 1 : ℝ≥0∞) * μ B := by
        simpa using
          (lintegral_indicator_const_comp (μ := μ) measurable_id hBMeas
            (n + 1 : ℝ≥0∞))
  -- Proof comment: the rectangle mass is bounded by a finite constant multiple of the finite
  -- measure `μ B`.
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top (by simp) (measure_lt_top μ B))

/-- Helper for Corollary 14.23: the truncation rectangles
`{ω₁ | κ ω₁ Set.univ < n + 1} ×ˢ Set.univ` form a countable cover of `Ω₁ × Ω₂`. -/
private theorem transitionKernelRectangleCover_spanning
    (κ : Kernel Ω₁ Ω₂) (hκ : IsFiniteTransitionKernel κ) :
    (⋃ n : ℕ, ({ω₁ | κ ω₁ Set.univ < n + 1} ×ˢ (Set.univ : Set Ω₂))) = Set.univ := by
  ext p
  constructor
  · intro _
    simp
  · intro _
    have hpFinite : κ p.1 Set.univ < ∞ := (hκ p.1).measure_univ_lt_top
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hpFinite.ne
    -- Proof comment: every row mass is finite, so it lands below some integer truncation level.
    refine Set.mem_iUnion.2 ⟨n, ?_⟩
    exact ⟨lt_of_lt_of_le hn (by exact_mod_cast Nat.le_succ n), by simp⟩

/-- Helper for Corollary 14.23: the rectangle formula uniquely determines the product measure. -/
private theorem eq_of_agree_on_product_rectangles
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)
    (hκ : IsFiniteTransitionKernel κ) {ν₁ ν₂ : Measure (Ω₁ × Ω₂)}
    (h₁ : ∀ A₁ : Set Ω₁, ∀ A₂ : Set Ω₂,
      MeasurableSet A₁ → MeasurableSet A₂ →
        ν₁ (A₁ ×ˢ A₂) = ∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ)
    (h₂ : ∀ A₁ : Set Ω₁, ∀ A₂ : Set Ω₂,
      MeasurableSet A₁ → MeasurableSet A₂ →
        ν₂ (A₁ ×ˢ A₂) = ∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ) :
    ν₁ = ν₂ := by
  let C : Set (Set (Ω₁ × Ω₂)) :=
    Set.image2 (· ×ˢ ·) {A₁ : Set Ω₁ | MeasurableSet A₁} {A₂ : Set Ω₂ | MeasurableSet A₂}
  let B : ℕ → Set (Ω₁ × Ω₂) :=
    fun n ↦ {ω₁ | κ ω₁ Set.univ < n + 1} ×ˢ (Set.univ : Set Ω₂)
  have hB_mem : ∀ n, B n ∈ C := by
    intro n
    have hSliceMeas : MeasurableSet {ω₁ | κ ω₁ Set.univ < n + 1} := by
      -- Proof comment: the generating cover uses measurable truncation slices.
      refine measurableSet_lt ?_ measurable_const
      exact Kernel.measurable_coe κ MeasurableSet.univ
    simpa [B, C] using Set.mem_image2_of_mem hSliceMeas MeasurableSet.univ
  have hB_finite : ∀ n, ν₁ (B n) < ∞ := by
    -- Proof comment: each covering rectangle has finite mass by the truncation estimate.
    intro n
    simpa [B] using rectangleFormula_coverSlice_ltTop μ κ h₁ n
  have hB_spanning : ⋃ n, B n = Set.univ := by
    -- Proof comment: the rowwise finiteness cover from `κ` spans the whole product space.
    simpa [B] using transitionKernelRectangleCover_spanning κ hκ
  let hfiniteRectangles : ν₁.FiniteSpanningSetsIn C := .mk B hB_mem hB_finite hB_spanning
  -- Proof comment: equality on the generating π-system of rectangles extends to all measurable
  -- sets once one measure has a finite spanning family inside that generator.
  exact hfiniteRectangles.ext generateFrom_prod.symm isPiSystem_prod <| by
    rintro s ⟨A₁, hA₁, A₂, hA₂, rfl⟩
    rw [h₁ A₁ A₂ hA₁ hA₂, h₂ A₁ A₂ hA₁ hA₂]

/-- Corollary 14.23: a finite measure `μ` and a finite transition kernel `κ` determine a unique
σ-finite measure on the product space whose value on measurable rectangles is
`∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ`. -/
theorem existsUnique_sigmaFinite_product_measure_of_isFiniteTransitionKernel
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂) (hκ : IsFiniteTransitionKernel κ) :
    ∃! ν : Measure (Ω₁ × Ω₂),
      SigmaFinite ν ∧
        ∀ A₁ : Set Ω₁, ∀ A₂ : Set Ω₂,
          MeasurableSet A₁ → MeasurableSet A₂ →
            ν (A₁ ×ˢ A₂) = ∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ := by
  let κμ : Kernel Unit Ω₁ := Kernel.const Unit μ
  let κ' : Kernel (Unit × Ω₁) Ω₂ := Kernel.prodMkLeft Unit κ
  let ν : Measure (Ω₁ × Ω₂) := transitionKernelProduct κμ κ' ()
  have hconst : IsFiniteTransitionKernel κμ := by
    -- Proof comment: the constant kernel is finite because `μ` is a finite measure.
    simpa [κμ] using
      (isFiniteTransitionKernel_of_isFiniteKernel (Kernel.const Unit μ) :
        IsFiniteTransitionKernel (Kernel.const Unit μ))
  have hprodMkLeft : IsFiniteTransitionKernel κ' := by
    -- Proof comment: `κ'` is just `κ` with a dummy `Unit` coordinate added to the source.
    simpa [κ'] using isFiniteTransitionKernel_prodMkLeft_unit κ hκ
  have hν_sigma : SigmaFinite ν := by
    -- Proof comment: Theorem 14.22 gives rowwise σ-finiteness for the specialized product kernel.
    simpa [ν, κμ, κ'] using
      transitionKernelProduct_isSigmaFiniteTransitionKernel κμ κ' hconst hprodMkLeft ()
  have hν_rect :
      ∀ A₁ : Set Ω₁, ∀ A₂ : Set Ω₂,
        MeasurableSet A₁ → MeasurableSet A₂ →
          ν (A₁ ×ˢ A₂) = ∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ := by
    intro A₁ A₂ hA₁ hA₂
    -- Proof comment: on rectangles, the specialized product kernel reduces to the textbook
    -- iterated-integral formula.
    simp only [ν, κ']
    rw [transitionKernelProduct_prodMkLeft_apply κμ κ hconst hκ () (hA₁.prod hA₂)]
    rw [Kernel.const_apply]
    rw [← lintegral_indicator hA₁]
    refine lintegral_congr_ae <| Filter.Eventually.of_forall ?_
    intro ω₁
    by_cases hω₁ : ω₁ ∈ A₁
    · simp [hω₁]
    · simp [hω₁]
  refine ⟨ν, ?_, ?_⟩
  · exact ⟨hν_sigma, hν_rect⟩
  · intro ν' hν'
    rcases hν' with ⟨_, hν'_rect⟩
    -- Proof comment: the competitor's sigma-finiteness is redundant because the rectangle formula
    -- already forces the same finite spanning cover used in the uniqueness argument.
    exact (eq_of_agree_on_product_rectangles μ κ hκ hν_rect hν'_rect).symm

/-- The canonical product measure from Corollary 14.23 attached to a finite measure `μ` and a
finite transition kernel `κ`. -/
noncomputable def finiteTransitionKernelProductMeasure
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)
    (hκ : IsFiniteTransitionKernel κ) : Measure (Ω₁ × Ω₂) :=
  Classical.choose <|
    existsUnique_sigmaFinite_product_measure_of_isFiniteTransitionKernel μ κ hκ

private theorem finiteTransitionKernelProductMeasure_spec
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)
    (hκ : IsFiniteTransitionKernel κ) :
    SigmaFinite (finiteTransitionKernelProductMeasure μ κ hκ) ∧
      ∀ A₁ : Set Ω₁, ∀ A₂ : Set Ω₂,
        MeasurableSet A₁ → MeasurableSet A₂ →
          finiteTransitionKernelProductMeasure μ κ hκ (A₁ ×ˢ A₂) =
            ∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ :=
  (Classical.choose_spec <|
    existsUnique_sigmaFinite_product_measure_of_isFiniteTransitionKernel μ κ hκ).1

/-- The canonical product measure from Corollary 14.23 is sigma-finite. -/
theorem sigmaFinite_finiteTransitionKernelProductMeasure
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)
    (hκ : IsFiniteTransitionKernel κ) :
    SigmaFinite (finiteTransitionKernelProductMeasure μ κ hκ) :=
  (finiteTransitionKernelProductMeasure_spec μ κ hκ).1

/-- On measurable rectangles, the canonical product measure from Corollary 14.23 satisfies the
textbook transition-kernel formula. -/
theorem finiteTransitionKernelProductMeasure_apply_prod
    (μ : Measure Ω₁) [IsFiniteMeasure μ] (κ : Kernel Ω₁ Ω₂)
    (hκ : IsFiniteTransitionKernel κ)
    (A₁ : Set Ω₁) (A₂ : Set Ω₂)
    (hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂) :
    finiteTransitionKernelProductMeasure μ κ hκ (A₁ ×ˢ A₂) =
      ∫⁻ ω₁ in A₁, κ ω₁ A₂ ∂μ :=
  (finiteTransitionKernelProductMeasure_spec μ κ hκ).2 A₁ A₂ hA₁ hA₂

-- Proof sketch: use the canonical mathlib instance stating that the composition-product of a
-- probability measure with a Markov kernel is again a probability measure.
/- The composition-product of a probability measure with a stochastic kernel is already the
canonical mathlib owner instance on `μ ⊗ₘ κ`, so this corollary is recorded by direct reuse
rather than a parallel local wrapper theorem. -/
example
    (μ : Measure Ω₁) [IsProbabilityMeasure μ] (κ : Kernel Ω₁ Ω₂) [IsMarkovKernel κ] :
    IsProbabilityMeasure (μ ⊗ₘ κ) :=
  inferInstance

end
