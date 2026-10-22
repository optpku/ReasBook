/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Definition_8_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_20

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u v w

section FiniteTransitionKernelProduct

variable {Ω₀ : Type u} {Ω₁ : Type v} {Ω₂ : Type w}
variable [MeasurableSpace Ω₀] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/- Source-facing layer: Theorem 14.22 builds the rowwise-finite product kernel directly from the
iterated-integral formula. The core/canonical owner for the s-finite setting is
`ProbabilityTheory.Kernel.compProd`; we keep that as a bridge/view only, since outside
`IsSFiniteKernel` mathlib defines `κ₁ ⊗ₖ κ₂` to be `0`. -/

/-- The measurable-set content used to build the product measure
`transitionKernelProduct κ₁ κ₂ ω₀` on `Ω₁ × Ω₂` at a fixed base point `ω₀`. -/
private noncomputable def productContent
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) (ω₀ : Ω₀)
    (s : Set (Ω₁ × Ω₂)) (_hs : MeasurableSet s) : ℝ≥0∞ :=
  ∫⁻ ω₁, κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' s) ∂κ₁ ω₀

-- Proof sketch: for the empty measurable set, every section `Prod.mk ω₁ ⁻¹' ∅` is empty, so the
-- inner kernel values vanish and the outer `lintegral` is zero.
/-- The content defining the product transition measure sends the empty set to `0`. -/
private theorem productContent_empty
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) (ω₀ : Ω₀) :
    productContent κ₁ κ₂ ω₀ ∅ MeasurableSet.empty = 0 := by
  -- Proof comment: every fiber section of `∅` is empty, so the defining integrand vanishes.
  simp [productContent]

-- Proof sketch: apply monotone convergence to the disjoint measurable sections
-- `Prod.mk ω₁ ⁻¹' f i`, use countable additivity of each measure `κ₂ (ω₀, ω₁)`, and exchange the
-- resulting sum with the outer `lintegral`.
/-- The content defining the product transition measure is countably additive on pairwise disjoint
measurable unions. -/
private theorem productContent_iUnion
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) (ω₀ : Ω₀)
    (hκ₂ : IsFiniteTransitionKernel κ₂)
    ⦃f : ℕ → Set (Ω₁ × Ω₂)⦄ (hf : ∀ i, MeasurableSet (f i))
    (hd : Pairwise fun i j ↦ Disjoint (f i) (f j)) :
    productContent κ₁ κ₂ ω₀ (⋃ i, f i) (MeasurableSet.iUnion hf) =
      ∑' i, productContent κ₁ κ₂ ω₀ (f i) (hf i) := by
  -- Proof comment: apply countable additivity on each finite row `Kernel.sectR κ₂ ω₀ ω₁`.
  have hmeas :
      ∀ i, Measurable fun ω₁ ↦ κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' f i) := by
    intro i
    simpa using
      (Kernel.measurable_kernel_prodMk_left_of_finite
        (κ := Kernel.sectR κ₂ ω₀) (t := f i) (ht := hf i)
        (hκs := fun ω₁ ↦ hκ₂ (ω₀, ω₁)))
  have hsum :
      ∀ ω₁, κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' ⋃ i, f i) =
        ∑' i, κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' f i) := by
    intro ω₁
    have hpreDisj :
        Pairwise fun i j ↦ Disjoint (Prod.mk ω₁ ⁻¹' f i) (Prod.mk ω₁ ⁻¹' f j) := by
      intro i j hij
      exact (hd hij).preimage (Prod.mk ω₁)
    have hpreMeas : ∀ i, MeasurableSet (Prod.mk ω₁ ⁻¹' f i) := by
      intro i
      exact measurable_prodMk_left (hf i)
    rw [Set.preimage_iUnion, measure_iUnion hpreDisj hpreMeas]
  -- Proof comment: after the rowwise measure identity, exchange `tsum` with the outer integral.
  simp_rw [productContent, hsum]
  rw [lintegral_tsum fun i ↦ (hmeas i).aemeasurable]

/-- The measure on `Ω₁ × Ω₂` obtained by integrating the fibers of `κ₂` against the row measure
`κ₁ ω₀`. -/
private noncomputable def productMeasure
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    (hκ₂ : IsFiniteTransitionKernel κ₂) (ω₀ : Ω₀) : Measure (Ω₁ × Ω₂) :=
  Measure.ofMeasurable
    (productContent κ₁ κ₂ ω₀)
    (productContent_empty κ₁ κ₂ ω₀)
    (productContent_iUnion κ₁ κ₂ ω₀ hκ₂)

-- Proof sketch: unfold `productMeasure` and apply
-- `Measure.ofMeasurable_apply` to recover the defining iterated integral on measurable sets.
/-- On measurable subsets of `Ω₁ × Ω₂`, the product transition measure is given by the textbook
iterated integral formula. -/
private theorem productMeasure_apply
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    (hκ₂ : IsFiniteTransitionKernel κ₂) (ω₀ : Ω₀)
    {s : Set (Ω₁ × Ω₂)} (hs : MeasurableSet s) :
    productMeasure κ₁ κ₂ hκ₂ ω₀ s =
      ∫⁻ ω₁, κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' s) ∂κ₁ ω₀ := by
  -- Proof comment: `Measure.ofMeasurable_apply` recovers the defining content on measurable sets.
  rw [productMeasure, Measure.ofMeasurable_apply s hs, productContent]

-- Proof sketch: use `Measure.measurable_of_measurable_coe`; for each measurable `s`, Lemma 14.20
-- gives measurability of `ω₀ ↦ ∫⁻ ω₁, κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' s) ∂κ₁ ω₀`.
/-- The family of product measures depends measurably on the base point `ω₀`. -/
private theorem measurable_productMeasure
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    (hκ₁ : IsFiniteTransitionKernel κ₁) (hκ₂ : IsFiniteTransitionKernel κ₂) :
    Measurable (productMeasure κ₁ κ₂ hκ₂) := by
  -- Route correction: the measurable-lintegral bridge here needs the finite-row hypotheses.
  refine Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
  let t : Set ((Ω₀ × Ω₁) × Ω₂) := {q | (q.1.2, q.2) ∈ s}
  have ht : MeasurableSet t := by
    dsimp [t]
    exact (measurable_fst.snd.prodMk measurable_snd) hs
  have hsection :
      Measurable fun p : Ω₀ × Ω₁ ↦ κ₂ p (Prod.mk p ⁻¹' t) := by
    exact Kernel.measurable_kernel_prodMk_left_of_finite
      (κ := κ₂) ht (fun p ↦ hκ₂ p)
  have hsection' :
      Measurable fun p : Ω₀ × Ω₁ ↦ κ₂ p (Prod.mk p.2 ⁻¹' s) := by
    simpa [t] using hsection
  have happly :
      (fun b ↦ (productMeasure κ₁ κ₂ hκ₂ b) s) =
        fun b ↦ ∫⁻ ω₁, κ₂ (b, ω₁) (Prod.mk ω₁ ⁻¹' s) ∂κ₁ b := by
    funext b
    exact productMeasure_apply κ₁ κ₂ hκ₂ b hs
  -- Proof comment: Lemma 14.20 now applies to the jointly measurable section-mass integrand.
  rw [happly]
  exact measurable_lintegral_finite_transition_kernel κ₁ hκ₁ hsection'

/-- The source-facing product of a kernel `κ₁ : Ω₀ → Ω₁` and a kernel
`κ₂ : Ω₀ × Ω₁ → Ω₂`, defined rowwise by the iterated integral from Theorem 14.22. -/
noncomputable def transitionKernelProduct
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂) : Kernel Ω₀ (Ω₁ × Ω₂) :=
  @dite (Kernel Ω₀ (Ω₁ × Ω₂)) (IsFiniteTransitionKernel κ₁ ∧ IsFiniteTransitionKernel κ₂)
    (Classical.propDecidable _)
    (fun h ↦ ⟨productMeasure κ₁ κ₂ h.2, measurable_productMeasure κ₁ κ₂ h.1 h.2⟩)
    (fun _ ↦ 0)

-- Proof sketch: this is the corresponding measurable-set formula for the kernel obtained by
-- packaging `productMeasure` into a `Kernel`.
/-- The product transition kernel evaluates on measurable sets by the same iterated integral
formula as its underlying row measures. -/
theorem transitionKernelProduct_apply
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    (hκ₁ : IsFiniteTransitionKernel κ₁) (hκ₂ : IsFiniteTransitionKernel κ₂) (ω₀ : Ω₀)
    {s : Set (Ω₁ × Ω₂)} (hs : MeasurableSet s) :
    transitionKernelProduct κ₁ κ₂ ω₀ s =
      ∫⁻ ω₁, κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' s) ∂κ₁ ω₀ := by
  -- Proof comment: under the finite-row hypotheses, `transitionKernelProduct` is the
  -- `productMeasure` branch of its defining `if`.
  simp [transitionKernelProduct, hκ₁, hκ₂, productMeasure_apply, hs]

-- Proof sketch: `Kernel.prodMkLeft Ω₀ κ` has fiber `(ω₀, ω₁) ↦ κ ω₁`, so rowwise finiteness is
-- inherited immediately from the corresponding fiber of `κ`.
/-- Viewing a kernel `κ : Ω₁ → Ω₂` as a kernel on `Ω₀ × Ω₁` independent of `Ω₀` preserves rowwise
finiteness. -/
private theorem isFiniteTransitionKernel_prodMkLeft
    (κ : Kernel Ω₁ Ω₂) (hκ : IsFiniteTransitionKernel κ) :
    IsFiniteTransitionKernel (Kernel.prodMkLeft Ω₀ κ) := by
  intro ω
  simpa [Kernel.prodMkLeft_apply] using hκ ω.2

-- Proof sketch: compare both kernels on measurable sets; the source-facing definition and
-- mathlib's `κ₁ ⊗ₖ κ₂` satisfy the same rectangle-section integral formula, so extensionality gives
-- equality.
/-- Under the stronger s-finiteness assumptions from mathlib, the source-facing product kernel
agrees with the canonical composition-product `κ₁ ⊗ₖ κ₂`. -/
theorem transitionKernelProduct_eq_compProd
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    [IsSFiniteKernel κ₁] [IsSFiniteKernel κ₂]
    (hκ₁ : IsFiniteTransitionKernel κ₁) (hκ₂ : IsFiniteTransitionKernel κ₂) :
    transitionKernelProduct κ₁ κ₂ = κ₁ ⊗ₖ κ₂ := by
  ext ω₀ s hs
  -- Proof comment: both kernels have the same measurable-set evaluation formula.
  rw [transitionKernelProduct_apply κ₁ κ₂ hκ₁ hκ₂ ω₀ hs, Kernel.compProd_apply hs]

/-- Helper for Theorem 14.22: each truncation slice
`{ω₁ | κ₂ (ω₀, ω₁) Set.univ < n + 1} ×ˢ Set.univ` has finite product-kernel mass. -/
private theorem transitionKernelProduct_coverSlice_lt_top
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    (hκ₁ : IsFiniteTransitionKernel κ₁) (hκ₂ : IsFiniteTransitionKernel κ₂)
    (ω₀ : Ω₀) (n : ℕ) :
    transitionKernelProduct κ₁ κ₂ ω₀
      ({ω₁ | κ₂ (ω₀, ω₁) Set.univ < n + 1} ×ˢ Set.univ) < ∞ := by
  let B : Set Ω₁ := {ω₁ | κ₂ (ω₀, ω₁) Set.univ < n + 1}
  have hBMeas : MeasurableSet B := by
    refine measurableSet_lt ?_ measurable_const
    simpa [B] using Kernel.measurable_coe (Kernel.sectR κ₂ ω₀) MeasurableSet.univ
  have hpointwise :
      ∀ ω₁,
        κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' (B ×ˢ Set.univ)) ≤
          B.indicator (fun _ ↦ (n + 1 : ℝ≥0∞)) ω₁ := by
    intro ω₁
    by_cases hω₁ : ω₁ ∈ B
    · simpa [B, hω₁] using le_of_lt hω₁
    · simp [B, hω₁]
  have hBFinite : κ₁ ω₀ B < ∞ := by
    exact lt_of_le_of_lt (measure_mono (Set.subset_univ B)) (hκ₁ ω₀).measure_univ_lt_top
  have hbound :
      transitionKernelProduct κ₁ κ₂ ω₀ (B ×ˢ Set.univ) ≤ (n + 1 : ℝ≥0∞) * κ₁ ω₀ B := by
    rw [transitionKernelProduct_apply κ₁ κ₂ hκ₁ hκ₂ ω₀ (hBMeas.prod MeasurableSet.univ)]
    calc
      ∫⁻ ω₁, κ₂ (ω₀, ω₁) (Prod.mk ω₁ ⁻¹' (B ×ˢ Set.univ)) ∂κ₁ ω₀
          ≤ ∫⁻ ω₁, B.indicator (fun _ ↦ (n + 1 : ℝ≥0∞)) ω₁ ∂κ₁ ω₀ := by
            exact lintegral_mono fun ω₁ ↦ hpointwise ω₁
      _ = (n + 1 : ℝ≥0∞) * κ₁ ω₀ B := by
        simpa using
          (lintegral_indicator_const_comp (μ := κ₁ ω₀) measurable_id hBMeas
            (n + 1 : ℝ≥0∞))
  -- Proof comment: the truncation bound reduces the mass to a finite constant multiple.
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top (by simp) hBFinite)

-- Proof sketch: for each `ω₀`, use the finite-fiber assumption on `κ₂` to cover `Ω₁ × Ω₂` by the
-- sets `A_{ω₀,n} ×ˢ univ` from the textbook proof, each having finite product-kernel mass; then
-- package the rowwise σ-finiteness into `IsSigmaFiniteTransitionKernel`.
/-- Theorem 14.22: if `κ₁ : Ω₀ → Ω₁` and `κ₂ : Ω₀ × Ω₁ → Ω₂` are finite transition kernels, then
their product kernel is a rowwise σ-finite transition kernel from `Ω₀` to `Ω₁ × Ω₂`. -/
theorem transitionKernelProduct_isSigmaFiniteTransitionKernel
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    (hκ₁ : IsFiniteTransitionKernel κ₁) (hκ₂ : IsFiniteTransitionKernel κ₂) :
    IsSigmaFiniteTransitionKernel (transitionKernelProduct κ₁ κ₂) := by
  intro ω₀
  let cover : Set (Set (Ω₁ × Ω₂)) := Set.range fun n : ℕ =>
    {ω₁ | κ₂ (ω₀, ω₁) Set.univ < n + 1} ×ˢ Set.univ
  have hcount : cover.Countable := Set.countable_range _
  have hfinite :
      ∀ s ∈ cover, transitionKernelProduct κ₁ κ₂ ω₀ s < ∞ := by
    intro s hs
    rcases hs with ⟨n, rfl⟩
    exact transitionKernelProduct_coverSlice_lt_top κ₁ κ₂ hκ₁ hκ₂ ω₀ n
  have hcover : ⋃₀ cover = Set.univ := by
    ext p
    constructor
    · intro _
      simp
    · intro _
      have hpFinite : κ₂ (ω₀, p.1) Set.univ < ∞ := (hκ₂ (ω₀, p.1)).measure_univ_lt_top
      obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hpFinite.ne
      refine Set.mem_sUnion.2 ?_
      refine ⟨{ω₁ | κ₂ (ω₀, ω₁) Set.univ < n + 1} ×ˢ Set.univ, ⟨n, rfl⟩, ?_⟩
      exact ⟨lt_of_lt_of_le hn (by exact_mod_cast Nat.le_succ n), by simp⟩
  -- Proof comment: the textbook slices form a countable measurable cover by finite-mass sets.
  exact Measure.sigmaFinite_of_countable hcount hfinite hcover

-- Proof sketch: evaluate the product kernel on `univ`; the inner total masses are at most `1`
-- almost everywhere, so the iterated integral is bounded by the total mass of `κ₁`, which is also
-- at most `1`.
/-- Sub-Markov kernels are stable under the product construction of Theorem 14.22. -/
theorem transitionKernelProduct_isSubMarkovKernel
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    (hκ₁ : IsSubMarkovKernel κ₁) (hκ₂ : IsSubMarkovKernel κ₂) :
    IsSubMarkovKernel (transitionKernelProduct κ₁ κ₂) := by
  letI : IsFiniteKernel κ₁ := ⟨⟨1, ENNReal.one_lt_top, hκ₁⟩⟩
  letI : IsFiniteKernel κ₂ := ⟨⟨1, ENNReal.one_lt_top, hκ₂⟩⟩
  let hκ₁Finite : IsFiniteTransitionKernel κ₁ := hκ₁.isFiniteTransitionKernel
  let hκ₂Finite : IsFiniteTransitionKernel κ₂ := hκ₂.isFiniteTransitionKernel
  have hκ₂_bound : κ₂.bound ≤ 1 := by
    refine iSup_le fun ω ↦ ?_
    simpa [Kernel.bound] using hκ₂ ω
  intro ω₀
  calc
    transitionKernelProduct κ₁ κ₂ ω₀ Set.univ = (κ₁ ⊗ₖ κ₂) ω₀ Set.univ := by
      rw [transitionKernelProduct_eq_compProd κ₁ κ₂ hκ₁Finite hκ₂Finite]
    _ ≤ κ₁ ω₀ Set.univ * κ₂.bound := Kernel.compProd_apply_univ_le κ₁ κ₂ ω₀
    _ ≤ κ₁ ω₀ Set.univ * 1 := mul_le_mul_right hκ₂_bound _
    _ = κ₁ ω₀ Set.univ := by simp
    _ ≤ 1 := hκ₁ ω₀

-- Proof sketch: evaluate the product kernel on `univ`; now both total masses are exactly `1`, so
-- the iterated integral equals `1` for every base point.
/-- Markov kernels are stable under the product construction of Theorem 14.22. -/
theorem transitionKernelProduct_isMarkovKernel
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel (Ω₀ × Ω₁) Ω₂)
    [IsMarkovKernel κ₁] [IsMarkovKernel κ₂] :
    IsMarkovKernel (transitionKernelProduct κ₁ κ₂) := by
  let hκ₁Finite : IsFiniteTransitionKernel κ₁ :=
    (isSubMarkovKernel_of_isMarkovKernel κ₁).isFiniteTransitionKernel
  let hκ₂Finite : IsFiniteTransitionKernel κ₂ :=
    (isSubMarkovKernel_of_isMarkovKernel κ₂).isFiniteTransitionKernel
  simpa [transitionKernelProduct_eq_compProd κ₁ κ₂ hκ₁Finite hκ₂Finite] using
    (inferInstance : IsMarkovKernel (κ₁ ⊗ₖ κ₂))

-- Proof sketch: specialize `transitionKernelProduct_apply` to `Kernel.prodMkLeft Ω₀ κ₂`, then use
-- `Kernel.sectR_prodMkLeft` or the defining formula of `prodMkLeft` to remove the dummy `Ω₀`
-- coordinate from the inner kernel.
/-- If the second factor is a kernel `κ₂ : Ω₁ → Ω₂`, viewing it as
`Kernel.prodMkLeft Ω₀ κ₂ : Kernel (Ω₀ × Ω₁) Ω₂` recovers the textbook supplementary definition of
the product. -/
theorem transitionKernelProduct_prodMkLeft_apply
    (κ₁ : Kernel Ω₀ Ω₁) (κ₂ : Kernel Ω₁ Ω₂)
    (hκ₁ : IsFiniteTransitionKernel κ₁) (hκ₂ : IsFiniteTransitionKernel κ₂) (ω₀ : Ω₀)
    {s : Set (Ω₁ × Ω₂)} (hs : MeasurableSet s) :
    transitionKernelProduct κ₁ (Kernel.prodMkLeft Ω₀ κ₂) ω₀ s =
      ∫⁻ ω₁, κ₂ ω₁ (Prod.mk ω₁ ⁻¹' s) ∂κ₁ ω₀ := by
  -- Proof comment: `Kernel.prodMkLeft` makes the inner kernel independent of `Ω₀`.
  simpa [Kernel.prodMkLeft_apply'] using
    transitionKernelProduct_apply κ₁ (Kernel.prodMkLeft Ω₀ κ₂) hκ₁
      (isFiniteTransitionKernel_prodMkLeft (Ω₀ := Ω₀) κ₂ hκ₂) ω₀ hs

end FiniteTransitionKernelProduct
