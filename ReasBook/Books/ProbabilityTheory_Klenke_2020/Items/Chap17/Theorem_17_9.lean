/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Definition_9_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

variable {I : AddSubmonoid NNReal}
variable {Ω : Type v} [mΩ : MeasurableSpace Ω]
variable {E : Type w} [mE : MeasurableSpace E]

/-- The shifted future path of a process `X` after time `s`, viewed again as an `I`-indexed path.
-/
def futurePath (X : I → Ω → E) (s : I) : Ω → I → E :=
  fun ω t ↦ X (t + s) ω

/-- The ordered future coordinates of a process `X` after time `s`. -/
def futurePathCoordinates {n : ℕ} (X : I → Ω → E) (s : I) (t : Fin n → I) :
    Ω → Fin n → E :=
  fun ω i ↦ X (t i + s) ω

/-- The Chapter 17 future-path conditional-expectation formula for bounded measurable path
functionals on `I → E` and a path-space kernel `κ`. -/
def HasFuturePathConditionalExpectationFormula
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E)) : Prop :=
  ∀ ⦃f : (I → E) → ℝ⦄, Measurable f → Bornology.IsBounded (Set.range f) →
    ∀ s x, 0 ≤ s →
      (P x)[fun ω ↦ f (futurePath X s ω) | generatedFiltrationSpace X s] =ᵐ[
        (P x : Measure Ω)]
        fun ω ↦ ∫ y, f y ∂κ (X s ω)

/-- Helper for Theorem 17.9: the ordered finite-coordinate future-path conditional-expectation
formula for bounded measurable cylinder functionals along an ordered time family. -/
def HasOrderedFutureCoordinateConditionalExpectationFormula
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E)) : Prop :=
  ∀ ⦃n : ℕ⦄ ⦃f : (Fin n → E) → ℝ⦄, Measurable f → Bornology.IsBounded (Set.range f) →
    ∀ ⦃t : Fin n → I⦄, Monotone t → ∀ s x, 0 ≤ s →
      (P x)[fun ω ↦ f (futurePathCoordinates X s t ω) | generatedFiltrationSpace X s] =ᵐ[
        (P x : Measure Ω)]
        fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω)

/-- Helper for Theorem 17.9: the shifted future-path map is measurable once the process is
coordinatewise measurable. -/
lemma measurable_futurePath
    (X : I → Ω → E) (hX_meas : ∀ t, Measurable (X t)) (s : I) :
    Measurable (futurePath X s) := by
  -- Proof comment: each future coordinate is the measurable slice `X (t + s)`.
  refine measurable_pi_lambda _ fun t ↦ ?_
  simpa [futurePath] using hX_meas (t + s)

/-- Helper for Theorem 17.9: the finite tuple of ordered future coordinates is measurable once
the process is coordinatewise measurable. -/
lemma measurable_futurePathCoordinates {n : ℕ}
    (X : I → Ω → E) (hX_meas : ∀ t, Measurable (X t)) (s : I) (t : Fin n → I) :
    Measurable (futurePathCoordinates X s t) := by
  -- Proof comment: each tuple coordinate is the measurable slice `X (t i + s)`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [futurePathCoordinates] using hX_meas (t i + s)

/-- Helper for Theorem 17.9: projecting a path onto a finite ordered coordinate family is
measurable. -/
lemma measurable_pathCoordinateProjection {n : ℕ} (t : Fin n → I) :
    Measurable (fun y : I → E ↦ fun i ↦ y (t i)) := by
  -- Proof comment: each tuple coordinate is just evaluation at the selected time `t i`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply (t i)

/-- Helper for Theorem 17.9: once every coordinate of `X` is measurable, the generated history
σ-algebra at time `s` is contained in the ambient measurable space on `Ω`. -/
lemma generatedFiltrationSpace_le_ambient_of_measurable
    (X : I → Ω → E) (hX_meas : ∀ t, Measurable (X t)) (s : I) :
    generatedFiltrationSpace X s ≤ mΩ := by
  -- Proof comment: every comap appearing in the defining supremum already lies below the ambient
  -- measurable space because the corresponding coordinate map is measurable.
  rw [generatedFiltrationSpace]
  refine iSup₂_le fun t ht ↦ ?_
  exact (hX_meas t).comap_le

/-- Helper for Theorem 17.9: real-valued indicator functions take only the values `0` and `1`,
so their range is bounded. -/
lemma isBounded_range_indicator_one {α : Type*} (A : Set α) :
    Bornology.IsBounded (Set.range (Set.indicator A fun _ : α ↦ (1 : ℝ))) := by
  -- Proof comment: the indicator can only output `0` or `1`, so its range sits inside the union
  -- of those two singleton sets.
  have h01 :
      Set.range (Set.indicator A fun _ : α ↦ (1 : ℝ)) ⊆
        ({(0 : ℝ)} ∪ ({(1 : ℝ)} : Set ℝ)) := by
    intro r hr
    rcases hr with ⟨x, rfl⟩
    by_cases hx : x ∈ A
    · right
      simp [hx]
    · left
      simp [hx]
  have hBound01 :
      Bornology.IsBounded (({(0 : ℝ)} : Set ℝ) ∪ ({(1 : ℝ)} : Set ℝ)) :=
    Bornology.IsBounded.union Bornology.isBounded_singleton Bornology.isBounded_singleton
  exact hBound01.subset h01

/-- Helper for Theorem 17.9: the `s = 0` specialization of the future-path conditional-
expectation formula identifies the path kernel rows with the actual path laws of the process. -/
lemma pathLaw_eq_kernel_of_futurePathFormula_zero
    [MeasurableSingletonClass E]
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hX_meas : ∀ t, Measurable (X t))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hFuture : HasFuturePathConditionalExpectationFormula X P κ) :
    ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun t : I ↦ X t ω) := by
  intro x
  let μ : Measure Ω := (P x : Measure Ω)
  let pathMap : Ω → I → E := fun ω t ↦ X t ω
  have hpathMap_meas : Measurable pathMap := by
    -- Proof comment: the full path map is the zero-shifted future-path map.
    refine measurable_pi_lambda _ fun t ↦ ?_
    simpa [pathMap] using hX_meas t
  have hpath_eq_future0 : pathMap = futurePath X 0 := by
    -- Proof comment: shifting by time `0` leaves the full path unchanged.
    funext ω t
    simp [pathMap, futurePath]
  have hX0_ae : (fun ω ↦ X 0 ω) =ᵐ[μ] fun _ ↦ x := by
    -- Proof comment: the initial-state hypothesis says that the event `X 0 = x` has
    -- probability one under `P x`.
    have hmem :
        {ω | X 0 ω ∈ ({x} : Set E)} ∈ ae μ := by
      refine
        (MeasureTheory.mem_ae_iff_prob_eq_one
          ((hX_meas 0) (measurableSet_singleton x))).2 ?_
      simpa [μ] using hX0 x
    filter_upwards [hmem] with ω hω
    simpa using hω
  have hreal_of_measurable :
      ∀ ⦃A : Set (I → E)⦄, MeasurableSet A → ((μ.map pathMap).real A) = (κ x).real A := by
    intro A hA
    let indicatorA : (I → E) → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
    have hIndicator_meas : Measurable indicatorA := by
      -- Proof comment: measurable path events give measurable indicator test functions.
      exact Measurable.indicator measurable_const hA
    have hIndicator_int :
        Integrable (fun ω ↦ indicatorA (futurePath X 0 ω)) μ := by
      -- Proof comment: indicator test functions are bounded by `1`, hence integrable on the
      -- probability space `(Ω, P x)`.
      refine Integrable.of_bound
        (hIndicator_meas.comp (measurable_futurePath X hX_meas 0)).aestronglyMeasurable 1 ?_
      refine Filter.Eventually.of_forall fun ω ↦ ?_
      by_cases hω : futurePath X 0 ω ∈ A
      · simp [indicatorA, hω]
      · simp [indicatorA, hω]
    have hfuture_zero :
        μ[fun ω ↦ indicatorA (futurePath X 0 ω) | generatedFiltrationSpace X 0] =ᵐ[μ]
          fun ω ↦ ∫ y, indicatorA y ∂κ (X 0 ω) := by
      -- Proof comment: specialize the assumed future-path conditional-expectation formula to
      -- `s = 0` and the indicator of the measurable path event `A`.
      simpa [μ, indicatorA] using
        hFuture hIndicator_meas (isBounded_range_indicator_one A) 0 x (show (0 : I) ≤ 0 by simp)
    calc
      ((μ.map pathMap).real A)
          = ∫ ω, indicatorA (futurePath X 0 ω) ∂μ := by
              rw [MeasureTheory.map_measureReal_apply hpathMap_meas hA]
              rw [hpath_eq_future0]
              simpa using
                (MeasureTheory.integral_indicator_one
                  ((measurable_futurePath X hX_meas 0) hA)).symm
      _ = ∫ ω,
            (μ[fun ω ↦ indicatorA (futurePath X 0 ω) |
              generatedFiltrationSpace X 0]) ω ∂μ := by
            symm
            exact
              integral_condExp
                (generatedFiltrationSpace_le_ambient_of_measurable X hX_meas 0)
      _ = ∫ ω, ∫ y, indicatorA y ∂κ (X 0 ω) ∂μ := by
            exact integral_congr_ae hfuture_zero
      _ = ∫ ω, ∫ y, indicatorA y ∂κ x ∂μ := by
            refine integral_congr_ae ?_
            filter_upwards [hX0_ae] with ω hω
            simp [hω]
      _ = ∫ ω, (κ x).real A ∂μ := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
            simpa [indicatorA] using
              (MeasureTheory.integral_indicator_one hA)
      _ = (κ x).real A := by
            simp [μ]
  have hκ_univ_ne_top : (κ x) Set.univ ≠ ⊤ := by
    intro htop
    have huniv : ((μ.map pathMap).real Set.univ) = (κ x).real Set.univ :=
      hreal_of_measurable MeasurableSet.univ
    have huniv' : ((μ.map pathMap).real Set.univ) = 0 := by
      simpa [MeasureTheory.Measure.real_def, htop] using huniv
    have hmap_univ : ((μ.map pathMap).real Set.univ) = 1 := by
      have hmap_univ' : ((μ.map pathMap).real Set.univ) = μ.real Set.univ :=
        MeasureTheory.map_measureReal_apply hpathMap_meas MeasurableSet.univ
      simpa [μ] using
        hmap_univ'
    have h10 : (1 : ℝ) = 0 := by
      have : ((μ.map pathMap).real Set.univ) = 0 := huniv'
      simp [hmap_univ] at this
    exact one_ne_zero h10
  have hκ_finite : ∀ A : Set (I → E), (κ x) A ≠ ⊤ := by
    intro A
    refine ne_of_lt <| lt_of_le_of_lt (measure_mono (Set.subset_univ A)) ?_
    simpa using (show ((κ x) Set.univ) < ⊤ from lt_of_le_of_ne le_top hκ_univ_ne_top)
  refine Measure.ext fun A hA ↦ ?_
  have hreal_eq_measure_eq :
      ((μ.map pathMap).real A = (κ x).real A) ↔ (μ.map pathMap) A = (κ x) A := by
    have hκA_finite : (κ x) A ≠ ⊤ := hκ_finite A
    simpa [MeasureTheory.Measure.real_def] using
      (ENNReal.toReal_eq_toReal_iff' (by finiteness) hκA_finite)
  exact (hreal_eq_measure_eq.mp (hreal_of_measurable hA)).symm

/-- Helper for Theorem 17.9: on an additive submonoid of `NNReal` closed under ordered
differences, the source-facing future-path formula is equivalent to its ordered finite-coordinate
restriction. -/
lemma hasOrderedFutureCoordinateConditionalExpectationFormula_of_futurePathFormula
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω)
    (κ : Kernel E (I → E))
    (hFuture : HasFuturePathConditionalExpectationFormula X P κ) :
    HasOrderedFutureCoordinateConditionalExpectationFormula X P κ := by
  intro n f hf_meas hf_bdd t _ht s x hs
  let coordinateProjection : (I → E) → Fin n → E := fun y i ↦ y (t i)
  have hcoordinateProjection_meas : Measurable coordinateProjection := by
    -- Proof comment: each coordinate of the finite projection is just evaluation at `t i`.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_pi_apply (t i)
  have hcomposed_meas : Measurable (fun y ↦ f (coordinateProjection y)) := by
    -- Proof comment: the ordered cylinder functional is a measurable composition of `f` with the
    -- finite coordinate projection.
    exact hf_meas.comp hcoordinateProjection_meas
  have hcomposed_bdd :
      Bornology.IsBounded (Set.range fun y ↦ f (coordinateProjection y)) := by
    -- Proof comment: the composed functional takes values inside the original bounded range of
    -- `f`.
    refine hf_bdd.subset ?_
    intro r hr
    rcases hr with ⟨y, rfl⟩
    exact ⟨coordinateProjection y, rfl⟩
  -- Proof comment: specialize the full future-path formula to the composed finite-coordinate
  -- functional and simplify the resulting path evaluations.
  simpa [coordinateProjection, futurePathCoordinates, futurePath] using
    hFuture hcomposed_meas hcomposed_bdd s x hs

/-- Helper for Theorem 17.9: the ordered-coordinate conditional-expectation formula identifies
the restricted law of future coordinates on any history event with the corresponding mixed kernel
cylinder mass. -/
lemma restrictedFutureCoordinateLaw_eq_mixedKernel_on_historyEvent
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω)
    (κ : Kernel E (I → E))
    (hX_meas : ∀ t, Measurable (X t))
    (hOrdered : HasOrderedFutureCoordinateConditionalExpectationFormula X P κ)
    {n : ℕ} {t : Fin n → I} (ht : Monotone t)
    {A : Set (Fin n → E)} (hA : MeasurableSet A)
    {s : I} {x : E} (hs : 0 ≤ s)
    {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X s] B) :
    ((((P x : Measure Ω).restrict B).map (futurePathCoordinates X s t)).real A) =
      ∫ ω in B, (((κ (X s ω)).map (fun y i ↦ y (t i))).real A) ∂(P x : Measure Ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let indicatorA : (Fin n → E) → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
  let coordinateProjection : (I → E) → Fin n → E := fun y i ↦ y (t i)
  have hcoords_meas : Measurable (futurePathCoordinates X s t) := by
    -- Proof comment: the future-coordinate tuple is measurable coordinatewise.
    exact measurable_futurePathCoordinates X hX_meas s t
  have hcoordinateProjection_meas : Measurable coordinateProjection := by
    -- Proof comment: the tuple projection from path space to the chosen coordinates is
    -- coordinatewise measurable.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_pi_apply (t i)
  have hIndicator_meas : Measurable indicatorA := by
    -- Proof comment: measurable cylinder sets give measurable indicator test functions.
    exact Measurable.indicator measurable_const hA
  have hIndicator_int :
      Integrable (fun ω ↦ indicatorA (futurePathCoordinates X s t ω)) μ := by
    -- Proof comment: indicator test functions are bounded by `1`, hence integrable on the
    -- probability measure `P x`.
    refine Integrable.of_bound (hIndicator_meas.comp hcoords_meas).aestronglyMeasurable 1 ?_
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    by_cases hω : futurePathCoordinates X s t ω ∈ A
    · simp [indicatorA, hω]
    · simp [indicatorA, hω]
  have hordered_indicator :
      μ[fun ω ↦ indicatorA (futurePathCoordinates X s t ω) |
        generatedFiltrationSpace X s] =ᵐ[μ]
          fun ω ↦ ∫ y, indicatorA (coordinateProjection y) ∂κ (X s ω) := by
    -- Proof comment: specialize the ordered formula to the indicator of the measurable
    -- coordinate cylinder `A`.
    simpa [μ, indicatorA, coordinateProjection] using
      @hOrdered n indicatorA hIndicator_meas (isBounded_range_indicator_one A) t ht s x hs
  have hB_ambient : MeasurableSet B := by
    exact generatedFiltrationSpace_le_ambient_of_measurable X hX_meas s B hB
  have hkernel_mass :
      ∀ ω,
        (∫ y, indicatorA (coordinateProjection y) ∂κ (X s ω)) =
          (((κ (X s ω)).map coordinateProjection).real A) := by
    intro ω
    calc
      ∫ y, indicatorA (coordinateProjection y) ∂κ (X s ω)
          = ((κ (X s ω)).real (coordinateProjection ⁻¹' A)) := by
              simpa [indicatorA] using
                (MeasureTheory.integral_indicator_one (hcoordinateProjection_meas hA))
      _ = (((κ (X s ω)).map coordinateProjection).real A) := by
            symm
            exact
              MeasureTheory.map_measureReal_apply hcoordinateProjection_meas hA
  calc
    ((((μ.restrict B).map (futurePathCoordinates X s t)).real A))
        = ∫ ω, indicatorA (futurePathCoordinates X s t ω) ∂(μ.restrict B) := by
            rw [MeasureTheory.map_measureReal_apply hcoords_meas hA]
            simpa [indicatorA] using
              (MeasureTheory.integral_indicator_one (hcoords_meas hA)).symm
    _ = ∫ ω in B, indicatorA (futurePathCoordinates X s t ω) ∂μ := by
          rfl
    _ = ∫ ω in B,
          (μ[fun ω ↦ indicatorA (futurePathCoordinates X s t ω) |
            generatedFiltrationSpace X s]) ω ∂μ := by
          symm
          exact
            MeasureTheory.setIntegral_condExp
              (generatedFiltrationSpace_le_ambient_of_measurable X hX_meas s)
              hIndicator_int hB
    _ = ∫ ω in B, ∫ y, indicatorA (coordinateProjection y) ∂κ (X s ω) ∂μ := by
          refine MeasureTheory.setIntegral_congr_ae hB_ambient ?_
          filter_upwards [hordered_indicator] with ω hω hωB
          exact hω
    _ = ∫ ω in B, (((κ (X s ω)).map coordinateProjection).real A) ∂μ := by
          refine MeasureTheory.setIntegral_congr_ae hB_ambient ?_
          exact Filter.Eventually.of_forall fun ω _ ↦ hkernel_mass ω
    _ = ∫ ω in B, (((κ (X s ω)).map (fun y i ↦ y (t i))).real A) ∂(P x : Measure Ω) := by
          rfl

/-- Helper for Theorem 17.9: every path measure is the projective limit of its finite restriction
marginals. -/
lemma pathMeasure_isProjectiveLimit_restrictions
    (ν : Measure (I → E)) :
    MeasureTheory.IsProjectiveLimit ν (fun J : Finset I ↦ ν.map J.restrict) := by
  -- Proof comment: the defining property of a projective limit is exactly that each finite
  -- restriction marginal is the corresponding pushforward.
  intro J
  rfl

/-- Helper for Theorem 17.9: reindexing the ordered tuple attached to `J.orderEmbOfFin` recovers
the ordinary finite restriction map on path space. -/
lemma orderedTupleReindex_eq_restrict
    (J : Finset I) (y : I → E) :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → I := J.orderEmbOfFin rfl
    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (fun i ↦ y (t i)) = J.restrict y := by
  -- Proof comment: the order isomorphism `Fin J.card ≃ J` turns the sorted tuple coordinates back
  -- into the canonical finite restriction map.
  dsimp
  ext j
  have hindex :
      J.orderEmbOfFin rfl ((J.orderIsoOfFin rfl).symm j) = j.1 := by
    exact congrArg Subtype.val ((J.orderIsoOfFin rfl).apply_symm_apply j)
  change
    ((Equiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
        (fun i ↦ y (J.orderEmbOfFin rfl i)) j) =
      J.restrict y j
  rw [Equiv.piCongrLeft_apply]
  simp [hindex]

omit mΩ mE in
/-- Helper for Theorem 17.9: a monotone future-time tuple factors through the strict ordered
image of its values. -/
lemma monotoneFutureTupleFactorsThroughOrderedImage
    {n : ℕ} (X : I → Ω → E) (s : I) {t : Fin n → I} (_ht : Monotone t) :
    let J : Finset I := Finset.univ.image t
    let τ : Fin J.card → I := J.orderEmbOfFin rfl
    let lift : Fin n → Fin J.card := fun i ↦
      (J.orderIsoOfFin rfl).symm ⟨t i, by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    futurePathCoordinates X s t = fun ω i ↦ futurePathCoordinates X s τ ω (lift i) := by
  let J : Finset I := Finset.univ.image t
  let τ : Fin J.card → I := J.orderEmbOfFin rfl
  let lift : Fin n → Fin J.card := fun i ↦
    (J.orderIsoOfFin rfl).symm ⟨t i, by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  change futurePathCoordinates X s t = fun ω i ↦ futurePathCoordinates X s τ ω (lift i)
  -- Proof comment: each original coordinate `t i` is recovered by reindexing through the ordered
  -- image `J.orderEmbOfFin rfl`.
  funext ω i
  have hindex : τ (lift i) = t i := by
    exact congrArg Subtype.val ((J.orderIsoOfFin rfl).apply_symm_apply
      ⟨t i, by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
  simp [futurePathCoordinates, τ, lift, hindex]

omit mE in
/-- Helper for Theorem 17.9: the path-space coordinate projection along a monotone tuple factors
through the strict ordered image of its values. -/
lemma monotonePathCoordinateProjectionFactorsThroughOrderedImage
    {n : ℕ} {t : Fin n → I} (_ht : Monotone t) :
    let J : Finset I := Finset.univ.image t
    let τ : Fin J.card → I := J.orderEmbOfFin rfl
    let lift : Fin n → Fin J.card := fun i ↦
      (J.orderIsoOfFin rfl).symm ⟨t i, by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    (fun y : I → E ↦ fun i ↦ y (t i)) = fun y i ↦ y (τ (lift i)) := by
  let J : Finset I := Finset.univ.image t
  let τ : Fin J.card → I := J.orderEmbOfFin rfl
  let lift : Fin n → Fin J.card := fun i ↦
    (J.orderIsoOfFin rfl).symm ⟨t i, by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  change (fun y : I → E ↦ fun i ↦ y (t i)) = fun y i ↦ y (τ (lift i))
  -- Proof comment: the same ordered-image reindexing works on the path-space coordinate map.
  funext y i
  have hindex : τ (lift i) = t i := by
    exact congrArg Subtype.val ((J.orderIsoOfFin rfl).apply_symm_apply
      ⟨t i, by
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
  simp [hindex]

/-- Helper for Theorem 17.9: equality of all ordered tuple marginals forces equality of all
finite restriction marginals. -/
lemma mapRestrict_eq_of_orderedTupleMap_eq
    {ν₁ ν₂ : Measure (I → E)}
    (hmap :
      ∀ {n : ℕ} (t : Fin n → I), StrictMono t →
        ν₁.map (fun y i ↦ y (t i)) = ν₂.map (fun y i ↦ y (t i))) :
    ∀ J : Finset I, ν₁.map J.restrict = ν₂.map J.restrict := by
  intro J
  let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
  let t : Fin J.card → I := J.orderEmbOfFin rfl
  have ht : StrictMono t := (J.orderEmbOfFin rfl).strictMono
  have htuple_meas : Measurable (fun y : I → E ↦ fun i ↦ y (t i)) := by
    -- Proof comment: the ordered tuple projection is coordinatewise evaluation on the selected
    -- times.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_pi_apply (t i)
  have hcomp :
      (fun y : I → E ↦ (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (fun i ↦ y (t i))) =
        J.restrict := by
    -- Proof comment: after reindexing the ordered tuple by `e`, we are back in the canonical
    -- restriction spelling.
    funext y
    simpa [e, t] using orderedTupleReindex_eq_restrict J y
  have hmap₁ :
      (ν₁.map (fun y i ↦ y (t i))).map (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) =
        ν₁.map J.restrict := by
    calc
      (ν₁.map (fun y i ↦ y (t i))).map (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e)
          = ν₁.map (fun y : I → E ↦
              (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (fun i ↦ y (t i))) := by
                rw [Measure.map_map
                  (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e).measurable htuple_meas]
                rfl
      _ = ν₁.map J.restrict := by rw [hcomp]
  have hmap₂ :
      (ν₂.map (fun y i ↦ y (t i))).map (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) =
        ν₂.map J.restrict := by
    calc
      (ν₂.map (fun y i ↦ y (t i))).map (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e)
          = ν₂.map (fun y : I → E ↦
              (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (fun i ↦ y (t i))) := by
                rw [Measure.map_map
                  (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e).measurable htuple_meas]
                rfl
      _ = ν₂.map J.restrict := by rw [hcomp]
  -- Proof comment: transport the ordered-tuple equality through the finite-set reindexing map.
  calc
    ν₁.map J.restrict
        = (ν₁.map (fun y i ↦ y (t i))).map
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) := hmap₁.symm
    _ = (ν₂.map (fun y i ↦ y (t i))).map
          (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) := by
            rw [hmap t ht]
    _ = ν₂.map J.restrict := hmap₂

/-- Helper for Theorem 17.9: equality of all finite restriction marginals determines a finite
path measure uniquely. -/
lemma measure_eq_of_mapRestrict_eq
    {ν₁ ν₂ : Measure (I → E)} [IsFiniteMeasure ν₁]
    (hmap : ∀ J : Finset I, ν₁.map J.restrict = ν₂.map J.restrict) :
    ν₁ = ν₂ := by
  have hν :
      MeasureTheory.IsProjectiveLimit ν₁ (fun J : Finset I ↦ ν₁.map J.restrict) := by
    simpa using pathMeasure_isProjectiveLimit_restrictions ν₁
  have hρ :
      MeasureTheory.IsProjectiveLimit ν₂ (fun J : Finset I ↦ ν₁.map J.restrict) := by
    intro J
    exact (hmap J).symm
  haveI : ∀ J : Finset I, IsFiniteMeasure (ν₁.map J.restrict) := fun _ ↦ inferInstance
  -- Proof comment: `IsProjectiveLimit.unique` is the canonical owner theorem that reconstructs
  -- the whole path measure from its finite restrictions.
  exact MeasureTheory.IsProjectiveLimit.unique hν hρ

/-- Helper for Theorem 17.9: the `n = 0` specialization of the ordered-cylinder formula forces
the path-kernel row mass at the present state to be `1` almost surely. -/
lemma kernelRowMass_univ_ae_one_of_orderedFormula
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hX_meas : ∀ t, Measurable (X t))
    (hOrdered : HasOrderedFutureCoordinateConditionalExpectationFormula X P κ)
    (s : I) (x : E) (hs : 0 ≤ s) :
    (fun ω ↦ κ (X s ω) Set.univ) =ᵐ[(P x : Measure Ω)] fun _ : Ω ↦ (1 : ENNReal) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let t : Fin 0 → I := Fin.elim0
  have ht : Monotone t := by
    intro i
    exact Fin.elim0 i
  have hordered_zero :
      μ[fun _ ↦ (1 : ℝ) | generatedFiltrationSpace X s] =ᵐ[μ]
        fun ω ↦ ∫ y, (1 : ℝ) ∂κ (X s ω) := by
    -- Proof comment: specialize the ordered finite-coordinate formula to the empty tuple and the
    -- constant-one test function.
    simpa [μ, t] using
      @hOrdered 0 (fun _ : Fin 0 → E ↦ (1 : ℝ)) measurable_const
        (by simpa using Bornology.isBounded_singleton)
        t ht s x hs
  have hconst :
      μ[fun _ ↦ (1 : ℝ) | generatedFiltrationSpace X s] = fun _ ↦ (1 : ℝ) := by
    -- Proof comment: the conditional expectation of a constant on the probability measure `P x`
    -- is the same constant.
    simpa [μ] using
      (MeasureTheory.condExp_const
        (generatedFiltrationSpace_le_ambient_of_measurable X hX_meas s) (1 : ℝ))
  have hreal :
      (fun ω ↦ (κ (X s ω)).real Set.univ) =ᵐ[μ] fun _ ↦ (1 : ℝ) := by
    -- Proof comment: identify the kernel integral of the constant-one function with the real mass
    -- of the whole row measure.
    have hmass :
        (fun ω ↦ ∫ y, (1 : ℝ) ∂κ (X s ω)) =ᵐ[μ]
          fun ω ↦ (κ (X s ω)).real Set.univ := by
      exact Filter.Eventually.of_forall fun ω ↦ by
        simpa using
          (MeasureTheory.integral_indicator_one (μ := κ (X s ω))
            (s := Set.univ) MeasurableSet.univ)
    exact hmass.symm.trans <| hordered_zero.symm.trans <| Filter.EventuallyEq.of_eq hconst
  -- Proof comment: once the real mass of the whole row is `1`, the row itself has total mass
  -- exactly `1`.
  filter_upwards [hreal] with ω hω
  exact (ENNReal.toReal_eq_one_iff (κ (X s ω) Set.univ)).mp <| by
    simpa [MeasureTheory.Measure.real_def] using hω

/-- Helper for Theorem 17.9: on each history event, the restricted future-path law agrees with the
mixed path-kernel law obtained by averaging `κ` against the present-state law. -/
lemma restrictedFuturePathLaw_eq_mixedPathLaw_on_historyEvent
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hX_meas : ∀ t, Measurable (X t))
    (hOrdered : HasOrderedFutureCoordinateConditionalExpectationFormula X P κ)
    (s : I) (x : E) (hs : 0 ≤ s)
    {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X s] B) :
    let μ : Measure Ω := (P x : Measure Ω)
    let νB : Measure (I → E) := (μ.restrict B).map (futurePath X s)
    let ρB : Measure (I → E) := κ ∘ₘ ((μ.restrict B).map (X s))
    νB = ρB := by
  let μ : Measure Ω := (P x : Measure Ω)
  let νB : Measure (I → E) := (μ.restrict B).map (futurePath X s)
  let ρB : Measure (I → E) := κ ∘ₘ ((μ.restrict B).map (X s))
  have hB_ambient : MeasurableSet B :=
    generatedFiltrationSpace_le_ambient_of_measurable X hX_meas s B hB
  have hrowMass :
      (fun ω ↦ κ (X s ω) Set.univ) =ᵐ[μ] fun _ : Ω ↦ (1 : ENNReal) :=
    kernelRowMass_univ_ae_one_of_orderedFormula X P κ hX_meas hOrdered s x hs
  have hρB_univ :
      ρB Set.univ = μ B := by
    let κ₀ : Kernel Unit E := Kernel.const Unit ((μ.restrict B).map (X s))
    have hcomp : (κ ∘ₖ κ₀) () = ρB := by
      simp [κ₀, ρB]
    calc
      ρB Set.univ = ((κ ∘ₖ κ₀) ()) Set.univ := by rw [← hcomp]
      _ = ∫⁻ z, κ z Set.univ ∂κ₀ () := by
            rw [Kernel.comp_apply' _ _ _ MeasurableSet.univ]
      _ = ∫⁻ z, κ z Set.univ ∂((μ.restrict B).map (X s)) := by
            simp [κ₀]
      _ = ∫⁻ ω, κ (X s ω) Set.univ ∂(μ.restrict B) := by
            rw [MeasureTheory.lintegral_map'
              (Kernel.measurable_coe κ MeasurableSet.univ).aemeasurable
              (hX_meas s).aemeasurable]
      _ = ∫⁻ ω, (1 : ENNReal) ∂(μ.restrict B) := by
            exact MeasureTheory.lintegral_congr_ae <|
              hrowMass.filter_mono ae_restrict_le
      _ = μ B := by
            simp
  have hρB_univ_ne_top : ρB Set.univ ≠ ⊤ := by
    rw [hρB_univ]
    exact (measure_lt_top μ B).ne
  haveI : IsFiniteMeasure ρB := ⟨by
    simpa [lt_top_iff_ne_top] using hρB_univ_ne_top⟩
  have hOrderedTuples :
      ∀ {n : ℕ} (t : Fin n → I), StrictMono t →
        νB.map (fun y i ↦ y (t i)) = ρB.map (fun y i ↦ y (t i)) := by
    intro n t ht
    let tupleProjection : (I → E) → Fin n → E := fun y i ↦ y (t i)
    let κt : Kernel E (Fin n → E) := κ.map tupleProjection
    have htupleProjection_meas : Measurable tupleProjection := by
      -- Proof comment: the ordered tuple projection is coordinatewise evaluation on the selected
      -- times.
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact measurable_pi_apply (t i)
    have hleft_real :
        ∀ A : Set (Fin n → E), MeasurableSet A →
          ((νB.map tupleProjection).real A) =
            ∫ ω in B, (((κ (X s ω)).map tupleProjection).real A) ∂μ := by
      intro A hA
      have hmap :
          νB.map tupleProjection = ((μ.restrict B).map (futurePathCoordinates X s t)) := by
        dsimp [νB, tupleProjection]
        rw [Measure.map_map htupleProjection_meas (measurable_futurePath X hX_meas s)]
        rfl
      -- Proof comment: rewrite the tuple pushforward of the restricted future-path law through the
      -- already proved ordered-cylinder history-event formula.
      rw [hmap]
      simpa [μ] using
        (restrictedFutureCoordinateLaw_eq_mixedKernel_on_historyEvent
          X P κ hX_meas hOrdered ht.monotone hA hs hB)
    have hright_real :
        ∀ A : Set (Fin n → E), MeasurableSet A →
          ((ρB.map tupleProjection).real A) =
            ∫ ω in B, (((κ (X s ω)).map tupleProjection).real A) ∂μ := by
      intro A hA
      let indicatorA : (Fin n → E) → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
      have hmap :
          ρB.map tupleProjection = κt ∘ₘ ((μ.restrict B).map (X s)) := by
        dsimp [ρB, κt]
        simpa using Measure.map_comp (((μ.restrict B).map (X s))) κ htupleProjection_meas
      haveI : IsFiniteMeasure (κt ∘ₘ ((μ.restrict B).map (X s))) := by
        rw [← hmap]
        infer_instance
      have hIndicatorInt :
          Integrable indicatorA (κt ∘ₘ ((μ.restrict B).map (X s))) := by
        -- Proof comment: the indicator test function is bounded on the finite mixed tuple law.
        refine Integrable.of_bound
          (Measurable.indicator measurable_const hA).aestronglyMeasurable 1 ?_
        exact Filter.Eventually.of_forall fun z ↦ by
          by_cases hz : z ∈ A <;> simp [indicatorA, hz]
      calc
        ((ρB.map tupleProjection).real A)
            = ∫ y, indicatorA y ∂(κt ∘ₘ ((μ.restrict B).map (X s))) := by
                rw [hmap]
                simpa [indicatorA] using
                  (MeasureTheory.integral_indicator_one (μ := κt ∘ₘ ((μ.restrict B).map (X s)))
                    (s := A) hA).symm
        _ = ∫ z, ∫ y, indicatorA y ∂κt z ∂((μ.restrict B).map (X s)) := by
              let κ₀ : Kernel Unit E := Kernel.const Unit ((μ.restrict B).map (X s))
              have hcomp :
                  (κt ∘ₖ κ₀) () = κt ∘ₘ ((μ.restrict B).map (X s)) := by
                simp [κ₀]
              rw [← hcomp]
              simpa using
                (ProbabilityTheory.Kernel.integral_comp
                  (η := κt) (κ := κ₀) (a := ()) hIndicatorInt)
        _ = ∫ z, (κt z).real A ∂((μ.restrict B).map (X s)) := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
              simpa [indicatorA] using
                (MeasureTheory.integral_indicator_one (μ := κt z) (s := A) hA)
        _ = ∫ ω in B, (κt (X s ω)).real A ∂μ := by
              simpa [κt] using
                (MeasureTheory.integral_map (hX_meas s).aemeasurable
                  ((Kernel.measurable_coe κt hA).ennreal_toReal.aestronglyMeasurable))
        _ = ∫ ω in B, (((κ (X s ω)).map tupleProjection).real A) ∂μ := by
              refine MeasureTheory.setIntegral_congr_ae hB_ambient ?_
              exact Filter.Eventually.of_forall fun ω _ ↦ by
                have hrow : κt (X s ω) = (κ (X s ω)).map tupleProjection := by
                  simpa [κt] using Kernel.map_apply κ htupleProjection_meas (X s ω)
                exact congrArg (fun ν : Measure (Fin n → E) ↦ ν.real A) hrow
    refine Measure.ext fun A hA ↦ ?_
    have hleft_ne_top : (νB.map tupleProjection) A ≠ ⊤ := by
      simpa using measure_lt_top (νB.map tupleProjection) A
    have hright_ne_top : (ρB.map tupleProjection) A ≠ ⊤ := by
      simpa using measure_lt_top (ρB.map tupleProjection) A
    exact
      (MeasureTheory.measureReal_eq_measureReal_iff
        (μ := νB.map tupleProjection) (ν := ρB.map tupleProjection)
        (s := A) (t := A) hleft_ne_top hright_ne_top).mp
        ((hleft_real A hA).trans (hright_real A hA).symm)
  have hJ :
      ∀ J : Finset I, νB.map J.restrict = ρB.map J.restrict :=
    mapRestrict_eq_of_orderedTupleMap_eq hOrderedTuples
  haveI : IsFiniteMeasure νB := by
    dsimp [νB]
    infer_instance
  -- Proof comment: once the restricted future-path law and the mixed path-kernel law have the
  -- same finite restrictions, projective-limit uniqueness identifies the full path measures.
  exact measure_eq_of_mapRestrict_eq hJ

/-- Helper for Theorem 17.9: the ordered finite-coordinate conditional-expectation formula
upgrades to the full path-space future-path formula. -/
-- Proof comment: this upgrade now runs by identifying the restricted future-path law and the
-- mixed path-kernel law on every history event, then applying
-- `ae_eq_condExp_of_forall_setIntegral_eq` to bounded measurable path functionals.
lemma hasFuturePathConditionalExpectationFormula_of_orderedFormula
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hX_meas : ∀ t, Measurable (X t))
    (hOrdered : HasOrderedFutureCoordinateConditionalExpectationFormula X P κ) :
    HasFuturePathConditionalExpectationFormula X P κ := by
  intro f hf_meas hf_bdd s x hs
  let μ : Measure Ω := (P x : Measure Ω)
  have hfuture_meas : Measurable (futurePath X s) := measurable_futurePath X hX_meas s
  have hf_int :
      Integrable (fun ω ↦ f (futurePath X s ω)) μ := by
    obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range f) hf_bdd
    -- Proof comment: bounded measurable path test functions are integrable under the start law.
    refine Integrable.of_bound (hf_meas.comp hfuture_meas).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC _ ⟨futurePath X s ω, rfl⟩
  have hrowMass :
      (fun ω ↦ κ (X s ω) Set.univ) =ᵐ[μ] fun _ : Ω ↦ (1 : ENNReal) :=
    kernelRowMass_univ_ae_one_of_orderedFormula X P κ hX_meas hOrdered s x hs
  have hKernelIntegral_meas :
      Measurable fun z : E ↦ ∫ y, f y ∂κ z := by
    -- Proof comment: integrating a measurable bounded path functional against the kernel is
    -- measurable in the present state.
    exact
      (hf_meas.stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun z : E ↦ ∫ y, f y ∂κ z).measurable
  have hKernelIntegral_meas_generated :
      Measurable[generatedFiltrationSpace X s] fun ω ↦ ∫ y, f y ∂κ (X s ω) := by
    -- Proof comment: the kernel integral depends on the history only through the present state
    -- `X s`.
    exact hKernelIntegral_meas.comp <|
      Measurable.of_comap_le (show MeasurableSpace.comap (X s) mE ≤ generatedFiltrationSpace X s by
        exact le_iSup_of_le s <| le_iSup_of_le le_rfl le_rfl)
  have hKernelIntegral_meas_ambient :
      Measurable fun ω ↦ ∫ y, f y ∂κ (X s ω) := by
    exact hKernelIntegral_meas.comp (hX_meas s)
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range f) hf_bdd
  refine
    (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
      (generatedFiltrationSpace_le_ambient_of_measurable X hX_meas s)
      hf_int
      (fun B _ hμB ↦ by
        -- Proof comment: the kernel-integral candidate is bounded on every history event once the
        -- row mass is known to be `1` almost surely along the present state.
        refine IntegrableOn.of_bound hμB hKernelIntegral_meas_ambient.aestronglyMeasurable C ?_
        filter_upwards [hrowMass.filter_mono ae_restrict_le] with ω hω
        have hωne : κ (X s ω) Set.univ ≠ ⊤ := by
          simpa [hω]
        have hωfin : IsFiniteMeasure (κ (X s ω)) := ⟨by
          simpa [lt_top_iff_ne_top] using hωne⟩
        have hbound_row :
            ‖∫ y, f y ∂κ (X s ω)‖ ≤ C := by
          have hfC : ∀ᵐ y ∂κ (X s ω), ‖f y‖ ≤ C :=
            Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
          simpa [MeasureTheory.Measure.real_def, hω] using
            (MeasureTheory.norm_integral_le_of_norm_le_const (μ := κ (X s ω)) hfC)
        exact hbound_row)
      (fun B hB hμB ↦ by
        let νB : Measure (I → E) := (μ.restrict B).map (futurePath X s)
        let ρB : Measure (I → E) := κ ∘ₘ ((μ.restrict B).map (X s))
        have hlaw : νB = ρB := by
          simpa [μ, νB, ρB] using
            restrictedFuturePathLaw_eq_mixedPathLaw_on_historyEvent X P κ hX_meas hOrdered
              s x hs hB
        haveI : IsFiniteMeasure νB := by
          dsimp [νB]
          infer_instance
        have hf_νB_int : Integrable f νB := by
          refine Integrable.of_bound hf_meas.aestronglyMeasurable C ?_
          exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
        have hf_ρB_int : Integrable f ρB := by
          rw [← hlaw]
          exact hf_νB_int
        have hleft :
            ∫ ω in B, f (futurePath X s ω) ∂μ = ∫ y, f y ∂νB := by
          change ∫ ω, f (futurePath X s ω) ∂(μ.restrict B) = ∫ y, f y ∂νB
          rw [show νB = (μ.restrict B).map (futurePath X s) by rfl]
          exact
            (MeasureTheory.integral_map hfuture_meas.aemeasurable
              hf_meas.aestronglyMeasurable).symm
        have hright :
            ∫ y, f y ∂ρB = ∫ ω in B, ∫ y, f y ∂κ (X s ω) ∂μ := by
          let κ₀ : Kernel Unit E := Kernel.const Unit ((μ.restrict B).map (X s))
          have hcomp : (κ ∘ₖ κ₀) () = ρB := by
            simp [κ₀, ρB]
          calc
            ∫ y, f y ∂ρB = ∫ y, f y ∂((κ ∘ₖ κ₀) ()) := by rw [← hcomp]
            _ = ∫ z, ∫ y, f y ∂κ z ∂κ₀ () := by
                  simpa using
                    (ProbabilityTheory.Kernel.integral_comp
                      (η := κ) (κ := κ₀) (a := ()) hf_ρB_int)
            _ = ∫ z, ∫ y, f y ∂κ z ∂((μ.restrict B).map (X s)) := by
                  simp [κ₀]
            _ = ∫ ω in B, ∫ y, f y ∂κ (X s ω) ∂μ := by
                  simpa using
                    (MeasureTheory.integral_map (hX_meas s).aemeasurable
                      hKernelIntegral_meas.aestronglyMeasurable)
        exact (hleft.trans (hlaw ▸ hright)).symm)
      hKernelIntegral_meas_generated.aestronglyMeasurable).symm

/-- Helper for Theorem 17.9: on an additive submonoid of `NNReal` closed under ordered
differences, the source-facing future-path formula is equivalent to its ordered finite-coordinate
restriction. -/
-- Proof comment: the forward implication is specialization along the finite coordinate
-- projection, and the backward implication is the ordered-cylinder-to-path-law upgrade proved in
-- `hasFuturePathConditionalExpectationFormula_of_orderedFormula`.
theorem
    hasFuturePathConditionalExpectationFormula_iff_hasOrderedFutureCoordinateFormula
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω)
    (κ : Kernel E (I → E))
    (hX_meas : ∀ t, Measurable (X t))
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I) :
    HasFuturePathConditionalExpectationFormula X P κ ↔
      HasOrderedFutureCoordinateConditionalExpectationFormula X P κ := by
  constructor
  · -- Proof comment: the full path-functional formula immediately specializes to ordered finite
    -- coordinate functionals by composition with the coordinate projection.
    exact
      hasOrderedFutureCoordinateConditionalExpectationFormula_of_futurePathFormula
        X P κ
  · intro hOrdered
    -- Proof comment: first identify the restricted future-path laws on every history event, then
    -- feed that law equality into `ae_eq_condExp_of_forall_setIntegral_eq`.
    exact hasFuturePathConditionalExpectationFormula_of_orderedFormula X P κ hX_meas hOrdered

/-- Helper for Theorem 17.9: the future-path conditional-expectation formula upgrades to the
Chapter 17 time-homogeneous Markov owner when the initial law and path law are already fixed. -/
theorem isTimeHomogeneousMarkovProcess_of_hasFuturePathConditionalExpectationFormula_of_pathKernel
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hX_meas : ∀ t, Measurable (X t))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun t : I ↦ X t ω))
    (hFuture : HasFuturePathConditionalExpectationFormula X P κ) :
    IsTimeHomogeneousMarkovProcess X P κ := by
  refine
    { measurable_process := hX_meas
      initial_state := hX0
      path_law := hpath
      markov_property := ?_ }
  intro x A hA s t
  let indicatorA : (I → E) → ℝ := Set.indicator ((fun y : I → E ↦ y t) ⁻¹' A) fun _ ↦ (1 : ℝ)
  have hIndicator_meas : Measurable indicatorA := by
    -- Proof comment: the one-coordinate event `{y | y t ∈ A}` is a measurable path event.
    exact Measurable.indicator measurable_const ((measurable_pi_apply t) hA)
  have hfuture_indicator :
      (P x)[fun ω ↦ indicatorA (futurePath X s ω) | generatedFiltrationSpace X s] =ᵐ[
        (P x : Measure Ω)]
          fun ω ↦ ∫ y, indicatorA y ∂κ (X s ω) := by
    -- Proof comment: specialize the future-path formula to the indicator of the time-`t`
    -- cylinder event `A`.
    exact
      hFuture hIndicator_meas (isBounded_range_indicator_one ((fun y : I → E ↦ y t) ⁻¹' A))
        s x (show (0 : I) ≤ s by
          change (0 : NNReal) ≤ (s : NNReal)
          exact zero_le _)
  -- Proof comment: after unfolding the chosen path-event indicator, the left-hand side is the
  -- source Markov conditional expectation and the right-hand side is the time-`t` transition row.
  filter_upwards [hfuture_indicator] with ω hω
  have hright :
      (∫ y, indicatorA y ∂κ (X s ω)) = ((transitionKernel κ t) (X s ω)).real A := by
    calc
      ∫ y, indicatorA y ∂κ (X s ω)
          = (κ (X s ω)).real ((fun y : I → E ↦ y t) ⁻¹' A) := by
              simpa [indicatorA] using
                (MeasureTheory.integral_indicator_one ((measurable_pi_apply t) hA))
      _ = ((transitionKernel κ t) (X s ω)).real A := by
            rw [transitionKernel_apply]
            simpa using
              (MeasureTheory.map_measureReal_apply (measurable_pi_apply t) hA).symm
  simpa [indicatorA, futurePath] using hω.trans hright

/-- Helper for Theorem 17.9: pushing a path-kernel row forward to an ordered tuple gives the same
finite-dimensional law as the realized tuple of `X` started from the same state. -/
lemma pathKernelRow_map_orderedTuple_eq_realizedTupleLaw
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    {n : ℕ} (t : Fin n → I) (x : E) :
    (κ x).map (fun y : I → E ↦ fun i ↦ y (t i)) =
      (P x : Measure Ω).map (fun ω ↦ fun i ↦ X (t i) ω) := by
  let pathMap : Ω → I → E := fun ω u ↦ X u ω
  have hpathMap_meas : Measurable pathMap := by
    -- Proof comment: the full path map is measurable because every coordinate of `X` is
    -- measurable under the Markov-process owner.
    refine measurable_pi_lambda _ fun u ↦ ?_
    exact hMarkov.measurable_process u
  have hcoord_meas :
      Measurable (fun y : I → E ↦ fun i ↦ y (t i)) :=
    measurable_pathCoordinateProjection (I := I) (E := E) t
  -- Proof comment: rewrite the row `κ x` as the realized path law and then compose the two
  -- measurable pushforwards.
  calc
    (κ x).map (fun y : I → E ↦ fun i ↦ y (t i))
        = (((P x : Measure Ω).map pathMap).map (fun y : I → E ↦ fun i ↦ y (t i))) := by
            rw [hMarkov.path_law x]
    _ = (P x : Measure Ω).map (fun ω ↦ fun i ↦ X (t i) ω) := by
          rw [Measure.map_map hcoord_meas hpathMap_meas]
          rfl

/-- Helper for Theorem 17.9: the ordered-coordinate conditional-expectation formula is trivial
for the empty tuple. -/
lemma orderedFutureCoordinateFormula_zero_of_isTimeHomogeneousMarkovProcess
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    {f : (Fin 0 → E) → ℝ} (_hf_meas : Measurable f)
    (_hf_bdd : Bornology.IsBounded (Set.range f))
    (t : Fin 0 → I) (_ht : Monotone t) (s x) (_hs : 0 ≤ s) :
    (P x)[fun ω ↦ f (futurePathCoordinates X s t ω) | generatedFiltrationSpace X s] =ᵐ[
      (P x : Measure Ω)]
      fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let c : ℝ := f (fun i ↦ Fin.elim0 i)
  let _ : IsMarkovKernel κ :=
    IsTimeHomogeneousMarkovProcess.isMarkovKernel (X := X) (P := P) (κ := κ)
  have hleft_const : (fun ω ↦ f (futurePathCoordinates X s t ω)) = fun _ : Ω ↦ c := by
    -- Proof comment: there is only one `Fin 0`-tuple, so the test functional is constant.
    funext ω
    congr
    funext i
    exact Fin.elim0 i
  have hright_const :
      (fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω)) = fun _ : Ω ↦ c := by
    -- Proof comment: the path-kernel integral is the same constant because the integrand does
    -- not depend on the sampled path.
    have htuple : ∀ y : I → E, (fun i ↦ y (t i)) = fun i ↦ Fin.elim0 i := by
      intro y
      funext i
      exact Fin.elim0 i
    funext ω
    simp [c, htuple]
  have hcond_const :
      μ[fun _ : Ω ↦ c | generatedFiltrationSpace X s] = fun _ : Ω ↦ c := by
    -- Proof comment: conditional expectation preserves constants on the probability measure
    -- `P x`.
    simpa [μ] using
      (MeasureTheory.condExp_const
        (generatedFiltrationSpace_le_ambient_of_measurable
          X (fun u ↦ hMarkov.measurable_process u) s) c)
  -- Proof comment: after rewriting both sides to the common constant `c`, the empty-tuple case
  -- is immediate.
  simpa [hleft_const, hright_const] using Filter.EventuallyEq.of_eq hcond_const

/-- Helper for Theorem 17.9: on a history event, the restricted law of one future coordinate is
the mixed transition law from the present state. -/
lemma restrictedSingleFutureCoordinateLaw_eq_mixedKernel_on_historyEvent
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    (u s : I) (x : E)
    {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X s] B) :
    (((P x : Measure Ω).restrict B).map (X (u + s))) =
      (transitionKernel κ u) ∘ₘ (((P x : Measure Ω).restrict B).map (X s)) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let κu : Kernel E E := transitionKernel κ u
  let _ : IsMarkovKernel κ :=
    IsTimeHomogeneousMarkovProcess.isMarkovKernel (X := X) (P := P) (κ := κ)
  let _ : IsMarkovKernel κu := inferInstance
  have hX_meas : ∀ r : I, Measurable (X r) := fun r ↦ hMarkov.measurable_process r
  have hB_ambient : MeasurableSet B := by
    exact generatedFiltrationSpace_le_ambient_of_measurable X hX_meas s B hB
  refine Measure.ext fun A hA ↦ ?_
  let indicatorA : E → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
  have hIndicator_meas : Measurable indicatorA := by
    -- Proof comment: measurable state events give measurable indicator test functions.
    exact Measurable.indicator measurable_const hA
  have hIndicator_int :
      Integrable (fun ω ↦ indicatorA (X (u + s) ω)) μ := by
    -- Proof comment: the indicator test function is bounded by `1`, so it is integrable under
    -- the probability measure `P x`.
    refine Integrable.of_bound (hIndicator_meas.comp (hX_meas (u + s))).aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : X (u + s) ω ∈ A <;> simp [indicatorA, hω]
  have hmarkov :
      μ[fun ω ↦ indicatorA (X (u + s) ω) | generatedFiltrationSpace X s] =ᵐ[μ]
        fun ω ↦ ((κu (X s ω)).real A) := by
    -- Proof comment: this is the one-step Markov property specialized to the measurable event
    -- `A` at the time gap `u`.
    simpa [μ, κu, indicatorA, add_comm, add_left_comm, add_assoc] using
      hMarkov.markov_property x hA s u
  have hright_real :
      (((κu ∘ₘ ((μ.restrict B).map (X s))).real A)) =
        ∫ ω in B, ((κu (X s ω)).real A) ∂μ := by
    haveI : IsFiniteMeasure (κu ∘ₘ ((μ.restrict B).map (X s))) := by
      infer_instance
    have hIndicatorInt :
        Integrable indicatorA (κu ∘ₘ ((μ.restrict B).map (X s))) := by
      -- Proof comment: the indicator remains bounded on the finite mixed one-coordinate law.
      refine Integrable.of_bound hIndicator_meas.aestronglyMeasurable 1 ?_
      exact Filter.Eventually.of_forall fun z ↦ by
        by_cases hz : z ∈ A <;> simp [indicatorA, hz]
    calc
      (((κu ∘ₘ ((μ.restrict B).map (X s))).real A))
          = ∫ y, indicatorA y ∂(κu ∘ₘ ((μ.restrict B).map (X s))) := by
              simpa [indicatorA] using
                (MeasureTheory.integral_indicator_one
                  (μ := κu ∘ₘ ((μ.restrict B).map (X s))) (s := A) hA).symm
      _ = ∫ z, ∫ y, indicatorA y ∂κu z ∂((μ.restrict B).map (X s)) := by
            let κ₀ : Kernel Unit E := Kernel.const Unit ((μ.restrict B).map (X s))
            have hcomp : (κu ∘ₖ κ₀) () = κu ∘ₘ ((μ.restrict B).map (X s)) := by
              simp [κ₀]
            rw [← hcomp]
            simpa using
              (ProbabilityTheory.Kernel.integral_comp
                (η := κu) (κ := κ₀) (a := ()) hIndicatorInt)
      _ = ∫ z, (κu z).real A ∂((μ.restrict B).map (X s)) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            simpa [indicatorA] using
              (MeasureTheory.integral_indicator_one (μ := κu z) (s := A) hA)
      _ = ∫ ω in B, ((κu (X s ω)).real A) ∂μ := by
            simpa [κu] using
              (MeasureTheory.integral_map (hX_meas s).aemeasurable
                ((Kernel.measurable_coe κu hA).ennreal_toReal.aestronglyMeasurable))
  have hleft_real :
      ((((μ.restrict B).map (X (u + s))).real A)) =
        ∫ ω in B, ((κu (X s ω)).real A) ∂μ := by
    calc
      ((((μ.restrict B).map (X (u + s))).real A))
          = ∫ ω in B, indicatorA (X (u + s) ω) ∂μ := by
              rw [MeasureTheory.map_measureReal_apply (hX_meas (u + s)) hA]
              simpa [indicatorA] using
                (MeasureTheory.integral_indicator_one
                  (μ := μ.restrict B) (s := X (u + s) ⁻¹' A) ((hX_meas (u + s)) hA)).symm
      _ = ∫ ω in B,
            (μ[fun ω ↦ indicatorA (X (u + s) ω) | generatedFiltrationSpace X s]) ω ∂μ := by
            symm
            exact
              MeasureTheory.setIntegral_condExp
                (generatedFiltrationSpace_le_ambient_of_measurable X hX_meas s)
                hIndicator_int hB
      _ = ∫ ω in B, ((κu (X s ω)).real A) ∂μ := by
            refine MeasureTheory.setIntegral_congr_ae hB_ambient ?_
            filter_upwards [hmarkov] with ω hω hωB
            exact hω
  have hleft_ne_top : (((μ.restrict B).map (X (u + s))) A) ≠ ⊤ := by
    simpa using measure_lt_top (((μ.restrict B).map (X (u + s)))) A
  have hright_ne_top : ((κu ∘ₘ ((μ.restrict B).map (X s))) A) ≠ ⊤ := by
    simpa using measure_lt_top (κu ∘ₘ ((μ.restrict B).map (X s))) A
  exact
    (MeasureTheory.measureReal_eq_measureReal_iff
      (μ := ((μ.restrict B).map (X (u + s))))
      (ν := κu ∘ₘ ((μ.restrict B).map (X s)))
      (s := A) (t := A) hleft_ne_top hright_ne_top).mp
      (hleft_real.trans hright_real.symm)

/-- Helper for Theorem 17.9: the ordered-coordinate conditional-expectation formula for a single
future time is exactly the one-step Markov property upgraded from events to bounded observables. -/
lemma orderedFutureCoordinateFormula_one_of_isTimeHomogeneousMarkovProcess
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    {f : (Fin 1 → E) → ℝ} (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (Set.range f))
    (t : Fin 1 → I) (_ht : Monotone t) (s x) (_hs : 0 ≤ s) :
    (P x)[fun ω ↦ f (futurePathCoordinates X s t ω) | generatedFiltrationSpace X s] =ᵐ[
      (P x : Measure Ω)]
      fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω) := by
  let μ : Measure Ω := (P x : Measure Ω)
  let u : I := t 0
  let stateObservable : E → ℝ := fun z ↦ f (fun _ : Fin 1 ↦ z)
  let _ : IsMarkovKernel κ :=
    IsTimeHomogeneousMarkovProcess.isMarkovKernel (X := X) (P := P) (κ := κ)
  have hX_meas : ∀ r : I, Measurable (X r) := fun r ↦ hMarkov.measurable_process r
  have hstateObservable_meas : Measurable stateObservable := by
    -- Proof comment: a one-coordinate cylinder function is just `f` composed with the constant
    -- `Fin 1` tuple constructor.
    have hsingle_meas : Measurable (fun z : E ↦ fun _ : Fin 1 ↦ z) := by
      refine measurable_pi_lambda _ fun _ ↦ measurable_id
    exact hf_meas.comp hsingle_meas
  have hstateObservable_bdd : Bornology.IsBounded (Set.range stateObservable) := by
    -- Proof comment: the one-coordinate observable takes values in the bounded range of `f`.
    refine hf_bdd.subset ?_
    intro r hr
    rcases hr with ⟨z, rfl⟩
    exact ⟨fun _ : Fin 1 ↦ z, rfl⟩
  have hfuture_eq :
      (fun ω ↦ f (futurePathCoordinates X s t ω)) = fun ω ↦ stateObservable (X (u + s) ω) := by
    -- Proof comment: a `Fin 1` tuple is determined by its unique coordinate.
    funext ω
    congr 1
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    simpa [stateObservable, u, futurePathCoordinates, hi]
  have hkernel_eq :
      (fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω)) = fun ω ↦
        ∫ z, stateObservable z ∂transitionKernel κ u (X s ω) := by
    -- Proof comment: on the kernel side, the `Fin 1` observable depends only on the time-`u`
    -- coordinate of the sampled path.
    funext ω
    rw [transitionKernel_apply]
    calc
      ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω)
          = ∫ y, stateObservable (y u) ∂κ (X s ω) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
            have htup : (fun _ : Fin 1 ↦ y u) = fun i ↦ y (t i) := by
              funext i
              have hi : i = 0 := Subsingleton.elim i 0
              simp [u, hi]
            simp [stateObservable, htup]
      _ = ∫ z, stateObservable z ∂(κ (X s ω)).map (fun y : I → E ↦ y u) := by
            symm
            exact
              (MeasureTheory.integral_map (μ := κ (X s ω))
                (φ := fun y : I → E ↦ y u)
                (f := stateObservable)
                (measurable_pi_apply u).aemeasurable
                hstateObservable_meas.aestronglyMeasurable)
  have hkernelIntegral_meas :
      Measurable fun z : E ↦ ∫ y, stateObservable y ∂transitionKernel κ u z := by
    -- Proof comment: integrating a measurable bounded state observable against the transition
    -- kernel is measurable in the present state.
    exact
      (hstateObservable_meas.stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun z : E ↦ ∫ y, stateObservable y ∂transitionKernel κ u z).measurable
  have hkernelIntegral_meas_generated :
      Measurable[generatedFiltrationSpace X s]
        fun ω ↦ ∫ y, stateObservable y ∂transitionKernel κ u (X s ω) := by
    -- Proof comment: the kernel integral depends on the history only through the present state.
    exact hkernelIntegral_meas.comp <|
      Measurable.of_comap_le (show MeasurableSpace.comap (X s) mE ≤ generatedFiltrationSpace X s by
        exact le_iSup_of_le s <| le_iSup_of_le le_rfl le_rfl)
  have hleft_int :
      Integrable (fun ω ↦ stateObservable (X (u + s) ω)) μ := by
    obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range stateObservable)
      hstateObservable_bdd
    -- Proof comment: bounded one-coordinate observables are integrable under the start law.
    refine Integrable.of_bound (hstateObservable_meas.comp (hX_meas (u + s))).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC _ ⟨X (u + s) ω, rfl⟩
  have hbase :
      μ[fun ω ↦ stateObservable (X (u + s) ω) | generatedFiltrationSpace X s] =ᵐ[μ]
        fun ω ↦ ∫ y, stateObservable y ∂transitionKernel κ u (X s ω) := by
    exact
      (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
      (generatedFiltrationSpace_le_ambient_of_measurable X hX_meas s)
      hleft_int
      (fun B _ hμB ↦ by
        obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range stateObservable)
          hstateObservable_bdd
        -- Proof comment: the candidate row-average is bounded on every history event by the same
        -- uniform bound on `stateObservable`.
        refine IntegrableOn.of_bound hμB
          (hkernelIntegral_meas.comp (hX_meas s)).aestronglyMeasurable C ?_
        let κu : Kernel E E := transitionKernel κ u
        let _ : IsMarkovKernel κu := inferInstance
        refine Filter.Eventually.of_forall fun ω ↦ ?_
        have hrow_bound :
            ‖∫ y, stateObservable y ∂κu (X s ω)‖ ≤ C := by
          have hstateC : ∀ᵐ y ∂κu (X s ω), ‖stateObservable y‖ ≤ C :=
            Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
          simpa [κu, MeasureTheory.Measure.real_def] using
            (MeasureTheory.norm_integral_le_of_norm_le_const (μ := κu (X s ω)) hstateC)
        exact hrow_bound)
      (fun B hB hμB ↦ by
        have hlaw :
            ((μ.restrict B).map (X (u + s))) =
              (transitionKernel κ u) ∘ₘ ((μ.restrict B).map (X s)) := by
          exact
            restrictedSingleFutureCoordinateLaw_eq_mixedKernel_on_historyEvent
              X P κ u s x hB
        let κu : Kernel E E := transitionKernel κ u
        have hleft :
            ∫ ω in B, stateObservable (X (u + s) ω) ∂μ =
              ∫ z, stateObservable z ∂(((μ.restrict B).map (X (u + s)))) := by
          change ∫ ω, stateObservable (X (u + s) ω) ∂(μ.restrict B) =
            ∫ z, stateObservable z ∂(((μ.restrict B).map (X (u + s))))
          exact
            (MeasureTheory.integral_map (hX_meas (u + s)).aemeasurable
              hstateObservable_meas.aestronglyMeasurable).symm
        have hright :
            ∫ z, stateObservable z ∂(κu ∘ₘ (((μ.restrict B).map (X s)))) =
              ∫ ω in B, ∫ y, stateObservable y ∂κu (X s ω) ∂μ := by
          haveI : IsFiniteMeasure (κu ∘ₘ (((μ.restrict B).map (X s)))) := by
            infer_instance
          let κ₀ : Kernel Unit E := Kernel.const Unit (((μ.restrict B).map (X s)))
          have hcomp : (κu ∘ₖ κ₀) () = κu ∘ₘ (((μ.restrict B).map (X s))) := by
            simp [κ₀]
          have hstateInt :
              Integrable stateObservable (κu ∘ₘ (((μ.restrict B).map (X s)))) := by
            obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range stateObservable)
              hstateObservable_bdd
            refine Integrable.of_bound hstateObservable_meas.aestronglyMeasurable C ?_
            exact Filter.Eventually.of_forall fun z ↦ hC _ ⟨z, rfl⟩
          calc
            ∫ z, stateObservable z ∂(κu ∘ₘ (((μ.restrict B).map (X s)))) =
                ∫ z, stateObservable z ∂((κu ∘ₖ κ₀) ()) := by rw [← hcomp]
            _ = ∫ z, ∫ y, stateObservable y ∂κu z ∂κ₀ () := by
                  simpa using
                    (ProbabilityTheory.Kernel.integral_comp
                      (η := κu) (κ := κ₀) (a := ()) hstateInt)
            _ = ∫ z, ∫ y, stateObservable y ∂κu z ∂(((μ.restrict B).map (X s))) := by
                  simp [κ₀]
            _ = ∫ ω in B, ∫ y, stateObservable y ∂κu (X s ω) ∂μ := by
                  simpa using
                    (MeasureTheory.integral_map (hX_meas s).aemeasurable
                      (hkernelIntegral_meas.aestronglyMeasurable))
        calc
          ∫ ω in B, ∫ y, stateObservable y ∂κu (X s ω) ∂μ
              = ∫ z, stateObservable z ∂(κu ∘ₘ (((μ.restrict B).map (X s)))) := hright.symm
          _ = ∫ z, stateObservable z ∂((μ.restrict B).map (X (u + s))) := by rw [hlaw]
          _ = ∫ ω in B, stateObservable (X (u + s) ω) ∂μ := hleft.symm)
      hkernelIntegral_meas_generated.aestronglyMeasurable).symm
  have hleft_cond :
      μ[fun ω ↦ f (futurePathCoordinates X s t ω) | generatedFiltrationSpace X s] =ᵐ[μ]
        μ[fun ω ↦ stateObservable (X (u + s) ω) | generatedFiltrationSpace X s] := by
    exact MeasureTheory.condExp_congr_ae (Filter.EventuallyEq.of_eq hfuture_eq)
  calc
    μ[fun ω ↦ f (futurePathCoordinates X s t ω) | generatedFiltrationSpace X s] =ᵐ[μ]
        μ[fun ω ↦ stateObservable (X (u + s) ω) | generatedFiltrationSpace X s] := hleft_cond
    _ =ᵐ[μ] fun ω ↦ ∫ y, stateObservable y ∂transitionKernel κ u (X s ω) := hbase
    _ =ᵐ[μ] fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω) :=
      Filter.EventuallyEq.of_eq hkernel_eq.symm

/-- Helper for Theorem 17.9: reindexing a finite tuple by a fixed map is measurable. -/
lemma measurable_tuplePostcompose {m n : ℕ} (lift : Fin n → Fin m) :
    Measurable (fun z : (Fin m → E) ↦ fun i : Fin n ↦ z (lift i)) := by
  -- Proof comment: each output coordinate is evaluation at the fixed source coordinate `lift i`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply (lift i)

/-- Helper for Theorem 17.9: a successor future-coordinate tuple splits into its prefix tuple and
terminal coordinate. -/
lemma futurePathCoordinates_succSplit {n : ℕ}
    (X : I → Ω → E) (s : I) (t : Fin (n + 2) → I) :
    futurePathCoordinates X s t =
      fun ω ↦
        Fin.snoc
          (futurePathCoordinates X s (fun i : Fin (n + 1) ↦ t i.castSucc) ω)
          (X (t (Fin.last (n + 1)) + s) ω) := by
  -- Proof comment: the first `n + 1` coordinates are the cast-successor prefix, and the last
  -- coordinate is the terminal time of `t`.
  funext ω
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [futurePathCoordinates, Fin.snoc_castSucc]
  · simp [futurePathCoordinates, Fin.snoc_last]

/-- Helper for Theorem 17.9: the path-space projection along a successor tuple also splits into
its prefix tuple and terminal coordinate. -/
lemma pathCoordinateProjection_succSplit {n : ℕ} (t : Fin (n + 2) → I) :
    (fun y : I → E ↦ fun i ↦ y (t i)) =
      fun y ↦
        Fin.snoc
          (fun i : Fin (n + 1) ↦ y (t i.castSucc))
          (y (t (Fin.last (n + 1)))) := by
  -- Proof comment: evaluation on a successor tuple is determined by the cast-successor prefix
  -- and the final coordinate.
  funext y
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp [Fin.snoc_castSucc]
  · simp [Fin.snoc_last]

/-- Helper for Theorem 17.9: appending a terminal state to a prefix tuple is measurable. -/
lemma measurable_tupleSnoc {n : ℕ} :
    Measurable (fun p : (Fin (n + 1) → E) × E ↦ (Fin.snoc p.1 p.2 : Fin (n + 2) → E)) := by
  -- Proof comment: each coordinate of the appended tuple is either a prefix coordinate or the
  -- terminal state projection.
  refine measurable_pi_lambda _ fun i ↦ ?_
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simpa [Fin.snoc_castSucc] using (measurable_pi_apply j).comp measurable_fst
  · simpa [Fin.snoc_last] using measurable_snd

/-- Helper for Theorem 17.9: enlarging the time index enlarges the generated history
σ-algebra. -/
lemma generatedFiltrationSpace_mono_of_le
    (X : I → Ω → E) {s u : I} (hsu : s ≤ u) :
    generatedFiltrationSpace X s ≤ generatedFiltrationSpace X u := by
  -- Proof comment: every coordinate used to generate `𝓕_s` is also allowed in the larger
  -- supremum defining `𝓕_u`.
  rw [generatedFiltrationSpace]
  refine iSup₂_le fun t ht ↦ ?_
  exact le_iSup_of_le t <| le_iSup_of_le (le_trans ht hsu) le_rfl

/-- Helper for Theorem 17.9: a strict prefix future tuple is measurable with respect to the
later filtration determined by its terminal time. -/
lemma measurable_futurePathCoordinates_atLastFiltration {n : ℕ}
    (X : I → Ω → E) {u : Fin (n + 1) → I} (hu : StrictMono u) (s : I) :
    Measurable[generatedFiltrationSpace X (u (Fin.last n) + s)] (futurePathCoordinates X s u) := by
  -- Proof comment: each prefix coordinate occurs no later than the terminal time `u (Fin.last n)
  -- + s`, so it belongs to that generated filtration.
  rw [@measurable_pi_iff]
  intro i
  refine Measurable.of_comap_le ?_
  exact le_iSup_of_le (u i + s) <| le_iSup_of_le
    (by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (hu.monotone (Fin.le_last i)) s)
    le_rfl

/-- Helper for Theorem 17.9: on a history event, the successor future tuple splits into its
prefix tuple together with one final step from the predecessor state. -/
lemma restrictedFutureSuccSplitLaw_eq_compProd_on_historyEvent
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    {n : ℕ} {t : Fin (n + 2) → I} (ht : StrictMono t)
    {s : I} {x : E} {B : Set Ω}
    (hB : MeasurableSet[generatedFiltrationSpace X s] B) :
    let μ : Measure Ω := (P x : Measure Ω)
    let tp : Fin (n + 1) → I := fun i ↦ t i.castSucc
    let tPrev : I := tp (Fin.last n)
    let tLast : I := t (Fin.last (n + 1))
    let dt : I :=
      ⟨tLast.1 - tPrev.1, hsub (le_of_lt (ht (Fin.castSucc_lt_last (Fin.last n))))⟩
    let prefixTuple : Ω → Fin (n + 1) → E := futurePathCoordinates X s tp
    let splitTuple : Ω → (Fin (n + 1) → E) × E :=
      fun ω ↦ (prefixTuple ω, X (tLast + s) ω)
    let prefixMeasure : Measure (Fin (n + 1) → E) := ((μ.restrict B).map prefixTuple)
    let stepKernel : Kernel (Fin (n + 1) → E) E :=
      Kernel.comap (transitionKernel κ dt) (fun z ↦ z (Fin.last n)) (by fun_prop)
    ((μ.restrict B).map splitTuple) = prefixMeasure ⊗ₘ stepKernel := by
  let μ : Measure Ω := (P x : Measure Ω)
  let tp : Fin (n + 1) → I := fun i ↦ t i.castSucc
  let tPrev : I := tp (Fin.last n)
  let tLast : I := t (Fin.last (n + 1))
  let _ : IsMarkovKernel κ :=
    IsTimeHomogeneousMarkovProcess.isMarkovKernel (X := X) (P := P) (κ := κ)
  let dt : I :=
    ⟨tLast.1 - tPrev.1, hsub (le_of_lt (ht (Fin.castSucc_lt_last (Fin.last n))))⟩
  let prefixTuple : Ω → Fin (n + 1) → E := futurePathCoordinates X s tp
  let splitTuple : Ω → (Fin (n + 1) → E) × E := fun ω ↦ (prefixTuple ω, X (tLast + s) ω)
  let prefixMeasure : Measure (Fin (n + 1) → E) := ((μ.restrict B).map prefixTuple)
  let stepKernel : Kernel (Fin (n + 1) → E) E :=
    Kernel.comap (transitionKernel κ dt) (fun z ↦ z (Fin.last n)) (by fun_prop)
  let _ : IsFiniteKernel stepKernel := by
    refine ⟨⟨1, by simp, fun z ↦ ?_⟩⟩
    simp [stepKernel]
  have hX_meas : ∀ r : I, Measurable (X r) := fun r ↦ hMarkov.measurable_process r
  have htp : StrictMono tp := by
    -- Proof comment: the successor tuple prefix inherits strict order from `t`.
    intro i j hij
    exact ht (by simpa [tp] using hij)
  have htPrev_lt_tLast : tPrev < tLast := by
    -- Proof comment: the predecessor time is strictly earlier than the terminal time.
    simpa [tp, tPrev, tLast] using ht (Fin.castSucc_lt_last (Fin.last n))
  have hdt : dt + tPrev = tLast := by
    -- Proof comment: `dt` was defined as the ordered difference between the last and predecessor
    -- times.
    apply Subtype.ext
    change ((tLast : NNReal) - (tPrev : NNReal)) + (tPrev : NNReal) = (tLast : NNReal)
    exact tsub_add_cancel_of_le (show (tPrev : NNReal) ≤ (tLast : NNReal) by
      exact le_of_lt htPrev_lt_tLast)
  have hprefixTupleMeas : Measurable prefixTuple := by
    -- Proof comment: the prefix tuple is coordinatewise measurable in the ambient space.
    simpa [prefixTuple] using measurable_futurePathCoordinates X hX_meas s tp
  have hsplitTupleMeas : Measurable splitTuple := by
    -- Proof comment: the split tuple combines the measurable prefix tuple with the terminal
    -- future coordinate.
    exact hprefixTupleMeas.prodMk (hX_meas (tLast + s))
  have hB_big :
      MeasurableSet[generatedFiltrationSpace X (tPrev + s)] B := by
    -- Proof comment: an `𝓕_s` event is still measurable for the larger filtration
    -- `𝓕_{tPrev + s}`.
    exact
      (generatedFiltrationSpace_mono_of_le X
        (show s ≤ tPrev + s by
          change (s : NNReal) ≤ ((tPrev + s : I) : NNReal)
          simpa [zero_add] using
            add_le_add_right (show (0 : NNReal) ≤ (tPrev : NNReal) by exact zero_le _) s)) B hB
  refine Measure.ext_prod ?_
  intro C D hC hD
  let prefixEvent : Set Ω := prefixTuple ⁻¹' C
  let histEvent : Set Ω := B ∩ prefixEvent
  let lastEvent : Set Ω := X (tLast + s) ⁻¹' D
  have hprefixGenerated :
      MeasurableSet[generatedFiltrationSpace X (tPrev + s)] prefixEvent := by
    -- Proof comment: the prefix tuple only uses times up to `tPrev + s`, so measurable tuple
    -- events are measurable history events at that later time.
    have hprefixMeas :
        Measurable[generatedFiltrationSpace X (tPrev + s)] prefixTuple := by
      simpa [prefixTuple, tp, tPrev] using
        measurable_futurePathCoordinates_atLastFiltration X htp s
    exact hprefixMeas hC
  have hhistGenerated :
      MeasurableSet[generatedFiltrationSpace X (tPrev + s)] histEvent := by
    exact hB_big.inter hprefixGenerated
  have hgenerated_le :
      generatedFiltrationSpace X (tPrev + s) ≤ mΩ := by
    exact generatedFiltrationSpace_le_ambient_of_measurable X hX_meas (tPrev + s)
  have hprefixEventMeas : MeasurableSet prefixEvent := hgenerated_le prefixEvent hprefixGenerated
  have hhistEventMeas : MeasurableSet histEvent := hgenerated_le histEvent hhistGenerated
  have hlastEventMeas : MeasurableSet lastEvent := by
    simpa [lastEvent] using (hX_meas (tLast + s)) hD
  have hpresent_last :
      (fun ω ↦ prefixTuple ω (Fin.last n)) = X (tPrev + s) := by
    -- Proof comment: the last coordinate of the prefix tuple is exactly the predecessor state.
    funext ω
    simp [prefixTuple, tp, tPrev, futurePathCoordinates]
  have hhistPresent :
      ((μ.restrict histEvent).map (X (tPrev + s))) =
        (((prefixMeasure.restrict C).map (fun z : Fin (n + 1) → E ↦ z (Fin.last n)))) := by
    -- Proof comment: restricting to `histEvent = B ∩ {prefixTuple ∈ C}` and then reading the
    -- predecessor state matches restricting the prefix law to `C` and taking its last coordinate.
    refine Measure.ext fun A hA ↦ ?_
    have hlastCoordMeas :
        Measurable (fun z : Fin (n + 1) → E ↦ z (Fin.last n)) :=
      measurable_pi_apply (Fin.last n)
    have hpresentMeas : Measurable (X (tPrev + s)) := hX_meas (tPrev + s)
    rw [Measure.map_apply hpresentMeas hA, Measure.map_apply hlastCoordMeas hA]
    rw [Measure.restrict_apply (hpresentMeas hA), Measure.restrict_apply (hlastCoordMeas hA)]
    rw [Measure.map_apply hprefixTupleMeas ((hlastCoordMeas hA).inter hC)]
    rw [Measure.restrict_apply (hprefixTupleMeas ((hlastCoordMeas hA).inter hC))]
    have hcoord :
        prefixTuple ⁻¹' ((fun z : Fin (n + 1) → E ↦ z (Fin.last n)) ⁻¹' A) =
          X (tPrev + s) ⁻¹' A := by
      ext ω
      simp [prefixTuple, tp, tPrev, futurePathCoordinates]
    simp [histEvent, prefixEvent, hcoord, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
  have hdt_shift : dt + (tPrev + s) = tLast + s := by
    -- Proof comment: shifting the predecessor-step identity by `s` identifies the final time.
    simpa [add_assoc] using congrArg (fun u : I ↦ u + s) hdt
  have hstepLaw :
      ((μ.restrict histEvent).map (X (tLast + s))) =
        (transitionKernel κ dt) ∘ₘ ((μ.restrict histEvent).map (X (tPrev + s))) := by
    -- Proof comment: on the enlarged history event `histEvent`, the final coordinate is one
    -- Markov step of size `dt` from the predecessor state at time `tPrev + s`.
    simpa [histEvent, hdt_shift] using
      (restrictedSingleFutureCoordinateLaw_eq_mixedKernel_on_historyEvent
        X P κ dt (tPrev + s) x hhistGenerated)
  have hrealizedRect :
      ((μ.restrict B).map splitTuple) (C ×ˢ D) =
        ∫⁻ z in C, stepKernel z D ∂prefixMeasure := by
    -- Proof comment: evaluate the restricted split law on the measurable rectangle `C × D`.
    have hsplitEvent : splitTuple ⁻¹' (C ×ˢ D) = prefixEvent ∩ lastEvent := by
      ext ω
      simp [splitTuple, prefixEvent, lastEvent]
    calc
      ((μ.restrict B).map splitTuple) (C ×ˢ D)
          = ((μ.restrict histEvent).map (X (tLast + s))) D := by
              rw [Measure.map_apply hsplitTupleMeas (hC.prod hD)]
              rw [Measure.map_apply (hX_meas (tLast + s)) hD]
              rw [Measure.restrict_apply (hsplitTupleMeas (hC.prod hD))]
              rw [Measure.restrict_apply hlastEventMeas]
              rw [hsplitEvent]
              simp [histEvent, prefixEvent, lastEvent, Set.inter_assoc,
                Set.inter_left_comm, Set.inter_comm]
      _ = ((transitionKernel κ dt) ∘ₘ ((μ.restrict histEvent).map (X (tPrev + s)))) D := by
            rw [hstepLaw]
      _ = ((transitionKernel κ dt) ∘ₘ
            (((prefixMeasure.restrict C).map (fun z : Fin (n + 1) → E ↦ z (Fin.last n))))) D := by
            rw [hhistPresent]
      _ = ∫⁻ y, transitionKernel κ dt y D
            ∂(((prefixMeasure.restrict C).map (fun z : Fin (n + 1) → E ↦ z (Fin.last n)))) := by
            let κ₀ : Kernel Unit E :=
              Kernel.const Unit (((prefixMeasure.restrict C).map (fun z : Fin (n + 1) → E ↦
                z (Fin.last n))))
            have hcomp :
                (transitionKernel κ dt ∘ₖ κ₀) () =
                  (transitionKernel κ dt) ∘ₘ
                    (((prefixMeasure.restrict C).map (fun z : Fin (n + 1) → E ↦ z (Fin.last n)))) := by
              simp [κ₀]
            rw [← hcomp, Kernel.comp_apply' _ _ _ hD]
            simp [κ₀]
      _ = ∫⁻ z in C, transitionKernel κ dt (z (Fin.last n)) D ∂prefixMeasure := by
            rw [MeasureTheory.lintegral_map'
              (Kernel.measurable_coe (transitionKernel κ dt) hD).aemeasurable
              (measurable_pi_apply (Fin.last n)).aemeasurable]
      _ = ∫⁻ z in C, stepKernel z D ∂prefixMeasure := by
            simp [stepKernel]
  calc
    ((μ.restrict B).map splitTuple) (C ×ˢ D)
        = ∫⁻ z in C, stepKernel z D ∂prefixMeasure := hrealizedRect
    _ = (prefixMeasure ⊗ₘ stepKernel) (C ×ˢ D) := by
          symm
          simpa using (Measure.compProd_apply_prod (μ := prefixMeasure) (κ := stepKernel) hC hD)

/-- Helper for Theorem 17.9: on every history event, the successor observable and the averaged
prefix observable have the same set integral. -/
lemma setIntegral_strictSuccessorFutureTuple_eq_prefixAverage
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    {n : ℕ} {f : (Fin (n + 2) → E) → ℝ} (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (Set.range f))
    {t : Fin (n + 2) → I} (ht : StrictMono t)
    {s : I} {x : E} {B : Set Ω}
    (hB : MeasurableSet[generatedFiltrationSpace X s] B) :
    let μ : Measure Ω := (P x : Measure Ω)
    let tp : Fin (n + 1) → I := fun i ↦ t i.castSucc
    let tPrev : I := tp (Fin.last n)
    let tLast : I := t (Fin.last (n + 1))
    let dt : I :=
      ⟨tLast.1 - tPrev.1, hsub (le_of_lt (ht (Fin.castSucc_lt_last (Fin.last n))))⟩
    let g : (Fin (n + 1) → E) → ℝ :=
      fun z ↦ ∫ y, f (Fin.snoc z y) ∂transitionKernel κ dt (z (Fin.last n))
    ∫ ω in B, f (futurePathCoordinates X s t ω) ∂μ =
      ∫ ω in B, g (futurePathCoordinates X s tp ω) ∂μ := by
  let μ : Measure Ω := (P x : Measure Ω)
  let tp : Fin (n + 1) → I := fun i ↦ t i.castSucc
  let tPrev : I := tp (Fin.last n)
  let tLast : I := t (Fin.last (n + 1))
  let _ : IsMarkovKernel κ :=
    IsTimeHomogeneousMarkovProcess.isMarkovKernel (X := X) (P := P) (κ := κ)
  let dt : I :=
    ⟨tLast.1 - tPrev.1, hsub (le_of_lt (ht (Fin.castSucc_lt_last (Fin.last n))))⟩
  let g : (Fin (n + 1) → E) → ℝ :=
    fun z ↦ ∫ y, f (Fin.snoc z y) ∂transitionKernel κ dt (z (Fin.last n))
  let prefixTuple : Ω → Fin (n + 1) → E := futurePathCoordinates X s tp
  let splitTuple : Ω → (Fin (n + 1) → E) × E := fun ω ↦ (prefixTuple ω, X (tLast + s) ω)
  let prefixMeasure : Measure (Fin (n + 1) → E) := ((μ.restrict B).map prefixTuple)
  let stepKernel : Kernel (Fin (n + 1) → E) E :=
    Kernel.comap (transitionKernel κ dt) (fun z ↦ z (Fin.last n)) (by fun_prop)
  let _ : IsFiniteKernel stepKernel := by
    refine ⟨⟨1, by simp, fun z ↦ ?_⟩⟩
    simp [stepKernel]
  have hX_meas : ∀ r : I, Measurable (X r) := fun r ↦ hMarkov.measurable_process r
  have hg_meas : Measurable g := by
    letI : IsSFiniteKernel stepKernel := by infer_instance
    have happend_meas :
        Measurable (fun p : (Fin (n + 1) → E) × E ↦ f (Fin.snoc p.1 p.2)) :=
      hf_meas.comp (measurable_tupleSnoc (E := E))
    -- Proof comment: the averaged successor observable is measurable on the prefix space because
    -- the split observable is measurable on the product space.
    have hg_meas' :
        StronglyMeasurable fun z : Fin (n + 1) → E ↦
          ∫ y, f (Fin.snoc z y) ∂stepKernel z := by
      exact
        (happend_meas.stronglyMeasurable.integral_kernel_prod_right'
          (κ := stepKernel))
    simpa [g, stepKernel] using hg_meas'.measurable
  have hprefixTupleMeas : Measurable prefixTuple := by
    simpa [prefixTuple] using measurable_futurePathCoordinates X hX_meas s tp
  have hsplitTupleMeas : Measurable splitTuple := by
    exact hprefixTupleMeas.prodMk (hX_meas (tLast + s))
  have hsplitLaw :
      ((μ.restrict B).map splitTuple) = prefixMeasure ⊗ₘ stepKernel := by
    -- Proof comment: the restricted future tuple law factors through the prefix law and the final
    -- transition from the predecessor state.
    simpa [μ, tp, tPrev, tLast, dt, prefixTuple, splitTuple, prefixMeasure, stepKernel] using
      (restrictedFutureSuccSplitLaw_eq_compProd_on_historyEvent X P κ hsub ht hB)
  have happendInt :
      Integrable (fun p : (Fin (n + 1) → E) × E ↦ f (Fin.snoc p.1 p.2)) (prefixMeasure ⊗ₘ stepKernel) := by
    -- Proof comment: the split observable is bounded because it factors through the bounded
    -- tuple observable `f`.
    letI : IsFiniteMeasure (prefixMeasure ⊗ₘ stepKernel) := by infer_instance
    obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range f) hf_bdd
    refine Integrable.of_bound
      ((hf_meas.comp (measurable_tupleSnoc (E := E))).aestronglyMeasurable) C ?_
    exact Filter.Eventually.of_forall fun p ↦ hC _ ⟨Fin.snoc p.1 p.2, rfl⟩
  calc
    ∫ ω in B, f (futurePathCoordinates X s t ω) ∂μ
        = ∫ z, f (Fin.snoc z.1 z.2) ∂((μ.restrict B).map splitTuple) := by
            have hsplit :
                futurePathCoordinates X s t =
                  fun ω ↦ (Fin.snoc (prefixTuple ω) (X (tLast + s) ω) : Fin (n + 2) → E) := by
              simpa [prefixTuple, tLast, splitTuple] using futurePathCoordinates_succSplit X s t
            rw [show ∫ ω in B, f (futurePathCoordinates X s t ω) ∂μ =
                ∫ ω, f (futurePathCoordinates X s t ω) ∂(μ.restrict B) by rfl]
            rw [hsplit]
            exact
              (MeasureTheory.integral_map hsplitTupleMeas.aemeasurable
                ((hf_meas.comp (measurable_tupleSnoc (E := E))).aestronglyMeasurable)).symm
    _ = ∫ z, f (Fin.snoc z.1 z.2) ∂(prefixMeasure ⊗ₘ stepKernel) := by rw [hsplitLaw]
    _ = ∫ z, g z ∂prefixMeasure := by
          simpa [g, stepKernel] using
            (MeasureTheory.Measure.integral_compProd (μ := prefixMeasure) (κ := stepKernel)
              happendInt)
    _ = ∫ ω in B, g (futurePathCoordinates X s tp ω) ∂μ := by
          rw [show ∫ ω in B, g (futurePathCoordinates X s tp ω) ∂μ =
              ∫ ω, g (prefixTuple ω) ∂(μ.restrict B) by rfl]
          exact
            MeasureTheory.integral_map hprefixTupleMeas.aemeasurable
              hg_meas.aestronglyMeasurable

/-- Helper for Theorem 17.9: once duplicate times are removed, only the strict-chain successor
induction remains. -/
-- Route correction: the duplicate-time transport is already isolated in the ordered-image
-- factorization lemmas, so this helper keeps only the strict tuple case and leaves the remaining
-- blocker as the `n ≥ 2` successor-step induction.
lemma strictOrderedFutureCoordinateFormula_of_isTimeHomogeneousMarkovProcess
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ]
    {n : ℕ} {f : (Fin n → E) → ℝ} (hf_meas : Measurable f)
    (hf_bdd : Bornology.IsBounded (Set.range f))
    {t : Fin n → I} (ht : StrictMono t) (s x) (hs : 0 ≤ s) :
    (P x)[fun ω ↦ f (futurePathCoordinates X s t ω) | generatedFiltrationSpace X s] =ᵐ[
      (P x : Measure Ω)]
      fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω) := by
  let _ : IsMarkovKernel κ :=
    IsTimeHomogeneousMarkovProcess.isMarkovKernel (X := X) (P := P) (κ := κ)
  induction n with
  | zero =>
      -- Proof comment: the strict empty tuple case is the already isolated constant formula.
      exact
        orderedFutureCoordinateFormula_zero_of_isTimeHomogeneousMarkovProcess
          X P κ hf_meas hf_bdd t ht.monotone s x hs
  | succ n ih =>
      cases n with
      | zero =>
          -- Proof comment: the strict singleton case is exactly the one-step Markov formula.
          exact
            orderedFutureCoordinateFormula_one_of_isTimeHomogeneousMarkovProcess
              X P κ hf_meas hf_bdd t ht.monotone s x hs
      | succ n =>
          let tp : Fin (n + 1) → I := fun i ↦ t i.castSucc
          let tPrev : I := tp (Fin.last n)
          let tLast : I := t (Fin.last (n + 1))
          let dt : I :=
            ⟨tLast.1 - tPrev.1, hsub (le_of_lt (ht (Fin.castSucc_lt_last (Fin.last n))))⟩
          let g : (Fin (n + 1) → E) → ℝ :=
            fun z ↦ ∫ y, f (Fin.snoc z y) ∂transitionKernel κ dt (z (Fin.last n))
          have htp : StrictMono tp := by
            -- Proof comment: the cast-successor prefix inherits strict monotonicity from `t`.
            intro i j hij
            exact ht (by simpa using hij)
          have hg_meas : Measurable g := by
            let stepKernel : Kernel (Fin (n + 1) → E) E :=
              Kernel.comap (transitionKernel κ dt) (fun z ↦ z (Fin.last n)) (by fun_prop)
            letI : IsSFiniteKernel stepKernel := by infer_instance
            have hsnoc_meas :
                Measurable
                  (fun p : (Fin (n + 1) → E) × E ↦ (Fin.snoc p.1 p.2 : Fin (n + 2) → E)) :=
              measurable_tupleSnoc (E := E)
            have happend_meas :
                Measurable (fun p : (Fin (n + 1) → E) × E ↦ f (Fin.snoc p.1 p.2)) :=
              hf_meas.comp hsnoc_meas
            -- Proof comment: the successor observable is measurable on the split tuple space, so
            -- integrating it against the last-step kernel gives a measurable prefix observable.
            have hg_meas' :
                StronglyMeasurable fun z : Fin (n + 1) → E ↦
                  ∫ y, f (Fin.snoc z y) ∂stepKernel z := by
              exact
                (happend_meas.stronglyMeasurable.integral_kernel_prod_right'
                  (κ := stepKernel))
            simpa [g, stepKernel, dt]
              using hg_meas'.measurable
          have hg_bdd : Bornology.IsBounded (Set.range g) := by
            obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range f) hf_bdd
            refine isBounded_iff_forall_norm_le.2 ⟨C, ?_⟩
            intro r hr
            rcases hr with ⟨z, rfl⟩
            letI : IsFiniteMeasure ((transitionKernel κ dt) (z (Fin.last n))) := by
              refine ⟨by
                simpa using (show
                  ((transitionKernel κ dt) (z (Fin.last n))) Set.univ < ⊤ by simp)⟩
            have hfC :
                ∀ᵐ y ∂transitionKernel κ dt (z (Fin.last n)), ‖f (Fin.snoc z y)‖ ≤ C :=
              Filter.Eventually.of_forall fun y ↦ hC _ ⟨Fin.snoc z y, rfl⟩
            have hnorm :
                ‖∫ y, f (Fin.snoc z y) ∂transitionKernel κ dt (z (Fin.last n))‖ ≤
                  C * (((transitionKernel κ dt) (z (Fin.last n))) Set.univ).toReal := by
              exact
                (MeasureTheory.norm_integral_le_of_norm_le_const
                  (μ := transitionKernel κ dt (z (Fin.last n))) hfC)
            have hrow_univ :
                ((transitionKernel κ dt) (z (Fin.last n))) Set.univ = 1 := by
              simp
            calc
              ‖∫ y, f (Fin.snoc z y) ∂transitionKernel κ dt (z (Fin.last n))‖
                  ≤ C * (((transitionKernel κ dt) (z (Fin.last n))) Set.univ).toReal := hnorm
              _ = C * 1 := by rw [hrow_univ, ENNReal.toReal_one]
              _ = C := by simp
          have hprefix :
              (P x)[fun ω ↦ g (futurePathCoordinates X s tp ω) |
                  generatedFiltrationSpace X s] =ᵐ[(P x : Measure Ω)]
                fun ω ↦ ∫ y, g (fun i ↦ y (tp i)) ∂κ (X s ω) := by
            -- Proof comment: the induction hypothesis already handles the strict prefix tuple and
            -- the successor observable `g`.
            exact ih hg_meas hg_bdd (t := tp) htp
          have hX_meas : ∀ r : I, Measurable (X r) := fun r ↦ hMarkov.measurable_process r
          let μ : Measure Ω := (P x : Measure Ω)
          let prefixProjection : (I → E) → Fin (n + 1) → E := fun y i ↦ y (tp i)
          have hprefixProjection_meas : Measurable prefixProjection := by
            -- Proof comment: the kernel-side prefix projection is the ordered coordinate map for
            -- `tp`.
            simpa [prefixProjection] using
              measurable_pathCoordinateProjection (I := I) (E := E) tp
          have hleft_int :
              Integrable (fun ω ↦ f (futurePathCoordinates X s t ω)) μ := by
            obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range f) hf_bdd
            -- Proof comment: the strict successor observable is bounded on the probability space
            -- `(Ω, P x)`.
            refine Integrable.of_bound
              (hf_meas.comp (measurable_futurePathCoordinates X hX_meas s t)).aestronglyMeasurable
              C ?_
            exact Filter.Eventually.of_forall fun ω ↦ hC _ ⟨futurePathCoordinates X s t ω, rfl⟩
          have hprefix_int :
              Integrable (fun ω ↦ g (futurePathCoordinates X s tp ω)) μ := by
            obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
            -- Proof comment: the prefix observable is also bounded on the same probability
            -- space.
            refine Integrable.of_bound
              (hg_meas.comp (measurable_futurePathCoordinates X hX_meas s tp)).aestronglyMeasurable
              C ?_
            exact Filter.Eventually.of_forall fun ω ↦ hC _ ⟨futurePathCoordinates X s tp ω, rfl⟩
          have hkernelPrefix_meas :
              Measurable fun z : E ↦ ∫ y, g (prefixProjection y) ∂κ z := by
            -- Proof comment: integrating the measurable bounded prefix functional along the path
            -- kernel is measurable in the starting state.
            exact
              ((hg_meas.comp hprefixProjection_meas).stronglyMeasurable.integral_kernel :
                StronglyMeasurable fun z : E ↦ ∫ y, g (prefixProjection y) ∂κ z).measurable
          have hkernelPrefix_meas_generated :
              Measurable[generatedFiltrationSpace X s]
                fun ω ↦ ∫ y, g (prefixProjection y) ∂κ (X s ω) := by
            -- Proof comment: the kernel-side prefix average depends on the history only through
            -- the present state `X s`.
            exact hkernelPrefix_meas.comp <|
              Measurable.of_comap_le (show MeasurableSpace.comap (X s) mE ≤
                  generatedFiltrationSpace X s by
                exact le_iSup_of_le s <| le_iSup_of_le le_rfl le_rfl)
          have hkernelPrefix_meas_ambient :
              Measurable fun ω ↦ ∫ y, g (prefixProjection y) ∂κ (X s ω) := by
            exact hkernelPrefix_meas.comp (hX_meas s)
          have htupleIntegral_eq :
              ∀ {m : ℕ} (u : Fin m → I) (φ : (Fin m → E) → ℝ), Measurable φ → ∀ z : E,
                ∫ y, φ (fun i ↦ y (u i)) ∂κ z =
                  ∫ ω, φ (fun i ↦ X (u i) ω) ∂(P z : Measure Ω) := by
            intro m u φ hφ_meas z
            let tupleProjection : (I → E) → Fin m → E := fun y i ↦ y (u i)
            let realizedTuple : Ω → Fin m → E := fun ω i ↦ X (u i) ω
            have htupleProjection_meas : Measurable tupleProjection := by
              simpa [tupleProjection] using
                measurable_pathCoordinateProjection (I := I) (E := E) u
            have hrealizedTuple_meas : Measurable realizedTuple := by
              -- Proof comment: the realized finite tuple is coordinatewise measurable.
              refine measurable_pi_lambda _ fun i ↦ ?_
              simpa [realizedTuple] using hX_meas (u i)
            calc
              ∫ y, φ (tupleProjection y) ∂κ z
                  = ∫ p, φ p ∂((κ z).map tupleProjection) := by
                      symm
                      exact
                        MeasureTheory.integral_map htupleProjection_meas.aemeasurable
                          hφ_meas.aestronglyMeasurable
              _ = ∫ p, φ p ∂((P z : Measure Ω).map realizedTuple) := by
                    simpa [tupleProjection, realizedTuple] using
                      congrArg (fun ν : Measure (Fin m → E) ↦ ∫ p, φ p ∂ν)
                        (pathKernelRow_map_orderedTuple_eq_realizedTupleLaw X P κ u z)
              _ = ∫ ω, φ (realizedTuple ω) ∂(P z : Measure Ω) := by
                    exact
                      MeasureTheory.integral_map hrealizedTuple_meas.aemeasurable
                        hφ_meas.aestronglyMeasurable
          have hkernel_eq :
              (fun ω ↦ ∫ y, g (fun i ↦ y (tp i)) ∂κ (X s ω)) =
                fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω) := by
            -- Proof comment: evaluate both kernel-side tuple integrals through the realized path
            -- law at time `s = 0`, where the strict split integral identity is already proved on
            -- the whole space.
            funext ω
            have hsplit0 :
                ∫ ω' in (Set.univ : Set Ω), f (futurePathCoordinates X 0 t ω') ∂(P (X s ω) : Measure Ω) =
                  ∫ ω' in (Set.univ : Set Ω), g (futurePathCoordinates X 0 tp ω') ∂
                    (P (X s ω) : Measure Ω) := by
              simpa [tp, tPrev, tLast, dt, g] using
                (setIntegral_strictSuccessorFutureTuple_eq_prefixAverage
                  X P κ hsub hf_meas hf_bdd ht
                  (s := 0) (x := X s ω) (B := Set.univ)
                  (show MeasurableSet[generatedFiltrationSpace X 0] (Set.univ : Set Ω) by simp))
            have hleft0 :
                ∫ ω' in (Set.univ : Set Ω), f (futurePathCoordinates X 0 t ω') ∂
                    (P (X s ω) : Measure Ω) =
                  ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω) := by
              have hfuture0_t :
                  (fun ω' ↦ f (futurePathCoordinates X 0 t ω')) =
                    fun ω' ↦ f (fun i ↦ X (t i) ω') := by
                funext ω'
                have htuple : futurePathCoordinates X 0 t ω' = fun i ↦ X (t i) ω' := by
                  funext i
                  simp [futurePathCoordinates]
                simpa [htuple]
              calc
                ∫ ω' in (Set.univ : Set Ω), f (futurePathCoordinates X 0 t ω') ∂
                    (P (X s ω) : Measure Ω)
                    = ∫ ω', f (futurePathCoordinates X 0 t ω') ∂(P (X s ω) : Measure Ω) := by simp
                _ = ∫ ω', f (fun i ↦ X (t i) ω') ∂(P (X s ω) : Measure Ω) := by
                      rw [hfuture0_t]
                _ = ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω) := by
                      symm
                      exact htupleIntegral_eq t f hf_meas (X s ω)
            have hright0 :
                ∫ ω' in (Set.univ : Set Ω), g (futurePathCoordinates X 0 tp ω') ∂
                    (P (X s ω) : Measure Ω) =
                  ∫ y, g (fun i ↦ y (tp i)) ∂κ (X s ω) := by
              have hfuture0_tp :
                  (fun ω' ↦ g (futurePathCoordinates X 0 tp ω')) =
                    fun ω' ↦ g (fun i ↦ X (tp i) ω') := by
                funext ω'
                have htuple : futurePathCoordinates X 0 tp ω' = fun i ↦ X (tp i) ω' := by
                  funext i
                  simp [futurePathCoordinates]
                simpa [htuple]
              calc
                ∫ ω' in (Set.univ : Set Ω), g (futurePathCoordinates X 0 tp ω') ∂
                    (P (X s ω) : Measure Ω)
                    = ∫ ω', g (futurePathCoordinates X 0 tp ω') ∂(P (X s ω) : Measure Ω) := by simp
                _ = ∫ ω', g (fun i ↦ X (tp i) ω') ∂(P (X s ω) : Measure Ω) := by
                      rw [hfuture0_tp]
                _ = ∫ y, g (fun i ↦ y (tp i)) ∂κ (X s ω) := by
                      symm
                      exact htupleIntegral_eq tp g hg_meas (X s ω)
            calc
              ∫ y, g (fun i ↦ y (tp i)) ∂κ (X s ω)
                  = ∫ ω' in (Set.univ : Set Ω), g (futurePathCoordinates X 0 tp ω') ∂
                      (P (X s ω) : Measure Ω) := hright0.symm
              _ = ∫ ω' in (Set.univ : Set Ω), f (futurePathCoordinates X 0 t ω') ∂
                    (P (X s ω) : Measure Ω) := hsplit0.symm
              _ = ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω) := hleft0
          have hcompare :
              (P x)[fun ω ↦ f (futurePathCoordinates X s t ω) | generatedFiltrationSpace X s] =ᵐ[
                μ]
                fun ω ↦ ∫ y, g (fun i ↦ y (tp i)) ∂κ (X s ω) := by
            obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
            symm
            refine
              (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
                (generatedFiltrationSpace_le_ambient_of_measurable X hX_meas s)
                hleft_int
                (fun B _ hμB ↦ by
                  -- Proof comment: the kernel-side prefix average is uniformly bounded on each
                  -- history event because every row of `κ` is a probability measure.
                  refine IntegrableOn.of_bound hμB hkernelPrefix_meas_ambient.aestronglyMeasurable
                    C ?_
                  refine Filter.Eventually.of_forall fun ω ↦ ?_
                  letI : IsFiniteMeasure (κ (X s ω)) := by infer_instance
                  have hrowC :
                      ∀ᵐ y ∂κ (X s ω), ‖g (prefixProjection y)‖ ≤ C :=
                    Filter.Eventually.of_forall fun y ↦ hC _ ⟨prefixProjection y, rfl⟩
                  simpa [prefixProjection] using
                    (MeasureTheory.norm_integral_le_of_norm_le_const
                      (μ := κ (X s ω)) hrowC))
                (fun B hB hμB ↦ by
                  have hB_ambient : MeasurableSet B := by
                    exact generatedFiltrationSpace_le_ambient_of_measurable X hX_meas s B hB
                  have hprefix_setIntegral :
                      ∫ ω in B, (∫ y, g (fun i ↦ y (tp i)) ∂κ (X s ω)) ∂μ =
                        ∫ ω in B, g (futurePathCoordinates X s tp ω) ∂μ := by
                    calc
                      ∫ ω in B, (∫ y, g (fun i ↦ y (tp i)) ∂κ (X s ω)) ∂μ
                          = ∫ ω in B,
                              (μ[fun ω ↦ g (futurePathCoordinates X s tp ω) |
                                generatedFiltrationSpace X s]) ω ∂μ := by
                                  refine MeasureTheory.setIntegral_congr_ae hB_ambient ?_
                                  filter_upwards [hprefix] with ω hω hωB
                                  exact hω.symm
                      _ = ∫ ω in B, g (futurePathCoordinates X s tp ω) ∂μ := by
                            exact
                              MeasureTheory.setIntegral_condExp
                                (generatedFiltrationSpace_le_ambient_of_measurable
                                  X hX_meas s)
                                hprefix_int hB
                  calc
                    ∫ ω in B, (∫ y, g (fun i ↦ y (tp i)) ∂κ (X s ω)) ∂μ
                        = ∫ ω in B, g (futurePathCoordinates X s tp ω) ∂μ := hprefix_setIntegral
                    _ = ∫ ω in B, f (futurePathCoordinates X s t ω) ∂μ := by
                            symm
                            simpa [μ, tp, tPrev, tLast, dt, g] using
                              (setIntegral_strictSuccessorFutureTuple_eq_prefixAverage
                                X P κ hsub hf_meas hf_bdd ht hB))
                hkernelPrefix_meas_generated.aestronglyMeasurable)
          exact hcompare.trans <| Filter.EventuallyEq.of_eq hkernel_eq

/-- Helper for Theorem 17.9: the time-homogeneous Markov owner should first be upgraded to the
ordered finite-coordinate conditional-expectation formula before the path-space formula is
recovered. -/
-- Route correction: the rowwise path-law transport to finite tuples is now isolated in
-- `pathKernelRow_map_orderedTuple_eq_realizedTupleLaw`, and the empty-tuple case is discharged by
-- `orderedFutureCoordinateFormula_zero_of_isTimeHomogeneousMarkovProcess`; the duplicate-time
-- transport is now isolated in `monotoneFutureTupleFactorsThroughOrderedImage`, so the remaining
-- blocker is the strict-chain successor-step induction on history events.
lemma hasOrderedFutureCoordinateConditionalExpectationFormula_of_isTimeHomogeneousMarkovProcess
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)
    [hMarkov : IsTimeHomogeneousMarkovProcess X P κ] :
    HasOrderedFutureCoordinateConditionalExpectationFormula X P κ := by
  intro n f hf_meas hf_bdd t ht s x hs
  let J : Finset I := Finset.univ.image t
  let τ : Fin J.card → I := J.orderEmbOfFin rfl
  let lift : Fin n → Fin J.card := fun i ↦
    (J.orderIsoOfFin rfl).symm ⟨t i, by
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  let g : (Fin J.card → E) → ℝ := fun z ↦ f (fun i ↦ z (lift i))
  have hg_meas : Measurable g := by
    -- Proof comment: the strict-image observable is `f` composed with the fixed reindexing
    -- map back to the original monotone tuple.
    exact hf_meas.comp (measurable_tuplePostcompose (E := E) lift)
  have hg_bdd : Bornology.IsBounded (Set.range g) := by
    -- Proof comment: the reindexed observable still takes values in the original bounded range
    -- of `f`.
    refine hf_bdd.subset ?_
    intro r hr
    rcases hr with ⟨z, rfl⟩
    exact ⟨fun i ↦ z (lift i), rfl⟩
  have hfuture_factor :
      futurePathCoordinates X s t = fun ω i ↦ futurePathCoordinates X s τ ω (lift i) := by
    -- Proof comment: the original monotone tuple is obtained by repeating coordinates from its
    -- strict ordered image.
    simpa [J, τ, lift] using
      (monotoneFutureTupleFactorsThroughOrderedImage (X := X) (s := s) (t := t) ht)
  have hpath_factor :
      (fun y : I → E ↦ fun i ↦ y (t i)) = fun y i ↦ y (τ (lift i)) := by
    -- Proof comment: the same strict-image factorization holds for the path-space coordinate
    -- projection.
    simpa [J, τ, lift] using
      (monotonePathCoordinateProjectionFactorsThroughOrderedImage (E := E) (t := t) ht)
  have hfuture :
      (fun ω ↦ f (futurePathCoordinates X s t ω)) =
        fun ω ↦ g (futurePathCoordinates X s τ ω) := by
    -- Proof comment: after rewriting the future tuple through the strict image, the left test
    -- function is exactly `g`.
    funext ω
    have hω :
        futurePathCoordinates X s t ω = fun i ↦ futurePathCoordinates X s τ ω (lift i) := by
      simpa using congrFun hfuture_factor ω
    simp [g, hω]
  have hkernel :
      (fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω)) =
        fun ω ↦ ∫ y, g (fun i ↦ y (τ i)) ∂κ (X s ω) := by
    -- Proof comment: on the kernel side, the original coordinate projection is the same
    -- reindexing of the strict-image projection.
    funext ω
    refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
    have hy : (fun i ↦ y (t i)) = fun i ↦ y (τ (lift i)) := by
      simpa using congrFun hpath_factor y
    simp [g, hy]
  have hstrict :
      (P x)[fun ω ↦ g (futurePathCoordinates X s τ ω) |
          generatedFiltrationSpace X s] =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ∫ y, g (fun i ↦ y (τ i)) ∂κ (X s ω) := by
    -- Proof comment: once duplicate times are removed, the strict helper is exactly the desired
    -- conditional-expectation formula.
    exact
      strictOrderedFutureCoordinateFormula_of_isTimeHomogeneousMarkovProcess
        X P κ hsub hg_meas hg_bdd (t := τ) (J.orderEmbOfFin rfl).strictMono s x hs
  calc
    (P x)[fun ω ↦ f (futurePathCoordinates X s t ω) | generatedFiltrationSpace X s] =ᵐ[
        (P x : Measure Ω)]
          (P x)[fun ω ↦ g (futurePathCoordinates X s τ ω) |
            generatedFiltrationSpace X s] := by
              exact MeasureTheory.condExp_congr_ae (Filter.EventuallyEq.of_eq hfuture)
    _ =ᵐ[(P x : Measure Ω)] fun ω ↦ ∫ y, g (fun i ↦ y (τ i)) ∂κ (X s ω) := hstrict
    _ =ᵐ[(P x : Measure Ω)] fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X s ω) :=
      Filter.EventuallyEq.of_eq hkernel.symm

/-- Helper for Theorem 17.9: once a specific path-space kernel and the source-facing realization
data are fixed, the Chapter 17 future-path conditional-expectation formula is equivalent to the
corresponding time-homogeneous Markov owner. -/
-- Proof comment: the forward implication factors through the ordered finite-coordinate formula
-- and then uses the path/ordered equivalence above; the backward implication is the direct owner
-- reconstruction theorem from the fixed initial state and path law.
theorem
    isTimeHomogeneousMarkovProcess_iff_hasFuturePathConditionalExpectationFormula_of_fixedPathKernel
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (I → E))
    (hX_meas : ∀ t, Measurable (X t))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun t : I ↦ X t ω))
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I)
    :
    IsTimeHomogeneousMarkovProcess X P κ ↔
      HasFuturePathConditionalExpectationFormula X P κ := by
  constructor
  · intro hMarkov
    letI : IsTimeHomogeneousMarkovProcess X P κ := hMarkov
    have hOrdered :
        HasOrderedFutureCoordinateConditionalExpectationFormula X P κ :=
      hasOrderedFutureCoordinateConditionalExpectationFormula_of_isTimeHomogeneousMarkovProcess
        X P κ hsub
    have hiff :=
      hasFuturePathConditionalExpectationFormula_iff_hasOrderedFutureCoordinateFormula
        X P κ hX_meas hsub
    -- Proof comment: upgrade the owner first to the ordered finite-coordinate formula, then use
    -- the ordered-to-path equivalence already isolated above.
    exact hiff.mpr hOrdered
  · -- Proof comment: the backward implication is exactly the direct owner reconstruction theorem
    -- from the already fixed initial state and path law.
    exact
      isTimeHomogeneousMarkovProcess_of_hasFuturePathConditionalExpectationFormula_of_pathKernel
        X P κ hX_meas hX0 hpath

-- Semantic recall: no direct mathlib theorem packages Klenke's path-space formula (17.3); the
-- source uses Borel singleton events, so the existential source-facing theorem keeps
-- `[MeasurableSingletonClass E]` for the backward path-law recovery step.
/-- Theorem 17.9: a stochastic process is a time-homogeneous Markov process if and only if there
exists a path-space kernel satisfying the future-path conditional-expectation formula (17.3),
with `P x` started from `x` at time `0`, for a nonnegative time set `I` modeled here as an
additive submonoid of `NNReal` that is closed under ordered differences. -/
-- Proof comment: package the forward fixed-kernel equivalence with the owner's path law, and in
-- the backward direction recover that path law from the `s = 0` specialization before invoking
-- the fixed-kernel reconstruction theorem.
theorem isTimeHomogeneousMarkovProcess_iff_hasFuturePathConditionalExpectationFormula_of_pathKernel
    [MeasurableSingletonClass E]
    (X : I → Ω → E) (P : E → ProbabilityMeasure Ω) (hX : IsStochasticProcess X)
    (hsub : ∀ ⦃s t : I⦄, s ≤ t → t.1 - s.1 ∈ I) :
    (∃ κ : Kernel E (I → E), IsTimeHomogeneousMarkovProcess X P κ) ↔
      ∃ κ : Kernel E (I → E),
        (∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1) ∧
          HasFuturePathConditionalExpectationFormula X P κ := by
  constructor
  · rintro ⟨κ, hMarkov⟩
    letI : IsTimeHomogeneousMarkovProcess X P κ := hMarkov
    have hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1 := hMarkov.initial_state
    have hpath :
        ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun t : I ↦ X t ω) :=
      hMarkov.path_law
    have hFuture :
        HasFuturePathConditionalExpectationFormula X P κ :=
      (isTimeHomogeneousMarkovProcess_iff_hasFuturePathConditionalExpectationFormula_of_fixedPathKernel
        X P κ hX.measurable hX0 hpath hsub).mp hMarkov
    -- Proof comment: once the fixed path kernel is chosen to be the owner's path law, the
    -- existential statement is just the forward implication of the fixed-kernel theorem.
    exact ⟨κ, hX0, hFuture⟩
  · rintro ⟨κ, hX0, hFuture⟩
    have hpath :
        ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun t : I ↦ X t ω) :=
      pathLaw_eq_kernel_of_futurePathFormula_zero X P κ hX.measurable hX0 hFuture
    refine ⟨κ, ?_⟩
    -- Proof comment: recover the owner by combining the `s = 0` path-law reconstruction with
    -- the direct backward implication from the future-path conditional-expectation formula.
    exact
      isTimeHomogeneousMarkovProcess_of_hasFuturePathConditionalExpectationFormula_of_pathKernel
        X P κ hX.measurable hX0 hpath hFuture

end ProbabilityTheory
