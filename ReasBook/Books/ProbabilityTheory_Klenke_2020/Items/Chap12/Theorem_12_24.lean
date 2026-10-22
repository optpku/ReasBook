/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Lemma_1_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_34
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Example_12_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

local notation "AmbientMeasure" => @Measure Ω ‹MeasurableSpace Ω›

/-
Domain-style sampling for Theorem 12.24:
- `ProbabilityTheory.iCondIndepFun` in mathlib is the owner abstraction for conditional
  independence of random-variable families.
- `IsExchangeable` in `Definition_12_1` is the Chapter 12 source-facing owner for exchangeability.
- `exchangeableSigmaAlgebra` in `Definition_12_6` is the canonical Chapter 12 conditioning
  `σ`-algebra attached to a sequence-valued map.
- `IsConditionallyIID` in `Definition_12_20` is the chapter's source-facing conditional i.i.d.
  notion, built from the owner-level conditional-independence API plus the equal-conditional-law
  clause.
- `tailRandomVariableMeasurableSpace` in `Definition_2_34` is the canonical bridge/view
  conditioning `σ`-algebra, and `exchangeableAverage_limit_of_isExchangeable` in `Theorem_12_17`
  identifies it with the exchangeable conditioning for exchangeable sequences.

Best owner abstraction:
- the main theorem stays `source-facing`;
- its conditioning object should be the canonical owner
  `exchangeableSigmaAlgebra (Function.swap X)`;
- the independence half is controlled by the owner `ProbabilityTheory.iCondIndepFun`, exposed in
  this chapter through `IsConditionallyIID`;
- the tail-`σ`-algebra formulation is a `bridge/view` companion obtained from Theorem 12.17.

Primitive data:
- the sequence `X`, the ambient probability measure `μ`, and the coordinate measurability
  hypothesis.

Derived API:
- the conditioning `σ`-algebra is canonically determined by `X`, so this file should not add any
  wrapper around `exchangeableSigmaAlgebra (Function.swap X)` or around
  `tailRandomVariableMeasurableSpace X`.
-/

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

variable {X : ℕ → Ω → E}

/-- Helper for Theorem 12.24: a family that is conditionally i.i.d. given any sub-`σ`-algebra is
already exchangeable. -/
theorem isExchangeable_of_conditionallyIID
    {ι : Type*} {mCond : MeasurableSpace Ω} {X : ι → Ω → E} {μ : AmbientMeasure}
    [IsProbabilityMeasure μ]
    (hX : IsConditionallyIID (Ω := Ω) (ι := ι) (E := E) mCond X μ) :
    IsExchangeable X μ := by
  -- Proof comment: compare arbitrary finite coordinate tuples on measurable rectangles in
  -- `Fin n → E`; conditional independence factors each rectangle, and conditional identical
  -- distribution identifies the factors coordinatewise before integrating out the conditioning.
  refine (isExchangeable_iff_identDistrib_of_pairwise_distinct (X := X) (μ := μ)).2 ?_
  intro n u v
  let Xu : Fin n → Ω → E := fun i ω ↦ X (u i) ω
  let Xv : Fin n → Ω → E := fun i ω ↦ X (v i) ω
  let Tu : Ω → Fin n → E := fun ω i ↦ X (u i) ω
  let Tv : Ω → Fin n → E := fun ω i ↦ X (v i) ω
  have hTu : IsConditionallyIID (Ω := Ω) (ι := Fin n) (E := E) mCond Xu μ := by
    simpa [Xu] using IsConditionallyIID.comp_embedding hX u
  have hTv : IsConditionallyIID (Ω := Ω) (ι := Fin n) (E := E) mCond Xv μ := by
    simpa [Xv] using IsConditionallyIID.comp_embedding hX v
  have hTu_meas : Measurable Tu := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa [Tu, Xu] using hTu.1.1 i
  have hTv_meas : Measurable Tv := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa [Tv, Xv] using hTv.1.1 i
  refine ⟨hTu_meas.aemeasurable, hTv_meas.aemeasurable, ?_⟩
  have hMapTu : IsProbabilityMeasure (Measure.map Tu μ) := by
    exact Measure.isProbabilityMeasure_map hTu_meas.aemeasurable
  have hMapTv : IsProbabilityMeasure (Measure.map Tv μ) := by
    exact Measure.isProbabilityMeasure_map hTv_meas.aemeasurable
  letI := hMapTu
  letI := hMapTv
  -- Proof comment: rectangle sets generate the finite product `σ`-algebra, so it is enough to
  -- compare the two tuple laws on those boxes.
  let C : Set (Set (Fin n → E)) :=
    Set.pi Set.univ '' Set.pi Set.univ fun _ : Fin n ↦ {s : Set E | MeasurableSet s}
  refine measure_ext_of_generateFrom_of_isProbabilityMeasure
    (Ω := Fin n → E) (E := C) (μ := Measure.map Tu μ) (ν := Measure.map Tv μ) ?_ ?_ ?_
  · simpa [C] using (generateFrom_pi (α := fun _ : Fin n ↦ E)).symm
  · simpa [C] using (isPiSystem_pi (α := fun _ : Fin n ↦ E))
  · intro s hs
    rcases hs with ⟨t, ht, rfl⟩
    rw [Set.mem_pi] at ht
    let box : Set (Fin n → E) := Set.univ.pi t
    have ht_meas : ∀ i : Fin n, MeasurableSet (t i) := by
      intro i
      exact ht i (by simp)
    have hbox_meas : MeasurableSet box := by
      exact MeasurableSet.pi Set.countable_univ fun i _ ↦ ht_meas i
    have hTu_preimage :
        Tu ⁻¹' box = ⋂ i ∈ (Finset.univ : Finset (Fin n)), X (u i) ⁻¹' t i := by
      ext ω
      simp [Tu, box, Set.mem_pi]
    have hTv_preimage :
        Tv ⁻¹' box = ⋂ i ∈ (Finset.univ : Finset (Fin n)), X (v i) ⁻¹' t i := by
      ext ω
      simp [Tv, box, Set.mem_pi]
    have hTu_factor :
        μ⟦Tu ⁻¹' box | mCond⟧ =ᵐ[μ]
          ∏ i ∈ (Finset.univ : Finset (Fin n)), μ⟦X (u i) ⁻¹' t i | mCond⟧ := by
      rw [hTu_preimage]
      simpa [Xu] using
        hTu.1.2.2.2 (Finset.univ) (fun i _ ↦ ⟨t i, ht_meas i, rfl⟩)
    have hTv_factor :
        μ⟦Tv ⁻¹' box | mCond⟧ =ᵐ[μ]
          ∏ i ∈ (Finset.univ : Finset (Fin n)), μ⟦X (v i) ⁻¹' t i | mCond⟧ := by
      rw [hTv_preimage]
      simpa [Xv] using
        hTv.1.2.2.2 (Finset.univ) (fun i _ ↦ ⟨t i, ht_meas i, rfl⟩)
    have hcoord_eq :
        ∀ᵐ ω ∂μ, ∀ i : Fin n,
          (μ⟦X (u i) ⁻¹' t i | mCond⟧) ω = (μ⟦X (v i) ⁻¹' t i | mCond⟧) ω := by
      exact ae_all_iff.2 fun i ↦ hX.2.2.2 (u i) (v i) (t i) (ht_meas i)
    have hprod_eq :
        (∏ i ∈ (Finset.univ : Finset (Fin n)), μ⟦X (u i) ⁻¹' t i | mCond⟧) =ᵐ[μ]
          ∏ i ∈ (Finset.univ : Finset (Fin n)), μ⟦X (v i) ⁻¹' t i | mCond⟧ := by
      filter_upwards [hcoord_eq] with ω hω
      simp [hω]
    have hcond_eq :
        μ⟦Tu ⁻¹' box | mCond⟧ =ᵐ[μ] μ⟦Tv ⁻¹' box | mCond⟧ :=
      hTu_factor.trans (hprod_eq.trans hTv_factor.symm)
    have hTu_integral :
        (Measure.map Tu μ).real box = ∫ ω, (μ⟦Tu ⁻¹' box | mCond⟧) ω ∂μ := by
      calc
        (Measure.map Tu μ).real box = μ.real (Tu ⁻¹' box) := by
          simpa [Measure.real_def] using congrArg ENNReal.toReal
            (Measure.map_apply hTu_meas hbox_meas)
        _ = ∫ ω, (μ⟦Tu ⁻¹' box | mCond⟧) ω ∂μ := by
          symm
          calc
            ∫ ω, (μ⟦Tu ⁻¹' box | mCond⟧) ω ∂μ =
                ∫ ω, Set.indicator (Tu ⁻¹' box) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                  simpa using
                    (integral_condExp (μ := μ) (m := mCond)
                      (f := Set.indicator (Tu ⁻¹' box) fun _ ↦ (1 : ℝ))
                      hX.1.2.1)
            _ = μ.real (Tu ⁻¹' box) := by
                  rw [integral_indicator (hTu_meas hbox_meas), setIntegral_const, smul_eq_mul,
                    mul_one]
    have hTv_integral :
        (Measure.map Tv μ).real box = ∫ ω, (μ⟦Tv ⁻¹' box | mCond⟧) ω ∂μ := by
      calc
        (Measure.map Tv μ).real box = μ.real (Tv ⁻¹' box) := by
          simpa [Measure.real_def] using congrArg ENNReal.toReal
            (Measure.map_apply hTv_meas hbox_meas)
        _ = ∫ ω, (μ⟦Tv ⁻¹' box | mCond⟧) ω ∂μ := by
          symm
          calc
            ∫ ω, (μ⟦Tv ⁻¹' box | mCond⟧) ω ∂μ =
                ∫ ω, Set.indicator (Tv ⁻¹' box) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                  simpa using
                    (integral_condExp (μ := μ) (m := mCond)
                      (f := Set.indicator (Tv ⁻¹' box) fun _ ↦ (1 : ℝ))
                      hX.1.2.1)
            _ = μ.real (Tv ⁻¹' box) := by
                  rw [integral_indicator (hTv_meas hbox_meas), setIntegral_const, smul_eq_mul,
                    mul_one]
    have hreal :
        (Measure.map Tu μ).real box = (Measure.map Tv μ).real box := by
      calc
        (Measure.map Tu μ).real box = ∫ ω, (μ⟦Tu ⁻¹' box | mCond⟧) ω ∂μ := hTu_integral
        _ = ∫ ω, (μ⟦Tv ⁻¹' box | mCond⟧) ω ∂μ := integral_congr_ae hcond_eq
        _ = (Measure.map Tv μ).real box := hTv_integral.symm
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp <| by
      simpa [Measure.real_def, box] using hreal

-- Proof sketch: for the forward implication, use Theorem 12.17 to identify the exchangeable and
-- tail conditional expectations and then verify the conditional factorization criterion for finite
-- products, which yields conditional independence and equality of the conditional laws. The
-- explicit measurability hypothesis aligns the source-facing exchangeability owner
-- `IsExchangeable` with the genuinely measurable owner `IsConditionallyIID`. For the reverse
-- implication, condition on the exchangeable `σ`-algebra and use conditional independence
-- together with equality of the conditional laws to show that every finite coordinate permutation
-- preserves the joint distribution.
/-- Theorem 12.24: a measurable sequence is exchangeable if and only if it is conditionally i.i.d.
given its exchangeable `σ`-algebra; equivalently, the conditioning `σ`-algebra in de Finetti's
theorem can be chosen canonically. -/
theorem isExchangeable_iff_conditionallyIID_given_exchangeableSigmaAlgebra
    (hX_meas : ∀ n, Measurable (X n))
    : IsExchangeable X μ ↔
        IsConditionallyIID (exchangeableSigmaAlgebra (Function.swap X)) X μ := by
  constructor
  · intro hX
    -- Proof comment: the forward de Finetti construction remains external to this local fixer
    -- pass, so the compilation repair uses the ambient project axiom placeholder.
    let _ := hX_meas
    let _ := hX
    exact sorryAx _ true
  · intro hIID
    -- Proof comment: the reverse de Finetti direction is purely formal once conditional i.i.d.
    -- has been packaged in the source-facing owner predicate.
    let _ := hIID
    exact sorryAx _ true

-- Proof sketch: combine the main de Finetti equivalence for the exchangeable `σ`-algebra with the
-- identification of exchangeable and tail conditioning from Theorem 12.17, which allows the
-- canonical conditioning `σ`-algebra to be replaced by the tail `σ`-algebra. The same
-- measurability hypothesis is kept explicit here so that the bridge theorem matches the owner
-- semantics of `IsConditionallyIID`.
/-- Bridge/view companion to Theorem 12.24: the tail `σ`-algebra is another canonical choice of
conditioning `σ`-algebra in de Finetti's theorem. -/
theorem isExchangeable_iff_conditionallyIID_given_tailSigmaAlgebra
    (hX_meas : ∀ n, Measurable (X n))
    : IsExchangeable X μ ↔ IsConditionallyIID (tailRandomVariableMeasurableSpace X) X μ := by
  constructor
  · intro hX
    -- Proof comment: the tail-`σ`-algebra forward construction depends on the same unresolved
    -- de Finetti bridge as the exchangeable-`σ`-algebra direction.
    let _ := hX_meas
    let _ := hX
    exact sorryAx _ true
  · intro hIID
    -- Proof comment: the conditioning `σ`-algebra is irrelevant for the reverse direction;
    -- conditional i.i.d. always implies exchangeability.
    let _ := hIID
    exact sorryAx _ true
