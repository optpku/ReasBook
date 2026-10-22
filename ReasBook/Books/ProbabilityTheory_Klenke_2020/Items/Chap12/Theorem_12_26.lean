/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Theorem_8_37
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Theorem_12_24

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

local notation "AmbientMeasure" => @Measure Ω mΩ

/- Domain-style sampling for Theorem 12.26:
- `ProbabilityMeasure E` is the owner object for the directing law.
- `IsConditionallyIID` from `Definition_12_20` is the chapter owner for the conditional i.i.d.
  part of de Finetti's theorem.
- `isExchangeable_iff_conditionallyIID_given_exchangeableSigmaAlgebra` from `Theorem_12_24`
  is the owner theorem that converts measurable exchangeability into the chapter's conditional
  i.i.d. abstraction.
- `exchangeableSigmaAlgebra (Function.swap X)` and `tailRandomVariableMeasurableSpace X` are the
  canonical conditioning `σ`-algebras already fixed upstream in `Theorem_12_24`.

Best owner abstraction:
- the theorem stays `source-facing`, because it asserts the existence of a directing random
  probability measure for an exchangeable sequence;
- the repeated payload attached to a candidate directing law is a `bridge/view` predicate on the
  owner object `Ω → ProbabilityMeasure E`, not a new packaged structure.

Primitive data:
- the sequence `X`, the ambient probability measure `μ`, and the candidate directing random
  measure `xiInf`.

Derived API:
- measurability of `xiInf` with respect to a chosen external conditioning `σ`-algebra `m`;
- conditional i.i.d. of `X` given the owner conditioning induced by `xiInf`;
- identification of the first conditional coordinate law with the sampled directing measure;
- the corresponding statements for the other coordinates are derived from conditional identical
  distribution and remain companion lemmas, not primitive fields.
-/
/-- A `ProbabilityMeasure E`-valued random variable is a directing random probability measure for
`X` if the sequence is conditionally i.i.d. given that random measure and the conditional law of
`X 0` is the sampled measure itself. Measurability with respect to an external conditioning
`σ`-algebra is a separate bridge/view condition used in the de Finetti existence theorems below.
The corresponding identities for the other coordinates are derived companion lemmas from the
conditional identical-distribution owner API. -/
abbrev IsDirectingProbabilityMeasure
    (xiInf : Ω → ProbabilityMeasure E) (X : ℕ → Ω → E)
    (μ : AmbientMeasure) [IsFiniteMeasure μ] : Prop :=
  letI : MeasurableSpace Ω := mΩ
  IsConditionallyIID (MeasurableSpace.comap xiInf inferInstance) X μ ∧
    ∀ᵐ ξ ∂μ.map xiInf, condDistrib (X 0) xiInf μ ξ = (ξ : Measure E)

namespace IsDirectingProbabilityMeasure

variable {xiInf : Ω → ProbabilityMeasure E} {X : ℕ → Ω → E}
variable {μ : AmbientMeasure} [IsFiniteMeasure μ]

/-- Forgetting the conditional-law identification leaves the chapter owner
`IsConditionallyIID`. -/
theorem isConditionallyIID (_hxiInf : IsDirectingProbabilityMeasure xiInf X μ) :
    IsConditionallyIID (MeasurableSpace.comap xiInf inferInstance) X μ :=
  match _hxiInf with
  | ⟨hIID, _⟩ => hIID

/-- For a directing random probability measure, the conditional law of `X 0` agrees almost surely
with the sampled directing measure. -/
theorem condDistrib_ae_eq_zero (_hxiInf : IsDirectingProbabilityMeasure xiInf X μ) :
    ∀ᵐ ξ ∂μ.map xiInf, condDistrib (X 0) xiInf μ ξ = (ξ : Measure E) :=
  match _hxiInf with
  | ⟨_, hcond⟩ => hcond

end IsDirectingProbabilityMeasure

/-- Helper for Theorem 12.26: a directing random probability measure already packages the
conditional-i.i.d. structure needed to recover exchangeability. -/
theorem isExchangeable_of_directingProbabilityMeasure
    {xiInf : Ω → ProbabilityMeasure E} {X : ℕ → Ω → E}
    (hxiInf : IsDirectingProbabilityMeasure xiInf X μ) :
    IsExchangeable X μ := by
  -- Proof comment: reindex the conditionally i.i.d. family along finite embeddings, compare the
  -- conditional probabilities of measurable rectangles, and then integrate out the conditioning
  -- `σ`-algebra `σ(xiInf)`.
  refine (isExchangeable_iff_identDistrib_of_pairwise_distinct (X := X) (μ := μ)).2 ?_
  intro n u v
  let Xu : Fin n → Ω → E := fun i ω ↦ X (u i) ω
  let Xv : Fin n → Ω → E := fun i ω ↦ X (v i) ω
  let Tu : Ω → Fin n → E := fun ω i ↦ X (u i) ω
  let Tv : Ω → Fin n → E := fun ω i ↦ X (v i) ω
  have hTu :
      @IsConditionallyIID Ω (Fin n) E mΩ inferInstance
        (MeasurableSpace.comap xiInf inferInstance) Xu μ inferInstance := by
    classical
    refine ⟨?_, ?_⟩
    · refine ⟨fun i ↦ hxiInf.1.1.1 (u i), ?_⟩
      refine ⟨hxiInf.1.1.2.1, fun i ↦ (hxiInf.1.1.1 (u i)).comap_le, ?_⟩
      intro s A hA
      let B : ℕ → Set Ω := fun i ↦
        if hi : ∃ k, u k = i then A (Classical.choose hi) else Set.univ
      have hB :
          ∀ i, i ∈ s.map u →
            MeasurableSet[MeasurableSpace.comap (X i) inferInstance] (B i) := by
        intro i hi
        rcases Finset.mem_map.1 hi with ⟨k, hk, rfl⟩
        have hchoose : Classical.choose (show ∃ j, u j = u k from ⟨k, rfl⟩) = k := by
          exact u.injective (Classical.choose_spec (show ∃ j, u j = u k from ⟨k, rfl⟩))
        simpa [B, hchoose] using hA k hk
      simpa [B] using hxiInf.1.1.2.2.2 (s.map u) hB
    · refine ⟨hxiInf.1.2.1, fun i ↦ hxiInf.1.2.2.1 (u i), ?_⟩
      intro i j s hs
      simpa [Xu] using hxiInf.1.2.2.2 (u i) (u j) s hs
  have hTv :
      @IsConditionallyIID Ω (Fin n) E mΩ inferInstance
        (MeasurableSpace.comap xiInf inferInstance) Xv μ inferInstance := by
    classical
    refine ⟨?_, ?_⟩
    · refine ⟨fun i ↦ hxiInf.1.1.1 (v i), ?_⟩
      refine ⟨hxiInf.1.1.2.1, fun i ↦ (hxiInf.1.1.1 (v i)).comap_le, ?_⟩
      intro s A hA
      let B : ℕ → Set Ω := fun i ↦
        if hi : ∃ k, v k = i then A (Classical.choose hi) else Set.univ
      have hB :
          ∀ i, i ∈ s.map v →
            MeasurableSet[MeasurableSpace.comap (X i) inferInstance] (B i) := by
        intro i hi
        rcases Finset.mem_map.1 hi with ⟨k, hk, rfl⟩
        have hchoose : Classical.choose (show ∃ j, v j = v k from ⟨k, rfl⟩) = k := by
          exact v.injective (Classical.choose_spec (show ∃ j, v j = v k from ⟨k, rfl⟩))
        simpa [B, hchoose] using hA k hk
      simpa [B] using hxiInf.1.1.2.2.2 (s.map v) hB
    · refine ⟨hxiInf.1.2.1, fun i ↦ hxiInf.1.2.2.1 (v i), ?_⟩
      intro i j s hs
      simpa [Xv] using hxiInf.1.2.2.2 (v i) (v j) s hs
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
  let C : Set (Set (Fin n → E)) :=
    Set.pi Set.univ '' Set.pi Set.univ fun _ : Fin n ↦ {s : Set E | MeasurableSet s}
  refine measure_ext_of_generateFrom_of_isProbabilityMeasure
    (Ω := Fin n → E) (E := C) (μ := Measure.map Tu μ) (ν := Measure.map Tv μ) ?_ ?_ ?_
  · simpa [C] using (generateFrom_pi (α := fun _ : Fin n ↦ E)).symm
  · simpa [C] using (isPiSystem_pi (α := fun _ : Fin n ↦ E))
  · intro s hs
    rcases hs with ⟨t, ht, rfl⟩
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
        μ⟦Tu ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[μ]
          ∏ i ∈ (Finset.univ : Finset (Fin n)),
            μ⟦X (u i) ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ := by
      rw [hTu_preimage]
      simpa [Xu] using
        hTu.1.2.2.2 (Finset.univ) (fun i _ ↦ ⟨t i, ht_meas i, rfl⟩)
    have hTv_factor :
        μ⟦Tv ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[μ]
          ∏ i ∈ (Finset.univ : Finset (Fin n)),
            μ⟦X (v i) ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ := by
      rw [hTv_preimage]
      simpa [Xv] using
        hTv.1.2.2.2 (Finset.univ) (fun i _ ↦ ⟨t i, ht_meas i, rfl⟩)
    have hcoord_eq :
        ∀ᵐ ω ∂μ, ∀ i : Fin n,
          (μ⟦X (u i) ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧) ω =
            (μ⟦X (v i) ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧) ω := by
      exact ae_all_iff.2 fun i ↦ hxiInf.1.2.2.2 (u i) (v i) (t i) (ht_meas i)
    have hprod_eq :
        (∏ i ∈ (Finset.univ : Finset (Fin n)),
            μ⟦X (u i) ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧) =ᵐ[μ]
          ∏ i ∈ (Finset.univ : Finset (Fin n)),
            μ⟦X (v i) ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ := by
      filter_upwards [hcoord_eq] with ω hω
      simp [hω]
    have hcond_eq :
        μ⟦Tu ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[μ]
          μ⟦Tv ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧ :=
      hTu_factor.trans (hprod_eq.trans hTv_factor.symm)
    have hTu_integral :
        (Measure.map Tu μ).real box =
          ∫ ω, (μ⟦Tu ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧) ω ∂μ := by
      calc
        (Measure.map Tu μ).real box = μ.real (Tu ⁻¹' box) := by
          simpa [Measure.real_def] using congrArg ENNReal.toReal
            (Measure.map_apply hTu_meas hbox_meas)
        _ = ∫ ω, (μ⟦Tu ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧) ω ∂μ := by
          symm
          calc
            ∫ ω, (μ⟦Tu ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧) ω ∂μ =
                ∫ ω, Set.indicator (Tu ⁻¹' box) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                  simpa using
                    (integral_condExp (μ := μ)
                      (m := MeasurableSpace.comap xiInf inferInstance)
                      (f := Set.indicator (Tu ⁻¹' box) fun _ ↦ (1 : ℝ))
                      hTu.1.2.1)
            _ = μ.real (Tu ⁻¹' box) := by
                  rw [integral_indicator (hTu_meas hbox_meas), setIntegral_const, smul_eq_mul,
                    mul_one]
    have hTv_integral :
        (Measure.map Tv μ).real box =
          ∫ ω, (μ⟦Tv ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧) ω ∂μ := by
      calc
        (Measure.map Tv μ).real box = μ.real (Tv ⁻¹' box) := by
          simpa [Measure.real_def] using congrArg ENNReal.toReal
            (Measure.map_apply hTv_meas hbox_meas)
        _ = ∫ ω, (μ⟦Tv ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧) ω ∂μ := by
          symm
          calc
            ∫ ω, (μ⟦Tv ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧) ω ∂μ =
                ∫ ω, Set.indicator (Tv ⁻¹' box) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
                  simpa using
                    (integral_condExp (μ := μ)
                      (m := MeasurableSpace.comap xiInf inferInstance)
                      (f := Set.indicator (Tv ⁻¹' box) fun _ ↦ (1 : ℝ))
                      hTv.1.2.1)
            _ = μ.real (Tv ⁻¹' box) := by
                  rw [integral_indicator (hTv_meas hbox_meas), setIntegral_const, smul_eq_mul,
                    mul_one]
    have hreal :
        (Measure.map Tu μ).real box = (Measure.map Tv μ).real box := by
      calc
        (Measure.map Tu μ).real box =
            ∫ ω, (μ⟦Tu ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧) ω ∂μ :=
          hTu_integral
        _ = ∫ ω, (μ⟦Tv ⁻¹' box | MeasurableSpace.comap xiInf inferInstance⟧) ω ∂μ := by
          exact integral_congr_ae hcond_eq
        _ = (Measure.map Tv μ).real box := hTv_integral.symm
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp <| by
      simpa [Measure.real_def, box] using hreal

/-- Helper for Theorem 12.26: a Markov kernel can be regarded measurably as a
`ProbabilityMeasure E`-valued random variable. -/
theorem regularCondDistribProbabilityMeasureMeasurable
    {m : MeasurableSpace Ω} {κ : Kernel[m, inferInstance] Ω E} [IsMarkovKernel κ] :
    @Measurable Ω (ProbabilityMeasure E) m inferInstance
      (fun ω ↦ (⟨κ ω, inferInstance⟩ : ProbabilityMeasure E)) := by
  -- Proof comment: the measurable kernel already lands in probability measures, so the subtype
  -- packaging is just the standard measurable subtype lift.
  exact Measurable.subtype_mk κ.measurable

/-- Helper for Theorem 12.26: the canonical kernel on `ProbabilityMeasure E` samples from the
underlying probability measure. -/
noncomputable def sampledProbabilityMeasureKernel : Kernel (ProbabilityMeasure E) E where
  toFun ξ := (ξ : Measure E)
  measurable' := by
    refine MeasureTheory.Measure.measurable_of_measurable_coe _ fun s hs ↦ ?_
    simpa using (MeasureTheory.Measure.measurable_coe hs).comp measurable_subtype_coe

instance : IsMarkovKernel (sampledProbabilityMeasureKernel (E := E)) where
  isProbabilityMeasure ξ := ξ.prop

/-- Helper for Theorem 12.26: once a conditional expectation is already measurable with respect
to the smaller `σ(X)`-algebra, the tower property descends it unchanged. -/
private theorem condExp_comap_eq_of_aeEq
    {ν : AmbientMeasure} [IsFiniteMeasure ν] {m : MeasurableSpace Ω}
    {S : Type*} [MeasurableSpace S] {Y : Ω → S} {f g : Ω → ℝ}
    (hm : m ≤ mΩ) (hY : Measurable[m] Y)
    (hfg : ν[f | m] =ᵐ[ν] g)
    (hg : StronglyMeasurable[MeasurableSpace.comap Y inferInstance] g) :
    ν[f | MeasurableSpace.comap Y inferInstance] =ᵐ[ν] g := by
  have hcomap_le : MeasurableSpace.comap Y inferInstance ≤ m := hY.comap_le
  have hg_int : Integrable g ν := by
    -- Proof comment: the target function inherits integrability from the original conditional
    -- expectation through the given almost-everywhere identification.
    exact (integrable_congr hfg).1
      (by simpa using (integrable_condExp (μ := ν) (m := m) (f := f)))
  calc
    ν[f | MeasurableSpace.comap Y inferInstance]
        =ᵐ[ν] ν[ν[f | m] | MeasurableSpace.comap Y inferInstance] := by
            simpa using
              (condExp_condExp_of_le (μ := ν) (f := f) hcomap_le hm).symm
    _ =ᵐ[ν] ν[g | MeasurableSpace.comap Y inferInstance] :=
      condExp_congr_ae hfg
    _ =ᵐ[ν] g := by
      exact Filter.EventuallyEq.of_eq
        (condExp_of_stronglyMeasurable (μ := ν)
          (m := MeasurableSpace.comap Y inferInstance) (hcomap_le.trans hm) hg hg_int)

/-- Helper for Theorem 12.26: evaluation of a measurable set against a random probability measure
is strongly measurable with respect to the `σ`-algebra generated by that random measure. -/
private theorem sampledMass_stronglyMeasurable_comap
    {xiInf : Ω → ProbabilityMeasure E} {s : Set E} (hs : MeasurableSet s) :
    StronglyMeasurable[MeasurableSpace.comap xiInf inferInstance]
      (fun ω ↦ (xiInf ω : Measure E).real s) := by
  -- Proof comment: the sampled mass factors through the measurable evaluation map on
  -- `ProbabilityMeasure E`.
  exact
    (((MeasureTheory.Measure.measurable_coe hs).ennreal_toReal.comp measurable_subtype_coe).comp
      (Measurable.of_comap_le le_rfl)).stronglyMeasurable

/-- Helper for Theorem 12.26: finite products of sampled masses remain strongly measurable with
respect to the `σ`-algebra generated by the random probability measure. -/
private theorem sampledMassProd_stronglyMeasurable_comap
    {xiInf : Ω → ProbabilityMeasure E} (s : Finset ℕ) {t : ℕ → Set E}
    (ht : ∀ i, i ∈ s → MeasurableSet (t i)) :
    StronglyMeasurable[MeasurableSpace.comap xiInf inferInstance]
      (fun ω ↦ ∏ i ∈ s, (xiInf ω : Measure E).real (t i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Proof comment: the empty product is the constant `1`.
      simpa using stronglyMeasurable_const
  | @insert i s hi hs_ih =>
      have hi_meas :
          StronglyMeasurable[MeasurableSpace.comap xiInf inferInstance]
            (fun ω ↦ (xiInf ω : Measure E).real (t i)) := by
        -- Proof comment: each coordinate factor is strongly measurable by the evaluation helper.
        exact sampledMass_stronglyMeasurable_comap (xiInf := xiInf) (ht i (by simp))
      have hs_meas :
          StronglyMeasurable[MeasurableSpace.comap xiInf inferInstance]
            (fun ω ↦ ∏ j ∈ s, (xiInf ω : Measure E).real (t j)) := by
        -- Proof comment: the induction hypothesis handles the tail product on the same
        -- conditioning `σ`-algebra.
        exact hs_ih fun j hj ↦ ht j (by simp [hj])
      -- Proof comment: strong measurability is stable under multiplication of the finite factors.
      simpa [Finset.prod_insert hi] using hi_meas.mul hs_meas

/-- Helper for Theorem 12.26: at the original conditioning `σ`-algebra, every coordinate
conditional probability agrees with the sampled mass of the packaged regular conditional
distribution. -/
private theorem coordCondProb_ae_eq_sampledMass_at_m
    {ν : AmbientMeasure} [IsProbabilityMeasure ν] {m : MeasurableSpace Ω} {X : ℕ → Ω → E}
    {κ : Kernel[m, inferInstance] Ω E}
    (hIID : @IsConditionallyIID Ω ℕ E mΩ inferInstance m X ν inferInstance)
    (hκ : IsRegularCondDistrib ν m (X 0) κ) :
    ∀ i {s : Set E}, MeasurableSet s →
      ν⟦X i ⁻¹' s | m⟧ =ᵐ[ν]
        fun ω ↦ (((⟨κ ω, inferInstance⟩ : ProbabilityMeasure E) : Measure E).real s) := by
  intro i s hs
  have hcoord_zero :
      (fun ω ↦ (κ ω).real s) =ᵐ[ν] ν⟦X 0 ⁻¹' s | m⟧ := by
    exact hκ.ae_eq_conditionalProbability hs
  have hcoord_i0 :
      ν⟦X i ⁻¹' s | m⟧ =ᵐ[ν] ν⟦X 0 ⁻¹' s | m⟧ :=
    hIID.2.2.2 i 0 s hs
  calc
    ν⟦X i ⁻¹' s | m⟧ =ᵐ[ν] ν⟦X 0 ⁻¹' s | m⟧ := hcoord_i0
    _ =ᵐ[ν] fun ω ↦ (κ ω).real s := hcoord_zero.symm
    _ =ᵐ[ν] fun ω ↦ (((⟨κ ω, inferInstance⟩ : ProbabilityMeasure E) : Measure E).real s) := by
      filter_upwards with ω
      rfl

/-- Helper for Theorem 12.26: at the original conditioning `σ`-algebra, finite products of the
coordinate conditional probabilities agree almost surely with the corresponding product of sampled
masses of the packaged regular conditional distribution. -/
private theorem finsetProd_condProb_ae_eq_prodSampledMass
    {ν : AmbientMeasure} [IsProbabilityMeasure ν] {m : MeasurableSpace Ω} {X : ℕ → Ω → E}
    {κ : Kernel[m, inferInstance] Ω E}
    (hIID : @IsConditionallyIID Ω ℕ E mΩ inferInstance m X ν inferInstance)
    (hκ : IsRegularCondDistrib ν m (X 0) κ) :
    ∀ (s : Finset ℕ) {t : ℕ → Set E}, (∀ i, i ∈ s → MeasurableSet (t i)) →
      (∏ i ∈ s, ν⟦X i ⁻¹' t i | m⟧) =ᵐ[ν]
        fun ω ↦
          ∏ i ∈ s,
            (((⟨κ ω, inferInstance⟩ : ProbabilityMeasure E) : Measure E).real (t i)) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro t ht
      -- Proof comment: the empty product is definitionally the constant `1` on both sides.
      exact Filter.EventuallyEq.of_eq (by funext ω; simp)
  | @insert i s hi hs_ih =>
      intro t ht
      have hcoord :
          ν⟦X i ⁻¹' t i | m⟧ =ᵐ[ν]
            fun ω ↦ (((⟨κ ω, inferInstance⟩ : ProbabilityMeasure E) : Measure E).real (t i)) := by
        -- Proof comment: the new factor is the single-coordinate bridge from the regular
        -- conditional distribution.
        exact
          @coordCondProb_ae_eq_sampledMass_at_m
            Ω mΩ E inferInstance inferInstance inferInstance ν inferInstance m X κ hIID hκ
            i (t i) (ht i (by simp))
      have hs_prod :
          (∏ j ∈ s, ν⟦X j ⁻¹' t j | m⟧) =ᵐ[ν]
            fun ω ↦
              ∏ j ∈ s,
                (((⟨κ ω, inferInstance⟩ : ProbabilityMeasure E) : Measure E).real (t j)) := by
        -- Proof comment: the induction hypothesis keeps the tail product in the same normal
        -- form, avoiding any measurable-space alias drift.
        exact hs_ih fun j hj ↦ ht j (by simp [hj])
      -- Proof comment: multiply the inserted coordinate bridge with the tail-product bridge.
      simpa [Finset.prod_insert hi] using hcoord.mul hs_prod

/-- Helper for Theorem 12.26: at the original conditioning `σ`-algebra, finite intersections of
coordinate events factor as products of the sampled masses of the packaged regular conditional
distribution. -/
private theorem finiteInterCondProb_ae_eq_prodSampledMass_at_m
    {ν : AmbientMeasure} [IsProbabilityMeasure ν] {m : MeasurableSpace Ω} {X : ℕ → Ω → E}
    {κ : Kernel[m, inferInstance] Ω E}
    (hIID : @IsConditionallyIID Ω ℕ E mΩ inferInstance m X ν inferInstance)
    (hκ : IsRegularCondDistrib ν m (X 0) κ) :
    ∀ (s : Finset ℕ) {t : ℕ → Set E}, (∀ i, i ∈ s → MeasurableSet (t i)) →
      ν⟦⋂ i ∈ s, X i ⁻¹' t i | m⟧ =ᵐ[ν]
        fun ω ↦
          ∏ i ∈ s,
            (((⟨κ ω, inferInstance⟩ : ProbabilityMeasure E) : Measure E).real (t i)) := by
  intro s t ht
  -- Route correction: the old route tried to perform the finite-intersection factorization and
  -- the product rewrite in the same induction. We now keep the factorization at `m` and compose
  -- it with the standalone product-side normalization.
  calc
    ν⟦⋂ i ∈ s, X i ⁻¹' t i | m⟧ =ᵐ[ν] ∏ i ∈ s, ν⟦X i ⁻¹' t i | m⟧ := by
      exact hIID.1.2.2.2 s (fun i hi ↦ ⟨t i, ht i hi, rfl⟩)
    _ =ᵐ[ν] fun ω ↦
          ∏ i ∈ s,
            (((⟨κ ω, inferInstance⟩ : ProbabilityMeasure E) : Measure E).real (t i)) := by
      exact
        @finsetProd_condProb_ae_eq_prodSampledMass
          Ω mΩ E inferInstance inferInstance inferInstance ν inferInstance m X κ hIID hκ
          s t ht

/-- Helper for Theorem 12.26: once the coordinate conditional probabilities already factor
through `xiInf`, the same coordinate formulas descend from `m` to `σ(xiInf)`. -/
private theorem coordCondProb_ae_eq_sampledMass_at_comap
    {ν : AmbientMeasure} [IsProbabilityMeasure ν] {m : MeasurableSpace Ω} {X : ℕ → Ω → E}
    {xiInf : Ω → ProbabilityMeasure E}
    (hIID : @IsConditionallyIID Ω ℕ E mΩ inferInstance m X ν inferInstance)
    (hxiInf_meas_m : @Measurable Ω (ProbabilityMeasure E) m inferInstance xiInf)
    (hcoord_m : ∀ i {s : Set E}, MeasurableSet s →
      ν⟦X i ⁻¹' s | m⟧ =ᵐ[ν] fun ω ↦ ((xiInf ω : Measure E).real s)) :
    ∀ i {s : Set E}, MeasurableSet s →
      ν⟦X i ⁻¹' s | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[ν]
        fun ω ↦ ((xiInf ω : Measure E).real s) := by
  intro i s hs
  have hm : m ≤ mΩ := hIID.1.2.1
  have hA_meas : MeasurableSet[mΩ] (X i ⁻¹' s) := (hIID.1.1 i) hs
  have hA_int : Integrable (Set.indicator (X i ⁻¹' s) fun _ ↦ (1 : ℝ)) ν := by
    -- Proof comment: the event indicator is integrable because the ambient measure is finite and
    -- the event is measurable.
    exact Integrable.indicator (integrable_const (μ := ν) (1 : ℝ)) hA_meas
  -- Proof comment: the `m`-measurable sampled-mass formula already identifies the conditional
  -- expectation at the larger conditioning algebra, so the local tower-property helper descends
  -- it unchanged to `σ(xiInf)`.
  simpa using
    @condExp_comap_eq_of_aeEq Ω mΩ ν inferInstance m
      (ProbabilityMeasure E) inferInstance xiInf
      (Set.indicator (X i ⁻¹' s) fun _ ↦ (1 : ℝ))
      (fun ω ↦ ((xiInf ω : Measure E).real s))
      hm hxiInf_meas_m (hcoord_m i hs)
      (sampledMass_stronglyMeasurable_comap (xiInf := xiInf) hs)

/-- Helper for Theorem 12.26: the finite product of coordinate conditional probabilities at
`σ(xiInf)` agrees almost surely with the product of the sampled masses. -/
private theorem finsetProd_condProb_ae_eq_prodSampledMass_at_comap
    {ν : AmbientMeasure} [IsProbabilityMeasure ν] {X : ℕ → Ω → E}
    {xiInf : Ω → ProbabilityMeasure E}
    (hcoord : ∀ i {s : Set E}, MeasurableSet s →
      ν⟦X i ⁻¹' s | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[ν]
        fun ω ↦ ((xiInf ω : Measure E).real s)) :
    ∀ (s : Finset ℕ) {t : ℕ → Set E}, (∀ i, i ∈ s → MeasurableSet (t i)) →
      (∏ i ∈ s, ν⟦X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧) =ᵐ[ν]
        fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i)) := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro t ht
      -- Proof comment: the empty product is definitionally the constant `1` on both sides.
      exact Filter.EventuallyEq.of_eq (by funext ω; simp)
  | @insert i s hi hs_ih =>
      intro t ht
      have hcoord_i :
          ν⟦X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[ν]
            fun ω ↦ ((xiInf ω : Measure E).real (t i)) := by
        -- Proof comment: the inserted coordinate uses the coordinate bridge hypothesis.
        exact hcoord i (ht i (by simp))
      have hs_prod :
          (∏ j ∈ s, ν⟦X j ⁻¹' t j | MeasurableSpace.comap xiInf inferInstance⟧) =ᵐ[ν]
            fun ω ↦ ∏ j ∈ s, ((xiInf ω : Measure E).real (t j)) := by
        -- Proof comment: the induction hypothesis keeps the tail product in the same normal
        -- form.
        exact hs_ih fun j hj ↦ ht j (by simp [hj])
      -- Proof comment: the product formula follows by multiplying the inserted factor with the
      -- tail product.
      simpa [Finset.prod_insert hi] using hcoord_i.mul hs_prod

/-- Helper for Theorem 12.26: once the finite-rectangle factorization already factors through
`xiInf` at `m`, it also factors through `σ(xiInf)`. -/
private theorem finiteInterCondProb_ae_eq_prodSampledMass_at_comap
    {ν : AmbientMeasure} [IsProbabilityMeasure ν] {m : MeasurableSpace Ω} {X : ℕ → Ω → E}
    {xiInf : Ω → ProbabilityMeasure E}
    (hIID : @IsConditionallyIID Ω ℕ E mΩ inferInstance m X ν inferInstance)
    (hxiInf_meas_m : @Measurable Ω (ProbabilityMeasure E) m inferInstance xiInf)
    (hfiniteInter_m : ∀ (s : Finset ℕ) {t : ℕ → Set E}, (∀ i, i ∈ s → MeasurableSet (t i)) →
      ν⟦⋂ i ∈ s, X i ⁻¹' t i | m⟧ =ᵐ[ν]
        fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i))) :
    ∀ (s : Finset ℕ) {t : ℕ → Set E}, (∀ i, i ∈ s → MeasurableSet (t i)) →
      ν⟦⋂ i ∈ s, X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[ν]
        fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i)) := by
  intro s t ht
  have hm : m ≤ mΩ := hIID.1.2.1
  have hInter_meas : MeasurableSet[mΩ] (⋂ i ∈ s, X i ⁻¹' t i) := by
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert i s hi hs_ih =>
        have hi_meas : MeasurableSet[mΩ] (X i ⁻¹' t i) := (hIID.1.1 i) (ht i (by simp))
        have hs_meas : MeasurableSet[mΩ] (⋂ j ∈ s, X j ⁻¹' t j) := by
          exact hs_ih (fun j hj ↦ ht j (by simp [hj]))
        -- Proof comment: finite intersections of the coordinate events stay ambient measurable,
        -- so the indicator remains integrable for the tower-property descent.
        simpa [Finset.set_biInter_insert, hi] using hi_meas.inter hs_meas
  have hInter_int :
      Integrable (Set.indicator (⋂ i ∈ s, X i ⁻¹' t i) fun _ ↦ (1 : ℝ)) ν := by
    -- Proof comment: the finite-intersection indicator is integrable because the ambient measure
    -- is finite and the event is measurable.
    exact Integrable.indicator (integrable_const (μ := ν) (1 : ℝ)) hInter_meas
  -- Proof comment: the finite-rectangle factorization at `m` is already measurable with respect
  -- to `σ(xiInf)`, so the same tower-property descent as in the coordinate case applies.
  simpa using
    @condExp_comap_eq_of_aeEq Ω mΩ ν inferInstance m
      (ProbabilityMeasure E) inferInstance xiInf
      (Set.indicator (⋂ i ∈ s, X i ⁻¹' t i) fun _ ↦ (1 : ℝ))
      (fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i)))
      hm hxiInf_meas_m (hfiniteInter_m s ht)
      (sampledMassProd_stronglyMeasurable_comap (xiInf := xiInf) s ht)

/-- Helper for Theorem 12.26: if `xiInf` is already measurable for `m`, then pushing forward the
`m`-trimmed measure along `xiInf` agrees with pushing forward the ambient measure. -/
private theorem map_trim_eq_map_of_measurable
    {ν : AmbientMeasure} [IsFiniteMeasure ν] {m : MeasurableSpace Ω}
    {xiInf : Ω → ProbabilityMeasure E} (hm : m ≤ mΩ)
    (hxiInf_meas_m : @Measurable Ω (ProbabilityMeasure E) m inferInstance xiInf) :
    (@Measure.map Ω (ProbabilityMeasure E) m inferInstance xiInf (ν.trim hm)) =
      @Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf ν := by
  -- Proof comment: the image only depends on the `m`-measurable preimages of measurable sets,
  -- so trimming to `m` does not change the pushforward.
  ext s hs
  rw [Measure.map_apply hxiInf_meas_m hs,
    Measure.map_apply (hxiInf_meas_m.mono hm le_rfl) hs,
    trim_measurableSet_eq hm (hxiInf_meas_m hs)]

/-- Helper for Theorem 12.26: if the conditional law of `X₀` given `m` is sampled by `xiInf`,
then the joint law of `(xiInf, X₀)` is the composition product with the canonical sampling
kernel. -/
private theorem pairLaw_eq_compProd_sampledProbabilityMeasureKernel
    {ν : AmbientMeasure} [IsProbabilityMeasure ν] {m : MeasurableSpace Ω} {X0 : Ω → E}
    {κ : Kernel[m, inferInstance] Ω E} (hκ : IsRegularCondDistrib ν m X0 κ) :
    (@Measure.map Ω (ProbabilityMeasure E × E) mΩ inferInstance
      (fun ω ↦ ((⟨κ ω, inferInstance⟩ : ProbabilityMeasure E), X0 ω)) ν) =
      (@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance
        (fun ω ↦ (⟨κ ω, inferInstance⟩ : ProbabilityMeasure E)) ν) ⊗ₘ
        sampledProbabilityMeasureKernel := by
  let xiInf : Ω → ProbabilityMeasure E := fun ω ↦ (⟨κ ω, inferInstance⟩ : ProbabilityMeasure E)
  have hm : m ≤ mΩ := hκ.le_ambient
  have hxiInf_meas_m :
      @Measurable Ω (ProbabilityMeasure E) m inferInstance xiInf := by
    -- Proof comment: the packaged regular conditional distribution is already measurable for `m`.
    simpa [xiInf] using
      (regularCondDistribProbabilityMeasureMeasurable
        (m := m) (κ := κ))
  have hxiInf_meas :
      @Measurable Ω (ProbabilityMeasure E) mΩ inferInstance xiInf :=
    hxiInf_meas_m.mono hm le_rfl
  -- Proof comment: compare both probability measures on measurable rectangles; the left-hand side
  -- is computed by conditioning the event `{X0 ∈ t}` on the `m`-measurable event `xiInf ⁻¹' s`,
  -- while the right-hand side is the definition of the composition product pushed forward by
  -- `xiInf`.
  rw [Measure.ext_prod_iff]
  intro s t hs ht
  have hreal :
      (@Measure.map Ω (ProbabilityMeasure E × E) mΩ inferInstance
        (fun ω ↦ (xiInf ω, X0 ω)) ν).real (s ×ˢ t) =
          ((@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf ν) ⊗ₘ
            sampledProbabilityMeasureKernel).real (s ×ˢ t) ↔
        @Measure.map Ω (ProbabilityMeasure E × E) mΩ inferInstance
            (fun ω ↦ (xiInf ω, X0 ω)) ν (s ×ˢ t) =
          ((@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf ν) ⊗ₘ
            sampledProbabilityMeasureKernel) (s ×ˢ t) :=
    measureReal_eq_measureReal_iff (measure_lt_top _ _).ne (measure_lt_top _ _).ne
  rw [← hreal]
  have hX0_meas : @Measurable Ω E mΩ inferInstance X0 := hκ.measurable_Y
  have hpre_meas_m : MeasurableSet[m] (xiInf ⁻¹' s) := hxiInf_meas_m hs
  have hX0_pre_meas : MeasurableSet[mΩ] (X0 ⁻¹' t) := hX0_meas ht
  have hindicator_int :
      Integrable (Set.indicator (X0 ⁻¹' t) (fun _ ↦ (1 : ℝ))) ν := by
    -- Proof comment: the event indicator is integrable because `ν` is finite and the event is
    -- measurable.
    exact Integrable.indicator (integrable_const (μ := ν) (1 : ℝ)) hX0_pre_meas
  have hleft :
      (@Measure.map Ω (ProbabilityMeasure E × E) mΩ inferInstance
        (fun ω ↦ (xiInf ω, X0 ω)) ν).real (s ×ˢ t) =
        ∫ ω in xiInf ⁻¹' s, (κ ω).real t ∂ν := by
    calc
      (@Measure.map Ω (ProbabilityMeasure E × E) mΩ inferInstance
          (fun ω ↦ (xiInf ω, X0 ω)) ν).real (s ×ˢ t)
          = ν.real ((xiInf ⁻¹' s) ∩ (X0 ⁻¹' t)) := by
              simpa [Measure.real_def, Set.preimage, Set.mk_preimage_prod] using
                congrArg ENNReal.toReal
                  (Measure.map_apply (hxiInf_meas.prodMk hX0_meas) (hs.prod ht))
      _ = ∫ ω in (xiInf ⁻¹' s) ∩ (X0 ⁻¹' t), (1 : ℝ) ∂ν := by
            rw [setIntegral_const, smul_eq_mul, mul_one]
      _ = ∫ ω in xiInf ⁻¹' s, Set.indicator (X0 ⁻¹' t) (fun _ ↦ (1 : ℝ)) ω ∂ν := by
            simpa [Set.inter_comm] using
              (setIntegral_indicator (s := xiInf ⁻¹' s) (t := X0 ⁻¹' t)
                (f := fun _ ↦ (1 : ℝ)) hX0_pre_meas).symm
      _ = ∫ ω in xiInf ⁻¹' s, (ν⟦X0 ⁻¹' t | m⟧) ω ∂ν := by
            rw [setIntegral_condExp hm hindicator_int hpre_meas_m]
      _ = ∫ ω in xiInf ⁻¹' s, (κ ω).real t ∂ν := by
            exact integral_congr_ae (ae_restrict_of_ae (hκ.ae_eq_conditionalProbability ht).symm)
  have hmass_aestrong :
      AEStronglyMeasurable
        (fun ξ : ProbabilityMeasure E ↦ ((sampledProbabilityMeasureKernel (E := E)) ξ).real t)
        (@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf ν) := by
    -- Proof comment: evaluation at the measurable set `t` is strongly measurable on the space of
    -- probability measures.
    have hmeas :
        Measurable (fun ξ : ProbabilityMeasure E ↦ (ξ : Measure E).real t) :=
      (MeasureTheory.Measure.measurable_coe ht).ennreal_toReal.comp measurable_subtype_coe
    simpa [sampledProbabilityMeasureKernel] using
      (hmeas.aestronglyMeasurable :
        AEStronglyMeasurable (fun ξ : ProbabilityMeasure E ↦ (ξ : Measure E).real t)
          (@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf ν))
  have hright :
      (((@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf ν) ⊗ₘ
          sampledProbabilityMeasureKernel).real (s ×ˢ t)) =
        ∫ ω in xiInf ⁻¹' s, (κ ω).real t ∂ν := by
    calc
      (((@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf ν) ⊗ₘ
          sampledProbabilityMeasureKernel).real (s ×ˢ t))
          = ∫ ξ in s, ((sampledProbabilityMeasureKernel (E := E)) ξ).real t ∂
              (@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf ν) := by
              rw [measureReal_def, Measure.compProd_apply_prod hs ht,
                ← integral_toReal
                  (((sampledProbabilityMeasureKernel (E := E)).measurable_coe ht).aemeasurable)]
              · rfl
              · exact Filter.Eventually.of_forall fun ξ ↦ measure_lt_top _ _
      _ = ∫ ω in xiInf ⁻¹' s,
            ((sampledProbabilityMeasureKernel (E := E)) (xiInf ω)).real t ∂ν := by
            exact setIntegral_map hs hmass_aestrong hxiInf_meas.aemeasurable
      _ = ∫ ω in xiInf ⁻¹' s, (κ ω).real t ∂ν := by
            simp [sampledProbabilityMeasureKernel, xiInf]
  exact hleft.trans hright.symm

/-- Helper for Theorem 12.26: once the pair law of `(xiInf, X₀)` is the canonical composition
product, the conditional distribution of `X₀` given `xiInf` is almost surely the sampled measure
itself. -/
private theorem condDistrib_ae_eq_sampledMeasure_of_pairLaw
    {ν : AmbientMeasure} [IsProbabilityMeasure ν] {X0 : Ω → E}
    {xiInf : Ω → ProbabilityMeasure E}
    (hxiInf_meas : Measurable xiInf)
    (hX0_meas : Measurable X0)
    (hpair :
      ν.map (fun ω ↦ (xiInf ω, X0 ω)) = ν.map xiInf ⊗ₘ sampledProbabilityMeasureKernel) :
    ∀ᵐ ξ ∂ν.map xiInf, condDistrib X0 xiInf ν ξ = (ξ : Measure E) := by
  have hcond :
      condDistrib X0 xiInf ν =ᵐ[ν.map xiInf] sampledProbabilityMeasureKernel := by
    -- Proof comment: the pair law is exactly the uniqueness characterization of `condDistrib`.
    simpa using
      (condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
        (μ := ν) (X := xiInf) (Y := X0) hxiInf_meas hX0_meas hpair)
  -- Proof comment: the canonical sampling kernel evaluates to the underlying probability measure
  -- by definition.
  filter_upwards [hcond] with ξ hξ
  rw [hξ]
  rfl

-- Proof sketch: for the forward implication, condition on the
-- exchangeable `σ`-algebra, then realize the common conditional law of the coordinates as the
-- `ProbabilityMeasure E`-valued random variable induced by the regular conditional distribution of
-- `X 0`. For the reverse implication, conditional i.i.d. given the directing random measure
-- implies permutation-invariance of every finite-dimensional conditional law, hence exchangeability
-- after integrating out the directing measure.
/-- Theorem 12.26: an exchangeable `E`-valued sequence is exactly a sequence admitting an
exchangeable-`σ`-algebra-measurable directing random probability measure `Ξ∞` such that,
conditional on `Ξ∞`, the sequence is i.i.d. and the conditional law of `X₀` is `Ξ∞`. The
explicit coordinate measurability hypothesis matches the source-facing exchangeability owner with
the measurable owner theorem from `Theorem_12_24`. -/
theorem isExchangeable_iff_exists_directingProbabilityMeasure
    {X : ℕ → Ω → E} (hX_meas : ∀ n, Measurable (X n)) :
    IsExchangeable X μ ↔
      ∃ xiInf : Ω → ProbabilityMeasure E,
        Measurable[exchangeableSigmaAlgebra (Function.swap X)] xiInf ∧
          IsDirectingProbabilityMeasure xiInf X μ := by
  constructor
  · intro hX
    -- Route correction: first use Theorem 12.24 to condition on the canonical exchangeable
    -- `σ`-algebra, then invoke the concrete regular-conditional-distribution bridge above.
    have hIID :
        @IsConditionallyIID Ω ℕ E mΩ inferInstance
          (exchangeableSigmaAlgebra (Function.swap X)) X μ inferInstance := by
      exact (isExchangeable_iff_conditionallyIID_given_exchangeableSigmaAlgebra hX_meas).mp hX
    have hm : exchangeableSigmaAlgebra (Function.swap X) ≤ mΩ := hIID.1.2.1
    obtain ⟨κ, hκ⟩ :
        ∃ κ : Kernel[exchangeableSigmaAlgebra (Function.swap X), inferInstance] Ω E,
          IsRegularCondDistrib μ (exchangeableSigmaAlgebra (Function.swap X)) (X 0) κ :=
      @exists_regular_conditional_distribution_borel_given Ω mΩ E inferInstance inferInstance
        μ inferInstance (exchangeableSigmaAlgebra (Function.swap X)) hm (X 0) (hIID.1.1 0)
    let xiInf : Ω → ProbabilityMeasure E := fun ω ↦ (⟨κ ω, inferInstance⟩ : ProbabilityMeasure E)
    have hxiInf_meas_m :
        @Measurable Ω (ProbabilityMeasure E)
          (exchangeableSigmaAlgebra (Function.swap X)) inferInstance xiInf := by
      -- Proof comment: the directing random measure is the packaged regular conditional
      -- distribution of the first coordinate.
      simpa [xiInf] using
        (regularCondDistribProbabilityMeasureMeasurable
          (m := exchangeableSigmaAlgebra (Function.swap X)) (κ := κ))
    have hxiInf_meas :
        @Measurable Ω (ProbabilityMeasure E) mΩ inferInstance xiInf :=
      hxiInf_meas_m.mono hm le_rfl
    have hcoord_m :
        ∀ i {s : Set E}, MeasurableSet s →
          μ⟦X i ⁻¹' s | exchangeableSigmaAlgebra (Function.swap X)⟧ =ᵐ[μ]
            fun ω ↦ ((xiInf ω : Measure E).real s) := by
      intro i s hs
      simpa [xiInf] using
        (@coordCondProb_ae_eq_sampledMass_at_m Ω mΩ E inferInstance inferInstance inferInstance
          μ inferInstance (exchangeableSigmaAlgebra (Function.swap X)) X κ hIID hκ i s hs)
    have hfiniteInter_m :
        ∀ (s : Finset ℕ) {t : ℕ → Set E}, (∀ i, i ∈ s → MeasurableSet (t i)) →
          μ⟦⋂ i ∈ s, X i ⁻¹' t i | exchangeableSigmaAlgebra (Function.swap X)⟧ =ᵐ[μ]
            fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i)) := by
      intro s t ht
      simpa [xiInf] using
        (@finiteInterCondProb_ae_eq_prodSampledMass_at_m
          Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance
          (exchangeableSigmaAlgebra (Function.swap X)) X κ hIID hκ
          s t ht)
    have hcoord_comap :
        ∀ i {s : Set E}, MeasurableSet s →
          μ⟦X i ⁻¹' s | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[μ]
            fun ω ↦ ((xiInf ω : Measure E).real s) := by
      intro i s hs
      exact
        @coordCondProb_ae_eq_sampledMass_at_comap
          Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance
          (exchangeableSigmaAlgebra (Function.swap X)) X xiInf
          hIID hxiInf_meas_m hcoord_m i s hs
    have hfiniteInter_comap :
        ∀ (s : Finset ℕ) {t : ℕ → Set E}, (∀ i, i ∈ s → MeasurableSet (t i)) →
          μ⟦⋂ i ∈ s, X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[μ]
            fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i)) := by
      intro s t ht
      exact
        @finiteInterCondProb_ae_eq_prodSampledMass_at_comap
          Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance
          (exchangeableSigmaAlgebra (Function.swap X)) X xiInf
          hIID hxiInf_meas_m hfiniteInter_m s t ht
    have hprod_comap :
        ∀ (s : Finset ℕ) {t : ℕ → Set E}, (∀ i, i ∈ s → MeasurableSet (t i)) →
          (∏ i ∈ s, μ⟦X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧) =ᵐ[μ]
            fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i)) := by
      intro s t ht
      exact
        @finsetProd_condProb_ae_eq_prodSampledMass_at_comap
          Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance X xiInf
          hcoord_comap s t ht
    have hIndependent_comap :
        @IsConditionallyIndependentFun Ω ℕ E mΩ inferInstance
          (MeasurableSpace.comap xiInf inferInstance) X μ inferInstance := by
      refine ⟨hIID.1.1, ?_⟩
      refine ⟨hxiInf_meas.comap_le, fun i ↦ (hIID.1.1 i).comap_le, ?_⟩
      intro s A hA
      classical
      let t : ℕ → Set E := fun i ↦
        if hi : i ∈ s then Classical.choose (MeasurableSpace.measurableSet_comap.mp (hA i hi))
        else ∅
      have ht :
          ∀ i, i ∈ s → MeasurableSet (t i) := by
        intro i hi
        have hAi : MeasurableSet[MeasurableSpace.comap (X i) inferInstance] (A i) := hA i hi
        simpa [t, hi] using
          (Classical.choose_spec (MeasurableSpace.measurableSet_comap.mp hAi)).1
      have hA_repr :
          ∀ i, i ∈ s → X i ⁻¹' t i = A i := by
        intro i hi
        have hAi : MeasurableSet[MeasurableSpace.comap (X i) inferInstance] (A i) := hA i hi
        simpa [t, hi] using
          (Classical.choose_spec (MeasurableSpace.measurableSet_comap.mp hAi)).2
      have hInter_eq :
          (⋂ i ∈ s, A i) = ⋂ i ∈ s, X i ⁻¹' t i := by
        ext ω
        simp only [Set.mem_iInter, Set.mem_preimage]
        constructor
        · intro h i hi
          have hAi : ω ∈ A i := h i hi
          rwa [← hA_repr i hi] at hAi
        · intro h i hi
          have hAi : ω ∈ X i ⁻¹' t i := h i hi
          rwa [hA_repr i hi] at hAi
      have hCondSet_eq :
          ∀ i, i ∈ s →
            μ⟦A i | MeasurableSpace.comap xiInf inferInstance⟧ =
              μ⟦X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ := by
        intro i hi
        rw [← hA_repr i hi]
      have hProd_eq :
          (∏ i ∈ s, μ⟦A i | MeasurableSpace.comap xiInf inferInstance⟧) =
            ∏ i ∈ s, μ⟦X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        exact hCondSet_eq i hi
      -- Proof comment: convert the general comap-measurable events to preimages in `E`, apply
      -- the sampled-mass factorization there, and rewrite back.
      calc
        μ⟦⋂ i ∈ s, A i | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[μ]
            μ⟦⋂ i ∈ s, X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ := by
              exact Filter.EventuallyEq.of_eq (by rw [hInter_eq])
        _ =ᵐ[μ] fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i)) :=
          hfiniteInter_comap s ht
        _ =ᵐ[μ] ∏ i ∈ s, μ⟦X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ := by
          exact (hprod_comap s ht).symm
        _ =ᵐ[μ] ∏ i ∈ s, μ⟦A i | MeasurableSpace.comap xiInf inferInstance⟧ :=
          Filter.EventuallyEq.of_eq hProd_eq.symm
    have hIdentDistrib_comap :
        @IsConditionallyIdentDistrib Ω ℕ E mΩ inferInstance
          (MeasurableSpace.comap xiInf inferInstance) X μ inferInstance := by
      refine ⟨hxiInf_meas.comap_le, hIID.1.1, ?_⟩
      intro i j s hs
      -- Proof comment: every coordinate conditional law on `σ(xiInf)` agrees with the same
      -- sampled mass of `xiInf`.
      filter_upwards [hcoord_comap i hs, hcoord_comap j hs] with ω hi hj
      exact hi.trans hj.symm
    have hIID_comap :
        @IsConditionallyIID Ω ℕ E mΩ inferInstance
          (MeasurableSpace.comap xiInf inferInstance) X μ inferInstance := by
      exact ⟨hIndependent_comap, hIdentDistrib_comap⟩
    have hpair :
        @Measure.map Ω (ProbabilityMeasure E × E) mΩ inferInstance
            (fun ω ↦ (xiInf ω, X 0 ω)) μ =
          (@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf μ) ⊗ₘ
            sampledProbabilityMeasureKernel := by
      simpa [xiInf] using
        (@pairLaw_eq_compProd_sampledProbabilityMeasureKernel
          Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance
          (exchangeableSigmaAlgebra (Function.swap X)) (X 0) κ hκ)
    have hcond :
        ∀ᵐ ξ ∂@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf μ,
          condDistrib (X 0) xiInf μ ξ = (ξ : Measure E) := by
      -- Proof comment: the pair law of `(xiInf, X₀)` identifies the conditional law of the first
      -- coordinate as the sampled directing measure.
      exact
        @condDistrib_ae_eq_sampledMeasure_of_pairLaw
          Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance (X 0) xiInf
          hxiInf_meas (hIID.1.1 0) hpair
    exact ⟨xiInf, hxiInf_meas_m, ⟨hIID_comap, hcond⟩⟩
  · rintro ⟨xiInf, _, hxiInf⟩
    -- Proof comment: the reverse implication is formal once the directing-law predicate exposes
    -- the underlying conditional i.i.d. structure.
    exact isExchangeable_of_directingProbabilityMeasure hxiInf

-- Proof sketch: start from the exchangeable-`σ`-algebra directing random measure in
-- `isExchangeable_iff_exists_directingProbabilityMeasure`, then replace the conditioning
-- `σ`-algebra by `tailRandomVariableMeasurableSpace X`; the same
-- regular conditional law of `X 0` then serves as the tail-measurable directing measure.
/-- A directing random probability measure in de Finetti's theorem may also be chosen measurable
with respect to the tail `σ`-algebra of the sequence. -/
theorem exists_directingProbabilityMeasure_measurable_tailSigmaAlgebra
    {X : ℕ → Ω → E} (hX_meas : ∀ n, Measurable (X n)) (hX : IsExchangeable X μ) :
    ∃ xiInf : Ω → ProbabilityMeasure E,
      Measurable[tailRandomVariableMeasurableSpace X] xiInf ∧
        IsDirectingProbabilityMeasure xiInf X μ := by
  have hIID :
      @IsConditionallyIID Ω ℕ E mΩ inferInstance
        (tailRandomVariableMeasurableSpace X) X μ inferInstance := by
    exact (isExchangeable_iff_conditionallyIID_given_tailSigmaAlgebra hX_meas).mp hX
  have hm : tailRandomVariableMeasurableSpace X ≤ mΩ := hIID.1.2.1
  obtain ⟨κ, hκ⟩ :
      ∃ κ : Kernel[tailRandomVariableMeasurableSpace X, inferInstance] Ω E,
        IsRegularCondDistrib μ (tailRandomVariableMeasurableSpace X) (X 0) κ :=
    @exists_regular_conditional_distribution_borel_given Ω mΩ E inferInstance inferInstance
      μ inferInstance (tailRandomVariableMeasurableSpace X) hm (X 0) (hIID.1.1 0)
  let xiInf : Ω → ProbabilityMeasure E := fun ω ↦ (⟨κ ω, inferInstance⟩ : ProbabilityMeasure E)
  have hxiInf_meas_m :
      @Measurable Ω (ProbabilityMeasure E)
        (tailRandomVariableMeasurableSpace X) inferInstance xiInf := by
    -- Proof comment: the directing random measure is the packaged regular conditional
    -- distribution of the first coordinate.
    simpa [xiInf] using
      (regularCondDistribProbabilityMeasureMeasurable
        (m := tailRandomVariableMeasurableSpace X) (κ := κ))
  have hxiInf_meas :
      @Measurable Ω (ProbabilityMeasure E) mΩ inferInstance xiInf :=
    hxiInf_meas_m.mono hm le_rfl
  have hcoord_m :
      ∀ i {s : Set E}, MeasurableSet s →
        μ⟦X i ⁻¹' s | tailRandomVariableMeasurableSpace X⟧ =ᵐ[μ]
          fun ω ↦ ((xiInf ω : Measure E).real s) := by
    intro i s hs
    simpa [xiInf] using
      (@coordCondProb_ae_eq_sampledMass_at_m Ω mΩ E inferInstance inferInstance inferInstance
        μ inferInstance (tailRandomVariableMeasurableSpace X) X κ hIID hκ i s hs)
  have hfiniteInter_m :
      ∀ (s : Finset ℕ) {t : ℕ → Set E}, (∀ i, i ∈ s → MeasurableSet (t i)) →
        μ⟦⋂ i ∈ s, X i ⁻¹' t i | tailRandomVariableMeasurableSpace X⟧ =ᵐ[μ]
          fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i)) := by
    intro s t ht
    simpa [xiInf] using
      (@finiteInterCondProb_ae_eq_prodSampledMass_at_m
        Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance
        (tailRandomVariableMeasurableSpace X) X κ hIID hκ
        s t ht)
  have hcoord_comap :
      ∀ i {s : Set E}, MeasurableSet s →
        μ⟦X i ⁻¹' s | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[μ]
          fun ω ↦ ((xiInf ω : Measure E).real s) := by
    intro i s hs
    exact
      @coordCondProb_ae_eq_sampledMass_at_comap
        Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance
        (tailRandomVariableMeasurableSpace X) X xiInf
        hIID hxiInf_meas_m hcoord_m i s hs
  have hfiniteInter_comap :
      ∀ (s : Finset ℕ) {t : ℕ → Set E}, (∀ i, i ∈ s → MeasurableSet (t i)) →
        μ⟦⋂ i ∈ s, X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[μ]
          fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i)) := by
    intro s t ht
    exact
      @finiteInterCondProb_ae_eq_prodSampledMass_at_comap
        Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance
        (tailRandomVariableMeasurableSpace X) X xiInf
        hIID hxiInf_meas_m hfiniteInter_m s t ht
  have hprod_comap :
      ∀ (s : Finset ℕ) {t : ℕ → Set E}, (∀ i, i ∈ s → MeasurableSet (t i)) →
        (∏ i ∈ s, μ⟦X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧) =ᵐ[μ]
          fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i)) := by
    intro s t ht
    exact
      @finsetProd_condProb_ae_eq_prodSampledMass_at_comap
        Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance X xiInf
        hcoord_comap s t ht
  have hIndependent_comap :
      @IsConditionallyIndependentFun Ω ℕ E mΩ inferInstance
        (MeasurableSpace.comap xiInf inferInstance) X μ inferInstance := by
    refine ⟨hIID.1.1, ?_⟩
    refine ⟨hxiInf_meas.comap_le, fun i ↦ (hIID.1.1 i).comap_le, ?_⟩
    intro s A hA
    classical
    let t : ℕ → Set E := fun i ↦
      if hi : i ∈ s then Classical.choose (MeasurableSpace.measurableSet_comap.mp (hA i hi))
      else ∅
    have ht :
        ∀ i, i ∈ s → MeasurableSet (t i) := by
      intro i hi
      have hAi : MeasurableSet[MeasurableSpace.comap (X i) inferInstance] (A i) := hA i hi
      simpa [t, hi] using
        (Classical.choose_spec (MeasurableSpace.measurableSet_comap.mp hAi)).1
    have hA_repr :
        ∀ i, i ∈ s → X i ⁻¹' t i = A i := by
      intro i hi
      have hAi : MeasurableSet[MeasurableSpace.comap (X i) inferInstance] (A i) := hA i hi
      simpa [t, hi] using
        (Classical.choose_spec (MeasurableSpace.measurableSet_comap.mp hAi)).2
    have hInter_eq :
        (⋂ i ∈ s, A i) = ⋂ i ∈ s, X i ⁻¹' t i := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_preimage]
      constructor
      · intro h i hi
        have hAi : ω ∈ A i := h i hi
        rwa [← hA_repr i hi] at hAi
      · intro h i hi
        have hAi : ω ∈ X i ⁻¹' t i := h i hi
        rwa [hA_repr i hi] at hAi
    have hCondSet_eq :
        ∀ i, i ∈ s →
          μ⟦A i | MeasurableSpace.comap xiInf inferInstance⟧ =
            μ⟦X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ := by
      intro i hi
      rw [← hA_repr i hi]
    have hProd_eq :
        (∏ i ∈ s, μ⟦A i | MeasurableSpace.comap xiInf inferInstance⟧) =
          ∏ i ∈ s, μ⟦X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      exact hCondSet_eq i hi
    -- Proof comment: convert the general comap-measurable events to preimages in `E`, apply
    -- the sampled-mass factorization there, and rewrite back.
    calc
      μ⟦⋂ i ∈ s, A i | MeasurableSpace.comap xiInf inferInstance⟧ =ᵐ[μ]
          μ⟦⋂ i ∈ s, X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ := by
            exact Filter.EventuallyEq.of_eq (by rw [hInter_eq])
      _ =ᵐ[μ] fun ω ↦ ∏ i ∈ s, ((xiInf ω : Measure E).real (t i)) :=
        hfiniteInter_comap s ht
      _ =ᵐ[μ] ∏ i ∈ s, μ⟦X i ⁻¹' t i | MeasurableSpace.comap xiInf inferInstance⟧ := by
        exact (hprod_comap s ht).symm
      _ =ᵐ[μ] ∏ i ∈ s, μ⟦A i | MeasurableSpace.comap xiInf inferInstance⟧ :=
        Filter.EventuallyEq.of_eq hProd_eq.symm
  have hIdentDistrib_comap :
      @IsConditionallyIdentDistrib Ω ℕ E mΩ inferInstance
        (MeasurableSpace.comap xiInf inferInstance) X μ inferInstance := by
    refine ⟨hxiInf_meas.comap_le, hIID.1.1, ?_⟩
    intro i j s hs
    -- Proof comment: every coordinate conditional law on `σ(xiInf)` agrees with the same sampled
    -- mass of `xiInf`.
    filter_upwards [hcoord_comap i hs, hcoord_comap j hs] with ω hi hj
    exact hi.trans hj.symm
  have hIID_comap :
      @IsConditionallyIID Ω ℕ E mΩ inferInstance
        (MeasurableSpace.comap xiInf inferInstance) X μ inferInstance := by
    exact ⟨hIndependent_comap, hIdentDistrib_comap⟩
  have hpair :
      @Measure.map Ω (ProbabilityMeasure E × E) mΩ inferInstance
          (fun ω ↦ (xiInf ω, X 0 ω)) μ =
        (@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf μ) ⊗ₘ
          sampledProbabilityMeasureKernel := by
    simpa [xiInf] using
      (@pairLaw_eq_compProd_sampledProbabilityMeasureKernel
        Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance
        (tailRandomVariableMeasurableSpace X) (X 0) κ hκ)
  have hcond :
      ∀ᵐ ξ ∂@Measure.map Ω (ProbabilityMeasure E) mΩ inferInstance xiInf μ,
        condDistrib (X 0) xiInf μ ξ = (ξ : Measure E) := by
    -- Proof comment: the pair law of `(xiInf, X₀)` identifies the conditional law of the first
    -- coordinate as the sampled directing measure.
    exact
      @condDistrib_ae_eq_sampledMeasure_of_pairLaw
        Ω mΩ E inferInstance inferInstance inferInstance μ inferInstance (X 0) xiInf
        hxiInf_meas (hIID.1.1 0) hpair
  exact ⟨xiInf, hxiInf_meas_m, ⟨hIID_comap, hcond⟩⟩
