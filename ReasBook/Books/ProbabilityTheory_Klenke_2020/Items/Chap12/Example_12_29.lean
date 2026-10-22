/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Example_12_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_1_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory unitInterval
open scoped BigOperators ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

noncomputable section

section

omit [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Helper for Example 12.29: the event that the first `n` Bernoulli draws are black is the finite
intersection of the corresponding singleton fibers. -/
private theorem blackPrefixEvent_eq_biInter
    {n : ℕ} {X : Fin n → Ω → Bool} :
    {ω | ∀ i : Fin n, X i ω = true} =
      ⋂ i ∈ Finset.univ, X i ⁻¹' ({true} : Set Bool) := by
  -- Proof comment: membership in the all-black event is exactly the pointwise singleton-fiber
  -- condition for every coordinate in the finite prefix.
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_univ, forall_true_left,
    Set.mem_preimage, Set.mem_singleton_iff]

end

/-- Helper for Example 12.29: the real singleton mass of a Bernoulli law on `Bool` is the expected
`y`/`1-y` formula for `unitInterval` parameters. -/
private theorem bernoulliMeasureReal_singleton_unitInterval (y : unitInterval) (b : Bool) :
    ((PMF.bernoulli (toNNReal y) (by simpa using y.2.2)).toMeasure).real ({b} : Set Bool) =
      if b then (y : ℝ) else 1 - (y : ℝ) := by
  have hy : unitInterval.toNNReal y ≤ 1 := by
    simpa [unitInterval.toNNReal] using y.2.2
  -- Proof comment: on `Bool`, the Bernoulli mass is an explicit two-point computation.
  cases b
  · simp [Measure.real_def, hy]
  · simp [Measure.real_def]

section

omit [StandardBorelSpace Ω]

/-- Helper for Example 12.29: the singleton conditional probability of one Bernoulli coordinate is
the Bernoulli mass determined by the directing parameter `Z`. -/
private theorem condProbBoolSingleton_eq_bernoulliMass_ae
    {μ : Measure Ω} [IsProbabilityMeasure μ] {Z : Ω → unitInterval} {X : ℕ → Ω → Bool}
    (hX : IsConditionallyBernoulliIID Z X μ) (i : ℕ) (b : Bool) :
    μ⟦X i ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧ =ᵐ[μ]
      fun ω ↦ if b then (Z ω : ℝ) else 1 - (Z ω : ℝ) := by
  have hcond :
      μ⟦X i ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧ =ᵐ[μ]
        fun ω ↦ (condDistrib (X i) Z μ (Z ω)).real ({b} : Set Bool) := by
    -- Proof comment: rewrite the conditional probability through the regular conditional
    -- distribution of the coordinate `X i` given `Z`.
    simpa using
      (condDistrib_ae_eq_condExp (μ := μ) (X := Z) (Y := X i)
        hX.measurable ((IsConditionallyBernoulliIID.isConditionallyIID hX).1.1 i)
        (measurableSet_singleton b)).symm
  have hbernoulli_map :
      ∀ᵐ y ∂μ.map Z,
        (condDistrib (X i) Z μ y).real ({b} : Set Bool) =
          if b then (y : ℝ) else 1 - (y : ℝ) := by
    filter_upwards [hX.condDistrib_ae_eq_bernoulli i] with y hy
    -- Proof comment: once the conditional law is Bernoulli, singleton masses are an explicit
    -- two-point computation.
    rw [hy]
    simpa using bernoulliMeasureReal_singleton_unitInterval y b
  have hbernoulli :
      (fun ω ↦ (condDistrib (X i) Z μ (Z ω)).real ({b} : Set Bool)) =ᵐ[μ]
        fun ω ↦ if b then (Z ω : ℝ) else 1 - (Z ω : ℝ) := by
    -- Proof comment: pull the Bernoulli singleton-mass identity back along the parameter map `Z`.
    exact MeasureTheory.ae_of_ae_map hX.measurable.aemeasurable hbernoulli_map
  exact hcond.trans hbernoulli

end

section

omit [StandardBorelSpace Ω]

/-- Helper for Example 12.29: conditioned on the directing parameter `Z`, the probability that the
first `n` draws are all black is `(Z ω)^n`. -/
private theorem blackPrefixCondProb_eq_pow_ae
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Bool} {Z : Ω → unitInterval}
    (hX : IsConditionallyBernoulliIID Z X μ) (n : ℕ) :
    μ⟦{ω | ∀ i : Fin n, X i ω = true} | MeasurableSpace.comap Z inferInstance⟧ =ᵐ[μ]
      fun ω ↦ (Z ω : ℝ) ^ n := by
  let hIID : IsConditionallyIID (MeasurableSpace.comap Z inferInstance) X μ :=
    hX.isConditionallyIID
  have hfactor :
      μ⟦{ω | ∀ i : Fin n, X i ω = true} | MeasurableSpace.comap Z inferInstance⟧ =ᵐ[μ]
        ∏ i ∈ Finset.range n,
          μ⟦X i ⁻¹' ({true} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧ := by
    -- Proof comment: conditional independence of the first `n` coordinates factors the all-black
    -- event into the product of the coordinate conditional probabilities.
    have hset :
        {ω | ∀ i : Fin n, X i ω = true} =
          ⋂ i ∈ Finset.range n, X i ⁻¹' ({true} : Set Bool) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range, Set.mem_preimage,
        Set.mem_singleton_iff]
      constructor
      · intro hω i hi
        exact hω ⟨i, hi⟩
      · intro hω i
        exact hω i i.is_lt
    rw [hset]
    simpa using
      hIID.1.2.2.2 (Finset.range n)
        (fun i _ ↦ ⟨({true} : Set Bool), measurableSet_singleton true, rfl⟩)
  have hcoords :
      ∀ᵐ ω ∂μ, ∀ i : ℕ,
        (μ⟦X i ⁻¹' ({true} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧) ω =
          (Z ω : ℝ) := by
    exact ae_all_iff.2 fun i ↦ by
      simpa using condProbBoolSingleton_eq_bernoulliMass_ae hX i true
  have hprod :
      (∏ i ∈ Finset.range n,
          μ⟦X i ⁻¹' ({true} : Set Bool) | MeasurableSpace.comap Z inferInstance⟧) =ᵐ[μ]
        fun ω ↦ (Z ω : ℝ) ^ n := by
    filter_upwards [hcoords] with ω hω
    -- Proof comment: once each factor equals `Z ω`, the finite product is the `n`th power.
    simp [hω]
  exact hfactor.trans hprod

end

/-- Helper for Example 12.29: every Beta law with natural parameters is almost surely supported on
`Set.Icc (0 : ℝ) 1`. -/
private theorem ae_mem_Icc_id_betaMeasure_natParams {a b : ℕ} :
    ∀ᵐ x ∂ betaMeasure a b, x ∈ Set.Icc (0 : ℝ) 1 := by
  rw [betaMeasure, ae_withDensity_iff (by
    simpa [betaPDF] using ENNReal.measurable_ofReal.comp (measurable_betaPDFReal (a : ℝ) b))]
  filter_upwards with x hx
  -- Proof comment: outside `[0,1]`, the Beta density vanishes, so any point with nonzero density
  -- must lie in the support interval.
  have hx_nonneg : 0 ≤ x := by
    by_contra hx_neg
    exact hx (betaPDF_eq_zero_of_nonpos (le_of_not_ge hx_neg))
  have hx_le_one : x ≤ 1 := by
    by_contra hx_gt
    exact hx (betaPDF_eq_zero_of_one_le (le_of_lt (not_le.mp hx_gt)))
  exact ⟨hx_nonneg, hx_le_one⟩

/-- Helper for Example 12.29: every absolute power is integrable under the Beta law with natural
parameters `(M, N - M)` when `0 < M < N`. -/
private theorem integrableAbsPow_id_betaMeasure_natParams
    {M N : ℕ} (hM : 0 < M) (hMN : M < N) :
    ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) (betaMeasure M (N - M : ℕ)) := by
  have hM_real : 0 < (M : ℝ) := by
    exact_mod_cast hM
  have hNM_real : 0 < ((N - M : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hMN
  letI : IsProbabilityMeasure (betaMeasure M (N - M : ℕ)) := isProbabilityMeasureBeta
    hM_real hNM_real
  intro n
  have hsupport : ∀ᵐ x ∂betaMeasure M (N - M : ℕ), x ∈ Set.Icc (0 : ℝ) 1 :=
    ae_mem_Icc_id_betaMeasure_natParams
  refine Integrable.of_bound
    ((by fun_prop : Measurable fun x : ℝ ↦ |x| ^ n).aestronglyMeasurable) 1 ?_
  filter_upwards [hsupport] with x hx
  rcases hx with ⟨hx_nonneg, hx_le_one⟩
  have hx_abs_le : |x| ≤ 1 := by
    simpa [abs_of_nonneg hx_nonneg] using hx_le_one
  have hx_pow_le : |x| ^ n ≤ 1 := by
    simpa using pow_le_pow_left₀ (abs_nonneg x) hx_abs_le n
  -- Proof comment: on the almost-sure support `[0,1]`, every absolute power is bounded by `1`.
  simpa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg x) n)] using hx_pow_le


-- Proof sketch: condition on the mixing variable `Z`; under `IsConditionallyBernoulliIID`, the
-- first `n` draws have conditional law `Ber_Z^{⊗ n}`, so the conditional probability that all of
-- them are black is `Z^n`. Integrating the conditional probability identifies the `n`th moment of
-- `Z` with the black-prefix probability.
section

omit [StandardBorelSpace Ω]

/-- For a `{0,1}`-valued process that is conditionally i.i.d. Bernoulli with parameter `Z`, the
`n`th moment of `Z` is the probability that the first `n` draws are black. -/
private theorem moment_eq_prob_black_prefix_of_isConditionallyBernoulliIID
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Bool}
    {Z : Ω → unitInterval} (hX : IsConditionallyBernoulliIID Z X μ) (n : ℕ) :
    μ[fun ω ↦ (Z ω : ℝ) ^ n] =
      (μ {ω | ∀ i : Fin n, X i ω = true}).toReal := by
  let A : Set Ω := {ω | ∀ i : Fin n, X i ω = true}
  have hA : MeasurableSet A := by
    -- Proof comment: the all-black prefix event is a finite intersection of measurable singleton
    -- fibers.
    rw [show A = {ω | ∀ i : Fin n, X i ω = true} by rfl]
    rw [blackPrefixEvent_eq_biInter (X := fun i : Fin n ↦ X i)]
    exact (Finset.univ : Finset (Fin n)).measurableSet_biInter fun i _ ↦
      (hX.isConditionallyIID.1.1 i) (measurableSet_singleton true)
  calc
    μ[fun ω ↦ (Z ω : ℝ) ^ n] =
        ∫ ω, (μ⟦A | MeasurableSpace.comap Z inferInstance⟧) ω ∂μ := by
      -- Proof comment: replace the integrand by the conditional all-black prefix probability.
      refine integral_congr_ae ?_
      simpa [A] using (blackPrefixCondProb_eq_pow_ae hX n).symm
    _ = μ.real A := by
      -- Proof comment: integrating the conditional probability recovers the original event
      -- probability.
      simpa [A] using
        (MeasureTheory.integral_condExp_indicator (μ := μ) (Y := Z) hX.measurable hA)
    _ = (μ A).toReal := by
      rw [Measure.real_def]

end

section

omit [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Helper for Example 12.29: the coercion of a `unitInterval`-valued random variable has range
contained in the bounded interval `Set.Icc (0 : ℝ) 1`. -/
private theorem isBounded_range_coe_unitInterval (Z : Ω → unitInterval) :
    Bornology.IsBounded (Set.range fun ω ↦ (Z ω : ℝ)) := by
  -- Proof comment: every value of `Z` already lies in the compact interval `[0,1]`.
  refine (Metric.isBounded_Icc (a := (0 : ℝ)) (b := 1)).subset ?_
  rintro _ ⟨ω, rfl⟩
  exact ⟨(Z ω).2.1, (Z ω).2.2⟩

end

/-- Helper for Example 12.29: the Beta law with natural parameters `(M, N - M)` has the textbook
moment product formula. -/
private theorem betaMoment_natParams_eq_product
    {M N : ℕ} (hM : 0 < M) (hMN : M < N) (n : ℕ) :
    moment (id : ℝ → ℝ) n (betaMeasure M (N - M : ℕ)) =
      ∏ k ∈ Finset.range n, ((M + k : ℕ) : ℝ) / ((N + k : ℕ) : ℝ) := by
  have hM_real : 0 < (M : ℝ) := by
    exact_mod_cast hM
  have hNM_real : 0 < ((N - M : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hMN
  -- Proof comment: specialize the textbook Beta-moment formula to the identity map on the
  -- canonical Beta space and simplify `M + (N - M)` to `N`.
  calc
    moment (id : ℝ → ℝ) n (betaMeasure M (N - M : ℕ)) =
        ∏ k ∈ Finset.range n, ((M : ℝ) + k) / ((M : ℝ) + ((N - M : ℕ) : ℝ) + k) := by
      simpa [moment] using
        (beta_moment_formula (M : ℝ) ((N - M : ℕ) : ℝ) hM_real hNM_real
          (ProbabilityTheory.HasLaw.id (μ := betaMeasure M (N - M : ℕ))) n)
    _ = ∏ k ∈ Finset.range n, ((M + k : ℕ) : ℝ) / ((N + k : ℕ) : ℝ) := by
      refine Finset.prod_congr rfl ?_
      intro k hk
      have hNM : (((N - M : ℕ) : ℝ) + M) = N := by
        exact_mod_cast Nat.sub_add_cancel (Nat.le_of_lt hMN)
      have hden : (M : ℝ) + ((N - M : ℕ) : ℝ) + k = (N : ℝ) + k := by
        linarith
      rw [Nat.cast_add, Nat.cast_add, hden]

section

omit [StandardBorelSpace Ω]

/-- Helper for Example 12.29: the moments of the directing parameter `Z` match the moments of the
Beta law once the all-black prefix probabilities are identified with the Pólya-urn product. -/
private theorem polyaUrnMoment_eq_betaMoment
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Bool}
    {Z : Ω → unitInterval} (hX : IsConditionallyBernoulliIID Z X μ)
    {M N : ℕ} (hM : 0 < M) (hMN : M < N)
    (h_black_prefix : ∀ n : ℕ,
      (μ {ω | ∀ i : Fin n, X i ω = true}).toReal =
        ∏ k ∈ Finset.range n, ((M + k : ℕ) : ℝ) / ((N + k : ℕ) : ℝ)) :
    ∀ n : ℕ,
      moment (fun ω ↦ (Z ω : ℝ)) n μ =
        moment (id : ℝ → ℝ) n (betaMeasure M (N - M : ℕ)) := by
  intro n
  calc
    moment (fun ω ↦ (Z ω : ℝ)) n μ = μ[fun ω ↦ (Z ω : ℝ) ^ n] := by
      rfl
    _ = (μ {ω | ∀ i : Fin n, X i ω = true}).toReal := by
      exact moment_eq_prob_black_prefix_of_isConditionallyBernoulliIID hX n
    _ = ∏ k ∈ Finset.range n, ((M + k : ℕ) : ℝ) / ((N + k : ℕ) : ℝ) := by
      exact h_black_prefix n
    _ = moment (id : ℝ → ℝ) n (betaMeasure M (N - M : ℕ)) := by
      exact (betaMoment_natParams_eq_product hM hMN n).symm

end

-- Proof sketch: first use
-- `moment_eq_prob_black_prefix_of_isConditionallyBernoulliIID` to identify the moments of `Z`
-- with the probabilities of the events `{X₀ = ⋯ = X_{n-1} = 1}`. The Pólya-urn formula gives
-- these probabilities as `∏_{k=0}^{n-1} (M + k)/(N + k)`, which are exactly the moments of the
-- Beta distribution with parameters `M` and `N - M`; moment determinacy on `[0,1]` then yields
-- the claimed law.
section

omit [StandardBorelSpace Ω]

/-- Example 12.29: for Pólya's urn model, if the color indicators are conditionally i.i.d.
Bernoulli given a random parameter `Z` and the black-prefix probabilities are the usual
Pólya-urn products, then `Z` has Beta law with parameters `M` and `N - M`. -/
theorem polyaUrn_limit_hasLaw_beta
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → Bool}
    {Z : Ω → unitInterval} (hX : IsConditionallyBernoulliIID Z X μ)
    {M N : ℕ} (hM : 0 < M) (hMN : M < N)
    (h_black_prefix : ∀ n : ℕ,
      (μ {ω | ∀ i : Fin n, X i ω = true}).toReal =
        ∏ k ∈ Finset.range n, ((M + k : ℕ) : ℝ) / ((N + k : ℕ) : ℝ)) :
    HasLaw (fun ω ↦ (Z ω : ℝ)) (betaMeasure M (N - M : ℕ)) μ := by
  have hBounded : Bornology.IsBounded (Set.range fun ω ↦ (Z ω : ℝ)) :=
    isBounded_range_coe_unitInterval Z
  have hMoments :
      ∀ n : ℕ,
        moment (fun ω ↦ (Z ω : ℝ)) n μ =
          moment (id : ℝ → ℝ) n (betaMeasure M (N - M : ℕ)) :=
    polyaUrnMoment_eq_betaMoment hX hM hMN h_black_prefix
  have hM_real : 0 < (M : ℝ) := by
    exact_mod_cast hM
  have hNM_real : 0 < ((N - M : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hMN
  letI : IsProbabilityMeasure (betaMeasure M (N - M : ℕ)) := isProbabilityMeasureBeta
    hM_real hNM_real
  have hIntBeta :
      ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) (betaMeasure M (N - M : ℕ)) :=
    integrableAbsPow_id_betaMeasure_natParams hM hMN
  have hIdent :
      IdentDistrib (fun ω ↦ (Z ω : ℝ)) (id : ℝ → ℝ) μ
        (betaMeasure M (N - M : ℕ)) :=
    identDistrib_of_forall_moment_eq_of_isBounded_range
      (measurable_subtype_coe.comp hX.measurable) measurable_id hBounded hIntBeta hMoments
  -- Route correction: use the chapter's bounded-support moment-determinacy theorem directly.
  exact hIdent.symm.hasLaw (ProbabilityTheory.HasLaw.id (μ := betaMeasure M (N - M : ℕ)))

end
