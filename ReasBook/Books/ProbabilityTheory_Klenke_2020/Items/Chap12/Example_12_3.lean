/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Definition_12_20
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory unitInterval

universe u v w

/-- The set of binary words of length `N` containing exactly `M` black entries. -/
def blackIndicatorWordSet (N M : ℕ) : Set (Fin N → Bool) :=
  {x | (Finset.univ.filter fun i : Fin N ↦ x i).card = M}

/-- Helper for Example 12.3: a permutation of the coordinates of a binary word acts by precomposing
with the inverse permutation. -/
def permuteBlackIndicatorWord {N : ℕ} (ρ : Equiv.Perm (Fin N)) (x : Fin N → Bool) : Fin N → Bool :=
  fun i ↦ x (ρ.symm i)

/-- A `Bool`-valued family is conditionally i.i.d. Bernoulli with parameter `Y`: this is the
source-facing Bernoulli specialization of the chapter owner `IsConditionallyIID`, with the extra
requirement that each conditional coordinate law given `Y` is the Bernoulli law of parameter
`Y`. -/
abbrev IsConditionallyBernoulliIID {Ω : Type u} {ι : Type v}
    [mΩ : MeasurableSpace Ω]
    (Y : Ω → unitInterval) (X : ι → Ω → Bool)
    (μ : Measure Ω) [IsFiniteMeasure μ] : Prop :=
  Measurable Y ∧
    IsConditionallyIID (MeasurableSpace.comap Y inferInstance) X μ ∧
      ∀ i, ∀ᵐ y ∂μ.map Y,
        condDistrib (X i) Y μ y =
          (PMF.bernoulli (toNNReal y) (by simpa using y.2.2)).toMeasure

namespace IsConditionallyBernoulliIID

variable {Ω : Type u} {ι : Type v}
variable [mΩ : MeasurableSpace Ω]
variable {Y : Ω → unitInterval} {X : ι → Ω → Bool} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The Bernoulli specialization is defined over a measurable parameter `Y`. -/
theorem measurable (hX : IsConditionallyBernoulliIID Y X μ) : Measurable Y := by
  exact hX.1

/-- Forgetting the Bernoulli conditional-law clause leaves the chapter owner
`IsConditionallyIID`. -/
theorem isConditionallyIID (hX : IsConditionallyBernoulliIID Y X μ) :
    IsConditionallyIID (MeasurableSpace.comap Y inferInstance) X μ := by
  exact hX.2.1

theorem condDistrib_ae_eq_bernoulli (hX : IsConditionallyBernoulliIID Y X μ) (i : ι) :
    ∀ᵐ y ∂μ.map Y,
      condDistrib (X i) Y μ y =
        (PMF.bernoulli (toNNReal y) (by simpa using y.2.2)).toMeasure := by
  exact hX.2.2 i

end IsConditionallyBernoulliIID

namespace IsConditionallyIndependentFun

variable {Ω : Type u} {ι : Type v} {κ : Type*} {E : Type w}
variable [MeasurableSpace E]
variable {m : MeasurableSpace Ω} {X : ι → Ω → E} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Helper for Example 12.3: precomposing a source-facing conditionally independent family with an
embedding preserves conditional independence. -/
theorem comp_embedding (hX : IsConditionallyIndependentFun m X μ) (u : κ ↪ ι) :
    IsConditionallyIndependentFun m (fun k ↦ X (u k)) μ := by
  classical
  refine ⟨fun k ↦ hX.1 (u k), ?_⟩
  refine ⟨hX.2.1, fun k ↦ hX.2.2.1 (u k), ?_⟩
  intro s A hA
  let B : ι → Set Ω := fun i ↦
    if hi : ∃ k, u k = i then A (Classical.choose hi) else Set.univ
  have hB :
      ∀ i, i ∈ s.map u →
        MeasurableSet[MeasurableSpace.comap (X i) inferInstance] (B i) := by
    intro i hi
    rcases Finset.mem_map.1 hi with ⟨k, hk, rfl⟩
    -- Proof comment: on the image of `u`, the transported event family `B` is literally `A`.
    have hchoose : Classical.choose (show ∃ j, u j = u k from ⟨k, rfl⟩) = k := by
      exact u.injective (Classical.choose_spec (show ∃ j, u j = u k from ⟨k, rfl⟩))
    simpa [B, hchoose] using hA k hk
  -- Proof comment: factor the conditional probability on the mapped finite family, then simplify
  -- the mapped intersection and product back to the original `κ`-indexed expressions.
  simpa [B] using hX.2.2.2 (s.map u) hB

end IsConditionallyIndependentFun

namespace IsConditionallyIID

variable {Ω : Type u} {ι : Type v} {κ : Type*} {E : Type w}
variable [MeasurableSpace E]
variable {m : MeasurableSpace Ω} {X : ι → Ω → E} {μ : Measure Ω} [IsFiniteMeasure μ]

/-- Helper for Example 12.3: precomposing a source-facing conditionally i.i.d. family with an
embedding preserves the full conditional i.i.d. structure. -/
theorem comp_embedding (hX : IsConditionallyIID m X μ) (u : κ ↪ ι) :
    IsConditionallyIID m (fun k ↦ X (u k)) μ := by
  refine ⟨IsConditionallyIndependentFun.comp_embedding hX.1 u, ?_⟩
  refine ⟨hX.2.1, fun k ↦ hX.2.2.1 (u k), ?_⟩
  intro i j s hs
  -- Proof comment: the conditional identical-distribution clause is coordinatewise, so it passes
  -- to the embedded family without any extra finite-set argument.
  simpa using hX.2.2.2 (u i) (u j) s hs

end IsConditionallyIID

/-- Helper for Example 12.3: two injective `Fin n`-tuples in `Fin N` can be matched by a
permutation of `Fin N`. -/
private theorem existsPermApplyEqOfEmbedding {N n : ℕ} (u v : Fin n ↪ Fin N) :
    ∃ ρ : Equiv.Perm (Fin N), ∀ i, ρ (v i) = u i := by
  classical
  let e : Set.range v ≃ Set.range u :=
    { toFun := fun x ↦ ⟨u (v.invOfMemRange x), Set.mem_range_self _⟩
      invFun := fun x ↦ ⟨v (u.invOfMemRange x), Set.mem_range_self _⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro x
        apply Subtype.ext
        simp }
  -- Proof comment: extend the bijection between the two finite ranges to a permutation of all of
  -- `Fin N`.
  refine ⟨e.extendSubtype, ?_⟩
  intro i
  rw [Equiv.extendSubtype_apply_of_mem e (v i) (Set.mem_range_self i)]
  simp [e]

/-- Helper for Example 12.3: permuting coordinates does not change the number of black entries in a
binary word. -/
private theorem mem_blackIndicatorWordSet_compSymm_iff {N M : ℕ}
    (ρ : Equiv.Perm (Fin N)) (x : Fin N → Bool) :
    permuteBlackIndicatorWord ρ x ∈ blackIndicatorWordSet N M ↔ x ∈ blackIndicatorWordSet N M := by
  classical
  have hcard :
      (Finset.univ.filter fun i : Fin N ↦ x (ρ.symm i)).card =
        (Finset.univ.filter fun i : Fin N ↦ x i).card := by
    refine Finset.card_nbij (fun i : Fin N ↦ ρ.symm i) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
      exact hi
    · intro i hi j hj hij
      exact ρ.symm.injective hij
    · intro j hj
      refine ⟨ρ j, ?_, by simp⟩
      simpa using hj
  -- Proof comment: the finite filter selecting the black positions is carried bijectively onto the
  -- original one by `ρ.symm`.
  simpa [blackIndicatorWordSet, permuteBlackIndicatorWord] using
    congrArg (fun n ↦ n = M) hcard

/-- Helper for Example 12.3: the uniform measure on binary words with exactly `M` black entries is
invariant under coordinate permutations. -/
private theorem map_uniformOn_blackIndicatorWordSet_eq_self {N M : ℕ}
    (ρ : Equiv.Perm (Fin N)) :
    Measure.map (permuteBlackIndicatorWord ρ) (uniformOn (blackIndicatorWordSet N M)) =
      uniformOn (blackIndicatorWordSet N M) := by
  classical
  let s : Finset (Fin N → Bool) :=
    Finset.univ.filter fun x ↦ x ∈ blackIndicatorWordSet N M
  have hs :
      (blackIndicatorWordSet N M : Set (Fin N → Bool)) = (s : Set (Fin N → Bool)) := by
    ext z
    simp [s]
  -- Proof comment: on the countable space `Fin N → Bool`, it is enough to compare singleton
  -- masses. The permutation sends a singleton back to the singleton of the inverse image, and the
  -- previous support-invariance lemma shows that both singleton masses coincide.
  apply Measure.ext_of_singleton
  intro x
  have hpreimage :
      (permuteBlackIndicatorWord ρ) ⁻¹' ({x} : Set (Fin N → Bool)) =
        {permuteBlackIndicatorWord ρ.symm x} := by
    ext z
    constructor
    · intro hz
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hz ⊢
      ext i
      have hzi := congrArg (fun f : Fin N → Bool ↦ f (ρ i)) hz
      simpa [permuteBlackIndicatorWord] using hzi
    · intro hz
      simp only [Set.mem_singleton_iff] at hz
      subst hz
      ext i
      simp [permuteBlackIndicatorWord]
  have hmem :
      permuteBlackIndicatorWord ρ.symm x ∈ blackIndicatorWordSet N M ↔
        x ∈ blackIndicatorWordSet N M := by
    simpa using mem_blackIndicatorWordSet_compSymm_iff (N := N) (M := M) ρ.symm x
  rw [Measure.map_apply (Measurable.of_discrete : Measurable (permuteBlackIndicatorWord ρ))
      (measurableSet_singleton x), hpreimage]
  rw [hs]
  rw [show ({permuteBlackIndicatorWord ρ.symm x} : Set (Fin N → Bool)) =
      ((({permuteBlackIndicatorWord ρ.symm x} : Finset (Fin N → Bool)) : Set (Fin N → Bool))) by
        ext y
        simp,
    show ({x} : Set (Fin N → Bool)) = ((({x} : Finset (Fin N → Bool)) : Set (Fin N → Bool))) by
        ext y
        simp]
  by_cases hx_s : x ∈ s
  · have hx : x ∈ blackIndicatorWordSet N M := by simpa [s] using hx_s
    have hx' : permuteBlackIndicatorWord ρ.symm x ∈ blackIndicatorWordSet N M := hmem.2 hx
    have hx'_s : permuteBlackIndicatorWord ρ.symm x ∈ s := by simp [s, hx']
    rw [ProbabilityTheory.uniformOn_apply_finset, ProbabilityTheory.uniformOn_apply_finset]
    simp [hx_s, hx'_s]
  · have hx : x ∉ blackIndicatorWordSet N M := by simpa [s] using hx_s
    have hx' : permuteBlackIndicatorWord ρ.symm x ∉ blackIndicatorWordSet N M := by
      exact fun hx' ↦ hx (hmem.1 hx')
    have hx'_s : permuteBlackIndicatorWord ρ.symm x ∉ s := by simp [s, hx']
    rw [ProbabilityTheory.uniformOn_apply_finset, ProbabilityTheory.uniformOn_apply_finset]
    simp [hx_s, hx'_s]

/-- Helper for Example 12.3: the real singleton mass of a Bernoulli law on `Bool` is the expected
`y`/`1-y` formula for `unitInterval` parameters. -/
private theorem bernoulliMeasureReal_singleton_unitInterval (y : unitInterval) (b : Bool) :
    ((PMF.bernoulli (toNNReal y) (by simpa using y.2.2)).toMeasure).real ({b} : Set Bool) =
      if b then (y : ℝ) else 1 - (y : ℝ) := by
  have hy : unitInterval.toNNReal y ≤ 1 := by
    simpa [unitInterval.toNNReal] using y.2.2
  cases b
  · simp [Measure.real_def, hy]
  · simp [Measure.real_def]

/-- Helper for Example 12.3: the singleton conditional probability for a Bernoulli coordinate is
the Bernoulli mass determined by `Y`. -/
private theorem condProbBoolSingleton_eq_bernoulliMass_ae {Ω : Type u} {ι : Type v}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : Ω → unitInterval} {X : ι → Ω → Bool}
    (hX : IsConditionallyBernoulliIID Y X μ) (i : ι) (b : Bool) :
    μ⟦X i ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap Y inferInstance⟧ =ᵐ[μ]
      fun ω ↦ if b then (Y ω : ℝ) else 1 - (Y ω : ℝ) := by
  have hcond :
      μ⟦X i ⁻¹' ({b} : Set Bool) | MeasurableSpace.comap Y inferInstance⟧ =ᵐ[μ]
        fun ω ↦ (condDistrib (X i) Y μ (Y ω)).real ({b} : Set Bool) := by
    -- Proof comment: rewrite the source-facing conditional probability through the regular
    -- conditional distribution of `X i` given `Y`.
    simpa using
      (condDistrib_ae_eq_condExp (μ := μ) (X := Y) (Y := X i)
        hX.measurable
        ((IsConditionallyBernoulliIID.isConditionallyIID hX).1.1 i)
        (measurableSet_singleton b)).symm
  have hbernoulli_map :
      ∀ᵐ y ∂μ.map Y,
        (condDistrib (X i) Y μ y).real ({b} : Set Bool) =
          if b then (y : ℝ) else 1 - (y : ℝ) := by
    filter_upwards [hX.condDistrib_ae_eq_bernoulli i] with y hy
    -- Proof comment: once the conditional law is identified as Bernoulli, singleton masses are a
    -- direct `simp` computation on `Bool`.
    rw [hy]
    simpa using bernoulliMeasureReal_singleton_unitInterval y b
  have hbernoulli :
      (fun ω ↦ (condDistrib (X i) Y μ (Y ω)).real ({b} : Set Bool)) =ᵐ[μ]
        fun ω ↦ if b then (Y ω : ℝ) else 1 - (Y ω : ℝ) := by
    exact MeasureTheory.ae_of_ae_map hX.measurable.aemeasurable hbernoulli_map
  exact hcond.trans hbernoulli

/-- Helper for Example 12.3: the conditional probability of a finite Boolean cylinder event is the
corresponding Bernoulli product, hence depends only on `x` and `Y`, not on the embedding `u`. -/
private theorem condProbTupleSingleton_eq_bernoulliProduct_ae {Ω : Type u} {ι : Type v}
    [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : Ω → unitInterval} {X : ι → Ω → Bool}
    (hX : IsConditionallyBernoulliIID Y X μ) {n : ℕ} (u : Fin n ↪ ι) (x : Fin n → Bool) :
    μ⟦⋂ i ∈ Finset.univ, X (u i) ⁻¹' ({x i} : Set Bool)
        | MeasurableSpace.comap Y inferInstance⟧ =ᵐ[μ]
      fun ω ↦ ∏ i : Fin n, if x i then (Y ω : ℝ) else 1 - (Y ω : ℝ) := by
  have hXu :
      IsConditionallyIID (MeasurableSpace.comap Y inferInstance) (fun k ↦ X (u k)) μ :=
    by
      let hIID : IsConditionallyIID (MeasurableSpace.comap Y inferInstance) X μ :=
        IsConditionallyBernoulliIID.isConditionallyIID hX
      have hIndep :
          IsConditionallyIndependentFun (MeasurableSpace.comap Y inferInstance)
            (fun k ↦ X (u k)) μ := by
        classical
        refine ⟨fun k ↦ hIID.1.1 (u k), ?_⟩
        refine ⟨hIID.1.2.1, fun k ↦ hIID.1.2.2.1 (u k), ?_⟩
        intro s A hA
        let B : ι → Set Ω := fun i ↦
          if hi : ∃ k, u k = i then A (Classical.choose hi) else Set.univ
        have hB :
            ∀ i, i ∈ s.map u →
              MeasurableSet[MeasurableSpace.comap (X i) inferInstance] (B i) := by
          intro i hi
          rcases Finset.mem_map.1 hi with ⟨k, hk, rfl⟩
          have hchoose : Classical.choose (show ∃ j, u j = u k from ⟨k, rfl⟩) = k := by
            exact u.injective (Classical.choose_spec (show ∃ j, u j = u k from ⟨k, rfl⟩))
          simpa [B, hchoose] using hA k hk
        -- Proof comment: the same finite-range reindexing used in the standalone embedding lemma
        -- transports the source-facing conditional-independence factorization to the tuple family.
        simpa [B] using hIID.1.2.2.2 (s.map u) hB
      refine ⟨hIndep, ?_⟩
      refine ⟨hIID.2.1, fun k ↦ hIID.2.2.1 (u k), ?_⟩
      intro i j s hs
      simpa using hIID.2.2.2 (u i) (u j) s hs
  have hfactor :
      μ⟦⋂ i ∈ Finset.univ, X (u i) ⁻¹' ({x i} : Set Bool)
          | MeasurableSpace.comap Y inferInstance⟧ =ᵐ[μ]
        ∏ i ∈ Finset.univ, μ⟦X (u i) ⁻¹' ({x i} : Set Bool)
          | MeasurableSpace.comap Y inferInstance⟧ := by
    -- Proof comment: after restricting along `u`, conditional independence factors the finite
    -- cylinder event into the product of the one-coordinate conditional probabilities.
    simpa using hXu.1.2.2.2 (Finset.univ)
      (fun i _ ↦ ⟨({x i} : Set Bool), measurableSet_singleton _, rfl⟩)
  have hcoords :
      ∀ᵐ ω ∂μ, ∀ i : Fin n,
        (μ⟦X (u i) ⁻¹' ({x i} : Set Bool) | MeasurableSpace.comap Y inferInstance⟧) ω =
          if x i then (Y ω : ℝ) else 1 - (Y ω : ℝ) := by
    exact ae_all_iff.2 fun i ↦ condProbBoolSingleton_eq_bernoulliMass_ae hX (u i) (x i)
  have hprod :
      (∏ i ∈ Finset.univ, μ⟦X (u i) ⁻¹' ({x i} : Set Bool)
          | MeasurableSpace.comap Y inferInstance⟧) =ᵐ[μ]
        fun ω ↦ ∏ i : Fin n, if x i then (Y ω : ℝ) else 1 - (Y ω : ℝ) := by
    filter_upwards [hcoords] with ω hω
    -- Proof comment: on the almost-sure set where every coordinate factor has the Bernoulli mass,
    -- the finite product is pointwise identical to the Bernoulli product formula.
    simp [hω]
  exact hfactor.trans hprod

-- Proof sketch: for each finite tuple, independence and pairwise identical distribution imply that
-- the tuple law is a product of identical marginals, and this product measure is invariant under
-- permuting the coordinates.
/-- Helper for Example 12.3 (1): an i.i.d. family of random variables is exchangeable. -/
theorem exchangeableFamily_of_isIID {Ω : Type u} {ι : Type v} {E : Type w}
    [MeasurableSpace Ω] [MeasurableSpace E] {μ : Measure Ω}
    {X : ι → Ω → E} (hX : IsIID X μ) :
    IsExchangeable X μ := by
  refine (isExchangeable_iff_identDistrib_of_pairwise_distinct (X := X) (μ := μ)).2 ?_
  intro n u v
  -- Proof comment: restrict the i.i.d. family to the two injective `n`-tuples and compare their
  -- product laws coordinatewise.
  refine IdentDistrib.pi ?_ ?_ ?_
  · intro i
    exact hX.identDistrib (u i) (v i)
  · simpa using hX.iIndepFun.precomp u.injective
  · simpa using hX.iIndepFun.precomp v.injective

-- Proof sketch: under the uniform measure on binary words with exactly `M` ones, every admissible
-- word has the same probability. Permuting coordinates preserves both admissibility and this
-- uniform weight, so the coordinate process is exchangeable.
/-- Helper for Example 12.3 (2): the coordinate process under the uniform law on black/white
words of length `N` with exactly `M` black draws is exchangeable; this is the
without-replacement urn model. -/
theorem exchangeableFamily_coordinateProcess_uniformOn_blackIndicatorWordSet (N M : ℕ) :
    IsExchangeable (fun i (x : Fin N → Bool) ↦ x i)
      (uniformOn (blackIndicatorWordSet N M)) := by
  classical
  refine (isExchangeable_iff_identDistrib_of_pairwise_distinct
    (X := fun i (x : Fin N → Bool) ↦ x i)
    (μ := uniformOn (blackIndicatorWordSet N M))).2 ?_
  intro n u v
  obtain ⟨ρ, hρ⟩ := existsPermApplyEqOfEmbedding u v
  let τ : (Fin N → Bool) → (Fin N → Bool) := permuteBlackIndicatorWord ρ
  have hτ_measure :
      Measure.map τ (uniformOn (blackIndicatorWordSet N M)) =
        uniformOn (blackIndicatorWordSet N M) :=
    map_uniformOn_blackIndicatorWordSet_eq_self (N := N) (M := M) ρ
  have htuple :
      (fun x i ↦ (τ x) (u i)) = fun x i ↦ x (v i) := by
    funext x
    ext i
    have hρi := congrArg ρ.symm (hρ i)
    simpa [τ, permuteBlackIndicatorWord] using (congrArg x hρi).symm
  refine ⟨(Measurable.of_discrete :
      Measurable (fun x : Fin N → Bool ↦ fun i ↦ x (u i))).aemeasurable,
    (Measurable.of_discrete :
      Measurable (fun x : Fin N → Bool ↦ fun i ↦ x (v i))).aemeasurable,
    ?_⟩
  -- Proof comment: transport the sample-space law by the permutation matching `v` to `u`, then
  -- rewrite the tuple extractor along the pointwise identity `hρ`.
  calc
    Measure.map (fun x : Fin N → Bool ↦ fun i ↦ x (u i))
        (uniformOn (blackIndicatorWordSet N M))
      =
        Measure.map (fun x : Fin N → Bool ↦ fun i ↦ x (u i))
          (Measure.map τ (uniformOn (blackIndicatorWordSet N M))) := by
            rw [hτ_measure]
    _ =
        Measure.map (fun x : Fin N → Bool ↦ fun i ↦ (τ x) (u i))
          (uniformOn (blackIndicatorWordSet N M)) := by
            rw [Measure.map_map]
            · rfl
            · exact Measurable.of_discrete
            · exact Measurable.of_discrete
    _ =
        Measure.map (fun x : Fin N → Bool ↦ fun i ↦ x (v i))
          (uniformOn (blackIndicatorWordSet N M)) := by
            simp [htuple]

-- Proof sketch: conditional on `Y = y`, the finite-dimensional laws are products of Bernoulli
-- measures with common parameter `y`, hence invariant under coordinate permutations. Integrating
-- these conditional laws over the law of `Y` preserves the permutation invariance.
/-- Example 12.3 (3): A Bernoulli family that is conditionally i.i.d. with parameter `Y ∈ [0,1]`
is exchangeable. -/
theorem exchangeableFamily_of_isConditionallyBernoulliIID {Ω : Type u} {ι : Type v}
    [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : Ω → unitInterval} {X : ι → Ω → Bool}
    (hX : IsConditionallyBernoulliIID Y X μ) :
    IsExchangeable X μ := by
  refine (isExchangeable_iff_identDistrib_of_pairwise_distinct (X := X) (μ := μ)).2 ?_
  intro n u v
  let Tu : Ω → Fin n → Bool := fun ω i ↦ X (u i) ω
  let Tv : Ω → Fin n → Bool := fun ω i ↦ X (v i) ω
  have hTu_meas : Measurable Tu := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa [Tu] using
      ((IsConditionallyBernoulliIID.isConditionallyIID hX).1.1 (u i))
  have hTv_meas : Measurable Tv := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    simpa [Tv] using
      ((IsConditionallyBernoulliIID.isConditionallyIID hX).1.1 (v i))
  refine ⟨hTu_meas.aemeasurable, hTv_meas.aemeasurable, ?_⟩
  apply (MeasureTheory.ext_iff_measureReal_singleton
    (μ1 := Measure.map Tu μ) (μ2 := Measure.map Tv μ)).2
  intro x
  have hTu_preimage :
      Tu ⁻¹' ({x} : Set (Fin n → Bool)) =
        ⋂ i ∈ Finset.univ, X (u i) ⁻¹' ({x i} : Set Bool) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Finset.mem_univ,
      forall_true_left, Tu]
    constructor
    · intro hω i
      exact congrArg (fun f : Fin n → Bool ↦ f i) hω
    · intro hω
      ext i
      exact hω i
  have hTv_preimage :
      Tv ⁻¹' ({x} : Set (Fin n → Bool)) =
        ⋂ i ∈ Finset.univ, X (v i) ⁻¹' ({x i} : Set Bool) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Finset.mem_univ,
      forall_true_left, Tv]
    constructor
    · intro hω i
      exact congrArg (fun f : Fin n → Bool ↦ f i) hω
    · intro hω
      ext i
      exact hω i
  have hTu_singleton :
      (Measure.map Tu μ).real ({x} : Set (Fin n → Bool)) =
        ∫ ω, ∏ i : Fin n, if x i then (Y ω : ℝ) else 1 - (Y ω : ℝ) ∂μ := by
    calc
      (Measure.map Tu μ).real ({x} : Set (Fin n → Bool))
          = μ.real (Tu ⁻¹' ({x} : Set (Fin n → Bool))) := by
              simpa [Measure.real_def] using congrArg ENNReal.toReal
                (Measure.map_apply hTu_meas (measurableSet_singleton x))
      _ = ∫ ω, (μ⟦Tu ⁻¹' ({x} : Set (Fin n → Bool))
            | MeasurableSpace.comap Y inferInstance⟧) ω ∂μ := by
              symm
              exact integral_condExp_indicator hX.measurable (hTu_meas (measurableSet_singleton x))
      _ = ∫ ω, (μ⟦⋂ i ∈ Finset.univ, X (u i) ⁻¹' ({x i} : Set Bool)
            | MeasurableSpace.comap Y inferInstance⟧) ω ∂μ := by
              rw [hTu_preimage]
      _ = ∫ ω, ∏ i : Fin n, if x i then (Y ω : ℝ) else 1 - (Y ω : ℝ) ∂μ := by
              refine integral_congr_ae ?_
              exact condProbTupleSingleton_eq_bernoulliProduct_ae hX u x
  have hTv_singleton :
      (Measure.map Tv μ).real ({x} : Set (Fin n → Bool)) =
        ∫ ω, ∏ i : Fin n, if x i then (Y ω : ℝ) else 1 - (Y ω : ℝ) ∂μ := by
    calc
      (Measure.map Tv μ).real ({x} : Set (Fin n → Bool))
          = μ.real (Tv ⁻¹' ({x} : Set (Fin n → Bool))) := by
              simpa [Measure.real_def] using congrArg ENNReal.toReal
                (Measure.map_apply hTv_meas (measurableSet_singleton x))
      _ = ∫ ω, (μ⟦Tv ⁻¹' ({x} : Set (Fin n → Bool))
            | MeasurableSpace.comap Y inferInstance⟧) ω ∂μ := by
              symm
              exact integral_condExp_indicator hX.measurable (hTv_meas (measurableSet_singleton x))
      _ = ∫ ω, (μ⟦⋂ i ∈ Finset.univ, X (v i) ⁻¹' ({x i} : Set Bool)
            | MeasurableSpace.comap Y inferInstance⟧) ω ∂μ := by
              rw [hTv_preimage]
      _ = ∫ ω, ∏ i : Fin n, if x i then (Y ω : ℝ) else 1 - (Y ω : ℝ) ∂μ := by
              refine integral_congr_ae ?_
              exact condProbTupleSingleton_eq_bernoulliProduct_ae hX v x
  exact hTu_singleton.trans hTv_singleton.symm
