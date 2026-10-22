/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_7
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Exercise_12_1_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Exercise_12_1_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap12.Remark_12_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u v

noncomputable section

variable {Ω : Type u} {S : Type v}

variable [MeasurableSpace Ω] [MeasurableSpace S]

/-- A finite family `X : Fin n → Ω → S` admits an infinite exchangeable extension if it is the
initial segment of an infinite exchangeable sequence on the same probability space. -/
def HasInfiniteExchangeableExtension {n : ℕ} (X : Fin n → Ω → S) (μ : Measure Ω) : Prop :=
  ∃ Y : ℕ → Ω → S, IsExchangeable Y μ ∧ X = Y ∘ Fin.valEmbedding

/-- Helper for Exercise 12.1.5: pulling identically distributed observables back along random
variables with the corresponding laws preserves identical distribution. -/
private theorem identDistrib_comp_hasLaw
    {Ω₁ Ω₂ Ξ₁ Ξ₂ E : Type*}
    [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace Ξ₁] [MeasurableSpace Ξ₂]
    [MeasurableSpace E]
    {μ : Measure Ω₁} {ν : Measure Ω₂} {P : Measure Ξ₁} {Q : Measure Ξ₂}
    {f : Ω₁ → E} {g : Ω₂ → E} {X : Ξ₁ → Ω₁} {Y : Ξ₂ → Ω₂}
    (hfg : IdentDistrib f g μ ν) (hX : HasLaw X μ P) (hY : HasLaw Y ν Q) :
    IdentDistrib (f ∘ X) (g ∘ Y) P Q := by
  -- Proof comment: realize both pullbacks through the common law `Measure.map f μ`.
  let κ : Measure E := Measure.map f μ
  have hf : HasLaw f κ μ := ⟨hfg.aemeasurable_fst, rfl⟩
  have hg : HasLaw g κ ν := by
    refine ⟨hfg.aemeasurable_snd, ?_⟩
    simpa [κ] using hfg.map_eq.symm
  exact (hf.comp hX).identDistrib (hg.comp hY)

/-- Helper for Exercise 12.1.5: pulling an exchangeable family back along a map with the
prescribed law preserves exchangeability. -/
private theorem isExchangeable_comp_hasLaw
    {I Ω Ω' E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace E]
    {μ : Measure Ω} {ν : Measure Ω'} {X : I → Ω → E} {T : Ω' → Ω}
    (hX : IsExchangeable X μ) (hT : HasLaw T μ ν) :
    IsExchangeable (fun i ω ↦ X i (T ω)) ν := by
  intro n u σ
  -- Proof comment: each finite tuple is pulled back from the source space along the same map.
  simpa using identDistrib_comp_hasLaw (hX u σ) hT hT

namespace IsExchangeable

/-- Helper for Exercise 12.1.5: measurable postcomposition preserves exchangeability. -/
theorem comp_measurable {I T : Type*} [MeasurableSpace T]
    {Ω : Type u} {E : Type v} [MeasurableSpace Ω] [MeasurableSpace E]
    {X : I → Ω → E} {μ : Measure Ω} {f : E → T}
    (hX : IsExchangeable X μ) (hf : Measurable f) :
    IsExchangeable (fun i ω ↦ f (X i ω)) μ := by
  intro n u σ
  -- Proof comment: apply the tuple-law invariance of `X` and postcompose coordinatewise by `f`.
  have hIdent := hX u σ
  have hPost : Measurable (fun z : Fin n → E ↦ fun i ↦ f (z i)) := by
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact hf.comp (measurable_pi_apply i)
  simpa [Function.comp] using hIdent.comp hPost

end IsExchangeable

/-- Helper for Exercise 12.1.5: the finite one-hot family on `Fin n` is Bool-valued. -/
private def indicatorBoolFamily (n : ℕ) : Fin n → Fin n → Bool :=
  fun i ω ↦ decide (ω = i)

/-- Helper for Exercise 12.1.5: the corresponding real-valued one-hot family on `Fin n`. -/
private def indicatorRealFamily (n : ℕ) : Fin n → Fin n → ℝ :=
  exchangeableCovarianceEqualityExample n

/-- Helper for Exercise 12.1.5: the uniform probability law on the nonempty finite space `Fin n`.
-/
private def indicatorFamilyLaw (n : ℕ) (hnz : n ≠ 0) : ProbabilityMeasure (Fin n) :=
  exchangeableCovarianceEqualityExampleLaw n hnz

/-- Helper for Exercise 12.1.5: converting the Bool indicator family to `0/1` reals recovers the
real-valued one-hot family. -/
private theorem indicatorBoolFamily_asReal (n : ℕ) :
    (fun i ω ↦ if indicatorBoolFamily n i ω then (1 : ℝ) else 0) =
      indicatorRealFamily n := by
  funext i ω
  -- Proof comment: the Bool indicator is true exactly at the unique marked atom.
  by_cases h : ω = i
  · simp [indicatorBoolFamily, indicatorRealFamily, exchangeableCovarianceEqualityExample, h]
  · simp [indicatorBoolFamily, indicatorRealFamily, exchangeableCovarianceEqualityExample, h]

/-- Helper for Exercise 12.1.5: reading the real-valued one-hot witness through the test
`x = 1` recovers the Bool-valued witness. -/
private theorem indicatorRealFamily_asBool (n : ℕ) :
    (fun i ω ↦ decide (indicatorRealFamily n i ω = (1 : ℝ))) = indicatorBoolFamily n := by
  funext i ω
  -- Proof comment: the real-valued indicator still only takes the values `0` and `1`.
  by_cases h : ω = i
  · simp [indicatorRealFamily, indicatorBoolFamily, exchangeableCovarianceEqualityExample, h]
  · simp [indicatorRealFamily, indicatorBoolFamily, exchangeableCovarianceEqualityExample, h]

/-- Helper for Exercise 12.1.5: the canonical `0/1` real coding of a Bool-valued sequence. -/
private def boolSequenceAsReal {Ω : Type*} (Y : ℕ → Ω → Bool) : ℕ → Ω → ℝ :=
  fun k ω ↦ if Y k ω then (1 : ℝ) else 0

/-- Helper for Exercise 12.1.5: if one coordinate of a Bool-valued extension agrees with the
finite one-hot witness, then its `0/1` real coding agrees with the real witness. -/
private theorem boolSequenceAsReal_eq_indicatorRealFamily_of_eq
    {n : ℕ} {Y : ℕ → Fin n → Bool} {k : ℕ} {i : Fin n}
    (hYi : Y k = indicatorBoolFamily n i) :
    boolSequenceAsReal Y k = indicatorRealFamily n i := by
  -- Proof comment: first rewrite the chosen coordinate using the witness equality, then collapse
  -- the Bool-to-Real coding with the canonical indicator identity.
  calc
    boolSequenceAsReal Y k = fun ω ↦ if indicatorBoolFamily n i ω then (1 : ℝ) else 0 := by
      funext ω
      simp [boolSequenceAsReal, hYi]
    _ = indicatorRealFamily n i := by
      simpa using
        congrArg (fun F : Fin n → Fin n → ℝ => F i) (indicatorBoolFamily_asReal n)

/-- Helper for Exercise 12.1.5: the finite Bool indicator family is exchangeable under the same
uniform law as the real-valued one-hot family. -/
private theorem indicatorBoolFamily_isExchangeable (n : ℕ) (hnz : n ≠ 0) :
    IsExchangeable (indicatorBoolFamily n)
      (indicatorFamilyLaw n hnz) := by
  have hReal :
      IsExchangeable (indicatorRealFamily n) (indicatorFamilyLaw n hnz) := by
    simpa [indicatorRealFamily, indicatorFamilyLaw] using
      exchangeableCovarianceEqualityExample_isExchangeable n hnz
  -- Proof comment: recover the Bool-valued family by postcomposing the real witness with the
  -- measurable test `x = 1`.
  simpa [indicatorRealFamily_asBool] using
    hReal.comp_measurable
      (f := fun x : ℝ ↦ decide (x = (1 : ℝ)))
      (Measurable.ite (measurableSet_singleton (1 : ℝ)) measurable_const measurable_const)

/-- Helper for Exercise 12.1.5: the first two coordinates of the real-valued one-hot family have
strictly negative covariance under the uniform law on `Fin n`. -/
private theorem indicatorRealFamilyFirstTwoCovariance_neg
    (n : ℕ) (hn : 1 < n) (hnz : n ≠ 0) :
    let i0 : Fin n := ⟨0, by omega⟩
    let i1 : Fin n := ⟨1, hn⟩
    cov[indicatorRealFamily n i0, indicatorRealFamily n i1; indicatorFamilyLaw n hnz] < 0 := by
  have hTwoLe : 2 ≤ n := by
    omega
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, hn⟩
  have hi01 : i0 ≠ i1 := by
    intro hEq
    have : (0 : ℕ) = 1 := by
      simpa [i0, i1] using congrArg Fin.val hEq
    omega
  have hEq :
      cov[indicatorRealFamily n i0, indicatorRealFamily n i1; indicatorFamilyLaw n hnz] =
        -((1 : ℝ) / (n - 1 : ℝ)) * Var[indicatorRealFamily n i0; indicatorFamilyLaw n hnz] := by
    simpa [indicatorRealFamily, indicatorFamilyLaw] using
      exchangeable_indicator_example_attains_covariance_bound n hTwoLe hi01
  have hVarNe :
      Var[indicatorRealFamily n i0; indicatorFamilyLaw n hnz] ≠ 0 := by
    simpa [indicatorRealFamily, indicatorFamilyLaw] using
      exchangeableCovarianceEqualityExample_variance_ne_zero n hTwoLe i0
  have hVarNonneg :
      0 ≤ Var[indicatorRealFamily n i0; indicatorFamilyLaw n hnz] := by
    exact variance_nonneg _ _
  have hVarPos :
      0 < Var[indicatorRealFamily n i0; indicatorFamilyLaw n hnz] :=
    lt_of_le_of_ne hVarNonneg hVarNe.symm
  have hCoeffNeg : -((1 : ℝ) / (n - 1 : ℝ)) < 0 := by
    have hDenPos : 0 < (n - 1 : ℝ) := by
      have : (1 : ℝ) < n := by
        exact_mod_cast hn
      linarith
    have hInvPos : 0 < (1 : ℝ) / (n - 1 : ℝ) := by
      positivity
    linarith
  have hNeg :
      cov[indicatorRealFamily n i0, indicatorRealFamily n i1; indicatorFamilyLaw n hnz] < 0 := by
    rw [hEq]
    nlinarith
  simpa [i0, i1] using hNeg

/-- Helper for Exercise 12.1.5: a Bool-valued random variable yields a square-integrable `0/1`
real indicator once it is almost everywhere measurable. -/
private theorem memLp_boolIndicator
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {B : Ω → Bool} (hB : AEMeasurable B μ) :
    MemLp (fun ω ↦ if B ω then (1 : ℝ) else 0) 2 μ := by
  let g : Bool → ℝ := fun b ↦ if b then 1 else 0
  have hg : Measurable g := Measurable.of_discrete
  have hbound :
      ∀ᵐ ω ∂μ, (g ∘ B) ω ∈ Set.Icc (0 : ℝ) 1 := by
    -- Proof comment: the transformed variable only takes the values `0` and `1`.
    filter_upwards with ω
    by_cases hω : B ω
    · simp [g, hω]
    · simp [g, hω]
  have hMeas : AEStronglyMeasurable (g ∘ B) μ :=
    (hg.aemeasurable.comp_aemeasurable hB).aestronglyMeasurable
  exact memLp_of_bounded hbound hMeas 2

/-- Helper for Exercise 12.1.5: the `0/1` real coding of an exchangeable Bool sequence remains
exchangeable. -/
private theorem boolSequenceAsReal_isExchangeable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Y : ℕ → Ω → Bool}
    (hY : IsExchangeable Y μ) :
    IsExchangeable (boolSequenceAsReal Y) μ := by
  -- Proof comment: postcompose every coordinate with the measurable map `Bool → ℝ`.
  simpa [boolSequenceAsReal] using
    hY.comp_measurable (f := fun b : Bool ↦ if b then (1 : ℝ) else 0) Measurable.of_discrete

/-- Helper for Exercise 12.1.5: each coordinate of the `0/1` real coding of an exchangeable Bool
sequence lies in `L²`. -/
private theorem boolSequenceAsReal_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {Y : ℕ → Ω → Bool} (hY : IsExchangeable Y μ) :
    ∀ k, MemLp (boolSequenceAsReal Y k) 2 μ := by
  intro k
  -- Proof comment: exchangeability gives the ae-measurability needed for the bounded indicator
  -- lemma.
  exact memLp_boolIndicator ((hY.identDistrib k k).aemeasurable_fst)

/-- Helper for Exercise 12.1.5: any infinite exchangeable extension of the Bool one-hot witness
forces the first two coded coordinates to have negative covariance. -/
private theorem indicatorBoolFamilyExtensionFirstTwoCovariance_neg
    (n : ℕ) (hn : 1 < n) (hnz : n ≠ 0)
    {Y : ℕ → Fin n → Bool}
    (hY : indicatorBoolFamily n = Y ∘ Fin.valEmbedding) :
    cov[boolSequenceAsReal Y 0, boolSequenceAsReal Y 1; indicatorFamilyLaw n hnz] < 0 := by
  have hZeroLt : 0 < n := by
    omega
  let i0 : Fin n := ⟨0, hZeroLt⟩
  let i1 : Fin n := ⟨1, hn⟩
  have hi01 : i0 ≠ i1 := by
    intro hEq
    have : (0 : ℕ) = 1 := by
      simpa [i0, i1] using congrArg Fin.val hEq
    omega
  have hY0 : Y 0 = indicatorBoolFamily n i0 := by
    -- Proof comment: the extension identity identifies the zeroth coordinate with the zeroth atom.
    have hCoord := congrArg (fun F : Fin n → Fin n → Bool => F i0) hY
    simpa [Function.comp, i0] using hCoord.symm
  have hY1 : Y 1 = indicatorBoolFamily n i1 := by
    -- Proof comment: the same restriction recovers the first coordinate of the finite witness.
    have hCoord := congrArg (fun F : Fin n → Fin n → Bool => F i1) hY
    simpa [Function.comp, i1] using hCoord.symm
  have hZ0 :
      boolSequenceAsReal Y 0 = indicatorRealFamily n i0 :=
    boolSequenceAsReal_eq_indicatorRealFamily_of_eq hY0
  have hZ1 :
      boolSequenceAsReal Y 1 = indicatorRealFamily n i1 :=
    boolSequenceAsReal_eq_indicatorRealFamily_of_eq hY1
  -- Proof comment: once the first two coordinates are normalized, the covariance is the explicit
  -- negative first-two-coordinate covariance from the finite one-hot model.
  simpa [hZ0, hZ1, i0, i1] using indicatorRealFamilyFirstTwoCovariance_neg n hn hnz

/-- Helper for Exercise 12.1.5: the finite one-hot Bool family on `Fin n` has no infinite
exchangeable extension under the uniform law. -/
private theorem indicatorBoolFamily_hasNoInfiniteExchangeableExtension
    (n : ℕ) (hn : 1 < n) (hnz : n ≠ 0) :
    ¬ HasInfiniteExchangeableExtension (indicatorBoolFamily n)
      (indicatorFamilyLaw n hnz) := by
  intro hExt
  rcases hExt with ⟨Y, hY, hY_ext⟩
  let Z : ℕ → Fin n → ℝ := boolSequenceAsReal Y
  have hZ : IsExchangeable Z (indicatorFamilyLaw n hnz) := by
    -- Proof comment: the `0/1` real coding preserves exchangeability of the hypothetical
    -- extension.
    simpa [Z] using boolSequenceAsReal_isExchangeable hY
  have hZ_memLp : ∀ k, MemLp (Z k) 2 (indicatorFamilyLaw n hnz) := by
    -- Proof comment: each coded coordinate is bounded between `0` and `1`.
    intro k
    dsimp [Z]
    exact boolSequenceAsReal_memLp hY k
  have hZCovNeg :
      cov[Z 0, Z 1; indicatorFamilyLaw n hnz] < 0 := by
    -- Route correction: keep the contradiction theorem linear by delegating the coordinate
    -- normalization and covariance sign computation to one dedicated helper.
    simpa [Z] using indicatorBoolFamilyExtensionFirstTwoCovariance_neg n hn hnz hY_ext
  have hCovNonneg :
      0 ≤ cov[Z 0, Z 1; indicatorFamilyLaw n hnz] := by
    -- Route correction: apply the earlier infinite-sequence covariance nonnegativity theorem
    -- directly to the real-coded extension.
    exact covariance_first_two_nonneg_of_isExchangeable hZ hZ_memLp
  linarith

/-- Helper for Exercise 12.1.5: pulling an infinite exchangeable extension back along a map with
the prescribed law preserves the extension property. -/
private theorem hasInfiniteExchangeableExtension_comp_hasLaw
    {n : ℕ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {S : Type*} [MeasurableSpace S]
    {μ : Measure Ω} {ν : Measure Ω'} {X : Fin n → Ω → S} {T : Ω' → Ω}
    (hX : HasInfiniteExchangeableExtension X μ) (hT : HasLaw T μ ν) :
    HasInfiniteExchangeableExtension (fun i ω ↦ X i (T ω)) ν := by
  rcases hX with ⟨Y, hY, rfl⟩
  -- Proof comment: pull back the full infinite extension coordinatewise along the same map.
  refine ⟨fun k ω ↦ Y k (T ω), isExchangeable_comp_hasLaw hY hT, ?_⟩
  funext i ω
  rfl

/-- Helper for Exercise 12.1.5: the lifted sample space used to package the finite witness at the
requested universe level. -/
private abbrev liftedIndicatorFamilySpace (n : ℕ) : Type u := ULift.{u} (Fin n)

/-- Helper for Exercise 12.1.5: the lifted probability law obtained from the base uniform law by
`ULift.up`. -/
private abbrev liftedIndicatorFamilyMeasure (n : ℕ) (hnz : n ≠ 0) :
    Measure (liftedIndicatorFamilySpace n) :=
  (indicatorFamilyLaw n hnz : Measure (Fin n)).map ULift.up

/-- Helper for Exercise 12.1.5: the finite Bool witness viewed on the lifted sample space. -/
private abbrev liftedIndicatorBoolFamily (n : ℕ) :
    Fin n → liftedIndicatorFamilySpace n → Bool :=
  fun i ω ↦ indicatorBoolFamily n i ω.down

/-- Helper for Exercise 12.1.5: the lifted measure is still a probability measure. -/
private theorem liftedIndicatorFamilyMeasure_isProbabilityMeasure
    (n : ℕ) (hnz : n ≠ 0) :
    IsProbabilityMeasure (liftedIndicatorFamilyMeasure n hnz) := by
  -- Proof comment: pushing a probability measure forward along `ULift.up` preserves total mass
  -- one.
  change IsProbabilityMeasure
    (((indicatorFamilyLaw n hnz : Measure (Fin n)).map ULift.up))
  infer_instance

/-- Helper for Exercise 12.1.5: `ULift.down` has the expected law from the lifted witness space
back to the base finite space. -/
private theorem uliftDownHasLawIndicatorFamily
    (n : ℕ) (hnz : n ≠ 0) :
    HasLaw (ULift.down : liftedIndicatorFamilySpace n → Fin n)
      (indicatorFamilyLaw n hnz : Measure (Fin n))
      (liftedIndicatorFamilyMeasure n hnz) := by
  -- Proof comment: `ULift.down` followed by `ULift.up` is the identity on the base finite space.
  refine ⟨measurable_down.aemeasurable, ?_⟩
  rw [show liftedIndicatorFamilyMeasure n hnz =
      ((indicatorFamilyLaw n hnz : Measure (Fin n)).map ULift.up) by rfl]
  rw [Measure.map_map measurable_down measurable_up]
  rw [show ULift.down ∘ ULift.up = (fun ω : Fin n ↦ ω) by
    funext ω
    rfl]
  exact Measure.map_id'

/-- Helper for Exercise 12.1.5: `ULift.up` pushes the base witness law to the lifted witness law.
-/
private theorem uliftUpHasLawIndicatorFamily
    (n : ℕ) (hnz : n ≠ 0) :
    HasLaw (ULift.up : Fin n → liftedIndicatorFamilySpace n)
      (liftedIndicatorFamilyMeasure n hnz)
      (indicatorFamilyLaw n hnz : Measure (Fin n)) := by
  -- Proof comment: the lifted measure was defined as the pushforward along `ULift.up`.
  exact ⟨measurable_up.aemeasurable, rfl⟩

/-- Helper for Exercise 12.1.5: the lifted Bool witness remains exchangeable under the lifted
measure. -/
private theorem uliftIndicatorBoolFamilyIsExchangeable
    (n : ℕ) (hnz : n ≠ 0) :
    IsExchangeable (liftedIndicatorBoolFamily n)
      (liftedIndicatorFamilyMeasure n hnz) := by
  -- Proof comment: pull back the base exchangeable family along `ULift.down`.
  simpa [liftedIndicatorBoolFamily] using
    isExchangeable_comp_hasLaw (indicatorBoolFamily_isExchangeable n hnz)
      (uliftDownHasLawIndicatorFamily n hnz)

/-- Helper for Exercise 12.1.5: an infinite extension of the lifted witness would pull back to an
infinite extension of the base witness. -/
private theorem uliftIndicatorBoolFamilyHasNoInfiniteExchangeableExtension
    (n : ℕ) (hn : 1 < n) (hnz : n ≠ 0) :
    ¬ HasInfiniteExchangeableExtension (liftedIndicatorBoolFamily n)
      (liftedIndicatorFamilyMeasure n hnz) := by
  intro hExt
  have hBaseExt :
      HasInfiniteExchangeableExtension (indicatorBoolFamily n)
        (indicatorFamilyLaw n hnz : Measure (Fin n)) := by
    -- Proof comment: compose the hypothetical lifted extension with `ULift.up` to recover an
    -- extension on the original finite sample space.
    simpa [liftedIndicatorBoolFamily] using
      hasInfiniteExchangeableExtension_comp_hasLaw hExt
        (uliftUpHasLawIndicatorFamily n hnz)
  exact indicatorBoolFamily_hasNoInfiniteExchangeableExtension n hn hnz hBaseExt

-- Proof sketch: restrict an infinite exchangeable extension to its first `n` coordinates via the
-- chapter-owner reindexing lemma `IsExchangeable.comp_embedding`.
/-- Any finite family admitting an infinite exchangeable extension is exchangeable. -/
theorem HasInfiniteExchangeableExtension.isExchangeable {n : ℕ}
    {X : Fin n → Ω → S} {μ : Measure Ω} (hX : HasInfiniteExchangeableExtension X μ) :
    IsExchangeable X μ := by
  rcases hX with ⟨Y, hY, rfl⟩
  simpa using hY.comp_embedding Fin.valEmbedding

-- Proof sketch: use the classical sampling-without-replacement example, for instance the
-- indicators of the unique marked element in a uniformly chosen point of `Fin n`; this family is
-- exchangeable, but de Finetti's theorem rules out any infinite exchangeable extension when
-- `n ≥ 2`.
/-- Exercise 12.1.5: for every `n ≥ 2`, there exists an exchangeable family
`X₁, …, Xₙ` that does not extend to any infinite exchangeable sequence on the same probability
space. -/
theorem exists_exchangeable_family_without_infinite_extension {n : ℕ} (hn : 1 < n) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ)
      (X : Fin n → Ω → Bool),
      IsExchangeable X μ ∧ ¬ HasInfiniteExchangeableExtension X μ := by
  have hnz : n ≠ 0 := by
    omega
  -- Proof comment: package the finite one-hot witness on a lifted copy of `Fin n`, and delegate
  -- exchangeability plus nonextendability to the dedicated transport helpers above.
  refine ⟨liftedIndicatorFamilySpace n, inferInstance,
    liftedIndicatorFamilyMeasure n hnz,
    liftedIndicatorFamilyMeasure_isProbabilityMeasure n hnz,
    liftedIndicatorBoolFamily n,
    uliftIndicatorBoolFamilyIsExchangeable n hnz,
    uliftIndicatorBoolFamilyHasNoInfiniteExchangeableExtension n hn hnz⟩
