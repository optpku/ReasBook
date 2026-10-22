/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The Bernoulli sequence space `{0,1}^ℕ`, modeled as `ℕ → Bool`. -/
abbrev BernoulliSequence := ℕ → Bool

/-- Helper for Exercise 7.4.1: the binary-expansion map `Real.fromBinary` is measurable. -/
theorem measurable_fromBinary :
    Measurable (Real.fromBinary : BernoulliSequence → unitInterval) :=
  Real.fromBinary_continuous.measurable

/-- Helper for Exercise 7.4.1: the canonical binary digits of a point of `[0,1]`, using the
constant-one expansion at the endpoint `1`. -/
noncomputable def canonicalBinaryDigits (x : unitInterval) : BernoulliSequence :=
  if (x : ℝ) = 1 then
    fun _ ↦ true
  else
    fun n ↦ finTwoEquiv (Real.digits (x : ℝ) 2 n)

/-- A binary digit is turned into the corresponding base-four digit `0` or `3`. -/
private def duplicatedBaseFourDigit (b : Bool) : Fin 4 :=
  cond b 3 0

/-- The base-four expansion obtained by replacing binary digits with `0` and `3`. -/
private noncomputable def duplicatedBaseFourMap (ω : BernoulliSequence) : unitInterval :=
  ⟨Real.ofDigits fun n ↦ duplicatedBaseFourDigit (ω n),
    ⟨Real.ofDigits_nonneg _, Real.ofDigits_le_one _⟩⟩

/-- The textbook binary digits on `[0,1]`: at positive dyadic rationals below `1`, replace the
terminating-zero expansion `...1000` by the equivalent eventually-one expansion `...0111`. -/
private noncomputable def textbookBinaryDigits (x : unitInterval) : BernoulliSequence :=
  let ω := canonicalBinaryDigits x
  if hω : ∃ N, 0 < N ∧ ω (N - 1) = true ∧ ∀ n ≥ N, ω n = false then
    let N := Nat.find hω
    fun n ↦ if n + 1 < N then ω n else if n + 1 = N then false else true
  else
    ω

/-- Helper for Exercise 7.4.1: the map `F : [0,1] → [0,1]` obtained by duplicating the textbook
binary digits of `x` into base-four digits `0` and `3`, using the eventually-one expansion at
dyadic rationals below `1`. -/
noncomputable def dyadicDuplicationMap (x : unitInterval) : unitInterval :=
  duplicatedBaseFourMap (textbookBinaryDigits x)

/-- The image measure of the uniform distribution on `[0,1]` under `dyadicDuplicationMap`. -/
noncomputable def dyadicDuplicationMeasure : Measure ℝ :=
  Measure.map (fun x : unitInterval ↦ (dyadicDuplicationMap x : ℝ)) volume

/-- Helper for Exercise 7.4.1: the measurable map obtained by duplicating the canonical binary
digits of a point of `[0,1]`. -/
private noncomputable def canonicalDyadicDuplicationMap (x : unitInterval) : unitInterval :=
  duplicatedBaseFourMap (canonicalBinaryDigits x)

/-- Helper for Exercise 7.4.1: the exceptional set where the textbook binary digits replace the
terminating-zero canonical expansion by the eventually-one expansion. -/
private def textbookCorrectionSet : Set unitInterval :=
  {x | ∃ N, 0 < N ∧ canonicalBinaryDigits x (N - 1) = true ∧
      ∀ n ≥ N, canonicalBinaryDigits x n = false}

/-- Helper for Exercise 7.4.1: the base-four pre-Cantor approximants keeping only the leftmost and
rightmost quarters at each stage. -/
private def baseFourPreCantorSet : ℕ → Set ℝ
  | 0 => Set.Icc 0 1
  | n + 1 => (· / 4) '' baseFourPreCantorSet n ∪ (fun x ↦ (3 + x) / 4) '' baseFourPreCantorSet n

/-- Helper for Exercise 7.4.1: the base-four Cantor-type set whose digits are only `0` or `3`. -/
private def baseFourCantorSet : Set ℝ :=
  ⋂ n, baseFourPreCantorSet n

/-- Helper for Exercise 7.4.1: each canonical binary digit is measurable as a function on
`[0,1]`. -/
private theorem measurable_canonicalBinaryDigitsCoord (n : ℕ) :
    Measurable (fun x : unitInterval ↦ canonicalBinaryDigits x n) := by
  have hs : MeasurableSet {x : unitInterval | (x : ℝ) = 1} := by
    exact (measurable_subtype_coe : Measurable (fun x : unitInterval ↦ (x : ℝ)))
      (measurableSet_singleton (1 : ℝ))
  have hfloor : Measurable (fun x : unitInterval ↦ ⌊(x : ℝ) * 2 ^ (n + 1)⌋₊) := by
    exact (measurable_subtype_coe.mul measurable_const).nat_floor
  have hdigitsFin : Measurable (fun x : unitInterval ↦ Real.digits (x : ℝ) 2 n) := by
    simpa [Real.digits] using (Measurable.of_discrete (f := Fin.ofNat 2)).comp hfloor
  have hdigitsBool :
      Measurable (fun x : unitInterval ↦ finTwoEquiv (Real.digits (x : ℝ) 2 n)) := by
    exact (Measurable.of_discrete (f := finTwoEquiv)).comp hdigitsFin
  have hcoord :
      (fun x : unitInterval ↦ canonicalBinaryDigits x n) =
        fun x : unitInterval ↦
          if (x : ℝ) = 1 then true else finTwoEquiv (Real.digits (x : ℝ) 2 n) := by
    funext x
    by_cases hx : (x : ℝ) = 1 <;> simp [canonicalBinaryDigits, hx]
  rw [hcoord]
  exact Measurable.ite hs measurable_const hdigitsBool

/-- Helper for Exercise 7.4.1: the coordinate maps of the canonical binary digit function are
measurable, hence the sequence-valued map itself is measurable. -/
private theorem measurable_canonicalBinaryDigits :
    Measurable (canonicalBinaryDigits : unitInterval → BernoulliSequence) := by
  -- Proof comment: product measurability reduces to the coordinate maps.
  exact measurable_pi_lambda _ measurable_canonicalBinaryDigitsCoord

/-- Helper for Exercise 7.4.1: the canonical duplicated-digit map is measurable because it is the
continuous `Real.ofDigits` construction applied to a measurable digit sequence. -/
private theorem measurable_canonicalDyadicDuplicationReal :
    Measurable (fun x : unitInterval ↦ (canonicalDyadicDuplicationMap x : ℝ)) := by
  -- Proof comment: first build the measurable base-four digit sequence, then compose with
  -- `Real.ofDigits`.
  change Measurable (fun x : unitInterval ↦
    Real.ofDigits fun n ↦ duplicatedBaseFourDigit (canonicalBinaryDigits x n))
  refine Real.continuous_ofDigits.measurable.comp <| measurable_pi_lambda _ fun n ↦ ?_
  exact (measurable_of_finite (duplicatedBaseFourDigit : Bool → Fin 4)).comp
    ((measurable_pi_apply n).comp measurable_canonicalBinaryDigits)

/-- Helper for Exercise 7.4.1: the canonical binary digits reconstruct the original point of
`[0,1]`. -/
private theorem fromBinary_canonicalBinaryDigits (x : unitInterval) :
    Real.fromBinary (canonicalBinaryDigits x) = x := by
  -- Proof comment: split between the endpoint `1`, where the canonical digits are all `true`,
  -- and the interior, where `Real.digits` already gives the canonical binary expansion.
  apply Subtype.ext
  change
    Real.ofDigits
        ((Homeomorph.piCongrRight fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
          (canonicalBinaryDigits x)) =
      (x : ℝ)
  by_cases hx : (x : ℝ) = 1
  · -- Proof comment: the endpoint branch is exactly the binary identity `0.111... = 1`.
    have hdigits :
        ((Homeomorph.piCongrRight fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
            (canonicalBinaryDigits x)) =
          fun _ ↦ (1 : Fin 2) := by
      funext n
      simp [Homeomorph.piCongrRight, Equiv.piCongrRight, canonicalBinaryDigits, hx]
      rfl
    rw [hdigits]
    simpa [hx] using Real.ofDigits_const_last_eq_one' (b := 2) (by norm_num)
  · -- Proof comment: away from `1`, the canonical digits agree with `Real.digits x 2`.
    have hxIco : (x : ℝ) ∈ Set.Ico 0 1 := by
      refine ⟨x.2.1, lt_of_le_of_ne x.2.2 hx⟩
    have hdigits :
        ((Homeomorph.piCongrRight fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
            (canonicalBinaryDigits x)) =
          fun n ↦ Real.digits (x : ℝ) 2 n := by
      funext n
      change finTwoEquiv.symm (canonicalBinaryDigits x n) = Real.digits (x : ℝ) 2 n
      simp [canonicalBinaryDigits, hx]
    rw [hdigits]
    exact Real.ofDigits_digits (b := 2) (by norm_num) hxIco

/-- Helper for Exercise 7.4.1: replacing a terminating binary expansion `...1000` by the
equivalent eventually-one expansion `...0111` does not change the represented real number. -/
private theorem fromBinary_replace_eventuallyZero (ω : BernoulliSequence) (K : ℕ)
    (hK : ω K = true) (htail : ∀ n > K, ω n = false) :
    Real.fromBinary (fun n ↦ if n < K then ω n else if n = K then false else true) =
      Real.fromBinary ω := by
  let η : BernoulliSequence := fun n ↦ if n < K then ω n else if n = K then false else true
  -- Proof comment: compare the two binary expansions after splitting off the first `K` digits.
  apply Subtype.ext
  change Real.ofDigits (fun n ↦ cond (η n) (1 : Fin 2) 0) =
    Real.ofDigits (fun n ↦ cond (ω n) (1 : Fin 2) 0)
  rw [Real.ofDigits_eq_sum_add_ofDigits (fun n ↦ cond (η n) (1 : Fin 2) 0) K,
    Real.ofDigits_eq_sum_add_ofDigits (fun n ↦ cond (ω n) (1 : Fin 2) 0) K]
  have hprefix :
      ∑ i ∈ Finset.range K, Real.ofDigitsTerm (fun n ↦ cond (η n) (1 : Fin 2) 0) i =
        ∑ i ∈ Finset.range K, Real.ofDigitsTerm (fun n ↦ cond (ω n) (1 : Fin 2) 0) i := by
    -- Proof comment: before the altered digit, the two binary strings are identical.
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i < K := Finset.mem_range.mp hi
    simp [Real.ofDigitsTerm, η, hi']
  rw [hprefix]
  have horigShape :
      (fun i ↦ cond (ω (i + K)) (1 : Fin 2) 0) = fun i ↦ if i = 0 then (1 : Fin 2) else 0 := by
    -- Proof comment: the original tail is `1000...`.
    funext i
    cases i with
    | zero =>
        simp [hK]
    | succ j =>
        have hfalse : ω (Nat.succ j + K) = false := by
          apply htail
          omega
        simp [hfalse]
  have hmodShape :
      (fun i ↦ cond (η (i + K)) (1 : Fin 2) 0) = fun i ↦ if i = 0 then (0 : Fin 2) else 1 := by
    -- Proof comment: the modified tail is `0111...`.
    funext i
    cases i with
    | zero =>
        simp [η]
    | succ j =>
      have hlt : ¬ Nat.succ j + K < K := by
        omega
      simp [η, hlt]
  have horigHalf :
      Real.ofDigits (fun i ↦ if i = 0 then (1 : Fin 2) else 0) = (1 : ℝ) / 2 := by
    -- Proof comment: `1000...` is the binary expansion of `1 / 2`.
    rw [Real.ofDigits_eq_sum_add_ofDigits (fun i ↦ if i = 0 then (1 : Fin 2) else 0) 1]
    simp [Real.ofDigits, Real.ofDigitsTerm]
  have hmodHalf :
      Real.ofDigits (fun i ↦ if i = 0 then (0 : Fin 2) else 1) = (1 : ℝ) / 2 := by
    -- Proof comment: `0111...` is the same number by `0.111... = 1`.
    have hones : Real.ofDigits (fun _ ↦ (1 : Fin 2)) = 1 := by
      exact Real.ofDigits_const_last_eq_one' (b := 2) (by norm_num)
    rw [Real.ofDigits_eq_sum_add_ofDigits (fun i ↦ if i = 0 then (0 : Fin 2) else 1) 1]
    simp [Real.ofDigitsTerm, hones]
  rw [hmodShape, horigShape, hmodHalf, horigHalf]

/-- Helper for Exercise 7.4.1: the textbook binary digits still decode to the original point. -/
private theorem fromBinary_textbookBinaryDigits (x : unitInterval) :
    Real.fromBinary (textbookBinaryDigits x) = x := by
  -- Route correction: first isolate the `...1000 = ...0111` replacement, then decode.
  by_cases hω : ∃ N, 0 < N ∧ canonicalBinaryDigits x (N - 1) = true ∧
      ∀ n ≥ N, canonicalBinaryDigits x n = false
  · let N := Nat.find hω
    have hN : 0 < N := (Nat.find_spec hω).1
    have hdigit : canonicalBinaryDigits x (N - 1) = true := (Nat.find_spec hω).2.1
    have htail : ∀ n > N - 1, canonicalBinaryDigits x n = false := by
      -- Proof comment: every digit strictly after the last `1` vanishes in the terminating tail.
      intro n hn
      exact (Nat.find_spec hω).2.2 n (by omega)
    have hrewrite :
        (fun n ↦
          if n + 1 < N then canonicalBinaryDigits x n else if n + 1 = N then false else true) =
          fun n ↦
            if n < N - 1 then canonicalBinaryDigits x n else if n = N - 1 then false else true := by
      -- Proof comment: rewrite the textbook branch into the tail-replacement normal form.
      funext n
      have hltEq : (n + 1 < N) = (n < N - 1) := by
        apply propext
        omega
      have heqEq : (n + 1 = N) = (n = N - 1) := by
        apply propext
        omega
      simp [hltEq, heqEq]
    -- Proof comment: after the normal-form rewrite, apply the standalone tail-replacement lemma.
    have hbranch :
        textbookBinaryDigits x =
          fun n ↦
            if n + 1 < N then canonicalBinaryDigits x n else if n + 1 = N then false else true := by
      simp [textbookBinaryDigits, hω, N]
    rw [hbranch, hrewrite]
    rw [fromBinary_replace_eventuallyZero (ω := canonicalBinaryDigits x) (K := N - 1) hdigit htail]
    exact fromBinary_canonicalBinaryDigits x
  · -- Proof comment: outside the correction set, the textbook digits are the canonical digits.
    simp [textbookBinaryDigits, hω, fromBinary_canonicalBinaryDigits]

/-- Helper for Exercise 7.4.1: sequences that are eventually zero form a countable subset of
`BernoulliSequence`. -/
private theorem countable_eventuallyFalseSet :
    ({ω : BernoulliSequence | ∃ N, ∀ n ≥ N, ω n = false} : Set BernoulliSequence).Countable := by
  let prefixExtension : ∀ N : ℕ, (Fin N → Bool) → BernoulliSequence :=
    fun N a n ↦ if hn : n < N then a ⟨n, hn⟩ else false
  have hunion :
      ({ω : BernoulliSequence | ∃ N, ∀ n ≥ N, ω n = false} : Set BernoulliSequence) =
        ⋃ N : ℕ, Set.range (prefixExtension N) := by
    -- Proof comment: an eventually-false sequence is determined by a cutoff and its finite prefix.
    ext ω
    constructor
    · intro hω
      rcases hω with ⟨N, hN⟩
      refine Set.mem_iUnion.2 ⟨N, Set.mem_range.2 ?_⟩
      refine ⟨fun i ↦ ω i, ?_⟩
      funext n
      by_cases hn : n < N
      · simp [prefixExtension, hn]
      · simp [prefixExtension, hn, hN n (Nat.not_lt.mp hn)]
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨N, hN⟩
      rcases Set.mem_range.1 hN with ⟨a, rfl⟩
      refine ⟨N, ?_⟩
      intro n hn
      simp [prefixExtension, Nat.not_lt.mpr hn]
  rw [hunion]
  refine Set.countable_iUnion fun N ↦ ?_
  exact Set.countable_range (prefixExtension N)

/-- Helper for Exercise 7.4.1: the correction set is countable, hence `volume`-null. -/
private theorem countable_textbookCorrectionSet :
    textbookCorrectionSet.Countable := by
  -- Proof comment: the correction set injects into the countable family of eventually-false
  -- canonical digit sequences.
  refine Set.countable_of_injective_of_countable_image (f := canonicalBinaryDigits) ?_ ?_
  · intro x hx y hy hxy
    have hdecode := congrArg Real.fromBinary hxy
    simpa [fromBinary_canonicalBinaryDigits x, fromBinary_canonicalBinaryDigits y] using hdecode
  · refine countable_eventuallyFalseSet.mono ?_
    intro ω hω
    rcases hω with ⟨x, hx, rfl⟩
    rcases hx with ⟨N, _, _, htail⟩
    exact ⟨N, htail⟩

/-- Helper for Exercise 7.4.1: the dyadic duplication map is almost everywhere equal to the
measurable canonical map, so it is `AEMeasurable`. -/
private theorem aemeasurable_dyadicDuplicationReal :
    AEMeasurable (fun x : unitInterval ↦ (dyadicDuplicationMap x : ℝ)) volume := by
  -- Proof comment: the textbook correction changes the canonical map only on the countable set of
  -- dyadic rationals with terminating binary expansion.
  refine measurable_canonicalDyadicDuplicationReal.aemeasurable.congr ?_
  filter_upwards [countable_textbookCorrectionSet.ae_notMem volume] with x hx
  have hcanon :
      textbookBinaryDigits x = canonicalBinaryDigits x := by
    have : ¬ ∃ N, 0 < N ∧ canonicalBinaryDigits x (N - 1) = true ∧
        ∀ n ≥ N, canonicalBinaryDigits x n = false := by
      simpa [textbookCorrectionSet] using hx
    simp [textbookBinaryDigits, this]
  simp [dyadicDuplicationMap, canonicalDyadicDuplicationMap, hcanon]

/-- Helper for Exercise 7.4.1: the base-four digit duplication is a rescaled Cantor function. -/
private theorem duplicatedBaseFourMap_eq_cantorFunction (ω : BernoulliSequence) :
    (duplicatedBaseFourMap ω : ℝ) = (3 / 4 : ℝ) * Cardinal.cantorFunction (1 / 4) ω := by
  -- Proof comment: both sides are the same series after converting the digits `0,3` to
  -- the Boolean coefficients in `Cardinal.cantorFunction`.
  change Real.ofDigits (fun n ↦ duplicatedBaseFourDigit (ω n)) =
    (3 / 4 : ℝ) * Cardinal.cantorFunction (1 / 4) ω
  rw [Real.ofDigits, Cardinal.cantorFunction]
  conv_rhs => rw [← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  cases h : ω n
  · rw [Cardinal.cantorFunctionAux_false h]
    simp [Real.ofDigitsTerm, duplicatedBaseFourDigit, h]
  · rw [Cardinal.cantorFunctionAux_true h]
    have hpown : ((4 : ℝ) ^ n)⁻¹ = (1 / 4 : ℝ) ^ n := by
      simp [one_div, inv_pow]
    calc
      Real.ofDigitsTerm (fun k ↦ duplicatedBaseFourDigit (ω k)) n =
          (3 : ℝ) * ((4 : ℝ) ^ (n + 1))⁻¹ := by
            simp [Real.ofDigitsTerm, duplicatedBaseFourDigit, h]
      _ = (3 / 4 : ℝ) * ((4 : ℝ) ^ n)⁻¹ := by
            rw [pow_succ']
            ring
      _ = (3 / 4 : ℝ) * (1 / 4 : ℝ) ^ n := by
            rw [hpown]

/-- Helper for Exercise 7.4.1: the duplicated base-four encoding of a Bernoulli sequence is
injective. -/
private theorem duplicatedBaseFourMap_injective :
    Function.Injective fun ω : BernoulliSequence ↦ (duplicatedBaseFourMap ω : ℝ) := by
  -- Proof comment: after the Cantor-function normalization, injectivity is the standard
  -- `0 < c < 1 / 2` injectivity theorem at `c = 1 / 4`.
  intro ω η hωη
  have hcantor :
      Cardinal.cantorFunction (1 / 4) ω = Cardinal.cantorFunction (1 / 4) η := by
    apply mul_left_cancel₀ (show (3 / 4 : ℝ) ≠ 0 by norm_num)
    simpa [duplicatedBaseFourMap_eq_cantorFunction] using hωη
  exact Cardinal.cantorFunction_injective (c := 1 / 4) (by norm_num) (by norm_num) hcantor

/-- Helper for Exercise 7.4.1: `dyadicDuplicationMap` is injective because the textbook digits
reconstruct the source point. -/
private theorem dyadicDuplicationMap_injective :
    Function.Injective dyadicDuplicationMap := by
  -- Proof comment: first recover the textbook digit sequence from the duplicated base-four value,
  -- then decode those digits back to the original point.
  intro x y hxy
  have hdigits : textbookBinaryDigits x = textbookBinaryDigits y := by
    apply duplicatedBaseFourMap_injective
    exact congrArg (fun z : unitInterval ↦ (z : ℝ)) hxy
  have hdecode := congrArg Real.fromBinary hdigits
  simpa [fromBinary_textbookBinaryDigits x, fromBinary_textbookBinaryDigits y] using hdecode

/-- `dyadicDuplicationMeasure` is the pushforward of the uniform measure on `[0,1]` under
`dyadicDuplicationMap`. -/
@[simp] theorem dyadicDuplicationMeasure_eq_map_dyadicDuplicationMap :
    dyadicDuplicationMeasure =
      Measure.map (fun x : unitInterval ↦ (dyadicDuplicationMap x : ℝ)) volume :=
  rfl

/-- Helper for Exercise 7.4.1: the Bernoulli realization used in this file is the pushforward of
`volume` under the canonical binary digit map. -/
noncomputable def fairBernoulliMeasure : Measure BernoulliSequence :=
  Measure.map canonicalBinaryDigits volume

/-- Helper for Exercise 7.4.1: pushing `fairBernoulliMeasure` forward through `Real.fromBinary`
recovers the uniform measure on `[0,1]`. -/
theorem map_fromBinary_fairBernoulliMeasure :
    Measure.map (Real.fromBinary : BernoulliSequence → unitInterval) fairBernoulliMeasure =
      volume := by
  calc
    Measure.map (Real.fromBinary : BernoulliSequence → unitInterval) fairBernoulliMeasure =
        Measure.map (Real.fromBinary ∘ canonicalBinaryDigits) volume := by
          rw [fairBernoulliMeasure,
            Measure.map_map measurable_fromBinary measurable_canonicalBinaryDigits]
    _ = Measure.map (fun x : unitInterval ↦ x) volume := by
          refine Measure.map_congr <| Filter.Eventually.of_forall ?_
          intro x
          exact fromBinary_canonicalBinaryDigits x
    _ = volume := by simp

/-- The canonical pushforward description of `dyadicDuplicationMeasure` agrees with the Bernoulli
realization `F(U)` from Chapter 1. -/
theorem dyadicDuplicationMeasure_eq_map_fromBinary :
    dyadicDuplicationMeasure =
      Measure.map (fun ω : BernoulliSequence ↦ (dyadicDuplicationMap (Real.fromBinary ω) : ℝ))
        fairBernoulliMeasure := by
  -- Proof comment: first rewrite `volume` as the pushforward of the fair Bernoulli measure under
  -- `Real.fromBinary`, then compose the maps using `map_map_of_aemeasurable`.
  rw [dyadicDuplicationMeasure, ← map_fromBinary_fairBernoulliMeasure]
  have houter :
      AEMeasurable (fun x : unitInterval ↦ (dyadicDuplicationMap x : ℝ))
        (Measure.map (Real.fromBinary : BernoulliSequence → unitInterval)
          fairBernoulliMeasure) := by
    simpa [map_fromBinary_fairBernoulliMeasure] using aemeasurable_dyadicDuplicationReal
  simpa [Function.comp] using
    AEMeasurable.map_map_of_aemeasurable houter measurable_fromBinary.aemeasurable

-- Proof sketch: identify the mass of a singleton with the probability of a single digit sequence;
-- the Bernoulli digit model has no dyadic ambiguity, so every singleton has measure `0`.
-- A monotone right-continuous cdf with no atoms is continuous.
/-- Helper for Exercise 7.4.1: the distribution function of the image measure is continuous. -/
theorem dyadicDuplicationMeasure_cdf_continuous :
    Continuous (cdf dyadicDuplicationMeasure) := by
  -- Proof comment: injectivity of the map shows that every singleton has zero mass, and a
  -- monotone right-continuous cdf with vanishing singleton masses is continuous.
  have hsingleton : ∀ y : ℝ, dyadicDuplicationMeasure {y} = 0 := by
    intro y
    rw [dyadicDuplicationMeasure]
    rw [Measure.map_apply_of_aemeasurable aemeasurable_dyadicDuplicationReal
      (measurableSet_singleton y)]
    by_cases hy : ∃ x : unitInterval, dyadicDuplicationMap x = y
    · rcases hy with ⟨x, rfl⟩
      have hpre :
          (fun z : unitInterval ↦ (dyadicDuplicationMap z : ℝ)) ⁻¹'
              ({(dyadicDuplicationMap x : ℝ)} : Set ℝ) =
            {x} := by
        ext z
        constructor
        · intro hz
          have hEq : dyadicDuplicationMap z = dyadicDuplicationMap x := by
            apply Subtype.ext
            simpa using hz
          exact dyadicDuplicationMap_injective hEq
        · intro hz
          rcases Set.mem_singleton_iff.mp hz with rfl
          simp
      rw [hpre]
      exact Set.Subsingleton.measure_zero Set.subsingleton_singleton volume
    · have hpre :
          (fun z : unitInterval ↦ (dyadicDuplicationMap z : ℝ)) ⁻¹' ({y} : Set ℝ) = ∅ := by
        ext z
        constructor
        · intro hz
          exact False.elim <| hy ⟨z, hz⟩
        · intro hz
          exact False.elim hz
      rw [hpre, measure_empty]
  have hleft :
      ∀ x : ℝ,
        Function.leftLim (cdf dyadicDuplicationMeasure) x = cdf dyadicDuplicationMeasure x := by
    intro x
    haveI : IsProbabilityMeasure dyadicDuplicationMeasure :=
      Measure.isProbabilityMeasure_map aemeasurable_dyadicDuplicationReal
    have hmeasure :
        (cdf dyadicDuplicationMeasure).measure {x} = 0 := by
      rw [ProbabilityTheory.measure_cdf]
      exact hsingleton x
    have hmono := ProbabilityTheory.monotone_cdf dyadicDuplicationMeasure
    have hle :
        Function.leftLim (cdf dyadicDuplicationMeasure) x ≤ cdf dyadicDuplicationMeasure x :=
      hmono.leftLim_le le_rfl
    have hnonpos :
        cdf dyadicDuplicationMeasure x - Function.leftLim (cdf dyadicDuplicationMeasure) x ≤
          0 := by
      rwa [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at hmeasure
    linarith
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hmono := ProbabilityTheory.monotone_cdf dyadicDuplicationMeasure
  rw [hmono.continuousAt_iff_leftLim_eq_rightLim, hleft x, StieltjesFunction.rightLim_eq]

/-- Helper for Exercise 7.4.1: every duplicated base-four digit is either `0` or `3`. -/
private theorem duplicatedBaseFourDigit_eq_zero_or_three (b : Bool) :
    duplicatedBaseFourDigit b = 0 ∨ duplicatedBaseFourDigit b = 3 := by
  -- Proof comment: unfold the Boolean branch and inspect the two possible digits.
  cases b <;> simp [duplicatedBaseFourDigit]

/-- Helper for Exercise 7.4.1: any base-four expansion using only digits `0` and `3` belongs to
the base-four Cantor set. -/
private theorem ofDigits_zero_three_sequence_mem_baseFourCantorSet {a : ℕ → Fin 4}
    (h : ∀ n, a n = 0 ∨ a n = 3) : Real.ofDigits a ∈ baseFourCantorSet := by
  -- Proof comment: at each stage, the first digit decides whether the point lies in the left or
  -- right quarter, and the tail remains a valid `0/3` expansion.
  simp only [baseFourCantorSet, Set.mem_iInter]
  intro i
  induction i generalizing a with
  | zero =>
      simp only [baseFourPreCantorSet, Set.mem_Icc]
      exact ⟨Real.ofDigits_nonneg a, Real.ofDigits_le_one a⟩
  | succ i ih =>
      simp only [baseFourPreCantorSet, Set.mem_union, Set.mem_image, ← exists_or]
      let tail : ℝ := Real.ofDigits (fun n ↦ a (n + 1))
      have htail : tail ∈ baseFourPreCantorSet i := by
        exact ih (fun n ↦ h (n + 1))
      have hsplit :
          Real.ofDigits a = (a 0 : ℝ) / 4 + tail / 4 := by
        -- Proof comment: split the base-four series into its first digit and the shifted tail.
        rw [Real.ofDigits_eq_sum_add_ofDigits a 1]
        simp [tail, Real.ofDigitsTerm]
        ring
      rcases h 0 with h0 | h0
      · refine ⟨tail, ?_⟩
        left
        refine ⟨htail, ?_⟩
        rw [hsplit, h0]
        norm_num
      · refine ⟨tail, ?_⟩
        right
        refine ⟨htail, ?_⟩
        rw [hsplit, h0]
        have hthree : (((3 : Fin 4) : ℝ)) = 3 := by
          norm_num
        rw [hthree]
        ring

/-- Helper for Exercise 7.4.1: every value of the duplicated-digit map lies in the base-four
Cantor set. -/
private theorem dyadicDuplicationMap_mem_baseFourCantorSet (x : unitInterval) :
    (dyadicDuplicationMap x : ℝ) ∈ baseFourCantorSet := by
  -- Proof comment: the textbook binary digits generate a base-four expansion with digits only
  -- `0` and `3`, so the generic membership lemma applies directly.
  refine ofDigits_zero_three_sequence_mem_baseFourCantorSet ?_
  intro n
  exact duplicatedBaseFourDigit_eq_zero_or_three (textbookBinaryDigits x n)

/-- Helper for Exercise 7.4.1: each successive base-four pre-Cantor stage is contained in the
previous one. -/
private theorem baseFourPreCantorSet_succ_subset (n : ℕ) :
    baseFourPreCantorSet (n + 1) ⊆ baseFourPreCantorSet n := by
  -- Proof comment: either quarter map lands back in the previous stage, and the base case lands
  -- in `[0,1]` by elementary interval arithmetic.
  intro x hx
  induction n generalizing x with
  | zero =>
      rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · rcases hy with ⟨hy0, hy1⟩
        constructor <;> nlinarith
      · rcases hy with ⟨hy0, hy1⟩
        constructor <;> nlinarith
  | succ n ih =>
      rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
      · exact Or.inl ⟨y, ih hy, rfl⟩
      · exact Or.inr ⟨y, ih hy, rfl⟩

/-- Helper for Exercise 7.4.1: the base-four pre-Cantor approximants form a decreasing sequence of
sets. -/
private theorem baseFourPreCantorSet_antitone : Antitone baseFourPreCantorSet := by
  -- Proof comment: the stagewise subset relation upgrades to antitonicity along `ℕ`.
  exact antitone_nat_of_succ_le baseFourPreCantorSet_succ_subset

/-- Helper for Exercise 7.4.1: the base-four Cantor set sits inside the unit interval. -/
private theorem baseFourCantorSet_subset_unitInterval :
    baseFourCantorSet ⊆ Set.Icc (0 : ℝ) 1 := by
  -- Proof comment: the intersection is contained in its zeroth approximant `[0,1]`.
  exact Set.iInter_subset _ 0

/-- Helper for Exercise 7.4.1: every base-four pre-Cantor stage is closed. -/
private theorem isClosed_baseFourPreCantorSet (n : ℕ) :
    IsClosed (baseFourPreCantorSet n) := by
  let f := Homeomorph.mulRight₀ (1 / 4 : ℝ) (by norm_num)
  let g := (Homeomorph.addRight (3 : ℝ)).trans f
  -- Proof comment: each stage is obtained from the previous one by two closed embeddings and a
  -- finite union.
  induction n with
  | zero =>
      simpa [baseFourPreCantorSet] using isClosed_Icc
  | succ n ih =>
      refine IsClosed.union ?_ ?_
      · simpa [f, div_eq_mul_inv] using
          f.isClosedEmbedding.isClosed_iff_image_isClosed.mp ih
      · simpa [g, f, div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using
          g.isClosedEmbedding.isClosed_iff_image_isClosed.mp ih

/-- Helper for Exercise 7.4.1: the base-four Cantor set is closed. -/
private theorem isClosed_baseFourCantorSet :
    IsClosed baseFourCantorSet := by
  -- Proof comment: closedness is preserved under countable intersections of the closed stages.
  simpa [baseFourCantorSet] using isClosed_iInter isClosed_baseFourPreCantorSet

/-- Helper for Exercise 7.4.1: the map `x ↦ x / 4` shrinks Lebesgue measure by a factor `1 / 4`
on images. -/
private theorem volume_image_div_four (s : Set ℝ) :
    volume ((fun x : ℝ ↦ x / 4) '' s) = ENNReal.ofReal (1 / 4 : ℝ) * volume s := by
  have hf : MeasurableEmbedding (fun x : ℝ ↦ x / 4) := by
    simpa [div_eq_mul_inv] using
      (Homeomorph.mulRight₀ (1 / 4 : ℝ) (by norm_num)).toMeasurableEquiv.measurableEmbedding
  have hmap :
      Measure.map (fun x : ℝ ↦ x / 4) volume = ENNReal.ofReal (4 : ℝ) • volume := by
    simpa [div_eq_mul_inv] using
      (Real.map_volume_mul_right (a := (1 / 4 : ℝ)) (by norm_num))
  have himage :
      ENNReal.ofReal (4 : ℝ) * volume ((fun x : ℝ ↦ x / 4) '' s) = volume s := by
    -- Proof comment: push forward `volume` through the quarter map, then invert the image using
    -- injectivity.
    calc
      ENNReal.ofReal (4 : ℝ) * volume ((fun x : ℝ ↦ x / 4) '' s) =
          Measure.map (fun x : ℝ ↦ x / 4) volume ((fun x : ℝ ↦ x / 4) '' s) := by
            rw [hmap]
            simp
      _ = volume s := by
            rw [hf.map_apply, Set.preimage_image_eq _ hf.injective]
  -- Proof comment: multiply by the inverse scaling factor to recover the image measure.
  have hscale : ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (4 : ℝ) = 1 := by
    rw [← ENNReal.ofReal_mul]
    · norm_num
    · positivity
  have hmul :
      ENNReal.ofReal (1 / 4 : ℝ) *
          (ENNReal.ofReal (4 : ℝ) * volume ((fun x : ℝ ↦ x / 4) '' s)) =
        ENNReal.ofReal (1 / 4 : ℝ) * volume s := by
    exact congrArg (fun t ↦ ENNReal.ofReal (1 / 4 : ℝ) * t) himage
  calc
    volume ((fun x : ℝ ↦ x / 4) '' s) =
        (ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (4 : ℝ)) *
          volume ((fun x : ℝ ↦ x / 4) '' s) := by
            rw [hscale, one_mul]
    _ = ENNReal.ofReal (1 / 4 : ℝ) *
          (ENNReal.ofReal (4 : ℝ) * volume ((fun x : ℝ ↦ x / 4) '' s)) := by
            rw [mul_assoc]
    _ = ENNReal.ofReal (1 / 4 : ℝ) * volume s := hmul

/-- Helper for Exercise 7.4.1: translation by `3` preserves Lebesgue measure on images. -/
private theorem volume_image_add_three (s : Set ℝ) :
    volume ((fun x : ℝ ↦ x + 3) '' s) = volume s := by
  have hf : MeasurableEmbedding (fun x : ℝ ↦ x + 3) := by
    simpa using (Homeomorph.addRight (3 : ℝ)).toMeasurableEquiv.measurableEmbedding
  -- Proof comment: use translation invariance of Lebesgue measure and invert the image through
  -- the measurable embedding.
  calc
    volume ((fun x : ℝ ↦ x + 3) '' s) =
        Measure.map (fun x : ℝ ↦ x + 3) volume ((fun x : ℝ ↦ x + 3) '' s) := by
          rw [map_add_right_eq_self volume (3 : ℝ)]
    _ = volume s := by
          rw [hf.map_apply, Set.preimage_image_eq _ hf.injective]

/-- Helper for Exercise 7.4.1: the affine branch `x ↦ (3 + x) / 4` also shrinks Lebesgue measure
by a factor `1 / 4` on images. -/
private theorem volume_image_addThree_div_four (s : Set ℝ) :
    volume ((fun x : ℝ ↦ (3 + x) / 4) '' s) = ENNReal.ofReal (1 / 4 : ℝ) * volume s := by
  have himage :
      (fun x : ℝ ↦ (3 + x) / 4) '' s =
        (fun x : ℝ ↦ x / 4) '' ((fun x : ℝ ↦ x + 3) '' s) := by
    -- Proof comment: factor the affine branch as translation by `3` followed by division by `4`.
    simpa [Function.comp, add_comm, add_left_comm, add_assoc, div_eq_mul_inv, mul_add, add_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      (Set.image_image (fun x : ℝ ↦ x / 4) (fun x : ℝ ↦ x + 3) s).symm
  -- Proof comment: combine the translation invariance with the quarter-scaling lemma.
  rw [himage, volume_image_div_four, volume_image_add_three]

/-- Helper for Exercise 7.4.1: the stagewise base-four approximants have exponentially decaying
Lebesgue measure. -/
private theorem baseFourPreCantorSet_volume_le_pow (n : ℕ) :
    volume (baseFourPreCantorSet n) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  induction n with
  | zero =>
      -- Proof comment: the initial stage is the whole unit interval and has measure `1`.
      simp [baseFourPreCantorSet]
  | succ n ih =>
      -- Proof comment: each stage is a union of two quarter-sized affine images of the previous
      -- stage, so its measure is at most half of the previous measure.
      calc
        volume (baseFourPreCantorSet (n + 1))
            ≤ volume ((fun x : ℝ ↦ x / 4) '' baseFourPreCantorSet n) +
                volume ((fun x : ℝ ↦ (3 + x) / 4) '' baseFourPreCantorSet n) := by
                  simpa [baseFourPreCantorSet] using
                    measure_union_le ((fun x : ℝ ↦ x / 4) '' baseFourPreCantorSet n)
                      ((fun x : ℝ ↦ (3 + x) / 4) '' baseFourPreCantorSet n)
        _ = ENNReal.ofReal (1 / 4 : ℝ) * volume (baseFourPreCantorSet n) +
              ENNReal.ofReal (1 / 4 : ℝ) * volume (baseFourPreCantorSet n) := by
                rw [volume_image_div_four, volume_image_addThree_div_four]
        _ = ENNReal.ofReal (1 / 2 : ℝ) * volume (baseFourPreCantorSet n) := by
              rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
              norm_num
        _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
              gcongr
        _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)) := by
              simp [pow_succ, ENNReal.ofReal_mul, mul_comm]

/-- Helper for Exercise 7.4.1: the base-four Cantor set has Lebesgue measure zero. -/
private theorem volume_baseFourCantorSet_zero :
    volume baseFourCantorSet = 0 := by
  have hs : ∀ n, NullMeasurableSet (baseFourPreCantorSet n) volume := fun n ↦
    (isClosed_baseFourPreCantorSet n).nullMeasurableSet
  have h_tendsto_measure :
      Filter.Tendsto (fun n : ℕ ↦ volume (baseFourPreCantorSet n)) Filter.atTop
        (𝓝 (volume baseFourCantorSet)) := by
    -- Proof comment: the decreasing closed approximants converge in measure to their
    -- intersection.
    simpa [baseFourCantorSet] using
      tendsto_measure_iInter_atTop hs baseFourPreCantorSet_antitone
        ⟨0, by
          rw [baseFourPreCantorSet, Real.volume_Icc]
          norm_num⟩
  have h_tendsto_zero :
      Filter.Tendsto (fun n : ℕ ↦ ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) Filter.atTop (𝓝 0) := by
    -- Proof comment: the geometric upper bound tends to zero.
    have hpow :
        Filter.Tendsto (fun n : ℕ ↦ (ENNReal.ofReal (1 / 2 : ℝ)) ^ n) Filter.atTop (𝓝 0) := by
      exact ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
        (r := ENNReal.ofReal (1 / 2 : ℝ)) (by norm_num)
    convert hpow using 1
    ext n
    rw [ENNReal.ofReal_pow]
    positivity
  have h_measure_zero :
      Filter.Tendsto (fun n : ℕ ↦ volume (baseFourPreCantorSet n)) Filter.atTop (𝓝 0) := by
    -- Proof comment: squeeze the stage measures between `0` and the geometric bound.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_tendsto_zero ?_ ?_
    · intro n
      exact bot_le
    · intro n
      exact baseFourPreCantorSet_volume_le_pow n
  exact tendsto_nhds_unique h_tendsto_measure h_measure_zero

-- Proof sketch: the image of `dyadicDuplicationMap` is contained in the classical Cantor-type set
-- of numbers whose base-four digits are only `0` or `3`; that set has Lebesgue measure `0`, while
-- the pushforward measure assigns it full mass, yielding mutual singularity.
/-- Exercise 7.4.1: the image measure is singular with respect to Lebesgue measure on `(0,1]`. -/
theorem dyadicDuplicationMeasure_mutuallySingular_restrict_volume :
    dyadicDuplicationMeasure ⟂ₘ volume.restrict (Set.Ioc (0 : ℝ) 1) := by
  -- Proof comment: use the complement of the base-four Cantor set as the null set for the
  -- pushforward measure and the Cantor set itself as the null set for the restricted volume.
  have h_support :
      dyadicDuplicationMeasure (baseFourCantorSetᶜ) = 0 := by
    rw [dyadicDuplicationMeasure]
    rw [Measure.map_apply_of_aemeasurable aemeasurable_dyadicDuplicationReal
      isClosed_baseFourCantorSet.isOpen_compl.measurableSet]
    have hpre :
        (fun x : unitInterval ↦ (dyadicDuplicationMap x : ℝ)) ⁻¹' baseFourCantorSetᶜ = ∅ := by
      ext x
      constructor
      · intro hx
        exact False.elim <| hx (dyadicDuplicationMap_mem_baseFourCantorSet x)
      · intro hx
        exact False.elim hx
    rw [hpre, measure_empty]
  have h_restrict :
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) baseFourCantorSet = 0 := by
    -- Proof comment: the Cantor set is Lebesgue-null, so its restriction to `(0,1]` is null as
    -- well.
    rw [Measure.restrict_apply isClosed_baseFourCantorSet.measurableSet]
    exact measure_mono_null Set.inter_subset_left volume_baseFourCantorSet_zero
  refine Measure.MutuallySingular.mk h_support h_restrict ?_
  intro x hx
  by_cases hmem : x ∈ baseFourCantorSet
  · exact Or.inr hmem
  · exact Or.inl hmem

end
