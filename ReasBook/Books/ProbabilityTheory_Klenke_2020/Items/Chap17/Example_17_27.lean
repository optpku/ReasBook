/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Exercise_2_2_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Example_5_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Exercise_8_2_8

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The cylinder event that the first `n` weighted-urn draws match the prescribed Boolean prefix
`x`, with `true` encoding black and `false` encoding red. -/
def weightedUrnPrefixEvent (X : ℕ → Ω → Bool) {n : ℕ} (x : Fin n → Bool) : Set Ω :=
  {ω | ∀ i : Fin n, X i ω = x i}

/-- The number of black draws in the Boolean prefix `x`. -/
def blackPrefixCount {n : ℕ} (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ x i = true).card

/-- Helper for Example 17.27: a prefix cylinder is measurable once each coordinate of the
underlying Boolean process is measurable. -/
theorem measurableSet_weightedUrnPrefixEvent
    {X : ℕ → Ω → Bool} (hX : ∀ n : ℕ, Measurable (X n)) {n : ℕ} (x : Fin n → Bool) :
    MeasurableSet (weightedUrnPrefixEvent X x) := by
  -- Proof comment: rewrite the prefix cylinder as the intersection of the measurable coordinate
  -- fibers `{ω | X i ω = x i}`.
  have hset :
      {ω | ∀ i : Fin n, X i ω = x i} = ⋂ i : Fin n, {ω | X i ω = x i} := by
    ext ω
    simp
  rw [weightedUrnPrefixEvent, hset]
  exact MeasurableSet.iInter fun i : Fin n ↦
    (hX i) (measurableSet_singleton (x i))

omit [MeasurableSpace Ω] in
/-- Helper for Example 17.27: adjoining one last Boolean value to a prefix cylinder means
intersecting with the corresponding next-coordinate event. -/
theorem weightedUrnPrefixEvent_snoc
    {X : ℕ → Ω → Bool} {n : ℕ} (x : Fin n → Bool) (b : Bool) :
    weightedUrnPrefixEvent X (Fin.snoc x b) =
      weightedUrnPrefixEvent X x ∩ {ω | X n ω = b} := by
  -- Proof comment: split the `Fin (n + 1)` quantifier into the old prefix coordinates and the
  -- last coordinate.
  ext ω
  simp [weightedUrnPrefixEvent, Fin.forall_iff_castSucc, and_comm]

/-- Helper for Example 17.27: the black-prefix count is the sum of the `0/1` indicators of the
black entries in the prefix. -/
theorem blackPrefixCount_eq_sum_indicator
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount x = ∑ i : Fin n, if x i = true then 1 else 0 := by
  classical
  -- Proof comment: filtering `Finset.univ` by the black coordinates is equivalent to summing the
  -- associated indicator function.
  simp [blackPrefixCount]

/-- Helper for Example 17.27: appending a black draw increments the black-prefix count by `1`. -/
theorem blackPrefixCount_snoc_true
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount (Fin.snoc x true) = blackPrefixCount x + 1 := by
  -- Proof comment: split the successor-index sum into the old coordinates and the last one.
  rw [blackPrefixCount_eq_sum_indicator, blackPrefixCount_eq_sum_indicator, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, add_comm]

/-- Helper for Example 17.27: appending a red draw leaves the black-prefix count unchanged. -/
theorem blackPrefixCount_snoc_false
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount (Fin.snoc x false) = blackPrefixCount x := by
  -- Proof comment: the last Boolean indicator vanishes when the appended color is red.
  rw [blackPrefixCount_eq_sum_indicator, blackPrefixCount_eq_sum_indicator, Fin.sum_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last, add_comm]

/-- Helper for Example 17.27: a Boolean prefix can contain at most `n` black entries. -/
theorem blackPrefixCount_le
    {n : ℕ} (x : Fin n → Bool) :
    blackPrefixCount x ≤ n := by
  classical
  -- Proof comment: the filtered set of black indices is a subset of the full `Fin n`.
  simpa [blackPrefixCount] using
    (Finset.card_filter_le (s := Finset.univ) (p := fun i : Fin n ↦ x i = true))

/-- The source-facing owner predicate for the generalized two-color weighted Pólya urn from
Example 17.27. Each coordinate is measurable, and every one-step black-cylinder probability is
given by the textbook weight ratio determined by the current number of black draws. -/
def IsGeneralizedPolyaUrnWithWeights
    (μ : Measure Ω) (w : ℕ → NNReal) (X : ℕ → Ω → Bool) : Prop :=
  (∀ n : ℕ, Measurable (X n)) ∧
    ∀ ⦃n : ℕ⦄ (x : Fin n → Bool),
      let ℓ := blackPrefixCount x
      μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
        (((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ (weightedUrnPrefixEvent X x)

namespace IsGeneralizedPolyaUrnWithWeights

/-- Every coordinate of a generalized weighted Pólya-urn draw sequence is measurable. -/
theorem measurable
    {μ : Measure Ω} {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) (n : ℕ) :
    Measurable (X n) :=
  hX.1 n

/-- The defining one-step black-cylinder formula of a generalized weighted Pólya urn. -/
theorem prefixEvent_inter_true_eq
    {μ : Measure Ω} {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) {n : ℕ} (x : Fin n → Bool) :
    let ℓ := blackPrefixCount x
    μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
      (((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ (weightedUrnPrefixEvent X x) :=
  hX.2 x

end IsGeneralizedPolyaUrnWithWeights

/-- Example 17.27: in a generalized weighted Pólya urn, the next-black cylinder measure over any
Boolean prefix is the textbook weight ratio times the prefix-cylinder measure. -/
theorem weightedUrnNextBlackRace_eq_weightRatio
    {μ : Measure Ω} {w : ℕ → NNReal} {X : ℕ → Ω → Bool}
    (hX : IsGeneralizedPolyaUrnWithWeights μ w X) {n : ℕ} (x : Fin n → Bool) :
    let ℓ := blackPrefixCount x
    μ (weightedUrnPrefixEvent X x ∩ {ω | X n ω = true}) =
      (((w ℓ) / (w ℓ + w (n - ℓ)) : NNReal) : ℝ≥0∞) * μ (weightedUrnPrefixEvent X x) := by
  -- Proof comment: this is exactly the source-facing one-step formula already packaged in the
  -- generalized weighted-urn owner predicate.
  exact IsGeneralizedPolyaUrnWithWeights.prefixEvent_inter_true_eq hX x

/- Example 17.27 is `source-facing` at the level of the induced Boolean-valued draw process. The
exponential clock family and its product law are the `bridge/view` layer, while the owner
abstraction for the resulting urn path is `IsGeneralizedPolyaUrnWithWeights`. For the cumulative
clock bookkeeping, the chapter's owner declaration is `arrivalTime`, so the file reuses that API
instead of keeping a parallel local partial-sum layer. -/

/-- A trajectory of the exponential-clock realization of the weighted Pólya urn, with genuine
nonnegative waiting times. The value `ω (true, n)` is the `(n + 1)`st black clock increment and
`ω (false, n)` is the `(n + 1)`st red clock increment. -/
abbrev WeightedUrnClockTrajectory := Bool × ℕ → NNReal

/-- The product law of the exponential-clock construction of the weighted Pólya urn with weight
sequence `w`. For each color and each `n`, the corresponding clock increment has law
`Exp (w n)` transported to the nonnegative waiting-time space, and all increments are independent.
-/
noncomputable def weightedUrnClockLaw (w : ℕ → ℝ) : Measure WeightedUrnClockTrajectory :=
  Measure.infinitePi fun i : Bool × ℕ ↦ (expMeasure (w i.2)).map Real.toNNReal

-- Proof sketch: `isProbabilityMeasure_expMeasure (hw n)` makes each coordinate law a probability
-- measure, and the canonical `Measure.infinitePi` instance promotes their product law to a
-- probability measure.
/-- The exponential-clock law is a probability measure whenever every rate `w n` is positive. -/
theorem weightedUrnClockLaw_isProbabilityMeasure
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) :
    IsProbabilityMeasure (weightedUrnClockLaw w) := by
  letI : ∀ i : Bool × ℕ, IsProbabilityMeasure ((expMeasure (w i.2)).map Real.toNNReal) :=
    fun i ↦ by
      letI : IsProbabilityMeasure (expMeasure (w i.2)) := isProbabilityMeasure_expMeasure (hw i.2)
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  simpa [weightedUrnClockLaw] using
    (inferInstance :
      IsProbabilityMeasure
        (Measure.infinitePi fun i : Bool × ℕ ↦ (expMeasure (w i.2)).map Real.toNNReal))

/-- Helper for Example 17.27: each coordinate projection of the product clock law has the
corresponding pushed-forward exponential law. -/
lemma weightedUrnClockCoordinate_hasLaw
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) (color : Bool) (n : ℕ) :
    HasLaw
      (fun ω : WeightedUrnClockTrajectory ↦ ω (color, n))
      ((expMeasure (w n)).map Real.toNNReal)
      (weightedUrnClockLaw w) := by
  letI : ∀ i : Bool × ℕ, IsProbabilityMeasure ((expMeasure (w i.2)).map Real.toNNReal) :=
    fun i ↦ by
      letI : IsProbabilityMeasure (expMeasure (w i.2)) := by
        exact isProbabilityMeasure_expMeasure (hw i.2)
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  -- Proof comment: `measurePreserving_eval_infinitePi` identifies every coordinate of the product
  -- measure with its prescribed marginal law.
  simpa [weightedUrnClockLaw] using
    (MeasurePreserving.hasLaw
      (measurePreserving_eval_infinitePi
        (fun i : Bool × ℕ ↦ (expMeasure (w i.2)).map Real.toNNReal)
        (color, n)))

/-- Helper for Example 17.27: after coercing back to `ℝ`, each coordinate clock increment has the
original exponential law with rate `w n`. -/
lemma weightedUrnClockCoordinateReal_hasLaw
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) (color : Bool) (n : ℕ) :
    HasLaw
      (fun ω : WeightedUrnClockTrajectory ↦ (ω (color, n) : ℝ))
      (expMeasure (w n))
      (weightedUrnClockLaw w) := by
  have hcoe :
      HasLaw
        (fun x : NNReal ↦ (x : ℝ))
        (expMeasure (w n))
        ((expMeasure (w n)).map Real.toNNReal) := by
    have hroundtrip :
        (fun x : ℝ ↦ ((Real.toNNReal x : NNReal) : ℝ)) =ᵐ[expMeasure (w n)] fun x : ℝ ↦ x := by
      have hnonneg : ∀ᵐ x ∂ expMeasure (w n), 0 ≤ x :=
        aeNonnegOfHasLawExp (HasLaw.id (μ := expMeasure (w n)))
      -- Proof comment: on the almost-sure support of an exponential law, coercing through
      -- `Real.toNNReal` and back to `ℝ` is just the identity.
      filter_upwards [hnonneg] with x hx
      simp [Real.toNNReal_of_nonneg hx]
    have hmap :
        Measure.map (fun x : NNReal ↦ (x : ℝ)) ((expMeasure (w n)).map Real.toNNReal) =
          expMeasure (w n) := by
      calc
        Measure.map (fun x : NNReal ↦ (x : ℝ)) ((expMeasure (w n)).map Real.toNNReal)
            = Measure.map (fun x : ℝ ↦ ((Real.toNNReal x : NNReal) : ℝ)) (expMeasure (w n)) := by
                simpa [Function.comp] using
                  (AEMeasurable.map_map_of_aemeasurable
                    (μ := expMeasure (w n))
                    (f := Real.toNNReal)
                    (g := fun x : NNReal ↦ (x : ℝ))
                    measurable_coe_nnreal_real.aemeasurable
                    measurable_real_toNNReal.aemeasurable)
        _ = Measure.map (fun x : ℝ ↦ x) (expMeasure (w n)) := by
              exact Measure.map_congr hroundtrip
        _ = expMeasure (w n) := by simp
    -- Proof comment: the coordinate already has the pushed-forward exponential law on `NNReal`,
    -- and the previous map identity transports it back to the original law on `ℝ`.
    exact ⟨measurable_coe_nnreal_real.aemeasurable, hmap⟩
  simpa [Function.comp] using
    HasLaw.comp hcoe (weightedUrnClockCoordinate_hasLaw w hw color n)

/-- Helper for Example 17.27: distinct real-valued clock coordinates are independent under the
product clock law. -/
lemma weightedUrnClockCoordinateReal_indep
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) (i j : Bool × ℕ) (hij : i ≠ j) :
    IndepFun
      (fun ω : WeightedUrnClockTrajectory ↦ (ω i : ℝ))
      (fun ω : WeightedUrnClockTrajectory ↦ (ω j : ℝ))
      (weightedUrnClockLaw w) := by
  letI : ∀ p : Bool × ℕ, IsProbabilityMeasure ((expMeasure (w p.2)).map Real.toNNReal) :=
    fun p ↦ by
      letI : IsProbabilityMeasure (expMeasure (w p.2)) := isProbabilityMeasure_expMeasure (hw p.2)
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hcoordIndep :
      iIndepFun
        (fun p : Bool × ℕ ↦ fun ω : WeightedUrnClockTrajectory ↦ ω p)
        (weightedUrnClockLaw w) := by
    -- Proof comment: the coordinate projections of an infinite product measure are independent.
    simpa [weightedUrnClockLaw] using
      (iIndepFun_infinitePi
        (P := fun p : Bool × ℕ ↦ (expMeasure (w p.2)).map Real.toNNReal)
        (X := fun _ x ↦ x)
        (fun _ ↦ measurable_id))
  have hrealIndep :
      iIndepFun
        (fun p : Bool × ℕ ↦ fun ω : WeightedUrnClockTrajectory ↦ (ω p : ℝ))
        (weightedUrnClockLaw w) := by
    -- Proof comment: coercing the nonnegative coordinates back to `ℝ` preserves independence.
    simpa using
      hcoordIndep.comp (fun _ ↦ fun x : NNReal ↦ (x : ℝ))
        (fun _ ↦ measurable_coe_nnreal_real)
  simpa using hrealIndep.indepFun hij

/-- Helper for Example 17.27: any two distinct real-valued clock coordinates have the product law
of their exponential marginals. -/
lemma weightedUrnClockCoordinateRealPair_hasLaw
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) (i j : Bool × ℕ) (hij : i ≠ j) :
    HasLaw
      (fun ω : WeightedUrnClockTrajectory ↦ ((ω i : ℝ), (ω j : ℝ)))
      ((expMeasure (w i.2)).prod (expMeasure (w j.2)))
      (weightedUrnClockLaw w) := by
  letI : IsProbabilityMeasure (weightedUrnClockLaw w) :=
    weightedUrnClockLaw_isProbabilityMeasure w hw
  have hi :
      HasLaw
        (fun ω : WeightedUrnClockTrajectory ↦ (ω i : ℝ))
        (expMeasure (w i.2))
        (weightedUrnClockLaw w) :=
    weightedUrnClockCoordinateReal_hasLaw w hw i.1 i.2
  have hj :
      HasLaw
        (fun ω : WeightedUrnClockTrajectory ↦ (ω j : ℝ))
        (expMeasure (w j.2))
        (weightedUrnClockLaw w) :=
    weightedUrnClockCoordinateReal_hasLaw w hw j.1 j.2
  have hIndep :
      IndepFun
        (fun ω : WeightedUrnClockTrajectory ↦ (ω i : ℝ))
        (fun ω : WeightedUrnClockTrajectory ↦ (ω j : ℝ))
        (weightedUrnClockLaw w) :=
    weightedUrnClockCoordinateReal_indep w hw i j hij
  -- Proof comment: combine the two marginal laws with the coordinate independence to identify the
  -- joint pushforward as the corresponding product law.
  refine ⟨hi.aemeasurable.prodMk hj.aemeasurable, ?_⟩
  rw [(indepFun_iff_map_prod_eq_prod_map_map hi.aemeasurable hj.aemeasurable).mp hIndep,
    hi.map_eq, hj.map_eq]

/-- Helper for Example 17.27: any injective finite family of real-valued clock coordinates has the
product law of the corresponding exponential marginals. -/
lemma weightedUrnClockFiniteRealFamily_hasLaw_pi
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) {k : ℕ}
    (f : Fin k → Bool × ℕ) (hf : Function.Injective f) :
    HasLaw
      (fun ω : WeightedUrnClockTrajectory ↦ fun i : Fin k ↦ (ω (f i) : ℝ))
      (Measure.pi fun i : Fin k ↦ expMeasure (w (f i).2))
      (weightedUrnClockLaw w) := by
  letI : IsProbabilityMeasure (weightedUrnClockLaw w) :=
    weightedUrnClockLaw_isProbabilityMeasure w hw
  letI : ∀ p : Bool × ℕ, IsProbabilityMeasure ((expMeasure (w p.2)).map Real.toNNReal) :=
    fun p ↦ by
      letI : IsProbabilityMeasure (expMeasure (w p.2)) := isProbabilityMeasure_expMeasure (hw p.2)
      exact Measure.isProbabilityMeasure_map (by fun_prop)
  have hcoordIndep :
      iIndepFun
        (fun p : Bool × ℕ ↦ fun ω : WeightedUrnClockTrajectory ↦ (ω p : ℝ))
        (weightedUrnClockLaw w) := by
    have hcoordNNReal :
        iIndepFun
          (fun p : Bool × ℕ ↦ fun ω : WeightedUrnClockTrajectory ↦ ω p)
          (weightedUrnClockLaw w) := by
      -- Proof comment: the infinite product law makes the coordinate projections independent on
      -- the native `NNReal` clock space.
      simpa [weightedUrnClockLaw] using
        (iIndepFun_infinitePi
          (P := fun p : Bool × ℕ ↦ (expMeasure (w p.2)).map Real.toNNReal)
          (X := fun _ x ↦ x)
          (fun _ ↦ measurable_id))
    -- Proof comment: composing each coordinate with the coercion `NNReal → ℝ` keeps the finite
    -- family independent on the real-valued clock scale used by the race lemmas.
    simpa using
      hcoordNNReal.comp (fun _ ↦ fun x : NNReal ↦ (x : ℝ))
        (fun _ ↦ measurable_coe_nnreal_real)
  have hfamilyIndep :
      iIndepFun
        (fun i : Fin k ↦ fun ω : WeightedUrnClockTrajectory ↦ (ω (f i) : ℝ))
        (weightedUrnClockLaw w) := by
    exact hcoordIndep.precomp hf
  have hfamilyLaw :
      ∀ i : Fin k,
        HasLaw
          (fun ω : WeightedUrnClockTrajectory ↦ (ω (f i) : ℝ))
          (expMeasure (w (f i).2))
          (weightedUrnClockLaw w) := by
    intro i
    exact weightedUrnClockCoordinateReal_hasLaw w hw (f i).1 (f i).2
  -- Proof comment: finite independence identifies the joint pushforward with the product of the
  -- marginal exponential laws of the selected coordinates.
  refine ⟨aemeasurable_pi_lambda _ fun i ↦ (hfamilyLaw i).aemeasurable, ?_⟩
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (hfamilyLaw i).aemeasurable).1 hfamilyIndep]
  congr 1
  funext i
  exact (hfamilyLaw i).map_eq

/-- Helper for Example 17.27: splitting off the last coordinate from a finite real tuple leaves
the `Fin.castSucc` prefix in the second component. -/
lemma piFinSuccAboveLast_snd_eq_castSuccReal {n : ℕ} :
    Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) (Fin.last n) =
      fun z : Fin (n + 1) → ℝ ↦ fun i : Fin n ↦ z i.castSucc := by
  funext z i
  -- Proof comment: for `Fin.last`, `succAbove` is exactly `Fin.castSucc`, so the tail component is
  -- the usual prefix of the finite tuple.
  simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]

/-- Helper for Example 17.27: splitting the last two coordinates off a finite real product law
gives the terminal marginal, the penultimate marginal, and the `Fin.castSucc.castSucc` prefix
product law. -/
lemma realPi_map_lastTwoPrefix
    {k : ℕ} (μ : Fin (k + 2) → Measure ℝ) [∀ i : Fin (k + 2), SigmaFinite (μ i)] :
    Measure.map
      (fun z : Fin (k + 2) → ℝ ↦
        (z (Fin.last (k + 1)),
          (z (Fin.castSucc (Fin.last k)), fun i : Fin k ↦ z i.castSucc.castSucc)))
      (Measure.pi μ) =
        (μ (Fin.last (k + 1))).prod
          ((μ (Fin.castSucc (Fin.last k))).prod
            (Measure.pi fun i : Fin k ↦ μ i.castSucc.castSucc)) := by
  let eLast : (Fin (k + 2) → ℝ) ≃ᵐ ℝ × (Fin (k + 1) → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 2) ↦ ℝ) (Fin.last (k + 1))
  let eHead : (Fin (k + 1) → ℝ) ≃ᵐ ℝ × (Fin k → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) ↦ ℝ) (Fin.last k)
  let μPrefix : Fin (k + 1) → Measure ℝ := fun i ↦ μ i.castSucc
  have hsplit :
      (fun z : Fin (k + 2) → ℝ ↦
        (z (Fin.last (k + 1)),
          (z (Fin.castSucc (Fin.last k)), fun i : Fin k ↦ z i.castSucc.castSucc))) =
        (fun q : ℝ × (Fin (k + 1) → ℝ) ↦ (q.1, eHead q.2)) ∘ eLast := by
    funext z
    apply Prod.ext
    · simp [eLast, MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]
    · apply Prod.ext
      · simp [eLast, eHead, MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]
      · ext i
        simp [eLast, eHead, MeasurableEquiv.piFinSuccAbove_apply, Fin.init_def]
  have hLast :
      Measure.map eLast (Measure.pi μ) =
        (μ (Fin.last (k + 1))).prod (Measure.pi μPrefix) := by
    -- Proof comment: the first split isolates the terminal coordinate and leaves the cast-succ
    -- prefix under the finite product law.
    simpa [eLast, μPrefix, Fin.succAbove_last] using
      (measurePreserving_piFinSuccAbove μ (Fin.last (k + 1))).map_eq
  have hHead :
      Measure.map eHead (Measure.pi μPrefix) =
        (μ (Fin.castSucc (Fin.last k))).prod
          (Measure.pi fun i : Fin k ↦ μ i.castSucc.castSucc) := by
    -- Proof comment: the second split repeats the same `Fin.last` factorization on the remaining
    -- prefix product law.
    simpa [eHead, μPrefix, Fin.succAbove_last] using
      (measurePreserving_piFinSuccAbove μPrefix (Fin.last k)).map_eq
  calc
    Measure.map
        (fun z : Fin (k + 2) → ℝ ↦
          (z (Fin.last (k + 1)),
          (z (Fin.castSucc (Fin.last k)), fun i : Fin k ↦ z i.castSucc.castSucc)))
        (Measure.pi μ)
        =
      Measure.map (fun q : ℝ × (Fin (k + 1) → ℝ) ↦ (q.1, eHead q.2))
        (Measure.map eLast (Measure.pi μ)) := by
          rw [hsplit, Measure.map_map
            (show Measurable (fun q : ℝ × (Fin (k + 1) → ℝ) ↦ (q.1, eHead q.2)) by
              exact measurable_fst.prodMk (eHead.measurable.comp measurable_snd))
            eLast.measurable]
    _ = Measure.map (fun q : ℝ × (Fin (k + 1) → ℝ) ↦ (q.1, eHead q.2))
          ((μ (Fin.last (k + 1))).prod (Measure.pi μPrefix)) := by
            rw [hLast]
    _ = (μ (Fin.last (k + 1))).prod (Measure.map eHead (Measure.pi μPrefix)) := by
          simpa [eHead] using
            (Measure.map_prod_map
              (μa := μ (Fin.last (k + 1)))
              (μc := Measure.pi μPrefix)
              (f := fun x : ℝ ↦ x)
              (g := eHead)
              measurable_id eHead.measurable).symm
    _ = (μ (Fin.last (k + 1))).prod
          ((μ (Fin.castSucc (Fin.last k))).prod
            (Measure.pi fun i : Fin k ↦ μ i.castSucc.castSucc)) := by
          rw [hHead]

/-- Helper for Example 17.27: an injective finite family of real-valued clock coordinates can be
split into its last two coordinates together with the preceding prefix, and the law factors as the
corresponding product of exponential marginals. -/
lemma weightedUrnClockFiniteRealFamily_lastTwoPrefix_hasLaw
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) {k : ℕ}
    (f : Fin (k + 2) → Bool × ℕ) (hf : Function.Injective f) :
    HasLaw
      (fun ω : WeightedUrnClockTrajectory ↦
        ((ω (f (Fin.last (k + 1))) : ℝ),
          ((ω (f (Fin.castSucc (Fin.last k))) : ℝ),
            fun i : Fin k ↦ (ω (f i.castSucc.castSucc) : ℝ))))
      ((expMeasure (w (f (Fin.last (k + 1))).2)).prod
        ((expMeasure (w (f (Fin.castSucc (Fin.last k))).2)).prod
          (Measure.pi fun i : Fin k ↦ expMeasure (w (f i.castSucc.castSucc).2))))
      (weightedUrnClockLaw w) := by
  let tupleMap : WeightedUrnClockTrajectory → Fin (k + 2) → ℝ :=
    fun ω i ↦ (ω (f i) : ℝ)
  let splitMap : (Fin (k + 2) → ℝ) → ℝ × (ℝ × (Fin k → ℝ)) :=
    fun z ↦
      (z (Fin.last (k + 1)),
        (z (Fin.castSucc (Fin.last k)), fun i : Fin k ↦ z i.castSucc.castSucc))
  have htuple :
      HasLaw tupleMap (Measure.pi fun i : Fin (k + 2) ↦ expMeasure (w (f i).2))
        (weightedUrnClockLaw w) :=
    weightedUrnClockFiniteRealFamily_hasLaw_pi w hw f hf
  have hsplit :
      HasLaw splitMap
        ((expMeasure (w (f (Fin.last (k + 1))).2)).prod
          ((expMeasure (w (f (Fin.castSucc (Fin.last k))).2)).prod
            (Measure.pi fun i : Fin k ↦ expMeasure (w (f i.castSucc.castSucc).2))))
        (Measure.pi fun i : Fin (k + 2) ↦ expMeasure (w (f i).2)) := by
    letI : ∀ i : Fin (k + 2), IsProbabilityMeasure (expMeasure (w (f i).2)) :=
      fun i ↦ isProbabilityMeasure_expMeasure (hw (f i).2)
    refine ⟨?_, ?_⟩
    · exact
        ((measurable_pi_apply _).prodMk <|
          (measurable_pi_apply _).prodMk <|
            measurable_pi_lambda _ fun i ↦ measurable_pi_apply _).aemeasurable
    · simpa using
        realPi_map_lastTwoPrefix (μ := fun i : Fin (k + 2) ↦ expMeasure (w (f i).2))
  -- Proof comment: first identify the finite joint law of the selected coordinates, then apply
  -- the canonical two-step split of the last two coordinates.
  simpa [Function.comp, tupleMap, splitMap] using hsplit.comp htuple

/-- Helper for Example 17.27: the last-two-prefix finite clock law can be reassociated to a
`prefix × (last × penultimate)` product law, which is the stable transport shape used for the
successor-branch residual race computation. -/
lemma weightedUrnClockFiniteRealFamily_prefixHeads_hasLaw
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) {k : ℕ}
    (f : Fin (k + 3) → Bool × ℕ) (hf : Function.Injective f) :
    HasLaw
      (fun ω : WeightedUrnClockTrajectory ↦
        ((fun i : Fin (k + 1) ↦ (ω (f i.castSucc.castSucc) : ℝ)),
          ((ω (f (Fin.last (k + 2))) : ℝ),
            (ω (f (Fin.castSucc (Fin.last (k + 1)))) : ℝ))))
      (((Measure.pi fun i : Fin (k + 1) ↦ expMeasure (w (f i.castSucc.castSucc).2)).prod
        ((expMeasure (w (f (Fin.last (k + 2))).2)).prod
          (expMeasure (w (f (Fin.castSucc (Fin.last (k + 1)))).2)))))
      (weightedUrnClockLaw w) := by
  let baseMap : WeightedUrnClockTrajectory → ℝ × (ℝ × (Fin (k + 1) → ℝ)) :=
    fun ω ↦
      ((ω (f (Fin.last (k + 2))) : ℝ),
        ((ω (f (Fin.castSucc (Fin.last (k + 1)))) : ℝ),
          fun i : Fin (k + 1) ↦ (ω (f i.castSucc.castSucc) : ℝ)))
  let rearrange : ℝ × (ℝ × (Fin (k + 1) → ℝ)) → (Fin (k + 1) → ℝ) × (ℝ × ℝ) :=
    fun z ↦ (z.2.2, (z.1, z.2.1))
  let νprefix : Measure (Fin (k + 1) → ℝ) :=
    Measure.pi fun i : Fin (k + 1) ↦ expMeasure (w (f i.castSucc.castSucc).2)
  let νlast : Measure ℝ := expMeasure (w (f (Fin.last (k + 2))).2)
  let νpenult : Measure ℝ := expMeasure (w (f (Fin.castSucc (Fin.last (k + 1)))).2)
  letI : IsProbabilityMeasure νlast := by
    dsimp [νlast]
    exact isProbabilityMeasure_expMeasure (hw _)
  letI : IsProbabilityMeasure νpenult := by
    dsimp [νpenult]
    exact isProbabilityMeasure_expMeasure (hw _)
  letI : ∀ i : Fin (k + 1), IsProbabilityMeasure (expMeasure (w (f i.castSucc.castSucc).2)) :=
    fun i ↦ isProbabilityMeasure_expMeasure (hw _)
  letI : IsProbabilityMeasure νprefix := by
    dsimp [νprefix]
    infer_instance
  letI : SFinite νprefix := inferInstance
  letI : SFinite (νlast.prod νpenult) := inferInstance
  have hbase :
      HasLaw baseMap
        (νlast.prod (νpenult.prod νprefix))
        (weightedUrnClockLaw w) := by
    simpa [baseMap, νprefix, νlast, νpenult] using
      weightedUrnClockFiniteRealFamily_lastTwoPrefix_hasLaw w hw f hf
  have hswap :
      HasLaw rearrange
        (νprefix.prod (νlast.prod νpenult))
        (νlast.prod (νpenult.prod νprefix)) := by
    refine ⟨?_, ?_⟩
    · -- Proof comment: the reassociation is the measurable composition of `prodAssoc.symm` with
      -- the outer `Prod.swap`.
      exact (measurable_snd.snd.prodMk
        (measurable_fst.prodMk measurable_snd.fst)).aemeasurable
    · have hrearrange :
          rearrange =
            Prod.swap ∘
              (MeasurableEquiv.prodAssoc.symm :
                ℝ × (ℝ × (Fin (k + 1) → ℝ)) ≃ᵐ
                  (ℝ × ℝ) × (Fin (k + 1) → ℝ)) := by
        funext z
        rfl
      -- Proof comment: first reassociate `(last, (penultimate, prefix))` to
      -- `((last, penultimate), prefix)`, then swap the outer pair to put the prefix first.
      calc
        Measure.map rearrange (νlast.prod (νpenult.prod νprefix))
            = Measure.map Prod.swap
                (Measure.map
                  (MeasurableEquiv.prodAssoc.symm :
                    ℝ × (ℝ × (Fin (k + 1) → ℝ)) ≃ᵐ
                      (ℝ × ℝ) × (Fin (k + 1) → ℝ))
                  (νlast.prod (νpenult.prod νprefix))) := by
                rw [Measure.map_map measurable_swap MeasurableEquiv.prodAssoc.symm.measurable]
                simp [hrearrange]
        _ = Measure.map Prod.swap ((νlast.prod νpenult).prod νprefix) := by
              rw [((measurePreserving_prodAssoc νlast νpenult νprefix).symm).map_eq]
        _ = νprefix.prod (νlast.prod νpenult) := by
              rw [Measure.prod_swap]
  -- Proof comment: compose the existing finite-coordinate split law with the canonical
  -- reassociation map to obtain the stable `prefix × (head × head)` transport interface.
  simpa [Function.comp, baseMap, rearrange, νprefix, νlast, νpenult] using hswap.comp hbase

/-- The arrival time of the `(n + 1)`st clock ring of one fixed color in the exponential embedding
of the weighted urn. -/
def weightedUrnColorArrivalTime (color : Bool) (n : ℕ) : WeightedUrnClockTrajectory → ℝ :=
  arrivalTime (fun k ω ↦ (ω (color, k) : ℝ)) n

/-- The black/red draw counts after the first `n` draws of the clock-embedded urn process. -/
def weightedUrnDrawCounts : ℕ → WeightedUrnClockTrajectory → ℕ × ℕ
  | 0, _ => (0, 0)
  | n + 1, ω =>
      let counts := weightedUrnDrawCounts n ω
      if weightedUrnColorArrivalTime true (counts.1 + 1) ω <
          weightedUrnColorArrivalTime false (counts.2 + 1) ω then
        (counts.1 + 1, counts.2)
      else
        (counts.1, counts.2 + 1)

/-- The source-facing draw process induced by the merged exponential clock rings, where `true`
encodes a black draw and `false` a red draw. -/
def weightedUrnDrawProcess (n : ℕ) (ω : WeightedUrnClockTrajectory) : Bool :=
  let counts := weightedUrnDrawCounts n ω
  weightedUrnColorArrivalTime true (counts.1 + 1) ω <
    weightedUrnColorArrivalTime false (counts.2 + 1) ω

/-- Helper for Example 17.27: the Boolean draw process is `true` exactly when the next black
arrival beats the next red arrival at the current deterministic draw counts. -/
lemma weightedUrnDrawProcess_true_iff_arrivalComparison
    (n : ℕ) (ω : WeightedUrnClockTrajectory) :
    weightedUrnDrawProcess n ω = true ↔
      weightedUrnColorArrivalTime true ((weightedUrnDrawCounts n ω).1 + 1) ω <
        weightedUrnColorArrivalTime false ((weightedUrnDrawCounts n ω).2 + 1) ω := by
  -- Proof comment: `weightedUrnDrawProcess` is defined by exactly this next-arrival comparison.
  simp [weightedUrnDrawProcess]

/-- Helper for Example 17.27: the Boolean draw process is `false` exactly when the next red
arrival is no later than the next black arrival at the current draw counts. -/
lemma weightedUrnDrawProcess_false_iff_arrivalComparison
    (n : ℕ) (ω : WeightedUrnClockTrajectory) :
    weightedUrnDrawProcess n ω = false ↔
      weightedUrnColorArrivalTime false ((weightedUrnDrawCounts n ω).2 + 1) ω ≤
        weightedUrnColorArrivalTime true ((weightedUrnDrawCounts n ω).1 + 1) ω := by
  -- Proof comment: the `false` branch is the complementary weak inequality to the `true` race.
  simp [weightedUrnDrawProcess, not_lt]

/-- The total clock time of one fixed color, written as the infinite sum of its successive
exponential waiting times. -/
def weightedUrnColorTotalTime (color : Bool) (ω : WeightedUrnClockTrajectory) : ℝ≥0∞ :=
  ∑' n : ℕ, (ω (color, n) : ℝ≥0∞)

/-- Helper for Example 17.27: the finite arrival time of one color is exactly the corresponding
finite partial sum of that color's clock increments, viewed in `ℝ≥0∞`. -/
lemma weightedUrnColorArrivalTime_toENNReal
    (color : Bool) (n : ℕ) (ω : WeightedUrnClockTrajectory) :
    ENNReal.ofReal (weightedUrnColorArrivalTime color n ω) =
      ∑ i ∈ Finset.range n, (ω (color, i) : ℝ≥0∞) := by
  -- Proof comment: each increment already lives in `NNReal`, so `ofReal` turns the real-valued
  -- arrival-time sum back into the corresponding `ℝ≥0∞` partial sum.
  simp [weightedUrnColorArrivalTime, arrivalTime, ENNReal.ofReal_sum_of_nonneg]

/-- Helper for Example 17.27: the total clock time of one color is the supremum of its finite
arrival times. -/
lemma weightedUrnColorTotalTime_eq_iSup_arrivalTime
    (color : Bool) (ω : WeightedUrnClockTrajectory) :
    weightedUrnColorTotalTime color ω =
      ⨆ n : ℕ, ENNReal.ofReal (weightedUrnColorArrivalTime color n ω) := by
  -- Proof comment: `ENNReal.tsum_eq_iSup_nat` rewrites the infinite sum as the supremum of its
  -- finite partial sums, and the previous lemma identifies those partial sums with arrival times.
  rw [weightedUrnColorTotalTime, ENNReal.tsum_eq_iSup_nat]
  congr with n
  exact (weightedUrnColorArrivalTime_toENNReal color n ω).symm

/-- Helper for Example 17.27: if all increments of one color are strictly positive, then the
arrival times of that color form a strictly increasing sequence. -/
lemma weightedUrnColorArrivalTime_strictMono_of_pos
    (color : Bool) (ω : WeightedUrnClockTrajectory)
    (hpos : ∀ n : ℕ, 0 < ω (color, n)) :
    StrictMono (fun n : ℕ ↦ weightedUrnColorArrivalTime color n ω) := by
  -- Proof comment: each successor step adds the next strictly positive interarrival time.
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  have hstep : 0 < ((ω (color, n) : NNReal) : ℝ) := by
    exact_mod_cast hpos n
  simpa [weightedUrnColorArrivalTime, arrivalTime_succ] using
    (lt_add_of_pos_right (weightedUrnColorArrivalTime color n ω) hstep)

/-- Helper for Example 17.27: if all increments of one color are strictly positive, then every
finite arrival time stays strictly below that color's total clock time. -/
lemma weightedUrnColorArrivalTime_lt_totalTime_of_pos
    (color : Bool) (ω : WeightedUrnClockTrajectory)
    (hpos : ∀ n : ℕ, 0 < ω (color, n)) (n : ℕ) :
    ENNReal.ofReal (weightedUrnColorArrivalTime color n ω) <
      weightedUrnColorTotalTime color ω := by
  -- Proof comment: the `(n + 1)`st partial sum is strictly larger than the `n`th one because the
  -- next increment is positive, and the total time dominates every finite partial sum.
  rw [weightedUrnColorTotalTime_eq_iSup_arrivalTime]
  refine lt_of_lt_of_le ?_
    (le_iSup
      (fun m : ℕ ↦ ENNReal.ofReal (weightedUrnColorArrivalTime color m ω))
      (n + 1))
  rw [weightedUrnColorArrivalTime_toENNReal, weightedUrnColorArrivalTime_toENNReal]
  rw [Finset.sum_range_succ]
  have hstep : (0 : ℝ≥0∞) < (ω (color, n) : ℝ≥0∞) := by
    exact_mod_cast hpos n
  have hsum_ne_top :
      (∑ i ∈ Finset.range n, (ω (color, i) : ℝ≥0∞)) ≠ ∞ := by
    simp
  simpa [add_comm, add_left_comm, add_assoc] using ENNReal.lt_add_right hsum_ne_top hstep.ne'

/-- Helper for Example 17.27: every fixed coordinate clock increment is almost surely strictly
positive under the exponential clock law. -/
lemma weightedUrnClockCoordinate_ae_pos
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) (color : Bool) (n : ℕ) :
    ∀ᵐ ω ∂ weightedUrnClockLaw w, 0 < ω (color, n) := by
  have hcoord :
      HasLaw
        (fun ω : WeightedUrnClockTrajectory ↦ (ω (color, n) : ℝ))
        (expMeasure (w n))
        (weightedUrnClockLaw w) :=
    weightedUrnClockCoordinateReal_hasLaw w hw color n
  have hnonneg : ∀ᵐ ω ∂ weightedUrnClockLaw w, 0 ≤ (ω (color, n) : ℝ) :=
    aeNonnegOfHasLawExp hcoord
  have hsingleton : expMeasure (w n) ({0} : Set ℝ) = 0 := by
    rw [expMeasure, gammaMeasure, withDensity_apply _ (measurableSet_singleton 0)]
    simp
  have hne_zero_exp : ∀ᵐ x ∂ expMeasure (w n), x ≠ 0 := by
    rw [ae_iff]
    simpa using hsingleton
  have hne_zero : ∀ᵐ ω ∂ weightedUrnClockLaw w, (ω (color, n) : ℝ) ≠ 0 := by
    exact (hcoord.ae_iff (p := fun x : ℝ ↦ x ≠ 0) (by fun_prop)).2 hne_zero_exp
  -- Proof comment: positivity is the conjunction of the almost-sure nonnegativity and the fact
  -- that the exponential law has no atom at `0`.
  filter_upwards [hnonneg, hne_zero] with ω hω_nonneg hω_ne
  exact_mod_cast (lt_of_le_of_ne hω_nonneg (Ne.symm hω_ne))

/-- Helper for Example 17.27: after `n` draws, the black and red draw counts always add up to
`n`. -/
lemma weightedUrnDrawCounts_total (n : ℕ) (ω : WeightedUrnClockTrajectory) :
    (weightedUrnDrawCounts n ω).1 + (weightedUrnDrawCounts n ω).2 = n := by
  induction n with
  | zero =>
      -- Proof comment: initially no draw of either color has occurred.
      simp [weightedUrnDrawCounts]
  | succ n ih =>
      -- Proof comment: each recursive step increments exactly one of the two counters.
      simp only [weightedUrnDrawCounts]
      split_ifs <;> simp [ih, Nat.add_left_comm, Nat.add_comm]

/-- Helper for Example 17.27: the next count update increments exactly the color selected by the
current draw comparison. -/
lemma weightedUrnDrawCounts_succ
    (n : ℕ) (ω : WeightedUrnClockTrajectory) :
    weightedUrnDrawCounts (n + 1) ω =
      if weightedUrnDrawProcess n ω then
        ((weightedUrnDrawCounts n ω).1 + 1, (weightedUrnDrawCounts n ω).2)
      else
        ((weightedUrnDrawCounts n ω).1, (weightedUrnDrawCounts n ω).2 + 1) := by
  -- Proof comment: both definitions use the same next-arrival comparison, so unfolding aligns the
  -- recursive count update with the Boolean draw process.
  simp [weightedUrnDrawCounts, weightedUrnDrawProcess]

/-- Helper for Example 17.27: once the draw process is eventually black, the red count freezes and
the black count grows linearly from the freezing time onward. -/
lemma weightedUrnDrawCounts_eq_of_eventuallyBlack
    (ω : WeightedUrnClockTrajectory) {N : ℕ}
    (hblack : ∀ n : ℕ, N ≤ n → weightedUrnDrawProcess n ω = true) :
    ∀ k : ℕ,
      weightedUrnDrawCounts (N + k) ω =
        ((weightedUrnDrawCounts N ω).1 + k, (weightedUrnDrawCounts N ω).2) := by
  intro k
  induction k with
  | zero =>
      -- Proof comment: at the freezing time, the counts are unchanged.
      simp
  | succ k ih =>
      -- Proof comment: every later step is black, so only the black counter increments.
      have hdraw : weightedUrnDrawProcess (N + k) ω = true := hblack (N + k) (Nat.le_add_right _ _)
      have hstep := weightedUrnDrawCounts_succ (N + k) ω
      rw [hdraw, ih] at hstep
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep

/-- Helper for Example 17.27: once the draw process is eventually red, the black count freezes and
the red count grows linearly from the freezing time onward. -/
lemma weightedUrnDrawCounts_eq_of_eventuallyRed
    (ω : WeightedUrnClockTrajectory) {N : ℕ}
    (hred : ∀ n : ℕ, N ≤ n → weightedUrnDrawProcess n ω = false) :
    ∀ k : ℕ,
      weightedUrnDrawCounts (N + k) ω =
        ((weightedUrnDrawCounts N ω).1, (weightedUrnDrawCounts N ω).2 + k) := by
  intro k
  induction k with
  | zero =>
      -- Proof comment: at the freezing time, the counts are unchanged.
      simp
  | succ k ih =>
      -- Proof comment: every later step is red, so only the red counter increments.
      have hdraw : weightedUrnDrawProcess (N + k) ω = false := hred (N + k) (Nat.le_add_right _ _)
      have hstep := weightedUrnDrawCounts_succ (N + k) ω
      rw [hdraw, ih] at hstep
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hstep

/-- Helper for Example 17.27: if `∑ 1 / w n` converges, then the total clock time of each color is
almost surely finite under the product exponential law. -/
lemma weightedUrnColorTotalTime_ae_lt_top
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n)
    (hsummable : Summable fun n : ℕ ↦ 1 / w n) (color : Bool) :
    ∀ᵐ ω ∂ weightedUrnClockLaw w, weightedUrnColorTotalTime color ω < ∞ := by
  let X : ℕ → WeightedUrnClockTrajectory → ℝ := fun n ω ↦ (ω (color, n) : ℝ)
  letI : IsProbabilityMeasure (weightedUrnClockLaw w) :=
    weightedUrnClockLaw_isProbabilityMeasure w hw
  have hX_nonneg : ∀ n : ℕ, 0 ≤ᵐ[weightedUrnClockLaw w] X n := fun n ↦
    aeNonnegOfHasLawExp (weightedUrnClockCoordinateReal_hasLaw w hw color n)
  have hX_int : ∀ n : ℕ, Integrable (X n) (weightedUrnClockLaw w) := fun n ↦
    integrableOfHasLawExp (weightedUrnClockCoordinateReal_hasLaw w hw color n)
  have h_meas :
      AEMeasurable (weightedUrnColorTotalTime color) (weightedUrnClockLaw w) := by
    -- Proof comment: the total time is the `ℝ≥0∞` series of the coordinate waiting times.
    simpa [weightedUrnColorTotalTime, X] using
      (AEMeasurable.ennreal_tsum fun n ↦
        (weightedUrnClockCoordinateReal_hasLaw w hw color n).aemeasurable.ennreal_ofReal)
  have h_lintegral :
      ∫⁻ ω, weightedUrnColorTotalTime color ω ∂ weightedUrnClockLaw w =
        ∑' n : ℕ, ENNReal.ofReal (1 / w n) := by
    calc
      ∫⁻ ω, weightedUrnColorTotalTime color ω ∂ weightedUrnClockLaw w
          = ∑' n : ℕ, ENNReal.ofReal (∫ ω, X n ω ∂ weightedUrnClockLaw w) := by
              simpa [weightedUrnColorTotalTime, X] using
                lintegral_tsum_of_nonnegative_integrable_sequence
                  (μ := weightedUrnClockLaw w) (X := X) hX_int hX_nonneg
      _ = ∑' n : ℕ, ENNReal.ofReal (1 / w n) := by
            congr with n
            rw [(weightedUrnClockCoordinateReal_hasLaw w hw color n).integral_eq]
            exact congrArg ENNReal.ofReal (integral_id_expMeasure_eq_inv (hw n))
  have h_ne_top :
      ∫⁻ ω, weightedUrnColorTotalTime color ω ∂ weightedUrnClockLaw w ≠ ∞ := by
    rw [h_lintegral]
    exact hsummable.tsum_ofReal_lt_top.ne
  -- Proof comment: finite lower integral forces almost-sure finiteness of the `ℝ≥0∞`-valued
  -- total-time series.
  exact ae_lt_top' h_meas h_ne_top

/-- Helper for Example 17.27: on a fixed Boolean prefix event, the recursive clock embedding has
already accumulated exactly the deterministic black/red draw counts encoded by that prefix. -/
lemma weightedUrnPrefixEvent_forces_drawCounts
    {n : ℕ} (x : Fin n → Bool) {ω : WeightedUrnClockTrajectory}
    (hω : ω ∈ weightedUrnPrefixEvent weightedUrnDrawProcess x) :
    weightedUrnDrawCounts n ω = (blackPrefixCount x, n - blackPrefixCount x) := by
  induction n with
  | zero =>
      -- Proof comment: the empty prefix forces the initial count pair `(0, 0)`.
      simp [weightedUrnDrawCounts, blackPrefixCount]
  | succ n ih =>
      let x0 : Fin n → Bool := fun i ↦ x i.castSucc
      have hx :
          x = Fin.snoc x0 (x (Fin.last n)) := by
        ext i
        refine Fin.lastCases ?_ ?_ i
        · simp [x0]
        · intro j
          simp [x0]
      have hω0 : ω ∈ weightedUrnPrefixEvent weightedUrnDrawProcess x0 := by
        intro i
        exact hω i.castSucc
      have hcounts0 :
          weightedUrnDrawCounts n ω = (blackPrefixCount x0, n - blackPrefixCount x0) :=
        ih x0 hω0
      have hlast : weightedUrnDrawProcess n ω = x (Fin.last n) := hω (Fin.last n)
      have hstep :
          weightedUrnDrawCounts (n + 1) ω =
            if x (Fin.last n) then
              (blackPrefixCount x0 + 1, n - blackPrefixCount x0)
            else
              (blackPrefixCount x0, n - blackPrefixCount x0 + 1) := by
        rw [weightedUrnDrawCounts_succ, hcounts0, hlast]
      by_cases hlastb : x (Fin.last n) = true
      · -- Proof comment: a final black bit appends one black draw to the deterministic prefix
        -- state.
        have hcount :
            blackPrefixCount x = blackPrefixCount x0 + 1 := by
          rw [hx, hlastb]
          exact blackPrefixCount_snoc_true x0
        simp [hstep, hlastb, hcount, Nat.succ_sub_succ_eq_sub]
      · -- Proof comment: a final red bit leaves the black count unchanged and increments only the
        -- red counter.
        have hlastf : x (Fin.last n) = false := by
          cases hcolor : x (Fin.last n) with
          | false => rfl
          | true => cases (hlastb hcolor)
        have hcount :
            blackPrefixCount x = blackPrefixCount x0 := by
          rw [hx, hlastf]
          exact blackPrefixCount_snoc_false x0
        have hle : blackPrefixCount x0 ≤ n := blackPrefixCount_le x0
        simp [hstep, hlastf, hcount, Nat.succ_sub hle, Nat.add_comm]

/-- Helper for Example 17.27: a product measure with an atomless first marginal assigns measure
zero to any measurable graph over the second coordinate. -/
lemma prod_graph_eq_zero_of_noAtoms_fst
    {β : Type*} [MeasurableSpace β] {μ : Measure ℝ} [SFinite μ] [NoAtoms μ]
    {ν : Measure β} [SFinite ν]
    {g : β → ℝ} (hg : Measurable g) :
    (μ.prod ν) {p : ℝ × β | p.1 = g p.2} = 0 := by
  have hgraph :
      MeasurableSet {p : ℝ × β | p.1 = g p.2} := by
    simpa using measurableSet_eq_fun measurable_fst (hg.comp measurable_snd)
  -- Proof comment: integrate the singleton fiber masses over the second coordinate; every fiber is
  -- a singleton in the atomless first marginal.
  rw [Measure.prod_apply_symm hgraph]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  refine Filter.Eventually.of_forall fun b ↦ ?_
  simp [NoAtoms.measure_singleton]

/-- Helper for Example 17.27: every singleton has zero mass under an exponential law. -/
lemma expMeasure_singleton_eq_zero
    (a t : ℝ) :
    expMeasure a ({t} : Set ℝ) = 0 := by
  -- Proof comment: the exponential law is given by a density with respect to Lebesgue measure, so
  -- singletons have zero mass.
  rw [expMeasure, gammaMeasure, withDensity_apply _ (measurableSet_singleton t)]
  simp

/-- Helper for Example 17.27: under a product of a past measure and two exponential heads, the
boundary where the current black head matches a measurable past-dependent threshold has measure
zero. -/
lemma expProd_gapBoundary_eq_zero
    {P : Type*} [MeasurableSpace P] {ν : Measure P} [SFinite ν]
    {a b : ℝ} [SFinite (expMeasure a)] [SFinite (expMeasure b)] {g : P → ℝ}
    (hg : Measurable g) :
    (ν.prod ((expMeasure a).prod (expMeasure b)))
      {q : P × (ℝ × ℝ) | q.2.1 = g q.1} = 0 := by
  have hgraph :
      MeasurableSet {q : P × (ℝ × ℝ) | q.2.1 = g q.1} := by
    exact measurableSet_eq_fun measurable_snd.fst (hg.comp measurable_fst)
  -- Proof comment: Fubini reduces the boundary to singleton fibers in the black-head coordinate,
  -- and those singleton fibers have zero exponential mass.
  rw [Measure.prod_apply hgraph]
  refine lintegral_eq_zero_of_ae_eq_zero ?_
  refine Filter.Eventually.of_forall fun p ↦ ?_
  have hsection :
      {q : ℝ × ℝ | (p, q) ∈ {q : P × (ℝ × ℝ) | q.2.1 = g q.1}} =
        ({g p} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext q
    simp
  change ((expMeasure a).prod (expMeasure b))
      {q : ℝ × ℝ | (p, q) ∈ {q : P × (ℝ × ℝ) | q.2.1 = g q.1}} = 0
  rw [hsection, Measure.prod_prod]
  simp [expMeasure_singleton_eq_zero]

/-- The total black-clock time in the exponential embedding of the weighted urn. -/
abbrev weightedUrnBlackTotalTime : WeightedUrnClockTrajectory → ℝ≥0∞ :=
  weightedUrnColorTotalTime true

/-- The total red-clock time in the exponential embedding of the weighted urn. -/
abbrev weightedUrnRedTotalTime : WeightedUrnClockTrajectory → ℝ≥0∞ :=
  weightedUrnColorTotalTime false

/-- The source-facing textbook event that, from some time on, the induced weighted-urn draw
process keeps drawing only one fixed color. -/
def weightedUrnEventuallySingleColorEvent : Set WeightedUrnClockTrajectory :=
  {ω | ∃ color : Bool, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → weightedUrnDrawProcess n ω = color}

/-- The bridge event in the exponential embedding that one color exhausts its total clock time
strictly before the other. -/
def weightedUrnOneColorFinishesFirstEvent : Set WeightedUrnClockTrajectory :=
  {ω | weightedUrnBlackTotalTime ω < weightedUrnRedTotalTime ω ∨
      weightedUrnRedTotalTime ω < weightedUrnBlackTotalTime ω}

/-- Helper for Example 17.27: if the draw process is eventually black, then the red counter
freezes and every later black arrival still occurs before the next unseen red arrival. This forces
the total black clock time to stay strictly below the total red clock time. -/
lemma weightedUrnBlackTotalTime_lt_of_eventuallyBlack
    (ω : WeightedUrnClockTrajectory)
    (hpos : ∀ color : Bool, ∀ n : ℕ, 0 < ω (color, n))
    {N : ℕ} (hblack : ∀ n : ℕ, N ≤ n → weightedUrnDrawProcess n ω = true) :
    weightedUrnBlackTotalTime ω < weightedUrnRedTotalTime ω := by
  let frozenBlack := (weightedUrnDrawCounts N ω).1
  let frozenRed := (weightedUrnDrawCounts N ω).2
  have hcounts := weightedUrnDrawCounts_eq_of_eventuallyBlack ω hblack
  have hmonoBlack :
      StrictMono (fun n : ℕ ↦ weightedUrnColorArrivalTime true n ω) :=
    weightedUrnColorArrivalTime_strictMono_of_pos true ω (hpos true)
  have htail :
      ∀ k : ℕ,
        weightedUrnColorArrivalTime true (frozenBlack + (k + 1)) ω <
          weightedUrnColorArrivalTime false (frozenRed + 1) ω := by
    intro k
    have hdraw : weightedUrnDrawProcess (N + k) ω = true :=
      hblack (N + k) (Nat.le_add_right _ _)
    have hstep :
        weightedUrnColorArrivalTime true (((weightedUrnDrawCounts (N + k) ω).1) + 1) ω <
          weightedUrnColorArrivalTime false (((weightedUrnDrawCounts (N + k) ω).2) + 1) ω := by
      simpa [weightedUrnDrawProcess] using hdraw
    simpa [hcounts k, frozenBlack, frozenRed, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      hstep
  have hall :
      ∀ m : ℕ,
        weightedUrnColorArrivalTime true m ω <
          weightedUrnColorArrivalTime false (frozenRed + 1) ω := by
    intro m
    by_cases hm : m ≤ frozenBlack
    · have hbase :
          weightedUrnColorArrivalTime true frozenBlack ω <
            weightedUrnColorArrivalTime false (frozenRed + 1) ω := by
        exact lt_of_le_of_lt (hmonoBlack.monotone (Nat.le_succ _))
          (by simpa [frozenBlack, frozenRed] using htail 0)
      exact lt_of_le_of_lt (hmonoBlack.monotone hm) hbase
    · have htailIndex : frozenBlack + 1 ≤ m := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htailIndex
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, frozenBlack, frozenRed] using htail k
  have hupper :
      weightedUrnBlackTotalTime ω ≤
        ENNReal.ofReal (weightedUrnColorArrivalTime false (frozenRed + 1) ω) := by
    rw [weightedUrnBlackTotalTime, weightedUrnColorTotalTime_eq_iSup_arrivalTime]
    refine iSup_le ?_
    intro m
    exact ENNReal.ofReal_le_ofReal (le_of_lt (hall m))
  -- Proof comment: the frozen red counter gives a fixed next red arrival that bounds all black
  -- arrivals from above, while positivity makes that red arrival strictly smaller than the full red
  -- total time.
  exact lt_of_le_of_lt hupper <|
    weightedUrnColorArrivalTime_lt_totalTime_of_pos false ω (hpos false) (frozenRed + 1)

/-- Helper for Example 17.27: if the draw process is eventually red, then the black counter
freezes and the symmetric arrival-time argument forces the total red clock time to stay strictly
below the total black clock time. -/
lemma weightedUrnRedTotalTime_lt_of_eventuallyRed
    (ω : WeightedUrnClockTrajectory)
    (hpos : ∀ color : Bool, ∀ n : ℕ, 0 < ω (color, n))
    {N : ℕ} (hred : ∀ n : ℕ, N ≤ n → weightedUrnDrawProcess n ω = false) :
    weightedUrnRedTotalTime ω < weightedUrnBlackTotalTime ω := by
  let frozenBlack := (weightedUrnDrawCounts N ω).1
  let frozenRed := (weightedUrnDrawCounts N ω).2
  have hcounts := weightedUrnDrawCounts_eq_of_eventuallyRed ω hred
  have hmonoRed :
      StrictMono (fun n : ℕ ↦ weightedUrnColorArrivalTime false n ω) :=
    weightedUrnColorArrivalTime_strictMono_of_pos false ω (hpos false)
  have htail :
      ∀ k : ℕ,
        weightedUrnColorArrivalTime false (frozenRed + (k + 1)) ω ≤
          weightedUrnColorArrivalTime true (frozenBlack + 1) ω := by
    intro k
    have hdraw : weightedUrnDrawProcess (N + k) ω = false :=
      hred (N + k) (Nat.le_add_right _ _)
    have hstep :
        weightedUrnColorArrivalTime false (((weightedUrnDrawCounts (N + k) ω).2) + 1) ω ≤
          weightedUrnColorArrivalTime true (((weightedUrnDrawCounts (N + k) ω).1) + 1) ω := by
      exact not_lt.mp (by simpa [weightedUrnDrawProcess] using hdraw)
    simpa [hcounts k, frozenBlack, frozenRed, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      hstep
  have hall :
      ∀ m : ℕ,
        weightedUrnColorArrivalTime false m ω ≤
          weightedUrnColorArrivalTime true (frozenBlack + 1) ω := by
    intro m
    by_cases hm : m ≤ frozenRed
    · have hbase :
          weightedUrnColorArrivalTime false frozenRed ω ≤
            weightedUrnColorArrivalTime true (frozenBlack + 1) ω := by
        exact le_trans (hmonoRed.monotone (Nat.le_succ _))
          (by simpa [frozenBlack, frozenRed] using htail 0)
      exact le_trans (hmonoRed.monotone hm) hbase
    · have htailIndex : frozenRed + 1 ≤ m := by omega
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le htailIndex
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, frozenBlack, frozenRed] using htail k
  have hupper :
      weightedUrnRedTotalTime ω ≤
        ENNReal.ofReal (weightedUrnColorArrivalTime true (frozenBlack + 1) ω) := by
    rw [weightedUrnRedTotalTime, weightedUrnColorTotalTime_eq_iSup_arrivalTime]
    refine iSup_le ?_
    intro m
    exact ENNReal.ofReal_le_ofReal (hall m)
  -- Proof comment: after the black counter freezes, the next unseen black arrival becomes a fixed
  -- ceiling for all future red arrivals, and positivity upgrades that ceiling to a strict bound
  -- below the full black total time.
  exact lt_of_le_of_lt hupper <|
    weightedUrnColorArrivalTime_lt_totalTime_of_pos true ω (hpos true) (frozenBlack + 1)

/-- Helper for Example 17.27: an eventual monochromatic tail forces one of the two total color
clock times to be strictly smaller than the other. -/
lemma weightedUrnTotalTime_lt_of_eventuallyColor
    (ω : WeightedUrnClockTrajectory)
    (hpos : ∀ color : Bool, ∀ n : ℕ, 0 < ω (color, n))
    (hevent : ω ∈ weightedUrnEventuallySingleColorEvent) :
    ω ∈ weightedUrnOneColorFinishesFirstEvent := by
  rcases hevent with ⟨color, N, hcolor⟩
  cases color with
  | false =>
      right
      exact weightedUrnRedTotalTime_lt_of_eventuallyRed ω hpos hcolor
  | true =>
      left
      exact weightedUrnBlackTotalTime_lt_of_eventuallyBlack ω hpos hcolor

/-- Helper for Example 17.27: if the total black clock time is strictly smaller than the total
red clock time, then only finitely many red draws can occur, so the draw process is eventually
constantly black. -/
lemma weightedUrnEventuallyBlack_of_blackTotalTime_lt
    (ω : WeightedUrnClockTrajectory)
    (hlt : weightedUrnBlackTotalTime ω < weightedUrnRedTotalTime ω) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → weightedUrnDrawProcess n ω = true := by
  rw [weightedUrnRedTotalTime, weightedUrnColorTotalTime_eq_iSup_arrivalTime] at hlt
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt
  cases k with
  | zero =>
      exfalso
      simp [weightedUrnColorArrivalTime, arrivalTime] at hk
  | succ m =>
      let redCount : ℕ → ℕ := fun n ↦ (weightedUrnDrawCounts n ω).2
      have hred_mono : Monotone redCount := by
        refine monotone_nat_of_le_succ ?_
        intro n
        cases hdraw : weightedUrnDrawProcess n ω with
        | false =>
            have hsnd : redCount (n + 1) = redCount n + 1 := by
              simpa [redCount, hdraw] using
                congrArg Prod.snd (weightedUrnDrawCounts_succ n ω)
            rw [hsnd]
            exact Nat.le_succ _
        | true =>
            have hsnd : redCount (n + 1) = redCount n := by
              simpa [redCount, hdraw] using
                congrArg Prod.snd (weightedUrnDrawCounts_succ n ω)
            rw [hsnd]
      have hbound : ∀ n : ℕ, redCount n ≤ m := by
        intro n
        induction n with
        | zero =>
            simp [redCount, weightedUrnDrawCounts]
        | succ n ih =>
            cases hdraw : weightedUrnDrawProcess n ω with
            | true =>
                have hsnd : redCount (n + 1) = redCount n := by
                  simpa [redCount, hdraw] using
                    congrArg Prod.snd (weightedUrnDrawCounts_succ n ω)
                rw [hsnd]
                exact ih
            | false =>
                have hsnd : redCount (n + 1) = redCount n + 1 := by
                  simpa [redCount, hdraw] using
                    congrArg Prod.snd (weightedUrnDrawCounts_succ n ω)
                rw [hsnd]
                have hm_ne : redCount n ≠ m := by
                  intro hm
                  have hblack_le :
                      ENNReal.ofReal
                          (weightedUrnColorArrivalTime true ((weightedUrnDrawCounts n ω).1 + 1) ω) ≤
                        weightedUrnBlackTotalTime ω := by
                    rw [weightedUrnBlackTotalTime, weightedUrnColorTotalTime_eq_iSup_arrivalTime]
                    exact le_iSup
                      (fun j : ℕ ↦ ENNReal.ofReal (weightedUrnColorArrivalTime true j ω))
                      ((weightedUrnDrawCounts n ω).1 + 1)
                  have hnot_lt :
                      ¬ weightedUrnColorArrivalTime true
                          ((weightedUrnDrawCounts n ω).1 + 1) ω <
                        weightedUrnColorArrivalTime false
                          ((weightedUrnDrawCounts n ω).2 + 1) ω := by
                    simpa [weightedUrnDrawProcess] using hdraw
                  have hred_le_black :
                      ENNReal.ofReal
                          (weightedUrnColorArrivalTime false
                            ((weightedUrnDrawCounts n ω).2 + 1) ω) ≤
                        ENNReal.ofReal
                          (weightedUrnColorArrivalTime true
                            ((weightedUrnDrawCounts n ω).1 + 1) ω) := by
                    exact ENNReal.ofReal_le_ofReal (not_lt.mp hnot_lt)
                  have hred_gt_black :
                      weightedUrnBlackTotalTime ω <
                        ENNReal.ofReal
                          (weightedUrnColorArrivalTime false
                            ((weightedUrnDrawCounts n ω).2 + 1) ω) := by
                    simpa [redCount, hm] using hk
                  exact
                    (not_lt_of_ge (le_trans hred_le_black hblack_le)) hred_gt_black
                have hltm : redCount n < m := lt_of_le_of_ne ih hm_ne
                exact Nat.succ_le_of_lt hltm
      classical
      let M : ℕ := Nat.findGreatest (fun j : ℕ ↦ ∃ n : ℕ, redCount n = j) m
      have hM_exists : ∃ n : ℕ, redCount n = M := by
        refine Nat.findGreatest_spec (P := fun j : ℕ ↦ ∃ n : ℕ, redCount n = j) (m := 0) ?_ ?_
        · exact (Nat.zero_le m)
        · exact ⟨0, by simp [redCount, weightedUrnDrawCounts]⟩
      obtain ⟨N, hN⟩ := hM_exists
      have hstable : ∀ n : ℕ, N ≤ n → redCount n = M := by
        intro n hn
        have hlow : M ≤ redCount n := by
          rw [← hN]
          exact hred_mono hn
        have hhigh : redCount n ≤ M := by
          exact Nat.le_findGreatest (P := fun j : ℕ ↦ ∃ n : ℕ, redCount n = j)
            (hbound n) ⟨n, rfl⟩
        exact le_antisymm hhigh hlow
      refine ⟨N, ?_⟩
      intro n hn
      cases hdraw : weightedUrnDrawProcess n ω with
      | true =>
          rfl
      | false =>
          have hcount : redCount n = M := hstable n hn
          have hsnd : redCount (n + 1) = M + 1 := by
            simpa [redCount, hdraw, hcount] using
              congrArg Prod.snd (weightedUrnDrawCounts_succ n ω)
          have hsnd' : redCount (n + 1) = M := hstable (n + 1) (le_trans hn (Nat.le_succ n))
          have : M + 1 = M := by
            simp [hsnd'] at hsnd
          omega

/-- Helper for Example 17.27: if the total red clock time is strictly smaller than the total black
clock time, then only finitely many black draws can occur, so the draw process is eventually
constantly red. -/
lemma weightedUrnEventuallyRed_of_redTotalTime_lt
    (ω : WeightedUrnClockTrajectory)
    (hlt : weightedUrnRedTotalTime ω < weightedUrnBlackTotalTime ω) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → weightedUrnDrawProcess n ω = false := by
  rw [weightedUrnBlackTotalTime, weightedUrnColorTotalTime_eq_iSup_arrivalTime] at hlt
  obtain ⟨k, hk⟩ := lt_iSup_iff.mp hlt
  cases k with
  | zero =>
      exfalso
      simp [weightedUrnColorArrivalTime, arrivalTime] at hk
  | succ m =>
      let blackCount : ℕ → ℕ := fun n ↦ (weightedUrnDrawCounts n ω).1
      have hblack_mono : Monotone blackCount := by
        refine monotone_nat_of_le_succ ?_
        intro n
        cases hdraw : weightedUrnDrawProcess n ω with
        | false =>
            have hfst : blackCount (n + 1) = blackCount n := by
              simpa [blackCount, hdraw] using
                congrArg Prod.fst (weightedUrnDrawCounts_succ n ω)
            rw [hfst]
        | true =>
            have hfst : blackCount (n + 1) = blackCount n + 1 := by
              simpa [blackCount, hdraw] using
                congrArg Prod.fst (weightedUrnDrawCounts_succ n ω)
            rw [hfst]
            exact Nat.le_succ _
      have hbound : ∀ n : ℕ, blackCount n ≤ m := by
        intro n
        induction n with
        | zero =>
            simp [blackCount, weightedUrnDrawCounts]
        | succ n ih =>
            cases hdraw : weightedUrnDrawProcess n ω with
            | false =>
                have hfst : blackCount (n + 1) = blackCount n := by
                  simpa [blackCount, hdraw] using
                    congrArg Prod.fst (weightedUrnDrawCounts_succ n ω)
                rw [hfst]
                exact ih
            | true =>
                have hfst : blackCount (n + 1) = blackCount n + 1 := by
                  simpa [blackCount, hdraw] using
                    congrArg Prod.fst (weightedUrnDrawCounts_succ n ω)
                rw [hfst]
                have hm_ne : blackCount n ≠ m := by
                  intro hm
                  have hred_le :
                      ENNReal.ofReal
                          (weightedUrnColorArrivalTime false
                            ((weightedUrnDrawCounts n ω).2 + 1) ω) ≤
                        weightedUrnRedTotalTime ω := by
                    rw [weightedUrnRedTotalTime, weightedUrnColorTotalTime_eq_iSup_arrivalTime]
                    exact le_iSup
                      (fun j : ℕ ↦ ENNReal.ofReal (weightedUrnColorArrivalTime false j ω))
                      ((weightedUrnDrawCounts n ω).2 + 1)
                  have hlt_draw :
                      weightedUrnColorArrivalTime true
                          ((weightedUrnDrawCounts n ω).1 + 1) ω <
                        weightedUrnColorArrivalTime false
                          ((weightedUrnDrawCounts n ω).2 + 1) ω := by
                    simpa [weightedUrnDrawProcess] using hdraw
                  have hblack_lt_red :
                      ENNReal.ofReal
                          (weightedUrnColorArrivalTime true
                            ((weightedUrnDrawCounts n ω).1 + 1) ω) <
                        ENNReal.ofReal
                          (weightedUrnColorArrivalTime false
                            ((weightedUrnDrawCounts n ω).2 + 1) ω) := by
                    have hblack_nonneg :
                        0 ≤ weightedUrnColorArrivalTime true
                          ((weightedUrnDrawCounts n ω).1 + 1) ω := by
                      simpa [weightedUrnColorArrivalTime, arrivalTime] using
                        (Finset.sum_nonneg fun i hi ↦ by
                          exact_mod_cast (show (0 : NNReal) ≤ ω (true, i) from bot_le))
                    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hblack_nonneg).2 hlt_draw
                  have hblack_gt_red :
                      weightedUrnRedTotalTime ω <
                        ENNReal.ofReal
                          (weightedUrnColorArrivalTime true
                            ((weightedUrnDrawCounts n ω).1 + 1) ω) := by
                    simpa [blackCount, hm] using hk
                  exact
                    (not_lt_of_ge (le_trans hred_le hblack_gt_red.le)) hblack_lt_red
                have hltm : blackCount n < m := lt_of_le_of_ne ih hm_ne
                exact Nat.succ_le_of_lt hltm
      classical
      let M : ℕ := Nat.findGreatest (fun j : ℕ ↦ ∃ n : ℕ, blackCount n = j) m
      have hM_exists : ∃ n : ℕ, blackCount n = M := by
        refine Nat.findGreatest_spec (P := fun j : ℕ ↦ ∃ n : ℕ, blackCount n = j) (m := 0) ?_ ?_
        · exact Nat.zero_le m
        · exact ⟨0, by simp [blackCount, weightedUrnDrawCounts]⟩
      obtain ⟨N, hN⟩ := hM_exists
      have hstable : ∀ n : ℕ, N ≤ n → blackCount n = M := by
        intro n hn
        have hlow : M ≤ blackCount n := by
          rw [← hN]
          exact hblack_mono hn
        have hhigh : blackCount n ≤ M := by
          exact Nat.le_findGreatest (P := fun j : ℕ ↦ ∃ n : ℕ, blackCount n = j)
            (hbound n) ⟨n, rfl⟩
        exact le_antisymm hhigh hlow
      refine ⟨N, ?_⟩
      intro n hn
      cases hdraw : weightedUrnDrawProcess n ω with
      | false =>
          rfl
      | true =>
          have hcount : blackCount n = M := hstable n hn
          have hfst : blackCount (n + 1) = M + 1 := by
            simpa [blackCount, hdraw, hcount] using
              congrArg Prod.fst (weightedUrnDrawCounts_succ n ω)
          have hfst' : blackCount (n + 1) = M := hstable (n + 1) (le_trans hn (Nat.le_succ n))
          have : M + 1 = M := by
            simp [hfst'] at hfst
          omega

-- Proof sketch: if one total color-clock time is strictly smaller than the other, then after the
-- smaller total time only the other color contributes further rings, so the draw process is
-- eventually constant. Conversely, if both colors keep ringing arbitrarily close to the same total
-- horizon, the draw process cannot be eventually monochromatic.
/-- In the exponential embedding, the total-time comparison event is exactly the source-facing
event that eventually only one color is drawn, once the individual clock increments are strictly
positive. -/
theorem mem_weightedUrnEventuallySingleColorEvent_iff
    (ω : WeightedUrnClockTrajectory)
    (hpos : ∀ color : Bool, ∀ n : ℕ, 0 < ω (color, n)) :
    ω ∈ weightedUrnEventuallySingleColorEvent ↔ ω ∈ weightedUrnOneColorFinishesFirstEvent :=
  by
    constructor
    · -- Proof comment: once one color is drawn forever, the opposite counter freezes, so the
      -- eventual tail bounds one total time strictly below the other.
      exact weightedUrnTotalTime_lt_of_eventuallyColor ω hpos
    · -- Proof comment: once one color's total horizon lies strictly before the other's, the losing
      -- color can only be drawn finitely often; the bounded losing-color count then stabilizes, so
      -- every later draw must have the winning color.
      intro hfinish
      rcases hfinish with hblack | hred
      · rcases weightedUrnEventuallyBlack_of_blackTotalTime_lt ω hblack with ⟨N, hN⟩
        exact ⟨true, N, hN⟩
      · rcases weightedUrnEventuallyRed_of_redTotalTime_lt ω hred with ⟨N, hN⟩
        exact ⟨false, N, hN⟩

/-- Helper for Example 17.27: after currying the pair-indexed clock family by color, the full real
clock family has the expected `Bool`-indexed product law of exponential rows. -/
lemma weightedUrnClockRealFamily_hasLaw_curry
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) :
    HasLaw
      (fun ω : WeightedUrnClockTrajectory ↦ fun color : Bool ↦ fun n : ℕ ↦ (ω (color, n) : ℝ))
      (Measure.infinitePi
        (fun _ : Bool ↦ Measure.infinitePi fun n : ℕ ↦ expMeasure (w n)))
      (weightedUrnClockLaw w) := by
  letI : IsProbabilityMeasure (weightedUrnClockLaw w) :=
    weightedUrnClockLaw_isProbabilityMeasure w hw
  letI : ∀ n : ℕ, IsProbabilityMeasure (expMeasure (w n)) := fun n ↦
    isProbabilityMeasure_expMeasure (hw n)
  letI : ∀ p : Bool × ℕ, IsProbabilityMeasure ((expMeasure (w p.2)).map Real.toNNReal) :=
    fun p ↦ Measure.isProbabilityMeasure_map (by fun_prop)
  have hcoordIndep :
      iIndepFun
        (fun p : Bool × ℕ ↦ fun ω : WeightedUrnClockTrajectory ↦ ω p)
        (weightedUrnClockLaw w) := by
    -- Proof comment: the clock law is an infinite product, so its coordinate projections are
    -- independent.
    simpa [weightedUrnClockLaw] using
      (iIndepFun_infinitePi
        (P := fun p : Bool × ℕ ↦ (expMeasure (w p.2)).map Real.toNNReal)
        (X := fun _ x ↦ x)
        (fun _ ↦ measurable_id))
  have hrealIndep :
      iIndepFun
        (fun p : Bool × ℕ ↦ fun ω : WeightedUrnClockTrajectory ↦ (ω p : ℝ))
        (weightedUrnClockLaw w) := by
    -- Proof comment: measurable coordinatewise coercion from `NNReal` to `ℝ` preserves
    -- independence.
    simpa using
      hcoordIndep.comp (fun _ ↦ fun x : NNReal ↦ (x : ℝ))
        (fun _ ↦ measurable_coe_nnreal_real)
  have hpair :
      HasLaw
        (fun ω : WeightedUrnClockTrajectory ↦ fun p : Bool × ℕ ↦ (ω p : ℝ))
        (Measure.infinitePi fun p : Bool × ℕ ↦ expMeasure (w p.2))
        (weightedUrnClockLaw w) := by
    refine ⟨aemeasurable_pi_iff.2 (fun p ↦
      (weightedUrnClockCoordinateReal_hasLaw w hw p.1 p.2).aemeasurable), ?_⟩
    -- Proof comment: first identify the pair-indexed family law with the infinite product of its
    -- exponential coordinate marginals.
    calc
      Measure.map (fun ω : WeightedUrnClockTrajectory ↦ fun p : Bool × ℕ ↦ (ω p : ℝ))
          (weightedUrnClockLaw w)
          =
            Measure.infinitePi
              (fun p : Bool × ℕ ↦
                Measure.map
                  (fun ω : WeightedUrnClockTrajectory ↦ (ω p : ℝ))
                  (weightedUrnClockLaw w)) := by
            exact
              (iIndepFun_iff_map_fun_eq_infinitePi_map₀'
                (P := weightedUrnClockLaw w)
                (X := fun p : Bool × ℕ ↦
                  fun ω : WeightedUrnClockTrajectory ↦ (ω p : ℝ))
                (fun p ↦
                  (weightedUrnClockCoordinateReal_hasLaw w hw p.1 p.2).aemeasurable)).1
                hrealIndep
      _ = Measure.infinitePi fun p : Bool × ℕ ↦ expMeasure (w p.2) := by
            congr 1
            funext p
            exact (weightedUrnClockCoordinateReal_hasLaw w hw p.1 p.2).map_eq
  have hcurry :
      HasLaw
        (MeasurableEquiv.curry Bool ℕ ℝ)
        (Measure.infinitePi
          (fun color : Bool ↦ Measure.infinitePi fun n : ℕ ↦ expMeasure (w n)))
        (Measure.infinitePi fun p : Bool × ℕ ↦ expMeasure (w p.2)) := by
    refine ⟨(MeasurableEquiv.curry Bool ℕ ℝ).measurable.aemeasurable, ?_⟩
    -- Proof comment: then curry the pair-indexed product law into independent color rows.
    simpa using
      (Measure.infinitePi_map_curry (μ := fun (_ : Bool) (n : ℕ) ↦ expMeasure (w n)))
  -- Proof comment: composing the pair law with the measurable curry equivalence produces the row
  -- family law needed for the final theorem.
  simpa [Function.comp] using hcurry.comp hpair

/-- Helper for Example 17.27: the black and red real-valued clock rows are independent under the
curried product law of the exponential embedding. -/
lemma weightedUrnClockRowFamily_iIndep
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) :
    iIndepFun
      (fun color : Bool ↦
        fun ω : WeightedUrnClockTrajectory ↦ fun n : ℕ ↦ (ω (color, n) : ℝ))
      (weightedUrnClockLaw w) := by
  letI : IsProbabilityMeasure (weightedUrnClockLaw w) :=
    weightedUrnClockLaw_isProbabilityMeasure w hw
  letI : ∀ n : ℕ, IsProbabilityMeasure (expMeasure (w n)) := fun n ↦
    isProbabilityMeasure_expMeasure (hw n)
  have hfamily := weightedUrnClockRealFamily_hasLaw_curry w hw
  have hrow :
      ∀ color : Bool,
        HasLaw
          (fun ω : WeightedUrnClockTrajectory ↦ fun n : ℕ ↦ (ω (color, n) : ℝ))
          (Measure.infinitePi fun n : ℕ ↦ expMeasure (w n))
          (weightedUrnClockLaw w) := by
    intro color
    have heval :
        HasLaw
          (Function.eval color)
          (Measure.infinitePi fun n : ℕ ↦ expMeasure (w n))
          (Measure.infinitePi
            (fun color : Bool ↦ Measure.infinitePi fun n : ℕ ↦ expMeasure (w n))) := by
      exact
        (measurePreserving_eval_infinitePi
          (fun color : Bool ↦ Measure.infinitePi fun n : ℕ ↦ expMeasure (w n)) color).hasLaw
    -- Proof comment: evaluate the joint row-family law at a fixed color to recover that row's
    -- marginal.
    simpa [Function.comp] using heval.comp hfamily
  -- Proof comment: compare the joint row-family law with the infinite product of its row
  -- marginals to recover rowwise independence.
  refine
    (iIndepFun_iff_map_fun_eq_infinitePi_map₀'
      (P := weightedUrnClockLaw w)
      (X := fun color : Bool ↦
        fun ω : WeightedUrnClockTrajectory ↦ fun n : ℕ ↦ (ω (color, n) : ℝ))
      (fun color ↦ (hrow color).aemeasurable)).2 ?_
  calc
    Measure.map
        (fun ω : WeightedUrnClockTrajectory ↦
          fun color : Bool ↦ fun n : ℕ ↦ (ω (color, n) : ℝ))
        (weightedUrnClockLaw w)
        =
          Measure.infinitePi
            (fun color : Bool ↦ Measure.infinitePi fun n : ℕ ↦ expMeasure (w n)) :=
      hfamily.map_eq
    _ =
        Measure.infinitePi
          (fun color : Bool ↦
            Measure.map
              (fun ω : WeightedUrnClockTrajectory ↦ fun n : ℕ ↦ (ω (color, n) : ℝ))
              (weightedUrnClockLaw w)) := by
          congr 1
          funext color
          symm
          exact (hrow color).map_eq

/-- The real-valued total time of one color row, obtained by summing the nonnegative row entries
as an `ℝ≥0∞` series and then taking `toReal`. -/
def weightedUrnRowTotalTimeToReal (x : ℕ → ℝ) : ℝ :=
  ENNReal.toReal (∑' n : ℕ, ENNReal.ofReal (x n))

/-- Helper for Example 17.27: split a real row into its head entry and the shifted tail row, and
glue such a pair back into a full row. -/
noncomputable def weightedUrnRowHeadTailEquiv : (ℝ × (ℕ → ℝ)) ≃ᵐ (ℕ → ℝ) where
  toFun p
    | 0 => p.1
    | n + 1 => p.2 n
  invFun x := (x 0, fun n : ℕ ↦ x (n + 1))
  left_inv := by
    intro p
    ext <;> rfl
  right_inv := by
    intro x
    funext n
    cases n <;> rfl
  measurable_toFun := by
    -- Proof comment: every output coordinate is either the head projection or one shifted tail
    -- coordinate.
    refine measurable_pi_lambda _ fun n ↦ ?_
    cases n with
    | zero =>
        simpa using measurable_fst
    | succ n =>
        simpa using (measurable_pi_apply n).comp measurable_snd
  measurable_invFun := by
    -- Proof comment: the inverse packages the `0`th coordinate together with the shifted tail
    -- coordinate projections.
    refine (measurable_pi_apply 0).prodMk ?_
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa using (measurable_pi_apply (n + 1 : ℕ))

/-- Helper for Example 17.27: `Nat.succ` is injective on the preimage of any finite set. -/
lemma natSucc_injOn_preimage_finset (s : Finset ℕ) :
    Set.InjOn Nat.succ (Nat.succ ⁻¹' (s : Set ℕ)) := by
  intro a ha b hb hab
  exact Nat.succ_injective hab

/-- Helper for Example 17.27: finite-coordinate boxes on the row space pull back through
`weightedUrnRowHeadTailEquiv` to the corresponding head constraint and shifted tail box. -/
lemma weightedUrnRowHeadTailEquiv_preimage_pi
    (s : Finset ℕ) (t : ℕ → Set ℝ) :
    weightedUrnRowHeadTailEquiv ⁻¹' Set.pi s t =
      ((if 0 ∈ s then t 0 else Set.univ) ×ˢ
        Set.pi (s.preimage Nat.succ (natSucc_injOn_preimage_finset s))
          (fun n : ℕ ↦ t (n + 1))) := by
  -- Proof comment: the head entry controls exactly coordinate `0`, while every positive row
  -- coordinate corresponds to one tail coordinate shifted by `1`.
  ext p
  simp only [Set.mem_preimage, Set.mem_prod, Set.mem_pi]
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    · by_cases h0 : 0 ∈ s
      · simpa [weightedUrnRowHeadTailEquiv, h0] using hp 0 h0
      · simp [h0]
    · intro n hn
      have hsucc : n + 1 ∈ s := by
        simpa using hn
      simpa [weightedUrnRowHeadTailEquiv] using hp (n + 1) hsucc
  · rintro ⟨hhead, htail⟩ n hn
    cases n with
    | zero =>
        have h0 : 0 ∈ s := hn
        simpa [weightedUrnRowHeadTailEquiv, h0] using hhead
    | succ n =>
        have htailMem : n ∈ s.preimage Nat.succ (natSucc_injOn_preimage_finset s) := by
          simpa using hn
        simpa [weightedUrnRowHeadTailEquiv] using htail n htailMem

/-- Helper for Example 17.27: shifting a finite product over the successor-preimage of a finite
set matches the product over the positive coordinates of the original set. -/
lemma prod_preimage_succ_eq_prod_erase_zero
    {α : Type*} [CommMonoid α] (s : Finset ℕ) (F : ℕ → α) :
    ∏ n ∈ s.preimage Nat.succ (natSucc_injOn_preimage_finset s), F (n + 1) =
      ∏ n ∈ s.erase 0, F n := by
  classical
  -- Proof comment: `n ↦ n + 1` bijects the successor-preimage of `s` with the positive elements
  -- of `s`.
  refine Finset.prod_bij (fun n _ ↦ n + 1) ?_ ?_ ?_ ?_
  · intro n hn
    refine Finset.mem_erase.2 ⟨Nat.succ_ne_zero n, ?_⟩
    simpa using hn
  · intro a₁ _ a₂ _ hEq
    exact Nat.succ_injective hEq
  · intro b hb
    rcases Nat.exists_eq_succ_of_ne_zero (Finset.mem_erase.1 hb).1 with ⟨a, rfl⟩
    refine ⟨a, ?_, rfl⟩
    simpa using (Finset.mem_erase.1 hb).2
  · intro n hn
    rfl

/-- Helper for Example 17.27: the real-valued row total-time functional is measurable on the
product row space. -/
lemma measurable_weightedUrnRowTotalTimeToReal :
    Measurable (weightedUrnRowTotalTimeToReal : (ℕ → ℝ) → ℝ) := by
  -- Proof comment: the row total time is the composition of the measurable nonnegative series map
  -- with `ENNReal.toReal`.
  refine ENNReal.measurable_toReal.comp ?_
  exact Measurable.ennreal_tsum fun n ↦ (measurable_pi_apply n).ennreal_ofReal

/-- Helper for Example 17.27: once the shifted tail sum is finite, the row total splits into the
head coordinate plus the shifted tail total. -/
lemma weightedUrnRowTotalTimeToReal_cons
    (x : ℕ → ℝ)
    (hhead : 0 ≤ x 0)
    (htail : (∑' n : ℕ, ENNReal.ofReal (x (n + 1))) < ∞) :
    weightedUrnRowTotalTimeToReal x =
      x 0 + weightedUrnRowTotalTimeToReal (fun n : ℕ ↦ x (n + 1)) := by
  have hsplit :
      ∑' n : ℕ, ENNReal.ofReal (x n) =
        ENNReal.ofReal (x 0) + ∑' n : ℕ, ENNReal.ofReal (x (n + 1)) := by
    -- Proof comment: split the nonnegative series into its initial term and the shifted tail.
    simpa using (tsum_eq_zero_add' (f := fun n : ℕ ↦ ENNReal.ofReal (x n)) ENNReal.summable)
  -- Proof comment: after the deterministic series split, `ENNReal.toReal_add` turns the total
  -- time into the head coordinate plus the tail total.
  rw [weightedUrnRowTotalTimeToReal, hsplit, ENNReal.toReal_add (by simp) htail.ne,
    ENNReal.toReal_ofReal hhead]
  simp [weightedUrnRowTotalTimeToReal]

/-- Helper for Example 17.27: for a fixed color, the full real-valued clock row has the expected
independent product law of exponentials. -/
lemma weightedUrnColorRow_hasLaw
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) (color : Bool) :
    HasLaw
      (fun ω : WeightedUrnClockTrajectory ↦ fun n : ℕ ↦ (ω (color, n) : ℝ))
      (Measure.infinitePi fun n : ℕ ↦ expMeasure (w n))
      (weightedUrnClockLaw w) := by
  letI : IsProbabilityMeasure (weightedUrnClockLaw w) :=
    weightedUrnClockLaw_isProbabilityMeasure w hw
  letI : ∀ n : ℕ, IsProbabilityMeasure (expMeasure (w n)) := fun n ↦
    isProbabilityMeasure_expMeasure (hw n)
  have hfamily := weightedUrnClockRealFamily_hasLaw_curry w hw
  have heval :
      HasLaw
        (Function.eval color)
        (Measure.infinitePi fun n : ℕ ↦ expMeasure (w n))
        (Measure.infinitePi
          (fun color : Bool ↦ Measure.infinitePi fun n : ℕ ↦ expMeasure (w n))) := by
    -- Proof comment: evaluating the `Bool`-indexed row family at one fixed color returns the
    -- corresponding row marginal of the product law.
    exact
      (measurePreserving_eval_infinitePi
        (fun color : Bool ↦ Measure.infinitePi fun n : ℕ ↦ expMeasure (w n)) color).hasLaw
  -- Proof comment: compose the curried family law with evaluation at `color` to recover the law
  -- of that single exponential row.
  simpa [Function.comp] using heval.comp hfamily

/-- Helper for Example 17.27: the canonical row product law splits into the first exponential
coordinate and the shifted tail product law under `weightedUrnRowHeadTailEquiv.symm`. -/
lemma weightedUrnRowHeadTail_map_infinitePi
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) :
    Measure.map
      (fun x : ℕ → ℝ ↦ (x 0, fun n : ℕ ↦ x (n + 1)))
      (Measure.infinitePi fun n : ℕ ↦ expMeasure (w n)) =
        (expMeasure (w 0)).prod (Measure.infinitePi fun n : ℕ ↦ expMeasure (w (n + 1))) := by
  classical
  let νTail : Measure (ℕ → ℝ) := Measure.infinitePi fun n : ℕ ↦ expMeasure (w (n + 1))
  have hreverse :
      Measure.map weightedUrnRowHeadTailEquiv ((expMeasure (w 0)).prod νTail) =
        Measure.infinitePi fun n : ℕ ↦ expMeasure (w n) := by
    letI : ∀ n : ℕ, IsProbabilityMeasure (expMeasure (w n)) := fun n ↦
      isProbabilityMeasure_expMeasure (hw n)
    letI : IsProbabilityMeasure (expMeasure (w 0)) := isProbabilityMeasure_expMeasure (hw 0)
    letI : ∀ n : ℕ, IsProbabilityMeasure (expMeasure (w (n + 1))) := fun n ↦
      isProbabilityMeasure_expMeasure (hw (n + 1))
    letI : IsProbabilityMeasure νTail := by
      dsimp [νTail]
      infer_instance
    -- Proof comment: match the reverse pushforward with the canonical row product law on finite
    -- cylinders, where the available head/tail preimage lemma has the correct orientation.
    apply Measure.eq_infinitePi (μ := fun n : ℕ ↦ expMeasure (w n))
    intro s t ht
    have hpiMeas : MeasurableSet (Set.pi s t) := by
      exact MeasurableSet.pi s.countable_toSet fun i _ ↦ ht i
    have hheadMeas : MeasurableSet (if 0 ∈ s then t 0 else (Set.univ : Set ℝ)) := by
      by_cases h0 : 0 ∈ s
      · simpa [h0] using ht 0
      · simp [h0]
    have htailMeas :
        MeasurableSet
          (Set.pi (s.preimage Nat.succ (natSucc_injOn_preimage_finset s))
            (fun n : ℕ ↦ t (n + 1))) := by
      exact
        MeasurableSet.pi (s.preimage Nat.succ (natSucc_injOn_preimage_finset s)).countable_toSet
          fun n _ ↦ ht (n + 1)
    have htailPi :
        νTail
            (Set.pi (s.preimage Nat.succ (natSucc_injOn_preimage_finset s))
              (fun n : ℕ ↦ t (n + 1))) =
          ∏ n ∈ s.preimage Nat.succ (natSucc_injOn_preimage_finset s),
            expMeasure (w (n + 1)) (t (n + 1)) := by
      simpa [νTail] using
        (Measure.infinitePi_pi
          (μ := fun n : ℕ ↦ expMeasure (w (n + 1)))
          (s := s.preimage Nat.succ (natSucc_injOn_preimage_finset s))
          (t := fun n : ℕ ↦ t (n + 1))
          (fun n _ ↦ ht (n + 1)))
    have htailShift :
        ∏ n ∈ s.preimage Nat.succ (natSucc_injOn_preimage_finset s),
            expMeasure (w (n + 1)) (t (n + 1)) =
          ∏ n ∈ s.erase 0, expMeasure (w n) (t n) := by
      simpa using
        (prod_preimage_succ_eq_prod_erase_zero
          (s := s) (F := fun n : ℕ ↦ expMeasure (w n) (t n)))
    calc
      (Measure.map weightedUrnRowHeadTailEquiv ((expMeasure (w 0)).prod νTail)) (Set.pi s t)
          = ((expMeasure (w 0)).prod νTail) (weightedUrnRowHeadTailEquiv ⁻¹' Set.pi s t) := by
              simpa using
                (Measure.map_apply (μ := (expMeasure (w 0)).prod νTail)
                  weightedUrnRowHeadTailEquiv.measurable hpiMeas)
      _ = ((expMeasure (w 0)).prod νTail)
            (((if 0 ∈ s then t 0 else Set.univ) ×ˢ
              Set.pi (s.preimage Nat.succ (natSucc_injOn_preimage_finset s))
                (fun n : ℕ ↦ t (n + 1)))) := by
            rw [weightedUrnRowHeadTailEquiv_preimage_pi]
      _ = (expMeasure (w 0)) (if 0 ∈ s then t 0 else Set.univ) *
            νTail
              (Set.pi (s.preimage Nat.succ (natSucc_injOn_preimage_finset s))
                (fun n : ℕ ↦ t (n + 1))) := by
            rw [Measure.prod_prod]
      _ = (expMeasure (w 0)) (if 0 ∈ s then t 0 else Set.univ) *
            ∏ n ∈ s.erase 0, expMeasure (w n) (t n) := by
            rw [htailPi, htailShift]
      _ = ∏ n ∈ s, expMeasure (w n) (t n) := by
            by_cases h0 : 0 ∈ s
            · rw [if_pos h0]
              simpa using
                (Finset.mul_prod_erase (s := s) (f := fun n : ℕ ↦ expMeasure (w n) (t n))
                  (h := h0))
            · rw [if_neg h0]
              simp [Finset.erase_eq_self.mpr h0]
  -- Proof comment: once the reverse pushforward is identified, map back through the inverse
  -- measurable equivalence to recover the original head/tail pushforward statement.
  have hmapBack :
      Measure.map weightedUrnRowHeadTailEquiv.symm
          (Measure.map weightedUrnRowHeadTailEquiv ((expMeasure (w 0)).prod νTail)) =
        Measure.map weightedUrnRowHeadTailEquiv.symm
          (Measure.infinitePi fun n : ℕ ↦ expMeasure (w n)) := by
    exact congrArg (Measure.map weightedUrnRowHeadTailEquiv.symm) hreverse
  simpa [νTail, Function.comp] using hmapBack.symm

/-- Helper for Example 17.27: under the shifted exponential row product law, the shifted row
total clock time is almost surely finite when `∑ n, 1 / w n` converges. -/
lemma weightedUrnShiftedRowTotal_ae_lt_top
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n)
    (hsummable : Summable fun n : ℕ ↦ 1 / w n) :
    ∀ᵐ y ∂ Measure.infinitePi fun n : ℕ ↦ expMeasure (w (n + 1)),
      (∑' n : ℕ, ENNReal.ofReal (y n)) < ∞ := by
  let wShift : ℕ → ℝ := fun n : ℕ ↦ w (n + 1)
  have hsummableShift : Summable fun n : ℕ ↦ 1 / wShift n := by
    simpa [wShift] using hsummable.comp_injective Nat.succ_injective
  have hrowLaw :
      HasLaw
        (fun ω : WeightedUrnClockTrajectory ↦ fun n : ℕ ↦ (ω (true, n) : ℝ))
        (Measure.infinitePi fun n : ℕ ↦ expMeasure (wShift n))
        (weightedUrnClockLaw wShift) :=
    weightedUrnColorRow_hasLaw wShift (fun n ↦ hw (n + 1)) true
  have hfiniteSource :
      ∀ᵐ ω ∂ weightedUrnClockLaw wShift, weightedUrnColorTotalTime true ω < ∞ :=
    weightedUrnColorTotalTime_ae_lt_top wShift (fun n ↦ hw (n + 1)) hsummableShift true
  have htailMeas :
      Measurable (fun y : ℕ → ℝ ↦ (∑' n : ℕ, ENNReal.ofReal (y n)) < ∞) := by
    have hsumMeas :
        Measurable (fun y : ℕ → ℝ ↦ ∑' n : ℕ, ENNReal.ofReal (y n)) := by
      exact Measurable.ennreal_tsum fun n ↦ (measurable_pi_apply n).ennreal_ofReal
    simpa using hsumMeas.lt measurable_const
  -- Proof comment: transport the already-proved almost-sure finiteness of one color total time
  -- through the shifted row law.
  exact
    (hrowLaw.ae_iff
      (p := fun y : ℕ → ℝ ↦ (∑' n : ℕ, ENNReal.ofReal (y n)) < ∞) htailMeas).1 <|
      by
        simpa [wShift, weightedUrnColorTotalTime] using hfiniteSource

/-- Helper for Example 17.27: the real total-time observable of one color is measurable. -/
lemma measurable_weightedUrnColorTotalTime_toReal (color : Bool) :
    Measurable
      (fun ω : WeightedUrnClockTrajectory ↦
        ENNReal.toReal (weightedUrnColorTotalTime color ω)) := by
  -- Proof comment: the color total time is an `ℝ≥0∞` series of measurable coordinates, followed
  -- by `ENNReal.toReal`.
  refine ENNReal.measurable_toReal.comp ?_
  simpa [weightedUrnColorTotalTime] using
    (Measurable.ennreal_tsum fun n ↦ (measurable_pi_apply (color, n)).coe_nnreal_ennreal)

/-- Helper for Example 17.27: after selecting one color row, the first coordinate and the shifted
tail row have the product law of an exponential head and an independent exponential tail family. -/
lemma weightedUrnColorRowHeadTail_map_eq_prod
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) (color : Bool) :
    Measure.map
      (fun ω : WeightedUrnClockTrajectory ↦
        ((ω (color, 0) : ℝ), fun n : ℕ ↦ (ω (color, n + 1) : ℝ)))
      (weightedUrnClockLaw w) =
        (expMeasure (w 0)).prod (Measure.infinitePi fun n : ℕ ↦ expMeasure (w (n + 1))) := by
  let row : WeightedUrnClockTrajectory → (ℕ → ℝ) :=
    fun ω n ↦ (ω (color, n) : ℝ)
  have hrowMeas : Measurable row := by
    refine measurable_pi_lambda _ fun n ↦ ?_
    exact measurable_coe_nnreal_real.comp (measurable_pi_apply (color, n))
  have hsplit :
      (fun ω : WeightedUrnClockTrajectory ↦
        ((ω (color, 0) : ℝ), fun n : ℕ ↦ (ω (color, n + 1) : ℝ))) =
        weightedUrnRowHeadTailEquiv.symm ∘ row := by
    -- Proof comment: the concrete head/tail split is exactly the inverse row equivalence applied
    -- to the selected color row.
    funext ω
    rfl
  -- Proof comment: first transport to the canonical one-color row law, then apply the already
  -- proved row head/tail factorization.
  calc
    Measure.map
        (fun ω : WeightedUrnClockTrajectory ↦
          ((ω (color, 0) : ℝ), fun n : ℕ ↦ (ω (color, n + 1) : ℝ)))
        (weightedUrnClockLaw w)
        =
      Measure.map weightedUrnRowHeadTailEquiv.symm (Measure.map row (weightedUrnClockLaw w)) := by
          rw [hsplit, Measure.map_map weightedUrnRowHeadTailEquiv.symm.measurable hrowMeas]
    _ = Measure.map weightedUrnRowHeadTailEquiv.symm
          (Measure.infinitePi fun n : ℕ ↦ expMeasure (w n)) := by
            rw [(weightedUrnColorRow_hasLaw w hw color).map_eq]
    _ = (expMeasure (w 0)).prod (Measure.infinitePi fun n : ℕ ↦ expMeasure (w (n + 1))) := by
          exact weightedUrnRowHeadTail_map_infinitePi w hw

/-- Helper for Example 17.27: the real-valued total time of one fixed color has no atoms under the
exponential-clock law when `∑ 1 / w n` converges. -/
lemma weightedUrnColorTotalTime_toReal_singleton_eq_zero
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n)
    (hsummable : Summable fun n : ℕ ↦ 1 / w n)
    (color : Bool) (t : ℝ) :
    Measure.map
      (fun ω : WeightedUrnClockTrajectory ↦ ENNReal.toReal (weightedUrnColorTotalTime color ω))
      (weightedUrnClockLaw w) {t} = 0 := by
  let νTail : Measure (ℕ → ℝ) := Measure.infinitePi fun n : ℕ ↦ expMeasure (w (n + 1))
  let ν : Measure (ℝ × (ℕ → ℝ)) := (expMeasure (w 0)).prod νTail
  let split : WeightedUrnClockTrajectory → ℝ × (ℕ → ℝ) := fun ω ↦
    ((ω (color, 0) : ℝ), fun n : ℕ ↦ (ω (color, n + 1) : ℝ))
  let totalOnPair : ℝ × (ℕ → ℝ) → ℝ := fun p ↦
    weightedUrnRowTotalTimeToReal (weightedUrnRowHeadTailEquiv p)
  let tailFinite : Set (ℕ → ℝ) := {y | (∑' n : ℕ, ENNReal.ofReal (y n)) < ∞}
  let good : Set (ℝ × (ℕ → ℝ)) := {p | 0 ≤ p.1 ∧ p.2 ∈ tailFinite}
  let graph : Set (ℝ × (ℕ → ℝ)) := {p | p.1 = t - weightedUrnRowTotalTimeToReal p.2}
  have hsplitMeas : Measurable split := by
    refine (measurable_coe_nnreal_real.comp (measurable_pi_apply (color, 0))).prodMk ?_
    refine measurable_pi_lambda _ fun n ↦ ?_
    exact measurable_coe_nnreal_real.comp (measurable_pi_apply (color, n + 1))
  have htotalOnPairMeas : Measurable totalOnPair := by
    exact measurable_weightedUrnRowTotalTimeToReal.comp weightedUrnRowHeadTailEquiv.measurable
  have htailFiniteMeas : MeasurableSet tailFinite := by
    have hsumMeas :
        Measurable (fun y : ℕ → ℝ ↦ ∑' n : ℕ, ENNReal.ofReal (y n)) := by
      exact Measurable.ennreal_tsum fun n ↦ (measurable_pi_apply n).ennreal_ofReal
    simpa only [tailFinite, Set.preimage_setOf_eq] using
      (measurableSet_Iio : MeasurableSet (Set.Iio (∞ : ℝ≥0∞))).preimage hsumMeas
  letI : IsProbabilityMeasure (expMeasure (w 0)) := isProbabilityMeasure_expMeasure (hw 0)
  letI : ∀ n : ℕ, IsProbabilityMeasure (expMeasure (w (n + 1))) := fun n ↦
    isProbabilityMeasure_expMeasure (hw (n + 1))
  letI : IsProbabilityMeasure νTail := by
    dsimp [νTail]
    infer_instance
  letI : SFinite νTail := inferInstance
  have htailFiniteAe : ∀ᵐ y ∂ νTail, y ∈ tailFinite := by
    simpa [νTail, tailFinite] using weightedUrnShiftedRowTotal_ae_lt_top w hw hsummable
  have htailBadZero : ν ((Set.univ : Set ℝ) ×ˢ tailFiniteᶜ) = 0 := by
    have htailBad : νTail (tailFiniteᶜ) = 0 := by
      rw [ae_iff] at htailFiniteAe
      simpa using htailFiniteAe
    rw [Measure.prod_prod, htailBad]
    simp
  have hheadNonnegAe : ∀ᵐ x ∂ expMeasure (w 0), 0 ≤ x :=
    aeNonnegOfHasLawExp (HasLaw.id (μ := expMeasure (w 0)))
  have hheadBadZero : ν {p : ℝ × (ℕ → ℝ) | p.1 < 0} = 0 := by
    have hheadBad : expMeasure (w 0) {x : ℝ | x < 0} = 0 := by
      rw [ae_iff] at hheadNonnegAe
      simpa [not_le] using hheadNonnegAe
    have hstrip :
        {p : ℝ × (ℕ → ℝ) | p.1 < 0} = ({x : ℝ | x < 0} ×ˢ (Set.univ : Set (ℕ → ℝ))) := by
      ext p
      simp
    rw [hstrip, Measure.prod_prod, hheadBad]
    simp
  have hgoodCompl :
      goodᶜ = {p : ℝ × (ℕ → ℝ) | p.1 < 0} ∪ ((Set.univ : Set ℝ) ×ˢ tailFiniteᶜ) := by
    ext p
    by_cases hhead : 0 ≤ p.1
    · simp [good, tailFinite, hhead]
    · have hlt : p.1 < 0 := lt_of_not_ge hhead
      simp [good, tailFinite, hhead, hlt]
  have hgoodBadZero : ν goodᶜ = 0 := by
    rw [hgoodCompl]
    exact measure_union_null hheadBadZero htailBadZero
  have hgraphZero : ν graph = 0 := by
    -- Proof comment: under the product law, the singleton fiber is contained in a measurable
    -- graph over the tail row, and the atomless first marginal kills that graph.
    letI : NoAtoms (expMeasure (w 0)) := ⟨expMeasure_singleton_eq_zero (w 0)⟩
    simpa [ν, graph] using
      (prod_graph_eq_zero_of_noAtoms_fst
        (μ := expMeasure (w 0)) (ν := νTail)
        (g := fun y : ℕ → ℝ ↦ t - weightedUrnRowTotalTimeToReal y)
        (measurable_const.sub measurable_weightedUrnRowTotalTimeToReal))
  have hpreimageSubset :
      totalOnPair ⁻¹' {t} ⊆ goodᶜ ∪ graph := by
    intro p hp
    by_cases hgood : p ∈ good
    · right
      rcases hgood with ⟨hhead, htail⟩
      have hsplitTotal :
          totalOnPair p = p.1 + weightedUrnRowTotalTimeToReal p.2 := by
        -- Proof comment: on the full-measure good set, the row total splits into the head
        -- coordinate plus the shifted tail total.
        simpa [totalOnPair, weightedUrnRowHeadTailEquiv] using
          (weightedUrnRowTotalTimeToReal_cons (x := weightedUrnRowHeadTailEquiv p) hhead
            (by simpa [weightedUrnRowHeadTailEquiv, tailFinite] using htail))
      have hpEq : totalOnPair p = t := by simpa using hp
      have hgraphEq : p.1 = t - weightedUrnRowTotalTimeToReal p.2 := by
        linarith [hsplitTotal, hpEq]
      simpa [graph] using hgraphEq
    · left
      simpa [good] using hgood
  have hpreimageZero : ν (totalOnPair ⁻¹' {t}) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      ν (totalOnPair ⁻¹' {t}) ≤ ν (goodᶜ ∪ graph) := measure_mono hpreimageSubset
      _ ≤ ν goodᶜ + ν graph := measure_union_le _ _
      _ = 0 := by rw [hgoodBadZero, hgraphZero, zero_add]
  have hcomp :
      (fun ω : WeightedUrnClockTrajectory ↦ ENNReal.toReal (weightedUrnColorTotalTime color ω)) =
        totalOnPair ∘ split := by
    -- Proof comment: the concrete color total time factors through the head/tail split as the row
    -- total-time functional on the reconstructed row.
    funext ω
    have hrow :
        weightedUrnRowHeadTailEquiv (split ω) = fun n : ℕ ↦ (ω (color, n) : ℝ) := by
      funext n
      cases n <;> rfl
    simp [totalOnPair, split, weightedUrnColorTotalTime, weightedUrnRowTotalTimeToReal, hrow]
  calc
    Measure.map
        (fun ω : WeightedUrnClockTrajectory ↦ ENNReal.toReal (weightedUrnColorTotalTime color ω))
        (weightedUrnClockLaw w) {t}
        =
      Measure.map totalOnPair (Measure.map split (weightedUrnClockLaw w)) {t} := by
          rw [hcomp, Measure.map_map htotalOnPairMeas hsplitMeas]
    _ = Measure.map totalOnPair ν {t} := by
          rw [weightedUrnColorRowHeadTail_map_eq_prod w hw color]
    _ = ν (totalOnPair ⁻¹' {t}) := by
          rw [Measure.map_apply (μ := ν) htotalOnPairMeas (measurableSet_singleton t)]
    _ = 0 := hpreimageZero

/-- Helper for Example 17.27: after currying the clock family by color, composing each row with
the row total-time functional yields independent black and red total clock times in `ℝ`. -/
lemma weightedUrnBlackRedTotalTime_toReal_indep
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) :
    IndepFun
      (fun ω : WeightedUrnClockTrajectory ↦ ENNReal.toReal (weightedUrnBlackTotalTime ω))
      (fun ω : WeightedUrnClockTrajectory ↦ ENNReal.toReal (weightedUrnRedTotalTime ω))
      (weightedUrnClockLaw w) := by
  have hrows := weightedUrnClockRowFamily_iIndep w hw
  have hrowIndep :
      IndepFun
        (fun ω : WeightedUrnClockTrajectory ↦ fun n : ℕ ↦ (ω (true, n) : ℝ))
        (fun ω : WeightedUrnClockTrajectory ↦ fun n : ℕ ↦ (ω (false, n) : ℝ))
        (weightedUrnClockLaw w) :=
    hrows.indepFun (show true ≠ false by decide)
  have hcomp :
      IndepFun
        (fun ω : WeightedUrnClockTrajectory ↦
          weightedUrnRowTotalTimeToReal (fun n : ℕ ↦ (ω (true, n) : ℝ)))
        (fun ω : WeightedUrnClockTrajectory ↦
          weightedUrnRowTotalTimeToReal (fun n : ℕ ↦ (ω (false, n) : ℝ)))
        (weightedUrnClockLaw w) :=
    hrowIndep.comp measurable_weightedUrnRowTotalTimeToReal
      measurable_weightedUrnRowTotalTimeToReal
  have hblackEq :
      (fun ω : WeightedUrnClockTrajectory ↦
        weightedUrnRowTotalTimeToReal (fun n : ℕ ↦ (ω (true, n) : ℝ))) =ᵐ[weightedUrnClockLaw w]
        fun ω : WeightedUrnClockTrajectory ↦ ENNReal.toReal (weightedUrnBlackTotalTime ω) := by
    -- Proof comment: on `NNReal` coordinates, the row-level `ofReal` spelling is definitionally
    -- the same as the original black total time.
    filter_upwards with ω
    simp [weightedUrnRowTotalTimeToReal, weightedUrnBlackTotalTime, weightedUrnColorTotalTime]
  have hredEq :
      (fun ω : WeightedUrnClockTrajectory ↦
        weightedUrnRowTotalTimeToReal (fun n : ℕ ↦ (ω (false, n) : ℝ))) =ᵐ[weightedUrnClockLaw w]
        fun ω : WeightedUrnClockTrajectory ↦ ENNReal.toReal (weightedUrnRedTotalTime ω) := by
    -- Proof comment: the same pointwise identification holds for the red row.
    filter_upwards with ω
    simp [weightedUrnRowTotalTimeToReal, weightedUrnRedTotalTime, weightedUrnColorTotalTime]
  -- Proof comment: measurable postcomposition of the independent black and red rows by the same
  -- total-time functional preserves independence.
  exact hcomp.congr hblackEq hredEq

/-- Helper for Example 17.27: the black and red total clock times are almost surely unequal under
the exponential-clock law. -/
lemma weightedUrnTotalTimes_equal_zero_measure
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n)
    (hsummable : Summable fun n : ℕ ↦ 1 / w n) :
    weightedUrnClockLaw w {ω | weightedUrnBlackTotalTime ω = weightedUrnRedTotalTime ω} = 0 := by
  letI : IsProbabilityMeasure (weightedUrnClockLaw w) :=
    weightedUrnClockLaw_isProbabilityMeasure w hw
  let f : WeightedUrnClockTrajectory → ℝ :=
    fun ω ↦ ENNReal.toReal (weightedUrnBlackTotalTime ω)
  let g : WeightedUrnClockTrajectory → ℝ :=
    fun ω ↦ ENNReal.toReal (weightedUrnRedTotalTime ω)
  let μBlack : Measure ℝ := Measure.map f (weightedUrnClockLaw w)
  let μRed : Measure ℝ := Measure.map g (weightedUrnClockLaw w)
  have hpair :
      Measure.map (fun ω : WeightedUrnClockTrajectory ↦ (f ω, g ω)) (weightedUrnClockLaw w) =
        μBlack.prod μRed := by
    -- Proof comment: the already-proved independence of the two real total-time observables turns
    -- their joint law into the product of the two marginals.
    exact
      (indepFun_iff_map_prod_eq_prod_map_map
        (by
          simpa [f] using
            (measurable_weightedUrnColorTotalTime_toReal true).aemeasurable)
        (by
          simpa [g] using
            (measurable_weightedUrnColorTotalTime_toReal false).aemeasurable)).1
        (weightedUrnBlackRedTotalTime_toReal_indep w hw)
  haveI : NoAtoms μBlack := by
    refine ⟨fun t ↦ ?_⟩
    -- Proof comment: the black real total-time law has no singleton atoms by the one-color
    -- singleton-zero lemma.
    simpa [μBlack, f] using
      weightedUrnColorTotalTime_toReal_singleton_eq_zero w hw hsummable true t
  have hdiagReal :
      Measure.map (fun ω : WeightedUrnClockTrajectory ↦ (f ω, g ω)) (weightedUrnClockLaw w)
        {p : ℝ × ℝ | p.1 = p.2} = 0 := by
    -- Proof comment: an atomless first marginal kills the diagonal graph in the product of the
    -- two real total-time laws.
    rw [hpair]
    simpa using
      (prod_graph_eq_zero_of_noAtoms_fst (μ := μBlack) (ν := μRed)
        (g := fun x : ℝ ↦ x) measurable_id)
  have hsubset :
      {ω | weightedUrnBlackTotalTime ω = weightedUrnRedTotalTime ω} ⊆
        {ω | f ω = g ω} := by
    -- Proof comment: equality of the `ℝ≥0∞` total times forces equality after applying
    -- `ENNReal.toReal`.
    intro ω hω
    simpa [f, g] using congrArg ENNReal.toReal hω
  have hpreimage :
      {ω | f ω = g ω} =
        (fun ω : WeightedUrnClockTrajectory ↦ (f ω, g ω)) ⁻¹' {p : ℝ × ℝ | p.1 = p.2} := by
    ext ω
    simp [f, g]
  -- Proof comment: the equal-total event embeds into the real diagonal event under the pair map,
  -- whose measure is already zero.
  refine measure_mono_null hsubset ?_
  rw [hpreimage, ← Measure.map_apply
    (show Measurable (fun ω : WeightedUrnClockTrajectory ↦ (f ω, g ω)) by
      have hblack : Measurable f := by
        simpa [f] using measurable_weightedUrnColorTotalTime_toReal true
      have hred : Measurable g := by
        simpa [g] using measurable_weightedUrnColorTotalTime_toReal false
      exact hblack.prodMk hred)
    (by
      exact measurableSet_eq_fun measurable_fst measurable_snd)]
  exact hdiagReal

-- Proof sketch: the summability hypothesis makes the black and red total clock times almost surely
-- finite. Under the product law `weightedUrnClockLaw w`, the two color-clock families are
-- independent, so the two total times are independent as well. Each total time has a density
-- because it is an exponential variable convolved with an independent remainder. Hence the
-- diagonal event where the two total times agree has probability zero, so almost surely one color
-- finishes first.
/-- A summability consequence for Example 17.27: if `∑ n, 1 / w n` is summable, then in the
exponential-clock realization of the weighted Pólya urn with rates `w n`, almost surely one color
finishes all of its clock time strictly before the other. Equivalently, the induced generalized
urn process eventually draws only one color. -/
theorem weightedUrnClockLaw_ae_eventually_single_color
    (w : ℕ → ℝ) (hw : ∀ n : ℕ, 0 < w n) (hsummable : Summable fun n : ℕ ↦ 1 / w n) :
    ∀ᵐ ω ∂ weightedUrnClockLaw w, ω ∈ weightedUrnEventuallySingleColorEvent :=
  -- Route correction: the original-space diagonal transport was the wrong layer. The curried row
  -- law and the independence of the two real total-time maps are now available above; the missing
  -- step is the one-color head/tail split that proves
  -- `Measure.map (fun ω ↦ ENNReal.toReal (weightedUrnColorTotalTime color ω))
  --   (weightedUrnClockLaw w) {t} = 0`
  -- for every `color` and `t`, after which `prod_graph_eq_zero_of_noAtoms_fst` kills the
  -- diagonal event `weightedUrnBlackTotalTime = weightedUrnRedTotalTime`.
  by
    have hpos :
        ∀ᵐ ω ∂ weightedUrnClockLaw w, ∀ i : Bool × ℕ, 0 < ω i := by
      -- Proof comment: every fixed clock coordinate is almost surely positive, and the index set
      -- `Bool × ℕ` is countable, so the intersection of those full-measure events is still
      -- full-measure.
      rw [ae_all_iff]
      intro i
      simpa using weightedUrnClockCoordinate_ae_pos w hw i.1 i.2
    have hneq :
        ∀ᵐ ω ∂ weightedUrnClockLaw w, weightedUrnBlackTotalTime ω ≠ weightedUrnRedTotalTime ω := by
      -- Proof comment: the equal-total event has measure zero by the previous diagonal lemma, so
      -- almost surely the two total times are distinct.
      refine compl_mem_ae_iff.2 ?_
      simpa [Set.compl_setOf] using
        weightedUrnTotalTimes_equal_zero_measure w hw hsummable
    -- Proof comment: on the event of positive coordinates and unequal total times, one color
    -- finishes strictly first, and the source-facing characterization turns this into eventual
    -- monochromaticity.
    filter_upwards [hpos, hneq] with ω hωpos hωneq
    have hfinish : ω ∈ weightedUrnOneColorFinishesFirstEvent := by
      rcases lt_or_gt_of_ne hωneq with hlt | hgt
      · exact Or.inl hlt
      · exact Or.inr hgt
    exact
      (mem_weightedUrnEventuallySingleColorEvent_iff ω
        (fun color n ↦ hωpos (color, n))).2 hfinish

end ProbabilityTheory
