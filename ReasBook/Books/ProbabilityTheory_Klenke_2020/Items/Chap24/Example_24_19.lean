/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap09.Example_9_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Theorem_2_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Definition_24_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Theorem_24_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Example_24_19.LaplaceCore

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open MeasureTheory.FiniteMeasure
open MeasureTheory.ProbabilityMeasure
open scoped ENNReal

noncomputable section

universe u

namespace MeasureTheory.FiniteMeasure

/-- Helper for Example 24.19: the log-Laplace transform of a probability measure on `[0, ∞)`. -/
def logLaplaceTransform (μ : ProbabilityMeasure NNReal) (t : NNReal) : ℝ :=
  -Real.log (∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal))

/-- Helper for Example 24.19: the subordinator Lévy--Khinchin representation predicate on
`[0, ∞)`. -/
def HasSubordinatorLevyKhinchinRepresentation
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal) : Prop :=
  ν {0} = 0 ∧
    Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν ∧
    ∀ t : NNReal,
      logLaplaceTransform μ t =
        ((α : ℝ) * (t : ℝ)) +
          ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν

end MeasureTheory.FiniteMeasure

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Helper for Example 24.19: the extended-real Laplace kernel is `0` at `∞` and otherwise
equals `exp (-t.toReal)`. -/
private def ennrealExpNeg (t : ℝ≥0∞) : ℝ :=
  if t = ∞ then 0 else Real.exp (-t.toReal)

/-- Helper for Example 24.19: the extended-real Laplace kernel vanishes at `∞`. -/
private lemma ennrealExpNeg_top : ennrealExpNeg ∞ = 0 := by
  simp [ennrealExpNeg]

/-- Lebesgue measure on `[0, ∞)` transported to `NNReal`. -/
def nnrealLebesgue : Measure NNReal :=
  Measure.map Real.toNNReal ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))

/-- Helper for Example 24.19: the first-coordinate image of the Poisson points whose time
coordinate lies in `(s, t]`. -/
def stripFirstCoordinate
    (X : Ω → Measure (NNReal × NNReal)) (s t : NNReal) : Ω → Measure NNReal :=
  fun ω ↦ Measure.map Prod.fst ((X ω).restrict (Set.univ ×ˢ Set.Ioc s t))

/-- Helper for Example 24.19: `nnrealLebesgue` assigns to `(s, t]` its interval length. -/
lemma nnrealLebesgue_Ioc (s t : NNReal) (hst : s ≤ t) :
    nnrealLebesgue (Set.Ioc s t) = ((t - s : NNReal) : ℝ≥0∞) := by
  have hpreimage :
      Real.toNNReal ⁻¹' Set.Ioc s t ∩ Set.Ici (0 : ℝ) = Set.Ioc (s : ℝ) t := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hx_mem, hx_nonneg⟩
      exact ⟨(Real.lt_toNNReal_iff_coe_lt).1 hx_mem.1,
        (Real.toNNReal_le_iff_le_coe).1 hx_mem.2⟩
    · intro hx
      refine ⟨⟨(Real.lt_toNNReal_iff_coe_lt).2 hx.1,
          (Real.toNNReal_le_iff_le_coe).2 hx.2⟩, ?_⟩
      -- Proof comment: every point in the transported interval is automatically nonnegative.
      exact le_trans s.2 (le_of_lt hx.1)
  -- Proof comment: rewrite the transported interval back to the real interval `(s, t]` and use
  -- the standard real volume formula there.
  rw [nnrealLebesgue, Measure.map_apply measurable_real_toNNReal measurableSet_Ioc]
  rw [Measure.restrict_apply (measurable_real_toNNReal measurableSet_Ioc), hpreimage,
    Real.volume_Ioc]
  rw [← NNReal.coe_sub hst]
  simp

/-- Helper for Example 24.19: the time strip `(0, t]` has `nnrealLebesgue`-mass `t`. -/
lemma nnrealLebesgue_Ioc_zero_left (t : NNReal) :
    nnrealLebesgue (Set.Ioc (0 : NNReal) t) = (t : ℝ≥0∞) := by
  -- Proof comment: this is the special case `s = 0` of the interval-length formula.
  simpa using nnrealLebesgue_Ioc 0 t bot_le

/-- The process obtained by summing the `x`-coordinates of all Poisson points whose time
coordinate lies in `(0, t]`. -/
def poissonPointProcessIntegralProcessENNReal
    (X : Ω → Measure (NNReal × NNReal)) : NNReal → Ω → ENNReal :=
  fun t ω ↦
    ∫⁻ z : NNReal × NNReal,
      (z.1 : ENNReal) *
        Set.indicator (Set.Ioc (0 : NNReal) t) (fun _ ↦ (1 : ENNReal)) z.2 ∂ X ω

/-- The `[0, ∞)`-valued companion obtained by applying `ENNReal.toNNReal` to the extended Poisson
stochastic integral. The source integral itself is carried by
`poissonPointProcessIntegralProcessENNReal`, and this coercion-based specialization is used only
after the almost-sure finiteness bridge recorded below. -/
def poissonPointProcessIntegralProcessNNReal
    (X : Ω → Measure (NNReal × NNReal)) : NNReal → Ω → NNReal :=
  fun t ω ↦ (poissonPointProcessIntegralProcessENNReal X t ω).toNNReal

/-- Helper for Example 24.19: the time-zero value of the extended Poisson integral process
vanishes. -/
theorem poissonPointProcessIntegralProcessENNReal_zero
    (X : Ω → Measure (NNReal × NNReal)) (ω : Ω) :
    poissonPointProcessIntegralProcessENNReal X 0 ω = 0 := by
  -- Proof comment: the interval `(0, 0]` is empty, so the indicator integrand is identically `0`.
  unfold poissonPointProcessIntegralProcessENNReal
  simp

/-- Helper for Example 24.19: at a fixed time `t`, the process value is the `x`-integral of the
first-coordinate image of the strip `(0, t]`. -/
theorem poissonPointProcessIntegralProcessENNReal_eq_lintegral_strip_zero_left
    (X : Ω → Measure (NNReal × NNReal)) (t : NNReal) (ω : Ω) :
    poissonPointProcessIntegralProcessENNReal X t ω =
      ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X 0 t ω := by
  -- Proof comment: push the strip-restricted random measure forward along `Prod.fst`, then rewrite
  -- the restricted integral as the original integrand multiplied by the strip indicator.
  unfold poissonPointProcessIntegralProcessENNReal stripFirstCoordinate
  rw [MeasureTheory.lintegral_map measurable_coe_nnreal_ennreal measurable_fst]
  rw [← MeasureTheory.lintegral_indicator
    (MeasurableSet.univ.prod measurableSet_Ioc)]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  simp [Set.indicator]

/-- Helper for Example 24.19: evaluating the strip image on a measurable set is the same as
evaluating the source random measure on the corresponding product strip. -/
theorem stripFirstCoordinate_apply
    (X : Ω → Measure (NNReal × NNReal)) (s t : NNReal) (ω : Ω)
    {A : Set NNReal} (hA : MeasurableSet A) :
    stripFirstCoordinate X s t ω A = X ω (A ×ˢ Set.Ioc s t) := by
  -- Proof comment: unfold the pushforward/restriction definition and rewrite the preimage of `A`
  -- under `Prod.fst` as the product strip with time window `(s, t]`.
  unfold stripFirstCoordinate
  rw [Measure.map_apply measurable_fst hA]
  rw [Measure.restrict_apply (measurable_fst hA)]
  have hpreimage :
      Prod.fst ⁻¹' A ∩ (Set.univ ×ˢ Set.Ioc s t) = A ×ˢ Set.Ioc s t := by
    ext z
    simp
  rw [hpreimage]

/-- Helper for Example 24.19: the source intensity of a measurable product strip factors into the
spatial mass and the interval length. -/
theorem stripFirstCoordinate_intensity_apply
    (ν : Measure NNReal) {s t : NNReal} (hst : s ≤ t) {A : Set NNReal} :
    (ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t) =
      ν A * (((t - s : NNReal) : ℝ≥0∞)) := by
  -- Proof comment: evaluate the product measure on the measurable rectangle and rewrite the
  -- Lebesgue factor by the interval-length formula on `NNReal`.
  letI : SFinite nnrealLebesgue := by
    unfold nnrealLebesgue
    infer_instance
  simpa [nnrealLebesgue_Ioc s t hst] using
    (Measure.prod_prod ν nnrealLebesgue A (Set.Ioc s t))

/-- Helper for Example 24.19: restricting the source Poisson point process to one time strip and
then projecting to the first coordinate preserves independent increments. -/
theorem stripFirstCoordinate_hasIndependentIncrements
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    (s t : NNReal) :
    HasIndependentIncrements P (stripFirstCoordinate X s t) := by
  intro n A hA hdisj
  have hprodDisj :
      Pairwise
        (fun i j ↦ Disjoint (A i ×ˢ Set.Ioc s t) (A j ×ˢ Set.Ioc s t)) := by
    intro i j hij
    refine Set.disjoint_left.2 ?_
    intro z hz_i hz_j
    exact Set.disjoint_left.mp (hdisj hij) hz_i.1 hz_j.1
  have hsource :
      iIndepFun
        (fun i ω ↦ X ω (A i ×ˢ Set.Ioc s t))
        (P : Measure Ω) :=
    hX.2.1 n (fun i ↦ A i ×ˢ Set.Ioc s t)
      (fun i ↦ (hA i).prod measurableSet_Ioc) hprodDisj
  -- Proof comment: each strip-image evaluation is definitionally the corresponding source
  -- evaluation on the product strip.
  refine hsource.congr ?_
  intro i
  exact Filter.Eventually.of_forall fun ω ↦
    (stripFirstCoordinate_apply X s t ω (hA i)).symm

/-- Helper for Example 24.19: bounded evaluations of adjacent strips along a monotone time grid
form an independent family. This is the scalar owner obtained directly from the source PPP by
evaluating on pairwise disjoint product strips. -/
theorem stripFirstCoordinate_eval_iIndepFun_of_monotoneTimes
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    {n : ℕ} (τ : Fin (n + 1) → NNReal) (hτ : Monotone τ)
    (A : Fin n → Set NNReal) (hA : ∀ i, MeasurableSet (A i)) :
    iIndepFun
      (fun i ω ↦ stripFirstCoordinate X (τ i.castSucc) (τ i.succ) ω (A i))
      (P : Measure Ω) := by
  let B : Fin n → Set (NNReal × NNReal) := fun i ↦
    A i ×ˢ Set.Ioc (τ i.castSucc) (τ i.succ)
  have hB : ∀ i, MeasurableSet (B i) := by
    intro i
    exact (hA i).prod measurableSet_Ioc
  have hB_disj : Pairwise (fun i j ↦ Disjoint (B i) (B j)) := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hij_lt | hij_lt
    · refine Set.disjoint_left.2 ?_
      intro z hz_i hz_j
      have hle :
          τ i.succ ≤ τ j.castSucc := by
        exact hτ (show i.succ ≤ j.castSucc by exact Fin.succ_le_castSucc_iff.mpr (Nat.succ_le_of_lt hij_lt))
      exact (Set.Ioc_disjoint_Ioc_of_le hle).le_bot ⟨hz_i.2, hz_j.2⟩
    · refine Set.disjoint_left.2 ?_
      intro z hz_i hz_j
      have hle :
          τ j.succ ≤ τ i.castSucc := by
        exact hτ (show j.succ ≤ i.castSucc by exact Fin.succ_le_castSucc_iff.mpr (Nat.succ_le_of_lt hij_lt))
      exact (Set.Ioc_disjoint_Ioc_of_le hle).le_bot ⟨hz_j.2, hz_i.2⟩
  have hsource :
      iIndepFun (fun i ω ↦ X ω (B i)) (P : Measure Ω) :=
    hX.2.1 _ B hB hB_disj
  -- Proof comment: each strip evaluation is exactly the corresponding source PPP count on the
  -- product rectangle `A i ×ˢ (τ i, τ (i + 1)]`.
  refine hsource.congr ?_
  intro i
  exact Filter.Eventually.of_forall fun ω ↦
    (stripFirstCoordinate_apply X (τ i.castSucc) (τ i.succ) ω (hA i)).symm

/-- Helper for Example 24.19: whenever the source PPP assigns a Poisson law to the product strip
`A ×ˢ (s, t]`, the corresponding first-coordinate strip count inherits that law verbatim. -/
theorem stripFirstCoordinate_hasLaw_of_ne_top
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    {s t : NNReal} {A : Set NNReal}
    (hA : MeasurableSet A)
    (hrect_bdd : Bornology.IsBounded (A ×ˢ Set.Ioc s t))
    (hrect_ne_top : (ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t) ≠ ∞) :
    HasLaw
      (fun ω ↦ stripFirstCoordinate X s t ω A)
      (Measure.map
        (fun n : ℕ ↦ (n : ENNReal))
        (poissonMeasure (((ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t)).toNNReal)))
      (P : Measure Ω) := by
  have hrectLaw :
      HasLaw
        (fun ω ↦ X ω (A ×ˢ Set.Ioc s t))
        (Measure.map
          (fun n : ℕ ↦ (n : ENNReal))
          (poissonMeasure (((ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t)).toNNReal)))
        (P : Measure Ω) := by
    exact hX.2.2.2 (hA.prod measurableSet_Ioc) hrect_bdd hrect_ne_top
  -- Proof comment: rewrite the observed variable to the strip image and normalize the rectangle
  -- intensity with the product-measure computation.
  simpa using
    (HasLaw.congr hrectLaw <| Filter.Eventually.of_forall fun ω ↦
      stripFirstCoordinate_apply X s t ω hA)

/-- Helper for Example 24.19: the strip-first-coordinate random measure is measurable as a
`Measure NNReal`-valued map. -/
theorem stripFirstCoordinate_measurable
    (X : Ω → Measure (NNReal × NNReal)) (hX : Measurable X) (s t : NNReal) :
    Measurable (stripFirstCoordinate X s t) := by
  have hrestrict :
      Measurable
        (fun μ : Measure (NNReal × NNReal) ↦
          μ.restrict (Set.univ ×ˢ Set.Ioc s t)) := by
    -- Proof comment: measurable-set evaluation of the restricted measure is evaluation on the
    -- corresponding intersection with the fixed product strip.
    refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
    simpa [Measure.restrict_apply, hA, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using
      (Measure.measurable_coe (hA.inter (MeasurableSet.univ.prod measurableSet_Ioc)))
  -- Proof comment: `stripFirstCoordinate` is the composition of the source random measure with
  -- restriction to the time strip and then the measurable first-coordinate pushforward.
  simpa [stripFirstCoordinate] using
    (Measure.measurable_map Prod.fst measurable_fst).comp (hrestrict.comp hX)

/-- Helper for Example 24.19: the `toNNReal` strip integral is measurable in the sample point. -/
theorem stripPoissonIntegral_toNNReal_measurable
    (X : Ω → Measure (NNReal × NNReal)) (hX : Measurable X) (s t : NNReal) :
    Measurable
      (fun ω ↦ ((∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω).toNNReal)) := by
  have hlintegral :
      Measurable (fun ω ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) := by
    exact
      (Measure.measurable_lintegral measurable_coe_nnreal_ennreal).comp
        (stripFirstCoordinate_measurable X hX s t)
  -- Proof comment: the scalar strip integral is measurable before and after applying
  -- `ENNReal.toNNReal`.
  exact ENNReal.measurable_toNNReal.comp hlintegral

/-- Helper for Example 24.19: projecting the source Poisson point process to one fixed time strip
again yields a source-level random measure. -/
theorem stripFirstCoordinate_isRandomMeasure
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    (s t : NNReal) :
    IsRandomMeasure P (stripFirstCoordinate X s t) := by
  refine ⟨stripFirstCoordinate_measurable X hX.1.measurable s t, ?_⟩
  -- Proof comment: local finiteness is preserved by restricting the source measure to the strip
  -- and then controlling compact first-coordinate neighborhoods by compact source rectangles.
  filter_upwards [hX.1.ae_isLocallyFiniteMeasure] with ω hω
  letI : IsLocallyFiniteMeasure (X ω) := hω
  refine ⟨fun x ↦ ?_⟩
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x zero_lt_one, ?_⟩
  have happly :
      stripFirstCoordinate X s t ω (Metric.closedBall x 1) =
        X ω (Metric.closedBall x 1 ×ˢ Set.Ioc s t) := by
    exact
      stripFirstCoordinate_apply X s t ω Metric.isClosed_closedBall.measurableSet
  have hsubset :
      Metric.closedBall x 1 ×ˢ Set.Ioc s t ⊆
        Metric.closedBall x 1 ×ˢ Set.Icc s t := by
    intro z hz
    exact ⟨hz.1, ⟨le_of_lt hz.2.1, hz.2.2⟩⟩
  have hfinite :
      X ω (Metric.closedBall x 1 ×ˢ Set.Icc s t) < ∞ := by
    exact ((isCompact_closedBall x 1).prod isCompact_Icc).measure_lt_top
  rw [happly]
  exact lt_of_le_of_lt (measure_mono hsubset) hfinite

/-- Helper for Example 24.19: equal-length time strips induce identically distributed
first-coordinate image random measures. -/
theorem stripFirstCoordinate_identDistrib_of_sameLength
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    {s t s' t' : NNReal} (hst : s ≤ t) (hst' : s' ≤ t')
    (hlen : t - s = t' - s') :
    IdentDistrib (stripFirstCoordinate X s t) (stripFirstCoordinate X s' t')
      (P : Measure Ω) (P : Measure Ω) := by
  letI : IsLocallyFiniteMeasure (ν.prod nnrealLebesgue) := hX.2.2.1
  refine identDistrib_of_bounded_eval_identDistrib_of_independentIncrements
    (stripFirstCoordinate_isRandomMeasure P ν X hX s t)
    (stripFirstCoordinate_isRandomMeasure P ν X hX s' t')
    (stripFirstCoordinate_hasIndependentIncrements P ν X hX s t)
    (stripFirstCoordinate_hasIndependentIncrements P ν X hX s' t')
    ?_
  intro A hA hA_bdd
  have hIoc_bdd : Bornology.IsBounded (Set.Ioc s t) := by
    exact Bornology.IsBounded.subset (Metric.isBounded_Icc s t) Set.Ioc_subset_Icc_self
  have hIoc'_bdd : Bornology.IsBounded (Set.Ioc s' t') := by
    exact Bornology.IsBounded.subset (Metric.isBounded_Icc s' t') Set.Ioc_subset_Icc_self
  have hrect_bdd : Bornology.IsBounded (A ×ˢ Set.Ioc s t) := hA_bdd.prod hIoc_bdd
  have hrect'_bdd : Bornology.IsBounded (A ×ˢ Set.Ioc s' t') := hA_bdd.prod hIoc'_bdd
  have hrect_ne_top : (ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t) ≠ ∞ := by
    have hrect_lt_top : (ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t) < ∞ := hrect_bdd.measure_lt_top
    exact ne_of_lt hrect_lt_top
  have hrect'_ne_top : (ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s' t') ≠ ∞ := by
    have hrect'_lt_top : (ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s' t') < ∞ :=
      hrect'_bdd.measure_lt_top
    exact ne_of_lt hrect'_lt_top
  have hparam :
      (ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t) =
        (ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s' t') := by
    rw [stripFirstCoordinate_intensity_apply ν hst, stripFirstCoordinate_intensity_apply ν hst']
    simpa [hlen]
  have hLaw :
      HasLaw
        (fun ω ↦ stripFirstCoordinate X s t ω A)
        (Measure.map
          (fun n : ℕ ↦ (n : ENNReal))
          (poissonMeasure (((ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t)).toNNReal)))
        (P : Measure Ω) :=
    stripFirstCoordinate_hasLaw_of_ne_top P ν X hX hA hrect_bdd hrect_ne_top
  have hLaw' :
      HasLaw
        (fun ω ↦ stripFirstCoordinate X s' t' ω A)
        (Measure.map
          (fun n : ℕ ↦ (n : ENNReal))
          (poissonMeasure (((ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t)).toNNReal)))
        (P : Measure Ω) := by
    simpa [hparam] using
      (stripFirstCoordinate_hasLaw_of_ne_top P ν X hX hA hrect'_bdd hrect'_ne_top)
  -- Proof comment: bounded evaluations on equal-length strips share the same Poisson parameter,
  -- so Corollary 24.9 upgrades the matching one-dimensional marginals to the full measure law.
  exact hLaw.identDistrib hLaw'

/-- Helper for Example 24.19: if `ν ⊗ λ` is locally finite on `NNReal × NNReal`, then `ν` is
already locally finite on `NNReal`. -/
theorem isLocallyFiniteMeasure_of_prod_nnrealLebesgue
    (ν : Measure NNReal) [IsLocallyFiniteMeasure (ν.prod nnrealLebesgue)] :
    IsLocallyFiniteMeasure ν := by
  refine ⟨fun x ↦ ?_⟩
  refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x zero_lt_one, ?_⟩
  have hcompact :
      IsCompact (Metric.closedBall x 1 ×ˢ Set.Icc (0 : NNReal) 1) := by
    exact (isCompact_closedBall x 1).prod isCompact_Icc
  have hfinite :
      (ν.prod nnrealLebesgue) (Metric.closedBall x 1 ×ˢ Set.Icc (0 : NNReal) 1) < ∞ := by
    exact hcompact.measure_lt_top
  have hsubset :
      Metric.closedBall x 1 ×ˢ Set.Ioc (0 : NNReal) 1 ⊆
        Metric.closedBall x 1 ×ˢ Set.Icc (0 : NNReal) 1 := by
    intro z hz
    exact ⟨hz.1, ⟨le_of_lt hz.2.1, hz.2.2⟩⟩
  have hstrip :
      (ν.prod nnrealLebesgue) (Metric.closedBall x 1 ×ˢ Set.Ioc (0 : NNReal) 1) =
        ν (Metric.closedBall x 1) := by
    letI : SFinite nnrealLebesgue := by
      unfold nnrealLebesgue
      infer_instance
    have hstrip' :
        (ν.prod nnrealLebesgue) (Metric.closedBall x 1 ×ˢ Set.Ioc (0 : NNReal) 1) =
          ν (Metric.closedBall x 1) * (1 : ℝ≥0∞) :=
      by
        simpa [nnrealLebesgue_Ioc_zero_left] using
          (Measure.prod_prod ν nnrealLebesgue (Metric.closedBall x 1) (Set.Ioc (0 : NNReal) 1))
    simpa using
      hstrip'
  -- Proof comment: the unit-time strip has Lebesgue mass `1`, so finite product mass on a
  -- compact space-time rectangle forces the spatial marginal to be locally finite.
  calc
    ν (Metric.closedBall x 1)
        = (ν.prod nnrealLebesgue) (Metric.closedBall x 1 ×ˢ Set.Ioc (0 : NNReal) 1) := hstrip.symm
    _ ≤ (ν.prod nnrealLebesgue) (Metric.closedBall x 1 ×ˢ Set.Icc (0 : NNReal) 1) :=
      measure_mono hsubset
    _ < ∞ := hfinite

/-- Helper for Example 24.19: each fixed strip carries the one-dimensional Poisson point-process
data with scaled intensity `((t - s) • ν)`. -/
theorem stripFirstCoordinate_hasPoissonPointProcessData
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    {s t : NNReal} (hst : s ≤ t) :
    IsRandomMeasure P (stripFirstCoordinate X s t) ∧
      HasIndependentIncrements P (stripFirstCoordinate X s t) ∧
      IsLocallyFiniteMeasure ((((t - s : NNReal) : ENNReal) • ν)) ∧
      ∀ ⦃A : Set NNReal⦄, MeasurableSet A → Bornology.IsBounded A →
        ((((t - s : NNReal) : ENNReal) • ν) A) ≠ ∞ →
          HasLaw
            (fun ω ↦ stripFirstCoordinate X s t ω A)
            (Measure.map
              (fun n : ℕ ↦ (n : ENNReal))
              (poissonMeasure ((((((t - s : NNReal) : ENNReal) • ν) A).toNNReal))))
            (P : Measure Ω) := by
  letI : IsLocallyFiniteMeasure (ν.prod nnrealLebesgue) := hX.2.2.1
  letI : IsLocallyFiniteMeasure ν := isLocallyFiniteMeasure_of_prod_nnrealLebesgue ν
  refine ⟨stripFirstCoordinate_isRandomMeasure P ν X hX s t,
    stripFirstCoordinate_hasIndependentIncrements P ν X hX s t, ?_, ?_⟩
  · -- Proof comment: the strip intensity is just a finite scalar multiple of `ν`, so local
    -- finiteness is inherited from the base Lévy measure.
    simpa using (inferInstance : IsLocallyFiniteMeasure (((t - s : NNReal)) • ν))
  · intro A hA hA_bdd _hscaled_ne_top
    have hIoc_bdd : Bornology.IsBounded (Set.Ioc s t) := by
      exact Bornology.IsBounded.subset (Metric.isBounded_Icc s t) Set.Ioc_subset_Icc_self
    have hrect_bdd : Bornology.IsBounded (A ×ˢ Set.Ioc s t) := hA_bdd.prod hIoc_bdd
    have hrect_ne_top : (ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t) ≠ ∞ := by
      have hrect_lt_top : (ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t) < ∞ := hrect_bdd.measure_lt_top
      exact ne_of_lt hrect_lt_top
    have hparam :
        (((ν.prod nnrealLebesgue) (A ×ˢ Set.Ioc s t)).toNNReal) =
          (t - s) * (ν A).toNNReal := by
      rw [stripFirstCoordinate_intensity_apply ν hst, ENNReal.toNNReal_mul, mul_comm]
      simp
    -- Proof comment: the strip count law is exactly the source Poisson law after rewriting the
    -- product-strip intensity as the scaled one-dimensional intensity.
    simpa [hparam] using
      (stripFirstCoordinate_hasLaw_of_ne_top P ν X hX hA hrect_bdd hrect_ne_top)

/-- Helper for Example 24.19: equal-length strips have the same strip-integral law after
postcomposing the random-measure law by `μ ↦ ∫ x ∂μ`. -/
theorem stripPoissonIntegral_identDistrib_of_sameLength
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    {s t s' t' : NNReal} (hst : s ≤ t) (hst' : s' ≤ t')
    (hlen : t - s = t' - s') :
    IdentDistrib
      (fun ω ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω)
      (fun ω ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s' t' ω)
      (P : Measure Ω) (P : Measure Ω) := by
  let integrateFirstCoordinate : Measure NNReal → ENNReal := fun ξ ↦ ∫⁻ x, (x : ENNReal) ∂ ξ
  have hintegrate_meas : Measurable integrateFirstCoordinate :=
    Measure.measurable_lintegral measurable_coe_nnreal_ennreal
  -- Proof comment: once the strip random measures have the same law, the strip integrals inherit
  -- the same law by measurable postcomposition.
  exact
    (stripFirstCoordinate_identDistrib_of_sameLength P ν X hX hst hst' hlen).comp
      hintegrate_meas

/-- Helper for Example 24.19: the strip integral over `(s, t]` is the original two-dimensional
Poisson integral with the corresponding time indicator. -/
theorem poissonPointProcessIntegralProcessENNReal_eq_lintegral_strip
    (X : Ω → Measure (NNReal × NNReal)) (s t : NNReal) (ω : Ω) :
    ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω =
      ∫⁻ z : NNReal × NNReal,
        (z.1 : ENNReal) *
          Set.indicator (Set.Ioc s t) (fun _ ↦ (1 : ENNReal)) z.2 ∂ X ω := by
  -- Proof comment: push the strip-restricted measure forward along `Prod.fst`, then rewrite the
  -- restricted integral as the original integrand multiplied by the strip indicator.
  unfold stripFirstCoordinate
  rw [MeasureTheory.lintegral_map measurable_coe_nnreal_ennreal measurable_fst]
  rw [← MeasureTheory.lintegral_indicator
    (MeasurableSet.univ.prod measurableSet_Ioc)]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  simp [Set.indicator]

/-- Helper for Example 24.19: the indicator of `(0, t]` splits into the indicators of `(0, s]`
and `(s, t]` when `s ≤ t`. -/
theorem indicator_Ioc_zero_eq_add_indicator_strip
    {s t x : NNReal} (hst : s ≤ t) :
    Set.indicator (Set.Ioc (0 : NNReal) t) (fun _ ↦ (1 : ENNReal)) x =
      Set.indicator (Set.Ioc (0 : NNReal) s) (fun _ ↦ (1 : ENNReal)) x +
        Set.indicator (Set.Ioc s t) (fun _ ↦ (1 : ENNReal)) x := by
  -- Proof comment: the interval `(0, t]` is the disjoint union of `(0, s]` and `(s, t]`.
  by_cases hxs : x ∈ Set.Ioc (0 : NNReal) s
  · have hxt : x ∈ Set.Ioc (0 : NNReal) t := ⟨hxs.1, le_trans hxs.2 hst⟩
    have hxstrip : x ∉ Set.Ioc s t := by
      intro hxstrip
      exact not_lt_of_ge hxs.2 hxstrip.1
    simp [Set.indicator, hxs, hxt, hxstrip]
  · by_cases hxstrip : x ∈ Set.Ioc s t
    · have hxt : x ∈ Set.Ioc (0 : NNReal) t := ⟨lt_of_le_of_lt bot_le hxstrip.1, hxstrip.2⟩
      simp [Set.indicator, hxs, hxstrip, hxt]
    · have hxt : x ∉ Set.Ioc (0 : NNReal) t := by
        intro hxt
        have hnotle : ¬ x ≤ s := by
          intro hle
          exact hxs ⟨hxt.1, hle⟩
        exact hxstrip ⟨lt_of_not_ge hnotle, hxt.2⟩
      simp [Set.indicator, hxs, hxstrip, hxt]

/-- Helper for Example 24.19: the time-`t` Poisson integral splits into the earlier prefix
integral and the strip integral over `(s, t]`. -/
theorem poissonPointProcessIntegralProcessENNReal_eq_add_stripIntegral
    (X : Ω → Measure (NNReal × NNReal)) {s t : NNReal} (hst : s ≤ t) (ω : Ω) :
    poissonPointProcessIntegralProcessENNReal X t ω =
      poissonPointProcessIntegralProcessENNReal X s ω +
        ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω := by
  let g : NNReal × NNReal → ENNReal := fun z ↦
    (z.1 : ENNReal) * Set.indicator (Set.Ioc s t) (fun _ ↦ (1 : ENNReal)) z.2
  have hg : Measurable g := by
    -- Proof comment: the strip integrand is a measurable product of the first coordinate and the
    -- time-strip indicator.
    dsimp [g]
    exact (measurable_coe_nnreal_ennreal.comp measurable_fst).mul
      ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)
  -- Proof comment: rewrite the strip term as an integral over the original measure and then split
  -- the time indicator into the disjoint prefix and strip contributions.
  rw [poissonPointProcessIntegralProcessENNReal_eq_lintegral_strip X s t ω]
  unfold poissonPointProcessIntegralProcessENNReal
  rw [← MeasureTheory.lintegral_add_right _ hg]
  refine lintegral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
  change
    (z.1 : ENNReal) * Set.indicator (Set.Ioc (0 : NNReal) t) (fun _ ↦ (1 : ENNReal)) z.2 =
      (z.1 : ENNReal) * Set.indicator (Set.Ioc (0 : NNReal) s) (fun _ ↦ (1 : ENNReal)) z.2 +
        g z
  rw [indicator_Ioc_zero_eq_add_indicator_strip hst]
  simp [g, left_distrib]

/-- Helper for Example 24.19: once the earlier process value is almost surely finite, the process
increment over `(s, t]` agrees almost surely with the strip integral. -/
theorem poissonPointProcessIntegralProcess_increment_ae_eq_stripPoissonIntegral
    (P : ProbabilityMeasure Ω) (X : Ω → Measure (NNReal × NNReal))
    {s t : NNReal} (hst : s ≤ t)
    (hsfinite : ∀ᵐ ω ∂(P : Measure Ω), poissonPointProcessIntegralProcessENNReal X s ω < ∞) :
    ∀ᵐ ω ∂(P : Measure Ω),
      poissonPointProcessIntegralProcessENNReal X t ω -
          poissonPointProcessIntegralProcessENNReal X s ω =
        ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω := by
  -- Proof comment: on the almost-sure finite event for the earlier endpoint, subtract the
  -- additive decomposition of the time-`t` integral by cancelling the finite prefix.
  filter_upwards [hsfinite] with ω hω
  exact ENNReal.sub_eq_of_eq_add_rev (ne_of_lt hω)
    (poissonPointProcessIntegralProcessENNReal_eq_add_stripIntegral X hst ω)

/-- Helper for Example 24.19: the Poisson Laplace kernel is bounded above by the textbook
truncation kernel `x ↦ min 1 x` on `[0, ∞)`. -/
private lemma one_sub_expNeg_le_min_one (x : ℝ) :
    1 - Real.exp (-x) ≤ min 1 x := by
  -- Proof comment: the tangent-line bound gives the `≤ x` half of the comparison.
  have hx_le : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.one_sub_le_exp_neg x]
  -- Proof comment: positivity of the exponential gives the uniform `≤ 1` half.
  have h_one : 1 - Real.exp (-x) ≤ 1 := by
    have hpos : 0 < Real.exp (-x) := Real.exp_pos (-x)
    linarith
  exact le_min h_one hx_le

/-- Helper for Example 24.19: the fixed lower-comparison constant in the Laplace-kernel estimate
is strictly positive. -/
private lemma poissonExpKernelLowerConst_pos :
    0 < 1 - Real.exp (-(1 / 2 : ℝ)) := by
  -- Proof comment: `exp (-1 / 2)` is strictly below `1`.
  have hhalf_neg : -(1 / 2 : ℝ) < 0 := by
    norm_num
  have hlt : Real.exp (-(1 / 2 : ℝ)) < 1 := by
    calc
      Real.exp (-(1 / 2 : ℝ)) < Real.exp 0 := Real.exp_lt_exp.mpr hhalf_neg
      _ = 1 := by simp
  linarith

/-- Helper for Example 24.19: on `[0, 1]`, the Poisson Laplace kernel dominates a fixed positive
multiple of `x`. -/
private lemma poissonExpKernel_lower_on_unitInterval
    (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (1 - Real.exp (-(1 / 2 : ℝ))) * x ≤ 1 - Real.exp (-x) := by
  by_cases hhalf : x ≤ 1 / 2
  · -- Proof comment: for small `x`, use the quadratic remainder bound for `exp (-x)`.
    have habs_arg : |(-x : ℝ)| ≤ 1 := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have hrem :
        |Real.exp (-x) - 1 + x| ≤ x ^ 2 := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, pow_two] using
        (Real.abs_exp_sub_one_sub_id_le habs_arg)
    have hquad :
        Real.exp (-x) - 1 + x ≤ x ^ 2 := by
      exact le_trans (le_abs_self _) hrem
    have hhalfCoeff : 1 - Real.exp (-(1 / 2 : ℝ)) ≤ 1 / 2 := by
      have hExpLower : 1 - (1 / 2 : ℝ) ≤ Real.exp (-(1 / 2 : ℝ)) :=
        Real.one_sub_le_exp_neg (1 / 2 : ℝ)
      linarith
    have hcoeffMul : (1 - Real.exp (-(1 / 2 : ℝ))) * x ≤ x / 2 := by
      nlinarith
    have hlinear : x / 2 ≤ x - x ^ 2 := by
      nlinarith
    linarith
  · -- Proof comment: on `[1 / 2, 1]`, monotonicity yields a uniform positive lower bound.
    have hhalf_lt : 1 / 2 < x := by
      linarith
    have hmono :
        Real.exp (-x) ≤ Real.exp (-(1 / 2 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hconst_le :
        1 - Real.exp (-(1 / 2 : ℝ)) ≤ 1 - Real.exp (-x) := by
      linarith
    have hcoeff_nonneg : 0 ≤ 1 - Real.exp (-(1 / 2 : ℝ)) := by
      exact le_of_lt poissonExpKernelLowerConst_pos
    have hmul_le :
        (1 - Real.exp (-(1 / 2 : ℝ))) * x ≤ 1 - Real.exp (-(1 / 2 : ℝ)) := by
      nlinarith
    exact le_trans hmul_le hconst_le

/-- Helper for Example 24.19: on `[0, ∞)`, the Poisson Laplace kernel dominates a fixed positive
multiple of the truncation kernel `x ↦ min 1 x`. -/
private lemma poissonExpKernel_lower_mul_min (x : ℝ) (hx : 0 ≤ x) :
    (1 - Real.exp (-(1 / 2 : ℝ))) * min 1 x ≤ 1 - Real.exp (-x) := by
  by_cases hx1 : x ≤ 1
  · -- Proof comment: on `[0, 1]` the truncation kernel is exactly `x`.
    simpa [min_eq_right hx1] using poissonExpKernel_lower_on_unitInterval x hx hx1
  · -- Proof comment: on `[1, ∞)`, monotonicity gives the same fixed lower bound.
    have hx1' : 1 ≤ x := le_of_not_ge hx1
    have hmono :
        Real.exp (-x) ≤ Real.exp (-(1 / 2 : ℝ)) := by
      apply Real.exp_le_exp.mpr
      linarith
    have hconst_le :
        1 - Real.exp (-(1 / 2 : ℝ)) ≤ 1 - Real.exp (-x) := by
      linarith
    simpa [min_eq_left hx1'] using hconst_le

/-- Helper for Example 24.19: on finite `NNReal` points, the Poisson exponent kernel is exactly
the `ENNReal` lift of `x ↦ 1 - exp (-x)`. -/
private lemma poissonLaplaceKernel_eq_ofReal (x : NNReal) :
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (x : ℝ≥0∞)) =
      ENNReal.ofReal (1 - Real.exp (-(x : ℝ))) := by
  have hExpNonneg : 0 ≤ Real.exp (-(x : ℝ)) := Real.exp_nonneg _
  -- Proof comment: finite `NNReal` inputs reduce `ennrealExpNeg` to the ordinary exponential.
  simp [ennrealExpNeg, ENNReal.ofReal_sub, hExpNonneg]

/-- Helper for Example 24.19: the Poisson exponent kernel is integrable exactly when the textbook
truncation kernel `x ↦ min 1 x` is integrable. -/
private lemma poissonLaplaceKernel_integrable_iff
    (ν : Measure NNReal) :
    Integrable (fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ))) ν ↔
      Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν := by
  let k : NNReal → ℝ := fun x ↦ 1 - Real.exp (-(x : ℝ))
  let m : NNReal → ℝ := fun x ↦ min (1 : ℝ) (x : ℝ)
  have hk_nonneg : ∀ x : NNReal, 0 ≤ k x := by
    intro x
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by simpa using x.2))
  have hm_nonneg : ∀ x : NNReal, 0 ≤ m x := by
    intro x
    exact le_min zero_le_one x.2
  have hk_meas : AEStronglyMeasurable k ν := by
    have hk_meas' : Measurable k := by
      fun_prop
    exact hk_meas'.aestronglyMeasurable
  have hm_meas : AEStronglyMeasurable m ν := by
    have hm_meas' : Measurable m := by
      fun_prop
    exact hm_meas'.aestronglyMeasurable
  constructor
  · intro hk
    -- Proof comment: the lower comparison upgrades integrability of `k` to integrability of `m`.
    have hscaled :
        Integrable (fun x : NNReal ↦ (1 - Real.exp (-(1 / 2 : ℝ))) * m x) ν := by
      refine Integrable.mono' hk (hm_meas.const_mul _) ?_
      filter_upwards with x
      have hconst_nonneg : 0 ≤ 1 - Real.exp (-(1 / 2 : ℝ)) :=
        le_of_lt poissonExpKernelLowerConst_pos
      have hx :
          (1 - Real.exp (-(1 / 2 : ℝ))) * m x ≤ k x :=
        poissonExpKernel_lower_mul_min (x : ℝ) x.2
      have hx' : |1 - Real.exp (-(1 / 2 : ℝ))| * m x ≤ k x := by
        rw [abs_of_nonneg hconst_nonneg]
        exact hx
      simpa [k, m, Real.norm_eq_abs, Real.norm_of_nonneg (hk_nonneg x),
        Real.norm_of_nonneg (hm_nonneg x)] using hx'
    have hconst_ne : (1 - Real.exp (-(1 / 2 : ℝ))) ≠ 0 := by
      linarith [poissonExpKernelLowerConst_pos]
    have hm' :
        Integrable
          (fun x : NNReal ↦
            (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹ *
              ((1 - Real.exp (-(1 / 2 : ℝ))) * m x)) ν :=
      hscaled.const_mul (1 - Real.exp (-(1 / 2 : ℝ)))⁻¹
    -- Proof comment: divide by the strictly positive comparison constant to recover `m`.
    convert hm' using 1
    funext x
    field_simp [hconst_ne]
    ring
  · intro hm
    -- Proof comment: the pointwise upper bound `k ≤ min 1 x` gives the reverse implication.
    refine Integrable.mono' hm hk_meas ?_
    filter_upwards with x
    have hx : k x ≤ m x := one_sub_expNeg_le_min_one (x : ℝ)
    simpa [k, m, Real.norm_of_nonneg (hk_nonneg x), Real.norm_of_nonneg (hm_nonneg x)] using hx

/-- Helper for Example 24.19: the small Laplace scales are `s_n = (n + 1)⁻¹` on `ℝ`. -/
private def invSuccScaleReal (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- Helper for Example 24.19: the kernel `ennrealExpNeg` is measurable on `ℝ≥0∞`. -/
private lemma measurable_ennrealExpNeg : Measurable ennrealExpNeg := by
  classical
  have hcore : Measurable (fun t : ℝ≥0∞ ↦ Real.exp (-t.toReal)) := by
    fun_prop
  -- Proof comment: rewrite the definition as a singleton-piecewise function.
  simpa [ennrealExpNeg, Set.piecewise] using
    (measurable_const.piecewise (measurableSet_singleton (∞ : ℝ≥0∞)) hcore)

/-- Helper for Example 24.19: the extended-real Laplace kernel is pointwise nonnegative. -/
private lemma ennrealExpNeg_nonneg (t : ℝ≥0∞) : 0 ≤ ennrealExpNeg t := by
  by_cases ht : t = ∞
  · -- Proof comment: at `∞` the kernel is exactly `0`.
    simp [ennrealExpNeg, ht]
  · -- Proof comment: away from `∞`, the kernel is an ordinary exponential.
    simp [ennrealExpNeg, ht]
    exact le_of_lt (Real.exp_pos _)

/-- Helper for Example 24.19: the extended-real Laplace kernel is bounded above by `1`. -/
private lemma ennrealExpNeg_le_one (t : ℝ≥0∞) : ennrealExpNeg t ≤ 1 := by
  by_cases ht : t = ∞
  · -- Proof comment: the `∞` value is `0`.
    simp [ennrealExpNeg, ht]
  · -- Proof comment: on finite inputs, the exponent is nonpositive.
    have hto : 0 ≤ t.toReal := ENNReal.toReal_nonneg
    have hle : Real.exp (-t.toReal) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      linarith
    simpa [ennrealExpNeg, ht] using hle

/-- Helper for Example 24.19: the scaled Laplace kernel tends to the finiteness indicator on
`ℝ≥0∞`. -/
private lemma ennrealExpNeg_invSucc_mul_tendsto_indicator (y : ℝ≥0∞) :
    Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y))
      Filter.atTop (nhds (if y = ∞ then (0 : ℝ) else 1)) := by
  by_cases hy : y = ∞
  · -- Proof comment: positive scales keep `∞` fixed, so the sequence is constantly `0`.
    have hconst :
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y)) =
          fun _ ↦ (0 : ℝ) := by
      funext n
      have hn : 0 < (n : ℝ) + 1 := by
        positivity
      have hs_pos : 0 < invSuccScaleReal n := by
        simpa [invSuccScaleReal] using one_div_pos.mpr hn
      have hs_pos' : 0 < ENNReal.ofReal (invSuccScaleReal n) := ENNReal.ofReal_pos.mpr hs_pos
      simp [hy, ennrealExpNeg, ne_of_gt hs_pos']
    rw [hconst]
    simp [hy]
  · -- Proof comment: on finite inputs, rewrite to the ordinary exponential and use continuity.
    have hs : Filter.Tendsto invSuccScaleReal Filter.atTop (nhds 0) := by
      change Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hmul :
        Filter.Tendsto (fun n : ℕ ↦ invSuccScaleReal n * y.toReal) Filter.atTop
          (nhds (0 * y.toReal)) := by
      exact hs.mul tendsto_const_nhds
    have hcont : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
      Real.continuous_exp.comp continuous_neg
    have hexp :
        Filter.Tendsto (fun n : ℕ ↦ Real.exp (-(invSuccScaleReal n * y.toReal))) Filter.atTop
          (nhds (Real.exp (-(0 * y.toReal)))) := by
      have hcontAt : ContinuousAt (fun r : ℝ ↦ Real.exp (-r)) (0 * y.toReal) :=
        hcont.continuousAt
      exact hcontAt.tendsto.comp hmul
    have hrewrite :
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * y)) =
          (fun n : ℕ ↦ Real.exp (-(invSuccScaleReal n * y.toReal))) := by
      funext n
      have hmul_ne_top : ENNReal.ofReal (invSuccScaleReal n) * y ≠ ∞ :=
        ENNReal.mul_ne_top (by simp [invSuccScaleReal]) hy
      have hs_nonneg : 0 ≤ invSuccScaleReal n := by
        have hn : 0 ≤ (n : ℝ) + 1 := by
          positivity
        simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
      rw [ennrealExpNeg, if_neg hmul_ne_top, ENNReal.toReal_mul]
      change Real.exp (-((ENNReal.ofReal (invSuccScaleReal n)).toReal * y.toReal)) = _
      rw [ENNReal.toReal_ofReal hs_nonneg]
    rw [hrewrite]
    simpa [hy] using hexp

/-- Helper for Example 24.19: the small-scale Laplace expectations converge to the probability
that the extended-real variable is finite. -/
private lemma poissonPointIntegralLaplace_invSucc_tendsto_measureFinite
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {Y : α → ℝ≥0∞}
    (hY : Measurable Y) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ a, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) ∂μ)
      Filter.atTop (nhds (μ {a | Y a < ∞}).toReal) := by
  let A : Set α := {a | Y a < ∞}
  let G : α → ℝ := Set.indicator A fun _ ↦ (1 : ℝ)
  have hF_meas :
      ∀ n, AEStronglyMeasurable
        (fun a ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a)) μ := by
    intro n
    exact (measurable_ennrealExpNeg.comp (measurable_const.mul hY)).aestronglyMeasurable
  have h_bound :
      ∀ n, ∀ᵐ a ∂μ, ‖ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a)‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with a
    have hnonneg : 0 ≤ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) :=
      ennrealExpNeg_nonneg _
    have hle : ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a) ≤ 1 :=
      ennrealExpNeg_le_one _
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have h_lim :
      ∀ᵐ a ∂μ, Filter.Tendsto
        (fun n : ℕ ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y a))
        Filter.atTop (nhds (G a)) := by
    filter_upwards with a
    by_cases ha : Y a = ∞
    · -- Proof comment: at `∞`, the pointwise limit is `0`.
      simpa [G, A, ha] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
    · -- Proof comment: at finite points, the pointwise limit is `1`.
      have ha' : Y a < ∞ := lt_top_iff_ne_top.mpr ha
      simpa [G, A, ha, ha'] using ennrealExpNeg_invSucc_mul_tendsto_indicator (Y a)
  have hDCT :=
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : α ↦ (1 : ℝ)) hF_meas (integrable_const 1) h_bound h_lim
  have hA : MeasurableSet A := measurableSet_lt hY measurable_const
  have hG_integral : ∫ a, G a ∂μ = (μ A).toReal := by
    -- Proof comment: integrating the indicator of `A` against a finite measure recovers `μ A`.
    rw [integral_indicator hA]
    simp [A, Measure.real_def]
  simpa [A, G, hG_integral] using hDCT

/-- Helper for Example 24.19: scaling the textbook kernel by a factor `s ≤ 1` preserves the
domination by `x ↦ min 1 x`. -/
private lemma poissonExpKernel_scale_le_minOne
    (s : ℝ) (hs1 : s ≤ 1) (x : NNReal) :
    1 - Real.exp (-(s * (x : ℝ))) ≤ min (1 : ℝ) (x : ℝ) := by
  have hmul_le : s * (x : ℝ) ≤ (x : ℝ) := by
    nlinarith [x.2, hs1]
  -- Proof comment: `min 1 ·` is monotone in its second argument.
  calc
    1 - Real.exp (-(s * (x : ℝ))) ≤ min 1 (s * (x : ℝ)) := one_sub_expNeg_le_min_one _
    _ ≤ min 1 (x : ℝ) := min_le_min le_rfl hmul_le

/-- Helper for Example 24.19: the scaled Poisson Laplace kernel is the `ENNReal` lift of the
ordinary real kernel. -/
private lemma poissonLaplaceKernel_scale_eq_ofReal (s : ℝ) (hs : 0 ≤ s) (x : NNReal) :
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (ENNReal.ofReal (s * (x : ℝ)))) =
      ENNReal.ofReal (1 - Real.exp (-(s * (x : ℝ)))) := by
  have hmul_nonneg : 0 ≤ s * (x : ℝ) := by
    nlinarith [hs, x.2]
  have hExpNonneg : 0 ≤ Real.exp (-(s * (x : ℝ))) := Real.exp_nonneg _
  -- Proof comment: finite `ENNReal.ofReal` inputs reduce the extended-real kernel to the real one.
  simp [ennrealExpNeg, hmul_nonneg, ENNReal.ofReal_sub, hExpNonneg]

/-- Helper for Example 24.19: the scaled Laplace exponents converge to `0` under the Lévy
integrability condition. -/
private lemma poissonLaplaceExponent_invSucc_tendstoZero
    (ν : Measure NNReal)
    (hInt : Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν) :
    Filter.Tendsto
      (fun n : ℕ ↦ ∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν)
      Filter.atTop (nhds 0) := by
  have hs : Filter.Tendsto invSuccScaleReal Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have h_meas :
      ∀ n, AEStronglyMeasurable
        (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ν := by
    intro n
    have h : Measurable (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) := by
      fun_prop
    exact h.aestronglyMeasurable
  have h_bound :
      ∀ n, ∀ᵐ x : NNReal ∂ν,
        ‖1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))‖ ≤ min (1 : ℝ) (x : ℝ) := by
    intro n
    filter_upwards with x
    have hs1 : invSuccScaleReal n ≤ 1 := by
      have hn : (0 : ℝ) ≤ n := by
        exact_mod_cast Nat.zero_le n
      have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        linarith
      simpa [invSuccScaleReal] using inv_le_one_of_one_le₀ hn'
    have hnonneg : 0 ≤ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) := by
      have hs0 : 0 ≤ invSuccScaleReal n := by
        have hn : 0 ≤ (n : ℝ) + 1 := by
          positivity
        simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
      have harg_nonneg : 0 ≤ invSuccScaleReal n * (x : ℝ) := by
        nlinarith [x.2, hs0]
      have hle : Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        linarith
      exact sub_nonneg.mpr hle
    have hle : 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ min (1 : ℝ) (x : ℝ) :=
      poissonExpKernel_scale_le_minOne (invSuccScaleReal n) hs1 x
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have h_lim :
      ∀ᵐ x : NNReal ∂ν,
        Filter.Tendsto
          (fun n : ℕ ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) Filter.atTop
          (nhds 0) := by
    filter_upwards with x
    have hmul :
        Filter.Tendsto (fun n : ℕ ↦ invSuccScaleReal n * (x : ℝ)) Filter.atTop
          (nhds (0 * (x : ℝ))) := by
      exact hs.mul tendsto_const_nhds
    have hcont : Continuous (fun r : ℝ ↦ 1 - Real.exp (-r)) := by
      simpa using continuous_const.sub (Real.continuous_exp.comp continuous_neg)
    -- Proof comment: for each fixed `x`, the scale tends to `0`.
    have hcontAt : ContinuousAt (fun r : ℝ ↦ 1 - Real.exp (-r)) (0 * (x : ℝ)) :=
      hcont.continuousAt
    simpa using hcontAt.tendsto.comp hmul
  simpa using
    MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) h_meas hInt h_bound h_lim

/-- Helper for Example 24.19: for `s ≥ 0`, the scaled Bernstein kernel is dominated by
`max 1 s * min 1 x`. -/
private lemma poissonExpKernel_scale_le_max_mul_minOne
    (s : ℝ) (hs : 0 ≤ s) (x : NNReal) :
    1 - Real.exp (-(s * (x : ℝ))) ≤ max 1 s * min (1 : ℝ) (x : ℝ) := by
  by_cases hx1 : (x : ℝ) ≤ 1
  · calc
      1 - Real.exp (-(s * (x : ℝ))) ≤ s * (x : ℝ) := by
        refine le_trans (one_sub_expNeg_le_min_one (s * (x : ℝ))) ?_
        exact min_le_right _ _
      _ ≤ max 1 s * (x : ℝ) := by
        nlinarith [le_max_right 1 s, x.2]
      _ = max 1 s * min (1 : ℝ) (x : ℝ) := by
        rw [min_eq_right hx1]
  · have hx1' : 1 ≤ (x : ℝ) := le_of_not_ge hx1
    calc
      1 - Real.exp (-(s * (x : ℝ))) ≤ 1 := by
        have hpos : 0 < Real.exp (-(s * (x : ℝ))) := Real.exp_pos _
        linarith
      _ ≤ max 1 s * min (1 : ℝ) (x : ℝ) := by
        simpa [min_eq_left hx1'] using (le_max_left (1 : ℝ) s)

/-- Helper for Example 24.19: for `u > 0`, the scaled Poisson kernel dominates a positive
multiple of `x ↦ min 1 x`. -/
private lemma poissonExpKernel_scale_lower_mul_minOne
    (u : ℝ) (hu_pos : 0 < u) (x : NNReal) :
    ((1 - Real.exp (-(1 / 2 : ℝ))) * min (1 : ℝ) u) * min (1 : ℝ) (x : ℝ) ≤
      1 - Real.exp (-(u * (x : ℝ))) := by
  have hu_nonneg : 0 ≤ u := le_of_lt hu_pos
  have hbase :
      (1 - Real.exp (-(1 / 2 : ℝ))) * min (1 : ℝ) (u * (x : ℝ)) ≤
        1 - Real.exp (-(u * (x : ℝ))) :=
    poissonExpKernel_lower_mul_min (u * (x : ℝ)) (by nlinarith [hu_nonneg, x.2])
  have hscaledMin :
      min (1 : ℝ) u * min (1 : ℝ) (x : ℝ) ≤ min (1 : ℝ) (u * (x : ℝ)) := by
    by_cases hx1 : (x : ℝ) ≤ 1
    · by_cases hu1 : u ≤ 1
      · have hux1 : u * (x : ℝ) ≤ 1 := by
          nlinarith [hu1, x.2]
        rw [min_eq_right hu1, min_eq_right hx1, min_eq_right hux1]
      · have hu1' : 1 ≤ u := le_of_not_ge hu1
        rw [min_eq_left hu1', min_eq_right hx1]
        refine le_min ?_ ?_
        · simpa using hx1
        nlinarith [hu1', x.2]
    · have hx1' : 1 ≤ (x : ℝ) := le_of_not_ge hx1
      by_cases hu1 : u ≤ 1
      · rw [min_eq_right hu1, min_eq_left hx1']
        refine le_min ?_ ?_
        · simpa using hu1
        nlinarith [hu_nonneg, hx1']
      · have hu1' : 1 ≤ u := le_of_not_ge hu1
        have hux1 : 1 ≤ u * (x : ℝ) := by
          nlinarith [hu1', hx1']
        rw [min_eq_left hu1', min_eq_left hx1', min_eq_left hux1]
        simp
  calc
    ((1 - Real.exp (-(1 / 2 : ℝ))) * min (1 : ℝ) u) * min (1 : ℝ) (x : ℝ)
        = (1 - Real.exp (-(1 / 2 : ℝ))) * (min (1 : ℝ) u * min (1 : ℝ) (x : ℝ)) := by
            ring
    _ ≤ (1 - Real.exp (-(1 / 2 : ℝ))) * min (1 : ℝ) (u * (x : ℝ)) := by
          have hconst_nonneg : 0 ≤ 1 - Real.exp (-(1 / 2 : ℝ)) :=
            le_of_lt poissonExpKernelLowerConst_pos
          gcongr
    _ ≤ 1 - Real.exp (-(u * (x : ℝ))) := hbase

/-- Helper for Example 24.19: for `u > 0`, the scaled Poisson exponent kernel is integrable
exactly when the textbook truncation kernel is integrable. -/
private lemma poissonLaplaceKernel_scale_integrable_iff
    (ν : Measure NNReal) {u : ℝ} (hu_pos : 0 < u) :
    Integrable (fun x : NNReal ↦ 1 - Real.exp (-(u * (x : ℝ)))) ν ↔
      Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν := by
  let k : NNReal → ℝ := fun x ↦ 1 - Real.exp (-(u * (x : ℝ)))
  let m : NNReal → ℝ := fun x ↦ min (1 : ℝ) (x : ℝ)
  have hk_nonneg : ∀ x : NNReal, 0 ≤ k x := by
    intro x
    have hle : Real.exp (-(u * (x : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [le_of_lt hu_pos, x.2]
    exact sub_nonneg.mpr hle
  have hm_nonneg : ∀ x : NNReal, 0 ≤ m x := by
    intro x
    exact le_min zero_le_one x.2
  have hk_meas' : Measurable k := by
    fun_prop
  have hm_meas' : Measurable m := by
    fun_prop
  have hk_meas : AEStronglyMeasurable k ν := by
    exact hk_meas'.aestronglyMeasurable
  have hm_meas : AEStronglyMeasurable m ν := by
    exact hm_meas'.aestronglyMeasurable
  constructor
  · intro hk
    let c : ℝ := (1 - Real.exp (-(1 / 2 : ℝ))) * min (1 : ℝ) u
    have hc_pos : 0 < c := by
      have hmin_pos : 0 < min (1 : ℝ) u := by
        by_cases hu1 : u ≤ 1
        · rw [min_eq_right hu1]
          exact hu_pos
        · have hu1' : 1 ≤ u := le_of_not_ge hu1
          rw [min_eq_left hu1']
          norm_num
      have hconst_pos : 0 < 1 - Real.exp (-(1 / 2 : ℝ)) :=
        poissonExpKernelLowerConst_pos
      positivity
    have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
    have hcm :
        Integrable (fun x : NNReal ↦ c * m x) ν := by
      refine Integrable.mono' hk ((measurable_const.mul hm_meas').aestronglyMeasurable)
        ?_
      filter_upwards with x
      have hle := poissonExpKernel_scale_lower_mul_minOne u hu_pos x
      have hcm_nonneg : 0 ≤ c * m x := mul_nonneg hc_nonneg (hm_nonneg x)
      have hcm_le : c * m x ≤ k x := by
        simpa [c, m] using hle
      have hnorm : ‖c * m x‖ ≤ k x := by
        simpa [Real.norm_of_nonneg hcm_nonneg] using hcm_le
      simpa [k, Real.norm_of_nonneg (hk_nonneg x)] using hnorm
    have hm' : Integrable (fun x : NNReal ↦ c⁻¹ * (c * m x)) ν := hcm.const_mul c⁻¹
    have hc_ne : c ≠ 0 := ne_of_gt hc_pos
    convert hm' using 1
    funext x
    field_simp [hc_ne]
    ring
  · intro hm
    have hdom :
        Integrable (fun x : NNReal ↦ max 1 u * m x) ν :=
      hm.const_mul (max 1 u)
    refine Integrable.mono' hdom hk_meas ?_
    filter_upwards with x
    have hle := poissonExpKernel_scale_le_max_mul_minOne u (le_of_lt hu_pos) x
    have hmax_nonneg : 0 ≤ max 1 u := le_trans zero_le_one (le_max_left 1 u)
    have hdom_nonneg : 0 ≤ max 1 u * m x := mul_nonneg hmax_nonneg (hm_nonneg x)
    simpa [k, m, Real.norm_of_nonneg (hk_nonneg x), Real.norm_of_nonneg hdom_nonneg] using hle

/-- Helper for Example 24.19: on `NNReal`, the one-dimensional source PPP owner is exactly the
ordinary `IsPoissonPointProcess` predicate. -/
def IsPoissonPointProcessOnNNReal
    (ν : Measure NNReal) (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal) : Prop :=
  ProbabilityTheory.IsPoissonPointProcess ν P X

/-- Helper for Example 24.19: the one-dimensional Poisson stochastic integral is the identity
integral `∫ x X(dx)` on `NNReal`. -/
def poissonPointIntegral (X : Ω → Measure NNReal) (ω : Ω) : ℝ≥0∞ :=
  ∫⁻ x, (x : ℝ≥0∞) ∂ X ω

/-- Helper for Example 24.19: unfolding `poissonPointIntegral` recovers the defining nonnegative
Lebesgue integral. -/
theorem poissonPointIntegral_def (X : Ω → Measure NNReal) (ω : Ω) :
    poissonPointIntegral X ω = ∫⁻ x, (x : ℝ≥0∞) ∂ X ω := by
  -- Proof comment: the stochastic integral notation is defined by this `lintegral`.
  rfl

/-- Helper for Example 24.19: a nonzero simple-function fiber lies inside the support of the
simple function. -/
private lemma simpleFuncFiber_subset_support
    {β : Type*} [Zero β] {s : MeasureTheory.SimpleFunc NNReal β} {r : β} (hr : r ≠ 0) :
    s ⁻¹' {r} ⊆ Function.support s := by
  intro x hx
  have hsx : s x = r := by
    simpa using hx
  -- Proof comment: a point in a nonzero fiber cannot lie outside the support.
  simpa [Function.mem_support, hsx] using hr

/-- Helper for Example 24.19: a finite nonnegative step function integrates to the corresponding
finite sum of cell masses. -/
private lemma stepLintegral_eq_fintypeSum
    {ι : Type*} [Fintype ι] {ν : Measure NNReal} (A : ι → Set NNReal) (a : ι → NNReal)
    (hA : ∀ i, MeasurableSet (A i)) :
    ∫⁻ x, ∑ i, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) x ∂ν =
      ∑ i, (a i : ℝ≥0∞) * ν (A i) := by
  classical
  calc
    ∫⁻ x, ∑ i, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) x ∂ν
        = ∑ i, ∫⁻ x, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) x ∂ν := by
            simpa using
              (lintegral_finset_sum Finset.univ
                (fun i _ ↦
                  (show Measurable (fun x ↦ (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) x) from
                    measurable_const.indicator (hA i))))
    _ = ∑ i, (a i : ℝ≥0∞) * ν (A i) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [lintegral_indicator_const (hA i)]

/-- Helper for Example 24.19: a finite real step function with finite cell masses integrates to
the corresponding finite real sum. -/
private lemma stepIntegral_eq_fintypeSum
    {ι : Type*} [Fintype ι] {ν : Measure NNReal} (A : ι → Set NNReal) (c : ι → ℝ)
    (hA : ∀ i, MeasurableSet (A i)) (hA_finite : ∀ i, ν (A i) ≠ ⊤) :
    ∫ x, ∑ i, (A i).indicator (fun _ ↦ c i) x ∂ν =
      ∑ i, c i * (ν (A i)).toReal := by
  classical
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_indicator_const (c i) (hA i), Measure.real_def]
    simpa [smul_eq_mul, mul_comm]
  · intro i _
    have hAi_lt_top : ν (A i) < ∞ := lt_top_iff_ne_top.mpr (hA_finite i)
    have hIntOn : IntegrableOn (fun _ : NNReal ↦ c i) (A i) ν := by
      refine IntegrableOn.of_bound hAi_lt_top stronglyMeasurable_const.aestronglyMeasurable
        ‖c i‖ ?_
      exact Filter.Eventually.of_forall fun _ ↦ le_rfl
    -- Proof comment: finite mass on each cell makes the constant-on-cell summand integrable.
    exact hIntOn.integrable_indicator (hA i)

/-- Helper for Example 24.19: bounded measurable cells of a Poisson point process have almost
surely finite counts. -/
private lemma poissonPointProcess_count_ae_ltTop
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess ν P X)
    {A : Set NNReal} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A) :
    ∀ᵐ ω ∂(P : Measure Ω), X ω A < ∞ := by
  letI : IsLocallyFiniteMeasure ν := hX.2.2.1
  have hA_finite : ν A ≠ ∞ := hA_bdd.measure_lt_top.ne
  have hLaw :
      HasLaw (fun ω ↦ X ω A)
        (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure (ν A).toNNReal))
        (P : Measure Ω) :=
    hX.2.2.2 hA hA_bdd hA_finite
  have hNatLaw :
      HasLaw (fun n : ℕ ↦ (n : ℝ≥0∞))
        (Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure (ν A).toNNReal))
        (poissonMeasure (ν A).toNNReal) := by
    refine ⟨(measurable_of_countable (fun n : ℕ ↦ (n : ℝ≥0∞))).aemeasurable, ?_⟩
    rfl
  have hFiniteMap :
      ∀ᵐ x ∂(Measure.map (fun n : ℕ ↦ (n : ℝ≥0∞)) (poissonMeasure (ν A).toNNReal)), x < ∞ := by
    -- Proof comment: every point of the pushed Poisson count law comes from a natural number.
    exact (hNatLaw.ae_iff (p := fun x : ℝ≥0∞ ↦ x < ∞) (by fun_prop)).1 <|
      Filter.Eventually.of_forall fun n : ℕ ↦ ENNReal.natCast_lt_top n
  -- Proof comment: transport finiteness from the explicit Poisson law back to the PPP count.
  exact (hLaw.ae_iff (p := fun x : ℝ≥0∞ ↦ x < ∞) (by fun_prop)).2 hFiniteMap

/-- Helper for Example 24.19: a bounded-support simple nonnegative integrand already satisfies the
finite-cell Laplace transform formula over an arbitrary one-dimensional PPP. -/
private lemma simpleFuncLaplaceTransformNNReal
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess ν P X)
    (s : MeasureTheory.SimpleFunc NNReal NNReal)
    (hsupport_bdd : Bornology.IsBounded (Function.support s)) :
    ∫ ω, ennrealExpNeg (∫⁻ y, (s y : ENNReal) ∂ X ω) ∂(P : Measure Ω) =
      Real.exp (∫ y : NNReal, (Real.exp (-(s y : ℝ)) - 1) ∂ν) := by
  classical
  letI : IsLocallyFiniteMeasure ν := hX.2.2.1
  let values : Finset NNReal := s.range.filter fun r ↦ r ≠ 0
  let ι := {r : NNReal // r ∈ values}
  letI : Fintype ι := Finset.fintypeCoeSort values
  let A : ι → Set NNReal := fun i ↦ s ⁻¹' {i.1}
  let a : ι → NNReal := fun i ↦ i.1
  have hA : ∀ i : ι, MeasurableSet (A i) := by
    intro i
    simpa [A] using s.measurableSet_preimage ({i.1} : Set NNReal)
  have hA_bdd : ∀ i : ι, Bornology.IsBounded (A i) := by
    intro i
    refine hsupport_bdd.subset ?_
    intro x hx
    exact simpleFuncFiber_subset_support (r := i.1) (Finset.mem_filter.mp i.2).2 hx
  have hA_finite : ∀ i : ι, ν (A i) ≠ ∞ := by
    intro i
    exact (hA_bdd i).measure_lt_top.ne
  have hdisj : Pairwise (fun i j : ι ↦ Disjoint (A i) (A j)) := by
    intro i j hij
    refine Set.disjoint_left.2 fun x hx hx' ↦ ?_
    apply hij
    apply Subtype.ext
    have hxi : s x = i.1 := by
      simpa [A] using hx
    have hxj : s x = j.1 := by
      simpa [A] using hx'
    exact hxi.symm.trans hxj
  have hsampleFun :
      (fun y : NNReal ↦ ∑ i : ι, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) y) =
        fun y ↦ (s y : ℝ≥0∞) := by
    funext y
    by_cases hy0 : s y = 0
    · have hterm_zero :
          ∀ i : ι, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) y = 0 := by
        intro i
        have hne0 : i.1 ≠ 0 := (Finset.mem_filter.mp i.2).2
        have hy_not : y ∉ A i := by
          intro hy
          have hsy : s y = i.1 := by
            simpa [A] using hy
          exact hne0 (hsy.symm.trans hy0)
        simp [A, a, hy_not]
      simp [hy0, hterm_zero]
    · let i0 : ι := ⟨s y, Finset.mem_filter.2 ⟨s.mem_range_self y, hy0⟩⟩
      have hsum :
          ∑ i : ι, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) y = (a i0 : ℝ≥0∞) := by
        rw [Finset.sum_eq_single i0]
        · simp [A, a, i0]
        · intro j hj hji
          have hy_not : y ∉ A j := by
            intro hy
            have hsy : s y = j.1 := by
              simpa [A] using hy
            exact hji (Subtype.ext (by simpa [i0] using hsy.symm))
          simp [A, a, hy_not]
        · intro hi0
          exact False.elim (hi0 (Finset.mem_univ i0))
      simpa [a, i0] using hsum
  have hcenteredFun :
      (fun y : NNReal ↦
        ∑ i : ι, (A i).indicator (fun _ ↦ Real.exp (-(a i : ℝ)) - 1) y) =
        fun y ↦ Real.exp (-(s y : ℝ)) - 1 := by
    funext y
    by_cases hy0 : s y = 0
    · have hterm_zero :
          ∀ i : ι, (A i).indicator (fun _ ↦ Real.exp (-(a i : ℝ)) - 1) y = 0 := by
        intro i
        have hne0 : i.1 ≠ 0 := (Finset.mem_filter.mp i.2).2
        have hy_not : y ∉ A i := by
          intro hy
          have hsy : s y = i.1 := by
            simpa [A] using hy
          exact hne0 (hsy.symm.trans hy0)
        simp [A, a, hy_not]
      simp [hy0, hterm_zero]
    · let i0 : ι := ⟨s y, Finset.mem_filter.2 ⟨s.mem_range_self y, hy0⟩⟩
      have hsum :
          ∑ i : ι, (A i).indicator (fun _ ↦ Real.exp (-(a i : ℝ)) - 1) y =
            Real.exp (-(a i0 : ℝ)) - 1 := by
        rw [Finset.sum_eq_single i0]
        · simp [A, a, i0]
        · intro j hj hji
          have hy_not : y ∉ A j := by
            intro hy
            have hsy : s y = j.1 := by
              simpa [A] using hy
            exact hji (Subtype.ext (by simpa [i0] using hsy.symm))
          simp [A, a, hy_not]
        · intro hi0
          exact False.elim (hi0 (Finset.mem_univ i0))
      simpa [a, i0] using hsum
  have hFiniteAll :
      ∀ᵐ ω ∂(P : Measure Ω), ∀ i : ι, X ω (A i) < ∞ := by
    rw [ae_all_iff]
    intro i
    exact poissonPointProcess_count_ae_ltTop P ν X hX (hA i) (hA_bdd i)
  have hsampleSum :
      ∀ ω,
        ∫⁻ y, (s y : ℝ≥0∞) ∂ X ω =
          ∑ i : ι, (a i : ℝ≥0∞) * X ω (A i) := by
    intro ω
    calc
      ∫⁻ y, (s y : ℝ≥0∞) ∂ X ω
          = ∫⁻ y, ∑ i : ι, (A i).indicator (fun _ ↦ (a i : ℝ≥0∞)) y ∂ X ω := by
              rw [← hsampleFun]
      _ = ∑ i : ι, (a i : ℝ≥0∞) * X ω (A i) := stepLintegral_eq_fintypeSum A a hA
  have hIntensitySum :
      ∑ i : ι, (ν (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1) =
        ∫ y : NNReal, (Real.exp (-(s y : ℝ)) - 1) ∂ν := by
    calc
      ∑ i : ι, (ν (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)
          = ∫ y : NNReal,
              ∑ i : ι, (A i).indicator (fun _ ↦ Real.exp (-(a i : ℝ)) - 1) y ∂ν := by
                symm
                simpa [mul_comm] using
                  stepIntegral_eq_fintypeSum A (fun i ↦ Real.exp (-(a i : ℝ)) - 1) hA hA_finite
      _ = ∫ y : NNReal, (Real.exp (-(s y : ℝ)) - 1) ∂ν := by
            simpa [hcenteredFun]
  have hraw :
      ∫ ω, Real.exp (-∑ i : ι, (a i : ℝ) * (X ω (A i)).toReal) ∂(P : Measure Ω) =
        Real.exp (∑ i : ι, (ν (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)) := by
    -- Proof comment: apply the finite-cell Laplace identity to the finitely many nonzero fibers.
    simpa [A, a] using
      ProbabilityTheory.disjointBoundedStepLaplaceTransformNNReal P ν X hX
        A a hA hA_bdd hdisj
  calc
    ∫ ω, ennrealExpNeg (∫⁻ y, (s y : ENNReal) ∂ X ω) ∂(P : Measure Ω)
        = ∫ ω, Real.exp (-∑ i : ι, (a i : ℝ) * (X ω (A i)).toReal) ∂(P : Measure Ω) := by
            refine integral_congr_ae ?_
            filter_upwards [hFiniteAll] with ω hω
            have hsum_ne_top :
                (∑ i : ι, (a i : ℝ≥0∞) * X ω (A i)) ≠ ∞ := by
              exact (ENNReal.sum_lt_top.mpr fun i _ ↦ ENNReal.mul_lt_top (by simp [a]) (hω i)).ne
            have hsum_toReal :
                (∑ i : ι, (a i : ℝ≥0∞) * X ω (A i)).toReal =
                  ∑ i : ι, (a i : ℝ) * (X ω (A i)).toReal := by
              rw [ENNReal.toReal_sum]
              · refine Finset.sum_congr rfl fun i _ ↦ ?_
                rw [ENNReal.toReal_mul]
                simp [a]
              · intro i _
                exact (ENNReal.mul_lt_top (by simp [a]) (hω i)).ne
            rw [hsampleSum ω, ennrealExpNeg, if_neg hsum_ne_top, hsum_toReal]
    _ = Real.exp (∑ i : ι, (ν (A i)).toReal * (Real.exp (-(a i : ℝ)) - 1)) := hraw
    _ = Real.exp (∫ y : NNReal, (Real.exp (-(s y : ℝ)) - 1) ∂ν) := by
          rw [hIntensitySum]

/-- Helper for Example 24.19: the standard cutoff `y ↦ if y ≤ n then min (g y) n else 0`
has bounded support inside `[0, n]`. -/
private def truncationKernel (g : NNReal → NNReal) (n : ℕ) (y : NNReal) : NNReal :=
  if y ≤ n then min (g y) n else 0

/-- Helper for Example 24.19: the cutoff kernels increase pointwise with the truncation level. -/
private lemma truncationKernel_mono
    (g : NNReal → NNReal) {n m : ℕ} (hnm : n ≤ m) (y : NNReal) :
    truncationKernel g n y ≤ truncationKernel g m y := by
  by_cases hyn : y ≤ n
  · have hnm' : (n : NNReal) ≤ m := by
      exact_mod_cast hnm
    have hym : y ≤ m := le_trans hyn hnm'
    simpa [truncationKernel, hyn, hym] using min_le_min_left (g y) hnm'
  · by_cases hym : y ≤ m
    · simp [truncationKernel, hyn, hym]
    · simp [truncationKernel, hyn, hym]

/-- Helper for Example 24.19: every fixed point is eventually unchanged by the truncation
kernel. -/
private lemma iSup_truncationKernel_eq
    (g : NNReal → NNReal) (y : NNReal) :
    (⨆ n : ℕ, (truncationKernel g n y : ℝ≥0∞)) = g y := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun n ↦ ?_
    by_cases hyn : y ≤ n
    · simp [truncationKernel, hyn]
    · simp [truncationKernel, hyn]
  · rcases exists_nat_gt (max (y : ℝ) (g y : ℝ)) with ⟨n, hn⟩
    have hy_le : y ≤ n := by
      exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn)
    have hg_le : g y ≤ n := by
      exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)
    refine le_iSup_of_le n ?_
    simp [truncationKernel, hy_le, min_eq_left hg_le]

/-- Helper for Example 24.19: the standard cutoff has bounded support inside the closed ball
`[0, n]`. -/
private lemma truncationSupport_isBounded
    (g : NNReal → NNReal) (n : ℕ) :
    Bornology.IsBounded (Function.support (truncationKernel g n)) := by
  have hsubset :
      Function.support (truncationKernel g n) ⊆ Metric.closedBall (0 : NNReal) n := by
    intro y hy
    have hy_le : y ≤ n := by
      by_cases hyn : y ≤ n
      · exact hyn
      · exfalso
        exact hy (by simp [truncationKernel, hyn])
    -- Proof comment: outside the radius-`n` ball the cutoff vanishes identically.
    simpa [Metric.mem_closedBall, NNReal.dist_eq, abs_of_nonneg y.2] using hy_le
  exact Metric.isBounded_closedBall.subset hsubset

/-- Helper for Example 24.19: a bounded-support `ℝ≥0∞`-valued kernel dominated by `1` has finite
integral under any locally finite measure on `NNReal`. -/
private lemma lintegral_ltTop_of_support_bounded_le_one
    {ν : Measure NNReal} [IsLocallyFiniteMeasure ν] {h : NNReal → ℝ≥0∞}
    (hsupport_bdd : Bornology.IsBounded (Function.support h))
    (h_le_one : ∀ y, h y ≤ 1) :
    ∫⁻ y, h y ∂ν < ∞ := by
  rcases hsupport_bdd.subset_closedBall (0 : NNReal) with ⟨r, hr⟩
  have hpoint :
      ∀ y,
        h y ≤ Set.indicator (Metric.closedBall (0 : NNReal) r) (fun _ ↦ (1 : ℝ≥0∞)) y := by
    intro y
    by_cases hy : y ∈ Metric.closedBall (0 : NNReal) r
    · simpa [hy] using h_le_one y
    · have hy_not_support : y ∉ Function.support h := by
        intro hy_support
        exact hy (hr hy_support)
      have hh0 : h y = 0 := by
        simpa [Function.mem_support] using hy_not_support
      simp [hy, hh0]
  calc
    ∫⁻ y, h y ∂ν
        ≤ ∫⁻ y,
            Set.indicator (Metric.closedBall (0 : NNReal) r) (fun _ ↦ (1 : ℝ≥0∞)) y ∂ν := by
              exact MeasureTheory.lintegral_mono hpoint
    _ = ν (Metric.closedBall (0 : NNReal) r) := by
          rw [MeasureTheory.lintegral_indicator_const (Metric.isClosed_closedBall.measurableSet)]
          simp
    _ < ∞ := by
          exact Metric.isBounded_closedBall.measure_lt_top

/-- Helper for Example 24.19: the Poisson exponent kernel vanishes whenever the underlying
nonnegative kernel vanishes. -/
private lemma support_poissonLaplaceKernel_subset_support
    {g : NNReal → ℝ≥0∞} :
    Function.support
        (fun y : NNReal ↦
          (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y))) ⊆
      Function.support g := by
  intro y hy
  by_contra hgy
  have hg0 : g y = 0 := by
    simpa [Function.mem_support] using hgy
  have hkernel0 :
      (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y)) = 0 := by
    simp [hg0, ennrealExpNeg]
  exact hy hkernel0

/-- Helper for Example 24.19: on finite `ℝ≥0∞` inputs, the Poisson exponent kernel is the
`ENNReal` lift of the real Bernstein kernel. -/
private lemma poissonLaplaceKernel_eq_ofReal_of_neTop
    {z : ℝ≥0∞} (hz : z ≠ ∞) :
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg z) =
      ENNReal.ofReal (1 - Real.exp (-z.toReal)) := by
  have hExpNonneg : 0 ≤ Real.exp (-z.toReal) := Real.exp_nonneg _
  -- Proof comment: once the `ENNReal` argument is finite, this is just `ofReal_sub`.
  simp [ennrealExpNeg, hz, ENNReal.ofReal_sub, hExpNonneg]

/-- Helper for Example 24.19: the Poisson exponent kernel is monotone on finite
`ℝ≥0∞`-arguments. -/
private lemma poissonLaplaceKernel_mono
    {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) (hab : a ≤ b) :
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg a) ≤
      (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg b) := by
  have htoReal : a.toReal ≤ b.toReal := ENNReal.toReal_mono hb hab
  have hreal : 1 - Real.exp (-a.toReal) ≤ 1 - Real.exp (-b.toReal) := by
    have hExp : Real.exp (-b.toReal) ≤ Real.exp (-a.toReal) := by
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  rw [poissonLaplaceKernel_eq_ofReal_of_neTop ha, poissonLaplaceKernel_eq_ofReal_of_neTop hb]
  exact ENNReal.ofReal_le_ofReal hreal

/-- Helper for Example 24.19: if a monotone sequence of finite `ℝ≥0∞` values has supremum `a`,
then applying `ennrealExpNeg` preserves the limit. -/
private lemma tendsto_ennrealExpNeg_of_monotone_iSup
    {u : ℕ → ℝ≥0∞} (hu_mono : Monotone u) (hu_finite : ∀ n, u n ≠ ∞)
    {a : ℝ≥0∞} (ha : (⨆ n, u n) = a) :
    Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (u n)) Filter.atTop (nhds (ennrealExpNeg a)) := by
  have hu_tendsto : Filter.Tendsto u Filter.atTop (nhds a) := by
    rw [← ha]
    exact tendsto_atTop_iSup hu_mono
  by_cases ha_top : a = ∞
  · have hcoe_top :
        Filter.Tendsto (fun n : ℕ ↦ (((u n).toNNReal : NNReal) : ℝ≥0∞))
          Filter.atTop (nhds ∞) := by
      have hcoe :
          (fun n : ℕ ↦ (((u n).toNNReal : NNReal) : ℝ≥0∞)) = u := by
        funext n
        exact ENNReal.coe_toNNReal (hu_finite n)
      simpa [ha_top, hcoe] using hu_tendsto
    have htoNN_top : Filter.Tendsto (fun n : ℕ ↦ (u n).toNNReal) Filter.atTop Filter.atTop :=
      (ENNReal.tendsto_coe_nhds_top).1 hcoe_top
    have htoReal_top : Filter.Tendsto (fun n : ℕ ↦ (u n).toReal) Filter.atTop Filter.atTop := by
      have hcoeReal :
          Filter.Tendsto (fun n : ℕ ↦ ((u n).toNNReal : ℝ)) Filter.atTop Filter.atTop :=
        (NNReal.tendsto_coe_atTop).2 htoNN_top
      simpa [ENNReal.coe_toNNReal_eq_toReal] using hcoeReal
    have hExpZero :
        Filter.Tendsto (fun n : ℕ ↦ Real.exp (-((u n).toReal))) Filter.atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp htoReal_top
    have hseq :
        (fun n : ℕ ↦ ennrealExpNeg (u n)) = fun n : ℕ ↦ Real.exp (-((u n).toReal)) := by
      funext n
      rw [ennrealExpNeg, if_neg (hu_finite n)]
    rw [ha_top, ennrealExpNeg]
    simp only [if_pos rfl]
    simpa [hseq] using hExpZero
  · have htoReal :
        Filter.Tendsto (fun n : ℕ ↦ (u n).toReal) Filter.atTop (nhds a.toReal) :=
      (ENNReal.tendsto_toReal ha_top).comp hu_tendsto
    have hExp :
        Filter.Tendsto (fun n : ℕ ↦ Real.exp (-((u n).toReal))) Filter.atTop
          (nhds (Real.exp (-a.toReal))) := by
      have hcont : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
        Real.continuous_exp.comp continuous_neg
      exact hcont.continuousAt.tendsto.comp htoReal
    have hseq :
        (fun n : ℕ ↦ ennrealExpNeg (u n)) = fun n : ℕ ↦ Real.exp (-((u n).toReal)) := by
      funext n
      rw [ennrealExpNeg, if_neg (hu_finite n)]
    have hlim : ennrealExpNeg a = Real.exp (-a.toReal) := by
      rw [ennrealExpNeg, if_neg ha_top]
    rw [hlim]
    simpa [hseq] using hExp

/-- Helper for Example 24.19: coercing a nonnegative real-valued kernel to `ℝ≥0∞` preserves its
support. -/
private lemma support_coe_nnreal_ennreal
    (g : NNReal → NNReal) :
    Function.support (fun y : NNReal ↦ (g y : ℝ≥0∞)) = Function.support g := by
  ext y
  simp [Function.mem_support]

/-- Helper for Example 24.19: the cutoff kernel is measurable whenever the original kernel is
measurable. -/
private lemma measurable_truncationKernel
    {g : NNReal → NNReal} (hg_meas : Measurable g) (n : ℕ) :
    Measurable (truncationKernel g n) := by
  have hmin : Measurable fun y : NNReal ↦ min (g y) n := hg_meas.min measurable_const
  simpa [truncationKernel] using
    hmin.piecewise (measurableSet_le measurable_id measurable_const) measurable_const

/-- Helper for Example 24.19: the `ENNReal` simple approximation vanishes wherever the target
function vanishes. -/
private lemma eapprox_eq_zero_of_eq_zero
    {g : NNReal → ℝ≥0∞} (hg_meas : Measurable g) (n : ℕ) {y : NNReal} (hy : g y = 0) :
    (MeasureTheory.SimpleFunc.eapprox g n : MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y = 0 := by
  apply le_antisymm
  · calc
      (MeasureTheory.SimpleFunc.eapprox g n : MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y
          ≤ ⨆ m,
              (MeasureTheory.SimpleFunc.eapprox g m : MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y := by
                exact le_iSup
                  (fun m ↦
                    (MeasureTheory.SimpleFunc.eapprox g m : MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y)
                  n
      _ = 0 := by
            simpa [hy] using MeasureTheory.SimpleFunc.iSup_eapprox_apply hg_meas y
  · exact bot_le

/-- Helper for Example 24.19: each simple approximation is supported inside the support of the
target function. -/
private lemma support_eapprox_subset_support
    {g : NNReal → ℝ≥0∞} (hg_meas : Measurable g) (n : ℕ) :
    Function.support (MeasureTheory.SimpleFunc.eapprox g n) ⊆ Function.support g := by
  intro y hy
  by_contra hgy
  have hg0 : g y = 0 := by
    simpa [Function.mem_support] using hgy
  have happrox0 :
      (MeasureTheory.SimpleFunc.eapprox g n : MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y = 0 :=
    eapprox_eq_zero_of_eq_zero hg_meas n hg0
  exact hy happrox0

/-- Helper for Example 24.19: after converting the finite `ENNReal` simple-approximation values
to `NNReal`, the support still stays inside the original support. -/
private lemma support_eapproxToNNReal_subset_support
    {g : NNReal → ℝ≥0∞} (hg_meas : Measurable g) (n : ℕ) :
    Function.support ((MeasureTheory.SimpleFunc.eapprox g n).map ENNReal.toNNReal) ⊆
      Function.support g := by
  intro y hy
  by_contra hgy
  have hg0 : g y = 0 := by
    simpa [Function.mem_support] using hgy
  have happrox0 :
      (MeasureTheory.SimpleFunc.eapprox g n : MeasureTheory.SimpleFunc NNReal ℝ≥0∞) y = 0 :=
    eapprox_eq_zero_of_eq_zero hg_meas n hg0
  have hmap0 :
      ((MeasureTheory.SimpleFunc.eapprox g n).map ENNReal.toNNReal) y = 0 := by
    rw [MeasureTheory.SimpleFunc.map_apply, happrox0]
    simp
  exact hy hmap0

/-- Helper for Example 24.19: a bounded-support simple `ℝ≥0∞`-valued kernel with finite values
already satisfies the executable one-dimensional Laplace identity. -/
private lemma simpleFuncLaplaceTransformENNRealFiniteSupport
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess ν P X)
    (s : MeasureTheory.SimpleFunc NNReal ℝ≥0∞)
    (hsupport_bdd : Bornology.IsBounded (Function.support s))
    (hsfinite : ∀ y, s y ≠ ∞) :
    ∫ ω, ennrealExpNeg (∫⁻ y, s y ∂ X ω) ∂(P : Measure Ω) =
      ennrealExpNeg
        (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s y)) ∂ν) := by
  letI : IsLocallyFiniteMeasure ν := hX.2.2.1
  let sNN : MeasureTheory.SimpleFunc NNReal NNReal := s.map ENNReal.toNNReal
  have hsNN_support_bdd :
      Bornology.IsBounded (Function.support sNN) := by
    refine hsupport_bdd.subset ?_
    intro y hy
    by_contra hsy
    have hs0 : s y = 0 := by
      simpa [Function.mem_support] using hsy
    have hsNN0 : sNN y = 0 := by
      rw [MeasureTheory.SimpleFunc.map_apply, hs0]
      simp [sNN]
    exact hy hsNN0
  have hsNN_eq : ∀ y, ((sNN y : NNReal) : ℝ≥0∞) = s y := by
    intro y
    rw [MeasureTheory.SimpleFunc.map_apply]
    simpa [sNN] using ENNReal.coe_toNNReal (hsfinite y)
  have hsNN_eq' : ∀ y, s y = ((sNN y : NNReal) : ℝ≥0∞) := by
    intro y
    symm
    exact hsNN_eq y
  have hkernel_nonneg :
      0 ≤ᵐ[ν] fun y : NNReal ↦ 1 - Real.exp (-(sNN y : ℝ)) := by
    filter_upwards with y
    have hle : Real.exp (-(sNN y : ℝ)) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [(sNN y).2]
    exact sub_nonneg.mpr hle
  have hkernel_meas :
      AEStronglyMeasurable (fun y : NNReal ↦ 1 - Real.exp (-(sNN y : ℝ))) ν := by
    have hmeas : Measurable (fun y : NNReal ↦ 1 - Real.exp (-(sNN y : ℝ))) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hkernel_rewrite :
      ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-(sNN y : ℝ))) ∂ν =
        ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s y)) ∂ν := by
    refine lintegral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
    calc
      ENNReal.ofReal (1 - Real.exp (-(sNN y : ℝ)))
          = ENNReal.ofReal (1 - Real.exp (-(s y).toReal)) := by
              have hs_toReal : (sNN y : ℝ) = (s y).toReal := by
                simpa using congrArg ENNReal.toReal (hsNN_eq y)
              rw [hs_toReal]
      _ = (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s y)) := by
            symm
            exact poissonLaplaceKernel_eq_ofReal_of_neTop (hsfinite y)
  have hkernel_finite :
      ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s y)) ∂ν < ∞ := by
    refine lintegral_ltTop_of_support_bounded_le_one ?_ ?_
    · refine hsupport_bdd.subset ?_
      intro y hy
      exact support_poissonLaplaceKernel_subset_support hy
    · intro y
      exact tsub_le_self
  have hkernel_integral :
      ∫ y : NNReal, (1 - Real.exp (-(sNN y : ℝ))) ∂ν =
        ENNReal.toReal
          (∫⁻ y, ENNReal.ofReal (1 - Real.exp (-(sNN y : ℝ))) ∂ν) :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae hkernel_nonneg hkernel_meas
  have hkernel_finite' :
      ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-(sNN y : ℝ))) ∂ν < ∞ := by
    rw [hkernel_rewrite]
    exact hkernel_finite
  have hkernel_int :
      Integrable (fun y : NNReal ↦ 1 - Real.exp (-(sNN y : ℝ))) ν := by
    exact
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hkernel_meas hkernel_nonneg).mp
        hkernel_finite'.ne
  have hcentered_eq :
      ∫ y : NNReal, (Real.exp (-(sNN y : ℝ)) - 1) ∂ν =
        -∫ y : NNReal, (1 - Real.exp (-(sNN y : ℝ))) ∂ν := by
    calc
      ∫ y : NNReal, (Real.exp (-(sNN y : ℝ)) - 1) ∂ν
          = ∫ y : NNReal, -(1 - Real.exp (-(sNN y : ℝ))) ∂ν := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
              ring
      _ = -∫ y : NNReal, (1 - Real.exp (-(sNN y : ℝ))) ∂ν := by
            simpa using (integral_neg (f := fun y : NNReal ↦ 1 - Real.exp (-(sNN y : ℝ))) (μ := ν))
  calc
    ∫ ω, ennrealExpNeg (∫⁻ y, s y ∂ X ω) ∂(P : Measure Ω)
        = ∫ ω, ennrealExpNeg (∫⁻ y, (sNN y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω) := by
            congr 1
            funext ω
            congr 1
            exact lintegral_congr_ae <| Filter.Eventually.of_forall hsNN_eq'
    _ = Real.exp (∫ y : NNReal, (Real.exp (-(sNN y : ℝ)) - 1) ∂ν) := by
          simpa [sNN] using simpleFuncLaplaceTransformNNReal P ν X hX sNN hsNN_support_bdd
    _ = Real.exp (-∫ y : NNReal, (1 - Real.exp (-(sNN y : ℝ))) ∂ν) := by
          rw [hcentered_eq]
    _ = ennrealExpNeg
          (∫⁻ y, ENNReal.ofReal (1 - Real.exp (-(sNN y : ℝ))) ∂ν) := by
            rw [ennrealExpNeg, if_neg hkernel_finite'.ne, ← hkernel_integral]
    _ = ennrealExpNeg
          (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s y)) ∂ν) := by
            rw [hkernel_rewrite]

/-- Helper for Example 24.19: a bounded measurable deterministic kernel with bounded support
satisfies the executable one-dimensional Laplace formula. -/
private theorem boundedSupportLaplaceTransformENNReal
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess ν P X)
    {g : NNReal → NNReal} (hg_meas : Measurable g)
    (hsupport_bdd : Bornology.IsBounded (Function.support g))
    (R : NNReal) (hbound : ∀ y, g y ≤ R) :
    ∫ ω, ennrealExpNeg (∫⁻ y, (g y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω) =
      ennrealExpNeg
        (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y : ℝ≥0∞)) ∂ν) := by
  letI : IsLocallyFiniteMeasure ν := hX.2.2.1
  let gENN : NNReal → ℝ≥0∞ := fun y ↦ (g y : ℝ≥0∞)
  let s : ℕ → MeasureTheory.SimpleFunc NNReal ℝ≥0∞ := MeasureTheory.SimpleFunc.eapprox gENN
  have hgENN_meas : Measurable gENN := measurable_coe_nnreal_ennreal.comp hg_meas
  have hsFormula :
      ∀ k,
        ∫ ω, ennrealExpNeg (∫⁻ y, s k y ∂ X ω) ∂(P : Measure Ω) =
          ennrealExpNeg
            (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s k y)) ∂ν) := by
    intro k
    refine simpleFuncLaplaceTransformENNRealFiniteSupport P ν X hX (s k) ?_ ?_
    · refine hsupport_bdd.subset ?_
      intro y hy
      simpa [gENN, support_coe_nnreal_ennreal g] using
        support_eapprox_subset_support hgENN_meas k hy
    · intro y
      exact (MeasureTheory.SimpleFunc.eapprox_lt_top gENN k y).ne
  rcases hsupport_bdd.subset_closedBall (0 : NNReal) with ⟨r, hr⟩
  let B : Set NNReal := Metric.closedBall (0 : NNReal) r
  have hB_meas : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  have hCountBall :
      ∀ᵐ ω ∂(P : Measure Ω), X ω B < ∞ :=
    poissonPointProcess_count_ae_ltTop P ν X hX hB_meas Metric.isBounded_closedBall
  have hg_bound_ball :
      ∀ y, gENN y ≤ Set.indicator B (fun _ ↦ (R : ℝ≥0∞)) y := by
    intro y
    by_cases hy : y ∈ B
    · simpa [gENN, B, hy] using
        (show (g y : ℝ≥0∞) ≤ (R : ℝ≥0∞) by exact_mod_cast hbound y)
    · have hy_not_support : y ∉ Function.support g := by
        intro hy_support
        exact hy (hr hy_support)
      have hg0 : g y = 0 := by
        simpa [Function.mem_support] using hy_not_support
      simp [gENN, B, hy, hg0]
  have hs_bound_ball :
      ∀ k y, s k y ≤ Set.indicator B (fun _ ↦ (R : ℝ≥0∞)) y := by
    intro k y
    by_cases hy : y ∈ B
    · have hs_le_g : s k y ≤ gENN y := by
        calc
          s k y ≤ ⨆ m, s m y := le_iSup (fun m ↦ s m y) k
          _ = gENN y := by
                simpa [s, gENN] using MeasureTheory.SimpleFunc.iSup_eapprox_apply hgENN_meas y
      exact hs_le_g.trans (by simpa [B, hy] using hg_bound_ball y)
    · have hy_not_support_g : y ∉ Function.support g := by
        intro hy_support
        exact hy (hr hy_support)
      have hy_not_support_s : y ∉ Function.support (s k) := by
        intro hy_support
        exact hy_not_support_g <| by
          simpa [gENN, support_coe_nnreal_ennreal g] using
            support_eapprox_subset_support hgENN_meas k hy_support
      have hs0 : s k y = 0 := by
        simpa [Function.mem_support] using hy_not_support_s
      simp [B, hy, hs0]
  have hLeft_meas :
      ∀ k,
        AEStronglyMeasurable
          (fun ω ↦ ennrealExpNeg (∫⁻ y, s k y ∂ X ω)) (P : Measure Ω) := by
    intro k
    refine (measurable_ennrealExpNeg.comp ?_).aestronglyMeasurable
    refine (Measure.measurable_lintegral (s k).measurable).comp ?_
    exact hX.1.measurable
  have hLeft_bound :
      ∀ k,
        ∀ᵐ ω ∂(P : Measure Ω), ‖ennrealExpNeg (∫⁻ y, s k y ∂ X ω)‖ ≤ (1 : ℝ) := by
    intro k
    filter_upwards with ω
    have hnonneg : 0 ≤ ennrealExpNeg (∫⁻ y, s k y ∂ X ω) := ennrealExpNeg_nonneg _
    have hle : ennrealExpNeg (∫⁻ y, s k y ∂ X ω) ≤ 1 := ennrealExpNeg_le_one _
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hLeft_lim :
      ∀ᵐ ω ∂(P : Measure Ω),
        Filter.Tendsto (fun k : ℕ ↦ ennrealExpNeg (∫⁻ y, s k y ∂ X ω))
          Filter.atTop (nhds (ennrealExpNeg (∫⁻ y, gENN y ∂ X ω))) := by
    filter_upwards [hCountBall] with ω hω
    let u : ℕ → ℝ≥0∞ := fun k ↦ ∫⁻ y, s k y ∂ X ω
    have hu_mono : Monotone u := by
      intro i j hij
      exact MeasureTheory.lintegral_mono fun y ↦ MeasureTheory.SimpleFunc.monotone_eapprox gENN hij y
    have hu_finite : ∀ k, u k ≠ ∞ := by
      intro k
      have hu_le :
          u k ≤ ∫⁻ y, Set.indicator B (fun _ ↦ (R : ℝ≥0∞)) y ∂ X ω := by
        exact MeasureTheory.lintegral_mono (hs_bound_ball k)
      have hBoundedCell :
          ∫⁻ y, Set.indicator B (fun _ ↦ (R : ℝ≥0∞)) y ∂ X ω = (R : ℝ≥0∞) * X ω B := by
        rw [MeasureTheory.lintegral_indicator_const hB_meas]
      have hBoundedCell_lt :
          ∫⁻ y, Set.indicator B (fun _ ↦ (R : ℝ≥0∞)) y ∂ X ω < ∞ := by
        simpa [hBoundedCell] using ENNReal.mul_lt_top (by simp) hω
      refine (lt_of_le_of_lt ?_ hBoundedCell_lt).ne
      · simpa [u, hBoundedCell] using hu_le
    have hu_iSup : (⨆ k, u k) = ∫⁻ y, gENN y ∂ X ω := by
      calc
        (⨆ k, u k) = ⨆ k, (s k).lintegral (X ω) := by
          congr with k
          simpa [u] using (s k).lintegral_eq_lintegral (X ω)
        _ = ∫⁻ y, gENN y ∂ X ω := (MeasureTheory.lintegral_eq_iSup_eapprox_lintegral hgENN_meas).symm
    simpa [u, gENN] using tendsto_ennrealExpNeg_of_monotone_iSup hu_mono hu_finite hu_iSup
  have hLeft_tendsto :
      Filter.Tendsto
        (fun k : ℕ ↦ ∫ ω, ennrealExpNeg (∫⁻ y, s k y ∂ X ω) ∂(P : Measure Ω))
        Filter.atTop
        (nhds (∫ ω, ennrealExpNeg (∫⁻ y, gENN y ∂ X ω) ∂(P : Measure Ω))) := by
    simpa [gENN] using
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ : Ω ↦ (1 : ℝ)) hLeft_meas (integrable_const 1) hLeft_bound hLeft_lim
  let v : ℕ → ℝ≥0∞ := fun k ↦
    ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s k y)) ∂ν
  have hv_mono : Monotone v := by
    intro i j hij
    refine MeasureTheory.lintegral_mono fun y ↦ ?_
    exact poissonLaplaceKernel_mono
      (MeasureTheory.SimpleFunc.eapprox_lt_top gENN i y).ne
      (MeasureTheory.SimpleFunc.eapprox_lt_top gENN j y).ne
      (MeasureTheory.SimpleFunc.monotone_eapprox gENN hij y)
  have hv_finite : ∀ k, v k ≠ ∞ := by
    intro k
    have hkernel_support_bdd :
        Bornology.IsBounded
          (Function.support
            (fun y : NNReal ↦
              (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s k y)))) := by
      refine hsupport_bdd.subset ?_
      intro y hy
      exact
        (by
          simpa [gENN, support_coe_nnreal_ennreal g] using
            support_eapprox_subset_support hgENN_meas k
              (support_poissonLaplaceKernel_subset_support hy))
    exact (lintegral_ltTop_of_support_bounded_le_one hkernel_support_bdd
      (fun y ↦ tsub_le_self)).ne
  have hv_iSup :
      (⨆ k, v k) =
        ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gENN y)) ∂ν := by
    calc
      (⨆ k, v k)
          =
        ∫⁻ y, ⨆ k, ((1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s k y))) ∂ν := by
              symm
              exact MeasureTheory.lintegral_iSup
                (fun k ↦ by
                  exact measurable_const.sub
                    (ENNReal.measurable_ofReal.comp
                      (measurable_ennrealExpNeg.comp (s k).measurable)))
                (fun i j hij y ↦
                  poissonLaplaceKernel_mono
                    (MeasureTheory.SimpleFunc.eapprox_lt_top gENN i y).ne
                    (MeasureTheory.SimpleFunc.eapprox_lt_top gENN j y).ne
                    (MeasureTheory.SimpleFunc.monotone_eapprox gENN hij y))
      _ =
        ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gENN y)) ∂ν := by
          refine MeasureTheory.lintegral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          let w : ℕ → ℝ≥0∞ := fun k ↦
            (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (s k y))
          have hw_mono : Monotone w := by
            intro i j hij
            exact poissonLaplaceKernel_mono
              (MeasureTheory.SimpleFunc.eapprox_lt_top gENN i y).ne
              (MeasureTheory.SimpleFunc.eapprox_lt_top gENN j y).ne
              (MeasureTheory.SimpleFunc.monotone_eapprox gENN hij y)
          have hgENN_ne_top : gENN y ≠ ∞ := by
            simp [gENN]
          have hw_tendsto :
              Filter.Tendsto w Filter.atTop
                (nhds ((1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gENN y)))) := by
            have hs_tendsto :
                Filter.Tendsto (fun k : ℕ ↦ s k y) Filter.atTop (nhds (gENN y)) := by
              simpa [s, gENN] using MeasureTheory.SimpleFunc.tendsto_eapprox hgENN_meas y
            have hs_toReal_tendsto :
                Filter.Tendsto (fun k : ℕ ↦ (s k y).toReal) Filter.atTop (nhds (g y : ℝ)) := by
              exact (ENNReal.tendsto_toReal hgENN_ne_top).comp hs_tendsto
            have hkernel_tendsto :
                Filter.Tendsto
                  (fun k : ℕ ↦ ENNReal.ofReal (1 - Real.exp (-((s k y).toReal))))
                  Filter.atTop (nhds (ENNReal.ofReal (1 - Real.exp (-(g y : ℝ))))) := by
              have hcont : Continuous (fun r : ℝ ↦ ENNReal.ofReal (1 - Real.exp (-r))) :=
                ENNReal.continuous_ofReal.comp
                  (continuous_const.sub (Real.continuous_exp.comp continuous_neg))
              exact hcont.continuousAt.tendsto.comp hs_toReal_tendsto
            have hw_seq :
                (fun k : ℕ ↦ w k) =
                  fun k : ℕ ↦ ENNReal.ofReal (1 - Real.exp (-((s k y).toReal))) := by
              funext k
              simpa [w] using
                (poissonLaplaceKernel_eq_ofReal_of_neTop
                  (MeasureTheory.SimpleFunc.eapprox_lt_top gENN k y).ne)
            have hw_lim :
                (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gENN y)) =
                  ENNReal.ofReal (1 - Real.exp (-(g y : ℝ))) := by
              simpa [gENN] using
                poissonLaplaceKernel_eq_ofReal_of_neTop hgENN_ne_top
            rw [hw_lim]
            simpa [w, hw_seq] using hkernel_tendsto
          exact tendsto_nhds_unique (tendsto_atTop_iSup hw_mono) hw_tendsto
  have hRight_tendsto :
      Filter.Tendsto (fun k : ℕ ↦ ennrealExpNeg (v k)) Filter.atTop
        (nhds
          (ennrealExpNeg
            (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gENN y)) ∂ν))) := by
    exact tendsto_ennrealExpNeg_of_monotone_iSup hv_mono hv_finite hv_iSup
  have hSeqEq :
      (fun k : ℕ ↦ ∫ ω, ennrealExpNeg (∫⁻ y, s k y ∂ X ω) ∂(P : Measure Ω)) =
        (fun k : ℕ ↦ ennrealExpNeg (v k)) := by
    funext k
    simpa [v] using hsFormula k
  rw [hSeqEq] at hLeft_tendsto
  exact tendsto_nhds_unique hLeft_tendsto hRight_tendsto

/-- Helper for Example 24.19: the missing executable `ENNReal` Laplace bridge for deterministic
Poisson integrands over an arbitrary one-dimensional PPP. -/
private theorem deterministicPoissonIntegral_laplaceTransformENNReal
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess ν P X)
    {g : NNReal → NNReal} (hg_meas : Measurable g) :
    ∫ ω, ennrealExpNeg (∫⁻ y, (g y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω) =
      ennrealExpNeg
        (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y : ℝ≥0∞)) ∂ν) := by
  letI : IsLocallyFiniteMeasure ν := hX.2.2.1
  -- Route correction: Theorem 24.14 is only a source-facing placeholder here, so rebuild the
  -- executable Laplace bridge from bounded-support cutoffs and monotone convergence.
  let gCut : ℕ → NNReal → NNReal := fun n y ↦ truncationKernel g n y
  have hgCut_meas : ∀ n, Measurable (gCut n) := by
    intro n
    simpa [gCut] using measurable_truncationKernel hg_meas n
  have hCutFormula :
      ∀ n,
        ∫ ω, ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω) =
          ennrealExpNeg
            (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gCut n y : ℝ≥0∞)) ∂ν) := by
    intro n
    refine boundedSupportLaplaceTransformENNReal P ν X hX (hgCut_meas n)
      (truncationSupport_isBounded g n) n ?_
    intro y
    by_cases hyn : y ≤ n
    · simp [gCut, truncationKernel, hyn]
    · simp [gCut, truncationKernel, hyn]
  have hCountAll :
      ∀ᵐ ω ∂(P : Measure Ω), ∀ n : ℕ, X ω (Metric.closedBall (0 : NNReal) n) < ∞ := by
    rw [ae_all_iff]
    intro n
    exact poissonPointProcess_count_ae_ltTop P ν X hX
      (Metric.isClosed_closedBall.measurableSet) Metric.isBounded_closedBall
  have hLeft_meas :
      ∀ n,
        AEStronglyMeasurable
          (fun ω ↦ ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω)) (P : Measure Ω) := by
    intro n
    refine (measurable_ennrealExpNeg.comp ?_).aestronglyMeasurable
    refine (Measure.measurable_lintegral
      (measurable_coe_nnreal_ennreal.comp (hgCut_meas n))).comp ?_
    exact hX.1.measurable
  have hLeft_bound :
      ∀ n,
        ∀ᵐ ω ∂(P : Measure Ω),
          ‖ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω)‖ ≤ (1 : ℝ) := by
    intro n
    filter_upwards with ω
    have hnonneg : 0 ≤ ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω) := ennrealExpNeg_nonneg _
    have hle : ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω) ≤ 1 := ennrealExpNeg_le_one _
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hLeft_lim :
      ∀ᵐ ω ∂(P : Measure Ω),
        Filter.Tendsto
          (fun n : ℕ ↦ ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω))
          Filter.atTop (nhds (ennrealExpNeg (∫⁻ y, (g y : ℝ≥0∞) ∂ X ω))) := by
    filter_upwards [hCountAll] with ω hω
    let u : ℕ → ℝ≥0∞ := fun n ↦ ∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω
    have hu_mono : Monotone u := by
      intro i j hij
      exact MeasureTheory.lintegral_mono fun y ↦ by
        have hmono : gCut i y ≤ gCut j y := by
          simpa [gCut] using truncationKernel_mono g hij y
        simpa using
          (show ((gCut i y : NNReal) : ℝ≥0∞) ≤ ((gCut j y : NNReal) : ℝ≥0∞) by
            exact_mod_cast hmono)
    have hu_finite : ∀ n, u n ≠ ∞ := by
      intro n
      have hu_le :
          u n ≤ ∫⁻ y,
            Set.indicator (Metric.closedBall (0 : NNReal) n) (fun _ ↦ (n : ℝ≥0∞)) y ∂ X ω := by
        refine MeasureTheory.lintegral_mono fun y ↦ ?_
        by_cases hyn : y ∈ Metric.closedBall (0 : NNReal) n
        · have hy_le : y ≤ n := by
            simpa [Metric.mem_closedBall, NNReal.dist_eq, abs_of_nonneg y.2] using hyn
          simp [gCut, truncationKernel, hy_le, hyn]
        · have hy_not : ¬ y ≤ n := by
            intro hy_le
            exact hyn (by
              simpa [Metric.mem_closedBall, NNReal.dist_eq, abs_of_nonneg y.2] using hy_le)
          simp [gCut, truncationKernel, hy_not, hyn]
      have hCell :
          ∫⁻ y,
              Set.indicator (Metric.closedBall (0 : NNReal) n) (fun _ ↦ (n : ℝ≥0∞)) y ∂ X ω =
            (n : ℝ≥0∞) * X ω (Metric.closedBall (0 : NNReal) n) := by
        rw [MeasureTheory.lintegral_indicator_const (Metric.isClosed_closedBall.measurableSet)]
      have hCell_lt :
          ∫⁻ y,
              Set.indicator (Metric.closedBall (0 : NNReal) n) (fun _ ↦ (n : ℝ≥0∞)) y ∂ X ω < ∞ := by
        simpa [hCell] using ENNReal.mul_lt_top (by simp) (hω n)
      refine (lt_of_le_of_lt ?_ hCell_lt).ne
      · simpa [u, hCell] using hu_le
    have hu_iSup : (⨆ n, u n) = ∫⁻ y, (g y : ℝ≥0∞) ∂ X ω := by
      calc
        (⨆ n, u n) = ∫⁻ y, ⨆ n, (gCut n y : ℝ≥0∞) ∂ X ω := by
          symm
          exact MeasureTheory.lintegral_iSup
            (fun n ↦ measurable_coe_nnreal_ennreal.comp (hgCut_meas n))
            (fun i j hij y ↦ by
              have hmono : gCut i y ≤ gCut j y := by
                simpa [gCut] using truncationKernel_mono g hij y
              simpa using
                (show ((gCut i y : NNReal) : ℝ≥0∞) ≤ ((gCut j y : NNReal) : ℝ≥0∞) by
                  exact_mod_cast hmono))
        _ = ∫⁻ y, (g y : ℝ≥0∞) ∂ X ω := by
          refine MeasureTheory.lintegral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          simpa [gCut] using iSup_truncationKernel_eq g y
    simpa [u] using tendsto_ennrealExpNeg_of_monotone_iSup hu_mono hu_finite hu_iSup
  have hLeft_tendsto :
      Filter.Tendsto
        (fun n : ℕ ↦
          ∫ ω, ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω))
        Filter.atTop
        (nhds (∫ ω, ennrealExpNeg (∫⁻ y, (g y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω))) := by
    simpa [gCut] using
      MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ : Ω ↦ (1 : ℝ)) hLeft_meas (integrable_const 1) hLeft_bound hLeft_lim
  let v : ℕ → ℝ≥0∞ := fun n ↦
    ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gCut n y : ℝ≥0∞)) ∂ν
  have hv_mono : Monotone v := by
    intro i j hij
    refine MeasureTheory.lintegral_mono fun y ↦ ?_
    have hmono : gCut i y ≤ gCut j y := by
      simpa [gCut] using truncationKernel_mono g hij y
    exact poissonLaplaceKernel_mono (by simp) (by simp) <| by
      simpa using
        (show ((gCut i y : NNReal) : ℝ≥0∞) ≤ ((gCut j y : NNReal) : ℝ≥0∞) by
          exact_mod_cast hmono)
  have hv_finite : ∀ n, v n ≠ ∞ := by
    intro n
    have hkernel_support_bdd :
        Bornology.IsBounded
          (Function.support
            (fun y : NNReal ↦
              (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gCut n y : ℝ≥0∞)))) := by
      refine (truncationSupport_isBounded g n).subset ?_
      intro y hy
      simpa [gCut, support_coe_nnreal_ennreal (truncationKernel g n)] using
        support_poissonLaplaceKernel_subset_support hy
    exact (lintegral_ltTop_of_support_bounded_le_one hkernel_support_bdd
      (fun y ↦ tsub_le_self)).ne
  have hv_iSup :
      (⨆ n, v n) =
        ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y : ℝ≥0∞)) ∂ν := by
    calc
      (⨆ n, v n)
          =
        ∫⁻ y, ⨆ n, ((1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (gCut n y : ℝ≥0∞))) ∂ν := by
              symm
              exact MeasureTheory.lintegral_iSup
                (fun n ↦ by
                  exact measurable_const.sub
                    (ENNReal.measurable_ofReal.comp
                      (measurable_ennrealExpNeg.comp
                        (measurable_coe_nnreal_ennreal.comp (hgCut_meas n)))))
                (fun i j hij y ↦ by
                  have hmono : gCut i y ≤ gCut j y := by
                    simpa [gCut] using truncationKernel_mono g hij y
                  exact poissonLaplaceKernel_mono (by simp) (by simp) <| by
                    simpa using
                      (show ((gCut i y : NNReal) : ℝ≥0∞) ≤ ((gCut j y : NNReal) : ℝ≥0∞) by
                        exact_mod_cast hmono))
      _ =
        ∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y : ℝ≥0∞)) ∂ν := by
          refine MeasureTheory.lintegral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          refine le_antisymm ?_ ?_
          · exact iSup_le fun n ↦ by
              have hle : gCut n y ≤ g y := by
                simpa [gCut] using
                  (show truncationKernel g n y ≤ g y by
                    by_cases hyn : y ≤ n
                    · simp [truncationKernel, hyn]
                    · simp [truncationKernel, hyn])
              exact poissonLaplaceKernel_mono (by simp) (by simp) <| by
                simpa using
                  (show ((gCut n y : NNReal) : ℝ≥0∞) ≤ (g y : ℝ≥0∞) by
                    exact_mod_cast hle)
          · rcases exists_nat_gt (max (y : ℝ) (g y : ℝ)) with ⟨n, hn⟩
            have hy_le : y ≤ n := by
              exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_left _ _) hn)
            have hg_le : g y ≤ n := by
              exact_mod_cast le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)
            refine le_iSup_of_le n ?_
            simp [gCut, truncationKernel, hy_le, min_eq_left hg_le]
  have hRight_tendsto :
      Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (v n)) Filter.atTop
        (nhds
          (ennrealExpNeg
            (∫⁻ y, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (g y : ℝ≥0∞)) ∂ν))) := by
    exact tendsto_ennrealExpNeg_of_monotone_iSup hv_mono hv_finite hv_iSup
  have hSeqEq :
      (fun n : ℕ ↦
          ∫ ω, ennrealExpNeg (∫⁻ y, (gCut n y : ℝ≥0∞) ∂ X ω) ∂(P : Measure Ω)) =
        (fun n : ℕ ↦ ennrealExpNeg (v n)) := by
    funext n
    simpa [v] using hCutFormula n
  rw [hSeqEq] at hLeft_tendsto
  exact tendsto_nhds_unique hLeft_tendsto hRight_tendsto

/-- Helper for Example 24.19: the executable linear-kernel Laplace transform for a
one-dimensional Poisson point process. This private owner sits before the finiteness and
real-valued Laplace theorems so they can reuse it without forward references. -/
private lemma nnrealLinearLaplaceTransformOfIsPoissonPointProcessAux
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess ν P X) (u : ℝ) (hu : 0 ≤ u) :
    ∫ ω, ennrealExpNeg (∫⁻ x, ENNReal.ofReal u * x ∂ X ω) ∂(P : Measure Ω) =
      ennrealExpNeg
        (∫⁻ x, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (ENNReal.ofReal u * x)) ∂ν) := by
  let c : NNReal := ⟨u, hu⟩
  let scaledKernel : NNReal → NNReal := fun x ↦ c * x
  have hscaledKernel_meas : Measurable scaledKernel := by
    simpa [scaledKernel] using measurable_const.mul measurable_id
  have hc : ((c : NNReal) : ℝ≥0∞) = ENNReal.ofReal u := by
    simpa [c] using ENNReal.coe_nnreal_eq c
  -- Proof comment: specialize the deterministic Laplace bridge to the linear kernel `x ↦ u * x`.
  convert
    (deterministicPoissonIntegral_laplaceTransformENNReal
      (P := P) (ν := ν) (X := X) hX (g := scaledKernel) hscaledKernel_meas) using 1
  · congr 1
    ext ω
    congr 1
    refine lintegral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
    simp [scaledKernel, hc]
  · congr 1
    refine lintegral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
    simp [scaledKernel, hc]

/-- Helper for Example 24.19: the finiteness TFAE for the one-dimensional Poisson integral on
`NNReal`. -/
theorem poissonPointIntegral_finite_tfae
    {P : ProbabilityMeasure Ω} {ν : Measure NNReal} {X : Ω → Measure NNReal}
    (hX : IsPoissonPointProcessOnNNReal ν P X) :
    List.TFAE
      [ 0 < (P : Measure Ω) {ω | poissonPointIntegral X ω < ∞}
      , (P : Measure Ω) {ω | poissonPointIntegral X ω < ∞} = 1
      , Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν
      ] :=
by
  let Y : Ω → ℝ≥0∞ := poissonPointIntegral X
  let A : Set Ω := {ω | Y ω < ∞}
  let laplaceEvent : Ω → ℝ := Set.indicator A fun ω ↦ Real.exp (-(Y ω).toReal)
  let idNNReal : NonnegativeMeasurableFunction NNReal :=
    ⟨fun x ↦ (x : ℝ≥0∞), measurable_coe_nnreal_ennreal⟩
  let exponent : ℝ≥0∞ :=
    ∫⁻ x, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg ((idNNReal x : ℝ≥0∞))) ∂ν
  have hPPP : ProbabilityTheory.IsPoissonPointProcess ν P X := by
    simpa [IsPoissonPointProcessOnNNReal] using hX
  have hY_meas : Measurable Y := by
    -- Proof comment: the Poisson integral is measurable because the random-measure map is.
    simpa [Y, poissonPointIntegral_def] using
      (Measure.measurable_lintegral measurable_coe_nnreal_ennreal).comp hPPP.1.measurable
  have hA_meas : MeasurableSet A := measurableSet_lt hY_meas measurable_const
  have hlaplaceEvent_eq :
      (fun ω ↦ ennrealExpNeg (Y ω)) = laplaceEvent := by
    funext ω
    by_cases hω : Y ω = ∞
    · have hω' : ω ∉ A := by simpa [A, Y] using hω
      simp [laplaceEvent, A, hω, hω', ennrealExpNeg_top]
    · have hω' : ω ∈ A := by
        simpa [A, Y, lt_top_iff_ne_top] using hω
      simp [laplaceEvent, A, hω', ennrealExpNeg, hω]
  have hlaplaceEvent_nonneg : ∀ ω, 0 ≤ laplaceEvent ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp [laplaceEvent, hω, Real.exp_pos]
      exact le_of_lt (Real.exp_pos _)
    · simp [laplaceEvent, hω]
  have hlaplaceEvent_meas : AEStronglyMeasurable laplaceEvent (P : Measure Ω) := by
    have hcore : Measurable (fun ω ↦ Real.exp (-(Y ω).toReal)) := by
      have htoReal : Measurable (fun ω ↦ (Y ω).toReal) :=
        ENNReal.measurable_toReal.comp hY_meas
      fun_prop
    exact (hcore.stronglyMeasurable.indicator hA_meas).aestronglyMeasurable
  have hlaplaceEvent_integrable : Integrable laplaceEvent (P : Measure Ω) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hlaplaceEvent_meas ?_
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · have hle : Real.exp (-(Y ω).toReal) ≤ 1 := by
        have htoReal_nonneg : 0 ≤ (Y ω).toReal := ENNReal.toReal_nonneg
        exact Real.exp_le_one_iff.mpr (by linarith)
      simp [laplaceEvent, hω, abs_of_nonneg (hlaplaceEvent_nonneg ω), hle]
    · simp [laplaceEvent, hω]
  have hsupport :
      Function.support laplaceEvent = A := by
    ext ω
    by_cases hω : ω ∈ A
    · simp [laplaceEvent, hω, Real.exp_pos]
    · simp [laplaceEvent, hω]
  have hleft_pos :
      0 < ∫ ω, ennrealExpNeg (Y ω) ∂(P : Measure Ω) ↔ 0 < (P : Measure Ω) A := by
    rw [hlaplaceEvent_eq, MeasureTheory.integral_pos_iff_support_of_nonneg
      hlaplaceEvent_nonneg hlaplaceEvent_integrable, hsupport]
  have hLaplaceOne :
      ∫ ω, ennrealExpNeg (Y ω) ∂(P : Measure Ω) = ennrealExpNeg exponent := by
    -- Proof comment: specialize the executable Laplace bridge to the identity kernel.
    simpa [Y, exponent, idNNReal, poissonPointIntegral_def] using
      nnrealLinearLaplaceTransformOfIsPoissonPointProcessAux P ν X hPPP 1 (by positivity)
  have hexponent_eq :
      exponent = ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(x : ℝ))) ∂ν := by
    -- Proof comment: on finite `NNReal` inputs, the exponent kernel is exactly `ofReal (1-e^{-x})`.
    refine lintegral_congr_ae ?_
    filter_upwards with x
    simpa [exponent, idNNReal] using poissonLaplaceKernel_eq_ofReal x
  have hkernel_nonneg :
      0 ≤ᵐ[ν] fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ)) :=
    Filter.Eventually.of_forall fun x ↦
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by simpa using x.2))
  have hkernel_meas :
      AEStronglyMeasurable (fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ))) ν := by
    have hmeas : Measurable (fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ))) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hright_pos :
      0 < ennrealExpNeg exponent ↔
        Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν := by
    have hexponent_finite :
        exponent ≠ ∞ ↔ Integrable (fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ))) ν := by
      rw [hexponent_eq]
      exact MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hkernel_meas hkernel_nonneg
    have hExpPos : 0 < ennrealExpNeg exponent ↔ exponent ≠ ∞ := by
      by_cases htop : exponent = ∞
      · simp [ennrealExpNeg, htop]
      · simp [ennrealExpNeg, htop, Real.exp_pos]
    exact hExpPos.trans <| hexponent_finite.trans (poissonLaplaceKernel_integrable_iff ν)
  tfae_have 1 → 3 := by
    -- Proof comment: positive finiteness probability makes the Laplace expectation positive.
    intro hPos
    exact hright_pos.mp <| by
      rw [← hLaplaceOne]
      exact hleft_pos.mpr hPos
  tfae_have 2 → 1 := by
    intro hAlmostSure
    rw [hAlmostSure]
    positivity
  tfae_have 3 → 1 := by
    -- Proof comment: the same `u = 1` Laplace identity runs in reverse.
    intro hInt
    exact hleft_pos.mp <| by
      rw [hLaplaceOne]
      exact hright_pos.mpr hInt
  tfae_have 3 → 2 := by
    intro hInt
    let scaledId : ℕ → NonnegativeMeasurableFunction NNReal := fun n ↦
      ⟨fun x ↦ ENNReal.ofReal (invSuccScaleReal n) * x,
        measurable_const.mul measurable_coe_nnreal_ennreal⟩
    let scaledExponent : ℕ → ℝ≥0∞ := fun n ↦
      ∫⁻ x, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (scaledId n x)) ∂ν
    have hs_nonneg : ∀ n, 0 ≤ invSuccScaleReal n := by
      intro n
      have hn : 0 ≤ (n : ℝ) + 1 := by positivity
      simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
    have hs_le_one : ∀ n, invSuccScaleReal n ≤ 1 := by
      intro n
      have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      simpa [invSuccScaleReal] using inv_le_one_of_one_le₀ hn'
    have hkernel_meas :
        ∀ n, AEStronglyMeasurable
          (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ν := by
      intro n
      have hmeas : Measurable (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) := by
        fun_prop
      exact hmeas.aestronglyMeasurable
    have hkernel_nonneg :
        ∀ n, 0 ≤ᵐ[ν] fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) := by
      intro n
      filter_upwards with x
      have harg_nonneg : 0 ≤ invSuccScaleReal n * (x : ℝ) := by
        nlinarith [hs_nonneg n, x.2]
      have hle : Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        linarith
      exact sub_nonneg.mpr hle
    have hkernel_int :
        ∀ n, Integrable (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ν := by
      intro n
      refine Integrable.mono' hInt (hkernel_meas n) ?_
      filter_upwards with x
      have hnonneg : 0 ≤ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) := by
        have harg_nonneg : 0 ≤ invSuccScaleReal n * (x : ℝ) := by
          nlinarith [hs_nonneg n, x.2]
        have hle : Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ 1 := by
          refine Real.exp_le_one_iff.mpr ?_
          linarith
        exact sub_nonneg.mpr hle
      have hle :
          1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ min (1 : ℝ) (x : ℝ) :=
        poissonExpKernel_scale_le_minOne (invSuccScaleReal n) (hs_le_one n) x
      simpa [Real.norm_of_nonneg hnonneg] using hle
    have hscaledExponent_eq :
        ∀ n,
          scaledExponent n =
            ENNReal.ofReal
              (∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν) := by
      intro n
      calc
        scaledExponent n
            = ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν := by
                refine lintegral_congr_ae ?_
                filter_upwards with x
                simpa [scaledExponent, scaledId, ENNReal.ofReal_mul, hs_nonneg n] using
                  poissonLaplaceKernel_scale_eq_ofReal (invSuccScaleReal n) (hs_nonneg n) x
        _ = ENNReal.ofReal
              (∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν) := by
              symm
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                (hkernel_int n) (hkernel_nonneg n)
    have hLeft :
        Filter.Tendsto
          (fun n : ℕ ↦ ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂
            (P : Measure Ω))
          Filter.atTop (nhds ((P : Measure Ω) A).toReal) :=
      poissonPointIntegralLaplace_invSucc_tendsto_measureFinite (μ := (P : Measure Ω)) hY_meas
    have hRight :
        Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (scaledExponent n)) Filter.atTop (nhds 1) := by
      have hrewrite :
          (fun n : ℕ ↦ ennrealExpNeg (scaledExponent n)) =
            (fun n : ℕ ↦
              Real.exp
                (-(∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν))) := by
        funext n
        have hIntegral_nonneg :
            0 ≤ ∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) ∂ν :=
          integral_nonneg_of_ae (hkernel_nonneg n)
        rw [hscaledExponent_eq n, ennrealExpNeg]
        simp [hIntegral_nonneg]
      rw [hrewrite]
      have hcont : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
        Real.continuous_exp.comp continuous_neg
      simpa using hcont.continuousAt.tendsto.comp
        (poissonLaplaceExponent_invSucc_tendstoZero ν hInt)
    have hLaplaceScaled :
        ∀ n,
          ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂(P : Measure Ω) =
            ennrealExpNeg (scaledExponent n) := by
      intro n
      -- Proof comment: apply the linear-kernel Laplace theorem at scale `s_n = (n + 1)⁻¹`.
      have hlintegral :
          (fun ω ↦ ∫⁻ x, scaledId n x ∂ X ω) =
            (fun ω ↦ ENNReal.ofReal (invSuccScaleReal n) * Y ω) := by
        funext ω
        simpa [scaledId, Y, poissonPointIntegral_def] using
          (lintegral_const_mul' (μ := X ω) (ENNReal.ofReal (invSuccScaleReal n))
            (fun x : NNReal ↦ (x : ℝ≥0∞)) (by simp))
      have hraw :
          ∫ ω, ennrealExpNeg (∫⁻ x, scaledId n x ∂ X ω) ∂(P : Measure Ω) =
            ennrealExpNeg (scaledExponent n) := by
        simpa [scaledExponent] using
          nnrealLinearLaplaceTransformOfIsPoissonPointProcessAux
            P ν X hPPP (invSuccScaleReal n) (hs_nonneg n)
      have hleftRewrite :
          (fun ω ↦ ennrealExpNeg (∫⁻ x, scaledId n x ∂ X ω)) =
            (fun ω ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω)) := by
        funext ω
        simpa using congrArg ennrealExpNeg (congrArg (fun f ↦ f ω) hlintegral)
      simpa [hleftRewrite] using hraw
    have hLeftOne :
        Filter.Tendsto
          (fun n : ℕ ↦ ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂
            (P : Measure Ω))
          Filter.atTop (nhds 1) := by
      simpa [hLaplaceScaled] using hRight
    have hToRealOne : ((P : Measure Ω) A).toReal = 1 :=
      tendsto_nhds_unique hLeft hLeftOne
    exact (ENNReal.toReal_eq_one_iff ((P : Measure Ω) A)).mp hToRealOne
  tfae_finish

/-- Helper for Example 24.19: once the one-dimensional Poisson integral is almost surely finite,
its real-valued Laplace transform has the standard exponential form. -/
theorem poissonPointIntegral_laplaceFormula
    {P : ProbabilityMeasure Ω} {ν : Measure NNReal} {X : Ω → Measure NNReal}
    (hX : IsPoissonPointProcessOnNNReal ν P X)
    (hfinite : (P : Measure Ω) {ω | poissonPointIntegral X ω < ∞} = 1) :
    ∀ t : NNReal,
      ∫ ω,
          Real.exp (-((t : ℝ) * (poissonPointIntegral X ω).toReal))
        ∂(P : Measure Ω) =
        Real.exp (∫ x : NNReal, (Real.exp (-((t : ℝ) * (x : ℝ))) - 1) ∂ν) :=
by
  intro t
  let Y : Ω → ℝ≥0∞ := poissonPointIntegral X
  let scaledId : NonnegativeMeasurableFunction NNReal :=
    ⟨fun x ↦ ENNReal.ofReal (t : ℝ) * x,
      measurable_const.mul measurable_coe_nnreal_ennreal⟩
  let scaledExponent : ℝ≥0∞ := ∫⁻ x,
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (scaledId x)) ∂ν
  have hPPP : ProbabilityTheory.IsPoissonPointProcess ν P X := by
    simpa [IsPoissonPointProcessOnNNReal] using hX
  have hInt :
      Integrable (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ)) ν :=
    ((poissonPointIntegral_finite_tfae hX).out 1 2).mp hfinite
  have hY_meas : Measurable Y := by
    -- Proof comment: the Poisson integral is measurable because the random-measure map is.
    simpa [Y, poissonPointIntegral_def] using
      (Measure.measurable_lintegral measurable_coe_nnreal_ennreal).comp hPPP.1.measurable
  have hA_meas : MeasurableSet {ω | Y ω < ∞} := measurableSet_lt hY_meas measurable_const
  have hAeFinite : ∀ᵐ ω ∂(P : Measure Ω), Y ω < ∞ :=
    (mem_ae_iff_prob_eq_one hA_meas).2 hfinite
  have hs_nonneg : 0 ≤ (t : ℝ) := t.2
  have hkernel_meas :
      AEStronglyMeasurable (fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ν := by
    have hmeas : Measurable (fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ)))) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hkernel_nonneg :
      0 ≤ᵐ[ν] fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ))) := by
    filter_upwards with x
    have hle : Real.exp (-((t : ℝ) * (x : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [t.2, x.2]
    exact sub_nonneg.mpr hle
  have hkernel_int :
      Integrable (fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ν := by
    have hdom :
        Integrable (fun x : NNReal ↦ max 1 (t : ℝ) * min (1 : ℝ) (x : ℝ)) ν :=
      hInt.const_mul (max 1 (t : ℝ))
    refine Integrable.mono' hdom hkernel_meas ?_
    filter_upwards with x
    have hnonneg : 0 ≤ 1 - Real.exp (-((t : ℝ) * (x : ℝ))) := by
      have hle : Real.exp (-((t : ℝ) * (x : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        nlinarith [t.2, x.2]
      exact sub_nonneg.mpr hle
    have hle :
        1 - Real.exp (-((t : ℝ) * (x : ℝ))) ≤
          max 1 (t : ℝ) * min (1 : ℝ) (x : ℝ) :=
      poissonExpKernel_scale_le_max_mul_minOne (t : ℝ) hs_nonneg x
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hscaledExponent_eq :
      scaledExponent =
        ENNReal.ofReal (∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν) := by
    calc
      scaledExponent
          = ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν := by
              refine lintegral_congr_ae ?_
              filter_upwards with x
              simpa [scaledExponent, scaledId, ENNReal.ofReal_mul, hs_nonneg] using
                poissonLaplaceKernel_scale_eq_ofReal (t : ℝ) hs_nonneg x
      _ = ENNReal.ofReal (∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hkernel_int hkernel_nonneg
  have hraw :
      ∫ ω, ennrealExpNeg (∫⁻ x, scaledId x ∂ X ω) ∂(P : Measure Ω) =
        ennrealExpNeg scaledExponent := by
    -- Proof comment: this is the linear-kernel specialization of the executable Laplace bridge.
    simpa [scaledExponent, scaledId] using
      nnrealLinearLaplaceTransformOfIsPoissonPointProcessAux P ν X hPPP (t : ℝ) t.2
  have hlintegral :
      (fun ω ↦ ∫⁻ x, scaledId x ∂ X ω) =
        fun ω ↦ ENNReal.ofReal (t : ℝ) * Y ω := by
    funext ω
    simpa [scaledId, Y, poissonPointIntegral_def] using
      (lintegral_const_mul' (μ := X ω) (ENNReal.ofReal (t : ℝ))
        (fun x : NNReal ↦ (x : ℝ≥0∞)) (by simp))
  have hleft_ae :
      (fun ω ↦ ennrealExpNeg (ENNReal.ofReal (t : ℝ) * Y ω)) =ᵐ[(P : Measure Ω)]
        (fun ω ↦ Real.exp (-((t : ℝ) * (Y ω).toReal))) := by
    filter_upwards [hAeFinite] with ω hω
    have hω_ne_top : Y ω ≠ ∞ := lt_top_iff_ne_top.mp hω
    have hmul_ne_top : ENNReal.ofReal (t : ℝ) * Y ω ≠ ∞ :=
      ENNReal.mul_ne_top (by simp [t.2]) hω_ne_top
    rw [ennrealExpNeg, if_neg hmul_ne_top, ENNReal.toReal_mul]
    simpa using
      congrArg (fun r : ℝ ↦ Real.exp (-(r * (Y ω).toReal))) (ENNReal.toReal_ofReal t.2)
  have hcentered :
      Integrable (fun x : NNReal ↦ Real.exp (-((t : ℝ) * (x : ℝ))) - 1) ν := by
    have hneg : Integrable (fun x : NNReal ↦ -(1 - Real.exp (-((t : ℝ) * (x : ℝ))))) ν :=
      hkernel_int.neg
    convert hneg using 1
    funext x
    ring
  calc
    ∫ ω, Real.exp (-((t : ℝ) * (poissonPointIntegral X ω).toReal)) ∂(P : Measure Ω)
        = ∫ ω, ennrealExpNeg (ENNReal.ofReal (t : ℝ) * Y ω) ∂(P : Measure Ω) := by
            symm
            exact integral_congr_ae hleft_ae
    _ = ∫ ω, ennrealExpNeg (∫⁻ x, scaledId x ∂ X ω) ∂(P : Measure Ω) := by
          congr 1
          funext ω
          symm
          exact congrArg ennrealExpNeg (congrArg (fun f ↦ f ω) hlintegral)
    _ = ennrealExpNeg scaledExponent := hraw
    _ = Real.exp (∫ x : NNReal, (Real.exp (-((t : ℝ) * (x : ℝ))) - 1) ∂ν) := by
          rw [hscaledExponent_eq, ennrealExpNeg]
          have hIntegral_nonneg :
              0 ≤ ∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν :=
            integral_nonneg_of_ae hkernel_nonneg
          have hrewrite :
              -(∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν) =
                ∫ x : NNReal, (Real.exp (-((t : ℝ) * (x : ℝ))) - 1) ∂ν := by
            calc
              -(∫ x : NNReal, (1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν)
                  = ∫ x : NNReal, -(1 - Real.exp (-((t : ℝ) * (x : ℝ)))) ∂ν := by
                      simpa using
                        (integral_neg
                          (f := fun x : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (x : ℝ)))) (μ := ν)).symm
              _ = ∫ x : NNReal, (Real.exp (-((t : ℝ) * (x : ℝ))) - 1) ∂ν := by
                    refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
                    ring
          rw [if_neg ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hIntegral_nonneg, hrewrite]

/-- Helper for Example 24.19: the Poisson Laplace transform on `NNReal` for the linear test
function `x ↦ u * x`. -/
theorem nnrealLinearLaplaceTransformOfIsPoissonPointProcess
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess ν P X) (u : ℝ) (hu : 0 ≤ u) :
    ∫ ω, ennrealExpNeg (∫⁻ x, ENNReal.ofReal u * x ∂ X ω) ∂(P : Measure Ω) =
      ennrealExpNeg
        (∫⁻ x, (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (ENNReal.ofReal u * x)) ∂ν) :=
by
  -- Proof comment: expose the earlier linear-kernel owner under the public theorem name.
  exact nnrealLinearLaplaceTransformOfIsPoissonPointProcessAux P ν X hX u hu

/-- Helper for Example 24.19: the strip integral is finite with positive probability iff it is
finite almost surely iff the scaled Lévy measure satisfies the textbook integrability condition. -/
theorem stripPoissonIntegral_finite_tfae
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    {s t : NNReal} (hst : s ≤ t) :
    List.TFAE
      [ 0 < (P : Measure Ω)
            {ω | (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) < ∞}
      , (P : Measure Ω)
          {ω | (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) < ∞} = 1
      , Integrable
          (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ))
          ((((t - s : NNReal) : ENNReal) • ν))
      ] := by
  let Y : Ω → ℝ≥0∞ := fun ω ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω
  let A : Set Ω := {ω | Y ω < ∞}
  let laplaceEvent : Ω → ℝ :=
    Set.indicator A fun ω ↦ Real.exp (-(Y ω).toReal)
  let idNNReal : NonnegativeMeasurableFunction NNReal :=
    ⟨fun x ↦ (x : ℝ≥0∞), measurable_coe_nnreal_ennreal⟩
  let exponent : ℝ≥0∞ :=
    ∫⁻ x,
      (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg ((idNNReal x : ℝ≥0∞)))
      ∂ ((((t - s : NNReal) : ENNReal) • ν))
  have hPPP :
      ProbabilityTheory.IsPoissonPointProcess
        ((((t - s : NNReal) : ENNReal) • ν)) P (stripFirstCoordinate X s t) := by
    -- Proof comment: the strip-image process already carries the exact PPP data for the scaled
    -- one-dimensional intensity.
    simpa [ProbabilityTheory.IsPoissonPointProcess] using
      (stripFirstCoordinate_hasPoissonPointProcessData P ν X hX hst)
  have hY_meas : Measurable Y := by
    -- Proof comment: the strip integral is measurable because the strip random measure is.
    simpa [Y] using
      (Measure.measurable_lintegral measurable_coe_nnreal_ennreal).comp
        (stripFirstCoordinate_measurable X hX.1.measurable s t)
  have hA_meas : MeasurableSet A := measurableSet_lt hY_meas measurable_const
  have hlaplaceEvent_eq :
      (fun ω ↦ ennrealExpNeg (Y ω)) = laplaceEvent := by
    funext ω
    by_cases hω : Y ω = ∞
    · have hω' : ω ∉ A := by simpa [A, Y] using hω
      simp [laplaceEvent, A, hω, hω', ennrealExpNeg_top]
    · have hω' : ω ∈ A := by
        simpa [A, Y, lt_top_iff_ne_top] using hω
      simp [laplaceEvent, A, hω', ennrealExpNeg, hω]
  have hlaplaceEvent_nonneg : ∀ ω, 0 ≤ laplaceEvent ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp [laplaceEvent, hω, Real.exp_pos]
      exact le_of_lt (Real.exp_pos _)
    · simp [laplaceEvent, hω]
  have hlaplaceEvent_meas : AEStronglyMeasurable laplaceEvent (P : Measure Ω) := by
    have hcore : Measurable (fun ω ↦ Real.exp (-(Y ω).toReal)) := by
      have htoReal : Measurable (fun ω ↦ (Y ω).toReal) :=
        ENNReal.measurable_toReal.comp hY_meas
      fun_prop
    exact (hcore.stronglyMeasurable.indicator hA_meas).aestronglyMeasurable
  have hlaplaceEvent_integrable : Integrable laplaceEvent (P : Measure Ω) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hlaplaceEvent_meas ?_
    filter_upwards with ω
    by_cases hω : ω ∈ A
    · have hle : Real.exp (-(Y ω).toReal) ≤ 1 := by
        have htoReal_nonneg : 0 ≤ (Y ω).toReal := ENNReal.toReal_nonneg
        exact Real.exp_le_one_iff.mpr (by linarith)
      simp [laplaceEvent, hω, abs_of_nonneg (hlaplaceEvent_nonneg ω), hle]
    · simp [laplaceEvent, hω]
  have hsupport :
      Function.support laplaceEvent = A := by
    ext ω
    by_cases hω : ω ∈ A
    · simp [laplaceEvent, hω, Real.exp_pos]
    · simp [laplaceEvent, hω]
  have hleft_pos :
      0 < ∫ ω, ennrealExpNeg (Y ω) ∂(P : Measure Ω) ↔ 0 < (P : Measure Ω) A := by
    rw [hlaplaceEvent_eq, MeasureTheory.integral_pos_iff_support_of_nonneg
      hlaplaceEvent_nonneg hlaplaceEvent_integrable, hsupport]
  have hLaplaceOne :
      ∫ ω, ennrealExpNeg (Y ω) ∂(P : Measure Ω) = ennrealExpNeg exponent := by
    -- Proof comment: specialize the PPP Laplace transform to the identity test function on the
    -- strip image.
    simpa [Y, exponent, idNNReal] using
      nnrealLinearLaplaceTransformOfIsPoissonPointProcess
        P ((((t - s : NNReal) : ENNReal) • ν)) (stripFirstCoordinate X s t) hPPP 1
        (by positivity)
  have hexponent_eq :
      exponent =
        ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(x : ℝ))) ∂ ((((t - s : NNReal) : ENNReal) • ν)) := by
    -- Proof comment: on finite `NNReal` points, the Poisson exponent kernel is exactly the
    -- `ENNReal` lift of `x ↦ 1 - exp (-x)`.
    refine lintegral_congr_ae ?_
    filter_upwards with x
    simpa [exponent, idNNReal] using poissonLaplaceKernel_eq_ofReal x
  have hkernel_nonneg :
      0 ≤ᵐ[((((t - s : NNReal) : ENNReal) • ν))]
        fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ)) :=
    Filter.Eventually.of_forall fun x ↦
      sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by simpa using x.2))
  have hkernel_meas :
      AEStronglyMeasurable
        (fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ)))
        ((((t - s : NNReal) : ENNReal) • ν)) := by
    have hmeas : Measurable (fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ))) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hright_pos :
      0 < ennrealExpNeg exponent ↔
        Integrable
          (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ))
          ((((t - s : NNReal) : ENNReal) • ν)) := by
    have hexponent_finite :
        exponent ≠ ∞ ↔
          Integrable
            (fun x : NNReal ↦ 1 - Real.exp (-(x : ℝ)))
            ((((t - s : NNReal) : ENNReal) • ν)) := by
      rw [hexponent_eq]
      exact MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hkernel_meas hkernel_nonneg
    have hExpPos : 0 < ennrealExpNeg exponent ↔ exponent ≠ ∞ := by
      by_cases htop : exponent = ∞
      · simp [ennrealExpNeg, htop]
      · simp [ennrealExpNeg, htop, Real.exp_pos]
    exact hExpPos.trans <| hexponent_finite.trans <|
      poissonLaplaceKernel_integrable_iff ((((t - s : NNReal) : ENNReal) • ν))
  tfae_have 1 → 3 := by
    -- Proof comment: positive finiteness probability makes the identity Laplace expectation
    -- positive, so the Lévy truncation kernel is integrable.
    intro hPos
    exact hright_pos.mp <| by
      rw [← hLaplaceOne]
      exact hleft_pos.mpr hPos
  tfae_have 2 → 1 := by
    intro hAlmostSure
    rw [hAlmostSure]
    positivity
  tfae_have 3 → 1 := by
    -- Proof comment: run the same Laplace identity in reverse.
    intro hInt
    exact hleft_pos.mp <| by
      rw [hLaplaceOne]
      exact hright_pos.mpr hInt
  tfae_have 3 → 2 := by
    intro hInt
    let scaledId : ℕ → NonnegativeMeasurableFunction NNReal := fun n ↦
      ⟨fun x ↦ ENNReal.ofReal (invSuccScaleReal n) * x,
        measurable_const.mul measurable_coe_nnreal_ennreal⟩
    let scaledExponent : ℕ → ℝ≥0∞ := fun n ↦
      ∫⁻ x,
        (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (scaledId n x))
        ∂ ((((t - s : NNReal) : ENNReal) • ν))
    have hs_nonneg : ∀ n, 0 ≤ invSuccScaleReal n := by
      intro n
      have hn : 0 ≤ (n : ℝ) + 1 := by
        positivity
      simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
    have hs_le_one : ∀ n, invSuccScaleReal n ≤ 1 := by
      intro n
      have hn : (0 : ℝ) ≤ n := by
        exact_mod_cast Nat.zero_le n
      have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        linarith
      simpa [invSuccScaleReal] using inv_le_one_of_one_le₀ hn'
    have hkernel_meas :
        ∀ n, AEStronglyMeasurable
          (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))))
          ((((t - s : NNReal) : ENNReal) • ν)) := by
      intro n
      have hmeas :
          Measurable (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ)))) := by
        fun_prop
      exact hmeas.aestronglyMeasurable
    have hkernel_nonneg :
        ∀ n,
          0 ≤ᵐ[((((t - s : NNReal) : ENNReal) • ν))]
            fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) := by
      intro n
      filter_upwards with x
      have harg_nonneg : 0 ≤ invSuccScaleReal n * (x : ℝ) := by
        nlinarith [hs_nonneg n, x.2]
      have hle : Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        linarith
      exact sub_nonneg.mpr hle
    have hkernel_int :
        ∀ n,
          Integrable
            (fun x : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))))
            ((((t - s : NNReal) : ENNReal) • ν)) := by
      intro n
      -- Proof comment: each scaled Laplace kernel is dominated by the textbook truncation
      -- kernel on the scaled intensity.
      refine Integrable.mono' hInt (hkernel_meas n) ?_
      filter_upwards with x
      have hnonneg : 0 ≤ 1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) := by
        have harg_nonneg : 0 ≤ invSuccScaleReal n * (x : ℝ) := by
          nlinarith [hs_nonneg n, x.2]
        have hle : Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ 1 := by
          refine Real.exp_le_one_iff.mpr ?_
          linarith
        exact sub_nonneg.mpr hle
      have hle :
          1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))) ≤ min (1 : ℝ) (x : ℝ) :=
        poissonExpKernel_scale_le_minOne (invSuccScaleReal n) (hs_le_one n) x
      simpa [Real.norm_of_nonneg hnonneg] using hle
    have hscaledExponent_eq :
        ∀ n,
          scaledExponent n =
            ENNReal.ofReal
              (∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))))
                ∂ ((((t - s : NNReal) : ENNReal) • ν))) := by
      intro n
      calc
        scaledExponent n
            = ∫⁻ x, ENNReal.ofReal (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))))
                ∂ ((((t - s : NNReal) : ENNReal) • ν)) := by
                  refine lintegral_congr_ae ?_
                  filter_upwards with x
                  -- Proof comment: rewrite the scaled extended-real kernel back to the ordinary
                  -- real Laplace kernel.
                  simpa [scaledExponent, scaledId, ENNReal.ofReal_mul, hs_nonneg n] using
                    poissonLaplaceKernel_scale_eq_ofReal (invSuccScaleReal n) (hs_nonneg n) x
        _ = ENNReal.ofReal
              (∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))))
                ∂ ((((t - s : NNReal) : ENNReal) • ν))) := by
              symm
              exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                (hkernel_int n) (hkernel_nonneg n)
    have hLeft :
        Filter.Tendsto
          (fun n : ℕ ↦
            ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂(P : Measure Ω))
          Filter.atTop (nhds ((P : Measure Ω) A).toReal) :=
      poissonPointIntegralLaplace_invSucc_tendsto_measureFinite (μ := (P : Measure Ω)) hY_meas
    have hRight :
        Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (scaledExponent n)) Filter.atTop (nhds 1) := by
      have hrewrite :
          (fun n : ℕ ↦ ennrealExpNeg (scaledExponent n)) =
            (fun n : ℕ ↦
              Real.exp
                (-(∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))))
                    ∂ ((((t - s : NNReal) : ENNReal) • ν))))) := by
        funext n
        have hIntegral_nonneg :
            0 ≤
              ∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))))
                ∂ ((((t - s : NNReal) : ENNReal) • ν)) :=
          integral_nonneg_of_ae (hkernel_nonneg n)
        have hscaled_ne_top : scaledExponent n ≠ ∞ := by
          rw [hscaledExponent_eq n]
          simpa [integral_smul_measure, ENNReal.ofReal_mul] using
            (show
              ENNReal.ofReal
                  (∫ x : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (x : ℝ))))
                    ∂ ((((t - s : NNReal) : ENNReal) • ν))) ≠ ∞
              from ENNReal.ofReal_ne_top)
        rw [ennrealExpNeg, if_neg hscaled_ne_top, hscaledExponent_eq n,
          ENNReal.toReal_ofReal hIntegral_nonneg]
      rw [hrewrite]
      have hcont : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
        Real.continuous_exp.comp continuous_neg
      -- Proof comment: dominated convergence collapses the exponent to `0`, so the Laplace side
      -- tends to `exp 0 = 1`.
      simpa using hcont.continuousAt.tendsto.comp
        (poissonLaplaceExponent_invSucc_tendstoZero ((((t - s : NNReal) : ENNReal) • ν)) hInt)
    have hLaplaceScaled :
        ∀ n,
          ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂(P : Measure Ω) =
            ennrealExpNeg (scaledExponent n) := by
      intro n
      -- Proof comment: specialize the PPP Laplace transform to the scaled identity test function.
      have hlintegral :
          (fun ω ↦ ∫⁻ x, scaledId n x ∂ stripFirstCoordinate X s t ω) =
            (fun ω ↦ ENNReal.ofReal (invSuccScaleReal n) * Y ω) := by
        funext ω
        simpa [scaledId, Y] using
          (lintegral_const_mul' (μ := stripFirstCoordinate X s t ω)
            (ENNReal.ofReal (invSuccScaleReal n))
            (fun x : NNReal ↦ (x : ℝ≥0∞)) (by simp))
      have hraw :
          ∫ ω, ennrealExpNeg (∫⁻ x, scaledId n x ∂ stripFirstCoordinate X s t ω) ∂
              (P : Measure Ω) =
            ennrealExpNeg (scaledExponent n) := by
        simpa [scaledExponent] using
          nnrealLinearLaplaceTransformOfIsPoissonPointProcess
            P ((((t - s : NNReal) : ENNReal) • ν))
            (stripFirstCoordinate X s t) hPPP (invSuccScaleReal n) (hs_nonneg n)
      have hleftRewrite :
          (fun ω ↦ ennrealExpNeg (∫⁻ x, scaledId n x ∂ stripFirstCoordinate X s t ω)) =
            (fun ω ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω)) := by
        funext ω
        simpa using congrArg ennrealExpNeg (congrArg (fun f ↦ f ω) hlintegral)
      simpa [hleftRewrite] using hraw
    have hLeftOne :
        Filter.Tendsto
          (fun n : ℕ ↦
            ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂(P : Measure Ω))
          Filter.atTop (nhds 1) := by
      simpa [hLaplaceScaled] using hRight
    have hToRealOne : ((P : Measure Ω) A).toReal = 1 :=
      tendsto_nhds_unique hLeft hLeftOne
    exact (ENNReal.toReal_eq_one_iff ((P : Measure Ω) A)).mp hToRealOne
  tfae_finish

/-- Helper for Example 24.19: the strip integral over `(s, t]` satisfies the same Laplace
transform formula as the one-dimensional Poisson integral with scaled intensity
`((t - s) • ν)`. -/
theorem stripPoissonIntegral_laplaceFormula
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    {s t : NNReal} (hst : s ≤ t)
    (hfinite :
      (P : Measure Ω)
        {ω | (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) < ∞} = 1) :
    ∀ u : NNReal,
      ∫ ω,
          Real.exp
            (-((u : ℝ) * (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω).toReal))
        ∂(P : Measure Ω) =
        Real.exp
          (∫ x : NNReal, (Real.exp (-((u : ℝ) * (x : ℝ))) - 1)
            ∂ ((((t - s : NNReal) : ENNReal) • ν))) := by
  intro u
  let Y : Ω → ℝ≥0∞ := fun ω ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω
  let scaledId : NonnegativeMeasurableFunction NNReal :=
    ⟨fun x ↦ ENNReal.ofReal (u : ℝ) * x,
      measurable_const.mul measurable_coe_nnreal_ennreal⟩
  let scaledExponent : ℝ≥0∞ := ∫⁻ x,
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (scaledId x))
      ∂ ((((t - s : NNReal) : ENNReal) • ν))
  have hPPP :
      ProbabilityTheory.IsPoissonPointProcess
        ((((t - s : NNReal) : ENNReal) • ν)) P (stripFirstCoordinate X s t) := by
    -- Proof comment: the strip image already carries the one-dimensional PPP owner with scaled
    -- intensity.
    simpa [ProbabilityTheory.IsPoissonPointProcess] using
      (stripFirstCoordinate_hasPoissonPointProcessData P ν X hX hst)
  have hInt :
      Integrable
        (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ))
        ((((t - s : NNReal) : ENNReal) • ν)) :=
    ((stripPoissonIntegral_finite_tfae P ν X hX hst).out 1 2).mp hfinite
  have hY_meas : Measurable Y := by
    -- Proof comment: the strip integral is measurable because the strip random measure is.
    simpa [Y] using
      (Measure.measurable_lintegral measurable_coe_nnreal_ennreal).comp
        (stripFirstCoordinate_measurable X hX.1.measurable s t)
  have hA_meas : MeasurableSet {ω | Y ω < ∞} := measurableSet_lt hY_meas measurable_const
  have hAeFinite : ∀ᵐ ω ∂(P : Measure Ω), Y ω < ∞ :=
    (mem_ae_iff_prob_eq_one hA_meas).2 hfinite
  have hs_nonneg : 0 ≤ (u : ℝ) := u.2
  have hkernel_meas :
      AEStronglyMeasurable
        (fun x : NNReal ↦ 1 - Real.exp (-((u : ℝ) * (x : ℝ))))
        ((((t - s : NNReal) : ENNReal) • ν)) := by
    have hmeas : Measurable (fun x : NNReal ↦ 1 - Real.exp (-((u : ℝ) * (x : ℝ)))) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hkernel_nonneg :
      0 ≤ᵐ[((((t - s : NNReal) : ENNReal) • ν))]
        fun x : NNReal ↦ 1 - Real.exp (-((u : ℝ) * (x : ℝ))) := by
    filter_upwards with x
    have hle : Real.exp (-((u : ℝ) * (x : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [u.2, x.2]
    exact sub_nonneg.mpr hle
  have hkernel_int :
      Integrable
        (fun x : NNReal ↦ 1 - Real.exp (-((u : ℝ) * (x : ℝ))))
        ((((t - s : NNReal) : ENNReal) • ν)) := by
    have hdom :
        Integrable
          (fun x : NNReal ↦ max 1 (u : ℝ) * min (1 : ℝ) (x : ℝ))
          ((((t - s : NNReal) : ENNReal) • ν)) :=
      hInt.const_mul (max 1 (u : ℝ))
    refine Integrable.mono' hdom hkernel_meas ?_
    filter_upwards with x
    have hnonneg : 0 ≤ 1 - Real.exp (-((u : ℝ) * (x : ℝ))) := by
      have hle : Real.exp (-((u : ℝ) * (x : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        nlinarith [u.2, x.2]
      exact sub_nonneg.mpr hle
    have hle :
        1 - Real.exp (-((u : ℝ) * (x : ℝ))) ≤
          max 1 (u : ℝ) * min (1 : ℝ) (x : ℝ) :=
      poissonExpKernel_scale_le_max_mul_minOne (u : ℝ) hs_nonneg x
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hscaledExponent_eq :
      scaledExponent =
        ENNReal.ofReal
          (∫ x : NNReal, (1 - Real.exp (-((u : ℝ) * (x : ℝ))))
            ∂ ((((t - s : NNReal) : ENNReal) • ν))) := by
    calc
      scaledExponent
          = ∫⁻ x,
              ENNReal.ofReal (1 - Real.exp (-((u : ℝ) * (x : ℝ))))
              ∂ ((((t - s : NNReal) : ENNReal) • ν)) := by
                refine lintegral_congr_ae ?_
                filter_upwards with x
                -- Proof comment: rewrite the scaled extended-real kernel back to the ordinary
                -- real Laplace kernel.
                simpa [scaledExponent, scaledId, ENNReal.ofReal_mul, hs_nonneg] using
                  poissonLaplaceKernel_scale_eq_ofReal (u : ℝ) hs_nonneg x
      _ = ENNReal.ofReal
            (∫ x : NNReal, (1 - Real.exp (-((u : ℝ) * (x : ℝ))))
              ∂ ((((t - s : NNReal) : ENNReal) • ν))) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hkernel_int hkernel_nonneg
  have hscaledExponent_eq' :
      scaledExponent =
        ENNReal.ofReal
          ((((t - s : NNReal) : ℝ) *
            ∫ x : NNReal, (1 - Real.exp (-((u : ℝ) * (x : ℝ)))) ∂ν)) := by
    rw [hscaledExponent_eq]
    simp [integral_smul_measure, ENNReal.ofReal_mul]
  have hraw :
      ∫ ω, ennrealExpNeg (∫⁻ x, scaledId x ∂ stripFirstCoordinate X s t ω) ∂(P : Measure Ω) =
        ennrealExpNeg scaledExponent := by
    -- Proof comment: this is Theorem 24.14 specialized to the scaled identity test function on
    -- the strip image.
    simpa [scaledExponent, scaledId] using
      nnrealLinearLaplaceTransformOfIsPoissonPointProcess
        P ((((t - s : NNReal) : ENNReal) • ν)) (stripFirstCoordinate X s t) hPPP (u : ℝ) u.2
  have hlintegral :
      (fun ω ↦ ∫⁻ x, scaledId x ∂ stripFirstCoordinate X s t ω) =
        fun ω ↦ ENNReal.ofReal (u : ℝ) * Y ω := by
    funext ω
    simpa [scaledId, Y] using
      (lintegral_const_mul' (μ := stripFirstCoordinate X s t ω) (ENNReal.ofReal (u : ℝ))
        (fun x : NNReal ↦ (x : ℝ≥0∞)) (by simp))
  have hleft_ae :
      (fun ω ↦ ennrealExpNeg (ENNReal.ofReal (u : ℝ) * Y ω)) =ᵐ[(P : Measure Ω)]
        (fun ω ↦ Real.exp (-((u : ℝ) * (Y ω).toReal))) := by
    filter_upwards [hAeFinite] with ω hω
    have hω_ne_top : Y ω ≠ ∞ := lt_top_iff_ne_top.mp hω
    have hmul_ne_top : ENNReal.ofReal (u : ℝ) * Y ω ≠ ∞ :=
      ENNReal.mul_ne_top (by simp [u.2]) hω_ne_top
    rw [ennrealExpNeg, if_neg hmul_ne_top, ENNReal.toReal_mul]
    simpa using
      congrArg (fun r : ℝ ↦ Real.exp (-(r * (Y ω).toReal)))
        (ENNReal.toReal_ofReal u.2)
  have hcentered :
      Integrable
        (fun x : NNReal ↦ Real.exp (-((u : ℝ) * (x : ℝ))) - 1)
        ((((t - s : NNReal) : ENNReal) • ν)) := by
    have hneg :
        Integrable
          (fun x : NNReal ↦ -(1 - Real.exp (-((u : ℝ) * (x : ℝ)))))
          ((((t - s : NNReal) : ENNReal) • ν)) :=
      hkernel_int.neg
    convert hneg using 1
    funext x
    ring
  have hkernel_nonneg_base :
      0 ≤ᵐ[ν] fun x : NNReal ↦ 1 - Real.exp (-((u : ℝ) * (x : ℝ))) := by
    filter_upwards with x
    have hle : Real.exp (-((u : ℝ) * (x : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [u.2, x.2]
    exact sub_nonneg.mpr hle
  have hIntegral_nonneg_base :
      0 ≤ ∫ x : NNReal, (1 - Real.exp (-((u : ℝ) * (x : ℝ)))) ∂ν :=
    integral_nonneg_of_ae hkernel_nonneg_base
  have hscaledIntegral_nonneg :
      0 ≤
        (((t - s : NNReal) : ℝ) *
          ∫ x : NNReal, (1 - Real.exp (-((u : ℝ) * (x : ℝ)))) ∂ν) := by
    exact mul_nonneg (by exact_mod_cast (show (0 : NNReal) ≤ t - s from bot_le))
      hIntegral_nonneg_base
  calc
    ∫ ω,
        Real.exp (-((u : ℝ) * (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω).toReal))
      ∂(P : Measure Ω)
        = ∫ ω, ennrealExpNeg (ENNReal.ofReal (u : ℝ) * Y ω) ∂(P : Measure Ω) := by
            -- Proof comment: on the almost-sure finite event, the extended-real Laplace kernel
            -- is exactly the ordinary exponential.
            symm
            exact integral_congr_ae hleft_ae
    _ = ∫ ω, ennrealExpNeg (∫⁻ x, scaledId x ∂ stripFirstCoordinate X s t ω) ∂(P : Measure Ω) := by
          congr 1
          funext ω
          symm
          exact congrArg ennrealExpNeg (congrArg (fun f ↦ f ω) hlintegral)
    _ = ennrealExpNeg scaledExponent := hraw
    _ = Real.exp
          ((((t - s : NNReal) : ℝ) *
            ∫ x : NNReal, (Real.exp (-((u : ℝ) * (x : ℝ))) - 1) ∂ν)) := by
          rw [hscaledExponent_eq', ennrealExpNeg, if_neg ENNReal.ofReal_ne_top,
            ENNReal.toReal_ofReal hscaledIntegral_nonneg]
          rw [show
              -((((t - s : NNReal) : ℝ) *
                  ∫ x : NNReal, (1 - Real.exp (-((u : ℝ) * (x : ℝ)))) ∂ν)) =
                (((t - s : NNReal) : ℝ) *
                  ∫ x : NNReal, (Real.exp (-((u : ℝ) * (x : ℝ))) - 1) ∂ν) by
                calc
                  -((((t - s : NNReal) : ℝ) *
                      ∫ x : NNReal, (1 - Real.exp (-((u : ℝ) * (x : ℝ)))) ∂ν))
                      = (((t - s : NNReal) : ℝ) *
                          (-(∫ x : NNReal, (1 - Real.exp (-((u : ℝ) * (x : ℝ)))) ∂ν))) := by
                            ring
                  _ = (((t - s : NNReal) : ℝ) *
                        ∫ x : NNReal, -(1 - Real.exp (-((u : ℝ) * (x : ℝ)))) ∂ν) := by
                          rw [integral_neg]
                  _ = (((t - s : NNReal) : ℝ) *
                        ∫ x : NNReal, (Real.exp (-((u : ℝ) * (x : ℝ))) - 1) ∂ν) := by
                          congr 1
                          refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
                          ring]
    _ = Real.exp
          (∫ x : NNReal, (Real.exp (-((u : ℝ) * (x : ℝ))) - 1)
            ∂ ((((t - s : NNReal) : ENNReal) • ν))) := by
          congr 1
          calc
            (((t - s : NNReal) : ℝ) *
                ∫ x : NNReal, (Real.exp (-((u : ℝ) * (x : ℝ))) - 1) ∂ν)
                = ((((t - s : NNReal) : ENNReal).toReal) •
                    ∫ x : NNReal, (Real.exp (-((u : ℝ) * (x : ℝ))) - 1) ∂ν) := by
                      rw [smul_eq_mul]
                      congr 1
            _ = ∫ x : NNReal, (Real.exp (-((u : ℝ) * (x : ℝ))) - 1)
                  ∂ ((((t - s : NNReal) : ENNReal) • ν)) := by
                    symm
                    exact integral_smul_measure
                      (c := ((t - s : NNReal) : ENNReal))
                      (f := fun x : NNReal ↦ Real.exp (-((u : ℝ) * (x : ℝ))) - 1)
                      (μ := ν)

/-- Helper for Example 24.19: the strip integral is almost surely finite because the scaled Lévy
measure inherits the textbook truncated first-moment condition from `ν`. -/
theorem stripPoissonIntegral_ae_lt_top
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal)
    (hν : HasSubordinatorLevyKhinchinRepresentation μ α ν)
    (P : ProbabilityMeasure Ω) (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) {s t : NNReal} (hst : s ≤ t) :
    ∀ᵐ ω ∂(P : Measure Ω),
      (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) < ∞ := by
  have hscaled :
      Integrable
        (fun x : NNReal ↦ min (1 : ℝ) (x : ℝ))
        ((((t - s : NNReal) : ENNReal) • ν)) := by
    exact hν.2.1.smul_measure (by simp)
  have hmeas :
      MeasurableSet {ω | (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) < ∞} := by
    have hY_meas :
        Measurable (fun ω ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) := by
      simpa using
        (Measure.measurable_lintegral measurable_coe_nnreal_ennreal).comp
          (stripFirstCoordinate_measurable X hX.1.measurable s t)
    exact measurableSet_lt hY_meas measurable_const
  have hfinite :
      (P : Measure Ω) {ω | (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) < ∞} = 1 :=
    ((stripPoissonIntegral_finite_tfae P ν X hX hst).out 2 1).mp hscaled
  -- Proof comment: convert the probability-one statement into the corresponding almost-sure event.
  exact (mem_ae_iff_prob_eq_one hmeas).2 hfinite

-- Semantic recall note: `lean_leansearch` did not surface a ready-made subordinator PPP owner, so
-- this file uses the chapter's Definition 24.10 Poisson point-process owner together with the
-- existing Chapter 16 subordinator Lévy--Khinchin owner.
/-- Under the source Poisson point-process hypothesis, each time increment of the Poisson
integral process is almost surely finite. -/
theorem poissonPointProcessIntegralProcess_increment_ae_lt_top
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal)
    (hν : HasSubordinatorLevyKhinchinRepresentation μ α ν) (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) {s t : NNReal} (hst : s ≤ t) :
    ∀ᵐ ω ∂(P : Measure Ω),
      poissonPointProcessIntegralProcessENNReal X t ω -
          poissonPointProcessIntegralProcessENNReal X s ω < ∞ :=
by
  -- Route correction: the naive pathwise identity
  -- `Y_t ω - Y_s ω = ∫ x d(stripFirstCoordinate X s t ω)` is false in `ENNReal` on points where
  -- `Y_s ω = Y_t ω = ∞`, so we first prove a.e. finiteness of the strip integral and of the left
  -- endpoint, then transport that a.e. identity.
  have hsfinite : ∀ᵐ ω ∂(P : Measure Ω), poissonPointProcessIntegralProcessENNReal X s ω < ∞ := by
    have hstripfinite :
        ∀ᵐ ω ∂(P : Measure Ω),
          (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X 0 s ω) < ∞ :=
      stripPoissonIntegral_ae_lt_top μ α ν hν P X hX bot_le
    -- Proof comment: the left endpoint is the zero-left strip integral `(0, s]`.
    simpa [poissonPointProcessIntegralProcessENNReal_eq_lintegral_strip_zero_left] using
      hstripfinite
  have hstripfinite :
      ∀ᵐ ω ∂(P : Measure Ω),
        (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) < ∞ :=
    stripPoissonIntegral_ae_lt_top μ α ν hν P X hX hst
  have hEq :
      ∀ᵐ ω ∂(P : Measure Ω),
        poissonPointProcessIntegralProcessENNReal X t ω -
            poissonPointProcessIntegralProcessENNReal X s ω =
          ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω :=
    poissonPointProcessIntegralProcess_increment_ae_eq_stripPoissonIntegral P X hst hsfinite
  -- Proof comment: on the full-measure event where the increment equals the strip integral, the
  -- strip finiteness theorem gives the desired finiteness of the increment.
  filter_upwards [hEq, hstripfinite] with ω hEqω hstripω
  simpa [hEqω] using hstripω

/-- Helper for Example 24.19: every fixed natural-time value is almost surely finite once the
increment finiteness theorem is available. -/
theorem poissonPointProcessIntegralProcess_nat_ae_lt_top
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal)
    (hν : HasSubordinatorLevyKhinchinRepresentation μ α ν) (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) (n : ℕ) :
    ∀ᵐ ω ∂(P : Measure Ω),
      poissonPointProcessIntegralProcessENNReal X (n : NNReal) ω < ∞ := by
  have hstripfinite :
      ∀ᵐ ω ∂(P : Measure Ω),
        poissonPointProcessIntegralProcessENNReal X n ω -
            poissonPointProcessIntegralProcessENNReal X 0 ω < ∞ :=
    poissonPointProcessIntegralProcess_increment_ae_lt_top μ α ν hν P X hX bot_le
  -- Proof comment: specialize the increment finiteness theorem to the interval `[0, n]` and
  -- simplify the left endpoint by the time-zero identity.
  simpa [poissonPointProcessIntegralProcessENNReal_zero] using
    hstripfinite

/-- Helper for Example 24.19: almost-sure finiteness at all natural times upgrades to all times by
monotonicity of the sample paths. -/
theorem poissonPointProcessIntegralProcess_ae_lt_top_of_nat
    (P : ProbabilityMeasure Ω) (X : Ω → Measure (NNReal × NNReal))
    (hnat :
      ∀ᵐ ω ∂(P : Measure Ω), ∀ n : ℕ,
        poissonPointProcessIntegralProcessENNReal X (n : NNReal) ω < ∞) :
    ∀ᵐ ω ∂(P : Measure Ω), ∀ t : NNReal,
      poissonPointProcessIntegralProcessENNReal X t ω < ∞ := by
  -- Proof comment: each path is monotone, so every time `t` is bounded above by the next
  -- integer time and therefore inherits its finiteness there.
  filter_upwards [hnat] with ω hω t
  let n : ℕ := Nat.ceil (t : ℝ)
  have htle : t ≤ (n : NNReal) := by
    exact_mod_cast Nat.le_ceil (t : ℝ)
  have hmono :
      poissonPointProcessIntegralProcessENNReal X t ω ≤
        poissonPointProcessIntegralProcessENNReal X (n : NNReal) ω := by
    -- Proof comment: enlarge the time strip from `(0, t]` to `(0, n]` pointwise inside the
    -- defining nonnegative integral.
    unfold poissonPointProcessIntegralProcessENNReal
    refine lintegral_mono fun z ↦ ?_
    have hsubset : Set.Ioc (0 : NNReal) t ⊆ Set.Ioc (0 : NNReal) (n : NNReal) := by
      intro x hx
      exact ⟨hx.1, le_trans hx.2 htle⟩
    have hindicator :
        Set.indicator (Set.Ioc (0 : NNReal) t) (fun _ ↦ (1 : ENNReal)) z.2 ≤
          Set.indicator (Set.Ioc (0 : NNReal) (n : NNReal)) (fun _ ↦ (1 : ENNReal)) z.2 := by
      by_cases hz_t : z.2 ∈ Set.Ioc (0 : NNReal) t
      · have hz_n : z.2 ∈ Set.Ioc (0 : NNReal) (n : NNReal) := hsubset hz_t
        simp [Set.indicator, hz_t, hz_n]
      · by_cases hz_n : z.2 ∈ Set.Ioc (0 : NNReal) (n : NNReal)
        · simp [Set.indicator, hz_t, hz_n]
        · simp [Set.indicator, hz_t, hz_n]
    simpa [mul_comm] using mul_le_mul_right' hindicator (z.1 : ENNReal)
  exact lt_of_le_of_lt hmono (hω n)

/-- On the almost-sure finite event supplied by the Poisson construction, coercing the
source-facing process back to `ENNReal` recovers the underlying extended integral. -/
theorem poissonPointProcessIntegralProcessNNReal_ae_coe_eq
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal)
    (hν : HasSubordinatorLevyKhinchinRepresentation μ α ν) (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) :
    ∀ᵐ ω ∂(P : Measure Ω), ∀ t : NNReal,
      (poissonPointProcessIntegralProcessNNReal X t ω : ENNReal) =
        poissonPointProcessIntegralProcessENNReal X t ω :=
by
  -- Proof comment: first collect almost-sure finiteness at every natural time, then use the
  -- monotone-path companion to extend finiteness to all `t`.
  have hnat :
      ∀ᵐ ω ∂(P : Measure Ω), ∀ n : ℕ,
        poissonPointProcessIntegralProcessENNReal X (n : NNReal) ω < ∞ := by
    exact ae_all_iff.2 fun n ↦
      poissonPointProcessIntegralProcess_nat_ae_lt_top μ α ν hν P X hX n
  have hall :
      ∀ᵐ ω ∂(P : Measure Ω), ∀ t : NNReal,
        poissonPointProcessIntegralProcessENNReal X t ω < ∞ :=
    poissonPointProcessIntegralProcess_ae_lt_top_of_nat P X hnat
  filter_upwards [hall] with ω hω t
  -- Proof comment: on the full-measure finite event, `ENNReal.coe_toNNReal` removes the coercion
  -- introduced in the `NNReal` companion definition.
  simpa [poissonPointProcessIntegralProcessNNReal] using
    ENNReal.coe_toNNReal (ne_of_lt (hω t))

/-- Helper for Example 24.19: after proving almost-sure finiteness of the left endpoint, the
`toNNReal` of the `ENNReal` increment agrees almost surely with the `toNNReal` strip integral. -/
theorem poissonPointProcessIntegralProcess_incrementToNNReal_ae_eq_stripPoissonIntegral_toNNReal
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal)
    (hν : HasSubordinatorLevyKhinchinRepresentation μ α ν) (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) {s t : NNReal} (hst : s ≤ t) :
    ∀ᵐ ω ∂(P : Measure Ω),
      (poissonPointProcessIntegralProcessENNReal X t ω -
          poissonPointProcessIntegralProcessENNReal X s ω).toNNReal =
        ((∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω).toNNReal) := by
  have hsfinite : ∀ᵐ ω ∂(P : Measure Ω), poissonPointProcessIntegralProcessENNReal X s ω < ∞ := by
    have hstripfinite :
        ∀ᵐ ω ∂(P : Measure Ω),
          (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X 0 s ω) < ∞ :=
      stripPoissonIntegral_ae_lt_top μ α ν hν P X hX bot_le
    -- Proof comment: normalize the left endpoint to the zero-left strip integral.
    simpa [poissonPointProcessIntegralProcessENNReal_eq_lintegral_strip_zero_left] using
      hstripfinite
  have hEq :
      ∀ᵐ ω ∂(P : Measure Ω),
        poissonPointProcessIntegralProcessENNReal X t ω -
            poissonPointProcessIntegralProcessENNReal X s ω =
          ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω :=
    poissonPointProcessIntegralProcess_increment_ae_eq_stripPoissonIntegral P X hst hsfinite
  -- Proof comment: once the `ENNReal` increment identity is available almost surely, apply
  -- `toNNReal` on both sides on that same full-measure event.
  filter_upwards [hEq] with ω hEqω
  simpa [hEqω]

/-- Helper for Example 24.19: the finite-valued `NNReal` increment agrees almost surely with the
`toNNReal` strip integral on the same time window. -/
theorem poissonPointProcessIntegralProcessNNReal_increment_ae_eq_stripPoissonIntegral_toNNReal
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal)
    (hν : HasSubordinatorLevyKhinchinRepresentation μ α ν) (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) {s t : NNReal} (hst : s ≤ t) :
    ∀ᵐ ω ∂(P : Measure Ω),
      poissonPointProcessIntegralProcessNNReal X t ω -
          poissonPointProcessIntegralProcessNNReal X s ω =
        ((∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω).toNNReal) := by
  have hstrip :
      ∀ᵐ ω ∂(P : Measure Ω),
        (poissonPointProcessIntegralProcessENNReal X t ω -
            poissonPointProcessIntegralProcessENNReal X s ω).toNNReal =
          ((∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω).toNNReal) :=
    poissonPointProcessIntegralProcess_incrementToNNReal_ae_eq_stripPoissonIntegral_toNNReal
      μ α ν hν P X hX hst
  have hsfinite :
      ∀ᵐ ω ∂(P : Measure Ω), poissonPointProcessIntegralProcessENNReal X s ω < ∞ := by
    have hstripfinite :
        ∀ᵐ ω ∂(P : Measure Ω),
          (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X 0 s ω) < ∞ :=
      stripPoissonIntegral_ae_lt_top μ α ν hν P X hX bot_le
    -- Proof comment: reuse the zero-left strip normalization for the left endpoint finiteness.
    simpa [poissonPointProcessIntegralProcessENNReal_eq_lintegral_strip_zero_left] using
      hstripfinite
  -- Proof comment: rewrite the `NNReal` increment as the `toNNReal` of the `ENNReal` increment,
  -- then invoke the strip-normalization bridge proved just above.
  filter_upwards [hstrip, hsfinite] with ω hstripω hsfiniteω
  rw [poissonPointProcessIntegralProcessNNReal, poissonPointProcessIntegralProcessNNReal,
    ← ENNReal.toNNReal_sub (ne_of_lt hsfiniteω)]
  exact hstripω

/-- Helper for Example 24.19: fixed bounded evaluations on adjacent monotone strips already satisfy
the finite-prefix product-law identity. -/
theorem stripFirstCoordinate_eval_map_eq_pi_of_monotoneTimes
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    {n : ℕ} (τ : Fin (n + 1) → NNReal) (hτ : Monotone τ)
    (A : Fin n → Set NNReal) (hA : ∀ i, MeasurableSet (A i)) :
    Measure.map
      (fun ω ↦ fun i : Fin n ↦
        stripFirstCoordinate X (τ i.castSucc) (τ i.succ) ω (A i))
      (P : Measure Ω) =
      Measure.pi
        (fun i : Fin n ↦
          Measure.map
            (fun ω ↦ stripFirstCoordinate X (τ i.castSucc) (τ i.succ) ω (A i))
            (P : Measure Ω)) := by
  have hIndep :
      iIndepFun
        (fun i ω ↦ stripFirstCoordinate X (τ i.castSucc) (τ i.succ) ω (A i))
        (P : Measure Ω) :=
    stripFirstCoordinate_eval_iIndepFun_of_monotoneTimes P ν X hX τ hτ A hA
  have hMeas :
      ∀ i : Fin n,
        AEMeasurable
          (fun ω ↦ stripFirstCoordinate X (τ i.castSucc) (τ i.succ) ω (A i))
          (P : Measure Ω) := by
    intro i
    -- Proof comment: each scalar bounded evaluation is a measurable postcomposition of the
    -- strip random measure with ordinary measurable-set evaluation.
    exact
      ((Measure.measurable_coe (hA i)).comp
        (stripFirstCoordinate_measurable X hX.1.measurable (τ i.castSucc) (τ i.succ))).aemeasurable
  -- Proof comment: the existing scalar `iIndepFun` owner is equivalent to the finite-prefix
  -- product-law identity of the tuple map.
  exact (iIndepFun_iff_map_fun_eq_pi_map hMeas).1 hIndep

/-- Helper for Example 24.19: measurable subsets of `NNReal`, packaged as coordinate indices for
measure evaluations. -/
private abbrev MeasurableSetNNReal :=
  {A : Set NNReal // MeasurableSet A}

/-- Helper for Example 24.19: the full measurable-set evaluation family on `Measure NNReal`. -/
private def measureMeasurableSetEvaluationFamily :
    Measure NNReal → MeasurableSetNNReal → ENNReal :=
  fun μ A ↦ μ A.1

/-- Helper for Example 24.19: the measurable-set evaluation family on `Measure NNReal` is
coordinatewise measurable. -/
private theorem measurable_measureMeasurableSetEvaluationFamily :
    Measurable (measureMeasurableSetEvaluationFamily) := by
  -- Proof comment: each coordinate is an ordinary measurable-set evaluation map on `Measure NNReal`.
  exact measurable_pi_lambda _ fun A ↦ Measure.measurable_coe A.2

/-- Helper for Example 24.19: the Giry measurable space on `Measure NNReal` is generated by the
measurable-set evaluation family. -/
private theorem measureMeasurableSpace_eq_comap_measurableSetEvaluationFamily :
    (inferInstance : MeasurableSpace (Measure NNReal)) =
      MeasurableSpace.comap
        measureMeasurableSetEvaluationFamily
        (inferInstance : MeasurableSpace (MeasurableSetNNReal → ENNReal)) := by
  have hFamilyMeas :
      Measurable measureMeasurableSetEvaluationFamily :=
    measurable_measureMeasurableSetEvaluationFamily
  refine le_antisymm ?_ hFamilyMeas.comap_le
  rw [show (inferInstance : MeasurableSpace (Measure NNReal)) =
      ⨆ (A : Set NNReal) (_ : MeasurableSet A), (borel ENNReal).comap (fun μ : Measure NNReal ↦ μ A) by
        rfl]
  refine iSup₂_le ?_
  intro A hA
  refine MeasurableSpace.comap_le_iff_le_map.2 ?_
  let A' : MeasurableSetNNReal := ⟨A, hA⟩
  have hSelf :
      @Measurable (Measure NNReal) (MeasurableSetNNReal → ENNReal)
        (MeasurableSpace.comap
          measureMeasurableSetEvaluationFamily
          (inferInstance : MeasurableSpace (MeasurableSetNNReal → ENNReal)))
        (inferInstance : MeasurableSpace (MeasurableSetNNReal → ENNReal))
        measureMeasurableSetEvaluationFamily :=
    Measurable.of_comap_le le_rfl
  -- Proof comment: evaluation on a fixed measurable set is one coordinate of the full evaluation
  -- family, so it is measurable for the pulled-back sigma-algebra.
  simpa [measureMeasurableSetEvaluationFamily, A'] using
    (measurable_pi_apply A').comp hSelf

/-- Helper for Example 24.19: a probability measure on a pullback product sigma-algebra is
determined by its pushforward along the full coordinate family. -/
private theorem probabilityMeasureEqOfMapEqOfComapPi
    {Ω' : Type*} {ι : Type*} {α : ι → Type*} [mΩ' : MeasurableSpace Ω']
    [∀ i, MeasurableSpace (α i)] {P Q : ProbabilityMeasure Ω'} {X : Ω' → ∀ i, α i}
    (hX :
      mΩ' =
        MeasurableSpace.comap X (inferInstance : MeasurableSpace ((i : ι) → α i)))
    (hmap : (P : Measure Ω').map X = (Q : Measure Ω').map X) :
    P = Q := by
  apply ProbabilityMeasure.toMeasure_injective
  have hXm : Measurable X := by
    exact Measurable.of_comap_le (by simpa [hX])
  let G : Set (Set Ω') := Set.preimage X '' measurableCylinders α
  have hgen : mΩ' = MeasurableSpace.generateFrom G := by
    -- Proof comment: the domain sigma-algebra is the pullback of the cylinder generator.
    calc
      mΩ' = MeasurableSpace.comap X (inferInstance : MeasurableSpace ((i : ι) → α i)) := hX
      _ = MeasurableSpace.comap X (MeasurableSpace.generateFrom (measurableCylinders α)) := by
            rw [generateFrom_measurableCylinders]
      _ = MeasurableSpace.generateFrom G := by
            rw [MeasurableSpace.comap_generateFrom]
  have hG : IsPiSystem G := by
    have hmc : IsPiSystem (measurableCylinders α) := by
      simpa using
        (isPiSystem_measurableCylinders : IsPiSystem (measurableCylinders α))
    intro s hs t ht hst
    rcases hs with ⟨u, hu, rfl⟩
    rcases ht with ⟨v, hv, rfl⟩
    have huv_nonempty : (u ∩ v).Nonempty := by
      rcases hst with ⟨ω, hωu, hωv⟩
      exact ⟨X ω, hωu, hωv⟩
    refine ⟨u ∩ v, hmc u hu v hv huv_nonempty, ?_⟩
    ext ω
    rfl
  refine ext_of_generate_finite G hgen hG ?_ ?_
  · intro s hs
    rcases hs with ⟨u, hu, rfl⟩
    have hu_meas : MeasurableSet u := MeasurableSet.of_mem_measurableCylinders hu
    rw [← Measure.map_apply hXm hu_meas, hmap, Measure.map_apply hXm hu_meas]
  · simp

/-- Helper for Example 24.19: finite tuples of `Measure NNReal` are measurable through the full
coordinatewise evaluation family. -/
private theorem measurePiMeasurableSpace_eq_comap_measureMeasurableSetEvaluationFamily
    {n : ℕ} :
    (inferInstance : MeasurableSpace (Fin n → Measure NNReal)) =
      MeasurableSpace.comap
        (fun ξ (i : Fin n) ↦ measureMeasurableSetEvaluationFamily (ξ i))
        (inferInstance : MeasurableSpace (Fin n → MeasurableSetNNReal → ENNReal)) := by
  let F : (Fin n → Measure NNReal) → Fin n → MeasurableSetNNReal → ENNReal := fun ξ i ↦
    measureMeasurableSetEvaluationFamily (ξ i)
  have hFmeas : Measurable F := by
    -- Proof comment: each outer coordinate is the measurable evaluation family composed with the
    -- corresponding tuple projection.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_measureMeasurableSetEvaluationFamily.comp (measurable_pi_apply i)
  refine le_antisymm ?_ hFmeas.comap_le
  rw [show (inferInstance : MeasurableSpace (Fin n → Measure NNReal)) =
      ⨆ i : Fin n,
        MeasurableSpace.comap
          (fun ξ : Fin n → Measure NNReal ↦ ξ i)
          (inferInstance : MeasurableSpace (Measure NNReal)) by
        rfl]
  refine iSup_le fun i ↦ ?_
  rw [measureMeasurableSpace_eq_comap_measurableSetEvaluationFamily]
  simpa [F, Function.comp] using
    (MeasurableSpace.comap_le_comap_pi
      (g := fun i : Fin n ↦ fun ξ : Fin n → Measure NNReal ↦
        measureMeasurableSetEvaluationFamily (ξ i)) i)

/-- Helper for Example 24.19: the source PPP independence owner on `Fin n` transports to any
finite index type. -/
private theorem poissonPointProcess_iIndepFun_of_finite_pairwiseDisjoint
    {α : Type*} [Fintype α]
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    (B : α → Set (NNReal × NNReal))
    (hB : ∀ a, MeasurableSet (B a))
    (hB_disj : Pairwise (fun a b ↦ Disjoint (B a) (B b))) :
    iIndepFun (fun a ω ↦ X ω (B a)) (P : Measure Ω) := by
  classical
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  have hFin :
      iIndepFun (fun k ω ↦ X ω (B (e k))) (P : Measure Ω) := by
    refine hX.2.1 _ (fun k ↦ B (e k)) (fun k ↦ hB (e k)) ?_
    intro i j hij
    exact hB_disj (e.injective.ne hij)
  -- Proof comment: `Fin (card α)` and `α` carry the same finite family, so surjective reindexing
  -- transports the source PPP product law to the target index type.
  simpa [e] using hFin.of_precomp e.surjective

/-- Helper for Example 24.19: the membership-pattern cell of a finite measurable-set family
records exactly which sets contain a point. -/
private def membershipPatternCell {m : ℕ} (As : Fin m → MeasurableSetNNReal)
    (s : Finset (Fin m)) : Set NNReal :=
  {x | ∀ i, x ∈ (As i).1 ↔ i ∈ s}

/-- Helper for Example 24.19: every measurable-set membership-pattern cell is measurable. -/
private theorem measurableSet_membershipPatternCell {m : ℕ}
    (As : Fin m → MeasurableSetNNReal) (s : Finset (Fin m)) :
    MeasurableSet (membershipPatternCell As s) := by
  have hrepr :
      membershipPatternCell As s =
        ⋂ i, if i ∈ s then (As i).1 else ((As i).1)ᶜ := by
    ext x
    constructor
    · intro hx
      simp only [Set.mem_iInter]
      intro i
      by_cases hi : i ∈ s
      · simpa [hi] using (hx i).2 hi
      · have hnotin : x ∉ (As i).1 := by
          intro hxi
          exact hi ((hx i).1 hxi)
        simpa [hi, Set.mem_compl_iff, hnotin]
    · intro hx
      have hx' : ∀ i, x ∈ if i ∈ s then (As i).1 else ((As i).1)ᶜ := by
        simpa [Set.mem_iInter] using hx
      intro i
      constructor
      · intro hxi
        by_cases hi : i ∈ s
        · exact hi
        · have hcompl : x ∈ ((As i).1)ᶜ := by
            simpa [hi] using hx' i
          exact False.elim (hcompl hxi)
      · intro hi
        simpa [hi] using hx' i
  -- Proof comment: the cell is a finite intersection of measurable sets and complements.
  rw [hrepr]
  exact MeasurableSet.iInter fun i ↦ by
    by_cases hi : i ∈ s
    · simpa [hi] using (As i).2
    · simpa [hi] using (As i).2.compl

/-- Helper for Example 24.19: distinct membership patterns define disjoint measurable cells. -/
private theorem disjoint_membershipPatternCell {m : ℕ}
    (As : Fin m → MeasurableSetNNReal) {s t : Finset (Fin m)} (hst : s ≠ t) :
    Disjoint (membershipPatternCell As s) (membershipPatternCell As t) := by
  -- Proof comment: a common point would force the same membership pattern twice.
  refine Set.disjoint_left.2 fun x hsx htx ↦ ?_
  apply hst
  ext i
  constructor
  · intro hi
    exact (htx i).1 ((hsx i).2 hi)
  · intro hi
    exact (hsx i).1 ((htx i).2 hi)

/-- Helper for Example 24.19: any finite measurable-set tuple factors through the disjoint tuple
of its nonempty membership-pattern cells. -/
-- TODO: prove the finite partition factorization by the explicit membership-pattern partition
-- route; the current blocker is the regrouping interface used later for strip-evaluation blocks.
private theorem measurableSetTupleFactorsThroughPatternCells {m : ℕ}
    (As : Fin m → MeasurableSetNNReal) :
    ∃ k : ℕ, ∃ Bs : Fin k → MeasurableSetNNReal,
      Pairwise (fun i j ↦ Disjoint ((Bs i).1 : Set NNReal) ((Bs j).1 : Set NNReal)) ∧
      ∃ collapse : (Fin k → ENNReal) → Fin m → ENNReal,
        Measurable collapse ∧
        ∀ μ : Measure NNReal,
          (fun i ↦ μ ((As i).1)) =
            collapse (fun j ↦ μ ((Bs j).1)) :=
by
  classical
  let e : Fin (Fintype.card (Finset (Fin m))) ≃ Finset (Fin m) :=
    (Fintype.equivFin (Finset (Fin m))).symm
  let Bs : Fin (Fintype.card (Finset (Fin m))) → MeasurableSetNNReal := fun j ↦
    ⟨membershipPatternCell As (e j), measurableSet_membershipPatternCell As (e j)⟩
  let collapse :
      (Fin (Fintype.card (Finset (Fin m))) → ENNReal) → Fin m → ENNReal := fun y i ↦
        let S : Finset (Fin (Fintype.card (Finset (Fin m)))) :=
          Finset.univ.filter (fun j ↦ i ∈ e j)
        ;
        S.sum y
  refine ⟨_, Bs, ?_, collapse, ?_, ?_⟩
  · intro i j hij
    exact disjoint_membershipPatternCell As (e.injective.ne hij)
  · -- Proof comment: each output coordinate is a finite sum of measurable coordinate projections.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact Finset.measurable_sum _ fun j _ ↦ measurable_pi_apply j
  · intro μ
    funext i
    let S : Finset (Fin (Fintype.card (Finset (Fin m)))) :=
      Finset.univ.filter (fun j ↦ i ∈ e j)
    have hUnion :
        (As i).1 = ⋃ j ∈ S, ((Bs j).1 : Set NNReal) := by
      ext x
      constructor
      · intro hx
        let sx : Finset (Fin m) := Finset.univ.filter (fun j ↦ x ∈ (As j).1)
        have hsx_mem : x ∈ membershipPatternCell As sx := by
          intro j
          simp [sx]
        have hi : i ∈ sx := by
          simpa [sx] using hx
        refine Set.mem_iUnion.2 ⟨e.symm sx, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
        · simpa [S, sx] using hi
        · simpa [Bs, sx] using hsx_mem
      · intro hx
        rcases Set.mem_iUnion.1 hx with ⟨j, hx⟩
        rcases Set.mem_iUnion.1 hx with ⟨hjS, hxj⟩
        exact (hxj i).2 (by simpa [S] using hjS)
    have hS_disj :
        Set.PairwiseDisjoint (S : Set (Fin (Fintype.card (Finset (Fin m)))))
          (fun j ↦ ((Bs j).1 : Set NNReal)) := by
      intro j hj k hk hjk
      exact (disjoint_membershipPatternCell As (show e j ≠ e k from fun h ↦ hjk (e.injective h)))
    -- Proof comment: each original measurable set is the disjoint union of the membership-pattern
    -- cells that contain its index, so its measure is the corresponding finite sum of cell masses.
    rw [hUnion, MeasureTheory.measure_biUnion_finset hS_disj (fun j _ ↦ (Bs j).2)]

/-- Helper for Example 24.19: a Sigma-indexed independent family can be regrouped into an outer
family of dependent function-valued random variables. -/
private theorem groupedCellCount_iIndepFun_of_flattened
    (P : ProbabilityMeasure Ω)
    {I : Type*} [Fintype I] {κ : I → Type*} [∀ i, Fintype (κ i)]
    {β : (p : (i : I) × κ i) → Type*} [∀ p, MeasurableSpace (β p)]
    (Y : (p : (i : I) × κ i) → Ω → β p)
    (hY : ∀ p, Measurable (Y p))
    (hFlat : iIndepFun Y (P : Measure Ω)) :
    iIndepFun (fun i ω ↦ fun (u : κ i) ↦ Y ⟨i, u⟩ ω) (P : Measure Ω) := by
  letI : ∀ i (u : κ i), IsProbabilityMeasure ((P : Measure Ω).map (fun ω ↦ Y ⟨i, u⟩ ω)) :=
    fun i u ↦ Measure.isProbabilityMeasure_map (hY ⟨i, u⟩).aemeasurable
  have hFiber (i : I) :
      iIndepFun (fun (u : κ i) ω ↦ Y ⟨i, u⟩ ω) (P : Measure Ω) := by
    -- Proof comment: each fiber is obtained by restricting the flat Sigma-indexed family.
    exact hFlat.precomp (g := fun u : κ i ↦ (⟨i, u⟩ : (p : I) × κ p)) fun a b hab ↦ by
      cases hab
      rfl
  have hFiberMap (i : I) :
      (P : Measure Ω).map (fun ω (u : κ i) ↦ Y ⟨i, u⟩ ω) =
        Measure.infinitePi (fun u : κ i ↦ (P : Measure Ω).map (fun ω ↦ Y ⟨i, u⟩ ω)) := by
    -- Proof comment: one grouped block has the product law of its fiber coordinates.
    exact (iIndepFun_iff_map_fun_eq_infinitePi_map fun u : κ i ↦ hY ⟨i, u⟩).1 (hFiber i)
  have hFlatMap :
      (P : Measure Ω).map (fun ω p ↦ Y p ω) =
        Measure.infinitePi (fun p : (i : I) × κ i ↦ (P : Measure Ω).map (fun ω ↦ Y p ω)) := by
    -- Proof comment: the flat Sigma-indexed independence is exactly the infinite-product law.
    exact (iIndepFun_iff_map_fun_eq_infinitePi_map hY).1 hFlat
  have hGroupedMeas :
      ∀ i, Measurable (fun ω (u : κ i) ↦ Y ⟨i, u⟩ ω) := by
    intro i
    -- Proof comment: each grouped block is the measurable tuple of the fiber coordinates.
    exact measurable_pi_lambda _ fun u ↦ hY ⟨i, u⟩
  refine (iIndepFun_iff_map_fun_eq_infinitePi_map hGroupedMeas).2 ?_
  have hUncurry :
      (MeasurableEquiv.piCurry (fun i u => β ⟨i, u⟩)).symm ∘
          (fun ω i u ↦ Y ⟨i, u⟩ ω) =
        fun ω p ↦ Y p ω := by
    -- Proof comment: uncurrying the grouped tuple recovers the original flat Sigma-indexed tuple.
    ext ω p
    rcases p with ⟨i, u⟩
    rfl
  have hGroupedMarg :
      Measure.infinitePi (fun i : I ↦ (P : Measure Ω).map (fun ω (u : κ i) ↦ Y ⟨i, u⟩ ω)) =
        Measure.infinitePi
          (fun i : I ↦ Measure.infinitePi (fun u : κ i ↦ (P : Measure Ω).map (fun ω ↦ Y ⟨i, u⟩ ω))) := by
    -- Proof comment: replace each grouped marginal by the already proved fiber product law.
    exact congrArg Measure.infinitePi (funext hFiberMap)
  -- Proof comment: compare both sides after uncurrying through `piCurry`; the left-hand side
  -- becomes the flat tuple law, and the right-hand side becomes the flat product law.
  rw [← ((MeasurableEquiv.piCurry (fun i u => β ⟨i, u⟩)).symm).map_measurableEquiv_injective.eq_iff,
    Measure.map_map (by fun_prop) (by fun_prop), hUncurry, hFlatMap, hGroupedMarg,
    Measure.infinitePi_map_piCurry_symm]

/-- Helper for Example 24.19: after flattening the pattern cells inside each strip block, the
resulting space-time rectangles are pairwise disjoint. -/
private theorem stripPatternRectangles_pairwiseDisjoint
    {n : ℕ} (τ : Fin (n + 1) → NNReal) (hτ : Monotone τ)
    (I : Finset (Fin n)) (k : I → ℕ)
    (Bs : ∀ i : I, Fin (k i) → MeasurableSetNNReal)
    (hBs :
      ∀ i,
        Pairwise (fun u v ↦ Disjoint (((Bs i u).1 : Set NNReal)) (((Bs i v).1 : Set NNReal)))) :
    Pairwise
      (fun p q : (i : I) × Fin (k i) ↦
        Disjoint
          ((((Bs p.1 p.2).1 : Set NNReal) ×ˢ Set.Ioc (τ p.1.1.castSucc) (τ p.1.1.succ)))
          ((((Bs q.1 q.2).1 : Set NNReal) ×ˢ Set.Ioc (τ q.1.1.castSucc) (τ q.1.1.succ)))) := by
  intro p q hpq
  rcases p with ⟨i, u⟩
  rcases q with ⟨j, v⟩
  by_cases hij : i = j
  · subst hij
    have huv : u ≠ v := by
      intro huv
      apply hpq
      cases huv
      rfl
    -- Proof comment: inside one strip, the flattened pattern cells are already pairwise disjoint
    -- in the spatial coordinate, so the product rectangles are disjoint as well.
    refine Set.disjoint_left.2 ?_
    intro z hz₁ hz₂
    exact Set.disjoint_left.mp (hBs i huv) hz₁.1 hz₂.1
  · have hij_val : i.1 ≠ j.1 := by
      intro hij_val
      exact hij (Subtype.ext hij_val)
    rcases lt_or_gt_of_ne hij_val with hij_lt | hij_gt
    · -- Proof comment: distinct block indices correspond to disjoint adjacent time strips on the
      -- monotone grid, so no point can lie in both product rectangles.
      refine Set.disjoint_left.2 ?_
      intro z hz₁ hz₂
      have hle : τ i.1.succ ≤ τ j.1.castSucc := by
        exact hτ (show i.1.succ ≤ j.1.castSucc by
          exact Fin.succ_le_castSucc_iff.mpr (Nat.succ_le_of_lt hij_lt))
      exact (Set.Ioc_disjoint_Ioc_of_le hle).le_bot ⟨hz₁.2, hz₂.2⟩
    · -- Proof comment: the reverse inequality gives the symmetric disjointness statement.
      refine Set.disjoint_left.2 ?_
      intro z hz₁ hz₂
      have hle : τ j.1.succ ≤ τ i.1.castSucc := by
        exact hτ (show j.1.succ ≤ i.1.castSucc by
          exact Fin.succ_le_castSucc_iff.mpr (Nat.succ_le_of_lt hij_gt))
      exact (Set.Ioc_disjoint_Ioc_of_le hle).le_bot ⟨hz₂.2, hz₁.2⟩

/-- Helper for Example 24.19: finite blocks of strip evaluations are the remaining owner needed
to upgrade scalar strip independence to the full evaluation process. -/
-- Route correction: the missing owner is the block-level regrouping theorem, not another scalar
-- strip lemma. Flatten the pattern cells inside each block, apply PPP independence once on the
-- disjoint rectangles, and collapse back to the original finite evaluation tuple.
private theorem stripFirstCoordinate_evalBlock_iIndepFun_of_monotoneTimes
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    {n : ℕ} (τ : Fin (n + 1) → NNReal) (hτ : Monotone τ)
    (I : Finset (Fin n)) (J : (i : I) → Finset MeasurableSetNNReal) :
    iIndepFun
      (fun i ω (j : J i) ↦
        stripFirstCoordinate X (τ i.1.castSucc) (τ i.1.succ) ω j.1.1)
      (P : Measure Ω) :=
by
  classical
  let e : (i : I) → Fin (Fintype.card (J i)) ≃ J i := fun i ↦ (Fintype.equivFin (J i)).symm
  let As : (i : I) → Fin (Fintype.card (J i)) → MeasurableSetNNReal := fun i j ↦ (e i j).1
  choose k Bs hBs collapse hcollapse_meas hcollapse_spec using
    fun i ↦ measurableSetTupleFactorsThroughPatternCells (As i)
  let rect : (p : (i : I) × Fin (k i)) → Set (NNReal × NNReal) := fun p ↦
    (((Bs p.1 p.2).1 : Set NNReal) ×ˢ Set.Ioc (τ p.1.1.castSucc) (τ p.1.1.succ))
  have hrect_meas : ∀ p, MeasurableSet (rect p) := by
    intro p
    exact (Bs p.1 p.2).2.prod measurableSet_Ioc
  have hrect_disj :
      Pairwise (fun p q : (i : I) × Fin (k i) ↦ Disjoint (rect p) (rect q)) :=
    stripPatternRectangles_pairwiseDisjoint τ hτ I k Bs hBs
  let Y : (p : (i : I) × Fin (k i)) → Ω → ENNReal := fun p ω ↦ X ω (rect p)
  have hY_meas : ∀ p, Measurable (Y p) := by
    intro p
    -- Proof comment: each flattened rectangle count is an ordinary measurable evaluation of the
    -- source random measure.
    exact ((Measure.measurable_coe (hrect_meas p)).comp hX.1.measurable)
  have hFlat : iIndepFun Y (P : Measure Ω) := by
    -- Proof comment: all flattened rectangles are pairwise disjoint, so the source PPP gives the
    -- full flat Sigma-indexed independence in one application.
    exact
      poissonPointProcess_iIndepFun_of_finite_pairwiseDisjoint
        P ν X hX rect hrect_meas hrect_disj
  have hGrouped :
      iIndepFun (fun i ω ↦ fun u : Fin (k i) ↦ Y ⟨i, u⟩ ω) (P : Measure Ω) := by
    -- Proof comment: regroup the flat Sigma-indexed family back into one finite block for each
    -- time strip.
    exact groupedCellCount_iIndepFun_of_flattened P Y hY_meas hFlat
  let recover : (i : I) → (Fin (k i) → ENNReal) → J i → ENNReal := fun i y j ↦
    collapse i y ((e i).symm j)
  have hrecover_meas : ∀ i, Measurable (recover i) := by
    intro i
    -- Proof comment: recovering one original block is just the measurable collapse map followed
    -- by coordinate reindexing along the chosen finite equivalence.
    refine measurable_pi_lambda _ fun j ↦ ?_
    exact (measurable_pi_apply ((e i).symm j)).comp (hcollapse_meas i)
  have hRecovered :
      iIndepFun
        (fun i ω ↦ recover i (fun u : Fin (k i) ↦ Y ⟨i, u⟩ ω))
        (P : Measure Ω) := by
    -- Proof comment: measurably collapsing each disjoint cell block preserves independence across
    -- the outer strip index.
    exact hGrouped.comp recover hrecover_meas
  -- Proof comment: the collapse identities turn the recovered cell-count blocks back into the
  -- original strip-evaluation blocks.
  refine hRecovered.congr ?_
  intro i
  exact Filter.Eventually.of_forall fun ω ↦ by
    ext j
    let μi : Measure NNReal := stripFirstCoordinate X (τ i.1.castSucc) (τ i.1.succ) ω
    have hcoord :
        collapse i (fun u : Fin (k i) ↦ μi ((Bs i u).1)) ((e i).symm j) =
          μi j.1.1 := by
      simpa [As, μi] using
        (congrArg (fun g ↦ g ((e i).symm j)) (hcollapse_spec i μi)).symm
    have hrect_eval :
        (fun u : Fin (k i) ↦ Y ⟨i, u⟩ ω) =
          fun u : Fin (k i) ↦ μi ((Bs i u).1) := by
      funext u
      simpa [Y, rect, μi] using
        (stripFirstCoordinate_apply
          X (τ i.1.castSucc) (τ i.1.succ) ω (Bs i u).2).symm
    simpa [recover, hrect_eval] using hcoord

/-- Helper for Example 24.19: finite block independence on cylinder generators upgrades to
independence of the full function-valued family. -/
private theorem iIndepFun_of_finiteBlockCylinders
    {I : Type*} [Fintype I] {κ : I → Type*} {β : I → Type*}
    [∀ i, MeasurableSpace (β i)]
    (P : ProbabilityMeasure Ω)
    (F : (i : I) → Ω → κ i → β i)
    (hF : ∀ i, Measurable (fun ω j ↦ F i ω j))
    (hBlock :
      ∀ J : (i : I) → Finset (κ i),
        iIndepFun (fun i ω (j : J i) ↦ F i ω j.1) (P : Measure Ω)) :
    iIndepFun (fun i ω ↦ F i ω) (P : Measure Ω) := by
  classical
  refine
    iIndepFun_of_iIndepSets_preimage_generators (μ := (P : Measure Ω))
      (X := fun i ω ↦ F i ω) (hX := hF)
      (ℰ := fun i ↦ measurableCylinders (fun _ : κ i ↦ β i)) ?_ ?_ ?_
  · intro i
    simpa using
      (MeasureTheory.isPiSystem_measurableCylinders :
        IsPiSystem (measurableCylinders (fun _ : κ i ↦ β i)))
  · intro i
    simpa using
      (MeasureTheory.generateFrom_measurableCylinders :
        MeasurableSpace.generateFrom (measurableCylinders (fun _ : κ i ↦ β i)) =
          MeasurableSpace.pi)
  · rw [ProbabilityTheory.iIndepSets_iff]
    intro S sets hsets
    have hCyl :
        ∀ i, ∃ J : Finset (κ i), ∃ T : Set ((j : J) → β i),
          MeasurableSet T ∧
            (i ∈ S → sets i = (fun ω ↦ F i ω) ⁻¹' cylinder J T) := by
      intro i
      by_cases hi : i ∈ S
      · rcases hsets i hi with ⟨C, hC, hCeq⟩
        rcases (MeasureTheory.mem_measurableCylinders C).1 hC with ⟨J, T, hT, rfl⟩
        exact ⟨J, T, hT, fun _ ↦ hCeq.symm⟩
      · exact ⟨∅, Set.univ, MeasurableSet.univ, fun h ↦ False.elim (hi h)⟩
    choose J T hT hEq using hCyl
    have hBlockJ :
        iIndepFun (fun i ω (j : J i) ↦ F i ω j.1) (P : Measure Ω) :=
      hBlock J
    have hMul :
        (P : Measure Ω) (⋂ i ∈ S, (fun ω : Ω ↦ fun j : J i ↦ F i ω j.1) ⁻¹' T i) =
          ∏ i ∈ S, (P : Measure Ω) ((fun ω : Ω ↦ fun j : J i ↦ F i ω j.1) ⁻¹' T i) := by
      -- Proof comment: the chosen cylinder at each index depends on only finitely many inner
      -- coordinates, so the corresponding block family is covered by the finite-block owner.
      exact hBlockJ.measure_inter_preimage_eq_mul S (fun i hi ↦ hT i)
    have hrewrite :
        ∀ i, i ∈ S →
          (fun ω : Ω ↦ fun j : J i ↦ F i ω j.1) ⁻¹' T i = sets i := by
      intro i hi
      calc
        (fun ω : Ω ↦ fun j : J i ↦ F i ω j.1) ⁻¹' T i
            = (fun ω ↦ F i ω) ⁻¹' cylinder (J i) (T i) := by
                ext ω
                rfl
        _ = sets i := by
              simpa using (hEq i hi).symm
    have hInter :
        (⋂ i ∈ S, sets i) =
          ⋂ i ∈ S, (fun ω : Ω ↦ fun j : J i ↦ F i ω j.1) ⁻¹' T i := by
      ext ω
      simp only [Set.mem_iInter]
      constructor
      · intro h i hi
        have hω : ω ∈ sets i := h i hi
        rwa [← hrewrite i hi] at hω
      · intro h i hi
        have hω :
            ω ∈ (fun ω : Ω ↦ fun j : J i ↦ F i ω j.1) ⁻¹' T i := h i hi
        rwa [hrewrite i hi] at hω
    have hProd :
        ∏ i ∈ S, (P : Measure Ω) ((fun ω : Ω ↦ fun j : J i ↦ F i ω j.1) ⁻¹' T i) =
          ∏ i ∈ S, (P : Measure Ω) (sets i) := by
      refine Finset.prod_congr rfl ?_
      intro i hi
      rw [hrewrite i hi]
    -- Proof comment: replacing each generator event by its finite-coordinate block form turns the
    -- cylinder product formula into the desired independence identity.
    calc
      (P : Measure Ω) (⋂ i ∈ S, sets i)
          = (P : Measure Ω) (⋂ i ∈ S, (fun ω : Ω ↦ fun j : J i ↦ F i ω j.1) ⁻¹' T i) := by
              rw [hInter]
      _ = ∏ i ∈ S, (P : Measure Ω) ((fun ω : Ω ↦ fun j : J i ↦ F i ω j.1) ⁻¹' T i) := hMul
      _ = ∏ i ∈ S, (P : Measure Ω) (sets i) := hProd

-- Route correction: the missing owner is the finite-cylinder extension theorem, not another
-- downstream evaluation wrapper. Apply the existing finite block theorem on measurable cylinders
-- and then lift to the full function space with Theorem 2.16.
private theorem stripFirstCoordinate_evalFamily_iIndepFunFin_of_monotoneTimes
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    {n : ℕ} (τ : Fin (n + 1) → NNReal) (hτ : Monotone τ) :
    iIndepFun
      (fun (i : Fin n) ω (A : MeasurableSetNNReal) ↦
        stripFirstCoordinate X (τ i.castSucc) (τ i.succ) ω A.1)
      (P : Measure Ω) :=
by
  classical
  let F : (i : Fin n) → Ω → MeasurableSetNNReal → ENNReal := fun i ω A ↦
    stripFirstCoordinate X (τ i.castSucc) (τ i.succ) ω A.1
  have hF : ∀ i : Fin n, Measurable (fun ω A ↦ F i ω A) := by
    intro i
    -- Proof comment: each evaluation family is coordinatewise measurable because it is ordinary
    -- measurable-set evaluation composed with the strip random measure.
    refine measurable_pi_lambda _ fun A ↦ ?_
    exact
      ((Measure.measurable_coe A.2).comp
        (stripFirstCoordinate_measurable X hX.1.measurable (τ i.castSucc) (τ i.succ)))
  have hBlock :
      ∀ J : (i : Fin n) → Finset MeasurableSetNNReal,
        iIndepFun (fun i ω (j : J i) ↦ F i ω j.1) (P : Measure Ω) := by
    intro J
    let Juniv : (i : (Finset.univ : Finset (Fin n))) → Finset MeasurableSetNNReal := fun i ↦
      J i.1
    have hUniv :
        iIndepFun (fun i ω (j : Juniv i) ↦ F i.1 ω j.1) (P : Measure Ω) := by
      -- Proof comment: the previously closed block owner already gives independence on the
      -- `univ`-indexed subtype carrying all strip coordinates.
      simpa [Juniv, F] using
        stripFirstCoordinate_evalBlock_iIndepFun_of_monotoneTimes
          P ν X hX τ hτ (Finset.univ : Finset (Fin n)) Juniv
    have hsurj :
        Function.Surjective (fun i : ↥(Finset.univ : Finset (Fin n)) ↦ i.1) := by
      intro i
      exact ⟨⟨i, by simp⟩, rfl⟩
    -- Proof comment: forgetting the trivial `i ∈ univ` proof reindexes the same block family back
    -- to the original `Fin n` coordinates.
    exact hUniv.of_precomp hsurj
  -- Proof comment: measurable cylinders generate the function-space sigma-algebra, so finite block
  -- independence upgrades directly to independence of the full evaluation families.
  simpa [F] using iIndepFun_of_finiteBlockCylinders P F hF hBlock

/-- Helper for Example 24.19: finite prefixes of the strip random measures themselves are
independent. -/
-- TODO: identify the finite tuple law of strip random measures with the product of its marginals
-- via the full measurable-set evaluation family.
private theorem stripFirstCoordinate_iIndepFunFin_of_monotoneTimes
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    {n : ℕ} (τ : Fin (n + 1) → NNReal) (hτ : Monotone τ) :
    iIndepFun
      (fun (i : Fin n) ω ↦ stripFirstCoordinate X (τ i.castSucc) (τ i.succ) ω)
      (P : Measure Ω) := by
  let stripFamily : Ω → Fin n → Measure NNReal := fun ω i ↦
    stripFirstCoordinate X (τ i.castSucc) (τ i.succ) ω
  have hstripFamily_meas : Measurable stripFamily := by
    -- Proof comment: each coordinate of the strip tuple is a measurable random measure.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact stripFirstCoordinate_measurable X hX.1.measurable (τ i.castSucc) (τ i.succ)
  have hMeas :
      ∀ i : Fin n, AEMeasurable (fun ω ↦ stripFamily ω i) (P : Measure Ω) := by
    intro i
    exact (stripFirstCoordinate_measurable X hX.1.measurable (τ i.castSucc) (τ i.succ)).aemeasurable
  have hEvalMeas :
      ∀ i : Fin n,
        AEMeasurable
          (fun ω ↦ measureMeasurableSetEvaluationFamily (stripFamily ω i))
          (P : Measure Ω) := by
    intro i
    exact
      (measurable_measureMeasurableSetEvaluationFamily.comp
        (stripFirstCoordinate_measurable X hX.1.measurable (τ i.castSucc) (τ i.succ))).aemeasurable
  have hEvalMap :
      (P : Measure Ω).map
          (fun ω i ↦ measureMeasurableSetEvaluationFamily (stripFamily ω i)) =
        Measure.pi
          (fun i : Fin n ↦
            (P : Measure Ω).map
              (fun ω ↦ measureMeasurableSetEvaluationFamily (stripFamily ω i))) := by
    -- Proof comment: the remaining function-valued evaluation owner packages exactly the
    -- coordinate family that generates the Giry sigma-algebra on `Measure NNReal`.
    exact
      (iIndepFun_iff_map_fun_eq_pi_map hEvalMeas).1 <|
        (by
          simpa [stripFamily, measureMeasurableSetEvaluationFamily] using
            stripFirstCoordinate_evalFamily_iIndepFunFin_of_monotoneTimes P ν X hX τ hτ)
  let evalTuple :
      (Fin n → Measure NNReal) → Fin n → MeasurableSetNNReal → ENNReal := fun ξ i ↦
    measureMeasurableSetEvaluationFamily (ξ i)
  have hevalTuple_meas : Measurable evalTuple := by
    -- Proof comment: tuple evaluation is coordinatewise measurable because each coordinate is the
    -- usual measurable-set evaluation map on `Measure NNReal`.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact measurable_measureMeasurableSetEvaluationFamily.comp (measurable_pi_apply i)
  let jointLaw : ProbabilityMeasure (Fin n → Measure NNReal) :=
    ⟨(P : Measure Ω).map (fun ω i ↦ stripFamily ω i),
      Measure.isProbabilityMeasure_map hstripFamily_meas.aemeasurable⟩
  letI : ∀ i : Fin n,
      IsProbabilityMeasure ((P : Measure Ω).map (fun ω ↦ stripFamily ω i)) := fun i ↦
    Measure.isProbabilityMeasure_map (hMeas i)
  let productLaw : ProbabilityMeasure (Fin n → Measure NNReal) :=
    ⟨Measure.pi (fun i : Fin n ↦ (P : Measure Ω).map (fun ω ↦ stripFamily ω i)), inferInstance⟩
  have hMarginalEvalMap (i : Fin n) :
      (P : Measure Ω).map (fun ω ↦ measureMeasurableSetEvaluationFamily (stripFamily ω i)) =
        ((P : Measure Ω).map (fun ω ↦ stripFamily ω i)).map
          measureMeasurableSetEvaluationFamily := by
    -- Proof comment: each one-time evaluation family is the measurable postcomposition of the
    -- corresponding strip random measure.
    symm
    simpa [Function.comp, stripFamily] using
      (Measure.map_map
        (μ := (P : Measure Ω))
        (f := fun ω ↦ stripFamily ω i)
        (g := measureMeasurableSetEvaluationFamily)
        measurable_measureMeasurableSetEvaluationFamily
        (stripFirstCoordinate_measurable X hX.1.measurable (τ i.castSucc) (τ i.succ)))
  have hJointEval :
      (jointLaw : Measure (Fin n → Measure NNReal)).map evalTuple =
        (productLaw : Measure (Fin n → Measure NNReal)).map evalTuple := by
    calc
      (jointLaw : Measure (Fin n → Measure NNReal)).map evalTuple
          = (P : Measure Ω).map
              (fun ω i ↦ measureMeasurableSetEvaluationFamily (stripFamily ω i)) := by
                simpa [jointLaw, evalTuple, stripFamily, Function.comp] using
                  (Measure.map_map
                    (μ := (P : Measure Ω))
                    (f := fun ω i ↦ stripFamily ω i)
                    (g := evalTuple)
                    hevalTuple_meas
                    hstripFamily_meas)
      _ = Measure.pi
            (fun i : Fin n ↦
              (P : Measure Ω).map
                (fun ω ↦ measureMeasurableSetEvaluationFamily (stripFamily ω i))) := hEvalMap
      _ = Measure.pi
            (fun i : Fin n ↦
              ((P : Measure Ω).map (fun ω ↦ stripFamily ω i)).map
                measureMeasurableSetEvaluationFamily) := by
                  congr 1
                  funext i
                  exact hMarginalEvalMap i
      _ = (productLaw : Measure (Fin n → Measure NNReal)).map evalTuple := by
            symm
            simpa [productLaw, evalTuple] using
              (Measure.pi_map_pi
                (μ := fun i : Fin n ↦ (P : Measure Ω).map (fun ω ↦ stripFamily ω i))
                (f := fun _ : Fin n ↦ measureMeasurableSetEvaluationFamily)
                (fun _ : Fin n ↦ measurable_measureMeasurableSetEvaluationFamily.aemeasurable))
  have hLawEq : jointLaw = productLaw := by
    -- Proof comment: the full tuple law on `Fin n → Measure NNReal` is determined by the full
    -- evaluation family because that family generates the ambient measurable space.
    exact
      probabilityMeasureEqOfMapEqOfComapPi
        (Ω' := Fin n → Measure NNReal)
        (ι := Fin n)
        (α := fun _ : Fin n ↦ MeasurableSetNNReal → ENNReal)
        (P := jointLaw)
        (Q := productLaw)
        (X := evalTuple)
        measurePiMeasurableSpace_eq_comap_measureMeasurableSetEvaluationFamily
        hJointEval
  have hMapEq :
      (P : Measure Ω).map (fun ω i ↦ stripFamily ω i) =
        Measure.pi (fun i : Fin n ↦ (P : Measure Ω).map (fun ω ↦ stripFamily ω i)) := by
    simpa [jointLaw, productLaw] using congrArg
      (fun Q : ProbabilityMeasure (Fin n → Measure NNReal) ↦ (Q : Measure (Fin n → Measure NNReal)))
      hLawEq
  -- Proof comment: the tuple law identified above is exactly the finite-index `iIndepFun`
  -- criterion for the strip random measures.
  exact (iIndepFun_iff_map_fun_eq_pi_map hMeas).2 <| by
    simpa [stripFamily] using hMapEq

/-- Helper for Example 24.19: the strip random measures on a monotone natural-time grid form an
independent family. -/
-- TODO: derive the infinite-grid owner from the finite-prefix theorem once that tuple law is
-- stabilized.
private theorem stripFirstCoordinate_iIndepFun_of_monotoneTimes
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    (τ : ℕ → NNReal) (hτ : Monotone τ) :
    iIndepFun
      (fun i ω ↦ stripFirstCoordinate X (τ i) (τ (i + 1)) ω)
      (P : Measure Ω) := by
  -- Proof comment: reduce the nat-indexed family to each finite subset, realize that subset as
  -- a restriction of one anchored finite prefix, and invoke the finite-prefix strip owner.
  refine iIndepFun_iff_finset.2 ?_
  intro s
  by_cases hs : s.Nonempty
  · let N : ℕ := s.max' hs + 1
    let times : Fin (N + 1) → NNReal := fun i ↦ τ i
    have htimes : Monotone times := by
      intro i j hij
      exact hτ (show (i : ℕ) ≤ (j : ℕ) by simpa using hij)
    have hprefix :
        iIndepFun
          (fun i : Fin N ↦ fun ω ↦ stripFirstCoordinate X (times i.castSucc) (times i.succ) ω)
          (P : Measure Ω) := by
      -- Proof comment: this is exactly the finite-prefix theorem specialized to the natural-time
      -- grid restricted to the first `N + 1` endpoints.
      exact stripFirstCoordinate_iIndepFunFin_of_monotoneTimes P ν X hX times htimes
    let g : s → Fin N := fun x ↦
      ⟨x.1, Nat.lt_of_le_of_lt (s.le_max' x.1 x.2) (Nat.lt_succ_self _)⟩
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      exact Fin.ext_iff.mp hab
    -- Proof comment: every requested finite set of strips is obtained by restricting the prefix
    -- family to the corresponding indices.
    simpa [times, g, Finset.restrict] using hprefix.precomp (g := g) hg
  · have hs' : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst hs'
    -- Proof comment: the empty family is independent for trivial reasons.
    simpa using
      (iIndepFun.of_subsingleton
        (μ := (P : Measure Ω))
        (X := fun i ω ↦ stripFirstCoordinate X (τ i) (τ (i + 1)) ω))

/-- Helper for Example 24.19: once the finite-dimensional strip-integral product law is available,
the strip integrals over adjacent monotone time strips form an independent family. -/
theorem stripPoissonIntegral_toNNReal_iIndepFun_of_monotoneTimes
    (P : ProbabilityMeasure Ω) (ν : Measure NNReal)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess (ν.prod nnrealLebesgue) P X)
    (τ : ℕ → NNReal) (hτ : Monotone τ) :
    iIndepFun
      (fun i ω ↦
        ((∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X (τ i) (τ (i + 1)) ω).toNNReal))
      (P : Measure Ω) := by
  -- Route correction: the scalar bounded-evaluation product law is now available via
  -- `stripFirstCoordinate_eval_map_eq_pi_of_monotoneTimes`; the remaining missing owner is the
  -- upgrade from those scalar evaluations to the full `Measure NNReal`-valued strip family.
  let stripMeasure : ℕ → Ω → Measure NNReal := fun i ω ↦
    stripFirstCoordinate X (τ i) (τ (i + 1)) ω
  let integrateStrip : Measure NNReal → NNReal := fun ξ ↦
    (∫⁻ x, (x : ENNReal) ∂ ξ).toNNReal
  have hintegrateStrip : Measurable integrateStrip := by
    -- Proof comment: the strip integral is measurable on `Measure NNReal`, and `toNNReal`
    -- preserves measurability.
    exact ENNReal.measurable_toNNReal.comp
      (Measure.measurable_lintegral measurable_coe_nnreal_ennreal)
  have hstrip :
      iIndepFun stripMeasure (P : Measure Ω) :=
    stripFirstCoordinate_iIndepFun_of_monotoneTimes P ν X hX τ hτ
  -- Proof comment: once the strip random measures are independent, the strip integrals are just a
  -- measurable postcomposition by `integrateStrip`.
  simpa [stripMeasure, integrateStrip] using hstrip.comp (fun _ ↦ integrateStrip) (fun _ ↦ hintegrateStrip)

/-- Helper for Example 24.19: after the strip-integral `iIndepFun` owner is available, the actual
`NNReal` increments form an independent family on every monotone nat grid. -/
theorem poissonPointProcessIntegralProcessNNReal_increment_iIndepFun_of_monotoneTimes
    (μ : ProbabilityMeasure NNReal) (α : NNReal) (ν : Measure NNReal)
    (hν : HasSubordinatorLevyKhinchinRepresentation μ α ν) (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X)
    (τ : ℕ → NNReal) (hτ : Monotone τ) :
    iIndepFun
      (fun i ω ↦
        poissonPointProcessIntegralProcessNNReal X (τ (i + 1)) ω -
          poissonPointProcessIntegralProcessNNReal X (τ i) ω)
      (P : Measure Ω) := by
  have hstrip :
      iIndepFun
        (fun i ω ↦
          ((∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X (τ i) (τ (i + 1)) ω).toNNReal))
        (P : Measure Ω) :=
    stripPoissonIntegral_toNNReal_iIndepFun_of_monotoneTimes P ν X hX τ hτ
  have htransport :
      ∀ i,
        (fun ω ↦
          ((∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X (τ i) (τ (i + 1)) ω).toNNReal)) =ᵐ[
            (P : Measure Ω)]
          (fun ω ↦
            poissonPointProcessIntegralProcessNNReal X (τ (i + 1)) ω -
              poissonPointProcessIntegralProcessNNReal X (τ i) ω) := by
    intro i
    -- Proof comment: each actual increment already agrees almost surely with the corresponding
    -- strip integral on that fixed time window.
    exact Filter.EventuallyEq.symm <|
      (poissonPointProcessIntegralProcessNNReal_increment_ae_eq_stripPoissonIntegral_toNNReal
        μ α ν hν P X hX (hτ (Nat.le_succ i)))
  -- Proof comment: independence is stable under coordinatewise almost-sure replacement.
  exact hstrip.congr htransport

-- Proof sketch: apply the Poisson mapping theorem to the restriction of `X` to
-- `NNReal × Set.Ioc s t`, identify the image measure under the first-coordinate map as
-- `((t - s : NNReal) : ENNReal) • ν`, and then read the source `ENNReal` increment through
-- `toNNReal` on the almost-sure finite event from
-- `poissonPointProcessIntegralProcess_increment_ae_lt_top`.
/-- The increments of the source Poisson integral process, viewed in `NNReal` via the almost-sure
finiteness bridge, have the subordinator Levy-Khinchin law with zero drift and Levy measure
`((t - s : NNReal) : ENNReal) • ν`. -/
theorem poissonPointProcessIntegralProcess_increment_hasLevyKhinchinRepresentation
    (ν : Measure NNReal)
    (hν : ∃ μ : ProbabilityMeasure NNReal, ∃ α : NNReal,
      HasSubordinatorLevyKhinchinRepresentation μ α ν)
    (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) {s t : NNReal}
    (hst : s ≤ t) :
    ∃ μst : ProbabilityMeasure NNReal,
      HasLaw
        (fun ω ↦
          (poissonPointProcessIntegralProcessENNReal X t ω -
            poissonPointProcessIntegralProcessENNReal X s ω).toNNReal)
        (μst : Measure NNReal) (P : Measure Ω) ∧
      HasSubordinatorLevyKhinchinRepresentation μst 0 (((t - s : NNReal) : ENNReal) • ν) := by
  rcases hν with ⟨μ, α, hrep⟩
  let stripIntegralToNNReal : Ω → NNReal := fun ω ↦
    ((∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω).toNNReal)
  have hstripIntegralToNNReal_meas : Measurable stripIntegralToNNReal := by
    have hstrip_meas :
        Measurable (fun ω ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) :=
      (Measure.measurable_lintegral measurable_coe_nnreal_ennreal).comp
        (stripFirstCoordinate_measurable X hX.1.measurable s t)
    -- Proof comment: the strip integral is a measurable `ENNReal` random variable, and
    -- `ENNReal.toNNReal` produces the finite-valued bridge used in the law statement.
    exact ENNReal.measurable_toNNReal.comp hstrip_meas
  let μst : ProbabilityMeasure NNReal :=
    ProbabilityMeasure.map P hstripIntegralToNNReal_meas.aemeasurable
  have hLawStrip :
      HasLaw stripIntegralToNNReal (μst : Measure NNReal) (P : Measure Ω) := by
    refine ⟨hstripIntegralToNNReal_meas.aemeasurable, ?_⟩
    rfl
  have hIncEq :
      (fun ω ↦
        (poissonPointProcessIntegralProcessENNReal X t ω -
          poissonPointProcessIntegralProcessENNReal X s ω).toNNReal) =ᵐ[(P : Measure Ω)]
        stripIntegralToNNReal :=
    poissonPointProcessIntegralProcess_incrementToNNReal_ae_eq_stripPoissonIntegral_toNNReal
      μ α ν hrep P X hX hst
  have hLawInc :
      HasLaw
        (fun ω ↦
          (poissonPointProcessIntegralProcessENNReal X t ω -
            poissonPointProcessIntegralProcessENNReal X s ω).toNNReal)
        (μst : Measure NNReal) (P : Measure Ω) :=
    hLawStrip.congr hIncEq
  have hfinite_ae :
      ∀ᵐ ω ∂(P : Measure Ω),
        (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) < ∞ :=
    stripPoissonIntegral_ae_lt_top μ α ν hrep P X hX hst
  have hfinite_set_meas :
      MeasurableSet
        {ω | (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) < ∞} := by
    have hstrip_meas :
        Measurable (fun ω ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) :=
      (Measure.measurable_lintegral measurable_coe_nnreal_ennreal).comp
        (stripFirstCoordinate_measurable X hX.1.measurable s t)
    exact measurableSet_lt hstrip_meas measurable_const
  have hfinite :
      (P : Measure Ω)
        {ω | (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω) < ∞} = 1 :=
    (mem_ae_iff_prob_eq_one hfinite_set_meas).1 hfinite_ae
  refine ⟨μst, hLawInc, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: the scaled Lévy measure keeps zero mass at the origin because the base Lévy
    -- measure already satisfies that condition.
    simp [hrep.1]
  · -- Proof comment: the truncated first-moment condition is preserved under nonnegative scalar
    -- multiplication of the Lévy measure.
    exact hrep.2.1.smul_measure (by simp)
  · intro u
    let stripExponent : ℝ := ∫ x : NNReal,
      (1 - Real.exp (-((u : ℝ) * (x : ℝ)))) ∂ ((((t - s : NNReal) : ENNReal) • ν))
    have hkernel_meas :
        AEStronglyMeasurable
          (fun x : NNReal ↦ Real.exp (-((u : ℝ) * (x : ℝ))))
          (μst : Measure NNReal) := by
      have hmeas : Measurable (fun x : NNReal ↦ Real.exp (-((u : ℝ) * (x : ℝ)))) := by
        fun_prop
      exact hmeas.aestronglyMeasurable
    have hLaplaceMap :
        ∫ x : NNReal, Real.exp (-((u : ℝ) * (x : ℝ))) ∂(μst : Measure NNReal) =
          ∫ ω, Real.exp (-((u : ℝ) * (stripIntegralToNNReal ω : ℝ))) ∂(P : Measure Ω) := by
      symm
      exact hLawStrip.integral_comp hkernel_meas
    have hLaplaceStrip :
        ∫ x : NNReal, Real.exp (-((u : ℝ) * (x : ℝ))) ∂(μst : Measure NNReal) =
          Real.exp (-stripExponent) := by
      calc
        ∫ x : NNReal, Real.exp (-((u : ℝ) * (x : ℝ))) ∂(μst : Measure NNReal)
            = ∫ ω, Real.exp (-((u : ℝ) * (stripIntegralToNNReal ω : ℝ))) ∂(P : Measure Ω) :=
              hLaplaceMap
        _ = ∫ ω,
              Real.exp (-((u : ℝ) *
                (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω).toReal)) ∂
              (P : Measure Ω) := by
                simpa [stripIntegralToNNReal, ENNReal.coe_toNNReal_eq_toReal]
        _ = Real.exp
              (∫ x : NNReal, (Real.exp (-((u : ℝ) * (x : ℝ))) - 1) ∂
                ((((t - s : NNReal) : ENNReal) • ν))) := by
                  simpa using stripPoissonIntegral_laplaceFormula P ν X hX hst hfinite u
        _ = Real.exp (-stripExponent) := by
              congr 1
              calc
                ∫ x : NNReal, (Real.exp (-((u : ℝ) * (x : ℝ))) - 1) ∂
                    ((((t - s : NNReal) : ENNReal) • ν))
                    = ∫ x : NNReal, -(1 - Real.exp (-((u : ℝ) * (x : ℝ)))) ∂
                        ((((t - s : NNReal) : ENNReal) • ν)) := by
                          refine integral_congr_ae <| Filter.Eventually.of_forall fun x ↦ ?_
                          ring
                _ = -stripExponent := by
                      rw [integral_neg]
    -- Proof comment: the strip Laplace formula is now expressed exactly as `exp (-stripExponent)`,
    -- so one `log` rewrite yields the required Bernstein identity with zero drift.
    rw [MeasureTheory.FiniteMeasure.logLaplaceTransform, hLaplaceStrip, Real.log_exp]
    simp [stripExponent]

-- Proof sketch: for disjoint time intervals, the restrictions of the Poisson point process to the
-- corresponding strips in `NNReal × NNReal` are independent, giving independent increments.
-- The strip `(r, r + s]` has intensity induced by restricting `nnrealLebesgue` to `Set.Ioc r
-- (r + s)`, whose first-coordinate image depends only on `s`, so the increment law is
-- translation invariant. The source-facing process is the finite-valued `NNReal` companion under
-- the explicit Lévy-measure hypothesis on `ν`; the underlying `ENNReal` integral remains an
-- internal bridge for almost-sure finiteness and path-regularity statements.
/-- Helper for Example 24.19: the finite-valued Poisson integral process has stationary increment
laws because equal-length time strips have the same strip-integral law. -/
theorem poissonPointProcessIntegralProcess_hasStationaryIncrementLaws
    (ν : Measure NNReal)
    (hν : ∃ μ : ProbabilityMeasure NNReal, ∃ α : NNReal,
      HasSubordinatorLevyKhinchinRepresentation μ α ν)
    (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) :
    HasStationaryIncrementLaws (poissonPointProcessIntegralProcessNNReal X)
      (P : Measure Ω) := by
  rcases hν with ⟨μ, α, hrep⟩
  intro r s t
  let left : Ω → NNReal := fun ω ↦
    poissonPointProcessIntegralProcessNNReal X ((s + t) + r) ω -
      poissonPointProcessIntegralProcessNNReal X (t + r) ω
  let leftStrip : Ω → NNReal := fun ω ↦
    ((∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X (t + r) ((s + t) + r) ω).toNNReal)
  let right : Ω → NNReal := fun ω ↦
    poissonPointProcessIntegralProcessNNReal X (s + r) ω -
      poissonPointProcessIntegralProcessNNReal X r ω
  let rightStrip : Ω → NNReal := fun ω ↦
    ((∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X r (s + r) ω).toNNReal)
  have hprocNN_meas : ∀ u : NNReal, Measurable (poissonPointProcessIntegralProcessNNReal X u) := by
    intro u
    have hprocENN_meas : Measurable (poissonPointProcessIntegralProcessENNReal X u) := by
      unfold poissonPointProcessIntegralProcessENNReal
      exact
        ((Measure.measurable_lintegral
            ((measurable_coe_nnreal_ennreal.comp measurable_fst).mul
              ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd))).comp
          hX.1.measurable)
    -- Proof comment: apply `ENNReal.toNNReal` only after recording measurability of the source
    -- extended integral.
    exact ENNReal.measurable_toNNReal.comp hprocENN_meas
  have hleft_meas : AEMeasurable left (P : Measure Ω) := by
    simpa [left] using ((hprocNN_meas _).sub (hprocNN_meas _)).aemeasurable
  have hright_meas : AEMeasurable right (P : Measure Ω) := by
    simpa [right] using ((hprocNN_meas _).sub (hprocNN_meas _)).aemeasurable
  have hstLeftBase : t + r ≤ (s + t) + r := by
    have hst' : t ≤ s + t := by
      simpa [add_comm] using (le_add_of_nonneg_left s.2 : t ≤ s + t)
    simpa [add_assoc] using add_le_add_right hst' r
  have hstRightBase : r ≤ s + r := by
    simpa [add_comm] using (le_add_of_nonneg_left s.2 : r ≤ s + r)
  have hleft_eq : left =ᵐ[(P : Measure Ω)] leftStrip := by
    simpa [left, leftStrip] using
      poissonPointProcessIntegralProcessNNReal_increment_ae_eq_stripPoissonIntegral_toNNReal
        μ α ν hrep P X hX hstLeftBase
  have hright_eq : right =ᵐ[(P : Measure Ω)] rightStrip := by
    simpa [right, rightStrip] using
      poissonPointProcessIntegralProcessNNReal_increment_ae_eq_stripPoissonIntegral_toNNReal
        μ α ν hrep P X hX hstRightBase
  have hstrip_id :
      IdentDistrib
        (fun ω ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X (t + r) ((s + t) + r) ω)
        (fun ω ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X r (s + r) ω)
        (P : Measure Ω) (P : Measure Ω) := by
    refine stripPoissonIntegral_identDistrib_of_sameLength P ν X hX hstLeftBase hstRightBase ?_
    calc
      ((s + t) + r) - (t + r) = s := by
        apply tsub_eq_of_eq_add_rev
        abel
      _ = (s + r) - r := by
        symm
        apply tsub_eq_of_eq_add_rev
        abel
  have hstrip_toNNReal :
      IdentDistrib leftStrip rightStrip (P : Measure Ω) (P : Measure Ω) := by
    simpa [leftStrip, rightStrip, Function.comp] using
      hstrip_id.comp ENNReal.measurable_toNNReal
  exact
    (IdentDistrib.of_ae_eq hleft_meas hleft_eq).trans <|
      hstrip_toNNReal.trans <|
        (IdentDistrib.of_ae_eq hright_meas hright_eq).symm

/-- Example 24.19: if `X` is a Poisson point process with intensity `ν ⊗ λ` and `ν` is the Lévy
measure of a subordinator, then the finite-valued Poisson stochastic integral process has
stationary independent increments. -/
theorem poissonPointProcessIntegralProcess_hasStationaryIndependentIncrements
    (ν : Measure NNReal)
    (hν : ∃ μ : ProbabilityMeasure NNReal, ∃ α : NNReal,
      HasSubordinatorLevyKhinchinRepresentation μ α ν)
    (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) :
    HasStationaryIndependentIncrements (poissonPointProcessIntegralProcessNNReal X)
      (P : Measure Ω) := by
  rcases hν with ⟨μ, α, hrep⟩
  refine ⟨?_, poissonPointProcessIntegralProcess_hasStationaryIncrementLaws ν ⟨μ, α, hrep⟩ P X hX⟩
  refine ProbabilityTheory.HasIndepIncrements.of_nat ?_
  intro t ht _
  -- Proof comment: the independent-increments owner reduces to monotone nat grids, and on each
  -- such grid the actual increments are the a.e. transport of the strip-integral family.
  exact
    poissonPointProcessIntegralProcessNNReal_increment_iIndepFun_of_monotoneTimes
      μ α ν hrep P X hX t ht

/-- Helper for Example 24.19: the pathwise weighted time measure records the `x`-mass of the
space-time points by their time coordinate. -/
private def weightedTimeMeasure
    (X : Ω → Measure (NNReal × NNReal)) (ω : Ω) : Measure NNReal :=
  Measure.map Prod.snd ((X ω).withDensity fun z ↦ (z.1 : ℝ≥0∞))

/-- Helper for Example 24.19: the weighted time measure of `(s, t]` is exactly the strip
integral over that time window. -/
private theorem weightedTimeMeasure_Ioc_eq_stripIntegral
    (X : Ω → Measure (NNReal × NNReal)) (ω : Ω) (s t : NNReal) :
    weightedTimeMeasure X ω (Set.Ioc s t) =
      ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω := by
  -- Proof comment: rewrite the weighted pushforward mass as the original weighted integral over
  -- the time strip, then identify that with the established strip-integral formula.
  calc
    weightedTimeMeasure X ω (Set.Ioc s t)
        = ∫⁻ z in (Set.univ : Set NNReal) ×ˢ Set.Ioc s t, (z.1 : ENNReal) ∂ X ω := by
            rw [weightedTimeMeasure, Measure.map_apply measurable_snd measurableSet_Ioc]
            have hpre :
                Prod.snd ⁻¹' Set.Ioc s t = (Set.univ : Set NNReal) ×ˢ Set.Ioc s t := by
              ext z
              simp
            rw [hpre]
            exact MeasureTheory.withDensity_apply _ (MeasurableSet.univ.prod measurableSet_Ioc)
    _ =
        ∫⁻ z : NNReal × NNReal,
          (z.1 : ENNReal) *
            Set.indicator (Set.Ioc s t) (fun _ ↦ (1 : ENNReal)) z.2 ∂ X ω := by
              rw [← MeasureTheory.lintegral_indicator
                (MeasurableSet.univ.prod measurableSet_Ioc)]
              refine lintegral_congr_ae (Filter.Eventually.of_forall fun z ↦ ?_)
              simp [Set.indicator]
    _ = ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X s t ω := by
          symm
          exact poissonPointProcessIntegralProcessENNReal_eq_lintegral_strip X s t ω

/-- Helper for Example 24.19: a finite horizon above `t` forces the weighted strip tail to vanish
when the right endpoint decreases to `t`. -/
private theorem poissonPointProcessIntegralProcessENNReal_stripTail_tendstoZero_of_exists_lt_top
    (X : Ω → Measure (NNReal × NNReal)) {ω : Ω} {t : NNReal}
    (hfinite : ∃ u : NNReal, t < u ∧ poissonPointProcessIntegralProcessENNReal X u ω < ∞) :
    Filter.Tendsto
      (fun s : NNReal ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X t s ω)
      (nhdsWithin t (Set.Ioi t)) (nhds 0) := by
  rcases hfinite with ⟨u, htu, hu_fin⟩
  let ρ : Measure NNReal := weightedTimeMeasure X ω
  have hρ_finite : ρ (Set.Ioc t u) < ∞ := by
    have htail_le :
        ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X t u ω ≤
          poissonPointProcessIntegralProcessENNReal X u ω := by
      calc
        ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X t u ω
            ≤ poissonPointProcessIntegralProcessENNReal X t ω +
                ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X t u ω := by
                  exact le_add_of_nonneg_left bot_le
        _ = poissonPointProcessIntegralProcessENNReal X u ω := by
              symm
              exact
                poissonPointProcessIntegralProcessENNReal_eq_add_stripIntegral X
                  (le_of_lt htu) ω
    have htail_fin :
        ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X t u ω < ∞ :=
      lt_of_le_of_lt htail_le hu_fin
    simpa [ρ] using
      (weightedTimeMeasure_Ioc_eq_stripIntegral X ω t u).trans_lt htail_fin
  have htail_sub :
      Filter.Tendsto
        (fun s : Set.Ioi t ↦ ρ (Set.Ioc t (s : NNReal)))
        Filter.atBot
        (nhds (ρ (⋂ s : Set.Ioi t, Set.Ioc t (s : NNReal)))) := by
    refine MeasureTheory.tendsto_measure_iInter_atBot ?_ ?_ ?_
    · intro s
      exact measurableSet_Ioc.nullMeasurableSet
    · intro a b hab
      exact Set.Ioc_subset_Ioc_right hab
    · exact ⟨⟨u, htu⟩, ne_of_lt hρ_finite⟩
  have hInter_empty : (⋂ s : Set.Ioi t, Set.Ioc t (s : NNReal)) = (∅ : Set NNReal) := by
    ext z
    constructor
    · intro hz
      simp only [Set.mem_iInter, Set.mem_Ioc] at hz
      have htz : t < z := (hz ⟨u, htu⟩).1
      obtain ⟨s, hts, hsz⟩ := exists_between htz
      exact (not_le_of_gt hsz) (hz ⟨s, hts⟩).2
    · intro hz
      simp at hz
  have htail_right :
      Filter.Tendsto (fun s : NNReal ↦ ρ (Set.Ioc t s)) (nhdsWithin t (Set.Ioi t)) (nhds 0) := by
    rw [hInter_empty, measure_empty] at htail_sub
    exact (tendsto_comp_coe_Ioi_atBot (f := fun s : NNReal ↦ ρ (Set.Ioc t s)) (a := t)).1
      htail_sub
  -- Proof comment: replace the weighted time-measure tail by the strip integral itself.
  refine Filter.Tendsto.congr' ?_ htail_right
  exact Filter.Eventually.of_forall fun s ↦
    weightedTimeMeasure_Ioc_eq_stripIntegral X ω t s

/-- Helper for Example 24.19: a finite horizon above `t` should force right continuity of the
extended strip-integral process at `t`. -/
theorem poissonPointProcessIntegralProcessENNReal_rightContinuous_of_exists_lt_top
    (X : Ω → Measure (NNReal × NNReal)) {ω : Ω} {t : NNReal}
    (hfinite : ∃ u : NNReal, t < u ∧ poissonPointProcessIntegralProcessENNReal X u ω < ∞) :
    ContinuousWithinAt
      (fun s : NNReal ↦ poissonPointProcessIntegralProcessENNReal X s ω)
      (Set.Ici t) t := by
  -- Route correction: the obsolete local-finiteness helper had the wrong interface. The usable
  -- pathwise owner is a finite-horizon witness above `t`, from which the shrinking strip tail
  -- tends to `0`.
  rw [← continuousWithinAt_Ioi_iff_Ici]
  have htail_zero :
      (∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X t t ω) = 0 := by
    -- Proof comment: the degenerate strip `(t, t]` is empty.
    rw [poissonPointProcessIntegralProcessENNReal_eq_lintegral_strip X t t ω]
    simp
  have htail :
      Filter.Tendsto
        (fun s : NNReal ↦ ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X t s ω)
        (nhdsWithin t (Set.Ioi t)) (nhds 0) :=
    poissonPointProcessIntegralProcessENNReal_stripTail_tendstoZero_of_exists_lt_top X hfinite
  have hsum :
      ContinuousWithinAt
        (fun s : NNReal ↦
          poissonPointProcessIntegralProcessENNReal X t ω +
            ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X t s ω)
        (Set.Ioi t) t := by
    -- Proof comment: add the constant left-endpoint mass back to the vanishing tail.
    simpa [ContinuousWithinAt, htail_zero] using
      htail.const_add (poissonPointProcessIntegralProcessENNReal X t ω)
  have hEq :
      (fun s : NNReal ↦ poissonPointProcessIntegralProcessENNReal X s ω) =ᶠ[
        nhdsWithin t (Set.Ioi t)]
        (fun s : NNReal ↦
          poissonPointProcessIntegralProcessENNReal X t ω +
            ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X t s ω) := by
    refine Filter.mem_of_superset self_mem_nhdsWithin ?_
    intro s hs
    exact poissonPointProcessIntegralProcessENNReal_eq_add_stripIntegral X hs.le ω
  have hEq_t :
      poissonPointProcessIntegralProcessENNReal X t ω =
        poissonPointProcessIntegralProcessENNReal X t ω +
          ∫⁻ x, (x : ENNReal) ∂ stripFirstCoordinate X t t ω := by
    simpa [htail_zero]
  exact hsum.congr_of_eventuallyEq hEq hEq_t

/-- Under the source Poisson point-process owner and the source Lévy-measure hypothesis, the
finite-valued Poisson integral process has almost surely right-continuous sample paths. -/
theorem poissonPointProcessIntegralProcess_hasRightContinuousPaths
    (ν : Measure NNReal)
    (hν : ∃ μ : ProbabilityMeasure NNReal, ∃ α : NNReal,
      HasSubordinatorLevyKhinchinRepresentation μ α ν)
    (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) :
    ∀ᵐ ω ∂(P : Measure Ω), ∀ t : NNReal,
      ContinuousWithinAt
        (fun s : NNReal ↦ poissonPointProcessIntegralProcessNNReal X s ω)
        (Set.Ici t) t := by
  rcases hν with ⟨μ, α, hrep⟩
  have hcoe :
      ∀ᵐ ω ∂(P : Measure Ω), ∀ t : NNReal,
        (poissonPointProcessIntegralProcessNNReal X t ω : ENNReal) =
          poissonPointProcessIntegralProcessENNReal X t ω :=
    poissonPointProcessIntegralProcessNNReal_ae_coe_eq μ α ν hrep P X hX
  filter_upwards [hcoe] with ω hω t
  have hfinite :
      ∃ u : NNReal, t < u ∧ poissonPointProcessIntegralProcessENNReal X u ω < ∞ := by
    refine ⟨t + 1, by simpa, ?_⟩
    -- Proof comment: on the full-measure coercion event, every deterministic time value of the
    -- `ENNReal` process is already finite.
    rw [← hω (t + 1)]
    exact ENNReal.coe_lt_top
  have hcontENN :
      ContinuousWithinAt
        (fun s : NNReal ↦ poissonPointProcessIntegralProcessENNReal X s ω)
        (Set.Ici t) t :=
    poissonPointProcessIntegralProcessENNReal_rightContinuous_of_exists_lt_top X hfinite
  have hfinite_t : poissonPointProcessIntegralProcessENNReal X t ω ≠ ∞ := by
    rw [← hω t]
    exact ENNReal.coe_ne_top
  have hcontNN :
      ContinuousWithinAt
        (fun s : NNReal ↦ (poissonPointProcessIntegralProcessENNReal X s ω).toNNReal)
        (Set.Ici t) t := by
    -- Proof comment: `ENNReal.toNNReal` is continuous at finite targets, so the `NNReal`
    -- companion inherits right continuity from the source `ENNReal` path.
    simpa [ContinuousWithinAt, Function.comp] using
      (ENNReal.tendsto_toNNReal hfinite_t).comp hcontENN
  simpa [poissonPointProcessIntegralProcessNNReal] using hcontNN

/-- Helper for Example 24.19: if every path admits a finite horizon above every time, then the
extended Poisson integral process has right-continuous sample paths. -/
theorem poissonPointProcessIntegralProcess_hasRightContinuousPaths_of_pathwiseLocallyFinite
    (ν : Measure NNReal) (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X)
    (hfinitePath :
      ∀ ω : Ω, ∀ t : NNReal,
        ∃ u : NNReal, t < u ∧ poissonPointProcessIntegralProcessENNReal X u ω < ∞) :
    HasRightContinuousPaths (poissonPointProcessIntegralProcessENNReal X) :=
by
  intro ω t
  -- Proof comment: this helper is now the direct pathwise wrapper around the finite-horizon
  -- continuity owner proved above.
  exact
    poissonPointProcessIntegralProcessENNReal_rightContinuous_of_exists_lt_top X
      (hfinitePath ω t)

-- Proof sketch: on the almost-sure finite event coming from the Lévy-measure hypothesis, the
-- coercion bridge identifies the `NNReal` process with the monotone `ENNReal` integral process.
/-- Under the source Lévy-measure hypothesis, the finite-valued Poisson integral process has
almost surely monotone increasing sample paths. -/
theorem poissonPointProcessIntegralProcess_monotone
    (ν : Measure NNReal)
    (hν : ∃ μ : ProbabilityMeasure NNReal, ∃ α : NNReal,
      HasSubordinatorLevyKhinchinRepresentation μ α ν)
    (P : ProbabilityMeasure Ω)
    (X : Ω → Measure (NNReal × NNReal))
    (hX : ProbabilityTheory.IsPoissonPointProcess
      (ν.prod nnrealLebesgue) P X) :
    ∀ᵐ ω ∂(P : Measure Ω),
      Monotone (fun t : NNReal ↦ poissonPointProcessIntegralProcessNNReal X t ω) :=
by
  rcases hν with ⟨μ, α, hrep⟩
  have hcoe :
      ∀ᵐ ω ∂(P : Measure Ω), ∀ t : NNReal,
        (poissonPointProcessIntegralProcessNNReal X t ω : ENNReal) =
          poissonPointProcessIntegralProcessENNReal X t ω :=
    poissonPointProcessIntegralProcessNNReal_ae_coe_eq μ α ν hrep P X hX
  filter_upwards [hcoe] with ω hω
  intro s t hst
  exact ENNReal.coe_le_coe.mp <| by
    rw [hω s, hω t]
    -- Proof comment: enlarging the time strip from `(0, s]` to `(0, t]` only increases the
    -- pointwise indicator in the defining nonnegative integral.
    unfold poissonPointProcessIntegralProcessENNReal
    refine lintegral_mono fun z ↦ ?_
    have hsubset : Set.Ioc (0 : NNReal) s ⊆ Set.Ioc (0 : NNReal) t := by
      intro x hx
      exact ⟨hx.1, le_trans hx.2 hst⟩
    have hindicator :
        Set.indicator (Set.Ioc (0 : NNReal) s) (fun _ ↦ (1 : ENNReal)) z.2 ≤
          Set.indicator (Set.Ioc (0 : NNReal) t) (fun _ ↦ (1 : ENNReal)) z.2 := by
      by_cases hz_s : z.2 ∈ Set.Ioc (0 : NNReal) s
      · have hz_t : z.2 ∈ Set.Ioc (0 : NNReal) t := hsubset hz_s
        simp [Set.indicator, hz_s, hz_t]
      · by_cases hz_t : z.2 ∈ Set.Ioc (0 : NNReal) t
        · simp [Set.indicator, hz_s, hz_t]
        · simp [Set.indicator, hz_s, hz_t]
    simpa [mul_comm] using mul_le_mul_right' hindicator (z.1 : ENNReal)

end ProbabilityTheory
