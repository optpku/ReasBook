/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap06.Theorem_6_17
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

universe u v

section LawLevel

variable {E : Type u} [MeasurableSpace E]

/- Exercise 13.2.15 is `source-facing`: the textbook assumption is a tail-first-moment condition
for one fixed observable `f` tested against a sequence of laws `μₙ`. The `core/canonical` owner
used downstream is `MeasureTheory.UniformIntegrable` on a single measure space. The local
predicate below is therefore the law-level `bridge/view`, while the bridge theorem records the
canonical reformulation through any common-space realization with the same one-dimensional laws. -/
/-- A real-valued function is uniformly integrable with respect to a sequence of probability
measures when the supremum of its tail first moments tends to `0`, written in the textbook form as
an infimum over positive cutoffs. -/
def uniformlyIntegrableWithRespectToProbabilitySequence
    (f : E → ℝ) (μs : ℕ → ProbabilityMeasure E) : Prop :=
  (⨅ a : {a : ℝ // 0 < a},
      ⨆ n : ℕ,
        ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)) = 0

/-- Helper for Exercise 13.2.15: the source `iInf/iSup` tail condition is equivalent to the usual
`ε`-tail formulation. -/
private theorem uniformlyIntegrableWithRespectToProbabilitySequence_iff_forall_epsilon
    {f : E → ℝ} {μs : ℕ → ProbabilityMeasure E} :
    uniformlyIntegrableWithRespectToProbabilitySequence f μs ↔
      ∀ ε : ℝ, 0 < ε → ∃ a : {a : ℝ // 0 < a},
        ∀ n, ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)
          ≤ ENNReal.ofReal ε := by
  constructor
  · intro hUI ε hε
    -- Rewrite the infimum criterion as a vanishing `sInf`, then read off one cutoff whose tail
    -- `iSup` is already below `ε`.
    rw [uniformlyIntegrableWithRespectToProbabilitySequence] at hUI
    change sInf (Set.range fun a : {a : ℝ // 0 < a} ↦
      ⨆ n : ℕ, ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)) = 0 at hUI
    rw [sInfRange_eq_zero_iff_forall_epsilon] at hUI
    obtain ⟨a, ha⟩ := hUI ε hε
    refine ⟨a, fun n ↦ ?_⟩
    exact le_of_lt <|
      lt_of_le_of_lt
        (le_iSup (fun n ↦ ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x|
          ∂(μs n : Measure E)) n)
        ha
  · intro hε
    -- Conversely, a pointwise `≤ ε / 2` estimate forces the `iSup` to be strictly below `ε`.
    rw [uniformlyIntegrableWithRespectToProbabilitySequence]
    change sInf (Set.range fun a : {a : ℝ // 0 < a} ↦
      ⨆ n : ℕ, ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)) = 0
    rw [sInfRange_eq_zero_iff_forall_epsilon]
    intro ε hε_pos
    obtain ⟨a, ha⟩ := hε (ε / 2) (half_pos hε_pos)
    refine ⟨a, lt_of_le_of_lt (iSup_le fun n ↦ ha n) ?_⟩
    simpa using (ENNReal.ofReal_lt_ofReal_iff hε_pos).2 (by linarith : ε / 2 < ε)

/-- Helper for Exercise 13.2.15: the strict-tail absolute-value integrand on `ℝ` is measurable. -/
private lemma measurableStrictTailAbsIndicator (a : ℝ) :
    Measurable (fun y : ℝ ↦ Set.indicator {t : ℝ | a < |t|} (fun t ↦ ENNReal.ofReal |t|) y) := by
  -- The tail set is measurable, and so is the absolute-value weight.
  exact Measurable.indicator (ENNReal.measurable_ofReal.comp continuous_abs.measurable) <|
    measurableSet_lt measurable_const continuous_abs.measurable

/-- Helper for Exercise 13.2.15: a restricted strict-tail integral can be rewritten as the
lintegral of the codomain strict-tail indicator. -/
private lemma lintegral_strictTailAbsIndicator_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : AEMeasurable g μ) (a : ℝ) :
    ∫⁻ x in {x | a < |g x|}, ENNReal.ofReal |g x| ∂μ =
      ∫⁻ x, Set.indicator {t : ℝ | a < |t|} (fun t ↦ ENNReal.ofReal |t|) (g x) ∂μ := by
  -- Replace the restricted integral by the corresponding indicator integrand on the full space.
  have hs : NullMeasurableSet {x | a < |g x|} μ := by
    simpa [Real.norm_eq_abs] using hg.norm.nullMeasurableSet_preimage measurableSet_Ioi
  rw [← lintegral_indicator₀ hs]
  refine lintegral_congr_ae ?_
  filter_upwards with x
  simp [Set.indicator]

/-- Helper for Exercise 13.2.15: the owner cutoff seminorm at exponent `1` is the lintegral of
the corresponding non-strict tail indicator. -/
private lemma eLpNorm_indicator_ge_eq_lintegral_nonStrictTailAbsIndicator
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ} (C : ℝ≥0) :
    eLpNorm ({x | C ≤ ‖g x‖₊}.indicator g) 1 μ =
      ∫⁻ x, Set.indicator {t : ℝ | (C : ℝ) ≤ |t|} (fun t ↦ ENNReal.ofReal |t|) (g x) ∂μ := by
  -- Expand the `L¹` seminorm and simplify the cutoff indicator pointwise.
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
  refine lintegral_congr_ae ?_
  filter_upwards with x
  by_cases hx : (C : ℝ) ≤ |g x|
  · have hx' : C ≤ ‖g x‖₊ := by simpa using hx
    simpa [hx, hx', Real.enorm_eq_ofReal_abs]
  · have hx' : ¬ C ≤ ‖g x‖₊ := by simpa using hx
    simpa [hx, hx']

-- Proof sketch: compare the tail integrals under `μₙ` with those of any common-space real
-- sequence having the same one-dimensional laws, using `IdentDistrib` to transport the relevant
-- truncated first moments. In the exercise proof, the needed realization comes from a Skorohod
-- coupling of the pushforward laws, but that auxiliary convergence package is not part of the
-- bridge API itself.
/-- The law-level tail criterion for `f` along `μₙ` is equivalent to the canonical owner
predicate `MeasureTheory.UniformIntegrable` for any real sequence with the same one-dimensional
laws. -/
theorem uniformlyIntegrableWithRespectToProbabilitySequence_iff_uniformIntegrable_of_identDistrib
    {Ω : Type v} [MeasurableSpace Ω] {P : ProbabilityMeasure Ω}
    {f : E → ℝ} {μs : ℕ → ProbabilityMeasure E} {Ys : ℕ → Ω → ℝ}
    (hYs : ∀ n, IdentDistrib (Ys n) f (P : Measure Ω) (μs n : Measure E)) :
    uniformlyIntegrableWithRespectToProbabilitySequence f μs ↔
      UniformIntegrable Ys 1 (P : Measure Ω) := by
  constructor
  · intro hUI
    rw [MeasureTheory.uniformIntegrable_iff le_rfl ENNReal.one_ne_top]
    refine ⟨fun n ↦ (hYs n).aestronglyMeasurable_fst, ?_⟩
    -- Convert the source strict-tail control into the owner cutoff control by shifting the cutoff
    -- by `1` and transporting the tail integrals through `IdentDistrib`.
    intro ε hε
    obtain ⟨a, ha⟩ :=
      (uniformlyIntegrableWithRespectToProbabilitySequence_iff_forall_epsilon).1 hUI ε hε
    let C : ℝ≥0 := ⟨a.1 + 1, by linarith [a.2]⟩
    refine ⟨C, fun n ↦ ?_⟩
    have htransport :
        ∫⁻ ω, Set.indicator {t : ℝ | a.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (Ys n ω)
            ∂(P : Measure Ω) =
          ∫⁻ x, Set.indicator {t : ℝ | a.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
            ∂(μs n : Measure E) := by
      exact ((hYs n).comp (measurableStrictTailAbsIndicator a.1)).lintegral_eq
    calc
      eLpNorm ({ω | C ≤ ‖Ys n ω‖₊}.indicator (Ys n)) 1 (P : Measure Ω) =
          ∫⁻ ω, Set.indicator {t : ℝ | (C : ℝ) ≤ |t|} (fun t ↦ ENNReal.ofReal |t|)
            (Ys n ω) ∂(P : Measure Ω) := by
              exact eLpNorm_indicator_ge_eq_lintegral_nonStrictTailAbsIndicator (μ := (P : Measure Ω))
                (g := Ys n) C
      _ ≤ ∫⁻ ω, Set.indicator {t : ℝ | a.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (Ys n ω)
            ∂(P : Measure Ω) := by
              refine lintegral_mono fun ω ↦ ?_
              by_cases hω : (C : ℝ) ≤ |Ys n ω|
              · have hω' : a.1 < |Ys n ω| := by
                  have : a.1 + 1 ≤ |Ys n ω| := by simpa [C] using hω
                  linarith
                simpa [hω, hω']
              · simp [hω]
      _ = ∫⁻ x, Set.indicator {t : ℝ | a.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
            ∂(μs n : Measure E) := htransport
      _ = ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E) := by
            symm
            exact lintegral_strictTailAbsIndicator_eq (hYs n).aemeasurable_snd a.1
      _ ≤ ENNReal.ofReal ε := ha n
  · intro hUI
    refine (uniformlyIntegrableWithRespectToProbabilitySequence_iff_forall_epsilon).2 ?_
    intro ε hε
    -- Use the owner cutoff at size `C`, then tighten it to the source strict cutoff `C + 1`.
    obtain ⟨C, hC⟩ := hUI.spec one_ne_zero ENNReal.one_ne_top (ε := ε / 2) (half_pos hε)
    let a : {a : ℝ // 0 < a} := ⟨(C : ℝ) + 1, by positivity⟩
    refine ⟨a, fun n ↦ ?_⟩
    have htransport :
        ∫⁻ ω, Set.indicator {t : ℝ | a.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (Ys n ω)
            ∂(P : Measure Ω) =
          ∫⁻ x, Set.indicator {t : ℝ | a.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
            ∂(μs n : Measure E) := by
      exact ((hYs n).comp (measurableStrictTailAbsIndicator a.1)).lintegral_eq
    calc
      ∫⁻ x in {x | a.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E) =
          ∫⁻ x, Set.indicator {t : ℝ | a.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
            ∂(μs n : Measure E) := by
              exact lintegral_strictTailAbsIndicator_eq (hYs n).aemeasurable_snd a.1
      _ = ∫⁻ ω, Set.indicator {t : ℝ | a.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (Ys n ω)
            ∂(P : Measure Ω) := htransport.symm
      _ ≤ ∫⁻ ω, Set.indicator {t : ℝ | (C : ℝ) ≤ |t|} (fun t ↦ ENNReal.ofReal |t|)
            (Ys n ω) ∂(P : Measure Ω) := by
              refine lintegral_mono fun ω ↦ ?_
              by_cases hω : a.1 < |Ys n ω|
              · have hω' : (C : ℝ) ≤ |Ys n ω| := by
                  have : (C : ℝ) + 1 < |Ys n ω| := hω
                  linarith
                simp [hω, hω', a]
              · simp [hω]
      _ = eLpNorm ({ω | C ≤ ‖Ys n ω‖₊}.indicator (Ys n)) 1 (P : Measure Ω) := by
            symm
            exact eLpNorm_indicator_ge_eq_lintegral_nonStrictTailAbsIndicator (μ := (P : Measure Ω))
              (g := Ys n) C
      _ ≤ ENNReal.ofReal (ε / 2) := hC n
      _ ≤ ENNReal.ofReal ε := by
            exact le_of_lt <|
              (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith : ε / 2 < ε)

end LawLevel

section

variable {E : Type u} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Helper for Exercise 13.2.15: larger strict-tail cutoffs produce smaller indicator
integrands. -/
private lemma strictTailAbsIndicator_mono {a b y : ℝ} (hab : a ≤ b) :
    Set.indicator {t : ℝ | b < |t|} (fun t ↦ ENNReal.ofReal |t|) y ≤
      Set.indicator {t : ℝ | a < |t|} (fun t ↦ ENNReal.ofReal |t|) y := by
  -- Proof comment: a larger cutoff can only shrink the strict-tail set, so the indicator-weighted
  -- absolute value decreases pointwise.
  by_cases hy : b < |y|
  · have hy' : a < |y| := lt_of_le_of_lt hab hy
    simp [hy, hy']
  · simp [hy]

/-- Helper for Exercise 13.2.15: the pointwise absolute value splits into a bounded part and a
strict-tail part. -/
private lemma abs_le_cutoff_add_strictTailAbsIndicator {A y : ℝ} (hA : 0 ≤ A) :
    |y| ≤ A + Set.indicator {t : ℝ | A < |t|} (fun t ↦ |t|) y := by
  -- Outside the strict tail we use `|y| ≤ A`; on the tail the additional indicator term absorbs
  -- the remaining mass.
  by_cases hy : A < |y|
  · have : |y| ≤ |y| + A := by linarith
    simpa [hy, add_comm] using this
  · simpa [hy] using le_of_not_gt hy

/-- Helper for Exercise 13.2.15: the real-valued strict-tail absolute-value observable is
measurable. -/
private lemma measurableRealStrictTailAbsIndicator (a : ℝ) :
    Measurable (fun y : ℝ ↦ Set.indicator {t : ℝ | a < |t|} (fun t ↦ |t|) y) := by
  -- Proof comment: the strict-tail set is measurable and the weight is the measurable absolute
  -- value, so the real indicator observable is measurable.
  exact Measurable.indicator continuous_abs.measurable <|
    measurableSet_lt measurable_const continuous_abs.measurable

/-- Helper for Exercise 13.2.15: the bounded continuous cutoff `x ↦ min |f x| N`. -/
private def absCutoffContinuous {f : E → ℝ} (hf_cont : Continuous f) (N : ℕ) :
    BoundedContinuousFunction E ℝ where
  toFun := fun x ↦ min |f x| (N : ℝ)
  continuous_toFun := hf_cont.abs.min continuous_const
  map_bounded' := by
    -- Proof comment: each cutoff value already lies in `[0, N]`, so pairwise distances are
    -- bounded by `2N`.
    refine ⟨2 * (N : ℝ), ?_⟩
    intro x y
    have hx : |min |f x| (N : ℝ)| ≤ (N : ℝ) := by
      have hnonneg : 0 ≤ min |f x| (N : ℝ) := le_min (abs_nonneg _) (Nat.cast_nonneg _)
      rw [abs_of_nonneg hnonneg]
      exact min_le_right _ _
    have hy : |min |f y| (N : ℝ)| ≤ (N : ℝ) := by
      have hnonneg : 0 ≤ min |f y| (N : ℝ) := le_min (abs_nonneg _) (Nat.cast_nonneg _)
      rw [abs_of_nonneg hnonneg]
      exact min_le_right _ _
    calc
      dist (min |f x| (N : ℝ)) (min |f y| (N : ℝ))
          = |min |f x| (N : ℝ) - min |f y| (N : ℝ)| := by simp [Real.dist_eq]
      _ ≤ |min |f x| (N : ℝ)| + |min |f y| (N : ℝ)| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le (min |f x| (N : ℝ)) (-(min |f y| (N : ℝ)))
      _ ≤ 2 * (N : ℝ) := by linarith

/-- Helper for Exercise 13.2.15: the symmetric clamp `y ↦ max (-N) (min y N)` is bounded by
`N` in absolute value. -/
private lemma abs_clampNat_le (N : ℕ) (y : ℝ) :
    |max (-(N : ℝ)) (min y (N : ℝ))| ≤ (N : ℝ) := by
  -- Proof comment: the clamp always stays between `-N` and `N`, so its absolute value is at most
  -- `N`.
  have hupper : max (-(N : ℝ)) (min y (N : ℝ)) ≤ (N : ℝ) := by
    exact max_le (by linarith) (min_le_right _ _)
  have hlower : -(N : ℝ) ≤ max (-(N : ℝ)) (min y (N : ℝ)) := le_max_left _ _
  exact abs_le.2 ⟨by linarith, hupper⟩

/-- Helper for Exercise 13.2.15: the bounded continuous symmetric clamp of `f` at level `N`. -/
private def clampContinuous {f : E → ℝ} (hf_cont : Continuous f) (N : ℕ) :
    BoundedContinuousFunction E ℝ where
  toFun := fun x ↦ max (-(N : ℝ)) (min (f x) (N : ℝ))
  continuous_toFun := Continuous.max continuous_const (hf_cont.min continuous_const)
  map_bounded' := by
    -- Proof comment: as with the cutoff, the clamp values lie in `[-N, N]`, so pairwise
    -- distances are bounded by `2N`.
    refine ⟨2 * (N : ℝ), ?_⟩
    intro x y
    have hx : |max (-(N : ℝ)) (min (f x) (N : ℝ))| ≤ (N : ℝ) := abs_clampNat_le N (f x)
    have hy : |max (-(N : ℝ)) (min (f y) (N : ℝ))| ≤ (N : ℝ) := abs_clampNat_le N (f y)
    calc
      dist (max (-(N : ℝ)) (min (f x) (N : ℝ))) (max (-(N : ℝ)) (min (f y) (N : ℝ)))
          = |max (-(N : ℝ)) (min (f x) (N : ℝ)) -
              max (-(N : ℝ)) (min (f y) (N : ℝ))| := by
                simp [Real.dist_eq]
      _ ≤ |max (-(N : ℝ)) (min (f x) (N : ℝ))| +
            |max (-(N : ℝ)) (min (f y) (N : ℝ))| := by
              simpa [sub_eq_add_neg, abs_neg] using
                abs_add_le (max (-(N : ℝ)) (min (f x) (N : ℝ)))
                  (-(max (-(N : ℝ)) (min (f y) (N : ℝ))))
      _ ≤ 2 * (N : ℝ) := by linarith

/-- Helper for Exercise 13.2.15: the clamp error is supported on the strict tail and bounded by
the tail absolute value. -/
private lemma abs_sub_clampNat_le_strictTailAbsIndicator (N : ℕ) (y : ℝ) :
    |y - max (-(N : ℝ)) (min y (N : ℝ))| ≤
      Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) y := by
  -- Proof comment: on the strict tail the clamp only removes the excess over `±N`, while inside
  -- the cutoff interval the clamp is exact.
  by_cases hy : (N : ℝ) < |y|
  · by_cases hy_nonneg : 0 ≤ y
    · have hNy : (N : ℝ) < y := by simpa [abs_of_nonneg hy_nonneg] using hy
      have hclamp : max (-(N : ℝ)) (min y (N : ℝ)) = (N : ℝ) := by
        rw [min_eq_right (le_of_lt hNy), max_eq_right]
        linarith
      have hsub : 0 ≤ y - (N : ℝ) := by linarith
      rw [hclamp, abs_of_nonneg hsub]
      rw [show Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) y = |y| by simp [hy]]
      rw [abs_of_nonneg hy_nonneg]
      linarith
    · have hy_neg : y < 0 := lt_of_not_ge hy_nonneg
      have hyN : y < -(N : ℝ) := by
        have : (N : ℝ) < -y := by simpa [abs_of_neg hy_neg] using hy
        linarith
      have hclamp : max (-(N : ℝ)) (min y (N : ℝ)) = -(N : ℝ) := by
        have hy_le : y ≤ (N : ℝ) := by linarith
        rw [min_eq_left hy_le, max_eq_left (le_of_lt hyN)]
      have hsub : y + (N : ℝ) < 0 := by linarith
      rw [hclamp, show y - (-(N : ℝ)) = y + (N : ℝ) by ring, abs_of_neg hsub]
      rw [show Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) y = |y| by simp [hy]]
      rw [abs_of_neg hy_neg]
      linarith
  · have hy_le : |y| ≤ (N : ℝ) := le_of_not_gt hy
    have hy_bounds : -(N : ℝ) ≤ y ∧ y ≤ (N : ℝ) := abs_le.mp hy_le
    have hclamp : max (-(N : ℝ)) (min y (N : ℝ)) = y := by
      rw [min_eq_left hy_bounds.2, max_eq_right hy_bounds.1]
    rw [hclamp]
    simp [hy]

/-- Helper for Exercise 13.2.15: the real strict-tail indicator integral is the corresponding
tail `lintegral` written back in `ℝ`. -/
private lemma integral_strictTailAbsIndicator_eq
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {g : α → ℝ}
    (hg : AEStronglyMeasurable g μ) (a : ℝ) :
    ∫ x, Set.indicator {t : ℝ | a < |t|} (fun t ↦ |t|) (g x) ∂μ =
      (∫⁻ x in {x | a < |g x|}, ENNReal.ofReal |g x| ∂μ).toReal := by
  -- Proof comment: first rewrite the real integral as a nonnegative `lintegral`, then use the
  -- codomain-indicator identity already available for strict tails.
  have htail_sm :
      AEStronglyMeasurable (fun x ↦ Set.indicator {t : ℝ | a < |t|} (fun t ↦ |t|) (g x)) μ :=
    (measurableRealStrictTailAbsIndicator a).aestronglyMeasurable.comp_aemeasurable hg.aemeasurable
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun x ↦ by
      by_cases hx : a < |g x| <;> simp [hx, Set.indicator])
    htail_sm]
  have hpoint :
      (∫⁻ x, ENNReal.ofReal (Set.indicator {t : ℝ | a < |t|} (fun t ↦ |t|) (g x)) ∂μ) =
        ∫⁻ x, Set.indicator {t : ℝ | a < |t|} (fun t ↦ ENNReal.ofReal |t|) (g x) ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    by_cases hx : a < |g x| <;> simp [hx, Set.indicator]
  rw [hpoint]
  simpa using congrArg ENNReal.toReal (lintegral_strictTailAbsIndicator_eq hg.aemeasurable a).symm

-- Route correction: the old proof route depended on a Skorohod-coupling module whose `.olean`
-- is unavailable here. The remaining task is to finish the direct truncation argument inside this
-- theorem.
/-- Exercise 13.2.15: if `f` is continuous, uniformly integrable with respect to the probability
measures `μₙ`, and `μₙ` converges weakly to `μ`, then `f` is integrable under `μ` and the
integrals `∫ f dμₙ` converge to `∫ f dμ`. -/
theorem integrable_and_tendsto_integral_of_continuous_of_uniformlyIntegrableProbabilitySequence
    {f : E → ℝ} {μs : ℕ → ProbabilityMeasure E} {μ : ProbabilityMeasure E}
    (hf_cont : Continuous f)
    (hf_ui : uniformlyIntegrableWithRespectToProbabilitySequence f μs)
    (hμs : Tendsto μs atTop (𝓝 μ)) :
    Integrable f (μ : Measure E) ∧
      Tendsto (fun n ↦ ∫ x, f x ∂(μs n : Measure E)) atTop
        (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
  -- Proof comment: first use the uniform tail estimate at level `1` to get a uniform absolute
  -- first-moment bound for the approximating laws.
  have hε_form :=
    (uniformlyIntegrableWithRespectToProbabilitySequence_iff_forall_epsilon).1 hf_ui
  obtain ⟨aOne, haOne⟩ := hε_form 1 zero_lt_one
  let B : ℝ := aOne.1 + 1
  have hμs_abs_lintegral_bound :
      ∀ n, ∫⁻ x, ENNReal.ofReal |f x| ∂(μs n : Measure E) ≤ ENNReal.ofReal B := by
    intro n
    have hpoint :
        ∀ x, ENNReal.ofReal |f x| ≤
          ENNReal.ofReal aOne.1 +
            Set.indicator {t : ℝ | aOne.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x) := by
      intro x
      by_cases hx : aOne.1 < |f x|
      · have hnonneg : 0 ≤ aOne.1 := le_of_lt aOne.2
        simpa [Set.indicator, hx, ENNReal.ofReal_add hnonneg (abs_nonneg _)] using
          (show ENNReal.ofReal |f x| ≤ ENNReal.ofReal (aOne.1 + |f x|) by
            exact ENNReal.ofReal_le_ofReal <| by linarith)
      · simpa [Set.indicator, hx] using
          (ENNReal.ofReal_le_ofReal (le_of_not_gt hx))
    calc
      ∫⁻ x, ENNReal.ofReal |f x| ∂(μs n : Measure E)
          ≤ ∫⁻ x,
              ENNReal.ofReal aOne.1 +
                Set.indicator {t : ℝ | aOne.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
                ∂(μs n : Measure E) := by
                  exact lintegral_mono hpoint
      _ = ENNReal.ofReal aOne.1 +
            ∫⁻ x, Set.indicator {t : ℝ | aOne.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
              ∂(μs n : Measure E) := by
                rw [lintegral_add_left measurable_const]
                simp
      _ = ENNReal.ofReal aOne.1 +
            ∫⁻ x in {x | aOne.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E) := by
                rw [← lintegral_strictTailAbsIndicator_eq hf_cont.measurable.aemeasurable]
      _ ≤ ENNReal.ofReal aOne.1 + ENNReal.ofReal 1 := by
            gcongr
            exact haOne n
      _ = ENNReal.ofReal B := by
            symm
            simpa [B, add_comm] using
              (ENNReal.ofReal_add (le_of_lt aOne.2) (show 0 ≤ (1 : ℝ) by positivity))
  have hf_integrable_seq : ∀ n, Integrable f (μs n : Measure E) := by
    intro n
    have hlt :
        ∫⁻ x, ENNReal.ofReal |f x| ∂(μs n : Measure E) < ∞ := by
      exact lt_of_le_of_lt (hμs_abs_lintegral_bound n) (by simpa using ENNReal.ofReal_lt_top)
    have hAbsInt :
        Integrable (fun x : E ↦ |f x|) (μs n : Measure E) :=
      (lintegral_ofReal_ne_top_iff_integrable (hf_cont.abs.measurable.aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ abs_nonneg (f x))).1 (ne_of_lt hlt)
    exact (integrable_norm_iff hf_cont.measurable.aestronglyMeasurable).1 <| by
      simpa [Real.norm_eq_abs] using hAbsInt
  -- Proof comment: test weak convergence against bounded continuous cutoffs of `|f|` to transfer
  -- the uniform first-moment bound from the sequence to the limit law.
  have hcutoff_bound : ∀ N : ℕ, ∫ x, absCutoffContinuous hf_cont N x ∂(μ : Measure E) ≤ B := by
    intro N
    have hcutoff_tendsto :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1 hμs (absCutoffContinuous hf_cont N)
    have hcutoff_seq_bound :
        ∀ n, ∫ x, absCutoffContinuous hf_cont N x ∂(μs n : Measure E) ≤ B := by
      intro n
      have hcutoff_int :
          Integrable (absCutoffContinuous hf_cont N : E → ℝ) (μs n : Measure E) :=
        (absCutoffContinuous hf_cont N).integrable (μs n : Measure E)
      have hlintegral_bound :
          ∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μs n : Measure E) ≤
            ∫⁻ x, ENNReal.ofReal |f x| ∂(μs n : Measure E) := by
        refine lintegral_mono fun x ↦ ?_
        exact ENNReal.ofReal_le_ofReal <| min_le_left _ _
      have hnonneg :
          0 ≤ᵐ[(μs n : Measure E)] fun x ↦ absCutoffContinuous hf_cont N x :=
        Eventually.of_forall fun x ↦ le_min (abs_nonneg _) (Nat.cast_nonneg _)
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg hcutoff_int.aestronglyMeasurable]
      have hB_nonneg : 0 ≤ B := by
        dsimp [B]
        linarith [aOne.2]
      refine ENNReal.toReal_le_of_le_ofReal hB_nonneg ?_
      exact le_trans hlintegral_bound (hμs_abs_lintegral_bound n)
    exact le_of_tendsto hcutoff_tendsto (Eventually.of_forall hcutoff_seq_bound)
  have hμ_abs_lintegral_bound :
      ∫⁻ x, ENNReal.ofReal |f x| ∂(μ : Measure E) ≤ ENNReal.ofReal B := by
    have hcutoff_lintegral_tendsto :
        Tendsto
          (fun N : ℕ ↦
            ∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μ : Measure E))
          atTop
          (𝓝 (∫⁻ x, ENNReal.ofReal |f x| ∂(μ : Measure E))) := by
      refine lintegral_tendsto_of_tendsto_of_monotone
        (fun N ↦ (hf_cont.abs.min continuous_const).measurable.aemeasurable.ennreal_ofReal) ?_ ?_
      · filter_upwards with x N M hNM
        exact ENNReal.ofReal_le_ofReal <| min_le_min_left _ (Nat.cast_le.mpr hNM)
      · filter_upwards with x
        apply tendsto_const_nhds.congr'
        filter_upwards [Ioi_mem_atTop (Nat.ceil |f x|)] with N hN
        have hN' : |f x| < (N : ℝ) := by
          exact lt_of_le_of_lt (Nat.le_ceil |f x|) (by exact_mod_cast hN)
        have hmin : min |f x| (N : ℝ) = |f x| := min_eq_left (le_of_lt hN')
        simp [absCutoffContinuous, hmin]
    have hcutoff_lintegral_bound :
        ∀ N : ℕ,
          ∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μ : Measure E) ≤
            ENNReal.ofReal B := by
      intro N
      have hcutoff_int :
          Integrable (absCutoffContinuous hf_cont N : E → ℝ) (μ : Measure E) :=
        (absCutoffContinuous hf_cont N).integrable (μ : Measure E)
      have hnonneg :
          0 ≤ᵐ[(μ : Measure E)] fun x ↦ absCutoffContinuous hf_cont N x :=
        Eventually.of_forall fun x ↦ le_min (abs_nonneg _) (Nat.cast_nonneg _)
      have hreal_bound := hcutoff_bound N
      have h_eq :
          ∫ x, absCutoffContinuous hf_cont N x ∂(μ : Measure E) =
            (∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μ : Measure E)).toReal := by
        exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg hcutoff_int.aestronglyMeasurable
      have : (∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μ : Measure E)).toReal ≤ B := by
        simpa [h_eq] using hreal_bound
      have hlt :
          ∫⁻ x, ENNReal.ofReal (absCutoffContinuous hf_cont N x) ∂(μ : Measure E) < ∞ := by
        exact lt_of_le_of_lt
          (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal <| min_le_right _ _)
          (by simpa using ENNReal.ofReal_lt_top)
      have hB_nonneg : 0 ≤ B := by
        dsimp [B]
        linarith [aOne.2]
      exact (ENNReal.le_ofReal_iff_toReal_le (ne_of_lt hlt) hB_nonneg).2 this
    exact le_of_tendsto hcutoff_lintegral_tendsto (Eventually.of_forall hcutoff_lintegral_bound)
  have hf_integrable : Integrable f (μ : Measure E) := by
    have hAbsInt :
        Integrable (fun x : E ↦ |f x|) (μ : Measure E) :=
      (lintegral_ofReal_ne_top_iff_integrable (hf_cont.abs.measurable.aestronglyMeasurable)
        (Eventually.of_forall fun x ↦ abs_nonneg (f x))).1 <|
        ne_of_lt (lt_of_le_of_lt hμ_abs_lintegral_bound (by simpa using ENNReal.ofReal_lt_top))
    exact (integrable_norm_iff hf_cont.measurable.aestronglyMeasurable).1 <| by
      simpa [Real.norm_eq_abs] using hAbsInt
  -- Proof comment: the limit-law tail integral vanishes by dominated convergence, since the tail
  -- indicators decrease pointwise to zero and are dominated by `|f| ∈ L¹(μ)`.
  have hμ_tail_tendsto :
      Tendsto
        (fun N : ℕ ↦
          ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μ : Measure E))
        atTop (𝓝 0) := by
    -- Proof comment: package the four dominated-convergence inputs separately so the theorem sees
    -- the exact normal form it expects.
    have htail_meas :
        ∀ᶠ N : ℕ in atTop,
          AEStronglyMeasurable
            (fun x ↦ Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x))
            (μ : Measure E) := by
      exact Eventually.of_forall fun N ↦
        (measurableRealStrictTailAbsIndicator (N : ℝ)).aestronglyMeasurable.comp_aemeasurable
          hf_cont.measurable.aemeasurable
    have htail_bound :
        ∀ᶠ N : ℕ in atTop,
          ∀ᵐ x ∂(μ : Measure E),
            ‖Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x)‖ ≤ |f x| := by
      refine Eventually.of_forall fun N ↦ ?_
      filter_upwards with x
      by_cases hx : (N : ℝ) < |f x| <;> simp [hx, Set.indicator]
    have htail_lim :
        ∀ᵐ x ∂(μ : Measure E),
          Tendsto
            (fun N : ℕ ↦ Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x))
            atTop (𝓝 0) := by
      filter_upwards with x
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioi_mem_atTop (Nat.ceil |f x|)] with N hN
      have hN' : |f x| < (N : ℝ) := by
        exact lt_of_le_of_lt (Nat.le_ceil |f x|) (by exact_mod_cast hN)
      have hx : ¬ (N : ℝ) < |f x| := not_lt_of_ge (le_of_lt hN')
      simp [hx, Set.indicator]
    simpa using
      tendsto_integral_filter_of_dominated_convergence
        (μ := (μ : Measure E))
        (F := fun N : ℕ ↦ fun x ↦
          Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x))
        (f := fun _ ↦ 0)
        (bound := fun x ↦ |f x|)
        htail_meas htail_bound hf_integrable.norm htail_lim
  constructor
  · exact hf_integrable
  ·
    -- Proof comment: fix one clamp level with both source and limit tails below `ε / 3`, use weak
    -- convergence for the bounded clamp, and finish with a triangle inequality.
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    obtain ⟨aε, haε⟩ := hε_form (ε / 3) (by positivity)
    have hμ_tail_eventually :
        ∀ᶠ N : ℕ in atTop,
          ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μ : Measure E) <
            ε / 3 := by
      exact hμ_tail_tendsto.eventually (Iio_mem_nhds (by positivity))
    obtain ⟨Nμ, hNμ⟩ := Filter.eventually_atTop.1 hμ_tail_eventually
    let N : ℕ := max Nμ (Nat.ceil aε.1)
    have haε_le_N : aε.1 ≤ (N : ℝ) := by
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast le_max_right Nμ (Nat.ceil aε.1))
    have htail_seq_small :
        ∀ n,
          ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μs n : Measure E) ≤
            ε / 3 := by
      intro n
      have htail_lintegral_le :
          ∫⁻ x in {x | (N : ℝ) < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E) ≤
            ENNReal.ofReal (ε / 3) := by
        calc
          ∫⁻ x in {x | (N : ℝ) < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)
              = ∫⁻ x,
                  Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
                  ∂(μs n : Measure E) := by
                    exact lintegral_strictTailAbsIndicator_eq hf_cont.measurable.aemeasurable (N : ℝ)
          _ ≤ ∫⁻ x,
                Set.indicator {t : ℝ | aε.1 < |t|} (fun t ↦ ENNReal.ofReal |t|) (f x)
                ∂(μs n : Measure E) := by
                  refine lintegral_mono fun x ↦ ?_
                  exact strictTailAbsIndicator_mono haε_le_N
          _ = ∫⁻ x in {x | aε.1 < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E) := by
                symm
                exact lintegral_strictTailAbsIndicator_eq hf_cont.measurable.aemeasurable aε.1
          _ ≤ ENNReal.ofReal (ε / 3) := haε n
      have htail_real_eq :=
        integral_strictTailAbsIndicator_eq
          (μ := (μs n : Measure E))
          hf_cont.measurable.aestronglyMeasurable (N : ℝ)
      have htail_real_le :
          (∫⁻ x in {x | (N : ℝ) < |f x|}, ENNReal.ofReal |f x| ∂(μs n : Measure E)).toReal ≤
            ε / 3 := by
        have hε_third_nonneg : 0 ≤ ε / 3 := by linarith
        simpa [ENNReal.toReal_ofReal hε_third_nonneg] using
          (ENNReal.toReal_le_toReal
            (by
              exact ne_of_lt <|
                lt_of_le_of_lt htail_lintegral_le (by simpa using ENNReal.ofReal_lt_top))
            ENNReal.ofReal_ne_top).2 htail_lintegral_le
      rw [htail_real_eq]
      exact htail_real_le
    have htail_μ_small :
        ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μ : Measure E) < ε / 3 := by
      exact hNμ N (le_max_left _ _)
    have hclamp_tendsto :=
      (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).1 hμs (clampContinuous hf_cont N)
    have hclamp_eventually :
        ∀ᶠ n in atTop,
          |∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E) -
              ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E)| < ε / 3 := by
      have hdiff_tendsto :
          Tendsto
            (fun n ↦
              ∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E) -
                ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E))
            atTop (𝓝 0) := by
        simpa using
          hclamp_tendsto.sub
            (tendsto_const_nhds :
              Tendsto (fun _ : ℕ ↦ ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E)) atTop
                (𝓝 (∫ x, clampContinuous hf_cont N x ∂(μ : Measure E))))
      have hnorm_tendsto :
          Tendsto
            (fun n ↦
              |∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E) -
                  ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E)|)
            atTop (𝓝 0) := by
        simpa [Real.norm_eq_abs] using hdiff_tendsto.norm
      exact hnorm_tendsto.eventually (Iio_mem_nhds (by positivity))
    obtain ⟨Nclamp, hNclamp⟩ := Filter.eventually_atTop.1 hclamp_eventually
    refine ⟨max N Nclamp, fun n hn ↦ ?_⟩
    have htail_seq_n : ∫ x,
        Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μs n : Measure E) ≤ ε / 3 :=
      htail_seq_small n
    have hclamp_n :
        |∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E) -
            ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E)| < ε / 3 :=
      hNclamp n (le_trans (le_max_right _ _) hn)
    have herror_seq :
        |∫ x, f x ∂(μs n : Measure E) - ∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E)| ≤
          ε / 3 := by
      have hsub_int :
          Integrable (fun x ↦ f x - clampContinuous hf_cont N x) (μs n : Measure E) :=
        (hf_integrable_seq n).sub ((clampContinuous hf_cont N).integrable (μs n : Measure E))
      have htail_int :
          Integrable (fun x ↦ Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x))
            (μs n : Measure E) := by
        have hs : MeasurableSet {x | (N : ℝ) < |f x|} :=
          measurableSet_lt measurable_const hf_cont.measurable.norm
        simpa [Set.indicator] using (hf_integrable_seq n).norm.indicator hs
      calc
        |∫ x, f x ∂(μs n : Measure E) - ∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E)|
            = |∫ x, (f x - clampContinuous hf_cont N x) ∂(μs n : Measure E)| := by
                rw [integral_sub (hf_integrable_seq n) ((clampContinuous hf_cont N).integrable _)]
        _ ≤ ∫ x, |f x - clampContinuous hf_cont N x| ∂(μs n : Measure E) :=
              abs_integral_le_integral_abs
        _ ≤ ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μs n : Measure E) := by
              refine integral_mono_ae hsub_int.norm htail_int ?_
              filter_upwards with x
              simpa [clampContinuous] using abs_sub_clampNat_le_strictTailAbsIndicator N (f x)
        _ ≤ ε / 3 := htail_seq_n
    have herror_μ :
        |∫ x, clampContinuous hf_cont N x ∂(μ : Measure E) - ∫ x, f x ∂(μ : Measure E)| ≤ ε / 3 := by
      have hsub_int :
          Integrable (fun x ↦ clampContinuous hf_cont N x - f x) (μ : Measure E) :=
        ((clampContinuous hf_cont N).integrable (μ : Measure E)).sub hf_integrable
      have hsub_norm :
          Integrable (fun x ↦ |clampContinuous hf_cont N x - f x|) (μ : Measure E) := by
        simpa [Real.norm_eq_abs] using hsub_int.norm
      -- Proof comment: `integral_mono_ae` is applied after rewriting the error term to
      -- `|f - clamp|`, so normalize the integrability witness into the same order.
      have hsub_norm' :
          Integrable (fun x ↦ |f x - clampContinuous hf_cont N x|) (μ : Measure E) := by
        simpa [abs_sub_comm] using hsub_norm
      have htail_int :
          Integrable (fun x ↦ Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x))
            (μ : Measure E) := by
        have hs : MeasurableSet {x | (N : ℝ) < |f x|} :=
          measurableSet_lt measurable_const hf_cont.measurable.norm
        simpa [Set.indicator] using hf_integrable.norm.indicator hs
      have htail_μ_le : ∫ x,
          Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μ : Measure E) ≤ ε / 3 :=
        le_of_lt htail_μ_small
      calc
        |∫ x, clampContinuous hf_cont N x ∂(μ : Measure E) - ∫ x, f x ∂(μ : Measure E)|
            = |∫ x, (clampContinuous hf_cont N x - f x) ∂(μ : Measure E)| := by
                rw [integral_sub ((clampContinuous hf_cont N).integrable _) hf_integrable]
        _ ≤ ∫ x, |clampContinuous hf_cont N x - f x| ∂(μ : Measure E) :=
              abs_integral_le_integral_abs
        _ = ∫ x, |f x - clampContinuous hf_cont N x| ∂(μ : Measure E) := by
              congr 1
              ext x
              rw [abs_sub_comm]
        _ ≤ ∫ x, Set.indicator {t : ℝ | (N : ℝ) < |t|} (fun t ↦ |t|) (f x) ∂(μ : Measure E) := by
              refine integral_mono_ae hsub_norm' htail_int ?_
              filter_upwards with x
              simpa [clampContinuous, abs_sub_comm] using
                abs_sub_clampNat_le_strictTailAbsIndicator N (f x)
        _ ≤ ε / 3 := htail_μ_le
    have hmain :
        |∫ x, f x ∂(μs n : Measure E) - ∫ x, f x ∂(μ : Measure E)| < ε := by
      calc
      |∫ x, f x ∂(μs n : Measure E) - ∫ x, f x ∂(μ : Measure E)|
          ≤ |∫ x, f x ∂(μs n : Measure E) -
                ∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E)| +
              |∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E) -
                ∫ x, clampContinuous hf_cont N x ∂(μ : Measure E)| +
              |∫ x, clampContinuous hf_cont N x ∂(μ : Measure E) -
                ∫ x, f x ∂(μ : Measure E)| := by
              have h₁ := abs_sub_le
                (∫ x, f x ∂(μs n : Measure E))
                (∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E))
                (∫ x, f x ∂(μ : Measure E))
              have h₂ := abs_sub_le
                (∫ x, clampContinuous hf_cont N x ∂(μs n : Measure E))
                (∫ x, clampContinuous hf_cont N x ∂(μ : Measure E))
                (∫ x, f x ∂(μ : Measure E))
              linarith
      _ < ε / 3 + ε / 3 + ε / 3 := by linarith
      _ = ε := by ring
    simpa [Real.dist_eq] using hmain

end
