/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Corollary_7_45
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.TotalVariation
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_53
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Topology.MetricSpace.Polish

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory BoundedContinuousFunction

noncomputable section

universe u

namespace ProbabilityTheory

section Wasserstein

variable {E : Type u} [MeasurableSpace E] [MetricSpace E] [BorelSpace E]

private abbrev WassersteinCoupling (P Q : ProbabilityMeasure E) :=
  {π : ProbabilityMeasure (E × E) // IsCoupling π P Q}

/-- Definition for Example 17.55 (1): the Wasserstein distance between two probability measures is the
infimum, over all couplings `π` of `P` and `Q`, of the transport cost `∫ dist(x, y) dπ(x, y)`. -/
def wassersteinDistance (P Q : ProbabilityMeasure E) : ℝ≥0∞ :=
  sInf <| Set.range fun π : WassersteinCoupling P Q ↦
    ∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2)
      ∂((π.1 : ProbabilityMeasure (E × E)) : Measure (E × E))

variable [CompleteSpace E] [SecondCountableTopology E]

/-- Helper for Example 17.55: an anchored real-valued `1`-Lipschitz function is pointwise
dominated by the distance to the anchor. -/
private theorem anchoredLipschitz_norm_le_dist
    (x₀ : E) {f : E → ℝ} (hf₀ : f x₀ = 0) (hfLip : LipschitzWith 1 f) :
    ∀ x, ‖f x‖ ≤ dist x x₀ := by
  intro x
  -- Proof comment: the `1`-Lipschitz bound controls the oscillation between `x` and the anchor,
  -- and the anchor normalization turns that oscillation into `‖f x‖`.
  simpa [Real.dist_eq, hf₀] using hfLip.dist_le_mul x x₀

/-- Helper for Example 17.55: the anchored first-moment assumption makes every anchored
`1`-Lipschitz test function integrable. -/
private theorem anchoredLipschitz_integrable_of_integrableDist
    (x₀ : E) (μ : ProbabilityMeasure E) {f : E → ℝ} (hf₀ : f x₀ = 0)
    (hfLip : LipschitzWith 1 f)
    (hμ : Integrable (fun x ↦ dist x x₀) (μ : Measure E)) :
    Integrable f (μ : Measure E) := by
  -- Proof comment: the anchored Lipschitz bound lets us dominate `‖f‖` by the already
  -- integrable distance function.
  refine Integrable.mono' hμ hfLip.continuous.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (anchoredLipschitz_norm_le_dist x₀ hf₀ hfLip)

/-- Helper for Example 17.55: if a coupling has marginals with finite first moment at `x₀`, then
its transport cost `dist z.1 z.2` is integrable. -/
private theorem couplingDist_integrable_of_integrableDist
    (x₀ : E) {P Q : ProbabilityMeasure E} {π : ProbabilityMeasure (E × E)}
    (hπ : IsCoupling π P Q)
    (hP : Integrable (fun x ↦ dist x x₀) (P : Measure E))
    (hQ : Integrable (fun x ↦ dist x x₀) (Q : Measure E)) :
    Integrable (fun z : E × E ↦ dist z.1 z.2) (π : Measure (E × E)) := by
  rcases hπ with ⟨hfst, hsnd⟩
  have hfstInt :
      Integrable (fun z : E × E ↦ dist z.1 x₀) (π : Measure (E × E)) := by
    -- Proof comment: the first marginal identity transports the first-moment hypothesis from `P`
    -- back to the coupling.
    have hfstMap :
        Integrable (fun x ↦ dist x x₀) ((π : Measure (E × E)).fst) := by
      rw [hfst]
      exact hP
    simpa [Measure.fst] using hfstMap.comp_measurable measurable_fst
  have hsndInt :
      Integrable (fun z : E × E ↦ dist z.2 x₀) (π : Measure (E × E)) := by
    -- Proof comment: the same pullback argument transports the second first-moment hypothesis
    -- from `Q` to the coupling.
    have hsndMap :
        Integrable (fun x ↦ dist x x₀) ((π : Measure (E × E)).snd) := by
      rw [hsnd]
      exact hQ
    simpa [Measure.snd] using hsndMap.comp_measurable measurable_snd
  -- Proof comment: the triangle inequality bounds the transport cost by the sum of the two
  -- anchored distance coordinates, both already known to be integrable.
  refine Integrable.mono' (hfstInt.add hsndInt)
    ((continuous_fst.dist continuous_snd).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun z ↦ by
    simpa [Real.norm_eq_abs, abs_of_nonneg (dist_nonneg : 0 ≤ dist z.1 z.2)] using
      dist_triangle_right z.1 z.2 x₀

/-- Helper for Example 17.55: every anchored `1`-Lipschitz test function is bounded above by the
cost of any coupling of `P` and `Q`. -/
private theorem lipschitzIntegralDifference_le_couplingCost
    (x₀ : E) {P Q : ProbabilityMeasure E} {π : ProbabilityMeasure (E × E)}
    (hπ : IsCoupling π P Q) {f : E → ℝ} (hf₀ : f x₀ = 0) (hfLip : LipschitzWith 1 f)
    (hP : Integrable (fun x ↦ dist x x₀) (P : Measure E))
    (hQ : Integrable (fun x ↦ dist x x₀) (Q : Measure E)) :
    ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E) ≤
      (∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2)
        ∂((π : ProbabilityMeasure (E × E)) : Measure (E × E))).toReal := by
  rcases hπ with ⟨hfst, hsnd⟩
  have hfIntP : Integrable f (P : Measure E) :=
    anchoredLipschitz_integrable_of_integrableDist x₀ P hf₀ hfLip hP
  have hfIntQ : Integrable f (Q : Measure E) :=
    anchoredLipschitz_integrable_of_integrableDist x₀ Q hf₀ hfLip hQ
  have hfIntFst :
      Integrable (fun z : E × E ↦ f z.1) (π : Measure (E × E)) := by
    -- Proof comment: rewrite the first marginal integral through `Prod.fst` and pull the
    -- integrability back along the projection.
    have hfMap :
        Integrable f ((π : Measure (E × E)).fst) := by
      rw [hfst]
      exact hfIntP
    simpa [Measure.fst] using hfMap.comp_measurable measurable_fst
  have hfIntSnd :
      Integrable (fun z : E × E ↦ f z.2) (π : Measure (E × E)) := by
    -- Proof comment: the second coordinate is handled by the same projection argument.
    have hfMap :
        Integrable f ((π : Measure (E × E)).snd) := by
      rw [hsnd]
      exact hfIntQ
    simpa [Measure.snd] using hfMap.comp_measurable measurable_snd
  have hfstIntegral :
      ∫ z : E × E, f z.1 ∂(π : Measure (E × E)) = ∫ x, f x ∂(P : Measure E) := by
    -- Proof comment: replace the first-coordinate integral under the coupling by the integral
    -- against the first marginal, then use the coupling identity.
    calc
      ∫ z : E × E, f z.1 ∂(π : Measure (E × E)) =
          ∫ x, f x ∂((π : Measure (E × E)).fst) := by
        simpa [Measure.fst] using
          (MeasureTheory.integral_map (μ := (π : Measure (E × E)))
            measurable_fst.aemeasurable (f := f)
            hfLip.continuous.aestronglyMeasurable).symm
      _ = ∫ x, f x ∂(P : Measure E) := by rw [hfst]
  have hsndIntegral :
      ∫ z : E × E, f z.2 ∂(π : Measure (E × E)) = ∫ x, f x ∂(Q : Measure E) := by
    -- Proof comment: the second marginal identity yields the same rewrite for `Q`.
    calc
      ∫ z : E × E, f z.2 ∂(π : Measure (E × E)) =
          ∫ x, f x ∂((π : Measure (E × E)).snd) := by
        simpa [Measure.snd] using
          (MeasureTheory.integral_map (μ := (π : Measure (E × E)))
            measurable_snd.aemeasurable (f := f)
            hfLip.continuous.aestronglyMeasurable).symm
      _ = ∫ x, f x ∂(Q : Measure E) := by rw [hsnd]
  have hdiffIntegral :
      ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E) =
        ∫ z : E × E, (f z.1 - f z.2) ∂(π : Measure (E × E)) := by
    -- Proof comment: after both marginal rewrites, the dual difference becomes the integral of
    -- the pointwise oscillation along the coupling.
    calc
      ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E) =
          ∫ z : E × E, f z.1 ∂(π : Measure (E × E)) -
            ∫ z : E × E, f z.2 ∂(π : Measure (E × E)) := by
        rw [hfstIntegral, hsndIntegral]
      _ = ∫ z : E × E, (f z.1 - f z.2) ∂(π : Measure (E × E)) := by
        rw [← MeasureTheory.integral_sub hfIntFst hfIntSnd]
  have hcostInt :
      Integrable (fun z : E × E ↦ dist z.1 z.2) (π : Measure (E × E)) :=
    couplingDist_integrable_of_integrableDist x₀ ⟨hfst, hsnd⟩ hP hQ
  have hpointwise :
      ∀ z : E × E, ‖f z.1 - f z.2‖ ≤ dist z.1 z.2 := by
    intro z
    -- Proof comment: the `1`-Lipschitz bound turns the oscillation of `f` into the ambient
    -- metric distance between the coupled points.
    simpa [Real.dist_eq] using hfLip.dist_le_mul z.1 z.2
  have hcostEq :
      ∫ z : E × E, dist z.1 z.2 ∂(π : Measure (E × E)) =
        (∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2)
          ∂((π : ProbabilityMeasure (E × E)) : Measure (E × E))).toReal := by
    -- Proof comment: the cost integrand is nonnegative, so its real integral agrees with the
    -- `toReal` of the nonnegative Lebesgue integral.
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z ↦ dist_nonneg)
      ((continuous_fst.dist continuous_snd).aestronglyMeasurable)
  have hnorm :
      ‖∫ z : E × E, (f z.1 - f z.2) ∂(π : Measure (E × E))‖ ≤
        (∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2)
          ∂((π : ProbabilityMeasure (E × E)) : Measure (E × E))).toReal := by
    -- Proof comment: bound the norm of the oscillation integral by the real transport cost and
    -- then rewrite that real cost as the `toReal` of the coupling lintegral.
    calc
      ‖∫ z : E × E, (f z.1 - f z.2) ∂(π : Measure (E × E))‖ ≤
          ∫ z : E × E, dist z.1 z.2 ∂(π : Measure (E × E)) := by
        refine MeasureTheory.norm_integral_le_of_norm_le hcostInt ?_
        exact Filter.Eventually.of_forall hpointwise
      _ = (∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2)
          ∂((π : ProbabilityMeasure (E × E)) : Measure (E × E))).toReal := hcostEq
  -- Proof comment: the signed integral difference is bounded by the absolute oscillation, which
  -- is already controlled by the coupling cost.
  have haux :
      ∫ z : E × E, (f z.1 - f z.2) ∂(π : Measure (E × E)) ≤
        (∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2)
          ∂((π : ProbabilityMeasure (E × E)) : Measure (E × E))).toReal := by
    exact le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hnorm)
  simpa [hdiffIntegral] using haux

/-- Helper for Example 17.55: clamping an anchored `1`-Lipschitz witness to `[-R, R]` preserves
the anchor normalization and the `1`-Lipschitz constant. -/
private theorem clampAnchoredWitness_zero_lipschitz
    (x₀ : E) {f : E → ℝ} (hf₀ : f x₀ = 0) (hfLip : LipschitzWith 1 f) {R : ℝ}
    (hR : 0 ≤ R) :
    let g : E → ℝ := fun x ↦ (Set.projIcc (-R) R (neg_le_self hR) (f x) : ℝ)
    g x₀ = 0 ∧ LipschitzWith 1 g := by
  let g : E → ℝ := fun x ↦ (Set.projIcc (-R) R (neg_le_self hR) (f x) : ℝ)
  have hprojLip :
      LipschitzWith 1 fun t : ℝ ↦ (Set.projIcc (-R) R (neg_le_self hR) t : ℝ) := by
    -- Proof comment: projection to a closed interval is itself `1`-Lipschitz on `ℝ`.
    simpa using
      (LipschitzWith.projIcc (a := -R) (b := R) (h := neg_le_self hR))
  have hgLip : LipschitzWith 1 g := by
    -- Proof comment: compose the interval projection with the original witness.
    simpa [g] using hprojLip.comp hfLip
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (-R) R := by
    constructor <;> linarith
  have hg₀ : g x₀ = 0 := by
    -- Proof comment: the anchor value is already in the clamp interval, so projection fixes it.
    change ((Set.projIcc (-R) R (neg_le_self hR) (f x₀) : Set.Icc (-R) R) : ℝ) = 0
    rw [hf₀]
    simpa using congrArg (fun z : Set.Icc (-R) R => (z : ℝ))
      (Set.projIcc_of_mem (a := -R) (b := R) (h := neg_le_self hR) hzero_mem)
  exact ⟨hg₀, hgLip⟩

/-- Helper for Example 17.55: on points whose distance to the anchor is at most `R`, clamping an
anchored `1`-Lipschitz witness to `[-R, R]` does not change its value. -/
private theorem clampAnchoredWitness_eq_self_of_dist_le
    (x₀ : E) {f : E → ℝ} (hf₀ : f x₀ = 0) (hfLip : LipschitzWith 1 f) {R : ℝ}
    (hR : 0 ≤ R) {x : E} (hx : dist x x₀ ≤ R) :
    (Set.projIcc (-R) R (neg_le_self hR) (f x) : ℝ) = f x := by
  have hfx_abs : ‖f x‖ ≤ R := by
    -- Proof comment: the anchored Lipschitz estimate puts `f x` inside the clamp interval.
    exact le_trans (anchoredLipschitz_norm_le_dist x₀ hf₀ hfLip x) hx
  have hfx_mem : f x ∈ Set.Icc (-R) R := by
    exact abs_le.mp (by simpa [Real.norm_eq_abs] using hfx_abs)
  simpa using congrArg (fun z : Set.Icc (-R) R => (z : ℝ))
    (Set.projIcc_of_mem (a := -R) (b := R) (h := neg_le_self hR) hfx_mem)

/-- Helper for Example 17.55: the pointwise error between an anchored `1`-Lipschitz witness and
its clamp to `[-R, R]` is controlled by the distance to the anchor. -/
private theorem clampAnchoredWitness_sub_norm_le_dist
    (x₀ : E) {f : E → ℝ} (hf₀ : f x₀ = 0) (hfLip : LipschitzWith 1 f) {R : ℝ}
    (hR : 0 ≤ R) :
    ∀ x, ‖f x - (Set.projIcc (-R) R (neg_le_self hR) (f x) : ℝ)‖ ≤ dist x x₀ := by
  intro x
  let c : ℝ := (Set.projIcc (-R) R (neg_le_self hR) (f x) : ℝ)
  have hc_mem : c ∈ Set.uIcc (0 : ℝ) (f x) := by
    by_cases hfx_nonneg : 0 ≤ f x
    · by_cases hfx_le_R : f x ≤ R
      · have hc_eq : c = f x := by
          have hfx_mem : f x ∈ Set.Icc (-R) R := by
            constructor <;> linarith
          unfold c
          simpa using congrArg (fun z : Set.Icc (-R) R => (z : ℝ))
            (Set.projIcc_of_mem (a := -R) (b := R) (h := neg_le_self hR) hfx_mem)
        rw [hc_eq]
        exact Set.mem_uIcc_of_le hfx_nonneg le_rfl
      · have hR_le_fx : R ≤ f x := le_of_not_ge hfx_le_R
        have hc_eq : c = R := by
          unfold c
          simpa using congrArg (fun z : Set.Icc (-R) R => (z : ℝ))
            (Set.projIcc_of_right_le
              (a := -R) (b := R) (h := neg_le_self hR) hR_le_fx)
        rw [hc_eq]
        exact Set.mem_uIcc_of_le hR hR_le_fx
    · have hfx_le_zero : f x ≤ 0 := le_of_not_ge hfx_nonneg
      by_cases hnegR_le_fx : -R ≤ f x
      · have hc_eq : c = f x := by
          have hfx_mem : f x ∈ Set.Icc (-R) R := by
            constructor
            · exact hnegR_le_fx
            · linarith
          unfold c
          simpa using congrArg (fun z : Set.Icc (-R) R => (z : ℝ))
            (Set.projIcc_of_mem (a := -R) (b := R) (h := neg_le_self hR) hfx_mem)
        rw [hc_eq]
        exact Set.mem_uIcc_of_ge le_rfl hfx_le_zero
      · have hfx_le_negR : f x ≤ -R := le_of_not_ge hnegR_le_fx
        have hc_eq : c = -R := by
          unfold c
          simpa using congrArg (fun z : Set.Icc (-R) R => (z : ℝ))
            (Set.projIcc_of_le_left
              (a := -R) (b := R) (h := neg_le_self hR) hfx_le_negR)
        rw [hc_eq]
        exact Set.mem_uIcc_of_ge hfx_le_negR (by linarith)
  have hclamp :
      ‖f x - c‖ ≤ ‖f x‖ := by
    -- Proof comment: the symmetric clamp stays on the segment between `0` and `f x`.
    simpa [Real.norm_eq_abs] using
      (Set.abs_sub_right_of_mem_uIcc (a := (0 : ℝ)) (b := f x) (c := c) hc_mem)
  exact le_trans hclamp (anchoredLipschitz_norm_le_dist x₀ hf₀ hfLip x)

/-- Helper for Example 17.55: clamping an anchored `1`-Lipschitz witness yields another test
function that is integrable under every probability measure with finite first moment. -/
private theorem clampAnchoredWitness_integrable_of_integrableDist
    (x₀ : E) (μ : ProbabilityMeasure E) {f : E → ℝ} (hf₀ : f x₀ = 0)
    (hfLip : LipschitzWith 1 f) {R : ℝ} (hR : 0 ≤ R)
    (hμ : Integrable (fun x ↦ dist x x₀) (μ : Measure E)) :
    Integrable (fun x ↦ (Set.projIcc (-R) R (neg_le_self hR) (f x) : ℝ)) (μ : Measure E) := by
  obtain ⟨hg₀, hgLip⟩ :=
    clampAnchoredWitness_zero_lipschitz x₀ hf₀ hfLip (R := R) hR
  -- Proof comment: after the clamp, the witness is still anchored and `1`-Lipschitz, so the
  -- existing first-moment integrability lemma applies unchanged.
  simpa using
    (anchoredLipschitz_integrable_of_integrableDist x₀ μ hg₀ hgLip hμ)

/-- Helper for Example 17.55: a finite first moment at the anchor yields a compact set containing
the anchor with both small outside mass and small outside first-moment tail. -/
private theorem existsCompactContaining_smallTail
    (x₀ : E) (μ : ProbabilityMeasure E)
    (hμ : Integrable (fun x ↦ dist x x₀) (μ : Measure E))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set E, IsCompact K ∧ x₀ ∈ K ∧
      (μ : Measure E) Kᶜ ≤ ENNReal.ofReal ε ∧
      ∫ x in Kᶜ, dist x x₀ ∂(μ : Measure E) < ε := by
  have hlinTop :
      ∫⁻ x, ENNReal.ofReal (dist x x₀) ∂(μ : Measure E) ≠ ∞ := by
    exact hμ.lintegral_lt_top.ne
  have hεenn_pos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  have hεenn_ne : ENNReal.ofReal ε ≠ 0 := ne_of_gt hεenn_pos
  rcases MeasureTheory.exists_pos_setLIntegral_lt_of_measure_lt
      (μ := (μ : Measure E)) (f := fun x ↦ ENNReal.ofReal (dist x x₀))
      hlinTop (ε := ENNReal.ofReal ε) hεenn_ne with
    ⟨δ, hδpos, hδsmall⟩
  rcases exists_between hδpos with ⟨δ', hδ'pos, hδ'lt⟩
  have htight : MeasureTheory.IsTightMeasureSet {(μ : Measure E)} :=
    MeasureTheory.isTightMeasureSet_singleton
  rw [MeasureTheory.isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at htight
  have htarget_pos : 0 < min δ' (ENNReal.ofReal ε) := lt_min hδ'pos hεenn_pos
  rcases htight (min δ' (ENNReal.ofReal ε)) htarget_pos with ⟨K₀, hK₀compact, hK₀mass⟩
  let K : Set E := insert x₀ K₀
  have hKcompact : IsCompact K := hK₀compact.insert x₀
  have hKcompl_subset : Kᶜ ⊆ K₀ᶜ := by
    -- Proof comment: enlarging the compact core by the anchor only shrinks its complement.
    intro x hx
    exact (by simpa [K] using hx : x ≠ x₀ ∧ x ∉ K₀).2
  have hmass_lt_delta : (μ : Measure E) Kᶜ < δ := by
    -- Proof comment: the tightness bound is chosen strictly below the `δ` supplied by the
    -- absolute-continuity estimate for the nonnegative tail integral.
    calc
      (μ : Measure E) Kᶜ ≤ (μ : Measure E) K₀ᶜ := measure_mono hKcompl_subset
      _ ≤ min δ' (ENNReal.ofReal ε) := hK₀mass _ (by simp)
      _ ≤ δ' := min_le_left _ _
      _ < δ := hδ'lt
  have hmass : (μ : Measure E) Kᶜ ≤ ENNReal.ofReal ε := by
    -- Proof comment: the same tightness choice also forces the outside mass below `ε`.
    calc
      (μ : Measure E) Kᶜ ≤ (μ : Measure E) K₀ᶜ := measure_mono hKcompl_subset
      _ ≤ min δ' (ENNReal.ofReal ε) := hK₀mass _ (by simp)
      _ ≤ ENNReal.ofReal ε := min_le_right _ _
  have hlinTail :
      ∫⁻ x in Kᶜ, ENNReal.ofReal (dist x x₀) ∂(μ : Measure E) < ENNReal.ofReal ε :=
    hδsmall Kᶜ hmass_lt_delta
  have htail : ∫ x in Kᶜ, dist x x₀ ∂(μ : Measure E) < ε := by
    have hμrestrict :
        Integrable (fun x ↦ dist x x₀) ((μ : Measure E).restrict Kᶜ) := hμ.restrict
    have hnonneg :
        0 ≤ᵐ[(μ : Measure E).restrict Kᶜ] fun x ↦ dist x x₀ :=
      Filter.Eventually.of_forall fun _ ↦ dist_nonneg
    have htail_eq :
        ENNReal.ofReal (∫ x in Kᶜ, dist x x₀ ∂(μ : Measure E)) =
          ∫⁻ x in Kᶜ, ENNReal.ofReal (dist x x₀) ∂(μ : Measure E) := by
      simpa using
        (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
          (μ := ((μ : Measure E).restrict Kᶜ)) hμrestrict hnonneg)
    have htail_ofReal :
        ENNReal.ofReal (∫ x in Kᶜ, dist x x₀ ∂(μ : Measure E)) < ENNReal.ofReal ε := by
      rw [htail_eq]
      exact hlinTail
    exact (ENNReal.ofReal_lt_ofReal_iff hε).1 htail_ofReal
  exact ⟨K, hKcompact, by simp [K], hmass, htail⟩

/-- Helper for Example 17.55: the two first-moment hypotheses yield one common compact core
containing the anchor with small outside mass and small outside tails for both laws. -/
private theorem existsCompactCore_smallTail
    (x₀ : E) (P Q : ProbabilityMeasure E)
    (hP : Integrable (fun x ↦ dist x x₀) (P : Measure E))
    (hQ : Integrable (fun x ↦ dist x x₀) (Q : Measure E))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : Set E, IsCompact K ∧ x₀ ∈ K ∧
      (P : Measure E) Kᶜ ≤ ENNReal.ofReal ε ∧
      (Q : Measure E) Kᶜ ≤ ENNReal.ofReal ε ∧
      ∫ x in Kᶜ, dist x x₀ ∂(P : Measure E) < ε ∧
      ∫ x in Kᶜ, dist x x₀ ∂(Q : Measure E) < ε := by
  rcases existsCompactContaining_smallTail x₀ P hP hε with
    ⟨Kp, hKpcompact, hx₀p, hPmass, hPtail⟩
  rcases existsCompactContaining_smallTail x₀ Q hQ hε with
    ⟨Kq, hKqcompact, hx₀q, hQmass, hQtail⟩
  refine ⟨Kp ∪ Kq, hKpcompact.union hKqcompact, by simp [hx₀p, hx₀q], ?_, ?_, ?_, ?_⟩
  · -- Proof comment: taking the union only shrinks the complement, so the outside mass for `P`
    -- remains bounded by the already established `Kp` estimate.
    calc
      (P : Measure E) (Kp ∪ Kq)ᶜ ≤ (P : Measure E) Kpᶜ := by
        refine measure_mono ?_
        intro x hx hxKp
        exact hx (Or.inl hxKp)
      _ ≤ ENNReal.ofReal ε := hPmass
  · -- Proof comment: the same complement monotonicity gives the outside mass estimate for `Q`.
    calc
      (Q : Measure E) (Kp ∪ Kq)ᶜ ≤ (Q : Measure E) Kqᶜ := by
        refine measure_mono ?_
        intro x hx hxKq
        exact hx (Or.inr hxKq)
      _ ≤ ENNReal.ofReal ε := hQmass
  · -- Proof comment: since the distance integrand is nonnegative, shrinking the complement can
    -- only decrease the `P`-tail integral.
    have hmono :
        ∫ x in (Kp ∪ Kq)ᶜ, dist x x₀ ∂(P : Measure E) ≤
          ∫ x in Kpᶜ, dist x x₀ ∂(P : Measure E) := by
      refine MeasureTheory.integral_mono_measure ?_ ?_ (hP.restrict)
      · exact Measure.restrict_mono (by
          intro x hx hxKp
          exact hx (Or.inl hxKp)) le_rfl
      · exact Filter.Eventually.of_forall fun _ ↦ dist_nonneg
    exact lt_of_le_of_lt hmono hPtail
  · -- Proof comment: the `Q`-tail is controlled by the same monotonicity argument.
    have hmono :
        ∫ x in (Kp ∪ Kq)ᶜ, dist x x₀ ∂(Q : Measure E) ≤
          ∫ x in Kqᶜ, dist x x₀ ∂(Q : Measure E) := by
      refine MeasureTheory.integral_mono_measure ?_ ?_ (hQ.restrict)
      · exact Measure.restrict_mono (by
          intro x hx hxKq
          exact hx (Or.inr hxKq)) le_rfl
      · exact Filter.Eventually.of_forall fun _ ↦ dist_nonneg
    exact lt_of_le_of_lt hmono hQtail

/-- Helper for Example 17.55: a compact core admits a measurable finite-range representative map
that fixes the tail at the anchor and approximates the identity within `δ` on the core. -/
private theorem existsFiniteRangeRepresentativeMap
    (x₀ : E) {K : Set E} (hK : IsCompact K) (hx₀K : x₀ ∈ K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ : E → E, Measurable ρ ∧ Set.Finite (Set.range ρ) ∧
      (∀ x, ρ x ∈ K) ∧ ρ x₀ = x₀ ∧
      (∀ x ∈ K, dist (ρ x) x < δ) ∧
      (∀ x ∈ Kᶜ, ρ x = x₀) := by
  classical
  rcases hK.finite_cover_balls hδ with ⟨s, hsK, hsfin, hcover⟩
  let t : Set E := insert x₀ s
  have htfin : t.Finite := hsfin.insert x₀
  let l : List E := htfin.toFinset.toList
  let e : ℕ → E := fun n ↦ if h : n < l.length then l[n] else x₀
  let g : MeasureTheory.SimpleFunc E E := MeasureTheory.SimpleFunc.nearestPt e l.length
  let ρ : E → E := Set.piecewise K g fun _ ↦ x₀
  have hKmeas : MeasurableSet K := hK.measurableSet
  refine ⟨ρ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: the representative map is measurable because it is a simple-function
    -- quantizer on `K` and constant on the tail.
    exact Measurable.piecewise hKmeas g.measurable measurable_const
  · -- Proof comment: the representative map only takes values among the finite simple-function
    -- range together with the anchor.
    refine ((MeasureTheory.SimpleFunc.finite_range g).union (Set.finite_singleton x₀)).subset ?_
    rintro y ⟨x, rfl⟩
    by_cases hx : x ∈ K
    · left
      exact ⟨x, by simp [ρ, hx]⟩
    · right
      simp [ρ, hx]
  · intro x
    by_cases hx : x ∈ K
    · -- Proof comment: inside the compact core, the nearest-point simple function lands in the
      -- finite representative set chosen from `K`.
      have hg_mem : g x ∈ t := by
        let n := MeasureTheory.SimpleFunc.nearestPtInd e l.length x
        have hn : n ≤ l.length := MeasureTheory.SimpleFunc.nearestPtInd_le e l.length x
        have hg_eq : g x = e n := by
          simp [g, n, MeasureTheory.SimpleFunc.nearestPt]
        by_cases hnlt : n < l.length
        · have hnMemList : l[n] ∈ l := by
            simpa using (List.getElem_mem (l := l) (i := n))
          have hnMemFin : l[n] ∈ htfin.toFinset := by
            simpa [l] using (Finset.mem_toList.mp hnMemList : l[n] ∈ htfin.toFinset)
          have hnMemT : l[n] ∈ t := (Set.Finite.mem_toFinset htfin).1 hnMemFin
          simpa [hg_eq, e, hnlt] using hnMemT
        · have hnEq : n = l.length := le_antisymm hn (Nat.not_lt.mp hnlt)
          have hx₀t : x₀ ∈ t := by simp [t]
          simpa [hg_eq, e, hnlt, hnEq] using hx₀t
      have hρx : ρ x = g x := by simp [ρ, hx]
      have hg_mem' : g x = x₀ ∨ g x ∈ s := by
        simpa [t] using hg_mem
      cases hg_mem' with
      | inl hgx =>
          simpa [hρx, hgx] using hx₀K
      | inr hgs =>
          simpa [hρx] using hsK hgs
    · -- Proof comment: outside the core, the map is forced to the anchored tail representative.
      simpa [ρ, hx] using hx₀K
  · -- Proof comment: the anchor is in the core, and the nearest-point rule keeps it fixed
    -- because `x₀` itself is one of the representatives.
    have hx₀t : x₀ ∈ t := by simp [t]
    have hx₀MemList : x₀ ∈ l := by
      simpa [l] using
        (Finset.mem_toList.mpr ((Set.Finite.mem_toFinset htfin).2 hx₀t) :
          x₀ ∈ htfin.toFinset.toList)
    have hx₀idx : l.idxOf x₀ < l.length := List.idxOf_lt_length_iff.2 hx₀MemList
    have hx₀e : e (l.idxOf x₀) = x₀ := by
      simpa [e, hx₀idx] using (List.idxOf_get hx₀idx)
    have hzero :
        edist (g x₀) x₀ ≤ 0 := by
      calc
        edist (g x₀) x₀ ≤ edist (e (l.idxOf x₀)) x₀ := by
          simpa [g] using
            (MeasureTheory.SimpleFunc.edist_nearestPt_le e x₀
              (k := l.idxOf x₀) (N := l.length) (Nat.le_of_lt hx₀idx))
        _ = 0 := by simp [hx₀e]
    have hzero_eq : edist (g x₀) x₀ = 0 := le_antisymm hzero bot_le
    have hgx₀ : g x₀ = x₀ := by
      exact edist_eq_zero.1 hzero_eq
    simpa [ρ, hx₀K, hgx₀]
  · intro x hxK
    -- Proof comment: compactness supplied a finite `δ`-net of `K`, and the nearest-point simple
    -- function is at least as close as the net point covering `x`.
    rcases Set.mem_iUnion₂.1 (hcover hxK) with ⟨y, hyS, hyBall⟩
    have hyT : y ∈ t := by
      exact Or.inr hyS
    have hyMemList : y ∈ l := by
      simpa [l] using
        (Finset.mem_toList.mpr ((Set.Finite.mem_toFinset htfin).2 hyT) :
          y ∈ htfin.toFinset.toList)
    have hk : l.idxOf y < l.length := List.idxOf_lt_length_iff.2 hyMemList
    have hye : e (l.idxOf y) = y := by
      simpa [e, hk] using (List.idxOf_get hk)
    have hnearestENN :
        edist (g x) x ≤ edist y x := by
      calc
        edist (g x) x ≤ edist (e (l.idxOf y)) x := by
          simpa [g] using
            (MeasureTheory.SimpleFunc.edist_nearestPt_le e x
              (k := l.idxOf y) (N := l.length) (Nat.le_of_lt hk))
        _ = edist y x := by rw [hye]
    have hnearest :
        dist (g x) x ≤ dist y x := by
      exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).1
        (by simpa [edist_dist] using hnearestENN)
    have hgx : ρ x = g x := by simp [ρ, hxK]
    exact lt_of_le_of_lt (by simpa [hgx] using hnearest) (by simpa [dist_comm] using hyBall)
  · intro x hxK
    -- Proof comment: by construction, the tail cell is collapsed to the anchor.
    simpa [ρ] using
      (Set.piecewise_eq_of_notMem (s := K) (f := g) (g := fun _ ↦ x₀) hxK)

/-- Helper for Example 17.55: the fibers of a measurable finite-range map form a measurable
finite partition of the ambient space. -/
private theorem measurableFiberPartition_of_finiteRange
    {ρ : E → E} (hρmeas : Measurable ρ) (hρfin : Set.Finite (Set.range ρ)) :
    ∃ t : Set E, t.Finite ∧ ∃ A : t → Set E,
      (∀ y, MeasurableSet (A y)) ∧
      (Pairwise fun y z ↦ Disjoint (A y) (A z)) ∧
      (∀ x, ∃ y, x ∈ A y) ∧
      (∀ y, A y = ρ ⁻¹' {y.1}) := by
  refine ⟨Set.range ρ, hρfin, fun y ↦ ρ ⁻¹' {y.1}, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: each fiber is measurable as the preimage of a singleton.
    intro y
    exact hρmeas (measurableSet_singleton y.1)
  · -- Proof comment: distinct fibers are disjoint because a point cannot take two different
    -- values under a function.
    intro y z hyz
    refine Set.disjoint_left.2 ?_
    intro x hx hy
    have hyx : ρ x = y.1 := by simpa using hx
    have hzx : ρ x = z.1 := by simpa using hy
    exact hyz (Subtype.ext (hyx.symm.trans hzx))
  · -- Proof comment: every point belongs to the fiber of its own image.
    intro x
    refine ⟨⟨ρ x, ⟨x, rfl⟩⟩, ?_⟩
    simp
  · intro y
    rfl

/-- Helper for Example 17.55: a compact core admits finitely many measurable representative cells,
with one distinguished tail cell at the anchor and cellwise `δ`-control on the core. -/
private theorem existsFiniteRepresentativePartition_withTailCell
    (x₀ : E) {K : Set E} (hK : IsCompact K) (hx₀K : x₀ ∈ K) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : Set E, ∃ htfin : t.Finite, ∃ hx₀t : x₀ ∈ t, ∃ A : t → Set E,
      (∀ y, MeasurableSet (A y)) ∧
      (Pairwise fun y z ↦ Disjoint (A y) (A z)) ∧
      (∀ x, ∃ y, x ∈ A y) ∧
      Kᶜ ⊆ A ⟨x₀, hx₀t⟩ ∧
      (∀ y x, x ∈ A y → x ∈ K → dist y.1 x < δ) := by
  obtain ⟨ρ, hρmeas, hρfin, hρK, hρx₀, hρapprox, hρtail⟩ :=
    existsFiniteRangeRepresentativeMap x₀ hK hx₀K hδ
  let t : Set E := Set.range ρ
  let A : t → Set E := fun y ↦ ρ ⁻¹' {y.1}
  have htfin : t.Finite := hρfin
  have hx₀t : x₀ ∈ t := ⟨x₀, hρx₀⟩
  refine ⟨t, htfin, hx₀t, A, ?_, ?_, ?_, ?_, ?_⟩
  · -- Proof comment: the partition cells are measurable fibers of the representative map.
    intro y
    exact hρmeas (measurableSet_singleton y.1)
  · -- Proof comment: distinct fibers are disjoint.
    intro y z hyz
    refine Set.disjoint_left.2 ?_
    intro x hx hy
    have hyx : ρ x = y.1 := by simpa [A] using hx
    have hzx : ρ x = z.1 := by simpa [A] using hy
    exact hyz (Subtype.ext (hyx.symm.trans hzx))
  · -- Proof comment: every point belongs to the fiber of its own image.
    intro x
    refine ⟨⟨ρ x, ⟨x, rfl⟩⟩, ?_⟩
    simp [A]
  · -- Proof comment: outside the compact core, the representative map is constantly `x₀`,
    -- so those points lie in the anchor fiber.
    intro x hxK
    simpa [A, hρtail x hxK] using hρtail x hxK
  · intro y x hxA hxK
    -- Proof comment: on the compact core, membership in a fiber identifies the representative
    -- with the value of `ρ`, so the cellwise error bound comes directly from the quantizer.
    have hxρ : ρ x = y.1 := by simpa [A] using hxA
    simpa [hxρ] using hρapprox x hxK

/-- Helper for Example 17.55: the compact-core quantizer can be repackaged as a measurable map to
one finite subtype, with small mean approximation error under both laws. -/
private theorem existsFiniteRangeRepresentativeWithSmallMeanError
    (x₀ : E) (P Q : ProbabilityMeasure E)
    (hP : Integrable (fun x ↦ dist x x₀) (P : Measure E))
    (hQ : Integrable (fun x ↦ dist x x₀) (Q : Measure E))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Set E, ∃ htfin : t.Finite, ∃ hx₀t : x₀ ∈ t, ∃ ρ : E → t,
      Measurable ρ ∧
      ρ x₀ = ⟨x₀, hx₀t⟩ ∧
      ∫ x, dist x (ρ x).1 ∂(P : Measure E) < ε ∧
      ∫ x, dist x (ρ x).1 ∂(Q : Measure E) < ε := by
  let η : ℝ := ε / 2
  have hη : 0 < η := by
    dsimp [η]
    linarith
  rcases existsCompactCore_smallTail x₀ P Q hP hQ (ε := η) hη with
    ⟨K, hKcompact, hx₀K, hPKcompl, hQKcompl, hPtail, hQtail⟩
  obtain ⟨ρbase, hρbase_meas, hρbase_fin, hρbase_memK, hρbase_x₀, hρbase_approx, hρbase_tail⟩ :=
    existsFiniteRangeRepresentativeMap x₀ hKcompact hx₀K hη
  let t : Set E := Set.range ρbase
  have htfin : t.Finite := hρbase_fin
  have hx₀t : x₀ ∈ t := ⟨x₀, hρbase_x₀⟩
  let ρ : E → t := fun x ↦ ⟨ρbase x, ⟨x, rfl⟩⟩
  have hρmeas : Measurable ρ := by
    -- Proof comment: the ambient quantizer is already measurable, and the subtype target is
    -- obtained by bundling the finite-range membership proof.
    exact hρbase_meas.subtype_mk
  have hρx₀ : ρ x₀ = ⟨x₀, hx₀t⟩ := by
    -- Proof comment: the underlying representative fixes the anchor, so the subtype-valued map
    -- fixes the distinguished anchor point as well.
    apply Subtype.ext
    simp [ρ, hρbase_x₀]
  have hρdist_meas :
      Measurable fun x ↦ dist x (ρ x).1 := by
    exact measurable_id.dist (measurable_subtype_coe.comp hρmeas)
  have hρdist_le :
      ∀ x, dist x (ρ x).1 ≤ η + dist x x₀ := by
    intro x
    by_cases hx : x ∈ K
    · -- Proof comment: on the compact core, the quantizer error is uniformly smaller than `η`.
      have happrox : dist x (ρ x).1 < η := by
        simpa [ρ, dist_comm] using hρbase_approx x hx
      have hdist_nonneg : 0 ≤ dist x x₀ := dist_nonneg
      linarith
    · -- Proof comment: outside the core, the map is exactly the anchor, so the error equals the
      -- anchored distance.
      have htail : ρbase x = x₀ := hρbase_tail x hx
      have hdist_eq : dist x (ρ x).1 = dist x x₀ := by
        simp [ρ, htail]
      rw [hdist_eq]
      exact le_add_of_nonneg_left hη.le
  have hρdistIntP :
      Integrable (fun x ↦ dist x (ρ x).1) (P : Measure E) := by
    -- Proof comment: the quantization error is dominated by the integrable anchor distance plus
    -- the constant budget `η`.
    refine Integrable.mono' ((integrable_const η).add hP) hρdist_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      calc
        ‖dist x (ρ x).1‖ = dist x (ρ x).1 := by
          simpa [Real.norm_eq_abs] using abs_of_nonneg (dist_nonneg : 0 ≤ dist x (ρ x).1)
        _ ≤ η + dist x x₀ := hρdist_le x
  have hρdistIntQ :
      Integrable (fun x ↦ dist x (ρ x).1) (Q : Measure E) := by
    refine Integrable.mono' ((integrable_const η).add hQ) hρdist_meas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      calc
        ‖dist x (ρ x).1‖ = dist x (ρ x).1 := by
          simpa [Real.norm_eq_abs] using abs_of_nonneg (dist_nonneg : 0 ≤ dist x (ρ x).1)
        _ ≤ η + dist x x₀ := hρdist_le x
  have hinsideP :
      ∫ x in K, dist x (ρ x).1 ∂(P : Measure E) ≤ η := by
    -- Proof comment: on the compact core, the representative map stays within the uniform
    -- `η`-net radius.
    have hmono :
        ∫ x, K.indicator (fun x ↦ dist x (ρ x).1) x ∂(P : Measure E) ≤
          ∫ x, η ∂(P : Measure E) := by
      refine MeasureTheory.integral_mono_ae (hρdistIntP.indicator hKcompact.measurableSet)
        (integrable_const η) ?_
      exact Filter.Eventually.of_forall fun x ↦ by
        by_cases hx : x ∈ K
        · have happrox : dist x (ρ x).1 < η := by
            simpa [ρ, dist_comm] using hρbase_approx x hx
          have happrox' : dist x (ρ x).1 ≤ η := le_of_lt happrox
          simp [hx, happrox']
        · simp [hx, hη.le]
    calc
      ∫ x in K, dist x (ρ x).1 ∂(P : Measure E) =
          ∫ x, K.indicator (fun x ↦ dist x (ρ x).1) x ∂(P : Measure E) := by
        rw [MeasureTheory.integral_indicator hKcompact.measurableSet]
      _ ≤ ∫ x, η ∂(P : Measure E) := hmono
      _ = η := by
        rw [MeasureTheory.integral_const]
        simp [probReal_univ]
  have hinsideQ :
      ∫ x in K, dist x (ρ x).1 ∂(Q : Measure E) ≤ η := by
    -- Proof comment: the same uniform core bound holds under `Q`.
    have hmono :
        ∫ x, K.indicator (fun x ↦ dist x (ρ x).1) x ∂(Q : Measure E) ≤
          ∫ x, η ∂(Q : Measure E) := by
      refine MeasureTheory.integral_mono_ae (hρdistIntQ.indicator hKcompact.measurableSet)
        (integrable_const η) ?_
      exact Filter.Eventually.of_forall fun x ↦ by
        by_cases hx : x ∈ K
        · have happrox : dist x (ρ x).1 < η := by
            simpa [ρ, dist_comm] using hρbase_approx x hx
          have happrox' : dist x (ρ x).1 ≤ η := le_of_lt happrox
          simp [hx, happrox']
        · simp [hx, hη.le]
    calc
      ∫ x in K, dist x (ρ x).1 ∂(Q : Measure E) =
          ∫ x, K.indicator (fun x ↦ dist x (ρ x).1) x ∂(Q : Measure E) := by
        rw [MeasureTheory.integral_indicator hKcompact.measurableSet]
      _ ≤ ∫ x, η ∂(Q : Measure E) := hmono
      _ = η := by
        rw [MeasureTheory.integral_const]
        simp [probReal_univ]
  have houtsideP :
      ∫ x in Kᶜ, dist x (ρ x).1 ∂(P : Measure E) =
        ∫ x in Kᶜ, dist x x₀ ∂(P : Measure E) := by
    -- Proof comment: on the tail cell, the representative map is exactly the anchor.
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hKcompact.measurableSet.compl] with x hx
    have htail : ρbase x = x₀ := hρbase_tail x hx
    simp [ρ, htail, dist_comm]
  have houtsideQ :
      ∫ x in Kᶜ, dist x (ρ x).1 ∂(Q : Measure E) =
        ∫ x in Kᶜ, dist x x₀ ∂(Q : Measure E) := by
    -- Proof comment: the same tail identity holds under `Q` because the representative map is
    -- still the anchor on `Kᶜ`.
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hKcompact.measurableSet.compl] with x hx
    have htail : ρbase x = x₀ := hρbase_tail x hx
    simp [ρ, htail, dist_comm]
  have hsplitP :
      ∫ x, dist x (ρ x).1 ∂(P : Measure E) =
        ∫ x in K, dist x (ρ x).1 ∂(P : Measure E) +
          ∫ x in Kᶜ, dist x (ρ x).1 ∂(P : Measure E) := by
    simpa using (MeasureTheory.integral_add_compl hKcompact.measurableSet hρdistIntP).symm
  have hsplitQ :
      ∫ x, dist x (ρ x).1 ∂(Q : Measure E) =
        ∫ x in K, dist x (ρ x).1 ∂(Q : Measure E) +
          ∫ x in Kᶜ, dist x (ρ x).1 ∂(Q : Measure E) := by
    simpa using (MeasureTheory.integral_add_compl hKcompact.measurableSet hρdistIntQ).symm
  have hmeanP :
      ∫ x, dist x (ρ x).1 ∂(P : Measure E) < ε := by
    rw [hsplitP, houtsideP]
    have hsum_lt :
        ∫ x in K, dist x (ρ x).1 ∂(P : Measure E) +
            ∫ x in Kᶜ, dist x x₀ ∂(P : Measure E) <
          η + η := by
      exact add_lt_add_of_le_of_lt hinsideP hPtail
    have hηeq : η + η = ε := by
      dsimp [η]
      ring
    calc
      ∫ x in K, dist x (ρ x).1 ∂(P : Measure E) +
          ∫ x in Kᶜ, dist x x₀ ∂(P : Measure E) <
        η + η := hsum_lt
      _ = ε := hηeq
  have hmeanQ :
      ∫ x, dist x (ρ x).1 ∂(Q : Measure E) < ε := by
    rw [hsplitQ, houtsideQ]
    have hsum_lt :
        ∫ x in K, dist x (ρ x).1 ∂(Q : Measure E) +
            ∫ x in Kᶜ, dist x x₀ ∂(Q : Measure E) <
          η + η := by
      exact add_lt_add_of_le_of_lt hinsideQ hQtail
    have hηeq : η + η = ε := by
      dsimp [η]
      ring
    calc
      ∫ x in K, dist x (ρ x).1 ∂(Q : Measure E) +
          ∫ x in Kᶜ, dist x x₀ ∂(Q : Measure E) <
        η + η := hsum_lt
      _ = ε := hηeq
  exact ⟨t, htfin, hx₀t, ρ, hρmeas, hρx₀, hmeanP, hmeanQ⟩

/-- Helper for Example 17.55: the normalized restriction of `μ` to the fiber `ρ ⁻¹' {a}`. -/
private def normalizedFiberLaw [Nonempty E]
    (μ : ProbabilityMeasure E) {t : Set E} (ρ : E → t) (a : t) : ProbabilityMeasure E :=
  (μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).normalize

/-- Helper for Example 17.55: scaling the normalized fiber law by the mass of its fiber recovers
the corresponding restriction of `μ`. -/
private theorem fiberMass_smul_normalizedFiberLaw_apply
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} (ρ : E → t) (a : t)
    {s : Set E} (hs : MeasurableSet s) :
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) *
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E) s)) =
      ((μ : Measure E).restrict (ρ ⁻¹' {a})) s := by
  -- Proof comment: apply the finite-measure identity `mass • normalize = self` to the measurable
  -- set `s`, so the coercion boundary is crossed only once at the apply level.
  simpa [normalizedFiberLaw, FiniteMeasure.restrict_measure_eq, hs, smul_eq_mul] using
    congrArg (fun ν : FiniteMeasure E ↦ ((ν : Measure E) s))
      ((MeasureTheory.FiniteMeasure.self_eq_mass_smul_normalize
        (μ := μ.toFiniteMeasure.restrict (ρ ⁻¹' {a}))).symm)

/-- Helper for Example 17.55: scaling the normalized fiber law by the mass of its fiber recovers
the corresponding restriction of `μ`. -/
private theorem fiberMass_smul_normalizedFiberLaw_eq_restrict
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} (ρ : E → t) (a : t) :
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) •
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E))) =
      (μ : Measure E).restrict (ρ ⁻¹' {a}) := by
  -- Proof comment: once the apply-level normalization bridge is available, the whole-measure
  -- statement is just extensionality on measurable sets.
  ext s hs
  simpa [smul_eq_mul] using
    fiberMass_smul_normalizedFiberLaw_apply (μ := μ) (ρ := ρ) a hs

/-- Helper for Example 17.55: summing the fiberwise normalized restrictions with their fiber
masses reconstructs the original measure. -/
private theorem sum_smul_normalizedFiberLaw_eq
    [Nonempty E] {t : Set E} [Fintype t] (μ : ProbabilityMeasure E) {ρ : E → t}
    (hρmeas : Measurable ρ) :
    (∑ a : t, (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) •
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)))) =
      (μ : Measure E) := by
  have hpairwise : (Set.univ : Set t).Pairwise
      (Function.onFun Disjoint fun a : t ↦ ρ ⁻¹' {a}) := by
    intro a _ b _ hab
    refine Set.disjoint_left.2 ?_
    intro x hxa hxb
    have hxa' : ρ x = a := by simpa using hxa
    have hxb' : ρ x = b := by simpa using hxb
    exact hab (hxa'.symm.trans hxb')
  have hrestrict :
      ((μ : Measure E).restrict (⋃ a ∈ (Finset.univ : Finset t), ρ ⁻¹' {a})) =
        ∑ a ∈ (Finset.univ : Finset t), (μ : Measure E).restrict (ρ ⁻¹' {a}) := by
    simpa [FiniteMeasure.restrict_measure_eq] using
      congrArg (fun ν : FiniteMeasure E ↦ (ν : Measure E))
        (MeasureTheory.FiniteMeasure.restrict_biUnion_finset
          (μ := μ.toFiniteMeasure) (T := Finset.univ) (s := fun a : t ↦ ρ ⁻¹' {a})
          (by simpa using hpairwise)
          (fun a ↦ hρmeas (measurableSet_singleton a)))
  have hUnion :
      (⋃ a ∈ (Finset.univ : Finset t), ρ ⁻¹' {a}) = Set.univ := by
    ext x
    simp
  calc
    (∑ a : t, (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞) •
        (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)))) =
        ∑ a ∈ (Finset.univ : Finset t), (μ : Measure E).restrict (ρ ⁻¹' {a}) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      simpa using fiberMass_smul_normalizedFiberLaw_eq_restrict (μ := μ) (ρ := ρ) a
    _ = (μ : Measure E).restrict (⋃ a ∈ (Finset.univ : Finset t), ρ ⁻¹' {a}) := by
      simpa using hrestrict.symm
    _ = (μ : Measure E) := by
      rw [hUnion, Measure.restrict_univ]

/-- Helper for Example 17.55: the measurable representative map pushes a probability measure
forward to a probability measure on the finite representative subtype. -/
private abbrev representativeMapLaw
    (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ) :
    ProbabilityMeasure t :=
  μ.map (f := ρ) hρmeas.aemeasurable

/-- Helper for Example 17.55: the singleton masses of a finite coupling are the row and column
totals of its atom masses. -/
private theorem mapCouplingSingletonMarginals {t : Set E} [Fintype t]
    {P Q : ProbabilityMeasure E} {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    (∀ a : t, ∑ b : t, ((ν : Measure (t × t)) {(a, b)}) =
        (((representativeMapLaw P hρmeas : ProbabilityMeasure t) : Measure t) {a})) ∧
      (∀ b : t, ∑ a : t, ((ν : Measure (t × t)) {(a, b)}) =
        (((representativeMapLaw Q hρmeas : ProbabilityMeasure t) : Measure t) {b})) := by
  rcases hν with ⟨hfst, hsnd⟩
  constructor
  · intro a
    -- Proof comment: evaluate the first marginal identity on the singleton `{a}` and rewrite the
    -- preimage of `{a}` under `Prod.fst` as the finite row sum of atoms.
    have hfstSingleton := congrArg (fun μ : Measure t ↦ μ {a}) hfst
    simpa [Measure.fst_apply, MeasureTheory.measure_preimage_fst_singleton_eq_sum] using
      hfstSingleton
  · intro b
    -- Proof comment: the second marginal identity gives the analogous column-sum formula.
    have hsndSingleton := congrArg (fun μ : Measure t ↦ μ {b}) hsnd
    simpa [Measure.snd_apply, MeasureTheory.measure_preimage_snd_singleton_eq_sum] using
      hsndSingleton

/-- Helper for Example 17.55: the mass of a quantization fiber equals the singleton mass of the
pushforward measure at that representative. -/
private theorem fiberMass_eq_mapSingleton
    (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ) (a : t) :
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) =
      (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t) {a}) := by
  -- Proof comment: the restricted finite measure has mass equal to the fiber mass, and that fiber
  -- mass is exactly the singleton mass of the pushforward.
  calc
    (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) =
        ((μ.toFiniteMeasure : Measure E) (ρ ⁻¹' {a})) := by
      simpa using congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞))
        ((μ.toFiniteMeasure).restrict_mass (ρ ⁻¹' {a}))
    _ = (μ : Measure E) (ρ ⁻¹' {a}) := by
      simp
    _ = (((representativeMapLaw μ hρmeas : ProbabilityMeasure t) : Measure t) {a}) := by
      symm
      simpa [representativeMapLaw] using
        (MeasureTheory.ProbabilityMeasure.map_apply' (ν := μ) (f := ρ) hρmeas.aemeasurable
          (A := {a}) (measurableSet_singleton a))

/-- Helper for Example 17.55: a coupling of the quantized pushforwards induces a finite sum of
product fiber laws on `E × E`. -/
private def liftedMapCoupling [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) (ρ : E → t) (ν : ProbabilityMeasure (t × t)) :
    Measure (E × E) :=
  ∑ a : t, ∑ b : t,
    (((ν : Measure (t × t)) {(a, b)}) •
      ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
          ProbabilityMeasure (E × E)) : Measure (E × E))))

/-- Helper for Example 17.55: the lifted finite-cell coupling has first marginal `P`. -/
private theorem liftedMapCoupling_fst_eq [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    Measure.map Prod.fst (liftedMapCoupling P Q ρ ν) = (P : Measure E) := by
  rcases mapCouplingSingletonMarginals (hρmeas := hρmeas) hν with ⟨hrows, _⟩
  -- Proof comment: `Prod.fst` turns each product cell into its first factor because the second
  -- normalized fiber law is a probability measure of total mass `1`.
  calc
    Measure.map Prod.fst (liftedMapCoupling P Q ρ ν)
        = ∑ a : t, ∑ b : t,
            ((ν : Measure (t × t)) {(a, b)}) •
              (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      rw [liftedMapCoupling, ← Measure.sum_fintype]
      rw [Measure.map_sum measurable_fst.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← Measure.sum_fintype]
      rw [Measure.map_sum measurable_fst.aemeasurable]
      rw [Measure.sum_fintype]
      simp [Measure.sum_fintype, Measure.map_smul, Measure.map_fst_prod]
    _ = ∑ a : t, (∑ b : t, ((ν : Measure (t × t)) {(a, b)})) •
          (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      simp_rw [← Finset.sum_smul]
    _ = ∑ a : t, (((representativeMapLaw P hρmeas : ProbabilityMeasure t) : Measure t) {a}) •
          (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [hrows a]
    _ = ∑ a : t, (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) •
          (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← fiberMass_eq_mapSingleton (μ := P) (hρmeas := hρmeas) a]
    _ = (P : Measure E) := by
      simpa using sum_smul_normalizedFiberLaw_eq (μ := P) (ρ := ρ) hρmeas

/-- Helper for Example 17.55: the lifted finite-cell coupling has second marginal `Q`. -/
private theorem liftedMapCoupling_snd_eq [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    Measure.map Prod.snd (liftedMapCoupling P Q ρ ν) = (Q : Measure E) := by
  rcases mapCouplingSingletonMarginals (hρmeas := hρmeas) hν with ⟨_, hcols⟩
  -- Proof comment: the second marginal is the symmetric column-sum version of the first marginal
  -- calculation.
  calc
    Measure.map Prod.snd (liftedMapCoupling P Q ρ ν)
        = ∑ a : t, ∑ b : t,
            ((ν : Measure (t × t)) {(a, b)}) •
              (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      rw [liftedMapCoupling, ← Measure.sum_fintype]
      rw [Measure.map_sum measurable_snd.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← Measure.sum_fintype]
      rw [Measure.map_sum measurable_snd.aemeasurable]
      rw [Measure.sum_fintype]
      simp [Measure.sum_fintype, Measure.map_smul, Measure.map_snd_prod]
    _ = ∑ b : t, ∑ a : t,
          ((ν : Measure (t × t)) {(a, b)}) •
            (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      rw [Finset.sum_comm]
    _ = ∑ b : t, (∑ a : t, ((ν : Measure (t × t)) {(a, b)})) •
          (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      simp_rw [← Finset.sum_smul]
    _ = ∑ b : t, (((representativeMapLaw Q hρmeas : ProbabilityMeasure t) : Measure t) {b}) •
          (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [hcols b]
    _ = ∑ b : t, (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) •
          (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)) := by
      refine Finset.sum_congr rfl ?_
      intro b hb
      rw [← fiberMass_eq_mapSingleton (μ := Q) (hρmeas := hρmeas) b]
    _ = (Q : Measure E) := by
      simpa using sum_smul_normalizedFiberLaw_eq (μ := Q) (ρ := ρ) hρmeas

/-- Helper for Example 17.55: a finite-range representative map preserves first-moment
integrability of the distance to the chosen representative. -/
private theorem integrable_dist_mapRepresentative_of_integrableDist
    (x₀ : E) {μ : ProbabilityMeasure E} {t : Set E} (htfin : t.Finite) {ρ : E → t}
    (hρmeas : Measurable ρ)
    (hμ : Integrable (fun x ↦ dist x x₀) (μ : Measure E)) :
    Integrable (fun x ↦ dist x (ρ x).1) (μ : Measure E) := by
  classical
  letI : Fintype t := htfin.fintype
  let C : ℝ := ∑ a : t, dist a.1 x₀
  have hC_nonneg : 0 ≤ C := by
    exact Finset.sum_nonneg fun _ _ ↦ dist_nonneg
  have hrep_le : ∀ x, dist x₀ (ρ x).1 ≤ C := by
    intro x
    have hsingle :
        dist (ρ x).1 x₀ ≤ ∑ a : t, dist a.1 x₀ := by
      exact Finset.single_le_sum (fun _ _ ↦ dist_nonneg) (Finset.mem_univ (ρ x))
    simpa [C, dist_comm] using hsingle
  have hbound : ∀ x, dist x (ρ x).1 ≤ dist x x₀ + C := by
    intro x
    calc
      dist x (ρ x).1 ≤ dist x x₀ + dist x₀ (ρ x).1 := dist_triangle _ _ _
      _ ≤ dist x x₀ + C := add_le_add_right (hrep_le x) _
  have hmeas : Measurable fun x ↦ dist x (ρ x).1 := by
    fun_prop
  -- Proof comment: a finite-range representative map contributes only a uniform additive error,
  -- so the anchored first moment of `μ` still dominates the new distance function.
  refine Integrable.mono' (hμ.add (integrable_const C)) hmeas.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun x ↦ by
    have hleft_nonneg : 0 ≤ dist x (ρ x).1 := dist_nonneg
    have hright_nonneg : 0 ≤ dist x x₀ + C := add_nonneg dist_nonneg hC_nonneg
    simpa [Real.norm_eq_abs, abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg] using
      hbound x

/-- Helper for Example 17.55: inside the fiber of `a`, the preimage of a set `s` containing `a`
is the whole fiber. -/
private theorem preimage_inter_fiber_eq_fiber_of_mem
    {t : Set E} {ρ : E → t} {a : t} {s : Set t} (hsa : a ∈ s) :
    ρ ⁻¹' s ∩ ρ ⁻¹' {a} = ρ ⁻¹' {a} := by
  -- Proof comment: every point in the fiber already maps to `a`, so membership in `s` is
  -- automatic once `a ∈ s`.
  ext x
  constructor
  · intro hx
    exact hx.2
  · intro hx
    have hxEq : ρ x = a := by
      simpa using hx
    refine ⟨?_, hx⟩
    simpa [hxEq] using hsa

/-- Helper for Example 17.55: if `a ∉ s`, then the preimage of `s` is disjoint from the fiber of
`a`. -/
private theorem preimage_inter_fiber_eq_empty_of_notMem
    {t : Set E} {ρ : E → t} {a : t} {s : Set t} (hsa : a ∉ s) :
    ρ ⁻¹' s ∩ ρ ⁻¹' {a} = (∅ : Set E) := by
  -- Proof comment: a point cannot simultaneously map to `a` and to a set excluding `a`.
  ext x
  constructor
  · intro hx
    have hxEq : ρ x = a := by
      simpa using hx.2
    have ha_mem : a ∈ s := by
      simpa [hxEq] using hx.1
    exact (hsa ha_mem).elim
  · intro hx
    simp at hx

/-- Helper for Example 17.55: pushing the restriction of `μ` to the fiber `ρ ⁻¹' {a}` forward
along `ρ` gives the scalar Dirac mass at `a` weighted by the fiber mass. -/
private theorem measure_map_restrict_fiber_eq_smul_dirac
    (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ) (a : t) :
    Measure.map ρ ((μ : Measure E).restrict (ρ ⁻¹' {a})) =
      ((μ : Measure E) (ρ ⁻¹' {a})) • Measure.dirac a := by
  ext s hs
  by_cases hsa : a ∈ s
  · -- Proof comment: on a measurable set containing `a`, intersecting with the fiber leaves the
    -- full fiber, so the pushforward mass is exactly the fiber mass.
    rw [Measure.map_apply hρmeas hs, Measure.restrict_apply (hρmeas hs)]
    rw [preimage_inter_fiber_eq_fiber_of_mem hsa]
    simp [hsa]
  · -- Proof comment: if `a ∉ s`, the preimage of `s` misses the fiber completely, so both sides
    -- are zero.
    rw [Measure.map_apply hρmeas hs, Measure.restrict_apply (hρmeas hs)]
    rw [preimage_inter_fiber_eq_empty_of_notMem hsa]
    simp [hsa]

/-- Helper for Example 17.55: once the fiber of `a` has positive mass, pushing the normalized
fiber law forward along `ρ` gives the Dirac mass at `a`. -/
private theorem map_normalizedFiberLaw_apply_of_fiberMass_ne_zero
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ)
    (a : t)
    (ha :
      (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) ≠ 0)
    {s : Set t} (hs : MeasurableSet s) :
    Measure.map ρ (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)) s =
      Measure.dirac a s := by
  let ν : FiniteMeasure E := μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})
  have hmass :
      (μ : Measure E) (ρ ⁻¹' {a}) = ((ν.mass : ℝ≥0∞)) := by
    -- Proof comment: the fiber mass is exactly the mass of the restricted finite measure.
    calc
      (μ : Measure E) (ρ ⁻¹' {a}) = ((μ.toFiniteMeasure : Measure E) (ρ ⁻¹' {a})) := by
        simp
      _ = ((ν.mass : ℝ≥0∞)) := by
        simpa [ν] using
          (congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞))
            ((μ.toFiniteMeasure).restrict_mass (ρ ⁻¹' {a}))).symm
  have hν_ne : ν ≠ 0 := by
    -- Proof comment: positive fiber mass rules out the zero finite measure, so normalization
    -- reduces to scalar rescaling of the restricted fiber measure.
    intro hν
    have hν_mass_zero : ((ν.mass : ℝ≥0∞)) = 0 := by
      simpa [hν]
    exact ha <| by simpa [hmass] using hν_mass_zero
  -- Proof comment: rewrite the normalized fiber law as the inverse-mass scaling of the restricted
  -- fiber measure, then evaluate on `ρ ⁻¹' s` and split according to whether `s` contains `a`.
  rw [Measure.map_apply hρmeas hs]
  rw [normalizedFiberLaw, ν.toMeasure_normalize_eq_of_nonzero hν_ne, Measure.smul_apply]
  rw [show ((ν : Measure E) (ρ ⁻¹' s)) = ((μ : Measure E).restrict (ρ ⁻¹' {a}) (ρ ⁻¹' s)) by
        rfl]
  rw [Measure.restrict_apply (hρmeas hs)]
  by_cases hsa : a ∈ s
  · rw [preimage_inter_fiber_eq_fiber_of_mem hsa, hmass]
    have hν_mass_nnreal_ne : ν.mass ≠ 0 := by
      exact (MeasureTheory.FiniteMeasure.mass_nonzero_iff ν).2 hν_ne
    have hν_mass_ne : ((ν.mass : ℝ≥0∞)) ≠ 0 := by
      exact ENNReal.coe_ne_zero.2 ((MeasureTheory.FiniteMeasure.mass_nonzero_iff ν).2 hν_ne)
    have hν_univ_eq : ((ν : Measure E) Set.univ) = ((ν.mass : ℝ≥0∞)) := by
      simpa using (MeasureTheory.FiniteMeasure.ennreal_mass (μ := ν)).symm
    simp [hsa]
    rw [hν_univ_eq]
    rw [ENNReal.coe_inv hν_mass_nnreal_ne]
    exact ENNReal.inv_mul_cancel hν_mass_ne (by simp)
  · rw [preimage_inter_fiber_eq_empty_of_notMem hsa]
    simp [hsa]

/-- Helper for Example 17.55: once the fiber of `a` has positive mass, pushing the normalized
fiber law forward along `ρ` gives the Dirac mass at `a`. -/
private theorem map_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
    [Nonempty E] (μ : ProbabilityMeasure E) {t : Set E} {ρ : E → t} (hρmeas : Measurable ρ)
    (a : t)
    (ha :
      (((μ.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) ≠ 0) :
    Measure.map ρ (((normalizedFiberLaw μ ρ a : ProbabilityMeasure E) : Measure E)) =
      Measure.dirac a := by
  -- Proof comment: the measure equality is now the direct extensional wrapper around the
  -- apply-level normalization bridge.
  ext s hs
  simpa using map_normalizedFiberLaw_apply_of_fiberMass_ne_zero
    (μ := μ) (hρmeas := hρmeas) a ha hs

/-- Helper for Example 17.55: if both fiber masses are nonzero, then pushing the corresponding
product fiber law forward by the pair of representatives gives the Dirac mass at that pair. -/
private theorem map_prod_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
    [Nonempty E] {t : Set E} (P Q : ProbabilityMeasure E) {ρ : E → t}
    (hρmeas : Measurable ρ) (a b : t)
    (ha :
      (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) ≠ 0)
    (hb :
      (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) ≠ 0) :
    Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
      ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
          ProbabilityMeasure (E × E)) : Measure (E × E))) =
        Measure.dirac (a, b) := by
  -- Proof comment: rewrite the pair pushforward as the product of the two marginal
  -- pushforwards, then collapse both factors to Dirac masses on their representatives.
  have hmap :
      Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
          ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
              ProbabilityMeasure (E × E)) : Measure (E × E))) =
        (Measure.map ρ (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E))).prod
          (Measure.map ρ (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E))) := by
    simpa using
      (Measure.map_prod_map
        (μa := (((normalizedFiberLaw P ρ a : ProbabilityMeasure E) : Measure E)))
        (μc := (((normalizedFiberLaw Q ρ b : ProbabilityMeasure E) : Measure E)))
        hρmeas hρmeas).symm
  rw [hmap]
  rw [map_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
      (μ := P) (hρmeas := hρmeas) a ha]
  rw [map_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
      (μ := Q) (hρmeas := hρmeas) b hb]
  exact Measure.dirac_prod_dirac

/-- Helper for Example 17.55: pushing the lifted finite-cell coupling forward by the pair of
representatives recovers the original finite coupling `ν`. -/
private theorem liftedMapCoupling_map_representatives_eq [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)) :
    Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2)) (liftedMapCoupling P Q ρ ν) =
      (ν : Measure (t × t)) := by
  rcases mapCouplingSingletonMarginals (hρmeas := hρmeas) hν with ⟨hrows, hcols⟩
  have hpair_meas : Measurable (fun z : E × E ↦ (ρ z.1, ρ z.2)) := by
    fun_prop
  have hcell_zero_of_left_mass_zero :
      ∀ a b : t,
        (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) = 0 →
          ((ν : Measure (t × t)) {(a, b)}) = 0 := by
    intro a b ha0
    -- Proof comment: if the `a`-fiber has zero mass, then the whole `a`-row of the coupling has
    -- zero mass, so in particular the `(a,b)` cell coefficient vanishes.
    have hle :
        ((ν : Measure (t × t)) {(a, b)}) ≤
          ∑ b' : t, ((ν : Measure (t × t)) {(a, b')}) := by
      exact Finset.single_le_sum
        (f := fun b' : t ↦ ((ν : Measure (t × t)) {(a, b')}))
        (fun _ _ ↦ zero_le _) (Finset.mem_univ b)
    have hrow0 :
        ∑ b' : t, ((ν : Measure (t × t)) {(a, b')}) = 0 := by
      rw [hrows a, ← fiberMass_eq_mapSingleton (μ := P) (hρmeas := hρmeas) a, ha0]
    exact le_antisymm (by simpa [hrow0] using hle) bot_le
  have hcell_zero_of_right_mass_zero :
      ∀ a b : t,
        (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) = 0 →
          ((ν : Measure (t × t)) {(a, b)}) = 0 := by
    intro a b hb0
    -- Proof comment: the same singleton-sum argument on columns kills cells whose `b`-fiber has
    -- zero `Q`-mass.
    have hle :
        ((ν : Measure (t × t)) {(a, b)}) ≤
          ∑ a' : t, ((ν : Measure (t × t)) {(a', b)}) := by
      exact Finset.single_le_sum
        (f := fun a' : t ↦ ((ν : Measure (t × t)) {(a', b)}))
        (fun _ _ ↦ zero_le _) (Finset.mem_univ a)
    have hcol0 :
        ∑ a' : t, ((ν : Measure (t × t)) {(a', b)}) = 0 := by
      rw [hcols b, ← fiberMass_eq_mapSingleton (μ := Q) (hρmeas := hρmeas) b, hb0]
    exact le_antisymm (by simpa [hcol0] using hle) bot_le
  have hcell :
      ∀ a b : t,
        Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
            ((((ν : Measure (t × t)) {(a, b)}) •
                ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                    ProbabilityMeasure (E × E)) : Measure (E × E))))) =
          ((ν : Measure (t × t)) {(a, b)}) • Measure.dirac (a, b) := by
    intro a b
    by_cases ha0 :
        (((P.toFiniteMeasure.restrict (ρ ⁻¹' {a})).mass : ℝ≥0∞)) = 0
    · have hcoeff_zero := hcell_zero_of_left_mass_zero a b ha0
      -- Proof comment: a zero row coefficient annihilates the whole mapped cell.
      have hmap_smul :
          Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
              ((((ν : Measure (t × t)) {(a, b)}) •
                  ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                      ProbabilityMeasure (E × E)) : Measure (E × E))))) =
            ((ν : Measure (t × t)) {(a, b)}) •
              Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                    ProbabilityMeasure (E × E)) : Measure (E × E))) := by
        simpa using
          (Measure.map_smul
            (((ν : Measure (t × t)) {(a, b)}))
            ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                ProbabilityMeasure (E × E)) : Measure (E × E)))
            (fun z : E × E ↦ (ρ z.1, ρ z.2))).symm
      rw [hmap_smul]
      simp [hcoeff_zero]
    · by_cases hb0 :
          (((Q.toFiniteMeasure.restrict (ρ ⁻¹' {b})).mass : ℝ≥0∞)) = 0
      · have hcoeff_zero := hcell_zero_of_right_mass_zero a b hb0
        -- Proof comment: a zero column coefficient gives the symmetric annihilation.
        have hmap_smul :
            Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                ((((ν : Measure (t × t)) {(a, b)}) •
                    ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                        ProbabilityMeasure (E × E)) : Measure (E × E))))) =
              ((ν : Measure (t × t)) {(a, b)}) •
                Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                  ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                      ProbabilityMeasure (E × E)) : Measure (E × E))) := by
          simpa using
            (Measure.map_smul
              (((ν : Measure (t × t)) {(a, b)}))
              ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                  ProbabilityMeasure (E × E)) : Measure (E × E)))
              (fun z : E × E ↦ (ρ z.1, ρ z.2))).symm
        rw [hmap_smul]
        simp [hcoeff_zero]
      · -- Proof comment: when both fiber masses are positive, the mapped product cell collapses
        -- to the Dirac mass at the representative pair.
        have hmap_smul :
            Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                ((((ν : Measure (t × t)) {(a, b)}) •
                    ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                        ProbabilityMeasure (E × E)) : Measure (E × E))))) =
              ((ν : Measure (t × t)) {(a, b)}) •
                Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2))
                  ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                      ProbabilityMeasure (E × E)) : Measure (E × E))) := by
          simpa using
            (Measure.map_smul
              (((ν : Measure (t × t)) {(a, b)}))
              ((((normalizedFiberLaw P ρ a).prod (normalizedFiberLaw Q ρ b) :
                  ProbabilityMeasure (E × E)) : Measure (E × E)))
              (fun z : E × E ↦ (ρ z.1, ρ z.2))).symm
        rw [hmap_smul]
        rw [map_prod_normalizedFiberLaw_eq_dirac_of_fiberMass_ne_zero
          (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) a b ha0 hb0]
  -- Proof comment: after each cell has been identified with its weighted Dirac mass, the whole
  -- lifted pushforward is the canonical sum-of-Diracs expansion of `ν` on the finite target.
  calc
    Measure.map (fun z : E × E ↦ (ρ z.1, ρ z.2)) (liftedMapCoupling P Q ρ ν) =
        ∑ a : t, ∑ b : t, ((ν : Measure (t × t)) {(a, b)}) • Measure.dirac (a, b) := by
      rw [liftedMapCoupling, ← Measure.sum_fintype]
      rw [Measure.map_sum hpair_meas.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro a ha
      rw [← Measure.sum_fintype]
      rw [Measure.map_sum hpair_meas.aemeasurable]
      rw [Measure.sum_fintype]
      refine Finset.sum_congr rfl ?_
      intro b hb
      simpa using hcell a b
    _ = ∑ p : t × t, ((ν : Measure (t × t)) {p}) • Measure.dirac p := by
      simpa [Fintype.sum_prod_type]
    _ = (ν : Measure (t × t)) := by
      simpa [Measure.sum_fintype] using
        (Measure.sum_smul_dirac (μ := (ν : Measure (t × t))))

/-- Helper for Example 17.55: the lifted finite-cell coupling transport cost is bounded by the
finite representative-space cost plus the two mean representative errors. -/
private theorem liftedMapCoupling_transportCost_le_mapCost_addRepresentativeErrors
    [Nonempty E] {t : Set E} [Fintype t]
    (P Q : ProbabilityMeasure E) {ρ : E → t} (hρmeas : Measurable ρ)
    {ν : ProbabilityMeasure (t × t)}
    (hν : IsCoupling ν (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas))
    (hPρ : Integrable (fun x ↦ dist x (ρ x).1) (P : Measure E))
    (hQρ : Integrable (fun x ↦ dist x (ρ x).1) (Q : Measure E)) :
    ∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2) ∂liftedMapCoupling P Q ρ ν ≤
      ∫⁻ ab : t × t, ENNReal.ofReal (dist ab.1.1 ab.2.1) ∂(ν : Measure (t × t)) +
        ENNReal.ofReal
          (∫ x, dist x (ρ x).1 ∂(P : Measure E) +
            ∫ x, dist x (ρ x).1 ∂(Q : Measure E)) := by
  let μ : Measure (E × E) := liftedMapCoupling P Q ρ ν
  let errFst : E × E → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (dist z.1 (ρ z.1).1)
  let coreCost : E × E → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (dist (ρ z.1).1 (ρ z.2).1)
  let errSnd : E × E → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (dist z.2 (ρ z.2).1)
  have herrFst_meas : Measurable errFst := by
    -- Proof comment: the first quantization error is measurable because `ρ` is measurable.
    fun_prop
  have hcoreCost_meas : Measurable coreCost := by
    -- Proof comment: the representative-pair transport cost is a measurable pullback from `t × t`.
    fun_prop
  have herrSnd_meas : Measurable errSnd := by
    -- Proof comment: the second quantization error is the symmetric measurable companion.
    fun_prop
  have hpair_meas : Measurable (fun z : E × E ↦ (ρ z.1, ρ z.2)) := by
    fun_prop
  have hρcost_meas : Measurable (fun x : E ↦ ENNReal.ofReal (dist x (ρ x).1)) := by
    -- Proof comment: the one-coordinate representative error is measurable on `E`.
    fun_prop
  have hrepCost_meas : Measurable (fun ab : t × t ↦ ENNReal.ofReal (dist ab.1.1 ab.2.1)) := by
    -- Proof comment: the finite representative transport cost is measurable on `t × t`.
    fun_prop
  have hpointwise :
      ∀ z : E × E,
        ENNReal.ofReal (dist z.1 z.2) ≤ errFst z + coreCost z + errSnd z := by
    intro z
    have htri :
        dist z.1 z.2 ≤
          dist z.1 (ρ z.1).1 + dist (ρ z.1).1 (ρ z.2).1 + dist z.2 (ρ z.2).1 := by
      calc
        dist z.1 z.2 ≤ dist z.1 (ρ z.1).1 + dist (ρ z.1).1 z.2 := dist_triangle _ _ _
        _ ≤ dist z.1 (ρ z.1).1 +
              (dist (ρ z.1).1 (ρ z.2).1 + dist (ρ z.2).1 z.2) := by
            gcongr
            exact dist_triangle _ _ _
        _ = dist z.1 (ρ z.1).1 + dist (ρ z.1).1 (ρ z.2).1 + dist z.2 (ρ z.2).1 := by
            rw [dist_comm z.2 (ρ z.2).1, add_assoc]
    calc
      ENNReal.ofReal (dist z.1 z.2) ≤
          ENNReal.ofReal
            (dist z.1 (ρ z.1).1 + dist (ρ z.1).1 (ρ z.2).1 + dist z.2 (ρ z.2).1) :=
        ENNReal.ofReal_le_ofReal htri
      _ = ENNReal.ofReal (dist z.1 (ρ z.1).1 + dist (ρ z.1).1 (ρ z.2).1) +
            ENNReal.ofReal (dist z.2 (ρ z.2).1) := by
          rw [ENNReal.ofReal_add (add_nonneg dist_nonneg dist_nonneg) dist_nonneg]
      _ = (ENNReal.ofReal (dist z.1 (ρ z.1).1) +
            ENNReal.ofReal (dist (ρ z.1).1 (ρ z.2).1)) +
            ENNReal.ofReal (dist z.2 (ρ z.2).1) := by
          rw [ENNReal.ofReal_add dist_nonneg dist_nonneg]
      _ = errFst z + coreCost z + errSnd z := by
          simp [errFst, coreCost, errSnd, add_assoc]
  have hErrFst :
      ∫⁻ z : E × E, errFst z ∂μ =
        ENNReal.ofReal (∫ x, dist x (ρ x).1 ∂(P : Measure E)) := by
    -- Proof comment: push the first error term through `Prod.fst`, then rewrite by the first
    -- marginal identity of the lifted coupling.
    calc
      ∫⁻ z : E × E, errFst z ∂μ =
          ∫⁻ x, ENNReal.ofReal (dist x (ρ x).1) ∂Measure.map Prod.fst μ := by
        simpa [μ, errFst] using
          (MeasureTheory.lintegral_map'
            (μ := μ) (f := fun x ↦ ENNReal.ofReal (dist x (ρ x).1)) (g := Prod.fst)
            hρcost_meas.aemeasurable measurable_fst.aemeasurable).symm
      _ = ∫⁻ x, ENNReal.ofReal (dist x (ρ x).1) ∂(P : Measure E) := by
        rw [liftedMapCoupling_fst_eq (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) hν]
      _ = ENNReal.ofReal (∫ x, dist x (ρ x).1 ∂(P : Measure E)) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hPρ]
        exact Filter.Eventually.of_forall fun _ ↦ dist_nonneg
  have hCoreCost :
      ∫⁻ z : E × E, coreCost z ∂μ =
        ∫⁻ ab : t × t, ENNReal.ofReal (dist ab.1.1 ab.2.1) ∂(ν : Measure (t × t)) := by
    -- Proof comment: pushing the lifted coupling forward by the pair of representatives recovers
    -- the finite coupling `ν`, so the core transport term becomes the finite-space cost.
    calc
      ∫⁻ z : E × E, coreCost z ∂μ =
          ∫⁻ ab : t × t, ENNReal.ofReal (dist ab.1.1 ab.2.1) ∂Measure.map
            (fun z : E × E ↦ (ρ z.1, ρ z.2)) μ := by
        simpa [μ, coreCost] using
          (MeasureTheory.lintegral_map'
            (μ := μ) (f := fun ab : t × t ↦ ENNReal.ofReal (dist ab.1.1 ab.2.1))
            (g := fun z : E × E ↦ (ρ z.1, ρ z.2))
            hrepCost_meas.aemeasurable hpair_meas.aemeasurable).symm
      _ = ∫⁻ ab : t × t, ENNReal.ofReal (dist ab.1.1 ab.2.1) ∂(ν : Measure (t × t)) := by
        rw [liftedMapCoupling_map_representatives_eq
          (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) hν]
  have hErrSnd :
      ∫⁻ z : E × E, errSnd z ∂μ =
        ENNReal.ofReal (∫ x, dist x (ρ x).1 ∂(Q : Measure E)) := by
    -- Proof comment: the second error term is the same pushforward rewrite through `Prod.snd`.
    calc
      ∫⁻ z : E × E, errSnd z ∂μ =
          ∫⁻ x, ENNReal.ofReal (dist x (ρ x).1) ∂Measure.map Prod.snd μ := by
        simpa [μ, errSnd] using
          (MeasureTheory.lintegral_map'
            (μ := μ) (f := fun x ↦ ENNReal.ofReal (dist x (ρ x).1)) (g := Prod.snd)
            hρcost_meas.aemeasurable measurable_snd.aemeasurable).symm
      _ = ∫⁻ x, ENNReal.ofReal (dist x (ρ x).1) ∂(Q : Measure E) := by
        rw [liftedMapCoupling_snd_eq (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) hν]
      _ = ENNReal.ofReal (∫ x, dist x (ρ x).1 ∂(Q : Measure E)) := by
        rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hQρ]
        exact Filter.Eventually.of_forall fun _ ↦ dist_nonneg
  have hIntP_nonneg : 0 ≤ ∫ x, dist x (ρ x).1 ∂(P : Measure E) := by
    exact MeasureTheory.integral_nonneg fun _ ↦ dist_nonneg
  have hIntQ_nonneg : 0 ≤ ∫ x, dist x (ρ x).1 ∂(Q : Measure E) := by
    exact MeasureTheory.integral_nonneg fun _ ↦ dist_nonneg
  calc
    ∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2) ∂μ ≤
        ∫⁻ z : E × E, errFst z + coreCost z + errSnd z ∂μ := by
      exact lintegral_mono hpointwise
    _ = (∫⁻ z : E × E, errFst z ∂μ + ∫⁻ z : E × E, coreCost z ∂μ) +
          ∫⁻ z : E × E, errSnd z ∂μ := by
      rw [show (fun z : E × E ↦ errFst z + coreCost z + errSnd z) =
          fun z : E × E ↦ (errFst z + coreCost z) + errSnd z by
            funext z; simp [add_assoc]]
      rw [MeasureTheory.lintegral_add_right'
          (f := fun z : E × E ↦ errFst z + coreCost z)
          (g := errSnd) herrSnd_meas.aemeasurable]
      rw [MeasureTheory.lintegral_add_left' (f := errFst) (g := coreCost)
          herrFst_meas.aemeasurable]
    _ = (∫⁻ ab : t × t, ENNReal.ofReal (dist ab.1.1 ab.2.1) ∂(ν : Measure (t × t)) +
          ENNReal.ofReal (∫ x, dist x (ρ x).1 ∂(P : Measure E))) +
          ENNReal.ofReal (∫ x, dist x (ρ x).1 ∂(Q : Measure E)) := by
      rw [hErrFst, hCoreCost, hErrSnd]
      simp [add_assoc, add_left_comm, add_comm]
    _ = ∫⁻ ab : t × t, ENNReal.ofReal (dist ab.1.1 ab.2.1) ∂(ν : Measure (t × t)) +
          ENNReal.ofReal
            (∫ x, dist x (ρ x).1 ∂(P : Measure E) +
              ∫ x, dist x (ρ x).1 ∂(Q : Measure E)) := by
      rw [show
          (∫⁻ ab : t × t, ENNReal.ofReal (dist ab.1.1 ab.2.1) ∂(ν : Measure (t × t)) +
              ENNReal.ofReal (∫ x, dist x (ρ x).1 ∂(P : Measure E))) +
              ENNReal.ofReal (∫ x, dist x (ρ x).1 ∂(Q : Measure E)) =
            ∫⁻ ab : t × t, ENNReal.ofReal (dist ab.1.1 ab.2.1) ∂(ν : Measure (t × t)) +
              (ENNReal.ofReal (∫ x, dist x (ρ x).1 ∂(P : Measure E)) +
                ENNReal.ofReal (∫ x, dist x (ρ x).1 ∂(Q : Measure E))) by
            simp [add_assoc]]
      rw [← ENNReal.ofReal_add hIntP_nonneg hIntQ_nonneg]

private theorem wassersteinDistance_le_mapRepresentative_addError
    (x₀ : E) {P Q : ProbabilityMeasure E} {t : Set E} (htfin : t.Finite) {ρ : E → t}
    (hρmeas : Measurable ρ)
    (hP : Integrable (fun x ↦ dist x x₀) (P : Measure E))
    (hQ : Integrable (fun x ↦ dist x x₀) (Q : Measure E)) :
    wassersteinDistance P Q ≤
      wassersteinDistance (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas) +
        ENNReal.ofReal
          (∫ x, dist x (ρ x).1 ∂(P : Measure E) +
            ∫ x, dist x (ρ x).1 ∂(Q : Measure E)) := by
  classical
  letI : Fintype t := htfin.fintype
  letI : Nonempty E := P.nonempty
  let Pρ : ProbabilityMeasure t := representativeMapLaw P hρmeas
  let Qρ : ProbabilityMeasure t := representativeMapLaw Q hρmeas
  let err :
      ℝ≥0∞ :=
    ENNReal.ofReal
      (∫ x, dist x (ρ x).1 ∂(P : Measure E) +
        ∫ x, dist x (ρ x).1 ∂(Q : Measure E))
  have hPρ :
      Integrable (fun x ↦ dist x (ρ x).1) (P : Measure E) :=
    integrable_dist_mapRepresentative_of_integrableDist
      (x₀ := x₀) (μ := P) (htfin := htfin) (ρ := ρ) hρmeas hP
  have hQρ :
      Integrable (fun x ↦ dist x (ρ x).1) (Q : Measure E) :=
    integrable_dist_mapRepresentative_of_integrableDist
      (x₀ := x₀) (μ := Q) (htfin := htfin) (ρ := ρ) hρmeas hQ
  let S : Set ℝ≥0∞ :=
    Set.range fun π : WassersteinCoupling Pρ Qρ ↦
      ∫⁻ z : t × t, ENNReal.ofReal (dist z.1.1 z.2.1)
        ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))
  have hcompare :
      ∀ π : WassersteinCoupling Pρ Qρ, wassersteinDistance P Q ≤
        (∫⁻ z : t × t, ENNReal.ofReal (dist z.1.1 z.2.1)
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) + err := by
    intro π
    let πlift : ProbabilityMeasure (E × E) :=
      { val := liftedMapCoupling P Q ρ π.1
        property := by
        -- Proof comment: the first marginal already has total mass one, so every lifted finite
        -- coupling is automatically a probability measure on `E × E`.
          have hmass :
              (liftedMapCoupling P Q ρ π.1) Set.univ = 1 := by
            calc
              (liftedMapCoupling P Q ρ π.1) Set.univ =
                  (Measure.map Prod.fst (liftedMapCoupling P Q ρ π.1)) Set.univ := by
                rw [Measure.map_apply measurable_fst]
                · simp
                · simp
              _ = (P : Measure E) Set.univ := by
                rw [liftedMapCoupling_fst_eq
                  (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) π.2]
              _ = 1 := by simp
          exact IsProbabilityMeasure.mk hmass }
    have hπlift : IsCoupling πlift P Q := by
      constructor
      · -- Proof comment: the lifted measure has first marginal `P` by construction.
        simpa [πlift] using
          liftedMapCoupling_fst_eq (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) π.2
      · -- Proof comment: the second marginal identity is the symmetric companion.
        simpa [πlift] using
          liftedMapCoupling_snd_eq (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) π.2
    have hambient :
        wassersteinDistance P Q ≤
          ∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2) ∂(πlift : Measure (E × E)) := by
      -- Proof comment: the defining infimum is bounded above by the cost of any admissible
      -- ambient coupling, so we use the lift of `π`.
      rw [wassersteinDistance]
      exact sInf_le ⟨⟨πlift, hπlift⟩, rfl⟩
    exact le_trans hambient (by
      simpa [πlift, err] using
        liftedMapCoupling_transportCost_le_mapCost_addRepresentativeErrors
          (P := P) (Q := Q) (ρ := ρ) (hρmeas := hρmeas) π.2 hPρ hQρ)
  calc
    wassersteinDistance P Q ≤ ⨅ r ∈ S, r + err := by
      refine le_iInf ?_
      intro r
      refine le_iInf ?_
      intro hr
      rcases hr with ⟨π, rfl⟩
      exact hcompare π
    _ = wassersteinDistance Pρ Qρ + err := by
      simpa [S, wassersteinDistance] using (ENNReal.sInf_add (s := S) (a := err)).symm
    _ = wassersteinDistance (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas) +
        ENNReal.ofReal
          (∫ x, dist x (ρ x).1 ∂(P : Measure E) +
            ∫ x, dist x (ρ x).1 ∂(Q : Measure E)) := by
      rfl

/-- Helper for Example 17.55: for fixed finite marginals, the finite-coupling constraint set is
closed in the weak topology on probability measures. -/
private theorem isClosed_setOf_isCoupling
    {t : Set E} (P Q : ProbabilityMeasure t) :
    IsClosed {π : ProbabilityMeasure (t × t) | IsCoupling π P Q} := by
  let fstPush : ProbabilityMeasure (t × t) → ProbabilityMeasure t :=
    fun π ↦ π.map continuous_fst.measurable.aemeasurable
  let sndPush : ProbabilityMeasure (t × t) → ProbabilityMeasure t :=
    fun π ↦ π.map continuous_snd.measurable.aemeasurable
  have hfstCont : Continuous fstPush := ProbabilityMeasure.continuous_map continuous_fst
  have hsndCont : Continuous sndPush := ProbabilityMeasure.continuous_map continuous_snd
  have hdescr :
      {π : ProbabilityMeasure (t × t) | IsCoupling π P Q} =
        fstPush ⁻¹' {P} ∩ sndPush ⁻¹' {Q} := by
    -- Proof comment: a coupling is exactly a probability measure whose two coordinate
    -- pushforwards equal the prescribed marginals.
    ext π
    simp [fstPush, sndPush, isCoupling_iff]
  -- Proof comment: the marginal constraints are inverse images of singleton sets under
  -- continuous pushforward maps, hence closed.
  rw [hdescr]
  exact (isClosed_singleton.preimage hfstCont).inter
    (isClosed_singleton.preimage hsndCont)

/-- Helper for Example 17.55: on a finite subtype, the real-valued transport cost depends
continuously on the coupling. -/
private theorem continuous_couplingCost
    {t : Set E} (htfin : t.Finite) :
    Continuous fun π : ProbabilityMeasure (t × t) ↦
      ∫ z : t × t, dist z.1 z.2 ∂(π : Measure (t × t)) := by
  classical
  letI : Fintype t := htfin.fintype
  let costMap : C(t × t, ℝ) := ⟨fun z ↦ dist z.1 z.2, continuous_fst.dist continuous_snd⟩
  -- Proof comment: finite subtypes are compact, so integrating a continuous cost function against
  -- a probability measure varies continuously with the measure.
  simpa [costMap] using
    (ProbabilityMeasure.continuous_integral_continuousMap (f := costMap))

/-- Helper for Example 17.55: on a finite subtype, the transport cost attains its minimum over
all couplings of the prescribed marginals. -/
private theorem existsOptimalFiniteCoupling
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t) :
    ∃ πopt : WassersteinCoupling P Q,
      ∀ π : WassersteinCoupling P Q,
        ∫ z : t × t, dist z.1 z.2 ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) ≤
          ∫ z : t × t, dist z.1 z.2 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
  classical
  letI : Fintype t := htfin.fintype
  let S : Set (ProbabilityMeasure (t × t)) := {π | IsCoupling π P Q}
  have hScompact : IsCompact S := by
    exact (isClosed_setOf_isCoupling (P := P) (Q := Q)).isCompact
  have hSnonempty : S.Nonempty := by
    exact ⟨P.prod Q, isCoupling_prod P Q⟩
  let cost : ProbabilityMeasure (t × t) → ℝ :=
    fun π ↦ ∫ z : t × t, dist z.1 z.2 ∂(π : Measure (t × t))
  obtain ⟨πopt, hπoptS, hminEq, hminLe⟩ :=
    hScompact.exists_sInf_image_eq_and_le hSnonempty
      (continuous_couplingCost (htfin := htfin)).continuousOn
  refine ⟨⟨πopt, hπoptS⟩, ?_⟩
  intro π
  exact hminLe π.1 π.2

/-- Helper for Example 17.55: a feasible finite pair of transport potentials collapses to one
Lipschitz potential that dominates the first potential and negates the second. -/
private theorem existsLipschitzPotential_of_transportInequalities
    {t : Set E} (htfin : t.Finite) {α : ℝ} (hα : 0 ≤ α)
    {u v : t → ℝ}
    (hfeas : ∀ x y, u x + v y ≤ α * dist x y) :
    ∃ g : t → ℝ, LipschitzWith (Real.toNNReal α) g ∧
      (∀ x, u x ≤ g x) ∧
      (∀ y, v y ≤ -g y) := by
  classical
  letI : Fintype t := htfin.fintype
  by_cases hne : Nonempty t
  · let g : t → ℝ := fun x ↦ iInf fun y : t ↦ α * dist x y - v y
    have hB : ∀ x : t, BddBelow (Set.range fun y : t ↦ α * dist x y - v y) := by
      intro x
      rcases hne with ⟨z⟩
      refine ⟨u z - α * dist z x, ?_⟩
      rintro w ⟨y, rfl⟩
      -- Proof comment: one feasible row of the transport inequalities gives a uniform lower bound
      -- for the inf-envelope defining `g x`.
      have htri : dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
      have hmul : α * dist z y ≤ α * (dist z x + dist x y) :=
        mul_le_mul_of_nonneg_left htri hα
      linarith [hfeas z y, hmul]
    have hu_le : ∀ x : t, u x ≤ g x := by
      intro x
      -- Proof comment: the feasibility inequalities place `u x` below every candidate in the
      -- defining infimum, hence below `g x` itself.
      refine le_ciInf fun y ↦ ?_
      linarith [hfeas x y]
    have hv_le : ∀ y : t, v y ≤ -g y := by
      intro y
      -- Proof comment: evaluating the inf-envelope at the diagonal point `y` forces `g y` below
      -- `-v y`, since the transport cost of the diagonal is zero.
      have hdiag : g y ≤ α * dist y y - v y := ciInf_le (hB y) y
      have hdiag' : g y ≤ -v y := by simpa using hdiag
      linarith
    have hgLip : LipschitzWith (Real.toNNReal α) g := by
      -- Proof comment: the inf-envelope is `α`-Lipschitz because every defining term changes by
      -- at most `α * dist x y` when the base point moves from `y` to `x`.
      refine LipschitzWith.of_le_add_mul' α ?_
      intro x y
      rw [← sub_le_iff_le_add]
      refine le_ciInf fun z ↦ ?_
      rw [sub_le_iff_le_add]
      have htri : dist x z ≤ dist x y + dist y z := dist_triangle _ _ _
      have hmul : α * dist x z ≤ α * (dist x y + dist y z) :=
        mul_le_mul_of_nonneg_left htri hα
      have hxz : g x ≤ α * dist x z - v z := ciInf_le (hB x) z
      linarith
    exact ⟨g, hgLip, hu_le, hv_le⟩
  · have hempty : IsEmpty t := ⟨fun x ↦ hne ⟨x⟩⟩
    -- Proof comment: the empty subtype has a unique witness function, and all side conditions are
    -- vacuous.
    refine ⟨fun _ ↦ 0, LipschitzWith.const' (K := Real.toNNReal α) 0, ?_, ?_⟩
    · intro x
      exact False.elim (hempty.false x)
    · intro y
      exact False.elim (hempty.false y)

/-- Helper for Example 17.55: subtracting the anchor value from a finite Lipschitz witness keeps
the witness `1`-Lipschitz and leaves its integral difference unchanged. -/
private theorem anchorShift_integralDifference_eq
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t) {g : t → ℝ}
    (hgLip : LipschitzWith 1 g) :
    ∃ g₀ : t → ℝ, g₀ a₀ = 0 ∧
      LipschitzWith 1 g₀ ∧
      (∫ x, g₀ x ∂(P : Measure t) - ∫ x, g₀ x ∂(Q : Measure t) =
        ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t)) := by
  classical
  letI : Fintype t := htfin.fintype
  let g₀ : t → ℝ := fun x ↦ g x - g a₀
  have hg₀_zero : g₀ a₀ = 0 := by
    simp [g₀]
  have hg₀Lip : LipschitzWith 1 g₀ := by
    -- Proof comment: subtracting a constant preserves the `1`-Lipschitz bound.
    simpa [g₀, sub_eq_add_neg] using hgLip.sub (LipschitzWith.const (g a₀))
  have hPg : Integrable g (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hQg : Integrable g (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hPg₀ :
      ∫ x, g₀ x ∂(P : Measure t) = ∫ x, g x ∂(P : Measure t) - g a₀ := by
    -- Proof comment: anchor-shifting subtracts the same constant from the `P`-expectation.
    calc
      ∫ x, g₀ x ∂(P : Measure t) = ∫ x, (g x + (-g a₀)) ∂(P : Measure t) := by
        simp [g₀, sub_eq_add_neg]
      _ = ∫ x, g x ∂(P : Measure t) + ∫ x, (-g a₀) ∂(P : Measure t) := by
        rw [MeasureTheory.integral_add hPg (integrable_const (-g a₀))]
      _ = ∫ x, g x ∂(P : Measure t) - g a₀ := by
        rw [MeasureTheory.integral_const]
        simp [probReal_univ, sub_eq_add_neg]
  have hQg₀ :
      ∫ x, g₀ x ∂(Q : Measure t) = ∫ x, g x ∂(Q : Measure t) - g a₀ := by
    -- Proof comment: the same constant-cancellation identity holds for the `Q`-expectation.
    calc
      ∫ x, g₀ x ∂(Q : Measure t) = ∫ x, (g x + (-g a₀)) ∂(Q : Measure t) := by
        simp [g₀, sub_eq_add_neg]
      _ = ∫ x, g x ∂(Q : Measure t) + ∫ x, (-g a₀) ∂(Q : Measure t) := by
        rw [MeasureTheory.integral_add hQg (integrable_const (-g a₀))]
      _ = ∫ x, g x ∂(Q : Measure t) - g a₀ := by
        rw [MeasureTheory.integral_const]
        simp [probReal_univ, sub_eq_add_neg]
  refine ⟨g₀, hg₀_zero, hg₀Lip, ?_⟩
  linarith [hPg₀, hQg₀]

/-- Helper for Example 17.55: on a finite subtype, the Wasserstein distance is finite because the
product coupling has finite transport cost. -/
private theorem finiteSubtype_wassersteinDistance_lt_top
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t) :
    wassersteinDistance P Q < ∞ := by
  classical
  letI : Fintype t := htfin.fintype
  let C : ℝ := ∑ z : t × t, dist z.1 z.2
  have hC_nonneg : 0 ≤ C := by
    -- Proof comment: the finite transport-cost bound is a sum of nonnegative distances.
    exact Finset.sum_nonneg fun _ _ ↦ dist_nonneg
  have hbound :
      ∀ z : t × t, ENNReal.ofReal (dist z.1 z.2) ≤ ENNReal.ofReal C := by
    intro z
    refine ENNReal.ofReal_le_ofReal ?_
    exact le_trans
      (Finset.single_le_sum (fun _ _ ↦ dist_nonneg) (Finset.mem_univ z))
      le_rfl
  have hprodCost_lt :
      ∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
          ∂((P.prod Q : ProbabilityMeasure (t × t)) : Measure (t × t)) < ∞ := by
    calc
      ∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
          ∂((P.prod Q : ProbabilityMeasure (t × t)) : Measure (t × t)) ≤
          ∫⁻ _ : t × t, ENNReal.ofReal C
            ∂((P.prod Q : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
        exact lintegral_mono fun z ↦ hbound z
      _ = ENNReal.ofReal C *
            ((P.prod Q : ProbabilityMeasure (t × t)) : Measure (t × t)) Set.univ := by
        rw [lintegral_const]
      _ = ENNReal.ofReal C := by
        simp
      _ < ∞ := ENNReal.ofReal_lt_top
  -- Proof comment: the defining infimum is bounded above by the cost of the product coupling.
  refine lt_of_le_of_lt ?_ hprodCost_lt
  rw [wassersteinDistance]
  exact sInf_le ⟨⟨P.prod Q, isCoupling_prod P Q⟩, rfl⟩

/-- Helper for Example 17.55: the anchored finite dual set always contains `0`, witnessed by the
zero function. -/
private theorem zeroAnchoredPotential_mem_finiteDualSet
    {t : Set E} (a₀ : t) (P Q : ProbabilityMeasure t) :
    0 ∈ {r : ℝ | ∃ g : t → ℝ,
      g a₀ = 0 ∧
        LipschitzWith 1 g ∧
        r = ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t)} := by
  -- Proof comment: the zero function is anchored, `1`-Lipschitz, and has zero signed integral.
  refine ⟨fun _ ↦ 0, by simp, LipschitzWith.const' (K := 1) 0, ?_⟩
  simp

/-- Helper for Example 17.55: an exact anchored finite dual maximizer immediately yields every
strict lower witness below the Wasserstein value. -/
private theorem existsAnchoredPotential_gt_of_lt_of_exactWitness
    {t : Set E} (a₀ : t) (P Q : ProbabilityMeasure t)
    (hexact :
      ∃ g : t → ℝ,
        g a₀ = 0 ∧
          LipschitzWith 1 g ∧
          (wassersteinDistance P Q).toReal =
            ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t)) :
    ∀ r : ℝ, r < (wassersteinDistance P Q).toReal →
      ∃ g : t → ℝ,
        g a₀ = 0 ∧
          LipschitzWith 1 g ∧
          r < ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
  intro r hr
  rcases hexact with ⟨g, hg₀, hgLip, hgEq⟩
  refine ⟨g, hg₀, hgLip, ?_⟩
  -- Proof comment: the exact witness already realizes the Wasserstein value, so every strict
  -- lower real bound is automatically beaten by the same witness.
  rw [← hgEq]
  exact hr

/-- Helper for Example 17.55: on a real-valued metric target, `1`-Lipschitz continuity is
equivalent to the pointwise bound `‖g x - g y‖ ≤ dist x y`. -/
private theorem lipschitzWith_one_iff_norm_sub_le_dist
    {t : Set E} {g : t → ℝ} :
    LipschitzWith 1 g ↔ ∀ x y, ‖g x - g y‖ ≤ dist x y := by
  constructor
  · intro hg x y
    -- Proof comment: specialize the Lipschitz estimate to the pair `(x, y)` and rewrite the real
    -- distance as a norm of the difference.
    simpa [Real.dist_eq] using hg.dist_le_mul x y
  · intro hg
    -- Proof comment: the pointwise norm bound is exactly the defining distance inequality for a
    -- `1`-Lipschitz map.
    refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
    simpa [Real.dist_eq] using hg x y

/-- Helper for Example 17.55: the anchored finite dual feasible set is compact in the product
topology on `t → ℝ`. -/
private theorem anchoredFeasibleSet_isCompact
    {t : Set E} (a₀ : t) :
    IsCompact {g : t → ℝ | g a₀ = 0 ∧ LipschitzWith 1 g} := by
  let box : Set (t → ℝ) := Set.pi Set.univ fun x ↦ Set.Icc (-dist x a₀) (dist x a₀)
  have hbox : IsCompact box := by
    -- Proof comment: each coordinate interval is compact, so Tychonoff gives compactness of the
    -- full product box.
    exact isCompact_univ_pi fun x ↦ isCompact_Icc
  have hclosed :
      IsClosed {g : t → ℝ | g a₀ = 0 ∧ LipschitzWith 1 g} := by
    have hanchor : IsClosed {g : t → ℝ | g a₀ = 0} :=
      isClosed_eq (continuous_apply a₀) continuous_const
    have hlip :
        IsClosed {g : t → ℝ | LipschitzWith 1 g} := by
      have hlip_eq :
          {g : t → ℝ | LipschitzWith 1 g} =
            ⋂ x : t, ⋂ y : t, {g : t → ℝ | ‖g x - g y‖ ≤ dist x y} := by
        ext g
        simpa [lipschitzWith_one_iff_norm_sub_le_dist (g := g)]
      rw [hlip_eq]
      refine isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_
      -- Proof comment: each pairwise Lipschitz constraint is a closed inequality because the
      -- coordinate-difference map is continuous.
      exact isClosed_Iic.preimage (((continuous_apply x).sub (continuous_apply y)).norm)
    -- Proof comment: the anchored feasible set is the intersection of the closed anchor
    -- condition and the closed family of pairwise Lipschitz inequalities.
    simpa [Set.setOf_and] using hanchor.inter hlip
  have hsubset :
      {g : t → ℝ | g a₀ = 0 ∧ LipschitzWith 1 g} ⊆ box := by
    intro g hg
    rcases hg with ⟨hg₀, hgLip⟩
    -- Proof comment: anchoring and `1`-Lipschitz continuity force every coordinate into the
    -- distance box centered at `0`.
    simp [box]
    constructor
    · intro x
      exact (abs_le.mp <| by
        simpa [Real.dist_eq, hg₀, Real.norm_eq_abs] using hgLip.dist_le_mul x a₀).1
    · intro x
      exact (abs_le.mp <| by
        simpa [Real.dist_eq, hg₀, Real.norm_eq_abs] using hgLip.dist_le_mul x a₀).2
  -- Proof comment: a closed subset of the compact coordinate box is compact.
  exact hbox.of_isClosed_subset hclosed hsubset

/-- Helper for Example 17.55: on a finite subtype, the anchored dual objective depends
continuously on the witness function. -/
private theorem continuous_anchoredDualObjective
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t) :
    Continuous fun g : t → ℝ ↦
      ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
  classical
  letI : Fintype t := htfin.fintype
  have hP :
      (fun g : t → ℝ ↦ ∫ x, g x ∂(P : Measure t)) =
        fun g : t → ℝ ↦ ∑ x, (P : Measure t).real {x} * g x := by
    funext g
    -- Proof comment: on the finite subtype, the `P`-integral is a finite weighted sum of the
    -- coordinate evaluations.
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_fintype (μ := (P : Measure t)) (f := g)
        (MeasureTheory.Integrable.of_finite : Integrable g (P : Measure t)))
  have hQ :
      (fun g : t → ℝ ↦ ∫ x, g x ∂(Q : Measure t)) =
        fun g : t → ℝ ↦ ∑ x, (Q : Measure t).real {x} * g x := by
    funext g
    -- Proof comment: the same finite-sum formula holds for the `Q`-integral.
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_fintype (μ := (Q : Measure t)) (f := g)
        (MeasureTheory.Integrable.of_finite : Integrable g (Q : Measure t)))
  have hcontP :
      Continuous fun g : t → ℝ ↦ ∑ x, (P : Measure t).real {x} * g x := by
    -- Proof comment: finite sums of coordinate evaluations are continuous in the product
    -- topology.
    fun_prop
  have hcontQ :
      Continuous fun g : t → ℝ ↦ ∑ x, (Q : Measure t).real {x} * g x := by
    -- Proof comment: the same continuity statement holds for the `Q`-integral rewrite.
    fun_prop
  have hcontP' : Continuous fun g : t → ℝ ↦ ∫ x, g x ∂(P : Measure t) := by
    simpa [hP] using hcontP
  have hcontQ' : Continuous fun g : t → ℝ ↦ ∫ x, g x ∂(Q : Measure t) := by
    simpa [hQ] using hcontQ
  -- Proof comment: subtract the two continuous finite-sum functionals.
  exact hcontP'.sub hcontQ'

/-- Helper for Example 17.55: compactness of the anchored feasible set yields a maximizing
anchored finite Kantorovich potential. -/
private theorem existsMaximizingAnchoredPotential
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t) :
    ∃ g : t → ℝ,
      g a₀ = 0 ∧
        LipschitzWith 1 g ∧
        ∀ h : t → ℝ, h a₀ = 0 → LipschitzWith 1 h →
          ∫ x, h x ∂(P : Measure t) - ∫ x, h x ∂(Q : Measure t) ≤
            ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
  let feasible : Set (t → ℝ) := {g : t → ℝ | g a₀ = 0 ∧ LipschitzWith 1 g}
  have hcompact : IsCompact feasible := by
    simpa [feasible] using anchoredFeasibleSet_isCompact (a₀ := a₀)
  have hnonempty : feasible.Nonempty := by
    refine ⟨fun _ ↦ 0, ?_⟩
    exact ⟨by simp [feasible], LipschitzWith.const' (K := 1) 0⟩
  have hcont :
      ContinuousOn
        (fun g : t → ℝ ↦
          ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t))
        feasible :=
    (continuous_anchoredDualObjective (htfin := htfin) P Q).continuousOn
  obtain ⟨g, hgmem, hgmax⟩ := hcompact.exists_isMaxOn hnonempty hcont
  refine ⟨g, hgmem.1, hgmem.2, ?_⟩
  intro h hh₀ hhLip
  -- Proof comment: the point selected by compactness dominates every other feasible anchored
  -- witness by maximality on the feasible set.
  exact hgmax ⟨hh₀, hhLip⟩

/-- Helper for Example 17.55: every coupling on a finite subtype has finite transport cost. -/
private theorem finiteCoupling_cost_lt_top
    {t : Set E} (htfin : t.Finite) {P Q : ProbabilityMeasure t}
    (π : WassersteinCoupling P Q) :
    ∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
        ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) < ∞ := by
  classical
  letI : Fintype t := htfin.fintype
  let C : ℝ := ∑ z : t × t, dist z.1 z.2
  have hbound :
      ∀ z : t × t, ENNReal.ofReal (dist z.1 z.2) ≤ ENNReal.ofReal C := by
    intro z
    refine ENNReal.ofReal_le_ofReal ?_
    exact le_trans
      (Finset.single_le_sum (fun _ _ ↦ dist_nonneg) (Finset.mem_univ z))
      le_rfl
  -- Proof comment: the finite transport cost is uniformly bounded by the total distance sum over
  -- the whole finite product space.
  calc
    ∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
        ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) ≤
        ∫⁻ _ : t × t, ENNReal.ofReal C
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
      exact lintegral_mono fun z ↦ hbound z
    _ = ENNReal.ofReal C *
          ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) Set.univ := by
      rw [lintegral_const]
    _ = ENNReal.ofReal C := by simp
    _ < ∞ := ENNReal.ofReal_lt_top

/-- Helper for Example 17.55: every anchored finite dual witness is bounded above by the finite
Wasserstein value. -/
private theorem anchoredPotential_objective_le_wassersteinDistance
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t) {g : t → ℝ}
    (hg₀ : g a₀ = 0) (hgLip : LipschitzWith 1 g) :
    ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) ≤
      (wassersteinDistance P Q).toReal := by
  letI : Finite t := htfin.to_subtype
  have hW_ne_top : wassersteinDistance P Q ≠ ∞ := by
    exact (ne_of_lt (finiteSubtype_wassersteinDistance_lt_top htfin P Q))
  have hdual_le :
      ENNReal.ofReal
          (∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t)) ≤
        wassersteinDistance P Q := by
    rw [wassersteinDistance]
    refine le_sInf ?_
    rintro _ ⟨π, rfl⟩
    have hπcost_lt :
        ∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
            ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) < ∞ :=
      finiteCoupling_cost_lt_top (htfin := htfin) π
    -- Proof comment: weak duality holds against every coupling separately, so it also holds
    -- against the infimum over all couplings.
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt hπcost_lt)).2 <|
      lipschitzIntegralDifference_le_couplingCost
        (x₀ := a₀) (P := P) (Q := Q) (π := π.1) π.2 hg₀ hgLip
        MeasureTheory.Integrable.of_finite MeasureTheory.Integrable.of_finite
  -- Proof comment: the finite Wasserstein value is not `∞`, so the `ENNReal` comparison turns
  -- back into the desired real inequality.
  exact (ENNReal.ofReal_le_iff_le_toReal hW_ne_top).1 hdual_le

/-- Helper for Example 17.55: if a finite transport-potential pair is tight on every positive-mass
edge of a coupling, then its dual objective equals that coupling cost. -/
private theorem supportTightPair_objective_eq_couplingCost
    {t : Set E} (htfin : t.Finite) {P Q : ProbabilityMeasure t}
    (π : WassersteinCoupling P Q) {u v : t → ℝ}
    (htight :
      ∀ x y, ((π.1 : Measure (t × t)) {(x, y)}) ≠ 0 → u x + v y = dist x y) :
    ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
      ∫ z : t × t, dist z.1 z.2 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
  classical
  letI : Fintype t := htfin.fintype
  rcases π.2 with ⟨hfst, hsnd⟩
  have hIntU : Integrable u (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hIntV : Integrable v (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hIntUFstMap :
      Integrable u ((((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)).fst)) := by
    rw [hfst]
    exact hIntU
  have hIntVSndMap :
      Integrable v ((((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)).snd)) := by
    rw [hsnd]
    exact hIntV
  have hUAEStronglyMeasurable :
      AEStronglyMeasurable u
        (Measure.map Prod.fst ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) := by
    simpa [Measure.fst] using hIntUFstMap.aestronglyMeasurable
  have hVAEStronglyMeasurable :
      AEStronglyMeasurable v
        (Measure.map Prod.snd ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) := by
    simpa [Measure.snd] using hIntVSndMap.aestronglyMeasurable
  have hIntUFst :
      Integrable (fun z : t × t ↦ u z.1) ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
    -- Proof comment: transport the integrability of `u` along the first projection of the
    -- coupling.
    simpa [Measure.fst] using hIntUFstMap.comp_measurable measurable_fst
  have hIntVSnd :
      Integrable (fun z : t × t ↦ v z.2) ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
    -- Proof comment: the second coordinate is handled by the same marginal rewrite.
    simpa [Measure.snd] using hIntVSndMap.comp_measurable measurable_snd
  have hfstIntegral :
      ∫ z : t × t, u z.1 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        ∫ x, u x ∂(P : Measure t) := by
    -- Proof comment: rewrite the first-coordinate integral under the coupling as the integral
    -- against the first marginal, then use the coupling identity.
    calc
      ∫ z : t × t, u z.1 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
          ∫ x, u x ∂((((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)).fst)) := by
        simpa [Measure.fst] using
          (MeasureTheory.integral_map
            (μ := ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)))
            measurable_fst.aemeasurable (f := u) hUAEStronglyMeasurable).symm
      _ = ∫ x, u x ∂(P : Measure t) := by rw [hfst]
  have hsndIntegral :
      ∫ z : t × t, v z.2 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        ∫ y, v y ∂(Q : Measure t) := by
    -- Proof comment: the second marginal gives the same rewrite for `v`.
    calc
      ∫ z : t × t, v z.2 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
          ∫ y, v y ∂((((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)).snd)) := by
        simpa [Measure.snd] using
          (MeasureTheory.integral_map
            (μ := ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)))
            measurable_snd.aemeasurable (f := v) hVAEStronglyMeasurable).symm
      _ = ∫ y, v y ∂(Q : Measure t) := by rw [hsnd]
  have hpairIntegral :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∫ z : t × t, (u z.1 + v z.2)
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
    -- Proof comment: after both marginal rewrites, the pair objective becomes the integral of
    -- the pointwise pair sum along the coupling.
    calc
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
          ∫ z : t × t, u z.1 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) +
            ∫ z : t × t, v z.2 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
        rw [hfstIntegral, hsndIntegral]
      _ =
          ∫ z : t × t, (u z.1 + v z.2)
            ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
        rw [← MeasureTheory.integral_add hIntUFst hIntVSnd]
  have hcostInt :
      Integrable (fun z : t × t ↦ dist z.1 z.2)
        (((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) :=
    MeasureTheory.Integrable.of_finite
  calc
    ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∑ z : t × t, (((π.1 : Measure (t × t)).real {z}) * (u z.1 + v z.2)) := by
      rw [hpairIntegral]
      simpa [smul_eq_mul] using
        (MeasureTheory.integral_fintype
          (μ := ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)))
          (f := fun z : t × t ↦ u z.1 + v z.2)
          (MeasureTheory.Integrable.of_finite :
            Integrable (fun z : t × t ↦ u z.1 + v z.2)
              (((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))))
          )
    _ = ∑ z : t × t, (((π.1 : Measure (t × t)).real {z}) * dist z.1 z.2) := by
      -- Proof comment: every summand with positive coupling mass is tight by assumption, and
      -- zero-mass summands vanish automatically.
      refine Finset.sum_congr rfl ?_
      intro z hz
      by_cases hmass : ((π.1 : Measure (t × t)) {z}) = 0
      · simp [Measure.real_def, hmass]
      · rw [htight z.1 z.2 (by simpa using hmass)]
    _ =
        ∫ z : t × t, dist z.1 z.2 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
      simpa [smul_eq_mul] using
        (MeasureTheory.integral_fintype
          (μ := ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)))
          (f := fun z : t × t ↦ dist z.1 z.2)
          hcostInt).symm

/-- Helper for Example 17.55: the dual objective of a finite transport-potential pair can be
rewritten as the coupling integral of its pointwise pair sum. -/
private theorem transportPotentialPair_objective_eq_integral_pairSum
    {t : Set E} (htfin : t.Finite) {P Q : ProbabilityMeasure t}
    (π : WassersteinCoupling P Q) {u v : t → ℝ} :
    ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
      ∫ z : t × t, (u z.1 + v z.2)
        ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
  classical
  letI : Fintype t := htfin.fintype
  rcases π.2 with ⟨hfst, hsnd⟩
  have hIntU : Integrable u (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hIntV : Integrable v (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hIntUFstMap :
      Integrable u ((((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)).fst)) := by
    rw [hfst]
    exact hIntU
  have hIntVSndMap :
      Integrable v ((((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)).snd)) := by
    rw [hsnd]
    exact hIntV
  have hUAEStronglyMeasurable :
      AEStronglyMeasurable u
        (Measure.map Prod.fst ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) := by
    simpa [Measure.fst] using hIntUFstMap.aestronglyMeasurable
  have hVAEStronglyMeasurable :
      AEStronglyMeasurable v
        (Measure.map Prod.snd ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) := by
    simpa [Measure.snd] using hIntVSndMap.aestronglyMeasurable
  have hIntUFst :
      Integrable (fun z : t × t ↦ u z.1) ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
    -- Proof comment: pull the first potential back along the first projection of the coupling.
    simpa [Measure.fst] using hIntUFstMap.comp_measurable measurable_fst
  have hIntVSnd :
      Integrable (fun z : t × t ↦ v z.2) ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
    -- Proof comment: the same projection rewrite handles the second potential.
    simpa [Measure.snd] using hIntVSndMap.comp_measurable measurable_snd
  have hfstIntegral :
      ∫ z : t × t, u z.1 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        ∫ x, u x ∂(P : Measure t) := by
    -- Proof comment: rewrite the first-coordinate integral through the first marginal of the
    -- coupling, then apply the coupling identity.
    calc
      ∫ z : t × t, u z.1 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
          ∫ x, u x ∂((((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)).fst)) := by
        simpa [Measure.fst] using
          (MeasureTheory.integral_map
            (μ := ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)))
            measurable_fst.aemeasurable (f := u) hUAEStronglyMeasurable).symm
      _ = ∫ x, u x ∂(P : Measure t) := by rw [hfst]
  have hsndIntegral :
      ∫ z : t × t, v z.2 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        ∫ y, v y ∂(Q : Measure t) := by
    -- Proof comment: rewrite the second-coordinate integral through the second marginal.
    calc
      ∫ z : t × t, v z.2 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
          ∫ y, v y ∂((((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)).snd)) := by
        simpa [Measure.snd] using
          (MeasureTheory.integral_map
            (μ := ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)))
            measurable_snd.aemeasurable (f := v) hVAEStronglyMeasurable).symm
      _ = ∫ y, v y ∂(Q : Measure t) := by rw [hsnd]
  -- Proof comment: after both marginal rewrites, the pair objective is exactly the integral of
  -- the pointwise pair sum along the coupling.
  calc
    ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∫ z : t × t, u z.1 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) +
          ∫ z : t × t, v z.2 ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
      rw [hfstIntegral, hsndIntegral]
    _ =
        ∫ z : t × t, (u z.1 + v z.2)
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
      rw [← MeasureTheory.integral_add hIntUFst hIntVSnd]

/-- Helper for Example 17.55: on a finite subtype, an optimal coupling realizes the real value of
`wassersteinDistance`. -/
private theorem optimalFiniteCoupling_cost_eq_toReal
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t) :
    ∃ πopt : WassersteinCoupling P Q,
      ∫ z : t × t, dist z.1 z.2 ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        (wassersteinDistance P Q).toReal := by
  classical
  letI : Fintype t := htfin.fintype
  obtain ⟨πopt, hopt⟩ := existsOptimalFiniteCoupling (htfin := htfin) P Q
  let costE : WassersteinCoupling P Q → ℝ≥0∞ := fun π ↦
    ∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
      ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))
  have hcostFinite : ∀ π : WassersteinCoupling P Q, costE π < ∞ := by
    intro π
    let C : ℝ := ∑ z : t × t, dist z.1 z.2
    have hbound :
        ∀ z : t × t, ENNReal.ofReal (dist z.1 z.2) ≤ ENNReal.ofReal C := by
      intro z
      refine ENNReal.ofReal_le_ofReal ?_
      exact le_trans
        (Finset.single_le_sum (fun _ _ ↦ dist_nonneg) (Finset.mem_univ z))
        le_rfl
    -- Proof comment: every finite coupling cost is bounded by the finite constant obtained by
    -- summing the distance over the whole finite product space.
    calc
      costE π ≤ ∫⁻ _ : t × t, ENNReal.ofReal C
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
        exact lintegral_mono fun z ↦ hbound z
      _ = ENNReal.ofReal C *
          ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) Set.univ := by
        rw [lintegral_const]
      _ = ENNReal.ofReal C := by simp
      _ < ∞ := ENNReal.ofReal_lt_top
  have hcostToReal :
      ∀ π : WassersteinCoupling P Q,
        (costE π).toReal =
          ∫ z : t × t, dist z.1 z.2
            ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
    intro π
    -- Proof comment: the finite-space transport integrand is nonnegative, so its real integral
    -- is the `toReal` of the associated nonnegative Lebesgue integral.
    symm
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z ↦ dist_nonneg)
      ((continuous_fst.dist continuous_snd).aestronglyMeasurable)
  have hcostEq :
      ∀ π : WassersteinCoupling P Q,
        costE π =
          ENNReal.ofReal
            (∫ z : t × t, dist z.1 z.2
              ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) := by
    intro π
    -- Proof comment: after proving the cost is finite, the `ENNReal` cost is exactly the
    -- `ofReal` of the ordinary integral.
    calc
      costE π = ENNReal.ofReal ((costE π).toReal) := by
        rw [ENNReal.ofReal_toReal (ne_of_lt (hcostFinite π))]
      _ = ENNReal.ofReal
          (∫ z : t × t, dist z.1 z.2
            ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) := by
        rw [hcostToReal π]
  have hcost_le_wasserstein : costE πopt ≤ wassersteinDistance P Q := by
    rw [wassersteinDistance]
    refine le_sInf ?_
    rintro _ ⟨π, rfl⟩
    -- Proof comment: optimality of `πopt` in the real formulation turns into an `ENNReal`
    -- lower-bound statement for the entire coupling-cost range.
    rw [hcostEq πopt]
    change ENNReal.ofReal
        (∫ z : t × t, dist z.1 z.2
          ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) ≤ costE π
    rw [hcostEq π]
    exact ENNReal.ofReal_le_ofReal (hopt π)
  have hwasserstein_le_cost : wassersteinDistance P Q ≤ costE πopt := by
    -- Proof comment: the optimal coupling cost is itself one element of the infimum range.
    rw [wassersteinDistance]
    exact sInf_le ⟨πopt, rfl⟩
  refine ⟨πopt, ?_⟩
  -- Proof comment: combine the two infimum inequalities to identify the optimal real cost with
  -- the finite Wasserstein value.
  calc
    ∫ z : t × t, dist z.1 z.2 ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        (costE πopt).toReal := by
      rw [hcostToReal πopt]
    _ = (wassersteinDistance P Q).toReal := by
      rw [le_antisymm hcost_le_wasserstein hwasserstein_le_cost]

/-- Helper for Example 17.55: among all feasible finite transport-potential pairs, there is one
whose objective is maximal. -/
private theorem existsMaximizingTransportPotentialPair
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t) :
    ∃ u v : t → ℝ,
      (∀ x y, u x + v y ≤ dist x y) ∧
        ∀ u' v' : t → ℝ, (∀ x y, u' x + v' y ≤ dist x y) →
          ∫ x, u' x ∂(P : Measure t) + ∫ y, v' y ∂(Q : Measure t) ≤
            ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := by
  classical
  letI : Fintype t := htfin.fintype
  let a₀ : t := Classical.choice P.nonempty
  obtain ⟨g, hg₀, hgLip, hgmax⟩ :=
    existsMaximizingAnchoredPotential (htfin := htfin) (a₀ := a₀) P Q
  refine ⟨g, fun y ↦ -g y, ?_, ?_⟩
  · intro x y
    -- Proof comment: the maximizing anchored witness yields a feasible pair via `(g, -g)`
    -- because `1`-Lipschitz continuity rewrites exactly as the transport inequality.
    have hxy : g x ≤ g y + dist x y := by
      simpa using hgLip.le_add_mul x y
    linarith
  · intro u' v' hfeas'
    have hfeasOne : ∀ x y, u' x + v' y ≤ (1 : ℝ) * dist x y := by
      intro x y
      simpa using hfeas' x y
    obtain ⟨h, hhLip, hu'_le, hv'_le⟩ :=
      existsLipschitzPotential_of_transportInequalities
        (htfin := htfin) (α := 1) (hα := zero_le_one) hfeasOne
    have hhLipOne : LipschitzWith 1 h := by
      simpa using hhLip
    obtain ⟨h₀, hh₀, hh₀Lip, hh₀Eq⟩ :=
      anchorShift_integralDifference_eq (htfin := htfin) a₀ P Q hhLipOne
    have hPIntU' : Integrable u' (P : Measure t) := MeasureTheory.Integrable.of_finite
    have hQIntV' : Integrable v' (Q : Measure t) := MeasureTheory.Integrable.of_finite
    have hPIntH : Integrable h (P : Measure t) := MeasureTheory.Integrable.of_finite
    have hQIntH : Integrable h (Q : Measure t) := MeasureTheory.Integrable.of_finite
    have hPmono :
        ∫ x, u' x ∂(P : Measure t) ≤ ∫ x, h x ∂(P : Measure t) := by
      -- Proof comment: the envelope potential dominates the first coordinate of every feasible
      -- pair pointwise, so its integral dominates the first marginal objective.
      refine MeasureTheory.integral_mono hPIntU' hPIntH ?_
      intro x
      exact hu'_le x
    have hQmono :
        ∫ y, v' y ∂(Q : Measure t) ≤ ∫ y, -h y ∂(Q : Measure t) := by
      -- Proof comment: the same envelope bounds the second coordinate by `-h`.
      refine MeasureTheory.integral_mono hQIntV' hQIntH.neg ?_
      intro y
      exact hv'_le y
    have hQnegH :
        ∫ y, -h y ∂(Q : Measure t) = -∫ y, h y ∂(Q : Measure t) := by
      simpa using MeasureTheory.integral_neg (f := h) (μ := (Q : Measure t))
    have hQnegG :
        ∫ y, (-g y) ∂(Q : Measure t) = -∫ y, g y ∂(Q : Measure t) := by
      simpa using MeasureTheory.integral_neg (f := g) (μ := (Q : Measure t))
    have hpair_le_h :
        ∫ x, u' x ∂(P : Measure t) + ∫ y, v' y ∂(Q : Measure t) ≤
          ∫ x, h x ∂(P : Measure t) - ∫ y, h y ∂(Q : Measure t) := by
      -- Proof comment: combining the two pointwise envelope bounds collapses the pair objective
      -- to the single-potential dual objective.
      linarith
    have hh_le_g :
        ∫ x, h x ∂(P : Measure t) - ∫ y, h y ∂(Q : Measure t) ≤
          ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) := by
      -- Proof comment: after re-anchoring `h` at the chosen base point, maximality of `g`
      -- over anchored `1`-Lipschitz witnesses applies directly.
      have hh₀max :
          ∫ x, h₀ x ∂(P : Measure t) - ∫ y, h₀ y ∂(Q : Measure t) ≤
            ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) :=
        hgmax h₀ hh₀ hh₀Lip
      rwa [hh₀Eq] at hh₀max
    -- Proof comment: the maximizing anchored witness `g` and the feasible pair `(g, -g)` have
    -- the same objective, so the pair chosen above dominates every feasible competitor.
    linarith

/-- Helper for Example 17.55: a maximizing feasible finite transport-potential pair induces an
anchored maximizing `1`-Lipschitz potential with the same objective value. -/
private theorem maximizingTransportPotentialPair_inducesAnchoredPotential
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t) {u v : t → ℝ}
    (hfeas : ∀ x y, u x + v y ≤ dist x y)
    (hmax :
      ∀ u' v' : t → ℝ, (∀ x y, u' x + v' y ≤ dist x y) →
        ∫ x, u' x ∂(P : Measure t) + ∫ y, v' y ∂(Q : Measure t) ≤
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t)) :
    ∃ g : t → ℝ,
      g a₀ = 0 ∧
        LipschitzWith 1 g ∧
        (∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
          ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t)) ∧
        (∀ h : t → ℝ, h a₀ = 0 → LipschitzWith 1 h →
          ∫ x, h x ∂(P : Measure t) - ∫ y, h y ∂(Q : Measure t) ≤
            ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t)) := by
  classical
  letI : Fintype t := htfin.fintype
  have hfeasOne : ∀ x y, u x + v y ≤ (1 : ℝ) * dist x y := by
    intro x y
    simpa using hfeas x y
  obtain ⟨g, hgLip, hu_le, hv_le⟩ :=
    existsLipschitzPotential_of_transportInequalities
      (htfin := htfin) (α := 1) (hα := zero_le_one) hfeasOne
  have hgLipOne : LipschitzWith 1 g := by
    simpa using hgLip
  have hPIntU : Integrable u (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hQIntV : Integrable v (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hPIntG : Integrable g (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hQIntG : Integrable g (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hPmono :
      ∫ x, u x ∂(P : Measure t) ≤ ∫ x, g x ∂(P : Measure t) := by
    -- Proof comment: the transport envelope dominates the first potential pointwise.
    refine MeasureTheory.integral_mono hPIntU hPIntG ?_
    intro x
    exact hu_le x
  have hQmono :
      ∫ y, v y ∂(Q : Measure t) ≤ ∫ y, -g y ∂(Q : Measure t) := by
    -- Proof comment: the same envelope bounds the second potential above by `-g`.
    refine MeasureTheory.integral_mono hQIntV hQIntG.neg ?_
    intro y
    exact hv_le y
  have hQnegG :
      ∫ y, -g y ∂(Q : Measure t) = -∫ y, g y ∂(Q : Measure t) := by
    simpa using MeasureTheory.integral_neg (f := g) (μ := (Q : Measure t))
  have hpair_le_g :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) ≤
        ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) := by
    -- Proof comment: integrating the envelope bounds turns the pair objective into the
    -- single-potential objective of `g`.
    linarith
  have hgfeas :
      ∀ x y, g x + (-g y) ≤ dist x y := by
    intro x y
    have hxy : g x ≤ g y + dist x y := by
      simpa using hgLipOne.le_add_mul x y
    linarith
  have hg_pair_le :
      ∫ x, g x ∂(P : Measure t) + ∫ y, (-g y) ∂(Q : Measure t) ≤
        ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) :=
    hmax g (fun y ↦ -g y) hgfeas
  have hobjEqG :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) := by
    -- Proof comment: maximality of the original pair forces equality with the envelope pair.
    linarith
  obtain ⟨g₀, hg₀, hg₀Lip, hg₀Eq⟩ :=
    anchorShift_integralDifference_eq (htfin := htfin) a₀ P Q hgLipOne
  have hobjEqG₀ :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∫ x, g₀ x ∂(P : Measure t) - ∫ y, g₀ y ∂(Q : Measure t) := by
    -- Proof comment: re-anchoring the maximizing envelope leaves its signed objective unchanged.
    rw [hobjEqG]
    exact hg₀Eq.symm
  refine ⟨g₀, hg₀, hg₀Lip, hobjEqG₀, ?_⟩
  intro h hh₀ hhLip
  have hhfeas :
      ∀ x y, h x + (-h y) ≤ dist x y := by
    intro x y
    have hxy : h x ≤ h y + dist x y := by
      simpa using hhLip.le_add_mul x y
    linarith
  have hhmax :
      ∫ x, h x ∂(P : Measure t) + ∫ y, (-h y) ∂(Q : Measure t) ≤
        ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) :=
    hmax h (fun y ↦ -h y) hhfeas
  have hQnegH :
      ∫ y, (-h y) ∂(Q : Measure t) = -∫ y, h y ∂(Q : Measure t) := by
    simpa using MeasureTheory.integral_neg (f := h) (μ := (Q : Measure t))
  -- Proof comment: every anchored `1`-Lipschitz witness defines a feasible pair `(h, -h)`,
  -- so pair maximality turns into anchored dual maximality.
  linarith

/-- Helper for Example 17.55: once a finite anchored `1`-Lipschitz witness is known to maximize
the anchored dual problem, the remaining frontier is to identify its value with
`(wassersteinDistance P Q).toReal`. -/
private theorem existsExactAnchoredPotential_of_transportPotentialPair
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t)
    {u v : t → ℝ}
    (hfeas : ∀ x y, u x + v y ≤ dist x y)
    (hobj :
      (wassersteinDistance P Q).toReal =
        ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t)) :
    ∃ g : t → ℝ,
      g a₀ = 0 ∧
        LipschitzWith 1 g ∧
        (wassersteinDistance P Q).toReal =
          ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
  classical
  letI : Fintype t := htfin.fintype
  have hPIntU : Integrable u (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hQIntV : Integrable v (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hfeasOne : ∀ x y, u x + v y ≤ (1 : ℝ) * dist x y := by
    intro x y
    simpa using hfeas x y
  obtain ⟨g, hgLip, hu_le, hv_le⟩ :=
    existsLipschitzPotential_of_transportInequalities
      (htfin := htfin) (α := 1) (hα := zero_le_one) hfeasOne
  have hgLipOne : LipschitzWith 1 g := by
    -- Proof comment: the envelope theorem is already normalized to the transport inequality with
    -- coefficient `1`, so it returns a `1`-Lipschitz witness.
    simpa using hgLip
  have hPIntG : Integrable g (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hQIntG : Integrable g (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hPmono :
      ∫ x, u x ∂(P : Measure t) ≤ ∫ x, g x ∂(P : Measure t) := by
    -- Proof comment: the envelope dominates the first transport potential pointwise.
    refine MeasureTheory.integral_mono hPIntU hPIntG ?_
    intro x
    exact hu_le x
  have hQmono :
      ∫ y, v y ∂(Q : Measure t) ≤ ∫ y, -g y ∂(Q : Measure t) := by
    -- Proof comment: the same envelope bounds the second transport potential above by `-g`.
    refine MeasureTheory.integral_mono hQIntV hQIntG.neg ?_
    intro y
    exact hv_le y
  have hQneg :
      ∫ y, -g y ∂(Q : Measure t) = -∫ y, g y ∂(Q : Measure t) := by
    -- Proof comment: rewrite the second envelope bound into the signed dual objective.
    simpa using MeasureTheory.integral_neg (f := g) (μ := (Q : Measure t))
  have hpair_le_g :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) ≤
        ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
    -- Proof comment: combining the two monotonicity inequalities upgrades the pair objective to
    -- the single-potential objective of the envelope.
    linarith
  obtain ⟨g₀, hg₀, hg₀Lip, hg₀Eq⟩ :=
    anchorShift_integralDifference_eq (htfin := htfin) a₀ P Q hgLipOne
  have hg₀_le :
      ∫ x, g₀ x ∂(P : Measure t) - ∫ x, g₀ x ∂(Q : Measure t) ≤
        (wassersteinDistance P Q).toReal :=
    anchoredPotential_objective_le_wassersteinDistance
      (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q) hg₀ hg₀Lip
  have hg₀_ge :
      (wassersteinDistance P Q).toReal ≤
        ∫ x, g₀ x ∂(P : Measure t) - ∫ x, g₀ x ∂(Q : Measure t) := by
    -- Proof comment: the anchored translate keeps the envelope objective, and that objective
    -- dominates the exact pair value by the pointwise envelope bounds.
    rw [hg₀Eq]
    linarith [hobj, hpair_le_g]
  refine ⟨g₀, hg₀, hg₀Lip, ?_⟩
  exact le_antisymm hg₀_ge hg₀_le

/-- Helper for Example 17.55: the strict anchored-witness theorem reduces to a single owner
exact-witness theorem for one optimal finite coupling. -/
private theorem transportPotentialPair_objective_le_couplingCost
    {t : Set E} (htfin : t.Finite) {P Q : ProbabilityMeasure t}
    (π : WassersteinCoupling P Q) {u v : t → ℝ}
    (hfeas : ∀ x y, u x + v y ≤ dist x y) :
    ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) ≤
      ∫ z : t × t, dist z.1 z.2
        ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
  classical
  letI : Fintype t := htfin.fintype
  have hpairIntegral :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∫ z : t × t, (u z.1 + v z.2)
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) :=
    transportPotentialPair_objective_eq_integral_pairSum
      (htfin := htfin) (π := π)
  have hpairInt :
      Integrable (fun z : t × t ↦ u z.1 + v z.2)
        (((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) :=
    MeasureTheory.Integrable.of_finite
  have hcostInt :
      Integrable (fun z : t × t ↦ dist z.1 z.2)
        (((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) :=
    MeasureTheory.Integrable.of_finite
  -- Proof comment: rewrite the pair objective through the coupling, then compare the two
  -- integrands pointwise using feasibility.
  calc
    ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∫ z : t × t, (u z.1 + v z.2)
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := hpairIntegral
    _ ≤
        ∫ z : t × t, dist z.1 z.2
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
      refine MeasureTheory.integral_mono hpairInt hcostInt ?_
      intro z
      exact hfeas z.1 z.2

/-- Helper for Example 17.55: if a feasible finite transport-potential pair already realizes the
cost of a coupling, then every positive-mass atom of that coupling is tight. -/
private theorem exactTransportPotentialPair_tight_on_positiveMass
    {t : Set E} (htfin : t.Finite) {P Q : ProbabilityMeasure t}
    (π : WassersteinCoupling P Q) {u v : t → ℝ}
    (hfeas : ∀ x y, u x + v y ≤ dist x y)
    (hobj :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∫ z : t × t, dist z.1 z.2
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) :
    ∀ x y, ((π.1 : Measure (t × t)) {(x, y)}) ≠ 0 → u x + v y = dist x y := by
  classical
  letI : Fintype t := htfin.fintype
  let gap : t × t → ℝ := fun z ↦ dist z.1 z.2 - (u z.1 + v z.2)
  have hgap_nonneg : ∀ z : t × t, 0 ≤ gap z := by
    intro z
    dsimp [gap]
    linarith [hfeas z.1 z.2]
  have hpairIntegral :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∫ z : t × t, (u z.1 + v z.2)
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) :=
    transportPotentialPair_objective_eq_integral_pairSum (htfin := htfin) (π := π)
  have hgapInt :
      Integrable gap (((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) :=
    MeasureTheory.Integrable.of_finite
  have hgapIntegralZero :
      ∫ z : t × t, gap z ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) = 0 := by
    have hcostInt :
        Integrable (fun z : t × t ↦ dist z.1 z.2)
          (((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) :=
      MeasureTheory.Integrable.of_finite
    have hpairInt :
        Integrable (fun z : t × t ↦ u z.1 + v z.2)
          (((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) :=
      MeasureTheory.Integrable.of_finite
    -- Proof comment: the slack is nonnegative everywhere, and exact objective equality forces its
    -- integral against the cost-realizing coupling to vanish.
    calc
      ∫ z : t × t, gap z ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
          ∫ z : t × t, dist z.1 z.2
            ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) -
            ∫ z : t × t, (u z.1 + v z.2)
              ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
        rw [show gap = fun z : t × t ↦ dist z.1 z.2 - (u z.1 + v z.2) by rfl]
        rw [MeasureTheory.integral_sub hcostInt hpairInt]
      _ = 0 := by
        linarith [hobj, hpairIntegral]
  have hsumZero :
      ∑ z : t × t, (((π.1 : Measure (t × t)).real {z}) * gap z) = 0 := by
    -- Proof comment: on the finite subtype, the zero integral is exactly a finite weighted sum of
    -- the nonnegative pointwise slack terms.
    calc
      ∑ z : t × t, (((π.1 : Measure (t × t)).real {z}) * gap z) =
          ∫ z : t × t, gap z ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
        simpa [smul_eq_mul] using
          (MeasureTheory.integral_fintype
            (μ := ((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)))
            (f := gap) hgapInt).symm
      _ = 0 := hgapIntegralZero
  intro x y hmass
  have hcoeff_pos : 0 < ((π.1 : Measure (t × t)).real {(x, y)}) := by
    exact ENNReal.toReal_pos hmass (measure_ne_top _ _)
  have hterm_nonneg :
      0 ≤ (((π.1 : Measure (t × t)).real {(x, y)}) * gap (x, y)) := by
    exact mul_nonneg hcoeff_pos.le (hgap_nonneg (x, y))
  have hterm_le :
      (((π.1 : Measure (t × t)).real {(x, y)}) * gap (x, y)) ≤
        ∑ z : t × t, (((π.1 : Measure (t × t)).real {z}) * gap z) := by
    exact Finset.single_le_sum
      (f := fun z : t × t ↦ (((π.1 : Measure (t × t)).real {z}) * gap z))
      (fun z _ ↦ mul_nonneg (by simp [Measure.real_def]) (hgap_nonneg z))
      (Finset.mem_univ (x, y))
  have hterm_zero :
      (((π.1 : Measure (t × t)).real {(x, y)}) * gap (x, y)) = 0 := by
    have hterm_nonpos :
        (((π.1 : Measure (t × t)).real {(x, y)}) * gap (x, y)) ≤ 0 := by
      calc
        (((π.1 : Measure (t × t)).real {(x, y)}) * gap (x, y)) ≤
            ∑ z : t × t, (((π.1 : Measure (t × t)).real {z}) * gap z) := hterm_le
        _ = 0 := hsumZero
    exact le_antisymm hterm_nonpos hterm_nonneg
  have hgap_zero : gap (x, y) = 0 := by
    rcases mul_eq_zero.mp hterm_zero with hcoeff_zero | hgap_zero
    · exact False.elim (hcoeff_pos.ne' hcoeff_zero)
    · exact hgap_zero
  -- Proof comment: a positive singleton mass forces the corresponding nonnegative slack term to
  -- vanish, hence the transport inequality is tight on that atom.
  dsimp [gap] at hgap_zero
  linarith

/-- Helper for Example 17.55: if a feasible pair falls strictly below the cost of a coupling, then
some positive-mass atom of that coupling must carry strict slack. -/
private theorem positiveMassSlackAtom_of_objective_lt_cost
    {t : Set E} (htfin : t.Finite) {P Q : ProbabilityMeasure t}
    (π : WassersteinCoupling P Q) {u v : t → ℝ}
    (hfeas : ∀ x y, u x + v y ≤ dist x y)
    (hgap :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) <
        ∫ z : t × t, dist z.1 z.2
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t))) :
    ∃ x y, ((π.1 : Measure (t × t)) {(x, y)}) ≠ 0 ∧ u x + v y < dist x y := by
  classical
  by_contra hnoSlack
  push Not at hnoSlack
  have htight :
      ∀ x y, ((π.1 : Measure (t × t)) {(x, y)}) ≠ 0 → u x + v y = dist x y := by
    intro x y hmass
    -- Proof comment: if every positive-mass atom avoids strict slack, feasibility forces equality
    -- on all atoms seen by the coupling.
    have hge : dist x y ≤ u x + v y := hnoSlack x y hmass
    linarith [hfeas x y, hge]
  have hobjEq :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∫ z : t × t, dist z.1 z.2
          ∂((π.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) :=
    supportTightPair_objective_eq_couplingCost (htfin := htfin) (π := π) htight
  -- Proof comment: without a slack atom, the pair objective would already equal the coupling
  -- cost, contradicting the assumed strict gap.
  linarith

/-- Helper for Example 17.55: on a finite probability space, equality of integrals under a
pointwise order forces equality at each positive-mass atom. -/
private theorem eq_on_positiveAtoms_of_integral_eq
    {t : Set E} (htfin : t.Finite) {μ : ProbabilityMeasure t} {f g : t → ℝ}
    (hfg : ∀ x, f x ≤ g x)
    (hintEq : ∫ x, f x ∂(μ : Measure t) = ∫ x, g x ∂(μ : Measure t)) :
    ∀ x, ((μ : Measure t) {x}) ≠ 0 → f x = g x := by
  classical
  letI : Fintype t := htfin.fintype
  let gap : t → ℝ := fun x ↦ g x - f x
  have hgap_nonneg : ∀ x, 0 ≤ gap x := by
    intro x
    dsimp [gap]
    linarith [hfg x]
  have hgapInt : Integrable gap (μ : Measure t) := MeasureTheory.Integrable.of_finite
  have hgapIntegralZero : ∫ x, gap x ∂(μ : Measure t) = 0 := by
    have hIntF : Integrable f (μ : Measure t) := MeasureTheory.Integrable.of_finite
    have hIntG : Integrable g (μ : Measure t) := MeasureTheory.Integrable.of_finite
    -- Proof comment: the nonnegative pointwise gap has zero integral because the two endpoint
    -- integrals agree.
    calc
      ∫ x, gap x ∂(μ : Measure t) =
          ∫ x, g x ∂(μ : Measure t) - ∫ x, f x ∂(μ : Measure t) := by
        simp [gap, MeasureTheory.integral_sub hIntG hIntF]
      _ = 0 := by linarith
  have hsumZero :
      ∑ x : t, (((μ : Measure t).real {x}) * gap x) = 0 := by
    -- Proof comment: on the finite subtype, the zero integral is the weighted sum of the
    -- singleton masses times the nonnegative gap.
    calc
      ∑ x : t, (((μ : Measure t).real {x}) * gap x) =
          ∫ x, gap x ∂(μ : Measure t) := by
        simpa [smul_eq_mul] using
          (MeasureTheory.integral_fintype (μ := (μ : Measure t)) (f := gap) hgapInt).symm
      _ = 0 := hgapIntegralZero
  intro x hx
  have hcoeff_pos : 0 < ((μ : Measure t).real {x}) := by
    exact ENNReal.toReal_pos hx (measure_ne_top _ _)
  have hterm_nonneg :
      0 ≤ (((μ : Measure t).real {x}) * gap x) := by
    exact mul_nonneg hcoeff_pos.le (hgap_nonneg x)
  have hterm_le :
      (((μ : Measure t).real {x}) * gap x) ≤
        ∑ z : t, (((μ : Measure t).real {z}) * gap z) := by
    exact Finset.single_le_sum
      (f := fun z : t ↦ (((μ : Measure t).real {z}) * gap z))
      (fun z _ ↦ mul_nonneg measureReal_nonneg (hgap_nonneg z))
      (Finset.mem_univ x)
  have hterm_zero :
      (((μ : Measure t).real {x}) * gap x) = 0 := by
    have hterm_nonpos :
        (((μ : Measure t).real {x}) * gap x) ≤ 0 := by
      calc
        (((μ : Measure t).real {x}) * gap x) ≤
            ∑ z : t, (((μ : Measure t).real {z}) * gap z) := hterm_le
        _ = 0 := hsumZero
    exact le_antisymm hterm_nonpos hterm_nonneg
  have hgap_zero : gap x = 0 := by
    rcases mul_eq_zero.mp hterm_zero with hcoeff_zero | hgap_zero
    · exact False.elim ((ne_of_gt hcoeff_pos) hcoeff_zero)
    · exact hgap_zero
  -- Proof comment: a positive singleton mass cannot support a strictly positive gap term, so the
  -- pointwise order is an equality on that atom.
  dsimp [gap] at hgap_zero
  linarith

/-- Helper for Example 17.55: a positive-mass atom of a coupling forces positive singleton mass in
both marginals. -/
private theorem coupling_positiveAtom_gives_positiveMarginals
    {t : Set E} (htfin : t.Finite) {P Q : ProbabilityMeasure t}
    (π : WassersteinCoupling P Q) {x y : t}
    (hxy : ((π.1 : Measure (t × t)) {(x, y)}) ≠ 0) :
    ((P : Measure t) {x}) ≠ 0 ∧ ((Q : Measure t) {y}) ≠ 0 := by
  classical
  letI : Fintype t := htfin.fintype
  rcases π.2 with ⟨hfst, hsnd⟩
  have hrow :
      ∑ b : t, ((π.1 : Measure (t × t)) {(x, b)}) = ((P : Measure t) {x}) := by
    -- Proof comment: the first marginal singleton mass is the row sum through `x`.
    have hfstSingleton := congrArg (fun μ : Measure t ↦ μ {x}) hfst
    simpa [Measure.fst_apply, MeasureTheory.measure_preimage_fst_singleton_eq_sum] using
      hfstSingleton
  have hcol :
      ∑ a : t, ((π.1 : Measure (t × t)) {(a, y)}) = ((Q : Measure t) {y}) := by
    -- Proof comment: the second marginal singleton mass is the column sum through `y`.
    have hsndSingleton := congrArg (fun μ : Measure t ↦ μ {y}) hsnd
    simpa [Measure.snd_apply, MeasureTheory.measure_preimage_snd_singleton_eq_sum] using
      hsndSingleton
  constructor
  · intro hPx
    have hsingle_le :
        ((π.1 : Measure (t × t)) {(x, y)}) ≤
          ∑ b : t, ((π.1 : Measure (t × t)) {(x, b)}) := by
      exact Finset.single_le_sum
        (f := fun b : t ↦ ((π.1 : Measure (t × t)) {(x, b)}))
        (fun _ _ ↦ by simp)
        (Finset.mem_univ y)
    have hzero : ((π.1 : Measure (t × t)) {(x, y)}) = 0 := by
      refine le_antisymm ?_ bot_le
      calc
        ((π.1 : Measure (t × t)) {(x, y)}) ≤
            ∑ b : t, ((π.1 : Measure (t × t)) {(x, b)}) := hsingle_le
        _ = 0 := by simpa [hPx] using hrow
    exact hxy hzero
  · intro hQy
    have hsingle_le :
        ((π.1 : Measure (t × t)) {(x, y)}) ≤
          ∑ a : t, ((π.1 : Measure (t × t)) {(a, y)}) := by
      exact Finset.single_le_sum
        (f := fun a : t ↦ ((π.1 : Measure (t × t)) {(a, y)}))
        (fun _ _ ↦ by simp)
        (Finset.mem_univ x)
    have hzero : ((π.1 : Measure (t × t)) {(x, y)}) = 0 := by
      refine le_antisymm ?_ bot_le
      calc
        ((π.1 : Measure (t × t)) {(x, y)}) ≤
            ∑ a : t, ((π.1 : Measure (t × t)) {(a, y)}) := hsingle_le
        _ = 0 := by simpa [hQy] using hcol
    exact hxy hzero

/-- Helper for Example 17.55: the transport envelope of a maximizing feasible pair agrees with the
pair on every positive-mass marginal atom. -/
private theorem transportEnvelope_eq_on_positiveMarginals_of_maximizingPair
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t) {u v : t → ℝ}
    (hfeas : ∀ x y, u x + v y ≤ dist x y)
    (hmax :
      ∀ u' v' : t → ℝ, (∀ x y, u' x + v' y ≤ dist x y) →
        ∫ x, u' x ∂(P : Measure t) + ∫ y, v' y ∂(Q : Measure t) ≤
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t)) :
    ∃ g : t → ℝ,
      LipschitzWith 1 g ∧
        (∀ x, u x ≤ g x) ∧
        (∀ y, v y ≤ -g y) ∧
        (∀ x, ((P : Measure t) {x}) ≠ 0 → u x = g x) ∧
        (∀ y, ((Q : Measure t) {y}) ≠ 0 → v y = -g y) ∧
        (∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
          ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t)) := by
  classical
  letI : Fintype t := htfin.fintype
  have hfeasOne : ∀ x y, u x + v y ≤ (1 : ℝ) * dist x y := by
    intro x y
    simpa using hfeas x y
  obtain ⟨g, hgLip, hu_le, hv_le⟩ :=
    existsLipschitzPotential_of_transportInequalities
      (htfin := htfin) (α := 1) (hα := zero_le_one) hfeasOne
  have hgLipOne : LipschitzWith 1 g := by
    simpa using hgLip
  have hgfeas : ∀ x y, g x + (-g y) ≤ dist x y := by
    intro x y
    -- Proof comment: a `1`-Lipschitz witness defines the feasible pair `(g, -g)`.
    have hxy : g x ≤ g y + dist x y := by
      simpa using hgLipOne.le_add_mul x y
    linarith
  have hPIntU : Integrable u (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hQIntV : Integrable v (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hPIntG : Integrable g (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hQIntG : Integrable g (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hPmono :
      ∫ x, u x ∂(P : Measure t) ≤ ∫ x, g x ∂(P : Measure t) := by
    -- Proof comment: the transport envelope dominates the first potential pointwise.
    refine MeasureTheory.integral_mono hPIntU hPIntG ?_
    intro x
    exact hu_le x
  have hQmono :
      ∫ y, v y ∂(Q : Measure t) ≤ ∫ y, -g y ∂(Q : Measure t) := by
    -- Proof comment: the same envelope bounds the second potential above by `-g`.
    refine MeasureTheory.integral_mono hQIntV hQIntG.neg ?_
    intro y
    exact hv_le y
  have hpair_le_env :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) ≤
        ∫ x, g x ∂(P : Measure t) + ∫ y, -g y ∂(Q : Measure t) := by
    linarith
  have henv_le_pair :
      ∫ x, g x ∂(P : Measure t) + ∫ y, -g y ∂(Q : Measure t) ≤
        ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) :=
    hmax g (fun y ↦ -g y) hgfeas
  have hsumEq :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∫ x, g x ∂(P : Measure t) + ∫ y, -g y ∂(Q : Measure t) := by
    exact le_antisymm hpair_le_env henv_le_pair
  have hIntUEq :
      ∫ x, u x ∂(P : Measure t) = ∫ x, g x ∂(P : Measure t) := by
    -- Proof comment: since both coordinatewise monotonicity inequalities sum to equality, the
    -- first-coordinate inequality is itself an equality.
    linarith [hPmono, hQmono, hsumEq]
  have hIntVEq :
      ∫ y, v y ∂(Q : Measure t) = ∫ y, -g y ∂(Q : Measure t) := by
    -- Proof comment: the same equality-of-sums argument forces equality on the second marginal.
    linarith [hPmono, hQmono, hsumEq]
  have hQneg :
      ∫ y, -g y ∂(Q : Measure t) = -∫ y, g y ∂(Q : Measure t) := by
    simpa using MeasureTheory.integral_neg (f := g) (μ := (Q : Measure t))
  refine ⟨g, hgLipOne, hu_le, hv_le, ?_, ?_, ?_⟩
  · exact eq_on_positiveAtoms_of_integral_eq (htfin := htfin) (μ := P) hu_le hIntUEq
  · exact eq_on_positiveAtoms_of_integral_eq (htfin := htfin) (μ := Q) hv_le hIntVEq
  · -- Proof comment: the maximizing pair and its transport envelope have the same signed
    -- objective once both marginal inequalities are known to be sharp.
    linarith [hsumEq, hQneg]

/-- Helper for Example 17.55: the cut-style left shift raises `u` by `ε` exactly on `A`. -/
private def shiftedTransportPotentialLeft
    {t : Set E} (A : Set t) (u : t → ℝ) (ε : ℝ) : t → ℝ :=
  fun x ↦ @ite ℝ (x ∈ A) (Classical.decPred A x) (u x + ε) (u x)

/-- Helper for Example 17.55: the cut-style right shift lowers `v` by `ε` exactly on `B`. -/
private def shiftedTransportPotentialRight
    {t : Set E} (B : Set t) (v : t → ℝ) (ε : ℝ) : t → ℝ :=
  fun y ↦ @ite ℝ (y ∈ B) (Classical.decPred B y) (v y - ε) (v y)

/-- Helper for Example 17.55: raising `u` on `A` and lowering `v` on `B` preserves feasibility as
soon as the shifted inequality is checked on the only new cross-term `A × Bᶜ`. -/
private theorem shiftedTransportPotentialPair_feasible
    {t : Set E} {u v : t → ℝ} {A B : Set t} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hfeas : ∀ x y, u x + v y ≤ dist x y)
    (hcross : ∀ x ∈ A, ∀ y ∉ B, u x + v y + ε ≤ dist x y) :
    ∀ x y,
      shiftedTransportPotentialLeft A u ε x +
          shiftedTransportPotentialRight B v ε y ≤
        dist x y := by
  intro x y
  -- Proof comment: after splitting by membership in `A` and `B`, only the `A × Bᶜ` branch uses
  -- the strengthened cross-inequality; the remaining branches collapse to the original
  -- feasibility bound.
  classical
  by_cases hx : x ∈ A
  · by_cases hy : y ∈ B
    · simpa [shiftedTransportPotentialLeft, shiftedTransportPotentialRight, hx, hy] using
        hfeas x y
    · have hxy : u x + v y + ε ≤ dist x y := hcross x hx y hy
      simpa [shiftedTransportPotentialLeft, shiftedTransportPotentialRight, hx, hy, add_assoc,
        add_left_comm, add_comm] using hxy
  · by_cases hy : y ∈ B
    · have hxy : u x + v y ≤ dist x y := hfeas x y
      have hsub : u x + (v y - ε) ≤ u x + v y := by
        linarith
      simpa [shiftedTransportPotentialLeft, shiftedTransportPotentialRight, hx, hy] using
        le_trans hsub hxy
    · simpa [shiftedTransportPotentialLeft, shiftedTransportPotentialRight, hx, hy] using
        hfeas x y

/-- Helper for Example 17.55: the cut-style shift changes the finite dual objective by exactly
`ε * (P(A) - Q(B))`. -/
private theorem shiftedTransportPotentialPair_objective_eq
    {t : Set E} (htfin : t.Finite) {P Q : ProbabilityMeasure t}
    {u v : t → ℝ} {A B : Set t} {ε : ℝ} :
    ∫ x, shiftedTransportPotentialLeft A u ε x ∂(P : Measure t) +
        ∫ y, shiftedTransportPotentialRight B v ε y ∂(Q : Measure t) =
      (∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t)) +
        ε * (((P : Measure t).real A) - ((Q : Measure t).real B)) := by
  classical
  letI : Fintype t := htfin.fintype
  have hAmeas : MeasurableSet A := (Set.toFinite A).measurableSet
  have hBmeas : MeasurableSet B := (Set.toFinite B).measurableSet
  have hshiftU :
      shiftedTransportPotentialLeft A u ε =
        fun x : t ↦ u x + A.indicator (fun _ : t ↦ ε) x := by
    funext x
    by_cases hx : x ∈ A
    · simp [shiftedTransportPotentialLeft, hx, Set.indicator_of_mem]
    · simp [shiftedTransportPotentialLeft, hx, Set.indicator_of_notMem]
  have hshiftV :
      shiftedTransportPotentialRight B v ε =
        fun y : t ↦ v y + B.indicator (fun _ : t ↦ -ε) y := by
    funext y
    by_cases hy : y ∈ B
    · simp [shiftedTransportPotentialRight, hy, Set.indicator_of_mem, sub_eq_add_neg, add_assoc]
    · simp [shiftedTransportPotentialRight, hy, Set.indicator_of_notMem]
  have hIntU :
      Integrable u (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hIntV :
      Integrable v (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hIntA :
      Integrable (A.indicator (fun _ : t ↦ ε)) (P : Measure t) := by
    exact MeasureTheory.Integrable.of_finite
  have hIntB :
      Integrable (B.indicator (fun _ : t ↦ -ε)) (Q : Measure t) := by
    exact MeasureTheory.Integrable.of_finite
  have hAint :
      ∫ x, A.indicator (fun _ : t ↦ ε) x ∂(P : Measure t) =
        (P : Measure t).real A * ε := by
    -- Proof comment: the indicator contribution is the constant `ε` weighted by the `P`-mass of
    -- the cut set `A`.
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_indicator_const (μ := (P : Measure t)) (s := A) (e := ε) hAmeas)
  have hBint :
      ∫ y, B.indicator (fun _ : t ↦ -ε) y ∂(Q : Measure t) =
        (Q : Measure t).real B * (-ε) := by
    -- Proof comment: the second shift contributes the negative constant `-ε` weighted by the
    -- `Q`-mass of the cut set `B`.
    simpa [smul_eq_mul] using
      (MeasureTheory.integral_indicator_const (μ := (Q : Measure t)) (s := B) (e := -ε) hBmeas)
  -- Proof comment: after rewriting both shifted coordinates as base terms plus indicator
  -- corrections, the finite objective change is a direct linearity calculation.
  rw [hshiftU, hshiftV, MeasureTheory.integral_add hIntU hIntA,
    MeasureTheory.integral_add hIntV hIntB, hAint, hBint]
  ring

/-- Helper for Example 17.55: a cut with positive cross slack and larger `P`-mass than `Q`-mass
contradicts maximality of a feasible transport-potential pair. -/
private theorem cutGap_contradictsTransportPotentialMaximality
    {t : Set E} (htfin : t.Finite) {P Q : ProbabilityMeasure t}
    {u v : t → ℝ} (hfeas : ∀ x y, u x + v y ≤ dist x y)
    (hmax :
      ∀ u' v' : t → ℝ, (∀ x y, u' x + v' y ≤ dist x y) →
        ∫ x, u' x ∂(P : Measure t) + ∫ y, v' y ∂(Q : Measure t) ≤
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t))
    {A B : Set t}
    (hmassGap : ((Q : Measure t).real B) < ((P : Measure t).real A))
    (hcrossSlack : ∀ x ∈ A, ∀ y ∉ B, u x + v y < dist x y) :
    False := by
  classical
  letI : Fintype t := htfin.fintype
  have hA_nonempty : A.Nonempty := by
    by_contra hA
    have hAeq : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    have hQ_nonneg : 0 ≤ ((Q : Measure t).real B) := measureReal_nonneg
    have : ¬ ((Q : Measure t).real B < 0) := not_lt.mpr hQ_nonneg
    exact this (by simpa [hAeq] using hmassGap)
  have hB_ne_univ : B ≠ Set.univ := by
    intro hB
    have hPA_le_one : ((P : Measure t).real A) ≤ 1 := by
      simpa using (measureReal_le_one (μ := (P : Measure t)) (s := A))
    have hQB_eq_one : ((Q : Measure t).real B) = 1 := by
      simpa [hB] using (show ((Q : Measure t).real Set.univ) = 1 by simp)
    have hPA_gt_one : 1 < ((P : Measure t).real A) := by
      simpa [hQB_eq_one] using hmassGap
    exact (not_lt_of_ge hPA_le_one) hPA_gt_one
  have hBcompl_nonempty : Set.Nonempty Bᶜ := Set.nonempty_compl.mpr hB_ne_univ
  obtain ⟨x₀, hx₀A⟩ := hA_nonempty
  obtain ⟨y₀, hy₀B⟩ := hBcompl_nonempty
  let crossPairs : Finset (t × t) := Finset.univ.filter fun z ↦ z.1 ∈ A ∧ z.2 ∉ B
  have hcrossPairs_nonempty : crossPairs.Nonempty := by
    refine ⟨(x₀, y₀), ?_⟩
    change (x₀, y₀) ∈ Finset.univ.filter fun z : t × t ↦ z.1 ∈ A ∧ z.2 ∉ B
    refine Finset.mem_filter.mpr ?_
    exact ⟨Finset.mem_univ _, ⟨hx₀A, hy₀B⟩⟩
  let slack : t × t → ℝ := fun z ↦ dist z.1 z.2 - (u z.1 + v z.2)
  have hslack_pos : ∀ z ∈ crossPairs, 0 < slack z := by
    intro z hz
    have hz' : z ∈ Finset.univ.filter fun w : t × t ↦ w.1 ∈ A ∧ w.2 ∉ B := by
      simpa [crossPairs] using hz
    have hzA : z.1 ∈ A := (Finset.mem_filter.mp hz').2.1
    have hzB : z.2 ∉ B := (Finset.mem_filter.mp hz').2.2
    -- Proof comment: every cross edge in the cut has positive slack by assumption, so the slack
    -- function is strictly positive on the finite cross set.
    dsimp [slack]
    linarith [hcrossSlack z.1 hzA z.2 hzB]
  let crossSlack : Finset ℝ := crossPairs.image slack
  have hcrossSlack_nonempty : crossSlack.Nonempty := by
    rcases hcrossPairs_nonempty with ⟨z, hz⟩
    exact ⟨slack z, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  let ε : ℝ := Finset.min' crossSlack hcrossSlack_nonempty / 2
  have hmin_pos : 0 < Finset.min' crossSlack hcrossSlack_nonempty := by
    have hmin_mem : Finset.min' crossSlack hcrossSlack_nonempty ∈ crossSlack :=
      Finset.min'_mem _ _
    rcases Finset.mem_image.mp hmin_mem with ⟨z, hz, hzEq⟩
    rw [← hzEq]
    exact hslack_pos z hz
  have hε : 0 < ε := by
    -- Proof comment: half of the minimal cross slack is still positive, so it is a legal shift
    -- size for the cut argument.
    dsimp [ε]
    linarith
  have hcross :
      ∀ x ∈ A, ∀ y ∉ B, u x + v y + ε ≤ dist x y := by
    intro x hx y hy
    have hmem : slack (x, y) ∈ crossSlack := by
      refine Finset.mem_image.mpr ?_
      refine ⟨(x, y), ?_, rfl⟩
      simp [crossPairs, hx, hy]
    have hmin_le : Finset.min' crossSlack hcrossSlack_nonempty ≤ slack (x, y) :=
      Finset.min'_le _ _ hmem
    have hε_le : ε ≤ slack (x, y) := by
      have hε_le_min : ε ≤ Finset.min' crossSlack hcrossSlack_nonempty := by
        dsimp [ε]
        linarith
      dsimp [ε]
      linarith
    -- Proof comment: choosing `ε` below the smallest cross slack preserves feasibility after the
    -- cut shift.
    dsimp [slack] at hε_le ⊢
    linarith
  have hshiftFeas :
      ∀ x y,
        shiftedTransportPotentialLeft A u ε x +
            shiftedTransportPotentialRight B v ε y ≤
          dist x y :=
    shiftedTransportPotentialPair_feasible hε.le hfeas hcross
  have hshiftMax :
      ∫ x, shiftedTransportPotentialLeft A u ε x ∂(P : Measure t) +
          ∫ y, shiftedTransportPotentialRight B v ε y ∂(Q : Measure t) ≤
        ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) :=
    hmax _ _ hshiftFeas
  have hmassDiff_pos :
      0 < ((P : Measure t).real A) - ((Q : Measure t).real B) := sub_pos.mpr hmassGap
  have hshiftImprove :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) <
        ∫ x, shiftedTransportPotentialLeft A u ε x ∂(P : Measure t) +
          ∫ y, shiftedTransportPotentialRight B v ε y ∂(Q : Measure t) := by
    have hmul_pos : 0 < ε * (((P : Measure t).real A) - ((Q : Measure t).real B)) :=
      mul_pos hε hmassDiff_pos
    -- Proof comment: the shifted objective changes by `ε * (P(A) - Q(B))`, which is strictly
    -- positive under the cut mass-gap hypothesis.
    rw [shiftedTransportPotentialPair_objective_eq
      (htfin := htfin) (P := P) (Q := Q) (u := u) (v := v) (A := A) (B := B) (ε := ε)]
    linarith
  exact (not_lt_of_ge hshiftMax) hshiftImprove

/-- Helper for Example 17.55: a maximizing feasible finite transport-potential pair already
realizes the supremum of the anchored finite dual set. -/
private theorem maximizingTransportPotentialPair_objective_eq_sSupAnchoredDual
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t) {u v : t → ℝ}
    (hfeas : ∀ x y, u x + v y ≤ dist x y)
    (hmax :
      ∀ u' v' : t → ℝ, (∀ x y, u' x + v' y ≤ dist x y) →
        ∫ x, u' x ∂(P : Measure t) + ∫ y, v' y ∂(Q : Measure t) ≤
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t)) :
    ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
      sSup {r : ℝ | ∃ g : t → ℝ,
        g a₀ = 0 ∧
          LipschitzWith 1 g ∧
          r = ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t)} := by
  let dualSet : Set ℝ :=
    {r : ℝ | ∃ g : t → ℝ,
      g a₀ = 0 ∧
        LipschitzWith 1 g ∧
        r = ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t)}
  have hdual_nonempty : dualSet.Nonempty := by
    exact ⟨0, zeroAnchoredPotential_mem_finiteDualSet a₀ P Q⟩
  have hdual_bdd : BddAbove dualSet := by
    refine ⟨(wassersteinDistance P Q).toReal, ?_⟩
    intro r hr
    rcases hr with ⟨g, hg₀, hgLip, rfl⟩
    -- Proof comment: every anchored feasible witness is bounded above by the finite
    -- Wasserstein value through weak duality.
    exact anchoredPotential_objective_le_wassersteinDistance
      (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q) hg₀ hgLip
  obtain ⟨g, hg₀, hgLip, hobjEq, hgmax⟩ :=
    maximizingTransportPotentialPair_inducesAnchoredPotential
      (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q) hfeas hmax
  have hgmem :
      ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) ∈ dualSet := by
    exact ⟨g, hg₀, hgLip, rfl⟩
  have hsSup_le :
      sSup dualSet ≤
        ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) := by
    refine csSup_le hdual_nonempty ?_
    intro r hr
    rcases hr with ⟨h, hh₀, hhLip, rfl⟩
    -- Proof comment: the anchored witness induced from pair maximality dominates every other
    -- anchored feasible witness, so it is an upper bound for the whole dual set.
    rw [← hobjEq]
    exact hgmax h hh₀ hhLip
  have hg_le :
      ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) ≤ sSup dualSet := by
    -- Proof comment: the induced anchored witness belongs to the dual set, so its value is
    -- below the supremum of that set.
    exact le_csSup hdual_bdd hgmem
  -- Proof comment: pair maximality and anchored maximality have the same objective value, and
  -- the anchored maximizer is exactly a `sSup` witness for the finite dual set.
  rw [hobjEq]
  exact le_antisymm hg_le hsSup_le

/-- Helper for Example 17.55: once the reduced-cost/support graph is fixed, a reachable left
vertex cannot have a tight edge into an unreachable right vertex. -/
private theorem tightSupportReachabilityCrossSlack
    {t : Set E} {x₀ : t} {g₀ : t → ℝ}
    {step : Sum t t → Sum t t → Prop} {A B : Set t}
    (hg₀feas : ∀ x y, g₀ x + (-g₀ y) ≤ dist x y)
    (hstep_tight : ∀ x y, step (Sum.inl x) (Sum.inr y) ↔ g₀ x - g₀ y = dist x y)
    (hA : ∀ x, x ∈ A ↔ Relation.ReflTransGen step (Sum.inl x₀) (Sum.inl x))
    (hB : ∀ y, y ∈ B ↔ Relation.ReflTransGen step (Sum.inl x₀) (Sum.inr y)) :
    ∀ x ∈ A, ∀ y ∉ B, g₀ x + (-g₀ y) < dist x y := by
  intro x hxA y hyB
  have hxReach : Relation.ReflTransGen step (Sum.inl x₀) (Sum.inl x) := (hA x).1 hxA
  have hfeasXY : g₀ x + (-g₀ y) ≤ dist x y := hg₀feas x y
  -- Proof comment: a non-strict cross edge would be tight, and that tight edge would extend the
  -- left reachability witness to a right reachability witness for `y`.
  by_contra hnot_lt
  have hEq : g₀ x - g₀ y = dist x y := by
    linarith
  have hstep : step (Sum.inl x) (Sum.inr y) := (hstep_tight x y).2 hEq
  have hyReach : Relation.ReflTransGen step (Sum.inl x₀) (Sum.inr y) := by
    exact Relation.ReflTransGen.trans hxReach (Relation.ReflTransGen.single hstep)
  exact hyB ((hB y).2 hyReach)

/-- Helper for Example 17.55: the support edges of the reduced-cost graph cannot send mass from an
unreachable left vertex into the reachable right set. -/
private theorem tightSupportReachabilityRectangleZero
    {t : Set E} [Fintype t] {x₀ : t} (πμ : Measure (t × t)) [IsFiniteMeasure πμ]
    {step : Sum t t → Sum t t → Prop} {A B : Set t}
    (hA : ∀ x, x ∈ A ↔ Relation.ReflTransGen step (Sum.inl x₀) (Sum.inl x))
    (hB : ∀ y, y ∈ B ↔ Relation.ReflTransGen step (Sum.inl x₀) (Sum.inr y))
    (hstep_support : ∀ x y, step (Sum.inr y) (Sum.inl x) ↔ πμ {(x, y)} ≠ 0) :
    πμ.real (Aᶜ ×ˢ B : Set (t × t)) = 0 := by
  classical
  let AcBFin : Finset (t × t) := Finset.univ.filter fun z ↦ z.1 ∉ A ∧ z.2 ∈ B
  have hAcBFin_eq : ((AcBFin : Finset (t × t)) : Set (t × t)) = Aᶜ ×ˢ B := by
    ext z
    simp [AcBFin]
  rw [← hAcBFin_eq, ← MeasureTheory.sum_measureReal_singleton (μ := πμ) (s := AcBFin)]
  refine Finset.sum_eq_zero ?_
  intro z hz
  have hzA : z.1 ∉ A := (Finset.mem_filter.mp hz).2.1
  have hzB : z.2 ∈ B := (Finset.mem_filter.mp hz).2.2
  have hzZero : πμ {z} = 0 := by
    -- Proof comment: a positive-mass atom in `Aᶜ × B` would add a support edge from a reachable
    -- right vertex to an unreachable left vertex, contradicting closure of reachability.
    by_contra hzMass
    have hyReach : Relation.ReflTransGen step (Sum.inl x₀) (Sum.inr z.2) := (hB z.2).1 hzB
    have hstep : step (Sum.inr z.2) (Sum.inl z.1) := (hstep_support z.1 z.2).2 hzMass
    have hxReach : Relation.ReflTransGen step (Sum.inl x₀) (Sum.inl z.1) := by
      exact Relation.ReflTransGen.trans hyReach (Relation.ReflTransGen.single hstep)
    exact hzA ((hA z.1).2 hxReach)
  simp [Measure.real_def, hzZero]

/-- Helper for Example 17.55: a right-reaching witness in the bipartite reduced-cost graph ends
with a tight edge from some reachable left predecessor. -/
private theorem reachableRight_hasLastTightEdge
    {t : Set E} {x₀ y₀ : t} {g₀ : t → ℝ} {step : Sum t t → Sum t t → Prop}
    (hstep_right_right : ∀ y y' : t, ¬ step (Sum.inr y) (Sum.inr y'))
    (hstep_tight : ∀ x y, step (Sum.inl x) (Sum.inr y) ↔ g₀ x - g₀ y = dist x y)
    (hreach : Relation.ReflTransGen step (Sum.inl x₀) (Sum.inr y₀)) :
    ∃ x, Relation.ReflTransGen step (Sum.inl x₀) (Sum.inl x) ∧
      g₀ x - g₀ y₀ = dist x y₀ := by
  -- Proof comment: the last edge of any right-reaching witness must come from the left part of
  -- the bipartite graph, and `hstep_tight` then identifies that final edge as tight.
  rcases Relation.ReflTransGen.cases_tail hreach with hEq | ⟨c, hcReach, hcy⟩
  · cases hEq
  · cases c with
    | inl x =>
        exact ⟨x, hcReach, (hstep_tight x y₀).1 hcy⟩
    | inr y =>
        exact False.elim (hstep_right_right y y₀ hcy)

/-- Helper for Example 17.55: a nontrivial left-reaching witness in the bipartite reduced-cost
graph ends with a positive-mass support edge from some reachable right predecessor. -/
private theorem reachableLeft_hasLastSupportEdge
    {t : Set E} {x₀ x₁ : t} {step : Sum t t → Sum t t → Prop} {πμ : Measure (t × t)}
    (hstep_left_left : ∀ x x' : t, ¬ step (Sum.inl x) (Sum.inl x'))
    (hstep_support : ∀ x y, step (Sum.inr y) (Sum.inl x) ↔ πμ {(x, y)} ≠ 0)
    (hreach : Relation.ReflTransGen step (Sum.inl x₀) (Sum.inl x₁))
    (hx₁ : x₁ ≠ x₀) :
    ∃ y, Relation.ReflTransGen step (Sum.inl x₀) (Sum.inr y) ∧
      πμ {(x₁, y)} ≠ 0 := by
  -- Proof comment: because the theorem-local graph has no left-to-left edges, the last step of a
  -- nontrivial left-reaching witness must come from a right vertex, and `hstep_support`
  -- identifies that final step with a positive-mass support atom.
  rcases Relation.ReflTransGen.cases_tail hreach with hEq | ⟨c, hcReach, hcx⟩
  · exact False.elim <| hx₁ <| by
      cases hEq
      rfl
  · cases c with
    | inl x =>
        exact False.elim (hstep_left_left x x₁ hcx)
    | inr y =>
        exact ⟨y, hcReach, (hstep_support x₁ y).1 hcx⟩

/-- Helper for Example 17.55: ordered alternating data for a left-to-right reachability witness
in the reduced-cost/support graph. The `extend` constructor records one tight forward edge
followed by one positive-mass backward support edge, so iterating it packages the alternating
pattern `x₀ → y₁ ← x₁ → ... → y₀`. -/
private inductive ReachableRightData {t : Set E} (g₀ : t → ℝ)
    (πμ : Measure (t × t)) : t → t → Type _
  | direct {x y : t} (htight : g₀ x - g₀ y = dist x y) :
      ReachableRightData g₀ πμ x y
  | extend {x y₁ x₁ y₀ : t}
      (htight : g₀ x - g₀ y₁ = dist x y₁)
      (hsupport : πμ {(x₁, y₁)} ≠ 0)
      (tail : ReachableRightData g₀ πμ x₁ y₀) :
      ReachableRightData g₀ πμ x y₀

/-- Helper for Example 17.55: parse an explicit chain witness from a left vertex to a right
vertex into theorem-local ordered alternating reachability data. -/
private def reachableRightData_of_isChain
    {t : Set E} {πμ : Measure (t × t)} {g₀ : t → ℝ}
    {step : Sum t t → Sum t t → Prop}
    (hstep_left_left : ∀ x x' : t, ¬ step (Sum.inl x) (Sum.inl x'))
    (hstep_right_right : ∀ y y' : t, ¬ step (Sum.inr y) (Sum.inr y'))
    (hstep_tight : ∀ x y, step (Sum.inl x) (Sum.inr y) ↔ g₀ x - g₀ y = dist x y)
    (hstep_support : ∀ x y, step (Sum.inr y) (Sum.inl x) ↔ πμ {(x, y)} ≠ 0)
    {x₀ y₀ : t} {l : List (Sum t t)}
    (hl : List.IsChain step l)
    (hhead : l.head? = some (Sum.inl x₀))
    (hlast : l.getLast? = some (Sum.inr y₀)) :
    ReachableRightData g₀ πμ x₀ y₀ := by
  match l with
  | [] =>
      cases hhead
  | [a] =>
      have ha : a = Sum.inl x₀ := by
        simpa using hhead
      subst a
      cases hlast
  | a :: Sum.inl x :: l' =>
      have ha : a = Sum.inl x₀ := by
        simpa using hhead
      subst a
      have hab : step (Sum.inl x₀) (Sum.inl x) := by
        exact (List.isChain_cons.1 hl).1 _ (by simp)
      exact False.elim (hstep_left_left x₀ x hab)
  | a :: Sum.inr y₁ :: [] =>
      have ha : a = Sum.inl x₀ := by
        simpa using hhead
      subst a
      have hab : step (Sum.inl x₀) (Sum.inr y₁) := by
        exact (List.isChain_cons.1 hl).1 _ (by simp)
      have htight : g₀ x₀ - g₀ y₁ = dist x₀ y₁ := (hstep_tight x₀ y₁).1 hab
      have hy : y₁ = y₀ := by
        simpa using hlast
      subst hy
      -- Proof comment: a two-vertex chain is exactly one tight edge, so it is already the base
      -- alternating witness.
      exact ReachableRightData.direct htight
  | a :: Sum.inr y₁ :: Sum.inr y :: l' =>
      have ha : a = Sum.inl x₀ := by
        simpa using hhead
      subst a
      have htail : List.IsChain step (Sum.inr y₁ :: Sum.inr y :: l') := (List.isChain_cons.1 hl).2
      have hy : step (Sum.inr y₁) (Sum.inr y) := by
        exact (List.isChain_cons.1 htail).1 _ (by simp)
      exact False.elim (hstep_right_right y₁ y hy)
  | a :: Sum.inr y₁ :: Sum.inl x₁ :: l' =>
      have ha : a = Sum.inl x₀ := by
        simpa using hhead
      subst a
      have hab : step (Sum.inl x₀) (Sum.inr y₁) := by
        exact (List.isChain_cons.1 hl).1 _ (by simp)
      have htight : g₀ x₀ - g₀ y₁ = dist x₀ y₁ := (hstep_tight x₀ y₁).1 hab
      have htail : List.IsChain step (Sum.inr y₁ :: Sum.inl x₁ :: l') := (List.isChain_cons.1 hl).2
      have hsupportStep : step (Sum.inr y₁) (Sum.inl x₁) := by
        exact (List.isChain_cons.1 htail).1 _ (by simp)
      have htail₂ : List.IsChain step (Sum.inl x₁ :: l') := (List.isChain_cons.1 htail).2
      have hsupport : πμ {(x₁, y₁)} ≠ 0 := (hstep_support x₁ y₁).1 hsupportStep
      -- Proof comment: after peeling one tight/support pair, the remaining subchain starts again
      -- at a left vertex and ends at the same right target.
      exact ReachableRightData.extend htight hsupport
        (reachableRightData_of_isChain hstep_left_left hstep_right_right
          hstep_tight hstep_support htail₂ (by simp) (by simpa using hlast))
termination_by l.length
decreasing_by simp_wf

/-- Helper for Example 17.55: convert a reachability witness in the reduced-cost/support graph
into theorem-local ordered alternating data. -/
private def reachableRightData_of_reflTransGen
    {t : Set E} {πμ : Measure (t × t)} {g₀ : t → ℝ}
    {step : Sum t t → Sum t t → Prop}
    (hstep_left_left : ∀ x x' : t, ¬ step (Sum.inl x) (Sum.inl x'))
    (hstep_right_right : ∀ y y' : t, ¬ step (Sum.inr y) (Sum.inr y'))
    (hstep_tight : ∀ x y, step (Sum.inl x) (Sum.inr y) ↔ g₀ x - g₀ y = dist x y)
    (hstep_support : ∀ x y, step (Sum.inr y) (Sum.inl x) ↔ πμ {(x, y)} ≠ 0)
    {x₀ y₀ : t}
    (hreach : Relation.ReflTransGen step (Sum.inl x₀) (Sum.inr y₀)) :
    ReachableRightData g₀ πμ x₀ y₀ := by
  classical
  let l : List (Sum t t) := Classical.choose (List.exists_isChain_cons_of_relationReflTransGen hreach)
  have hl_and_last :
      List.IsChain step (Sum.inl x₀ :: l) ∧
        (Sum.inl x₀ :: l).getLast (List.cons_ne_nil _ _) = Sum.inr y₀ :=
    Classical.choose_spec (List.exists_isChain_cons_of_relationReflTransGen hreach)
  have hlast :
      (Sum.inl x₀ :: l).getLast? = some (Sum.inr y₀) := by
    rw [List.getLast?_eq_getLast_of_ne_nil (l := Sum.inl x₀ :: l) (List.cons_ne_nil _ _)]
    simpa using congrArg some hl_and_last.2
  -- Proof comment: the chain API exposes the reachability witness as an explicit finite list, and
  -- the theorem-local parser then strips off one tight/support pair at a time.
  exact reachableRightData_of_isChain hstep_left_left hstep_right_right hstep_tight
    hstep_support hl_and_last.1 (by simp) hlast

/-- Helper for Example 17.55: list the tight forward edges carried by ordered alternating data. -/
private def ReachableRightData.tightPairs
    {t : Set E} {g₀ : t → ℝ} {πμ : Measure (t × t)} {x y : t} :
    ReachableRightData g₀ πμ x y → List (t × t)
  | .direct (x := x) (y := y) _ => [(x, y)]
  | .extend (x := x) (y₁ := y₁) _ _ tail => (x, y₁) :: tail.tightPairs

/-- Helper for Example 17.55: list the positive-mass backward support edges carried by ordered
alternating data. -/
private def ReachableRightData.supportPairs
    {t : Set E} {g₀ : t → ℝ} {πμ : Measure (t × t)} {x y : t} :
    ReachableRightData g₀ πμ x y → List (t × t)
  | .direct _ => []
  | .extend (x₁ := x₁) (y₁ := y₁) _ _ tail => (x₁, y₁) :: tail.supportPairs

/-- Helper for Example 17.55: every ordered alternating witness has exactly one more tight edge
than support edge, matching the open path from the anchor to the terminal right vertex. -/
private theorem ReachableRightData.tightPairs_length_eq_supportPairs_length_succ
    {t : Set E} {g₀ : t → ℝ} {πμ : Measure (t × t)} {x y : t}
    (data : ReachableRightData g₀ πμ x y) :
    data.tightPairs.length = data.supportPairs.length + 1 := by
  induction data with
  | direct =>
      simp [ReachableRightData.tightPairs, ReachableRightData.supportPairs]
  | extend _ _ tail ih =>
      simp [ReachableRightData.tightPairs, ReachableRightData.supportPairs, ih]

/-- Helper for Example 17.55: every recorded backward support edge in ordered alternating data
comes from a positive-mass singleton of `πμ`. -/
private theorem ReachableRightData.supportPairs_mass_ne_zero
    {t : Set E} {g₀ : t → ℝ} {πμ : Measure (t × t)} {x y : t}
    (data : ReachableRightData g₀ πμ x y) :
    ∀ p ∈ data.supportPairs, πμ {p} ≠ 0 := by
  intro p hp
  induction data with
  | direct =>
      -- Proof comment: the base alternating witness has no backward support edges.
      simpa [ReachableRightData.supportPairs] using hp
  | extend htight hsupport tail ih =>
      -- Proof comment: the head support edge is positive by construction, and every tail support
      -- edge keeps the same positivity certificate by induction.
      simp [ReachableRightData.supportPairs] at hp
      rcases hp with rfl | hp
      · simpa using hsupport
      · exact ih hp

/-- Helper for Example 17.55: count how often a left endpoint appears in a list of pairs. -/
private def leftEndpointCount {α : Type*} [DecidableEq α] (x : α) (pairs : List (α × α)) : Nat :=
  (pairs.map Prod.fst).count x

/-- Helper for Example 17.55: count how often a right endpoint appears in a list of pairs. -/
private def rightEndpointCount {α : Type*} [DecidableEq α] (y : α) (pairs : List (α × α)) : Nat :=
  (pairs.map Prod.snd).count y

/-- Helper for Example 17.55: the tight/add list and the removable list carry the same left-endpoint
multiplicities once the slack atom is appended at the end. -/
private theorem ReachableRightData.leftEndpointCount_balance
    {t : Set E} [DecidableEq t] {g₀ : t → ℝ} {πμ : Measure (t × t)} {x y : t}
    (data : ReachableRightData g₀ πμ x y) :
    ∀ a, leftEndpointCount a data.tightPairs =
      leftEndpointCount a (data.supportPairs ++ [(x, y)]) := by
  intro a
  induction data generalizing a with
  | direct =>
      -- Proof comment: in the base case both sides count the single endpoint of the lone tight
      -- edge `(x, y)`.
      simp [ReachableRightData.tightPairs, ReachableRightData.supportPairs,
        leftEndpointCount]
  | extend htight hsupport tail ih =>
      rename_i x y₁ x₁ y₀
      -- Proof comment: the new front tight edge contributes one `x`, while the appended closing
      -- slack atom contributes the same `x` on the removable side; the tail induction accounts
      -- for the remaining interior multiplicities.
      calc
        leftEndpointCount a ((ReachableRightData.extend htight hsupport tail).tightPairs) =
            List.count a [x] + leftEndpointCount a tail.tightPairs := by
          by_cases hax : a = x
          · subst hax
            simp [ReachableRightData.tightPairs, leftEndpointCount, Nat.add_comm]
          · have hxa : ¬ x = a := by
              intro hxa
              exact hax hxa.symm
            simpa [ReachableRightData.tightPairs, leftEndpointCount, List.count_cons, hxa,
              Nat.add_comm]
        _ = List.count a [x] + leftEndpointCount a (tail.supportPairs ++ [(x₁, y₀)]) := by
          rw [ih a]
        _ = List.count a [x₁] + (List.count a [x] + leftEndpointCount a tail.supportPairs) := by
          simp [leftEndpointCount, List.map_append, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]
        _ = leftEndpointCount a (((ReachableRightData.extend htight hsupport tail).supportPairs) ++
            [(x, y₀)]) := by
          simp [ReachableRightData.supportPairs, leftEndpointCount, List.map_append,
            List.count_cons, List.count_append, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]

/-- Helper for Example 17.55: the tight/add list and the removable list carry the same right-endpoint
multiplicities once the slack atom is appended at the end. -/
private theorem ReachableRightData.rightEndpointCount_balance
    {t : Set E} [DecidableEq t] {g₀ : t → ℝ} {πμ : Measure (t × t)} {x y : t}
    (data : ReachableRightData g₀ πμ x y) :
    ∀ b, rightEndpointCount b data.tightPairs =
      rightEndpointCount b (data.supportPairs ++ [(x, y)]) := by
  intro b
  induction data generalizing b with
  | direct =>
      -- Proof comment: the base case records the same terminal right endpoint on both sides.
      simp [ReachableRightData.tightPairs, ReachableRightData.supportPairs,
        rightEndpointCount]
  | extend htight hsupport tail ih =>
      rename_i x y₁ x₁ y₀
      -- Proof comment: the head tight edge and the head removable support edge share the same
      -- right endpoint `y₁`, while the tail induction matches the remaining occurrences and the
      -- final slack atom contributes the terminal right endpoint `y₀`.
      calc
        rightEndpointCount b ((ReachableRightData.extend htight hsupport tail).tightPairs) =
            List.count b [y₁] + rightEndpointCount b tail.tightPairs := by
          by_cases hby₁ : b = y₁
          · subst hby₁
            simp [ReachableRightData.tightPairs, rightEndpointCount, Nat.add_comm]
          · have hy₁b : ¬ y₁ = b := by
              intro hy₁b
              exact hby₁ hy₁b.symm
            simpa [ReachableRightData.tightPairs, rightEndpointCount, List.count_cons, hy₁b,
              Nat.add_comm]
        _ = List.count b [y₁] + rightEndpointCount b (tail.supportPairs ++ [(x₁, y₀)]) := by
          rw [ih b]
        _ = List.count b [y₁] + (List.count b [y₀] + rightEndpointCount b tail.supportPairs) := by
          simp [rightEndpointCount, List.map_append, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]
        _ = rightEndpointCount b (((ReachableRightData.extend htight hsupport tail).supportPairs) ++
            [(x, y₀)]) := by
          simp [ReachableRightData.supportPairs, rightEndpointCount, List.map_append,
            List.count_cons, List.count_append, Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm]

/-- Helper for Example 17.55: ordered alternating data preserves both left-endpoint and
right-endpoint multiplicities between added tight edges and removable support edges plus the final
slack atom. -/
private theorem ReachableRightData.endpointCountBalance
    {t : Set E} [DecidableEq t] {g₀ : t → ℝ} {πμ : Measure (t × t)} {x y : t}
    (data : ReachableRightData g₀ πμ x y) :
    (∀ a, leftEndpointCount a data.tightPairs =
        leftEndpointCount a (data.supportPairs ++ [(x, y)])) ∧
      (∀ b, rightEndpointCount b data.tightPairs =
        rightEndpointCount b (data.supportPairs ++ [(x, y)])) := by
  -- Proof comment: the left and right endpoint counts are independent bookkeeping invariants, so
  -- we package the two previously separated count lemmas into one reusable statement.
  exact ⟨data.leftEndpointCount_balance, data.rightEndpointCount_balance⟩

/-- Helper for Example 17.55: the transport cost attached to a pair is just its metric distance. -/
private def pairTransportCost {α : Type*} [MetricSpace α] (p : α × α) : ℝ :=
  dist p.1 p.2

/-- Helper for Example 17.55: the total cost along the tight edges is bounded by the total cost
along the backward support edges plus the endpoint potential gap. -/
private theorem ReachableRightData.tightCost_le_supportCost_add_gap
    {t : Set E} {g₀ : t → ℝ} {πμ : Measure (t × t)} {x y : t}
    (data : ReachableRightData g₀ πμ x y)
    (hg₀feas : ∀ x y, g₀ x + (-g₀ y) ≤ dist x y) :
    (data.tightPairs.map pairTransportCost).sum ≤
      (data.supportPairs.map pairTransportCost).sum + (g₀ x - g₀ y) := by
  induction data with
  | direct htight =>
      -- Proof comment: the base path has one tight edge and no backward support edges, so the
      -- claimed estimate is exactly the tight-edge equality.
      simp [ReachableRightData.tightPairs, ReachableRightData.supportPairs,
        pairTransportCost, htight]
  | extend htight hsupport tail ih =>
      rename_i x y₁ x₁ y₀
      have hsupportFeas : g₀ x₁ - g₀ y₁ ≤ dist x₁ y₁ := by
        -- Proof comment: feasibility bounds the removable support edge by the potential gap
        -- across that edge.
        simpa [sub_eq_add_neg] using hg₀feas x₁ y₁
      -- Proof comment: the tight equalities telescope along the path, and the support-edge
      -- feasibility estimate absorbs the remaining interior gap.
      calc
        ((ReachableRightData.extend htight hsupport tail).tightPairs.map pairTransportCost).sum =
            dist x y₁ + (tail.tightPairs.map pairTransportCost).sum := by
          simp [ReachableRightData.tightPairs, pairTransportCost]
        _ = (g₀ x - g₀ y₁) + (tail.tightPairs.map pairTransportCost).sum := by
          rw [htight]
        _ ≤ (g₀ x - g₀ y₁) +
              ((tail.supportPairs.map pairTransportCost).sum + (g₀ x₁ - g₀ y₀)) := by
          gcongr
        _ = (tail.supportPairs.map pairTransportCost).sum +
              ((g₀ x₁ - g₀ y₁) + (g₀ x - g₀ y₀)) := by
          ring
        _ ≤ (tail.supportPairs.map pairTransportCost).sum +
              (dist x₁ y₁ + (g₀ x - g₀ y₀)) := by
          gcongr
        _ = ((ReachableRightData.extend htight hsupport tail).supportPairs.map pairTransportCost).sum +
              (g₀ x - g₀ y₀) := by
          simp [ReachableRightData.supportPairs, pairTransportCost, add_assoc, add_left_comm,
            add_comm]

/-- Helper for Example 17.55: once the closing slack atom is appended to the removable support
list, the removable total transport cost strictly exceeds the added tight cost. -/
private theorem ReachableRightData.strictCostDrop
    {t : Set E} {g₀ : t → ℝ} {πμ : Measure (t × t)} {x y : t}
    (data : ReachableRightData g₀ πμ x y)
    (hg₀feas : ∀ x y, g₀ x + (-g₀ y) ≤ dist x y)
    (hslack : g₀ x - g₀ y < dist x y) :
    (data.tightPairs.map pairTransportCost).sum <
      ((data.supportPairs ++ [(x, y)]).map pairTransportCost).sum := by
  have hle := data.tightCost_le_supportCost_add_gap hg₀feas
  -- Proof comment: the path telescoping bound reduces the whole inequality to the strict slack on
  -- the closing atom `(x, y)`.
  calc
    (data.tightPairs.map pairTransportCost).sum ≤
        (data.supportPairs.map pairTransportCost).sum + (g₀ x - g₀ y) := hle
    _ < (data.supportPairs.map pairTransportCost).sum + dist x y := by
      gcongr
    _ = ((data.supportPairs ++ [(x, y)]).map pairTransportCost).sum := by
      simp [pairTransportCost, List.map_append, add_assoc, add_left_comm, add_comm]

/-- Helper for Example 17.55: summing pair multiplicities over the second coordinate recovers the
multiplicity of the left endpoint. -/
private theorem sum_pairCount_eq_leftEndpointCount
    {α : Type*} [Fintype α] [DecidableEq α] (a : α) (pairs : List (α × α)) :
    ∑ b : α, pairs.count (a, b) = leftEndpointCount a pairs := by
  induction pairs with
  | nil =>
      -- Proof comment: the empty list contributes no pairs and no left endpoints.
      simp [leftEndpointCount]
  | cons p pairs ih =>
      rcases p with ⟨x, y⟩
      by_cases hxa : x = a
      · subst hxa
        -- Proof comment: the new head contributes exactly one extra pair in the `a`-row.
        calc
          ∑ b : α, List.count (x, b) ((x, y) :: pairs) =
              ∑ b : α, ((if b = y then 1 else 0) + List.count (x, b) pairs) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            by_cases hby : b = y
            · subst hby
              simp [Nat.add_comm]
            · have hneq : (x, b) ≠ (x, y) := by
                intro h
                exact hby (Prod.mk.inj h).2
              have hyb : y ≠ b := by simpa [eq_comm] using hby
              simpa [List.count_cons, hneq, hyb, Nat.add_comm]
          _ = (∑ b : α, if b = y then 1 else 0) + ∑ b : α, List.count (x, b) pairs := by
            rw [Finset.sum_add_distrib]
          _ = 1 + ∑ b : α, List.count (x, b) pairs := by
            simp
          _ = 1 + leftEndpointCount x pairs := by rw [ih]
          _ = leftEndpointCount x ((x, y) :: pairs) := by
            simp [leftEndpointCount, Nat.add_comm]
      · -- Proof comment: if the head starts at a different left endpoint, both row counts are
        -- unchanged and the induction hypothesis carries the whole computation.
        simp [leftEndpointCount, ih, hxa]

/-- Helper for Example 17.55: summing pair multiplicities over the first coordinate recovers the
multiplicity of the right endpoint. -/
private theorem sum_pairCount_eq_rightEndpointCount
    {α : Type*} [Fintype α] [DecidableEq α] (b : α) (pairs : List (α × α)) :
    ∑ a : α, pairs.count (a, b) = rightEndpointCount b pairs := by
  induction pairs with
  | nil =>
      -- Proof comment: the empty list contributes no pairs and no right endpoints.
      simp [rightEndpointCount]
  | cons p pairs ih =>
      rcases p with ⟨x, y⟩
      by_cases hyb : y = b
      · subst hyb
        -- Proof comment: the new head contributes exactly one extra pair in the `b`-column.
        calc
          ∑ a : α, List.count (a, y) ((x, y) :: pairs) =
              ∑ a : α, ((if a = x then 1 else 0) + List.count (a, y) pairs) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            by_cases hax : a = x
            · subst hax
              simp [Nat.add_comm]
            · have hneq : (a, y) ≠ (x, y) := by
                intro h
                exact hax (Prod.mk.inj h).1
              have hxa : x ≠ a := by simpa [eq_comm] using hax
              simpa [List.count_cons, hneq, hxa, Nat.add_comm]
          _ = (∑ a : α, if a = x then 1 else 0) + ∑ a : α, List.count (a, y) pairs := by
            rw [Finset.sum_add_distrib]
          _ = 1 + ∑ a : α, List.count (a, y) pairs := by
            simp
          _ = 1 + rightEndpointCount y pairs := by rw [ih]
          _ = rightEndpointCount y ((x, y) :: pairs) := by
            simp [rightEndpointCount, Nat.add_comm]
      · -- Proof comment: if the head ends at a different right endpoint, both column counts are
        -- unchanged and the induction hypothesis carries the computation.
        simp [rightEndpointCount, ih, hyb]

/-- Helper for Example 17.55: on a finite type, the weighted sum of multiplicities of a list is
the sum of the weights along that list. -/
private theorem sum_count_mul_eq_listSum
    {α : Type*} [Fintype α] [DecidableEq α] (pairs : List α) (f : α → ℝ) :
    ∑ a : α, (pairs.count a : ℝ) * f a = (pairs.map f).sum := by
  induction pairs with
  | nil =>
      -- Proof comment: the empty list has zero multiplicity at every point, so both sides vanish.
      simp
  | cons a pairs ih =>
      -- Proof comment: the head contributes one extra copy of `f a`, and the induction
      -- hypothesis handles the tail multiplicities.
      simp [List.count_cons, ih, Finset.sum_add_distrib, add_mul, add_assoc, add_left_comm,
        add_comm]

/-- Helper for Example 17.55: on a finite subtype, summing the multiplicities of all pairs in the
`a`-row recovers the left-endpoint multiplicity of `a`. -/
private theorem subtypePairCount_eq_leftEndpointCount
    {t : Set E} [Fintype t] [DecidableEq t] (a : t) (pairs : List (t × t)) :
    ∑ b : t, List.count (a, b) pairs = leftEndpointCount a pairs := by
  induction pairs with
  | nil =>
      -- Proof comment: the empty list contributes no row mass.
      simp [leftEndpointCount]
  | cons p pairs ih =>
      rcases p with ⟨x, y⟩
      by_cases hxa : x = a
      · subst hxa
        calc
          ∑ b : t, List.count (x, b) ((x, y) :: pairs) =
              ∑ b : t, ((if b = y then 1 else 0) + List.count (x, b) pairs) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            by_cases hby : b = y
            · subst hby
              simp [Nat.add_comm]
            · have hneq : (x, b) ≠ (x, y) := by
                intro h
                exact hby (Prod.mk.inj h).2
              have hyb : y ≠ b := by simpa [eq_comm] using hby
              simpa [List.count_cons, hneq, hyb, Nat.add_comm]
          _ = (∑ b : t, if b = y then 1 else 0) + ∑ b : t, List.count (x, b) pairs := by
            rw [Finset.sum_add_distrib]
          _ = 1 + ∑ b : t, List.count (x, b) pairs := by
            simp
          _ = 1 + leftEndpointCount x pairs := by rw [ih]
          _ = leftEndpointCount x ((x, y) :: pairs) := by
            simp [leftEndpointCount, Nat.add_comm]
      · simp [leftEndpointCount, ih, hxa]

/-- Helper for Example 17.55: on a finite subtype, summing the multiplicities of all pairs in the
`b`-column recovers the right-endpoint multiplicity of `b`. -/
private theorem subtypePairCount_eq_rightEndpointCount
    {t : Set E} [Fintype t] [DecidableEq t] (b : t) (pairs : List (t × t)) :
    ∑ a : t, List.count (a, b) pairs = rightEndpointCount b pairs := by
  induction pairs with
  | nil =>
      -- Proof comment: the empty list contributes no column mass.
      simp [rightEndpointCount]
  | cons p pairs ih =>
      rcases p with ⟨x, y⟩
      by_cases hyb : y = b
      · subst hyb
        calc
          ∑ a : t, List.count (a, y) ((x, y) :: pairs) =
              ∑ a : t, ((if a = x then 1 else 0) + List.count (a, y) pairs) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            by_cases hax : a = x
            · subst hax
              simp [Nat.add_comm]
            · have hneq : (a, y) ≠ (x, y) := by
                intro h
                exact hax (Prod.mk.inj h).1
              have hxa : x ≠ a := by simpa [eq_comm] using hax
              simpa [List.count_cons, hneq, hxa, Nat.add_comm]
          _ = (∑ a : t, if a = x then 1 else 0) + ∑ a : t, List.count (a, y) pairs := by
            rw [Finset.sum_add_distrib]
          _ = 1 + ∑ a : t, List.count (a, y) pairs := by
            simp
          _ = 1 + rightEndpointCount y pairs := by rw [ih]
          _ = rightEndpointCount y ((x, y) :: pairs) := by
            simp [rightEndpointCount, Nat.add_comm]
      · simp [rightEndpointCount, ih, hyb]

/-- Helper for Example 17.55: on a finite subtype, the weighted sum of multiplicities of a list
of pairs equals the list-sum of the weights. -/
private theorem subtypeSum_count_mul_eq_listSum
    {t : Set E} [Fintype t] [DecidableEq t] (pairs : List (t × t)) (f : t × t → ℝ) :
    ∑ p : t × t, (pairs.count p : ℝ) * f p = (pairs.map f).sum := by
  induction pairs with
  | nil =>
      -- Proof comment: the empty list contributes zero weight.
      simp
  | cons p pairs ih =>
      -- Proof comment: the head contributes one extra copy of `f p`, and the tail follows by
      -- induction.
      simp [List.count_cons, ih, Finset.sum_add_distrib, add_mul, add_assoc, add_left_comm,
        add_comm]

/-- Helper for Example 17.55: a finite family of positive singleton masses admits a uniform
positive perturbation scale that fits beneath every multiplicity-weighted singleton mass. -/
private theorem existsPositiveAtomicScale
    {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [Fintype α] [DecidableEq α]
    (μ : Measure α) (removable : List α)
    (hpos : ∀ p ∈ removable, 0 < μ.real {p}) :
    ∃ ε > 0, ∀ p : α, (removable.count p : ℝ) * ε ≤ μ.real {p} := by
  classical
  by_cases hrem : removable = []
  · refine ⟨1, zero_lt_one, ?_⟩
    intro p
    -- Proof comment: if there is nothing to remove, every multiplicity is zero and any positive
    -- scale works.
    simp [hrem]
  · let active : Finset α := Finset.univ.filter fun p ↦ 0 < removable.count p
    have hactive_nonempty : active.Nonempty := by
      obtain ⟨p, hp⟩ : ∃ p, p ∈ removable := by
        cases removable with
        | nil =>
            cases hrem rfl
        | cons p ps =>
            exact ⟨p, by simp⟩
      have hcount_pos : 0 < removable.count p := List.count_pos_iff.2 hp
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ p, hcount_pos⟩⟩
    let capacity : α → ℝ := fun p ↦ μ.real {p} / (removable.count p : ℝ)
    let capacities : Finset ℝ := active.image capacity
    have hcapacities_nonempty : capacities.Nonempty := by
      rcases hactive_nonempty with ⟨p, hp⟩
      exact ⟨capacity p, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
    have hcapacity_pos : ∀ p, p ∈ active → 0 < capacity p := by
      intro p hp
      have hcount_pos : 0 < removable.count p := (Finset.mem_filter.mp hp).2
      have hp_mem : p ∈ removable := List.count_pos_iff.1 hcount_pos
      have hμ_pos : 0 < μ.real {p} := hpos p hp_mem
      dsimp [capacity]
      exact div_pos hμ_pos (by exact_mod_cast hcount_pos)
    have hmin_pos : 0 < Finset.min' capacities hcapacities_nonempty := by
      have hmin_mem : Finset.min' capacities hcapacities_nonempty ∈ capacities :=
        Finset.min'_mem _ _
      rcases Finset.mem_image.mp hmin_mem with ⟨p, hp, hpEq⟩
      rw [← hpEq]
      exact hcapacity_pos p hp
    refine ⟨Finset.min' capacities hcapacities_nonempty / 2, by linarith, ?_⟩
    intro p
    by_cases hp : 0 < removable.count p
    · have hp_active : p ∈ active := by
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ p, hp⟩
      have hp_mem_capacity : capacity p ∈ capacities := by
        exact Finset.mem_image.mpr ⟨p, hp_active, rfl⟩
      have hε_le_min : Finset.min' capacities hcapacities_nonempty / 2 ≤
          Finset.min' capacities hcapacities_nonempty := by
        linarith
      have hmin_le : Finset.min' capacities hcapacities_nonempty ≤ capacity p :=
        Finset.min'_le _ _ hp_mem_capacity
      have hε_le_capacity : Finset.min' capacities hcapacities_nonempty / 2 ≤ capacity p :=
        le_trans hε_le_min hmin_le
      have hmul :=
        mul_le_mul_of_nonneg_left hε_le_capacity (by positivity : 0 ≤ (removable.count p : ℝ))
      have hcount_ne : (removable.count p : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt hp)
      calc
        (removable.count p : ℝ) * (Finset.min' capacities hcapacities_nonempty / 2) ≤
            (removable.count p : ℝ) * capacity p := hmul
        _ = μ.real {p} := by
          dsimp [capacity]
          rw [mul_div_cancel₀ _ hcount_ne]
    · have hcount_zero : removable.count p = 0 := by
        exact le_antisymm (Nat.le_of_not_gt hp) (Nat.zero_le _)
      -- Proof comment: outside the removable list, the multiplicity bound is vacuous.
      simp [hcount_zero]

/-- Helper for Example 17.55: after the graph witness is packaged as `ReachableRightData`, the only
remaining contradiction is the finite atomic perturbation of the optimal coupling. -/
private theorem reachableRightDataAtomicPerturbationContradictsOptimality
    {t : Set E} [Fintype t] (P Q : ProbabilityMeasure t)
    (πopt : WassersteinCoupling P Q) (πμ : Measure (t × t)) {x y : t}
    {g₀ : t → ℝ} (data : ReachableRightData g₀ πμ x y)
    (hπμ : πμ = ((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)))
    (hπoptCost :
      ∫ z : t × t, dist z.1 z.2 ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        (wassersteinDistance P Q).toReal)
    (hg₀feas : ∀ x y, g₀ x + (-g₀ y) ≤ dist x y)
    (hxy_mass : ((πopt.1 : Measure (t × t)) {(x, y)}) ≠ 0)
    (hslackG₀ : g₀ x - g₀ y < dist x y) :
    False := by
  classical
  letI : DecidableEq (t × t) := inferInstance
  letI : BEq (t × t) := instBEqOfDecidableEq
  subst πμ
  let removable : List (t × t) := data.supportPairs ++ [(x, y)]
  let added : List (t × t) := data.tightPairs
  have hsupportMass :
      ∀ p ∈ data.supportPairs, ((πopt.1 : Measure (t × t)) {p}) ≠ 0 :=
    data.supportPairs_mass_ne_zero
  have hendpointBalance := data.endpointCountBalance
  have hcostDrop := data.strictCostDrop hg₀feas hslackG₀
  have hremovableMassPos :
      ∀ p ∈ removable, 0 < ((πopt.1 : Measure (t × t)).real {p}) := by
    intro p hp
    simp [removable] at hp
    rcases hp with hp | hp
    · exact ENNReal.toReal_pos (hsupportMass p hp) (measure_ne_top _ _)
    · subst hp
      exact ENNReal.toReal_pos hxy_mass (measure_ne_top _ _)
  obtain ⟨ε, hεpos, hεbound⟩ :=
    existsPositiveAtomicScale ((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t))
      removable hremovableMassPos
  let weight : t × t → ℝ := fun p ↦
    (πopt.1 ({p} : Set (t × t)) : ℝ) +
      (added.count p : ℝ) * ε - (removable.count p : ℝ) * ε
  have hweight_nonneg : ∀ p, 0 ≤ weight p := by
    intro p
    have hremove_le : (removable.count p : ℝ) * ε ≤ (πopt.1 ({p} : Set (t × t)) : ℝ) := by
      simpa [MeasureTheory.ProbabilityMeasure.measureReal_eq_coe_coeFn] using hεbound p
    have hadd_nonneg : 0 ≤ (added.count p : ℝ) * ε := by positivity
    dsimp [weight]
    linarith
  let πpertμ : Measure (t × t) :=
    Measure.sum fun p : t × t ↦ ENNReal.ofReal (weight p) • Measure.dirac p
  have hπpertSingleton : ∀ p : t × t, πpertμ {p} = ENNReal.ofReal (weight p) := by
    intro p
    -- Proof comment: the perturbed measure is defined atomwise, so its singleton mass is exactly
    -- the prescribed atom weight.
    simpa [πpertμ] using
      (Measure.sum_smul_dirac_singleton (f := fun q : t × t ↦ ENNReal.ofReal (weight q))
        (a := p))
  have hπpertRealSingleton : ∀ p : t × t, πpertμ.real {p} = weight p := by
    intro p
    rw [Measure.real_def, hπpertSingleton, ENNReal.toReal_ofReal (hweight_nonneg p)]
  have hrowBase :
      ∀ a : t, ∑ b : t, ((πopt.1 : Measure (t × t)).real {(a, b)}) =
        (P : Measure t).real {a} := by
    intro a
    have hfstSingleton := congrArg (fun μ : Measure t ↦ μ {a}) πopt.2.1
    change (((πopt.1 : Measure (t × t)).fst) {a}) = ((P : Measure t) {a}) at hfstSingleton
    rw [Measure.fst_apply (measurableSet_singleton a),
      MeasureTheory.measure_preimage_fst_singleton_eq_sum] at hfstSingleton
    -- Proof comment: the first marginal of the optimal coupling records each row sum of
    -- singleton masses.
    simpa [Measure.real_def, ENNReal.toReal_sum] using
      congrArg ENNReal.toReal hfstSingleton
  have hcolBase :
      ∀ b : t, ∑ a : t, ((πopt.1 : Measure (t × t)).real {(a, b)}) =
        (Q : Measure t).real {b} := by
    intro b
    have hsndSingleton := congrArg (fun μ : Measure t ↦ μ {b}) πopt.2.2
    change (((πopt.1 : Measure (t × t)).snd) {b}) = ((Q : Measure t) {b}) at hsndSingleton
    rw [Measure.snd_apply (measurableSet_singleton b),
      MeasureTheory.measure_preimage_snd_singleton_eq_sum] at hsndSingleton
    -- Proof comment: the second marginal of the optimal coupling records each column sum of
    -- singleton masses.
    simpa [Measure.real_def, ENNReal.toReal_sum] using
      congrArg ENNReal.toReal hsndSingleton
  have rowCountSum :
      ∀ a : t, ∀ pairs : List (t × t), ∑ b : t, List.count (a, b) pairs = leftEndpointCount a pairs := by
    intro a pairs
    induction pairs with
    | nil =>
        simp [leftEndpointCount]
    | cons p pairs ih =>
        rcases p with ⟨x, y⟩
        by_cases hxa : x = a
        · subst hxa
          calc
            ∑ b : t, List.count (x, b) ((x, y) :: pairs) =
                ∑ b : t, ((if b = y then 1 else 0) + List.count (x, b) pairs) := by
              refine Finset.sum_congr rfl ?_
              intro b hb
              by_cases hby : b = y
              · subst hby
                simp [Nat.add_comm]
              · have hneq : (x, b) ≠ (x, y) := by
                  intro h
                  exact hby (Prod.mk.inj h).2
                have hyb : y ≠ b := by simpa [eq_comm] using hby
                simpa [List.count_cons, hneq, hyb, Nat.add_comm]
            _ = (∑ b : t, if b = y then 1 else 0) + ∑ b : t, List.count (x, b) pairs := by
              rw [Finset.sum_add_distrib]
            _ = 1 + ∑ b : t, List.count (x, b) pairs := by
              simp
            _ = 1 + leftEndpointCount x pairs := by rw [ih]
            _ = leftEndpointCount x ((x, y) :: pairs) := by
              simp [leftEndpointCount, Nat.add_comm]
        · simp [leftEndpointCount, ih, hxa]
  have colCountSum :
      ∀ b : t, ∀ pairs : List (t × t), ∑ a : t, List.count (a, b) pairs = rightEndpointCount b pairs := by
    intro b pairs
    induction pairs with
    | nil =>
        simp [rightEndpointCount]
    | cons p pairs ih =>
        rcases p with ⟨x, y⟩
        by_cases hyb : y = b
        · subst hyb
          calc
            ∑ a : t, List.count (a, y) ((x, y) :: pairs) =
                ∑ a : t, ((if a = x then 1 else 0) + List.count (a, y) pairs) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              by_cases hax : a = x
              · subst hax
                simp [Nat.add_comm]
              · have hneq : (a, y) ≠ (x, y) := by
                  intro h
                  exact hax (Prod.mk.inj h).1
                have hxa : x ≠ a := by simpa [eq_comm] using hax
                simpa [List.count_cons, hneq, hxa, Nat.add_comm]
            _ = (∑ a : t, if a = x then 1 else 0) + ∑ a : t, List.count (a, y) pairs := by
              rw [Finset.sum_add_distrib]
            _ = 1 + ∑ a : t, List.count (a, y) pairs := by
              simp
            _ = 1 + rightEndpointCount y pairs := by rw [ih]
            _ = rightEndpointCount y ((x, y) :: pairs) := by
              simp [rightEndpointCount, Nat.add_comm]
        · simp [rightEndpointCount, ih, hyb]
  have countWeightedSum :
      ∀ pairs : List (t × t), ∀ f : t × t → ℝ,
        ∑ p : t × t, (List.count p pairs : ℝ) * f p = (pairs.map f).sum := by
    intro pairs f
    induction pairs with
    | nil =>
        simp
    | cons p pairs ih =>
        simp [List.count_cons, ih, Finset.sum_add_distrib, add_mul, add_assoc, add_left_comm,
          add_comm]
  have hrowWeight :
      ∀ a : t, ∑ b : t, weight (a, b) = (P : Measure t).real {a} := by
    intro a
    have haddRow :
        ∑ b : t, ((added.count (a, b) : ℝ) * ε) =
          (leftEndpointCount a added : ℝ) * ε := by
      have hcountNat :
          ∑ b : t, List.count (a, b) added = leftEndpointCount a added :=
        by
          exact rowCountSum a added
      have hcount :
          ∑ b : t, (added.count (a, b) : ℝ) = (leftEndpointCount a added : ℝ) := by
        exact_mod_cast hcountNat
      calc
        ∑ b : t, ((added.count (a, b) : ℝ) * ε) =
            (∑ b : t, (added.count (a, b) : ℝ)) * ε := by
          rw [Finset.sum_mul]
        _ = (leftEndpointCount a added : ℝ) * ε := by rw [hcount]
    have hremoveRow :
        ∑ b : t, ((removable.count (a, b) : ℝ) * ε) =
          (leftEndpointCount a removable : ℝ) * ε := by
      have hcountNat :
          ∑ b : t, List.count (a, b) removable = leftEndpointCount a removable :=
        by
          exact rowCountSum a removable
      have hcount :
          ∑ b : t, (removable.count (a, b) : ℝ) = (leftEndpointCount a removable : ℝ) := by
        exact_mod_cast hcountNat
      calc
        ∑ b : t, ((removable.count (a, b) : ℝ) * ε) =
            (∑ b : t, (removable.count (a, b) : ℝ)) * ε := by
          rw [Finset.sum_mul]
        _ = (leftEndpointCount a removable : ℝ) * ε := by rw [hcount]
    have hbalanceR :
        (leftEndpointCount a added : ℝ) = (leftEndpointCount a removable : ℝ) := by
      exact_mod_cast hendpointBalance.1 a
    -- Proof comment: row sums are unchanged because the added and removed atomic corrections have
    -- identical left-endpoint multiplicities.
    calc
      ∑ b : t, weight (a, b) =
          ∑ b : t, ((πopt.1 : Measure (t × t)).real {(a, b)}) +
            ∑ b : t, ((added.count (a, b) : ℝ) * ε) -
            ∑ b : t, ((removable.count (a, b) : ℝ) * ε) := by
        simp [weight, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (P : Measure t).real {a} +
            (leftEndpointCount a added : ℝ) * ε -
            (leftEndpointCount a removable : ℝ) * ε := by
        rw [hrowBase, haddRow, hremoveRow]
      _ = (P : Measure t).real {a} +
            (leftEndpointCount a removable : ℝ) * ε -
            (leftEndpointCount a removable : ℝ) * ε := by
        rw [hbalanceR]
      _ = (P : Measure t).real {a} := by
        ring
  have hcolWeight :
      ∀ b : t, ∑ a : t, weight (a, b) = (Q : Measure t).real {b} := by
    intro b
    have haddCol :
        ∑ a : t, ((added.count (a, b) : ℝ) * ε) =
          (rightEndpointCount b added : ℝ) * ε := by
      have hcountNat :
          ∑ a : t, List.count (a, b) added = rightEndpointCount b added :=
        by
          exact colCountSum b added
      have hcount :
          ∑ a : t, (added.count (a, b) : ℝ) = (rightEndpointCount b added : ℝ) := by
        exact_mod_cast hcountNat
      calc
        ∑ a : t, ((added.count (a, b) : ℝ) * ε) =
            (∑ a : t, (added.count (a, b) : ℝ)) * ε := by
          rw [Finset.sum_mul]
        _ = (rightEndpointCount b added : ℝ) * ε := by rw [hcount]
    have hremoveCol :
        ∑ a : t, ((removable.count (a, b) : ℝ) * ε) =
          (rightEndpointCount b removable : ℝ) * ε := by
      have hcountNat :
          ∑ a : t, List.count (a, b) removable = rightEndpointCount b removable :=
        by
          exact colCountSum b removable
      have hcount :
          ∑ a : t, (removable.count (a, b) : ℝ) = (rightEndpointCount b removable : ℝ) := by
        exact_mod_cast hcountNat
      calc
        ∑ a : t, ((removable.count (a, b) : ℝ) * ε) =
            (∑ a : t, (removable.count (a, b) : ℝ)) * ε := by
          rw [Finset.sum_mul]
        _ = (rightEndpointCount b removable : ℝ) * ε := by rw [hcount]
    have hbalanceR :
        (rightEndpointCount b added : ℝ) = (rightEndpointCount b removable : ℝ) := by
      exact_mod_cast hendpointBalance.2 b
    -- Proof comment: the same endpoint-count bookkeeping preserves every column sum.
    calc
      ∑ a : t, weight (a, b) =
          ∑ a : t, ((πopt.1 : Measure (t × t)).real {(a, b)}) +
            ∑ a : t, ((added.count (a, b) : ℝ) * ε) -
            ∑ a : t, ((removable.count (a, b) : ℝ) * ε) := by
        simp [weight, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (Q : Measure t).real {b} +
            (rightEndpointCount b added : ℝ) * ε -
            (rightEndpointCount b removable : ℝ) * ε := by
        rw [hcolBase, haddCol, hremoveCol]
      _ = (Q : Measure t).real {b} +
            (rightEndpointCount b removable : ℝ) * ε -
            (rightEndpointCount b removable : ℝ) * ε := by
        rw [hbalanceR]
      _ = (Q : Measure t).real {b} := by
        ring
  have hfstPert : πpertμ.fst = (P : Measure t) := by
    refine Measure.ext_of_singleton ?_
    intro a
    -- Proof comment: the first marginal singleton masses are exactly the row sums of the atomic
    -- weights, which we already matched to `P`.
    calc
      πpertμ.fst {a} = πpertμ (Prod.fst ⁻¹' {a}) := by
        rw [Measure.fst_apply (measurableSet_singleton a)]
      _ = ∑ b : t, πpertμ {(a, b)} := by
        simpa using MeasureTheory.measure_preimage_fst_singleton_eq_sum πpertμ a
      _ = ∑ b : t, ENNReal.ofReal (weight (a, b)) := by
        refine Finset.sum_congr rfl ?_
        intro b hb
        rw [hπpertSingleton]
      _ = ENNReal.ofReal (∑ b : t, weight (a, b)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        intro b hb
        exact hweight_nonneg (a, b)
      _ = ENNReal.ofReal ((P : Measure t).real {a}) := by rw [hrowWeight]
      _ = (P : Measure t) {a} := by
        simp [Measure.real_def]
  have hsndPert : πpertμ.snd = (Q : Measure t) := by
    refine Measure.ext_of_singleton ?_
    intro b
    -- Proof comment: the second marginal singleton masses are the column sums of the same atomic
    -- weights, so the endpoint balance also recovers `Q`.
    calc
      πpertμ.snd {b} = πpertμ (Prod.snd ⁻¹' {b}) := by
        rw [Measure.snd_apply (measurableSet_singleton b)]
      _ = ∑ a : t, πpertμ {(a, b)} := by
        simpa using MeasureTheory.measure_preimage_snd_singleton_eq_sum πpertμ b
      _ = ∑ a : t, ENNReal.ofReal (weight (a, b)) := by
        refine Finset.sum_congr rfl ?_
        intro a ha
        rw [hπpertSingleton]
      _ = ENNReal.ofReal (∑ a : t, weight (a, b)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        intro a ha
        exact hweight_nonneg (a, b)
      _ = ENNReal.ofReal ((Q : Measure t).real {b}) := by rw [hcolWeight]
      _ = (Q : Measure t) {b} := by
        simp [Measure.real_def]
  have hπpertProb : IsProbabilityMeasure πpertμ := by
    refine IsProbabilityMeasure.mk ?_
    -- Proof comment: one exact marginal equality is enough to recover total mass `1` for the
    -- perturbed atomic measure.
    calc
      πpertμ Set.univ = πpertμ.fst Set.univ := by
        symm
        rw [Measure.fst_apply MeasurableSet.univ]
        simp
      _ = (P : Measure t) Set.univ := by rw [hfstPert]
      _ = 1 := by simp
  let πpert : WassersteinCoupling P Q := ⟨⟨πpertμ, hπpertProb⟩, ⟨hfstPert, hsndPert⟩⟩
  let htfin : t.Finite := Set.toFinite t
  have hπpertCost_lt_top :
      ∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
          ∂((πpert.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) < ∞ :=
    finiteCoupling_cost_lt_top (htfin := htfin) πpert
  have hπpertCostReal :
      (∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
          ∂((πpert.1 : ProbabilityMeasure (t × t)) : Measure (t × t))).toReal =
        ∫ z : t × t, dist z.1 z.2 ∂πpertμ := by
    -- Proof comment: on the finite product space, the nonnegative transport integrand has the
    -- same ordinary integral as the `toReal` of its `lintegral`.
    symm
    exact MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z ↦ dist_nonneg)
      ((continuous_fst.dist continuous_snd).aestronglyMeasurable)
  have hπoptCostSum :
      ∫ z : t × t, dist z.1 z.2
          ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        ∑ p : t × t, (πopt.1 ({p} : Set (t × t)) : ℝ) * pairTransportCost p := by
    -- Proof comment: the optimal coupling cost is the finite weighted sum of singleton masses
    -- times transport costs.
    simpa [pairTransportCost, smul_eq_mul] using
      (MeasureTheory.integral_fintype
        (μ := ((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)))
        (f := fun p : t × t ↦ dist p.1 p.2)
        (MeasureTheory.Integrable.of_finite :
          Integrable (fun p : t × t ↦ dist p.1 p.2)
            (((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)))))
  have hπpertCostSum :
      ∫ z : t × t, dist z.1 z.2 ∂πpertμ =
        ∑ p : t × t, weight p * pairTransportCost p := by
    calc
      ∫ z : t × t, dist z.1 z.2 ∂πpertμ =
          ∑ p : t × t, πpertμ.real {p} * dist p.1 p.2 := by
        simpa [smul_eq_mul] using
          (MeasureTheory.integral_fintype (μ := πpertμ)
            (f := fun p : t × t ↦ dist p.1 p.2)
            (MeasureTheory.Integrable.of_finite :
              Integrable (fun p : t × t ↦ dist p.1 p.2) πpertμ))
      _ = ∑ p : t × t, weight p * pairTransportCost p := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        rw [hπpertRealSingleton]
        simp [pairTransportCost]
  have haddContribution :
      ∑ p : t × t, (((added.count p : ℝ) * ε) * pairTransportCost p) =
        ε * (added.map pairTransportCost).sum := by
    have hcountCost :
        ∑ p : t × t, (List.count p added : ℝ) * pairTransportCost p =
          (added.map pairTransportCost).sum := by
      exact countWeightedSum added pairTransportCost
    calc
      ∑ p : t × t, (((added.count p : ℝ) * ε) * pairTransportCost p) =
          ∑ p : t × t, ε * ((added.count p : ℝ) * pairTransportCost p) := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        ring
      _ = ε * ∑ p : t × t, (added.count p : ℝ) * pairTransportCost p := by
        rw [Finset.mul_sum]
      _ = ε * (added.map pairTransportCost).sum := by
        rw [hcountCost]
  have hremoveContribution :
      ∑ p : t × t, (((removable.count p : ℝ) * ε) * pairTransportCost p) =
        ε * (removable.map pairTransportCost).sum := by
    have hcountCost :
        ∑ p : t × t, (List.count p removable : ℝ) * pairTransportCost p =
          (removable.map pairTransportCost).sum := by
      exact countWeightedSum removable pairTransportCost
    calc
      ∑ p : t × t, (((removable.count p : ℝ) * ε) * pairTransportCost p) =
          ∑ p : t × t, ε * ((removable.count p : ℝ) * pairTransportCost p) := by
        refine Finset.sum_congr rfl ?_
        intro p hp
        ring
      _ = ε * ∑ p : t × t, (removable.count p : ℝ) * pairTransportCost p := by
        rw [Finset.mul_sum]
      _ = ε * (removable.map pairTransportCost).sum := by
        rw [hcountCost]
  have hπpertCostFormula :
      ∫ z : t × t, dist z.1 z.2 ∂πpertμ =
        ∫ z : t × t, dist z.1 z.2
          ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) +
            ε * ((added.map pairTransportCost).sum - (removable.map pairTransportCost).sum) := by
    calc
      ∫ z : t × t, dist z.1 z.2 ∂πpertμ =
          ∑ p : t × t, weight p * pairTransportCost p := hπpertCostSum
      _ =
          ∑ p : t × t, (πopt.1 ({p} : Set (t × t)) : ℝ) * pairTransportCost p +
            ∑ p : t × t, (((added.count p : ℝ) * ε) * pairTransportCost p) -
            ∑ p : t × t, (((removable.count p : ℝ) * ε) * pairTransportCost p) := by
        calc
          ∑ p : t × t, weight p * pairTransportCost p =
              ∑ p : t × t,
                ((((πopt.1 ({p} : Set (t × t)) : ℝ)) * pairTransportCost p) +
                  (((added.count p : ℝ) * ε) * pairTransportCost p) -
                  (((removable.count p : ℝ) * ε) * pairTransportCost p)) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            dsimp [weight]
            ring
          _ =
              ∑ p : t × t, (πopt.1 ({p} : Set (t × t)) : ℝ) * pairTransportCost p +
                ∑ p : t × t, (((added.count p : ℝ) * ε) * pairTransportCost p) -
                ∑ p : t × t, (((removable.count p : ℝ) * ε) * pairTransportCost p) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      _ =
          ∫ z : t × t, dist z.1 z.2
            ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) +
              ε * ((added.map pairTransportCost).sum - (removable.map pairTransportCost).sum) := by
        rw [← hπoptCostSum, haddContribution, hremoveContribution]
        ring
  have hπpertCost_lt :
      ∫ z : t × t, dist z.1 z.2 ∂πpertμ <
        ∫ z : t × t, dist z.1 z.2
          ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
    have hdelta_neg :
        ε * ((added.map pairTransportCost).sum - (removable.map pairTransportCost).sum) < 0 := by
      have hdrop_neg :
          (added.map pairTransportCost).sum - (removable.map pairTransportCost).sum < 0 := by
        linarith [hcostDrop]
      exact mul_neg_of_pos_of_neg hεpos hdrop_neg
    -- Proof comment: the cost change is the positive scale `ε` times the negative path-drop
    -- quantity, so the perturbed coupling is strictly cheaper.
    rw [hπpertCostFormula]
    linarith
  have hwasserstein_ne_top : wassersteinDistance P Q ≠ ∞ := by
    exact ne_of_lt (finiteSubtype_wassersteinDistance_lt_top htfin P Q)
  have hwasserstein_le_pert :
      wassersteinDistance P Q ≤
        ∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
          ∂((πpert.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
    -- Proof comment: the perturbed measure is still a coupling of `P` and `Q`, so its cost lies
    -- above the defining infimum.
    rw [wassersteinDistance]
    exact sInf_le ⟨πpert, rfl⟩
  have hwasserstein_real_le :
      (wassersteinDistance P Q).toReal ≤
        ∫ z : t × t, dist z.1 z.2 ∂πpertμ := by
    have hle_ofReal :
        ENNReal.ofReal ((wassersteinDistance P Q).toReal) ≤
          ∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
            ∂((πpert.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
      simpa [ENNReal.ofReal_toReal hwasserstein_ne_top] using hwasserstein_le_pert
    rw [← hπpertCostReal]
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt hπpertCost_lt_top)).1 hle_ofReal
  have hπpertCost_lt_wasserstein :
      ∫ z : t × t, dist z.1 z.2 ∂πpertμ < (wassersteinDistance P Q).toReal := by
    calc
      ∫ z : t × t, dist z.1 z.2 ∂πpertμ <
          ∫ z : t × t, dist z.1 z.2
            ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := hπpertCost_lt
      _ = (wassersteinDistance P Q).toReal := hπoptCost
  exact (not_lt_of_ge hwasserstein_real_le) hπpertCost_lt_wasserstein

/-- Helper for Example 17.55: the only remaining owner step is that the slack atom cannot be
reachable in the reduced-cost/support graph. -/
private theorem slackSupportAtomNotReachable
    {t : Set E} [Fintype t] (P Q : ProbabilityMeasure t)
    (πopt : WassersteinCoupling P Q) (πμ : Measure (t × t)) {x₀ y₀ : t}
    {g₀ : t → ℝ} {step : Sum t t → Sum t t → Prop}
    (hπμ : πμ = ((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)))
    (hπoptCost :
      ∫ z : t × t, dist z.1 z.2 ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        (wassersteinDistance P Q).toReal)
    (hg₀feas : ∀ x y, g₀ x + (-g₀ y) ≤ dist x y)
    (hxy_mass : ((πopt.1 : Measure (t × t)) {(x₀, y₀)}) ≠ 0)
    (hslackG₀ : g₀ x₀ - g₀ y₀ < dist x₀ y₀)
    (hstep_tight : ∀ x y, step (Sum.inl x) (Sum.inr y) ↔ g₀ x - g₀ y = dist x y)
    (hstep_support : ∀ x y, step (Sum.inr y) (Sum.inl x) ↔ πμ {(x, y)} ≠ 0)
    (hstep_right_right : ∀ y y' : t, ¬ step (Sum.inr y) (Sum.inr y'))
    (hstep_left_left : ∀ x x' : t, ¬ step (Sum.inl x) (Sum.inl x')) :
    ¬ Relation.ReflTransGen step (Sum.inl x₀) (Sum.inr y₀) := by
  -- Route correction: the reachability parsing is now complete; the owner lemma delegates the
  -- remaining work to one theorem-local perturbation contradiction built from `ReachableRightData`.
  intro hy₀Reach
  -- Proof comment: the explicit list-valued alternating witness packages exactly the data needed
  -- for the finite atomic perturbation contradiction.
  have hpathData : ReachableRightData g₀ πμ x₀ y₀ :=
    reachableRightData_of_reflTransGen hstep_left_left hstep_right_right hstep_tight
      hstep_support hy₀Reach
  exact reachableRightDataAtomicPerturbationContradictsOptimality
    (P := P) (Q := Q) (πopt := πopt) (πμ := πμ) (x := x₀) (y := y₀) hpathData
    hπμ hπoptCost hg₀feas hxy_mass hslackG₀

/-- Helper for Example 17.55: the remaining finite reverse-duality step is to show that the
Wasserstein value is below the supremum of the anchored finite dual set. -/
private theorem wassersteinDistanceToReal_le_sSupAnchoredDual
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t)
    (πopt : WassersteinCoupling P Q)
    (hπoptCost :
      ∫ z : t × t, dist z.1 z.2 ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        (wassersteinDistance P Q).toReal)
    {u v : t → ℝ}
    (hfeas : ∀ x y, u x + v y ≤ dist x y)
    (hmax :
      ∀ u' v' : t → ℝ, (∀ x y, u' x + v' y ≤ dist x y) →
        ∫ x, u' x ∂(P : Measure t) + ∫ y, v' y ∂(Q : Measure t) ≤
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t)) :
    (wassersteinDistance P Q).toReal ≤
      sSup {r : ℝ | ∃ g : t → ℝ,
        g a₀ = 0 ∧
          LipschitzWith 1 g ∧
          r = ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t)} := by
  classical
  letI : Fintype t := htfin.fintype
  let dualSet : Set ℝ :=
    {r : ℝ | ∃ g : t → ℝ,
      g a₀ = 0 ∧
        LipschitzWith 1 g ∧
        r = ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t)}
  have hobjSup :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) = sSup dualSet := by
    -- Proof comment: pair maximality already identifies the current objective with the anchored
    -- dual supremum, so the remaining work is only the reverse inequality from the primal side.
    simpa [dualSet] using
      maximizingTransportPotentialPair_objective_eq_sSupAnchoredDual
        (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q) hfeas hmax
  by_contra hdualLower
  push Not at hdualLower
  have hgap :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) <
        ∫ z : t × t, dist z.1 z.2
          ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
    -- Proof comment: under the negated target, the maximizing pair objective is strictly below
    -- the cost of the chosen optimal coupling.
    rw [hobjSup]
    linarith
  obtain ⟨x₀, y₀, hxy_mass, hxy_slack⟩ :=
    positiveMassSlackAtom_of_objective_lt_cost
      (htfin := htfin) (π := πopt) hfeas hgap
  obtain ⟨g, hgLip, hu_le, hv_le, hu_eq, hv_eq, hobjEqG⟩ :=
    transportEnvelope_eq_on_positiveMarginals_of_maximizingPair
      (htfin := htfin) (P := P) (Q := Q) hfeas hmax
  have hx₀P_mass : ((P : Measure t) {x₀}) ≠ 0 := by
    exact (coupling_positiveAtom_gives_positiveMarginals
      (htfin := htfin) (π := πopt) hxy_mass).1
  have hy₀Q_mass : ((Q : Measure t) {y₀}) ≠ 0 := by
    exact (coupling_positiveAtom_gives_positiveMarginals
      (htfin := htfin) (π := πopt) hxy_mass).2
  have hslackG : g x₀ - g y₀ < dist x₀ y₀ := by
    -- Proof comment: on every marginal atom seen by the slack support atom, the maximizing pair
    -- agrees with its Lipschitz envelope, so the slack transfers to that envelope.
    have hux₀ : u x₀ = g x₀ := hu_eq x₀ hx₀P_mass
    have hvy₀ : v y₀ = -g y₀ := hv_eq y₀ hy₀Q_mass
    linarith [hxy_slack]
  let g₀ : t → ℝ := fun x ↦ g x - g a₀
  have hg₀ : g₀ a₀ = 0 := by
    simp [g₀]
  have hg₀Lip : LipschitzWith 1 g₀ := by
    -- Proof comment: subtracting the anchor value preserves all pairwise differences, hence the
    -- same `1`-Lipschitz constant.
    refine (lipschitzWith_one_iff_norm_sub_le_dist (g := g₀)).2 ?_
    intro x y
    have hxy : ‖g x - g y‖ ≤ dist x y :=
      (lipschitzWith_one_iff_norm_sub_le_dist (g := g)).1 hgLip x y
    have hsame : g₀ x - g₀ y = g x - g y := by
      dsimp [g₀]
      ring
    simpa [hsame] using hxy
  have hg₀Eq :
      ∫ x, g₀ x ∂(P : Measure t) - ∫ y, g₀ y ∂(Q : Measure t) =
        ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) := by
    have hPIntG : Integrable g (P : Measure t) := MeasureTheory.Integrable.of_finite
    have hQIntG : Integrable g (Q : Measure t) := MeasureTheory.Integrable.of_finite
    -- Proof comment: translating by the anchor value subtracts the same constant from both
    -- probability integrals, so the signed objective is unchanged.
    calc
      ∫ x, g₀ x ∂(P : Measure t) - ∫ y, g₀ y ∂(Q : Measure t) =
          (∫ x, g x ∂(P : Measure t) - ∫ x, g a₀ ∂(P : Measure t)) -
            (∫ y, g y ∂(Q : Measure t) - ∫ y, g a₀ ∂(Q : Measure t)) := by
        simp [g₀, MeasureTheory.integral_sub hPIntG (integrable_const _),
          MeasureTheory.integral_sub hQIntG (integrable_const _)]
      _ = ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) := by
        simp
  have hslackG₀ : g₀ x₀ - g₀ y₀ < dist x₀ y₀ := by
    -- Proof comment: anchoring subtracts a common constant, so the strict slack survives.
    dsimp [g₀]
    linarith [hslackG]
  have hg₀Sup :
      ∫ x, g₀ x ∂(P : Measure t) - ∫ y, g₀ y ∂(Q : Measure t) = sSup dualSet := by
    -- Proof comment: the anchored envelope carries the same objective as the maximizing pair, and
    -- that pair objective already equals the anchored dual supremum.
    rw [hg₀Eq, ← hobjEqG, hobjSup]
  have hg₀Gap :
      ∫ x, g₀ x ∂(P : Measure t) - ∫ y, g₀ y ∂(Q : Measure t) <
        ∫ z : t × t, dist z.1 z.2
          ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
    rw [hg₀Sup, hπoptCost]
    exact hdualLower
  have hg₀feas : ∀ x y, g₀ x + (-g₀ y) ≤ dist x y := by
    intro x y
    -- Proof comment: every anchored `1`-Lipschitz witness defines a feasible pair
    -- `(g₀, fun y ↦ -g₀ y)` for the finite dual problem.
    have hxy : ‖g₀ x - g₀ y‖ ≤ dist x y :=
      (lipschitzWith_one_iff_norm_sub_le_dist (g := g₀)).1 hg₀Lip x y
    have hle : g₀ x + (-g₀ y) ≤ ‖g₀ x - g₀ y‖ := by
      simpa [sub_eq_add_neg] using (le_abs_self (g₀ x - g₀ y))
    exact le_trans hle hxy
  have hg₀max :
      ∀ u' v' : t → ℝ, (∀ x y, u' x + v' y ≤ dist x y) →
        ∫ x, u' x ∂(P : Measure t) + ∫ y, v' y ∂(Q : Measure t) ≤
          ∫ x, g₀ x ∂(P : Measure t) + ∫ y, (-g₀ y) ∂(Q : Measure t) := by
    intro u' v' hfeas'
    -- Proof comment: the anchored envelope pair has the same objective as the original
    -- maximizing pair, so it inherits the same maximality property.
    have hbase := hmax u' v' hfeas'
    have hg₀Obj :
        ∫ x, g₀ x ∂(P : Measure t) + ∫ y, (-g₀ y) ∂(Q : Measure t) =
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := by
      calc
        ∫ x, g₀ x ∂(P : Measure t) + ∫ y, (-g₀ y) ∂(Q : Measure t) =
            ∫ x, g₀ x ∂(P : Measure t) - ∫ y, g₀ y ∂(Q : Measure t) := by
          rw [MeasureTheory.integral_neg]
          ring
        _ = ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) := hg₀Eq
        _ = ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := hobjEqG.symm
    linarith
  let πμ : Measure (t × t) := ((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t))
  let step : Sum t t → Sum t t → Prop := fun a b ↦
    match a, b with
    | Sum.inl x, Sum.inr y => g₀ x - g₀ y = dist x y
    | Sum.inr y, Sum.inl x => πμ {(x, y)} ≠ 0
    | _, _ => False
  let A : Set t := {x | Relation.ReflTransGen step (Sum.inl x₀) (Sum.inl x)}
  let B : Set t := {y | Relation.ReflTransGen step (Sum.inl x₀) (Sum.inr y)}
  have hx₀A : x₀ ∈ A := by
    -- Proof comment: the start vertex is reachable from itself by reflexivity.
    exact Relation.ReflTransGen.refl
  have hA : ∀ x, x ∈ A ↔ Relation.ReflTransGen step (Sum.inl x₀) (Sum.inl x) := by
    intro x
    rfl
  have hB : ∀ y, y ∈ B ↔ Relation.ReflTransGen step (Sum.inl x₀) (Sum.inr y) := by
    intro y
    rfl
  have hstep_tight : ∀ x y, step (Sum.inl x) (Sum.inr y) ↔ g₀ x - g₀ y = dist x y := by
    intro x y
    simp [step]
  have hstep_support : ∀ x y, step (Sum.inr y) (Sum.inl x) ↔ πμ {(x, y)} ≠ 0 := by
    intro x y
    simp [step]
  have hstep_right_right : ∀ y y' : t, ¬ step (Sum.inr y) (Sum.inr y') := by
    intro y y'
    simp [step]
  have hstep_left_left : ∀ x x' : t, ¬ step (Sum.inl x) (Sum.inl x') := by
    intro x x'
    simp [step]
  have hy₀_not_reachable : ¬ Relation.ReflTransGen step (Sum.inl x₀) (Sum.inr y₀) := by
    exact slackSupportAtomNotReachable (P := P) (Q := Q) (πopt := πopt) (πμ := πμ)
      (x₀ := x₀) (y₀ := y₀) (g₀ := g₀) (step := step) rfl hπoptCost hg₀feas hxy_mass
      hslackG₀ hstep_tight hstep_support hstep_right_right hstep_left_left
  have hy₀_not_B : y₀ ∉ B := by
    -- Proof comment: the right reachable set is defined exactly by the reduced-cost reachability
    -- relation, so the owner lemma immediately excludes `y₀`.
    intro hy₀B
    exact hy₀_not_reachable (by simpa [B] using hy₀B)
  have hcrossSlack :
      ∀ x ∈ A, ∀ y ∉ B, g₀ x + (-g₀ y) < dist x y := by
    -- Proof comment: this is the abstract cut consequence of the reduced-cost graph definition.
    exact tightSupportReachabilityCrossSlack hg₀feas hstep_tight hA hB
  have hAmeas : MeasurableSet A := (Set.toFinite A).measurableSet
  have hBmeas : MeasurableSet B := (Set.toFinite B).measurableSet
  have hPA :
      ((P : Measure t).real A) = πμ.real (A ×ˢ (Set.univ : Set t)) := by
    -- Proof comment: the first marginal identity rewrites the `P`-mass of `A` as the coupling
    -- mass of the left rectangle `A × univ`.
    calc
      ((P : Measure t).real A) = ENNReal.toReal ((P : Measure t) A) := by
        rw [Measure.real_def]
      _ = ENNReal.toReal (πμ.fst A) := by rw [← πopt.2.1]
      _ = ENNReal.toReal (πμ (Prod.fst ⁻¹' A)) := by rw [Measure.fst_apply hAmeas]
      _ = ENNReal.toReal (πμ (A ×ˢ (Set.univ : Set t))) := by
        rw [show Prod.fst ⁻¹' A = A ×ˢ (Set.univ : Set t) by
          ext z
          simp]
      _ = πμ.real (A ×ˢ (Set.univ : Set t)) := by
        rw [Measure.real_def]
  have hQB :
      ((Q : Measure t).real B) = πμ.real ((Set.univ : Set t) ×ˢ B) := by
    -- Proof comment: the second marginal identity gives the analogous rectangle formula for `Q`.
    calc
      ((Q : Measure t).real B) = ENNReal.toReal ((Q : Measure t) B) := by
        rw [Measure.real_def]
      _ = ENNReal.toReal (πμ.snd B) := by rw [← πopt.2.2]
      _ = ENNReal.toReal (πμ (Prod.snd ⁻¹' B)) := by rw [Measure.snd_apply hBmeas]
      _ = ENNReal.toReal (πμ ((Set.univ : Set t) ×ˢ B)) := by
        rw [show Prod.snd ⁻¹' B = (Set.univ : Set t) ×ˢ B by
          ext z
          simp]
      _ = πμ.real ((Set.univ : Set t) ×ˢ B) := by
        rw [Measure.real_def]
  have hAB_disjoint : Disjoint (A ×ˢ B : Set (t × t)) (A ×ˢ Bᶜ) := by
    rw [Set.disjoint_left]
    intro z hzAB hzABc
    exact hzABc.2 hzAB.2
  have hAcB_disjoint : Disjoint (A ×ˢ B : Set (t × t)) (Aᶜ ×ˢ B) := by
    rw [Set.disjoint_left]
    intro z hzAB hzAcB
    exact hzAcB.1 hzAB.1
  have hPA_split :
      πμ.real (A ×ˢ (Set.univ : Set t)) =
        πμ.real (A ×ˢ B : Set (t × t)) + πμ.real (A ×ˢ Bᶜ : Set (t × t)) := by
    -- Proof comment: the left rectangle splits into the reachable-right part and its complement.
    rw [show (A ×ˢ (Set.univ : Set t) : Set (t × t)) = (A ×ˢ B) ∪ (A ×ˢ Bᶜ) by
      ext z
      by_cases hzB : z.2 ∈ B <;> simp [hzB]]
    exact MeasureTheory.measureReal_union hAB_disjoint (hAmeas.prod hBmeas.compl)
  have hQB_split :
      πμ.real ((Set.univ : Set t) ×ˢ B) =
        πμ.real (A ×ˢ B : Set (t × t)) + πμ.real (Aᶜ ×ˢ B : Set (t × t)) := by
    -- Proof comment: the right rectangle splits according to whether the left endpoint is
    -- reachable from `x₀`.
    rw [show ((Set.univ : Set t) ×ˢ B : Set (t × t)) = (A ×ˢ B) ∪ (Aᶜ ×ˢ B) by
      ext z
      by_cases hzA : z.1 ∈ A <;> simp [hzA]]
    exact MeasureTheory.measureReal_union hAcB_disjoint (hAmeas.compl.prod hBmeas)
  have hAcB_zero : πμ.real (Aᶜ ×ˢ B : Set (t × t)) = 0 := by
    -- Proof comment: the reachable-right set is predecessor-closed under support edges.
    exact tightSupportReachabilityRectangleZero (πμ := πμ) hA hB hstep_support
  have hxy_subset : ({(x₀, y₀)} : Set (t × t)) ⊆ A ×ˢ Bᶜ := by
    intro z hz
    have hzEq : z = (x₀, y₀) := by simpa using hz
    subst z
    exact ⟨hx₀A, hy₀_not_B⟩
  have hABc_pos : 0 < πμ.real (A ×ˢ Bᶜ : Set (t × t)) := by
    -- Proof comment: the original slack support atom lies in the cross rectangle `A × Bᶜ`, so
    -- that rectangle carries strictly positive coupling mass.
    have hsingleton_pos : 0 < πμ.real ({(x₀, y₀)} : Set (t × t)) := by
      exact ENNReal.toReal_pos hxy_mass (measure_ne_top _ _)
    exact lt_of_lt_of_le hsingleton_pos (MeasureTheory.measureReal_mono hxy_subset)
  have hmassGap : ((Q : Measure t).real B) < ((P : Measure t).real A) := by
    -- Proof comment: the reachable-right rectangle has no mass from unreachable left vertices,
    -- while the cross rectangle contains the positive slack atom `(x₀, y₀)`.
    rw [hPA, hQB, hPA_split, hQB_split, hAcB_zero]
    have hAB_nonneg : 0 ≤ πμ.real (A ×ˢ B : Set (t × t)) := MeasureTheory.measureReal_nonneg
    linarith
  exact False.elim <|
    cutGap_contradictsTransportPotentialMaximality
      (htfin := htfin) (P := P) (Q := Q) (u := g₀) (v := fun y ↦ -g₀ y) hg₀feas hg₀max
      hmassGap hcrossSlack

/-- Helper for Example 17.55: finite strong duality already provides an exact feasible
transport-potential pair, independently of any chosen optimal coupling. -/
private theorem existsExactTransportPotentialPair
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t) :
    ∃ u v : t → ℝ,
      (∀ x y, u x + v y ≤ dist x y) ∧
        (wassersteinDistance P Q).toReal =
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := by
  obtain ⟨u, v, hfeas, hmax⟩ :=
    existsMaximizingTransportPotentialPair (htfin := htfin) P Q
  obtain ⟨πopt, hπoptCost⟩ := optimalFiniteCoupling_cost_eq_toReal (htfin := htfin) P Q
  refine ⟨u, v, hfeas, ?_⟩
  have hupper :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) ≤
        (wassersteinDistance P Q).toReal := by
    -- Proof comment: weak duality against one cost-realizing coupling gives the easy direction
    -- of strong duality for the maximizing feasible pair.
    calc
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) ≤
          ∫ z : t × t, dist z.1 z.2
            ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
        exact transportPotentialPair_objective_le_couplingCost
          (htfin := htfin) (π := πopt) hfeas
      _ = (wassersteinDistance P Q).toReal := hπoptCost
  classical
  let a₀ : t := Classical.choice P.nonempty
  let dualSet : Set ℝ :=
    {r : ℝ | ∃ g : t → ℝ,
      g a₀ = 0 ∧
        LipschitzWith 1 g ∧
        r = ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t)}
  have hobjSup :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) = sSup dualSet := by
    -- Proof comment: the maximizing feasible pair can be read as the maximizer of the anchored
    -- finite dual set via the previously extracted envelope witness.
    simpa [dualSet] using
      maximizingTransportPotentialPair_objective_eq_sSupAnchoredDual
        (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q) hfeas hmax
  have hlower :
      (wassersteinDistance P Q).toReal ≤
        ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := by
    have hdualLower :
        (wassersteinDistance P Q).toReal ≤ sSup dualSet := by
      -- Proof comment: the extracted reverse-duality owner theorem isolates the remaining
      -- combinatorial slack-atom contradiction away from the exact-pair assembly.
      simpa [dualSet] using
        wassersteinDistanceToReal_le_sSupAnchoredDual
          (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q) πopt hπoptCost hfeas hmax
    rw [hobjSup]
    exact hdualLower
  exact le_antisymm hlower hupper

/-- Helper for Example 17.55: the strict anchored-witness theorem reduces to a single owner
exact-witness theorem for one optimal finite coupling. -/
private theorem optimalFiniteCoupling_supportTightPotentials
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t)
    (πopt : WassersteinCoupling P Q)
    (hπoptCost :
      ∫ z : t × t, dist z.1 z.2 ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        (wassersteinDistance P Q).toReal) :
    ∃ u v : t → ℝ,
      (∀ x y, u x + v y ≤ dist x y) ∧
        (∀ x y, ((πopt.1 : Measure (t × t)) {(x, y)}) ≠ 0 → u x + v y = dist x y) := by
  -- Route correction: the target is only the complementary-slackness wrapper. Once an exact
  -- feasible pair is available, the positive-mass atomwise tightness is already proved by the
  -- standalone slack lemma above.
  obtain ⟨u, v, hfeas, hobj⟩ := existsExactTransportPotentialPair (htfin := htfin) P Q
  refine ⟨u, v, hfeas, ?_⟩
  have hobjCost :
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) =
        ∫ z : t × t, dist z.1 z.2
          ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
    -- Proof comment: combine the exact dual-objective identity with the cost-realizer property of
    -- `πopt` to put the pair in the shape consumed by complementary slackness.
    linarith [hobj, hπoptCost]
  -- Proof comment: once the exact feasible pair and the exact cost identity are in place, the
  -- previously hoisted slack lemma gives tightness on every positive-mass atom of `πopt`.
  exact exactTransportPotentialPair_tight_on_positiveMass
    (htfin := htfin) (π := πopt) hfeas hobjCost

/-- Helper for Example 17.55: the strict anchored-witness theorem reduces to a single owner
exact-witness theorem for one optimal finite coupling. -/
private theorem existsExactAnchoredPotential_of_optimalFiniteCoupling
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t) :
    ∃ g : t → ℝ,
      g a₀ = 0 ∧
        LipschitzWith 1 g ∧
        (wassersteinDistance P Q).toReal =
          ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
  obtain ⟨πopt, hπoptCost⟩ := optimalFiniteCoupling_cost_eq_toReal (htfin := htfin) P Q
  obtain ⟨u, v, hfeas, htight⟩ :=
    optimalFiniteCoupling_supportTightPotentials
      (htfin := htfin) (P := P) (Q := Q) πopt hπoptCost
  have hobj :
      (wassersteinDistance P Q).toReal =
        ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := by
    -- Proof comment: support tightness upgrades the pair objective to the `πopt` transport cost,
    -- and the chosen coupling already realizes `(wassersteinDistance P Q).toReal`.
    calc
      (wassersteinDistance P Q).toReal =
          ∫ z : t × t, dist z.1 z.2
            ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
        symm
        exact hπoptCost
      _ =
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := by
        symm
        exact supportTightPair_objective_eq_couplingCost
          (htfin := htfin) (π := πopt) htight
  -- Proof comment: once the exact feasible pair is available, the existing envelope-to-anchored
  -- bridge produces the desired anchored `1`-Lipschitz exact witness.
  exact existsExactAnchoredPotential_of_transportPotentialPair
    (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q) hfeas hobj

/-- Helper for Example 17.55: once a finite anchored `1`-Lipschitz witness is known to maximize
the anchored dual problem, the remaining frontier is to identify its value with
`(wassersteinDistance P Q).toReal`. -/
private theorem existsAnchoredPotential_gt_of_lt_wassersteinDistance
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t) :
    ∀ r : ℝ, r < (wassersteinDistance P Q).toReal →
      ∃ g : t → ℝ,
        g a₀ = 0 ∧
          LipschitzWith 1 g ∧
          r < ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
  intro r hr
  obtain ⟨g, hg₀, hgLip, hgEq⟩ :=
    existsExactAnchoredPotential_of_optimalFiniteCoupling
      (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q)
  -- Proof comment: once one anchored witness realizes the exact finite Wasserstein value, the
  -- strict lower-bound version is the standard exact-witness handoff.
  exact existsAnchoredPotential_gt_of_lt_of_exactWitness
    (a₀ := a₀) (P := P) (Q := Q) ⟨g, hg₀, hgLip, hgEq⟩ r hr

/-- Helper for Example 17.55: once a finite anchored `1`-Lipschitz witness is known to maximize
the anchored dual problem, the remaining frontier is to identify its value with
`(wassersteinDistance P Q).toReal`. -/
private theorem maximizingAnchoredPotential_objective_eq_wassersteinDistance
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t) {g : t → ℝ}
    (hg₀ : g a₀ = 0) (hgLip : LipschitzWith 1 g)
    (hgmax :
      ∀ h : t → ℝ, h a₀ = 0 → LipschitzWith 1 h →
        ∫ x, h x ∂(P : Measure t) - ∫ y, h y ∂(Q : Measure t) ≤
          ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t)) :
    (wassersteinDistance P Q).toReal =
      ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) := by
  have hupper :
      ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) ≤
        (wassersteinDistance P Q).toReal :=
    anchoredPotential_objective_le_wassersteinDistance
      (htfin := htfin) (a₀ := a₀) P Q hg₀ hgLip
  have hlower :
      (wassersteinDistance P Q).toReal ≤
        ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) := by
    refine le_of_forall_lt ?_
    intro r hr
    obtain ⟨h, hh₀, hhLip, hlt⟩ :=
      existsAnchoredPotential_gt_of_lt_wassersteinDistance
        (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q) r hr
    -- Proof comment: every strict lower bound is exceeded by an anchored feasible witness, and
    -- maximality of `g` forces that witness objective below the objective of `g`.
    exact lt_of_lt_of_le hlt (hgmax h hh₀ hhLip)
  -- Proof comment: weak duality gives the upper bound, and the strict-witness owner theorem
  -- upgrades maximality to the reverse inequality.
  exact le_antisymm hlower hupper

/-- Helper for Example 17.55: the remaining finite strong-duality frontier is to show that a
maximizing feasible pair actually reaches `(wassersteinDistance P Q).toReal`. -/
private theorem maximizingTransportPotentialPair_objective_eq_wassersteinDistance
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t) {u v : t → ℝ}
    (hfeas : ∀ x y, u x + v y ≤ dist x y)
    (hmax :
      ∀ u' v' : t → ℝ, (∀ x y, u' x + v' y ≤ dist x y) →
        ∫ x, u' x ∂(P : Measure t) + ∫ y, v' y ∂(Q : Measure t) ≤
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t)) :
    (wassersteinDistance P Q).toReal =
      ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := by
  classical
  let a₀ : t := Classical.choice P.nonempty
  obtain ⟨g, hg₀, hgLip, hobjEq, hgmax⟩ :=
    maximizingTransportPotentialPair_inducesAnchoredPotential
      (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q) hfeas hmax
  have hgmax' :
      ∀ h : t → ℝ, h a₀ = 0 → LipschitzWith 1 h →
        ∫ x, h x ∂(P : Measure t) - ∫ y, h y ∂(Q : Measure t) ≤
          ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) := by
    intro h hh₀ hhLip
    rw [← hobjEq]
    exact hgmax h hh₀ hhLip
  have hgEq :
      (wassersteinDistance P Q).toReal =
        ∫ x, g x ∂(P : Measure t) - ∫ y, g y ∂(Q : Measure t) :=
    maximizingAnchoredPotential_objective_eq_wassersteinDistance
      (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q) hg₀ hgLip hgmax'
  -- Proof comment: after reducing the pair maximizer to an anchored dual maximizer, the target
  -- equality is exactly the remaining anchored strong-duality statement.
  rw [hobjEq]
  exact hgEq

/-- Helper for Example 17.55: an exact finite transport-potential pair should realize
`(wassersteinDistance P Q).toReal`. -/
private theorem existsExactTransportPotentialPair_of_costRealizer
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t) :
    ∃ u v : t → ℝ,
      (∀ x y, u x + v y ≤ dist x y) ∧
        (wassersteinDistance P Q).toReal =
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := by
  -- Proof comment: this theorem is now only the legacy wrapper around the earlier exact
  -- finite-duality owner, so downstream callers keep the same API without recreating the cycle.
  exact existsExactTransportPotentialPair (htfin := htfin) P Q

/-- Helper for Example 17.55: once an optimal finite coupling carries a support-tight feasible
pair, that pair already realizes `(wassersteinDistance P Q).toReal`. -/
private theorem existsExactTransportPotentialPair_of_costOptimalCoupling
    {t : Set E} (htfin : t.Finite) {P Q : ProbabilityMeasure t}
    (πopt : WassersteinCoupling P Q)
    (hπoptCost :
      ∫ z : t × t, dist z.1 z.2 ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) =
        (wassersteinDistance P Q).toReal) :
    ∃ u v : t → ℝ,
      (∀ x y, u x + v y ≤ dist x y) ∧
        (wassersteinDistance P Q).toReal =
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := by
  -- Proof comment: once exact finite duality is proved independently of the coupling, the
  -- cost-realizer wrapper no longer needs to reconstruct exactness from support tightness.
  exact existsExactTransportPotentialPair (htfin := htfin) P Q

/-- Helper for Example 17.55: on a finite subtype, an optimal coupling should induce an exact
finite transport-potential pair realizing `(wassersteinDistance P Q).toReal`. -/
private theorem existsExactTransportPotentialPair_of_optimalFiniteCoupling
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t) :
    ∃ u v : t → ℝ,
      (∀ x y, u x + v y ≤ dist x y) ∧
        (wassersteinDistance P Q).toReal =
          ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := by
  obtain ⟨πopt, hπoptCost⟩ := optimalFiniteCoupling_cost_eq_toReal (htfin := htfin) P Q
  -- Proof comment: the public optimal-coupling wrapper now factors through support tightness of
  -- the chosen cost-realizing coupling, instead of reopening the transport-maximizer wrapper.
  exact existsExactTransportPotentialPair_of_costOptimalCoupling
    (htfin := htfin) (P := P) (Q := Q) πopt hπoptCost

/-- Helper for Example 17.55: a strict finite transport-potential pair yields an anchored
`1`-Lipschitz witness with the same strict gap. -/
private theorem existsAnchoredPotential_gt_of_transportPotentialPair
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t)
    {r : ℝ} {u v : t → ℝ}
    (hfeas : ∀ x y, u x + v y ≤ dist x y)
    (hgap :
      r < ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t)) :
    ∃ g : t → ℝ,
      g a₀ = 0 ∧
        LipschitzWith 1 g ∧
        r < ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
  classical
  letI : Fintype t := htfin.fintype
  have hPIntU : Integrable u (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hQIntV : Integrable v (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hfeasOne : ∀ x y, u x + v y ≤ (1 : ℝ) * dist x y := by
    intro x y
    simpa using hfeas x y
  obtain ⟨g, hgLip, hu_le, hv_le⟩ :=
    existsLipschitzPotential_of_transportInequalities
      (htfin := htfin) (α := 1) (hα := zero_le_one) hfeasOne
  have hgLipOne : LipschitzWith 1 g := by
    -- Proof comment: the finite transport-envelope helper already returns a `1`-Lipschitz
    -- potential once `α = 1`.
    simpa using hgLip
  have hPIntG : Integrable g (P : Measure t) := MeasureTheory.Integrable.of_finite
  have hQIntG : Integrable g (Q : Measure t) := MeasureTheory.Integrable.of_finite
  have hPmono :
      ∫ x, u x ∂(P : Measure t) ≤ ∫ x, g x ∂(P : Measure t) := by
    -- Proof comment: the envelope dominates the first transport potential pointwise, so the same
    -- order holds after integrating against `P`.
    refine MeasureTheory.integral_mono hPIntU hPIntG ?_
    intro x
    exact hu_le x
  have hQmono :
      ∫ y, v y ∂(Q : Measure t) ≤ ∫ y, -g y ∂(Q : Measure t) := by
    -- Proof comment: the envelope also bounds the second potential from above by `-g`.
    refine MeasureTheory.integral_mono hQIntV hQIntG.neg ?_
    intro y
    exact hv_le y
  have hQneg :
      ∫ y, -g y ∂(Q : Measure t) = -∫ y, g y ∂(Q : Measure t) := by
    -- Proof comment: rewrite the integrated upper bound into the signed dual difference.
    simpa using MeasureTheory.integral_neg (f := g) (μ := (Q : Measure t))
  have hgapG :
      r < ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
    -- Proof comment: combining the two monotonicity inequalities upgrades the strict pair gap to
    -- the single-potential dual gap.
    linarith
  obtain ⟨g₀, hg₀, hg₀Lip, hg₀Eq⟩ :=
    anchorShift_integralDifference_eq (htfin := htfin) a₀ P Q hgLipOne
  refine ⟨g₀, hg₀, hg₀Lip, ?_⟩
  -- Proof comment: subtracting the anchor value preserves the integral difference, so the
  -- anchored translate inherits the same strict inequality.
  rwa [hg₀Eq]

/-- Helper for Example 17.55: every feasible finite transport-potential pair is bounded above by
the finite Wasserstein value. -/
private theorem transportPotentialPair_objective_le_wassersteinDistance
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t)
    {u v : t → ℝ} (hfeas : ∀ x y, u x + v y ≤ dist x y) :
    ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) ≤
      (wassersteinDistance P Q).toReal := by
  obtain ⟨πopt, hπoptCost⟩ := optimalFiniteCoupling_cost_eq_toReal (htfin := htfin) P Q
  -- Proof comment: evaluate weak duality on one coupling that already realizes the finite
  -- Wasserstein cost.
  calc
    ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) ≤
        ∫ z : t × t, dist z.1 z.2
          ∂((πopt.1 : ProbabilityMeasure (t × t)) : Measure (t × t)) := by
      exact transportPotentialPair_objective_le_couplingCost
        (htfin := htfin) (π := πopt) hfeas
    _ = (wassersteinDistance P Q).toReal := hπoptCost

/-- Helper for Example 17.55: on a finite subtype, every strict lower real bound below
`wassersteinDistance P Q` admits a feasible finite transport-potential pair beating that bound. -/
private theorem existsFiniteTransportPotentialPair_gt_of_lt_wassersteinDistance
    {t : Set E} (htfin : t.Finite) (P Q : ProbabilityMeasure t) :
    ∀ r : ℝ, r < (wassersteinDistance P Q).toReal →
      ∃ u v : t → ℝ,
        (∀ x y, u x + v y ≤ dist x y) ∧
          r < ∫ x, u x ∂(P : Measure t) + ∫ y, v y ∂(Q : Measure t) := by
  intro r hr
  obtain ⟨u, v, hfeas, huvEq⟩ :=
    existsExactTransportPotentialPair_of_optimalFiniteCoupling
      (htfin := htfin) (P := P) (Q := Q)
  refine ⟨u, v, hfeas, ?_⟩
  -- Proof comment: the exact finite pair already realizes the Wasserstein value, so it beats
  -- every strict lower bound below that value.
  rw [← huvEq]
  exact hr

private theorem finiteSubtype_wassersteinDistance_le_dual
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t) :
    wassersteinDistance P Q ≤
      ENNReal.ofReal
        (sSup {r : ℝ | ∃ g : t → ℝ,
          g a₀ = 0 ∧
            LipschitzWith 1 g ∧
            r = ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t)}) := by
  classical
  letI : Fintype t := htfin.fintype
  let dualSet : Set ℝ :=
    {r : ℝ | ∃ g : t → ℝ,
      g a₀ = 0 ∧
        LipschitzWith 1 g ∧
        r = ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t)}
  have hdual_nonempty : dualSet.Nonempty := by
    exact ⟨0, zeroAnchoredPotential_mem_finiteDualSet a₀ P Q⟩
  have hdual_bdd : BddAbove dualSet := by
    refine ⟨(∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
      ∂((P.prod Q : ProbabilityMeasure (t × t)) : Measure (t × t))).toReal, ?_⟩
    intro r hr
    rcases hr with ⟨g, hg₀, hgLip, rfl⟩
    -- Proof comment: weak duality against the product coupling gives a concrete uniform upper
    -- bound for every anchored finite witness.
    exact lipschitzIntegralDifference_le_couplingCost
      (x₀ := a₀) (P := P) (Q := Q) (π := P.prod Q) (isCoupling_prod P Q) hg₀ hgLip
      MeasureTheory.Integrable.of_finite MeasureTheory.Integrable.of_finite
  have hdual_nonneg : 0 ≤ sSup dualSet := by
    -- Proof comment: the anchored zero witness shows that the finite dual supremum is at least
    -- `0`, so comparing `ENNReal.ofReal` values reduces to comparing real numbers.
    exact le_csSup hdual_bdd (zeroAnchoredPotential_mem_finiteDualSet a₀ P Q)
  have hW_ne_top : wassersteinDistance P Q ≠ ∞ := by
    exact (ne_of_lt (finiteSubtype_wassersteinDistance_lt_top htfin P Q))
  have hleSup :
      (wassersteinDistance P Q).toReal ≤ sSup dualSet := by
    refine le_of_forall_lt ?_
    intro r hr
    obtain ⟨g, hg₀, hgLip, hgap⟩ :=
      existsAnchoredPotential_gt_of_lt_wassersteinDistance
        (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q) r hr
    have hmem :
        ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) ∈ dualSet := by
      exact ⟨g, hg₀, hgLip, rfl⟩
    -- Proof comment: every strict lower real bound is exceeded by some dual-set element, so the
    -- dual supremum dominates the finite Wasserstein value.
    exact lt_csSup_of_lt hdual_bdd hmem hgap
  -- Proof comment: the finite Wasserstein value is finite, so the real comparison upgrades back
  -- to the desired `ENNReal` inequality.
  exact (ENNReal.le_ofReal_iff_toReal_le hW_ne_top hdual_nonneg).2 hleSup

/-- Helper for Example 17.55: on a finite subtype, the anchored finite dual problem admits an
exact maximizer realizing `(wassersteinDistance P Q).toReal`. -/
private theorem existsExactAnchoredPotential_eq_wassersteinDistance
    {t : Set E} (htfin : t.Finite) (a₀ : t) (P Q : ProbabilityMeasure t) :
    ∃ g : t → ℝ,
      g a₀ = 0 ∧
        LipschitzWith 1 g ∧
        (wassersteinDistance P Q).toReal =
          ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
  letI : Finite t := htfin.to_subtype
  -- Route correction: after isolating the strict reverse inequality at the dual-supremum level,
  -- the exact theorem only has to compare the compactness maximizer against that supremum.
  obtain ⟨g, hg₀, hgLip, hgmax⟩ :=
    existsMaximizingAnchoredPotential (htfin := htfin) (a₀ := a₀) P Q
  let dualSet : Set ℝ :=
    {r : ℝ | ∃ h : t → ℝ,
      h a₀ = 0 ∧
        LipschitzWith 1 h ∧
        r = ∫ x, h x ∂(P : Measure t) - ∫ x, h x ∂(Q : Measure t)}
  have hdual_nonempty : dualSet.Nonempty := by
    exact ⟨0, zeroAnchoredPotential_mem_finiteDualSet a₀ P Q⟩
  have hdual_nonneg : 0 ≤ sSup dualSet := by
    exact le_csSup
      (by
        refine ⟨(∫⁻ z : t × t, ENNReal.ofReal (dist z.1 z.2)
          ∂((P.prod Q : ProbabilityMeasure (t × t)) : Measure (t × t))).toReal, ?_⟩
        intro r hr
        rcases hr with ⟨h, hh₀, hhLip, rfl⟩
        exact lipschitzIntegralDifference_le_couplingCost
          (x₀ := a₀) (P := P) (Q := Q) (π := P.prod Q) (isCoupling_prod P Q) hh₀ hhLip
          MeasureTheory.Integrable.of_finite MeasureTheory.Integrable.of_finite)
      (zeroAnchoredPotential_mem_finiteDualSet a₀ P Q)
  have hW_ne_top : wassersteinDistance P Q ≠ ∞ := by
    exact (ne_of_lt (finiteSubtype_wassersteinDistance_lt_top htfin P Q))
  have hupper :
      ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) ≤
        (wassersteinDistance P Q).toReal :=
    anchoredPotential_objective_le_wassersteinDistance
      (htfin := htfin) (a₀ := a₀) P Q hg₀ hgLip
  have hsSup_le :
      sSup dualSet ≤
        ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
    refine csSup_le hdual_nonempty ?_
    intro r hr
    rcases hr with ⟨h, hh₀, hhLip, rfl⟩
    -- Proof comment: the compactness maximizer dominates every anchored feasible witness, so it
    -- also dominates the whole dual supremum.
    exact hgmax h hh₀ hhLip
  have hlower :
      (wassersteinDistance P Q).toReal ≤
        ∫ x, g x ∂(P : Measure t) - ∫ x, g x ∂(Q : Measure t) := by
    have hW_le_dual :
        wassersteinDistance P Q ≤ ENNReal.ofReal (sSup dualSet) := by
      simpa [dualSet] using
        finiteSubtype_wassersteinDistance_le_dual
          (htfin := htfin) (a₀ := a₀) (P := P) (Q := Q)
    have hW_le_sSup :
        (wassersteinDistance P Q).toReal ≤ sSup dualSet :=
      (ENNReal.le_ofReal_iff_toReal_le hW_ne_top hdual_nonneg).1 hW_le_dual
    -- Proof comment: the standalone dual-sup lower bound and the maximality of `g` now combine
    -- to give the exact reverse inequality for the compactness-selected witness.
    exact le_trans hW_le_sSup hsSup_le
  refine ⟨g, hg₀, hgLip, ?_⟩
  exact le_antisymm hlower hupper

/-- Helper for Example 17.55: a finite-subtype dual witness transports back to the ambient space
with only the mean quantization error loss. -/
private theorem mapRepresentativeDual_le_dual_addError
    (x₀ : E) {P Q : ProbabilityMeasure E} {t : Set E} (htfin : t.Finite) (hx₀t : x₀ ∈ t)
    {ρ : E → t} (hρmeas : Measurable ρ) (hρx₀ : ρ x₀ = ⟨x₀, hx₀t⟩)
    (hP : Integrable (fun x ↦ dist x x₀) (P : Measure E))
    (hQ : Integrable (fun x ↦ dist x x₀) (Q : Measure E)) :
    ENNReal.ofReal
        (sSup {r : ℝ | ∃ g : t → ℝ,
          g ⟨x₀, hx₀t⟩ = 0 ∧
            LipschitzWith 1 g ∧
            r = ∫ x, g x ∂((representativeMapLaw P hρmeas : ProbabilityMeasure t) : Measure t) -
              ∫ x, g x ∂((representativeMapLaw Q hρmeas : ProbabilityMeasure t) : Measure t)}) ≤
      ENNReal.ofReal
          (sSup {r : ℝ | ∃ f : E → ℝ,
            f x₀ = 0 ∧
              LipschitzWith 1 f ∧
              r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)}) +
        ENNReal.ofReal
          (∫ x, dist x (ρ x).1 ∂(P : Measure E) +
            ∫ x, dist x (ρ x).1 ∂(Q : Measure E)) := by
  classical
  letI : Fintype t := htfin.fintype
  let finiteDualSet : Set ℝ :=
    {r : ℝ | ∃ g : t → ℝ,
      g ⟨x₀, hx₀t⟩ = 0 ∧
        LipschitzWith 1 g ∧
        r = ∫ x, g x ∂((representativeMapLaw P hρmeas : ProbabilityMeasure t) : Measure t) -
          ∫ x, g x ∂((representativeMapLaw Q hρmeas : ProbabilityMeasure t) : Measure t)}
  let ambientDualSet : Set ℝ :=
    {r : ℝ | ∃ f : E → ℝ,
      f x₀ = 0 ∧
        LipschitzWith 1 f ∧
        r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)}
  let errReal : ℝ :=
    ∫ x, dist x (ρ x).1 ∂(P : Measure E) +
      ∫ x, dist x (ρ x).1 ∂(Q : Measure E)
  have hfinite_nonempty : finiteDualSet.Nonempty := by
    refine ⟨0, ?_⟩
    exact zeroAnchoredPotential_mem_finiteDualSet ⟨x₀, hx₀t⟩
      (representativeMapLaw P hρmeas) (representativeMapLaw Q hρmeas)
  have hfinite_bdd : BddAbove finiteDualSet := by
    refine ⟨(∫⁻ z : t × t, ENNReal.ofReal (dist z.1.1 z.2.1)
      ∂(((representativeMapLaw P hρmeas : ProbabilityMeasure t).prod
        (representativeMapLaw Q hρmeas : ProbabilityMeasure t) :
          ProbabilityMeasure (t × t)) : Measure (t × t))).toReal, ?_⟩
    intro r hr
    rcases hr with ⟨g, hg₀, hgLip, rfl⟩
    -- Proof comment: weak duality on the finite representative space bounds every finite witness
    -- by the cost of the product coupling of the representative laws.
    exact lipschitzIntegralDifference_le_couplingCost
      (x₀ := ⟨x₀, hx₀t⟩)
      (P := representativeMapLaw P hρmeas)
      (Q := representativeMapLaw Q hρmeas)
      (π := (representativeMapLaw P hρmeas).prod (representativeMapLaw Q hρmeas))
      (isCoupling_prod _ _) hg₀ hgLip
      MeasureTheory.Integrable.of_finite MeasureTheory.Integrable.of_finite
  have hambient_nonempty : ambientDualSet.Nonempty := by
    refine ⟨0, ?_⟩
    exact ⟨fun _ ↦ 0, by simp, LipschitzWith.const' (K := 1) 0, by simp⟩
  have hambient_bdd : BddAbove ambientDualSet := by
    refine ⟨(∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2)
      ∂((P.prod Q : ProbabilityMeasure (E × E)) : Measure (E × E))).toReal, ?_⟩
    intro r hr
    rcases hr with ⟨f, hf₀, hfLip, rfl⟩
    -- Proof comment: the ambient product coupling gives the same weak-duality upper bound for
    -- every anchored ambient witness.
    exact lipschitzIntegralDifference_le_couplingCost
      (x₀ := x₀) (P := P) (Q := Q) (π := P.prod Q) (isCoupling_prod P Q)
      hf₀ hfLip hP hQ
  have hambient_nonneg : 0 ≤ sSup ambientDualSet := by
    exact le_csSup hambient_bdd (by
      exact ⟨fun _ ↦ 0, by simp, LipschitzWith.const' (K := 1) 0, by simp⟩)
  have hErrNonneg : 0 ≤ errReal := by
    dsimp [errReal]
    have hPnonneg : 0 ≤ ∫ x, dist x (ρ x).1 ∂(P : Measure E) := by
      exact MeasureTheory.integral_nonneg fun _ ↦ dist_nonneg
    have hQnonneg : 0 ≤ ∫ x, dist x (ρ x).1 ∂(Q : Measure E) := by
      exact MeasureTheory.integral_nonneg fun _ ↦ dist_nonneg
    linarith
  have hupper :
      ∀ r ∈ finiteDualSet, r ≤ sSup ambientDualSet + errReal := by
    intro r hr
    rcases hr with ⟨g, hg₀, hgLip, rfl⟩
    let gOnE : E → ℝ := fun x ↦ if hx : x ∈ t then g ⟨x, hx⟩ else 0
    have hgOnELip : LipschitzOnWith 1 gOnE t := by
      intro x hx y hy
      -- Proof comment: on the representative subset, the auxiliary total-space spelling of `g`
      -- agrees with the original finite witness, so the same Lipschitz bound applies.
      simpa [gOnE, hx, hy] using hgLip ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨f, hfLip, hfEq⟩ := hgOnELip.extend_real
    have hEqAtRepresentative : ∀ x, f (ρ x).1 = g (ρ x) := by
      intro x
      calc
        f (ρ x).1 = gOnE (ρ x).1 := (hfEq (ρ x).2).symm
        _ = g (ρ x) := by simp [gOnE, (ρ x).2]
    have hf₀ : f x₀ = 0 := by
      -- Proof comment: the extension still agrees with the finite witness at the distinguished
      -- representative of the anchor.
      calc
        f x₀ = g (ρ x₀) := by simpa [hρx₀] using hEqAtRepresentative x₀
        _ = g ⟨x₀, hx₀t⟩ := by rw [hρx₀]
        _ = 0 := hg₀
    have hfIntP : Integrable f (P : Measure E) :=
      anchoredLipschitz_integrable_of_integrableDist x₀ P hf₀ hfLip hP
    have hfIntQ : Integrable f (Q : Measure E) :=
      anchoredLipschitz_integrable_of_integrableDist x₀ Q hf₀ hfLip hQ
    have hgIntPρ :
        Integrable g ((representativeMapLaw P hρmeas : ProbabilityMeasure t) : Measure t) :=
      MeasureTheory.Integrable.of_finite
    have hgIntQρ :
        Integrable g ((representativeMapLaw Q hρmeas : ProbabilityMeasure t) : Measure t) :=
      MeasureTheory.Integrable.of_finite
    have hgRhoIntP : Integrable (fun x ↦ g (ρ x)) (P : Measure E) :=
      hgIntPρ.comp_measurable hρmeas
    have hgRhoIntQ : Integrable (fun x ↦ g (ρ x)) (Q : Measure E) :=
      hgIntQρ.comp_measurable hρmeas
    have hErrIntP :
        Integrable (fun x ↦ dist x (ρ x).1) (P : Measure E) :=
      integrable_dist_mapRepresentative_of_integrableDist
        (x₀ := x₀) (μ := P) (htfin := htfin) (ρ := ρ) hρmeas hP
    have hErrIntQ :
        Integrable (fun x ↦ dist x (ρ x).1) (Q : Measure E) :=
      integrable_dist_mapRepresentative_of_integrableDist
        (x₀ := x₀) (μ := Q) (htfin := htfin) (ρ := ρ) hρmeas hQ
    have hRepP :
        ∫ x, g x ∂((representativeMapLaw P hρmeas : ProbabilityMeasure t) : Measure t) =
          ∫ x, g (ρ x) ∂(P : Measure E) := by
      -- Proof comment: representative expectations are just ambient expectations of the pulled-back
      -- finite witness along the measurable representative map.
      simpa [representativeMapLaw] using
        (MeasureTheory.integral_map (μ := (P : Measure E)) hρmeas.aemeasurable
          hgIntPρ.aestronglyMeasurable)
    have hRepQ :
        ∫ x, g x ∂((representativeMapLaw Q hρmeas : ProbabilityMeasure t) : Measure t) =
          ∫ x, g (ρ x) ∂(Q : Measure E) := by
      -- Proof comment: the same pushforward identity rewrites the representative expectation
      -- under `Q`.
      simpa [representativeMapLaw] using
        (MeasureTheory.integral_map (μ := (Q : Measure E)) hρmeas.aemeasurable
          hgIntQρ.aestronglyMeasurable)
    have hPointwise :
        ∀ x, ‖f x - g (ρ x)‖ ≤ dist x (ρ x).1 := by
      intro x
      -- Proof comment: the extension is globally `1`-Lipschitz and agrees with the finite witness
      -- at each representative point.
      simpa [Real.dist_eq, hEqAtRepresentative x] using hfLip.dist_le_mul x (ρ x).1
    have hPcompare :
        ∫ x, g (ρ x) ∂(P : Measure E) ≤
          ∫ x, f x ∂(P : Measure E) + ∫ x, dist x (ρ x).1 ∂(P : Measure E) := by
      have hmono :
          ∫ x, g (ρ x) ∂(P : Measure E) ≤
            ∫ x, (f x + dist x (ρ x).1) ∂(P : Measure E) := by
        refine MeasureTheory.integral_mono hgRhoIntP (hfIntP.add hErrIntP) ?_
        intro x
        have hx := hPointwise x
        have hx' := abs_le.mp (by simpa [Real.norm_eq_abs] using hx)
        linarith
      simpa [MeasureTheory.integral_add hfIntP hErrIntP] using hmono
    have hQcompare :
        ∫ x, f x ∂(Q : Measure E) ≤
          ∫ x, g (ρ x) ∂(Q : Measure E) + ∫ x, dist x (ρ x).1 ∂(Q : Measure E) := by
      have hmono :
          ∫ x, f x ∂(Q : Measure E) ≤
            ∫ x, (g (ρ x) + dist x (ρ x).1) ∂(Q : Measure E) := by
        refine MeasureTheory.integral_mono hfIntQ (hgRhoIntQ.add hErrIntQ) ?_
        intro x
        have hx := hPointwise x
        have hx' := abs_le.mp (by simpa [Real.norm_eq_abs] using hx)
        linarith
      simpa [MeasureTheory.integral_add hgRhoIntQ hErrIntQ] using hmono
    have hambient_mem :
        ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E) ∈ ambientDualSet := by
      exact ⟨f, hf₀, hfLip, rfl⟩
    have hambient_le :
        ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E) ≤ sSup ambientDualSet := by
      exact le_csSup hambient_bdd hambient_mem
    -- Proof comment: after rewriting the representative expectations through `ρ`, the two
    -- pointwise extension bounds control the loss by the mean quantization error.
    rw [hRepP, hRepQ]
    linarith
  have hmain :
      sSup finiteDualSet ≤ sSup ambientDualSet + errReal := by
    exact csSup_le hfinite_nonempty hupper
  calc
    ENNReal.ofReal (sSup finiteDualSet) ≤ ENNReal.ofReal (sSup ambientDualSet + errReal) := by
      exact ENNReal.ofReal_le_ofReal hmain
    _ = ENNReal.ofReal (sSup ambientDualSet) + ENNReal.ofReal errReal := by
      rw [ENNReal.ofReal_add hambient_nonneg hErrNonneg]
    _ =
        ENNReal.ofReal
          (sSup {r : ℝ | ∃ f : E → ℝ,
            f x₀ = 0 ∧
              LipschitzWith 1 f ∧
              r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)}) +
          ENNReal.ofReal
            (∫ x, dist x (ρ x).1 ∂(P : Measure E) +
              ∫ x, dist x (ρ x).1 ∂(Q : Measure E)) := by
      simp [ambientDualSet, errReal]

-- Proof sketch: this is the Kantorovich--Rubinstein duality theorem; identify the primal
-- coupling infimum with the supremum of the signed integral difference over anchored
-- real-valued `1`-Lipschitz test functions, assuming finite first moment at the anchor.
/-- Helper for Example 17.55: the descriptive-name Kantorovich--Rubinstein duality theorem used
downstream in this file. -/
-- TODO: Reuse an owner Kantorovich--Rubinstein duality theorem if available; otherwise prove the
-- anchored dual formula by reducing the primal coupling infimum to the standard Polish-space KR
-- theorem with the finite-first-moment hypotheses `hP` and `hQ`.
theorem wassersteinDistance_eq_sSup_lipschitz_of_integrableDist
    (x₀ : E) (P Q : ProbabilityMeasure E)
    (hP : Integrable (fun x ↦ dist x x₀) (P : Measure E))
    (hQ : Integrable (fun x ↦ dist x x₀) (Q : Measure E)) :
    wassersteinDistance P Q =
      ENNReal.ofReal
        (sSup {r : ℝ | ∃ f : E → ℝ,
          f x₀ = 0 ∧
            LipschitzWith 1 f ∧
            r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)}) := by
  let dualSet : Set ℝ :=
    {r : ℝ | ∃ f : E → ℝ,
      f x₀ = 0 ∧
        LipschitzWith 1 f ∧
        r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)}
  have hzero_mem : 0 ∈ dualSet := by
    exact ⟨fun _ ↦ 0, by simp, LipschitzWith.const' (K := 1) 0, by simp⟩
  have hdual_nonempty : dualSet.Nonempty := ⟨0, hzero_mem⟩
  have hdual_bdd : BddAbove dualSet := by
    refine ⟨(∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2)
      ∂((P.prod Q : ProbabilityMeasure (E × E)) : Measure (E × E))).toReal, ?_⟩
    intro r hr
    rcases hr with ⟨f, hf₀, hfLip, rfl⟩
    -- Proof comment: weak duality against the ambient product coupling gives a uniform upper
    -- bound for every anchored ambient witness.
    exact lipschitzIntegralDifference_le_couplingCost
      (x₀ := x₀) (P := P) (Q := Q) (π := P.prod Q) (isCoupling_prod P Q)
      hf₀ hfLip hP hQ
  have hdual_nonneg : 0 ≤ sSup dualSet := by
    exact le_csSup hdual_bdd hzero_mem
  have hprodCost_lt :
      ∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2)
          ∂((P.prod Q : ProbabilityMeasure (E × E)) : Measure (E × E)) < ∞ := by
    -- Proof comment: the product coupling has finite cost because the two first-moment
    -- hypotheses control `dist z.1 z.2` by the triangle inequality.
    exact
      (couplingDist_integrable_of_integrableDist
        (x₀ := x₀) (P := P) (Q := Q) (π := P.prod Q)
        (isCoupling_prod P Q) hP hQ).lintegral_lt_top
  have hW_ne_top : wassersteinDistance P Q ≠ ∞ := by
    exact ne_of_lt <| lt_of_le_of_lt
      (by
        rw [wassersteinDistance]
        exact sInf_le ⟨⟨P.prod Q, isCoupling_prod P Q⟩, rfl⟩)
      hprodCost_lt
  have hdual_le : ENNReal.ofReal (sSup dualSet) ≤ wassersteinDistance P Q := by
    have hsSup_le :
        sSup dualSet ≤ (wassersteinDistance P Q).toReal := by
      refine csSup_le hdual_nonempty ?_
      intro r hr
      rcases hr with ⟨f, hf₀, hfLip, rfl⟩
      have hcost_le :
          ENNReal.ofReal
              (∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)) ≤
            wassersteinDistance P Q := by
        rw [wassersteinDistance]
        refine le_sInf ?_
        rintro _ ⟨π, rfl⟩
        have hπcost_lt :
            ∫⁻ z : E × E, ENNReal.ofReal (dist z.1 z.2)
                ∂(((π.1 : ProbabilityMeasure (E × E))) : Measure (E × E)) < ∞ := by
          exact
            (couplingDist_integrable_of_integrableDist
              (x₀ := x₀) (P := P) (Q := Q) (π := π.1) π.2 hP hQ).lintegral_lt_top
        exact
          (ENNReal.ofReal_le_iff_le_toReal (ne_of_lt hπcost_lt)).2
            (lipschitzIntegralDifference_le_couplingCost
              (x₀ := x₀) (P := P) (Q := Q) (π := π.1) π.2 hf₀ hfLip hP hQ)
      exact (ENNReal.ofReal_le_iff_le_toReal hW_ne_top).1 hcost_le
    exact (ENNReal.ofReal_le_iff_le_toReal hW_ne_top).2 hsSup_le
  by_cases hle : wassersteinDistance P Q ≤ ENNReal.ofReal (sSup dualSet)
  · exact le_antisymm hle hdual_le
  · have hsSup_lt :
        sSup dualSet < (wassersteinDistance P Q).toReal := by
      exact lt_of_not_ge fun hsSup_ge ↦
        hle ((ENNReal.le_ofReal_iff_toReal_le hW_ne_top hdual_nonneg).2 hsSup_ge)
    let ε : ℝ := ((wassersteinDistance P Q).toReal - sSup dualSet) / 4
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    obtain ⟨t, htfin, hx₀t, ρ, hρmeas, hρx₀, hErrP, hErrQ⟩ :=
      existsFiniteRangeRepresentativeWithSmallMeanError x₀ P Q hP hQ hε
    let Pρ : ProbabilityMeasure t := representativeMapLaw P hρmeas
    let Qρ : ProbabilityMeasure t := representativeMapLaw Q hρmeas
    let errReal : ℝ :=
      ∫ x, dist x (ρ x).1 ∂(P : Measure E) +
        ∫ x, dist x (ρ x).1 ∂(Q : Measure E)
    let finiteDualSet : Set ℝ :=
      {r : ℝ | ∃ g : t → ℝ,
        g ⟨x₀, hx₀t⟩ = 0 ∧
          LipschitzWith 1 g ∧
          r = ∫ x, g x ∂((Pρ : ProbabilityMeasure t) : Measure t) -
            ∫ x, g x ∂((Qρ : ProbabilityMeasure t) : Measure t)}
    have hErrNonneg : 0 ≤ errReal := by
      dsimp [errReal]
      have hPnonneg : 0 ≤ ∫ x, dist x (ρ x).1 ∂(P : Measure E) := by
        exact MeasureTheory.integral_nonneg fun _ ↦ dist_nonneg
      have hQnonneg : 0 ≤ ∫ x, dist x (ρ x).1 ∂(Q : Measure E) := by
        exact MeasureTheory.integral_nonneg fun _ ↦ dist_nonneg
      linarith
    have hquantized :
        wassersteinDistance P Q ≤ ENNReal.ofReal (sSup dualSet + errReal + errReal) := by
      have hstep₁ :
          wassersteinDistance P Q ≤ wassersteinDistance Pρ Qρ + ENNReal.ofReal errReal := by
        simpa [Pρ, Qρ, errReal] using
          wassersteinDistance_le_mapRepresentative_addError
            (x₀ := x₀) (P := P) (Q := Q) (htfin := htfin)
            (ρ := ρ) hρmeas hP hQ
      have hstep₂ :
          wassersteinDistance Pρ Qρ ≤ ENNReal.ofReal (sSup finiteDualSet) := by
        simpa [Pρ, Qρ, finiteDualSet] using
          finiteSubtype_wassersteinDistance_le_dual
            (htfin := htfin) (a₀ := ⟨x₀, hx₀t⟩) (P := Pρ) (Q := Qρ)
      have hstep₃ :
          ENNReal.ofReal (sSup finiteDualSet) ≤
            ENNReal.ofReal (sSup dualSet) + ENNReal.ofReal errReal := by
        simpa [Pρ, Qρ, finiteDualSet, dualSet, errReal] using
          mapRepresentativeDual_le_dual_addError
            (x₀ := x₀) (P := P) (Q := Q) (htfin := htfin) (hx₀t := hx₀t)
            (ρ := ρ) hρmeas hρx₀ hP hQ
      calc
        wassersteinDistance P Q ≤ wassersteinDistance Pρ Qρ + ENNReal.ofReal errReal := hstep₁
        _ ≤ ENNReal.ofReal (sSup finiteDualSet) + ENNReal.ofReal errReal := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hstep₂ (ENNReal.ofReal errReal)
        _ ≤ (ENNReal.ofReal (sSup dualSet) + ENNReal.ofReal errReal) +
              ENNReal.ofReal errReal := by
          simpa [add_comm, add_left_comm, add_assoc] using
            add_le_add_left hstep₃ (ENNReal.ofReal errReal)
        _ = ENNReal.ofReal (sSup dualSet + errReal + errReal) := by
          calc
            (ENNReal.ofReal (sSup dualSet) + ENNReal.ofReal errReal) +
                ENNReal.ofReal errReal =
                ENNReal.ofReal (sSup dualSet + errReal) + ENNReal.ofReal errReal := by
              rw [← ENNReal.ofReal_add hdual_nonneg hErrNonneg]
            _ = ENNReal.ofReal ((sSup dualSet + errReal) + errReal) := by
              rw [← ENNReal.ofReal_add (add_nonneg hdual_nonneg hErrNonneg) hErrNonneg]
            _ = ENNReal.ofReal (sSup dualSet + errReal + errReal) := by
              ring
    have hquantized_real :
        (wassersteinDistance P Q).toReal ≤ sSup dualSet + errReal + errReal := by
      exact
        (ENNReal.le_ofReal_iff_toReal_le hW_ne_top
          (by nlinarith [hdual_nonneg, hErrNonneg])).1 hquantized
    have hstrict :
        sSup dualSet + errReal + errReal < (wassersteinDistance P Q).toReal := by
      -- Proof comment: choosing the representative map with error below one quarter of the duality
      -- gap leaves enough room to contradict the negated target inequality after two error terms.
      have hgap : 0 < (wassersteinDistance P Q).toReal - sSup dualSet := sub_pos.mpr hsSup_lt
      have hErrHalf :
          errReal < ((wassersteinDistance P Q).toReal - sSup dualSet) / 2 := by
        dsimp [ε, errReal] at hErrP hErrQ ⊢
        nlinarith
      have hErrGap :
          errReal + errReal < (wassersteinDistance P Q).toReal - sSup dualSet := by
        linarith
      linarith
    exact False.elim ((not_lt_of_ge hquantized_real) hstrict)

-- Proof comment: the item pipeline expects the raw label on Agent C's planned declaration name,
-- so expose the proved KR formula under that name as a thin alias.
/-- Example 17.55 (2): on a Polish metric space, if `P` and `Q` have finite first moment at
`x₀`, then the Kantorovich--Rubinstein formula expresses `wassersteinDistance P Q` as the dual
supremum of the signed integral difference over real-valued `1`-Lipschitz test functions
normalized by `f x₀ = 0`. -/
theorem reachableRightDataPerturbationContradictsOptimality
    (x₀ : E) (P Q : ProbabilityMeasure E)
    (hP : Integrable (fun x ↦ dist x x₀) (P : Measure E))
    (hQ : Integrable (fun x ↦ dist x x₀) (Q : Measure E)) :
    wassersteinDistance P Q =
      ENNReal.ofReal
        (sSup {r : ℝ | ∃ f : E → ℝ,
          f x₀ = 0 ∧
            LipschitzWith 1 f ∧
            r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)}) := by
  exact wassersteinDistance_eq_sSup_lipschitz_of_integrableDist x₀ P Q hP hQ

variable [BoundedSpace E]

/-- Helper for Example 17.55: on a bounded space, a real-valued `1`-Lipschitz function is
uniformly bounded by its value at one anchor plus the diameter of the space. -/
private theorem lipschitz_norm_le_anchor_add_diam
    (x₀ : E) {f : E → ℝ} (hf : LipschitzWith 1 f) :
    ∀ x, ‖f x‖ ≤ ‖f x₀‖ + Metric.diam (Set.univ : Set E) := by
  let C : ℝ := Metric.diam (Set.univ : Set E)
  have hUnivBounded : Bornology.IsBounded (Set.univ : Set E) := by
    simpa using (Bornology.isBounded_univ (α := E)).2 (show BoundedSpace E from inferInstance)
  intro x
  have hdist : dist (f x) (f x₀) ≤ dist x x₀ := by
    simpa using hf.dist_le_mul x x₀
  have hsub : ‖f x - f x₀‖ ≤ dist x x₀ := by
    simpa [Real.dist_eq] using hdist
  have hdiam : dist x x₀ ≤ C := by
    simpa [C] using Metric.dist_le_diam_of_mem hUnivBounded (by simp) (by simp)
  -- Proof comment: split `f x` into its anchored oscillation and the anchor value, then bound
  -- the oscillation by the diameter of the space.
  calc
    ‖f x‖ = ‖(f x - f x₀) + f x₀‖ := by ring_nf
    _ ≤ ‖f x - f x₀‖ + ‖f x₀‖ := norm_add_le _ _
    _ ≤ dist x x₀ + ‖f x₀‖ := add_le_add hsub le_rfl
    _ ≤ C + ‖f x₀‖ := add_le_add hdiam le_rfl
    _ = ‖f x₀‖ + Metric.diam (Set.univ : Set E) := by
      simp [C, add_comm]

/-- Helper for Example 17.55: on a bounded space, every real-valued `1`-Lipschitz function has
bounded range. -/
private theorem lipschitz_isBounded_range
    (x₀ : E) {f : E → ℝ} (hf : LipschitzWith 1 f) :
    Bornology.IsBounded (Set.range f) := by
  refine isBounded_iff_forall_norm_le.mpr ?_
  refine ⟨‖f x₀‖ + Metric.diam (Set.univ : Set E), ?_⟩
  intro y hy
  rcases hy with ⟨x, rfl⟩
  exact lipschitz_norm_le_anchor_add_diam x₀ hf x

/-- Helper for Example 17.55: on a bounded space, a real-valued `1`-Lipschitz function canonically
bundles to a bounded continuous function. -/
private def boundedContinuousOfLipschitz
    (x₀ : E) (f : E → ℝ) (hf : LipschitzWith 1 f) : E →ᵇ ℝ :=
  ⟨⟨f, hf.continuous⟩, Metric.isBounded_range_iff.1 (lipschitz_isBounded_range x₀ hf)⟩

/-- Helper for Example 17.55: on a bounded space, every real-valued `1`-Lipschitz function is
integrable against every probability measure. -/
private theorem lipschitz_integrable_of_boundedSpace
    (x₀ : E) (μ : ProbabilityMeasure E) {f : E → ℝ} (hf : LipschitzWith 1 f) :
    Integrable f (μ : Measure E) := by
  -- Proof comment: boundedness of the ambient space turns the pointwise Lipschitz estimate into
  -- a global bound, so the function is integrable under the finite probability measure `μ`.
  refine Integrable.of_bound hf.continuous.aestronglyMeasurable
      (‖f x₀‖ + Metric.diam (Set.univ : Set E)) ?_
  exact Filter.Eventually.of_forall (lipschitz_norm_le_anchor_add_diam x₀ hf)

-- Proof sketch: on bounded spaces, every `1`-Lipschitz function is automatically bounded, so the
-- anchored finite-first-moment formulation reduces to the simpler bounded test-function duality.
/-- Helper for Example 17.55: on a bounded Polish metric space, the Kantorovich--Rubinstein
formula expresses `wassersteinDistance P Q` as the dual supremum of the signed integral
difference over real-valued `1`-Lipschitz test functions. -/
-- TODO: Deduce this from the anchored KR formula by anchoring at an arbitrary point and using
-- boundedness to supply the first-moment integrability and remove the normalization `f x₀ = 0`.
theorem wassersteinDistance_eq_sSup_lipschitz
    (P Q : ProbabilityMeasure E) :
    wassersteinDistance P Q =
      ENNReal.ofReal
        (sSup {r : ℝ | ∃ f : E → ℝ,
          LipschitzWith 1 f ∧
            r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)}) := by
  let x₀ : E := Classical.choice P.nonempty
  have hP : Integrable (fun x ↦ dist x x₀) (P : Measure E) := by
    -- Proof comment: on a bounded space, the distance to the chosen anchor is uniformly bounded
    -- by the diameter of the whole space.
    refine Integrable.of_bound (by fun_prop) (Metric.diam (Set.univ : Set E)) ?_
    have hUnivBounded : Bornology.IsBounded (Set.univ : Set E) := by
      simpa using (Bornology.isBounded_univ (α := E)).2 (show BoundedSpace E from inferInstance)
    refine Filter.Eventually.of_forall ?_
    intro x
    have hdiam :
        dist x x₀ ≤ Metric.diam (Set.univ : Set E) := by
      exact Metric.dist_le_diam_of_mem hUnivBounded (by simp) (by simp)
    simpa [Real.norm_eq_abs, abs_of_nonneg (dist_nonneg : 0 ≤ dist x x₀)] using hdiam
  have hQ : Integrable (fun x ↦ dist x x₀) (Q : Measure E) := by
    -- Proof comment: the same bounded-diameter estimate gives the first moment bound for `Q`.
    refine Integrable.of_bound (by fun_prop) (Metric.diam (Set.univ : Set E)) ?_
    have hUnivBounded : Bornology.IsBounded (Set.univ : Set E) := by
      simpa using (Bornology.isBounded_univ (α := E)).2 (show BoundedSpace E from inferInstance)
    refine Filter.Eventually.of_forall ?_
    intro x
    have hdiam :
        dist x x₀ ≤ Metric.diam (Set.univ : Set E) := by
      exact Metric.dist_le_diam_of_mem hUnivBounded (by simp) (by simp)
    simpa [Real.norm_eq_abs, abs_of_nonneg (dist_nonneg : 0 ≤ dist x x₀)] using hdiam
  rw [wassersteinDistance_eq_sSup_lipschitz_of_integrableDist x₀ P Q hP hQ]
  -- Proof comment: the anchored and unanchored dual witness sets coincide after subtracting the
  -- anchor value, because constants cancel in the integral difference.
  congr 1
  have hset :
      {r : ℝ | ∃ f : E → ℝ, f x₀ = 0 ∧ LipschitzWith 1 f ∧
          r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)} =
        {r : ℝ | ∃ f : E → ℝ, LipschitzWith 1 f ∧
          r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)} := by
    ext r
    constructor
    · rintro ⟨f, -, hfLip, rfl⟩
      exact ⟨f, hfLip, rfl⟩
    · rintro ⟨f, hfLip, rfl⟩
      let g : E → ℝ := fun x ↦ f x - f x₀
      have hPf : Integrable f (P : Measure E) := lipschitz_integrable_of_boundedSpace x₀ P hfLip
      have hQf : Integrable f (Q : Measure E) := lipschitz_integrable_of_boundedSpace x₀ Q hfLip
      have hgLip : LipschitzWith 1 g := by
        simpa [g] using hfLip.sub (LipschitzWith.const (f x₀))
      have hPg : Integrable g (P : Measure E) := lipschitz_integrable_of_boundedSpace x₀ P hgLip
      have hQg : Integrable g (Q : Measure E) := lipschitz_integrable_of_boundedSpace x₀ Q hgLip
      have hPg_eq : ∫ x, g x ∂(P : Measure E) = ∫ x, f x ∂(P : Measure E) - f x₀ := by
        -- Proof comment: subtracting the anchor value shifts the expectation by the same constant.
        calc
          ∫ x, g x ∂(P : Measure E) = ∫ x, (f x + (-f x₀)) ∂(P : Measure E) := by
            simp [g, sub_eq_add_neg]
          _ = ∫ x, f x ∂(P : Measure E) + ∫ x, (-f x₀) ∂(P : Measure E) := by
            rw [integral_add hPf (integrable_const (-f x₀))]
          _ = ∫ x, f x ∂(P : Measure E) - f x₀ := by
            rw [MeasureTheory.integral_const]
            simp [probReal_univ, sub_eq_add_neg]
      have hQg_eq : ∫ x, g x ∂(Q : Measure E) = ∫ x, f x ∂(Q : Measure E) - f x₀ := by
        -- Proof comment: the same constant-cancellation identity holds for `Q`.
        calc
          ∫ x, g x ∂(Q : Measure E) = ∫ x, (f x + (-f x₀)) ∂(Q : Measure E) := by
            simp [g, sub_eq_add_neg]
          _ = ∫ x, f x ∂(Q : Measure E) + ∫ x, (-f x₀) ∂(Q : Measure E) := by
            rw [integral_add hQf (integrable_const (-f x₀))]
          _ = ∫ x, f x ∂(Q : Measure E) - f x₀ := by
            rw [MeasureTheory.integral_const]
            simp [probReal_univ, sub_eq_add_neg]
      have hdiff :
          ∫ x, g x ∂(P : Measure E) - ∫ x, g x ∂(Q : Measure E) =
            ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E) := by
        linarith
      exact ⟨g, by simp [g], hgLip, hdiff.symm⟩
  simpa [hset]

/-- Helper for Example 17.55: the bounded-continuous-function version of the
Kantorovich--Rubinstein dual formula on a bounded Polish metric space. -/
-- TODO: Convert bounded `1`-Lipschitz functions to bounded continuous functions and back using
-- the canonical bounded-continuous-function wrapper, then transport the previous supremum formula.
theorem wassersteinDistance_eq_sSup_boundedContinuous_lipschitz
    (P Q : ProbabilityMeasure E) :
    wassersteinDistance P Q =
      ENNReal.ofReal
        (sSup {r : ℝ | ∃ f : E →ᵇ ℝ,
          LipschitzWith 1 f ∧
            r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)}) := by
  let x₀ : E := Classical.choice P.nonempty
  rw [wassersteinDistance_eq_sSup_lipschitz P Q]
  -- Proof comment: on a bounded space, bundling and unbundling bounded Lipschitz functions does
  -- not change either the Lipschitz constraint or the integral difference.
  congr 1
  have hset :
      {r : ℝ | ∃ f : E → ℝ, LipschitzWith 1 f ∧
          r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)} =
        {r : ℝ | ∃ f : E →ᵇ ℝ, LipschitzWith 1 f ∧
          r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)} := by
    ext r
    constructor
    · rintro ⟨f, hfLip, rfl⟩
      let g : E →ᵇ ℝ := boundedContinuousOfLipschitz x₀ f hfLip
      exact ⟨g, by simpa [g, boundedContinuousOfLipschitz] using hfLip, rfl⟩
    · rintro ⟨f, hfLip, rfl⟩
      exact ⟨fun x ↦ f x, by simpa using hfLip, rfl⟩
  simpa [hset]

end Wasserstein

section TotalVariation

variable {E : Type u} [MeasurableSpace E]

/-- Helper for Example 17.55: the chosen Lean owner
`SignedMeasure.totalVariationNorm E
((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure)`
is twice the normalized probability total variation distance
`totalVariationDistance P Q`. -/
theorem sourceTVNorm_eq_two_mul_totalVariationDistance
    (P Q : ProbabilityMeasure E) :
    SignedMeasure.totalVariationNorm E
        ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) =
      2 * totalVariationDistance P Q := by
  -- Proof comment: the imported owner already identifies `totalVariationDistance` with half the
  -- source norm, so this wrapper is just a one-line algebraic rearrangement.
  rw [totalVariationDistance_eq_half_totalVariationNorm]
  ring

/-- Consequence for Example 17.55 (3): the book's total-variation norm formula (17.28) is the supremum of the signed
integral difference over measurable real-valued test functions bounded in absolute value by `1`.
-/
theorem sourceTVNorm_eq_sSup_bounded_measurable
    [TopologicalSpace E] [BorelSpace E] [PolishSpace E]
    (P Q : ProbabilityMeasure E) :
    SignedMeasure.totalVariationNorm E
        ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) =
      sSup {r : ℝ | ∃ f : E → ℝ,
        Measurable f ∧
          (∀ x, ‖f x‖ ≤ 1) ∧
          r = ∫ x, f x ∂(P : Measure E) - ∫ x, f x ∂(Q : Measure E)} := by
  -- Proof comment: combine the imported half-supremum formula with the factor-`2` normalization
  -- wrapper already established above.
  rw [sourceTVNorm_eq_two_mul_totalVariationDistance,
    ProbabilityTheory.totalVariationDistance_eq_sSup_bounded_measurable]
  ring

section CouplingOffDiagonal

variable [TopologicalSpace E] [BorelSpace E] [PolishSpace E] [MeasurableEq E]

/-- Helper for Example 17.55: for a Hahn decomposition set `A`, every coupling of `P` and `Q`
must spend at least the Hahn excess mass outside the diagonal. -/
private theorem couplingOffDiagonal_ge_hahnExcess
    (P Q : ProbabilityMeasure E) {A : Set E} (hA : MeasurableSet A)
    {π : ProbabilityMeasure (E × E)} (hπ : IsCoupling π P Q) :
    (P : Measure E).real A - (Q : Measure E).real A ≤
      ((π : Measure (E × E)) ((Set.univ : Set (E × E)) \ Set.diagonal E)).toReal := by
  let μ : Measure (E × E) := (π : Measure (E × E))
  let offDiag : Set (E × E) := (Set.univ : Set (E × E)) \ Set.diagonal E
  have hPA :
      (P : Measure E).real A = μ.real (Prod.fst ⁻¹' A) := by
    -- Proof comment: the first marginal of a coupling is `P`, so `P(A)` is the mass of the
    -- first-coordinate preimage of `A`.
    have hfst : μ (Prod.fst ⁻¹' A) = (P : Measure E) A := by
      have hfst' : μ.fst A = (P : Measure E) A := by
        simpa [μ] using congrArg (fun ν : Measure E ↦ ν A) hπ.1
      calc
        μ (Prod.fst ⁻¹' A) = μ.fst A := by rw [Measure.fst_apply hA]
        _ = (P : Measure E) A := hfst'
    rw [Measure.real_def, Measure.real_def]
    exact congrArg ENNReal.toReal hfst.symm
  have hQA :
      (Q : Measure E).real A = μ.real (Prod.snd ⁻¹' A) := by
    -- Proof comment: the second marginal identity gives the analogous formula for `Q(A)`.
    have hsnd : μ (Prod.snd ⁻¹' A) = (Q : Measure E) A := by
      have hsnd' : μ.snd A = (Q : Measure E) A := by
        simpa [μ] using congrArg (fun ν : Measure E ↦ ν A) hπ.2
      calc
        μ (Prod.snd ⁻¹' A) = μ.snd A := by rw [Measure.snd_apply hA]
        _ = (Q : Measure E) A := hsnd'
    rw [Measure.real_def, Measure.real_def]
    exact congrArg ENNReal.toReal hsnd.symm
  have hfst_preimage :
      Prod.fst ⁻¹' A = (A ×ˢ A) ∪ (A ×ˢ Aᶜ) := by
    ext z
    by_cases hz : z.2 ∈ A <;> simp [hz]
  have hsnd_preimage :
      Prod.snd ⁻¹' A = (A ×ˢ A) ∪ (Aᶜ ×ˢ A) := by
    ext z
    by_cases hz : z.1 ∈ A <;> simp [hz]
  have hAA_disjoint : Disjoint (A ×ˢ A : Set (E × E)) (A ×ˢ Aᶜ) := by
    rw [Set.disjoint_left]
    intro z hzAA hzAAc
    exact hzAAc.2 hzAA.2
  have hAA'_disjoint : Disjoint (A ×ˢ A : Set (E × E)) (Aᶜ ×ˢ A) := by
    rw [Set.disjoint_left]
    intro z hzAA hzAcA
    exact hzAcA.1 hzAA.1
  have hfst_split :
      μ.real (Prod.fst ⁻¹' A) = μ.real (A ×ˢ A) + μ.real (A ×ˢ Aᶜ) := by
    -- Proof comment: the first-coordinate preimage splits into the diagonal rectangle `A × A`
    -- and the off-diagonal rectangle `A × Aᶜ`.
    rw [hfst_preimage, measureReal_union hAA_disjoint (hA.prod hA.compl)]
  have hsnd_split :
      μ.real (Prod.snd ⁻¹' A) = μ.real (A ×ˢ A) + μ.real (Aᶜ ×ˢ A) := by
    -- Proof comment: the second-coordinate preimage has the symmetric split.
    rw [hsnd_preimage, measureReal_union hAA'_disjoint (hA.compl.prod hA)]
  have hAAc_subset : (A ×ˢ Aᶜ : Set (E × E)) ⊆ offDiag := by
    -- Proof comment: points in `A × Aᶜ` cannot lie on the diagonal because their coordinates lie
    -- on opposite sides of the partition.
    intro z hz
    refine ⟨by simp, ?_⟩
    intro hzDiag
    have hzEq : z.1 = z.2 := by simpa [Set.mem_diagonal] using hzDiag
    have hz2A : z.2 ∈ A := by simpa [hzEq] using hz.1
    exact hz.2 hz2A
  have hAAc_le :
      μ.real (A ×ˢ Aᶜ : Set (E × E)) ≤ μ.real offDiag :=
    measureReal_mono hAAc_subset
  have hAcA_nonneg : 0 ≤ μ.real (Aᶜ ×ˢ A : Set (E × E)) := by positivity
  calc
    (P : Measure E).real A - (Q : Measure E).real A
      = (μ.real (A ×ˢ A) + μ.real (A ×ˢ Aᶜ)) -
          (μ.real (A ×ˢ A) + μ.real (Aᶜ ×ˢ A)) := by
            rw [hPA, hQA, hfst_split, hsnd_split]
    _ = μ.real (A ×ˢ Aᶜ) - μ.real (Aᶜ ×ˢ A) := by ring
    _ ≤ μ.real (A ×ˢ Aᶜ) := by linarith
    _ ≤ μ.real offDiag := hAAc_le
    _ = ((π : Measure (E × E)) offDiag).toReal := by
          rw [Measure.real_def]

/-- Helper for Example 17.55: a Hahn decomposition set yields the common part and the two residual
measures whose masses equal `totalVariationDistance P Q`. -/
-- TODO: Package the Hahn-set residual measures `ρ` and `σ`, prove the decomposition identities
-- `P = α + ρ` and `Q = α + σ`, then identify `ρ.real univ = σ.real univ = totalVariationDistance P Q`
-- via the Hahn-excess formula from the imported total-variation owner.
private theorem hahnResidualDecomposition
    (P Q : ProbabilityMeasure E) {A : Set E} (hA : MeasurableSet A)
    (hA_le : (Q : Measure E).restrict A ≤ (P : Measure E).restrict A)
    (hAc_le : (P : Measure E).restrict Aᶜ ≤ (Q : Measure E).restrict Aᶜ) :
    let α : Measure E := (Q : Measure E).restrict A + (P : Measure E).restrict Aᶜ
    let ρ : Measure E := (P : Measure E).restrict A - (Q : Measure E).restrict A
    let σ : Measure E := (Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ
    (P : Measure E) = α + ρ ∧
      (Q : Measure E) = α + σ ∧
      ρ Aᶜ = 0 ∧
      σ A = 0 ∧
      (P : Measure E).real A - (Q : Measure E).real A = totalVariationDistance P Q ∧
      ρ.real Set.univ = totalVariationDistance P Q ∧
      σ.real Set.univ = totalVariationDistance P Q := by
  dsimp only
  have hP_decomp :
      (P : Measure E) =
        ((Q : Measure E).restrict A + (P : Measure E).restrict Aᶜ) +
          ((P : Measure E).restrict A - (Q : Measure E).restrict A) := by
    -- Proof comment: split `P` across the Hahn partition and then replace the `A` piece by the
    -- common part plus the positive residual.
    calc
      (P : Measure E) = (P : Measure E).restrict A + (P : Measure E).restrict Aᶜ := by
        simpa using (Measure.restrict_add_restrict_compl (μ := (P : Measure E)) hA).symm
      _ = (((P : Measure E).restrict A - (Q : Measure E).restrict A) +
            (Q : Measure E).restrict A) + (P : Measure E).restrict Aᶜ := by
          rw [Measure.sub_add_cancel_of_le hA_le]
      _ = ((Q : Measure E).restrict A + (P : Measure E).restrict Aᶜ) +
            ((P : Measure E).restrict A - (Q : Measure E).restrict A) := by
          rw [add_assoc,
            add_left_comm ((P : Measure E).restrict A - (Q : Measure E).restrict A)
              ((Q : Measure E).restrict A) ((P : Measure E).restrict Aᶜ),
            add_comm ((P : Measure E).restrict A - (Q : Measure E).restrict A)
              ((P : Measure E).restrict Aᶜ),
            ← add_assoc]
  have hQ_decomp :
      (Q : Measure E) =
        ((Q : Measure E).restrict A + (P : Measure E).restrict Aᶜ) +
          ((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ) := by
    -- Proof comment: the same partition argument for `Q` uses the residual on `Aᶜ`.
    calc
      (Q : Measure E) = (Q : Measure E).restrict A + (Q : Measure E).restrict Aᶜ := by
        simpa using (Measure.restrict_add_restrict_compl (μ := (Q : Measure E)) hA).symm
      _ = (Q : Measure E).restrict A +
            (((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ) +
              (P : Measure E).restrict Aᶜ) := by
          rw [Measure.sub_add_cancel_of_le hAc_le]
      _ = ((Q : Measure E).restrict A + (P : Measure E).restrict Aᶜ) +
            ((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ) := by
          rw [add_assoc,
            add_comm ((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ)
              ((P : Measure E).restrict Aᶜ),
            ← add_assoc]
  have hρ_compl :
      (((P : Measure E).restrict A - (Q : Measure E).restrict A) Aᶜ) = 0 := by
    -- Proof comment: both restricted pieces vanish on `Aᶜ`, so the positive residual is supported
    -- on `A`.
    rw [Measure.sub_apply hA.compl hA_le]
    simp [Measure.restrict_apply, hA.compl]
  have hσ_A :
      (((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ) A) = 0 := by
    -- Proof comment: symmetrically, the negative residual is supported on `Aᶜ`.
    rw [Measure.sub_apply hA hAc_le]
    simp [Measure.restrict_apply, hA]
  have hsub_compl_zero :
      (((P : Measure E) - (Q : Measure E)).restrict Aᶜ) = 0 := by
    -- Proof comment: on the Hahn negative side there is no positive part of `P - Q`.
    exact Measure.restrict_eq_zero.2
      (Measure.sub_apply_eq_zero_of_restrict_le_restrict hAc_le hA.compl)
  have hsub_A_zero :
      (((Q : Measure E) - (P : Measure E)).restrict A) = 0 := by
    -- Proof comment: reversing the pair gives the same vanishing statement on `A`.
    exact Measure.restrict_eq_zero.2
      (Measure.sub_apply_eq_zero_of_restrict_le_restrict hA_le hA)
  have hρ_eq :
      (P : Measure E).restrict A - (Q : Measure E).restrict A = (P : Measure E) - (Q : Measure E) := by
    -- Proof comment: the whole positive Jordan part of `P - Q` lives on `A`.
    calc
      (P : Measure E).restrict A - (Q : Measure E).restrict A
          = (((P : Measure E) - (Q : Measure E)).restrict A) := by
              rw [← Measure.restrict_sub_eq_restrict_sub_restrict hA]
      _ = (((P : Measure E) - (Q : Measure E)).restrict A) +
            (((P : Measure E) - (Q : Measure E)).restrict Aᶜ) := by
              rw [hsub_compl_zero, add_zero]
      _ = (P : Measure E) - (Q : Measure E) := by
              simpa using
                (Measure.restrict_add_restrict_compl (μ := (P : Measure E) - (Q : Measure E)) hA)
  have hσ_eq :
      (Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ = (Q : Measure E) - (P : Measure E) := by
    -- Proof comment: the reversed positive Jordan part is concentrated on the complement side.
    calc
      (Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ
          = (((Q : Measure E) - (P : Measure E)).restrict Aᶜ) := by
              rw [← Measure.restrict_sub_eq_restrict_sub_restrict hA.compl]
      _ = (((Q : Measure E) - (P : Measure E)).restrict A) +
            (((Q : Measure E) - (P : Measure E)).restrict Aᶜ) := by
              rw [hsub_A_zero, zero_add]
      _ = (Q : Measure E) - (P : Measure E) := by
              simpa using
                (Measure.restrict_add_restrict_compl (μ := (Q : Measure E) - (P : Measure E)) hA)
  have hρ_mass :
      ((P : Measure E).restrict A - (Q : Measure E).restrict A).real Set.univ =
        (P : Measure E).real A - (Q : Measure E).real A := by
    -- Proof comment: the residual mass on `A` is exactly the Hahn excess on `A`.
    calc
      ((P : Measure E).restrict A - (Q : Measure E).restrict A).real Set.univ
          = ((((P : Measure E).restrict A) Set.univ - ((Q : Measure E).restrict A) Set.univ).toReal) := by
              simp [Measure.real_def, Measure.sub_apply MeasurableSet.univ hA_le]
      _ = ((P : Measure E).restrict A).real Set.univ -
            ((Q : Measure E).restrict A).real Set.univ := by
              rw [ENNReal.toReal_sub_of_le (hA_le Set.univ) (measure_ne_top _ _),
                Measure.real_def, Measure.real_def]
      _ = (P : Measure E).real A - (Q : Measure E).real A := by
              rw [measureReal_restrict_apply_univ, measureReal_restrict_apply_univ]
  have hσ_mass :
      ((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ).real Set.univ =
        (Q : Measure E).real Aᶜ - (P : Measure E).real Aᶜ := by
    -- Proof comment: the complement residual mass is the complementary excess.
    calc
      ((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ).real Set.univ
          = ((((Q : Measure E).restrict Aᶜ) Set.univ - ((P : Measure E).restrict Aᶜ) Set.univ).toReal) := by
              simp [Measure.real_def, Measure.sub_apply MeasurableSet.univ hAc_le]
      _ = ((Q : Measure E).restrict Aᶜ).real Set.univ -
            ((P : Measure E).restrict Aᶜ).real Set.univ := by
              rw [ENNReal.toReal_sub_of_le (hAc_le Set.univ) (measure_ne_top _ _),
                Measure.real_def, Measure.real_def]
      _ = (Q : Measure E).real Aᶜ - (P : Measure E).real Aᶜ := by
              rw [measureReal_restrict_apply_univ, measureReal_restrict_apply_univ]
  have hmass_eq :
      ((P : Measure E).restrict A - (Q : Measure E).restrict A).real Set.univ =
        ((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ).real Set.univ := by
    -- Proof comment: because `P` and `Q` both have total mass `1`, the excess on `A` equals the
    -- deficit on `Aᶜ`.
    rw [hρ_mass, hσ_mass, measureReal_compl (μ := (P : Measure E)) hA,
      measureReal_compl (μ := (Q : Measure E)) hA]
    simp [probReal_univ]
  have htvNorm :
      SignedMeasure.totalVariationNorm E
          ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) =
        ((P : Measure E).restrict A - (Q : Measure E).restrict A).real Set.univ +
          ((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ).real Set.univ := by
    -- Proof comment: after identifying the residuals with the global Jordan parts, the total
    -- variation norm is the sum of their masses.
    calc
      SignedMeasure.totalVariationNorm E
          ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure)
          = (((P : Measure E) - (Q : Measure E)).real Set.univ) +
              (((Q : Measure E) - (P : Measure E)).real Set.univ) := by
                simpa [SignedMeasure.totalVariationNorm,
                  Measure.toJordanDecomposition_toSignedMeasure_sub] using
                  (SignedMeasure.totalVariation_real_univ_eq_jordan
                    ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure))
      _ = ((P : Measure E).restrict A - (Q : Measure E).restrict A).real Set.univ +
            ((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ).real Set.univ := by
              rw [← hρ_eq, ← hσ_eq]
  have hρ_tv :
      ((P : Measure E).restrict A - (Q : Measure E).restrict A).real Set.univ =
        totalVariationDistance P Q := by
    -- Proof comment: equal positive and negative residual masses turn the half-norm formula into
    -- the claimed identity for `ρ`.
    calc
      ((P : Measure E).restrict A - (Q : Measure E).restrict A).real Set.univ
          = ((((P : Measure E).restrict A - (Q : Measure E).restrict A).real Set.univ) +
              (((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ).real Set.univ)) / 2 := by
                rw [hmass_eq]
                ring
      _ = SignedMeasure.totalVariationNorm E
            ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) / 2 := by
                rw [htvNorm]
      _ = totalVariationDistance P Q := by
                rw [totalVariationDistance_eq_half_totalVariationNorm]
  have hσ_tv :
      ((Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ).real Set.univ =
        totalVariationDistance P Q := by
    -- Proof comment: the complement residual has the same mass as `ρ`, so it realizes the same
    -- total variation distance.
    rw [← hρ_tv, hmass_eq]
  have hExcess_tv :
      (P : Measure E).real A - (Q : Measure E).real A = totalVariationDistance P Q := by
    -- Proof comment: the Hahn excess is exactly the mass of `ρ`, and that mass is already
    -- identified with `totalVariationDistance`.
    rw [← hρ_mass, hρ_tv]
  exact ⟨hP_decomp, hQ_decomp, hρ_compl, hσ_A, hExcess_tv, hρ_tv, hσ_tv⟩

/-- Helper for Example 17.55: the diagonal pushforward of a measure has the original first
marginal. -/
private theorem map_diagonal_fst_eq (μ : Measure E) :
    Measure.map Prod.fst (Measure.map (fun x : E ↦ (x, x)) μ) = μ := by
  -- Proof comment: projecting after the diagonal embedding is the identity map.
  ext s hs
  calc
    Measure.map Prod.fst (Measure.map (fun x : E ↦ (x, x)) μ) s
        = (Measure.map (fun x : E ↦ (x, x)) μ) (Prod.fst ⁻¹' s) := by
            rw [Measure.map_apply measurable_fst hs]
    _ = μ ((fun x : E ↦ (x, x)) ⁻¹' (Prod.fst ⁻¹' s)) := by
            rw [Measure.map_apply (μ := μ) (f := fun x : E ↦ (x, x))
              (s := Prod.fst ⁻¹' s) (measurable_id.prodMk measurable_id) (measurable_fst hs)]
    _ = μ s := by rfl

/-- Helper for Example 17.55: the diagonal pushforward of a measure has the original second
marginal. -/
private theorem map_diagonal_snd_eq (μ : Measure E) :
    Measure.map Prod.snd (Measure.map (fun x : E ↦ (x, x)) μ) = μ := by
  -- Proof comment: the second projection also collapses the diagonal embedding back to the
  -- identity.
  ext s hs
  calc
    Measure.map Prod.snd (Measure.map (fun x : E ↦ (x, x)) μ) s
        = (Measure.map (fun x : E ↦ (x, x)) μ) (Prod.snd ⁻¹' s) := by
            rw [Measure.map_apply measurable_snd hs]
    _ = μ ((fun x : E ↦ (x, x)) ⁻¹' (Prod.snd ⁻¹' s)) := by
            rw [Measure.map_apply (μ := μ) (f := fun x : E ↦ (x, x))
              (s := Prod.snd ⁻¹' s) (measurable_id.prodMk measurable_id) (measurable_snd hs)]
    _ = μ s := by rfl

/-- Helper for Example 17.55: the diagonal pushforward gives zero mass to the off-diagonal set. -/
private theorem map_diagonal_offDiagonal_eq_zero (μ : Measure E) :
    Measure.map (fun x : E ↦ (x, x)) μ
      ((Set.univ : Set (E × E)) \ Set.diagonal E) = 0 := by
  -- Proof comment: a diagonal point never lands in the complement of the diagonal.
  have hOff :
      MeasurableSet (((Set.univ : Set (E × E)) \ Set.diagonal E)) := by
    convert (measurableSet_diagonal : MeasurableSet (Set.diagonal E)).compl using 1
    ext z
    simp
  rw [Measure.map_apply (μ := μ) (f := fun x : E ↦ (x, x)) (s := ((Set.univ : Set (E × E)) \ Set.diagonal E))
      (measurable_id.prodMk measurable_id) hOff]
  simp [Set.diagonal]

/-- Helper for Example 17.55: scaling the product `ρ ⊗ σ` by the common residual mass gives first
marginal `ρ`. -/
private theorem scaledResidualProduct_fst_eq
    (ρ σ : Measure E) [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hMass : σ Set.univ = ρ Set.univ) :
    Measure.map Prod.fst ((ρ Set.univ)⁻¹ • (ρ.prod σ)) = ρ := by
  by_cases hρ0 : ρ Set.univ = 0
  · -- Proof comment: if the residual mass vanishes, then both residual measures are zero and the
    -- scaled product vanishes as well.
    have hρ_zero : ρ = 0 := Measure.measure_univ_eq_zero.mp hρ0
    have hσ0 : σ Set.univ = 0 := by rw [hMass, hρ0]
    have hσ_zero : σ = 0 := Measure.measure_univ_eq_zero.mp hσ0
    simp [hρ_zero, hσ_zero]
  · -- Proof comment: away from the zero-mass case, one scalar cancellation turns the first
    -- marginal of the normalized product into `ρ`.
    calc
      Measure.map Prod.fst ((ρ Set.univ)⁻¹ • (ρ.prod σ))
          = (ρ Set.univ)⁻¹ • Measure.map Prod.fst (ρ.prod σ) := by
              rw [Measure.map_smul]
      _ = (ρ Set.univ)⁻¹ • ((σ Set.univ) • ρ) := by
              rw [Measure.map_fst_prod]
      _ = ((ρ Set.univ)⁻¹ * σ Set.univ) • ρ := by
              rw [smul_smul]
      _ = ((ρ Set.univ)⁻¹ * ρ Set.univ) • ρ := by
              rw [hMass]
      _ = ρ := by
              rw [ENNReal.inv_mul_cancel hρ0 (measure_ne_top _ _), one_smul]

/-- Helper for Example 17.55: the same normalized residual product has second marginal `σ`. -/
private theorem scaledResidualProduct_snd_eq
    (ρ σ : Measure E) [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hMass : ρ Set.univ = σ Set.univ) :
    Measure.map Prod.snd ((ρ Set.univ)⁻¹ • (ρ.prod σ)) = σ := by
  by_cases hρ0 : ρ Set.univ = 0
  · -- Proof comment: when the common residual mass is zero, both residual measures vanish.
    have hρ_zero : ρ = 0 := Measure.measure_univ_eq_zero.mp hρ0
    have hσ0 : σ Set.univ = 0 := by rw [← hMass, hρ0]
    have hσ_zero : σ = 0 := Measure.measure_univ_eq_zero.mp hσ0
    simp [hρ_zero, hσ_zero]
  · -- Proof comment: in the nonzero branch, the second marginal is another one-line scalar
    -- cancellation.
    calc
      Measure.map Prod.snd ((ρ Set.univ)⁻¹ • (ρ.prod σ))
          = (ρ Set.univ)⁻¹ • Measure.map Prod.snd (ρ.prod σ) := by
              rw [Measure.map_smul]
      _ = (ρ Set.univ)⁻¹ • ((ρ Set.univ) • σ) := by
              rw [Measure.map_snd_prod]
      _ = ((ρ Set.univ)⁻¹ * ρ Set.univ) • σ := by
              rw [smul_smul]
      _ = σ := by
              rw [ENNReal.inv_mul_cancel hρ0 (measure_ne_top _ _), one_smul]

/-- Helper for Example 17.55: the normalized residual product lives off the diagonal because the
two residual measures live on opposite Hahn pieces. -/
private theorem scaledResidualProduct_diagonal_eq_zero
    {A : Set E} (ρ σ : Measure E) [IsFiniteMeasure ρ] [IsFiniteMeasure σ]
    (hρAc : ρ Aᶜ = 0) (hσA : σ A = 0) :
    ((ρ Set.univ)⁻¹ • (ρ.prod σ)) (Set.diagonal E) = 0 := by
  have hDiagSubset :
      Set.diagonal E ⊆ ((A ×ˢ A : Set (E × E)) ∪ (Aᶜ ×ˢ Aᶜ)) := by
    intro z hz
    have hzEq : z.1 = z.2 := by simpa [Set.mem_diagonal] using hz
    by_cases hzA : z.1 ∈ A
    · left
      exact ⟨hzA, by simpa [hzEq] using hzA⟩
    · right
      exact ⟨by simpa [Set.mem_compl] using hzA, by simpa [Set.mem_compl, hzEq] using hzA⟩
  have hAA_zero : (ρ.prod σ) (A ×ˢ A : Set (E × E)) = 0 := by
    rw [Measure.prod_prod]
    simp [hσA]
  have hAcAc_zero : (ρ.prod σ) (Aᶜ ×ˢ Aᶜ : Set (E × E)) = 0 := by
    rw [Measure.prod_prod]
    simp [hρAc]
  have hUnion_zero :
      (ρ.prod σ) (((A ×ˢ A : Set (E × E)) ∪ (Aᶜ ×ˢ Aᶜ))) = 0 := by
    exact measure_union_null hAA_zero hAcAc_zero
  have hProdDiag_zero : (ρ.prod σ) (Set.diagonal E) = 0 :=
    measure_mono_null hDiagSubset hUnion_zero
  -- Proof comment: scaling preserves the zero diagonal mass of the raw residual product.
  rw [Measure.smul_apply, smul_eq_mul, hProdDiag_zero, mul_zero]

/-- Helper for Example 17.55: a Hahn decomposition packages the common diagonal part and the
normalized residual product into a coupling attaining `totalVariationDistance`. -/
private theorem existsCoupling_offDiagonal_eq_totalVariationDistance
    (P Q : ProbabilityMeasure E) :
    ∃ π : ProbabilityMeasure (E × E), IsCoupling π P Q ∧
      ((π : Measure (E × E))
        ((Set.univ : Set (E × E)) \ Set.diagonal E)).toReal =
        totalVariationDistance P Q := by
  rcases exists_isHahnDecomposition (Q : Measure E) (P : Measure E) with ⟨A, hA⟩
  let α : Measure E := (Q : Measure E).restrict A + (P : Measure E).restrict Aᶜ
  let ρ : Measure E := (P : Measure E).restrict A - (Q : Measure E).restrict A
  let σ : Measure E := (Q : Measure E).restrict Aᶜ - (P : Measure E).restrict Aᶜ
  letI : IsFiniteMeasure α := by
    dsimp [α]
    infer_instance
  letI : IsFiniteMeasure ρ := by
    dsimp [ρ]
    infer_instance
  letI : IsFiniteMeasure σ := by
    dsimp [σ]
    infer_instance
  rcases (by
    simpa [α, ρ, σ] using
      hahnResidualDecomposition P Q hA.measurableSet hA.le_on hA.ge_on_compl) with
    ⟨hP_decomp, hQ_decomp, hρ_compl, hσ_A, -, hρ_tv, hσ_tv⟩
  let common : Measure (E × E) := Measure.map (fun x : E ↦ (x, x)) α
  let residual : Measure (E × E) := (ρ Set.univ)⁻¹ • (ρ.prod σ)
  let μ : Measure (E × E) := common + residual
  letI : IsFiniteMeasure common := by
    dsimp [common]
    infer_instance
  letI : IsFiniteMeasure residual := by
    refine ⟨?_⟩
    dsimp [residual]
    rw [← Set.univ_prod_univ, Measure.prod_prod]
    rcases eq_or_ne (ρ Set.univ) 0 with hρ0 | hρ0
    · simp [hρ0]
    · have hInv_lt_top : (ρ Set.univ)⁻¹ < ∞ := by
        exact lt_of_le_of_ne le_top (ENNReal.inv_ne_top.mpr hρ0)
      exact ENNReal.mul_lt_top hInv_lt_top <|
        ENNReal.mul_lt_top (measure_lt_top _ _) (measure_lt_top _ _)
  letI : IsFiniteMeasure μ := by
    dsimp [μ]
    infer_instance
  have hOffMeas :
      MeasurableSet (((Set.univ : Set (E × E)) \ Set.diagonal E)) := by
    convert (measurableSet_diagonal : MeasurableSet (Set.diagonal E)).compl using 1
    ext z
    simp
  have hMassEq : ρ Set.univ = σ Set.univ := by
    -- Proof comment: the two residual masses agree because the decomposition identifies both of
    -- their real masses with the same total variation distance.
    refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp ?_
    simpa [Measure.real_def] using hρ_tv.trans hσ_tv.symm
  have hCommon_fst : Measure.map Prod.fst common = α := by
    -- Proof comment: the common part sits on the diagonal, so either projection recovers `α`.
    simpa [common] using map_diagonal_fst_eq (μ := α)
  have hCommon_snd : Measure.map Prod.snd common = α := by
    -- Proof comment: the second projection behaves identically on the diagonal common part.
    simpa [common] using map_diagonal_snd_eq (μ := α)
  have hResidual_fst : Measure.map Prod.fst residual = ρ := by
    -- Proof comment: the normalized residual product was calibrated so its first marginal is
    -- exactly the positive residual `ρ`.
    simpa [residual] using scaledResidualProduct_fst_eq ρ σ hMassEq.symm
  have hResidual_snd : Measure.map Prod.snd residual = σ := by
    -- Proof comment: the same normalization gives the second marginal `σ`.
    simpa [residual] using scaledResidualProduct_snd_eq ρ σ hMassEq
  have hμ_fst : Measure.map Prod.fst μ = (P : Measure E) := by
    -- Proof comment: adding the diagonal common part and the residual product reconstructs the
    -- first marginal decomposition `P = α + ρ`.
    calc
      Measure.map Prod.fst μ = Measure.map Prod.fst (common + residual) := by
        rfl
      _ = Measure.map Prod.fst common + Measure.map Prod.fst residual := by
        rw [Measure.map_add _ _ measurable_fst]
      _ = α + ρ := by rw [hCommon_fst, hResidual_fst]
      _ = (P : Measure E) := hP_decomp.symm
  have hμ_snd : Measure.map Prod.snd μ = (Q : Measure E) := by
    -- Proof comment: the second marginal similarly reconstructs `Q = α + σ`.
    calc
      Measure.map Prod.snd μ = Measure.map Prod.snd (common + residual) := by
        rfl
      _ = Measure.map Prod.snd common + Measure.map Prod.snd residual := by
        rw [Measure.map_add _ _ measurable_snd]
      _ = α + σ := by rw [hCommon_snd, hResidual_snd]
      _ = (Q : Measure E) := hQ_decomp.symm
  have hμ_prob : IsProbabilityMeasure μ := by
    -- Proof comment: once one marginal is `P`, the total mass of `μ` must be `1`.
    refine ⟨?_⟩
    calc
      μ Set.univ = Measure.map Prod.fst μ Set.univ := by
        rw [Measure.map_apply measurable_fst MeasurableSet.univ]
        simp
      _ = (P : Measure E) Set.univ := by rw [hμ_fst]
      _ = 1 := by simp
  let π : ProbabilityMeasure (E × E) := ⟨μ, hμ_prob⟩
  have hπ : IsCoupling π P Q := by
    -- Proof comment: the two marginal identities are exactly the coupling conditions.
    exact ⟨hμ_fst, hμ_snd⟩
  have hCommon_offDiag :
      common (((Set.univ : Set (E × E)) \ Set.diagonal E)) = 0 := by
    -- Proof comment: the diagonal common part never leaves the diagonal.
    simpa [common] using map_diagonal_offDiagonal_eq_zero (μ := α)
  have hResidual_diag :
      residual (Set.diagonal E) = 0 := by
    -- Proof comment: the residual product is supported on `A × Aᶜ`, so it has zero diagonal mass.
    simpa [residual] using scaledResidualProduct_diagonal_eq_zero (ρ := ρ) (σ := σ) hρ_compl hσ_A
  have hResidual_univ : residual Set.univ = ρ Set.univ := by
    -- Proof comment: the first marginal computation on `univ` identifies the total residual mass.
    calc
      residual Set.univ = Measure.map Prod.fst residual Set.univ := by
        rw [Measure.map_apply measurable_fst MeasurableSet.univ]
        simp
      _ = ρ Set.univ := by rw [hResidual_fst]
  have hResidual_offDiag :
      residual (((Set.univ : Set (E × E)) \ Set.diagonal E)) = residual Set.univ := by
    -- Proof comment: since the residual product gives zero mass to the diagonal, its off-diagonal
    -- mass is its full mass.
    have hOffEq :
        ((Set.univ : Set (E × E)) \ Set.diagonal E) = (Set.diagonal E)ᶜ := by
      ext z
      simp
    rw [hOffEq, measure_compl (measurableSet_diagonal : MeasurableSet (Set.diagonal E))
      (measure_ne_top _ _), hResidual_diag, tsub_zero]
  have hμ_offDiag :
      μ (((Set.univ : Set (E × E)) \ Set.diagonal E)) =
        residual (((Set.univ : Set (E × E)) \ Set.diagonal E)) := by
    -- Proof comment: the only off-diagonal mass comes from the residual product term.
    calc
      μ (((Set.univ : Set (E × E)) \ Set.diagonal E))
          = (common + residual) (((Set.univ : Set (E × E)) \ Set.diagonal E)) := by
              rfl
      _ = common (((Set.univ : Set (E × E)) \ Set.diagonal E)) +
            residual (((Set.univ : Set (E × E)) \ Set.diagonal E)) := by
              simpa using
                (Measure.add_apply common residual
                  (((Set.univ : Set (E × E)) \ Set.diagonal E)) hOffMeas)
      _ = residual (((Set.univ : Set (E × E)) \ Set.diagonal E)) := by
              rw [hCommon_offDiag, zero_add]
  refine ⟨π, hπ, ?_⟩
  -- Proof comment: the off-diagonal mass of the constructed coupling is exactly the residual mass,
  -- which the Hahn residual decomposition already identified with `totalVariationDistance`.
  calc
    ((π : Measure (E × E)) (((Set.univ : Set (E × E)) \ Set.diagonal E))).toReal
        = (μ (((Set.univ : Set (E × E)) \ Set.diagonal E))).toReal := by
            rfl
    _ = (residual (((Set.univ : Set (E × E)) \ Set.diagonal E))).toReal := by
            rw [hμ_offDiag]
    _ = (residual Set.univ).toReal := by
            rw [hResidual_offDiag]
    _ = (ρ Set.univ).toReal := by
            rw [hResidual_univ]
    _ = ρ.real Set.univ := by
            rw [Measure.real_def]
    _ = totalVariationDistance P Q := hρ_tv

-- Proof sketch: among all couplings of `P` and `Q`, minimize the mass away from the diagonal.
-- This off-diagonal mass equals the probability that the coupled coordinates disagree and yields
-- the classical coupling representation of total variation.
-- `MeasurableEq.measurableSet_diagonal` is the Lean fact ensuring that `Set.diagonal E` is
-- measurable.
/-- Helper for Example 17.55: in the normalized probability convention used by
`totalVariationDistance`, the total variation distance is the infimum, over all couplings of `P`
and `Q`, of the mass assigned to the complement of the diagonal in `E × E`. -/
-- TODO: Combine the proved universal lower bound `couplingOffDiagonal_ge_hahnExcess` with an
-- explicit maximal-coupling witness built from `hahnResidualDecomposition`; the remaining blocker
-- is the residual-product normalization and marginal verification of that witness.
theorem totalVariationDistance_eq_sInf_couplings_offDiagonal
    (P Q : ProbabilityMeasure E) :
    totalVariationDistance P Q =
      sInf {r : ℝ | ∃ π : ProbabilityMeasure (E × E),
        IsCoupling π P Q ∧
          r = ((π : Measure (E × E))
            ((Set.univ : Set (E × E)) \ Set.diagonal E)).toReal} := by
  let S : Set ℝ := {r : ℝ | ∃ π : ProbabilityMeasure (E × E),
    IsCoupling π P Q ∧
      r = ((π : Measure (E × E))
        ((Set.univ : Set (E × E)) \ Set.diagonal E)).toReal}
  rcases exists_isHahnDecomposition (Q : Measure E) (P : Measure E) with ⟨A, hA⟩
  rcases (by
    simpa using
      hahnResidualDecomposition P Q hA.measurableSet hA.le_on hA.ge_on_compl) with
    ⟨_, _, _, _, hExcess_tv, _, _⟩
  have hS_nonempty : S.Nonempty := by
    rcases existsCoupling_offDiagonal_eq_totalVariationDistance P Q with ⟨π, hπ, hπ_offDiag⟩
    exact ⟨totalVariationDistance P Q, by simpa [S] using ⟨π, hπ, hπ_offDiag.symm⟩⟩
  have hS_bddBelow : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨π, hπ, rfl⟩
    exact ENNReal.toReal_nonneg
  change totalVariationDistance P Q = sInf S
  refine le_antisymm ?_ ?_
  · -- Proof comment: every coupling must spend at least the Hahn excess outside the diagonal, so
    -- `totalVariationDistance` is a lower bound for the whole coupling cost set.
    show totalVariationDistance P Q ≤ sInf S
    refine le_csInf hS_nonempty ?_
    intro r hr
    rcases hr with ⟨π, hπ, rfl⟩
    calc
      totalVariationDistance P Q = (P : Measure E).real A - (Q : Measure E).real A := by
        exact hExcess_tv.symm
      _ ≤ ((π : Measure (E × E)) ((Set.univ : Set (E × E)) \ Set.diagonal E)).toReal :=
        couplingOffDiagonal_ge_hahnExcess P Q hA.measurableSet hπ
  · -- Proof comment: the maximal coupling built above is one admissible point of the infimum set
    -- and attains `totalVariationDistance`.
    show sInf S ≤ totalVariationDistance P Q
    rcases existsCoupling_offDiagonal_eq_totalVariationDistance P Q with ⟨π, hπ, hπ_offDiag⟩
    exact csInf_le hS_bddBelow (by simpa [S] using ⟨π, hπ, hπ_offDiag.symm⟩)

/-- Consequence for Example 17.55 (4): in the Lean normalization
`SignedMeasure.totalVariationNorm E
((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure)
= 2 * totalVariationDistance P Q`, the coupling formula (17.29) is the equality between the
source total-variation norm and twice the off-diagonal coupling infimum. The explicit
`[MeasurableEq E]` hypothesis is the Lean side condition ensuring that `Set.diagonal E` is
measurable. -/
theorem sourceTVNorm_eq_sInf_couplings_offDiagonal
    (P Q : ProbabilityMeasure E) :
    SignedMeasure.totalVariationNorm E
        ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) =
      2 * sInf {r : ℝ | ∃ π : ProbabilityMeasure (E × E),
        IsCoupling π P Q ∧
          r = ((π : Measure (E × E))
            ((Set.univ : Set (E × E)) \ Set.diagonal E)).toReal} := by
  -- Proof comment: once the normalized coupling infimum is identified with
  -- `totalVariationDistance`, the source convention is exactly the same factor-`2` rewrite as
  -- in the bounded measurable dual formula.
  rw [sourceTVNorm_eq_two_mul_totalVariationDistance,
    totalVariationDistance_eq_sInf_couplings_offDiagonal]

/-- Helper for Example 17.55: the source total-variation norm is twice the normalized
off-diagonal coupling infimum coming from `totalVariationDistance_eq_sInf_couplings_offDiagonal`.
-/
private theorem sourceTVNorm_eq_two_mul_sInf_couplings_offDiagonal
    (P Q : ProbabilityMeasure E) :
    SignedMeasure.totalVariationNorm E
        ((P : Measure E).toSignedMeasure - (Q : Measure E).toSignedMeasure) =
      2 * sInf {r : ℝ | ∃ π : ProbabilityMeasure (E × E),
        IsCoupling π P Q ∧
          r = ((π : Measure (E × E))
            ((Set.univ : Set (E × E)) \ Set.diagonal E)).toReal} := by
  -- Proof comment: this private helper is exactly the public source-norm coupling formula just
  -- proved above.
  exact sourceTVNorm_eq_sInf_couplings_offDiagonal P Q

end CouplingOffDiagonal

end TotalVariation

end ProbabilityTheory
