/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A nonnegative `L¹(μ)` cutoff function for the tail criterion in Theorem 6.17. -/
structure IntegrableNonnegativeCutoff where
  toLp : Lp ℝ 1 μ
  ae_nonneg : 0 ≤ᵐ[μ] (toLp : Ω → ℝ)

instance : CoeFun (@IntegrableNonnegativeCutoff Ω _ μ) (fun _ ↦ Ω → ℝ) where
  coe g := g.toLp

-- `lean_leansearch` confirms the relevant mathlib owners `UniformIntegrable`/`UnifIntegrable`.
-- The source integrable-cutoff characterization in Theorem 6.17 matches the full owner
-- `UniformIntegrable`; the small-set-only owner `UnifIntegrable` remains available for later
-- bridge results when only the small-set clause is intended.
/-- The source-side integrable-cutoff excess criterion `(6.2)` used in Theorem 6.17. -/
def HasIntegrableCutoffExcessCriterion (F : Set (Lp ℝ 1 μ)) : Prop :=
  sInf (Set.range fun g : @IntegrableNonnegativeCutoff Ω _ μ ↦
    iSup fun f : F ↦ ∫⁻ x, ENNReal.ofReal (max (|f.1 x| - g x) 0) ∂μ) = 0

/-- The source-side integrable-cutoff tail criterion `(6.3)` from Theorem 6.17. -/
def HasIntegrableCutoffTailCriterion (F : Set (Lp ℝ 1 μ)) : Prop :=
  sInf (Set.range fun g : @IntegrableNonnegativeCutoff Ω _ μ ↦
    iSup fun f : F ↦ ∫⁻ x in {x | g x < |f.1 x|}, ENNReal.ofReal |f.1 x| ∂μ) = 0

/-- The finite-measure constant-cutoff excess criterion from Theorem 6.17(i). -/
def HasConstantCutoffExcessCriterion (F : Set (Lp ℝ 1 μ)) : Prop :=
  sInf (Set.range fun a : ℝ≥0 ↦
    iSup fun f : F ↦ ∫⁻ x, ENNReal.ofReal (max (|f.1 x| - (a : ℝ)) 0) ∂μ) = 0

/-- The finite-measure constant-cutoff tail criterion from Theorem 6.17(ii). -/
def HasConstantCutoffTailCriterion (F : Set (Lp ℝ 1 μ)) : Prop :=
  sInf (Set.range fun a : ℝ≥0 ↦
    iSup fun f : F ↦ ∫⁻ x in {x | (a : ℝ) < |f.1 x|}, ENNReal.ofReal |f.1 x| ∂μ) = 0

/-- Helper for Theorem 6.17: a vanishing `sInf` over `ℝ≥0∞` is equivalent to the usual
`ε`-formulation. -/
lemma sInfRange_eq_zero_iff_forall_epsilon {κ : Type*} (Φ : κ → ℝ≥0∞) :
    sInf (Set.range Φ) = 0 ↔ ∀ ε : ℝ, 0 < ε → ∃ k, Φ k < ENNReal.ofReal ε := by
  change sInf (Set.range Φ) = ⊥ ↔ ∀ ε : ℝ, 0 < ε → ∃ k, Φ k < ENNReal.ofReal ε
  rw [sInf_eq_bot]
  constructor
  · intro h ε hε
    obtain ⟨a, ha, ha_lt⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
    rcases ha with ⟨k, rfl⟩
    exact ⟨k, ha_lt⟩
  · intro h η hη
    by_cases hη_top : η = ⊤
    · obtain ⟨k, hk⟩ := h 1 zero_lt_one
      refine ⟨Φ k, ⟨k, rfl⟩, ?_⟩
      simpa [hη_top] using (lt_of_lt_of_le hk le_top)
    · have hη_real : 0 < η.toReal := ENNReal.toReal_pos (ne_of_gt hη) hη_top
      obtain ⟨k, hk⟩ := h η.toReal hη_real
      refine ⟨Φ k, ⟨k, rfl⟩, ?_⟩
      simpa [ENNReal.ofReal_toReal hη_top] using hk

/-- Helper for Theorem 6.17: in `L¹`, the indicator seminorm is the corresponding restricted
tail integral. -/
lemma eLpNorm_indicator_one_eq_setLIntegral_abs (f : Ω → ℝ) {s : Set Ω} (hs : MeasurableSet s) :
    eLpNorm (s.indicator f) 1 μ = ∫⁻ x in s, ENNReal.ofReal |f x| ∂μ := by
  -- Convert the `L¹` seminorm into the restricted `lintegral` of `|f|`.
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [MeasureTheory.lintegral_indicator hs]
  refine lintegral_congr_ae ?_
  filter_upwards with x
  simp [Real.enorm_eq_ofReal_abs]

/-- Helper for Theorem 6.17: rewrite a real-valued tail indicator in the canonical ENNReal
normal form used by `lintegral`. -/
lemma tailIndicatorOfReal_eq (s : Set Ω) (h : Ω → ℝ) :
    s.indicator (fun x ↦ ENNReal.ofReal |h x|) =
      fun x ↦ ENNReal.ofReal (s.indicator (fun x ↦ |h x|) x) := by
  -- Compare both sides pointwise by splitting on membership in the tail set.
  ext x
  by_cases hx : x ∈ s
  · simp [hx]
  · simp [hx]

/-- Helper for Theorem 6.17: a nonnegative cutoff controls the corresponding positive-part excess
by the strict tail integrand. -/
private lemma max_abs_sub_le_strictTail (a y : ℝ) (ha : 0 ≤ a) :
    max (|y| - a) 0 ≤ Set.indicator {t : ℝ | a < |t|} (fun t ↦ |t|) y := by
  -- Split on the strict-tail membership and simplify the indicator on each side.
  by_cases hy : a < |y|
  · simpa [hy] using (max_le (sub_le_self _ ha) (abs_nonneg y))
  · simpa [hy] using (max_le (sub_nonpos.mpr (le_of_not_gt hy)) le_rfl)

/-- Helper for Theorem 6.17: the `2a`-tail is bounded by twice the positive-part excess. -/
private lemma strictTail_le_two_mul_max_abs_sub (a y : ℝ) :
    Set.indicator {t : ℝ | 2 * a < |t|} (fun t ↦ |t|) y ≤ 2 * max (|y| - a) 0 := by
  -- Split on the `2a`-tail. On the tail the positive part is `|y| - a`; otherwise the left side
  -- vanishes.
  by_cases hy : 2 * a < |y|
  · have hy' : Set.indicator {t : ℝ | 2 * a < |t|} (fun t ↦ |t|) y = |y| := by
      simp [hy]
    rw [hy']
    have ha_le : a ≤ |y| := by
      by_cases ha : 0 ≤ a
      · linarith
      · linarith [abs_nonneg y]
    have hsub : 0 ≤ |y| - a := sub_nonneg.mpr ha_le
    rw [max_eq_left hsub]
    linarith
  · simpa [hy] using (show (0 : ℝ) ≤ 2 * max (|y| - a) 0 by positivity)

/-- Helper for Theorem 6.17: doubling a cutoff preserves almost-everywhere nonnegativity. -/
private lemma doubleCutoff_aeNonneg (g : @IntegrableNonnegativeCutoff Ω _ μ) :
    0 ≤ᵐ[μ] ((((2 : ℝ) • g.toLp : Lp ℝ 1 μ) : Ω → ℝ)) := by
  -- Rewrite the doubled cutoff pointwise and keep the original nonnegativity witness.
  filter_upwards [g.ae_nonneg, Lp.coeFn_smul (2 : ℝ) g.toLp] with x hx hsmul
  rw [hsmul]
  exact mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hx

/-- Helper for Theorem 6.17: doubling a cutoff produces another admissible integrable cutoff. -/
private def doubleCutoff (g : @IntegrableNonnegativeCutoff Ω _ μ) :
    @IntegrableNonnegativeCutoff Ω _ μ :=
  { toLp := (2 : ℝ) • g.toLp
    ae_nonneg := doubleCutoff_aeNonneg g }

/-- Helper for Theorem 6.17: the doubled cutoff agrees almost everywhere with the pointwise
doubling of the original cutoff. -/
private lemma doubleCutoff_coe_ae_eq (g : @IntegrableNonnegativeCutoff Ω _ μ) :
    (doubleCutoff g : Ω → ℝ) =ᵐ[μ] fun x ↦ 2 * g x := by
  simpa [doubleCutoff] using (Lp.coeFn_smul (2 : ℝ) g.toLp)

/-- Helper for Theorem 6.17: the finite-measure owner criterion from mathlib is equivalent to the
source constant-tail criterion. -/
lemma uniformIntegrable_iff_constantCutoffTailCriterionAux [IsFiniteMeasure μ]
    (F : Set (Lp ℝ 1 μ)) :
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ ↔
      @HasConstantCutoffTailCriterion Ω _ μ F := by
  constructor
  · intro hUI
    rw [HasConstantCutoffTailCriterion, sInfRange_eq_zero_iff_forall_epsilon]
    rw [MeasureTheory.uniformIntegrable_iff le_rfl ENNReal.one_ne_top] at hUI
    -- The owner theorem gives small non-strict tails; strict tails are smaller.
    intro ε hε
    obtain ⟨C, hC⟩ := hUI.2 (ε / 2) (half_pos hε)
    refine ⟨C, ?_⟩
    have hbound :
        iSup (fun f : F ↦
          ∫⁻ x in {x | ((C : ℝ) < |(f.1 : Ω → ℝ) x|)}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) ≤
          ENNReal.ofReal (ε / 2) := by
      refine iSup_le fun f ↦ ?_
      have hs :
          MeasurableSet {x | ((C : ℝ) < |(f.1 : Ω → ℝ) x|)} :=
        measurableSet_lt measurable_const (Lp.stronglyMeasurable f.1).norm.measurable
      calc
        ∫⁻ x in {x | ((C : ℝ) < |(f.1 : Ω → ℝ) x|)}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ
            = eLpNorm ({x | ((C : ℝ) < |(f.1 : Ω → ℝ) x|)}.indicator ((f.1 : Ω → ℝ))) 1 μ := by
                rw [eLpNorm_indicator_one_eq_setLIntegral_abs _ hs]
        _ ≤ eLpNorm ({x | C ≤ ‖(f.1 : Ω → ℝ) x‖₊}.indicator ((f.1 : Ω → ℝ))) 1 μ := by
              refine eLpNorm_mono fun x ↦ ?_
              by_cases hx : (C : ℝ) < |(f.1 : Ω → ℝ) x|
              · have hx' : C ≤ ‖(f.1 : Ω → ℝ) x‖₊ := by
                  simpa using le_of_lt hx
                simp [hx, hx']
              · simp [hx]
        _ ≤ ENNReal.ofReal (ε / 2) := hC f
    exact lt_of_le_of_lt hbound <| (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  · intro hTail
    rw [HasConstantCutoffTailCriterion, sInfRange_eq_zero_iff_forall_epsilon] at hTail
    rw [MeasureTheory.uniformIntegrable_iff le_rfl ENNReal.one_ne_top]
    refine ⟨fun f ↦ (Lp.stronglyMeasurable f.1).aestronglyMeasurable, ?_⟩
    -- Shift the strict cutoff by `1` to recover the owner non-strict threshold set.
    intro ε hε
    obtain ⟨a, ha⟩ := hTail ε hε
    refine ⟨a + 1, fun f ↦ ?_⟩
    have hs :
        MeasurableSet {x | ((a : ℝ) < |(f.1 : Ω → ℝ) x|)} :=
      measurableSet_lt measurable_const (Lp.stronglyMeasurable f.1).norm.measurable
    calc
      eLpNorm ({x | a + 1 ≤ ‖(f.1 : Ω → ℝ) x‖₊}.indicator ((f.1 : Ω → ℝ))) 1 μ
          ≤ eLpNorm ({x | ((a : ℝ) < |(f.1 : Ω → ℝ) x|)}.indicator ((f.1 : Ω → ℝ))) 1 μ := by
              refine eLpNorm_mono fun x ↦ ?_
              by_cases hx : a + 1 ≤ ‖(f.1 : Ω → ℝ) x‖₊
              · have hx' : (a : ℝ) < |(f.1 : Ω → ℝ) x| := by
                  have hx'' : ((a : ℝ) + 1) ≤ |(f.1 : Ω → ℝ) x| := by
                    simpa using hx
                  linarith
                simp [hx, hx']
              · simp [hx]
      _ = ∫⁻ x in {x | ((a : ℝ) < |(f.1 : Ω → ℝ) x|)}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ := by
            rw [eLpNorm_indicator_one_eq_setLIntegral_abs _ hs]
      _ ≤ iSup (fun f : F ↦
            ∫⁻ x in {x | ((a : ℝ) < |(f.1 : Ω → ℝ) x|)}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) := by
            exact le_iSup (fun f : F ↦
              ∫⁻ x in {x | ((a : ℝ) < |(f.1 : Ω → ℝ) x|)}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) f
      _ ≤ ENNReal.ofReal ε := ha.le

/-- Helper for Theorem 6.17: the two constant-cutoff formulations are equivalent by direct
pointwise comparison. -/
lemma constantCutoffExcessCriterion_iff_constantCutoffTailCriterionAux [IsFiniteMeasure μ]
    (F : Set (Lp ℝ 1 μ)) :
    @HasConstantCutoffExcessCriterion Ω _ μ F ↔
      @HasConstantCutoffTailCriterion Ω _ μ F := by
  -- Normalize both criteria into their `ε`-forms and compare the pointwise integrands.
  rw [HasConstantCutoffExcessCriterion, HasConstantCutoffTailCriterion,
    sInfRange_eq_zero_iff_forall_epsilon, sInfRange_eq_zero_iff_forall_epsilon]
  constructor
  · intro hExcess ε hε
    obtain ⟨a, ha⟩ := hExcess (ε / 4) (by positivity)
    refine ⟨2 * a, ?_⟩
    have hbound :
        iSup (fun f : F ↦
          ∫⁻ x in {x | ((2 * a : ℝ≥0) : ℝ) < |(f.1 : Ω → ℝ) x|},
            ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) ≤
          (2 : ℝ≥0∞) * iSup (fun f : F ↦
            ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) ∂μ) := by
      refine iSup_le fun f ↦ ?_
      have hs :
          MeasurableSet {x | ((2 * a : ℝ≥0) : ℝ) < |(f.1 : Ω → ℝ) x|} :=
        measurableSet_lt measurable_const (Lp.stronglyMeasurable f.1).norm.measurable
      calc
        ∫⁻ x in {x | ((2 * a : ℝ≥0) : ℝ) < |(f.1 : Ω → ℝ) x|},
            ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ
            = ∫⁻ x,
                Set.indicator {x | ((2 * a : ℝ≥0) : ℝ) < |(f.1 : Ω → ℝ) x|}
                  (fun x ↦ ENNReal.ofReal |(f.1 : Ω → ℝ) x|) x ∂μ := by
                rw [← MeasureTheory.lintegral_indicator hs]
        _ ≤ ∫⁻ x, (2 : ℝ≥0∞) * ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) ∂μ := by
              refine lintegral_mono fun x ↦ ?_
              have hmax_nonneg : 0 ≤ max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0 := le_max_right _ _
              calc
                Set.indicator {x | ((2 * a : ℝ≥0) : ℝ) < |(f.1 : Ω → ℝ) x|}
                    (fun x ↦ ENNReal.ofReal |(f.1 : Ω → ℝ) x|) x
                    = ENNReal.ofReal
                        (Set.indicator {x | ((2 * a : ℝ≥0) : ℝ) < |(f.1 : Ω → ℝ) x|}
                          (fun x ↦ |(f.1 : Ω → ℝ) x|) x) := by
                        rw [tailIndicatorOfReal_eq]
                _ ≤ ENNReal.ofReal (2 * max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) := by
                      exact ENNReal.ofReal_le_ofReal
                        (strictTail_le_two_mul_max_abs_sub (a : ℝ) ((f.1 : Ω → ℝ) x))
                _ = (2 : ℝ≥0∞) * ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) := by
                      simpa [hmax_nonneg] using
                        (show ENNReal.ofReal (2 * max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) =
                          (2 : ℝ≥0∞) * ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) by
                            rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
                              ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)])
        _ = (2 : ℝ≥0∞) *
              ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) ∂μ := by
              rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num)]
        _ ≤ (2 : ℝ≥0∞) * iSup (fun f : F ↦
              ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) ∂μ) := by
              gcongr
              exact le_iSup (fun f : F ↦
                ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) ∂μ) f
    have hhalf :
        (2 : ℝ≥0∞) * iSup (fun f : F ↦
          ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) ∂μ) ≤
          ENNReal.ofReal (ε / 2) := by
      calc
        (2 : ℝ≥0∞) * iSup (fun f : F ↦
            ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) ∂μ)
            ≤ (2 : ℝ≥0∞) * ENNReal.ofReal (ε / 4) := by
              exact mul_le_mul_left' ha.le (2 : ℝ≥0∞)
        _ = ENNReal.ofReal (ε / 2) := by
              simpa using
                (show (2 : ℝ≥0∞) * ENNReal.ofReal (ε / 4) = ENNReal.ofReal (ε / 2) by
                  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
                    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
                  congr 1
                  ring)
    exact lt_of_le_of_lt hbound <|
      lt_of_le_of_lt hhalf ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))
  · intro hTail ε hε
    obtain ⟨a, ha⟩ := hTail ε hε
    refine ⟨a, ?_⟩
    refine lt_of_le_of_lt ?_ ha
    refine iSup_le fun f ↦ ?_
    have hs :
        MeasurableSet {x | (a : ℝ) < |(f.1 : Ω → ℝ) x|} :=
      measurableSet_lt measurable_const (Lp.stronglyMeasurable f.1).norm.measurable
    calc
      ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - (a : ℝ)) 0) ∂μ
          ≤ ∫⁻ x,
              Set.indicator {x | (a : ℝ) < |(f.1 : Ω → ℝ) x|}
                (fun x ↦ ENNReal.ofReal |(f.1 : Ω → ℝ) x|) x ∂μ := by
              refine lintegral_mono fun x ↦ ?_
              rw [tailIndicatorOfReal_eq]
              exact ENNReal.ofReal_le_ofReal <|
                max_abs_sub_le_strictTail (a : ℝ) ((f.1 : Ω → ℝ) x) (by exact_mod_cast a.2)
      _ = ∫⁻ x in {x | (a : ℝ) < |(f.1 : Ω → ℝ) x|},
            ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ := by
            rw [MeasureTheory.lintegral_indicator hs]
      _ ≤ iSup (fun f : F ↦
            ∫⁻ x in {x | (a : ℝ) < |(f.1 : Ω → ℝ) x|},
              ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) := by
            exact le_iSup (fun f : F ↦
              ∫⁻ x in {x | (a : ℝ) < |(f.1 : Ω → ℝ) x|},
                ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) f

/-- Helper for Theorem 6.17: the source `2g` argument upgrades the excess-cutoff criterion to the
tail-cutoff criterion. -/
lemma integrableCutoffTailCriterion_of_excessCriterion (F : Set (Lp ℝ 1 μ)) :
    @HasIntegrableCutoffExcessCriterion Ω _ μ F →
      @HasIntegrableCutoffTailCriterion Ω _ μ F := by
  intro hExcess
  -- Normalize the excess criterion into `ε`-form and reuse the same `2a` comparison pointwise.
  change
    sInf (Set.range fun g : @IntegrableNonnegativeCutoff Ω _ μ ↦
      iSup fun f : F ↦ ∫⁻ x, ENNReal.ofReal (max (|f.1 x| - g x) 0) ∂μ) = 0 at hExcess
  change
    sInf (Set.range fun g : @IntegrableNonnegativeCutoff Ω _ μ ↦
      iSup fun f : F ↦ ∫⁻ x in {x | g x < |f.1 x|}, ENNReal.ofReal |f.1 x| ∂μ) = 0
  rw [sInfRange_eq_zero_iff_forall_epsilon] at hExcess ⊢
  intro ε hε
  obtain ⟨g, hg⟩ := hExcess (ε / 4) (by positivity)
  refine ⟨doubleCutoff g, ?_⟩
  have hbound :
      iSup (fun f : F ↦
        ∫⁻ x in {x | doubleCutoff g x < |(f.1 : Ω → ℝ) x|},
          ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) ≤
        (2 : ℝ≥0∞) * iSup (fun f : F ↦
          ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ) := by
    refine iSup_le fun f ↦ ?_
    have hs :
        MeasurableSet {x | doubleCutoff g x < |(f.1 : Ω → ℝ) x|} :=
      measurableSet_lt (Lp.stronglyMeasurable (doubleCutoff g).toLp).measurable
        (Lp.stronglyMeasurable f.1).norm.measurable
    have hdouble := doubleCutoff_coe_ae_eq g
    calc
      ∫⁻ x in {x | doubleCutoff g x < |(f.1 : Ω → ℝ) x|},
          ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ
          = ∫⁻ x,
              Set.indicator {x | doubleCutoff g x < |(f.1 : Ω → ℝ) x|}
                (fun x ↦ ENNReal.ofReal |(f.1 : Ω → ℝ) x|) x ∂μ := by
              rw [← MeasureTheory.lintegral_indicator hs]
      _ = ∫⁻ x,
            Set.indicator {x | 2 * g x < |(f.1 : Ω → ℝ) x|}
              (fun x ↦ ENNReal.ofReal |(f.1 : Ω → ℝ) x|) x ∂μ := by
            refine lintegral_congr_ae ?_
            filter_upwards [hdouble] with x hx
            by_cases htail : 2 * g x < |(f.1 : Ω → ℝ) x|
            · have htail' : doubleCutoff g x < |(f.1 : Ω → ℝ) x| := by simpa [hx] using htail
              simp [htail, htail']
            · have htail' : ¬ doubleCutoff g x < |(f.1 : Ω → ℝ) x| := by simpa [hx] using htail
              simp [htail, htail']
      _ ≤ ∫⁻ x, (2 : ℝ≥0∞) * ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ := by
            refine lintegral_mono fun x ↦ ?_
            have hmax_nonneg : 0 ≤ max (|(f.1 : Ω → ℝ) x| - g x) 0 := le_max_right _ _
            have hreal :=
              strictTail_le_two_mul_max_abs_sub (g x) ((f.1 : Ω → ℝ) x)
            calc
              Set.indicator {x | 2 * g x < |(f.1 : Ω → ℝ) x|}
                  (fun x ↦ ENNReal.ofReal |(f.1 : Ω → ℝ) x|) x
                  = ENNReal.ofReal
                      (Set.indicator {x | 2 * g x < |(f.1 : Ω → ℝ) x|}
                        (fun x ↦ |(f.1 : Ω → ℝ) x|) x) := by
                      rw [tailIndicatorOfReal_eq]
              _ ≤ ENNReal.ofReal (2 * max (|(f.1 : Ω → ℝ) x| - g x) 0) := by
                    exact ENNReal.ofReal_le_ofReal hreal
              _ = (2 : ℝ≥0∞) * ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) := by
                    simpa [hmax_nonneg] using
                      (show ENNReal.ofReal (2 * max (|(f.1 : Ω → ℝ) x| - g x) 0) =
                        (2 : ℝ≥0∞) * ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) by
                          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
                            ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)])
      _ = (2 : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ := by
            rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num)]
      _ ≤ (2 : ℝ≥0∞) * iSup (fun f : F ↦
            ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ) := by
            gcongr
            exact le_iSup (fun f : F ↦
              ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ) f
  have hhalf :
      (2 : ℝ≥0∞) * iSup (fun f : F ↦
        ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ) ≤
        ENNReal.ofReal (ε / 2) := by
    calc
      (2 : ℝ≥0∞) * iSup (fun f : F ↦
          ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ)
          ≤ (2 : ℝ≥0∞) * ENNReal.ofReal (ε / 4) := by
            exact mul_le_mul_left' hg.le (2 : ℝ≥0∞)
      _ = ENNReal.ofReal (ε / 2) := by
            simpa using
              (show (2 : ℝ≥0∞) * ENNReal.ofReal (ε / 4) = ENNReal.ofReal (ε / 2) by
                rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
                  ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
                congr 1
                ring)
  exact lt_of_le_of_lt hbound <|
    lt_of_le_of_lt hhalf ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith))

/-- Helper for Theorem 6.17: the source tail criterion `(6.3)` implies the source excess
criterion `(6.2)` by the pointwise bound
`(|f| - g)^+ ≤ |f| * 𝟙_{ {g < |f|} }`. -/
lemma integrableCutoffExcessCriterion_of_tailCriterion (F : Set (Lp ℝ 1 μ)) :
    @HasIntegrableCutoffTailCriterion Ω _ μ F →
      @HasIntegrableCutoffExcessCriterion Ω _ μ F := by
  intro hTail
  rw [HasIntegrableCutoffTailCriterion] at hTail
  rw [HasIntegrableCutoffExcessCriterion]
  rw [sInfRange_eq_zero_iff_forall_epsilon] at hTail ⊢
  intro ε hε
  obtain ⟨g, hg⟩ := hTail ε hε
  refine ⟨g, ?_⟩
  refine lt_of_le_of_lt ?_ hg
  refine iSup_le fun f ↦ ?_
  have hs :
      MeasurableSet {x | g x < |(f.1 : Ω → ℝ) x|} :=
    measurableSet_lt (Lp.stronglyMeasurable g.toLp).measurable
      (Lp.stronglyMeasurable f.1).norm.measurable
  calc
    ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ
        ≤ ∫⁻ x,
            Set.indicator {x | g x < |(f.1 : Ω → ℝ) x|}
              (fun x ↦ ENNReal.ofReal |(f.1 : Ω → ℝ) x|) x ∂μ := by
            refine lintegral_mono_ae ?_
            filter_upwards [g.ae_nonneg] with x hx
            rw [tailIndicatorOfReal_eq]
            exact ENNReal.ofReal_le_ofReal <|
              max_abs_sub_le_strictTail (g x) ((f.1 : Ω → ℝ) x) hx
    _ = ∫⁻ x in {x | g x < |(f.1 : Ω → ℝ) x|},
          ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ := by
          rw [MeasureTheory.lintegral_indicator hs]
    _ ≤ iSup (fun f : F ↦
          ∫⁻ x in {x | g x < |(f.1 : Ω → ℝ) x|},
            ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) := by
          exact le_iSup (fun f : F ↦
            ∫⁻ x in {x | g x < |(f.1 : Ω → ℝ) x|},
              ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) f

/-- Helper for Theorem 6.17: one integrable cutoff controls both the small-set and boundedness
parts of uniform integrability. -/
lemma uniformIntegrable_of_integrableCutoffTailCriterion (F : Set (Lp ℝ 1 μ)) :
    @HasIntegrableCutoffTailCriterion Ω _ μ F →
      UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ := by
  intro hTail
  -- Route correction: derive uniform integrability directly from a bounded-plus-tail
  -- decomposition instead of routing through the excess criterion again.
  rw [HasIntegrableCutoffTailCriterion, sInfRange_eq_zero_iff_forall_epsilon] at hTail
  obtain ⟨gBound, hgBound⟩ := hTail 1 zero_lt_one
  refine ⟨fun f ↦ (Lp.stronglyMeasurable f.1).aestronglyMeasurable, ?_, ?_⟩
  · -- Use one cutoff for the small-set estimate and split each function into tail and bounded
    -- pieces on that cutoff.
    intro ε hε
    obtain ⟨gSmall, hgSmall⟩ := hTail (ε / 2) (half_pos hε)
    obtain ⟨δ, hδpos, hδ⟩ :=
      MeasureTheory.Lp.memLp gSmall.toLp |>.eLpNorm_indicator_le le_rfl ENNReal.one_ne_top
        (half_pos hε)
    refine ⟨δ, hδpos, fun f s hs hμs ↦ ?_⟩
    let tailSet : Set Ω := {x | gSmall x < |(f.1 : Ω → ℝ) x|}
    have htailSet_meas : MeasurableSet tailSet :=
      measurableSet_lt (Lp.stronglyMeasurable gSmall.toLp).measurable
        (Lp.stronglyMeasurable f.1).norm.measurable
    have hTailPieceMeas :
        AEStronglyMeasurable (s.indicator (tailSet.indicator ((f.1 : Ω → ℝ)))) μ :=
      (((Lp.stronglyMeasurable f.1).indicator htailSet_meas).indicator hs).aestronglyMeasurable
    have hBoundedPieceMeas :
        AEStronglyMeasurable (s.indicator (tailSetᶜ.indicator ((f.1 : Ω → ℝ)))) μ :=
      (((Lp.stronglyMeasurable f.1).indicator htailSet_meas.compl).indicator hs).aestronglyMeasurable
    have hsplit :
        s.indicator ((f.1 : Ω → ℝ)) =
          s.indicator (tailSet.indicator ((f.1 : Ω → ℝ))) +
            s.indicator (tailSetᶜ.indicator ((f.1 : Ω → ℝ))) := by
      -- Split the restriction into the tail piece and its complement.
      ext x
      by_cases hx : x ∈ s
      · by_cases htail : x ∈ tailSet
        · simp [tailSet, hx, htail]
        · simp [tailSet, hx, htail]
      · simp [hx]
    have hεSplit :
        ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    calc
      eLpNorm (s.indicator ((f.1 : Ω → ℝ))) 1 μ
          ≤ eLpNorm (s.indicator (tailSet.indicator ((f.1 : Ω → ℝ)))) 1 μ +
              eLpNorm (s.indicator (tailSetᶜ.indicator ((f.1 : Ω → ℝ)))) 1 μ := by
              rw [hsplit]
              exact eLpNorm_add_le hTailPieceMeas hBoundedPieceMeas le_rfl
      _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
            refine add_le_add ?_ ?_
            · -- The restricted tail piece is controlled by the tail criterion itself.
              refine le_trans (eLpNorm_indicator_le _) ?_
              calc
                eLpNorm (tailSet.indicator ((f.1 : Ω → ℝ))) 1 μ
                    = ∫⁻ x in tailSet, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ := by
                        rw [eLpNorm_indicator_one_eq_setLIntegral_abs _ htailSet_meas]
                _ ≤ iSup (fun f : F ↦
                      ∫⁻ x in {x | gSmall x < |(f.1 : Ω → ℝ) x|},
                        ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) := by
                      exact le_iSup (fun f : F ↦
                        ∫⁻ x in {x | gSmall x < |(f.1 : Ω → ℝ) x|},
                          ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) f
                _ ≤ ENNReal.ofReal (ε / 2) := hgSmall.le
            · -- On the complement of the tail set, `|f|` is dominated by the chosen cutoff.
              refine le_trans (eLpNorm_mono fun x ↦ ?_) (hδ s hs hμs)
              by_cases hx : x ∈ s
              · by_cases htail : x ∈ tailSet
                · simp [tailSet, hx, htail]
                · have hle : |(f.1 : Ω → ℝ) x| ≤ gSmall x := le_of_not_gt htail
                  have hnonneg : 0 ≤ gSmall x := by
                    by_contra hneg
                    have : gSmall x < |(f.1 : Ω → ℝ) x| := by
                      have habs_nonneg : 0 ≤ |(f.1 : Ω → ℝ) x| := abs_nonneg _
                      linarith
                    exact htail this
                  simp [tailSet, hx, htail, abs_of_nonneg hnonneg, hle]
              · simp [hx]
      _ ≤ ENNReal.ofReal ε := by
            rw [hεSplit]
  · -- A second cutoff at `ε = 1` provides the global `L¹` bound needed by
    -- `UniformIntegrable`.
    refine ⟨(eLpNorm (gBound : Ω → ℝ) 1 μ).toNNReal + 1, fun f ↦ ?_⟩
    let tailSet : Set Ω := {x | gBound x < |(f.1 : Ω → ℝ) x|}
    have htailSet_meas : MeasurableSet tailSet :=
      measurableSet_lt (Lp.stronglyMeasurable gBound.toLp).measurable
        (Lp.stronglyMeasurable f.1).norm.measurable
    have hTailMeas :
        AEStronglyMeasurable (tailSet.indicator ((f.1 : Ω → ℝ))) μ :=
      ((Lp.stronglyMeasurable f.1).indicator htailSet_meas).aestronglyMeasurable
    have hBoundedMeas :
        AEStronglyMeasurable (tailSetᶜ.indicator ((f.1 : Ω → ℝ))) μ :=
      ((Lp.stronglyMeasurable f.1).indicator htailSet_meas.compl).aestronglyMeasurable
    have hsplit :
        (f.1 : Ω → ℝ) =
          tailSet.indicator ((f.1 : Ω → ℝ)) + tailSetᶜ.indicator ((f.1 : Ω → ℝ)) := by
      -- Split the full function into its tail and bounded pieces.
      ext x
      by_cases htail : x ∈ tailSet
      · simp [tailSet, htail]
      · simp [tailSet, htail]
    have hBoundedTarget :
        ENNReal.ofReal 1 + eLpNorm (gBound : Ω → ℝ) 1 μ ≤
          ↑((eLpNorm (gBound : Ω → ℝ) 1 μ).toNNReal + 1 : ℝ≥0) := by
      have hcoe :
          ↑((eLpNorm (gBound : Ω → ℝ) 1 μ).toNNReal + 1 : ℝ≥0) =
            eLpNorm (gBound : Ω → ℝ) 1 μ + 1 := by
        simp [NNReal.coe_add]
        exact ENNReal.coe_toNNReal (MeasureTheory.Lp.eLpNorm_ne_top gBound.toLp)
      rw [hcoe]
      simpa [add_comm] using
        (le_rfl : ENNReal.ofReal 1 + eLpNorm (gBound : Ω → ℝ) 1 μ ≤
          ENNReal.ofReal 1 + eLpNorm (gBound : Ω → ℝ) 1 μ)
    calc
      eLpNorm ((f.1 : Ω → ℝ)) 1 μ
          ≤ eLpNorm (tailSet.indicator ((f.1 : Ω → ℝ))) 1 μ +
              eLpNorm (tailSetᶜ.indicator ((f.1 : Ω → ℝ))) 1 μ := by
              nth_rewrite 1 [hsplit]
              exact eLpNorm_add_le hTailMeas hBoundedMeas le_rfl
      _ ≤ ENNReal.ofReal 1 + eLpNorm (gBound : Ω → ℝ) 1 μ := by
            refine add_le_add ?_ ?_
            · -- The tail contribution is uniformly bounded by the witness at `ε = 1`.
              calc
                eLpNorm (tailSet.indicator ((f.1 : Ω → ℝ))) 1 μ
                    = ∫⁻ x in tailSet, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ := by
                        rw [eLpNorm_indicator_one_eq_setLIntegral_abs _ htailSet_meas]
                _ ≤ iSup (fun f : F ↦
                      ∫⁻ x in {x | gBound x < |(f.1 : Ω → ℝ) x|},
                        ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) := by
                      exact le_iSup (fun f : F ↦
                        ∫⁻ x in {x | gBound x < |(f.1 : Ω → ℝ) x|},
                          ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) f
                _ ≤ ENNReal.ofReal 1 := hgBound.le
            · -- Outside the tail set the function is pointwise dominated by the cutoff.
              refine eLpNorm_mono fun x ↦ ?_
              by_cases htail : x ∈ tailSet
              · simp [tailSet, htail]
              · have hle : |(f.1 : Ω → ℝ) x| ≤ gBound x := le_of_not_gt htail
                have hnonneg : 0 ≤ gBound x := by
                  by_contra hneg
                  have : gBound x < |(f.1 : Ω → ℝ) x| := by
                    have habs_nonneg : 0 ≤ |(f.1 : Ω → ℝ) x| := abs_nonneg _
                    linarith
                  exact htail this
                simp [tailSet, htail, abs_of_nonneg hnonneg, hle]
      _ ≤ ↑((eLpNorm (gBound : Ω → ℝ) 1 μ).toNNReal + 1 : ℝ≥0) := by
            exact hBoundedTarget

/-- Helper for Theorem 6.17: on a finite measure space, a nonnegative constant is almost
everywhere nonnegative as a cutoff function. -/
private lemma constantCutoff_aeNonneg [IsFiniteMeasure μ] (a : ℝ≥0) :
    0 ≤ᵐ[μ] fun _ : Ω ↦ (a : ℝ) := by
  -- The constant representative is pointwise nonnegative.
  filter_upwards with x
  exact_mod_cast a.2

/-- Helper for Theorem 6.17: on a finite measure space, a nonnegative constant defines an
admissible integrable cutoff. -/
private lemma constantCutoff_toLp_aeNonneg [IsFiniteMeasure μ] (a : ℝ≥0) :
    0 ≤ᵐ[μ]
      ((MeasureTheory.MemLp.toLp (fun _ : Ω ↦ (a : ℝ))
        (MeasureTheory.memLp_const (p := 1) (μ := μ) (a : ℝ))) : Ω → ℝ) := by
  -- Compare the `Lp` constant representative with the underlying pointwise constant function.
  filter_upwards
      [MeasureTheory.MemLp.coeFn_toLp
        (f := fun _ : Ω ↦ (a : ℝ))
        (μ := μ)
        (p := 1)
        (MeasureTheory.memLp_const (p := 1) (μ := μ) (a : ℝ))] with x hx
  rw [hx]
  exact_mod_cast a.2

/-- Helper for Theorem 6.17: on a finite measure space, a nonnegative constant defines an
admissible integrable cutoff. -/
private def constantCutoff [IsFiniteMeasure μ] (a : ℝ≥0) :
    @IntegrableNonnegativeCutoff Ω _ μ :=
  { toLp := MeasureTheory.MemLp.toLp (fun _ : Ω ↦ (a : ℝ))
      (MeasureTheory.memLp_const (p := 1) (μ := μ) (a : ℝ))
    ae_nonneg := constantCutoff_toLp_aeNonneg a }

/-- Helper for Theorem 6.17: on a finite measure space, the constant-cutoff excess criterion is a
special case of the integrable-cutoff excess criterion. -/
private lemma integrableCutoffExcessCriterion_of_constantCutoffExcessCriterion
    [IsFiniteMeasure μ] (F : Set (Lp ℝ 1 μ)) :
    @HasConstantCutoffExcessCriterion Ω _ μ F →
      @HasIntegrableCutoffExcessCriterion Ω _ μ F := by
  intro hConst
  -- Normalize both criteria into `ε`-form and insert the finite-measure constant as a cutoff.
  rw [HasConstantCutoffExcessCriterion, sInfRange_eq_zero_iff_forall_epsilon] at hConst
  rw [HasIntegrableCutoffExcessCriterion, sInfRange_eq_zero_iff_forall_epsilon]
  intro ε hε
  obtain ⟨a, ha⟩ := hConst ε hε
  refine ⟨constantCutoff a, ?_⟩
  have hconst :
      (((constantCutoff a).toLp : Lp ℝ 1 μ) : Ω → ℝ) =ᵐ[μ] fun _ : Ω ↦ (a : ℝ) := by
    -- The `Lp` constant cutoff agrees almost everywhere with its pointwise representative.
    simpa [constantCutoff] using
      (MeasureTheory.MemLp.coeFn_toLp
        (f := fun _ : Ω ↦ (a : ℝ))
        (μ := μ)
        (p := 1)
        (MeasureTheory.memLp_const (p := 1) (μ := μ) (a : ℝ)))
  have hterms :
      (fun f : F ↦ ∫⁻ x,
        ENNReal.ofReal (|f.1 x| - (((constantCutoff a).toLp : Lp ℝ 1 μ) : Ω → ℝ) x) ∂μ) =
        fun f : F ↦ ∫⁻ x, ENNReal.ofReal (|f.1 x| - (a : ℝ)) ∂μ := by
    -- Rewrite each witness integral with the almost-everywhere equality to the constant function.
    funext f
    refine lintegral_congr_ae ?_
    filter_upwards [hconst] with x hx
    simp [hx]
  simpa [hterms] using ha

/-- Helper for Theorem 6.17: on finite measure spaces, mathlib `UniformIntegrable` implies the
source excess criterion `(6.2)`. -/
lemma integrableCutoffExcessCriterion_of_uniformIntegrable [IsFiniteMeasure μ]
    (F : Set (Lp ℝ 1 μ)) :
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ →
      @HasIntegrableCutoffExcessCriterion Ω _ μ F := by
  intro hUI
  -- Compare the owner constant-tail criterion with the source constant-excess version, then view
  -- finite-measure constants as integrable cutoffs.
  have hConstTail : @HasConstantCutoffTailCriterion Ω _ μ F :=
    (uniformIntegrable_iff_constantCutoffTailCriterionAux F).mp hUI
  have hConstExcess : @HasConstantCutoffExcessCriterion Ω _ μ F :=
    (constantCutoffExcessCriterion_iff_constantCutoffTailCriterionAux F).2 hConstTail
  exact integrableCutoffExcessCriterion_of_constantCutoffExcessCriterion F hConstExcess

/-- Helper for Theorem 6.17: a single integrable nonnegative weight controlling restricted
`L¹` integrals is the only missing bridge in the general-measure forward direction. -/
private def HasIntegrableWeightControlAux (F : Set (Lp ℝ 1 μ)) : Prop :=
  ∃ weight : Ω → ℝ,
    0 ≤ᵐ[μ] weight ∧
      Integrable weight μ ∧
        ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ s : Set Ω, MeasurableSet s → (∫ x, weight x ∂(μ.restrict s)) < δ →
            ∀ ⦃f : Lp ℝ 1 μ⦄, f ∈ F → (∫ x, |f x| ∂(μ.restrict s)) ≤ ε

/-- Helper for Theorem 6.17: for an `L¹` function, the restricted `L¹` seminorm is the
corresponding restricted real integral of `|f|`. -/
private lemma eLpNorm_indicator_eq_ofReal_setIntegral_abs (f : Lp ℝ 1 μ) {s : Set Ω}
    (hs : MeasurableSet s) :
    eLpNorm (s.indicator (f : Ω → ℝ)) 1 μ =
      ENNReal.ofReal (∫ x, |(f : Ω → ℝ) x| ∂(μ.restrict s)) := by
  -- Rewrite the restricted `L¹` seminorm into the real-valued set integral used by the source
  -- tail estimate.
  have hInt : Integrable (f : Ω → ℝ) (μ.restrict s) :=
    memLp_one_iff_integrable.mp <| (Lp.memLp f).mono_measure μ.restrict_le_self
  calc
    eLpNorm (s.indicator (f : Ω → ℝ)) 1 μ
        = ∫⁻ x in s, ENNReal.ofReal |(f : Ω → ℝ) x| ∂μ := by
            rw [eLpNorm_indicator_one_eq_setLIntegral_abs _ hs]
    _ = ENNReal.ofReal (∫ x in s, |(f : Ω → ℝ) x| ∂μ) := by
          symm
          simpa [Real.enorm_eq_ofReal_abs] using
            (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hInt)

/-- Helper for Theorem 6.17: packaging a nonnegative integrable real function as an admissible
integrable cutoff preserves almost-everywhere nonnegativity after `MemLp.toLp`. -/
private lemma scaledIntegrableCutoff_aeNonneg (weight : Ω → ℝ) (hweight_nonneg : 0 ≤ᵐ[μ] weight)
    (hweight_int : Integrable weight μ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    0 ≤ᵐ[μ]
      ((MeasureTheory.MemLp.toLp (fun x ↦ c * weight x)
        (memLp_one_iff_integrable.mpr (hweight_int.const_mul c))) : Ω → ℝ) := by
  -- Compare the chosen `Lp` representative with the original scaled weight pointwise almost
  -- everywhere and reuse the nonnegativity of `weight`.
  filter_upwards
      [MeasureTheory.MemLp.coeFn_toLp
        (f := fun x ↦ c * weight x)
        (μ := μ)
        (p := 1)
        (memLp_one_iff_integrable.mpr (hweight_int.const_mul c)),
        hweight_nonneg] with x htoLp hx
  simpa [htoLp] using mul_nonneg hc_nonneg hx

/-- Helper for Theorem 6.17: a nonnegative integrable real weight can be used as an
integrable-cutoff witness after scaling by a nonnegative real constant. -/
private def mkCutoffOfIntegrableNonnegative (weight : Ω → ℝ) (hweight_nonneg : 0 ≤ᵐ[μ] weight)
    (hweight_int : Integrable weight μ) {c : ℝ} (hc_nonneg : 0 ≤ c) :
    @IntegrableNonnegativeCutoff Ω _ μ :=
  { toLp := MeasureTheory.MemLp.toLp (fun x ↦ c * weight x)
      (memLp_one_iff_integrable.mpr (hweight_int.const_mul c))
    ae_nonneg := scaledIntegrableCutoff_aeNonneg weight hweight_nonneg hweight_int hc_nonneg }

/-- Helper for Theorem 6.17: the cutoff built from a scaled integrable weight agrees
almost everywhere with the original pointwise scalar multiple. -/
private lemma mkCutoffOfIntegrableNonnegative_coe_ae_eq (weight : Ω → ℝ)
    (hweight_nonneg : 0 ≤ᵐ[μ] weight) (hweight_int : Integrable weight μ) {c : ℝ}
    (hc_nonneg : 0 ≤ c) :
    (mkCutoffOfIntegrableNonnegative weight hweight_nonneg hweight_int hc_nonneg : Ω → ℝ)
      =ᵐ[μ] fun x ↦ c * weight x := by
  simpa [mkCutoffOfIntegrableNonnegative] using
    (MeasureTheory.MemLp.coeFn_toLp
      (f := fun x ↦ c * weight x)
      (μ := μ)
      (p := 1)
      (memLp_one_iff_integrable.mpr (hweight_int.const_mul c)))

/-- Helper for Theorem 6.17: once one integrable weight controls restricted `L¹` integrals and a
uniform global `L¹` bound is available, the source scaling argument produces an admissible
integrable cutoff with uniformly small strict tails. -/
private lemma integrableCutoffTailCriterion_of_weightControlAux (F : Set (Lp ℝ 1 μ))
    (hBound : ∃ C : ℝ≥0, ∀ f : F, eLpNorm ((f.1 : Ω → ℝ)) 1 μ ≤ C)
    (hWeight : HasIntegrableWeightControlAux F) :
    @HasIntegrableCutoffTailCriterion Ω _ μ F := by
  rcases hBound with ⟨C, hC⟩
  rcases hWeight with ⟨weight, hweight_nonneg, hweight_int, hweight_control⟩
  rw [HasIntegrableCutoffTailCriterion, sInfRange_eq_zero_iff_forall_epsilon]
  intro ε hε
  -- Use the weight-control witness at scale `ε / 2`; the remaining half-gap yields the strict
  -- inequality required by the `sInf` criterion.
  obtain ⟨δ, hδ_pos, hδ⟩ := hweight_control (ε / 2) (half_pos hε)
  let B : ℝ := C
  let c : ℝ := (B + 1) / δ
  have hB_nonneg : 0 ≤ B := by
    exact_mod_cast C.2
  have hc_pos : 0 < c := by
    -- The scaling constant is chosen exactly as in the source proof to force
    -- `(1 / c) * B < δ`.
    dsimp [c, B]
    positivity
  have hc_nonneg : 0 ≤ c := hc_pos.le
  let g : IntegrableNonnegativeCutoff :=
    mkCutoffOfIntegrableNonnegative weight hweight_nonneg hweight_int hc_nonneg
  refine ⟨g, ?_⟩
  have hIntegralBound : ∀ f : F, ∫ x, |(f.1 : Ω → ℝ) x| ∂μ ≤ B := by
    intro f
    have hnorm :
        eLpNorm ((f.1 : Ω → ℝ)) 1 μ =
          ENNReal.ofReal (∫ x, |(f.1 : Ω → ℝ) x| ∂μ) := by
      simpa using
        (eLpNorm_indicator_eq_ofReal_setIntegral_abs (μ := μ) f.1
          (s := Set.univ) MeasurableSet.univ)
    have hbound :
        ENNReal.ofReal (∫ x, |(f.1 : Ω → ℝ) x| ∂μ) ≤ ENNReal.ofReal B := by
      simpa [B, hnorm] using hC f
    exact (ENNReal.ofReal_le_ofReal_iff hB_nonneg).mp hbound
  have hScaleSmall : (1 / c) * B < δ := by
    have hB1_pos : 0 < B + 1 := by
      linarith
    have hfrac_lt_one : B / (B + 1) < 1 := by
      rw [div_lt_one hB1_pos]
      linarith
    have hrewrite : (1 / c) * B = δ * (B / (B + 1)) := by
      dsimp [c]
      field_simp [hδ_pos.ne', hB1_pos.ne]
    rw [hrewrite]
    have : δ * (B / (B + 1)) < δ * 1 := by
      exact mul_lt_mul_of_pos_left hfrac_lt_one hδ_pos
    simpa using this
  have hsmall :
      iSup (fun f : F ↦
        ∫⁻ x in {x | g x < |(f.1 : Ω → ℝ) x|}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) ≤
        ENNReal.ofReal (ε / 2) := by
    refine iSup_le fun f ↦ ?_
    let s : Set Ω := {x | g x < |(f.1 : Ω → ℝ) x|}
    have hs : MeasurableSet s :=
      measurableSet_lt (Lp.stronglyMeasurable g.toLp).measurable
        (Lp.stronglyMeasurable f.1).norm.measurable
    have hscaled_eq :
        (g : Ω → ℝ) =ᵐ[μ] fun x ↦ c * weight x :=
      mkCutoffOfIntegrableNonnegative_coe_ae_eq weight hweight_nonneg hweight_int hc_nonneg
    have hweight_le :
        ∫ x in s, weight x ∂μ ≤ ∫ x in s, (1 / c) * |(f.1 : Ω → ℝ) x| ∂μ := by
      have hscaled_int : Integrable (fun x ↦ (1 / c) * |(f.1 : Ω → ℝ) x|) μ :=
        ((memLp_one_iff_integrable.mp (Lp.memLp f.1)).norm.const_mul (1 / c))
      refine setIntegral_mono_on_ae hweight_int.integrableOn hscaled_int.integrableOn hs ?_
      filter_upwards [hscaled_eq] with x hx hxmem
      have htail : c * weight x < |(f.1 : Ω → ℝ) x| := by
        simpa [s, hx] using hxmem
      have hdiv : weight x ≤ |(f.1 : Ω → ℝ) x| / c := by
        rw [le_div_iff₀ hc_pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using htail.le
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
    have hscaled_set_le :
        ∫ x in s, (1 / c) * |(f.1 : Ω → ℝ) x| ∂μ ≤
          (1 / c) * ∫ x, |(f.1 : Ω → ℝ) x| ∂μ := by
      have hscaled_int : Integrable (fun x ↦ (1 / c) * |(f.1 : Ω → ℝ) x|) μ :=
        ((memLp_one_iff_integrable.mp (Lp.memLp f.1)).norm.const_mul (1 / c))
      have hscaled_nonneg : 0 ≤ᵐ[μ] fun x ↦ (1 / c) * |(f.1 : Ω → ℝ) x| := by
        filter_upwards with x
        positivity
      calc
        ∫ x in s, (1 / c) * |(f.1 : Ω → ℝ) x| ∂μ
            ≤ ∫ x, (1 / c) * |(f.1 : Ω → ℝ) x| ∂μ := by
                exact setIntegral_le_integral hscaled_int hscaled_nonneg
        _ = (1 / c) * ∫ x, |(f.1 : Ω → ℝ) x| ∂μ := by
              rw [integral_const_mul]
    have hweight_small : ∫ x in s, weight x ∂μ < δ := by
      have hbound_to_B :
          (1 / c) * ∫ x, |(f.1 : Ω → ℝ) x| ∂μ ≤ (1 / c) * B := by
        exact mul_le_mul_of_nonneg_left (hIntegralBound f) (by positivity)
      exact lt_of_le_of_lt (le_trans hweight_le (le_trans hscaled_set_le hbound_to_B)) hScaleSmall
    have htail_real :
        ∫ x in s, |(f.1 : Ω → ℝ) x| ∂μ ≤ ε / 2 :=
      by
        simpa using hδ s hs (by simpa using hweight_small) f.2
    calc
      ∫⁻ x in {x | g x < |(f.1 : Ω → ℝ) x|}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ
          = ENNReal.ofReal (∫ x in s, |(f.1 : Ω → ℝ) x| ∂μ) := by
              rw [← eLpNorm_indicator_one_eq_setLIntegral_abs _ hs,
                eLpNorm_indicator_eq_ofReal_setIntegral_abs (μ := μ) f.1 hs]
      _ ≤ ENNReal.ofReal (ε / 2) := ENNReal.ofReal_le_ofReal htail_real
  exact lt_of_le_of_lt hsmall <|
    (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

/-- Helper for Theorem 6.17: mathlib's `UniformIntegrable.spec` already supplies an arbitrary-
measure constant-tail estimate, so the unresolved step is only the passage from constant tails to a
single integrable weight. -/
private lemma uniformIntegrableToConstantTailCriterionAux (F : Set (Lp ℝ 1 μ)) :
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ →
      ∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0,
        iSup (fun f : F ↦
          ∫⁻ x in {x | (C : ℝ) < |(f.1 : Ω → ℝ) x|}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) <
            ENNReal.ofReal ε := by
  intro hUI ε hε
  have hone_ne_zero : (1 : ℝ≥0∞) ≠ 0 := by simp
  obtain ⟨C, hC⟩ :=
    hUI.spec hone_ne_zero ENNReal.one_ne_top (ε := ε / 2) (half_pos hε)
  refine ⟨C, ?_⟩
  have hbound :
      iSup (fun f : F ↦
        ∫⁻ x in {x | (C : ℝ) < |(f.1 : Ω → ℝ) x|}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) ≤
        ENNReal.ofReal (ε / 2) := by
    -- Compare the strict tail set with mathlib's non-strict cutoff set from `UniformIntegrable.spec`.
    refine iSup_le fun f ↦ ?_
    have hs :
        MeasurableSet {x | (C : ℝ) < |(f.1 : Ω → ℝ) x|} :=
      measurableSet_lt measurable_const (Lp.stronglyMeasurable f.1).norm.measurable
    calc
      ∫⁻ x in {x | (C : ℝ) < |(f.1 : Ω → ℝ) x|}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ
          = eLpNorm ({x | (C : ℝ) < |(f.1 : Ω → ℝ) x|}.indicator ((f.1 : Ω → ℝ))) 1 μ := by
              rw [eLpNorm_indicator_one_eq_setLIntegral_abs _ hs]
      _ ≤ eLpNorm ({x | C ≤ ‖(f.1 : Ω → ℝ) x‖₊}.indicator ((f.1 : Ω → ℝ))) 1 μ := by
            refine eLpNorm_mono fun x ↦ ?_
            by_cases hx : (C : ℝ) < |(f.1 : Ω → ℝ) x|
            · have hx' : C ≤ ‖(f.1 : Ω → ℝ) x‖₊ := by
                simpa using le_of_lt hx
              simp [hx, hx']
            · simp [hx]
      _ ≤ ENNReal.ofReal (ε / 2) := hC f
  -- The `ε / 2` estimate is enough because the target `sInf` criterion only needs strict
  -- inequality at level `ε`.
  exact lt_of_le_of_lt hbound <| (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)

/-- Helper for Theorem 6.17: package the absolute-value density of an `L¹(μ)` function as a finite
measure. -/
private def lpAbsMeasure (f : Lp ℝ 1 μ) : Measure Ω :=
  μ.withDensity fun x ↦ ENNReal.ofReal |(f : Ω → ℝ) x|

/-- Helper for Theorem 6.17: the packaged absolute-value measure evaluates on measurable sets as
the restricted real integral of `|f|`. -/
private lemma lpAbsMeasure_apply_eq_ofReal_setIntegral_abs (f : Lp ℝ 1 μ) {s : Set Ω}
    (hs : MeasurableSet s) :
    lpAbsMeasure (μ := μ) f s =
      ENNReal.ofReal (∫ x in s, |(f : Ω → ℝ) x| ∂μ) := by
  have hInt : Integrable (f : Ω → ℝ) (μ.restrict s) :=
    memLp_one_iff_integrable.mp <| (Lp.memLp f).mono_measure μ.restrict_le_self
  -- Rewrite `withDensity` on measurable sets and convert the resulting `lintegral` back to a real
  -- set integral.
  calc
    lpAbsMeasure (μ := μ) f s = ∫⁻ x in s, ENNReal.ofReal |(f : Ω → ℝ) x| ∂μ := by
        rw [lpAbsMeasure, MeasureTheory.withDensity_apply _ hs]
    _ = ENNReal.ofReal (∫ x in s, |(f : Ω → ℝ) x| ∂μ) := by
          symm
          simpa [Real.enorm_eq_ofReal_abs] using
            (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm hInt)

/-- Helper for Theorem 6.17: the owner `UnifIntegrable` clause is exactly the source small-set
control on restricted integrals of `|f|`. -/
private lemma setIntegralAbs_small_of_uniformIntegrable (F : Set (Lp ℝ 1 μ))
    (hUI : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s : Set Ω, MeasurableSet s → μ s ≤ ENNReal.ofReal δ →
        ∀ ⦃f : Lp ℝ 1 μ⦄, f ∈ F → (∫ x in s, |(f : Ω → ℝ) x| ∂μ) ≤ ε := by
  intro ε hε
  obtain ⟨δ, hδ_pos, hδ⟩ := hUI.2.1 hε
  refine ⟨δ, hδ_pos, fun s hs hμs f hf ↦ ?_⟩
  have hIndicator :
      eLpNorm (s.indicator (f : Ω → ℝ)) 1 μ ≤ ENNReal.ofReal ε :=
    hδ ⟨f, hf⟩ s hs hμs
  -- Convert the owner restricted `L¹` bound into the real-valued set integral used in the file.
  rw [eLpNorm_indicator_eq_ofReal_setIntegral_abs (μ := μ) f hs] at hIndicator
  exact (ENNReal.ofReal_le_ofReal_iff hε.le).mp hIndicator

/-- Helper for Theorem 6.17: the family measures `lpAbsMeasure f` inherit a uniform total-mass
bound from the owner `UniformIntegrable` definition. -/
private lemma lpAbsMeasure_univ_le_of_uniformIntegrable (F : Set (Lp ℝ 1 μ))
    (hUI : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ) :
    ∃ C : ℝ≥0, ∀ ⦃f : Lp ℝ 1 μ⦄, f ∈ F → lpAbsMeasure (μ := μ) f Set.univ ≤ C := by
  rcases hUI.2.2 with ⟨C, hC⟩
  refine ⟨C, fun f hf ↦ ?_⟩
  -- Evaluate the packaged family measure on `univ` and compare it with the owner `L¹` bound.
  calc
    lpAbsMeasure (μ := μ) f Set.univ =
        ENNReal.ofReal (∫ x, |(f : Ω → ℝ) x| ∂μ) := by
          simpa using lpAbsMeasure_apply_eq_ofReal_setIntegral_abs (μ := μ) f MeasurableSet.univ
    _ = eLpNorm ((f : Ω → ℝ)) 1 μ := by
          symm
          simpa using
            (eLpNorm_indicator_eq_ofReal_setIntegral_abs (μ := μ) f
              (s := Set.univ) MeasurableSet.univ)
    _ ≤ C := by
          simpa using hC ⟨f, hf⟩

/-- Helper for Theorem 6.17: if the excess criterion fails, then one can normalize the failure to
one fixed positive gap `ε₀` that defeats every admissible cutoff. -/
private lemma uniformIntegrableCounterexampleNormalization (F : Set (Lp ℝ 1 μ))
    (hFail : ¬ @HasIntegrableCutoffExcessCriterion Ω _ μ F) :
    ∃ ε0 : ℝ, 0 < ε0 ∧
      ∀ g : @IntegrableNonnegativeCutoff Ω _ μ,
        ENNReal.ofReal ε0 <
          iSup (fun f : F ↦
            ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ) := by
  let Φ : @IntegrableNonnegativeCutoff Ω _ μ → ℝ≥0∞ := fun g ↦
    iSup (fun f : F ↦ ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ)
  have hnot :
      ¬ ∀ ε : ℝ, 0 < ε → ∃ g, Φ g < ENNReal.ofReal ε := by
    simpa [HasIntegrableCutoffExcessCriterion, Φ, sInfRange_eq_zero_iff_forall_epsilon] using hFail
  push Not at hnot
  rcases hnot with ⟨ε, hε_pos, hε⟩
  refine ⟨ε / 2, half_pos hε_pos, ?_⟩
  intro g
  -- Shrink the nonzero lower bound once so that the normalized counterexample is strict.
  have hε_lt : ENNReal.ofReal (ε / 2) < ENNReal.ofReal ε :=
    (ENNReal.ofReal_lt_ofReal_iff hε_pos).2 (by linarith)
  exact lt_of_lt_of_le hε_lt (hε g)

/-- Helper for Theorem 6.17: summable real bounds on the ENNReal-valued cutoff terms force the
packaged series to have finite total `lintegral`. -/
private lemma geometricCutoffSeries_lintegral_ne_top (u : ℕ → Ω → ℝ)
    (hu_aemeas : ∀ n, AEMeasurable (fun x ↦ ENNReal.ofReal (u n x)) μ) (eps : ℕ → ℝ)
    (hterm :
      ∀ n, ∫⁻ x, ENNReal.ofReal (u n x) ∂μ ≤ ENNReal.ofReal (eps n))
    (hsum : Summable eps) :
    ∫⁻ x, (∑' n, ENNReal.ofReal (u n x)) ∂μ ≠ ⊤ := by
  have hseries_le :
      ∫⁻ x, (∑' n, ENNReal.ofReal (u n x)) ∂μ ≤ ∑' n, ENNReal.ofReal (eps n) := by
    -- Sum the packaged ENNReal terms first, then compare termwise with the summable real bounds.
    calc
      ∫⁻ x, (∑' n, ENNReal.ofReal (u n x)) ∂μ =
          ∑' n, ∫⁻ x, ENNReal.ofReal (u n x) ∂μ := by
            simpa using
              (lintegral_tsum hu_aemeas :
                ∫⁻ x, (∑' n, ENNReal.ofReal (u n x)) ∂μ =
                  ∑' n, ∫⁻ x, ENNReal.ofReal (u n x) ∂μ)
      _ ≤ ∑' n, ENNReal.ofReal (eps n) := by
            exact ENNReal.tsum_le_tsum hterm
  exact ne_top_of_le_ne_top hsum.tsum_ofReal_ne_top hseries_le

/-- Helper for Theorem 6.17: a series of nonnegative ENNReal-valued cutoff terms with finite total
`lintegral` packages into one admissible integrable cutoff after taking `toReal`. -/
private lemma geometricCutoffSeries_isIntegrableCutoff (u : ℕ → Ω → ℝ)
    (hu_aemeas : ∀ n, AEMeasurable (fun x ↦ ENNReal.ofReal (u n x)) μ)
    (hfin : ∫⁻ x, (∑' n, ENNReal.ofReal (u n x)) ∂μ ≠ ⊤) :
    ∃ g : @IntegrableNonnegativeCutoff Ω _ μ,
      g =ᵐ[μ] fun x ↦ (∑' n, ENNReal.ofReal (u n x)).toReal := by
  let weightInf : Ω → ℝ≥0∞ := fun x ↦ ∑' n, ENNReal.ofReal (u n x)
  let weight : Ω → ℝ := fun x ↦ (weightInf x).toReal
  have hweightInf_aemeas : AEMeasurable weightInf μ := by
    -- The `ENNReal` series is measurable termwise, so its pointwise sum is measurable as well.
    simpa [weightInf] using (AEMeasurable.ennreal_tsum hu_aemeas)
  have hweight_int : Integrable weight μ := by
    -- Finite total `lintegral` lets us pass from the `ENNReal` series to an integrable real
    -- representative by taking `toReal`.
    exact integrable_toReal_of_lintegral_ne_top hweightInf_aemeas hfin
  let g : @IntegrableNonnegativeCutoff Ω _ μ :=
    { toLp := MeasureTheory.MemLp.toLp weight (memLp_one_iff_integrable.mpr hweight_int)
      ae_nonneg := by
        -- Compare the chosen `Lp` representative with the underlying `toReal` series pointwise.
        filter_upwards
            [MeasureTheory.MemLp.coeFn_toLp
              (f := weight)
              (μ := μ)
              (p := 1)
              (memLp_one_iff_integrable.mpr hweight_int)] with x hx
        rw [hx]
        exact ENNReal.toReal_nonneg }
  refine ⟨g, ?_⟩
  -- The packaged cutoff agrees almost everywhere with the pointwise `toReal` series.
  simpa [g, weight, weightInf] using
    (MeasureTheory.MemLp.coeFn_toLp
      (f := weight)
      (μ := μ)
      (p := 1)
      (memLp_one_iff_integrable.mpr hweight_int))

/-- Helper for Theorem 6.17: the bounded-window excess term is pointwise dominated by the witness
absolute value, so its total mass is controlled by `lpAbsMeasure`. -/
private lemma boundedWindowExcessTerm_lintegral_le (g : @IntegrableNonnegativeCutoff Ω _ μ)
    (f : Lp ℝ 1 μ) (s : Set Ω) :
    ∫⁻ x, ENNReal.ofReal (s.indicator (fun x ↦ max (|(f : Ω → ℝ) x| - g x) 0) x) ∂μ ≤
      lpAbsMeasure (μ := μ) f Set.univ := by
  -- Route correction: keep the stage-term mass estimate in the `lpAbsMeasure` spelling so the
  -- recursive contradiction does not keep reopening the same `withDensity` normalization.
  have hpointwise :
      (fun x ↦ ENNReal.ofReal (s.indicator (fun x ↦ max (|(f : Ω → ℝ) x| - g x) 0) x))
        ≤ᵐ[μ] fun x ↦ ENNReal.ofReal |(f : Ω → ℝ) x| := by
    -- On the window the excess term is at most `|f|`; off the window it vanishes.
    filter_upwards [g.ae_nonneg] with x hx
    by_cases hsx : x ∈ s
    · have hle : max (|(f : Ω → ℝ) x| - g x) 0 ≤ |(f : Ω → ℝ) x| := by
        exact max_le (sub_le_self _ hx) (abs_nonneg _)
      rw [Set.indicator_of_mem hsx]
      exact ENNReal.ofReal_le_ofReal hle
    · rw [Set.indicator_of_notMem hsx]
      simp
  calc
    ∫⁻ x, ENNReal.ofReal (s.indicator (fun x ↦ max (|(f : Ω → ℝ) x| - g x) 0) x) ∂μ
        ≤ ∫⁻ x, ENNReal.ofReal |(f : Ω → ℝ) x| ∂μ := by
            exact lintegral_mono_ae hpointwise
    _ = ENNReal.ofReal (∫ x, |(f : Ω → ℝ) x| ∂μ) := by
          -- Convert the total `lintegral` back to the real `L¹` norm of `f`.
          symm
          simpa [Real.enorm_eq_ofReal_abs] using
            (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm
              (memLp_one_iff_integrable.mp (Lp.memLp f)).norm)
    _ = lpAbsMeasure (μ := μ) f Set.univ := by
          -- The packaged absolute-value measure has the same total mass on `univ`.
          symm
          simpa using lpAbsMeasure_apply_eq_ofReal_setIntegral_abs
            (μ := μ) f MeasurableSet.univ

/-- Helper for Theorem 6.17: adding a fraction of the current bounded-window excess term shrinks
the same excess by the factor `1 - a` on that window. -/
private lemma oneStepWindowedExcessSuppression {s : Set Ω} (h g : Ω → ℝ) {a : ℝ}
    (ha1 : a ≤ 1) {x : Ω} (hx : x ∈ s) :
    max
        (|h x| -
          (g x + a * s.indicator (fun y ↦ max (|h y| - g y) 0) x))
        0 =
      (1 - a) * s.indicator (fun y ↦ max (|h y| - g y) 0) x := by
  -- On the chosen window the indicator is active, so the algebra reduces to the scalar identity
  -- `max (d - a * d) 0 = (1 - a) * d` for `d = (|h| - g)^+`.
  simp [hx]
  let d : ℝ := |h x| - g x
  have hleft :
      |h x| - (g x + a * max (|h x| - g x) 0) = d - a * max d 0 := by
    dsimp [d]
    ring
  have hright : (1 - a) * max (|h x| - g x) 0 = (1 - a) * max d 0 := by
    simp [d]
  rw [hleft, hright]
  by_cases hd : 0 ≤ d
  · have hmul_nonneg : 0 ≤ (1 - a) * d := by
      exact mul_nonneg (sub_nonneg.mpr ha1) hd
    rw [max_eq_left hd]
    -- Once `d` is nonnegative, the excess term is exactly `d`.
    rw [show d - a * d = (1 - a) * d by ring]
    rw [max_eq_left hmul_nonneg]
  · have hd' : d ≤ 0 := le_of_not_ge hd
    rw [max_eq_right hd']
    -- When `d ≤ 0`, the positive-part excess vanishes before and after the update.
    rw [mul_zero, sub_zero, max_eq_right hd']
    simp

/-- Helper for Theorem 6.17: on a large-value tail, the excess integrand is dominated by the
absolute-value tail integrand. -/
private lemma excessTailOnLargeValues_le_tailIntegral (g : @IntegrableNonnegativeCutoff Ω _ μ)
    (f : Lp ℝ 1 μ) (C : ℝ≥0) :
    ∫⁻ x in {x | (C : ℝ) < |(f : Ω → ℝ) x|},
      ENNReal.ofReal (max (|(f : Ω → ℝ) x| - g x) 0) ∂μ ≤
      ∫⁻ x in {x | (C : ℝ) < |(f : Ω → ℝ) x|},
        ENNReal.ofReal |(f : Ω → ℝ) x| ∂μ := by
  let s : Set Ω := {x | (C : ℝ) < |(f : Ω → ℝ) x|}
  have hs : MeasurableSet s :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable f).norm.measurable
  have hpointwise :
      (fun x ↦ s.indicator (fun x ↦ ENNReal.ofReal (max (|(f : Ω → ℝ) x| - g x) 0)) x) ≤ᵐ[μ]
        fun x ↦ s.indicator (fun x ↦ ENNReal.ofReal |(f : Ω → ℝ) x|) x := by
    -- Proof comment: on the tail set both indicators are active, so only the pointwise estimate
    -- `( |f| - g )⁺ ≤ |f|` remains.
    filter_upwards [g.ae_nonneg] with x hx
    by_cases hsx : x ∈ s
    · rw [Set.indicator_of_mem hsx, Set.indicator_of_mem hsx]
      exact ENNReal.ofReal_le_ofReal <| max_le (sub_le_self _ hx) (abs_nonneg _)
    · rw [Set.indicator_of_notMem hsx, Set.indicator_of_notMem hsx]
  -- Proof comment: rewrite both restricted `lintegral`s as indicators and apply the pointwise tail
  -- domination on the ambient measure.
  calc
    ∫⁻ x in s, ENNReal.ofReal (max (|(f : Ω → ℝ) x| - g x) 0) ∂μ
        = ∫⁻ x, s.indicator (fun x ↦ ENNReal.ofReal (max (|(f : Ω → ℝ) x| - g x) 0)) x ∂μ := by
            rw [← MeasureTheory.lintegral_indicator hs]
    _ ≤ ∫⁻ x, s.indicator (fun x ↦ ENNReal.ofReal |(f : Ω → ℝ) x|) x ∂μ := by
          exact lintegral_mono_ae hpointwise
    _ = ∫⁻ x in s, ENNReal.ofReal |(f : Ω → ℝ) x| ∂μ := by
          rw [MeasureTheory.lintegral_indicator hs]

/-- Helper for Theorem 6.17: every counterexample cutoff already has one bounded bad window in the
exact indicator spelling used by the later recursive stage terms. -/
private lemma counterexampleBoundedWindow_of_tailBound (F : Set (Lp ℝ 1 μ))
    {ε0 : ℝ} (hε0 : 0 < ε0)
    (hCounter :
      ∀ g : @IntegrableNonnegativeCutoff Ω _ μ,
        ENNReal.ofReal ε0 <
          iSup (fun f : F ↦
            ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ))
    {C : ℝ≥0}
    (hC :
      iSup (fun f : F ↦
        ∫⁻ x in {x | (C : ℝ) < |(f.1 : Ω → ℝ) x|}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) <
          ENNReal.ofReal (ε0 / 4))
    (g : @IntegrableNonnegativeCutoff Ω _ μ) :
    ∃ f : F,
      ENNReal.ofReal (ε0 / 2) <
        ∫⁻ x,
          ENNReal.ofReal
            ({x | g x < |(f.1 : Ω → ℝ) x| ∧ |(f.1 : Ω → ℝ) x| ≤ C}.indicator
              (fun x ↦ max (|(f.1 : Ω → ℝ) x| - g x) 0) x) ∂μ := by
  obtain ⟨f, hf⟩ := lt_iSup_iff.mp (hCounter g)
  let bounded : Set Ω := {x | |(f.1 : Ω → ℝ) x| ≤ C}
  let tail : Set Ω := {x | (C : ℝ) < |(f.1 : Ω → ℝ) x|}
  let s : Set Ω := {x | g x < |(f.1 : Ω → ℝ) x| ∧ |(f.1 : Ω → ℝ) x| ≤ C}
  have hbounded : MeasurableSet bounded :=
    measurableSet_le (Lp.stronglyMeasurable f.1).norm.measurable measurable_const
  have htail :
      ∫⁻ x in tail, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ <
        ENNReal.ofReal (ε0 / 4) := by
    have htail_abs :
        ∫⁻ x in tail, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ < ENNReal.ofReal (ε0 / 4) :=
      lt_of_le_of_lt
        (le_iSup (fun f : F ↦
          ∫⁻ x in {x | (C : ℝ) < |(f.1 : Ω → ℝ) x|}, ENNReal.ofReal |(f.1 : Ω → ℝ) x| ∂μ) f)
        hC
    exact lt_of_le_of_lt (excessTailOnLargeValues_le_tailIntegral g f.1 C) htail_abs
  have hsplit :
      ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ =
        (∫⁻ x,
          ENNReal.ofReal
            (s.indicator (fun x ↦ max (|(f.1 : Ω → ℝ) x| - g x) 0) x) ∂μ) +
          ∫⁻ x in tail, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ := by
    have hbounded_eq :
        ∫⁻ x in bounded, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ =
          ∫⁻ x,
            ENNReal.ofReal
              (s.indicator (fun x ↦ max (|(f.1 : Ω → ℝ) x| - g x) 0) x) ∂μ := by
      -- Proof comment: on the fixed bounded region, the excess survives exactly on the bad window
      -- where the cutoff is still strictly below `|f|`.
      calc
        ∫⁻ x in bounded, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ
            = ∫⁻ x,
                bounded.indicator
                  (fun x ↦ ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0)) x ∂μ := by
                  rw [← MeasureTheory.lintegral_indicator hbounded]
        _ = ∫⁻ x,
              ENNReal.ofReal
                (s.indicator (fun x ↦ max (|(f.1 : Ω → ℝ) x| - g x) 0) x) ∂μ := by
              refine lintegral_congr_ae ?_
              filter_upwards with x
              by_cases hbx : x ∈ bounded
              · by_cases hgx : g x < |(f.1 : Ω → ℝ) x|
                · have hsx : x ∈ s := ⟨hgx, hbx⟩
                  have hnonneg : 0 ≤ |(f.1 : Ω → ℝ) x| - g x := sub_nonneg.mpr (le_of_lt hgx)
                  rw [Set.indicator_of_mem hbx, Set.indicator_of_mem hsx, max_eq_left hnonneg]
                · have hsx : x ∉ s := by simp [s, hgx]
                  have hnonpos : |(f.1 : Ω → ℝ) x| - g x ≤ 0 :=
                    sub_nonpos.mpr (le_of_not_gt hgx)
                  rw [Set.indicator_of_mem hbx, Set.indicator_of_notMem hsx, max_eq_right hnonpos]
              · have hsx : x ∉ s := by
                  intro hs_mem
                  exact hbx hs_mem.2
                rw [Set.indicator_of_notMem hbx, Set.indicator_of_notMem hsx]
                simp
    have htail_eq : boundedᶜ = tail := by
      ext x
      simp [bounded, tail, not_le]
    -- Proof comment: split the total excess into the bounded region and the large-value tail.
    calc
      ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ
          = ∫⁻ x in bounded, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ +
              ∫⁻ x in boundedᶜ, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ := by
                rw [← MeasureTheory.lintegral_add_compl
                  (μ := μ) (fun x ↦ ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0)) hbounded]
      _ = (∫⁻ x,
            ENNReal.ofReal
              (s.indicator (fun x ↦ max (|(f.1 : Ω → ℝ) x| - g x) 0) x) ∂μ) +
            ∫⁻ x in tail, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ := by
              rw [hbounded_eq, htail_eq]
  refine ⟨f, ?_⟩
  have hwindow_not_le :
      ¬ ∫⁻ x,
          ENNReal.ofReal
            (s.indicator (fun x ↦ max (|(f.1 : Ω → ℝ) x| - g x) 0) x) ∂μ ≤
          ENNReal.ofReal (ε0 / 2) := by
    intro hs_le
    have hsum_le :
        ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ ≤
          ENNReal.ofReal (ε0 / 2) + ENNReal.ofReal (ε0 / 4) := by
      rw [hsplit]
      exact add_le_add hs_le htail.le
    have hsum_lt :
        ENNReal.ofReal (ε0 / 2) + ENNReal.ofReal (ε0 / 4) < ENNReal.ofReal ε0 := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      exact (ENNReal.ofReal_lt_ofReal_iff hε0).2 (by linarith)
    have hcontr :
        ENNReal.ofReal ε0 <
          ENNReal.ofReal (ε0 / 2) + ENNReal.ofReal (ε0 / 4) :=
      lt_of_lt_of_le hf hsum_le
    exact (not_lt_of_ge hsum_lt.le) hcontr
  exact lt_of_not_ge hwindow_not_le

/-- Helper for Theorem 6.17: the bad windows can be chosen below one common height cutoff coming
from the owner constant-tail estimate, independently of the current cutoff `g`. -/
private lemma counterexampleUniformWindowHeight (F : Set (Lp ℝ 1 μ))
    (hUI : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ) {ε0 : ℝ} (hε0 : 0 < ε0)
    (hCounter :
      ∀ g : @IntegrableNonnegativeCutoff Ω _ μ,
        ENNReal.ofReal ε0 <
          iSup (fun f : F ↦
            ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ)) :
    ∃ C : ℝ≥0, ∀ g : @IntegrableNonnegativeCutoff Ω _ μ,
      ∃ f : F,
        ENNReal.ofReal (ε0 / 2) <
          ∫⁻ x,
            ENNReal.ofReal
              ({x | g x < |(f.1 : Ω → ℝ) x| ∧ |(f.1 : Ω → ℝ) x| ≤ C}.indicator
                (fun x ↦ max (|(f.1 : Ω → ℝ) x| - g x) 0) x) ∂μ := by
  have hquarter : 0 < ε0 / 4 := by positivity
  obtain ⟨C, hC⟩ := uniformIntegrableToConstantTailCriterionAux F hUI (ε0 / 4) hquarter
  refine ⟨C, fun g ↦ ?_⟩
  -- Proof comment: reuse the single tail cutoff `C` for every later stage cutoff `g`.
  exact counterexampleBoundedWindow_of_tailBound F hε0 hCounter hC g

/-- Helper for Theorem 6.17: every counterexample cutoff already has one bounded bad window in the
exact indicator spelling used by the later recursive stage terms. -/
private lemma counterexampleBoundedWindow (F : Set (Lp ℝ 1 μ))
    (hUI : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ) {ε0 : ℝ} (hε0 : 0 < ε0)
    (hCounter :
      ∀ g : @IntegrableNonnegativeCutoff Ω _ μ,
        ENNReal.ofReal ε0 <
          iSup (fun f : F ↦
            ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ))
    (g : @IntegrableNonnegativeCutoff Ω _ μ) :
    ∃ f : F, ∃ C : ℝ≥0,
      ENNReal.ofReal (ε0 / 2) <
        ∫⁻ x,
          ENNReal.ofReal
            ({x | g x < |(f.1 : Ω → ℝ) x| ∧ |(f.1 : Ω → ℝ) x| ≤ C}.indicator
              (fun x ↦ max (|(f.1 : Ω → ℝ) x| - g x) 0) x) ∂μ := by
  have hquarter : 0 < ε0 / 4 := by positivity
  obtain ⟨C, hC⟩ := uniformIntegrableToConstantTailCriterionAux F hUI (ε0 / 4) hquarter
  obtain ⟨f, hf⟩ := counterexampleBoundedWindow_of_tailBound F hε0 hCounter hC g
  -- Proof comment: the owner constant-tail cutoff `C` is already enough for the stage witness.
  exact ⟨f, C, hf⟩

/-- Helper for Theorem 6.17: the global excess functional decreases when the cutoff increases
almost everywhere. -/
private lemma excessFunctional_mono (F : Set (Lp ℝ 1 μ))
    {g h : @IntegrableNonnegativeCutoff Ω _ μ} (hgh : (g : Ω → ℝ) ≤ᵐ[μ] h) :
    iSup (fun f : F ↦
      ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - h x) 0) ∂μ) ≤
      iSup (fun f : F ↦
        ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ) := by
  -- Proof comment: once the cutoff gets larger, every pointwise positive-part excess can only
  -- decrease, so the same monotonicity passes through `lintegral` and then through `iSup`.
  refine iSup_le fun f ↦ ?_
  refine le_trans (lintegral_mono_ae ?_) <|
    le_iSup (fun f : F ↦
      ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ) f
  filter_upwards [hgh] with x hx
  exact ENNReal.ofReal_le_ofReal <|
    max_le_max (sub_le_sub_left hx (|(f.1 : Ω → ℝ) x|)) le_rfl

/-- Helper for Theorem 6.17: combine the bad-window witness with the uniform total-mass bound into
one reusable stage package. -/
private lemma counterexampleStageData (F : Set (Lp ℝ 1 μ))
    (hUI : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ) {ε0 : ℝ} (hε0 : 0 < ε0)
    (hCounter :
      ∀ g : @IntegrableNonnegativeCutoff Ω _ μ,
        ENNReal.ofReal ε0 <
          iSup (fun f : F ↦
            ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ)) :
    ∃ B : ℝ≥0, ∀ g : @IntegrableNonnegativeCutoff Ω _ μ,
      ∃ f : F, ∃ C : ℝ≥0,
        let s : Set Ω := {x | g x < |(f.1 : Ω → ℝ) x| ∧ |(f.1 : Ω → ℝ) x| ≤ C}
        let u : Ω → ℝ := s.indicator (fun x ↦ max (|(f.1 : Ω → ℝ) x| - g x) 0)
        0 ≤ᵐ[μ] u ∧
          ENNReal.ofReal (ε0 / 2) < ∫⁻ x, ENNReal.ofReal (u x) ∂μ ∧
          ∫⁻ x, ENNReal.ofReal (u x) ∂μ ≤ B := by
  rcases lpAbsMeasure_univ_le_of_uniformIntegrable F hUI with ⟨B, hB⟩
  refine ⟨B, fun g ↦ ?_⟩
  rcases counterexampleBoundedWindow F hUI hε0 hCounter g with ⟨f, C, hwindow⟩
  refine ⟨f, C, ?_⟩
  dsimp
  constructor
  · -- Proof comment: the stage integrand is an indicator of a positive-part excess, so it is
    -- pointwise nonnegative without any further input.
    filter_upwards with x
    by_cases hx :
        x ∈ {x | g x < |(f.1 : Ω → ℝ) x| ∧ |(f.1 : Ω → ℝ) x| ≤ C}
    · simp [hx]
    · simp [hx]
  constructor
  · -- Proof comment: this lower bound is exactly the bounded bad-window witness from the previous
    -- lemma, now only repackaged under the stage notation.
    simpa using hwindow
  · -- Proof comment: the same stage term is pointwise dominated by `|f|`, so the uniform
    -- `lpAbsMeasure` bound gives one common mass bound `B` for every stage.
    exact le_trans
      (boundedWindowExcessTerm_lintegral_le (μ := μ) g f
        {x | g x < |(f.1 : Ω → ℝ) x| ∧ |(f.1 : Ω → ℝ) x| ≤ C})
      (by simpa using hB (f := f.1) f.2)

/-- Helper for Theorem 6.17: the recursive stage package can be chosen with one common bad-window
height cutoff, so only the global `Φ`-drop lemma remains missing. -/
private lemma counterexampleUniformStageData (F : Set (Lp ℝ 1 μ))
    (hUI : UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ) {ε0 : ℝ} (hε0 : 0 < ε0)
    (hCounter :
      ∀ g : @IntegrableNonnegativeCutoff Ω _ μ,
        ENNReal.ofReal ε0 <
          iSup (fun f : F ↦
            ∫⁻ x, ENNReal.ofReal (max (|(f.1 : Ω → ℝ) x| - g x) 0) ∂μ)) :
    ∃ B : ℝ≥0, ∃ C : ℝ≥0, ∀ g : @IntegrableNonnegativeCutoff Ω _ μ,
      ∃ f : F,
        let s : Set Ω := {x | g x < |(f.1 : Ω → ℝ) x| ∧ |(f.1 : Ω → ℝ) x| ≤ C}
        let u : Ω → ℝ := s.indicator (fun x ↦ max (|(f.1 : Ω → ℝ) x| - g x) 0)
        0 ≤ᵐ[μ] u ∧
          ENNReal.ofReal (ε0 / 2) < ∫⁻ x, ENNReal.ofReal (u x) ∂μ ∧
          ∫⁻ x, ENNReal.ofReal (u x) ∂μ ≤ B := by
  rcases lpAbsMeasure_univ_le_of_uniformIntegrable F hUI with ⟨B, hB⟩
  rcases counterexampleUniformWindowHeight F hUI hε0 hCounter with ⟨C, hC⟩
  refine ⟨B, C, fun g ↦ ?_⟩
  rcases hC g with ⟨f, hf⟩
  refine ⟨f, ?_⟩
  dsimp
  constructor
  · -- Proof comment: the fixed-height stage integrand is still an indicator of a positive-part
    -- excess, so it remains pointwise nonnegative.
    filter_upwards with x
    by_cases hx :
        x ∈ {x | g x < |(f.1 : Ω → ℝ) x| ∧ |(f.1 : Ω → ℝ) x| ≤ C}
    · simp [hx]
    · simp [hx]
  constructor
  · -- Proof comment: this is exactly the common-height bad-window lower bound.
    simpa using hf
  · -- Proof comment: the same uniform mass bound `B` still controls each fixed-height stage term.
    exact le_trans
      (boundedWindowExcessTerm_lintegral_le (μ := μ) g f
        {x | g x < |(f.1 : Ω → ℝ) x| ∧ |(f.1 : Ω → ℝ) x| ≤ C})
      (by simpa using hB (f := f.1) f.2)


/-- Helper for Theorem 6.17: the source uniform-integrability definition directly implies the
integrable-cutoff tail criterion. -/
lemma integrableCutoffTailCriterion_of_uniformIntegrable (F : Set (Lp ℝ 1 μ)) :
    @HasIntegrableCutoffExcessCriterion Ω _ μ F →
      @HasIntegrableCutoffTailCriterion Ω _ μ F := by
  exact integrableCutoffTailCriterion_of_excessCriterion F



/-- Helper for Theorem 6.17: the source excess and tail cutoff criteria are equivalent. -/
theorem integrableCutoffExcessCriterion_iff_tailCriterion (F : Set (Lp ℝ 1 μ)) :
    @HasIntegrableCutoffExcessCriterion Ω _ μ F ↔
      @HasIntegrableCutoffTailCriterion Ω _ μ F := by
  constructor
  · exact integrableCutoffTailCriterion_of_excessCriterion F
  · exact integrableCutoffExcessCriterion_of_tailCriterion F

/-- Theorem 6.17: on an arbitrary measure space, the source uniform-integrability criterion
`(6.2)` is equivalent to the integrable-cutoff tail criterion `(6.3)`. -/
theorem uniformIntegrable_iff_cutoff_tail_inf_eq_zero (F : Set (Lp ℝ 1 μ)) :
    @HasIntegrableCutoffExcessCriterion Ω _ μ F ↔
      @HasIntegrableCutoffTailCriterion Ω _ μ F := by
  exact integrableCutoffExcessCriterion_iff_tailCriterion F


/-- Finite-measure addendum: on a finite measure space, uniform integrability is equivalent to
vanishing constant-cutoff excess integrals. -/
theorem uniformIntegrable_iff_cutoff_excess_sInf_eq_zero [IsFiniteMeasure μ]
    (F : Set (Lp ℝ 1 μ)) :
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ ↔
      @HasConstantCutoffExcessCriterion Ω _ μ F := by
  -- Compare the owner constant-tail criterion with the source constant-excess formulation.
  calc
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ
        ↔ @HasConstantCutoffTailCriterion Ω _ μ F :=
      uniformIntegrable_iff_constantCutoffTailCriterionAux F
    _ ↔ @HasConstantCutoffExcessCriterion Ω _ μ F :=
      (constantCutoffExcessCriterion_iff_constantCutoffTailCriterionAux F).symm

/-- Finite-measure addendum: the two constant-cutoff formulations from the
textbook are equivalent. -/
theorem cutoff_excess_sInf_eq_zero_iff_cutoff_tail_integral_sInf_eq_zero [IsFiniteMeasure μ]
    (F : Set (Lp ℝ 1 μ)) :
    @HasConstantCutoffExcessCriterion Ω _ μ F ↔
      @HasConstantCutoffTailCriterion Ω _ μ F := by
  -- This is exactly the direct comparison between excess and tail integrals.
  exact constantCutoffExcessCriterion_iff_constantCutoffTailCriterionAux F

/-- Finite-measure addendum: on a finite measure space, uniform integrability is equivalent to
vanishing constant-cutoff restricted tail integrals. -/
theorem uniformIntegrable_iff_cutoff_tail_integral_sInf_eq_zero [IsFiniteMeasure μ]
    (F : Set (Lp ℝ 1 μ)) :
    UniformIntegrable ((↑) : F → Ω → ℝ) 1 μ ↔
      @HasConstantCutoffTailCriterion Ω _ μ F := by
  -- This is the finite-measure owner bridge from `MeasureTheory.uniformIntegrable_iff`.
  exact uniformIntegrable_iff_constantCutoffTailCriterionAux F

end
