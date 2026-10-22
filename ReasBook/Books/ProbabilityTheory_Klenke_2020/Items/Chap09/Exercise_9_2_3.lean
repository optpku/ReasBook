/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Probability.Martingale.Basic
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_9

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u v

variable {ι : Type u} {Ω : Type v} [Preorder ι]
variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ι m0} {μ : Measure Ω}

-- Proof sketch: combine the submartingale inequality `X s ≤ E[X t | ℱ s]` with conditional
-- Jensen for the convex map `φ`; monotonicity of `φ` lets one pass from `X s ≤ E[X t | ℱ s]` to
-- `φ (X s) ≤ φ (E[X t | ℱ s])`, and the positive-part integrability assumption upgrades the
-- resulting a.e. inequality to the submartingale API.
section

variable [SigmaFiniteFiltration μ ℱ]

/-- Helper for Exercise 9.2.3: Chapter 7 Jensen gives integrability of the negative part of
`φ ∘ Y` on a probability space. -/
private lemma integrableNegPartConvexComp {Y : Ω → ℝ} {φ : ℝ → ℝ}
    [IsProbabilityMeasure μ] (hY : Integrable Y μ) (hφ : ConvexOn ℝ Set.univ φ) :
    Integrable (fun ω ↦ (-φ (Y ω))⁺) μ := by
  -- Proof comment: Chapter 7 already bounds the lower integral of the negative part.
  obtain ⟨hneg_fin, -⟩ :=
    convexOn_erealExpectation_comp_ge (P := μ) (I := Set.univ) hY
      (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _) hφ
  have hφ_cont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  have hmeas : AEStronglyMeasurable (fun ω ↦ (-φ (Y ω))⁺) μ :=
    (continuous_posPart.comp hφ_cont.neg).comp_aestronglyMeasurable hY.aestronglyMeasurable
  -- Proof comment: for a nonnegative real integrand, finite lower integral is integrability.
  exact
    (lintegral_ofReal_ne_top_iff_integrable hmeas
      (Filter.Eventually.of_forall fun _ ↦ posPart_nonneg _)).mp
      (ne_of_lt (by
        simpa [Function.comp_apply, posPart_def] using hneg_fin))

/-- Helper for Exercise 9.2.3: positive-part integrability upgrades `φ ∘ Y` to full
integrability. -/
private lemma integrableConvexCompOfPosPart {Y : Ω → ℝ} {φ : ℝ → ℝ}
    [IsProbabilityMeasure μ] (hY : Integrable Y μ) (hφ : ConvexOn ℝ Set.univ φ)
    (hφ_pos : Integrable (fun ω ↦ (φ (Y ω))⁺) μ) :
    Integrable (fun ω ↦ φ (Y ω)) μ := by
  have hneg : Integrable (fun ω ↦ (-φ (Y ω))⁺) μ :=
    integrableNegPartConvexComp hY hφ
  -- Proof comment: `φ ∘ Y` is the difference between its positive and negative parts.
  refine (hφ_pos.sub hneg).congr ?_
  filter_upwards with ω
  by_cases hω : 0 ≤ φ (Y ω)
  · have hω_neg : -φ (Y ω) ≤ 0 := by linarith
    simp [posPart_def, hω, hω_neg]
  · have hω' : φ (Y ω) ≤ 0 := le_of_not_ge hω
    have hω_neg : 0 ≤ -φ (Y ω) := by linarith
    simp [posPart_def, hω', hω_neg]

/-- Helper for Exercise 9.2.3: the submartingale inequality for `X`, monotonicity of `φ`, and
conditional Jensen imply the submartingale inequality for `φ ∘ X`. -/
private lemma aeLeCondExpConvexMonotoneComp {X : ι → Ω → ℝ} {φ : ℝ → ℝ}
    [IsProbabilityMeasure μ] (hX : Submartingale X ℱ μ) (hφ : ConvexOn ℝ Set.univ φ)
    (hφ_mono : Monotone φ)
    (hφ_int : ∀ i, Integrable (fun ω ↦ (φ (X i ω))⁺) μ) {i j : ι} (hij : i ≤ j) :
    (fun ω ↦ φ (X i ω)) ≤ᵐ[μ] μ[fun ω ↦ φ (X j ω) | ℱ i] := by
  have hφ_comp_int : Integrable (fun ω ↦ φ (X j ω)) μ :=
    integrableConvexCompOfPosPart (hX.integrable j) hφ (hφ_int j)
  have hmono_ae :
      (fun ω ↦ φ (X i ω)) ≤ᵐ[μ] fun ω ↦ φ (μ[X j | ℱ i] ω) := by
    -- Proof comment: monotonicity transports the submartingale inequality through `φ`.
    filter_upwards [hX.ae_le_condExp hij] with ω hω
    exact hφ_mono hω
  have hJensen :
      (fun ω ↦ φ (μ[X j | ℱ i] ω)) ≤ᵐ[μ] μ[fun ω ↦ φ (X j ω) | ℱ i] := by
    -- Proof comment: conditional Jensen handles the convex step at time `j`.
    simpa [Function.comp_apply] using
      hφ.map_condExp_le_of_finiteDimensional
        (ℱ.le i) (hX.integrable j) hφ_comp_int
  exact hmono_ae.trans hJensen

-- Semantic search and the Chapter 9 owner `submartingale_convex_comp` confirm that this exercise
-- keeps the probability-space hypothesis from Theorem 9.35.
/-- Exercise 9.2.3 (1): on a probability space, if `X` is a submartingale and
`φ : ℝ → ℝ` is convex and monotone increasing, then integrability of the positive
part of `φ ∘ X_t` at every time implies that the process `φ(X_t)` is a
submartingale. -/
theorem submartingale_convex_monotone_comp {X : ι → Ω → ℝ} {φ : ℝ → ℝ}
    [IsProbabilityMeasure μ]
    (hX : Submartingale X ℱ μ) (hφ : ConvexOn ℝ Set.univ φ) (hφ_mono : Monotone φ)
    (hφ_int : ∀ i, Integrable (fun ω ↦ (φ (X i ω))⁺) μ) :
    Submartingale (fun i ω ↦ φ (X i ω)) ℱ μ := by
  have hφ_cont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: composition with the continuous map `φ` preserves adaptedness.
    intro i
    exact hφ_cont.comp_stronglyMeasurable (hX.stronglyMeasurable i)
  · -- Proof comment: monotonicity upgrades the submartingale inequality to the Jensen input.
    intro i j hij
    exact aeLeCondExpConvexMonotoneComp hX hφ hφ_mono hφ_int hij
  · -- Proof comment: positive-part integrability plus the negative-part estimate gives
    -- integrability of `φ ∘ X i`.
    intro i
    exact integrableConvexCompOfPosPart (hX.integrable i) hφ (hφ_int i)

end

/-- The deterministic two-time process taking the values `-1` and then `0` on the one-point
probability space. -/
def square_counterexample_process : Fin 2 → PUnit → ℝ
  | 0, _ => -1
  | 1, _ => 0

/-- The trivial two-time filtration on the one-point measurable space used for the monotonicity
counterexample. -/
abbrev square_counterexample_filtration : Filtration (Fin 2) (⊤ : MeasurableSpace PUnit) := ⊥

/-- The Dirac probability measure at the unique point of `PUnit`. -/
abbrev square_counterexample_measure : Measure PUnit := Measure.dirac PUnit.unit

-- Proof sketch: on the one-point space with the trivial filtration, conditional expectations are
-- ordinary values. The deterministic path `-1 ≤ 0` therefore defines a submartingale.
/-- The deterministic two-time process `(-1, 0)` is a submartingale on the one-point space. -/
theorem square_counterexample_process_submartingale :
    Submartingale square_counterexample_process square_counterexample_filtration
      square_counterexample_measure := by
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: every time slice is a constant function on the one-point space.
    simpa [square_counterexample_process] using
      (stronglyAdapted_const' square_counterexample_filtration
        (fun i : Fin 2 ↦ square_counterexample_process i PUnit.unit))
  · -- Proof comment: conditional expectations of constants are constant, so only the scalar
    -- inequalities `-1 ≤ -1`, `-1 ≤ 0`, and `0 ≤ 0` remain.
    intro i j hij
    fin_cases i <;> fin_cases j
    · have hce :
          square_counterexample_measure[square_counterexample_process 0 |
            square_counterexample_filtration 0] = square_counterexample_process 0 := by
        simpa only [square_counterexample_process] using
          (condExp_const (μ := square_counterexample_measure)
            (m := square_counterexample_filtration 0)
            (square_counterexample_filtration.le 0) (-1 : ℝ))
      have hce_dirac :
          (Measure.dirac PUnit.unit)[square_counterexample_process 0 |
            square_counterexample_filtration 0] = square_counterexample_process 0 := by
        simpa [square_counterexample_measure] using hce
      have hpoint :
          square_counterexample_process 0 PUnit.unit ≤
            ((Measure.dirac PUnit.unit)[square_counterexample_process 0 |
              square_counterexample_filtration 0]) PUnit.unit := by
        rw [hce_dirac]
      have hpure :
          square_counterexample_process 0 ≤ᶠ[pure PUnit.unit]
            (Measure.dirac PUnit.unit)[square_counterexample_process 0 |
              square_counterexample_filtration 0] := by
        simpa using hpoint
      simpa [square_counterexample_measure, ae_dirac_eq] using hpure
    · have hce :
          square_counterexample_measure[square_counterexample_process 1 |
            square_counterexample_filtration 0] = square_counterexample_process 1 := by
        simpa only [square_counterexample_process] using
          (condExp_const (μ := square_counterexample_measure)
            (m := square_counterexample_filtration 0)
            (square_counterexample_filtration.le 0) (0 : ℝ))
      have hce_dirac :
          (Measure.dirac PUnit.unit)[square_counterexample_process 1 |
            square_counterexample_filtration 0] = square_counterexample_process 1 := by
        simpa [square_counterexample_measure] using hce
      have hpoint :
          square_counterexample_process 0 PUnit.unit ≤
            ((Measure.dirac PUnit.unit)[square_counterexample_process 1 |
              square_counterexample_filtration 0]) PUnit.unit := by
        rw [hce_dirac]
        norm_num [square_counterexample_process]
      have hpure :
          square_counterexample_process 0 ≤ᶠ[pure PUnit.unit]
            (Measure.dirac PUnit.unit)[square_counterexample_process 1 |
              square_counterexample_filtration 0] := by
        simpa using hpoint
      simpa [square_counterexample_measure, ae_dirac_eq] using hpure
    · exact False.elim ((not_le_of_gt (show (0 : Fin 2) < 1 by decide)) hij)
    · have hce :
          square_counterexample_measure[square_counterexample_process 1 |
            square_counterexample_filtration 1] = square_counterexample_process 1 := by
        simpa only [square_counterexample_process] using
          (condExp_const (μ := square_counterexample_measure)
            (m := square_counterexample_filtration 1)
            (square_counterexample_filtration.le 1) (0 : ℝ))
      have hce_dirac :
          (Measure.dirac PUnit.unit)[square_counterexample_process 1 |
            square_counterexample_filtration 1] = square_counterexample_process 1 := by
        simpa [square_counterexample_measure] using hce
      have hpoint :
          square_counterexample_process 1 PUnit.unit ≤
            ((Measure.dirac PUnit.unit)[square_counterexample_process 1 |
              square_counterexample_filtration 1]) PUnit.unit := by
        rw [hce_dirac]
      have hpure :
          square_counterexample_process 1 ≤ᶠ[pure PUnit.unit]
            (Measure.dirac PUnit.unit)[square_counterexample_process 1 |
              square_counterexample_filtration 1] := by
        simpa using hpoint
      simpa [square_counterexample_measure, ae_dirac_eq] using hpure
  · -- Proof comment: each slice is constant, hence integrable.
    intro i
    fin_cases i
    · simpa [square_counterexample_process] using
        (integrable_const (-1 : ℝ))
    · simpa [square_counterexample_process] using
        (integrable_const (0 : ℝ))

-- Proof sketch: `x ↦ x^2` is convex on `ℝ` by the standard polynomial convexity criterion.
/-- The square map is convex on all of `ℝ`. -/
theorem square_counterexample_function_convex :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ x ^ 2) := by
  -- Proof comment: the square map is the even power `x ↦ x^2`.
  simpa using (show ConvexOn ℝ Set.univ (fun x : ℝ ↦ x ^ (2 : ℕ)) from
    (show Even (2 : ℕ) from by decide).convexOn_pow)

-- Proof sketch: compare the values at `-1` and `0`; monotonicity would force
-- `(-1)^2 ≤ 0^2`, which is false.
/-- The square map is not monotone increasing on `ℝ`. -/
theorem square_counterexample_function_not_monotone :
    ¬ Monotone (fun x : ℝ ↦ x ^ 2) := by
  intro hmono
  -- Proof comment: monotonicity would send `-1 ≤ 0` to the false inequality `1 ≤ 0`.
  have hbad : ((-1 : ℝ) ^ 2) ≤ (0 : ℝ) ^ 2 :=
    hmono (show (-1 : ℝ) ≤ 0 by norm_num)
  norm_num at hbad

-- Proof sketch: the one-point measure turns integrability into finiteness of a single real value,
-- and the transformed process only takes the values `1` and `0`.
/-- The positive part of the transformed counterexample process is integrable at each time. -/
theorem square_counterexample_comp_pos_integrable :
    ∀ i, Integrable
      (fun ω ↦ ((square_counterexample_process i ω) ^ 2)⁺)
      square_counterexample_measure := by
  intro i
  -- Proof comment: after squaring, each slice is again a constant function.
  fin_cases i
  · simpa [square_counterexample_process] using
      (integrable_const (1 : ℝ))
  · simpa [square_counterexample_process] using
      (integrable_const (0 : ℝ))

-- Proof sketch: after applying `x ↦ x^2`, the deterministic path becomes `1` then `0`, so the
-- one-step submartingale inequality fails already at times `0 ≤ 1`.
/-- Exercise 9.2.3 (2): the deterministic two-time submartingale `(-1, 0)` on the one-point
space together with the convex but nonmonotone map `x ↦ x^2` shows that monotonicity of `φ` is
essential, because the transformed process is not a submartingale. -/
theorem square_counterexample_transform_not_submartingale :
    ¬ Submartingale
      (fun i ω ↦ (square_counterexample_process i ω) ^ 2)
      square_counterexample_filtration square_counterexample_measure := by
  intro hsq
  have hineq :
      (fun ω ↦ (square_counterexample_process 0 ω) ^ 2) ≤ᵐ[square_counterexample_measure]
        square_counterexample_measure[fun ω ↦ (square_counterexample_process 1 ω) ^ 2 |
          square_counterexample_filtration 0] :=
    hsq.ae_le_condExp (i := 0) (j := 1) (by decide)
  have hce :
      square_counterexample_measure[fun ω ↦ (square_counterexample_process 1 ω) ^ 2 |
        square_counterexample_filtration 0] = fun _ : PUnit ↦ 0 := by
    convert
      (condExp_const (μ := square_counterexample_measure)
        (m := square_counterexample_filtration 0)
        (square_counterexample_filtration.le 0) (0 : ℝ)) using 1
    ext ω
    simp [square_counterexample_process]
  have hce_dirac :
      (Measure.dirac PUnit.unit)[fun ω ↦ (square_counterexample_process 1 ω) ^ 2 |
        square_counterexample_filtration 0] = fun _ : PUnit ↦ 0 := by
    simpa [square_counterexample_measure] using hce
  have hineq_pure :
      (fun ω ↦ (square_counterexample_process 0 ω) ^ 2) ≤ᶠ[pure PUnit.unit]
        (Measure.dirac PUnit.unit)[fun ω ↦ (square_counterexample_process 1 ω) ^ 2 |
          square_counterexample_filtration 0] := by
    simpa [square_counterexample_measure, ae_dirac_eq] using hineq
  have hbad : (1 : ℝ) ≤ 0 := by
    -- Proof comment: after rewriting the conditional expectation, the failed step is `1 ≤ 0`.
    have hpoint :
        (square_counterexample_process 0 PUnit.unit) ^ 2 ≤
          ((Measure.dirac PUnit.unit)[fun ω ↦ (square_counterexample_process 1 ω) ^ 2 |
            square_counterexample_filtration 0]) PUnit.unit := by
      simpa using hineq_pure
    rw [hce_dirac] at hpoint
    simpa [square_counterexample_process] using hpoint
  norm_num at hbad
