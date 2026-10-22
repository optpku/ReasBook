/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Filtration
open scoped ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {μ : Measure Ω} [IsFiniteMeasure μ]

/- Theorem 11.4 is `source-facing`: its hypothesis is the textbook boundedness of the positive
parts. The `core/canonical` owner layer is the `Submartingale` API for `ℱ.limitProcess`. The only
local `bridge/view` needed here is the passage from bounded positive-part expectations to the
owner hypothesis `∀ n, eLpNorm (X n) 1 μ ≤ R`. -/

-- Proof sketch: bounded positive-part expectations and monotonicity of submartingale expectations
-- give a uniform `L¹` bound on `X`, which is exactly the owner input for the canonical
-- `limitProcess` convergence and integrability theorems.
/-- Helper for Theorem 11.4: a submartingale has nondecreasing expectations. -/
private lemma expectationAtZero_le_expectation {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ) (n : ℕ) :
    μ[X 0] ≤ μ[X n] := by
  -- Proof comment: normalize the owner set-integral monotonicity on `univ` to plain expectations.
  simpa [MeasureTheory.setIntegral_univ] using
    hX.setIntegral_le (Nat.zero_le n) MeasurableSet.univ

/-- Helper for Theorem 11.4: bounded positive-part expectations control the negative parts. -/
private lemma negPartExpectationBound_of_bddPosPart {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ) {B : ℝ}
    (hB : ∀ n, μ[fun ω ↦ (X n ω)⁺] ≤ B) (n : ℕ) :
    μ[fun ω ↦ (X n ω)⁻] ≤ B + |μ[X 0]| := by
  have hmono : μ[X 0] ≤ μ[X n] :=
    expectationAtZero_le_expectation hX n
  have hdecomp :
      μ[X n] = μ[fun ω ↦ (X n ω)⁺] - μ[fun ω ↦ (X n ω)⁻] := by
    -- Proof comment: decompose the expectation into the positive and negative parts.
    simpa using integral_eq_integral_pos_part_sub_integral_neg_part (hX.integrable n)
  have hstep : μ[fun ω ↦ (X n ω)⁻] ≤ μ[fun ω ↦ (X n ω)⁺] + |μ[X 0]| := by
    -- Proof comment: rearrange the decomposition and bound `-μ[X 0]` by `|μ[X 0]|`.
    linarith [hmono, hdecomp, neg_le_abs (μ[X 0])]
  exact le_trans hstep (add_le_add (hB n) le_rfl)

private theorem submartingale_eLpNorm_one_bounded_of_bdd_pos_part {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (Set.range fun n ↦ μ[fun ω ↦ (X n ω)⁺])) :
    ∃ R : NNReal, ∀ n, eLpNorm (X n) 1 μ ≤ R := by
  rcases hpos with ⟨B, hBdd⟩
  have hB : ∀ n, μ[fun ω ↦ (X n ω)⁺] ≤ B := by
    intro n
    exact hBdd (Set.mem_range.2 ⟨n, rfl⟩)
  have hB_nonneg : 0 ≤ B := by
    have hpos_nonneg : 0 ≤ μ[fun ω ↦ (X 0 ω)⁺] := by
      refine integral_nonneg_of_ae ?_
      filter_upwards with ω
      exact posPart_nonneg (X 0 ω)
    exact hpos_nonneg.trans (hB 0)
  have hR_nonneg : 0 ≤ 2 * B + |μ[X 0]| := by
    exact add_nonneg (mul_nonneg (by positivity) hB_nonneg) (abs_nonneg _)
  let R : NNReal := ⟨2 * B + |μ[X 0]|, hR_nonneg⟩
  refine ⟨R, fun n ↦ ?_⟩
  have hnegB : μ[fun ω ↦ (X n ω)⁻] ≤ B + |μ[X 0]| :=
    negPartExpectationBound_of_bddPosPart hX hB n
  have hpos_int : Integrable (fun ω ↦ (X n ω)⁺) μ := by
    -- Proof comment: the positive part of an integrable real random variable stays integrable.
    simpa using (hX.integrable n).pos_part
  have hneg_int : Integrable (fun ω ↦ (X n ω)⁻) μ := by
    -- Proof comment: the negative part is handled by the same owner API.
    simpa using (hX.integrable n).neg_part
  have hnorm_eq : ∀ ω, ‖X n ω‖ = (X n ω)⁺ + (X n ω)⁻ := by
    intro ω
    by_cases hω : 0 ≤ X n ω
    · -- Proof comment: on the nonnegative branch, the negative part vanishes.
      rw [Real.norm_eq_abs, abs_of_nonneg hω, posPart_eq_self.2 hω, negPart_eq_zero.2 hω, add_zero]
    · have hω' : X n ω ≤ 0 := le_of_not_ge hω
      -- Proof comment: on the nonpositive branch, the positive part vanishes and the negative
      -- part records `-X n ω`.
      rw [Real.norm_eq_abs, abs_of_nonpos hω', posPart_eq_zero.2 hω', negPart_eq_neg.2 hω',
        zero_add]
  have hnorm_bound : ∫ ω, ‖X n ω‖ ∂μ ≤ 2 * B + |μ[X 0]| := by
    -- Proof comment: rewrite the norm as positive part plus negative part, then apply the two
    -- uniform expectation bounds.
    calc
      ∫ ω, ‖X n ω‖ ∂μ = ∫ ω, ((X n ω)⁺ + (X n ω)⁻) ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards with ω
        exact hnorm_eq ω
      _ = μ[fun ω ↦ (X n ω)⁺] + μ[fun ω ↦ (X n ω)⁻] := by
        rw [integral_add hpos_int hneg_int]
      _ ≤ B + (B + |μ[X 0]|) := add_le_add (hB n) hnegB
      _ = 2 * B + |μ[X 0]| := by ring
  -- Proof comment: convert the real `L¹` bound into the owner `eLpNorm` bound using the canonical
  -- `p = 1` normalization.
  calc
    eLpNorm (X n) 1 μ = ENNReal.ofReal (∫ ω, ‖X n ω‖ ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hX.integrable n)]
    _ ≤ ENNReal.ofReal (2 * B + |μ[X 0]|) :=
      ENNReal.ofReal_le_ofReal hnorm_bound
    _ = R := by
      simpa [R] using (ENNReal.ofReal_eq_coe_nnreal hR_nonneg)

/-- Theorem 11.4: if a real-valued discrete submartingale has uniformly bounded expectations of
its positive parts, then its canonical limit process is integrable and the submartingale converges
to it almost surely. -/
theorem submartingale_convergence_to_integrable_limitProcess_of_bdd_pos_part {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ)
    (hpos : BddAbove (Set.range fun n ↦ μ[fun ω ↦ (X n ω)⁺])) :
    Integrable (ℱ.limitProcess X μ) μ ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω)) := by
  obtain ⟨R, hR⟩ := submartingale_eLpNorm_one_bounded_of_bdd_pos_part hX hpos
  refine ⟨(hX.memLp_limitProcess hR).integrable le_rfl, hX.ae_tendsto_limitProcess hR⟩

-- Proof sketch: the canonical limit object in the previous theorem is `ℱ.limitProcess X μ`; its
-- `⨆ n, ℱ n`-strong measurability is exactly the owner-level `limitProcess` regularity theorem,
-- so no local wrapper is needed here.
/- The canonical limit process of an `L¹`-bounded submartingale is measurable with respect to the
terminal σ-algebra `⨆ n, ℱ n`; the project uses the stronger owner declaration asserting
`StronglyMeasurable[⨆ n, ℱ n]`. -/
recall MeasureTheory.Filtration.stronglyMeasurable_limitProcess
