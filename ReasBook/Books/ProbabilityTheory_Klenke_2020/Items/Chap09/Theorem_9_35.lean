/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Probability.Martingale.Basic
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Theorem_7_9

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search confirmed the Jensen owner via `ConvexOn.map_average_le`; the file uses the
-- conditional-expectation specialization `ConvexOn.map_condExp_le_of_finiteDimensional`.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u v

variable {ι : Type u} {Ω : Type v} [Preorder ι]
variable {m0 : MeasurableSpace Ω}
variable {ℱ : Filtration ι m0} {μ : Measure Ω}

private lemma abs_rpow_convexOn_univ (p : ℝ) (hp : 1 ≤ p) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x| ^ p) := by
  have hrange_abs : (fun x : ℝ ↦ |x|) '' Set.univ = Set.Ici (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact abs_nonneg y
    · intro hx
      exact ⟨x, Set.mem_univ x, abs_of_nonneg hx⟩
  have hrpow : ConvexOn ℝ ((fun x : ℝ ↦ |x|) '' Set.univ) (fun x : ℝ ↦ x ^ p) := by
    simpa [hrange_abs] using convexOn_rpow hp
  have habs : ConvexOn ℝ Set.univ (fun x : ℝ ↦ |x|) := by
    simpa [Real.norm_eq_abs] using
      (convexOn_univ_norm : ConvexOn ℝ Set.univ (norm : ℝ → ℝ))
  simpa using hrpow.comp habs
    (by
      simpa [hrange_abs] using
        (Real.monotoneOn_rpow_Ici_of_exponent_nonneg (le_trans zero_le_one hp)))

section

variable [SigmaFiniteFiltration μ ℱ]

/-- Helper for Theorem 9.35: taking positive parts preserves convexity of a real convex function. -/
private lemma convexOn_posPart_comp {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ (φ x)⁺) := by
  -- The positive part is the pointwise supremum with the zero function.
  simpa [posPart_def] using
    hφ.sup (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ Set.univ))

/-- Helper for Theorem 9.35: Jensen's inequality from Chapter 7 gives integrability of the negative
part of `φ ∘ Y` on a probability space. -/
private lemma integrableNegPartConvexComp {Y : Ω → ℝ} {φ : ℝ → ℝ}
    [IsProbabilityMeasure μ] (hY : Integrable Y μ) (hφ : ConvexOn ℝ Set.univ φ) :
    Integrable (fun ω ↦ (-φ (Y ω))⁺) μ := by
  -- Proof comment: Chapter 7 already shows that the lower integral of the negative part is finite.
  obtain ⟨hneg_fin, -⟩ :=
    convexOn_erealExpectation_comp_ge (P := μ) (I := Set.univ) hY
      (Filter.Eventually.of_forall fun _ ↦ Set.mem_univ _) hφ
  have hφ_cont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  have hmeas : AEStronglyMeasurable (fun ω ↦ (-φ (Y ω))⁺) μ :=
    (continuous_posPart.comp hφ_cont.neg).comp_aestronglyMeasurable hY.aestronglyMeasurable
  -- Proof comment: the integrand is nonnegative, so finite lower integral is exactly integrability.
  exact
    (lintegral_ofReal_ne_top_iff_integrable hmeas
      (Filter.Eventually.of_forall fun _ ↦ posPart_nonneg _)).mp
      (ne_of_lt (by
        simpa [Function.comp_apply, posPart_def] using hneg_fin))

/-- Helper for Theorem 9.35: positive-part integrability and Chapter 7 Jensen together imply full
integrability of `φ ∘ Y`. -/
private lemma integrableConvexCompOfPosPart {Y : Ω → ℝ} {φ : ℝ → ℝ}
    [IsProbabilityMeasure μ] (hY : Integrable Y μ) (hφ : ConvexOn ℝ Set.univ φ)
    (hφ_pos : Integrable (fun ω ↦ (φ (Y ω))⁺) μ) :
    Integrable (fun ω ↦ φ (Y ω)) μ := by
  have hneg : Integrable (fun ω ↦ (-φ (Y ω))⁺) μ := integrableNegPartConvexComp hY hφ
  -- Proof comment: decompose a real-valued function into positive part minus negative part.
  refine (hφ_pos.sub hneg).congr ?_
  filter_upwards with ω
  by_cases hω : 0 ≤ φ (Y ω)
  · have hω_neg : -φ (Y ω) ≤ 0 := by linarith
    simp [posPart_def, hω, hω_neg]
  · have hω' : φ (Y ω) ≤ 0 := le_of_not_ge hω
    have hω_neg : 0 ≤ -φ (Y ω) := by linarith
    simp [posPart_def, hω', hω_neg]

/-- Helper for Theorem 9.35: conditional Jensen and the martingale identity give the
submartingale inequality for `φ ∘ X`. -/
private lemma aeLeCondExpConvexComp {X : ι → Ω → ℝ} {φ : ℝ → ℝ}
    [IsProbabilityMeasure μ] (hX : Martingale X ℱ μ) (hφ : ConvexOn ℝ Set.univ φ)
    (hφ_int : ∀ i, Integrable (fun ω ↦ (φ (X i ω))⁺) μ) {i j : ι} (hij : i ≤ j) :
    (fun ω ↦ φ (X i ω)) ≤ᵐ[μ] μ[fun ω ↦ φ (X j ω) | ℱ i] := by
  have hφ_comp_int : Integrable (fun ω ↦ φ (X j ω)) μ :=
    integrableConvexCompOfPosPart (hX.integrable j) hφ (hφ_int j)
  have hJensen :
      (fun ω ↦ φ (μ[X j | ℱ i] ω)) ≤ᵐ[μ] μ[fun ω ↦ φ (X j ω) | ℱ i] := by
    -- Proof comment: conditional Jensen gives the inequality once `φ ∘ X j` is integrable.
    simpa [Function.comp_apply] using
      hφ.map_condExp_le_of_finiteDimensional
        (ℱ.le i) (hX.integrable j) hφ_comp_int
  -- Proof comment: replace the conditional expectation of `X j` by `X i` using the martingale law.
  filter_upwards [hJensen, hX.condExp_ae_eq hij] with ω hJensenω hcond
  simpa [Function.comp_apply, hcond] using hJensenω

/-- Theorem 9.35 (1): on a probability space, if `X` is a martingale and `φ : ℝ → ℝ` is convex,
then integrability of the positive part of `φ ∘ X_t` at every time implies that the process
`φ(X_t)` is a submartingale. -/
-- Proof sketch: convexity on `ℝ` gives Jensen's inequality for conditional expectation, and the
-- positive-part integrability hypothesis supplies the integrability needed to promote the resulting
-- conditional expectation inequality to the submartingale API.
theorem submartingale_convex_comp {X : ι → Ω → ℝ} {φ : ℝ → ℝ}
    [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ) (hφ : ConvexOn ℝ Set.univ φ)
    (hφ_int : ∀ i, Integrable (fun ω ↦ (φ (X i ω))⁺) μ) :
    Submartingale (fun i ω ↦ φ (X i ω)) ℱ μ := by
  have hφ_cont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: composing the adapted martingale with a continuous map preserves adaptation.
    intro i
    exact hφ_cont.comp_stronglyMeasurable (hX.stronglyMeasurable i)
  · -- Proof comment: the submartingale inequality is exactly the conditional Jensen estimate.
    intro i j hij
    exact aeLeCondExpConvexComp hX hφ hφ_int hij
  · -- Proof comment: positive-part integrability plus Jensen's lower bound yields full
    -- integrability.
    intro i
    exact integrableConvexCompOfPosPart (hX.integrable i) hφ (hφ_int i)

/-- Theorem 9.35 (2): on a probability space, if the time index has a greatest element, then
integrability of the positive part of `φ(X_t)` at the terminal time implies the same integrability
at every earlier time. -/
-- Proof sketch: write each earlier value `X i` as the conditional expectation of the terminal value
-- `X ⊤`, apply Jensen's inequality to the convex map `x ↦ (φ x)⁺`, and conclude by monotonicity of
-- expectation under conditional expectation.
theorem integrable_pos_convex_comp_of_top {X : ι → Ω → ℝ} {φ : ℝ → ℝ} [OrderTop ι]
    [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ) (hφ : ConvexOn ℝ Set.univ φ)
    (hφ_top : Integrable (fun ω ↦ (φ (X ⊤ ω))⁺) μ) :
    ∀ i, Integrable (fun ω ↦ (φ (X i ω))⁺) μ := by
  -- Apply Jensen to the convex positive-part composition at the terminal time.
  have hφ_cont : Continuous φ := continuousOn_univ.1 (hφ.continuousOn isOpen_univ)
  have hψ : ConvexOn ℝ Set.univ (fun x : ℝ ↦ (φ x)⁺) :=
    convexOn_posPart_comp hφ
  have hψ_cont : Continuous (fun x : ℝ ↦ (φ x)⁺) :=
    continuous_posPart.comp hφ_cont
  intro i
  have hφ_top' : Integrable ((fun x : ℝ ↦ (φ x)⁺) ∘ X ⊤) μ := by
    simpa [Function.comp_apply] using hφ_top
  have hJensen :
      (fun ω ↦ (φ (μ[X ⊤ | ℱ i] ω))⁺) ≤ᵐ[μ] μ[((fun x : ℝ ↦ (φ x)⁺) ∘ X ⊤) | ℱ i] :=
    by
      simpa [Function.comp_apply] using
        hψ.map_condExp_le_of_finiteDimensional (ℱ.le i) (hX.integrable ⊤) hφ_top'
  have hBound :
      (fun ω ↦ (φ (X i ω))⁺) ≤ᵐ[μ] μ[((fun x : ℝ ↦ (φ x)⁺) ∘ X ⊤) | ℱ i] := by
    filter_upwards [hJensen, hX.condExp_ae_eq (le_top : i ≤ ⊤)] with ω hJensenω hcond
    simpa [Function.comp_apply, hcond] using hJensenω
  have hMeas : AEStronglyMeasurable (fun ω ↦ (φ (X i ω))⁺) μ :=
    hψ_cont.comp_aestronglyMeasurable (hX.integrable i).aestronglyMeasurable
  -- The Jensen bound dominates the earlier positive part by an integrable conditional expectation.
  exact Integrable.mono_nonneg integrable_condExp hMeas
    (Filter.Eventually.of_forall fun ω ↦ posPart_nonneg _) hBound

/-- Theorem 9.35 (3): on a probability space, if `p ≥ 1` and every `|X_t|^p` is integrable, then
the process `(|X_t|^p)_{t ∈ I}` is a submartingale. -/
-- Proof sketch: specialize part (1) to the convex function `x ↦ |x| ^ p`, using the standard
-- convexity result for `p ≥ 1` together with the assumed integrability of the power process.
theorem submartingale_abs_rpow {X : ι → Ω → ℝ} {p : ℝ}
    [IsProbabilityMeasure μ]
    (hX : Martingale X ℱ μ) (hp : 1 ≤ p)
    (hXp : ∀ i, Integrable (fun ω ↦ |X i ω| ^ p) μ) :
    Submartingale (fun i ω ↦ |X i ω| ^ p) ℱ μ := by
  refine submartingale_convex_comp hX (abs_rpow_convexOn_univ p hp) ?_
  intro i
  convert hXp i using 1
  ext ω
  exact max_eq_left (Real.rpow_nonneg (abs_nonneg _) _)

end
