/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.TotalVariation
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Definition_18_5
import Books.ProbabilityTheory_Klenke_2020.Items.Chap18.Theorem_18_9
import Mathlib

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

/-- The `n`-step law obtained by evolving the initial distribution `μ` under the transition
matrix `p`. -/
def nStepLaw (p : E → E → ℝ≥0∞) [IsMarkovKernel (discreteMatrixKernel p)]
    (μ : ProbabilityMeasure E) (n : ℕ) : ProbabilityMeasure E :=
  let κn : Kernel E E := (discreteMatrixKernel p : Kernel E E) ^ n
  ⟨κn ∘ₘ (μ : Measure E), inferInstance⟩

section SuccessfulCoupling

variable {Ω : Type v} [MeasurableSpace Ω]
variable {p : E → E → ℝ≥0∞}
variable {P : E × E → ProbabilityMeasure Ω} {Z : ℕ → Ω → E × E}

/-- Helper for Theorem 18.12: a successful coupling forces the underlying transition matrix to
define a Markov kernel. -/
private theorem discreteMatrixKernel_isMarkovKernel_of_successfulCoupling
    (hsuccess : IsSuccessfulMarkovCoupling p P Z) :
    IsMarkovKernel (discreteMatrixKernel p) := by
  by_cases hE : IsEmpty E
  · letI : IsEmpty E := hE
    exact discreteMatrixKernel_isMarkovKernel p (by intro x; exact False.elim (isEmptyElim x))
  · have hne : Nonempty E := not_isEmpty_iff.mp hE
    let y : E := Classical.choice hne
    simpa using (hsuccess.fst_realization y).semigroup.isMarkovKernel 1

/-- Helper for Theorem 18.12: bounded test functions are integrable against every evolved law
`nStepLaw p μ n`. -/
private theorem integrable_nStepLaw_of_norm_le_one
    [IsMarkovKernel (discreteMatrixKernel p)]
    {f : E → ℝ} (hf_meas : Measurable f) (hf_bound : ∀ x, ‖f x‖ ≤ 1)
    (μ : ProbabilityMeasure E) (n : ℕ) :
    Integrable f (nStepLaw p μ n : Measure E) := by
  refine Integrable.of_bound hf_meas.aestronglyMeasurable 1 ?_
  exact ae_of_all _ hf_bound

/-- Helper for Theorem 18.12: integrating a bounded observable against the evolved law
`nStepLaw p μ n` is the same as averaging its kernel-row expectations against the initial law
`μ`. -/
private theorem integral_nStepLaw_eq_integral_kernel
    [IsMarkovKernel (discreteMatrixKernel p)]
    {f : E → ℝ} (hf_meas : Measurable f) (hf_bound : ∀ x, ‖f x‖ ≤ 1)
    (μ : ProbabilityMeasure E) (n : ℕ) :
    ∫ z, f z ∂(nStepLaw p μ n : Measure E) =
      ∫ x, ∫ z, f z ∂((discreteMatrixKernel p ^ n) x) ∂(μ : Measure E) := by
  let κn : Kernel E E := discreteMatrixKernel p ^ n
  let κμ : Kernel Unit E := ProbabilityTheory.Kernel.const Unit (μ : Measure E)
  have hcomp : κn ∘ₘ (μ : Measure E) = (κn ∘ₖ κμ) () := by
    simpa [κμ] using
      (MeasureTheory.Measure.comp_eq_comp_const_apply (κ := κn) (μ := (μ : Measure E)))
  have hint : Integrable f ((κn ∘ₖ κμ) ()) := by
    -- Route correction: avoid the unstable `snd_compProd`/`integral_map` route and rewrite the
    -- evolved law as a kernel composition over `Unit`.
    rw [← hcomp]
    simpa [κn, nStepLaw] using (integrable_nStepLaw_of_norm_le_one (p := p) hf_meas hf_bound μ n)
  calc
    ∫ z, f z ∂(nStepLaw p μ n : Measure E)
      = ∫ z, f z ∂(κn ∘ₘ (μ : Measure E)) := by
          simp [κn, nStepLaw]
    _ = ∫ z, f z ∂((κn ∘ₖ κμ) ()) := by
          rw [hcomp]
    _ = ∫ x, ∫ z, f z ∂κn x ∂κμ () := by
          simpa using
            (ProbabilityTheory.Kernel.integral_comp
              (η := κn) (κ := κμ) (a := ()) hint)
    _ = ∫ x, ∫ z, f z ∂((discreteMatrixKernel p ^ n) x) ∂(μ : Measure E) := by
          simp [κn, κμ]

/-- Helper for Theorem 18.12: disagreement event masses under a coupling are probabilities, so
their real values are bounded by `1`. -/
private theorem disagreementProbReal_le_one
    (P : E × E → ProbabilityMeasure Ω) (Z : ℕ → Ω → E × E)
    (n : ℕ) (x y : E) :
    (P (x, y) : Measure Ω).real {ω | (Z n ω).1 ≠ (Z n ω).2} ≤ 1 := by
  have hsubset : {ω | (Z n ω).1 ≠ (Z n ω).2} ⊆ Set.univ := by
    intro ω hω
    simp
  have hle :
      (P (x, y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2} ≤
        (P (x, y) : Measure Ω) Set.univ := by
    exact measure_mono hsubset
  have huniv_eq : (P (x, y) : Measure Ω) Set.univ = 1 := by
    simpa using (measure_univ : (P (x, y) : Measure Ω) Set.univ = 1)
  have huniv_ne_top : (P (x, y) : Measure Ω) Set.univ ≠ ∞ := by
    simpa [huniv_eq]
  -- Proof comment: compare the disagreement event with the whole sample space and then pass from
  -- `ENNReal` mass to real mass using the explicit total-mass identity.
  simpa [Measure.real_def, huniv_eq] using ENNReal.toReal_mono huniv_ne_top hle

/-- Helper for Theorem 18.12: along a successful coupling, the difference of two bounded test
function expectations after `n` steps is controlled by twice the current disagreement
probability. -/
private theorem successfulCoupling_testFunctionDifference_le_twoMul_disagreementProb
    (hsuccess : IsSuccessfulMarkovCoupling p P Z)
    {f : E → ℝ} (hf_meas : Measurable f) (hf_bound : ∀ x, ‖f x‖ ≤ 1)
    (x y : E) (n : ℕ) :
    ∫ z, f z ∂((discreteMatrixKernel p ^ n) x) -
        ∫ z, f z ∂((discreteMatrixKernel p ^ n) y) ≤
      2 * (P (x, y) : Measure Ω).real {ω | (Z n ω).1 ≠ (Z n ω).2} := by
  letI : IsMarkovKernel (discreteMatrixKernel p) :=
    discreteMatrixKernel_isMarkovKernel_of_successfulCoupling (P := P) (Z := Z) hsuccess
  let μΩ : Measure Ω := (P (x, y) : Measure Ω)
  let X₁ : ℕ → Ω → E := fun m ω ↦ (Z m ω).1
  let X₂ : ℕ → Ω → E := fun m ω ↦ (Z m ω).2
  have hreal₁ :
      IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m)
        (fun x' ↦ P (x', y)) X₁ := by
    simpa [X₁] using hsuccess.fst_realization y
  have hreal₂ :
      IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m)
        (fun y' ↦ P (x, y')) X₂ := by
    simpa [X₂] using hsuccess.snd_realization x
  have hcoordInt₁ : Integrable (fun ω ↦ f (X₁ n ω)) μΩ := by
    refine Integrable.of_bound
      ((hf_meas.comp (hreal₁.measurable_process n)).aestronglyMeasurable) 1 ?_
    exact ae_of_all _ fun ω ↦ hf_bound (X₁ n ω)
  have hcoordInt₂ : Integrable (fun ω ↦ f (X₂ n ω)) μΩ := by
    refine Integrable.of_bound
      ((hf_meas.comp (hreal₂.measurable_process n)).aestronglyMeasurable) 1 ?_
    exact ae_of_all _ fun ω ↦ hf_bound (X₂ n ω)
  have hdiffInt : Integrable (fun ω ↦ f (X₁ n ω) - f (X₂ n ω)) μΩ :=
    hcoordInt₁.sub hcoordInt₂
  have hgap :
      ∫ z, f z ∂((discreteMatrixKernel p ^ n) x) -
          ∫ z, f z ∂((discreteMatrixKernel p ^ n) y) =
        μΩ[fun ω ↦ f (X₁ n ω) - f (X₂ n ω)] := by
    calc
      ∫ z, f z ∂((discreteMatrixKernel p ^ n) x) -
          ∫ z, f z ∂((discreteMatrixKernel p ^ n) y)
        = μΩ[fun ω ↦ f (X₁ n ω)] - μΩ[fun ω ↦ f (X₂ n ω)] := by
            rw [show ∫ z, f z ∂((discreteMatrixKernel p ^ n) x) =
                μΩ[fun ω ↦ f (X₁ n ω)] by
                  simpa [μΩ, X₁] using
                    (markovRealization_integral_comp_transition_eq
                      (p := p) (P := fun x' ↦ P (x', y)) (X := X₁) (g := f) x n).symm,
              show ∫ z, f z ∂((discreteMatrixKernel p ^ n) y) =
                μΩ[fun ω ↦ f (X₂ n ω)] by
                  simpa [μΩ, X₂] using
                    (markovRealization_integral_comp_transition_eq
                      (p := p) (P := fun y' ↦ P (x, y')) (X := X₂) (g := f) y n).symm]
      _ = μΩ[fun ω ↦ f (X₁ n ω) - f (X₂ n ω)] := by
            rw [integral_sub hcoordInt₁ hcoordInt₂]
  have habs :
      μΩ[fun ω ↦ |f (X₁ n ω) - f (X₂ n ω)|] ≤
        2 * μΩ.real {ω | X₁ n ω ≠ X₂ n ω} := by
    simpa [X₁, X₂, mul_comm, mul_left_comm, mul_assoc] using
      (integral_abs_coordDifference_le_twoMul_disagreementProb
        (μ := μΩ) (f := f) (X := X₁ n) (Y := X₂ n) (R := 1)
        (hX := hreal₁.measurable_process n) (hY := hreal₂.measurable_process n)
        (hR := by positivity)
        (hbound := fun z ↦ by simpa using hf_bound z)
        (hintegrable := hdiffInt))
  calc
    ∫ z, f z ∂((discreteMatrixKernel p ^ n) x) -
        ∫ z, f z ∂((discreteMatrixKernel p ^ n) y)
      = μΩ[fun ω ↦ f (X₁ n ω) - f (X₂ n ω)] := hgap
    _ ≤ μΩ[fun ω ↦ |f (X₁ n ω) - f (X₂ n ω)|] := by
          exact integral_mono_ae hdiffInt hdiffInt.norm (ae_of_all _ fun ω ↦ le_abs_self _)
    _ ≤ 2 * μΩ.real {ω | X₁ n ω ≠ X₂ n ω} := habs
    _ = 2 * (P (x, y) : Measure Ω).real {ω | (Z n ω).1 ≠ (Z n ω).2} := by
          simp [μΩ, X₁, X₂]

/-- Helper for Theorem 18.12: averaging the pointwise coupling estimate over two initial laws
controls the dual test-function gap between the evolved laws. -/
private theorem averagedTestFunctionDifference_le_twoMul_disagreementAverage
    [IsMarkovKernel (discreteMatrixKernel p)]
    (hsuccess : IsSuccessfulMarkovCoupling p P Z)
    (μ ν : ProbabilityMeasure E)
    {f : E → ℝ} (hf_meas : Measurable f) (hf_bound : ∀ x, ‖f x‖ ≤ 1)
    (n : ℕ) :
    ∫ z, f z ∂(nStepLaw p μ n : Measure E) -
        ∫ z, f z ∂(nStepLaw p ν n : Measure E) ≤
      2 * ∫ x, ∫ y,
          (P (x, y) : Measure Ω).real {ω | (Z n ω).1 ≠ (Z n ω).2}
        ∂(ν : Measure E) ∂(μ : Measure E) := by
  letI : IsMarkovKernel (discreteMatrixKernel p) :=
    discreteMatrixKernel_isMarkovKernel_of_successfulCoupling (P := P) (Z := Z) hsuccess
  let a : E → ℝ := fun x ↦ ∫ z, f z ∂((discreteMatrixKernel p ^ n) x)
  let D : E → E → ℝ := fun x y ↦
    (P (x, y) : Measure Ω).real {ω | (Z n ω).1 ≠ (Z n ω).2}
  have ha_bound : ∀ x, ‖a x‖ ≤ 1 := by
    intro x
    simpa [a] using
      (norm_integral_le_of_norm_le_const
        (μ := ((discreteMatrixKernel p ^ n) x)) (C := 1) (ae_of_all _ hf_bound))
  have ha_intμ : Integrable a (μ : Measure E) := by
    refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 1 ?_
    exact ae_of_all _ ha_bound
  have ha_intν : Integrable a (ν : Measure E) := by
    refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 1 ?_
    exact ae_of_all _ ha_bound
  have hD_nonneg : ∀ x y, 0 ≤ D x y := by
    intro x y
    exact ENNReal.toReal_nonneg
  have hD_le_one : ∀ x y, D x y ≤ 1 := by
    intro x y
    simpa [D] using disagreementProbReal_le_one (P := P) (Z := Z) n x y
  have hInnerAvgInt :
      ∀ x, Integrable (fun y ↦ 2 * D x y) (ν : Measure E) := by
    intro x
    refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 2 ?_
    exact ae_of_all _ fun y ↦ by
      have hDy := hD_le_one x y
      have hDy_nonneg := hD_nonneg x y
      have hnorm : ‖2 * D x y‖ = 2 * D x y := by
        rw [Real.norm_of_nonneg]
        positivity
      rw [hnorm]
      nlinarith
  have hAverageInt :
      Integrable
        (fun x ↦ ∫ y, 2 * D x y ∂(ν : Measure E))
        (μ : Measure E) := by
    refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 2 ?_
    exact ae_of_all _ fun x ↦ by
      have hnonneg :
          0 ≤ ∫ y, 2 * D x y ∂(ν : Measure E) := by
        exact MeasureTheory.integral_nonneg_of_ae <|
          ae_of_all _ fun y ↦ mul_nonneg (by norm_num) (hD_nonneg x y)
      have hle :
          ∫ y, 2 * D x y ∂(ν : Measure E) ≤ 2 := by
        have hmono :
            ∫ y, 2 * D x y ∂(ν : Measure E) ≤ ∫ y, (2 : ℝ) ∂(ν : Measure E) :=
          integral_mono_ae
            (hInnerAvgInt x)
            (integrable_const 2)
            (ae_of_all _ fun y ↦ by
              have hDy := hD_le_one x y
              nlinarith)
        simpa using hmono
      simpa [Real.norm_of_nonneg hnonneg] using hle
  have hDInnerInt : ∀ x, Integrable (fun y ↦ D x y) (ν : Measure E) := by
    intro x
    refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 1 ?_
    exact ae_of_all _ fun y ↦ by
      have hDy_nonneg := hD_nonneg x y
      have hDy := hD_le_one x y
      simpa [Real.norm_of_nonneg hDy_nonneg] using hDy
  have hDAverageInt :
      Integrable
        (fun x ↦ ∫ y, D x y ∂(ν : Measure E))
        (μ : Measure E) := by
    refine Integrable.of_bound (Measurable.of_discrete.aestronglyMeasurable) 1 ?_
    exact ae_of_all _ fun x ↦ by
      have hnonneg :
          0 ≤ ∫ y, D x y ∂(ν : Measure E) := by
        exact MeasureTheory.integral_nonneg_of_ae <| ae_of_all _ fun y ↦ hD_nonneg x y
      have hle :
          ∫ y, D x y ∂(ν : Measure E) ≤ 1 := by
        have hmono :
            ∫ y, D x y ∂(ν : Measure E) ≤ ∫ y, (1 : ℝ) ∂(ν : Measure E) :=
          integral_mono_ae
            (hDInnerInt x)
            (integrable_const 1)
            (ae_of_all _ fun y ↦ hD_le_one x y)
        simpa using hmono
      simpa [Real.norm_of_nonneg hnonneg] using hle
  calc
    ∫ z, f z ∂(nStepLaw p μ n : Measure E) -
        ∫ z, f z ∂(nStepLaw p ν n : Measure E)
      = ∫ x, a x - ∫ y, a y ∂(ν : Measure E) ∂(μ : Measure E) := by
          rw [integral_nStepLaw_eq_integral_kernel (p := p) hf_meas hf_bound μ n,
            integral_nStepLaw_eq_integral_kernel (p := p) hf_meas hf_bound ν n,
            integral_sub ha_intμ (integrable_const _)]
          simp [a]
    _ ≤ ∫ x, ∫ y, 2 * D x y ∂(ν : Measure E) ∂(μ : Measure E) := by
          refine integral_mono_ae (ha_intμ.sub (integrable_const _)) hAverageInt ?_
          exact ae_of_all _ fun x ↦ by
            have hxeq :
                a x - ∫ y, a y ∂(ν : Measure E) =
                  ∫ y, (a x - a y) ∂(ν : Measure E) := by
              rw [integral_sub (integrable_const _) ha_intν]
              simp
            -- Proof comment: freeze the centered identity before applying the pointwise
            -- successful-coupling estimate inside the inner integral.
            have hpoint :
                a x - ∫ y, a y ∂(ν : Measure E) ≤ ∫ y, 2 * D x y ∂(ν : Measure E) := by
              rw [hxeq]
              exact integral_mono_ae
                ((integrable_const _).sub ha_intν)
                (hInnerAvgInt x)
                (ae_of_all _ fun y ↦ by
                  simpa [a, D] using
                    (successfulCoupling_testFunctionDifference_le_twoMul_disagreementProb
                      (P := P) (Z := Z) (hsuccess := hsuccess) hf_meas hf_bound x y n))
            simpa using hpoint
    _ = 2 * ∫ x, ∫ y,
          (P (x, y) : Measure Ω).real {ω | (Z n ω).1 ≠ (Z n ω).2}
        ∂(ν : Measure E) ∂(μ : Measure E) := by
          calc
            ∫ x, ∫ y, 2 * D x y ∂(ν : Measure E) ∂(μ : Measure E)
              = ∫ x, 2 * ∫ y, D x y ∂(ν : Measure E) ∂(μ : Measure E) := by
                  refine integral_congr_ae <| ae_of_all _ fun x ↦ ?_
                  have hpoint :
                      ∫ y, 2 * D x y ∂(ν : Measure E) =
                        2 * ∫ y, D x y ∂(ν : Measure E) := by
                    rw [integral_const_mul]
                  simpa using hpoint
            _ = 2 * ∫ x, ∫ y, D x y ∂(ν : Measure E) ∂(μ : Measure E) := by
                  rw [integral_const_mul]
            _ = 2 * ∫ x, ∫ y,
                  (P (x, y) : Measure Ω).real {ω | (Z n ω).1 ≠ (Z n ω).2}
                ∂(ν : Measure E) ∂(μ : Measure E) := by
                  simp [D]

/-- Theorem 18.12: if the transition matrix `p` admits a successful coupling, then the total
variation distance between the `n`-step laws started from any two initial distributions tends to
`0`. -/
theorem nStepTotalVariationDistance_tendsto_zero_of_hasSuccessfulCoupling
    [IsMarkovKernel (discreteMatrixKernel p)]
    (hcoupling : HasSuccessfulCoupling p) (μ ν : ProbabilityMeasure E) :
    Tendsto
      (fun n : ℕ ↦ totalVariationDistance (nStepLaw p μ n) (nStepLaw p ν n))
      atTop (𝓝 0) := by
  rcases hcoupling.exists_successfulCoupling with ⟨Ω, mΩ, P, Z, hsuccess⟩
  letI : IsMarkovKernel (discreteMatrixKernel p) :=
    discreteMatrixKernel_isMarkovKernel_of_successfulCoupling (P := P) (Z := Z) hsuccess
  let D : ℕ → E → E → ℝ := fun n x y ↦
    (P (x, y) : Measure Ω).real {ω | (Z n ω).1 ≠ (Z n ω).2}
  let G : ℕ → E → ℝ := fun n x ↦ ∫ y, D n x y ∂(ν : Measure E)
  have hD_nonneg : ∀ n x y, 0 ≤ D n x y := by
    intro n x y
    exact ENNReal.toReal_nonneg
  have hD_le_one : ∀ n x y, D n x y ≤ 1 := by
    intro n x y
    simpa [D] using disagreementProbReal_le_one (P := P) (Z := Z) n x y
  have hD_tendsto : ∀ x y, Tendsto (fun n : ℕ ↦ D n x y) atTop (𝓝 0) := by
    intro x y
    simpa [D, Measure.real] using
      ((ENNReal.tendsto_toReal_zero_iff
        (fun n ↦ measure_ne_top (P (x, y) : Measure Ω) {ω | (Z n ω).1 ≠ (Z n ω).2})).2
        (successfulCoupling_disagreementProb_tendsto_zero
          (Ω := Ω) (p := p) (P := P) (Z := Z) hsuccess x y))
  have hG_tendsto : ∀ x, Tendsto (fun n : ℕ ↦ G n x) atTop (𝓝 0) := by
    intro x
    simpa [G] using
      (MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun _ : E ↦ (1 : ℝ))
        (F_measurable := fun n ↦
          (Measurable.of_discrete : Measurable (D n x)).aestronglyMeasurable)
        (bound_integrable := integrable_const 1)
        (h_bound := fun n ↦
          ae_of_all _ fun y ↦ by
            have hDy_nonneg := hD_nonneg n x y
            have hDy := hD_le_one n x y
            simpa [Real.norm_of_nonneg hDy_nonneg] using hDy)
        (h_lim := ae_of_all _ fun y ↦ hD_tendsto x y))
  have hAverage_tendsto :
      Tendsto (fun n : ℕ ↦ ∫ x, G n x ∂(μ : Measure E)) atTop (𝓝 0) := by
    simpa [G] using
      (MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun _ : E ↦ (1 : ℝ))
        (F_measurable := fun n ↦
          (Measurable.of_discrete : Measurable (G n)).aestronglyMeasurable)
        (bound_integrable := integrable_const 1)
        (h_bound := fun n ↦
          ae_of_all _ fun x ↦ by
            have hIntDx : Integrable (fun y ↦ D n x y) (ν : Measure E) := by
              refine Integrable.of_bound
                (Measurable.of_discrete.aestronglyMeasurable) 1 ?_
              exact ae_of_all _ fun y ↦ by
                have hDy_nonneg := hD_nonneg n x y
                have hDy := hD_le_one n x y
                simpa [Real.norm_of_nonneg hDy_nonneg] using hDy
            have hnonneg : 0 ≤ G n x := by
              simpa [G] using
                (MeasureTheory.integral_nonneg_of_ae <|
                  ae_of_all _ fun y ↦ hD_nonneg n x y)
            have hle : G n x ≤ 1 := by
              have hmono :
                  ∫ y, D n x y ∂(ν : Measure E) ≤ ∫ y, (1 : ℝ) ∂(ν : Measure E) :=
                integral_mono_ae
                  hIntDx
                  (integrable_const 1)
                  (ae_of_all _ fun y ↦ hD_le_one n x y)
              simpa [G] using hmono
            simpa [Real.norm_of_nonneg hnonneg] using hle)
        (h_lim := ae_of_all _ fun x ↦ hG_tendsto x))
  have htv_le :
      ∀ n : ℕ,
        totalVariationDistance (nStepLaw p μ n) (nStepLaw p ν n) ≤
          ∫ x, G n x ∂(μ : Measure E) := by
    intro n
    let S : Set ℝ := {r : ℝ | ∃ f : E → ℝ,
      Measurable f ∧
        (∀ x, ‖f x‖ ≤ 1) ∧
        r = ∫ x, f x ∂(nStepLaw p μ n : Measure E) -
          ∫ x, f x ∂(nStepLaw p ν n : Measure E)}
    have hzero_mem : 0 ∈ S := by
      exact ⟨fun _ : E ↦ 0, measurable_const, by intro x; simp, by simp⟩
    have hS_nonempty : S.Nonempty := ⟨0, hzero_mem⟩
    have hupper : ∀ {r : ℝ}, r ∈ S → r ≤ 2 * ∫ x, G n x ∂(μ : Measure E) := by
      intro r hr
      rcases hr with ⟨f, hf_meas, hf_bound, rfl⟩
      simpa [G, D] using
        (averagedTestFunctionDifference_le_twoMul_disagreementAverage
          (P := P) (Z := Z) (hsuccess := hsuccess) μ ν hf_meas hf_bound n)
    have hsSup_le : sSup S ≤ 2 * ∫ x, G n x ∂(μ : Measure E) := by
      exact csSup_le hS_nonempty fun r hr ↦ hupper hr
    rw [totalVariationDistance_eq_sSup_bounded_measurable]
    change sSup S / 2 ≤ ∫ x, G n x ∂(μ : Measure E)
    nlinarith
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAverage_tendsto
    (fun n ↦ by
      rw [totalVariationDistance_eq_half_totalVariationNorm]
      positivity) htv_le

end SuccessfulCoupling

end ProbabilityTheory
