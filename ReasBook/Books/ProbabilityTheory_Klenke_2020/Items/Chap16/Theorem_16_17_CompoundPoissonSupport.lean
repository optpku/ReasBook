/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_3

open MeasureTheory ProbabilityTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- Helper for Theorem 16.17: restrict a finite measure on `ℝ \ {0}` to the punctured line. -/
noncomputable def puncturedIntensity (ν : FiniteMeasure ℝ) :
    FiniteMeasure {x : ℝ // x ≠ 0} :=
  (ν.restrict ({0}ᶜ : Set ℝ)).comap Subtype.val

/-- Helper for Theorem 16.17: mapping the punctured restriction back along `Subtype.val`
recovers the original finite measure restricted away from `0`. -/
theorem puncturedIntensity_map_subtypeVal (ν : FiniteMeasure ℝ) :
    (puncturedIntensity ν).map Subtype.val = ν.restrict ({0}ᶜ : Set ℝ) := by
  apply FiniteMeasure.toMeasure_injective
  -- Proof comment: `map` after `comap` along the subtype inclusion recovers the restricted
  -- measure.
  simpa [puncturedIntensity] using
    (map_comap_subtype_coe (s := ({0}ᶜ : Set ℝ)) (measurableSet_singleton (0 : ℝ)).compl
      (((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ))))

/-- Helper for Theorem 16.17: removing the atom at `0` from the intensity does not change the
compound-Poisson law. -/
theorem compoundPoissonMeasure_ignoreZeroAtom (ν : FiniteMeasure ℝ) :
    compoundPoissonMeasure ((puncturedIntensity ν).map Subtype.val) = compoundPoissonMeasure ν := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext_of_charFun
  funext t
  let f : ℝ → ℂ := fun x ↦ Complex.exp (t * x * Complex.I) - 1
  have hfInt : Integrable f (μ := (ν : Measure ℝ)) := by
    refine Integrable.of_bound (by fun_prop) 2 ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      have hnormExp : ‖Complex.exp (t * x * Complex.I)‖ = 1 := by
        simpa using Complex.norm_exp_ofReal_mul_I (t * x)
      calc
        ‖f x‖ = ‖Complex.exp (t * x * Complex.I) - 1‖ := rfl
        _ ≤ ‖Complex.exp (t * x * Complex.I)‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by
          rw [hnormExp]
          norm_num
  have hfIntCompl : Integrable f (μ := ((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ))) :=
    hfInt.mono_measure Measure.restrict_le_self
  have hfIntZero : Integrable f (μ := ((ν : Measure ℝ).restrict ({0} : Set ℝ))) :=
    hfInt.mono_measure Measure.restrict_le_self
  have hsplit :
      ((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) + ((ν : Measure ℝ).restrict ({0} : Set ℝ)) =
        (ν : Measure ℝ) := by
    simpa using
      (Measure.restrict_add_restrict_compl (μ := (ν : Measure ℝ))
        (s := ({0}ᶜ : Set ℝ)) ((measurableSet_singleton (0 : ℝ)).compl))
  have hsingleton :
      ∫ x, f x ∂((ν : Measure ℝ).restrict ({0} : Set ℝ)) = 0 := by
    rw [Measure.restrict_singleton, integral_smul_measure, integral_dirac]
    simp [f]
  rw [charFun_compoundPoissonMeasure, charFun_compoundPoissonMeasure,
    puncturedIntensity_map_subtypeVal]
  congr 1
  -- Proof comment: the Lévy exponent is unchanged because the integrand vanishes at the deleted
  -- atom.
  calc
    ∫ x, f x ∂((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ))
        = ∫ x, f x ∂((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) + 0 := by
            rw [add_zero]
    _ = ∫ x, f x ∂((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) +
          ∫ x, f x ∂((ν : Measure ℝ).restrict ({0} : Set ℝ)) := by
            rw [hsingleton]
    _ = ∫ x, f x ∂(((ν : Measure ℝ).restrict ({0}ᶜ : Set ℝ)) +
          ((ν : Measure ℝ).restrict ({0} : Set ℝ))) := by
            symm
            exact integral_add_measure hfIntCompl hfIntZero
    _ = ∫ x, f x ∂(ν : Measure ℝ) := by rw [hsplit]

/-- Helper for Theorem 16.17: scaling a probability law by `n` in the compound-Poisson intensity
turns its characteristic function into the centered exponential form. -/
theorem charFun_compoundPoissonMeasure_natSmulProbability
    (ρ : ProbabilityMeasure ℝ) (n : ℕ) (t : ℝ) :
    charFun (compoundPoissonMeasure ((((n : NNReal) • ρ.toFiniteMeasure) : FiniteMeasure ℝ)) :
      Measure ℝ) t =
      Complex.exp ((n : ℂ) * (charFun (ρ : Measure ℝ) t - 1)) := by
  have hintegrable :
      Integrable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I)) (μ := (ρ : Measure ℝ)) := by
    refine Integrable.of_bound (by fun_prop) 1 ?_
    exact Filter.Eventually.of_forall fun x ↦ by
      exact le_of_eq (by simpa using (Complex.norm_exp_ofReal_mul_I (t * x)))
  have hcentered :
      ∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂(ρ : Measure ℝ) =
        charFun (ρ : Measure ℝ) t - 1 := by
    -- Proof comment: the nonconstant part is the characteristic function, and the constant part
    -- contributes the total mass `1`.
    rw [integral_sub hintegrable (integrable_const (1 : ℂ)), MeasureTheory.charFun_apply_real]
    simp
  rw [charFun_compoundPoissonMeasure]
  congr 1
  let c : ENNReal := (n : NNReal)
  change
    (∫ x, (Complex.exp (t * x * Complex.I) - 1) ∂
      (((((n : NNReal) • ρ.toFiniteMeasure) : FiniteMeasure ℝ) : Measure ℝ))) =
        (n : ℂ) * (charFun (ρ : Measure ℝ) t - 1)
  have hscaledMeasure :
      (((((n : NNReal) • ρ.toFiniteMeasure) : FiniteMeasure ℝ) : Measure ℝ)) = c •
        (ρ : Measure ℝ) := by
    rfl
  rw [hscaledMeasure, integral_smul_measure, hcentered]
  change ((c.toReal : ℂ) * (charFun (ρ : Measure ℝ) t - 1)) =
      (n : ℂ) * (charFun (ρ : Measure ℝ) t - 1)
  simp [c]

end MeasureTheory.ProbabilityMeasure
