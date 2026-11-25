/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

@[expose] public section

namespace ADMM.UnitCircle.Fourier

open MeasureTheory
open scoped ENNReal ComplexConjugate

noncomputable section

instance unitPeriod_pos : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

abbrev TimeSequence := lp (fun _ : ℤ ↦ ℂ) 2
abbrev CircleL2 := Lp ℂ 2 (@AddCircle.haarAddCircle (1 : ℝ) unitPeriod_pos)

/-- Bilateral Fourier synthesis, using the Haar probability measure.
The circle point used below reverses orientation so a time delay has symbol `z⁻¹`. -/
noncomputable def transform : TimeSequence ≃ₗᵢ[ℂ] CircleL2 :=
  (@fourierBasis 1 unitPeriod_pos).repr.symm

@[simp] theorem transform_norm (x : TimeSequence) : ‖transform x‖ = ‖x‖ :=
  transform.norm_map x

@[simp] theorem transform_coefficient (x : TimeSequence) (k : ℤ) :
    fourierCoeff (transform x) k = x k := by
  rw [← fourierBasis_repr]
  exact congrArg (fun y : TimeSequence ↦ y k) (transform.symm_apply_apply x)

/-- Parseval for the actual bilateral sequence, with no pointwise Fourier-series assumption. -/
theorem transform_parseval (x : TimeSequence) :
    (∑' k : ℤ, ‖x k‖ ^ 2) =
      ∫ t : AddCircle (1 : ℝ), ‖transform x t‖ ^ 2 ∂AddCircle.haarAddCircle := by
  simpa only [transform_coefficient] using tsum_sq_fourierCoeff (transform x)

/-- The polarized Parseval identity, retaining the complex pairing. -/
theorem transform_inner (x y : TimeSequence) :
    (∑' k : ℤ, conj (x k) * y k) =
      ∫ t : AddCircle (1 : ℝ), conj (transform x t) * transform y t
        ∂AddCircle.haarAddCircle := by
  have h := transform.inner_map_map x y
  rw [lp.inner_eq_tsum, L2.inner_def] at h
  simpa only [RCLike.inner_apply'] using h.symm

/-- Multiplication by a Fourier character preserves square integrability. -/
noncomputable def characterMultiply (j : ℤ) (f : CircleL2) : CircleL2 :=
  ((Lp.memLp f).mul' (ContinuousMap.memLp (p := ∞) (μ := AddCircle.haarAddCircle) ℂ (fourier j))).toLp
    (fun t ↦ fourier j t * f t)

theorem characterMultiply_ae (j : ℤ) (f : CircleL2) :
    characterMultiply j f =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ fourier j t * f t) :=
  MemLp.coeFn_toLp _

/-- Multiplying by the `j`th character shifts each Fourier coefficient by `j`. -/
theorem characterMultiply_coefficient (j : ℤ) (f : CircleL2) (k : ℤ) :
    fourierCoeff (characterMultiply j f) k = fourierCoeff f (k - j) := by
  rw [fourierCoeff_congr_ae (characterMultiply_ae j f)]
  simp only [fourierCoeff, smul_eq_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ by
    change fourier (-k) t * (fourier j t * f t) = fourier (-(k - j)) t * f t
    rw [← mul_assoc, ← fourier_add]
    congr 2
    ring

/-- The true shift on all bilateral square-summable sequences. -/
noncomputable def delay (j : ℤ) (x : TimeSequence) : TimeSequence :=
  transform.symm (characterMultiply j (transform x))

@[simp] theorem delay_apply (j : ℤ) (x : TimeSequence) (k : ℤ) :
    delay j x k = x (k - j) := by
  change fourierBasis.repr (characterMultiply j (transform x)) k = _
  rw [fourierBasis_repr, characterMultiply_coefficient, transform_coefficient]

@[simp] theorem transform_delay (j : ℤ) (x : TimeSequence) :
    transform (delay j x) = characterMultiply j (transform x) :=
  transform.apply_symm_apply _

/-- Each delayed time pairing equals its actual frequency-domain pairing. -/
theorem delay_pairing_parseval (j : ℤ) (x y : TimeSequence) :
    (∑' k : ℤ, conj (x k) * y (k - j)) =
      ∫ t : AddCircle (1 : ℝ), conj (transform x t) *
        (fourier j t * transform y t) ∂AddCircle.haarAddCircle := by
  have h := transform_inner x (delay j y)
  simp only [delay_apply, transform_delay] at h
  refine h.trans (integral_congr_ae ?_)
  filter_upwards [characterMultiply_ae j (transform y)] with t ht
  rw [ht]

end

end ADMM.UnitCircle.Fourier
