module

public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.Converse
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusQuadraticGermTransport
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusJetCertificates
public import ReasLib.Analysis.Asymptotics.ArctanTaylor
public import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.Converse
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusQuadraticGermTransport
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusJetCertificates

public section

noncomputable section

open Filter
open scoped Topology

namespace DFP.TwoLeg.Mixed

/-- Helper for Appendix Lemma A.6: composing a zero-based quadratic germ with
    `Real.arctan` preserves its constant, linear, and quadratic coefficients. -/
theorem HasQuadraticGerm.arctan_of_zero
    {f : ℝ → ℝ} {a₁ a₂ : ℝ}
    (hf : HasQuadraticGerm f 0 a₁ a₂)
    (hregular : ContDiffAt ℝ 3 f 0) :
    HasQuadraticGerm (fun r ↦ Real.arctan (f r)) 0 a₁ a₂ := by
  have hf_coeff := hf.iteratedDeriv_coefficients_of_contDiffAt hregular
  have hf_zero : f 0 = 0 := by
    simpa only [iteratedDeriv_zero] using hf_coeff.1
  have hf_first : deriv f 0 = a₁ := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hf_coeff.2.1
  have hf_second : iteratedDeriv 2 f 0 = 2 * a₂ := hf_coeff.2.2
  have hone_le_three : (1 : WithTop ENat) ≤ (3 : WithTop ENat) := by
    norm_num
  have htwo_le_three : (2 : WithTop ENat) ≤ (3 : WithTop ENat) := by
    norm_num
  have hregular_one : ContDiffAt ℝ 1 f 0 := hregular.of_le hone_le_three
  have hfd : HasDerivAt f (deriv f 0) 0 :=
    (hregular_one.differentiableAt one_ne_zero).hasDerivAt
  have hatan : HasDerivAt (Real.arctan ∘ f)
      ((1 / (1 + f 0 ^ 2)) * deriv f 0) 0 := by
    simpa only [Function.comp_def] using (Real.hasDerivAt_arctan (f 0)).comp 0 hfd
  have hcomp_zero : (Real.arctan ∘ f) 0 = 0 := by
    simp only [Function.comp_apply, hf_zero, Real.arctan_zero]
  have hcomp_first : deriv (Real.arctan ∘ f) 0 = a₁ := by
    rw [hatan.deriv, hf_zero, hf_first]
    norm_num
  have hcomp_regular : ContDiffAt ℝ 3 (Real.arctan ∘ f) 0 := by
    exact Real.contDiff_arctan.contDiffAt.comp 0 hregular
  have harctan_regular : ContDiffAt ℝ 2 Real.arctan (f 0) := by
    exact Real.contDiff_arctan.contDiffAt.of_le htwo_le_three
  have hf_regular_two : ContDiffAt ℝ 2 f 0 := hregular.of_le htwo_le_three
  have hcomp_second_raw := iteratedDeriv_comp_two
    harctan_regular hf_regular_two
  have harctan_second : iteratedDeriv 2 Real.arctan 0 = 0 := by
    simp [iteratedDeriv_succ, Real.deriv_arctan]
  have hcomp_second : iteratedDeriv 2 (Real.arctan ∘ f) 0 = 2 * a₂ := by
    rw [hcomp_second_raw]
    simp only [hf_zero, harctan_second, Real.deriv_arctan, hf_first, hf_second]
    norm_num
  exact HasQuadraticGerm.of_contDiffAt_iteratedDeriv_two
    hcomp_regular hcomp_zero hcomp_first hcomp_second

/-- Helper for Appendix Lemma A.6: an `EqModPow n` certificate with `3 ≤ n` is a
    quadratic germ once the source path is continuous at zero. -/
theorem HasQuadraticGerm.of_eqModPow_of_order
    {f : ℝ → ℝ} {a₀ a₁ a₂ : ℝ} {n : ℕ}
    (horder : 3 ≤ n) (hcontinuous : ContinuousAt f 0)
    (heq : EqModPow n f (quadraticModel a₀ a₁ a₂)) :
    HasQuadraticGerm f a₀ a₁ a₂ := by
  refine ⟨hcontinuous, ?_⟩
  obtain rfl | hlt := horder.eq_or_lt
  · exact heq
  · unfold EqModPow at heq ⊢
    exact heq.trans (Asymptotics.isLittleO_pow_pow hlt).isBigO

/-
The next adapter is deliberately stated at the scalar-slope level.  It keeps
the frame algebra out of the germ transport: a caller only has to identify a
zero-based slope and its first derivative.
-/

/-- Helper for Appendix Lemma A.6: a zero-based scalar slope with first derivative
    `a` gives the arctangent coefficient germ `[0, a]` in the independent radius. -/
theorem independentRadiusTruncatedGerm_of_arctan_zero_slope
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)}
    {a : (ℝ × ℝ × ℝ) → ℝ}
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 2 (Function.uncurry f) (θ, 0))
    (hzero : ∀ θ, θ ∈ K → f θ 0 = 0)
    (hlinear : ∀ θ, θ ∈ K → deriv (f θ) 0 = a θ) :
    IndependentRadiusTruncatedGerm
      (fun θ r ↦ Real.arctan (f θ r)) K 2
      (fun n θ ↦ (![0, a θ] : Fin 2 → ℝ) n) := by
  have hone_le_two : (1 : WithTop ENat) ≤ (2 : WithTop ENat) := by
    norm_num
  have houtputRegular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 2
        (Function.uncurry (fun η r ↦ Real.arctan (f η r))) (θ, 0) := by
    intro θ hθ
    have hcomp := Real.contDiff_arctan.contDiffAt.comp (θ, 0) (hregular θ hθ)
    have hfun :
        (Real.arctan ∘ Function.uncurry f) =
          Function.uncurry (fun η r ↦ Real.arctan (f η r)) := by
      funext z
      rfl
    rw [hfun] at hcomp
    exact hcomp
  have houtputZero : ∀ θ, θ ∈ K →
      (fun r ↦ Real.arctan (f θ r)) 0 = 0 := by
    intro θ hθ
    simp only [hzero θ hθ, Real.arctan_zero]
  have houtputLinear : ∀ θ, θ ∈ K →
      iteratedDeriv 1 (fun r ↦ Real.arctan (f θ r)) 0 = a θ := by
    intro θ hθ
    have htwo_ne_zero : (2 : WithTop ENat) ≠ 0 := by
      norm_num
    have hsliceMap : ContDiffAt ℝ 2 (fun r : ℝ ↦ (θ, r)) 0 := by
      fun_prop
    have hslice : ContDiffAt ℝ 2 (f θ) 0 := by
      have hcomp := (hregular θ hθ).comp 0 hsliceMap
      have hfun : (Function.uncurry f ∘ Prod.mk θ) = f θ := by
        funext r
        rfl
      rw [hfun] at hcomp
      exact hcomp
    have hfd : HasDerivAt (f θ) (deriv (f θ) 0) 0 :=
      (hslice.differentiableAt htwo_ne_zero).hasDerivAt
    have hatan := (Real.hasDerivAt_arctan (f θ 0)).comp 0 hfd
    have hderiv : deriv (fun r ↦ Real.arctan (f θ r)) 0 = a θ := by
      have hangleFun : (fun r ↦ Real.arctan (f θ r)) = Real.arctan ∘ f θ := by
        funext r
        rfl
      rw [hangleFun, hatan.deriv, hzero θ hθ, hlinear θ hθ]
      norm_num
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using hderiv
  exact independentRadiusTruncatedGerm_of_twoDerivativeData
    houtputRegular houtputZero houtputLinear

end DFP.TwoLeg.Mixed
