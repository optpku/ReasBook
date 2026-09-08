module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusJet
public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion
public import ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.Converse
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion.IndependentRadiusJet
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion
import all ReasLib.Optimization.DFP.TwoPhaseControls.PhysicalDrift.AmplitudeSecondJet.Converse

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-!
This companion transports scalar quadratic-germ certificates into the coefficient-germ
interface used by the independent-radius uniform remainder theorems.
-/

/-- Appendix Lemma A.6: `C³` quadratic germs determine an independent-radius coefficient
    germ with the factorial-normalized coefficients `[a₀, a₁, a₂]`. -/
theorem independentRadiusCoefficientGerm_of_quadraticGerms
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)}
    {a₀ a₁ a₂ : (ℝ × ℝ × ℝ) → ℝ}
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3 (Function.uncurry f) (θ, 0))
    (hgerm : ∀ θ, θ ∈ K →
      HasQuadraticGerm (f θ) (a₀ θ) (a₁ θ) (a₂ θ)) :
    IndependentRadiusCoefficientGerm f K 2
      (fun n θ ↦ (![a₀ θ, a₁ θ, a₂ θ] : Fin 3 → ℝ) n) := by
  have horder : (2 : WithTop ENat) ≤ (3 : WithTop ENat) := by
    norm_num
  refine ⟨?_, ?_⟩
  · intro θ hθ
    exact (hregular θ hθ).of_le horder
  · intro n θ hθ
    rw [FiniteTaylorJet.scalarCoeff_ofFunction]
    have hsliceMap : ContDiffAt ℝ 3 (fun r : ℝ ↦ (θ, r)) 0 := by
      fun_prop
    have hslice : ContDiffAt ℝ 3 (f θ) 0 := by
      have hcomp := (hregular θ hθ).comp 0 hsliceMap
      have hfun : (Function.uncurry f ∘ Prod.mk θ) = f θ := by
        funext r
        rfl
      rw [hfun] at hcomp
      exact hcomp
    have hcoeff :=
      (hgerm θ hθ).iteratedDeriv_coefficients_of_contDiffAt hslice
    fin_cases n
    · simpa [hcoeff.1]
    · simpa [hcoeff.2.1]
    · rw [hcoeff.2.2]
      norm_num
      ring

/-- Helper for Appendix Lemma A.6: the same quadratic certificates give the truncated
    three-term germ whose compact-uniform remainder has order three. -/
theorem independentRadiusTruncatedGerm_of_quadraticGerms
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)}
    {a₀ a₁ a₂ : (ℝ × ℝ × ℝ) → ℝ}
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3 (Function.uncurry f) (θ, 0))
    (hgerm : ∀ θ, θ ∈ K →
      HasQuadraticGerm (f θ) (a₀ θ) (a₁ θ) (a₂ θ)) :
    IndependentRadiusTruncatedGerm f K 3
      (fun n θ ↦ (![a₀ θ, a₁ θ, a₂ θ] : Fin 3 → ℝ) n) := by
  have horder : (2 : WithTop ENat) ≤ (3 : WithTop ENat) := by
    norm_num
  refine ⟨hregular, ?_⟩
  intro n θ hθ
  rw [FiniteTaylorJet.scalarCoeff_ofFunction]
  have hsliceMap : ContDiffAt ℝ 3 (fun r : ℝ ↦ (θ, r)) 0 := by
    fun_prop
  have hslice : ContDiffAt ℝ 3 (f θ) 0 := by
    have hcomp := (hregular θ hθ).comp 0 hsliceMap
    have hfun : (Function.uncurry f ∘ Prod.mk θ) = f θ := by
      funext r
      rfl
    rw [hfun] at hcomp
    exact hcomp
  have hcoeff :=
    (hgerm θ hθ).iteratedDeriv_coefficients_of_contDiffAt hslice
  fin_cases n
  · simpa [hcoeff.1]
  · simpa [hcoeff.2.1]
  · norm_num
    rw [hcoeff.2.2]
    norm_num
    ring

end DFP.TwoLeg.Mixed
