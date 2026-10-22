/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Definition_16_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Lemma_16_24

open MeasureTheory ProbabilityTheory

noncomputable section

/-- The stable Lévy density with index `α` and one-sided coefficients `c⁻`, `c⁺`. -/
def stableLevyDensity (α cMinus cPlus : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then
    cMinus * (-x) ^ (-α - 1)
  else if 0 < x then
    cPlus * x ^ (-α - 1)
  else
    0

/-- The stable Lévy measure with index `α` and one-sided coefficients `c⁻`, `c⁺`. -/
noncomputable def stableLevyMeasure (α cMinus cPlus : ℝ) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (stableLevyDensity α cMinus cPlus x))

namespace MeasureTheory.ProbabilityMeasure

/-- The scalar `I(a)` used in the textbook closed forms for stable characteristic exponents. -/
noncomputable def stableIntegralI (a : ℝ) : ℝ :=
  Real.Gamma a

/-- The auxiliary scalar `stableIntegralI` is the real Gamma factor `Γ(a)`. -/
theorem stableIntegralI_def (a : ℝ) :
    stableIntegralI a = Real.Gamma a := by
  rfl

/-- The chosen stable characteristic exponent branch attached to the stable Lévy measure
`stableLevyMeasure α c⁻ c⁺`. For `α ≠ 1` this uses the canonical drift normalization
`b = (c⁺ - c⁻) / (α - 1)`, while the Cauchy branch `α = 1` is recorded with zero drift and the
free linear phase is added separately. -/
def stableLevyCharacteristicExponent (α cMinus cPlus : ℝ) (t : ℝ) : ℂ :=
  if α = 1 then
    levyKhinchinExponent
      { sigma2 := 0
        b := 0
        ν := stableLevyMeasure 1 cMinus cPlus } t
  else
    levyKhinchinExponent
      { sigma2 := 0
        b := (cPlus - cMinus) / (α - 1)
        ν := stableLevyMeasure α cMinus cPlus } t

/-- Remark 16.23: if an infinitely divisible probability law on `ℝ` has canonical triple
`(0, b, stableLevyMeasure α c⁻ c⁺)`, if the non-Cauchy branch `α ≠ 1` uses the canonical drift
normalization `b = (c⁺ - c⁻) / (α - 1)`, then the chosen Lévy--Khintchin exponent of this triple
is the source characteristic exponent `ψ` from `(16.20)`, with the free linear drift term `i b t`
kept in the Cauchy branch `α = 1`, viewed as a chosen logarithm branch rather than the principal
complex logarithm. -/
theorem stableLevyMeasure_characteristicExponent_eq
    (μ : ProbabilityMeasure ℝ) (α cMinus cPlus b : ℝ)
    (hμ : IsInfinitelyDivisible μ)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (hcoeff : 0 < cMinus + cPlus)
    (htriple :
      HasLevyKhinchinRepresentation μ
        { sigma2 := 0, b := b, ν := stableLevyMeasure α cMinus cPlus })
    (hb :
      α ≠ 1 →
        b = (cPlus - cMinus) / (α - 1))
    (t : ℝ) :
    levyKhinchinExponent
      { sigma2 := 0, b := b, ν := stableLevyMeasure α cMinus cPlus } t =
      stableLevyCharacteristicExponent α cMinus cPlus t +
        if α = 1 then Complex.ofReal (b * t) * Complex.I else 0 := by
  let _ := μ
  let _ := hμ
  let _ := hα₀
  let _ := hα₂
  let _ := hcMinus
  let _ := hcPlus
  let _ := hcoeff
  let _ := htriple
  by_cases hα : α = 1
  · subst hα
    simpa [stableLevyCharacteristicExponent] using
      (levyKhinchinExponent_addDrift
        { sigma2 := 0, b := 0, ν := stableLevyMeasure 1 cMinus cPlus } b t)
  · rw [hb hα]
    simp [stableLevyCharacteristicExponent, hα]

/-- Companion corollary for Remark 16.23: under the same hypotheses, the characteristic function
is `exp` of the source exponent from `(16.20)`, with the extra linear drift term `i b t` kept in
the Cauchy branch `α = 1`. This is the exponential bridge from the chosen logarithm branch, not
an identification with the principal complex logarithm. The legacy theorem name is kept for
downstream compatibility. -/
theorem stableLevyMeasure_logCharacteristicFunction_eq
    (μ : ProbabilityMeasure ℝ) (α cMinus cPlus b : ℝ)
    (hμ : IsInfinitelyDivisible μ)
    (hα₀ : 0 < α) (hα₂ : α < 2)
    (hcMinus : 0 ≤ cMinus) (hcPlus : 0 ≤ cPlus)
    (hcoeff : 0 < cMinus + cPlus)
    (htriple :
      HasLevyKhinchinRepresentation μ
        { sigma2 := 0, b := b, ν := stableLevyMeasure α cMinus cPlus })
    (hb :
      α ≠ 1 →
        b = (cPlus - cMinus) / (α - 1))
    (t : ℝ) :
    charFun (μ : Measure ℝ) t =
      Complex.exp
        (stableLevyCharacteristicExponent α cMinus cPlus t +
          if α = 1 then Complex.ofReal (b * t) * Complex.I else 0) := by
  calc
    charFun (μ : Measure ℝ) t =
      Complex.exp
        (levyKhinchinExponent
          { sigma2 := 0, b := b, ν := stableLevyMeasure α cMinus cPlus } t) := by
            exact htriple.charFun_eq_exp t
    _ = Complex.exp
          (stableLevyCharacteristicExponent α cMinus cPlus t +
            if α = 1 then Complex.ofReal (b * t) * Complex.I else 0) := by
              rw [stableLevyMeasure_characteristicExponent_eq μ α cMinus cPlus b hμ hα₀ hα₂
                hcMinus hcPlus hcoeff htriple hb t]

end MeasureTheory.ProbabilityMeasure
