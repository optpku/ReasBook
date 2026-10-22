/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_5.FairCoin
public import Mathlib.Probability.IdentDistrib

public section

noncomputable section

namespace FairCoin

/-- The flipped `0/1` value map on fair-coin outcomes, with `false = tails` and
`true = heads`. -/
def flippedValue : Bool → ℝ
  | false => 1
  | true => 0

/-- The flipped value map has the same law as the original fair-coin `0/1`
random variable. -/
theorem hasLaw_flippedValue :
    ProbabilityTheory.HasLaw flippedValue valuePmf.toMeasure pmf.toMeasure := by
  refine { map_eq := ?_ }
  rw [PMF.toMeasure_map flippedValue pmf (measurable_of_countable flippedValue), PMF.toMeasure_inj]
  ext x
  by_cases hx0 : x = 0
  · subst hx0
    simp [PMF.map_apply, flippedValue]
  · by_cases hx1 : x = 1
    · subst hx1
      simp [PMF.map_apply, flippedValue]
    · rw [valuePmf_eq_zero_of_ne_zero_ne_one hx0 hx1]
      simp [PMF.map_apply, flippedValue, hx0, hx1]

/-- Remark 4.8 (1). The fair-coin random variables `value` and `flippedValue`
have the same distribution on the common probability space `pmf.toMeasure`. -/
theorem value_identDistrib_flippedValue :
    ProbabilityTheory.IdentDistrib value flippedValue pmf.toMeasure pmf.toMeasure :=
  hasLaw_value.identDistrib hasLaw_flippedValue

/-- Remark 4.8 (2). The fair-coin random variables `value` and `flippedValue`
are not equal as functions `Bool → ℝ`. -/
theorem value_ne_flippedValue :
    value ≠ flippedValue := by
  intro h
  have hfalse := congrFun h false
  simp [flippedValue] at hfalse

end FairCoin
