module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-!
# Cubic Taylor control for the real arctangent

The fourth-order remainder is exposed as a public asymptotic lemma, together with
its standard composition rule for a slope germ of prescribed order.
-/

public section

noncomputable section

open Filter
open Asymptotics
open scoped Topology

namespace Real

/-- The cubic Taylor polynomial of `Real.arctan` has a fourth-order remainder at zero. -/
theorem arctan_sub_cubic_isBigO :
    (fun x : ℝ ↦ Real.arctan x - (x - x ^ 3 / 3)) =O[𝓝 0]
      (fun x : ℝ ↦ x ^ 4) := by
  let den : ℝ → ℝ := fun x ↦ 1 + x ^ 2
  let d : ℝ → ℝ := fun x ↦ (den x)⁻¹
  have hden : ContDiff ℝ 4 den := by
    fun_prop
  have hd : ContDiff ℝ 4 d := by
    apply hden.inv
    intro x
    dsimp [den]
    positivity
  have hproduct : den * d = fun _ ↦ 1 := by
    funext x
    dsimp [den, d]
    field_simp
  have hdZero : iteratedDeriv 0 d 0 = 1 := by
    norm_num [d, den]
  have hdOne : iteratedDeriv 1 d 0 = 0 := by
    simp [d, den, iteratedDeriv_succ]
  have hdenZero : iteratedDeriv 0 den 0 = 1 := by
    norm_num [den]
  have hdenOne : iteratedDeriv 1 den 0 = 0 := by
    rw [show den = fun x : ℝ ↦ 1 + x ^ 2 by rfl,
      iteratedDeriv_const_add (by norm_num) 1]
    simp
  have hdenTwo : iteratedDeriv 2 den 0 = 2 := by
    rw [show den = fun x : ℝ ↦ 1 + x ^ 2 by rfl,
      iteratedDeriv_const_add (by norm_num) 1]
    simp
  have hdenThree : iteratedDeriv 3 den 0 = 0 := by
    rw [show den = fun x : ℝ ↦ 1 + x ^ 2 by rfl,
      iteratedDeriv_const_add (by norm_num) 1]
    simp
  have hdTwo : iteratedDeriv 2 d 0 = -2 := by
    have h := congrArg (fun f : ℝ → ℝ ↦ iteratedDeriv 2 f 0) hproduct
    rw [iteratedDeriv_mul (hden.contDiffAt.of_le (by norm_num))
      (hd.contDiffAt.of_le (by norm_num))] at h
    norm_num [Finset.sum_range_succ, hdenZero, hdenOne, hdenTwo,
      hdZero, hdOne, iteratedDeriv_const] at h
    linarith
  have hdThree : iteratedDeriv 3 d 0 = 0 := by
    have h := congrArg (fun f : ℝ → ℝ ↦ iteratedDeriv 3 f 0) hproduct
    rw [iteratedDeriv_mul (hden.contDiffAt.of_le (by norm_num))
      (hd.contDiffAt.of_le (by norm_num))] at h
    norm_num [Finset.sum_range_succ, hdenZero, hdenOne, hdenTwo, hdenThree,
      hdZero, hdOne, hdTwo, iteratedDeriv_const] at h
    linarith
  have hderivArctan : deriv Real.arctan = d := by
    simpa only [d, den, one_div] using Real.deriv_arctan
  have h₀ : iteratedDeriv 0 Real.arctan 0 = 0 := by
    simp
  have h₁ : iteratedDeriv 1 Real.arctan 0 = 1 := by
    simp [iteratedDeriv_succ, Real.deriv_arctan]
  have h₂ : iteratedDeriv 2 Real.arctan 0 = 0 := by
    simp [iteratedDeriv_succ, Real.deriv_arctan]
  have h₃ : iteratedDeriv 3 Real.arctan 0 = -2 := by
    rw [show 3 = 2 + 1 by norm_num, iteratedDeriv_succ', hderivArctan]
    exact hdTwo
  have h₄ : iteratedDeriv 4 Real.arctan 0 = 0 := by
    rw [show 4 = 3 + 1 by norm_num, iteratedDeriv_succ', hderivArctan]
    exact hdThree
  have hTaylor := taylor_isLittleO_univ (x₀ := 0) (n := 4) Real.contDiff_arctan
  have hPolynomial (x : ℝ) :
      taylorWithinEval Real.arctan 4 Set.univ 0 x = x - x ^ 3 / 3 := by
    rw [taylor_within_apply]
    norm_num [iteratedDerivWithin_univ, Finset.sum_range_succ,
      h₀, h₁, h₂, h₃, h₄]
    ring
  exact hTaylor.isBigO.congr'
    (Filter.Eventually.of_forall fun x ↦ by simp only [hPolynomial])
    (Filter.Eventually.of_forall fun x ↦ by simp)

/-- Composing the cubic arctangent remainder with an order-`n` slope germ gives an
order-`4n` remainder. -/
theorem arctan_comp_sub_cubic_isBigO {n : ℕ} {s : ℝ → ℝ}
    (hs0 : Tendsto s (𝓝 0) (𝓝 0))
    (hs : s =O[𝓝 0] (fun ε : ℝ ↦ ε ^ n)) :
    (fun ε : ℝ ↦ Real.arctan (s ε) - (s ε - s ε ^ 3 / 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ (n * 4)) := by
  have hcomp := Real.arctan_sub_cubic_isBigO.comp_tendsto hs0
  have h := hcomp.trans (hs.pow 4)
  change ((fun x : ℝ ↦ Real.arctan x - (x - x ^ 3 / 3)) ∘ s) =O[𝓝 0]
    (fun ε : ℝ ↦ ε ^ (n * 4))
  simpa only [Function.comp_apply, ← pow_mul] using h

end Real
