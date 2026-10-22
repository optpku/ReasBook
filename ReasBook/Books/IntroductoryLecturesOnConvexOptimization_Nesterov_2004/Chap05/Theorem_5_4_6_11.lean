/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_5

open scoped Gradient

noncomputable section

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]

/- Theorem 5.4.6.11 lies in the subsection's slice-level second-directional-derivative domain.

Sampled owner declarations:
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the source-facing composed barrier owner;
* `compositionPotential_secondDirectionalDerivative_eq_sigmaOne_add_sigmaTwo` from
  `Theorem_5_4_6_5`, the upstream owner for the fixed-`z` composition slice;
* `secondDirectionalDerivative` from `Definition_5_0_10`, the chapter owner for `D₂`;
* `sigmaThree` from `Definition_5_4_6_8`, the source-facing name for the barrier local squared
  norm.

Source/core/bridge triage:
* source-facing: the second-derivative formula and lower bound for the fixed-`z` slice
  `x' ↦ coneCompositionBarrier F Φ ξ β (x', z)`;
* core/canonical: `secondDirectionalDerivative`;
* bridge/view: the additive slice decomposition of `coneCompositionBarrier` together with the
  upstream identity `Δ₂ = σ₁ + σ₂`.

Primitive data:
* the standard self-concordance owner for `F` at `x`, used to identify the barrier part of the
  second derivative with `sigmaThree F x h`;
* the `C²` hypotheses on `ξ` and `Φ`, used by the upstream composition-potential owner;
* the parameter bound `1 ≤ β` for the lower bound.

Derived API:
* the slice decomposition
  `secondDirectionalDerivative (fun x' ↦ coneCompositionBarrier F Φ ξ β (x', z)) x h =
    secondDirectionalDerivative (fun x' ↦ compositionPotential Φ ξ (x', z)) x h + β^3 σ₃`;
* the rewritten equality
  `D₂ = compositionPotentialSigmaOne Φ ξ x z h + compositionPotentialSigmaTwo Φ ξ x z h + β^3 σ₃`;
* the lower bound
  `compositionPotentialSigmaOne Φ ξ x z h + compositionPotentialSigmaTwo Φ ξ x z h + β^2 σ₃ ≤ D₂`.

The public theorem surface therefore belongs on the fixed-`z` slice owner
`x' ↦ coneCompositionBarrier F Φ ξ β (x', z)`, not on an arbitrary product direction
`(h, v)`. The upstream theorem `Theorem_5_4_6_5` remains the owner for
`Δ₂ = σ₁ + σ₂`, while this file supplies the source-facing bridge for the barrier term and
combines the two owner-level formulas into the textbook `D₂` identity and lower bound. -/

section SliceDecomposition

variable [NormedSpace ℝ E₂]

variable (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal)
  (x : E₁) (z : E₃) (h : E₁)

local notation "ψ" => fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)
local notation "Ψ" => fun x' : E₁ ↦ coneCompositionBarrier F Φ ξ β (x', z)

-- Proof sketch: rewrite the directional slice of `Ψ` as the sum of the directional slice of
-- `ψ` and the scaled barrier slice `β^3 • directionalSlice F x h`. Additivity of
-- `secondDirectionalDerivative` on `C²` slices gives the decomposition
-- `D₂(Ψ) = D₂(ψ) + β^3 D₂(F)`. The standard self-concordance owner for `F` makes the Hessian
-- quadratic form nonnegative, so `D₂(F)` identifies with `sigmaThree F x h`.
/-- The second directional derivative of the fixed-`z` slice
`Ψ(x') = coneCompositionBarrier F Φ ξ β (x', z)` splits as the second directional derivative of
`ψ(x') = compositionPotential Φ ξ (x', z)` plus the barrier term `β^3 σ₃`, where
`σ₃ = sigmaThree F x h`. -/
theorem
    coneCompositionBarrier_slice_secondDirectionalDerivative_eq_compositionPotential_add_betaCube_sigmaThree
    {dom : Set E₁}
    (hF_self : IsStandardSelfConcordantOn dom F) (hx : x ∈ dom)
    (hξ : ContDiffAt ℝ 2 ξ x) (hΦ : ContDiffAt ℝ 2 Φ (ξ x, z)) :
    secondDirectionalDerivative Ψ x h =
      secondDirectionalDerivative ψ x h + ((β : ℝ) ^ 3) * sigmaThree F x h := by
  have hF_sigma : secondDirectionalDerivative F x h = sigmaThree F x h := by
    have hF3 : ContDiffAt ℝ 3 F x :=
      hF_self.contDiffOn.contDiffAt (hF_self.isOpen_domain.mem_nhds hx)
    have hF2 : ContDiffAt ℝ 2 F x := hF3.of_le (by norm_num)
    have hF_diff : DifferentiableAt ℝ F x := hF3.differentiableAt (by norm_num)
    have hF_fderiv : ContDiffAt ℝ 1 (fderiv ℝ F) x := by
      simpa using hF2.fderiv_right_succ
    have hgrad : DifferentiableAt ℝ (∇ F) x := by
      simpa [gradient] using
        (InnerProductSpace.toDual ℝ E₁).symm.differentiableAt.comp x
          (hF_fderiv.differentiableAt (by norm_num))
    rw [secondDirectionalDerivative_eq_hessian_quadratic_form hF_diff hgrad]
    symm
    exact sigmaThree_eq_inner_hessian F x h (hF_self.hessian_posSemidef hx h)
  have hψ : ContDiffAt ℝ 2 ψ x := by
    simpa [compositionPotential] using hΦ.comp x (hξ.prodMk contDiffAt_const)
  have hψ_slice : ContDiffAt ℝ 2 (directionalSlice ψ x h) 0 := by
    have hline : ContDiffAt ℝ 2 (fun t : ℝ ↦ x + t • h) 0 :=
      contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    have hψ' : ContDiffAt ℝ 2 ψ ((fun t : ℝ ↦ x + t • h) 0) := by
      simpa using hψ
    simpa [directionalSlice] using hψ'.comp 0 hline
  have hF2 : ContDiffAt ℝ 2 F x := by
    have hF3 : ContDiffAt ℝ 3 F x :=
      hF_self.contDiffOn.contDiffAt (hF_self.isOpen_domain.mem_nhds hx)
    exact hF3.of_le (by norm_num)
  have hF_slice : ContDiffAt ℝ 2 (directionalSlice F x h) 0 := by
    have hline : ContDiffAt ℝ 2 (fun t : ℝ ↦ x + t • h) 0 :=
      contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    have hF' : ContDiffAt ℝ 2 F ((fun t : ℝ ↦ x + t • h) 0) := by
      simpa using hF2
    simpa [directionalSlice] using hF'.comp 0 hline
  let g : ℝ → ℝ := ((β : ℝ) ^ 3) • directionalSlice F x h
  have hg : ContDiffAt ℝ 2 g 0 := by
    simpa [g] using ContDiffAt.const_smul ((β : ℝ) ^ 3) hF_slice
  have hslice : directionalSlice Ψ x h = directionalSlice ψ x h + g := by
    funext t
    simp [g, directionalSlice, coneCompositionBarrier, compositionPotential, smul_eq_mul]
  rw [secondDirectionalDerivative, hslice, iteratedDeriv_add hψ_slice hg]
  simp only [g, iteratedDeriv_const_smul_field]
  rw [show iteratedDeriv 2 (directionalSlice F x h) 0 = secondDirectionalDerivative F x h by
    rfl]
  rw [hF_sigma]
  rfl

end SliceDecomposition

section SigmaTheorems

variable [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

variable (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal)
  (x : E₁) (z : E₃) (h : E₁)

local notation "ψ" => fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)
local notation "Ψ" => fun x' : E₁ ↦ coneCompositionBarrier F Φ ξ β (x', z)

-- Proof sketch: rewrite the directional slice of `Ψ` as the sum of the directional slice of
-- `ψ` and the scaled barrier slice `β^3 • directionalSlice F x h`. Additivity of
-- `secondDirectionalDerivative` on `C²` slices gives the decomposition
-- `D₂(Ψ) = D₂(ψ) + β^3 D₂(F)`. The standard self-concordance owner for `F` makes the Hessian
-- quadratic form nonnegative, so `D₂(F)` identifies with `sigmaThree F x h`.
-- Proof sketch: combine the slice decomposition above with the canonical upstream decomposition
-- `Δ₂ = σ₁ + σ₂` from `Theorem_5_4_6_5`.
/-- Theorem 5.4.6.11: if `F` is standard self-concordant at `x` and `ξ`, `Φ` are `C²` at the
relevant points, then the fixed-`z` slice
`Ψ(x') = coneCompositionBarrier F Φ ξ β (x', z)` satisfies
`D₂ = σ₁ + σ₂ + β^3 σ₃`, where `σ₁`, `σ₂`, and `σ₃` are the canonical subsection owners. -/
theorem
    coneCompositionBarrier_slice_secondDirectionalDerivative_eq_sigmaSum_add_betaCube_sigmaThree
    {dom : Set E₁}
    (hF_self : IsStandardSelfConcordantOn dom F) (hx : x ∈ dom)
    (hξ : ContDiffAt ℝ 2 ξ x) (hΦ : ContDiffAt ℝ 2 Φ (ξ x, z)) :
    secondDirectionalDerivative Ψ x h =
      compositionPotentialSigmaOne Φ ξ x z h +
        compositionPotentialSigmaTwo Φ ξ x z h +
          ((β : ℝ) ^ 3) * sigmaThree F x h := by
  have hψ : ContDiffAt ℝ 2 ψ x := by
    simpa [compositionPotential] using hΦ.comp x (hξ.prodMk contDiffAt_const)
  have hslice :=
    coneCompositionBarrier_slice_secondDirectionalDerivative_eq_compositionPotential_add_betaCube_sigmaThree
      F Φ ξ β x z h hF_self hx hξ hΦ
  rw [hslice]
  rw [compositionPotential_secondDirectionalDerivative_eq_sigmaOne_add_sigmaTwo hξ hψ]

-- Proof sketch: rewrite `D₂` using the previous theorem, then use `β ≥ 1` and the automatic
-- nonnegativity of `sigmaThree F x h` to compare the coefficients `β^2` and `β^3`.
/-- If `β ≥ 1`, then the fixed-`z` slice decomposition yields the lower bound
`σ₁ + σ₂ + β^2 σ₃ ≤ D₂`, where
`D₂ = secondDirectionalDerivative (fun x' ↦ coneCompositionBarrier F Φ ξ β (x', z)) x h`
and `σ₃ = sigmaThree F x h`. -/
theorem
    coneCompositionBarrier_slice_secondDirectionalDerivative_ge_sigmaSum_add_betaSq_sigmaThree
    {dom : Set E₁}
    (hF_self : IsStandardSelfConcordantOn dom F) (hx : x ∈ dom)
    (hξ : ContDiffAt ℝ 2 ξ x) (hΦ : ContDiffAt ℝ 2 Φ (ξ x, z))
    (hβ : 1 ≤ β) :
    compositionPotentialSigmaOne Φ ξ x z h +
        compositionPotentialSigmaTwo Φ ξ x z h +
          ((β : ℝ) ^ 2) * sigmaThree F x h ≤
      secondDirectionalDerivative Ψ x h := by
  rw
    [coneCompositionBarrier_slice_secondDirectionalDerivative_eq_sigmaSum_add_betaCube_sigmaThree
      F Φ ξ β x z h hF_self hx hξ hΦ]
  have hβ_real : (1 : ℝ) ≤ (β : ℝ) := by
    exact_mod_cast hβ
  have hβ_nonneg : 0 ≤ (β : ℝ) := by
    exact_mod_cast β.2
  have hβsq : ((β : ℝ) ^ 2) ≤ (β : ℝ) ^ 3 := by
    nlinarith
  have hmul :
      ((β : ℝ) ^ 2) * sigmaThree F x h ≤ ((β : ℝ) ^ 3) * sigmaThree F x h :=
    mul_le_mul_of_nonneg_right hβsq (sigmaThree_nonneg F x h)
  linarith

end SigmaTheorems

end
