/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_56
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_57
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_62

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open ContinuousLinearMap
open Filter
open InnerProductSpace
open scoped InnerProductSpace Gradient Topology

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 2.58: a continuous linear Gâteaux derivative field on the whole space
is the Fréchet derivative field. -/
private lemma hasFDerivAt_of_isGateauxDerivativeOn_univ
    (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) (x : H) :
    HasFDerivAt f (toDual ℝ H (L x)) x := by
  let DT : H → H →L[ℝ] ℝ := fun y ↦ toDual ℝ H (L y)
  have hU : Set.univ ∈ 𝓝 x := by
    simp
  have hcont : ContinuousWithinAt DT Set.univ x := by
    exact ((toDual ℝ H).continuous.comp L.continuous).continuousWithinAt
  simpa [DT] using hasFDerivAt_of_gateauxDerivative_continuousWithinAt hU hGateaux hcont

/-- Helper for Proposition 2.58: a continuous linear Gâteaux gradient field is the Fréchet
gradient field. -/
private lemma hasGradientAt_of_isGateauxDerivativeOn_univ
    (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) (x : H) :
    HasGradientAt f (L x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  simpa using hasFDerivAt_of_isGateauxDerivativeOn_univ f L hGateaux x

/-- Helper for Proposition 2.58: restricting `f` to the line `t ↦ t • x` has derivative
`t * ⟪L x, x⟫_ℝ` when `∇f = L`. -/
-- This is the one-dimensional bridge from the Hilbert-space gradient hypothesis to the
-- fundamental theorem of calculus on the segment from `0` to `x`.
private lemma line_restriction_hasDerivAt
    (f : H → ℝ) (L : H →L[ℝ] H) (hgrad : ∀ x, HasGradientAt f (L x) x) (x : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ f (s • x)) (t * ⟪L x, x⟫_ℝ) t := by
  -- Compose the gradient derivative of `f` at `t • x` with the scalar line map `s ↦ s • x`.
  have hline : HasDerivAt (fun s : ℝ ↦ s • x) x t := by
    simpa using ((hasDerivAt_id t).smul_const x)
  have hcomp := (hgrad (t • x)).hasFDerivAt.comp_hasDerivAt (x := t) hline
  -- Simplify the resulting scalar derivative using linearity of `L` and the inner product.
  simpa [map_smul, inner_smul_left, mul_comm, mul_left_comm, mul_assoc]
    using hcomp

/-- Helper for Proposition 2.58: integrating the line restriction yields the quadratic increment
formula for `f`. -/
-- Once the derivative along `t ↦ t • x` is known explicitly, the scalar FTC on `[0,1]` gives
-- the value of `f x - f 0`.
private lemma quadratic_increment_formula
    (f : H → ℝ) (L : H →L[ℝ] H) (hgrad : ∀ x, HasGradientAt f (L x) x) (x : H) :
    f x - f 0 = (1 / 2 : ℝ) * ⟪L x, x⟫_ℝ := by
  have hderiv :
      ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ ↦ f (s • x)) (t * ⟪L x, x⟫_ℝ) t := by
    intro t ht
    exact line_restriction_hasDerivAt f L hgrad x t
  have hint :
      IntervalIntegrable (fun t : ℝ ↦ t * ⟪L x, x⟫_ℝ) MeasureTheory.volume 0 1 := by
    exact
      Continuous.intervalIntegrable (μ := MeasureTheory.volume)
        (show Continuous (fun t : ℝ ↦ t * ⟪L x, x⟫_ℝ) by fun_prop) 0 1
  -- Apply the scalar FTC to the line restriction `t ↦ f (t • x)`.
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hEval : ∫ t in (0 : ℝ)..1, t * ⟪L x, x⟫_ℝ = (1 / 2 : ℝ) * ⟪L x, x⟫_ℝ := by
    -- The remaining integral is the elementary integral of `t` times a constant.
    rw [intervalIntegral.integral_mul_const, integral_id]
    norm_num
  rw [show (1 : ℝ) • x = x by simp, show (0 : ℝ) • x = 0 by simp, hEval] at hFTC
  linarith

/-- Helper for Proposition 2.58: Example 2.57 gives the gradient of the quadratic model
`y ↦ c + (1 / 2) * ⟪L y, y⟫_ℝ`. -/
private lemma quadratic_model_hasGradientAt (L : H →L[ℝ] H) (c : ℝ) (x : H) :
    HasGradientAt (fun y : H ↦ c + (1 / 2 : ℝ) * ⟪L y, y⟫_ℝ)
      ((1 / 2 : ℝ) • ((L + L.adjoint) x)) x := by
  have hq :
      HasGradientAt (quadratic_affine_functional L 0) ((L + L.adjoint) x) x := by
    simpa [quadratic_affine_functional] using quadratic_affine_functional_hasGradientAt L 0 x
  have hscaled := hq.hasFDerivAt.const_smul (1 / 2 : ℝ)
  have hshifted := hscaled.const_add c
  convert hshifted.hasGradientAt using 1
  · ext y
    simp [quadratic_affine_functional]
  · apply (toDual ℝ H).injective
    ext y
    simp

/-- Helper for Proposition 2.58: Example 2.57 gives the `C²` regularity of the quadratic model
`y ↦ c + (1 / 2) * ⟪L y, y⟫_ℝ`. -/
private lemma quadratic_model_contDiff_two (L : H →L[ℝ] H) (c : ℝ) :
    ContDiff ℝ 2 (fun y : H ↦ c + (1 / 2 : ℝ) * ⟪L y, y⟫_ℝ) := by
  have hmodel :
      ContDiff ℝ 2 (fun y : H ↦ (1 / 2 : ℝ) * quadratic_affine_functional L 0 y) :=
    (quadratic_affine_functional_contDiff_two L 0).const_smul (1 / 2 : ℝ)
  simpa [quadratic_affine_functional] using contDiff_const.add hmodel

/-- Proposition 2.58: if the Gâteaux derivative field of `f` is the continuous linear map `L`,
then `f` is the quadratic function `x ↦ f 0 + (1 / 2) * ⟪L x, x⟫_ℝ`. -/
-- Proof sketch: first upgrade the Gâteaux field to the Fréchet gradient field using
-- `Fact_2_62`, then integrate the line restriction from `0` to `x`.
theorem gradient_eq_continuousLinearMap_eq_quadratic_form (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) :
    f = fun x ↦ f 0 + (1 / 2 : ℝ) * ⟪L x, x⟫_ℝ := by
  let hgrad : ∀ x, HasGradientAt f (L x) x := fun x ↦
    hasGradientAt_of_isGateauxDerivativeOn_univ f L hGateaux x
  funext x
  -- The line-integral identity gives the increment of `f` from `0` to `x`.
  have hx := quadratic_increment_formula f L hgrad x
  linarith

/-- Proposition 2.58: a continuous linear map that is the Gâteaux gradient field of a real-valued
function is self-adjoint. -/
-- Proof sketch: upgrade to the Fréchet gradient field, rewrite `f` by the quadratic formula, and
-- compare with the canonical quadratic-gradient formula from Example 2.57.
theorem gradient_eq_continuousLinearMap_self_adjoint (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) :
    IsSelfAdjoint L := by
  let hgrad : ∀ x, HasGradientAt f (L x) x := fun x ↦
    hasGradientAt_of_isGateauxDerivativeOn_univ f L hGateaux x
  have hquad := gradient_eq_continuousLinearMap_eq_quadratic_form f L hGateaux
  rw [isSelfAdjoint_iff']
  ext x
  -- Compare the given gradient of `f` with the gradient of the quadratic model at the same point.
  have hfx : HasGradientAt f (L x) x := hgrad x
  have hqx :
      HasGradientAt (fun y : H ↦ f 0 + (1 / 2 : ℝ) * ⟪L y, y⟫_ℝ)
        ((1 / 2 : ℝ) • ((L + L.adjoint) x)) x :=
    quadratic_model_hasGradientAt L (f 0) x
  have hrew : HasGradientAt f ((1 / 2 : ℝ) • ((L + L.adjoint) x)) x := by
    rw [hquad]
    simpa using hqx
  have hx : L x = (1 / 2 : ℝ) • ((L + L.adjoint) x) := hfx.unique hrew
  -- Clear the factor `1 / 2` to isolate the pointwise equality `L x = L.adjoint x`.
  have hsum : L x + L x = L x + L.adjoint x := by
    calc
      L x + L x = (2 : ℝ) • L x := by simp [two_smul]
      _ = (2 : ℝ) • ((1 / 2 : ℝ) • ((L + L.adjoint) x)) := by rw [hx]
      _ = (L + L.adjoint) x := by simp [smul_smul]
      _ = L x + L.adjoint x := by simp [add_apply]
  simpa [star_eq_adjoint] using (add_left_cancel hsum).symm

/-- Proposition 2.58: a real-valued function whose Gâteaux gradient field is a continuous linear
map is twice Fréchet differentiable on the whole space, in the sense of Definition 2.56. -/
theorem gradient_eq_continuousLinearMap_twiceFrechetDifferentiableWithinAt
    (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) (x : H) :
    TwiceFrechetDifferentiableWithinAt ℝ f Set.univ x := by
  rw [gradient_eq_continuousLinearMap_eq_quadratic_form f L hGateaux]
  exact (quadratic_model_contDiff_two L (f 0)).twiceFrechetDifferentiableWithinAt_univ x

/-- Canonical strengthening of Proposition 2.58: a real-valued function whose Gâteaux gradient
field is a continuous linear map is `C²`. -/
theorem gradient_eq_continuousLinearMap_contDiff_two (f : H → ℝ) (L : H →L[ℝ] H)
    (hGateaux : HasGateauxDerivativeOn f (fun x ↦ toDual ℝ H (L x)) Set.univ) :
    ContDiff ℝ 2 f := by
  -- Rewrite `f` as the explicit quadratic model and then use the established `C²` regularity.
  rw [gradient_eq_continuousLinearMap_eq_quadratic_form f L hGateaux]
  exact quadratic_model_contDiff_two L (f 0)
