/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Analysis.Calculus.Gradient.OrthogonalSum.Hessian
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Hölder Hessians and changes of coordinates

These estimates retain Hölder regularity under the coordinate changes used in
the DFP counterexample, and give the gradient remainder used for sharpness.
-/

public section

open scoped InnerProduct

/-- Helper for cor:identity-initialization: adjoint congruence multiplies an
operator norm by at most the square of the coordinate map's norm.
This estimate is upstream-worthy for the Hessian coordinate-change API. -/
theorem ContinuousLinearMap.norm_pullback_le
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (L : E →L[ℝ] F) (A : F →L[ℝ] F) :
    ‖L.pullback A‖ ≤ ‖L‖ ^ 2 * ‖A‖ := by
  rw [ContinuousLinearMap.pullback_def]
  calc
    ‖L.adjoint ∘L A ∘L L‖ ≤ ‖L.adjoint‖ * ‖A ∘L L‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖L.adjoint‖ * (‖A‖ * ‖L‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = ‖L‖ ^ 2 * ‖A‖ := by
      rw [ContinuousLinearMap.adjoint.norm_map]
      ring

/-- Helper for cor:identity-initialization: linear pullback preserves a Hölder
Hessian bound on a set, with its explicit coordinate-dependent constant.
This estimate is upstream-worthy for the Hessian coordinate-change API. -/
theorem hessianHolderOn_comp_continuousLinearEquiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (L : E ≃L[ℝ] F)
    {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    {K : Set F}
    (h : ∀ x ∈ K, ∀ y ∈ K, ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ β) :
    ∀ x, L x ∈ K → ∀ y, L y ∈ K → ‖hessian (f ∘ L) x - hessian (f ∘ L) y‖ ≤
      (‖L.toContinuousLinearMap‖ ^ 2 * C * ‖L.toContinuousLinearMap‖ ^ β) *
        ‖x - y‖ ^ β := by
  have hdiff : Differentiable ℝ (gradient f) :=
    (hf.gradient_succ (n := 1)).differentiable_one
  intro x hx y hy
  rw [L.comp_right_hessian f x (hdiff _), L.comp_right_hessian f y (hdiff _),
    ← ContinuousLinearMap.pullback_sub]
  have hdist : ‖L x - L y‖ ≤ ‖L.toContinuousLinearMap‖ * ‖x - y‖ := by
    rw [← map_sub]
    exact L.toContinuousLinearMap.le_opNorm _
  calc
    ‖L.toContinuousLinearMap.pullback (hessian f (L x) - hessian f (L y))‖ ≤
        ‖L.toContinuousLinearMap‖ ^ 2 * ‖hessian f (L x) - hessian f (L y)‖ :=
      L.toContinuousLinearMap.norm_pullback_le _
    _ ≤ ‖L.toContinuousLinearMap‖ ^ 2 * (C * ‖L x - L y‖ ^ β) :=
      mul_le_mul_of_nonneg_left (h _ hx _ hy) (sq_nonneg _)
    _ ≤ ‖L.toContinuousLinearMap‖ ^ 2 *
        (C * (‖L.toContinuousLinearMap‖ * ‖x - y‖) ^ β) := by
      gcongr
    _ = _ := by
      rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
      ring

/-- Helper for cor:identity-initialization: a linear pullback preserves a
global Hölder Hessian estimate. -/
theorem hessianHolder_comp_continuousLinearEquiv
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {f : F → ℝ} (hf : ContDiff ℝ 2 f) (L : E ≃L[ℝ] F)
    {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (h : ∀ x y, ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ β) :
    ∀ x y, ‖hessian (f ∘ L) x - hessian (f ∘ L) y‖ ≤
      (‖L.toContinuousLinearMap‖ ^ 2 * C * ‖L.toContinuousLinearMap‖ ^ β) *
        ‖x - y‖ ^ β := by
  have hset : ∀ x ∈ Set.univ, ∀ y ∈ Set.univ,
      ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ β := fun x _ y _ ↦ h x y
  exact fun x y ↦ hessianHolderOn_comp_continuousLinearEquiv hf L hC hβ hset
    x (Set.mem_univ _) y (Set.mem_univ _)

/-- Helper for eq:counterexample-nonlipschitz: a Hölder derivative on a segment
gives a remainder of order `1 + β`. This upstream-worthy mean-value estimate
does not require the sharp integral constant. -/
theorem norm_firstOrderRemainder_le_of_holderDerivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x y : E} {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (hf : ∀ z ∈ segment ℝ x y, DifferentiableAt ℝ f z)
    (h : ∀ z ∈ segment ℝ x y,
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖z - x‖ ^ β) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ C * ‖y - x‖ ^ (1 + β) := by
  have hbound (z) (hz : z ∈ segment ℝ x y) :
      ‖fderiv ℝ f z - fderiv ℝ f x‖ ≤ C * ‖y - x‖ ^ β := by
    apply (h z hz).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) (norm_sub_le_of_mem_segment hz) hβ) hC
  have hmean := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le'
    hf hbound (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  have hpow : ‖y - x‖ ^ (1 + β) = ‖y - x‖ * ‖y - x‖ ^ β := by
    rw [Real.rpow_add_of_nonneg (norm_nonneg _) zero_le_one hβ, Real.rpow_one]
  rw [hpow]
  calc
    _ ≤ C * ‖y - x‖ ^ β * ‖y - x‖ := hmean
    _ = _ := by ring

namespace EuclideanSpace.OrthogonalSum.Gradient

/-- Helper for thm:main: the Hessian of an objective extended by an identity
quadratic acts separately on its two orthogonal coordinates. -/
theorem hessian_objective_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : ContDiff ℝ 2 f)
    (p w : EuclideanSpace ℝ (ι ⊕ κ)) :
    hessian (objective (κ := κ) f) p w =
      (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm
        (hessian f (left p) (left w), right w) := by
  have hdiff : Differentiable ℝ f := hf.differentiable two_ne_zero
  have hgradDiff : Differentiable ℝ (gradient f) :=
    (hf.gradient_succ (n := 1)).differentiable_one
  have hgradEq : gradient (objective (κ := κ) f) =
      fun q ↦ (EuclideanSpace.sumEquivProd (𝕜 := ℝ)).symm
        (gradient f (left q), right q) := by
    funext q
    exact gradient_objective (hdiff _)
  have hleft : HasFDerivAt (fun q : EuclideanSpace ℝ (ι ⊕ κ) ↦ gradient f (left q))
      ((hessian f (left p)).comp left) p := by
    have hgradF : HasFDerivAt (gradient f) (hessian f (left p)) (left p) := by
      rw [hessian_def]
      exact (hgradDiff (left p)).hasFDerivAt
    exact hgradF.comp p (left (ι := ι) (κ := κ)).hasFDerivAt
  have hpair := hleft.prodMk (right (ι := ι) (κ := κ)).hasFDerivAt
  have hblock := (EuclideanSpace.sumEquivProd (𝕜 := ℝ) (ι := ι) (κ := κ)).symm.hasFDerivAt.comp
    p hpair
  have hderiv := hblock.fderiv
  simp only [Function.comp_def] at hderiv
  rw [hessian_def, hgradEq, hderiv]
  rfl

/-- Helper for thm:main: an orthogonal coordinate projection does not increase norm. -/
theorem norm_left_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (z : EuclideanSpace ℝ (ι ⊕ κ)) : ‖left z‖ ≤ ‖z‖ := by
  have h := norm_sq_eq_left_add_right z
  nlinarith [sq_nonneg ‖right z‖, norm_nonneg z, norm_nonneg (left z)]

/-- Helper for thm:main: the variable part of the extended Hessian is supported
on the original coordinates, so its difference has no larger operator norm. -/
theorem norm_hessian_objective_sub_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : ContDiff ℝ 2 f)
    (p q : EuclideanSpace ℝ (ι ⊕ κ)) :
    ‖hessian (objective (κ := κ) f) p - hessian (objective (κ := κ) f) q‖ ≤
      ‖hessian f (left p) - hessian f (left q)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro w
  have hnorm :
      ‖(hessian (objective (κ := κ) f) p - hessian (objective (κ := κ) f) q) w‖ =
        ‖(hessian f (left p) - hessian f (left q)) (left w)‖ := by
    have hsquare := norm_sq_eq_left_add_right
      ((hessian (objective (κ := κ) f) p - hessian (objective (κ := κ) f) q) w)
    simp only [sub_apply, hessian_objective_apply hf, map_sub,
      left_sumEquivProd_symm, right_sumEquivProd_symm, sub_self,
      norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hsquare
    simpa only [sub_apply, hessian_objective_apply hf] using
      (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsquare
  rw [hnorm]
  exact ((hessian f (left p) - hessian f (left q)).le_opNorm (left w)).trans
    (mul_le_mul_of_nonneg_left (norm_left_le w) (norm_nonneg _))

/-- Helper for eq:counterexample-nonlipschitz: restriction to the original
coordinates recovers a lower bound for the extended Hessian difference norm. -/
theorem norm_hessian_sub_le_objective {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : ContDiff ℝ 2 f)
    (x y : EuclideanSpace ℝ ι) :
    ‖hessian f x - hessian f y‖ ≤
      ‖hessian (objective (κ := κ) f) (EuclideanSpace.OrthogonalSum.inl x) -
        hessian (objective (κ := κ) f) (EuclideanSpace.OrthogonalSum.inl y)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro w
  let A := hessian (objective (κ := κ) f) (EuclideanSpace.OrthogonalSum.inl x) -
    hessian (objective (κ := κ) f) (EuclideanSpace.OrthogonalSum.inl y)
  have hproj : left (A (EuclideanSpace.OrthogonalSum.inl w)) =
      (hessian f x - hessian f y) w := by
    simp only [A, sub_apply, hessian_objective_apply hf, map_sub,
      left_sumEquivProd_symm, left_inl]
  rw [← hproj]
  apply (norm_left_le _).trans
  simpa only [EuclideanSpace.OrthogonalSum.norm_inl] using
    A.le_opNorm (EuclideanSpace.OrthogonalSum.inl w)

/-- Helper for thm:main: adjoining an identity quadratic block preserves a
global Hölder Hessian bound with the same exponent and constant. -/
theorem hessianHolder_objective {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : EuclideanSpace ℝ ι → ℝ} (hf : ContDiff ℝ 2 f)
    {C β : ℝ} (hC : 0 ≤ C) (hβ : 0 ≤ β)
    (h : ∀ x y, ‖hessian f x - hessian f y‖ ≤ C * ‖x - y‖ ^ β)
    (p q : EuclideanSpace ℝ (ι ⊕ κ)) :
    ‖hessian (objective (κ := κ) f) p - hessian (objective (κ := κ) f) q‖ ≤
      C * ‖p - q‖ ^ β := by
  apply (norm_hessian_objective_sub_le hf p q).trans
  apply (h (left p) (left q)).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply Real.rpow_le_rpow (norm_nonneg _) _ hβ
  rw [← map_sub]
  exact norm_left_le (p - q)

end EuclideanSpace.OrthogonalSum.Gradient
