/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

noncomputable section

open scoped Gradient

universe u

section Objective

variable {E : Type u} [NormedAddCommGroup E]

/-- The quadratic regularization of `f` centered at `x0` with parameter `δ`. -/
def quadraticallyRegularizedObjective (f : E → ℝ) (δ : ℝ) (x0 : E) : E → ℝ :=
  fun x ↦ f x + (δ / 2) * ‖x - x0‖ ^ (2 : ℕ)

/-- Evaluating the quadratic regularization recovers the centered squared-distance penalty. -/
@[simp] theorem quadraticallyRegularizedObjective_apply (f : E → ℝ) (δ : ℝ) (x0 x : E) :
    quadraticallyRegularizedObjective f δ x0 x =
      f x + (δ / 2) * ‖x - x0‖ ^ (2 : ℕ) :=
  rfl

end Objective

section ObjectiveStrongConvexity

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem strongConvexOn_origin_quadraticPenalty (δ : ℝ) :
    StrongConvexOn Set.univ δ (fun x : E ↦ (δ / 2) * ‖x‖ ^ (2 : ℕ)) := by
  rw [strongConvexOn_iff_convex]
  simpa using convexOn_const (0 : ℝ) convex_univ

private theorem strongConvexOn_translate_sub
    {δ : ℝ} {f : E → ℝ} (hf : StrongConvexOn Set.univ δ f) (x0 : E) :
    StrongConvexOn Set.univ δ (fun x ↦ f (x - x0)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let u := x - x0
  let v := y - x0
  have h :
      f (a • u + b • v) ≤
        a * f u + b * f v - a * b * ((δ / 2) * ‖u - v‖ ^ (2 : ℕ)) :=
    hf.2 (by simp [u]) (by simp [v]) ha hb hab
  have hcomb : a • u + b • v = (a • x + b • y) - x0 := by
    dsimp [u, v]
    calc
      a • (x - x0) + b • (y - x0)
          = a • x + a • (-x0) + (b • y + b • (-x0)) := by
              simp [sub_eq_add_neg, smul_add]
      _ = a • x + b • y + (a • (-x0) + b • (-x0)) := by
            abel_nf
      _ = a • x + b • y + (a + b) • (-x0) := by
            rw [← add_smul]
      _ = a • x + b • y + -x0 := by
            simp [hab]
      _ = (a • x + b • y) - x0 := by
            simp [sub_eq_add_neg]
  have huv : u - v = x - y := by
    dsimp [u, v]
    abel_nf
  rw [hcomb, huv] at h
  simpa [u, v, sub_eq_add_neg, hab, add_assoc, add_left_comm, add_comm] using h

/-- The centered quadratic regularization with zero base objective is `δ`-strongly convex on the
whole space. -/
theorem quadraticallyRegularizedObjective_zero_strongConvexOn (x0 : E) (δ : ℝ) :
    StrongConvexOn Set.univ δ (quadraticallyRegularizedObjective (fun _ : E ↦ 0) δ x0) := by
  have hq :
      quadraticallyRegularizedObjective (fun _ : E ↦ 0) δ x0 =
        fun x : E ↦ (δ / 2) * ‖x - x0‖ ^ (2 : ℕ) := by
    funext x
    simp [quadraticallyRegularizedObjective_apply]
  exact hq.symm ▸
    strongConvexOn_translate_sub (strongConvexOn_origin_quadraticPenalty δ) x0

end ObjectiveStrongConvexity

section TaylorModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine model of `f` at `x` with an explicit first-order field `g`. -/
def affineModelAt (f : E → ℝ) (g : E → E) (x : E) : E → ℝ :=
  fun y ↦ f x + inner ℝ (g x) (y - x)

/-- Evaluating `affineModelAt f g x` recovers the displayed affine formula. -/
@[simp] theorem affineModelAt_apply (f : E → ℝ) (g : E → E) (x y : E) :
    affineModelAt f g x y =
      f x + inner ℝ (g x) (y - x) :=
  rfl

end TaylorModel

section TaylorModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The first-order Taylor model of `f` at `x`, written with the totalized Chapter 1 gradient
`∇ f x`. -/
abbrev firstOrderTaylorModelAt (f : E → ℝ) (x : E) : E → ℝ :=
  affineModelAt f (∇ f) x

/-- Evaluating `firstOrderTaylorModelAt f x` recovers the displayed affine formula. -/
@[simp] theorem firstOrderTaylorModelAt_apply (f : E → ℝ) (x y : E) :
    firstOrderTaylorModelAt f x y =
      f x + inner ℝ (∇ f x) (y - x) :=
  rfl

/-- The first-order Taylor model is convex on every convex set. -/
theorem firstOrderTaylorModelAt_convexOn
    (s : Set E) (hs : Convex ℝ s) (f : E → ℝ) (xBar : E) :
    ConvexOn ℝ s (firstOrderTaylorModelAt f xBar) := by
  have hAffine :
      ConvexOn ℝ s
        (fun x : E ↦
          inner ℝ (∇ f xBar) x +
            (f xBar - inner ℝ (∇ f xBar) xBar)) := by
    simpa [Pi.add_apply] using
      ((innerSL ℝ (∇ f xBar)).convexOn hs).add_const
        (f xBar - inner ℝ (∇ f xBar) xBar)
  refine hAffine.congr ?_
  intro x hx
  change
    inner ℝ (∇ f xBar) x + (f xBar - inner ℝ (∇ f xBar) xBar) =
      f xBar + inner ℝ (∇ f xBar) (x - xBar)
  rw [inner_sub_right]
  ring

/-- Completing the square rewrites the quadratically regularized first-order model at `xBar` as a
constant plus a squared-distance term from the explicit gradient step. -/
theorem gradient_quadratic_model_eq_completedSquare
    (f : E → ℝ) (xBar x : E) {γ : ℝ} (hγ : γ ≠ 0) :
    quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) γ xBar x =
      f xBar + (γ / 2) * ‖x - (xBar - γ⁻¹ • ∇ f xBar)‖ ^ (2 : ℕ) -
        (1 / (2 * γ)) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
  have hsub :
      x - (xBar - γ⁻¹ • ∇ f xBar) = (x - xBar) + γ⁻¹ • ∇ f xBar := by
    abel_nf
  have hsq :
      (γ / 2 : ℝ) * ‖x - (xBar - γ⁻¹ • ∇ f xBar)‖ ^ (2 : ℕ) =
        (γ / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
          inner ℝ (∇ f xBar) (x - xBar) +
          (1 / (2 * γ)) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
    calc
      (γ / 2 : ℝ) * ‖x - (xBar - γ⁻¹ • ∇ f xBar)‖ ^ (2 : ℕ)
          = (γ / 2 : ℝ) *
              inner ℝ (x - (xBar - γ⁻¹ • ∇ f xBar)) (x - (xBar - γ⁻¹ • ∇ f xBar)) := by
                rw [real_inner_self_eq_norm_sq]
      _ = (γ / 2 : ℝ) *
            inner ℝ ((x - xBar) + γ⁻¹ • ∇ f xBar) ((x - xBar) + γ⁻¹ • ∇ f xBar) := by
              rw [hsub]
      _ = (γ / 2 : ℝ) *
            (inner ℝ (x - xBar) (x - xBar) +
              inner ℝ (x - xBar) (γ⁻¹ • ∇ f xBar) +
              inner ℝ (γ⁻¹ • ∇ f xBar) (x - xBar) +
              inner ℝ (γ⁻¹ • ∇ f xBar) (γ⁻¹ • ∇ f xBar)) := by
                rw [inner_add_add_self]
      _ = (γ / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
            inner ℝ (∇ f xBar) (x - xBar) +
            (1 / (2 * γ)) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
              rw [real_inner_self_eq_norm_sq, inner_smul_right, real_inner_smul_left,
                real_inner_smul_left, inner_smul_right, real_inner_self_eq_norm_sq]
              have hcomm : inner ℝ (x - xBar) (∇ f xBar) = inner ℝ (∇ f xBar) (x - xBar) := by
                simpa using (real_inner_comm (x - xBar) (∇ f xBar)).symm
              rw [hcomm]
              field_simp [hγ]
              ring
  rw [quadraticallyRegularizedObjective_apply, firstOrderTaylorModelAt_apply]
  calc
    f xBar + inner ℝ (∇ f xBar) (x - xBar) + (γ / 2) * ‖x - xBar‖ ^ (2 : ℕ) =
        f xBar +
          ((γ / 2 : ℝ) * ‖x - xBar‖ ^ (2 : ℕ) +
            inner ℝ (∇ f xBar) (x - xBar) +
            (1 / (2 * γ)) * ‖∇ f xBar‖ ^ (2 : ℕ)) -
          (1 / (2 * γ)) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
      ring
    _ = f xBar + (γ / 2) * ‖x - (xBar - γ⁻¹ • ∇ f xBar)‖ ^ (2 : ℕ) -
          (1 / (2 * γ)) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
      rw [← hsq]

end TaylorModel
