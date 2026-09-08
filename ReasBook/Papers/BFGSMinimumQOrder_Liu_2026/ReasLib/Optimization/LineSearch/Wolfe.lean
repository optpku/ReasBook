module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import ReasLib.Optimization.LineSearch.Ratio

public section

/-!
# Wolfe line-search conditions

This module models Wolfe conditions through endpoint directional derivatives.  The core API
therefore needs only a real module as its search space; Frechet derivatives and gradients are
provided by separate adapters.
-/

noncomputable section

universe u

namespace LineSearch.Wolfe

/-- Admissible coefficients for weak or strong Wolfe conditions. -/
structure Coefficients where
  c₁ : ℝ
  c₂ : ℝ
  c₁_pos : 0 < c₁
  c₁_lt_c₂ : c₁ < c₂
  c₂_lt_one : c₂ < 1

/-- The first coefficient in an admissible Wolfe pair is nonnegative. -/
theorem Coefficients.c₁_nonneg (p : Coefficients) : 0 ≤ p.c₁ :=
  p.c₁_pos.le

/-- The first coefficient in an admissible Wolfe pair is less than one. -/
theorem Coefficients.c₁_lt_one (p : Coefficients) : p.c₁ < 1 :=
  p.c₁_lt_c₂.trans p.c₂_lt_one

/-- The second coefficient in an admissible Wolfe pair is positive. -/
theorem Coefficients.c₂_pos (p : Coefficients) : 0 < p.c₂ :=
  p.c₁_pos.trans p.c₁_lt_c₂

/-- The second coefficient in an admissible Wolfe pair is nonnegative. -/
theorem Coefficients.c₂_nonneg (p : Coefficients) : 0 ≤ p.c₂ :=
  p.c₂_pos.le

/-- The scalar Armijo sufficient-decrease condition. -/
def IsArmijo (c₁ before after slope : ℝ) : Prop :=
  after ≤ before + c₁ * slope

/-- The scalar weak-Wolfe curvature condition. -/
def IsWeakCurvature (c₂ slope nextSlope : ℝ) : Prop :=
  c₂ * slope ≤ nextSlope

/-- The scalar strong-Wolfe curvature condition. -/
def IsStrongCurvature (c₂ slope nextSlope : ℝ) : Prop :=
  |nextSlope| ≤ c₂ * |slope|

/-- The scalar Armijo predicate unfolds to its defining inequality. -/
theorem isArmijo_iff {c₁ before after slope : ℝ} :
    IsArmijo c₁ before after slope ↔ after ≤ before + c₁ * slope :=
  Iff.rfl

/-- The scalar weak-curvature predicate unfolds to its defining inequality. -/
theorem isWeakCurvature_iff {c₂ slope nextSlope : ℝ} :
    IsWeakCurvature c₂ slope nextSlope ↔ c₂ * slope ≤ nextSlope :=
  Iff.rfl

/-- The scalar strong-curvature predicate unfolds to its defining inequality. -/
theorem isStrongCurvature_iff {c₂ slope nextSlope : ℝ} :
    IsStrongCurvature c₂ slope nextSlope ↔ |nextSlope| ≤ c₂ * |slope| :=
  Iff.rfl

/-- A normalized objective decrease proves the scalar Armijo condition along a descent
direction. -/
theorem IsArmijo.of_decreaseRatio {c₁ before after slope : ℝ}
    (descent : slope < 0)
    (decrease : c₁ ≤ (before - after) / (-slope)) :
    IsArmijo c₁ before after slope := by
  apply armijo_of_decrease_ratio_lower_bound (neg_pos.mpr descent)
  · ring
  · exact decrease
  · exact le_rfl

/-- Multiplicative control of the next slope proves strong curvature. -/
theorem IsStrongCurvature.of_eq_mul {c₂ slope nextSlope ratio : ℝ}
    (next_eq : nextSlope = ratio * slope) (ratio_le : |ratio| ≤ c₂) :
    IsStrongCurvature c₂ slope nextSlope := by
  rw [IsStrongCurvature, next_eq, abs_mul]
  exact mul_le_mul_of_nonneg_right ratio_le (abs_nonneg slope)

/-- Strong curvature implies weak curvature along a nonascending direction. -/
theorem IsStrongCurvature.weak {c₂ slope nextSlope : ℝ}
    (h : IsStrongCurvature c₂ slope nextSlope) (descent : slope ≤ 0) :
    IsWeakCurvature c₂ slope nextSlope := by
  rw [IsStrongCurvature, abs_of_nonpos descent] at h
  rw [IsWeakCurvature]
  have lower : -|nextSlope| ≤ nextSlope := neg_abs_le nextSlope
  linarith

/-- A step satisfies the weak Wolfe conditions when its two endpoint line derivatives exist
and obey Armijo and weak curvature. -/
structure IsWeak {E : Type u} [AddCommGroup E] [Module ℝ E]
    (p : Coefficients) (f : E → ℝ) (x s : E) : Prop where
  lineDifferentiableAt : LineDifferentiableAt ℝ f x s
  lineDifferentiableAtNext : LineDifferentiableAt ℝ f (x + s) s
  armijo : IsArmijo p.c₁ (f x) (f (x + s)) (lineDeriv ℝ f x s)
  weakCurvature :
    IsWeakCurvature p.c₂ (lineDeriv ℝ f x s) (lineDeriv ℝ f (x + s) s)

/-- A step satisfies the strong Wolfe conditions when its two endpoint line derivatives exist
and obey Armijo and absolute curvature. -/
structure IsStrong {E : Type u} [AddCommGroup E] [Module ℝ E]
    (p : Coefficients) (f : E → ℝ) (x s : E) : Prop where
  lineDifferentiableAt : LineDifferentiableAt ℝ f x s
  lineDifferentiableAtNext : LineDifferentiableAt ℝ f (x + s) s
  armijo : IsArmijo p.c₁ (f x) (f (x + s)) (lineDeriv ℝ f x s)
  strongCurvature :
    IsStrongCurvature p.c₂ (lineDeriv ℝ f x s) (lineDeriv ℝ f (x + s) s)

/-- Certified endpoint line derivatives construct weak Wolfe satisfaction. -/
theorem IsWeak.ofHasLineDerivAt {E : Type u} [AddCommGroup E] [Module ℝ E]
    {p : Coefficients} {f : E → ℝ} {x s : E} {slope nextSlope : ℝ}
    (atStart : HasLineDerivAt ℝ f slope x s)
    (atNext : HasLineDerivAt ℝ f nextSlope (x + s) s)
    (armijo : IsArmijo p.c₁ (f x) (f (x + s)) slope)
    (curvature : IsWeakCurvature p.c₂ slope nextSlope) :
    IsWeak p f x s := by
  refine {
    lineDifferentiableAt := atStart.lineDifferentiableAt
    lineDifferentiableAtNext := atNext.lineDifferentiableAt
    armijo := ?_
    weakCurvature := ?_
  }
  · simpa only [atStart.lineDeriv] using armijo
  · simpa only [atStart.lineDeriv, atNext.lineDeriv] using curvature

/-- Certified endpoint line derivatives construct strong Wolfe satisfaction. -/
theorem IsStrong.ofHasLineDerivAt {E : Type u} [AddCommGroup E] [Module ℝ E]
    {p : Coefficients} {f : E → ℝ} {x s : E} {slope nextSlope : ℝ}
    (atStart : HasLineDerivAt ℝ f slope x s)
    (atNext : HasLineDerivAt ℝ f nextSlope (x + s) s)
    (armijo : IsArmijo p.c₁ (f x) (f (x + s)) slope)
    (curvature : IsStrongCurvature p.c₂ slope nextSlope) :
    IsStrong p f x s := by
  refine {
    lineDifferentiableAt := atStart.lineDifferentiableAt
    lineDifferentiableAtNext := atNext.lineDifferentiableAt
    armijo := ?_
    strongCurvature := ?_
  }
  · simpa only [atStart.lineDeriv] using armijo
  · simpa only [atStart.lineDeriv, atNext.lineDeriv] using curvature

/-- Strong Wolfe satisfaction becomes weak Wolfe satisfaction along a nonascending step. -/
theorem IsStrong.toWeak {E : Type u} [AddCommGroup E] [Module ℝ E]
    {p : Coefficients} {f : E → ℝ} {x s : E} (h : IsStrong p f x s)
    (descent : lineDeriv ℝ f x s ≤ 0) : IsWeak p f x s where
  lineDifferentiableAt := h.lineDifferentiableAt
  lineDifferentiableAtNext := h.lineDifferentiableAtNext
  armijo := h.armijo
  weakCurvature := h.strongCurvature.weak descent

/-- Weak Wolfe curvature strictly increases a strictly negative endpoint slope. -/
theorem IsWeak.slope_lt_next {E : Type u} [AddCommGroup E] [Module ℝ E]
    {p : Coefficients} {f : E → ℝ} {x s : E} (h : IsWeak p f x s)
    (descent : lineDeriv ℝ f x s < 0) :
    lineDeriv ℝ f x s < lineDeriv ℝ f (x + s) s := by
  have scaled : lineDeriv ℝ f x s < p.c₂ * lineDeriv ℝ f x s := by
    simpa only [one_mul] using mul_lt_mul_of_neg_right p.c₂_lt_one descent
  exact scaled.trans_le h.weakCurvature

/-- Along a descent step, weak Wolfe curvature makes the secant slope positive. -/
theorem IsWeak.secantSlope_pos {E : Type u} [AddCommGroup E] [Module ℝ E]
    {p : Coefficients} {f : E → ℝ} {x s : E} (h : IsWeak p f x s)
    (descent : lineDeriv ℝ f x s < 0) :
    0 < lineDeriv ℝ f (x + s) s - lineDeriv ℝ f x s := by
  exact sub_pos.mpr (h.slope_lt_next descent)

end LineSearch.Wolfe
