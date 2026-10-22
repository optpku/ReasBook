/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.FirstOrderTaylorModel
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open AffineMap
open scoped ConvexC1 Gradient SeminormDualNorm

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p] {L : NNReal}
variable {Q : Set E} {f : E → ℝ}

/- Primary domain: first-order smooth convex analysis on real Hilbert spaces with an arbitrary
norm-like seminorm.

Sampled owner-style declarations:
* `ConvexC1On` in `Definition_2_4`
* mathlib `HasGradientAt`
* mathlib `gradient`
* `convexC1On_iff_gradient_monotone` in `Theorem_2_3`
* `Seminorm.dualNorm` in `Definition_2_5`
* `Seminorm.dualNorm_normSeminorm_eq_norm` in `Lemma_2_3`

Source/core/bridge triage:
* source-facing: `ConvexC1SeminormSmoothOn p L Q f`
* core/canonical: `ConvexC1On Q f` together with actual ambient-gradient data
  `HasGradientAt f (∇ f x) x` on `Q` and the dual-norm Lipschitz inequality for `∇ f`
* bridge/view: the whole-space specialization `ConvexC1SeminormSmooth p L f` and, for
  `p = normSeminorm ℝ E`, the metric reformulation `ConvexC1SeminormSmooth.gradient_lipschitz`

Primitive data:
* the set `Q`
* the function `f`
* the owner predicate `ConvexC1On Q f`
* the ambient gradient witnesses `HasGradientAt f (∇ f x) x` on `Q`
* the dual-norm Lipschitz bound for `∇ f` on `Q`

Derived API:
* owner projections to `ContDiffOn` and `ConvexOn`
* the whole-space owner view with ambient gradient `∇ f`
* the ambient-norm `LipschitzWith` reformulation for `p = normSeminorm ℝ E`
* semantic recall note: `lean_leansearch` did not expose a direct mathlib owner for the bundled
  `(2.1.12)` gradient-witness clause, so this file keeps the local bundled API
-/

/-- A function belongs to the smooth-convex class `𝓕_L^{1,1}(Q, ‖·‖)` when it is `C¹` convex on
`Q`, its ambient gradient is defined at every feasible point, and that ambient gradient is
`L`-Lipschitz on `Q` with respect to the seminorm `p` and the dual seminorm `‖·‖[p,*]`. This
keeps the arbitrary-set API faithful to the textbook gradient inequalities instead of relying on
the total fallback behavior of `gradientWithin`. -/
abbrev ConvexC1SeminormSmoothOn
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (Q : Set E) (f : E → ℝ) : Prop :=
  ConvexC1On Q f ∧
    (∀ ⦃x⦄, x ∈ Q → HasGradientAt f (∇ f x) x) ∧
    ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
      ‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y)

scoped[SmoothConvex] notation "𝓕[" L ", " p "]¹¹(" Q ")" =>
  setOf (ConvexC1SeminormSmoothOn p L Q)

open scoped SmoothConvex

/-- Membership in `𝓕[L, p]¹¹(Q)` includes the owner `C¹` convexity data on `Q`. -/
theorem ConvexC1SeminormSmoothOn.convexC1On
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    ConvexC1On Q f :=
  hf.1

/-- Membership in `𝓕[L, p]¹¹(Q)` includes `C¹` regularity on `Q`. -/
theorem ConvexC1SeminormSmoothOn.contDiffOn
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    ContDiffOn ℝ 1 f Q :=
  convexC1On_contDiffOn hf.1

/-- Membership in `𝓕[L, p]¹¹(Q)` includes the ambient gradient witness at every feasible point. -/
theorem ConvexC1SeminormSmoothOn.hasGradientAt
    (hf : ConvexC1SeminormSmoothOn p L Q f)
    {x : E} (hx : x ∈ Q) :
    HasGradientAt f (∇ f x) x :=
  hf.2.1 hx

/-- Membership in `𝓕[L, p]¹¹(Q)` includes convexity on `Q`. -/
theorem ConvexC1SeminormSmoothOn.convexOn
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    ConvexOn ℝ Q f :=
  convexC1On_convexOn hf.1

/-- Membership in `𝓕[L, p]¹¹(Q)` forces the feasible set `Q` itself to be convex. -/
theorem ConvexC1SeminormSmoothOn.convex
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    Convex ℝ Q :=
  hf.convexOn.1

/-- The whole-space class `𝓕_L^{1,1}(E, ‖·‖)` is the ambient-gradient view of the set-based owner
`ConvexC1SeminormSmoothOn`. The textbook Euclidean class is the finite-dimensional
specialization. -/
abbrev ConvexC1SeminormSmooth
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (f : E → ℝ) : Prop :=
  ConvexC1SeminormSmoothOn p L Set.univ f

scoped[SmoothConvex] notation "𝓕[" L ", " p "]¹¹" =>
  setOf (ConvexC1SeminormSmooth p L)

/-- The set-based notation `𝓕[L, p]¹¹(Q)` is the source-facing set view of the owner predicate
`ConvexC1SeminormSmoothOn p L Q`. -/
theorem mem_F11On_iff : f ∈ 𝓕[L, p]¹¹(Q) ↔ ConvexC1SeminormSmoothOn p L Q f :=
  Iff.rfl

/-- The whole-space notation `𝓕[L, p]¹¹` is the source-facing set view of the owner predicate
`ConvexC1SeminormSmooth p L`. -/
theorem mem_F11_iff : f ∈ 𝓕[L, p]¹¹ ↔ ConvexC1SeminormSmooth p L f :=
  Iff.rfl

/-- Membership in `𝓕[L, p]¹¹` retains the whole-space `ConvexC1On` owner predicate. -/
theorem ConvexC1SeminormSmooth.convexC1On
    (hf : ConvexC1SeminormSmooth p L f) :
    ConvexC1On Set.univ f :=
  hf.1

/-- Membership in `𝓕[L, p]¹¹` includes global `C¹` regularity. -/
theorem ConvexC1SeminormSmooth.contDiff
    (hf : ConvexC1SeminormSmooth p L f) :
    ContDiff ℝ 1 f :=
  contDiffOn_univ.mp (convexC1On_contDiffOn hf.1)

/-- Membership in `𝓕[L, p]¹¹` includes the canonical ambient gradient at every point. -/
theorem ConvexC1SeminormSmooth.hasGradientAt
    (hf : ConvexC1SeminormSmooth p L f) (x : E) :
    HasGradientAt f (∇ f x) x :=
  hf.2.1 (by simp)

/-- Membership in `𝓕[L, p]¹¹` includes whole-space convexity. -/
theorem ConvexC1SeminormSmooth.convexOn
    (hf : ConvexC1SeminormSmooth p L f) :
    ConvexOn ℝ Set.univ f :=
  convexC1On_convexOn hf.1

/-- Membership in `𝓕[L, p]¹¹` gives the defining dual-norm Lipschitz bound for the ambient
gradient on the whole space. -/
theorem ConvexC1SeminormSmooth.dualNorm_gradient_sub_le
    (hf : ConvexC1SeminormSmooth p L f)
    (x y : E) :
    ‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y) :=
  hf.2.2 (by simp) (by simp)

/-- For the ambient norm seminorm, membership in `𝓕[L, normSeminorm ℝ E]¹¹` makes the gradient
`L`-Lipschitz in the ordinary norm. -/
theorem ConvexC1SeminormSmooth.gradient_lipschitz
    (hf : ConvexC1SeminormSmooth (normSeminorm ℝ E) L f) :
    LipschitzWith L (∇ f) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  simpa [dist_eq_norm, Seminorm.dualNorm_normSeminorm_eq_norm] using
    hf.dualNorm_gradient_sub_le x y

/-- A global minimizer of a smooth convex objective carries the canonical stationary-point witness
`HasGradientAt f 0 xStar`. -/
theorem ConvexC1SeminormSmooth.hasGradientAt_zero_of_isMinOn
    (hf : ConvexC1SeminormSmooth (normSeminorm ℝ E) L f)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar) :
    HasGradientAt f 0 xStar :=
  isMinOn_hasGradientAt_zero_of_differentiableAt (hf.contDiff.differentiable_one xStar) hxStar

/-- Every global minimizer of a smooth convex objective in `𝓕[L, normSeminorm ℝ E]¹¹` is
stationary. -/
theorem ConvexC1SeminormSmooth.gradient_eq_zero_of_isMinOn
    (hf : ConvexC1SeminormSmooth (normSeminorm ℝ E) L f)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar) :
    ∇ f xStar = 0 := by
  exact (hf.hasGradientAt_zero_of_isMinOn hxStar).gradient

/-- Membership in `𝓕[L, p]¹¹(Q)` gives the defining dual-norm Lipschitz bound for the ambient
gradient on `Q`. -/
-- Proof sketch: unfold `ConvexC1SeminormSmoothOn` and project to the gradient-Lipschitz clause.
theorem ConvexC1SeminormSmoothOn.dualNorm_gradient_sub_le
    (hf : ConvexC1SeminormSmoothOn p L Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    ‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y) :=
  hf.2.2 hx hy

/-- The whole-space view `𝓕[L, p]¹¹` is the `Q = Set.univ` specialization of the set-based owner
`𝓕[L, p]¹¹(Q)`. -/
theorem ConvexC1SeminormSmooth.toOn
    (hf : ConvexC1SeminormSmooth p L f) :
    ConvexC1SeminormSmoothOn p L Set.univ f :=
  hf

section TangentErrorBoundsOn

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : Seminorm ℝ E} {L : NNReal} {g : E → E} {Q : Set E} {f : E → ℝ}

/-- The condition `(2.1.9)` on a set `Q`: the tangent-plane error of `f` is nonnegative and at
most `(L / 2) ‖x - y‖²` with respect to the seminorm `p`, measured with an explicit gradient field
`g` on `Q`.
-/
def smoothConvexTangentErrorBoundsOn
    (p : Seminorm ℝ E) (L : NNReal) (g : E → E) (Q : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
    0 ≤ f y - f x - inner ℝ (g x) (y - x) ∧
      f y - f x - inner ℝ (g x) (y - x) ≤
        ((L : ℝ) / 2) * (p (x - y)) ^ 2

/-- Membership in `(2.1.9)` gives the nonnegativity half of the tangent error bound. -/
theorem smoothConvexTangentErrorBoundsOn.nonneg
    (hf : smoothConvexTangentErrorBoundsOn p L g Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    0 ≤ f y - f x - inner ℝ (g x) (y - x) :=
  (hf hx hy).1

/-- Membership in `(2.1.9)` gives the quadratic upper bound for the tangent error. -/
theorem smoothConvexTangentErrorBoundsOn.upperBound
    (hf : smoothConvexTangentErrorBoundsOn p L g Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y - f x - inner ℝ (g x) (y - x) ≤
      ((L : ℝ) / 2) * (p (x - y)) ^ 2 :=
  (hf hx hy).2

end TangentErrorBoundsOn

/-- The condition `(2.1.10)` on a set `Q`: the value at `y` dominates the tangent model at `x`
plus the squared dual norm of the gradient-field difference. The separate positivity
assumption `0 < L` belongs to the surrounding theorem hypotheses, not to this displayed
inequality itself. -/
def smoothConvexGradientQuadraticLowerBoundOn
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (g : E → E) (Q : Set E)
    (f : E → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
    f x + inner ℝ (g x) (y - x) +
        (1 / (2 * (L : ℝ))) *
          (‖g x - g y‖[p,*]) ^ 2 ≤
      f y

/-- The condition `(2.1.11)` on a set `Q`: the gradient field `g` is `1 / L`-cocoercive with
respect to the seminorm `p` and its dual norm. The separate positivity assumption `0 < L` belongs
to the surrounding theorem hypotheses, not to this displayed inequality itself. -/
def smoothConvexCocoerciveGradientOn
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (g : E → E) (Q : Set E) : Prop :=
  ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
    (1 / (L : ℝ)) * (‖g x - g y‖[p,*]) ^ 2 ≤
      inner ℝ (g x - g y) (x - y)

section MonotoneGradientBoundsOn

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {p : Seminorm ℝ E} {L : NNReal} {g : E → E} {Q : Set E}

/-- The condition `(2.1.12)` on a set `Q`: the gradient field `g` is monotone and the
monotonicity pairing is bounded above by `L ‖x - y‖²` with respect to `p`. -/
def smoothConvexMonotoneGradientBoundsOn
    (p : Seminorm ℝ E) (L : NNReal) (g : E → E) (Q : Set E) : Prop :=
  (∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → 0 ≤ inner ℝ (g x - g y) (x - y)) ∧
    ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
      inner ℝ (g x - g y) (x - y) ≤
        (L : ℝ) * (p (x - y)) ^ 2

/-- Membership in `(2.1.12)` recovers the monotonicity half of the gradient-field bound. -/
theorem smoothConvexMonotoneGradientBoundsOn.monotone
    (hf : smoothConvexMonotoneGradientBoundsOn p L g Q) :
    ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → 0 ≤ inner ℝ (g x - g y) (x - y) :=
  hf.1

/-- Membership in `(2.1.12)` gives the upper quadratic bound for the monotonicity pairing. -/
theorem smoothConvexMonotoneGradientBoundsOn.upperBound
    (hf : smoothConvexMonotoneGradientBoundsOn p L g Q) :
    ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
      inner ℝ (g x - g y) (x - y) ≤
        (L : ℝ) * (p (x - y)) ^ 2 :=
  hf.2

end MonotoneGradientBoundsOn

/-- The source-facing version of `(2.1.12)` for a function `f`: the ambient field `∇ f`
satisfies the monotonicity and upper pairing bounds on `Q`, and each value `∇ f x` is witnessed
to be the genuine ambient gradient of `f` at `x`. This keeps the theorem statement tied to the
actual gradient rather than Lean's totalized `gradient` fallback. -/
abbrev smoothConvexMonotoneGradientBoundsWithGradientOn
    (p : Seminorm ℝ E) (L : NNReal) (Q : Set E) (f : E → ℝ) : Prop :=
  (∀ ⦃x⦄, x ∈ Q → HasGradientAt f (∇ f x) x) ∧
    smoothConvexMonotoneGradientBoundsOn p L (∇ f) Q

/-- The bundled `(2.1.12)` condition records the ambient-gradient witness at each feasible point.
-/
theorem smoothConvexMonotoneGradientBoundsWithGradientOn.hasGradientAt
    (hf : smoothConvexMonotoneGradientBoundsWithGradientOn p L Q f)
    {x : E} (hx : x ∈ Q) :
    HasGradientAt f (∇ f x) x :=
  hf.1 hx

/-- The bundled `(2.1.12)` condition recovers the monotonicity half of the gradient pairing
bound. -/
theorem smoothConvexMonotoneGradientBoundsWithGradientOn.monotone
    (hf : smoothConvexMonotoneGradientBoundsWithGradientOn p L Q f) :
    ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → 0 ≤ inner ℝ (∇ f x - ∇ f y) (x - y) :=
  hf.2.monotone

/-- The bundled `(2.1.12)` condition gives the quadratic upper bound for the monotonicity
pairing. -/
theorem smoothConvexMonotoneGradientBoundsWithGradientOn.upperBound
    (hf : smoothConvexMonotoneGradientBoundsWithGradientOn p L Q f) :
    ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
        (L : ℝ) * (p (x - y)) ^ 2 :=
  hf.2.upperBound

/-- The condition `(2.1.13)` on a set `Q`: every convex combination of two values of `f`
dominates the value at the convex-combination point by a term involving the squared dual norm of
the gradient-field difference. The separate positivity assumption `0 < L` belongs to the
surrounding theorem hypotheses, not to this displayed inequality itself. -/
def smoothConvexConvexCombinationGradientBoundOn
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (g : E → E) (Q : Set E)
    (f : E → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Icc (0 : ℝ) 1 →
    α * f x + (1 - α) * f y ≥
      f (α • x + (1 - α) • y) +
        (α * (1 - α) / (2 * (L : ℝ))) *
          (‖g x - g y‖[p,*]) ^ 2

section ConvexCombinationQuadraticBoundOn

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable {p : Seminorm ℝ E} {L : NNReal} {Q : Set E} {f : E → ℝ}

/-- The condition `(2.1.14)` on a set `Q`: the Jensen gap of `f` is nonnegative and at most
`α (1 - α) (L / 2) ‖x - y‖²` with respect to `p`. -/
def smoothConvexConvexCombinationQuadraticBoundOn
    (p : Seminorm ℝ E) (L : NNReal) (Q : Set E) (f : E → ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q → ∀ ⦃α : ℝ⦄, α ∈ Set.Icc (0 : ℝ) 1 →
    0 ≤ α * f x + (1 - α) * f y - f (α • x + (1 - α) • y) ∧
      α * f x + (1 - α) * f y - f (α • x + (1 - α) • y) ≤
        α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ 2

/-- Membership in `(2.1.14)` gives the nonnegativity of the Jensen gap. -/
theorem smoothConvexConvexCombinationQuadraticBoundOn.nonneg
    (hf : smoothConvexConvexCombinationQuadraticBoundOn p L Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ α * f x + (1 - α) * f y - f (α • x + (1 - α) • y) :=
  (hf hx hy hα).1

/-- Membership in `(2.1.14)` gives the quadratic upper bound for the Jensen gap. -/
theorem smoothConvexConvexCombinationQuadraticBoundOn.upperBound
    (hf : smoothConvexConvexCombinationQuadraticBoundOn p L Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    α * f x + (1 - α) * f y - f (α • x + (1 - α) • y) ≤
      α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ 2 :=
  (hf hx hy hα).2

end ConvexCombinationQuadraticBoundOn

/-- Helper for Theorem 2.5: along a feasible segment, the corrected first-order remainder has
derivative given by the gradient increment paired with the segment direction. -/
private lemma segment_corrected_remainder_hasDerivAt
    (hf : ConvexC1SeminormSmoothOn p L Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun u : ℝ ↦ f (x + u • (y - x)) - f x - u * inner ℝ (∇ f x) (y - x))
      (inner ℝ (∇ f (x + t • (y - x)) - ∇ f x) (y - x)) t := by
  -- Route correction: differentiate the segment remainder directly from the ambient
  -- `HasGradientAt` witnesses along the feasible line segment.
  have hseg_mem : x + t • (y - x) ∈ Q := by
    simpa [AffineMap.lineMap_apply, add_comm, add_left_comm, add_assoc] using
      hf.convex.mapsTo_lineMap hx hy ⟨ht.1.le, ht.2.le⟩
  have hdiff : DifferentiableAt ℝ f (x + t • (y - x)) :=
    (hf.hasGradientAt hseg_mem).differentiableAt
  have hseg :
      HasDerivAt (fun u : ℝ ↦ f (x + u • (y - x)))
        ((fderiv ℝ f (x + t • (y - x))) (y - x)) t := by
    have hline : HasDerivAt (fun u : ℝ ↦ x + u • (y - x)) (y - x) t := by
      simpa [one_smul] using (((hasDerivAt_id t).smul_const (y - x)).const_add x)
    simpa [Function.comp] using (hdiff.hasFDerivAt.comp t hline.hasFDerivAt).hasDerivAt
  have hlin :
      HasDerivAt (fun u : ℝ ↦ u * inner ℝ (∇ f x) (y - x))
        (inner ℝ (∇ f x) (y - x)) t := by
    simpa [one_mul] using (hasDerivAt_id t).mul_const (inner ℝ (∇ f x) (y - x))
  have hmain :
      HasDerivAt
        (fun u : ℝ ↦ f (x + u • (y - x)) - f x - u * inner ℝ (∇ f x) (y - x))
        (((fderiv ℝ f (x + t • (y - x))) (y - x)) - inner ℝ (∇ f x) (y - x)) t := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hseg.sub ((hasDerivAt_const t (f x)).add hlin)
  -- Rewrite the Fréchet derivative through the canonical gradient pairing.
  convert hmain using 1
  rw [inner_sub_left]
  rw [inner_gradient_left hdiff]

/-- Helper for Theorem 2.5: the right derivative of the scalar slice
`t ↦ f (x + t • (y - x))` at `t = 0` is the ambient gradient pairing at `x`. -/
private lemma segment_slice_hasDerivWithinAt_zero
    {x y : E} (hgrad : HasGradientAt f (∇ f x) x) :
    HasDerivWithinAt
      (fun t : ℝ ↦ f (x + t • (y - x)))
      (inner ℝ (∇ f x) (y - x))
      (Set.Ici (0 : ℝ)) 0 := by
  -- Differentiate the ambient line restriction and rewrite the Fréchet derivative through the
  -- canonical gradient pairing.
  have hslice :
      HasDerivWithinAt
        (fun t : ℝ ↦ f (x + t • (y - x)))
        ((fderiv ℝ f x) (y - x))
        (Set.Ici (0 : ℝ)) 0 :=
    hasDerivWithinAt_directionalSlice_of_differentiableAt hgrad.differentiableAt
  simpa [inner_gradient_left hgrad.differentiableAt] using hslice

/-- Helper for Theorem 2.5: along a segment based at `x`, the secant slopes of the scalar slice
converge to the ambient gradient pairing at `x` when the parameter tends to `0` from the right.
-/
private lemma segment_slope_tendsto_gradientPairing
    {x y : E} (hgrad : HasGradientAt f (∇ f x) x) :
    let φ : ℝ → ℝ := fun t ↦ f (x + t • (y - x))
    Filter.Tendsto (fun β : ℝ ↦ slope φ 0 β)
      (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
      (nhds (inner ℝ (∇ f x) (y - x))) := by
  -- Restrict the one-sided derivative statement to the punctured right neighborhood and rewrite
  -- it as convergence of secant slopes.
  dsimp
  have hslice := (segment_slice_hasDerivWithinAt_zero (x := x) (y := y) hgrad).Ioi_of_Ici
  exact
    (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi (0 : ℝ))).mp hslice

/-- Helper for Theorem 2.5: on the whole space, the corrected first-order remainder along a
segment has derivative given by the gradient increment paired with the segment direction as soon
as the canonical ambient gradient exists pointwise. -/
private lemma segment_corrected_remainder_hasDerivAt_univ_of_hasGradientAt
    (hgrad : ∀ z : E, HasGradientAt f (∇ f z) z)
    {x y : E} {t : ℝ} (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun u : ℝ ↦ f (x + u • (y - x)) - f x - u * inner ℝ (∇ f x) (y - x))
      (inner ℝ (∇ f (x + t • (y - x)) - ∇ f x) (y - x)) t := by
  -- Route correction: for the reverse implications we only need pointwise `HasGradientAt`, not
  -- the full owner `f ∈ 𝓕[L,p]¹¹`.
  have hdiff : DifferentiableAt ℝ f (x + t • (y - x)) :=
    (hgrad (x + t • (y - x))).differentiableAt
  have hseg :
      HasDerivAt (fun u : ℝ ↦ f (x + u • (y - x)))
        ((fderiv ℝ f (x + t • (y - x))) (y - x)) t := by
    have hline : HasDerivAt (fun u : ℝ ↦ x + u • (y - x)) (y - x) t := by
      simpa [one_smul] using (((hasDerivAt_id t).smul_const (y - x)).const_add x)
    simpa [Function.comp] using (hdiff.hasFDerivAt.comp t hline.hasFDerivAt).hasDerivAt
  have hlin :
      HasDerivAt (fun u : ℝ ↦ u * inner ℝ (∇ f x) (y - x))
        (inner ℝ (∇ f x) (y - x)) t := by
    simpa [one_mul] using (hasDerivAt_id t).mul_const (inner ℝ (∇ f x) (y - x))
  have hmain :
      HasDerivAt
        (fun u : ℝ ↦ f (x + u • (y - x)) - f x - u * inner ℝ (∇ f x) (y - x))
        (((fderiv ℝ f (x + t • (y - x))) (y - x)) - inner ℝ (∇ f x) (y - x)) t := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      hseg.sub ((hasDerivAt_const t (f x)).add hlin)
  -- Rewrite the Fréchet derivative through the canonical gradient at the interior point.
  convert hmain using 1
  rw [inner_sub_left]
  rw [inner_gradient_left hdiff]

/-- Helper for Theorem 2.5: the tangent error on a feasible segment is bounded above by the
quadratic seminorm term obtained by integrating the gradient increment bound. -/
private lemma tangent_error_upperBound
    (hf : ConvexC1SeminormSmoothOn p L Q f)
    {x y : E} (hx : x ∈ Q) (hy : y ∈ Q) :
    f y - f x - inner ℝ (∇ f x) (y - x) ≤
      ((L : ℝ) / 2) * (p (x - y)) ^ 2 := by
  let d : E := y - x
  have hmaps : Set.MapsTo (fun t : ℝ ↦ x + t • d) (Set.Icc (0 : ℝ) 1) Q := by
    intro t ht
    simpa [d, AffineMap.lineMap_apply, add_comm, add_left_comm, add_assoc] using
      hf.convex.mapsTo_lineMap hx hy ht
  -- The corrected segment remainder is continuous on `[0, 1]`.
  have hcont :
      ContinuousOn (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d)
        (Set.Icc (0 : ℝ) 1) := by
    have hContinuousOn : ContinuousOn f Q := hf.contDiffOn.continuousOn
    have hsegCont :
        ContinuousOn (fun t : ℝ ↦ f (x + t • d)) (Set.Icc (0 : ℝ) 1) :=
      hContinuousOn.comp (by fun_prop) hmaps
    have hlinCont : Continuous (fun t : ℝ ↦ t * inner ℝ (∇ f x) d) := by
      fun_prop
    exact ((hsegCont.sub continuousOn_const).sub hlinCont.continuousOn)
  -- The derivative formula from the previous helper gives differentiability on `(0, 1)`.
  have hdiff :
      DifferentiableOn ℝ (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d)
        (Set.Ioo (0 : ℝ) 1) := by
    intro t ht
    exact (segment_corrected_remainder_hasDerivAt hf hx hy ht).differentiableAt
      |>.differentiableWithinAt
  -- Control the scalar derivative by dual Cauchy and the defining dual-norm Lipschitz estimate.
  have hbound :
      ‖(fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d) 1 -
          (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d) 0‖ ≤
        ∫ t in (0 : ℝ)..1, (L : ℝ) * t * (p d) ^ (2 : ℕ) := by
    exact norm_sub_le_integral_of_norm_deriv_le_of_le
      (by norm_num) hcont hdiff
      (Filter.Eventually.of_forall fun t ht ↦ by
        have hderivAt := segment_corrected_remainder_hasDerivAt hf hx hy ht
        rw [hderivAt.deriv]
        have hseg_mem : x + t • d ∈ Q := hmaps ⟨ht.1.le, ht.2.le⟩
        have hinner_abs :
            |inner ℝ (∇ f (x + t • d) - ∇ f x) d| ≤
              ‖∇ f (x + t • d) - ∇ f x‖[p,*] * p d := by
          refine abs_le.2 ?_
          constructor
          · have hneg :=
              Seminorm.inner_le_dualNorm_mul p (-d) (∇ f (x + t • d) - ∇ f x)
            have hneg' :
                -(inner ℝ (∇ f (x + t • d) - ∇ f x) d) ≤
                  ‖∇ f (x + t • d) - ∇ f x‖[p,*] * p d := by
              simpa [inner_neg_right] using hneg
            linarith
          · exact Seminorm.inner_le_dualNorm_mul p d (∇ f (x + t • d) - ∇ f x)
        have hgrad_bound :
            ‖∇ f (x + t • d) - ∇ f x‖[p,*] ≤
              (L : ℝ) * p ((x + t • d) - x) :=
          hf.dualNorm_gradient_sub_le hseg_mem hx
        have hseg_norm : p ((x + t • d) - x) = t * p d := by
          calc
            p ((x + t • d) - x) = p (t • d) := by simp
            _ = |t| * p d := by
                  simpa [Real.norm_eq_abs] using (map_smul_eq_mul p t d)
            _ = t * p d := by rw [abs_of_pos ht.1]
        calc
          |inner ℝ (∇ f (x + t • d) - ∇ f x) d| ≤
              ‖∇ f (x + t • d) - ∇ f x‖[p,*] * p d := hinner_abs
          _ ≤ ((L : ℝ) * p ((x + t • d) - x)) * p d := by
                exact mul_le_mul_of_nonneg_right hgrad_bound (apply_nonneg p d)
          _ = ((L : ℝ) * (t * p d)) * p d := by rw [hseg_norm]
          _ = (L : ℝ) * t * (p d) ^ (2 : ℕ) := by ring)
      (by
        have hint : IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 :=
          Continuous.intervalIntegrable continuous_id 0 1
        simpa [mul_assoc] using hint.const_mul ((L : ℝ) * (p d) ^ (2 : ℕ)))
  have hR0 :
      (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d) 0 = 0 := by
    simp [d]
  have hR1 :
      (fun t : ℝ ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d) 1 =
        f y - f x - inner ℝ (∇ f x) (y - x) := by
    simp [d]
  have habs :
      |f y - f x - inner ℝ (∇ f x) (y - x)| ≤
        ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
    rw [hR1, hR0, sub_zero, Real.norm_eq_abs] at hbound
    calc
      |f y - f x - inner ℝ (∇ f x) (y - x)| ≤
          ∫ t in (0 : ℝ)..1, (L : ℝ) * t * (p d) ^ (2 : ℕ) := hbound
      _ = ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
            calc
              ∫ t in (0 : ℝ)..1, (L : ℝ) * t * (p d) ^ (2 : ℕ) =
                  ∫ t in (0 : ℝ)..1, ((L : ℝ) * (p d) ^ (2 : ℕ)) * t := by
                    congr with t
                    ring
              _ = ((L : ℝ) * (p d) ^ (2 : ℕ)) * ∫ t in (0 : ℝ)..1, t := by
                    rw [intervalIntegral.integral_const_mul]
              _ = ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
                    rw [integral_id]
                    norm_num
                    ring
  -- Extract the needed upper inequality from the absolute remainder bound.
  have hupper : f y - f x - inner ℝ (∇ f x) (y - x) ≤ ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) :=
    (abs_le.mp habs).2
  have hp : p d = p (x - y) := by
    simpa [d, neg_sub] using (map_neg_eq_map p (x - y))
  have hp_sym : (p d) ^ (2 : ℕ) = (p (x - y)) ^ (2 : ℕ) := by
    rw [hp]
  calc
    f y - f x - inner ℝ (∇ f x) (y - x) ≤ ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := hupper
    _ = ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by rw [hp_sym]

/-- Helper for Theorem 2.5: every separated seminorm on the finite-dimensional ambient Hilbert
space is bounded above by a positive multiple of the ambient norm. -/
private lemma seminorm_le_mul_norm
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] :
    ∃ C > 0, ∀ x : E, p x ≤ C * ‖x‖ := by
  let b := Module.finBasis ℝ E
  let C : ℝ :=
    (∑ i, ‖((b.coord i).toContinuousLinearMap)‖ * p (b i)) + 1
  have hC_pos : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC_pos, ?_⟩
  intro x
  have hx : x = ∑ i, (b.repr x i) • b i := by
    exact (b.sum_repr x).symm
  have hsum :
      p (∑ i, (b.repr x i) • b i) ≤
        ∑ i, p ((b.repr x i) • b i) := by
    exact
      Finset.le_sum_of_subadditive p (by simp) (map_add_le_add p) Finset.univ
        (fun i ↦ (b.repr x i) • b i)
  calc
    p x = p (∑ i, (b.repr x i) • b i) := congrArg p hx
    _ ≤ ∑ i, p ((b.repr x i) • b i) := by
      simpa using hsum
    _ = ∑ i, |b.repr x i| * p (b i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      simpa [Real.norm_eq_abs] using
        (map_smul_eq_mul p (b.repr x i) (b i))
    _ ≤ ∑ i, (‖((b.coord i).toContinuousLinearMap)‖ * p (b i)) * ‖x‖ := by
      exact Finset.sum_le_sum fun i _ ↦ by
        have hcoeff :
            |b.repr x i| ≤ ‖((b.coord i).toContinuousLinearMap)‖ * ‖x‖ := by
          simpa [Real.norm_eq_abs] using
            ((b.coord i).toContinuousLinearMap.le_opNorm x)
        have hpi_nonneg : 0 ≤ p (b i) := apply_nonneg p (b i)
        calc
          |b.repr x i| * p (b i) ≤
              (‖((b.coord i).toContinuousLinearMap)‖ * ‖x‖) * p (b i) := by
            exact mul_le_mul_of_nonneg_right hcoeff hpi_nonneg
          _ = (‖((b.coord i).toContinuousLinearMap)‖ * p (b i)) * ‖x‖ := by
            ring
    _ ≤ C * ‖x‖ := by
      dsimp [C]
      have hsum_le :
          ∑ i, ‖((b.coord i).toContinuousLinearMap)‖ * p (b i) ≤ C := by
        linarith
      exact le_trans (by rw [← Finset.sum_mul]) (mul_le_mul_of_nonneg_right hsum_le (norm_nonneg _))

/-- Helper for Theorem 2.5: a seminorm bound `p x ≤ C ‖x‖` forces the reverse comparison
`‖g‖ ≤ C ‖g‖[p,*]` on the dual side. -/
private lemma norm_le_mul_dualNorm_of_seminorm_le_mul_norm
    {C : ℝ} (hC_pos : 0 < C)
    (hC : ∀ x : E, p x ≤ C * ‖x‖) :
    ∀ g : E, ‖g‖ ≤ C * ‖g‖[p,*] := by
  intro g
  by_cases hg : g = 0
  · have hdual_zero : ‖(0 : E)‖[p,*] = 0 := by
      rw [Seminorm.dualNorm_apply]
      have hzero_mem : (0 : ℝ) ∈ (fun x : E ↦ inner ℝ (0 : E) x) '' {x : E | p x ≤ 1} := by
        refine ⟨0, ?_, by simp⟩
        simp
      have hnonempty : ((fun x : E ↦ inner ℝ (0 : E) x) '' {x : E | p x ≤ 1}).Nonempty :=
        ⟨0, hzero_mem⟩
      have hbounded : BddAbove ((fun x : E ↦ inner ℝ (0 : E) x) '' {x : E | p x ≤ 1}) := by
        refine ⟨0, ?_⟩
        rintro y ⟨u, hu, rfl⟩
        simp
      refine le_antisymm ?_ ?_
      · refine csSup_le hnonempty ?_
        rintro y ⟨u, hu, rfl⟩
        simp
      · exact le_csSup hbounded hzero_mem
    simpa [hg, hdual_zero]
  · let u : E := ‖g‖⁻¹ • g
    have hg_norm_pos : 0 < ‖g‖ := norm_pos_iff.mpr hg
    have hu_norm : ‖u‖ = 1 := by
      -- Normalize `g` to a unit vector in the ambient norm.
      simp [u, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hg_norm_pos),
        hg_norm_pos.ne']
    have hu_bound : p u ≤ C := by
      -- The primal seminorm bound places the normalized direction in the `C`-scaled `p`-ball.
      calc
        p u ≤ C * ‖u‖ := hC u
        _ = C := by simp [hu_norm]
    have hscaled_mem : C⁻¹ • u ∈ p.closedBall 0 1 := by
      -- Scaling by `C⁻¹` moves that direction into the closed primal unit ball.
      rw [Seminorm.mem_closedBall_zero]
      have hCinv_pos : 0 < C⁻¹ := inv_pos.mpr hC_pos
      have hCp_nonneg : 0 ≤ C⁻¹ := hCinv_pos.le
      calc
        p (C⁻¹ • u) = |C⁻¹| * p u := by
            simpa [Real.norm_eq_abs] using (map_smul_eq_mul p C⁻¹ u)
        _ = C⁻¹ * p u := by rw [abs_of_pos hCinv_pos]
        _ ≤ C⁻¹ * C := mul_le_mul_of_nonneg_left hu_bound hCp_nonneg
        _ = 1 := by
            field_simp [hC_pos.ne']
    have hdual_ge :
        inner ℝ g (C⁻¹ • u) ≤ ‖g‖[p,*] := by
      -- The support-function definition of the dual norm bounds every point of the primal unit
      -- ball, including the normalized maximizing direction.
      have hbdd :
          BddAbove ((fun v : E ↦ inner ℝ g v) '' p.closedBall 0 1) := by
        obtain ⟨D, hD_pos, hDnorm⟩ := p.exists_norm_le_mul
        refine ⟨‖g‖ * D, ?_⟩
        rintro z ⟨v, hv, rfl⟩
        have hpv : p v ≤ 1 := by
          simpa [Seminorm.mem_closedBall_zero] using hv
        have hv_norm : ‖v‖ ≤ D := by
          calc
            ‖v‖ ≤ D * p v := hDnorm v
            _ ≤ D * 1 := by gcongr
            _ = D := by ring
        calc
          inner ℝ g v ≤ ‖g‖ * ‖v‖ := real_inner_le_norm _ _
          _ ≤ ‖g‖ * D := by gcongr
      rw [Seminorm.dualNorm]
      exact le_csSup hbdd ⟨C⁻¹ • u, hscaled_mem, rfl⟩
    have hunit_pairing : inner ℝ g u = ‖g‖ := by
      -- Pairing `g` with its normalized copy recovers the ambient norm.
      calc
        inner ℝ g u = inner ℝ g (‖g‖⁻¹ • g) := by rfl
        _ = ‖g‖⁻¹ * inner ℝ g g := by rw [real_inner_smul_right]
        _ = ‖g‖⁻¹ * ‖g‖ ^ (2 : ℕ) := by rw [real_inner_self_eq_norm_sq]
        _ = ‖g‖ := by
            rw [pow_two]
            field_simp [hg_norm_pos.ne']
    have hscaled_pairing :
        inner ℝ g (C⁻¹ • u) = C⁻¹ * ‖g‖ := by
      -- The additional `C⁻¹` scaling simply rescales the normalized pairing.
      simpa [hunit_pairing] using (real_inner_smul_right g u C⁻¹)
    have hscaled_le : C⁻¹ * ‖g‖ ≤ ‖g‖[p,*] := by
      simpa [hscaled_pairing] using hdual_ge
    have hmul := mul_le_mul_of_nonneg_left hscaled_le hC_pos.le
    -- Multiply back by the positive constant `C`.
    simpa [mul_assoc, hC_pos.ne', div_eq_mul_inv] using hmul

/-- Helper for Theorem 2.5: every separated seminorm on the ambient finite-dimensional Hilbert
space is continuous. -/
private lemma seminorm_continuous
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] :
    Continuous p := by
  obtain ⟨C, hC_pos, hC⟩ := seminorm_le_mul_norm p
  have hball : p.ball 0 1 ∈ nhds (0 : E) := by
    refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : E) (inv_pos.mpr hC_pos)) ?_
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hy
    rw [Seminorm.mem_ball_zero]
    calc
      p y ≤ C * ‖y‖ := hC y
      _ < C * C⁻¹ := mul_lt_mul_of_pos_left hy hC_pos
      _ = 1 := by rw [mul_inv_cancel₀ hC_pos.ne']
  exact Seminorm.continuous hball

/-- Helper for Theorem 2.5: the dual norm is attained on the closed primal unit ball. -/
private lemma dualNorm_attained_on_closedBall
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (g : E) :
    ∃ u ∈ p.closedBall 0 1,
      inner ℝ g u = ‖g‖[p,*] ∧
      IsMaxOn (fun v : E ↦ inner ℝ g v) (p.closedBall 0 1) u := by
  obtain ⟨D, hD_pos, hD⟩ := p.exists_norm_le_mul
  have hp_cont : Continuous p := seminorm_continuous p
  have hclosed : IsClosed (p.closedBall 0 1) := by
    rw [p.closedBall_zero_eq_preimage_closedBall]
    exact IsClosed.preimage hp_cont Metric.isClosed_closedBall
  have hsubset : p.closedBall 0 1 ⊆ Metric.closedBall (0 : E) D := by
    intro u hu
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hpu : p u ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hu
    calc
      ‖u‖ ≤ D * p u := hD u
      _ ≤ D * 1 := by
        gcongr
      _ = D := by ring
  have hcompact : IsCompact (p.closedBall 0 1) :=
    (isCompact_closedBall (0 : E) D).of_isClosed_subset hclosed hsubset
  have hnonempty : (p.closedBall 0 1).Nonempty := by
    exact ⟨0, by simpa [Seminorm.mem_closedBall_zero]⟩
  have hcont : ContinuousOn (fun v : E ↦ inner ℝ g v) (p.closedBall 0 1) := by
    simpa using (continuous_const.inner continuous_id).continuousOn
  obtain ⟨u, hu, huMax⟩ := hcompact.exists_isMaxOn hnonempty hcont
  have himage_bdd :
      BddAbove ((fun v : E ↦ inner ℝ g v) '' p.closedBall 0 1) :=
    (hcompact.image (continuous_const.inner continuous_id)).bddAbove
  have himage_nonempty :
      ((fun v : E ↦ inner ℝ g v) '' p.closedBall 0 1).Nonempty := by
    exact ⟨inner ℝ g 0, ⟨0, by simpa [Seminorm.mem_closedBall_zero], by simp⟩⟩
  have hsup_le :
      sSup ((fun v : E ↦ inner ℝ g v) '' p.closedBall 0 1) ≤ inner ℝ g u := by
    refine csSup_le himage_nonempty ?_
    rintro t ⟨v, hv, rfl⟩
    exact huMax hv
  have hu_le :
      inner ℝ g u ≤ sSup ((fun v : E ↦ inner ℝ g v) '' p.closedBall 0 1) := by
    exact le_csSup himage_bdd ⟨u, hu, rfl⟩
  refine ⟨u, hu, ?_, huMax⟩
  rw [Seminorm.dualNorm]
  exact le_antisymm hu_le hsup_le

/-- Helper for Theorem 2.5: the dual norm is nonnegative. -/
private lemma dualNorm_nonneg
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (g : E) :
    0 ≤ ‖g‖[p,*] := by
  obtain ⟨u, hu, hu_eq, huMax⟩ := dualNorm_attained_on_closedBall p g
  have hzero : (0 : E) ∈ p.closedBall 0 1 := by
    simpa [Seminorm.mem_closedBall_zero]
  have hmax0 : inner ℝ g 0 ≤ inner ℝ g u := huMax hzero
  simpa [hu_eq] using hmax0

/-- Helper for Theorem 2.5: the dual norm is invariant under negation. -/
private lemma dualNorm_neg_eq
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (g : E) :
    ‖-g‖[p,*] = ‖g‖[p,*] := by
  have hle : ‖-g‖[p,*] ≤ ‖g‖[p,*] := by
    obtain ⟨u, hu, hu_eq, _⟩ := dualNorm_attained_on_closedBall p (-g)
    have hneg_mem : -u ∈ p.closedBall 0 1 := by
      simpa [Seminorm.mem_closedBall_zero, map_neg_eq_map] using hu
    have hpu : p (-u) ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hneg_mem
    have hinner :
        inner ℝ (-g) u ≤ ‖g‖[p,*] := by
      calc
        inner ℝ (-g) u = inner ℝ g (-u) := by simp
        _ ≤ ‖g‖[p,*] * p (-u) := Seminorm.inner_le_dualNorm_mul p (-u) g
        _ ≤ ‖g‖[p,*] := by
              have hnonneg := dualNorm_nonneg p g
              nlinarith
    simpa [hu_eq] using hinner
  have hge : ‖g‖[p,*] ≤ ‖-g‖[p,*] := by
    obtain ⟨u, hu, hu_eq, _⟩ := dualNorm_attained_on_closedBall p g
    have hneg_mem : -u ∈ p.closedBall 0 1 := by
      simpa [Seminorm.mem_closedBall_zero, map_neg_eq_map] using hu
    have hpu : p (-u) ≤ 1 := by
      simpa [Seminorm.mem_closedBall_zero] using hneg_mem
    have hinner :
        inner ℝ g u ≤ ‖-g‖[p,*] := by
      calc
        inner ℝ g u = inner ℝ (-g) (-u) := by simp
        _ ≤ ‖-g‖[p,*] * p (-u) := Seminorm.inner_le_dualNorm_mul p (-u) (-g)
        _ ≤ ‖-g‖[p,*] := by
              have hnonneg := dualNorm_nonneg p (-g)
              nlinarith
    simpa [hu_eq] using hinner
  exact le_antisymm hle hge

/-- Helper for Theorem 2.5: the dual norm satisfies the triangle inequality. -/
private lemma dualNorm_add_le
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (g h : E) :
    ‖g + h‖[p,*] ≤ ‖g‖[p,*] + ‖h‖[p,*] := by
  obtain ⟨u, hu, hu_eq, _⟩ := dualNorm_attained_on_closedBall p (g + h)
  have hpu : p u ≤ 1 := by
    simpa [Seminorm.mem_closedBall_zero] using hu
  have hg_le : inner ℝ g u ≤ ‖g‖[p,*] := by
    calc
      inner ℝ g u ≤ ‖g‖[p,*] * p u := Seminorm.inner_le_dualNorm_mul p u g
      _ ≤ ‖g‖[p,*] := by
            have hnonneg := dualNorm_nonneg p g
            nlinarith
  have hh_le : inner ℝ h u ≤ ‖h‖[p,*] := by
    calc
      inner ℝ h u ≤ ‖h‖[p,*] * p u := Seminorm.inner_le_dualNorm_mul p u h
      _ ≤ ‖h‖[p,*] := by
            have hnonneg := dualNorm_nonneg p h
            nlinarith
  calc
    ‖g + h‖[p,*] = inner ℝ (g + h) u := hu_eq.symm
    _ = inner ℝ g u + inner ℝ h u := by rw [inner_add_left]
    _ ≤ ‖g‖[p,*] + ‖h‖[p,*] := add_le_add hg_le hh_le

/-- Helper for Theorem 2.5: the dual norm of a difference is controlled by the two intermediate
dual norms. -/
private lemma dualNorm_sub_le_add
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (x y z : E) :
    ‖x - y‖[p,*] ≤ ‖x - z‖[p,*] + ‖y - z‖[p,*] := by
  calc
    ‖x - y‖[p,*] = ‖(x - z) + (z - y)‖[p,*] := by congr 1; abel
    _ ≤ ‖x - z‖[p,*] + ‖z - y‖[p,*] := dualNorm_add_le p (x - z) (z - y)
    _ = ‖x - z‖[p,*] + ‖y - z‖[p,*] := by
          rw [show z - y = -(y - z) by abel, dualNorm_neg_eq p (y - z)]

/-- Helper for Theorem 2.5: a fixed-base affine-model remainder bound measured with the separated
seminorm `p` still forces the prescribed field value `g x` to be the ambient gradient of `f` at
`x`, after converting the seminorm control to the ambient norm on the finite-dimensional space. -/
private lemma hasGradientAt_of_pointwiseAffineModelSeminormSqBound
    {g : E → E} {x : E} {K : NNReal}
    (hquad :
      ∀ y : E,
        |f y - affineModelAt f g x y| ≤
          ((K : ℝ) / 2) * (p (y - x)) ^ (2 : ℕ)) :
    HasGradientAt f (g x) x := by
  obtain ⟨C, hC_pos, hC⟩ := seminorm_le_mul_norm p
  let K' : NNReal := ⟨(K : ℝ) * C ^ (2 : ℕ), by positivity⟩
  -- First convert the `p`-quadratic remainder estimate to the ambient norm used by Chapter 1.
  have hquadNorm :
      ∀ y : E,
        |f y - affineModelAt f g x y| ≤
          ((K' : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
    intro y
    have hp_le : p (y - x) ≤ C * ‖y - x‖ := hC (y - x)
    have hsq_le :
        (p (y - x)) ^ (2 : ℕ) ≤ C ^ (2 : ℕ) * ‖y - x‖ ^ (2 : ℕ) := by
      nlinarith [hp_le, apply_nonneg p (y - x), norm_nonneg (y - x)]
    have hcoef_nonneg : 0 ≤ (K : ℝ) / 2 := by
      positivity
    calc
      |f y - affineModelAt f g x y| ≤ ((K : ℝ) / 2) * (p (y - x)) ^ (2 : ℕ) := hquad y
      _ ≤ ((K : ℝ) / 2) * (C ^ (2 : ℕ) * ‖y - x‖ ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hsq_le hcoef_nonneg
      _ = ((K' : ℝ) / 2) * ‖y - x‖ ^ (2 : ℕ) := by
            have hK' : (K' : ℝ) = (K : ℝ) * C ^ (2 : ℕ) := rfl
            rw [hK']
            ring
  let r : E → ℝ := fun y ↦ f y - affineModelAt f g x y
  -- Record the fixed-base quadratic remainder as a local `O(‖y - x‖²)` bound near `x`.
  have hBigO : r =O[nhds x] fun y ↦ ‖y - x‖ ^ (2 : ℕ) := by
    refine Asymptotics.IsBigO.of_bound (((K' : NNReal) : ℝ) / 2) ?_
    filter_upwards with y
    simpa [r, Real.norm_eq_abs] using hquadNorm y
  -- A quadratic remainder has zero Fréchet derivative at the base point, hence little-`o`.
  have hLittle :
      (fun y ↦ f y - affineModelAt f g x y) =o[nhds x] fun y ↦ ‖y - x‖ := by
    have hDeriv0 : HasFDerivAt r (0 : E →L[ℝ] ℝ) x :=
      hBigO.hasFDerivAt (by norm_num : 1 < 2)
    simpa [r] using (hasFDerivAt_iff_isLittleO).mp hDeriv0
  -- The Chapter 1 affine-approximation criterion now identifies `g x` as the true gradient.
  simpa [affineModelAt] using
    (hasGradientAt_iff_sub_affineApproximation_isLittleO).mpr hLittle

/-- Helper for Theorem 2.5: every dual vector admits a primal displacement whose quadratic model
attains the source extremal-direction bound `-(2L)⁻¹ ‖g‖[p,*]²`. -/
private lemma extremal_direction_quadratic_model_bound
    (g : E) (hL : 0 < L) :
    ∃ d : E,
      inner ℝ g d + ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) ≤
        -(1 / (2 * (L : ℝ))) * (‖g‖[p,*]) ^ (2 : ℕ) := by
  obtain ⟨u, hu, hu_eq, _⟩ := dualNorm_attained_on_closedBall p g
  let a : ℝ := ‖g‖[p,*] / (L : ℝ)
  let d : E := -(a • u)
  refine ⟨d, ?_⟩
  have hLr : 0 < (L : ℝ) := by
    exact_mod_cast hL
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (dualNorm_nonneg p g) hLr.le
  have hpu : p u ≤ 1 := by
    simpa [Seminorm.mem_closedBall_zero] using hu
  have hpd_le : p d ≤ a := by
    calc
      p d = p (a • u) := by
        dsimp [d]
        simp [map_neg_eq_map]
      _ = |a| * p u := by
        simpa [Real.norm_eq_abs] using (map_smul_eq_mul p a u)
      _ = a * p u := by
        rw [abs_of_nonneg ha_nonneg]
      _ ≤ a * 1 := by
        gcongr
      _ = a := by ring
  have hinner_eq : inner ℝ g d = -a * ‖g‖[p,*] := by
    calc
      inner ℝ g d = inner ℝ g (-(a • u)) := by rfl
      _ = -(a * inner ℝ g u) := by
            rw [inner_neg_right, inner_smul_right]
      _ = -(a * ‖g‖[p,*]) := by rw [hu_eq]
      _ = -a * ‖g‖[p,*] := by ring
  have hsq_le : (p d) ^ (2 : ℕ) ≤ a ^ (2 : ℕ) := by
    nlinarith [hpd_le, apply_nonneg p d, ha_nonneg]
  have hquad_le :
      ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) ≤ ((L : ℝ) / 2) * a ^ (2 : ℕ) := by
    have hcoef_nonneg : 0 ≤ (L : ℝ) / 2 := by
      positivity
    exact mul_le_mul_of_nonneg_left hsq_le hcoef_nonneg
  calc
    inner ℝ g d + ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) ≤
        -a * ‖g‖[p,*] + ((L : ℝ) / 2) * a ^ (2 : ℕ) := by
          rw [hinner_eq]
          linarith
    _ = -(1 / (2 * (L : ℝ))) * (‖g‖[p,*]) ^ (2 : ℕ) := by
          dsimp [a]
          field_simp [hLr.ne']
          ring

/-- Helper for Theorem 2.5: the tangent-error bounds `(2.1.9)` imply the quadratic
gradient lower bound `(2.1.10)` by applying the upper tangent model to the translated objective
`z ↦ f z - ⟪∇f x, z⟫` and optimizing that quadratic model in a dual-norm extremal direction. -/
private lemma gradient_quadratic_lower_bound_of_tangent_error_bounds
    (h1 : smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f)
    (hL : 0 < L) :
    smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f := by
  intro x _ y _
  let φ : E → ℝ := fun z ↦ f z - inner ℝ (∇ f x) z
  let gy : E := ∇ f y - ∇ f x
  let a : ℝ := (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ)
  -- The translated objective has `x` as a minimizer because the lower tangent error is nonnegative.
  have hx_min : ∀ z : E, φ x ≤ φ z := by
    intro z
    have hnonneg : 0 ≤ f z - f x - inner ℝ (∇ f x) (z - x) :=
      h1.nonneg (by simp) (by simp)
    have hphi_nonneg : 0 ≤ φ z - φ x := by
      have hphi_eq : φ z - φ x = f z - f x - inner ℝ (∇ f x) (z - x) := by
        dsimp [φ]
        rw [inner_sub_right]
        ring_nf
      rw [hphi_eq]
      exact hnonneg
    linarith
  obtain ⟨d, hd⟩ :
      ∃ d : E,
        inner ℝ gy d + ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) ≤
          -(1 / (2 * (L : ℝ))) * (‖gy‖[p,*]) ^ (2 : ℕ) :=
    extremal_direction_quadratic_model_bound gy hL
  have hnorm :
      (‖gy‖[p,*]) ^ (2 : ℕ) = a := by
    dsimp [gy, a]
    rw [show ∇ f y - ∇ f x = -(∇ f x - ∇ f y) by abel, dualNorm_neg_eq p]
  have hd' :
      inner ℝ gy d + ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) ≤
        -(1 / (2 * (L : ℝ))) * a := by
    simpa [hnorm] using hd
  -- Apply the upper tangent model to the translated objective at `y` and the trial point `y + d`.
  have hup :
      φ (y + d) ≤ φ y + inner ℝ gy d + ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
    have hy' :
        f (y + d) - f y - inner ℝ (∇ f y) ((y + d) - y) ≤
          ((L : ℝ) / 2) * (p (y - (y + d))) ^ (2 : ℕ) :=
      h1.upperBound (by simp) (by simp)
    have hy'' :
        f (y + d) - f y - inner ℝ (∇ f y) d ≤
          ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
      have hpneg : p (y - (y + d)) = p d := by
        calc
          p (y - (y + d)) = p (-d) := by abel_nf
          _ = p d := by simpa using (map_neg_eq_map p d)
      simpa [hpneg] using hy'
    have hphi_upper :
        φ (y + d) - φ y - inner ℝ gy d ≤
          ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
      have hphi_eq :
          φ (y + d) - φ y - inner ℝ gy d =
            f (y + d) - f y - inner ℝ (∇ f y) d := by
        calc
          φ (y + d) - φ y - inner ℝ gy d =
              f (y + d) - inner ℝ (∇ f x) (y + d) -
                (f y - inner ℝ (∇ f x) y) - inner ℝ gy d := by
                  rfl
          _ = f (y + d) - inner ℝ (∇ f x) y - inner ℝ (∇ f x) d -
                (f y - inner ℝ (∇ f x) y) - inner ℝ gy d := by
                  rw [inner_add_right]
                  ring
          _ = f (y + d) - f y - inner ℝ (∇ f x) d - inner ℝ gy d := by
                ring
          _ = f (y + d) - f y - inner ℝ (∇ f y) d := by
                dsimp [gy]
                rw [inner_sub_left]
                ring
      rw [hphi_eq]
      exact hy''
    linarith
  -- Comparing the minimizing point `x` with the extremal trial point yields `(2.1.10)`.
  have hphi :
      φ x ≤ φ y - (1 / (2 * (L : ℝ))) * a := by
    calc
      φ x ≤ φ (y + d) := hx_min (y + d)
      _ ≤ φ y + inner ℝ gy d + ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := hup
      _ ≤ φ y - (1 / (2 * (L : ℝ))) * a := by linarith [hd']
  have hfinal :
      f x + inner ℝ (∇ f x) (y - x) + (1 / (2 * (L : ℝ))) * a ≤
        f y := by
    have hphi' :
        f x - inner ℝ (∇ f x) x + (1 / (2 * (L : ℝ))) * a ≤
          f y - inner ℝ (∇ f x) y := by
      dsimp [φ] at hphi
      linarith
    have hrewrite :
        f x + inner ℝ (∇ f x) (y - x) + (1 / (2 * (L : ℝ))) * a =
          f x - inner ℝ (∇ f x) x + (1 / (2 * (L : ℝ))) * a +
            inner ℝ (∇ f x) y := by
      rw [inner_sub_right]
      ring
    rw [hrewrite]
    linarith
  simpa [a] using hfinal

/-- Helper for Theorem 2.5: the quadratic lower bound `(2.1.10)` implies cocoercivity
`(2.1.11)` after adding the inequalities with the two endpoints interchanged. -/
private lemma cocoerciveGradient_of_gradient_quadratic_lower_bound
    (h2 : smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f)
    (hL : 0 < L) :
    smoothConvexCocoerciveGradientOn p L (∇ f) Set.univ := by
  intro x _ y _
  -- Add the two endpoint-swapped copies of `(2.1.10)` after normalizing the dual norm.
  have hxy :
      f x + inner ℝ (∇ f x) (y - x) +
          (1 / (2 * (L : ℝ))) * (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ) ≤
        f y :=
    h2 (by simp) (by simp)
  have hyx :
      f y + inner ℝ (∇ f y) (x - y) +
          (1 / (2 * (L : ℝ))) * (‖∇ f y - ∇ f x‖[p,*]) ^ (2 : ℕ) ≤
        f x :=
    h2 (by simp) (by simp)
  let a : ℝ := (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ)
  have hnorm :
      (‖∇ f y - ∇ f x‖[p,*]) ^ (2 : ℕ) = (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ) := by
    rw [show ∇ f y - ∇ f x = -(∇ f x - ∇ f y) by abel, dualNorm_neg_eq p]
  have hxy' :
      f x + inner ℝ (∇ f x) (y - x) + (1 / (2 * (L : ℝ))) * a ≤ f y := by
    simpa [a] using hxy
  have hyx' :
      f y + inner ℝ (∇ f y) (x - y) +
          (1 / (2 * (L : ℝ))) * a ≤
        f x := by
    rw [hnorm] at hyx
    simpa [a] using hyx
  -- The linear terms collapse to the monotonicity pairing of the gradient difference.
  have hlin :
      inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y) =
        -inner ℝ (∇ f x - ∇ f y) (x - y) := by
    calc
      inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y)
          = -inner ℝ (∇ f x) (x - y) + inner ℝ (∇ f y) (x - y) := by
              rw [show y - x = -(x - y) by abel, inner_neg_right]
      _ = -inner ℝ (∇ f x - ∇ f y) (x - y) := by
            rw [inner_sub_left]
            ring
  have hLr : 0 < (L : ℝ) := by
    exact_mod_cast hL
  have hlinear :
      inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y) +
          (1 / (L : ℝ)) * a ≤ 0 := by
    have hsum := add_le_add hxy' hyx'
    ring_nf at hsum ⊢
    linarith
  rw [hlin] at hlinear
  simpa [a] using (show (1 / (L : ℝ)) * a ≤ inner ℝ (∇ f x - ∇ f y) (x - y) by
    nlinarith [hlinear, hLr])

/-- Helper for Theorem 2.5: cocoercivity `(2.1.11)` yields the monotonicity and upper pairing
bound `(2.1.12)` after combining it with dual Cauchy. -/
private lemma monotoneGradientBounds_of_cocoerciveGradient
    (h3 : smoothConvexCocoerciveGradientOn p L (∇ f) Set.univ)
    (hL : 0 < L) :
    smoothConvexMonotoneGradientBoundsOn p L (∇ f) Set.univ := by
  refine ⟨?_, ?_⟩
  · intro x _ y _
    -- Cocoercivity already places a nonnegative quantity below the gradient pairing.
    have hxy :
        (1 / (L : ℝ)) * (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ) ≤
          inner ℝ (∇ f x - ∇ f y) (x - y) :=
      h3 (by simp) (by simp)
    have hnonneg :
        0 ≤ (1 / (L : ℝ)) * (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ) := by
      positivity
    exact le_trans hnonneg hxy
  · intro x _ y _
    -- Dual Cauchy turns cocoercivity into the Lipschitz-style upper pairing bound.
    have hxy :
        (1 / (L : ℝ)) * (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ) ≤
          inner ℝ (∇ f x - ∇ f y) (x - y) :=
      h3 (by simp) (by simp)
    have hinner :
        inner ℝ (∇ f x - ∇ f y) (x - y) ≤
          ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
      Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
    have hp_nonneg : 0 ≤ p (x - y) := apply_nonneg p (x - y)
    have hbound : ‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y) := by
      by_cases hgrad0 : ‖∇ f x - ∇ f y‖[p,*] = 0
      · have hLr_nonneg : 0 ≤ (L : ℝ) := by
          exact_mod_cast hL.le
        simpa [hgrad0] using mul_nonneg hLr_nonneg hp_nonneg
      · have hdual_nonneg : 0 ≤ ‖∇ f x - ∇ f y‖[p,*] :=
          dualNorm_nonneg p (∇ f x - ∇ f y)
        have hdual_pos : 0 < ‖∇ f x - ∇ f y‖[p,*] :=
          lt_of_le_of_ne hdual_nonneg (Ne.symm hgrad0)
        let a : ℝ := ‖∇ f x - ∇ f y‖[p,*]
        let s : ℝ := p (x - y)
        have hchain :
            (1 / (L : ℝ)) * a ^ (2 : ℕ) ≤ a * s := by
          simpa [a, s] using le_trans hxy hinner
        have hLr : 0 < (L : ℝ) := by
          exact_mod_cast hL
        have hchain' : a * a ≤ a * ((L : ℝ) * s) := by
          have hscaled := mul_le_mul_of_nonneg_left hchain hLr.le
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, hLr.ne'] using hscaled
        have hbound' : a ≤ (L : ℝ) * s := by
          refine le_of_mul_le_mul_left ?_ hdual_pos
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hchain'
        simpa [a, s] using hbound'
    calc
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
          ‖∇ f x - ∇ f y‖[p,*] * p (x - y) := hinner
      _ ≤ ((L : ℝ) * p (x - y)) * p (x - y) := by
            exact mul_le_mul_of_nonneg_right hbound hp_nonneg
      _ = (L : ℝ) * (p (x - y)) ^ (2 : ℕ) := by
            ring

/-- Helper for Theorem 2.5: the tangent-error bounds `(2.1.9)` imply the convex-combination
quadratic gap estimate `(2.1.14)` by applying those tangent inequalities at the midpoint
`αx + (1 - α)y` to both endpoints and adding them with weights `α` and `1 - α`. -/
private lemma convexCombinationQuadraticBound_of_tangent_error_bounds
    (h1 : smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f) :
    smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f := by
  intro x _ y _ α hα
  let z : E := α • x + (1 - α) • y
  have hx_bound :
      0 ≤ f x - f z - inner ℝ (∇ f z) (x - z) ∧
        f x - f z - inner ℝ (∇ f z) (x - z) ≤
          ((L : ℝ) / 2) * (p (z - x)) ^ (2 : ℕ) :=
    h1 (by simp) (by simp)
  have hy_bound :
      0 ≤ f y - f z - inner ℝ (∇ f z) (y - z) ∧
        f y - f z - inner ℝ (∇ f z) (y - z) ≤
          ((L : ℝ) / 2) * (p (z - y)) ^ (2 : ℕ) :=
    h1 (by simp) (by simp)
  have hz_line : z = AffineMap.lineMap y x α := by
    simp [z, AffineMap.lineMap_apply_module, add_comm]
  have hz_sub_x : z - x = (1 - α) • (y - x) := by
    simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_right y x α
  have hz_sub_y : z - y = α • (x - y) := by
    simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_left y x α
  have hp_sub : p (y - x) = p (x - y) := by
    simpa [neg_sub] using (map_neg_eq_map p (x - y))
  have hx_disp : x - z = (1 - α) • (x - y) := by
    calc
      x - z = -((z - x)) := by abel
      _ = -((1 - α) • (y - x)) := by rw [hz_sub_x]
      _ = (1 - α) • (x - y) := by simp [smul_neg, sub_eq_add_neg]
  have hy_disp : y - z = α • (y - x) := by
    calc
      y - z = -(z - y) := by abel
      _ = -(α • (x - y)) := by rw [hz_sub_y]
      _ = α • (y - x) := by simp [smul_neg, sub_eq_add_neg]
  have hcancel_vec : α • (x - z) + (1 - α) • (y - z) = 0 := by
    rw [hx_disp, hy_disp]
    rw [show y - x = -(x - y) by abel]
    rw [smul_smul, smul_smul, smul_neg]
    calc
      (α * (1 - α)) • (x - y) + -(((1 - α) * α) • (x - y)) =
          ((α * (1 - α)) - ((1 - α) * α)) • (x - y) := by
            rw [← sub_eq_add_neg, sub_smul]
      _ = 0 := by
            have hcoeff : α * (1 - α) - ((1 - α) * α) = 0 := by ring
            simp [hcoeff]
  have hcancel :
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) = 0 := by
    calc
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) =
          inner ℝ (∇ f z) (α • (x - z) + (1 - α) • (y - z)) := by
            rw [inner_add_right, inner_smul_right, inner_smul_right]
      _ = 0 := by simp [hcancel_vec]
  have hgap_eq :
      α * f x + (1 - α) * f y - f z =
        α * (f x - f z - inner ℝ (∇ f z) (x - z)) +
          (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := by
    linarith
  have hx_scaled :
      α * (f x - f z - inner ℝ (∇ f z) (x - z)) ≤
        α * (((L : ℝ) / 2) * (p (z - x)) ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hx_bound.2 hα.1
  have hy_scaled :
      (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) ≤
        (1 - α) * (((L : ℝ) / 2) * (p (z - y)) ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hy_bound.2 (sub_nonneg.mpr hα.2)
  have hupper :
      α * f x + (1 - α) * f y - f z ≤
        α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by
    have hsum := add_le_add hx_scaled hy_scaled
    calc
      α * f x + (1 - α) * f y - f z
          = α * (f x - f z - inner ℝ (∇ f z) (x - z)) +
              (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := hgap_eq
      _ ≤ α * (((L : ℝ) / 2) * (p (z - x)) ^ (2 : ℕ)) +
            (1 - α) * (((L : ℝ) / 2) * (p (z - y)) ^ (2 : ℕ)) := hsum
      _ = α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by
            rw [hz_sub_x, hz_sub_y]
            simp [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hα.1,
              hp_sub, abs_of_nonneg (sub_nonneg.mpr hα.2)]
            ring
  have hx_nonneg :
      0 ≤ α * (f x - f z - inner ℝ (∇ f z) (x - z)) := by
    exact mul_nonneg hα.1 hx_bound.1
  have hy_nonneg :
      0 ≤ (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := by
    exact mul_nonneg (sub_nonneg.mpr hα.2) hy_bound.1
  have hnonneg :
      0 ≤ α * f x + (1 - α) * f y - f z := by
    rw [hgap_eq]
    exact add_nonneg hx_nonneg hy_nonneg
  exact ⟨hnonneg, by simpa [z] using hupper⟩

/-- Helper for Theorem 2.5: the quadratic lower bound `(2.1.10)` implies the convex-combination
gradient bound `(2.1.13)` by applying `(2.1.10)` at the convex-combination point
`αx + (1 - α)y` toward each endpoint and combining the results. -/
private lemma convexCombinationGradientBound_of_gradient_quadratic_lower_bound
    (h2 : smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f)
    (hL : 0 < L) :
    smoothConvexConvexCombinationGradientBoundOn p L (∇ f) Set.univ f := by
  intro x _ y _ α hα
  let z : E := α • x + (1 - α) • y
  have hx_bound :
      f z + inner ℝ (∇ f z) (x - z) +
          (1 / (2 * (L : ℝ))) * (‖∇ f z - ∇ f x‖[p,*]) ^ (2 : ℕ) ≤
        f x :=
    h2 (by simp) (by simp)
  have hy_bound :
      f z + inner ℝ (∇ f z) (y - z) +
          (1 / (2 * (L : ℝ))) * (‖∇ f z - ∇ f y‖[p,*]) ^ (2 : ℕ) ≤
        f y :=
    h2 (by simp) (by simp)
  have hz_line : z = AffineMap.lineMap y x α := by
    simp [z, AffineMap.lineMap_apply_module, add_comm]
  have hx_disp : x - z = (1 - α) • (x - y) := by
    calc
      x - z = -((z - x)) := by abel
      _ = -((1 - α) • (y - x)) := by
            rw [show z - x = (1 - α) • (y - x) by
              simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_right y x α]
      _ = (1 - α) • (x - y) := by
            simp [smul_neg, sub_eq_add_neg]
  have hy_disp : y - z = α • (y - x) := by
    calc
      y - z = -(z - y) := by abel
      _ = -(α • (x - y)) := by
            rw [show z - y = α • (x - y) by
              simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_left y x α]
      _ = α • (y - x) := by
            simp [smul_neg, sub_eq_add_neg]
  -- The two tangent directions from `z` to the endpoints cancel after weighting.
  have hcancel_vec : α • (x - z) + (1 - α) • (y - z) = 0 := by
    rw [hx_disp, hy_disp]
    rw [show y - x = -(x - y) by abel]
    rw [smul_smul, smul_smul, smul_neg]
    calc
      (α * (1 - α)) • (x - y) + -(((1 - α) * α) • (x - y)) =
          ((α * (1 - α)) - ((1 - α) * α)) • (x - y) := by
            rw [← sub_eq_add_neg, sub_smul]
      _ = 0 := by
            have hcoeff : α * (1 - α) - ((1 - α) * α) = 0 := by
              ring
            simp [hcoeff]
  have hcancel :
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) = 0 := by
    calc
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) =
          inner ℝ (∇ f z) (α • (x - z) + (1 - α) • (y - z)) := by
            rw [inner_add_right, inner_smul_right, inner_smul_right]
      _ = 0 := by
            simp [hcancel_vec]
  -- After weighting the two `(2.1.10)` inequalities, only the dual-norm squares remain.
  have hx_scaled :
      α *
          (f z + inner ℝ (∇ f z) (x - z) +
            (1 / (2 * (L : ℝ))) * (‖∇ f z - ∇ f x‖[p,*]) ^ (2 : ℕ)) ≤
        α * f x := by
    exact mul_le_mul_of_nonneg_left hx_bound hα.1
  have hy_scaled :
      (1 - α) *
          (f z + inner ℝ (∇ f z) (y - z) +
            (1 / (2 * (L : ℝ))) * (‖∇ f z - ∇ f y‖[p,*]) ^ (2 : ℕ)) ≤
        (1 - α) * f y := by
    exact mul_le_mul_of_nonneg_left hy_bound (sub_nonneg.mpr hα.2)
  have hmain :
      f z +
          (1 / (2 * (L : ℝ))) *
            (α * (‖∇ f z - ∇ f x‖[p,*]) ^ (2 : ℕ) +
              (1 - α) * (‖∇ f z - ∇ f y‖[p,*]) ^ (2 : ℕ)) ≤
        α * f x + (1 - α) * f y := by
    have hsum := add_le_add hx_scaled hy_scaled
    nlinarith [hsum, hcancel]
  -- The endpoint gradient gap is controlled by the two intermediate gaps through `z`.
  let a : ℝ := ‖∇ f z - ∇ f x‖[p,*]
  let b : ℝ := ‖∇ f z - ∇ f y‖[p,*]
  let c : ℝ := ‖∇ f x - ∇ f y‖[p,*]
  have htriangle : c ≤ a + b := by
    have htriangle' := dualNorm_sub_le_add p (∇ f x) (∇ f y) (∇ f z)
    have hzx : ‖∇ f x - ∇ f z‖[p,*] = a := by
      dsimp [a]
      rw [show ∇ f x - ∇ f z = -(∇ f z - ∇ f x) by abel, dualNorm_neg_eq p]
    have hzy : ‖∇ f y - ∇ f z‖[p,*] = b := by
      dsimp [b]
      rw [show ∇ f y - ∇ f z = -(∇ f z - ∇ f y) by abel, dualNorm_neg_eq p]
    have htriangle'' : c ≤ ‖∇ f x - ∇ f z‖[p,*] + ‖∇ f y - ∇ f z‖[p,*] := by
      simpa [c] using htriangle'
    rw [hzx, hzy] at htriangle''
    exact htriangle''
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact dualNorm_nonneg p (∇ f z - ∇ f x)
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    exact dualNorm_nonneg p (∇ f z - ∇ f y)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact dualNorm_nonneg p (∇ f x - ∇ f y)
  have hsum_nonneg : 0 ≤ a + b := add_nonneg ha_nonneg hb_nonneg
  have hc_sq : c ^ (2 : ℕ) ≤ (a + b) ^ (2 : ℕ) := by
    nlinarith [htriangle, hc_nonneg, hsum_nonneg]
  have hsq_aux :
      α * (1 - α) * (a + b) ^ (2 : ℕ) ≤ α * a ^ (2 : ℕ) + (1 - α) * b ^ (2 : ℕ) := by
    have hsquare : 0 ≤ (α * a - (1 - α) * b) ^ (2 : ℕ) := sq_nonneg _
    nlinarith [hsquare, hα.1, hα.2]
  have hsq :
      α * (1 - α) * c ^ (2 : ℕ) ≤ α * a ^ (2 : ℕ) + (1 - α) * b ^ (2 : ℕ) := by
    have hleft :
        α * (1 - α) * c ^ (2 : ℕ) ≤ α * (1 - α) * (a + b) ^ (2 : ℕ) := by
      have hα_nonneg : 0 ≤ α * (1 - α) := by
        nlinarith [hα.1, hα.2]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hc_sq hα_nonneg
    exact le_trans hleft hsq_aux
  have hcoef_nonneg : 0 ≤ 1 / (2 * (L : ℝ)) := by
    positivity
  have hsq_scaled :
      (1 / (2 * (L : ℝ))) * (α * (1 - α) * c ^ (2 : ℕ)) ≤
        (1 / (2 * (L : ℝ))) * (α * a ^ (2 : ℕ) + (1 - α) * b ^ (2 : ℕ)) :=
    mul_le_mul_of_nonneg_left hsq hcoef_nonneg
  have htail :
      f z + (α * (1 - α) / (2 * (L : ℝ))) * (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ) ≤
        f z +
          (1 / (2 * (L : ℝ))) *
            (α * (‖∇ f z - ∇ f x‖[p,*]) ^ (2 : ℕ) +
              (1 - α) * (‖∇ f z - ∇ f y‖[p,*]) ^ (2 : ℕ)) := by
    dsimp [a, b, c] at hsq_scaled
    have htail' := add_le_add_left hsq_scaled (f z)
    simpa [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using htail'
  exact le_trans htail hmain

/-- Helper for Theorem 2.5: the tangent-error bounds `(2.1.9)` reconstruct the owner
membership `f ∈ 𝓕[L,p]¹¹` by recovering `HasGradientAt` from a global quadratic affine-model
bound, deriving convexity from the lower tangent planes, and extracting the dual-norm Lipschitz
estimate from the cocoercivity inequality. -/
private lemma mem_F11_of_tangent_error_bounds
    (h1 : smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f)
    (hL : 0 < L) :
    f ∈ 𝓕[L, p]¹¹ := by
  -- Reconstruct the ambient gradient pointwise from the quadratic affine-model remainder bound.
  have hgrad : ∀ x : E, HasGradientAt f (∇ f x) x := by
    intro x
    refine hasGradientAt_of_pointwiseAffineModelSeminormSqBound (p := p) (f := f) (K := L) ?_
    intro y
    have hxy := h1 (x := x) (by simp) (y := y) (by simp)
    have hp_sym : p (x - y) = p (y - x) := by
      simpa [neg_sub] using (map_neg_eq_map p (y - x))
    have hupper :
        f y - f x - inner ℝ (∇ f x) (y - x) ≤
          ((L : ℝ) / 2) * (p (y - x)) ^ (2 : ℕ) := by
      simpa [hp_sym] using hxy.2
    -- The tangent error is already nonnegative, so its absolute value is itself.
    calc
      |f y - affineModelAt f (∇ f) x y|
          = |f y - f x - inner ℝ (∇ f x) (y - x)| := by
              rw [affineModelAt_apply]
              ring_nf
      _ = f y - f x - inner ℝ (∇ f x) (y - x) := by
            rw [abs_of_nonneg hxy.1]
      _ ≤ ((L : ℝ) / 2) * (p (y - x)) ^ (2 : ℕ) := hupper
  have h2 := gradient_quadratic_lower_bound_of_tangent_error_bounds h1 hL
  have h3 := cocoerciveGradient_of_gradient_quadratic_lower_bound h2 hL
  have hLip :
      ∀ x y : E, ‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y) := by
    intro x y
    -- The same dual-Cauchy argument used in `(2.1.11) → (2.1.12)` recovers the dual-norm
    -- Lipschitz estimate from cocoercivity.
    have hxy :
        (1 / (L : ℝ)) * (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ) ≤
          inner ℝ (∇ f x - ∇ f y) (x - y) :=
      h3 (by simp) (by simp)
    have hinner :
        inner ℝ (∇ f x - ∇ f y) (x - y) ≤
          ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
      Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
    have hp_nonneg : 0 ≤ p (x - y) := apply_nonneg p (x - y)
    by_cases hgrad0 : ‖∇ f x - ∇ f y‖[p,*] = 0
    · have hLr_nonneg : 0 ≤ (L : ℝ) := by
        exact_mod_cast hL.le
      simpa [hgrad0] using mul_nonneg hLr_nonneg hp_nonneg
    · have hdual_nonneg : 0 ≤ ‖∇ f x - ∇ f y‖[p,*] :=
        dualNorm_nonneg p (∇ f x - ∇ f y)
      have hdual_pos : 0 < ‖∇ f x - ∇ f y‖[p,*] :=
        lt_of_le_of_ne hdual_nonneg (Ne.symm hgrad0)
      let a : ℝ := ‖∇ f x - ∇ f y‖[p,*]
      let s : ℝ := p (x - y)
      have hchain :
          (1 / (L : ℝ)) * a ^ (2 : ℕ) ≤ a * s := by
        simpa [a, s] using le_trans hxy hinner
      have hLr : 0 < (L : ℝ) := by
        exact_mod_cast hL
      have hchain' : a * a ≤ a * ((L : ℝ) * s) := by
        have hscaled := mul_le_mul_of_nonneg_left hchain hLr.le
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm, hLr.ne'] using hscaled
      have hbound' : a ≤ (L : ℝ) * s := by
        refine le_of_mul_le_mul_left ?_ hdual_pos
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hchain'
      simpa [a, s] using hbound'
  obtain ⟨C, hC_pos, hC⟩ := seminorm_le_mul_norm p
  have hnorm_le_dual :
      ∀ g : E, ‖g‖ ≤ C * ‖g‖[p,*] :=
    norm_le_mul_dualNorm_of_seminorm_le_mul_norm (p := p) hC_pos hC
  let K : NNReal := ⟨(L : ℝ) * C ^ (2 : ℕ), by positivity⟩
  have hLipNorm : LipschitzWith K (∇ f) := by
    rw [lipschitzWith_iff_norm_sub_le]
    intro x y
    -- Convert the dual-norm Lipschitz estimate to the ambient norm using the primal/dual
    -- comparison constants coming from finite dimensionality.
    calc
      ‖∇ f x - ∇ f y‖ ≤ C * ‖∇ f x - ∇ f y‖[p,*] := hnorm_le_dual (∇ f x - ∇ f y)
      _ ≤ C * ((L : ℝ) * p (x - y)) := by
            exact mul_le_mul_of_nonneg_left (hLip x y) hC_pos.le
      _ ≤ C * ((L : ℝ) * (C * ‖x - y‖)) := by
            gcongr
            exact hC (x - y)
      _ = (K : ℝ) * ‖x - y‖ := by
            rw [show (K : ℝ) = (L : ℝ) * C ^ (2 : ℕ) by rfl]
            ring
  have hcontDiff : ContDiff ℝ 1 f := by
    -- A globally Lipschitz gradient field is continuous, so the pointwise gradient witnesses
    -- package into a `C¹` owner.
    rw [contDiff_one_iff_hasFDerivAt]
    refine ⟨fun x ↦ (InnerProductSpace.toDual ℝ E) (∇ f x), ?_, ?_⟩
    · exact (LinearIsometryEquiv.continuous (InnerProductSpace.toDual ℝ E)).comp
        hLipNorm.continuous
    · intro x
      simpa using (hgrad x).hasFDerivAt
  have hdiff : DifferentiableOn ℝ f Set.univ := by
    intro x hx
    exact (hgrad x).differentiableAt.differentiableWithinAt
  have hmonoField := monotoneGradientBounds_of_cocoerciveGradient h3 hL
  have hconv : ConvexOn ℝ Set.univ f := by
    have hmono : GradientMonotoneOn Set.univ f := by
      intro x y hx hy
      -- On the whole space, the within-gradient monotonicity is the ambient monotonicity from
      -- `(2.1.12)`.
      simpa [gradientWithin, gradient, fderivWithin_univ] using
        (hmonoField.monotone (x := x) (by simp) (y := y) (by simp))
    exact (convexOn_iff_gradient_monotone convex_univ hdiff).mpr hmono
  refine ⟨⟨contDiffOn_univ.mpr hcontDiff, hconv⟩, ?_, ?_⟩
  · intro x hx
    simpa using hgrad x
  · intro x hx y hy
    exact hLip x y

/-- Helper for Theorem 2.5: the convex-combination gradient bound `(2.1.13)` already implies the
ordinary Jensen inequality, hence convexity of `f` on the whole space. -/
private lemma convexOn_univ_of_convexCombinationGradientBound
    (h6 : smoothConvexConvexCombinationGradientBoundOn p L (∇ f) Set.univ f) :
    ConvexOn ℝ Set.univ f := by
  -- Drop the nonnegative quadratic correction and keep only the Jensen inequality.
  refine (convexOn_iff_segment_inequality convex_univ).2 ?_
  intro x hx y hy α hα
  have hxy := h6 hx hy hα
  have hquad_nonneg :
      0 ≤ (α * (1 - α) / (2 * (L : ℝ))) * (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ) := by
    by_cases hL0 : (L : ℝ) = 0
    · simp [hL0]
    · have hL_nonneg : 0 ≤ (L : ℝ) := by
        exact_mod_cast (show 0 ≤ L by exact L.2)
      have hL_pos : 0 < (L : ℝ) := lt_of_le_of_ne hL_nonneg (fun h ↦ hL0 h.symm)
      have hα_nonneg : 0 ≤ α * (1 - α) := by
        nlinarith [hα.1, hα.2]
      positivity
  linarith

/-- Helper for Theorem 2.5: the convex-combination quadratic bound `(2.1.14)` is exactly the
Jensen inequality together with a quadratic upper control, so in particular it implies convexity
of `f` on the whole space. -/
private lemma convexOn_univ_of_convexCombinationQuadraticBound
    (h7 : smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f) :
    ConvexOn ℝ Set.univ f := by
  -- The nonnegative Jensen gap is precisely the segment form of convexity.
  refine (convexOn_iff_segment_inequality convex_univ).2 ?_
  intro x hx y hy α hα
  have hxy := h7.nonneg hx hy hα
  linarith

/-- Helper for Theorem 2.5: the witness-bundled monotone-gradient clause `(2.1.12)` recovers the
upper tangent-error estimate by integrating the corrected segment remainder derivative. -/
-- TODO: prove this by integrating the derivative of the corrected segment remainder along
-- `x + t • (y - x)` and using the scalar line estimate from
-- `segment_pairing_bounds_of_monotoneGradientBounds`.
private lemma tangent_error_upperBound_of_monotoneGradientBounds
    (h5 : smoothConvexMonotoneGradientBoundsWithGradientOn p L Set.univ f)
    {x y : E} :
    f y - f x - inner ℝ (∇ f x) (y - x) ≤
      ((L : ℝ) / 2) * (p (x - y)) ^ 2 := by
  let d : E := y - x
  let R : ℝ → ℝ := fun t ↦ f (x + t • d) - f x - t * inner ℝ (∇ f x) d
  let hgrad : ∀ z : E, HasGradientAt f (∇ f z) z := fun z ↦ h5.hasGradientAt (x := z) (by simp)
  have hf_cont : Continuous f := by
    -- The global gradient witnesses make `f` continuous at every ambient point.
    refine continuous_iff_continuousAt.2 ?_
    intro z
    exact (hgrad z).continuousAt
  have hR_cont : ContinuousOn R (Set.Icc (0 : ℝ) 1) := by
    -- The corrected remainder is a continuous scalar slice of `f`.
    have hslice_cont : Continuous fun t : ℝ ↦ f (x + t • d) := hf_cont.comp (by fun_prop)
    have hlin_cont : Continuous fun t : ℝ ↦ t * inner ℝ (∇ f x) d := by
      fun_prop
    exact ((hslice_cont.continuousOn.sub continuousOn_const).sub hlin_cont.continuousOn)
  have hR_diff : DifferentiableOn ℝ R (Set.Ioo (0 : ℝ) 1) := by
    -- On the open segment, differentiate via the ambient gradient witness.
    intro t ht
    have hseg_deriv :=
      segment_corrected_remainder_hasDerivAt_univ_of_hasGradientAt
        (f := f) hgrad (x := x) (y := y) (t := t) ht
    exact hseg_deriv.differentiableAt.differentiableWithinAt
  have hR_bound :
      ‖R 1 - R 0‖ ≤ ∫ t in (0 : ℝ)..1, (L : ℝ) * t * (p d) ^ (2 : ℕ) := by
    -- The derivative is nonnegative and bounded above by the scalarized monotonicity estimate.
    refine norm_sub_le_integral_of_norm_deriv_le_of_le (by norm_num) hR_cont hR_diff ?_ ?_
    · exact Filter.Eventually.of_forall fun t ht ↦ by
        have hderiv :=
          segment_corrected_remainder_hasDerivAt_univ_of_hasGradientAt hgrad
            (x := x) (y := y) (t := t) ht
        rw [hderiv.deriv]
        have hmono :
            0 ≤ inner ℝ (∇ f (x + t • d) - ∇ f x) ((x + t • d) - x) :=
          h5.monotone (x := x + t • d) (by simp) (y := x) (by simp)
        have hupper :
            inner ℝ (∇ f (x + t • d) - ∇ f x) ((x + t • d) - x) ≤
              (L : ℝ) * (p ((x + t • d) - x)) ^ (2 : ℕ) :=
          h5.upperBound (x := x + t • d) (by simp) (y := x) (by simp)
        have hmono' :
            0 ≤ t * inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
          simpa [d, inner_smul_right] using hmono
        have hpair_nonneg :
            0 ≤ inner ℝ (∇ f (x + t • d) - ∇ f x) d := by
          nlinarith [hmono', ht.1]
        have hpseg :
            p ((x + t • d) - x) = t * p d := by
          calc
            p ((x + t • d) - x) = p (t • d) := by simp
            _ = |t| * p d := by
                  simpa [Real.norm_eq_abs] using (map_smul_eq_mul p t d)
            _ = t * p d := by rw [abs_of_pos ht.1]
        have hupper' :
            t * inner ℝ (∇ f (x + t • d) - ∇ f x) d ≤
              t * ((L : ℝ) * t * (p d) ^ (2 : ℕ)) := by
          calc
            t * inner ℝ (∇ f (x + t • d) - ∇ f x) d
                ≤ (L : ℝ) * (p ((x + t • d) - x)) ^ (2 : ℕ) := by
                    simpa [d, inner_smul_right] using hupper
            _ = (L : ℝ) * (t * p d) ^ (2 : ℕ) := by rw [hpseg]
            _ = t * ((L : ℝ) * t * (p d) ^ (2 : ℕ)) := by ring
        have hpair_upper :
            inner ℝ (∇ f (x + t • d) - ∇ f x) d ≤
              (L : ℝ) * t * (p d) ^ (2 : ℕ) := by
          nlinarith [hupper', ht.1]
        rw [Real.norm_eq_abs, abs_of_nonneg hpair_nonneg]
        exact hpair_upper
    · have hint : IntervalIntegrable (fun t : ℝ ↦ t) MeasureTheory.volume 0 1 :=
        Continuous.intervalIntegrable continuous_id 0 1
      simpa [mul_assoc] using hint.const_mul ((L : ℝ) * (p d) ^ (2 : ℕ))
  have hR0 : R 0 = 0 := by
    simp [R, d]
  have hR1 : R 1 = f y - f x - inner ℝ (∇ f x) (y - x) := by
    simp [R, d]
  have habs :
      |f y - f x - inner ℝ (∇ f x) (y - x)| ≤
        ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
    -- Integrating the scalar derivative bound gives the quadratic remainder estimate.
    rw [hR1, hR0, sub_zero, Real.norm_eq_abs] at hR_bound
    calc
      |f y - f x - inner ℝ (∇ f x) (y - x)| ≤
          ∫ t in (0 : ℝ)..1, (L : ℝ) * t * (p d) ^ (2 : ℕ) := hR_bound
      _ = ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
            calc
              ∫ t in (0 : ℝ)..1, (L : ℝ) * t * (p d) ^ (2 : ℕ) =
                  ∫ t in (0 : ℝ)..1, ((L : ℝ) * (p d) ^ (2 : ℕ)) * t := by
                    congr with t
                    ring
              _ = ((L : ℝ) * (p d) ^ (2 : ℕ)) * ∫ t in (0 : ℝ)..1, t := by
                    rw [intervalIntegral.integral_const_mul]
              _ = ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
                    rw [integral_id]
                    norm_num
                    ring
  have hupper : f y - f x - inner ℝ (∇ f x) (y - x) ≤ ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) :=
    (abs_le.mp habs).2
  have hp : p d = p (x - y) := by
    simpa [d, neg_sub] using (map_neg_eq_map p (x - y))
  calc
    f y - f x - inner ℝ (∇ f x) (y - x) ≤ ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := hupper
    _ = ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by rw [hp]

/-- Helper for Theorem 2.5: the witness-bundled monotone-gradient clause `(2.1.12)` implies the
tangent-error inequalities `(2.1.9)` by combining Theorem 2.3 for convexity with the integrated
upper remainder estimate above. -/
private lemma tangent_error_bounds_of_witnessedMonotoneGradientBounds
    (h5 : smoothConvexMonotoneGradientBoundsWithGradientOn p L Set.univ f) :
    smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f := by
  have hdiff : DifferentiableOn ℝ f Set.univ := by
    intro z hz
    exact (h5.hasGradientAt (x := z) (by simp)).differentiableAt.differentiableWithinAt
  have hconv : ConvexOn ℝ Set.univ f := by
    have hmono : GradientMonotoneOn Set.univ f := by
      intro x y hx hy
      -- On the whole space, the monotonicity clause `(2.1.12)` is exactly the within-gradient
      -- monotonicity from Theorem 2.3.
      simpa [gradientWithin, gradient, fderivWithin_univ] using
        (h5.monotone (x := x) (by simp) (y := y) (by simp))
    exact (convexOn_iff_gradient_monotone convex_univ hdiff).mpr hmono
  intro x hx y hy
  have hlower :=
    hconv.lower_tangent_plane
      x hx ((h5.hasGradientAt (x := x) (by simp)).differentiableAt.differentiableWithinAt) y hy
  have hlower' :
      0 ≤ f y - f x - inner ℝ (∇ f x) (y - x) := by
    have hgradWithin_eq : gradientWithin f Set.univ x = ∇ f x := by
      simp [gradientWithin, gradient, fderivWithin_univ]
    rw [hgradWithin_eq] at hlower
    linarith
  -- Pair the convexity lower bound with the integrated upper remainder estimate.
  refine ⟨?_, tangent_error_upperBound_of_monotoneGradientBounds h5⟩
  exact hlower'

/-- Helper for Theorem 2.5: the convex-combination gradient bound `(2.1.13)` recovers the
gradient quadratic lower bound `(2.1.10)` by the scalar endpoint limit `α → 1` along the segment
from `x` to `y`. -/
-- TODO: prove this by restricting to the scalar slice `t ↦ f (x + t • (y - x))`, sending
-- `β → 0⁺`, and converting the secant-slope limit to the ambient gradient pairing.
private lemma gradient_quadratic_lower_bound_of_convexCombinationGradientBound_of_hasGradientAt
    (h6 : smoothConvexConvexCombinationGradientBoundOn p L (∇ f) Set.univ f)
    (hgrad : ∀ z : E, HasGradientAt f (∇ f z) z)
    (hL : 0 < L) :
    smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f := by
  intro x hx y hy
  let φ : ℝ → ℝ := fun β ↦ f (x + β • (y - x))
  let A : ℝ := (1 / (2 * (L : ℝ))) * (‖∇ f x - ∇ f y‖[p,*]) ^ (2 : ℕ)
  have hslope :
      Filter.Tendsto (fun β : ℝ ↦ slope φ 0 β)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (inner ℝ (∇ f x) (y - x))) := by
    -- The segment secant slopes converge to the ambient gradient pairing at the left endpoint.
    simpa [φ] using
      (segment_slope_tendsto_gradientPairing (f := f) (x := x) (y := y) (hgrad x))
  have hβ_tendsto :
      Filter.Tendsto (fun β : ℝ ↦ β)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) :=
    Filter.tendsto_id'.2 nhdsWithin_le_nhds
  have hcoeff :
      Filter.Tendsto (fun β : ℝ ↦ (1 - β) * A)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds A) := by
    -- The prefactor `(1 - β)` converges to `1` along the right-endpoint limit.
    have hcont : Continuous fun β : ℝ ↦ (1 - β) * A :=
      (continuous_const.sub continuous_id).mul continuous_const
    simpa [A] using hcont.continuousAt.tendsto.comp hβ_tendsto
  have hpoint :
      ∀ᶠ β in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        slope φ 0 β + (1 - β) * A ≤ f y - f x := by
    -- Rewrite `(2.1.13)` with `α = 1 - β`, divide by `β > 0`, and identify the quotient as
    -- the segment secant slope.
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)]
      with β hβ hβ_lt_one
    have hβ_pos : 0 < β := hβ
    have hβ_lt_one' : β < 1 := hβ_lt_one
    have hα : 1 - β ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith
    have hxy := h6 hx hy hα
    have hseg : (1 - β) • x + (1 - (1 - β)) • y = x + β • (y - x) := by
      calc
        (1 - β) • x + (1 - (1 - β)) • y = AffineMap.lineMap x y β := by
          simpa [AffineMap.lineMap_apply_module]
        _ = x + β • (y - x) := by
          simpa [add_comm] using (AffineMap.lineMap_apply_module' x y β)
    have hstep :
        (φ β - φ 0) + β * ((1 - β) * A) ≤ β * (f y - f x) := by
      rw [hseg] at hxy
      dsimp [A] at hxy ⊢
      simp [φ] at hxy ⊢
      ring_nf at hxy ⊢
      nlinarith [hxy]
    have hmul : β * (slope φ 0 β + (1 - β) * A) ≤ β * (f y - f x) := by
      calc
        β * (slope φ 0 β + (1 - β) * A) = (φ β - φ 0) + β * ((1 - β) * A) := by
          rw [mul_add, slope_def_field, sub_zero]
          field_simp [hβ_pos.ne']
        _ ≤ β * (f y - f x) := hstep
    exact le_of_mul_le_mul_left hmul hβ_pos
  have hlimit :
      inner ℝ (∇ f x) (y - x) + A ≤ f y - f x :=
    le_of_tendsto_of_tendsto (hslope.add hcoeff) tendsto_const_nhds hpoint
  -- Sending `β → 0⁺` recovers the desired lower quadratic bound at the endpoint.
  dsimp [A] at hlimit
  linarith

/-- Helper for Theorem 2.5: the convex-combination quadratic bound `(2.1.14)` recovers the
tangent-error inequalities `(2.1.9)` once the canonical ambient gradient is known to exist
pointwise, by taking the endpoint limit `α → 1` along the segment from `x` to `y`. -/
-- TODO: combine convexity from `(2.1.14)` with the same scalar endpoint-limit argument used for
-- `(2.1.13)`, after rewriting the secant limit through the recovered ambient gradient.
private lemma tangent_error_bounds_of_convexCombinationQuadraticBound_of_hasGradientAt
    (h7 : smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f)
    (hgrad : ∀ z : E, HasGradientAt f (∇ f z) z) :
    smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f := by
  intro x hx y hy
  let φ : ℝ → ℝ := fun β ↦ f (x + β • (y - x))
  let B : ℝ := ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ)
  have hslope :
      Filter.Tendsto (fun β : ℝ ↦ slope φ 0 β)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ)))
        (nhds (inner ℝ (∇ f x) (y - x))) := by
    -- The one-sided segment secants still converge to the recovered ambient gradient pairing.
    simpa [φ] using
      (segment_slope_tendsto_gradientPairing (f := f) (x := x) (y := y) (hgrad x))
  have hβ_tendsto :
      Filter.Tendsto (fun β : ℝ ↦ β)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) :=
    Filter.tendsto_id'.2 nhdsWithin_le_nhds
  have hcoeff :
      Filter.Tendsto (fun β : ℝ ↦ (1 - β) * B)
        (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds B) := by
    -- The quadratic prefactor converges to the endpoint constant.
    have hcont : Continuous fun β : ℝ ↦ (1 - β) * B :=
      (continuous_const.sub continuous_id).mul continuous_const
    simpa [B] using hcont.continuousAt.tendsto.comp hβ_tendsto
  have hlowerPoint :
      ∀ᶠ β in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        slope φ 0 β ≤ f y - f x := by
    -- The nonnegative Jensen gap from `(2.1.14)` gives the lower tangent inequality after
    -- dividing by `β > 0`.
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)]
      with β hβ hβ_lt_one
    have hβ_pos : 0 < β := hβ
    have hβ_lt_one' : β < 1 := hβ_lt_one
    have hα : 1 - β ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith
    have hxy := (h7.nonneg hx hy hα)
    have hseg : (1 - β) • x + (1 - (1 - β)) • y = x + β • (y - x) := by
      calc
        (1 - β) • x + (1 - (1 - β)) • y = AffineMap.lineMap x y β := by
          simpa [AffineMap.lineMap_apply_module]
        _ = x + β • (y - x) := by
          simpa [add_comm] using (AffineMap.lineMap_apply_module' x y β)
    have hstep : φ β - φ 0 ≤ β * (f y - f x) := by
      rw [hseg] at hxy
      simp [φ] at hxy ⊢
      ring_nf at hxy ⊢
      nlinarith [hxy]
    have hmul : β * slope φ 0 β ≤ β * (f y - f x) := by
      calc
        β * slope φ 0 β = φ β - φ 0 := by
          rw [slope_def_field, sub_zero]
          field_simp [hβ_pos.ne']
        _ ≤ β * (f y - f x) := hstep
    exact le_of_mul_le_mul_left hmul hβ_pos
  have hupperPoint :
      ∀ᶠ β in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
        f y - f x - slope φ 0 β ≤ (1 - β) * B := by
    -- The upper Jensen-gap bound gives the quadratic tangent-error estimate after the same
    -- endpoint normalization.
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)]
      with β hβ hβ_lt_one
    have hβ_pos : 0 < β := hβ
    have hβ_lt_one' : β < 1 := hβ_lt_one
    have hα : 1 - β ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · linarith
      · linarith
    have hxy := (h7.upperBound hx hy hα)
    have hseg : (1 - β) • x + (1 - (1 - β)) • y = x + β • (y - x) := by
      calc
        (1 - β) • x + (1 - (1 - β)) • y = AffineMap.lineMap x y β := by
          simpa [AffineMap.lineMap_apply_module]
        _ = x + β • (y - x) := by
          simpa [add_comm] using (AffineMap.lineMap_apply_module' x y β)
    have hstep :
        β * (f y - f x) - (φ β - φ 0) ≤ β * ((1 - β) * B) := by
      rw [hseg] at hxy
      dsimp [B] at hxy ⊢
      simp [φ] at hxy ⊢
      ring_nf at hxy ⊢
      nlinarith [hxy]
    have hmul : β * (f y - f x - slope φ 0 β) ≤ β * ((1 - β) * B) := by
      calc
        β * (f y - f x - slope φ 0 β) = β * (f y - f x) - β * slope φ 0 β := by ring
        _ = β * (f y - f x) - (φ β - φ 0) := by
          rw [slope_def_field, sub_zero]
          field_simp [hβ_pos.ne']
        _ ≤ β * ((1 - β) * B) := hstep
    exact le_of_mul_le_mul_left hmul hβ_pos
  have hlower :
      inner ℝ (∇ f x) (y - x) ≤ f y - f x :=
    le_of_tendsto_of_tendsto hslope tendsto_const_nhds hlowerPoint
  have hupper :
      f y - f x - inner ℝ (∇ f x) (y - x) ≤ B :=
    le_of_tendsto_of_tendsto (tendsto_const_nhds.sub hslope) hcoeff hupperPoint
  -- The two endpoint limits recover the lower and upper tangent-error bounds.
  constructor
  · linarith
  · simpa [B] using hupper

/-- Helper for Theorem 2.5: affine combinations of two points on the same line remain on that
line with the expected scalar parameter. -/
private lemma affineLineCombination_eq
    (x d : E) (s t α : ℝ) :
    α • (x + s • d) + (1 - α) • (x + t • d) =
      x + (α * s + (1 - α) * t) • d := by
  -- Expand both affine combinations and regroup the two `x` terms and the two `d` terms.
  calc
    α • (x + s • d) + (1 - α) • (x + t • d)
        = α • x + (α * s) • d + ((1 - α) • x + ((1 - α) * t) • d) := by
            simp [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]
    _ = (α • x + (1 - α) • x) + ((α * s) • d + ((1 - α) * t) • d) := by
          abel_nf
    _ = (α + (1 - α)) • x + ((α * s) + (1 - α) * t) • d := by
          rw [add_smul, add_smul]
    _ = x + (α * s + (1 - α) * t) • d := by
          simp

/-- Helper for Theorem 2.5: subtracting two points on the same affine line leaves the scalar
difference times the direction vector. -/
private lemma affineLineSub_eq
    (x d : E) (s t : ℝ) :
    (x + s • d) - (x + t • d) = (s - t) • d := by
  -- The base point cancels, leaving only the signed scalar difference along `d`.
  calc
    (x + s • d) - (x + t • d) = s • d - t • d := by
      abel
    _ = (s - t) • d := by
      rw [sub_smul]

/-- Helper for Theorem 2.5: `(2.1.13)` restricts to the same convex-combination inequality along
every affine line `t ↦ x + t • d`. -/
private lemma segment_convexCombinationGradientBound_of_convexCombinationGradientBound
    (h6 : smoothConvexConvexCombinationGradientBoundOn p L (∇ f) Set.univ f)
    {x d : E} :
    let φ : ℝ → ℝ := fun t ↦ f (x + t • d)
    let gLine : ℝ → E := fun t ↦ ∇ f (x + t • d)
    ∀ ⦃s t α : ℝ⦄, α ∈ Set.Icc (0 : ℝ) 1 →
      α * φ s + (1 - α) * φ t ≥
        φ (α * s + (1 - α) * t) +
          (α * (1 - α) / (2 * (L : ℝ))) *
            (‖gLine s - gLine t‖[p,*]) ^ (2 : ℕ) := by
  dsimp
  intro s t α hα
  have hline :=
    h6 (x := x + s • d) (by simp) (y := x + t • d) (by simp) hα
  -- Normalize the ambient affine combination back to the scalar parameter on the fixed line.
  rw [affineLineCombination_eq x d s t α] at hline
  simpa [one_smul, zero_smul] using hline

/-- Helper for Theorem 2.5: `(2.1.14)` restricts to the same one-dimensional quadratic Jensen-gap
bound along every affine line `t ↦ x + t • d`. -/
private lemma segment_convexCombinationQuadraticBound_of_convexCombinationQuadraticBound
    (h7 : smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f)
    {x d : E} :
    let φ : ℝ → ℝ := fun t ↦ f (x + t • d)
    ∀ ⦃s t α : ℝ⦄, α ∈ Set.Icc (0 : ℝ) 1 →
      0 ≤ α * φ s + (1 - α) * φ t - φ (α * s + (1 - α) * t) ∧
        α * φ s + (1 - α) * φ t - φ (α * s + (1 - α) * t) ≤
          α * (1 - α) * ((L : ℝ) / 2) * (p ((s - t) • d)) ^ (2 : ℕ) := by
  dsimp
  intro s t α hα
  have hline :=
    h7 (x := x + s • d) (by simp) (y := x + t • d) (by simp) hα
  -- Both the convex-combination point and the line displacement reduce to scalar normal forms.
  rw [affineLineCombination_eq x d s t α, affineLineSub_eq x d s t] at hline
  simpa [one_smul, zero_smul] using hline

/-- Helper for Theorem 2.5: under `(2.1.12)`, pairing the totalized gradient along a line with
the line direction gives a monotone scalar field with a linear increment bound. -/
-- TODO: rewrite the ambient monotonicity and upper pairing inequalities on the two line points
-- `x + s • d` and `x + t • d` to a scalar estimate for `t ↦ ⟪∇f(x + t d), d⟫`.
private lemma segment_pairing_bounds_of_monotoneGradientBounds
    (h5 : smoothConvexMonotoneGradientBoundsOn p L (∇ f) Set.univ)
    {x d : E} :
    let m : ℝ → ℝ := fun t ↦ inner ℝ (∇ f (x + t • d)) d
    ∀ ⦃s t : ℝ⦄, s ≤ t →
      0 ≤ m t - m s ∧
        m t - m s ≤ (L : ℝ) * (t - s) * (p d) ^ (2 : ℕ) := by
  dsimp
  intro s t hst
  by_cases hst_eq : s = t
  · subst hst_eq
    simp
  · have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
    have hδ_pos : 0 < t - s := sub_pos.mpr hst_lt
    have hmono :
        0 ≤ inner ℝ (∇ f (x + t • d) - ∇ f (x + s • d))
          ((x + t • d) - (x + s • d)) :=
      h5.monotone (x := x + t • d) (by simp) (y := x + s • d) (by simp)
    have hupper :
        inner ℝ (∇ f (x + t • d) - ∇ f (x + s • d))
            ((x + t • d) - (x + s • d)) ≤
          (L : ℝ) * (p ((x + t • d) - (x + s • d))) ^ (2 : ℕ) :=
      h5.upperBound (x := x + t • d) (by simp) (y := x + s • d) (by simp)
    have hseg : (x + t • d) - (x + s • d) = (t - s) • d := affineLineSub_eq x d t s
    have hpseg :
        p ((x + t • d) - (x + s • d)) = (t - s) * p d := by
      calc
        p ((x + t • d) - (x + s • d)) = p ((t - s) • d) := by rw [hseg]
        _ = |t - s| * p d := by
              simpa [Real.norm_eq_abs] using (map_smul_eq_mul p (t - s) d)
        _ = (t - s) * p d := by rw [abs_of_pos hδ_pos]
    have hmono' :
        0 ≤ (t - s) *
          (inner ℝ (∇ f (x + t • d)) d - inner ℝ (∇ f (x + s • d)) d) := by
      simpa [hseg, inner_sub_left, inner_smul_right] using hmono
    have hm_nonneg :
        0 ≤ inner ℝ (∇ f (x + t • d)) d - inner ℝ (∇ f (x + s • d)) d := by
      nlinarith [hmono', hδ_pos]
    have hupper' :
        (t - s) *
            (inner ℝ (∇ f (x + t • d)) d - inner ℝ (∇ f (x + s • d)) d) ≤
          (t - s) * ((L : ℝ) * (t - s) * (p d) ^ (2 : ℕ)) := by
      calc
        (t - s) *
            (inner ℝ (∇ f (x + t • d)) d - inner ℝ (∇ f (x + s • d)) d)
            ≤ (L : ℝ) * (p ((x + t • d) - (x + s • d))) ^ (2 : ℕ) := by
                simpa [hseg, inner_sub_left, inner_smul_right] using hupper
        _ = (L : ℝ) * ((t - s) * p d) ^ (2 : ℕ) := by rw [hpseg]
        _ = (t - s) * ((L : ℝ) * (t - s) * (p d) ^ (2 : ℕ)) := by ring
    have hm_upper :
        inner ℝ (∇ f (x + t • d)) d - inner ℝ (∇ f (x + s • d)) d ≤
          (L : ℝ) * (t - s) * (p d) ^ (2 : ℕ) := by
      nlinarith [hupper', hδ_pos]
    exact ⟨hm_nonneg, hm_upper⟩

/-- Helper for Theorem 2.5: restricting `(2.1.14)` to a line gives the right-tangent error bound
at the left endpoint of the scalar slice. -/
-- TODO: derive convexity of the scalar slice from the nonnegative Jensen gap, identify the
-- right derivative at `0`, and compare it to the endpoint secant slope.
private lemma segment_tangent_error_bounds_of_convexCombinationQuadraticBound
    (h7 : smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f)
    {z d : E} :
    0 ≤ f (z + d) - f z - derivWithin (fun t : ℝ ↦ f (z + t • d)) (Set.Ioi (0 : ℝ)) 0 ∧
      f (z + d) - f z - derivWithin (fun t : ℝ ↦ f (z + t • d)) (Set.Ioi (0 : ℝ)) 0 ≤
        ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
  let φ : ℝ → ℝ := fun t ↦ f (z + t • d)
  let q : ℝ → ℝ := fun t ↦ ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) * t ^ (2 : ℕ)
  let ψ : ℝ → ℝ := fun t ↦ q t - φ t
  have hline :=
    segment_convexCombinationQuadraticBound_of_convexCombinationQuadraticBound
      (f := f) (p := p) (L := L) h7 (x := z) (d := d)
  have hφconv : ConvexOn ℝ Set.univ φ := by
    -- The nonnegative Jensen gap from `(2.1.14)` is exactly convexity of the scalar slice.
    refine (convexOn_iff_segment_inequality convex_univ).2 ?_
    intro s hs t ht α hα
    have hgap := (hline (s := s) (t := t) (α := α) hα).1
    exact sub_nonneg.mp (by simpa [smul_eq_mul] using hgap)
  have hφderiv :
      HasDerivWithinAt φ (derivWithin φ (Set.Ioi (0 : ℝ)) 0) (Set.Ioi (0 : ℝ)) 0 := by
    -- The right derivative exists for every convex real slice on the interior of its domain.
    exact ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior hφconv (by simp)
  have hlowerSlope :
      derivWithin φ (Set.Ioi (0 : ℝ)) 0 ≤ slope φ 0 1 := by
    -- Convexity makes the right derivative at `0` lie below the secant slope to `1`.
    exact ConvexOn.le_slope_of_hasDerivWithinAt_Ioi hφconv (by simp) (by simp) (by norm_num)
      hφderiv
  have hlower :
      0 ≤ φ 1 - φ 0 - derivWithin φ (Set.Ioi (0 : ℝ)) 0 := by
    have hslope : slope φ 0 1 = φ 1 - φ 0 := by
      simp [φ, slope_def_field]
    linarith
  have hψconv : ConvexOn ℝ Set.univ ψ := by
    -- Route correction: rather than pushing endpoint secant algebra directly, convexify the
    -- corrected scalar slice `q - φ` and apply the same right-derivative comparison once.
    refine (convexOn_iff_segment_inequality convex_univ).2 ?_
    intro s hs t ht α hα
    rcases hline (s := s) (t := t) (α := α) hα with ⟨_, hupper⟩
    have hpseg_sq :
        (p ((s - t) • d)) ^ (2 : ℕ) = (s - t) ^ (2 : ℕ) * (p d) ^ (2 : ℕ) := by
      calc
        (p ((s - t) • d)) ^ (2 : ℕ) = (|s - t| * p d) ^ (2 : ℕ) := by
          congr 1
          simpa [Real.norm_eq_abs] using (map_smul_eq_mul p (s - t) d)
        _ = (s - t) ^ (2 : ℕ) * (p d) ^ (2 : ℕ) := by
          rw [pow_two, pow_two]
          nlinarith [sq_abs (s - t)]
    have hqgap :
        α * q s + (1 - α) * q t - q (α * s + (1 - α) * t) =
          α * (1 - α) * ((L : ℝ) / 2) * (p ((s - t) • d)) ^ (2 : ℕ) := by
      rw [hpseg_sq]
      dsimp [q]
      ring
    have hgap_nonneg :
        0 ≤ α * ψ s + (1 - α) * ψ t - ψ (α * s + (1 - α) * t) := by
      have hrew :
          α * ψ s + (1 - α) * ψ t - ψ (α * s + (1 - α) * t) =
            (α * q s + (1 - α) * q t - q (α * s + (1 - α) * t)) -
              (α * φ s + (1 - α) * φ t - φ (α * s + (1 - α) * t)) := by
        dsimp [ψ]
        ring
      rw [hrew, hqgap]
      linarith
    have hgap :
        ψ (α * s + (1 - α) * t) ≤ α * ψ s + (1 - α) * ψ t := by
      linarith
    exact hgap
  have hqderiv : HasDerivWithinAt q 0 (Set.Ioi (0 : ℝ)) 0 := by
    -- The quadratic correction has vanishing derivative at the left endpoint.
    have hq0 : HasDerivAt q 0 0 := by
      dsimp [q]
      simpa using (((hasDerivAt_id 0).pow 2).const_mul (((L : ℝ) / 2) * (p d) ^ (2 : ℕ)))
    exact hq0.hasDerivWithinAt
  have hψderiv :
      HasDerivWithinAt ψ (-derivWithin φ (Set.Ioi (0 : ℝ)) 0) (Set.Ioi (0 : ℝ)) 0 := by
    -- The corrected slice differentiates to minus the right derivative of `φ` at `0`.
    dsimp [ψ]
    simpa using hqderiv.sub hφderiv
  have hupperSlope :
      -derivWithin φ (Set.Ioi (0 : ℝ)) 0 ≤ slope ψ 0 1 := by
    -- Applying the same convex secant comparison to the corrected slice gives the upper bound.
    exact ConvexOn.le_slope_of_hasDerivWithinAt_Ioi hψconv (by simp) (by simp) (by norm_num)
      hψderiv
  have hslopeψ :
      slope ψ 0 1 = ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) - (φ 1 - φ 0) := by
    dsimp [ψ, q]
    simp [slope_def_field]
    ring
  have hupper :
      φ 1 - φ 0 - derivWithin φ (Set.Ioi (0 : ℝ)) 0 ≤ ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
    rw [hslopeψ] at hupperSlope
    linarith
  have hlower' :
      0 ≤ f (z + d) - f z - derivWithin (fun t : ℝ ↦ f (z + t • d)) (Set.Ioi (0 : ℝ)) 0 := by
    simpa [φ] using hlower
  have hupper' :
      f (z + d) - f z - derivWithin (fun t : ℝ ↦ f (z + t • d)) (Set.Ioi (0 : ℝ)) 0 ≤
        ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
    simpa [φ] using hupper
  -- Re-expand the slice notation back to the ambient statement.
  exact ⟨hlower', hupper'⟩

/-- Helper for Theorem 2.5: after scaling a line direction by a positive factor, the right
derivative of the corresponding slice still tracks the positive secant slope with only an `O(t)`
error. This packages the endpoint algebra needed to compare line slices at different speeds. -/
private lemma scaledSlice_hasDerivWithinAt_zero_of_pos
    {φ : ℝ → ℝ} {a t : ℝ} (ht : 0 < t)
    (hφ : HasDerivWithinAt φ a (Set.Ioi (0 : ℝ)) 0) :
    HasDerivWithinAt (fun s : ℝ ↦ φ (s * t)) (t * a) (Set.Ioi (0 : ℝ)) 0 := by
  -- Compose the original right-derivative witness with the positive rescaling `s ↦ s * t`,
  -- which preserves the domain `Set.Ioi 0`.
  have hmul : HasDerivWithinAt (fun s : ℝ ↦ s * t) t (Set.Ioi (0 : ℝ)) 0 := by
    simpa [one_mul] using ((hasDerivAt_id 0).mul_const t).hasDerivWithinAt
  have hmaps : Set.MapsTo (fun s : ℝ ↦ s * t) (Set.Ioi (0 : ℝ)) (Set.Ioi (0 : ℝ)) := by
    intro s hs
    exact mul_pos hs ht
  simpa [smul_eq_mul, mul_comm] using hφ.scomp_of_eq 0 hmul hmaps (by simp)

 /-- Helper for Theorem 2.5: after scaling a line direction by a positive factor, the right
derivative of the corresponding slice still tracks the positive secant slope with only an `O(t)`
error. This packages the endpoint algebra needed to compare line slices at different speeds. -/
-- TODO: apply `segment_tangent_error_bounds_of_convexCombinationQuadraticBound` to the rescaled
-- direction `t • d`, rewrite the derivative by the chain rule, and divide by `t > 0`.
private lemma sliceSecantApprox_rightDeriv_of_convexCombinationQuadraticBound
    (h7 : smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f)
    {z d : E} {t : ℝ} (ht : 0 < t) :
    let φ : ℝ → ℝ := fun s ↦ f (z + s • d)
    |((φ t - φ 0) / t) - derivWithin φ (Set.Ioi (0 : ℝ)) 0| ≤
      t * ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
  let φ : ℝ → ℝ := fun s ↦ f (z + s • d)
  let ψ : ℝ → ℝ := fun s ↦ f (z + s • (t • d))
  have hline :=
    segment_convexCombinationQuadraticBound_of_convexCombinationQuadraticBound
      (f := f) (p := p) (L := L) h7 (x := z) (d := d)
  have hφconv : ConvexOn ℝ Set.univ φ := by
    -- The nonnegative Jensen gap from `(2.1.14)` restricts to convexity of the scalar slice.
    refine (convexOn_iff_segment_inequality convex_univ).2 ?_
    intro s hs u hu α hα
    have hgap := (hline (s := s) (t := u) (α := α) hα).1
    exact sub_nonneg.mp (by simpa [φ, smul_eq_mul] using hgap)
  have hφderiv :
      HasDerivWithinAt φ (derivWithin φ (Set.Ioi (0 : ℝ)) 0) (Set.Ioi (0 : ℝ)) 0 := by
    -- Convex real slices admit a right derivative at interior points of their domain.
    exact ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior hφconv (by simp)
  have hψderiv :
      HasDerivWithinAt ψ (t * derivWithin φ (Set.Ioi (0 : ℝ)) 0) (Set.Ioi (0 : ℝ)) 0 := by
    -- Route correction: compare the faster slice `ψ` to the original `φ` through the positive
    -- rescaling `s ↦ s * t`, instead of unfolding the endpoint algebra directly.
    have hscaled :=
      scaledSlice_hasDerivWithinAt_zero_of_pos (t := t) ht hφderiv
    simpa [φ, ψ, smul_smul, mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hψderiv_eq :
      derivWithin ψ (Set.Ioi (0 : ℝ)) 0 = t * derivWithin φ (Set.Ioi (0 : ℝ)) 0 := by
    exact hψderiv.derivWithin (uniqueDiffWithinAt_Ioi (0 : ℝ))
  rcases
      segment_tangent_error_bounds_of_convexCombinationQuadraticBound
        (f := f) (p := p) (L := L) h7 (z := z) (d := t • d)
    with ⟨hψ_nonneg, hψ_upper⟩
  have hpseg : p (t • d) = t * p d := by
    calc
      p (t • d) = |t| * p d := by
        simpa [Real.norm_eq_abs] using (map_smul_eq_mul p t d)
      _ = t * p d := by rw [abs_of_pos ht]
  have habs :
      |f (z + t • d) - f z - t * derivWithin φ (Set.Ioi (0 : ℝ)) 0| ≤
        ((L : ℝ) / 2) * (p (t • d)) ^ (2 : ℕ) := by
    rw [← hψderiv_eq, abs_of_nonneg hψ_nonneg]
    simpa [ψ] using hψ_upper
  have hquot :
      ((φ t - φ 0) / t) - derivWithin φ (Set.Ioi (0 : ℝ)) 0 =
        (f (z + t • d) - f z - t * derivWithin φ (Set.Ioi (0 : ℝ)) 0) / t := by
    calc
      ((φ t - φ 0) / t) - derivWithin φ (Set.Ioi (0 : ℝ)) 0
          = ((φ t - φ 0) - t * derivWithin φ (Set.Ioi (0 : ℝ)) 0) / t := by
              field_simp [ht.ne']
      _ = (f (z + t • d) - f z - t * derivWithin φ (Set.Ioi (0 : ℝ)) 0) / t := by
            congr 1
            simp [φ]
  calc
    |((φ t - φ 0) / t) - derivWithin φ (Set.Ioi (0 : ℝ)) 0|
        = |(f (z + t • d) - f z - t * derivWithin φ (Set.Ioi (0 : ℝ)) 0) / t| := by
            rw [hquot]
    _ = |f (z + t • d) - f z - t * derivWithin φ (Set.Ioi (0 : ℝ)) 0| / t := by
          rw [abs_div, abs_of_pos ht]
    _ ≤ (((L : ℝ) / 2) * (p (t • d)) ^ (2 : ℕ)) / t := by
          exact div_le_div_of_nonneg_right habs (le_of_lt ht)
    _ = (((L : ℝ) / 2) * (t * p d) ^ (2 : ℕ)) / t := by rw [hpseg]
    _ = (((L : ℝ) / 2) * (t ^ (2 : ℕ) * (p d) ^ (2 : ℕ))) / t := by
          ring
    _ = (((L : ℝ) / 2) * t) * (p d) ^ (2 : ℕ) := by
          field_simp [ht.ne']
    _ = t * ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
          ring

/-- Helper for Theorem 2.5: at a fixed base point, the right directional derivatives coming from
`(2.1.14)` assemble into a continuous linear functional with the same quadratic affine-model
remainder bound. -/
private lemma rightDirectionalDerivativeLinearMapOfConvexCombinationQuadraticBound
    (h7 : smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f)
    (z : E) :
    ∃ ell : E →L[ℝ] ℝ,
      ∀ d : E,
        ell d = derivWithin (fun t : ℝ ↦ f (z + t • d)) (Set.Ioi (0 : ℝ)) 0 ∧
          |f (z + d) - f z - ell d| ≤ ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
  let D : E → ℝ := fun d ↦
    derivWithin (fun t : ℝ ↦ f (z + t • d)) (Set.Ioi (0 : ℝ)) 0
  let sec : E → ℝ → ℝ := fun d t ↦ slope (fun s : ℝ ↦ f (z + s • d)) 0 t
  have hsec_tendsto :
      ∀ d : E,
        Filter.Tendsto (sec d) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (D d)) := by
    intro d
    let φ : ℝ → ℝ := fun t ↦ f (z + t • d)
    have hφconv : ConvexOn ℝ Set.univ φ := by
      -- The nonnegative Jensen gap from `(2.1.14)` restricts to convexity on each scalar slice.
      refine (convexOn_iff_segment_inequality convex_univ).2 ?_
      intro s hs t ht α hα
      have hgap :=
        (segment_convexCombinationQuadraticBound_of_convexCombinationQuadraticBound
          (f := f) (p := p) (L := L) h7 (x := z) (d := d) (s := s) (t := t) (α := α) hα).1
      exact sub_nonneg.mp (by simpa [smul_eq_mul] using hgap)
    have hφderiv :
        HasDerivWithinAt φ (D d) (Set.Ioi (0 : ℝ)) 0 := by
      -- Convex scalar slices admit the canonical right derivative at the left endpoint.
      simpa [D, φ] using
        ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior hφconv (by simp)
    simpa [sec, φ] using
      (hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Set.Ioi (0 : ℝ))).mp hφderiv
  have hscaled_tendsto :
      ∀ {a : ℝ}, 0 < a → ∀ d : E,
        Filter.Tendsto (fun t : ℝ ↦ sec d (a * t))
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (D d)) := by
    intro a ha d
    have hscale :
        Filter.Tendsto (fun t : ℝ ↦ a * t)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhdsWithin 0 (Set.Ioi (0 : ℝ))) := by
      -- Positive scalar reparameterizations preserve the right-neighborhood filter at `0`.
      have hcont : Continuous fun t : ℝ ↦ a * t := continuous_const.mul continuous_id
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · simpa using Filter.Tendsto.mono_left
          ((hcont.continuousAt : ContinuousAt (fun t : ℝ ↦ a * t) 0).tendsto) nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos ha ht
    exact (hsec_tendsto d).comp hscale
  have hodd : ∀ d : E, D (-d) = -D d := by
    intro d
    have hbound_tendsto :
        Filter.Tendsto (fun t : ℝ ↦ t * ((L : ℝ) * (p d) ^ (2 : ℕ)))
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
      -- The symmetric secant-sum bound vanishes linearly as `t → 0⁺`.
      have hcont : Continuous fun t : ℝ ↦ t * ((L : ℝ) * (p d) ^ (2 : ℕ)) :=
        continuous_id.mul continuous_const
      simpa using Filter.Tendsto.mono_left
        ((hcont.continuousAt :
          ContinuousAt (fun t : ℝ ↦ t * ((L : ℝ) * (p d) ^ (2 : ℕ))) 0).tendsto)
        nhdsWithin_le_nhds
    have hsum_tendsto_zero :
        Filter.Tendsto (fun t : ℝ ↦ sec d t + sec (-d) t)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds 0) := by
      refine squeeze_zero' ?_ ?_ hbound_tendsto
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have ht_pos : 0 < t := ht
        let hline :=
          segment_convexCombinationQuadraticBound_of_convexCombinationQuadraticBound
            (f := f) (p := p) (L := L) h7 (x := z) (d := d)
        have hgap_nonneg := (hline (s := t) (t := -t) (α := (1 / 2 : ℝ)) (by norm_num)).1
        have hmid_scalar : (1 / 2 : ℝ) * t + (1 - 1 / 2) * (-t) = 0 := by ring
        have hsec_eq :
            sec d t + sec (-d) t =
              (f (z + t • d) + f (z + t • (-d)) - 2 * f z) / t := by
          simp [sec, slope_def_field, sub_eq_add_neg]
          ring
        rw [hmid_scalar] at hgap_nonneg
        norm_num at hgap_nonneg
        have hgap_nonneg2 :
            2 * f z ≤ f (z + t • d) + f (z + t • (-d)) := by
          have hmul := mul_le_mul_of_nonneg_left hgap_nonneg (show 0 ≤ (2 : ℝ) by norm_num)
          ring_nf at hmul
          simpa [two_mul, mul_comm, smul_neg] using hmul
        have hnum_nonneg :
            0 ≤ f (z + t • d) + f (z + t • (-d)) - 2 * f z := by
          linarith
        rw [hsec_eq]
        exact div_nonneg hnum_nonneg ht_pos.le
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have ht_pos : 0 < t := ht
        let hline :=
          segment_convexCombinationQuadraticBound_of_convexCombinationQuadraticBound
            (f := f) (p := p) (L := L) h7 (x := z) (d := d)
        have hgap_upper := (hline (s := t) (t := -t) (α := (1 / 2 : ℝ)) (by norm_num)).2
        have hmid_scalar : (1 / 2 : ℝ) * t + (1 - 1 / 2) * (-t) = 0 := by ring
        have hpseg :
            p ((t - (-t)) • d) = (2 * t) * p d := by
          calc
            p ((t - (-t)) • d) = |t - (-t)| * p d := by
              simpa [Real.norm_eq_abs] using (map_smul_eq_mul p (t - (-t)) d)
            _ = (2 * t) * p d := by
              rw [abs_of_pos (by linarith [ht_pos] : 0 < t - (-t))]
              ring
        have hsec_eq :
            sec d t + sec (-d) t =
              (f (z + t • d) + f (z + t • (-d)) - 2 * f z) / t := by
          simp [sec, slope_def_field, sub_eq_add_neg]
          ring
        rw [hmid_scalar] at hgap_upper
        norm_num at hgap_upper
        have hgap_upper2 :
            f (z + t • d) + f (z + t • (-d)) ≤
              2 * f z + (L : ℝ) * ((1 / 4 : ℝ) * p ((t * 2) • d) ^ (2 : ℕ)) := by
          have hmul := mul_le_mul_of_nonneg_left hgap_upper (show 0 ≤ (2 : ℝ) by norm_num)
          ring_nf at hmul
          simpa [two_mul, smul_neg, add_assoc, add_left_comm, add_comm,
            mul_assoc, mul_left_comm, mul_comm] using hmul
        have hnum_le :
            f (z + t • d) + f (z + t • (-d)) - 2 * f z ≤
              t * (t * ((L : ℝ) * (p d) ^ (2 : ℕ))) := by
          have hpseg_sq :
              (p ((t * 2) • d)) ^ (2 : ℕ) =
                (2 * t) ^ (2 : ℕ) * (p d) ^ (2 : ℕ) := by
            calc
              (p ((t * 2) • d)) ^ (2 : ℕ) = (((t * 2) : ℝ) * p d) ^ (2 : ℕ) := by
                congr 1
                calc
                  p ((t * 2) • d) = |t * 2| * p d := by
                    simpa [Real.norm_eq_abs] using (map_smul_eq_mul p (t * 2) d)
                  _ = (t * 2) * p d := by
                    rw [abs_of_pos (by positivity : 0 < t * 2)]
              _ = (2 * t) ^ (2 : ℕ) * (p d) ^ (2 : ℕ) := by
                ring
          have hgap_upper3 :
              f (z + t • d) + f (z + t • (-d)) - 2 * f z ≤
                (L : ℝ) * ((1 / 4 : ℝ) * p ((t * 2) • d) ^ (2 : ℕ)) := by
            nlinarith [hgap_upper2]
          have hgap_upper4 :
              f (z + t • d) + f (z + t • (-d)) - 2 * f z ≤
                (L : ℝ) * ((1 / 4 : ℝ) * ((2 * t) ^ (2 : ℕ) * (p d) ^ (2 : ℕ))) := by
            rw [hpseg_sq] at hgap_upper3
            exact hgap_upper3
          nlinarith [hgap_upper4, ht_pos]
        rw [hsec_eq]
        have hdiv := div_le_div_of_nonneg_right hnum_le ht_pos.le
        simpa [ht_pos.ne', mul_assoc] using hdiv
    have hsum_tendsto :
        Filter.Tendsto (fun t : ℝ ↦ sec d t + sec (-d) t)
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (D d + D (-d))) :=
      (hsec_tendsto d).add (hsec_tendsto (-d))
    have hsum_eq_zero : D d + D (-d) = 0 :=
      tendsto_nhds_unique hsum_tendsto hsum_tendsto_zero
    linarith
  have hsmul_nonneg : ∀ d : E, ∀ {a : ℝ}, 0 ≤ a → D (a • d) = a * D d := by
    intro d a ha
    rcases lt_or_eq_of_le ha with hpos | rfl
    · have hφderiv :
          HasDerivWithinAt (fun t : ℝ ↦ f (z + t • d)) (D d) (Set.Ioi (0 : ℝ)) 0 := by
        -- Reuse the canonical right derivative of the original slice before rescaling the speed.
        let φ : ℝ → ℝ := fun t ↦ f (z + t • d)
        have hφconv : ConvexOn ℝ Set.univ φ := by
          refine (convexOn_iff_segment_inequality convex_univ).2 ?_
          intro s hs t ht α hα
          have hgap :=
            (segment_convexCombinationQuadraticBound_of_convexCombinationQuadraticBound
              (f := f) (p := p) (L := L) h7 (x := z) (d := d) (s := s) (t := t) (α := α) hα).1
          exact sub_nonneg.mp (by simpa [smul_eq_mul] using hgap)
        simpa [D, φ] using
          ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior hφconv (by simp)
      have hscaled :=
        scaledSlice_hasDerivWithinAt_zero_of_pos (t := a) hpos hφderiv
      have hderiv_eq :
          derivWithin (fun s : ℝ ↦ f (z + s • (a • d))) (Set.Ioi (0 : ℝ)) 0 = a * D d := by
        simpa [D, smul_smul, mul_comm, mul_left_comm, mul_assoc] using
          hscaled.derivWithin (uniqueDiffWithinAt_Ioi (0 : ℝ))
      simpa [D] using hderiv_eq
    · have hzero : D (0 : E) = 0 := by
        have h0 := hodd (0 : E)
        have hsum := congrArg (fun x : ℝ ↦ x + D (0 : E)) h0
        simpa using hsum
      simpa using hzero
  have hsmul : ∀ a : ℝ, ∀ d : E, D (a • d) = a * D d := by
    intro a d
    rcases lt_or_ge a 0 with ha | ha
    · have hneg' : 0 < -a := by linarith
      calc
        D (a • d) = D ((-a) • (-d)) := by
          congr 1
          calc
            a • d = -((-a) • d) := by simpa using (neg_smul (-a) d).symm
            _ = (-a) • (-d) := by rw [smul_neg]
        _ = (-a) * D (-d) := hsmul_nonneg (-d) hneg'.le
        _ = a * D d := by rw [hodd d]; ring
    · exact hsmul_nonneg d ha
  have hsubadd : ∀ d₁ d₂ : E, D (d₁ + d₂) ≤ D d₁ + D d₂ := by
    intro d₁ d₂
    have hsec2_1 :
        Filter.Tendsto (fun t : ℝ ↦ sec d₁ (2 * t))
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (D d₁)) :=
      hscaled_tendsto (a := 2) (by norm_num) d₁
    have hsec2_2 :
        Filter.Tendsto (fun t : ℝ ↦ sec d₂ (2 * t))
          (nhdsWithin 0 (Set.Ioi (0 : ℝ))) (nhds (D d₂)) :=
      hscaled_tendsto (a := 2) (by norm_num) d₂
    have hpoint :
        ∀ᶠ t in nhdsWithin 0 (Set.Ioi (0 : ℝ)),
          sec (d₁ + d₂) t ≤ sec d₁ (2 * t) + sec d₂ (2 * t) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht_pos : 0 < t := ht
      have ht2_ne : (2 * t) ≠ 0 := by positivity
      have hmid_nonneg :=
        (h7.nonneg (x := z + (2 * t) • d₁) (by simp) (y := z + (2 * t) • d₂) (by simp)
          (α := (1 / 2 : ℝ)) (by norm_num))
      have hmid :
          (1 / 2 : ℝ) • (z + (2 * t) • d₁) + (1 - 1 / 2 : ℝ) • (z + (2 * t) • d₂) =
            z + t • (d₁ + d₂) := by
        rw [show (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) by norm_num]
        calc
          (1 / 2 : ℝ) • (z + (2 * t) • d₁) + (1 / 2 : ℝ) • (z + (2 * t) • d₂)
              = (1 / 2 : ℝ) • z + t • d₁ + ((1 / 2 : ℝ) • z + t • d₂) := by
                  simp [smul_add, smul_smul, mul_comm, mul_left_comm, mul_assoc]
          _ = ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • z) + (t • d₁ + t • d₂) := by
                abel_nf
          _ = z + (t • d₁ + t • d₂) := by
                rw [← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
          _ = z + t • (d₁ + d₂) := by rw [smul_add]
      have hsec_eq :
          sec (d₁ + d₂) t = (f (z + t • (d₁ + d₂)) - f z) / t := by
        simp [sec, slope_def_field]
      have hsec2_eq₁ :
          sec d₁ (2 * t) = (f (z + (2 * t) • d₁) - f z) / (2 * t) := by
        simp [sec, slope_def_field]
      have hsec2_eq₂ :
          sec d₂ (2 * t) = (f (z + (2 * t) • d₂) - f z) / (2 * t) := by
        simp [sec, slope_def_field]
      rw [hmid] at hmid_nonneg
      rw [hsec_eq, hsec2_eq₁, hsec2_eq₂]
      have hnum :
          f (z + t • (d₁ + d₂)) - f z ≤
            ((f (z + (2 * t) • d₁) - f z) + (f (z + (2 * t) • d₂) - f z)) / 2 := by
        nlinarith
      have hscaled :
          (f (z + t • (d₁ + d₂)) - f z) / t ≤
            (f (z + (2 * t) • d₁) - f z) / (2 * t) +
              (f (z + (2 * t) • d₂) - f z) / (2 * t) := by
        have hscaled_num :
            2 * (f (z + t • (d₁ + d₂)) - f z) ≤
              (f (z + (2 * t) • d₁) - f z) + (f (z + (2 * t) • d₂) - f z) := by
          nlinarith [hnum]
        have hdiv :=
          div_le_div_of_nonneg_right hscaled_num (show 0 ≤ 2 * t by positivity)
        convert hdiv using 1 <;> field_simp [ht_pos.ne', ht2_ne] <;> ring
      exact hscaled
    exact le_of_tendsto_of_tendsto (hsec_tendsto (d₁ + d₂)) (hsec2_1.add hsec2_2) hpoint
  have hadd : ∀ d₁ d₂ : E, D (d₁ + d₂) = D d₁ + D d₂ := by
    intro d₁ d₂
    refine le_antisymm (hsubadd d₁ d₂) ?_
    have hneg_sub : D (-(d₁ + d₂)) ≤ D (-d₁) + D (-d₂) := by
      simpa [add_comm] using hsubadd (-d₁) (-d₂)
    rw [hodd (d₁ + d₂), hodd d₁, hodd d₂] at hneg_sub
    linarith
  let ellLin : E →ₗ[ℝ] ℝ :=
    { toFun := D
      map_add' := hadd
      map_smul' := hsmul }
  let ell : E →L[ℝ] ℝ := ⟨ellLin, ellLin.continuous_of_finiteDimensional⟩
  refine ⟨ell, ?_⟩
  intro d
  have hline :=
    segment_tangent_error_bounds_of_convexCombinationQuadraticBound
      (f := f) (p := p) (L := L) h7 (z := z) (d := d)
  have hnonneg :
      0 ≤ f (z + d) - f z - ell d := by
    simpa [ell, ellLin, D] using hline.1
  have hupper :
      f (z + d) - f z - ell d ≤ ((L : ℝ) / 2) * (p d) ^ (2 : ℕ) := by
    simpa [ell, ellLin, D] using hline.2
  refine ⟨by rfl, ?_⟩
  rw [abs_of_nonneg hnonneg]
  exact hupper

-- TODO: package the fixed-base affine model coming from
-- `rightDirectionalDerivativeLinearMapOfConvexCombinationQuadraticBound` through the Chapter 1
-- quadratic-affine bridge, then discard the auxiliary witness in favor of the canonical gradient.
private lemma hasGradientAt_of_convexCombinationQuadraticBound
    (h7 : smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f)
    (hL : 0 < L) :
    ∀ z : E, HasGradientAt f (∇ f z) z := by
  intro z
  -- Route correction: rather than rebuilding the canonical gradient directly from endpoint
  -- secants, first recover a fixed-base affine model with quadratic remainder and then invoke the
  -- existing affine-approximation theorem.
  obtain ⟨ell, hell⟩ :=
    rightDirectionalDerivativeLinearMapOfConvexCombinationQuadraticBound
      (f := f) (p := p) (L := L) h7 z
  let gz : E := (InnerProductSpace.toDual ℝ E).symm ell
  let g : E → E := fun _ ↦ gz
  have hquad :
      ∀ y : E,
        |f y - affineModelAt f g z y| ≤
          ((L : ℝ) / 2) * (p (y - z)) ^ (2 : ℕ) := by
    intro y
    let d : E := y - z
    obtain ⟨hdEll, hdBound⟩ := hell d
    have hRiesz : inner ℝ gz d = ell d := by
      simpa [gz] using
        (InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := gz) (y := ell))
    -- Rewrite the recovered linear functional back into the ambient affine model at `z`.
    have hmodel :
        f y - affineModelAt f g z y = f y - f z - ell (y - z) := by
      rw [affineModelAt_apply, hRiesz]
      ring
    rw [hmodel]
    simpa [d] using hdBound
  have hgradAux : HasGradientAt f gz z := by
    refine hasGradientAt_of_pointwiseAffineModelSeminormSqBound
      (p := p) (f := f) (g := g) (x := z) (K := L) ?_
    simpa [g] using hquad
  have _ := hL
  -- Once one genuine ambient gradient witness exists, the totalized gradient agrees with it.
  exact hgradAux.differentiableAt.hasGradientAt

/-- Helper for Theorem 2.5: the witness-bundled `(2.1.13)` clause recovers the gradient quadratic
lower bound `(2.1.10)` by the scalar endpoint limit `α → 1` along the segment from `x` to `y`.
-/
private lemma gradient_quadratic_lower_bound_of_convexCombinationGradientBound
    (h6 : (∀ z : E, HasGradientAt f (∇ f z) z) ∧
      smoothConvexConvexCombinationGradientBoundOn p L (∇ f) Set.univ f)
    (hL : 0 < L) :
    smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f := by
  exact gradient_quadratic_lower_bound_of_convexCombinationGradientBound_of_hasGradientAt
    h6.2 h6.1 hL

/-- Helper for Theorem 2.5: the convex-combination quadratic bound `(2.1.14)` recovers the
tangent-error bounds `(2.1.9)` by the same scalar endpoint limit `α → 1` on the line segment from
`x` to `y`. -/
private lemma tangent_error_bounds_of_convexCombinationQuadraticBound
    (h7 : smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f)
    (hL : 0 < L) :
    smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f := by
  have hconv : ConvexOn ℝ Set.univ f :=
    convexOn_univ_of_convexCombinationQuadraticBound h7
  have hgrad : ∀ z : E, HasGradientAt f (∇ f z) z :=
    hasGradientAt_of_convexCombinationQuadraticBound h7 hL
  have _ := hconv
  exact tangent_error_bounds_of_convexCombinationQuadraticBound_of_hasGradientAt
    h7 hgrad

/-- Helper for Theorem 2.5: the witness-bundled `(2.1.12)` clause recovers the tangent-error
bounds `(2.1.9)` by integrating the gradient pairing estimate along the segment from `x` to `y`.
-/
private lemma tangent_error_bounds_of_monotoneGradientBounds
    (h5 : smoothConvexMonotoneGradientBoundsWithGradientOn p L Set.univ f) :
    smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f := by
  exact tangent_error_bounds_of_witnessedMonotoneGradientBounds h5

private abbrev cond2_1_9
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (f : E → ℝ) : Prop :=
  (∀ x : E, HasGradientAt f (∇ f x) x) ∧
    smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f

private abbrev cond2_1_10
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (f : E → ℝ) : Prop :=
  (∀ x : E, HasGradientAt f (∇ f x) x) ∧
    smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f

private abbrev cond2_1_11
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (f : E → ℝ) : Prop :=
  (∀ x : E, HasGradientAt f (∇ f x) x) ∧
    smoothConvexCocoerciveGradientOn p L (∇ f) Set.univ

private abbrev cond2_1_13
    (p : Seminorm ℝ E) [Seminorm.IsNorm p] (L : NNReal) (f : E → ℝ) : Prop :=
  (∀ x : E, HasGradientAt f (∇ f x) x) ∧
    smoothConvexConvexCombinationGradientBoundOn p L (∇ f) Set.univ f

/-- Theorem 2.5: for a positive smoothness constant `L`, membership in `𝓕[L, p]¹¹` is equivalent
to each of the six standard smooth convex inequalities `(2.1.9)` through `(2.1.14)`. In Lean,
every clause that mentions `∇ f` is bundled with the witness that `∇ f x` is the genuine ambient
gradient of `f` at `x`, avoiding the totalized fallback behavior of `gradient`. The textbook
Euclidean theorem is the finite-dimensional specialization. -/
-- Proof sketch: derive `(2.1.9)` from the gradient Lipschitz bound by integrating the derivative
-- of `τ ↦ f (x + τ • (y - x))` along the segment from `x` to `y`; obtain `(2.1.10)` by applying
-- `(2.1.9)` to the translated function `y ↦ f y - ⟪∇ f x, y⟫`; deduce `(2.1.11)` by adding the
-- two copies of `(2.1.10)` with `(x, y)` interchanged; derive `(2.1.12)` from `(2.1.9)` and the
-- dual-norm Lipschitz bound; and pass between `(2.1.10)`, `(2.1.13)`, `(2.1.14)`, and `(2.1.9)`
-- by applying the two-point inequalities at the convex-combination point and taking the limit
-- `α → 1`.
theorem convexC1SeminormSmooth_tfae
    (p : Seminorm ℝ E) [Seminorm.IsNorm p]
    {L : NNReal} (hL : 0 < L) (f : E → ℝ) :
    List.TFAE
      [ f ∈ 𝓕[L, p]¹¹
      , cond2_1_9 p L f
      , cond2_1_10 p L f
      , cond2_1_11 p L f
      , smoothConvexMonotoneGradientBoundsWithGradientOn p L Set.univ f
      , cond2_1_13 p L f
      , smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f ] := by
  tfae_have 1 ↔ 2 := by
    constructor
    · intro hf
      -- The owner packages the ambient gradient witness, and the upper tangent-error estimate is
      -- the already-proved owner consequence on `Set.univ`.
      refine ⟨fun x ↦ hf.hasGradientAt x, ?_⟩
      intro x hx y hy
      have hlower :=
        hf.convexOn.lower_tangent_plane
          x hx (hf.hasGradientAt x).differentiableAt.differentiableWithinAt y hy
      have hlower' :
          0 ≤ f y - f x - inner ℝ (∇ f x) (y - x) := by
        have hgradWithin_eq : gradientWithin f Set.univ x = ∇ f x := by
          simp [gradientWithin, gradient, fderivWithin_univ]
        rw [hgradWithin_eq] at hlower
        linarith
      exact ⟨hlower', tangent_error_upperBound hf.toOn hx hy⟩
    · intro h1
      -- Route correction: the reverse owner implication now uses the reconstructed owner lemma
      -- from the tangent-error package instead of reproving regularity inside the TFAE proof.
      exact mem_F11_of_tangent_error_bounds h1.2 hL
  tfae_have 2 → 3 := by
    intro h1
    exact ⟨h1.1, gradient_quadratic_lower_bound_of_tangent_error_bounds h1.2 hL⟩
  tfae_have 3 → 4 := by
    intro h2
    exact ⟨h2.1, cocoerciveGradient_of_gradient_quadratic_lower_bound h2.2 hL⟩
  tfae_have 4 → 5 := by
    intro h3
    exact ⟨fun x _ ↦ h3.1 x, monotoneGradientBounds_of_cocoerciveGradient h3.2 hL⟩
  tfae_have 5 → 2 := by
    intro h5
    exact ⟨fun x ↦ h5.1 (by simp), tangent_error_bounds_of_monotoneGradientBounds h5⟩
  tfae_have 3 → 6 := by
    intro h2
    exact ⟨h2.1, convexCombinationGradientBound_of_gradient_quadratic_lower_bound h2.2 hL⟩
  tfae_have 6 → 3 := by
    intro h6
    exact ⟨h6.1, gradient_quadratic_lower_bound_of_convexCombinationGradientBound h6 hL⟩
  tfae_have 2 → 7 := by
    intro h1
    exact convexCombinationQuadraticBound_of_tangent_error_bounds h1.2
  tfae_have 7 → 2 := by
    intro h7
    exact ⟨hasGradientAt_of_convexCombinationQuadraticBound h7 hL,
      tangent_error_bounds_of_convexCombinationQuadraticBound h7 hL⟩
  tfae_finish

/-- A named consequence of the previous theorem: membership in `𝓕[L, p]¹¹` yields the gradient
quadratic lower bound `(2.1.10)`. -/
theorem ConvexC1SeminormSmooth.gradientQuadraticLowerBound
    (hf : ConvexC1SeminormSmooth p L f) (hL : 0 < L) :
    smoothConvexGradientQuadraticLowerBoundOn p L (∇ f) Set.univ f := by
  have h1 : smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f := by
    intro x hx y hy
    have hlower :=
      hf.convexOn.lower_tangent_plane
        x hx (hf.hasGradientAt x).differentiableAt.differentiableWithinAt y hy
    have hgradWithin_eq : gradientWithin f Set.univ x = ∇ f x := by
      simp [gradientWithin, gradient, fderivWithin_univ]
    rw [hgradWithin_eq] at hlower
    refine ⟨?_, tangent_error_upperBound hf.toOn hx hy⟩
    linarith
  exact gradient_quadratic_lower_bound_of_tangent_error_bounds h1 hL

/-- A named consequence of the previous theorem: membership in `𝓕[L, p]¹¹` yields the
cocoercivity inequality `(2.1.11)`. -/
theorem ConvexC1SeminormSmooth.cocoerciveGradient
    (hf : ConvexC1SeminormSmooth p L f) (hL : 0 < L) :
    smoothConvexCocoerciveGradientOn p L (∇ f) Set.univ := by
  have h1 : smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f := by
    intro x hx y hy
    have hlower :=
      hf.convexOn.lower_tangent_plane
        x hx (hf.hasGradientAt x).differentiableAt.differentiableWithinAt y hy
    have hgradWithin_eq : gradientWithin f Set.univ x = ∇ f x := by
      simp [gradientWithin, gradient, fderivWithin_univ]
    rw [hgradWithin_eq] at hlower
    refine ⟨?_, tangent_error_upperBound hf.toOn hx hy⟩
    linarith
  exact cocoerciveGradient_of_gradient_quadratic_lower_bound
    (gradient_quadratic_lower_bound_of_tangent_error_bounds h1 hL) hL

/-- A named consequence of the previous theorem: membership in `𝓕[L, p]¹¹` yields the
convex-combination gradient bound `(2.1.13)`. -/
theorem ConvexC1SeminormSmooth.convexCombinationGradientBound
    (hf : ConvexC1SeminormSmooth p L f) (hL : 0 < L) :
    smoothConvexConvexCombinationGradientBoundOn p L (∇ f) Set.univ f := by
  have h1 : smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f := by
    intro x hx y hy
    have hlower :=
      hf.convexOn.lower_tangent_plane
        x hx (hf.hasGradientAt x).differentiableAt.differentiableWithinAt y hy
    have hgradWithin_eq : gradientWithin f Set.univ x = ∇ f x := by
      simp [gradientWithin, gradient, fderivWithin_univ]
    rw [hgradWithin_eq] at hlower
    refine ⟨?_, tangent_error_upperBound hf.toOn hx hy⟩
    linarith
  exact convexCombinationGradientBound_of_gradient_quadratic_lower_bound
    (gradient_quadratic_lower_bound_of_tangent_error_bounds h1 hL) hL

/-- On an arbitrary set `Q`, membership in `𝓕[L, p]¹¹(Q)` implies the tangent error bounds
`(2.1.9)` for all pairs of points in `Q`. -/
-- Proof sketch: localize the proof of `(2.1.9)` from the whole-space case to the segment joining
-- `x` and `y`, using only the ambient-gradient Lipschitz bound and first-order convexity on
-- `Q`.
theorem ConvexC1SeminormSmoothOn.tangentErrorBounds
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    smoothConvexTangentErrorBoundsOn p L (∇ f) Q f := by
  intro x hx y hy
  -- The lower bound is the usual supporting-nesterovHyperplane inequality from convexity.
  have hgradWithin : HasGradientWithinAt f (∇ f x) Q x := by
    simpa using (hf.hasGradientAt hx).hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt
  have hlower :=
    hf.convexOn.lower_tangent_plane_of_hasGradientWithinAt
      x hx (∇ f x) hgradWithin y hy
  -- The upper bound is obtained by integrating the corrected segment remainder.
  refine ⟨?_, tangent_error_upperBound hf hx hy⟩
  linarith

/-- On an arbitrary set `Q`, membership in `𝓕[L, p]¹¹(Q)` implies the monotonicity and upper
bound `(2.1.12)` for the ambient-gradient pairing on `Q`, together with the witness that the
ambient field `∇ f` is the genuine gradient of `f` at every feasible point. -/
-- Proof sketch: combine the first-order convexity inequality from `ConvexC1On Q f` with the
-- ambient-gradient Lipschitz bound measured by `‖·‖[p,*]` and apply the dual
-- Cauchy--Schwarz estimate.
theorem ConvexC1SeminormSmoothOn.monotoneGradientBounds
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    smoothConvexMonotoneGradientBoundsWithGradientOn p L Q f := by
  refine ⟨?_, ?_⟩
  · -- The bundled statement keeps the ambient gradient witness unchanged.
    intro x hx
    exact hf.hasGradientAt hx
  · refine ⟨?_, ?_⟩
    · intro x hx y hy
      -- Add the two supporting-nesterovHyperplane inequalities to get monotonicity of the gradient
      -- pairing.
      have hgradWithinX : HasGradientWithinAt f (∇ f x) Q x := by
        simpa using (hf.hasGradientAt hx).hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt
      have hgradWithinY : HasGradientWithinAt f (∇ f y) Q y := by
        simpa using (hf.hasGradientAt hy).hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt
      have hxy :=
        hf.convexOn.lower_tangent_plane_of_hasGradientWithinAt
          x hx (∇ f x) hgradWithinX y hy
      have hyx :=
        hf.convexOn.lower_tangent_plane_of_hasGradientWithinAt
          y hy (∇ f y) hgradWithinY x hx
      have hlin :
          inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y) =
            -inner ℝ (∇ f x - ∇ f y) (x - y) := by
        calc
          inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y)
              = -inner ℝ (∇ f x) (x - y) + inner ℝ (∇ f y) (x - y) := by
                  rw [show y - x = -(x - y) by abel, inner_neg_right]
          _ = -inner ℝ (∇ f x - ∇ f y) (x - y) := by
                rw [inner_sub_left]
                ring
      linarith [hxy, hyx, hlin]
    · intro x hx y hy
      -- Dual Cauchy together with the defining dual-norm Lipschitz estimate yields the upper
      -- quadratic pairing bound.
      have hLip := hf.dualNorm_gradient_sub_le hx hy
      have hinner :
          inner ℝ (∇ f x - ∇ f y) (x - y) ≤
            ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
        Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
      have hp_nonneg : 0 ≤ p (x - y) := apply_nonneg p (x - y)
      calc
        inner ℝ (∇ f x - ∇ f y) (x - y) ≤
            ‖∇ f x - ∇ f y‖[p,*] * p (x - y) := hinner
        _ ≤ ((L : ℝ) * p (x - y)) * p (x - y) := by
              exact mul_le_mul_of_nonneg_right hLip hp_nonneg
        _ = (L : ℝ) * (p (x - y)) ^ (2 : ℕ) := by
              ring

/-- On an arbitrary set `Q`, membership in `𝓕[L, p]¹¹(Q)` implies the Jensen gap bounds
`(2.1.14)` for all pairs of points in `Q`. -/
-- Proof sketch: apply the tangent error bounds at the convex-combination point to both endpoints,
-- weight the resulting inequalities by `α` and `1 - α`, and add them.
theorem ConvexC1SeminormSmoothOn.convexCombinationQuadraticBound
    (hf : ConvexC1SeminormSmoothOn p L Q f) :
    smoothConvexConvexCombinationQuadraticBoundOn p L Q f := by
  intro x hx y hy α hα
  let z : E := α • x + (1 - α) • y
  have hz : z ∈ Q := hf.convex hx hy hα.1 (sub_nonneg.mpr hα.2) (by ring)
  have hx_bound :
      0 ≤ f x - f z - inner ℝ (∇ f z) (x - z) ∧
        f x - f z - inner ℝ (∇ f z) (x - z) ≤
          ((L : ℝ) / 2) * (p (z - x)) ^ (2 : ℕ) :=
    hf.tangentErrorBounds hz hx
  have hy_bound :
      0 ≤ f y - f z - inner ℝ (∇ f z) (y - z) ∧
        f y - f z - inner ℝ (∇ f z) (y - z) ≤
          ((L : ℝ) / 2) * (p (z - y)) ^ (2 : ℕ) :=
    hf.tangentErrorBounds hz hy
  have hz_line : z = AffineMap.lineMap y x α := by
    simp [z, AffineMap.lineMap_apply_module, add_comm]
  have hz_sub_x : z - x = (1 - α) • (y - x) := by
    simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_right y x α
  have hz_sub_y : z - y = α • (x - y) := by
    simpa [hz_line, vsub_eq_sub] using AffineMap.lineMap_vsub_left y x α
  have hp_sub : p (y - x) = p (x - y) := by
    simpa [neg_sub] using (map_neg_eq_map p (x - y))
  have hx_disp : x - z = (1 - α) • (x - y) := by
    calc
      x - z = -((z - x)) := by abel
      _ = -((1 - α) • (y - x)) := by rw [hz_sub_x]
      _ = (1 - α) • (x - y) := by simp [smul_neg, sub_eq_add_neg]
  have hy_disp : y - z = α • (y - x) := by
    calc
      y - z = -(z - y) := by abel
      _ = -(α • (x - y)) := by rw [hz_sub_y]
      _ = α • (y - x) := by simp [smul_neg, sub_eq_add_neg]
  have hcancel_vec : α • (x - z) + (1 - α) • (y - z) = 0 := by
    rw [hx_disp, hy_disp]
    rw [show y - x = -(x - y) by abel]
    rw [smul_smul, smul_smul, smul_neg]
    calc
      (α * (1 - α)) • (x - y) + -(((1 - α) * α) • (x - y)) =
          ((α * (1 - α)) - ((1 - α) * α)) • (x - y) := by
            rw [← sub_eq_add_neg, sub_smul]
      _ = 0 := by
            have hcoeff : α * (1 - α) - ((1 - α) * α) = 0 := by ring
            simp [hcoeff]
  have hcancel :
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) = 0 := by
    calc
      α * inner ℝ (∇ f z) (x - z) + (1 - α) * inner ℝ (∇ f z) (y - z) =
          inner ℝ (∇ f z) (α • (x - z) + (1 - α) • (y - z)) := by
            rw [inner_add_right, inner_smul_right, inner_smul_right]
      _ = 0 := by simp [hcancel_vec]
  have hgap_eq :
      α * f x + (1 - α) * f y - f z =
        α * (f x - f z - inner ℝ (∇ f z) (x - z)) +
          (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := by
    linarith
  have hx_scaled :
      α * (f x - f z - inner ℝ (∇ f z) (x - z)) ≤
        α * (((L : ℝ) / 2) * (p (z - x)) ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hx_bound.2 hα.1
  have hy_scaled :
      (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) ≤
        (1 - α) * (((L : ℝ) / 2) * (p (z - y)) ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hy_bound.2 (sub_nonneg.mpr hα.2)
  have hupper :
      α * f x + (1 - α) * f y - f z ≤
        α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by
    have hsum := add_le_add hx_scaled hy_scaled
    calc
      α * f x + (1 - α) * f y - f z
          = α * (f x - f z - inner ℝ (∇ f z) (x - z)) +
              (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := hgap_eq
      _ ≤ α * (((L : ℝ) / 2) * (p (z - x)) ^ (2 : ℕ)) +
            (1 - α) * (((L : ℝ) / 2) * (p (z - y)) ^ (2 : ℕ)) := hsum
      _ = α * (1 - α) * ((L : ℝ) / 2) * (p (x - y)) ^ (2 : ℕ) := by
            rw [hz_sub_x, hz_sub_y]
            simp [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg hα.1,
              hp_sub,
              abs_of_nonneg (sub_nonneg.mpr hα.2)]
            ring
  have hx_nonneg :
      0 ≤ α * (f x - f z - inner ℝ (∇ f z) (x - z)) := by
    exact mul_nonneg hα.1 hx_bound.1
  have hy_nonneg :
      0 ≤ (1 - α) * (f y - f z - inner ℝ (∇ f z) (y - z)) := by
    exact mul_nonneg (sub_nonneg.mpr hα.2) hy_bound.1
  have hnonneg :
      0 ≤ α * f x + (1 - α) * f y - f z := by
    rw [hgap_eq]
    exact add_nonneg hx_nonneg hy_nonneg
  exact ⟨hnonneg, by simpa [z] using hupper⟩

/-- The tangent-error bounds `(2.1.9)` for a smooth convex objective are the `Q = Set.univ`
specialization of `ConvexC1SeminormSmoothOn.tangentErrorBounds`. -/
theorem ConvexC1SeminormSmooth.tangentErrorBounds
    (hf : ConvexC1SeminormSmooth p L f) :
    smoothConvexTangentErrorBoundsOn p L (∇ f) Set.univ f :=
  hf.toOn.tangentErrorBounds

/-- The monotone-gradient bounds `(2.1.12)` for a smooth convex objective are the
`Q = Set.univ` specialization of `ConvexC1SeminormSmoothOn.monotoneGradientBounds`, bundled with
the pointwise ambient-gradient witnesses. -/
theorem ConvexC1SeminormSmooth.monotoneGradientBounds
    (hf : ConvexC1SeminormSmooth p L f) :
    smoothConvexMonotoneGradientBoundsWithGradientOn p L Set.univ f :=
  hf.toOn.monotoneGradientBounds

/-- The convex-combination quadratic bounds `(2.1.14)` for a smooth convex objective are the
`Q = Set.univ` specialization of
`ConvexC1SeminormSmoothOn.convexCombinationQuadraticBound`. -/
theorem ConvexC1SeminormSmooth.convexCombinationQuadraticBound
    (hf : ConvexC1SeminormSmooth p L f) :
    smoothConvexConvexCombinationQuadraticBoundOn p L Set.univ f :=
  hf.toOn.convexCombinationQuadraticBound

end
