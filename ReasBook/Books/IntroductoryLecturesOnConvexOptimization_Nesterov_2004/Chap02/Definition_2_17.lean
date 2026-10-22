/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A function on a real Hilbert space belongs to the strongly convex smooth class with
parameters `μ` and `L` when it is `C¹`, `μ`-strongly convex on the whole space, and has
`L`-Lipschitz gradient. Chapter 2 specializes this owner predicate to `ℝⁿ`, but the same
mathematics applies unchanged to `ℓ²(ℕ, ℝ)` and other real Hilbert spaces. -/
def IsStrongConvexSmoothObjective (μ L : ℝ) (f : E → ℝ) : Prop :=
  0 < μ ∧
    ContDiff ℝ 1 f ∧
    StrongConvexOn Set.univ μ f ∧
    ∀ x y : E, ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖

scoped[StrongConvexSmooth] notation "𝓢[" μ ", " L "]¹¹" =>
  setOf (IsStrongConvexSmoothObjective μ L)

scoped[StrongConvexSmooth] notation "q[" μ ", " L "]" => (μ / L : ℝ)

open scoped StrongConvexSmooth

/-- The whole-space notation `𝓢[μ, L]¹¹` is the source-facing set view of the owner predicate
`IsStrongConvexSmoothObjective μ L`. -/
theorem mem_S11_iff {μ L : ℝ} {f : E → ℝ} :
    f ∈ 𝓢[μ, L]¹¹ ↔ IsStrongConvexSmoothObjective μ L f :=
  Iff.rfl

namespace IsStrongConvexSmoothObjective

/-- Membership in the strongly convex smooth class forces the strong-convexity parameter to be
positive. -/
theorem mu_pos {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f) :
    0 < μ :=
  hf.1

/-- Membership in the strongly convex smooth class includes `C^1` regularity. -/
theorem contDiff {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f) :
    ContDiff ℝ 1 f :=
  hf.2.1

/-- Membership in the strongly convex smooth class includes strong convexity on the whole space. -/
theorem strongConvexOn {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f) :
    StrongConvexOn Set.univ μ f :=
  hf.2.2.1

/-- A strongly convex smooth objective is strictly convex on the whole ambient space. -/
theorem strictConvexOn {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f) :
    StrictConvexOn ℝ Set.univ f :=
  hf.strongConvexOn.strictConvexOn hf.mu_pos

/-- Membership in the strongly convex smooth class includes the gradient-Lipschitz bound with
constant `L`. -/
theorem gradient_lipschitz {μ L : ℝ} {f : E → ℝ}
    (hf : IsStrongConvexSmoothObjective μ L f) (x y : E) :
    ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖ :=
  hf.2.2.2 x y

/-- Translating the ambient coordinates of a strongly convex smooth objective preserves
membership in the same owner class. -/
-- Proof sketch: precompose `f` with the affine translation `x ↦ x - x₀`; translation preserves
-- `C¹` regularity, whole-space strong convexity, and the gradient-Lipschitz constant.
theorem translate {μ L : ℝ} {f : E → ℝ}
    (hf : IsStrongConvexSmoothObjective μ L f) (x0 : E) :
    IsStrongConvexSmoothObjective μ L (fun x ↦ f (x - x0)) := by
  refine ⟨hf.mu_pos, ?_, ?_, ?_⟩
  · -- Compose the `C¹` objective with the ambient translation map.
    have htranslate : ContDiff ℝ 1 (fun x : E ↦ x - x0) := by
      simpa [sub_eq_add_neg] using
        contDiff_id.add (contDiff_const : ContDiff ℝ 1 fun _ : E ↦ -x0)
    simpa [Function.comp_def] using hf.contDiff.comp htranslate
  · -- Whole-space strong convexity is preserved by translating the argument.
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    let u := x - x0
    let v := y - x0
    have h :
        f (a • u + b • v) ≤
          a * f u + b * f v - a * b * ((μ / 2) * ‖u - v‖ ^ (2 : ℕ)) :=
      hf.strongConvexOn.2 (by simp [u]) (by simp [v]) ha hb hab
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
  · intro x y
    have hx : HasGradientAt f (∇ f (x - x0)) (x - x0) :=
      hf.contDiff.differentiable_one (x - x0) |>.hasGradientAt
    have hy : HasGradientAt f (∇ f (y - x0)) (y - x0) :=
      hf.contDiff.differentiable_one (y - x0) |>.hasGradientAt
    have hsubx : HasFDerivAt (fun z : E ↦ z - x0) (ContinuousLinearMap.id ℝ E) x := by
      simpa using (hasFDerivAt_id x).sub_const x0
    have hsuby : HasFDerivAt (fun z : E ↦ z - x0) (ContinuousLinearMap.id ℝ E) y := by
      simpa using (hasFDerivAt_id y).sub_const x0
    have hx_translate :
        HasGradientAt (fun z : E ↦ f (z - x0)) (∇ f (x - x0)) x := by
      simpa [Function.comp_def] using (hx.hasFDerivAt.comp x hsubx).hasGradientAt
    have hy_translate :
        HasGradientAt (fun z : E ↦ f (z - x0)) (∇ f (y - x0)) y := by
      simpa [Function.comp_def] using (hy.hasFDerivAt.comp y hsuby).hasGradientAt
    rw [hx_translate.gradient, hy_translate.gradient]
    simpa [sub_eq_add_neg, sub_add_eq_sub_sub] using
      hf.gradient_lipschitz (x - x0) (y - x0)

/-- Expanding `IsStrongConvexSmoothObjective μ L f` yields the canonical `C¹`-plus-strong-convex
data together with the equivalent whole-space strong gradient-monotonicity formulation. -/
theorem iff_contDiff_and_gradient_strong_mono {μ L : ℝ} {f : E → ℝ} :
    IsStrongConvexSmoothObjective μ L f ↔
      0 < μ ∧
        ContDiff ℝ 1 f ∧
        (∀ x y : E,
          μ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x - ∇ f y) (x - y)) ∧
        ∀ x y : E, ‖∇ f x - ∇ f y‖ ≤ L * ‖x - y‖ := by
  constructor
  · intro hf
    let hf_diff : DifferentiableOn ℝ f (Set.univ : Set E) :=
      (contDiffOn_univ.2 hf.contDiff).differentiableOn (by simp)
    have hstrong :
        StrongConvexOn (Set.univ : Set E) μ f ↔
          ∀ x y : E,
            μ * ‖x - y‖ ^ (2 : ℕ) ≤
              inner ℝ
                (gradientWithin f Set.univ x - gradientWithin f Set.univ y)
                (x - y) := by
      let hstrong' :
          StrongConvexOn (Set.univ : Set E) μ f ↔
            ∀ ⦃x y : E⦄, x ∈ Set.univ → y ∈ Set.univ →
              μ * ‖x - y‖ ^ (2 : ℕ) ≤
                inner ℝ
                  (gradientWithin f Set.univ x - gradientWithin f Set.univ y)
                  (x - y) :=
        strongConvexOn_iff_gradient_monotone convex_univ hf_diff
      simpa using hstrong'
    refine ⟨hf.mu_pos, hf.contDiff, ?_, hf.gradient_lipschitz⟩
    simpa [gradientWithin, gradient, fderivWithin_univ] using
      hstrong.mp hf.strongConvexOn
  · rintro ⟨hμ, hf_contDiff, hmono, hf_lip⟩
    let hf_diff : DifferentiableOn ℝ f (Set.univ : Set E) :=
      (contDiffOn_univ.2 hf_contDiff).differentiableOn (by simp)
    have hstrong :
        StrongConvexOn (Set.univ : Set E) μ f ↔
          ∀ x y : E,
            μ * ‖x - y‖ ^ (2 : ℕ) ≤
              inner ℝ
                (gradientWithin f Set.univ x - gradientWithin f Set.univ y)
                (x - y) := by
      let hstrong' :
          StrongConvexOn (Set.univ : Set E) μ f ↔
            ∀ ⦃x y : E⦄, x ∈ Set.univ → y ∈ Set.univ →
              μ * ‖x - y‖ ^ (2 : ℕ) ≤
                inner ℝ
                  (gradientWithin f Set.univ x - gradientWithin f Set.univ y)
                  (x - y) :=
        strongConvexOn_iff_gradient_monotone convex_univ hf_diff
      simpa using hstrong'
    refine ⟨hμ, hf_contDiff, ?_, hf_lip⟩
    exact hstrong.mpr (by simpa [gradientWithin, gradient, fderivWithin_univ] using hmono)

/-- A strongly convex smooth objective has `μ`-strongly monotone gradient on the whole space. -/
theorem gradient_strong_mono {μ L : ℝ} {f : E → ℝ}
    (hf : IsStrongConvexSmoothObjective μ L f) (x y : E) :
    μ * ‖x - y‖ ^ (2 : ℕ) ≤ inner ℝ (∇ f x - ∇ f y) (x - y) :=
  (IsStrongConvexSmoothObjective.iff_contDiff_and_gradient_strong_mono.mp hf).2.2.1 x y

/-- A strongly convex smooth objective satisfies the standard quadratic lower tangent bound on the
whole space. -/
-- Proof sketch: apply the whole-space strong-convexity tangent inequality at the base point `x`.
theorem lower_tangent_quadratic {μ L : ℝ} {f : E → ℝ}
    (hf : IsStrongConvexSmoothObjective μ L f) (x y : E) :
    f y ≥ f x + inner ℝ (∇ f x) (y - x) + (μ / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  have hgrad : HasGradientAt f (∇ f x) x :=
    hf.contDiff.differentiable_one x |>.hasGradientAt
  simpa using
    StrongConvexOn.lower_tangent_quadratic_of_hasGradientAt
      hf.strongConvexOn (by simp) (by simp) hgrad

/-- On a nontrivial real Hilbert space, the strong-convexity parameter of a strongly convex smooth
objective cannot exceed the gradient-Lipschitz constant. -/
-- Proof sketch: add the lower tangent inequalities at `x, y` and `y, x` to obtain strong
-- monotonicity of the gradient, then bound the resulting inner product by Cauchy-Schwarz and the
-- gradient-Lipschitz estimate. Dividing by `‖x - y‖² > 0` gives `μ ≤ L`.
theorem mu_le_L {μ L : ℝ} {f : E → ℝ} [Nontrivial E]
    (hf : IsStrongConvexSmoothObjective μ L f) :
    μ ≤ L := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne E
  have hmono := hf.gradient_strong_mono x y
  have hupper :
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤ L * ‖x - y‖ ^ (2 : ℕ) := by
    calc
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤ ‖∇ f x - ∇ f y‖ * ‖x - y‖ := by
        exact real_inner_le_norm _ _
      _ ≤ (L * ‖x - y‖) * ‖x - y‖ := by
        exact mul_le_mul_of_nonneg_right (hf.gradient_lipschitz x y) (norm_nonneg _)
      _ = L * ‖x - y‖ ^ (2 : ℕ) := by
        ring
  have hnormsq_pos : 0 < ‖x - y‖ ^ (2 : ℕ) := by
    exact pow_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) 2
  exact le_of_mul_le_mul_right (le_trans hmono hupper) hnormsq_pos

/-- A strongly convex smooth objective satisfies the standard quadratic upper tangent bound on the
whole space. -/
-- Proof sketch: combine `C¹` regularity and the gradient-Lipschitz bound to control the tangent
-- error by `(L / 2) * ‖y - x‖²`.
theorem upper_tangent_quadratic {μ L : ℝ} {f : E → ℝ}
    (hf : IsStrongConvexSmoothObjective μ L f) (x y : E) :
    f y ≤ f x + inner ℝ (∇ f x) (y - x) + (L / 2) * ‖y - x‖ ^ (2 : ℕ) := by
  by_cases hE : Subsingleton E
  · have hxy : x = y := hE.elim x y
    subst hxy
    simp
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hL : 0 ≤ L := le_trans hf.mu_pos.le hf.mu_le_L
    have hgrad : LipschitzWith (Real.toNNReal L) (∇ f) := by
      refine LipschitzWith.of_dist_le_mul ?_
      intro x' y'
      have hdist :
          ‖∇ f x' - ∇ f y'‖ ≤ L * ‖x' - y'‖ :=
        hf.gradient_lipschitz x' y'
      have hL' : L ≤ (Real.toNNReal L : ℝ) := by
        simp [Real.toNNReal_of_nonneg hL]
      simpa [dist_eq_norm] using
        le_trans hdist (mul_le_mul_of_nonneg_right hL' (norm_nonneg _))
    have hupper :=
      taylor_upper_bound_of_contDiffOne_withLipschitzGradient
        hf.contDiff hgrad x y
    simpa [firstOrderTaylorModelAt_apply, Real.toNNReal_of_nonneg hL] using hupper

/-- A global minimizer of a strongly convex smooth objective is stationary. -/
theorem gradient_eq_zero_of_isMinOn
    {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar) :
    ∇ f xStar = 0 := by
  exact
    (isMinOn_hasGradientAt_zero_of_differentiableAt
      (hf.contDiff.differentiable_one xStar) hxStar).gradient

/-- A stationary point of a strongly convex smooth objective is a global minimizer. -/
theorem isMinOn_of_gradient_eq_zero
    {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f)
    (xStar : E) (hgrad : ∇ f xStar = 0) :
    IsMinOn f Set.univ xStar := by
  rw [isMinOn_univ_iff]
  intro x
  have hbound : f x ≥ f xStar + (μ / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    simpa [hgrad] using hf.lower_tangent_quadratic xStar x
  have hnormsq : 0 ≤ ‖x - xStar‖ ^ (2 : ℕ) := by positivity
  nlinarith [hf.mu_pos, hnormsq, hbound]

/-- For a strongly convex smooth objective on a real Hilbert space, global minimizers are exactly
the stationary points. -/
theorem isMinOn_iff_gradient_eq_zero
    {μ L : ℝ} {f : E → ℝ} (hf : IsStrongConvexSmoothObjective μ L f)
    (xStar : E) :
    IsMinOn f Set.univ xStar ↔ ∇ f xStar = 0 :=
  ⟨hf.gradient_eq_zero_of_isMinOn, hf.isMinOn_of_gradient_eq_zero xStar⟩

end IsStrongConvexSmoothObjective

section ApproximateSolution

variable {μ L : ℝ}

/- Definition 2.17 next adds the textbook approximate-solution clause relative to a chosen
minimizer `xStar`. The objective-side owner `IsStrongConvexSmoothObjective μ L` already lives on
the intrinsic real-Hilbert-space ambient type `E`, and the approximate-solution data below use
only that same ambient owner `SetConstrainedMinimizationProblem.unconstrained f` together with the
squared-distance bound to `xStar`. The textbook `ℝⁿ` statement is therefore recovered by
specializing `E = EuclideanSpace ℝ (Fin n)`, rather than by keeping a separate Euclidean owner.

Source/core/bridge triage:
* source-facing: an objective `f : E → ℝ` in `𝓢^{1,1}_{μ,L}` together with a minimizing point
  `xStar`;
* core/canonical: the Chapter 1 owner `SetConstrainedMinimizationProblem E`, specialized to
  feasible set `Set.univ`, and the minimizer predicate `IsMinOn f Set.univ xStar`;
* bridge/view: the ambient owner problem `SetConstrainedMinimizationProblem.unconstrained f`, the
  Chapter 1 derived notions of optimal value and approximate minimizer for that owner problem, and
  the local value-gradient map `x ↦ (f x, ∇ f x)`.

Primitive data:
* the objective `f : E → ℝ`;
* the owner objective hypothesis `hf : IsStrongConvexSmoothObjective μ L f`;
* a minimizing point `xStar : E` with `hxStar : IsMinOn f Set.univ xStar`.

Derived API:
* strict convexity and hence uniqueness of minimizers, via `hf.strictConvexOn`;
* the whole-space lower and upper quadratic tangent bounds, via
  `hf.lower_tangent_quadratic` and `hf.upper_tangent_quadratic`;
* the ambient owner problem on `Set.univ`;
* optimal values, approximate minimizers, and first-order locality statements, all taken directly
  from the Chapter 1 owner problem and the value-gradient map rather than from a parallel wrapper.

No separate public `StrongConvexSmoothMinimizationProblem`, local `optimalValue`, or first-order
data wrapper is introduced here. The source-facing approximate-solution predicate below is kept as
a thin bridge over the Chapter 1 approximate-minimizer owner together with the squared-distance
condition from the textbook. -/

variable (f : E → ℝ) (xStar : E)
variable (sameDataNear : (E → ℝ) → (E → ℝ) → E → Prop)

#check f ∈ 𝓢[μ, L]¹¹
#check IsMinOn f Set.univ xStar
#check (SetConstrainedMinimizationProblem.unconstrained f : SetConstrainedMinimizationProblem E)
#check fun x : E ↦ (f x, ∇ f x)
/- The first-order local black-box oracle clause is the Chapter 1 class-level value-gradient
oracle `fun f x ↦ (f x, ∇ f x)` together with its locality predicate. -/
set_option linter.hashCommand false in
#check ((fun f x ↦ (f x, ∇ f x)) : (E → ℝ) → E → ℝ × E)
set_option linter.hashCommand false in
#check OptimizationOracle.IsLocal (fun f x ↦ (f x, ∇ f x)) sameDataNear

/-- Definition 2.17: relative to a chosen minimizer `x*` of an objective in
`𝓢^{1,1}_{μ,L}`, a point `x̄` is an approximate solution with accuracy `ε` when both the
objective gap `f(x̄) - f(x*)` and the squared distance `‖x̄ - x*‖²` are at most `ε`. The
textbook `ℝⁿ` version is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
def IsStrongConvexSmoothApproximateSolution (f : E → ℝ) (xStar : E) (ε : ℝ) (xBar : E) : Prop :=
  f xBar - f xStar ≤ ε ∧ ‖xBar - xStar‖ ^ (2 : ℕ) ≤ ε

section

variable {E : Type*} [NormedAddCommGroup E]

/-- The source-facing Definition 2.17 approximate-solution predicate is the Chapter 1
unconstrained approximate-minimizer predicate together with the extra squared-distance bound to
the chosen minimizer `x*`. No Euclidean coordinates or finite-dimensional structure enter this
owner-level equivalence; those are only a specialization layer for the textbook presentation. -/
-- Proof sketch: rewrite the objective-gap inequality with the canonical upstream bridge
-- `SetConstrainedMinimizationProblem.unconstrained_isApproximateMinimizer_iff_sub_le`, then keep
-- the squared-distance clause unchanged.
theorem isStrongConvexSmoothApproximateSolution_iff_isApproximateMinimizer_and_sqdist_le
    {f : E → ℝ} {xStar xBar : E} (hxStar : IsMinOn f Set.univ xStar) (ε : ℝ) :
    IsStrongConvexSmoothApproximateSolution f xStar ε xBar ↔
      (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar ∧
        ‖xBar - xStar‖ ^ (2 : ℕ) ≤ ε := by
  have happrox_iff :
      (SetConstrainedMinimizationProblem.unconstrained f).IsApproximateMinimizer ε xBar ↔
        f xBar - f xStar ≤ ε := by
    have hoptimalValue :
        (SetConstrainedMinimizationProblem.unconstrained f).optimalValue = (f xStar : EReal) := by
      simpa using
        (SetConstrainedMinimizationProblem.unconstrained f).optimalValue_eq_of_isMinOn
          (by simp) hxStar
    rw [(SetConstrainedMinimizationProblem.unconstrained f).isApproximateMinimizer_iff,
      SetConstrainedMinimizationProblem.unconstrained_feasibleSet, hoptimalValue]
    constructor
    · rintro ⟨_, happrox⟩
      refine sub_le_iff_le_add'.mpr ?_
      have happrox' : ((f xBar : ℝ) : EReal) ≤ ((f xStar + ε : ℝ) : EReal) := by
        simpa [EReal.coe_add] using happrox
      exact EReal.coe_le_coe_iff.mp happrox'
    · intro hgap
      have hgap' : f xBar ≤ f xStar + ε :=
        sub_le_iff_le_add'.mp hgap
      refine ⟨by simp, ?_⟩
      have happrox : ((f xBar : ℝ) : EReal) ≤ ((f xStar + ε : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.mpr hgap'
      simpa [EReal.coe_add] using happrox
  -- Rewrite only the objective-gap clause through the Chapter 1 owner bridge.
  constructor
  · rintro ⟨hgap, hsqdist⟩
    -- Keep the squared-distance bound unchanged while converting the gap inequality.
    refine ⟨?_, hsqdist⟩
    exact happrox_iff.2 hgap
  · rintro ⟨happrox, hsqdist⟩
    -- Convert the approximate-minimizer clause back to the textbook objective-gap form.
    refine ⟨?_, hsqdist⟩
    exact happrox_iff.1 happrox

end

end ApproximateSolution
