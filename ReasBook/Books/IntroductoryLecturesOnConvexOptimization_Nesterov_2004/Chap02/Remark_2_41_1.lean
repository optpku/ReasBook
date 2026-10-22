/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_35
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_41
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_45

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-
Remark 2.41.1 is source-facing in the constrained max-type exact-step domain.

Mandatory domain-style sampling for this refinement:
* `maxTypeAffineApproximation` in `Lemma_2_18`, the owner affine max-type model at `xBar`;
* `quadraticallyRegularizedObjective` in `Definition_1_4_17.lean`, the owner quadratic
  regularization of that model;
* `maxTypeObjective_quadratic_bounds_of_components_mem` in `Lemma_2_18`, the chapter theorem that
  turns componentwise `𝓢^{1,1}` control into a max-type quadratic model inequality;
* `gradientMapping` / `reducedGradient` in `Definition_2_35_1`, the owner source-facing
  projected-gradient pair recovered when there is only one component.

Best owner abstraction:
* the exact-step predicate from `Definition_2_41`,
  `IsMinOn
      (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar)
      Q
      xPlus`.

Primitive data:
* the feasible set `Q`;
* the nonempty finite component family `fi`;
* the base point `xBar`;
* the positive inverse-stepsize / regularization parameter `γ : NNRealˣ`,
  together with the closed / convex / nonempty hypotheses needed for well-definedness.

Derived API:
* the chosen exact step `maxTypeGradientMapping`, i.e. the textbook `x_f(xBar; γ)`, as the
  unique point in the owner `gradientMappingSet` of the regularized max-type model;
* the reduced gradient `maxTypeReducedGradient`, i.e. the textbook `g_f(xBar; γ)`, recovered from
  the owner residual formula `reducedGradientOf`;
* `Fact`-based bridges that keep the source-facing `x_f` / `g_f` surface free of auxiliary
  feasible-set witness arguments;
* the exact-step theorem for `maxTypeGradientMapping`;
* the singleton bridge back to `gradientMapping` and `reducedGradient`.

Source/core/bridge triage:
* source-facing: `maxTypeGradientMapping` and `maxTypeReducedGradient`;
* core/canonical: the exact-step predicate above together with `gradientMappingSet` and
  `reducedGradientOf` from `Definition_2_41`;
* bridge/view: the `m = 1` reduction to `Definition_2_35_1`.

The center `xBar` is ambient data and is not assumed to belong to `Q`, so the max-type step is
not presented as a projection of `xBar` onto `Q`. Only in the singleton case does the model
collapse to the usual quadratically regularized first-order model, recovering the projected-
gradient constructions from `Definition_2_35_1`.
-/

section MaxTypeStep

private theorem quadratic_shift_eq (x xBar : E) (γ : ℝ) :
    (γ / 2) * ‖x - xBar‖ ^ (2 : ℕ) - (γ / 2) * ‖x‖ ^ (2 : ℕ) =
      -γ * inner ℝ x xBar + (γ / 2) * ‖xBar‖ ^ (2 : ℕ) := by
  rw [norm_sub_sq_real]
  ring

private theorem quadratic_shift_affine
    (x y xBar : E) {a b γ : ℝ} (hab : a + b = 1) :
    ((γ / 2) * ‖a • x + b • y - xBar‖ ^ (2 : ℕ) - (γ / 2) * ‖a • x + b • y‖ ^ (2 : ℕ)) =
      a * ((γ / 2) * ‖x - xBar‖ ^ (2 : ℕ) - (γ / 2) * ‖x‖ ^ (2 : ℕ)) +
      b * ((γ / 2) * ‖y - xBar‖ ^ (2 : ℕ) - (γ / 2) * ‖y‖ ^ (2 : ℕ)) := by
  rw [quadratic_shift_eq, quadratic_shift_eq, quadratic_shift_eq]
  simp only [inner_add_left, real_inner_smul_left, neg_mul]
  calc
    -(γ * (a * inner ℝ x xBar + b * inner ℝ y xBar)) + (γ / 2) * ‖xBar‖ ^ (2 : ℕ)
      = -(γ * (a * inner ℝ x xBar + b * inner ℝ y xBar)) +
          (a + b) * ((γ / 2) * ‖xBar‖ ^ (2 : ℕ)) := by
            rw [hab]
            ring
    _ = a * (-(γ * inner ℝ x xBar) + (γ / 2) * ‖xBar‖ ^ (2 : ℕ)) +
          b * (-(γ * inner ℝ y xBar) + (γ / 2) * ‖xBar‖ ^ (2 : ℕ)) := by ring

section

variable [CompleteSpace E]

/-- The quadratically regularized affine max-type model is `γ`-strongly convex on the ambient real
inner-product space. -/
theorem regularizedMaxTypeObjective_strongConvexOn_univ
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) :
    StrongConvexOn (Set.univ : Set E) γ
      (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar) := by
  rw [strongConvexOn_iff_convex]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hconv :
      maxTypeAffineApproximation fi xBar (a • x + b • y) ≤
        a * maxTypeAffineApproximation fi xBar x +
          b * maxTypeAffineApproximation fi xBar y :=
    (maxTypeAffineApproximation_convexOn (Set.univ : Set E) convex_univ fi xBar).2
      (by simp : x ∈ (Set.univ : Set E))
      (by simp : y ∈ (Set.univ : Set E))
      ha hb hab
  have hquad :
      ((γ / 2) * ‖a • x + b • y - xBar‖ ^ (2 : ℕ) -
          (γ / 2) * ‖a • x + b • y‖ ^ (2 : ℕ)) =
        a * ((γ / 2) * ‖x - xBar‖ ^ (2 : ℕ) - (γ / 2) * ‖x‖ ^ (2 : ℕ)) +
          b * ((γ / 2) * ‖y - xBar‖ ^ (2 : ℕ) - (γ / 2) * ‖y‖ ^ (2 : ℕ)) :=
    quadratic_shift_affine x y xBar hab
  calc
    (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar (a • x + b • y) -
        (γ / 2) * ‖a • x + b • y‖ ^ (2 : ℕ))
      = maxTypeAffineApproximation fi xBar (a • x + b • y) +
          (((γ / 2) * ‖a • x + b • y - xBar‖ ^ (2 : ℕ)) -
            (γ / 2) * ‖a • x + b • y‖ ^ (2 : ℕ)) := by
              simp [quadraticallyRegularizedObjective_apply, sub_eq_add_neg]
              ring
    _ ≤ (a * maxTypeAffineApproximation fi xBar x + b * maxTypeAffineApproximation fi xBar y) +
          (((γ / 2) * ‖a • x + b • y - xBar‖ ^ (2 : ℕ)) -
            (γ / 2) * ‖a • x + b • y‖ ^ (2 : ℕ)) := by
              gcongr
    _ = a *
          (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar x -
            (γ / 2) * ‖x‖ ^ (2 : ℕ)) +
        b *
          (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar y -
            (γ / 2) * ‖y‖ ^ (2 : ℕ)) := by
              rw [hquad]
              simp [quadraticallyRegularizedObjective_apply, sub_eq_add_neg]
              ring

private theorem regularizedMaxTypeObjective_strongConvexOn
    (Q : Set E) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) :
    StrongConvexOn Q γ
      (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar) := by
  have hstrong_univ :
      StrongConvexOn Set.univ γ
        (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar) :=
    regularizedMaxTypeObjective_strongConvexOn_univ fi xBar γ
  rw [strongConvexOn_iff_convex] at hstrong_univ ⊢
  exact hstrong_univ.subset (by simp) hQ_convex

private theorem firstOrderTaylorModelAt_continuous
    (f : E → ℝ) (xBar : E) :
    Continuous (firstOrderTaylorModelAt f xBar) := by
  simpa [firstOrderTaylorModelAt_apply] using
    continuous_const.add
      ((innerSL ℝ (∇ f xBar)).continuous.comp (continuous_id.sub continuous_const))

private theorem maxTypeAffineApproximation_continuous
    (fi : ι → E → ℝ) (xBar : E) :
    Continuous (maxTypeAffineApproximation fi xBar) := by
  classical
  have hcont :
      Continuous
        (fun x ↦
          Finset.univ.sup' Finset.univ_nonempty
            (fun i : ι ↦ firstOrderTaylorModelAt (fi i) xBar x)) :=
    Continuous.finset_sup'_apply Finset.univ_nonempty
      (fun i _ ↦ firstOrderTaylorModelAt_continuous (fi i) xBar)
  simpa [maxTypeAffineApproximation] using hcont

private theorem regularizedMaxTypeObjective_continuous
    (fi : ι → E → ℝ) (xBar : E) (γ : ℝ) :
    Continuous (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar) := by
  simpa [quadraticallyRegularizedObjective_apply] using
    (maxTypeAffineApproximation_continuous fi xBar).add
      (continuous_const.mul (((continuous_id.sub continuous_const).norm).pow (2 : ℕ)))

end

section ExactStep

variable [ProperSpace E]

/-- Remark 2.41.1: the regularized max-type affine subproblem has a unique feasible exact step.
This well-definedness is obtained by combining convexity of the affine max-type model with the
centered quadratic regularization. -/
-- Proof sketch: the affine max-type model is convex on `Set.univ`, and after subtracting
-- `(γ / 2) * ‖x‖²` from the regularized objective, the quadratic remainder is affine in `x`.
-- Hence the owner regularized max-type model is `γ`-strongly convex on `Q`, and it is continuous
-- because it is the sum of a finite maximum of affine functions and the quadratic penalty. The
-- owner theorem `StrongConvexOn.existsUnique_isMinOn_of_isClosed` then gives a unique feasible
-- minimizer on the nonempty closed set `Q`.
theorem existsUnique_maxTypeGradientMapping
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) :
    ∃! xPlus : E,
      xPlus ∈ Q ∧
        IsMinOn
          (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar)
          Q
          xPlus := by
  have hγ : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  exact
    StrongConvexOn.existsUnique_isMinOn_of_isClosed
      (regularizedMaxTypeObjective_strongConvexOn Q hQ_convex fi xBar γ)
      hγ
      (regularizedMaxTypeObjective_continuous fi xBar γ).continuousOn
      hQ_nonempty hQ_closed

/-- The regularized max-type model viewed through the generic gradient-mapping owner from
`Definition_2_41`. -/
private abbrev maxTypeRegularizedModel
    (fi : ι → E → ℝ) (γ : NNRealˣ) :
    E → E → ℝ :=
  fun xBar ↦ quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar

private theorem existsUnique_mem_gradientMappingSet
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) :
    ∃! xPlus : E, xPlus ∈ gradientMappingSet Q (maxTypeRegularizedModel fi γ) xBar := by
  simpa [maxTypeRegularizedModel, gradientMappingSet, mem_gradientMappingSet_iff] using
    existsUnique_maxTypeGradientMapping Q hQ_nonempty hQ_closed hQ_convex fi xBar γ

/-- The textbook exact max-type step `x_f(xBar; γ)` attached to the regularized affine model. -/
noncomputable def maxTypeGradientMapping
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) : E :=
  Classical.choose
    (ExistsUnique.exists
      (existsUnique_mem_gradientMappingSet Q hQ_nonempty hQ_closed hQ_convex fi xBar γ))

private abbrev nonemptyOfFact (Q : Set E) [Fact Q.Nonempty] : Q.Nonempty :=
  Fact.out

private abbrev closedOfFact (Q : Set E) [Fact (IsClosed Q)] : IsClosed Q :=
  Fact.out

private abbrev convexOfFact (Q : Set E) [Fact (Convex ℝ Q)] : Convex ℝ Q :=
  Fact.out

namespace MaxTypeStep

scoped notation:max
    "x_f[" Q ";" hQ_nonempty ";" hQ_closed ";" hQ_convex "|" fi ";" γ "]" "(" xBar ")" =>
  maxTypeGradientMapping
    Q hQ_nonempty hQ_closed hQ_convex fi xBar γ

scoped notation:max
    "x_f[" Q "|" fi ";" γ "]" "(" xBar ")" =>
  maxTypeGradientMapping
    Q (nonemptyOfFact Q) (closedOfFact Q) (convexOfFact Q) fi xBar γ

end MaxTypeStep

open scoped MaxTypeStep

/-- The chosen exact step is the unique element of the owner gradient-mapping set for the
regularized max-type model. -/
theorem maxTypeGradientMapping_mem_gradientMappingSet
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) :
    x_f[Q; hQ_nonempty; hQ_closed; hQ_convex | fi; γ](xBar) ∈
      gradientMappingSet Q (maxTypeRegularizedModel fi γ) xBar := by
  simpa [maxTypeGradientMapping] using
    Classical.choose_spec
      (ExistsUnique.exists
        (existsUnique_mem_gradientMappingSet Q hQ_nonempty hQ_closed hQ_convex fi xBar γ))

/-- The chosen exact step lies in `Q` and minimizes the owner regularized max-type model there. -/
theorem maxTypeGradientMapping_mem_and_isMinOn
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) :
    x_f[Q; hQ_nonempty; hQ_closed; hQ_convex | fi; γ](xBar) ∈ Q ∧
      IsMinOn
        (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar)
        Q
        x_f[Q; hQ_nonempty; hQ_closed; hQ_convex | fi; γ](xBar) := by
  simpa [maxTypeRegularizedModel] using
    (mem_gradientMappingSet_iff.mp
      (maxTypeGradientMapping_mem_gradientMappingSet
        Q hQ_nonempty hQ_closed hQ_convex fi xBar γ))

/-- The `Fact`-based exact-step surface keeps the feasible exact-step property while hiding the
auxiliary feasible-set witness arguments. -/
theorem maxTypeGradientMapping_mem_and_isMinOn_ofFact
    (Q : Set E) [Fact Q.Nonempty] [Fact (IsClosed Q)] [Fact (Convex ℝ Q)]
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) :
    x_f[Q | fi; γ](xBar) ∈ Q ∧
      IsMinOn
        (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar)
        Q
        x_f[Q | fi; γ](xBar) := by
  simpa using
    maxTypeGradientMapping_mem_and_isMinOn
      Q (nonemptyOfFact Q) (closedOfFact Q) (convexOfFact Q) fi xBar γ

/-- The chosen exact max-type step is feasible. -/
theorem maxTypeGradientMapping_mem
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) :
    x_f[Q; hQ_nonempty; hQ_closed; hQ_convex | fi; γ](xBar) ∈ Q :=
  (maxTypeGradientMapping_mem_and_isMinOn
    Q hQ_nonempty hQ_closed hQ_convex fi xBar γ).1

/-- The chosen exact max-type step minimizes the owner regularized max-type model on `Q`. -/
theorem maxTypeGradientMapping_isMinOn
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) :
    IsMinOn
      (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar)
      Q
      x_f[Q; hQ_nonempty; hQ_closed; hQ_convex | fi; γ](xBar) :=
  (maxTypeGradientMapping_mem_and_isMinOn
    Q hQ_nonempty hQ_closed hQ_convex fi xBar γ).2

/-- Any feasible exact step for the regularized max-type model agrees with the chosen one. -/
theorem eq_maxTypeGradientMapping_of_mem_and_isMinOn
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) {xPlus : E}
    (hxPlus : xPlus ∈ Q)
    (hxPlus_min :
      IsMinOn
        (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar)
        Q
        xPlus) :
    xPlus = x_f[Q; hQ_nonempty; hQ_closed; hQ_convex | fi; γ](xBar) := by
  exact
    ((existsUnique_maxTypeGradientMapping Q hQ_nonempty hQ_closed hQ_convex fi xBar γ).unique
      (maxTypeGradientMapping_mem_and_isMinOn
        Q hQ_nonempty hQ_closed hQ_convex fi xBar γ)
      ⟨hxPlus, hxPlus_min⟩).symm

/-- Any feasible exact step for the regularized max-type model agrees with the `Fact`-based
source-facing exact step `x_f(xBar; γ)`. -/
theorem eq_maxTypeGradientMapping_of_mem_and_isMinOn_ofFact
    (Q : Set E) [Fact Q.Nonempty] [Fact (IsClosed Q)] [Fact (Convex ℝ Q)]
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) {xPlus : E}
    (hxPlus : xPlus ∈ Q)
    (hxPlus_min :
      IsMinOn
        (quadraticallyRegularizedObjective (maxTypeAffineApproximation fi xBar) γ xBar)
        Q
        xPlus) :
    xPlus = x_f[Q | fi; γ](xBar) := by
  simpa using
    eq_maxTypeGradientMapping_of_mem_and_isMinOn
      Q (nonemptyOfFact Q) (closedOfFact Q) (convexOfFact Q) fi xBar γ hxPlus hxPlus_min

/-- The textbook reduced gradient `g_f(xBar; γ)` is the scaled residual from `xBar` to the exact
max-type step. -/
abbrev maxTypeReducedGradient
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) : E :=
  reducedGradientOf
    (γ : ℝ)
    xBar
    (x_f[Q; hQ_nonempty; hQ_closed; hQ_convex | fi; γ](xBar))

namespace MaxTypeStep

scoped notation:max
    "g_f[" Q ";" hQ_nonempty ";" hQ_closed ";" hQ_convex "|" fi ";" γ "]" "(" xBar ")" =>
  maxTypeReducedGradient
    Q hQ_nonempty hQ_closed hQ_convex fi xBar γ

scoped notation:max
    "g_f[" Q "|" fi ";" γ "]" "(" xBar ")" =>
  maxTypeReducedGradient
    Q (nonemptyOfFact Q) (closedOfFact Q) (convexOfFact Q) fi xBar γ

end MaxTypeStep

/-- The `Fact`-based reduced gradient keeps the usual scaled-residual formula while hiding the
auxiliary feasible-set witness arguments. -/
@[simp] theorem maxTypeReducedGradient_eq_smul_sub_ofFact
    (Q : Set E) [Fact Q.Nonempty] [Fact (IsClosed Q)] [Fact (Convex ℝ Q)]
    (fi : ι → E → ℝ) (xBar : E) (γ : NNRealˣ) :
    g_f[Q | fi; γ](xBar) = (γ : ℝ) • (xBar - x_f[Q | fi; γ](xBar)) := by
  rfl

end ExactStep

end MaxTypeStep

section Singleton

section

variable [CompleteSpace E]

/-- With one component, the max-type affine model is the ordinary first-order affine model. -/
@[simp] theorem maxTypeAffineApproximation_singleton
    (f : E → ℝ) (xBar x : E) :
    maxTypeAffineApproximation (fun _ : Unit ↦ f) xBar x =
      f xBar + inner ℝ (∇ f xBar) (x - xBar) := by
  simp [maxTypeAffineApproximation_apply]

end

section

variable
    [ProperSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ)

/-- For a single component, the max-type exact step agrees with the projected-gradient mapping
from `Definition_2_35_1`. -/
@[simp] theorem maxTypeGradientMapping_singleton_eq_gradientMapping
    :
    maxTypeGradientMapping
      Q hQ_nonempty hQ_closed hQ_convex (fun _ : Unit ↦ f) xBar γ =
      gradientMapping Q hQ_nonempty hQ_closed hQ_convex f xBar γ :=
  let hmin :
      gradientMapping Q hQ_nonempty hQ_closed hQ_convex f xBar γ ∈ Q ∧
        IsMinOn
          (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) γ xBar)
          Q
          (gradientMapping Q hQ_nonempty hQ_closed hQ_convex f xBar γ) :=
    gradientMapping_minimizes_objective hQ_nonempty hQ_closed hQ_convex
  (eq_maxTypeGradientMapping_of_mem_and_isMinOn
    Q hQ_nonempty hQ_closed hQ_convex (fun _ : Unit ↦ f) xBar γ
    hmin.1
    (by
      simpa [maxTypeAffineApproximation_singleton] using hmin.2)).symm

/-- For a single component, the max-type reduced gradient agrees with the reduced gradient from
`Definition_2_35_1`. -/
@[simp] theorem maxTypeReducedGradient_singleton_eq_reducedGradient
    :
    maxTypeReducedGradient
      Q hQ_nonempty hQ_closed hQ_convex (fun _ : Unit ↦ f) xBar γ =
      reducedGradient Q hQ_nonempty hQ_closed hQ_convex f xBar γ := by
  simp [maxTypeReducedGradient, reducedGradientOf, reducedGradient,
    maxTypeGradientMapping_singleton_eq_gradientMapping]

end

end Singleton
