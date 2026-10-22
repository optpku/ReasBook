/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_81

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/-
Lemma 7.20 lies in the chapter's relative-scale subgradient-transform domain.

Sampled owner-style declarations:
- `StrictlyPositiveOn` and `StrictlyPositiveOn.inequality` in `Chap07/Definition_7_81`, the
  chapter's source-facing positivity owner and its atomic projection lemma;
- `subdifferentialWithin` and the notation `∂[Set.univ] f(x)` in `Chap03/Theorem_3_44`, the
  canonical real-valued whole-space subdifferential surface used by `StrictlyPositiveOn`;
- `IsSubgradientAt` in `Chap03/Definition_3_1_5`, the underlying extended-valued owner reused by
  that real-valued subdifferential surface.

Best owner abstraction:
- source-facing: the relative-scale transformed objective and transformed subgradient;
- core/canonical: the Chapter 7 positivity owner `StrictlyPositiveOn`, written on the whole-space
  subdifferential surface `g ∈ ∂[Set.univ] f(x)`;
- bridge/view: the nonlinear lower-support inequality below for the transformed objective.

Primitive data:
- a real-valued objective `f : X → ℝ` for the transformed objective owner, and
  `f : V → ℝ` for the subgradient theorem;
- a base point `x` and a vector `g`.

Derived API:
- the textbook notation `f̂` for the transformed objective `x ↦ (1 / 2) * f(x)^2`;
- the textbook notation `ĝ[f; x] g` for the transformed subgradient `f x • g`;
- the nonlinear lower-support inequality obtained from `StrictlyPositiveOn Q f`.

Source/core/bridge triage:
- source-facing: `relativeScaleTransformedObjective`,
  `relativeScaleTransformedSubgradient`, and the displayed lower-support theorem;
- core/canonical: `StrictlyPositiveOn` and `∂[Set.univ] f(x)`;
- bridge/view: the lower-support inequality specialized to the transformed objective.

This file is the Chapter 7 owner for the relative-scale transform itself. The transformed
objective lives on the weakest ambient layer `X → ℝ`, the transformed subgradient only uses scalar
multiplication, and the nonlinear lower-support theorem adds the inner-product structure.
Downstream files should reuse these owners directly rather than rebuilding local copies of the
transformed objective or of its subgradient interface.
-/
variable {X : Type u}

/-- The transformed objective associated to `f` is `x ↦ (1 / 2) * f(x)^2`. -/
def relativeScaleTransformedObjective (f : X → ℝ) : X → ℝ :=
  fun x ↦ (1 / 2 : ℝ) * (f x) ^ 2

/- Source-facing Lean notation for the textbook transformed objective `f̂`. -/
scoped[RelativeScaleTransformNotation] postfix:max "̂" => relativeScaleTransformedObjective

open scoped RelativeScaleTransformNotation

/-- Evaluating the transformed objective notation `f̂` recovers the formula `(1 / 2) * f(x)^2`. -/
-- Proof sketch: unfold `f̂`.
theorem relativeScaleTransformedObjective_apply (f : X → ℝ) (x : X) :
    f̂ x = (1 / 2 : ℝ) * (f x) ^ 2 :=
  rfl

section Smul

variable {V : Type u} [SMul ℝ V]

/-- The pointwise transformed subgradient value attached to `g ∈ ∂f(x)` is `f(x) • g`. -/
def relativeScaleTransformedSubgradient (f : V → ℝ) (x g : V) : V :=
  f x • g

/- Source-facing Lean notation for the textbook transformed subgradient `ĝ[f; x] g`. -/
scoped[RelativeScaleTransformNotation] notation:max "ĝ[" f:arg "; " x:arg "]" =>
  relativeScaleTransformedSubgradient f x

/-- Evaluating the transformed subgradient notation gives the scaled vector `f(x) • g`. -/
-- Proof sketch: unfold `ĝ[f; x] g`.
theorem relativeScaleTransformedSubgradient_def (f : V → ℝ) (x g : V) :
    ĝ[f; x] g = f x • g :=
  rfl

end Smul

section InnerProduct

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

-- Proof sketch: rewrite `f̂` as `(1 / 2) * f^2` and
-- `ĝ[f; x] g` as `f(x) • g`, then apply
-- `StrictlyPositiveOn.inequality` to get `f y ≥ -(f x + ⟪g, y - x⟫)`. Squaring the resulting
-- lower bound and expanding the square yields the displayed estimate.
/-- Lemma 7.20: if `f` is strictly positive on `Q`, then for every `x, y ∈ Q` and every
whole-space subgradient `g ∈ ∂[Set.univ] f(x)`, the
transformed objective satisfies the nonlinear lower-support inequality
`f̂ y ≥ f̂ x + ⟪ĝ[f; x] g, y - x⟫ + (1 / 2) * ⟪g, y - x⟫^2`. -/
theorem relativeScaleTransformedObjective_nonlinear_lower_support
    {Q : Set V} {f : V → ℝ}
    (hstrict : StrictlyPositiveOn Q f)
    {x y g : V} (hx : x ∈ Q) (hy : y ∈ Q)
    (hg : g ∈ ∂[Set.univ] f(x)) :
    f̂ y ≥
      f̂ x +
        inner ℝ (ĝ[f; x] g) (y - x) +
        (1 / 2 : ℝ) * (inner ℝ g (y - x)) ^ 2 := by
  -- Rewrite the Chapter 7 positivity hypothesis into the companion lower bound `f y ≥ -a`.
  have hpositive : 0 ≤ f y + f x + inner ℝ g (y - x) :=
    hstrict.inequality hx hy hg
  -- Rewrite the whole-space subgradient membership into the affine lower-support inequality.
  rw [mem_subdifferentialWithin_iff] at hg
  have hsupport : f y ≥ f x + inner ℝ g (y - x) :=
    hg.2 (by simp)
  let a : ℝ := f x + inner ℝ g (y - x)
  have hneg_support : f y ≥ -a := by
    dsimp [a] at *
    linarith
  have hsq : (1 / 2 : ℝ) * (f y) ^ 2 ≥ (1 / 2 : ℝ) * a ^ 2 := by
    nlinarith [hsupport, hneg_support]
  have hinner :
      inner ℝ (ĝ[f; x] g) (y - x) = f x * inner ℝ g (y - x) := by
    rw [relativeScaleTransformedSubgradient_def, inner_smul_left]
    simp
  have hrhs :
      f̂ x + inner ℝ (ĝ[f; x] g) (y - x) + (1 / 2 : ℝ) * (inner ℝ g (y - x)) ^ 2 =
        (1 / 2 : ℝ) * a ^ 2 := by
    rw [relativeScaleTransformedObjective_apply, hinner]
    dsimp [a]
    ring
  -- Compare `f̂ y = (1 / 2) * f y^2` with the normalized quadratic right-hand side.
  calc
    f̂ y = (1 / 2 : ℝ) * (f y) ^ 2 := by
      rw [relativeScaleTransformedObjective_apply]
    _ ≥ (1 / 2 : ℝ) * a ^ 2 := hsq
    _ = f̂ x + inner ℝ (ĝ[f; x] g) (y - x) + (1 / 2 : ℝ) * (inner ℝ g (y - x)) ^ 2 := by
      symm
      exact hrhs

end InnerProduct

end
