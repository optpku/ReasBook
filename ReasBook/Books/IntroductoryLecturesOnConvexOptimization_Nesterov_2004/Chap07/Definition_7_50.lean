/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_37

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Definition 7.50 lies in the chapter's real-valued concave-subdifferential domain.

Sampled owner-style declarations:
- `IsSubgradientAt` in `Chap03/Definition_3_1_5`, the chapter owner for affine lower supports of
  `WithTop ℝ`-valued functions;
- `subdifferential` and the notation `∂ f(x)` in `Chap03/Definition_3_1_5`, the derived set-valued
  owner API;
- `mem_subdifferential_coe_iff` in `Chap06/Definition_6_37`, the real-valued bridge from the
  Chapter 3 owner to the usual affine lower-support inequality;
- `dualAffineSupport_iff_isSubgradientAt` in `Chap07/Definition_7_7`, a nearby Chapter 7 bridge
  that also reuses `IsSubgradientAt` instead of rebuilding a parallel real-valued support owner.

Best owner abstraction:
- core/canonical: `IsSubgradientAt` and `∂` applied to the negated function `-f`;
- bridge/view: the sign change `g ↦ -g`, which turns concave upper supports for `f` into convex
  lower supports for `-f`.

Primitive data:
- a real-valued function `f : E → ℝ`;
- a base point `x : E`;
- a vector `g : E`.

Derived API:
- the source-facing concave-subgradient predicate;
- the source-facing concave subdifferential;
- the textbook affine upper-support equivalence.

Source/core/bridge triage:
- source-facing: `IsConcaveSubgradientAt` and `concaveSubdifferential`;
- core/canonical: `IsSubgradientAt` and `∂` for the negated function;
- bridge/view: `isConcaveSubgradientAt_iff` and `mem_concaveSubdifferential_iff`.

Definition 7.50 does introduce a source-facing concave notion, so this file should not collapse to
a bare recall. But the primitive inequality owner already exists upstream: a concave subgradient of
`f` is exactly a Chapter 3 subgradient of `-f` after the canonical sign flip `g ↦ -g`. The file
therefore keeps the Chapter 7 vocabulary only as a thin bridge layer over that owner abstraction,
instead of maintaining a second primitive affine-support definition.
-/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 7.50: a vector `g` is a subgradient of a concave real-valued function `f` at `x`
when `-g` is a Chapter 3 subgradient of the convex function `-f` at `x`. Equivalently, `g` gives
the global affine upper support inequality for `f`. Since `f : E → ℝ`, the textbook domain
conditions `x ∈ dom f` and `y ∈ dom f` are automatic. -/
def IsConcaveSubgradientAt (f : E → ℝ) (x g : E) : Prop :=
  IsSubgradientAt (fun y ↦ ((-f y : ℝ) : WithTop ℝ)) x (-g)

/-- The concave subgradient predicate is exactly the defining affine upper-support inequality. -/
theorem isConcaveSubgradientAt_iff (f : E → ℝ) (x g : E) :
    IsConcaveSubgradientAt f x g ↔ ∀ y : E, f y ≤ f x + inner ℝ g (y - x) := by
  rw [IsConcaveSubgradientAt, ← mem_subdifferential_iff]
  have hneg :
      -g ∈ ∂ (fun y ↦ ((-f y : ℝ) : WithTop ℝ))(x) ↔
        ∀ y : E, -f y ≥ -f x + inner ℝ (-g) (y - x) :=
    mem_subdifferential_coe_iff
  constructor
  · intro hg y
    have hy : -f y ≥ -f x + inner ℝ (-g) (y - x) := hneg.mp hg y
    have hy' : -f y ≥ -f x - inner ℝ g (y - x) := by
      simpa [inner_neg_left] using hy
    linarith
  · intro hg
    exact hneg.mpr fun y ↦ by
      have hy : f y ≤ f x + inner ℝ g (y - x) := hg y
      have hy' : -f y ≥ -f x - inner ℝ g (y - x) := by
        linarith
      simpa [inner_neg_left] using hy'

/-- The set of all concave subgradients of `f` at `x`, corresponding to the textbook notation
`∇ f(x)`. -/
def concaveSubdifferential (f : E → ℝ) (x : E) : Set E :=
  {g | -g ∈ ∂ (fun y ↦ ((-f y : ℝ) : WithTop ℝ))(x)}

/-- Membership in `concaveSubdifferential f x` is exactly the defining concave subgradient
inequality. -/
@[simp] theorem mem_concaveSubdifferential_iff {f : E → ℝ} {x g : E} :
    g ∈ concaveSubdifferential f x ↔ IsConcaveSubgradientAt f x g := by
  rw [concaveSubdifferential, IsConcaveSubgradientAt]
  change -g ∈ subdifferential (fun y ↦ ((-f y : ℝ) : WithTop ℝ)) x ↔
    IsSubgradientAt (fun y ↦ ((-f y : ℝ) : WithTop ℝ)) x (-g)
  exact mem_subdifferential_iff

end
