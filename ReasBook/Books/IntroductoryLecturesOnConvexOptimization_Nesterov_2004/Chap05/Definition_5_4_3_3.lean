/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Convex.Cone.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Definition 5.4.3.3 lies in the Chapter 5 logarithmic-homogeneity / cone-barrier domain.

Sampled owner-style declarations in the same domain:
* mathlib `ConvexCone ℝ E`, the canonical owner for convex cone domains;
* mathlib `ConvexCone.convex`, which derives convexity from that owner instead of storing it as
  parallel data;
* mathlib `ConvexCone.Pointed.of_nonempty_of_isClosed`, which recovers `0 ∈ K` for a closed
  nonempty cone and supports the nonnegative-scalar bridge;
* `IsBarrierFunctionOn` in `Chap01/Definition_1_10_18`, which carries closedness canonically as a
  parent `Fact`;
* `IsSelfConcordantBarrierOnWith` in `Chap05/Definition_5_3_2`, which keeps the source-facing
  owner while shrinking primitive data to the actual mathematical content.

Best owner abstraction:
* source-facing: `IsLogarithmicallyHomogeneousOnWith K ν F`;
* core/canonical ambient owner: `ConvexCone ℝ E`, with closedness carried separately as
  `Fact (IsClosed (K : Set E))`;
* bridge/view: the set-level `isClosed`, `pointed`, and nonnegative-scalar `smul_mem` lemmas.

Primitive data:
* a cone owner `K : ConvexCone ℝ E`;
* closedness of `K`;
* nonempty interior of `K`;
* `C²` regularity of `F` on `interior K`;
* the source-facing logarithmic scaling law on `interior K` for positive real scalars.

Derived API:
* convexity of `K` from `K.convex`;
* origin membership from closedness plus nonempty interior;
* the nonnegative real-scalar cone-closure bridge `smul_mem`.

Source/core/bridge triage:
* source-facing: logarithmic homogeneity with parameter `ν`;
* core/canonical: `ConvexCone ℝ E` together with the parent closedness assumption;
* bridge/view: the set-level closure/pointedness lemmas.

There is no earlier project or mathlib owner for this full logarithmic-homogeneity notion, so the
file keeps a source-facing owner declaration. The refinement here is therefore not to delete the
owner, but to organize it around the chapter's canonical cone owner and keep only the genuinely
source-facing extra data. -/

/-- Definition 5.4.3.3: a function `F : E → ℝ` is logarithmically homogeneous on a closed convex
cone `K` with nonempty interior and logarithmic homogeneity parameter `ν` when `F` is twice
continuously differentiable on `interior K` and `F (τ • x) = F x - ν log τ` for every
`x ∈ interior K` and every `τ > 0`. The cone structure itself is carried by the canonical owner
`K : ConvexCone ℝ E`, while closedness remains part of the source-facing notion; sign conditions on
`ν` belong to later barrier layers when they are actually needed, not to logarithmic homogeneity
itself. -/
class IsLogarithmicallyHomogeneousOnWith (K : ConvexCone ℝ E) (ν : ℝ) (F : E → ℝ) : Prop
    extends Fact (IsClosed (K : Set E)) where
  /-- The cone `K` has nonempty interior. -/
  interior_nonempty : (interior (K : Set E)).Nonempty
  /-- The function `F` is twice continuously differentiable on `interior K`. -/
  contDiffOn : ContDiffOn ℝ 2 F (interior (K : Set E))
  /-- The logarithmic scaling identity holds on `interior K` for every positive scalar. -/
  logarithmic_scaling {x : E} (hx : x ∈ interior (K : Set E)) {τ : ℝ} (hτ : 0 < τ) :
    F (τ • x) = F x - ν * Real.log τ

attribute [instance] IsLogarithmicallyHomogeneousOnWith.toFact

namespace IsLogarithmicallyHomogeneousOnWith

/-- A logarithmic-homogeneity hypothesis canonically supplies the closedness of its cone. -/
theorem isClosed
    {K : ConvexCone ℝ E} {ν : ℝ} {F : E → ℝ} (h : IsLogarithmicallyHomogeneousOnWith K ν F) :
    IsClosed (K : Set E) := by
  let _ : IsLogarithmicallyHomogeneousOnWith K ν F := h
  exact Fact.out

/-- A logarithmic-homogeneity hypothesis canonically supplies the owner property `K.Pointed`. -/
theorem pointed
    {K : ConvexCone ℝ E} {ν : ℝ} {F : E → ℝ} (h : IsLogarithmicallyHomogeneousOnWith K ν F) :
    K.Pointed :=
  ConvexCone.Pointed.of_nonempty_of_isClosed (h.interior_nonempty.mono interior_subset) h.isClosed

/-- A logarithmic-homogeneity hypothesis gives the usual real-scalar cone-closure statement for
nonnegative scalars. -/
theorem smul_mem
    {K : ConvexCone ℝ E} {ν : ℝ} {F : E → ℝ}
    (h : IsLogarithmicallyHomogeneousOnWith K ν F)
    {x : E} (hx : x ∈ K) {τ : ℝ} (hτ : 0 ≤ τ) :
    τ • x ∈ K := by
  rcases lt_or_eq_of_le hτ with hτ' | rfl
  · exact K.smul_mem hτ' hx
  · simpa [ConvexCone.Pointed] using h.pointed

end IsLogarithmicallyHomogeneousOnWith

end
