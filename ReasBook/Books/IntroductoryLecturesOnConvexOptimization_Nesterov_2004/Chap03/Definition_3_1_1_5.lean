/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped WithTopConvexAnalysis

/-- On a set where `f` is finite, the constrained epigraph of `f` is exactly the ordinary
epigraph of the finite real part `withTopRealPart f`. -/
theorem constrainedEpigraph_eq_epigraph_withTopRealPart
    {X : Type u} {Q : Set X} {f : X → WithTop ℝ}
    (hQ_dom : Q ⊆ dom f) :
    constrainedEpigraph Q f = {p : X × ℝ | p.1 ∈ Q ∧ withTopRealPart f p.1 ≤ p.2} := by
  ext p
  constructor
  · rintro ⟨hpQ, hp⟩
    exact ⟨hpQ, (withTopRealPart_le_iff (hQ_dom hpQ)).2 hp⟩
  · rintro ⟨hpQ, hp⟩
    exact ⟨hpQ, (withTopRealPart_le_iff (hQ_dom hpQ)).1 hp⟩

/- Definition 3.1.1.5 lives in the chapter's `WithTop`-valued convex-analysis API.

Primary domain:
- closed convex extended-real-valued functions on real topological modules, specializing to the
  textbook `ℝⁿ` setting.

Sampled owner-style declarations in this domain:
- `withTopEffectiveDomain`, `withTopRealPart`, `constrainedEpigraph` from `Definition_3_3`
- mathlib `ConvexOn`
- mathlib `convexOn_iff_convex_epigraph`

Owner abstraction:
- source-facing owner: `ClosedConvexOn Q f`
- core/canonical convexity view: `ConvexOn ℝ Q (withTopRealPart f)`
- primitive bridge data: `dom f` and `constrainedEpigraph Q f`

Primitive data:
- the domain inclusion `Q ⊆ dom f`
- the closedness of `constrainedEpigraph Q f`
- the convexity of `constrainedEpigraph Q f`

Derived API:
- `constrainedEpigraph_eq_epigraph_withTopRealPart`
- the projection lemmas out of `ClosedConvexOn`
- `ClosedConvexOn.convexOn_withTopRealPart`
- `ClosedConvexOn.convex`
- `ClosedConvexFunction f` as the special case `Q = dom f`

Source/core/bridge triage:
- source-facing: `ClosedConvexOn`, `ClosedConvexFunction`
- core/canonical: `withTopEffectiveDomain`, `constrainedEpigraph`, `ConvexOn`
- bridge/view: `constrainedEpigraph_eq_epigraph_withTopRealPart`, the projection lemmas, and the
  `ConvexOn` consequences on `dom f`

This file therefore reuses the owner effective-domain abstraction directly instead of keeping a
parallel set-level presentation, while exposing the canonical `ConvexOn` owner view as derived
API rather than storing it as parallel primitive data. -/

section

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-- Definition 3.1.1.5, generalized from the textbook `ℝⁿ` setting: an `ℝ ∪ {+∞}`-valued
function is closed and convex on `Q` when `Q ⊆ dom f` and its constrained epigraph is a closed
convex subset of `X × ℝ`. -/
def ClosedConvexOn (Q : Set X) (f : X → WithTop ℝ) : Prop :=
  Q ⊆ dom f ∧
    IsClosed (constrainedEpigraph Q f) ∧
    Convex ℝ (constrainedEpigraph Q f)

namespace ClosedConvexOn

variable {Q : Set X} {f : X → WithTop ℝ}

/-- A function that is closed and convex on `Q` is finite on every point of `Q`. -/
-- Proof sketch: unfold `ClosedConvexOn` and read off the first conjunct recording
-- `Q ⊆ dom f`.
theorem subset_withTopEffectiveDomain (hf : ClosedConvexOn Q f) :
    Q ⊆ dom f :=
  hf.1

/-- A function that is closed and convex on `Q` has a closed constrained epigraph over `Q`. -/
-- Proof sketch: unfold `ClosedConvexOn` and project to the second conjunct.
theorem isClosed_constrainedEpigraph (hf : ClosedConvexOn Q f) :
    IsClosed (constrainedEpigraph Q f) :=
  hf.2.1

/-- A function that is closed and convex on `Q` has a convex constrained epigraph over `Q`. -/
-- Proof sketch: unfold `ClosedConvexOn` and project to the final conjunct.
theorem convex_constrainedEpigraph (hf : ClosedConvexOn Q f) :
    Convex ℝ (constrainedEpigraph Q f) :=
  hf.2.2

/-- A closed convex function on `Q` induces the canonical `ConvexOn` structure on its finite
real part over `Q`. -/
theorem convexOn_withTopRealPart (hf : ClosedConvexOn Q f) :
    ConvexOn ℝ Q (withTopRealPart f) := by
  refine (convexOn_iff_convex_epigraph).2 ?_
  simpa [constrainedEpigraph_eq_epigraph_withTopRealPart hf.subset_withTopEffectiveDomain] using
    hf.convex_constrainedEpigraph

/-- A function that is closed and convex on `Q` has a convex feasible set `Q`. -/
theorem convex (hf : ClosedConvexOn Q f) :
    Convex ℝ Q :=
  hf.convexOn_withTopRealPart.1

/-- Restricting a closed convex function to a closed convex subset preserves closed convexity. -/
theorem restrict
    {Q Q₁ : Set X} (hf : ClosedConvexOn Q f) (hQ₁_closed : IsClosed Q₁)
    (hQ₁_convex : Convex ℝ Q₁) (hQ₁Q : Q₁ ⊆ Q) :
    ClosedConvexOn Q₁ f := by
  have hQ₁_domain : Q₁ ⊆ dom f := fun x hx ↦
    hf.subset_withTopEffectiveDomain (hQ₁Q hx)
  have hEpigraph :
      constrainedEpigraph Q₁ f = (Q₁ ×ˢ (Set.univ : Set ℝ)) ∩ constrainedEpigraph Q f :=
    constrainedEpigraph_eq_prod_univ_inter_of_subset hQ₁Q
  refine ⟨hQ₁_domain, ?_, ?_⟩
  · rw [hEpigraph]
    exact (hQ₁_closed.prod isClosed_univ).inter hf.isClosed_constrainedEpigraph
  · rw [hEpigraph]
    exact (hQ₁_convex.prod convex_univ).inter hf.convex_constrainedEpigraph

end ClosedConvexOn

/-- A function is a closed convex function when it is closed and convex on its effective domain. -/
abbrev ClosedConvexFunction (f : X → WithTop ℝ) : Prop :=
  ClosedConvexOn (dom f) f

end
