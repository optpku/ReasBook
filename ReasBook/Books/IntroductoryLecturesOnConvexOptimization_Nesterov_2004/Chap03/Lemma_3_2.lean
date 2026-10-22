/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/- Lemma 3.2 lies in the chapter's constrained-epigraph convex-analysis domain.

Primary domain:
- restriction of a closed convex constrained epigraph to a closed convex subset of the base domain
  in a real topological module.

Sampled owner-style declarations:
- `constrainedEpigraph` in `Definition_3_3`, the chapter owner for the constrained epigraph;
- `mem_constrainedEpigraph_iff` in `Definition_3_3`, the atomic membership view for that owner;
- `constrainedEpigraph_eq_prod_univ_inter_of_subset` in `Definition_3_3`, the canonical bridge
  from restriction to intersection with the base cylinder;
- mathlib `Convex.prod`, the canonical convex-product constructor used by the bridge proof;
- `ClosedConvexOn.restrict` in `Definition_3_1_1_5`, the stronger owner theorem obtained from the
  same bridge once one also has the primitive domain-finiteness data `Q ⊆ dom f`.

Best owner abstraction:
- `constrainedEpigraph Q f`.

Primitive data:
- the constrained epigraph `constrainedEpigraph Q f`;
- the closed/convex subset data `Q₁ ⊆ Q`, `IsClosed Q₁`, and `Convex ℝ Q₁`.

Derived API:
- the restricted closedness/convexity conclusion for `constrainedEpigraph Q₁ f`, obtained from the
  owner bridge `constrainedEpigraph_eq_prod_univ_inter_of_subset`.

Source/core/bridge triage:
- source-facing: Lemma 3.2 as the restricted-epigraph closedness/convexity statement;
- core/canonical: `constrainedEpigraph` from `Definition_3_3`;
- bridge/view: `constrainedEpigraph_eq_prod_univ_inter_of_subset`.

This file therefore reuses the chapter owner `constrainedEpigraph` directly and does not keep a
parallel local definition or membership lemma. Since Lemma 3.2 assumes only closedness and
convexity of the constrained epigraph, and not the stronger owner datum `Q ⊆ dom f`, the theorem
remains source-facing rather than collapsing to `ClosedConvexOn.restrict`; the refinement is the
ambient generalization from the textbook model `ℝⁿ` to an arbitrary real topological module. -/

/-- Lemma 3.2: if the epigraph of `f` over `Q` is a closed convex subset of `X × ℝ` and
`Q₁ ⊆ Q` is closed and convex, then the epigraph of the restriction of `f` to `Q₁` is also closed
and convex. -/
theorem isClosed_convex_constrainedEpigraph_restrict
    {Q Q₁ : Set X} {f : X → WithTop ℝ}
    (hf_closed : IsClosed (constrainedEpigraph Q f))
    (hf_convex : Convex ℝ (constrainedEpigraph Q f))
    (hQ₁_subset : Q₁ ⊆ Q)
    (hQ₁_closed : IsClosed Q₁)
    (hQ₁_convex : Convex ℝ Q₁) :
    IsClosed (constrainedEpigraph Q₁ f) ∧ Convex ℝ (constrainedEpigraph Q₁ f) := by
  -- Rewrite the restricted epigraph as the original epigraph intersected with the base cylinder.
  have hEpigraph :
      constrainedEpigraph Q₁ f = (Q₁ ×ˢ (Set.univ : Set ℝ)) ∩ constrainedEpigraph Q f :=
    constrainedEpigraph_eq_prod_univ_inter_of_subset hQ₁_subset
  constructor
  · rw [hEpigraph]
    -- Closedness is inherited from the closed cylinder `Q₁ × ℝ` and the closed original epigraph.
    exact (hQ₁_closed.prod isClosed_univ).inter hf_closed
  · rw [hEpigraph]
    -- Convexity is inherited from the convex cylinder `Q₁ × ℝ` and the convex original epigraph.
    exact (hQ₁_convex.prod convex_univ).inter hf_convex

end
