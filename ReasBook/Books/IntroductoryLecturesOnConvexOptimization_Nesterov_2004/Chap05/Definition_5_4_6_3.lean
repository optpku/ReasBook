/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w uR

section

variable {R : Type uR}
variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
variable [Semiring R] [PartialOrder R]
variable [AddCommGroup E₂] [SMul R E₂]

/- Definition 5.4.6.3 lies in the chapter's cone-composition feasible-set domain.

Sampled owner declarations:
* mathlib `ConvexCone R E₂`, the canonical owner for the ambient cone order;
* `constrainedEpigraph` and `mem_constrainedEpigraph_iff` from `Chap03/Definition_3_3`, the
  chapter's standard owner/view pattern for source-facing feasible-set constructions on product
  spaces;
* `power_cone_plus` from `Definition_5_4_7_4`, the later source-facing power-cone owner obtained
  by specializing this construction;
* `entropyEpigraphCone` from `Definition_5_4_7_8`, the later entropy-epigraph owner obtained by
  the same specialization pattern.

Source/core/bridge triage:
* source-facing: `coneCompositionFeasibleSet Q₁ K ξ Q₂`;
* core/canonical: the cone owner `ConvexCone R E₂` together with ordinary `Set` membership on
  product spaces;
* bridge/view: the membership expansion lemma.

Primitive data:
* the domain `Q₁`;
* the cone `K` at the primitive ordered-semiring action layer;
* the map `ξ`;
* the downstream feasible set `Q₂`.

Derived API:
* the canonical pair-membership expansion lemma for the owner set.

The source-facing owner here is the composed feasible set itself. The intermediate pair relation
is only implementation scaffolding, so this refinement deletes that wrapper and keeps the single
owner spelling reused downstream in `Theorem_5_4_6_13`. -/

/-- Definition 5.4.6.3: the feasible set obtained by composing `Q₂` with the cone-order
domination relation induced by `ξ` and `K`. -/
def coneCompositionFeasibleSet
    (Q₁ : Set E₁) (K : ConvexCone R E₂) (ξ : E₁ → E₂)
    (Q₂ : Set (E₂ × E₃)) : Set (E₁ × E₃) :=
  { p | ∃ y : E₂, p.1 ∈ Q₁ ∧ ξ p.1 - y ∈ K ∧ (y, p.2) ∈ Q₂ }

-- Proof sketch: unfold `coneCompositionFeasibleSet`.
/-- A pair `p` lies in `coneCompositionFeasibleSet Q₁ K ξ Q₂` exactly when there exists
`y : E₂` with `p.1 ∈ Q₁`, `ξ p.1 - y ∈ K`, and `(y, p.2) ∈ Q₂`. -/
@[simp] theorem mem_coneCompositionFeasibleSet_iff
    (Q₁ : Set E₁) (K : ConvexCone R E₂) (ξ : E₁ → E₂)
    (Q₂ : Set (E₂ × E₃)) {p : E₁ × E₃} :
    p ∈ coneCompositionFeasibleSet Q₁ K ξ Q₂ ↔
      ∃ y : E₂, p.1 ∈ Q₁ ∧ ξ p.1 - y ∈ K ∧ (y, p.2) ∈ Q₂ :=
  Iff.rfl

end
