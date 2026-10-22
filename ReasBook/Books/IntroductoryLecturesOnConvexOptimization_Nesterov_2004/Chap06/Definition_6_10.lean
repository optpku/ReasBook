/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 6.10 lies in the prox-function / strong-convexity domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`, the canonical owner for strong convexity on a feasible set;
- chapter `NesterovIsProxFunction` in `Definition_6_31`, which later packages continuity together with the
  same unit-strong-convexity hypothesis;
- mathlib `IsGreatest`, the canonical order-theoretic owner for the textbook maximum datum
  `max_{x ∈ Q₁} d₁(x)`;
- the generic supremum companion `h.csSup_eq` attached to an `IsGreatest` witness.

Best owner abstraction:
- source-facing: the unit-strong-convexity surface `StrongConvexOn Q₁ 1 d₁` together with the
  maximum-attainment surface `IsGreatest (d₁ '' Q₁) D₁`;
- core/canonical: `StrongConvexOn` and `IsGreatest`;
- bridge/view: the pointwise bound extracted from `IsGreatest`, and the generic supremum
  companion `hD₁.csSup_eq`.

Primitive data:
- a feasible set `Q₁`;
- a prox term `d₁`;
- a bound value `D₁`.

Derived API:
- the prox-function clause, reused directly from `StrongConvexOn Q₁ 1 d₁`;
- the order-theoretic maximum surface `IsGreatest (d₁ '' Q₁) D₁`;
- the induced pointwise bound `d₁ x ≤ D₁` for `x ∈ Q₁` and the companion supremum identity.

Source/core/bridge triage:
- source-facing: `StrongConvexOn Q₁ 1 d₁` and `IsGreatest (d₁ '' Q₁) D₁`;
- core/canonical: `StrongConvexOn` and `IsGreatest`;
- bridge/view: `image_le_of_isGreatest` and `hD₁.csSup_eq`.

Definition 6.10 therefore does not introduce a second owner for prox-functions or prox-bounds:
the strong-convexity clause is already owned by `StrongConvexOn`, and the `D₁` datum is already
captured canonically by `IsGreatest` on the image set.
-/

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Q₁ : Set E} {d₁ : E → ℝ}

/- Definition 6.10: for a real normed space, a prox-function on `Q₁` is exactly the unit-strongly
convex owner `StrongConvexOn Q₁ 1 d₁`. -/
#check (StrongConvexOn Q₁ 1 d₁ : Prop)

end

section

variable {E : Type u}
variable {Q₁ : Set E} {d₁ : E → ℝ} {D₁ : ℝ}

/- The textbook constant `D₁` is the maximum of `d₁` on `Q₁`; in Lean this is the canonical
order-theoretic surface `IsGreatest (d₁ '' Q₁) D₁`. -/
#check IsGreatest (d₁ '' Q₁) D₁

section

variable (hD₁ : IsGreatest (d₁ '' Q₁) D₁)

/- The supremum reformulation is the generic order-theoretic companion `hD₁.csSup_eq`, not a
second source-facing owner. -/
#check hD₁.csSup_eq

end

/-- If `D₁` is the greatest value of `d₁` on `Q₁`, then every feasible point satisfies the
textbook bound `d₁ x ≤ D₁`. -/
theorem image_le_of_isGreatest (hD₁ : IsGreatest (d₁ '' Q₁) D₁) {x : E} (hx : x ∈ Q₁) :
    d₁ x ≤ D₁ :=
  hD₁.2 (Set.mem_image_of_mem d₁ hx)

end
