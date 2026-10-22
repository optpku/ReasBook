/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 3.1.1.2 is the source-facing owner of the finite-value domain of an
extended-real-valued function.

Primary domain:
- finite-value domains of `EReal`-valued functions.

Relevant owner-style declarations sampled before refinement:
- chapter `withTopEffectiveDomain` in `Definition_3_3`, the analogous owner for `WithTop ℝ`
- chapter `mem_withTopEffectiveDomain_iff` in `Definition_3_3`, the atomic membership bridge for
  that owner
- mathlib `EReal.canLift`, whose predicate is exactly "neither `⊤` nor `⊥`"
- mathlib `EReal.range_coe_eq_Ioo`, the canonical order-theoretic description of finite `EReal`
  values

Best owner abstraction:
- `extendedRealEffectiveDomain`

Primitive data:
- the pointwise finiteness predicate `f x ≠ ⊤ ∧ f x ≠ ⊥`

Derived API:
- `mem_extendedRealEffectiveDomain_iff`
- `extendedRealEffectiveDomain_nonempty_iff`

Source/core/bridge triage:
- source-facing: the effective domain of an extended-real-valued function
- core/canonical: `extendedRealEffectiveDomain`
- bridge/view: `mem_extendedRealEffectiveDomain_iff`

The textbook states this notion for functions on `ℝⁿ`, but the domain construction itself uses no
Euclidean structure. Following the chapter owner style from `Definition_3_3`, this file exposes
the canonical owner on an arbitrary domain type; later items simply specialize it. -/

/-- Definition 3.1.1.2: the chapter's effective-domain owner for an extended-real-valued
function, namely the set of points where the value is a finite real. The textbook then treats the
nonemptiness condition on this domain as a standing assumption. -/
abbrev extendedRealEffectiveDomain {X : Type u} (f : X → EReal) : Set X :=
  {x | f x ≠ ⊤ ∧ f x ≠ ⊥}

/-- Textbook notation for the effective domain of an extended-real-valued function. -/
scoped[ConvexAnalysis] notation "dom " f:arg => extendedRealEffectiveDomain f

open scoped ConvexAnalysis

/-- Membership in the effective domain means that the function value is neither `⊤` nor `⊥`. -/
@[simp] theorem mem_extendedRealEffectiveDomain_iff {X : Type u} {f : X → EReal} {x : X} :
    x ∈ dom f ↔ f x ≠ ⊤ ∧ f x ≠ ⊥ :=
  Iff.rfl

/-- The effective domain is nonempty exactly when the function takes a finite value somewhere. -/
-- Proof sketch: unpack `Set.Nonempty` for `extendedRealEffectiveDomain f` and translate pointwise
-- membership through `mem_extendedRealEffectiveDomain_iff`.
theorem extendedRealEffectiveDomain_nonempty_iff {X : Type u} {f : X → EReal} :
    (dom f).Nonempty ↔ ∃ x, f x ≠ ⊤ ∧ f x ≠ ⊥ := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, hx⟩

section

variable {X : Type u} (f : X → EReal)

/- The textbook immediately adds the standing assumption that the effective domain is nonempty.
The canonical Lean surface for that assumption is simply `(dom f).Nonempty`. -/
#check (dom f).Nonempty

end
