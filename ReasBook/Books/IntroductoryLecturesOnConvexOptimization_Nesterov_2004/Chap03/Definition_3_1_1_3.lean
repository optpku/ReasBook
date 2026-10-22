/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open scoped ConvexAnalysis

/-
Definition 3.1.1.3 is the chapter's `EReal`-valued convex-analysis bridge.

Primary domain:
- finite-value domains and finite real parts of `EReal`-valued functions, together with their
  canonical convexity owners.

Relevant owner-style declarations sampled before refinement:
- mathlib `ConvexOn` in `Mathlib/Analysis/Convex/Function`
- mathlib `StrictConvexOn` in `Mathlib/Analysis/Convex/Function`
- mathlib `ConcaveOn` in `Mathlib/Analysis/Convex/Function`
- chapter `extendedRealEffectiveDomain` in `Definition_3_1_1_2`, exposed on the theorem surface
  by the textbook notation `dom f`
- mathlib `EReal.coe_toReal` in `Mathlib/Data/EReal/Basic`, the finite-value identification used
  in the bridge comparison lemmas

Best owner abstraction:
- the imported owner `extendedRealEffectiveDomain` together with the derived bridge
  `extendedRealRealPart` and the source-facing epigraph owner `effectiveEpigraph`
- core/canonical convexity owners:
  `ConvexOn ℝ (dom f) (extendedRealRealPart f)`,
  `StrictConvexOn ℝ (dom f) (extendedRealRealPart f)`, and
  `ConcaveOn ℝ (dom f) (extendedRealRealPart f)`.

Primitive data:
- the imported effective domain `dom f`
- the finite real part `extendedRealRealPart f`
- the effective epigraph `effectiveEpigraph f`, defined directly as the real epigraph owner over
  `dom f`

Derived API:
- `extendedRealRealPart_eq_toReal`
- `coe_extendedRealRealPart`
- the order-translation lemmas for `extendedRealRealPart` on `dom f`
- `mem_effectiveEpigraph_iff`, which restores the textbook `f x ≤ t` membership reading
- `effectiveEpigraph_eq_epigraph_extendedRealRealPart`

Source/core/bridge triage:
- source-facing: the three specialized convexity predicates recalled below
- core/canonical: mathlib `ConvexOn`, `StrictConvexOn`, and `ConcaveOn`
- bridge/view: `extendedRealRealPart`, `effectiveEpigraph`, and their comparison lemmas

The textbook states these notions on `ℝⁿ`, but this derived bridge still uses no Euclidean
structure beyond the imported domain owner. This file therefore keeps the arbitrary-domain owner
style and records only the finite-real-part bridge plus the three canonical convexity recalls.
-/

/-- The finite real part of an extended-real-valued function, extended by `0` at `±∞`. -/
abbrev extendedRealRealPart {X : Type u} (f : X → EReal) : X → ℝ :=
  EReal.toReal ∘ f

/-- The effective epigraph of an extended-real-valued function, realized canonically as the real
epigraph of its finite real part over `dom f`. -/
abbrev effectiveEpigraph {X : Type u} (f : X → EReal) : Set (X × ℝ) :=
  {p | p.1 ∈ dom f ∧ extendedRealRealPart f p.1 ≤ p.2}

/-- Evaluating `extendedRealRealPart` simply applies `EReal.toReal` to `f x`. -/
@[simp] theorem extendedRealRealPart_eq_toReal {X : Type u} {f : X → EReal} {x : X} :
    extendedRealRealPart f x = (f x).toReal :=
  rfl

/-- On the finite-value domain, coercing the finite real part back to `EReal` recovers the
original extended-real value. -/
@[simp] theorem coe_extendedRealRealPart {X : Type u} {f : X → EReal} {x : X}
    (hx : x ∈ dom f) :
    ((extendedRealRealPart f x : ℝ) : EReal) = f x := by
  rcases mem_extendedRealEffectiveDomain_iff.mp hx with ⟨hx_top, hx_bot⟩
  simpa [extendedRealRealPart] using (EReal.coe_toReal hx_top hx_bot)

/-- On the finite-value domain, a real upper bound on `extendedRealRealPart f x` is exactly an
upper bound on `f x` by the corresponding real point of `EReal`. -/
theorem extendedRealRealPart_le_iff {X : Type u} {f : X → EReal} {x : X}
    (hx : x ∈ dom f) {r : ℝ} :
    extendedRealRealPart f x ≤ r ↔ f x ≤ (r : EReal) := by
  rw [← coe_extendedRealRealPart hx]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- On the finite-value domain, a real lower bound by `extendedRealRealPart f x` is exactly a
lower bound by the corresponding real point of `EReal`. -/
theorem le_extendedRealRealPart_iff {X : Type u} {f : X → EReal} {x : X}
    (hx : x ∈ dom f) {r : ℝ} :
    r ≤ extendedRealRealPart f x ↔ (r : EReal) ≤ f x := by
  rw [← coe_extendedRealRealPart hx]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- Membership in `effectiveEpigraph f` means belonging to the finite-value domain and lying
above the original extended-real value. -/
@[simp] theorem mem_effectiveEpigraph_iff {X : Type u} {f : X → EReal} {p : X × ℝ} :
    p ∈ effectiveEpigraph f ↔ p.1 ∈ dom f ∧ f p.1 ≤ p.2 :=
by
  constructor
  · rintro ⟨hp, hp₂⟩
    exact ⟨hp, (extendedRealRealPart_le_iff hp).1 hp₂⟩
  · rintro ⟨hp, hp₂⟩
    exact ⟨hp, (extendedRealRealPart_le_iff hp).2 hp₂⟩

/-- The effective epigraph of `f` is exactly the real epigraph of its finite real part over
`dom f`. -/
theorem effectiveEpigraph_eq_epigraph_extendedRealRealPart {X : Type u} (f : X → EReal) :
    effectiveEpigraph f = {p : X × ℝ | p.1 ∈ dom f ∧ extendedRealRealPart f p.1 ≤ p.2} := by
  rfl

section Convexity

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]

/-
Definition 3.1.1.3 (1): an `EReal`-valued function is convex when its finite real part is convex
on its effective domain. The chapter owner surface is the specialized mathlib predicate below.
-/
variable (f : X → EReal)

#check ConvexOn ℝ (dom f) (extendedRealRealPart f)

/- Definition 3.1.1.3 (2): an `EReal`-valued function is strictly convex when its finite real part
is strictly convex on the same effective domain. -/
#check StrictConvexOn ℝ (dom f) (extendedRealRealPart f)

/- Definition 3.1.1.3 (3): an `EReal`-valued function is concave when its finite real part is
concave on the same effective domain. -/
#check ConcaveOn ℝ (dom f) (extendedRealRealPart f)

end Convexity

end
