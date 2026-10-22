/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 3.3 is the chapter's `WithTop`-valued convex-analysis bridge.

Sampled owner-style declarations:
- mathlib `WithTop.untop₀`
- mathlib `ConvexOn`
- mathlib `StrictConvexOn`
- mathlib `ConcaveOn`

Best owner abstraction:
- primitive bridge data: `withTopEffectiveDomain`, `withTopToEReal`, `withTopRealPart`,
  `constrainedSublevelSet`, `constrainedEpigraph`, and the source-facing owner
  `WithTopConvexAnalysis.effectiveEpigraph`
- core/canonical convexity owners:
  `ConvexOn ℝ (dom f) (withTopRealPart f)`,
  `StrictConvexOn ℝ (dom f) (withTopRealPart f)`, and
  `ConcaveOn ℝ (dom f) (withTopRealPart f)`

Primitive data:
- the finite-value domain `dom f`
- the canonical `EReal` image `withTopToEReal`
- the finite real representative `withTopRealPart f`
- the constrained real sublevel set `constrainedSublevelSet Q f β`
- the constrained epigraph `constrainedEpigraph Q f`
- the effective epigraph owner `WithTopConvexAnalysis.effectiveEpigraph f`

Derived API:
- `mem_withTopEffectiveDomain_iff`
- `withTopToEReal`
- `coe_withTopRealPart`
- `withTopRealPart_eq_untop`
- `withTopRealPart_le_iff`
- `le_withTopRealPart_iff`
- `mem_constrainedSublevelSet_iff`
- `mem_constrainedEpigraph_iff`
- `WithTopConvexAnalysis.mem_effectiveEpigraph_iff`
- `WithTopConvexAnalysis.effectiveEpigraph_eq_epigraph_withTopRealPart`
- `constrainedEpigraph_eq_prod_univ_inter_of_subset`

Source/core/bridge triage:
- source-facing: the chapter's `WithTop`-valued convexity vocabulary from Definition 3.3
- core/canonical: mathlib `ConvexOn`, `StrictConvexOn`, `ConcaveOn`
- bridge/view: `withTopEffectiveDomain`, `withTopRealPart`, `constrainedEpigraph`, and
  `WithTopConvexAnalysis.effectiveEpigraph`

The textbook states these notions on `ℝⁿ`, but the bridge data itself does not use any Euclidean
structure. This file therefore keeps the same semantics while exposing the owner bridge on an
arbitrary domain type, with the textbook notation `dom f` on the theorem surface, while the three
convexity clauses are recalled directly from the canonical mathlib owners instead of being
repackaged as new predicate names.
-/

/-- The effective domain of an `ℝ ∪ {+∞}`-valued function, i.e. the points where the value is
finite. -/
abbrev withTopEffectiveDomain {X : Type u} (f : X → WithTop ℝ) : Set X :=
  {x | f x < ⊤}

/-- Textbook notation for the effective domain of an `ℝ ∪ {+∞}`-valued function. -/
scoped[WithTopConvexAnalysis] notation "dom " f:arg => withTopEffectiveDomain f

open scoped WithTopConvexAnalysis

/-- The canonical embedding of `ℝ ∪ {+∞}` into `[-∞, +∞]`. -/
abbrev withTopToEReal : WithTop ℝ → EReal := ((↑) : WithTop ℝ → WithBot (WithTop ℝ))

/-- The real-valued representative of an `ℝ ∪ {+∞}`-valued function, obtained by reading off its
finite value on the effective domain and extending by `0` outside that domain. -/
abbrev withTopRealPart {X : Type u} (f : X → WithTop ℝ) : X → ℝ :=
  WithTop.untop₀ ∘ f

/-- A point lies in the effective domain exactly when the function value is finite there. -/
@[simp] theorem mem_withTopEffectiveDomain_iff {X : Type u} {f : X → WithTop ℝ} {x : X} :
    x ∈ dom f ↔ f x < ⊤ :=
  Iff.rfl

/-- On the effective domain, the real-valued representative agrees with the underlying finite
real value of the function. -/
theorem withTopRealPart_eq_untop {X : Type u} {f : X → WithTop ℝ} {x : X}
    (hx : x ∈ dom f) :
    withTopRealPart f x = (f x).untop (ne_of_lt hx) := by
  have hne : f x ≠ ⊤ := ne_of_lt hx
  apply WithTop.coe_injective
  simpa [withTopRealPart] using WithTop.coe_untop₀_of_ne_top hne

/-- On the effective domain, coercing the finite real part back to `WithTop ℝ` recovers the
original function value. -/
@[simp] theorem coe_withTopRealPart {X : Type u} {f : X → WithTop ℝ} {x : X}
    (hx : x ∈ dom f) :
    ((withTopRealPart f x : ℝ) : WithTop ℝ) = f x := by
  simpa [withTopRealPart] using WithTop.coe_untop₀_of_ne_top (ne_of_lt hx)

/-- On the effective domain, a real upper bound on `withTopRealPart f x` is exactly an upper
bound on `f x` by the corresponding real point of `WithTop ℝ`. -/
theorem withTopRealPart_le_iff {X : Type u} {f : X → WithTop ℝ} {x : X}
    (hx : x ∈ dom f) {r : ℝ} :
    withTopRealPart f x ≤ r ↔ f x ≤ (r : WithTop ℝ) := by
  rw [← coe_withTopRealPart hx]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- On the effective domain, a real lower bound by `withTopRealPart f x` is exactly a lower bound
by the corresponding real point of `WithTop ℝ`. -/
theorem le_withTopRealPart_iff {X : Type u} {f : X → WithTop ℝ} {x : X}
    (hx : x ∈ dom f) {r : ℝ} :
    r ≤ withTopRealPart f x ↔ (r : WithTop ℝ) ≤ f x := by
  rw [← coe_withTopRealPart hx]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- The epigraph of an `ℝ ∪ {+∞}`-valued function constrained to a feasible set `Q`. -/
abbrev constrainedEpigraph {X : Type u} (Q : Set X) (f : X → WithTop ℝ) : Set (X × ℝ) :=
  {p | p.1 ∈ Q ∧ f p.1 ≤ p.2}

/-- The constrained real sublevel set of an `ℝ ∪ {+∞}`-valued function over a feasible set `Q`.
-/
abbrev constrainedSublevelSet {X : Type u}
    (Q : Set X) (f : X → WithTop ℝ) (β : ℝ) : Set X :=
  {x | x ∈ Q ∧ f x ≤ β}

/-- Membership in `constrainedSublevelSet Q f β` means belonging to `Q` and satisfying the
sublevel inequality `f x ≤ β`. -/
@[simp] theorem mem_constrainedSublevelSet_iff
    {X : Type u} {Q : Set X} {f : X → WithTop ℝ} {β : ℝ} {x : X} :
    x ∈ constrainedSublevelSet Q f β ↔ x ∈ Q ∧ f x ≤ β :=
  Iff.rfl

/-- Membership in the constrained epigraph means lying in `Q` and being above the function
value. -/
@[simp] theorem mem_constrainedEpigraph_iff
    {X : Type u} {Q : Set X} {f : X → WithTop ℝ} {p : X × ℝ} :
    p ∈ constrainedEpigraph Q f ↔ p.1 ∈ Q ∧ f p.1 ≤ p.2 :=
  Iff.rfl

namespace WithTopConvexAnalysis

/-- The effective epigraph of an `ℝ ∪ {+∞}`-valued function. -/
abbrev effectiveEpigraph {X : Type u} (f : X → WithTop ℝ) : Set (X × ℝ) :=
  constrainedEpigraph (dom f) f

/-- Membership in `effectiveEpigraph f` means belonging to the effective domain and lying above
the original `WithTop ℝ`-valued function. -/
@[simp] theorem mem_effectiveEpigraph_iff
    {X : Type u} {f : X → WithTop ℝ} {p : X × ℝ} :
    p ∈ effectiveEpigraph f ↔ p.1 ∈ dom f ∧ f p.1 ≤ p.2 :=
  Iff.rfl

/-- The effective epigraph of `f` is exactly the ordinary epigraph of its finite real part over
`dom f`. -/
theorem effectiveEpigraph_eq_epigraph_withTopRealPart
    {X : Type u} (f : X → WithTop ℝ) :
    effectiveEpigraph f = {p : X × ℝ | p.1 ∈ dom f ∧ withTopRealPart f p.1 ≤ p.2} := by
  ext p
  constructor
  · rintro ⟨hp, hp₂⟩
    exact ⟨hp, (withTopRealPart_le_iff hp).2 hp₂⟩
  · rintro ⟨hp, hp₂⟩
    exact ⟨hp, (withTopRealPart_le_iff hp).1 hp₂⟩

end WithTopConvexAnalysis

/-- Restricting the feasible set from `Q` to a subset `Q₁` cuts the constrained epigraph by the
corresponding base cylinder. -/
theorem constrainedEpigraph_eq_prod_univ_inter_of_subset
    {X : Type u} {Q Q₁ : Set X} {f : X → WithTop ℝ} (hQ₁Q : Q₁ ⊆ Q) :
    constrainedEpigraph Q₁ f = (Q₁ ×ˢ (Set.univ : Set ℝ)) ∩ constrainedEpigraph Q f := by
  ext p
  constructor
  · rintro ⟨hpQ₁, hfp⟩
    refine ⟨?_, ?_⟩
    · simpa [Set.mem_prod] using And.intro hpQ₁ (Set.mem_univ p.2)
    · exact mem_constrainedEpigraph_iff.2 ⟨hQ₁Q hpQ₁, hfp⟩
  · rintro ⟨hpQ₁, hp⟩
    rw [Set.mem_prod] at hpQ₁
    exact mem_constrainedEpigraph_iff.2 ⟨hpQ₁.1, (mem_constrainedEpigraph_iff.1 hp).2⟩

section Convexity

variable {X : Type u} [AddCommMonoid X] [Module ℝ X]
variable (f : X → WithTop ℝ)

/- Definition 3.3 (1), generalized from the textbook `ℝⁿ` setting: an `ℝ ∪ {+∞}`-valued
function is convex when its effective domain is convex and its finite-value part satisfies the
Jensen inequality there. -/
#check ConvexOn ℝ (dom f) (withTopRealPart f)

/- Definition 3.3 (2), generalized from the textbook `ℝⁿ` setting: an `ℝ ∪ {+∞}`-valued
function is strictly convex when its effective domain is convex and its finite-value part
satisfies the strict Jensen inequality there. -/
#check StrictConvexOn ℝ (dom f) (withTopRealPart f)

/- Definition 3.3 (3), generalized from the textbook `ℝⁿ` setting: an `ℝ ∪ {+∞}`-valued
function is concave when its finite-value part is concave on the same effective domain. -/
#check ConcaveOn ℝ (dom f) (withTopRealPart f)

end Convexity
