/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_5_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Text 6.1.1 lies in the chapter's Fenchel-conjugacy / effective-epigraph domain.

Primary domain:
- the source-facing Fenchel dual `f⋆`, its effective domain `dom (f⋆)`, and its effective
  epigraph `effectiveEpigraph (f⋆)` on a real inner-product space.

Mandatory domain-style sampling before refinement:
- `fenchelDual` and the notation `f⋆` in `Chap03/Definition_3_1_2_1`, the source-facing Fenchel
  dual owner on real inner-product spaces;
- `subdifferential` and the notation `∂ f(x)` in `Chap03/Definition_3_1_5`, the chapter owner for
  extended-valued subgradients;
- `effectiveEpigraph` and `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the chapter
  owners for the `EReal` effective epigraph and finite real part;
- `subdifferential_subset_dom_fenchelDual` in `Chap03/Theorem_3_1_5_2`, the canonical
  subdifferential-to-dual-domain bridge already used downstream in later Fenchel files.

Best owner abstraction:
- core/canonical: the chapter owner stack `f⋆`, `dom (f⋆)`, and `effectiveEpigraph (f⋆)`;
- bridge/view: `IsClosed (effectiveEpigraph (f⋆))`, `Convex ℝ (effectiveEpigraph (f⋆))`, and the
  domain corollary derived from `subdifferential_subset_dom_fenchelDual`.

Primitive data:
- `f : E → WithTop ℝ`;
- the point `x : E` for the subdifferential-domain inclusion.

Derived API in this file:
- the source-facing theorem that `effectiveEpigraph (f⋆)` is closed and convex;
- the domain nonemptiness corollary from a nonempty subdifferential.

Source/core/bridge triage:
- source-facing: the textbook claims about the effective epigraph of the Fenchel dual and the
  finiteness of the dual at subgradients;
- core/canonical: `f⋆`, `dom (f⋆)`, and the chapter owner stack around `effectiveEpigraph`;
- bridge/view: `effectiveEpigraph (f⋆)` and the subdifferential-domain inclusion.

The previous version kept an extra local companion for the owner-level convexity surface of `f⋆`.
That surface already belongs upstream in the Chapter 3 Fenchel stack, so this file now keeps only
the source-facing closed-convex epigraph statement together with the domain consequence needed in
later Chapter 5/6 Fenchel files.
-/

-- Proof sketch: a Fenchel conjugate is convex on its effective domain, and Theorem 3.1.1.2
-- converts that owner-level convexity into convexity of the effective epigraph; closedness is the
-- standard epigraph closedness property of conjugates.
/-- Helper for Text 6 1 1 Conjugate Closedness and Domain Nonemptiness: if `f` has empty effective
domain, then its Fenchel dual is identically `⊥`. -/
lemma fenchelDual_eq_bot_of_not_dom_nonempty
    {f : E → WithTop ℝ} (hdom : ¬ (dom f).Nonempty) :
    ∀ s : E, (f⋆) s = ⊥ := by
  intro s
  -- Outside `dom f`, every primal value is `⊤`, so each maximand in the Fenchel supremum is `⊥`.
  rw [fenchelDual_apply]
  refine le_antisymm ?_ bot_le
  refine iSup_le fun x ↦ ?_
  have hx_top : f x = ⊤ := by
    apply top_unique
    exact le_of_not_gt (fun hx ↦ hdom ⟨x, hx⟩)
  rw [hx_top]
  change (inner ℝ s x : EReal) - (⊤ : EReal) ≤ ⊥
  simp

/-- Helper for Text 6 1 1 Conjugate Closedness and Domain Nonemptiness: when `dom f` is nonempty,
membership in the effective epigraph of `f⋆` is equivalent to satisfying all support
halfspace inequalities. -/
lemma mem_effectiveEpigraph_fenchelDual_iff_forall_support_le
    {f : E → WithTop ℝ} (hdom : (dom f).Nonempty) {p : E × ℝ} :
    p ∈ effectiveEpigraph (f⋆) ↔
      ∀ x : E, (inner ℝ p.1 x : EReal) - withTopToEReal (f x) ≤ p.2 := by
  constructor
  · intro hp
    rcases mem_effectiveEpigraph_iff.mp hp with ⟨_, hp₂⟩
    -- Rewrite the dual value as a supremum and compare each support term with the epigraph height.
    rw [fenchelDual_apply] at hp₂
    exact fun x ↦
      le_trans
        (le_iSup (fun y : E ↦ (inner ℝ p.1 y : EReal) - withTopToEReal (f y)) x)
        hp₂
  · intro hp
    rcases hdom with ⟨x, hx⟩
    have hdual_le : (f⋆) p.1 ≤ p.2 := by
      -- The support inequalities exactly bound the defining supremum for `(f⋆) p.1`.
      rw [fenchelDual_apply]
      exact iSup_le hp
    have hdual_ne_top : (f⋆) p.1 ≠ ⊤ := by
      -- Any value bounded by the finite height `p.2` is not `⊤`.
      exact ne_of_lt (lt_of_le_of_lt hdual_le (by simp))
    have hdual_ne_bot : (f⋆) p.1 ≠ ⊥ :=
      fenchelDual_ne_bot_of_mem_dom (f := f) (s := p.1) hx
    -- The nonempty primal domain rules out `⊥`, and the support bounds rule out `⊤`.
    exact mem_effectiveEpigraph_iff.mpr
      ⟨(mem_extendedRealEffectiveDomain_iff).2 ⟨hdual_ne_top, hdual_ne_bot⟩, hdual_le⟩

/-- Helper for Text 6 1 1 Conjugate Closedness and Domain Nonemptiness: each Fenchel support
halfspace is closed and convex. -/
lemma fenchelDual_support_halfspace_closed_convex
    {f : E → WithTop ℝ} (x : E) :
    IsClosed {p : E × ℝ | (inner ℝ p.1 x : EReal) - withTopToEReal (f x) ≤ p.2} ∧
      Convex ℝ {p : E × ℝ | (inner ℝ p.1 x : EReal) - withTopToEReal (f x) ≤ p.2} := by
  by_cases hx : x ∈ dom f
  · let c : ℝ := withTopRealPart f x
    have hset :
        {p : E × ℝ | (inner ℝ p.1 x : EReal) - withTopToEReal (f x) ≤ p.2} =
          {p : E × ℝ | inner ℝ p.1 x ≤ p.2 + c} := by
      ext p
      -- On `dom f`, the `EReal` support inequality is just the corresponding real affine bound.
      rw [withTopToEReal_eq_coe_withTopRealPart_of_mem_dom (f := f) hx]
      constructor
      · intro hp
        have hp' : inner ℝ p.1 x - c ≤ p.2 := by
          exact_mod_cast hp
        exact (sub_le_iff_le_add).1 hp'
      · intro hp
        have hp' : inner ℝ p.1 x - c ≤ p.2 :=
          (sub_le_iff_le_add).2 hp
        exact_mod_cast hp'
    have hconv :
        ConvexOn ℝ Set.univ (fun s : E ↦ inner ℝ s x - c) := by
      -- The support slice is an affine real function, hence convex on the whole space.
      have hlin : ConvexOn ℝ Set.univ (fun s : E ↦ inner ℝ s x) := by
        simpa [real_inner_comm] using
          ((innerSL ℝ x).toLinearMap.convexOn (s := Set.univ) convex_univ)
      simpa [sub_eq_add_neg] using hlin.add_const (-c)
    have hcont : Continuous (fun s : E ↦ inner ℝ s x - c) := by
      -- The support slice is continuous because it is linear plus a constant.
      continuity
    constructor
    · -- The support halfspace is the preimage of a closed interval under a continuous affine map.
      rw [hset]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        IsClosed.epigraph isClosed_univ hcont.continuousOn
    · -- Convexity follows by checking the affine inequality on convex combinations.
      rw [hset]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hconv.convex_epigraph
  · have hx_top : f x = ⊤ := by
      have hx' : ¬ f x < ⊤ := by
        simpa [withTopEffectiveDomain] using hx
      exact top_unique (le_of_not_gt hx')
    have hset_univ :
        {p : E × ℝ | (inner ℝ p.1 x : EReal) - withTopToEReal (f x) ≤ p.2} = Set.univ := by
      ext p
      rw [hx_top]
      change ((inner ℝ p.1 x : EReal) - (⊤ : EReal) ≤ p.2) ↔ True
      simp
    constructor
    · -- Outside `dom f`, the support halfspace is all of `E × ℝ`.
      rw [hset_univ]
      exact isClosed_univ
    · -- The whole space is convex.
      rw [hset_univ]
      exact convex_univ

/-- Helper for Text 6 1 1 Conjugate Closedness and Domain Nonemptiness: when `dom f` is
nonempty, the effective epigraph of `f⋆` is the intersection of its support halfspaces. -/
lemma effectiveEpigraph_fenchelDual_eq_iInter_support_halfspaces
    {f : E → WithTop ℝ} (hdom : (dom f).Nonempty) :
    effectiveEpigraph (f⋆) =
      ⋂ x : E, {p : E × ℝ | (inner ℝ p.1 x : EReal) - withTopToEReal (f x) ≤ p.2} := by
  ext p
  -- Unpack epigraph membership into the family of support inequalities, then rewrite as `iInter`.
  rw [mem_effectiveEpigraph_fenchelDual_iff_forall_support_le (f := f) hdom]
  simp [Set.mem_setOf_eq]

/-- Text 6 1 1 Conjugate Closedness and Domain Nonemptiness: the Fenchel dual has a closed and
convex effective epigraph. The domain nonemptiness consequence is recorded separately below. -/
theorem fenchelDual_effectiveEpigraph_closed_convex
    (f : E → WithTop ℝ) :
    IsClosed (effectiveEpigraph (f⋆)) ∧
      Convex ℝ (effectiveEpigraph (f⋆)) := by
  by_cases hdom : (dom f).Nonempty
  · -- Rewrite the epigraph as an intersection of support halfspaces.
    rw [effectiveEpigraph_fenchelDual_eq_iInter_support_halfspaces (f := f) hdom]
    constructor
    · exact isClosed_iInter fun x ↦ (fenchelDual_support_halfspace_closed_convex (f := f) x).1
    · exact convex_iInter fun x ↦ (fenchelDual_support_halfspace_closed_convex (f := f) x).2
  · have hdual_bot : ∀ s : E, (f⋆) s = ⊥ :=
      fenchelDual_eq_bot_of_not_dom_nonempty (f := f) hdom
    have hepigraph_empty : effectiveEpigraph (f⋆) = (∅ : Set (E × ℝ)) := by
      ext p
      -- If `(f⋆)` is identically `⊥`, then its effective domain is empty.
      constructor
      · intro hp
        rcases mem_effectiveEpigraph_iff.mp hp with ⟨hpdom, _⟩
        exact (mem_extendedRealEffectiveDomain_iff.mp hpdom).2 (hdual_bot p.1)
      · intro hp
        exact False.elim hp
    -- The empty set is both closed and convex.
    rw [hepigraph_empty]
    exact ⟨isClosed_empty, convex_empty⟩

-- The owner-level `ConvexOn` surface for `f⋆` is already the canonical Chapter 3 API, so this
-- file does not keep a second local theorem for it.

-- Proof sketch: choose `g ∈ ∂ f(x)` from the nonempty subdifferential and apply the inclusion
-- theorem above.
/-- If some subdifferential of `f` is nonempty, then the effective domain of the Fenchel dual is
nonempty. -/
theorem dom_fenchelDual_nonempty_of_subdifferential_nonempty
    {f : E → WithTop ℝ} {x : E} (hsub : (∂ f(x)).Nonempty) :
    (dom (f⋆)).Nonempty := by
  rcases hsub with ⟨g, hg⟩
  -- A subgradient is automatically a finite point of the Fenchel dual.
  exact ⟨g, subdifferential_subset_dom_fenchelDual (f := f) (x := x) hg⟩

end
