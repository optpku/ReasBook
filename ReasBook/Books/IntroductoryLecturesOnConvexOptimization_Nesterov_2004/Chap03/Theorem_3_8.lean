/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped ConvexAnalysis WithTopConvexAnalysis

variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module ℝ X]
variable [AddCommMonoid Y] [Module ℝ Y]

/- Theorem 3.8 lies in the chapter's `WithTop`-to-`EReal` partial-infimal-projection domain.

Primary mathematical domain:
- constrained fiberwise infima of `WithTop ℝ`-valued convex objectives, expressed on the chapter's
  canonical `EReal` owner.

Relevant owner-style declarations sampled before refinement:
- `partialInfProjection` and `partialInfProjection_convexOn` in `Theorem_3_1_2_3`, the source
  owner and its canonical convexity theorem for real-valued fibers;
- `withTopToEReal`, `dom`, and `withTopRealPart` in `Definition_3_3`, the chapter bridge from
  `WithTop ℝ` data to the owner surface used by convexity statements;
- `extendedRealRealPart` in `Definition_3_1_1_3`, the finite-value bridge on the `EReal` owner;
- mathlib `ConvexOn`, the ambient canonical convexity owner.

Best owner abstraction:
- source-facing: the `WithTop` specialization of convexity for the canonical owner
  `partialInfProjection Q (withTopToEReal ∘ φ)`;
- core/canonical: `partialInfProjection_convexOn`;
- bridge/view: restricting the feasible set to `Q ∩ dom φ` and replacing `withTopToEReal ∘ φ` by
  `Real.toEReal ∘ withTopRealPart φ` on that intrinsic finite-value locus.

Primitive data:
- a convex feasible set `Q : Set (X × Y)`;
- a `WithTop ℝ`-valued objective `φ : X × Y → WithTop ℝ`;
- the convexity witness `ConvexOn ℝ (dom φ) (withTopRealPart φ)`.

Derived API:
- the theorem below, transporting the canonical real-valued infimal-projection convexity theorem
  to the chapter's `WithTop` surface.

Source/core/bridge triage:
- source-facing: Theorem 3.8's `WithTop`-valued partial-infimum convexity statement;
- core/canonical: `partialInfProjection_convexOn`;
- bridge/view: `withTopToEReal`, `withTopRealPart`, and the finite-locus restriction `Q ∩ dom φ`.

The source mathematics adds genuine `WithTop` bridge content, so this file should not collapse to
a pure recall of `partialInfProjection_convexOn`. The refinement instead keeps the source-facing
statement and removes the ad hoc proof gap by proving that points with value `⊤` do not alter the
fiber infimum, so the owner theorem applies directly on the intrinsic finite-value restriction.
-/

/-- Theorem 3.8: if `Q ⊆ X × Y` is convex and `φ : X × Y → ℝ ∪ {+∞}` is convex on its
effective domain, then the constrained partial infimum of the canonical `EReal` view
`withTopToEReal ∘ φ` is convex in the chapter's `EReal` sense. Internally one restricts to
`Q ∩ dom φ` to reuse the real-valued owner theorem, but that restriction is a proof device rather
than a public hypothesis. -/
theorem partialInfProjection_convexOn_of_convexWithTop
    {Q : Set (X × Y)} {φ : X × Y → WithTop ℝ}
    (hQ : Convex ℝ Q)
    (hφ : ConvexOn ℝ (dom φ) (withTopRealPart φ)) :
    ConvexOn ℝ (dom (partialInfProjection Q (withTopToEReal ∘ φ)))
      (extendedRealRealPart (partialInfProjection Q (withTopToEReal ∘ φ))) := by
  let Q' : Set (X × Y) := Q ∩ dom φ
  have hQ' : Convex ℝ Q' := hQ.inter hφ.1
  have hφ' : ConvexOn ℝ Q' (withTopRealPart φ) := by
    refine ⟨hQ', ?_⟩
    intro x hx y hy a b ha hb hab
    exact hφ.2 hx.2 hy.2 ha hb hab
  have hconv : ConvexOn ℝ (dom (partialInfProjection Q' (Real.toEReal ∘ withTopRealPart φ)))
      (extendedRealRealPart (partialInfProjection Q' (Real.toEReal ∘ withTopRealPart φ))) :=
    partialInfProjection_convexOn hQ' hφ'
  have hproj :
      partialInfProjection Q (withTopToEReal ∘ φ) =
        partialInfProjection Q' (Real.toEReal ∘ withTopRealPart φ) := by
    funext x
    let S : Set EReal := (withTopToEReal ∘ φ) '' {z : X × Y | z ∈ Q ∧ z.1 = x}
    let T : Set EReal := (Real.toEReal ∘ withTopRealPart φ) '' {z : X × Y | z ∈ Q' ∧ z.1 = x}
    have hTS : T ⊆ S := by
      intro a ha
      rcases ha with ⟨z, hz, rfl⟩
      refine ⟨z, ⟨hz.1.1, hz.2⟩, ?_⟩
      simpa [withTopToEReal] using
        (congrArg withTopToEReal (coe_withTopRealPart hz.1.2)).symm
    have hSinsert : S ⊆ insert ⊤ T := by
      intro a ha
      rcases ha with ⟨z, hz, rfl⟩
      by_cases hzdom : z ∈ dom φ
      · right
        refine ⟨z, ⟨⟨hz.1, hzdom⟩, hz.2⟩, ?_⟩
        simpa [withTopToEReal] using
          congrArg withTopToEReal (coe_withTopRealPart hzdom)
      · left
        rw [mem_withTopEffectiveDomain_iff, lt_top_iff_ne_top] at hzdom
        have hztop : φ z = ⊤ := by
          simpa using hzdom
        simpa [withTopToEReal] using congrArg withTopToEReal hztop
    change sInf S = sInf T
    refine le_antisymm (sInf_le_sInf hTS) ?_
    simpa using (sInf_le_sInf hSinsert : sInf (insert ⊤ T) ≤ sInf S)
  simpa [hproj] using hconv

end
