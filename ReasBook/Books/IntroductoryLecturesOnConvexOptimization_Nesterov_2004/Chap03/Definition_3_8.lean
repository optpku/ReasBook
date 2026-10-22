/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexAnalysis WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.8 is a `bridge/view` item in the chapter's Fenchel-conjugacy domain.

Primary domain:
- Fenchel duals of `ℝ ∪ {+∞}`-valued functions on real inner-product spaces.

Relevant owner-style declarations sampled before refinement:
- `fenchelDual` in `Definition_3_1_2_1`, the chapter's source-facing Fenchel-dual owner;
- `fenchelDual_apply` in `Definition_3_1_2_1`, the canonical inner-product-space supremum
  expansion;
- `withTopEffectiveDomain` and the notation `dom f` in `Definition_3_3`, the chapter owner for the
  effective domain `{x | f x < +∞}`;
- `fenchelConjugate` in `Chap06/Definition_6_1`, the core dual-space owner from which
  `fenchelDual` is derived.

Best owner abstraction:
- source-facing: `fenchelDual`, written `φ⋆`;
- core/canonical: `fenchelConjugate`;
- bridge/view: the effective-domain restriction of the supremum formula from `fenchelDual_apply`.

Primitive data:
- `φ : E → WithTop ℝ`.

Derived API:
- the recalled owner `fenchelDual` with notation `φ⋆`;
- the recalled evaluation theorem `fenchelDual_apply`;
- the source-faithful effective-domain expansion theorem below.

Source/core/bridge triage:
- source-facing: the textbook Fenchel dual `φ*`;
- core/canonical: `fenchelConjugate`;
- bridge/view: rewriting the supremum over all `x` as the same supremum over `dom φ`.

The source-facing owner is already present in the chapter as `fenchelDual`, so this file should
not keep a parallel low-level surface phrased directly in terms of
`fenchelConjugate ... (innerₗ _ _)`. The only extra mathematical content here is the textbook
observation that points with value `φ x = +∞` contribute `⊥`, so the supremum may be restricted to
the effective domain `dom φ`.
-/

section

variable (φ : E → WithTop ℝ)

/- Definition 3.8: the textbook Fenchel dual is the chapter owner `fenchelDual`, written `φ⋆`. -/
#check fenchelDual

/- The defining supremum formula is recalled through the canonical companion theorem
`fenchelDual_apply`. -/
#check fenchelDual_apply

variable (s : E)

/-- Helper for Definition 3.8: points outside the effective domain contribute `⊥` to the
Fenchel-dual maximand. -/
lemma fenchelDual_maximand_eq_bot_of_not_mem_dom
    {x : E} (hx : x ∉ dom φ) :
    ((inner ℝ s x : EReal) - withTopToEReal (φ x)) = ⊥ := by
  -- Outside `dom φ`, the function value is `⊤`, so the affine term becomes `x - ⊤ = ⊥`.
  have hx_top : φ x = ⊤ := by
    rw [mem_withTopEffectiveDomain_iff, not_lt_top_iff] at hx
    exact hx
  rw [hx_top]
  exact EReal.sub_top _

/-- Helper for Definition 3.8: removing the `⊥` terms outside `dom φ` does not change the
Fenchel-dual supremum. -/
lemma iSup_fenchelDual_maximand_eq_iSup_dom :
    (⨆ x : E, ((inner ℝ s x : EReal) - withTopToEReal (φ x))) =
      ⨆ x : dom φ, ((inner ℝ s x.1 : EReal) - withTopToEReal (φ x.1)) := by
  refine le_antisymm ?_ ?_
  · -- Every unrestricted term is either indexed by a domain point, or is `⊥` outside the domain.
    refine iSup_le ?_
    intro x
    by_cases hx : x ∈ dom φ
    · exact le_iSup
        (fun y : dom φ ↦ ((inner ℝ s y.1 : EReal) - withTopToEReal (φ y.1)))
        ⟨x, hx⟩
    · rw [fenchelDual_maximand_eq_bot_of_not_mem_dom (φ := φ) (s := s) hx]
      exact bot_le
  · -- Any domain point is also an index for the unrestricted supremum.
    refine iSup_le ?_
    intro x
    exact le_iSup (fun y : E ↦ ((inner ℝ s y : EReal) - withTopToEReal (φ y))) x.1

-- Proof sketch: expand `fenchelDual_apply`; if `φ x = ⊤`, then
-- `(inner ℝ s x : EReal) - withTopToEReal (φ x) = ⊥`, so those points do not affect the
-- supremum. The remaining points are exactly `dom φ`.
/-- Expanding the Fenchel dual gives the textbook supremum formula over the effective
domain `{x | φ x < +∞}`, written canonically as `dom φ`. -/
theorem fenchelDual_apply_eq_sSup_image_dom :
    (φ⋆) s =
      sSup ((fun x : E ↦ (inner ℝ s x : EReal) - withTopToEReal (φ x)) '' dom φ) := by
  calc
    (φ⋆) s = ⨆ x : E, ((inner ℝ s x : EReal) - withTopToEReal (φ x)) := by
      -- Start from the owner formula for `fenchelDual`.
      rw [fenchelDual_apply]
    _ = ⨆ x : dom φ, ((inner ℝ s x.1 : EReal) - withTopToEReal (φ x.1)) := by
      -- Restrict the supremum to the effective domain because the complementary terms are `⊥`.
      rw [iSup_fenchelDual_maximand_eq_iSup_dom (φ := φ) (s := s)]
    _ = sSup (Set.range fun x : dom φ ↦
        ((inner ℝ s x.1 : EReal) - withTopToEReal (φ x.1))) := by
      -- Convert the subtype-indexed `iSup` into the supremum over its range.
      rw [sSup_range]
    _ = sSup ((fun x : E ↦ (inner ℝ s x : EReal) - withTopToEReal (φ x)) '' dom φ) := by
      -- Identify the subtype range with the image of the maximand on `dom φ`.
      congr 1
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.1, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩

end

end
