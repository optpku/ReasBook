module

public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Separation.Hausdorff
import stacks_project.Chap05.Lemma_5_25_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Cardinal Function Set

/- Domain-style sampling for Remark 5.26.10:
- primary domain: dense sections of minimal surjections and the resulting Hausdorff cardinal bounds
- sampled owner declarations:
  `Function.surjInv`
  `Function.rightInverse_surjInv`
  `DenseRange`
  `cardinalMk_le_powerpower_of_denseRange`
- best owner abstraction: the section data already has the canonical owner `Function.surjInv`;
  dense range and the cardinal estimate are derived API on top of that owner
- primitive data: a surjective map `f : X' → X` together with the proper-closed-image minimality
  condition on subsets of `X'`
- derived API: the canonical section `surjInv hsurj` has dense range, and for Hausdorff `X'` this
  feeds into `cardinalMk_le_powerpower_of_denseRange`

Layer triage:
- `source-facing`: the cardinal estimate of Remark 5.26.10
- `core/canonical`: `Function.surjInv`, `Function.rightInverse_surjInv`, and `DenseRange`
- `bridge/view`: `denseRange_surjInv_of_minimal_surjective`

The existential helper is duplicate wheel API: once `hsurj` is fixed, the relevant section already
has the canonical owner `surjInv hsurj`, so the refined file should prove properties of that owner
directly and derive the cardinal bound from the chapter owner
`cardinalMk_le_powerpower_of_denseRange`.
-/

section

variable {X : Type u} {X' : Type v} [TopologicalSpace X']

/-- The canonical right inverse of a minimal surjection has dense range. -/
theorem denseRange_surjInv_of_minimal_surjective
    (f : X' → X) (hsurj : Surjective f)
    (hminimal :
      ∀ Z : Set X', Z ≠ (Set.univ : Set X') → IsClosed Z → f '' Z ≠ (Set.univ : Set X)) :
    DenseRange (surjInv hsurj) := by
  rw [denseRange_iff_closure_range]
  by_contra hclosure
  have hproper : closure (range (surjInv hsurj)) ≠ (univ : Set X') := by
    simpa using hclosure
  have himage : f '' closure (range (surjInv hsurj)) = (univ : Set X) := by
    refine eq_univ_iff_forall.mpr fun x ↦ ?_
    refine ⟨surjInv hsurj x, subset_closure ?_, surjInv_eq hsurj x⟩
    exact ⟨x, rfl⟩
  exact hminimal _ hproper isClosed_closure himage

end

section

variable {X : Type u} {X' : Type v} [TopologicalSpace X'] [T2Space X']

-- Proof sketch: the minimality hypothesis forces the canonical section `surjInv hsurj : X → X'`
-- to have dense range. Apply the chapter owner theorem
-- `cardinalMk_le_powerpower_of_denseRange` to that section and then use monotonicity in `κ`.
/-- Remark 5.26.10: if `|X| ≤ κ` and `f : X' → X` is a minimal surjection, then
`|X'| ≤ 2 ^ (2 ^ κ)`. The compactness, Hausdorff, and extremal-disconnectedness assumptions from
the textbook are not needed for this cardinal estimate once the minimality hypothesis is given. -/
theorem cardinalMk_le_powerpower_of_minimal_surjective
    (f : X' → X) (hsurj : Surjective f)
    (hminimal :
      ∀ Z : Set X', Z ≠ (Set.univ : Set X') → IsClosed Z → f '' Z ≠ (Set.univ : Set X))
    (κ : Cardinal.{max u v}) (hκX : Cardinal.lift (Cardinal.mk X) ≤ κ) :
    Cardinal.lift (Cardinal.mk X') ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ κ) := by
  calc
    Cardinal.lift (Cardinal.mk X') ≤
        (2 : Cardinal) ^ ((2 : Cardinal) ^ Cardinal.lift (Cardinal.mk X)) := by
      simpa using
        (cardinalMk_le_powerpower_of_denseRange
          (denseRange_surjInv_of_minimal_surjective f hsurj hminimal))
    _ ≤ (2 : Cardinal) ^ ((2 : Cardinal) ^ κ) := by
      exact power_le_power_left two_ne_zero (power_le_power_left two_ne_zero hκX)

end
