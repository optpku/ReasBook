module

import Mathlib.Tactic.Recall
public import Mathlib.Topology.JacobsonSpace

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set TopologicalSpace
open scoped TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

local macro "X₀" : term => `(closedPoints X)

/-
Domain-style sampling for Jacobson locality on open covers:
- chapter owner recall already established in `Definition_5_18_1`: `closedPoints X`,
  `JacobsonSpace X`
- same-domain mathlib owner companions: `jacobsonSpace_iff_locallyClosed`,
  `TopologicalSpace.IsOpenEmbedding.preimage_closedPoints`,
  `TopologicalSpace.IsOpenCover.jacobsonSpace_iff`

Layer triage:
- `source-facing`: Lemma 5.18.4, consisting of the open-cover Jacobson criterion together with the
  closed-point union conclusion `X₀ = ⋃ i, ((↑) : U i → X) '' closedPoints (U i)`
- `core/canonical`: the owner `JacobsonSpace X`
- `bridge/view`: the image of `closedPoints (U i)` in `X` along the open-subspace inclusion

Primitive data remains the owner `JacobsonSpace X`; the open-cover criterion is exact derived API.
The extra closed-point equality is source-facing companion data, so the file should recall the
owner theorem directly and add only the atomic bridge theorem needed for the “moreover” clause.
-/

/- Lemma 5.18.4 is the canonical owner-level locality theorem for Jacobson spaces on open covers. -/
recall IsOpenCover.jacobsonSpace_iff {ι : Type*} {U : ι → Opens X} (hU : IsOpenCover U) :
  JacobsonSpace X ↔ ∀ i, JacobsonSpace (U i)

namespace TopologicalSpace.IsOpenCover

/-- Lemma 5.18.4 (moreover): in a Jacobson space, the closed points are exactly the union of the
closed points of any open cover members, viewed in `X` via the subtype inclusions. -/
theorem closedPoints_eq_iUnion_image {ι : Type*} {U : ι → Opens X} [JacobsonSpace X]
    (hU : IsOpenCover U) :
    X₀ = ⋃ i, ((↑) : U i → X) '' closedPoints (U i) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hix⟩ := hU.exists_mem x
    refine mem_iUnion.2 ⟨i, ⟨⟨x, hix⟩, ?_, rfl⟩⟩
    have hpre : ((↑) : U i → X) ⁻¹' X₀ = closedPoints (U i) :=
      (U i).2.isOpenEmbedding_subtypeVal.preimage_closedPoints
    have hx' : (⟨x, hix⟩ : U i) ∈ ((↑) : U i → X) ⁻¹' X₀ := by
      simpa using hx
    simpa [hpre] using hx'
  · intro hx
    rcases mem_iUnion.1 hx with ⟨i, hx⟩
    rcases hx with ⟨y, hy, rfl⟩
    have hpre : ((↑) : U i → X) ⁻¹' X₀ = closedPoints (U i) :=
      (U i).2.isOpenEmbedding_subtypeVal.preimage_closedPoints
    have hy' : y ∈ ((↑) : U i → X) ⁻¹' X₀ := by
      simpa [hpre] using hy
    simpa using hy'

/-- Source-style corollary of Lemma 5.18.4 (moreover): if the cover members are Jacobson, then the
same closed-point union formula holds. -/
theorem closedPoints_eq_iUnion_image_of_forall_jacobson {ι : Type*} {U : ι → Opens X}
    (hU : IsOpenCover U) (hJacobson : ∀ i, JacobsonSpace (U i)) :
    X₀ = ⋃ i, ((↑) : U i → X) '' closedPoints (U i) := by
  let _ : JacobsonSpace X := hU.jacobsonSpace_iff.2 hJacobson
  simpa using hU.closedPoints_eq_iUnion_image

end TopologicalSpace.IsOpenCover
