/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Theorem_3_8_10

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped FundamentalGroup
open Lean Elab Tactic Meta Term

universe u

namespace IsUniversalCoveringMap

variable {E B : Type u} [TopologicalSpace E] [LocPathConnectedSpace E] [TopologicalSpace B]
  {p : C(E, B)}

/-- Helper for Lemma 3.8.11: local path connectedness descends from a universal cover to the
base because the covering projection is a quotient map. -/
theorem universal_cover_base_locPathConnectedSpace
    (hp : IsUniversalCoveringMap p) :
    LocPathConnectedSpace B := by
  exact (hp.isCoveringMap.isQuotientMap hp.surjective).locPathConnectedSpace

/-- Helper for Lemma 3.8.11: the point obtained by applying the deck transformation attached to
`γ` to `e` still lies over `p e`. -/
theorem universal_cover_deck_aut_point_mem_fiber
    (hp : IsUniversalCoveringMap p) (e : E) (γ : FundamentalGroup B (p e)) :
    p (((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ) • e) = p e := by
  letI : LocPathConnectedSpace B := universal_cover_base_locPathConnectedSpace hp
  letI : SimplyConnectedSpace E := hp.simplyConnectedSpace
  letI : PathConnectedSpace E := inferInstance
  -- Evaluate the commutative triangle for the deck transformation corresponding to `γ`.
  have hcomm :=
    congrArg
      (fun f : TopCat.of E ⟶ TopCat.of B => f.hom e)
      (Over.w (((coveringSpaceAutMulEquivFundamentalGroup hp e).symm γ).hom))
  simpa [ContinuousMap.comp_apply] using hcomm

/-- Helper for Lemma 3.8.11: the quotient map `E → E / H` is a covering-space morphism from the
universal cover to the quotient covering over `B`. -/
noncomputable def universal_cover_orbit_quotient_map_hom
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    Over.mk (TopCat.ofHom p) ⟶
      Over.mk (TopCat.ofHom (universalCoverOrbitProjection hp e H)) :=
  Over.homMk
    (TopCat.ofHom
      (show C(E, universalCoverOrbit hp e H) from
        ⟨Quotient.mk'', continuous_quotient_mk'⟩))
    (by
      -- The quotient projection was defined by descending `p`, so the triangle commutes
      -- literally on representatives.
      ext x
      rfl)

/-- Helper for Lemma 3.8.11: the imported proof of Theorem 3.8.10 already computes the subgroup
associated to the canonical orbit point when the basepoint is written using `mapOfEq`. -/
theorem universal_cover_orbit_projection_mapOfEq_range_eq_subgroup
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    letI : SimplyConnectedSpace E := hp.simplyConnectedSpace
    letI : PathConnectedSpace E := inferInstance
    letI : LocPathConnectedSpace E := inferInstance
    letI := universalCoverDeckMulAction hp e
    (FundamentalGroup.mapOfEq
      (universalCoverOrbitProjection hp e H)
      (by
        change universalCoverOrbitProjection hp e H (universalCoverOrbitPoint hp e H) = p e
        rfl)).range = H := by
  -- Reuse the already-verified range computation from Theorem 3.8.10 instead of rebuilding the
  -- same orbit-stabilizer comparison in this single-item file.
  exact universalCoverOrbitProjection_range_eq_subgroup hp e ⟨H⟩

/-- Lemma 3.8.11: for the quotient covering `E / H → B` attached to a subgroup
`H ≤ π₁(B, p e)` of a universal cover, the subgroup associated to the canonical orbit class of
`e` is exactly `H`. -/
-- Proof sketch: identify the associated subgroup with the monodromy stabilizer of the canonical
-- orbit point in the fiber over `p e`, then compare that stabilizer with the stabilizer of the
-- identity coset in `π₁(B, p e) / H` via the restriction of the quotient map `E → E / H`.
theorem universalCoverOrbitProjection_associatedSubgroup_eq
    (hp : IsUniversalCoveringMap p) (e : E)
    (H : Subgroup (FundamentalGroup B (p e))) :
    (FundamentalGroup.map
      (universalCoverOrbitProjection hp e H) (universalCoverOrbitPoint hp e H)).range = H := by
  letI : LocPathConnectedSpace B := universal_cover_base_locPathConnectedSpace hp
  letI : SimplyConnectedSpace E := hp.simplyConnectedSpace
  letI : PathConnectedSpace E := inferInstance
  let hpH := universalCoverOrbitProjection_isPathConnectedCoveringMap hp e H
  let y0 : (universalCoverOrbitProjection hp e H) ⁻¹' ({p e} : Set B) :=
    ⟨universalCoverOrbitPoint hp e H, rfl⟩
  letI := IsPathConnectedCoveringMap.fiberMonodromyMulAction hpH (p e)
  have hmap_eq :
      FundamentalGroup.map
          (universalCoverOrbitProjection hp e H) (universalCoverOrbitPoint hp e H) =
        FundamentalGroup.mapOfEq
          (universalCoverOrbitProjection hp e H)
          (by
            change universalCoverOrbitProjection hp e H (universalCoverOrbitPoint hp e H) = p e
            rfl) := by
    -- The canonical orbit point already lies over `p e`, so the quotient-cover basepoint agrees
    -- with the `mapOfEq` convention used in the imported range computation.
    ext γ
    refine Quotient.inductionOn γ ?_
    intro r
    simpa using
      (FundamentalGroup.mapOfEq_apply
        (f := universalCoverOrbitProjection hp e H)
        (h := by
          change universalCoverOrbitProjection hp e H (universalCoverOrbitPoint hp e H) = p e
          rfl)
        (p := r)).symm
  -- Route correction: keep the source-faithful orbit-stabilizer argument from Theorem 3.8.10,
  -- but consume its completed `mapOfEq` range computation through the local wrapper above.
  calc
    (FundamentalGroup.map
      (universalCoverOrbitProjection hp e H) (universalCoverOrbitPoint hp e H)).range =
        (FundamentalGroup.mapOfEq
          (universalCoverOrbitProjection hp e H)
          (by
            change universalCoverOrbitProjection hp e H (universalCoverOrbitPoint hp e H) = p e
            rfl)).range := by
              rw [hmap_eq]
    _ = H := by
          simpa [hpH, y0] using
            universal_cover_orbit_projection_mapOfEq_range_eq_subgroup hp e H

end IsUniversalCoveringMap
