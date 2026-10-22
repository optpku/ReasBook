/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Construction_3_8_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Path.Homotopic.Quotient
open TopologicalSpace
open TopologicalSpace.OpenNhdsOf
open scoped UniversalCover

variable {B : Type u} [TopologicalSpace B]

/-- The endpoint of a point in a universal-cover basic set lies in the chosen neighborhood. -/
-- Proof sketch: unpack membership in `universalCoverCandidateBasicSet`; the witness
-- `y : U` occurring in the definition has endpoint `y.1`, and the defining equality of the basic
-- set identifies this endpoint with the first component of `r`.
theorem universalCoverCandidateBasicSet_endpoint_mem
    (b : B) (q : universalCoverCandidate b) (U : OpenNhdsOf q.1)
    {r : universalCoverCandidate b} (hr : r ∈ U[q]) :
    r.1 ∈ (U : Set B) := sorry

/-- The class obtained by extending `q` with a path in `U` belongs to the associated basic set. -/
-- Proof sketch: use the defining witnesses `y := u` and `c` in the definition of
-- `universalCoverCandidateBasicSet`, with the displayed class as the required endpoint-fixed
-- homotopy class.
theorem universalCoverCandidateBasicSet_pathClass_mem
    (b : B) (q : universalCoverCandidate b) (U : OpenNhdsOf q.1)
    (u : U) (c : Path ⟨q.1, U.mem⟩ u) :
    (⟨u.1, q.2.trans ((mk c).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))⟩ :
      universalCoverCandidate b) ∈ U[q] :=
  sorry

/-- Any two paths in a neighborhood with trivial induced based fundamental-group map determine the
same point of the universal-cover candidate. -/
-- Proof sketch: if the inclusion `U ↪ B` induces the trivial map on the based fundamental group
-- at `q.1`, then the loop obtained by traversing `c₁` and then `c₂⁻¹` is null-homotopic in `B`.
-- Hence the two concatenated path classes represent the same point of the universal-cover
-- candidate.
theorem universalCoverCandidate_pathClass_eq_of_paths
    (b : B) (q : universalCoverCandidate b) (U : OpenNhdsOf q.1)
    (htriv : FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B))
      ⟨q.1, U.mem⟩ = 1)
    (u : U) (c₁ c₂ : Path ⟨q.1, U.mem⟩ u) :
    (⟨u.1, q.2.trans ((mk c₁).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))⟩ :
      universalCoverCandidate b) =
      ⟨u.1, q.2.trans ((mk c₂).map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, B)))⟩ := sorry

/-- The endpoint projection restricted to a universal-cover basic set. -/
def universalCoverCandidateBasicSet_projectionToNeighborhood
    (b : B) (q : universalCoverCandidate b) (U : OpenNhdsOf q.1) :
    {r // r ∈ U[q]} → U
  | ⟨r, hr⟩ => ⟨r.1, universalCoverCandidateBasicSet_endpoint_mem b q U hr⟩

@[simp] theorem universalCoverCandidateBasicSet_projectionToNeighborhood_apply
    (b : B) (q : universalCoverCandidate b) (U : OpenNhdsOf q.1)
    (r : {r // r ∈ U[q]}) :
    (universalCoverCandidateBasicSet_projectionToNeighborhood b q U r : B) = r.1.1 := rfl

/-- Lemma 3.8.5: for a suitable basic set `U[f]`, the endpoint projection restricts to an open
embedding onto `U`; equivalently, the explicit restricted endpoint map is a homeomorphism onto
`U`. -/
-- Proof sketch: surjectivity follows from path connectedness of `U`, since every `u : U` is
-- joined to the endpoint of `q` by a path producing a point of the basic set above `u`.
-- Injectivity comes from `universalCoverCandidate_pathClass_eq_of_paths`, using that the
-- inclusion `U ↪ B` kills based loops. Openness and continuity are checked on the basis
-- `universalCoverCandidateBasicSets b`, so the restricted endpoint map is a homeomorphism onto
-- `U`.
theorem universalCoverCandidateBasicSet_projectionToNeighborhood_homeomorphic
    (b : B) (q : universalCoverCandidate b) (U : OpenNhdsOf q.1)
    (hU : U.IsSuitableForUniversalCover) :
    IsHomeomorph (universalCoverCandidateBasicSet_projectionToNeighborhood b q U) := sorry
