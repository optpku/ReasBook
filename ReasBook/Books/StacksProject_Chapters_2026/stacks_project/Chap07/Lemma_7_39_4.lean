module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_17_2
public import stacks_project.Chap07.Lemma_7_38_5
public import stacks_project.Chap07.Proposition_7_39_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{max (u + 1) (v + 1)} C]

/- Domain-style sampling for Lemma 7.39.4:
- primary domain: enough points on a Grothendieck site via a family covering the terminal object
  and enough points on the corresponding slice sites;
- sampled owner API:
  `GrothendieckTopology.CoversTop`,
  `GrothendieckTopology.HasEnoughPoints`,
  `hasEnoughPoints_of_covering_family_and_slice_sites`,
  `hasEnoughPoints_of_finite_cover_refinement`;
- best owner abstraction: `J.HasEnoughPoints`, with the covering-family input expressed by the
  canonical owner `J.CoversTop U`;
- source/core/bridge triage:
  `source-facing`: this lemma combines a covering family of localizations with the slice-site
    finite-refinement hypothesis from Proposition 7.39.3;
  `core/canonical`: `J.HasEnoughPoints`, `J.CoversTop U`, and
    `(J.over (U i)).HasFiniteRefinementProperty`;
  `bridge/view`: Proposition 7.39.3 produces enough points on each slice site, and Lemma 7.38.5
    transports those slice points back to points of `(C, J)`.

Primitive data are only the canonical cover-family owner `J.CoversTop U` and the slice-site
finite-refinement hypotheses. The enough-points structure on each slice is derived API from
Proposition 7.39.3, so this file should stay a thin composition theorem rather than restating the
cover-family hypothesis in an ad hoc `∃ S : J.Cover W, ...` form.
-/
-- Proof sketch: the first hypothesis is the site-level form of the statement that the coproduct of
-- the representables `h_{U i}` surjects onto the terminal sheaf. For each `i`, apply Proposition
-- 7.39.3 to the slice site `(C / U i, J.over (U i))` to obtain enough points there; then use the
-- cover-family criterion from Lemma 7.38.5, and transport slice points back to points of `C` via
-- Lemma 7.34.2.
/-- Helper for Lemma 7.39.4: a site with finite limits and the finite-refinement property has
enough points. This is the local slice-site input supplied by Proposition 7.39.3. -/
lemma site_has_enough_points_of_finite_cover_refinement
    [Limits.HasFiniteLimits C]
    (hfinite : ∀ X : C, J.HasFiniteRefinementProperty X) :
    HasEnoughPoints.{max (u + 1) (v + 1)} J :=
by
  -- Apply Proposition 7.39.3 directly: finite refinement on the site produces enough points.
  simpa using hasEnoughPoints_of_finite_cover_refinement (J := J) hfinite

/-- Helper for Lemma 7.39.4: every slice site in the covering family has enough points once the
slice-site finite-refinement hypothesis is available. -/
lemma slice_sites_have_enough_points
    {I : Type (max (u + 1) (v + 1))} (U : I → C)
    [∀ i : I, Limits.HasFiniteLimits (Over (U i))]
    (hfinite : ∀ i : I, ∀ X : Over (U i), (J.over (U i)).HasFiniteRefinementProperty X) :
    ∀ i : I, HasEnoughPoints.{max (u + 1) (v + 1)} (J.over (U i)) := by
  intro i
  -- Apply the local finite-refinement theorem on the slice site indexed by `i`.
  simpa using site_has_enough_points_of_finite_cover_refinement
    (J := J.over (U i)) (hfinite := hfinite i)

/-- Lemma 7.39.4: if the family `U` covers the terminal object of `(C, J)` and each slice site
`(C / U i, J.over (U i))` satisfies the finite-limit and
finite-refinement hypotheses of Proposition 7.39.3, then `(C, J)` has enough points. -/
lemma hasEnoughPoints_of_covering_family_and_slice_finite_cover_refinement
    {I : Type (max (u + 1) (v + 1))} (U : I → C)
    (hcover : J.CoversTop U)
    [∀ i : I, Limits.HasFiniteLimits (Over (U i))]
    (hfinite : ∀ i : I, ∀ X : Over (U i), (J.over (U i)).HasFiniteRefinementProperty X) :
    HasEnoughPoints.{max (u + 1) (v + 1)} J := by
  -- The global enough-points statement follows once each slice site has enough points.
  apply hasEnoughPoints_of_covering_family_and_slice_sites U hcover
  -- Package the slice-site application of Proposition 7.39.3 into a single local family.
  exact slice_sites_have_enough_points (J := J) U hfinite

end CategoryTheory
