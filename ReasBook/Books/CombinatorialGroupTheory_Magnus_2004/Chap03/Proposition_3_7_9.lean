/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_5_3
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_4
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_7_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped BigOperators

set_option autoImplicit false

section

/-!
Primary domain: finite-index subgroups of `F`-groups and the Section `7` Fuchsian measure.

Layer triage:
- `source-facing`: an `F`-group `G`, a finite-index subgroup `H ≤ G`, and the textbook quantity
  `μ(G)` attached to an `F`-group in the Fuchsian-complex discussion.
- `core/canonical`: `IsFGroup` from Definition `3-5-3`, `Subgroup.FiniteIndex` and
  `Subgroup.index` from mathlib, and the standard orientable/nonorientable surface presentations
  from Proposition `3-5-4`.
- `bridge/view`: the scalar `μ(G)` is not an earlier chapter owner, so this file keeps only the
  thin bridge from the standard surface-presentation owners in Proposition `3-5-4` to the
  rational value computed from their signatures.

Domain sampling:
1. `IsFGroup` is the existing project owner predicate for the source notion of an `F`-group.
2. `Subgroup.FiniteIndex` and `Subgroup.index` are mathlib's owner API for subgroup index.
3. `FGroupPresentation.orientableStandardRelators` and
   `FGroupPresentation.nonorientableStandardRelators` from Proposition `3-5-4` are the chapter's
   canonical standard-presentation owners for `F`-groups.
4. Finite sums over the torsion exponents naturally live in `ℚ`, so the Section `7` measure is
   recorded as a rational number.

Best owner abstraction: the finite-index proposition should be stated directly over
`Subgroup.FiniteIndex`, `Subgroup.index`, and `FGroupPresentation.IsMeasure`; the source-facing
main equality is the multiplicative relation `μ(H) = index(H) * μ(G)`, while the ratio form is
only a derived companion when `μ(G) ≠ 0`.

Primitive vs. derived:
- primitive data: the subgroup `H` and the standard surface-presentation witnesses for the two
  measure values `μ(G)` and `μ(H)`;
- derived API: the bridge from a standard surface presentation to `IsFGroup`, the source-facing
  multiplicative finite-index formula `μ(H) = index(H) * μ(G)`, and the ratio formula only as the
  nonzero-denominator companion. No extra wrapper structure for finite-index Fuchsian subgroups is
  introduced.
-/

variable {G : Type u} [Group G]

namespace FGroupPresentation

/-- The torsion contribution `∑ (1 - 1 / mᵢ)` occurring in the standard Fuchsian measure formula
for an `F`-group presentation. -/
private def torsionContribution {p : ℕ} (m : Fin p → ℕ) : ℚ :=
  ∑ i, ((1 : ℚ) - (m i : ℚ)⁻¹)

/-- The Section `7` Fuchsian measure of an orientable standard presentation with `p` cone points,
genus `g`, and torsion exponents `m`. -/
def orientableMeasure (p g : ℕ) (m : Fin p → ℕ) : ℚ :=
  (2 : ℚ) * g - 2 + torsionContribution m

/-- The Section `7` Fuchsian measure of a nonorientable standard presentation with `p` cone
points, nonorientable genus `g`, and torsion exponents `m`. -/
def nonorientableMeasure (p g : ℕ) (m : Fin p → ℕ) : ℚ :=
  (g : ℚ) - 2 + torsionContribution m

/-- A rational number `μ` is a Fuchsian measure for `G` when `G` admits one of the standard
surface presentations of Proposition `3-5-4` whose signature yields the value `μ`. -/
def IsMeasure (G : Type u) [Group G] (μ : ℚ) : Prop :=
  (∃ (p g : ℕ) (m : Fin p → ℕ),
    (∃ _ : PresentedGroup (orientableStandardRelators p g m) ≃* G,
      ∀ i, 1 < m i) ∧
    μ = orientableMeasure p g m) ∨
  (∃ (p g : ℕ) (m : Fin p → ℕ),
    (∃ _ : PresentedGroup (nonorientableStandardRelators p g m) ≃* G,
      ∀ i, 1 < m i) ∧
    μ = nonorientableMeasure p g m)

/-- Any group carrying a Fuchsian measure is an `F`-group, since such a measure is defined from a
standard surface presentation of the type furnished in Proposition `3-5-4`. -/
-- Proof sketch: discard the scalar equality in the definition of `IsMeasure G μ`, retaining only
-- the underlying standard surface-presentation witness, and invoke
-- `isFGroup_of_standardSurfacePresentation`.
theorem IsMeasure.isFGroup {μ : ℚ} (hμ : IsMeasure G μ) :
    IsFGroup G := by
  rcases hμ with hμ | hμ
  · rcases hμ with ⟨p, g, m, hpres, _⟩
    exact isFGroup_of_standardSurfacePresentation <| Or.inl ⟨p, g, m, hpres⟩
  · rcases hμ with ⟨p, g, m, hpres, _⟩
    exact isFGroup_of_standardSurfacePresentation <| Or.inr ⟨p, g, m, hpres⟩

end FGroupPresentation

open FGroupPresentation

variable (H : Subgroup G) [H.FiniteIndex] {μG μH : ℚ}

/-- Proposition 3-7-9: if `H` is a finite-index subgroup of the `F`-group `G`, then Proposition
`3-7-4` makes `H` into an `F`-group again, and any Section `7` Fuchsian measures `μ(G)` and
`μ(H)` satisfy the multiplicative index formula `μ(H) = index(H) * μ(G)`. -/
-- Proof sketch: Proposition `3-7-4` gives that a finite-index subgroup of an `F`-group is again
-- an `F`-group. Choose a Fuchsian complex for `G` and the induced Fuchsian complex for `H`; each
-- face of the latter is a union of exactly `index(H)` faces of the former. By the additivity of
-- the associated area measure from Corollary `3-7-6`, the face areas differ by the same factor,
-- and canceling the common factor `2π` gives the stated proportionality between the corresponding
-- Fuchsian measures.
theorem finiteIndex_subgroup_fuchsianMeasure_eq_index_mul
    (hμG : IsMeasure G μG) (hμH : IsMeasure H μH) :
    μH = (H.index : ℚ) * μG := sorry

/-- The division form of Proposition `3-7-9` is a derived corollary once `μ(G) ≠ 0`. -/
theorem finiteIndex_subgroup_index_eq_fuchsianMeasure_ratio
    (hμG : IsMeasure G μG) (hμH : IsMeasure H μH) (hμG0 : μG ≠ 0) :
    (H.index : ℚ) = μH / μG := by
  exact (eq_div_iff hμG0).2 <| by
    simpa [mul_comm] using (finiteIndex_subgroup_fuchsianMeasure_eq_index_mul H hμG hμH).symm

end
