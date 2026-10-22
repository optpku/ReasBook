/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_39
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Proposition_15_24

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section AttouchBrezisTheorem

/-
Source/core/bridge triage:
- `source-facing`: Proposition 15.5 is the five-branch regularity condition on
  `effectiveDomain f - effectiveDomain g`.
- `core/canonical`: the Chapter 6 owner abstraction is
  `strongRelativeInteriorSubImageRegularity`, together with the origin-in-`sri` criterion
  `zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex`.
- `bridge/view`: clauses `(ii)` through `(v)` map directly to the identity-map specialization of
  the Chapter 6 owner. Clause `(i)` is kept in the source-facing closed-span form of
  Definition 6.9 and is discharged directly by the corresponding Chapter 6 criterion.
-/

/-- The five regularity alternatives used in Proposition 15.5. Clause `(i)` is the textbook
Attouch--Brézis strong-relative-interior condition
`cone (dom f - dom g) = closure (span (dom f - dom g))`. Clause `(iv)` uses the textbook
continuity set `cont f`, written in the local-domain continuity form provided by Corollary 8.39.
-/
def effectiveDomainStrongRelativeInteriorRegularity
    (f g : H → Set.Ioi (⊥ : EReal)) : Prop :=
  let S := effectiveDomain f - effectiveDomain g
  cone S = (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ H) : Set H) ∨
    (0 : H) ∈ core S ∨
    (0 : H) ∈ interior S ∨
    (∃ x ∈ effectiveDomain g, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball x ρ ⊆ effectiveDomain f ∧
      ContinuousAt (fun y : H ↦ (f y : EReal).toReal) x) ∨
    (FiniteDimensional ℝ H ∧ (ri (effectiveDomain f) ∩ ri (effectiveDomain g)).Nonempty)

set_option linter.style.longLine false in
private theorem continuousPoints_eq_interior_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    {y : H | ∃ σ : ℝ, 0 < σ ∧ Metric.ball y σ ⊆ effectiveDomain f ∧
      ContinuousAt (fun z : H ↦ (f z : EReal).toReal) y} = interior (effectiveDomain f) := by
  exact
    continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
      f
      hf.2
      (Or.inr <| Or.inl hf.1)

/-
Clause `(i)` now matches the Chapter 6 origin-in-`sri` criterion directly, while the owner bridge
below covers clauses `(ii)` through `(v)`. Those clauses are later branches of Proposition 6.19
for the identity map, and clause `(iv)` is converted to the interior-domain branch via
Corollary 8.39.
-/
/-- Bridge lemma: Proposition 15.5 clauses `(ii)` through `(v)` imply the Chapter 6 regularity
predicate used by Proposition 15.24 for the identity map. -/
private theorem tail_to_strongRelativeInteriorSubImageRegularity
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hreg :
      (0 : H) ∈ core (effectiveDomain f - effectiveDomain g) ∨
        (0 : H) ∈ interior (effectiveDomain f - effectiveDomain g) ∨
        (∃ x ∈ effectiveDomain g, ∃ ρ : ℝ, 0 < ρ ∧
          Metric.ball x ρ ⊆ effectiveDomain f ∧
          ContinuousAt (fun y : H ↦ (f y : EReal).toReal) x) ∨
        (FiniteDimensional ℝ H ∧
          (ri (effectiveDomain f) ∩ ri (effectiveDomain g)).Nonempty)) :
    strongRelativeInteriorSubImageRegularity (effectiveDomain g) (effectiveDomain f)
      (ContinuousLinearMap.id ℝ H) := by
  rcases hreg with hcore | hint | hcont | hri
  · dsimp [strongRelativeInteriorSubImageRegularity]
    refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ?_
    simpa using hcore
  · exact
      strongRelativeInteriorSubImageRegularity_of_zero_mem_interior (ContinuousLinearMap.id ℝ H)
        (by simpa using hint)
  · rcases hcont with ⟨x, hxg, ρ, hρ, hball, hxcont⟩
    have hx_int : x ∈ interior (effectiveDomain f) := by
      rw [← continuousPoints_eq_interior_of_mem_gammaZero hf]
      exact ⟨ρ, hρ, hball, hxcont⟩
    have hinter :
        ((ContinuousLinearMap.id ℝ H) '' effectiveDomain g ∩
          interior (effectiveDomain f)).Nonempty := by
      simpa using ⟨x, hxg, hx_int⟩
    dsimp [strongRelativeInteriorSubImageRegularity]
    exact
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| Or.inr hinter
  · dsimp [strongRelativeInteriorSubImageRegularity]
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| by
      simpa using hri

/-- Proposition 15.5: if `f` and `g` belong to `Γ₀(H)` and one of the five regularity
alternatives `(i)` through `(v)` holds, then the origin belongs to the strong relative interior of
`dom f - dom g`. The source also lists `dom f ∩ dom g ≠ ∅`, but the Chapter 6 route for clauses
`(ii)` through `(v)` makes that extra hypothesis redundant. Clause `(i)` is kept in the
closed-span form from Definition 6.9. -/
theorem zero_mem_strongRelativeInterior_sub_effectiveDomain_of_mem_gammaZero_of_regularity
    {f g : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hg : g ∈ Γ₀(H))
    (hreg : effectiveDomainStrongRelativeInteriorRegularity f g) :
    (0 : H) ∈ sri (effectiveDomain f - effectiveDomain g) := by
  rw [effectiveDomainStrongRelativeInteriorRegularity] at hreg
  rcases hreg with hcone | hreg
  · exact
      (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
        (hf.2.nonempty.sub hg.2.nonempty)
        (hf.2.convex_effectiveDomain.sub hg.2.convex_effectiveDomain)).2 hcone
  · have hregular :
        strongRelativeInteriorSubImageRegularity (effectiveDomain g) (effectiveDomain f)
          (ContinuousLinearMap.id ℝ H) :=
      tail_to_strongRelativeInteriorSubImageRegularity hf hreg
    simpa using
      (zero_mem_strongRelativeInterior_sub_image_effectiveDomain_of_owner_regularity
        hg.2.nonempty
        hf.2.nonempty
        hg.2.convex_effectiveDomain
        hf.2.convex_effectiveDomain
        (ContinuousLinearMap.id ℝ H) hregular)

end AttouchBrezisTheorem

end ERealFunction
