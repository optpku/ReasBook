/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_19
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_21
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_39
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise Topology

universe u v

namespace ERealFunction

section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 15.24 is the ten-branch regularity statement for
  `effectiveDomain g - L '' effectiveDomain f`.
- `core/canonical`: the owner abstraction is Chapter 6's
  `strongRelativeInteriorSubImageRegularity` together with
  `zero_mem_strongRelativeInterior_sub_image_of_regularity`.
- `bridge/view`: clauses `(ii)` through `(x)` are routed into the Chapter 6 owner predicate, while
  clause `(i)` is kept in its source-facing cone/closed-span form and proved directly.
-/

/-- The ten regularity alternatives from Proposition 15.24. Clauses `(ii)` through `(iv)` use the
canonical span/closedness characterizations of the corresponding linear-subspace conditions, and
clause `(vii)` writes the textbook continuity set `cont g` in the local-domain continuity form
provided by Corollary 8.39. -/
def effectiveDomainSubImageStrongRelativeInteriorRegularity
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) : Prop :=
  let C := effectiveDomain f
  let D := effectiveDomain g
  let A : Set K := L '' C
  let S : Set K := D - A
  let T : Set K := D - cone A
  cone S = (((Submodule.span ℝ S).topologicalClosure : Submodule ℝ K) : Set K) ∨
    (S = (Submodule.span ℝ S : Set K) ∧
      IsClosed (((Submodule.span ℝ S : Submodule ℝ K) : Set K))) ∨
    (C = (Submodule.span ℝ C : Set H) ∧
      D = (Submodule.span ℝ D : Set K) ∧
      IsClosed
        (((Submodule.span ℝ D ⊔ (Submodule.span ℝ C).map L.toLinearMap : Submodule ℝ K) :
          Set K))) ∨
    (IsCone D ∧
      T = (Submodule.span ℝ T : Set K) ∧
      IsClosed (((Submodule.span ℝ T : Submodule ℝ K) : Set K))) ∨
    ((0 : K) ∈ core S) ∨
    ((0 : K) ∈ interior S) ∨
    (∃ y ∈ A, ∃ ρ : ℝ, 0 < ρ ∧
      Metric.ball y ρ ⊆ D ∧
      ContinuousAt (fun z : K ↦ (g z : EReal).toReal) y) ∨
    (FiniteDimensional ℝ K ∧ (ri D ∩ ri A).Nonempty) ∨
    (FiniteDimensional ℝ K ∧ (ri D ∩ (L '' qri C)).Nonempty) ∨
    (FiniteDimensional ℝ H ∧ FiniteDimensional ℝ K ∧ (ri D ∩ (L '' ri C)).Nonempty)

set_option linter.style.longLine false in
private theorem continuousPoints_eq_interior_effectiveDomain_of_mem_gammaZero
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K)) :
    {y : K | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ effectiveDomain g ∧
      ContinuousAt (fun z : K ↦ (g z : EReal).toReal) y} = interior (effectiveDomain g) := by
  exact
    continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
      g
      hg.2
      (Or.inr <| Or.inl hg.1)

-- Clauses `(ii)` through `(x)` route into the Chapter 6 owner predicate; clause `(i)` is handled
-- separately by the closed-span criterion in the main theorem.
private theorem tail_to_strongRelativeInteriorSubImageRegularity
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (hg : g ∈ Γ₀(K)) (L : H →L[ℝ] K)
    (hregular :
      (effectiveDomain g - L '' effectiveDomain f = (Submodule.span ℝ
          (effectiveDomain g - L '' effectiveDomain f) : Set K) ∧
        IsClosed (((Submodule.span ℝ (effectiveDomain g - L '' effectiveDomain f) :
          Submodule ℝ K) : Set K))) ∨
        (effectiveDomain f = (Submodule.span ℝ (effectiveDomain f) : Set H) ∧
          effectiveDomain g = (Submodule.span ℝ (effectiveDomain g) : Set K) ∧
          IsClosed
            (((Submodule.span ℝ (effectiveDomain g) ⊔
                (Submodule.span ℝ (effectiveDomain f)).map L.toLinearMap :
                Submodule ℝ K) : Set K))) ∨
        (IsCone (effectiveDomain g) ∧
          (effectiveDomain g - cone (L '' effectiveDomain f)) =
            (Submodule.span ℝ (effectiveDomain g - cone (L '' effectiveDomain f)) : Set K) ∧
          IsClosed (((Submodule.span ℝ (effectiveDomain g - cone (L '' effectiveDomain f)) :
            Submodule ℝ K) : Set K))) ∨
        ((0 : K) ∈ core (effectiveDomain g - L '' effectiveDomain f)) ∨
        ((0 : K) ∈ interior (effectiveDomain g - L '' effectiveDomain f)) ∨
        (∃ y ∈ L '' effectiveDomain f, ∃ ρ : ℝ, 0 < ρ ∧
          Metric.ball y ρ ⊆ effectiveDomain g ∧
          ContinuousAt (fun z : K ↦ (g z : EReal).toReal) y) ∨
        (FiniteDimensional ℝ K ∧
          (ri (effectiveDomain g) ∩ ri (L '' effectiveDomain f)).Nonempty) ∨
        (FiniteDimensional ℝ K ∧
          (ri (effectiveDomain g) ∩ (L '' qri (effectiveDomain f))).Nonempty) ∨
        (FiniteDimensional ℝ H ∧ FiniteDimensional ℝ K ∧
          (ri (effectiveDomain g) ∩ (L '' ri (effectiveDomain f))).Nonempty)) :
    strongRelativeInteriorSubImageRegularity (effectiveDomain f) (effectiveDomain g) L := by
  rcases hregular with hsubspace | hregular
  · dsimp [strongRelativeInteriorSubImageRegularity]
    exact Or.inl hsubspace
  rcases hregular with hlinear | hregular
  · dsimp [strongRelativeInteriorSubImageRegularity]
    exact Or.inr <| Or.inl <| ⟨hlinear.1, hlinear.2.1, Or.inl hlinear.2.2⟩
  rcases hregular with hcone | hregular
  · dsimp [strongRelativeInteriorSubImageRegularity]
    exact Or.inr <| Or.inr <| Or.inl hcone
  rcases hregular with hcore | hregular
  · dsimp [strongRelativeInteriorSubImageRegularity]
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hcore
  rcases hregular with hinter | hregular
  · exact strongRelativeInteriorSubImageRegularity_of_zero_mem_interior L hinter
  rcases hregular with hcont | hregular
  · rcases hcont with ⟨y, hyA, ρ, hρ, hball, hycont⟩
    have hy_int : y ∈ interior (effectiveDomain g) := by
      rw [← continuousPoints_eq_interior_effectiveDomain_of_mem_gammaZero hg]
      exact ⟨ρ, hρ, hball, hycont⟩
    have hinter :
        (L '' effectiveDomain f ∩ interior (effectiveDomain g)).Nonempty := by
      exact ⟨y, hyA, hy_int⟩
    dsimp [strongRelativeInteriorSubImageRegularity]
    exact
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl <| Or.inr hinter
  rcases hregular with hri | hregular
  · dsimp [strongRelativeInteriorSubImageRegularity]
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hri
  rcases hregular with hqri | hri_image
  · dsimp [strongRelativeInteriorSubImageRegularity]
    exact
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inl hqri
  · dsimp [strongRelativeInteriorSubImageRegularity]
    exact
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr hri_image

-- Proof sketch: this is Proposition 6.19 specialized to `effectiveDomain f` and
-- `effectiveDomain g`.
/-- Bridge theorem: if the effective domains of `f` and `g` are nonempty and convex, and the
Chapter 6 regularity predicate holds for them along `L`, then
`0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`. -/
theorem zero_mem_strongRelativeInterior_sub_image_effectiveDomain_of_owner_regularity
    {f : H → Set.Ioi (⊥ : EReal)} {g : K → Set.Ioi (⊥ : EReal)}
    (hf_nonempty : (effectiveDomain f).Nonempty) (hg_nonempty : (effectiveDomain g).Nonempty)
    (hf_convex : Convex ℝ (effectiveDomain f)) (hg_convex : Convex ℝ (effectiveDomain g))
    (L : H →L[ℝ] K)
    (hregular :
      strongRelativeInteriorSubImageRegularity (effectiveDomain f) (effectiveDomain g) L) :
    (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f) := by
  simpa using
    (zero_mem_strongRelativeInterior_sub_image_of_regularity
      hf_nonempty
      hg_nonempty
      hf_convex
      hg_convex
      L hregular)

-- Proof sketch: clause `(i)` is the source-facing cone/closed-span criterion handled directly by
-- Proposition 6.21, while clauses `(ii)` through `(x)` are first pushed into the Chapter 6 owner
-- predicate and then discharged by the bridge theorem above. The textbook intersection hypothesis
-- `effectiveDomain g ∩ L '' effectiveDomain f ≠ ∅` is redundant here: clause `(i)` only needs the
-- separate nonemptiness of the two effective domains, already supplied by `hf` and `hg`, and the
-- owner route for clauses `(ii)` through `(x)` also uses only those separate nonemptiness facts.
/-- Proposition 15.24: let `f ∈ Γ₀(H)`, let `g ∈ Γ₀(K)`, and let `L : H →L[ℝ] K`. If one of the
ten source regularity alternatives holds, then `0 ∈ sri (effectiveDomain g - L ''
effectiveDomain f)`. -/
theorem zero_mem_strongRelativeInterior_sub_image_effectiveDomain_of_regularity
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    {g : K → Set.Ioi (⊥ : EReal)} (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hregular : effectiveDomainSubImageStrongRelativeInteriorRegularity f g L) :
    (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f) := by
  rw [effectiveDomainSubImageStrongRelativeInteriorRegularity] at hregular
  rcases hregular with hcone | hregular
  · have hsub_nonempty : (effectiveDomain g - L '' effectiveDomain f).Nonempty := by
      rcases hg.2.nonempty with ⟨y, hyg⟩
      rcases hf.2.nonempty with ⟨x, hxf⟩
      exact ⟨y - L x, Set.mem_sub.mpr ⟨y, hyg, L x, ⟨x, hxf, rfl⟩, rfl⟩⟩
    have hsub_convex : Convex ℝ (effectiveDomain g - L '' effectiveDomain f) := by
      exact hg.2.convex_effectiveDomain.sub (hf.2.convex_effectiveDomain.linear_image L.toLinearMap)
    exact
      (zero_mem_strongRelativeInterior_iff_cone_eq_closure_span_of_nonempty_convex
        hsub_nonempty hsub_convex).2 hcone
  · have howner :
        strongRelativeInteriorSubImageRegularity (effectiveDomain f) (effectiveDomain g) L :=
      tail_to_strongRelativeInteriorSubImageRegularity hg L hregular
    exact
      zero_mem_strongRelativeInterior_sub_image_effectiveDomain_of_owner_regularity
        hf.2.nonempty
        hg.2.nonempty
        hf.2.convex_effectiveDomain
        hg.2.convex_effectiveDomain
        L howner

end

end ERealFunction
