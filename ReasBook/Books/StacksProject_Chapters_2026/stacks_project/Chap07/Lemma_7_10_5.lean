module

public import stacks_project.Chap07.Lemma_7_8_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w₁ w₂ v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : Precoverage C} [J.HasPullbacks] [J.IsStableUnderBaseChange]
  [J.IsStableUnderComposition]

open Limits
open Precoverage

namespace SemiRepresentableFamily
namespace Over

variable {U : C}

/- Domain-style sampling for Lemma 7.10.5:
- primary domain: precoverage covering families and common refinements;
- sampled owner API:
  `Precoverage.ZeroHypercover`,
  `Precoverage.ZeroHypercover.inter`,
  `PreZeroHypercover.interFst`,
  `PreZeroHypercover.interSnd`;
- source/core/bridge triage:
  `source-facing`: the existence of a common covering refinement of two fixed-target families;
  `core/canonical`: `J.ZeroHypercover U` together with its canonical intersection cover;
  `bridge/view`: the comparison between a covering family and the canonical intersection
  construction on `J.ZeroHypercover U`.

Primitive data are only the two covering families and their covering proofs. The common refinement
is derived from `ZeroHypercover.inter`, so the public statement should stay at the level of the
covering-family API rather than introducing extra wrapper data.
-/

/-- Lemma 7.10.5: two covering fixed-target families over `U` admit a common covering
refinement. -/
theorem exists_covering_family_common_refinement {U : C}
    (𝒰 𝒱 : Over U)
    (h𝒰 : IsCovering J 𝒰) (h𝒱 : IsCovering J 𝒱) :
    ∃ (𝒲 : Over U) (_ : IsCovering J 𝒲), Refines 𝒲 𝒰 ∧ Refines 𝒲 𝒱 := by
  let E : J.ZeroHypercover U :=
    { I₀ := 𝒰.index
      X := fun i ↦ (𝒰.obj i).left
      f := fun i ↦ (𝒰.obj i).hom
      mem₀ := h𝒰 }
  let F : J.ZeroHypercover U :=
    { I₀ := 𝒱.index
      X := fun i ↦ (𝒱.obj i).left
      f := fun i ↦ (𝒱.obj i).hom
      mem₀ := h𝒱 }
  -- Each pair of covering arrows admits a pullback, so the canonical intersection exists.
  have hpull :
      ∀ i : E.I₀, ∀ j : F.I₀, HasPullback (E.f i) (F.f j) := by
    intro i j
    letI : F.presieve₀.HasPullbacks (E.f i) :=
      J.hasPullbacks_of_mem (E.f i) F.mem₀
    letI : HasPullback (F.f j) (E.f i) :=
      Presieve.HasPullbacks.hasPullback (R := F.presieve₀) (f := E.f i) (h := F.f j) (by
        exact ⟨j⟩)
    exact hasPullback_symmetry (F.f j) (E.f i)
  letI : ∀ i : E.I₀, ∀ j : F.I₀, HasPullback (E.f i) (F.f j) := hpull
  let W₀ : J.ZeroHypercover U := E.inter F
  let 𝒲 : Over U :=
    { index := W₀.I₀
      obj := fun i ↦ CategoryTheory.Over.mk (W₀.f i) }
  let π₁ : W₀.toPreZeroHypercover.Hom E.toPreZeroHypercover :=
    PreZeroHypercover.interFst E.toPreZeroHypercover F.toPreZeroHypercover
  let π₂ : W₀.toPreZeroHypercover.Hom F.toPreZeroHypercover :=
    PreZeroHypercover.interSnd E.toPreZeroHypercover F.toPreZeroHypercover
  -- The pullback-intersection hypercover is covering by the base-change and composition axioms.
  have h𝒲 : IsCovering J 𝒲 := by
    simpa [IsCovering, toPresieve, 𝒲] using W₀.mem₀
  -- The first pullback projection sends each intersection term to the corresponding `𝒰`-member.
  have hRefines𝒰 : Refines 𝒲 𝒰 := by
    refine ⟨{ α := π₁.s₀, f := fun i ↦ CategoryTheory.Over.homMk (π₁.h₀ i) (π₁.w₀ i) }⟩
  -- The second pullback projection does the same for the family `𝒱`.
  have hRefines𝒱 : Refines 𝒲 𝒱 := by
    refine ⟨{ α := π₂.s₀, f := fun i ↦ CategoryTheory.Over.homMk (π₂.h₀ i) (π₂.w₀ i) }⟩
  exact ⟨𝒲, h𝒲, hRefines𝒰, hRefines𝒱⟩

end Over
end SemiRepresentableFamily

end CategoryTheory
