module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import stacks_project.Chap07.Definition_7_8_2
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u₁ u₂ v₁ v₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-
Domain-style sampling:
- primary domain: Grothendieck topologies and cocontinuous functors between sites;
- sampled owner API:
  `SemiRepresentableFamily.Over`,
  `SemiRepresentableFamily.Over.IsCovering`,
  `SemiRepresentableFamily.Over.toSieve`,
  `Functor.IsCocontinuous`,
  `Functor.cover_lift`,
  `Sieve.ofArrows_eq_pullback_of_isPullback`,
  `Sieve.exists_eq_ofArrows`,
  `Sieve.mem_ofArrows_iff`,
  `CategoryTheory.ran_isSheaf_of_isCocontinuous`,
  `Functor.relativelyRepresentable`;
- source/core/bridge triage:
  `source-facing`: the family-level representable pullback-cover criterion of the remark, phrased
  on the chapter's fixed-target family owner `SemiRepresentableFamily.Over`;
  `core/canonical`: `Functor.IsCocontinuous J K`;
  `bridge/view`: the theorem below, which upgrades the source family criterion directly to the
  canonical sieve-level owner property through the family-to-sieve bridge `toSieve`.

Primitive data are a covering family `𝒲 : SemiRepresentableFamily.Over V`, its source-facing
covering predicate `IsCovering K.toPrecoverage 𝒲`, explicit pullback squares for its members
along any `g : u.obj U ⟶ V`, and the fact that the resulting family in `C` is covering.
Cocontinuity is derived API from that source-facing owner abstraction, so this file should expose
the family criterion only as the hypothesis of a bridge theorem deriving
`u.IsCocontinuous J K`, not as a parallel public owner.

The single-arrow owner `Functor.relativelyRepresentable` is relevant background but not the right
main hypothesis here: it globalizes pullback existence for one arrow across all test morphisms
`u.obj U ⟶ V`, whereas Remark 7.20.5 only assumes pullback squares for the chosen covering family
and the chosen `g`. So the source-facing primitive data remain the indexwise pullback squares for
that one family and that one arrow, while the proof should still reuse the canonical sieve theorem
`Sieve.ofArrows_eq_pullback_of_isPullback` instead of reproving the corresponding sieve inclusion
entrywise.
-/

-- Proof sketch: represent an arbitrary covering sieve on `u(U)` by `Sieve.ofArrows`. Apply the
-- family-level hypothesis to that generating family. Any arrow in the resulting pullback cover
-- maps to an arrow in the original covering sieve because it factors through one of the chosen
-- generators. Upward closure then gives cocontinuity.
/-- Remark 7.20.5, bridge layer: if every `K`-covering fixed-target family on `V` pulls back
along every `g : u.obj U ⟶ V` to a `J`-covering fixed-target family on `U`, with each component
square a pullback, then `u` is cocontinuous. -/
theorem isCocontinuous_of_pullbackCoveringFamilies
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {u : C ⥤ D}
    (h :
      ∀ ⦃V : D⦄ (𝒲 : SemiRepresentableFamily.Over.{max u₂ v₂} V)
        (_ : IsCovering K.toPrecoverage 𝒲)
        ⦃U : C⦄ (g : u.obj U ⟶ V),
          ∃ (Z : 𝒲.index → C) (p : ∀ i, Z i ⟶ U) (q : ∀ i, u.obj (Z i) ⟶ (𝒲.obj i).left),
            (∀ i, IsPullback (q i) (u.map (p i)) (𝒲.obj i).hom g) ∧
              IsCovering J.toPrecoverage (ofArrows Z p)) :
    u.IsCocontinuous J K where
  cover_lift {U} {S} hS := by
    -- Repackage the covering sieve on `u.obj U` as an explicit indexed family of arrows.
    obtain ⟨ι, W, f, rfl⟩ := S.exists_eq_ofArrows
    let 𝒲 : SemiRepresentableFamily.Over.{max u₂ v₂} (u.obj U) := ofArrows W f
    have h𝒲 : IsCovering K.toPrecoverage 𝒲 := by
      rw [IsCovering, GrothendieckTopology.mem_toPrecoverage_iff]
      simpa [𝒲] using hS
    -- Apply the source-facing pullback-cover hypothesis to the identity of `u.obj U`.
    obtain ⟨Z, p, q, hpb, hcover⟩ := h 𝒲 h𝒲 (𝟙 (u.obj U))
    -- The component pullback squares identify the image family with the original covering sieve.
    have hEq :
        Sieve.ofArrows (fun i ↦ u.obj (Z i)) (fun i ↦ u.map (p i)) = Sieve.ofArrows W f := by
      simpa [Sieve.pullback_id] using
        (Sieve.ofArrows_eq_pullback_of_isPullback f fun i ↦ (hpb i).flip)
    -- Therefore every generator of the pullback family maps into the original covering sieve.
    have hmap :
        (Presieve.ofArrows Z p).map u ≤ Sieve.ofArrows W f := by
      rw [Presieve.map_ofArrows]
      intro X g hg
      rcases hg with ⟨i⟩
      exact hEq ▸ Sieve.ofArrows_mk _ _ i
    -- Passing from presieves to generated sieves gives the functor-pullback refinement.
    have hle : Sieve.ofArrows Z p ≤ (Sieve.ofArrows W f).functorPullback u := by
      rw [Sieve.generate_le_iff]
      exact Presieve.map_le_iff_le_functorPullback.mp hmap
    refine J.superset_covering hle ?_
    rw [IsCovering, GrothendieckTopology.mem_toPrecoverage_iff] at hcover
    simpa using hcover

end Functor
end CategoryTheory
