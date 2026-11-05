module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import stacks_project.Chap07.Lemma_7_42_2
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Definition 7.42.3:
- primary domain: Grothendieck topologies and site functors with cover-lifting conditions;
- sampled owner API:
  `CategoryTheory.Functor.IsCocontinuous`,
  `CategoryTheory.Functor.cover_lift`,
  `CategoryTheory.GrothendieckTopology.Cover`,
  `CategoryTheory.GrothendieckTopology.IsSheafTheoreticallyEmpty`;
- source/core/bridge triage:
  `source-facing`: the Stacks Project notion of an almost cocontinuous functor of sites;
  `core/canonical`: the owner class `CategoryTheory.Functor.IsAlmostCocontinuous`, modeled on
  mathlib's owner `Functor.IsCocontinuous`;
  `bridge/view`: the explicit covering-family refinement statement with the
  sheaf-theoretically-empty alternative.

Primitive data are only the functor, the two Grothendieck topologies, and the covering sieve on
`U` obtained by adjoining the sheaf-theoretically-empty-image sieve to the canonical pullback
sieve `T.functorPullback u`. The explicit covering-family refinement and
factorization-through-an-arrow formulations from the source are derived bridge lemmas recovered
from that covering-sieve owner statement. The stronger owner `Functor.IsCocontinuous` remains a
derived special case. -/

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

namespace Functor

/-- Definition 7.42.3: a functor of sites is almost cocontinuous if every covering of `u(U)` can
be pulled back to a covering sieve on `U` consisting of arrows whose image objects are each either
sheaf theoretically empty in `D` or whose map to `u(U)` already belongs to the original covering
sieve. The explicit covering-family refinement and factorization-through-an-arrow formulations are
equivalent and are provided below as derived API. -/
class IsAlmostCocontinuous (u : C ⥤ D) (J : GrothendieckTopology C)
    (K : GrothendieckTopology D) : Prop where
  cover_lift {U : C} {T : Sieve (u.obj U)} (hT : T ∈ K (u.obj U)) :
      ({
        arrows := fun Y f ↦ K.IsSheafTheoreticallyEmpty (u.obj Y) ∨ (T.functorPullback u) f
        downward_closed := by
          intro Y Z f hf g
          rcases hf with h | h
          · exact .inl <| h.of_arrow (u.map g)
          · exact .inr <| (T.functorPullback u).downward_closed h g
      } : Sieve U) ∈ J U

/-- The source-text formulation of almost cocontinuity using explicit factorization through an
arrow of the covering sieve. -/
lemma cover_lift_factors
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsAlmostCocontinuous J K] {U : C} (T : K.Cover (u.obj U)) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      K.IsSheafTheoreticallyEmpty (u.obj I.Y) ∨
        ∃ (j : T.Arrow) (g : u.obj I.Y ⟶ j.Y), g ≫ j.f = u.map I.f := by
  let h : IsAlmostCocontinuous u J K := inferInstance
  let S : Sieve U :=
    {
      arrows := fun Y f ↦ K.IsSheafTheoreticallyEmpty (u.obj Y) ∨
        ((T : Sieve (u.obj U)).functorPullback u) f
      downward_closed := by
        intro Y Z f hf g
        rcases hf with h | h
        · exact .inl <| h.of_arrow (u.map g)
        · exact .inr <| ((T : Sieve (u.obj U)).functorPullback u).downward_closed h g
    }
  have hS : S ∈ J U := by
    simpa [S] using h.cover_lift T.condition
  refine ⟨⟨S, hS⟩, ?_⟩
  intro I
  rcases I.hf with hI | hI
  · exact .inl hI
  · exact .inr ⟨⟨_, _, hI⟩, 𝟙 _, by simp⟩

/-- Every cocontinuous functor of sites is almost cocontinuous. -/
instance isAlmostCocontinuous_of_isCocontinuous
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsCocontinuous J K] :
    IsAlmostCocontinuous u J K where
  cover_lift {U} {T} hT := by
    refine J.superset_covering ?_ <| u.cover_lift J K hT
    intro Y f hf
    exact .inr hf

end Functor

end CategoryTheory
