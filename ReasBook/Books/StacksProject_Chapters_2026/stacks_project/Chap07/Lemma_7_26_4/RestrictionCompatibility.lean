module

public import stacks_project.Chap07.Lemma_7_26_4.FixedCoverDescent

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory
namespace GrothendieckTopology

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C} {U : C}

/-- Helper for Lemma 7.26.4: transporting a pulled-back cover arrow along the identity morphism
of the slice site leaves the arrow unchanged. -/
theorem localized_cover_descent_pullback_arrow_map_id
    (𝒰 : J.Cover U)
    (V : Over U)
    (K : (𝒰.pullback V.hom).Arrow) :
    localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 (𝟙 V) K = K := by
  -- Expand the transported arrow and let proof irrelevance remove the cover-membership field.
  cases K
  simp [localized_cover_descent_pullback_arrow_map]

/-- Helper for Lemma 7.26.4: transporting a pulled-back cover arrow along two slice morphisms is
the same as transporting it along their composite. -/
theorem localized_cover_descent_pullback_arrow_map_comp
    (𝒰 : J.Cover U)
    {V W X : Over U}
    (g : V ⟶ W)
    (h : W ⟶ X)
    (K : (𝒰.pullback V.hom).Arrow) :
    localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 h
        (localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 g K) =
      localized_cover_descent_pullback_arrow_map (J := J) (U := U) 𝒰 (g ≫ h) K := by
  -- After unfolding the cover-arrow transport, associativity of the underlying arrows is the
  -- only remaining data; proof irrelevance handles the sieve-membership witnesses.
  cases K
  simp [localized_cover_descent_pullback_arrow_map, Category.assoc]

/-- Helper for Lemma 7.26.4: the relation-level pullback transport is packaged as an honest
relation of the pulled-back cover over `W`, so compatibility of a glued family over `W` can be
applied directly. -/
def localized_cover_descent_pullback_relation_cover_map
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (𝒰.pullback W.hom).Relation :=
  GrothendieckTopology.Cover.Relation.mk'
    (localized_cover_descent_pullback_relation_map (J := J) (U := U) 𝒰 g R)

/-- Helper for Lemma 7.26.4: the first arrow of the transported cover relation is the
transported first arrow. -/
theorem localized_cover_descent_pullback_relation_cover_map_fst
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).fst =
      localized_cover_descent_pullback_arrow_map
        (J := J) (U := U) 𝒰 g R.fst := by
  -- The packaged cover relation was built from the arrow-level transported relation.
  rfl

/-- Helper for Lemma 7.26.4: the second arrow of the transported cover relation is the
transported second arrow. -/
theorem localized_cover_descent_pullback_relation_cover_map_snd
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).snd =
      localized_cover_descent_pullback_arrow_map
        (J := J) (U := U) 𝒰 g R.snd := by
  -- The packaged cover relation was built from the arrow-level transported relation.
  rfl

/-- Helper for Lemma 7.26.4: applying a dependent family to the first projection of a transported
relation is heterogeneously the same as applying it to the transported first arrow. -/
theorem localized_cover_descent_pullback_relation_cover_map_fst_apply_heq
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation)
    {β : (𝒰.pullback W.hom).Arrow → Sort*}
    (s : ∀ K, β K) :
    HEq
      (s (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).fst)
      (s (localized_cover_descent_pullback_arrow_map
        (J := J) (U := U) 𝒰 g R.fst)) := by
  -- Rewrite the packaged relation projection to the canonical transported arrow, then the two
  -- dependent applications are identical.
  rw [localized_cover_descent_pullback_relation_cover_map_fst]

/-- Helper for Lemma 7.26.4: applying a dependent family to the second projection of a transported
relation is heterogeneously the same as applying it to the transported second arrow. -/
theorem localized_cover_descent_pullback_relation_cover_map_snd_apply_heq
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation)
    {β : (𝒰.pullback W.hom).Arrow → Sort*}
    (s : ∀ K, β K) :
    HEq
      (s (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).snd)
      (s (localized_cover_descent_pullback_arrow_map
        (J := J) (U := U) 𝒰 g R.snd)) := by
  -- The second projection of the transported relation has the same definitional normal form as
  -- the transported second arrow.
  rw [localized_cover_descent_pullback_relation_cover_map_snd]

/-- Helper for Lemma 7.26.4: the overlap witness of the transported cover relation is exactly the
arrow-level transported overlap witness. -/
theorem localized_cover_descent_pullback_relation_cover_map_r
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).r =
      localized_cover_descent_pullback_relation_map
        (J := J) (U := U) 𝒰 g R := by
  -- The relation witness is not recomputed when we package it as a cover relation.
  rfl

/-- Helper for Lemma 7.26.4: the transported packaged relation has the same overlap object as
the source relation. This is the relation-level version of the object normal form used by the
restriction-compatibility transport. -/
theorem localized_cover_descent_pullback_relation_cover_map_Z
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).r.Z = R.r.Z := by
  -- The packaged relation stores exactly the arrow-level transported relation.
  exact localized_cover_descent_pullback_relation_map_Z (J := J) (U := U) 𝒰 g R

/-- Helper for Lemma 7.26.4: the first overlap map of the transported relation is unchanged. -/
theorem localized_cover_descent_pullback_relation_cover_map_g₁
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).r.g₁ = R.r.g₁ := by
  -- The relation map only changes the cover-arrow structure maps by postcomposition with `g`.
  rfl

/-- Helper for Lemma 7.26.4: the second overlap map of the transported relation is unchanged. -/
theorem localized_cover_descent_pullback_relation_cover_map_g₂
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).r.g₂ = R.r.g₂ := by
  -- The relation map only changes the cover-arrow structure maps by postcomposition with `g`.
  rfl

/-- Helper for Lemma 7.26.4: the first transported relation arrow has the same underlying
original-cover base as the first source relation arrow. -/
theorem localized_cover_descent_pullback_relation_cover_map_fst_base
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).fst.base = R.fst.base := by
  -- First expose the transported first arrow, then use the arrow-level base normalization.
  rw [localized_cover_descent_pullback_relation_cover_map_fst]
  exact localized_cover_descent_pullback_arrow_map_base
    (J := J) (U := U) 𝒰 g R.fst

/-- Helper for Lemma 7.26.4: the second transported relation arrow has the same underlying
original-cover base as the second source relation arrow. -/
theorem localized_cover_descent_pullback_relation_cover_map_snd_base
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).snd.base = R.snd.base := by
  -- First expose the transported second arrow, then use the arrow-level base normalization.
  rw [localized_cover_descent_pullback_relation_cover_map_snd]
  exact localized_cover_descent_pullback_arrow_map_base
    (J := J) (U := U) 𝒰 g R.snd

/-- Helper for Lemma 7.26.4: the first transported relation arrow has structure map obtained by
postcomposing the source first arrow with the slice morphism. -/
theorem localized_cover_descent_pullback_relation_cover_map_fst_f
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).fst.f = R.fst.f ≫ g.left := by
  -- The packaged relation uses the same arrow-level transport on its first projection.
  simp [localized_cover_descent_pullback_relation_cover_map,
    localized_cover_descent_pullback_relation_map,
    localized_cover_descent_pullback_arrow_map]

/-- Helper for Lemma 7.26.4: the second transported relation arrow has structure map obtained by
postcomposing the source second arrow with the slice morphism. -/
theorem localized_cover_descent_pullback_relation_cover_map_snd_f
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).snd.f = R.snd.f ≫ g.left := by
  -- The packaged relation uses the same arrow-level transport on its second projection.
  simp [localized_cover_descent_pullback_relation_cover_map,
    localized_cover_descent_pullback_relation_map,
    localized_cover_descent_pullback_arrow_map]

/-- Helper for Lemma 7.26.4: the first transported overlap composite is the source overlap
composite followed by the slice morphism. -/
theorem localized_cover_descent_pullback_relation_cover_map_fst_q
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).r.g₁ ≫
        (localized_cover_descent_pullback_relation_cover_map
          (J := J) (U := U) 𝒰 g R).fst.f =
      R.r.g₁ ≫ R.fst.f ≫ g.left := by
  -- Normalize the transported relation by its two projection lemmas and then reassociate.
  rw [localized_cover_descent_pullback_relation_cover_map_g₁,
    localized_cover_descent_pullback_relation_cover_map_fst_f]
  rfl

/-- Helper for Lemma 7.26.4: the second transported overlap composite is the source overlap
composite followed by the slice morphism. -/
theorem localized_cover_descent_pullback_relation_cover_map_snd_q
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).r.g₂ ≫
        (localized_cover_descent_pullback_relation_cover_map
          (J := J) (U := U) 𝒰 g R).snd.f =
      R.r.g₂ ≫ R.snd.f ≫ g.left := by
  -- Normalize the transported relation by its two projection lemmas and then reassociate.
  rw [localized_cover_descent_pullback_relation_cover_map_g₂,
    localized_cover_descent_pullback_relation_cover_map_snd_f]
  rfl

/-- Helper for Lemma 7.26.4: after transporting a relation along a slice morphism, the first
overlap composite followed by the target structure map is the original composite followed by the
source structure map. -/
theorem localized_cover_descent_pullback_relation_cover_map_fst_to_source
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).r.g₁ ≫
        (localized_cover_descent_pullback_relation_cover_map
          (J := J) (U := U) 𝒰 g R).fst.f ≫ W.hom =
      R.r.g₁ ≫ R.fst.f ≫ V.hom := by
  -- First normalize the transported relation, then use the slice equation for `g`.
  rw [← Category.assoc]
  rw [localized_cover_descent_pullback_relation_cover_map_fst_q]
  calc
    (R.r.g₁ ≫ R.fst.f ≫ g.left) ≫ W.hom =
        R.r.g₁ ≫ R.fst.f ≫ g.left ≫ W.hom := by
      simp only [Category.assoc]
    _ = R.r.g₁ ≫ R.fst.f ≫ V.hom := by
      exact congrArg (fun h ↦ R.r.g₁ ≫ R.fst.f ≫ h) (Over.w g)

/-- Helper for Lemma 7.26.4: after transporting a relation along a slice morphism, the second
overlap composite followed by the target structure map is the original composite followed by the
source structure map. -/
theorem localized_cover_descent_pullback_relation_cover_map_snd_to_source
    (𝒰 : J.Cover U)
    {V W : Over U}
    (g : V ⟶ W)
    (R : (𝒰.pullback V.hom).Relation) :
    (localized_cover_descent_pullback_relation_cover_map
        (J := J) (U := U) 𝒰 g R).r.g₂ ≫
        (localized_cover_descent_pullback_relation_cover_map
          (J := J) (U := U) 𝒰 g R).snd.f ≫ W.hom =
      R.r.g₂ ≫ R.snd.f ≫ V.hom := by
  -- The second projection uses the same normalization and slice equation.
  rw [← Category.assoc]
  rw [localized_cover_descent_pullback_relation_cover_map_snd_q]
  calc
    (R.r.g₂ ≫ R.snd.f ≫ g.left) ≫ W.hom =
        R.r.g₂ ≫ R.snd.f ≫ g.left ≫ W.hom := by
      simp only [Category.assoc]
    _ = R.r.g₂ ≫ R.snd.f ≫ V.hom := by
      exact congrArg (fun h ↦ R.r.g₂ ≫ R.snd.f ≫ h) (Over.w g)

end

end GrothendieckTopology
end CategoryTheory
