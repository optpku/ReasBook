module

public import stacks_project.Chap07.Definition_7_8_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {U : C}

namespace SemiRepresentableFamily

namespace Over

@[ext]
theorem Hom.ext {U : C} {𝒰 𝒱 : CategoryTheory.SemiRepresentableFamily.Over U}
    {φ ψ : Hom 𝒰 𝒱} (hα : φ.α = ψ.α) (hf : ∀ i, HEq (φ.f i) (ψ.f i)) :
    φ = ψ := by
  cases φ with
  | mk αφ fφ =>
      cases ψ with
      | mk αψ fψ =>
          cases hα
          have hf' : fφ = fψ := by
            funext i
            exact eq_of_heq (hf i)
          cases hf'
          rfl

instance {U : C} : Category (CategoryTheory.SemiRepresentableFamily.Over U) where
  Hom 𝒰 𝒱 := Hom 𝒰 𝒱
  id 𝒰 :=
    { α := fun i ↦ i
      f := fun i ↦ 𝟙 (𝒰.obj i) }
  comp f g :=
    { α := fun i ↦ g.α (f.α i)
      f := fun i ↦ f.f i ≫ g.f (f.α i) }
  id_comp := by
    intro 𝒰 𝒱 f
    cases f
    simp
  comp_id := by
    intro 𝒰 𝒱 f
    cases f
    simp
  assoc := by
    intro 𝒰 𝒱 𝒲 𝒳 f g h
    cases f
    cases g
    cases h
    simp [Category.assoc]

/-- Transport a fixed-target family along a base morphism. -/
def map {U V : C} (base : U ⟶ V) :
    CategoryTheory.SemiRepresentableFamily.Over U ⥤
      CategoryTheory.SemiRepresentableFamily.Over V where
  obj 𝒰 :=
    { index := 𝒰.index
      obj := fun i => (CategoryTheory.Over.map base).obj (𝒰.obj i) }
  map φ :=
    { α := φ.α
      f := fun i => (CategoryTheory.Over.map base).map (φ.f i) }
  map_id := by
    intro 𝒰
    apply Hom.ext
    · rfl
    · intro i
      exact heq_of_eq ((CategoryTheory.Over.map base).map_id (𝒰.obj i))
  map_comp := by
    intro 𝒰 𝒱 𝒲 φ ψ
    apply Hom.ext
    · rfl
    · intro i
      exact heq_of_eq ((CategoryTheory.Over.map base).map_comp (φ.f i) (ψ.f (φ.α i)))

@[simp]
theorem map_obj_obj {U V : C} (base : U ⟶ V)
    (𝒰 : CategoryTheory.SemiRepresentableFamily.Over U) (i : 𝒰.index) :
    ((map base).obj 𝒰).obj i = (CategoryTheory.Over.map base).obj (𝒰.obj i) :=
  rfl

@[simp]
theorem map_map_α {U V : C} (base : U ⟶ V)
    {𝒰 𝒱 : CategoryTheory.SemiRepresentableFamily.Over U} (φ : 𝒰 ⟶ 𝒱) :
    ((map base).map φ).α = φ.α :=
  rfl

@[simp]
theorem map_map_f {U V : C} (base : U ⟶ V)
    {𝒰 𝒱 : CategoryTheory.SemiRepresentableFamily.Over U} (φ : 𝒰 ⟶ 𝒱) (i : 𝒰.index) :
    ((map base).map φ).f i = (CategoryTheory.Over.map base).map (φ.f i) :=
  rfl

/-- Helper for Lemma 7.8.3: a presieve inclusion between fixed-target families yields a
refinement whose components are isomorphisms in the slice category. -/
private theorem exists_componentwise_iso_hom_of_toPresieve_le
    {𝒰 𝒱 : CategoryTheory.SemiRepresentableFamily.Over U}
    (h : 𝒰.toPresieve ≤ 𝒱.toPresieve) :
    ∃ f : 𝒰 ⟶ 𝒱, ∀ i : 𝒰.index, IsIso (f.f i) := by
  classical
  -- Each component arrow of `𝒰` belongs to the presieve of `𝒱`, so it coincides with a chosen
  -- component of `𝒱` up to an explicit slice isomorphism.
  have hi :
      ∀ i : 𝒰.index,
        ∃ j : 𝒱.index,
          ∃ hobj : (𝒱.obj j).left = (𝒰.obj i).left,
            (𝒰.obj i).hom = eqToHom hobj.symm ≫ (𝒱.obj j).hom := by
    intro i
    exact Presieve.ofArrows_surj (fun j : 𝒱.index ↦ (𝒱.obj j).hom) ((𝒰.obj i).hom)
      (h _ _ (Presieve.ofArrows.mk i))
  choose α hαobj hαhom using hi
  -- Package those chosen componentwise identifications into a morphism of families.
  refine ⟨
    { α := α
      f := fun i ↦
        (CategoryTheory.Over.isoMk
          (eqToIso (hαobj i).symm)
          (by simpa using (hαhom i).symm)).hom },
    ?_⟩
  intro i
  -- Each component map is an isomorphism because it is the hom of an explicit slice isomorphism.
  change IsIso
    ((CategoryTheory.Over.isoMk
      (eqToIso (hαobj i).symm)
      (by simpa using (hαhom i).symm)).hom)
  infer_instance

-- Route correction: the imported chapter prefix does not currently expose the fixed-target family
-- owner API, so this file proves Lemma 7.8.3 directly from the canonical presieve and slice data.

/-- Helper for Lemma 7.8.3: a tautological equivalence forgets to a refinement. -/
theorem TautologicallyEquivalent.refines
    {𝒰 𝒱 : CategoryTheory.SemiRepresentableFamily.Over U}
    (h : TautologicallyEquivalent 𝒰 𝒱) :
    Refines 𝒰 𝒱 := by
  -- Forget the componentwise isomorphism data and keep only the forward family morphism.
  rcases h with ⟨f, _, _, _⟩
  exact ⟨f⟩

/-- Helper for Lemma 7.8.3: tautological equivalence is reflexive. -/
theorem TautologicallyEquivalent.refl
    (𝒰 : CategoryTheory.SemiRepresentableFamily.Over U) :
    TautologicallyEquivalent 𝒰 𝒰 := by
  -- The identity morphisms witness the two directions, and each identity component is an
  -- isomorphism in the slice category.
  refine ⟨𝟙 𝒰, 𝟙 𝒰, ?_, ?_⟩
  · intro i
    change IsIso (𝟙 (𝒰.obj i))
    infer_instance
  · intro i
    change IsIso (𝟙 (𝒰.obj i))
    infer_instance

/-- Helper for Lemma 7.8.3: tautological equivalence is symmetric. -/
theorem TautologicallyEquivalent.symm
    {𝒰 𝒱 : CategoryTheory.SemiRepresentableFamily.Over U}
    (h : TautologicallyEquivalent 𝒰 𝒱) :
    TautologicallyEquivalent 𝒱 𝒰 := by
  -- Swap the two witness morphisms and their componentwise isomorphism data.
  rcases h with ⟨f, g, hf, hg⟩
  exact ⟨g, f, hg, hf⟩

/-- Helper for Lemma 7.8.3: tautological equivalence is transitive. -/
theorem TautologicallyEquivalent.trans
    {𝒰 𝒱 𝒲 : CategoryTheory.SemiRepresentableFamily.Over U}
    (h𝒰𝒱 : TautologicallyEquivalent 𝒰 𝒱)
    (h𝒱𝒲 : TautologicallyEquivalent 𝒱 𝒲) :
    TautologicallyEquivalent 𝒰 𝒲 := by
  -- Compose the witness morphisms in both directions; composition preserves slice isomorphisms.
  rcases h𝒰𝒱 with ⟨f, g, hf, hg⟩
  rcases h𝒱𝒲 with ⟨f', g', hf', hg'⟩
  refine ⟨f ≫ f', g' ≫ g, ?_, ?_⟩
  · intro i
    change IsIso (f.f i ≫ f'.f (f.α i))
    infer_instance
  · intro i
    change IsIso (g'.f i ≫ g.f (g'.α i))
    infer_instance

/-- Helper for Lemma 7.8.3: refinement is reflexive. -/
theorem Refines.refl
    (𝒰 : CategoryTheory.SemiRepresentableFamily.Over U) : Refines 𝒰 𝒰 :=
  ⟨𝟙 𝒰⟩

/-- Helper for Lemma 7.8.3: refinement is transitive by composition of family morphisms. -/
theorem Refines.trans
    {𝒰 𝒱 𝒲 : CategoryTheory.SemiRepresentableFamily.Over U}
    (h𝒰𝒱 : Refines 𝒰 𝒱) (h𝒱𝒲 : Refines 𝒱 𝒲) :
    Refines 𝒰 𝒲 :=
  Nonempty.map2 (· ≫ ·) h𝒰𝒱 h𝒱𝒲

-- Proof sketch: a tautological equivalence already contains family morphisms in both directions,
-- so forgetting the componentwise isomorphism data gives mutual refinement.
/-- Lemma 7.8.3 (1): tautologically equivalent families of morphisms with fixed target refine each
other. -/
theorem tautologicallyEquivalent_implies_refines_in_both_directions
    {𝒰 𝒱 : CategoryTheory.SemiRepresentableFamily.Over U}
    (h : TautologicallyEquivalent 𝒰 𝒱) :
    Refines 𝒰 𝒱 ∧ Refines 𝒱 𝒰 := by
  -- Use the forward witness directly and symmetry for the reverse refinement.
  exact ⟨h.refines, h.symm.refines⟩

-- Proof sketch: `CombinatoriallyEquivalent` is equality of the canonical presieves attached to the
-- two families, so its relation laws are exactly the equality laws transported along `toPresieve`.
/-- Lemma 7.8.3 (2): combinatorial equivalence is an equivalence relation on families of
morphisms with fixed target `U`. -/
theorem combinatoriallyEquivalent_isEquivalence :
    _root_.Equivalence
      (CombinatoriallyEquivalent :
        CategoryTheory.SemiRepresentableFamily.Over U →
          CategoryTheory.SemiRepresentableFamily.Over U → Prop) := by
  -- This relation is equality after applying the generated-presieve map.
  simpa [CombinatoriallyEquivalent] using
    eq_equivalence.comap
      (fun 𝒰 : CategoryTheory.SemiRepresentableFamily.Over U ↦ 𝒰.toPresieve)

-- Proof sketch: reflexivity uses identity morphisms, symmetry swaps the two witness morphisms,
-- and transitivity composes them while preserving componentwise isomorphisms.
/-- Lemma 7.8.3 (3): tautological equivalence is an equivalence relation on families of morphisms
with fixed target `U`. -/
theorem tautologicallyEquivalent_isEquivalence :
    _root_.Equivalence
      (TautologicallyEquivalent :
        CategoryTheory.SemiRepresentableFamily.Over U →
          CategoryTheory.SemiRepresentableFamily.Over U → Prop) := by
  -- Assemble the relation API proved above.
  exact ⟨TautologicallyEquivalent.refl, TautologicallyEquivalent.symm,
    TautologicallyEquivalent.trans⟩

-- Proof sketch: reflexivity is identity, symmetry swaps the two refinements, and transitivity
-- composes the refinement morphisms in each direction.
/-- Lemma 7.8.3 (4): refining each other is an equivalence relation on families of morphisms with
fixed target `U`. -/
theorem refines_in_both_directions_isEquivalence :
    _root_.Equivalence
      (fun 𝒰 𝒱 : CategoryTheory.SemiRepresentableFamily.Over U ↦
        Refines 𝒰 𝒱 ∧ Refines 𝒱 𝒰) := by
  -- Package the reflexive, symmetric, and transitive structure of mutual refinement.
  refine ⟨?_, ?_, ?_⟩
  · intro 𝒰
    exact ⟨Refines.refl 𝒰, Refines.refl 𝒰⟩
  · intro 𝒰 𝒱 h
    exact ⟨h.2, h.1⟩
  · intro 𝒰 𝒱 𝒲 h𝒰𝒱 h𝒱𝒲
    exact ⟨h𝒰𝒱.1.trans h𝒱𝒲.1, h𝒱𝒲.2.trans h𝒰𝒱.2⟩

end Over
end SemiRepresentableFamily

end CategoryTheory
