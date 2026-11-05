module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import stacks_project.Chap07.Remark_7_48_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w' w u v

namespace CategoryTheory

open SemiRepresentableFamily.Over

variable {C : Type u} [Category.{v} C]

abbrev CoverFamily (X : C) := SemiRepresentableFamily.Over.{max u v} X

/- Domain-style sampling for Remark 7.48.4:
- primary domain: precoverages, their closure axioms, and covering families up to tautological
  equivalence;
- inspected owner declarations:
  `Precoverage`,
  `Precoverage.toGrothendieck`,
  `Precoverage.comp_mem_coverings`,
  `Precoverage.mem_coverings_of_isPullback`,
  `Coverage.toGrothendieck_eq_of_tautological_enlargement`,
  `Precoverage.HasIsos`,
  `Precoverage.IsStableUnderComposition`,
  `Precoverage.IsStableUnderBaseChange`,
  `SemiRepresentableFamily.Over.IsCovering`,
  `SemiRepresentableFamily.Over.combinatoriallyEquivalent_implies_tautologicallyEquivalent`;
- best owner abstraction: the source-facing owner here is the modified precoverage
  `Precoverage.tautologicalEnlargement K`; the remark's `(1')-(3')` statements are owner-level
  closure properties of that precoverage, while the induced-topology comparison is a separate
  bridge back to `Coverage`;
- primitive data: the enlarged covering predicate on presieves;
- derived API: the owner-level characterization of its covering families, the remark's modified
  closure axioms, and the equality of the associated Grothendieck topologies.

Source/core/bridge triage:
- `source-facing`: `tautologicalEnlargement`;
- `core/canonical`: `Precoverage C` together with `Precoverage.toGrothendieck` and the canonical
  precoverage owner
  classes for isomorphisms, composition, and base change;
- `bridge/view`: `SemiRepresentableFamily.Over.IsCovering` and the passage from presieve equality
  to tautological equivalence via combinatorial equivalence, plus the final coverage-level topology
  comparison.
-/

namespace Precoverage

/-- Remark 7.48.4: for a precoverage `K`, the "shrunk" collection of coverings consisting of those
presieves tautologically equivalent to some original `K`-cover is the canonical precoverage
obtained by adjoining precisely those tautologically equivalent covering families. -/
def tautologicalEnlargement (K : Precoverage C) : Precoverage C where
  coverings X :=
    { R : Presieve X |
        ∃ 𝒰 𝒱 : CoverFamily X,
          IsCovering K 𝒰 ∧
            TautologicallyEquivalent 𝒰 𝒱 ∧
            𝒱.toPresieve = R }

/-- Helper for Remark 7.48.4: tautological equivalences of fixed-target covering families compose
by composing the witness morphisms in the slice category. -/
theorem tautologicallyEquivalent_trans
    {X : C} {𝒰 𝒱 𝒲 : CoverFamily X}
    (h𝒰𝒱 : TautologicallyEquivalent 𝒰 𝒱)
    (h𝒱𝒲 : TautologicallyEquivalent 𝒱 𝒲) :
    TautologicallyEquivalent 𝒰 𝒲 := by
  -- Compose the forward and backward witnesses explicitly at the quiver level.
  rcases h𝒰𝒱 with ⟨f, g, hf, hg⟩
  rcases h𝒱𝒲 with ⟨f', g', hf', hg'⟩
  refine ⟨
    { α := fun i ↦ f'.α (f.α i)
      f := fun i ↦ f.f i ≫ f'.f (f.α i) },
    { α := fun i ↦ g.α (g'.α i)
      f := fun i ↦ g'.f i ≫ g.f (g'.α i) },
    ?_, ?_⟩
  · intro i
    change IsIso (f.f i ≫ f'.f (f.α i))
    infer_instance
  · intro i
    change IsIso (g'.f i ≫ g.f (g'.α i))
    infer_instance

/-- A family is covering for the tautological enlargement exactly when it is tautologically
equivalent to an original `K`-covering family. -/
theorem isCovering_tautologicalEnlargement_iff
    {K : Precoverage C} {X : C}
    {𝒱 : CoverFamily X} :
    IsCovering K.tautologicalEnlargement 𝒱 ↔
      ∃ 𝒰 : CoverFamily X,
        IsCovering K 𝒰 ∧ TautologicallyEquivalent 𝒰 𝒱 := by
  constructor
  · intro h𝒱
    -- Unpack the enlargement witness and replace presieve equality by a tautological equivalence.
    rcases h𝒱 with ⟨𝒰, 𝒲, h𝒰, h𝒰𝒲, h𝒲𝒱⟩
    have h𝒲𝒱' : TautologicallyEquivalent 𝒲 𝒱 :=
      combinatoriallyEquivalent_implies_tautologicallyEquivalent h𝒲𝒱
    exact ⟨𝒰, h𝒰, tautologicallyEquivalent_trans h𝒰𝒲 h𝒲𝒱'⟩
  · rintro ⟨𝒰, h𝒰, h𝒰𝒱⟩
    -- The defining enlargement witness can use the displayed target family itself.
    exact ⟨𝒰, 𝒱, h𝒰, h𝒰𝒱, rfl⟩

/-- Every original `K`-cover is also a cover for the tautological enlargement. -/
theorem le_tautologicalEnlargement (K : Precoverage C) :
    K ≤ K.tautologicalEnlargement := by
  intro X R hR
  obtain ⟨ι, Y, f, rfl⟩ := R.exists_eq_ofArrows
  let 𝒰 : CoverFamily X := ofArrows Y f
  have h𝒰 : IsCovering K 𝒰 := by
    -- Repackage the original covering presieve as its canonical indexed family of arrows.
    simpa [𝒰, IsCovering] using hR
  have h𝒰𝒰 : TautologicallyEquivalent 𝒰 𝒰 := by
    -- Identity maps witness tautological equivalence of a family with itself.
    refine ⟨
      { α := fun i ↦ i
        f := fun i ↦ 𝟙 (𝒰.obj i) },
      { α := fun i ↦ i
        f := fun i ↦ 𝟙 (𝒰.obj i) },
      ?_, ?_⟩
    · intro i
      change IsIso (𝟙 (𝒰.obj i))
      infer_instance
    · intro i
      change IsIso (𝟙 (𝒰.obj i))
      infer_instance
  exact ⟨𝒰, 𝒰, h𝒰, h𝒰𝒰, rfl⟩

/-- Remark 7.48.4 (1'): singleton isomorphism families are covering for the tautological
enlargement whenever the original site has isomorphism coverings. -/
theorem mem_tautologicalEnlargement_of_isIso
    {K : Precoverage C} [K.HasIsos]
    {X Y : C} (f : Y ⟶ X) [IsIso f] :
    Presieve.singleton f ∈ K.tautologicalEnlargement X := by
  -- Push the original singleton isomorphism cover through the inclusion into the enlargement.
  exact (le_tautologicalEnlargement K) X (Precoverage.mem_coverings_of_isIso f)

instance instHasIsos_tautologicalEnlargement
    (K : Precoverage C) [K.HasIsos] :
    K.tautologicalEnlargement.HasIsos where
  mem_coverings_of_isIso f := mem_tautologicalEnlargement_of_isIso f

/-- Helper for Remark 7.48.4: reindexing an `ofArrows` family by `ULift` does not change the
covering predicate. -/
theorem isCovering_ofArrows_ulift_iff
    {J : Precoverage C} {ι : Type w} {S : C}
    (X : ι → C) (f : ∀ i, X i ⟶ S) :
    IsCovering J
        (ofArrows (fun i : ULift.{max u v} ι ↦ X i.down) fun i ↦ f i.down) ↔
      Presieve.ofArrows X f ∈ J S := by
  -- The lifted indexing type presents the same presieve, so covering is unchanged.
  simpa [IsCovering] using
    congrArg (fun R : Presieve S ↦ R ∈ J S)
      (toPresieve_ofArrows_ulift (Uᵢ := X) (π := f))

/-- Helper for Remark 7.48.4: postcomposing an original covering family with an isomorphism
preserves covering, because we may compose with the singleton isomorphism cover. -/
theorem isCovering_postcompose_iso
    {K : Precoverage C} [K.HasIsos] [K.IsStableUnderComposition]
    {X Y : C} (e : X ⟶ Y) [IsIso e]
    {𝒰 : CoverFamily X} (h𝒰 : IsCovering K 𝒰) :
    IsCovering K (ofArrows (fun i ↦ (𝒰.obj i).left) fun i ↦ (𝒰.obj i).hom ≫ e) := by
  let X₀ : PUnit → C := fun _ ↦ X
  let e₀ : ∀ _ : PUnit, X₀ () ⟶ Y := fun _ ↦ e
  have he : Presieve.ofArrows X₀ e₀ ∈ K Y := by
    -- The outer family is just the singleton isomorphism cover of `e`.
    simpa [X₀, e₀, Presieve.ofArrows_of_unique] using Precoverage.mem_coverings_of_isIso e
  have hcomp :
      Presieve.ofArrows
          (fun p : Σ _ : PUnit, 𝒰.index ↦ (𝒰.obj p.2).left)
          (fun p ↦ (𝒰.obj p.2).hom ≫ e) ∈
        K Y := by
    -- Compose the singleton isomorphism cover with the given covering family.
    simpa [X₀, e₀, IsCovering] using
      (Precoverage.comp_mem_coverings (J := K) e₀ he
        (fun _ i ↦ (𝒰.obj i).hom) fun _ ↦ by
          simpa [IsCovering] using h𝒰)
  have hreindex :
      Presieve.ofArrows
          (fun p : Σ _ : PUnit, 𝒰.index ↦ (𝒰.obj p.2).left)
          (fun p ↦ (𝒰.obj p.2).hom ≫ e) =
        Presieve.ofArrows
          (fun i ↦ (𝒰.obj i).left)
          (fun i ↦ (𝒰.obj i).hom ≫ e) := by
    -- Remove the dummy singleton index by the obvious surjective projection.
    simpa using
      (Presieve.ofArrows_comp_eq_of_surjective
        (f := fun i : 𝒰.index ↦ (𝒰.obj i).hom ≫ e)
        (a := fun p : Σ _ : PUnit, 𝒰.index ↦ p.2)
        (by
          intro i
          exact ⟨⟨PUnit.unit, i⟩, rfl⟩))
  simpa [IsCovering] using (hreindex ▸ hcomp)

/-- Helper for Remark 7.48.4: a family consisting of the identity arrow together with any number
of isomorphisms to the same target is covering for the tautological enlargement. -/
theorem covering_of_identity_augmented_iso_family
    {K : Precoverage C} [K.HasIsos]
    {X : C} {ι : Type (max u v)} {Y : ι → C}
    (a : ∀ i, Y i ⟶ X) [∀ i, IsIso (a i)] :
    Presieve.ofArrows
        (fun s : Sum ι Unit ↦ Sum.elim Y (fun _ ↦ X) s)
        (fun
          | Sum.inl i => a i
          | Sum.inr _ => 𝟙 X) ∈
      K.tautologicalEnlargement X := by
  let 𝒰 : CoverFamily X := ofArrows (fun _ : PUnit ↦ X) fun _ ↦ 𝟙 X
  let 𝒱 : CoverFamily X :=
    ofArrows
      (fun s : Sum ι Unit ↦ Sum.elim Y (fun _ ↦ X) s)
      (fun
        | Sum.inl i => a i
        | Sum.inr _ => 𝟙 X)
  have hIso : ∀ i, IsIso (a i) := inferInstance
  have h𝒰 : IsCovering K 𝒰 := by
    -- The singleton identity family is an original `K`-cover because identities are isomorphisms.
    simpa [𝒰, IsCovering, Presieve.ofArrows_of_unique] using
      (Precoverage.mem_coverings_of_isIso (J := K) (𝟙 X))
  have h𝒰𝒱 : TautologicallyEquivalent 𝒰 𝒱 := by
    -- Route correction: instead of forcing a literal `K`-cover immediately, first exhibit the
    -- augmented family as tautologically equivalent to the singleton identity family.
    let φ : 𝒰 ⟶ 𝒱 :=
      { α := fun _ ↦ Sum.inr ()
        f := fun _ ↦ 𝟙 _ }
    let ψ : 𝒱 ⟶ 𝒰 :=
      { α := fun
          | Sum.inl _ => PUnit.unit
          | Sum.inr _ => PUnit.unit
        f := fun
          | Sum.inl i =>
              let e : Over.mk (a i) ≅ Over.mk (𝟙 X) :=
                by
                  haveI : IsIso (a i) := hIso i
                  let b : X ⟶ Y i := inv (a i)
                  have hb₁ : a i ≫ b = 𝟙 (Y i) := by
                    simpa [b] using (IsIso.hom_inv_id (a i))
                  have hb₂ : b ≫ a i = 𝟙 X := by
                    simpa [b] using (IsIso.inv_hom_id (a i))
                  refine Over.isoMk ?_ ?_
                  · exact ⟨a i, b, hb₁, hb₂⟩
                  · simp
              e.hom
          | Sum.inr _ => 𝟙 _ }
    refine ⟨φ, ψ, ?_, ?_⟩
    · intro u
      -- The forward component is the identity on the singleton identity branch.
      change IsIso (𝟙 (𝒰.obj u))
      infer_instance
    · intro s
      -- Each backward component is either the chosen isomorphism `a i` or the identity.
      cases s with
      | inl i =>
          change IsIso
            ((let e : Over.mk (a i) ≅ Over.mk (𝟙 X) :=
                by
                  haveI : IsIso (a i) := hIso i
                  let b : X ⟶ Y i := inv (a i)
                  have hb₁ : a i ≫ b = 𝟙 (Y i) := by
                    simpa [b] using (IsIso.hom_inv_id (a i))
                  have hb₂ : b ≫ a i = 𝟙 X := by
                    simpa [b] using (IsIso.inv_hom_id (a i))
                  refine Over.isoMk ?_ ?_
                  · exact ⟨a i, b, hb₁, hb₂⟩
                  · simp
              e.hom))
          dsimp
          infer_instance
      | inr u =>
          change IsIso (𝟙 (𝒱.obj (Sum.inr u)))
          infer_instance
  -- Package the original singleton cover together with the explicit tautological equivalence.
  simpa [IsCovering, 𝒱] using
    (isCovering_tautologicalEnlargement_iff (K := K) (𝒱 := 𝒱)).2 ⟨𝒰, h𝒰, h𝒰𝒱⟩

/-- Helper for Remark 7.48.4: rewrite the triangle identity from `Presieve.ofArrows_surj` into the
shape expected by `Over.isoMk`. -/
theorem over_isoMk_hom
    {S : C} {A B : Over S}
    (hleft : B.left = A.left)
    (hhom : A.hom = eqToHom hleft.symm ≫ B.hom) :
    (eqToIso hleft.symm).hom ≫ B.hom = A.hom := by
  -- This is the same triangle equation, read in the direction required by `Over.isoMk`.
  simpa using hhom.symm

/-- Helper for Remark 7.48.4: an equality of slice generators yields an explicit slice
isomorphism. -/
noncomputable def over_iso_of_left_eq_hom
    {S : C} {A B : Over S}
    (hleft : B.left = A.left)
    (hhom : A.hom = eqToHom hleft.symm ≫ B.hom) :
    A ≅ B :=
  Over.isoMk (eqToIso hleft.symm) (over_isoMk_hom hleft hhom)

/-- Helper for Remark 7.48.4: the underlying arrow of an isomorphism in a slice category is an
isomorphism in the ambient category. -/
theorem isIso_left_of_over_hom
    {S : C} {A B : Over S} (u : A ⟶ B) [IsIso u] :
    IsIso u.left := by
  -- The forgetful functor from the slice category reflects isomorphisms.
  change IsIso ((Over.forget S).map u)
  infer_instance

/-- Helper for Remark 7.48.4: an ambient isomorphism can be recovered from an isomorphic arrow. -/
noncomputable abbrev iso_of_isIso
    {X Y : C} (u : X ⟶ Y) [IsIso u] :
    X ≅ Y :=
  asIso u

/-- Helper for Remark 7.48.4: packaging an isomorphic underlying arrow into a morphism of slice
objects preserves the isomorphism. -/
theorem isIso_homMk_of_isIso_left
    {S X Y : C} {f : X ⟶ S} {g : Y ⟶ S}
    (u : X ⟶ Y) [IsIso u] (hu : u ≫ g = f) :
    IsIso (Over.homMk u hu : Over.mk f ⟶ Over.mk g) := by
  -- Package the same underlying isomorphism as an explicit isomorphism in the slice category.
  let e : Over.mk f ≅ Over.mk g := Over.isoMk (@iso_of_isIso _ _ _ _ u ‹IsIso u›) hu
  simpa [e] using (show IsIso e.hom from inferInstance)

/-- Helper for Remark 7.48.4: postcomposing a tautological equivalence by a fixed target map keeps
the two families tautologically equivalent over the new target. -/
theorem tautologicallyEquivalent_postcompose
    {X S : C} {𝒰 𝒱 : CoverFamily X}
    (h𝒰𝒱 : TautologicallyEquivalent 𝒰 𝒱)
    (f : X ⟶ S) :
    TautologicallyEquivalent
      (ofArrows (fun i ↦ (𝒰.obj i).left) fun i ↦ (𝒰.obj i).hom ≫ f)
      (ofArrows (fun i ↦ (𝒱.obj i).left) fun i ↦ (𝒱.obj i).hom ≫ f) := by
  -- Reuse the same component maps, now viewed in the slice over the larger target.
  rcases h𝒰𝒱 with ⟨φ, ψ, hφ, hψ⟩
  let φ' :
      ofArrows (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom ≫ f) ⟶
        ofArrows (fun i ↦ (𝒱.obj i).left) (fun i ↦ (𝒱.obj i).hom ≫ f) :=
    { α := φ.α
      f := fun i ↦ Over.homMk (φ.f i).left (by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ f) (Over.w (φ.f i))) }
  let ψ' :
      ofArrows (fun i ↦ (𝒱.obj i).left) (fun i ↦ (𝒱.obj i).hom ≫ f) ⟶
        ofArrows (fun i ↦ (𝒰.obj i).left) (fun i ↦ (𝒰.obj i).hom ≫ f) :=
    { α := ψ.α
      f := fun i ↦ Over.homMk (ψ.f i).left (by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ f) (Over.w (ψ.f i))) }
  refine ⟨
    φ',
    ψ',
    ?_, ?_⟩
  · intro i
    -- The postcomposed component is an isomorphism because its underlying arrow already was.
    haveI : IsIso (φ.f i) := hφ i
    haveI : IsIso (φ.f i).left := isIso_left_of_over_hom (φ.f i)
    have hpost :
        (φ.f i).left ≫ ((𝒱.obj (φ.α i)).hom ≫ f) =
          (𝒰.obj i).hom ≫ f := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ f) (Over.w (φ.f i))
    simpa [φ'] using
      (isIso_homMk_of_isIso_left (u := (φ.f i).left) hpost)
  · intro i
    -- The backward component is handled by the same underlying-arrow argument.
    haveI : IsIso (ψ.f i) := hψ i
    haveI : IsIso (ψ.f i).left := isIso_left_of_over_hom (ψ.f i)
    have hpost :
        (ψ.f i).left ≫ ((𝒰.obj (ψ.α i)).hom ≫ f) =
          (𝒱.obj i).hom ≫ f := by
      simpa [Category.assoc] using congrArg (fun k ↦ k ≫ f) (Over.w (ψ.f i))
    simpa [ψ'] using
      (isIso_homMk_of_isIso_left (u := (ψ.f i).left) hpost)

/-- Helper for Remark 7.48.4: tautological equivalences on each fibre remain tautological after
forming the sigma-family and postcomposing with the outer arrows. -/
theorem sigma_postcompose_tautologically_equivalent
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {𝒜 ℬ : ∀ i, CoverFamily (X i)}
    (h : ∀ i, TautologicallyEquivalent (𝒜 i) (ℬ i)) :
    TautologicallyEquivalent
      (ofArrows
        (fun p : Σ i, (𝒜 i).index ↦ ((𝒜 p.1).obj p.2).left)
        (fun p ↦ ((𝒜 p.1).obj p.2).hom ≫ f p.1))
      (ofArrows
        (fun p : Σ i, (ℬ i).index ↦ ((ℬ p.1).obj p.2).left)
        (fun p ↦ ((ℬ p.1).obj p.2).hom ≫ f p.1)) := by
  classical
  -- Choose the componentwise comparison maps and package them into sigma-family morphisms.
  choose φ ψ hφ hψ using h
  let φ' :
      ofArrows
          (fun p : Σ i, (𝒜 i).index ↦ ((𝒜 p.1).obj p.2).left)
          (fun p ↦ ((𝒜 p.1).obj p.2).hom ≫ f p.1) ⟶
        ofArrows
          (fun p : Σ i, (ℬ i).index ↦ ((ℬ p.1).obj p.2).left)
          (fun p ↦ ((ℬ p.1).obj p.2).hom ≫ f p.1) :=
    { α := fun p ↦ ⟨p.1, (φ p.1).α p.2⟩
      f := fun p ↦ Over.homMk (((φ p.1).f p.2).left) (by
        simpa [Category.assoc] using
          congrArg (fun k ↦ k ≫ f p.1) (Over.w ((φ p.1).f p.2))) }
  let ψ' :
      ofArrows
          (fun p : Σ i, (ℬ i).index ↦ ((ℬ p.1).obj p.2).left)
          (fun p ↦ ((ℬ p.1).obj p.2).hom ≫ f p.1) ⟶
        ofArrows
          (fun p : Σ i, (𝒜 i).index ↦ ((𝒜 p.1).obj p.2).left)
          (fun p ↦ ((𝒜 p.1).obj p.2).hom ≫ f p.1) :=
    { α := fun p ↦ ⟨p.1, (ψ p.1).α p.2⟩
      f := fun p ↦ Over.homMk (((ψ p.1).f p.2).left) (by
        simpa [Category.assoc] using
          congrArg (fun k ↦ k ≫ f p.1) (Over.w ((ψ p.1).f p.2))) }
  refine ⟨φ', ψ', ?_, ?_⟩
  · intro p
    -- Each sigma-component remains an isomorphism because the chosen fibrewise component was one.
    haveI : IsIso ((φ p.1).f p.2) := hφ p.1 p.2
    haveI : IsIso (((φ p.1).f p.2).left) := isIso_left_of_over_hom ((φ p.1).f p.2)
    have hpost :
        ((φ p.1).f p.2).left ≫ (((ℬ p.1).obj ((φ p.1).α p.2)).hom ≫ f p.1) =
          ((𝒜 p.1).obj p.2).hom ≫ f p.1 := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ f p.1) (Over.w ((φ p.1).f p.2))
    simpa [φ'] using
      (isIso_homMk_of_isIso_left (u := ((φ p.1).f p.2).left) hpost)
  · intro p
    -- The backward sigma-component is handled by the same underlying-arrow argument.
    haveI : IsIso ((ψ p.1).f p.2) := hψ p.1 p.2
    haveI : IsIso (((ψ p.1).f p.2).left) := isIso_left_of_over_hom ((ψ p.1).f p.2)
    have hpost :
        ((ψ p.1).f p.2).left ≫ (((𝒜 p.1).obj ((ψ p.1).α p.2)).hom ≫ f p.1) =
          ((ℬ p.1).obj p.2).hom ≫ f p.1 := by
      simpa [Category.assoc] using
        congrArg (fun k ↦ k ≫ f p.1) (Over.w ((ψ p.1).f p.2))
    simpa [ψ'] using
      (isIso_homMk_of_isIso_left (u := ((ψ p.1).f p.2).left) hpost)

/-- Helper for Remark 7.48.4: if a small fixed-target family generates the same presieve as a
displayed family of arrows, then every chosen small generator is isomorphic in the slice to one of
the displayed generators, and conversely. -/
noncomputable def generator_isos_of_toPresieve_eq
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {𝒻 : CoverFamily S}
    (hpres : 𝒻.toPresieve = Presieve.ofArrows X f) :
    Σ α : 𝒻.index → ι, Σ β : ι → 𝒻.index,
      (∀ k, 𝒻.obj k ≅ Over.mk (f (α k))) ×
      (∀ i, Over.mk (f i) ≅ 𝒻.obj (β i)) := by
  classical
  have hα :
      ∀ k : 𝒻.index, Σ i : ι, 𝒻.obj k ≅ Over.mk (f i) := by
    intro k
    -- Read the `k`-th small generator as a displayed generator of the original presieve.
    let hk := Classical.choose <|
      Presieve.ofArrows_surj f ((𝒻.obj k).hom) (hpres.le _ _ (Presieve.ofArrows.mk k))
    let hk' := Classical.choose_spec <|
      Presieve.ofArrows_surj f ((𝒻.obj k).hom) (hpres.le _ _ (Presieve.ofArrows.mk k))
    let hobj : X hk = (𝒻.obj k).left := Classical.choose hk'
    let hhom : (𝒻.obj k).hom = eqToHom hobj.symm ≫ f hk := Classical.choose_spec hk'
    exact ⟨hk, over_iso_of_left_eq_hom (A := 𝒻.obj k) (B := Over.mk (f hk)) hobj hhom⟩
  have hβ :
      ∀ i : ι, Σ k : 𝒻.index, Over.mk (f i) ≅ 𝒻.obj k := by
    intro i
    -- Conversely, every displayed generator appears among the chosen small generators.
    let hi := Classical.choose <|
      Presieve.ofArrows_surj
        (fun k : 𝒻.index ↦ (𝒻.obj k).hom) (f i) (hpres.ge _ _ (Presieve.ofArrows.mk i))
    let hi' := Classical.choose_spec <|
      Presieve.ofArrows_surj
        (fun k : 𝒻.index ↦ (𝒻.obj k).hom) (f i) (hpres.ge _ _ (Presieve.ofArrows.mk i))
    let hobj : (𝒻.obj hi).left = X i := Classical.choose hi'
    let hhom : f i = eqToHom hobj.symm ≫ (𝒻.obj hi).hom := Classical.choose_spec hi'
    exact ⟨hi, over_iso_of_left_eq_hom (A := Over.mk (f i)) (B := 𝒻.obj hi) hobj hhom⟩
  let α : 𝒻.index → ι := fun k ↦ (hα k).1
  let eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)) := fun k ↦ (hα k).2
  let β : ι → 𝒻.index := fun i ↦ (hβ i).1
  let eβ : ∀ i, Over.mk (f i) ≅ 𝒻.obj (β i) := fun i ↦ (hβ i).2
  -- Package the two chosen reindexings and their slice isomorphisms.
  exact ⟨α, β, eα, eβ⟩

/-- Helper for Remark 7.48.4: a chosen pullback square may be transported across a slice
isomorphism by postcomposing the left leg with the inverse underlying arrow. -/
theorem isPullback_comp_inv_left_of_iso
    {S Y X P : C} {p₁ : P ⟶ Y} {p₂ : P ⟶ X} {g : Y ⟶ S} {f : X ⟶ S}
    (h : IsPullback p₁ p₂ g f)
    {A : CategoryTheory.Over S} (e : A ≅ Over.mk f) :
    IsPullback p₁ (p₂ ≫ e.inv.left) g A.hom := by
  -- Transport the bottom-left object of the pullback square along the slice isomorphism `e`.
  let eLeft : X ≅ A.left := (Over.forget S).mapIso e.symm
  refine h.of_iso (Iso.refl _) (Iso.refl _) eLeft (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp [eLeft]
  · simp
  · simpa [eLeft] using (Over.w e.inv).symm

/-- Helper for Remark 7.48.4: the outer tautological-equivalence witness identifies each original
outer generator with the corresponding displayed generator of `f`. -/
noncomputable abbrev outer_generator_iso
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    (u : 𝒰.index) :
    𝒰.obj u ≅ Over.mk (f (α (φ.α u))) :=
  @asIso _ _ _ _ (φ.f u) (hφ u) ≪≫ eα (φ.α u)

/-- Helper for Remark 7.48.4: the inverse of the transported outer-generator isomorphism rewrites
the original outer arrow back to the displayed arrow `f (α (φ.α u))`. -/
theorem outer_generator_iso_inv_left_hom
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    (u : 𝒰.index) :
    (outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u).inv.left ≫ (𝒰.obj u).hom =
      f (α (φ.α u)) := by
  -- Read the inverse slice morphism equation as an identity in the ambient category.
  simpa [outer_generator_iso] using
    (Over.w ((outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u).inv))

/-- Helper for Remark 7.48.4: the backward outer transport coming from `β` and `ψ` rewrites the
displayed outer arrow `f i` to the corresponding original outer generator. -/
theorem outer_backward_transport_hom
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (ψ : 𝒻 ⟶ 𝒰)
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {β : ι → 𝒻.index}
    (eβ : ∀ i, Over.mk (f i) ≅ 𝒻.obj (β i))
    (i : ι) :
    ((eβ i).hom ≫ ψ.f (β i)).left ≫ (𝒰.obj (ψ.α (β i))).hom = f i := by
  -- Read the composite slice morphism equation in the ambient category.
  simpa [Category.assoc] using Over.w ((eβ i).hom ≫ ψ.f (β i))

/-- Helper for Remark 7.48.4: the backward outer witness packages each displayed outer arrow `f i`
as an explicit slice isomorphism to the corresponding original outer generator. -/
noncomputable abbrev outer_backward_component_iso
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (ψ : 𝒻 ⟶ 𝒰)
    (hψ : ∀ k : 𝒻.index, IsIso (ψ.f k))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {β : ι → 𝒻.index}
    (eβ : ∀ i, Over.mk (f i) ≅ 𝒻.obj (β i))
    (i : ι) :
    Over.mk (f i) ≅ 𝒰.obj (ψ.α (β i)) :=
  eβ i ≪≫ @asIso _ _ _ _ (ψ.f (β i)) (hψ (β i))

/-- Helper for Remark 7.48.4: transporting a displayed fibre family along the backward outer
comparison lands it over the corresponding original outer generator selected by `ψ` and `β`. -/
noncomputable abbrev backwardTransportedInnerFamily
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (ψ : 𝒻 ⟶ 𝒰)
    (hψ : ∀ k : 𝒻.index, IsIso (ψ.f k))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {β : ι → 𝒻.index}
    (eβ : ∀ i, Over.mk (f i) ≅ 𝒻.obj (β i))
    (𝒜 : ∀ i, CoverFamily (X i))
    (i : ι) :
    CoverFamily (𝒰.obj (ψ.α (β i))).left :=
  ofArrows
    (fun j ↦ ((𝒜 i).obj j).left)
    (fun j ↦ ((𝒜 i).obj j).hom ≫
      (outer_backward_component_iso (ψ := ψ) hψ (f := f) (β := β) eβ i).hom.left)

/-- Helper for Remark 7.48.4: each backward-transported original inner family is still a genuine
`K`-cover, because the backward outer comparison is an isomorphism in the ambient category. -/
theorem backward_transported_inner_family_is_covering
    {K : Precoverage C} [K.HasIsos] [K.IsStableUnderComposition]
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (ψ : 𝒻 ⟶ 𝒰)
    (hψ : ∀ k : 𝒻.index, IsIso (ψ.f k))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {β : ι → 𝒻.index}
    (eβ : ∀ i, Over.mk (f i) ≅ 𝒻.obj (β i))
    {𝒲 : ∀ i, CoverFamily (X i)}
    (h𝒲 : ∀ i, IsCovering K (𝒲 i)) :
    ∀ i, IsCovering K (backwardTransportedInnerFamily (ψ := ψ) hψ (f := f) (β := β) eβ 𝒲 i) := by
  intro i
  -- Transport the `i`-th original inner cover along the backward outer comparison.
  haveI :
      IsIso ((outer_backward_component_iso (ψ := ψ) hψ (f := f) (β := β) eβ i).hom.left) :=
    isIso_left_of_over_hom
      ((outer_backward_component_iso (ψ := ψ) hψ (f := f) (β := β) eβ i).hom)
  simpa [backwardTransportedInnerFamily] using
    (isCovering_postcompose_iso
      (K := K)
      ((outer_backward_component_iso (ψ := ψ) hψ (f := f) (β := β) eβ i).hom.left)
      (h𝒲 i))

/-- Helper for Remark 7.48.4: fibrewise tautological equivalences remain tautological after
backward transport along the chosen outer comparison. -/
theorem backward_transported_inner_family_tautologicallyEquivalent
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (ψ : 𝒻 ⟶ 𝒰)
    (hψ : ∀ k : 𝒻.index, IsIso (ψ.f k))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {β : ι → 𝒻.index}
    (eβ : ∀ i, Over.mk (f i) ≅ 𝒻.obj (β i))
    {𝒲 𝒢 : ∀ i, CoverFamily (X i)}
    (h : ∀ i, TautologicallyEquivalent (𝒲 i) (𝒢 i)) :
    ∀ i,
      TautologicallyEquivalent
        (backwardTransportedInnerFamily (ψ := ψ) hψ (f := f) (β := β) eβ 𝒲 i)
        (backwardTransportedInnerFamily (ψ := ψ) hψ (f := f) (β := β) eβ 𝒢 i) := by
  intro i
  -- Postcompose the chosen fibrewise equivalence by the same backward outer isomorphism.
  simpa [backwardTransportedInnerFamily] using
    (tautologicallyEquivalent_postcompose
      (h i)
      ((outer_backward_component_iso (ψ := ψ) hψ (f := f) (β := β) eβ i).hom.left))

/-- Helper for Remark 7.48.4: after unfolding the transported outer-generator isomorphism, the
underlying ambient morphism still collapses to the displayed outer arrow. -/
theorem outer_generator_expanded_inv_left_hom
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    (u : 𝒰.index) :
    (eα (φ.α u)).inv.left ≫ (inv (φ.f u)).left ≫ (𝒰.obj u).hom =
      f (α (φ.α u)) := by
  -- First rewrite the inverse outer component back to the chosen small generator of `𝒻`.
  haveI : IsIso (φ.f u) := hφ u
  have hφinv : (inv (φ.f u)).left ≫ (𝒰.obj u).hom = (𝒻.obj (φ.α u)).hom := by
    simpa using (Over.w (inv (φ.f u)))
  have heαinv : (eα (φ.α u)).inv.left ≫ (𝒻.obj (φ.α u)).hom = f (α (φ.α u)) := by
    simpa using (Over.w (eα (φ.α u)).inv)
  rw [hφinv]
  exact heαinv

/-- Helper for Remark 7.48.4: whiskering the transported outer-generator comparison by an
additional incoming morphism produces the corresponding whiskered displayed arrow. -/
theorem whisker_outer_generator_expanded_inv_left_hom
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    {A : C} (u : 𝒰.index) (a : A ⟶ X (α (φ.α u))) :
    a ≫ (eα (φ.α u)).inv.left ≫ (inv (φ.f u)).left ≫ (𝒰.obj u).hom =
      a ≫ f (α (φ.α u)) := by
  -- Reassociate once, then use the unwhiskered transport identity.
  simpa [Category.assoc] using
    congrArg (fun k ↦ a ≫ k)
      (outer_generator_expanded_inv_left_hom (φ := φ) hφ (f := f) (α := α) eα u)

/-- Helper for Remark 7.48.4: for a fixed fibre family, transporting along the inverse
outer-generator isomorphism gives a family over the corresponding original outer generator. -/
noncomputable abbrev transportedInnerFamily
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    (𝒜 : ∀ i, CoverFamily (X i))
    (u : 𝒰.index) : CoverFamily (𝒰.obj u).left :=
  ofArrows
    (fun j ↦ ((𝒜 (α (φ.α u))).obj j).left)
    (fun j ↦
      ((𝒜 (α (φ.α u))).obj j).hom ≫
        (outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u).inv.left)

/-- Helper for Remark 7.48.4: each transported inner generator has the same source object as the
original inner generator it came from. -/
theorem transportedInnerFamily_obj_left
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    (𝒜 : ∀ i, CoverFamily (X i))
    (u : 𝒰.index) (j : (transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒜 u).index) :
    ((transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒜 u).obj j).left =
      ((𝒜 (α (φ.α u))).obj j).left := by
  rfl

/-- Helper for Remark 7.48.4: the underlying arrow of a transported inner generator is the
original inner arrow postcomposed with the inverse transported outer-generator isomorphism. -/
theorem transportedInnerFamily_obj_hom
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    (𝒜 : ∀ i, CoverFamily (X i))
    (u : 𝒰.index) (j : (transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒜 u).index) :
    ((transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒜 u).obj j).hom =
      ((𝒜 (α (φ.α u))).obj j).hom ≫
        (outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u).inv.left := by
  rfl

/-- Helper for Remark 7.48.4: composing the transported fibre families with the original outer
cover packages the source-faithful sigma-family that lives over `S`. -/
noncomputable abbrev transportedSigmaFamily
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    (𝒜 : ∀ i, CoverFamily (X i)) : CoverFamily S :=
  ofArrows
    (fun p : Σ u, (transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒜 u).index ↦
      ((transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒜 p.1).obj p.2).left)
    (fun p ↦
      ((transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒜 p.1).obj p.2).hom ≫
        (𝒰.obj p.1).hom)

/-- Helper for Remark 7.48.4: the directly displayed sigma-family over the chosen outer legs. -/
abbrev displayedSigmaFamily
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (𝒜 : ∀ i, CoverFamily (X i)) : CoverFamily S :=
  ofArrows
    (fun p : Σ u, (𝒜 (α (φ.α u))).index ↦ ((𝒜 (α (φ.α p.1))).obj p.2).left)
    (fun p ↦ ((𝒜 (α (φ.α p.1))).obj p.2).hom ≫ f (α (φ.α p.1)))

/-- Helper for Remark 7.48.4: an equality of domains and arrows in the slice category gives
literal equality of the corresponding slice objects. -/
theorem over_obj_eq_of_left_eq_hom
    {S : C} {A B : Over S}
    (hleft : B.left = A.left)
    (hhom : A.hom = eqToHom hleft.symm ≫ B.hom) :
    A = B := by
  -- Extensionality in the slice category reduces object equality to equality of domains and maps.
  simpa using
    (CostructuredArrow.obj_ext A B hleft.symm hhom.symm)

/-- Helper for Remark 7.48.4: the transported sigma-family and the directly displayed sigma-family
generate the same presieve, because the outer-generator comparison rewrites every composite arrow
back to the displayed outer leg. -/
theorem transported_sigma_family_combinatorially_equivalent
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    (𝒜 : ∀ i, CoverFamily (X i)) :
    CombinatoriallyEquivalent
      (transportedSigmaFamily (φ := φ) hφ (f := f) (α := α) eα 𝒜)
      (displayedSigmaFamily (φ := φ) (f := f) (α := α) 𝒜) := by
  -- Identify corresponding generators by the identity reindexing once the outer transport is
  -- rewritten back to the displayed outer leg.
  refine (combinatoriallyEquivalent_iff_exists_reindexings).2 ?_
  refine ⟨fun p ↦ p, fun p ↦ p, ?_, ?_⟩
  · intro p
    change
      Over.mk
          ((((transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒜 p.1).obj p.2).hom ≫
              (𝒰.obj p.1).hom)) =
        Over.mk ((((𝒜 (α (φ.α p.1))).obj p.2).hom ≫ f (α (φ.α p.1))))
    rw [transportedInnerFamily_obj_hom (φ := φ) hφ (f := f) (α := α) eα 𝒜 p.1 p.2]
    have hmk :
        Over.mk
            ((((𝒜 (α (φ.α p.1))).obj p.2).hom ≫
                (eα (φ.α p.1)).inv.left ≫
                (inv (φ.f p.1)).left) ≫
              (𝒰.obj p.1).hom) =
          Over.mk ((((𝒜 (α (φ.α p.1))).obj p.2).hom ≫ f (α (φ.α p.1)))) := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ Over.mk ((((𝒜 (α (φ.α p.1))).obj p.2).hom ≫ k)))
          (outer_generator_expanded_inv_left_hom
            (φ := φ) hφ (f := f) (α := α) eα p.1)
    exact hmk
  · intro p
    change
      Over.mk ((((𝒜 (α (φ.α p.1))).obj p.2).hom ≫ f (α (φ.α p.1)))) =
        Over.mk
          ((((transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒜 p.1).obj p.2).hom ≫
              (𝒰.obj p.1).hom))
    rw [transportedInnerFamily_obj_hom (φ := φ) hφ (f := f) (α := α) eα 𝒜 p.1 p.2]
    have hmk :
        Over.mk
            ((((𝒜 (α (φ.α p.1))).obj p.2).hom ≫
                (eα (φ.α p.1)).inv.left ≫
                (inv (φ.f p.1)).left) ≫
              (𝒰.obj p.1).hom) =
          Over.mk ((((𝒜 (α (φ.α p.1))).obj p.2).hom ≫ f (α (φ.α p.1)))) := by
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ Over.mk ((((𝒜 (α (φ.α p.1))).obj p.2).hom ≫ k)))
          (outer_generator_expanded_inv_left_hom
            (φ := φ) hφ (f := f) (α := α) eα p.1)
    exact hmk.symm

/-- Helper for Remark 7.48.4: after transporting the inner original covers along the outer
generator isomorphisms, the original composition axiom gives a genuine `K`-cover of `S`. -/
theorem transported_sigma_family_is_covering
    {K : Precoverage C} [K.HasIsos] [K.IsStableUnderComposition]
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (h𝒰 : IsCovering K 𝒰)
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    {𝒲 : ∀ i, CoverFamily (X i)}
    (h𝒲 : ∀ i, IsCovering K (𝒲 i)) :
    IsCovering K
      (ofArrows
        (fun p : Σ u, (𝒲 (α (φ.α u))).index ↦ ((𝒲 (α (φ.α p.1))).obj p.2).left)
        (fun p ↦ ((𝒲 (α (φ.α p.1))).obj p.2).hom ≫ f (α (φ.α p.1)))) := by
  let 𝒲t : ∀ u : 𝒰.index, CoverFamily (𝒰.obj u).left :=
    transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒲
  have h𝒲t :
      ∀ u : 𝒰.index, IsCovering K (𝒲t u) := by
    intro u
    -- Transport each inner original cover along the inverse outer-generator isomorphism.
    dsimp [𝒲t, transportedInnerFamily]
    exact isCovering_postcompose_iso
      (K := K)
      ((outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u).inv.left)
      (h𝒲 (α (φ.α u)))
  have hcomp :
      IsCovering K
        (transportedSigmaFamily (φ := φ) hφ (f := f) (α := α) eα 𝒲) := by
    -- Apply composition to the original outer cover and the transported inner covers.
    simpa [IsCovering, transportedSigmaFamily] using
      (Precoverage.comp_mem_coverings
        (J := K)
        (f := fun u ↦ (𝒰.obj u).hom)
        (by simpa [IsCovering] using h𝒰)
        (g := fun u j ↦ ((𝒲t u).obj j).hom)
        (fun u ↦ by simpa [IsCovering] using h𝒲t u))
  let hσ :
      (transportedSigmaFamily (φ := φ) hφ (f := f) (α := α) eα 𝒲).toPresieve =
        (displayedSigmaFamily (φ := φ) (f := f) (α := α) 𝒲).toPresieve :=
    transported_sigma_family_combinatorially_equivalent
      (φ := φ) hφ (f := f) (α := α) eα 𝒲
  -- Replace the transported sigma-family by the displayed one using presieve equality.
  have hcomp' :
      (displayedSigmaFamily (φ := φ) (f := f) (α := α) 𝒲).toPresieve ∈ K.coverings S := by
    rw [← hσ]
    simpa [IsCovering] using hcomp
  simpa [IsCovering, displayedSigmaFamily] using hcomp'

/-- Helper for Remark 7.48.4: transporting the fibrewise tautological equivalences and then
forming the sigma-family yields a tautological equivalence of composite families over `S`. -/
theorem transported_sigma_family_tautologically_equivalent
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    {𝒲 𝒢 : ∀ i, CoverFamily (X i)}
    (h : ∀ i, TautologicallyEquivalent (𝒲 i) (𝒢 i)) :
    TautologicallyEquivalent
      (ofArrows
        (fun p : Σ u, (𝒲 (α (φ.α u))).index ↦ ((𝒲 (α (φ.α p.1))).obj p.2).left)
        (fun p ↦ ((𝒲 (α (φ.α p.1))).obj p.2).hom ≫ f (α (φ.α p.1))))
      (ofArrows
        (fun p : Σ u, (𝒢 (α (φ.α u))).index ↦ ((𝒢 (α (φ.α p.1))).obj p.2).left)
        (fun p ↦ ((𝒢 (α (φ.α p.1))).obj p.2).hom ≫ f (α (φ.α p.1)))) := by
  let 𝒲t : ∀ u : 𝒰.index, CoverFamily (𝒰.obj u).left :=
    transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒲
  let 𝒢t : ∀ u : 𝒰.index, CoverFamily (𝒰.obj u).left :=
    transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒢
  have htransport :
      ∀ u : 𝒰.index, TautologicallyEquivalent (𝒲t u) (𝒢t u) := by
    intro u
    -- Transport each fibrewise tautological equivalence along the same inverse outer-generator.
    dsimp [𝒲t, 𝒢t, transportedInnerFamily]
    exact tautologicallyEquivalent_postcompose
      (h (α (φ.α u)))
      ((outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u).inv.left)
  have hsigma :
      TautologicallyEquivalent
        (transportedSigmaFamily (φ := φ) hφ (f := f) (α := α) eα 𝒲)
        (transportedSigmaFamily (φ := φ) hφ (f := f) (α := α) eα 𝒢) := by
    -- Package the transported fibrewise equivalences into the sigma-family over `S`.
    simpa [transportedSigmaFamily] using sigma_postcompose_tautologically_equivalent
      (f := fun u ↦ (𝒰.obj u).hom)
      htransport
  have h𝒲σ :
      TautologicallyEquivalent
        (displayedSigmaFamily (φ := φ) (f := f) (α := α) 𝒲)
        (transportedSigmaFamily (φ := φ) hφ (f := f) (α := α) eα 𝒲) :=
    combinatoriallyEquivalent_implies_tautologicallyEquivalent
      (transported_sigma_family_combinatorially_equivalent
        (φ := φ) hφ (f := f) (α := α) eα 𝒲).symm
  have h𝒢σ :
      TautologicallyEquivalent
        (transportedSigmaFamily (φ := φ) hφ (f := f) (α := α) eα 𝒢)
        (displayedSigmaFamily (φ := φ) (f := f) (α := α) 𝒢) :=
    combinatoriallyEquivalent_implies_tautologicallyEquivalent
      (transported_sigma_family_combinatorially_equivalent
        (φ := φ) hφ (f := f) (α := α) eα 𝒢)
  -- Compare the two displayed sigma-families by composing the transport equivalence with the two
  -- presieve-identification equivalences.
  exact tautologicallyEquivalent_trans h𝒲σ (tautologicallyEquivalent_trans hsigma h𝒢σ)

/-- Helper for Remark 7.48.4: the forward transported inner family over an original outer branch is
still a genuine `K`-cover. -/
theorem transported_inner_family_is_covering
    {K : Precoverage C} [K.HasIsos] [K.IsStableUnderComposition]
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    {𝒲 : ∀ i, CoverFamily (X i)}
    (h𝒲 : ∀ i, IsCovering K (𝒲 i)) :
    ∀ u : 𝒰.index,
      IsCovering K (transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒲 u) := by
  intro u
  -- Transport the chosen inner `K`-cover along the inverse outer-generator isomorphism.
  dsimp [transportedInnerFamily]
  exact isCovering_postcompose_iso
    (K := K)
    ((outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u).inv.left)
    (h𝒲 (α (φ.α u)))

/-- Helper for Remark 7.48.4: the forward transported displayed family remains tautologically
equivalent to the corresponding forward transported original family. -/
theorem transported_inner_family_tautologicallyEquivalent
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    {𝒲 𝒢 : ∀ i, CoverFamily (X i)}
    (h : ∀ i, TautologicallyEquivalent (𝒲 i) (𝒢 i)) :
    ∀ u : 𝒰.index,
      TautologicallyEquivalent
        (transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒲 u)
        (transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒢 u) := by
  intro u
  -- Postcompose the chosen fibrewise equivalence by the same inverse outer-generator.
  dsimp [transportedInnerFamily]
  exact tautologicallyEquivalent_postcompose
    (h (α (φ.α u)))
    ((outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u).inv.left)

/-- Helper for Remark 7.48.4: transporting the chosen pullback squares to the original outer cover
produces a genuine `K`-cover of the base-change target. -/
theorem transported_pullback_family_is_covering
    {K : Precoverage C} [K.IsStableUnderBaseChange]
    {S : C} {𝒻 𝒰 : CoverFamily S}
    (h𝒰 : IsCovering K 𝒰)
    (φ : 𝒰 ⟶ 𝒻)
    (hφ : ∀ u : 𝒰.index, IsIso (φ.f u))
    {ι : Type w} {X : ι → C} {f : ∀ i, X i ⟶ S}
    {α : 𝒻.index → ι}
    (eα : ∀ k, 𝒻.obj k ≅ Over.mk (f (α k)))
    {Y : C} (g : Y ⟶ S)
    {P : ι → C} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    IsCovering K
      (ofArrows
        (fun u ↦ P (α (φ.α u)))
        (fun u ↦ p₁ (α (φ.α u)))) := by
  have hpull :
      ∀ u,
        IsPullback
          (p₁ (α (φ.α u)))
          (p₂ (α (φ.α u)) ≫
            (outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u).inv.left)
          g
          (𝒰.obj u).hom := by
    intro u
    -- Transport the displayed pullback square along the inverse outer generator isomorphism.
    exact isPullback_comp_inv_left_of_iso
      (h (α (φ.α u)))
      (outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u)
  -- Apply the original base-change axiom to the original outer cover.
  simpa [IsCovering] using
    (Precoverage.mem_coverings_of_isPullback
      (J := K)
      (f := fun u ↦ (𝒰.obj u).hom)
      (by simpa [IsCovering] using h𝒰)
      g
      (p₁ := fun u ↦ p₁ (α (φ.α u)))
      (p₂ := fun u ↦
        p₂ (α (φ.α u)) ≫
          (outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u).inv.left)
      hpull)

/-- Helper for Remark 7.48.4: every generator of the transported sigma-family `𝒢σ` is isomorphic
to a chosen generator of any small presentation of the literal displayed composite presieve. -/
theorem composite_forward_small_presentation_iso
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {σ : ι → Type w'} {Y : ∀ i, σ i → C}
    (g : ∀ i j, Y i j ⟶ X i)
    {κ : Type (max u v)} (outer : κ → ι)
    {𝒢 : ∀ i, CoverFamily (X i)}
    (h𝒢 : ∀ i, Presieve.ofArrows (Y i) (g i) = (𝒢 i).toPresieve)
    {𝒢σ Dσ : CoverFamily S}
    (h𝒢σ :
      𝒢σ =
        ofArrows
          (fun p : Σ u : κ, (𝒢 (outer u)).index ↦ ((𝒢 (outer p.1)).obj p.2).left)
          (fun p ↦ ((𝒢 (outer p.1)).obj p.2).hom ≫ f (outer p.1)))
    (hDσPres :
      Dσ.toPresieve =
        Presieve.ofArrows
          (fun p : Σ i, σ i ↦ Y p.1 p.2)
          (fun p ↦ g p.1 p.2 ≫ f p.1)) :
    ∀ q : 𝒢σ.index, ∃ r : Dσ.index, Nonempty (𝒢σ.obj q ≅ Dσ.obj r) := by
  classical
  subst h𝒢σ
  intro q
  let i : ι := outer q.1
  -- First replace the chosen inner small generator by one literal displayed inner generator.
  have hinner :
      Presieve.ofArrows (Y i) (g i) (((𝒢 i).obj q.2).hom) :=
    (h𝒢 i).ge _ _ (Presieve.ofArrows.mk q.2)
  obtain ⟨j, hjleft, hjhom⟩ := Presieve.ofArrows_surj (g i) (((𝒢 i).obj q.2).hom) hinner
  -- Then read the resulting displayed composite arrow back inside the small presentation `Dσ`.
  have hdisplay :
      Presieve.ofArrows
        (fun p : Σ i, σ i ↦ Y p.1 p.2)
        (fun p ↦ g p.1 p.2 ≫ f p.1)
        ((((𝒢 i).obj q.2).hom) ≫ f i) := by
    refine Presieve.ofArrows.mk' ⟨i, j⟩ hjleft.symm ?_
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ f i) hjhom
  have hmemD :
      Dσ.toPresieve ((((𝒢 i).obj q.2).hom) ≫ f i) :=
    hDσPres.ge _ _ hdisplay
  obtain ⟨r, hrleft, hrhom⟩ := Presieve.ofArrows_surj
    (fun r : Dσ.index ↦ (Dσ.obj r).hom)
    ((((𝒢 i).obj q.2).hom) ≫ f i)
    hmemD
  -- The two chosen generators have the same displayed composite arrow, hence are isomorphic in
  -- the slice over `S`.
  exact ⟨r, ⟨over_iso_of_left_eq_hom
    (A :=
      (ofArrows
        (fun p : Σ u : κ, (𝒢 (outer u)).index ↦ ((𝒢 (outer p.1)).obj p.2).left)
        (fun p ↦ ((𝒢 (outer p.1)).obj p.2).hom ≫ f (outer p.1))).obj q)
    (B := Dσ.obj r)
    hrleft
    hrhom⟩⟩

/-- Helper for Remark 7.48.4: once the reverse displayed-component transport is available, a small
presentation of the literal displayed composite family is tautologically equivalent to `𝒢σ`. -/
theorem composite_small_presentation_tautologically_equivalent
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {σ : ι → Type w'} {Y : ∀ i, σ i → C}
    (g : ∀ i j, Y i j ⟶ X i)
    {κ : Type (max u v)} (outer : κ → ι)
    {𝒢 : ∀ i, CoverFamily (X i)}
    (h𝒢 : ∀ i, Presieve.ofArrows (Y i) (g i) = (𝒢 i).toPresieve)
    {𝒢σ Dσ : CoverFamily S}
    (h𝒢σ :
      𝒢σ =
        ofArrows
          (fun p : Σ u : κ, (𝒢 (outer u)).index ↦ ((𝒢 (outer p.1)).obj p.2).left)
          (fun p ↦ ((𝒢 (outer p.1)).obj p.2).hom ≫ f (outer p.1)))
    (hDσPres :
      Dσ.toPresieve =
        Presieve.ofArrows
          (fun p : Σ i, σ i ↦ Y p.1 p.2)
          (fun p ↦ g p.1 p.2 ≫ f p.1))
    (hback :
      ∀ p : Σ i, σ i,
        ∃ q : 𝒢σ.index, Nonempty (Over.mk (g p.1 p.2 ≫ f p.1) ≅ 𝒢σ.obj q)) :
    TautologicallyEquivalent 𝒢σ Dσ := by
  classical
  -- The forward direction uses only the two chosen small presentations of the same displayed
  -- composite presieve.
  have hforward :
      ∀ q : 𝒢σ.index, ∃ r : Dσ.index, Nonempty (𝒢σ.obj q ≅ Dσ.obj r) :=
    composite_forward_small_presentation_iso
      (f := f)
      (g := g)
      (outer := outer)
      h𝒢
      h𝒢σ
      hDσPres
  let χ : 𝒢σ ⟶ Dσ :=
    { α := fun q ↦ Classical.choose (hforward q)
      f := fun q ↦ (Classical.choice (Classical.choose_spec (hforward q))).hom }
  have hχ : ∀ q : 𝒢σ.index, IsIso (χ.f q) := by
    intro q
    -- Each forward component is the hom of the chosen slice isomorphism into `Dσ`.
    dsimp [χ]
    infer_instance
  let δ : Dσ ⟶ 𝒢σ :=
    { α := fun r ↦
        let hmem :
            Presieve.ofArrows
              (fun p : Σ i, σ i ↦ Y p.1 p.2)
              (fun p ↦ g p.1 p.2 ≫ f p.1)
              ((Dσ.obj r).hom) :=
          hDσPres.le _ _ (Presieve.ofArrows.mk r)
        let p := Classical.choose <|
          Presieve.ofArrows_surj
            (fun p : Σ i, σ i ↦ g p.1 p.2 ≫ f p.1)
            ((Dσ.obj r).hom)
            hmem
        Classical.choose (hback p)
      f := fun r ↦
        let hmem :
            Presieve.ofArrows
              (fun p : Σ i, σ i ↦ Y p.1 p.2)
              (fun p ↦ g p.1 p.2 ≫ f p.1)
              ((Dσ.obj r).hom) :=
          hDσPres.le _ _ (Presieve.ofArrows.mk r)
        let p := Classical.choose <|
          Presieve.ofArrows_surj
            (fun p : Σ i, σ i ↦ g p.1 p.2 ≫ f p.1)
            ((Dσ.obj r).hom)
            hmem
        let hp := Classical.choose_spec <|
          Presieve.ofArrows_surj
            (fun p : Σ i, σ i ↦ g p.1 p.2 ≫ f p.1)
            ((Dσ.obj r).hom)
            hmem
        let hleft : Y p.1 p.2 = (Dσ.obj r).left := Classical.choose hp
        let hhom :
            (Dσ.obj r).hom = eqToHom hleft.symm ≫ (g p.1 p.2 ≫ f p.1) :=
          Classical.choose_spec hp
        let q := Classical.choose (hback p)
        let eback : Over.mk (g p.1 p.2 ≫ f p.1) ≅ 𝒢σ.obj q :=
          Classical.choice (Classical.choose_spec (hback p))
        ((over_iso_of_left_eq_hom
            (A := Dσ.obj r)
            (B := Over.mk (g p.1 p.2 ≫ f p.1))
            hleft
            hhom) ≪≫ eback).hom }
  have hδ : ∀ r : Dσ.index, IsIso (δ.f r) := by
    intro r
    -- Each backward component is the hom of the explicit displayed-generator comparison.
    dsimp [δ]
    infer_instance
  exact ⟨χ, δ, hχ, hδ⟩

/-- Helper for Remark 7.48.4: an isomorphism in a slice category stays an isomorphism after
postcomposing both arrows with a fixed map to a larger target. -/
noncomputable def postcompose_over_iso
    {X S : C} {A B : Over X}
    (e : A ≅ B) (f : X ⟶ S) :
    Over.mk (A.hom ≫ f) ≅ Over.mk (B.hom ≫ f) :=
  -- Keep the same underlying source-object isomorphism and whisker the triangle by `f`.
  Over.isoMk ((Over.forget X).mapIso e) (by
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ f) (Over.w e.hom))

/-- Helper for Remark 7.48.4: if a family is tautologically equivalent to another one, then any
object already identified with a component of the first family also identifies with a component of
the second family. -/
theorem exists_component_iso_of_tautologicallyEquivalent
    {S : C} {𝒜 ℬ : CoverFamily S} {A : Over S}
    (h𝒜ℬ : TautologicallyEquivalent 𝒜 ℬ)
    (hA : ∃ q : 𝒜.index, Nonempty (A ≅ 𝒜.obj q)) :
    ∃ r : ℬ.index, Nonempty (A ≅ ℬ.obj r) := by
  rcases h𝒜ℬ with ⟨χ, δ, hχ, hδ⟩
  rcases hA with ⟨q, ⟨e⟩⟩
  -- Compose the chosen component isomorphism with the forward component of the family morphism.
  haveI : IsIso (χ.f q) := hχ q
  exact ⟨χ.α q, ⟨e ≪≫ asIso (χ.f q)⟩⟩

/-- Helper for Remark 7.48.4: an equality between a literal displayed family and a small
presentation provides an explicit slice isomorphism from each literal generator to a chosen small
generator. -/
theorem displayed_component_iso_of_toPresieve_eq
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {𝒻 : CoverFamily S}
    (hpres : Presieve.ofArrows X f = 𝒻.toPresieve)
    (i : ι) :
    ∃ k : 𝒻.index, Nonempty (Over.mk (f i) ≅ 𝒻.obj k) := by
  have hi : 𝒻.toPresieve (f i) := by
    -- Rewrite the literal generator membership along the chosen presieve equality.
    simpa [hpres] using (Presieve.ofArrows.mk i : Presieve.ofArrows X f (f i))
  obtain ⟨k, hkleft, hkhom⟩ := Presieve.ofArrows_surj
    (fun k : 𝒻.index ↦ (𝒻.obj k).hom)
    (f i)
    hi
  -- The chosen small generator has the same slice object as the literal generator.
  exact ⟨k, ⟨over_iso_of_left_eq_hom
    (A := Over.mk (f i))
    (B := 𝒻.obj k)
    hkleft
    hkhom⟩⟩

/-- Helper for Remark 7.48.4: every literal displayed composite generator appears in the auxiliary
sigma-family built directly from the chosen small inner presentations. -/
theorem literal_composite_component_iso
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {σ : ι → Type w'} {Y : ∀ i, σ i → C}
    (g : ∀ i j, Y i j ⟶ X i)
    {𝒢 : ∀ i, CoverFamily (X i)}
    (h𝒢 : ∀ i, Presieve.ofArrows (Y i) (g i) = (𝒢 i).toPresieve)
    {ℬσ : CoverFamily S}
    (hℬσPres :
      Presieve.ofArrows
          (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).left)
          (fun p ↦ ((𝒢 p.1).obj p.2).hom ≫ f p.1) =
        ℬσ.toPresieve) :
    ∀ p : Σ i, σ i,
      ∃ q : ℬσ.index, Nonempty (Over.mk (g p.1 p.2 ≫ f p.1) ≅ ℬσ.obj q) := by
  -- First smallify the literal inner generator inside the chosen family `𝒢 i`, then postcompose
  -- the resulting slice isomorphism by the displayed outer arrow `f i`.
  intro p
  obtain ⟨q, ⟨eq_inner⟩⟩ :=
    displayed_component_iso_of_toPresieve_eq
      (f := g p.1)
      (hpres := h𝒢 p.1)
      p.2
  obtain ⟨r, ⟨er⟩⟩ :=
    displayed_component_iso_of_toPresieve_eq
      (f := fun s : Σ i, (𝒢 i).index ↦ ((𝒢 s.1).obj s.2).hom ≫ f s.1)
      (hpres := hℬσPres)
      ⟨p.1, q⟩
  exact ⟨r, ⟨postcompose_over_iso eq_inner (f p.1) ≪≫ er⟩⟩

/-- Helper for Remark 7.48.4: replacing each literal inner family by a small presentation leaves
the displayed composite presieve unchanged. -/
theorem literal_small_sigma_combinatorially_equivalent
    {ι : Type w} {S : C} {X : ι → C} (f : ∀ i, X i ⟶ S)
    {σ : ι → Type w'} {Y : ∀ i, σ i → C}
    (g : ∀ i j, Y i j ⟶ X i)
    {𝒢 : ∀ i, CoverFamily (X i)}
    (h𝒢 : ∀ i, Presieve.ofArrows (Y i) (g i) = (𝒢 i).toPresieve) :
    Presieve.ofArrows
        (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).left)
        (fun p ↦ ((𝒢 p.1).obj p.2).hom ≫ f p.1) =
      Presieve.ofArrows
        (fun p : Σ i, σ i ↦ Y p.1 p.2)
        (fun p ↦ g p.1 p.2 ≫ f p.1) := by
  -- Replace inner generators fibrewise using the chosen presieve equalities `h𝒢 i`.
  apply le_antisymm
  · rw [Presieve.ofArrows_le_iff]
    intro p
    have hinner :
        Presieve.ofArrows (Y p.1) (g p.1) (((𝒢 p.1).obj p.2).hom) :=
      (h𝒢 p.1).ge _ _ (Presieve.ofArrows.mk p.2)
    obtain ⟨j, hjleft, hjhom⟩ := Presieve.ofArrows_surj
      (g p.1)
      (((𝒢 p.1).obj p.2).hom)
      hinner
    refine Presieve.ofArrows.mk' ⟨p.1, j⟩ hjleft.symm ?_
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ f p.1) hjhom
  · rw [Presieve.ofArrows_le_iff]
    intro p
    have hinner :
        (𝒢 p.1).toPresieve (g p.1 p.2) :=
      (h𝒢 p.1).le _ _ (Presieve.ofArrows.mk p.2)
    obtain ⟨q, hqleft, hqhom⟩ := Presieve.ofArrows_surj
      (fun q : (𝒢 p.1).index ↦ ((𝒢 p.1).obj q).hom)
      (g p.1 p.2)
      hinner
    refine Presieve.ofArrows.mk' ⟨p.1, q⟩ hqleft.symm ?_
    simpa [Category.assoc] using congrArg (fun k ↦ k ≫ f p.1) hqhom

/-- Helper for Remark 7.48.4: once the outer family has been replaced by a tautologically
equivalent `K`-cover and each inner displayed family has been replaced by an original `K`-cover,
the remaining structural step is to compare the resulting literal sigma-family with the displayed
composite family. -/
theorem comp_mem_tautologicalEnlargement_of_outer_tautological
    {K : Precoverage C} [K.HasIsos] [K.IsStableUnderComposition]
    {ι : Type w} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S)
    {𝒻 𝒰 : CoverFamily S}
    (h𝒰 : IsCovering K 𝒰)
    (h𝒰f : TautologicallyEquivalent 𝒰 𝒻)
    (h𝒻pres : 𝒻.toPresieve = Presieve.ofArrows X f)
    {σ : ι → Type w'} {Y : ∀ i, σ i → C}
    (g : ∀ i j, Y i j ⟶ X i)
    {𝒢 𝒲 : ∀ i, CoverFamily (X i)}
    (h𝒲 : ∀ i, IsCovering K (𝒲 i))
    (h𝒲𝒢 : ∀ i, TautologicallyEquivalent (𝒲 i) (𝒢 i))
    (h𝒢pres : ∀ i, (𝒢 i).toPresieve = Presieve.ofArrows (Y i) (g i)) :
    Presieve.ofArrows (fun p : Σ i, σ i ↦ Y p.1 p.2) (fun p ↦ g p.1 p.2 ≫ f p.1) ∈
      K.tautologicalEnlargement S := by
  rcases h𝒰f with ⟨φ, ψ, hφ, hψ⟩
  obtain ⟨α, β, eα, eβ⟩ := generator_isos_of_toPresieve_eq f h𝒻pres
  let 𝒲σ : CoverFamily S := displayedSigmaFamily (φ := φ) (f := f) (α := α) 𝒲
  have h𝒲σ : IsCovering K 𝒲σ := by
    -- First transport the original inner `K`-covers along the original outer `K`-cover.
    simpa [𝒲σ] using
      transported_sigma_family_is_covering
        (K := K)
        h𝒰
        φ
        hφ
        (f := f)
        (α := α)
        eα
        (𝒲 := 𝒲)
        h𝒲
  let 𝒢σ : CoverFamily S := displayedSigmaFamily (φ := φ) (f := f) (α := α) 𝒢
  have h𝒲σ𝒢σ : TautologicallyEquivalent 𝒲σ 𝒢σ := by
    -- Then replace each transported original inner family by the chosen displayed small family.
    simpa [𝒲σ, 𝒢σ] using
      transported_sigma_family_tautologically_equivalent
        (φ := φ)
        hφ
        (f := f)
        (α := α)
        eα
        (𝒲 := 𝒲)
        (𝒢 := 𝒢)
        h𝒲𝒢
  obtain ⟨κℬ, Zℬ, b, hℬeq⟩ :=
    (Presieve.ofArrows
      (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).left)
      (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).hom ≫ f p.1)).exists_eq_ofArrows
  let ℬσ : CoverFamily S := ofArrows Zℬ b
  have hℬσSmall :
      ℬσ.toPresieve =
        Presieve.ofArrows
          (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).left)
          (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).hom ≫ f p.1) := by
    -- This auxiliary small presentation is definitionally the literal sigma-family on `𝒢`.
    simpa [ℬσ] using hℬeq.symm
  have hℬσPres :
      ℬσ.toPresieve =
        Presieve.ofArrows
          (fun p : Σ i, σ i ↦ Y p.1 p.2)
          (fun p ↦ g p.1 p.2 ≫ f p.1) := by
    -- Replacing each literal inner family by the chosen small presentation does not change the
    -- displayed composite presieve.
    calc
      ℬσ.toPresieve =
          Presieve.ofArrows
            (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).left)
            (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).hom ≫ f p.1) := hℬσSmall
      _ =
          Presieve.ofArrows
            (fun p : Σ i, σ i ↦ Y p.1 p.2)
            (fun p ↦ g p.1 p.2 ≫ f p.1) :=
        literal_small_sigma_combinatorially_equivalent
          (f := f)
          (g := g)
          (𝒢 := 𝒢)
          (fun i ↦ (h𝒢pres i).symm)
  obtain ⟨κσ, Yσ, hσ, hDσEq⟩ :=
    (Presieve.ofArrows
      (fun p : Σ i, σ i ↦ Y p.1 p.2)
      (fun p ↦ g p.1 p.2 ≫ f p.1)).exists_eq_ofArrows
  let Dσ : CoverFamily S := ofArrows Yσ hσ
  have hDσPres :
      Dσ.toPresieve =
        Presieve.ofArrows
          (fun p : Σ i, σ i ↦ Y p.1 p.2)
          (fun p ↦ g p.1 p.2 ≫ f p.1) := by
    -- The chosen small presentation `Dσ` is definitionally the displayed composite presieve.
    simpa [Dσ] using hDσEq.symm
  have hℬσDσ : TautologicallyEquivalent ℬσ Dσ := by
    -- The two chosen small presentations define the same presieve, so they are tautologically
    -- equivalent by combinatorial equivalence.
    exact combinatoriallyEquivalent_implies_tautologicallyEquivalent (hℬσPres.trans hDσPres.symm)
  let 𝒲β : ∀ i, CoverFamily (𝒰.obj (ψ.α (β i))).left :=
    backwardTransportedInnerFamily (ψ := ψ) hψ (f := f) (β := β) eβ 𝒲
  have h𝒲β : ∀ i, IsCovering K (𝒲β i) := by
    intro i
    -- Route correction: duplicate displayed outer indices using the backward outer witness before
    -- trying to compare with the literal sigma-family.
    simpa [𝒲β] using
      backward_transported_inner_family_is_covering
        (K := K)
        (ψ := ψ)
        hψ
        (f := f)
        (β := β)
        eβ
        (𝒲 := 𝒲)
        h𝒲
        i
  let 𝒢β : ∀ i, CoverFamily (𝒰.obj (ψ.α (β i))).left :=
    backwardTransportedInnerFamily (ψ := ψ) hψ (f := f) (β := β) eβ 𝒢
  have h𝒲β𝒢β : ∀ i, TautologicallyEquivalent (𝒲β i) (𝒢β i) := by
    intro i
    -- The backward-transported original and displayed fibre families remain tautologically
    -- equivalent over the same original outer component.
    simpa [𝒲β, 𝒢β] using
      backward_transported_inner_family_tautologicallyEquivalent
        (ψ := ψ)
        hψ
        (f := f)
        (β := β)
        eβ
        (𝒲 := 𝒲)
        (𝒢 := 𝒢)
        h𝒲𝒢
        i
  have h𝒲t : ∀ u, IsCovering K (transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒲 u) := by
    intro u
    -- The filler branches use the forward transport along `φ`.
    exact transported_inner_family_is_covering
      (K := K)
      (φ := φ)
      hφ
      (f := f)
      (α := α)
      eα
      (𝒲 := 𝒲)
      h𝒲
      u
  have h𝒲t𝒢t :
      ∀ u,
        TautologicallyEquivalent
          (transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒲 u)
          (transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒢 u) := by
    intro u
    -- The same forward transport preserves the chosen fibrewise tautological equivalences.
    exact transported_inner_family_tautologicallyEquivalent
      (φ := φ)
      hφ
      (f := f)
      (α := α)
      eα
      (𝒲 := 𝒲)
      (𝒢 := 𝒢)
      h𝒲𝒢
      u
  let Dup := Sum (ULift.{max u v} ι) 𝒰.index
  let Xdup : Dup → C := fun
    | Sum.inl i => (𝒰.obj (ψ.α (β i.down))).left
    | Sum.inr u => (𝒰.obj u).left
  let fdup : ∀ s : Dup, Xdup s ⟶ S := fun
    | Sum.inl i => (𝒰.obj (ψ.α (β i.down))).hom
    | Sum.inr u => (𝒰.obj u).hom
  have h𝒰dup : Presieve.ofArrows Xdup fdup ∈ K S := by
    -- Route correction: duplicate the outer branches globally, with one filler branch `Sum.inr u`
    -- for each original outer generator, so surjective reindexing reduces the cover back to `𝒰`.
    have hpres :
        Presieve.ofArrows Xdup fdup = 𝒰.toPresieve := by
      apply le_antisymm
      · rw [Presieve.ofArrows_le_iff]
        intro s
        cases s with
        | inl i =>
            simpa [Xdup, fdup] using
              (Presieve.ofArrows.mk (ψ.α (β i.down)) :
                𝒰.toPresieve ((𝒰.obj (ψ.α (β i.down))).hom))
        | inr u =>
            simpa [Xdup, fdup] using
              (Presieve.ofArrows.mk u : 𝒰.toPresieve ((𝒰.obj u).hom))
      · intro Z g hg
        obtain ⟨u, hleft, hhom⟩ := Presieve.ofArrows_surj
          (fun u : 𝒰.index ↦ (𝒰.obj u).hom)
          g
          hg
        refine Presieve.ofArrows.mk' (Sum.inr u) hleft.symm ?_
        simpa [Xdup, fdup] using hhom
    rw [hpres]
    simpa [IsCovering] using h𝒰
  let 𝒲dup : ∀ s : Dup, CoverFamily (Xdup s) :=
    fun
      | Sum.inl i => 𝒲β i.down
      | Sum.inr u => transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒲 u
  let 𝒢dup : ∀ s : Dup, CoverFamily (Xdup s) :=
    fun
      | Sum.inl i => 𝒢β i.down
      | Sum.inr u => transportedInnerFamily (φ := φ) hφ (f := f) (α := α) eα 𝒢 u
  have h𝒲dup : ∀ s, IsCovering K (𝒲dup s) := by
    intro s
    -- Each duplicated branch carries either a backward-transported cover or a forward filler cover.
    cases s with
    | inl i =>
        simpa [𝒲dup] using h𝒲β i.down
    | inr u =>
        simpa [𝒲dup] using h𝒲t u
  have h𝒲dup𝒢dup : ∀ s, TautologicallyEquivalent (𝒲dup s) (𝒢dup s) := by
    intro s
    -- The branchwise comparison follows the same `Sum` split as the branchwise covering witness.
    cases s with
    | inl i =>
        simpa [𝒲dup, 𝒢dup] using h𝒲β𝒢β i.down
    | inr u =>
        simpa [𝒲dup, 𝒢dup] using h𝒲t𝒢t u
  let WdupLarge :=
    ofArrows
      (fun p : Σ s, (𝒲dup s).index ↦ ((𝒲dup p.1).obj p.2).left)
      (fun p ↦ ((𝒲dup p.1).obj p.2).hom ≫ fdup p.1)
  have hWdupLarge : WdupLarge.toPresieve ∈ K S := by
    -- Apply the original composition axiom once to the duplicated outer cover.
    simpa [WdupLarge, Xdup, fdup] using
      (Precoverage.comp_mem_coverings
        (J := K)
        (f := fdup)
        h𝒰dup
        (g := fun s j ↦ ((𝒲dup s).obj j).hom)
        (fun s ↦ by simpa [IsCovering] using h𝒲dup s))
  obtain ⟨κWdup, YWdup, wdup, hWdupEq⟩ := WdupLarge.toPresieve.exists_eq_ofArrows
  let Wdupσ : CoverFamily S := ofArrows YWdup wdup
  have hWdupσPres : Wdupσ.toPresieve = WdupLarge.toPresieve := by
    -- Smallify the duplicated original composite presieve before using it in the enlargement API.
    simpa [Wdupσ] using hWdupEq.symm
  have hWdupσPres' :
      Wdupσ.toPresieve =
        Presieve.ofArrows
          (fun p : Σ s, (𝒲dup s).index ↦ ((𝒲dup p.1).obj p.2).left)
          (fun p ↦ ((𝒲dup p.1).obj p.2).hom ≫ fdup p.1) := by
    -- Record the smallified duplicated original family against the literal sigma presentation.
    simpa [WdupLarge] using hWdupσPres
  have hWdupσ : IsCovering K Wdupσ := by
    -- Transport the genuine covering result for the large duplicated presieve across smallification.
    rw [IsCovering, hWdupσPres]
    exact hWdupLarge
  let GdupLarge :=
    ofArrows
      (fun p : Σ s, (𝒢dup s).index ↦ ((𝒢dup p.1).obj p.2).left)
      (fun p ↦ ((𝒢dup p.1).obj p.2).hom ≫ fdup p.1)
  obtain ⟨κGdup, YGdup, gdup, hGdupEq⟩ := GdupLarge.toPresieve.exists_eq_ofArrows
  let Gdupσ : CoverFamily S := ofArrows YGdup gdup
  have hGdupσPres : Gdupσ.toPresieve = GdupLarge.toPresieve := by
    -- Smallify the duplicated displayed composite presieve for the later tautological comparison.
    simpa [Gdupσ] using hGdupEq.symm
  have hGdupσPres' :
      Gdupσ.toPresieve =
        Presieve.ofArrows
          (fun p : Σ s, (𝒢dup s).index ↦ ((𝒢dup p.1).obj p.2).left)
          (fun p ↦ ((𝒢dup p.1).obj p.2).hom ≫ fdup p.1) := by
    -- Record the smallified duplicated displayed family against its literal sigma presentation.
    simpa [GdupLarge] using hGdupσPres
  have hWdupLargeGdupLarge : TautologicallyEquivalent WdupLarge GdupLarge := by
    -- Replace the duplicated original inner covers branchwise by the duplicated displayed ones.
    simpa [WdupLarge, GdupLarge, Xdup, fdup] using
      sigma_postcompose_tautologically_equivalent
        (f := fdup)
        h𝒲dup𝒢dup
  have hWdupσGdupσ : TautologicallyEquivalent Wdupσ Gdupσ := by
    classical
    obtain ⟨αW, βW, eαW, eβW⟩ :=
      generator_isos_of_toPresieve_eq
        (f := fun p : Σ s, (𝒲dup s).index ↦ ((𝒲dup p.1).obj p.2).hom ≫ fdup p.1)
        (𝒻 := Wdupσ)
        hWdupσPres'
    obtain ⟨αG, βG, eαG, eβG⟩ :=
      generator_isos_of_toPresieve_eq
        (f := fun p : Σ s, (𝒢dup s).index ↦ ((𝒢dup p.1).obj p.2).hom ≫ fdup p.1)
        (𝒻 := Gdupσ)
        hGdupσPres'
    rcases hWdupLargeGdupLarge with ⟨χLarge, δLarge, hχLarge, hδLarge⟩
    let χIso :
        ∀ k : Wdupσ.index,
          WdupLarge.obj (αW k) ≅ GdupLarge.obj (χLarge.α (αW k)) := fun k ↦ by
            letI : IsIso (χLarge.f (αW k)) := hχLarge (αW k)
            exact asIso (χLarge.f (αW k))
    let δIso :
        ∀ k : Gdupσ.index,
          GdupLarge.obj (αG k) ≅ WdupLarge.obj (δLarge.α (αG k)) := fun k ↦ by
            letI : IsIso (δLarge.f (αG k)) := hδLarge (αG k)
            exact asIso (δLarge.f (αG k))
    let χα : Wdupσ.index → Gdupσ.index := fun k ↦ βG (χLarge.α (αW k))
    let χf : ∀ k : Wdupσ.index, Wdupσ.obj k ⟶ Gdupσ.obj (χα k) := fun k ↦
      ((show Wdupσ.obj k ≅ WdupLarge.obj (αW k) from eαW k) ≪≫
        χIso k ≪≫
        (show GdupLarge.obj (χLarge.α (αW k)) ≅ Gdupσ.obj (βG (χLarge.α (αW k))) from
          eβG (χLarge.α (αW k)))).hom
    let δα : Gdupσ.index → Wdupσ.index := fun k ↦ βW (δLarge.α (αG k))
    let δf : ∀ k : Gdupσ.index, Gdupσ.obj k ⟶ Wdupσ.obj (δα k) := fun k ↦
      ((show Gdupσ.obj k ≅ GdupLarge.obj (αG k) from eαG k) ≪≫
        δIso k ≪≫
        (show WdupLarge.obj (δLarge.α (αG k)) ≅ Wdupσ.obj (βW (δLarge.α (αG k))) from
          eβW (δLarge.α (αG k)))).hom
    let χ : Wdupσ ⟶ Gdupσ := { α := χα, f := χf }
    let δ : Gdupσ ⟶ Wdupσ := { α := δα, f := δf }
    refine ⟨χ, δ, ?_, ?_⟩
    · intro k
      -- Each forward component is the hom of the chosen slice isomorphism into `Gdupσ`.
      dsimp [χ, χf]
      infer_instance
    · intro k
      -- Each backward component is the hom of the chosen slice isomorphism into `Wdupσ`.
      dsimp [δ, δf]
      infer_instance
  let ℒLarge :=
    ofArrows
      (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).left)
      (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).hom ≫ f p.1)
  have hGdupLargeℒLarge :
      CombinatoriallyEquivalent GdupLarge ℒLarge := by
    -- Compare the duplicated displayed composite with the literal sigma-family by splitting into
    -- backward branches `Sum.inl i` and forward filler branches `Sum.inr u`.
    refine (combinatoriallyEquivalent_iff_exists_reindexings).2 ?_
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro ⟨s, j⟩
      cases s with
      | inl i =>
          exact ⟨i.down, j⟩
      | inr u =>
          exact ⟨α (φ.α u), j⟩
    · rintro ⟨i, j⟩
      exact ⟨Sum.inl (ULift.up i), j⟩
    · rintro ⟨s, j⟩
      cases s with
      | inl i =>
          change
            Over.mk
                ((((𝒢dup (Sum.inl i)).obj j).hom) ≫ fdup (Sum.inl i)) =
              Over.mk ((((𝒢 i.down).obj j).hom) ≫ f i.down)
          dsimp [GdupLarge, ℒLarge, ofArrows, 𝒢dup, Xdup, fdup, 𝒢β, backwardTransportedInnerFamily,
            outer_backward_component_iso]
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ Over.mk ((((𝒢 i.down).obj j).hom) ≫ k))
              (outer_backward_transport_hom
                (ψ := ψ)
                (f := f)
                (β := β)
                eβ
                i.down)
      | inr u =>
          change
            Over.mk
                ((((𝒢dup (Sum.inr u)).obj j).hom) ≫ fdup (Sum.inr u)) =
              Over.mk ((((𝒢 (α (φ.α u))).obj j).hom) ≫ f (α (φ.α u)))
          dsimp [GdupLarge, ℒLarge, ofArrows, 𝒢dup, Xdup, fdup, transportedInnerFamily,
            outer_generator_iso]
          simpa [Category.assoc] using
            congrArg
              (fun k ↦ Over.mk ((((𝒢 (α (φ.α u))).obj j).hom) ≫ k))
              (outer_generator_expanded_inv_left_hom
                (φ := φ)
                hφ
                (f := f)
                (α := α)
                eα
                u)
    · rintro ⟨i, j⟩
      change
        Over.mk ((((𝒢 i).obj j).hom) ≫ f i) =
          Over.mk
            ((((𝒢dup (Sum.inl (ULift.up i))).obj j).hom) ≫ fdup (Sum.inl (ULift.up i)))
      dsimp [GdupLarge, ℒLarge, ofArrows, 𝒢dup, Xdup, fdup, 𝒢β, backwardTransportedInnerFamily,
        outer_backward_component_iso]
      simpa [Category.assoc] using
        congrArg
          (fun k ↦ Over.mk ((((𝒢 i).obj j).hom) ≫ k))
          (outer_backward_transport_hom
            (ψ := ψ)
            (f := f)
            (β := β)
            eβ
            i).symm
  have hℬσPres' :
      ℬσ.toPresieve =
        Presieve.ofArrows
          (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).left)
          (fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).hom ≫ f p.1) := by
    -- Record the chosen small presentation `ℬσ` against the literal sigma-family on `𝒢`.
    simpa [ℒLarge] using hℬσSmall
  have hGdupσℬσ : TautologicallyEquivalent Gdupσ ℬσ := by
    classical
    obtain ⟨αG, βG, eαG, eβG⟩ :=
      generator_isos_of_toPresieve_eq
        (f := fun p : Σ s, (𝒢dup s).index ↦ ((𝒢dup p.1).obj p.2).hom ≫ fdup p.1)
        (𝒻 := Gdupσ)
        hGdupσPres'
    obtain ⟨αB, βB, eαB, eβB⟩ :=
      generator_isos_of_toPresieve_eq
        (f := fun p : Σ i, (𝒢 i).index ↦ ((𝒢 p.1).obj p.2).hom ≫ f p.1)
        (𝒻 := ℬσ)
        hℬσPres'
    obtain ⟨αL, βL, hαL, hβL⟩ :=
      (combinatoriallyEquivalent_iff_exists_reindexings
        (𝒰 := GdupLarge)
        (𝒱 := ℒLarge)).1 hGdupLargeℒLarge
    let χα : Gdupσ.index → ℬσ.index := fun k ↦ βB (αL (αG k))
    let χf : ∀ k : Gdupσ.index, Gdupσ.obj k ⟶ ℬσ.obj (χα k) := fun k ↦
      ((show Gdupσ.obj k ≅ GdupLarge.obj (αG k) from eαG k) ≪≫
        eqToIso (hαL (αG k)) ≪≫
        (show ℒLarge.obj (αL (αG k)) ≅ ℬσ.obj (βB (αL (αG k))) from
          eβB (αL (αG k)))).hom
    let δα : ℬσ.index → Gdupσ.index := fun k ↦ βG (βL (αB k))
    let δf : ∀ k : ℬσ.index, ℬσ.obj k ⟶ Gdupσ.obj (δα k) := fun k ↦
      ((show ℬσ.obj k ≅ ℒLarge.obj (αB k) from eαB k) ≪≫
        eqToIso (hβL (αB k)) ≪≫
        (show GdupLarge.obj (βL (αB k)) ≅ Gdupσ.obj (βG (βL (αB k))) from
          eβG (βL (αB k)))).hom
    let χ : Gdupσ ⟶ ℬσ := { α := χα, f := χf }
    let δ : ℬσ ⟶ Gdupσ := { α := δα, f := δf }
    refine ⟨χ, δ, ?_, ?_⟩
    · intro k
      -- Each forward component is the hom of the chosen comparison into the small presentation `ℬσ`.
      dsimp [χ, χf]
      infer_instance
    · intro k
      -- Each backward component is the hom of the chosen comparison back into `Gdupσ`.
      dsimp [δ, δf]
      infer_instance
  have hWdupσDσ : TautologicallyEquivalent Wdupσ Dσ := by
    -- Chain the duplicated-cover comparison through the chosen small presentations `ℬσ` and `Dσ`.
    exact tautologicallyEquivalent_trans
      hWdupσGdupσ
      (tautologicallyEquivalent_trans
        hGdupσℬσ
        hℬσDσ)
  have hDσ : IsCovering K.tautologicalEnlargement Dσ := by
    -- Package the genuine `K`-cover witness `Wdupσ` together with the explicit tautological
    -- equivalence to the chosen small presentation `Dσ`.
    exact (isCovering_tautologicalEnlargement_iff (K := K) (𝒱 := Dσ)).2
      ⟨Wdupσ, hWdupσ, hWdupσDσ⟩
  -- Replace the chosen small presentation `Dσ` by the literal displayed composite presieve.
  simpa [Dσ, IsCovering] using (hDσPres ▸ hDσ)

/-- Remark 7.48.4 (2'): the tautological enlargement is stable under indexed composition of
covering families whenever the original precoverage is stable under composition and contains
isomorphism coverings. This is the modified axiom (2') from the source text: if `(T, U)` is a
covering and each fibre family `(T_f, U')` is covering, then the displayed composite family is
covering. -/
theorem comp_mem_tautologicalEnlargement
    {K : Precoverage C} [K.HasIsos] [K.IsStableUnderComposition]
    {ι : Type w} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ K.tautologicalEnlargement S)
    {σ : ι → Type w'} {Y : ∀ i, σ i → C}
    (g : ∀ i j, Y i j ⟶ X i)
    (hg : ∀ i, Presieve.ofArrows (Y i) (g i) ∈ K.tautologicalEnlargement (X i)) :
    Presieve.ofArrows (fun p : Σ i, σ i ↦ Y p.1 p.2) (fun p ↦ g p.1 p.2 ≫ f p.1) ∈
      K.tautologicalEnlargement S := by
  obtain ⟨κ, X', f', h𝒻eq⟩ := (Presieve.ofArrows X f).exists_eq_ofArrows
  let 𝒻 : CoverFamily S := ofArrows X' f'
  have hf' : IsCovering K.tautologicalEnlargement 𝒻 := by
    -- Repackage the displayed outer presieve as a canonical small family before unpacking it.
    simpa [𝒻, IsCovering] using (h𝒻eq ▸ hf)
  rcases (isCovering_tautologicalEnlargement_iff (K := K)
      (𝒱 := 𝒻)).mp hf' with ⟨𝒰, h𝒰, h𝒰f⟩
  have h𝒻pres : 𝒻.toPresieve = Presieve.ofArrows X f := by
    -- The chosen small presentation `𝒻` is definitionally the displayed outer family.
    simpa [𝒻] using h𝒻eq.symm
  choose κg Xg gg h𝒢eq using
    fun i : ι ↦ (Presieve.ofArrows (Y i) (g i)).exists_eq_ofArrows
  let 𝒢 : ∀ i, CoverFamily (X i) := fun i ↦ ofArrows (Xg i) (gg i)
  have hg' : ∀ i, IsCovering K.tautologicalEnlargement (𝒢 i) := by
    intro i
    -- Repackage each displayed inner presieve as a canonical small family before unpacking it.
    simpa [𝒢, IsCovering] using (h𝒢eq i ▸ hg i)
  choose 𝒲 h𝒲 h𝒲𝒢 using
    fun i : ι ↦
      (isCovering_tautologicalEnlargement_iff (K := K)
        (𝒱 := 𝒢 i)).mp (hg' i)
  have h𝒢pres : ∀ i, (𝒢 i).toPresieve = Presieve.ofArrows (Y i) (g i) := by
    intro i
    -- Each chosen small inner presentation is definitionally the displayed inner presieve.
    simpa [𝒢] using (h𝒢eq i).symm
  -- Route correction: after unpacking the outer and inner enlargement witnesses, the theorem is
  -- reduced to the single structural comparison encoded in the helper below.
  exact comp_mem_tautologicalEnlargement_of_outer_tautological
    (K := K)
    (f := f)
    h𝒰
    h𝒰f
    h𝒻pres
    (g := g)
    h𝒲
    h𝒲𝒢
    h𝒢pres

instance instIsStableUnderComposition_tautologicalEnlargement
    (K : Precoverage C) [K.HasIsos] [K.IsStableUnderComposition] :
    K.tautologicalEnlargement.IsStableUnderComposition where
  comp_mem_coverings := comp_mem_tautologicalEnlargement

/-- Remark 7.48.4 (3'): the tautological enlargement is stable under chosen pullback/base-change
families whenever the original site is and has isomorphism coverings. -/
theorem mem_tautologicalEnlargement_of_isPullback
    {K : Precoverage C} [K.HasIsos] [K.IsStableUnderBaseChange]
    {ι : Type w} {S : C} {X : ι → C}
    (f : ∀ i, X i ⟶ S) (hf : Presieve.ofArrows X f ∈ K.tautologicalEnlargement S)
    {Y : C} (g : Y ⟶ S)
    {P : ι → C} (p₁ : ∀ i, P i ⟶ Y) (p₂ : ∀ i, P i ⟶ X i)
    (h : ∀ i, IsPullback (p₁ i) (p₂ i) g (f i)) :
    Presieve.ofArrows P p₁ ∈ K.tautologicalEnlargement Y := by
  -- Route correction: the missing step is not the base-change axiom itself, but the family-level
  -- comparison between the transported original pullback family and the displayed pullback family.
  obtain ⟨κ, X', f', h𝒻eq⟩ := (Presieve.ofArrows X f).exists_eq_ofArrows
  let 𝒻 : CoverFamily S := ofArrows X' f'
  have hf' : IsCovering K.tautologicalEnlargement 𝒻 := by
    -- Repackage the displayed outer presieve as a canonical small family before unpacking it.
    simpa [𝒻, IsCovering] using (h𝒻eq ▸ hf)
  rcases (isCovering_tautologicalEnlargement_iff (K := K)
      (𝒱 := 𝒻)).mp hf' with ⟨𝒰, h𝒰, h𝒰f⟩
  rcases h𝒰f with ⟨φ, ψ, hφ, hψ⟩
  have h𝒻pres : 𝒻.toPresieve = Presieve.ofArrows X f := by
    -- The chosen small presentation `𝒻` is definitionally the same presieve as the displayed one.
    simpa [𝒻] using h𝒻eq.symm
  obtain ⟨α, β, eα, eβ⟩ := generator_isos_of_toPresieve_eq f h𝒻pres
  let 𝒫u : CoverFamily Y :=
    ofArrows
      (fun u ↦ P (α (φ.α u)))
      (fun u ↦ p₁ (α (φ.α u)))
  have h𝒫u : IsCovering K 𝒫u := by
    -- Route correction: apply base change only after rewriting the displayed pullback squares
    -- along the original outer generators, so the original axiom closes the structural part.
    simpa [𝒫u] using
      transported_pullback_family_is_covering
        (K := K)
        h𝒰
        φ
        hφ
        (f := f)
        (α := α)
        eα
        g
        p₁
        p₂
        h
  obtain ⟨κp, P', p₁', hDpEq⟩ := (Presieve.ofArrows P p₁).exists_eq_ofArrows
  let Dp : CoverFamily Y := ofArrows P' p₁'
  have hDpPres : Dp.toPresieve = Presieve.ofArrows P p₁ := by
    -- The chosen small presentation `Dp` is definitionally the displayed pullback presieve.
    simpa [Dp] using hDpEq.symm
  classical
  let χ : 𝒫u ⟶ Dp :=
    { α := fun u ↦
        Classical.choose <|
          Presieve.ofArrows_surj p₁'
            (p₁ (α (φ.α u)))
            (hDpPres.ge _ _ (Presieve.ofArrows.mk (α (φ.α u))))
      f := fun u ↦
        let q :=
          Classical.choose <|
            Presieve.ofArrows_surj p₁'
              (p₁ (α (φ.α u)))
              (hDpPres.ge _ _ (Presieve.ofArrows.mk (α (φ.α u))))
        let hq :=
          Classical.choose_spec <|
            Presieve.ofArrows_surj p₁'
              (p₁ (α (φ.α u)))
              (hDpPres.ge _ _ (Presieve.ofArrows.mk (α (φ.α u))))
        let hleft : P' q = P (α (φ.α u)) := Classical.choose hq
        let hhom : p₁ (α (φ.α u)) = eqToHom hleft.symm ≫ p₁' q := Classical.choose_spec hq
        (over_iso_of_left_eq_hom
          (A := 𝒫u.obj u)
          (B := Dp.obj q)
          hleft
          hhom).hom }
  have hχ : ∀ u : 𝒫u.index, IsIso (χ.f u) := by
    intro u
    -- Each forward component is the hom of the chosen slice isomorphism into `Dp`.
    dsimp [χ]
    infer_instance
  let δ : Dp ⟶ 𝒫u :=
    { α := fun q ↦
        let hmem : Presieve.ofArrows P p₁ ((Dp.obj q).hom) := hDpPres.le _ _ (Presieve.ofArrows.mk q)
        let i := Classical.choose <| Presieve.ofArrows_surj p₁ ((Dp.obj q).hom) hmem
        ψ.α (β i)
      f := fun q ↦
        let hmem : Presieve.ofArrows P p₁ ((Dp.obj q).hom) := hDpPres.le _ _ (Presieve.ofArrows.mk q)
        let i := Classical.choose <| Presieve.ofArrows_surj p₁ ((Dp.obj q).hom) hmem
        let hi := Classical.choose_spec <| Presieve.ofArrows_surj p₁ ((Dp.obj q).hom) hmem
        let hleft : P i = (Dp.obj q).left := Classical.choose hi
        let hhom : (Dp.obj q).hom = eqToHom hleft.symm ≫ p₁ i := Classical.choose_spec hi
        let u : 𝒫u.index := ψ.α (β i)
        let eback : Over.mk (f i) ≅ 𝒰.obj u :=
          eβ i ≪≫ @asIso _ _ _ _ (ψ.f (β i)) (hψ (β i))
        let hback_i :
            IsPullback
              (p₁ i)
              (p₂ i ≫ eback.hom.left)
              g
              (𝒰.obj u).hom := by
          -- Transport the displayed pullback square to the original outer generator indexed by `u`.
          simpa [u, eback] using isPullback_comp_inv_left_of_iso (h i) eback.symm
        let hback_u :
            IsPullback
              (p₁ (α (φ.α u)))
              (p₂ (α (φ.α u)) ≫
                (outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u).inv.left)
              g
              (𝒰.obj u).hom := by
          -- The transported original pullback family uses the same cospan over `𝒰.obj u`.
          simpa [u] using
            isPullback_comp_inv_left_of_iso
              (h (α (φ.α u)))
              (outer_generator_iso (φ := φ) hφ (f := f) (α := α) eα u)
        let epb : Over.mk (p₁ i) ≅ 𝒫u.obj u :=
          Over.isoMk
            (hback_i.isoIsPullback _ _ hback_u)
            (by
              -- The pullback comparison isomorphism preserves the left leg by uniqueness.
              change (hback_i.isoIsPullback _ _ hback_u).hom ≫ p₁ (α (φ.α u)) = p₁ i
              simp)
        ((over_iso_of_left_eq_hom
            (A := Dp.obj q)
            (B := Over.mk (p₁ i))
            hleft
            hhom) ≪≫ epb).hom }
  have hδ : ∀ q : Dp.index, IsIso (δ.f q) := by
    intro q
    -- Each backward component is the hom of the explicit pullback comparison isomorphism.
    dsimp [δ]
    infer_instance
  have h𝒫uDp : TautologicallyEquivalent 𝒫u Dp := by
    -- The displayed pullback family and the transported original family differ only by the chosen
    -- smallification and by canonical pullback-object isomorphisms.
    exact ⟨χ, δ, hχ, hδ⟩
  have hDp : IsCovering K.tautologicalEnlargement Dp := by
    -- Package the original `K`-cover `𝒫u` together with the explicit tautological equivalence.
    exact (isCovering_tautologicalEnlargement_iff (K := K) (𝒱 := Dp)).2 ⟨𝒫u, h𝒫u, h𝒫uDp⟩
  -- Replace the chosen small presentation `Dp` by the literal displayed pullback presieve.
  simpa [Dp, IsCovering] using (hDpPres ▸ hDp)

instance instIsStableUnderBaseChange_tautologicalEnlargement
    (K : Precoverage C) [K.HasIsos] [K.IsStableUnderBaseChange] :
    K.tautologicalEnlargement.IsStableUnderBaseChange where
  mem_coverings_of_isPullback := mem_tautologicalEnlargement_of_isPullback

end Precoverage

namespace Coverage

open Precoverage

/-- The tautological enlargement of a site defines the same Grothendieck topology as the original
coverage. This formalizes the remark's claim that the modified covering notion makes no difference
to the associated topology. -/
theorem tautologicalEnlargement_toGrothendieck (K : Coverage C) :
    (tautologicalEnlargement K.toPrecoverage).toGrothendieck = K.toGrothendieck := by
  exact toGrothendieck_eq_of_tautological_enlargement
    (le_tautologicalEnlargement K.toPrecoverage) fun _ _ h𝒱 ↦
      isCovering_tautologicalEnlargement_iff.mp h𝒱

end Coverage
end CategoryTheory
