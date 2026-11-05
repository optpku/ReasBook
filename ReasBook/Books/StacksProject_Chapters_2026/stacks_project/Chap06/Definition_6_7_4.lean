module

public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.LocalPredicate
public import stacks_project.Chap06.Definition_6_3_2
import Mathlib.Tactic.Recall
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace TopologicalSpace.Opens Topology
open scoped TopCat AlgebraicGeometry

universe u v

attribute [local instance] Types.instFunLike Types.instConcreteCategory

section

variable (X : TopCat.{u})

/- Domain-style sampling for Definition 6.7.4:
- primary domain: set-valued sheaves on a topological space, comparing the source-facing locally
  constant model with the canonical constant sheaf;
- sampled owner abstractions:
  `CategoryTheory.constantSheaf`,
  `A ₚ X`,
  `TopCat.LocalPredicate`,
  `TopCat.subpresheafToTypes`,
  `TopCat.subsheafToTypes`;
- source/core/bridge triage:
  `source-facing`: `locallyConstantPresheaf`, `locallyConstantSheaf`;
  `core/canonical`: `TopCat.subsheafToTypes` for the sheaf of locally constant functions, and
    `CategoryTheory.constantSheaf` for the constant-object comparison;
  `bridge/view`: `constantSheafToLocallyConstantSheaf` and the theorem-level `IsIso` results for
  it and its section maps;
- primitive data: the only genuine data are the local predicate `IsLocallyConstant` on ordinary
  `A`-valued sections, together with the chapter-owner constant presheaf `A ₚ X`;
- derived API: both the presheaf and the sheaf come from the local-predicate owner, while the
  comparison with `constantSheaf` is the bridge built by sheafification and proved invertible
  afterward.
-/

public def locallyConstantPredicate (A : Type (max u v)) : LocalPredicate fun _ : X ↦ A where
  pred {U} f := IsLocallyConstant f
  res {_ _} i f hf := hf.comp_continuous (Opens.isOpenEmbedding_of_le i.le).continuous
  locality {U} f hf := (IsLocallyConstant.iff_exists_open f).2 fun x ↦ by
    rcases hf x with ⟨V, hxV, i, hi⟩
    rcases hi.exists_open ⟨x.1, hxV⟩ with ⟨W, hW_open, hxW, hW⟩
    refine ⟨i '' W, (Opens.isOpenEmbedding_of_le i.le).isOpenMap _ hW_open, ?_, ?_⟩
    · exact ⟨⟨x.1, hxV⟩, hxW, by ext; rfl⟩
    · rintro y ⟨z, hz, rfl⟩
      simpa using hW z hz

/-- Definition 6.7.4 source-facing presheaf: over an open `U ⊆ X`, the sections are the locally
constant maps `U → A`, viewed canonically as the subpresheaf of all `A`-valued functions cut out by
the local predicate `IsLocallyConstant`. -/
abbrev locallyConstantPresheaf (A : Type (max u v)) : X.Presheaf (Type (max u v)) :=
  subpresheafToTypes (locallyConstantPredicate X A).toPrelocalPredicate

/-- The source-facing locally constant presheaf is a sheaf. -/
theorem locallyConstantPresheaf_isSheaf (A : Type (max u v)) :
    (locallyConstantPresheaf X A).IsSheaf :=
  subpresheafToTypes.isSheaf (locallyConstantPredicate X A)

/-- Definition 6.7.4 source-facing sheaf: the sheaf of locally constant `A`-valued functions. -/
abbrev locallyConstantSheaf (A : Type (max u v)) : TopCat.Sheaf (Type (max u v)) X :=
  subsheafToTypes (locallyConstantPredicate X A)

section

variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

/- Definition 6.7.4: the constant sheaf on `X` with value `A` is the canonical sheafification
of the constant presheaf, namely `CategoryTheory.constantSheaf`. -/
recall CategoryTheory.constantSheaf

public def constantToLocallyConstantPresheaf (A : Type u) :
    (A ₚ X) ⟶ locallyConstantPresheaf X A where
  app U a := ⟨fun _ ↦ a, IsLocallyConstant.const a⟩
  naturality {_ _} i := by
    rfl

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- Helper for Definition 6.7.4: the constant-to-locally-constant presheaf map is locally
surjective because every locally constant section is constant on a neighborhood of each point. -/
private theorem constantToLocallyConstantPresheaf_isLocallySurjective (A : Type u) :
    CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (constantToLocallyConstantPresheaf X A) := by
  constructor
  intro U s x hx
  -- Use local constancy to choose a neighborhood where the section is literally constant.
  rcases s.2.exists_open ⟨x, hx⟩ with ⟨V, hV_open, hxV, hV⟩
  let W : Opens X := ⟨Subtype.val '' V, U.2.isOpenMap_subtype_val _ hV_open⟩
  have hW_le : W ≤ U := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact z.2
  refine ⟨W, homOfLE hW_le, ?_, ?_⟩
  · -- The chosen neighborhood is hit by the constant section with value `s x`.
    refine ⟨s.1 ⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    funext y
    rcases y.2 with ⟨z, hz, hyz⟩
    have hz_eq : z = ⟨y, hW_le y.2⟩ := by
      apply Subtype.ext
      simpa using hyz
    simpa [hz_eq] using (hV z hz).symm
  · exact ⟨⟨x, hx⟩, hxV, rfl⟩

omit [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)] in
/-- Helper for Definition 6.7.4: equality of two constant sections holds locally because, at each
point, evaluating the equality shows the two constants agree on the whole ambient open. -/
private theorem constantToLocallyConstantPresheaf_isLocallyInjective (A : Type u) :
    CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (constantToLocallyConstantPresheaf X A) := by
  constructor
  intro U a b h x hx
  -- Evaluate the equality of constant functions at the chosen point to identify the constants.
  have hab : a = b := by
    exact congrFun (congrArg Subtype.val h) ⟨x, hx⟩
  refine ⟨U.unop, 𝟙 _, ?_, hx⟩
  simp [CategoryTheory.Presheaf.equalizerSieve, hab]

/-- Definition 6.7.4 bridge: the canonical comparison from the constant sheaf with value `A` to
the source-facing sheaf of locally constant `A`-valued functions. -/
noncomputable def constantSheafToLocallyConstantSheaf (A : Type u) :
    (constantSheaf (Opens.grothendieckTopology X) (Type u)).obj A ⟶
      locallyConstantSheaf X A :=
  ⟨sheafifyLift (Opens.grothendieckTopology X) (constantToLocallyConstantPresheaf X A)
      (locallyConstantPresheaf_isSheaf X A)⟩

/-- Helper for Definition 6.7.4: the concrete bridge to locally constant functions factors through
the generic sheafification map and the inverse of the sheafification isomorphism on the target
sheaf. -/
public theorem constantSheafToLocallyConstantSheaf_hom_factorization
    (A : Type u) :
    (constantSheafToLocallyConstantSheaf X A).hom =
      ((presheafToSheaf (Opens.grothendieckTopology X) (Type u)).map
          (constantToLocallyConstantPresheaf X A)).hom ≫
        (sheafificationIso (locallyConstantSheaf X A)).inv.hom := by
  let J := Opens.grothendieckTopology X
  let η : (A ₚ X) ⟶ locallyConstantPresheaf X A := constantToLocallyConstantPresheaf X A
  -- Compare the concrete bridge with the universal sheafification map followed by the inverse
  -- of the target sheafification isomorphism.
  simpa [J, η, constantSheafToLocallyConstantSheaf, CategoryTheory.sheafificationIso,
    CategoryTheory.isoSheafify_inv] using
    (CategoryTheory.sheafifyMap_sheafifyLift
      (J := J) η (𝟙 (locallyConstantPresheaf X A))
      (locallyConstantPresheaf_isSheaf X A))

/-- Definition 6.7.4 companion: the canonical comparison from the constant sheaf to the sheaf of
locally constant functions is an isomorphism. -/
theorem constantSheafToLocallyConstantSheaf_isIso (A : Type u) :
    IsIso (constantSheafToLocallyConstantSheaf X A) := by
  let J := Opens.grothendieckTopology X
  let f :
      (constantSheaf J (Type u)).obj A ⟶
        (presheafToSheaf J (Type u)).obj (locallyConstantPresheaf X A) :=
    (presheafToSheaf J (Type u)).map (constantToLocallyConstantPresheaf X A)
  let g :
      (presheafToSheaf J (Type u)).obj (locallyConstantPresheaf X A) ⟶
        locallyConstantSheaf X A :=
    (sheafificationIso (locallyConstantSheaf X A)).inv
  -- Route correction: use the library equivalence between local bijectivity of a presheaf map
  -- and of its sheafification map, then factor the concrete comparison through that map.
  have hf_inj : CategoryTheory.Sheaf.IsLocallyInjective (J := J) f := by
    -- Unfold `f` and transfer local injectivity directly across `presheafToSheaf.map`.
    change CategoryTheory.Sheaf.IsLocallyInjective
      ((presheafToSheaf J (Type u)).map (constantToLocallyConstantPresheaf X A))
    exact
      (Presheaf.isLocallyInjective_presheafToSheaf_map_iff
        (J := J) (A := Type u) (φ := constantToLocallyConstantPresheaf X A)).2
        (constantToLocallyConstantPresheaf_isLocallyInjective (X := X) A)
  have hf_surj : CategoryTheory.Sheaf.IsLocallySurjective (J := J) f := by
    -- Unfold `f` and transfer local surjectivity by the analogous equivalence.
    change CategoryTheory.Sheaf.IsLocallySurjective
      ((presheafToSheaf J (Type u)).map (constantToLocallyConstantPresheaf X A))
    exact
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
        (J := J) (A := Type u) (φ := constantToLocallyConstantPresheaf X A)).2
        (constantToLocallyConstantPresheaf_isLocallySurjective (X := X) A)
  have hf_iso : IsIso f := by
    -- A locally bijective morphism of sheaves of types is an isomorphism.
    exact
      (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso
        (J := J) (A := Type u) (f := f)).1 ⟨hf_inj, hf_surj⟩
  have hg_iso : IsIso g := by
    infer_instance
  have hfactor : constantSheafToLocallyConstantSheaf X A = f ≫ g := by
    -- Identify the concrete bridge with the sheafified map followed by the target inverse.
    apply CategoryTheory.Sheaf.hom_ext
    exact constantSheafToLocallyConstantSheaf_hom_factorization (X := X) (A := A)
  letI : IsIso f := hf_iso
  letI : IsIso g := hg_iso
  rw [hfactor]
  infer_instance

/-- Definition 6.7.4 companion: for every open `U ⊆ X`, the induced map on sections of the
canonical comparison from the constant sheaf with value `A` to the sheaf of locally constant
`A`-valued functions is an isomorphism. -/
theorem constantSheafToLocallyConstantSheaf_app_isIso
    (A : Type u) (U : Opens X) :
    IsIso ((constantSheafToLocallyConstantSheaf X A).hom.app (op U)) := by
  letI := constantSheafToLocallyConstantSheaf_isIso X A
  letI :
      IsIso
        ((sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).map
          (constantSheafToLocallyConstantSheaf X A)) :=
    Functor.map_isIso _ (constantSheafToLocallyConstantSheaf X A)
  simpa using
    (show IsIso
      ((((sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).map
          (constantSheafToLocallyConstantSheaf X A)).app (op U))) by
      infer_instance)

end

end
