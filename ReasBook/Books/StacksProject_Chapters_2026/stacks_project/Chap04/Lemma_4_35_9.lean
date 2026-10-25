module

public import stacks_project.Chap04.Lemma_4_2_18
public import stacks_project.Chap04.Lemma_4_2_19
public import stacks_project.Chap04.Definition_4_35_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v uS vS

namespace CategoryTheory

open Functor Functor.Fiber IsHomLift IsStronglyCartesian

variable {C : Type u} [Category.{v} C]

namespace FibredCategoryMor

section

variable {X Y : FibredCategoryOver C}
variable (F : X ⟶ Y)

/-- Helper for Lemma 4.35.9: use the canonical `HasFibers` pullbacks as an explicit pullback
system so later proofs can refer to the chosen pullback object and map without extra instance
search. -/
private noncomputable abbrev local_canonical_pullback_choice
    {S : Type uS} [Category.{vS} S] (p : S ⥤ C) [p.IsFibered] :
    PullbackChoice p :=
  let _ : HasFibers p := HasFibers.canonical p
  { obj := fun f x ↦ HasFibers.mkPullback f x.2
    map := fun f x ↦ HasFibers.pullbackMap f x.2
    isStronglyCartesian := fun f x ↦
      Functor.IsFibered.isStronglyCartesian_of_isCartesian p f (HasFibers.pullbackMap f x.2) }

/-- Helper for Lemma 4.35.9: a morphism into a strongly cartesian arrow over `f` is equivalent to
the corresponding vertical morphism in the fiber over the domain of `f`. -/
private noncomputable def hom_over_equiv_vertical_hom_to_strongly_cartesian
    {U V : C} (x : X.p.Fiber U) {y' y : X.S} (f : U ⟶ V) (φ : y' ⟶ y)
    [X.p.IsStronglyCartesian f φ] :
    { ψ : x.1 ⟶ y // X.p.IsHomLift f ψ } ≃
      (x ⟶ Functor.Fiber.mk (domain_eq X.p f φ)) := by
  rcases x with ⟨x, rfl⟩
  have hf_id : f = 𝟙 (X.p.obj x) ≫ f := by
    simp
  have hφ : X.p.IsHomLift f φ :=
    (show X.p.IsStronglyCartesian f φ from inferInstance).toIsHomLift
  refine
    { toFun := fun ψ ↦
        letI : X.p.IsHomLift f φ := hφ
        letI : X.p.IsHomLift f ψ.1 := ψ.2
        ⟨IsStronglyCartesian.map (p := X.p) f φ (g := 𝟙 (X.p.obj x)) hf_id ψ.1, by
          simpa using
            (inferInstance :
              X.p.IsHomLift (𝟙 (X.p.obj x))
                (IsStronglyCartesian.map (p := X.p) f φ (g := 𝟙 (X.p.obj x)) hf_id ψ.1))⟩
      invFun := fun τ ↦
        letI : X.p.IsHomLift f φ := hφ
        let τhom : x ⟶ y' := τ.1
        letI : X.p.IsHomLift (𝟙 (X.p.obj x)) τhom := τ.2
        let hτφ : X.p.IsHomLift ((𝟙 (X.p.obj x)) ≫ f) (τhom ≫ φ) :=
          IsHomLift.comp X.p (𝟙 (X.p.obj x)) f τhom φ
        ⟨τhom ≫ φ, by
          simpa using hτφ⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro ψ
    letI : X.p.IsHomLift f φ := hφ
    letI : X.p.IsHomLift f ψ.1 := ψ.2
    apply Subtype.ext
    exact IsStronglyCartesian.fac (p := X.p) f φ (g := 𝟙 (X.p.obj x)) hf_id ψ.1
  · intro τ
    letI : X.p.IsHomLift f φ := hφ
    let τhom : x ⟶ y' := τ.1
    letI : X.p.IsHomLift (𝟙 (X.p.obj x)) τhom := τ.2
    let hτφ : X.p.IsHomLift ((𝟙 (X.p.obj x)) ≫ f) (τhom ≫ φ) :=
      IsHomLift.comp X.p (𝟙 (X.p.obj x)) f τhom φ
    letI : X.p.IsHomLift f (τhom ≫ φ) := by
      simpa using hτφ
    apply Functor.Fiber.hom_ext
    exact
      (IsStronglyCartesian.map_uniq (p := X.p) f φ (g := 𝟙 (X.p.obj x))
        hf_id (τhom ≫ φ) τhom rfl).symm

/-- Helper for Lemma 4.35.9: a morphism of fibred categories sends a lift over `f` to a lift over
the same arrow `f`. -/
private theorem map_isHomLift_over_base
    {U V : C} {a b : X.S} {f : U ⟶ V} {ψ : a ⟶ b}
    (hψ : X.p.IsHomLift f ψ) :
    Y.p.IsHomLift f ((toFunctor F).map ψ) := by
  -- The based-functor compatibility already transports the lifting equation along `F`.
  letI : X.p.IsHomLift f ψ := hψ
  exact (show Y.p.IsHomLift f ((toFunctor F).map ψ) from inferInstance)

/-- Helper for Lemma 4.35.9: the based-functor compatibility rewrites the image of a morphism in
the total category to the corresponding base morphism in `C`. -/
private theorem map_base_eq
    {a b : X.S} (ψ : a ⟶ b) :
    Y.p.map ((toFunctor F).map ψ) =
      eqToHom (BasedFunctor.w_obj (toBasedFunctor F) a) ≫
        X.p.map ψ ≫ eqToHom (BasedFunctor.w_obj (toBasedFunctor F) b).symm := by
  simpa using Functor.congr_hom (toBasedFunctor F).w ψ

/-- Helper for Lemma 4.35.9: a morphism of fibred categories sends a strongly cartesian morphism
over `f` to a strongly cartesian morphism over the same arrow `f`. -/
private theorem map_stronglyCartesian_over_base
    {U V : C} {a b : X.S} {f : U ⟶ V} {φ : a ⟶ b}
    (hφ : X.p.IsStronglyCartesian f φ) :
    Y.p.IsStronglyCartesian f ((toFunctor F).map φ) := by
  -- First rewrite both source and target base indices to the actual projected arrows.
  have hφ' : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    letI : X.p.IsStronglyCartesian f φ := hφ
    subst_hom_lift X.p f φ
    simpa using hφ
  have hmap :
      Y.p.IsStronglyCartesian (Y.p.map ((toFunctor F).map φ)) ((toFunctor F).map φ) :=
    FibredCategoryMor.map_stronglyCartesian F φ hφ'
  have hLift : Y.p.IsHomLift f ((toFunctor F).map φ) :=
    map_isHomLift_over_base (F := F) hφ.toIsHomLift
  letI : Y.p.IsHomLift f ((toFunctor F).map φ) := hLift
  subst_hom_lift Y.p f ((toFunctor F).map φ)
  simpa using hmap

/-- Helper for Lemma 4.35.9: the vertical factor produced by the strongly-cartesian reduction
composes back to the original morphism over `f`. -/
private theorem vertical_factor_comp_eq
    {U V : C} {x : X.p.Fiber U} {y' y : X.S} (f : U ⟶ V) (φ : y' ⟶ y)
    [X.p.IsStronglyCartesian f φ]
    (ψ : { η : x.1 ⟶ y // X.p.IsHomLift f η }) :
    ((hom_over_equiv_vertical_hom_to_strongly_cartesian (X := X) x f φ).toFun ψ).1 ≫ φ = ψ.1 := by
  rcases x with ⟨x, rfl⟩
  letI : X.p.IsHomLift f ψ.1 := ψ.2
  have hf_id : f = 𝟙 (X.p.obj x) ≫ f := by simp
  change
    IsStronglyCartesian.map (p := X.p) f φ (g := 𝟙 (X.p.obj x)) hf_id ψ.1 ≫ φ = ψ.1
  exact IsStronglyCartesian.fac (p := X.p) f φ (g := 𝟙 (X.p.obj x)) hf_id ψ.1

/-- Helper for Lemma 4.35.9: factoring through a chosen strongly cartesian lift commutes with
applying a morphism of fibred categories. -/
private theorem map_vertical_factor_eq_vertical_factor_map
    {U V : C} {x : X.p.Fiber U} {y' y : X.S} (f : U ⟶ V) (φ : y' ⟶ y)
    [X.p.IsStronglyCartesian f φ]
    [Y.p.IsStronglyCartesian f ((toFunctor F).map φ)]
    (ψ : { η : x.1 ⟶ y // X.p.IsHomLift f η }) :
    (fiberFunctor F U).map
        ((hom_over_equiv_vertical_hom_to_strongly_cartesian (X := X) x f φ).toFun ψ) =
      (hom_over_equiv_vertical_hom_to_strongly_cartesian
          (X := Y) ((fiberFunctor F U).obj x) f ((toFunctor F).map φ)).toFun
        ⟨(toFunctor F).map ψ.1, map_isHomLift_over_base (F := F) ψ.2⟩ := by
  -- Normalize the fiber object so the source and target vertical factors live over the same
  -- identity arrow on the base object `X.p.obj x`.
  rcases x with ⟨x, rfl⟩
  let τX :=
    ((hom_over_equiv_vertical_hom_to_strongly_cartesian (X := X) ⟨x, rfl⟩ f φ).toFun ψ)
  have hτX : Y.p.IsHomLift (𝟙 (X.p.obj x)) ((toFunctor F).map τX.1) :=
    map_isHomLift_over_base (F := F) τX.2
  letI : Y.p.IsHomLift (𝟙 (X.p.obj x)) ((toFunctor F).map τX.1) := hτX
  let τY :=
    ((hom_over_equiv_vertical_hom_to_strongly_cartesian
        (X := Y) ((fiberFunctor F (X.p.obj x)).obj ⟨x, rfl⟩) f ((toFunctor F).map φ)).toFun
      ⟨(toFunctor F).map ψ.1, map_isHomLift_over_base (F := F) ψ.2⟩)
  letI : Y.p.IsHomLift (𝟙 (X.p.obj x)) τY.1 := τY.2
  apply Functor.Fiber.hom_ext
  change (toFunctor F).map τX.1 = τY.1
  -- Map the source factorization identity across `F`; this gives the comparison equation needed
  -- for the target-side uniqueness comparison.
  have hfacX : (toFunctor F).map τX.1 ≫ (toFunctor F).map φ = (toFunctor F).map ψ.1 := by
    simpa [τX, Functor.map_comp] using
      congrArg ((toFunctor F).map)
        (vertical_factor_comp_eq (X := X) (x := ⟨x, rfl⟩) (f := f) (φ := φ) ψ)
  have hfacY : τY.1 ≫ (toFunctor F).map φ = (toFunctor F).map ψ.1 := by
    simpa [τY] using
      (vertical_factor_comp_eq
        (X := Y) (x := (fiberFunctor F (X.p.obj x)).obj ⟨x, rfl⟩) (f := f)
        (φ := ((toFunctor F).map φ))
        ⟨(toFunctor F).map ψ.1, map_isHomLift_over_base (F := F) ψ.2⟩)
  exact
    @IsStronglyCartesian.ext _ _ _ _ Y.p _ _ _ _ f ((toFunctor F).map φ) inferInstance
      _ _ (𝟙 (X.p.obj x)) ((toFunctor F).map τX.1) τY.1 hτX τY.2
      (hfacX.trans hfacY.symm)

/- Domain-style sampling for Lemma 4.35.9:
- primary domain: morphisms of fibred categories over `C` and, in the source-facing textbook
  specialization, morphisms of categories fibred in groupoids;
- sampled owner-level declarations:
  `FibredCategoryMor.fiberFunctor`,
  `FibredInGroupoidsMor.fiberFunctor`,
  `FibredInGroupoidsMor.G`,
  `Functor.IsEquivalence`,
  `BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase`,
  `FibredInGroupoidsMor.IsEquivalenceOverBase`;
- best owner abstraction: the source-facing owner is `FibredInGroupoidsMor`; the faithful,
  fully faithful, and ordinary-equivalence clauses admit a canonical bridge/view generalization on
  the ambient owner `FibredCategoryMor`, while `F.IsEquivalenceOverBase` remains a derived
  upgrade over the base rather than the primary textbook owner here;
- primitive data: the owner morphism `F : FibredCategoryMor X Y`;
- derived API: the induced fiber functors `F.fiberFunctor U`, together with the source-facing
  specialization to `FibredInGroupoidsMor` and the derived over-base equivalence upgrade.

Source/core/bridge triage:
- `source-facing`: the `FibredInGroupoidsMor` faithful, fully faithful, and ordinary-equivalence
  statements below;
- `core/canonical`: `(toBasedFunctor F).Faithful`,
  `Nonempty (toBasedFunctor F).FullyFaithful`, and `(G F).IsEquivalence`;
- `bridge/view`: the ambient `FibredCategoryMor` faithful and fully faithful criteria and the
  induced fiber functors `fiberFunctor F U`; `IsEquivalenceOverBase F` is a companion upgrade
  over the base. -/

-- Proof sketch: if `F` is faithful, then its restriction to each fibre is faithful. Conversely,
-- a morphism over an arbitrary base arrow is determined by the corresponding vertical morphism
-- into a chosen pullback, so fibrewise faithfulness implies global faithfulness.
/-- Bridge/view form of Lemma 4.35.9: a morphism of fibred categories over `C` is faithful
exactly when each induced functor on the fiber over `U` is faithful. -/
theorem faithful_iff_fiberwise :
    (toBasedFunctor F).Faithful ↔ ∀ U : C, (fiberFunctor F U).Faithful := by
  constructor
  · intro hF U
    letI : (toBasedFunctor F).Faithful := hF
    refine ⟨?_⟩
    intro x y φ ψ hφψ
    apply Functor.Fiber.hom_ext
    exact (toBasedFunctor F).map_injective (congrArg Subtype.val hφψ)
  · intro hFiber
    refine ⟨?_⟩
    intro a b ψ₁ ψ₂ hψ
    let U := X.p.obj a
    let V := X.p.obj b
    let x : X.p.Fiber U := ⟨a, rfl⟩
    let y : X.p.Fiber V := ⟨b, rfl⟩
    have hbase :
        X.p.map ψ₁ = X.p.map ψ₂ := by
      have hmap := congrArg (fun k ↦ Y.p.map k) hψ
      calc
        X.p.map ψ₁
            =
          eqToHom (BasedFunctor.w_obj (toBasedFunctor F) a).symm ≫
            Y.p.map ((toFunctor F).map ψ₁) ≫
            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) b) := by
              simp [map_base_eq (F := F) ψ₁, Category.assoc]
        _ =
          eqToHom (BasedFunctor.w_obj (toBasedFunctor F) a).symm ≫
            Y.p.map ((toFunctor F).map ψ₂) ≫
            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) b) := by
              simpa using
                congrArg
                  (fun k ↦
                    eqToHom (BasedFunctor.w_obj (toBasedFunctor F) a).symm ≫
                      Y.p.map k ≫
                      eqToHom (BasedFunctor.w_obj (toBasedFunctor F) b))
                  hψ
        _ = X.p.map ψ₂ := by
              simp [map_base_eq (F := F) ψ₂, Category.assoc]
    let f : U ⟶ V := X.p.map ψ₁
    let hc := local_canonical_pullback_choice X.p
    let φ : (f ^*[hc] y).1 ⟶ b := hc.map f y
    haveI : X.p.IsStronglyCartesian f φ := by
      exact hc.isStronglyCartesian f y
    have hψ₁Lift : X.p.IsHomLift f ψ₁ := by
      simp [f]
    have hψ₂Lift : X.p.IsHomLift f ψ₂ := by
      exact IsHomLift.of_fac X.p f ψ₂ rfl rfl (by simpa [f] using hbase)
    have hφY : Y.p.IsStronglyCartesian f ((toFunctor F).map φ) :=
      map_stronglyCartesian_over_base (F := F)
        (hφ := (show X.p.IsStronglyCartesian f φ from inferInstance))
    letI : Y.p.IsStronglyCartesian f ((toFunctor F).map φ) := hφY
    let τ₁ :
        x ⟶ Functor.Fiber.mk (IsHomLift.domain_eq X.p f φ) :=
      (hom_over_equiv_vertical_hom_to_strongly_cartesian (X := X) x f φ).toFun
        ⟨ψ₁, hψ₁Lift⟩
    let τ₂ :
        x ⟶ Functor.Fiber.mk (IsHomLift.domain_eq X.p f φ) :=
      (hom_over_equiv_vertical_hom_to_strongly_cartesian (X := X) x f φ).toFun
        ⟨ψ₂, hψ₂Lift⟩
    have hτY :
        (hom_over_equiv_vertical_hom_to_strongly_cartesian
            (X := Y) ((fiberFunctor F U).obj x) f ((toFunctor F).map φ)).toFun
          ⟨(toFunctor F).map ψ₁, map_isHomLift_over_base (F := F) hψ₁Lift⟩ =
        (hom_over_equiv_vertical_hom_to_strongly_cartesian
            (X := Y) ((fiberFunctor F U).obj x) f ((toFunctor F).map φ)).toFun
          ⟨(toFunctor F).map ψ₂, map_isHomLift_over_base (F := F) hψ₂Lift⟩ := by
      apply congrArg
      apply Subtype.ext
      exact hψ
    have hτ₁map :
        (fiberFunctor F U).map τ₁ =
          (hom_over_equiv_vertical_hom_to_strongly_cartesian
              (X := Y) ((fiberFunctor F U).obj x) f ((toFunctor F).map φ)).toFun
            ⟨(toFunctor F).map ψ₁, map_isHomLift_over_base (F := F) hψ₁Lift⟩ := by
      simpa [τ₁] using
        map_vertical_factor_eq_vertical_factor_map
          (F := F) (x := x) (f := f) (φ := φ) ⟨ψ₁, hψ₁Lift⟩
    have hτ₂map :
        (fiberFunctor F U).map τ₂ =
          (hom_over_equiv_vertical_hom_to_strongly_cartesian
              (X := Y) ((fiberFunctor F U).obj x) f ((toFunctor F).map φ)).toFun
            ⟨(toFunctor F).map ψ₂, map_isHomLift_over_base (F := F) hψ₂Lift⟩ := by
      simpa [τ₂] using
        map_vertical_factor_eq_vertical_factor_map
          (F := F) (x := x) (f := f) (φ := φ) ⟨ψ₂, hψ₂Lift⟩
    have hmapτ : (fiberFunctor F U).map τ₁ = (fiberFunctor F U).map τ₂ := by
      rw [hτ₁map, hτY, hτ₂map]
    letI : (fiberFunctor F U).Faithful := hFiber U
    have hτ : τ₁ = τ₂ := (fiberFunctor F U).map_injective hmapτ
    calc
      ψ₁ = τ₁.1 ≫ φ := by
        symm
        exact vertical_factor_comp_eq (X := X) (x := x) (f := f) (φ := φ) ⟨ψ₁, hψ₁Lift⟩
      _ = τ₂.1 ≫ φ := by rw [congrArg Subtype.val hτ]
      _ = ψ₂ := vertical_factor_comp_eq (X := X) (x := x) (f := f) (φ := φ) ⟨ψ₂, hψ₂Lift⟩

-- Proof sketch: the fully-faithful statement is proved fibrewise exactly as in the faithful case,
-- using pullbacks to reduce arbitrary morphisms over `f : U ⟶ V` to vertical morphisms in the
-- fibre over `U`.
/-- Bridge/view form of Lemma 4.35.9: a morphism of fibred categories over `C` is fully faithful
exactly when each induced functor on the fiber over `U` is fully faithful. -/
theorem fullyFaithful_iff_fiberwise :
    Nonempty (toBasedFunctor F).FullyFaithful ↔
      ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful :=
  by
    constructor
    · rintro ⟨hF⟩ U
      letI : (fiberFunctor F U).Faithful := by
        refine ⟨?_⟩
        intro x y φ ψ hφψ
        apply Functor.Fiber.hom_ext
        exact hF.map_injective (congrArg Subtype.val hφψ)
      letI : (fiberFunctor F U).Full := by
        refine ⟨?_⟩
        intro x y φ
        let ψ : x.1 ⟶ y.1 := hF.preimage φ.1
        have hψ : X.p.IsHomLift (𝟙 U) ψ := by
          have hFψ : Y.p.IsHomLift (𝟙 U) ((toFunctor F).map ψ) := by
            simpa [ψ] using (φ.2 : Y.p.IsHomLift (𝟙 U) φ.1)
          exact ((toBasedFunctor F).isHomLift_iff (𝟙 U) ψ).1 hFψ
        refine ⟨⟨ψ, hψ⟩, ?_⟩
        apply Functor.Fiber.hom_ext
        change (toFunctor F).map ψ = φ.1
        simpa [ψ] using hF.map_preimage φ.1
      exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩
    · intro hFiber
      classical
      rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
      intro a b
      constructor
      · letI : (toBasedFunctor F).Faithful :=
          (faithful_iff_fiberwise (F := F)).2
            (fun U ↦ (Classical.choice (hFiber U)).faithful)
        intro φ ψ hφψ
        exact (toBasedFunctor F).map_injective hφψ
      · intro χ
        let U := X.p.obj a
        let V := X.p.obj b
        let x : X.p.Fiber U := ⟨a, rfl⟩
        let y : X.p.Fiber V := ⟨b, rfl⟩
        let f : U ⟶ V :=
          eqToHom (BasedFunctor.w_obj (toBasedFunctor F) a).symm ≫
            Y.p.map χ ≫
            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) b)
        have hχ : Y.p.IsHomLift f χ := by
          refine IsHomLift.of_fac Y.p f χ
            (BasedFunctor.w_obj (toBasedFunctor F) a)
            (BasedFunctor.w_obj (toBasedFunctor F) b) ?_
          simp [f]
        let hc := local_canonical_pullback_choice X.p
        let φ : (f ^*[hc] y).1 ⟶ b := hc.map f y
        haveI : X.p.IsStronglyCartesian f φ := by
          exact hc.isStronglyCartesian f y
        have hφY : Y.p.IsStronglyCartesian f ((toFunctor F).map φ) :=
          map_stronglyCartesian_over_base (F := F)
            (hφ := (show X.p.IsStronglyCartesian f φ from inferInstance))
        letI : Y.p.IsStronglyCartesian f ((toFunctor F).map φ) := hφY
        let τY :
            (fiberFunctor F U).obj x ⟶ (fiberFunctor F U).obj (f ^*[hc] y) :=
          (hom_over_equiv_vertical_hom_to_strongly_cartesian
              (X := Y) ((fiberFunctor F U).obj x) f ((toFunctor F).map φ)).toFun
            ⟨χ, hχ⟩
        let hffU : (fiberFunctor F U).FullyFaithful := Classical.choice (hFiber U)
        let τX :
            x ⟶ f ^*[hc] y :=
          hffU.preimage τY
        have hτX : (toFunctor F).map τX.1 = τY.1 := by
          have hEq : (fiberFunctor F U).map τX = τY := by
            simpa [τX] using hffU.map_preimage τY
          exact congrArg (Functor.Fiber.fiberInclusion.map) hEq
        have hτYcomp : τY.1 ≫ (toFunctor F).map φ = χ := by
          simpa [τY] using
            (vertical_factor_comp_eq
              (X := Y) (x := (fiberFunctor F U).obj x) (f := f) (φ := ((toFunctor F).map φ))
              ⟨χ, hχ⟩)
        refine ⟨τX.1 ≫ φ, ?_⟩
        rw [Functor.map_comp, hτX]
        exact hτYcomp

end

end FibredCategoryMor

namespace FibredInGroupoidsMor

section

variable {X Y : FibredInGroupoidsOver C}
variable (F : X ⟶ Y)

/-- Lemma 4.35.9, faithful clause, on the source-facing owner `FibredInGroupoidsMor`. -/
theorem faithful_iff_fiberwise :
    (toBasedFunctor F).Faithful ↔ ∀ U : C, (fiberFunctor F U).Faithful := by
  simpa using
    (FibredCategoryMor.faithful_iff_fiberwise
      (F := FibredInGroupoidsMor.toFibredCategoryMor F))

/-- Lemma 4.35.9, fully faithful clause, on the source-facing owner `FibredInGroupoidsMor`. -/
theorem fullyFaithful_iff_fiberwise :
    Nonempty (toBasedFunctor F).FullyFaithful ↔
      ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful := by
  simpa using
    (FibredCategoryMor.fullyFaithful_iff_fiberwise
      (F := FibredInGroupoidsMor.toFibredCategoryMor F))

/-- Helper for Lemma 4.35.9: an equivalence of total categories can be corrected fiberwise to a
preimage lying over the same base object. -/
private theorem fiber_preimage_of_total_equivalence
    (hF : (G F).IsEquivalence) (U : C) (y : Y.p.Fiber U) :
    ∃ x : X.p.Fiber U, Nonempty (y ≅ (fiberFunctor F U).obj x) := by
  letI : (G F).IsEquivalence := hF
  let x₀ := (G F).objPreimage y.1
  let e₀ : y.1 ≅ (G F).obj x₀ := ((G F).objObjPreimageIso y.1).symm
  let f : U ⟶ X.p.obj x₀ :=
    eqToHom y.2.symm ≫
      Y.p.map e₀.hom ≫
        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) x₀)
  have he₀Lift : Y.p.IsHomLift f e₀.hom := by
    -- The chosen total isomorphism determines the base arrow used to pull the source preimage
    -- back into the fiber over `U`.
    refine IsHomLift.of_fac Y.p f e₀.hom y.2 (BasedFunctor.w_obj (toBasedFunctor F) x₀) ?_
    rfl
  let hc := FibredCategoryMor.local_canonical_pullback_choice X.p
  let x₀Fiber : X.p.Fiber (X.p.obj x₀) := ⟨x₀, rfl⟩
  let x : X.p.Fiber U := f ^*[hc] x₀Fiber
  let φX : x.1 ⟶ x₀ := hc.map f x₀Fiber
  haveI : X.p.IsStronglyCartesian f φX := hc.isStronglyCartesian f x₀Fiber
  have hφY : Y.p.IsStronglyCartesian f ((G F).map φX) :=
    FibredCategoryMor.map_stronglyCartesian_over_base
      (F := FibredInGroupoidsMor.toFibredCategoryMor F)
      (hφ := (show X.p.IsStronglyCartesian f φX from inferInstance))
  letI : Y.p.IsStronglyCartesian f ((G F).map φX) := hφY
  let τY :
      y ⟶ Functor.Fiber.mk (IsHomLift.domain_eq Y.p f ((G F).map φX)) :=
    (FibredCategoryMor.hom_over_equiv_vertical_hom_to_strongly_cartesian
        (X := Y) y f ((G F).map φX)).toFun
      ⟨e₀.hom, he₀Lift⟩
  haveI : IsIso τY := by infer_instance
  refine ⟨x, ?_⟩
  refine ⟨?_⟩
  simpa [x, φX, hc] using asIso τY

/-- Helper for Lemma 4.35.9: fiberwise equivalences give same-fiber preimages objectwise. -/
private theorem fiber_preimage_of_fiberwise_equivalence
    (hFiber : ∀ U : C, (fiberFunctor F U).IsEquivalence) (U : C) (y : Y.p.Fiber U) :
    ∃ x : X.p.Fiber U, Nonempty (y ≅ (fiberFunctor F U).obj x) := by
  letI : (fiberFunctor F U).IsEquivalence := hFiber U
  -- Use the canonical preimage object chosen by the fiber equivalence.
  refine ⟨(fiberFunctor F U).objPreimage y, ?_⟩
  refine ⟨((fiberFunctor F U).objObjPreimageIso y).symm⟩

/-- Helper for Lemma 4.35.9: an ordinary lift equipped with vertical comparison isomorphisms to
the identity functor already commutes strictly with the base projections. -/
private theorem same_fiber_lift_commutes_with_base
    {j : Y.S ⥤ X.S} (α : 𝟭 Y.S ≅ j ⋙ G F)
    (hjBaseObj : ∀ y : Y.S, X.p.obj (j.obj y) = Y.p.obj y)
    (hαLift : ∀ y : Y.S, Y.p.IsHomLift (𝟙 (Y.p.obj y)) (α.hom.app y)) :
    j ⋙ X.p = Y.p := by
  -- Compare the two projection functors objectwise, then use naturality of the vertical
  -- comparison isomorphism `α` to identify their action on morphisms.
  refine CategoryTheory.Functor.ext hjBaseObj ?_
  intro y y' g
  have hyBase :
      IsHomLift.codomain_eq Y.p (𝟙 (Y.p.obj y)) (α.hom.app y) =
        Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)) (hjBaseObj y) := by
    apply Subsingleton.elim
  have hy'Base :
      IsHomLift.codomain_eq Y.p (𝟙 (Y.p.obj y')) (α.hom.app y') =
        Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) (hjBaseObj y') := by
    apply Subsingleton.elim
  have hyVert :
      Y.p.map (α.hom.app y) =
        eqToHom (Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y))
          (hjBaseObj y)).symm := by
    rw [← hyBase]
    simpa using (IsHomLift.fac' Y.p (𝟙 (Y.p.obj y)) (α.hom.app y))
  have hy'Vert :
      Y.p.map (α.hom.app y') =
        eqToHom (Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y'))
          (hjBaseObj y')).symm := by
    rw [← hy'Base]
    simpa using (IsHomLift.fac' Y.p (𝟙 (Y.p.obj y')) (α.hom.app y'))
  have hnat := congrArg (Functor.map Y.p) (α.hom.naturality g)
  rw [Functor.map_comp, Functor.map_comp, hyVert, hy'Vert] at hnat
  have hleft :
      eqToHom (Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y))
          (hjBaseObj y)) ≫
        Y.p.map g ≫
          eqToHom (Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y'))
            (hjBaseObj y')).symm =
      Y.p.map ((G F).map (j.map g)) := by
    -- After moving the vertical comparison on the source to the left-hand side, naturality is
    -- exactly the desired base-map equation for the mapped lift.
    have h0 :
        Y.p.map g ≫
            eqToHom (Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y'))
              (hjBaseObj y')).symm =
          eqToHom (Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y))
            (hjBaseObj y)).symm ≫
            Y.p.map ((G F).map (j.map g)) := by
      simpa using hnat
    have h1 := congrArg (fun k ↦
      eqToHom (Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y))
        (hjBaseObj y)) ≫ k) h0
    simpa [Category.assoc] using h1
  have hcomm :
      X.p.map (j.map g) =
        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
          Y.p.map ((G F).map (j.map g)) ≫
            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) := by
    -- Rewrite the base map of `F (j.map g)` via the defining over-base equality of `F`.
    have h' := congrArg
      (fun k ↦
        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
          k ≫
            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')))
      (Functor.congr_hom (toBasedFunctor F).w (j.map g))
    simpa [Category.assoc] using h'.symm
  calc
    X.p.map (j.map g) =
        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
          Y.p.map ((G F).map (j.map g)) ≫
            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) := hcomm
    _ =
        eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
          (eqToHom (Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y))
              (hjBaseObj y)) ≫
            Y.p.map g ≫
              eqToHom (Eq.trans (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y'))
                (hjBaseObj y')).symm) ≫
            eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')) := by
          have h' := congrArg
            (fun k ↦
              eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y)).symm ≫
                k ≫
                  eqToHom (BasedFunctor.w_obj (toBasedFunctor F) (j.obj y')))
            hleft
          simpa [Category.assoc] using h'.symm
    _ = eqToHom (hjBaseObj y) ≫ Y.p.map g ≫ eqToHom (hjBaseObj y').symm := by
          simp [Category.assoc]

/-- Helper for Lemma 4.35.9: fiberwise equivalences assemble to an equivalence over the base. -/
private theorem toBasedFunctor_isEquivalenceOverBase_of_fiberwise_isEquivalence
    (hFiber : ∀ U : C, (fiberFunctor F U).IsEquivalence) :
    IsEquivalenceOverBase F := by
  classical
  change BasedFunctor.IsEquivalenceOverBase (toBasedFunctor F)
  -- Route correction: the remaining work is not another pullback transport lemma. The fiberwise
  -- preimages already give an ordinary quasi-inverse; we only need to package it as based data.
  let jFiber : ∀ y : Y.S, X.p.Fiber (Y.p.obj y) :=
    fun y ↦
      Classical.choose
        (fiber_preimage_of_fiberwise_equivalence (F := F) hFiber (Y.p.obj y) ⟨y, rfl⟩)
  let iFiber :
      ∀ y : Y.S, ⟨y, rfl⟩ ≅ (fiberFunctor F (Y.p.obj y)).obj (jFiber y) :=
    fun y ↦
      Classical.choice
        (Classical.choose_spec
          (fiber_preimage_of_fiberwise_equivalence (F := F) hFiber (Y.p.obj y) ⟨y, rfl⟩))
  let jObj : Y.S → X.S := fun y ↦ (jFiber y).1
  let i : ∀ y : Y.S, y ≅ (G F).obj (jObj y) := fun y ↦ by
    simpa [jObj, G, fiberFunctor] using
      (Functor.Fiber.fiberInclusion : Y.p.Fiber (Y.p.obj y) ⥤ Y.S).mapIso (iFiber y)
  have hFiberFullyFaithful :
      ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful := by
    intro U
    letI : (fiberFunctor F U).IsEquivalence := hFiber U
    exact ⟨Functor.FullyFaithful.ofFullyFaithful (fiberFunctor F U)⟩
  have hGlobalFullyFaithful :
      Nonempty (toBasedFunctor F).FullyFaithful :=
    (fullyFaithful_iff_fiberwise (F := F)).2 hFiberFullyFaithful
  let hFF : (toBasedFunctor F).FullyFaithful := Classical.choice hGlobalFullyFaithful
  letI : (G F).Faithful := by
    refine ⟨?_⟩
    intro a b φ ψ hφψ
    exact hFF.map_injective hφψ
  letI : (G F).Full := by
    refine ⟨?_⟩
    intro a b φ
    refine ⟨hFF.preimage φ, ?_⟩
    simpa [G] using hFF.map_preimage φ
  rcases (Functor.fully_faithful_objwise_iso_existsUnique_lift (F := G F) jObj i) with
    ⟨j, ⟨hjObj, α, hα⟩, _⟩
  have hjBaseObj : ∀ y : Y.S, X.p.obj (j.obj y) = Y.p.obj y := by
    intro y
    rw [hjObj y]
    exact (jFiber y).2
  have hαLift : ∀ y : Y.S, Y.p.IsHomLift (𝟙 (Y.p.obj y)) (α.hom.app y) := by
    intro y
    have hiLift : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (i y).hom := by
      simpa [i] using (show Y.p.IsHomLift (𝟙 (Y.p.obj y)) (iFiber y).hom.1 from (iFiber y).hom.2)
    simpa [hα y, hjObj y] using hiLift
  have hjBase : j ⋙ X.p = Y.p :=
    same_fiber_lift_commutes_with_base (F := F) α hjBaseObj hαLift
  let jBased : Y.toBasedCategory ⥤ᵇ X.toBasedCategory :=
    { toFunctor := j
      w := hjBase }
  have hCounitLift : ∀ y : Y.S, Y.p.IsHomLift (𝟙 (Y.p.obj y)) (α.inv.app y) := by
    intro y
    letI : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (α.app y).hom := by simpa using hαLift y
    have : Y.p.IsHomLift (𝟙 (Y.p.obj y)) (α.app y).inv := by infer_instance
    simpa using this
  have eps : BasedFunctor.comp jBased (toBasedFunctor F) ≅ BasedFunctor.id Y.toBasedCategory := by
    simpa [jBased] using BasedNatIso.mkNatIso α.symm hCounitLift
  let compIso : (𝟭 X.S) ⋙ G F ≅ ((G F) ⋙ j) ⋙ G F :=
    (Functor.leftUnitor (G F)).symm ≪≫
      (Functor.rightUnitor (G F)).symm ≪≫
      Functor.isoWhiskerLeft (G F) α ≪≫
      (Functor.associator (G F) j (G F)).symm
  let ηNat : 𝟭 X.S ≅ (G F) ⋙ j :=
    Functor.fullyFaithfulCancelRight (G F) compIso
  have hηLift : ∀ x : X.S, X.p.IsHomLift (𝟙 (X.p.obj x)) (ηNat.hom.app x) := by
    intro x
    have hcompRaw :
        Y.p.IsHomLift (𝟙 (Y.p.obj ((G F).obj x))) (compIso.hom.app x) := by
      -- The whiskered comparison `compIso` has the same component as `α` up to the standard
      -- unitor/associator identities in `Cat`.
      simpa [compIso, Category.assoc] using hαLift ((G F).obj x)
    have hcomp :
        Y.p.IsHomLift (𝟙 (X.p.obj x)) (compIso.hom.app x) := by
      -- Transport the base identity along the over-base equality of `F` at `x`.
      have :
          Y.p.IsHomLift
            (eqToHom (BasedFunctor.w_obj (toBasedFunctor F) x).symm ≫
              𝟙 (Y.p.obj ((G F).obj x)) ≫
                eqToHom (BasedFunctor.w_obj (toBasedFunctor F) x))
            (compIso.hom.app x) := by
        exact inferInstance
      simpa using this
    have hmap : Y.p.IsHomLift (𝟙 (X.p.obj x)) ((G F).map (ηNat.hom.app x)) := by
      -- `fullyFaithfulCancelRight` is defined by taking the preimage of the whiskered component.
      simpa [ηNat, Functor.fullyFaithfulCancelRight_hom_app] using hcomp
    exact ((toBasedFunctor F).isHomLift_iff (𝟙 (X.p.obj x)) (ηNat.hom.app x)).1 hmap
  have eta :
      BasedFunctor.id X.toBasedCategory ≅ BasedFunctor.comp (toBasedFunctor F) jBased := by
    simpa [jBased, BasedFunctor.comp_assoc] using BasedNatIso.mkNatIso ηNat hηLift
  exact BasedFunctor.IsEquivalenceOverBase.mkPrime jBased eta eps

-- Proof sketch: one direction restricts a quasi-inverse of `F` to each fibre. For the converse,
-- fibrewise equivalences imply fibrewise full faithfulness and essential surjectivity; the first
-- gives global full faithfulness by the previous theorem, and the second gives global essential
-- surjectivity because every target object already lies in a fixed fibre.
/-- Lemma 4.35.9: the underlying functor of a morphism of categories fibred in groupoids over
`C` is an equivalence exactly when each induced functor on the fiber over `U` is an equivalence.
-/
theorem isEquivalence_iff_fiberwise :
    (G F).IsEquivalence ↔ ∀ U : C, (fiberFunctor F U).IsEquivalence :=
  by
    constructor
    · intro hF
      letI : (G F).IsEquivalence := hF
      have hGlobalFullyFaithful :
          Nonempty (toBasedFunctor F).FullyFaithful := by
        rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
        intro a b
        simpa [G] using
          (Functor.FullyFaithful.ofFullyFaithful (G F)).map_bijective a b
      have hFiberFullyFaithful :
          ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful :=
        (fullyFaithful_iff_fiberwise (F := F)).1 hGlobalFullyFaithful
      intro U
      have hBij :
          ∀ a b : X.p.Fiber U, Function.Bijective
            ((fiberFunctor F U).map :
              (a ⟶ b) → ((fiberFunctor F U).obj a ⟶ (fiberFunctor F U).obj b)) := by
        rcases hFiberFullyFaithful U with ⟨hFF⟩
        intro a b
        exact hFF.map_bijective a b
      have hEss : (fiberFunctor F U).EssSurj := by
        refine ⟨?_⟩
        intro y
        obtain ⟨x, ⟨e⟩⟩ := fiber_preimage_of_total_equivalence (F := F) hF U y
        exact ⟨x, ⟨e.symm⟩⟩
      exact
        (Functor.isEquivalence_iff_full_faithful_essSurj (fiberFunctor F U)).2
          ⟨hBij, hEss⟩
    · intro hFiber
      -- Fiberwise equivalences give fiberwise full faithfulness, hence global full faithfulness.
      have hFiberFullyFaithful :
          ∀ U : C, Nonempty (fiberFunctor F U).FullyFaithful := by
        intro U
        letI : (fiberFunctor F U).IsEquivalence := hFiber U
        exact ⟨Functor.FullyFaithful.ofFullyFaithful (fiberFunctor F U)⟩
      have hGlobalFullyFaithful :
          Nonempty (toBasedFunctor F).FullyFaithful :=
        (fullyFaithful_iff_fiberwise (F := F)).2 hFiberFullyFaithful
      have hBij :
          ∀ a b : X.S, Function.Bijective
            ((G F).map : (a ⟶ b) → ((G F).obj a ⟶ (G F).obj b)) := by
        rcases hGlobalFullyFaithful with ⟨hFF⟩
        intro a b
        simpa [G] using hFF.map_bijective a b
      have hEss : (G F).EssSurj := by
        refine ⟨?_⟩
        intro y
        obtain ⟨x, ⟨e⟩⟩ :=
          fiber_preimage_of_fiberwise_equivalence
            (F := F) hFiber (Y.p.obj y) ⟨y, rfl⟩
        refine ⟨x.1, ?_⟩
        refine ⟨?_⟩
        -- Forgetting the fiber identifies the chosen same-fiber isomorphism with a total one.
        simpa [G, fiberFunctor] using
          (Functor.Fiber.fiberInclusion : Y.p.Fiber (Y.p.obj y) ⥤ Y.S).mapIso e.symm
      exact
        (Functor.isEquivalence_iff_full_faithful_essSurj (G F)).2
          ⟨hBij, hEss⟩

/-- Companion to Lemma 4.35.9: under the equivalent source-facing conditions, `F` is in
particular an equivalence over the base. -/
theorem isEquivalenceOverBase_of_isEquivalence
    (hF : (G F).IsEquivalence) : IsEquivalenceOverBase F :=
  by
    -- Reduce the public over-base upgrade to the remaining based quasi-inverse construction from
    -- the already-proved fiberwise equivalence criterion.
    exact
      toBasedFunctor_isEquivalenceOverBase_of_fiberwise_isEquivalence (F := F)
        ((isEquivalence_iff_fiberwise (F := F)).1 hF)

end

end FibredInGroupoidsMor

end CategoryTheory
