module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Sites.Point.Comap
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_25_2
public import stacks_project.Chap07.Lemma_7_35_1
public import stacks_project.Chap07.Remark_7_25_10

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite

universe w v u

namespace CategoryTheory

open GrothendieckTopology

section

noncomputable section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]

variable (U : C)
variable [((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).IsRightAdjoint]

/-- Module-mode wrapper for the membership condition in the localized fiber over `x`. -/
lemma point_over_mem_of_eq
    (p : Point.{w} J) {x : p.fiber.obj U} {V : Over U} {y : p.fiber.obj V.left}
    (hy : p.fiber.map V.hom y = x) :
    y ∈ (FunctorToTypes.fromOverSubfunctor p.fiber x).obj V := by
  rwa [FunctorToTypes.mem_fromOverSubfunctor_iff]

/-- Module-mode wrapper for reading the localized-fiber membership condition as an equality. -/
lemma point_over_eq_of_mem
    (p : Point.{w} J) {x : p.fiber.obj U} {V : Over U} {y : p.fiber.obj V.left}
    (hy : y ∈ (FunctorToTypes.fromOverSubfunctor p.fiber x).obj V) :
    p.fiber.map V.hom y = x := by
  rwa [FunctorToTypes.mem_fromOverSubfunctor_iff] at hy

/-- Helper for Lemma 7.35.3: the fiber of the comapped point over `V : C/U` splits by the image
`x : p.fiber.obj U`, exactly as in the source proof. -/
noncomputable def point_over_fiber_sigma_equiv
    (p : Point.{w} J)
    (V : Over U) :
    (Σ x : p.fiber.obj U, (p.over x).fiber.obj V) ≃ p.fiber.obj V.left where
  toFun z := z.2.1
  invFun y := ⟨p.fiber.map V.hom y, ⟨y, point_over_mem_of_eq (U := U) p rfl⟩⟩
  left_inv := by
    rintro ⟨x, y⟩
    cases y with
    | mk y hy =>
        have hy' := point_over_eq_of_mem (U := U) p hy
        cases hy'
        simp
  right_inv := by
    intro y
    rfl

/-- Helper for Lemma 7.35.3: objectwise sections of the pulled-back skyscraper at `p` split into
families of sections of the localized skyscrapers at the points `p.over x`. -/
noncomputable def point_over_skyscraper_section_equiv
    (p : Point.{w} J)
    (V : Over U)
    (E : Type w) :
    (p.fiber.obj V.left → E) ≃
      ∀ x : p.fiber.obj U, ((p.over x).fiber.obj V → E) where
  toFun s := fun x y ↦ s y.1
  invFun t := fun y ↦ t (p.fiber.map V.hom y) ⟨y, point_over_mem_of_eq (U := U) p rfl⟩
  left_inv := by
    intro s
    funext y
    rfl
  right_inv := by
    intro t
    funext x
    funext y
    cases y with
    | mk y hy =>
        have hy' := point_over_eq_of_mem (U := U) p hy
        cases hy'
        rfl

/-- Helper for Lemma 7.35.3: the abstract pullback `j_{U!}` can be tested at the point `p` by the
fiber functor of the comapped point along `Over.forget U`. -/
noncomputable def localizationLowerShriek_sheafFiberIso_comapSheafFiber
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w)) :
    [RepresentablyFlat (Over.forget U)] →
    [InitiallySmall ((Over.forget U) ⋙ p.fiber).Elements] →
    p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢) ≅
      ((p.comap (Over.forget U)
        (J.over_forget_coverPreserving U)).sheafFiber.obj 𝒢) := by
  intro _ _
  let hF : CoverPreserving (J.over U) J (Over.forget U) := J.over_forget_coverPreserving U
  -- First replace the stalk of the abstract left adjoint by the fiber functor of the comapped
  -- point, which is the correct owner for the source proof's split-by-`x` argument.
  simpa using ((p.sheafFiberComapIso (Over.forget U) hF (Type w)).app 𝒢).symm

/-- Helper for Lemma 7.35.3: the stalk of `j_{U!} 𝒢` identifies with the presheaf fiber of the
left Kan extension before the source proof splits generators by their image in `p.fiber.obj U`. -/
noncomputable def
    localizationLowerShriek_sheafFiberIso_presheafFiber_leftKanExtension
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type w)]
    [HasWeakSheafify J (Type w)] :
    p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢) ≅
      p.presheafFiber.obj ((Over.forget U).op.lan.obj 𝒢.1) :=
  -- First rewrite `j_{U!} 𝒢` through the associated-sheaf model of Lemma 7.25.2.
  (p.sheafFiber.mapIso
      ((((Over.forget U).sheafPullback (Type w) (J.over U) J).mapIso
          (sheafificationIso 𝒢)) ≪≫
        localization_lowerShriek_associatedSheafIso J U 𝒢.1)) ≪≫
    -- Then replace the sheaf fiber of the associated sheaf by the presheaf fiber.
    (((p.presheafToSheafCompSheafFiberIso (Type w)).app
      ((Over.forget U).op.lan.obj 𝒢.1)))

/-- Helper for Lemma 7.35.3: after the source proof splits the ambient stalk by
`x : p.fiber.obj U`, each summand is converted from the presheaf fiber of `𝒢.1.obj` to the sheaf
fiber of `𝒢` at the localized point `p.over x`. -/
noncomputable def sigma_pointOver_presheafFiberIsoSigma_pointOver_sheafFiber
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    [HasWeakSheafify (J.over U) (Type w)] :
    (Σ x : p.fiber.obj U, (p.over x).presheafFiber.obj 𝒢.1) ≅
      (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢) :=
  (Equiv.sigmaCongrRight fun x ↦
      ((((p.over x).presheafToSheafCompSheafFiberIso (Type w)).app 𝒢.1).symm ≪≫
        (p.over x).sheafFiber.mapIso (sheafificationIso 𝒢).symm).toEquiv).toIso

/-- Helper for Lemma 7.35.3: under the split-by-`x` equivalence, a generator `y` of the ambient
fiber is sent to the invariant `x = p.fiber.map V.hom y`. -/
theorem point_over_fiber_sigma_equiv_symm_fst
    (p : Point.{w} J)
    (V : Over U)
    (y : p.fiber.obj V.left) :
    ((point_over_fiber_sigma_equiv (U := U) p V).symm y).1 = p.fiber.map V.hom y := by
  -- This is the first coordinate built into `point_over_fiber_sigma_equiv.invFun`.
  rfl

/-- Helper for Lemma 7.35.3: under the split-by-`x` equivalence, the localized fiber element is
the canonical witness lying over `y`. -/
theorem point_over_fiber_sigma_equiv_symm_snd
    (p : Point.{w} J)
    (V : Over U)
    (y : p.fiber.obj V.left) :
    ((point_over_fiber_sigma_equiv (U := U) p V).symm y).2 =
      ⟨y, point_over_mem_of_eq (U := U) p rfl⟩ := by
  -- This is the second coordinate built into `point_over_fiber_sigma_equiv.invFun`.
  rfl


/-- Helper for Lemma 7.35.3: the actual `Type`-valued skyscraper sections over `V : C/U`
identify with the split-by-`x` family of localized skyscraper sections. -/
noncomputable def point_over_skyscraper_section_objEquiv
    (p : Point.{w} J)
    (V : Over U)
    (E : Type w) :
    (((Over.forget U).op ⋙ p.skyscraperPresheaf E).obj (op V)) ≃
      ∀ x : p.fiber.obj U, ((p.over x).skyscraperPresheaf E).obj (op V) :=
  (((Types.productIso (fun _ : p.fiber.obj V.left ↦ E)).toEquiv).trans
      (point_over_skyscraper_section_equiv (U := U) p V E)).trans
    (Equiv.piCongrRight fun x ↦
      ((Types.productIso (fun _ : (p.over x).fiber.obj V ↦ E)).toEquiv.symm))

/-- Helper for Lemma 7.35.3: the underlying value of the localized restriction map is the
expected restriction in the ambient fiber, with the subtype proof carried separately. -/
lemma fromOverFunctor_map_val
    (p : Point.{w} J) {x : p.fiber.obj U} {V W : Over U}
    (g : op V ⟶ op W) (y : p.fiber.obj W.left) (hy : p.fiber.map W.hom y = x) :
    (((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop
        ⟨y, point_over_mem_of_eq (U := U) p hy⟩).1) =
      p.fiber.map g.unop.left y := by
  -- The localized map is defined by the subfunctor structure, so its value is definitionally the
  -- ambient restriction map.
  rfl

/-- Helper for Lemma 7.35.3: after projecting to a fixed localized point `⟨y, hy⟩`, the
split-by-`x` section equivalence commutes with restriction maps. -/
theorem point_over_skyscraper_section_objEquiv_naturality_apply
    (p : Point.{w} J)
    (E : Type w)
    {V W : Over U}
    (g : op V ⟶ op W)
    (s : (((Over.forget U).op ⋙ p.skyscraperPresheaf E).obj (op V)))
    (x : p.fiber.obj U)
    (y : p.fiber.obj W.left)
    (hy : p.fiber.map W.hom y = x) :
    Pi.π (fun _ : (p.over x).fiber.obj W ↦ E) ⟨y, point_over_mem_of_eq (U := U) p hy⟩
      ((point_over_skyscraper_section_objEquiv (U := U) p W E
        ((((Over.forget U).op ⋙ p.skyscraperPresheaf E).map g) s)) x) =
    Pi.π (fun _ : (p.over x).fiber.obj W ↦ E) ⟨y, point_over_mem_of_eq (U := U) p hy⟩
      (((p.over x).skyscraperPresheaf E).map g
        ((point_over_skyscraper_section_objEquiv (U := U) p V E s) x)) := by
  -- Route correction: first peel off the terminal product isomorphism, then compare both sides
  -- through the common ambient projection indexed by `p.fiber.map g.unop.left y`.
  let t : (p.over x).fiber.obj W → E :=
    ((point_over_skyscraper_section_equiv (U := U) p W E)
      (((Types.productIso (fun _ : p.fiber.obj W.left ↦ E)).hom)
        ((((Over.forget U).op ⋙ p.skyscraperPresheaf E).map g) s))) x
  let yOver : (p.over x).fiber.obj W := ⟨y, point_over_mem_of_eq (U := U) p hy⟩
  have h_left :
      Pi.π (fun _ : (p.over x).fiber.obj W ↦ E) yOver
        ((point_over_skyscraper_section_objEquiv (U := U) p W E
          ((((Over.forget U).op ⋙ p.skyscraperPresheaf E).map g) s)) x) =
      Pi.π (fun _ : p.fiber.obj V.left ↦ E) (p.fiber.map g.unop.left y) s := by
    -- The left branch is the ambient restriction evaluated at `y`.
    have hproj :
        Pi.π (fun _ : (p.over x).fiber.obj W ↦ E) yOver
          (((Types.productIso (fun _ : (p.over x).fiber.obj W ↦ E)).inv) t) =
        t yOver := by
      simp
    have h_eval : t yOver = Pi.π (fun _ : p.fiber.obj V.left ↦ E) (p.fiber.map g.unop.left y) s := by
      -- Unfold the source-side restriction and rewrite the product map by `Pi.map'_comp_π`.
      change ((Types.productIso (fun _ : p.fiber.obj W.left ↦ E)).hom
          ((((Over.forget U).op ⋙ p.skyscraperPresheaf E).map g) s)) y = _
      simp only [Functor.op_obj, Functor.comp_map, Functor.op_map,
        Over.forget_map, Point.skyscraperPresheafFunctor_obj_map, Quiver.Hom.unop_op,
        Types.productIso_hom_comp_eval_apply]
      change (Pi.map' (p.fiber.map g.unop.left) (fun _ ↦ 𝟙 E) ≫
          Pi.π (fun _ : p.fiber.obj W.left ↦ E) y) s = _
      rw [Pi.map'_comp_π]
      simp
    calc
      Pi.π (fun _ : (p.over x).fiber.obj W ↦ E) yOver
          ((point_over_skyscraper_section_objEquiv (U := U) p W E
            ((((Over.forget U).op ⋙ p.skyscraperPresheaf E).map g) s)) x)
        = Pi.π (fun _ : (p.over x).fiber.obj W ↦ E) yOver
            (((Types.productIso (fun _ : (p.over x).fiber.obj W ↦ E)).inv) t) := by
              rfl
      _ = t yOver := hproj
      _ = Pi.π (fun _ : p.fiber.obj V.left ↦ E) (p.fiber.map g.unop.left y) s := h_eval
  have h_right :
      Pi.π (fun _ : (p.over x).fiber.obj W ↦ E) yOver
        (((p.over x).skyscraperPresheaf E).map g
          ((point_over_skyscraper_section_objEquiv (U := U) p V E s) x)) =
      Pi.π (fun _ : p.fiber.obj V.left ↦ E) (p.fiber.map g.unop.left y) s := by
    -- The right branch first restricts in the localized skyscraper, then projects at the mapped
    -- localized point.
    let hmor :
        Pi.map' ((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) (fun _ ↦ 𝟙 E) ≫
          Pi.π (fun _ : (p.over x).fiber.obj W ↦ E) yOver =
        Pi.π (fun _ : (p.over x).fiber.obj V ↦ E)
          (((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) yOver) ≫ 𝟙 E :=
      Pi.map'_comp_π (f := fun _ : (p.over x).fiber.obj V ↦ E)
        (g := fun _ : (p.over x).fiber.obj W ↦ E)
        ((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) (fun _ ↦ 𝟙 E) yOver
    have hmap :
        (((p.over x).skyscraperPresheaf E).map g ≫
            Pi.π (fun _ : (p.over x).fiber.obj W ↦ E) yOver)
          (((point_over_skyscraper_section_objEquiv (U := U) p V E s) x)) =
        Pi.π (fun _ : (p.over x).fiber.obj V ↦ E)
            (((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) yOver)
          (((point_over_skyscraper_section_objEquiv (U := U) p V E s) x)) := by
      simpa [Point.over_fiber, Functor.op_obj, Functor.comp_map, Functor.op_map,
        Over.forget_map, Point.skyscraperPresheafFunctor_obj_map, Quiver.Hom.unop_op] using
        congr_fun hmor (((point_over_skyscraper_section_objEquiv (U := U) p V E s) x))
    let t' : (p.over x).fiber.obj V → E :=
      ((point_over_skyscraper_section_equiv (U := U) p V E)
        (((Types.productIso (fun _ : p.fiber.obj V.left ↦ E)).hom) s)) x
    have hproj' :
        Pi.π (fun _ : (p.over x).fiber.obj V ↦ E)
            (((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) yOver)
            (((Types.productIso (fun _ : (p.over x).fiber.obj V ↦ E)).inv) t') =
        t' (((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) yOver) := by
      simp
    have h_eval' :
        t' (((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) yOver) =
          Pi.π (fun _ : p.fiber.obj V.left ↦ E) (p.fiber.map g.unop.left y) s := by
      -- The projection index on the localized side reduces to the ambient restriction index.
      change ((Types.productIso (fun _ : p.fiber.obj V.left ↦ E)).hom s)
          ((((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) yOver).1) = _
      have hval : ((((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) yOver).1) =
          p.fiber.map g.unop.left y := by
        rfl
      rw [hval]
      simp [Types.productIso_hom_comp_eval_apply]
    calc
      Pi.π (fun _ : (p.over x).fiber.obj W ↦ E) yOver
          (((p.over x).skyscraperPresheaf E).map g
            ((point_over_skyscraper_section_objEquiv (U := U) p V E s) x))
        = (((p.over x).skyscraperPresheaf E).map g ≫
              Pi.π (fun _ : (p.over x).fiber.obj W ↦ E) yOver)
            (((point_over_skyscraper_section_objEquiv (U := U) p V E s) x)) := by
              rfl
      _ = Pi.π (fun _ : (p.over x).fiber.obj V ↦ E)
            (((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) yOver)
            (((point_over_skyscraper_section_objEquiv (U := U) p V E s) x)) := hmap
      _ = Pi.π (fun _ : (p.over x).fiber.obj V ↦ E)
            (((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) yOver)
            (((Types.productIso (fun _ : (p.over x).fiber.obj V ↦ E)).inv) t') := by
              rfl
      _ = t' (((FunctorToTypes.fromOverFunctor p.fiber x).map g.unop) yOver) := hproj'
      _ = Pi.π (fun _ : p.fiber.obj V.left ↦ E) (p.fiber.map g.unop.left y) s := h_eval'
  exact h_left.trans h_right.symm

/-- Helper for Lemma 7.35.3: the sectionwise split-by-`x` equivalence is natural in the slice
object `V`, so the source proof's decomposition becomes an honest presheaf comparison. -/
theorem point_over_skyscraper_section_objEquiv_naturality
    (p : Point.{w} J)
    (E : Type w)
    {V W : Over U}
  (g : op V ⟶ op W)
  (s : (((Over.forget U).op ⋙ p.skyscraperPresheaf E).obj (op V))) :
    point_over_skyscraper_section_objEquiv (U := U) p W E
        ((((Over.forget U).op ⋙ p.skyscraperPresheaf E).map g) s) =
      fun x =>
        ((p.over x).skyscraperPresheaf E).map g
          ((point_over_skyscraper_section_objEquiv (U := U) p V E s) x) := by
  -- We compare the two product-valued sections coordinatewise on each localized point over `x`.
  funext x
  apply Types.limit_ext
  intro y
  cases y with
  | mk y =>
      exact point_over_skyscraper_section_objEquiv_naturality_apply (U := U) p E g s x y.1
        (point_over_eq_of_mem (U := U) p y.2)

/-- Helper for Lemma 7.35.3: the pulled-back skyscraper presheaf is compared with the explicit
family `x ↦ (p.over x).skyscraperPresheaf E`, equipped with pointwise restriction maps. -/
noncomputable def point_over_skyscraper_family
    (p : Point.{w} J)
    (E : Type w) :
    (Over U)ᵒᵖ ⥤ Type w where
  obj V := ∀ x : p.fiber.obj U, ((p.over x).skyscraperPresheaf E).obj V
  map g t := fun x => ((p.over x).skyscraperPresheaf E).map g (t x)
  map_id V := by
    -- Restriction in the family presheaf is pointwise in `x`.
    funext t x
    simp
  map_comp g h := by
    -- Composition is inherited pointwise from each localized skyscraper presheaf.
    funext t x
    simp

/-- Helper for Lemma 7.35.3: the source proof's sectionwise decomposition upgrades to a literal
presheaf isomorphism after the naturality check above is recorded once. -/
noncomputable def localization_point_skyscraper_presheafIso_forall_pointOver
    (p : Point.{w} J)
    (E : Type w) :
    ((Over.forget U).op ⋙ p.skyscraperPresheaf E) ≅
      point_over_skyscraper_family (U := U) p E := by
  refine NatIso.ofComponents
    (fun V ↦ (point_over_skyscraper_section_objEquiv (U := U) p V.unop E).toIso) ?_
  intro V W g
  -- The componentwise equivalences commute with restriction by the naturality theorem above.
  funext s
  exact point_over_skyscraper_section_objEquiv_naturality (U := U) p E g s

/-- Helper for Lemma 7.35.3: morphisms into the explicit family presheaf are exactly families of
localized skyscraper morphisms indexed by `x : p.fiber.obj U`. -/
noncomputable def point_over_skyscraper_family_homEquiv
    (p : Point.{w} J)
    (P : (Over U)ᵒᵖ ⥤ Type w)
    (E : Type w) :
    (P ⟶ point_over_skyscraper_family (U := U) p E) ≃
      ∀ x : p.fiber.obj U, P ⟶ (p.over x).skyscraperPresheaf E where
  toFun α x :=
    { app := fun V t => α.app V t x
      naturality := by
        intro V W g
        ext t
        exact congrFun (congrArg (fun f => f t) (α.naturality g)) x }
  invFun α :=
    { app := fun V t x => (α x).app V t
      naturality := by
        intro V W g
        funext t x
        exact congrFun ((α x).naturality g) t }
  left_inv α := by
    -- Reading a family morphism componentwise and reassembling it changes nothing.
    ext V t
    rfl
  right_inv α := by
    -- Reassembling a family and then projecting back to each `x` is definitionally the identity.
    funext x
    ext V t
    rfl

/-- Helper for Lemma 7.35.3: after rewriting skyscraper sections through `Types.productIso`, maps
to the pulled-back skyscraper presheaf should split into `x`-indexed localized maps. -/
noncomputable def localization_point_skyscraper_presheafHomEquiv_forall_pointOver
    (p : Point.{w} J)
    (P : (Over U)ᵒᵖ ⥤ Type w)
    (E : Type w) :
    (P ⟶ ((Over.forget U).op ⋙ p.skyscraperPresheaf E)) ≃
      ∀ x : p.fiber.obj U, P ⟶ (p.over x).skyscraperPresheaf E := by
  let e := localization_point_skyscraper_presheafIso_forall_pointOver (U := U) p E
  -- First transport morphisms to the explicit family presheaf, then read them pointwise in `x`.
  exact ((Iso.refl P).homCongr e).trans (point_over_skyscraper_family_homEquiv (U := U) p P E)

/-- Helper for Lemma 7.35.3: whiskering a skyscraper-presheaf map along `(Over.forget U).op`
gives the coefficient-change map on the pulled-back skyscraper presheaf. -/
noncomputable def localization_point_skyscraper_presheaf_postcompose
    (p : Point.{w} J)
    {E E' : Type w}
    (g : E ⟶ E') :
    ((Over.forget U).op ⋙ p.skyscraperPresheaf E) ⟶
      ((Over.forget U).op ⋙ p.skyscraperPresheaf E') :=
  ((Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ (Type w)).obj (Over.forget U).op).map
    (p.skyscraperPresheafFunctor.map g)

/-- Helper for Lemma 7.35.3: evaluating the split-by-`x` section equivalence at a localized point
recovers the original ambient section value at the underlying point. -/
theorem point_over_skyscraper_section_objEquiv_apply
    (p : Point.{w} J)
    (V : Over U)
    (E : Type w)
    (s : (((Over.forget U).op ⋙ p.skyscraperPresheaf E).obj (op V)))
    (x : p.fiber.obj U)
    (y : p.fiber.obj V.left)
    (hy : p.fiber.map V.hom y = x) :
    Pi.π (fun _ : (p.over x).fiber.obj V ↦ E) ⟨y, point_over_mem_of_eq (U := U) p hy⟩
      ((point_over_skyscraper_section_objEquiv (U := U) p V E s) x) =
    Pi.π (fun _ : p.fiber.obj V.left ↦ E) y s := by
  let t : (p.over x).fiber.obj V → E :=
    ((point_over_skyscraper_section_equiv (U := U) p V E)
      (((Types.productIso (fun _ : p.fiber.obj V.left ↦ E)).hom) s)) x
  let yOver : (p.over x).fiber.obj V := ⟨y, point_over_mem_of_eq (U := U) p hy⟩
  have hproj :
      Pi.π (fun _ : (p.over x).fiber.obj V ↦ E) yOver
        (((Types.productIso (fun _ : (p.over x).fiber.obj V ↦ E)).inv) t) =
      t yOver := by
    simp
  have h_eval :
      t yOver = Pi.π (fun _ : p.fiber.obj V.left ↦ E) y s := by
    change ((Types.productIso (fun _ : p.fiber.obj V.left ↦ E)).hom s) y = _
    simp
  calc
    Pi.π (fun _ : (p.over x).fiber.obj V ↦ E) yOver
        ((point_over_skyscraper_section_objEquiv (U := U) p V E s) x)
      = Pi.π (fun _ : (p.over x).fiber.obj V ↦ E) yOver
          (((Types.productIso (fun _ : (p.over x).fiber.obj V ↦ E)).inv) t) := by
            rfl
    _ = t yOver := hproj
    _ = Pi.π (fun _ : p.fiber.obj V.left ↦ E) y s := h_eval

/-- Helper for Lemma 7.35.3: on each slice object `V`, the sectionwise split-by-`x` comparison is
compatible with postcomposition by a map of coefficient sets. -/
theorem point_over_skyscraper_section_objEquiv_naturality_right
    (p : Point.{w} J)
    (V : Over U)
    {E E' : Type w}
    (s : (((Over.forget U).op ⋙ p.skyscraperPresheaf E).obj (op V)))
    (g : E ⟶ E') :
    point_over_skyscraper_section_objEquiv (U := U) p V E'
        (((p.skyscraperPresheafFunctor.map g).app (op V.left)) s) =
      fun x ↦
        ((p.over x).skyscraperPresheafFunctor.map g).app (op V)
          ((point_over_skyscraper_section_objEquiv (U := U) p V E s) x) := by
  -- Project to each localized point over `x`; both branches reduce to applying `g` to the same
  -- ambient section value.
  funext x
  apply Types.limit_ext
  intro y
  cases y with
  | mk y =>
      have h_left :
          Pi.π (fun _ : (p.over x).fiber.obj V ↦ E') y
            ((point_over_skyscraper_section_objEquiv (U := U) p V E'
              (((p.skyscraperPresheafFunctor.map g).app (op V.left)) s)) x) =
          g (Pi.π (fun _ : p.fiber.obj V.left ↦ E) y.1 s) := by
        simpa [Point.skyscraperPresheafFunctor_obj_map] using
          point_over_skyscraper_section_objEquiv_apply (U := U) p V E'
            (((p.skyscraperPresheafFunctor.map g).app (op V.left)) s) x y.1
            (point_over_eq_of_mem (U := U) p y.2)
      have h_right :
          Pi.π (fun _ : (p.over x).fiber.obj V ↦ E') y
            (((p.over x).skyscraperPresheafFunctor.map g).app (op V)
              ((point_over_skyscraper_section_objEquiv (U := U) p V E s) x)) =
          g (Pi.π (fun _ : p.fiber.obj V.left ↦ E) y.1 s) := by
        rw [show
          Pi.π (fun _ : (p.over x).fiber.obj V ↦ E') y
              (((p.over x).skyscraperPresheafFunctor.map g).app (op V)
                ((point_over_skyscraper_section_objEquiv (U := U) p V E s) x)) =
            g (Pi.π (fun _ : (p.over x).fiber.obj V ↦ E) y
              ((point_over_skyscraper_section_objEquiv (U := U) p V E s) x)) by
              simp]
        simpa using
          congrArg g
            (point_over_skyscraper_section_objEquiv_apply (U := U) p V E s x y.1
              (point_over_eq_of_mem (U := U) p y.2))
      exact h_left.trans h_right.symm

/-- Helper for Lemma 7.35.3: morphisms into the pulled-back skyscraper presheaf respect
postcomposition by a map of coefficient sets after splitting the source by `x`. -/
theorem localization_point_skyscraper_presheafHomEquiv_forall_pointOver_naturality_right
    (p : Point.{w} J)
    (P : (Over U)ᵒᵖ ⥤ Type w)
    {E E' : Type w}
    (α : P ⟶ ((Over.forget U).op ⋙ p.skyscraperPresheaf E))
    (g : E ⟶ E') :
    localization_point_skyscraper_presheafHomEquiv_forall_pointOver (U := U) p P E'
        (α ≫ localization_point_skyscraper_presheaf_postcompose (U := U) p g) =
      fun x ↦
        localization_point_skyscraper_presheafHomEquiv_forall_pointOver (U := U) p P E α x ≫
          (p.over x).skyscraperPresheafFunctor.map g := by
  -- Unpack the Hom-equivalence at each object `V`; after that the comparison is exactly the
  -- sectionwise naturality from the previous lemma.
  funext x
  ext V t
  simpa [localization_point_skyscraper_presheafHomEquiv_forall_pointOver,
    localization_point_skyscraper_presheafIso_forall_pointOver,
    point_over_skyscraper_family_homEquiv, localization_point_skyscraper_presheaf_postcompose,
    point_over_skyscraper_family] using
    congrFun
      (point_over_skyscraper_section_objEquiv_naturality_right
        (U := U) p V.unop (α.app V t) g) x

/-- Helper for Lemma 7.35.3: the Hom-sets out of the presheaf fiber of the left Kan extension
split by `x : p.fiber.obj U`, exactly matching the source proof's decomposition of generators by
their image in `u(U)`. -/
noncomputable def localization_leftKanExtension_presheafFiber_homEquiv_forall_pointOver
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    (E : Type w)
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F] :
    (p.presheafFiber.obj ((Over.forget U).op.lan.obj 𝒢.1) ⟶ E) ≃
      ∀ x : p.fiber.obj U, (p.over x).presheafFiber.obj 𝒢.1 ⟶ E := by
  let e₁ :
      (p.presheafFiber.obj ((Over.forget U).op.lan.obj 𝒢.1) ⟶ E) ≃
        (((Over.forget U).op.lan.obj 𝒢.1) ⟶ p.skyscraperPresheaf E) :=
    p.skyscraperPresheafAdjunction.homEquiv _ _
  let e₂ :
      (((Over.forget U).op.lan.obj 𝒢.1) ⟶ p.skyscraperPresheaf E) ≃
        (𝒢.1 ⟶ ((Over.forget U).op ⋙ p.skyscraperPresheaf E)) :=
    ((Over.forget U).op.lanAdjunction (Type w)).homEquiv _ _
  let e₃ :
      (𝒢.1 ⟶ ((Over.forget U).op ⋙ p.skyscraperPresheaf E)) ≃
        ∀ x : p.fiber.obj U, 𝒢.1 ⟶ (p.over x).skyscraperPresheaf E :=
    localization_point_skyscraper_presheafHomEquiv_forall_pointOver (U := U) p 𝒢.1 E
  let e₄ :
      (∀ x : p.fiber.obj U, 𝒢.1 ⟶ (p.over x).skyscraperPresheaf E) ≃
        ∀ x : p.fiber.obj U, (p.over x).presheafFiber.obj 𝒢.1 ⟶ E :=
    Equiv.piCongrRight fun x ↦ ((p.over x).skyscraperPresheafAdjunction.homEquiv 𝒢.1 E).symm
  -- The Hom-level source proof is the composite of the stalk/skyscraper adjunction, the Kan
  -- adjunction, the split of the pulled-back skyscraper by `x`, and the localized stalk adjunctions.
  exact e₁.trans <| e₂.trans <| e₃.trans e₄

/-- Helper for Lemma 7.35.3: the Hom-level split of the left Kan extension is natural in the
target set `E`. -/
theorem localization_leftKanExtension_presheafFiber_homEquiv_forall_pointOver_naturality_right
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    {E E' : Type w}
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    (f : p.presheafFiber.obj ((Over.forget U).op.lan.obj 𝒢.1) ⟶ E)
    (g : E ⟶ E') :
    localization_leftKanExtension_presheafFiber_homEquiv_forall_pointOver
        (U := U) p 𝒢 E' (f ≫ g) =
      fun x ↦
        localization_leftKanExtension_presheafFiber_homEquiv_forall_pointOver
          (U := U) p 𝒢 E f x ≫ g := by
  let e₁ :
      (p.presheafFiber.obj ((Over.forget U).op.lan.obj 𝒢.1) ⟶ E) ≃
        (((Over.forget U).op.lan.obj 𝒢.1) ⟶ p.skyscraperPresheaf E) :=
    p.skyscraperPresheafAdjunction.homEquiv _ _
  let e₁' :
      (p.presheafFiber.obj ((Over.forget U).op.lan.obj 𝒢.1) ⟶ E') ≃
        (((Over.forget U).op.lan.obj 𝒢.1) ⟶ p.skyscraperPresheaf E') :=
    p.skyscraperPresheafAdjunction.homEquiv _ _
  let e₂ :
      (((Over.forget U).op.lan.obj 𝒢.1) ⟶ p.skyscraperPresheaf E) ≃
        (𝒢.1 ⟶ ((Over.forget U).op ⋙ p.skyscraperPresheaf E)) :=
    ((Over.forget U).op.lanAdjunction (Type w)).homEquiv _ _
  let e₂' :
      (((Over.forget U).op.lan.obj 𝒢.1) ⟶ p.skyscraperPresheaf E') ≃
        (𝒢.1 ⟶ ((Over.forget U).op ⋙ p.skyscraperPresheaf E')) :=
    ((Over.forget U).op.lanAdjunction (Type w)).homEquiv _ _
  let e₃ :
      (𝒢.1 ⟶ ((Over.forget U).op ⋙ p.skyscraperPresheaf E)) ≃
        ∀ x : p.fiber.obj U, 𝒢.1 ⟶ (p.over x).skyscraperPresheaf E :=
    localization_point_skyscraper_presheafHomEquiv_forall_pointOver (U := U) p 𝒢.1 E
  let e₃' :
      (𝒢.1 ⟶ ((Over.forget U).op ⋙ p.skyscraperPresheaf E')) ≃
        ∀ x : p.fiber.obj U, 𝒢.1 ⟶ (p.over x).skyscraperPresheaf E' :=
    localization_point_skyscraper_presheafHomEquiv_forall_pointOver (U := U) p 𝒢.1 E'
  let e₄ :
      (∀ x : p.fiber.obj U, 𝒢.1 ⟶ (p.over x).skyscraperPresheaf E) ≃
        ∀ x : p.fiber.obj U, (p.over x).presheafFiber.obj 𝒢.1 ⟶ E :=
    Equiv.piCongrRight fun x ↦ ((p.over x).skyscraperPresheafAdjunction.homEquiv 𝒢.1 E).symm
  let e₄' :
      (∀ x : p.fiber.obj U, 𝒢.1 ⟶ (p.over x).skyscraperPresheaf E') ≃
        ∀ x : p.fiber.obj U, (p.over x).presheafFiber.obj 𝒢.1 ⟶ E' :=
    Equiv.piCongrRight fun x ↦ ((p.over x).skyscraperPresheafAdjunction.homEquiv 𝒢.1 E').symm
  have h₁ :
      e₁' (f ≫ g) = e₁ f ≫ p.skyscraperPresheafFunctor.map g := by
    simpa [e₁, e₁'] using (p.skyscraperPresheafAdjunction.homEquiv_naturality_right f g)
  have h₂ :
      e₂' (e₁' (f ≫ g)) =
        e₂ (e₁ f) ≫ localization_point_skyscraper_presheaf_postcompose (U := U) p g := by
    rw [h₁]
    simpa [e₂, e₂', localization_point_skyscraper_presheaf_postcompose] using
      (((Over.forget U).op.lanAdjunction (Type w)).homEquiv_naturality_right
        (e₁ f) (p.skyscraperPresheafFunctor.map g))
  have h₃ :
      e₃' (e₂' (e₁' (f ≫ g))) =
        fun x ↦ e₃ (e₂ (e₁ f)) x ≫ (p.over x).skyscraperPresheafFunctor.map g := by
    rw [h₂]
    simpa [e₃, e₃'] using
      localization_point_skyscraper_presheafHomEquiv_forall_pointOver_naturality_right
        (U := U) p 𝒢.1 (e₂ (e₁ f)) g
  have h₄ :
      e₄' (e₃' (e₂' (e₁' (f ≫ g)))) =
        fun x ↦ e₄ (e₃ (e₂ (e₁ f))) x ≫ g := by
    rw [h₃]
    funext x
    simpa [e₄, e₄'] using
      (((p.over x).skyscraperPresheafAdjunction).homEquiv_naturality_right_symm
        (e₃ (e₂ (e₁ f)) x) g)
  -- Reassemble the stagewise naturality into the composite Hom-equivalence.
  simpa [localization_leftKanExtension_presheafFiber_homEquiv_forall_pointOver, e₁, e₁', e₂, e₂',
    e₃, e₃', e₄, e₄'] using h₄

/-- Helper for Lemma 7.35.3: functions out of the sigma coproduct of localized presheaf fibers are
the same as `x`-indexed families of functions out of each localized presheaf fiber. -/
noncomputable def sigma_pointOver_presheafFiber_sectionsEquiv
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    (E : Type w) :
    ((Σ x : p.fiber.obj U, (p.over x).presheafFiber.obj 𝒢.1) ⟶ E) ≃
      ∀ x : p.fiber.obj U, (p.over x).presheafFiber.obj 𝒢.1 ⟶ E where
  toFun f x y := f ⟨x, y⟩
  invFun f z := f z.1 z.2
  left_inv f := by
    funext z
    cases z
    rfl
  right_inv f := by
    funext x y
    rfl

/-- Helper for Lemma 7.35.3: after currying functions out of the sigma coproduct, the resulting
family description is natural in the target set `E`. -/
theorem sigma_pointOver_presheafFiber_sectionsEquiv_symm_naturality_right
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    {E E' : Type w}
    (f : ∀ x : p.fiber.obj U, (p.over x).presheafFiber.obj 𝒢.1 ⟶ E)
    (g : E ⟶ E') :
    (sigma_pointOver_presheafFiber_sectionsEquiv (U := U) p 𝒢 E').symm
        (fun x ↦ f x ≫ g) =
      (sigma_pointOver_presheafFiber_sectionsEquiv (U := U) p 𝒢 E).symm f ≫ g := by
  funext z
  cases z
  rfl

/-- Helper for Lemma 7.35.3: the source-proof decomposition of the left Kan-extension stalk
upgrades to an actual coproduct isomorphism after currying the sigma family. -/
noncomputable def
    localization_leftKanExtension_presheafFiberIsoSigma_pointOver_presheafFiber
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type w)]
    [HasWeakSheafify J (Type w)] :
    p.presheafFiber.obj ((Over.forget U).op.lan.obj 𝒢.1) ≅
      (Σ x : p.fiber.obj U, (p.over x).presheafFiber.obj 𝒢.1) := by
  let e := localization_leftKanExtension_presheafFiber_homEquiv_forall_pointOver (U := U) p 𝒢
  let q :
      ∀ E : Type w,
        (p.presheafFiber.obj ((Over.forget U).op.lan.obj 𝒢.1) ⟶ E) ≃
          ((Σ x : p.fiber.obj U, (p.over x).presheafFiber.obj 𝒢.1) ⟶ E) :=
    fun E ↦ (e E).trans (sigma_pointOver_presheafFiber_sectionsEquiv (U := U) p 𝒢 E).symm
  -- Co-Yoneda packages the natural Hom-equivalence into the desired isomorphism of sets.
  exact
    (Coyoneda.ext
      (Σ x : p.fiber.obj U, (p.over x).presheafFiber.obj 𝒢.1)
      (p.presheafFiber.obj ((Over.forget U).op.lan.obj 𝒢.1))
      (fun {E} f ↦ (q E).symm f)
      (fun {E} f ↦ q E f)
      (fun {E} f ↦ (q E).right_inv f)
      (fun {E} f ↦ (q E).left_inv f)
      (fun {E E'} f g ↦ by
        dsimp [q]
        rw [localization_leftKanExtension_presheafFiber_homEquiv_forall_pointOver_naturality_right
          (U := U) p 𝒢 f g]
        simpa [q] using
          sigma_pointOver_presheafFiber_sectionsEquiv_symm_naturality_right
            (U := U) p 𝒢
            (localization_leftKanExtension_presheafFiber_homEquiv_forall_pointOver
              (U := U) p 𝒢 E f)
            g)).symm

/-- Helper for Lemma 7.35.3: after passing through the fully faithful forgetful functor from
sheaves to presheaves, the split-by-`x` comparison on pulled-back skyscraper sections becomes a
Hom-set equivalence of sheaves. -/
noncomputable def localization_point_skyscraper_homEquiv_forall_pointOver
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    (E : Type w) :
    (𝒢 ⟶ ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).obj
        (p.skyscraperSheafFunctor.obj E)) ≃
      ∀ x : p.fiber.obj U, 𝒢 ⟶ (p.over x).skyscraperSheafFunctor.obj E := by
  let e₁ :
      (𝒢 ⟶ ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).obj
          (p.skyscraperSheafFunctor.obj E)) ≃
        (𝒢.1 ⟶ (((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).obj
          (p.skyscraperSheafFunctor.obj E)).1) := by
    simpa using
      ((fullyFaithfulSheafToPresheaf (J.over U) (Type w)).homEquiv
        (X := 𝒢)
        (Y := ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).obj
          (p.skyscraperSheafFunctor.obj E)))
  let e₂ :
      (𝒢.1 ⟶ (((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).obj
          (p.skyscraperSheafFunctor.obj E)).1) ≃
        (𝒢.1 ⟶ ((Over.forget U).op ⋙ p.skyscraperPresheaf E)) :=
    (Iso.refl 𝒢.1).homCongr
      (((Over.forget U).sheafPushforwardContinuousCompSheafToPresheafIso
          (Type w) (J.over U) J).app (p.skyscraperSheafFunctor.obj E))
  -- Conjugate the presheaf-level split by the fully faithful forgetful functor and the owner
  -- comparison `sheafPushforwardContinuousCompSheafToPresheafIso`.
  exact e₁.trans <|
    e₂.trans <|
      (localization_point_skyscraper_presheafHomEquiv_forall_pointOver (U := U) p 𝒢.1 E).trans <|
        Equiv.piCongrRight fun x ↦ by
          simpa using
            (((fullyFaithfulSheafToPresheaf (J.over U) (Type w)).homEquiv
              (X := 𝒢)
              (Y := (p.over x).skyscraperSheafFunctor.obj E)).symm)

/-- Helper for Lemma 7.35.3: the sheaf-level split of pulled-back skyscraper morphisms is
compatible with postcomposition by a map of coefficient sets. -/
theorem localization_point_skyscraper_homEquiv_forall_pointOver_naturality_right
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    {E E' : Type w}
    (α : 𝒢 ⟶ ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).obj
      (p.skyscraperSheafFunctor.obj E))
    (g : E ⟶ E') :
    localization_point_skyscraper_homEquiv_forall_pointOver (U := U) p 𝒢 E'
        (α ≫ ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).map
          (p.skyscraperSheafFunctor.map g)) =
      fun x ↦
        localization_point_skyscraper_homEquiv_forall_pointOver (U := U) p 𝒢 E α x ≫
          (p.over x).skyscraperSheafFunctor.map g := by
  let α' :
      𝒢.1 ⟶ ((Over.forget U).op ⋙ p.skyscraperPresheaf E) :=
    (((fullyFaithfulSheafToPresheaf (J.over U) (Type w)).homEquiv
      (X := 𝒢)
      (Y := ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).obj
        (p.skyscraperSheafFunctor.obj E))) α) ≫
      (((Over.forget U).sheafPushforwardContinuousCompSheafToPresheafIso
        (Type w) (J.over U) J).app (p.skyscraperSheafFunctor.obj E)).hom
  -- Compare the underlying presheaf maps; the fully faithful forgetful functor then upgrades the
  -- result back to sheaves.
  funext x
  ext V t
  have h :=
    congrFun
      (localization_point_skyscraper_presheafHomEquiv_forall_pointOver_naturality_right
        (U := U) p 𝒢.1 α' g) x
  simpa [localization_point_skyscraper_homEquiv_forall_pointOver, α',
    localization_point_skyscraper_presheaf_postcompose] using
    congrArg (fun η => η.app V t) h

/-- Helper for Lemma 7.35.3: the source-proof coproduct over `x : p.fiber.obj U` is recorded as
an explicit `Type`-valued functor on sheaves over `C/U`. -/
noncomputable def sigma_pointOver_sheafFiber_functor
    (p : Point.{w} J) :
    Sheaf (J.over U) (Type w) ⥤ Type w where
  obj 𝒢 := Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢
  map f := fun z ↦ ⟨z.1, (p.over z.1).sheafFiber.map f z.2⟩
  map_id 𝒢 := by
    -- The sigma-valued functor acts componentwise on each localized stalk.
    funext z
    cases z
    simp
  map_comp f g := by
    -- Composition is inherited componentwise from the localized stalk functors.
    funext z
    cases z
    simp

/-- Helper for Lemma 7.35.3: functions out of the sigma-valued coproduct are equivalent to the
same split family of skyscraper morphisms that already realizes the source proof. -/
noncomputable def sigma_pointOver_sheafFiber_sectionsEquiv
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    (E : Type w) :
    (((sigma_pointOver_sheafFiber_functor (U := U) p).obj 𝒢) → E) ≃
      (∀ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢 → E) where
  toFun f x y := f ⟨x, y⟩
  invFun f z := f z.1 z.2
  left_inv f := by
    -- Re-currying a function on the sigma coproduct changes nothing.
    funext z
    cases z
    rfl
  right_inv f := by
    -- Splitting and then reassembling the family is definitionally the identity.
    funext x y
    rfl

/-- Helper for Lemma 7.35.3: currying functions out of the sigma coproduct of localized sheaf
fibers is natural in the target coefficient set. -/
theorem sigma_pointOver_sheafFiber_sectionsEquiv_symm_naturality_right
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    {E E' : Type w}
    (f : ∀ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢 → E)
    (g : E ⟶ E') :
    (sigma_pointOver_sheafFiber_sectionsEquiv (U := U) p 𝒢 E').symm
        (fun x ↦ f x ≫ g) =
      (sigma_pointOver_sheafFiber_sectionsEquiv (U := U) p 𝒢 E).symm f ≫ g := by
  funext z
  cases z
  rfl

/-- Helper for Lemma 7.35.3: functions out of the sigma-valued coproduct are equivalent to the
same split family of skyscraper morphisms that already realizes the source proof. -/
noncomputable def sigma_pointOver_sheafFiber_homEquiv
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    (E : Type w) :
    (((sigma_pointOver_sheafFiber_functor (U := U) p).obj 𝒢) → E) ≃
      (𝒢 ⟶ ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).obj
        (p.skyscraperSheafFunctor.obj E)) :=
  let pointwiseAdjunctionEquiv :
      (∀ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢 → E) ≃
        (∀ x : p.fiber.obj U, 𝒢 ⟶ (p.over x).skyscraperSheafFunctor.obj E) :=
    Equiv.piCongrRight fun x ↦
      show ((p.over x).sheafFiber.obj 𝒢 → E) ≃
          (𝒢 ⟶ (p.over x).skyscraperSheafFunctor.obj E) from
        (p.over x).skyscraperSheafAdjunction.homEquiv 𝒢 E
  -- First curry maps out of the sigma-coproduct, then use the stalk/skyscraper adjunction at
  -- each localized point, and finally reassemble the family through the proved split sheaf-Hom
  -- equivalence.
  (sigma_pointOver_sheafFiber_sectionsEquiv (U := U) p 𝒢 E).trans <|
    pointwiseAdjunctionEquiv.trans <|
      (localization_point_skyscraper_homEquiv_forall_pointOver (U := U) p 𝒢 E).symm

/-- Helper for Lemma 7.35.3: the sigma-coproduct sheaf-fiber Hom-equivalence is natural in the
target coefficient set. -/
theorem sigma_pointOver_sheafFiber_homEquiv_symm_naturality_right
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    {E E' : Type w}
    (f : 𝒢 ⟶ ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).obj
      (p.skyscraperSheafFunctor.obj E))
    (g : E ⟶ E') :
    (sigma_pointOver_sheafFiber_homEquiv (U := U) p 𝒢 E').symm
        (f ≫ ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).map
          (p.skyscraperSheafFunctor.map g)) =
      (sigma_pointOver_sheafFiber_homEquiv (U := U) p 𝒢 E).symm f ≫ g := by
  let e₁ := localization_point_skyscraper_homEquiv_forall_pointOver (U := U) p 𝒢 E
  let e₁' := localization_point_skyscraper_homEquiv_forall_pointOver (U := U) p 𝒢 E'
  let e₂ :
      (∀ x : p.fiber.obj U, 𝒢 ⟶ (p.over x).skyscraperSheafFunctor.obj E) ≃
        (∀ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢 → E) :=
    Equiv.piCongrRight fun x ↦
      ((p.over x).skyscraperSheafAdjunction.homEquiv 𝒢 E).symm
  let e₂' :
      (∀ x : p.fiber.obj U, 𝒢 ⟶ (p.over x).skyscraperSheafFunctor.obj E') ≃
        (∀ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢 → E') :=
    Equiv.piCongrRight fun x ↦
      ((p.over x).skyscraperSheafAdjunction.homEquiv 𝒢 E').symm
  let e₃ := sigma_pointOver_sheafFiber_sectionsEquiv (U := U) p 𝒢 E
  let e₃' := sigma_pointOver_sheafFiber_sectionsEquiv (U := U) p 𝒢 E'
  have h₁ :
      e₁' (f ≫ ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).map
        (p.skyscraperSheafFunctor.map g)) =
        fun x ↦ e₁ f x ≫ (p.over x).skyscraperSheafFunctor.map g := by
    simpa [e₁, e₁'] using
      localization_point_skyscraper_homEquiv_forall_pointOver_naturality_right
        (U := U) p 𝒢 f g
  have h₂ :
      e₂' (e₁' (f ≫ ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).map
        (p.skyscraperSheafFunctor.map g))) =
        fun x ↦ e₂ (e₁ f) x ≫ g := by
    rw [h₁]
    funext x
    simpa [e₂, e₂'] using
      (((p.over x).skyscraperSheafAdjunction).homEquiv_naturality_right_symm
        (e₁ f x) g)
  have h₃ :
      e₃'.symm
          (e₂' (e₁' (f ≫ ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).map
            (p.skyscraperSheafFunctor.map g)))) =
        e₃.symm (e₂ (e₁ f)) ≫ g := by
    rw [h₂]
    simpa [e₃, e₃'] using
      sigma_pointOver_sheafFiber_sectionsEquiv_symm_naturality_right
        (U := U) p 𝒢 (e₂ (e₁ f)) g
  simpa [sigma_pointOver_sheafFiber_homEquiv, e₁, e₁', e₂, e₂', e₃, e₃'] using h₃

/-- Helper for Lemma 7.35.3: the Hom-sets out of the stalk of `j_{U!} 𝒢` are identified with the
Hom-sets out of the sigma coproduct of localized sheaf fibers. -/
noncomputable def localizationLowerShriek_sheafFiber_homEquiv_sigma_pointOver_sheafFiber
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    (E : Type w) :
    (p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢) → E) ≃
      ((Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢) → E) :=
  let e₁ := p.skyscraperSheafAdjunction.homEquiv
    (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢) E
  let e₂ := ((Over.forget U).sheafAdjunctionContinuous (Type w) (J.over U) J).homEquiv
    𝒢 (p.skyscraperSheafFunctor.obj E)
  e₁.trans <| e₂.trans <| (sigma_pointOver_sheafFiber_homEquiv (U := U) p 𝒢 E).symm

/-- Helper for Lemma 7.35.3: the final Hom-equivalence used to package the stalk decomposition is
natural in the target coefficient set. -/
theorem localizationLowerShriek_sheafFiber_homEquiv_sigma_pointOver_sheafFiber_naturality_right
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    {E E' : Type w}
    (f : p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢) → E)
    (g : E ⟶ E') :
    localizationLowerShriek_sheafFiber_homEquiv_sigma_pointOver_sheafFiber
        (U := U) p 𝒢 E' (f ≫ g) =
      localizationLowerShriek_sheafFiber_homEquiv_sigma_pointOver_sheafFiber
        (U := U) p 𝒢 E f ≫ g := by
  let e₁ := p.skyscraperSheafAdjunction.homEquiv
    (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢) E
  let e₁' := p.skyscraperSheafAdjunction.homEquiv
    (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢) E'
  let e₂ := ((Over.forget U).sheafAdjunctionContinuous (Type w) (J.over U) J).homEquiv
    𝒢 (p.skyscraperSheafFunctor.obj E)
  let e₂' := ((Over.forget U).sheafAdjunctionContinuous (Type w) (J.over U) J).homEquiv
    𝒢 (p.skyscraperSheafFunctor.obj E')
  let e₃ := (sigma_pointOver_sheafFiber_homEquiv (U := U) p 𝒢 E).symm
  let e₃' := (sigma_pointOver_sheafFiber_homEquiv (U := U) p 𝒢 E').symm
  have h₁ :
      e₁' (f ≫ g) = e₁ f ≫ p.skyscraperSheafFunctor.map g := by
    simpa [e₁, e₁'] using
      (p.skyscraperSheafAdjunction.homEquiv_naturality_right f g)
  have h₂ :
      e₂' (e₁' (f ≫ g)) =
        e₂ (e₁ f) ≫ ((Over.forget U).sheafPushforwardContinuous (Type w) (J.over U) J).map
          (p.skyscraperSheafFunctor.map g) := by
    rw [h₁]
    simpa [e₂, e₂'] using
      (((Over.forget U).sheafAdjunctionContinuous (Type w) (J.over U) J).homEquiv_naturality_right
        (e₁ f) (p.skyscraperSheafFunctor.map g))
  have h₃ :
      e₃' (e₂' (e₁' (f ≫ g))) = e₃ (e₂ (e₁ f)) ≫ g := by
    rw [h₂]
    simpa [e₃, e₃'] using
      sigma_pointOver_sheafFiber_homEquiv_symm_naturality_right
        (U := U) p 𝒢 (e₂ (e₁ f)) g
  simpa [localizationLowerShriek_sheafFiber_homEquiv_sigma_pointOver_sheafFiber,
    e₁, e₁', e₂, e₂', e₃, e₃'] using h₃

/-- Helper for Lemma 7.35.3: once the owner hypotheses for left Kan extensions and weak
sheafification are available, the source proof closes by composing the three canonical
comparisons. -/
noncomputable def
    localizationLowerShriek_sheafFiberIsoSigma_pointOver_sheafFiber_of_instances
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w))
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type w)]
    [HasWeakSheafify J (Type w)] :
    p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢) ≅
      (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢) := by
  -- First rewrite the stalk through the left Kan extension, then perform the source split by
  -- `x`, and finally pass from presheaf fibers back to sheaf fibers.
  exact
    localizationLowerShriek_sheafFiberIso_presheafFiber_leftKanExtension (U := U) p 𝒢 ≪≫
      localization_leftKanExtension_presheafFiberIsoSigma_pointOver_presheafFiber
        (U := U) p 𝒢 ≪≫
      sigma_pointOver_presheafFiberIsoSigma_pointOver_sheafFiber (U := U) p 𝒢

-- Proof sketch: the intended source-faithful route is
-- `j_{U!} 𝒢` -> associated sheaf of `((Over.forget U).op.lan.obj 𝒢.1)` via
-- `localization_lowerShriek_associatedSheafIso`, then replace the sheaf stalk by the presheaf
-- stalk using `p.presheafToSheafCompSheafFiberIso (Type w)`, and finally split that filtered
-- colimit by the image `x : p.fiber.obj U` of a generator.
/-- Lemma 7.35.3: for a point `p` of the site `(C, J)`, an object `U : C`, and a sheaf `𝒢` on the
localized site `(C/U, J.over U)`, the stalk of `j_{U!} 𝒢` at `p` is isomorphic to the coproduct
of the stalks of `𝒢` at the localized points `p.over x` attached to elements
`x : p.fiber.obj U`. -/
noncomputable def localizationLowerShriek_sheafFiberIsoSigma_pointOver_sheafFiber
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w)) :
    p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢) ≅
      (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢) :=
  let q :
      ∀ E : Type w,
        (p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢) → E) ≃
          ((Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢) → E) :=
    fun E ↦ localizationLowerShriek_sheafFiber_homEquiv_sigma_pointOver_sheafFiber
      (U := U) p 𝒢 E
  -- Package the sheaf-level Hom-equivalence into the desired isomorphism of stalks.
  (Coyoneda.ext
    (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢)
    (p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢))
    (fun {E} f ↦ (q E).symm f)
    (fun {E} f ↦ q E f)
    (fun {E} f ↦ (q E).right_inv f)
    (fun {E} f ↦ (q E).left_inv f)
    (fun {E E'} f g ↦ by
      dsimp [q]
      rw [localizationLowerShriek_sheafFiber_homEquiv_sigma_pointOver_sheafFiber_naturality_right
        (U := U) p 𝒢 f g])).symm

-- Proof sketch: this is the canonical `Iso`-to-`IsIso` companion attached to the main
-- decomposition isomorphism.
/-- The morphism underlying the stalk decomposition of Lemma 7.35.3 is an isomorphism. -/
theorem localizationLowerShriek_sheafFiberIsoSigma_pointOver_sheafFiber_hom_isIso
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w)) :
    IsIso (localizationLowerShriek_sheafFiberIsoSigma_pointOver_sheafFiber U p 𝒢).hom := by
  -- The forward map of an isomorphism is an isomorphism.
  infer_instance

-- Proof sketch: package the canonical `Iso` from Lemma 7.35.3 as an `IsIsomorphic` statement.
/-- Proposition-level corollary of `localizationLowerShriek_sheafFiberIsoSigma_pointOver_sheafFiber`.
-/
theorem localizationLowerShriek_sheafFiber_isomorphic_sigma_pointOver_sheafFiber
    (p : Point.{w} J)
    (𝒢 : Sheaf (J.over U) (Type w)) :
    IsIsomorphic
      (p.sheafFiber.obj (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj 𝒢))
      (Σ x : p.fiber.obj U, (p.over x).sheafFiber.obj 𝒢) := by
  -- Package the canonical isomorphism as the proposition-level textbook statement.
  exact ⟨localizationLowerShriek_sheafFiberIsoSigma_pointOver_sheafFiber U p 𝒢⟩

end

end

end CategoryTheory
