module

public import stacks_project.Chap04.Definition_4_33_9
public import stacks_project.Chap04.Lemma_4_32_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryOver
open FibredCategoryMor
open scoped Bicategory

/-
Domain-style sampling for Lemma 4.33.10:
- primary domain: fibred categories over a fixed base together with bicategorical `2`-fibre
  products in the fibred full sub-`2`-category of `Cat/C`;
- sampled owner declarations:
  `explicitTwoFibreProduct`,
  `explicitTwoFibreProductSquareOver`,
  `explicitTwoFibreProduct_isTwoFibreProduct`,
  `FibredCategoryOver.ofFunctor`,
  `FibredCategoryMor.ofBasedFunctor`;
- best owner abstraction: `FibredCategoryOver C`, viewed through the owner sub-`2`-category
  `fibredCategoryOverSubTwoCategory C`, with `explicitTwoFibreProduct` supplying the canonical
  source-facing pullback model in `Cat/C`;
- primitive data: entirely owned upstream by `explicitTwoFibreProduct` and its two projection
  based functors;
- derived API kept here: the fibredness of the explicit apex, the upgraded projection morphisms in
  `FibredCategoryOver C`, and the resulting `BicategoricalTwoCommutativeSquare`.

Source/core/bridge triage:
- `source-facing`: the square `FibredCategoryOver.twoFibreProductSquare F G` and its
  `2`-fibre-product property in `FibredCategoryOver C`;
- `core/canonical`: `FibredCategoryOver C`, the ambient owner homs `X ⟶ Y`, and
  `Bicategory.IsFinal (FibredCategoryOver.twoFibreProductSquare F G)`;
- `bridge/view`: the bundled apex `FibredCategoryOver.twoFibreProduct F G` and the ambient
  `Cat/C` square
  `(explicitTwoFibreProductSquareOver F.toBasedFunctor G.toBasedFunctor).toBicategoricalSquare`;
- exact-interface wrapper eliminated here: downstream ambient uses should call
  `explicitTwoFibreProduct_isTwoFibreProduct` directly rather than through a renamed local shell. -/

variable {C : Type u} [Category.{v} C]
variable {Xf Yf Sf : FibredCategoryOver.{u, v, max u v, v} C}

/-- Helper for Lemma 4.33.10: a morphism of fibred categories sends a strongly cartesian lift over
the chosen base arrow to a strongly cartesian lift over the same base arrow. -/
private theorem map_stronglyCartesian_over_base
    {X Y : FibredCategoryOver C} (H : X ⟶ Y)
    {U V : C} {a b : X.S} {f : U ⟶ V} {φ : a ⟶ b}
    (hφ : X.p.IsStronglyCartesian f φ) :
    Y.p.IsStronglyCartesian f ((toFunctor H).map φ) := by
  -- Rewrite the source lift to the projected base so the owner preservation theorem applies.
  have hφ' : X.p.IsStronglyCartesian (X.p.map φ) φ := by
    letI : X.p.IsStronglyCartesian f φ := hφ
    subst_hom_lift X.p f φ
    simpa using hφ
  have hmap :
      Y.p.IsStronglyCartesian (Y.p.map ((toFunctor H).map φ)) ((toFunctor H).map φ) :=
    FibredCategoryMor.map_stronglyCartesian H φ hφ'
  -- Then transport the target lift back to the original chosen base arrow `f`.
  have hLift : Y.p.IsHomLift f ((toFunctor H).map φ) := by
    letI : X.p.IsHomLift f φ := hφ.toIsHomLift
    exact show Y.p.IsHomLift f ((toFunctor H).map φ) from inferInstance
  letI : Y.p.IsHomLift f ((toFunctor H).map φ) := hLift
  subst_hom_lift Y.p f ((toFunctor H).map φ)
  simpa using hmap

/-- Helper for Lemma 4.33.10: if a morphism is strongly cartesian for one chosen lift of its base
arrow, then it is strongly cartesian for any other chosen lift of the same morphism. -/
private theorem isStronglyCartesian_rebase_of_same_lift
    {𝒮 : Type u} {𝒳 : Type v} [Category 𝒮] [Category 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {a b : 𝒳} {f f' : p.obj a ⟶ p.obj b} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] [p.IsHomLift f' φ] :
    p.IsStronglyCartesian f' φ := by
  -- Both lift witnesses identify their base arrows with `p.map φ`.
  have hf : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  have hf' : f' = p.map φ := IsHomLift.eq_of_isHomLift p f' φ
  subst hf
  subst hf'
  infer_instance

/-- Helper for Lemma 4.33.10: an external lift witness upgrades strong cartesianness back to the
owner-level base map of the same morphism. -/
private theorem isStronglyCartesian_of_external_hom_lift
    {𝒮 : Type u} {𝒳 : Type v} [Category 𝒮] [Category 𝒳]
    (p : 𝒳 ⥤ 𝒮)
    {R S : 𝒮} {a b : 𝒳} {f : R ⟶ S} (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] [p.IsHomLift f φ] :
    p.IsStronglyCartesian (p.map φ) φ := by
  -- Normalize the chosen external source and target to the actual owner source and target.
  have ha : p.obj a = R := IsHomLift.domain_eq p f φ
  have hb : p.obj b = S := IsHomLift.codomain_eq p f φ
  subst ha
  subst hb
  exact isStronglyCartesian_rebase_of_same_lift (p := p) (f := f) (f' := p.map φ) φ

/-- Helper for Lemma 4.33.10: the base projection of a morphism in the explicit pullback is its
stored `base` field. -/
theorem explicitTwoFibreProduct_base_projection_map
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    (φ : P ⟶ Q) :
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.map φ = φ.base := by
  rfl

/-- Helper for Lemma 4.33.10: a lift for the projection of the explicit pullback has base arrow
equal to the stored `base` field of the morphism. -/
private theorem explicitTwoFibreProduct_isHomLift_base_eq
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift f φ) :
    φ.base = f := by
  let p := (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p
  have h : f = p.map φ := @IsHomLift.eq_of_isHomLift _ _ _ _ p _ _ f φ hφ
  simpa [p, explicitTwoFibreProduct_base_projection_map F G φ] using h.symm

/-- Helper for Lemma 4.33.10: a lift in the explicit pullback induces the corresponding lift on
the left component over the same base arrow. -/
private theorem explicitTwoFibreProduct_left_isHomLift_of_isHomLift
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift f φ) :
    Xf.p.IsHomLift f φ.a := by
  -- After identifying the outer base with `φ.base`, the stored component lift is exactly over `f`.
  change Xf.toBasedCategory.p.IsHomLift f φ.a
  have hbase : φ.base = f := explicitTwoFibreProduct_isHomLift_base_eq F G φ hφ
  rw [← hbase]
  simpa using (φ.a_over : Xf.p.IsHomLift φ.base φ.a)

/-- Helper for Lemma 4.33.10: a lift in the explicit pullback induces the corresponding lift on
the right component over the same base arrow. -/
private theorem explicitTwoFibreProduct_right_isHomLift_of_isHomLift
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    {f : P.U ⟶ Q.U} (φ : P ⟶ Q)
    (hφ : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift f φ) :
    Yf.p.IsHomLift f φ.b := by
  -- The same normalization works for the right component.
  change Yf.toBasedCategory.p.IsHomLift f φ.b
  have hbase : φ.base = f := explicitTwoFibreProduct_isHomLift_base_eq F G φ hφ
  rw [← hbase]
  simpa using (φ.b_over : Yf.p.IsHomLift φ.base φ.b)

/-- Helper for Lemma 4.33.10: a morphism in the explicit pullback is strongly cartesian whenever
its left and right components are strongly cartesian over the same base arrow. -/
private theorem explicitTwoFibreProduct_hom_isStronglyCartesian_of_components
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    (φ : P ⟶ Q)
    (ha : Xf.p.IsStronglyCartesian φ.base φ.a)
    (hb : Yf.p.IsStronglyCartesian φ.base φ.b) :
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsStronglyCartesian
      φ.base φ := by
  letI : Xf.p.IsStronglyCartesian φ.base φ.a := ha
  letI : Yf.p.IsStronglyCartesian φ.base φ.b := hb
  refine
    { toIsHomLift := by
        change (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
          ((explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.map φ) φ
        infer_instance
      universal_property' := ?_ }
  intro R g ψ hψ
  letI :
      (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
        (g ≫ φ.base) ψ := hψ
  have hψa : Xf.p.IsHomLift (g ≫ φ.base) ψ.a := by
    exact explicitTwoFibreProduct_left_isHomLift_of_isHomLift F G (f := g ≫ φ.base) ψ hψ
  have hψb : Yf.p.IsHomLift (g ≫ φ.base) ψ.b := by
    exact explicitTwoFibreProduct_right_isHomLift_of_isHomLift F G (f := g ≫ φ.base) ψ hψ
  -- Factor the left and right components through the chosen strongly cartesian lifts.
  letI : Xf.p.IsHomLift (g ≫ φ.base) ψ.a := hψa
  obtain ⟨χa, hχa, hχa_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property Xf.p φ.base φ.a g (g ≫ φ.base) rfl ψ.a
  have hχa_over : Xf.p.IsHomLift g χa := hχa.1
  have hχa_fac : χa ≫ φ.a = ψ.a := hχa.2
  letI : Yf.p.IsHomLift (g ≫ φ.base) ψ.b := hψb
  obtain ⟨χb, hχb, hχb_uniq⟩ :=
    Functor.IsStronglyCartesian.universal_property Yf.p φ.base φ.b g (g ≫ φ.base) rfl ψ.b
  have hχb_over : Yf.p.IsHomLift g χb := hχb.1
  have hχb_fac : χb ≫ φ.b = ψ.b := hχb.2
  have hmap_hb :
      Sf.p.IsStronglyCartesian φ.base ((toFunctor G).map φ.b) :=
    map_stronglyCartesian_over_base G hb
  letI : Sf.p.IsStronglyCartesian φ.base ((toFunctor G).map φ.b) := hmap_hb
  have hleft_over : Sf.p.IsHomLift g ((toFunctor F).map χa ≫ P.comparison) := by
    -- Map the left factorization into `Sf`, then append the vertical comparison of `P`.
    have hFχa : Sf.p.IsHomLift g ((toFunctor F).map χa) := by
      infer_instance
    letI : Sf.p.IsHomLift g ((toFunctor F).map χa) := hFχa
    letI : Sf.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
    exact IsHomLift.comp_lift_id_right' (p := Sf.p) g ((toFunctor F).map χa) P.U P.comparison
  have hright_over : Sf.p.IsHomLift g (R.comparison ≫ (toFunctor G).map χb) := by
    -- Do the same for the right factorization, now precomposing with the vertical comparison of
    -- the source object `R`.
    have hGχb : Sf.p.IsHomLift g ((toFunctor G).map χb) := by
      infer_instance
    letI : Sf.p.IsHomLift g ((toFunctor G).map χb) := hGχb
    letI : Sf.p.IsHomLift (𝟙 R.U) R.comparison := R.comparison_over
    exact
      IsHomLift.comp_lift_id_left' (p := Sf.p) R.U R.comparison g ((toFunctor G).map χb)
  have hcomm_after_comp :
      ((toFunctor F).map χa ≫ P.comparison) ≫ (toFunctor G).map φ.b =
        (R.comparison ≫ (toFunctor G).map χb) ≫ (toFunctor G).map φ.b := by
    -- Both candidate comparison squares become the same after composing with `G.map φ.b`.
    calc
      ((toFunctor F).map χa ≫ P.comparison) ≫ (toFunctor G).map φ.b
          = (toFunctor F).map χa ≫ ((toFunctor F).map φ.a ≫ Q.comparison) := by
              rw [φ.comm.w]
              simp [Category.assoc]
      _ = (toFunctor F).map (χa ≫ φ.a) ≫ Q.comparison := by
            simp [Functor.map_comp, Category.assoc]
      _ = (toFunctor F).map ψ.a ≫ Q.comparison := by
            rw [hχa_fac]
      _ = R.comparison ≫ (toFunctor G).map ψ.b := by
            exact ψ.comm.w
      _ = R.comparison ≫ (toFunctor G).map (χb ≫ φ.b) := by
            rw [hχb_fac]
      _ = (R.comparison ≫ (toFunctor G).map χb) ≫ (toFunctor G).map φ.b := by
            simp [Functor.map_comp, Category.assoc]
  have hcomm :
      (toFunctor F).map χa ≫ P.comparison =
        R.comparison ≫ (toFunctor G).map χb := by
    -- Cancel the mapped strongly cartesian arrow `(toFunctor G).map φ.b`.
    apply Functor.IsStronglyCartesian.ext (p := Sf.p) (f := φ.base) ((toFunctor G).map φ.b) g
    simpa [Category.assoc] using hcomm_after_comp
  let χ : R ⟶ P :=
    { base := g
      a := χa
      a_over := hχa_over
      b := χb
      b_over := hχb_over
      comm := ⟨hcomm⟩ }
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · -- The assembled morphism factors through `φ` by the chosen component factorizations.
    change (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
      ((explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.map χ) χ
    infer_instance
  · -- The assembled morphism factors through `φ` by the chosen component factorizations.
    apply ExplicitTwoFibreProductHom.ext
    · simpa [χ] using hχa_fac
    · simpa [χ] using hχb_fac
  · intro χ' hχ'
    rcases hχ' with ⟨hχ'_over, hχ'_fac⟩
    letI :
        (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
          g χ' := hχ'_over
    have hχ'a : Xf.p.IsHomLift g χ'.a := by
      exact explicitTwoFibreProduct_left_isHomLift_of_isHomLift F G (f := g) χ' hχ'_over
    have hχ'b : Yf.p.IsHomLift g χ'.b := by
      exact explicitTwoFibreProduct_right_isHomLift_of_isHomLift F G (f := g) χ' hχ'_over
    -- Uniqueness is checked componentwise using the universal properties of `φ.a` and `φ.b`.
    apply ExplicitTwoFibreProductHom.ext
    · exact hχa_uniq χ'.a ⟨hχ'a, by simpa using congrArg ExplicitTwoFibreProductHom.a hχ'_fac⟩
    · exact hχb_uniq χ'.b ⟨hχ'b, by simpa using congrArg ExplicitTwoFibreProductHom.b hχ'_fac⟩

/-- Helper for Lemma 4.33.10: the comparison carried by an explicit pullback object is an
isomorphism in the total category of `Sf`. -/
private theorem explicitTwoFibreProduct_comparison_isIso
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj) :
    IsIso P.comparison := by
  -- Forget the fiberwise comparison isomorphism to the total category `Sf`.
  let e : (toFunctor F).obj P.obj.fst.1 ≅ (toFunctor G).obj P.obj.snd.1 :=
    { hom := P.comparison
      inv := P.obj.iso.inv.1
      hom_inv_id := by
        exact congrArg Subtype.val P.obj.iso.hom_inv_id
      inv_hom_id := by
        exact congrArg Subtype.val P.obj.iso.inv_hom_id }
  exact ⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- Helper for Lemma 4.33.10: the chosen pullback of the left component of `P` along `f`, viewed
as an object of the standard fiber of `Xf` over the new base. -/
private noncomputable def explicitTwoFibreProduct_left_pullback
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    Xf.p.Fiber V :=
  let _ : HasFibers Xf.p := HasFibers.canonical Xf.p
  let a := HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2
  Functor.Fiber.mk (IsHomLift.domain_eq Xf.p f a)

/-- Helper for Lemma 4.33.10: the chosen pullback map of the left component of `P` along `f`. -/
private noncomputable def explicitTwoFibreProduct_left_pullback_map
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    (explicitTwoFibreProduct_left_pullback F G P f).1 ⟶ P.obj.fst.1 :=
  let _ : HasFibers Xf.p := HasFibers.canonical Xf.p
  let a := HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2
  show (explicitTwoFibreProduct_left_pullback F G P f).1 ⟶ P.obj.fst.1 from a

/-- Helper for Lemma 4.33.10: the chosen pullback of the right component of `P` along `f`, viewed
as an object of the standard fiber of `Yf` over the new base. -/
private noncomputable def explicitTwoFibreProduct_right_pullback
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    Yf.p.Fiber V :=
  let _ : HasFibers Yf.p := HasFibers.canonical Yf.p
  let b := HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2
  Functor.Fiber.mk (IsHomLift.domain_eq Yf.p f b)

/-- Helper for Lemma 4.33.10: the chosen pullback map of the right component of `P` along `f`. -/
private noncomputable def explicitTwoFibreProduct_right_pullback_map
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    (explicitTwoFibreProduct_right_pullback F G P f).1 ⟶ P.obj.snd.1 :=
  let _ : HasFibers Yf.p := HasFibers.canonical Yf.p
  let b := HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2
  show (explicitTwoFibreProduct_right_pullback F G P f).1 ⟶ P.obj.snd.1 from b

/-- Helper for Lemma 4.33.10: pulling back the two components of an explicit pullback object along
`f` produces the unique comparison isomorphism in the fiber of `Sf` over the new base. -/
private noncomputable def explicitTwoFibreProduct_pulledback_comparison_iso
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    ((toBasedFunctor F).fiberFunctor V).obj
        (explicitTwoFibreProduct_left_pullback F G P f) ≅
      ((toBasedFunctor G).fiberFunctor V).obj
        (explicitTwoFibreProduct_right_pullback F G P f) := by
  let _ : HasFibers Xf.p := HasFibers.canonical Xf.p
  let _ : HasFibers Yf.p := HasFibers.canonical Yf.p
  let a := explicitTwoFibreProduct_left_pullback_map F G P f
  let b := explicitTwoFibreProduct_right_pullback_map F G P f
  -- The chosen pullback maps are strongly cartesian in `Xf` and `Yf`.
  have ha_cart : Xf.p.IsCartesian f a := by
    change Xf.p.IsCartesian f (HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2)
    infer_instance
  have hb_cart : Yf.p.IsCartesian f b := by
    change Yf.p.IsCartesian f (HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2)
    infer_instance
  have ha : Xf.p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Xf.p f a
  have hb : Yf.p.IsStronglyCartesian f b :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Yf.p f b
  -- Map those strongly cartesian lifts into `Sf`.
  have hFa : Sf.p.IsStronglyCartesian f ((toFunctor F).map a) :=
    map_stronglyCartesian_over_base F ha
  have hGb : Sf.p.IsStronglyCartesian f ((toFunctor G).map b) :=
    map_stronglyCartesian_over_base G hb
  letI : IsIso P.comparison := explicitTwoFibreProduct_comparison_isIso F G P
  letI : Sf.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
  have hcomparison : Sf.p.IsStronglyCartesian (𝟙 P.U) P.comparison :=
    Functor.IsStronglyCartesian.of_isIso Sf.p (𝟙 P.U) P.comparison
  -- Compose `F.map a` with the vertical comparison of `P` to obtain a second lift over `f`.
  have hleft :
      Sf.p.IsStronglyCartesian f ((toFunctor F).map a ≫ P.comparison) := by
    letI : Sf.p.IsStronglyCartesian f ((toFunctor F).map a) := hFa
    letI : Sf.p.IsStronglyCartesian (𝟙 P.U) P.comparison := hcomparison
    simpa using
      (show Sf.p.IsStronglyCartesian (f ≫ 𝟙 P.U)
          ((toFunctor F).map a ≫ P.comparison) from inferInstance)
  letI : Sf.p.IsStronglyCartesian f ((toFunctor G).map b) := hGb
  letI : Sf.p.IsStronglyCartesian f ((toFunctor F).map a ≫ P.comparison) := hleft
  let e :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      Sf.p
      (g := Iso.refl V)
      (show f = (Iso.refl V).hom ≫ f by simp)
      ((toFunctor G).map b)
      ((toFunctor F).map a ≫ P.comparison)
  have hhom : Sf.p.IsHomLift (𝟙 V) e.hom := by
    simpa [e] using
      (show Sf.p.IsHomLift (Iso.refl V).hom e.hom from inferInstance)
  have hinv : Sf.p.IsHomLift (𝟙 V) e.inv := by
    simpa [e] using
      (show Sf.p.IsHomLift (Iso.refl V).inv e.inv from inferInstance)
  -- Package the domain comparison back into the standard fiber over `V`.
  refine
    { hom := Functor.Fiber.homMk Sf.p V e.hom
      inv := Functor.Fiber.homMk Sf.p V e.inv
      hom_inv_id := by
        apply Functor.Fiber.hom_ext
        exact e.hom_inv_id
      inv_hom_id := by
        apply Functor.Fiber.hom_ext
        exact e.inv_hom_id }

/-- Helper for Lemma 4.33.10: every base arrow into an explicit pullback object admits the
canonical pullback morphism obtained by pulling back each component in the two fibred categories. -/
private theorem explicitTwoFibreProduct_exists_isStronglyCartesian
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    ∃ Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj,
      ∃ η : Q ⟶ P,
        Xf.p.IsStronglyCartesian (Xf.p.map η.a) η.a ∧
          Yf.p.IsStronglyCartesian (Yf.p.map η.b) η.b ∧
            (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsStronglyCartesian
              f η := by
  let _ : HasFibers Xf.p := HasFibers.canonical Xf.p
  let _ : HasFibers Yf.p := HasFibers.canonical Yf.p
  let a := explicitTwoFibreProduct_left_pullback_map F G P f
  let b := explicitTwoFibreProduct_right_pullback_map F G P f
  -- Pull back the two components of `P` along `f`.
  let Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj :=
    { U := V
      obj :=
        { fst := explicitTwoFibreProduct_left_pullback F G P f
          snd := explicitTwoFibreProduct_right_pullback F G P f
          iso := explicitTwoFibreProduct_pulledback_comparison_iso F G P f } }
  have ha_over : Xf.p.IsHomLift f a := by
    change Xf.p.IsHomLift f (HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2)
    infer_instance
  have hb_over : Yf.p.IsHomLift f b := by
    change Yf.p.IsHomLift f (HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2)
    infer_instance
  have ha_cart : Xf.p.IsCartesian f a := by
    change Xf.p.IsCartesian f (HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2)
    infer_instance
  have hb_cart : Yf.p.IsCartesian f b := by
    change Yf.p.IsCartesian f (HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2)
    infer_instance
  have ha : Xf.p.IsStronglyCartesian f a :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Xf.p f a
  have hb : Yf.p.IsStronglyCartesian f b :=
    Functor.IsFibered.isStronglyCartesian_of_isCartesian Yf.p f b
  have hFa : Sf.p.IsStronglyCartesian f ((toFunctor F).map a) :=
    map_stronglyCartesian_over_base F ha
  have hGb : Sf.p.IsStronglyCartesian f ((toFunctor G).map b) :=
    map_stronglyCartesian_over_base G hb
  letI : IsIso P.comparison := explicitTwoFibreProduct_comparison_isIso F G P
  letI : Sf.p.IsHomLift (𝟙 P.U) P.comparison := P.comparison_over
  have hcomparison : Sf.p.IsStronglyCartesian (𝟙 P.U) P.comparison :=
    Functor.IsStronglyCartesian.of_isIso Sf.p (𝟙 P.U) P.comparison
  have hleft :
      Sf.p.IsStronglyCartesian f ((toFunctor F).map a ≫ P.comparison) := by
    letI : Sf.p.IsStronglyCartesian f ((toFunctor F).map a) := hFa
    letI : Sf.p.IsStronglyCartesian (𝟙 P.U) P.comparison := hcomparison
    simpa using
      (show Sf.p.IsStronglyCartesian (f ≫ 𝟙 P.U)
          ((toFunctor F).map a ≫ P.comparison) from inferInstance)
  letI : Sf.p.IsStronglyCartesian f ((toFunctor G).map b) := hGb
  letI : Sf.p.IsStronglyCartesian f ((toFunctor F).map a ≫ P.comparison) := hleft
  let e :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      Sf.p
      (g := Iso.refl V)
      (show f = (Iso.refl V).hom ≫ f by simp)
      ((toFunctor G).map b)
      ((toFunctor F).map a ≫ P.comparison)
  have hfac :
      e.hom ≫ (toFunctor G).map b = (toFunctor F).map a ≫ P.comparison := by
    simpa [e] using
      (Functor.IsStronglyCartesian.fac
        Sf.p
        f
        ((toFunctor G).map b)
        (show f = (Iso.refl V).hom ≫ f by simp)
        ((toFunctor F).map a ≫ P.comparison))
  have hcomm :
      CommSq
        ((toFunctor F).map a)
        Q.comparison
        P.comparison
        ((toFunctor G).map b) := by
    -- The defining square is exactly the comparison furnished by `e`.
    refine ⟨?_⟩
    simpa [Q, explicitTwoFibreProduct_pulledback_comparison_iso] using hfac.symm
  let η : Q ⟶ P :=
    { base := f
      a := a
      a_over := ha_over
      b := b
      b_over := hb_over
      comm := hcomm }
  have hηa : Xf.p.IsStronglyCartesian (Xf.p.map η.a) η.a := by
    letI : Xf.p.IsStronglyCartesian f η.a := ha
    letI : Xf.p.IsHomLift f η.a := ha_over
    exact
      isStronglyCartesian_of_external_hom_lift
        (p := Xf.p) (R := V) (S := P.U) (f := f) η.a
  have hηb : Yf.p.IsStronglyCartesian (Yf.p.map η.b) η.b := by
    letI : Yf.p.IsStronglyCartesian f η.b := hb
    letI : Yf.p.IsHomLift f η.b := hb_over
    exact
      isStronglyCartesian_of_external_hom_lift
        (p := Yf.p) (R := V) (S := P.U) (f := f) η.b
  have hη :
      (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsStronglyCartesian
        f η :=
    explicitTwoFibreProduct_hom_isStronglyCartesian_of_components F G η ha hb
  -- The canonical component pullbacks assemble to the desired strongly cartesian lift.
  exact ⟨Q, η, hηa, hηb, hη⟩

theorem explicitTwoFibreProductProjection_isFibered
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsFibered := by
  -- Route correction: prove fibredness from the textbook pullback construction itself, rather
  -- than trying to descend it from a later owner-level `2`-fibre-product theorem.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro P V f
  -- Pull back both components of `P` along `f`, then use the comparison in `Sf` to rebuild the
  -- missing pullback isomorphism upstairs.
  obtain ⟨Q, η, _, _, hη⟩ := explicitTwoFibreProduct_exists_isStronglyCartesian F G P f
  exact ⟨Q, η, hη⟩

namespace FibredCategoryOver

open FibredCategoryMor

/-- The explicit `2`-fibre-product category of Lemma 4.32.3, bundled as a fibred category over
`C` when the legs are morphisms of fibred categories. -/
noncomputable abbrev twoFibreProduct
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    FibredCategoryOver C :=
  let p := (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p
  letI : p.IsFibered := explicitTwoFibreProductProjection_isFibered F G
  ofFunctor p

noncomputable abbrev twoFibreProductLeftBased
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    (twoFibreProduct F G).toBasedCategory ⥤ᵇ Xf.toBasedCategory :=
  show (twoFibreProduct F G).toBasedCategory ⥤ᵇ Xf.toBasedCategory from
    explicitTwoFibreProductLeftProjection (toBasedFunctor F) (toBasedFunctor G)

noncomputable abbrev twoFibreProductRightBased
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    (twoFibreProduct F G).toBasedCategory ⥤ᵇ Yf.toBasedCategory :=
  show (twoFibreProduct F G).toBasedCategory ⥤ᵇ Yf.toBasedCategory from
    explicitTwoFibreProductRightProjection (toBasedFunctor F) (toBasedFunctor G)

/-- Helper for Lemma 4.33.10: once the canonical comparison with the textbook pullback lifts is
available, both projection functors preserve strongly cartesian morphisms. -/
private theorem explicitTwoFibreProduct_components_of_isStronglyCartesian
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    (φ : P ⟶ Q)
    (hφ :
      (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsStronglyCartesian
        ((explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.map φ) φ) :
    Xf.p.IsStronglyCartesian (Xf.p.map φ.a) φ.a ∧
      Yf.p.IsStronglyCartesian (Yf.p.map φ.b) φ.b := by
  have hφ_base :
      (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsStronglyCartesian
        φ.base φ := by
    simpa [explicitTwoFibreProduct_base_projection_map F G φ] using hφ
  obtain ⟨R, η, hηa, hηb, hη⟩ :=
    explicitTwoFibreProduct_exists_isStronglyCartesian F G Q φ.base
  letI :
      (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsStronglyCartesian
        φ.base η := hη
  letI :
      (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsStronglyCartesian
        φ.base φ := hφ_base
  let e :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      ((explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p)
      (g := Iso.refl P.U)
      (show φ.base = (Iso.refl P.U).hom ≫ φ.base by simp)
      η
      φ
  have hfac : e.hom ≫ η = φ := by
    simpa [e] using
      (Functor.IsStronglyCartesian.fac
        ((explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p)
        φ.base
        η
        (show φ.base = (Iso.refl P.U).hom ≫ φ.base by simp)
        φ)
  have hhom :
      (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
        (𝟙 P.U) e.hom := by
    simpa [e] using
      (show
          (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
            (Iso.refl P.U).hom e.hom from inferInstance)
  have hhom_base :
      (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
        e.hom.base e.hom := by
    change
      (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
        ((explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.map e.hom) e.hom
    infer_instance
  have hEa_over_base : Xf.p.IsHomLift e.hom.base e.hom.a :=
    explicitTwoFibreProduct_left_isHomLift_of_isHomLift
      (F := F) (G := G) (P := P) (Q := R) (f := e.hom.base) e.hom hhom_base
  have hEb_over_base : Yf.p.IsHomLift e.hom.base e.hom.b :=
    explicitTwoFibreProduct_right_isHomLift_of_isHomLift
      (F := F) (G := G) (P := P) (Q := R) (f := e.hom.base) e.hom hhom_base
  have hEa_iso : IsIso e.hom.a := by
    refine ⟨e.inv.a, ?_, ?_⟩
    · exact congrArg ExplicitTwoFibreProductHom.a e.hom_inv_id
    · exact congrArg ExplicitTwoFibreProductHom.a e.inv_hom_id
  have hEb_iso : IsIso e.hom.b := by
    refine ⟨e.inv.b, ?_, ?_⟩
    · exact congrArg ExplicitTwoFibreProductHom.b e.hom_inv_id
    · exact congrArg ExplicitTwoFibreProductHom.b e.inv_hom_id
  have hEa_base :
      Xf.p.IsStronglyCartesian e.hom.base e.hom.a :=
    Functor.IsStronglyCartesian.of_isIso Xf.p e.hom.base e.hom.a
  have hEb_base :
      Yf.p.IsStronglyCartesian e.hom.base e.hom.b :=
    Functor.IsStronglyCartesian.of_isIso Yf.p e.hom.base e.hom.b
  have hEa :
      Xf.p.IsStronglyCartesian (Xf.p.map e.hom.a) e.hom.a := by
    letI : Xf.p.IsStronglyCartesian e.hom.base e.hom.a := hEa_base
    letI : Xf.p.IsHomLift e.hom.base e.hom.a := hEa_over_base
    exact
      isStronglyCartesian_of_external_hom_lift
        (p := Xf.p) (R := P.U) (S := R.U) (f := e.hom.base) e.hom.a
  have hEb :
      Yf.p.IsStronglyCartesian (Yf.p.map e.hom.b) e.hom.b := by
    letI : Yf.p.IsStronglyCartesian e.hom.base e.hom.b := hEb_base
    letI : Yf.p.IsHomLift e.hom.base e.hom.b := hEb_over_base
    exact
      isStronglyCartesian_of_external_hom_lift
        (p := Yf.p) (R := P.U) (S := R.U) (f := e.hom.base) e.hom.b
  have hfac_a : e.hom.a ≫ η.a = φ.a := by
    exact congrArg ExplicitTwoFibreProductHom.a hfac
  have hfac_b : e.hom.b ≫ η.b = φ.b := by
    exact congrArg ExplicitTwoFibreProductHom.b hfac
  -- Owner-level strong cartesianness is stable under composition and the computed factorization.
  letI : Xf.p.IsStronglyCartesian (Xf.p.map e.hom.a) e.hom.a := hEa
  letI : Xf.p.IsStronglyCartesian (Xf.p.map η.a) η.a := hηa
  have hφa :
      Xf.p.IsStronglyCartesian (Xf.p.map φ.a) φ.a := by
    have hcomp :
        Xf.p.IsStronglyCartesian (Xf.p.map e.hom.a ≫ Xf.p.map η.a) φ.a := by
      simpa [hfac_a] using
        (show Xf.p.IsStronglyCartesian
            (Xf.p.map e.hom.a ≫ Xf.p.map η.a)
            (e.hom.a ≫ η.a) from inferInstance)
    letI : Xf.p.IsStronglyCartesian (Xf.p.map e.hom.a ≫ Xf.p.map η.a) φ.a := hcomp
    exact
      isStronglyCartesian_rebase_of_same_lift
        (p := Xf.p)
        (f := Xf.p.map e.hom.a ≫ Xf.p.map η.a)
        (f' := Xf.p.map φ.a)
        φ.a
  letI : Yf.p.IsStronglyCartesian (Yf.p.map e.hom.b) e.hom.b := hEb
  letI : Yf.p.IsStronglyCartesian (Yf.p.map η.b) η.b := hηb
  have hφb :
      Yf.p.IsStronglyCartesian (Yf.p.map φ.b) φ.b := by
    have hcomp :
        Yf.p.IsStronglyCartesian (Yf.p.map e.hom.b ≫ Yf.p.map η.b) φ.b := by
      simpa [hfac_b] using
        (show Yf.p.IsStronglyCartesian
            (Yf.p.map e.hom.b ≫ Yf.p.map η.b)
            (e.hom.b ≫ η.b) from inferInstance)
    letI : Yf.p.IsStronglyCartesian (Yf.p.map e.hom.b ≫ Yf.p.map η.b) φ.b := hcomp
    exact
      isStronglyCartesian_rebase_of_same_lift
        (p := Yf.p)
        (f := Yf.p.map e.hom.b ≫ Yf.p.map η.b)
        (f' := Yf.p.map φ.b)
        φ.b
  exact ⟨hφa, hφb⟩

/-- Helper for Lemma 4.33.10: once the canonical comparison with the textbook pullback lifts is
available, both projection functors preserve strongly cartesian morphisms. -/
private theorem explicitTwoFibreProduct_projections_preserveStronglyCartesian
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    BasedFunctor.PreservesStronglyCartesian (twoFibreProductLeftBased F G) ∧
      BasedFunctor.PreservesStronglyCartesian (twoFibreProductRightBased F G) := by
  constructor
  · intro P Q φ hφ
    -- The left projection preserves strong cartesianness because strong cartesianness in the
    -- explicit pullback can be read off on the two components.
    exact (explicitTwoFibreProduct_components_of_isStronglyCartesian F G φ hφ).1
  · intro P Q φ hφ
    -- The same comparison argument works for the right projection.
    exact (explicitTwoFibreProduct_components_of_isStronglyCartesian F G φ hφ).2

theorem twoFibreProductLeftProjection_preservesStronglyCartesian
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    BasedFunctor.PreservesStronglyCartesian (twoFibreProductLeftBased F G) := by
  exact (explicitTwoFibreProduct_projections_preserveStronglyCartesian F G).1

theorem twoFibreProductRightProjection_preservesStronglyCartesian
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    BasedFunctor.PreservesStronglyCartesian (twoFibreProductRightBased F G) := by
  exact (explicitTwoFibreProduct_projections_preserveStronglyCartesian F G).2

/-- The left projection from the canonical fibred `2`-fibre product. -/
noncomputable abbrev twoFibreProductLeftProjection
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    twoFibreProduct F G ⟶ Xf :=
  ofBasedFunctor
    (twoFibreProductLeftBased F G)
    (twoFibreProductLeftProjection_preservesStronglyCartesian F G)

/-- The right projection from the canonical fibred `2`-fibre product. -/
noncomputable abbrev twoFibreProductRightProjection
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    twoFibreProduct F G ⟶ Yf :=
  ofBasedFunctor
    (twoFibreProductRightBased F G)
    (twoFibreProductRightProjection_preservesStronglyCartesian F G)

/-- The canonical `2`-commutative square in the bicategory of fibred categories over `C`
underlying Lemma 4.33.10. -/
noncomputable def twoFibreProductSquare
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    BicategoricalTwoCommutativeSquare F G :=
  { obj := twoFibreProduct F G
    p := twoFibreProductLeftProjection F G
    q := twoFibreProductRightProjection F G
    ψ := by
      let e :
          (twoFibreProductLeftProjection F G ≫ F).obj ≅
            (twoFibreProductRightProjection F G ≫ G).obj := by
        exact
          ObjectProperty.isoMk
            (show ObjectProperty
                ((twoFibreProduct F G).toBasedCategory ⥤ᵇ Sf.toBasedCategory) from
              BasedFunctor.PreservesStronglyCartesian)
            (show BasedFunctor.comp (twoFibreProductLeftBased F G) F.toHom ≅
                BasedFunctor.comp (twoFibreProductRightBased F G) G.toHom from
              explicitTwoFibreProductComparisonIsoOver (toBasedFunctor F) (toBasedFunctor G))
      exact CategoryTheory.isoMk e trivial trivial }

/-- Helper for Lemma 4.33.10: equality of based natural transformations is detected on the
underlying ordinary natural transformations. -/
theorem basedNatTrans_ext_toNatTrans
    {A B : BasedCategory C}
    {H K : A ⥤ᵇ B}
    (η θ : H ⟶ K)
    (h : η.toNatTrans = θ.toNatTrans) :
    η = θ := by
  exact BasedNatTrans.ext η θ h

/-- Helper for Lemma 4.33.10: forget a square of fibred categories to the ambient square of based
categories over `C`. -/
noncomputable def toBasedSquare
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G) :
    BicategoricalTwoCommutativeSquare (B := BasedCategory C)
      (toBasedFunctor F) (toBasedFunctor G) :=
  { obj := P.obj.toBasedCategory
    p := toBasedFunctor P.p
    q := toBasedFunctor P.q
    ψ := FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ }

/-- Helper for Lemma 4.33.10: the ambient explicit pullback square of the underlying based
functors of `F` and `G`. -/
noncomputable abbrev explicitTwoFibreProductBasedSquare
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :=
  CategoryOver.explicitTwoFibreProductSquare.{u, v, max u v, max u v}
    (X := Xf.toBasedCategory) (Y := Yf.toBasedCategory) (S := Sf.toBasedCategory)
    (show Xf.toBasedCategory ⟶ Sf.toBasedCategory from toBasedFunctor F)
    (show Yf.toBasedCategory ⟶ Sf.toBasedCategory from toBasedFunctor G)

/-- Helper for Lemma 4.33.10: the forward component of the owner square comparison is vertical
over the chosen base object. -/
theorem twoFibreProduct_terminalLift_obj_hom_isHomLift
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    Sf.p.IsHomLift (𝟙 (P.obj.p.obj T))
      ((FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T) := by
  -- Forget the owner `2`-cell to a based natural transformation and use its verticality.
  exact
    BasedNatTrans.isHomLift
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom
      (rfl : P.obj.p.obj T = P.obj.p.obj T)

/-- Helper for Lemma 4.33.10: the inverse component of the owner square comparison is also
vertical over the chosen base object. -/
theorem twoFibreProduct_terminalLift_obj_inv_isHomLift
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    Sf.p.IsHomLift (𝟙 (P.obj.p.obj T))
      ((FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).inv.app T) := by
  -- The inverse based natural transformation has the same identity-base property.
  exact
    BasedNatTrans.isHomLift
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).inv
      (rfl : P.obj.p.obj T = P.obj.p.obj T)

/-- Helper for Lemma 4.33.10: the forward and inverse comparison components compose to the
identity in the appropriate fiber of `Sf`. -/
theorem twoFibreProduct_terminalLift_obj_iso_hom_inv_id
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    @Functor.Fiber.homMk _ _ _ _ Sf.p (P.obj.p.obj T) _ _
        ((FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T)
        (twoFibreProduct_terminalLift_obj_hom_isHomLift F G P T) ≫
    @Functor.Fiber.homMk _ _ _ _ Sf.p (P.obj.p.obj T) _ _
        ((FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).inv.app T)
        (twoFibreProduct_terminalLift_obj_inv_isHomLift F G P T) =
      𝟙 ((toBasedFunctor F).fiberFunctor (P.obj.p.obj T)).obj
        (Functor.Fiber.mk (BasedFunctor.w_obj (toBasedFunctor P.p) T)) := by
  -- Forget the fiber packaging and use the inverse law of the underlying based-functor
  -- isomorphism.
  apply Functor.Fiber.hom_ext
  let τ :=
    (BasedNatTrans.forgetful P.obj.toBasedCategory Sf.toBasedCategory).mapIso
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ)
  change (τ.app T).hom ≫ (τ.app T).inv = 𝟙 _
  exact Iso.hom_inv_id (τ.app T)

/-- Helper for Lemma 4.33.10: the inverse and forward comparison components also compose to the
identity in the target fiber of `Sf`. -/
theorem twoFibreProduct_terminalLift_obj_iso_inv_hom_id
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    @Functor.Fiber.homMk _ _ _ _ Sf.p (P.obj.p.obj T) _ _
        ((FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).inv.app T)
        (twoFibreProduct_terminalLift_obj_inv_isHomLift F G P T) ≫
    @Functor.Fiber.homMk _ _ _ _ Sf.p (P.obj.p.obj T) _ _
        ((FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T)
        (twoFibreProduct_terminalLift_obj_hom_isHomLift F G P T) =
      𝟙 ((toBasedFunctor G).fiberFunctor (P.obj.p.obj T)).obj
        (Functor.Fiber.mk (BasedFunctor.w_obj (toBasedFunctor P.q) T)) := by
  -- The second inverse law is identical after forgetting the fiber structure.
  apply Functor.Fiber.hom_ext
  let τ :=
    (BasedNatTrans.forgetful P.obj.toBasedCategory Sf.toBasedCategory).mapIso
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ)
  change (τ.app T).inv ≫ (τ.app T).hom = 𝟙 _
  exact Iso.inv_hom_id (τ.app T)

/-- Helper for Lemma 4.33.10: the textbook factorization sends `T` to the quadruple
`(p(T), P.p(T), P.q(T), ψ_T)` inside the explicit fibred pullback. -/
noncomputable def twoFibreProduct_terminalLift_obj
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj :=
  { U := P.obj.p.obj T
    obj :=
      { fst := Functor.Fiber.mk (BasedFunctor.w_obj (toBasedFunctor P.p) T)
        snd := Functor.Fiber.mk (BasedFunctor.w_obj (toBasedFunctor P.q) T)
        iso :=
          { hom := @Functor.Fiber.homMk _ _ _ _ Sf.p (P.obj.p.obj T) _ _
              ((FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T)
              (twoFibreProduct_terminalLift_obj_hom_isHomLift F G P T)
            inv := @Functor.Fiber.homMk _ _ _ _ Sf.p (P.obj.p.obj T) _ _
              ((FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).inv.app T)
              (twoFibreProduct_terminalLift_obj_inv_isHomLift F G P T)
            hom_inv_id := twoFibreProduct_terminalLift_obj_iso_hom_inv_id F G P T
            inv_hom_id := twoFibreProduct_terminalLift_obj_iso_inv_hom_id F G P T } } }

/-- Helper for Lemma 4.33.10: the comparison of the textbook factorization object is exactly the
underlying component of the square isomorphism `P.ψ`. -/
private theorem twoFibreProduct_terminalLift_obj_comparison
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    (twoFibreProduct_terminalLift_obj F G P T).comparison =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T := by
  rfl

/-- Helper for Lemma 4.33.10: the morphism part of the textbook factorization satisfies the
pullback comparison square by naturality of `P.ψ`. -/
theorem twoFibreProduct_terminalLift_map_comm
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    {T T' : P.obj.S}
    (f : T ⟶ T') :
    CommSq
      ((toFunctor F).map ((toFunctor P.p).map f))
      (twoFibreProduct_terminalLift_obj F G P T).comparison
      (twoFibreProduct_terminalLift_obj F G P T').comparison
      ((toFunctor G).map ((toFunctor P.q).map f)) := by
  -- The defining square is exactly the naturality square of the forgotten owner comparison.
  refine ⟨?_⟩
  change
    ((toBasedFunctor (P.p ≫ F)).map f) ≫
        (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T' =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T ≫
        ((toBasedFunctor (P.q ≫ G)).map f)
  exact (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.toNatTrans.naturality f

/-- Helper for Lemma 4.33.10: the left leg of the textbook factorization lies over the same base
arrow as the apex morphism in the source fibred category. -/
theorem twoFibreProduct_terminalLift_map_left_isHomLift
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    {T T' : P.obj.S}
    (f : T ⟶ T') :
    Xf.p.IsHomLift (P.obj.p.map f) ((toFunctor P.p).map f) := by
  exact inferInstance

/-- Helper for Lemma 4.33.10: the right leg of the textbook factorization lies over the same base
arrow as the apex morphism in the source fibred category. -/
theorem twoFibreProduct_terminalLift_map_right_isHomLift
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    {T T' : P.obj.S}
    (f : T ⟶ T') :
    Yf.p.IsHomLift (P.obj.p.map f) ((toFunctor P.q).map f) := by
  exact inferInstance

/-- Helper for Lemma 4.33.10: the morphism part of the textbook factorization uses the original
maps on the left and right legs. -/
noncomputable def twoFibreProduct_terminalLift_map
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    {T T' : P.obj.S}
    (f : T ⟶ T') :
    twoFibreProduct_terminalLift_obj F G P T ⟶
      twoFibreProduct_terminalLift_obj F G P T' :=
  { base := P.obj.p.map f
    a := (toFunctor P.p).map f
    a_over := twoFibreProduct_terminalLift_map_left_isHomLift F G P f
    b := (toFunctor P.q).map f
    b_over := twoFibreProduct_terminalLift_map_right_isHomLift F G P f
    comm := twoFibreProduct_terminalLift_map_comm F G P f }

/-- Helper for Lemma 4.33.10: the textbook factorization preserves identity morphisms. -/
theorem twoFibreProduct_terminalLift_map_id
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    twoFibreProduct_terminalLift_map F G P (𝟙 T) =
      𝟙 (twoFibreProduct_terminalLift_obj F G P T) := by
  -- Identity is checked on the left and right fiber components.
  apply ExplicitTwoFibreProductHom.ext
  · change (toFunctor P.p).map (𝟙 T) = 𝟙 ((toFunctor P.p).obj T)
    simp
  · change (toFunctor P.q).map (𝟙 T) = 𝟙 ((toFunctor P.q).obj T)
    simp

/-- Helper for Lemma 4.33.10: the textbook factorization preserves composition of morphisms. -/
theorem twoFibreProduct_terminalLift_map_comp
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    {T₁ T₂ T₃ : P.obj.S}
    (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
    twoFibreProduct_terminalLift_map F G P (f ≫ g) =
      twoFibreProduct_terminalLift_map F G P f ≫
        twoFibreProduct_terminalLift_map F G P g := by
  -- Composition is checked componentwise on the two projections.
  apply ExplicitTwoFibreProductHom.ext
  · change (toFunctor P.p).map (f ≫ g) =
        (toFunctor P.p).map f ≫ (toFunctor P.p).map g
    simp
  · change (toFunctor P.q).map (f ≫ g) =
        (toFunctor P.q).map f ≫ (toFunctor P.q).map g
    simp

/-- Helper for Lemma 4.33.10: the underlying based functor of the owner-level terminal lift is
the textbook factorization from Lemma 4.32.3. -/
noncomputable def twoFibreProduct_terminalLiftBased
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G) :
    P.obj.toBasedCategory ⥤ᵇ (twoFibreProduct F G).toBasedCategory :=
  { toFunctor :=
      { obj := twoFibreProduct_terminalLift_obj F G P
        map := fun f ↦ twoFibreProduct_terminalLift_map F G P f
        map_id := twoFibreProduct_terminalLift_map_id F G P
        map_comp := fun f g ↦ twoFibreProduct_terminalLift_map_comp F G P f g }
    w := rfl }

/-- Helper for Lemma 4.33.10: the textbook factorization preserves strongly cartesian arrows
because its left and right components are obtained by the strongly-cartesian-preserving maps
`P.p` and `P.q`. -/
theorem twoFibreProduct_terminalLift_preservesStronglyCartesian
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G) :
    BasedFunctor.PreservesStronglyCartesian (twoFibreProduct_terminalLiftBased F G P) := by
  intro T T' f hf
  -- Map the source strongly cartesian arrow through the two projections of the competing square.
  have hleft :
      Xf.p.IsStronglyCartesian (P.obj.p.map f) ((toFunctor P.p).map f) :=
    map_stronglyCartesian_over_base P.p hf
  have hright :
      Yf.p.IsStronglyCartesian (P.obj.p.map f) ((toFunctor P.q).map f) :=
    map_stronglyCartesian_over_base P.q hf
  -- Then the explicit pullback criterion upgrades the componentwise statement to the apex map.
  simpa [twoFibreProduct_terminalLiftBased, twoFibreProduct_terminalLift_map] using
    explicitTwoFibreProduct_hom_isStronglyCartesian_of_components
      F G (twoFibreProduct_terminalLift_map F G P f) hleft hright

/-- Helper for Lemma 4.33.10: convert a based natural transformation into the corresponding
owner morphism in the hom-category of fibred-category morphisms. -/
abbrev fibredCategoryMorHomOfBasedNatTrans
    {X Y : FibredCategoryOver C}
    {H K : X ⟶ Y}
    (η : FibredCategoryMor.toBasedFunctor H ⟶ FibredCategoryMor.toBasedFunctor K) :
    H ⟶ K :=
  ⟨ObjectProperty.homMk η, trivial⟩

/-- Helper for Lemma 4.33.10: forgetting the owner wrapper around a based natural transformation
recovers the original underlying transformation. -/
@[simp] private theorem fibredCategoryMorHomOfBasedNatTrans_hom_hom
    {X Y : FibredCategoryOver C}
    {H K : X ⟶ Y}
    (η : FibredCategoryMor.toBasedFunctor H ⟶ FibredCategoryMor.toBasedFunctor K) :
    (fibredCategoryMorHomOfBasedNatTrans η).hom.hom = η :=
  rfl

/-- Helper for Lemma 4.33.10: `2`-morphisms between morphisms of fibred categories are determined
by their objectwise underlying based natural-transformation components. -/
private theorem fibredCategoryMor_two_hom_ext
    {X Y : FibredCategoryOver C}
    {H K : X ⟶ Y}
    (η θ : H ⟶ K)
    (h : ∀ T : X.S, (η.hom.hom).app T = (θ.hom.hom).app T) :
    η = θ := by
  -- Peel the induced wrappers before comparing the underlying based natural transformations.
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  apply basedNatTrans_ext_toNatTrans
  ext T
  exact h T

/-- Helper for Lemma 4.33.10: the owner-level apex morphism underlying the textbook terminal
factorization. -/
noncomputable abbrev twoFibreProduct_terminalLift_hom
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G) :
    P.obj ⟶ twoFibreProduct F G :=
  ofBasedFunctor
    (twoFibreProduct_terminalLiftBased F G P)
    (twoFibreProduct_terminalLift_preservesStronglyCartesian F G P)

/-- Helper for Lemma 4.33.10: forgetting a right-whiskered owner `2`-morphism recovers the
right-whiskered underlying based natural transformation. -/
private theorem fibredCategoryMor_whisker_right_hom_hom
    {X Y Z : FibredCategoryOver C} {H K : X ⟶ Y}
    (η : H ⟶ K) (L : Y ⟶ Z) :
    (η ▷ L).hom.hom =
      CategoryTheory.BasedCategory.whiskerRight η.hom.hom (toBasedFunctor L) := by
  rfl

/-- Helper for Lemma 4.33.10: forgetting a left-whiskered owner `2`-morphism recovers the
left-whiskered underlying based natural transformation. -/
private theorem fibredCategoryMor_whisker_left_hom_hom
    {X Y Z : FibredCategoryOver C} (L : X ⟶ Y) {H K : Y ⟶ Z}
    (η : H ⟶ K) :
    (L ◁ η).hom.hom =
      CategoryTheory.BasedCategory.whiskerLeft (toBasedFunctor L) η.hom.hom := by
  rfl

/-- Helper for Lemma 4.33.10: after forgetting to based categories, the owner-level terminal lift
satisfies exactly the ambient square equation from Lemma 4.32.3. -/
private theorem twoFibreProduct_terminalLift_comparison_app
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    ((twoFibreProduct_terminalLiftBased F G P ◁
          (explicitTwoFibreProductBasedSquare F G).ψ.hom).app T) =
      (twoFibreProduct_terminalLift_obj F G P T).comparison := by
  rfl

/-- Helper for Lemma 4.33.10: objectwise, the forgotten owner comparison component is exactly the
stored comparison of the textbook pullback object. -/
private theorem twoFibreProduct_terminalLift_based_comparison_component
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T =
      (twoFibreProduct_terminalLift_obj F G P T).comparison := by
  -- This is just the stored comparison field of the explicit pullback object.
  exact (twoFibreProduct_terminalLift_obj_comparison F G P T).symm

/-- Helper for Lemma 4.33.10: the middle whisker in the forgotten terminal-lift square equation
evaluates objectwise to the owner comparison component. -/
private theorem twoFibreProduct_terminalLift_middle_whisker_app
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    ((twoFibreProduct_terminalLiftBased F G P ◁
          (explicitTwoFibreProductBasedSquare F G).ψ.hom).app T) =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T := by
  -- Route correction: factor through the stored comparison of the explicit pullback object rather
  -- than normalizing the whole square equation in one `simp`.
  exact
    (twoFibreProduct_terminalLift_comparison_app F G P T).trans
      (twoFibreProduct_terminalLift_based_comparison_component F G P T)

/-- Helper for Lemma 4.33.10: whiskering the identity `2`-cell on the left leg contributes no
extra component in the forgotten terminal-lift square equation. -/
private theorem twoFibreProduct_terminalLift_left_endpoint_app
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    ((((𝟙 (toBasedFunctor P.p)) ▷ (toBasedFunctor F)) ≫
          (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom).app T) =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T := by
  -- Rewrite the whiskered identity component explicitly before cancelling the identity arrow.
  change
    ((CategoryTheory.BasedCategory.whiskerRight
          (CategoryTheory.BasedNatTrans.id (toBasedFunctor P.p))
          (toBasedFunctor F)).app T) ≫
        (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T =
      (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T
  simp [CategoryTheory.BasedCategory.whiskerRight, CategoryTheory.BasedNatTrans.id]

/-- Helper for Lemma 4.33.10: the strict associator and right whisker on the forgotten right leg
do not alter the middle whisker component of the terminal-lift square equation. -/
private theorem twoFibreProduct_terminalLift_right_endpoint_app
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    (((α_ (twoFibreProduct_terminalLiftBased F G P)
          (explicitTwoFibreProductBasedSquare F G).p
          (toBasedFunctor F)).hom ≫
        twoFibreProduct_terminalLiftBased F G P ◁
          (explicitTwoFibreProductBasedSquare F G).ψ.hom ≫
        (α_ (twoFibreProduct_terminalLiftBased F G P)
          (explicitTwoFibreProductBasedSquare F G).q
          (toBasedFunctor G)).inv ≫
        ((𝟙 (toBasedFunctor P.q)) ▷ (toBasedFunctor G))).app T) =
      ((twoFibreProduct_terminalLiftBased F G P ◁
          (explicitTwoFibreProductBasedSquare F G).ψ.hom).app T) := by
  -- Expand the strict whiskers and associators pointwise, then cancel the identity endpoints.
  change
    ((((α_ (twoFibreProduct_terminalLiftBased F G P)
            (explicitTwoFibreProductBasedSquare F G).p
            (toBasedFunctor F)).hom).app T) ≫
        (((twoFibreProduct_terminalLiftBased F G P ◁
              (explicitTwoFibreProductBasedSquare F G).ψ.hom).app T) ≫
          ((((α_ (twoFibreProduct_terminalLiftBased F G P)
                  (explicitTwoFibreProductBasedSquare F G).q
                  (toBasedFunctor G)).inv).app T) ≫
            (((((𝟙 (toBasedFunctor P.q)) ▷ (toBasedFunctor G))).app T))))) =
      ((twoFibreProduct_terminalLiftBased F G P ◁
          (explicitTwoFibreProductBasedSquare F G).ψ.hom).app T)
  simp only [Bicategory.Strict.associator_eqToIso]
  change
    𝟙 _ ≫
        (twoFibreProduct_terminalLiftBased F G P ◁
            (explicitTwoFibreProductBasedSquare F G).ψ.hom).app T ≫
          𝟙 _ ≫
            (CategoryTheory.BasedCategory.whiskerRight
                (CategoryTheory.BasedNatTrans.id (toBasedFunctor P.q))
                (toBasedFunctor G)).app T =
      (twoFibreProduct_terminalLiftBased F G P ◁
          (explicitTwoFibreProductBasedSquare F G).ψ.hom).app T
  have hη :
      (CategoryTheory.BasedCategory.whiskerRight
          (CategoryTheory.BasedNatTrans.id (toBasedFunctor P.q))
          (toBasedFunctor G)).app T =
        𝟙 (((toBasedFunctor P.q).comp (toBasedFunctor G)).obj T) := by
    simp [CategoryTheory.BasedCategory.whiskerRight, CategoryTheory.BasedNatTrans.id]
  rw [hη]
  calc
    𝟙 _ ≫
          (twoFibreProduct_terminalLiftBased F G P ◁
              (explicitTwoFibreProductBasedSquare F G).ψ.hom).app T ≫
            𝟙 _ ≫ 𝟙 _ =
        (twoFibreProduct_terminalLiftBased F G P ◁
            (explicitTwoFibreProductBasedSquare F G).ψ.hom).app T ≫ 𝟙 _ := by
          simp [Category.assoc]
    _ =
        (twoFibreProduct_terminalLiftBased F G P ◁
            (explicitTwoFibreProductBasedSquare F G).ψ.hom).app T := by
          rw [Category.comp_id]

/-- Helper for Lemma 4.33.10: objectwise, the forgotten terminal-lift square equation reduces to
the comparison component carried by `P.ψ`. -/
private theorem twoFibreProduct_terminalLift_comm_on_based_app
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    ((((𝟙 (toBasedFunctor P.p)) ▷ (toBasedFunctor F)) ≫
          (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom).app T) =
      (((α_ (twoFibreProduct_terminalLiftBased F G P)
            (explicitTwoFibreProductBasedSquare F G).p
            (toBasedFunctor F)).hom ≫
          twoFibreProduct_terminalLiftBased F G P ◁
            (explicitTwoFibreProductBasedSquare F G).ψ.hom ≫
          (α_ (twoFibreProduct_terminalLiftBased F G P)
            (explicitTwoFibreProductBasedSquare F G).q
            (toBasedFunctor G)).inv ≫
          ((𝟙 (toBasedFunctor P.q)) ▷ (toBasedFunctor G))).app T) := by
  -- Normalize the left endpoint first, then reuse the already-stabilized middle whisker.
  calc
    ((((𝟙 (toBasedFunctor P.p)) ▷ (toBasedFunctor F)) ≫
          (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom).app T)
        = (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T :=
          twoFibreProduct_terminalLift_left_endpoint_app F G P T
    _ =
        (((α_ (twoFibreProduct_terminalLiftBased F G P)
              (explicitTwoFibreProductBasedSquare F G).p
              (toBasedFunctor F)).hom ≫
            twoFibreProduct_terminalLiftBased F G P ◁
              (explicitTwoFibreProductBasedSquare F G).ψ.hom ≫
            (α_ (twoFibreProduct_terminalLiftBased F G P)
              (explicitTwoFibreProductBasedSquare F G).q
              (toBasedFunctor G)).inv ≫
            ((𝟙 (toBasedFunctor P.q)) ▷ (toBasedFunctor G))).app T) := by
          -- Route correction: factor through the already-normalized middle whisker and then
          -- cancel the strict endpoint coherence pointwise.
          exact
            (twoFibreProduct_terminalLift_middle_whisker_app F G P T).symm.trans
              (twoFibreProduct_terminalLift_right_endpoint_app F G P T).symm

/-- Helper for Lemma 4.33.10: the based square equation can be evaluated on an owner object
without reintroducing coercion metavariables. -/
private theorem twoFibreProduct_terminalLift_comm_on_owner_app
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    ((((𝟙 (toBasedFunctor P.p)) ▷ (toBasedFunctor F)) ≫
          (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom).app T) =
      (((α_ (twoFibreProduct_terminalLiftBased F G P)
            (explicitTwoFibreProductBasedSquare F G).p
            (toBasedFunctor F)).hom ≫
          twoFibreProduct_terminalLiftBased F G P ◁
            (explicitTwoFibreProductBasedSquare F G).ψ.hom ≫
          (α_ (twoFibreProduct_terminalLiftBased F G P)
            (explicitTwoFibreProductBasedSquare F G).q
            (toBasedFunctor G)).inv ≫
          ((𝟙 (toBasedFunctor P.q)) ▷ (toBasedFunctor G))).app T) := by
  -- This is just the based objectwise square equation on the same underlying object.
  exact twoFibreProduct_terminalLift_comm_on_based_app F G P T

/-- Helper for Lemma 4.33.10: after forgetting to based categories, the owner-level terminal lift
satisfies exactly the ambient square equation from Lemma 4.32.3. -/
private theorem twoFibreProduct_terminalLift_comm_on_based
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G) :
    ((𝟙 (toBasedFunctor P.p)) ▷ (toBasedFunctor F)) ≫
        (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom =
      (α_ (twoFibreProduct_terminalLiftBased F G P)
          (explicitTwoFibreProductBasedSquare F G).p
          (toBasedFunctor F)).hom ≫
        twoFibreProduct_terminalLiftBased F G P ◁
          (explicitTwoFibreProductBasedSquare F G).ψ.hom ≫
        (α_ (twoFibreProduct_terminalLiftBased F G P)
          (explicitTwoFibreProductBasedSquare F G).q
          (toBasedFunctor G)).inv ≫
        ((𝟙 (toBasedFunctor P.q)) ▷ (toBasedFunctor G)) :=
by
  -- Equality of based natural transformations is checked componentwise on objects of `P.obj`.
  apply basedNatTrans_ext_toNatTrans
  ext T
  exact twoFibreProduct_terminalLift_comm_on_based_app F G P T

/-- Helper for Lemma 4.33.10: the owner-level textbook factorization satisfies the square
compatibility after forgetting to the underlying based natural transformations. -/
private theorem twoFibreProduct_terminalLift_comm_owner_left_app
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    ((((𝟙 P.p) ▷ F) ≫ P.ψ.hom).hom.hom.app T) =
      ((((𝟙 (toBasedFunctor P.p)) ▷ (toBasedFunctor F)) ≫
          (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom).app T) := by
  -- Forgetting the owner-level left side is definitionally the based left side.
  rfl

/-- Helper for Lemma 4.33.10: the owner-level right-hand side of the terminal-lift square equation
forgets objectwise to the corresponding based right-hand side. -/
private theorem twoFibreProduct_terminalLift_comm_owner_right_app
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    (((α_ (twoFibreProduct_terminalLiftBased F G P)
          (explicitTwoFibreProductBasedSquare F G).p
          (toBasedFunctor F)).hom ≫
        twoFibreProduct_terminalLiftBased F G P ◁
          (explicitTwoFibreProductBasedSquare F G).ψ.hom ≫
        (α_ (twoFibreProduct_terminalLiftBased F G P)
          (explicitTwoFibreProductBasedSquare F G).q
          (toBasedFunctor G)).inv ≫
        ((𝟙 (toBasedFunctor P.q)) ▷ (toBasedFunctor G))).app T) =
      (((α_ (twoFibreProduct_terminalLift_hom F G P)
            (twoFibreProductSquare F G).p F).hom ≫
          twoFibreProduct_terminalLift_hom F G P ◁
            (twoFibreProductSquare F G).ψ.hom ≫
          (α_ (twoFibreProduct_terminalLift_hom F G P)
            (twoFibreProductSquare F G).q G).inv ≫
          ((𝟙 P.q) ▷ G)).hom.hom.app T) := by
  -- Forgetting the owner right-hand side is definitionally the based right-hand side.
  rfl

/-- Helper for Lemma 4.33.10: objectwise, the owner-level left-hand side of the terminal-lift
square equation agrees with the already-normalized based middle term. -/
private theorem twoFibreProduct_terminalLift_comm_owner_to_based_app
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    ((((𝟙 P.p) ▷ F) ≫ P.ψ.hom).hom.hom.app T) =
      (((α_ (twoFibreProduct_terminalLiftBased F G P)
            (explicitTwoFibreProductBasedSquare F G).p
            (toBasedFunctor F)).hom ≫
          twoFibreProduct_terminalLiftBased F G P ◁
            (explicitTwoFibreProductBasedSquare F G).ψ.hom ≫
          (α_ (twoFibreProduct_terminalLiftBased F G P)
            (explicitTwoFibreProductBasedSquare F G).q
            (toBasedFunctor G)).inv ≫
          ((𝟙 (toBasedFunctor P.q)) ▷ (toBasedFunctor G))).app T) := by
  -- The verified objectwise prefix is just the owner-left normalization followed by the
  -- already-established based square equation.
  calc
    ((((𝟙 P.p) ▷ F) ≫ P.ψ.hom).hom.hom.app T)
        = ((((𝟙 (toBasedFunctor P.p)) ▷ (toBasedFunctor F)) ≫
            (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom).app T) :=
          twoFibreProduct_terminalLift_comm_owner_left_app F G P T
    _ =
        (((α_ (twoFibreProduct_terminalLiftBased F G P)
              (explicitTwoFibreProductBasedSquare F G).p
              (toBasedFunctor F)).hom ≫
            twoFibreProduct_terminalLiftBased F G P ◁
              (explicitTwoFibreProductBasedSquare F G).ψ.hom ≫
            (α_ (twoFibreProduct_terminalLiftBased F G P)
              (explicitTwoFibreProductBasedSquare F G).q
              (toBasedFunctor G)).inv ≫
            ((𝟙 (toBasedFunctor P.q)) ▷ (toBasedFunctor G))).app T) :=
          twoFibreProduct_terminalLift_comm_on_owner_app F G P T

/-- Helper for Lemma 4.33.10: the owner-level left-hand side of the textbook terminal-lift square
equation, isolated so later proofs do not repeatedly elaborate the whole whiskered expression. -/
private def twoFibreProduct_terminalLift_comm_lhs
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G) :
    P.p ≫ F ⟶ P.q ≫ G :=
  ((𝟙 P.p) ▷ F) ≫ P.ψ.hom

/-- Helper for Lemma 4.33.10: evaluating the isolated owner-level left-hand side on an object
simply recovers the corresponding component of the original whiskered square equation. -/
private theorem twoFibreProduct_terminalLift_comm_lhs_hom_hom_app
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    (twoFibreProduct_terminalLift_comm_lhs F G P).hom.hom.app T =
      ((((𝟙 P.p) ▷ F) ≫ P.ψ.hom).hom.hom.app T) := by
  rfl

/-- Helper for Lemma 4.33.10: the owner-level right-hand side of the textbook terminal-lift square
equation, isolated so later proofs do not repeatedly elaborate the whole associator chain. -/
private noncomputable def twoFibreProduct_terminalLift_comm_rhs
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G) :
    P.p ≫ F ⟶ P.q ≫ G :=
  (α_ (twoFibreProduct_terminalLift_hom F G P) (twoFibreProductSquare F G).p F).hom ≫
    twoFibreProduct_terminalLift_hom F G P ◁ (twoFibreProductSquare F G).ψ.hom ≫
    (α_ (twoFibreProduct_terminalLift_hom F G P) (twoFibreProductSquare F G).q G).inv ≫
    ((𝟙 P.q) ▷ G)

/-- Helper for Lemma 4.33.10: evaluating the isolated owner-level right-hand side on an object
recovers the corresponding component of the original whiskered associator chain. -/
private theorem twoFibreProduct_terminalLift_comm_rhs_hom_hom_app
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (T : P.obj.S) :
    (twoFibreProduct_terminalLift_comm_rhs F G P).hom.hom.app T =
      (((α_ (twoFibreProduct_terminalLift_hom F G P)
            (twoFibreProductSquare F G).p F).hom ≫
          twoFibreProduct_terminalLift_hom F G P ◁
            (twoFibreProductSquare F G).ψ.hom ≫
          (α_ (twoFibreProduct_terminalLift_hom F G P)
            (twoFibreProductSquare F G).q G).inv ≫
          ((𝟙 P.q) ▷ G)).hom.hom.app T) := by
  rfl

/-- Helper for Lemma 4.33.10: the concrete owner-level terminal-lift square equation is detected
objectwise on the underlying based natural-transformation components. -/
private theorem twoFibreProduct_terminalLift_comm_owner_ext
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (h : ∀ T : P.obj.S,
      (twoFibreProduct_terminalLift_comm_lhs F G P).hom.hom.app T =
        (twoFibreProduct_terminalLift_comm_rhs F G P).hom.hom.app T) :
    twoFibreProduct_terminalLift_comm_lhs F G P =
      twoFibreProduct_terminalLift_comm_rhs F G P := by
  -- The two concrete owner `2`-cells are determined by their objectwise based components.
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  apply basedNatTrans_ext_toNatTrans
  ext T
  exact h T

/-- Helper for Lemma 4.33.10: a based square morphism is determined by its apex map and the two
comparison `2`-cells on the projection legs. -/
private theorem based_square_hom_eq_of_fields
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P : BicategoricalTwoCommutativeSquare (B := BasedCategory C)
      (toBasedFunctor F) (toBasedFunctor G)}
    {u v : P ⟶ explicitTwoFibreProductBasedSquare F G}
    (hhom : u.hom = v.hom)
    (hleft : u.left ≍ v.left)
    (hright : u.right ≍ v.right) :
    u = v := by
  -- Unpack both square morphisms and compare the final compatibility proof by proof irrelevance.
  rcases u with ⟨uh, ul, ur, uc⟩
  rcases v with ⟨vh, vl, vr, vc⟩
  cases hhom
  cases hleft
  cases hright
  have hcomm : uc = vc := Subsingleton.elim _ _
  cases hcomm
  rfl

/-- Helper for Lemma 4.33.10: forgetting the owner square equation all the way down to based
natural transformations yields the exact ambient square equation needed for the owner-to-based
transport step. -/
private theorem owner_square_comm_hom_hom
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : P ⟶ twoFibreProductSquare F G) :
    (fun α ↦ α.hom.hom) (u.left ▷ F ≫ P.ψ.hom) =
      (fun α ↦ α.hom.hom)
        ((α_ u.hom (twoFibreProductSquare F G).p F).hom ≫
          u.hom ◁ (twoFibreProductSquare F G).ψ.hom ≫
          (α_ u.hom (twoFibreProductSquare F G).q G).inv ≫
          u.right ▷ G) := by
  -- Forget the owner square equation to the underlying based natural transformations.
  exact congrArg (fun α => α.hom.hom) u.comm

/-- Helper for Lemma 4.33.10: the owner-level terminal factorization through the explicit
two-fibre-product square. -/
noncomputable def twoFibreProduct_terminalLift
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G) :
    P ⟶ twoFibreProductSquare F G :=
  { hom :=
      twoFibreProduct_terminalLift_hom F G P
    left := 𝟙 P.p
    right := 𝟙 P.q
    comm := by
      -- Equality of owner `2`-cells is checked objectwise after forgetting to based natural
      -- transformations.
      repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
      apply basedNatTrans_ext_toNatTrans
      ext T
      exact
        (twoFibreProduct_terminalLift_comm_on_owner_app F G P T).trans
          (twoFibreProduct_terminalLift_comm_owner_right_app F G P T) }

/-- Helper for Lemma 4.33.10: the forgotten owner square equation is exactly the ambient square
equation for the packaged based-square morphism. -/
theorem owner_hom_to_based_square_hom_comm
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : P ⟶ twoFibreProductSquare F G) :
    (u.left.hom.hom ▷ (toBasedFunctor F)) ≫
        (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom =
      (α_ (FibredCategoryMor.toBasedFunctor u.hom)
          (explicitTwoFibreProductBasedSquare F G).p
          (toBasedFunctor F)).hom ≫
        FibredCategoryMor.toBasedFunctor u.hom ◁
          (explicitTwoFibreProductBasedSquare F G).ψ.hom ≫
        (α_ (FibredCategoryMor.toBasedFunctor u.hom)
          (explicitTwoFibreProductBasedSquare F G).q
          (toBasedFunctor G)).inv ≫
        (u.right.hom.hom ▷ (toBasedFunctor G)) := by
  -- The ambient square equation is exactly the full forgetting of the owner square equation.
  exact owner_square_comm_hom_hom F G u

/-- Helper for Lemma 4.33.10: forget an owner morphism into the fibred two-fibre-product square
to the corresponding ambient morphism into the based explicit pullback square. -/
noncomputable def owner_hom_to_based_square_hom
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P : BicategoricalTwoCommutativeSquare F G}
    (u : P ⟶ twoFibreProductSquare F G) :
    toBasedSquare F G P ⟶
      explicitTwoFibreProductBasedSquare F G :=
  { hom := FibredCategoryMor.toBasedFunctor u.hom
    left := u.left.hom.hom
    right := u.right.hom.hom
    comm := owner_hom_to_based_square_hom_comm F G u }

/-- Helper for Lemma 4.33.10: forgetting the owner terminal lift recovers the ambient terminal
factorization in the based square-hom category from Lemma 4.32.3. -/
private theorem explicitTwoFibreProductBasedSquare_isFinal
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    : Bicategory.IsFinal (explicitTwoFibreProductBasedSquare F G) := by
  simpa [explicitTwoFibreProductBasedSquare] using
    (CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct.{u, v, max u v, max u v}
      (X := Xf.toBasedCategory) (Y := Yf.toBasedCategory) (S := Sf.toBasedCategory)
      (show Xf.toBasedCategory ⟶ Sf.toBasedCategory from toBasedFunctor F)
      (show Yf.toBasedCategory ⟶ Sf.toBasedCategory from toBasedFunctor G))

/-- Helper for Lemma 4.33.10: forgetting the owner terminal lift recovers a terminal object in the
ambient based square-hom category. -/
noncomputable def twoFibreProduct_terminalLift_forget_isTerminal
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G) :
    Limits.IsTerminal
      (owner_hom_to_based_square_hom F G (twoFibreProduct_terminalLift F G P) :
        toBasedSquare F G P ⟶ explicitTwoFibreProductBasedSquare F G) := by
  -- Route correction: mirror the Lemma 4.32.3 universal property directly in the ambient based
  -- square-hom category, with the forgotten owner lift as the concrete terminal object.
  let target :
      toBasedSquare F G P ⟶ explicitTwoFibreProductBasedSquare F G :=
    owner_hom_to_based_square_hom F G (twoFibreProduct_terminalLift F G P)
  let canonical
      (u : toBasedSquare F G P ⟶ explicitTwoFibreProductBasedSquare F G) :
      u ⟶ target := by
    let component :
        ∀ T : P.obj.S, u.hom.obj T ⟶ twoFibreProduct_terminalLift_obj F G P T :=
      fun T ↦
        let hleft :
            Xf.p.IsHomLift (eqToHom (u.hom.w_obj T)) (u.left.app T) := by
          let hs :
              Xf.p.obj ((u.hom ≫ (explicitTwoFibreProductBasedSquare F G).p).obj T) =
                (u.hom.obj T).U := by
            simpa [explicitTwoFibreProductBasedSquare, CategoryOver.explicitTwoFibreProductSquare,
              CategoryOver.explicitTwoFibreProductLeftProjection,
              CategoryOver.explicitTwoFibreProduct] using
              (u.hom.obj T).obj.fst.2
          let ht : Xf.p.obj ((toBasedFunctor P.p).obj T) = P.obj.p.obj T :=
            BasedFunctor.w_obj (toBasedFunctor P.p) T
          refine IsHomLift.of_fac' Xf.p (eqToHom (u.hom.w_obj T)) (u.left.app T) hs ht ?_
          have hfac := IsHomLift.fac' Xf.p (𝟙 (P.obj.p.obj T)) (u.left.app T)
          simpa [hs, ht, Category.assoc] using hfac
        let hright :
            Yf.p.IsHomLift (eqToHom (u.hom.w_obj T)) (u.right.app T) := by
          let hs :
              Yf.p.obj ((u.hom ≫ (explicitTwoFibreProductBasedSquare F G).q).obj T) =
                (u.hom.obj T).U := by
            simpa [explicitTwoFibreProductBasedSquare, CategoryOver.explicitTwoFibreProductSquare,
              CategoryOver.explicitTwoFibreProductRightProjection,
              CategoryOver.explicitTwoFibreProduct] using
              (u.hom.obj T).obj.snd.2
          let ht : Yf.p.obj ((toBasedFunctor P.q).obj T) = P.obj.p.obj T :=
            BasedFunctor.w_obj (toBasedFunctor P.q) T
          refine IsHomLift.of_fac' Yf.p (eqToHom (u.hom.w_obj T)) (u.right.app T) hs ht ?_
          have hfac := IsHomLift.fac' Yf.p (𝟙 (P.obj.p.obj T)) (u.right.app T)
          simpa [hs, ht, Category.assoc] using hfac
        have hcomm :
            (toFunctor F).map (u.left.app T) ≫
                (twoFibreProduct_terminalLift_obj F G P T).comparison =
              (u.hom.obj T).comparison ≫ (toFunctor G).map (u.right.app T) := by
          have hsquare :=
            congrArg (fun τ => τ.app T) (congrArg BasedNatTrans.toNatTrans u.comm)
          have hleft_side :
              ((u.left ▷ (toBasedFunctor F)) ≫
                  (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom).app T =
                (toFunctor F).map (u.left.app T) ≫
                  (twoFibreProduct_terminalLift_obj F G P T).comparison := by
            change (toFunctor F).map (u.left.app T) ≫
                (FibredCategoryMor.basedFunctorIsoOfOwnerIso P.ψ).hom.app T =
              (toFunctor F).map (u.left.app T) ≫
                (twoFibreProduct_terminalLift_obj F G P T).comparison
            rfl
          have hright_side :
              ((α_ u.hom (explicitTwoFibreProductBasedSquare F G).p
                    (toBasedFunctor F)).hom ≫
                  u.hom ◁ (explicitTwoFibreProductBasedSquare F G).ψ.hom ≫
                  (α_ u.hom (explicitTwoFibreProductBasedSquare F G).q
                    (toBasedFunctor G)).inv ≫
                  (u.right ▷ (toBasedFunctor G))).app T =
                (u.hom.obj T).comparison ≫ (toFunctor G).map (u.right.app T) := by
            simp [explicitTwoFibreProductBasedSquare, CategoryOver.explicitTwoFibreProductSquare,
              CategoryOver.explicitTwoFibreProductComparisonIsoOver,
              CategoryOver.explicitTwoFibreProductLeftProjection,
              CategoryOver.explicitTwoFibreProductRightProjection,
              CategoryOver.explicitTwoFibreProduct, Bicategory.Strict.associator_eqToIso]
            rfl
          exact hleft_side.symm.trans (hsquare.trans hright_side)
        { base := eqToHom (u.hom.w_obj T)
          a := u.left.app T
          a_over := hleft
          b := u.right.app T
          b_over := hright
          comm := ⟨hcomm⟩ }
    have component_naturality :
        ∀ {T T' : P.obj.S} (f : T ⟶ T'),
          u.hom.map f ≫ component T' =
            component T ≫ twoFibreProduct_terminalLift_map F G P f := by
      intro T T' f
      -- The explicit pullback morphism is determined by its left and right components.
      apply ExplicitTwoFibreProductHom.ext
      · simpa [component, twoFibreProduct_terminalLift_map, explicitTwoFibreProductBasedSquare,
          CategoryOver.explicitTwoFibreProductSquare,
          CategoryOver.explicitTwoFibreProductLeftProjection,
          CategoryOver.explicitTwoFibreProduct] using
          u.left.toNatTrans.naturality f
      · simpa [component, twoFibreProduct_terminalLift_map, explicitTwoFibreProductBasedSquare,
          CategoryOver.explicitTwoFibreProductSquare,
          CategoryOver.explicitTwoFibreProductRightProjection,
          CategoryOver.explicitTwoFibreProduct] using
          u.right.toNatTrans.naturality f
    have component_isHomLift :
        ∀ T : P.obj.S,
          (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsHomLift
            (𝟙 (P.obj.p.obj T)) (component T) := by
      intro T
      -- The component is vertical in the explicit pullback because its stored base is
      -- `eqToHom (u.hom.w_obj T)`.
      refine
        IsHomLift.of_fac'
          (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p
          (𝟙 (P.obj.p.obj T)) (component T) (u.hom.w_obj T) rfl ?_
      rw [explicitTwoFibreProduct_base_projection_map]
      -- The remaining endpoint transport is a pure `eqToHom` normalization.
      aesop
    let homη : u.hom ⟶ twoFibreProduct_terminalLiftBased F G P :=
      { toNatTrans :=
          { app := component
            naturality := fun {_ _} f ↦ component_naturality f }
        isHomLift' := component_isHomLift }
    have left_comm_app :
        ∀ T : P.obj.S,
          ((homη ▷ (explicitTwoFibreProductBasedSquare F G).p ≫ target.left).app T) =
            u.left.app T := by
      intro T
      -- The left leg of the forgotten owner lift is the identity on `P.p`.
      simpa [target, owner_hom_to_based_square_hom, twoFibreProduct_terminalLift] using
        (by
          change ((homη ▷ (explicitTwoFibreProductBasedSquare F G).p).app T) ≫
              ((𝟙 (toBasedFunctor P.p) : toBasedFunctor P.p ⟶ toBasedFunctor P.p).app T) =
                u.left.app T
          have hid :
              ((homη ▷ (explicitTwoFibreProductBasedSquare F G).p).app T) ≫
                  𝟙 ((toBasedFunctor P.p).obj T) =
                ((homη ▷ (explicitTwoFibreProductBasedSquare F G).p).app T) := by
            exact Category.comp_id _
          simpa [homη, component] using hid.trans (rfl :
            ((homη ▷ (explicitTwoFibreProductBasedSquare F G).p).app T) = u.left.app T))
    have right_comm_app :
        ∀ T : P.obj.S,
          ((homη ▷ (explicitTwoFibreProductBasedSquare F G).q ≫ target.right).app T) =
            u.right.app T := by
      intro T
      -- The right leg is identical for the same reason.
      simpa [target, owner_hom_to_based_square_hom, twoFibreProduct_terminalLift] using
        (by
          change ((homη ▷ (explicitTwoFibreProductBasedSquare F G).q).app T) ≫
              ((𝟙 (toBasedFunctor P.q) : toBasedFunctor P.q ⟶ toBasedFunctor P.q).app T) =
                u.right.app T
          have hid :
              ((homη ▷ (explicitTwoFibreProductBasedSquare F G).q).app T) ≫
                  𝟙 ((toBasedFunctor P.q).obj T) =
                ((homη ▷ (explicitTwoFibreProductBasedSquare F G).q).app T) := by
            exact Category.comp_id _
          simpa [homη, component] using hid.trans (rfl :
            ((homη ▷ (explicitTwoFibreProductBasedSquare F G).q).app T) = u.right.app T))
    exact
      { hom := homη
        left_comm := by
          apply basedNatTrans_ext_toNatTrans
          ext T
          exact left_comm_app T
        right_comm := by
          apply basedNatTrans_ext_toNatTrans
          ext T
          exact right_comm_app T }
  refine Limits.IsTerminal.ofUniqueHom (fun u ↦ canonical u) ?_
  intro u η
  -- Uniqueness is detected on the apex transformation, and then objectwise on the two pullback
  -- projections.
  apply BicategoricalTwoCommutativeSquare.TwoHom.ext
  apply basedNatTrans_ext_toNatTrans
  ext T
  apply ExplicitTwoFibreProductHom.ext
  · have hη := congrArg BasedNatTrans.toNatTrans η.left_comm
    have hηT := congrArg (fun τ => τ.app T) hη
    have hηT' :
        ((η.hom ▷ (explicitTwoFibreProductBasedSquare F G).p).app T) = u.left.app T := by
      change ((η.hom ▷ (explicitTwoFibreProductBasedSquare F G).p).app T) ≫
          ((((𝟙 P.p : P.p ⟶ P.p).hom.hom) : toBasedFunctor P.p ⟶ toBasedFunctor P.p).app T) =
        u.left.app T at hηT
      have hid :
          ((η.hom ▷ (explicitTwoFibreProductBasedSquare F G).p).app T) =
            ((η.hom ▷ (explicitTwoFibreProductBasedSquare F G).p).app T) ≫
              𝟙 ((toBasedFunctor P.p).obj T) := by
        exact (Category.comp_id _).symm
      simpa [target, owner_hom_to_based_square_hom, twoFibreProduct_terminalLift] using
        hid.trans hηT
    -- The left compatibility identifies the `a`-component with the original left comparison map.
    change ((η.hom ▷ (explicitTwoFibreProductBasedSquare F G).p).app T) =
      ((canonical u).hom.app T).a
    simpa [canonical] using hηT'
  · have hη := congrArg BasedNatTrans.toNatTrans η.right_comm
    have hηT := congrArg (fun τ => τ.app T) hη
    have hηT' :
        ((η.hom ▷ (explicitTwoFibreProductBasedSquare F G).q).app T) = u.right.app T := by
      change ((η.hom ▷ (explicitTwoFibreProductBasedSquare F G).q).app T) ≫
          ((((𝟙 P.q : P.q ⟶ P.q).hom.hom) : toBasedFunctor P.q ⟶ toBasedFunctor P.q).app T) =
        u.right.app T at hηT
      have hid :
          ((η.hom ▷ (explicitTwoFibreProductBasedSquare F G).q).app T) =
            ((η.hom ▷ (explicitTwoFibreProductBasedSquare F G).q).app T) ≫
              𝟙 ((toBasedFunctor P.q).obj T) := by
        exact (Category.comp_id _).symm
      simpa [target, owner_hom_to_based_square_hom, twoFibreProduct_terminalLift] using
        hid.trans hηT
    -- The right compatibility identifies the `b`-component with the original right comparison
    -- map.
    change ((η.hom ▷ (explicitTwoFibreProductBasedSquare F G).q).app T) =
      ((canonical u).hom.app T).b
    simpa [canonical] using hηT'

/-- Helper for Lemma 4.33.10: the repackaged ambient `2`-morphism satisfies the owner left-leg
compatibility automatically after forgetting. -/
theorem owner_twoHom_of_based_square_twoHom_left_comm
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ twoFibreProductSquare F G}
    (η : owner_hom_to_based_square_hom F G u ⟶ owner_hom_to_based_square_hom F G v) :
    (fibredCategoryMorHomOfBasedNatTrans η.hom ▷ (twoFibreProductSquare F G).p) ≫ v.left = u.left := by
  -- Strip the owner wrappers until only the underlying based square equation remains.
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  change
    CategoryTheory.BasedCategory.whiskerRight η.hom (toBasedFunctor ((twoFibreProductSquare F G).p)) ≫
        v.left.hom.hom =
      u.left.hom.hom
  exact η.left_comm

/-- Helper for Lemma 4.33.10: the repackaged ambient `2`-morphism also satisfies the owner
right-leg compatibility after forgetting. -/
theorem owner_twoHom_of_based_square_twoHom_right_comm
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ twoFibreProductSquare F G}
    (η : owner_hom_to_based_square_hom F G u ⟶ owner_hom_to_based_square_hom F G v) :
    (fibredCategoryMorHomOfBasedNatTrans η.hom ▷ (twoFibreProductSquare F G).q) ≫ v.right = u.right := by
  -- The right leg is identical after forgetting to the underlying based square morphism.
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  change
    CategoryTheory.BasedCategory.whiskerRight η.hom (toBasedFunctor ((twoFibreProductSquare F G).q)) ≫
        v.right.hom.hom =
      u.right.hom.hom
  exact η.right_comm

/-- Helper for Lemma 4.33.10: repackage an ambient based-square `2`-morphism as an owner-level
`2`-morphism between square morphisms of fibred categories. -/
noncomputable def owner_twoHom_of_based_square_twoHom
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P : BicategoricalTwoCommutativeSquare F G}
    {u v : P ⟶ twoFibreProductSquare F G}
    (η : owner_hom_to_based_square_hom F G u ⟶ owner_hom_to_based_square_hom F G v) :
    u ⟶ v :=
  { hom := fibredCategoryMorHomOfBasedNatTrans η.hom
    left_comm := owner_twoHom_of_based_square_twoHom_left_comm F G η
    right_comm := owner_twoHom_of_based_square_twoHom_right_comm F G η }

/-- Helper for Lemma 4.33.10: the ambient terminal `2`-cell out of a competing owner morphism,
repackaged back into the owner hom-category. -/
noncomputable def twoFibreProduct_terminalLift_from
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ twoFibreProductSquare F G) :
    u ⟶ twoFibreProduct_terminalLift F G P :=
  owner_twoHom_of_based_square_twoHom F G
    ((twoFibreProduct_terminalLift_forget_isTerminal F G P).from
      (owner_hom_to_based_square_hom F G u))

/-- Helper for Lemma 4.33.10: any owner `2`-morphism into the textbook factorization is forced by
the ambient terminality of the forgotten based square. -/
theorem twoFibreProduct_terminalLift_from_eq
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G)
    (u : P ⟶ twoFibreProductSquare F G)
    (η : u ⟶ twoFibreProduct_terminalLift F G P) :
    η = twoFibreProduct_terminalLift_from F G P u := by
  let η' :
      owner_hom_to_based_square_hom F G u ⟶
        owner_hom_to_based_square_hom F G (twoFibreProduct_terminalLift F G P) :=
    { hom := η.hom.hom.hom
      left_comm := by
        -- Forget the owner left compatibility to the corresponding based square equation.
        exact congrArg (fun α => α.hom.hom) η.left_comm
      right_comm := by
        -- The right compatibility behaves identically after forgetting.
        exact congrArg (fun α => α.hom.hom) η.right_comm }
  have hη' :
      η' =
        (twoFibreProduct_terminalLift_forget_isTerminal F G P).from
          (owner_hom_to_based_square_hom F G u) := by
    -- Downstairs terminality forces the forgotten `2`-morphism uniquely.
    exact (twoFibreProduct_terminalLift_forget_isTerminal F G P).hom_ext η' _
  -- Repackage the ambient uniqueness statement upstairs and compare only the apex transformation.
  apply BicategoricalTwoCommutativeSquare.TwoHom.ext
  repeat first | apply InducedWideCategory.Hom.ext | apply InducedCategory.Hom.ext
  change η'.hom = (twoFibreProduct_terminalLift_from F G P u).hom.hom.hom
  exact congrArg (fun ζ => ζ.hom) hη'

/-- Helper for Lemma 4.33.10: the owner-level terminal factorization is terminal in the fixed
hom-category of squares into the canonical fibred two-fibre product. -/
noncomputable def twoFibreProduct_terminalLift_isTerminal
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G) :
    Limits.IsTerminal
      (twoFibreProduct_terminalLift F G P : P ⟶ twoFibreProductSquare F G) :=
  Limits.IsTerminal.ofUniqueHom
    (fun u ↦ twoFibreProduct_terminalLift_from F G P u)
    (fun u η ↦ twoFibreProduct_terminalLift_from_eq F G P u η)

/-- Helper for Lemma 4.33.10: for any competing fibred square `P`, the hom-category into the
canonical fibred two-fibre-product square has a terminal object given by the textbook terminal
lift. -/
private theorem twoFibreProductSquare_hasTerminal
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : BicategoricalTwoCommutativeSquare F G) :
    Limits.HasTerminal
      (BicategoricalTwoCommutativeSquare.Hom P (twoFibreProductSquare F G)) := by
  -- Freeze the hom-category first, then reuse the already-proved owner-level terminality.
  change Limits.HasTerminal (P ⟶ twoFibreProductSquare F G)
  exact (twoFibreProduct_terminalLift_isTerminal F G P).hasTerminal

-- Proof sketch: the explicit apex from Lemma `4.32.3` is fibred by
-- `explicitTwoFibreProductProjection_isFibered`, and the two ambient projection functors are
-- upgraded here to `FibredCategoryMor`s by the strongly-cartesian-preservation results above.
-- The terminal factorization in the bicategory of fibred categories is then obtained by refining
-- the ambient `Cat/C` factorization so that the induced apex map also preserves strongly
-- cartesian morphisms.
/-- Lemma 4.33.10: for morphisms of fibred categories over `C`, the canonical explicit square of
Lemma 4.32.3 is a bicategorical `2`-fibre product square in `FibredCategoryOver C`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := by
  -- Route correction: rebuild the textbook terminal lift as a morphism of fibred categories, then
  -- transport terminality from the ambient square-hom category by forgetting and rewrapping
  -- based natural transformations.
  refine ⟨fun (P : BicategoricalTwoCommutativeSquare F G) ↦ ?_⟩
  -- The remaining work is only the terminal-object packaging in the fixed owner hom-category.
  exact twoFibreProductSquare_hasTerminal F G P

end FibredCategoryOver

end CategoryTheory
