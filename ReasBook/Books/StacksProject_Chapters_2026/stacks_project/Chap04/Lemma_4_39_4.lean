module

public import stacks_project.Chap04.Definition_4_39_3
public import stacks_project.Chap04.Lemma_4_35_2
public import stacks_project.Chap04.Lemma_4_32_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryTheory.Limits
open CategoryOver
open scoped Bicategory
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {X Y S : FibredInSetoidsOver.{u, v, max u v, v} C}

set_option maxHeartbeats 10000000

/- Domain-style sampling for Lemma 4.39.4:
- primary domain: categories fibred in setoids over a fixed base and their bicategorical
  `2`-fibre products;
- inspected owner-level declarations:
  `IsFibredInSetoids`,
  `FibredInSetoidsOver`,
  `CategoryOver.explicitTwoFibreProductSquare`,
  `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`;
- best owner abstraction: the source-facing owner data already lives in the explicit pullback over
  `Cat/C`, so this file should keep only the setoid-valued rebundling and its inherited
  bicategorical universal property.

Primitive-vs-derived split:
- primitive source-facing data: the morphisms `F : X ⟶ S` and `G : Y ⟶ S`;
- derived API: the closure theorem asserting that the explicit pullback projection is again fibred
  in setoids, the rebundled owner `FibredInSetoidsOver.twoFibreProduct`, the canonical square, and
  the inherited finality statement.

Source/core/bridge triage:
- `source-facing`: `FibredInSetoidsOver.twoFibreProductSquare` and
  `FibredInSetoidsOver.twoFibreProduct_isTwoFibreProduct`;
- `core/canonical`: `CategoryOver.explicitTwoFibreProductSquare` and
  `CategoryOver.explicitTwoFibreProduct_isTwoFibreProduct`;
- `bridge/view`: the owner-level rebundling through `FibredInSetoidsOver.ofFunctor`,
  `FibredInSetoidsOver.ofAmbientHom`, and `FibredInSetoidsOver.ofAmbientIso`. -/

section FibredCategoryPullback

open FibredCategoryMor

variable {Xf Yf Sf : FibredCategoryOver C}

/-- Helper for Lemma 4.39.4: a morphism of fibred categories sends a strongly cartesian lift over
the chosen base arrow to a strongly cartesian lift over the same base arrow. -/
private theorem map_stronglyCartesian_over_base
    {A B : FibredCategoryOver C} (H : A ⟶ B)
    {U V : C} {a b : A.S} {f : U ⟶ V} {φ : a ⟶ b}
    (hφ : A.p.IsStronglyCartesian f φ) :
    B.p.IsStronglyCartesian f ((toFunctor H).map φ) := by
  -- Rewrite the source lift to the projected base so the owner preservation theorem applies.
  have hφ' : A.p.IsStronglyCartesian (A.p.map φ) φ := by
    letI : A.p.IsStronglyCartesian f φ := hφ
    subst_hom_lift A.p f φ
    simpa using hφ
  have hmap :
      B.p.IsStronglyCartesian (B.p.map ((toFunctor H).map φ)) ((toFunctor H).map φ) :=
    FibredCategoryMor.map_stronglyCartesian H φ hφ'
  -- Then transport the target lift back to the original chosen base arrow `f`.
  have hLift : B.p.IsHomLift f ((toFunctor H).map φ) := by
    letI : A.p.IsHomLift f φ := hφ.toIsHomLift
    exact show B.p.IsHomLift f ((toFunctor H).map φ) from inferInstance
  letI : B.p.IsHomLift f ((toFunctor H).map φ) := hLift
  subst_hom_lift B.p f ((toFunctor H).map φ)
  simpa using hmap

/-- Helper for Lemma 4.39.4: if a morphism is strongly cartesian for one chosen lift of its base
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

/-- Helper for Lemma 4.39.4: an external lift witness upgrades strong cartesianness back to the
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

/-- Helper for Lemma 4.39.4: the base projection of a morphism in the explicit pullback is its
stored `base` field. -/
private theorem explicitTwoFibreProduct_base_projection_map
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    {P Q : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj}
    (φ : P ⟶ Q) :
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.map φ = φ.base := by
  rfl

/-- Helper for Lemma 4.39.4: a lift for the projection of the explicit pullback has base arrow
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

/-- Helper for Lemma 4.39.4: a lift in the explicit pullback induces the corresponding lift on
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

/-- Helper for Lemma 4.39.4: a lift in the explicit pullback induces the corresponding lift on
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

/-- Helper for Lemma 4.39.4: a morphism in the explicit pullback is strongly cartesian whenever
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

/-- Helper for Lemma 4.39.4: the comparison carried by an explicit pullback object is an
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

/-- Helper for Lemma 4.39.4: the chosen pullback of the left component of `P` along `f`, viewed
as an object of the standard fiber of `Xf` over the new base. -/
private noncomputable def explicitTwoFibreProduct_left_pullback
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    Xf.p.Fiber V :=
  let _ : HasFibers Xf.p := HasFibers.canonical Xf.p
  let a := HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2
  Functor.Fiber.mk (IsHomLift.domain_eq Xf.p f a)

/-- Helper for Lemma 4.39.4: the chosen pullback map of the left component of `P` along `f`. -/
private noncomputable def explicitTwoFibreProduct_left_pullback_map
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    (explicitTwoFibreProduct_left_pullback F G P f).1 ⟶ P.obj.fst.1 :=
  let _ : HasFibers Xf.p := HasFibers.canonical Xf.p
  let a := HasFibers.pullbackMap (p := Xf.p) f P.obj.fst.2
  show (explicitTwoFibreProduct_left_pullback F G P f).1 ⟶ P.obj.fst.1 from a

/-- Helper for Lemma 4.39.4: the chosen pullback of the right component of `P` along `f`, viewed
as an object of the standard fiber of `Yf` over the new base. -/
private noncomputable def explicitTwoFibreProduct_right_pullback
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    Yf.p.Fiber V :=
  let _ : HasFibers Yf.p := HasFibers.canonical Yf.p
  let b := HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2
  Functor.Fiber.mk (IsHomLift.domain_eq Yf.p f b)

/-- Helper for Lemma 4.39.4: the chosen pullback map of the right component of `P` along `f`. -/
private noncomputable def explicitTwoFibreProduct_right_pullback_map
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf)
    (P : (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).obj)
    {V : C} (f : V ⟶ P.U) :
    (explicitTwoFibreProduct_right_pullback F G P f).1 ⟶ P.obj.snd.1 :=
  let _ : HasFibers Yf.p := HasFibers.canonical Yf.p
  let b := HasFibers.pullbackMap (p := Yf.p) f P.obj.snd.2
  show (explicitTwoFibreProduct_right_pullback F G P f).1 ⟶ P.obj.snd.1 from b

/-- Helper for Lemma 4.39.4: pulling back the two components of an explicit pullback object along
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
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      Sf.p
      (g := Iso.refl V)
      hf
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

/-- Helper for Lemma 4.39.4: every base arrow into an explicit pullback object admits the
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
  have hf : f = (Iso.refl V).hom ≫ f := by
    simp
  let e :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso
      Sf.p
      (g := Iso.refl V)
      hf
      ((toFunctor G).map b)
      ((toFunctor F).map a ≫ P.comparison)
  have hfac :
      e.hom ≫ (toFunctor G).map b = (toFunctor F).map a ≫ P.comparison := by
    change
      (Functor.IsStronglyCartesian.domainIsoOfBaseIso
          Sf.p
          hf
          ((toFunctor G).map b)
          ((toFunctor F).map a ≫ P.comparison)).hom ≫
        (toFunctor G).map b =
          (toFunctor F).map a ≫ P.comparison
    exact
      Functor.IsStronglyCartesian.fac
        Sf.p
        f
        ((toFunctor G).map b)
        hf
        ((toFunctor F).map a ≫ P.comparison)
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

/-- Helper for Lemma 4.39.4: the explicit pullback projection is fibred for morphisms of fibred
categories over `C`. -/
private theorem explicitTwoFibreProductProjection_isFibered
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsFibered := by
  -- Prove fibredness from the textbook pullback construction itself.
  refine Functor.IsFibered.of_exists_isStronglyCartesian ?_
  intro P V f
  obtain ⟨Q, η, _, _, hη⟩ := explicitTwoFibreProduct_exists_isStronglyCartesian F G P f
  exact ⟨Q, η, hη⟩

end FibredCategoryPullback

namespace FibredInSetoidsOver

/-- Helper for Lemma 4.39.4: the explicit pullback of the underlying based functors of `F` and
`G` over `C`. -/
noncomputable abbrev explicitTwoFibreProductOver
    (F : X ⟶ S) (G : Y ⟶ S) :
    BasedCategory C :=
  CategoryOver.explicitTwoFibreProduct
    (FibredInSetoidsOver.toBasedFunctor F)
    (FibredInSetoidsOver.toBasedFunctor G)

/-- Helper for Lemma 4.39.4: a morphism in the fibre of the explicit `2`-fibre product over `U`
has left component lying over the identity of `U`. -/
private theorem explicitTwoFibreProduct_fiber_left_over_id
    (F : X ⟶ S) (G : Y ⟶ S)
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProductOver F G).p U}
    (φ : P ⟶ Q) :
    X.p.IsHomLift (𝟙 U) φ.1.a := by
  -- After normalizing the outer fibre equalities, the stored left component is visibly vertical.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  letI : (explicitTwoFibreProductOver F G).p.IsHomLift (𝟙 UP) φ.1 := φ.2
                  have hbase : φ.1.base = 𝟙 UP := by
                    simpa [explicitTwoFibreProductOver] using
                      (IsHomLift.fac' ((explicitTwoFibreProductOver F G).p) (𝟙 UP) φ.1)
                  simpa [hbase, explicitTwoFibreProductOver] using φ.1.a_over

/-- Helper for Lemma 4.39.4: a morphism in the fibre of the explicit `2`-fibre product over `U`
has right component lying over the identity of `U`. -/
private theorem explicitTwoFibreProduct_fiber_right_over_id
    (F : X ⟶ S) (G : Y ⟶ S)
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProductOver F G).p U}
    (φ : P ⟶ Q) :
    Y.p.IsHomLift (𝟙 U) φ.1.b := by
  -- The right component is treated by the same outer-fibre normalization.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  letI : (explicitTwoFibreProductOver F G).p.IsHomLift (𝟙 UP) φ.1 := φ.2
                  have hbase : φ.1.base = 𝟙 UP := by
                    simpa [explicitTwoFibreProductOver] using
                      (IsHomLift.fac' ((explicitTwoFibreProductOver F G).p) (𝟙 UP) φ.1)
                  simpa [hbase, explicitTwoFibreProductOver] using φ.1.b_over

/-- Helper for Lemma 4.39.4: each fibre of the explicit `2`-fibre product projection is thin. -/
private theorem explicitTwoFibreProduct_fiber_isThin
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    Quiver.IsThin ((explicitTwoFibreProductOver F G).p.Fiber U) := by
  intro P Q
  refine ⟨fun φ ψ ↦ ?_⟩
  -- Equality of fibre morphisms is detected on the left and right fibre components.
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  apply Functor.Fiber.hom_ext
                  apply ExplicitTwoFibreProductHom.ext
                  · let φfst : Pobj.fst ⟶ Qobj.fst :=
                        ⟨φ.1.a, explicitTwoFibreProduct_fiber_left_over_id F G φ⟩
                    let ψfst : Pobj.fst ⟶ Qobj.fst :=
                        ⟨ψ.1.a, explicitTwoFibreProduct_fiber_left_over_id F G ψ⟩
                    exact congrArg (fun f ↦ f.1) (Subsingleton.elim φfst ψfst)
                  · let φsnd : Pobj.snd ⟶ Qobj.snd :=
                        ⟨φ.1.b, explicitTwoFibreProduct_fiber_right_over_id F G φ⟩
                    let ψsnd : Pobj.snd ⟶ Qobj.snd :=
                        ⟨ψ.1.b, explicitTwoFibreProduct_fiber_right_over_id F G ψ⟩
                    exact congrArg (fun f ↦ f.1) (Subsingleton.elim φsnd ψsnd)

/-- Helper for Lemma 4.39.4: every morphism in a fibre of the explicit pullback projection is an
isomorphism. -/
private theorem explicitTwoFibreProduct_fiber_hom_isIso
    (F : X ⟶ S) (G : Y ⟶ S)
    {U : C} {P Q : Functor.Fiber (explicitTwoFibreProductOver F G).p U}
    (φ : P ⟶ Q) : IsIso φ := by
  cases P with
  | mk P hP =>
      cases Q with
      | mk Q hQ =>
          cases P with
          | mk UP Pobj =>
              cases Q with
              | mk UQ Qobj =>
                  cases hP
                  cases hQ
                  let φfst : Pobj.fst ⟶ Qobj.fst :=
                    ⟨φ.1.a, explicitTwoFibreProduct_fiber_left_over_id F G φ⟩
                  let φsnd : Pobj.snd ⟶ Qobj.snd :=
                    ⟨φ.1.b, explicitTwoFibreProduct_fiber_right_over_id F G φ⟩
                  let ψfst : Qobj.fst ⟶ Pobj.fst := inv φfst
                  let ψsnd : Qobj.snd ⟶ Pobj.snd := inv φsnd
                  let eA : Pobj.fst.1 ≅ Qobj.fst.1 :=
                    { hom := φfst.1
                      inv := ψfst.1
                      hom_inv_id := by
                        exact congrArg (fun f ↦ f.1) (Iso.hom_inv_id (asIso φfst))
                      inv_hom_id := by
                        exact congrArg (fun f ↦ f.1) (Iso.inv_hom_id (asIso φfst)) }
                  let eB : Pobj.snd.1 ≅ Qobj.snd.1 :=
                    { hom := φsnd.1
                      inv := ψsnd.1
                      hom_inv_id := by
                        exact congrArg (fun f ↦ f.1) (Iso.hom_inv_id (asIso φsnd))
                      inv_hom_id := by
                        exact congrArg (fun f ↦ f.1) (Iso.inv_hom_id (asIso φsnd)) }
                  let eFA : (FibredInSetoidsOver.toBasedFunctor F).toFunctor.obj Pobj.fst.1 ≅
                      (FibredInSetoidsOver.toBasedFunctor F).toFunctor.obj Qobj.fst.1 :=
                    Functor.mapIso (FibredInSetoidsOver.toBasedFunctor F).toFunctor eA
                  let eGB : (FibredInSetoidsOver.toBasedFunctor G).toFunctor.obj Pobj.snd.1 ≅
                      (FibredInSetoidsOver.toBasedFunctor G).toFunctor.obj Qobj.snd.1 :=
                    Functor.mapIso (FibredInSetoidsOver.toBasedFunctor G).toFunctor eB
                  have hcomm :
                      CommSq ((FibredInSetoidsOver.toBasedFunctor F).toFunctor.map ψfst.1)
                        Qobj.iso.hom.1 Pobj.iso.hom.1
                        ((FibredInSetoidsOver.toBasedFunctor G).toFunctor.map ψsnd.1) := by
                    simpa [eFA, eGB, eA, eB] using
                      (CommSq.horiz_inv (f := eFA) (i := eGB) φ.1.comm)
                  let ψ0 :
                      ({ U := UP, obj := Qobj } : (explicitTwoFibreProductOver F G).obj) ⟶
                        ({ U := UP, obj := Pobj } : (explicitTwoFibreProductOver F G).obj) :=
                    { base := 𝟙 UP
                      a := ψfst.1
                      a_over := ψfst.2
                      b := ψsnd.1
                      b_over := ψsnd.2
                      comm := hcomm }
                  have hψ0 : (explicitTwoFibreProductOver F G).p.IsHomLift (𝟙 UP) ψ0 := by
                    refine IsHomLift.of_fac' (explicitTwoFibreProductOver F G).p (𝟙 UP) ψ0 rfl rfl ?_
                    simpa using (show (explicitTwoFibreProductOver F G).p.map ψ0 = 𝟙 UP by rfl)
                  refine ⟨⟨?_, ?_, ?_⟩⟩
                  · exact
                      @Functor.Fiber.homMk _ _ _ _ (explicitTwoFibreProductOver F G).p UP _ _ ψ0 hψ0
                  · apply Functor.Fiber.hom_ext
                    apply ExplicitTwoFibreProductHom.ext
                    · exact congrArg (fun f ↦ f.1) (Iso.hom_inv_id (asIso φfst))
                    · exact congrArg (fun f ↦ f.1) (Iso.hom_inv_id (asIso φsnd))
                  · apply Functor.Fiber.hom_ext
                    apply ExplicitTwoFibreProductHom.ext
                    · exact congrArg (fun f ↦ f.1) (Iso.inv_hom_id (asIso φfst))
                    · exact congrArg (fun f ↦ f.1) (Iso.inv_hom_id (asIso φsnd))

/-- Helper for Lemma 4.39.4: each fibre of the explicit `2`-fibre product projection is a
groupoid. -/
private theorem explicitTwoFibreProduct_fiber_isGroupoid
    (F : X ⟶ S) (G : Y ⟶ S) (U : C) :
    IsGroupoid ((explicitTwoFibreProductOver F G).p.Fiber U) where
  all_isIso φ := explicitTwoFibreProduct_fiber_hom_isIso F G φ

/-- Lemma 4.39.4: the explicit pullback projection is again fibred in setoids. -/
theorem explicitTwoFibreProductProjection_isFibredInSetoids
    (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids (explicitTwoFibreProductOver F G).p := by
  letI : (explicitTwoFibreProductOver F G).p.IsFibered :=
    show (explicitTwoFibreProductOver F G).p.IsFibered from
      explicitTwoFibreProductProjection_isFibered
        (F := (show X.toFibredCategoryOver ⟶ S.toFibredCategoryOver from F.toHom))
        (G := (show Y.toFibredCategoryOver ⟶ S.toFibredCategoryOver from G.toHom))
  letI : IsFibredInGroupoids (explicitTwoFibreProductOver F G).p :=
    CategoryTheory.isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (explicitTwoFibreProductOver F G).p inferInstance
      (explicitTwoFibreProduct_fiber_isGroupoid F G)
  letI : ∀ U : C, Quiver.IsThin ((explicitTwoFibreProductOver F G).p.Fiber U) :=
    explicitTwoFibreProduct_fiber_isThin F G
  infer_instance

/-- The explicit pullback projection carries the canonical fibred-in-setoids structure. -/
instance (F : X ⟶ S) (G : Y ⟶ S) :
    IsFibredInSetoids (explicitTwoFibreProductOver F G).p :=
  explicitTwoFibreProductProjection_isFibredInSetoids F G

end FibredInSetoidsOver

end CategoryTheory
