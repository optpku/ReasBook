module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.GSetForgetfulPoint
public import stacks_project.Chap07.Lemma_7_8_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite Limits

universe u v

namespace CategoryTheory

section

variable (G : Type u) [Group G]

/- Domain-style sampling for Proposition 7.9.1:
- primary domain: sheaves on the jointly surjective site of `G`-sets and their recovery from the
  left regular `G`-set;
- sampled owner API:
  `Action.jointlySurjectiveTopology`,
  `GrothendieckTopology.yonedaEquiv`,
  `Action.ofMulAction`,
  `Functor.IsEquivalence`,
  `Functor.inv`,
  `Functor.asEquivalence`;
- primitive data: the source-facing functor `sheafSectionsOnLeftRegularFunctor`;
- derived API: the owner-level equivalence statement for
  `(Action.jointlySurjectiveTopology G).yoneda` and the identification of its canonical inverse
  with `sheafSectionsOnLeftRegularFunctor`;
- source/core/bridge triage:
  `source-facing`: the left-regular-sections functor from sheaves to `G`-sets;
  `core/canonical`: the site Yoneda functor together with the owner predicate
    `Functor.IsEquivalence`;
  `bridge/view`: the induced `MulAction` on `ℱ({}_G G)`, from which the bundled `Action` object is
    derived.

The public owner in this file remains `sheafSectionsOnLeftRegularFunctor`, while Proposition 7.9.1
itself is organized around the canonical owner `Functor.IsEquivalence` for the site Yoneda functor.
-/

/-- Helper for Proposition 7.9.1: the orbit map from the left regular `G`-set through a chosen
point of a `G`-set. -/
def leftRegularHomOfPoint {U : Action (Type u) G} (u : U.V) :
    Action.leftRegular G ⟶ U where
  hom := fun g ↦ U.ρ (show G from g) u
  comm := by
    -- Multiplication in the left regular action records the orbit relation.
    intro g
    ext h
    exact congrFun (MonoidHom.map_mul U.ρ (show G from g) (show G from h)) u

/-- Helper for Proposition 7.9.1: if two points have the same image in `X`, then the orbit maps
from the left regular `G`-set become equal after composing with the corresponding arrows to `X`. -/
theorem leftRegularHomOfPoint_comp_eq
    {Y₁ Y₂ X : Action (Type u) G} {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X} (y₁ : Y₁.V) (y₂ : Y₂.V)
    (h : f₁.hom y₁ = f₂.hom y₂) :
    leftRegularHomOfPoint G y₁ ≫ f₁ = leftRegularHomOfPoint G y₂ ≫ f₂ := by
  -- Both composites are equivariant maps out of the left regular action with the same value at `1`.
  apply Action.hom_ext
  ext g
  have h₁ := congrFun (f₁.comm (show G from g)) y₁
  have h₂ := congrFun (f₂.comm (show G from g)) y₂
  simp only [types_comp_apply] at h₁ h₂
  change f₁.hom (Y₁.ρ (show G from g) y₁) = f₂.hom (Y₂.ρ (show G from g) y₂)
  rw [h₁, h₂]
  exact congrArg (X.ρ (show G from g)) h

/-- Helper for Proposition 7.9.1: precomposing the orbit map by right multiplication on the left
regular `G`-set corresponds to translating the chosen point. -/
theorem leftRegularHomOfPoint_rightMul
    {U : Action (Type u) G} (u : U.V) (g : G) :
    gSetForgetfulPointLeftRegularRightMul G g ≫ leftRegularHomOfPoint G u =
      leftRegularHomOfPoint G (U.ρ g u) := by
  -- Both sides are orbit maps, and evaluating on `h` gives the point `(h * g) • u`.
  apply Action.hom_ext
  ext h
  change U.ρ (show G from ((show G from h) * g)) u = U.ρ (show G from h) (U.ρ g u)
  exact congrFun (MonoidHom.map_mul U.ρ (show G from h) g) u

/-- Helper for Proposition 7.9.1: on the left regular `G`-set, the orbit map determined by a
point is exactly right multiplication by that point. -/
theorem leftRegularHomOfPoint_leftRegular (g : (Action.leftRegular G).V) :
    leftRegularHomOfPoint G g = gSetForgetfulPointLeftRegularRightMul G g := by
  -- Both endomorphisms of the left regular action send `h` to `h * g`.
  apply Action.hom_ext
  ext h
  rfl

/-- The jointly surjective topology `\mathcal T_G` on `G`-sets is subcanonical. -/
instance : (Action.jointlySurjectiveTopology G).Subcanonical := by
  classical
  refine GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj _ ?_
  intro A X R hR x hx
  rw [Action.mem_jointlySurjectiveTopology_iff] at hR
  choose Y f hf y hy using hR
  let tHom : X.V → A.V := fun a ↦ (x (f a) (hf a)).hom (y a)
  have htHom_eq : ∀ {Y' : Action (Type u) G} (f' : Y' ⟶ X) (hf' : R f') (y' : Y'.V),
      tHom (f'.hom y') = (x f' hf').hom y' := by
    intro Y' f' hf' y'
    dsimp [tHom]
    -- Compare the chosen lift of `f'.hom y'` with the given lift through the left regular orbit.
    have hcomp :
        leftRegularHomOfPoint G (y (f'.hom y')) ≫ f (f'.hom y') =
          leftRegularHomOfPoint G y' ≫ f' := by
      apply leftRegularHomOfPoint_comp_eq G
      exact hy (f'.hom y')
    have hcompat :=
      hx (leftRegularHomOfPoint G (y (f'.hom y'))) (leftRegularHomOfPoint G y')
        (hf (f'.hom y')) hf' hcomp
    have hcompat1 :=
      congrFun (congrArg Action.Hom.hom hcompat)
        (show (Action.leftRegular G).V from ((1 : G) : G))
    simpa [leftRegularHomOfPoint] using hcompat1
  have htHom_comm : ∀ (g : G) (a : X.V), tHom (X.ρ g a) = A.ρ g (tHom a) := by
    intro g a
    have hfcomm := congrFun ((f a).comm g) (y a)
    simp only [types_comp_apply, hy a] at hfcomm
    -- Use equivariance of the chosen local section above the orbit of `a`.
    calc
      tHom (X.ρ g a) = tHom ((f a).hom ((Y a).ρ g (y a))) := by
        rw [hfcomm]
      _ = (x (f a) (hf a)).hom ((Y a).ρ g (y a)) := by
        exact htHom_eq (f a) (hf a) ((Y a).ρ g (y a))
      _ = A.ρ g ((x (f a) (hf a)).hom (y a)) := by
        have hcomm := congrFun ((x (f a) (hf a)).comm g) (y a)
        simpa only [types_comp_apply] using hcomm
      _ = A.ρ g (tHom a) := rfl
  let t : X ⟶ A :=
    { hom := tHom
      comm := by
        intro g
        ext a
        exact htHom_comm g a }
  refine ⟨t, ?_, ?_⟩
  · intro Y' f' hf'
    -- The glued map restricts to the original family on each covering arrow.
    apply Action.hom_ext
    ext y'
    change t.hom (f'.hom y') = (x f' hf').hom y'
    simpa using htHom_eq f' hf' y'
  · intro t' ht'
    -- Any other amalgamation agrees on the chosen local lift of each point, hence globally.
    apply Action.hom_ext
    ext a
    have ha := congrFun (congrArg Action.Hom.hom (ht' (f a) (hf a))) (y a)
    simpa [hy a, t, tHom] using ha

-- Proof sketch: pullback along the identity endomorphism is the identity map on sections. -/
/-- Pullback along right multiplication by `1` acts trivially on sections over the left regular
`G`-set. -/
theorem sheafSectionsOnLeftRegular_map_one
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) :
    ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G 1)) =
      𝟙 (ℱ.obj.obj (op (Action.leftRegular G))) := by
  rw [gSetForgetfulPointLeftRegularRightMul_one]
  change ℱ.obj.map (𝟙 (op (Action.leftRegular G))) = 𝟙 (ℱ.obj.obj (op (Action.leftRegular G)))
  exact ℱ.obj.map_id (op (Action.leftRegular G))

-- Proof sketch: functoriality of the underlying presheaf identifies pullback along the composite
-- right multiplication map with the composite of the two pullback maps.
/-- Pullback along right multiplication turns multiplication in `G` into the induced left action on
sections over the left regular `G`-set. -/
theorem sheafSectionsOnLeftRegular_map_mul
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) (g h : G) :
    ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G (g * h))) =
      ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G h)) ≫
        ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g)) := by
  rw [gSetForgetfulPointLeftRegularRightMul_mul]
  change
    ℱ.obj.map
        (op (gSetForgetfulPointLeftRegularRightMul G h) ≫
          op (gSetForgetfulPointLeftRegularRightMul G g)) =
      ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G h)) ≫
        ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g))
  exact
    ℱ.obj.map_comp
      (op (gSetForgetfulPointLeftRegularRightMul G h))
      (op (gSetForgetfulPointLeftRegularRightMul G g))

/-- The left action on sections over the left regular `G`-set induced by pullback along right
translations. -/
instance sheafSectionsOnLeftRegularMulAction
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) :
    MulAction G (ℱ.obj.obj (op (Action.leftRegular G))) where
  smul g := ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g))
  one_smul x := by
    change ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G 1)) x = x
    simpa using congrArg (fun f : End (ℱ.obj.obj (op (Action.leftRegular G))) ↦ f x)
      (sheafSectionsOnLeftRegular_map_one G ℱ)
  mul_smul g h x := by
    change ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G (g * h))) x =
      ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g))
        (ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G h)) x)
    simpa using congrArg (fun f : End (ℱ.obj.obj (op (Action.leftRegular G))) ↦ f x)
      (sheafSectionsOnLeftRegular_map_mul G ℱ g h)

/-- The equivariant map on left-regular sections induced by a sheaf morphism. -/
def sheafSectionsOnLeftRegularMap
    {ℱ 𝒢 : Sheaf (Action.jointlySurjectiveTopology G) (Type v)} (η : ℱ ⟶ 𝒢) :
    Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G))) ⟶
      Action.ofMulAction G (𝒢.obj.obj (op (Action.leftRegular G))) where
  hom := η.hom.app (op (Action.leftRegular G))
  comm g := by
    change
      ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g)) ≫
          η.hom.app (op (Action.leftRegular G)) =
        η.hom.app (op (Action.leftRegular G)) ≫
          𝒢.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g))
    exact η.hom.naturality (op (gSetForgetfulPointLeftRegularRightMul G g))

-- Proof sketch: evaluate the identity natural transformation at the left regular `G`-set. -/
/-- The left-regular sections construction sends identity morphisms of sheaves to identity
equivariant maps. -/
theorem sheafSectionsOnLeftRegularFunctor_map_id
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)) :
    sheafSectionsOnLeftRegularMap G (𝟙 ℱ) =
      𝟙 (Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G)))) := by
  apply Action.hom_ext
  rfl

-- Proof sketch: evaluate the composite natural transformation at the left regular `G`-set and use
-- the functoriality of the sheaf morphism components.
/-- The left-regular sections construction preserves composition of sheaf morphisms. -/
theorem sheafSectionsOnLeftRegularFunctor_map_comp
    {ℱ 𝒢 ℋ : Sheaf (Action.jointlySurjectiveTopology G) (Type v)}
    (η : ℱ ⟶ 𝒢) (θ : 𝒢 ⟶ ℋ) :
    sheafSectionsOnLeftRegularMap G (η ≫ θ) =
      sheafSectionsOnLeftRegularMap G η ≫ sheafSectionsOnLeftRegularMap G θ := by
  apply Action.hom_ext
  rfl

/-- The functor sending a sheaf on the surjective site of `G`-sets to its `G`-set of sections on
the left regular object `{}_G G`. -/
def sheafSectionsOnLeftRegularFunctor :
    Sheaf (Action.jointlySurjectiveTopology G) (Type v) ⥤ Action (Type v) G where
  obj ℱ := Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G)))
  map := sheafSectionsOnLeftRegularMap G
  map_id := sheafSectionsOnLeftRegularFunctor_map_id G
  map_comp := fun η θ ↦ sheafSectionsOnLeftRegularFunctor_map_comp G η θ

/-- Helper for Proposition 7.9.1: evaluating an equivariant map `{}_G G ⟶ S` at `1 ∈ G`
identifies the left-regular sections of the representable sheaf `h_S` with `S` itself. -/
def yoneda_leftRegular_sections_iso (S : Action (Type u) G) :
    S ≅ (sheafSectionsOnLeftRegularFunctor G).obj ((Action.jointlySurjectiveTopology G).yoneda.obj S) := by
  refine Action.mkIso ?_ ?_
  · refine
      { hom := fun s ↦ leftRegularHomOfPoint G s
        inv := fun a ↦ a.hom (show (Action.leftRegular G).V from ((1 : G) : G))
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · funext a
      change S.ρ 1 a = a
      exact congrFun (MonoidHom.map_one S.ρ) a
    · funext a
      -- An equivariant map out of the left regular action is determined by its value at `1`.
      apply Action.hom_ext
      ext g
      have hcomm := congrFun (a.comm (show G from g))
        (show (Action.leftRegular G).V from ((1 : G) : G))
      simp only [types_comp_apply, leftRegularHomOfPoint] at hcomm ⊢
      simpa using hcomm.symm
  · intro g
    ext s
    -- The induced action on sections is pullback by right translation on the source.
    simpa [sheafSectionsOnLeftRegularFunctor, sheafSectionsOnLeftRegularMulAction] using
      (leftRegularHomOfPoint_rightMul G s g).symm

/-- Helper for Proposition 7.9.1: for a chosen point `u : U`, the singleton cover
`{}_G G ⟶ U` and the stabilizer-indexed right-translation family on `{}_G G` impose the same
sheaf condition on any sheaf. -/
theorem singleton_cover_isSheafFor_iff_stabilizer_family
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type v))
    {U : Action (Type u) G} (u : U.V) :
    (Presieve.ofArrows
      (fun _ : PUnit ↦ Action.leftRegular G)
      (fun _ : PUnit ↦ leftRegularHomOfPoint G u)).IsSheafFor ℱ.obj ↔
      (Presieve.ofArrows
        (fun _ : { g : G // U.ρ g u = u } ↦ Action.leftRegular G)
        (fun h : { g : G // U.ρ g u = u } ↦
          gSetForgetfulPointLeftRegularRightMul G h.1 ≫
            leftRegularHomOfPoint G u)).IsSheafFor ℱ.obj := by
  -- Route correction: package the fiber-product calculation through Lemma 7.8.4 instead of
  -- unfolding the sheaf equalizer by hand.
  refine isSheafFor_ofArrows_iff_of_tautological_equivalence
    (Ui := fun _ : PUnit ↦ Action.leftRegular G)
    (π := fun _ : PUnit ↦ leftRegularHomOfPoint G u)
    (Vj := fun _ : { g : G // U.ρ g u = u } ↦ Action.leftRegular G)
    (ψ := fun h : { g : G // U.ρ g u = u } ↦
      gSetForgetfulPointLeftRegularRightMul G h.1 ≫
        leftRegularHomOfPoint G u)
    (F := ℱ.obj)
    (α := fun _ ↦ ⟨1, by simp⟩)
    (β := fun _ ↦ PUnit.unit)
    ?_ ?_
  · intro _
    -- The trivial stabilizer element gives back the original singleton arrow.
    apply eqToIso
    congr 1
    simp
  · intro h
    -- A stabilizer element acts by right translation without changing the resulting orbit map.
    apply eqToIso
    simpa using congrArg Over.mk <| calc
      gSetForgetfulPointLeftRegularRightMul G h.1 ≫ leftRegularHomOfPoint G u =
          leftRegularHomOfPoint G (U.ρ h.1 u) := by
            simpa using leftRegularHomOfPoint_rightMul (G := G) u h.1
      _ = leftRegularHomOfPoint G u := by
            congr 1
            exact h.2

-- Proof sketch: the surjective topology is subcanonical, so the functor `S ↦ Hom_G(-, S)` is the
-- canonical Yoneda functor `(Action.jointlySurjectiveTopology G).yoneda`. For any sheaf `ℱ`, the canonical map
-- `ℱ(U) → Hom_G(U, ℱ({}_G G))` sends a section to its translates along the maps `{}_G G → U`; the
-- orbit decompositions and Lemma 7.8.4 reduce bijectivity to the transitive case, where the sheaf
-- condition for the cover `{}_G G → U` identifies sections with stabilizer-invariant elements of
-- `ℱ({}_G G)`. This yields unit and counit isomorphisms exhibiting
-- `sheafSectionsOnLeftRegularFunctor G` as a quasi-inverse to `(Action.jointlySurjectiveTopology G).yoneda`.
/-- Helper for Proposition 7.9.1: the explicit canonical map
`ℱ(U) → Hom_G(U, ℱ({}_G G))` first viewed on underlying presheaves. -/
noncomputable def sheafSections_counit_toPresheaf :
    sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u) ⟶
      (sheafSectionsOnLeftRegularFunctor G ⋙ (Action.jointlySurjectiveTopology G).yoneda) ⋙
        sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u) where
  app ℱ :=
    { app := fun U s =>
        { hom := fun u ↦ ℱ.obj.map (op (leftRegularHomOfPoint G u)) s
          comm := by
            -- Pullback along the translated orbit map matches the induced action on sections.
            intro g
            ext u
            change
              ℱ.obj.map (op (leftRegularHomOfPoint G (U.unop.ρ g u))) s =
                ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g))
                  (ℱ.obj.map (op (leftRegularHomOfPoint G u)) s)
            rw [← leftRegularHomOfPoint_rightMul (G := G) u g]
            change
              ℱ.obj.map
                  (op (leftRegularHomOfPoint G u) ≫
                    op (gSetForgetfulPointLeftRegularRightMul G g)) s =
                ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g))
                  (ℱ.obj.map (op (leftRegularHomOfPoint G u)) s)
            simpa using
              congrFun
                (ℱ.obj.map_comp
                  (op (leftRegularHomOfPoint G u))
                  (op (gSetForgetfulPointLeftRegularRightMul G g))) s }
      naturality := by
        -- Naturality in `U` is the compatibility of the orbit maps with composition.
        intro U V f
        ext s
        apply Action.hom_ext
        ext u
        change
          ℱ.obj.map (op (leftRegularHomOfPoint G u)) (ℱ.obj.map f s) =
            ℱ.obj.map (op (leftRegularHomOfPoint G (f.unop.hom u))) s
        have hcomp :
            leftRegularHomOfPoint G u ≫ f.unop =
              leftRegularHomOfPoint G (f.unop.hom u) := by
          simpa using
            leftRegularHomOfPoint_comp_eq (G := G) (f₁ := f.unop) (f₂ := 𝟙 U.unop)
              u (f.unop.hom u) rfl
        rw [← hcomp]
        symm
        change
          ℱ.obj.map (f ≫ op (leftRegularHomOfPoint G u)) s =
            ℱ.obj.map (op (leftRegularHomOfPoint G u)) (ℱ.obj.map f s)
        exact
          FunctorToTypes.map_comp_apply
            (F := ℱ.obj) f (op (leftRegularHomOfPoint G u)) s }
  naturality := by
    -- Naturality in `ℱ` is the naturality of the sheaf morphism on each orbit map.
    intro ℱ 𝒢 η
    ext U s
    apply Action.hom_ext
    ext u
    change
      𝒢.obj.map (op (leftRegularHomOfPoint G u)) (η.hom.app U s) =
        η.hom.app (op (Action.leftRegular G)) (ℱ.obj.map (op (leftRegularHomOfPoint G u)) s)
    simpa [sheafSectionsOnLeftRegularFunctor, sheafSectionsOnLeftRegularMap] using
      (congrFun (η.hom.naturality (op (leftRegularHomOfPoint G u))) s).symm

/-- Helper for Proposition 7.9.1: the explicit counit lifted back from presheaves to sheaves
using the full faithfulness of `sheafToPresheaf`. -/
noncomputable def sheafSections_counit :
    𝟭 (Sheaf (Action.jointlySurjectiveTopology G) (Type u)) ⟶
      sheafSectionsOnLeftRegularFunctor G ⋙ (Action.jointlySurjectiveTopology G).yoneda :=
  ((fullyFaithfulSheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u)).whiskeringRight
      (Sheaf (Action.jointlySurjectiveTopology G) (Type u))).preimage
    (sheafSections_counit_toPresheaf G)

/-- Helper for Proposition 7.9.1: on the left regular object, the presheaf counit is the orbit-map
construction `s ↦ (g ↦ g • s)`. -/
theorem sheafSections_counit_toPresheaf_app_leftRegular_eq
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u))
    (s : ℱ.obj.obj (op (Action.leftRegular G))) :
    (((sheafSections_counit_toPresheaf G).app ℱ).app (op (Action.leftRegular G)) s) =
      leftRegularHomOfPoint G s := by
  -- Evaluating the explicit counit on `{}_G G` replaces the orbit map `α_u` by right translation.
  apply Action.hom_ext
  ext g
  change ℱ.obj.map (op (leftRegularHomOfPoint G g)) s =
    ℱ.obj.map (op (gSetForgetfulPointLeftRegularRightMul G g)) s
  rw [leftRegularHomOfPoint_leftRegular (G := G) g]
  rfl

/-- Helper for Proposition 7.9.1: the source proof's easy case `U = {}_G G` already makes the
presheaf counit component bijective. -/
theorem sheafSections_counit_toPresheaf_app_leftRegular_bijective
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u)) :
    Function.Bijective
      (((sheafSections_counit_toPresheaf G).app ℱ).app (op (Action.leftRegular G))) := by
  constructor
  · intro s₁ s₂ hs
    -- Equality of orbit maps can be tested at `1 ∈ G`.
    have hs' := congrArg
      (fun a : Action.leftRegular G ⟶
          Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G))) ↦
        a.hom (show (Action.leftRegular G).V from ((1 : G) : G))) hs
    rw [sheafSections_counit_toPresheaf_app_leftRegular_eq (G := G) ℱ s₁,
      sheafSections_counit_toPresheaf_app_leftRegular_eq (G := G) ℱ s₂] at hs'
    simpa [leftRegularHomOfPoint] using hs'
  · intro a
    refine ⟨a.hom (show (Action.leftRegular G).V from ((1 : G) : G)), ?_⟩
    -- An equivariant map out of the left regular action is determined by its value at `1`.
    apply Action.hom_ext
    ext g
    rw [sheafSections_counit_toPresheaf_app_leftRegular_eq (G := G) ℱ]
    have hg := congrFun (a.comm (show G from g))
      (show (Action.leftRegular G).V from ((1 : G) : G))
    simpa [leftRegularHomOfPoint] using hg.symm

/-- Helper for Proposition 7.9.1: the family of orbit maps indexed by points of `U` is jointly
surjective, hence covering for the jointly surjective topology. -/
theorem leftRegular_point_family_covering
    (U : Action (Type u) G) :
    Sieve.ofArrows (fun _ : U.V ↦ Action.leftRegular G)
      (fun u : U.V ↦ leftRegularHomOfPoint G u) ∈
        Action.jointlySurjectiveTopology G U := by
  -- Every point of `U` is hit by the orbit map indexed by that point and evaluated at `1`.
  rw [Action.mem_jointlySurjectiveTopology_iff]
  intro u
  refine ⟨Action.leftRegular G, leftRegularHomOfPoint G u, ?_, ?_⟩
  · change Sieve.generate
        (Presieve.ofArrows (fun _ : U.V ↦ Action.leftRegular G)
          (fun u : U.V ↦ leftRegularHomOfPoint G u))
        (leftRegularHomOfPoint G u)
    exact Sieve.le_generate _ _ _ (Presieve.ofArrows.mk u)
  refine ⟨(show (Action.leftRegular G).V from ((1 : G) : G)), ?_⟩
  change U.ρ 1 u = u
  exact congrFun (MonoidHom.map_one U.ρ) u

/-- Helper for Proposition 7.9.1: two sections over `U` agree once their pullbacks along all orbit
maps `{}_G G ⟶ U` agree. -/
theorem eq_of_leftRegular_restrictions_eq
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u))
    {U : Action (Type u) G} {s₁ s₂ : ℱ.obj.obj (op U)}
    (h :
      ∀ u : U.V,
        ℱ.obj.map (op (leftRegularHomOfPoint G u)) s₁ =
          ℱ.obj.map (op (leftRegularHomOfPoint G u)) s₂) :
    s₁ = s₂ := by
  let hℱ : Presheaf.IsSheaf (Action.jointlySurjectiveTopology G) ℱ.obj := by
    simpa [isSheaf_iff_isSheaf_of_type] using ℱ.2
  -- The point-indexed left-regular family is covering, so separatedness identifies the sections.
  have hFun :
      (fun _ : PUnit ↦ s₁) = fun _ : PUnit ↦ s₂ := by
    apply hℱ.hom_ext_ofArrows
      (f := fun u : U.V ↦ leftRegularHomOfPoint G u)
      (hf := leftRegular_point_family_covering (G := G) U)
    intro u
    funext _
    exact h u
  exact congrFun hFun PUnit.unit

/-- Helper for Proposition 7.9.1: the explicit presheaf counit commutes with pullback along a map
of `G`-sets. -/
theorem sheafSections_counit_toPresheaf_app_eq_comp
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u))
    {U V : Action (Type u) G} (f : U ⟶ V) (s : ℱ.obj.obj (op V)) :
    (((sheafSections_counit_toPresheaf G).app ℱ).app (op U) (ℱ.obj.map f.op s)) =
      f ≫ (((sheafSections_counit_toPresheaf G).app ℱ).app (op V) s) := by
  -- Unfold the explicit counit and use the orbit-map compatibility `α_u ≫ f = α_{f(u)}`.
  apply Action.hom_ext
  ext u
  change ℱ.obj.map (op (leftRegularHomOfPoint G u)) (ℱ.obj.map f.op s) =
    ((((sheafSections_counit_toPresheaf G).app ℱ).app (op V) s).hom (f.hom u))
  have hcomp :
      leftRegularHomOfPoint G u ≫ f =
        leftRegularHomOfPoint G (f.hom u) := by
    simpa using
      leftRegularHomOfPoint_comp_eq (G := G) (f₁ := f) (f₂ := 𝟙 V) u (f.hom u) rfl
  change ℱ.obj.map (op (leftRegularHomOfPoint G u)) (ℱ.obj.map f.op s) =
    ℱ.obj.map (op (leftRegularHomOfPoint G (f.hom u))) s
  rw [← hcomp]
  symm
  change ℱ.obj.map (f.op ≫ op (leftRegularHomOfPoint G u)) s =
    ℱ.obj.map (op (leftRegularHomOfPoint G u)) (ℱ.obj.map f.op s)
  exact FunctorToTypes.map_comp_apply (F := ℱ.obj) f.op (op (leftRegularHomOfPoint G u)) s

/-- Helper for Proposition 7.9.1: an equivariant map out of `U` restricts along the orbit map of
`u` to the orbit map of its value at `u`. -/
theorem leftRegularHomOfPoint_comp_equivariant
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u))
    {U : Action (Type u) G}
    (t : U ⟶ Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G)))) (u : U.V) :
    leftRegularHomOfPoint G (t.hom u) = leftRegularHomOfPoint G u ≫ t := by
  -- Both equivariant maps out of `{}_G G` send `g` to `t(g • u)`.
  apply Action.hom_ext
  ext g
  have hcomm := congrFun (t.comm (show G from g)) u
  simpa [leftRegularHomOfPoint] using hcomm.symm

/-- Helper for Proposition 7.9.1: the family `u ↦ t(u)` produced by an equivariant map
`t : U ⟶ ℱ({}_G G)` is compatible on the point-indexed orbit cover of `U`. -/
theorem sheafSections_counit_family_compatible
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u))
    {U : Action (Type u) G}
    (t :
      (((Action.jointlySurjectiveTopology G).yoneda.obj
        (Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G))))).obj.obj (op U))) :
    Presieve.Arrows.Compatible ℱ.obj
      (fun u : U.V ↦ leftRegularHomOfPoint G u)
      (fun u : U.V ↦ t.hom u) := by
  intro u₁ u₂ Z g₁ g₂ hEq
  -- Equality on the overlap is checked after restricting to each orbit map in `Z`.
  apply eq_of_leftRegular_restrictions_eq (G := G) ℱ
  intro z
  apply (sheafSections_counit_toPresheaf_app_leftRegular_bijective (G := G) ℱ).1
  have hzEq :
      leftRegularHomOfPoint G z ≫ g₁ ≫ leftRegularHomOfPoint G u₁ =
        leftRegularHomOfPoint G z ≫ g₂ ≫ leftRegularHomOfPoint G u₂ := by
    simpa [Category.assoc] using
      congrArg (fun k : Z ⟶ U ↦ leftRegularHomOfPoint G z ≫ k) hEq
  have hLeft :
      (((sheafSections_counit_toPresheaf G).app ℱ).app (op (Action.leftRegular G)))
        (ℱ.obj.map (op (leftRegularHomOfPoint G z))
          (ℱ.obj.map g₁.op (t.hom u₁))) =
        leftRegularHomOfPoint G z ≫ g₁ ≫ leftRegularHomOfPoint G u₁ ≫ t := by
    have h0 :
        (((sheafSections_counit_toPresheaf G).app ℱ).app (op (Action.leftRegular G)))
          (ℱ.obj.map (op (leftRegularHomOfPoint G z))
            (ℱ.obj.map g₁.op (t.hom u₁))) =
          leftRegularHomOfPoint G z ≫
            (((sheafSections_counit_toPresheaf G).app ℱ).app (op Z)
              (ℱ.obj.map g₁.op (t.hom u₁))) := by
      simpa using sheafSections_counit_toPresheaf_app_eq_comp (G := G) ℱ
        (leftRegularHomOfPoint G z) (ℱ.obj.map g₁.op (t.hom u₁))
    have h1 :
        leftRegularHomOfPoint G z ≫
            (((sheafSections_counit_toPresheaf G).app ℱ).app (op Z)
              (ℱ.obj.map g₁.op (t.hom u₁))) =
          leftRegularHomOfPoint G z ≫ g₁ ≫
            (((sheafSections_counit_toPresheaf G).app ℱ).app (op (Action.leftRegular G))
              (t.hom u₁)) := by
      rw [sheafSections_counit_toPresheaf_app_eq_comp (G := G) ℱ g₁ (t.hom u₁)]
    have h2 :
        leftRegularHomOfPoint G z ≫ g₁ ≫
            (((sheafSections_counit_toPresheaf G).app ℱ).app (op (Action.leftRegular G))
              (t.hom u₁)) =
          leftRegularHomOfPoint G z ≫ g₁ ≫ leftRegularHomOfPoint G (t.hom u₁) := by
      simpa [Category.assoc] using congrArg
        (fun k :
          Action.leftRegular G ⟶
            Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G))) ↦
          leftRegularHomOfPoint G z ≫ g₁ ≫ k)
        (sheafSections_counit_toPresheaf_app_leftRegular_eq (G := G) ℱ (t.hom u₁))
    have h3 :
        leftRegularHomOfPoint G z ≫ g₁ ≫ leftRegularHomOfPoint G (t.hom u₁) =
          leftRegularHomOfPoint G z ≫ g₁ ≫ leftRegularHomOfPoint G u₁ ≫ t := by
      simpa [Category.assoc] using congrArg
        (fun k :
          Action.leftRegular G ⟶
            Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G))) ↦
          leftRegularHomOfPoint G z ≫ g₁ ≫ k)
        (leftRegularHomOfPoint_comp_equivariant (G := G) ℱ t u₁)
    exact h0.trans (h1.trans (h2.trans h3))
  have hRight :
      (((sheafSections_counit_toPresheaf G).app ℱ).app (op (Action.leftRegular G)))
        (ℱ.obj.map (op (leftRegularHomOfPoint G z))
          (ℱ.obj.map g₂.op (t.hom u₂))) =
        leftRegularHomOfPoint G z ≫ g₂ ≫ leftRegularHomOfPoint G u₂ ≫ t := by
    have h0 :
        (((sheafSections_counit_toPresheaf G).app ℱ).app (op (Action.leftRegular G)))
          (ℱ.obj.map (op (leftRegularHomOfPoint G z))
            (ℱ.obj.map g₂.op (t.hom u₂))) =
          leftRegularHomOfPoint G z ≫
            (((sheafSections_counit_toPresheaf G).app ℱ).app (op Z)
              (ℱ.obj.map g₂.op (t.hom u₂))) := by
      simpa using sheafSections_counit_toPresheaf_app_eq_comp (G := G) ℱ
        (leftRegularHomOfPoint G z) (ℱ.obj.map g₂.op (t.hom u₂))
    have h1 :
        leftRegularHomOfPoint G z ≫
            (((sheafSections_counit_toPresheaf G).app ℱ).app (op Z)
              (ℱ.obj.map g₂.op (t.hom u₂))) =
          leftRegularHomOfPoint G z ≫ g₂ ≫
            (((sheafSections_counit_toPresheaf G).app ℱ).app (op (Action.leftRegular G))
              (t.hom u₂)) := by
      rw [sheafSections_counit_toPresheaf_app_eq_comp (G := G) ℱ g₂ (t.hom u₂)]
    have h2 :
        leftRegularHomOfPoint G z ≫ g₂ ≫
            (((sheafSections_counit_toPresheaf G).app ℱ).app (op (Action.leftRegular G))
              (t.hom u₂)) =
          leftRegularHomOfPoint G z ≫ g₂ ≫ leftRegularHomOfPoint G (t.hom u₂) := by
      simpa [Category.assoc] using congrArg
        (fun k :
          Action.leftRegular G ⟶
            Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G))) ↦
          leftRegularHomOfPoint G z ≫ g₂ ≫ k)
        (sheafSections_counit_toPresheaf_app_leftRegular_eq (G := G) ℱ (t.hom u₂))
    have h3 :
        leftRegularHomOfPoint G z ≫ g₂ ≫ leftRegularHomOfPoint G (t.hom u₂) =
          leftRegularHomOfPoint G z ≫ g₂ ≫ leftRegularHomOfPoint G u₂ ≫ t := by
      simpa [Category.assoc] using congrArg
        (fun k :
          Action.leftRegular G ⟶
            Action.ofMulAction G (ℱ.obj.obj (op (Action.leftRegular G))) ↦
          leftRegularHomOfPoint G z ≫ g₂ ≫ k)
        (leftRegularHomOfPoint_comp_equivariant (G := G) ℱ t u₂)
    exact h0.trans (h1.trans (h2.trans h3))
  have hMid :
      leftRegularHomOfPoint G z ≫ g₁ ≫ leftRegularHomOfPoint G u₁ ≫ t =
        leftRegularHomOfPoint G z ≫ g₂ ≫ leftRegularHomOfPoint G u₂ ≫ t := by
    simpa [Category.assoc] using
      congrArg (fun k : Action.leftRegular G ⟶ U ↦ k ≫ t) hzEq
  exact hLeft.trans (hMid.trans hRight.symm)

/-- Helper for Proposition 7.9.1: the explicit presheaf counit is bijective on every object,
using the point-indexed orbit cover together with the left-regular base case. -/
theorem sheafSections_counit_toPresheaf_app_bijective
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u))
    (U : Action (Type u) G) :
    Function.Bijective (((sheafSections_counit_toPresheaf G).app ℱ).app (op U)) := by
  let hℱ : Presheaf.IsSheaf (Action.jointlySurjectiveTopology G) ℱ.obj := by
    simpa [isSheaf_iff_isSheaf_of_type] using ℱ.2
  let π : U.V → (Action.leftRegular G ⟶ U) := fun u ↦ leftRegularHomOfPoint G u
  have hSheafFor :
      (Presieve.ofArrows (fun _ : U.V ↦ Action.leftRegular G) π).IsSheafFor ℱ.obj :=
    by
      rw [Presieve.isSheafFor_iff_generate]
      simpa [Sieve.ofArrows] using
        hℱ.isSheafFor
          (Sieve.ofArrows (fun _ : U.V ↦ Action.leftRegular G) π)
          (leftRegular_point_family_covering (G := G) U)
  have hbij :
      Function.Bijective (Presieve.Arrows.toCompatible ℱ.obj π) :=
    (Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible (P := ℱ.obj) (π := π)).1 hSheafFor
  constructor
  · intro s₁ s₂ hs
    -- Equality of equivariant maps gives equality of all orbit-map pullbacks.
    apply hbij.1
    apply Subtype.ext
    funext u
    exact congrFun (congrArg Action.Hom.hom hs) u
  · intro t
    -- Glue the compatible family `u ↦ t(u)` and check that the resulting section maps back to `t`.
    let y :
        Subtype (Presieve.Arrows.Compatible ℱ.obj π) :=
      ⟨fun u : U.V ↦ t.hom u, sheafSections_counit_family_compatible (G := G) ℱ t⟩
    rcases hbij.2 y with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    apply Action.hom_ext
    ext u
    have hs' := congrFun (congrArg Subtype.val hs) u
    simpa [π, y] using hs'

/-- Helper for Proposition 7.9.1: each sheaf-side counit component is an isomorphism once the
explicit presheaf counit is objectwise bijective. -/
theorem sheafSections_counit_app_isIso
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u)) :
    IsIso ((sheafSections_counit G).app ℱ) := by
  -- Reflect the objectwise isomorphism of the underlying presheaf map back to sheaves.
  letI : ∀ U : (Action (Type u) G)ᵒᵖ,
      IsIso ((((sheafSections_counit_toPresheaf G).app ℱ).app U)) := fun U ↦ by
        rw [isIso_iff_bijective]
        exact sheafSections_counit_toPresheaf_app_bijective (G := G) ℱ U.unop
  haveI : IsIso ((sheafSections_counit_toPresheaf G).app ℱ) :=
    NatIso.isIso_of_isIso_app _
  let F := sheafToPresheaf (Action.jointlySurjectiveTopology G) (Type u)
  have hmap : F.map ((sheafSections_counit G).app ℱ) = ((sheafSections_counit_toPresheaf G).app ℱ) := by
    rfl
  haveI : IsIso (F.map ((sheafSections_counit G).app ℱ)) := by
    simpa [hmap] using (inferInstance : IsIso ((sheafSections_counit_toPresheaf G).app ℱ))
  exact isIso_of_reflects_iso ((sheafSections_counit G).app ℱ) F

/-- Helper for Proposition 7.9.1: the sheaf-side counit is a natural isomorphism once each
component has been shown to be an isomorphism. -/
noncomputable instance sheafSections_counit_isIso :
    IsIso (sheafSections_counit G) := by
  letI : ∀ ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u),
      IsIso ((sheafSections_counit G).app ℱ) := fun ℱ ↦ sheafSections_counit_app_isIso (G := G) ℱ
  exact NatIso.isIso_of_isIso_app _

/-- Helper for Proposition 7.9.1: the orbit-cover argument should package the explicit counit
`ℱ ⟶ 𝓕_{ℱ({}_G G)}` into a natural isomorphism on sheaves. -/
noncomputable def sheafSections_counitIso :
    sheafSectionsOnLeftRegularFunctor G ⋙ (Action.jointlySurjectiveTopology G).yoneda ≅
      𝟭 (Sheaf (Action.jointlySurjectiveTopology G) (Type u)) :=
  -- Route correction: the point-indexed orbit cover upgrades the explicit counit to a natural
  -- isomorphism, so the final counit is just the inverse of that natural transformation.
  (asIso (sheafSections_counit G)).symm

/-- Proposition 7.9.1: the canonical Yoneda functor from `G`-sets to sheaves for the jointly
surjective topology on `G`-sets is an equivalence of categories, with inverse given by evaluation
on the left regular `G`-set `{}_G G`. -/
theorem jointlySurjectiveTopology_yoneda_isEquivalence :
    Functor.IsEquivalence
      ((Action.jointlySurjectiveTopology G).yoneda :
        Action (Type u) G ⥤ Sheaf (Action.jointlySurjectiveTopology G) (Type u)) := by
  refine Functor.IsEquivalence.mk' (sheafSectionsOnLeftRegularFunctor G) ?_ ?_
  · -- The source-side unit is the evaluation-at-`1` identification for representable sheaves.
    refine NatIso.ofComponents (fun S ↦ yoneda_leftRegular_sections_iso G S) ?_
    intro S T f
    apply Action.hom_ext
    funext s
    have hs := leftRegularHomOfPoint_comp_eq (G := G) (f₁ := f) (f₂ := 𝟙 T) s (f.hom s) rfl
    simpa using hs.symm
  · -- The remaining source-faithful input is the counit isomorphism on sheaves.
    exact sheafSections_counitIso G

attribute [instance] jointlySurjectiveTopology_yoneda_isEquivalence

/-- Helper for Proposition 7.9.1: package the explicit unit and counit data into the concrete
equivalence whose inverse is the left-regular-sections functor. -/
noncomputable def yoneda_explicit_equivalence :
    Action (Type u) G ≌ Sheaf (Action.jointlySurjectiveTopology G) (Type u) :=
  CategoryTheory.Equivalence.mk
    ((Action.jointlySurjectiveTopology G).yoneda)
    (sheafSectionsOnLeftRegularFunctor G)
    (NatIso.ofComponents (fun S ↦ yoneda_leftRegular_sections_iso G S) (by
      -- The unit is the evaluation-at-`1` identification, natural in the `G`-set.
      intro S T f
      apply Action.hom_ext
      funext s
      have hs :=
        leftRegularHomOfPoint_comp_eq (G := G) (f₁ := f) (f₂ := 𝟙 T) s (f.hom s) rfl
      simpa using hs.symm))
    (sheafSections_counitIso G)

/-- Companion bridge for Proposition 7.9.1: the canonical inverse functor attached to the
equivalence `(Action.jointlySurjectiveTopology G).yoneda` is naturally isomorphic to the
left-regular-sections functor. -/
noncomputable def jointlySurjectiveTopology_yoneda_inv_eq_sheafSectionsOnLeftRegularFunctor :
    (((Action.jointlySurjectiveTopology G).yoneda :
        Action (Type u) G ⥤ Sheaf (Action.jointlySurjectiveTopology G) (Type u)).inv) ≅
      sheafSectionsOnLeftRegularFunctor G := by
  -- Route correction: `Functor.inv` is defined using chosen preimages in the essential image, so
  -- the canonical comparison with the explicit inverse is a natural isomorphism, not literal
  -- equality of functors.
  simpa [yoneda_explicit_equivalence] using
    (Iso.isoInverseOfIsoFunctor
      (G := ((Action.jointlySurjectiveTopology G).yoneda).asEquivalence)
      (G' := yoneda_explicit_equivalence G)
      (Iso.refl _))

/-- Helper for Proposition 7.9.1: the repaired bridge from the canonical inverse functor to the
explicit left-regular-sections functor evaluated at a single sheaf. -/
noncomputable def jointlySurjectiveTopology_yoneda_inv_obj_iso
    (ℱ : Sheaf (Action.jointlySurjectiveTopology G) (Type u)) :
    ((Action.jointlySurjectiveTopology G).yoneda.inv.obj ℱ) ≅
      (sheafSectionsOnLeftRegularFunctor G).obj ℱ :=
  -- Take the component of the repaired natural isomorphism at `ℱ`.
  (jointlySurjectiveTopology_yoneda_inv_eq_sheafSectionsOnLeftRegularFunctor (G := G)).app ℱ

/-- Helper for Proposition 7.9.1: the objectwise bridge is natural in the sheaf argument, giving
the map-level replacement for old rewrites through a functor equality. -/
theorem jointlySurjectiveTopology_yoneda_inv_obj_iso_naturality
    {ℱ 𝒢 : Sheaf (Action.jointlySurjectiveTopology G) (Type u)} (η : ℱ ⟶ 𝒢) :
    ((Action.jointlySurjectiveTopology G).yoneda.inv.map η) ≫
        (jointlySurjectiveTopology_yoneda_inv_obj_iso (G := G) 𝒢).hom =
      (jointlySurjectiveTopology_yoneda_inv_obj_iso (G := G) ℱ).hom ≫
        (sheafSectionsOnLeftRegularFunctor G).map η := by
  -- This is exactly the naturality identity of the repaired bridge natural isomorphism.
  exact
    (jointlySurjectiveTopology_yoneda_inv_eq_sheafSectionsOnLeftRegularFunctor
      (G := G)).hom.naturality η

end

end CategoryTheory
