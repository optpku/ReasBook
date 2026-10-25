module

public import stacks_project.Chap04.Lemma_4_34_1
public import stacks_project.Chap04.Lemma_4_35_9

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open scoped CategoricalPullback

universe v u

namespace CategoryTheory

/-- Helper for Lemma 4.35.10: the canonical diagonal functor into the categorical self-pullback
of a functor. -/
abbrev categorical_pullback_diagonal_local
    {A : Type (max u v)} {B : Type (max u v)}
    [Category.{v} A] [Category.{v} B]
    (F : A ⥤ B) :
    A ⥤ F ⊡ F :=
  (CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
      (F := F) (G := F) (X := A)).obj
    { fst := 𝟭 A
      snd := 𝟭 A
      iso := Iso.refl _ }

local notation "Δₚ" => categorical_pullback_diagonal_local

/-- Helper for Lemma 4.35.10: a fully faithful functor into a groupoid is essentially surjective
onto the objects of its categorical self-pullback diagonal. -/
private theorem diagonal_essSurj_of_fullyFaithful
    {A : Type (max u v)} {B : Type (max u v)}
    [Category.{v} A] [Category.{v} B] [IsGroupoid B]
    (F : A ⥤ B) (hF : Nonempty F.FullyFaithful) :
    (Δₚ F).EssSurj := by
  rcases hF with ⟨hFF⟩
  refine ⟨?_⟩
  intro P
  -- A pullback object is determined by an isomorphism `F.obj P.fst ≅ F.obj P.snd`; pull it back
  -- across full faithfulness to obtain a diagonal source.
  refine ⟨P.fst, ⟨?_⟩⟩
  refine
    CategoricalPullback.mkIso
      (show ((Δₚ F).obj P.fst).fst ≅ P.fst from Iso.refl P.fst)
      (show ((Δₚ F).obj P.fst).snd ≅ P.snd from hFF.preimageIso P.iso)
      ?_
  simpa using (hFF.map_preimage P.iso.hom).symm

/- Internal categorical bridge: on fibers, the target category is a groupoid, so the diagonal
captures exactly the full-faithfulness data of the functor. -/
private theorem fullyFaithful_iff_diagonal_to_self_pullback_isEquivalence
    {A : Type (max u v)} {B : Type (max u v)}
    [Category.{v} A] [Category.{v} B]
    [IsGroupoid B]
    (F : A ⥤ B) :
    Nonempty F.FullyFaithful ↔
      (Δₚ F).IsEquivalence := by
  constructor
  · intro hF
    rcases hF with ⟨hFF⟩
    have hBij :
        ∀ X Y : A, Function.Bijective
          ((Δₚ F).map : (X ⟶ Y) → ((Δₚ F).obj X ⟶ (Δₚ F).obj Y)) := by
      intro X Y
      refine ⟨?_, ?_⟩
      · intro f g hfg
        simpa [categorical_pullback_diagonal_local] using
          congrArg CategoricalPullback.Hom.fst hfg
      · intro φ
        -- A morphism between diagonal objects is a pair with equal images under `F`, hence the
        -- two components coincide by faithfulness of `F`.
        have hsame :
            (show X ⟶ Y from φ.fst) = (show X ⟶ Y from φ.snd) := by
          apply hFF.map_injective
          simpa [categorical_pullback_diagonal_local] using φ.w
        refine ⟨show X ⟶ Y from φ.fst, ?_⟩
        apply CategoricalPullback.hom_ext
        · simp [categorical_pullback_diagonal_local]
        · simpa [categorical_pullback_diagonal_local] using hsame
    -- Combine hom-set bijectivity with the objectwise preimage argument above.
    exact
      (Functor.isEquivalence_iff_full_faithful_essSurj (Δₚ F)).2
        ⟨hBij, diagonal_essSurj_of_fullyFaithful F ⟨hFF⟩⟩
  · intro hΔ
    have hDiag :=
      (Functor.isEquivalence_iff_full_faithful_essSurj (Δₚ F)).1 hΔ
    have hBij := hDiag.1
    have hEss := hDiag.2
    -- Route correction: the converse direction is not a generic pullback theorem. We extract
    -- morphisms in `A` from the diagonal equivalence using fullness on diagonal homs and
    -- essential surjectivity on pullback objects.
    rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
    intro X Y
    refine ⟨?_, ?_⟩
    · intro β₁ β₂ hβ
      let φ : (Δₚ F).obj X ⟶ (Δₚ F).obj Y :=
        ⟨show ((Δₚ F).obj X).fst ⟶ ((Δₚ F).obj Y).fst from β₁,
          show ((Δₚ F).obj X).snd ⟶ ((Δₚ F).obj Y).snd from β₂,
          by
            change F.map β₁ ≫ 𝟙 (F.obj Y) = 𝟙 (F.obj X) ≫ F.map β₂
            simpa using hβ⟩
      obtain ⟨γ, hγ⟩ := (hBij X Y).2 φ
      have hγfst : γ = β₁ := by
        simpa [φ, categorical_pullback_diagonal_local] using
          congrArg CategoricalPullback.Hom.fst hγ
      have hγsnd : γ = β₂ := by
        simpa [φ, categorical_pullback_diagonal_local] using
          congrArg CategoricalPullback.Hom.snd hγ
      exact hγfst.symm.trans hγsnd
    · intro α
      let P : F ⊡ F :=
        { fst := X
          snd := Y
          iso := asIso α }
      obtain ⟨Z, ⟨e⟩⟩ := hEss.mem_essImage P
      -- The chosen diagonal preimage produces `X ← Z → Y`; compose these legs to obtain a
      -- morphism in `A` whose image is exactly `α`.
      refine
        ⟨show X ⟶ Y from
            (show X ⟶ Z from e.inv.fst) ≫ (show Z ⟶ Y from e.hom.snd),
          ?_⟩
      have hInv :
          F.map (show X ⟶ Z from e.inv.fst) =
            α ≫ F.map (show Y ⟶ Z from e.inv.snd) := by
        simpa [P, categorical_pullback_diagonal_local] using e.inv.w
      have hCancel :
          F.map (show Y ⟶ Z from e.inv.snd) ≫
              F.map (show Z ⟶ Y from e.hom.snd) =
            𝟙 (F.obj Y) := by
        have hsnd : e.inv.snd ≫ e.hom.snd = 𝟙 P.snd := by
          exact congrArg CategoricalPullback.Hom.snd e.inv_hom_id
        simpa [Functor.map_comp] using congrArg (fun f => F.map f) hsnd
      calc
        F.map
              ((show X ⟶ Z from e.inv.fst) ≫
                (show Z ⟶ Y from e.hom.snd))
            = F.map (show X ⟶ Z from e.inv.fst) ≫
                F.map (show Z ⟶ Y from e.hom.snd) := by simp
        _ = (α ≫ F.map (show Y ⟶ Z from e.inv.snd)) ≫
              F.map (show Z ⟶ Y from e.hom.snd) := by rw [hInv]
        _ = α ≫ F.map (show Y ⟶ Z from e.inv.snd) ≫
              F.map (show Z ⟶ Y from e.hom.snd) := by
            simpa using
              (Category.assoc α
                (F.map (show Y ⟶ Z from e.inv.snd))
                (F.map (show Z ⟶ Y from e.hom.snd)))
        _ = α := by
          simpa [Category.assoc] using congrArg (fun f => α ≫ f) hCancel

section

variable {C : Type (max u v)} {S : Type (max u v)} {S' : Type (max u v)}
  [Category.{v} C] [Category.{v} S] [Category.{v} S']
variable {p : S ⥤ C} {p' : S' ⥤ C} [IsFibredInGroupoids p] [IsFibredInGroupoids p']
variable (F : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor p')

local instance : IsFibredInGroupoids (BasedCategory.ofFunctor p).p := by
  simpa using (inferInstance : IsFibredInGroupoids p)

local instance : IsFibredInGroupoids (BasedCategory.ofFunctor p').p := by
  simpa using (inferInstance : IsFibredInGroupoids p')

/- Domain-style sampling for the auxiliary bridge layer of Lemma 4.35.10:
- primary domain: based functors between categories fibred in groupoids over a fixed base and the
  canonical diagonal functor over that base;
- sampled owner-level declarations:
  `FibredInGroupoidsMor`,
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsMor.diagonalMor`,
  `relativeDiagonalOver`,
  `FibredInGroupoidsMor.fullyFaithful_iff_fiberwise`;
- best owner abstraction for the final source-facing statement: `FibredInGroupoidsMor`; the raw
  `BasedFunctor` theorem here is the bridge/view used to prove that owner-level statement;
- primitive data at this bridge layer: only the based functor `F`;
- derived API: the diagonal equivalence-over-base criterion and its fiberwise restatement.

Source/core/bridge triage:
- `source-facing`: the bundled `FibredInGroupoidsMor` theorem stated below;
- `core/canonical`: `Nonempty F.FullyFaithful`,
  `F.relativeDiagonalOver.IsEquivalenceOverBase`;
- `bridge/view`: the comparison between the raw diagonal-over-base criterion and the diagonal of
  each fiber functor. -/

-- Proof sketch: apply Lemma `4.35.9` to the diagonal based functor over `C`, so the global
-- diagonal equivalence criterion reduces to equivalence on each fiber. On the fiber over `U`, the
-- owner-level relative diagonal `BasedFunctor.relativeDiagonalOver F` specializes to the
-- explicit self-`2`-fibre-product model from Lemma `4.35.7`. On each fiber over `U`, its induced
-- functor is the canonical diagonal `Δₚ (F.fiberFunctor U)`.
/-- Helper for Lemma 4.35.10: on a diagonal fiber object, the comparison isomorphism coming from
`fibreOfPullback_equiv_pullbackOfFibres` has identity underlying morphism. -/
private theorem relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_app_iso_hom
    (x : S) :
    Functor.Fiber.fiberInclusion.map
      (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
          ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj (Functor.Fiber.mk rfl))).iso.hom) =
        𝟙 (F.obj x) := by
  -- The diagonal object is sent to the same fibre isomorphism, so the comparison is literally
  -- the identity map in the ambient category.
  rfl

/-- Helper for Lemma 4.35.10: objectwise, the fiber of the owner-level relative diagonal matches
the canonical diagonal object in the categorical pullback of fibres. -/
private noncomputable abbrev relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_app_iso
    (U : C) (x : p.Fiber U) :
    ((((F.relativeDiagonalOver).fiberFunctor U) ⋙
          (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor).obj x) ≅
      ((Δₚ (F.fiberFunctor U)).obj x) := by
  -- Route correction: compare the two pullback objects by their projections instead of forcing a
  -- strict equality of functors through transport terms.
  cases x with
  | mk x hx =>
      cases hx
      refine CategoricalPullback.mkIso ?_ ?_ ?_
      · exact Iso.refl (Functor.Fiber.mk rfl)
      · exact Iso.refl (Functor.Fiber.mk rfl)
      -- The comparison iso in the explicit pullback model is the identity after forgetting back
      -- to the ambient fibre, so extensionality in the fibre closes the pullback compatibility.
      apply Functor.Fiber.hom_ext
      -- Both identity legs forget to `F.map (𝟙 x)`, while the diagonal structural map forgets to
      -- `𝟙 (F.obj x)`, so the compatibility reduces to the previously normalized comparison map.
      simp only [Functor.map_comp]
      have hleft :
          F.map
              (Functor.Fiber.fiberInclusion.map
                (𝟙 (Functor.Fiber.mk rfl : p.Fiber (p.obj x)))) =
            F.map (𝟙 x) := by
        rfl
      have hright :
          Functor.Fiber.fiberInclusion.map
              (((Δₚ (F.fiberFunctor (p.obj x))).obj (Functor.Fiber.mk rfl)).iso.hom) =
            𝟙 (F.obj x) := by
        rfl
      have hleft' :
          Functor.Fiber.fiberInclusion.map
              ((F.fiberFunctor (p.obj x)).map (Iso.refl (Functor.Fiber.mk rfl)).hom) =
            F.map (𝟙 x) := by
        rfl
      have h₁ :
          Functor.Fiber.fiberInclusion.map
              ((F.fiberFunctor (p.obj x)).map (Iso.refl (Functor.Fiber.mk rfl)).hom) ≫
            Functor.Fiber.fiberInclusion.map
              (((Δₚ (F.fiberFunctor (p.obj x))).obj (Functor.Fiber.mk rfl)).iso.hom) =
          F.map (𝟙 x) := by
        have h₁a :
            Functor.Fiber.fiberInclusion.map
                ((F.fiberFunctor (p.obj x)).map (Iso.refl (Functor.Fiber.mk rfl)).hom) ≫
              Functor.Fiber.fiberInclusion.map
                (((Δₚ (F.fiberFunctor (p.obj x))).obj (Functor.Fiber.mk rfl)).iso.hom) =
              F.map (𝟙 x) ≫
                Functor.Fiber.fiberInclusion.map
                  (((Δₚ (F.fiberFunctor (p.obj x))).obj (Functor.Fiber.mk rfl)).iso.hom) := by
          rw [hleft']
          rfl
        have h₁b :
            F.map (𝟙 x) ≫
                Functor.Fiber.fiberInclusion.map
                  (((Δₚ (F.fiberFunctor (p.obj x))).obj (Functor.Fiber.mk rfl)).iso.hom) =
              F.map (𝟙 x) := by
          simpa [hright]
        exact h₁a.trans h₁b
      have h₂ : F.map (𝟙 x) = 𝟙 (F.obj x) ≫ F.map (𝟙 x) := by
        simp
      have h₃ :
          𝟙 (F.obj x) ≫ F.map (𝟙 x) =
            Functor.Fiber.fiberInclusion.map
                (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                    ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                      (Functor.Fiber.mk rfl))).iso.hom) ≫
              F.map (𝟙 x) := by
        rw [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_app_iso_hom
          (F := F) x]
        rfl
      have h₄ :
          Functor.Fiber.fiberInclusion.map
              (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                  ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                    (Functor.Fiber.mk rfl))).iso.hom) ≫
            F.map (𝟙 x) =
              Functor.Fiber.fiberInclusion.map
                (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                    ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                      (Functor.Fiber.mk rfl))).iso.hom) ≫
                F.map
                  (Functor.Fiber.fiberInclusion.map
                    (𝟙 (Functor.Fiber.mk rfl : p.Fiber (p.obj x)))) := by
        simpa using
          congrArg
            (fun k =>
              Functor.Fiber.fiberInclusion.map
                  (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                      ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                        (Functor.Fiber.mk rfl))).iso.hom) ≫
                k)
            hleft.symm
      exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- Helper for Lemma 4.35.10: after passing to the explicit self-pullback model, the left
projection of the relative diagonal fiber is definitionally the identity fiber functor. -/
private theorem relativeDiagonalOver_fiberFunctor_comp_leftProjection
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.explicitTwoFibreProductLeftProjection F F).fiberFunctor U =
      𝟭 (p.Fiber U) := by
  rfl

/-- Helper for Lemma 4.35.10: after passing to the explicit self-pullback model, the right
projection of the relative diagonal fiber is definitionally the identity fiber functor. -/
private theorem relativeDiagonalOver_fiberFunctor_comp_rightProjection
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.explicitTwoFibreProductRightProjection F F).fiberFunctor U =
      𝟭 (p.Fiber U) := by
  rfl

/-- Helper for Lemma 4.35.10: the left projection of the transported owner-level diagonal fiber
is the identity functor on the source fiber. -/
private theorem relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₁
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U) =
      𝟭 (p.Fiber U) := by
  -- Compose the packaged pullback equivalence with its left projection formula, then observe
  -- that the relative diagonal remembers the left fibre coordinate definitionally.
  calc
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U)
        =
          ((F.relativeDiagonalOver).fiberFunctor U) ⋙
            (CategoryOver.explicitTwoFibreProductLeftProjection F F).fiberFunctor U := by
              simpa [Functor.assoc] using
                congrArg
                  (fun H =>
                    ((F.relativeDiagonalOver).fiberFunctor U) ⋙ H)
                  (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₁
                    (F := F) (G := F) U)
    _ = 𝟭 (p.Fiber U) :=
      relativeDiagonalOver_fiberFunctor_comp_leftProjection (F := F) U

/-- Helper for Lemma 4.35.10: the right projection of the transported owner-level diagonal fiber
is the identity functor on the source fiber. -/
private theorem relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₂
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U) =
      𝟭 (p.Fiber U) := by
  -- The same calculation with the right projection gives the symmetric identity functor.
  calc
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U)
        =
          ((F.relativeDiagonalOver).fiberFunctor U) ⋙
            (CategoryOver.explicitTwoFibreProductRightProjection F F).fiberFunctor U := by
              simpa [Functor.assoc] using
                congrArg
                  (fun H =>
                    ((F.relativeDiagonalOver).fiberFunctor U) ⋙ H)
                  (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres_functor_comp_pi₂
                    (F := F) (G := F) U)
    _ = 𝟭 (p.Fiber U) :=
      relativeDiagonalOver_fiberFunctor_comp_rightProjection (F := F) U

/-- Helper for Lemma 4.35.10: after projecting to the left fiber coordinate, the transported
owner-level diagonal agrees with the categorical diagonal. -/
private noncomputable abbrev
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
    (U : C) :
    (((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U)) ≅
      (Δₚ (F.fiberFunctor U)) ⋙
        CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U) :=
  NatIso.ofComponents
    (fun x ↦
      eqToIso
        (congrArg
          (fun H =>
            H.obj x)
          (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₁
            (F := F) U)))
    (fun {x y} f ↦ by
    -- Both projected functors are the identity on the source fiber, so the map comparison is
    -- exactly the functor-congruence statement for the left projection.
    erw [Functor.congr_hom
      (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₁
        (F := F) U) f]
    simp [Category.assoc])

/-- Helper for Lemma 4.35.10: after projecting to the right fiber coordinate, the transported
owner-level diagonal agrees with the categorical diagonal. -/
private noncomputable abbrev
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
    (U : C) :
    (((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ⋙
        CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U)) ≅
      (Δₚ (F.fiberFunctor U)) ⋙
        CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U) :=
  NatIso.ofComponents
    (fun x ↦
      eqToIso
        (congrArg
          (fun H =>
            H.obj x)
          (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₂
            (F := F) U)))
    (fun {x y} f ↦ by
    -- The right projection is symmetric: both functors are again the identity on each fiber.
    erw [Functor.congr_hom
      (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₂
        (F := F) U) f]
    simp [Category.assoc])

/-- Helper for Lemma 4.35.10: transporting a fiber object along an equality between an
endofunctor and the identity gives the corresponding transport morphism in the ambient category. -/
private theorem fiberInclusion_map_eqToHom_functor_obj
    {U : C} {J : p.Fiber U ⥤ p.Fiber U}
    (e : J = 𝟭 (p.Fiber U)) (x : p.Fiber U) :
    Functor.Fiber.fiberInclusion.map
      (eqToHom (congrArg (fun H => H.obj x) e)) =
        eqToHom
          (congrArg
            (fun H =>
              Functor.Fiber.fiberInclusion.obj (H.obj x))
            e) := by
  cases e
  rfl

/-- Helper for Lemma 4.35.10: after forgetting to the ambient category, the left projected
component of the comparison isomorphism is the identity map. -/
@[simp] private theorem
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso_app_hom
    (x : S) :
    Functor.Fiber.fiberInclusion.map
      (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
          (F := F) (p.obj x)).hom.app
        (Functor.Fiber.mk rfl))) = 𝟙 x := by
  -- The component is the transport attached to the left projected functor equality.
  simpa [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso] using
    fiberInclusion_map_eqToHom_functor_obj
      (p := p)
      (e :=
        relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₁
          (F := F) (p.obj x))
      (x := Functor.Fiber.mk rfl)

/-- Helper for Lemma 4.35.10: after forgetting to the ambient category, the right projected
component of the comparison isomorphism is the identity map. -/
@[simp] private theorem
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso_app_hom
    (x : S) :
    Functor.Fiber.fiberInclusion.map
      (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
          (F := F) (p.obj x)).hom.app
        (Functor.Fiber.mk rfl))) = 𝟙 x := by
  -- The right projected component is the same transport shape, hence also forgets to the identity.
  simpa [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso] using
    fiberInclusion_map_eqToHom_functor_obj
      (p := p)
      (e :=
        relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₂
          (F := F) (p.obj x))
      (x := Functor.Fiber.mk rfl)

/-- Helper for Lemma 4.35.10: after applying `F`, the left projected comparison component still
forgets to the identity on `F.obj x`. -/
@[simp] private theorem
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso_app_hom_map
    (x : S) :
    F.map
        (Functor.Fiber.fiberInclusion.map
          (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
              (F := F) (p.obj x)).hom.app
            (Functor.Fiber.mk rfl)))) =
      𝟙 (F.obj x) := by
  rw [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso_app_hom
    (F := F) x]
  exact F.map_id x

/-- Helper for Lemma 4.35.10: after applying `F`, the right projected comparison component still
forgets to the identity on `F.obj x`. -/
@[simp] private theorem
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso_app_hom_map
    (x : S) :
    F.map
        (Functor.Fiber.fiberInclusion.map
          (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
              (F := F) (p.obj x)).hom.app
            (Functor.Fiber.mk rfl)))) =
      𝟙 (F.obj x) := by
  rw [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso_app_hom
    (F := F) x]
  exact F.map_id x

/-- Helper for Lemma 4.35.10: the projected comparison isomorphisms satisfy the pullback
coherence relation needed to reconstruct the full comparison `NatIso`. -/
private theorem
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_projection_coherence
    (U : C) :
    Functor.whiskerRight
        (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
          (F := F) U).hom
        (F.fiberFunctor U) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (Δₚ (F.fiberFunctor U))
          (CatCommSq.iso
            (CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U))
            (CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U))
            (F.fiberFunctor U) (F.fiberFunctor U)).hom ≫
        (Functor.associator _ _ _).inv =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft
          (((F.relativeDiagonalOver).fiberFunctor U) ⋙
            (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor)
          (CatCommSq.iso
            (CategoricalPullback.π₁ (F.fiberFunctor U) (F.fiberFunctor U))
            (CategoricalPullback.π₂ (F.fiberFunctor U) (F.fiberFunctor U))
            (F.fiberFunctor U) (F.fiberFunctor U)).hom ≫
        (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight
          (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
            (F := F) U).hom
          (F.fiberFunctor U) := by
  ext x
  cases x with
  | mk x hx =>
      cases hx
      -- The target diagonal carries the identity comparison, while the transported owner-level
      -- diagonal has the same underlying comparison map by the explicit pullback-of-fibres model.
      have hcomp :
          F.map
              (Functor.Fiber.fiberInclusion.map
                (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
                    (F := F) (p.obj x)).hom.app
                  (Functor.Fiber.mk rfl)))) =
            Functor.Fiber.fiberInclusion.map
              (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                  ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                    (Functor.Fiber.mk rfl))).iso.hom) ≫
              F.map
                (Functor.Fiber.fiberInclusion.map
                  (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
                      (F := F) (p.obj x)).hom.app
                    (Functor.Fiber.mk rfl)))) := by
        rw [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso_app_hom_map
          (F := F) x]
        have hright :
            Functor.Fiber.fiberInclusion.map
                (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                    ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                      (Functor.Fiber.mk rfl))).iso.hom) =
              Functor.Fiber.fiberInclusion.map
                  (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                      ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                        (Functor.Fiber.mk rfl))).iso.hom) ≫
                F.map
                  (Functor.Fiber.fiberInclusion.map
                    (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
                        (F := F) (p.obj x)).hom.app
                      (Functor.Fiber.mk rfl)))) := by
          have hmap :=
            relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso_app_hom_map
              (F := F) x
          let mid :
              F.obj x ⟶ F.obj x :=
            Functor.Fiber.fiberInclusion.map
              (((CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F (p.obj x)).functor.obj
                  ((F.relativeDiagonalOver.fiberFunctor (p.obj x)).obj
                    (Functor.Fiber.mk rfl))).iso.hom)
          have hmap' :
              F.map
                  (Functor.Fiber.fiberInclusion.map
                    (eqToHom
                      (congrArg
                        (fun H =>
                          H.obj (Functor.Fiber.mk rfl))
                        (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_comp_pi₂
                          (F := F) (p.obj x))))) =
                𝟙 (F.obj x) := by
            simpa [relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso] using
              hmap
          calc
            mid = mid ≫ 𝟙 (F.obj x) := by
              simp [mid]
            _ = mid ≫
                  F.map
                    (Functor.Fiber.fiberInclusion.map
                      (((relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
                          (F := F) (p.obj x)).hom.app
                        (Functor.Fiber.mk rfl)))) := by
                          simpa [mid] using congrArg (fun k => mid ≫ k) hmap.symm
        exact
          (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_app_iso_hom
            (F := F) x).symm.trans hright
      simpa [NatTrans.comp_app, Functor.comp_map, Category.assoc] using hcomp

/-- Helper for Lemma 4.35.10: after transporting the fiber of the owner-level relative diagonal
across the canonical pullback-of-fibres equivalence, one obtains the categorical diagonal of the
fiber functor up to natural isomorphism. -/
private noncomputable abbrev relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_iso_diagonal
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U) ⋙
        (CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U).functor ≅
      Δₚ (F.fiberFunctor U) := by
  -- Route correction: package the comparison through the two pullback projections and then use
  -- the explicit pullback-of-fibres normalization to recover the full diagonal isomorphism.
  exact
    CategoricalPullback.mkNatIso
      (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_first_iso
        (F := F) U)
      (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_second_iso
        (F := F) U)
      (relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_projection_coherence
        (F := F) U)

/-- Helper for Lemma 4.35.10: the fiber of the owner-level relative diagonal is an equivalence
exactly when the categorical diagonal of the fiber functor is an equivalence. -/
private theorem relativeDiagonalOver_fiberFunctor_isEquivalence_iff_diagonal_isEquivalence
    (U : C) :
    ((F.relativeDiagonalOver).fiberFunctor U).IsEquivalence ↔
      (Δₚ (F.fiberFunctor U)).IsEquivalence := by
  let E := CategoryOver.fibreOfPullback_equiv_pullbackOfFibres F F U
  let e :
      ((F.relativeDiagonalOver).fiberFunctor U) ⋙ E.functor ≅
        Δₚ (F.fiberFunctor U) :=
    relativeDiagonalOver_fiberFunctor_comp_pullback_equiv_functor_iso_diagonal
      (F := F) U
  constructor
  · intro hDiagonal
    -- Compose the fiber functor with the canonical equivalence to move into the categorical
    -- pullback model used by the purely categorical diagonal criterion.
    letI : ((F.relativeDiagonalOver).fiberFunctor U).IsEquivalence := hDiagonal
    letI : E.functor.IsEquivalence := by infer_instance
    have hComp :
        (((F.relativeDiagonalOver).fiberFunctor U) ⋙ E.functor).IsEquivalence :=
      inferInstance
    exact (Functor.isEquivalence_iff_of_iso e).1 hComp
  · intro hDiagonal
    -- The converse transports the diagonal equivalence back across the same packaged
    -- equivalence, then cancels it from the right.
    letI : E.functor.IsEquivalence := by infer_instance
    have hComp :
        (((F.relativeDiagonalOver).fiberFunctor U) ⋙ E.functor).IsEquivalence := by
      exact (Functor.isEquivalence_iff_of_iso e).2 hDiagonal
    exact Functor.isEquivalence_of_comp_right ((F.relativeDiagonalOver).fiberFunctor U) E.functor

private theorem basedFunctor_diagonal_isEquivalenceOverBase_iff_fiberwise :
    F.relativeDiagonalOver.IsEquivalenceOverBase ↔
      ∀ U : C, (Δₚ (F.fiberFunctor U)).IsEquivalence := by
  constructor
  · intro hDiagonal U
    -- Lemma 4.35.9 reduces the owner-level equivalence-over-base condition to each fiber, and the
    -- fixed-fiber bridge above rewrites those fibers as the textbook diagonal functors.
    exact
      (relativeDiagonalOver_fiberFunctor_isEquivalence_iff_diagonal_isEquivalence
        (F := F) U).1
        (BasedFunctor.fiberFunctor_isEquivalence_of_isEquivalenceOverBase
          F.relativeDiagonalOver hDiagonal U)
  · intro hFiber
    -- Package the diagonal as a morphism of categories fibred in groupoids and invoke the
    -- fiberwise equivalence criterion from Lemma 4.35.9.
    let ownerF :
        FibredInGroupoidsOver.ofFunctor (BasedCategory.ofFunctor p).p ⟶
          FibredInGroupoidsOver.ofFunctor (BasedCategory.ofFunctor p').p :=
      FibredInGroupoidsMor.ofBasedFunctor F
    letI :
        IsFibredInGroupoids (CategoryOver.explicitTwoFibreProduct F F).p :=
      by
        simpa [ownerF] using
          (FibredInGroupoidsMor.diagonalTargetProjection_isFibredInGroupoids
            (F := ownerF))
    let diagonalMor :
        FibredInGroupoidsOver.ofFunctor (BasedCategory.ofFunctor p).p ⟶
          FibredInGroupoidsOver.ofFunctor
            (CategoryOver.explicitTwoFibreProduct F F).p :=
      FibredInGroupoidsMor.ofBasedFunctor F.relativeDiagonalOver
    have hEq :
        (FibredInGroupoidsMor.G diagonalMor).IsEquivalence := by
      refine (FibredInGroupoidsMor.isEquivalence_iff_fiberwise (F := diagonalMor)).2 ?_
      intro U
      simpa [diagonalMor] using
        (relativeDiagonalOver_fiberFunctor_isEquivalence_iff_diagonal_isEquivalence
          (F := F) U).2 (hFiber U)
    simpa [diagonalMor] using
      (FibredInGroupoidsMor.isEquivalenceOverBase_of_isEquivalence
        (F := diagonalMor) hEq)

-- Proof sketch: the textbook statement is the global diagonal criterion in `Cat/C`, realized by
-- the explicit fibred `2`-fibre-product model from Lemma `4.35.7`.
end

namespace FibredInGroupoidsMor

section

open FibredInGroupoidsOver

variable {C : Type (max u v)} [Category.{v} C]
variable {X Y : FibredInGroupoidsOver.{v, max u v, max u v, v} C}
variable (F : X ⟶ Y)

/- Domain-style sampling for Lemma 4.35.10:
- primary domain: morphisms of categories fibred in groupoids over a fixed base together with
  their canonical diagonal into the fibred self-`2`-fibre product;
- sampled owner-level declarations:
  `FibredInGroupoidsMor`,
  `FibredInGroupoidsOver.twoFibreProduct`,
  `FibredInGroupoidsMor.diagonalMor`,
  `FibredInGroupoidsMor.fiberFunctor`,
  `FibredInGroupoidsMor.IsEquivalenceOverBase`;
- best owner abstraction: the morphism `F : FibredInGroupoidsMor X Y`, with the target owner
  `FibredInGroupoidsOver.twoFibreProduct F F` and the bundled canonical diagonal `F.diagonalMor`;
- primitive data: only the owner morphism `F`;
- derived API: the fully-faithful criterion expressed directly in terms of the canonical diagonal
  over-base equivalence predicate.

Source/core/bridge triage:
- `source-facing`: Lemma 4.35.10 on `FibredInGroupoidsMor`;
- `core/canonical`: `Nonempty F.FullyFaithful` and the owner predicate
  `F.diagonalMor.IsEquivalenceOverBase`;
- `bridge/view`: the raw `BasedFunctor` diagonal criterion above. -/

/-- Companion bridge: the owner-level diagonal of `F` is an equivalence over the base exactly
when the induced diagonal on every fiber is an equivalence. -/
theorem diagonal_isEquivalenceOverBase_iff_fiberwise :
    IsEquivalenceOverBase (diagonalMor F) ↔
      ∀ U : C, (Δₚ (fiberFunctor F U)).IsEquivalence := by
  simpa [FibredInGroupoidsMor.diagonalMor] using
    basedFunctor_diagonal_isEquivalenceOverBase_iff_fiberwise (toBasedFunctor F)

/-- Lemma 4.35.10: a morphism of categories fibred in groupoids over `C` is fully faithful if and
only if its canonical diagonal into the fibred self-`2`-fibre product is an equivalence over
`C`. The target is the chapter owner `FibredInGroupoidsOver.twoFibreProduct F F`, and the
diagonal is the bundled owner morphism `F.diagonalMor`.
-/
theorem fullyFaithful_iff_diagonal_isEquivalenceOverBase :
    Nonempty (toBasedFunctor F).FullyFaithful ↔ IsEquivalenceOverBase (diagonalMor F) := by
  rw [diagonal_isEquivalenceOverBase_iff_fiberwise, fullyFaithful_iff_fiberwise]
  constructor
  · intro hF U
    exact
      (fullyFaithful_iff_diagonal_to_self_pullback_isEquivalence (fiberFunctor F U)).mp (hF U)
  · intro hΔ U
    exact
      (fullyFaithful_iff_diagonal_to_self_pullback_isEquivalence (fiberFunctor F U)).mpr (hΔ U)

end

end FibredInGroupoidsMor

end CategoryTheory
