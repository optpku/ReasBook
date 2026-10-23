module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Example_7_10_2
public import stacks_project.Chap07.Lemma_7_12_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.GrothendieckTopology

open scoped SheafifiedRepresentable
open scoped TerminalSheaf

attribute [local instance] CategoryTheory.Types.instConcreteCategory
attribute [local instance] CategoryTheory.Types.instFunLike

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type (max u v))]

variable {J}
variable {U V : C} (a b : V ⟶ U)

/- Domain-style sampling for Lemma 7.45.2:
- primary domain: global sections of sheaves of types, viewed through Hom-sets out of the
  sheafified representables `h[U]^#[J]` and the terminal sheaf;
- sampled owner API:
  `GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv`,
  `Sheaf.ΓObjEquivHom`,
  `Sheaf.ΓRes`,
  `Cofork.IsColimit.homIso`;
- best owner abstraction: apply `Hom(-, ℱ)` to the source-facing coequalizer
  `h[V]^#[J] ⇉ h[U]^#[J] ⟶ 1` and then identify the resulting Hom-sets by the canonical
  sheafified-Yoneda and global-sections equivalences;
- primitive data: the coequalizer cofork in `Sheaf J (Type (max u v))`;
- derived API: the equalizer cone on `Γ(C, ℱ) ⟶ ℱ(U) ⇉ ℱ(V)`.

Source/core/bridge triage:
- `source-facing`: the public equalizer statement on global sections;
- `core/canonical`: `uliftSheafifiedRepresentableHomEquiv`, `Sheaf.ΓRes`, and
  `Cofork.IsColimit.homIso`;
- `bridge/view`: the local comparison between morphisms from the constant singleton sheaf and
  the chosen terminal singleton sheaf `*[J]`.

Accordingly the public theorem below stays source-facing, while the proof reuses the owner-level
Hom equivalences rather than introducing a parallel coequalizer/equalizer API. -/

-- Proof sketch: the explicit terminal singleton sheaf is terminal, so the two composites agree by
-- uniqueness of morphisms into a terminal object.
theorem sheafifiedRepresentable_to_terminalSheaf_condition :
    J.sheafifiedRepresentableMap a ≫ (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ =
      J.sheafifiedRepresentableMap b ≫ (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ := by
  simp

-- Proof sketch: the chosen terminal singleton sheaf is canonically the constant singleton sheaf
-- after sheafification, so the owner equivalence `Sheaf.ΓObjEquivHom` specializes to morphisms
-- from this terminal sheaf.
noncomputable def constantSheafPUnitIsoTerminalSheaf :
    (constantSheaf J (Type (max u v))).obj PUnit.{(max u v) + 1} ≅
      *[J] := by
  simpa [constantSheaf, Sheaf.terminal] using (sheafificationIso (*[J])).symm

noncomputable def globalSectionsEquivTerminalSheafHom
    (ℱ : Sheaf J (Type (max u v))) :
    (Sheaf.Γ J (Type (max u v))).obj ℱ ≃ (*[J] ⟶ ℱ) :=
  (Sheaf.ΓObjEquivHom J ℱ PUnit.{(max u v) + 1}).trans
    ((constantSheafPUnitIsoTerminalSheaf).homCongr (Iso.refl ℱ))

-- Proof sketch: after transporting along the sheafification adjunction, the unique map from
-- `h_U^#` to the terminal singleton sheaf is sent by
-- `uliftSheafifiedRepresentableHomEquiv` to `PUnit.unit`, so composition with `τ` evaluates to
-- `τ.app (op U) ()`.
theorem sheafifiedRepresentableHomEquiv_terminalSheaf_comp
    (ℱ : Sheaf J (Type (max u v))) (W : C) (τ : *[J] ⟶ ℱ) :
    J.uliftSheafifiedRepresentableHomEquiv ℱ W
        ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ τ) =
      τ.hom.app (op W) PUnit.unit := by
  calc
    CategoryTheory.uliftYonedaEquiv
        (((sheafificationAdjunction J (Type (max u v))).homEquiv
            (CategoryTheory.uliftYoneda.{max u v}.obj W) ℱ)
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ τ)) =
      τ.hom.app (op W)
        (J.uliftSheafifiedRepresentableHomEquiv *[J] W
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _)) := by
            simpa using
              (J.uliftSheafifiedRepresentableHomEquiv_comp
                ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from (h[W]^#[J])) τ)
    _ = τ.hom.app (op W) PUnit.unit := by
      simp [GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv, Sheaf.terminal]

-- Proof sketch: the owner equivalence `Sheaf.ΓObjEquivHom` sends a global section to the induced
-- morphism from the constant singleton sheaf, and evaluating that morphism at the unique element
-- recovers the usual restriction map `ΓRes`.
theorem globalSectionsEquivTerminalSheafHom_app_eq_res
    (ℱ : Sheaf J (Type (max u v))) (W : C)
    (x : (Sheaf.Γ J (Type (max u v))).obj ℱ) :
    ((globalSectionsEquivTerminalSheafHom ℱ x).hom.app (op W) PUnit.unit) =
      Sheaf.ΓRes ℱ (op W) x := by
  have h := congr_fun
    (congr_app
      (Sheaf.ΓHomEquiv_naturality_left_symm
        (show PUnit.{(max u v) + 1} ⟶ (Sheaf.Γ J (Type (max u v))).obj ℱ from
          (Equiv.funUnique PUnit _).symm x)
        (𝟙 _))
      (op W))
    PUnit.unit
  simpa [globalSectionsEquivTerminalSheafHom, constantSheafPUnitIsoTerminalSheaf,
    Sheaf.ΓObjEquivHom, Sheaf.ΓRes, Sheaf.coneΓ] using h

theorem sheafifiedRepresentableHomEquiv_globalSection_comp
    (ℱ : Sheaf J (Type (max u v))) (W : C)
    (x : (Sheaf.Γ J (Type (max u v))).obj ℱ) :
    J.uliftSheafifiedRepresentableHomEquiv ℱ W
        ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫
          globalSectionsEquivTerminalSheafHom ℱ x) =
      Sheaf.ΓRes ℱ (op W) x := by
  calc
    J.uliftSheafifiedRepresentableHomEquiv ℱ W
        ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫
          globalSectionsEquivTerminalSheafHom ℱ x) =
      (globalSectionsEquivTerminalSheafHom ℱ x).hom.app (op W) PUnit.unit := by
        simpa using
          sheafifiedRepresentableHomEquiv_terminalSheaf_comp ℱ W
            (globalSectionsEquivTerminalSheafHom ℱ x)
    _ = Sheaf.ΓRes ℱ (op W) x := by
        exact globalSectionsEquivTerminalSheafHom_app_eq_res ℱ W x

-- Proof sketch: apply `Hom(-, ℱ)` to the given coequalizer cofork
-- `h_V^# ⇉ h_U^# ⟶ *`. The resulting map on global sections equalizes the two pullback maps.
theorem globalSections_equalizer_condition
    (ℱ : Sheaf J (Type (max u v))) :
    Sheaf.ΓRes ℱ (op U) ≫ ℱ.obj.map a.op =
      Sheaf.ΓRes ℱ (op U) ≫ ℱ.obj.map b.op := by
  ext x
  let β : *[J] ⟶ ℱ :=
    globalSectionsEquivTerminalSheafHom ℱ x
  have hw :
      J.sheafifiedRepresentableMap a ≫ (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β =
        J.sheafifiedRepresentableMap b ≫ (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫
          β := by
    exact congrArg (fun k ↦ k ≫ β) (sheafifiedRepresentable_to_terminalSheaf_condition a b)
  calc
    ℱ.obj.map a.op (Sheaf.ΓRes ℱ (op U) x) =
      ℱ.obj.map a.op
        (J.uliftSheafifiedRepresentableHomEquiv ℱ U
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β)) := by
            rw [sheafifiedRepresentableHomEquiv_globalSection_comp ℱ U x]
    _ = J.uliftSheafifiedRepresentableHomEquiv ℱ V
        (J.sheafifiedRepresentableMap a ≫
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β)) := by
            simpa [Category.assoc, sheafifiedRepresentableMap,
              sheafifiedRepresentableFunctor] using
              (J.uliftSheafifiedRepresentableHomEquiv_naturality a ℱ
                ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β)).symm
    _ = J.uliftSheafifiedRepresentableHomEquiv ℱ V
        (J.sheafifiedRepresentableMap b ≫
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β)) := by
            rw [hw]
    _ = ℱ.obj.map b.op
        (J.uliftSheafifiedRepresentableHomEquiv ℱ U
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β)) := by
            simpa [Category.assoc, sheafifiedRepresentableMap,
              sheafifiedRepresentableFunctor] using
              (J.uliftSheafifiedRepresentableHomEquiv_naturality b ℱ
                ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β))
    _ = ℱ.obj.map b.op (Sheaf.ΓRes ℱ (op U) x) := by
            rw [sheafifiedRepresentableHomEquiv_globalSection_comp ℱ U x]

-- Proof sketch: apply `Hom(-, ℱ)` to the given coequalizer cofork
-- `h_V^# ⇉ h_U^# ⟶ *`. By `Limits.Types.type_equalizer_iff_unique`, the resulting equalizer on
-- Hom-sets says that `Γ(C, ℱ)` is the equalizer of the pullback maps `ℱ(U) ⇉ ℱ(V)`.
/-- Lemma 7.45.2: if the canonical cofork
`h[V]^#[J] ⇉ h[U]^#[J] ⟶ *[J]` is a coequalizer in sheaves on
`(C, J)`, then the global sections of `ℱ` are the equalizer of the restriction maps
`ℱ(U) ⇉ ℱ(V)` induced by `a` and `b`. -/
noncomputable def globalSections_is_equalizer_of_sheafifiedRepresentable_coequalizer
    (ℱ : Sheaf J (Type (max u v)))
    (hcoeq : IsColimit
      (Cofork.ofπ ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from
          (h[U]^#[J]))
        (sheafifiedRepresentable_to_terminalSheaf_condition a b))) :
    IsLimit
      (Fork.ofι (Sheaf.ΓRes ℱ (op U)) (globalSections_equalizer_condition a b ℱ)) := by
  refine Limits.Types.typeEqualizerOfUnique
    (Sheaf.ΓRes ℱ (op U))
    (globalSections_equalizer_condition a b ℱ) ?_
  intro y hy
  let α : h[U]^#[J] ⟶ ℱ := (J.uliftSheafifiedRepresentableHomEquiv ℱ U).symm y
  have hα : J.sheafifiedRepresentableMap a ≫ α = J.sheafifiedRepresentableMap b ≫ α := by
    apply (J.uliftSheafifiedRepresentableHomEquiv ℱ V).injective
    calc
      J.uliftSheafifiedRepresentableHomEquiv ℱ V (J.sheafifiedRepresentableMap a ≫ α) =
        ℱ.obj.map a.op (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) := by
          simpa [sheafifiedRepresentableMap, sheafifiedRepresentableFunctor] using
            J.uliftSheafifiedRepresentableHomEquiv_naturality a ℱ α
      _ = ℱ.obj.map b.op (J.uliftSheafifiedRepresentableHomEquiv ℱ U α) := by
          rw [(J.uliftSheafifiedRepresentableHomEquiv ℱ U).apply_symm_apply y]
          exact hy
      _ = J.uliftSheafifiedRepresentableHomEquiv ℱ V (J.sheafifiedRepresentableMap b ≫ α) := by
          symm
          simpa [sheafifiedRepresentableMap, sheafifiedRepresentableFunctor] using
            J.uliftSheafifiedRepresentableHomEquiv_naturality b ℱ α
  let e := Cofork.IsColimit.homIso hcoeq ℱ
  let β : *[J] ⟶ ℱ :=
    e.symm ⟨α, hα⟩
  refine ⟨(globalSectionsEquivTerminalSheafHom ℱ).symm β, ?_, ?_⟩
  · have hβ :
        (Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from (h[U]^#[J]) ≫ β = α := by
      exact congrArg Subtype.val (e.apply_symm_apply ⟨α, hα⟩)
    calc
      Sheaf.ΓRes ℱ (op U) ((globalSectionsEquivTerminalSheafHom ℱ).symm β) =
        J.uliftSheafifiedRepresentableHomEquiv ℱ U
          ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from _ ≫ β) := by
            symm
            simpa [β] using
              (sheafifiedRepresentableHomEquiv_globalSection_comp ℱ U
                ((globalSectionsEquivTerminalSheafHom ℱ).symm β))
      _ = J.uliftSheafifiedRepresentableHomEquiv ℱ U α := by rw [hβ]
      _ = y := by
          exact (J.uliftSheafifiedRepresentableHomEquiv ℱ U).apply_symm_apply y
  · intro x hx
    apply (globalSectionsEquivTerminalSheafHom ℱ).injective
    apply e.injective
    trans ⟨α, hα⟩
    · apply Subtype.ext
      apply (J.uliftSheafifiedRepresentableHomEquiv ℱ U).injective
      calc
        J.uliftSheafifiedRepresentableHomEquiv ℱ U
            ((e (globalSectionsEquivTerminalSheafHom ℱ x)).1) =
          Sheaf.ΓRes ℱ (op U) x := by
            simpa [e, Cofork.IsColimit.homIso] using
              (sheafifiedRepresentableHomEquiv_globalSection_comp ℱ U x)
      _ = y := hx
      _ = J.uliftSheafifiedRepresentableHomEquiv ℱ U α := by
            exact ((J.uliftSheafifiedRepresentableHomEquiv ℱ U).apply_symm_apply y).symm
    · simpa [β] using
        (e.apply_symm_apply ⟨α, hα⟩).symm

-- Proof sketch: apply `Limits.Types.unique_of_type_equalizer` to the equalizer witness
-- constructed above; this directly packages the unique global section restricting to the
-- compatible section `y`.
/-- A section of `ℱ(U)` whose pullbacks along `a` and `b` agree comes from a unique global section
of `ℱ` whenever `h[V]^#[J] ⇉ h[U]^#[J] ⟶ *[J]` is a coequalizer. -/
theorem globalSections_is_equalizer_of_sheafifiedRepresentable_coequalizer_existsUnique
    (ℱ : Sheaf J (Type (max u v)))
    (hcoeq : IsColimit
      (Cofork.ofπ ((Sheaf.isTerminalTerminal J Types.isTerminalPUnit).from
          (h[U]^#[J]))
        (sheafifiedRepresentable_to_terminalSheaf_condition a b)))
    (y : ℱ.obj.obj (op U))
    (hy : ℱ.obj.map a.op y = ℱ.obj.map b.op y) :
    ∃! x : (Sheaf.Γ J (Type (max u v))).obj ℱ, Sheaf.ΓRes ℱ (op U) x = y := by
  -- Apply the previously constructed equalizer witness in `Type` to the compatible section `y`.
  simpa using
    (Limits.Types.unique_of_type_equalizer
      (f := Sheaf.ΓRes ℱ (op U))
      (g := ℱ.obj.map a.op)
      (h := ℱ.obj.map b.op)
      (w := globalSections_equalizer_condition a b ℱ)
      (t := globalSections_is_equalizer_of_sheafifiedRepresentable_coequalizer
        (J := J) (a := a) (b := b) ℱ hcoeq)
      y hy)

end CategoryTheory.GrothendieckTopology
