module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Functors
import Mathlib.Tactic.Recall
public import stacks_project.Chap06.Definition_6_15_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe w v u

/- Domain-style sampling for algebraic-structure forgetful functors:
- primary domain: forgetful functors `F : C ⥤ Type w` satisfying the chapter owner predicate
  `IsAlgebraicStructure C F`, together with the canonical comparison isomorphisms expressing the
  source-level identifications of underlying sets for limits and filtered colimits;
- inspected owner declarations:
  `PreservesTerminal.iso`,
  `PreservesProduct.iso`,
  `PreservesPullback.iso`,
  `preservesColimitIso`;
- best owner abstraction:
  the chapter-level owner is `IsAlgebraicStructure C F`, while the main public surface here should
  directly reuse the corresponding comparison isomorphisms rather than restating only their
  projection formulas;
- primitive-vs-derived split:
  primitive data are exactly the fields of `IsAlgebraicStructure C F`;
  terminal/product/pullback/equalizer/filtered-colimit identifications and mono/epi detection are
  derived API, while the induced `ConcreteCategory` structure is only a local bridge for (5) and
  (6).

Source/core/bridge triage:
- `source-facing`: the six clauses of Lemma 6.15.3 about underlying sets and underlying maps for a
  type of algebraic structure;
- `core/canonical`: the preservation comparison isomorphisms and the concrete-category mono/epi
  theorems from mathlib;
- `bridge/view`: the concrete-category structure induced by `F`, used only to access the mono/epi
  owner theorems.
-/

section Terminal

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

/- Lemma 6.15.3 (1): the underlying type of the terminal algebraic structure is canonically
identified with the singleton type. The owner comparison is `PreservesTerminal.iso`, specialized
through `Types.terminalIso`. -/
recall PreservesTerminal.iso

/- Source-facing specialization of the terminal comparison to `PUnit`. -/
#check ((((PreservesTerminal.iso F) ≪≫ Types.terminalIso).toEquiv) :
  F.obj (⊤_ C) ≃ PUnit)

/-- Companion formula: under the canonical terminal identification, every element maps to the
unique point. -/
theorem terminalUnderlyingEquiv_apply (x : F.obj (⊤_ C)) :
    ((PreservesTerminal.iso F ≪≫ Types.terminalIso).hom) x = PUnit.unit := by
  simp

end Terminal

section Products

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
variable {ι : Type w} (A : ι → C) [HasProduct A] [PreservesLimit (Discrete.functor A) F]

/- Lemma 6.15.3 (2): the underlying type of a product is identified with the product of the
underlying types by the canonical owner comparison `PreservesProduct.iso`. -/
recall PreservesProduct.iso

/- Source-facing specialization of the product comparison isomorphism. -/
#check (PreservesProduct.iso F A : F.obj (∏ᶜ A) ≅ ∏ᶜ fun i ↦ F.obj (A i))

/-- Companion formula: the canonical product comparison recovers each underlying projection. -/
theorem productUnderlying_apply (x : F.obj (∏ᶜ A)) (i : ι) :
    Pi.π (fun j ↦ F.obj (A j)) i ((PreservesProduct.iso F A).hom x) =
      F.map (Pi.π A i) x := by
  letI : HasProduct (fun j ↦ F.obj (A j)) := inferInstance
  simpa [PreservesProduct.iso_hom] using congr_fun (piComparison_comp_π F A i) x

end Products

section PullbacksAndEqualizers

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

variable {A B C' : C} (f : A ⟶ B) (g : C' ⟶ B) [HasPullback f g]

/- Lemma 6.15.3 (3): the underlying type of a fibre product is identified with the pullback of the
underlying maps by the canonical owner comparison `PreservesPullback.iso`. -/
recall PreservesPullback.iso

/- Source-facing specialization of the pullback comparison isomorphism. -/
#check (PreservesPullback.iso F f g : F.obj (pullback f g) ≅ pullback (F.map f) (F.map g))

/-- Companion formula: the canonical pullback comparison is compatible with the left projection. -/
theorem pullbackUnderlying_fst_apply (x : F.obj (pullback f g)) :
    pullback.fst (F.map f) (F.map g) ((PreservesPullback.iso F f g).hom x) =
      F.map (pullback.fst f g) x := by
  simpa using congr_fun (PreservesPullback.iso_hom_fst F f g) x

variable {A' B' : C} (f' g' : A' ⟶ B') [HasEqualizer f' g']

/- Lemma 6.15.3 (4): the underlying type of an equalizer is identified with the equalizer of the
underlying maps by the canonical owner comparison `PreservesEqualizer.iso`. -/
recall PreservesEqualizer.iso

/- Source-facing specialization of the equalizer comparison isomorphism. -/
#check (PreservesEqualizer.iso F f' g' :
  F.obj (equalizer f' g') ≅ equalizer (F.map f') (F.map g'))

/-- Companion formula: the canonical equalizer comparison is compatible with the equalizer
inclusion. -/
theorem equalizerUnderlying_apply (x : F.obj (equalizer f' g')) :
    equalizer.ι (F.map f') (F.map g') ((PreservesEqualizer.iso F f' g').hom x) =
      F.map (equalizer.ι f' g') x := by
  simpa [PreservesEqualizer.iso_hom] using congr_fun (equalizerComparison_comp_π f' g' F) x

end PullbacksAndEqualizers

section MonoEpi

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

/-- Helper for Lemma 6.15.3: a mono becomes an injective underlying map after applying the
forgetful functor to types. -/
lemma underlying_injective_of_mono
    {A B : C} (f : A ⟶ B) [Mono f] :
    Function.Injective (F.map f) := by
  -- Map the mono into `Type` and read the result with the standard concrete criterion there.
  letI : Mono (F.map f) := F.map_mono f
  exact (CategoryTheory.mono_iff_injective (F.map f)).1 inferInstance

/-- Helper for Lemma 6.15.3: injectivity of the underlying map makes the mapped kernel-pair
projection an isomorphism. -/
lemma mapped_pullback_fst_isIso_of_underlying_injective
    {A B : C} (f : A ⟶ B) [HasPullback f f] [PreservesLimit (cospan f f) F]
    (hf : Function.Injective (F.map f)) :
    IsIso (F.map (pullback.fst f f)) := by
  -- The kernel pair of an injective map in `Type` has first projection an isomorphism.
  letI : Mono (F.map f) := (CategoryTheory.mono_iff_injective (F.map f)).2 hf
  -- Transport the `Type`-level kernel-pair isomorphism across the pullback comparison of `F`.
  have hcomparison_iso :
      IsIso ((PreservesPullback.iso F f f).hom ≫ pullback.fst (F.map f) (F.map f)) := by
    infer_instance
  simpa [PreservesPullback.iso_hom_fst] using hcomparison_iso

/-- Helper for Lemma 6.15.3: if the underlying map is injective, then the original morphism is
mono. -/
lemma mono_of_underlying_injective
    {A B : C} (f : A ⟶ B) (hf : Function.Injective (F.map f)) :
    Mono f := by
  -- Route correction: rather than using the general concrete-category criterion directly, we
  -- follow the source proof through the kernel pair of `f`.
  let hshape : HasLimitsOfShape WalkingCospan C := inferInstance
  let hpres : PreservesLimitsOfShape WalkingCospan F := inferInstance
  letI : HasPullback f f := hshape.has_limit (cospan f f)
  letI : PreservesLimit (cospan f f) F := hpres.preservesLimit
  letI : IsIso (F.map (pullback.fst f f)) :=
    mapped_pullback_fst_isIso_of_underlying_injective F f hf
  -- Since `F` reflects isomorphisms, the kernel-pair projection is already an isomorphism in `C`.
  letI : IsIso (pullback.fst f f) := isIso_of_reflects_iso (pullback.fst f f) F
  -- An isomorphism on the first kernel-pair projection forces `f` to be mono.
  exact (pullback.diagonal_isKernelPair f).mono_of_isIso_fst

/-- Lemma 6.15.3 (5): a morphism is a monomorphism exactly when its underlying map of types is
injective. -/
theorem mono_iff_underlying_injective
    {A B : C} (f : A ⟶ B) :
    Mono f ↔ Function.Injective (F.map f) := by
  constructor
  · intro hf
    -- The forward direction is the direct image of a mono under `F`.
    letI : Mono f := hf
    exact underlying_injective_of_mono F f
  · intro hf
    -- The converse is the source-faithful kernel-pair argument.
    exact mono_of_underlying_injective F f hf

/-- Lemma 6.15.3 (6): if the underlying map of a morphism under a faithful functor to types is
surjective, then the morphism is an epimorphism. -/
theorem epi_of_underlying_surjective
    {A B : C} (f : A ⟶ B) (hf : Function.Surjective (F.map f)) :
    Epi f := by
  -- Surjectivity makes the mapped morphism epi in `Type`.
  letI : Epi (F.map f) := (CategoryTheory.epi_iff_surjective (F.map f)).2 hf
  -- Because `F` is faithful, it reflects epimorphisms back to `C`.
  exact F.epi_of_epi_map (f := f) inferInstance

end MonoEpi

section FilteredColimit

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)
variable {I : Type v} [Category.{v} I] [IsFiltered I] (D : I ⥤ C)
variable [HasColimit D] [PreservesColimit D F]

/- The filtered-colimit clause of Lemma 6.15.3 is the canonical comparison isomorphism
`preservesColimitIso F D`; the cocone-leg formula is the companion theorem
`ι_preservesColimitIso_inv`. -/
recall preservesColimitIso

/- Source-facing specialization of the filtered-colimit comparison isomorphism. -/
#check (preservesColimitIso F D : F.obj (colimit D) ≅ colimit (D ⋙ F))

recall ι_preservesColimitIso_inv

end FilteredColimit
