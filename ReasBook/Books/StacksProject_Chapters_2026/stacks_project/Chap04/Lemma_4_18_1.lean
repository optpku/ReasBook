module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.CategoryTheory.Limits.FinallySmall
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe vI uI

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I]

/- Domain-style sampling for Lemma 4.18.1:
- primary domain: finite reductions of indexing categories via initial/final functors;
- sampled owner API:
  `InitiallySmall.mk'`,
  `FinallySmall.mk'`,
  `Functor.Initial.hasLimit_comp_iff`,
  `Functor.Final.hasColimit_comp_iff`;
- best owner abstraction: the mathlib owner layer built from `InitiallySmall`,
  `FinallySmall`, `Functor.Initial`, and `Functor.Final`;
- primitive-vs-derived split:
  primitive source data: `[Finite I]` together with `HasFiniteArrowGenerators I`;
  derived API: the source-facing finite reduction theorem and the owner/view consequences given by
    `InitiallySmall`, `FinallySmall`, and the standard limit/colimit comparison theorems;

Source/core/bridge triage:
- `source-facing`: `hasFiniteReduction_of_finite_objects_and_arrow_generators`;
- `core/canonical`: `Functor.Initial`, `Functor.Final`, `InitiallySmall`, and `FinallySmall`;
- `bridge/view`: the two source-hypothesis-to-owner theorems below. -/

/-- A category has finite arrow generators if some finite set of arrows generates every morphism
as a finite composable chain. -/
def HasFiniteArrowGenerators (I : Type uI) [Category.{vI} I] : Prop :=
  ∃ S : Set (Arrow I), S.Finite ∧
    ∀ {X Y : I} (f : X ⟶ Y),
      ∃ n : ℕ, ∃ g : ComposableArrows I (n + 1),
        Arrow.mk g.hom = Arrow.mk f ∧
          ∀ i : Fin (n + 1), Arrow.mk (g.map' i (i + 1)) ∈ S

section

/-- Helper for Lemma 4.18.1: the explicit finite reduction category has two copies of each object
of `I`, called a source copy and a target copy. -/
inductive ReductionObj (S : Set (Arrow I)) : Type (max uI vI) where
  | src : I → ReductionObj S
  | tgt : I → ReductionObj S

/-- Helper for Lemma 4.18.1: a chosen generator arrow from `X` to `Y`. -/
abbrev GeneratorData (S : Set (Arrow I)) (X Y : I) : Type (max uI vI) :=
  { a : Arrow I // a ∈ S ∧ a.left = X ∧ a.right = Y }

/-- Helper for Lemma 4.18.1: the underlying morphism of a chosen generator, rewritten so that its
source is exactly `X` and its target is exactly `Y`. -/
def GeneratorData.hom {S : Set (Arrow I)} {X Y : I} (a : GeneratorData S X Y) : X ⟶ Y :=
  eqToHom a.2.2.1.symm ≫ a.1.hom ≫ eqToHom a.2.2.2

/-- Helper for Lemma 4.18.1: morphisms in the explicit bipartite reduction category.

Besides identities, the only nonidentity arrows go from a source copy to a target copy, either
coming from a chosen generator or from the diagonal identity-copy arrow. -/
inductive ReductionHom (S : Set (Arrow I)) : ReductionObj S → ReductionObj S → Type (max uI vI) where
  | id_src (X : I) : ReductionHom S (.src X) (.src X)
  | id_tgt (X : I) : ReductionHom S (.tgt X) (.tgt X)
  | gen {X Y : I} (a : GeneratorData S X Y) : ReductionHom S (.src X) (.tgt Y)
  | diag (X : I) : ReductionHom S (.src X) (.tgt X)

/-- Helper for Lemma 4.18.1: the identity morphisms in the explicit reduction category. -/
def reductionId (S : Set (Arrow I)) : ∀ A : ReductionObj S, ReductionHom S A A
  | .src X => .id_src X
  | .tgt X => .id_tgt X

/-- Helper for Lemma 4.18.1: composition in the explicit reduction category is forced because
the only nonidentity composable pairs involve an identity. -/
def reductionComp (S : Set (Arrow I)) :
    ∀ {A B C : ReductionObj S}, ReductionHom S A B → ReductionHom S B C → ReductionHom S A C
  | _, _, _, .id_src _, g => g
  | _, _, _, .id_tgt _, g => g
  | _, _, _, .gen a, .id_tgt _ => .gen a
  | _, _, _, .diag X, .id_tgt _ => .diag X

/-- Helper for Lemma 4.18.1: the explicit bipartite reduction category attached to `S`. -/
instance reductionCategory (S : Set (Arrow I)) : SmallCategory (ReductionObj S) where
  Hom := ReductionHom S
  id := reductionId S
  comp := reductionComp S
  -- The category laws reduce to the four constructors of `ReductionHom`.
  id_comp := by
    intro A B f
    cases f <;> rfl
  -- Right identities are equally forced by the same constructor analysis.
  comp_id := by
    intro A B f
    cases f <;> rfl
  -- Associativity is trivial because every nonidentity composite is absorbed by an identity.
  assoc := by
    intro A B C D f g h
    cases f <;> cases g <;> cases h <;> rfl

/-- Helper for Lemma 4.18.1: on objects, the reduction functor forgets whether we are in the
source copy or the target copy. -/
def reductionFunctorObj (S : Set (Arrow I)) : ReductionObj S → I
  | .src X => X
  | .tgt X => X

/-- Helper for Lemma 4.18.1: on morphisms, the reduction functor sends identities to identities,
generator arrows to their chosen morphisms, and diagonal arrows to identities. -/
def reductionFunctorMap (S : Set (Arrow I)) {X Y : ReductionObj S} :
    ReductionHom S X Y →
      ((reductionFunctorObj (I := I) S X) ⟶ (reductionFunctorObj (I := I) S Y))
  | ReductionHom.id_src X => 𝟙 X
  | ReductionHom.id_tgt X => 𝟙 X
  | ReductionHom.gen a => a.hom
  | ReductionHom.diag X => 𝟙 X

/-- Helper for Lemma 4.18.1: the explicit object/morphism formulas for the reduction functor are
compatible with the explicit composition law on the reduction category. -/
lemma reductionFunctorMap_comp (S : Set (Arrow I)) {X Y Z : ReductionObj S}
    (f : ReductionHom S X Y) (g : ReductionHom S Y Z) :
    reductionFunctorMap (I := I) S (reductionComp S f g) =
      reductionFunctorMap (I := I) S f ≫ reductionFunctorMap (I := I) S g := by
  -- The reduction category has only identity composites, so constructor analysis closes the goal.
  cases f with
  | id_src X =>
      cases g with
      | id_src Y =>
          dsimp [reductionComp, reductionFunctorMap]
          symm
          exact Category.id_comp (𝟙 X : X ⟶ X)
      | gen a =>
          dsimp [reductionComp, reductionFunctorMap]
          symm
          exact Category.id_comp a.hom
      | diag Y =>
          dsimp [reductionComp, reductionFunctorMap]
          symm
          exact Category.id_comp (𝟙 X : X ⟶ X)
  | id_tgt X =>
      cases g with
      | id_tgt Y =>
          dsimp [reductionComp, reductionFunctorMap]
          symm
          exact Category.id_comp (𝟙 X : X ⟶ X)
  | gen a =>
      cases g with
      | id_tgt Y =>
          dsimp [reductionComp, reductionFunctorMap]
          symm
          exact Category.comp_id a.hom
  | diag X =>
      cases g with
      | id_tgt Y =>
          dsimp [reductionComp, reductionFunctorMap]
          symm
          exact Category.id_comp (𝟙 X : X ⟶ X)

/-- Helper for Lemma 4.18.1: the reduction functor from the explicit finite bipartite category to
`I`. -/
def reductionFunctor (S : Set (Arrow I)) : ReductionObj S ⥤ I where
  obj := reductionFunctorObj (I := I) S
  map := reductionFunctorMap (I := I) S
  map_id := by
    intro X
    cases X <;> rfl
  map_comp := by
    intro X Y Z f g
    simpa using reductionFunctorMap_comp (I := I) S f g

/-- Helper for Lemma 4.18.1: the chosen generator subtype is finite because `S` is finite. -/
@[reducible] noncomputable def generatorDataFintype (S : Set (Arrow I)) (hS : S.Finite)
    (X Y : I) :
    Fintype (GeneratorData S X Y) := by
  classical
  let S' : Type (max uI vI) := { a : Arrow I // a ∈ S }
  letI : Fintype S' := hS.fintype
  letI : Fintype { a : S' // a.1.left = X ∧ a.1.right = Y } := Subtype.fintype _
  refine Fintype.ofEquiv { a : S' // a.1.left = X ∧ a.1.right = Y } ?_
  refine
    { toFun := fun a => ⟨a.1.1, a.1.2, a.2.1, a.2.2⟩
      invFun := fun a => ⟨⟨a.1, a.2.1⟩, a.2.2.1, a.2.2.2⟩
      left_inv := by
        intro a
        cases a
        rfl
      right_inv := by
        intro a
        cases a
        rfl }

/-- Helper for Lemma 4.18.1: a one-point type in the reduction-category universe. -/
abbrev ReductionOne : Type (max uI vI) := ULift.{max uI vI, 0} PUnit

/-- Helper for Lemma 4.18.1: an empty type in the reduction-category universe. -/
abbrev ReductionZero : Type (max uI vI) := ULift.{max uI vI, 0} PEmpty

section

variable [Finite I]

/-- Helper for Lemma 4.18.1: the object type of the explicit reduction category is finite. -/
@[reducible] noncomputable def reductionObjFintype (S : Set (Arrow I)) :
    Fintype (ReductionObj S) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  refine Fintype.ofEquiv (Sum I I) ?_
  refine
    { toFun := fun
        | Sum.inl X => .src X
        | Sum.inr X => .tgt X
      invFun := fun
        | .src X => Sum.inl X
        | .tgt X => Sum.inr X
      left_inv := by
        intro X
        cases X <;> rfl
      right_inv := by
        intro X
        cases X <;> rfl }

/-- Helper for Lemma 4.18.1: each hom-space in the reduction category is finite. -/
@[reducible] noncomputable def reductionHomFintype (S : Set (Arrow I)) (hS : S.Finite) :
    ∀ A B : ReductionObj S, Fintype (ReductionHom S A B) :=
  by
    classical
    intro A B
    cases A with
    | src X =>
      cases B with
      | src Y =>
        -- Only the identity source-copy arrow can occur between two source copies.
        by_cases h : X = Y
        · subst h
          letI : Subsingleton (ReductionHom S (.src X) (.src X)) := by
            refine ⟨?_⟩
            intro f g
            cases f with
            | id_src _ =>
                cases g with
                | id_src _ => rfl
          exact Fintype.ofSubsingleton (ReductionHom.id_src (S := S) X)
        · letI : IsEmpty (ReductionHom S (.src X) (.src Y)) := ⟨fun f => by
            cases f
            exact h rfl⟩
          exact Fintype.ofIsEmpty
      | tgt Y =>
        -- A source-to-target hom is either a chosen generator or, when `X = Y`, the diagonal.
        by_cases h : X = Y
        · subst h
          letI : Fintype (GeneratorData S X X) := generatorDataFintype (I := I) S hS X X
          refine Fintype.ofEquiv (Option (GeneratorData S X X)) ?_
          refine
            { toFun := fun
                | some d => ReductionHom.gen d
                | none => ReductionHom.diag (S := S) X
              invFun := fun
                | .gen d => some d
                | .diag _ => none
              left_inv := by
                intro o
                cases o <;> rfl
              right_inv := by
                intro f
                cases f <;> rfl }
        · letI : Fintype (GeneratorData S X Y) := generatorDataFintype (I := I) S hS X Y
          refine Fintype.ofEquiv (GeneratorData S X Y) ?_
          refine
            { toFun := fun d => ReductionHom.gen d
              invFun := fun
                | .gen d => d
                | .diag Z => (h rfl).elim
              left_inv := by
                intro d
                rfl
              right_inv := by
                intro f
                cases f with
                | gen d => rfl
                | diag Z => exact (h rfl).elim }
    | tgt X =>
      cases B with
      | src Y =>
        -- There are no arrows from a target copy to a source copy.
        letI : IsEmpty (ReductionHom S (.tgt X) (.src Y)) := ⟨fun f => by cases f⟩
        exact Fintype.ofIsEmpty
      | tgt Y =>
        -- Only the identity target-copy arrow can occur between two target copies.
        by_cases h : X = Y
        · subst h
          letI : Subsingleton (ReductionHom S (.tgt X) (.tgt X)) := by
            refine ⟨?_⟩
            intro f g
            cases f with
            | id_tgt _ =>
                cases g with
                | id_tgt _ => rfl
          exact Fintype.ofSubsingleton (ReductionHom.id_tgt (S := S) X)
        · letI : IsEmpty (ReductionHom S (.tgt X) (.tgt Y)) := ⟨fun f => by
              cases f
              exact h rfl⟩
          exact Fintype.ofIsEmpty

/-- Helper for Lemma 4.18.1: the explicit reduction category is finite when `S` is finite. -/
@[reducible] noncomputable def reductionFinCategory (S : Set (Arrow I)) (hS : S.Finite) :
    FinCategory (ReductionObj S) where
  fintypeObj := reductionObjFintype (I := I) S
  fintypeHom := reductionHomFintype (I := I) S hS

end

/-- Helper for Lemma 4.18.1: the image of a generator arrow under the reduction functor is the
underlying morphism of that generator. -/
@[simp] lemma reductionFunctor_map_gen (S : Set (Arrow I)) {X Y : I} (a : GeneratorData S X Y) :
    reductionFunctorMap (I := I) S (.gen a) = a.hom := rfl

/-- Helper for Lemma 4.18.1: the image of a diagonal arrow under the reduction functor is the
identity. -/
@[simp] lemma reductionFunctor_map_diag (S : Set (Arrow I)) (X : I) :
    reductionFunctorMap (I := I) S (.diag X) = 𝟙 X := rfl

/-- Helper for Lemma 4.18.1: an equality in the arrow category identifies the source, target, and
underlying morphism after transport. -/
lemma arrow_hom_eq_of_mk_eq_mk {X Y : I} {f : X ⟶ Y} {n : ℕ} (g : ComposableArrows I (n + 1))
    (h : Arrow.mk g.hom = Arrow.mk f) :
    ∃ (hleft : g.left = X) (hright : g.right = Y),
      g.hom = eqToHom hleft ≫ f ≫ eqToHom hright.symm := by
  simpa [ComposableArrows.left, ComposableArrows.right] using (Arrow.mk_eq_mk_iff g.hom f).1 h

/-- Helper for Lemma 4.18.1: an edge of a generator chain determines the corresponding generator
datum in the reduction category. -/
def generatorData_of_chain_edge (S : Set (Arrow I)) {n : ℕ} (g : ComposableArrows I (n + 1))
    (i : Fin (n + 1)) (hmem : Arrow.mk (g.map' i (i + 1)) ∈ S) :
    GeneratorData S (g.obj' i) (g.obj' (i + 1)) :=
  ⟨Arrow.mk (g.map' i (i + 1)), hmem, rfl, rfl⟩

/-- Helper for Lemma 4.18.1: the morphism underlying the generator datum extracted from a chain
edge is exactly that edge. -/
@[simp] lemma generatorData_of_chain_edge_hom (S : Set (Arrow I)) {n : ℕ}
    (g : ComposableArrows I (n + 1)) (i : Fin (n + 1))
    (hmem : Arrow.mk (g.map' i (i + 1)) ∈ S) :
    (generatorData_of_chain_edge (I := I) S g i hmem).hom = g.map' i (i + 1) := by
  simp [generatorData_of_chain_edge, GeneratorData.hom]

/-- Helper for Lemma 4.18.1: cancel endpoint transports around an aligned chain composite. -/
lemma transported_hom_eq {X X' Y Y' : I} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hleft : X' = X) (hright : Y' = Y)
    (h : g = eqToHom hleft ≫ f ≫ eqToHom hright.symm) :
    eqToHom hleft.symm ≫ g ≫ eqToHom hright = f := by
  -- After identifying the endpoints, both transport factors become identities.
  subst hleft
  subst hright
  simpa using h

/-- Helper for Lemma 4.18.1: a nontrivial composable chain splits into its first edge followed by
the tail chain. -/
lemma composableArrows_hom_eq_first_edge_comp_tail {n : ℕ} (g : ComposableArrows I (n + 2)) :
    g.hom = g.map' 0 1 ≫ g.δ₀.hom := by
  -- This is `map'_comp` specialized to the first, middle, and last vertices.
  simpa [ComposableArrows.hom, ComposableArrows.δ₀] using
    (ComposableArrows.map'_comp g 0 1 (n + 2))

/-- Helper for Lemma 4.18.1: the diagonal arrow gives the one-step copy switch from a target copy
back to the corresponding source copy in the structured-arrow comma category. -/
lemma structuredArrow_zigzag_diag_switch (S : Set (Arrow I)) {X Y : I} (k : X ⟶ Y) :
    Zigzag
      (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) Y) k)
      (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) Y) k)
    := by
  -- The diagonal arrow is sent to an identity, so it only switches which copy of `Y` we use.
  refine Zigzag.of_inv ?_
  refine StructuredArrow.homMk (.diag (S := S) Y) ?_
  simp [reductionFunctor, reductionFunctorMap, reductionFunctorObj, Category.comp_id]

/-- Helper for Lemma 4.18.1: the diagonal arrow gives the one-step copy switch from a target copy
back to the corresponding source copy in the costructured-arrow comma category. -/
lemma costructuredArrow_zigzag_diag_switch (S : Set (Arrow I)) {X Y : I} (k : Y ⟶ X) :
    Zigzag
      (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) Y)
        k)
      (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) Y)
        k) := by
  -- Dually, the same diagonal arrow only changes which copy of `Y` the costructured arrow starts
  -- from.
  refine Zigzag.of_inv ?_
  refine CostructuredArrow.homMk (.diag (S := S) Y) ?_
  simp [reductionFunctor, reductionFunctorMap, reductionFunctorObj, Category.id_comp]

/-- Helper for Lemma 4.18.1: a generator chain gives the alternating zigzag from the source-copy
base object to the target-copy endpoint in the relevant structured-arrow category. -/
lemma structuredArrow_zigzag_of_generator_chain (S : Set (Arrow I)) :
    ∀ {X : I} {n : ℕ} (g : ComposableArrows I (n + 1)) (u : X ⟶ g.left),
      (∀ i : Fin (n + 1), Arrow.mk (g.map' i (i + 1)) ∈ S) →
      Zigzag
        (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := .src g.left) u)
        (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := .tgt g.right)
          (u ≫ g.hom : X ⟶ reductionFunctorObj (I := I) S (.tgt g.right)))
    := by
  intro X n
  induction n generalizing X with
  | zero =>
      intro g u hmem
      -- A one-edge chain is exactly one generator morphism in the structured-arrow category.
      refine Zigzag.of_hom ?_
      refine StructuredArrow.homMk
        (.gen (generatorData_of_chain_edge (I := I) S g 0 (hmem 0))) ?_
      simpa [ComposableArrows.hom] using congrArg (fun k ↦ u ≫ k)
        (generatorData_of_chain_edge_hom (I := I) S g 0 (hmem 0))
  | succ n ih =>
      intro g u hmem
      -- Route correction: cross the first generator edge, switch copies with `diag`, then recurse.
      have hfirst :
          Zigzag
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := .src g.left) u)
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := .tgt (g.obj' 1))
              (u ≫ g.map' 0 1 :
                X ⟶ reductionFunctorObj (I := I) S (.tgt (g.obj' 1)))) := by
        refine Zigzag.of_hom ?_
        refine StructuredArrow.homMk
          (.gen (generatorData_of_chain_edge (I := I) S g 0 (hmem 0))) ?_
        simpa using congrArg (fun k ↦ u ≫ k)
          (generatorData_of_chain_edge_hom (I := I) S g 0 (hmem 0))
      have hdiag :
          Zigzag
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := .tgt (g.obj' 1))
              (u ≫ g.map' 0 1 :
                X ⟶ reductionFunctorObj (I := I) S (.tgt (g.obj' 1))))
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := .src (g.obj' 1))
              (u ≫ g.map' 0 1 :
                X ⟶ reductionFunctorObj (I := I) S (.src (g.obj' 1)))) :=
        structuredArrow_zigzag_diag_switch (I := I) S (u ≫ g.map' 0 1)
      have htail :
          Zigzag
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := .src g.δ₀.left)
              (u ≫ g.map' 0 1 :
                X ⟶ reductionFunctorObj (I := I) S (.src g.δ₀.left)))
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := .tgt g.δ₀.right)
              ((u ≫ g.map' 0 1) ≫ g.δ₀.hom :
                X ⟶ reductionFunctorObj (I := I) S (.tgt g.δ₀.right))) := by
        refine ih g.δ₀ (u ≫ g.map' 0 1) ?_
        intro i
        simpa [ComposableArrows.δ₀] using hmem i.succ
      -- The tail composite is the canonical decomposition of `g.hom`.
      simpa [ComposableArrows.δ₀, Category.assoc, Category.comp_id,
        composableArrows_hom_eq_first_edge_comp_tail (g := g)] using
        (hfirst.trans hdiag).trans htail

/-- Helper for Lemma 4.18.1: a generator chain gives the alternating zigzag from the source-copy
representation of the whole composite to the target-copy identity object in the costructured-arrow
category. -/
lemma costructuredArrow_zigzag_of_generator_chain (S : Set (Arrow I)) :
    ∀ {X : I} {n : ℕ} (g : ComposableArrows I (n + 1)) (v : g.right ⟶ X),
      (∀ i : Fin (n + 1), Arrow.mk (g.map' i (i + 1)) ∈ S) →
      Zigzag
        (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := .src g.left)
          (g.hom ≫ v : reductionFunctorObj (I := I) S (.src g.left) ⟶ X))
        (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := .tgt g.right)
          (v : reductionFunctorObj (I := I) S (.tgt g.right) ⟶ X))
    := by
  intro X n
  induction n generalizing X with
  | zero =>
      intro g v hmem
      -- A one-edge chain gives the desired costructured-arrow morphism in one step.
      refine Zigzag.of_hom ?_
      refine CostructuredArrow.homMk
        (.gen (generatorData_of_chain_edge (I := I) S g 0 (hmem 0))) ?_
      change
        reductionFunctorMap (I := I) S (.gen (generatorData_of_chain_edge (I := I) S g 0 (hmem 0)))
          ≫ v = g.hom ≫ v
      rw [reductionFunctor_map_gen, generatorData_of_chain_edge_hom, ComposableArrows.hom]
      simp
      rfl
  | succ n ih =>
      intro g v hmem
      -- Route correction: expose the tail object first, then recurse on `g.δ₀`.
      have hfirst :
          Zigzag
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := .src g.left)
              (g.hom ≫ v :
                reductionFunctorObj (I := I) S (.src g.left) ⟶ X))
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := .tgt (g.obj' 1))
              (g.δ₀.hom ≫ v :
                reductionFunctorObj (I := I) S (.tgt (g.obj' 1)) ⟶ X)) := by
        refine Zigzag.of_hom ?_
        refine CostructuredArrow.homMk
          (.gen (generatorData_of_chain_edge (I := I) S g 0 (hmem 0))) ?_
        change
          (generatorData_of_chain_edge (I := I) S g 0 (hmem 0)).hom ≫ g.δ₀.hom ≫ v = g.hom ≫ v
        rw [generatorData_of_chain_edge_hom, composableArrows_hom_eq_first_edge_comp_tail]
        -- Normalize the first edge index, then the goal is exactly associativity.
        change g.map' 0 1 ≫ g.δ₀.hom ≫ v = (g.map' 0 1 ≫ g.δ₀.hom) ≫ v
        exact (Category.assoc (g.map' 0 1) g.δ₀.hom v).symm
      have hdiag :
          Zigzag
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := .tgt (g.obj' 1))
              (g.δ₀.hom ≫ v :
                reductionFunctorObj (I := I) S (.tgt (g.obj' 1)) ⟶ X))
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := .src (g.obj' 1))
              (g.δ₀.hom ≫ v :
                reductionFunctorObj (I := I) S (.src (g.obj' 1)) ⟶ X)) :=
        costructuredArrow_zigzag_diag_switch (I := I) S (g.δ₀.hom ≫ v)
      have htail :
          Zigzag
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := .src g.δ₀.left)
              (g.δ₀.hom ≫ v :
                reductionFunctorObj (I := I) S (.src g.δ₀.left) ⟶ X))
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := .tgt g.δ₀.right)
              (v :
                reductionFunctorObj (I := I) S (.tgt g.δ₀.right) ⟶ X)) := by
        refine ih g.δ₀ v ?_
        intro i
        simpa [ComposableArrows.δ₀] using hmem i.succ
      simpa [ComposableArrows.δ₀, Category.assoc, Category.id_comp] using
        (hfirst.trans hdiag).trans htail

/-- Helper for Lemma 4.18.1: move endpoint transports for the structured-arrow chain zigzag out
of the recursive proof and discharge them once at the end. -/
lemma structuredArrow_zigzag_of_generator_chain_transport (S : Set (Arrow I)) {X Y : I} {n : ℕ}
    (g : ComposableArrows I (n + 1)) (hleft : g.left = X) (hright : g.right = Y)
    (hmem : ∀ i : Fin (n + 1), Arrow.mk (g.map' i (i + 1)) ∈ S) :
    Zigzag
      (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) X)
        (𝟙 X : X ⟶ reductionFunctorObj (I := I) S (.src X)))
      (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) Y)
        (eqToHom hleft.symm ≫ g.hom ≫ eqToHom hright :
          X ⟶ reductionFunctorObj (I := I) S (.tgt Y))) := by
  -- Rewrite the endpoint objects once, then use the fixed-endpoint structured-arrow zigzag.
  cases hleft
  cases hright
  simpa [reductionFunctorObj, eqToHom_refl, Category.id_comp, Category.comp_id] using
    structuredArrow_zigzag_of_generator_chain (I := I) S g (𝟙 g.left) hmem

/-- Helper for Lemma 4.18.1: dually move endpoint transports for the costructured-arrow chain
zigzag out of the recursive proof. -/
lemma costructuredArrow_zigzag_of_generator_chain_transport (S : Set (Arrow I)) {X Y : I}
    {n : ℕ} (g : ComposableArrows I (n + 1)) (hleft : g.left = X) (hright : g.right = Y)
    (hmem : ∀ i : Fin (n + 1), Arrow.mk (g.map' i (i + 1)) ∈ S) :
    Zigzag
      (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) X)
        (eqToHom hleft.symm ≫ g.hom ≫ eqToHom hright :
          reductionFunctorObj (I := I) S (.src X) ⟶ Y))
      (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) Y)
        (𝟙 Y : reductionFunctorObj (I := I) S (.tgt Y) ⟶ Y)) := by
  -- Rewrite the endpoint objects once, then use the fixed-endpoint costructured-arrow zigzag.
  cases hleft
  cases hright
  simpa [reductionFunctorObj, eqToHom_refl, Category.id_comp, Category.comp_id] using
    costructuredArrow_zigzag_of_generator_chain (I := I) S g (𝟙 g.right) hmem

/-- Helper for Lemma 4.18.1: every object of the structured-arrow comma category contracts to the
identity source-copy basepoint. -/
lemma structuredArrow_zigzag_to_identity_copy (S : Set (Arrow I))
    (hsplit :
      ∀ {X Y : I} (f : X ⟶ Y),
        ∃ n : ℕ, ∃ g : ComposableArrows I (n + 1),
          Arrow.mk g.hom = Arrow.mk f ∧
            ∀ i : Fin (n + 1), Arrow.mk (g.map' i (i + 1)) ∈ S)
    {X : I} (A : StructuredArrow X (reductionFunctor (I := I) S)) :
    Zigzag A (StructuredArrow.mk (T := reductionFunctor (I := I) S)
      (Y := ReductionObj.src (S := S) X)
      (𝟙 X : X ⟶ reductionFunctorObj (I := I) S (.src X))) := by
  -- Rewrite the comma object into one of the explicit source/target copies.
  rcases StructuredArrow.mk_surjective A with ⟨Y, f, rfl⟩
  cases Y with
  | src Y =>
      -- A source-copy object crosses the diagonal identity arrow before contracting the chain.
      rcases hsplit f with ⟨n, g, hg, hmem⟩
      rcases arrow_hom_eq_of_mk_eq_mk g hg with ⟨hleft, hright, hcomp⟩
      have htransport :
          Zigzag
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) X)
              (𝟙 X : X ⟶ reductionFunctorObj (I := I) S (.src X)))
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) Y)
              (eqToHom hleft.symm ≫ g.hom ≫ eqToHom hright :
                X ⟶ reductionFunctorObj (I := I) S (.tgt Y))) :=
        structuredArrow_zigzag_of_generator_chain_transport (I := I) S g hleft hright hmem
      have hf :
          eqToHom hleft.symm ≫ g.hom ≫ eqToHom hright = f :=
        transported_hom_eq hleft hright hcomp
      have htarget :
          Zigzag
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) X)
              (𝟙 X : X ⟶ reductionFunctorObj (I := I) S (.src X)))
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) Y)
              (f : X ⟶ reductionFunctorObj (I := I) S (.tgt Y))) := by
        revert hf htransport
        cases hleft
        cases hright
        intro htransport hf
        simpa [reductionFunctorObj, eqToHom_refl, Category.id_comp, Category.comp_id] using
          (hf ▸ htransport)
      have hdiag :
          Zigzag
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) Y)
              (f : X ⟶ reductionFunctorObj (I := I) S (.src Y)))
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) Y)
              (f : X ⟶ reductionFunctorObj (I := I) S (.tgt Y))) :=
        (structuredArrow_zigzag_diag_switch (I := I) S f).symm
      exact hdiag.trans htarget.symm
  | tgt Y =>
      -- A target-copy object is already the endpoint of the chain contraction.
      rcases hsplit f with ⟨n, g, hg, hmem⟩
      rcases arrow_hom_eq_of_mk_eq_mk g hg with ⟨hleft, hright, hcomp⟩
      have htransport :
          Zigzag
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) X)
              (𝟙 X : X ⟶ reductionFunctorObj (I := I) S (.src X)))
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) Y)
              (eqToHom hleft.symm ≫ g.hom ≫ eqToHom hright :
                X ⟶ reductionFunctorObj (I := I) S (.tgt Y))) :=
        structuredArrow_zigzag_of_generator_chain_transport (I := I) S g hleft hright hmem
      have hf :
          eqToHom hleft.symm ≫ g.hom ≫ eqToHom hright = f :=
        transported_hom_eq hleft hright hcomp
      have htarget :
          Zigzag
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) X)
              (𝟙 X : X ⟶ reductionFunctorObj (I := I) S (.src X)))
            (StructuredArrow.mk (T := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) Y)
              (f : X ⟶ reductionFunctorObj (I := I) S (.tgt Y))) := by
        revert hf htransport
        cases hleft
        cases hright
        intro htransport hf
        simpa [reductionFunctorObj, eqToHom_refl, Category.id_comp, Category.comp_id] using
          (hf ▸ htransport)
      exact htarget.symm

/-- Helper for Lemma 4.18.1: every object of the costructured-arrow comma category contracts to
the identity target-copy basepoint. -/
lemma costructuredArrow_zigzag_to_identity_copy (S : Set (Arrow I))
    (hsplit :
      ∀ {X Y : I} (f : X ⟶ Y),
        ∃ n : ℕ, ∃ g : ComposableArrows I (n + 1),
          Arrow.mk g.hom = Arrow.mk f ∧
            ∀ i : Fin (n + 1), Arrow.mk (g.map' i (i + 1)) ∈ S)
    {X : I} (A : CostructuredArrow (reductionFunctor (I := I) S) X) :
    Zigzag A (CostructuredArrow.mk (S := reductionFunctor (I := I) S)
      (Y := ReductionObj.tgt (S := S) X)
      (𝟙 X : reductionFunctorObj (I := I) S (.tgt X) ⟶ X)) := by
  -- Rewrite the comma object into one of the explicit source/target copies.
  rcases CostructuredArrow.mk_surjective A with ⟨Y, f, rfl⟩
  cases Y with
  | src Y =>
      -- A source-copy object is the starting point of the chain contraction.
      rcases hsplit f with ⟨n, g, hg, hmem⟩
      rcases arrow_hom_eq_of_mk_eq_mk g hg with ⟨hleft, hright, hcomp⟩
      have htransport :
          Zigzag
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) Y)
              (eqToHom hleft.symm ≫ g.hom ≫ eqToHom hright :
                reductionFunctorObj (I := I) S (.src Y) ⟶ X))
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) X)
              (𝟙 X : reductionFunctorObj (I := I) S (.tgt X) ⟶ X)) :=
        costructuredArrow_zigzag_of_generator_chain_transport (I := I) S g hleft hright hmem
      have hf :
          eqToHom hleft.symm ≫ g.hom ≫ eqToHom hright = f :=
        transported_hom_eq hleft hright hcomp
      revert hf htransport
      cases hleft
      cases hright
      intro htransport hf
      simpa [reductionFunctorObj, eqToHom_refl, Category.id_comp, Category.comp_id] using
        (hf ▸ htransport)
  | tgt Y =>
      -- A target-copy object first moves back across the diagonal identity arrow.
      rcases hsplit f with ⟨n, g, hg, hmem⟩
      rcases arrow_hom_eq_of_mk_eq_mk g hg with ⟨hleft, hright, hcomp⟩
      have hdiag :
          Zigzag
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) Y)
              (f : reductionFunctorObj (I := I) S (.tgt Y) ⟶ X))
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) Y)
              (f : reductionFunctorObj (I := I) S (.src Y) ⟶ X)) :=
        costructuredArrow_zigzag_diag_switch (I := I) S f
      have htransport :
          Zigzag
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) Y)
              (eqToHom hleft.symm ≫ g.hom ≫ eqToHom hright :
                reductionFunctorObj (I := I) S (.src Y) ⟶ X))
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) X)
              (𝟙 X : reductionFunctorObj (I := I) S (.tgt X) ⟶ X)) :=
        costructuredArrow_zigzag_of_generator_chain_transport (I := I) S g hleft hright hmem
      have hf :
          eqToHom hleft.symm ≫ g.hom ≫ eqToHom hright = f :=
        transported_hom_eq hleft hright hcomp
      have hsource :
          Zigzag
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.src (S := S) Y)
              (f : reductionFunctorObj (I := I) S (.src Y) ⟶ X))
            (CostructuredArrow.mk (S := reductionFunctor (I := I) S) (Y := ReductionObj.tgt (S := S) X)
              (𝟙 X : reductionFunctorObj (I := I) S (.tgt X) ⟶ X)) := by
        revert hf htransport
        cases hleft
        cases hright
        intro htransport hf
        simpa [reductionFunctorObj, eqToHom_refl, Category.id_comp, Category.comp_id] using
          (hf ▸ htransport)
      exact hdiag.trans hsource

/-- Helper for Lemma 4.18.1: the explicit reduction functor is both initial and final once the
chosen arrows generate every morphism of `I`. -/
lemma reductionFunctor_initial_final (S : Set (Arrow I))
    (hsplit :
      ∀ {X Y : I} (f : X ⟶ Y),
        ∃ n : ℕ, ∃ g : ComposableArrows I (n + 1),
          Arrow.mk g.hom = Arrow.mk f ∧
            ∀ i : Fin (n + 1), Arrow.mk (g.map' i (i + 1)) ∈ S) :
    (reductionFunctor (I := I) S).Initial ∧ (reductionFunctor (I := I) S).Final := by
  constructor
  · -- Every costructured-arrow object contracts to the target-copy identity object.
    refine { out := fun X => ?_ }
    letI : Nonempty (CostructuredArrow (reductionFunctor (I := I) S) X) :=
      ⟨CostructuredArrow.mk (S := reductionFunctor (I := I) S)
        (Y := ReductionObj.tgt (S := S) X) (𝟙 X)⟩
    apply zigzag_isConnected
    intro A B
    exact (costructuredArrow_zigzag_to_identity_copy (I := I) S hsplit A).trans
      (costructuredArrow_zigzag_to_identity_copy (I := I) S hsplit B).symm
  · -- Dually, every structured-arrow object contracts to the source-copy identity object.
    refine { out := fun X => ?_ }
    letI : Nonempty (StructuredArrow X (reductionFunctor (I := I) S)) :=
      ⟨StructuredArrow.mk (T := reductionFunctor (I := I) S)
        (Y := ReductionObj.src (S := S) X) (𝟙 X)⟩
    apply zigzag_isConnected
    intro A B
    exact (structuredArrow_zigzag_to_identity_copy (I := I) S hsplit A).trans
      (structuredArrow_zigzag_to_identity_copy (I := I) S hsplit B).symm

variable [Finite I]

/-- Lemma 4.18.1: assume `I` has finitely many objects and there is a finite set of chosen
morphisms such that every morphism of `I` is a finite composition of chosen morphisms. Then there
is a finite category `J` and a functor `F : J ⥤ I` which is both initial and final. -/
theorem hasFiniteReduction_of_finite_objects_and_arrow_generators
    (hgen : HasFiniteArrowGenerators I) :
    ∃ (J : Type (max uI vI)) (_ : SmallCategory J) (_ : FinCategory J) (F : J ⥤ I),
      F.Initial ∧ F.Final := by
  rcases hgen with ⟨S, hS, hsplit⟩
  -- The textbook reduction category is the bipartite category attached to the finite generator set.
  refine ⟨ReductionObj S, reductionCategory (I := I) S, reductionFinCategory (I := I) S hS,
    reductionFunctor (I := I) S, ?_⟩
  -- The comma-category zigzags proved above package the reduction functor as both initial and final.
  exact reductionFunctor_initial_final S hsplit

end

/- Lemma 4.18.1, limit comparison isomorphism: once the finite reduction functor is initial, the
canonical owner theorem is `Functor.Initial.limitIso`. -/
recall Functor.Initial.limitIso

/- Lemma 4.18.1, limit existence transfer: once the finite reduction functor is initial, the
canonical owner theorem is `Functor.Initial.hasLimit_comp_iff`. -/
recall Functor.Initial.hasLimit_comp_iff

/- Lemma 4.18.1, colimit comparison isomorphism: once the finite reduction functor is final, the
canonical owner theorem is `Functor.Final.colimitIso`. -/
recall Functor.Final.colimitIso

/- Lemma 4.18.1, colimit existence transfer: once the finite reduction functor is final, the
canonical owner theorem is `Functor.Final.hasColimit_comp_iff`. -/
recall Functor.Final.hasColimit_comp_iff

/- Lemma 4.18.1, connectedness comparison: for an initial functor, the canonical owner theorem is
`Functor.isConnected_iff_of_initial`. -/
recall Functor.isConnected_iff_of_initial

/- Lemma 4.18.1, connectedness comparison: for a final functor, the canonical owner theorem is
`Functor.isConnected_iff_of_final`. -/
recall Functor.isConnected_iff_of_final

section

variable [Finite I]

/-- Bridge to the canonical owner abstraction `CategoryTheory.InitiallySmall`: under the finite
generation hypothesis of Lemma 4.18.1, the category `I` admits an initial functor from a finite
small category. -/
theorem initiallySmall_of_finite_objects_and_arrow_generators
    (hgen : HasFiniteArrowGenerators I) :
    InitiallySmall.{max uI vI} I := by
  rcases hasFiniteReduction_of_finite_objects_and_arrow_generators hgen with
    ⟨J, _, _, F, hF, _⟩
  letI : F.Initial := hF
  exact InitiallySmall.mk' F

/-- Bridge to the canonical owner abstraction `CategoryTheory.FinallySmall`: under the finite
generation hypothesis of Lemma 4.18.1, the category `I` admits a final functor from a finite
small category. -/
theorem finallySmall_of_finite_objects_and_arrow_generators
    (hgen : HasFiniteArrowGenerators I) :
    FinallySmall.{max uI vI} I := by
  rcases hasFiniteReduction_of_finite_objects_and_arrow_generators hgen with
    ⟨J, _, _, F, _, hF⟩
  letI : F.Final := hF
  exact FinallySmall.mk' F

end

end CategoryTheory
