module

public import stacks_project.Chap04.Remark_4_22_7
import Mathlib.CategoryTheory.Limits.Types.Filtered

@[expose] public section

open CategoryTheory Limits Opposite
open scoped CategoryTheory

universe u v

namespace CategoryTheory

/- Domain-style sampling for Example 4.22.6:
- primary domain: sequential inverse systems as source-facing models for morphisms in the
  pro-category of `C`.
- inspected owner-level declarations:
  `OrderHom.toFunctor`,
  `proObjectHomEquivLimitProSystemHomColimitFunctor`,
  `Types.sectionsEquiv`,
  `Types.limitEquivSections`,
  `Limits.colimitObjIsoColimitCompEvaluation`.
- best owner abstraction:
  `limit (Y ⋙ proSystemHomColimitFunctor X)`.

Primitive-vs-derived split:
  `reindex.toFunctor.op ⋙ X ⟶ Y`.
- derived API: the level maps `X_{reindex(n)} ⟶ Y_n` and their compatibility squares.

Source/core/bridge triage:
- `source-facing`: `SequentialProObjectMorphismRep X Y`, consisting canonically of a reindexing
  order hom and the induced natural transformation of sequential inverse systems.
- `core/canonical`: the pro-object morphism type
  `(colimit (Y.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor X ⋙ uliftFunctor.{0})`
  between the associated sequential pro-objects, together with its plain-limit owner
  `limit (Y ⋙ proSystemHomColimitFunctor X)`.
- `bridge/view`: the inverse-limit point `SequentialProObjectMorphismRep.toLimitHom`, built from
  the stagewise Hom-colimit classes via the canonical `Types.Limit.mk` constructor. -/

/-- A representative of a morphism between sequential inverse systems consists of a monotone
reindexing `m : ℕ → ℕ` together with compatible level maps `X_{m(n)} ⟶ Y_n`. -/
structure SequentialProObjectMorphismRep {C : Type u} [Category.{v} C] (X Y : ℕᵒᵖ ⥤ C) where
  reindex : ℕ →o ℕ
  hom : reindex.toFunctor.op ⋙ X ⟶ Y

namespace SequentialProObjectMorphismRep

variable {C : Type u} [Category.{v} C] {X Y : ℕᵒᵖ ⥤ C}

/-- The level map associated to a sequential representative at stage `n`. -/
abbrev map (r : SequentialProObjectMorphismRep X Y) (n : ℕ) :
    X.obj (op (r.reindex n)) ⟶ Y.obj (op n) :=
  r.hom.app (op n)

/-- The naturality square for the level maps of a sequential representative. -/
theorem comm (r : SequentialProObjectMorphismRep X Y) {n n' : ℕ} (h : n ≤ n') :
    CommSq (X.map (homOfLE (r.reindex.monotone h)).op) (r.map n') (r.map n)
      (Y.map (homOfLE h).op) := by
  refine CommSq.mk ?_
  simpa using r.hom.naturality (homOfLE h).op

/-- Build a sequential representative from its source-facing coordinate data. -/
def ofMaps (reindex : ℕ →o ℕ)
    (map : ∀ n : ℕ, X.obj (op (reindex n)) ⟶ Y.obj (op n))
    (comm : ∀ ⦃n n' : ℕ⦄ (h : n ≤ n'),
      X.map (homOfLE (reindex.monotone h)).op ≫ map n =
        map n' ≫ Y.map (homOfLE h).op) :
    SequentialProObjectMorphismRep X Y where
  reindex := reindex
  hom :=
    { app := fun n ↦ map n.unop
      naturality := fun n n' g ↦ by
        let h : n'.unop ≤ n.unop := leOfHom g.unop
        simpa [h] using comm h }

/-- The class in `colim_i Hom(X_i, Y_n)` represented by the `n`-th level map of a sequential
representative. -/
noncomputable abbrev classOf (r : SequentialProObjectMorphismRep X Y) (n : ℕ) :
    (proSystemHomColimitFunctor X).obj (Y.obj (op n)) :=
  (colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))).inv <|
    colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
      (ULift.up (r.map n))

private theorem classOf_naturality (r : SequentialProObjectMorphismRep X Y) {n n' : ℕ}
    (h : n ≤ n') :
    (proSystemHomColimitFunctor X).map (Y.map (homOfLE h).op) (r.classOf n') = r.classOf n := by
  let τ :=
    ((Functor.whiskeringLeft ℕᵒᵖᵒᵖ Cᵒᵖ _).obj X.op).map
      (uliftYoneda.map (Y.map (homOfLE h).op))
  let eₙ := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
  let eₙ' := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n'))
  have hmap :
      colim.map τ
          (colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n'))) (op (op (r.reindex n')))
            (ULift.up (r.map n'))) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n')))
          (τ.app (op (op (r.reindex n'))) (ULift.up (r.map n'))) :=
    Types.Colimit.ι_map_apply τ (op (op (r.reindex n'))) (ULift.up (r.map n'))
  have hcolim :
      colim.map τ (eₙ'.hom (r.classOf n')) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
          (ULift.up (r.map n)) := by
    calc
      colim.map τ (eₙ'.hom (r.classOf n')) =
          colim.map τ
            (colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n'))) (op (op (r.reindex n')))
              (ULift.up (r.map n'))) := by
                simp [classOf, eₙ']
      _ = colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n')))
            (τ.app (op (op (r.reindex n'))) (ULift.up (r.map n'))) := hmap
      _ = colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
            (ULift.up (r.map n)) := by
              symm
              refine Types.colimit_sound (((homOfLE (r.reindex.monotone h)).op).op) ?_
              simp [τ, (r.comm h).w]
  have hleft :
      eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE h).op) (r.classOf n')) =
        colim.map τ (eₙ'.hom (r.classOf n')) := by
    change
      eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE h).op) (r.classOf n')) =
        colimMap ((X.op ⋙ uliftCoyoneda).whiskerLeft ((evaluation _ _).map (Y.map (homOfLE h).op)))
          (eₙ'.hom (r.classOf n'))
    simpa [eₙ, eₙ', proSystemHomColimitFunctor] using
      congrFun
        (colimit_map_colimitObjIsoColimitCompEvaluation_hom
          (X.op ⋙ uliftCoyoneda) (Y.map (homOfLE h).op)) (r.classOf n')
  have hright :
      colim.map τ (eₙ'.hom (r.classOf n')) = eₙ.hom (r.classOf n) := by
    exact hcolim.trans <| by simp [classOf, eₙ]
  exact eₙ.toEquiv.injective (hleft.trans hright)

/-- The inverse-limit presentation of the pro-object morphism represented by `r`. -/
noncomputable def toLimitHom (r : SequentialProObjectMorphismRep X Y) :
    limit (Y ⋙ proSystemHomColimitFunctor X) :=
  Types.Limit.mk _ (fun n ↦ r.classOf n.unop) fun i j g ↦ by
    let h : j.unop ≤ i.unop := leOfHom g.unop
    simpa [h] using r.classOf_naturality h

/-- A sequential representative determines a morphism between the associated sequential
pro-objects. -/
noncomputable def toProObjectHom (r : SequentialProObjectMorphismRep X Y) :
    colimit (Y.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor X ⋙ uliftFunctor.{0} :=
  (proObjectHomEquivLimitProSystemHomColimitFunctor X Y).symm r.toLimitHom

/-- Refining the source stages of a sequential representative along a larger monotone reindexing
does not change the underlying level maps in the Hom-colimits. -/
private theorem refine_comm
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) {n n' : ℕ} (h : n ≤ n') :
    X.map (homOfLE (reindex'.monotone h)).op ≫ (X.map (homOfLE (hle n)).op ≫ r.map n) =
      (X.map (homOfLE (hle n')).op ≫ r.map n') ≫ Y.map (homOfLE h).op := by
  -- Reassociate the source transition so that the original compatibility square applies.
  have hsource :
      ((homOfLE (reindex'.monotone h)).op ≫ (homOfLE (hle n)).op) =
        ((homOfLE (hle n')).op ≫ (homOfLE (r.reindex.monotone h)).op) := by
    apply Subsingleton.elim
  calc
    X.map (homOfLE (reindex'.monotone h)).op ≫ (X.map (homOfLE (hle n)).op ≫ r.map n) =
        X.map (((homOfLE (reindex'.monotone h)).op ≫ (homOfLE (hle n)).op)) ≫ r.map n := by
          rw [← Category.assoc, ← X.map_comp]
    _ = X.map (((homOfLE (hle n')).op ≫ (homOfLE (r.reindex.monotone h)).op)) ≫ r.map n := by
          rw [hsource]
    _ =
        (X.map (homOfLE (hle n')).op ≫
          X.map (homOfLE (r.reindex.monotone h)).op) ≫ r.map n := by
          rw [X.map_comp]
    _ = X.map (homOfLE (hle n')).op ≫
        (X.map (homOfLE (r.reindex.monotone h)).op ≫ r.map n) := by
          simp [Category.assoc]
    _ = X.map (homOfLE (hle n')).op ≫ (r.map n' ≫ Y.map (homOfLE h).op) := by
          simp [(r.comm h).w]
    _ = (X.map (homOfLE (hle n')).op ≫ r.map n') ≫ Y.map (homOfLE h).op := by
          simp [Category.assoc]

/-- Enlarging the chosen source stage at each target level gives a canonical refinement of a
sequential representative. -/
private def refine
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    SequentialProObjectMorphismRep X Y :=
  ofMaps reindex'
    (fun n ↦ X.map (homOfLE (hle n)).op ≫ r.map n)
    (fun _ _ h ↦ refine_comm r reindex' hle h)

/-- The class represented at level `n` is unchanged by passing to a larger source stage. -/
private theorem classOf_refine
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) (n : ℕ) :
    (r.refine reindex' hle).classOf n = r.classOf n := by
  let e := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
  -- Passing to a larger source stage does not change the represented colimit class.
  suffices hcolim : e.hom ((r.refine reindex' hle).classOf n) = e.hom (r.classOf n) by
    exact e.toEquiv.injective hcolim
  have hleft :
      e.hom ((r.refine reindex' hle).classOf n) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (reindex' n)))
          (ULift.up (X.map (homOfLE (hle n)).op ≫ r.map n)) := by
    simp [classOf, refine, ofMaps, map, e]
  have hmid :
      colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (reindex' n)))
          (ULift.up (X.map (homOfLE (hle n)).op ≫ r.map n)) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
          (ULift.up (r.map n)) := by
    symm
    refine Types.colimit_sound (((homOfLE (hle n)).op).op) ?_
    simp
  have hright :
      colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r.reindex n)))
          (ULift.up (r.map n)) =
        e.hom (r.classOf n) := by
    simp [classOf, e]
  exact hleft.trans (hmid.trans hright)

/-- Refinement does not change the represented inverse-limit point. -/
private theorem refine_toLimitHom
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    (r.refine reindex' hle).toLimitHom = r.toLimitHom := by
  apply Types.limit_ext
  intro n
  simp [toLimitHom, r.classOf_refine reindex' hle n.unop]

/-- Refinement does not change the represented morphism between the associated pro-objects. -/
private theorem refine_toProObjectHom
    (r : SequentialProObjectMorphismRep X Y)
    (reindex' : ℕ →o ℕ)
    (hle : ∀ n : ℕ, r.reindex n ≤ reindex' n) :
    (r.refine reindex' hle).toProObjectHom = r.toProObjectHom := by
  simpa [toProObjectHom] using
    congrArg
      (fun η ↦ (proObjectHomEquivLimitProSystemHomColimitFunctor X Y).symm η)
      (r.refine_toLimitHom reindex' hle)

/-- Two sequential representatives are equivalent when, after passing to a common monotone
refinement, their level maps agree. -/
def Equivalent (r₁ r₂ : SequentialProObjectMorphismRep X Y) : Prop :=
  ∃ reindex' : ℕ →o ℕ,
    ∃ h₁ : ∀ n : ℕ, r₁.reindex n ≤ reindex' n,
      ∃ h₂ : ∀ n : ℕ, r₂.reindex n ≤ reindex' n,
        ∀ n : ℕ,
          X.map (homOfLE (h₁ n)).op ≫ r₁.map n =
            X.map (homOfLE (h₂ n)).op ≫ r₂.map n

/-- Helper for Example 4.22.6: a concrete map `X_i ⟶ Y_n` represents the `n`-th component of a
limit point when it maps to that component in the Hom-colimit. -/
abbrev Represents
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X))
    (n i : ℕ) (f : X.obj (op i) ⟶ Y.obj (op n)) : Prop :=
  colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op i)) (ULift.up f) =
    (colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))).hom
      (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ)

/-- Helper for Example 4.22.6: a chosen representative of the `n`-th component of a limit
point. -/
private structure LevelRepresentative
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X)) (n : ℕ) where
  source : ℕ
  hom : X.obj (op source) ⟶ Y.obj (op n)
  represents : Represents ξ n source hom

/-- Helper for Example 4.22.6: a one-step enlargement of a chosen level representative, recording
both the new representative and the adjacent compatibility square. -/
private structure SuccessorRefinement
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X))
    (n : ℕ) (p : LevelRepresentative (X := X) (Y := Y) ξ n) where
  source : ℕ
  le_source : p.source ≤ source
  hom : X.obj (op source) ⟶ Y.obj (op (n + 1))
  represents : Represents ξ (n + 1) source hom
  comm : X.map (homOfLE le_source).op ≫ p.hom =
    hom ≫ Y.map (homOfLE (Nat.le_succ n)).op

/-- Helper for Example 4.22.6: forget the extra compatibility data from a successor refinement
and retain only the new level representative. -/
private def SuccessorRefinement.toLevelRepresentative
    {ξ : limit (Y ⋙ proSystemHomColimitFunctor X)}
    {n : ℕ} {p : LevelRepresentative (X := X) (Y := Y) ξ n}
    (s : SuccessorRefinement (X := X) (Y := Y) ξ n p) :
    LevelRepresentative (X := X) (Y := Y) ξ (n + 1) where
  source := s.source
  hom := s.hom
  represents := s.represents

/-- Helper for Example 4.22.6: each component of a limit point is represented by some source
stage. -/
theorem exists_level_representation
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X)) (n : ℕ) :
    ∃ i : ℕ, ∃ f : X.obj (op i) ⟶ Y.obj (op n), Represents ξ n i f := by
  let e := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
  -- Choose one concrete representative of the `n`-th Hom-colimit class.
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective'
    (e.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ))
  refine ⟨j.unop.unop, y.down, ?_⟩
  simpa [Represents, e] using hy

/-- Helper for Example 4.22.6: a chosen representative at level `n` can be enlarged so that it
comes from a representative of level `n + 1` with the adjacent square commuting. -/
theorem exists_successor_refinement
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X))
    (n i : ℕ)
    (f : X.obj (op i) ⟶ Y.obj (op n))
    (hf : Represents ξ n i f) :
    ∃ k : ℕ, ∃ hik : i ≤ k, ∃ g : X.obj (op k) ⟶ Y.obj (op (n + 1)),
      Represents ξ (n + 1) k g ∧
      X.map (homOfLE hik).op ≫ f = g ≫ Y.map (homOfLE (Nat.le_succ n)).op := by
  obtain ⟨j, g₀, hg₀⟩ := exists_level_representation (X := X) (Y := Y) ξ (n + 1)
  let Fₙ := X.op ⋙ uliftYoneda.obj (Y.obj (op n))
  let Fₙ₁ := X.op ⋙ uliftYoneda.obj (Y.obj (op (n + 1)))
  let eₙ := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
  let eₙ₁ := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op (n + 1)))
  let τ :=
    ((Functor.whiskeringLeft ℕᵒᵖᵒᵖ Cᵒᵖ _).obj X.op).map
      (uliftYoneda.map (Y.map (homOfLE (Nat.le_succ n)).op))
  have hlimit :
      (proSystemHomColimitFunctor X).map (Y.map (homOfLE (Nat.le_succ n)).op)
          (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ) =
        limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ := by
    simpa using
      congrFun
        (limit.w (Y ⋙ proSystemHomColimitFunctor X) (homOfLE (Nat.le_succ n)).op) ξ
  have htransport :
      colim.map τ (eₙ₁.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) =
        eₙ.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ) := by
    have hleft :
        eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE (Nat.le_succ n)).op)
            (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) =
          colim.map τ (eₙ₁.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) := by
      change
        eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE (Nat.le_succ n)).op)
            (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) =
          colimMap ((X.op ⋙ uliftCoyoneda).whiskerLeft
            ((evaluation _ _).map (Y.map (homOfLE (Nat.le_succ n)).op)))
            (eₙ₁.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ))
      simpa [eₙ, eₙ₁, proSystemHomColimitFunctor] using
        congrFun
          (colimit_map_colimitObjIsoColimitCompEvaluation_hom
            (X.op ⋙ uliftCoyoneda) (Y.map (homOfLE (Nat.le_succ n)).op))
          (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)
    calc
      colim.map τ (eₙ₁.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) =
          eₙ.hom ((proSystemHomColimitFunctor X).map (Y.map (homOfLE (Nat.le_succ n)).op)
            (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) := by
              symm
              exact hleft
      _ = eₙ.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ) := by
            rw [hlimit]
  have hcolim :
      colimit.ι Fₙ (op (op j)) (ULift.up (g₀ ≫ Y.map (homOfLE (Nat.le_succ n)).op)) =
        colimit.ι Fₙ (op (op i)) (ULift.up f) := by
    have hmap_g₀ :
        colim.map τ (colimit.ι Fₙ₁ (op (op j)) (ULift.up g₀)) =
          colim.map τ (eₙ₁.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ)) := by
      rw [hg₀]
    have hmiddle :
        colim.map τ (colimit.ι Fₙ₁ (op (op j)) (ULift.up g₀)) =
          eₙ.hom (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ) :=
      hmap_g₀.trans htransport
    -- Compare the two representatives after transporting the `(n + 1)`-component down to level
    -- `n` using the limit compatibility.
    refine (Eq.trans ?_ hmiddle).trans ?_
    · symm
      simpa [Fₙ, Fₙ₁, τ]
        using Types.Colimit.ι_map_apply τ (op (op j)) (ULift.up g₀)
    · rw [← hf]
  obtain ⟨k, a, b, hab⟩ :=
    (CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff Fₙ).mp hcolim
  let k' : ℕ := k.unop.unop
  have hjk : j ≤ k' := leOfHom a.unop.unop
  have hik : i ≤ k' := leOfHom b.unop.unop
  let g : X.obj (op k') ⟶ Y.obj (op (n + 1)) := X.map (homOfLE hjk).op ≫ g₀
  refine ⟨k', hik, g, ?_, ?_⟩
  · -- Enlarge the representative of level `n + 1` to the common larger stage.
    calc
      colimit.ι Fₙ₁ (op (op k')) (ULift.up g) =
          colimit.ι Fₙ₁ (op (op j)) (ULift.up g₀) := by
            symm
            refine Types.colimit_sound (((homOfLE hjk).op).op) ?_
            simp [Fₙ₁, g]
      _ =
          (colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0})
            (Y.obj (op (n + 1)))).hom
            (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op (n + 1)) ξ) := hg₀
  · -- The filtered-colimit witness is exactly the desired adjacent compatibility square.
    simpa [Fₙ, g, k', hik, hjk, Category.assoc] using hab.symm

/-- Helper for Example 4.22.6: adjacent compatibility squares imply compatibility for every
transition map `n' ⟶ n`. -/
theorem comm_of_succ_comm
    (reindex : ℕ →o ℕ)
    (a : ∀ n : ℕ, X.obj (op (reindex n)) ⟶ Y.obj (op n))
    (hsucc : ∀ n : ℕ,
      X.map (homOfLE (reindex.monotone (Nat.le_succ n))).op ≫ a n =
        a (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op) :
    ∀ ⦃n n' : ℕ⦄ (h : n ≤ n'),
      X.map (homOfLE (reindex.monotone h)).op ≫ a n =
        a n' ≫ Y.map (homOfLE h).op := by
  intro n n' h
  induction h with
  | refl =>
      simp
  | @step n' h ih =>
      have hsource :
          (homOfLE (reindex.monotone (Nat.le_succ_of_le h))).op =
            (homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫
              (homOfLE (reindex.monotone h)).op := by
        apply Subsingleton.elim
      have htarget :
          (homOfLE (Nat.le_succ_of_le h)).op =
            (homOfLE (Nat.le_succ n')).op ≫ (homOfLE h).op := by
        apply Subsingleton.elim
      -- Compose the inductive compatibility with the next adjacent square.
      calc
        X.map (homOfLE (reindex.monotone (Nat.le_succ_of_le h))).op ≫ a n =
            X.map ((homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫
                (homOfLE (reindex.monotone h)).op) ≫ a n := by
                  rw [hsource]
        _ = (X.map (homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫
              X.map (homOfLE (reindex.monotone h)).op) ≫ a n := by
                rw [X.map_comp]
        _ = X.map (homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫
              (X.map (homOfLE (reindex.monotone h)).op ≫ a n) := by
                simp [Category.assoc]
        _ = X.map (homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫
              (a n' ≫ Y.map (homOfLE h).op) := by
                rw [ih]
        _ = (X.map (homOfLE (reindex.monotone (Nat.le_succ n'))).op ≫ a n') ≫
              Y.map (homOfLE h).op := by
                simp [Category.assoc]
        _ = (a (n' + 1) ≫ Y.map (homOfLE (Nat.le_succ n')).op) ≫
              Y.map (homOfLE h).op := by
                rw [hsucc n']
        _ = a (n' + 1) ≫
              (Y.map (homOfLE (Nat.le_succ n')).op ≫ Y.map (homOfLE h).op) := by
                simp [Category.assoc]
        _ = a (n' + 1) ≫
              Y.map ((homOfLE (Nat.le_succ n')).op ≫ (homOfLE h).op) := by
                rw [← Y.map_comp]
        _ = a (n' + 1) ≫ Y.map (homOfLE (Nat.le_succ_of_le h)).op := by
                rw [htarget]

/-- Helper for Example 4.22.6: every limit point of
`Y ⋙ proSystemHomColimitFunctor X` comes from a sequential representative. -/
theorem exists_rep_of_limit_point
    (ξ : limit (Y ⋙ proSystemHomColimitFunctor X)) :
    ∃ r : SequentialProObjectMorphismRep X Y, r.toLimitHom = ξ := by
  classical
  let baseLevel : LevelRepresentative (X := X) (Y := Y) ξ 0 :=
    let h0 := exists_level_representation (X := X) (Y := Y) ξ 0
    { source := Classical.choose h0
      hom := Classical.choose (Classical.choose_spec h0)
      represents := Classical.choose_spec (Classical.choose_spec h0) }
  let successorChoice :
      ∀ n : ℕ,
        (p : LevelRepresentative (X := X) (Y := Y) ξ n) →
          SuccessorRefinement (X := X) (Y := Y) ξ n p := fun n p ↦
    let hs := exists_successor_refinement (X := X) (Y := Y) ξ n p.source p.hom p.represents
    { source := Classical.choose hs
      le_source := Classical.choose (Classical.choose_spec hs)
      hom := Classical.choose (Classical.choose_spec (Classical.choose_spec hs))
      represents := (Classical.choose_spec
        (Classical.choose_spec (Classical.choose_spec hs))).1
      comm := (Classical.choose_spec
        (Classical.choose_spec (Classical.choose_spec hs))).2 }
  let choice : ∀ n : ℕ, LevelRepresentative (X := X) (Y := Y) ξ n :=
    Nat.rec (motive := fun n ↦ LevelRepresentative (X := X) (Y := Y) ξ n)
      baseLevel
      (fun n p ↦ (successorChoice n p).toLevelRepresentative)
  have choice_succ :
      ∀ n : ℕ,
        choice (n + 1) = (successorChoice n (choice n)).toLevelRepresentative := by
    intro n
    rfl
  let stage : ℕ → ℕ := fun n ↦ (choice n).source
  let maps : ∀ n : ℕ, X.obj (op (stage n)) ⟶ Y.obj (op n) := fun n ↦ (choice n).hom
  have hrep : ∀ n : ℕ, Represents ξ n (stage n) (maps n) := fun n ↦ (choice n).represents
  have hsucc_le : ∀ n : ℕ, stage n ≤ stage (n + 1) := by
    intro n
    simpa [stage, choice_succ n] using (successorChoice n (choice n)).le_source
  have hsucc_comm :
      ∀ n : ℕ,
        X.map (homOfLE (hsucc_le n)).op ≫ maps n =
          maps (n + 1) ≫ Y.map (homOfLE (Nat.le_succ n)).op := by
    intro n
    simpa [stage, maps, choice_succ n] using (successorChoice n (choice n)).comm
  let reindex : ℕ →o ℕ :=
    { toFun := stage
      monotone' := monotone_nat_of_le_succ hsucc_le }
  let r : SequentialProObjectMorphismRep X Y :=
    ofMaps reindex maps (fun _ _ h ↦ comm_of_succ_comm (X := X) (Y := Y) reindex maps hsucc_comm h)
  have hclass :
      ∀ n : ℕ, r.classOf n = limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n) ξ := by
    intro n
    let e := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
    -- Both classes have the same image in the raw Hom-colimit, so they are equal.
    apply e.toEquiv.injective
    simpa [SequentialProObjectMorphismRep.classOf, SequentialProObjectMorphismRep.map,
      SequentialProObjectMorphismRep.ofMaps, r, reindex, stage, maps, e] using hrep n
  refine ⟨r, ?_⟩
  apply Types.limit_ext
  intro n
  -- Compare the constructed representative with `ξ` componentwise in the limit.
  simpa [SequentialProObjectMorphismRep.toLimitHom] using hclass n.unop

/-- Helper for Example 4.22.6: equality of two level Hom-colimit classes can be witnessed after
passing to one common source stage. -/
private theorem exists_common_stage_of_classOf_eq
    (r₁ r₂ : SequentialProObjectMorphismRep X Y) {n : ℕ}
    (hclass : r₁.classOf n = r₂.classOf n) :
    ∃ k : ℕ, ∃ h₁ : r₁.reindex n ≤ k, ∃ h₂ : r₂.reindex n ≤ k,
      X.map (homOfLE h₁).op ≫ r₁.map n = X.map (homOfLE h₂).op ≫ r₂.map n := by
  let e := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
  have hcolim :
      colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r₁.reindex n)))
          (ULift.up (r₁.map n)) =
        colimit.ι (X.op ⋙ uliftYoneda.obj (Y.obj (op n))) (op (op (r₂.reindex n)))
          (ULift.up (r₂.map n)) := by
    simpa [classOf, e] using congrArg e.hom hclass
  -- Equality in the filtered colimit is detected at a common larger index.
  obtain ⟨k, f, g, hfg⟩ :=
    (CategoryTheory.Limits.Types.FilteredColimit.colimit_eq_iff
      (X.op ⋙ uliftYoneda.obj (Y.obj (op n)))).mp hcolim
  let k' : ℕ := k.unop.unop
  have hk₁ : r₁.reindex n ≤ k' := leOfHom f.unop.unop
  have hk₂ : r₂.reindex n ≤ k' := leOfHom g.unop.unop
  refine ⟨k', hk₁, hk₂, ?_⟩
  simpa [k', hk₁, hk₂] using hfg

/-- Helper for Example 4.22.6: an equality of level maps remains true after enlarging the common
source stage once more. -/
private theorem transport_level_eq
    {n i j k l : ℕ}
    {f : X.obj (op i) ⟶ Y.obj (op n)}
    {g : X.obj (op j) ⟶ Y.obj (op n)}
    {hᵢ : i ≤ k}
    {hⱼ : j ≤ k}
    (heq : X.map (homOfLE hᵢ).op ≫ f = X.map (homOfLE hⱼ).op ≫ g)
    (hkl : k ≤ l) :
    X.map (homOfLE (le_trans hᵢ hkl)).op ≫ f =
      X.map (homOfLE (le_trans hⱼ hkl)).op ≫ g := by
  have hcomp₁ :
      (homOfLE (le_trans hᵢ hkl)).op = (homOfLE hkl).op ≫ (homOfLE hᵢ).op := by
    apply Subsingleton.elim
  have hcomp₂ :
      (homOfLE (le_trans hⱼ hkl)).op = (homOfLE hkl).op ≫ (homOfLE hⱼ).op := by
    apply Subsingleton.elim
  -- Precompose the known equality with the transition map from the larger stage.
  calc
    X.map (homOfLE (le_trans hᵢ hkl)).op ≫ f =
        X.map ((homOfLE hkl).op ≫ (homOfLE hᵢ).op) ≫ f := by
          rw [hcomp₁]
    _ = X.map (homOfLE hkl).op ≫ (X.map (homOfLE hᵢ).op ≫ f) := by
          rw [X.map_comp, Category.assoc]
    _ = X.map (homOfLE hkl).op ≫ (X.map (homOfLE hⱼ).op ≫ g) := by
          rw [heq]
    _ = X.map ((homOfLE hkl).op ≫ (homOfLE hⱼ).op) ≫ g := by
          rw [X.map_comp, Category.assoc]
    _ = X.map (homOfLE (le_trans hⱼ hkl)).op ≫ g := by
          rw [hcomp₂]

/-- Helper for Example 4.22.6: levelwise equality of Hom-colimit classes implies the textbook
common-refinement equivalence of representatives. -/
theorem equivalent_of_level_class_eq
    (r₁ r₂ : SequentialProObjectMorphismRep X Y)
    (hclass : ∀ n : ℕ, r₁.classOf n = r₂.classOf n) :
    r₁.Equivalent r₂ := by
  classical
  let stage : ℕ → ℕ := fun n ↦
    (exists_common_stage_of_classOf_eq r₁ r₂ (hclass n)).choose
  let stage_h₁ : ∀ n : ℕ, r₁.reindex n ≤ stage n := fun n ↦
    (exists_common_stage_of_classOf_eq r₁ r₂ (hclass n)).choose_spec.1
  let stage_h₂ : ∀ n : ℕ, r₂.reindex n ≤ stage n := fun n ↦
    (exists_common_stage_of_classOf_eq r₁ r₂ (hclass n)).choose_spec.2.1
  let stage_eq :
      ∀ n : ℕ,
        X.map (homOfLE (stage_h₁ n)).op ≫ r₁.map n =
          X.map (homOfLE (stage_h₂ n)).op ≫ r₂.map n := fun n ↦
      (exists_common_stage_of_classOf_eq r₁ r₂ (hclass n)).choose_spec.2.2
  let reindexFn : ℕ → ℕ :=
    Nat.rec (stage 0) (fun n m ↦ max m (stage (n + 1)))
  let reindex' : ℕ →o ℕ :=
    { toFun := reindexFn
      monotone' := monotone_nat_of_le_succ fun n ↦ by
        simp [reindexFn] }
  have hstage_le : ∀ n : ℕ, stage n ≤ reindex' n := by
    intro n
    induction n with
    | zero =>
        simp [reindex', reindexFn]
    | succ n ih =>
        simp [reindex', reindexFn]
  have h₁ : ∀ n : ℕ, r₁.reindex n ≤ reindex' n := fun n ↦
    le_trans (stage_h₁ n) (hstage_le n)
  have h₂ : ∀ n : ℕ, r₂.reindex n ≤ reindex' n := fun n ↦
    le_trans (stage_h₂ n) (hstage_le n)
  refine ⟨reindex', h₁, h₂, ?_⟩
  intro n
  -- Transport the stagewise equality to the recursively enlarged common stage.
  simpa [h₁, h₂] using
    transport_level_eq (f := r₁.map n) (g := r₂.map n) (heq := stage_eq n) (hkl := hstage_le n)

/-- The identity representative of a sequential inverse system. -/
def idRep (X : ℕᵒᵖ ⥤ C) : SequentialProObjectMorphismRep X X :=
  ofMaps OrderHom.id
    (fun n ↦ 𝟙 (X.obj (op n)))
    (fun _ _ h ↦ by simp)

/-- Compatibility of the composite representative with transition morphisms. -/
theorem compRep_comm
    {Z : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y)
    (s : SequentialProObjectMorphismRep Y Z) :
    ∀ ⦃n n' : ℕ⦄ (h : n ≤ n'),
      X.map (homOfLE ((r.reindex.comp s.reindex).monotone h)).op ≫
          (r.map (s.reindex n) ≫ s.map n) =
        (r.map (s.reindex n') ≫ s.map n') ≫ Z.map (homOfLE h).op := by
  intro n n' h
  calc
    X.map (homOfLE ((r.reindex.comp s.reindex).monotone h)).op ≫
        (r.map (s.reindex n) ≫ s.map n) =
      (X.map (homOfLE (r.reindex.monotone (s.reindex.monotone h))).op ≫
          r.map (s.reindex n)) ≫ s.map n := by simp [Category.assoc]
    _ = (r.map (s.reindex n') ≫ Y.map (homOfLE (s.reindex.monotone h)).op) ≫ s.map n := by
      simp [Category.assoc, (r.comm (s.reindex.monotone h)).w]
    _ = r.map (s.reindex n') ≫
        (Y.map (homOfLE (s.reindex.monotone h)).op ≫ s.map n) := by
      simp [Category.assoc]
    _ = r.map (s.reindex n') ≫ (s.map n' ≫ Z.map (homOfLE h).op) := by
      simp [(s.comm h).w]
    _ = (r.map (s.reindex n') ≫ s.map n') ≫ Z.map (homOfLE h).op := by
      simp [Category.assoc]

/-- Composition of sequential representatives of pro-object morphisms. -/
def compRep
    {Z : ℕᵒᵖ ⥤ C}
    (r : SequentialProObjectMorphismRep X Y)
    (s : SequentialProObjectMorphismRep Y Z) :
    SequentialProObjectMorphismRep X Z :=
  ofMaps (r.reindex.comp s.reindex)
    (fun n ↦ r.map (s.reindex n) ≫ s.map n)
    (compRep_comm r s)

/-- A representative is a pro-isomorphism if it admits an inverse up to common-refinement
equivalence. -/
def IsProIsomorphism (r : SequentialProObjectMorphismRep X Y) : Prop :=
  ∃ s : SequentialProObjectMorphismRep Y X,
    Equivalent (compRep r s) (idRep X) ∧ Equivalent (compRep s r) (idRep Y)

end SequentialProObjectMorphismRep

section

variable {C : Type u} [Category.{v} C] {X Y : ℕᵒᵖ ⥤ C}

-- Proof sketch: choose, for each `n`, a stage of `X` and a map to `Y_n` representing the `n`-th
-- Hom-colimit class of `η`; then enlarge inductively so the chosen stages are monotone and the
-- compatibility squares commute.
/-- Example 4.22.6: every morphism between the associated sequential pro-objects is represented by
a monotone reindexing and compatible level maps. -/
theorem exists_representative
    (η : colimit (Y.op ⋙ uliftCoyoneda.{0}) ⟶ proSystemHomColimitFunctor X ⋙ uliftFunctor.{0}) :
    ∃ r : SequentialProObjectMorphismRep X Y, r.toProObjectHom = η := by
  let ξ := proObjectHomEquivLimitProSystemHomColimitFunctor X Y η
  -- Route correction: first solve the source-stage extraction problem for the canonical limit
  -- point, then transport the resulting representative back across the equivalence.
  obtain ⟨r, hr⟩ := SequentialProObjectMorphismRep.exists_rep_of_limit_point
    (X := X) (Y := Y) ξ
  refine ⟨r, ?_⟩
  -- Apply the inverse equivalence to the identified limit point.
  simpa [ξ, SequentialProObjectMorphismRep.toProObjectHom] using
    congrArg
      (fun ζ ↦ (proObjectHomEquivLimitProSystemHomColimitFunctor X Y).symm ζ) hr

-- Proof sketch: one direction follows by refining both representatives to a common larger
-- monotone sequence and comparing the resulting stage maps; the converse uses that equality after
-- such a common refinement gives the same classes in every Hom-colimit.
/-- Companion to Example 4.22.6: two sequential representatives define the same pro-object
morphism exactly when, after passing to a common monotone refinement, their level maps become
equal. -/
theorem represents_eq_iff_equivalent
    (r₁ r₂ : SequentialProObjectMorphismRep X Y) :
    r₁.toProObjectHom = r₂.toProObjectHom ↔ r₁.Equivalent r₂ := by
  constructor
  · intro h
    -- Apply the comparison equivalence to identify the represented limit points.
    have hlimit : r₁.toLimitHom = r₂.toLimitHom := by
      simpa [SequentialProObjectMorphismRep.toProObjectHom] using
        congrArg (proObjectHomEquivLimitProSystemHomColimitFunctor X Y) h
    have hclass : ∀ n : ℕ, r₁.classOf n = r₂.classOf n := by
      intro n
      -- Equality in the limit is checked componentwise.
      simpa [SequentialProObjectMorphismRep.toLimitHom] using
        congrArg (limit.π (Y ⋙ proSystemHomColimitFunctor X) (op n)) hlimit
    exact SequentialProObjectMorphismRep.equivalent_of_level_class_eq r₁ r₂ hclass
  · rintro ⟨reindex', h₁, h₂, heq⟩
    have hclass_refined :
        ∀ n : ℕ,
          (r₁.refine reindex' h₁).classOf n = (r₂.refine reindex' h₂).classOf n := by
      intro n
      let e := colimitObjIsoColimitCompEvaluation (X.op ⋙ uliftCoyoneda.{0}) (Y.obj (op n))
      apply e.toEquiv.injective
      -- After refining to the same stages, the level maps agree by hypothesis.
      simp [SequentialProObjectMorphismRep.classOf, SequentialProObjectMorphismRep.refine,
        SequentialProObjectMorphismRep.ofMaps, SequentialProObjectMorphismRep.map, e, heq n]
    have hlimit_refined :
        (r₁.refine reindex' h₁).toLimitHom = (r₂.refine reindex' h₂).toLimitHom := by
      apply Types.limit_ext
      intro n
      simpa [SequentialProObjectMorphismRep.toLimitHom] using hclass_refined n.unop
    -- Route correction: compare both representatives only after moving them to the same reindexing.
    calc
      r₁.toProObjectHom = (r₁.refine reindex' h₁).toProObjectHom := by
        symm
        exact r₁.refine_toProObjectHom reindex' h₁
      _ = (r₂.refine reindex' h₂).toProObjectHom := by
        simpa [SequentialProObjectMorphismRep.toProObjectHom] using
          congrArg
            (fun ξ ↦ (proObjectHomEquivLimitProSystemHomColimitFunctor X Y).symm ξ)
            hlimit_refined
      _ = r₂.toProObjectHom := by
        exact r₂.refine_toProObjectHom reindex' h₂

end

end CategoryTheory
