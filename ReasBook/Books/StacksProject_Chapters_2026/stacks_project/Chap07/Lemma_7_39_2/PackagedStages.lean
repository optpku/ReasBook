module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_8_2
public import stacks_project.Chap07.Lemma_7_39_1
public import stacks_project.Chap07.Lemma_7_39_2.RequestScheduling

@[expose] public section

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

section

variable {J : GrothendieckTopology C}

open GrothendieckTopology.Point.ofIsCofiltered

variable {ι : Type w} [Preorder ι]

/-- Helper for Lemma 7.39.2: a packaged refinement stage over the original system, together with
the requests already forced on that stage. -/
structure refinement_stage
    (S' : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    (s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ) where
  I : Type w
  instPreorder : Preorder I
  instDirected : IsDirected I (· ≤ ·)
  T : Iᵒᵖ ⥤ C
  j : ι ↪o I
  e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T
  separated :
    ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
      (Type (max u v w))).obj ℱ) s ≠
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s'
  solved : Set (finite_cover_lift_request J T)
  solved_realized :
    ∀ ⦃r : finite_cover_lift_request J T⦄, r ∈ solved → request_realized (J := J) r

attribute [instance] refinement_stage.instPreorder refinement_stage.instDirected

/-- Helper for Lemma 7.39.2: the identity order embedding gives the trivial refinement of an
inverse system. -/
noncomputable def identity_refinement_iso (S' : ιᵒᵖ ⥤ C) :
    S' ≅
      ((show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩).toOrderHom.toFunctor).op ⋙ S' := by
  -- The identity refinement is just the left unitor for functor composition.
  simpa using (Functor.leftUnitor S').symm

/-- Helper for Lemma 7.39.2: the trivial refinement acts as the identity on inverse-system
fibers. -/
theorem refinementFiber_identity
    (S' : ιᵒᵖ ⥤ C) :
    refinementFiber (show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩) S'
        (identity_refinement_iso (ι := ι) S') =
      𝟙 (fiber.{max u v w} S') := by
  ext W x
  rcases fiberMk_jointly_surjective x with ⟨U, f, rfl⟩
  -- The identity refinement sends each generator to itself.
  simp [identity_refinement_iso, refinementFiber_app_fiberMk]

/-- Helper for Lemma 7.39.2: the base stage preserves the original separation hypothesis because
the trivial refinement induces the identity on sheaf fibers. -/
theorem identity_refinement_preserves_separation
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') :
    ((refinementFiber (show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩) S'
        (identity_refinement_iso (ι := ι) S')).presheafFiber).app
        ((sheafToPresheaf J (Type (max u v w))).obj ℱ) s ≠
    ((refinementFiber (show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩) S'
        (identity_refinement_iso (ι := ι) S')).presheafFiber).app
        ((sheafToPresheaf J (Type (max u v w))).obj ℱ) s' := by
  -- After identifying the trivial refinement map with the identity, this is exactly `hss'`.
  let Fobj : Cᵒᵖ ⥤ Type (max u v w) := (sheafToPresheaf J (Type (max u v w))).obj ℱ
  have hpresheafIdentity :
      (NatTrans.presheafFiber (𝟙 (fiber.{max u v w} S'))).app Fobj = 𝟙 _ := by
    -- The induced map on raw sheaf fibers is determined by the canonical generators.
    apply (fiber.{max u v w} S').presheafFiber_hom_ext
    intro X x
    calc
      (fiber.{max u v w} S').toPresheafFiber X x Fobj ≫
          (NatTrans.presheafFiber (𝟙 (fiber.{max u v w} S'))).app Fobj =
        (fiber.{max u v w} S').toPresheafFiber X
          ((show fiber.{max u v w} S' ⟶ fiber.{max u v w} S' from 𝟙 _).app X x) Fobj := by
            simpa using NatTrans.toPresheafFiber_presheafFiber_app
              (η := 𝟙 (fiber.{max u v w} S')) (F := Fobj) X x
      _ = (fiber.{max u v w} S').toPresheafFiber X x Fobj := by
            rfl
      _ = (fiber.{max u v w} S').toPresheafFiber X x Fobj ≫ 𝟙 _ := by
            simp
  rw [show ((refinementFiber (show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩) S'
      (identity_refinement_iso (ι := ι) S')).presheafFiber).app Fobj =
      (NatTrans.presheafFiber (𝟙 (fiber.{max u v w} S'))).app Fobj by
        simpa [Fobj, refinementFiber_identity (ι := ι) (S' := S')]
  ]
  rw [hpresheafIdentity]
  simpa using hss'

/-- Helper for Lemma 7.39.2: the empty solved set satisfies the `solved_realized` field
vacuously. -/
theorem empty_solved_requests_realized
    {S' : ιᵒᵖ ⥤ C} :
    ∀ ⦃r : finite_cover_lift_request J S'⦄,
      r ∈ (∅ : Set (finite_cover_lift_request J S')) → request_realized (J := J) r := by
  intro r hr
  simpa using hr

/-- Helper for Lemma 7.39.2: the initial packaged stage is the original inverse system with no
scheduled lifting requests solved yet. -/
noncomputable def base_refinement_stage
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    [IsDirected ι (· ≤ ·)] (hss' : s ≠ s') :
    refinement_stage (J := J) S' (ℱ := ℱ) s s' := {
  I := ι
  instPreorder := inferInstance
  instDirected := inferInstance
  T := S'
  j := ⟨Function.Embedding.refl _, Iff.rfl⟩
  e := identity_refinement_iso (ι := ι) S'
  separated := identity_refinement_preserves_separation (J := J) (ι := ι) (S' := S') hss'
  solved := ∅
  solved_realized := empty_solved_requests_realized (J := J)
}

/-- Helper for Lemma 7.39.2: a global code for one stage-relative finite-cover lifting request. -/
abbrev request_code
    (S' : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    (s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ) :=
  Σ A : refinement_stage (J := J) S' (ℱ := ℱ) s s', finite_cover_lift_request J A.T

/-- Helper for Lemma 7.39.2: a morphism of packaged stages is a further refinement that transports
every previously solved request to a solved request on the larger stage. -/
structure refinement_stage_hom
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A B : refinement_stage (J := J) S' (ℱ := ℱ) s s') where
  k : A.I ↪o B.I
  hT : A.T ≅ (k.toOrderHom.toFunctor).op ⋙ B.T
  solved_mono :
    ∀ ⦃r : finite_cover_lift_request J A.T⦄, r ∈ A.solved →
      transport_request (J := J) k B.T hT r ∈ B.solved

namespace refinement_stage_hom

/-- Helper for Lemma 7.39.2: a stage morphism is compatible with the recorded refinement from
the original inverse system when the target's original embedding and original-system
identification are obtained by composing the source's data with the stage morphism. This is the
coherence datum needed when taking direct unions of constructed chains of stages. -/
def original_compatible
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A B) : Prop :=
  B.j = compose_refinement_embedding A.j h.k ∧
    HEq B.e (compose_refinement_iso A.j h.k A.e h.hT)

end refinement_stage_hom

/-- Helper for Lemma 7.39.2: transporting a request along the identity refinement leaves the
request unchanged. -/
theorem transport_request_identity
    {S' : ιᵒᵖ ⥤ C} (r : finite_cover_lift_request J S') :
    transport_request (J := J)
        (show ι ↪o ι from ⟨Function.Embedding.refl _, Iff.rfl⟩) S'
        (identity_refinement_iso (ι := ι) S') r = r := by
  cases r
  -- The only nontrivial field is the transported fiber element, and the identity refinement fixes it.
  simp [transport_request, refinementFiber_identity (ι := ι) (S' := S')]

/-- Helper for Lemma 7.39.2: every packaged stage has the obvious identity self-refinement. -/
noncomputable def refinement_stage_hom_refl
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    refinement_stage_hom (J := J) A A where
  k := ⟨Function.Embedding.refl _, Iff.rfl⟩
  hT := identity_refinement_iso (ι := A.I) A.T
  solved_mono := by
    intro r hr
    -- The identity stage morphism does not change the transported request.
    simpa [transport_request_identity (J := J) (ι := A.I) r] using hr

namespace refinement_stage_hom

/-- Helper for Lemma 7.39.2: the identity stage morphism is compatible with the recorded
refinement from the original inverse system. -/
theorem original_compatible_refl
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    (refinement_stage_hom_refl (J := J) A).original_compatible := by
  constructor
  · ext i
    rfl
  · apply heq_of_eq
    ext X
    simp [refinement_stage_hom_refl, compose_refinement_iso, compose_refinement_embedding,
      identity_refinement_iso, Functor.associator]

/-- Helper for Lemma 7.39.2: transport one request along a morphism of packaged stages. -/
noncomputable def map_request
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A B) (r : finite_cover_lift_request J A.T) :
    finite_cover_lift_request J B.T :=
  transport_request (J := J) h.k B.T h.hT r

/-- Helper for Lemma 7.39.2: a realized request remains realized after transporting it along a
stage morphism. -/
theorem map_request_realized
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A B) (r : finite_cover_lift_request J A.T) :
    request_realized (J := J) r →
      request_realized (J := J) (h.map_request r) := by
  -- This is the request-transport monotonicity needed in the successor and union steps.
  exact request_realized_transport (J := J) h.k B.T h.hT r

/-- Helper for Lemma 7.39.2: compose two morphisms of packaged stages. -/
noncomputable def comp
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B D : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hAB : refinement_stage_hom (J := J) A B)
    (hBD : refinement_stage_hom (J := J) B D) :
    refinement_stage_hom (J := J) A D where
  k := compose_refinement_embedding hAB.k hBD.k
  hT := compose_refinement_iso hAB.k hBD.k hAB.hT hBD.hT
  solved_mono := by
    intro r hr
    -- Rewrite the two-step transport as the direct composite transport, then use monotonicity
    -- along each stage morphism once.
    have hmid : hAB.map_request r ∈ B.solved := hAB.solved_mono hr
    rw [show transport_request (J := J) (compose_refinement_embedding hAB.k hBD.k) D.T
          (compose_refinement_iso hAB.k hBD.k hAB.hT hBD.hT) r =
        transport_request (J := J) hBD.k D.T hBD.hT (hAB.map_request r) by
          simpa [map_request] using
            transport_request_comp (J := J) hAB.k hBD.k hAB.hT hBD.hT r]
    exact hBD.solved_mono hmid

/-- Helper for Lemma 7.39.2: mapping a request along a composite stage morphism is the same as
mapping it successively along the two stage morphisms. -/
theorem map_request_comp
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B D : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hAB : refinement_stage_hom (J := J) A B)
    (hBD : refinement_stage_hom (J := J) B D)
    (r : finite_cover_lift_request J A.T) :
    (comp (J := J) hAB hBD).map_request r = hBD.map_request (hAB.map_request r) := by
  -- Normalize the composite-stage transport to the two one-step transports.
  exact transport_request_comp (J := J) hAB.k hBD.k hAB.hT hBD.hT r

/-- Helper for Lemma 7.39.2: composing a packaged stage morphism with the identity morphism on
the target stage gives the original packaged stage morphism. -/
theorem comp_refl
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A B) :
    refinement_stage_hom.comp (J := J) h (refinement_stage_hom_refl (J := J) B) = h := by
  cases h with
  | mk k hT solved_mono =>
      simp [comp, refinement_stage_hom_refl, compose_refinement_iso,
        compose_refinement_embedding, identity_refinement_iso]
      constructor
      · ext i
        rfl
      · ext X
        simp [Functor.associator]

/-- Helper for Lemma 7.39.2: composing the identity morphism on the source stage with a packaged
stage morphism gives the original packaged stage morphism. -/
theorem refl_comp
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A B) :
    refinement_stage_hom.comp (J := J) (refinement_stage_hom_refl (J := J) A) h = h := by
  cases h with
  | mk k hT solved_mono =>
      simp [comp, refinement_stage_hom_refl, compose_refinement_iso,
        compose_refinement_embedding, identity_refinement_iso]
      constructor
      · ext i
        rfl
      · ext X
        simp [Functor.associator]

/-- Helper for Lemma 7.39.2: composition of packaged stage morphisms is associative. -/
theorem comp_assoc
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B D E : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hAB : refinement_stage_hom (J := J) A B)
    (hBD : refinement_stage_hom (J := J) B D)
    (hDE : refinement_stage_hom (J := J) D E) :
    refinement_stage_hom.comp (J := J) (refinement_stage_hom.comp (J := J) hAB hBD) hDE =
      refinement_stage_hom.comp (J := J) hAB
        (refinement_stage_hom.comp (J := J) hBD hDE) := by
  cases hAB with
  | mk kAB hTAB solvedAB =>
  cases hBD with
  | mk kBD hTBD solvedBD =>
  cases hDE with
  | mk kDE hTDE solvedDE =>
      simp [comp, compose_refinement_iso, compose_refinement_embedding]
      ext X
      simp [Functor.associator]

/-- Helper for Lemma 7.39.2: if a stage morphism is compatible with the recorded refinement from
the original inverse system, then the target stage's original map on presheaf fibers is the source
stage's original map followed by the morphism-induced map. This is the coherence form consumed by
direct-union separation arguments. -/
theorem original_compatible_presheafFiber_app
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A B)
    (hc : h.original_compatible)
    (F : Cᵒᵖ ⥤ Type (max u v w)) :
    ((refinementFiber B.j B.T B.e).presheafFiber).app F =
      ((refinementFiber A.j A.T A.e).presheafFiber).app F ≫
        ((refinementFiber h.k B.T h.hT).presheafFiber).app F := by
  cases B with
  | mk I instPreorder instDirected T j e separated solved solved_realized =>
      change ((refinementFiber j T e).presheafFiber).app F =
        ((refinementFiber A.j A.T A.e).presheafFiber).app F ≫
          ((refinementFiber h.k T h.hT).presheafFiber).app F
      rcases hc with ⟨hj, he⟩
      rw [show ((refinementFiber A.j A.T A.e).presheafFiber).app F ≫
            ((refinementFiber h.k T h.hT).presheafFiber).app F =
          (((refinementFiber A.j A.T A.e).presheafFiber ≫
            (refinementFiber h.k T h.hT).presheafFiber).app F) by rfl]
      have hcomp :
          ((refinementFiber (compose_refinement_embedding A.j h.k) T
              (compose_refinement_iso A.j h.k A.e h.hT)).presheafFiber).app F =
            ((refinementFiber A.j A.T A.e).presheafFiber ≫
              (refinementFiber h.k T h.hT).presheafFiber).app F := by
        calc
          ((refinementFiber (compose_refinement_embedding A.j h.k) T
              (compose_refinement_iso A.j h.k A.e h.hT)).presheafFiber).app F =
              ((refinementFiber A.j A.T A.e ≫ refinementFiber h.k T h.hT).presheafFiber).app
                F := by
                  simpa using congrArg (fun η => η.presheafFiber.app F)
                    (GrothendieckTopology.Point.ofIsCofiltered.refinementFiber_comp
                      A.j h.k A.e h.hT)
          _ = ((refinementFiber A.j A.T A.e).presheafFiber ≫
                (refinementFiber h.k T h.hT).presheafFiber).app F := by
                  simpa using refinementFiber_presheafFiber_app_comp
                    (j := A.j) (k := h.k) (e := A.e) (e' := h.hT) F
      rw [← hcomp]
      exact refinementFiber_presheafFiber_app_heq T hj he F

/-- Helper for Lemma 7.39.2: compatibility with the original refinement data is preserved by
composition of packaged stage morphisms. This is the coherence rule needed for directed diagrams
of refinement stages. -/
theorem original_compatible_comp
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B D : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hAB : refinement_stage_hom (J := J) A B)
    (hBD : refinement_stage_hom (J := J) B D)
    (hcAB : hAB.original_compatible)
    (hcBD : hBD.original_compatible) :
    (refinement_stage_hom.comp (J := J) hAB hBD).original_compatible := by
  rcases hcAB with ⟨hjAB, heAB⟩
  rcases hcBD with ⟨hjBD, heBD⟩
  let Φ :
      (Σ j : ι ↪o B.I, S' ≅ (j.toOrderHom.toFunctor).op ⋙ B.T) →
        (Σ j : ι ↪o D.I, S' ≅ (j.toOrderHom.toFunctor).op ⋙ D.T) :=
    fun p => ⟨compose_refinement_embedding p.1 hBD.k,
      compose_refinement_iso p.1 hBD.k p.2 hBD.hT⟩
  have hpAB :
      (⟨B.j, B.e⟩ :
        Σ j : ι ↪o B.I, S' ≅ (j.toOrderHom.toFunctor).op ⋙ B.T) =
      ⟨compose_refinement_embedding A.j hAB.k,
        compose_refinement_iso A.j hAB.k A.e hAB.hT⟩ := by
    exact Sigma.ext hjAB heAB
  have hpBD :
      (⟨D.j, D.e⟩ :
        Σ j : ι ↪o D.I, S' ≅ (j.toOrderHom.toFunctor).op ⋙ D.T) =
      ⟨compose_refinement_embedding B.j hBD.k,
        compose_refinement_iso B.j hBD.k B.e hBD.hT⟩ := by
    exact Sigma.ext hjBD heBD
  have hstep :
      (⟨compose_refinement_embedding B.j hBD.k,
        compose_refinement_iso B.j hBD.k B.e hBD.hT⟩ :
        Σ j : ι ↪o D.I, S' ≅ (j.toOrderHom.toFunctor).op ⋙ D.T) =
      ⟨compose_refinement_embedding (compose_refinement_embedding A.j hAB.k) hBD.k,
        compose_refinement_iso (compose_refinement_embedding A.j hAB.k) hBD.k
          (compose_refinement_iso A.j hAB.k A.e hAB.hT) hBD.hT⟩ := by
    simpa [Φ] using congrArg Φ hpAB
  have hassoc :
      (⟨compose_refinement_embedding (compose_refinement_embedding A.j hAB.k) hBD.k,
        compose_refinement_iso (compose_refinement_embedding A.j hAB.k) hBD.k
          (compose_refinement_iso A.j hAB.k A.e hAB.hT) hBD.hT⟩ :
        Σ j : ι ↪o D.I, S' ≅ (j.toOrderHom.toFunctor).op ⋙ D.T) =
      ⟨compose_refinement_embedding A.j (compose_refinement_embedding hAB.k hBD.k),
        compose_refinement_iso A.j (compose_refinement_embedding hAB.k hBD.k) A.e
          (compose_refinement_iso hAB.k hBD.k hAB.hT hBD.hT)⟩ := by
    apply Sigma.ext
    · ext i
      rfl
    · apply heq_of_eq
      ext X
      simp [compose_refinement_iso, compose_refinement_embedding, Functor.associator]
  have hp :
      (⟨D.j, D.e⟩ :
        Σ j : ι ↪o D.I, S' ≅ (j.toOrderHom.toFunctor).op ⋙ D.T) =
      ⟨compose_refinement_embedding A.j
          (refinement_stage_hom.comp (J := J) hAB hBD).k,
        compose_refinement_iso A.j
          (refinement_stage_hom.comp (J := J) hAB hBD).k A.e
          (refinement_stage_hom.comp (J := J) hAB hBD).hT⟩ := by
    simpa [refinement_stage_hom.comp] using hpBD.trans (hstep.trans hassoc)
  constructor
  · exact congrArg Sigma.fst hp
  · exact ((Sigma.mk.inj_iff).1 hp).2

end refinement_stage_hom

/-- Helper for Lemma 7.39.2: packaged refinement stages are ordered by existence of a stage
morphism. -/
instance refinement_stage_preorder
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ} :
    Preorder (refinement_stage (J := J) S' (ℱ := ℱ) s s') where
  le A B := Nonempty (refinement_stage_hom (J := J) A B)
  le_refl A := by
    -- Every stage refines itself by the identity stage morphism.
    exact ⟨refinement_stage_hom_refl (J := J) A⟩
  le_trans A B D hAB hBD := by
    rcases hAB with ⟨hAB⟩
    rcases hBD with ⟨hBD⟩
    -- Compose the two refinement morphisms to obtain the transitive comparison.
    exact ⟨refinement_stage_hom.comp (J := J) hAB hBD⟩

/-- Helper for Lemma 7.39.2: any two members of a chain admit a common successor inside the
same chain. -/
theorem chain_common_successor
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {c : Set (refinement_stage (J := J) S' (ℱ := ℱ) s s')}
    (_hcne : c.Nonempty) (hchain : IsChain (· ≤ ·) c)
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A ∈ c) (hB : B ∈ c) :
    ∃ D ∈ c,
      Nonempty (refinement_stage_hom (J := J) A D) ∧
        Nonempty (refinement_stage_hom (J := J) B D) := by
  -- In a chain, either `A ≤ B` or `B ≤ A`; choose the later stage as the common successor.
  rcases hchain.total hA hB with hAB | hBA
  · refine ⟨B, hB, hAB, ?_⟩
    -- The later stage always maps to itself by the identity stage morphism.
    exact ⟨refinement_stage_hom_refl (J := J) B⟩
  · refine ⟨A, hA, ?_, hBA⟩
    -- Symmetrically, if `B ≤ A`, then `A` is the common successor.
    exact ⟨refinement_stage_hom_refl (J := J) A⟩

namespace refinement_stage_hom

/-- Helper for Lemma 7.39.2: if a request is already marked solved on a stage, then after
transporting it along any stage morphism it is realized on the target stage. -/
theorem map_request_realized_of_mem_solved
    {S' : ιᵒᵖ ⥤ C}
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A B)
    {r : finite_cover_lift_request J A.T} (hr : r ∈ A.solved) :
    request_realized (J := J) (h.map_request r) := by
  -- First transport solvedness along the stage morphism, then use the target-stage invariant.
  exact B.solved_realized (h.solved_mono hr)

end refinement_stage_hom

-- Proof sketch: repackage the one-step extension theorem at the level of packaged stages by
-- transporting the previously solved requests to the larger stage and adding the new request.
/-- Helper for Lemma 7.39.2: extend a packaged stage by one additional request while preserving
all previously solved requests. -/
theorem extend_stage_by_request
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (r : finite_cover_lift_request J A.T) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.map_request r ∈ B.solved ∧
          B.j = compose_refinement_embedding A.j h.k ∧
          HEq B.e (compose_refinement_iso A.j h.k A.e h.hT) := by
  let Fobj : Cᵒᵖ ⥤ Type (max u v w) := (sheafToPresheaf J (Type (max u v w))).obj ℱ
  let sA := ((refinementFiber A.j A.T A.e).presheafFiber).app Fobj s
  let sA' := ((refinementFiber A.j A.T A.e).presheafFiber).app Fobj s'
  have hAsep : sA ≠ sA' := by
    -- The current stage already separates the transported images of `s` and `s'`.
    simpa [sA, sA', Fobj] using A.separated
  rcases stage_extend_by_request (J := J) A.T (ℱ := ℱ) (s := sA) (s' := sA') hAsep r with
    ⟨I', hI', hdir', U, k, e', hsep, hsolve⟩
  let B : refinement_stage (J := J) S' (ℱ := ℱ) s s' := {
    I := I'
    instPreorder := hI'
    instDirected := hdir'
    T := U
    j := compose_refinement_embedding A.j k
    e := compose_refinement_iso A.j k A.e e'
    separated := by
      -- Route correction: the successor stage separates `s` and `s'` through the composed
      -- refinement, so we normalize that composite map before applying the one-step result.
      have hsepMap :
          ((refinementFiber (compose_refinement_embedding A.j k) U
              (compose_refinement_iso A.j k A.e e')).presheafFiber).app Fobj =
            ((refinementFiber A.j A.T A.e).presheafFiber).app Fobj ≫
              ((refinementFiber k U e').presheafFiber).app Fobj := by
        calc
          ((refinementFiber (compose_refinement_embedding A.j k) U
              (compose_refinement_iso A.j k A.e e')).presheafFiber).app Fobj =
              ((refinementFiber A.j A.T A.e ≫ refinementFiber k U e').presheafFiber).app
                Fobj := by
                  simpa using congrArg (fun η => η.presheafFiber.app Fobj)
                    (GrothendieckTopology.Point.ofIsCofiltered.refinementFiber_comp
                      A.j k A.e e')
          _ = ((refinementFiber A.j A.T A.e).presheafFiber ≫
                (refinementFiber k U e').presheafFiber).app Fobj := by
                  simpa using refinementFiber_presheafFiber_app_comp
                    (j := A.j) (k := k) (e := A.e) (e' := e') Fobj
          _ = ((refinementFiber A.j A.T A.e).presheafFiber).app Fobj ≫
                ((refinementFiber k U e').presheafFiber).app Fobj := by
                  rfl
      intro hEq
      have hEq' :
          ((refinementFiber k U e').presheafFiber).app Fobj sA =
            ((refinementFiber k U e').presheafFiber).app Fobj sA' := by
        have hEqMap :
            ((((refinementFiber A.j A.T A.e).presheafFiber).app Fobj) ≫
                (((refinementFiber k U e').presheafFiber).app Fobj)) s =
              ((((refinementFiber A.j A.T A.e).presheafFiber).app Fobj) ≫
                (((refinementFiber k U e').presheafFiber).app Fobj)) s' := by
          -- Rewrite the composed refinement map into the normalized two-step composite.
          rw [← hsepMap]
          exact hEq
        simpa [sA, sA', Fobj] using hEqMap
      exact hsep hEq'
    solved :=
      {r' | ∃ r₀ : finite_cover_lift_request J A.T,
          r₀ ∈ A.solved ∧ transport_request (J := J) k U e' r₀ = r'} ∪
        {transport_request (J := J) k U e' r}
    solved_realized := by
      intro r' hr'
      rcases hr' with hr' | hr'
      · rcases hr' with ⟨r₀, hr₀, rfl⟩
        -- Previously solved requests stay realized after transporting them to the successor stage.
        exact request_realized_transport (J := J) k U e' r₀ (A.solved_realized hr₀)
      · rcases Set.mem_singleton_iff.mp hr' with rfl
        -- The new request is realized by the one-step extension theorem.
        simpa [request_solved_iff_request_realized_transport] using hsolve
  }
  refine ⟨B, ?_⟩
  let hnew : refinement_stage_hom (J := J) A B := {
    k := k
    hT := e'
    solved_mono := by
      intro r₀ hr₀
      -- By construction, all old solved requests are transported into the new solved set.
      exact Or.inl ⟨r₀, hr₀, rfl⟩
  }
  refine ⟨hnew, ?_⟩
  -- The chosen request is added to the solved set at the successor stage, and the target stage
  -- records the composed original refinement data.
  have he : HEq B.e (compose_refinement_iso A.j hnew.k A.e hnew.hT) := by
    dsimp [B, hnew]
    exact HEq.rfl
  exact ⟨Or.inr (Set.mem_singleton _), rfl, he⟩

/-- Helper for Lemma 7.39.2: one successor extension realizes the transported form of the
request used to build it. -/
theorem extend_stage_by_request_realizes
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (r : finite_cover_lift_request J A.T) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        request_realized (J := J) (h.map_request r) := by
  -- Package the one-step construction and then use the target stage's solved-request invariant.
  rcases extend_stage_by_request (J := J) A r with ⟨B, h, hr⟩
  exact ⟨B, h, B.solved_realized hr.1⟩

/-- Helper for Lemma 7.39.2: the one-step extension morphism returned by
`extend_stage_by_request` is compatible with the original-system refinement data. -/
theorem extend_stage_by_request_original_compatible
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (r : finite_cover_lift_request J A.T) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.map_request r ∈ B.solved ∧ h.original_compatible := by
  rcases extend_stage_by_request (J := J) A r with ⟨B, h, hsolved, hj, he⟩
  exact ⟨B, h, hsolved, hj, he⟩

/-- Helper for Lemma 7.39.2: once an earlier-stage request has been transported into the current
prefix stage, the successor constructor is just `extend_stage_by_request` on that transported
request. -/
noncomputable def next_stage_for_scheduled_request
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) (r : finite_cover_lift_request J A₀.T) :
    refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  Classical.choose <| extend_stage_by_request (J := J) L (h.map_request r)

/-- Helper for Lemma 7.39.2: the current prefix stage maps canonically into the successor stage
obtained by solving one transported request. -/
noncomputable def next_stage_for_scheduled_request_hom
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) (r : finite_cover_lift_request J A₀.T) :
    refinement_stage_hom (J := J) L (next_stage_for_scheduled_request (J := J) A₀ L h r) :=
  Classical.choose <| Classical.choose_spec (extend_stage_by_request (J := J) L (h.map_request r))

/-- Helper for Lemma 7.39.2: the successor stage obtained by solving a transported request has
the original refinement embedding obtained by composing the current stage embedding with the
successor morphism. -/
theorem next_stage_for_scheduled_request_j
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) (r : finite_cover_lift_request J A₀.T) :
    (next_stage_for_scheduled_request (J := J) A₀ L h r).j =
      compose_refinement_embedding L.j
        (next_stage_for_scheduled_request_hom (J := J) A₀ L h r).k := by
  -- Unpack the compatibility field recorded by `extend_stage_by_request`.
  exact (Classical.choose_spec <|
    Classical.choose_spec (extend_stage_by_request (J := J) L (h.map_request r))).2.1

/-- Helper for Lemma 7.39.2: the successor stage obtained by solving a transported request has
the original refinement iso obtained, up to dependent equality, by composing the current stage iso
with the successor morphism iso. -/
theorem next_stage_for_scheduled_request_e_heq
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) (r : finite_cover_lift_request J A₀.T) :
    HEq (next_stage_for_scheduled_request (J := J) A₀ L h r).e
      (compose_refinement_iso L.j
        (next_stage_for_scheduled_request_hom (J := J) A₀ L h r).k L.e
        (next_stage_for_scheduled_request_hom (J := J) A₀ L h r).hT) := by
  -- Unpack the dependent iso compatibility recorded by `extend_stage_by_request`.
  exact (Classical.choose_spec <|
    Classical.choose_spec (extend_stage_by_request (J := J) L (h.map_request r))).2.2

/-- Helper for Lemma 7.39.2: the successor morphism produced by
`next_stage_for_scheduled_request` is compatible with the original-system refinement data. -/
theorem next_stage_for_scheduled_request_original_compatible
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) (r : finite_cover_lift_request J A₀.T) :
    (next_stage_for_scheduled_request_hom (J := J) A₀ L h r).original_compatible := by
  exact ⟨next_stage_for_scheduled_request_j (J := J) A₀ L h r,
    next_stage_for_scheduled_request_e_heq (J := J) A₀ L h r⟩

/-- Helper for Lemma 7.39.2: the scheduled request is solved at the successor stage produced from
the current prefix stage. -/
theorem next_stage_for_scheduled_request_solved
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) (r : finite_cover_lift_request J A₀.T) :
    (next_stage_for_scheduled_request_hom (J := J) A₀ L h r).map_request (h.map_request r) ∈
      (next_stage_for_scheduled_request (J := J) A₀ L h r).solved := by
  -- Unpack the witness returned by `extend_stage_by_request` for the transported request.
  exact (Classical.choose_spec <|
    Classical.choose_spec (extend_stage_by_request (J := J) L (h.map_request r))
  ).1

/-- Helper for Lemma 7.39.2: after solving a scheduled request at the successor stage, the
request is realized after the composed map from the original stage to that successor. -/
theorem next_stage_for_scheduled_request_comp_realized
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) (r : finite_cover_lift_request J A₀.T) :
    request_realized (J := J)
      ((refinement_stage_hom.comp (J := J) h
        (next_stage_for_scheduled_request_hom (J := J) A₀ L h r)).map_request r) := by
  -- First use the successor stage's solved-set invariant, then rewrite the two-step map as one
  -- composed stage morphism.
  have hsolved :
      request_realized (J := J)
        ((next_stage_for_scheduled_request_hom (J := J) A₀ L h r).map_request
          (h.map_request r)) :=
    (next_stage_for_scheduled_request (J := J) A₀ L h r).solved_realized
      (next_stage_for_scheduled_request_solved (J := J) A₀ L h r)
  simpa [refinement_stage_hom.map_request_comp] using hsolved

/-- Helper for Lemma 7.39.2: any single finite-cover request from the original inverse system can
be realized after a further refinement of an arbitrary packaged stage, once the request is
transported to that stage. This is the successor step in the source-facing Zorn/transfinite
construction of Stacks tag `00YP`. -/
theorem exists_stage_hom_realizing_one_source_request
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (r : finite_cover_lift_request J S') :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        request_realized (J := J)
          (h.map_request (transport_request (J := J) A.j A.T A.e r)) := by
  rcases extend_stage_by_request_realizes (J := J) A
      (transport_request (J := J) A.j A.T A.e r) with
    ⟨B, h, hreal⟩
  exact ⟨B, h, hreal⟩

/-- Helper for Lemma 7.39.2: if a packaged refinement stage realizes every request on its own
fiber functor, then that stage already supplies the theorem's final refinement. -/
theorem stage_realizing_all_requests_yields_target
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hA : ∀ r : finite_cover_lift_request J A.T, request_realized (J := J) r) :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      let u := fiber.{max u v w} T
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{w} W) [Finite 𝒰.index]
          (h𝒰 : 𝒰.toSieve ∈ J W) (f : u.obj W),
            ∃ i : 𝒰.index, ∃ y : u.obj (𝒰.obj i).left, u.map (𝒰.obj i).hom y = f := by
  refine ⟨A.I, inferInstance, inferInstance, A.T, A.j, A.e, ?_⟩
  refine ⟨A.separated, ?_⟩
  intro W 𝒰 _ h𝒰 f
  -- First replace the arbitrary finite family by its equivalent `Fin n`-indexed presentation,
  -- then package that final-stage lifting problem as one scheduled request.
  let 𝒰fin : SemiRepresentableFamily.Over.{0} W := 𝒰.finReindex
  letI : Finite 𝒰fin.index := by
    dsimp [𝒰fin, SemiRepresentableFamily.Over.finReindex]
    infer_instance
  have h𝒰fin : 𝒰fin.toSieve ∈ J W := by
    simpa [𝒰fin, SemiRepresentableFamily.Over.finReindex_toSieve] using h𝒰
  let r : finite_cover_lift_request J A.T := {
    W := W
    n := Nat.card 𝒰.index
    obj := fun i => 𝒰.obj ((Finite.equivFin 𝒰.index).symm i)
    h𝒰 := h𝒰fin
    f := f
  }
  rcases hA r with ⟨i, y, hy⟩
  refine ⟨(Finite.equivFin 𝒰.index).symm i, y, ?_⟩
  simpa [r, request_realized, 𝒰fin, SemiRepresentableFamily.Over.finReindex] using hy

/-- Helper for Lemma 7.39.2: if a packaged stage realizes every finite-cover request from the
original system after transport, then it supplies the source-facing target of Stacks tag `00YP`.
This is the exact bridge for the textbook statement, where the element starts in `u'(W)` and is
then mapped to the refined functor. -/
theorem stage_realizing_source_requests_yields_source_target
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hA : ∀ r : finite_cover_lift_request J S',
      request_realized (J := J) (transport_request (J := J) A.j A.T A.e r)) :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      let u := fiber.{max u v w} T
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{w} W) [Finite 𝒰.index]
          (h𝒰 : 𝒰.toSieve ∈ J W) (f : (fiber.{max u v w} S').obj W),
            ∃ i : 𝒰.index, ∃ y : u.obj (𝒰.obj i).left,
              u.map (𝒰.obj i).hom y = (refinementFiber j T e).app W f := by
  refine ⟨A.I, inferInstance, inferInstance, A.T, A.j, A.e, ?_⟩
  refine ⟨A.separated, ?_⟩
  intro W 𝒰 _ h𝒰 f
  -- Reindex the finite cover by `Fin n`, then package the original-system lifting request.
  let 𝒰fin : SemiRepresentableFamily.Over.{0} W := 𝒰.finReindex
  letI : Finite 𝒰fin.index := by
    dsimp [𝒰fin, SemiRepresentableFamily.Over.finReindex]
    infer_instance
  have h𝒰fin : 𝒰fin.toSieve ∈ J W := by
    simpa [𝒰fin, SemiRepresentableFamily.Over.finReindex_toSieve] using h𝒰
  let r : finite_cover_lift_request J S' := {
    W := W
    n := Nat.card 𝒰.index
    obj := fun i => 𝒰.obj ((Finite.equivFin 𝒰.index).symm i)
    h𝒰 := h𝒰fin
    f := f
  }
  -- The stage hypothesis realizes the transported request, which is exactly the desired image.
  rcases hA r with ⟨i, y, hy⟩
  refine ⟨(Finite.equivFin 𝒰.index).symm i, y, ?_⟩
  simpa [r, request_realized, transport_request, 𝒰fin,
    SemiRepresentableFamily.Over.finReindex] using hy


end

end CategoryTheory
