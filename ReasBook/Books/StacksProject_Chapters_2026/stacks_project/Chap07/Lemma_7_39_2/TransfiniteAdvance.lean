module

public import stacks_project.Chap07.Lemma_7_39_2.RequestScheduling
public import stacks_project.Chap07.Lemma_7_39_2.PackagedStages
public import stacks_project.Chap07.Lemma_7_39_2.FiniteFrontier
public import stacks_project.Chap07.Lemma_7_39_2.OmegaSystem
public import stacks_project.Chap07.Lemma_7_39_2.DiagramUnionCore
public import stacks_project.Chap07.Lemma_7_39_2.DiagramUnionLimit
public import stacks_project.Chap07.NaturalDiagramUnion
public import stacks_project.Chap07.Lemma_7_39_2.OmegaTerminal
public import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData

@[expose] public section

/-
Transfinite-recursion endgame for Lemma 7.39.2.

This module closes the one remaining gap in `Lemma_7_39_2.lean`, namely
`exists_terminal_refinement_stage_realizing_all_requests`.  The architecture:

* `advance_compatible` (THE KERNEL): for any packaged stage `A`, a single further
  *compatible* refinement realizing every finite-cover request of `A.T`.  This is the
  inner transfinite recursion over the (`UnivLE`-small) well-ordered set of requests of
  one fixed stage.
* the outer `ℕ`-tower: iterate `advance_compatible`, take the directed union over
  `δ = ULift.{w} ℕ`, and read off separation + realization from the already-proven
  `refinementStageDiagramLimitStage_separated_of_compatible` and
  `refinementStageDiagramLimitStage_realizes_all_requests_of_eventually`.

The `[UnivLE.{max u v w, w}]` hypothesis is harmless downstream: at the only call site
(Proposition 7.39.3) the stage universe `w` equals `max u v`, so it is discharged
automatically.
-/

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over
open GrothendieckTopology.Point.ofIsCofiltered

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

variable {J : GrothendieckTopology C}
variable {ι : Type w} [Preorder ι]

section

/-- The composite `omegaStageHomLE` is compatible with the original refinement data whenever
every successor step is. -/
theorem omegaStageHomLE_original_compatible
    {ℱ : Sheaf J (Type (max u v w))} {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (hstep : ∀ n, (step n).original_compatible)
    {n m : ℕ} (h : n ≤ m) :
    (omegaStageHomLE (J := J) A step h).original_compatible := by
  induction m, h using Nat.le_induction with
  | base =>
      rw [omegaStageHomLE_self_eq (J := J) A step (le_rfl)]
      exact refinement_stage_hom.original_compatible_refl (J := J) (A n)
  | succ m hm ih =>
      rw [omegaStageHomLE_succ_eq_comp (J := J) A step hm]
      exact refinement_stage_hom.original_compatible_comp (J := J)
        (omegaStageHomLE (J := J) A step hm) (step m) ih (hstep m)

variable {ℱ : Sheaf J (Type (max u v w))} {S' : ιᵒᵖ ⥤ C}
  {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
    (fiber.{max u v w} S').presheafFiber).obj ℱ}

/-- Helper for Lemma 7.39.2: model the requests of one fixed packaged stage in the stage
universe, so the transfinite saturation can be indexed by a `Type w`. -/
private abbrev stageRequestSchedule [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') : Type w :=
  Shrink.{w} (finite_cover_lift_request J A.T)

/-- Helper for Lemma 7.39.2: decode one stage-universe request schedule entry back to the
actual finite-cover request on the fixed stage. -/
private noncomputable def requestOfStageSchedule [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    stageRequestSchedule (J := J) A → finite_cover_lift_request J A.T :=
  (equivShrink (finite_cover_lift_request J A.T)).symm

/-- Helper for Lemma 7.39.2: every actual request of the fixed stage occurs in the
stage-universe schedule. -/
private theorem requestOfStageSchedule_surjective [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    Function.Surjective (requestOfStageSchedule (J := J) A) := by
  intro r
  -- The shrink equivalence gives a code for each original request and decodes it back exactly.
  refine ⟨(equivShrink (finite_cover_lift_request J A.T)) r, ?_⟩
  simp [requestOfStageSchedule]

/-- Helper for Lemma 7.39.2: transport a packaged refinement-stage morphism along equalities
of its source and target stages. -/
private noncomputable def refinementStageHomCast
    {A A' B B' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') (hB : B = B')
    (f : refinement_stage_hom (J := J) A' B') :
    refinement_stage_hom (J := J) A B :=
  match hA, hB with
  | rfl, rfl => f

/-- Helper for Lemma 7.39.2: transporting a morphism along reflexive endpoint equalities is
definitionally the original morphism. -/
private theorem refinementStageHomCast_rfl
    {A B : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (f : refinement_stage_hom (J := J) A B) :
    refinementStageHomCast (J := J) (rfl : A = A) (rfl : B = B) f = f := by
  -- Reflexive endpoint transports reduce directly to the original morphism.
  rfl

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: transporting an identity morphism
along the same endpoint equality gives the identity at the transported endpoint. -/
private theorem refinementStageHomCast_refl
    {A A' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') :
    refinementStageHomCast (J := J) hA hA
        (refinement_stage_hom_refl (J := J) A') =
      refinement_stage_hom_refl (J := J) A := by
  -- Once the endpoint equality is reflexive, the transported identity is definitionally the
  -- identity morphism on the same stage.
  subst hA
  rfl

/-- Helper for Lemma 7.39.2: original-system compatibility is preserved by endpoint transport
of packaged refinement-stage morphisms. -/
private theorem refinementStageHomCast_original_compatible
    {A A' B B' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') (hB : B = B')
    (f : refinement_stage_hom (J := J) A' B') (hf : f.original_compatible) :
    (refinementStageHomCast (J := J) hA hB f).original_compatible := by
  -- Reduce endpoint equalities to reflexivity, where the transported morphism is just `f`.
  subst hA
  subst hB
  exact hf

/-- Helper for Lemma 7.39.2: endpoint transport commutes with composition of packaged
refinement-stage morphisms. -/
private theorem refinementStageHomCast_comp
    {A A' B B' D D' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') (hB : B = B') (hD : D = D')
    (f : refinement_stage_hom (J := J) A' B')
    (g : refinement_stage_hom (J := J) B' D') :
    refinementStageHomCast (J := J) hA hD (refinement_stage_hom.comp (J := J) f g) =
      refinement_stage_hom.comp (J := J)
        (refinementStageHomCast (J := J) hA hB f)
        (refinementStageHomCast (J := J) hB hD g) := by
  -- After replacing all endpoint equalities by reflexivity, both sides are the same composite.
  subst hA
  subst hB
  subst hD
  rfl

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the same endpoint-transport
composition law in the rewrite direction needed when normalizing composites of branch-defined
successor maps. -/
private theorem refinementStageHomCast_comp_reverse
    {A A' B B' D D' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') (hB : B = B') (hD : D = D')
    (f : refinement_stage_hom (J := J) A' B')
    (g : refinement_stage_hom (J := J) B' D') :
    refinement_stage_hom.comp (J := J)
        (refinementStageHomCast (J := J) hA hB f)
        (refinementStageHomCast (J := J) hB hD g) =
      refinementStageHomCast (J := J) hA hD
        (refinement_stage_hom.comp (J := J) f g) := by
  -- This is just the symmetric orientation of `refinementStageHomCast_comp`, recorded so later
  -- successor-field proofs can rewrite branch composites toward the old prefix-system law.
  exact (refinementStageHomCast_comp (J := J) hA hB hD f g).symm

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: composing a casted morphism with a
casted target identity collapses back to the casted morphism. -/
private theorem refinementStageHomCast_comp_refl_right
    {A A' B B' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') (hB : B = B')
    (f : refinement_stage_hom (J := J) A' B') :
    refinement_stage_hom.comp (J := J)
        (refinementStageHomCast (J := J) hA hB f)
        (refinementStageHomCast (J := J) hB hB
          (refinement_stage_hom_refl (J := J) B')) =
      refinementStageHomCast (J := J) hA hB f := by
  -- Once endpoints are identified, this is the ordinary right identity law for packaged stage
  -- morphisms.
  subst hA
  subst hB
  exact refinement_stage_hom.comp_refl (J := J) f

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: composing a casted source identity
with a casted morphism collapses back to the casted morphism. -/
private theorem refinementStageHomCast_refl_comp_left
    {A A' B B' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') (hB : B = B')
    (f : refinement_stage_hom (J := J) A' B') :
    refinement_stage_hom.comp (J := J)
        (refinementStageHomCast (J := J) hA hA
          (refinement_stage_hom_refl (J := J) A'))
        (refinementStageHomCast (J := J) hA hB f) =
      refinementStageHomCast (J := J) hA hB f := by
  -- Once endpoints are identified, this is the ordinary left identity law for packaged stage
  -- morphisms.
  subst hA
  subst hB
  exact refinement_stage_hom.refl_comp (J := J) f

/-- Helper for Lemma 7.39.2: endpoint transport respects equality of packaged
refinement-stage morphisms. -/
private theorem refinementStageHomCast_congr
    {A A' B B' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') (hB : B = B')
    {f g : refinement_stage_hom (J := J) A' B'} (hfg : f = g) :
    refinementStageHomCast (J := J) hA hB f =
      refinementStageHomCast (J := J) hA hB g := by
  -- Congruence follows by first identifying the source morphisms.
  subst hfg
  rfl

/-- Helper for Lemma 7.39.2: endpoint transport of a refinement-stage morphism is independent
of the particular proof terms used for the endpoint equalities. -/
private theorem refinementStageHomCast_congr_proof
    {A A' B B' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    {hA hA' : A = A'} {hB hB' : B = B'}
    {f g : refinement_stage_hom (J := J) A' B'} (hfg : f = g) :
    refinementStageHomCast (J := J) hA hB f =
      refinementStageHomCast (J := J) hA' hB' g := by
  -- Reduce one set of endpoint equalities to reflexivity, then proof irrelevance removes the
  -- remaining equality-proof choices.
  subst hA
  subst hB
  subst hfg
  rfl

/-- Helper for Lemma 7.39.2: endpoint transport respects heterogeneous equality of packaged
stage morphisms. -/
private theorem refinementStageHomCast_congr_heq
    {A A' A'' B B' B'' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') (hB : B = B') (hA' : A = A'') (hB' : B = B'')
    {f : refinement_stage_hom (J := J) A' B'}
    {g : refinement_stage_hom (J := J) A'' B''} (hfg : HEq f g) :
    refinementStageHomCast (J := J) hA hB f =
      refinementStageHomCast (J := J) hA' hB' g := by
  -- Reduce all endpoint transports to reflexivity; the heterogeneous equality then becomes an
  -- ordinary equality of morphisms.
  cases hA
  cases hB
  cases hA'
  cases hB'
  cases hfg
  rfl

/-- Helper for Lemma 7.39.2: composing after endpoint transport on the middle object agrees
with composing the heterogeneously equal untransported left morphism. -/
private theorem refinementStageHomCast_comp_heq_left
    {A B B' D : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hB : B = B')
    {f : refinement_stage_hom (J := J) A B'}
    {f' : refinement_stage_hom (J := J) A B} (hf : HEq f f')
    (g : refinement_stage_hom (J := J) B' D) :
    refinement_stage_hom.comp (J := J) f'
        (refinementStageHomCast (J := J) hB rfl g) =
      refinement_stage_hom.comp (J := J) f g := by
  -- Once the middle endpoint is identified, the left morphisms have the same type and `hf`
  -- collapses the comparison to reflexivity.
  cases hB
  cases hf
  rfl

/-- Helper for Lemma 7.39.2: endpoint transport of a stage morphism transports mapped
finite-cover requests by the same endpoint equalities. -/
private theorem refinementStageHomCast_map_request_heq
    {A A' B B' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') (hB : B = B')
    (f : refinement_stage_hom (J := J) A' B')
    (r : finite_cover_lift_request J A.T)
    (r' : finite_cover_lift_request J A'.T) (hr : HEq r r') :
    HEq ((refinementStageHomCast (J := J) hA hB f).map_request r)
      (f.map_request r') := by
  -- Once both endpoint transports and the request transport are reflexive, the mapped requests
  -- are judgmentally identical.
  subst hA
  subst hB
  cases hr
  rfl

/-- Helper for Lemma 7.39.2: endpoint transport of a packaged refinement-stage morphism is
heterogeneously equal to the original morphism. -/
private theorem refinementStageHomCast_heq
    {A A' B B' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') (hB : B = B')
    (f : refinement_stage_hom (J := J) A' B') :
    HEq (refinementStageHomCast (J := J) hA hB f) f := by
  -- After identifying both transported endpoints, the casted morphism is the original one.
  subst hA
  subst hB
  rfl

/-- Helper for Lemma 7.39.2: realization of finite-cover requests is invariant under
heterogeneous equality of the request data. -/
private theorem requestRealized_of_heq
    {T T' : ιᵒᵖ ⥤ C} (hT : T = T')
    {r : finite_cover_lift_request J T}
    {r' : finite_cover_lift_request J T'} (hr : HEq r r') :
    request_realized (J := J) r → request_realized (J := J) r' := by
  -- First identify the request functors; the remaining heterogeneous request equality is
  -- ordinary proof transport of the same realization predicate.
  subst hT
  cases hr
  exact id

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: realization of a request transported
by an endpoint-cast morphism is the same as realization after the original morphism. -/
private theorem refinementStageHomCast_map_request_realized
    {A A' B B' : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA : A = A') (hB : B = B')
    (f : refinement_stage_hom (J := J) A' B')
    (r : finite_cover_lift_request J A.T)
    (r' : finite_cover_lift_request J A'.T) (hr : HEq r r') :
    request_realized (J := J) (f.map_request r') →
      request_realized (J := J)
        ((refinementStageHomCast (J := J) hA hB f).map_request r) := by
  -- Replace the endpoint equalities first; the casted morphism and heterogeneous source request
  -- then reduce to the original realized request.
  intro hreal
  subst hA
  subst hB
  cases hr
  exact hreal

/-- Helper for Lemma 7.39.2: predecessor cuts in `WithTop` over a linearly ordered request
schedule are directed by taking the maximum of two predecessors. -/
private theorem withTopPredecessorCutDirected {α : Type w} [LinearOrder α] (a : WithTop α) :
    IsDirected {b : WithTop α // b < a} (· ≤ ·) where
  directed x y := by
    -- The maximum of two elements below the cut is still below the cut and dominates both.
    refine ⟨⟨max x.1 y.1, ?_⟩, ?_, ?_⟩
    · exact max_lt x.2 y.2
    · exact le_max_left _ _
    · exact le_max_right _ _

/-- Helper for Lemma 7.39.2: the predecessor cuts of the well-ordered stage request schedule are
directed, which is the order-theoretic input needed by the direct-union limit stage. -/
private theorem stageRequestScheduleCutDirected [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (a : WithTop (stageRequestSchedule (J := J) A)) :
    letI : LinearOrder (stageRequestSchedule (J := J) A) :=
      IsWellOrder.linearOrder WellOrderingRel
    IsDirected {b : WithTop (stageRequestSchedule (J := J) A) // b < a} (· ≤ ·) := by
  letI : LinearOrder (stageRequestSchedule (J := J) A) :=
    IsWellOrder.linearOrder WellOrderingRel
  -- Reduce the scheduled cut to the generic `WithTop` predecessor-cut lemma.
  exact withTopPredecessorCutDirected a

/-- Helper for Lemma 7.39.2: a prefix stage at a cut in the well-ordered request schedule.
It asserts that some compatible refinement of the original packaged stage realizes every
scheduled request below the cut. -/
private def scheduledPrefixData [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (b : WithTop (stageRequestSchedule (J := J) A)) : Prop :=
  ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
    ∃ h : refinement_stage_hom (J := J) A B,
      h.original_compatible ∧
        ∀ a : stageRequestSchedule (J := J) A,
          (a : WithTop (stageRequestSchedule (J := J) A)) < b →
            request_realized (J := J) (h.map_request (requestOfStageSchedule (J := J) A a))

/-- Helper for Lemma 7.39.2: a coherent scheduled prefix system over all cuts below a fixed
cut.  It stores the prefix stages, transition morphisms, their coherence, the maps from the
fixed base stage, and the realization invariant at every stored cut. -/
private structure scheduledPrefixSystemData [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (b : WithTop (stageRequestSchedule (J := J) A)) where
  stage :
    {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'
  hom :
    ∀ ⦃c d : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b}⦄,
      (c : WithTop (stageRequestSchedule (J := J) A)) ≤ d →
        refinement_stage_hom (J := J) (stage c) (stage d)
  hom_refl :
    ∀ c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b},
      hom (show (c : WithTop (stageRequestSchedule (J := J) A)) ≤ c from le_rfl) =
        refinement_stage_hom_refl (J := J) (stage c)
  hom_comp :
    ∀ ⦃c d e : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b}⦄
      (hcd : (c : WithTop (stageRequestSchedule (J := J) A)) ≤ d)
      (hde : (d : WithTop (stageRequestSchedule (J := J) A)) ≤ e),
        hom (le_trans hcd hde) =
          refinement_stage_hom.comp (J := J) (hom hcd) (hom hde)
  hom_original_compatible :
    ∀ ⦃c d : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b}⦄
      (hcd : (c : WithTop (stageRequestSchedule (J := J) A)) ≤ d),
        (hom hcd).original_compatible
  fromBase :
    ∀ c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b},
      refinement_stage_hom (J := J) A (stage c)
  fromBase_compatible :
    ∀ c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b},
      (fromBase c).original_compatible
  fromBase_comp :
    ∀ ⦃c d : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b}⦄
      (hcd : (c : WithTop (stageRequestSchedule (J := J) A)) ≤ d),
        fromBase d = refinement_stage_hom.comp (J := J) (fromBase c) (hom hcd)
  realizes :
    ∀ (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b})
      (a : stageRequestSchedule (J := J) A),
        (a : WithTop (stageRequestSchedule (J := J) A)) < c →
          request_realized (J := J) ((fromBase c).map_request
            (requestOfStageSchedule (J := J) A a))

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: coherent scheduled prefix systems over
the same cut are equal once their stage, transition, and base-map data agree; the remaining
fields are proof irrelevant coherence witnesses. -/
private theorem scheduledPrefixSystemData_ext [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)}
    (D E : scheduledPrefixSystemData (J := J) A b)
    (hstage : D.stage = E.stage)
    (hhom : HEq D.hom E.hom)
    (hfromBase : HEq D.fromBase E.fromBase) :
    D = E := by
  -- Reduce the three data fields to reflexivity; the coherence and realization fields are
  -- propositions and disappear by proof irrelevance.
  cases D
  cases E
  cases hstage
  cases hhom
  cases hfromBase
  rfl

/-- Helper for Lemma 7.39.2: one coherent scheduled diagram over every cut in the request
schedule.  This is the global normal form needed at successor-limit cuts; it stores comparison
maps and base maps before any limit restriction is taken. -/
private structure scheduledGlobalDiagramData [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)] where
  stage :
    WithTop (stageRequestSchedule (J := J) A) →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'
  hom :
    ∀ ⦃b c : WithTop (stageRequestSchedule (J := J) A)⦄, b ≤ c →
      refinement_stage_hom (J := J) (stage b) (stage c)
  hom_refl :
    ∀ b : WithTop (stageRequestSchedule (J := J) A),
      hom (show b ≤ b from le_rfl) = refinement_stage_hom_refl (J := J) (stage b)
  hom_comp :
    ∀ ⦃b c d : WithTop (stageRequestSchedule (J := J) A)⦄
      (hbc : b ≤ c) (hcd : c ≤ d),
        hom (le_trans hbc hcd) =
          refinement_stage_hom.comp (J := J) (hom hbc) (hom hcd)
  hom_original_compatible :
    ∀ ⦃b c : WithTop (stageRequestSchedule (J := J) A)⦄ (hbc : b ≤ c),
      (hom hbc).original_compatible
  fromBase :
    ∀ b : WithTop (stageRequestSchedule (J := J) A),
      refinement_stage_hom (J := J) A (stage b)
  fromBase_compatible :
    ∀ b : WithTop (stageRequestSchedule (J := J) A),
      (fromBase b).original_compatible
  fromBase_comp :
    ∀ ⦃b c : WithTop (stageRequestSchedule (J := J) A)⦄ (hbc : b ≤ c),
      fromBase c = refinement_stage_hom.comp (J := J) (fromBase b) (hom hbc)
  realizes_lt :
    ∀ (b : WithTop (stageRequestSchedule (J := J) A))
      (a : stageRequestSchedule (J := J) A),
        (a : WithTop (stageRequestSchedule (J := J) A)) < b →
          request_realized (J := J) ((fromBase b).map_request
            (requestOfStageSchedule (J := J) A a))

/-- Helper for Lemma 7.39.2: a coherent scheduled prefix system restricts functorially to any
smaller closed schedule cut. -/
private noncomputable def scheduledPrefixSystemData_restrict [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)} (hcb : c ≤ b)
    (D : scheduledPrefixSystemData (J := J) A b) :
    scheduledPrefixSystemData (J := J) A c :=
  -- Reindex every node of the smaller closed cut as a node of the larger stored system.
  let lift :
      {d : WithTop (stageRequestSchedule (J := J) A) // d ≤ c} →
        {d : WithTop (stageRequestSchedule (J := J) A) // d ≤ b} :=
    fun d => ⟨d.1, le_trans d.2 hcb⟩
  { stage := fun d => D.stage (lift d)
    hom := fun {d e} hde => D.hom (c := lift d) (d := lift e) hde
    hom_refl := fun d => D.hom_refl (lift d)
    hom_comp := fun {d e f} hde hef =>
      D.hom_comp (c := lift d) (d := lift e) (e := lift f) hde hef
    hom_original_compatible := fun {d e} hde =>
      D.hom_original_compatible (c := lift d) (d := lift e) hde
    fromBase := fun d => D.fromBase (lift d)
    fromBase_compatible := fun d => D.fromBase_compatible (lift d)
    fromBase_comp := fun {d e} hde => D.fromBase_comp (c := lift d) (d := lift e) hde
    realizes := fun d a ha => D.realizes (lift d) a ha }

/-- Helper for Lemma 7.39.2: the transition map of a restricted scheduled prefix system is the
original transition map between the lifted closed-cut indices. -/
private theorem scheduledPrefixSystemData_restrict_hom_apply [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)} (hcb : c ≤ b)
    (D : scheduledPrefixSystemData (J := J) A b)
    {d e : {d : WithTop (stageRequestSchedule (J := J) A) // d ≤ c}}
    (hde : (d : WithTop (stageRequestSchedule (J := J) A)) ≤ e) :
    (scheduledPrefixSystemData_restrict (J := J) A hcb D).hom hde =
      D.hom (c := ⟨d.1, le_trans d.2 hcb⟩)
        (d := ⟨e.1, le_trans e.2 hcb⟩) hde := by
  -- The restricted comparison is definitionally the original comparison after lifting indices.
  rfl

/-- Helper for Lemma 7.39.2: restricting a scheduled prefix system to its own closed cut
returns the same prefix system. -/
private theorem scheduledPrefixSystemData_restrict_self [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)}
    (D : scheduledPrefixSystemData (J := J) A b) :
    scheduledPrefixSystemData_restrict (J := J) A (le_refl b) D = D := by
  -- The restriction only changes proof arguments in the closed-cut subtype.
  cases D
  rfl

/-- Helper for Lemma 7.39.2: two successive restrictions of a scheduled prefix system agree
with restriction by the composite closed-cut inequality. -/
private theorem scheduledPrefixSystemData_restrict_restrict [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (D : scheduledPrefixSystemData (J := J) A b) (hcb : c ≤ b) (hdc : d ≤ c) :
    scheduledPrefixSystemData_restrict (J := J) A hdc
        (scheduledPrefixSystemData_restrict (J := J) A hcb D) =
      scheduledPrefixSystemData_restrict (J := J) A (le_trans hdc hcb) D := by
  -- Both sides reindex the same stored data along proof-irrelevant closed-cut inequalities.
  cases D
  rfl

/-- Helper for Lemma 7.39.2: the stage field of a restricted scheduled prefix system is the
original stage at the reindexed closed cut. -/
private theorem scheduledPrefixSystemData_restrict_stage_apply [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)} (hcb : c ≤ b)
    (D : scheduledPrefixSystemData (J := J) A b)
    (d : {d : WithTop (stageRequestSchedule (J := J) A) // d ≤ c}) :
    (scheduledPrefixSystemData_restrict (J := J) A hcb D).stage d =
      D.stage ⟨d.1, le_trans d.2 hcb⟩ := by
  -- This projection lemma freezes the definitional reindexing used by restriction.
  rfl

/-- Helper for Lemma 7.39.2: the base map of a restricted scheduled prefix system is the
original base map at the reindexed closed cut. -/
private theorem scheduledPrefixSystemData_restrict_fromBase_apply [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)} (hcb : c ≤ b)
    (D : scheduledPrefixSystemData (J := J) A b)
    (d : {d : WithTop (stageRequestSchedule (J := J) A) // d ≤ c}) :
    (scheduledPrefixSystemData_restrict (J := J) A hcb D).fromBase d =
      D.fromBase ⟨d.1, le_trans d.2 hcb⟩ := by
  -- This keeps later base-map comparisons at the projection level instead of unfolding the
  -- whole restricted record.
  rfl

/-- Helper for Lemma 7.39.2: the whole transition-field of a restricted scheduled prefix system
is heterogeneously equal to the transition-field of the larger system on lifted indices. -/
private theorem scheduledPrefixSystemData_restrict_hom_heq [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)} (hcb : c ≤ b)
    (D : scheduledPrefixSystemData (J := J) A b) :
    HEq (scheduledPrefixSystemData_restrict (J := J) A hcb D).hom
      (fun {d e : {d : WithTop (stageRequestSchedule (J := J) A) // d ≤ c}}
          (hde : (d : WithTop (stageRequestSchedule (J := J) A)) ≤ e) =>
        D.hom (c := ⟨d.1, le_trans d.2 hcb⟩)
          (d := ⟨e.1, le_trans e.2 hcb⟩) hde) := by
  -- Restriction is defined by lifting both endpoints into the larger closed cut.
  rfl

/-- Helper for Lemma 7.39.2: the whole base-map field of a restricted scheduled prefix system
is heterogeneously equal to the base-map field of the larger system on lifted indices. -/
private theorem scheduledPrefixSystemData_restrict_fromBase_heq [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)} (hcb : c ≤ b)
    (D : scheduledPrefixSystemData (J := J) A b) :
    HEq (scheduledPrefixSystemData_restrict (J := J) A hcb D).fromBase
      (fun d : {d : WithTop (stageRequestSchedule (J := J) A) // d ≤ c} =>
        D.fromBase ⟨d.1, le_trans d.2 hcb⟩) := by
  -- The restricted base map is just the larger base map after closed-cut reindexing.
  rfl

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a restricted coherent scheduled prefix
system is equal to a target prefix system once the restricted stage, transition, and base-map
fields are identified. -/
private theorem scheduledPrefixSystemData_restrict_eq_of_extensional_fields
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)} (hcb : c ≤ b)
    (Q : scheduledPrefixSystemData (J := J) A b)
    (D : scheduledPrefixSystemData (J := J) A c)
    (hstage : (scheduledPrefixSystemData_restrict (J := J) A hcb Q).stage = D.stage)
    (hhom : HEq (scheduledPrefixSystemData_restrict (J := J) A hcb Q).hom D.hom)
    (hfromBase :
      HEq (scheduledPrefixSystemData_restrict (J := J) A hcb Q).fromBase D.fromBase) :
    scheduledPrefixSystemData_restrict (J := J) A hcb Q = D := by
  -- The restriction has the same carrier data as `D`; the remaining stored fields are propositions.
  exact scheduledPrefixSystemData_ext (J := J) A
    (scheduledPrefixSystemData_restrict (J := J) A hcb Q) D hstage hhom hfromBase

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: transition maps in a restricted
scheduled prefix system inherit original-system compatibility from the larger prefix system. -/
private theorem scheduledPrefixSystemData_restrict_hom_original_compatible_apply
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)} (hcb : c ≤ b)
    (D : scheduledPrefixSystemData (J := J) A b)
    {d e : {d : WithTop (stageRequestSchedule (J := J) A) // d ≤ c}}
    (hde : (d : WithTop (stageRequestSchedule (J := J) A)) ≤ e) :
    ((scheduledPrefixSystemData_restrict (J := J) A hcb D).hom hde).original_compatible := by
  -- Project the restricted transition map to the corresponding transition in the larger system.
  simpa [scheduledPrefixSystemData_restrict_hom_apply] using
    (D.hom_original_compatible
      (c := ⟨d.1, le_trans d.2 hcb⟩) (d := ⟨e.1, le_trans e.2 hcb⟩) hde)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: base maps in a restricted scheduled
prefix system inherit original-system compatibility from the larger prefix system. -/
private theorem scheduledPrefixSystemData_restrict_fromBase_compatible_apply
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)} (hcb : c ≤ b)
    (D : scheduledPrefixSystemData (J := J) A b)
    (d : {d : WithTop (stageRequestSchedule (J := J) A) // d ≤ c}) :
    ((scheduledPrefixSystemData_restrict (J := J) A hcb D).fromBase d).original_compatible := by
  -- The restricted base map is the larger system's base map at the lifted closed-cut index.
  simpa [scheduledPrefixSystemData_restrict_fromBase_apply] using
    (D.fromBase_compatible ⟨d.1, le_trans d.2 hcb⟩)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: realization in a restricted scheduled
prefix system is exactly the realization recorded at the lifted cut of the larger system. -/
private theorem scheduledPrefixSystemData_restrict_realizes_apply [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)} (hcb : c ≤ b)
    (D : scheduledPrefixSystemData (J := J) A b)
    (d : {d : WithTop (stageRequestSchedule (J := J) A) // d ≤ c})
    (a : stageRequestSchedule (J := J) A)
    (ha : (a : WithTop (stageRequestSchedule (J := J) A)) < d) :
    request_realized (J := J)
      (((scheduledPrefixSystemData_restrict (J := J) A hcb D).fromBase d).map_request
        (requestOfStageSchedule (J := J) A a)) := by
  -- Lift the closed-cut index and apply the original realization invariant there.
  simpa [scheduledPrefixSystemData_restrict_fromBase_apply] using
    (D.realizes ⟨d.1, le_trans d.2 hcb⟩ a ha)

/-- Helper for Lemma 7.39.2: the restriction operation has the identity law needed by the
scheduled prefix-system functor. -/
private theorem scheduledPrefixSystemRestrictionFunctor_map_id [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (x : (WithTop (stageRequestSchedule (J := J) A))ᵒᵖ) :
    (fun D : scheduledPrefixSystemData (J := J) A x.unop =>
      scheduledPrefixSystemData_restrict (J := J) A (leOfHom (𝟙 x).unop) D) = id := by
  -- Identity morphisms in the opposite preorder are self-restrictions.
  funext D
  exact scheduledPrefixSystemData_restrict_self (J := J) A D

/-- Helper for Lemma 7.39.2: the restriction operation has the composition law needed by the
scheduled prefix-system functor. -/
private theorem scheduledPrefixSystemRestrictionFunctor_map_comp [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {x y z : (WithTop (stageRequestSchedule (J := J) A))ᵒᵖ} (f : x ⟶ y) (g : y ⟶ z) :
    (fun D : scheduledPrefixSystemData (J := J) A x.unop =>
      scheduledPrefixSystemData_restrict (J := J) A (leOfHom (f ≫ g).unop) D) =
      fun D : scheduledPrefixSystemData (J := J) A x.unop =>
        scheduledPrefixSystemData_restrict (J := J) A (leOfHom g.unop)
          (scheduledPrefixSystemData_restrict (J := J) A (leOfHom f.unop) D) := by
  -- Composition in the opposite preorder is iterated restriction of closed cuts.
  funext D
  exact scheduledPrefixSystemData_restrict_restrict (J := J) A D
    (leOfHom f.unop) (leOfHom g.unop)

/-- Helper for Lemma 7.39.2: the restriction functor for coherent scheduled prefix systems over
the well-ordered request cuts. -/
private noncomputable def scheduledPrefixSystemRestrictionFunctor [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)] :
    (WithTop (stageRequestSchedule (J := J) A))ᵒᵖ ⥤ Type (max (max u v) (w + 1)) where
  obj x := scheduledPrefixSystemData (J := J) A x.unop
  map f D := scheduledPrefixSystemData_restrict (J := J) A (leOfHom f.unop) D
  map_id := scheduledPrefixSystemRestrictionFunctor_map_id (J := J) A
  map_comp := scheduledPrefixSystemRestrictionFunctor_map_comp (J := J) A

/-- Helper for Lemma 7.39.2: the scheduled prefix-system restriction functor acts by the
existing closed-cut restriction operation. -/
private theorem scheduledPrefixSystemRestrictionFunctor_map_apply [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {c b : WithTop (stageRequestSchedule (J := J) A)} (hcb : c ≤ b)
    (D : scheduledPrefixSystemData (J := J) A b) :
    (scheduledPrefixSystemRestrictionFunctor (J := J) A).map (homOfLE hcb).op D =
      scheduledPrefixSystemData_restrict (J := J) A hcb D := by
  -- This is the defining action of the functor on an order comparison.
  rfl

/-- Helper for Lemma 7.39.2: the top node of a coherent scheduled prefix system gives the older
existential prefix invariant. -/
private theorem scheduledPrefixSystemData_to_prefixData [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)}
    (D : scheduledPrefixSystemData (J := J) A b) :
    scheduledPrefixData (J := J) A b := by
  -- Project the stored top cut and its base map back to the weaker prefix proposition.
  let topCut : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b} := ⟨b, le_rfl⟩
  refine ⟨D.stage topCut, D.fromBase topCut, D.fromBase_compatible topCut, ?_⟩
  intro a ha
  exact D.realizes topCut a ha

/-- Helper for Lemma 7.39.2: in a coherent scheduled prefix system, the base map at a later
stored cut maps requests as the earlier base map followed by the stored transition morphism. -/
private theorem scheduledPrefixSystemData_fromBase_map_request_comp [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)}
    (D : scheduledPrefixSystemData (J := J) A b)
    {c d : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b}}
    (hcd : (c : WithTop (stageRequestSchedule (J := J) A)) ≤ d)
    (r : finite_cover_lift_request J A.T) :
    (D.fromBase d).map_request r = (D.hom hcd).map_request ((D.fromBase c).map_request r) := by
  -- Unfold the stored base-map composition only through the public `map_request_comp` API.
  rw [D.fromBase_comp hcd]
  exact refinement_stage_hom.map_request_comp (J := J) (D.fromBase c) (D.hom hcd) r

/-- Helper for Lemma 7.39.2: in a coherent scheduled prefix system, the base map to the top of
the closed cut is the base map to any stored predecessor followed by the stored comparison to
the top. -/
private theorem scheduledPrefixSystemData_fromBase_comp_to_top [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)}
    (D : scheduledPrefixSystemData (J := J) A b)
    (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b}) :
    refinement_stage_hom.comp (J := J) (D.fromBase c)
        (D.hom (c := c) (d := ⟨b, le_rfl⟩) c.2) =
      D.fromBase ⟨b, le_rfl⟩ := by
  -- This is the top-cut specialization of the stored base-map composition law.
  exact (D.fromBase_comp (c := c) (d := ⟨b, le_rfl⟩) c.2).symm

/-- Helper for Lemma 7.39.2: stored comparison morphisms from a predecessor to the top cut are
compatible with the original refinement data. -/
private theorem scheduledPrefixSystemData_hom_to_top_original_compatible
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)}
    (D : scheduledPrefixSystemData (J := J) A b)
    (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b}) :
    (D.hom (c := c) (d := ⟨b, le_rfl⟩) c.2).original_compatible := by
  -- Compatibility is one of the coherent prefix-system fields, specialized to the top cut.
  exact D.hom_original_compatible (c := c) (d := ⟨b, le_rfl⟩) c.2

/-- Helper for Lemma 7.39.2: realization recorded at an earlier stored cut of a coherent
scheduled prefix system persists at any later stored cut. -/
private theorem scheduledPrefixSystemData_realizes_of_le [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)}
    (D : scheduledPrefixSystemData (J := J) A b)
    {c d : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b}}
    (hcd : (c : WithTop (stageRequestSchedule (J := J) A)) ≤ d)
    (a : stageRequestSchedule (J := J) A)
    (ha : (a : WithTop (stageRequestSchedule (J := J) A)) < c) :
    request_realized (J := J) ((D.fromBase d).map_request
      (requestOfStageSchedule (J := J) A a)) := by
  -- First use the realization stored at the earlier cut.
  have hreal_c :
      request_realized (J := J) ((D.fromBase c).map_request
        (requestOfStageSchedule (J := J) A a)) :=
    D.realizes c a ha
  -- Then transport that realization along the coherent comparison to the later cut.
  have hreal_d :
      request_realized (J := J) ((D.hom hcd).map_request
        ((D.fromBase c).map_request (requestOfStageSchedule (J := J) A a))) :=
    refinement_stage_hom.map_request_realized (J := J) (D.hom hcd)
      ((D.fromBase c).map_request (requestOfStageSchedule (J := J) A a)) hreal_c
  -- The stored base-map composition identifies this transported request with the later base map.
  rw [← scheduledPrefixSystemData_fromBase_map_request_comp (J := J) A D hcd
    (requestOfStageSchedule (J := J) A a)] at hreal_d
  exact hreal_d

/-- Helper for Lemma 7.39.2: a global scheduled diagram restricts to a coherent prefix system
on any closed cut. -/
private noncomputable def scheduledGlobalDiagram_to_prefixSystemData [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (D : scheduledGlobalDiagramData (J := J) A)
    (b : WithTop (stageRequestSchedule (J := J) A)) :
    scheduledPrefixSystemData (J := J) A b :=
  { stage := fun c => D.stage c.1
    hom := fun {_ _} hcd => D.hom hcd
    hom_refl := fun c => D.hom_refl c.1
    hom_comp := fun {_ _ _} hcd hde => D.hom_comp hcd hde
    hom_original_compatible := fun {_ _} hcd => D.hom_original_compatible hcd
    fromBase := fun c => D.fromBase c.1
    fromBase_compatible := fun c => D.fromBase_compatible c.1
    fromBase_comp := fun {_ _} hcd => D.fromBase_comp hcd
    realizes := fun c a ha => D.realizes_lt c.1 a ha }

/-- Helper for Lemma 7.39.2: a global scheduled diagram gives the older prefix invariant at any
closed cut. -/
private theorem scheduledGlobalDiagram_to_prefixData [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (D : scheduledGlobalDiagramData (J := J) A)
    (b : WithTop (stageRequestSchedule (J := J) A)) :
    scheduledPrefixData (J := J) A b := by
  -- Restrict the global diagram to the closed cut and forget the transition data at its top.
  exact scheduledPrefixSystemData_to_prefixData (J := J) A
    (scheduledGlobalDiagram_to_prefixSystemData (J := J) A D b)

/-- Helper for Lemma 7.39.2: a coherent prefix system at the top cut already contains all
the data of a global scheduled diagram. -/
private theorem existsScheduledGlobalDiagramData_of_topPrefixSystem [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (D : scheduledPrefixSystemData (J := J) A
      (⊤ : WithTop (stageRequestSchedule (J := J) A))) :
    Nonempty (scheduledGlobalDiagramData (J := J) A) := by
  -- Reindex the top closed-cut system along the tautological inclusion of every cut into `⊤`.
  exact ⟨
    { stage := fun b => D.stage ⟨b, le_top⟩
      hom := fun {b c} hbc => D.hom (c := ⟨b, le_top⟩) (d := ⟨c, le_top⟩) hbc
      hom_refl := fun b => D.hom_refl ⟨b, le_top⟩
      hom_comp := fun {b c d} hbc hcd =>
        D.hom_comp (c := ⟨b, le_top⟩) (d := ⟨c, le_top⟩) (e := ⟨d, le_top⟩)
          hbc hcd
      hom_original_compatible := fun {b c} hbc =>
        D.hom_original_compatible (c := ⟨b, le_top⟩) (d := ⟨c, le_top⟩) hbc
      fromBase := fun b => D.fromBase ⟨b, le_top⟩
      fromBase_compatible := fun b => D.fromBase_compatible ⟨b, le_top⟩
      fromBase_comp := fun {b c} hbc =>
        D.fromBase_comp (c := ⟨b, le_top⟩) (d := ⟨c, le_top⟩) hbc
      realizes_lt := fun b a ha => D.realizes ⟨b, le_top⟩ a ha }⟩

/-- Helper for Lemma 7.39.2: at a minimal schedule cut, the coherent prefix system is the
constant one-node system on the original packaged stage. -/
private theorem existsScheduledPrefixSystemData_of_isMin [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)} (hb : IsMin b) :
    Nonempty (scheduledPrefixSystemData (J := J) A b) := by
  -- The whole closed cut collapses to the minimal cut, so all stages and maps are identities.
  refine ⟨
    { stage := fun _ => A
      hom := fun {_ _} _ => refinement_stage_hom_refl (J := J) A
      hom_refl := ?_
      hom_comp := ?_
      hom_original_compatible := ?_
      fromBase := fun _ => refinement_stage_hom_refl (J := J) A
      fromBase_compatible := ?_
      fromBase_comp := ?_
      realizes := ?_ }⟩
  · intro c
    rfl
  · intro c d e hcd hde
    exact (refinement_stage_hom.refl_comp (J := J) (refinement_stage_hom_refl (J := J) A)).symm
  · intro c d hcd
    exact refinement_stage_hom.original_compatible_refl (J := J) A
  · intro c
    exact refinement_stage_hom.original_compatible_refl (J := J) A
  · intro c d hcd
    exact (refinement_stage_hom.refl_comp (J := J) (refinement_stage_hom_refl (J := J) A)).symm
  · intro c a ha
    -- No request can lie strictly below a member of a minimal closed cut.
    have hab : (a : WithTop (stageRequestSchedule (J := J) A)) ≤ b := le_trans (le_of_lt ha) c.2
    have hba : b ≤ (a : WithTop (stageRequestSchedule (J := J) A)) := hb hab
    exact False.elim ((not_le_of_gt ha) (le_trans c.2 hba))

/-- Helper for Lemma 7.39.2: at a minimal schedule cut there are no earlier scheduled requests,
so the original stage with the identity morphism satisfies the prefix invariant. -/
private theorem scheduledPrefixData_of_isMin [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)} (hb : IsMin b) :
    scheduledPrefixData (J := J) A b := by
  refine ⟨A, refinement_stage_hom_refl (J := J) A,
    refinement_stage_hom.original_compatible_refl (J := J) A, ?_⟩
  intro a ha
  -- A request below a minimal cut is impossible.
  have hle : (a : WithTop (stageRequestSchedule (J := J) A)) ≤ b := le_of_lt ha
  have hge : b ≤ (a : WithTop (stageRequestSchedule (J := J) A)) := hb hle
  exact (not_le_of_gt ha hge).elim

/-- Helper for Lemma 7.39.2: prefix realization data restricts from a larger schedule cut to a
smaller one. -/
private theorem scheduledPrefixData_mono [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)} (hbc : b ≤ c) :
    scheduledPrefixData (J := J) A c → scheduledPrefixData (J := J) A b := by
  intro P
  rcases P with ⟨B, h, hcompat, hreal⟩
  refine ⟨B, h, hcompat, ?_⟩
  intro a ha
  -- A request below the smaller cut is also below the larger cut.
  exact hreal a (lt_of_lt_of_le ha hbc)

/-- Helper for Lemma 7.39.2: the successor step extends the current prefix stage by the request at
the current cut, while old realized requests are transported through the one-step refinement. -/
private theorem scheduledPrefixData_succ [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    [SuccOrder (WithTop (stageRequestSchedule (J := J) A))]
    {b : WithTop (stageRequestSchedule (J := J) A)} (hb : ¬ IsMax b)
    (P : scheduledPrefixData (J := J) A b) :
    scheduledPrefixData (J := J) A (Order.succ b) := by
  classical
  rcases P with ⟨B, h, hcompat, hreal⟩
  obtain - | a := b
  · -- The top cut is maximal, so it cannot occur in the successor branch.
    exact (hb isMax_top).elim
  · let r : finite_cover_lift_request J A.T := requestOfStageSchedule (J := J) A a
    let step : refinement_stage_hom (J := J) B
        (next_stage_for_scheduled_request (J := J) A B h r) :=
      next_stage_for_scheduled_request_hom (J := J) A B h r
    let h' : refinement_stage_hom (J := J) A
        (next_stage_for_scheduled_request (J := J) A B h r) :=
      refinement_stage_hom.comp (J := J) h step
    refine ⟨next_stage_for_scheduled_request (J := J) A B h r, h', ?_, ?_⟩
    · -- Compatibility composes the old prefix compatibility with the one-request extension.
      exact refinement_stage_hom.original_compatible_comp (J := J) h step hcompat
        (next_stage_for_scheduled_request_original_compatible (J := J) A B h r)
    · intro c hc
      have hc_le : (c : WithTop (stageRequestSchedule (J := J) A)) ≤
          (a : WithTop (stageRequestSchedule (J := J) A)) :=
        Order.le_of_lt_succ hc
      rcases hc_le.lt_or_eq with hlt | heq
      · -- Previously realized requests remain realized after transport through `step`.
        have hreal_old :
            request_realized (J := J)
              (h.map_request (requestOfStageSchedule (J := J) A c)) :=
          hreal c hlt
        have hreal_new :
            request_realized (J := J)
              (step.map_request (h.map_request (requestOfStageSchedule (J := J) A c))) :=
          refinement_stage_hom.map_request_realized (J := J) step
            (h.map_request (requestOfStageSchedule (J := J) A c)) hreal_old
        simpa [h', refinement_stage_hom.map_request_comp] using hreal_new
      · -- The only new request below the successor cut is the request at the old cut.
        have hc_eq : c = a := WithTop.coe_injective heq
        subst c
        simpa [h', r] using
          next_stage_for_scheduled_request_comp_realized (J := J) A B h r

/-- Helper for Lemma 7.39.2: prefix data at the top cut gives the scheduled saturation statement
for the fixed packaged stage. -/
private theorem scheduledPrefixData_top_yields_scheduledRequests [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (P : scheduledPrefixData (J := J) A (⊤ : WithTop (stageRequestSchedule (J := J) A))) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ a : stageRequestSchedule (J := J) A,
            request_realized (J := J)
              (h.map_request (requestOfStageSchedule (J := J) A a)) := by
  rcases P with ⟨B, h, hcompat, hreal⟩
  refine ⟨B, h, hcompat, ?_⟩
  intro a
  -- Every concrete schedule entry lies strictly below the adjoined top cut.
  exact hreal a (WithTop.coe_lt_top a)

/-- Helper for Lemma 7.39.2: any prefix witness can be promoted to a constant coherent prefix
system over the same cut. -/
private theorem existsScheduledPrefixSystemData_of_prefixData [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)}
    (P : scheduledPrefixData (J := J) A b) :
    Nonempty (scheduledPrefixSystemData (J := J) A b) := by
  rcases P with ⟨B, h, hcompat, hreal⟩
  -- Use the same realized prefix stage at every cut below `b`; all transition maps are identities.
  refine ⟨
    { stage := fun _ => B
      hom := fun {_ _} _ => refinement_stage_hom_refl (J := J) B
      hom_refl := ?_
      hom_comp := ?_
      hom_original_compatible := ?_
      fromBase := fun _ => h
      fromBase_compatible := ?_
      fromBase_comp := ?_
      realizes := ?_ }⟩
  · intro c
    rfl
  · intro c d e hcd hde
    exact (refinement_stage_hom.refl_comp (J := J)
      (refinement_stage_hom_refl (J := J) B)).symm
  · intro c d hcd
    exact refinement_stage_hom.original_compatible_refl (J := J) B
  · intro c
    exact hcompat
  · intro c d hcd
    exact (refinement_stage_hom.comp_refl (J := J) h).symm
  · intro c a ha
    -- A request below a stored cut is below the ambient cut, so the prefix witness realizes it.
    exact hreal a (lt_of_lt_of_le ha c.2)

/-- Helper for Lemma 7.39.2: a coherent prefix system at a cut gives the weaker successor-cut
prefix invariant after solving the scheduled request at that cut. -/
private theorem scheduledPrefixSystemData_succ_to_prefixData
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    [SuccOrder (WithTop (stageRequestSchedule (J := J) A))]
    {b : WithTop (stageRequestSchedule (J := J) A)} (hb : ¬ IsMax b)
    (D : scheduledPrefixSystemData (J := J) A b) :
    scheduledPrefixData (J := J) A (Order.succ b) := by
  -- Forget the coherence to the older prefix proposition, then apply the checked successor step.
  exact scheduledPrefixData_succ (J := J) A hb
    (scheduledPrefixSystemData_to_prefixData (J := J) A D)

/-- Helper for Lemma 7.39.2: successor cuts have a coherent prefix system after solving the
scheduled request at the previous cut. -/
private theorem existsScheduledPrefixSystemData_succ
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    [SuccOrder (WithTop (stageRequestSchedule (J := J) A))]
    {b : WithTop (stageRequestSchedule (J := J) A)} (hb : ¬ IsMax b)
    (D : scheduledPrefixSystemData (J := J) A b) :
    Nonempty (scheduledPrefixSystemData (J := J) A (Order.succ b)) := by
  -- The checked successor prefix witness can be promoted to a constant coherent system.
  exact existsScheduledPrefixSystemData_of_prefixData (J := J) A
    (scheduledPrefixSystemData_succ_to_prefixData (J := J) A hb D)

/-- Helper for Lemma 7.39.2: the base map to the successor top factors through any old closed
cut by first using the stored comparison to the old top and then the one-request successor map. -/
private theorem scheduledPrefixSystemData_succTop_fromBase_comp
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)}
    (D : scheduledPrefixSystemData (J := J) A b)
    (r : finite_cover_lift_request J A.T)
    (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b}) :
    let topCut : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b} := ⟨b, le_rfl⟩
    let step : refinement_stage_hom (J := J) (D.stage topCut)
        (next_stage_for_scheduled_request (J := J) A (D.stage topCut) (D.fromBase topCut) r) :=
      next_stage_for_scheduled_request_hom (J := J) A (D.stage topCut) (D.fromBase topCut) r
    refinement_stage_hom.comp (J := J) (D.fromBase c)
        (refinement_stage_hom.comp (J := J)
          (D.hom (c := c) (d := topCut) c.2) step) =
      refinement_stage_hom.comp (J := J) (D.fromBase topCut) step := by
  let topCut : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b} := ⟨b, le_rfl⟩
  let step : refinement_stage_hom (J := J) (D.stage topCut)
      (next_stage_for_scheduled_request (J := J) A (D.stage topCut) (D.fromBase topCut) r) :=
    next_stage_for_scheduled_request_hom (J := J) A (D.stage topCut) (D.fromBase topCut) r
  -- First reassociate the two stored comparisons, then replace the old-top factor by the
  -- prefix system's base-map coherence.
  calc
    refinement_stage_hom.comp (J := J) (D.fromBase c)
        (refinement_stage_hom.comp (J := J)
          (D.hom (c := c) (d := topCut) c.2) step) =
        refinement_stage_hom.comp (J := J)
          (refinement_stage_hom.comp (J := J) (D.fromBase c)
            (D.hom (c := c) (d := topCut) c.2)) step := by
          exact (refinement_stage_hom.comp_assoc (J := J) (D.fromBase c)
            (D.hom (c := c) (d := topCut) c.2) step).symm
    _ = refinement_stage_hom.comp (J := J) (D.fromBase topCut) step := by
          -- Collapse the old-cut base map followed by the top comparison to the stored top map.
          rw [scheduledPrefixSystemData_fromBase_comp_to_top (J := J) A D c]

/-- Helper for Lemma 7.39.2: the composed base map into the successor top is compatible with
the original refinement data. -/
private theorem scheduledPrefixSystemData_succTop_fromBase_compatible
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)}
    (D : scheduledPrefixSystemData (J := J) A b)
    (r : finite_cover_lift_request J A.T) :
    let topCut : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b} := ⟨b, le_rfl⟩
    let step : refinement_stage_hom (J := J) (D.stage topCut)
        (next_stage_for_scheduled_request (J := J) A (D.stage topCut) (D.fromBase topCut) r) :=
      next_stage_for_scheduled_request_hom (J := J) A (D.stage topCut) (D.fromBase topCut) r
    (refinement_stage_hom.comp (J := J) (D.fromBase topCut) step).original_compatible := by
  let topCut : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b} := ⟨b, le_rfl⟩
  let step : refinement_stage_hom (J := J) (D.stage topCut)
      (next_stage_for_scheduled_request (J := J) A (D.stage topCut) (D.fromBase topCut) r) :=
    next_stage_for_scheduled_request_hom (J := J) A (D.stage topCut) (D.fromBase topCut) r
  -- Compatibility is inherited by composing the old top base map with the one-request extension.
  exact refinement_stage_hom.original_compatible_comp (J := J) (D.fromBase topCut) step
    (D.fromBase_compatible topCut)
    (next_stage_for_scheduled_request_original_compatible (J := J) A (D.stage topCut)
      (D.fromBase topCut) r)

/-- Helper for Lemma 7.39.2: an element below a nonmaximal successor cut but not below the
predecessor cut is the successor cut itself. -/
private theorem eq_succ_of_le_succ_not_le {α : Type w} [LinearOrder α] [SuccOrder α]
    {b c : α} (hb : ¬ IsMax b) (hc : c ≤ Order.succ b) (hcb : ¬ c ≤ b) :
    c = Order.succ b := by
  -- Split the comparison with the successor; the strict case would put `c` below `b`.
  rcases hc.lt_or_eq with hlt | heq
  · exact False.elim (hcb ((Order.lt_succ_iff_of_not_isMax hb).1 hlt))
  · exact heq

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: inside a closed successor cut, being
outside the old closed cut is equivalent to being the new successor top. -/
private theorem not_le_old_iff_eq_succ_of_le_succ {α : Type w} [LinearOrder α] [SuccOrder α]
    {b c : α} (hb : ¬ IsMax b) (hc : c ≤ Order.succ b) :
    ¬ c ≤ b ↔ c = Order.succ b := by
  -- One direction is the no-gap property of `succ`; the converse uses the strict inequality
  -- from the old cut to its successor.
  constructor
  · exact eq_succ_of_le_succ_not_le hb hc
  · intro hcb hle
    exact not_le_of_gt (Order.lt_succ_of_not_isMax hb) (hcb ▸ hle)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a closed-cut index below a successor
which is not in the old closed cut is exactly the new successor top. -/
private theorem closedCut_eq_succ_of_not_le_old {α : Type w} [LinearOrder α] [SuccOrder α]
    {b : α} (hb : ¬ IsMax b) (c : {c : α // c ≤ Order.succ b})
    (hc : ¬ c.1 ≤ b) : c.1 = Order.succ b := by
  -- The subtype carries the upper bound by the successor; combine it with the no-gap successor
  -- lemma to normalize the branch index to the new top.
  exact eq_succ_of_le_succ_not_le hb c.2 hc

/-- Helper for Lemma 7.39.2: below a nonmaximal successor cut, any element that is not the
successor itself already lies below the old cut. -/
private theorem le_of_le_succ_of_ne_succ {α : Type w} [LinearOrder α] [SuccOrder α]
    {b c : α} (hb : ¬ IsMax b) (hc : c ≤ Order.succ b) (hne : c ≠ Order.succ b) :
    c ≤ b := by
  -- The weak comparison to the successor is either strict, hence below the old cut, or equality,
  -- which is ruled out by the hypothesis.
  rcases hc.lt_or_eq with hlt | heq
  · exact (Order.lt_succ_iff_of_not_isMax hb).1 hlt
  · exact False.elim (hne heq)

/-- Helper for Lemma 7.39.2: the successor step should extend a coherent prefix system without
changing its restriction to the previous closed cut. -/
private theorem existsScheduledPrefixSystemData_succ_restrict_eq
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    [SuccOrder (WithTop (stageRequestSchedule (J := J) A))]
    (b : WithTop (stageRequestSchedule (J := J) A)) (hb : ¬ IsMax b)
    (D : scheduledPrefixSystemData (J := J) A b) :
    ∃ Q : scheduledPrefixSystemData (J := J) A (Order.succ b),
      scheduledPrefixSystemData_restrict (J := J) A (Order.le_succ b) Q = D := by
  classical
  obtain - | b₀ := b
  · -- The adjoined top cut is maximal, contradicting the successor-branch hypothesis.
    exact (hb isMax_top).elim
  · -- Route correction: build the branch-defined successor prefix explicitly; old cuts reuse
    -- `D`, while the new top cut is the one-request extension of the old top stage.
    let bTop : WithTop (stageRequestSchedule (J := J) A) := b₀
    let oldTop : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ bTop} :=
      ⟨bTop, le_rfl⟩
    let r : finite_cover_lift_request J A.T := requestOfStageSchedule (J := J) A b₀
    let Btop : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
      next_stage_for_scheduled_request (J := J) A (D.stage oldTop) (D.fromBase oldTop) r
    let step : refinement_stage_hom (J := J) (D.stage oldTop) Btop :=
      next_stage_for_scheduled_request_hom (J := J) A (D.stage oldTop) (D.fromBase oldTop) r
    let stageAt :
        {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ Order.succ bTop} →
          refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
      fun c => if hc : c.1 ≤ bTop then D.stage ⟨c.1, hc⟩ else Btop
    have hsuccNotOld : ¬ Order.succ bTop ≤ bTop := by
      exact not_le_of_gt (Order.lt_succ_of_not_isMax hb)
    have stageAt_old
        (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ Order.succ bTop})
        (hc : c.1 ≤ bTop) : stageAt c = D.stage ⟨c.1, hc⟩ := by
      -- Old cuts are definitionally read from the original prefix after simplifying the branch.
      simp [stageAt, hc]
    have stageAt_top
        (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ Order.succ bTop})
        (hc : ¬ c.1 ≤ bTop) : stageAt c = Btop := by
      -- The non-old branch is the single successor top stage.
      simp [stageAt, hc]
    let homAt :
        ∀ ⦃c d : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ Order.succ bTop}⦄,
          (c : WithTop (stageRequestSchedule (J := J) A)) ≤ d →
            refinement_stage_hom (J := J) (stageAt c) (stageAt d) := by
      intro c d hcd
      by_cases hd : d.1 ≤ bTop
      · have hc : c.1 ≤ bTop := le_trans hcd hd
        -- Old-to-old maps are the stored maps of `D`, with endpoint transports made explicit.
        exact refinementStageHomCast (J := J) (stageAt_old c hc) (stageAt_old d hd)
          (D.hom (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcd)
      · by_cases hc : c.1 ≤ bTop
        · -- Old-to-new maps go through the old top and then the one-request successor step.
          exact refinementStageHomCast (J := J) (stageAt_old c hc) (stageAt_top d hd)
            (refinement_stage_hom.comp (J := J)
              (D.hom (c := ⟨c.1, hc⟩) (d := oldTop) hc) step)
        · -- New-to-new maps are identities at the successor top.
          exact refinementStageHomCast (J := J) (stageAt_top c hc) (stageAt_top d hd)
            (refinement_stage_hom_refl (J := J) Btop)
    let fromBaseAt :
        ∀ c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ Order.succ bTop},
          refinement_stage_hom (J := J) A (stageAt c) := by
      intro c
      by_cases hc : c.1 ≤ bTop
      · -- Old cuts keep the original base map, transported only across the stage branch.
        exact refinementStageHomCast (J := J) rfl (stageAt_old c hc)
          (D.fromBase ⟨c.1, hc⟩)
      · -- The successor top base map is the old top base map followed by the new step.
        exact refinementStageHomCast (J := J) rfl (stageAt_top c hc)
          (refinement_stage_hom.comp (J := J) (D.fromBase oldTop) step)
    have fromBaseAt_old
        (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ Order.succ bTop})
        (hc : c.1 ≤ bTop) :
        fromBaseAt c =
          refinementStageHomCast (J := J) rfl (stageAt_old c hc)
            (D.fromBase ⟨c.1, hc⟩) := by
      -- Old-cut base maps reduce by the same branch decision as the old-cut stages.
      simp [fromBaseAt, hc]
    have fromBaseAt_top
        (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ Order.succ bTop})
        (hc : ¬ c.1 ≤ bTop) :
        fromBaseAt c =
          refinementStageHomCast (J := J) rfl (stageAt_top c hc)
            (refinement_stage_hom.comp (J := J) (D.fromBase oldTop) step) := by
      -- The only non-old base map is the composite into the successor top.
      simp [fromBaseAt, hc]
    -- Package the branch data as the successor prefix.  Each coherence field is proved by
    -- splitting whether the target cut is old or the new successor top, so all maps normalize to
    -- either a stored field of `D` or the one-step successor map.
    let Q : scheduledPrefixSystemData (J := J) A (Order.succ bTop) := by
      refine
        { stage := stageAt
          hom := fun {c d} hcd => homAt hcd
          hom_refl := ?_
          hom_comp := ?_
          hom_original_compatible := ?_
          fromBase := fromBaseAt
          fromBase_compatible := ?_
          fromBase_comp := ?_
          realizes := ?_ }
      · intro c
        by_cases hc : c.1 ≤ bTop
        · -- On an old cut, reflexivity is the transported reflexivity field of `D`.
          simp [homAt, hc, D.hom_refl, refinementStageHomCast_refl]
        · -- At the new top, reflexivity is the transported identity of the successor stage.
          simp [homAt, hc, refinementStageHomCast_refl]
      · intro c d e hcd hde
        by_cases he : e.1 ≤ bTop
        · have hd : d.1 ≤ bTop := le_trans hde he
          have hc : c.1 ≤ bTop := le_trans hcd hd
          -- Old-old-old composition is exactly the stored composition law of `D`.
          have hD :=
            D.hom_comp (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩)
              (e := ⟨e.1, he⟩) hcd hde
          simpa [homAt, he, hd, hc] using
            (refinementStageHomCast_congr_proof (J := J) hD).trans
              (refinementStageHomCast_comp (J := J) (stageAt_old c hc)
                (stageAt_old d hd) (stageAt_old e he)
                (D.hom (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcd)
                (D.hom (c := ⟨d.1, hd⟩) (d := ⟨e.1, he⟩) hde))
        · by_cases hd : d.1 ≤ bTop
          · have hc : c.1 ≤ bTop := le_trans hcd hd
            -- Old-old-top composition is the stored old composition followed by `step`.
            have hD :
                D.hom (c := ⟨c.1, hc⟩) (d := oldTop) hc =
                  refinement_stage_hom.comp (J := J)
                    (D.hom (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcd)
                    (D.hom (c := ⟨d.1, hd⟩) (d := oldTop) hd) :=
              D.hom_comp (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩)
                (e := oldTop) hcd hd
            have hcomp :
                refinement_stage_hom.comp (J := J)
                    (D.hom (c := ⟨c.1, hc⟩) (d := oldTop) hc) step =
                  refinement_stage_hom.comp (J := J)
                    (D.hom (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcd)
                    (refinement_stage_hom.comp (J := J)
                      (D.hom (c := ⟨d.1, hd⟩) (d := oldTop) hd) step) := by
              rw [hD]
              exact refinement_stage_hom.comp_assoc (J := J)
                (D.hom (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcd)
                (D.hom (c := ⟨d.1, hd⟩) (d := oldTop) hd) step
            simpa [homAt, he, hd, hc] using
              (refinementStageHomCast_congr_proof (J := J) hcomp).trans
                (refinementStageHomCast_comp (J := J) (stageAt_old c hc)
                  (stageAt_old d hd) (stageAt_top e he)
                  (D.hom (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcd)
                  (refinement_stage_hom.comp (J := J)
                    (D.hom (c := ⟨d.1, hd⟩) (d := oldTop) hd) step))
          · by_cases hc : c.1 ≤ bTop
            · -- Old-top-top composition ends with the identity on the successor top.
              simp [homAt, he, hd, hc, refinementStageHomCast_comp_reverse,
                refinement_stage_hom.comp_refl]
            · -- Top-top-top composition is identity composition at the successor top.
              simp [homAt, he, hd, hc, refinementStageHomCast_comp_reverse,
                refinement_stage_hom.refl_comp]
      · intro c d hcd
        by_cases hd : d.1 ≤ bTop
        · have hc : c.1 ≤ bTop := le_trans hcd hd
          -- Old transition maps inherit original compatibility from `D`.
          simpa [homAt, hd, hc] using
            refinementStageHomCast_original_compatible (J := J) (stageAt_old c hc)
              (stageAt_old d hd) (D.hom (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcd)
              (D.hom_original_compatible hcd)
        · by_cases hc : c.1 ≤ bTop
          · -- Old-to-top maps are composites of a compatible old comparison with the successor step.
            simpa [homAt, hd, hc] using
              refinementStageHomCast_original_compatible (J := J) (stageAt_old c hc)
                (stageAt_top d hd)
                (refinement_stage_hom.comp (J := J)
                  (D.hom (c := ⟨c.1, hc⟩) (d := oldTop) hc) step)
                (refinement_stage_hom.original_compatible_comp (J := J)
                  (D.hom (c := ⟨c.1, hc⟩) (d := oldTop) hc) step
                  (D.hom_original_compatible hc)
                  (next_stage_for_scheduled_request_original_compatible (J := J) A
                    (D.stage oldTop) (D.fromBase oldTop) r))
          · -- The top-to-top map is an identity.
            simpa [homAt, hd, hc] using
              refinementStageHomCast_original_compatible (J := J) (stageAt_top c hc)
                (stageAt_top d hd) (refinement_stage_hom_refl (J := J) Btop)
                (refinement_stage_hom.original_compatible_refl (J := J) Btop)
      · intro c
        by_cases hc : c.1 ≤ bTop
        · -- Old base maps inherit original compatibility from `D`.
          simpa [fromBaseAt, hc] using
            refinementStageHomCast_original_compatible (J := J) rfl (stageAt_old c hc)
              (D.fromBase ⟨c.1, hc⟩) (D.fromBase_compatible ⟨c.1, hc⟩)
        · -- The new top base map is the compatible composite through the successor step.
          simpa [fromBaseAt, hc] using
            refinementStageHomCast_original_compatible (J := J) rfl (stageAt_top c hc)
              (refinement_stage_hom.comp (J := J) (D.fromBase oldTop) step)
              (scheduledPrefixSystemData_succTop_fromBase_compatible (J := J) A D r)
      · intro c d hcd
        by_cases hd : d.1 ≤ bTop
        · have hc : c.1 ≤ bTop := le_trans hcd hd
          -- Old base-map factorization is the stored factorization in `D`, transported through
          -- the branch equalities.
          have hD := D.fromBase_comp (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcd
          simpa [fromBaseAt, homAt, hd, hc] using
            (refinementStageHomCast_congr_proof (J := J) hD).trans
              (refinementStageHomCast_comp (J := J) rfl (stageAt_old c hc)
                (stageAt_old d hd) (D.fromBase ⟨c.1, hc⟩)
                (D.hom (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcd))
        · by_cases hc : c.1 ≤ bTop
          · -- Factoring to the new top uses the dedicated successor-top base-map lemma.
            have hcomp :=
              (scheduledPrefixSystemData_succTop_fromBase_comp (J := J) A D r
                ⟨c.1, hc⟩).symm
            simpa [fromBaseAt, homAt, hd, hc] using
              (refinementStageHomCast_congr_proof (J := J) hcomp).trans
                (refinementStageHomCast_comp (J := J) rfl (stageAt_old c hc)
                  (stageAt_top d hd) (D.fromBase ⟨c.1, hc⟩)
                  (refinement_stage_hom.comp (J := J)
                    (D.hom (c := ⟨c.1, hc⟩) (d := oldTop) hc) step))
          · -- Top-to-top factorization is composition with an identity.
            simp [fromBaseAt, homAt, hd, hc, refinementStageHomCast_comp_reverse,
              refinement_stage_hom.comp_refl]
      · intro c a ha
        by_cases hc : c.1 ≤ bTop
        · -- Old cuts preserve exactly the realization invariant of `D`.
          rw [fromBaseAt_old c hc]
          exact refinementStageHomCast_map_request_realized (J := J) rfl (stageAt_old c hc)
            (D.fromBase ⟨c.1, hc⟩)
            (requestOfStageSchedule (J := J) A a)
            (requestOfStageSchedule (J := J) A a) HEq.rfl
            (D.realizes ⟨c.1, hc⟩ a ha)
        · have hc_eq : c.1 = Order.succ bTop := closedCut_eq_succ_of_not_le_old hb c hc
          have ha_succ :
              (a : WithTop (stageRequestSchedule (J := J) A)) < Order.succ bTop := by
            simpa [hc_eq] using ha
          -- At the new top, the successor-top realization lemma covers old and new requests.
          rw [fromBaseAt_top c hc]
          refine refinementStageHomCast_map_request_realized (J := J) rfl (stageAt_top c hc)
            (refinement_stage_hom.comp (J := J) (D.fromBase oldTop) step)
            (requestOfStageSchedule (J := J) A a)
            (requestOfStageSchedule (J := J) A a) HEq.rfl ?_
          have ha_le :
              (a : WithTop (stageRequestSchedule (J := J) A)) ≤ bTop :=
            (Order.lt_succ_iff_of_not_isMax hb).1 ha_succ
          rcases ha_le.lt_or_eq with ha_old | ha_eq
          · -- Old requests at the predecessor top remain realized after applying the successor step.
            have htop :
                request_realized (J := J)
                  ((D.fromBase oldTop).map_request (requestOfStageSchedule (J := J) A a)) :=
              D.realizes oldTop a ha_old
            have hstep :
                request_realized (J := J)
                  (step.map_request
                    ((D.fromBase oldTop).map_request
                      (requestOfStageSchedule (J := J) A a))) :=
              refinement_stage_hom.map_request_realized (J := J) step
                ((D.fromBase oldTop).map_request (requestOfStageSchedule (J := J) A a)) htop
            simpa [refinement_stage_hom.map_request_comp] using hstep
          · -- The new request is the one used to construct the successor top.
            have hab : a = b₀ := WithTop.coe_injective (by simpa [bTop] using ha_eq)
            subst a
            simpa [r, step, refinement_stage_hom.map_request_comp] using
              next_stage_for_scheduled_request_comp_realized (J := J) A
                (D.stage oldTop) (D.fromBase oldTop) r
    refine ⟨Q, ?_⟩
    -- The restriction to the old cut is fieldwise identical to `D`; after the stage fields are
    -- identified, the transition and base-map fields become ordinary function equalities.
    have hstage :
        (scheduledPrefixSystemData_restrict (J := J) A (Order.le_succ bTop) Q).stage =
          D.stage := by
      funext c
      have hc : (c : WithTop (stageRequestSchedule (J := J) A)) ≤ bTop := c.2
      simp [Q, scheduledPrefixSystemData_restrict_stage_apply, stageAt, hc]
    have hhom :
        HEq (scheduledPrefixSystemData_restrict (J := J) A (Order.le_succ bTop) Q).hom
          D.hom := by
      -- Compare transition fields pointwise by heterogeneous function extensionality; each
      -- restricted transition is just an endpoint cast of the stored old transition.
      refine Function.hfunext rfl ?_
      intro c c' hc_eq
      cases hc_eq
      refine Function.hfunext rfl ?_
      intro d d' hd_eq
      cases hd_eq
      refine Function.hfunext rfl ?_
      intro hcd hcd' hhcd
      cases hhcd
      have hc : (c : WithTop (stageRequestSchedule (J := J) A)) ≤ bTop := c.2
      have hd : (d : WithTop (stageRequestSchedule (J := J) A)) ≤ bTop := d.2
      simpa [Q, scheduledPrefixSystemData_restrict_hom_apply, homAt, hc, hd] using
        refinementStageHomCast_heq (J := J)
          (stageAt_old ⟨c.1, le_trans c.2 (Order.le_succ bTop)⟩ hc)
          (stageAt_old ⟨d.1, le_trans d.2 (Order.le_succ bTop)⟩ hd)
          (D.hom (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcd)
    have hfromBase :
        HEq (scheduledPrefixSystemData_restrict (J := J) A (Order.le_succ bTop) Q).fromBase
          D.fromBase := by
      -- The base-map field is analogous: each restricted base map is the old base map, with
      -- only the stage endpoint transported across the old-branch equality.
      refine Function.hfunext rfl ?_
      intro c c' hc_eq
      cases hc_eq
      have hc : (c : WithTop (stageRequestSchedule (J := J) A)) ≤ bTop := c.2
      simpa [Q, scheduledPrefixSystemData_restrict_fromBase_apply, fromBaseAt, hc] using
        refinementStageHomCast_heq (J := J) rfl
          (stageAt_old ⟨c.1, le_trans c.2 (Order.le_succ bTop)⟩ hc)
          (D.fromBase ⟨c.1, hc⟩)
    exact scheduledPrefixSystemData_restrict_eq_of_extensional_fields (J := J) A
      (Order.le_succ bTop) Q D hstage hhom hfromBase

/-- Helper for Lemma 7.39.2: a coherent prefix system at the top cut gives the scheduled
saturation statement for the fixed packaged stage. -/
private theorem scheduledPrefixSystemData_top_yields_scheduledRequests [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (D : scheduledPrefixSystemData (J := J) A
      (⊤ : WithTop (stageRequestSchedule (J := J) A))) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ a : stageRequestSchedule (J := J) A,
            request_realized (J := J)
              (h.map_request (requestOfStageSchedule (J := J) A a)) := by
  -- First forget the stored coherence, then reuse the already checked top-cut adapter.
  exact scheduledPrefixData_top_yields_scheduledRequests (J := J) A
    (scheduledPrefixSystemData_to_prefixData (J := J) A D)

/-- Helper for Lemma 7.39.2: projecting a global scheduled diagram at the adjoined top cut
realizes every scheduled request for the fixed packaged stage. -/
private theorem scheduledGlobalDiagram_top_yields_scheduledRequests [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (D : scheduledGlobalDiagramData (J := J) A) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ a : stageRequestSchedule (J := J) A,
            request_realized (J := J)
              (h.map_request (requestOfStageSchedule (J := J) A a)) := by
  -- First forget the global-chain transition data at the top cut, then use the prefix adapter.
  exact scheduledPrefixData_top_yields_scheduledRequests (J := J) A
    (scheduledGlobalDiagram_to_prefixData (J := J) A D ⊤)

/-- Helper for Lemma 7.39.2: the canonical map from the base stage of a coherent diagram to its
direct-union stage preserves the recorded original refinement data. -/
private theorem refinementStageDiagramStageHomToLimit_original_compatible
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    (Aδ : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (Aδ a) (Aδ b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
        refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) Aδ hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso (J := J) Aδ hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s') :
    (refinementStageDiagramStageHomToLimit
      (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep).original_compatible := by
  -- The limit stage stores its original embedding and iso as the base stage's data followed by
  -- the canonical inclusion, which is exactly the compatibility predicate for that inclusion.
  constructor
  · ext i
    rfl
  · exact HEq.rfl

/-- Helper for Lemma 7.39.2: a direct-union stage realizes every request from its chosen base
diagram stage once those requests are eventually realized later in the diagram. -/
private theorem refinementStageDiagramLimitStage_realizes_base_requests_of_eventually
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    (Aδ : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (Aδ a) (Aδ b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
        refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) Aδ hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso (J := J) Aδ hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    (eventually_realized :
      ∀ r : finite_cover_lift_request J (Aδ a0).T,
        ∃ b, ∃ hb : a0 ≤ b,
          request_realized (J := J) ((hom hb).map_request r)) :
    ∀ r : finite_cover_lift_request J (Aδ a0).T,
      request_realized (J := J)
        ((refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep).map_request r) := by
  letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
    refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
  intro r
  rcases eventually_realized r with ⟨b, hb, hreal⟩
  have hlimit_later :
      request_realized (J := J)
        (transport_request (J := J)
          (refinementStageDiagramIndexInclusion (J := J) Aδ hom hom_refl hom_comp b)
          (refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp)
          (refinementStageDiagramSystemInclusionIso (J := J) Aδ hom hom_refl hom_comp b)
          ((hom hb).map_request r)) :=
    request_realized_transport (J := J)
      (refinementStageDiagramIndexInclusion (J := J) Aδ hom hom_refl hom_comp b)
      (refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp)
      (refinementStageDiagramSystemInclusionIso (J := J) Aδ hom hom_refl hom_comp b)
      ((hom hb).map_request r) hreal
  have hlimit_base :
      request_realized (J := J)
        (transport_request (J := J)
          (refinementStageDiagramIndexInclusion (J := J) Aδ hom hom_refl hom_comp a0)
          (refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp)
          (refinementStageDiagramSystemInclusionIso (J := J) Aδ hom hom_refl hom_comp a0) r) := by
    -- Normalize transport from the base stage to the limit through the later realizing stage.
    have htransport := refinementStageDiagramSystem_transport_request_of_le
      (J := J) Aδ hom hom_refl hom_comp hb r
    rw [htransport]
    exact hlimit_later
  -- The map from the base stage to the packaged limit is the canonical direct-union inclusion.
  simpa [refinement_stage_hom.map_request, refinementStageDiagramStageHomToLimit] using hlimit_base

/-- Helper for Lemma 7.39.2: if the chosen base map into a coherent diagram factors through a
later diagram stage, then mapping a source request to the direct-union limit through either stage
gives the same transported request. -/
private theorem refinementStageDiagramStageHomToLimit_map_request_base_comp_of_le
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    (Aδ : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (Aδ a) (Aδ b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
        refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) Aδ hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso (J := J) Aδ hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    {d : δ} (had : a0 ≤ d)
    {A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (hA0 : refinement_stage_hom (J := J) A (Aδ a0))
    (hAd : refinement_stage_hom (J := J) A (Aδ d))
    (hcoh : hAd = refinement_stage_hom.comp (J := J) hA0 (hom had))
    (r : finite_cover_lift_request J A.T) :
    (refinement_stage_hom.comp (J := J) hA0
      (refinementStageDiagramStageHomToLimit
        (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep)).map_request r =
      (refinementStageDiagramStageHomToLimit
        (J := J) Aδ hom hom_refl hom_comp a0 d hsep).map_request
          (hAd.map_request r) := by
  letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
    refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
  -- First normalize the coherent base map at `d` to the composite through `a0`.
  have hAd_map :
      hAd.map_request r = (hom had).map_request (hA0.map_request r) := by
    rw [hcoh]
    exact refinement_stage_hom.map_request_comp (J := J) hA0 (hom had) r
  -- The direct-union transport lemma identifies the inclusion from `a0` with the inclusion
  -- from the later stage `d` after applying the diagram comparison map.
  have htransport := refinementStageDiagramSystem_transport_request_of_le
    (J := J) Aδ hom hom_refl hom_comp had (hA0.map_request r)
  calc
    (refinement_stage_hom.comp (J := J) hA0
        (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep)).map_request r =
        (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep).map_request
          (hA0.map_request r) := by
          exact refinement_stage_hom.map_request_comp (J := J) hA0
            (refinementStageDiagramStageHomToLimit
              (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep) r
    _ = (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 d hsep).map_request
          ((hom had).map_request (hA0.map_request r)) := by
          simpa [refinement_stage_hom.map_request, refinementStageDiagramStageHomToLimit]
            using htransport
    _ = (refinementStageDiagramStageHomToLimit
          (J := J) Aδ hom hom_refl hom_comp a0 d hsep).map_request
          (hAd.map_request r) := by
          rw [hAd_map]

/-- Helper for Lemma 7.39.2: a successor-limit cut has a predecessor, which supplies the base
index needed when taking the direct union over the predecessor cut. -/
private theorem succLimitPredecessorSubtype_nonempty {α : Type w} [Preorder α]
    {b : α} (hb : Order.IsSuccLimit b) : Nonempty {c : α // c < b} := by
  -- The definition of successor-limit excludes minimal cuts, hence its open predecessor set is
  -- inhabited.
  rcases hb.nonempty_Iio with ⟨c, hc⟩
  exact ⟨⟨c, hc⟩⟩

/-- Helper for Lemma 7.39.2: strict predecessor subtypes in a linear order are directed by
taking the maximum of two predecessors. -/
private theorem succLimitPredecessorSubtype_directed {α : Type w} [LinearOrder α]
    {b : α} : IsDirected {c : α // c < b} (· ≤ ·) where
  directed x y := by
    -- The maximum of two strict predecessors is still a strict predecessor and dominates both.
    exact ⟨⟨max x.1 y.1, max_lt x.2 y.2⟩, le_max_left _ _, le_max_right _ _⟩

/-- Helper for Lemma 7.39.2: below a successor-limit cut, every predecessor is dominated by a
strictly larger predecessor of the same cut. -/
private theorem succLimitPredecessorSubtype_cofinal {α : Type w} [PartialOrder α] [SuccOrder α]
    {b a : α} (hb : Order.IsSuccLimit b) (ha : a < b) :
    ∃ c : {c : α // c < b}, a < c.1 := by
  -- Move from `a` to its successor; successor-limits are closed under this operation below `b`.
  have hnotMax : ¬ IsMax a := not_isMax_iff.mpr ⟨b, ha⟩
  exact ⟨⟨Order.succ a, hb.succ_lt ha⟩, Order.lt_succ_of_not_isMax hnotMax⟩

/-- Helper for Lemma 7.39.2: an element below a nontrivial successor cut either already lies
below the previous cut or is exactly the new top cut. -/
private theorem le_succ_cases_of_not_isMax {α : Type w} [LinearOrder α] [SuccOrder α]
    {b c : α} (hb : ¬ IsMax b) (hc : c ≤ Order.succ b) :
    c ≤ b ∨ c = Order.succ b := by
  -- Split the comparison with the successor into the strict and equality cases.
  rcases hc.lt_or_eq with hlt | heq
  · exact Or.inl ((Order.lt_succ_iff_of_not_isMax hb).1 hlt)
  · exact Or.inr heq

/-- Helper for Lemma 7.39.2: a strict predecessor of a nontrivial successor cut is either
strictly below the old cut or is the old cut itself. -/
private theorem lt_succ_cases_of_not_isMax {α : Type w} [LinearOrder α] [SuccOrder α]
    {b c : α} (hb : ¬ IsMax b) (hc : c < Order.succ b) :
    c < b ∨ c = b := by
  -- Convert the strict successor comparison to a weak comparison with the predecessor, then
  -- split that comparison in the linear order.
  exact ((Order.lt_succ_iff_of_not_isMax hb).1 hc).lt_or_eq

/-- Helper for Lemma 7.39.2: a coherent directed predecessor diagram whose stages realize
cofinally many scheduled requests produces prefix data at the limit cut. -/
private theorem scheduledPrefixData_limit_of_coherentDiagram
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    (cut : δ → WithTop (stageRequestSchedule (J := J) A))
    (b : WithTop (stageRequestSchedule (J := J) A))
    (Aδ : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (Aδ a) (Aδ b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
        refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) Aδ hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso (J := J) Aδ hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    (hA : ∀ d : δ, refinement_stage_hom (J := J) A (Aδ d))
    (hA_compat : ∀ d : δ, (hA d).original_compatible)
    (hreal :
      ∀ (d : δ) (a : stageRequestSchedule (J := J) A),
        (a : WithTop (stageRequestSchedule (J := J) A)) < cut d →
          request_realized (J := J)
            ((hA d).map_request (requestOfStageSchedule (J := J) A a)))
    (hcofinal :
      ∀ a : stageRequestSchedule (J := J) A,
        (a : WithTop (stageRequestSchedule (J := J) A)) < b →
          ∃ d : δ, (a : WithTop (stageRequestSchedule (J := J) A)) < cut d)
    (hmap_to_limit :
      ∀ (d : δ) (r : finite_cover_lift_request J A.T),
        (refinement_stage_hom.comp (J := J) (hA a0)
          (refinementStageDiagramStageHomToLimit
            (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep)).map_request r =
          (refinementStageDiagramStageHomToLimit
            (J := J) Aδ hom hom_refl hom_comp a0 d hsep).map_request
              ((hA d).map_request r)) :
    scheduledPrefixData (J := J) A b := by
  let L : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
    refinementStageDiagramLimitStage (J := J) Aδ hom hom_refl hom_comp a0 hsep
  let toLimit : ∀ d : δ, refinement_stage_hom (J := J) (Aδ d) L :=
    fun d => refinementStageDiagramStageHomToLimit
      (J := J) Aδ hom hom_refl hom_comp a0 d hsep
  let hLimit : refinement_stage_hom (J := J) A L :=
    refinement_stage_hom.comp (J := J) (hA a0) (toLimit a0)
  refine ⟨L, hLimit, ?_, ?_⟩
  · -- The base map to the limit is compatible because it factors through the compatible base
    -- predecessor and the limit inclusion at that predecessor.
    exact refinement_stage_hom.original_compatible_comp (J := J) (hA a0) (toLimit a0)
      (hA_compat a0)
      (refinementStageDiagramStageHomToLimit_original_compatible
        (J := J) Aδ hom hom_refl hom_comp a0 hsep)
  · intro a ha
    -- Choose a predecessor cut above this request and transport its recorded realization to the
    -- direct-union stage.
    rcases hcofinal a ha with ⟨d, had⟩
    have hstage :
        request_realized (J := J)
          ((hA d).map_request (requestOfStageSchedule (J := J) A a)) :=
      hreal d a had
    have hlimit :
        request_realized (J := J)
          ((toLimit d).map_request
            ((hA d).map_request (requestOfStageSchedule (J := J) A a))) :=
      refinement_stage_hom.map_request_realized (J := J) (toLimit d)
        ((hA d).map_request (requestOfStageSchedule (J := J) A a)) hstage
    rw [← hmap_to_limit d (requestOfStageSchedule (J := J) A a)] at hlimit
    exact hlimit

/-- Helper for Lemma 7.39.2: a coherent directed predecessor diagram at a limit cut can be
repackaged as a coherent prefix system at that cut. -/
private theorem existsScheduledPrefixSystemData_limit_of_coherentDiagram
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {δ : Type w} [Preorder δ] [IsDirected δ (· ≤ ·)]
    (cut : δ → WithTop (stageRequestSchedule (J := J) A))
    (b : WithTop (stageRequestSchedule (J := J) A))
    (Aδ : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (Aδ a) (Aδ b))
    (hom_refl :
      ∀ a : δ, hom (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ a))
    (hom_comp :
      ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
        hom (le_trans hab hbc) =
          refinement_stage_hom.comp (J := J) (hom hab) (hom hbc))
    (a0 : δ)
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
        refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) Aδ hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso (J := J) Aδ hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    (hA : ∀ d : δ, refinement_stage_hom (J := J) A (Aδ d))
    (hA_compat : ∀ d : δ, (hA d).original_compatible)
    (hreal :
      ∀ (d : δ) (a : stageRequestSchedule (J := J) A),
        (a : WithTop (stageRequestSchedule (J := J) A)) < cut d →
          request_realized (J := J)
            ((hA d).map_request (requestOfStageSchedule (J := J) A a)))
    (hcofinal :
      ∀ a : stageRequestSchedule (J := J) A,
        (a : WithTop (stageRequestSchedule (J := J) A)) < b →
          ∃ d : δ, (a : WithTop (stageRequestSchedule (J := J) A)) < cut d)
    (hmap_to_limit :
      ∀ (d : δ) (r : finite_cover_lift_request J A.T),
        (refinement_stage_hom.comp (J := J) (hA a0)
          (refinementStageDiagramStageHomToLimit
            (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep)).map_request r =
          (refinementStageDiagramStageHomToLimit
            (J := J) Aδ hom hom_refl hom_comp a0 d hsep).map_request
              ((hA d).map_request r)) :
    Nonempty (scheduledPrefixSystemData (J := J) A b) := by
  -- First build the direct-union prefix witness from the coherent predecessor diagram.
  have P : scheduledPrefixData (J := J) A b :=
    scheduledPrefixData_limit_of_coherentDiagram (J := J) A cut b Aδ hom hom_refl
      hom_comp a0 hsep hA hA_compat hreal hcofinal hmap_to_limit
  -- The older prefix witness is enough to produce the prefix-system package at this one cut.
  exact existsScheduledPrefixSystemData_of_prefixData (J := J) A P

/-- Helper for Lemma 7.39.2: a coherent diagram indexed by the strict predecessor cut of a
successor-limit schedule cut gives a coherent prefix system at that limit cut. -/
private theorem existsScheduledPrefixSystemData_limit_of_predecessorCutDiagram
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    [SuccOrder (WithTop (stageRequestSchedule (J := J) A))]
    {b : WithTop (stageRequestSchedule (J := J) A)} (hb : Order.IsSuccLimit b)
    [IsDirected {c : WithTop (stageRequestSchedule (J := J) A) // c < b} (· ≤ ·)]
    (Aδ : {c : WithTop (stageRequestSchedule (J := J) A) // c < b} →
      refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hom :
      ∀ {c d : {c : WithTop (stageRequestSchedule (J := J) A) // c < b}},
        c ≤ d → refinement_stage_hom (J := J) (Aδ c) (Aδ d))
    (hom_refl :
      ∀ c : {c : WithTop (stageRequestSchedule (J := J) A) // c < b},
        hom (show c ≤ c from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ c))
    (hom_comp :
      ∀ {d e f : {c : WithTop (stageRequestSchedule (J := J) A) // c < b}}
        (hde : d ≤ e) (hef : e ≤ f),
          hom (le_trans hde hef) =
            refinement_stage_hom.comp (J := J) (hom hde) (hom hef))
    (a0 : {c : WithTop (stageRequestSchedule (J := J) A) // c < b})
    (hsep :
      letI : Preorder (refinementStageDiagramIndex (J := J) Aδ) :=
        refinementStageDiagramIndexPreorder (J := J) Aδ hom hom_refl hom_comp
      let TΔ := refinementStageDiagramSystem (J := J) Aδ hom hom_refl hom_comp
      let jΔ := refinementStageDiagramSystemOriginalEmbedding
        (J := J) Aδ hom hom_refl hom_comp a0
      let eΔ := refinementStageDiagramSystemOriginalIso
        (J := J) Aδ hom hom_refl hom_comp a0
      ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber jΔ TΔ eΔ).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s')
    (hA :
      ∀ c : {c : WithTop (stageRequestSchedule (J := J) A) // c < b},
        refinement_stage_hom (J := J) A (Aδ c))
    (hA_compat :
      ∀ c : {c : WithTop (stageRequestSchedule (J := J) A) // c < b},
        (hA c).original_compatible)
    (hreal :
      ∀ (c : {c : WithTop (stageRequestSchedule (J := J) A) // c < b})
        (a : stageRequestSchedule (J := J) A),
          (a : WithTop (stageRequestSchedule (J := J) A)) < c.1 →
            request_realized (J := J)
              ((hA c).map_request (requestOfStageSchedule (J := J) A a)))
    (hmap_to_limit :
      ∀ (c : {c : WithTop (stageRequestSchedule (J := J) A) // c < b})
        (r : finite_cover_lift_request J A.T),
        (refinement_stage_hom.comp (J := J) (hA a0)
          (refinementStageDiagramStageHomToLimit
            (J := J) Aδ hom hom_refl hom_comp a0 a0 hsep)).map_request r =
          (refinementStageDiagramStageHomToLimit
            (J := J) Aδ hom hom_refl hom_comp a0 c hsep).map_request
              ((hA c).map_request r)) :
    Nonempty (scheduledPrefixSystemData (J := J) A b) := by
  -- The general coherent-diagram limit lemma applies with the predecessor cut as the index.
  refine existsScheduledPrefixSystemData_limit_of_coherentDiagram
    (J := J) A (cut := fun c => c.1) b Aδ hom hom_refl hom_comp a0 hsep
      hA hA_compat hreal ?_ hmap_to_limit
  intro a ha
  -- Successor-limit cuts are cofinal in their strict predecessor subtypes.
  exact succLimitPredecessorSubtype_cofinal hb ha

/-- Helper for Lemma 7.39.2: a compatible stage realizing every entry in the small request
schedule realizes every actual finite-cover request on the original packaged stage. -/
private theorem advanceCompatibleOfScheduledRequests [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hSat :
      ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
        ∃ h : refinement_stage_hom (J := J) A B,
          h.original_compatible ∧
            ∀ a : stageRequestSchedule (J := J) A,
              request_realized (J := J)
                (h.map_request (requestOfStageSchedule (J := J) A a))) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ r : finite_cover_lift_request J A.T, request_realized (J := J) (h.map_request r) := by
  rcases hSat with ⟨B, h, hcompat, hreal⟩
  refine ⟨B, h, hcompat, ?_⟩
  intro r
  -- Decode the actual request through the shrink schedule and use the scheduled realization.
  rcases requestOfStageSchedule_surjective (J := J) A r with ⟨a, ha⟩
  simpa [ha] using hreal a

/-- Helper for Lemma 7.39.2: every finite list of scheduled requests has a compatible frontier
stage realizing all entries of that list. -/
private theorem existsCompatibleStageRealizingScheduledListRequests
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (as : List (stageRequestSchedule (J := J) A)) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ ⦃a : stageRequestSchedule (J := J) A⦄, a ∈ as →
            request_realized (J := J)
              (h.map_request (requestOfStageSchedule (J := J) A a)) := by
  let rs : List (finite_cover_lift_request J A.T) :=
    as.map (requestOfStageSchedule (J := J) A)
  -- Use the existing list-frontier construction on the decoded requests.
  refine ⟨listFrontierStage (J := J) A rs, listFrontierHom (J := J) A rs, ?_, ?_⟩
  · -- The list frontier keeps the original-system compatibility required by later unions.
    exact listFrontierHom_original_compatible (J := J) A rs
  · intro a ha
    -- Membership in the scheduled list transports to membership in the decoded request list.
    have hmem : requestOfStageSchedule (J := J) A a ∈ rs :=
      List.mem_map_of_mem (f := requestOfStageSchedule (J := J) A) ha
    exact listFrontierHom_realizes_mem (J := J) A rs hmem

/-- Helper for Lemma 7.39.2: finite scheduled subsets can be realized by a compatible frontier
stage. This is the finite-cut form of the transfinite saturation invariant. -/
private theorem existsCompatibleStageRealizingScheduledFinsetRequests
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (as : Finset (stageRequestSchedule (J := J) A)) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ a : stageRequestSchedule (J := J) A, a ∈ as →
            request_realized (J := J)
              (h.map_request (requestOfStageSchedule (J := J) A a)) := by
  classical
  -- Reuse the list-frontier theorem on the canonical list underlying the finite set.
  rcases existsCompatibleStageRealizingScheduledListRequests (J := J) A as.toList with
    ⟨B, h, hcompat, hreal⟩
  refine ⟨B, h, hcompat, ?_⟩
  intro a ha
  exact hreal (by simpa using ha)

/-- Helper for Lemma 7.39.2: a successor extension of a prefix stage gives a compatible
composite from the fixed original stage and realizes the scheduled request used for that
successor. -/
private theorem compatibleSuccessorRealizesScheduledRequest
    [Limits.HasPullbacks C]
    {A L : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A L) (hcompat : h.original_compatible)
    (r : finite_cover_lift_request J A.T) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ step : refinement_stage_hom (J := J) L B,
        step.original_compatible ∧
          (refinement_stage_hom.comp (J := J) h step).original_compatible ∧
            request_realized (J := J)
              ((refinement_stage_hom.comp (J := J) h step).map_request r) := by
  let B := next_stage_for_scheduled_request (J := J) A L h r
  let step := next_stage_for_scheduled_request_hom (J := J) A L h r
  refine ⟨B, step, ?_, ?_, ?_⟩
  · -- The successor morphism records the original-system compatibility needed by the chain.
    exact next_stage_for_scheduled_request_original_compatible (J := J) A L h r
  · -- Composing the prefix map with the successor keeps compatibility from the fixed base stage.
    exact refinement_stage_hom.original_compatible_comp (J := J) h step hcompat
      (next_stage_for_scheduled_request_original_compatible (J := J) A L h r)
  · -- The successor was built precisely by solving the transported scheduled request.
    exact next_stage_for_scheduled_request_comp_realized (J := J) A L h r

/-- Helper for Lemma 7.39.2: after extending the top of a coherent scheduled prefix system by
one successor request, every request already realized at the old top remains realized at the new
top. -/
private theorem scheduledPrefixSystemData_succTop_realizes_lt
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b : WithTop (stageRequestSchedule (J := J) A)}
    (D : scheduledPrefixSystemData (J := J) A b)
    (r : finite_cover_lift_request J A.T)
    (a : stageRequestSchedule (J := J) A)
    (ha : (a : WithTop (stageRequestSchedule (J := J) A)) < b) :
    let topCut : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b} := ⟨b, le_rfl⟩
    let step : refinement_stage_hom (J := J) (D.stage topCut)
        (next_stage_for_scheduled_request (J := J) A (D.stage topCut) (D.fromBase topCut) r) :=
      next_stage_for_scheduled_request_hom (J := J) A (D.stage topCut) (D.fromBase topCut) r
    request_realized (J := J)
      ((refinement_stage_hom.comp (J := J) (D.fromBase topCut) step).map_request
        (requestOfStageSchedule (J := J) A a)) := by
  let topCut : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b} := ⟨b, le_rfl⟩
  let step : refinement_stage_hom (J := J) (D.stage topCut)
      (next_stage_for_scheduled_request (J := J) A (D.stage topCut) (D.fromBase topCut) r) :=
    next_stage_for_scheduled_request_hom (J := J) A (D.stage topCut) (D.fromBase topCut) r
  -- Start with the realization already stored at the old top cut.
  have htop :
      request_realized (J := J)
        ((D.fromBase topCut).map_request (requestOfStageSchedule (J := J) A a)) :=
    D.realizes topCut a ha
  -- Transport that realization through the successor morphism.
  have hstep :
      request_realized (J := J)
        (step.map_request
          ((D.fromBase topCut).map_request (requestOfStageSchedule (J := J) A a))) :=
    refinement_stage_hom.map_request_realized (J := J) step
      ((D.fromBase topCut).map_request (requestOfStageSchedule (J := J) A a)) htop
  -- Normalize the composite map from the fixed base stage to the successor top.
  simpa [step, refinement_stage_hom.map_request_comp] using hstep

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: a concrete request cut in `WithTop`
is never maximal, because it is strictly below the adjoined top. -/
private theorem withTop_coe_not_isMax {α : Type w} [Preorder α] (a : α) :
    ¬ IsMax (a : WithTop α) := by
  -- The adjoined top gives a strict upper bound for every concrete cut.
  exact not_isMax_iff.mpr ⟨⊤, WithTop.coe_lt_top a⟩

/-- Helper for Lemma 7.39.2: the successor top obtained by solving the request at a concrete
schedule cut realizes every scheduled request strictly below the successor cut. -/
private theorem scheduledPrefixSystemData_succTop_realizes_lt_succ
    [UnivLE.{max u v w, w}] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    [SuccOrder (WithTop (stageRequestSchedule (J := J) A))]
    (b : stageRequestSchedule (J := J) A)
    (D : scheduledPrefixSystemData (J := J) A
      (b : WithTop (stageRequestSchedule (J := J) A)))
    (a : stageRequestSchedule (J := J) A)
    (ha : (a : WithTop (stageRequestSchedule (J := J) A)) <
      Order.succ (b : WithTop (stageRequestSchedule (J := J) A))) :
    let topCut : {c : WithTop (stageRequestSchedule (J := J) A) //
      c ≤ (b : WithTop (stageRequestSchedule (J := J) A))} := ⟨b, le_rfl⟩
    let step : refinement_stage_hom (J := J) (D.stage topCut)
        (next_stage_for_scheduled_request (J := J) A (D.stage topCut) (D.fromBase topCut)
          (requestOfStageSchedule (J := J) A b)) :=
      next_stage_for_scheduled_request_hom (J := J) A (D.stage topCut)
        (D.fromBase topCut) (requestOfStageSchedule (J := J) A b)
    request_realized (J := J)
      ((refinement_stage_hom.comp (J := J) (D.fromBase topCut) step).map_request
        (requestOfStageSchedule (J := J) A a)) := by
  let topCut : {c : WithTop (stageRequestSchedule (J := J) A) //
    c ≤ (b : WithTop (stageRequestSchedule (J := J) A))} := ⟨b, le_rfl⟩
  let step : refinement_stage_hom (J := J) (D.stage topCut)
      (next_stage_for_scheduled_request (J := J) A (D.stage topCut) (D.fromBase topCut)
        (requestOfStageSchedule (J := J) A b)) :=
    next_stage_for_scheduled_request_hom (J := J) A (D.stage topCut) (D.fromBase topCut)
      (requestOfStageSchedule (J := J) A b)
  -- First reduce a predecessor of `succ b` to either an old request below `b` or the new
  -- request exactly at `b`.
  have hb_not_max : ¬ IsMax (b : WithTop (stageRequestSchedule (J := J) A)) :=
    withTop_coe_not_isMax b
  have hab :
      (a : WithTop (stageRequestSchedule (J := J) A)) ≤
        (b : WithTop (stageRequestSchedule (J := J) A)) :=
    (Order.lt_succ_iff_of_not_isMax hb_not_max).1 ha
  rcases hab.lt_or_eq with hlt | heq
  · -- Old requests were already realized at the previous top and are transported by `step`.
    exact scheduledPrefixSystemData_succTop_realizes_lt (J := J) A D
      (requestOfStageSchedule (J := J) A b) a hlt
  · -- The only new request is the one used to build the successor top.
    have hab_eq : a = b := WithTop.coe_injective heq
    subst a
    simpa [topCut, step] using
      next_stage_for_scheduled_request_comp_realized (J := J) A (D.stage topCut)
        (D.fromBase topCut) (requestOfStageSchedule (J := J) A b)

/-- Helper for Lemma 7.39.2: section compatibility for the scheduled prefix-system restriction
functor rewrites to the concrete closed-cut restriction equality. -/
private theorem scheduledPrefixSystemSection_restrict_eq [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hc : c < b) (hd : d < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    scheduledPrefixSystemData_restrict (J := J) A hcd (x.val (_root_.Opposite.op ⟨d, hd⟩)) =
      x.val (_root_.Opposite.op ⟨c, hc⟩) := by
  -- Apply the section law to the predecessor comparison and unfold the restriction functor map.
  have hsection := x.property
    ((homOfLE (show (⟨c, hc⟩ : Set.Iio b) ≤ ⟨d, hd⟩ from hcd)).op)
  exact hsection

/-- Helper for Lemma 7.39.2: section compatibility identifies the top stage of a predecessor
with the same node viewed inside any later predecessor prefix. -/
private theorem scheduledPrefixSystemSection_stage_top_eq [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hc : c < b) (hd : d < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    (x.val (_root_.Opposite.op ⟨d, hd⟩)).stage ⟨c, hcd⟩ =
      (x.val (_root_.Opposite.op ⟨c, hc⟩)).stage ⟨c, le_rfl⟩ := by
  -- Project the section equality to the top stage of the smaller closed cut.
  have hres := scheduledPrefixSystemSection_restrict_eq (J := J) A hcd hc hd x
  have hstage := congrArg
    (fun D : scheduledPrefixSystemData (J := J) A c => D.stage ⟨c, le_rfl⟩) hres
  simpa [scheduledPrefixSystemData_restrict_stage_apply] using hstage

/-- Helper for Lemma 7.39.2: section compatibility identifies every predecessor stage after
restricting a later predecessor prefix to an earlier cut. -/
private theorem scheduledPrefixSystemSection_stage_eq [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hc : c < b) (hd : d < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections))
    (a : {a : WithTop (stageRequestSchedule (J := J) A) // a ≤ c}) :
    (x.val (_root_.Opposite.op ⟨d, hd⟩)).stage ⟨a.1, le_trans a.2 hcd⟩ =
      (x.val (_root_.Opposite.op ⟨c, hc⟩)).stage a := by
  -- Project the section restriction equality to an arbitrary stored stage, then normalize the
  -- restriction projection once.
  have hres := scheduledPrefixSystemSection_restrict_eq (J := J) A hcd hc hd x
  have hstage := congrArg
    (fun D : scheduledPrefixSystemData (J := J) A c => D.stage a) hres
  simpa [scheduledPrefixSystemData_restrict_stage_apply] using hstage

/-- Helper for Lemma 7.39.2: section compatibility identifies every predecessor comparison
morphism after restricting a later predecessor prefix to an earlier cut. -/
private theorem scheduledPrefixSystemSection_hom_heq [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hc : c < b) (hd : d < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections))
    {a e : {a : WithTop (stageRequestSchedule (J := J) A) // a ≤ c}}
    (hae : (a : WithTop (stageRequestSchedule (J := J) A)) ≤ e) :
    HEq
      ((x.val (_root_.Opposite.op ⟨d, hd⟩)).hom
        (c := ⟨a.1, le_trans a.2 hcd⟩)
        (d := ⟨e.1, le_trans e.2 hcd⟩) hae)
      ((x.val (_root_.Opposite.op ⟨c, hc⟩)).hom
        (c := a) (d := e) hae) := by
  -- Rewrite the earlier section value as the restriction of the later one; the restricted hom
  -- field is definitionally the later hom on the lifted closed-cut indices.
  have hres := scheduledPrefixSystemSection_restrict_eq (J := J) A hcd hc hd x
  rw [← hres]
  rfl

/-- Helper for Lemma 7.39.2: section compatibility identifies the base map to a predecessor
top with the same base map viewed inside any later predecessor prefix. -/
private theorem scheduledPrefixSystemSection_fromBase_top_eq [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hc : c < b) (hd : d < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    HEq ((x.val (_root_.Opposite.op ⟨d, hd⟩)).fromBase ⟨c, hcd⟩)
      ((x.val (_root_.Opposite.op ⟨c, hc⟩)).fromBase ⟨c, le_rfl⟩) := by
  -- Project the same section equality to the base map at the predecessor top; the codomain
  -- stage is dependent, so the stable statement is heterogeneous equality.
  have hres := scheduledPrefixSystemSection_restrict_eq (J := J) A hcd hc hd x
  rw [← hres]
  rfl

/-- Helper for Lemma 7.39.2: section compatibility identifies every predecessor base map after
restricting a later predecessor prefix to an earlier cut. -/
private theorem scheduledPrefixSystemSection_fromBase_heq [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hc : c < b) (hd : d < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections))
    (a : {a : WithTop (stageRequestSchedule (J := J) A) // a ≤ c}) :
    HEq ((x.val (_root_.Opposite.op ⟨d, hd⟩)).fromBase ⟨a.1, le_trans a.2 hcd⟩)
      ((x.val (_root_.Opposite.op ⟨c, hc⟩)).fromBase a) := by
  -- Rewrite to the restricted later prefix; the restricted base-map projection is then
  -- judgmentally the later base map at the lifted index.
  have hres := scheduledPrefixSystemSection_restrict_eq (J := J) A hcd hc hd x
  rw [← hres]
  rfl

/-- Helper for Lemma 7.39.2: in a predecessor section, the base map to a later predecessor's
top is the base map to an earlier stored cut followed by the section's stored comparison to the
later top. -/
private theorem scheduledPrefixSystemSection_fromBase_comp_to_top [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hd : d < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    refinement_stage_hom.comp (J := J)
        ((x.val (_root_.Opposite.op ⟨d, hd⟩)).fromBase ⟨c, hcd⟩)
        ((x.val (_root_.Opposite.op ⟨d, hd⟩)).hom
          (c := ⟨c, hcd⟩) (d := ⟨d, le_rfl⟩) hcd) =
      (x.val (_root_.Opposite.op ⟨d, hd⟩)).fromBase ⟨d, le_rfl⟩ := by
  -- Specialize the prefix-system top composition law to the section value at the later cut.
  exact scheduledPrefixSystemData_fromBase_comp_to_top (J := J) A
    (x.val (_root_.Opposite.op ⟨d, hd⟩)) ⟨c, hcd⟩

/-- Helper for Lemma 7.39.2: section comparison morphisms from an earlier predecessor to a
later predecessor top are compatible with the original refinement data. -/
private theorem scheduledPrefixSystemSection_hom_to_top_original_compatible
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hd : d < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    ((x.val (_root_.Opposite.op ⟨d, hd⟩)).hom
      (c := ⟨c, hcd⟩) (d := ⟨d, le_rfl⟩) hcd).original_compatible := by
  -- This is the section-value specialization of compatibility for stored top comparisons.
  exact scheduledPrefixSystemData_hom_to_top_original_compatible (J := J) A
    (x.val (_root_.Opposite.op ⟨d, hd⟩)) ⟨c, hcd⟩

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the canonical comparison from the
top stage of one predecessor section value to the top stage of a later predecessor section
value. -/
private noncomputable def scheduledPrefixSystemSectionTopHom
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hc : c < b) (hd : d < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    refinement_stage_hom (J := J)
      ((x.val (_root_.Opposite.op ⟨c, hc⟩)).stage ⟨c, le_rfl⟩)
      ((x.val (_root_.Opposite.op ⟨d, hd⟩)).stage ⟨d, le_rfl⟩) :=
  refinementStageHomCast (J := J)
    (scheduledPrefixSystemSection_stage_top_eq (J := J) A hcd hc hd x).symm
    rfl
    ((x.val (_root_.Opposite.op ⟨d, hd⟩)).hom
      (c := ⟨c, hcd⟩) (d := ⟨d, le_rfl⟩) hcd)

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the canonical top comparison between
section predecessor values preserves original compatibility. -/
private theorem scheduledPrefixSystemSectionTopHom_original_compatible
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hc : c < b) (hd : d < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    (scheduledPrefixSystemSectionTopHom (J := J) A hcd hc hd x).original_compatible := by
  -- The named comparison is only the later section's top comparison with its source endpoint
  -- transported to the earlier section's top stage.
  exact refinementStageHomCast_original_compatible (J := J)
    (scheduledPrefixSystemSection_stage_top_eq (J := J) A hcd hc hd x).symm
    rfl
    ((x.val (_root_.Opposite.op ⟨d, hd⟩)).hom
      (c := ⟨c, hcd⟩) (d := ⟨d, le_rfl⟩) hcd)
    (scheduledPrefixSystemSection_hom_to_top_original_compatible (J := J) A hcd hd x)

/-- Helper for Lemma 7.39.2: the comparison from a predecessor section value's top node to
itself is the identity stage morphism. -/
private theorem scheduledPrefixSystemSection_hom_to_top_refl
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)}
    (hc : c < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    (x.val (_root_.Opposite.op ⟨c, hc⟩)).hom
        (c := ⟨c, le_rfl⟩) (d := ⟨c, le_rfl⟩) le_rfl =
      refinement_stage_hom_refl (J := J)
        ((x.val (_root_.Opposite.op ⟨c, hc⟩)).stage ⟨c, le_rfl⟩) := by
  -- This is the reflexivity field of the coherent prefix system stored at the predecessor cut.
  exact (x.val (_root_.Opposite.op ⟨c, hc⟩)).hom_refl ⟨c, le_rfl⟩

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the canonical section top comparison
is the identity when both predecessor cuts are the same. -/
private theorem scheduledPrefixSystemSectionTopHom_refl
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)}
    (hc : c < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    scheduledPrefixSystemSectionTopHom (J := J) A le_rfl hc hc x =
      refinement_stage_hom_refl (J := J)
        ((x.val (_root_.Opposite.op ⟨c, hc⟩)).stage ⟨c, le_rfl⟩) := by
  -- After the stored self-comparison is identified with reflexivity, endpoint-transport
  -- proof irrelevance removes the remaining cast.
  unfold scheduledPrefixSystemSectionTopHom
  simpa using scheduledPrefixSystemSection_hom_to_top_refl (J := J) A hc x

/-- Helper for Lemma 7.39.2: the base map to a predecessor section value's top node is
compatible with the original refinement data. -/
private theorem scheduledPrefixSystemSection_fromBase_to_top_original_compatible
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)}
    (hc : c < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    ((x.val (_root_.Opposite.op ⟨c, hc⟩)).fromBase ⟨c, le_rfl⟩).original_compatible := by
  -- The top base map is one of the compatible base maps in the stored predecessor prefix system.
  exact (x.val (_root_.Opposite.op ⟨c, hc⟩)).fromBase_compatible ⟨c, le_rfl⟩

/-- Helper for Lemma 7.39.2: requests below a predecessor cut are realized at that predecessor
section value's top node. -/
private theorem scheduledPrefixSystemSection_top_realizes
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c : WithTop (stageRequestSchedule (J := J) A)}
    (hc : c < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections))
    (a : stageRequestSchedule (J := J) A)
    (ha : (a : WithTop (stageRequestSchedule (J := J) A)) < c) :
    request_realized (J := J)
      (((x.val (_root_.Opposite.op ⟨c, hc⟩)).fromBase ⟨c, le_rfl⟩).map_request
        (requestOfStageSchedule (J := J) A a)) := by
  -- This is the realization invariant of the predecessor prefix system at its top cut.
  exact (x.val (_root_.Opposite.op ⟨c, hc⟩)).realizes ⟨c, le_rfl⟩ a ha

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: inside a later section value, the
comparison from an earlier predecessor to the later top factors through any intermediate
predecessor. -/
private theorem scheduledPrefixSystemSection_hom_to_top_comp
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d e : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hde : d ≤ e) (he : e < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    (x.val (_root_.Opposite.op ⟨e, he⟩)).hom
        (c := ⟨c, le_trans hcd hde⟩) (d := ⟨e, le_rfl⟩)
        (le_trans hcd hde) =
      refinement_stage_hom.comp (J := J)
        ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
          (c := ⟨c, le_trans hcd hde⟩) (d := ⟨d, hde⟩) hcd)
        ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
          (c := ⟨d, hde⟩) (d := ⟨e, le_rfl⟩) hde) := by
  -- This is exactly the coherent prefix-system composition field, specialized to the later
  -- predecessor section value and its top cut.
  exact (x.val (_root_.Opposite.op ⟨e, he⟩)).hom_comp
    (c := ⟨c, le_trans hcd hde⟩) (d := ⟨d, hde⟩) (e := ⟨e, le_rfl⟩) hcd hde

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the transported top comparisons
between predecessor section values compose as the underlying section comparisons do. -/
private theorem scheduledPrefixSystemSectionTopHom_comp
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d e : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hde : d ≤ e) (hc : c < b) (hd : d < b) (he : e < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    scheduledPrefixSystemSectionTopHom (J := J) A (le_trans hcd hde) hc he x =
      refinement_stage_hom.comp (J := J)
        (scheduledPrefixSystemSectionTopHom (J := J) A hcd hc hd x)
        (scheduledPrefixSystemSectionTopHom (J := J) A hde hd he x) := by
  -- Route correction: prove the comparison law at the stored-section level first, then
  -- transport only the three endpoints instead of unfolding whole prefix-system records.
  unfold scheduledPrefixSystemSectionTopHom
  have hraw :=
    scheduledPrefixSystemSection_hom_to_top_comp (J := J) A hcd hde he x
  have hfirst :
      refinementStageHomCast (J := J)
          (scheduledPrefixSystemSection_stage_top_eq (J := J) A (le_trans hcd hde) hc he x).symm
          (scheduledPrefixSystemSection_stage_top_eq (J := J) A hde hd he x).symm
          ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
            (c := ⟨c, le_trans hcd hde⟩) (d := ⟨d, hde⟩) hcd) =
        refinementStageHomCast (J := J)
          (scheduledPrefixSystemSection_stage_top_eq (J := J) A hcd hc hd x).symm
          rfl
          ((x.val (_root_.Opposite.op ⟨d, hd⟩)).hom
            (c := ⟨c, hcd⟩) (d := ⟨d, le_rfl⟩) hcd) := by
    -- The section law identifies the earlier comparison as seen in the later predecessor value.
    have hheq := scheduledPrefixSystemSection_hom_heq (J := J) A hde hd he x
      (a := ⟨c, hcd⟩) (e := ⟨d, le_rfl⟩) hcd
    exact refinementStageHomCast_congr_heq (J := J)
      (scheduledPrefixSystemSection_stage_top_eq (J := J) A (le_trans hcd hde) hc he x).symm
      (scheduledPrefixSystemSection_stage_top_eq (J := J) A hde hd he x).symm
      (scheduledPrefixSystemSection_stage_top_eq (J := J) A hcd hc hd x).symm
      rfl hheq
  have hcast :
      refinementStageHomCast (J := J)
          (scheduledPrefixSystemSection_stage_top_eq (J := J) A (le_trans hcd hde) hc he x).symm
          rfl
          ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
            (c := ⟨c, le_trans hcd hde⟩) (d := ⟨e, le_rfl⟩)
            (le_trans hcd hde)) =
        refinementStageHomCast (J := J)
          (scheduledPrefixSystemSection_stage_top_eq (J := J) A (le_trans hcd hde) hc he x).symm
          rfl
          (refinement_stage_hom.comp (J := J)
            ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
              (c := ⟨c, le_trans hcd hde⟩) (d := ⟨d, hde⟩) hcd)
            ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
              (c := ⟨d, hde⟩) (d := ⟨e, le_rfl⟩) hde)) := by
    exact refinementStageHomCast_congr (J := J)
      (scheduledPrefixSystemSection_stage_top_eq (J := J) A (le_trans hcd hde) hc he x).symm
      rfl hraw
  calc
    refinementStageHomCast (J := J)
        (scheduledPrefixSystemSection_stage_top_eq (J := J) A (le_trans hcd hde) hc he x).symm
        rfl
        ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
          (c := ⟨c, le_trans hcd hde⟩) (d := ⟨e, le_rfl⟩)
          (le_trans hcd hde)) =
        refinementStageHomCast (J := J)
          (scheduledPrefixSystemSection_stage_top_eq (J := J) A (le_trans hcd hde) hc he x).symm
          rfl
          (refinement_stage_hom.comp (J := J)
            ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
              (c := ⟨c, le_trans hcd hde⟩) (d := ⟨d, hde⟩) hcd)
            ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
              (c := ⟨d, hde⟩) (d := ⟨e, le_rfl⟩) hde)) := hcast
    _ = refinement_stage_hom.comp (J := J)
        (refinementStageHomCast (J := J)
          (scheduledPrefixSystemSection_stage_top_eq (J := J) A (le_trans hcd hde) hc he x).symm
          (scheduledPrefixSystemSection_stage_top_eq (J := J) A hde hd he x).symm
          ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
            (c := ⟨c, le_trans hcd hde⟩) (d := ⟨d, hde⟩) hcd))
        (refinementStageHomCast (J := J)
          (scheduledPrefixSystemSection_stage_top_eq (J := J) A hde hd he x).symm
          rfl
          ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
            (c := ⟨d, hde⟩) (d := ⟨e, le_rfl⟩) hde)) := by
          exact refinementStageHomCast_comp (J := J)
            (scheduledPrefixSystemSection_stage_top_eq (J := J) A (le_trans hcd hde) hc he x).symm
            (scheduledPrefixSystemSection_stage_top_eq (J := J) A hde hd he x).symm
            rfl
            ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
              (c := ⟨c, le_trans hcd hde⟩) (d := ⟨d, hde⟩) hcd)
            ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
              (c := ⟨d, hde⟩) (d := ⟨e, le_rfl⟩) hde)
    _ = refinement_stage_hom.comp (J := J)
        (refinementStageHomCast (J := J)
          (scheduledPrefixSystemSection_stage_top_eq (J := J) A hcd hc hd x).symm
          rfl
          ((x.val (_root_.Opposite.op ⟨d, hd⟩)).hom
            (c := ⟨c, hcd⟩) (d := ⟨d, le_rfl⟩) hcd))
        (refinementStageHomCast (J := J)
          (scheduledPrefixSystemSection_stage_top_eq (J := J) A hde hd he x).symm
          rfl
          ((x.val (_root_.Opposite.op ⟨e, he⟩)).hom
            (c := ⟨d, hde⟩) (d := ⟨e, le_rfl⟩) hde)) := by
          rw [hfirst]

/-- Helper for Chap07 Lemma 7 39 2/ScheduledSaturation: the predecessor top base map factors
through the canonical comparison to a later predecessor top. -/
private theorem scheduledPrefixSystemSectionTopHom_fromBase_comp
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    {b c d : WithTop (stageRequestSchedule (J := J) A)}
    (hcd : c ≤ d) (hc : c < b) (hd : d < b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    refinement_stage_hom.comp (J := J)
        ((x.val (_root_.Opposite.op ⟨c, hc⟩)).fromBase ⟨c, le_rfl⟩)
        (scheduledPrefixSystemSectionTopHom (J := J) A hcd hc hd x) =
      (x.val (_root_.Opposite.op ⟨d, hd⟩)).fromBase ⟨d, le_rfl⟩ := by
  -- Transport the stored base-factorization in the later predecessor value back to the
  -- predecessor top stage selected by the section.
  unfold scheduledPrefixSystemSectionTopHom
  have hbase := scheduledPrefixSystemSection_fromBase_comp_to_top (J := J) A hcd hd x
  have hfrom := scheduledPrefixSystemSection_fromBase_top_eq (J := J) A hcd hc hd x
  have hcomp :=
    refinementStageHomCast_comp_heq_left (J := J)
      (scheduledPrefixSystemSection_stage_top_eq (J := J) A hcd hc hd x).symm
      hfrom
      ((x.val (_root_.Opposite.op ⟨d, hd⟩)).hom
        (c := ⟨c, hcd⟩) (d := ⟨d, le_rfl⟩) hcd)
  rw [hcomp]
  exact hbase

/-- Helper for Lemma 7.39.2: the top nodes of an exact predecessor section form a coherent
diagram of refinement stages over the strict predecessor cut. -/
private noncomputable def scheduledPrefixSystemSectionTopDiagram
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (b : WithTop (stageRequestSchedule (J := J) A))
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    NaturalDiagramUnion.DiagramData (J := J)
      {c : WithTop (stageRequestSchedule (J := J) A) // c < b} s s' where
  obj := fun c => (x.val (_root_.Opposite.op c)).stage ⟨c.1, le_rfl⟩
  hom := fun {c d} hcd => scheduledPrefixSystemSectionTopHom (J := J) A hcd c.2 d.2 x
  hom_refl := fun c => scheduledPrefixSystemSectionTopHom_refl (J := J) A c.2 x
  hom_comp := fun {c d e} hcd hde =>
    scheduledPrefixSystemSectionTopHom_comp (J := J) A hcd hde c.2 d.2 e.2 x

/-- Helper for Lemma 7.39.2: the predecessor top-stage diagram has the expected object field. -/
private theorem scheduledPrefixSystemSectionTopDiagram_obj
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (b : WithTop (stageRequestSchedule (J := J) A))
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections))
    (c : {c : WithTop (stageRequestSchedule (J := J) A) // c < b}) :
    (scheduledPrefixSystemSectionTopDiagram (J := J) A b x).obj c =
      (x.val (_root_.Opposite.op c)).stage ⟨c.1, le_rfl⟩ := by
  -- Projecting the packaged diagram recovers the top stage of the section value.
  rfl

/-- Helper for Lemma 7.39.2: transition morphisms in the predecessor top-stage diagram remain
compatible with the original refinement data. -/
private theorem scheduledPrefixSystemSectionTopDiagram_hom_original_compatible
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (b : WithTop (stageRequestSchedule (J := J) A))
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections))
    {c d : {c : WithTop (stageRequestSchedule (J := J) A) // c < b}} (hcd : c ≤ d) :
    ((scheduledPrefixSystemSectionTopDiagram (J := J) A b x).hom hcd).original_compatible := by
  -- The packaged diagram uses the canonical section top comparison, whose compatibility was
  -- already proved from the stored prefix-system fields.
  exact scheduledPrefixSystemSectionTopHom_original_compatible (J := J) A hcd c.2 d.2 x

/-- Helper for Lemma 7.39.2: an abstract strict limit cone over the predecessor top stages of
an exact section at a successor-limit cut. -/
private structure scheduledPrefixSystemLimitCone
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (b : WithTop (stageRequestSchedule (J := J) A))
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) where
  top : refinement_stage (J := J) S' (ℱ := ℱ) s s'
  toTop :
    ∀ c : {c : WithTop (stageRequestSchedule (J := J) A) // c < b},
      refinement_stage_hom (J := J)
        ((x.val (_root_.Opposite.op c)).stage ⟨c.1, le_rfl⟩) top
  toTop_comp :
    ∀ ⦃c d : {c : WithTop (stageRequestSchedule (J := J) A) // c < b}⦄
      (hcd : (c : WithTop (stageRequestSchedule (J := J) A)) ≤ d),
        toTop c =
          refinement_stage_hom.comp (J := J)
            (scheduledPrefixSystemSectionTopHom (J := J) A hcd c.2 d.2 x)
            (toTop d)
  toTop_original_compatible :
    ∀ c : {c : WithTop (stageRequestSchedule (J := J) A) // c < b},
      (toTop c).original_compatible
  fromBaseTop : refinement_stage_hom (J := J) A top
  fromBaseTop_compatible : fromBaseTop.original_compatible
  fromBaseTop_comp :
    ∀ c : {c : WithTop (stageRequestSchedule (J := J) A) // c < b},
      fromBaseTop =
        refinement_stage_hom.comp (J := J)
          ((x.val (_root_.Opposite.op c)).fromBase ⟨c.1, le_rfl⟩)
          (toTop c)
  realizes_top :
    ∀ (a : stageRequestSchedule (J := J) A),
      (a : WithTop (stageRequestSchedule (J := J) A)) < b →
        request_realized (J := J)
          (fromBaseTop.map_request (requestOfStageSchedule (J := J) A a))

/-- Helper for Lemma 7.39.2: a strict cone on the predecessor top-stage diagram supplies the
scheduled limit-cone data needed by the exact successor-limit prefix-system lift. -/
private theorem existsScheduledPrefixSystemLimitCone_of_strictCone
    [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    [SuccOrder (WithTop (stageRequestSchedule (J := J) A))]
    (b : WithTop (stageRequestSchedule (J := J) A)) (hb : Order.IsSuccLimit b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections))
    (K : (scheduledPrefixSystemSectionTopDiagram (J := J) A b x).StrictLimitCone) :
    Nonempty (scheduledPrefixSystemLimitCone (J := J) A b x) := by
  classical
  let δ : Type w := {c : WithTop (stageRequestSchedule (J := J) A) // c < b}
  letI : IsDirected δ (· ≤ ·) := succLimitPredecessorSubtype_directed (b := b)
  let a0 : δ := Classical.choice (succLimitPredecessorSubtype_nonempty (b := b) hb)
  let fromBaseTop : refinement_stage_hom (J := J) A K.top :=
    refinement_stage_hom.comp (J := J)
      ((x.val (_root_.Opposite.op a0)).fromBase ⟨a0.1, le_rfl⟩)
      (K.toLimit a0)
  have fromBaseTop_compatible : fromBaseTop.original_compatible := by
    -- The chosen base-to-limit map factors through the chosen predecessor top stage.
    exact refinement_stage_hom.original_compatible_comp (J := J)
      ((x.val (_root_.Opposite.op a0)).fromBase ⟨a0.1, le_rfl⟩) (K.toLimit a0)
      (scheduledPrefixSystemSection_fromBase_to_top_original_compatible (J := J) A a0.2 x)
      (K.toLimit_original_compatible a0)
  have fromBaseTop_comp
      (c : {c : WithTop (stageRequestSchedule (J := J) A) // c < b}) :
      fromBaseTop =
        refinement_stage_hom.comp (J := J)
          ((x.val (_root_.Opposite.op c)).fromBase ⟨c.1, le_rfl⟩)
          (K.toLimit c) := by
    -- Compare the chosen base predecessor and the requested predecessor at a common upper
    -- predecessor, then rewrite both base maps through that common top stage.
    rcases directed_of (· ≤ ·) a0 c with ⟨d, ha0d, hcd⟩
    let fromBase0 : refinement_stage_hom (J := J) A
        ((x.val (_root_.Opposite.op a0)).stage ⟨a0.1, le_rfl⟩) :=
      (x.val (_root_.Opposite.op a0)).fromBase ⟨a0.1, le_rfl⟩
    let fromBasec : refinement_stage_hom (J := J) A
        ((x.val (_root_.Opposite.op c)).stage ⟨c.1, le_rfl⟩) :=
      (x.val (_root_.Opposite.op c)).fromBase ⟨c.1, le_rfl⟩
    let fromBased : refinement_stage_hom (J := J) A
        ((x.val (_root_.Opposite.op d)).stage ⟨d.1, le_rfl⟩) :=
      (x.val (_root_.Opposite.op d)).fromBase ⟨d.1, le_rfl⟩
    let hom0d : refinement_stage_hom (J := J)
        ((x.val (_root_.Opposite.op a0)).stage ⟨a0.1, le_rfl⟩)
        ((x.val (_root_.Opposite.op d)).stage ⟨d.1, le_rfl⟩) :=
      scheduledPrefixSystemSectionTopHom (J := J) A ha0d a0.2 d.2 x
    let homcd : refinement_stage_hom (J := J)
        ((x.val (_root_.Opposite.op c)).stage ⟨c.1, le_rfl⟩)
        ((x.val (_root_.Opposite.op d)).stage ⟨d.1, le_rfl⟩) :=
      scheduledPrefixSystemSectionTopHom (J := J) A hcd c.2 d.2 x
    have hbase_a0 : refinement_stage_hom.comp (J := J) fromBase0 hom0d = fromBased := by
      simpa [fromBase0, fromBased, hom0d] using
        scheduledPrefixSystemSectionTopHom_fromBase_comp (J := J) A ha0d a0.2 d.2 x
    have hbase_c : refinement_stage_hom.comp (J := J) fromBasec homcd = fromBased := by
      simpa [fromBasec, fromBased, homcd] using
        scheduledPrefixSystemSectionTopHom_fromBase_comp (J := J) A hcd c.2 d.2 x
    have hlimit_a0 :
        K.toLimit a0 = refinement_stage_hom.comp (J := J) hom0d (K.toLimit d) := by
      simpa [hom0d, scheduledPrefixSystemSectionTopDiagram] using K.toLimit_comp ha0d
    have hlimit_c :
        K.toLimit c = refinement_stage_hom.comp (J := J) homcd (K.toLimit d) := by
      simpa [homcd, scheduledPrefixSystemSectionTopDiagram] using K.toLimit_comp hcd
    calc
      fromBaseTop =
          refinement_stage_hom.comp (J := J) fromBase0 (K.toLimit a0) := rfl
      _ = refinement_stage_hom.comp (J := J) fromBase0
            (refinement_stage_hom.comp (J := J) hom0d (K.toLimit d)) := by
          rw [hlimit_a0]
      _ = refinement_stage_hom.comp (J := J)
            (refinement_stage_hom.comp (J := J) fromBase0 hom0d)
            (K.toLimit d) := by
          rw [← refinement_stage_hom.comp_assoc]
      _ = refinement_stage_hom.comp (J := J) fromBased (K.toLimit d) := by
          rw [hbase_a0]
      _ = refinement_stage_hom.comp (J := J)
            (refinement_stage_hom.comp (J := J) fromBasec homcd)
            (K.toLimit d) := by
          rw [← hbase_c]
      _ = refinement_stage_hom.comp (J := J) fromBasec
            (refinement_stage_hom.comp (J := J) homcd (K.toLimit d)) := by
          rw [refinement_stage_hom.comp_assoc]
      _ = refinement_stage_hom.comp (J := J) fromBasec (K.toLimit c) := by
          rw [← hlimit_c]
      _ = refinement_stage_hom.comp (J := J)
            ((x.val (_root_.Opposite.op c)).fromBase ⟨c.1, le_rfl⟩)
            (K.toLimit c) := rfl
  have realizes_top :
      ∀ (a : stageRequestSchedule (J := J) A),
        (a : WithTop (stageRequestSchedule (J := J) A)) < b →
          request_realized (J := J)
            (fromBaseTop.map_request (requestOfStageSchedule (J := J) A a)) := by
    intro a ha
    -- Choose a predecessor cut above the scheduled request and transport its stored realization
    -- through the strict cone leg into the limit top.
    rcases succLimitPredecessorSubtype_cofinal (b := b) hb ha with ⟨c, hac⟩
    have hreal :
        request_realized (J := J)
          (((x.val (_root_.Opposite.op c)).fromBase ⟨c.1, le_rfl⟩).map_request
            (requestOfStageSchedule (J := J) A a)) :=
      scheduledPrefixSystemSection_top_realizes (J := J) A c.2 x a hac
    have hlimit :
        request_realized (J := J)
          ((K.toLimit c).map_request
            (((x.val (_root_.Opposite.op c)).fromBase ⟨c.1, le_rfl⟩).map_request
              (requestOfStageSchedule (J := J) A a))) :=
      refinement_stage_hom.map_request_realized (J := J) (K.toLimit c)
        (((x.val (_root_.Opposite.op c)).fromBase ⟨c.1, le_rfl⟩).map_request
          (requestOfStageSchedule (J := J) A a)) hreal
    have hmap :
        fromBaseTop.map_request (requestOfStageSchedule (J := J) A a) =
          (K.toLimit c).map_request
            (((x.val (_root_.Opposite.op c)).fromBase ⟨c.1, le_rfl⟩).map_request
              (requestOfStageSchedule (J := J) A a)) := by
      rw [fromBaseTop_comp c]
      exact refinement_stage_hom.map_request_comp (J := J)
        ((x.val (_root_.Opposite.op c)).fromBase ⟨c.1, le_rfl⟩)
        (K.toLimit c) (requestOfStageSchedule (J := J) A a)
    rw [hmap]
    exact hlimit
  exact ⟨
    { top := K.top
      toTop := fun c => K.toLimit c
      toTop_comp := fun {c d} hcd => K.toLimit_comp hcd
      toTop_original_compatible := fun c => K.toLimit_original_compatible c
      fromBaseTop := fromBaseTop
      fromBaseTop_compatible := fromBaseTop_compatible
      fromBaseTop_comp := fromBaseTop_comp
      realizes_top := realizes_top }⟩

/-- Helper for Lemma 7.39.2: a closed-cut element of a limit cut that is not a strict
predecessor is the limit cut itself. -/
private theorem closedCut_eq_of_not_lt
    {α : Type w} [LinearOrder α] {b : α}
    (c : {c : α // c ≤ b}) (hc : ¬ c.1 < b) : c.1 = b := by
  -- In a linear order, the closed-cut upper bound and the negated strict comparison force
  -- equality with the top cut.
  exact le_antisymm c.2 (le_of_not_gt hc)

/-- Helper for Lemma 7.39.2: an abstract strict limit cone over predecessor top stages gives an
exact lift of the predecessor section to the successor-limit cut. -/
private theorem existsScheduledPrefixSystemData_limit_restrict_eq_of_limitCone
    [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    [SuccOrder (WithTop (stageRequestSchedule (J := J) A))]
    (b : WithTop (stageRequestSchedule (J := J) A)) (_hb : Order.IsSuccLimit b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections))
    (K : scheduledPrefixSystemLimitCone (J := J) A b x) :
    ∃ y : scheduledPrefixSystemData (J := J) A b,
      ∀ (i : WithTop (stageRequestSchedule (J := J) A)) (hi : i < b),
        scheduledPrefixSystemData_restrict (J := J) A hi.le y =
          x.val (_root_.Opposite.op ⟨i, hi⟩) := by
  classical
  let stageAt :
      {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b} →
        refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
    fun c => if hc : c.1 < b then
      (x.val (_root_.Opposite.op ⟨c.1, hc⟩)).stage ⟨c.1, le_rfl⟩
    else K.top
  have stageAt_old
      (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b})
      (hc : c.1 < b) :
      stageAt c = (x.val (_root_.Opposite.op ⟨c.1, hc⟩)).stage ⟨c.1, le_rfl⟩ := by
    -- Strict predecessor cuts are read directly from the section value at that predecessor.
    simp [stageAt, hc]
  have stageAt_top
      (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b})
      (hc : ¬ c.1 < b) :
      stageAt c = K.top := by
    -- The only non-predecessor branch is the new limit top.
    simp [stageAt, hc]
  let homAt :
      ∀ ⦃c d : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b}⦄,
        (c : WithTop (stageRequestSchedule (J := J) A)) ≤ d →
          refinement_stage_hom (J := J) (stageAt c) (stageAt d) := by
    intro c d hcd
    by_cases hd : d.1 < b
    · have hc : c.1 < b := lt_of_le_of_lt hcd hd
      -- Between predecessor cuts we use the section's canonical top comparison.
      exact refinementStageHomCast (J := J) (stageAt_old c hc) (stageAt_old d hd)
        (scheduledPrefixSystemSectionTopHom (J := J) A hcd hc hd x)
    · by_cases hc : c.1 < b
      · -- From a predecessor to the new top we use the strict cone leg.
        exact refinementStageHomCast (J := J) (stageAt_old c hc) (stageAt_top d hd)
          (K.toTop ⟨c.1, hc⟩)
      · -- The top-to-top comparison is the identity on the cone top.
        exact refinementStageHomCast (J := J) (stageAt_top c hc) (stageAt_top d hd)
          (refinement_stage_hom_refl (J := J) K.top)
  let fromBaseAt :
      ∀ c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b},
        refinement_stage_hom (J := J) A (stageAt c) := by
    intro c
    by_cases hc : c.1 < b
    · -- Old cuts keep the base map stored in the predecessor section value.
      exact refinementStageHomCast (J := J) rfl (stageAt_old c hc)
        ((x.val (_root_.Opposite.op ⟨c.1, hc⟩)).fromBase ⟨c.1, le_rfl⟩)
    · -- The limit top uses the base map supplied by the strict cone.
      exact refinementStageHomCast (J := J) rfl (stageAt_top c hc) K.fromBaseTop
  have fromBaseAt_old
      (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b})
      (hc : c.1 < b) :
      fromBaseAt c =
        refinementStageHomCast (J := J) rfl (stageAt_old c hc)
          ((x.val (_root_.Opposite.op ⟨c.1, hc⟩)).fromBase ⟨c.1, le_rfl⟩) := by
    -- The base-map branch for old cuts is definitionally the predecessor base map.
    simp [fromBaseAt, hc]
  have fromBaseAt_top
      (c : {c : WithTop (stageRequestSchedule (J := J) A) // c ≤ b})
      (hc : ¬ c.1 < b) :
      fromBaseAt c =
        refinementStageHomCast (J := J) rfl (stageAt_top c hc) K.fromBaseTop := by
    -- The top branch is the cone base map, transported across the branch equality.
    simp [fromBaseAt, hc]
  let Q : scheduledPrefixSystemData (J := J) A b := by
    refine
      { stage := stageAt
        hom := fun {c d} hcd => homAt hcd
        hom_refl := ?_
        hom_comp := ?_
        hom_original_compatible := ?_
        fromBase := fromBaseAt
        fromBase_compatible := ?_
        fromBase_comp := ?_
        realizes := ?_ }
    · intro c
      by_cases hc : c.1 < b
      · -- Reflexivity below the limit cut is the predecessor-section top reflexivity.
        simp [homAt, hc, scheduledPrefixSystemSectionTopHom_refl,
          refinementStageHomCast_refl]
      · -- Reflexivity at the limit top is the transported identity of the cone top.
        simp [homAt, hc, refinementStageHomCast_refl]
    · intro c d e hcd hde
      by_cases he : e.1 < b
      · have hd : d.1 < b := lt_of_le_of_lt hde he
        have hc : c.1 < b := lt_of_le_of_lt hcd hd
        -- Old-old-old composition is exactly the section top-comparison law.
        have hD :=
          scheduledPrefixSystemSectionTopHom_comp (J := J) A hcd hde hc hd he x
        simpa [homAt, he, hd, hc] using
          (refinementStageHomCast_congr_proof (J := J) hD).trans
            (refinementStageHomCast_comp (J := J) (stageAt_old c hc)
              (stageAt_old d hd) (stageAt_old e he)
              (scheduledPrefixSystemSectionTopHom (J := J) A hcd hc hd x)
              (scheduledPrefixSystemSectionTopHom (J := J) A hde hd he x))
      · by_cases hd : d.1 < b
        · have hc : c.1 < b := lt_of_le_of_lt hcd hd
          -- Composition into the limit top is the strict cone composition law.
          have hcomp := K.toTop_comp (c := ⟨c.1, hc⟩) (d := ⟨d.1, hd⟩) hcd
          simpa [homAt, he, hd, hc] using
            (refinementStageHomCast_congr_proof (J := J) hcomp).trans
              (refinementStageHomCast_comp (J := J) (stageAt_old c hc)
                (stageAt_old d hd) (stageAt_top e he)
                (scheduledPrefixSystemSectionTopHom (J := J) A hcd hc hd x)
                (K.toTop ⟨d.1, hd⟩))
        · by_cases hc : c.1 < b
          · -- A predecessor-to-top map followed by the top identity is itself.
            simp [homAt, he, hd, hc, refinementStageHomCast_comp_reverse,
              refinement_stage_hom.comp_refl]
          · -- The top identity composes with itself.
            simp [homAt, he, hd, hc, refinementStageHomCast_comp_reverse,
              refinement_stage_hom.refl_comp]
    · intro c d hcd
      by_cases hd : d.1 < b
      · have hc : c.1 < b := lt_of_le_of_lt hcd hd
        -- Old transition maps inherit compatibility from the section-top comparison.
        simpa [homAt, hd, hc] using
          refinementStageHomCast_original_compatible (J := J) (stageAt_old c hc)
            (stageAt_old d hd)
            (scheduledPrefixSystemSectionTopHom (J := J) A hcd hc hd x)
            (scheduledPrefixSystemSectionTopHom_original_compatible (J := J) A hcd hc hd x)
      · by_cases hc : c.1 < b
        · -- Cone legs are assumed compatible with the original refinement data.
          simpa [homAt, hd, hc] using
            refinementStageHomCast_original_compatible (J := J) (stageAt_old c hc)
              (stageAt_top d hd) (K.toTop ⟨c.1, hc⟩)
              (K.toTop_original_compatible ⟨c.1, hc⟩)
        · -- The identity at the cone top is compatible.
          simpa [homAt, hd, hc] using
            refinementStageHomCast_original_compatible (J := J) (stageAt_top c hc)
              (stageAt_top d hd) (refinement_stage_hom_refl (J := J) K.top)
              (refinement_stage_hom.original_compatible_refl (J := J) K.top)
    · intro c
      by_cases hc : c.1 < b
      · -- Old base maps inherit compatibility from the stored predecessor prefix system.
        simpa [fromBaseAt, hc] using
          refinementStageHomCast_original_compatible (J := J) rfl (stageAt_old c hc)
            ((x.val (_root_.Opposite.op ⟨c.1, hc⟩)).fromBase ⟨c.1, le_rfl⟩)
            (scheduledPrefixSystemSection_fromBase_to_top_original_compatible
              (J := J) A hc x)
      · -- The top base map is part of the strict limit cone data.
        simpa [fromBaseAt, hc] using
          refinementStageHomCast_original_compatible (J := J) rfl (stageAt_top c hc)
            K.fromBaseTop K.fromBaseTop_compatible
    · intro c d hcd
      by_cases hd : d.1 < b
      · have hc : c.1 < b := lt_of_le_of_lt hcd hd
        -- Old base-map factorization is the section top base-map law.
        have hD := (scheduledPrefixSystemSectionTopHom_fromBase_comp (J := J) A
          hcd hc hd x).symm
        simpa [fromBaseAt, homAt, hd, hc] using
          (refinementStageHomCast_congr_proof (J := J) hD).trans
            (refinementStageHomCast_comp (J := J) rfl (stageAt_old c hc)
              (stageAt_old d hd)
              ((x.val (_root_.Opposite.op ⟨c.1, hc⟩)).fromBase ⟨c.1, le_rfl⟩)
              (scheduledPrefixSystemSectionTopHom (J := J) A hcd hc hd x))
      · by_cases hc : c.1 < b
        · -- Factoring to the limit top is a cone base-map axiom.
          have hD := K.fromBaseTop_comp ⟨c.1, hc⟩
          simpa [fromBaseAt, homAt, hd, hc] using
            (refinementStageHomCast_congr_proof (J := J) hD).trans
              (refinementStageHomCast_comp (J := J) rfl (stageAt_old c hc)
                (stageAt_top d hd)
                ((x.val (_root_.Opposite.op ⟨c.1, hc⟩)).fromBase ⟨c.1, le_rfl⟩)
                (K.toTop ⟨c.1, hc⟩))
        · -- At the top, factorization is composition with an identity.
          simp [fromBaseAt, homAt, hd, hc, refinementStageHomCast_comp_reverse,
            refinement_stage_hom.comp_refl]
    · intro c a ha
      by_cases hc : c.1 < b
      · -- Old cuts keep the realization invariant of the predecessor section value.
        rw [fromBaseAt_old c hc]
        exact refinementStageHomCast_map_request_realized (J := J) rfl (stageAt_old c hc)
          ((x.val (_root_.Opposite.op ⟨c.1, hc⟩)).fromBase ⟨c.1, le_rfl⟩)
          (requestOfStageSchedule (J := J) A a)
          (requestOfStageSchedule (J := J) A a) HEq.rfl
          (scheduledPrefixSystemSection_top_realizes (J := J) A hc x a ha)
      · -- At the new top, use the cone realization field after identifying the branch.
        have hb_eq : c.1 = b := closedCut_eq_of_not_lt c hc
        have ha_top :
            (a : WithTop (stageRequestSchedule (J := J) A)) < b := by
          simpa [hb_eq] using ha
        rw [fromBaseAt_top c hc]
        exact refinementStageHomCast_map_request_realized (J := J) rfl (stageAt_top c hc)
          K.fromBaseTop
          (requestOfStageSchedule (J := J) A a)
          (requestOfStageSchedule (J := J) A a) HEq.rfl
          (K.realizes_top a ha_top)
  refine ⟨Q, ?_⟩
  intro i hi
  -- The constructed limit prefix restricts to the supplied section value because all predecessor
  -- branches were copied from that section and normalized through its section laws.
  have hstage :
      (scheduledPrefixSystemData_restrict (J := J) A hi.le Q).stage =
        (x.val (_root_.Opposite.op ⟨i, hi⟩)).stage := by
    funext c
    have hc_lt : (c : WithTop (stageRequestSchedule (J := J) A)) < b :=
      lt_of_le_of_lt c.2 hi
    have hsec := scheduledPrefixSystemSection_stage_eq (J := J) A c.2 hc_lt hi x
      ⟨c.1, le_rfl⟩
    simpa [Q, scheduledPrefixSystemData_restrict_stage_apply, stageAt, hc_lt] using hsec.symm
  have hhom :
      HEq (scheduledPrefixSystemData_restrict (J := J) A hi.le Q).hom
        (x.val (_root_.Opposite.op ⟨i, hi⟩)).hom := by
    refine Function.hfunext rfl ?_
    intro c c' hc_eq
    cases hc_eq
    refine Function.hfunext rfl ?_
    intro d d' hd_eq
    cases hd_eq
    refine Function.hfunext rfl ?_
    intro hcd hcd' hhcd
    cases hhcd
    have hc_lt : (c : WithTop (stageRequestSchedule (J := J) A)) < b :=
      lt_of_le_of_lt c.2 hi
    have hd_lt : (d : WithTop (stageRequestSchedule (J := J) A)) < b :=
      lt_of_le_of_lt d.2 hi
    have hsec := scheduledPrefixSystemSection_hom_heq (J := J) A d.2 hd_lt hi x
      (a := ⟨c.1, hcd⟩) (e := ⟨d.1, le_rfl⟩) hcd
    have htop :
        HEq (scheduledPrefixSystemSectionTopHom (J := J) A hcd hc_lt hd_lt x)
          ((x.val (_root_.Opposite.op ⟨d.1, hd_lt⟩)).hom
            (c := ⟨c.1, hcd⟩) (d := ⟨d.1, le_rfl⟩) hcd) := by
      unfold scheduledPrefixSystemSectionTopHom
      exact refinementStageHomCast_heq (J := J)
        (scheduledPrefixSystemSection_stage_top_eq (J := J) A hcd hc_lt hd_lt x).symm
        rfl
        ((x.val (_root_.Opposite.op ⟨d.1, hd_lt⟩)).hom
          (c := ⟨c.1, hcd⟩) (d := ⟨d.1, le_rfl⟩) hcd)
    have hraw :
        HEq (refinementStageHomCast (J := J)
            (stageAt_old ⟨c.1, le_trans c.2 hi.le⟩ hc_lt)
            (stageAt_old ⟨d.1, le_trans d.2 hi.le⟩ hd_lt)
            (scheduledPrefixSystemSectionTopHom (J := J) A hcd hc_lt hd_lt x))
          ((x.val (_root_.Opposite.op ⟨i, hi⟩)).hom (c := c) (d := d) hcd) :=
      (refinementStageHomCast_heq (J := J)
        (stageAt_old ⟨c.1, le_trans c.2 hi.le⟩ hc_lt)
        (stageAt_old ⟨d.1, le_trans d.2 hi.le⟩ hd_lt)
        (scheduledPrefixSystemSectionTopHom (J := J) A hcd hc_lt hd_lt x)).trans
          (htop.trans hsec.symm)
    simpa [Q, scheduledPrefixSystemData_restrict_hom_apply, homAt, hc_lt, hd_lt] using hraw
  have hfromBase :
      HEq (scheduledPrefixSystemData_restrict (J := J) A hi.le Q).fromBase
        (x.val (_root_.Opposite.op ⟨i, hi⟩)).fromBase := by
    refine Function.hfunext rfl ?_
    intro c c' hc_eq
    cases hc_eq
    have hc_lt : (c : WithTop (stageRequestSchedule (J := J) A)) < b :=
      lt_of_le_of_lt c.2 hi
    have hsec := scheduledPrefixSystemSection_fromBase_heq (J := J) A c.2 hc_lt hi x
      ⟨c.1, le_rfl⟩
    have hraw :
        HEq (refinementStageHomCast (J := J) rfl
            (stageAt_old ⟨c.1, le_trans c.2 hi.le⟩ hc_lt)
            ((x.val (_root_.Opposite.op ⟨c.1, hc_lt⟩)).fromBase ⟨c.1, le_rfl⟩))
          ((x.val (_root_.Opposite.op ⟨i, hi⟩)).fromBase c) :=
      (refinementStageHomCast_heq (J := J) rfl
        (stageAt_old ⟨c.1, le_trans c.2 hi.le⟩ hc_lt)
        ((x.val (_root_.Opposite.op ⟨c.1, hc_lt⟩)).fromBase ⟨c.1, le_rfl⟩)).trans
          hsec.symm
    simpa [Q, scheduledPrefixSystemData_restrict_fromBase_apply, fromBaseAt, hc_lt] using hraw
  exact scheduledPrefixSystemData_restrict_eq_of_extensional_fields (J := J) A
    hi.le Q (x.val (_root_.Opposite.op ⟨i, hi⟩)) hstage hhom hfromBase

/-- Helper for Lemma 7.39.2: an exact compatible section over the strict predecessors of a
successor-limit cut should lift to the cut with all predecessor restrictions unchanged. -/
private theorem existsScheduledPrefixSystemData_limit_restrict_eq_of_section
    [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    [SuccOrder (WithTop (stageRequestSchedule (J := J) A))]
    (b : WithTop (stageRequestSchedule (J := J) A)) (hb : Order.IsSuccLimit b)
    (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
      scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)) :
    ∃ y : scheduledPrefixSystemData (J := J) A b,
      ∀ (i : WithTop (stageRequestSchedule (J := J) A)) (hi : i < b),
        scheduledPrefixSystemData_restrict (J := J) A hi.le y =
          x.val (_root_.Opposite.op ⟨i, hi⟩) := by
  -- Route correction: the old direct-union predecessor inclusions are not strict cone maps, so
  -- the exact restriction proof is now separated from the missing quotient-union cone
  -- construction.  Once such a strict cone is available, the branch-defined prefix system above
  -- gives the required lift.
  have hcone : Nonempty (scheduledPrefixSystemLimitCone (J := J) A b x) := by
    have hstrict :
        Nonempty ((scheduledPrefixSystemSectionTopDiagram (J := J) A b x).StrictLimitCone) := by
      -- The remaining quotient-union work is isolated in the natural-diagram owner API; here we
      -- only supply nonemptiness/directedness of the strict predecessor cut and compatibility of
      -- the predecessor top-stage transition maps.
      letI : Nonempty {c : WithTop (stageRequestSchedule (J := J) A) // c < b} :=
        succLimitPredecessorSubtype_nonempty (b := b) hb
      letI : IsDirected {c : WithTop (stageRequestSchedule (J := J) A) // c < b} (· ≤ ·) :=
        succLimitPredecessorSubtype_directed (b := b)
      exact NaturalDiagramUnion.DiagramData.existsStrictLimitCone
        (D := scheduledPrefixSystemSectionTopDiagram (J := J) A b x)
        (by
          intro c d hcd
          exact scheduledPrefixSystemSectionTopDiagram_hom_original_compatible
            (J := J) A b x hcd)
    rcases hstrict with ⟨K⟩
    exact existsScheduledPrefixSystemLimitCone_of_strictCone (J := J) A b hb x K
  rcases hcone with ⟨K⟩
  exact existsScheduledPrefixSystemData_limit_restrict_eq_of_limitCone (J := J) A b hb x K

/-- Helper for Lemma 7.39.2: a coherent prefix system at the terminal request cut is exactly
the data needed to produce one compatible stage realizing every scheduled request. -/
private theorem existsCompatibleStageRealizingScheduledRequests_of_topPrefixSystem
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    (hD :
      Nonempty (scheduledPrefixSystemData (J := J) A
        (⊤ : WithTop (stageRequestSchedule (J := J) A)))) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ a : stageRequestSchedule (J := J) A,
            request_realized (J := J)
              (h.map_request (requestOfStageSchedule (J := J) A a)) := by
  rcases hD with ⟨D⟩
  -- Project the top node of the coherent prefix system and forget the internal transition data.
  exact scheduledPrefixSystemData_top_yields_scheduledRequests (J := J) A D

/-- Helper for Lemma 7.39.2: exact successor and successor-limit sections for the scheduled
prefix-system restriction functor produce a terminal coherent prefix system. -/
private theorem existsScheduledPrefixSystemData_top_of_exactSections
    [UnivLE.{max u v w, w}]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    [LinearOrder (stageRequestSchedule (J := J) A)]
    [WellFoundedLT (WithTop (stageRequestSchedule (J := J) A))]
    [OrderBot (WithTop (stageRequestSchedule (J := J) A))]
    [SuccOrder (WithTop (stageRequestSchedule (J := J) A))]
    (hsucc :
      ∀ (b : WithTop (stageRequestSchedule (J := J) A)) (_hb : ¬ IsMax b)
        (D : scheduledPrefixSystemData (J := J) A b),
          ∃ Q : scheduledPrefixSystemData (J := J) A (Order.succ b),
            scheduledPrefixSystemData_restrict (J := J) A (Order.le_succ b) Q = D)
    (hlimit :
      ∀ (b : WithTop (stageRequestSchedule (J := J) A)) (_hb : Order.IsSuccLimit b)
        (x : (((OrderHom.Subtype.val (· ∈ Set.Iio b)).monotone.functor.op ⋙
          scheduledPrefixSystemRestrictionFunctor (J := J) A).sections)),
          ∃ y : scheduledPrefixSystemData (J := J) A b,
            ∀ (i : WithTop (stageRequestSchedule (J := J) A)) (hi : i < b),
              scheduledPrefixSystemData_restrict (J := J) A hi.le y =
                x.val (_root_.Opposite.op ⟨i, hi⟩)) :
    Nonempty (scheduledPrefixSystemData (J := J) A
      (⊤ : WithTop (stageRequestSchedule (J := J) A))) := by
  let F := scheduledPrefixSystemRestrictionFunctor (J := J) A
  let d : F.WellOrderInductionData :=
    Functor.WellOrderInductionData.ofExists
      (F := F)
      (fun b hb D => by
        rcases hsucc b hb D with ⟨Q, hQ⟩
        -- The successor section hypothesis is already in the concrete restriction normal form.
        refine ⟨Q, ?_⟩
        simpa [F, scheduledPrefixSystemRestrictionFunctor_map_apply] using hQ)
      (fun b hb x => by
        rcases hlimit b hb x with ⟨y, hy⟩
        -- The limit section hypothesis supplies all predecessor restrictions of the lift.
        refine ⟨y, ?_⟩
        intro i hi
        simpa [F, scheduledPrefixSystemRestrictionFunctor_map_apply] using hy i hi)
  rcases existsScheduledPrefixSystemData_of_isMin (J := J) A isMin_bot with ⟨Dbot⟩
  -- Mathlib's well-order induction data extends the bottom prefix system to a global section;
  -- evaluating that section at `⊤` gives the terminal coherent prefix system.
  exact ⟨(d.sectionsMk Dbot).val (_root_.Opposite.op
    (⊤ : WithTop (stageRequestSchedule (J := J) A)))⟩

/-- Helper for Lemma 7.39.2: the missing source-facing saturation construction over the small
well-ordered schedule of requests of one packaged stage. -/
private theorem existsCompatibleStageRealizingScheduledRequests
    [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ a : stageRequestSchedule (J := J) A,
            request_realized (J := J)
              (h.map_request (requestOfStageSchedule (J := J) A a)) := by
  classical
  letI : LinearOrder (stageRequestSchedule (J := J) A) :=
    linearOrderOfSTO WellOrderingRel
  letI : WellFoundedLT (stageRequestSchedule (J := J) A) :=
    WellOrderingRel.isWellOrder.toIsWellFounded
  letI : WellFoundedLT (WithTop (stageRequestSchedule (J := J) A)) := inferInstance
  letI : OrderBot (WithTop (stageRequestSchedule (J := J) A)) :=
    WellFoundedLT.toOrderBot (WithTop (stageRequestSchedule (J := J) A))
  letI : SuccOrder (WithTop (stageRequestSchedule (J := J) A)) :=
    SuccOrder.ofLinearWellFoundedLT (WithTop (stageRequestSchedule (J := J) A))
  -- Route correction: the previous `OpenSaturationPrefix` route rebuilt a parallel cut type
  -- and still needed exact restriction sections.  The canonical invariant in this file is now
  -- `scheduledPrefixSystemData`; a top value of that functor immediately yields the stage wanted
  -- here, while the remaining construction is the exact `WellOrderInductionData` section.
  have htop :
      Nonempty (scheduledPrefixSystemData (J := J) A
        (⊤ : WithTop (stageRequestSchedule (J := J) A))) := by
    -- The remaining construction is now precisely the two exact section clauses for the
    -- restriction functor: one successor extension and one successor-limit lift.
    exact existsScheduledPrefixSystemData_top_of_exactSections (J := J) A
      (existsScheduledPrefixSystemData_succ_restrict_eq (J := J) A)
      (existsScheduledPrefixSystemData_limit_restrict_eq_of_section (J := J) A)
  -- The terminal prefix system reads off one compatible stage realizing every scheduled request.
  exact existsCompatibleStageRealizingScheduledRequests_of_topPrefixSystem (J := J) A htop

/-- THE KERNEL (transfinite recursion over the well-ordered request set of a fixed stage):
for any packaged stage `A`, there is a single compatible further refinement realizing every
finite-cover request of `A.T`. -/
theorem advance_compatible [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        h.original_compatible ∧
          ∀ r : finite_cover_lift_request J A.T, request_realized (J := J) (h.map_request r) := by
  -- Route correction: finite-list frontiers only solve finite scheduled subsets and do not give
  -- comparison maps between arbitrary frontiers.  It remains necessary to build one coherent
  -- scheduled saturation chain; the wrapper from such a chain to this theorem is now checked in
  -- `advanceCompatibleOfScheduledRequests`.
  exact advanceCompatibleOfScheduledRequests (J := J) A
    (existsCompatibleStageRealizingScheduledRequests (J := J) A)

/-- The iterated `advance_compatible` tower. -/
noncomputable def advTower [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    (A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  Nat.rec A₀ (fun _ A => Classical.choose (advance_compatible (J := J) A))

/-- The successor morphisms of the `advTower`. -/
noncomputable def advStep [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    (A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    ∀ n, refinement_stage_hom (J := J) (advTower (J := J) A₀ n) (advTower (J := J) A₀ (n + 1)) :=
  fun n => Classical.choose (Classical.choose_spec (advance_compatible (J := J) (advTower (J := J) A₀ n)))

theorem advStep_original_compatible [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)]
    [Limits.HasPullbacks C] (A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s') (n : ℕ) :
    (advStep (J := J) A₀ n).original_compatible :=
  (Classical.choose_spec (Classical.choose_spec
    (advance_compatible (J := J) (advTower (J := J) A₀ n)))).1

theorem advStep_realizes [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)]
    [Limits.HasPullbacks C] (A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s') (n : ℕ)
    (r : finite_cover_lift_request J (advTower (J := J) A₀ n).T) :
    request_realized (J := J) ((advStep (J := J) A₀ n).map_request r) :=
  (Classical.choose_spec (Classical.choose_spec
    (advance_compatible (J := J) (advTower (J := J) A₀ n)))).2 r

/-- Outer `ℕ`-tower assembly: closes `exists_terminal_refinement_stage_realizing_all_requests`.
Iterate `advance_compatible` and take the directed union over `δ = ULift.{w} ℕ`. -/
theorem terminal_refinement_stage_realizing_all_requests
    [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    (hss' : s ≠ s') :
    ∃ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∀ r : finite_cover_lift_request J A.T, request_realized (J := J) r := by
  -- The base stage and the iterated `advance` tower.
  let A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
    base_refinement_stage (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss'
  -- Repackage the tower as a directed diagram over `δ = ULift.{w} ℕ`.
  let δ : Type w := ULift.{w} ℕ
  let Aδ : δ → refinement_stage (J := J) S' (ℱ := ℱ) s s' := fun a => advTower (J := J) A₀ a.down
  let homδ : ∀ {a b : δ}, a ≤ b → refinement_stage_hom (J := J) (Aδ a) (Aδ b) :=
    fun {a b} h => omegaStageHomLE (J := J) (advTower (J := J) A₀) (advStep (J := J) A₀) h
  have homδ_refl : ∀ a : δ,
      homδ (show a ≤ a from le_rfl) = refinement_stage_hom_refl (J := J) (Aδ a) := by
    intro a
    exact omegaStageHomLE_self_eq (J := J) (advTower (J := J) A₀) (advStep (J := J) A₀) le_rfl
  have homδ_comp : ∀ {a b c : δ} (hab : a ≤ b) (hbc : b ≤ c),
      homδ (le_trans hab hbc) = refinement_stage_hom.comp (J := J) (homδ hab) (homδ hbc) := by
    intro a b c hab hbc
    exact omegaStageHomLE_eq_comp (J := J) (advTower (J := J) A₀) (advStep (J := J) A₀) hab hbc
  have homδ_compat : ∀ {a b : δ} (hab : a ≤ b), (homδ hab).original_compatible := by
    intro a b hab
    exact omegaStageHomLE_original_compatible (J := J) (advTower (J := J) A₀) (advStep (J := J) A₀)
      (advStep_original_compatible (J := J) A₀) hab
  -- Separation survives the directed union (compatible homs).
  have hsep := refinementStageDiagramLimitStage_separated_of_compatible
    (J := J) Aδ homδ homδ_refl homδ_comp homδ_compat (ULift.up 0)
  -- Every request of a finite stage is realized at the next successor stage.
  have heventually : ∀ a (r : finite_cover_lift_request J (Aδ a).T),
      ∃ b, ∃ hab : a ≤ b, request_realized (J := J) ((homδ hab).map_request r) := by
    intro a r
    refine ⟨ULift.up (a.down + 1), Nat.le_succ a.down, ?_⟩
    have hstep_eq :
        homδ (show a ≤ ULift.up (a.down + 1) from Nat.le_succ a.down)
          = advStep (J := J) A₀ a.down :=
      omegaStageHomLE_succ_self_eq_of_le (J := J) (advTower (J := J) A₀) (advStep (J := J) A₀)
        (Nat.le_succ a.down)
    rw [hstep_eq]
    exact advStep_realizes (J := J) A₀ a.down r
  -- The directed-union stage realizes all of its requests.
  refine ⟨refinementStageDiagramLimitStage (J := J) Aδ homδ homδ_refl homδ_comp (ULift.up 0) hsep, ?_⟩
  exact refinementStageDiagramLimitStage_realizes_all_requests_of_eventually
    (J := J) Aδ homδ homδ_refl homδ_comp (ULift.up 0) hsep heventually

end

end CategoryTheory
