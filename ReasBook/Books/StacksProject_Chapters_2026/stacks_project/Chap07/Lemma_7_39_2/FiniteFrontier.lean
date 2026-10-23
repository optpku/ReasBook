module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_8_2
public import stacks_project.Chap07.Lemma_7_39_1
public import stacks_project.Chap07.Lemma_7_39_2.PackagedStages

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

/-- Helper for Lemma 7.39.2: two requests on one stage can be realized after one further packaged
refinement. -/
theorem exists_refinement_stage_realizing_pair_requests
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (r1 r2 : finite_cover_lift_request J A.T) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J) A B,
        request_realized (J := J) (h.map_request r1) ∧
          request_realized (J := J) (h.map_request r2) := by
  -- Solve the first request, transport the second to the successor, then solve that transported
  -- request and compose the two stage morphisms.
  rcases extend_stage_by_request (J := J) A r1 with ⟨B1, h1, hr1⟩
  rcases extend_stage_by_request (J := J) B1 (h1.map_request r2) with ⟨B2, h2, hr2⟩
  refine ⟨B2, refinement_stage_hom.comp (J := J) h1 h2, ?_, ?_⟩
  · -- The first request was solved at `B1` and stays realized after the second extension.
    have hreal := B2.solved_realized (h2.solved_mono hr1.1)
    simpa [refinement_stage_hom.map_request_comp] using hreal
  · -- The second request is solved at `B2` after its first transport.
    have hreal := B2.solved_realized hr2.1
    simpa [refinement_stage_hom.map_request_comp] using hreal

/-- Helper for Lemma 7.39.2: any finite list of requests on one stage can be realized after one
further packaged refinement. This is the checked finite-prefix version of the source
well-ordering construction. -/
theorem exists_refinement_stage_realizing_list_requests
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s') :
    ∀ rs : List (finite_cover_lift_request J A.T),
      ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
        ∃ h : refinement_stage_hom (J := J) A B,
          ∀ ⦃r : finite_cover_lift_request J A.T⦄, r ∈ rs →
            request_realized (J := J) (h.map_request r)
    := by
  let motive : Nat → Prop := fun n =>
    ∀ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∀ rs : List (finite_cover_lift_request J A.T), rs.length = n →
        ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
          ∃ h : refinement_stage_hom (J := J) A B,
            ∀ ⦃r : finite_cover_lift_request J A.T⦄, r ∈ rs →
              request_realized (J := J) (h.map_request r)
  have hrec : ∀ n, motive n := by
    intro n
    refine Nat.strongRec (motive := motive) ?_ n
    intro n ih A rs hlen
    cases rs with
    | nil =>
        refine ⟨A, refinement_stage_hom_refl (J := J) A, ?_⟩
        intro r hr
        cases hr
    | cons r rs =>
        rcases extend_stage_by_request (J := J) A r with ⟨B₁, h₁, hr₁⟩
        have hlt : (rs.map h₁.map_request).length < n := by
          have hlen' : rs.length + 1 = n := by
            simpa using hlen
          rw [List.length_map, ← hlen']
          exact Nat.lt_succ_self rs.length
        rcases ih (rs.map h₁.map_request).length hlt B₁
            (rs.map h₁.map_request) rfl with
          ⟨B₂, h₂, hrs₂⟩
        refine ⟨B₂, refinement_stage_hom.comp (J := J) h₁ h₂, ?_⟩
        intro r₀ hr₀
        rcases List.mem_cons.mp hr₀ with hhead | hr₀
        · -- The head request was solved at the first successor and remains realized afterwards.
          have hreal₁ : request_realized (J := J) (h₁.map_request r₀) := by
            rw [hhead]
            exact B₁.solved_realized hr₁.1
          have hreal₂ :
              request_realized (J := J) (h₂.map_request (h₁.map_request r₀)) :=
            refinement_stage_hom.map_request_realized (J := J) h₂ (h₁.map_request r₀) hreal₁
          simpa [refinement_stage_hom.map_request_comp] using hreal₂
        · -- The tail requests are scheduled on `B₁` after transport by `h₁`.
          have hmem : h₁.map_request r₀ ∈ rs.map h₁.map_request :=
            List.mem_map_of_mem (f := h₁.map_request) hr₀
          have hreal₂ :
              request_realized (J := J) (h₂.map_request (h₁.map_request r₀)) :=
            hrs₂ hmem
          simpa [refinement_stage_hom.map_request_comp] using hreal₂
  intro rs
  exact hrec rs.length A rs rfl

/-- Helper for Lemma 7.39.2: any finite list of requests from an earlier stage can be realized
after a further refinement of the current stage that already refines that earlier one. -/
theorem exists_refinement_stage_realizing_transported_list_requests
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    {A₀ A : refinement_stage (J := J) S' (ℱ := ℱ) s s'}
    (h : refinement_stage_hom (J := J) A₀ A)
    (rs : List (finite_cover_lift_request J A₀.T)) :
    ∃ B : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ hAB : refinement_stage_hom (J := J) A B,
        ∀ ⦃r : finite_cover_lift_request J A₀.T⦄, r ∈ rs →
          request_realized (J := J)
            ((refinement_stage_hom.comp (J := J) h hAB).map_request r) := by
  -- Transport the finite source frontier to the current stage, solve it there, and compose.
  rcases exists_refinement_stage_realizing_list_requests (J := J) A (rs.map h.map_request) with
    ⟨B, hAB, hB⟩
  refine ⟨B, hAB, ?_⟩
  intro r hr
  have hmem : h.map_request r ∈ rs.map h.map_request :=
    List.mem_map_of_mem (f := h.map_request) hr
  have hreal : request_realized (J := J) (hAB.map_request (h.map_request r)) :=
    hB hmem
  simpa [refinement_stage_hom.map_request_comp] using hreal

/-- Helper for Lemma 7.39.2: finite-list frontier stage, starting from a current stage `L`
together with its map from a fixed original stage `A₀`. The list entries are requests on `A₀`;
each step transports the next original request to the current stage before applying the one-step
extension. -/
noncomputable def listFrontierStageFrom
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) :
    List (finite_cover_lift_request J A₀.T) →
      refinement_stage (J := J) S' (ℱ := ℱ) s s'
  | [] => L
  | r :: rs =>
      let L' := next_stage_for_scheduled_request (J := J) A₀ L h r
      let h' := refinement_stage_hom.comp (J := J) h
        (next_stage_for_scheduled_request_hom (J := J) A₀ L h r)
      listFrontierStageFrom A₀ L' h' rs

/-- Helper for Lemma 7.39.2: recursive hom from the fixed original stage `A₀` to a finite-list
frontier stage. -/
noncomputable def listFrontierHomFrom
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) :
    (rs : List (finite_cover_lift_request J A₀.T)) →
      refinement_stage_hom (J := J) A₀ (listFrontierStageFrom (J := J) A₀ L h rs)
  | [] => h
  | r :: rs =>
      let L' := next_stage_for_scheduled_request (J := J) A₀ L h r
      let h' := refinement_stage_hom.comp (J := J) h
        (next_stage_for_scheduled_request_hom (J := J) A₀ L h r)
      listFrontierHomFrom A₀ L' h' rs

/-- Helper for Lemma 7.39.2: if the current finite-list prefix stage records the original
refinement embedding as the composition through its prefix hom, then the final frontier stage
records the same compatibility for the recursively composed frontier hom. -/
theorem listFrontierStageFrom_j
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L)
    (hLj : L.j = compose_refinement_embedding A₀.j h.k) :
    ∀ rs : List (finite_cover_lift_request J A₀.T),
      (listFrontierStageFrom (J := J) A₀ L h rs).j =
        compose_refinement_embedding A₀.j
          (listFrontierHomFrom (J := J) A₀ L h rs).k
  | [] => hLj
  | r :: rs => by
      let step := next_stage_for_scheduled_request_hom (J := J) A₀ L h r
      let L' := next_stage_for_scheduled_request (J := J) A₀ L h r
      let h' := refinement_stage_hom.comp (J := J) h step
      have hL'j_step : L'.j = compose_refinement_embedding L.j step.k := by
        simpa [L', step] using next_stage_for_scheduled_request_j (J := J) A₀ L h r
      have hL'j : L'.j = compose_refinement_embedding A₀.j h'.k := by
        rw [hL'j_step, hLj]
        ext i
        rfl
      -- Apply the induction hypothesis to the successor prefix and unfold the recursion once.
      simpa [listFrontierStageFrom, listFrontierHomFrom, L', step, h'] using
        listFrontierStageFrom_j A₀ L' h' hL'j rs

/-- Helper for Lemma 7.39.2: appending a finite list of requests to a frontier construction is
the same as first constructing the frontier for the prefix and then continuing from that prefix
stage. -/
theorem listFrontierStageFrom_append
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) :
    ∀ (rs ts : List (finite_cover_lift_request J A₀.T)),
      listFrontierStageFrom (J := J) A₀ L h (rs ++ ts) =
        listFrontierStageFrom (J := J) A₀
          (listFrontierStageFrom (J := J) A₀ L h rs)
          (listFrontierHomFrom (J := J) A₀ L h rs) ts
  | [], _ => rfl
  | r :: rs, ts => by
      let L' := next_stage_for_scheduled_request (J := J) A₀ L h r
      let h' := refinement_stage_hom.comp (J := J) h
        (next_stage_for_scheduled_request_hom (J := J) A₀ L h r)
      -- Unfold one successor step and apply the induction hypothesis to the tail.
      simpa [List.cons_append, listFrontierStageFrom, listFrontierHomFrom, L', h'] using
        listFrontierStageFrom_append A₀ L' h' rs ts

/-- Helper for Lemma 7.39.2: the current prefix stage maps canonically to the frontier stage for
the remaining finite list. -/
noncomputable def listFrontierCurrentHomFrom
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) :
    (rs : List (finite_cover_lift_request J A₀.T)) →
      refinement_stage_hom (J := J) L (listFrontierStageFrom (J := J) A₀ L h rs)
  | [] => refinement_stage_hom_refl (J := J) L
  | r :: rs =>
      let step := next_stage_for_scheduled_request_hom (J := J) A₀ L h r
      let L' := next_stage_for_scheduled_request (J := J) A₀ L h r
      let h' := refinement_stage_hom.comp (J := J) h step
      refinement_stage_hom.comp (J := J) step
        (listFrontierCurrentHomFrom A₀ L' h' rs)

/-- Helper for Lemma 7.39.2: the current-stage-to-frontier morphism in the finite-list
construction is compatible with the recorded original-system refinement data. -/
theorem listFrontierCurrentHomFrom_original_compatible
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) :
    ∀ rs : List (finite_cover_lift_request J A₀.T),
      (listFrontierCurrentHomFrom (J := J) A₀ L h rs).original_compatible
  | [] => by
      change (refinement_stage_hom_refl (J := J) L).original_compatible
      exact refinement_stage_hom.original_compatible_refl L
  | r :: rs => by
      let step := next_stage_for_scheduled_request_hom (J := J) A₀ L h r
      let L' := next_stage_for_scheduled_request (J := J) A₀ L h r
      let h' := refinement_stage_hom.comp (J := J) h step
      change
        (refinement_stage_hom.comp (J := J) step
          (listFrontierCurrentHomFrom (J := J) A₀ L' h' rs)).original_compatible
      exact refinement_stage_hom.original_compatible_comp step
        (listFrontierCurrentHomFrom (J := J) A₀ L' h' rs)
        (next_stage_for_scheduled_request_original_compatible (J := J) A₀ L h r)
        (listFrontierCurrentHomFrom_original_compatible A₀ L' h' rs)

/-- Helper for Lemma 7.39.2: if the initial morphism into the current prefix stage is compatible
with the original refinement data, then so is the composed morphism to the finite-list frontier. -/
theorem listFrontierHomFrom_original_compatible
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L)
    (hcompat : h.original_compatible) :
    ∀ rs : List (finite_cover_lift_request J A₀.T),
      (listFrontierHomFrom (J := J) A₀ L h rs).original_compatible
  | [] => hcompat
  | r :: rs => by
      let step := next_stage_for_scheduled_request_hom (J := J) A₀ L h r
      let L' := next_stage_for_scheduled_request (J := J) A₀ L h r
      let h' := refinement_stage_hom.comp (J := J) h step
      have h'compat : h'.original_compatible :=
        refinement_stage_hom.original_compatible_comp h step hcompat
          (next_stage_for_scheduled_request_original_compatible (J := J) A₀ L h r)
      simpa [listFrontierHomFrom, step, L', h'] using
        listFrontierHomFrom_original_compatible A₀ L' h' h'compat rs

/-- Helper for Lemma 7.39.2: the direct original-to-frontier hom maps requests as first
transporting to the current stage and then along the current-to-frontier hom. -/
theorem listFrontierHomFrom_map_request
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) :
    ∀ (rs : List (finite_cover_lift_request J A₀.T))
      (r : finite_cover_lift_request J A₀.T),
      (listFrontierHomFrom (J := J) A₀ L h rs).map_request r =
        (listFrontierCurrentHomFrom (J := J) A₀ L h rs).map_request (h.map_request r)
  | [], r => by
      change h.map_request r =
        (refinement_stage_hom_refl (J := J) L).map_request (h.map_request r)
      simp [refinement_stage_hom.map_request, refinement_stage_hom_refl,
        transport_request_identity]
  | r₀ :: rs, r => by
      let step := next_stage_for_scheduled_request_hom (J := J) A₀ L h r₀
      let L' := next_stage_for_scheduled_request (J := J) A₀ L h r₀
      let h' := refinement_stage_hom.comp (J := J) h step
      have ih := listFrontierHomFrom_map_request A₀ L' h' rs r
      simpa [listFrontierHomFrom, listFrontierCurrentHomFrom,
        refinement_stage_hom.map_request_comp, step, L', h'] using ih

/-- Helper for Lemma 7.39.2: every original request in the finite list is realized after transport
to the constructed finite-list frontier stage. -/
theorem listFrontierHomFrom_realizes_mem
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (h : refinement_stage_hom (J := J) A₀ L) :
    ∀ (rs : List (finite_cover_lift_request J A₀.T))
      ⦃r : finite_cover_lift_request J A₀.T⦄, r ∈ rs →
        request_realized (J := J)
          ((listFrontierHomFrom (J := J) A₀ L h rs).map_request r)
  | [], r, hr => by
      cases hr
  | r₀ :: rs, r, hr => by
      let step := next_stage_for_scheduled_request_hom (J := J) A₀ L h r₀
      let L' := next_stage_for_scheduled_request (J := J) A₀ L h r₀
      let h' := refinement_stage_hom.comp (J := J) h step
      rcases List.mem_cons.mp hr with hhead | htail
      · -- The head is solved by the first successor and then transported through the tail frontier.
        have hreal₁ :
            request_realized (J := J) (h'.map_request r₀) := by
          simpa [h', step, L'] using
            next_stage_for_scheduled_request_comp_realized (J := J) A₀ L h r₀
        have hreal₂ :
            request_realized (J := J)
              ((listFrontierCurrentHomFrom (J := J) A₀ L' h' rs).map_request
                (h'.map_request r₀)) :=
          refinement_stage_hom.map_request_realized (J := J)
            (listFrontierCurrentHomFrom (J := J) A₀ L' h' rs) (h'.map_request r₀) hreal₁
        have hmap := listFrontierHomFrom_map_request A₀ L' h' rs r₀
        have hreal₃ :
            request_realized (J := J)
              ((listFrontierHomFrom (J := J) A₀ L' h' rs).map_request r₀) := by
          rwa [hmap]
        rw [hhead]
        simpa [listFrontierHomFrom, step, L', h'] using hreal₃
      · -- Tail requests are handled recursively after the first transported extension.
        simpa [listFrontierHomFrom, step, L', h'] using
          listFrontierHomFrom_realizes_mem A₀ L' h' rs htail

/-- Helper for Lemma 7.39.2: finite-list frontier stage starting from the original stage itself. -/
noncomputable def listFrontierStage
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (rs : List (finite_cover_lift_request J A₀.T)) :
    refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
  listFrontierStageFrom (J := J) A₀ A₀ (refinement_stage_hom_refl (J := J) A₀) rs

/-- Helper for Lemma 7.39.2: recursive hom from the original stage to its finite-list frontier
stage. -/
noncomputable def listFrontierHom
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (rs : List (finite_cover_lift_request J A₀.T)) :
    refinement_stage_hom (J := J) A₀ (listFrontierStage (J := J) A₀ rs) :=
  listFrontierHomFrom (J := J) A₀ A₀ (refinement_stage_hom_refl (J := J) A₀) rs

/-- Helper for Lemma 7.39.2: the finite-list frontier realizes every listed original request
transported to the frontier. -/
theorem listFrontierHom_realizes_mem
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (rs : List (finite_cover_lift_request J A₀.T))
    ⦃r : finite_cover_lift_request J A₀.T⦄ (hr : r ∈ rs) :
    request_realized (J := J) ((listFrontierHom (J := J) A₀ rs).map_request r) := by
  exact listFrontierHomFrom_realizes_mem (J := J) A₀ A₀
    (refinement_stage_hom_refl (J := J) A₀) rs hr

/-- Helper for Lemma 7.39.2: the finite-list frontier morphism is compatible with the original
refinement data recorded by the packaged stages. -/
theorem listFrontierHom_original_compatible
    [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (rs : List (finite_cover_lift_request J A₀.T)) :
    (listFrontierHom (J := J) A₀ rs).original_compatible := by
  exact listFrontierHomFrom_original_compatible (J := J) A₀ A₀
    (refinement_stage_hom_refl (J := J) A₀)
    (refinement_stage_hom.original_compatible_refl A₀) rs

/-- Helper for Lemma 7.39.2: finite source-frontier form of the source proof. Starting from the
original inverse system, any finite list of original finite-cover requests is realized after one
packaged refinement, with realization measured by the direct stage morphism from the original
stage. -/
theorem exists_refinement_stage_hom_realizing_source_request_list
    [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') (rs : List (finite_cover_lift_request J S')) :
    ∃ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J)
        (base_refinement_stage (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss') A,
        ∀ ⦃r : finite_cover_lift_request J S'⦄, r ∈ rs →
          request_realized (J := J) (h.map_request r) := by
  let A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
    base_refinement_stage (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss'
  let A : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
    listFrontierStage (J := J) A₀ rs
  let h : refinement_stage_hom (J := J) A₀ A :=
    listFrontierHom (J := J) A₀ rs
  refine ⟨A, h, ?_⟩
  intro r hr
  -- The list-frontier API realizes every listed original request after transport by `h`.
  simpa [A₀, A, h] using listFrontierHom_realizes_mem (J := J) A₀ rs hr

/-- Helper for Lemma 7.39.2: finite source-frontier form, with the compatibility datum needed
for directed-union separation arguments. -/
theorem exists_refinement_stage_hom_realizing_source_request_list_compatible
    [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') (rs : List (finite_cover_lift_request J S')) :
    ∃ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J)
        (base_refinement_stage (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss') A,
        h.original_compatible ∧
          ∀ ⦃r : finite_cover_lift_request J S'⦄, r ∈ rs →
            request_realized (J := J) (h.map_request r) := by
  let A₀ : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
    base_refinement_stage (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss'
  let A : refinement_stage (J := J) S' (ℱ := ℱ) s s' :=
    listFrontierStage (J := J) A₀ rs
  let h : refinement_stage_hom (J := J) A₀ A :=
    listFrontierHom (J := J) A₀ rs
  refine ⟨A, h, ?_, ?_⟩
  · simpa [A₀, A, h] using listFrontierHom_original_compatible (J := J) A₀ rs
  · intro r hr
    simpa [A₀, A, h] using listFrontierHom_realizes_mem (J := J) A₀ rs hr

/-- Helper for Lemma 7.39.2: finite source-frontier form using a `Finset` of original
finite-cover requests. This is the finite initial-segment package needed by the source proof
before passing to a well-ordered transfinite union. -/
theorem exists_refinement_stage_hom_realizing_source_request_finset
    [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') (rs : Finset (finite_cover_lift_request J S')) :
    ∃ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J)
        (base_refinement_stage (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss') A,
        ∀ ⦃r : finite_cover_lift_request J S'⦄, r ∈ rs →
          request_realized (J := J) (h.map_request r) := by
  -- Route correction: the existing checked frontier is list-based; this repackages the same
  -- construction for finite subsets, which are the natural finite stages of a well-order proof.
  rcases exists_refinement_stage_hom_realizing_source_request_list
      (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss' rs.toList with
    ⟨A, h, hA⟩
  refine ⟨A, h, ?_⟩
  intro r hr
  exact hA (by simpa using hr)

/-- Helper for Lemma 7.39.2: finite source-frontier form for finite subsets, retaining the
compatibility datum needed by later direct-union arguments. -/
theorem exists_refinement_stage_hom_realizing_source_request_finset_compatible
    [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') (rs : Finset (finite_cover_lift_request J S')) :
    ∃ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∃ h : refinement_stage_hom (J := J)
        (base_refinement_stage (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss') A,
        h.original_compatible ∧
          ∀ ⦃r : finite_cover_lift_request J S'⦄, r ∈ rs →
            request_realized (J := J) (h.map_request r) := by
  rcases exists_refinement_stage_hom_realizing_source_request_list_compatible
      (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss' rs.toList with
    ⟨A, h, hcompat, hA⟩
  refine ⟨A, h, hcompat, ?_⟩
  intro r hr
  exact hA (by simpa using hr)

end

end CategoryTheory
