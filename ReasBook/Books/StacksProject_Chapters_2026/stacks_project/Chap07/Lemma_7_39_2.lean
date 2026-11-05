module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_8_2
public import stacks_project.Chap07.Lemma_7_39_1
public import stacks_project.Chap07.Lemma_7_39_2.Index

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

section

variable {J : GrothendieckTopology C}

/-
Domain-style sampling for Lemma 7.39.2:
- primary domain: fibers of cofiltered inverse systems on a site and lifting along finite covering
  families;
- sampled owner API:
  `Functor.presheafFiber`,
  `GrothendieckTopology.Point.ofIsCofiltered.fiber`,
  `GrothendieckTopology.Point.ofIsCofiltered.refinementFiber`,
  `SemiRepresentableFamily.Over`,
  `SemiRepresentableFamily.Over.toSieve`;
- source/core/bridge triage:
  `source-facing`: a directed inverse system together with the requirement that, after refinement,
  every finite covering family lifts elements of its canonical fiber functor;
  `core/canonical`: `ofIsCofiltered.fiber` for the inverse-system fiber and
  `SemiRepresentableFamily.Over` for explicit fixed-target covering families;
  `bridge/view`: the refinement datum
  `S' ≅ (j.toOrderHom.toFunctor).op ⋙ T` and the induced natural transformation
  `refinementFiber`, together with its objectwise and raw-stalk applications.

Primitive data are only the inverse systems, the refinement datum, and the finite covering family
itself. The chapter already treats explicit covering families through `SemiRepresentableFamily.Over`
rather than the raw triple `(κ, Wk, π)`, so this file should reuse that owner and derive the
lifting clause from it instead of keeping a parallel coordinate-level encoding.
-/
open GrothendieckTopology.Point.ofIsCofiltered

variable {ι : Type w} [Preorder ι]

/-- Helper for Lemma 7.39.2: once an omega tower has coherent maps to a limit stage and every
limit request descends to a finite stage, the successor-stage realization invariant realizes every
request on the limit. -/
theorem omegaLimitStageRealizesAllRequests
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : ℕ → refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (step : ∀ n, refinement_stage_hom (J := J) (A n) (A (n + 1)))
    (L : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (toLimit : ∀ n, refinement_stage_hom (J := J) (A n) L)
    (step_realizes :
      ∀ n (r : finite_cover_lift_request J (A n).T),
        request_realized (J := J) ((step n).map_request r))
    (toLimit_succ :
      ∀ n (r : finite_cover_lift_request J (A n).T),
        (toLimit n).map_request r =
          (toLimit (n + 1)).map_request ((step n).map_request r))
    (descends :
      ∀ r : finite_cover_lift_request J L.T,
        ∃ n, ∃ r0 : finite_cover_lift_request J (A n).T,
          (toLimit n).map_request r0 = r) :
    ∀ r : finite_cover_lift_request J L.T, request_realized (J := J) r := by
  intro r
  rcases descends r with ⟨n, r0, hr0⟩
  -- Realize the finite-stage request after the next successor step.
  have hstep : request_realized (J := J) ((step n).map_request r0) :=
    step_realizes n r0
  -- Transport that realization along the comparison from the successor stage to the limit.
  have hlimit :
      request_realized (J := J)
        ((toLimit (n + 1)).map_request ((step n).map_request r0)) :=
    refinement_stage_hom.map_request_realized (J := J) (toLimit (n + 1))
      ((step n).map_request r0) hstep
  -- Coherence identifies the transported successor request with the descended limit request.
  rw [← toLimit_succ n r0, hr0] at hlimit
  exact hlimit

/-- Helper for Lemma 7.39.2: the remaining source-faithful construction is to produce a terminal
packaged refinement stage whose own finite-cover requests are all realized. -/
theorem exists_terminal_refinement_stage_realizing_all_requests
    [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') :
    ∃ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∀ r : finite_cover_lift_request J A.T, request_realized (J := J) r :=
  -- The stage-aware transfinite/Zorn construction: iterate the inner per-stage saturation
  -- (`advance_compatible`) and take the directed union over `ℕ`.  See
  -- `Lemma_7_39_2/TransfiniteAdvance.lean`.  The `[UnivLE.{max u v w, w}]` hypothesis makes the
  -- scheduled request type small in the stage universe `w` (it is discharged automatically at the
  -- Proposition 7.39.3 call site, where `w = max u v`).
  terminal_refinement_stage_realizing_all_requests (J := J) hss'

/-- Helper for Lemma 7.39.2: a terminal packaged stage that realizes all of its own requests
also realizes every original finite-cover request after transport to that stage. -/
theorem terminalStageRealizesTransportedSourceRequest
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (A : refinement_stage (J := J) S' (ℱ := ℱ) s s')
    (hA : ∀ r : finite_cover_lift_request J A.T, request_realized (J := J) r)
    (r : finite_cover_lift_request J S') :
    request_realized (J := J) (transport_request (J := J) A.j A.T A.e r) := by
  -- The transported source request is one of the terminal stage's own finite-cover requests.
  exact hA (transport_request (J := J) A.j A.T A.e r)

/-- Helper for Lemma 7.39.2: a terminal packaged stage realizing all of its own finite-cover
requests already gives the source-facing lifting target for the original inverse system. -/
theorem terminalStageRealizingAllRequestsYieldsSourceTarget
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
          (_h𝒰 : 𝒰.toSieve ∈ J W) (f : (fiber.{max u v w} S').obj W),
            ∃ i : 𝒰.index, ∃ y : u.obj (𝒰.obj i).left,
              u.map (𝒰.obj i).hom y = (refinementFiber j T e).app W f := by
  -- First turn terminal-stage realization into realization of every transported source request.
  have hsource :
      ∀ r : finite_cover_lift_request J S',
        request_realized (J := J) (transport_request (J := J) A.j A.T A.e r) := by
    intro r
    exact terminalStageRealizesTransportedSourceRequest (J := J) A hA r
  -- The existing source-target adapter now produces exactly the textbook lifting conclusion.
  exact stage_realizing_source_requests_yields_source_target (J := J) (A := A) hsource

/-- Helper for Lemma 7.39.2: a terminal packaged stage realizing all of its own finite-cover
requests gives the strengthened final-fiber lifting target. -/
theorem terminalStageRealizingAllRequestsYieldsFinalTarget
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
          (_h𝒰 : 𝒰.toSieve ∈ J W) (f : u.obj W),
            ∃ i : 𝒰.index, ∃ y : u.obj (𝒰.obj i).left, u.map (𝒰.obj i).hom y = f := by
  -- The packaged-stage adapter turns the terminal stage into the strengthened target directly.
  exact stage_realizing_all_requests_yields_target (J := J) (A := A) hA

/-- Helper for Lemma 7.39.2: a terminal packaged refinement stage realizes every original
finite-cover request after transporting it to that terminal stage. -/
theorem terminal_refinement_stage_realizes_source_requests
    [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') :
    ∃ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∀ r : finite_cover_lift_request J S',
        request_realized (J := J) (transport_request (J := J) A.j A.T A.e r) := by
  -- First obtain the terminal stage realizing all requests on its own refined inverse system.
  rcases exists_terminal_refinement_stage_realizing_all_requests
      (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss' with
    ⟨A, hA⟩
  -- Source requests are a special case after transport along the terminal refinement data.
  exact ⟨A, fun r => terminalStageRealizesTransportedSourceRequest (J := J) A hA r⟩

/-- Source-facing terminal package for Stacks tag `00YP`: it is enough for the final stage to
realize every finite-cover request transported from the original inverse system. This separates
the source-faithful statement from the stronger final-fiber closure used downstream. -/
theorem exists_refinement_stage_realizing_source_requests
    [UnivLE.{max u v w, w}] [IsDirected ι (· ≤ ·)] [Limits.HasPullbacks C]
    {ℱ : Sheaf J (Type (max u v w))}
    {S' : ιᵒᵖ ⥤ C}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') :
    ∃ A : refinement_stage (J := J) S' (ℱ := ℱ) s s',
      ∀ r : finite_cover_lift_request J S',
        request_realized (J := J) (transport_request (J := J) A.j A.T A.e r) := by
  -- Reuse the terminal-stage adapter so the source-facing theorem stays a direct projection of
  -- the stronger terminal realization statement.
  exact terminal_refinement_stage_realizes_source_requests
    (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss'

/-- Strengthened technical variant of Lemma 7.39.2 used by Proposition 7.39.3: the final refined
fiber functor itself lifts every element through finite covering families. This is stronger than
the source statement, which only asks for elements coming from the original system. -/
theorem exists_refined_inverse_system_separating_sections_and_lifting_all_final_finite_covers
    [Limits.HasPullbacks C]
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [UnivLE.{max u v w, w}] (S' : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      let u := fiber.{max u v w} T
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{w} W) [Finite 𝒰.index]
          (_h𝒰 : 𝒰.toSieve ∈ J W) (f : u.obj W),
            ∃ i : 𝒰.index, ∃ y : u.obj (𝒰.obj i).left, u.map (𝒰.obj i).hom y = f := by
  rcases exists_terminal_refinement_stage_realizing_all_requests
      (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss' with
    ⟨A, hA⟩
  -- Project the terminal stage through the final-fiber adapter.
  exact terminalStageRealizingAllRequestsYieldsFinalTarget (J := J) A hA

-- Proof sketch: well-order the class of pairs consisting of a finite covering family and an
-- element of `u'(W)`, then iterate Lemma 7.39.1 by transfinite recursion so that each stage
-- preserves the separation of `s` and `s'` while forcing the lifting condition for the next pair.
-- The directed union of the resulting chain is again a refinement of the original directed system,
-- and the induced canonical maps still separate `s` and `s'` while satisfying the required
-- finite-cover lifting property for every stage of the well-order.
/-- Lemma 7.39.2: given a directed inverse system on a site and two distinct elements of the
canonical raw sheaf fiber
`(sheafToPresheaf J (Type _) ⋙ (GrothendieckTopology.Point.ofIsCofiltered.fiber S').presheafFiber).obj ℱ`
of a sheaf, there exists a refinement of the inverse system whose induced canonical map on sheaf
fibers still separates those elements and whose refined object fiber functor has the property that
every element coming from the original object fiber lifts through some member of any finite
covering family after transport to the refinement. -/
theorem exists_refined_inverse_system_separating_sections_and_lifting_all_finite_covers
    [Limits.HasPullbacks C]
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] [UnivLE.{max u v w, w}] (S' : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      let u := fiber.{max u v w} T
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{w} W) [Finite 𝒰.index]
          (_h𝒰 : 𝒰.toSieve ∈ J W) (f : (fiber.{max u v w} S').obj W),
            ∃ i : 𝒰.index, ∃ y : u.obj (𝒰.obj i).left,
              u.map (𝒰.obj i).hom y = (refinementFiber j T e).app W f := by
  -- Reduce the source-facing theorem to the source request package, matching Stacks tag `00YP`.
  rcases exists_terminal_refinement_stage_realizing_all_requests
      (J := J) (S' := S') (ℱ := ℱ) (s := s) (s' := s') hss' with
    ⟨A, hA⟩
  -- A terminal stage realizing all of its own requests directly yields the source-facing target.
  exact terminalStageRealizingAllRequestsYieldsSourceTarget (J := J) A hA

end

end CategoryTheory
