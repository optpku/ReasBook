/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_3_7
import AlgebraicTopology_May_1999.Chap03.Proposition_3_3_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory FundamentalGroupoid

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsPathConnectedCoveringMap

variable {p : E → B}

/-- Fiber translation on ordinary fibers, obtained by transporting the categorical fiber
translation for `hp.fundamentalGroupoidMap` across the canonical fiber equivalences of
Proposition 3.3.4. -/
noncomputable abbrev fiberTranslationMap (hp : IsPathConnectedCoveringMap p) {b₀ b₁ : B}
    (f : mk b₀ ⟶ mk b₁) : p ⁻¹' {b₀} → p ⁻¹' {b₁} :=
  hp.fundamentalGroupoidMapFiberEquiv b₁ ∘
    Functor.IsCovering.fiberTranslationMap hp.fundamentalGroupoidMap_isCovering f ∘
    (hp.fundamentalGroupoidMapFiberEquiv b₀).symm

@[simp] theorem fiberTranslationMap_apply (hp : IsPathConnectedCoveringMap p) {b₀ b₁ : B}
    (f : mk b₀ ⟶ mk b₁) (e : p ⁻¹' {b₀}) :
    hp.fiberTranslationMap f e =
      hp.fundamentalGroupoidMapFiberEquiv b₁
        (Functor.IsCovering.fiberTranslationMap hp.fundamentalGroupoidMap_isCovering f
          ((hp.fundamentalGroupoidMapFiberEquiv b₀).symm e)) :=
  rfl

/-- Helper for Example 3.3.9: changing the endpoint of a path class only changes the codomain
bookkeeping of the corresponding `Under.mk` object. -/
private theorem under_mk_fromPath_cast_eq {x y z : B} (q : Path.Homotopic.Quotient x z)
    (h : y = z) :
    (Under.mk (fromPath q) : Under (mk x)) = Under.mk (fromPath (q.cast rfl h)) := by
  -- Collapse the endpoint transport to the reflexive case.
  cases h
  simp

/-- Helper for Example 3.3.9: the projected class of the canonical lifted path is the original
base path class after the endpoint cast coming from `liftPath_lifts`. -/
private theorem lifted_path_projects_to_base_class (hp : IsPathConnectedCoveringMap p)
    {e : E} {b : B} (γ : Path (p e) b) :
    ((Path.Homotopic.Quotient.mk
        (Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
          (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl)).map
      ⟨p, hp.isCoveringMap.continuous⟩).cast rfl
      ((congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans γ.target).symm =
        Path.Homotopic.Quotient.mk γ := by
  -- Rewrite the quotient statement back to an equality of actual paths.
  change Path.Homotopic.Quotient.mk
      (((Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
        (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl).map
          hp.isCoveringMap.continuous).cast rfl
        ((congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans γ.target).symm) =
      Path.Homotopic.Quotient.mk γ
  -- The covering projection of the lifted path agrees pointwise with `γ`.
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  simpa using congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) t

/-- Helper for Example 3.3.9: the categorical star lift of a path class is the under-object
represented by the actual lifted path starting at the chosen point. -/
private theorem starLift_fromPath_eq_lifted_under (hp : IsPathConnectedCoveringMap p)
    {e : E} {b : B} (γ : Path (p e) b) :
    Functor.IsCovering.starLift hp.fundamentalGroupoidMap_isCovering
      (fromPath (.mk γ)) ⟨mk e, rfl⟩ =
      Under.mk
        (fromPath
          (Path.Homotopic.Quotient.mk
            (Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
              (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl))) := by
  let δ : Path e (hp.isCoveringMap.liftPath γ e γ.source 1) :=
    Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
      (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl
  suffices htarget :
      Functor.IsCovering.starLift hp.fundamentalGroupoidMap_isCovering
        (fromPath (.mk γ)) ⟨mk e, rfl⟩ =
        Under.mk (fromPath (Path.Homotopic.Quotient.mk δ)) by
    simpa [δ] using htarget
  have hpost_explicit :
      (Under.post hp.fundamentalGroupoidMap).obj
          (Under.mk (fromPath (Path.Homotopic.Quotient.mk δ))) =
        (Under.mk
          (fromPath ((Path.Homotopic.Quotient.mk δ).map ⟨p, hp.isCoveringMap.continuous⟩)) :
            Under (mk (p e))) := by
    -- Applying `Under.post` to the explicit lifted path unfolds directly to the projected class.
    rfl
  have hpost_target :
      Under.mk (fromPath (.mk γ)) =
        (Under.post hp.fundamentalGroupoidMap).obj
          (Under.mk (fromPath (Path.Homotopic.Quotient.mk δ))) := by
    -- The projected lifted path represents the same base class as `γ`, up to the endpoint cast.
    calc
      Under.mk (fromPath (.mk γ)) = Under.mk
          (fromPath
            (((Path.Homotopic.Quotient.mk δ).map ⟨p, hp.isCoveringMap.continuous⟩).cast rfl
              ((congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans
                γ.target).symm)) := by
        symm
        exact congrArg Under.mk
          (congrArg fromPath (lifted_path_projects_to_base_class hp γ))
      _ = Under.mk
            (fromPath ((Path.Homotopic.Quotient.mk δ).map ⟨p, hp.isCoveringMap.continuous⟩)) := by
        symm
        exact under_mk_fromPath_cast_eq _
          ((congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans γ.target).symm
      _ = (Under.post hp.fundamentalGroupoidMap).obj
            (Under.mk (fromPath (Path.Homotopic.Quotient.mk δ))) := by
        exact hpost_explicit.symm
  -- Compare the chosen star lift with the explicit lifted path after applying `Under.post`.
  apply (hp.fundamentalGroupoidMap_isCovering.star_bijective (mk e)).injective
  exact
    (Functor.IsCovering.starLift_post_eq hp.fundamentalGroupoidMap_isCovering
      (fromPath (.mk γ)) ⟨mk e, rfl⟩).trans hpost_target

/-- Helper for Example 3.3.9: fiber translation along a represented path class lands at the
endpoint of the corresponding lifted path. -/
private theorem fiberTranslationMap_fromPath_eq_endpoint (hp : IsPathConnectedCoveringMap p)
    {e : E} {b : B} (γ : Path (p e) b) :
    hp.fiberTranslationMap (fromPath (.mk γ)) ⟨e, rfl⟩ =
      ⟨hp.isCoveringMap.liftPath γ e γ.source 1,
        (congr_fun (hp.isCoveringMap.liftPath_lifts γ e γ.source) 1).trans γ.target⟩ := by
  let δ : Path e (hp.isCoveringMap.liftPath γ e γ.source 1) :=
    Path.mk (hp.isCoveringMap.liftPath γ e γ.source)
      (hp.isCoveringMap.liftPath_zero γ e γ.source) rfl
  -- Transport the claim into the categorical fiber, where the star-lift description is explicit.
  apply (hp.fundamentalGroupoidMapFiberEquiv b).symm.injective
  apply Subtype.ext
  -- Equality of lifted under-objects identifies the endpoint object in the fundamental groupoid.
  simpa [IsPathConnectedCoveringMap.fiberTranslationMap, δ] using
    congrArg Comma.right (starLift_fromPath_eq_lifted_under hp γ)

/-- Example 3.3.9: for a covering space, the fiber-translation map along a path class agrees with
the monodromy map sending a chosen lift of the starting point to the endpoint of the lifted path
class. -/
-- Proof sketch: transport the categorical fiber of `hp.fundamentalGroupoidMap` to the ordinary
-- fiber `p ⁻¹' {b}` via `fundamentalGroupoidMapFiberEquiv`, then compare the resulting map with the
-- canonical monodromy functor of `hp.isCoveringMap`; both send a starting point in the fiber to
-- the endpoint of the unique lifted path class.
theorem fiberTranslationMap_eq_monodromy (hp : IsPathConnectedCoveringMap p)
    {b₀ b₁ : B} (f : mk b₀ ⟶ mk b₁) :
    hp.fiberTranslationMap f = hp.isCoveringMap.monodromy f := by
  funext x
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective f
  rcases x with ⟨e, rfl⟩
  -- Compare both maps on a literal basepoint fiber by the explicit lifted-path formula.
  rw [fiberTranslationMap_fromPath_eq_endpoint hp γ]
  rfl

/-- Evaluating fiber translation on the homotopy class of a path gives the endpoint of the lifted
representative path starting at the chosen point of the fiber. -/
-- Proof sketch: specialize `fiberTranslationMap_eq_monodromy` to the morphism
-- `fromPath (.mk γ)` and then apply mathlib's endpoint formula
-- `hp.isCoveringMap.monodromy_map (.mk γ)`.
theorem fiberTranslationMap_fromPath_eq_liftPath_endpoint
    (hp : IsPathConnectedCoveringMap p) {b₀ b₁ : B} (γ : Path b₀ b₁) (e : p ⁻¹' {b₀}) :
    hp.fiberTranslationMap (fromPath (.mk γ)) e =
      ⟨hp.isCoveringMap.liftPath γ e.1 (γ.source.trans e.2.symm) 1,
        (congr_fun (hp.isCoveringMap.liftPath_lifts γ e.1 (γ.source.trans e.2.symm)) 1).trans
          γ.target⟩ := by
  rcases e with ⟨e, rfl⟩
  -- After normalizing the fiber point to `⟨e, rfl⟩`, the private path-level helper applies.
  simpa using fiberTranslationMap_fromPath_eq_endpoint hp γ

end IsPathConnectedCoveringMap
