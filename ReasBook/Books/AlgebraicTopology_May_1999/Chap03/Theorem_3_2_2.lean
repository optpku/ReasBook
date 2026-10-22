/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped unitInterval

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace IsCoveringMap

variable {p : E → B}

/-- Theorem 3.2.2: homotopic paths in the base of a covering map starting at `b₀` lift to
homotopic paths in the total space relative to `{0, 1}` from a chosen point `e` over `b₀`. -/
-- Proof sketch: view `h : γ₀.Homotopic γ₁` as a homotopy relative `{0, 1}` of the underlying
-- continuous maps. Then apply `IsCoveringMap.homotopicRel_iff_comp` to the two lifted paths,
-- using `liftPath_zero` to witness that they agree at the initial point.
theorem liftPath_homotopicRel_of_homotopic (hp : IsCoveringMap p) {b₀ b₁ : B}
    {γ₀ γ₁ : Path b₀ b₁} (h : γ₀.Homotopic γ₁) (e : E) (he : p e = b₀) :
    (hp.liftPath γ₀ e (γ₀.source.trans he.symm)).HomotopicRel
      (hp.liftPath γ₁ e (γ₁.source.trans he.symm)) {0, 1} := by
  obtain ⟨H⟩ := h
  refine (hp.homotopicRel_iff_comp ?_).2 ?_
  · exact ⟨0, by simp, by simp [hp.liftPath_zero]⟩
  · convert (show (γ₀ : C(I, B)).HomotopicRel γ₁ {0, 1} from ⟨H⟩) using 1
    · ext t
      exact congr_fun (hp.liftPath_lifts γ₀ e (γ₀.source.trans he.symm)) t
    · ext t
      exact congr_fun (hp.liftPath_lifts γ₁ e (γ₁.source.trans he.symm)) t

/-- Homotopic base paths with the same chosen starting lift have the same lifted endpoint. -/
-- Proof sketch: apply `IsCoveringMap.liftPath_apply_one_eq_of_homotopicRel` to the path homotopy
-- `h`, viewed as a homotopy relative `{0, 1}` of the underlying continuous maps.
theorem liftPath_apply_one_eq_of_homotopic (hp : IsCoveringMap p) {b₀ b₁ : B}
    {γ₀ γ₁ : Path b₀ b₁} (h : γ₀.Homotopic γ₁) (e : E) (he : p e = b₀) :
    hp.liftPath γ₀ e (γ₀.source.trans he.symm) 1 =
      hp.liftPath γ₁ e (γ₁.source.trans he.symm) 1 := by
  obtain ⟨H⟩ := h
  exact hp.liftPath_apply_one_eq_of_homotopicRel ⟨H⟩ e
    (γ₀.source.trans he.symm) (γ₁.source.trans he.symm)

end IsCoveringMap
