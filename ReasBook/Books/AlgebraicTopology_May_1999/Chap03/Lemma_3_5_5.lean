/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import AlgebraicTopology_May_1999.Chap03.Definition_3_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

namespace CategoryTheory.Functor.IsCovering

variable {E E' B : Type u} [Groupoid.{v} E] [Groupoid.{v} E'] [Groupoid.{v} B]
variable [CategoryTheory.IsPreconnected E']
variable {p : E ⥤ B} {p' : E' ⥤ B}

/-- Lemma 3.5.5: if the target total groupoid is preconnected, then a functor between two covering
functors over the same base groupoid is itself a covering functor. -/
-- Proof sketch: surjectivity on objects follows from the commutative triangle
-- `g ⋙ p' = p`, using surjectivity of `p` on objects and then lifting the resulting base
-- isomorphism through the covering `p'`. Bijectivity on each star follows because the square of
-- star maps induced by `g`, `p`, and `p'` commutes, and the star maps for `p` and `p'` are
-- bijections.
theorem of_map_of_coverings (hp : Functor.IsCovering p) (hp' : Functor.IsCovering p')
    (g : E ⥤ E') (hg : g ⋙ p' = p) :
    Functor.IsCovering g := by
  cases hg
  refine ⟨?_, ?_⟩
  · intro e'
    obtain ⟨e, he⟩ := hp.obj_surjective (p'.obj e')
    let α : g.obj e ⟶ e' :=
      Classical.choice (CategoryTheory.nonempty_hom_of_preconnected_groupoid (g.obj e) e')
    obtain ⟨x, hx⟩ := (hp.star_bijective e).surjective (Under.mk (p'.map α))
    have hxg : (Under.post g).obj x = Under.mk α := by
      apply (hp'.star_bijective (g.obj e)).injective
      simpa [Functor.comp_map] using hx
    refine ⟨x.right, ?_⟩
    simpa using congrArg (fun u : Under (g.obj e) ↦ u.right) hxg
  · intro e
    refine ⟨?_, ?_⟩
    · intro u v h
      obtain ⟨_, fu, rfl⟩ := Under.mk_surjective u
      obtain ⟨_, fv, rfl⟩ := Under.mk_surjective v
      apply (hp.star_bijective e).injective
      have h' := congrArg (fun x ↦ (Under.post p').obj x) h
      simpa [Functor.comp_map] using h'
    · intro y
      obtain ⟨_, fy, rfl⟩ := Under.mk_surjective y
      obtain ⟨x, hx⟩ := (hp.star_bijective e).surjective (Under.mk (p'.map fy))
      refine ⟨x, ?_⟩
      apply (hp'.star_bijective (g.obj e)).injective
      simpa [Functor.comp_map] using hx

end CategoryTheory.Functor.IsCovering
