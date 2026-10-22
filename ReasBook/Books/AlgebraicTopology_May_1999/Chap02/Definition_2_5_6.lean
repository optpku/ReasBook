/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

open CategoryTheory

/- Definition 2.5.6: the canonical notion of a connected category is
`CategoryTheory.IsConnected`; in a nonempty category this is equivalent to saying that any two
objects are linked by a zigzag of morphisms, and for a groupoid it is equivalent to saying that
any two objects are isomorphic. -/
recall CategoryTheory.IsConnected (J : Type u) [Category.{v} J] : Prop

/-- A nonempty category is connected exactly when any two objects are linked by a zigzag of
morphisms. -/
theorem isConnected_iff_zigzag (J : Type u) [Category.{v} J] [Nonempty J] :
    IsConnected J ↔ ∀ j₁ j₂ : J, Zigzag j₁ j₂ := by
  constructor
  · intro h j₁ j₂
    let _ : IsConnected J := h
    exact isPreconnected_zigzag j₁ j₂
  · exact zigzag_isConnected

/-- A nonempty groupoid is connected exactly when any two objects are isomorphic. -/
theorem groupoid_isConnected_iff_isomorphic (G : Type u) [Groupoid.{v} G] [Nonempty G] :
    IsConnected G ↔ ∀ x y : G, Nonempty (x ≅ y) := by
  constructor
  · intro h x y
    let _ : IsConnected G := h
    simpa using
      Nonempty.map ((Groupoid.isoEquivHom x y).symm) (nonempty_hom_of_preconnected_groupoid x y)
  · intro h
    exact zigzag_isConnected fun x y ↦ by
      rcases h x y with ⟨e⟩
      exact Zigzag.of_hom e.hom
