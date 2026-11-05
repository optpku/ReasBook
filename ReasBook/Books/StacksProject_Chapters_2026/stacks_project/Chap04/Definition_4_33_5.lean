module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/- Domain-style sampling for Definition 4.33.5:
- primary domain: fibered categories over a base functor.
- inspected owner-level declarations:
  `Functor.IsFibered`,
  `Functor.IsPreFibered.exists_isCartesian`,
  `Functor.IsFibered.isStronglyCartesian_of_isCartesian`,
  `Functor.IsFibered.of_exists_isStronglyCartesian`.
- best owner abstraction: `Functor.IsFibered`.
- primitive data: the functor `p : 𝒮 ⥤ 𝒞` together with the owner predicate `p.IsFibered`,
  whose primitive lift datum is cartesian lift existence.
- derived API: the source-facing characterization by existence of strongly cartesian lifts.

Source/core/bridge triage:
- `source-facing`: the textbook characterization of fibredness by strongly cartesian lifts.
- `core/canonical`: `Functor.IsFibered`.
- `bridge/view`: the theorem `isFibered_iff_exists_isStronglyCartesian`, which translates the
  source phrasing to the canonical owner API without introducing a parallel owner. -/

/- Definition 4.33.5: the Stacks notion that a category over `𝒞` is fibred is the canonical
owner predicate `Functor.IsFibered`. -/
recall IsFibered

-- Proof sketch: one direction uses that in a fibered category every cartesian lift is strongly
-- cartesian, via `Functor.IsFibered.isStronglyCartesian_of_isCartesian` and the chosen lift from
-- `Functor.IsPreFibered.exists_isCartesian`; the converse is the constructor
-- `Functor.IsFibered.of_exists_isStronglyCartesian`.
/- Companion bridge: this source-facing characterization records the textbook strongly cartesian
lift criterion for fibredness. The owner abstraction remains `Functor.IsFibered`; this theorem is
the companion bridge from the source wording to that canonical predicate. -/
theorem isFibered_iff_exists_isStronglyCartesian (p : 𝒮 ⥤ 𝒞) :
    p.IsFibered ↔
      ∀ (x : 𝒮) (V : 𝒞) (f : V ⟶ p.obj x),
        ∃ (fx : 𝒮) (φ : fx ⟶ x), p.IsStronglyCartesian f φ := by
  constructor
  · intro hp x V f
    letI : p.IsFibered := hp
    obtain ⟨fx, φ, hφ⟩ := IsPreFibered.exists_isCartesian p rfl f
    letI : p.IsCartesian f φ := hφ
    exact ⟨fx, φ, IsFibered.isStronglyCartesian_of_isCartesian p f φ⟩
  · exact IsFibered.of_exists_isStronglyCartesian
end Functor
end CategoryTheory
