module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Data.EReal.Basic

@[expose] public section

namespace ADMM

open Set

universe u

/-- A closed proper convex extended-real function, expressed through its epigraph. -/
structure IsClosedProperConvex {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → EReal) : Prop where
  /-- The epigraph is convex. -/
  epigraph_convex : Convex ℝ {p : X × ℝ | f p.1 ≤ (p.2 : EReal)}
  /-- The epigraph is closed. -/
  epigraph_closed : IsClosed {p : X × ℝ | f p.1 ≤ (p.2 : EReal)}
  /-- A proper extended-real function never takes the value `⊥`. -/
  ne_bot : ∀ x, f x ≠ ⊥
  /-- A proper extended-real function is finite somewhere. -/
  exists_ne_top : ∃ x, f x ≠ ⊤

/-- Construct a closed proper convex function from its four epigraph conditions. -/
def IsClosedProperConvex.ofEpigraph {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : X → EReal}
    (epigraph_convex : Convex ℝ {p : X × ℝ | f p.1 ≤ (p.2 : EReal)})
    (epigraph_closed : IsClosed {p : X × ℝ | f p.1 ≤ (p.2 : EReal)})
    (ne_bot : ∀ x, f x ≠ ⊥) (exists_ne_top : ∃ x, f x ≠ ⊤) :
    IsClosedProperConvex f :=
  { epigraph_convex := epigraph_convex
    epigraph_closed := epigraph_closed
    ne_bot := ne_bot
    exists_ne_top := exists_ne_top }

/-- The defining conditions for a closed proper convex extended-real function. -/
theorem IsClosedProperConvex.spec {X : Type u} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {f : X → EReal} (h : IsClosedProperConvex f) :
    Convex ℝ {p : X × ℝ | f p.1 ≤ (p.2 : EReal)} ∧
      IsClosed {p : X × ℝ | f p.1 ≤ (p.2 : EReal)} ∧
      (∀ x, f x ≠ ⊥) ∧ ∃ x, f x ≠ ⊤ := by
  -- Recover each defining condition from the corresponding structure field.
  constructor
  · exact h.epigraph_convex
  · constructor
    · exact h.epigraph_closed
    · constructor
      · exact h.ne_bot
      · exact h.exists_ne_top

end ADMM
