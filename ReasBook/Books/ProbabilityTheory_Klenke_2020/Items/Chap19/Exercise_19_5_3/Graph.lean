/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23

open SimpleGraph

noncomputable section

namespace ProbabilityTheory

/- Source repair note for Exercise 19.5.3:
- Fig. 19.15 is modeled here as the bi-infinite ladder graph on `ℤ × Fin 2`, with the marked
  vertices `a` and `z` the two endpoints of the rung over `0`.
- The finite seven-column helper from `Exercise_19_5_LadderGraphs` is a useful approximation, but
  it does not satisfy the source constants `√3` and `1 / √3`. The source-facing statement in this
  file therefore uses the bi-infinite figure directly. -/

/-- The vertex set of Fig. 19.15, realized as the bi-infinite ladder `ℤ × {0, 1}`. -/
abbrev fig19_15SimpleLadderVertex : Type := ℤ × Fin 2

/-- The simple ladder graph of Fig. 19.15: vertices in the same row are connected across adjacent
columns, and each column has its vertical rung. -/
def fig19_15SimpleLadderGraph : SimpleGraph fig19_15SimpleLadderVertex where
  Adj x y :=
    (x.1 = y.1 ∧ (pathGraph 2).Adj x.2 y.2) ∨
      (x.2 = y.2 ∧ |x.1 - y.1| = 1)
  symm x y := by
    rintro (hxy | hxy)
    · left
      exact ⟨hxy.1.symm, by simpa [adj_comm] using hxy.2⟩
    · right
      exact ⟨hxy.1.symm, by simpa [abs_sub_comm] using hxy.2⟩
  loopless := ⟨by
    intro x hx
    rcases hx with (⟨_, hvertical⟩ | ⟨_, hhorizontal⟩)
    · simp at hvertical
    · simp at hhorizontal⟩

/-- Companion API for `fig19_15SimpleLadderGraph`: adjacency is either the vertical rung in a
fixed column or a horizontal edge in a fixed row between neighboring columns. -/
theorem fig19_15SimpleLadderGraph_adj_iff (x y : fig19_15SimpleLadderVertex) :
    fig19_15SimpleLadderGraph.Adj x y ↔
      (x.1 = y.1 ∧ (pathGraph 2).Adj x.2 y.2) ∨
        (x.2 = y.2 ∧ |x.1 - y.1| = 1) := by
  change
    ((x.1 = y.1 ∧ (pathGraph 2).Adj x.2 y.2) ∨ (x.2 = y.2 ∧ |x.1 - y.1| = 1)) ↔
      ((x.1 = y.1 ∧ (pathGraph 2).Adj x.2 y.2) ∨ (x.2 = y.2 ∧ |x.1 - y.1| = 1))
  rfl

/-- The distinguished upper vertex `a` of Fig. 19.15. -/
abbrev fig19_15SimpleLadderA : fig19_15SimpleLadderVertex := (0, ⟨1, by decide⟩)

/-- The distinguished lower vertex `z` of Fig. 19.15. -/
abbrev fig19_15SimpleLadderZ : fig19_15SimpleLadderVertex := (0, ⟨0, by decide⟩)

end ProbabilityTheory
