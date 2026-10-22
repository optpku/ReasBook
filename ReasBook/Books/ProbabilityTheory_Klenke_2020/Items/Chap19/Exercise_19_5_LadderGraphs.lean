/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open SimpleGraph

noncomputable section

namespace ProbabilityTheory

/-- The vertex set shared by the ladder graphs in Figs. 19.15 and 19.16, realized as seven
columns and two rows. -/
abbrev SimpleLadderVertex := Fin 7 × Fin 2

/-- The simple ladder graph of Fig. 19.15, realized as the box product of the seven-vertex path
with the two-vertex path. -/
def simpleLadderGraph : SimpleGraph SimpleLadderVertex :=
  pathGraph 7 □ pathGraph 2

/-- The crossed ladder graph of Fig. 19.16 on the same vertex set. Adjacent columns are completely
joined, and each column still contains its vertical rung. -/
def crossedLadderGraph : SimpleGraph SimpleLadderVertex where
  Adj x y := (pathGraph 7).Adj x.1 y.1 ∨ x.1 = y.1 ∧ (pathGraph 2).Adj x.2 y.2
  symm x y := by
    simp [or_comm, eq_comm, adj_comm]
  loopless := ⟨fun x ↦ by simp⟩

/-- The distinguished top-middle vertex `a` in Figs. 19.15 and 19.16. -/
abbrev simpleLadderA : SimpleLadderVertex := (⟨3, by decide⟩, ⟨1, by decide⟩)

/-- The distinguished bottom-middle vertex `z` in Figs. 19.15 and 19.16. -/
abbrev simpleLadderZ : SimpleLadderVertex := (⟨3, by decide⟩, ⟨0, by decide⟩)

/-- The boundary pair `{a, z}` shared by the ladder exercises. -/
def simpleLadderBoundary : Set SimpleLadderVertex := {simpleLadderA, simpleLadderZ}

end ProbabilityTheory
