/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Finite

public section

namespace SimpleGraph

universe u

variable {V : Type u}

/-- A vertex side `S` is an `s,t`-cut side when it contains `s` and excludes `t`. -/
def IsSTCutSide (s t : V) (S : Finset V) : Prop :=
  s ∈ S ∧ t ∉ S

/-- Membership in `IsSTCutSide s t S` means exactly that `S` contains `s` and omits `t`. -/
theorem isSTCutSide_iff {s t : V} {S : Finset V} :
    SimpleGraph.IsSTCutSide s t S ↔ s ∈ S ∧ t ∉ S := by
  rfl

/-- A vertex side `S` is a proper cut side when both sides of the cut are nonempty. -/
def IsProperCutSide [Fintype V] [DecidableEq V] (S : Finset V) : Prop :=
  S.Nonempty ∧ S ≠ Finset.univ

/-- Membership in `IsProperCutSide S` means exactly that `S` is nonempty and not all vertices. -/
theorem isProperCutSide_iff [Fintype V] [DecidableEq V] {S : Finset V} :
    SimpleGraph.IsProperCutSide S ↔ S.Nonempty ∧ S ≠ Finset.univ := by
  rfl

/-- An `s,t`-cut side is automatically a proper cut side. -/
theorem IsSTCutSide.isProperCutSide [Fintype V] [DecidableEq V]
    {s t : V} {S : Finset V} (hS : SimpleGraph.IsSTCutSide s t S) :
    SimpleGraph.IsProperCutSide S := by
  rw [SimpleGraph.isSTCutSide_iff] at hS
  rw [SimpleGraph.isProperCutSide_iff]
  refine ⟨⟨s, hS.1⟩, ?_⟩
  intro hEq
  exact hS.2 (by simp [hEq])

/-- The complementary vertex side of `S` inside a finite vertex set. -/
def cutComplement [Fintype V] [DecidableEq V] (S : Finset V) : Finset V :=
  Finset.univ \ S

/-- `cutComplement S` is the finset difference `Finset.univ \ S`. -/
theorem cutComplement_eq_sdiff [Fintype V] [DecidableEq V]
    (S : Finset V) :
    SimpleGraph.cutComplement S = Finset.univ \ S := by
  rfl

end SimpleGraph

end
