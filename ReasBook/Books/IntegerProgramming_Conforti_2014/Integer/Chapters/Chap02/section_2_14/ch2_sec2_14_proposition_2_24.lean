/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.VertexColoring

public section

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- Feasible assignments of `k` frequencies are exactly `k`-colorings of the interference graph.
-/
theorem frequencyAssignment_feasible_iff_colorable {k : ℕ} :
    (∃ f : V → Fin k, ∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v) ↔ G.Colorable k := by
  constructor
  · rintro ⟨f, hf⟩
    -- Package a feasible assignment as a bundled coloring.
    exact ⟨Coloring.mk f fun hAdj ↦ hf hAdj⟩
  · rintro ⟨C⟩
    -- Read a bundled coloring back as the underlying frequency assignment.
    exact ⟨C, fun {u v} hAdj ↦ C.valid hAdj⟩

/-- Helper for Proposition 2.24: the feasible-assignment index set is the standard colorable set.
-/
lemma feasibleAssignmentSet_eq_colorableSet :
    {k : ℕ | ∃ f : V → Fin k, ∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v} = {k : ℕ | G.Colorable k} := by
  -- Compare membership pointwise using the assignment-coloring bridge.
  ext k
  simp [frequencyAssignment_feasible_iff_colorable (G := G)]

/-- Helper for Proposition 2.24: for finite vertex sets, the infimum of the colorable indices is the
`ℕ`-valued chromatic number.
-/
theorem sInf_colorable_eq_toNat_chromaticNumber [Finite V] (G : SimpleGraph V) :
    sInf {k : ℕ | G.Colorable k} = ENat.toNat G.chromaticNumber := by
  -- Obtain one finite coloring so that the existing `chromaticNumber_eq_sInf` lemma applies.
  cases nonempty_fintype V
  have hColorable : G.Colorable (Fintype.card V) := G.colorable_of_fintype
  -- Transport the `ℕ∞`-valued equality back to `ℕ`.
  simpa [eq_comm] using congrArg ENat.toNat hColorable.chromaticNumber_eq_sInf

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_proposition_2_24.lean.
Proposition 2.24. For an interference graph `G`, the minimum number of frequencies in a
feasible assignment is the `ℕ`-valued chromatic number `ENat.toNat G.chromaticNumber`. -/
theorem frequencyAssignment_min_eq_chromaticNumber [Finite V] (G : SimpleGraph V) :
    sInf {k : ℕ | ∃ f : V → Fin k, ∀ ⦃u v : V⦄, G.Adj u v → f u ≠ f v} =
      ENat.toNat G.chromaticNumber := by
  -- Normalize the feasible-assignment set to the standard colorable set.
  rw [feasibleAssignmentSet_eq_colorableSet (G := G)]
  -- Finish with the `ℕ`-valued chromatic-number characterization.
  exact sInf_colorable_eq_toNat_chromaticNumber G

end SimpleGraph

end
