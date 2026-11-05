/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_16.Blocker

public section

universe u

namespace SteinerTripleSystem

variable {α : Type u} [DecidableEq α] (E : Finset α) (S : Set (Finset α))

/- Definition 2.27 [Cover of a Steiner triple system]. Given a Steiner triple system `(E, S)`, a
cover is formalized by `Clutter.IsTransversal E S`: a finite subset of `E` meeting every triple in
`S`. The Steiner axioms belong to the ambient structure on `(E, S)`, not to the cover predicate
itself. -/
#check (Clutter.IsTransversal E S : Finset α → Prop)

/-- Unfolding the canonical cover predicate recovers the textbook condition: a finite subset of
`E` meeting every triple in `S`. -/
theorem cover_iff {T : Finset α} :
    Clutter.IsTransversal E S T ↔ T ⊆ E ∧ ∀ s ∈ S, (T ∩ s).Nonempty := by
  simpa [Finset.inter_comm] using
    (Clutter.isTransversal_iff :
      Clutter.IsTransversal E S T ↔ T ⊆ E ∧ ∀ s ∈ S, (s ∩ T).Nonempty)

end SteinerTripleSystem
