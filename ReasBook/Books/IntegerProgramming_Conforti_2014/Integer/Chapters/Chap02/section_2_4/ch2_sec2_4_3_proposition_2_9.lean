/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_17.Blocker
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_proposition_2_9.SetCovering
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_proposition_2_8.DoubleBlocker

public section

namespace SetTransversal

open scoped SetCoveringNotation

/-- Proposition 2.9. If `(S, T)` is a blocking pair of clutters on the finite ground set
`Fin n`, then the minimal-support members of `S^C(incidenceMatrix T)` are exactly the
characteristic vectors `χ_{s}` of the members `s ∈ S`. -/
theorem isMinimalSupportMember_setCoveringFamily_incidenceMatrix_iff
    {n : ℕ} {S T : Finset (Finset (Fin n))}
    (hST : IsBlockingPair S T) {x : Fin n → ℤ} :
    IsMinimalSupportMember (S^C(incidenceMatrix T)) x ↔
      ∃ s ∈ S, x = χ_{s} := by
  have hBlocker :
      Clutter.blocker Finset.univ (T : Set (Finset (Fin n))) = (S : Set (Finset (Fin n))) := by
    calc
      Clutter.blocker Finset.univ (T : Set (Finset (Fin n))) =
          Clutter.blocker Finset.univ
            (Clutter.blocker Finset.univ (S : Set (Finset (Fin n)))) := by
        rw [hST.blocker_eq]
      _ = (S : Set (Finset (Fin n))) := by
        simpa using
          Clutter.blocker_blocker_eq Finset.univ
            (S : Set (Finset (Fin n))) hST.left_isClutter.toIsClutterOn
  have hMinimal :
      IsMinimalSupportMember (S^C(incidenceMatrix T)) x ↔
        ∃ s ∈ Clutter.blocker Finset.univ (T : Set (Finset (Fin n))), x = χ_{s} :=
    isMinimalSupportMember_setCoveringFamily_incidenceMatrix_iff_mem_blocker
  simpa [hBlocker] using
    hMinimal

end SetTransversal
