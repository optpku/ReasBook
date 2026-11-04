/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_21.ClassCoNP
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_24.Reduction

public section

/-- A decision problem `Q` is co-NP-hard when every decision problem in `co-NP` admits a
polynomial-time many-one reduction to `Q`. -/
def DecisionProblem.isCoNPHard (Q : DecisionProblem) : Prop :=
  ∀ D : DecisionProblem, D.inCoNP → Nonempty (PolynomialTimeManyOneReduction D Q)

namespace DecisionProblem

/-- A witness packaging `co-NP` membership and co-NP-hardness for a decision problem. -/
structure IsCoNPComplete (Q : DecisionProblem) : Prop where
  inCoNP : Q.inCoNP
  isCoNPHard : Q.isCoNPHard

namespace IsCoNPComplete

variable {Q : DecisionProblem}

/-- Build a co-NP-completeness witness from separate `co-NP` membership and co-NP-hardness
proofs. -/
def ofParts
    (h_inCoNP : Q.inCoNP)
    (h_isCoNPHard : Q.isCoNPHard) :
    DecisionProblem.IsCoNPComplete Q where
  inCoNP := h_inCoNP
  isCoNPHard := h_isCoNPHard

end IsCoNPComplete

/-- Definition 1.24. A decision problem `Q` is co-NP-complete if it belongs to `co-NP` and every
decision problem in `co-NP` admits a polynomial-time many-one reduction to `Q` preserving
yes-instances. -/
abbrev isCoNPComplete (Q : DecisionProblem) : Prop :=
  DecisionProblem.IsCoNPComplete Q

/-- Expanding `Q.isCoNPComplete` exposes its `co-NP` membership and universal many-one reduction
components. -/
theorem isCoNPComplete_spec
    (Q : DecisionProblem) :
    Q.isCoNPComplete ↔
      Q.inCoNP ∧
        ∀ D : DecisionProblem, D.inCoNP → Nonempty (PolynomialTimeManyOneReduction D Q) := by
  constructor
  · intro hQ
    exact ⟨hQ.inCoNP, hQ.isCoNPHard⟩
  · rintro ⟨h_inCoNP, h_isCoNPHard⟩
    exact IsCoNPComplete.ofParts h_inCoNP h_isCoNPHard

/-- `Q.isCoNPHard` means that every decision problem in `co-NP` admits a polynomial-time many-one
reduction to `Q`. -/
theorem isCoNPHard_iff
    (Q : DecisionProblem) :
    Q.isCoNPHard ↔
      ∀ D : DecisionProblem, D.inCoNP → Nonempty (PolynomialTimeManyOneReduction D Q) :=
  Iff.rfl

/-- Expanding `Q.isCoNPComplete` recalls its `co-NP` membership and hardness components. -/
theorem isCoNPComplete_def
    (Q : DecisionProblem) :
    Q.isCoNPComplete ↔ (Q.inCoNP ∧ Q.isCoNPHard) := by
  constructor
  · intro hQ
    exact ⟨hQ.inCoNP, hQ.isCoNPHard⟩
  · rintro ⟨h_inCoNP, h_isCoNPHard⟩
    exact IsCoNPComplete.ofParts h_inCoNP h_isCoNPHard

/-- `Q.isCoNPComplete` means that `Q` lies in `co-NP` and every decision problem in `co-NP`
polynomial-time many-one reduces to `Q`. -/
theorem isCoNPComplete_iff
    (Q : DecisionProblem) :
    Q.isCoNPComplete ↔
      Q.inCoNP ∧
        ∀ D : DecisionProblem, D.inCoNP → Nonempty (PolynomialTimeManyOneReduction D Q) :=
  isCoNPComplete_spec Q

end DecisionProblem
