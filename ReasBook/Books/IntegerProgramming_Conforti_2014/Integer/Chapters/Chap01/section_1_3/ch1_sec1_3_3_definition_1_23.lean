module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_24.Reduction
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_definition_1_25.Hardness

public section

namespace DecisionProblem

/-- A decision problem `Q` is NP-hard when every decision problem in `NP` admits a
polynomial-time many-one reduction to `Q`. -/
def isNPHard (Q : DecisionProblem) : Prop :=
  ∀ D : DecisionProblem, D.inNP → Nonempty (PolynomialTimeManyOneReduction D Q)

/-- A witness packaging `NP` membership and NP-hardness for a decision problem. -/
structure IsNPComplete (Q : DecisionProblem) : Prop where
  inNP : Q.inNP
  isNPHard : Q.isNPHard

namespace IsNPComplete

variable {Q : DecisionProblem}

/-- Build an NP-completeness witness from separate `NP` membership and NP-hardness proofs. -/
def ofParts
    (h_inNP : Q.inNP)
    (h_isNPHard : Q.isNPHard) :
    DecisionProblem.IsNPComplete Q where
  inNP := h_inNP
  isNPHard := h_isNPHard

end IsNPComplete

/-- Definition 1.23. A decision problem `Q` is NP-complete if it belongs to `NP` and every
decision problem in `NP` admits a polynomial-time many-one reduction to `Q` preserving the
correct yes-answer on each instance. -/
abbrev isNPComplete (Q : DecisionProblem) : Prop :=
  DecisionProblem.IsNPComplete Q

/-- Expanding `Q.isNPComplete` exposes its `NP` membership and universal many-one reduction
components. -/
theorem isNPComplete_spec
    (Q : DecisionProblem) :
    Q.isNPComplete ↔
      Q.inNP ∧
        ∀ D : DecisionProblem, D.inNP → Nonempty (PolynomialTimeManyOneReduction D Q) := by
  constructor
  · intro hQ
    -- Read the NP-completeness witness as its membership and hardness fields.
    exact ⟨hQ.inNP, hQ.isNPHard⟩
  · rintro ⟨h_inNP, h_isNPHard⟩
    -- Repackage the two components into the canonical structure witness.
    exact IsNPComplete.ofParts h_inNP h_isNPHard

/-- Expanding `Q.isNPHard` recalls the canonical many-one reduction owner. -/
theorem isNPHard_def
    (Q : DecisionProblem) :
    Q.isNPHard =
      (∀ D : DecisionProblem, D.inNP → Nonempty (PolynomialTimeManyOneReduction D Q)) := by
  -- This is the defining equation of `DecisionProblem.isNPHard`.
  rfl

/-- `Q.isNPHard` means that every decision problem in `NP` admits a polynomial-time many-one
reduction to `Q`. -/
theorem isNPHard_iff
    (Q : DecisionProblem) :
    Q.isNPHard ↔
      ∀ D : DecisionProblem, D.inNP → Nonempty (PolynomialTimeManyOneReduction D Q) := by
  -- The iff form is the same proposition as the definitional expansion.
  exact Iff.rfl

/-- Expanding `Q.isNPComplete` recalls its `NP` membership and hardness components. -/
theorem isNPComplete_def
    (Q : DecisionProblem) :
    Q.isNPComplete ↔ (Q.inNP ∧ Q.isNPHard) := by
  constructor
  · intro hQ
    -- Read the NP-completeness witness through its two structure fields.
    exact ⟨hQ.inNP, hQ.isNPHard⟩
  · rintro ⟨h_inNP, h_isNPHard⟩
    -- Reassemble the witness from the canonical parts constructor.
    exact IsNPComplete.ofParts h_inNP h_isNPHard

/-- `Q.isNPComplete` means that `Q` lies in `NP` and every decision problem in `NP`
polynomial-time many-one reduces to `Q`. -/
theorem isNPComplete_iff
    (Q : DecisionProblem) :
    Q.isNPComplete ↔
      Q.inNP ∧
        ∀ D : DecisionProblem, D.inNP → Nonempty (PolynomialTimeManyOneReduction D Q) := by
  -- Reuse the already-proved structural expansion.
  exact isNPComplete_spec Q

/-- Any NP-complete decision problem is NP-hard when viewed as a computational problem. -/
theorem isNPHard_of_isNPComplete
    {Q : DecisionProblem} :
    Q.isNPComplete → Q.toProblem.isNPHard := by
  intro hQ D hD
  -- Convert the many-one reduction supplied by NP-completeness into an answer reduction.
  rcases hQ.isNPHard D hD with ⟨f⟩
  exact ⟨f.toAnswerReduction⟩

end DecisionProblem
