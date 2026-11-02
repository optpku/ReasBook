module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.TraceEncoding
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_3_theorem_1_4.DPRM.Endpoints
public import Mathlib.Computability.Reduce

public section

namespace QuadraticIntegerFeasibility

namespace LinearTerm

/-- Helper for Theorem 1.4: negating a coded linear monomial keeps its slot and flips only its
coefficient. -/
def negate (term : LinearTerm) : LinearTerm where
  index := term.index
  coefficient := -term.coefficient

/-- Helper for Theorem 1.4: a coded linear term is equivalent to its index-coefficient data. -/
def dataEquiv : LinearTerm ≃ ℕ × ℤ where
  toFun := fun term ↦ (term.index, term.coefficient)
  invFun := fun data ↦ LinearTerm.ofData data.1 data.2
  left_inv := fun term ↦ by cases term; rfl
  right_inv := fun data ↦ by cases data; rfl

/-- Helper for Theorem 1.4: constructing a linear term from its raw data is primitive recursive. -/
lemma primrec_ofData : Primrec fun data : ℕ × ℤ ↦ LinearTerm.ofData data.1 data.2 := by
  exact Primrec.of_equiv_symm (e := dataEquiv)

end LinearTerm

namespace QuadraticTerm

/-- Helper for Theorem 1.4: negating a coded quadratic monomial preserves its two slots and flips
only its coefficient. -/
def negate (term : QuadraticTerm) : QuadraticTerm where
  leftIndex := term.leftIndex
  rightIndex := term.rightIndex
  coefficient := -term.coefficient

end QuadraticTerm

namespace Constraint

/-- Helper for Theorem 1.4: negating a quadratic inequality flips every coefficient so that the new
constraint evaluates to the opposite integer. -/
def negate (constraint : Constraint) : Constraint where
  constant := -constraint.constant
  linearTerms := constraint.linearTerms.map LinearTerm.negate
  quadraticTerms := constraint.quadraticTerms.map QuadraticTerm.negate

/-- Helper for Theorem 1.4: a coded equation is represented by a constraint together with its
opposite inequality. -/
def asEquation (constraint : Constraint) : List Constraint :=
  [constraint, constraint.negate]

/-- Helper for Theorem 1.4: a coded constraint is equivalent to its constant, linear, and
quadratic data. -/
def dataEquiv : Constraint ≃ ℤ × (List LinearTerm × List QuadraticTerm) where
  toFun := fun constraint ↦
    (constraint.constant, (constraint.linearTerms, constraint.quadraticTerms))
  invFun := fun data ↦ Constraint.ofData data.1 data.2.1 data.2.2
  left_inv := fun constraint ↦ by cases constraint; rfl
  right_inv := fun data ↦ by cases data; rfl

/-- Helper for Theorem 1.4: constructing a constraint from its raw data is primitive recursive. -/
lemma primrec_ofData : Primrec fun data : ℤ × (List LinearTerm × List QuadraticTerm) ↦
    Constraint.ofData data.1 data.2.1 data.2.2 := by
  exact Primrec.of_equiv_symm (e := dataEquiv)

end Constraint

namespace Code

/-- Helper for Theorem 1.4: a feasibility code is equivalent to its variable count and
constraint list. -/
def dataEquiv : Code ≃ ℕ × List Constraint where
  toFun := fun code ↦ (code.variableCount, code.constraints)
  invFun := fun data ↦ Code.ofData data.1 data.2
  left_inv := fun code ↦ by cases code; rfl
  right_inv := fun data ↦ by cases data; rfl

/-- Helper for Theorem 1.4: constructing a feasibility code from raw data is primitive recursive. -/
lemma primrec_ofData : Primrec fun data : ℕ × List Constraint ↦
    Code.ofData data.1 data.2 := by
  exact Primrec.of_equiv_symm (e := dataEquiv)

end Code

/-- Helper for Theorem 1.4: recursive evaluation of the coded linear monomials in a constraint. -/
def evalLinearTerms (assignment : List ℤ) : List LinearTerm → ℤ
  | [] => 0
  | term :: terms =>
      term.coefficient * assignment.getD term.index 0 + evalLinearTerms assignment terms

/-- Helper for Theorem 1.4: recursive evaluation of the coded quadratic monomials in a
constraint. -/
def evalQuadraticTerms (assignment : List ℤ) : List QuadraticTerm → ℤ
  | [] => 0
  | term :: terms =>
      term.coefficient * assignment.getD term.leftIndex 0 * assignment.getD term.rightIndex 0 +
        evalQuadraticTerms assignment terms

/-- Helper for Theorem 1.4: the recursive linear-term evaluator agrees with the fold used by
`evalConstraint`. -/
private lemma evalLinearTerms_foldl (terms : List LinearTerm) (assignment : List ℤ) (acc : ℤ) :
    terms.foldl
        (fun current term ↦ current + term.coefficient * assignment.getD term.index 0)
        acc =
      acc + evalLinearTerms assignment terms := by
  induction terms generalizing acc with
  | nil =>
      simp [evalLinearTerms]
  | cons term terms ih =>
      -- Peel off one monomial and regroup the additive accumulator before using the induction
      -- hypothesis on the tail.
      simpa [evalLinearTerms, add_assoc, add_left_comm, add_comm] using
        ih (acc + term.coefficient * assignment.getD term.index 0)

/-- Helper for Theorem 1.4: the recursive quadratic-term evaluator agrees with the fold used by
`evalConstraint`. -/
private lemma evalQuadraticTerms_foldl (terms : List QuadraticTerm) (assignment : List ℤ)
    (acc : ℤ) :
    terms.foldl
        (fun current term ↦
          current + term.coefficient * assignment.getD term.leftIndex 0 *
            assignment.getD term.rightIndex 0)
        acc =
      acc + evalQuadraticTerms assignment terms := by
  induction terms generalizing acc with
  | nil =>
      simp [evalQuadraticTerms]
  | cons term terms ih =>
      -- The quadratic contribution of the head monomial can also be separated from the tail
      -- accumulator before applying the inductive normalization.
      simpa [evalQuadraticTerms, add_assoc, add_left_comm, add_comm] using
        ih (acc + term.coefficient * assignment.getD term.leftIndex 0 *
          assignment.getD term.rightIndex 0)

/-- Helper for Theorem 1.4: `evalConstraint` splits into the constant term plus the recursive
linear and quadratic contributions. -/
lemma evalConstraint_eq (constraint : Constraint) (assignment : List ℤ) :
    evalConstraint constraint assignment =
      constraint.constant +
        evalLinearTerms assignment constraint.linearTerms +
        evalQuadraticTerms assignment constraint.quadraticTerms := by
  -- Normalize both folds so later correctness proofs can reason about one monomial at a time.
  rw [evalConstraint_def, evalLinearTerms_foldl, evalQuadraticTerms_foldl]
  simp [add_assoc]

/-- Helper for Theorem 1.4: negating all coded linear monomials negates their total contribution. -/
private lemma evalLinearTerms_negate (terms : List LinearTerm) (assignment : List ℤ) :
    evalLinearTerms assignment (terms.map LinearTerm.negate) =
      -evalLinearTerms assignment terms := by
  induction terms with
  | nil =>
      simp [evalLinearTerms]
  | cons term terms ih =>
      -- Negation distributes over the head contribution and the already normalized tail.
      simp [evalLinearTerms, LinearTerm.negate, ih, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 1.4: negating all coded quadratic monomials negates their total
contribution. -/
private lemma evalQuadraticTerms_negate (terms : List QuadraticTerm) (assignment : List ℤ) :
    evalQuadraticTerms assignment (terms.map QuadraticTerm.negate) =
      -evalQuadraticTerms assignment terms := by
  induction terms with
  | nil =>
      simp [evalQuadraticTerms]
  | cons term terms ih =>
      -- The quadratic head contribution changes sign exactly once, and so does the normalized
      -- tail contribution.
      simp [evalQuadraticTerms, QuadraticTerm.negate, ih, add_assoc, add_left_comm, add_comm,
        mul_assoc]

/-- Helper for Theorem 1.4: negating a coded inequality negates its evaluation on every
assignment. -/
lemma evalConstraint_negate (constraint : Constraint) (assignment : List ℤ) :
    evalConstraint constraint.negate assignment = -evalConstraint constraint assignment := by
  -- Rewrite both evaluations to explicit term sums and then push negation through each summand.
  rw [Constraint.negate, evalConstraint_eq, evalConstraint_eq, evalLinearTerms_negate,
    evalQuadraticTerms_negate]
  simp [add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 1.4: the paired inequalities of `constraint.asEquation` hold exactly when
the underlying coded polynomial evaluates to zero. -/
lemma equationConstraints_correct (constraint : Constraint) (assignment : List ℤ) :
    (∀ eqConstraint ∈ constraint.asEquation, evalConstraint eqConstraint assignment ≤ 0) ↔
      evalConstraint constraint assignment = 0 := by
  constructor
  · intro hEquation
    -- Read the two inequalities as `evalConstraint constraint assignment ≤ 0` and its opposite.
    have hNonpos :
        evalConstraint constraint assignment ≤ 0 :=
      hEquation constraint (by simp [Constraint.asEquation])
    have hNegNonpos :
        -evalConstraint constraint assignment ≤ 0 := by
      simpa [Constraint.asEquation, evalConstraint_negate] using
        hEquation constraint.negate (by simp [Constraint.asEquation])
    exact le_antisymm hNonpos (neg_nonpos.mp hNegNonpos)
  · intro hZero
    -- Once the compiled polynomial is zero, both inequalities are immediate.
    intro eqConstraint hMem
    rcases List.mem_cons.1 hMem with rfl | hMem
    · simpa [hZero]
    · simp only [List.mem_singleton] at hMem
      subst hMem
      rw [evalConstraint_negate]
      simpa [hZero]

/-- Helper for Theorem 1.4: the theorem-local straight-line gates record the intended arithmetic
equations on slot assignments before compilation to quadratic inequalities. -/
inductive StraightLineGate where
  | const (slot : ℕ) (value : ℤ)
  | copy (slot source : ℕ)
  | add (slot lhs rhs : ℕ)
  | mul (slot lhs rhs : ℕ)
  | nonneg (slot : ℕ)

namespace StraightLineGate

/-- Helper for Theorem 1.4: the semantic meaning of one straight-line arithmetic gate. -/
def holds (assignment : List ℤ) : StraightLineGate → Prop
  | const slot value => assignment.getD slot 0 = value
  | copy slot source => assignment.getD slot 0 = assignment.getD source 0
  | add slot lhs rhs =>
      assignment.getD slot 0 = assignment.getD lhs 0 + assignment.getD rhs 0
  | mul slot lhs rhs =>
      assignment.getD slot 0 = assignment.getD lhs 0 * assignment.getD rhs 0
  | nonneg slot => 0 ≤ assignment.getD slot 0

/-- Helper for Theorem 1.4: the raw coded quadratic constraint whose zero set expresses one
straight-line gate. -/
def baseConstraint : StraightLineGate → Constraint
  | const slot value =>
      Constraint.ofData (-value) [LinearTerm.ofData slot 1] []
  | copy slot source =>
      Constraint.ofData 0 [LinearTerm.ofData slot 1, LinearTerm.ofData source (-1)] []
  | add slot lhs rhs =>
      Constraint.ofData 0
        [LinearTerm.ofData slot 1, LinearTerm.ofData lhs (-1), LinearTerm.ofData rhs (-1)] []
  | mul slot lhs rhs =>
      Constraint.ofData 0 [LinearTerm.ofData slot 1] [QuadraticTerm.ofData lhs rhs (-1)]
  | nonneg slot =>
      Constraint.ofData 0 [LinearTerm.ofData slot (-1)] []

/-- Helper for Theorem 1.4: compilation of one straight-line gate to coded quadratic
inequalities. -/
def compile (gate : StraightLineGate) : List Constraint :=
  match gate with
  | nonneg _ => [gate.baseConstraint]
  | _ => gate.baseConstraint.asEquation

/-- Helper for Theorem 1.4: every compiled gate contributes at least one coded inequality, so a
nonempty straight-line program will later yield a nonempty feasibility instance. -/
lemma compile_ne_nil (gate : StraightLineGate) :
    gate.compile ≠ [] := by
  cases gate <;> simp [compile, Constraint.asEquation]

/-- Helper for Theorem 1.4: the base constraint of a constant gate evaluates to the expected slot
minus the required constant. -/
private lemma eval_baseConstraint_const (slot : ℕ) (value : ℤ) (assignment : List ℤ) :
    evalConstraint (baseConstraint (.const slot value)) assignment =
      assignment.getD slot 0 - value := by
  -- Expand the single linear monomial and normalize the resulting arithmetic expression.
  rw [baseConstraint, evalConstraint_eq]
  simpa [Constraint.ofData, LinearTerm.ofData, evalLinearTerms, evalQuadraticTerms, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 1.4: the base constraint of a copy gate evaluates to the target slot minus
the source slot. -/
private lemma eval_baseConstraint_copy (slot source : ℕ) (assignment : List ℤ) :
    evalConstraint (baseConstraint (.copy slot source)) assignment =
      assignment.getD slot 0 - assignment.getD source 0 := by
  -- Expand the two linear monomials and regroup them as a single difference.
  rw [baseConstraint, evalConstraint_eq]
  simpa [Constraint.ofData, LinearTerm.ofData, evalLinearTerms, evalQuadraticTerms, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 1.4: the base constraint of an addition gate evaluates to the target slot
minus the sum of the two input slots. -/
private lemma eval_baseConstraint_add (slot lhs rhs : ℕ) (assignment : List ℤ) :
    evalConstraint (baseConstraint (.add slot lhs rhs)) assignment =
      assignment.getD slot 0 - assignment.getD lhs 0 - assignment.getD rhs 0 := by
  -- Expand the three linear monomials and group them as the intended additivity equation.
  rw [baseConstraint, evalConstraint_eq]
  simpa [Constraint.ofData, LinearTerm.ofData, evalLinearTerms, evalQuadraticTerms, sub_eq_add_neg,
    add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 1.4: the base constraint of a multiplication gate evaluates to the target
slot minus the product of the two input slots. -/
private lemma eval_baseConstraint_mul (slot lhs rhs : ℕ) (assignment : List ℤ) :
    evalConstraint (baseConstraint (.mul slot lhs rhs)) assignment =
      assignment.getD slot 0 - assignment.getD lhs 0 * assignment.getD rhs 0 := by
  -- The only quadratic monomial in this gate already records the required product relation.
  rw [baseConstraint, evalConstraint_eq]
  simpa [Constraint.ofData, LinearTerm.ofData, QuadraticTerm.ofData, evalLinearTerms,
    evalQuadraticTerms, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 1.4: the base constraint of a nonnegativity gate evaluates to the negative
of the guarded slot. -/
private lemma eval_baseConstraint_nonneg (slot : ℕ) (assignment : List ℤ) :
    evalConstraint (baseConstraint (.nonneg slot)) assignment =
      -assignment.getD slot 0 := by
  -- The compiled inequality is exactly `-x_slot ≤ 0`.
  rw [baseConstraint, evalConstraint_eq]
  simpa [Constraint.ofData, LinearTerm.ofData, evalLinearTerms, evalQuadraticTerms]

/-- Helper for Theorem 1.4: satisfying the compiled inequalities of one straight-line gate is
equivalent to satisfying its intended arithmetic meaning. -/
lemma compile_correct (gate : StraightLineGate) (assignment : List ℤ) :
    (∀ constraint ∈ gate.compile, evalConstraint constraint assignment ≤ 0) ↔
      gate.holds assignment := by
  cases gate with
  | const slot value =>
      -- Route correction: the raw quadratic encoding is now discharged once via paired
      -- inequalities, so the gate semantics reduces to the explicit equation `x_slot = value`.
      constructor
      · intro hCompiled
        have hZero :
            evalConstraint (baseConstraint (.const slot value)) assignment = 0 :=
          (equationConstraints_correct _ _).1 hCompiled
        rw [eval_baseConstraint_const] at hZero
        simpa [holds] using sub_eq_zero.mp hZero
      · intro hGate
        apply (equationConstraints_correct _ _).2
        rw [eval_baseConstraint_const]
        exact sub_eq_zero.mpr hGate
  | copy slot source =>
      constructor
      · intro hCompiled
        have hZero :
            evalConstraint (baseConstraint (.copy slot source)) assignment = 0 :=
          (equationConstraints_correct _ _).1 hCompiled
        rw [eval_baseConstraint_copy] at hZero
        simpa [holds] using sub_eq_zero.mp hZero
      · intro hGate
        apply (equationConstraints_correct _ _).2
        rw [eval_baseConstraint_copy]
        exact sub_eq_zero.mpr hGate
  | add slot lhs rhs =>
      constructor
      · intro hCompiled
        have hZero :
            evalConstraint (baseConstraint (.add slot lhs rhs)) assignment = 0 :=
          (equationConstraints_correct _ _).1 hCompiled
        rw [eval_baseConstraint_add] at hZero
        have hZero' :
            assignment.getD slot 0 -
                (assignment.getD lhs 0 + assignment.getD rhs 0) = 0 := by
          simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hZero
        simpa [holds] using sub_eq_zero.mp hZero'
      · intro hGate
        apply (equationConstraints_correct _ _).2
        rw [eval_baseConstraint_add]
        have hZero :
            assignment.getD slot 0 -
                (assignment.getD lhs 0 + assignment.getD rhs 0) = 0 :=
          sub_eq_zero.mpr hGate
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hZero
  | mul slot lhs rhs =>
      constructor
      · intro hCompiled
        have hZero :
            evalConstraint (baseConstraint (.mul slot lhs rhs)) assignment = 0 :=
          (equationConstraints_correct _ _).1 hCompiled
        rw [eval_baseConstraint_mul] at hZero
        simpa [holds] using sub_eq_zero.mp hZero
      · intro hGate
        apply (equationConstraints_correct _ _).2
        rw [eval_baseConstraint_mul]
        exact sub_eq_zero.mpr hGate
  | nonneg slot =>
      constructor
      · intro hCompiled
        have hNonpos :
            evalConstraint (baseConstraint (.nonneg slot)) assignment ≤ 0 :=
          hCompiled _ (by simp [compile])
        rw [eval_baseConstraint_nonneg] at hNonpos
        exact neg_nonpos.mp hNonpos
      · intro hGate
        intro constraint hMem
        simp only [compile, List.mem_singleton] at hMem
        subst hMem
        rw [eval_baseConstraint_nonneg]
        exact neg_nonpos.mpr hGate

end StraightLineGate

/-- Helper for Theorem 1.4: compile a list of straight-line gates to the concatenated list of
coded quadratic inequalities. -/
def compileBlock : List StraightLineGate → List Constraint
  | [] => []
  | gate :: gates => gate.compile ++ compileBlock gates

/-- Helper for Theorem 1.4: semantic satisfaction of a straight-line block by an integral slot
assignment. -/
def blockHolds (assignment : List ℤ) : List StraightLineGate → Prop
  | [] => True
  | gate :: gates => gate.holds assignment ∧ blockHolds assignment gates

/-- Helper for Theorem 1.4: compiling a nonempty straight-line block yields a nonempty constraint
list, so the later feasibility wrapper only has to supply slot bounds. -/
lemma compileBlock_ne_nil_of_ne_nil {gates : List StraightLineGate} (hGates : gates ≠ []) :
    compileBlock gates ≠ [] := by
  cases gates with
  | nil =>
      contradiction
  | cons gate gates =>
      simp [compileBlock, StraightLineGate.compile_ne_nil]

/-- Helper for Theorem 1.4: satisfying the compiled quadratic block is equivalent to satisfying
all intended gate equalities and nonnegativity conditions on the same slot assignment. -/
lemma straightLineBlock_correct (gates : List StraightLineGate) (assignment : List ℤ) :
    (∀ constraint ∈ compileBlock gates, evalConstraint constraint assignment ≤ 0) ↔
      blockHolds assignment gates := by
  induction gates with
  | nil =>
      simp [compileBlock, blockHolds]
  | cons gate gates ih =>
      -- Split the compiled block into the head gate and the already certified tail block.
      constructor
      · intro hCompiled
        refine ⟨?_, ?_⟩
        · exact (StraightLineGate.compile_correct gate assignment).1
            (fun constraint hMem ↦ hCompiled constraint (by simp [compileBlock, hMem]))
        · exact ih.1
            (fun constraint hMem ↦ hCompiled constraint (by simp [compileBlock, hMem]))
      · rintro ⟨hGate, hTail⟩ constraint hMem
        rcases List.mem_append.1 hMem with hGateMem | hTailMem
        · exact (StraightLineGate.compile_correct gate assignment).2 hGate constraint hGateMem
        · exact ih.2 hTail constraint hTailMem

/-- Helper for Theorem 1.4: the slot references appearing in one straight-line gate stay within a
declared variable range. -/
def StraightLineGate.InRange (variableCount : ℕ) : StraightLineGate → Prop
  | .const slot _ => slot < variableCount
  | .copy slot source => slot < variableCount ∧ source < variableCount
  | .add slot lhs rhs => slot < variableCount ∧ lhs < variableCount ∧ rhs < variableCount
  | .mul slot lhs rhs => slot < variableCount ∧ lhs < variableCount ∧ rhs < variableCount
  | .nonneg slot => slot < variableCount

/-- Helper for Theorem 1.4: every linear term created by compiling one in-range gate stays within
the declared slot range. -/
private lemma linearTerm_inRange_of_mem_compile {variableCount : ℕ} {gate : StraightLineGate}
    (hGate : gate.InRange variableCount) {constraint : Constraint} {term : LinearTerm}
    (hConstraint : constraint ∈ gate.compile) (hTerm : term ∈ constraint.linearTerms) :
    term.index < variableCount := by
  -- Each gate compiles to a tiny fixed list of constraints, so a case split reduces the range
  -- check to the corresponding slot hypotheses.
  cases gate with
  | const slot value =>
      simp [StraightLineGate.compile, Constraint.asEquation] at hConstraint
      rcases hConstraint with rfl | rfl
      · simp [StraightLineGate.baseConstraint, Constraint.ofData, LinearTerm.ofData] at hTerm
        rcases hTerm with rfl
        simpa [LinearTerm.ofData] using hGate
      · simp [StraightLineGate.baseConstraint, Constraint.negate, Constraint.ofData,
          LinearTerm.ofData, LinearTerm.negate] at hTerm
        rcases hTerm with rfl
        simpa [LinearTerm.ofData, LinearTerm.negate] using hGate
  | copy slot source =>
      simp [StraightLineGate.compile, Constraint.asEquation] at hConstraint
      rcases hConstraint with rfl | rfl
      · simp [StraightLineGate.baseConstraint, Constraint.ofData, LinearTerm.ofData] at hTerm
        rcases hTerm with rfl | rfl
        · exact hGate.1
        · exact hGate.2
      · simp [StraightLineGate.baseConstraint, Constraint.negate, Constraint.ofData,
          LinearTerm.ofData, LinearTerm.negate] at hTerm
        rcases hTerm with rfl | rfl
        · exact hGate.1
        · exact hGate.2
  | add slot lhs rhs =>
      simp [StraightLineGate.compile, Constraint.asEquation] at hConstraint
      rcases hConstraint with rfl | rfl
      · simp [StraightLineGate.baseConstraint, Constraint.ofData, LinearTerm.ofData] at hTerm
        rcases hTerm with rfl | rfl | rfl
        · exact hGate.1
        · exact hGate.2.1
        · exact hGate.2.2
      · simp [StraightLineGate.baseConstraint, Constraint.negate, Constraint.ofData,
          LinearTerm.ofData, LinearTerm.negate] at hTerm
        rcases hTerm with rfl | rfl | rfl
        · exact hGate.1
        · exact hGate.2.1
        · exact hGate.2.2
  | mul slot lhs rhs =>
      simp [StraightLineGate.compile, Constraint.asEquation] at hConstraint
      rcases hConstraint with rfl | rfl
      · simp [StraightLineGate.baseConstraint, Constraint.ofData, LinearTerm.ofData] at hTerm
        rcases hTerm with rfl
        exact hGate.1
      · simp [StraightLineGate.baseConstraint, Constraint.negate, Constraint.ofData,
          LinearTerm.ofData, LinearTerm.negate, QuadraticTerm.ofData, QuadraticTerm.negate] at hTerm
        rcases hTerm with rfl
        exact hGate.1
  | nonneg slot =>
      simp [StraightLineGate.compile] at hConstraint
      subst hConstraint
      simp [StraightLineGate.baseConstraint, Constraint.ofData, LinearTerm.ofData] at hTerm
      rcases hTerm with rfl
      simpa [StraightLineGate.InRange] using hGate

/-- Helper for Theorem 1.4: every quadratic term created by compiling one in-range gate stays
within the declared slot range. -/
private lemma quadraticTerm_inRange_of_mem_compile {variableCount : ℕ} {gate : StraightLineGate}
    (hGate : gate.InRange variableCount) {constraint : Constraint} {term : QuadraticTerm}
    (hConstraint : constraint ∈ gate.compile) (hTerm : term ∈ constraint.quadraticTerms) :
    term.leftIndex < variableCount ∧ term.rightIndex < variableCount := by
  -- Only multiplication gates contribute quadratic monomials, and their two source slots are
  -- already recorded in the gate-range hypothesis.
  cases gate with
  | const slot value =>
      simp [StraightLineGate.compile, Constraint.asEquation] at hConstraint
      rcases hConstraint with rfl | rfl <;>
        simp [StraightLineGate.baseConstraint, Constraint.ofData, Constraint.negate,
          LinearTerm.ofData, LinearTerm.negate] at hTerm
  | copy slot source =>
      simp [StraightLineGate.compile, Constraint.asEquation] at hConstraint
      rcases hConstraint with rfl | rfl <;>
        simp [StraightLineGate.baseConstraint, Constraint.ofData, Constraint.negate,
          LinearTerm.ofData, LinearTerm.negate] at hTerm
  | add slot lhs rhs =>
      simp [StraightLineGate.compile, Constraint.asEquation] at hConstraint
      rcases hConstraint with rfl | rfl <;>
        simp [StraightLineGate.baseConstraint, Constraint.ofData, Constraint.negate,
          LinearTerm.ofData, LinearTerm.negate] at hTerm
  | mul slot lhs rhs =>
      simp [StraightLineGate.compile, Constraint.asEquation] at hConstraint
      rcases hConstraint with rfl | rfl
      · simp [StraightLineGate.baseConstraint, Constraint.ofData, QuadraticTerm.ofData] at hTerm
        rcases hTerm with rfl
        exact ⟨hGate.2.1, hGate.2.2⟩
      · simp [StraightLineGate.baseConstraint, Constraint.negate, Constraint.ofData,
          QuadraticTerm.ofData, QuadraticTerm.negate, LinearTerm.ofData, LinearTerm.negate] at hTerm
        rcases hTerm with rfl
        exact ⟨hGate.2.1, hGate.2.2⟩
  | nonneg slot =>
      simp [StraightLineGate.compile] at hConstraint
      subst hConstraint
      simp [StraightLineGate.baseConstraint, Constraint.ofData] at hTerm

/-- Helper for Theorem 1.4: every linear term in a compiled in-range straight-line block stays
within the declared slot range. -/
private lemma compileBlock_linearTerms_inRange {variableCount : ℕ} {gates : List StraightLineGate}
    (hRange : ∀ gate ∈ gates, gate.InRange variableCount) {constraint : Constraint}
    {term : LinearTerm} (hConstraint : constraint ∈ compileBlock gates)
    (hTerm : term ∈ constraint.linearTerms) :
    term.index < variableCount := by
  revert hRange
  induction gates with
  | nil =>
      intro hRange
      simpa [compileBlock] using hConstraint
  | cons gate gates ih =>
      intro hRange
      -- Split the compiled constraint membership into the head gate and the tail block.
      rcases List.mem_append.1 hConstraint with hHead | hTail
      · exact linearTerm_inRange_of_mem_compile (hRange gate (by simp)) hHead hTerm
      · exact ih hTail (fun gate' hGate' ↦ hRange gate' (by simp [hGate']))

/-- Helper for Theorem 1.4: every quadratic term in a compiled in-range straight-line block stays
within the declared slot range. -/
private lemma compileBlock_quadraticTerms_inRange {variableCount : ℕ}
    {gates : List StraightLineGate} (hRange : ∀ gate ∈ gates, gate.InRange variableCount)
    {constraint : Constraint} {term : QuadraticTerm}
    (hConstraint : constraint ∈ compileBlock gates) (hTerm : term ∈ constraint.quadraticTerms) :
    term.leftIndex < variableCount ∧ term.rightIndex < variableCount := by
  revert hRange
  induction gates with
  | nil =>
      intro hRange
      simpa [compileBlock] using hConstraint
  | cons gate gates ih =>
      intro hRange
      -- The quadratic range check also decomposes into the head gate or the recursive tail block.
      rcases List.mem_append.1 hConstraint with hHead | hTail
      · exact quadraticTerm_inRange_of_mem_compile (hRange gate (by simp)) hHead hTerm
      · exact ih hTail (fun gate' hGate' ↦ hRange gate' (by simp [hGate']))

/-- Helper for Theorem 1.4: package a compiled straight-line block as one quadratic-feasibility
instance. -/
def blockInstance (variableCount : ℕ) (gates : List StraightLineGate) : Code :=
  Code.ofData variableCount (compileBlock gates)

/-- Helper for Theorem 1.4: solving the packaged straight-line instance is equivalent to finding
an integral slot assignment satisfying the intended gate semantics. -/
lemma straightLineInstance_correct {variableCount : ℕ} {gates : List StraightLineGate}
    (hVariableCount : 0 < variableCount) (hGates : gates ≠ [])
    (hRange : ∀ gate ∈ gates, gate.InRange variableCount) :
    hasSolution (blockInstance variableCount gates) ↔
      ∃ assignment : List ℤ, assignment.length = variableCount ∧ blockHolds assignment gates := by
  -- Unfold the packaged instance once, then discharge well-formedness from the shared slot-range
  -- hypotheses and reuse the block semantics theorem for the actual constraints.
  simp only [hasSolution_iff, blockInstance, Code.ofData_variableCount, Code.ofData_constraints]
  constructor
  · rintro ⟨_, _, _, _, assignment, hLength, hConstraints⟩
    exact ⟨assignment, hLength, (straightLineBlock_correct gates assignment).1 hConstraints⟩
  · rintro ⟨assignment, hLength, hBlock⟩
    refine ⟨hVariableCount, compileBlock_ne_nil_of_ne_nil hGates, ?_, ?_, assignment, hLength, ?_⟩
    · intro constraint hConstraint term hTerm
      exact compileBlock_linearTerms_inRange hRange hConstraint hTerm
    · intro constraint hConstraint term hTerm
      exact compileBlock_quadraticTerms_inRange hRange hConstraint hTerm
    · exact (straightLineBlock_correct gates assignment).2 hBlock

/-! ### Quadratizing a fixed integer polynomial

The DPRM support theorem produces a finite polynomial code.  The following small expression
compiler turns that code into the already certified straight-line gate language. -/

/-- Helper for Theorem 1.4: arithmetic expressions use source slots, integer constants, addition,
and multiplication, exactly the operations supported by `StraightLineGate`. -/
inductive ArithmeticExpression where
  | source (slot : ℕ)
  | const (value : ℤ)
  | add (left right : ArithmeticExpression)
  | mul (left right : ArithmeticExpression)

namespace ArithmeticExpression

/-- Helper for Theorem 1.4: evaluate an arithmetic expression on an integral slot assignment. -/
def eval (assignment : List ℤ) : ArithmeticExpression → ℤ
  | .source slot => assignment.getD slot 0
  | .const value => value
  | .add left right => left.eval assignment + right.eval assignment
  | .mul left right => left.eval assignment * right.eval assignment

/-- Helper for Theorem 1.4: every source slot read by an expression lies below a fixed boundary. -/
def SourcesBelow (bound : ℕ) : ArithmeticExpression → Prop
  | .source slot => slot < bound
  | .const _ => True
  | .add left right => left.SourcesBelow bound ∧ right.SourcesBelow bound
  | .mul left right => left.SourcesBelow bound ∧ right.SourcesBelow bound

/-- Helper for Theorem 1.4: increasing the source boundary preserves the source-range property. -/
lemma sourcesBelow_mono {expression : ArithmeticExpression} {a b : ℕ}
    (hab : a ≤ b) (h : expression.SourcesBelow a) : expression.SourcesBelow b := by
  induction expression with
  | source slot =>
      -- A source already below `a` is also below the larger boundary `b`.
      exact lt_of_lt_of_le h hab
  | const value =>
      trivial
  | add left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩
  | mul left right ihLeft ihRight =>
      exact ⟨ihLeft h.1, ihRight h.2⟩

/-- Helper for Theorem 1.4: appending values after all source slots does not change expression
evaluation. -/
lemma eval_append {expression : ArithmeticExpression} {assignment extension : List ℤ}
    {bound : ℕ} (hSources : expression.SourcesBelow bound)
    (hBound : bound ≤ assignment.length) :
    expression.eval (assignment ++ extension) = expression.eval assignment := by
  induction expression with
  | source slot =>
      -- The requested source lies in the original prefix, so `getD` ignores the extension.
      exact List.getD_append _ _ _ _ (lt_of_lt_of_le hSources hBound)
  | const value =>
      rfl
  | add left right ihLeft ihRight =>
      simp only [eval, ihLeft hSources.1, ihRight hSources.2]
  | mul left right ihLeft ihRight =>
      simp only [eval, ihLeft hSources.1, ihRight hSources.2]

/-- Helper for Theorem 1.4: the expression for a natural power of one source slot. -/
def power (slot : ℕ) : ℕ → ArithmeticExpression
  | 0 => .const 1
  | exponent + 1 => .mul (.source slot) (power slot exponent)

/-- Helper for Theorem 1.4: the expression for a monomial whose first variable has the supplied
source index. -/
def monomialFrom (slot : ℕ) : Hilbert10.MonomialCode → ArithmeticExpression
  | [] => .const 1
  | exponent :: exponents =>
      .mul (power slot exponent) (monomialFrom (slot + 1) exponents)

/-- Helper for Theorem 1.4: the expression for one sparse polynomial term. -/
def term (codedTerm : ℤ × Hilbert10.MonomialCode) : ArithmeticExpression :=
  .mul (.const codedTerm.1) (monomialFrom 0 codedTerm.2)

/-- Helper for Theorem 1.4: the expression represented by a sparse integer polynomial code. -/
def polynomial : List (ℤ × Hilbert10.MonomialCode) → ArithmeticExpression
  | [] => .const 0
  | codedTerm :: codedTerms => .add (term codedTerm) (polynomial codedTerms)

/-- Helper for Theorem 1.4: expression evaluation computes the expected power. -/
lemma eval_power (slot exponent : ℕ) (assignment : List ℤ) :
    (power slot exponent).eval assignment = assignment.getD slot 0 ^ exponent := by
  induction exponent with
  | zero =>
      simp [power, eval]
  | succ exponent ih =>
      -- Peel off one multiplication and use the recursively computed lower power.
      simp [power, eval, ih, pow_succ, mul_comm]

/-- Helper for Theorem 1.4: functional monomial evaluation exposes the successive source slots. -/
def evalMonomialFrom (slot : ℕ) : Hilbert10.MonomialCode → (ℕ → ℤ) → ℤ
  | [], _ => 1
  | exponent :: exponents, assignment =>
      assignment slot ^ exponent * evalMonomialFrom (slot + 1) exponents assignment

/-- Helper for Theorem 1.4: the monomial expression agrees with functional monomial evaluation. -/
lemma eval_monomialFrom (slot : ℕ) (exponents : Hilbert10.MonomialCode)
    (assignment : List ℤ) :
    (monomialFrom slot exponents).eval assignment =
      evalMonomialFrom slot exponents (fun i ↦ assignment.getD i 0) := by
  induction exponents generalizing slot with
  | nil =>
      rfl
  | cons exponent exponents ih =>
      -- Separate the current power and invoke the induction hypothesis on the remaining slots.
      simp [monomialFrom, eval, eval_power, evalMonomialFrom, ih]

/-- Helper for Theorem 1.4: a functional assignment that agrees with list lookup from a given
offset gives the same monomial value as the list evaluator. -/
private lemma evalMonomialInt_eq_evalMonomialFrom_of_lookup
    (exponents : Hilbert10.MonomialCode) (assignment : List ℤ) (slot : ℕ)
    (functionalAssignment : ℕ → ℤ)
    (hLookup : ∀ i, functionalAssignment (slot + i) = assignment.getD i 0) :
    Hilbert10.PolynomialCode.evalMonomialInt exponents assignment =
      evalMonomialFrom slot exponents functionalAssignment := by
  induction exponents generalizing assignment slot with
  | nil =>
      rfl
  | cons exponent exponents ih =>
      cases assignment with
      | nil =>
          have hHead : functionalAssignment slot = 0 := by
            simpa using hLookup 0
          have hTail : ∀ i, functionalAssignment (slot + 1 + i) = ([] : List ℤ).getD i 0 := by
            intro i
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLookup (i + 1)
          -- The empty list and the functional assignment both contribute zero at every source.
          simp only [Hilbert10.PolynomialCode.evalMonomialInt, evalMonomialFrom, hHead]
          rw [← ih [] (slot + 1) hTail]
      | cons value values =>
          have hHead : functionalAssignment slot = value := by
            simpa using hLookup 0
          have hTail : ∀ i, functionalAssignment (slot + 1 + i) = values.getD i 0 := by
            intro i
            calc
              functionalAssignment (slot + 1 + i) =
                  functionalAssignment (slot + (i + 1)) := by
                    congr 1
                    omega
              _ = (value :: values).getD (i + 1) 0 := hLookup (i + 1)
              _ = values.getD i 0 := by simp [List.getD]
          -- Remove the head lookup, then apply the same invariant to the assignment tail.
          simp only [Hilbert10.PolynomialCode.evalMonomialInt, evalMonomialFrom, hHead]
          rw [← ih values (slot + 1) hTail]

/-- Helper for Theorem 1.4: list-based and functional monomial evaluation coincide. -/
lemma evalMonomialInt_eq_evalMonomialFrom (exponents : Hilbert10.MonomialCode)
    (assignment : List ℤ) :
    Hilbert10.PolynomialCode.evalMonomialInt exponents assignment =
      evalMonomialFrom 0 exponents (fun i ↦ assignment.getD i 0) := by
  -- Instantiate the offset invariant at zero, where functional lookup is literally list lookup.
  apply evalMonomialInt_eq_evalMonomialFrom_of_lookup
  intro i
  simp

/-- Helper for Theorem 1.4: the expression attached to a polynomial code evaluates to its
integer polynomial value. -/
lemma eval_polynomial (codedTerms : List (ℤ × Hilbert10.MonomialCode))
    (assignment : List ℤ) :
    (polynomial codedTerms).eval assignment =
      Hilbert10.PolynomialCode.evalInt ⟨codedTerms⟩ assignment := by
  induction codedTerms with
  | nil =>
      rfl
  | cons codedTerm codedTerms ih =>
      -- Normalize the head monomial and then use the polynomial-tail induction hypothesis.
      rw [Hilbert10.PolynomialCode.evalInt_mk_cons]
      simp only [polynomial, term, eval, eval_monomialFrom,
        ← evalMonomialInt_eq_evalMonomialFrom, ih]

/-- Helper for Theorem 1.4: a power expression reads only its single declared source slot. -/
lemma sourcesBelow_power {slot bound exponent : ℕ} (hSlot : slot < bound) :
    (power slot exponent).SourcesBelow bound := by
  induction exponent with
  | zero =>
      trivial
  | succ exponent ih =>
      -- The successor power reads the same source once more and then reuses the lower power.
      exact ⟨hSlot, ih⟩

/-- Helper for Theorem 1.4: a monomial expression only reads the slots covered by its exponent
vector. -/
lemma sourcesBelow_monomialFrom {slot bound : ℕ} {exponents : Hilbert10.MonomialCode}
    (hBound : slot + exponents.length ≤ bound) :
    (monomialFrom slot exponents).SourcesBelow bound := by
  induction exponents generalizing slot with
  | nil =>
      trivial
  | cons exponent exponents ih =>
      have hSlot : slot < bound := by
        simp only [List.length_cons] at hBound
        omega
      have hTail : slot + 1 + exponents.length ≤ bound := by
        simp only [List.length_cons] at hBound
        omega
      constructor
      · exact sourcesBelow_power hSlot
      · exact ih hTail

/-- Helper for Theorem 1.4: the polynomial expression reads only source slots below any declared
bound on the code's arity. -/
lemma sourcesBelow_polynomial {codedTerms : List (ℤ × Hilbert10.MonomialCode)} {bound : ℕ}
    (hBound : ∀ codedTerm ∈ codedTerms, codedTerm.2.length ≤ bound) :
    (polynomial codedTerms).SourcesBelow bound := by
  induction codedTerms with
  | nil =>
      trivial
  | cons codedTerm codedTerms ih =>
      have hTermBound : 0 + codedTerm.2.length ≤ bound := by
        simpa using hBound codedTerm (List.mem_cons_self)
      constructor
      · exact ⟨trivial, sourcesBelow_monomialFrom hTermBound⟩
      · exact ih (fun term hMem ↦ hBound term (by simp [hMem]))

/-- Helper for Theorem 1.4: the output of compiling an expression records the next free slot, its
result slot, and the generated straight-line gates. -/
structure Compilation where
  nextSlot : ℕ
  outputSlot : ℕ
  gates : List StraightLineGate

/-- Helper for Theorem 1.4: compile an expression using only fresh output slots at or above
`nextSlot`. -/
def compile : ArithmeticExpression → ℕ → Compilation
  | .source slot, nextSlot => ⟨nextSlot, slot, []⟩
  | .const value, nextSlot => ⟨nextSlot + 1, nextSlot, [.const nextSlot value]⟩
  | .add left right, nextSlot =>
      let leftCode := compile left nextSlot
      let rightCode := compile right leftCode.nextSlot
      ⟨rightCode.nextSlot + 1, rightCode.nextSlot,
        leftCode.gates ++ rightCode.gates ++
          [.add rightCode.nextSlot leftCode.outputSlot rightCode.outputSlot]⟩
  | .mul left right, nextSlot =>
      let leftCode := compile left nextSlot
      let rightCode := compile right leftCode.nextSlot
      ⟨rightCode.nextSlot + 1, rightCode.nextSlot,
        leftCode.gates ++ rightCode.gates ++
          [.mul rightCode.nextSlot leftCode.outputSlot rightCode.outputSlot]⟩

/-- Helper for Theorem 1.4: compilation never moves the next-free-slot boundary backwards. -/
lemma le_compile_nextSlot (expression : ArithmeticExpression) (nextSlot : ℕ) :
    nextSlot ≤ (compile expression nextSlot).nextSlot := by
  induction expression generalizing nextSlot with
  | source slot =>
      exact le_rfl
  | const value =>
      simp [compile]
  | add left right ihLeft ihRight =>
      simp only [compile]
      exact le_trans (ihLeft nextSlot) (le_trans (ihRight _) (Nat.le_succ _))
  | mul left right ihLeft ihRight =>
      simp only [compile]
      exact le_trans (ihLeft nextSlot) (le_trans (ihRight _) (Nat.le_succ _))

/-- Helper for Theorem 1.4: the result slot of a compiled expression lies below its returned
next-free-slot boundary. -/
lemma compile_outputSlot_lt {expression : ArithmeticExpression} {nextSlot : ℕ}
    (hSources : expression.SourcesBelow nextSlot) :
    (compile expression nextSlot).outputSlot < (compile expression nextSlot).nextSlot := by
  induction expression generalizing nextSlot with
  | source slot =>
      exact hSources
  | const value =>
      simp [compile]
  | add left right ihLeft ihRight =>
      simp [compile]
  | mul left right ihLeft ihRight =>
      simp [compile]

/-- Helper for Theorem 1.4: enlarging the declared slot range preserves gate well-formedness. -/
lemma StraightLineGate.InRange.mono {gate : StraightLineGate} {a b : ℕ}
    (h : gate.InRange a) (hab : a ≤ b) : gate.InRange b := by
  cases gate <;> simp only [StraightLineGate.InRange] at h ⊢ <;> omega

/-- Helper for Theorem 1.4: every gate emitted by expression compilation refers only to slots
strictly below the returned next-free-slot boundary. -/
lemma compile_gates_inRange {expression : ArithmeticExpression} {nextSlot : ℕ}
    (hSources : expression.SourcesBelow nextSlot) :
    ∀ gate ∈ (compile expression nextSlot).gates,
      gate.InRange (compile expression nextSlot).nextSlot := by
  induction expression generalizing nextSlot with
  | source slot =>
      simp [compile]
  | const value =>
      simp [compile, StraightLineGate.InRange]
  | add left right ihLeft ihRight =>
      have hLeftNext : nextSlot ≤ (compile left nextSlot).nextSlot :=
        le_compile_nextSlot left nextSlot
      have hRightSources : right.SourcesBelow (compile left nextSlot).nextSlot :=
        sourcesBelow_mono hLeftNext hSources.2
      have hLeftOutput := compile_outputSlot_lt hSources.1
      have hRightOutput := compile_outputSlot_lt hRightSources
      have hRightNext :
          (compile left nextSlot).nextSlot ≤
            (compile right (compile left nextSlot).nextSlot).nextSlot :=
        le_compile_nextSlot right _
      have hLeftRange := ihLeft hSources.1
      have hRightRange := ihRight hRightSources
      intro gate hGate
      simp only [compile, List.mem_append, List.mem_singleton] at hGate ⊢
      rcases hGate with (hGate | hGate) | rfl
      · exact StraightLineGate.InRange.mono (hLeftRange gate hGate)
          (Nat.le_trans (le_compile_nextSlot right _) (Nat.le_succ _))
      · exact StraightLineGate.InRange.mono (hRightRange gate hGate) (Nat.le_succ _)
      · exact ⟨Nat.lt_succ_self _,
          lt_of_lt_of_le (lt_of_lt_of_le hLeftOutput hRightNext) (Nat.le_succ _),
          lt_trans hRightOutput (Nat.lt_succ_self _)⟩
  | mul left right ihLeft ihRight =>
      have hLeftNext : nextSlot ≤ (compile left nextSlot).nextSlot :=
        le_compile_nextSlot left nextSlot
      have hRightSources : right.SourcesBelow (compile left nextSlot).nextSlot :=
        sourcesBelow_mono hLeftNext hSources.2
      have hLeftOutput := compile_outputSlot_lt hSources.1
      have hRightOutput := compile_outputSlot_lt hRightSources
      have hRightNext :
          (compile left nextSlot).nextSlot ≤
            (compile right (compile left nextSlot).nextSlot).nextSlot :=
        le_compile_nextSlot right _
      have hLeftRange := ihLeft hSources.1
      have hRightRange := ihRight hRightSources
      intro gate hGate
      simp only [compile, List.mem_append, List.mem_singleton] at hGate ⊢
      rcases hGate with (hGate | hGate) | rfl
      · exact StraightLineGate.InRange.mono (hLeftRange gate hGate)
          (Nat.le_trans (le_compile_nextSlot right _) (Nat.le_succ _))
      · exact StraightLineGate.InRange.mono (hRightRange gate hGate) (Nat.le_succ _)
      · exact ⟨Nat.lt_succ_self _,
          lt_of_lt_of_le (lt_of_lt_of_le hLeftOutput hRightNext) (Nat.le_succ _),
          lt_trans hRightOutput (Nat.lt_succ_self _)⟩

/-- Helper for Theorem 1.4: block satisfaction distributes over concatenation of gate lists. -/
lemma blockHolds_append (assignment : List ℤ) (left right : List StraightLineGate) :
    blockHolds assignment (left ++ right) ↔
      blockHolds assignment left ∧ blockHolds assignment right := by
  induction left with
  | nil =>
      simp [blockHolds]
  | cons gate gates ih =>
      simp [blockHolds, ih, and_assoc]

/-- Helper for Theorem 1.4: appending values after every slot read by a gate preserves whether
that gate holds. -/
lemma StraightLineGate.holds_append_iff {gate : StraightLineGate} {assignment extension : List ℤ}
    (hRange : gate.InRange assignment.length) :
    gate.holds (assignment ++ extension) ↔ gate.holds assignment := by
  cases gate with
  | const slot value =>
      simp only [StraightLineGate.holds, StraightLineGate.InRange] at hRange ⊢
      rw [List.getD_append _ _ _ _ hRange]
  | copy slot source =>
      simp only [StraightLineGate.holds, StraightLineGate.InRange] at hRange ⊢
      rw [List.getD_append _ _ _ _ hRange.1,
        List.getD_append _ _ _ _ hRange.2]
  | add slot lhs rhs =>
      simp only [StraightLineGate.holds, StraightLineGate.InRange] at hRange ⊢
      rw [List.getD_append _ _ _ _ hRange.1,
        List.getD_append _ _ _ _ hRange.2.1,
        List.getD_append _ _ _ _ hRange.2.2]
  | mul slot lhs rhs =>
      simp only [StraightLineGate.holds, StraightLineGate.InRange] at hRange ⊢
      rw [List.getD_append _ _ _ _ hRange.1,
        List.getD_append _ _ _ _ hRange.2.1,
        List.getD_append _ _ _ _ hRange.2.2]
  | nonneg slot =>
      simp only [StraightLineGate.holds, StraightLineGate.InRange] at hRange ⊢
      rw [List.getD_append _ _ _ _ hRange]

/-- Helper for Theorem 1.4: appending values after every slot read by a block preserves block
satisfaction. -/
lemma blockHolds_append_assignment {gates : List StraightLineGate}
    {assignment extension : List ℤ}
    (hRange : ∀ gate ∈ gates, gate.InRange assignment.length) :
    blockHolds (assignment ++ extension) gates ↔ blockHolds assignment gates := by
  induction gates with
  | nil =>
      simp [blockHolds]
  | cons gate gates ih =>
      rw [blockHolds, blockHolds, StraightLineGate.holds_append_iff]
      · rw [ih]
        exact fun gate' hGate' ↦ hRange gate' (List.mem_cons_of_mem gate hGate')
      · exact hRange gate List.mem_cons_self

/-- Helper for Theorem 1.4: all compiled gate equations determine the output slot as the value of
the source expression on the same assignment. -/
lemma compile_correct {expression : ArithmeticExpression} {nextSlot : ℕ}
    (hSources : expression.SourcesBelow nextSlot) (assignment : List ℤ)
    (hBlock : blockHolds assignment (compile expression nextSlot).gates) :
    assignment.getD (compile expression nextSlot).outputSlot 0 = expression.eval assignment := by
  induction expression generalizing nextSlot with
  | source slot =>
      rfl
  | const value =>
      simpa [compile, blockHolds, StraightLineGate.holds, eval] using hBlock
  | add left right ihLeft ihRight =>
      have hLeftNext : nextSlot ≤ (compile left nextSlot).nextSlot :=
        le_compile_nextSlot left nextSlot
      have hRightSources : right.SourcesBelow (compile left nextSlot).nextSlot :=
        sourcesBelow_mono hLeftNext hSources.2
      have hSplit := (blockHolds_append assignment
        ((compile left nextSlot).gates ++
          (compile right (compile left nextSlot).nextSlot).gates)
        [.add (compile right (compile left nextSlot).nextSlot).nextSlot
          (compile left nextSlot).outputSlot
          (compile right (compile left nextSlot).nextSlot).outputSlot]).1
          (by simpa only [compile] using hBlock)
      have hCore := (blockHolds_append assignment
        (compile left nextSlot).gates
        (compile right (compile left nextSlot).nextSlot).gates).1 hSplit.1
      have hGate :
          (StraightLineGate.add (compile right (compile left nextSlot).nextSlot).nextSlot
            (compile left nextSlot).outputSlot
            (compile right (compile left nextSlot).nextSlot).outputSlot).holds assignment := by
        simpa [blockHolds] using hSplit.2
      rw [show (compile (.add left right) nextSlot).outputSlot =
          (compile right (compile left nextSlot).nextSlot).nextSlot by rfl]
      rw [hGate, ihLeft hSources.1 hCore.1, ihRight hRightSources hCore.2]
      rfl
  | mul left right ihLeft ihRight =>
      have hLeftNext : nextSlot ≤ (compile left nextSlot).nextSlot :=
        le_compile_nextSlot left nextSlot
      have hRightSources : right.SourcesBelow (compile left nextSlot).nextSlot :=
        sourcesBelow_mono hLeftNext hSources.2
      have hSplit := (blockHolds_append assignment
        ((compile left nextSlot).gates ++
          (compile right (compile left nextSlot).nextSlot).gates)
        [.mul (compile right (compile left nextSlot).nextSlot).nextSlot
          (compile left nextSlot).outputSlot
          (compile right (compile left nextSlot).nextSlot).outputSlot]).1
          (by simpa only [compile] using hBlock)
      have hCore := (blockHolds_append assignment
        (compile left nextSlot).gates
        (compile right (compile left nextSlot).nextSlot).gates).1 hSplit.1
      have hGate :
          (StraightLineGate.mul (compile right (compile left nextSlot).nextSlot).nextSlot
            (compile left nextSlot).outputSlot
            (compile right (compile left nextSlot).nextSlot).outputSlot).holds assignment := by
        simpa [blockHolds] using hSplit.2
      rw [show (compile (.mul left right) nextSlot).outputSlot =
          (compile right (compile left nextSlot).nextSlot).nextSlot by rfl]
      rw [hGate, ihLeft hSources.1 hCore.1, ihRight hRightSources hCore.2]
      rfl

/-- Helper for Theorem 1.4: construct the extended assignment obtained by executing every gate
emitted for an arithmetic expression. -/
def realize : ArithmeticExpression → ℕ → List ℤ → List ℤ
  | .source _, _, assignment => assignment
  | .const value, _, assignment => assignment ++ [value]
  | .add left right, nextSlot, assignment =>
      let leftCode := compile left nextSlot
      let leftAssignment := realize left nextSlot assignment
      let rightCode := compile right leftCode.nextSlot
      let rightAssignment := realize right leftCode.nextSlot leftAssignment
      rightAssignment ++
        [rightAssignment.getD leftCode.outputSlot 0 +
          rightAssignment.getD rightCode.outputSlot 0]
  | .mul left right, nextSlot, assignment =>
      let leftCode := compile left nextSlot
      let leftAssignment := realize left nextSlot assignment
      let rightCode := compile right leftCode.nextSlot
      let rightAssignment := realize right leftCode.nextSlot leftAssignment
      rightAssignment ++
        [rightAssignment.getD leftCode.outputSlot 0 *
          rightAssignment.getD rightCode.outputSlot 0]

/-- Helper for Theorem 1.4: expression execution only appends fresh values to its input
assignment. -/
lemma exists_eq_append_realize (expression : ArithmeticExpression) (nextSlot : ℕ)
    (assignment : List ℤ) :
    ∃ extension, realize expression nextSlot assignment = assignment ++ extension := by
  induction expression generalizing nextSlot assignment with
  | source slot =>
      exact ⟨[], by simp [realize]⟩
  | const value =>
      exact ⟨[value], rfl⟩
  | add left right ihLeft ihRight =>
      obtain ⟨leftExtension, hLeft⟩ := ihLeft nextSlot assignment
      obtain ⟨rightExtension, hRight⟩ :=
        ihRight (compile left nextSlot).nextSlot (realize left nextSlot assignment)
      refine ⟨leftExtension ++ rightExtension ++
        [(realize right (compile left nextSlot).nextSlot (realize left nextSlot assignment)).getD
            (compile left nextSlot).outputSlot 0 +
          (realize right (compile left nextSlot).nextSlot (realize left nextSlot assignment)).getD
            (compile right (compile left nextSlot).nextSlot).outputSlot 0], ?_⟩
      rw [realize, hRight, hLeft]
      simp only [List.append_assoc]
  | mul left right ihLeft ihRight =>
      obtain ⟨leftExtension, hLeft⟩ := ihLeft nextSlot assignment
      obtain ⟨rightExtension, hRight⟩ :=
        ihRight (compile left nextSlot).nextSlot (realize left nextSlot assignment)
      refine ⟨leftExtension ++ rightExtension ++
        [(realize right (compile left nextSlot).nextSlot (realize left nextSlot assignment)).getD
            (compile left nextSlot).outputSlot 0 *
          (realize right (compile left nextSlot).nextSlot (realize left nextSlot assignment)).getD
            (compile right (compile left nextSlot).nextSlot).outputSlot 0], ?_⟩
      rw [realize, hRight, hLeft]
      simp only [List.append_assoc]

/-- Helper for Theorem 1.4: executing a compilation extends an assignment to exactly its returned
next-free-slot boundary. -/
lemma length_realize {expression : ArithmeticExpression} {nextSlot : ℕ} {assignment : List ℤ}
    (hLength : assignment.length = nextSlot) :
    (realize expression nextSlot assignment).length = (compile expression nextSlot).nextSlot := by
  induction expression generalizing nextSlot assignment with
  | source slot =>
      simpa [realize, compile] using hLength
  | const value =>
      simp [realize, compile, hLength]
  | add left right ihLeft ihRight =>
      have hLeft := ihLeft hLength
      have hRight := ihRight hLeft
      simpa [realize, compile, hRight]
  | mul left right ihLeft ihRight =>
      have hLeft := ihLeft hLength
      have hRight := ihRight hLeft
      simpa [realize, compile, hRight]

/-- Helper for Theorem 1.4: executing the compiler produces an assignment satisfying every
emitted gate. -/
lemma blockHolds_realize {expression : ArithmeticExpression} {nextSlot : ℕ}
    {assignment : List ℤ} (hSources : expression.SourcesBelow nextSlot)
    (hLength : assignment.length = nextSlot) :
    blockHolds (realize expression nextSlot assignment) (compile expression nextSlot).gates := by
  induction expression generalizing nextSlot assignment with
  | source slot =>
      trivial
  | const value =>
      simp only [realize, compile, blockHolds, StraightLineGate.holds, true_and]
      rw [List.getD_append_right]
      · simp [hLength]
      · omega
  | add left right ihLeft ihRight =>
      have hLeftLength := length_realize (expression := left) hLength
      have hLeftNext : nextSlot ≤ (compile left nextSlot).nextSlot :=
        le_compile_nextSlot left nextSlot
      have hRightSources : right.SourcesBelow (compile left nextSlot).nextSlot :=
        sourcesBelow_mono hLeftNext hSources.2
      have hRightLength := length_realize (expression := right) hLeftLength
      have hLeftOutputBound :
          (compile left nextSlot).outputSlot <
            (realize right (compile left nextSlot).nextSlot
              (realize left nextSlot assignment)).length := by
        rw [hRightLength]
        exact lt_of_lt_of_le (compile_outputSlot_lt hSources.1)
          (le_compile_nextSlot right _)
      have hRightOutputBound :
          (compile right (compile left nextSlot).nextSlot).outputSlot <
            (realize right (compile left nextSlot).nextSlot
              (realize left nextSlot assignment)).length := by
        simpa [hRightLength] using compile_outputSlot_lt hRightSources
      have hLeftBlock := ihLeft hSources.1 hLength
      have hRightBlock := ihRight hRightSources hLeftLength
      obtain ⟨rightExtension, hRightAppend⟩ :=
        exists_eq_append_realize right (compile left nextSlot).nextSlot
          (realize left nextSlot assignment)
      have hLeftRange := compile_gates_inRange hSources.1
      have hLeftPreserved :
          blockHolds
            (realize right (compile left nextSlot).nextSlot (realize left nextSlot assignment))
            (compile left nextSlot).gates := by
        rw [hRightAppend, blockHolds_append_assignment]
        · exact hLeftBlock
        · simpa [hLeftLength] using hLeftRange
      have hCore :
          blockHolds
            (realize right (compile left nextSlot).nextSlot (realize left nextSlot assignment))
            ((compile left nextSlot).gates ++
              (compile right (compile left nextSlot).nextSlot).gates) :=
        (blockHolds_append _ _ _).2 ⟨hLeftPreserved, hRightBlock⟩
      have hCoreRange : ∀ gate ∈
          (compile left nextSlot).gates ++
            (compile right (compile left nextSlot).nextSlot).gates,
          gate.InRange
            (realize right (compile left nextSlot).nextSlot
              (realize left nextSlot assignment)).length := by
        intro gate hGate
        rcases List.mem_append.1 hGate with hGate | hGate
        · apply StraightLineGate.InRange.mono (hLeftRange gate hGate)
          rw [hRightLength]
          exact le_compile_nextSlot right _
        · simpa [hRightLength] using compile_gates_inRange hRightSources gate hGate
      rw [show (compile (.add left right) nextSlot).gates =
          (compile left nextSlot).gates ++
            (compile right (compile left nextSlot).nextSlot).gates ++
              [.add (compile right (compile left nextSlot).nextSlot).nextSlot
                (compile left nextSlot).outputSlot
                (compile right (compile left nextSlot).nextSlot).outputSlot] by rfl]
      rw [show realize (.add left right) nextSlot assignment =
          realize right (compile left nextSlot).nextSlot (realize left nextSlot assignment) ++
            [(realize right (compile left nextSlot).nextSlot
                (realize left nextSlot assignment)).getD
                (compile left nextSlot).outputSlot 0 +
              (realize right (compile left nextSlot).nextSlot
                (realize left nextSlot assignment)).getD
                (compile right (compile left nextSlot).nextSlot).outputSlot 0] by rfl]
      apply (blockHolds_append _ _ _).2
      constructor
      · exact (blockHolds_append_assignment hCoreRange).2 hCore
      · simp only [blockHolds, StraightLineGate.holds, true_and]
        constructor
        · rw [List.getD_append _ _ _ _ hLeftOutputBound,
            List.getD_append _ _ _ _ hRightOutputBound,
            List.getD_append_right]
          · rw [hRightLength, Nat.sub_self]
            simp [List.getD]
          · omega
        · trivial
  | mul left right ihLeft ihRight =>
      have hLeftLength := length_realize (expression := left) hLength
      have hLeftNext : nextSlot ≤ (compile left nextSlot).nextSlot :=
        le_compile_nextSlot left nextSlot
      have hRightSources : right.SourcesBelow (compile left nextSlot).nextSlot :=
        sourcesBelow_mono hLeftNext hSources.2
      have hRightLength := length_realize (expression := right) hLeftLength
      have hLeftOutputBound :
          (compile left nextSlot).outputSlot <
            (realize right (compile left nextSlot).nextSlot
              (realize left nextSlot assignment)).length := by
        rw [hRightLength]
        exact lt_of_lt_of_le (compile_outputSlot_lt hSources.1)
          (le_compile_nextSlot right _)
      have hRightOutputBound :
          (compile right (compile left nextSlot).nextSlot).outputSlot <
            (realize right (compile left nextSlot).nextSlot
              (realize left nextSlot assignment)).length := by
        simpa [hRightLength] using compile_outputSlot_lt hRightSources
      have hLeftBlock := ihLeft hSources.1 hLength
      have hRightBlock := ihRight hRightSources hLeftLength
      obtain ⟨rightExtension, hRightAppend⟩ :=
        exists_eq_append_realize right (compile left nextSlot).nextSlot
          (realize left nextSlot assignment)
      have hLeftRange := compile_gates_inRange hSources.1
      have hLeftPreserved :
          blockHolds
            (realize right (compile left nextSlot).nextSlot (realize left nextSlot assignment))
            (compile left nextSlot).gates := by
        rw [hRightAppend, blockHolds_append_assignment]
        · exact hLeftBlock
        · simpa [hLeftLength] using hLeftRange
      have hCore :
          blockHolds
            (realize right (compile left nextSlot).nextSlot (realize left nextSlot assignment))
            ((compile left nextSlot).gates ++
              (compile right (compile left nextSlot).nextSlot).gates) :=
        (blockHolds_append _ _ _).2 ⟨hLeftPreserved, hRightBlock⟩
      have hCoreRange : ∀ gate ∈
          (compile left nextSlot).gates ++
            (compile right (compile left nextSlot).nextSlot).gates,
          gate.InRange
            (realize right (compile left nextSlot).nextSlot
              (realize left nextSlot assignment)).length := by
        intro gate hGate
        rcases List.mem_append.1 hGate with hGate | hGate
        · apply StraightLineGate.InRange.mono (hLeftRange gate hGate)
          rw [hRightLength]
          exact le_compile_nextSlot right _
        · simpa [hRightLength] using compile_gates_inRange hRightSources gate hGate
      rw [show (compile (.mul left right) nextSlot).gates =
          (compile left nextSlot).gates ++
            (compile right (compile left nextSlot).nextSlot).gates ++
              [.mul (compile right (compile left nextSlot).nextSlot).nextSlot
                (compile left nextSlot).outputSlot
                (compile right (compile left nextSlot).nextSlot).outputSlot] by rfl]
      rw [show realize (.mul left right) nextSlot assignment =
          realize right (compile left nextSlot).nextSlot (realize left nextSlot assignment) ++
            [(realize right (compile left nextSlot).nextSlot
                (realize left nextSlot assignment)).getD
                (compile left nextSlot).outputSlot 0 *
              (realize right (compile left nextSlot).nextSlot
                (realize left nextSlot assignment)).getD
                (compile right (compile left nextSlot).nextSlot).outputSlot 0] by rfl]
      apply (blockHolds_append _ _ _).2
      constructor
      · exact (blockHolds_append_assignment hCoreRange).2 hCore
      · simp only [blockHolds, StraightLineGate.holds, true_and]
        constructor
        · rw [List.getD_append _ _ _ _ hLeftOutputBound,
            List.getD_append _ _ _ _ hRightOutputBound,
            List.getD_append_right]
          · rw [hRightLength, Nat.sub_self]
            simp [List.getD]
          · omega
        · trivial

end ArithmeticExpression

/-- Helper for Theorem 1.4: the straight-line gates for a polynomial, followed by an equation
forcing the computed output to zero. -/
def polynomialGates (polynomialCode : Hilbert10.PolynomialCode) : List StraightLineGate :=
  let expression := ArithmeticExpression.polynomial polynomialCode.terms
  let compilation := ArithmeticExpression.compile expression polynomialCode.arity
  compilation.gates ++ [.const compilation.outputSlot 0]

/-- Helper for Theorem 1.4: compile an integer polynomial code to a quadratic-feasibility
instance with one slot per source or intermediate value. -/
def polynomialInstance (polynomialCode : Hilbert10.PolynomialCode) : Code :=
  let expression := ArithmeticExpression.polynomial polynomialCode.terms
  let compilation := ArithmeticExpression.compile expression polynomialCode.arity
  blockInstance compilation.nextSlot (polynomialGates polynomialCode)

/-- Helper for Theorem 1.4: the polynomial expression reads only the presentation arity declared
by its sparse code. -/
lemma polynomial_sourcesBelow (polynomialCode : Hilbert10.PolynomialCode) :
    (ArithmeticExpression.polynomial polynomialCode.terms).SourcesBelow polynomialCode.arity := by
  apply ArithmeticExpression.sourcesBelow_polynomial
  intro codedTerm hTerm
  exact Hilbert10.PolynomialCode.length_le_arity hTerm

/-- Helper for Theorem 1.4: the generated quadratic instance is solvable exactly when the input
integer polynomial code has an integer root. -/
lemma polynomialInstance_correct (polynomialCode : Hilbert10.PolynomialCode) :
    hasSolution (polynomialInstance polynomialCode) ↔ Hilbert10.IntSolvable polynomialCode := by
  let expression := ArithmeticExpression.polynomial polynomialCode.terms
  let compilation := ArithmeticExpression.compile expression polynomialCode.arity
  have hSources : expression.SourcesBelow polynomialCode.arity :=
    polynomial_sourcesBelow polynomialCode
  have hOutput : compilation.outputSlot < compilation.nextSlot :=
    ArithmeticExpression.compile_outputSlot_lt hSources
  have hPositive : 0 < compilation.nextSlot := lt_of_le_of_lt (Nat.zero_le _) hOutput
  have hGates : polynomialGates polynomialCode ≠ [] := by
    simp [polynomialGates, expression, compilation]
  have hRange : ∀ gate ∈ polynomialGates polynomialCode,
      gate.InRange compilation.nextSlot := by
    intro gate hGate
    simp only [polynomialGates, expression, compilation, List.mem_append,
      List.mem_singleton] at hGate
    rcases hGate with hGate | rfl
    · exact ArithmeticExpression.compile_gates_inRange hSources gate hGate
    · simpa [StraightLineGate.InRange] using hOutput
  rw [polynomialInstance, show
      (let expression := ArithmeticExpression.polynomial polynomialCode.terms
       let compilation := ArithmeticExpression.compile expression polynomialCode.arity
       blockInstance compilation.nextSlot (polynomialGates polynomialCode)) =
        blockInstance compilation.nextSlot (polynomialGates polynomialCode) by rfl]
  rw [straightLineInstance_correct hPositive hGates hRange]
  constructor
  · rintro ⟨assignment, hLength, hBlock⟩
    have hSplit := (ArithmeticExpression.blockHolds_append assignment compilation.gates
      [.const compilation.outputSlot 0]).1 (by
        simpa [polynomialGates, expression, compilation] using hBlock)
    have hZero : assignment.getD compilation.outputSlot 0 = 0 := by
      simpa [blockHolds, StraightLineGate.holds] using hSplit.2
    have hComputed : assignment.getD compilation.outputSlot 0 = expression.eval assignment :=
      ArithmeticExpression.compile_correct hSources assignment hSplit.1
    refine ⟨assignment, ?_⟩
    rw [← ArithmeticExpression.eval_polynomial]
    exact hComputed.symm.trans hZero
  · rintro ⟨sourceAssignment, hRoot⟩
    obtain ⟨normalizedAssignment, hNormalizedLength, hNormalizedRoot⟩ :=
      Hilbert10.PolynomialCode.exists_length_eq_arity_evalInt_eq
        polynomialCode sourceAssignment
    let fullAssignment :=
      ArithmeticExpression.realize expression polynomialCode.arity normalizedAssignment
    have hFullLength : fullAssignment.length = compilation.nextSlot :=
      ArithmeticExpression.length_realize hNormalizedLength
    have hCore : blockHolds fullAssignment compilation.gates :=
      ArithmeticExpression.blockHolds_realize hSources hNormalizedLength
    obtain ⟨extension, hExtension⟩ :=
      ArithmeticExpression.exists_eq_append_realize expression polynomialCode.arity
        normalizedAssignment
    have hExpressionStable : expression.eval fullAssignment = expression.eval normalizedAssignment := by
      unfold fullAssignment
      rw [hExtension]
      exact ArithmeticExpression.eval_append hSources (by omega)
    have hComputed : fullAssignment.getD compilation.outputSlot 0 = expression.eval fullAssignment :=
      ArithmeticExpression.compile_correct hSources fullAssignment hCore
    have hOutputZero : fullAssignment.getD compilation.outputSlot 0 = 0 := by
      rw [hComputed, hExpressionStable, ArithmeticExpression.eval_polynomial,
        hNormalizedRoot, hRoot]
    refine ⟨fullAssignment, hFullLength, ?_⟩
    apply (ArithmeticExpression.blockHolds_append _ _ _).2
    exact ⟨hCore, by simpa [blockHolds, StraightLineGate.holds] using hOutputZero⟩

/-- Helper for Theorem 1.4: the two quadratic inequalities fixing source slot `0` to a natural
input, written directly so only their constant coefficients vary. -/
def inputConstraints (input : ℕ) : List Constraint :=
  [Constraint.ofData (-(input : ℤ)) [LinearTerm.ofData 0 1] [],
    Constraint.ofData (input : ℤ) [LinearTerm.ofData 0 (-1)] []]

/-- Helper for Theorem 1.4: attach the varying input equation to a fixed tail of constraints. -/
def fixedInputInstance (variableCount : ℕ) (fixedConstraints : List Constraint)
    (input : ℕ) : Code :=
  Code.ofData variableCount (inputConstraints input ++ fixedConstraints)

/-- Helper for Theorem 1.4: the direct input constraints are exactly the compilation of the
constant gate fixing slot `0`. -/
lemma inputConstraints_eq_compile (input : ℕ) :
    inputConstraints input = (StraightLineGate.const 0 (input : ℤ)).compile := by
  simp [inputConstraints, StraightLineGate.compile, StraightLineGate.baseConstraint,
    Constraint.asEquation, Constraint.negate, Constraint.ofData, LinearTerm.ofData,
    LinearTerm.negate]

/-- Helper for Theorem 1.4: specializing the single input constant of a fixed quadratic template
is a computable operation. -/
lemma computable_fixedInputInstance (variableCount : ℕ) (fixedConstraints : List Constraint) :
    Computable (fixedInputInstance variableCount fixedConstraints) := by
  have hFirst : Primrec fun input : ℕ ↦
      Constraint.ofData (-(input : ℤ)) [LinearTerm.ofData 0 1] [] := by
    have hData := (Primrec.int_neg.comp Primrec.int_natCast).pair
      ((Primrec.const [LinearTerm.ofData 0 1]).pair
        (Primrec.const ([] : List QuadraticTerm)))
    exact (Constraint.primrec_ofData.comp hData).of_eq fun _ ↦ rfl
  have hSecond : Primrec fun input : ℕ ↦
      Constraint.ofData (input : ℤ) [LinearTerm.ofData 0 (-1)] [] := by
    have hData := Primrec.int_natCast.pair
      ((Primrec.const [LinearTerm.ofData 0 (-1)]).pair
        (Primrec.const ([] : List QuadraticTerm)))
    exact (Constraint.primrec_ofData.comp hData).of_eq fun _ ↦ rfl
  have hInputConstraints : Primrec inputConstraints := by
    have hTail : Primrec fun input : ℕ ↦
        Constraint.ofData (input : ℤ) [LinearTerm.ofData 0 (-1)] [] :: [] :=
      Primrec₂.comp Primrec.list_cons hSecond (Primrec.const [])
    have hList : Primrec fun input : ℕ ↦
        Constraint.ofData (-(input : ℤ)) [LinearTerm.ofData 0 1] [] ::
          Constraint.ofData (input : ℤ) [LinearTerm.ofData 0 (-1)] [] :: [] :=
      Primrec₂.comp Primrec.list_cons hFirst hTail
    exact hList.of_eq fun _ ↦ rfl
  have hConstraints : Primrec fun input : ℕ ↦ inputConstraints input ++ fixedConstraints :=
    Primrec₂.comp Primrec.list_append hInputConstraints (Primrec.const fixedConstraints)
  have hCode : Primrec fun input : ℕ ↦
      Code.ofData variableCount (inputConstraints input ++ fixedConstraints) := by
    exact Code.primrec_ofData.comp ((Primrec.const variableCount).pair hConstraints)
  exact hCode.to_comp

/-- Helper for Theorem 1.4: a fixed natural polynomial template, with all source slots guarded
as nonnegative and slot `0` fixed to the varying input. -/
def naturalPolynomialInstance (polynomialCode : Hilbert10.PolynomialCode)
    (sourceCount input : ℕ) : Code :=
  let expression := ArithmeticExpression.polynomial polynomialCode.terms
  let compilation := ArithmeticExpression.compile expression sourceCount
  let fixedGates :=
    (List.range sourceCount).map StraightLineGate.nonneg ++ compilation.gates ++
      [.const compilation.outputSlot 0]
  fixedInputInstance compilation.nextSlot (compileBlock fixedGates) input

/-- Helper for Theorem 1.4: specializing the input of a fixed natural-polynomial gate template is
computable. -/
lemma computable_naturalPolynomialInstance (polynomialCode : Hilbert10.PolynomialCode)
    (sourceCount : ℕ) :
    Computable (naturalPolynomialInstance polynomialCode sourceCount) := by
  exact computable_fixedInputInstance _ _

/-- Helper for Theorem 1.4: the natural-polynomial instance is the corresponding straight-line
block with its input gate prepended. -/
lemma naturalPolynomialInstance_eq_blockInstance (polynomialCode : Hilbert10.PolynomialCode)
    (sourceCount input : ℕ) :
    naturalPolynomialInstance polynomialCode sourceCount input =
      let expression := ArithmeticExpression.polynomial polynomialCode.terms
      let compilation := ArithmeticExpression.compile expression sourceCount
      blockInstance compilation.nextSlot
        (.const 0 (input : ℤ) ::
          (List.range sourceCount).map StraightLineGate.nonneg ++ compilation.gates ++
            [.const compilation.outputSlot 0]) := by
  rw [naturalPolynomialInstance]
  simp only [fixedInputInstance, blockInstance, compileBlock, inputConstraints_eq_compile]
  congr 1

/-- Helper for Theorem 1.4: a list of nonnegativity gates holds exactly when every indexed slot
is nonnegative. -/
lemma blockHolds_map_nonneg (assignment : List ℤ) (indices : List ℕ) :
    blockHolds assignment (indices.map StraightLineGate.nonneg) ↔
      ∀ index ∈ indices, 0 ≤ assignment.getD index 0 := by
  induction indices with
  | nil =>
      simp [blockHolds]
  | cons index indices ih =>
      simp [blockHolds, StraightLineGate.holds, ih]

/-- Helper for Theorem 1.4: casting `Int.toNat` back to integers recovers a finite prefix whose
entries are all nonnegative. -/
lemma map_natCast_toNat_take {assignment : List ℤ} {count : ℕ}
    (hCount : count ≤ assignment.length)
    (hNonneg : ∀ index < count, 0 ≤ assignment.getD index 0) :
    (assignment.take count).map (fun value ↦ ((value.toNat : ℕ) : ℤ)) =
      assignment.take count := by
  refine List.ext_getElem (by simp) fun index hMap hTake ↦ ?_
  have hIndex : index < count := by
    exact lt_of_lt_of_le hTake (by simp)
  have hAssignmentIndex : index < assignment.length := lt_of_lt_of_le hIndex hCount
  have hValue := hNonneg index hIndex
  have hGetD : assignment.getD index 0 = assignment[index]'hAssignmentIndex := by
    exact List.getD_eq_getElem assignment 0 hAssignmentIndex
  simp only [List.getElem_map, List.getElem_take]
  rw [hGetD] at hValue
  omega

/-- Helper for Theorem 1.4: the fixed natural-polynomial template is solvable exactly when the
polynomial has a natural root of the chosen source length whose first coordinate is the input. -/
lemma naturalPolynomialInstance_correct (polynomialCode : Hilbert10.PolynomialCode)
    (sourceCount input : ℕ) (hSourceCount : 0 < sourceCount)
    (hArity : polynomialCode.arity ≤ sourceCount) :
    hasSolution (naturalPolynomialInstance polynomialCode sourceCount input) ↔
      ∃ values : List ℕ,
        values.length = sourceCount ∧ values.getD 0 0 = input ∧ polynomialCode.eval values = 0 := by
  let expression := ArithmeticExpression.polynomial polynomialCode.terms
  let compilation := ArithmeticExpression.compile expression sourceCount
  let nonnegGates := (List.range sourceCount).map StraightLineGate.nonneg
  let gates :=
    .const 0 (input : ℤ) :: nonnegGates ++ compilation.gates ++
      [.const compilation.outputSlot 0]
  have hSources : expression.SourcesBelow sourceCount :=
    ArithmeticExpression.sourcesBelow_mono hArity (polynomial_sourcesBelow polynomialCode)
  have hNext : sourceCount ≤ compilation.nextSlot :=
    ArithmeticExpression.le_compile_nextSlot expression sourceCount
  have hOutput : compilation.outputSlot < compilation.nextSlot :=
    ArithmeticExpression.compile_outputSlot_lt hSources
  have hPositive : 0 < compilation.nextSlot := lt_of_lt_of_le hSourceCount hNext
  have hGates : gates ≠ [] := by
    simp [gates]
  have hRange : ∀ gate ∈ gates, gate.InRange compilation.nextSlot := by
    intro gate hGate
    change gate ∈
      (.const 0 (input : ℤ) ::
        nonnegGates ++ compilation.gates ++ [.const compilation.outputSlot 0]) at hGate
    rcases List.mem_cons.1 hGate with hHead | hGate
    · subst gate
      simpa [StraightLineGate.InRange] using lt_of_lt_of_le hSourceCount hNext
    · have hTail := (List.mem_append.1 hGate)
      rcases hTail with hNonnegOrCore | hOutputGate
      · rcases List.mem_append.1 hNonnegOrCore with hNonneg | hCore
        · obtain ⟨index, hIndex, rfl⟩ := List.mem_map.1 hNonneg
          simp only [StraightLineGate.InRange]
          exact lt_of_lt_of_le (List.mem_range.1 hIndex) hNext
        · exact ArithmeticExpression.compile_gates_inRange hSources gate hCore
      · simp only [List.mem_singleton] at hOutputGate
        subst hOutputGate
        simpa [StraightLineGate.InRange] using hOutput
  rw [naturalPolynomialInstance_eq_blockInstance]
  change hasSolution (blockInstance compilation.nextSlot gates) ↔ _
  rw [straightLineInstance_correct hPositive hGates hRange]
  constructor
  · rintro ⟨assignment, hLength, hBlock⟩
    have hInputAndTail :
        (StraightLineGate.const 0 (input : ℤ)).holds assignment ∧
          blockHolds assignment
            (nonnegGates ++ compilation.gates ++ [.const compilation.outputSlot 0]) := by
      simpa [gates, blockHolds] using hBlock
    have hTail := (ArithmeticExpression.blockHolds_append assignment
      (nonnegGates ++ compilation.gates) [.const compilation.outputSlot 0]).1
        hInputAndTail.2
    have hNonnegAndCore :=
      (ArithmeticExpression.blockHolds_append assignment nonnegGates compilation.gates).1 hTail.1
    have hInputInteger : assignment.getD 0 0 = (input : ℤ) := by
      simpa [StraightLineGate.holds] using hInputAndTail.1
    have hNonneg : ∀ index < sourceCount, 0 ≤ assignment.getD index 0 := by
      intro index hIndex
      exact (blockHolds_map_nonneg assignment (List.range sourceCount)).1 hNonnegAndCore.1
        index (List.mem_range.2 hIndex)
    have hOutputZero : assignment.getD compilation.outputSlot 0 = 0 := by
      simpa [blockHolds, StraightLineGate.holds] using hTail.2
    have hExpressionZero : expression.eval assignment = 0 := by
      rw [← ArithmeticExpression.compile_correct hSources assignment hNonnegAndCore.2]
      exact hOutputZero
    let values := (assignment.take sourceCount).map Int.toNat
    have hValuesLength : values.length = sourceCount := by
      simp only [values, List.length_map, List.length_take, hLength]
      omega
    have hCast : values.map (Nat.cast : ℕ → ℤ) = assignment.take sourceCount := by
      unfold values
      rw [List.map_map]
      exact map_natCast_toNat_take (assignment := assignment) (by omega) hNonneg
    have hTakeEval : polynomialCode.evalInt (assignment.take sourceCount) = 0 := by
      have hSplit := polynomialCode.evalInt_append_of_arity_le
        (x := assignment.take sourceCount) (y := assignment.drop sourceCount) (by
          simp only [List.length_take, hLength]
          omega)
      rw [List.take_append_drop] at hSplit
      rw [← hSplit, ← ArithmeticExpression.eval_polynomial]
      exact hExpressionZero
    have hNaturalEval : polynomialCode.eval values = 0 := by
      calc
        polynomialCode.eval values =
            polynomialCode.evalInt (values.map (Nat.cast : ℕ → ℤ)) :=
          (Hilbert10.PolynomialCode.evalInt_map_natCast polynomialCode values).symm
        _ = polynomialCode.evalInt (assignment.take sourceCount) := by
          simpa using congrArg polynomialCode.evalInt hCast
        _ = 0 := hTakeEval
    have hInputNatural : values.getD 0 0 = input := by
      have hTakeGetD : (assignment.take sourceCount).getD 0 0 = assignment.getD 0 0 := by
        have hTakePositive : 0 < (assignment.take sourceCount).length := by
          simp only [List.length_take, hLength]
          omega
        have hAppend := List.getD_append (assignment.take sourceCount)
          (assignment.drop sourceCount) 0 0 hTakePositive
        rw [List.take_append_drop] at hAppend
        exact hAppend.symm
      unfold values
      have hMap :
          ((assignment.take sourceCount).map Int.toNat).getD 0 0 =
            Int.toNat ((assignment.take sourceCount).getD 0 0) := by
        simpa using List.getD_map (assignment.take sourceCount) (0 : ℤ) Int.toNat
      rw [hMap, hTakeGetD, hInputInteger]
      omega
    exact ⟨values, hValuesLength, hInputNatural, hNaturalEval⟩
  · rintro ⟨values, hValuesLength, hInputNatural, hNaturalRoot⟩
    let sourceAssignment := values.map (Nat.cast : ℕ → ℤ)
    let assignment := ArithmeticExpression.realize expression sourceCount sourceAssignment
    have hSourceLength : sourceAssignment.length = sourceCount := by
      simpa [sourceAssignment] using hValuesLength
    have hLength : assignment.length = compilation.nextSlot :=
      ArithmeticExpression.length_realize hSourceLength
    have hCore : blockHolds assignment compilation.gates :=
      ArithmeticExpression.blockHolds_realize hSources hSourceLength
    obtain ⟨extension, hExtension⟩ :=
      ArithmeticExpression.exists_eq_append_realize expression sourceCount sourceAssignment
    have hExpressionStable : expression.eval assignment = expression.eval sourceAssignment := by
      unfold assignment
      rw [hExtension]
      exact ArithmeticExpression.eval_append hSources (by omega)
    have hOutputZero : assignment.getD compilation.outputSlot 0 = 0 := by
      rw [ArithmeticExpression.compile_correct hSources assignment hCore,
        hExpressionStable, ArithmeticExpression.eval_polynomial]
      change polynomialCode.evalInt sourceAssignment = 0
      unfold sourceAssignment
      rw [Hilbert10.PolynomialCode.evalInt_map_natCast, hNaturalRoot]
    have hInputInteger : assignment.getD 0 0 = (input : ℤ) := by
      unfold assignment
      rw [hExtension, List.getD_append]
      · have hMap : sourceAssignment.getD 0 0 = (values.getD 0 0 : ℤ) := by
          unfold sourceAssignment
          simpa using List.getD_map values 0 (Nat.cast : ℕ → ℤ)
        rw [hMap, hInputNatural]
      · simpa [sourceAssignment, hValuesLength] using hSourceCount
    have hNonneg : blockHolds assignment nonnegGates := by
      apply (blockHolds_map_nonneg assignment (List.range sourceCount)).2
      intro index hIndex
      unfold assignment
      rw [hExtension, List.getD_append]
      · have hMap : sourceAssignment.getD index 0 = (values.getD index 0 : ℤ) := by
          unfold sourceAssignment
          simpa using List.getD_map values 0 (Nat.cast : ℕ → ℤ)
        rw [hMap]
        exact Int.natCast_nonneg _
      · simpa [sourceAssignment, hValuesLength] using List.mem_range.1 hIndex
    refine ⟨assignment, hLength, ?_⟩
    simp only [gates, blockHolds]
    constructor
    · exact hInputInteger
    · apply (ArithmeticExpression.blockHolds_append _ _ _).2
      constructor
      · exact (ArithmeticExpression.blockHolds_append _ _ _).2 ⟨hNonneg, hCore⟩
      · simpa [blockHolds, StraightLineGate.holds] using hOutputZero


/-- Helper for Theorem 1.4: the remaining source-faithful step is a many-one reduction from the
halting predicate at input `0` to quadratic integer feasibility. -/
private lemma haltingManyOneToHasSolution :
    (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) ≤₀ hasSolution := by
  -- Route correction: the completed DPRM support module now supplies the previously missing
  -- bounded-conjunction argument, so first represent the encoded halting predicate by one fixed
  -- natural polynomial and only then invoke the finite straight-line compiler.
  let R : ℕ → Prop := fun code ↦
    (Nat.Partrec.Code.eval (Denumerable.ofNat Nat.Partrec.Code code) 0).Dom
  have hEncoded : REPred R := by
    exact Partrec.comp (ComputablePred.halting_problem_re 0)
      (Computable.ofNat Nat.Partrec.Code)
  have hDioph : Dioph {values : Fin 1 → ℕ | R (values 0)} :=
    Hilbert10.REPred.dioph (Hilbert10.REPred.fin_one hEncoded)
  obtain ⟨witnessCount, polynomial, hRepresents⟩ :=
    (Hilbert10.dioph_iff_exists_fin_mvPolynomial _).mp hDioph
  obtain ⟨polynomialCode, hArity, hPolynomialCode⟩ :=
    Hilbert10.PolynomialCode.exists_code_representsNat hRepresents
  -- Convert the finite input/witness tuples from the representation theorem to the single list
  -- interface consumed by the quadratic compiler.
  have hListRepresentation (input : ℕ) :
      R input ↔ ∃ values : List ℕ,
        values.length = 1 + witnessCount ∧ values.getD 0 0 = input ∧
          polynomialCode.eval values = 0 := by
    constructor
    · intro hInput
      have hConstantInput : R ((fun _ : Fin 1 ↦ input) 0) := by
        simpa using hInput
      obtain ⟨witnesses, hRoot⟩ :=
        (hPolynomialCode (fun _ : Fin 1 ↦ input)).1 hConstantInput
      refine ⟨List.ofFn (fun _ : Fin 1 ↦ input) ++ List.ofFn witnesses, ?_, ?_, hRoot⟩
      · simp only [List.length_append, List.length_ofFn]
      · simp
    · rintro ⟨values, hLength, hInput, hRoot⟩
      cases values with
      | nil =>
          simp only [List.length_nil] at hLength
          omega
      | cons head tail =>
          have hTailLength : tail.length = witnessCount := by
            simp only [List.length_cons] at hLength
            omega
          have hHead : head = input := by
            simpa using hInput
          subst head
          have hTailOfFn :
              List.ofFn (fun index : Fin witnessCount ↦ tail.getD index 0) = tail :=
            Hilbert10.PolynomialCode.ofFn_getD_of_length_eq hTailLength
          have hConstantInput : R ((fun _ : Fin 1 ↦ input) 0) := by
            apply (hPolynomialCode (fun _ : Fin 1 ↦ input)).2
            refine ⟨fun index ↦ tail.getD index 0, ?_⟩
            rw [hTailOfFn]
            simpa using hRoot
          simpa using hConstantInput
  -- The polynomial and its compiled gate block are fixed; the program code changes only the
  -- computable input constant in slot zero.
  have hSourcePositive : 0 < 1 + witnessCount := by
    omega
  refine ⟨fun code ↦ naturalPolynomialInstance polynomialCode (1 + witnessCount)
      (Encodable.encode code),
    (computable_naturalPolynomialInstance polynomialCode (1 + witnessCount)).comp
      Computable.encode, fun code ↦ ?_⟩
  calc
    (Nat.Partrec.Code.eval code 0).Dom ↔ R (Encodable.encode code) := by
      simp [R]
    _ ↔ ∃ values : List ℕ,
        values.length = 1 + witnessCount ∧ values.getD 0 0 = Encodable.encode code ∧
          polynomialCode.eval values = 0 := hListRepresentation (Encodable.encode code)
    _ ↔ hasSolution
        (naturalPolynomialInstance polynomialCode (1 + witnessCount) (Encodable.encode code)) :=
      (naturalPolynomialInstance_correct polynomialCode (1 + witnessCount)
        (Encodable.encode code)
        hSourcePositive hArity).symm

/-- Theorem 1.4. [Jeroslow] The canonical decision problem asking whether a finite nonempty system
of quadratic inequalities with integer coefficients has an integer solution is undecidable. -/
theorem undecidable :
    ¬ Computable decisionProblem.answer := by
  -- First package the Boolean output as a computable decidable predicate.
  intro hDecision
  have hAnswerTrue : ComputablePred (fun code : Code => decisionProblem.answer code = true) := by
    refine (computablePred_iff_computable_decide : _).2 ?_
    simpa using hDecision
  -- Then transport that computable predicate along the problem specification.
  have hHasSolution : ComputablePred hasSolution := by
    exact ComputablePred.of_eq hAnswerTrue decisionProblem_answer_eq_true_iff
  -- Pull computability back along the halting-to-feasibility reduction.
  have hHalting :
      ComputablePred (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c 0).Dom) :=
    ComputablePred.computable_of_manyOneReducible haltingManyOneToHasSolution hHasSolution
  -- This contradicts the standard undecidability of the halting problem.
  exact ComputablePred.halting_problem 0 hHalting

/-- Computability of the canonical Boolean answer function is equivalent to computability of the
source yes-predicate `hasSolution`. -/
theorem computable_answer_iff_computablePred_hasSolution :
    Computable decisionProblem.answer ↔ ComputablePred hasSolution := by
  classical
  simpa [decisionProblem] using
    ((computablePred_iff_computable_decide :
      ComputablePred hasSolution ↔
        Computable (fun code : Code ↦ decide (hasSolution code)))).symm

/-- The source yes-predicate for quadratic integer feasibility is not computable. -/
theorem hasSolution_not_computable :
    ¬ ComputablePred hasSolution := by
  simpa [computable_answer_iff_computablePred_hasSolution] using undecidable

/-- A computable Boolean decider for solvable coded systems is equivalent to computability of the
source yes-predicate `hasSolution`. -/
theorem computablePred_iff_exists_computableDecider :
    ComputablePred hasSolution ↔
      ∃ decider : Code → Bool,
        Computable decider ∧
          ∀ code, hasSolution code ↔ decider code = true := by
  constructor
  · intro hComputable
    rcases ComputablePred.computable_iff.mp hComputable with
      ⟨decider, hDecider, hSpec⟩
    refine ⟨decider, hDecider, ?_⟩
    intro code
    have hCode : hasSolution code = (decider code : Prop) := congrFun hSpec code
    rw [hCode]
  · rintro ⟨decider, hDecider, hSpec⟩
    refine ComputablePred.computable_iff.mpr ?_
    refine ⟨decider, hDecider, ?_⟩
    funext code
    apply propext
    simpa using hSpec code

/-- No computable Boolean decider recognizes exactly the solvable coded systems of quadratic
integer inequalities. -/
theorem noComputableDecider :
    ¬ ∃ decider : Code → Bool,
        Computable decider ∧
          ∀ code, hasSolution code ↔ decider code = true := by
  simpa [computablePred_iff_exists_computableDecider] using hasSolution_not_computable

end QuadraticIntegerFeasibility
