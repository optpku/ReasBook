import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_12.ch2_sec2_12_proposition_2_21.Linearization
import Mathlib.Tactic

namespace ZeroOnePolynomialProgram

variable {m n : ℕ}

/-- Helper for Proposition 2.21: a binary assignment to the original variables. -/
private abbrev BinaryAssignment (n : ℕ) := Fin n → Fin 2

/-- Helper for Proposition 2.21: the variables consist of original coordinates and assignment
selectors. -/
private abbrev SelectorVariable (n : ℕ) := Fin n ⊕ BinaryAssignment n

/-- Helper for Proposition 2.21: the rows of the finite selector formulation. -/
private inductive SelectorRow (n : ℕ) where
  | oneHotUpper
  | oneHotLower
  | linkUpper (i : Fin n)
  | linkLower (i : Fin n)
  | feasibility (a : BinaryAssignment n)
  | upper (v : SelectorVariable n)
  deriving DecidableEq, Fintype

/-- Helper for Proposition 2.21: the real vector represented by a binary assignment. -/
private def assignmentReal (a : BinaryAssignment n) : Fin n → ℝ :=
  fun i ↦ (a i : ℕ)

/-- Helper for Proposition 2.21: a fixed enumeration of the formulation variables. -/
private noncomputable def selectorVariableEquiv (n : ℕ) :
    Fin (Fintype.card (SelectorVariable n)) ≃ SelectorVariable n :=
  (Fintype.equivFin (SelectorVariable n)).symm

/-- Helper for Proposition 2.21: a fixed enumeration of the formulation rows. -/
private noncomputable def selectorRowEquiv (n : ℕ) :
    Fin (Fintype.card (SelectorRow n)) ≃ SelectorRow n :=
  (Fintype.equivFin (SelectorRow n)).symm

/-- Helper for Proposition 2.21: the original variables embed into the selector formulation. -/
private noncomputable def originalVariableEmbedding (n : ℕ) :
    Fin n ↪ Fin (Fintype.card (SelectorVariable n)) :=
  Function.Embedding.inl.trans (selectorVariableEquiv n).symm.toEmbedding

/-- Helper for Proposition 2.21: the coefficient of a conceptual row and variable. -/
private def selectorCoefficient : SelectorRow n → SelectorVariable n → ℝ
  | .oneHotUpper, .inl _ => 0
  | .oneHotUpper, .inr _ => 1
  | .oneHotLower, .inl _ => 0
  | .oneHotLower, .inr _ => -1
  | .linkUpper i, .inl j => if j = i then 1 else 0
  | .linkUpper i, .inr a => -assignmentReal a i
  | .linkLower i, .inl j => if j = i then -1 else 0
  | .linkLower i, .inr a => assignmentReal a i
  | .feasibility _, .inl _ => 0
  | .feasibility a, .inr b => if b = a then 1 else 0
  | .upper v, w => if w = v then 1 else 0

/-- Helper for Proposition 2.21: a selector is allowed exactly when its assignment is feasible. -/
private noncomputable def selectorFeasibilityBound
    (P : ZeroOnePolynomialProgram m n) (a : BinaryAssignment n) : ℝ :=
  @ite ℝ (assignmentReal a ∈ P.feasibleSet) (Classical.propDecidable _) 1 0

/-- Helper for Proposition 2.21: the right-hand side of each selector row. -/
private noncomputable def selectorRhs (P : ZeroOnePolynomialProgram m n) : SelectorRow n → ℝ
  | .oneHotUpper => 1
  | .oneHotLower => -1
  | .linkUpper _ => 0
  | .linkLower _ => 0
  | .feasibility a => selectorFeasibilityBound P a
  | .upper _ => 1

/-- Helper for Proposition 2.21: objective coefficients supported on assignment selectors. -/
private noncomputable def selectorObjective (P : ZeroOnePolynomialProgram m n) :
    SelectorVariable n → ℝ
  | .inl _ => 0
  | .inr a => P.objectiveValue (assignmentReal a)

/-- Helper for Proposition 2.21: the finite pure binary selector formulation. -/
private noncomputable def selectorProgram (P : ZeroOnePolynomialProgram m n) :
    MixedIntegerLinearProgram
      (Fintype.card (SelectorRow n)) (Fintype.card (SelectorVariable n)) 0 :=
  MixedIntegerLinearProgram.ofCoefficients
    (fun r v ↦ selectorCoefficient (selectorRowEquiv n r) (selectorVariableEquiv n v))
    0
    (fun r ↦ selectorRhs P (selectorRowEquiv n r))
    (fun v ↦ selectorObjective P (selectorVariableEquiv n v))
    0

/-- Helper for Proposition 2.21: matrix multiplication in the enumerated formulation is the
corresponding sum over conceptual selector variables. -/
private theorem selectorProgram_mulVec
    (P : ZeroOnePolynomialProgram m n)
    (z : Fin (Fintype.card (SelectorVariable n)) → ℝ)
    (r : SelectorRow n) :
    (selectorProgram P).integerMatrix.mulVec z ((selectorRowEquiv n).symm r) =
      ∑ v : SelectorVariable n,
        selectorCoefficient r v * z ((selectorVariableEquiv n).symm v) := by
  -- Expand the matrix product, then transport its finite sum through the chosen enumeration.
  rw [Matrix.mulVec, dotProduct]
  unfold selectorProgram MixedIntegerLinearProgram.ofCoefficients
  simpa using
    Equiv.sum_comp (selectorVariableEquiv n)
      (fun v : SelectorVariable n ↦
        selectorCoefficient r v * z ((selectorVariableEquiv n).symm v))

/-- Helper for Proposition 2.21: a dot product over the empty coordinate type vanishes. -/
private theorem emptyDotProduct (f g : Fin 0 → ℝ) : dotProduct f g = 0 := by
  -- The indexing finite set is empty, so its defining sum is zero.
  rw [dotProduct]
  exact Fintype.sum_empty _

/-- Helper for Proposition 2.21: the linear objective is the selector-weighted sum of the
polynomial objective values. -/
private theorem selectorProgram_objectiveValue
    (P : ZeroOnePolynomialProgram m n)
    (z : Fin (Fintype.card (SelectorVariable n)) → ℝ) :
    (selectorProgram P).objectiveValue (z, fun i : Fin 0 ↦ Fin.elim0 i) =
      ∑ a : BinaryAssignment n,
        P.objectiveValue (assignmentReal a) *
          z ((selectorVariableEquiv n).symm (.inr a)) := by
  -- Reindex the integer objective and split the conceptual variable sum into its two blocks.
  rw [MixedIntegerLinearProgram.objectiveValue_def, dotProduct]
  unfold selectorProgram MixedIntegerLinearProgram.ofCoefficients
  rw [emptyDotProduct, add_zero]
  have hreindex :=
    Equiv.sum_comp (selectorVariableEquiv n)
      (fun v : SelectorVariable n ↦
        selectorObjective P v * z ((selectorVariableEquiv n).symm v))
  simpa [selectorObjective] using hreindex

/-- Helper for Proposition 2.21: the upper one-hot row sums all assignment selectors. -/
private theorem selectorProgram_oneHotUpper
    (P : ZeroOnePolynomialProgram m n)
    (z : Fin (Fintype.card (SelectorVariable n)) → ℝ) :
    (selectorProgram P).integerMatrix.mulVec z
        ((selectorRowEquiv n).symm .oneHotUpper) =
      ∑ a : BinaryAssignment n, z ((selectorVariableEquiv n).symm (.inr a)) := by
  -- Use the conceptual row formula; the original-variable block has zero coefficients.
  rw [selectorProgram_mulVec]
  simp [selectorCoefficient]

/-- Helper for Proposition 2.21: the lower one-hot row is the negative selector sum. -/
private theorem selectorProgram_oneHotLower
    (P : ZeroOnePolynomialProgram m n)
    (z : Fin (Fintype.card (SelectorVariable n)) → ℝ) :
    (selectorProgram P).integerMatrix.mulVec z
        ((selectorRowEquiv n).symm .oneHotLower) =
      -(∑ a : BinaryAssignment n, z ((selectorVariableEquiv n).symm (.inr a))) := by
  -- Use the conceptual row formula and pull the common minus sign out of the selector sum.
  rw [selectorProgram_mulVec]
  simp [selectorCoefficient]

/-- Helper for Proposition 2.21: an upper linking row compares an original coordinate with the
selector-weighted assignment coordinate. -/
private theorem selectorProgram_linkUpper
    (P : ZeroOnePolynomialProgram m n)
    (z : Fin (Fintype.card (SelectorVariable n)) → ℝ)
    (i : Fin n) :
    (selectorProgram P).integerMatrix.mulVec z
        ((selectorRowEquiv n).symm (.linkUpper i)) =
      z ((selectorVariableEquiv n).symm (.inl i)) -
        ∑ a : BinaryAssignment n,
          assignmentReal a i * z ((selectorVariableEquiv n).symm (.inr a)) := by
  -- Split the variable sum; the Kronecker coefficient selects the original coordinate.
  rw [selectorProgram_mulVec]
  simp [selectorCoefficient, sub_eq_add_neg]

/-- Helper for Proposition 2.21: a lower linking row is the reverse coordinate difference. -/
private theorem selectorProgram_linkLower
    (P : ZeroOnePolynomialProgram m n)
    (z : Fin (Fintype.card (SelectorVariable n)) → ℝ)
    (i : Fin n) :
    (selectorProgram P).integerMatrix.mulVec z
        ((selectorRowEquiv n).symm (.linkLower i)) =
      -z ((selectorVariableEquiv n).symm (.inl i)) +
        ∑ a : BinaryAssignment n,
          assignmentReal a i * z ((selectorVariableEquiv n).symm (.inr a)) := by
  -- Split the variable sum; the negative Kronecker coefficient selects the original coordinate.
  rw [selectorProgram_mulVec]
  simp [selectorCoefficient]

/-- Helper for Proposition 2.21: a feasibility-filter row reads its single selector. -/
private theorem selectorProgram_feasibility
    (P : ZeroOnePolynomialProgram m n)
    (z : Fin (Fintype.card (SelectorVariable n)) → ℝ)
    (a : BinaryAssignment n) :
    (selectorProgram P).integerMatrix.mulVec z
        ((selectorRowEquiv n).symm (.feasibility a)) =
      z ((selectorVariableEquiv n).symm (.inr a)) := by
  -- The row has one nonzero coefficient, at the selector belonging to `a`.
  rw [selectorProgram_mulVec]
  simp [selectorCoefficient]

/-- Helper for Proposition 2.21: an upper-bound row reads its designated variable. -/
private theorem selectorProgram_upper
    (P : ZeroOnePolynomialProgram m n)
    (z : Fin (Fintype.card (SelectorVariable n)) → ℝ)
    (v : SelectorVariable n) :
    (selectorProgram P).integerMatrix.mulVec z
        ((selectorRowEquiv n).symm (.upper v)) =
      z ((selectorVariableEquiv n).symm v) := by
  -- The row is the coordinate functional at `v`.
  rw [selectorProgram_mulVec]
  simp [selectorCoefficient]

/-- Helper for Proposition 2.21: the empty continuous block contributes zero to every row. -/
private theorem selectorProgram_continuousMulVec
    (P : ZeroOnePolynomialProgram m n)
    (y : Fin 0 → ℝ)
    (r : Fin (Fintype.card (SelectorRow n))) :
    (selectorProgram P).continuousMatrix.mulVec y r = 0 := by
  -- Expand the empty dot product in the continuous block.
  unfold selectorProgram MixedIntegerLinearProgram.ofCoefficients
  rw [Matrix.mulVec, emptyDotProduct]

/-- Helper for Proposition 2.21: looking up an enumerated row recovers its conceptual right-hand
side. -/
private theorem selectorProgram_rhs
    (P : ZeroOnePolynomialProgram m n)
    (r : SelectorRow n) :
    (selectorProgram P).rhs ((selectorRowEquiv n).symm r) = selectorRhs P r := by
  -- Cancel the row enumeration in the defining right-hand-side function.
  unfold selectorProgram MixedIntegerLinearProgram.ofCoefficients
  simp

/-- Helper for Proposition 2.21: feasibility of the selector formulation is characterized by
binarity, one-hot selection, coordinate links, and feasibility filtering. -/
private theorem mem_selectorProgram_iff
    (P : ZeroOnePolynomialProgram m n)
    (z : Fin (Fintype.card (SelectorVariable n)) → ℝ) :
    (z, fun i : Fin 0 ↦ Fin.elim0 i) ∈ (selectorProgram P).mixedZeroOneFeasibleSet ↔
      (∀ v : SelectorVariable n,
        z ((selectorVariableEquiv n).symm v) = 0 ∨
          z ((selectorVariableEquiv n).symm v) = 1) ∧
      (∑ a : BinaryAssignment n,
        z ((selectorVariableEquiv n).symm (.inr a))) = 1 ∧
      (∀ i : Fin n,
        z ((selectorVariableEquiv n).symm (.inl i)) =
          ∑ a : BinaryAssignment n,
            assignmentReal a i * z ((selectorVariableEquiv n).symm (.inr a))) ∧
      (∀ a : BinaryAssignment n,
        z ((selectorVariableEquiv n).symm (.inr a)) ≤
          selectorFeasibilityBound P a) := by
  -- Expand mixed-binary feasibility once; all later reasoning uses the row interface above.
  rw [MixedIntegerLinearProgram.mem_mixedZeroOneFeasibleSet_iff]
  constructor
  · rintro ⟨hrows, hbinary, -⟩
    have hbinary' : ∀ v : SelectorVariable n,
        z ((selectorVariableEquiv n).symm v) = 0 ∨
          z ((selectorVariableEquiv n).symm v) = 1 := by
      intro v
      exact hbinary ((selectorVariableEquiv n).symm v)
    have honeUpper := hrows ((selectorRowEquiv n).symm .oneHotUpper)
    have honeLower := hrows ((selectorRowEquiv n).symm .oneHotLower)
    simp only [Pi.add_apply] at honeUpper honeLower
    rw [selectorProgram_oneHotUpper, selectorProgram_continuousMulVec, add_zero,
      selectorProgram_rhs] at honeUpper
    rw [selectorProgram_oneHotLower, selectorProgram_continuousMulVec, add_zero,
      selectorProgram_rhs] at honeLower
    have hone : (∑ a : BinaryAssignment n,
        z ((selectorVariableEquiv n).symm (.inr a))) = 1 := by
      -- The paired one-hot inequalities force equality.
      simp only [selectorRhs] at honeUpper honeLower
      linarith
    have hlink : ∀ i : Fin n,
        z ((selectorVariableEquiv n).symm (.inl i)) =
          ∑ a : BinaryAssignment n,
            assignmentReal a i * z ((selectorVariableEquiv n).symm (.inr a)) := by
      intro i
      have hupper := hrows ((selectorRowEquiv n).symm (.linkUpper i))
      have hlower := hrows ((selectorRowEquiv n).symm (.linkLower i))
      simp only [Pi.add_apply] at hupper hlower
      rw [selectorProgram_linkUpper, selectorProgram_continuousMulVec, add_zero,
        selectorProgram_rhs] at hupper
      rw [selectorProgram_linkLower, selectorProgram_continuousMulVec, add_zero,
        selectorProgram_rhs] at hlower
      -- The paired linking inequalities identify the original coordinate with its selector sum.
      simp only [selectorRhs] at hupper hlower
      linarith
    have hfilter : ∀ a : BinaryAssignment n,
        z ((selectorVariableEquiv n).symm (.inr a)) ≤
          selectorFeasibilityBound P a := by
      intro a
      have ha := hrows ((selectorRowEquiv n).symm (.feasibility a))
      simp only [Pi.add_apply] at ha
      rw [selectorProgram_feasibility, selectorProgram_continuousMulVec, add_zero,
        selectorProgram_rhs] at ha
      exact ha
    exact ⟨hbinary', hone, hlink, hfilter⟩
  · rintro ⟨hbinary, hone, hlink, hfilter⟩
    refine ⟨?_, ?_, ?_⟩
    · intro r
      rw [← (selectorRowEquiv n).symm_apply_apply r]
      simp only [Pi.add_apply]
      generalize hrow : selectorRowEquiv n r = row
      cases row with
      | oneHotUpper =>
          rw [selectorProgram_oneHotUpper, selectorProgram_continuousMulVec, add_zero,
            selectorProgram_rhs]
          simpa [selectorRhs] using le_of_eq hone
      | oneHotLower =>
          rw [selectorProgram_oneHotLower, selectorProgram_continuousMulVec, add_zero,
            selectorProgram_rhs]
          simp only [selectorRhs]
          linarith
      | linkUpper i =>
          rw [selectorProgram_linkUpper, selectorProgram_continuousMulVec, add_zero,
            selectorProgram_rhs]
          simp only [selectorRhs]
          rw [hlink i]
          simp
      | linkLower i =>
          rw [selectorProgram_linkLower, selectorProgram_continuousMulVec, add_zero,
            selectorProgram_rhs]
          simp only [selectorRhs]
          rw [hlink i]
          simp
      | feasibility a =>
          rw [selectorProgram_feasibility, selectorProgram_continuousMulVec, add_zero,
            selectorProgram_rhs]
          exact hfilter a
      | upper v =>
          rw [selectorProgram_upper, selectorProgram_continuousMulVec, add_zero,
            selectorProgram_rhs]
          rcases hbinary v with hv | hv
          · simp [hv, selectorRhs]
          · simp [hv, selectorRhs]
    · intro j
      simpa using hbinary (selectorVariableEquiv n j)
    · intro i
      exact Fin.elim0 i

/-- Helper for Proposition 2.21: the selector formulation has no nonbinary integer-feasible
points. -/
private theorem selectorProgram_isMixedZeroOne
    (P : ZeroOnePolynomialProgram m n) :
    (selectorProgram P).IsMixedZeroOne := by
  -- It suffices to show that every integer-feasible point satisfies the binary equations.
  rw [MixedIntegerLinearProgram.isMixedZeroOne_iff_feasibleSet_subset_mixedZeroOneFeasibleSet]
  intro xy hxy
  rw [MixedIntegerLinearProgram.mem_feasibleSet_iff] at hxy
  rw [MixedIntegerLinearProgram.mem_mixedZeroOneFeasibleSet_iff]
  rcases hxy with ⟨hrows, hnonneg, hcontinuous, hinteger⟩
  refine ⟨hrows, ?_, hcontinuous⟩
  intro j
  have hupper := hrows
    ((selectorRowEquiv n).symm (.upper (selectorVariableEquiv n j)))
  simp only [Pi.add_apply] at hupper
  rw [selectorProgram_upper, selectorProgram_continuousMulVec, add_zero,
    selectorProgram_rhs] at hupper
  simp only [Equiv.symm_apply_apply] at hupper
  simp only [selectorRhs] at hupper
  rcases hinteger j with ⟨k, hk⟩
  have hk0Real : (0 : ℝ) ≤ xy.1 j := by
    simpa using hnonneg j
  rw [hk] at hk0Real hupper
  have hk0 : (0 : ℤ) ≤ k := by
    exact_mod_cast hk0Real
  have hk1 : k ≤ (1 : ℤ) := by
    exact_mod_cast hupper
  have hk_binary : k = 0 ∨ k = 1 := by
    omega
  rcases hk_binary with hk_zero | hk_one
  · left
    simpa [hk_zero] using hk
  · right
    simpa [hk_one] using hk

/-- Helper for Proposition 2.21: every original feasible point has a one-hot feasible lift with
the same objective value. -/
private theorem selectorProgram_lift
    (P : ZeroOnePolynomialProgram m n)
    {x : Fin n → ℝ}
    (hx : x ∈ P.feasibleSet) :
    ∃ z : Fin (Fintype.card (SelectorVariable n)) → ℝ,
      (z, fun i : Fin 0 ↦ Fin.elim0 i) ∈ (selectorProgram P).mixedZeroOneFeasibleSet ∧
      (∀ i : Fin n, z (originalVariableEmbedding n i) = x i) ∧
      (selectorProgram P).objectiveValue (z, fun i : Fin 0 ↦ Fin.elim0 i) =
        P.objectiveValue x := by
  -- Read the binary original point as an assignment and activate exactly its selector.
  rw [mem_feasibleSet_iff] at hx
  let a : BinaryAssignment n := fun i ↦ if x i = 0 then 0 else 1
  have haReal : assignmentReal a = x := by
    funext i
    rcases hx.2 i with hzero | hone
    · simp [a, assignmentReal, hzero]
    · simp [a, assignmentReal, hone]
  have haFeasible : assignmentReal a ∈ P.feasibleSet := by
    rwa [haReal]
  let z : Fin (Fintype.card (SelectorVariable n)) → ℝ := fun v ↦
    match selectorVariableEquiv n v with
    | .inl i => x i
    | .inr b => if b = a then 1 else 0
  refine ⟨z, (mem_selectorProgram_iff P z).mpr ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro v
      cases v with
      | inl i =>
          simpa [z] using hx.2 i
      | inr b =>
          by_cases hba : b = a
          · right
            simp [z, hba]
          · left
            simp [z, hba]
    · -- The one-hot sum contains exactly the term indexed by `a`.
      simp [z]
    · intro i
      -- The linking sum collapses to the active assignment, whose realization is `x`.
      simp [z, haReal]
    · intro b
      by_cases hba : b = a
      · subst b
        simp [z, selectorFeasibilityBound, haFeasible]
      · by_cases hbFeasible : assignmentReal b ∈ P.feasibleSet
        · simp [z, hba, selectorFeasibilityBound, hbFeasible]
        · simp [z, hba, selectorFeasibilityBound, hbFeasible]
  · intro i
    -- The embedding lands in the original-variable block.
    simp [originalVariableEmbedding, z]
  · -- The selector-weighted linear objective collapses to the original polynomial value.
    rw [selectorProgram_objectiveValue]
    simp [z, haReal]

/-- Helper for Proposition 2.21: every selector-feasible point projects to an original feasible
point with the same objective value. -/
private theorem selectorProgram_project
    (P : ZeroOnePolynomialProgram m n)
    {z : Fin (Fintype.card (SelectorVariable n)) → ℝ}
    (hz : (z, fun i : Fin 0 ↦ Fin.elim0 i) ∈
      (selectorProgram P).mixedZeroOneFeasibleSet) :
    let x : Fin n → ℝ := fun i ↦ z (originalVariableEmbedding n i)
    x ∈ P.feasibleSet ∧
      P.objectiveValue x =
        (selectorProgram P).objectiveValue (z, fun i : Fin 0 ↦ Fin.elim0 i) := by
  -- Extract the four semantic invariants of the selector formulation.
  rcases (mem_selectorProgram_iff P z).mp hz with ⟨hbinary, hone, hlink, hfilter⟩
  let active : Finset (BinaryAssignment n) :=
    Finset.univ.filter fun a ↦ z ((selectorVariableEquiv n).symm (.inr a)) = 1
  have hsumAsCard :
      (∑ a : BinaryAssignment n,
        z ((selectorVariableEquiv n).symm (.inr a))) = (active.card : ℝ) := by
    calc
      (∑ a : BinaryAssignment n,
          z ((selectorVariableEquiv n).symm (.inr a))) =
          ∑ a : BinaryAssignment n, if a ∈ active then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro a _
            rcases hbinary (.inr a) with haZero | haOne
            · simp [active, haZero]
            · simp [active, haOne]
      _ = (active.card : ℝ) := by
        simp
  have hactiveCard : active.card = 1 := by
    rw [hsumAsCard] at hone
    exact_mod_cast hone
  obtain ⟨a, hactive⟩ := Finset.card_eq_one.mp hactiveCard
  have haOne : z ((selectorVariableEquiv n).symm (.inr a)) = 1 := by
    have haMem : a ∈ active := by
      rw [hactive]
      simp
    exact (Finset.mem_filter.mp haMem).2
  have hselector : ∀ b : BinaryAssignment n,
      z ((selectorVariableEquiv n).symm (.inr b)) = if b = a then 1 else 0 := by
    intro b
    by_cases hba : b = a
    · subst b
      simp [haOne]
    · rcases hbinary (.inr b) with hbZero | hbOne
      · simp [hba, hbZero]
      · have hbMem : b ∈ active := Finset.mem_filter.mpr ⟨Finset.mem_univ b, hbOne⟩
        rw [hactive] at hbMem
        exact (hba (Finset.mem_singleton.mp hbMem)).elim
  have haFeasible : assignmentReal a ∈ P.feasibleSet := by
    have haBound := hfilter a
    rw [haOne] at haBound
    by_contra ha
    simp [selectorFeasibilityBound, ha] at haBound
    linarith
  have hprojection :
      (fun i ↦ z (originalVariableEmbedding n i)) = assignmentReal a := by
    funext i
    calc
      z (originalVariableEmbedding n i) =
          z ((selectorVariableEquiv n).symm (.inl i)) := by
            simp [originalVariableEmbedding]
      _ = ∑ b : BinaryAssignment n,
          assignmentReal b i * z ((selectorVariableEquiv n).symm (.inr b)) := hlink i
      _ = assignmentReal a i := by
        simp [hselector]
  refine ⟨?_, ?_⟩
  · -- The linking equations identify the projection with the unique feasible assignment.
    rwa [hprojection]
  · -- The same one-hot collapse identifies the two objective values.
    calc
      P.objectiveValue (fun i ↦ z (originalVariableEmbedding n i)) =
          P.objectiveValue (assignmentReal a) := congrArg P.objectiveValue hprojection
      _ = ∑ b : BinaryAssignment n,
          P.objectiveValue (assignmentReal b) *
            z ((selectorVariableEquiv n).symm (.inr b)) := by
              simp [hselector]
      _ = (selectorProgram P).objectiveValue
          (z, fun i : Fin 0 ↦ Fin.elim0 i) := (selectorProgram_objectiveValue P z).symm

/-- Helper for Proposition 2.21: the finite selector program packaged with its projection and
objective-preservation certificates. -/
private noncomputable def finiteSelectorLinearization
    (P : ZeroOnePolynomialProgram m n) : PureLinearization P :=
  { vars := Fintype.card (SelectorVariable n)
    constraints := Fintype.card (SelectorRow n)
    program := selectorProgram P
    isMixedZeroOne := selectorProgram_isMixedZeroOne P
    xEmbedding := originalVariableEmbedding n
    ofOriginal := fun {_} hx ↦ selectorProgram_lift P hx
    toOriginal := fun {_} hz ↦ selectorProgram_project P hz }

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_12/ch2_sec2_12_proposition_2_21.lean.
Proposition 2.21. Every `0`--`1` polynomial program admits a finite pure `0`--`1` linear
reformulation with additional binary variables and linear constraints, preserving feasibility
under projection and preserving objective values. -/
theorem exists_pureLinearization
    (P : ZeroOnePolynomialProgram m n) :
    Nonempty (PureLinearization P) := by
  -- Package the verified finite selector construction as the required witness.
  exact Nonempty.intro (finiteSelectorLinearization P)

#print axioms exists_pureLinearization

end ZeroOnePolynomialProgram
