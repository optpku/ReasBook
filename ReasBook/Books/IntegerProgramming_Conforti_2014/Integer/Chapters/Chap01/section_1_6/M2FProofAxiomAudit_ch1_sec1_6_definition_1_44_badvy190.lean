/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_definition_1_7.Optimality

open scoped BigOperators IntegerVectorNotation Matrix MixedIntegerNotation

@[expose] public section

section Definition144

namespace OrderedCover

variable {n : ℕ}

/-- The source tuple bridge sending textbook coordinates `(y, x)` to the canonical mixed point in
`MixedRealPoint 1 n`. -/
def point (y : ℝ) (x : Fin n → ℝ) : MixedRealPoint 1 n :=
  (fun _ ↦ y, x)

/-- The first block of `point y x` is the constant one-coordinate function with value `y`. -/
theorem point_fst
    (y : ℝ) (x : Fin n → ℝ) :
    (point y x).1 = fun _ ↦ y := by
  -- The source bridge stores `y` as the unique integer-block coordinate.
  rfl

/-- The second block of `point y x` is exactly the source vector `x`. -/
theorem point_snd
    (y : ℝ) (x : Fin n → ℝ) :
    (point y x).2 = x := by
  -- The source bridge stores `x` unchanged in the continuous block.
  rfl

/-- Helper for Definition 1.44: every `xy : MixedRealPoint 1 n` is the source-form point built
from its unique first coordinate and its second block. -/
theorem point_eta
    (xy : MixedRealPoint 1 n) :
    point (xy.1 0) xy.2 = xy := by
  -- Extensionality reduces the first block to the unique `Fin 1` coordinate and leaves the
  -- second block unchanged.
  apply Prod.ext
  · funext j
    fin_cases j
    rfl
  · rfl

/-- Definition 1.44 (1). The optimization program `min h y + ∑ i, c i * x i` with covering
constraints `b i ≤ y + x i` is the Chapter 1 mixed integer linear program with one integer
coordinate for `y` and `n` continuous coordinates for `x`. -/
def program
    (h : ℝ) (b c : Fin n → ℝ) :
    MixedIntegerLinearProgram n 1 n :=
  MixedIntegerLinearProgram.ofCoefficients
    (fun _ _ ↦ (-1 : ℝ))
    (fun i j ↦ if j = i then (-1 : ℝ) else 0)
    (fun i ↦ -b i)
    (fun _ ↦ h)
    c

/-- The coefficient data of `program h b c` are exactly the source covering inequalities, right
hand side, and objective coefficients from Definition 1.44. -/
theorem program_def
    (h : ℝ) (b c : Fin n → ℝ) :
    program h b c =
      MixedIntegerLinearProgram.ofCoefficients
        (fun _ _ ↦ (-1 : ℝ))
        (fun i j ↦ if j = i then (-1 : ℝ) else 0)
        (fun i ↦ -b i)
        (fun _ ↦ h)
        c := by
  -- `program` is defined by exactly these coefficient arrays.
  rfl

/-- Definition 1.44 (2). The LP relaxation of the ordered-cover program allows both `y` and `x`
to vary over `ℝ≥0`. -/
abbrev lpFeasibleSet
    (h : ℝ) (b c : Fin n → ℝ) :
    Set (MixedRealPoint 1 n) :=
  (program h b c).lpRelaxation

/-- Definition 1.44 (3). The ILP variant of the ordered-cover program requires both the scalar
`y` and the vector `x` to be integral while keeping the same ambient carrier `MixedRealPoint 1 n`.
-/
def ilpFeasibleSet
    (h : ℝ) (b c : Fin n → ℝ) :
    Set (MixedRealPoint 1 n) :=
  lpFeasibleSet h b c ∩ {xy | xy.1 ∈ ℤ^1} ∩ {xy | xy.2 ∈ ℤ^n}

/-- Definition 1.44 (4). The MILP variant of the ordered-cover program requires the scalar `y` to
be integral and leaves the vector `x` continuous. -/
abbrev milpFeasibleSet
    (h : ℝ) (b c : Fin n → ℝ) :
    Set (MixedRealPoint 1 n) :=
  (program h b c).feasibleSet

/-- The source objective of the ordered-cover program is the objective function of
`program h b c`. -/
def objectiveValue
    (h : ℝ) (b c : Fin n → ℝ) :
    MixedRealPoint 1 n → ℝ :=
  (program h b c).objectiveValue

/-- Helper for Definition 1.44: the constant one-coordinate vector with value `y` belongs to
`ℤ^1` exactly when `y` is the real coercion of an integer. -/
theorem constantOne_mem_integerVectors_iff
    (y : ℝ) :
    (fun _ : Fin 1 ↦ y) ∈ ℤ^1 ↔ ∃ z : ℤ, y = (z : ℝ) := by
  constructor
  · intro hyInt
    -- Collapse the one-coordinate integer vector witness to its value at `0`.
    rcases (mem_integerVectors_iff.mp hyInt) with ⟨z, hz⟩
    refine ⟨z 0, ?_⟩
    simpa using congrFun hz 0
  · rintro ⟨z, rfl⟩
    -- Rebuild the constant one-coordinate integer vector from the scalar witness.
    refine (mem_integerVectors_iff).mpr ?_
    refine ⟨fun _ ↦ z, ?_⟩
    funext j
    fin_cases j
    rfl

/-- On source coordinates `(y, x)`, the ordered-cover objective is
`h * y + ∑ i, c i * x i`. -/
theorem objectiveValue_point_def
    (h : ℝ) (b c : Fin n → ℝ)
    (y : ℝ) (x : Fin n → ℝ) :
    objectiveValue h b c (point y x) = h * y + ∑ i : Fin n, c i * x i := by
  -- Rewrite the owner objective in source coordinates and simplify the unique integer block.
  rw [objectiveValue, (program h b c).objectiveValue_def]
  simp [program, point, dotProduct, MixedIntegerLinearProgram.ofCoefficients]

/-- Membership of `point y x` in the LP relaxation is exactly the source system
`y ≥ 0`, `x ≥ 0`, and `b i ≤ y + x i` for all `i`. -/
theorem point_mem_lpFeasibleSet_iff
    (h : ℝ) (b c : Fin n → ℝ)
    (y : ℝ) (x : Fin n → ℝ) :
    point y x ∈ lpFeasibleSet h b c ↔
      0 ≤ y ∧ 0 ≤ x ∧ ∀ i : Fin n, b i ≤ y + x i := by
  constructor
  · intro hpoint
    -- Convert LP feasibility to the owner inequality system and read off the source variables.
    rcases
      ((program h b c).mem_lpRelaxation_iff (point y x)).mp
        (by simpa [lpFeasibleSet] using hpoint) with
      ⟨hineq, hy_nonneg, hx_nonneg⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [point] using hy_nonneg 0
    · simpa [point] using hx_nonneg
    · intro i
      -- Each owner row inequality is exactly `b i ≤ y + x i` after normalization.
      have hi : -y - x i ≤ -b i := by
        simpa [program, point, Matrix.mulVec, dotProduct,
          MixedIntegerLinearProgram.ofCoefficients] using hineq i
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using neg_le_neg hi
  · rintro ⟨hy_nonneg, hx_nonneg, hcover⟩
    -- Reassemble the owner LP conditions from the source inequalities and nonnegativity data.
    refine ((program h b c).mem_lpRelaxation_iff (point y x)).mpr ?_
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi : -y - x i ≤ -b i := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using neg_le_neg (hcover i)
      simpa [program, point, Matrix.mulVec, dotProduct,
        MixedIntegerLinearProgram.ofCoefficients] using hi
    · intro j
      fin_cases j
      simpa [point] using hy_nonneg
    · simpa [point] using hx_nonneg

/-- Membership of `point y x` in the ILP variant is exactly the source system
`y ∈ ℤ≥0`, `x ∈ ℤ≥0`, and `b i ≤ y + x i` for all `i`. -/
theorem point_mem_ilpFeasibleSet_iff
    (h : ℝ) (b c : Fin n → ℝ)
    (y : ℝ) (x : Fin n → ℝ) :
    point y x ∈ ilpFeasibleSet h b c ↔
      0 ≤ y ∧ 0 ≤ x ∧ (∃ z : ℤ, y = (z : ℝ)) ∧ x ∈ ℤ^n ∧
        ∀ i : Fin n, b i ≤ y + x i := by
  constructor
  · intro hpoint
    -- Unpack ILP feasibility into LP feasibility together with the two integrality blocks.
    rw [ilpFeasibleSet, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_setOf_eq] at hpoint
    rcases hpoint with ⟨hleft, hx_int⟩
    rcases hleft with ⟨hlp, hy_int⟩
    rcases (point_mem_lpFeasibleSet_iff h b c y x).mp hlp with ⟨hy_nonneg, hx_nonneg, hcover⟩
    rw [point_fst] at hy_int
    refine ⟨hy_nonneg, hx_nonneg, ?_, ?_, hcover⟩
    · exact (constantOne_mem_integerVectors_iff y).mp hy_int
    · simpa [point_snd] using hx_int
  · rintro ⟨hy_nonneg, hx_nonneg, hy_int, hx_int, hcover⟩
    -- Rebuild the three ILP conjuncts from the source data.
    rw [ilpFeasibleSet, Set.mem_inter_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact (point_mem_lpFeasibleSet_iff h b c y x).mpr ⟨hy_nonneg, hx_nonneg, hcover⟩
      · rw [point_fst]
        exact (constantOne_mem_integerVectors_iff y).mpr hy_int
    · simpa [point_snd] using hx_int

/-- Membership of `point y x` in the MILP variant is exactly the source system
`y ∈ ℤ≥0`, `x ∈ ℝ≥0`, and `b i ≤ y + x i` for all `i`. -/
theorem point_mem_milpFeasibleSet_iff
    (h : ℝ) (b c : Fin n → ℝ)
    (y : ℝ) (x : Fin n → ℝ) :
    point y x ∈ milpFeasibleSet h b c ↔
      0 ≤ y ∧ 0 ≤ x ∧ (∃ z : ℤ, y = (z : ℝ)) ∧
        ∀ i : Fin n, b i ≤ y + x i := by
  constructor
  · intro hpoint
    -- Read the owner MILP conditions in source coordinates.
    rcases
      ((program h b c).mem_feasibleSet_iff (point y x)).mp
        (by simpa [milpFeasibleSet] using hpoint) with
      ⟨hineq, hy_nonneg, hx_nonneg, hy_int⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [point] using hy_nonneg 0
    · simpa [point] using hx_nonneg
    · simpa [point] using hy_int 0
    · intro i
      -- The matrix row simplifies to the source covering inequality.
      have hi : -y - x i ≤ -b i := by
        simpa [program, point, Matrix.mulVec, dotProduct,
          MixedIntegerLinearProgram.ofCoefficients] using hineq i
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using neg_le_neg hi
  · rintro ⟨hy_nonneg, hx_nonneg, hy_int, hcover⟩
    -- Assemble the owner MILP conditions from the source tuple data.
    refine ((program h b c).mem_feasibleSet_iff (point y x)).mpr ?_
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      have hi : -y - x i ≤ -b i := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using neg_le_neg (hcover i)
      simpa [program, point, Matrix.mulVec, dotProduct,
        MixedIntegerLinearProgram.ofCoefficients] using hi
    · intro j
      fin_cases j
      simpa [point] using hy_nonneg
    · simpa [point] using hx_nonneg
    · intro j
      fin_cases j
      simpa [point] using hy_int

/-- The LP-relaxation objective values attained by the ordered-cover program. -/
abbrev lpObjectiveValues
    (h : ℝ) (b c : Fin n → ℝ) :
    Set ℝ :=
  (program h b c).lpRelaxationObjectiveValues

/-- The ILP objective values attained by the ordered-cover program. -/
def ilpObjectiveValues
    (h : ℝ) (b c : Fin n → ℝ) :
    Set ℝ :=
  objectiveValue h b c '' ilpFeasibleSet h b c

/-- The MILP objective values attained by the ordered-cover program. -/
abbrev milpObjectiveValues
    (h : ℝ) (b c : Fin n → ℝ) :
    Set ℝ :=
  (program h b c).objectiveValues

/-- A real number belongs to `lpObjectiveValues h b c` exactly when it is attained by the source
objective at some LP-feasible point `(y, x)`. -/
theorem mem_lpObjectiveValues_iff
    (h : ℝ) (b c : Fin n → ℝ)
    (r : ℝ) :
    r ∈ lpObjectiveValues h b c ↔
      ∃ y : ℝ, ∃ x : Fin n → ℝ,
        point y x ∈ lpFeasibleSet h b c ∧ objectiveValue h b c (point y x) = r := by
  constructor
  · intro hr
    -- Convert an owner witness into source coordinates using the unique first-block entry.
    rcases
      ((program h b c).mem_lpRelaxationObjectiveValues_iff r).mp
        (by simpa [lpObjectiveValues] using hr) with
      ⟨xy, hxy, hobj⟩
    refine ⟨xy.1 0, xy.2, ?_, ?_⟩
    · simpa [lpFeasibleSet, point_eta] using hxy
    · simpa [objectiveValue, point_eta] using hobj
  · rintro ⟨y, x, hxy, hobj⟩
    -- Use the source witness `point y x` directly in the owner LP-objective image.
    have hr' : r ∈ (program h b c).lpRelaxationObjectiveValues := by
      refine ((program h b c).mem_lpRelaxationObjectiveValues_iff r).mpr ?_
      refine ⟨point y x, ?_, ?_⟩
      · simpa [lpFeasibleSet] using hxy
      · simpa [objectiveValue] using hobj
    simpa [lpObjectiveValues] using hr'

/-- A real number belongs to `ilpObjectiveValues h b c` exactly when it is attained by the source
objective at some ILP-feasible point `(y, x)`. -/
theorem mem_ilpObjectiveValues_iff
    (h : ℝ) (b c : Fin n → ℝ)
    (r : ℝ) :
    r ∈ ilpObjectiveValues h b c ↔
      ∃ y : ℝ, ∃ x : Fin n → ℝ,
        point y x ∈ ilpFeasibleSet h b c ∧ objectiveValue h b c (point y x) = r := by
  rw [ilpObjectiveValues, Set.mem_image]
  constructor
  · rintro ⟨xy, hxy, hobj⟩
    -- Repackage the image witness in source coordinates.
    refine ⟨xy.1 0, xy.2, ?_, ?_⟩
    · simpa [point_eta] using hxy
    · simpa [point_eta] using hobj
  · rintro ⟨y, x, hxy, hobj⟩
    -- The source point is already a valid image witness.
    exact ⟨point y x, hxy, hobj⟩

/-- A real number belongs to `milpObjectiveValues h b c` exactly when it is attained by the
source objective at some MILP-feasible point `(y, x)`. -/
theorem mem_milpObjectiveValues_iff
    (h : ℝ) (b c : Fin n → ℝ)
    (r : ℝ) :
    r ∈ milpObjectiveValues h b c ↔
      ∃ y : ℝ, ∃ x : Fin n → ℝ,
        point y x ∈ milpFeasibleSet h b c ∧ objectiveValue h b c (point y x) = r := by
  constructor
  · intro hr
    -- Convert the owner feasible witness to source coordinates via the unique first coordinate.
    rcases
      ((program h b c).mem_objectiveValues_iff r).mp
        (by simpa [milpObjectiveValues] using hr) with
      ⟨xy, hxy, hobj⟩
    refine ⟨xy.1 0, xy.2, ?_, ?_⟩
    · simpa [milpFeasibleSet, point_eta] using hxy
    · simpa [objectiveValue, point_eta] using hobj
  · rintro ⟨y, x, hxy, hobj⟩
    -- Feed the source witness back into the owner attained-value set.
    have hr' : r ∈ (program h b c).objectiveValues := by
      refine ((program h b c).mem_objectiveValues_iff r).mpr ?_
      refine ⟨point y x, ?_, ?_⟩
      · simpa [milpFeasibleSet] using hxy
      · simpa [objectiveValue] using hobj
    simpa [milpObjectiveValues] using hr'

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_6/ch1_sec1_6_definition_1_44.lean

Definition 1.44. The ordered-cover mixed-integer program is represented by `program h b c`; on
source coordinates `(y, x)`, its objective is `h * y + ∑ i, c i * x i`, and the LP, ILP, and
MILP feasible sets recover exactly the displayed source constraints and integrality conditions. -/
theorem orderedCoverProgramSummary
    (h : ℝ) (b c : Fin n → ℝ)
    (y : ℝ) (x : Fin n → ℝ) :
    program h b c =
        MixedIntegerLinearProgram.ofCoefficients
          (fun _ _ ↦ (-1 : ℝ))
          (fun i j ↦ if j = i then (-1 : ℝ) else 0)
          (fun i ↦ -b i)
          (fun _ ↦ h)
          c ∧
      objectiveValue h b c (point y x) = h * y + ∑ i : Fin n, c i * x i ∧
      (point y x ∈ lpFeasibleSet h b c ↔
        0 ≤ y ∧ 0 ≤ x ∧ ∀ i : Fin n, b i ≤ y + x i) ∧
      (point y x ∈ ilpFeasibleSet h b c ↔
        0 ≤ y ∧ 0 ≤ x ∧ (∃ z : ℤ, y = (z : ℝ)) ∧ x ∈ ℤ^n ∧
          ∀ i : Fin n, b i ≤ y + x i) ∧
      (point y x ∈ milpFeasibleSet h b c ↔
        0 ≤ y ∧ 0 ≤ x ∧ (∃ z : ℤ, y = (z : ℝ)) ∧
          ∀ i : Fin n, b i ≤ y + x i) := by
  -- Package the owner definition and the three source-coordinate characterizations into one item.
  refine ⟨program_def h b c, objectiveValue_point_def h b c y x, ?_, ?_, ?_⟩
  · exact point_mem_lpFeasibleSet_iff h b c y x
  · exact point_mem_ilpFeasibleSet_iff h b c y x
  · exact point_mem_milpFeasibleSet_iff h b c y x

end OrderedCover

end Definition144

end

#eval IO.println "M2F_PROOF_AXIOM_AUDIT_BEGIN_289d83cb163c254710c4"
#print axioms _root_.OrderedCover.orderedCoverProgramSummary
#eval IO.println "M2F_PROOF_AXIOM_AUDIT_END_289d83cb163c254710c4"
