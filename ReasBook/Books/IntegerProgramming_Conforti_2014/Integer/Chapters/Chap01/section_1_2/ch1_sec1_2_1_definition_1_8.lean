module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_2.ch1_sec1_2_1_definition_1_8.Children

public section

open MilpBranchAndBound

section Definition18

variable {n m : ℕ}

/-- Definition 1.8 (1). The left child feasible set `S₁` of the mixed-integer feasible region
`S ⊆ ℤ^n × ℝ^m` at coordinate `j` and source branching value `f = x_j^0` is
`S ∩ {(x, y) | x_j ≤ ⌊f⌋}`. -/
abbrev leftBranchFeasibleSet
    (S : Set (MixedRealPoint n m))
    (j : Fin n)
    (f : ℝ) : Set (MixedRealPoint n m) :=
  leftChild S j f

/-- Membership in `leftBranchFeasibleSet S j f` means feasibility in `S` together with the left
branch inequality on coordinate `j`. -/
theorem mem_leftBranchFeasibleSet_iff
    {S : Set (MixedRealPoint n m)}
    {j : Fin n}
    {f : ℝ}
    {xy : MixedRealPoint n m} :
    xy ∈ leftBranchFeasibleSet S j f ↔ xy ∈ S ∧ xy.1 j ≤ Int.floor f :=
  mem_leftChild_iff

/-- Definition 1.8 (2). The right child feasible set `S₂` of the mixed-integer feasible region
`S ⊆ ℤ^n × ℝ^m` at coordinate `j` and source branching value `f = x_j^0` is
`S ∩ {(x, y) | ⌈f⌉ ≤ x_j}`. -/
abbrev rightBranchFeasibleSet
    (S : Set (MixedRealPoint n m))
    (j : Fin n)
    (f : ℝ) : Set (MixedRealPoint n m) :=
  rightChild S j f

/-- Membership in `rightBranchFeasibleSet S j f` means feasibility in `S` together with the right
branch inequality on coordinate `j`. -/
theorem mem_rightBranchFeasibleSet_iff
    {S : Set (MixedRealPoint n m)}
    {j : Fin n}
    {f : ℝ}
    {xy : MixedRealPoint n m} :
    xy ∈ rightBranchFeasibleSet S j f ↔ xy ∈ S ∧ (Int.ceil f : ℝ) ≤ xy.1 j :=
  mem_rightChild_iff

/-- Definition 1.8 (3). The left child mixed-integer subproblem `MILP₁` keeps the objective
`(x, y) ↦ c x + h y` and records the objective values attained on `S₁` for the source branching
value `f = x_j^0`. -/
abbrev leftMilpBranchObjectiveValues
    (S : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (j : Fin n)
    (f : ℝ) : Set ℝ :=
  leftChildObjectiveValues S c h j f

/-- `leftMilpBranchObjectiveValues S c h j f` unfolds to the image of
`mixed_linear_objective c h` on `leftBranchFeasibleSet S j f`. -/
theorem leftMilpBranchObjectiveValues_def
    (S : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (j : Fin n)
    (f : ℝ) :
    leftMilpBranchObjectiveValues S c h j f =
      mixed_linear_objective c h '' leftBranchFeasibleSet S j f := by
  rfl

/-- Membership in `leftMilpBranchObjectiveValues S c h j f` is equivalent to the existence of a
feasible point of `S₁` whose objective value is the chosen real number. -/
theorem mem_leftMilpBranchObjectiveValues_iff
    {S : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {j : Fin n}
    {f : ℝ}
    {z : ℝ} :
    z ∈ leftMilpBranchObjectiveValues S c h j f ↔
      ∃ xy, xy ∈ S ∧ xy.1 j ≤ Int.floor f ∧ mixed_linear_objective c h xy = z :=
  mem_leftChildObjectiveValues_iff

/-- Definition 1.8 (4). The right child mixed-integer subproblem `MILP₂` keeps the objective
`(x, y) ↦ c x + h y` and records the objective values attained on `S₂` for the source branching
value `f = x_j^0`. -/
abbrev rightMilpBranchObjectiveValues
    (S : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (j : Fin n)
    (f : ℝ) : Set ℝ :=
  rightChildObjectiveValues S c h j f

/-- `rightMilpBranchObjectiveValues S c h j f` unfolds to the image of
`mixed_linear_objective c h` on `rightBranchFeasibleSet S j f`. -/
theorem rightMilpBranchObjectiveValues_def
    (S : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (j : Fin n)
    (f : ℝ) :
    rightMilpBranchObjectiveValues S c h j f =
      mixed_linear_objective c h '' rightBranchFeasibleSet S j f := by
  rfl

/-- Membership in `rightMilpBranchObjectiveValues S c h j f` is equivalent to the existence of a
feasible point of `S₂` whose objective value is the chosen real number. -/
theorem mem_rightMilpBranchObjectiveValues_iff
    {S : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {j : Fin n}
    {f : ℝ}
    {z : ℝ} :
    z ∈ rightMilpBranchObjectiveValues S c h j f ↔
      ∃ xy, xy ∈ S ∧ (Int.ceil f : ℝ) ≤ xy.1 j ∧ mixed_linear_objective c h xy = z := by
  simpa using
    (mem_rightChildObjectiveValues_iff :
      z ∈ rightChildObjectiveValues S c h j f ↔
        ∃ xy, xy ∈ S ∧ Int.ceil f ≤ xy.1 j ∧ mixed_linear_objective c h xy = z)

/-- Definition 1.8 (5). The left child relaxation `P₁` of the natural linear relaxation
`P₀ ⊇ S` at coordinate `j` and source branching value `f = x_j^0` is
`P₀ ∩ {(x, y) | x_j ≤ ⌊f⌋}`. -/
abbrev leftBranchRelaxation
    (P0 : Set (MixedRealPoint n m))
    (j : Fin n)
    (f : ℝ) : Set (MixedRealPoint n m) :=
  leftChild P0 j f

/-- Membership in `leftBranchRelaxation P0 j f` means membership in `P0` together with the left
branch inequality on coordinate `j`. -/
theorem mem_leftBranchRelaxation_iff
    {P0 : Set (MixedRealPoint n m)}
    {j : Fin n}
    {f : ℝ}
    {xy : MixedRealPoint n m} :
    xy ∈ leftBranchRelaxation P0 j f ↔ xy ∈ P0 ∧ xy.1 j ≤ Int.floor f :=
  mem_leftChild_iff

/-- Definition 1.8 (6). The right child relaxation `P₂` of the natural linear relaxation
`P₀ ⊇ S` at coordinate `j` and source branching value `f = x_j^0` is
`P₀ ∩ {(x, y) | ⌈f⌉ ≤ x_j}`. -/
abbrev rightBranchRelaxation
    (P0 : Set (MixedRealPoint n m))
    (j : Fin n)
    (f : ℝ) : Set (MixedRealPoint n m) :=
  rightChild P0 j f

/-- Membership in `rightBranchRelaxation P0 j f` means membership in `P0` together with the
right branch inequality on coordinate `j`. -/
theorem mem_rightBranchRelaxation_iff
    {P0 : Set (MixedRealPoint n m)}
    {j : Fin n}
    {f : ℝ}
    {xy : MixedRealPoint n m} :
    xy ∈ rightBranchRelaxation P0 j f ↔ xy ∈ P0 ∧ (Int.ceil f : ℝ) ≤ xy.1 j :=
  mem_rightChild_iff

/-- Definition 1.8 (7). The left child linear-relaxation subproblem `LP₁` keeps the objective
`(x, y) ↦ c x + h y` and records the objective values attained on `P₁` for the source branching
value `f = x_j^0`. -/
abbrev leftLpBranchObjectiveValues
    (P0 : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (j : Fin n)
    (f : ℝ) : Set ℝ :=
  leftChildObjectiveValues P0 c h j f

/-- `leftLpBranchObjectiveValues P0 c h j f` unfolds to the image of
`mixed_linear_objective c h` on `leftBranchRelaxation P0 j f`. -/
theorem leftLpBranchObjectiveValues_def
    (P0 : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (j : Fin n)
    (f : ℝ) :
    leftLpBranchObjectiveValues P0 c h j f =
      mixed_linear_objective c h '' leftBranchRelaxation P0 j f := by
  rfl

/-- Membership in `leftLpBranchObjectiveValues P0 c h j f` is equivalent to the existence of a
point of `P₁` whose objective value is the chosen real number. -/
theorem mem_leftLpBranchObjectiveValues_iff
    {P0 : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {j : Fin n}
    {f : ℝ}
    {z : ℝ} :
    z ∈ leftLpBranchObjectiveValues P0 c h j f ↔
      ∃ xy, xy ∈ P0 ∧ xy.1 j ≤ Int.floor f ∧ mixed_linear_objective c h xy = z :=
  mem_leftChildObjectiveValues_iff

/-- Definition 1.8 (8). The right child linear-relaxation subproblem `LP₂` keeps the objective
`(x, y) ↦ c x + h y` and records the objective values attained on `P₂` for the source branching
value `f = x_j^0`. -/
abbrev rightLpBranchObjectiveValues
    (P0 : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (j : Fin n)
    (f : ℝ) : Set ℝ :=
  rightChildObjectiveValues P0 c h j f

/-- `rightLpBranchObjectiveValues P0 c h j f` unfolds to the image of
`mixed_linear_objective c h` on `rightBranchRelaxation P0 j f`. -/
theorem rightLpBranchObjectiveValues_def
    (P0 : Set (MixedRealPoint n m))
    (c : Fin n → ℝ)
    (h : Fin m → ℝ)
    (j : Fin n)
    (f : ℝ) :
    rightLpBranchObjectiveValues P0 c h j f =
      mixed_linear_objective c h '' rightBranchRelaxation P0 j f := by
  rfl

/-- Membership in `rightLpBranchObjectiveValues P0 c h j f` is equivalent to the existence of a
point of `P₂` whose objective value is the chosen real number. -/
theorem mem_rightLpBranchObjectiveValues_iff
    {P0 : Set (MixedRealPoint n m)}
    {c : Fin n → ℝ}
    {h : Fin m → ℝ}
    {j : Fin n}
    {f : ℝ}
    {z : ℝ} :
    z ∈ rightLpBranchObjectiveValues P0 c h j f ↔
      ∃ xy, xy ∈ P0 ∧ (Int.ceil f : ℝ) ≤ xy.1 j ∧ mixed_linear_objective c h xy = z := by
  simpa using
    (mem_rightChildObjectiveValues_iff :
      z ∈ rightChildObjectiveValues P0 c h j f ↔
        ∃ xy, xy ∈ P0 ∧ Int.ceil f ≤ xy.1 j ∧ mixed_linear_objective c h xy = z)

end Definition18
