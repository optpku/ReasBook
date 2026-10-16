module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.Lower.Lookups
public meta import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseOne.Lower.Lower.Lookups

@[expose] public section

set_option maxRecDepth 4096
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.Lower

/-- Local pivot recurrence at scalar coordinate 0. -/
theorem pivot0 :
    candidateD (0, 0) = candidateK (0, 0) (0, 0) - ∑ r : Fin 3 × Fin 2,
      if coordinateRank r < coordinateRank ((0, 0) : Fin 3 × Fin 2) then
        candidateL (0, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 0. -/
theorem lower0 (j : Fin 3 × Fin 2)
    (h : coordinateRank ((0, 0) : Fin 3 × Fin 2) < coordinateRank j) :
    candidateL j (0, 0) =
      (candidateK j (0, 0) - ∑ r : Fin 3 × Fin 2,
        if coordinateRank r < coordinateRank ((0, 0) : Fin 3 × Fin 2) then
          candidateL j r * candidateL (0, 0) r * candidateD r else 0) / candidateD (0, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot0
#print axioms lower0

/-- Local pivot recurrence at scalar coordinate 1. -/
theorem pivot1 :
    candidateD (0, 1) = candidateK (0, 1) (0, 1) - ∑ r : Fin 3 × Fin 2,
      if coordinateRank r < coordinateRank ((0, 1) : Fin 3 × Fin 2) then
        candidateL (0, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 1. -/
theorem lower1 (j : Fin 3 × Fin 2)
    (h : coordinateRank ((0, 1) : Fin 3 × Fin 2) < coordinateRank j) :
    candidateL j (0, 1) =
      (candidateK j (0, 1) - ∑ r : Fin 3 × Fin 2,
        if coordinateRank r < coordinateRank ((0, 1) : Fin 3 × Fin 2) then
          candidateL j r * candidateL (0, 1) r * candidateD r else 0) / candidateD (0, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot1
#print axioms lower1

/-- Local pivot recurrence at scalar coordinate 2. -/
theorem pivot2 :
    candidateD (1, 0) = candidateK (1, 0) (1, 0) - ∑ r : Fin 3 × Fin 2,
      if coordinateRank r < coordinateRank ((1, 0) : Fin 3 × Fin 2) then
        candidateL (1, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 2. -/
theorem lower2 (j : Fin 3 × Fin 2)
    (h : coordinateRank ((1, 0) : Fin 3 × Fin 2) < coordinateRank j) :
    candidateL j (1, 0) =
      (candidateK j (1, 0) - ∑ r : Fin 3 × Fin 2,
        if coordinateRank r < coordinateRank ((1, 0) : Fin 3 × Fin 2) then
          candidateL j r * candidateL (1, 0) r * candidateD r else 0) / candidateD (1, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot2
#print axioms lower2

/-- Local pivot recurrence at scalar coordinate 3. -/
theorem pivot3 :
    candidateD (1, 1) = candidateK (1, 1) (1, 1) - ∑ r : Fin 3 × Fin 2,
      if coordinateRank r < coordinateRank ((1, 1) : Fin 3 × Fin 2) then
        candidateL (1, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 3. -/
theorem lower3 (j : Fin 3 × Fin 2)
    (h : coordinateRank ((1, 1) : Fin 3 × Fin 2) < coordinateRank j) :
    candidateL j (1, 1) =
      (candidateK j (1, 1) - ∑ r : Fin 3 × Fin 2,
        if coordinateRank r < coordinateRank ((1, 1) : Fin 3 × Fin 2) then
          candidateL j r * candidateL (1, 1) r * candidateD r else 0) / candidateD (1, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot3
#print axioms lower3

/-- Local pivot recurrence at scalar coordinate 4. -/
theorem pivot4 :
    candidateD (2, 0) = candidateK (2, 0) (2, 0) - ∑ r : Fin 3 × Fin 2,
      if coordinateRank r < coordinateRank ((2, 0) : Fin 3 × Fin 2) then
        candidateL (2, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 4. -/
theorem lower4 (j : Fin 3 × Fin 2)
    (h : coordinateRank ((2, 0) : Fin 3 × Fin 2) < coordinateRank j) :
    candidateL j (2, 0) =
      (candidateK j (2, 0) - ∑ r : Fin 3 × Fin 2,
        if coordinateRank r < coordinateRank ((2, 0) : Fin 3 × Fin 2) then
          candidateL j r * candidateL (2, 0) r * candidateD r else 0) / candidateD (2, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot4
#print axioms lower4

/-- Local pivot recurrence at scalar coordinate 5. -/
theorem pivot5 :
    candidateD (2, 1) = candidateK (2, 1) (2, 1) - ∑ r : Fin 3 × Fin 2,
      if coordinateRank r < coordinateRank ((2, 1) : Fin 3 × Fin 2) then
        candidateL (2, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 5. -/
theorem lower5 (j : Fin 3 × Fin 2)
    (h : coordinateRank ((2, 1) : Fin 3 × Fin 2) < coordinateRank j) :
    candidateL j (2, 1) =
      (candidateK j (2, 1) - ∑ r : Fin 3 × Fin 2,
        if coordinateRank r < coordinateRank ((2, 1) : Fin 3 × Fin 2) then
          candidateL j r * candidateL (2, 1) r * candidateD r else 0) / candidateD (2, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot5
#print axioms lower5

theorem candidatePositive : PositivePivots (1 / 10000000) candidateK := by
  apply positivePivots_of_recurrences candidateK candidateL candidateD
  · intro i
    fin_cases i
    · exact pivot0
    · exact pivot1
    · exact pivot2
    · exact pivot3
    · exact pivot4
    · exact pivot5
  · intro i j h
    fin_cases i
    · exact lower0 j h
    · exact lower1 j h
    · exact lower2 j h
    · exact lower3 j h
    · exact lower4 j h
    · exact lower5 j h
  · intro i
    fin_cases i <;> norm_num [coordinateRank]

#print axioms candidatePositive

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseOne.Lower.Lower
