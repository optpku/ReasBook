/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.Descent.Lookups
public meta import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalCertificates.CaseThree.Upper.Descent.Lookups

@[expose] public section

set_option maxRecDepth 4096
set_option maxHeartbeats 6400000
set_option linter.unusedSimpArgs false

namespace ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.Descent

/-- Local pivot recurrence at scalar coordinate 0. -/
theorem pivot0 :
    candidateD (0, 0) = candidateK (0, 0) (0, 0) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((0, 0) : Fin 9 × Fin 2) then
        candidateL (0, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 0. -/
theorem lower0 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((0, 0) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (0, 0) =
      (candidateK j (0, 0) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((0, 0) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (0, 0) r * candidateD r else 0) / candidateD (0, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot0
#print axioms lower0

/-- Local pivot recurrence at scalar coordinate 1. -/
theorem pivot1 :
    candidateD (0, 1) = candidateK (0, 1) (0, 1) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((0, 1) : Fin 9 × Fin 2) then
        candidateL (0, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 1. -/
theorem lower1 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((0, 1) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (0, 1) =
      (candidateK j (0, 1) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((0, 1) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (0, 1) r * candidateD r else 0) / candidateD (0, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot1
#print axioms lower1

/-- Local pivot recurrence at scalar coordinate 2. -/
theorem pivot2 :
    candidateD (1, 0) = candidateK (1, 0) (1, 0) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((1, 0) : Fin 9 × Fin 2) then
        candidateL (1, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 2. -/
theorem lower2 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((1, 0) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (1, 0) =
      (candidateK j (1, 0) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((1, 0) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (1, 0) r * candidateD r else 0) / candidateD (1, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot2
#print axioms lower2

/-- Local pivot recurrence at scalar coordinate 3. -/
theorem pivot3 :
    candidateD (1, 1) = candidateK (1, 1) (1, 1) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((1, 1) : Fin 9 × Fin 2) then
        candidateL (1, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 3. -/
theorem lower3 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((1, 1) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (1, 1) =
      (candidateK j (1, 1) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((1, 1) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (1, 1) r * candidateD r else 0) / candidateD (1, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot3
#print axioms lower3

/-- Local pivot recurrence at scalar coordinate 4. -/
theorem pivot4 :
    candidateD (2, 0) = candidateK (2, 0) (2, 0) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((2, 0) : Fin 9 × Fin 2) then
        candidateL (2, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 4. -/
theorem lower4 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((2, 0) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (2, 0) =
      (candidateK j (2, 0) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((2, 0) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (2, 0) r * candidateD r else 0) / candidateD (2, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot4
#print axioms lower4

/-- Local pivot recurrence at scalar coordinate 5. -/
theorem pivot5 :
    candidateD (2, 1) = candidateK (2, 1) (2, 1) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((2, 1) : Fin 9 × Fin 2) then
        candidateL (2, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 5. -/
theorem lower5 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((2, 1) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (2, 1) =
      (candidateK j (2, 1) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((2, 1) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (2, 1) r * candidateD r else 0) / candidateD (2, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot5
#print axioms lower5

/-- Local pivot recurrence at scalar coordinate 6. -/
theorem pivot6 :
    candidateD (3, 0) = candidateK (3, 0) (3, 0) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((3, 0) : Fin 9 × Fin 2) then
        candidateL (3, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 6. -/
theorem lower6 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((3, 0) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (3, 0) =
      (candidateK j (3, 0) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((3, 0) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (3, 0) r * candidateD r else 0) / candidateD (3, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot6
#print axioms lower6

/-- Local pivot recurrence at scalar coordinate 7. -/
theorem pivot7 :
    candidateD (3, 1) = candidateK (3, 1) (3, 1) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((3, 1) : Fin 9 × Fin 2) then
        candidateL (3, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 7. -/
theorem lower7 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((3, 1) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (3, 1) =
      (candidateK j (3, 1) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((3, 1) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (3, 1) r * candidateD r else 0) / candidateD (3, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot7
#print axioms lower7

/-- Local pivot recurrence at scalar coordinate 8. -/
theorem pivot8 :
    candidateD (4, 0) = candidateK (4, 0) (4, 0) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((4, 0) : Fin 9 × Fin 2) then
        candidateL (4, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 8. -/
theorem lower8 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((4, 0) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (4, 0) =
      (candidateK j (4, 0) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((4, 0) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (4, 0) r * candidateD r else 0) / candidateD (4, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot8
#print axioms lower8

/-- Local pivot recurrence at scalar coordinate 9. -/
theorem pivot9 :
    candidateD (4, 1) = candidateK (4, 1) (4, 1) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((4, 1) : Fin 9 × Fin 2) then
        candidateL (4, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 9. -/
theorem lower9 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((4, 1) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (4, 1) =
      (candidateK j (4, 1) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((4, 1) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (4, 1) r * candidateD r else 0) / candidateD (4, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot9
#print axioms lower9

/-- Local pivot recurrence at scalar coordinate 10. -/
theorem pivot10 :
    candidateD (5, 0) = candidateK (5, 0) (5, 0) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((5, 0) : Fin 9 × Fin 2) then
        candidateL (5, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 10. -/
theorem lower10 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((5, 0) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (5, 0) =
      (candidateK j (5, 0) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((5, 0) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (5, 0) r * candidateD r else 0) / candidateD (5, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot10
#print axioms lower10

/-- Local pivot recurrence at scalar coordinate 11. -/
theorem pivot11 :
    candidateD (5, 1) = candidateK (5, 1) (5, 1) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((5, 1) : Fin 9 × Fin 2) then
        candidateL (5, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 11. -/
theorem lower11 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((5, 1) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (5, 1) =
      (candidateK j (5, 1) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((5, 1) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (5, 1) r * candidateD r else 0) / candidateD (5, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot11
#print axioms lower11

/-- Local pivot recurrence at scalar coordinate 12. -/
theorem pivot12 :
    candidateD (6, 0) = candidateK (6, 0) (6, 0) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((6, 0) : Fin 9 × Fin 2) then
        candidateL (6, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 12. -/
theorem lower12 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((6, 0) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (6, 0) =
      (candidateK j (6, 0) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((6, 0) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (6, 0) r * candidateD r else 0) / candidateD (6, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot12
#print axioms lower12

/-- Local pivot recurrence at scalar coordinate 13. -/
theorem pivot13 :
    candidateD (6, 1) = candidateK (6, 1) (6, 1) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((6, 1) : Fin 9 × Fin 2) then
        candidateL (6, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 13. -/
theorem lower13 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((6, 1) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (6, 1) =
      (candidateK j (6, 1) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((6, 1) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (6, 1) r * candidateD r else 0) / candidateD (6, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot13
#print axioms lower13

/-- Local pivot recurrence at scalar coordinate 14. -/
theorem pivot14 :
    candidateD (7, 0) = candidateK (7, 0) (7, 0) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((7, 0) : Fin 9 × Fin 2) then
        candidateL (7, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 14. -/
theorem lower14 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((7, 0) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (7, 0) =
      (candidateK j (7, 0) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((7, 0) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (7, 0) r * candidateD r else 0) / candidateD (7, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot14
#print axioms lower14

/-- Local pivot recurrence at scalar coordinate 15. -/
theorem pivot15 :
    candidateD (7, 1) = candidateK (7, 1) (7, 1) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((7, 1) : Fin 9 × Fin 2) then
        candidateL (7, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 15. -/
theorem lower15 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((7, 1) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (7, 1) =
      (candidateK j (7, 1) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((7, 1) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (7, 1) r * candidateD r else 0) / candidateD (7, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot15
#print axioms lower15

/-- Local pivot recurrence at scalar coordinate 16. -/
theorem pivot16 :
    candidateD (8, 0) = candidateK (8, 0) (8, 0) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((8, 0) : Fin 9 × Fin 2) then
        candidateL (8, 0) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 16. -/
theorem lower16 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((8, 0) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (8, 0) =
      (candidateK j (8, 0) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((8, 0) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (8, 0) r * candidateD r else 0) / candidateD (8, 0) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot16
#print axioms lower16

/-- Local pivot recurrence at scalar coordinate 17. -/
theorem pivot17 :
    candidateD (8, 1) = candidateK (8, 1) (8, 1) - ∑ r : Fin 9 × Fin 2,
      if coordinateRank r < coordinateRank ((8, 1) : Fin 9 × Fin 2) then
        candidateL (8, 1) r ^ 2 * candidateD r else 0 := by
  norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- Local lower-column recurrence at scalar coordinate 17. -/
theorem lower17 (j : Fin 9 × Fin 2)
    (h : coordinateRank ((8, 1) : Fin 9 × Fin 2) < coordinateRank j) :
    candidateL j (8, 1) =
      (candidateK j (8, 1) - ∑ r : Fin 9 × Fin 2,
        if coordinateRank r < coordinateRank ((8, 1) : Fin 9 × Fin 2) then
          candidateL j r * candidateL (8, 1) r * candidateD r else 0) / candidateD (8, 1) := by
  fin_cases j <;>
    first
    | (exfalso; simpa [coordinateRank] using h)
    | norm_num [coordinateRank, Fintype.sum_prod_type, Fin.sum_univ_succ]

#print axioms pivot17
#print axioms lower17

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
    · exact pivot6
    · exact pivot7
    · exact pivot8
    · exact pivot9
    · exact pivot10
    · exact pivot11
    · exact pivot12
    · exact pivot13
    · exact pivot14
    · exact pivot15
    · exact pivot16
    · exact pivot17
  · intro i j h
    fin_cases i
    · exact lower0 j h
    · exact lower1 j h
    · exact lower2 j h
    · exact lower3 j h
    · exact lower4 j h
    · exact lower5 j h
    · exact lower6 j h
    · exact lower7 j h
    · exact lower8 j h
    · exact lower9 j h
    · exact lower10 j h
    · exact lower11 j h
    · exact lower12 j h
    · exact lower13 j h
    · exact lower14 j h
    · exact lower15 j h
    · exact lower16 j h
    · exact lower17 j h
  · intro i
    fin_cases i <;> norm_num [coordinateRank]

#print axioms candidatePositive

end ADMM.FiniteMemory.Reconstruction.RationalCertificates.CaseThree.Upper.Descent
