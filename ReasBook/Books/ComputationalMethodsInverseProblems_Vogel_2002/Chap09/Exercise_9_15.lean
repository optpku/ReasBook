/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_5_1.Iteration

public section

noncomputable section

namespace Exercise915

/-- Exercise 9.15. The Richardson-Lucy iterate family specialized to the
one-dimensional `§9.4.1` benchmark, with the concrete benchmark forward
operator, datum, and initial iterate kept explicit. -/
abbrev iterates
    (n : ℕ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 initialIterate941 : Fin n → ℝ) :
    ℕ → Fin n → ℝ :=
  RichardsonLucy.iterates forwardOperator941 data941 initialIterate941

/-- `Exercise915.iterates` is definitionally the `§9.4.1` benchmark
specialization of the canonical Richardson-Lucy iterate family. -/
theorem iterates_def
    (n : ℕ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 initialIterate941 : Fin n → ℝ) :
    iterates n forwardOperator941 data941 initialIterate941 =
      RichardsonLucy.iterates forwardOperator941 data941 initialIterate941 :=
  rfl

/-- `Exercise915.iterates` agrees with repeated application of the one-step
Richardson-Lucy update to the explicit `§9.4.1` initial iterate. -/
theorem iterates_eq_nat_iterate
    (n : ℕ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 initialIterate941 : Fin n → ℝ) :
    iterates n forwardOperator941 data941 initialIterate941 =
      fun v ↦
        Nat.iterate (RichardsonLucy.update forwardOperator941 data941) v
          initialIterate941 := by
  rw [iterates_def, RichardsonLucy.iterates_eq_nat_iterate]

end Exercise915

/- Source-facing check for the Exercise 9.15 one-dimensional Richardson-Lucy
iterate specialization.

Apply the R-L iteration to the one-dimensional test problem of section 9.4.1.

The concrete `§9.4.1` forward operator, datum, and initial iterate remain
explicit parameters, while the reusable backend owners are
`RichardsonLucy.iterates` and `RichardsonLucy.update`. -/
#check Exercise915.iterates

/- Backend anchors for the source-facing Richardson-Lucy iterate bridge. -/
#check RichardsonLucy.iterates
#check RichardsonLucy.update
#check Nat.iterate
