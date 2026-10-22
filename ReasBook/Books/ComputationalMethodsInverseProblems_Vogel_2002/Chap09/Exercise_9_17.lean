/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_5_1

public section

noncomputable section

open scoped Matrix

/-! Exercise 9.17. Canonical MRNSD equality reuse.

This exercise asks for the verification of the step-size equality `(9.55)` from
the MRNSD setup of `§9.5.2`. In the current Chapter 9 API, that equality is
already owned by the one-step MRNSD relation `Mrnsd.IsStep.stepSize_eq`. This
file keeps the exercise source-facing by exposing the same equality directly
along a valid MRNSD iterate sequence, without introducing a duplicate owner.
-/

namespace Mrnsd.IsIterateSequence

/-- Exercise 9.17. Along a valid MRNSD iterate sequence, the step size `τ v`
is exactly the minimum in `(9.55)`. -/
theorem stepSize_eq {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {K : Matrix m n ℝ} {d : EuclideanSpace ℝ m} {f0 : EuclideanSpace ℝ n}
    {τBoundary τ : ℕ → ℝ} (h : Mrnsd.IsIterateSequence K d f0 τBoundary τ) (v : ℕ) :
    τ v =
      min
        ((Mrnsd.iterates K d f0 τ v).gamma /
          ‖Mrnsd.appliedDirection K (Mrnsd.iterates K d f0 τ v)‖ ^ 2)
        (τBoundary v) :=
  (h.step v).stepSize_eq

end Mrnsd.IsIterateSequence

/- Exercise 9.17.

The source-facing formal anchor for the MRNSD equality `(9.55)` is the
sequence-level companion theorem `Mrnsd.IsIterateSequence.stepSize_eq`, derived
directly from the canonical one-step field `Mrnsd.IsStep.stepSize_eq`.
-/
#check Mrnsd.IsIterateSequence.stepSize_eq

/- Backend companions for the Exercise 9.17 MRNSD equality surface. -/
#check Mrnsd.IsStep.stepSize_eq
#check Mrnsd.IsIterateSequence.step
#check Mrnsd.IsStep
#check Mrnsd.IsIterateSequence
