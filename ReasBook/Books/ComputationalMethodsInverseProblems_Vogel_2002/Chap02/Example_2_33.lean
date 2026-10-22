/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_32
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

/-- Example 2.33. Equation `(2.37)` identifies the `i`-th coordinate of
`gradient J f` on `ℝ^n` with the Fréchet derivative applied to the `i`-th
standard basis vector. This is the standard-basis specialization of
Definition 2.32's gradient-pairing identity `inner_gradient_left`. The source's
continuous-partials clause is contextual here rather than a separate formal
hypothesis for this identity. -/
theorem gradient_apply_eq_fderiv_single {n : ℕ} (J : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    gradient J f i = fderiv ℝ J f (EuclideanSpace.single i (1 : ℝ)) := by
  calc
    gradient J f i = inner ℝ (gradient J f) (EuclideanSpace.single i (1 : ℝ)) := by
      simpa using (EuclideanSpace.inner_single_right i (1 : ℝ) (gradient J f)).symm
    _ = fderiv ℝ J f (EuclideanSpace.single i (1 : ℝ)) := by
      simp
