/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Topology.Sets.Opens

public section

noncomputable section

section

variable {d : ℕ}
variable (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))

/-- Example 2.5 (2). The source negative-Laplacian formula `(2.10)` is the
pointwise operator on `Ω` given by
`x ↦ -InnerProductSpace.laplacianWithin f Ω x`.
The source applies this operator to smooth functions `f`. -/
@[expose]
def smoothNegativeLaplacianWithin
    (f : EuclideanSpace ℝ (Fin d) → ℝ) : Ω → ℝ :=
  fun x ↦ -InnerProductSpace.laplacianWithin f Ω x

/-- Evaluation formula for `smoothNegativeLaplacianWithin`. -/
theorem smoothNegativeLaplacianWithin_apply
    (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x : Ω) :
    smoothNegativeLaplacianWithin Ω f x =
      -InnerProductSpace.laplacianWithin f Ω x := rfl

end
