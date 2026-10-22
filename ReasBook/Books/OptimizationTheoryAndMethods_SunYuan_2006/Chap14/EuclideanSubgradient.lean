/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_3_1

noncomputable section

open scoped Subgradient

namespace Chapter14

/-- `Point n` is the ambient Euclidean space `ℝ^n`, represented as
`EuclideanSpace ℝ (Fin n)`. -/
abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- `IsSubgradientAt f x g` means that `g` lies in the convex-analytic subdifferential
`∂ f(x)`. -/
def IsSubgradientAt {n : ℕ} (f : Point n → ℝ) (x g : Point n) : Prop :=
  InnerProductSpace.toDual ℝ (Point n) g ∈ subdifferential f x

/-- Unfolding `IsSubgradientAt f x g` gives membership in `subdifferential f x`. -/
theorem isSubgradientAt_iff_mem_subdifferential
    {n : ℕ} (f : Point n → ℝ) (x g : Point n) :
    IsSubgradientAt f x g ↔
      InnerProductSpace.toDual ℝ (Point n) g ∈ subdifferential f x :=
  Iff.rfl

/-- Unfolding `IsSubgradientAt f x g` gives the affine-support inequality for every `y`. -/
theorem isSubgradientAt_iff
    {n : ℕ} (f : Point n → ℝ) (x g : Point n) :
    IsSubgradientAt f x g ↔
      ∀ y : Point n, f y ≥ f x + inner ℝ g (y - x) := by
  simpa [IsSubgradientAt] using
    (mem_subdifferential_iff f x (InnerProductSpace.toDual ℝ (Point n) g))

end Chapter14
