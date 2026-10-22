/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/- Definition 7.1 is `source-facing`: it records invariance of a proper extended-real-valued
function under a chosen family of orthogonal symmetries of `ℝ^ι`. The `core/canonical` owner for
those symmetries in mathlib and this project is `Matrix.orthogonalGroup ι ℝ`, and the action on
`ι → ℝ` is the inherited matrix action. Primitive data are therefore just properness together with
invariance under every matrix in the chosen family. -/

/-- Definition 7.1: a proper extended-real-valued function on `ι → ℝ` is symmetric with respect to
a family `𝒜` of orthogonal matrices if it is invariant under the action of every element of `𝒜`. -/
class IsSymmetricFunction (𝒜 : Set (Matrix.orthogonalGroup ι ℝ))
    (f : (ι → ℝ) → EReal) : Prop extends IsProperExtendedRealFunction f where
  map_smul (A : Matrix.orthogonalGroup ι ℝ) (hA : A ∈ 𝒜) (x : ι → ℝ) :
    f (A • x) = f x

/-- The constant zero extended-real-valued function is symmetric with respect to any family of
orthogonal matrices. -/
instance (𝒜 : Set (Matrix.orthogonalGroup ι ℝ)) :
    IsSymmetricFunction 𝒜 (fun _ : ι → ℝ ↦ (0 : EReal)) := by
  refine
    { toIsProperExtendedRealFunction := ?_
      map_smul := ?_ }
  · refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · -- The constant zero function never attains `-∞`, so the first properness field is immediate.
      intro x
      simp
    · -- The zero vector lies in the effective domain because the function value there is finite.
      refine ⟨0, ?_⟩
      simp [effective_domain]
  · -- Symmetry follows because the function is constant, so both sides reduce to the same value.
    intro A hA x
    simp

end
