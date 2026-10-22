/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.EReal.Basic

public section

noncomputable section

namespace VariationalRegularization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 8.4 (2). The conjugate functional of `φ` on `C` is
`y ↦ sSup ((fun x ↦ ((inner ℝ x y - φ x : ℝ) : EReal)) '' C)`. -/
@[expose]
def conjugateFunctional (C : Set E) (φ : E → ℝ) : E → EReal :=
  fun y ↦ sSup ((fun x : E ↦ ((inner ℝ x y - φ x : ℝ) : EReal)) '' C)

/-- The defining supremum formula for `conjugateFunctional`. -/
theorem conjugateFunctional_def (C : Set E) (φ : E → ℝ) (y : E) :
    conjugateFunctional C φ y =
      sSup ((fun x : E ↦ ((inner ℝ x y - φ x : ℝ) : EReal)) '' C) :=
  rfl

/-- On `Set.univ`, `conjugateFunctional` is the supremum over all `x`. -/
theorem conjugateFunctional_univ_eq_sSup_range (φ : E → ℝ) (y : E) :
    conjugateFunctional Set.univ φ y =
      sSup (Set.range fun x : E ↦ ((inner ℝ x y - φ x : ℝ) : EReal)) := by
  simp [conjugateFunctional_def]

/-- Definition 8.4 (1). The conjugate set `conjugateSet C φ` is the set of
`y` where `conjugateFunctional C φ y` is finite. -/
@[expose]
def conjugateSet (C : Set E) (φ : E → ℝ) : Set E :=
  {y | conjugateFunctional C φ y < ⊤}

/-- Membership in `conjugateSet C φ` means finiteness of `conjugateFunctional C φ`. -/
theorem mem_conjugateSet_iff (C : Set E) (φ : E → ℝ) (y : E) :
    y ∈ conjugateSet C φ ↔ conjugateFunctional C φ y < ⊤ :=
  Iff.rfl

end VariationalRegularization
