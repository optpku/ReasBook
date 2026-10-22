/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Deriv.Basic
noncomputable section

section Chapter14OneSidedDirectionalDeriv

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- `HasOneSidedDirectionalDerivAt F v x h` means that the right directional derivative of
`F : X → Y` at `x` in the direction `h` exists and equals `v`. -/
def HasOneSidedDirectionalDerivAt (F : X → Y) (v : Y) (x h : X) : Prop :=
  HasDerivWithinAt (fun t : ℝ ↦ F (x + t • h)) v (Set.Ici 0) 0

/-- The right directional derivative value `F'(x; h)` of `F : X → Y` at `x` in the direction
`h`. -/
def oneSidedDirectionalDeriv (F : X → Y) (x h : X) : Y :=
  derivWithin (fun t : ℝ ↦ F (x + t • h)) (Set.Ici 0) 0

/-- OneSidedDirectionalDeriv: if the right directional derivative of `F` at `x` in the
direction `h` exists with value `v`, then `oneSidedDirectionalDeriv F x h` recovers that
value. -/
theorem HasOneSidedDirectionalDerivAt.oneSidedDirectionalDeriv_eq
    {F : X → Y} {v : Y} {x h : X}
    (hF : HasOneSidedDirectionalDerivAt F v x h) :
    oneSidedDirectionalDeriv F x h = v := by
  -- Unfold the one-sided wrapper definitions to reach the standard `derivWithin` statement.
  simp only [HasOneSidedDirectionalDerivAt, oneSidedDirectionalDeriv] at hF ⊢
  -- Recover the derivative value from the existing `HasDerivWithinAt` witness on `Set.Ici 0`.
  exact hF.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))

end Chapter14OneSidedDirectionalDeriv
