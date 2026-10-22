/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

noncomputable section

universe u

namespace ERealFunction

section Primal

variable {H : Type u}

/-- The primal objective of Fenchel duality is the canonical pointwise sum `f + g`, viewed in
`EReal`. -/
def primalObjective (f g : H → Set.Ioi (⊥ : EReal)) : H → EReal :=
  (f + g).asEReal

/-- Evaluating the primal objective gives the value `f(x) + g(x)`. -/
@[simp] theorem primalObjective_apply (f g : H → Set.Ioi (⊥ : EReal)) (x : H) :
    primalObjective f g x = (f x : EReal) + (g x : EReal) :=
  rfl

/-- The canonical primal objective is the raw `EReal` pointwise sum of the two coercions. -/
@[simp] theorem primalObjective_eq_add_asEReal (f g : H → Set.Ioi (⊥ : EReal)) :
    primalObjective f g = f.asEReal + g.asEReal := by
  funext x
  simp [primalObjective]

/-- The primal optimal value `μ`, defined as the infimum of the range of the primal objective. -/
def primalOptimalValue (f g : H → Set.Ioi (⊥ : EReal)) : EReal :=
  sInf (Set.range (primalObjective f g))

/-- The primal optimal value is the infimum of the range of the canonical primal objective
`primalObjective f g`. -/
theorem primalOptimalValue_def (f g : H → Set.Ioi (⊥ : EReal)) :
    primalOptimalValue f g = sInf (Set.range (primalObjective f g)) :=
  rfl

/-- Rewriting the primal objective through the underlying `EReal` coercions recovers the raw
pointwise sum formula. -/
theorem primalOptimalValue_eq_sInf_range_add_asEReal (f g : H → Set.Ioi (⊥ : EReal)) :
    primalOptimalValue f g = sInf (Set.range (f.asEReal + g.asEReal)) := by
  rw [primalOptimalValue_def, primalObjective_eq_add_asEReal]

/-- The primal optimal value is the indexed infimum of the canonical primal objective. -/
theorem primalOptimalValue_eq_iInf_primalObjective (f g : H → Set.Ioi (⊥ : EReal)) :
    primalOptimalValue f g = ⨅ x : H, primalObjective f g x :=
  rfl

end Primal

section FenchelDuality

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The dual objective of Fenchel duality is the canonical pointwise sum
`u ↦ f^*(-u) + g^*(u)`. -/
def fenchelDualObjective (f g : H → Set.Ioi (⊥ : EReal)) : H → EReal :=
  f.asEReal∗ᵛ + g.asEReal∗

/-- Evaluating the dual objective gives the value `f^*(-u) + g^*(u)`. -/
@[simp] theorem fenchelDualObjective_apply (f g : H → Set.Ioi (⊥ : EReal)) (u : H) :
    fenchelDualObjective f g u = f.asEReal∗ (-u) + g.asEReal∗ u :=
  rfl

/-- The canonical dual objective is the raw pointwise sum of the reflected conjugate of `f` and
the conjugate of `g`. -/
@[simp] theorem fenchelDualObjective_eq_add_conjugates (f g : H → Set.Ioi (⊥ : EReal)) :
    fenchelDualObjective f g = f.asEReal∗ᵛ + g.asEReal∗ :=
  rfl

/-- The dual optimal value `μ*`, defined as the infimum of the range of the dual objective. -/
def dualOptimalValue (f g : H → Set.Ioi (⊥ : EReal)) : EReal :=
  sInf (Set.range (fenchelDualObjective f g))

/-- The dual optimal value is the infimum of the range of the canonical dual objective
`fenchelDualObjective f g`. -/
theorem dualOptimalValue_def (f g : H → Set.Ioi (⊥ : EReal)) :
    dualOptimalValue f g = sInf (Set.range (fenchelDualObjective f g)) :=
  rfl

/-- The dual optimal value is the indexed infimum of the canonical dual objective. -/
theorem dualOptimalValue_eq_iInf_fenchelDualObjective (f g : H → Set.Ioi (⊥ : EReal)) :
    dualOptimalValue f g = ⨅ u : H, fenchelDualObjective f g u :=
  rfl

/-- Definition 15.10: the duality gap attached to the primal objective `x ↦ f(x) + g(x)` and the
dual objective `u ↦ f^*(-u) + g^*(u)` is `0` in the exceptional case `μ = -μ* ∈ {±∞}`, and
otherwise it is the sum `μ + μ*` of the primal and dual optimal values. -/
def dualityGap (f g : H → Set.Ioi (⊥ : EReal)) : EReal :=
  if primalOptimalValue f g = -dualOptimalValue f g ∧
      (primalOptimalValue f g = (⊥ : EReal) ∨ primalOptimalValue f g = ⊤) then
    0
  else
    primalOptimalValue f g + dualOptimalValue f g

/-- The duality gap is given by the case split in Definition 15.10. -/
theorem dualityGap_def (f g : H → Set.Ioi (⊥ : EReal)) :
    dualityGap f g =
      if primalOptimalValue f g = -dualOptimalValue f g ∧
          (primalOptimalValue f g = (⊥ : EReal) ∨ primalOptimalValue f g = ⊤) then
        0
      else primalOptimalValue f g + dualOptimalValue f g :=
  rfl

end FenchelDuality

end ERealFunction
