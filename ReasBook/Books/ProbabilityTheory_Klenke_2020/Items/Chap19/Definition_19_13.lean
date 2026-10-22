/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open scoped BigOperators

universe u

attribute [local instance] Classical.propDecidable

noncomputable section

namespace ProbabilityTheory

variable {E : Type u} [Fintype E]

/-- The net flow emitted from the vertex `x`, namely `∑ y, I x y`. -/
def netFlowAt (I : E → E → ℝ) (x : E) : ℝ :=
  ∑ y : E, I x y

-- Proof sketch: unfold `netFlowAt`; this is exactly the finite sum `∑ y, I x y` from the
-- definition.
/-- Evaluating `netFlowAt I` at `x` gives the sum `∑ y, I x y`. -/
theorem netFlowAt_def (I : E → E → ℝ) (x : E) :
    netFlowAt I x = ∑ y : E, I x y := rfl

/-- The total net flow emitted from the set `A`, namely `∑ x ∈ A, netFlowAt I x`. -/
def netFlowOnSet (I : E → E → ℝ) (A : Set E) : ℝ :=
  ∑ x : A, netFlowAt I x

-- Proof sketch: unfold `netFlowOnSet`; summing over the subtype `A` is the same as summing
-- `netFlowAt I x` over all `x ∈ A`.
/-- Evaluating `netFlowOnSet I A` gives the sum of `netFlowAt I x` over `x ∈ A`. -/
theorem netFlowOnSet_def (I : E → E → ℝ) (A : Set E) :
    netFlowOnSet I A = ∑ x : A, netFlowAt I x := rfl

/-- Definition 19.13: a map `I : E → E → ℝ` is a flow on `E \ A` if it is antisymmetric and its
net flow vanishes at every vertex outside `A`. In the finite setting, these conditions imply that
the total net flow across `A` is zero. Here `netFlowAt I x = ∑ y, I x y` and
`netFlowOnSet I A = ∑ x ∈ A, netFlowAt I x`. -/
class IsFlowOutside (A : Set E) (I : E → E → ℝ) : Prop where
  /-- The flow is antisymmetric on ordered pairs of vertices. -/
  antisymm : ∀ x y : E, I x y = -I y x
  /-- Kirchhoff's rule away from `A`: the net flow at each `x ∉ A` is zero. -/
  netFlowAt_eq_zero : ∀ ⦃x : E⦄, x ∉ A → netFlowAt I x = 0

/-- The total net flow through all vertices vanishes for an antisymmetric flow. -/
theorem sum_netFlowAt_eq_zero {I : E → E → ℝ}
    (hantisymm : ∀ x y : E, I x y = -I y x) :
    ∑ x : E, netFlowAt I x = 0 := by
  have hsum : ∑ x : E, ∑ y : E, I x y = -∑ x : E, ∑ y : E, I x y := by
    calc
      ∑ x : E, ∑ y : E, I x y = ∑ y : E, ∑ x : E, I x y := by
        rw [Finset.sum_comm]
      _ = ∑ y : E, ∑ x : E, -I y x := by
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [hantisymm x y]
      _ = -∑ y : E, ∑ x : E, I y x := by
        simp_rw [Finset.sum_neg_distrib]
      _ = -∑ x : E, ∑ y : E, I x y := by
        rfl
  have hzero : ∑ x : E, ∑ y : E, I x y = 0 := by
    linarith
  simpa [netFlowAt] using hzero

namespace IsFlowOutside

/-- Kirchhoff's rule on `A`: in the finite setting, the total net flow across `A` vanishes. -/
theorem netFlowOnSet_eq_zero {A : Set E} {I : E → E → ℝ}
    (hI : IsFlowOutside A I) : netFlowOnSet I A = 0 := by
  have htotal : ∑ x : E, netFlowAt I x = 0 :=
    sum_netFlowAt_eq_zero hI.antisymm
  have hsplit :
      ∑ x : E, netFlowAt I x =
        (∑ x : A, netFlowAt I x) + ∑ x : (Aᶜ : Set E), netFlowAt I x := by
    calc
      ∑ x : E, netFlowAt I x
          = ∑ z : A ⊕ (Aᶜ : Set E), netFlowAt I (Equiv.Set.sumCompl A z) := by
              rw [Equiv.sum_comp (Equiv.Set.sumCompl A) (netFlowAt I)]
      _ = (∑ x : A, netFlowAt I x) + ∑ x : (Aᶜ : Set E), netFlowAt I x := by
            simp [Fintype.sum_sum_type]
  have hcompl : ∑ x : (Aᶜ : Set E), netFlowAt I x = 0 := by
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    exact hI.netFlowAt_eq_zero x.2
  have hA : ∑ x : A, netFlowAt I x = 0 := by
    linarith
  simpa [netFlowOnSet] using hA

end IsFlowOutside

-- Proof sketch: the zero map is antisymmetric and every vertex sum `∑ y, 0` is zero, so it
-- satisfies the defining conditions for a flow on `E \ A`.
/-- The zero map is a flow on `E \ A` for every set `A`. -/
instance instIsFlowOutsideZero (A : Set E) : IsFlowOutside A (fun _ _ : E ↦ 0) where
  antisymm _ _ := by simp
  netFlowAt_eq_zero _ := by simp [netFlowAt]

end ProbabilityTheory
