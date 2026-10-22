/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_1

noncomputable section

section Chapter11Definition1117

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling:
-- * primary domain: first-order constrained optimization in a real Hilbert space
-- * owner abstractions inspected:
--   `IsFeasibleDirectionAt`, `feasibleDirections`, `IsDescentDirectionAt`
-- * source/core/bridge triage:
--   `source-facing`: `IsFeasibleSteepestDescentDirection`
--   `core/canonical`: Chapter 8's `IsFeasibleDirectionAt` / `feasibleDirections`
--   `bridge/view`: `isFeasibleSteepestDescentDirection_iff`
-- * primitive data here: differentiability at `x`, nonvanishing of the chosen direction `d`,
--   closure membership in the Chapter 8 feasible-direction set, and the minimization inequality
-- * derived API here: feasibility of the base point and the unpacked conjunction theorem

/-- The normalized first-order objective pairing `dᵀ ∇f(x) / ‖d‖` used in the source minimization
problem. -/
def normalizedGradientPairing (f : E → ℝ) (x d : E) : ℝ :=
  inner ℝ d (gradient f x) / ‖d‖

/-- The defining formula for `normalizedGradientPairing`. -/
theorem normalizedGradientPairing_eq
    (f : E → ℝ) (x d : E) :
    normalizedGradientPairing f x d = inner ℝ d (gradient f x) / ‖d‖ :=
  rfl

/-- Chapter11 Definition 11.1.7: a vector `d` is a feasible steepest descent direction at `x`
when `f` is differentiable at `x`, `d ≠ 0`, `d` belongs to the closure of the Chapter 8 feasible
direction set `FD(x, X)`, and its normalized gradient pairing is minimal among all feasible
directions in `FD(x, X)`. -/
class IsFeasibleSteepestDescentDirection
    (f : E → ℝ) (x : E) (X : Set E) (d : E) : Prop where
  ne : d ≠ 0
  differentiableAt : DifferentiableAt ℝ f x
  mem_closure : d ∈ closure (feasibleDirections x X)
  minimal (d' : E) (hd' : d' ∈ feasibleDirections x X) :
    normalizedGradientPairing f x d ≤ normalizedGradientPairing f x d'

/-- `IsFeasibleSteepestDescentDirection f x X d` is a proposition. -/
instance instSubsingletonIsFeasibleSteepestDescentDirection
    (f : E → ℝ) (x d : E) (X : Set E) :
    Subsingleton (IsFeasibleSteepestDescentDirection f x X d) :=
  inferInstance

/-- Unfolding formula for `IsFeasibleSteepestDescentDirection`. -/
theorem isFeasibleSteepestDescentDirection_iff
    (f : E → ℝ) (x d : E) (X : Set E) :
    IsFeasibleSteepestDescentDirection f x X d ↔
      d ≠ 0 ∧
        DifferentiableAt ℝ f x ∧
          d ∈ closure (feasibleDirections x X) ∧
            ∀ d' ∈ feasibleDirections x X,
              normalizedGradientPairing f x d ≤ normalizedGradientPairing f x d' := by
  constructor
  · intro h
    exact ⟨h.ne, h.differentiableAt, h.mem_closure, h.minimal⟩
  · rintro ⟨hne, hdiff, hclosure, hminimal⟩
    exact ⟨hne, hdiff, hclosure, hminimal⟩

/-- A feasible steepest descent direction is nonzero. -/
theorem IsFeasibleSteepestDescentDirection.ne_zero
    {f : E → ℝ} {x d : E} {X : Set E}
    (h : IsFeasibleSteepestDescentDirection f x X d) :
    d ≠ 0 :=
  h.ne

/-- A feasible steepest descent direction is based at a feasible point. -/
theorem IsFeasibleSteepestDescentDirection.mem_base
    {f : E → ℝ} {x d : E} {X : Set E}
    (h : IsFeasibleSteepestDescentDirection f x X d) :
    x ∈ X := by
  by_contra hx
  have h_empty : feasibleDirections x X = ∅ := by
    ext d'
    constructor
    · intro hd'
      exact False.elim (hx ((mem_feasibleDirections_iff x d' X).mp hd').mem)
    · intro hd'
      simp at hd'
  simpa [h_empty] using h.mem_closure

/-- The defining minimization inequality for a feasible steepest descent direction. -/
theorem IsFeasibleSteepestDescentDirection.le_normalizedGradientPairing
    {f : E → ℝ} {x d d' : E} {X : Set E}
    (h : IsFeasibleSteepestDescentDirection f x X d)
    (hd' : d' ∈ feasibleDirections x X) :
    normalizedGradientPairing f x d ≤ normalizedGradientPairing f x d' :=
  h.minimal d' hd'

end Chapter11Definition1117
