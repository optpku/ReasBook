/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Lemma_1_5_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped unitInterval

/-- The basepoint `0 : ℝ` lies in the fiber of `Real.fourierChar` over `1 : Circle`. -/
-- Proof sketch: evaluate `Real.fourierChar` at `0` and simplify to `1`.
theorem mem_fourierChar_unit_fiber_zero :
    (0 : ℝ) ∈ Real.fourierChar ⁻¹' ({(1 : Circle)} : Set Circle) := by
  -- Evaluating `Real.fourierChar` at `0` lands at the basepoint of the circle.
  simp

/-- The canonical endpoint of the lift of a based loop class in `S¹` through
`Real.fourierChar : ℝ → S¹`, starting at `0`. -/
def circleFundamentalGroupLiftEndpoint
    (γ : FundamentalGroup Circle (1 : Circle)) :
    Real.fourierChar ⁻¹' ({(1 : Circle)} : Set Circle) :=
  real_fourierChar_isCoveringMap.monodromy (FundamentalGroup.toPath γ)
    ⟨0, mem_fourierChar_unit_fiber_zero⟩

/-- Definition 1.5.8: the map `j : π₁(S^1, 1) → ℤ` sends a loop class to the integer endpoint of
the unique lift through `Real.fourierChar : ℝ → S¹` starting at `0`. -/
def circleFundamentalGroupLiftIndex
    (γ : FundamentalGroup Circle (1 : Circle)) : ℤ :=
  Int.floor (circleFundamentalGroupLiftEndpoint γ : ℝ)

/-- Helper for Definition 1.5.8: a point of the fiber of `Real.fourierChar` over `1` is an
integer, so taking its floor recovers it exactly. -/
lemma floor_eq_self_of_mem_fourierChar_unit_fiber (x : ℝ)
    (hx : x ∈ Real.fourierChar ⁻¹' ({(1 : Circle)} : Set Circle)) :
    ((Int.floor x : ℤ) : ℝ) = x := by
  -- Rewrite fiber membership as an equation in `Circle.exp`.
  exact (Int.floor_eq_self_iff_mem x).2 <| by
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    rw [Real.fourierChar_apply'] at hx
    rcases (Circle.exp_eq_one).1 hx with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    -- Cancel the nonzero factor `2 * π` to identify the endpoint with the integer `n`.
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by
      positivity
    have hx_eq := congrArg (fun t : ℝ => t / (2 * Real.pi)) hn
    simp [h2pi] at hx_eq
    simpa using hx_eq.symm

/-- The canonical lifted endpoint is the endpoint of the lifted representative loop starting
at `0`. -/
-- Proof sketch: unfold `circleFundamentalGroupLiftEndpoint`, evaluate monodromy on the path class
-- of `γ`, and identify the result with the endpoint of `real_fourierChar_isCoveringMap.liftPath`.
theorem circleFundamentalGroupLiftEndpoint_spec (γ : Path (1 : Circle) 1) :
    (circleFundamentalGroupLiftEndpoint (FundamentalGroup.fromPath ⟦γ⟧) : ℝ) =
      real_fourierChar_isCoveringMap.liftPath γ.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ) 1 := by
  -- Monodromy on the path class is definitionally the endpoint of the lifted path.
  rfl

/-- The lift index of a loop class is the endpoint of the lifted representative loop starting
at `0`. -/
-- Proof sketch: combine `circleFundamentalGroupLiftEndpoint_spec` with the fact that the lifted
-- endpoint lies in the unit fiber of `Real.fourierChar`, hence is an integer.
theorem circleFundamentalGroupLiftIndex_spec (γ : Path (1 : Circle) 1) :
    ((circleFundamentalGroupLiftIndex (FundamentalGroup.fromPath ⟦γ⟧) : ℤ) : ℝ) =
      real_fourierChar_isCoveringMap.liftPath γ.toContinuousMap 0
        (circle_path_start_eq_fourierChar_zero γ) 1 := by
  -- Rewrite the index through the concrete lifted endpoint supplied by monodromy.
  rw [circleFundamentalGroupLiftIndex, circleFundamentalGroupLiftEndpoint_spec]
  -- The endpoint remains in the unit fiber, so the floor lemma recovers it exactly.
  exact floor_eq_self_of_mem_fourierChar_unit_fiber _
    (circleFundamentalGroupLiftEndpoint (FundamentalGroup.fromPath ⟦γ⟧)).2
