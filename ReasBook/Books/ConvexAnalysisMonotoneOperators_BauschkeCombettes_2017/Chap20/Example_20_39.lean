/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_32_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Proposition_4_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Text_4_21_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_30

open SubtypeFirmness

open Filter
open scoped InnerProductSpace Topology

local notation "L2" => lp (fun _ : ℕ ↦ ℝ) 2

namespace Function

local notation "C" => Metric.closedBall (0 : L2) 1

private theorem closedUnitBall_nonempty :
    (Metric.closedBall (0 : L2) 1 : Set L2).Nonempty :=
  Metric.nonempty_closedBall.2 zero_le_one

local notation "hC" =>
  isChebyshev_of_nonempty_isClosed_convex
    closedUnitBall_nonempty
    (Metric.isClosed_closedBall : IsClosed C)
    (convex_closedBall (0 : L2) 1)

/-- The residual map `Id - P_C` for the closed unit ball `C` of `ℓ²(ℕ, ℝ)`. -/
noncomputable def l2ClosedUnitBallResidualMap : L2 → L2 :=
  id - P[C, hC]

local notation "W" => Prod.map (toWeakSpace ℝ L2) (toWeakSpace ℝ L2)

-- The standard unit vector `e_n` in `ℓ²(ℕ, ℝ)`.
private noncomputable def l2BasisVector (n : ℕ) : L2 :=
  lp.single 2 n 1

-- The 0-indexed Lean version of the textbook witness sequence `e_1 + e_{2n}`.
private noncomputable def l2CounterexampleSequence : ℕ → L2 :=
  fun n ↦ l2BasisVector 1 + l2BasisVector (2 * n + 2)

-- The weak limit of the witness sequence.
private noncomputable def l2CounterexampleLimit : L2 :=
  l2BasisVector 1

-- Proof sketch: the metric projection onto a nonempty closed convex set is firmly nonexpansive;
-- for the closed unit ball this makes the residual map `1 / 2`-averaged, so Example 20.30 gives
-- maximal monotonicity of the associated singleton-valued operator.
private theorem l2ClosedUnitBallResidualMap_isMaximallyMonotone :
    Maximal SetValuedOperator.IsMonotone l2ClosedUnitBallResidualMap.toSetValuedOperator := by
  have hproj :
      FirmlyNonexpansive (P[C, hC] : L2 → L2) :=
    firmlyNonexpansive_projectionPoint_of_nonempty_isClosed_convex
      closedUnitBall_nonempty
      (Metric.isClosed_closedBall : IsClosed C)
      (convex_closedBall (0 : L2) 1)
  have hproj_on :
      FirmlyNonexpansiveOn (Set.univ : Set L2) (fun x : Set.univ ↦ P[C, hC] x) := by
    simpa [firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ] using hproj
  have hresidual :
      FirmlyNonexpansive l2ClosedUnitBallResidualMap := by
    simpa [l2ClosedUnitBallResidualMap, residualMap,
      firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ] using
      (firmlyNonexpansiveOn_residualMap_iff (Set.univ : Set L2)
        (fun x : Set.univ ↦ P[C, hC] x)).2 hproj_on
  exact Function.toSetValuedOperator_isMaximallyMonotone_of_averaged_le_half
    ((firmlyNonexpansive_iff_averaged_half).mp hresidual) le_rfl

-- Proof sketch: every term of the witness sequence has norm `√2`, so projection onto the closed
-- unit ball rescales it by `1 / √2`; subtracting the projection gives the factor
-- `(1 - 1 / √2)`. This identifies the displayed pairs as graph points.
private theorem l2ClosedUnitBallResidualMap_witness_mem_graph (n : ℕ) :
    (l2CounterexampleSequence n,
      (1 - 1 / Real.sqrt 2) • l2CounterexampleSequence n) ∈
        l2ClosedUnitBallResidualMap.toSetValuedOperator.graph := sorry

-- Proof sketch: the shifted even-coordinate basis tail is orthonormal and hence weakly null;
-- adding `e_1` yields weak convergence of `x_n` to `e_1`, and scalar multiplication preserves weak
-- convergence of the second coordinate. Therefore the graph-point sequence converges in the
-- product weak topology.
private theorem l2ClosedUnitBallResidualMap_witness_tendsto_weakly :
    Tendsto
      (fun n ↦
        W
          (l2CounterexampleSequence n,
            (1 - 1 / Real.sqrt 2) • l2CounterexampleSequence n))
      atTop
      (𝓝 ((toWeakSpace ℝ L2) l2CounterexampleLimit,
        (toWeakSpace ℝ L2) ((1 - 1 / Real.sqrt 2) • l2CounterexampleLimit))) := sorry

-- Proof sketch: the limit vector `e_1` lies on the unit sphere, so its projection onto the
-- closed unit ball is itself and the residual vanishes there. Hence the graph value at `e_1` is
-- `0`, not `(1 - 1 / √2) • e_1`.
private theorem l2ClosedUnitBallResidualMap_witness_limit_not_mem_graph :
    (l2CounterexampleLimit,
      (1 - 1 / Real.sqrt 2) • l2CounterexampleLimit) ∉
        l2ClosedUnitBallResidualMap.toSetValuedOperator.graph := sorry

-- Proof sketch: combine maximal monotonicity of the residual map with the explicit witness graph
-- sequence, its product-weak convergence, and the fact that the limit pair lies outside the graph.
/-- Example 20.39: for the closed unit ball of `ℓ²(ℕ, ℝ)`, subtracting the canonical metric
projection onto that ball yields a maximally monotone operator whose graph is not sequentially
closed in the product weak topology. -/
theorem l2ClosedUnitBallResidualMap_maximallyMonotone_and_graph_not_seqClosed_weakProduct :
    Maximal SetValuedOperator.IsMonotone l2ClosedUnitBallResidualMap.toSetValuedOperator ∧
      ¬ IsSeqClosed
        (W '' l2ClosedUnitBallResidualMap.toSetValuedOperator.graph) := sorry

end Function
