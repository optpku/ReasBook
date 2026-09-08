module

public import ReasLib.Topology.ContinuousMap.SmallLipschitzGraph.Transform

public section

noncomputable section

open scoped NNReal

namespace SmallLipschitzGraph

/-!
# Generic split-coordinate contraction estimates

The first theorem below is independent of graph transforms: it packages the
triangle inequality, the stable-fiber estimate, and the inverse-center estimate
into the standard two-coordinate contraction coefficient.  The `ℝ≥0` wrappers
then make the coefficient convenient for `ContractingWith` and fixed-point APIs.
-/

/-- The real-valued coefficient produced by a linear/stable-fiber split and an
inverse-center estimate. -/
def splitRateReal (lower linearRate stableCenter stableFiber centerFiber slope : ℝ) : ℝ :=
  (linearRate + stableFiber) +
    (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ * centerFiber

/-- A coordinate split bounds the output displacement by the standard rate times
the input discrepancy. -/
theorem norm_add_sub_le_of_split_estimates
    {E : Type*} [NormedAddCommGroup E]
    {a b r s z w : E} {u v D : ℝ}
    {lower linearRate stableCenter stableFiber centerFiber slope : ℝ}
    (hlinear : ‖a - b‖ ≤ linearRate * ‖z - w‖)
    (hstable : ‖r - s‖ ≤ stableCenter * |u - v| + stableFiber * ‖z - w‖)
    (hgraph : ‖z - w‖ ≤ slope * |u - v| + D)
    (hinverse : |u - v| ≤ lower⁻¹ * centerFiber * D)
    (hlinear_nonneg : 0 ≤ linearRate)
    (hstableCenter_nonneg : 0 ≤ stableCenter)
    (hstableFiber_nonneg : 0 ≤ stableFiber)
    (hslope_nonneg : 0 ≤ slope) :
    ‖(a + r) - (b + s)‖ ≤
      splitRateReal lower linearRate stableCenter stableFiber centerFiber slope * D := by
  have hbase_nonneg : 0 ≤ linearRate + stableFiber := by
    exact add_nonneg hlinear_nonneg hstableFiber_nonneg
  have hcenter_nonneg :
      0 ≤ stableCenter + (linearRate + stableFiber) * slope := by
    exact add_nonneg hstableCenter_nonneg (mul_nonneg hbase_nonneg hslope_nonneg)
  have hgraph_scaled :
      (linearRate + stableFiber) * ‖z - w‖ ≤
        (linearRate + stableFiber) * (slope * |u - v| + D) := by
    exact mul_le_mul_of_nonneg_left hgraph hbase_nonneg
  have hinverse_scaled :
      (stableCenter + (linearRate + stableFiber) * slope) * |u - v| ≤
        (stableCenter + (linearRate + stableFiber) * slope) *
          (lower⁻¹ * centerFiber * D) := by
    exact mul_le_mul_of_nonneg_left hinverse hcenter_nonneg
  calc
    ‖(a + r) - (b + s)‖ ≤ ‖a - b‖ + ‖r - s‖ := by
      rw [add_sub_add_comm]
      exact norm_add_le _ _
    _ ≤ linearRate * ‖z - w‖ +
        (stableCenter * |u - v| + stableFiber * ‖z - w‖) :=
      add_le_add hlinear hstable
    _ = stableCenter * |u - v| + (linearRate + stableFiber) * ‖z - w‖ := by
      ring
    _ ≤ stableCenter * |u - v| +
        (linearRate + stableFiber) * (slope * |u - v| + D) := by
      exact add_le_add (le_refl _) hgraph_scaled
    _ = (stableCenter + (linearRate + stableFiber) * slope) * |u - v| +
        (linearRate + stableFiber) * D := by
      ring
    _ ≤ (stableCenter + (linearRate + stableFiber) * slope) *
          (lower⁻¹ * centerFiber * D) +
        (linearRate + stableFiber) * D := by
      exact add_le_add hinverse_scaled (le_refl _)
    _ = splitRateReal lower linearRate stableCenter stableFiber centerFiber slope * D := by
      dsimp only [splitRateReal]
      ring

/-- The nonnegative contraction coefficient associated with the coordinate split. -/
def splitRate (lower linearRate stableCenter stableFiber centerFiber slope : ℝ≥0) : ℝ≥0 :=
  (linearRate + stableFiber) +
    (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ * centerFiber

/-- Coercing `splitRate` to `ℝ` exposes the corresponding real coefficient. -/
theorem coe_splitRate (lower linearRate stableCenter stableFiber centerFiber slope : ℝ≥0) :
    (splitRate lower linearRate stableCenter stableFiber centerFiber slope : ℝ) =
      splitRateReal (lower : ℝ) (linearRate : ℝ) (stableCenter : ℝ)
        (stableFiber : ℝ) (centerFiber : ℝ) (slope : ℝ) := by
  rfl

/-- Component budgets imply an upper bound for the split contraction coefficient. -/
theorem splitRate_le_of_component_budgets
    (lower linearRate stableCenter stableFiber centerFiber slope base coupling : ℝ≥0)
    (hbase : linearRate + stableFiber ≤ base)
    (hcoupling :
      (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ * centerFiber ≤ coupling) :
    splitRate lower linearRate stableCenter stableFiber centerFiber slope ≤ base + coupling := by
  dsimp only [splitRate]
  exact add_le_add hbase hcoupling

/-- A strict budget below one makes the split coefficient a strict contraction. -/
theorem splitRate_lt_one_of_component_budgets
    (lower linearRate stableCenter stableFiber centerFiber slope base coupling : ℝ≥0)
    (hbase : linearRate + stableFiber ≤ base)
    (hcoupling :
      (stableCenter + (linearRate + stableFiber) * slope) * lower⁻¹ * centerFiber ≤ coupling)
    (hbudget : base + coupling < 1) :
    splitRate lower linearRate stableCenter stableFiber centerFiber slope < 1 := by
  exact (splitRate_le_of_component_budgets lower linearRate stableCenter stableFiber
    centerFiber slope base coupling hbase hcoupling).trans_lt hbudget

/-- A pointwise sup-distance estimate with `splitRate` yields the corresponding
`ContractingWith` instance for a small-Lipschitz-graph transform. -/
theorem contractingWith_of_splitRate_bound
    {E : Type*} [NormedAddCommGroup E] {radius slope : ℝ≥0}
    {T : SmallLipschitzGraph E radius slope → SmallLipschitzGraph E radius slope}
    (lower linearRate stableCenter stableFiber centerFiber : ℝ≥0)
    (hRate : splitRate lower linearRate stableCenter stableFiber centerFiber slope < 1)
    (hPointwise : ∀ ζ η : SmallLipschitzGraph E radius slope, ∀ x : ℝ,
      dist (T ζ x) (T η x) ≤
        (splitRate lower linearRate stableCenter stableFiber centerFiber slope : ℝ) *
          dist ζ η) :
    ContractingWith (splitRate lower linearRate stableCenter stableFiber centerFiber slope) T := by
  exact contractingWith_of_dist_apply_le_mul hRate hPointwise

end SmallLipschitzGraph
