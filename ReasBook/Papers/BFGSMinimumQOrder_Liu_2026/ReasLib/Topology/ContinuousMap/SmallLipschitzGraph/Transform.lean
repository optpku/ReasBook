module

public import ReasLib.Topology.ContinuousMap.SmallLipschitzGraph
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Topology.MetricSpace.Contracting

public section

open scoped NNReal

universe u v

namespace AntilipschitzWith

/-- Uniformly close forward maps have close right inverses when the first forward map
is antilipschitz. -/
theorem dist_rightInverse_rightInverse_le
    {α : Type u} {β : Type v} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {K : ℝ≥0} {f g : α → β} {fInv gInv : β → α}
    (hf : AntilipschitzWith K f)
    (hfInv : Function.RightInverse fInv f)
    (hgInv : Function.RightInverse gInv g)
    {C : ℝ} (hfg : ∀ x, dist (f x) (g x) ≤ C) (y : β) :
    dist (fInv y) (gInv y) ≤ K * C := by
  calc
    dist (fInv y) (gInv y) ≤ K * dist (f (fInv y)) (f (gInv y)) :=
      hf.le_mul_dist _ _
    _ = K * dist (f (gInv y)) y := by rw [hfInv y, dist_comm]
    _ = K * dist (f (gInv y)) (g (gInv y)) := by rw [hgInv y]
    _ ≤ K * C := mul_le_mul_of_nonneg_left (hfg _) K.coe_nonneg

end AntilipschitzWith

namespace SmallLipschitzGraph

variable {E : Type u} [NormedAddCommGroup E] {radius slope : ℝ≥0}

/-- Evaluation at any point is nonexpanding for the sup distance on small Lipschitz
graphs. -/
theorem dist_apply_le (ζ η : SmallLipschitzGraph E radius slope) (x : ℝ) :
    dist (ζ x) (η x) ≤ dist ζ η := by
  exact BoundedContinuousFunction.dist_coe_le_dist x

/-- A sup-distance bound on small Lipschitz graphs is equivalent to the corresponding
pointwise bounds. -/
theorem dist_le_iff {ζ η : SmallLipschitzGraph E radius slope} {C : ℝ} :
    dist ζ η ≤ C ↔ ∀ x : ℝ, dist (ζ x) (η x) ≤ C := by
  exact BoundedContinuousFunction.dist_le_iff_of_nonempty

/-- A pointwise output estimate by the input sup distance upgrades a self-map to
`ContractingWith`. -/
theorem contractingWith_of_dist_apply_le_mul
    {K : ℝ≥0} {T : SmallLipschitzGraph E radius slope →
      SmallLipschitzGraph E radius slope}
    (hK : K < 1)
    (hT : ∀ ζ η x, dist (T ζ x) (T η x) ≤ K * dist ζ η) :
    ContractingWith K T := by
  refine ⟨hK, LipschitzWith.of_dist_le_mul fun ζ η ↦ ?_⟩
  exact dist_le_iff.mpr (hT ζ η)

end SmallLipschitzGraph
