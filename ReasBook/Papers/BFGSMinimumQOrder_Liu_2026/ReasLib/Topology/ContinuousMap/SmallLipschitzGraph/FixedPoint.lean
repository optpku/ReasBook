module

public import ReasLib.Topology.ContinuousMap.SmallLipschitzGraph.Transform

public section

/-!
# Fixed-point bounds for small Lipschitz graphs

This file bridges pointwise estimates on graph transforms to Mathlib's canonical contraction
estimates in the sup metric.  In particular, it packages the exact `1 / (1 - K)` loss for
defect bounds, perturbations of the transform, and Lipschitz parameter dependence of the
resulting fixed-point graph.
-/

open scoped NNReal

universe u v

namespace SmallLipschitzGraph

variable {E : Type u} [NormedAddCommGroup E] [CompleteSpace E]
variable {radius slope : ℝ≥0}

/-- A pointwise defect bound controls the distance to the unique fixed-point graph. -/
theorem dist_fixedPoint_le_of_dist_apply_le
    {K : ℝ≥0}
    {T : SmallLipschitzGraph E radius slope →
      SmallLipschitzGraph E radius slope}
    (hT : ContractingWith K T)
    (ζ : SmallLipschitzGraph E radius slope)
    {C : ℝ}
    (hdefect : ∀ x : ℝ, dist (ζ x) (T ζ x) ≤ C) :
    dist ζ (ContractingWith.fixedPoint T hT) ≤ C / (1 - K) := by
  calc
    dist ζ (ContractingWith.fixedPoint T hT) ≤
        dist ζ (T ζ) / (1 - K) :=
      hT.dist_fixedPoint_le ζ
    _ ≤ C / (1 - K) :=
      (div_le_div_iff_of_pos_right hT.one_sub_K_pos).2
        (dist_le_iff.mpr hdefect)

/-- Pointwise closeness of two uniformly contracting graph transforms controls the distance
between their unique fixed-point graphs. -/
theorem dist_fixedPoint_fixedPoint_le_of_dist_apply_le
    {K : ℝ≥0}
    {T S : SmallLipschitzGraph E radius slope →
      SmallLipschitzGraph E radius slope}
    (hT : ContractingWith K T)
    (hS : ContractingWith K S)
    {C : ℝ}
    (hTS : ∀ ζ x, dist (T ζ x) (S ζ x) ≤ C) :
    dist (ContractingWith.fixedPoint T hT)
        (ContractingWith.fixedPoint S hS) ≤ C / (1 - K) := by
  apply hT.fixedPoint_lipschitz_in_map hS
  intro ζ
  exact dist_le_iff.mpr (hTS ζ)

/-- A uniformly contracting family whose outputs are pointwise Lipschitz in the parameter has
fixed-point graphs that are Lipschitz in that parameter, with the exact constant
`L / (1 - K)`. -/
theorem lipschitzWith_fixedPoint_of_dist_apply_le_mul
    {P : Type v} [PseudoMetricSpace P]
    {K L : ℝ≥0}
    {T : P → SmallLipschitzGraph E radius slope →
      SmallLipschitzGraph E radius slope}
    (hK : K < 1)
    (hT : ∀ p, ContractingWith K (T p))
    (hMap : ∀ p q ζ x, dist (T p ζ x) (T q ζ x) ≤ L * dist p q) :
    LipschitzWith (L / (1 - K))
      (fun p => ContractingWith.fixedPoint (T p) (hT p)) := by
  refine LipschitzWith.of_dist_le_mul fun p q => ?_
  have hbound :
      dist (ContractingWith.fixedPoint (T p) (hT p))
          (ContractingWith.fixedPoint (T q) (hT q)) ≤
        (L * dist p q) / (1 - K) :=
    dist_fixedPoint_fixedPoint_le_of_dist_apply_le
      (hT p) (hT q) (fun ζ x => hMap p q ζ x)
  calc
    dist (ContractingWith.fixedPoint (T p) (hT p))
        (ContractingWith.fixedPoint (T q) (hT q)) ≤
      (L * dist p q) / (1 - K) := hbound
    _ = (L / (1 - K) : ℝ≥0) * dist p q := by
      rw [NNReal.coe_div, NNReal.coe_sub hK.le]
      norm_num
      ring

end SmallLipschitzGraph
