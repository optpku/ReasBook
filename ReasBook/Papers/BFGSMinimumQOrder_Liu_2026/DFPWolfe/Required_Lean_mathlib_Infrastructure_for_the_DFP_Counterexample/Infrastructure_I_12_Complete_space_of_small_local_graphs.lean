module

public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import ReasLib.Topology.ContinuousMap.SmallLipschitzGraph

public section

open scoped NNReal

variable (m : ℕ) (radius slope : ℝ≥0)

/-
Infrastructure I.12 (Complete space of small local graphs): bounded maps
`ζ : ℝ → EuclideanSpace ℝ (Fin m)` that vanish at zero and satisfy prescribed sup-norm
and Lipschitz bounds form a closed complete subspace in the sup metric.
-/
#check (SmallLipschitzGraph (EuclideanSpace ℝ (Fin m)) radius slope : Type)
#check SmallLipschitzGraph.isClosed_carrier
#check SmallLipschitzGraph.instCompleteSpace
