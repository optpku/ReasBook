/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_12_Complete_space_of_small_local_graphs.lean
-/

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
