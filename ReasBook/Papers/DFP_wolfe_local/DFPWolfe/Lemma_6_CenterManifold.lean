/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.TwoPhaseControls.StateMap.Linearization
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve

/-!
# Lemma 6: invariant center manifold

Paper label: `lem:center-manifold` in `main-new.tex`.

After cancellation of the singular factors, the two-leg state map is real
analytic near `(0, 2, 1)`. Its derivative has eigenvalues `1`, `-1 / 9`, and
`0`. It admits a locally forward-invariant one-dimensional `C⁷` graph with
`p(ε) = 2 + (198 / 5)ε³ - (9 / 5)ε⁴ + O(ε⁵)` and
`h(ε) = 1 + 8ε³ + O(ε⁵)`, and scale recurrence
`ε₊ = ε - (3 / 2)ε⁴ + (5 / 4)ε⁵ + O(ε⁶)`.

The checks locate the analytic extension in `StateMap`, its derivative in
`StateMap.Linearization`, and the graph with both jets and recurrence in
`SlowCurve`. These are components of one paper lemma.
-/

-- Agreement with the recovered map and regularity at the singular limit.
#check DFP.TwoLeg.stateMap_eventuallyEq_recovered
#check DFP.TwoLeg.stateMapAnalytic

-- The derivative and its three eigenvalues.
#check DFP.TwoLeg.stateMap_fderiv_apply
#check DFP.TwoLeg.stateMap_centerEigenvalue
#check DFP.TwoLeg.stateMap_transverseEigenvalue_negNinth
#check DFP.TwoLeg.stateMap_transverseEigenvalue_zero

-- The graph, `eq:center-curve`, and `eq:epsilon-map`.
#check DFP.TwoLeg.exists_localForwardInvariantSlowCurve
