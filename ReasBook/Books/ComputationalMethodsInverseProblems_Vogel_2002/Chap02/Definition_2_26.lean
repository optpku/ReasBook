/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_24
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Basic

public section

/- Definition 2.26 (1). The source notion of a convex functional on a convex subset `C` of a
Hilbert space is formalized by the canonical mathlib predicate `ConvexOn ℝ C J`, where the
textbook `J : C → ℝ` is represented as an ambient map `J : H → ℝ` together with `C : Set H`. -/
#check ConvexOn

/- Definition 2.26 (2). The source notion of a strictly convex functional on `C` is formalized
by the canonical mathlib predicate `StrictConvexOn ℝ C J`. -/
#check StrictConvexOn

/- Definition 2.26 (3). The recalled notion that `C` is a convex subset is formalized by the
canonical predicate `Convex ℝ C`. -/
#check Convex

/- Definition 2.26 (4). The recalled notion that `C` is closed is formalized by the canonical
predicate `IsClosed C`. -/
#check IsClosed

/- The project notion referenced by the final sentence around weak lower semicontinuity is
`weakLowerSemicontinuous`. Recording that owner here does not assert an implication from bare
convexity alone; any such theorem requires extra hypotheses beyond Definition 2.26. -/
#check weakLowerSemicontinuous
