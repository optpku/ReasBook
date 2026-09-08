import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump.CenterJet
import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump.DisjointInterpolation
import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumC2
import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumC2Jets
import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumDecay
import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumObjectiveBounds
import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumObjectiveInterpolation
import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumStrongConvexity
import ReasLib.Analysis.Calculus.ContDiff.DisjointFinsumWeightedBounds
import ReasLib.Analysis.Calculus.EuclideanPlaneSmoothCutoff
import ReasLib.Analysis.Calculus.Gradient.OrthogonalSum.Hessian
import ReasLib.Analysis.Convex.HessianPerturbation.Bounds
import ReasLib.Analysis.Convex.HessianPerturbation.Interpolation

/-!
Compatibility import for the reusable smooth interpolation infrastructure selected
from `imathwy/DFP_wolfe_local` at commit
`e308927f5b7930bdd002f0c0e42b9d112ad821cb`.

This module intentionally does not import the DFP-specific theorem development.  It
collects only the transitive dependency closure needed for the local BFGS proof's
smooth extension, Hessian perturbation, orthogonal-sum, and strong-convexity steps.
-/
