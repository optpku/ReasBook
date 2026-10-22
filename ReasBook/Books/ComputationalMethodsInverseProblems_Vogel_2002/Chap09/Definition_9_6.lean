/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A1.ClosedConvex
public import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

public section

noncomputable section

namespace EuclideanProjection

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Definition 9.6. The Euclidean projection onto a nonempty closed convex set `C`, viewed as a
map `H → H`. -/
def proj (C : Set H) (hC_nonempty : C.Nonempty) (hC : Set.ClosedConvex C) :
    H → H :=
  fun f ↦
    Classical.choose
      (exists_norm_eq_iInf_of_complete_convex
        hC_nonempty
        hC.isClosed.isComplete
        hC.convex
        f)

end EuclideanProjection

/- Definition 9.6. The Euclidean projection onto a closed convex set is formalized
by the reusable map-valued owner `EuclideanProjection.proj`. Its signature
reuses the chapter-level feasible-set owner `Set.ClosedConvex C` and also makes
the hidden well-definedness hypothesis `C.Nonempty` explicit.
-/
#check EuclideanProjection.proj

#print axioms EuclideanProjection.proj
