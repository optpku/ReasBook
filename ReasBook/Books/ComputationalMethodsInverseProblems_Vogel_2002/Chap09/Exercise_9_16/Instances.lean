/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

namespace EuclideanSpace

universe u v

/-- `EuclideanSpace 𝕜 ι` inherits the canonical pointwise multiplication from
`ι → 𝕜`. -/
instance instMul {𝕜 : Type u} {ι : Type v} [Mul 𝕜] : Mul (EuclideanSpace 𝕜 ι) :=
  (WithLp.equiv 2 (ι → 𝕜)).mul

@[simp] theorem ofLp_mul {𝕜 : Type u} {ι : Type v} [Mul 𝕜]
    (u v : EuclideanSpace 𝕜 ι) : (u * v).ofLp = u.ofLp * v.ofLp :=
  rfl

end EuclideanSpace
