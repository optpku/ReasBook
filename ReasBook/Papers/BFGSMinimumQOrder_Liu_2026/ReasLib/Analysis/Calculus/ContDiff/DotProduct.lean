module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Smoothness of finite dot products

The finite dot product is a polynomial operation, but exposing its smoothness directly keeps
`fun_prop` from getting stuck on the named `dotProduct` wrapper.
-/

public section

open scoped Nat ContDiff

universe uE

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {ι : Type*} [Fintype ι] {k : ℕ∞ω}

/-- Pointwise smooth finite-vector families have a smooth pointwise dot product. -/
@[fun_prop]
theorem contDiffAt_dotProduct {f g : E → ι → 𝕜} {x : E}
    (hf : ContDiffAt 𝕜 k f x) (hg : ContDiffAt 𝕜 k g x) :
    ContDiffAt 𝕜 k (fun y ↦ dotProduct (f y) (g y)) x := by
  unfold dotProduct
  fun_prop

/-- Globally smooth finite-vector families have a smooth pointwise dot product. -/
@[fun_prop]
theorem contDiff_dotProduct {f g : E → ι → 𝕜}
    (hf : ContDiff 𝕜 k f) (hg : ContDiff 𝕜 k g) :
    ContDiff 𝕜 k (fun y ↦ dotProduct (f y) (g y)) := by
  unfold dotProduct
  fun_prop
