module

public import ReasLib.Analysis.Calculus.ContDiff.DotProduct
import all ReasLib.Analysis.Calculus.ContDiff.DotProduct
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Smoothness of matrix-vector multiplication

Matrix-vector multiplication is a finite family of dot products.  Registering that observation
directly lets `fun_prop` handle parameter-dependent matrices and vectors.
-/

public section

open scoped Nat ContDiff Matrix

universe uE

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {m n : Type*} [Fintype m] [Fintype n] {k : ℕ∞ω}

/-- Pointwise smooth matrix and vector families have a smooth matrix-vector product. -/
@[fun_prop]
theorem contDiffAt_matrix_mulVec
    {f : E → m → n → 𝕜} {g : E → n → 𝕜} {x : E}
    (hf : ContDiffAt 𝕜 k f x) (hg : ContDiffAt 𝕜 k g x) :
    ContDiffAt 𝕜 k (fun y ↦ Matrix.mulVec (f y) (g y)) x := by
  rw [contDiffAt_pi]
  intro i
  simpa only [Matrix.mulVec] using
    contDiffAt_dotProduct (contDiffAt_pi.mp hf i) hg

/-- Globally smooth matrix and vector families have a smooth matrix-vector product. -/
@[fun_prop]
theorem contDiff_matrix_mulVec
    {f : E → m → n → 𝕜} {g : E → n → 𝕜}
    (hf : ContDiff 𝕜 k f) (hg : ContDiff 𝕜 k g) :
    ContDiff 𝕜 k (fun y ↦ Matrix.mulVec (f y) (g y)) := by
  rw [contDiff_pi]
  intro i
  simpa only [Matrix.mulVec] using
    contDiff_dotProduct (contDiff_pi.mp hf i) hg
