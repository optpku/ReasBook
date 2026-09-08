module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed

/-!
# Smoothness of matrix assembly

`Matrix.of` changes a doubly indexed family into a matrix.  Under the elementwise matrix norm this
is an isometric linear map, so smooth matrix literals can be assembled coordinatewise.  The direct
`fun_prop` rules below hide the otherwise visible mismatch between the named matrix norm instance
and the definitionally equal Pi-space norm.
-/

public section

open scoped Nat ContDiff Matrix.Norms.Elementwise

universe uE

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {m n : Type*} [Fintype m] [Fintype n] {k : ℕ∞ω}

private noncomputable def matrixOfCLM :
    (m → n → 𝕜) →L[𝕜] Matrix m n 𝕜 :=
  (Matrix.ofLinearEquiv 𝕜).toLinearMap.mkContinuous 1 fun A => by
    change ‖Matrix.of A‖ ≤ 1 * ‖A‖
    rw [one_mul]
    rfl

private theorem matrixOfCLM_apply (A : m → n → 𝕜) :
    matrixOfCLM (𝕜 := 𝕜) A = Matrix.of A := by
  rfl

/-- Pointwise smooth doubly indexed families assemble into pointwise smooth matrices. -/
@[fun_prop]
theorem contDiffAt_matrix_of {f : E → m → n → 𝕜} {x : E}
    (hf : ContDiffAt 𝕜 k f x) :
    ContDiffAt 𝕜 k (fun y ↦ Matrix.of (f y)) x := by
  have hfun : (fun y ↦ Matrix.of (f y)) = matrixOfCLM (𝕜 := 𝕜) ∘ f := by
    funext y
    exact (matrixOfCLM_apply (𝕜 := 𝕜) (f y)).symm
  rw [hfun]
  exact (matrixOfCLM (𝕜 := 𝕜)).contDiff.contDiffAt.comp x hf

/-- Globally smooth doubly indexed families assemble into globally smooth matrices. -/
@[fun_prop]
theorem contDiff_matrix_of {f : E → m → n → 𝕜}
    (hf : ContDiff 𝕜 k f) :
    ContDiff 𝕜 k (fun y ↦ Matrix.of (f y)) := by
  have hfun : (fun y ↦ Matrix.of (f y)) = matrixOfCLM (𝕜 := 𝕜) ∘ f := by
    funext y
    exact (matrixOfCLM_apply (𝕜 := 𝕜) (f y)).symm
  rw [hfun]
  exact (matrixOfCLM (𝕜 := 𝕜)).contDiff.comp hf
