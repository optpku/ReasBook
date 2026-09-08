module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Matrix.Normed

/-!
# Smoothness of diagonal matrix families

With the elementwise matrix norm, `Matrix.diagonal` is an isometric linear map.  Packaging that
map continuously lets `fun_prop` recognize parameter-dependent diagonal matrices without exposing
matrix norm instances or the implementation of `Matrix.diagonal`.
-/

public section

open scoped Nat ContDiff Matrix.Norms.Elementwise

universe uE

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ∞ω}

private noncomputable def matrixDiagonalCLM :
    (ι → 𝕜) →L[𝕜] Matrix ι ι 𝕜 :=
  (Matrix.diagonalLinearMap ι 𝕜 𝕜).mkContinuous 1 fun v => by
    change ‖Matrix.diagonal v‖ ≤ 1 * ‖v‖
    rw [Matrix.norm_diagonal, one_mul]

private theorem matrixDiagonalCLM_apply (v : ι → 𝕜) :
    matrixDiagonalCLM (𝕜 := 𝕜) (ι := ι) v = Matrix.diagonal v := by
  rfl

/-- Pointwise smooth vector families give pointwise smooth diagonal matrix families. -/
@[fun_prop]
theorem contDiffAt_matrix_diagonal {f : E → ι → 𝕜} {x : E}
    (hf : ContDiffAt 𝕜 k f x) :
    ContDiffAt 𝕜 k (fun y ↦ Matrix.diagonal (f y)) x := by
  have hfun : (fun y ↦ Matrix.diagonal (f y)) =
      (matrixDiagonalCLM (𝕜 := 𝕜) (ι := ι)) ∘ f := by
    funext y
    exact (matrixDiagonalCLM_apply (𝕜 := 𝕜) (ι := ι) (f y)).symm
  rw [hfun]
  exact (matrixDiagonalCLM (𝕜 := 𝕜) (ι := ι)).contDiff.contDiffAt.comp x hf

/-- Globally smooth vector families give globally smooth diagonal matrix families. -/
@[fun_prop]
theorem contDiff_matrix_diagonal {f : E → ι → 𝕜}
    (hf : ContDiff 𝕜 k f) :
    ContDiff 𝕜 k (fun y ↦ Matrix.diagonal (f y)) := by
  have hfun : (fun y ↦ Matrix.diagonal (f y)) =
      (matrixDiagonalCLM (𝕜 := 𝕜) (ι := ι)) ∘ f := by
    funext y
    exact (matrixDiagonalCLM_apply (𝕜 := 𝕜) (ι := ι) (f y)).symm
  rw [hfun]
  exact (matrixDiagonalCLM (𝕜 := 𝕜) (ι := ι)).contDiff.comp hf
