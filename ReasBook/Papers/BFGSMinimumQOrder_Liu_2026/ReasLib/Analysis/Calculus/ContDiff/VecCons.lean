module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Data.Fin.VecNotation

/-!
# Smoothness of vector cons

`Matrix.vecCons` is the constructor used by the `![...]` notation for finite vectors.  The
coordinatewise smoothness lemmas for Pi types imply the results below, but registering the
constructor directly lets `fun_prop` handle vector literals without unfolding them coordinate by
coordinate.
-/

public section

open scoped Nat ContDiff

universe uE uF

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ} {k : ℕ∞ω}

/-- Pointwise smoothness is preserved by prepending a coordinate to a finite vector. -/
@[fun_prop]
theorem contDiffAt_matrix_vecCons {f : E → F} {g : E → Fin n → F} {x : E}
    (hf : ContDiffAt 𝕜 k f x) (hg : ContDiffAt 𝕜 k g x) :
    ContDiffAt 𝕜 k (fun y => Matrix.vecCons (f y) (g y)) x := by
  rw [contDiffAt_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hf
  · simpa using (contDiffAt_pi.mp hg j)

/-- Global smoothness is preserved by prepending a coordinate to a finite vector. -/
@[fun_prop]
theorem contDiff_matrix_vecCons {f : E → F} {g : E → Fin n → F}
    (hf : ContDiff 𝕜 k f) (hg : ContDiff 𝕜 k g) :
    ContDiff 𝕜 k (fun y => Matrix.vecCons (f y) (g y)) := by
  rw [contDiff_pi]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa using hf
  · simpa using (contDiff_pi.mp hg j)
