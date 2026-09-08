module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds

public section

noncomputable section

universe uE uF uG

variable {E : Type uE} {F : Type uF} {G : Type uG}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Precomposition by the affine map `x ↦ A x + b` multiplies the pointwise norm of
the `n`-th iterated Fréchet derivative by at most `‖A‖ ^ n`. -/
theorem norm_iteratedFDeriv_comp_affine_le (n : ℕ) (f : F → G) (A : E →L[ℝ] F)
    (b : F) (hf : ContDiff ℝ n f) (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ f (A y + b)) x‖ ≤
      ‖iteratedFDeriv ℝ n f (A x + b)‖ * ‖A‖ ^ n := by
  have hfb : ContDiff ℝ n (fun z : F ↦ f (z + b)) :=
    hf.comp (contDiff_id.add contDiff_const)
  have hn : (n : WithTop ℕ∞) ≤ n := le_rfl
  have hcomp : (fun y ↦ f (A y + b)) = (fun z ↦ f (z + b)) ∘ A := rfl
  rw [hcomp, A.iteratedFDeriv_comp_right hfb x hn,
    iteratedFDeriv_comp_add_right]
  simpa using
    (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ n f (A x + b)) (fun _ ↦ A))

/-- Precomposition by the affine map `x ↦ A x + b` multiplies the pointwise norm of
the first iterated Fréchet derivative by at most `‖A‖`. -/
theorem norm_iteratedFDeriv_one_comp_affine_le (f : F → G) (A : E →L[ℝ] F)
    (b : F) (hf : ContDiff ℝ 1 f) (x : E) :
    ‖iteratedFDeriv ℝ 1 (fun y ↦ f (A y + b)) x‖ ≤
      ‖iteratedFDeriv ℝ 1 f (A x + b)‖ * ‖A‖ := by
  simpa using norm_iteratedFDeriv_comp_affine_le 1 f A b hf x

/-- Precomposition by the affine map `x ↦ A x + b` multiplies the pointwise norm of
the second iterated Fréchet derivative by at most `‖A‖ ^ 2`. -/
theorem norm_iteratedFDeriv_two_comp_affine_le (f : F → G) (A : E →L[ℝ] F)
    (b : F) (hf : ContDiff ℝ 2 f) (x : E) :
    ‖iteratedFDeriv ℝ 2 (fun y ↦ f (A y + b)) x‖ ≤
      ‖iteratedFDeriv ℝ 2 f (A x + b)‖ * ‖A‖ ^ 2 := by
  exact norm_iteratedFDeriv_comp_affine_le 2 f A b hf x
