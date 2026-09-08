module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.PosDef

public section

/-- The explicit coordinates and positive parameters of a canonical DFP cycle-boundary state. -/
structure CycleBoundaryState where
  e : EuclideanSpace ℝ (Fin 2)
  r : ℝ
  p : ℝ
  h : ℝ
  amplitude : ℝ
  e_norm : ‖e‖ = 1
  r_pos : 0 < r
  p_pos : 0 < p
  h_pos : 0 < h
  amplitude_pos : 0 < amplitude

namespace CycleBoundaryState

/-- Construct a canonical cycle-boundary state from its coordinates and positivity
certificates. -/
def ofParams (e : EuclideanSpace ℝ (Fin 2)) (r p h amplitude : ℝ) (e_norm : ‖e‖ = 1)
    (r_pos : 0 < r) (p_pos : 0 < p) (h_pos : 0 < h) (amplitude_pos : 0 < amplitude) :
    CycleBoundaryState where
  e := e
  r := r
  p := p
  h := h
  amplitude := amplitude
  e_norm := e_norm
  r_pos := r_pos
  p_pos := p_pos
  h_pos := h_pos
  amplitude_pos := amplitude_pos

/-- The positively oriented perpendicular direction `(-e₂, e₁)`. -/
def perp (s : CycleBoundaryState) : EuclideanSpace ℝ (Fin 2) :=
  !₂[-s.e 1, s.e 0]

/-- The matrix whose columns are `s.e` and `s.perp`. -/
def frame (s : CycleBoundaryState) : Matrix (Fin 2) (Fin 2) ℝ :=
  fun i ↦ ![s.e i, s.perp i]

/-- The inverse-Hessian matrix encoded by a canonical cycle-boundary state. -/
def metric (s : CycleBoundaryState) : Matrix (Fin 2) (Fin 2) ℝ :=
  s.frame * Matrix.diagonal ![s.h * s.p * s.r ^ 2, s.h] * s.frame.transpose

/-- The gradient vector encoded by a canonical cycle-boundary state. -/
noncomputable def gradient (s : CycleBoundaryState) : EuclideanSpace ℝ (Fin 2) :=
  s.amplitude •
    (Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
      (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) s.frame
        !₂[(1 : ℝ), s.p * s.r]

/-- The perpendicular direction has the prescribed coordinate formula. -/
theorem perp_eq (s : CycleBoundaryState) : s.perp = !₂[-s.e 1, s.e 0] := by
  -- Unfolding `perp` exposes exactly the displayed coordinate vector.
  rfl

/-- The first column of the frame is the unit direction. -/
theorem frame_col_zero (s : CycleBoundaryState) (i : Fin 2) : s.frame i 0 = s.e i := by
  -- Evaluating the first entry of each row selects the original direction.
  rfl

/-- The second column of the frame is the positively oriented perpendicular direction. -/
theorem frame_col_one (s : CycleBoundaryState) (i : Fin 2) : s.frame i 1 = s.perp i := by
  -- Evaluating the second entry of each row selects the perpendicular direction.
  rfl

/-- The frame is orthogonal and positively oriented. -/
theorem frame_mem_specialOrthogonalGroup (s : CycleBoundaryState) :
    s.frame ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  -- Reduce special-orthogonal membership to the oriented two-coordinate criterion.
  rw [Matrix.mem_specialOrthogonalGroup_fin_two_iff]
  have hnorm := EuclideanSpace.real_norm_sq_eq s.e
  rw [s.e_norm, one_pow, Fin.sum_univ_two] at hnorm
  -- The perpendicular formula supplies orientation, while `hnorm` supplies orthonormality.
  simp only [frame_col_zero, frame_col_one, perp_eq]
  simpa using hnorm.symm

/-- A positively oriented orthogonal frame is invertible. -/
private lemma frame_isUnit (s : CycleBoundaryState) : IsUnit s.frame := by
  -- Determinant one from special-orthogonal membership gives the matrix unit criterion.
  rw [Matrix.isUnit_iff_isUnit_det]
  have hdet := (Matrix.mem_specialOrthogonalGroup_iff.mp
    (frame_mem_specialOrthogonalGroup s)).2
  simp [hdet]

/-- The metric of a state built by `ofParams` has the displayed diagonal-frame form. -/
theorem ofParams_metric (e : EuclideanSpace ℝ (Fin 2)) (r p h amplitude : ℝ)
    (e_norm : ‖e‖ = 1) (r_pos : 0 < r) (p_pos : 0 < p) (h_pos : 0 < h)
    (amplitude_pos : 0 < amplitude) :
    let s := ofParams e r p h amplitude e_norm r_pos p_pos h_pos amplitude_pos
    s.metric = s.frame * Matrix.diagonal ![h * p * r ^ 2, h] * s.frame.transpose := by
  -- The parameters stored by `ofParams` reduce to the displayed inputs.
  rfl

/-- The gradient of a state built by `ofParams` has the displayed frame-coordinate form. -/
theorem ofParams_gradient (e : EuclideanSpace ℝ (Fin 2)) (r p h amplitude : ℝ)
    (e_norm : ‖e‖ = 1) (r_pos : 0 < r) (p_pos : 0 < p) (h_pos : 0 < h)
    (amplitude_pos : 0 < amplitude) :
    let s := ofParams e r p h amplitude e_norm r_pos p_pos h_pos amplitude_pos
    s.gradient = amplitude •
      (Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) s.frame
          !₂[(1 : ℝ), p * r] := by
  -- The parameters stored by `ofParams` reduce to the displayed inputs.
  rfl

/-- The two defining formulas for the metric and gradient of a canonical state. -/
theorem spec (s : CycleBoundaryState) :
    s.metric = s.frame * Matrix.diagonal ![s.h * s.p * s.r ^ 2, s.h] * s.frame.transpose ∧
      s.gradient = s.amplitude •
        (Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
          (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) s.frame
            !₂[(1 : ℝ), s.p * s.r] := by
  -- Each conjunct is exactly one of the defining formulas.
  constructor
  · rfl
  · rfl

/-- The diagonal metric weights of a canonical state form a positive definite matrix. -/
private lemma metricDiagonal_posDef (s : CycleBoundaryState) :
    (Matrix.diagonal ![s.h * s.p * s.r ^ 2, s.h] :
      Matrix (Fin 2) (Fin 2) ℝ).PosDef := by
  -- Positivity of each stored parameter makes both diagonal weights positive.
  apply Matrix.PosDef.diagonal
  intro i
  fin_cases i
  · dsimp
    exact mul_pos (mul_pos s.h_pos s.p_pos) (pow_pos s.r_pos 2)
  · dsimp
    exact s.h_pos

/-- The encoded inverse-Hessian matrix is positive definite. -/
theorem metric_posDef (s : CycleBoundaryState) : s.metric.PosDef := by
  -- Rewrite transpose as star and transport diagonal positivity through the invertible frame.
  unfold metric
  rw [← Matrix.conjTranspose_eq_transpose_of_trivial s.frame,
    ← Matrix.star_eq_conjTranspose]
  exact (Matrix.IsUnit.posDef_star_right_conjugate_iff (frame_isUnit s)).mpr
    (metricDiagonal_posDef s)

/-- The continuous linear action of a canonical frame is injective. -/
private lemma frameToEuclideanCLM_injective (s : CycleBoundaryState) :
    Function.Injective
      ((Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) s.frame) := by
  intro x y hxy
  -- Pass to ordinary coordinate functions and use injectivity of matrix multiplication.
  apply WithLp.ofLp_injective 2
  apply Matrix.mulVec_injective_of_isUnit (frame_isUnit s)
  simpa only [Matrix.ofLp_toEuclideanCLM] using
    congrArg (fun z : EuclideanSpace ℝ (Fin 2) ↦ z.ofLp) hxy

/-- The canonical gradient-coordinate vector is nonzero. -/
private lemma gradientCoordinates_ne_zero (s : CycleBoundaryState) :
    (!₂[(1 : ℝ), s.p * s.r] : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
  intro hzero
  -- Its zeroth coordinate is one, whereas the zero vector has zeroth coordinate zero.
  have hcoord := congrArg (fun x : EuclideanSpace ℝ (Fin 2) ↦ x 0) hzero
  norm_num at hcoord

/-- The encoded gradient is nonzero. -/
theorem gradient_ne_zero (s : CycleBoundaryState) : s.gradient ≠ 0 := by
  -- Injectivity of the frame action preserves the nonzero coordinate vector.
  have hframed :
      (Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))) s.frame
          !₂[(1 : ℝ), s.p * s.r] ≠ 0 := by
    intro hzero
    apply gradientCoordinates_ne_zero s
    apply frameToEuclideanCLM_injective s
    simpa using hzero
  -- Multiplication by the positive amplitude cannot annihilate that vector.
  unfold gradient
  exact smul_ne_zero s.amplitude_pos.ne' hframed

end CycleBoundaryState
