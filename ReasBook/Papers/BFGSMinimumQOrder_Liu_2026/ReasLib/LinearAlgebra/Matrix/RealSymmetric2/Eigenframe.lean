module

public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2

public section

noncomputable section

namespace RealSymmetric2

open scoped Matrix Topology

/-- The first column of the canonical oriented frame is its defining vector. -/
private lemma frame_apply_zero (e : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    EuclideanPlane.frame e i 0 = e i := by
  -- Apply the frame to the first coordinate vector and read off coordinate `i`.
  have h := congrArg (fun v : Fin 2 → ℝ ↦ v i)
    (EuclideanPlane.frame_mulVec e 1 0)
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h

/-- The second column of the canonical oriented frame is the positive perpendicular. -/
private lemma frame_apply_one (e : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    EuclideanPlane.frame e i 1 = EuclideanPlane.perp e i := by
  -- Apply the frame to the second coordinate vector and read off coordinate `i`.
  have h := congrArg (fun v : Fin 2 → ℝ ↦ v i)
    (EuclideanPlane.frame_mulVec e 0 1)
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h

/-- The explicit high eigenvector is the positively oriented perpendicular of the fixed low
eigenvector branch. -/
theorem highVector_eq_perp_lowVector (a b d : ℝ) :
    highVector a b d = EuclideanPlane.perp (lowVector a b d) := by
  -- The public coordinate formulas for both sides are identical.
  rw [highVector_eq_coordinatePerp, EuclideanPlane.perp_apply]

/-- If the high eigenvalue is nonzero, the low eigenvalue is the determinant
divided by the high eigenvalue. -/
theorem low_eq_det_div_high_of_ne (a b d : ℝ) (hhigh : high a b d ≠ 0) :
    low a b d = (a * d - b ^ 2) / high a b d := by
  apply (eq_div_iff hhigh).2
  exact low_mul_high a b d

/-- Every entry of the positively oriented frame of the fixed low eigenvector branch is analytic
throughout `lowChart`. -/
theorem analyticOnNhd_frame :
    ∀ i j,
      AnalyticOnNhd ℝ
        (fun p : ℝ × ℝ × ℝ ↦ EuclideanPlane.frame (lowVector p.1 p.2.1 p.2.2) i j)
        lowChart := by
  -- Split by frame column, then compose the corresponding analytic vector field
  -- with a fixed coordinate projection.
  intro i j p hp
  have hproj : AnalyticAt ℝ (fun v : EuclideanSpace ℝ (Fin 2) ↦ v i)
      (lowVector p.1 p.2.1 p.2.2) :=
    (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).analyticAt _
  fin_cases j
  · apply (hproj.comp (f := fun q : ℝ × ℝ × ℝ ↦ lowVector q.1 q.2.1 q.2.2)
      (analyticOnNhd_lowVector p hp)).congr
    filter_upwards [] with q
    exact (frame_apply_zero _ i).symm
  · have hhighProj : AnalyticAt ℝ (fun v : EuclideanSpace ℝ (Fin 2) ↦ v i)
        (highVector p.1 p.2.1 p.2.2) :=
      (EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin 2) i).analyticAt _
    have hhigh := hhighProj.comp
      (f := fun q : ℝ × ℝ × ℝ ↦ highVector q.1 q.2.1 q.2.2)
      (analyticOnNhd_highVector p hp)
    apply hhigh.congr
    filter_upwards [] with q
    calc
      ((fun v : EuclideanSpace ℝ (Fin 2) ↦ v i) ∘
          fun x : ℝ × ℝ × ℝ ↦ highVector x.1 x.2.1 x.2.2) q =
          EuclideanPlane.perp (lowVector q.1 q.2.1 q.2.2) i := by
            exact congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v i)
              (highVector_eq_perp_lowVector q.1 q.2.1 q.2.2)
      _ = EuclideanPlane.frame (lowVector q.1 q.2.1 q.2.2) i 1 :=
        (frame_apply_one _ i).symm

/-- On `lowChart`, the frame of the fixed low eigenvector branch is special orthogonal. -/
theorem frame_mem_specialOrthogonalGroup (a b d : ℝ) (hchart : a < d) :
    EuclideanPlane.frame (lowVector a b d) ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  -- The canonical oriented frame is special orthogonal precisely when its first
  -- column has unit norm.
  rw [EuclideanPlane.frame_mem_specialOrthogonalGroup_iff]
  exact norm_lowVector a b d hchart

/-- A nonzero normalization denominator is enough for the fixed low-vector
branch to define a special orthogonal frame, without a separate chart
inequality. -/
theorem frame_mem_specialOrthogonalGroup_of_lowDenom_ne_zero
    (a b d : ℝ) (hdenom : lowDenom a b d ≠ 0) :
    EuclideanPlane.frame (lowVector a b d) ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ := by
  rw [EuclideanPlane.frame_mem_specialOrthogonalGroup_iff]
  have hdenomNonneg : 0 ≤ lowDenom a b d := lowDenom_nonneg a b d
  have hdenomPos : 0 < lowDenom a b d :=
    lt_of_le_of_ne hdenomNonneg (Ne.symm hdenom)
  have hraw : ‖lowRaw a b d‖ ≠ 0 := by
    rw [← lowDenom_eq_norm_lowRaw]
    exact hdenom
  rw [lowVector_apply, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos hdenomPos, lowDenom_eq_norm_lowRaw]
  exact inv_mul_cancel₀ hraw

/-- A positive base-point pairing with an analytic vector field persists on a positive-radius
ball, using the fixed analytic low-eigenvector branch throughout. -/
theorem exists_ball_inner_lowVector_pos
    (g : (ℝ × ℝ × ℝ) → EuclideanSpace ℝ (Fin 2))
    (hg : AnalyticAt ℝ g (0, 0, 1))
    (hpos : 0 < inner ℝ (lowVector 0 0 1) (g (0, 0, 1))) :
    ∃ r > 0,
      AnalyticOnNhd ℝ g (Metric.ball (0, 0, 1) r) ∧
        Metric.ball (0, 0, 1) r ⊆
          lowChart ∩ {p | 0 < inner ℝ (lowVector p.1 p.2.1 p.2.2) (g p)} := by
  -- Analyticity, chart membership, and positivity each hold eventually at the
  -- base point, so one sufficiently small metric ball satisfies all three.
  have hlowContinuous : ContinuousAt
      (fun p : ℝ × ℝ × ℝ ↦ lowVector p.1 p.2.1 p.2.2) (0, 0, 1) :=
    (analyticOnNhd_lowVector (0, 0, 1) diag_mem_lowChart).continuousAt
  have hinnerContinuous : ContinuousAt
      (fun p : ℝ × ℝ × ℝ ↦
        inner ℝ (lowVector p.1 p.2.1 p.2.2) (g p)) (0, 0, 1) :=
    hlowContinuous.inner hg.continuousAt
  have hpositive : ∀ᶠ p in 𝓝 ((0, 0, 1) : ℝ × ℝ × ℝ),
      0 < inner ℝ (lowVector p.1 p.2.1 p.2.2) (g p) :=
    hinnerContinuous.eventually (Ioi_mem_nhds hpos)
  have hchart : ∀ᶠ p in 𝓝 ((0, 0, 1) : ℝ × ℝ × ℝ), p ∈ lowChart :=
    isOpen_lowChart.mem_nhds diag_mem_lowChart
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (hg.eventually_analyticAt.and (hchart.and hpositive))
  refine ⟨r, hr, ?_, ?_⟩
  · -- The first component of the combined event gives analyticity on the ball.
    intro p hp
    exact (hball p hp).1
  · -- The remaining components give chart membership and strict positivity.
    intro p hp
    exact ⟨(hball p hp).2.1, (hball p hp).2.2⟩

/-- At `matrix 0 0 1`, the positively oriented eigenframe is the identity matrix. -/
theorem frame_diag :
    EuclideanPlane.frame (lowVector 0 0 1) = 1 := by
  -- At the base point the first column is the first standard basis vector and
  -- its positive perpendicular is the second.
  rw [lowVector_diag]
  ext i j
  fin_cases i <;> fin_cases j
  · simpa using frame_apply_zero (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) 0
  · calc
      EuclideanPlane.frame (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) 0 1 =
          EuclideanPlane.perp (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) 0 :=
        frame_apply_one _ _
      _ = 0 := by rw [EuclideanPlane.perp_apply]; simp
      _ = (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 1 := by simp
  · calc
      EuclideanPlane.frame (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) 1 0 =
          (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) 1 := frame_apply_zero _ _
      _ = 0 := by simp
      _ = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by simp
  · calc
      EuclideanPlane.frame (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) 1 1 =
          EuclideanPlane.perp (!₂[(1 : ℝ), 0] : EuclideanSpace ℝ (Fin 2)) 1 :=
        frame_apply_one _ _
      _ = 1 := by rw [EuclideanPlane.perp_apply]; simp
      _ = (1 : Matrix (Fin 2) (Fin 2) ℝ) 1 1 := by simp

/-- Multiplication by the symmetric matrix scales the two columns of its explicit eigenframe by
their corresponding eigenvalues. -/
private lemma matrixMulFrame_eq_frameMulDiagonal (a b d : ℝ) :
    matrix a b d * EuclideanPlane.frame (lowVector a b d) =
      EuclideanPlane.frame (lowVector a b d) *
        Matrix.diagonal ![low a b d, high a b d] := by
  -- Transport the two Euclidean eigen-equations to ordinary coordinate vectors.
  have hlow : matrix a b d *ᵥ WithLp.ofLp (lowVector a b d) =
      low a b d • WithLp.ofLp (lowVector a b d) := by
    simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul] using
      congrArg WithLp.ofLp (lowVector_eigen a b d)
  have hhigh : matrix a b d *ᵥ WithLp.ofLp (highVector a b d) =
      high a b d • WithLp.ofLp (highVector a b d) := by
    simpa only [Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_smul] using
      congrArg WithLp.ofLp (highVector_eigen a b d)
  -- Each frame column is one of those two eigenvectors.
  ext i j
  fin_cases j
  · have hcoord := congrArg (fun v : Fin 2 → ℝ ↦ v i) hlow
    calc
      (matrix a b d * EuclideanPlane.frame (lowVector a b d)) i 0 =
          (matrix a b d *ᵥ WithLp.ofLp (lowVector a b d)) i := by
            simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, frame_apply_zero]
      _ = (low a b d • WithLp.ofLp (lowVector a b d)) i := hcoord
      _ = (EuclideanPlane.frame (lowVector a b d) *
          Matrix.diagonal ![low a b d, high a b d]) i 0 := by
            rw [Matrix.mul_diagonal, frame_apply_zero]
            simp only [Pi.smul_apply, smul_eq_mul]
            exact mul_comm _ _
  · have hcoord := congrArg (fun v : Fin 2 → ℝ ↦ v i) hhigh
    simp only [highVector_eq_perp_lowVector] at hcoord
    calc
      (matrix a b d * EuclideanPlane.frame (lowVector a b d)) i 1 =
          (matrix a b d *ᵥ WithLp.ofLp
            (EuclideanPlane.perp (lowVector a b d))) i := by
              simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, frame_apply_one]
      _ = (high a b d • WithLp.ofLp
          (EuclideanPlane.perp (lowVector a b d))) i := hcoord
      _ = (EuclideanPlane.frame (lowVector a b d) *
          Matrix.diagonal ![low a b d, high a b d]) i 1 := by
            rw [Matrix.mul_diagonal, frame_apply_one]
            simp only [Pi.smul_apply, smul_eq_mul]
            exact mul_comm _ _

/-- Once the explicit eigenframe is known to be orthogonal, conjugation by it
diagonalizes the symmetric matrix. -/
theorem frame_diagonalizes_of_mem_orthogonalGroup (a b d : ℝ)
    (horthogonal : EuclideanPlane.frame (lowVector a b d) ∈
      Matrix.orthogonalGroup (Fin 2) ℝ) :
    (EuclideanPlane.frame (lowVector a b d)).transpose * matrix a b d *
        EuclideanPlane.frame (lowVector a b d) =
      Matrix.diagonal ![low a b d, high a b d] := by
  have hcancel : (EuclideanPlane.frame (lowVector a b d)).transpose *
      EuclideanPlane.frame (lowVector a b d) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin 2) ℝ).mp horthogonal
  calc
    (EuclideanPlane.frame (lowVector a b d)).transpose * matrix a b d *
        EuclideanPlane.frame (lowVector a b d) =
      (EuclideanPlane.frame (lowVector a b d)).transpose *
        (matrix a b d * EuclideanPlane.frame (lowVector a b d)) := by
          rw [Matrix.mul_assoc]
    _ = (EuclideanPlane.frame (lowVector a b d)).transpose *
        (EuclideanPlane.frame (lowVector a b d) *
          Matrix.diagonal ![low a b d, high a b d]) := by
            rw [matrixMulFrame_eq_frameMulDiagonal]
    _ = ((EuclideanPlane.frame (lowVector a b d)).transpose *
        EuclideanPlane.frame (lowVector a b d)) *
          Matrix.diagonal ![low a b d, high a b d] := by
            rw [Matrix.mul_assoc]
    _ = Matrix.diagonal ![low a b d, high a b d] := by
      rw [hcancel, Matrix.one_mul]

/-- Once the explicit eigenframe is known to be orthogonal, conjugating its
spectral diagonal back reconstructs the symmetric matrix. -/
theorem frame_reconstructs_of_mem_orthogonalGroup (a b d : ℝ)
    (horthogonal : EuclideanPlane.frame (lowVector a b d) ∈
      Matrix.orthogonalGroup (Fin 2) ℝ) :
    EuclideanPlane.frame (lowVector a b d) *
          Matrix.diagonal ![low a b d, high a b d] *
        (EuclideanPlane.frame (lowVector a b d)).transpose =
      matrix a b d := by
  let F := EuclideanPlane.frame (lowVector a b d)
  let A := matrix a b d
  let D := Matrix.diagonal ![low a b d, high a b d]
  have hcancel : F * F.transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin 2) ℝ).mp horthogonal
  have hdiagonal : F.transpose * A * F = D :=
    frame_diagonalizes_of_mem_orthogonalGroup a b d horthogonal
  change F * D * F.transpose = A
  calc
    F * D * F.transpose = F * (F.transpose * A * F) * F.transpose := by
      rw [hdiagonal]
    _ = (F * F.transpose) * A * (F * F.transpose) := by
      simp only [Matrix.mul_assoc]
    _ = A := by
      rw [hcancel, Matrix.one_mul, Matrix.mul_one]

/-- Conjugation by the positively oriented eigenframe diagonalizes the symmetric matrix. -/
theorem frame_diagonalizes (a b d : ℝ) (hchart : a < d) :
    (EuclideanPlane.frame (lowVector a b d)).transpose * matrix a b d *
        EuclideanPlane.frame (lowVector a b d) =
      Matrix.diagonal ![low a b d, high a b d] := by
  exact frame_diagonalizes_of_mem_orthogonalGroup a b d
    (Matrix.mem_specialOrthogonalGroup_iff.mp
      (frame_mem_specialOrthogonalGroup a b d hchart)).1

/-- A nonzero normalization denominator is sufficient for the fixed oriented
eigenframe to diagonalize the symmetric matrix; no separate chart inequality
is needed. -/
theorem frame_diagonalizes_of_lowDenom_ne_zero
    (a b d : ℝ) (hdenom : lowDenom a b d ≠ 0) :
    (EuclideanPlane.frame (lowVector a b d)).transpose * matrix a b d *
        EuclideanPlane.frame (lowVector a b d) =
      Matrix.diagonal ![low a b d, high a b d] := by
  exact frame_diagonalizes_of_mem_orthogonalGroup a b d
    (Matrix.mem_specialOrthogonalGroup_iff.mp
      (frame_mem_specialOrthogonalGroup_of_lowDenom_ne_zero
        a b d hdenom)).1

/-- A nonzero normalization denominator also gives the reverse spectral
reconstruction of the symmetric matrix. -/
theorem frame_reconstructs_of_lowDenom_ne_zero
    (a b d : ℝ) (hdenom : lowDenom a b d ≠ 0) :
    EuclideanPlane.frame (lowVector a b d) *
          Matrix.diagonal ![low a b d, high a b d] *
        (EuclideanPlane.frame (lowVector a b d)).transpose =
      matrix a b d := by
  exact frame_reconstructs_of_mem_orthogonalGroup a b d
    (Matrix.mem_specialOrthogonalGroup_iff.mp
      (frame_mem_specialOrthogonalGroup_of_lowDenom_ne_zero
        a b d hdenom)).1

end RealSymmetric2
