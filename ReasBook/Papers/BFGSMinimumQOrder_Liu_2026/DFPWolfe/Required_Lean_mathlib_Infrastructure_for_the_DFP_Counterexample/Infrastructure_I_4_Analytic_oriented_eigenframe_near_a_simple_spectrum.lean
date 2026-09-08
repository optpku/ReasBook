module

public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2.Eigenframe

public section

noncomputable section

open scoped Matrix

/- Infrastructure I.4 (Analytic oriented eigenframe near a simple spectrum) (1):
the explicit high eigenvector is the positively oriented perpendicular of the fixed low branch. -/
#check (RealSymmetric2.highVector_eq_perp_lowVector :
  ∀ a b d : ℝ,
    RealSymmetric2.highVector a b d =
      EuclideanPlane.perp (RealSymmetric2.lowVector a b d))

/- Infrastructure I.4 (Analytic oriented eigenframe near a simple spectrum) (2):
the entries of the positively oriented frame of the fixed low branch vary analytically on
`RealSymmetric2.lowChart`. -/
#check (RealSymmetric2.analyticOnNhd_frame :
    ∀ i j,
      AnalyticOnNhd ℝ
        (fun p : ℝ × ℝ × ℝ ↦
          EuclideanPlane.frame (RealSymmetric2.lowVector p.1 p.2.1 p.2.2) i j)
        RealSymmetric2.lowChart)

/- Infrastructure I.4 (Analytic oriented eigenframe near a simple spectrum) (3):
on `lowChart`, the analytic eigenframe is special orthogonal. -/
#check (RealSymmetric2.frame_mem_specialOrthogonalGroup :
  ∀ a b d : ℝ, a < d →
    EuclideanPlane.frame (RealSymmetric2.lowVector a b d) ∈
      Matrix.specialOrthogonalGroup (Fin 2) ℝ)

/- Infrastructure I.4 (Analytic oriented eigenframe near a simple spectrum) (4):
a positive base-point pairing with an analytic vector field persists on a positive-radius
ball, using the same fixed analytic low-eigenvector branch throughout. -/
#check (RealSymmetric2.exists_ball_inner_lowVector_pos :
  ∀ (g : (ℝ × ℝ × ℝ) → EuclideanSpace ℝ (Fin 2)),
    AnalyticAt ℝ g (0, 0, 1) →
    0 < inner ℝ (RealSymmetric2.lowVector 0 0 1) (g (0, 0, 1)) →
    ∃ r > 0,
      AnalyticOnNhd ℝ g (Metric.ball (0, 0, 1) r) ∧
        Metric.ball (0, 0, 1) r ⊆
          RealSymmetric2.lowChart ∩
            {p | 0 < inner ℝ (RealSymmetric2.lowVector p.1 p.2.1 p.2.2) (g p)})

/- At `RealSymmetric2.matrix 0 0 1`, the positively oriented eigenframe is the identity
matrix. -/
#check (RealSymmetric2.frame_diag :
  EuclideanPlane.frame (RealSymmetric2.lowVector 0 0 1) = 1)

/- Conjugation by the positively oriented eigenframe diagonalizes the symmetric matrix. -/
#check (RealSymmetric2.frame_diagonalizes :
  ∀ a b d : ℝ, a < d →
    (EuclideanPlane.frame (RealSymmetric2.lowVector a b d)).transpose *
        RealSymmetric2.matrix a b d *
        EuclideanPlane.frame (RealSymmetric2.lowVector a b d) =
      Matrix.diagonal ![RealSymmetric2.low a b d, RealSymmetric2.high a b d])
