module

public import ReasLib.Optimization.DFP.Polar.Recurrence

/- Compatibility surface for source-facing consumers of the promoted polar recurrence. -/
#check (DFP.Polar.Parameters : Type)
#check (DFP.Polar.baseAngle : ℝ)
#check (DFP.Polar.Parameters.matrix_succ :
  ∀ (p : DFP.Polar.Parameters) (k : ℕ),
    DFP.Polar.Parameters.matrix p (k + 1) =
      DFP.Polar.matrixStep (DFP.Polar.Parameters.matrix p k)
        (DFP.Polar.Parameters.angleIncrement p k)
        (DFP.Polar.Parameters.zeta p k) (DFP.Polar.Parameters.zeta p (k + 1)))
