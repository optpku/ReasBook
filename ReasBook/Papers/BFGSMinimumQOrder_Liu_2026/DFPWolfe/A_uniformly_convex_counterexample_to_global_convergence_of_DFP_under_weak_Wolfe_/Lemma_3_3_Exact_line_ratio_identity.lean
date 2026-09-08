module

public import ReasLib.Optimization.DFP.AbstractSecantStep

universe u

/- Lemma 3.3 (Exact line-ratio identity): for
`q = z.predictedDecrease = -(z.gradient ⬝ᵥ z.displacement)` and
`t = z.secantCurvature = z.displacement ⬝ᵥ z.gradientChange`, the abstract
secant step has `t / q = z.tau`. -/
#check (DFP.AbstractSecantStep.lineRatio :
  ∀ {n : Type u} [Fintype n] (z : DFP.AbstractSecantStep n),
    z.secantCurvature / z.predictedDecrease = z.tau)
