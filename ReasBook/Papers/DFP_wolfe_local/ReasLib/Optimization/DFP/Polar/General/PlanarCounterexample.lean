module

public import ReasLib.Optimization.DFP.Polar.General.Realization
public import ReasLib.Optimization.DFP.Polar.General.Transport
public import ReasLib.Optimization.DFP.LevelSetGlobalConvergence

public section

noncomputable section

open Filter
open scoped Matrix Topology

namespace DFP.Polar.General.PlanarCounterexample

/-- Helper for thm:main: the standard certificate stores precisely the source
objective, points, matrices, step lengths and gradients of the same construction. -/
structure SourceIdentity (p : Parameters) (κ : ℝ)
    (w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2) : Prop where
  /-- Helper for thm:main: the exact explicit cutoff objective. -/
  objective : w.iteration.objective = p.objective κ
  /-- Helper for thm:main: the exact source polar point sequence. -/
  point : w.iteration.point = p.point
  /-- Helper for thm:main: the exact positive source step lengths. -/
  stepLength : w.iteration.stepLength = p.stepLength
  /-- Helper for thm:main: the exact physical source inverse Hessian sequence. -/
  inverseHessian : w.iteration.inverseHessian = p.inverseHessian
  /-- Helper for thm:main: the exact canonical gradients are the source gradients. -/
  gradients : DFP.gradients w.iteration.objective w.iteration.point = p.gradients

/-- Helper for thm:main: package an actual source orbit with its proved
strong Wolfe laws, Hessian bounds and gradient limit in the canonical DFP
counterexample interface, retaining every source projection explicitly. -/
theorem existsSourceCertificate (p : Parameters) (κ : ℝ)
    (horbit : DFP.IsOrbit (p.objective κ) p.stepLength p.point p.gradients p.inverseHessian)
    (hpos : ∀ k, (p.inverseHessian k).PosDef)
    (hden : ∀ k,
      WithLp.ofLp (DFP.steps p.stepLength (DFP.directions p.inverseHessian p.gradients) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges p.gradients k) ≠ 0)
    (hC2 : ContDiff ℝ 2 (p.objective κ))
    (hBounds : HasHessianBounds (1 / 2) (3 / 2) (p.objective κ))
    (hWolfe : ∀ k, LineSearch.IsStrongWolfe p.c1 p.c2 (p.objective κ)
      (p.point k) (p.point (k + 1) - p.point k))
    (hLimit : Tendsto (fun k ↦ ‖p.gradients k‖) atTop (𝓝 1)) :
    ∃ w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2,
      SourceIdentity p κ w ∧ w.gradientLimit = 1 := by
  let it := horbit.toInverseIteration hpos hden
  have hobjective : it.objective = p.objective κ := horbit.toInverseIteration_objective hpos hden
  have hpoint : it.point = p.point := horbit.toInverseIteration_point_eq hpos hden
  have hstepLength : it.stepLength = p.stepLength := horbit.toInverseIteration_stepLength hpos hden
  have hmatrix : it.inverseHessian = p.inverseHessian :=
    horbit.toInverseIteration_inverseHessian_eq hpos hden
  have hgradients : DFP.gradients it.objective it.point = p.gradients := by
    rw [hobjective, hpoint]
    exact horbit.gradients_eq
  have hStep (k : ℕ) : 0 < it.stepLength k := by
    rw [hstepLength]
    exact horbit.stepLengthPos k
  have hStrong (k : ℕ) : LineSearch.IsStrongWolfe p.c1 p.c2 it.objective
      (it.point k) (it.point (k + 1) - it.point k) := by
    simpa only [hobjective, hpoint] using hWolfe k
  have hWeak (k : ℕ) : LineSearch.IsWeakWolfe p.c1 p.c2 it.objective
      (it.point k) (it.point (k + 1) - it.point k) := by
    apply (hStrong k).toWeakWolfe
    simpa only [DFP.gradients_apply] using (it.gradientInnerDisplacementNeg k (hStep k)).le
  have hContDiff : ContDiff ℝ 2 it.objective := by
    rwa [hobjective]
  have hHessian : HasHessianBounds (1 / 2) (3 / 2) it.objective := by
    rwa [hobjective]
  have hTendsto : Tendsto (fun k ↦ ‖DFP.gradients it.objective it.point k‖) atTop (𝓝 1) := by
    simpa only [hgradients] using hLimit
  let weak : DFP.WolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2 := {
    iteration := it
    gradientLimit := 1
    objectiveContDiff := hContDiff
    stepLengthPos := hStep
    hessianBounds := hHessian
    weakWolfe := hWeak
    gradientLimitPos := zero_lt_one
    gradientNormTendsto := hTendsto
  }
  let w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2 := {
    toWolfeCounterexample := weak
    strongWolfe := hStrong
  }
  have hw : w.iteration = it := rfl
  have hsource : SourceIdentity p κ w := by
    constructor
    · exact (congrArg DFP.InverseIteration.objective hw).trans hobjective
    · exact congrArg DFP.InverseIteration.point hw |>.trans hpoint
    · exact congrArg DFP.InverseIteration.stepLength hw |>.trans hstepLength
    · exact congrArg DFP.InverseIteration.inverseHessian hw |>.trans hmatrix
    · simpa only [hw] using hgradients
  have hgradientLimit : w.gradientLimit = 1 := rfl
  exact ⟨w, hsource, hgradientLimit⟩


/-- Helper for eq:counterexample-nonlipschitz: the canonical certificate's
secant-residual ratio is exactly the same source correction quotient. -/
theorem SourceIdentity.secantResidualRatio_eq {p : Parameters} {κ : ℝ}
    {w : DFP.StrongWolfeCounterexample (Fin 2) (1 / 2) (3 / 2) p.c1 p.c2}
    (hsource : SourceIdentity p κ w)
    (hGeometry : DFP.Polar.InterpolationSum.Geometry p.point (p.supportRadius κ) p.correction)
    (β' : ℝ) (j : ℕ) :
    DFP.Polar.OrthogonalExtension.secantResidualRatio w.iteration β' j =
      ‖p.correction (2 * j + 1)‖ / ‖p.point (2 * j + 1) - p.point (2 * j)‖ ^ (1 + β') := by
  have hresidual := HolderSharpness.gradientRemainder_objective_centers hGeometry
    (2 * j) (2 * j + 1) (p.correction_even j)
  rw [← p.objective_def κ, p.gradient_objective_center κ hGeometry,
    p.gradient_objective_center κ hGeometry] at hresidual
  rw [DFP.Polar.OrthogonalExtension.secantResidualRatio_apply, hsource.gradients,
    hsource.point, hsource.objective, hresidual]

end DFP.Polar.General.PlanarCounterexample
