module

public import DFPWolfe.V21.SecantDegeneration

/-!
Latest manuscript Lemma 12 (`lem:planar-degeneration`). The general secant argument
is unchanged. It uses positive definite search matrices and their secant equation,
without a DFP update or a Lipschitz Hessian assumption.
-/

public section

open Filter
open DFP.PlanarConvergence.SecantDegeneration
open scoped Topology ContDiff

namespace DFPWolfe.Latest

/-- lem:planar-degeneration. For a nonconvergent planar secant iteration, the
free coefficient `λₖ=κₖ₋₁ det Hₖ` has an eventual bound by a constant times
`‖sₖ₋₁‖‖sₖ‖` and tends to zero. `DegenerationEstimates` also bounds the search
matrices and proves that their smallest eigenvalues tend to zero. The source
secant representation and energy absorption argument are retained. -/
theorem planarDegeneration (iteration : DFP.SecantIteration 2) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 iteration.objective)
    (hstrong : StrongConvexOn Set.univ μ iteration.objective)
    (hμ : 0 < μ) (hStep : ∀ k, 0 < iteration.stepLength k)
    (hw : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ iteration.objective
      (iteration.point k) (iteration.point (k + 1) - iteration.point k)) :
    ∃! xstar : EuclideanSpace ℝ (Fin 2),
      (∀ z, iteration.objective xstar ≤ iteration.objective z) ∧
        (¬ Tendsto iteration.point atTop (𝓝 xstar) → DegenerationEstimates iteration) := by
  exact DFPWolfe.V21.planarDegeneration iteration hf hstrong hμ hStep hw

end DFPWolfe.Latest
