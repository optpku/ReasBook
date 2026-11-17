/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f0dee1064101ffc85a871f8c7f3a997668f5a83b:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import DFPWolfe.V21.PlanarConvergence

/-!
Latest manuscript Theorem 13 (`thm:planar-convergence`). The mathematical statement
and corrected-log proof are unchanged from the completed v21 proof. The source
initial Hessian, neighborhood regularity and complete weak-Wolfe parameter range
are retained. Finite termination is represented by constant continuation.
-/

public section

open Filter
open scoped Topology

namespace DFPWolfe.Latest

/-- thm:planar-convergence. In two dimensions, classical DFP under fixed weak
Wolfe conditions converges to the unique minimizer when the Hessian has a positive
global lower bound and is locally Lipschitz near the initial level set. The
conclusion explicitly distinguishes finite stopping and a nonstationary infinite
trajectory. The reused proof uses the source secant coefficient and corrected-log
cancellation with square-summable steps. -/
theorem planarConvergenceCases
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hH₀ : (H 0).PosDef)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k))
    (hNeighborhood : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧
      {z | f z ≤ f (x 0)} ⊆ U ∧ LocallyLipschitzOn U (fderiv ℝ (gradient f))) :
    ∃ xstar, (∀ z, f xstar ≤ f z) ∧ (∀ y, (∀ z, f y ≤ f z) → y = xstar) ∧
      ((∃ K : ℕ, gradient f (x K) = 0 ∧ x K = xstar ∧ ∀ k, K ≤ k → x k = xstar) ∨
        ((∀ k, gradient f (x k) ≠ 0) ∧ Tendsto x atTop (𝓝 xstar) ∧
          Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0))) := by
  exact DFPWolfe.V21.planarConvergenceCases orbit hf hμ hHessian hH₀ hWolfe hNeighborhood

end DFPWolfe.Latest
