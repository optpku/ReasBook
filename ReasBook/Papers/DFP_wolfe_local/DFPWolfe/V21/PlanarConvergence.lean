/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.PlanarConvergence
public import ReasLib.Optimization.DFP.StrongWolfeCounterexample

/-!
The v21 planar convergence proof controls the free secant coefficient λ. Under
nonconvergence it tends to zero, while the corrected logarithm has absolutely summable
increments of order `‖sₖ‖² + ‖sₖ₊₁‖²`. Its finite limit forces a positive lower bound
for λ, a contradiction. The reused proof has the same cancellation and a coherent
one-index shift of the source invariant; it requires only square-summable steps.

`DFP.IsOrbit` is a total algebraic trajectory with certified gradients, positive step
lengths, the search equation, and the inverse DFP recurrence. A stationary hit is modeled
by its constant point continuation. The explicit cases theorem distinguishes this
finite stopping case from an everywhere nonstationary infinite sequence. Every global
minimizer is identified with the limit. The Wolfe predicates themselves include the
full fixed range `0<c₁<c₂<1`. Only the initial matrix is assumed positive definite.
-/

public section

open Filter
open scoped Topology

namespace DFPWolfe.V21

/-- Helper for thm:planar-convergence: uniqueness of a convergent minimizing
point includes every global minimizer, independently of any limit property. -/
private theorem limitWithUniqueMinimizer
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {x : ℕ → EuclideanSpace ℝ (Fin 2)} {μ : ℝ}
    (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hraw : ∃! xstar, (∀ z, f xstar ≤ f z) ∧ Tendsto x atTop (𝓝 xstar) ∧
      Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0)) :
    ∃ xstar, (∀ z, f xstar ≤ f z) ∧
      (∀ y, (∀ z, f y ≤ f z) → y = xstar) ∧ Tendsto x atTop (𝓝 xstar) ∧
        Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0) := by
  obtain ⟨xstar, hresult, _⟩ := hraw
  obtain ⟨zstar, _, hunique⟩ :=
    DFP.PlanarConvergence.existsUniqueGlobalMinimizerOfHessian hf hμ hHessian
  refine ⟨xstar, hresult.1, ?_, hresult.2⟩
  intro y hy
  exact (hunique y hy).trans (hunique xstar hresult.1).symm

/-- Helper for thm:planar-convergence: a stationary hit is already the unique
global minimizer, and the total algebraic point continuation is constant thereafter. -/
theorem planarStationaryTail
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {μ : ℝ}
    (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    {K : ℕ} (hHit : gradient f (x K) = 0) :
    (∀ z, f (x K) ≤ f z) ∧
      (∀ y, (∀ z, f y ≤ f z) → y = x K) ∧
        ∀ k, K ≤ k → x k = x K := by
  have hg : g K = 0 := (orbit.gradientAt K).gradient.symm.trans hHit
  have hmin := DFP.PlanarConvergence.stationaryPointMinimizes hf hμ hHessian hHit
  obtain ⟨xstar, _, hunique⟩ :=
    DFP.PlanarConvergence.existsUniqueGlobalMinimizerOfHessian hf hμ hHessian
  refine ⟨hmin, ?_, ?_⟩
  · intro y hy
    exact (hunique y hy).trans (hunique (x K) hmin).symm
  · intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    exact DFP.PlanarConvergence.rawOrbitStationaryTail orbit hg j

/-- thm:planar-convergence. For arbitrary planar initial data with `H₀≻0`, a
globally positive Hessian lower bound and weak Wolfe in the full range `0<c₁<c₂<1`
give convergence to the unique global minimizer when the Hessian is locally Lipschitz
on an open neighborhood of the initial level set. Both point convergence and
gradient-norm convergence to zero are included. Uniqueness identifies every global
minimizer, not only points satisfying a convergence predicate.

The input is the total `IsOrbit` encoding. A stationary hit has the constant
continuation proved in `planarStationaryTail`; `planarConvergenceCases` exposes the
finite stopping versus nonstationary infinite branches explicitly. Later matrix
positivity and the corrected-log contradiction are derived by the source proof. -/
theorem planarConvergence
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hH₀ : (H 0).PosDef)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k))
    (hNeighborhood : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧
      {z | f z ≤ f (x 0)} ⊆ U ∧ LocallyLipschitzOn U (fderiv ℝ (gradient f))) :
    ∃ xstar, (∀ z, f xstar ≤ f z) ∧
      (∀ y, (∀ z, f y ≤ f z) → y = xstar) ∧ Tendsto x atTop (𝓝 xstar) ∧
        Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0) := by
  exact limitWithUniqueMinimizer hf hμ hHessian
    (DFP.PlanarConvergence.rawOrbitConvergenceOfNeighborhood
      orbit hf hμ hHessian hH₀ hWolfe hNeighborhood)

/-- Helper for thm:planar-convergence: either a stationary iterate reaches the
unique minimizer in finitely many steps and its point tail is constant, or all
iterates are nonstationary and the infinite sequence converges with gradient norm zero. -/
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
  classical
  obtain ⟨xstar, hmin, hunique, hpoint, hgradient⟩ :=
    planarConvergence orbit hf hμ hHessian hH₀ hWolfe hNeighborhood
  refine ⟨xstar, hmin, hunique, ?_⟩
  by_cases hhit : ∃ K, gradient f (x K) = 0
  · obtain ⟨K, hHit⟩ := hhit
    have htail := planarStationaryTail orbit hf hμ hHessian hHit
    have hK : x K = xstar := hunique (x K) htail.1
    left
    exact ⟨K, hHit, hK, fun k hk ↦ (htail.2.2 k hk).trans hK⟩
  · right
    refine ⟨?_, hpoint, hgradient⟩
    intro k hk
    exact hhit ⟨k, hk⟩

/-- Helper for thm:planar-convergence: strong Wolfe gives the same full-range
planar conclusion. The necessary nonascending pairing follows from Armijo and
the global Hessian lower bound, including stationary constant continuations. -/
theorem planarStrongWolfeConvergence
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 2 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hH₀ : (H 0).PosDef)
    (hWolfe : ∀ k, LineSearch.IsStrongWolfe c₁ c₂ f (x k) (x (k + 1) - x k))
    (hNeighborhood : ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧
      {z | f z ≤ f (x 0)} ⊆ U ∧ LocallyLipschitzOn U (fderiv ℝ (gradient f))) :
    ∃ xstar, (∀ z, f xstar ≤ f z) ∧
      (∀ y, (∀ z, f y ≤ f z) → y = xstar) ∧ Tendsto x atTop (𝓝 xstar) ∧
        Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0) := by
  have hWeak (k : ℕ) : LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k) := by
    apply (hWolfe k).toWeakWolfe
    exact DFP.PlanarConvergence.armijoDescentOfHessianLowerBound hf hμ hHessian
      ((hWolfe k).c₁_lt_c₂.trans (hWolfe k).c₂_lt_one) (hWolfe k).armijo
  exact planarConvergence orbit hf hμ hHessian hH₀ hWeak hNeighborhood

/-- Helper for thm:planar-convergence: C³ regularity supplies local Lipschitz
Hessian regularity through the reviewed raw-orbit theorem, without assuming a
uniform global Lipschitz constant. The minimizer is unique among all minimizers. -/
theorem planarConvergenceOfC3
    {f : EuclideanSpace ℝ (Fin 2) → ℝ} {α : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ (Fin 2)} {H : ℕ → Matrix (Fin 2) (Fin 2) ℝ}
    (orbit : DFP.IsOrbit f α x g H) {μ c₁ c₂ : ℝ}
    (hf : ContDiff ℝ 3 f) (hμ : 0 < μ)
    (hHessian : ∀ z v, μ * ‖v‖ ^ 2 ≤ inner ℝ (fderiv ℝ (gradient f) z v) v)
    (hH₀ : (H 0).PosDef)
    (hWolfe : ∀ k, LineSearch.IsWeakWolfe c₁ c₂ f (x k) (x (k + 1) - x k)) :
    ∃ xstar, (∀ z, f xstar ≤ f z) ∧
      (∀ y, (∀ z, f y ≤ f z) → y = xstar) ∧ Tendsto x atTop (𝓝 xstar) ∧
        Tendsto (fun k ↦ ‖gradient f (x k)‖) atTop (𝓝 0) := by
  have htwoThree : (2 : WithTop ℕ∞) ≤ 3 := by norm_num
  exact limitWithUniqueMinimizer (hf.of_le htwoThree) hμ hHessian
    (DFP.PlanarConvergence.rawOrbitConvergenceOfC3 orbit hf hμ hHessian hH₀ hWolfe)

end DFPWolfe.V21
