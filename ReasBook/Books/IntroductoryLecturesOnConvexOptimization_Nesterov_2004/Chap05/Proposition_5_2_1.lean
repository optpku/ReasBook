/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_24

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient NewtonDecrement

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 5.2.1 lies in the Chapter 5 self-concordant Newton local-convergence domain.

Sampled owner declarations:
* `HasPositiveDefiniteHessianOn` in `Definition_5_0_23`, the Chapter 5 owner for the
  positive-definite-Hessian regime used throughout the local-convergence theory;
* `NewtonDecrement.ofPosDefMem` in `Definition_5_0_24`, the Chapter 5 owner for evaluating the
  Newton
  decrement from ordinary domain membership in that regime;
* `NewtonDecrement.ofPosDefMem_def` in `Definition_5_0_24`, the canonical expansion of that owner
  into
  the inverse-Hessian pairing formula.

Best owner abstraction:
* source-facing: the intermediate Newton quadratic-convergence region;
* core/canonical: `NewtonDecrement.ofPosDefMem`;
* bridge/view: the region-membership theorem specialized at a point `x ∈ dom`.

Primitive data:
* a point `x ∈ dom`;
* a positive parameter `Mf`;
* the ambient owner assumption `HasPositiveDefiniteHessianOn dom f`.

Derived API:
* the Newton decrement `NewtonDecrement.ofPosDefMem f x hx`;
* the Hessian nondegeneracy supplied canonically from `HasPositiveDefiniteHessianOn dom f`;
* the inverse-Hessian pairing expansion from `NewtonDecrement.ofPosDefMem_def`.

This proposition remains source-facing as the quadratic-convergence region, but it no longer
packages Hessian witness bookkeeping into the public theorem surface: that data is already owned
canonically by the Chapter 5 Newton-decrement API, while self-concordance hypotheses belong only
to downstream convergence results that actually use them. -/

/-- Proposition 5.2.1: the region of quadratic convergence for the self-concordant Newton method
`(5.2.1) C` is the subset `𝒟_f = {x ∈ dom f | λ_f(x) < 1 / (2 M_f)}`. -/
def intermediateNewtonQuadraticConvergenceRegion
    (dom : Set E) (f : E → ℝ) (Mf : NNRealˣ)
    [HasPositiveDefiniteHessianOn dom f] : Set E :=
  {x | ∃ hx : x ∈ dom, λ[f; x | hx] < 1 / (2 * (Mf : ℝ))}

/-- Source-facing notation for the intermediate Newton quadratic-convergence region `𝒟_f`. -/
scoped[IntermediateNewtonQuadraticConvergenceRegion] notation:max "𝒟[" f " | " dom ", " Mf "]" =>
  intermediateNewtonQuadraticConvergenceRegion dom f Mf

open scoped IntermediateNewtonQuadraticConvergenceRegion

section

variable {dom : Set E} {f : E → ℝ} {Mf : NNRealˣ}
variable [HasPositiveDefiniteHessianOn dom f]

-- Proof sketch: unfold `intermediateNewtonQuadraticConvergenceRegion`; with `hx : x ∈ dom`
-- fixed as ordinary public data, membership is exactly the smallness inequality for the canonical
-- domain-level Newton decrement owner `NewtonDecrement.ofPosDefMem f x hx`.
/-- Any point of `𝒟[f | dom, Mf]` lies in `dom`. -/
theorem mem_dom_of_mem_intermediateNewtonQuadraticConvergenceRegion
    {x : E} (hxD : x ∈ 𝒟[f | dom, Mf]) : x ∈ dom := by
  rcases hxD with ⟨hx, _⟩
  exact hx

/-- For a fixed domain point `x ∈ dom`, membership in `𝒟[f | dom, Mf]` is equivalent to the
bound `λ_f(x) < 1 / (2 M_f)` expressed through the canonical domain-level owner
`NewtonDecrement.ofPosDefMem`. -/
theorem mem_intermediateNewtonQuadraticConvergenceRegion_iff
    {x : E} (hx : x ∈ dom) :
    x ∈ 𝒟[f | dom, Mf] ↔
      λ[f; x | hx] < 1 / (2 * (Mf : ℝ)) := by
  constructor
  · rintro ⟨hx', hDec⟩
    simpa using hDec
  · intro hDec
    exact ⟨hx, hDec⟩

end

end
