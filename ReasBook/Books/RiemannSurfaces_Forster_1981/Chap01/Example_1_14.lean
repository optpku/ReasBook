/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_9
import RiemannSurfaces_Forster_1981.Chap01.Definition_1_12
import RiemannSurfaces_Forster_1981.Chap01.Example_1_5
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Topology.Algebra.Polynomial

open scoped Manifold OnePoint
open TopologicalSpace

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `AnalyticOn.eval_polynomial`, `Polynomial.tendsto_norm_atTop`,
  `Polynomial.isProperMap_eval`.
- Verified locally: the chapter already models the Riemann sphere as `OnePoint ℂ`, uses the global
  owners `Holomorphic`, `MeromorphicOn`, and `𝓜(Y)`, and exposes
  `RiemannSurface (OnePoint ℂ)` in `Example_1_5`.
- Owner choice: keep the source polynomial as the canonical `Polynomial ℂ`, record the chosen
  finite value at `∞` as explicit data of the sphere-side extension, state holomorphicity on `ℂ`
  with `Holomorphic`, encode the growth-at-infinity clause with the cocompact filter on `ℂ`, and
  express the final conclusion primarily as `MeromorphicOn` on the top open subset of
  `OnePoint ℂ`, with `𝓜(Y)` membership as a companion surface.
-/

namespace RiemannSurface

/-- A complex polynomial viewed as a complex-valued function on the Riemann sphere after choosing a
finite value at `∞`. -/
def riemannSpherePolynomial (p : Polynomial ℂ) (a : ℂ) : OnePoint ℂ → ℂ :=
  fun x ↦ x.elim a (fun z : ℂ ↦ p.eval z)

/-- Evaluation of `riemannSpherePolynomial` at a finite point agrees with polynomial evaluation. -/
theorem riemannSpherePolynomial_coe (p : Polynomial ℂ) (a : ℂ) (z : ℂ) :
    riemannSpherePolynomial p a (z : OnePoint ℂ) = p.eval z := sorry

/-- Evaluation of `riemannSpherePolynomial` at `∞` is the chosen finite value. -/
theorem riemannSpherePolynomial_infty (p : Polynomial ℂ) (a : ℂ) :
    riemannSpherePolynomial p a (∞ : OnePoint ℂ) = a := sorry

/-- Example 1.14 (1): every complex polynomial, hence in particular every monic polynomial of
positive degree, defines a holomorphic map `ℂ → ℂ`. -/
theorem polynomial_holomorphic (p : Polynomial ℂ) :
    Holomorphic (fun z : ℂ ↦ p.eval z) := sorry

/-- Example 1.14 (2): when `ℂ` is viewed inside `ℙ¹(ℂ) = OnePoint ℂ`, the norm of a
positive-degree polynomial tends to `∞` along the cocompact filter on `ℂ`. -/
theorem polynomial_tendsto_norm_cocompactAtTop (p : Polynomial ℂ) (hp : 0 < p.degree) :
    Filter.Tendsto (fun z : ℂ ↦ ‖p.eval z‖) (Filter.cocompact ℂ) Filter.atTop := sorry

/-- Example 1.14 (3): after assigning any finite value at `∞`, the resulting function on
`ℙ¹(ℂ)` is meromorphic on the whole Riemann sphere. -/
theorem polynomial_meromorphicOn_riemannSphere (p : Polynomial ℂ) (a : ℂ) :
    MeromorphicOn (⊤ : Opens (OnePoint ℂ))
      (fun x : (⊤ : Opens (OnePoint ℂ)) ↦ riemannSpherePolynomial p a x) := sorry

/-- Example 1.14 (3), restated with the chapter's `𝓜(Y)` notation. -/
theorem polynomial_mem_meromorphicFunctions_riemannSphere (p : Polynomial ℂ) (a : ℂ) :
    (fun x : (⊤ : Opens (OnePoint ℂ)) ↦ riemannSpherePolynomial p a x) ∈
      𝓜((⊤ : Opens (OnePoint ℂ))) := by
  simpa [mem_meromorphicFunctions] using
    polynomial_meromorphicOn_riemannSphere p a

end RiemannSurface
