/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_9

open TopologicalSpace
open scoped Manifold

universe u v

noncomputable section

/- Semantic recall:
- `lean_leansearch`: analytic identity-theorem hits around
  `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`.
- Verified locally: `RiemannSurface.Holomorphic`, `Set.EqOn`, and `AccPt`.
- Owner choice: keep the source-facing identity theorem with the accumulation-point hypothesis
  stated explicitly as `AccPt a (Filter.principal A)`, but expose it on the minimal connected
  complex-manifold layer and add the closure-form companion theorem used by downstream topology
  arguments.
-/

namespace RiemannSurface

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [ConnectedSpace X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type v} [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) ω Y]

/-- Theorem 1.11 (Identity Theorem): if two holomorphic maps between Riemann surfaces agree on a
set with an accumulation point, then they agree everywhere. The Lean statement only assumes the
connected complex-manifold structure actually used by the argument, so it applies in particular to
maps between Riemann surfaces. -/
theorem eq_of_holomorphic_of_eqOn_of_accPt {f₁ f₂ : X → Y} (hf₁ : Holomorphic f₁)
    (hf₂ : Holomorphic f₂) {A : Set X} (hA : Set.EqOn f₁ f₂ A) {a : X}
    (ha : AccPt a (Filter.principal A)) :
    f₁ = f₂ := sorry

/-- Theorem 1.11 in closure form: it is enough that the agreement set have a point of
`closure (A \ {a})`. -/
theorem eq_of_holomorphic_of_eqOn_of_mem_closure {f₁ f₂ : X → Y} (hf₁ : Holomorphic f₁)
    (hf₂ : Holomorphic f₂) {A : Set X} (hA : Set.EqOn f₁ f₂ A) {a : X}
    (ha : a ∈ closure (A \ {a})) :
    f₁ = f₂ := by
  apply eq_of_holomorphic_of_eqOn_of_accPt hf₁ hf₂ hA
  rw [accPt_iff_frequently_nhdsNE]
  exact mem_closure_ne_iff_frequently_within.mp ha

end RiemannSurface
