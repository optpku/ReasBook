/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54

universe u v w

variable {H : Type u} {G : Type v} {K : Type w}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup G] [NormedSpace ℝ G]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

-- Proof sketch: compose the one-sided line derivatives from
-- `HasGateauxDerivativeWithinAt` with the Fréchet derivative of `R`; the additional Fréchet
-- conclusion is the standard composition theorem `HasFDerivAt.comp`.
/-- If `R` has Fréchet derivative `B` at `T x` and `T` has Gâteaux derivative `A` within `U`
at `x`, then `R ∘ T` has Gâteaux derivative `B.comp A` within `U` at `x`. -/
theorem HasFDerivAt.comp_hasGateauxDerivativeWithinAt
    {U : Set H} {x : H} {T : H → G} {R : G → K}
    {A : H →L[ℝ] G} {B : G →L[ℝ] K}
    (hR : HasFDerivAt R B (T x))
    (hTg : HasGateauxDerivativeWithinAt T A U x) :
    HasGateauxDerivativeWithinAt (R ∘ T) (B.comp A) U x := by
  rcases hTg with ⟨hSegments, hdir⟩
  refine ⟨hSegments, ?_⟩
  intro y
  let path : ℝ → G := fun α ↦ T (x + α • y)
  have hpath : HasDerivWithinAt path (A y) (Set.Ioi 0) 0 := hdir y
  have hRpath : HasFDerivAt R B (path 0) := by
    simpa [path] using hR
  simpa [path, Function.comp, ContinuousLinearMap.comp_apply] using
    hRpath.comp_hasDerivWithinAt 0 hpath

/-- Fact 2.63: if `R` has Fréchet derivative `B` at `T x` and `T` has Gâteaux derivative `A`
within `U` at `x`, then `R ∘ T` has Gâteaux derivative `B.comp A` within `U` at `x`; moreover,
if `T` is Fréchet differentiable at `x` with derivative `A`, then `R ∘ T` is Fréchet
differentiable at `x` with derivative `B.comp A`. -/
theorem hasGateauxDerivativeWithinAt_and_hasFDerivAt_comp
    {U : Set H} {x : H} {T : H → G} {R : G → K}
    {A : H →L[ℝ] G} {B : G →L[ℝ] K}
    (hR : HasFDerivAt R B (T x))
    (hTg : HasGateauxDerivativeWithinAt T A U x) :
    HasGateauxDerivativeWithinAt (R ∘ T) (B.comp A) U x ∧
      (HasFDerivAt T A x → HasFDerivAt (R ∘ T) (B.comp A) x) := by
  refine ⟨hR.comp_hasGateauxDerivativeWithinAt hTg, ?_⟩
  intro hT
  simpa [Function.comp] using hR.comp x hT
