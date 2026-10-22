/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap18.Proposition_18_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section EkelandLebourgTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Theorem 18.3 concerns the source differentiability locus of `f`, namely the
  points `x ∈ cont f` where the finite-valued representative of `f` is Fréchet differentiable.
- `core/canonical`: the primitive Chapter 18 owner is
  `HasSymmetricSecondDifferenceBound f x ε`, with the sampled project declarations
  `cont f`, `HasSymmetricSecondDifferenceBound f x ε`,
  `symmetricSecondDifferenceSublevelSet f ε`, and
  `dense_isGδ_iInter_of_dense_open`.
- `bridge/view`: Proposition 18.1 identifies the source differentiability locus with the
  countable intersection of the open source sets `symmetricSecondDifferenceSublevelSet f ε`, and
  this theorem records that locus inside the complete metric subtype
  `closure (effectiveDomain f)`.
-/

-- Proof sketch: for each `ε > 0`, use Ekeland's variational principle with the barrier from the
-- proof to produce differentiability points in
-- `symmetricSecondDifferenceSublevelSet f ε` near any point of `cont f`. Proposition 18.2 makes
-- each `symmetricSecondDifferenceSublevelSet f ε` open, Proposition 18.1 identifies
-- `⋂ n, symmetricSecondDifferenceSublevelSet f ⟨1 / (n + 1), by positivity⟩` with the source
-- differentiability locus `{x | x ∈ cont f ∧ DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x}`,
-- and `hcont` gives nonempty interior of `effectiveDomain f`; convexity then yields
-- `closure (interior (effectiveDomain f)) = closure (effectiveDomain f)`. Baire category is then
-- the canonical Chapter 1 owner `dense_isGδ_iInter_of_dense_open` applied in the complete metric
-- subtype `closure (effectiveDomain f)`.
/-- Theorem 18.3: if a convex `]-∞,+∞]`-valued function on a real Hilbert space has a nonempty
continuity set `cont f`, then the points where its finite-valued representative is Fréchet
differentiable in the source sense `x ∈ cont f` form a dense `Gδ` subset of
`closure (effectiveDomain f)`. -/
theorem dense_isGδ_differentiableAt_toReal_in_closure_effectiveDomain_of_exists_continuityPoint
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    (hcont : (cont f).Nonempty) :
    Dense {x : closure (effectiveDomain f) |
      (x : H) ∈ cont f ∧ DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x} ∧
    IsGδ {x : closure (effectiveDomain f) |
      (x : H) ∈ cont f ∧ DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x} := sorry

end EkelandLebourgTheorem

end ERealFunction
