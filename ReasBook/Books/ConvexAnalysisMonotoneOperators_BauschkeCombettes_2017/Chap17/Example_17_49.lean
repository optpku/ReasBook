/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Source/core/bridge triage:
- `source-facing`: Example 17.49 records regularity properties of the quadratic
  `x ↦ (f x) ^ 2` attached to a real linear functional.
- `core/canonical`: the owner abstractions are `ConvexOn`, `ERealFunction.effectiveDomain`,
  `_root_.GateauxDifferentiableAt`, `LowerSemicontinuousAt`, `ContinuousAt`, and
  `DifferentiableAt`.
- `bridge/view`: the canonical bridge `Function.toEReal` moves the real-valued quadratic to the
  extended-real domain and lower-semicontinuity owners.

Primitive data: a bare linear functional `f : H →ₗ[ℝ] ℝ`.
Derived API: convexity, full `EReal` domain, Gâteaux differentiability at `0`,
lower semicontinuity at `0`, and failure of continuity/differentiability when `f` is
discontinuous. -/

section Algebraic

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]

-- Proof sketch: apply the canonical scalar owner `Even.convexOn_pow` to `t ↦ t ^ 2` on `ℝ`, then
-- compose with the linear owner `f` via `ConvexOn.comp_linearMap`.
/-- Example 17.49 (1): if `g = f^2` for a real linear functional `f`, then `g` is convex on the
whole space. -/
theorem convexOn_univ_sq_linearForm (f : H →ₗ[ℝ] ℝ) :
    ConvexOn ℝ (Set.univ : Set H) (fun x : H ↦ (f x) ^ 2) := sorry

-- Proof sketch: a real-valued function never takes the value `+∞`, so the canonical bridge
-- `(fun x ↦ (f x)^2).toEReal` is finite at every point of `H`.
/-- Example 17.49 (2): after coercion to `]-∞,+∞]`, the square `g = f^2` has full domain. -/
theorem effectiveDomain_sq_linearForm_toEReal_eq_univ (f : H →ₗ[ℝ] ℝ) :
    ERealFunction.effectiveDomain ((fun x : H ↦ (f x) ^ 2).toEReal) = (Set.univ : Set H) := sorry

end Algebraic

section Gateaux

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: along every line through the origin, the restriction of `x ↦ (f x)^2` is the
-- scalar quadratic `t ↦ (t * f y)^2`, whose derivative at `0` is `0`.
/-- Example 17.49 (3): the square `g = f^2` is Gâteaux differentiable at `0`. -/
theorem gateauxDifferentiableAt_sq_linearForm_zero (f : H →ₗ[ℝ] ℝ) :
    GateauxDifferentiableAt (fun x : H ↦ (f x) ^ 2) (0 : H) := sorry

end Gateaux

section LowerSemicontinuity

variable {H : Type u} [TopologicalSpace H] [AddCommMonoid H] [Module ℝ H]

-- Proof sketch: the canonical bridge `(fun x ↦ (f x)^2).toEReal` takes values in `[0, +∞)`, so
-- every lower threshold below `0` is satisfied on all sufficiently small neighborhoods of the
-- origin; equivalently, one can apply Proposition 17.48 using the previous convexity and
-- Gâteaux differentiability clauses.
/-- Example 17.49 (4): after coercion to `]-∞,+∞]`, the square `g = f^2` is lower
semicontinuous at `0`. -/
theorem lowerSemicontinuousAt_sq_linearForm_toEReal_zero (f : H →ₗ[ℝ] ℝ) :
    LowerSemicontinuousAt ((fun x : H ↦ (f x) ^ 2).toEReal) (0 : H) := sorry

end LowerSemicontinuity

section Normed

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: if `x ↦ (f x)^2` were continuous at `0`, then some neighborhood of `0` would make
-- `|f x|^2` uniformly small, hence `|f x|` uniformly bounded. A linear map that is bounded on a
-- neighborhood of `0` is continuous, contradicting the hypothesis.
/-- Example 17.49 (5): if `f` is discontinuous, then `g = f^2` is not continuous at `0`. -/
theorem not_continuousAt_sq_linearForm_zero_of_not_continuous (f : H →ₗ[ℝ] ℝ)
    (hfdisc : ¬ Continuous f) :
    ¬ ContinuousAt (fun x : H ↦ (f x) ^ 2) (0 : H) := sorry

-- Proof sketch: Fréchet differentiability at a point implies continuity there. Apply this to
-- `g = f^2` and use the previous clause to rule out continuity at the origin.
/-- Example 17.49 (6): if `f` is discontinuous, then `g = f^2` is not Fréchet differentiable at
`0`. -/
theorem not_differentiableAt_sq_linearForm_zero_of_not_continuous (f : H →ₗ[ℝ] ℝ)
    (hfdisc : ¬ Continuous f) :
    ¬ DifferentiableAt ℝ (fun x : H ↦ (f x) ^ 2) (0 : H) := sorry

end Normed
