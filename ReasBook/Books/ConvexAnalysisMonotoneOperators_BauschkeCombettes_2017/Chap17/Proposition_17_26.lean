/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Corollary_11_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section RealNormedSpace

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: apply the uniform-convexity inequality from Definition 10.7 to the segment
-- `x + α • (y - x) = (1 - α) • x + α • y`, divide by `α`, and let `α ↓ 0` to identify the limit
-- with the directional derivative at `x` along `y - x`; if `y ∉ effectiveDomain f`, then the
-- right-hand side is `⊤`, so the inequality is immediate.
/-- Proposition 17.26 (1): if `f` is uniformly convex with modulus `φ`, then every
effective-domain base point satisfies the first-order lower bound
`f'(x; y - x) + φ(‖y - x‖) + f(x) ≤ f(y)` for every `y`. -/
theorem directionalDerivative_add_modulus_add_value_le_of_uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (huniform : UniformlyConvex f φ)
    {x y : H} (hx : x ∈ effectiveDomain f) :
    f′(x; y - x) + φ ‖y - x‖₊ + (f x : EReal) ≤ (f y : EReal) := sorry

-- Proof sketch: use Remark 16.2 to choose a subgradient `u ∈ ∂f(x)` at some effective-domain
-- point, combine Proposition 17.26 (1) with Proposition 17.14 and the positivity of the modulus
-- away from `0`, and then divide by `‖y‖` along `‖y‖ → +∞`.
/-- Proposition 17.26 (2): a uniformly convex member of `Γ₀(H)` is supercoercive. -/
theorem supercoercive_of_mem_gammaZero_of_uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : f ∈ Γ₀(H))
    (huniform : UniformlyConvex f φ) :
    Supercoercive f.asEReal := sorry

end RealNormedSpace

section RealHilbert

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: clause (2) gives supercoercivity, hence coercivity; uniform convexity also forces
-- strict convexity, so existence follows from the coercive `Γ₀(H)` minimization theorem and
-- uniqueness from strict convexity.
/-- Proposition 17.26 (3): a uniformly convex member of `Γ₀(H)` has exactly one global minimizer
over `H`. -/
theorem existsUnique_mem_argmin_of_mem_gammaZero_of_uniformlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} {φ : NNReal → EReal} (hf : f ∈ Γ₀(H))
    (huniform : UniformlyConvex f φ) :
    ∃! x : H, x ∈ Argmin f.asEReal := by
  have hf_coe : Coercive f.asEReal :=
    coercive_of_supercoercive <|
      supercoercive_of_mem_gammaZero_of_uniformlyConvex hf huniform
  exact
    existsUnique_mem_argmin_of_mem_gammaZero_of_coercive_of_strictlyConvex hf hf_coe
      huniform.strictlyConvex

end RealHilbert

end ERealFunction
