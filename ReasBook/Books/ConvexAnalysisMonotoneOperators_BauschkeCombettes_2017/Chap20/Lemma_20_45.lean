/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

section BivariateQuadratic

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Lemma 20.45 is about the real-valued quadratic kernel
  `G : H × H → ℝ`.
- `core/canonical`: Fenchel conjugation is the canonical `EReal`-valued owner on the product
  Hilbert space, using the Chapter 9 raw-product `ℓ²` bridges.
- `bridge/view`: when conjugation is needed, `G` is viewed through the canonical coercion
  `Function.toEReal` rather than by introducing a second `EReal`-valued kernel owner.
-/

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2 prod_normedSpace_l2
  prod_innerProductSpace_l2

/-- The swap-negation involution on `H × H`, sending `(u, x)` to `(-x, -u)`. -/
def skewSwapNeg : H × H → H × H :=
  fun p ↦ -(Prod.swap p)

/-- The real-valued bivariate quadratic kernel `G` centered at `(z, w)` from Lemma 20.45,
written in the equivalent form
`G(x, u) = -⟪x, u⟫ + ‖(x - z) + (u - w)‖² / 2`. -/
def bivariateQuadraticKernel (z w : H) : H × H → ℝ :=
  fun p ↦
    -⟪p.1, p.2⟫_ℝ + (1 / 2 : ℝ) * ‖(p.1 - z) + (p.2 - w)‖ ^ 2

-- Proof sketch: apply the product-space quadratic self-conjugacy from Proposition 13.19 to the
-- half-squared norm term on `H × H`, then use the translation and linear-perturbation rule from
-- Proposition 13.23 to account for the center `(z, w)` and the pairing term `-⟪x, u⟫`.
/-- Lemma 20.45: the quadratic kernel `G` centered at `(z, w)` has Fenchel conjugate
`G* = G ∘ L`, where `L(u, x) = (-x, -u)`. -/
theorem bivariateQuadraticKernel_conjugate_eq_comp_skewSwapNeg (z w : H) :
    ((bivariateQuadraticKernel z w).toEReal.asEReal)∗ =
      ((bivariateQuadraticKernel z w) ∘ skewSwapNeg).toEReal.asEReal := sorry

-- Proof sketch: rewrite `G(x, u) + ⟪x, u⟫` as
-- `(1 / 2) * ‖(x - z) + (u - w)‖ ^ 2`, which is nonnegative.
/-- Clause (i): adding the pairing `⟪x, u⟫` to the kernel value is always nonnegative. -/
theorem bivariateQuadraticKernel_add_pairing_nonneg (z w x u : H) :
    0 ≤ bivariateQuadraticKernel z w (x, u) + ⟪x, u⟫_ℝ := sorry

-- Proof sketch: after the same rewrite as in clause (i), equality holds exactly when the norm
-- vanishes, i.e. when `(x - z) + (u - w) = 0`.
/-- Clause (ii): equality in clause (i) holds exactly when `x - z = w - u`. -/
theorem bivariateQuadraticKernel_add_pairing_eq_zero_iff (z w x u : H) :
    bivariateQuadraticKernel z w (x, u) + ⟪x, u⟫_ℝ = 0 ↔
      x - z = w - u := sorry

-- Proof sketch: clause (ii) gives `x - z = w - u`; substituting this into
-- `⟪z - x, w - u⟫` yields the negative squared norm of `x - z`, so the extra nonnegativity
-- assumption forces `x = z` and then `u = w`.
/-- Clause (iii): equality in clause (i) together with
`0 ≤ ⟪z - x, w - u⟫` is equivalent to `(x, u) = (z, w)`. -/
theorem bivariateQuadraticKernel_zero_pairing_and_cross_nonneg_iff
    (z w x u : H) :
    (bivariateQuadraticKernel z w (x, u) + ⟪x, u⟫_ℝ = 0 ∧
      0 ≤ ⟪z - x, w - u⟫_ℝ) ↔
      (x, u) = (z, w) := sorry

end BivariateQuadratic

end

end ERealFunction
