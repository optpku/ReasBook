/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_35

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped DeltaN

local notation "E" N => EuclideanSpace ℝ (Fin (N + 1))

/-
Definition 3.41 is a recall-only item in the chapter's finite-horizon subgradient-stepsize
domain.

Sampled owner-style declarations:
- `EuclideanSpace.positiveOrthant` in `Nesterov.Chap01.Definition_1_10_2`, the strict
  orthant owner reused by the same stepsize functional
- `deltaN` in `Nesterov.Chap03.Proposition_3_35`, the chapter owner for the scalar
  `Δ_N(h₀, ..., h_N)`
- `deltaN_apply` in `Nesterov.Chap03.Proposition_3_35`, the pointwise evaluation bridge for
  that owner
- `deltaN_constantChoice_minimizes_positiveOrthant` in
  `Nesterov.Chap03.Proposition_3_35`, the later constant-stepsize optimality theorem for
  the same owner

Best owner abstraction:
- `source-facing`: the textbook scalar `Δ_N` attached to a finite stepsize vector
- `core/canonical`: `deltaN N R h`, with source-facing surface `Δ[N; R] h`
- `bridge/view`: `deltaN_apply`

Primitive data:
- the horizon `N : ℕ`
- the radius `R : ℝ`
- the finite stepsize vector `h : E N`

Derived API:
- the source-facing notation `Δ[N; R] h`
- the defining quotient formula from `deltaN_apply`
- the constant-stepsize minimization theorem from Proposition 3.35

Definition 3.41 adds no new mathematical data beyond this existing owner, so this file keeps only
the direct canonical recall surface and introduces no parallel public alias for `Δ_N`, while
reusing the owner notation from `Proposition_3_35`.
-/

/- Definition 3.41 reuses the chapter owner for the finite stepsize scalar directly. -/
recall deltaN (N : ℕ) (R : ℝ) (h : E N) : ℝ

/- Evaluating the recalled owner `deltaN` gives the textbook quotient
`(R² + ∑_{i=0}^N h_i²) / (2 ∑_{i=0}^N h_i)`. -/
recall deltaN_apply (N : ℕ) (R : ℝ) (h : E N) :
    Δ[N; R] h =
      (R ^ (2 : ℕ) + ∑ i : Fin (N + 1), h i ^ (2 : ℕ)) /
        (2 * ∑ i : Fin (N + 1), h i)

end
