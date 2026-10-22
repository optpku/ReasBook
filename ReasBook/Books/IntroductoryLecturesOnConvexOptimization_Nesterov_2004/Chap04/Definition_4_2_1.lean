/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Module

universe u v

/- This item is recall-only in the algebraic-duality / reflexive-module domain.

Sampled canonical owners:
- `Module.Dual`
- `Module.dualPairing`
- `Module.IsReflexive`
- `Module.evalEquiv`

Best owner abstraction:
- core/canonical: the ambient `R`-module owner `Dual R E` and its evaluation pairing
  `Module.dualPairing R E`
- for the bidual identification, the reflexive-module owner `[Module.IsReflexive R E]` with
  `Module.evalEquiv R E`

Primitive data:
- a scalar semiring `R`
- an additive commutative monoid `E` with an `R`-module structure
- for the bidual identification, the reflexivity witness on `E`

Derived API:
- the dual module `Dual R E`
- the evaluation pairing `Module.dualPairing R E`
- the canonical bidual equivalence `Module.evalEquiv R E`

Source/core/bridge triage:
- source-facing: the dual space, the evaluation pairing, and the finite-dimensional vector-space
  identification with the bidual
- core/canonical: `Module.Dual`, `Module.dualPairing`, `Module.evalEquiv`
- bridge/view: finite-dimensional vector spaces furnish `Module.IsReflexive`, so the textbook
  finite-dimensional case is a specialization of the reflexive owner `Module.evalEquiv`

The source-facing real-vector-space statements are therefore refined to the weakest owner level
already present in mathlib, with the finite-dimensional textbook case kept only as a bridge to the
canonical reflexive-module equivalence. -/

section DualSpace

variable {R : Type u} {E : Type v} [Semiring R] [AddCommMonoid E] [Module R E]

/- Definition 4.2.1: for an `R`-module `E`, the dual space `E*` is the canonical owner
`Dual R E`, i.e. the space `(E →ₗ[R] R)` of linear functionals on `E`. The textbook real-vector-
space case is the specialization `R = ℝ`. -/
recall Module.Dual

end DualSpace

section DualPairing

variable {R : Type u} {E : Type v} [CommSemiring R] [AddCommMonoid E] [Module R E]

/- The duality pairing is the canonical evaluation pairing on the module dual. -/
recall Module.dualPairing

/- Evaluating the canonical duality pairing agrees with applying the functional. -/
recall Module.dualPairing_apply

end DualPairing

section ReflexiveBidual

variable {R : Type u} {E : Type v} [CommSemiring R] [AddCommMonoid E] [Module R E]
variable [Module.IsReflexive R E]

/- The bidual identification belongs to the canonical reflexive-module owner
`Module.evalEquiv R E : E ≃ₗ[R] Dual R (Dual R E)`. -/
recall Module.evalEquiv

end ReflexiveBidual

section FiniteDimensionalBidualBridge

variable {K : Type u} {E : Type v} [Field K] [AddCommGroup E] [Module K E]
variable [FiniteDimensional K E]

/- Finite-dimensional vector spaces supply the reflexivity hypothesis needed by
`Module.evalEquiv`, so the textbook finite-dimensional bidual identification is the direct
finite-dimensional specialization of that canonical equivalence. -/
#check (Module.evalEquiv K E : E ≃ₗ[K] Dual K (Dual K E))

end FiniteDimensionalBidualBridge
