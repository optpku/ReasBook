/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Theorem_1_5_11
import AlgebraicTopology_May_1999.Chap01.Theorem_1_6_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Metric
open scoped ContinuousMap

/- Program 1.1.7: the chapter program centers on the construction of the fundamental group
`π₁(X, x)`, the computation `π₁(S¹, 1) = ℤ`, and the applications to Brouwer fixed point and the
fundamental theorem of algebra. The canonical owner for the construction is `FundamentalGroup`. -/
recall FundamentalGroup (X : Type u) [TopologicalSpace X] (x : X) : Type u

/- The circle appearing in the computation `π₁(S¹, 1)` is mathlib's canonical unit circle
`Circle`. -/
recall Circle : Type

/- The chapter's computation `π₁(S¹, 1) = ℤ` is formalized by the canonical infinite-cyclic
equivalence specialized to the generator `standardLoopClass 1`. -/
#check
  (intEquivOfZPowersEqTop (standardLoopClass 1) standardLoopClass_one_zpowers_eq_top :
    Multiplicative ℤ ≃* FundamentalGroup Circle (1 : Circle))

/- One topological application of that computation in the chapter is Brouwer's fixed point theorem
for the closed unit disk. -/
recall brouwer_fixed_point_closed_unit_disk
    (f : C(closedBall (0 : ℂ) 1, closedBall (0 : ℂ) 1)) :
    ∃ x : closedBall (0 : ℂ) 1, Function.IsFixedPt f x

/- The algebraic application is the fundamental theorem of algebra for complex polynomials. -/
recall Complex.exists_root {f : Polynomial ℂ} (hf : 0 < f.degree) :
    ∃ z, f.IsRoot z

/- The complex statement is a specialization of the canonical algebraically-closed-field root
existence theorem. -/
recall IsAlgClosed.exists_root {k : Type u} [Field k] [IsAlgClosed k] (p : Polynomial k)
    (hp : p.degree ≠ 0) :
    ∃ x, p.IsRoot x
