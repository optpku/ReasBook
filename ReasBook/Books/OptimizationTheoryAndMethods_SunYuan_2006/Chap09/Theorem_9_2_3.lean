/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.SaddlePoint
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_2_1

noncomputable section

namespace QuadraticProgram

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Multiplier" => QuadraticProgram.Multiplier me mi

-- Domain sampling:
-- * primary domain: quadratic-program duality via Lagrangian saddle points
-- * inspected relevant owner declarations:
--   `ConstrainedOptimizationProblem.lagrangian` from Chapter 8,
--   `QuadraticProgram.Multiplier`, `QuadraticProgram.multiplierVector`, `Λ[P]`, and `ℒ[P]`
--   from `Theorem_9_2_1`,
--   `IsSaddlePointOn` from mathlib
-- * best owner abstractions:
--   the upstream Chapter 9 split-multiplier/Lagrangian owner surface from `Theorem_9_2_1`,
--   `IsSaddlePointOn` for the saddle-point predicate
-- * layer triage in this file:
--   source-facing: the saddle-pair predicate
--   core/canonical: the upstream Chapter 9 owners `Λ[P]`, `ℒ[P]`, and `Multiplier`
--   together with mathlib's `IsSaddlePointOn`
--   bridge/view: none beyond the upstream owner surface
-- * primitive data vs. derived API:
--   primitive source-facing data already live upstream in the Chapter 9 owner surface;
--   this file contributes only the saddle-pair predicate and its equivalence theorem, built
--   from that owner surface and mathlib's saddle-point abstraction

open scoped QuadraticProgram

/-- `P.IsSaddlePair xStar multStar` means that `xStar ∈ X`, `multStar ∈ Λ[P]`, and
`(xStar, multStar)` is a saddle point of `ℒ[P]` on `X × Λ[P]`. -/
def IsSaddlePair (P : QuadraticProgram n me mi) (xStar : Point) (multStar : Multiplier) : Prop :=
  xStar ∈ P.feasibleSet ∧
    multStar ∈ Λ[P] ∧
      IsSaddlePointOn P.feasibleSet Λ[P] ℒ[P] xStar multStar

/-- Membership in `P.IsSaddlePair xStar multStar` is equivalent to the source saddle-point
inequalities `ℒ[P] xStar λ ≤ ℒ[P] xStar multStar ≤ ℒ[P] x multStar` for all `x ∈ X` and
`λ ∈ Λ[P]`. -/
theorem isSaddlePair_iff
    (P : QuadraticProgram n me mi) (xStar : Point) (multStar : Multiplier) :
    P.IsSaddlePair xStar multStar ↔
      xStar ∈ P.feasibleSet ∧
        multStar ∈ Λ[P] ∧
          (∀ mult ∈ Λ[P], ℒ[P] xStar mult ≤ ℒ[P] xStar multStar) ∧
            ∀ x ∈ P.feasibleSet,
              ℒ[P] xStar multStar ≤ ℒ[P] x multStar := by
  constructor
  · rintro ⟨hxStar, hmultStar, hsaddle⟩
    refine ⟨hxStar, hmultStar, ?_, ?_⟩
    · intro mult hmult
      exact hsaddle xStar hxStar mult hmult
    · intro x hx
      exact hsaddle x hx multStar hmultStar
  · rintro ⟨hxStar, hmultStar, hleft, hright⟩
    refine ⟨hxStar, hmultStar, ?_⟩
    intro x hx mult hmult
    exact le_trans (hleft mult hmult) (hright x hx)

/-- Chapter09 Theorem 9.2.3: if `P.G` is positive definite, then `xStar ∈ X` is a minimizer of
the quadratic program `(9.1.1)`-`(9.1.3)` if and only if there exists a multiplier pair
`(λeq⋆, λineq⋆) ∈ Λ[P]` such that `(xStar, (λeq⋆, λineq⋆))` is a saddle point of the
Lagrangian `ℒ[P]`; equivalently,
`ℒ[P] xStar λ ≤ ℒ[P] xStar (λeq⋆, λineq⋆) ≤
ℒ[P] x (λeq⋆, λineq⋆)` for all `x ∈ X` and `λ ∈ Λ[P]`. -/
theorem isMinOn_iff_exists_isSaddlePair_of_posDef
    (P : QuadraticProgram n me mi) (xStar : Point) (hG : P.G.PosDef) :
    IsMinOn P P.feasibleSet xStar ↔
      ∃ multStar : Multiplier, P.IsSaddlePair xStar multStar := sorry

end QuadraticProgram
