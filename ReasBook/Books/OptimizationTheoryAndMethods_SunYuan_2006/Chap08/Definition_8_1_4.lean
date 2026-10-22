/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_3

section Chapter08Definition814

variable {X : Type*} [PseudoMetricSpace X]
variable {α : Type*} [Preorder α]

-- Domain sampling:
-- * primary domain: constrained local minima in metric spaces
-- * source-facing owner reused from `Definition_8_1_3`: `IsConstrainedLocalMinOn`
-- * core/canonical owner: `IsLocalMinOn`
-- * inspected related declarations:
--   `IsLocalMinOn` / `IsLocalMinOn.on_subset` in `Mathlib.Topology.Order.LocalExtr`
--   `IsStrictLocalMin` in `Chapter01/Definition_1_4_1`
--   `isConstrainedLocalMinOn_iff_exists_forall_mem_closedBall` in `Chapter08/Definition_8_1_3`
-- * layer triage: source-facing owner built from the Chapter 8 constrained-local-minimum owner
--   and the canonical core owner `IsLocalMinOn`
-- * primitive data here: constrained local minimality at `xStar` and the isolation
--   radius/uniqueness clause
-- * derived API here: accessors recovering feasibility and the canonical local-minimum owner

/-- Chapter08 Definition 8.1.4: `xStar` is an isolated local minimizer of `f` on `X` when
`xStar` is a constrained local minimizer of `f` on `X`, and there exists `δ > 0` such that
every local minimizer of `f` on `X` lying in `X ∩ Metric.ball xStar δ` is equal to `xStar`. -/
def IsIsolatedLocalMinOn (f : X → α) (s : Set X) (xStar : X) : Prop :=
  IsConstrainedLocalMinOn f s xStar ∧
    ∃ δ > 0, ∀ x : X, x ∈ s ∩ Metric.ball xStar δ → IsLocalMinOn f s x → x = xStar

/-- Unfolding formula for `IsIsolatedLocalMinOn`. -/
theorem isIsolatedLocalMinOn_iff
    (f : X → α) (s : Set X) (xStar : X) :
    IsIsolatedLocalMinOn f s xStar ↔
      IsConstrainedLocalMinOn f s xStar ∧
        ∃ δ > 0, ∀ x : X, x ∈ s ∩ Metric.ball xStar δ → IsLocalMinOn f s x → x = xStar :=
  Iff.rfl

/-- An isolated local minimizer on `s` is feasible. -/
theorem IsIsolatedLocalMinOn.mem
    {f : X → α} {s : Set X} {xStar : X} (h : IsIsolatedLocalMinOn f s xStar) :
    xStar ∈ s :=
  h.1.mem

/-- An isolated local minimizer on `s` is, in particular, a local minimizer on `s`. -/
theorem IsIsolatedLocalMinOn.isLocalMinOn
    {f : X → α} {s : Set X} {xStar : X} (h : IsIsolatedLocalMinOn f s xStar) :
    IsLocalMinOn f s xStar :=
  h.1.isLocalMinOn

/-- In some ball around an isolated local minimizer, every feasible local minimizer coincides
with the base point. -/
theorem IsIsolatedLocalMinOn.isolated
    {f : X → α} {s : Set X} {xStar : X} (h : IsIsolatedLocalMinOn f s xStar) :
    ∃ δ > 0, ∀ x : X, x ∈ s ∩ Metric.ball xStar δ → IsLocalMinOn f s x → x = xStar :=
  h.2

end Chapter08Definition814
