/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Basic

open Filter

section

variable {α : Type*} [TopologicalSpace α]

/-- A sequence `u` has a subsequence converging to `a` when there is a strictly monotone
extraction `φ` such that `u ∘ φ → a`. -/
def HasSubsequenceTendstoTo (u : ℕ → α) (a : α) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (nhds a)

/-- Source-semantic expansion of `HasSubsequenceTendstoTo u a`. -/
theorem hasSubsequenceTendstoTo_iff (u : ℕ → α) (a : α) :
    HasSubsequenceTendstoTo u a ↔
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (nhds a) :=
  Iff.rfl

end
