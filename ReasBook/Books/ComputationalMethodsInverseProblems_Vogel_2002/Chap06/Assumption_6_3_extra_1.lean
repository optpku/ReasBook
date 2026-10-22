/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic

public section

open Filter
open scoped Topology

/-- Assumption 6.3-extra-1. The regularization parameter sequence `α` tends to `0`,
and the ratio `δ n ^ 2 / α n` also tends to `0` along `Filter.atTop`. This records the
source asymptotic regime that `α` goes to `0` more slowly than the square of the data
error sequence. -/
structure RegularizationParameterAssumptions (α δ : ℕ → ℝ) : Prop where
  /-- The regularization parameter sequence `α` tends to `0` along `Filter.atTop`. -/
  tendstoAlpha : Tendsto α atTop (𝓝 0)
  /-- The ratio `δ n ^ 2 / α n` tends to `0` along `Filter.atTop`. -/
  tendstoErrorSqDivAlpha : Tendsto (fun n ↦ δ n ^ 2 / α n) atTop (𝓝 0)

namespace RegularizationParameterAssumptions

set_option linter.defProp false in
/-- Build `RegularizationParameterAssumptions` from the two asymptotic clauses. -/
def ofTendsto {α δ : ℕ → ℝ}
    (hα : Tendsto α atTop (𝓝 0))
    (hδα : Tendsto (fun n ↦ δ n ^ 2 / α n) atTop (𝓝 0)) :
    RegularizationParameterAssumptions α δ :=
  { tendstoAlpha := hα
    tendstoErrorSqDivAlpha := hδα }

/-- Specification lemma for `RegularizationParameterAssumptions`. -/
theorem iff {α δ : ℕ → ℝ} :
    RegularizationParameterAssumptions α δ ↔
      Tendsto α atTop (𝓝 0) ∧ Tendsto (fun n ↦ δ n ^ 2 / α n) atTop (𝓝 0) := by
  constructor
  · intro h
    exact ⟨h.tendstoAlpha, h.tendstoErrorSqDivAlpha⟩
  · rintro ⟨hα, hδα⟩
    exact ofTendsto hα hδα

end RegularizationParameterAssumptions
