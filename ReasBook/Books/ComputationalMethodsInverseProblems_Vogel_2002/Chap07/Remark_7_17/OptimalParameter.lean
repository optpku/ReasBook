/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.OptimalIndex

public section

noncomputable section

namespace TsvdEstimation

/-- The explicit TSVD asymptotic constant `C₂^TSVD` from `(7.65)`. -/
def parameterConstant (b c p q : ℝ) : ℝ :=
  (c ^ q / b ^ p) ^ (1 / (p + q))

/-- The defining closed form for `parameterConstant`. -/
theorem parameterConstant_def (b c p q : ℝ) :
    parameterConstant b c p q = (c ^ q / b ^ p) ^ (1 / (p + q)) := by
  -- This companion theorem just exposes the closed form already stored in the definition.
  rfl

/-- The explicit TSVD filter-parameter benchmark sequence from `(7.65)`. -/
def parameterBenchmark (b c p q σ : ℝ) : ℕ → ℝ :=
  fun n ↦ parameterConstant b c p q * (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q)))

/-- The defining formula for `parameterBenchmark`. -/
theorem parameterBenchmark_def (b c p q σ : ℝ) (n : ℕ) :
    parameterBenchmark b c p q σ n =
      parameterConstant b c p q * (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q))) := by
  -- This benchmark theorem is a direct rewrite anchor for the local definition.
  rfl

/-- The explicit TSVD benchmark filter-parameter sequence derived from the
optimal truncation index `(7.63)`. -/
def optimalFilterParameter (b c p q σ : ℝ) : ℕ → ℝ :=
  fun n ↦ c * ((TsvdEstimation.optimalIndex b c p q σ n : ℝ) ^ (-p))

/-- The defining formula for `optimalFilterParameter`. -/
theorem optimalFilterParameter_def (b c p q σ : ℝ) (n : ℕ) :
    optimalFilterParameter b c p q σ n =
      c * ((TsvdEstimation.optimalIndex b c p q σ n : ℝ) ^ (-p)) := by
  -- This theorem only unfolds the owned TSVD parameter sequence once.
  rfl

end TsvdEstimation
