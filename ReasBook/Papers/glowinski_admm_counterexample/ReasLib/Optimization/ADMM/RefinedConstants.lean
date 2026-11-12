/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace ADMM.RefinedEndpoint

/-- The exact lower test factor `L` in the updated manuscript, equation (2.2). -/
noncomputable def lower : ℝ := 75475298801 / 40000000000

/-- The exact upper test factor `U` in the updated manuscript, equation (2.2). -/
noncomputable def upper : ℝ := 47172066094067 / 25000000000000

/-- The exact enclosure width; defining constants is separate from proving the bounds. -/
theorem width : upper - lower = (2171721 : ℝ) / 12500000000000 := by
  norm_num [upper, lower]

theorem classical_bound_lt_lower : (377 : ℝ) / 200 < lower := by
  norm_num [lower]

theorem lower_pos : 0 < lower := by norm_num [lower]

theorem lower_lt_upper : lower < upper := by norm_num [lower, upper]

theorem upper_lt_two : upper < 2 := by norm_num [upper]

/-- The refined upper test factor is below the threshold of the retained period-48 example. -/
theorem upper_lt_period48_factor : upper < (542407991247 : ℝ) / 287451196000 := by
  norm_num [upper]

end ADMM.RefinedEndpoint
