/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/ReasLib/Geometry/Euclidean/Angle/AbsToReal.lean
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

public section

namespace Real.Angle

/-- Although the principal representative `Angle.toReal` jumps at the branch cut,
its absolute value is a globally continuous function of the angle. -/
@[continuity, fun_prop]
theorem continuous_abs_toReal : Continuous (fun θ : Angle ↦ |θ.toReal|) := by
  have hformula : (fun θ : Angle ↦ |θ.toReal|) =
      fun θ ↦ Real.arccos (Real.Angle.cos θ) := by
    funext θ
    rw [← Real.Angle.cos_toReal, ← Real.cos_abs,
      Real.arccos_cos (abs_nonneg θ.toReal) (Real.Angle.abs_toReal_le_pi θ)]
  rw [hformula]
  exact Real.continuous_arccos.comp Real.Angle.continuous_cos

end Real.Angle
