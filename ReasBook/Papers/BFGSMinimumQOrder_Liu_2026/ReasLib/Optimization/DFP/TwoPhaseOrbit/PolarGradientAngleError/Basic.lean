module

public import ReasLib.Geometry.Euclidean.Angle.Oriented.Perturbation

public section

noncomputable section

universe u

namespace DFP.TwoPhaseOrbit

/-!
# Basic perturbation adapters for planar angle errors

These lemmas package the common positive-radius estimate for oriented angles in
a form that can be applied directly to endpoint and gradient vectors.  The
quantitative orbit files supply the norm lower bound and the perturbation
estimate; this companion only performs the stable analytic transport.
-/

/-- A common positive norm lower bound turns a vector perturbation estimate into
a real oriented-angle bound. -/
theorem abs_oangle_toReal_le_of_norm_perturbation
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (v w : V) (rho K : ℝ)
    (hrho : 0 < rho) (hv : rho ≤ ‖v‖) (hw : rho ≤ ‖w‖)
    (hpert : ‖w - v‖ ≤ K) :
    |(o.oangle v w).toReal| ≤ Real.pi * K / rho := by
  calc
    |(o.oangle v w).toReal| ≤ Real.pi * ‖w - v‖ / rho :=
      Orientation.abs_toReal_oangle_le o v w rho hrho hv hw
    _ ≤ Real.pi * K / rho := by
      apply (div_le_div_iff_of_pos_right hrho).2
      exact mul_le_mul_of_nonneg_left hpert (le_of_lt Real.pi_pos)

/-- If the vector perturbation is fourth order in a positive radius, the
oriented-angle error is bounded cubically in that radius. -/
theorem abs_oangle_toReal_le_of_cubic_perturbation
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (v w : V) (rho K : ℝ)
    (hrho : 0 < rho) (hv : rho ≤ ‖v‖) (hw : rho ≤ ‖w‖)
    (hpert : ‖w - v‖ ≤ K * rho ^ 4) :
    |(o.oangle v w).toReal| ≤ Real.pi * K * rho ^ 3 := by
  calc
    |(o.oangle v w).toReal| ≤ Real.pi * ‖w - v‖ / rho :=
      Orientation.abs_toReal_oangle_le o v w rho hrho hv hw
    _ ≤ Real.pi * (K * rho ^ 4) / rho := by
      apply (div_le_div_iff_of_pos_right hrho).2
      exact mul_le_mul_of_nonneg_left hpert (le_of_lt Real.pi_pos)
    _ = Real.pi * K * rho ^ 3 := by
      field_simp [ne_of_gt hrho]

/-- The additive form of the cubic adapter applies when the second planar
vector is written as a base vector plus a fourth-order error. -/
theorem abs_oangle_toReal_add_le_of_cubic_perturbation
    {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (v e : V) (rho K : ℝ)
    (hrho : 0 < rho) (hv : rho ≤ ‖v‖) (hve : rho ≤ ‖v + e‖)
    (hpert : ‖e‖ ≤ K * rho ^ 4) :
    |(o.oangle v (v + e)).toReal| ≤ Real.pi * K * rho ^ 3 := by
  calc
    |(o.oangle v (v + e)).toReal| ≤ Real.pi * ‖e‖ / rho :=
      Orientation.abs_toReal_oangle_add_le o v e rho hrho hv hve
    _ ≤ Real.pi * (K * rho ^ 4) / rho := by
      apply (div_le_div_iff_of_pos_right hrho).2
      exact mul_le_mul_of_nonneg_left hpert (le_of_lt Real.pi_pos)
    _ = Real.pi * K * rho ^ 3 := by
      field_simp [ne_of_gt hrho]

end DFP.TwoPhaseOrbit
