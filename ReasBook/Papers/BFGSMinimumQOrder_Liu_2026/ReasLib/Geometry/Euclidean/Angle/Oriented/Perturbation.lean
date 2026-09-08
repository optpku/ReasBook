module

public import Mathlib.Analysis.Complex.Angle
public import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
public import ReasLib.Analysis.Complex.Polar

public section

noncomputable section

universe u

namespace Orientation

/-- The Kähler coordinate is the polar point whose radius is the product of the vector norms
and whose argument is the oriented angle. -/
private lemma kahlerPolarDecomposition {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (v w : V) :
    (((‖v‖ * ‖w‖ : ℝ) : ℂ) *
      Complex.exp ((o.oangle v w).toReal * Complex.I)) = o.kahler v w := by
  -- Replace the radial and angular data by the norm and argument of the Kähler coordinate.
  rw [← o.norm_kahler v w]
  simp only [oangle, Complex.arg_coe_angle_toReal_eq_arg,
    Complex.norm_mul_exp_arg_mul_I]

/-- The Kähler chord from a vector to itself has norm equal to the first norm times the
underlying vector displacement. -/
private lemma normKahlerSubSelf {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (v w : V) :
    ‖o.kahler v w - o.kahler v v‖ = ‖v‖ * ‖w - v‖ := by
  -- Linearity in the second variable turns the complex chord into one Kähler coordinate.
  rw [← map_sub, o.norm_kahler]

/-- A common positive lower norm bound controls the real oriented angle between two vectors. -/
theorem abs_toReal_oangle_le {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (v w : V) (rho : ℝ)
    (hrho : 0 < rho) (hv : rho ≤ ‖v‖) (hw : rho ≤ ‖w‖) :
    |(o.oangle v w).toReal| ≤ Real.pi * ‖w - v‖ / rho := by
  -- Both Kähler radii lie in the annulus with lower radius `‖v‖ * rho`.
  have hvPos : 0 < ‖v‖ := hrho.trans_le hv
  have hRadiusPos : 0 < ‖v‖ * rho := mul_pos hvPos hrho
  have hvwRadius : ‖v‖ * ‖w‖ ∈ Set.Icc (‖v‖ * rho) (‖v‖ * max ‖v‖ ‖w‖) := by
    constructor
    · exact mul_le_mul_of_nonneg_left hw (norm_nonneg v)
    · exact mul_le_mul_of_nonneg_left (le_max_right ‖v‖ ‖w‖) (norm_nonneg v)
  have hvvRadius : ‖v‖ ^ 2 ∈ Set.Icc (‖v‖ * rho) (‖v‖ * max ‖v‖ ‖w‖) := by
    rw [pow_two]
    constructor
    · exact mul_le_mul_of_nonneg_left hv (norm_nonneg v)
    · exact mul_le_mul_of_nonneg_left (le_max_left ‖v‖ ‖w‖) (norm_nonneg v)
  -- Apply the annular chord estimate to the Kähler point and the self-coordinate.
  have hPolar := Complex.polarChordLowerBound
    (θ₁ := (o.oangle v w).toReal) (θ₂ := 0) hRadiusPos hvwRadius hvvRadius
  rw [sub_zero, Real.Angle.coe_toReal, kahlerPolarDecomposition, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero, mul_one, Complex.ofReal_pow, ← o.kahler_apply_self v,
    normKahlerSubSelf] at hPolar
  -- Cancel the positive common factor `‖v‖` from the chord estimate.
  have hFactor :
      2 * (‖v‖ * rho) / Real.pi * |(o.oangle v w).toReal| =
        ‖v‖ * (2 * rho / Real.pi * |(o.oangle v w).toReal|) := by
    ring
  rw [hFactor] at hPolar
  have hAngle :
      2 * rho / Real.pi * |(o.oangle v w).toReal| ≤ ‖w - v‖ :=
    le_of_mul_le_mul_left hPolar hvPos
  -- Clear the positive factor `Real.pi` and weaken the factor-two estimate.
  have hScaled :
      2 * rho * |(o.oangle v w).toReal| ≤ Real.pi * ‖w - v‖ := by
    calc
      2 * rho * |(o.oangle v w).toReal| ≤ ‖w - v‖ * Real.pi := by
        apply (div_le_iff₀ Real.pi_pos).mp
        calc
          2 * rho * |(o.oangle v w).toReal| / Real.pi =
              2 * rho / Real.pi * |(o.oangle v w).toReal| := by ring
          _ ≤ ‖w - v‖ := hAngle
      _ = Real.pi * ‖w - v‖ := mul_comm _ _
  have hWeak : rho * |(o.oangle v w).toReal| ≤ Real.pi * ‖w - v‖ := by
    nlinarith [mul_nonneg hrho.le (abs_nonneg (o.oangle v w).toReal)]
  apply (le_div_iff₀ hrho).2
  simpa only [mul_comm] using hWeak

/-- Adding an error vector changes the real oriented angle by at most its relative size. -/
theorem abs_toReal_oangle_add_le {V : Type u} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]
    (o : Orientation ℝ V (Fin 2)) (v e : V) (rho : ℝ)
    (hrho : 0 < rho) (hv : rho ≤ ‖v‖) (hve : rho ≤ ‖v + e‖) :
    |(o.oangle v (v + e)).toReal| ≤ Real.pi * ‖e‖ / rho := by
  -- Specialize the common-bound estimate and normalize the additive displacement.
  simpa only [add_sub_cancel_left] using
    (abs_toReal_oangle_le o v (v + e) rho hrho hv hve)

end Orientation
