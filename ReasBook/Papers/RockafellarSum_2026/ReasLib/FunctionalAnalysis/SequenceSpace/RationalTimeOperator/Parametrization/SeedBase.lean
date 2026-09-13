/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.FixedPositive
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.UnitDifferenceDetector
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.C0.Single
public import RockafellarSum_2026.ReasLib.Analysis.Normed.LorentzCone.SeedTemplate
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Norm

/-!
# Fixed-positive seed bases
-/

public section

namespace Lorentz

/-- The carrier point obtained from a source sequence `a` with prescribed
positive Lorentz coordinate `s`. -/
noncomputable def seedBase {d : C0Seq} (a : L1Seq) (s : ℝ) : parametrizedSubspace d :=
  parametrizedPoint d a (2 * s - C0Seq.pairingL d a)

/-- The seed base has exactly the prescribed positive coordinate. -/
theorem positiveCoordinate_seedBase {d : C0Seq} (hd : d ≠ 0)
    (a : L1Seq) (s : ℝ) :
    positiveCoordinate d hd (seedBase a s) = s := by
  unfold seedBase
  exact positiveCoordinate_adjustedParameter d hd a s

/-- The negative coordinate of a seed base is the interval-coordinate image
and the adjusted scalar residual. -/
theorem negativeCoordinate_seedBase {d : C0Seq} (hd : d ≠ 0)
    (a : L1Seq) (s : ℝ) :
    negativeCoordinate d hd (seedBase a s) =
      HilbertProd2.mk (L1Seq.intervalCoordinateOperator a)
        (s - C0Seq.pairingL d a) := by
  unfold seedBase
  exact negativeCoordinate_adjustedParameter d hd a s

/-- The canonical first-axis direction used by the S3 construction. -/
def axisDirection : C0Seq := c0Single 1 1

/-- The distinguished axis reads one at coordinate one and zero elsewhere. -/
theorem axisDirection_apply (n : ℕ) : axisDirection n = if n = 1 then 1 else 0 := by
  exact c0Single_apply 1 1 n

/-- The distinguished coordinate axis is nonzero. -/
theorem seed_axis_ne_zero : axisDirection ≠ 0 := by
  intro h
  have he := congrArg (fun x : C0Seq ↦ x 1) h
  simp [axisDirection_apply] at he

/-- The axis direction pairs with a unit difference at coordinate `1` as one
when the second coordinate is distinct. -/
theorem pairingL_axisDirection_unitDifference {r : ℕ} (hr : r ≠ 1) :
    C0Seq.pairingL axisDirection (unitDifference 1 r) = 1 := by
  rw [pairingL_unitDifference]
  simp [axisDirection, c0Single_apply, hr]

/-- The fixed-positive seed base specialized to the first-axis direction. -/
noncomputable def axisSeedBase (a : L1Seq) (s : ℝ) :
    parametrizedSubspace axisDirection :=
  seedBase a s

/-- Axis seed bases retain their prescribed positive coordinate. -/
theorem positiveCoordinate_axisSeedBase (hd : axisDirection ≠ 0) (a : L1Seq) (s : ℝ) :
    positiveCoordinate axisDirection hd (axisSeedBase a s) = s := by
  exact positiveCoordinate_seedBase hd a s

/-- For a scaled unit difference away from coordinate one, the axis seed base
has vanishing scalar negative coordinate. -/
theorem negativeCoordinate_axisSeedBase
    (r : ℕ) (hr : r ≠ 1) (s : ℝ) :
    negativeCoordinate axisDirection seed_axis_ne_zero
        (axisSeedBase (s • unitDifference 1 r) s) =
      HilbertProd2.mk
        (L1Seq.intervalCoordinateOperator (s • unitDifference 1 r)) 0 := by
  unfold axisSeedBase
  rw [negativeCoordinate_seedBase]
  rw [map_smul, map_smul, pairingL_axisDirection_unitDifference hr]
  simp

/-- The negative-coordinate norm of an axis seed base is controlled by the
corresponding rational-time interval distance. -/
theorem norm_negativeCoordinate_axisSeedBase
    (r : ℕ) (hr : r ≠ 1) (s : ℝ) :
    ‖negativeCoordinate axisDirection seed_axis_ne_zero
        (axisSeedBase (s • unitDifference 1 r) s)‖ =
      |s| * Real.sqrt |rationalTime 1 - rationalTime r| := by
  rw [negativeCoordinate_axisSeedBase r hr s]
  rw [norm_hilbertProd_mk_zero, map_smul, norm_smul]
  rw [norm_intervalCoordinate_unitDifference]
  simp only [Real.norm_eq_abs]


/-- The axis seed base agrees with the explicit source parametrization. -/
theorem axisSeedBase_unitDifference_eq (r : ℕ) (hr : r ≠ 1) (s : ℝ) :
    axisSeedBase (s • unitDifference 1 r) s =
      parametrizedPoint axisDirection (s • unitDifference 1 r) s := by
  unfold axisSeedBase seedBase
  rw [map_smul, pairingL_axisDirection_unitDifference hr]
  congr 1
  simp only [smul_eq_mul, mul_one]
  ring

/-- The primal component of an axis seed base is bounded independently of the
remote coordinate. -/
theorem norm_axisSeedBase_fst_le (r : ℕ) (hr : r ≠ 1) (s : ℝ) :
    ‖(axisSeedBase (s • unitDifference 1 r) s : C0Seq × L1Seq).1‖ ≤ 5 * |s| := by
  rw [axisSeedBase_unitDifference_eq r hr s, parametrizedPoint_apply,
    parametrization_apply]
  have ha : ‖s • unitDifference 1 r‖ ≤ |s| * 2 := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (norm_unitDifference_le_two 1 r) (abs_nonneg s)
  have hA := L1Seq.norm_positiveOperator_apply_le_two (s • unitDifference 1 r)
  have ht := norm_add_le (-L1Seq.positiveOperator (s • unitDifference 1 r))
    (s • axisDirection)
  simp only [norm_neg, norm_smul, Real.norm_eq_abs, axisDirection,
    norm_c0Single, abs_one, mul_one] at ht
  change ‖-L1Seq.positiveOperator (s • unitDifference 1 r) + s • axisDirection‖ ≤ _
  change ‖-L1Seq.positiveOperator (s • unitDifference 1 r) + s • axisDirection‖ ≤ _ at ht
  linarith

/-- Both components of the axis seed base have uniform bounds in the source
product norm. -/
theorem axisSeedBase_component_norms_le (r : ℕ) (hr : r ≠ 1) (s : ℝ) :
    ‖(axisSeedBase (s • unitDifference 1 r) s : C0Seq × L1Seq).1‖ +
      ‖(axisSeedBase (s • unitDifference 1 r) s : C0Seq × L1Seq).2‖ ≤ 7 * |s| := by
  have hx := norm_axisSeedBase_fst_le r hr s
  have hu : ‖(axisSeedBase (s • unitDifference 1 r) s : C0Seq × L1Seq).2‖ ≤
      2 * |s| := by
    rw [axisSeedBase_unitDifference_eq r hr s, parametrizedPoint_apply,
      parametrization_apply]
    change ‖s • unitDifference 1 r‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [norm_unitDifference_le_two 1 r, abs_nonneg s]
  linarith

/-- The symmetric pairing against an axis seed base is uniformly bounded for
all source scales of absolute value at most three halves. -/
theorem abs_symmetricForm_axisSeedBase_le (w : C0Seq × L1Seq)
    (r : ℕ) (hr : r ≠ 1) (s : ℝ) (hs : |s| ≤ 3 / 2) :
    |C0Seq.symmetricForm w (axisSeedBase (s • unitDifference 1 r) s)| ≤
      (21 / 2) * (‖w.1‖ + ‖w.2‖) := by
  let z : C0Seq × L1Seq := axisSeedBase (s • unitDifference 1 r) s
  have hz : ‖z.1‖ + ‖z.2‖ ≤ 21 / 2 := by
    have h := axisSeedBase_component_norms_le r hr s
    change ‖z.1‖ + ‖z.2‖ ≤ _ at h
    linarith
  have hfirst : |C0Seq.pairingL w.1 z.2| ≤ ‖w.1‖ * ‖z.2‖ := by
    simpa only [C0Seq.pairingL_apply] using C0Seq.abs_tsum_mul_le w.1 z.2
  have hsecond : |C0Seq.pairingL z.1 w.2| ≤ ‖z.1‖ * ‖w.2‖ := by
    simpa only [C0Seq.pairingL_apply] using C0Seq.abs_tsum_mul_le z.1 w.2
  have htriangle := abs_add_le (C0Seq.pairingL w.1 z.2) (C0Seq.pairingL z.1 w.2)
  have hformula : C0Seq.symmetricForm w z =
      C0Seq.pairingL w.1 z.2 + C0Seq.pairingL z.1 w.2 :=
    C0Seq.symmetricForm_apply w.1 z.1 w.2 z.2
  change |C0Seq.symmetricForm w z| ≤ _
  rw [hformula]
  have hwpos : 0 ≤ ‖w.1‖ + ‖w.2‖ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hproduct := mul_le_mul_of_nonneg_left hz hwpos
  nlinarith [mul_nonneg (norm_nonneg w.1) (norm_nonneg z.1),
    mul_nonneg (norm_nonneg w.2) (norm_nonneg z.2)]

end Lorentz
