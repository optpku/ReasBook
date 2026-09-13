/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedAssembly
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.DualPairing.MaximalExtension

/-!
# Concrete source witnesses for the S3 seed
-/

public section

namespace Lorentz

/-- The source direction is an explicit remote unit-difference base with
positive time one, small negative coordinate and bounded primal component. -/
theorem exists_seed_direction : ∃ v : parametrizedSubspace axisDirection,
    positiveCoordinate axisDirection seed_axis_ne_zero v = 1 ∧
    ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ < 1 / 64 ∧
    ‖(v : C0Seq × L1Seq).1‖ ≤ 5 := by
  have hε : (0 : ℝ) < 1 / 64 := by norm_num
  obtain ⟨r, hr, hsmall⟩ := exists_remote_unitDifference_norm_lt 1 2 (1 / 64) hε
  have hrone : r ≠ 1 := by omega
  refine ⟨axisSeedBase ((1 : ℝ) • unitDifference 1 r) 1, ?_, ?_, ?_⟩
  · exact positiveCoordinate_axisSeedBase _ _ _
  · rw [norm_negativeCoordinate_axisSeedBase r hrone,
      abs_one, one_mul, ← norm_intervalCoordinate_unitDifference]
    exact hsmall
  · simpa only [abs_one, mul_one] using norm_axisSeedBase_fst_le r hrone 1

/-- Twice a source direction lies strictly inside the radius-twelve primal ball. -/
theorem seed_anchor_primal_lt_twelve (v : parametrizedSubspace axisDirection)
    (hv : ‖(v : C0Seq × L1Seq).1‖ ≤ 5) :
    ‖(((2 : ℝ) • v : parametrizedSubspace axisDirection) : C0Seq × L1Seq).1‖ < 12 := by
  simp only [Submodule.coe_smul, Prod.smul_fst, norm_smul, Real.norm_eq_abs]
  norm_num
  linarith

/-- A scaled forward unit difference supplies the remote negative-energy
witness, without imposing a particular enumeration of rational times. -/
theorem exists_seed_negative_witness : ∃ z : parametrizedSubspace axisDirection,
    positiveCoordinate axisDirection seed_axis_ne_zero z = 0 ∧
    ‖negativeCoordinate axisDirection seed_axis_ne_zero z‖ < 1 / 64 ∧
    64 ≤ ‖(z : C0Seq × L1Seq).1‖ ∧ C0Seq.quadraticPairing z < 0 := by
  let t := rationalTime 2
  have ht : 0 < t := (rationalTime_mem_Ioo 2).1
  have htone : t < 1 := (rationalTime_mem_Ioo 2).2
  let L := 128 / t
  have hL : 0 < L := div_pos (by norm_num) ht
  have hscale : L * (t / 2) = 64 := by
    dsimp [L]
    field_simp
    ring
  have hε : 0 < min (t / 4) ((1 / 64) / L) :=
    lt_min (div_pos ht (by norm_num)) (div_pos (by norm_num) hL)
  obtain ⟨j, hj, hsmall⟩ := exists_remote_unitDifference_norm_lt 2 2 _ hε
  have hnorm := (lt_min_iff.mp hsmall).1
  have hscaled := (lt_div_iff₀ hL).mp (lt_min_iff.mp hsmall).2
  have hnonneg := norm_nonneg (L1Seq.intervalCoordinateOperator (unitDifference 2 j))
  have hsquare : ‖L1Seq.intervalCoordinateOperator (unitDifference 2 j)‖ ^ 2 =
      |rationalTime 2 - rationalTime j| := by
    rw [norm_intervalCoordinate_unitDifference, Real.sq_sqrt (abs_nonneg _)]
  have hclose : |rationalTime 2 - rationalTime j| < rationalTime 2 / 4 := by
    change |t - rationalTime j| < t / 4
    nlinarith
  have hp : C0Seq.pairingL axisDirection (unitDifference 2 j) = 0 := by
    rw [pairingL_unitDifference]
    have hjone : j ≠ 1 := by omega
    simp [axisDirection_apply, hjone]
  let h := unitDifferenceDetector axisDirection 2 j
  have hN : ‖negativeCoordinate axisDirection seed_axis_ne_zero h‖ =
      ‖L1Seq.intervalCoordinateOperator (unitDifference 2 j)‖ :=
    norm_negativeCoordinate_unitDifferenceDetector _ _ _ _ hp
  have hNpos : 0 < ‖negativeCoordinate axisDirection seed_axis_ne_zero h‖ := by
    rw [hN, norm_intervalCoordinate_unitDifference]
    apply Real.sqrt_pos.mpr
    apply abs_pos.mpr
    exact sub_ne_zero.mpr (rationalTime_injective.ne (ne_of_lt hj))
  refine ⟨L • h, ?_, ?_, ?_, ?_⟩
  · rw [map_smul, positiveCoordinate_unitDifferenceDetector _ _ _ _ hp]
    simp
  · rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hL, hN]
    nlinarith
  · have hx := unitDifferenceDetector_primal_norm_lower axisDirection 2 j hj hclose
    have hm := mul_lt_mul_of_pos_left hx hL
    rw [Submodule.coe_smul, Prod.smul_fst, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    change 64 ≤ L * ‖(h : C0Seq × L1Seq).1‖
    rw [hscale] at hm
    exact hm.le
  · rw [quadraticIdentity axisDirection seed_axis_ne_zero, map_smul,
      positiveCoordinate_unitDifferenceDetector _ _ _ _ hp, map_smul,
      norm_smul, Real.norm_eq_abs, abs_of_pos hL]
    simp only [smul_eq_mul, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_sub]
    have hprod : 0 < L * ‖negativeCoordinate axisDirection seed_axis_ne_zero h‖ := mul_pos hL hNpos
    nlinarith [sq_pos_of_pos hprod]

/-- The concrete S3 construction supplies a monotone seed with a negative
energy witness, a radius-twelve interior anchor, carrier-contained polar,
and nonnegative polar energy throughout the primal radius-sixteen ball. -/
theorem exists_S3_seed : ∃ S : Set (C0Seq × L1Seq),
    C0Seq.coordinateDualPairing.IsMonotone S ∧
    (∃ z ∈ S, C0Seq.quadraticPairing z < 0) ∧
    (∃ y ∈ S, ‖y.1‖ < 12) ∧
    C0Seq.monotonePolar S ⊆ parametrizedSubspace axisDirection ∧
    (∀ w ∈ C0Seq.monotonePolar S, ‖w.1‖ < 16 → 0 ≤ C0Seq.quadraticPairing w) := by
  obtain ⟨z, hzP, hzN, hzX, hzneg⟩ := exists_seed_negative_witness
  obtain ⟨v, hvP, hvN, hvX⟩ := exists_seed_direction
  refine ⟨assembledSeed z v, assembledSeed_isMonotone z v hzP hvP hzN.le hvN.le,
    ?_, ?_, assembledSeed_polar_subset_carrier z v, ?_⟩
  · exact ⟨z, seed_base_mem z v, hzneg⟩
  · exact ⟨((2 : ℝ) • v : parametrizedSubspace axisDirection),
      seed_anchor_mem z v, seed_anchor_primal_lt_twelve v hvX⟩
  · intro w hw hnorm
    exact assembledSeed_polar_local_nonneg z v hzP hvP hzN.le hvN.le hzX hvX w hw hnorm

/-- A maximal extension of the concrete S3 seed retains its negative witness,
interior anchor and local nonnegative energy condition. -/
theorem exists_S3_maximal_graph : ∃ G : Set (C0Seq × L1Seq),
    Maximal C0Seq.coordinateDualPairing.IsMonotone G ∧
    (∃ z ∈ G, C0Seq.quadraticPairing z < 0) ∧
    (∃ y ∈ G, ‖y.1‖ < 12) ∧
    (∀ w ∈ G, ‖w.1‖ < 16 → 0 ≤ C0Seq.quadraticPairing w) := by
  obtain ⟨S, hS, hz, hy, _, hlocal⟩ := exists_S3_seed
  obtain ⟨G, hSG, hG⟩ := C0Seq.coordinateDualPairing.exists_maximal_monotone_superset hS
  have hpolar : G ⊆ C0Seq.monotonePolar S := by
    intro w hw
    have hwp := (C0Seq.coordinateDualPairing.isMonotone_iff_subset_polar G).mp hG.1 hw
    rw [C0Seq.coordinateDualPairing.mem_monotonePolar] at hwp
    rw [C0Seq.mem_monotonePolar]
    intro z hz
    rw [C0Seq.quadraticPairing_eq_coordinateQuadratic]
    exact hwp z (hSG hz)
  refine ⟨G, hG, ?_, ?_, ?_⟩
  · obtain ⟨z, hzS, hneg⟩ := hz
    exact ⟨z, hSG hzS, hneg⟩
  · obtain ⟨y, hyS, hnorm⟩ := hy
    exact ⟨y, hSG hyS, hnorm⟩
  · intro w hw hnorm
    exact hlocal w (hpolar hw) hnorm

end Lorentz
