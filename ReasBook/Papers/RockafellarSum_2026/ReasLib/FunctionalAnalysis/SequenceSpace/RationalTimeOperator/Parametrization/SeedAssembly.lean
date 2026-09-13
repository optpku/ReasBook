/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SeedComparisons
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.SamePositiveCoordinate
public import RockafellarSum_2026.ReasLib.FunctionalAnalysis.SequenceSpace.RationalTimeOperator.Parametrization.LorentzCoordinates.Kernel

/-!
# Assembly of the S3 monotone seed

The detector sequence is fixed. Only the two source witnesses remain parameters.
-/

public section

open Filter Topology

namespace Lorentz

/-- The full source seed with the actual scheduled detector points. -/
def assembledSeed (z v : parametrizedSubspace axisDirection) : Set (C0Seq × L1Seq) :=
  {w | (∃ p : ℝ, p ≤ 1 / 2 ∧ w = (z + p • v : parametrizedSubspace axisDirection)) ∨
    (∃ n : ℕ, w = (seedPoint n : C0Seq × L1Seq)) ∨
    w = ((2 : ℝ) • v : parametrizedSubspace axisDirection)}

/-- The time-zero witness belongs to the assembled source seed. -/
theorem seed_base_mem (z v : parametrizedSubspace axisDirection) :
    (z : C0Seq × L1Seq) ∈ assembledSeed z v := by
  refine Or.inl ⟨0, ?_, ?_⟩
  · norm_num
  · simp

/-- The twice-direction anchor belongs to every assembled source seed. -/
theorem seed_anchor_mem (z v : parametrizedSubspace axisDirection) :
    (((2 : ℝ) • v : parametrizedSubspace axisDirection) : C0Seq × L1Seq) ∈
      assembledSeed z v := by
  exact Or.inr (Or.inr rfl)

/-- The full seed polar is contained in the carrier. -/
theorem assembledSeed_polar_subset_carrier (z v : parametrizedSubspace axisDirection) :
    C0Seq.monotonePolar (assembledSeed z v) ⊆ parametrizedSubspace axisDirection := by
  apply polar_subset_axisCarrier_of_seedPoint_mem
  intro n
  exact Or.inr (Or.inl ⟨n, rfl⟩)

/-- A Lorentz norm comparison implies nonnegative ambient difference pairing. -/
theorem seed_pairing_nonneg_of_norm_bound (a b : parametrizedSubspace axisDirection)
    (h : ‖negativeCoordinate axisDirection seed_axis_ne_zero a -
      negativeCoordinate axisDirection seed_axis_ne_zero b‖ ≤
      |positiveCoordinate axisDirection seed_axis_ne_zero a -
        positiveCoordinate axisDirection seed_axis_ne_zero b|) :
    0 ≤ C0Seq.quadraticPairing ((a : C0Seq × L1Seq) - (b : C0Seq × L1Seq)) := by
  rw [← Submodule.coe_sub, quadraticIdentity axisDirection seed_axis_ne_zero, map_sub, map_sub]
  have hs := (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mpr h
  rw [sq_abs] at hs
  linarith

/-- The source's five pair comparisons assemble into full seed monotonicity. -/
theorem assembledSeed_isMonotone (z v : parametrizedSubspace axisDirection)
    (hzP : positiveCoordinate axisDirection seed_axis_ne_zero z = 0)
    (hvP : positiveCoordinate axisDirection seed_axis_ne_zero v = 1)
    (hzN : ‖negativeCoordinate axisDirection seed_axis_ne_zero z‖ ≤ 1 / 64)
    (hvN : ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ ≤ 1 / 64) :
    C0Seq.coordinateDualPairing.IsMonotone (assembledSeed z v) := by
  have hhalf (p q : ℝ) : 0 ≤ C0Seq.quadraticPairing
      (((z + p • v : parametrizedSubspace axisDirection) : C0Seq × L1Seq) -
        (z + q • v : parametrizedSubspace axisDirection)) := by
    apply seed_pairing_nonneg_of_norm_bound
    simpa only [map_add, map_smul, hzP, hvP, smul_eq_mul, mul_one, zero_add] using
      seed_halfLine_pair_bound z v hvN p q
  have hhd (p : ℝ) (hp : p ≤ 1 / 2) (n : ℕ) : 0 ≤ C0Seq.quadraticPairing
      (((z + p • v : parametrizedSubspace axisDirection) : C0Seq × L1Seq) - seedPoint n) := by
    apply seed_pairing_nonneg_of_norm_bound
    simpa only [map_add, map_smul, hzP, hvP, smul_eq_mul, mul_one, zero_add,
      positiveCoordinate_seedPoint] using seed_halfLine_detector_bound z v hzN hvN p hp n
  have hha (p : ℝ) (hp : p ≤ 1 / 2) : 0 ≤ C0Seq.quadraticPairing
      (((z + p • v : parametrizedSubspace axisDirection) : C0Seq × L1Seq) -
        ((2 : ℝ) • v : parametrizedSubspace axisDirection)) := by
    apply seed_pairing_nonneg_of_norm_bound
    simpa only [map_add, map_smul, hzP, hvP, smul_eq_mul, mul_one, zero_add] using
      seed_halfLine_anchor_bound z v hzN hvN p hp
  have hda (n : ℕ) : 0 ≤ C0Seq.quadraticPairing
      ((seedPoint n : C0Seq × L1Seq) - ((2 : ℝ) • v : parametrizedSubspace axisDirection)) := by
    apply seed_pairing_nonneg_of_norm_bound
    simpa only [map_smul, hvP, smul_eq_mul, mul_one, positiveCoordinate_seedPoint] using
      seed_detector_anchor_bound v hvN n
  apply (C0Seq.coordinateDualPairing.isMonotone_iff_subset_polar _).2
  intro a ha
  rw [C0Seq.coordinateDualPairing.mem_monotonePolar]
  intro b hb
  rw [← C0Seq.quadraticPairing_eq_coordinateQuadratic]
  rcases ha with ⟨p, hp, rfl⟩ | ⟨i, rfl⟩ | rfl
  · rcases hb with ⟨q, hq, rfl⟩ | ⟨j, rfl⟩ | rfl
    · exact hhalf p q
    · exact hhd p hp j
    · exact hha p hp
  · rcases hb with ⟨q, hq, rfl⟩ | ⟨j, rfl⟩ | rfl
    · rw [C0Seq.quadraticPairing.map_sub]
      exact hhd q hq i
    · exact quadraticPairing_seedPoint_sub_nonneg i j
    · exact hda i
  · rcases hb with ⟨q, hq, rfl⟩ | ⟨j, rfl⟩ | rfl
    · rw [C0Seq.quadraticPairing.map_sub]
      exact hha q hq
    · rw [C0Seq.quadraticPairing.map_sub]
      exact hda j
    · simp

/-- Compatibility with the scheduled points forces the limiting Lorentz cone
bound and hence the source right-side energy lower bound. -/
theorem seedPoint_polar_energy_lower_bound (w : parametrizedSubspace axisDirection)
    (hw : ∀ n, 0 ≤ C0Seq.quadraticPairing
      ((w : C0Seq × L1Seq) - (seedPoint n : C0Seq × L1Seq))) :
    2 * positiveCoordinate axisDirection seed_axis_ne_zero w - 1 ≤
      C0Seq.quadraticPairing w := by
  have hineq (n : ℕ) :
      ‖negativeCoordinate axisDirection seed_axis_ne_zero w -
        negativeCoordinate axisDirection seed_axis_ne_zero (seedPoint n)‖ ^ 2 ≤
      (positiveCoordinate axisDirection seed_axis_ne_zero w - seedTime n) ^ 2 := by
    have h := hw n
    rw [← Submodule.coe_sub, quadraticIdentity axisDirection seed_axis_ne_zero,
      map_sub, map_sub, positiveCoordinate_seedPoint] at h
    linarith
  have hcN : Tendsto (fun _ : ℕ ↦ negativeCoordinate axisDirection seed_axis_ne_zero w)
      atTop (𝓝 (negativeCoordinate axisDirection seed_axis_ne_zero w)) := tendsto_const_nhds
  have hcP : Tendsto (fun _ : ℕ ↦ positiveCoordinate axisDirection seed_axis_ne_zero w)
      atTop (𝓝 (positiveCoordinate axisDirection seed_axis_ne_zero w)) := tendsto_const_nhds
  have hN := ((hcN.sub negativeCoordinate_seedPoint_tendsto_zero).norm).pow 2
  have hP := (hcP.sub seedTime_tendsto_one).pow 2
  have hlim := le_of_tendsto_of_tendsto' hN hP hineq
  simp only [sub_zero] at hlim
  rw [quadraticIdentity axisDirection seed_axis_ne_zero]
  nlinarith

/-- A polar point with positive coordinate at most one half lies on the seed
half-line, by comparison with the point of the same positive coordinate. -/
theorem assembledSeed_polar_left_rigidity (z v w : parametrizedSubspace axisDirection)
    (hzP : positiveCoordinate axisDirection seed_axis_ne_zero z = 0)
    (hvP : positiveCoordinate axisDirection seed_axis_ne_zero v = 1)
    (hw : (w : C0Seq × L1Seq) ∈ C0Seq.monotonePolar (assembledSeed z v))
    (hp : positiveCoordinate axisDirection seed_axis_ne_zero w ≤ 1 / 2) :
    w = z + positiveCoordinate axisDirection seed_axis_ne_zero w • v := by
  let p := positiveCoordinate axisDirection seed_axis_ne_zero w
  have hmem : ((z + p • v : parametrizedSubspace axisDirection) : C0Seq × L1Seq) ∈
      assembledSeed z v := Or.inl ⟨p, hp, rfl⟩
  have hquad := (C0Seq.mem_monotonePolar _ _).mp hw _ hmem
  have hsame : positiveCoordinate axisDirection seed_axis_ne_zero w =
      positiveCoordinate axisDirection seed_axis_ne_zero (z + p • v) := by
    rw [map_add, map_smul, hzP, hvP]
    simp only [smul_eq_mul, mul_one, zero_add, p]
  have hN := sameP_rigidity axisDirection seed_axis_ne_zero w (z + p • v) hsame hquad
  have hzero : negativeCoordinate axisDirection seed_axis_ne_zero (w - (z + p • v)) = 0 := by
    rw [map_sub, hN, sub_self]
  exact sub_eq_zero.mp (eq_zero_of_negativeCoordinate_eq_zero _ _ _ hzero)

/-- Negative energy on the seed half-line confines its scalar parameter to
the source interval of radius one sixty-third. -/
theorem seed_halfLine_negative_parameter_bound (z v : parametrizedSubspace axisDirection)
    (hzP : positiveCoordinate axisDirection seed_axis_ne_zero z = 0)
    (hvP : positiveCoordinate axisDirection seed_axis_ne_zero v = 1)
    (hzN : ‖negativeCoordinate axisDirection seed_axis_ne_zero z‖ ≤ 1 / 64)
    (hvN : ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ ≤ 1 / 64)
    (p : ℝ) (hneg : C0Seq.quadraticPairing
      (z + p • v : parametrizedSubspace axisDirection) < 0) : |p| < 1 / 63 := by
  rw [quadraticIdentity axisDirection seed_axis_ne_zero, map_add, map_smul, hzP, hvP] at hneg
  simp only [smul_eq_mul, mul_one, zero_add] at hneg
  have hsq : p ^ 2 < ‖negativeCoordinate axisDirection seed_axis_ne_zero (z + p • v)‖ ^ 2 := by
    linarith
  have hab : |p| < ‖negativeCoordinate axisDirection seed_axis_ne_zero (z + p • v)‖ := by
    have hs : |p| ^ 2 < ‖negativeCoordinate axisDirection seed_axis_ne_zero (z + p • v)‖ ^ 2 := by
      simpa only [sq_abs] using hsq
    exact (sq_lt_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hs
  rw [map_add, map_smul] at hab
  have ht := norm_add_le (negativeCoordinate axisDirection seed_axis_ne_zero z)
    (p • negativeCoordinate axisDirection seed_axis_ne_zero v)
  rw [norm_smul, Real.norm_eq_abs] at ht
  have hm := mul_le_mul_of_nonneg_left hvN (abs_nonneg p)
  nlinarith

/-- The source primal separation and small Lorentz bounds force local
nonnegative energy throughout the full seed polar. -/
theorem assembledSeed_polar_local_nonneg (z v : parametrizedSubspace axisDirection)
    (hzP : positiveCoordinate axisDirection seed_axis_ne_zero z = 0)
    (hvP : positiveCoordinate axisDirection seed_axis_ne_zero v = 1)
    (hzN : ‖negativeCoordinate axisDirection seed_axis_ne_zero z‖ ≤ 1 / 64)
    (hvN : ‖negativeCoordinate axisDirection seed_axis_ne_zero v‖ ≤ 1 / 64)
    (hzX : 64 ≤ ‖(z : C0Seq × L1Seq).1‖)
    (hvX : ‖(v : C0Seq × L1Seq).1‖ ≤ 5)
    (w : C0Seq × L1Seq) (hw : w ∈ C0Seq.monotonePolar (assembledSeed z v))
    (hx : ‖w.1‖ < 16) : 0 ≤ C0Seq.quadraticPairing w := by
  let wC : parametrizedSubspace axisDirection := ⟨w, assembledSeed_polar_subset_carrier z v hw⟩
  have hcompat (n : ℕ) : 0 ≤ C0Seq.quadraticPairing
      (w - (seedPoint n : C0Seq × L1Seq)) :=
    (C0Seq.mem_monotonePolar _ _).mp hw _ (Or.inr (Or.inl ⟨n, rfl⟩))
  have henergy := seedPoint_polar_energy_lower_bound wC hcompat
  by_contra hnot
  have hneg : C0Seq.quadraticPairing w < 0 := lt_of_not_ge hnot
  have hp : positiveCoordinate axisDirection seed_axis_ne_zero wC ≤ 1 / 2 := by
    change 2 * positiveCoordinate axisDirection seed_axis_ne_zero wC - 1 ≤
      C0Seq.quadraticPairing w at henergy
    linarith
  have heq := assembledSeed_polar_left_rigidity z v wC hzP hvP hw hp
  let p := positiveCoordinate axisDirection seed_axis_ne_zero wC
  have hn : C0Seq.quadraticPairing (z + p • v : parametrizedSubspace axisDirection) < 0 := by
    rw [← heq]
    exact hneg
  have hab := seed_halfLine_negative_parameter_bound z v hzP hvP hzN hvN p hn
  have heqX : w.1 = (z : C0Seq × L1Seq).1 + p • (v : C0Seq × L1Seq).1 :=
    congrArg (fun a : parametrizedSubspace axisDirection ↦ (a : C0Seq × L1Seq).1) heq
  have ht := norm_sub_le w.1 (p • (v : C0Seq × L1Seq).1)
  have hsub : w.1 - p • (v : C0Seq × L1Seq).1 = (z : C0Seq × L1Seq).1 := by
    rw [heqX]
    abel
  rw [hsub, norm_smul, Real.norm_eq_abs] at ht
  have hm := mul_le_mul_of_nonneg_left hvX (abs_nonneg p)
  nlinarith

end Lorentz
