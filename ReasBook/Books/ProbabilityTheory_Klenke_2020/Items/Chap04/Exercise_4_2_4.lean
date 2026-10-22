/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set
open scoped Topology

-- Proof sketch: use the regularity of Lebesgue measure to choose an open set `U ⊇ A` with
-- `volume (U \ A) < ε / 2` and a compact set `C ⊆ A` with `volume (A \ C) < ε / 2`. Let
-- `D := Uᶜ`, so `D` is closed and contained in `Aᶜ`. Apply
-- `exists_continuous_one_zero_of_isCompact` to the disjoint compact/closed pair `C` and `D` to
-- obtain a continuous cutoff `φ` with values in `[0, 1]` and `1_C ≤ φ ≤ 1_{ℝ \ D}`. The
-- pointwise sandwich bounds reduce the `L¹` error to the two regularity errors.
/-- Exercise 4.2.4: every Borel set `A ⊆ ℝ` of finite Lebesgue measure admits a compact subset
`C ⊆ A`, a closed set `D ⊆ Aᶜ`, and a continuous cutoff `φ` with values in `[0, 1]` such that
`1_C ≤ φ ≤ 1_{ℝ \ D}` and the `L¹` distance between `1_A` and `φ` is less than `ε`. -/
theorem exists_compact_closed_continuous_indicator_l1_sub_lt
    {A : Set ℝ} (hA : MeasurableSet A) (hA_fin : volume A < ⊤)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (C D : Set ℝ) (φ : C(ℝ, ℝ)),
      IsCompact C ∧
        C ⊆ A ∧
        IsClosed D ∧
        D ⊆ Aᶜ ∧
        EqOn φ 1 C ∧
        EqOn φ 0 D ∧
        (∀ x, φ x ∈ Set.Icc (0 : ℝ) 1) ∧
        (∫ x, |A.indicator (fun _ ↦ (1 : ℝ)) x - φ x| ∂volume) < ε := by
  have hε_half : 0 < ε / 2 := by linarith
  have hε_half_ne : ENNReal.ofReal (ε / 2) ≠ 0 := by
    simpa [ENNReal.ofReal_ne_zero_iff] using hε_half
  obtain ⟨C, hCA, hC_compact, hC_lt⟩ :=
    hA.exists_isCompact_diff_lt hA_fin.ne hε_half_ne
  obtain ⟨U, hAU, hU_open, hU_fin, hU_lt⟩ :=
    hA.exists_isOpen_diff_lt hA_fin.ne hε_half_ne
  obtain ⟨φ, hφC, hφD, hφ_compactSupport, hφ_range⟩ :=
    exists_continuous_one_zero_of_isCompact hC_compact hU_open.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hCA.trans hAU))
  have hA_indicator_int : Integrable (A.indicator (fun _ ↦ (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hA]
    exact integrableOn_const hA_fin.ne
  have hφ_int : Integrable φ volume :=
    φ.continuous.integrable_of_hasCompactSupport hφ_compactSupport
  have hAC_meas : MeasurableSet (A \ C) :=
    hA.diff hC_compact.isClosed.measurableSet
  have hUA_meas : MeasurableSet (U \ A) :=
    hU_open.measurableSet.diff hA
  have hAC_fin : volume (A \ C) ≠ ⊤ :=
    (measure_mono diff_subset).trans_lt hA_fin |>.ne
  have hUA_fin : volume (U \ A) ≠ ⊤ :=
    (measure_mono diff_subset).trans_lt hU_fin |>.ne
  have hAC_int : Integrable ((A \ C).indicator (fun _ ↦ (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hAC_meas]
    exact integrableOn_const hAC_fin
  have hUA_int : Integrable ((U \ A).indicator (fun _ ↦ (1 : ℝ))) volume := by
    rw [integrable_indicator_iff hUA_meas]
    exact integrableOn_const hUA_fin
  have h_bound :
      ∀ x,
        |A.indicator (fun _ ↦ (1 : ℝ)) x - φ x| ≤
          (A \ C).indicator (fun _ ↦ (1 : ℝ)) x + (U \ A).indicator (fun _ ↦ (1 : ℝ)) x := by
    intro x
    by_cases hxA : x ∈ A
    · by_cases hxC : x ∈ C
      · simp [hxA, hxC, hφC hxC]
      · have hφx_le : φ x ≤ 1 := (hφ_range x).2
        have hφx_nonneg : 0 ≤ φ x := (hφ_range x).1
        have habs : |1 - φ x| ≤ 1 := by
          rw [abs_of_nonneg (sub_nonneg.mpr hφx_le)]
          linarith
        simpa [hxA, hxC] using habs
    · by_cases hxU : x ∈ U
      · have hφx_nonneg : 0 ≤ φ x := (hφ_range x).1
        have habs : |0 - φ x| ≤ 1 := by
          rw [zero_sub, abs_neg, abs_of_nonneg hφx_nonneg]
          exact (hφ_range x).2
        simpa [hxA, hxU] using habs
      · have hφx : φ x = 0 := hφD hxU
        simp [hxA, hxU, hφx]
  have h_rhs_int :
      Integrable
        (fun x ↦
          (A \ C).indicator (fun _ ↦ (1 : ℝ)) x +
            (U \ A).indicator (fun _ ↦ (1 : ℝ)) x) volume :=
    hAC_int.add hUA_int
  have hC_real_lt : volume.real (A \ C) < ε / 2 :=
    ENNReal.toReal_lt_of_lt_ofReal hC_lt
  have hU_real_lt : volume.real (U \ A) < ε / 2 :=
    ENNReal.toReal_lt_of_lt_ofReal hU_lt
  refine ⟨C, Uᶜ, φ, hC_compact, hCA, hU_open.isClosed_compl, compl_subset_compl.mpr hAU, hφC,
    hφD, hφ_range, ?_⟩
  calc
    ∫ x, |A.indicator (fun _ ↦ (1 : ℝ)) x - φ x| ∂volume
        ≤ ∫ x,
            ((A \ C).indicator (fun _ ↦ (1 : ℝ)) x +
              (U \ A).indicator (fun _ ↦ (1 : ℝ)) x) ∂volume :=
      integral_mono (hA_indicator_int.sub hφ_int).norm h_rhs_int h_bound
    _ = volume.real (A \ C) + volume.real (U \ A) := by
      rw [integral_add hAC_int hUA_int]
      congr 1
      · simpa using
          (integral_indicator_one hAC_meas :
            ∫ x, (A \ C).indicator (fun _ ↦ (1 : ℝ)) x ∂volume = volume.real (A \ C))
      · simpa using
          (integral_indicator_one hUA_meas :
            ∫ x, (U \ A).indicator (fun _ ↦ (1 : ℝ)) x ∂volume = volume.real (U \ A))
    _ < ε := by linarith
