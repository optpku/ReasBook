/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Topology.UnitInterval
import Mathlib.Data.NNReal.Defs
import Mathlib.Order.CompleteLatticeIntervals

open scoped unitInterval
open unitInterval

-- Declarations for this item will be appended below by the statement pipeline.

/-- Definition 2.44: the critical value `p_c` is the infimum of the percolation parameters
`p ∈ [0,1]` for which the origin-percolation probability `θ(p)` is strictly positive. We encode
`p_c` directly as a point of the canonical mathlib type `unitInterval`, so the empty-set case is
handled by `sInf ∅ = 1` in `[0,1]`. -/
noncomputable def criticalPercolationValue (theta : unitInterval → NNReal) : unitInterval :=
  sInf {p : unitInterval | 0 < theta p}

/-- The critical value is the infimum, inside `[0,1]`, of the parameters with positive
origin-percolation probability. -/
theorem criticalPercolationValue_def (theta : unitInterval → NNReal) :
    criticalPercolationValue theta = sInf {p : unitInterval | 0 < theta p} := rfl

-- Proof sketch: when the threshold set is nonempty, `Set.Icc.coe_sInf` identifies the coercion of
-- the defining infimum in `unitInterval` with the real infimum of its image in `ℝ`.
/-- If `θ` is strictly positive for some parameter in `[0,1]`, then the underlying real number of
the critical value is the infimum of the corresponding set of real parameter values. -/
theorem criticalPercolationValue_eq_sInf_theta_pos (theta : unitInterval → NNReal)
    (h_theta_pos : {p : unitInterval | 0 < theta p}.Nonempty) :
    (criticalPercolationValue theta : ℝ) =
      sInf ((↑) '' {p : unitInterval | 0 < theta p}) := by
  -- Coerce the subtype infimum in `[0,1]` to the corresponding real infimum.
  simpa [criticalPercolationValue_def]
    using
      (Set.Icc.coe_sInf (a := (0 : ℝ)) (b := (1 : ℝ)) zero_le_one
        (S := {p : unitInterval | 0 < theta p}) h_theta_pos)

-- Proof sketch: for monotone `θ`, the zero set in `[0,1]` is an initial segment and the positive
-- set is the complementary final segment, so they have the same boundary point.
/-- For a monotone origin-percolation probability `θ`, the critical value is also the supremum of
the parameters in `[0,1]` where `θ` vanishes. -/
theorem criticalPercolationValue_eq_sSup_theta_zero (theta : unitInterval → NNReal)
    (h_theta_mono : Monotone theta) :
    criticalPercolationValue theta = sSup {p : unitInterval | theta p = 0} := by
  let positiveSet : Set unitInterval := {p | 0 < theta p}
  let zeroSet : Set unitInterval := {p | theta p = 0}
  -- A zero of `θ` must lie below every parameter where `θ` is positive.
  have h_zero_le_positive :
      ∀ {z p : unitInterval}, z ∈ zeroSet → p ∈ positiveSet → z ≤ p := by
    intro z p hz hp
    have hz_zero : theta z = 0 := by
      simpa [zeroSet] using hz
    have hp_pos : 0 < theta p := by
      simpa [positiveSet] using hp
    by_contra hzp
    have hpz : p < z := lt_of_not_ge hzp
    have h_theta_le : theta p ≤ theta z := h_theta_mono hpz.le
    rw [hz_zero] at h_theta_le
    exact (not_lt_of_ge h_theta_le) hp_pos
  -- The supremum of the zero set is a lower bound for the positive set.
  have h_sup_le_inf : sSup zeroSet ≤ sInf positiveSet := by
    refine sSup_le ?_
    intro z hz
    refine le_sInf ?_
    intro p hp
    exact h_zero_le_positive hz hp
  -- A strict gap between the two boundaries would create a point belonging to neither side.
  have h_inf_le_sup : sInf positiveSet ≤ sSup zeroSet := by
    by_contra hlt
    have h_gap : sSup zeroSet < sInf positiveSet := lt_of_not_ge hlt
    obtain ⟨r, hr_sup, hr_inf⟩ := exists_between h_gap
    have hr_not_mem_positive : r ∉ positiveSet := by
      exact notMem_of_lt_csInf hr_inf (OrderBot.bddBelow positiveSet)
    have hr_theta_zero : theta r = 0 := by
      have hr_not_pos : ¬ 0 < theta r := by
        simpa [positiveSet] using hr_not_mem_positive
      exact le_antisymm (le_of_not_gt hr_not_pos) (zero_le _)
    have hr_mem_zero : r ∈ zeroSet := by
      simpa [zeroSet] using hr_theta_zero
    have hr_not_mem_zero : r ∉ zeroSet := by
      exact notMem_of_csSup_lt hr_sup (OrderTop.bddAbove zeroSet)
    exact hr_not_mem_zero hr_mem_zero
  -- The critical value is the common boundary of the zero set and the positive set.
  rw [criticalPercolationValue_def]
  simpa [positiveSet, zeroSet] using le_antisymm h_inf_le_sup h_sup_le_inf

-- Proof sketch: replace the condition `0 < theta p` by the equivalent condition `psi p = 1`, then
-- rewrite the defining threshold set of `criticalPercolationValue`.
/-- If `ψ(p) = 1` is equivalent to `θ(p) > 0` on `[0,1]`, then the critical value is the infimum
of the parameters where `ψ` equals `1`. -/
theorem criticalPercolationValue_eq_sInf_psi_one (theta psi : unitInterval → NNReal)
    (h_theta_psi : ∀ p : unitInterval, 0 < theta p ↔ psi p = 1) :
    criticalPercolationValue theta = sInf {p : unitInterval | psi p = 1} := by
  -- Rewrite the defining threshold set pointwise via the supplied equivalence.
  have h_threshold_sets :
      {p : unitInterval | 0 < theta p} = {p : unitInterval | psi p = 1} := by
    ext p
    exact h_theta_psi p
  rw [criticalPercolationValue_def, h_threshold_sets]

/-- Helper for Definition 2.44: a `{0,1}`-valued `NNReal` map is positive exactly at value `1`. -/
lemma psiPos_iff_eq_one_of_zeroOrOne (psi : unitInterval → NNReal)
    (h_psi_zero_or_one : ∀ p : unitInterval, psi p = 0 ∨ psi p = 1) :
    ∀ p : unitInterval, 0 < psi p ↔ psi p = 1 := by
  intro p
  rcases h_psi_zero_or_one p with hpsi_zero | hpsi_one
  · -- At a zero value, both positivity and equality to `1` are false.
    simp [hpsi_zero]
  · -- At value `1`, positivity and equality to `1` are both immediate.
    simp [hpsi_one]

-- Proof sketch: first rewrite the threshold set using `0 < theta p ↔ psi p = 1`; then use that a
-- monotone `{0,1}`-valued function has complementary zero and one sets whose common boundary is
-- the critical threshold.
/-- If `ψ` is monotone and takes only the values `0` and `1` on `[0,1]`, and if `ψ(p) = 1` is
equivalent to `θ(p) > 0`, then the critical value is also the supremum of the parameters where
`ψ` vanishes. -/
theorem criticalPercolationValue_eq_sSup_psi_zero (theta psi : unitInterval → NNReal)
    (h_theta_psi : ∀ p : unitInterval, 0 < theta p ↔ psi p = 1)
    (h_psi_mono : Monotone psi)
    (h_psi_zero_or_one : ∀ p : unitInterval, psi p = 0 ∨ psi p = 1) :
    criticalPercolationValue theta = sSup {p : unitInterval | psi p = 0} := by
  -- Rewrite `criticalPercolationValue theta` through the `{p | psi p = 1}` threshold.
  have h_psi_pos : ∀ p : unitInterval, 0 < psi p ↔ psi p = 1 :=
    psiPos_iff_eq_one_of_zeroOrOne psi h_psi_zero_or_one
  -- Route correction: reuse the monotone boundary theorem for `psi` instead of reproving it.
  calc
    criticalPercolationValue theta = sInf {p : unitInterval | psi p = 1} :=
      criticalPercolationValue_eq_sInf_psi_one theta psi h_theta_psi
    _ = criticalPercolationValue psi := by
      symm
      exact criticalPercolationValue_eq_sInf_psi_one psi psi h_psi_pos
    _ = sSup {p : unitInterval | psi p = 0} :=
      criticalPercolationValue_eq_sSup_theta_zero psi h_psi_mono
