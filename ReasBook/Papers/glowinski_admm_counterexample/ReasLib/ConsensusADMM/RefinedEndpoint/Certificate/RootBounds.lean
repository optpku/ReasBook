/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Certificate.RootData

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

open ADMM.RefinedEndpoint

noncomputable def halfAngle (n : ℕ) : ℝ := Real.pi / 2 ^ (n + 1)

theorem halfAngle_nonneg (n : ℕ) : 0 ≤ halfAngle n :=
  div_nonneg Real.pi_pos.le (pow_nonneg (by norm_num) _)

theorem halfAngle_le_pi (n : ℕ) : halfAngle n ≤ Real.pi := by
  exact div_le_self Real.pi_pos.le (one_le_pow₀ (by norm_num))

theorem halfAngle_succ (n : ℕ) : halfAngle (n + 1) = halfAngle n / 2 := by
  unfold halfAngle
  rw [pow_succ]
  ring

theorem halfBox_zero : halfBox 0 = RootBox.point 0 1 := by decide +kernel
theorem rootBox_zero : rootBox 0 = RootBox.point 1 0 := by decide +kernel

/-- Each stored half-angle enclosure is justified by its checked rational
square inequalities and the positive trigonometric half-angle formulas. -/
theorem halfBoxes_sound (n : ℕ) (hn : n < 9) :
    (halfBox n).re.Contains (Real.cos (halfAngle n)) ∧
    (halfBox n).im.Contains (Real.sin (halfAngle n)) := by
  induction n with
  | zero =>
      rw [halfBox_zero]
      norm_num [halfAngle, RootBox.point, RatInterval.Contains, RatInterval.point]
  | succ n ih =>
      have hn8 : n < 8 := by omega
      have hprev := ih (by omega)
      have hcheck := halfSteps_valid ⟨n, hn8⟩
      rw [halfAngle_succ]
      exact halfAngleCheck_sound (halfAngle_nonneg n) (halfAngle_le_pi n) hprev.1 hcheck

theorem primitive_root_enclosed : (halfBox 8).Contains (root 1) := by
  have h := halfBoxes_sound 8 (by decide)
  constructor
  · rw [root_one_re]
    convert h.1 using 1 <;> norm_num [halfAngle]
  · rw [root_one_im]
    convert h.2 using 1 <;> norm_num [halfAngle]

/-- The complete table contains the actual roots, not merely numerical samples.
Every rounded multiplication step was checked by the Lean kernel. -/
theorem rootBoxes_sound (k : ℕ) (hk : k < 1024) : (rootBox k).Contains (root k) := by
  induction k with
  | zero =>
      rw [rootBox_zero, root_zero]
      norm_num [RootBox.Contains, RootBox.point, RatInterval.Contains, RatInterval.point]
  | succ k ih =>
      have hk' : k < 1023 := by omega
      rw [root_succ]
      exact (primitive_root_enclosed.mul (ih (by omega))).weaken (rootSteps_valid ⟨k, hk'⟩)

/-- All 75 actual Fourier modes at every phase are enclosed by the common table. -/
theorem phase_enclosed (h : Period1024.Coordinate) (i : Period1024.Phase) :
    (rootBox ((Period1024.mode h * i.val) % 1024)).Contains (Period1024.phase h i) := by
  have hp := phase_eq_root h i.val
  simp only [ZMod.natCast_zmod_val] at hp
  rw [hp]
  exact rootBoxes_sound _ (Nat.mod_lt _ (by decide))

end ConsensusADMM.RefinedEndpoint.Certificate
