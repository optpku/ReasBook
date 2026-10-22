/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap23.Example_23_10

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: rewrite the law of `X` as the canonical Gaussian law via `hX` and apply
-- `cgf_gaussianReal`; for the standard normal parameters `μ = 0`, `v = 1`, the resulting
-- quadratic simplifies to `t^2 / 2`.
/-- The cumulant-generating function of a standard normal random variable is `t ↦ t^2 / 2`. -/
theorem cgf_eq_half_sq_of_hasLaw_standardNormal
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) (t : ℝ) :
    cgf X P t = t ^ 2 / 2 := by
  simpa using cgf_gaussianReal hX.map_eq t

/-- Helper for Example 23.4: every quadratic tilt `t * z - t^2 / 2` is bounded above by
`z^2 / 2`. -/
private lemma quadraticTilt_le_half_sq (t z : ℝ) :
    t * z - t ^ 2 / 2 ≤ z ^ 2 / 2 := by
  -- Proof comment: the textbook completed-square identity is equivalent to the nonnegativity of
  -- `(t - z)^2`.
  have hsquare : 0 ≤ (t - z) ^ 2 := sq_nonneg (t - z)
  nlinarith

/-- Helper for Example 23.4: the quadratic tilt attains the value `z^2 / 2` at the witness
`t = z`. -/
private lemma quadraticTilt_eq_half_sq_at_self (z : ℝ) :
    z * z - z ^ 2 / 2 = z ^ 2 / 2 := by
  -- Proof comment: expand the quadratic at the stationary point `t = z`.
  ring

-- Proof sketch: use `cgf_eq_half_sq_of_hasLaw_standardNormal` to rewrite the variational
-- expression as `sup_t (t z - t^2 / 2)`, then complete the square:
-- `t z - t^2 / 2 = z^2 / 2 - (t - z)^2 / 2`, whose supremum is attained at `t = z`.
/-- Example 23.4: if `X` has the standard normal law, then the Legendre transform of its
cumulant-generating function is `z ↦ z^2 / 2`. -/
theorem legendreCgfRateFunction_eq_half_sq_of_hasLaw_standardNormal
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) (z : ℝ) :
    legendreCgfRateFunction X P z = z ^ 2 / 2 := by
  apply le_antisymm
  · -- Proof comment: rewrite each affine summand using the standard-normal cgf and then apply
    -- the completed-square upper bound pointwise before taking the supremum.
    have hupper : legendreCgfRateFunction X P z ≤ (((z ^ 2 / 2 : ℝ)) : EReal) := by
      rw [legendreCgfRateFunction]
      refine sSup_le ?_
      rintro _ ⟨t, rfl⟩
      have hreal : t * z - cgf X P t ≤ z ^ 2 / 2 := by
        rw [cgf_eq_half_sq_of_hasLaw_standardNormal hX t]
        exact quadraticTilt_le_half_sq t z
      have hcast :
          (((t * z - cgf X P t : ℝ)) : EReal) ≤ (((z ^ 2 / 2 : ℝ)) : EReal) := by
        exact_mod_cast hreal
      simpa using hcast
    simpa using hupper
  · -- Proof comment: evaluate the supremum family at the witness `t = z`, where the quadratic
    -- reaches its maximal value `z^2 / 2`.
    have hpoint :
        (((z * z - cgf X P z : ℝ)) : EReal) ≤ legendreCgfRateFunction X P z := by
      rw [legendreCgfRateFunction]
      exact le_sSup ⟨z, rfl⟩
    have hwitness : (((z ^ 2 / 2 : ℝ)) : EReal) ≤ legendreCgfRateFunction X P z := by
      calc
        (((z ^ 2 / 2 : ℝ)) : EReal) = (((z * z - cgf X P z : ℝ)) : EReal) := by
          rw [cgf_eq_half_sq_of_hasLaw_standardNormal hX z]
          exact congrArg (fun y : ℝ ↦ (y : EReal)) (quadraticTilt_eq_half_sq_at_self z).symm
        _ ≤ legendreCgfRateFunction X P z := hpoint
    simpa using hwitness

end ProbabilityTheory
