/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

namespace ProbabilityTheory

/-- The mean-field energy per particle in the Weiss ferromagnet with external field `h`. -/
def weissMeanFieldEnergy (h m : ℝ) : ℝ :=
  -((m ^ 2) / 2) - h * m

/-- The binary entropy term associated with a magnetization value `m`. -/
def weissEntropy (m : ℝ) : ℝ :=
  -((1 + m) / 2) * Real.log ((1 + m) / 2) -
    ((1 - m) / 2) * Real.log ((1 - m) / 2)

/-- The Weiss free energy per particle at inverse temperature `β` and external field `h`. -/
def weissFreeEnergy (β h m : ℝ) : ℝ :=
  weissMeanFieldEnergy h m - β⁻¹ * weissEntropy m

-- Proof sketch: unfold `weissFreeEnergy`, `weissMeanFieldEnergy`, and `weissEntropy`, then
-- simplify the signs in the entropy contribution.
/-- The Weiss free energy is the mean-field energy plus the inverse-temperature weighted entropy
term written in logarithmic form. -/
theorem weissFreeEnergy_def (β h m : ℝ) :
    weissFreeEnergy β h m =
      -((m ^ 2) / 2) - h * m +
        β⁻¹ * (((1 + m) / 2) * Real.log ((1 + m) / 2) +
          ((1 - m) / 2) * Real.log ((1 - m) / 2)) := by
  -- Expand the definitions so the entropy contribution can be normalized algebraically.
  unfold weissFreeEnergy weissMeanFieldEnergy weissEntropy
  ring

-- Proof sketch: the stationary-point equation is `-m - h + β⁻¹ * Real.artanh m = 0`. Multiply by
-- `β`, rewrite it as `Real.artanh m = β * (m + h)`, then apply `Real.tanh` and use
-- `Real.tanh_artanh hm`; the converse uses `Real.artanh_tanh`.
/-- Example 23.20: for `m ∈ (-1,1)` and positive inverse temperature `β`, the stationary-point
equation for the Weiss free energy is equivalent to the mean-field fixed-point equation
`m = tanh (β (m + h))`. -/
theorem weissFreeEnergy_stationary_iff {β h m : ℝ} (hβ : 0 < β)
    (hm : m ∈ Set.Ioo (-1 : ℝ) 1) :
    (-m - h + β⁻¹ * Real.artanh m = 0) ↔
      m = Real.tanh (β * (m + h)) := by
  have hβ0 : β ≠ 0 := ne_of_gt hβ
  constructor
  · intro hs
    have hartanh : Real.artanh m = β * (m + h) := by
      -- Normalize the stationary equation before using the inverse hyperbolic API.
      field_simp [hβ0] at hs
      linarith
    -- Transport the normalized identity through `Real.tanh`.
    calc
      m = Real.tanh (Real.artanh m) := by simpa using (Real.tanh_artanh hm).symm
      _ = Real.tanh (β * (m + h)) := by rw [hartanh]
  · intro hs
    have hartanh : Real.artanh m = β * (m + h) := by
      -- Apply `Real.artanh` to the fixed-point equation to return to the linear form.
      calc
        Real.artanh m = Real.artanh (Real.tanh (β * (m + h))) := congrArg Real.artanh hs
        _ = β * (m + h) := by rw [Real.artanh_tanh]
    -- Rewrite the stationary equation back from the normalized `artanh` form.
    calc
      -m - h + β⁻¹ * Real.artanh m = -m - h + β⁻¹ * (β * (m + h)) := by rw [hartanh]
      _ = 0 := by
        field_simp [hβ0]
        ring

-- Proof sketch: solve the linearized equation `m = β * (m + h)` by rearranging terms to
-- `(β⁻¹ - 1) * m = h` and dividing by `β⁻¹ - 1`.
/-- The linearized Weiss equation gives the Curie-Weiss response formula away from the critical
inverse temperature `β = 1`. -/
theorem weissLinearizedEquation_iff {β h m : ℝ} (hβ0 : β ≠ 0) (hβ1 : β ≠ 1) :
    m = β * (m + h) ↔ m = h / (β⁻¹ - 1) := by
  -- Route correction: the linearized response law must exclude `β = 0` before dividing by `β`.
  have hden : β⁻¹ - 1 ≠ 0 := by
    intro hzero
    have hinv : β⁻¹ = 1 := by linarith
    exact hβ1 (inv_eq_one.mp hinv)
  constructor
  · intro hs
    rw [eq_div_iff hden]
    have hscaled : β⁻¹ * m = m + h := by
      -- Divide the fixed-point equation by `β` to isolate the affine term.
      have hs' : β⁻¹ * m = β⁻¹ * (β * (m + h)) := congrArg (fun x ↦ β⁻¹ * x) hs
      calc
        β⁻¹ * m = β⁻¹ * (β * (m + h)) := hs'
        _ = (β⁻¹ * β) * (m + h) := by ring
        _ = m + h := by rw [inv_mul_cancel₀ hβ0, one_mul]
    -- Repackage the scaled equation into the quotient denominator from the statement.
    calc
      m * (β⁻¹ - 1) = m * β⁻¹ - m := by ring
      _ = β⁻¹ * m - m := by rw [mul_comm]
      _ = (m + h) - m := by rw [hscaled]
      _ = h := by ring
  · intro hs
    rw [eq_div_iff hden] at hs
    have hscaled : β⁻¹ * m = m + h := by
      -- Expand the denominator equation back into the linearized affine form.
      calc
        β⁻¹ * m = m * β⁻¹ := by rw [mul_comm]
        _ = m * (β⁻¹ - 1) + m := by ring
        _ = h + m := by rw [hs]
        _ = m + h := by ring
    -- Multiply by `β` to recover the original linearized fixed-point equation.
    calc
      m = (β * β⁻¹) * m := by rw [mul_inv_cancel₀ hβ0, one_mul]
      _ = β * (β⁻¹ * m) := by ring
      _ = β * (m + h) := by rw [hscaled]

end ProbabilityTheory
