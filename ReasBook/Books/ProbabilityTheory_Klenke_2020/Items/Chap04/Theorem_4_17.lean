/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

-- Proof sketch: this is the canonical homogeneity formula for the real-valued `L¹` seminorm,
-- given by `MeasureTheory.lpNorm_const_smul` at exponent `1`.
/-- Theorem 4.17 (1): The real-valued `L¹` seminorm is homogeneous:
`‖α f‖₁ = |α| ‖f‖₁`. In particular, this holds on `ℒ¹(μ)`. -/
theorem l1_seminorm_smul {f : Ω → ℝ} (α : ℝ) :
    lpNorm (α • f) 1 μ = |α| * lpNorm f 1 μ := by
  simpa using
    (lpNorm_const_smul α f μ : lpNorm (α • f) 1 μ = ‖α‖₊ * lpNorm f 1 μ)

-- Proof sketch: apply the triangle inequality for `MeasureTheory.lpNorm` at exponent `1`,
-- namely `MeasureTheory.lpNorm_add_le`, to the two `ℒ¹` functions `f` and `g`.
/-- Theorem 4.17 (2): On `ℒ¹(μ)`, the `L¹` seminorm is subadditive:
`‖f + g‖₁ ≤ ‖f‖₁ + ‖g‖₁`. -/
theorem l1_seminorm_add_le {f g : Ω → ℝ} (hf : MemLp f 1 μ) (hg : MemLp g 1 μ) :
    lpNorm (f + g) 1 μ ≤ lpNorm f 1 μ + lpNorm g 1 μ := by
  have _ : MemLp (f + g) 1 μ := hf.add hg
  have h1 : (1 : ENNReal) ≤ 1 := by simp
  simpa using (lpNorm_add_le hf h1 : lpNorm (f + g) 1 μ ≤ lpNorm f 1 μ + lpNorm g 1 μ)

-- Proof sketch: nonnegativity is the built-in theorem `MeasureTheory.lpNorm_nonneg`.
/-- Theorem 4.17 (3): The `L¹` seminorm is nonnegative. In particular, this holds on
`ℒ¹(μ)`. -/
theorem l1_seminorm_nonneg {f : Ω → ℝ} : 0 ≤ lpNorm f 1 μ :=
  lpNorm_nonneg

/-- Helper for Theorem 4.17: an `L¹` function has `L¹` seminorm zero exactly when it
vanishes almost everywhere. -/
theorem l1_seminorm_eq_zero_iff_ae_zero {f : Ω → ℝ} (hf : MemLp f 1 μ) :
    lpNorm f 1 μ = 0 ↔ f =ᵐ[μ] 0 := by
  -- The canonical `lpNorm_eq_zero` theorem already gives the exact `L¹` characterization.
  simpa using (lpNorm_eq_zero hf one_ne_zero)

-- Proof sketch: use the characterization `MeasureTheory.lpNorm_eq_zero` at exponent `1`;
-- the almost-everywhere vanishing assumption gives the forward implication required here.
/-- Theorem 4.17 (4): If an `L¹` function vanishes almost everywhere, then its `L¹` seminorm is
zero. -/
theorem l1_seminorm_eq_zero_of_ae_zero {f : Ω → ℝ} (hf : MemLp f 1 μ) (h_zero : f =ᵐ[μ] 0) :
    lpNorm f 1 μ = 0 := by
  -- Apply the zero-characterization specialized to `L¹` and use the a.e.-vanishing hypothesis.
  exact (l1_seminorm_eq_zero_iff_ae_zero hf).2 h_zero
