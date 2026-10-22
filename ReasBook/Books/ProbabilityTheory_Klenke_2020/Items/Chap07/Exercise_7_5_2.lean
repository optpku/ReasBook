/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Exercise 7.5.2 (1): for finite measures, the chain rule for Radon--Nikodym derivatives is the
canonical theorem `Measure.rnDeriv_mul_rnDeriv`; the textbook assumption `μ ≪ ξ` is redundant for
the statement itself. -/
recall MeasureTheory.Measure.rnDeriv_mul_rnDeriv

private theorem rnDeriv_add_compl (μ ν : Measure Ω) [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv (μ + ν) =ᵐ[μ] fun x ↦ 1 - ν.rnDeriv (μ + ν) x := by
  have h_add : (μ + ν).rnDeriv (μ + ν) =ᵐ[μ] μ.rnDeriv (μ + ν) + ν.rnDeriv (μ + ν) :=
    (ae_add_measure_iff.mp (rnDeriv_add' μ ν (μ + ν))).1
  have h_one : (μ + ν).rnDeriv (μ + ν) =ᵐ[μ] 1 :=
    (ae_add_measure_iff.mp (μ + ν).rnDeriv_self).1
  have h_le : ν ≤ μ + ν := by
    intro s
    rw [Measure.add_apply]
    exact le_add_of_nonneg_left (zero_le (μ s))
  have hμ_add : μ ≪ μ + ν := rfl.absolutelyContinuous.add_right _
  have h_rn_le : ν.rnDeriv (μ + ν) ≤ᵐ[μ] 1 :=
    hμ_add <| rnDeriv_le_one_of_le h_le
  filter_upwards [h_add, h_one, h_rn_le] with x hx_add hx_one hx_le
  rw [hx_one, Pi.add_apply] at hx_add
  exact ENNReal.eq_sub_of_add_eq' (by simp) hx_add.symm

-- Proof sketch: start from `Measure.rnDeriv_eq_div_rnDeriv_add` for the pair `(ν, μ)`, then
-- rewrite the denominator `μ.rnDeriv (μ + ν)` as `1 - ν.rnDeriv (μ + ν)` using the identities
-- relating the Radon--Nikodym derivatives of `μ` and `ν` with respect to `μ + ν`.
/-- Exercise 7.5.2 (2): For σ-finite measures and the canonical density `f = dν/d(μ + ν)`, one has
`dν/dμ = f / (1 - f)` `μ`-almost everywhere. -/
theorem rnDeriv_eq_div_one_sub_rnDeriv_add {μ ν : Measure Ω} [SigmaFinite μ] [SigmaFinite ν] :
    ν.rnDeriv μ =ᵐ[μ] fun ω ↦ ν.rnDeriv (μ + ν) ω / (1 - ν.rnDeriv (μ + ν) ω) := by
  have h_ratio : ν.rnDeriv μ =ᵐ[μ] fun x ↦ ν.rnDeriv (μ + ν) x / μ.rnDeriv (μ + ν) x := by
    simpa [add_comm] using ν.rnDeriv_eq_div_rnDeriv_add μ
  refine h_ratio.trans ?_
  filter_upwards [rnDeriv_add_compl μ ν] with x hx
  rw [hx]
