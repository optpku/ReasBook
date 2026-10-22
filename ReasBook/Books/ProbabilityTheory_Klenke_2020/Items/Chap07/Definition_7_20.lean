/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Remark_4_18

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

noncomputable section

/-- The canonical bracket on square-integrable real representatives defines a semi-inner product
space structure on `ℒ²(μ)`, represented by `mem_lp_submodule 2 μ`. -/
instance memLpTwoPreInnerProductSpaceCore :
    PreInnerProductSpace.Core ℝ (mem_lp_submodule 2 μ) where
  inner f g := ∫ x, (f : Ω → ℝ) x * (g : Ω → ℝ) x ∂μ
  conj_inner_symm f g := by
    simp [mul_comm]
  re_inner_nonneg f := by
    refine integral_nonneg fun x ↦ ?_
    simpa [sq] using sq_nonneg ((f : Ω → ℝ) x)
  add_left f g h := by
    simp_rw [Submodule.coe_add, Pi.add_apply, add_mul]
    exact integral_add (f.2.integrable_mul h.2) (g.2.integrable_mul h.2)
  smul_left f g r := by
    simp_rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul r (fun x ↦ (f : Ω → ℝ) x * (g : Ω → ℝ) x)

instance : Inner ℝ (mem_lp_submodule 2 μ) :=
  memLpTwoPreInnerProductSpaceCore.toInner

/-- For square-integrable real representatives, the canonical bracket on `ℒ²(μ)` is the integral
of the pointwise product. -/
theorem inner_memLp_two_eq_integral_mul (f g : mem_lp_submodule 2 μ) :
    inner ℝ f g = ∫ x, (f : Ω → ℝ) x * (g : Ω → ℝ) x ∂μ :=
  rfl

/- Definition 7.20: The canonical inner product on the real Hilbert space `L²(μ)` is the
`MeasureTheory.L2` inner product, whose value is the integral of the pointwise inner product of
representatives. -/
recall L2.inner_def

/-- For square-integrable real representatives, the inner product of their `L²(μ)` classes is the
integral of their pointwise product. -/
theorem inner_toLp_eq_integral_mul {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hx hy
  rw [hx, hy]
  simp [real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]
