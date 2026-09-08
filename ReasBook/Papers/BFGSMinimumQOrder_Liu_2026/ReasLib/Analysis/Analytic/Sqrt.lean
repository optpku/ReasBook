module

public import Mathlib.Analysis.Analytic.Binomial
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

open scoped Topology

universe u

namespace AnalyticAt

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The square root of a real-valued function analytic and nonzero at a point is analytic
at that point. -/
theorem sqrt {f : E → ℝ} {x : E} (hf : AnalyticAt ℝ f x) (hfx : f x ≠ 0) :
    AnalyticAt ℝ (fun y ↦ √(f y)) x := by
  -- Split according to the local branch of the real square root at the base value.
  rcases hfx.lt_or_gt with hfx_neg | hfx_pos
  · -- Near a negative base value, the real square root is identically zero.
    have hf_neg : ∀ᶠ y in 𝓝 x, f y < 0 :=
      hf.continuousAt.eventually_mem (Iio_mem_nhds hfx_neg)
    refine (analyticAt_const (𝕜 := ℝ) (v := (0 : ℝ)) (x := x)).congr ?_
    filter_upwards [hf_neg] with y hy
    simp only [Real.sqrt_eq_zero_of_nonpos hy.le]
  · -- Normalize the positive branch to the binomial series centered at `1`.
    have hinner : AnalyticAt ℝ (fun y ↦ f y / f x - 1) x :=
      hf.div_const.sub analyticAt_const
    have hinner_zero : f x / f x - 1 = 0 := by
      rw [div_self hfx, sub_self]
    have hpower :
        AnalyticAt ℝ (fun y ↦ (1 + (f y / f x - 1)) ^ (1 / 2 : ℝ)) x := by
      simpa only [Function.comp_def] using
        Real.one_add_rpow_hasFPowerSeriesAt_zero.analyticAt.comp_of_eq hinner hinner_zero
    -- Multiplication by `√(f x)` transports the normalized series back to `√(f y)`.
    refine ((analyticAt_const (𝕜 := ℝ) (v := √(f x)) (x := x)).mul hpower).congr
      (Filter.Eventually.of_forall ?_)
    intro y
    calc
      √(f x) * (1 + (f y / f x - 1)) ^ (1 / 2 : ℝ) =
          √(f x) * (f y / f x) ^ (1 / 2 : ℝ) := by ring_nf
      _ = √(f x) * √(f y / f x) := by rw [← Real.sqrt_eq_rpow (f y / f x)]
      _ = √(f x * (f y / f x)) := (Real.sqrt_mul hfx_pos.le _).symm
      _ = √(f y) := by rw [mul_div_cancel₀ _ hfx]

end AnalyticAt

namespace Real

/-- If `q` is analytic at `0`, satisfies `q 0 = 1`, and is eventually positive near
`0`, then `ε ↦ ε * √(q ε)` is analytic at `0`. -/
theorem analyticAt_signedSqrtBranch (q : ℝ → ℝ) (hq : AnalyticAt ℝ q 0)
    (hq_zero : q 0 = 1) :
    AnalyticAt ℝ (fun ε ↦ ε * √(q ε)) 0 := by
  -- The value condition makes the square-root composition analytic at the origin.
  have hq_ne : q 0 ≠ 0 := by
    rw [hq_zero]
    exact one_ne_zero
  have hsqrt : AnalyticAt ℝ (fun ε ↦ √(q ε)) 0 := AnalyticAt.sqrt hq hq_ne
  -- Multiplying by the analytic identity function gives the signed branch.
  refine (analyticAt_id.mul hsqrt).congr (Filter.Eventually.of_forall ?_)
  intro ε
  simp only [Pi.mul_apply, id_eq]

/-- On a sufficiently small right neighborhood of `0`, the signed square-root branch
`ε ↦ ε * √(q ε)` agrees with `ε ↦ √(ε ^ 2 * q ε)`. -/
theorem signedSqrtBranch_eventuallyEq_sqrt (q : ℝ → ℝ) :
    (fun ε : ℝ ↦ ε * √(q ε)) =ᶠ[𝓝[>] 0] (fun ε ↦ √(ε ^ 2 * q ε)) := by
  -- Every point of the right neighborhood is positive, so `√(ε²) = ε` there.
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [Real.sqrt_mul (sq_nonneg ε), Real.sqrt_sq hε.le]

/-- If `q` is analytic at `0`, satisfies `q 0 = 1`, and is eventually positive near
`0`, then the derivative at `0` of `ε ↦ ε * √(q ε)` is `1`. -/
theorem hasDerivAt_signedSqrtBranch (q : ℝ → ℝ) (hq : AnalyticAt ℝ q 0)
    (hq_zero : q 0 = 1) :
    HasDerivAt (fun ε : ℝ ↦ ε * √(q ε)) 1 0 := by
  -- Differentiate the square-root factor using its nonzero value at the origin.
  have hq_ne : q 0 ≠ 0 := by
    rw [hq_zero]
    exact one_ne_zero
  have hsqrt := hq.differentiableAt.hasDerivAt.sqrt hq_ne
  -- In the product rule, the unknown derivative of the square-root factor is killed by `ε = 0`.
  have hproduct : HasDerivAt (id * fun ε ↦ √(q ε)) 1 0 := by
    simpa only [id_eq, hq_zero, Real.sqrt_one, one_mul, zero_mul, add_zero] using
      (hasDerivAt_id 0).mul hsqrt
  refine hproduct.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro ε
  simp only [Pi.mul_apply, id_eq]

end Real
