/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

-- Proof sketch: combine the convexity inequality along the segment from `x` to `y`, which bounds
-- the right limsup by `f x`, with lower semicontinuity of `f` and the fact that
-- `AffineMap.lineMap x y α → x` as `α ↓ 0` to obtain the matching lower liminf inequality.
/-- Proposition 9.14: if `f` is lower semicontinuous and has convex epigraph, and if `x` and `y`
lie in the effective domain of `f`, then the values of `f` along the segment point
`x_α = (1 - α) • x + α • y = AffineMap.lineMap x y α` converge to `f x` as `α ↓ 0`. -/
theorem tendsto_apply_lineMap_right_zero_of_lowerSemicontinuous_epigraph_convex
    {f : H → Set.Ioi (⊥ : EReal)}
    (hf_lsc : LowerSemicontinuous (fun z : H ↦ (f z : EReal)))
    (hf_conv : Convex ℝ {p : H × ℝ | (f p.1 : EReal) ≤ (p.2 : EReal)})
    {x y : H} (hx : (f x : EReal) < ⊤) (hy : (f y : EReal) < ⊤) :
    Filter.Tendsto (fun α : ℝ ↦ (f (AffineMap.lineMap x y α) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (f x : EReal)) := by
  let u : ℝ → EReal := fun α ↦ (f (AffineMap.lineMap x y α) : EReal)
  let v : ℝ → EReal :=
    fun α ↦ (((1 - α : ℝ) : EReal) * (f x : EReal) + (α : EReal) * (f y : EReal))
  -- Reinterpret the endpoint hypotheses and convexity assumption in the Chapter 8 epigraph API.
  have hx_dom : x ∈ dom (fun z : H ↦ (f z : EReal)) := by
    simpa [dom] using hx
  have hy_dom : y ∈ dom (fun z : H ↦ (f z : EReal)) := by
    simpa [dom] using hy
  have hconv_epi : Convex ℝ (epigraph (fun z : H ↦ (f z : EReal))) := by
    simpa [epigraph] using hf_conv
  have hJ := (convex_epigraph_iff_jensen_on_dom (fun z : H ↦ (f z : EReal))).1 hconv_epi
  -- Lower semicontinuity along the segment gives the textbook `liminf` lower bound.
  have hu_lsc : LowerSemicontinuous u := by
    simpa [u, Function.comp] using hf_lsc.comp (AffineMap.lineMap_continuous (p := x) (q := y))
  have h_liminf : (f x : EReal) ≤ Filter.liminf u (𝓝[>] (0 : ℝ)) := by
    calc
      (f x : EReal) = u 0 := by simp [u]
      _ ≤ Filter.liminf u (𝓝 (0 : ℝ)) := (hu_lsc.lowerSemicontinuousAt 0).le_liminf
      _ ≤ Filter.liminf u (𝓝[>] (0 : ℝ)) :=
        Filter.liminf_le_liminf_of_le (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
  -- Convexity gives an eventual Jensen majorant once the right-neighborhood lies inside `]0,1[`.
  have hα_pos : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), 0 < α := by
    simpa using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
  have hα_lt_one : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), α < 1 := by
    exact nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  have huv : ∀ᶠ α : ℝ in 𝓝[>] (0 : ℝ), u α ≤ v α := by
    filter_upwards [hα_pos, hα_lt_one] with α hα_pos hα_lt_one
    simpa [u, v, AffineMap.lineMap_apply_module, add_comm, mul_comm] using
      hJ hy_dom hx_dom hα_pos hα_lt_one
  -- The affine majorant is finite, so we rewrite it through `toReal` and use ordinary continuity.
  have hx_ne_top : (f x : EReal) ≠ ⊤ := ne_of_lt hx
  have hy_ne_top : (f y : EReal) ≠ ⊤ := ne_of_lt hy
  have hx_ne_bot : (f x : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_ne_bot : (f y : EReal) ≠ ⊥ :=
    ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hv_real : Filter.Tendsto
      (fun α : ℝ ↦ AffineMap.lineMap (f x : EReal).toReal (f y : EReal).toReal α)
      (𝓝[>] (0 : ℝ)) (𝓝 ((f x : EReal).toReal)) := by
    simpa using
      (((AffineMap.lineMap_continuous (p := (f x : EReal).toReal)
          (q := (f y : EReal).toReal)).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds)
  have hv_tendsto_coe : Filter.Tendsto
      (fun α : ℝ ↦ ((AffineMap.lineMap (f x : EReal).toReal (f y : EReal).toReal α : ℝ) : EReal))
      (𝓝[>] (0 : ℝ)) (𝓝 (f x : EReal)) := by
    have hcoe : Filter.Tendsto
        (fun t : ℝ ↦ (t : EReal)) (𝓝 ((f x : EReal).toReal)) (𝓝 (f x : EReal)) := by
      simpa [EReal.coe_toReal hx_ne_top hx_ne_bot] using
        (continuous_coe_real_ereal.tendsto ((f x : EReal).toReal))
    simpa [Function.comp] using hcoe.comp hv_real
  have hv_eq : ∀ α : ℝ,
      v α = ((AffineMap.lineMap (f x : EReal).toReal (f y : EReal).toReal α : ℝ) : EReal) := by
    intro α
    simp [v, AffineMap.lineMap_apply_module, smul_eq_mul, EReal.coe_toReal hx_ne_top hx_ne_bot,
      EReal.coe_toReal hy_ne_top hy_ne_bot, add_comm, mul_comm]
  have hv_tendsto : Filter.Tendsto v (𝓝[>] (0 : ℝ)) (𝓝 (f x : EReal)) := by
    exact Filter.Tendsto.congr (fun α ↦ (hv_eq α).symm) hv_tendsto_coe
  -- Squeezing the `liminf` and `limsup` completes the convergence statement.
  have h_limsup : Filter.limsup u (𝓝[>] (0 : ℝ)) ≤ (f x : EReal) := by
    calc
      Filter.limsup u (𝓝[>] (0 : ℝ)) ≤ Filter.limsup v (𝓝[>] (0 : ℝ)) :=
        Filter.limsup_le_limsup huv
      _ = (f x : EReal) := hv_tendsto.limsup_eq
  exact tendsto_of_le_liminf_of_limsup_le h_liminf h_limsup

end ERealFunction
