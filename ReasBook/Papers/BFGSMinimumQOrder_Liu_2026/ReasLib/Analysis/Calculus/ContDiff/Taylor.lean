module

public import Mathlib.Analysis.Calculus.Taylor

public section

open Filter
open scoped BigOperators Topology

universe u

namespace ContDiffAt

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A `C^m` function whose derivatives below `q` vanish has a Taylor expansion
from degree `q` through degree `m`, with remainder `o(h ^ m)` at `0`. -/
theorem taylor_isLittleO_of_iteratedDeriv_eq_zero {f : ℝ → F} {x : ℝ} {q m : ℕ}
    (hf : ContDiffAt ℝ m f x) (hqm : q ≤ m)
    (hzero : ∀ n < q, iteratedDeriv n f x = 0) :
    (fun h : ℝ ↦ f (x + h) -
      ∑ n ∈ Finset.Icc q m,
        ((n.factorial : ℝ)⁻¹ * h ^ n) • iteratedDeriv n f x) =o[𝓝 0]
      fun h : ℝ ↦ h ^ m := by
  -- Shrink the local regularity neighborhood to a nondegenerate closed interval around `x`.
  rcases hf.contDiffOn le_rfl (by simp) with ⟨u, hu, hfu⟩
  rcases exists_Icc_mem_subset_of_mem_nhds hu with ⟨a, b, hxI, hI, hIu⟩
  have haxb : a < x ∧ x < b := Icc_mem_nhds_iff.mp hI
  have hab : a < b := haxb.1.trans haxb.2
  have hfI : ContDiffOn ℝ m f (Set.Icc a b) := hfu.mono hIu
  have hTaylor :
      (fun y ↦ f y - taylorWithinEval f m (Set.Icc a b) x y) =o[𝓝 x]
        fun y ↦ (y - x) ^ m := by
    -- Since the interval is a neighborhood, the within-filter Taylor theorem is an ambient one.
    rw [← nhdsWithin_eq_nhds.mpr hI]
    exact _root_.taylor_isLittleO (convex_Icc a b) hxI hfI
  have hderiv (n : ℕ) (hn : n ≤ m) :
      iteratedDerivWithin n f (Set.Icc a b) x = iteratedDeriv n f x := by
    -- On this nondegenerate interval, within derivatives agree with ordinary derivatives.
    refine iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hab) ?_ hxI
    exact hf.of_le (by exact_mod_cast hn)
  have hpoly (y : ℝ) :
      taylorWithinEval f m (Set.Icc a b) x y =
        ∑ n ∈ Finset.Icc q m,
          ((n.factorial : ℝ)⁻¹ * (y - x) ^ n) • iteratedDeriv n f x := by
    -- First replace all within derivatives in the full Taylor polynomial.
    rw [taylor_within_apply, Nat.range_succ_eq_Icc_zero]
    calc
      ∑ n ∈ Finset.Icc 0 m,
          ((n.factorial : ℝ)⁻¹ * (y - x) ^ n) •
            iteratedDerivWithin n f (Set.Icc a b) x =
          ∑ n ∈ Finset.Icc 0 m,
            ((n.factorial : ℝ)⁻¹ * (y - x) ^ n) • iteratedDeriv n f x := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [hderiv n (Finset.mem_Icc.mp hn).2]
      _ = ∑ n ∈ Finset.Icc q m,
          ((n.factorial : ℝ)⁻¹ * (y - x) ^ n) • iteratedDeriv n f x := by
        -- The terms removed from `Icc 0 m` have degree below `q`, hence vanish.
        symm
        apply Finset.sum_subset
        · intro n hn
          simp only [Finset.mem_Icc] at hn ⊢
          omega
        · intro n hn hnq
          simp only [Finset.mem_Icc] at hn hnq
          rw [hzero n (by omega)]
          exact smul_zero _
  -- Normalize the Taylor polynomial once, then translate the expansion from `x` to `0`.
  simp only [hpoly] at hTaylor
  have htranslate : Filter.Tendsto (fun h : ℝ ↦ x + h) (𝓝 0) (𝓝 x) := by
    simpa only [id_eq, add_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ ↦ x) (𝓝 0) (𝓝 x)).add tendsto_id
  simpa only [Function.comp_def, add_sub_cancel_left] using
    hTaylor.comp_tendsto htranslate

end ContDiffAt
