/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped RealInnerProductSpace Gradient

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Theorem 5.10 is `source-facing`: the textbook states the Euclidean-ball version. The reusable
`bridge/view` underneath it is the intrinsic segment formulation below, where the only geometric
input is that the closed segment from `x` to `y` stays in the `C²` domain. The canonical
second-order data is the bilinear Hessian `bilinearIteratedFDerivTwo`.
-/

-- Proof sketch: compose `f` with the affine line map `t ↦ AffineMap.lineMap x y t` on `[0, 1]`
-- and apply the one-variable Taylor theorem with Lagrange remainder. The first derivative of the
-- pullback at `0` is `⟪∇ f x, y - x⟫`, and the second derivative at an intermediate point is the
-- Hessian quadratic form `bilinearIteratedFDerivTwo ℝ f ξ (y - x) (y - x)`.
omit [CompleteSpace E] in
/-- Helper for Theorem 5.10: restricting a `C²` function to the affine segment from `x` to `y`
keeps it `C²` on `uIcc (0 : ℝ) 1`. -/
lemma segmentPullbackContDiffOn
    {U : Set E} {f : E → ℝ} {x y : E}
    (hf : ContDiffOn ℝ 2 f U) (hsegment : segment ℝ x y ⊆ U) :
    ContDiffOn ℝ 2 (fun t : ℝ ↦ f (AffineMap.lineMap x y t)) (Set.uIcc (0 : ℝ) 1) := by
  -- The line map stays inside the given segment, so the pullback stays in the `C²` domain.
  have hmaps : Set.MapsTo (AffineMap.lineMap x y) (Set.uIcc (0 : ℝ) 1) U := by
    intro t ht
    apply hsegment
    rw [segment_eq_image_lineMap]
    refine ⟨t, ?_, rfl⟩
    simpa [Set.uIcc_of_lt zero_lt_one] using ht
  -- Compose the ambient `C²` function with the affine parametrization of the segment.
  refine hf.comp ?_ hmaps
  simpa [AffineMap.lineMap_apply_module'] using
    (show ContDiffOn ℝ 2 (fun t : ℝ ↦ t • (y - x) + x) (Set.uIcc (0 : ℝ) 1) from by
      fun_prop)

/-- Helper for Theorem 5.10: the first derivative of the segment pullback at `0` is the gradient
pairing `inner ℝ (∇ f x) (y - x)`. -/
lemma segmentPullbackDerivWithinZero
    {U : Set E} {f : E → ℝ} {x y : E}
    (hU_open : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hsegment : segment ℝ x y ⊆ U) :
    derivWithin (fun t : ℝ ↦ f (AffineMap.lineMap x y t)) (Set.uIcc (0 : ℝ) 1) 0 =
      inner ℝ (∇ f x) (y - x) := by
  have hxU : x ∈ U := hsegment (left_mem_segment ℝ x y)
  have hfx : ContDiffAt ℝ 2 f x := hf.contDiffAt (hU_open.mem_nhds hxU)
  have hdiff : DifferentiableAt ℝ f x := hfx.differentiableAt (by norm_num)
  have hu :
      UniqueDiffWithinAt ℝ (Set.uIcc (0 : ℝ) 1) 0 := by
    rw [Set.uIcc_of_lt zero_lt_one]
    exact uniqueDiffOn_Icc_zero_one.uniqueDiffWithinAt (by simp)
  have hderiv :
      HasDerivWithinAt (fun t : ℝ ↦ f (AffineMap.lineMap x y t))
        (fderiv ℝ f x (y - x)) (Set.uIcc (0 : ℝ) 1) 0 := by
    -- Apply the chain rule to the pullback `t ↦ f (lineMap x y t)` at the left endpoint.
    exact (hdiff.hasFDerivAt.comp_hasDerivWithinAt_of_eq (x := 0)
      (AffineMap.hasDerivWithinAt_lineMap
        (a := x) (b := y) (s := Set.uIcc (0 : ℝ) 1) (x := 0))
      (by simp))
  -- Convert the Fréchet derivative into the gradient pairing.
  rw [hderiv.derivWithin hu, ← inner_gradient_left
    (𝕜 := ℝ) (f := f) (x := x) (y := y - x) hdiff]

omit [CompleteSpace E] in
/-- Helper for Theorem 5.10: the affine line map has vanishing second iterated derivative. -/
lemma iteratedDerivTwoLineMap
    {x y : E} (t : ℝ) :
    iteratedDeriv 2 (AffineMap.lineMap x y : ℝ → E) t = 0 := by
  -- The first derivative of the affine line map is constant, so its derivative vanishes.
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hconst : deriv (AffineMap.lineMap x y : ℝ → E) = fun _ : ℝ ↦ y - x := by
    funext s
    exact (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := s)).deriv
  rw [hconst]
  exact (hasDerivAt_const t (c := y - x)).deriv

omit [CompleteSpace E] in
/-- Helper for Theorem 5.10: the second derivative of the segment pullback is the Hessian
quadratic form evaluated on the direction `y - x`. -/
lemma segmentPullbackIteratedDerivTwo
    {U : Set E} {f : E → ℝ} {x y : E}
    (hU_open : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hsegment : segment ℝ x y ⊆ U)
    {t : ℝ} (ht : t ∈ Set.uIoo (0 : ℝ) 1) :
    iteratedDeriv 2 (fun s : ℝ ↦ f (AffineMap.lineMap x y s)) t =
      bilinearIteratedFDerivTwo ℝ f (AffineMap.lineMap x y t) (y - x) (y - x) := by
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [Set.uIoo_of_lt zero_lt_one] using ht
  have hline_mem : AffineMap.lineMap x y t ∈ U := by
    apply hsegment
    rw [segment_eq_image_lineMap]
    refine ⟨t, ⟨le_of_lt ht'.1, le_of_lt ht'.2⟩, rfl⟩
  have hft : ContDiffAt ℝ 2 f (AffineMap.lineMap x y t) := by
    exact hf.contDiffAt (hU_open.mem_nhds hline_mem)
  have hline : ContDiffAt ℝ 2 (AffineMap.lineMap x y : ℝ → E) t := by
    simpa [AffineMap.lineMap_apply_module'] using
      (show ContDiffAt ℝ 2 (fun s : ℝ ↦ s • (y - x) + x) t from by
        fun_prop)
  have hlineDeriv : deriv (AffineMap.lineMap x y : ℝ → E) t = y - x := by
    exact (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := t)).deriv
  have hvec : (fun _ : Fin 2 ↦ deriv (AffineMap.lineMap x y : ℝ → E) t) = ![y - x, y - x] := by
    ext i
    fin_cases i <;> simp [hlineDeriv]
  -- Expand the second derivative of a composition and kill the affine second-derivative term.
  calc
    iteratedDeriv 2 (fun s : ℝ ↦ f (AffineMap.lineMap x y s)) t
        = iteratedFDeriv ℝ 2 f (AffineMap.lineMap x y t)
            (fun _ ↦ deriv (AffineMap.lineMap x y : ℝ → E) t)
          + fderiv ℝ f (AffineMap.lineMap x y t)
              (iteratedDeriv 2 (AffineMap.lineMap x y : ℝ → E) t) := by
            simpa using
              (iteratedDeriv_vcomp_two (𝕜 := ℝ) (g := f)
                (f := (AffineMap.lineMap x y : ℝ → E)) (x := t) hft hline)
    _ = iteratedFDeriv ℝ 2 f (AffineMap.lineMap x y t) ![y - x, y - x]
          + fderiv ℝ f (AffineMap.lineMap x y t)
              (iteratedDeriv 2 (AffineMap.lineMap x y : ℝ → E) t) := by
            rw [hvec]
    _ = iteratedFDeriv ℝ 2 f (AffineMap.lineMap x y t) ![y - x, y - x] := by
            rw [iteratedDerivTwoLineMap]
            simp
    _ = bilinearIteratedFDerivTwo ℝ f (AffineMap.lineMap x y t) (y - x) (y - x) := by
            rw [← bilinearIteratedFDerivTwo_eq_iteratedFDeriv
              (𝕜 := ℝ) (f := f) (e := AffineMap.lineMap x y t)
              (e₁ := y - x) (e₂ := y - x)]

/-- Theorem 5.10: if a real-valued function is `C²` on an open set containing the segment
`segment ℝ x y`, then it admits the second-order Taylor expansion with Lagrange remainder along
that segment. -/
theorem linear_approximation_on_segment_with_lagrange_remainder
    {U : Set E} {f : E → ℝ} {x y : E}
    (hU_open : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hsegment : segment ℝ x y ⊆ U) :
    ∃ ξ ∈ segment ℝ x y,
      f y = f x + inner ℝ (∇ f x) (y - x)
        + (1 / 2 : ℝ) * bilinearIteratedFDerivTwo ℝ f ξ (y - x) (y - x) := by
  let φ : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap x y t)
  have hφ : ContDiffOn ℝ 2 φ (Set.uIcc (0 : ℝ) 1) := by
    -- Restrict `f` to the affine segment so that one-variable Taylor applies on `[0, 1]`.
    simpa [φ] using segmentPullbackContDiffOn (f := f) (x := x) (y := y) hf hsegment
  obtain ⟨θ, hθ, hTaylor⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv
      (f := φ) (x := (1 : ℝ)) (x₀ := (0 : ℝ)) (n := 1) one_ne_zero.symm hφ
  have hθ' : θ ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [Set.uIoo_of_lt zero_lt_one] using hθ
  have hTaylor' :
      φ 1 = φ 0 + derivWithin φ (Set.uIcc (0 : ℝ) 1) 0 + (1 / 2 : ℝ) * iteratedDeriv 2 φ θ := by
    -- Normalize the one-variable Taylor polynomial of order `1` and solve for `φ 1`.
    have hTaylorNorm' :
        φ 1 - (φ 0 + derivWithin φ (Set.uIcc (0 : ℝ) 1) 0) = iteratedDeriv 2 φ θ / 2 := by
      simpa [taylorWithinEval_succ, taylor_within_zero_eval, Set.uIcc_of_lt zero_lt_one] using
        hTaylor
    calc
      φ 1 = φ 0 + derivWithin φ (Set.uIcc (0 : ℝ) 1) 0 + iteratedDeriv 2 φ θ / 2 := by
        linarith [hTaylorNorm']
      _ = φ 0 + derivWithin φ (Set.uIcc (0 : ℝ) 1) 0
            + (1 / 2 : ℝ) * iteratedDeriv 2 φ θ := by
        ring
  let ξ : E := AffineMap.lineMap x y θ
  have hξ_segment : ξ ∈ segment ℝ x y := by
    -- The Lagrange point on `(0, 1)` corresponds to a point on the geometric segment.
    rw [segment_eq_image_lineMap]
    refine ⟨θ, ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩, rfl⟩
  refine ⟨ξ, hξ_segment, ?_⟩
  -- Rewrite the scalar Taylor formula back in terms of `f`, `∇ f`, and the Hessian quadratic form.
  calc
    f y = φ 1 := by
      simp [φ, AffineMap.lineMap_apply_one]
    _ = φ 0 + derivWithin φ (Set.uIcc (0 : ℝ) 1) 0 + (1 / 2 : ℝ) * iteratedDeriv 2 φ θ := hTaylor'
    _ = f x + inner ℝ (∇ f x) (y - x) + (1 / 2 : ℝ) * iteratedDeriv 2 φ θ := by
      rw [segmentPullbackDerivWithinZero (hU_open := hU_open) (hf := hf) (hsegment := hsegment)]
      simp [φ, AffineMap.lineMap_apply_zero]
    _ = f x + inner ℝ (∇ f x) (y - x)
          + (1 / 2 : ℝ)
              * bilinearIteratedFDerivTwo ℝ f
                  (AffineMap.lineMap x y θ) (y - x) (y - x) := by
      rw [segmentPullbackIteratedDerivTwo
        (hU_open := hU_open) (hf := hf) (hsegment := hsegment) (ht := hθ)]
    _ = f x + inner ℝ (∇ f x) (y - x)
          + (1 / 2 : ℝ)
              * bilinearIteratedFDerivTwo ℝ f ξ (y - x) (y - x) := by
      simp [ξ]

end

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- Source-facing corollary for Theorem 5.10: if `f : ℝ^n → ℝ` is twice continuously
differentiable on an open set `U`
containing the ball `Metric.ball x r`, then every `y` in that ball admits a point `ξ` on the
segment from `x` to `y` such that the second-order Taylor expansion of `f` at `x` with Lagrange
remainder holds. The Hessian term is expressed by the canonical bilinear second derivative
`bilinearIteratedFDerivTwo`. -/
theorem linear_approximation_with_lagrange_remainder
    {U : Set E} {f : E → ℝ} {x y : E} {r : ℝ}
    (hU_open : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hball : Metric.ball x r ⊆ U)
    (hy : y ∈ Metric.ball x r) :
    ∃ ξ ∈ segment ℝ x y,
      f y = f x + inner ℝ (∇ f x) (y - x)
        + (1 / 2 : ℝ) * bilinearIteratedFDerivTwo ℝ f ξ (y - x) (y - x) := by
  apply linear_approximation_on_segment_with_lagrange_remainder hU_open hf
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hy)
  exact ((convex_ball x r).segment_subset (Metric.mem_ball_self hr) hy).trans hball

end
