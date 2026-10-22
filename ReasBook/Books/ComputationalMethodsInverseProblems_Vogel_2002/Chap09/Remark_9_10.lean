/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Exercise_2_21
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Prop_2_34
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_30
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_9.CriticalPoint
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Geometry.Manifold.Instances.Real

public section

noncomputable section

namespace NonnegativeOrthant

open scoped Topology

variable {n : ℕ}
variable {J : EuclideanSpace ℝ (Fin n) → ℝ}
variable {fStar f₁ f₂ : EuclideanSpace ℝ (Fin n)}

/-- Helper for Remark 9.10: a critical point on the nonnegative orthant has
nonnegative inner product with every feasible displacement. -/
private theorem inner_gradient_sub_nonneg_of_isCriticalPoint
    (hcrit : IsCriticalPoint J fStar)
    {f : EuclideanSpace ℝ (Fin n)}
    (hf : f ∈ feasibleSet n) :
    0 ≤ inner ℝ (gradient J fStar) (f - fStar) := by
  have hsum_nonneg :
      0 ≤ ∑ i : Fin n, f i * gradient J fStar i := by
    -- Each coordinate contributes a product of two nonnegative terms.
    refine Finset.sum_nonneg fun i _ ↦ ?_
    exact mul_nonneg ((mem_feasibleSet.mp hf) i) (hcrit.gradientNonneg i)
  have hsum_complementarity :
      ∑ i : Fin n, fStar i * gradient J fStar i = 0 := by
    -- Complementarity kills the `fStar`-part of the inner product.
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    exact hcrit.complementarity i
  have hinner :
      inner ℝ (gradient J fStar) (f - fStar) =
        ∑ i : Fin n, f i * gradient J fStar i -
          ∑ i : Fin n, fStar i * gradient J fStar i := by
    -- Expand the Euclidean inner product into a coordinate sum.
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct, Pi.star_apply, RCLike.star_def, sub_eq_add_neg]
    calc
      ∑ x, (f x + -fStar x) * (gradient J fStar) x
          = ∑ x, (f x * (gradient J fStar) x + -(fStar x * (gradient J fStar) x)) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              ring
      _ = ∑ x, f x * (gradient J fStar) x - ∑ x, fStar x * (gradient J fStar) x := by
            rw [Finset.sum_add_distrib]
            simp [sub_eq_add_neg]
  rw [hinner, hsum_complementarity, sub_zero]
  exact hsum_nonneg

/-- Helper for Remark 9.10: on a convex scalar slice, the derivative at the
left endpoint is bounded above by the endpoint secant slope. -/
private theorem derivAtZero_le_sub_of_convexOn_Icc
    {g : ℝ → ℝ}
    {m : ℝ}
    (hg_convex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) g)
    (hg_deriv : HasDerivAt g m 0) :
    m ≤ g 1 - g 0 := by
  have hlimit :
      Filter.Tendsto (fun z : ℝ ↦ z⁻¹ * (g (0 + z) - g 0)) (𝓝[>] (0 : ℝ)) (𝓝 m) := by
    simpa [smul_eq_mul, zero_add] using hg_deriv.tendsto_slope_zero_right
  have hslope_le :
      ∀ᶠ z in 𝓝[>] (0 : ℝ), z⁻¹ * (g (0 + z) - g 0) ≤ g 1 - g 0 := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with z hz
    have hsecant :=
      hg_convex.secant_mono
        (a := (0 : ℝ))
        (by simp)
        (Set.mem_Icc.mpr ⟨hz.1.le, hz.2.le⟩)
        (by simp)
        hz.1.ne'
        one_ne_zero
        hz.2.le
    simpa [div_eq_inv_mul, zero_add, hz.1.ne'] using hsecant
  exact isClosed_Iic.mem_of_tendsto hlimit hslope_le

/-- Helper for Remark 9.10: on a convex set, nonnegative directional
derivatives from `x` toward every feasible point force `x` to be a minimizer. -/
private theorem isMinOn_of_inner_gradient_sub_nonneg_of_convexOn
    {x : EuclideanSpace ℝ (Fin n)}
    {C : Set (EuclideanSpace ℝ (Fin n))}
    (hJ_diff :
      ∀ z ∈ C,
        DifferentiableAt ℝ J z)
    (hJ_convex :
      ConvexOn ℝ C J)
    (hx : x ∈ C)
    (hfirst :
      ∀ z ∈ C,
        0 ≤ inner ℝ (gradient J x) (z - x)) :
    IsMinOn J C x := by
  intro y hy
  let g : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := AffineMap.lineMap x y
  have hmaps : Set.MapsTo g (Set.Icc (0 : ℝ) 1) C := by
    -- The entire segment from `x` to `y` stays inside the convex feasible set.
    intro t ht
    exact hJ_convex.1.lineMap_mem hx hy ht
  have hslice_convex :
      ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (J ∘ g) := by
    -- Restrict `J` to the affine line through `x` and `y`.
    exact (hJ_convex.comp_affineMap g).subset hmaps (convex_Icc (0 : ℝ) 1)
  have hslice_deriv :
      HasDerivAt (J ∘ g) (inner ℝ (gradient J x) (y - x)) 0 := by
    -- The derivative of the slice at `0` is the directional derivative at `x`.
    simpa [g, Function.comp_def, AffineMap.lineMap_apply_module', add_comm] using
      hasDerivAt_line_inner_gradient J x (y - x) (hJ_diff x hx)
  have hsecant :
      inner ℝ (gradient J x) (y - x) ≤ J y - J x := by
    -- Convexity bounds the initial derivative by the endpoint secant slope.
    simpa [g, Function.comp_def, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      derivAtZero_le_sub_of_convexOn_Icc hslice_convex hslice_deriv
  have hdir : 0 ≤ inner ℝ (gradient J x) (y - x) := hfirst y hy
  exact sub_nonneg.mp (le_trans hdir hsecant)

/-- Counterexample clause `(1)` of Remark 9.10. A critical point for problem `(9.16)` need not be a
minimizer in general: for `J x = (x 0 - 1)^3` on the nonnegative orthant in
`EuclideanSpace ℝ (Fin 1)`, the feasible point `!₂[(1 : ℝ)]` is critical but not
the global minimizer. -/
theorem criticalPointNeedNotBeMinimizer :
    IsCriticalPoint
        (fun x : EuclideanSpace ℝ (Fin 1) ↦ (x 0 - 1) ^ 3)
        !₂[(1 : ℝ)] ∧
      ¬ IsMinOn
        (fun x : EuclideanSpace ℝ (Fin 1) ↦ (x 0 - 1) ^ 3)
        (feasibleSet 1)
        !₂[(1 : ℝ)] := by
  let J : EuclideanSpace ℝ (Fin 1) → ℝ := fun x ↦ (x 0 - 1) ^ 3
  let fStar : EuclideanSpace ℝ (Fin 1) := !₂[(1 : ℝ)]
  have hgrad_zero : gradient J fStar 0 = 0 := by
    have hJ_diff : DifferentiableAt ℝ J fStar := by
      -- The one-dimensional cubic objective is differentiable at the test point.
      unfold J fStar
      fun_prop
    have hline :
        HasDerivAt
          (fun τ : ℝ ↦ J (fStar + τ • EuclideanSpace.single 0 (1 : ℝ)))
          (gradient J fStar 0)
          0 := by
      -- Identify the directional derivative with the unique gradient coordinate.
      simpa [J, fStar, gradient_apply_eq_fderiv_single] using
        hasDerivAt_line_inner_gradient J fStar (EuclideanSpace.single 0 (1 : ℝ)) hJ_diff
    have hpow :
        HasDerivAt (fun τ : ℝ ↦ τ ^ 3) 0 0 := by
      simpa using hasDerivAt_pow 3 (0 : ℝ)
    have hline_eq :
        (fun τ : ℝ ↦ J (fStar + τ • EuclideanSpace.single 0 (1 : ℝ))) =
          fun τ : ℝ ↦ τ ^ 3 := by
      -- Along the unique coordinate direction through `fStar`, the slice is exactly `τ ↦ τ^3`.
      funext τ
      simp [J, fStar, EuclideanSpace.single]
    rw [hline_eq] at hline
    exact hline.unique hpow
  constructor
  · -- Verify the three coordinatewise critical-point conditions at `fStar`.
    refine ofConditions ?_ ?_ ?_
    · intro i
      fin_cases i
      simp
    · intro i
      fin_cases i
      simpa [J] using (show 0 ≤ (gradient J fStar) 0 by
        simp [hgrad_zero])
    · intro i
      fin_cases i
      simpa [J, fStar] using (show fStar 0 * gradient J fStar 0 = 0 by
        simp [fStar, hgrad_zero])
  · intro hmin
    have hzero_mem : (0 : EuclideanSpace ℝ (Fin 1)) ∈ feasibleSet 1 := by
      -- The origin is feasible and gives a strictly smaller objective value.
      simp
    have hvalue := hmin hzero_mem
    norm_num [J, fStar] at hvalue

/-- Remark 9.10. On the nonnegative orthant, a critical point of a
differentiable convex functional is a global minimizer. This convex core yields
the strict-convex uniqueness and minimizer consequences recorded in clauses
`(2)` and `(3)`. -/
theorem isMinOn_of_isCriticalPoint_of_convexOn
    (hJ_diff :
      ∀ x ∈ feasibleSet n,
        DifferentiableAt ℝ J x)
    (hJ_convex :
      ConvexOn ℝ (feasibleSet n) J)
    (hcrit : IsCriticalPoint J fStar) :
    IsMinOn J (feasibleSet n) fStar := by
  -- Reduce the minimizer claim to the generic convex first-order criterion.
  refine isMinOn_of_inner_gradient_sub_nonneg_of_convexOn
    hJ_diff hJ_convex hcrit.mem_feasibleSet ?_
  intro f hf
  exact inner_gradient_sub_nonneg_of_isCriticalPoint hcrit hf

/-- Strict-convex minimizer clause `(3)` of Remark 9.10. If `J` is strictly
convex on the nonnegative orthant and Fréchet differentiable at every feasible
point, then any critical point for
problem `(9.16)` is the global minimizer on the nonnegative orthant. -/
theorem isMinOn_of_isCriticalPoint_of_strictConvexOn
    (hJ_diff :
      ∀ x ∈ feasibleSet n,
        DifferentiableAt ℝ J x)
    (hJ_strict :
      StrictConvexOn ℝ (feasibleSet n) J)
    (hcrit : IsCriticalPoint J fStar) :
    IsMinOn J (feasibleSet n) fStar :=
  isMinOn_of_isCriticalPoint_of_convexOn hJ_diff hJ_strict.convexOn hcrit

/-- Uniqueness clause `(2)` of Remark 9.10. If `J` is strictly convex on the nonnegative orthant and
Fréchet differentiable at every feasible point, then problem `(9.16)` has at
most one critical point. -/
theorem eq_of_isCriticalPoint_of_strictConvexOn
    (hJ_diff :
      ∀ x ∈ feasibleSet n,
        DifferentiableAt ℝ J x)
    (hJ_strict :
      StrictConvexOn ℝ (feasibleSet n) J)
    (hcrit₁ : IsCriticalPoint J f₁)
    (hcrit₂ : IsCriticalPoint J f₂) :
    f₁ = f₂ := by
  refine hJ_strict.eq_of_isMinOn ?_ ?_ hcrit₁.mem_feasibleSet hcrit₂.mem_feasibleSet
  · exact isMinOn_of_isCriticalPoint_of_convexOn hJ_diff hJ_strict.convexOn hcrit₁
  · exact isMinOn_of_isCriticalPoint_of_convexOn hJ_diff hJ_strict.convexOn hcrit₂

end NonnegativeOrthant
