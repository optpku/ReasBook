/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {C : Set E} {ω : E → EReal} {σ : ℝ}

/- Lemma 9.4 is `source-facing`: it records the lower quadratic bound, nonnegativity, and
definiteness properties of the Chapter 9 Bregman distance on `C × (C ∩ dom(∂ ω))`. Its owner
abstractions are already upstream: `B[ω]` / `bregmanDistance`, `IsBregmanPotentialOn`,
`subdifferential_domain`, and the strong-convexity support inequality behind clause (1). The
source item is therefore kept as three atomic Bregman lemmas rather than a new wrapper package. -/

-- Proof sketch: apply Theorem 5.24(ii) to the strongly convex real-valued restriction of
-- `ω + extendedIndicator C` given by `hω.strongConvexOn_add_indicator`. For `x ∈ C` and
-- `y ∈ C ∩ dom(∂ ω)`, the indicator terms vanish, and the additional ambient differentiability
-- hypothesis at `y` identifies the supporting subgradient there with the ambient gradient used in
-- `B[ω]`. The resulting quadratic lower-support inequality is exactly the displayed Bregman lower
-- bound.
/-- Lemma 9.4 (1): if `ω` is a Bregman potential on `C`, then for every `x ∈ C` and every
`y ∈ C ∩ dom(∂ ω)` where `x ↦ (ω x).toReal` is ambiently differentiable at `y`, the associated
Bregman distance dominates the quadratic term
`(σ / 2) ‖x - y‖²`. -/
theorem bregmanDistance_lower_quadratic_bound
    (hω : IsBregmanPotentialOn ω C σ) (x y : E)
    (hx : x ∈ C) (hyC : y ∈ C) (hy_subgrad : y ∈ subdifferential_domain ω)
    (hy_diff : DifferentiableAt ℝ (fun z ↦ (ω z).toReal) y) :
    B[ω] x y ≥ (σ / 2) * ‖x - y‖ ^ (2 : ℕ) := by
  have _ : y ∈ effective_domain ω :=
    subdifferential_domain_subset_effective_domain hy_subgrad
  let ψ : E → ℝ := fun z ↦ (ω z).toReal - (σ / 2) * ‖z‖ ^ (2 : ℕ)
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap y x
  let φ : ℝ → ℝ := fun s ↦ ψ (line s)
  have hψ_convex : ConvexOn ℝ C ψ := by
    -- Shift the strong-convexity owner by the quadratic term to recover an ordinary convex
    -- function on `C`.
    simpa [ψ] using (strongConvexOn_iff_convex.mp hω.strongConvexOn)
  have hφ_convex : ConvexOn ℝ (line ⁻¹' C) φ := by
    -- Restrict the shifted convex function to the segment joining `y` and `x`.
    simpa [φ, line] using hψ_convex.comp_affineMap line
  have hφ_zero : (0 : ℝ) ∈ line ⁻¹' C := by
    simpa [line] using hyC
  have hφ_one : (1 : ℝ) ∈ line ⁻¹' C := by
    simpa [line] using hx
  have hline : HasDerivAt line (x - y) 0 := by
    -- The derivative of the affine segment is the displacement vector `x - y`.
    simpa [line] using
      (show HasDerivAt (AffineMap.lineMap y x) (x - y) (0 : ℝ) from
        AffineMap.hasDerivAt_lineMap)
  have hφω_deriv :
      HasDerivAt
        (fun s ↦ (ω (line s)).toReal)
        (inner ℝ (∇ (fun z ↦ (ω z).toReal) y) (x - y))
        0 := by
    -- Differentiate the real-valued view of `ω` along the segment at its left endpoint.
    simpa [line] using
      lineMapDerivAtZero_eq_innerGradient
        (ω := fun z ↦ (ω z).toReal) (x := x) (y := y) hy_diff
  have hφq_deriv :
      HasDerivAt
        (fun s ↦ (σ / 2) * ‖line s‖ ^ (2 : ℕ))
        (σ * inner ℝ y (x - y))
        0 := by
    -- Differentiate the quadratic correction along the same segment.
    have hnorm_sq : HasDerivAt (fun s ↦ ‖line s‖ ^ (2 : ℕ)) (2 * inner ℝ y (x - y)) 0 := by
      simpa [line] using hline.norm_sq
    have hscaled := hnorm_sq.const_mul (σ / 2 : ℝ)
    convert hscaled using 1
    ring
  have hφ_deriv :
      HasDerivAt
        φ
        (inner ℝ (∇ (fun z ↦ (ω z).toReal) y) (x - y) - σ * inner ℝ y (x - y))
        0 := by
    -- The shifted potential has derivative equal to the original derivative minus the quadratic
    -- correction.
    simpa [φ, ψ] using hφω_deriv.sub hφq_deriv
  have hsecant :
      inner ℝ (∇ (fun z ↦ (ω z).toReal) y) (x - y) - σ * inner ℝ y (x - y) ≤
        slope φ 0 1 := by
    -- Convexity controls the left derivative by the secant slope on `[0, 1]`.
    exact hφ_convex.le_slope_of_hasDerivAt hφ_zero hφ_one zero_lt_one hφ_deriv
  have hsecant' :
      inner ℝ (∇ (fun z ↦ (ω z).toReal) y) (x - y) - σ * inner ℝ y (x - y) ≤
        ψ x - ψ y := by
    -- Evaluate the secant slope at the endpoints of the chosen segment.
    simpa [φ, line, slope] using hsecant
  have hsecant'' :
      inner ℝ (∇ (fun z ↦ (ω z).toReal) y) (x - y) - σ * inner ℝ y (x - y) ≤
        (ω x).toReal - (σ / 2) * ‖x‖ ^ (2 : ℕ) -
          ((ω y).toReal - (σ / 2) * ‖y‖ ^ (2 : ℕ)) := by
    -- Expand the shifted potential `ψ` back into the original and quadratic parts.
    simpa [ψ] using hsecant'
  have hsecant_expanded :
      inner ℝ x (∇ (fun z ↦ (ω z).toReal) y) -
          inner ℝ (∇ (fun z ↦ (ω z).toReal) y) y -
          σ * (inner ℝ y x - ‖y‖ ^ (2 : ℕ)) ≤
        (ω x).toReal - (σ / 2) * ‖x‖ ^ (2 : ℕ) -
          ((ω y).toReal - (σ / 2) * ‖y‖ ^ (2 : ℕ)) := by
    -- Normalize the inner-product terms so the final algebra matches the Bregman formula.
    simpa [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm] using hsecant''
  have hinner :
      inner ℝ (∇ (fun z ↦ (ω z).toReal) y) (x - y) =
        inner ℝ x (∇ (fun z ↦ (ω z).toReal) y) -
          inner ℝ (∇ (fun z ↦ (ω z).toReal) y) y := by
    -- Expand the gradient pairing against `x - y`.
    rw [inner_sub_right, real_inner_comm]
  have hnorm :
      ‖x - y‖ ^ (2 : ℕ) =
        ‖x‖ ^ (2 : ℕ) - 2 * inner ℝ y x + ‖y‖ ^ (2 : ℕ) := by
    -- Rewrite the squared displacement with the standard norm polarization identity.
    simpa [real_inner_comm] using (norm_sub_sq_real x y)
  -- Rearranging the convex secant estimate gives the claimed quadratic lower bound for
  -- the Bregman distance.
  rw [bregmanDistance_def, hinner, hnorm]
  linarith

-- Proof sketch: combine `bregmanDistance_lower_quadratic_bound` with `hω.sigma_pos`, which gives
-- `(σ / 2) * ‖x - y‖² ≥ 0`, and conclude that the Bregman distance is nonnegative.
/-- Lemma 9.4 (2): if `x ∈ C` and `y ∈ C ∩ dom(∂ ω)`, then the Bregman distance
`B_ω(x, y)` is nonnegative whenever `x ↦ (ω x).toReal` is ambiently differentiable at `y`. -/
theorem bregmanDistance_nonneg_of_mem_subdifferential_domain
    (hω : IsBregmanPotentialOn ω C σ) (x y : E)
    (hx : x ∈ C) (hyC : y ∈ C) (hy_subgrad : y ∈ subdifferential_domain ω)
    (hy_diff : DifferentiableAt ℝ (fun z ↦ (ω z).toReal) y) :
    0 ≤ B[ω] x y := by
  have hlower :=
    bregmanDistance_lower_quadratic_bound hω x y hx hyC hy_subgrad hy_diff
  have hnorm_sq_nonneg : 0 ≤ ‖x - y‖ ^ (2 : ℕ) := by
    positivity
  -- The quadratic lower bound is nonnegative because the modulus `σ` is positive.
  nlinarith [hω.sigma_pos, hlower, hnorm_sq_nonneg]

-- Proof sketch: if `x = y`, then `bregmanDistance_eq_zero_of_eq` gives the reverse implication.
-- Conversely, `bregmanDistance_nonneg_of_mem_subdifferential_domain` and
-- `bregmanDistance_lower_quadratic_bound` force `‖x - y‖² = 0` when the Bregman distance
-- vanishes, hence `x = y`.
/-- Lemma 9.4 (3): for `x ∈ C` and `y ∈ C ∩ dom(∂ ω)`, the Bregman distance vanishes exactly on
the diagonal, provided `x ↦ (ω x).toReal` is ambiently differentiable at `y`. -/
theorem bregmanDistance_eq_zero_iff_eq_of_mem_subdifferential_domain
    (hω : IsBregmanPotentialOn ω C σ) (x y : E)
    (hx : x ∈ C) (hyC : y ∈ C) (hy_subgrad : y ∈ subdifferential_domain ω)
    (hy_diff : DifferentiableAt ℝ (fun z ↦ (ω z).toReal) y) :
    B[ω] x y = 0 ↔ x = y := by
  constructor
  · intro hB
    have hlower :=
      bregmanDistance_lower_quadratic_bound hω x y hx hyC hy_subgrad hy_diff
    have hnorm_sq_nonneg : 0 ≤ ‖x - y‖ ^ (2 : ℕ) := by
      positivity
    have hnorm_sq_zero : ‖x - y‖ ^ (2 : ℕ) = 0 := by
      -- Vanishing Bregman distance forces the quadratic lower bound to vanish.
      nlinarith [hω.sigma_pos, hlower, hB, hnorm_sq_nonneg]
    have hnorm_zero : ‖x - y‖ = 0 := by
      -- A norm with zero square must itself be zero.
      nlinarith [hnorm_sq_zero]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
  · intro hxy
    -- The diagonal case is the canonical vanishing identity from Definition 9.2.
    simpa using bregmanDistance_eq_zero_of_eq (ω := ω) hxy

end
