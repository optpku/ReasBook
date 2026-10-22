/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Extrema
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_3_1

noncomputable section

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "DualSpace" => StrongDual ℝ E

open scoped Subgradient

-- Domain sampling:
-- * source-facing layer: the geometric-rate theorem for Algorithm 14.3.1 under the angle
--   condition from Theorem 14.3.5;
-- * core/canonical owners in this chapter: `SubgradientMethod`, `S⋆[f]`, and the dual
--   subgradient surface `∂ f(x)`;
-- * primitive data already live in `SubgradientMethod`;
-- * derived API refined here: the geometric-stepsize surface
--   `method.HasGeometricStepSize α0 q`.

namespace SubgradientMethod

/-- `method.HasGeometricStepSize α0 q` means that the Algorithm 14.3.1 execution `method` uses
the source geometric stepsizes `α_(k + 1) = α0 * q ^ k` for all `k`. -/
def HasGeometricStepSize (method : SubgradientMethod E) (α0 q : ℝ) : Prop :=
  ∀ k : ℕ, method.stepSize (k + 1) = α0 * q ^ k

/-- Unfolding `method.HasGeometricStepSize α0 q` gives the source geometric-stepsize law. -/
theorem hasGeometricStepSize_iff
    (method : SubgradientMethod E) (α0 q : ℝ) :
    method.HasGeometricStepSize α0 q ↔
      ∀ k : ℕ, method.stepSize (k + 1) = α0 * q ^ k :=
  Iff.rfl

end SubgradientMethod

/-- Helper for Chapter14 Theorem 14.3.5: the normalized negative subgradient direction has unit
norm whenever the chosen dual subgradient is nonzero. -/
lemma normalizedSubgradientDirection_norm_of_norm_pos
    (g : DualSpace) (hg : 0 < ‖g‖) :
    ‖normalizedSubgradientDirection g‖ = 1 := by
  -- Expand the direction into the Riesz representative scaled by `-‖g‖⁻¹`.
  rw [normalizedSubgradientDirection_eq, norm_smul]
  simp only [Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg g)), norm_neg,
    LinearIsometryEquiv.norm_map]
  have hg' : ‖g‖ ≠ 0 := ne_of_gt hg
  field_simp [hg']

/-- Helper for Chapter14 Theorem 14.3.5: pairing the displacement `x - xStar` with the normalized
negative subgradient direction converts the Hilbert inner product into the expected dual
evaluation divided by `‖g‖`. -/
lemma inner_displacement_normalizedSubgradientDirection_eq_neg_div
    (x xStar : E) (g : DualSpace) (hg : 0 < ‖g‖) :
    inner ℝ (x - xStar) (normalizedSubgradientDirection g) =
      -(g (x - xStar)) / ‖g‖ := by
  -- Rewrite the direction through the Riesz map and then use symmetry of the real inner product.
  rw [normalizedSubgradientDirection_eq, inner_smul_right, real_inner_comm,
    InnerProductSpace.toDual_symm_apply]
  field_simp [ne_of_gt hg]

/-- Helper for Chapter14 Theorem 14.3.5: one normalized subgradient step satisfies the source
squared-distance estimate once the angle condition is inserted. -/
lemma sq_dist_after_normalizedSubgradientStep_le
    (x xStar : E) (g : DualSpace) (α δ₁ : ℝ)
    (hg : 0 < ‖g‖)
    (hα : 0 ≤ α)
    (hangle : δ₁ * ‖g‖ * ‖x - xStar‖ ≤ g (x - xStar)) :
    ‖x + α • normalizedSubgradientDirection g - xStar‖ ^ 2 ≤
      ‖x - xStar‖ ^ 2 - 2 * δ₁ * α * ‖x - xStar‖ + α ^ 2 := by
  have hdiv : δ₁ * ‖x - xStar‖ ≤ (g (x - xStar)) / ‖g‖ := by
    -- Divide the angle inequality by the positive norm `‖g‖`.
    exact (le_div_iff₀ hg).2
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hangle)
  have hscaled : 2 * α * (δ₁ * ‖x - xStar‖) ≤
      2 * α * ((g (x - xStar)) / ‖g‖) := by
    -- The coefficient `2 * α` is nonnegative because Algorithm 14.3.1 uses positive stepsizes.
    gcongr
  have hneg : -(2 * α * ((g (x - xStar)) / ‖g‖)) ≤
      -(2 * α * (δ₁ * ‖x - xStar‖)) := by
    exact neg_le_neg hscaled
  have hmain : -2 * α * (g (x - xStar)) / ‖g‖ ≤
      -2 * δ₁ * α * ‖x - xStar‖ := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hneg
  calc
    ‖x + α • normalizedSubgradientDirection g - xStar‖ ^ 2
        = ‖(x - xStar) + α • normalizedSubgradientDirection g‖ ^ 2 := by
          congr 1
          abel_nf
    _ = ‖x - xStar‖ ^ 2
          + 2 * inner ℝ (x - xStar) (α • normalizedSubgradientDirection g)
          + ‖α • normalizedSubgradientDirection g‖ ^ 2 := by
          rw [norm_add_sq_real]
    _ = ‖x - xStar‖ ^ 2
          + 2 * α * inner ℝ (x - xStar) (normalizedSubgradientDirection g)
          + ‖α • normalizedSubgradientDirection g‖ ^ 2 := by
          -- Pull the scalar `α` out of the right inner-product slot.
          rw [inner_smul_right]
          ring
    _ = ‖x - xStar‖ ^ 2
          - 2 * α * (g (x - xStar)) / ‖g‖
          + ‖α • normalizedSubgradientDirection g‖ ^ 2 := by
          rw [inner_displacement_normalizedSubgradientDirection_eq_neg_div x xStar g hg]
          ring
    _ ≤ ‖x - xStar‖ ^ 2
          - 2 * δ₁ * α * ‖x - xStar‖
          + ‖α • normalizedSubgradientDirection g‖ ^ 2 := by
          have hstep :
              -2 * α * (g (x - xStar)) / ‖g‖ + ‖α • normalizedSubgradientDirection g‖ ^ 2 ≤
                -2 * δ₁ * α * ‖x - xStar‖ + ‖α • normalizedSubgradientDirection g‖ ^ 2 :=
            by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right hmain (‖α • normalizedSubgradientDirection g‖ ^ 2)
          have hstep' := add_le_add_left hstep (‖x - xStar‖ ^ 2)
          convert hstep' using 1 <;> ring
    _ = ‖x - xStar‖ ^ 2 - 2 * δ₁ * α * ‖x - xStar‖ + α ^ 2 := by
          -- The normalized direction has unit norm, so the squared step term is exactly `α ^ 2`.
          rw [norm_smul, normalizedSubgradientDirection_norm_of_norm_pos g hg]
          simp [pow_two, Real.norm_of_nonneg hα]

/-- Helper for Chapter14 Theorem 14.3.5: if a quadratic majorant is controlled at the two
endpoints of the interval `0 ≤ d ≤ t`, then the convex quadratic is controlled throughout the
interval. This is the scalar envelope step needed for the geometric induction. -/
lemma quadratic_interval_bound
    (d t β q δ : ℝ)
    (hd_nonneg : 0 ≤ d)
    (hdt : d ≤ t)
    (hβsq : β ^ 2 ≤ q ^ 2)
    (hqeq : q ^ 2 = 1 - 2 * δ * β + β ^ 2) :
    d ^ 2 - 2 * δ * (β * t) * d + (β * t) ^ 2 ≤ (q * t) ^ 2 := by
  -- Rewrite the quadratic against the endpoint values at `d = 0` and `d = t`.
  have ht_nonneg : 0 ≤ t := le_trans hd_nonneg hdt
  have htd_nonneg : 0 ≤ t - d := sub_nonneg.mpr hdt
  have hdecomp :
      d ^ 2 - 2 * δ * (β * t) * d + (β * t) ^ 2 =
        d * (q ^ 2 * t) + (t - d) * (β ^ 2 * t) - d * (t - d) := by
    rw [hqeq]
    ring
  have hβterm : (t - d) * (β ^ 2 * t) ≤ (t - d) * (q ^ 2 * t) := by
    have hprod_nonneg : 0 ≤ (t - d) * t := by
      nlinarith
    nlinarith [hβsq, hprod_nonneg]
  calc
    d ^ 2 - 2 * δ * (β * t) * d + (β * t) ^ 2
        = d * (q ^ 2 * t) + (t - d) * (β ^ 2 * t) - d * (t - d) := hdecomp
    _ ≤ d * (q ^ 2 * t) + (t - d) * (q ^ 2 * t) := by
      nlinarith [hβterm, hd_nonneg, htd_nonneg]
    _ = (q * t) ^ 2 := by
      ring

/-- Helper for Chapter14 Theorem 14.3.5: along a geometric-stepsize execution of
Algorithm 14.3.1, the angle condition yields the source one-step squared-distance recurrence. -/
lemma geometric_sq_distance_recurrence
    (f : E → ℝ)
    (xStar : E)
    (δ₁ α0 q : ℝ)
    (method : SubgradientMethod E)
    (h_objective : method.objective = f)
    (h_step : method.HasGeometricStepSize α0 q)
    (h_angle :
      ∀ x (g : DualSpace),
        g ∈ ∂ f(x) →
          δ₁ * ‖g‖ * ‖x - xStar‖ ≤ g (x - xStar)) :
    ∀ k : ℕ,
      ‖method (k + 2) - xStar‖ ^ 2 ≤
        ‖method (k + 1) - xStar‖ ^ 2
          - 2 * δ₁ * (α0 * q ^ k) * ‖method (k + 1) - xStar‖
          + (α0 * q ^ k) ^ 2 := by
  intro k
  have hk : 1 ≤ k + 1 := Nat.succ_le_succ (Nat.zero_le k)
  have hnorm_pos : 0 < ‖method.subgradient (k + 1)‖ :=
    method.subgradient_norm_pos (k + 1) hk
  have hstep_nonneg : 0 ≤ α0 * q ^ k := le_of_lt (by
    simpa [h_step k] using method.stepSize_pos (k + 1) hk)
  have hmem : method.subgradient (k + 1) ∈ ∂ f(method (k + 1)) := by
    simpa [h_objective] using method.subgradient_mem_at hk
  have hangle :
      δ₁ * ‖method.subgradient (k + 1)‖ * ‖method (k + 1) - xStar‖ ≤
        method.subgradient (k + 1) (method (k + 1) - xStar) :=
    h_angle (method (k + 1)) (method.subgradient (k + 1)) hmem
  -- Rewrite the algorithm update into the explicit Step-3 normalized direction formula.
  have hiterate :
      method (k + 2) =
        method (k + 1) +
          (α0 * q ^ k) • normalizedSubgradientDirection (method.subgradient (k + 1)) := by
    simpa [SubgradientMethod.directionAt_eq, h_step k] using
      method.iterate_succ_eq_add_direction hk
  rw [hiterate]
  exact sq_dist_after_normalizedSubgradientStep_le
    (method (k + 1)) xStar (method.subgradient (k + 1)) (α0 * q ^ k) δ₁
    hnorm_pos hstep_nonneg hangle

/-- Helper for Chapter14 Theorem 14.3.5: every `q` above the source threshold admits an exact
quadratic-envelope parameter `β` satisfying the algebraic identity required by the geometric
induction. -/
lemma geometric_envelope_parameter_exists
    (δ₁ q : ℝ)
    (hδ₁ : 0 < δ₁)
    (hq : q ∈ Set.Ioo (max (1 / 2 : ℝ) (max (1 - δ₁ ^ 2 / 2) (1 - δ₁ / 3))) 1) :
    ∃ β : ℝ, 0 < β ∧ β ≤ q ∧ β ≤ δ₁ ∧ q ^ 2 = 1 - 2 * δ₁ * β + β ^ 2 := by
  obtain ⟨hq_lower, hq_lt_one⟩ := hq
  have hq_gt_half : (1 / 2 : ℝ) < q := by
    -- The outer maximum packages the lower bound `q > 1 / 2`.
    have hhalf_le :
        (1 / 2 : ℝ) ≤ max (1 / 2 : ℝ) (max (1 - δ₁ ^ 2 / 2) (1 - δ₁ / 3)) :=
      le_max_left _ _
    exact lt_of_le_of_lt hhalf_le hq_lower
  have hq_gt_sq_threshold : 1 - δ₁ ^ 2 / 2 < q := by
    -- The same threshold also stores the quadratic lower bound `q > 1 - δ₁^2 / 2`.
    have hsq_le :
        1 - δ₁ ^ 2 / 2 ≤ max (1 / 2 : ℝ) (max (1 - δ₁ ^ 2 / 2) (1 - δ₁ / 3)) := by
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    exact lt_of_le_of_lt hsq_le hq_lower
  have hq_gt_linear_threshold : 1 - δ₁ / 3 < q := by
    -- The third branch is reserved for the estimate proving `β ≤ q`.
    have hlinear_le :
        1 - δ₁ / 3 ≤ max (1 / 2 : ℝ) (max (1 - δ₁ ^ 2 / 2) (1 - δ₁ / 3)) := by
      exact le_trans (le_max_right _ _) (le_max_right _ _)
    exact lt_of_le_of_lt hlinear_le hq_lower
  have hq_pos : 0 < q := by
    have hhalf_pos : (0 : ℝ) < 1 / 2 := by norm_num
    exact lt_trans hhalf_pos hq_gt_half
  have hinside_pos : 0 < q ^ 2 + δ₁ ^ 2 - 1 := by
    -- Squaring the lower threshold produces a positive radicand for the exact root witness.
    by_cases hδ_big : 2 ≤ δ₁ ^ 2
    · nlinarith [sq_nonneg q, hδ_big]
    · have hδ_small : δ₁ ^ 2 < 2 := by
        linarith
      have hthreshold_pos : 0 < 1 - δ₁ ^ 2 / 2 := by
        nlinarith
      have hsquare_lower : (1 - δ₁ ^ 2 / 2) ^ 2 < q ^ 2 := by
        nlinarith [hq_gt_sq_threshold, hthreshold_pos]
      nlinarith
  have hinside_nonneg : 0 ≤ q ^ 2 + δ₁ ^ 2 - 1 := le_of_lt hinside_pos
  let s : ℝ := Real.sqrt (q ^ 2 + δ₁ ^ 2 - 1)
  let β : ℝ := δ₁ - s
  have hs_nonneg : 0 ≤ s := by
    -- The square root of the radicand is nonnegative by construction.
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hs_sq : s ^ 2 = q ^ 2 + δ₁ ^ 2 - 1 := by
    -- The radicand was proved nonnegative, so `sqrt` squares back exactly.
    dsimp [s]
    rw [Real.sq_sqrt hinside_nonneg]
  have hs_lt_delta : s < δ₁ := by
    -- Since `q < 1`, the chosen square root lies strictly below `δ₁`.
    nlinarith [hs_sq, hq_lt_one, hq_pos, hδ₁]
  have hβ_pos : 0 < β := by
    -- The envelope parameter is the positive gap `δ₁ - s`.
    dsimp [β]
    nlinarith [hs_lt_delta]
  have hβ_le_delta : β ≤ δ₁ := by
    -- Subtracting a nonnegative square root can only decrease `δ₁`.
    dsimp [β]
    nlinarith [hs_nonneg]
  have hβ_le_q : β ≤ q := by
    -- Either `δ₁ ≤ q`, in which case `β ≤ δ₁ ≤ q`, or `q < δ₁` and the exact root estimate
    -- gives the stronger bound `β < q`.
    by_cases hδ₁_le_q : δ₁ ≤ q
    · dsimp [β]
      nlinarith [hδ₁_le_q, hs_nonneg]
    · have hq_lt_delta : q < δ₁ := lt_of_not_ge hδ₁_le_q
      have htwo_delta_q : 1 < 2 * δ₁ * q := by
        by_cases hq_le_three_quarters : q ≤ 3 / 4
        · -- On the lower branch, the threshold `q > 1 - δ₁ / 3` forces `δ₁` to be large.
          nlinarith [hq_gt_half, hq_gt_linear_threshold, hq_le_three_quarters]
        · -- On the upper branch, `q > 3 / 4` and `δ₁ > q` already give the product bound.
          have hthree_quarters_lt : 3 / 4 < q := lt_of_not_ge hq_le_three_quarters
          nlinarith [hthree_quarters_lt, hq_lt_delta]
      have hsquare_gap : (δ₁ - q) ^ 2 < s ^ 2 := by
        -- The product estimate is exactly the gap between the two squared sides.
        nlinarith [hs_sq, htwo_delta_q]
      have hdelta_gap_nonneg : 0 ≤ δ₁ - q := sub_nonneg.mpr (le_of_lt hq_lt_delta)
      have hdelta_gap_lt : δ₁ - q < s := by
        -- Nonnegativity lets us pass from the strict square inequality to the linear one.
        nlinarith [hsquare_gap, hdelta_gap_nonneg, hs_nonneg]
      dsimp [β]
      nlinarith [hdelta_gap_lt]
  refine ⟨β, hβ_pos, hβ_le_q, hβ_le_delta, ?_⟩
  -- Expanding the explicit witness reduces the target identity to the squared-root equation.
  dsimp [β]
  nlinarith [hs_sq]

/-- Helper for Chapter14 Theorem 14.3.5: the initial distance is controlled by the scaled
envelope constant `α0 / β` once `β` is bounded by `δ₁` and `α0` exceeds the source threshold. -/
lemma initial_distance_le_alpha0_div_beta
    (x1 xStar : E)
    (β δ₁ α0 : ℝ)
    (hβ_pos : 0 < β)
    (hβ_le_delta : β ≤ δ₁)
    (hα0 : δ₁ * ‖x1 - xStar‖ + 1 < α0) :
    ‖x1 - xStar‖ ≤ α0 / β := by
  have hnorm_nonneg : 0 ≤ ‖x1 - xStar‖ := norm_nonneg (x1 - xStar)
  have hβ_mul_le : β * ‖x1 - xStar‖ ≤ δ₁ * ‖x1 - xStar‖ := by
    -- Bounding `β` by `δ₁` transfers directly to the scaled initial distance.
    gcongr
  have hdelta_mul_lt : δ₁ * ‖x1 - xStar‖ < α0 := by
    -- The source threshold is strictly stronger than the plain product bound.
    nlinarith
  have hβ_mul_lt : β * ‖x1 - xStar‖ < α0 := by
    -- Chaining the previous two scalar bounds gives the exact numerator estimate.
    exact lt_of_le_of_lt hβ_mul_le hdelta_mul_lt
  -- Divide by the positive envelope parameter `β`.
  exact (le_div_iff₀ hβ_pos).2 (by simpa [mul_comm] using le_of_lt hβ_mul_lt)

/-- Helper for Chapter14 Theorem 14.3.5: the scalar quadratic envelope turns the squared-distance
recurrence into the next geometric-distance bound. -/
lemma next_distance_le_of_quadratic_envelope
    (d e t β q δ : ℝ)
    (hd_nonneg : 0 ≤ d)
    (he_nonneg : 0 ≤ e)
    (ht_nonneg : 0 ≤ t)
    (hβ_nonneg : 0 ≤ β)
    (hβ_le_q : β ≤ q)
    (hq_nonneg : 0 ≤ q)
    (hqeq : q ^ 2 = 1 - 2 * δ * β + β ^ 2)
    (he_sq :
      e ^ 2 ≤ d ^ 2 - 2 * δ * (β * t) * d + (β * t) ^ 2)
    (hdt : d ≤ t) :
    e ≤ q * t := by
  have hβsq : β ^ 2 ≤ q ^ 2 := by
    -- The interval bound only needs the monotonicity of squaring on `0 ≤ β ≤ q`.
    nlinarith [hβ_nonneg, hq_nonneg, hβ_le_q]
  have he_sq_le : e ^ 2 ≤ (q * t) ^ 2 := by
    -- Feed the recurrence into the endpoint-controlled quadratic majorant.
    exact le_trans he_sq (quadratic_interval_bound d t β q δ hd_nonneg hdt hβsq hqeq)
  have hqt_nonneg : 0 ≤ q * t := by
    -- Both `q` and `t` are nonnegative in the induction.
    nlinarith
  -- Compare nonnegative quantities through their squares.
  nlinarith

/-- Chapter14 Theorem 14.3.5: let `f : E → ℝ` be convex on a real Hilbert space, let `xStar` be
a global minimizer of `f`, and assume the source angle condition, written intrinsically on the
dual subgradient `g ∈ ∂ f(x)` as `δ₁ * ‖g‖ * ‖x - xStar‖ ≤ g (x - xStar)`. Then for each initial
iterate `x1` there exist thresholds `qBar ∈ (0, 1)` and
`αBar > 0`, depending on `δ₁` and the source quantity `‖x1 - xStar‖`, such that for every
`q ∈ (qBar, 1)`, every `α0 > αBar`, and every Algorithm 14.3.1 run with `x₁ = x1` and
geometric stepsizes `α_(k + 1) = α0 * q ^ k`, there exists a constant `M > 0` such that the
generated sequence satisfies the geometric bound
`‖x (k + 1) - xStar‖ ≤ M * q ^ k` for all `k`; here `M` is independent of `k` and is related to
`δ₁` and `α0` as in the source statement. -/
theorem subgradientMethod_geometric_rate_of_angle_condition
    (f : E → ℝ)
    (xStar : E)
    (h_convex : ConvexOn ℝ Set.univ f)
    (hxStar : xStar ∈ S⋆[f])
    (δ₁ : ℝ)
    (hδ₁ : 0 < δ₁)
    (h_angle :
      ∀ x (g : DualSpace),
        g ∈ ∂ f(x) →
          δ₁ * ‖g‖ * ‖x - xStar‖ ≤ g (x - xStar))
    (x1 : E) :
    ∃ qBar : Set.Ioo (0 : ℝ) 1,
      ∃ αBar : Set.Ioi (0 : ℝ),
        ∀ (q α0 : ℝ)
          (hq : q ∈ Set.Ioo qBar.1 1)
          (hα0 : α0 ∈ Set.Ioi αBar.1)
          (method : SubgradientMethod E)
          (h_objective : method.objective = f)
          (h_initial : method.initialPoint = x1)
          (h_step : method.HasGeometricStepSize α0 q),
          ∃ M : Set.Ioi (0 : ℝ),
            ∀ k : ℕ, ‖method (k + 1) - xStar‖ ≤ M.1 * q ^ k := by
  let qBarVal : ℝ := max (1 / 2 : ℝ) (max (1 - δ₁ ^ 2 / 2) (1 - δ₁ / 3))
  let αBarVal : ℝ := δ₁ * ‖x1 - xStar‖ + 1
  have hqBar_pos : 0 < qBarVal := by
    -- The rate threshold stays positive because it is bounded below by `1 / 2`.
    dsimp [qBarVal]
    have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
    exact lt_of_lt_of_le hhalf (le_max_left _ _)
  have hqBar_lt : qBarVal < 1 := by
    -- Each candidate branch is strictly below `1`.
    dsimp [qBarVal]
    refine max_lt_iff.mpr ?_
    constructor
    · norm_num
    · refine max_lt_iff.mpr ?_
      constructor
      · nlinarith [sq_pos_of_pos hδ₁]
      · nlinarith
  have hαBar_pos : 0 < αBarVal := by
    -- The stepsize threshold is positive because `δ₁ > 0` and `1` is added.
    dsimp [αBarVal]
    nlinarith [hδ₁, norm_nonneg (x1 - xStar)]
  let qBar : Set.Ioo (0 : ℝ) 1 := ⟨qBarVal, hqBar_pos, hqBar_lt⟩
  let αBar : Set.Ioi (0 : ℝ) := ⟨αBarVal, hαBar_pos⟩
  refine ⟨qBar, αBar, ?_⟩
  intro q α0 hq hα0 method h_objective h_initial h_step
  have hq_pos : 0 < q := lt_trans qBar.2.1 hq.1
  have hq_lt_one : q < 1 := hq.2
  have hα0_pos : 0 < α0 := lt_trans αBar.2 hα0
  have hrec :
      ∀ k : ℕ,
        ‖method (k + 2) - xStar‖ ^ 2 ≤
          ‖method (k + 1) - xStar‖ ^ 2
            - 2 * δ₁ * (α0 * q ^ k) * ‖method (k + 1) - xStar‖
            + (α0 * q ^ k) ^ 2 :=
    geometric_sq_distance_recurrence f xStar δ₁ α0 q method h_objective h_step h_angle
  -- Route correction: the proof is now reduced to a scalar envelope induction. The remaining
  -- step is to choose `β(q, δ₁)`, set `M = α0 / β`, verify
  -- `β ^ 2 ≤ q ^ 2` and `q ^ 2 = 1 - 2 * δ₁ * β + β ^ 2`, and then feed `hrec` into
  -- `quadratic_interval_bound`.
  have hβ_exists :
      ∃ β : ℝ, 0 < β ∧ β ≤ q ∧ β ≤ δ₁ ∧ q ^ 2 = 1 - 2 * δ₁ * β + β ^ 2 := by
    -- The rate threshold was chosen precisely so that the exact quadratic witness exists.
    simpa [qBar, qBarVal] using geometric_envelope_parameter_exists δ₁ q hδ₁ hq
  obtain ⟨β, hβ_pos, hβ_le_q, hβ_le_delta, hqeq⟩ := hβ_exists
  have hβ_nonneg : 0 ≤ β := le_of_lt hβ_pos
  have hα0_gt_bar : αBarVal < α0 := by
    simpa [αBar, αBarVal] using hα0
  let Mval : ℝ := α0 / β
  have hMpos : 0 < Mval := by
    -- The geometric-envelope constant is positive because both numerator and denominator are.
    dsimp [Mval]
    exact div_pos hα0_pos hβ_pos
  let M : Set.Ioi (0 : ℝ) := ⟨Mval, hMpos⟩
  have hmethod_one : method 1 = x1 := by
    -- The method starts from the prescribed initial iterate `x1`.
    simpa [SubgradientMethod.coe_apply, h_initial] using method.iterate_one
  have hbase : ‖method 1 - xStar‖ ≤ Mval := by
    -- The initial iterate is controlled by the same envelope constant `M = α0 / β`.
    have hinit :
        ‖x1 - xStar‖ ≤ α0 / β :=
      initial_distance_le_alpha0_div_beta x1 xStar β δ₁ α0 hβ_pos hβ_le_delta
        (by simpa [αBarVal] using hα0_gt_bar)
    simpa [Mval, hmethod_one] using hinit
  refine ⟨M, ?_⟩
  intro k
  induction k with
  | zero =>
      -- The base case is exactly the initial-distance estimate.
      simpa [M, Mval]
        using hbase
  | succ k hk =>
      let d : ℝ := ‖method (k + 1) - xStar‖
      let e : ℝ := ‖method (k + 2) - xStar‖
      let t : ℝ := Mval * q ^ k
      have hd_nonneg : 0 ≤ d := by
        -- Distances are nonnegative.
        dsimp [d]
        exact norm_nonneg _
      have he_nonneg : 0 ≤ e := by
        -- The next distance is also nonnegative.
        dsimp [e]
        exact norm_nonneg _
      have ht_nonneg : 0 ≤ t := by
        -- The geometric envelope `M q^k` stays nonnegative.
        dsimp [t]
        positivity
      have hstep_eq : α0 * q ^ k = β * t := by
        -- This is the scalar identity `α0 = β * M` with `M = α0 / β`.
        dsimp [t, Mval]
        field_simp [ne_of_gt hβ_pos]
      have hrec_step :
          e ^ 2 ≤ d ^ 2 - 2 * δ₁ * (β * t) * d + (β * t) ^ 2 := by
        -- Rewrite the recurrence in the envelope variable `t = M q^k`.
        simpa [d, e, t, hstep_eq] using hrec k
      have hnext : e ≤ q * t := by
        -- The scalar quadratic envelope turns the squared recurrence into the next distance
        -- bound.
        exact next_distance_le_of_quadratic_envelope d e t β q δ₁
          hd_nonneg he_nonneg ht_nonneg hβ_nonneg hβ_le_q hq_pos.le hqeq hrec_step hk
      have hstep_bound : ‖method (k + 2) - xStar‖ ≤ Mval * q ^ (k + 1) := by
        -- Rewrite `q * (M q^k)` as `M q^(k+1)` to match the claimed geometric rate.
        calc
          ‖method (k + 2) - xStar‖ = e := by
            rfl
          _ ≤ q * t := hnext
          _ = Mval * q ^ (k + 1) := by
            dsimp [t]
            rw [pow_succ]
            ring
      simpa [M, Mval] using hstep_bound

end
