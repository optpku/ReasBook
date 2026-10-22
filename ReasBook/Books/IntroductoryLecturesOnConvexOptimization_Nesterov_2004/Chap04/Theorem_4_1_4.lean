/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

universe u

/- Theorem 4.1.4 lies in the star-convex / cubic-regularization rate domain.

Sampled owner declarations:
* mathlib `StarConvex` and `starConvex_iff_segment_subset` for the ambient segment geometry;
* `argmin[Q]` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the project owner
  for feasible minimizers on a comparison set;
* mathlib `Bornology.IsBounded`, `Metric.diam`, and `Metric.dist_le_diam_of_mem` for the
  feasible-set diameter bound owner;
* project `cubicallyRegularizedObjective` in `Definition_4_2_16` for the cubic perturbation owner.

Source/core/bridge triage:
* source-facing: `StarConvexWithRespectToOn f xStar 𝓕`, the textbook function-level
  star-convexity inequality relative to a chosen feasible reference point on a feasible set;
* core/canonical: `argmin[𝓕] f`, `argmin[segment ℝ x0 xStar] ...`, and
  `cubicallyRegularizedObjective`;
* bridge/view: the projection lemma `StarConvexWithRespectToOn.mem`.

Primitive data:
* an objective `f`;
* a feasible set `𝓕` with a distinguished optimizer `xStar ∈ argmin[𝓕] f`;
* a boundedness witness and diameter bound for `𝓕`;
* the fixed-center star-convexity inequality from `xStar` to feasible points.

Derived API:
* feasibility and optimality of `xStar` from `xStar ∈ argmin[𝓕] f`;
* feasibility of the star center from `StarConvexWithRespectToOn.mem`;
* the two rate theorems below, phrased directly over the canonical cubic perturbation owner. -/

section StarConvexOwner

variable {E : Type*} [AddCommMonoid E] [Module ℝ E]

/-- `StarConvexWithRespectToOn f xStar 𝓕` is the textbook star-convexity inequality for `f`
with respect to the reference point `xStar` on the feasible set `𝓕`. -/
def StarConvexWithRespectToOn
    (f : E → ℝ) (xStar : E) (𝓕 : Set E) : Prop :=
  xStar ∈ 𝓕 ∧
    ∀ ⦃x : E⦄, x ∈ 𝓕 → ∀ ⦃α : ℝ⦄, α ∈ Set.Icc (0 : ℝ) 1 →
      f (α • xStar + (1 - α) • x) ≤ (1 - α) * f x + α * f xStar

/-- A star center with respect to `𝓕` is itself feasible. -/
theorem StarConvexWithRespectToOn.mem
    {f : E → ℝ} {xStar : E} {𝓕 : Set E}
    (hstar : StarConvexWithRespectToOn f xStar 𝓕) :
    xStar ∈ 𝓕 :=
  hstar.1

end StarConvexOwner

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

section StarConvexCubicRate

variable {f : E → ℝ} {𝓕 : Set E} {xStar : E} {L D : ℝ}

/-- Helper for Theorem 4.1.4: every feasible point has nonnegative objective gap above the
constrained minimizer `xStar`. -/
lemma objective_gap_nonneg_of_mem_argmin
    {x : E}
    (hxStar : xStar ∈ argmin[𝓕] f)
    (hx : x ∈ 𝓕) :
    0 ≤ f x - f xStar := by
  rcases (mem_constrainedArgmin_iff.mp hxStar) with ⟨_, hxStar_min⟩
  rw [isMinOn_iff] at hxStar_min
  -- Compare the feasible point directly against the constrained minimizer `xStar`.
  have hxStar_le : f xStar ≤ f x := hxStar_min x hx
  linarith

/-- Helper for Theorem 4.1.4: a cubic step along the segment to `xStar` satisfies the textbook
one-step scalar gap recurrence. -/
lemma cubic_segment_one_step_gap_le
    {xk y : E}
    (hF_bounded : Bornology.IsBounded 𝓕)
    (hdiam : Metric.diam 𝓕 ≤ D)
    (hstar : StarConvexWithRespectToOn f xStar 𝓕)
    (hxk : xk ∈ 𝓕)
    (hL : 0 < L)
    (hy :
      y ∈ argmin[segment ℝ xk xStar]
        (cubicallyRegularizedObjective f ((3 / 2 : ℝ) * L) xk))
    {α : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    f y - f xStar ≤
      (1 - α) * (f xk - f xStar) + (L / 2 : ℝ) * α ^ (3 : ℕ) * D ^ (3 : ℕ) := by
  rcases (mem_constrainedArgmin_iff.mp hy) with ⟨_, hy_min⟩
  rw [isMinOn_iff] at hy_min
  let z : E := AffineMap.lineMap xk xStar α
  have hz_mem : z ∈ segment ℝ xk xStar := by
    -- The comparison point is the canonical segment point with parameter `α`.
    rw [segment_eq_image_lineMap]
    exact ⟨α, hα, rfl⟩
  have hy_le :
      cubicallyRegularizedObjective f ((3 / 2 : ℝ) * L) xk y ≤
        cubicallyRegularizedObjective f ((3 / 2 : ℝ) * L) xk z :=
    hy_min z hz_mem
  have hcoeff : (3 / 2 : ℝ) * L / 3 = L / 2 := by
    ring
  have hy_le' :
      f y + (L / 2 : ℝ) * ‖y - xk‖ ^ (3 : ℕ) ≤
        f z + (L / 2 : ℝ) * ‖z - xk‖ ^ (3 : ℕ) := by
    rw [cubicallyRegularizedObjective_apply, cubicallyRegularizedObjective_apply] at hy_le
    simpa [hcoeff] using hy_le
  have hz_obj :
      f z ≤ (1 - α) * f xk + α * f xStar := by
    -- Star-convexity controls the objective value on the comparison segment.
    simpa [z, AffineMap.lineMap_apply_module, add_comm, add_left_comm, add_assoc] using
      hstar.2 hxk hα
  have hD_nonneg : 0 ≤ D := le_trans Metric.diam_nonneg hdiam
  have hbase_norm_le : ‖xStar - xk‖ ≤ D := by
    have hdist_le : dist xStar xk ≤ D :=
      (Metric.dist_le_diam_of_mem hF_bounded hstar.mem hxk).trans hdiam
    simpa [dist_eq_norm] using hdist_le
  have hz_norm_eq : ‖z - xk‖ = α * ‖xStar - xk‖ := by
    -- The comparison point differs from `xk` by the scalar displacement `α • (xStar - xk)`.
    rw [show z = α • (xStar - xk) + xk by
      simpa [z] using (AffineMap.lineMap_apply xk xStar α)]
    simp [norm_smul_of_nonneg, hα.1]
  have hz_norm_le : ‖z - xk‖ ≤ α * D := by
    rw [hz_norm_eq]
    exact mul_le_mul_of_nonneg_left hbase_norm_le hα.1
  have hcube_le :
      (L / 2 : ℝ) * ‖z - xk‖ ^ (3 : ℕ) ≤
        (L / 2 : ℝ) * α ^ (3 : ℕ) * D ^ (3 : ℕ) := by
    -- The cubic penalty is bounded by the feasible-set diameter.
    have hpow :
        ‖z - xk‖ ^ (3 : ℕ) ≤ (α * D) ^ (3 : ℕ) :=
      pow_le_pow_left₀ (norm_nonneg _) hz_norm_le 3
    have hcoef_nonneg : 0 ≤ L / 2 := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hpow hcoef_nonneg
    simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hy_pen_nonneg : 0 ≤ (L / 2 : ℝ) * ‖y - xk‖ ^ (3 : ℕ) := by
    positivity
  -- Drop the nonnegative penalty at `y`, then insert the star-convex and diameter bounds.
  nlinarith [hy_le', hz_obj, hy_pen_nonneg, hcube_le]

/-- Helper for Theorem 4.1.4: if the feasible-set diameter is nonpositive, every feasible point
coincides with the optimizer `xStar`, hence its objective gap vanishes. -/
lemma gap_eq_zero_of_diam_nonpos
    {x : E}
    (hF_bounded : Bornology.IsBounded 𝓕)
    (hdiam_nonpos : Metric.diam 𝓕 ≤ 0)
    (hxStar : xStar ∈ argmin[𝓕] f)
    (hx : x ∈ 𝓕) :
    f x - f xStar = 0 := by
  rcases (mem_constrainedArgmin_iff.mp hxStar) with ⟨hxStar_mem, _⟩
  -- A nonpositive diameter forces every feasible point to lie at zero distance from `xStar`.
  have hdist_le_zero : dist x xStar ≤ 0 :=
    (Metric.dist_le_diam_of_mem hF_bounded hx hxStar_mem).trans hdiam_nonpos
  have hdist_zero : dist x xStar = 0 := le_antisymm hdist_le_zero dist_nonneg
  have hx_eq : x = xStar := dist_eq_zero.mp hdist_zero
  simp [hx_eq]

/-- Helper for Theorem 4.1.4: the normalized square-root parameter of the scalar cubic recurrence
either vanishes or gains at least `1 / 3` in reciprocal value. -/
lemma reciprocal_alpha_growth_of_cubic_step
    {c α Δnext : ℝ}
    (hc : 0 < c)
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hΔnext_nonneg : 0 ≤ Δnext)
    (hstep : Δnext ≤ c * (α ^ (2 : ℕ) - (2 / 3 : ℝ) * α ^ (3 : ℕ))) :
    let αnext := Real.sqrt (Δnext / c)
    αnext ∈ Set.Icc (0 : ℝ) α ∧
      (Δnext = 0 ∨ 1 / αnext ≥ 1 / α + 1 / 3) := by
  dsimp
  have hcontract : Real.sqrt (Δnext / c) ≤ α * (1 - α / 3) := by
    -- Rewrite the cubic recurrence as a contraction for the normalized square-root parameter.
    apply (Real.sqrt_le_iff).2
    constructor
    · nlinarith [hα.1, hα.2]
    · have hquot : Δnext / c ≤ α ^ (2 : ℕ) - (2 / 3 : ℝ) * α ^ (3 : ℕ) := by
        exact (div_le_iff₀ hc).2 (by simpa [mul_comm] using hstep)
      nlinarith [hquot]
  have hαnext_nonneg : 0 ≤ Real.sqrt (Δnext / c) := Real.sqrt_nonneg _
  have hαnext_le_α : Real.sqrt (Δnext / c) ≤ α := by
    nlinarith [hcontract, hα.1, hα.2]
  refine ⟨⟨hαnext_nonneg, hαnext_le_α⟩, ?_⟩
  by_cases hΔnext_zero : Δnext = 0
  · exact Or.inl hΔnext_zero
  · right
    have hΔnext_pos : 0 < Δnext :=
      lt_of_le_of_ne hΔnext_nonneg (Ne.symm hΔnext_zero)
    have hα_pos : 0 < α := by
      by_contra hα_nonpos
      have hα_zero : α = 0 := by
        nlinarith [hα.1]
      rw [hα_zero] at hstep
      have : Δnext ≤ 0 := by
        simpa using hstep
      linarith
    have hsqrt_pos : 0 < Real.sqrt (Δnext / c) := by
      apply Real.sqrt_pos.2
      exact div_pos hΔnext_pos hc
    have hrecip :
        1 / (α * (1 - α / 3)) ≤ 1 / Real.sqrt (Δnext / c) := by
      exact one_div_le_one_div_of_le hsqrt_pos hcontract
    have hexpand : 1 / α + 1 / 3 ≤ 1 / (α * (1 - α / 3)) := by
      have hthree_sub_pos : 0 < 3 - α := by
        nlinarith
      have hα_ne : α ≠ 0 := ne_of_gt hα_pos
      have hthree_sub_ne : 3 - α ≠ 0 := ne_of_gt hthree_sub_pos
      have hsplit :
          1 / (α * (1 - α / 3)) = 1 / α + 1 / (3 - α) := by
        field_simp [hα_ne, hthree_sub_ne]
        ring
      rw [hsplit]
      have hbound : 1 / 3 ≤ 1 / (3 - α) := by
        refine one_div_le_one_div_of_le ?_ ?_
        · positivity
        · nlinarith
      linarith
    linarith

-- Proof sketch: evaluate the one-step segment minimization rule against the competitor `xStar`,
-- use that `xStar` is a feasible optimizer together with star-convexity at `xStar` to control
-- the objective term along the segment from `x0` to `xStar`, and bound the cubic penalty by the
-- feasible-set diameter bound `D`.
/-- Theorem 4.1.4 (1): if the initial objective gap is at least `(3 / 2) L D^3`, then one cubic
segment-minimization step reduces it to at most `(1 / 2) L D^3`. -/
theorem starConvex_cubicSegment_first_gap_le_half_LD_cube
    {x0 x1 : E}
    (hF_bounded : Bornology.IsBounded 𝓕)
    (hdiam : Metric.diam 𝓕 ≤ D)
    (hxStar : xStar ∈ argmin[𝓕] f)
    (hstar : StarConvexWithRespectToOn f xStar 𝓕)
    (hx0 : x0 ∈ 𝓕)
    (hL : 0 < L)
    (hx1 :
      x1 ∈ argmin[segment ℝ x0 xStar]
        (cubicallyRegularizedObjective f ((3 / 2 : ℝ) * L) x0))
    (hgap0 : f x0 - f xStar ≥ (3 / 2 : ℝ) * L * D ^ (3 : ℕ)) :
    f x1 - f xStar ≤ (1 / 2 : ℝ) * L * D ^ (3 : ℕ) := by
  -- Compare the step directly with the endpoint competitor `xStar`, i.e. with `α = 1`.
  have hstep_one :=
    cubic_segment_one_step_gap_le hF_bounded hdiam hstar hx0 hL hx1
      (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
  nlinarith [hstep_one]

-- Proof sketch: derive the one-step recurrence
-- `Δ_{k+1} ≤ min_{α ∈ [0,1]} ((1 - α) Δ_k + (L / 2) α^3 D^3)` from the segment minimization rule,
-- using that `xStar` is the chosen optimizer and star center. Then optimize it at
-- `α_k = sqrt (2 Δ_k / (3 L D^3))`, and telescope the reciprocal estimate
-- `1 / α_{k+1} - 1 / α_k ≥ 1 / 3` to obtain the inverse-square rate.
/-- Theorem 4.1.4 (2): if the initial objective gap is at most `(3 / 2) L D^3`, then every
iterate satisfies the inverse-square decay bound
`f(x_k) - f(xStar) ≤ 3 L D^3 / (2 (1 + k / 3)^2)`. -/
theorem starConvex_cubicSegment_gap_le_inverse_square_rate
    {x : ℕ → E}
    (hF_bounded : Bornology.IsBounded 𝓕)
    (hdiam : Metric.diam 𝓕 ≤ D)
    (hxStar : xStar ∈ argmin[𝓕] f)
    (hstar : StarConvexWithRespectToOn f xStar 𝓕)
    (hiterates : ∀ k : ℕ, x k ∈ 𝓕)
    (hL : 0 < L)
    (hstep :
      ∀ k : ℕ,
        x (k + 1) ∈ argmin[segment ℝ (x k) xStar]
          (cubicallyRegularizedObjective f ((3 / 2 : ℝ) * L) (x k)))
    (hgap0 : f (x 0) - f xStar ≤ (3 / 2 : ℝ) * L * D ^ (3 : ℕ)) :
    ∀ k : ℕ,
      f (x k) - f xStar ≤
        (3 * L * D ^ (3 : ℕ)) / (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ)) := by
  have hD_nonneg : 0 ≤ D := le_trans Metric.diam_nonneg hdiam
  by_cases hD_zero : D = 0
  · intro k
    have hdiam_nonpos : Metric.diam 𝓕 ≤ 0 := by
      simpa [hD_zero] using hdiam
    -- In the zero-diameter branch, every feasible iterate equals the optimizer.
    have hgap_eq :
        f (x k) - f xStar = 0 :=
      gap_eq_zero_of_diam_nonpos hF_bounded hdiam_nonpos hxStar (hiterates k)
    simpa [hD_zero] using hgap_eq.le
  · have hD_pos : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hD_zero)
    set c : ℝ := (3 / 2 : ℝ) * L * D ^ (3 : ℕ) with hcdef
    have hc : 0 < c := by
      rw [hcdef]
      positivity
    let Δ : ℕ → ℝ := fun k ↦ f (x k) - f xStar
    let α : ℕ → ℝ := fun k ↦ Real.sqrt (Δ k / c)
    have hΔ_nonneg : ∀ k : ℕ, 0 ≤ Δ k := by
      intro k
      simpa [Δ] using objective_gap_nonneg_of_mem_argmin hxStar (hiterates k)
    have hΔ_le_c : ∀ k : ℕ, Δ k ≤ c := by
      intro k
      induction k with
      | zero =>
          simpa [Δ, hcdef] using hgap0
      | succ k hk =>
          have hstep_one :
              Δ (k + 1) ≤ (L / 2 : ℝ) * D ^ (3 : ℕ) := by
            simpa [Δ, α] using
              cubic_segment_one_step_gap_le hF_bounded hdiam hstar
                (hiterates k) hL (hstep k)
                (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
          have hhalf_le_c : (L / 2 : ℝ) * D ^ (3 : ℕ) ≤ c := by
            rw [hcdef]
            nlinarith
          exact hstep_one.trans hhalf_le_c
    have hα_mem : ∀ k : ℕ, α k ∈ Set.Icc (0 : ℝ) 1 := by
      intro k
      refine ⟨?_, ?_⟩
      · simpa [α] using Real.sqrt_nonneg (Δ k / c)
      · have hsqrt_le_one : Real.sqrt (Δ k / c) ≤ 1 := by
          apply (Real.sqrt_le_iff).2
          constructor
          · norm_num
          · exact (div_le_iff₀ hc).2 (by simpa [hcdef] using hΔ_le_c k)
        simpa [α] using hsqrt_le_one
    have hΔ_eq : ∀ k : ℕ, Δ k = c * α k ^ (2 : ℕ) := by
      intro k
      have hsq : α k ^ (2 : ℕ) = Δ k / c := by
        simp [α, Real.sq_sqrt, div_nonneg (hΔ_nonneg k) hc.le]
      have hmul := congrArg (fun t : ℝ ↦ c * t) hsq
      field_simp [hc.ne'] at hmul
      nlinarith [hmul]
    have hstep_gap :
        ∀ k : ℕ,
          Δ (k + 1) ≤
            (1 - α k) * Δ k + (L / 2 : ℝ) * α k ^ (3 : ℕ) * D ^ (3 : ℕ) := by
      intro k
      simpa [Δ, α] using
        cubic_segment_one_step_gap_le hF_bounded hdiam hstar
          (hiterates k) hL (hstep k) (hα_mem k)
    have hrecurrence :
        ∀ k : ℕ,
          Δ (k + 1) ≤ c * (α k ^ (2 : ℕ) - (2 / 3 : ℝ) * α k ^ (3 : ℕ)) := by
      intro k
      have hstepk := hstep_gap k
      have hgapk := hΔ_eq k
      have hcubic :
          (L / 2 : ℝ) * α k ^ (3 : ℕ) * D ^ (3 : ℕ) =
            c * ((1 / 3 : ℝ) * α k ^ (3 : ℕ)) := by
        rw [hcdef]
        ring
      rw [hgapk, hcubic] at hstepk
      nlinarith
    have hreciprocal_or_zero :
        ∀ k : ℕ, Δ k = 0 ∨ 1 / α k ≥ 1 + (k : ℝ) / 3 := by
      intro k
      induction k with
      | zero =>
          by_cases hΔ0 : Δ 0 = 0
          · exact Or.inl hΔ0
          · have hα0_nonneg : 0 ≤ α 0 := (hα_mem 0).1
            have hα0_ne : α 0 ≠ 0 := by
              intro hα0_zero
              have : Δ 0 = 0 := by
                rw [hΔ_eq 0, hα0_zero]
                ring
              exact hΔ0 this
            have hα0_pos : 0 < α 0 := lt_of_le_of_ne hα0_nonneg (Ne.symm hα0_ne)
            have hone : 1 ≤ 1 / α 0 := by
              simpa using one_div_le_one_div_of_le hα0_pos (hα_mem 0).2
            exact Or.inr (by nlinarith)
      | succ k hk =>
          rcases hk with hΔk_zero | hk_recip
          · have hαk_zero : α k = 0 := by
              rw [hΔ_eq k] at hΔk_zero
              have hsq_zero : α k ^ (2 : ℕ) = 0 := by
                nlinarith [hΔk_zero, hc]
              nlinarith [sq_nonneg (α k), hsq_zero]
            have hnext_le_zero : Δ (k + 1) ≤ 0 := by
              have hrec := hrecurrence k
              rw [hαk_zero] at hrec
              simpa using hrec
            exact Or.inl (le_antisymm hnext_le_zero (hΔ_nonneg (k + 1)))
          · have hgrowth :
                α (k + 1) ∈ Set.Icc (0 : ℝ) (α k) ∧
                  (Δ (k + 1) = 0 ∨ 1 / α (k + 1) ≥ 1 / α k + 1 / 3) := by
              simpa [α] using
                reciprocal_alpha_growth_of_cubic_step hc (hα_mem k)
                  (hΔ_nonneg (k + 1)) (hrecurrence k)
            rcases hgrowth with ⟨_, hgrowth⟩
            rcases hgrowth with hΔnext_zero | hnext_recip
            · exact Or.inl hΔnext_zero
            · have hsum : 1 / α (k + 1) ≥ 1 + ((k + 1 : ℕ) : ℝ) / 3 := by
                have hsum' : 1 / α (k + 1) ≥ (1 + (k : ℝ) / 3) + 1 / 3 := by
                  nlinarith [hk_recip, hnext_recip]
                have hcast :
                    (1 + (k : ℝ) / 3) + 1 / 3 = 1 + ((k + 1 : ℕ) : ℝ) / 3 := by
                  rw [Nat.cast_add]
                  ring
                rw [← hcast]
                exact hsum'
              exact Or.inr hsum
    intro k
    change Δ k ≤ (3 * L * D ^ (3 : ℕ)) / (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ))
    rcases hreciprocal_or_zero k with hΔk_zero | hk_recip
    · simpa [hΔk_zero] using
        (show
          0 ≤ (3 * L * D ^ (3 : ℕ)) / (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ)) by
          positivity)
    · have hαk_nonneg : 0 ≤ α k := (hα_mem k).1
      have hαk_ne : α k ≠ 0 := by
        intro hαk_zero
        have hkfalse : ¬((0 : ℝ) ≥ 1 + (k : ℝ) / 3) := by
          have : (0 : ℝ) < 1 + (k : ℝ) / 3 := by
            positivity
          linarith
        have : (0 : ℝ) ≥ 1 + (k : ℝ) / 3 := by
          simpa [hαk_zero] using hk_recip
        exact hkfalse this
      have hαk_pos : 0 < α k := lt_of_le_of_ne hαk_nonneg (Ne.symm hαk_ne)
      have hs_pos : 0 < 1 + (k : ℝ) / 3 := by
        positivity
      have hsα : (1 + (k : ℝ) / 3) * α k ≤ 1 := by
        exact (le_div_iff₀ hαk_pos).1 (by simpa using hk_recip)
      have hαk_le : α k ≤ 1 / (1 + (k : ℝ) / 3) := by
        exact (le_div_iff₀ hs_pos).2 (by simpa [mul_comm] using hsα)
      have hsq_le :
          α k ^ (2 : ℕ) ≤ (1 / (1 + (k : ℝ) / 3)) ^ (2 : ℕ) :=
        pow_le_pow_left₀ hαk_nonneg hαk_le 2
      calc
        Δ k = c * α k ^ (2 : ℕ) := hΔ_eq k
        _ ≤ c * (1 / (1 + (k : ℝ) / 3)) ^ (2 : ℕ) := by
          gcongr
        _ = (3 * L * D ^ (3 : ℕ)) / (2 * (1 + (k : ℝ) / 3) ^ (2 : ℕ)) := by
          rw [hcdef]
          have hs_ne : (1 + (k : ℝ) / 3) ≠ 0 := by positivity
          field_simp [hs_ne]

end StarConvexCubicRate
