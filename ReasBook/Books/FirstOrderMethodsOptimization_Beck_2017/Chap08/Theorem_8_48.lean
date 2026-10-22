/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_47
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped BigOperators

section

variable {E : Type u}
variable {m : ℕ} [NeZero m]
variable {f : E → ℝ} {g : Fin m → E → ℝ} {fOpt qOpt L : ℝ}

/-- The explicit numerator constant from Theorem 8.48, namely
`2 * L * ((M + 2 * α)^2 + log 3)` with
`M = dual_projected_subgradient_multiplier_norm_bound f fOpt qOpt g xBar L 1 lam0` and
`α = (f xBar - fOpt) / strict_feasibility_margin g xBar`. -/
def dual_projected_subgradient_partial_average_rate_constant
    (f : E → ℝ) (fOpt qOpt : ℝ) (g : Fin m → E → ℝ) (xBar : E)
    (L : ℝ) (lam0 : Fin m → NNReal) : ℝ :=
  let α := (f xBar - fOpt) / strict_feasibility_margin g xBar
  let M := dual_projected_subgradient_multiplier_norm_bound f fOpt qOpt g xBar L 1 lam0
  2 * L * ((M + 2 * α) ^ (2 : ℕ) + Real.log 3)

@[simp] theorem dual_projected_subgradient_partial_average_rate_constant_def
    (f : E → ℝ) (fOpt qOpt : ℝ) (g : Fin m → E → ℝ) (xBar : E)
    (L : ℝ) (lam0 : Fin m → NNReal) :
    dual_projected_subgradient_partial_average_rate_constant f fOpt qOpt g xBar L lam0 =
      let α := (f xBar - fOpt) / strict_feasibility_margin g xBar
      let M := dual_projected_subgradient_multiplier_norm_bound f fOpt qOpt g xBar L 1 lam0
      2 * L * ((M + 2 * α) ^ (2 : ℕ) + Real.log 3) := rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m : ℕ} [NeZero m]
variable {X XStar : Set E} {f : E → ℝ} {g : Fin m → E → ℝ}
variable {fOpt qOpt L : ℝ}
variable (xSel : (Fin m → NNReal) → {x // x ∈ X}) (lam0 : Fin m → NNReal)
variable {xBar : E}

local notation "Λ" => EuclideanSpace ℝ (Fin m)
local notation "γ" => fun n : ℕ ↦ 1 / Real.sqrt ((n : ℝ) + 1)
local notation "q" => lagrangian_dual_objective X f (dual_constraint_vector g)
local notation "α" => (f xBar - fOpt) / strict_feasibility_margin g xBar
local notation "M" =>
  dual_projected_subgradient_multiplier_norm_bound f fOpt qOpt g xBar L 1 lam0
local notation "C" =>
  dual_projected_subgradient_partial_average_rate_constant f fOpt qOpt g xBar L lam0
local notation "lamSeq" => dual_projected_subgradient_method X g xSel γ lam0
local notation "xSeq" => dual_projected_subgradient_primal_iterate X g xSel γ lam0
local notation "constraintSeq" =>
  fun n ↦ dual_projected_subgradient_constraint_vector g (xSeq n : E)
local notation "partialAvg" =>
  dual_projected_subgradient_partial_average_iterate (X := X) (g := g) xSel γ lam0
local notation "gVec" => fun y i ↦ g i y

/-- Helper for Theorem 8.48: the squared suffix-window stepsizes are exactly the half-tail
harmonic sum from Lemma 8.27. -/
lemma partialGammaSqSum_eq_harmonicHalfTailSum (k : ℕ) :
    Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ)) = harmonicHalfTailSum k := by
  rw [harmonicHalfTailSum_eq_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  have hsqrt_ne : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by
    positivity
  rw [show γ n = (1 : ℝ) / Real.sqrt ((n : ℝ) + 1) by rfl]
  field_simp [hsqrt_ne]
  nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)]

/-- Helper for Theorem 8.48: scaling the half-tail harmonic ratio estimate by `L / 2` yields the
explicit `O(1 / √k)` suffix-window rate constant. -/
lemma scaledPartialTailRatioLeRateConstant
    (hL : 0 ≤ L) (D : ℝ) (hD : 0 ≤ D) (k : ℕ) :
    (L / 2) *
        (D + Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
          Finset.sum (Finset.Icc (k / 2) k) γ ≤
      (2 * L * (D + Real.log 3)) / Real.sqrt ((k : ℝ) + 2) := by
  have hratio := harmonic_half_tail_ratio_le_log_three_bound D hD k
  have hLhalf_nonneg : 0 ≤ L / 2 := by
    positivity
  have hscaled :
      (L / 2) * ((D + harmonicHalfTailSum k) / inverseSqrtHalfTailSum k) ≤
        (L / 2) * ((4 * (D + Real.log 3)) / Real.sqrt ((k : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_left hratio hLhalf_nonneg
  -- Normalize the suffix sums to the named Lemma 8.27 owners before simplifying the scalar factor.
  rw [← partialGammaSqSum_eq_harmonicHalfTailSum (k := k), inverseSqrtHalfTailSum_eq_sum] at hscaled
  calc
    (L / 2) *
        (D + Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
          Finset.sum (Finset.Icc (k / 2) k) γ
      ≤ (L / 2) * ((4 * (D + Real.log 3)) / Real.sqrt ((k : ℝ) + 2)) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled
    _ = (2 * L * (D + Real.log 3)) / Real.sqrt ((k : ℝ) + 2) := by
          ring_nf

/-- Helper for Theorem 8.48: on the active suffix window, the repaired partial average is the
`centerMass` attached to the suffix weights `γ_n / ‖g(x^n)‖₂`. -/
lemma partialAverageEqCenterMassOfActiveWindow
    {k : ℕ} (hactive : ∀ n ∈ Finset.Icc (k / 2) k, constraintSeq n ≠ 0) :
    partialAvg k =
      (Finset.Icc (k / 2) k).centerMass
        (fun n ↦ γ n / ‖constraintSeq n‖)
        (fun n ↦ (xSeq n : E)) := by
  have hbridge :=
    dual_projected_subgradient_partial_average_iterate_eq_weighted_sum
      (X := X) (g := g) xSel γ lam0 (k := k) hactive
  -- Rewrite the repaired suffix average to the weighted-window normal form from Lemma 8.45.
  calc
    partialAvg k
        = Finset.sum (Finset.Icc (k / 2) k) fun n ↦
            ((γ n / ‖constraintSeq n‖) /
              Finset.sum (Finset.Icc (k / 2) k) fun j ↦ γ j / ‖constraintSeq j‖) • (xSeq n : E) :=
      hbridge
    _ = (Finset.Icc (k / 2) k).centerMass
          (fun n ↦ γ n / ‖constraintSeq n‖)
          (fun n ↦ (xSeq n : E)) := by
        simpa using
          (activeWindowAverage_eq_centerMass
            (X := X) (g := g) xSel γ lam0 (p := k / 2) (k := k))

/-- Helper for Theorem 8.48: the repaired suffix average remains in the feasible set `X`. -/
lemma partialAverageMem
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    {k : ℕ} :
    partialAvg k ∈ X := by
  by_cases hzero : ∃ n ∈ Finset.Icc (k / 2) k, constraintSeq n = 0
  · have hcurrent :=
      dual_projected_subgradient_partial_average_iterate_eq_current_of_exists_constraint_eq_zero
        (X := X) (g := g) xSel γ lam0 (k := k) hzero
    -- On the zero-constraint branch the repaired suffix average is the current feasible iterate.
    exact hcurrent ▸ (xSeq k).property
  · have hactive : ∀ n ∈ Finset.Icc (k / 2) k, constraintSeq n ≠ 0 := by
      intro n hn
      exact fun hconstraint ↦ hzero ⟨n, hn, hconstraint⟩
    have hk_div_le : k / 2 ≤ k := by
      omega
    have hp_mem : k / 2 ∈ Finset.Icc (k / 2) k := Finset.mem_Icc.mpr ⟨le_rfl, hk_div_le⟩
    have hweights_nonneg :
        ∀ n ∈ Finset.Icc (k / 2) k, 0 ≤ γ n / ‖constraintSeq n‖ := by
      intro n hn
      exact div_nonneg
        (le_of_lt (dual_projected_subgradient_method_stepsize_pos
          (X := X) (g := g) xSel γ h_admissible n))
        (norm_nonneg _)
    have hweights_pos :
        0 < ∑ n ∈ Finset.Icc (k / 2) k, γ n / ‖constraintSeq n‖ := by
      have hp_pos : 0 < γ (k / 2) / ‖constraintSeq (k / 2)‖ := by
        exact div_pos
          (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) xSel γ h_admissible (k / 2))
          (norm_pos_iff.mpr (hactive (k / 2) hp_mem))
      have hle :
          γ (k / 2) / ‖constraintSeq (k / 2)‖ ≤
            ∑ n ∈ Finset.Icc (k / 2) k, γ n / ‖constraintSeq n‖ :=
        Finset.single_le_sum (fun n hn ↦ hweights_nonneg n hn) hp_mem
      exact lt_of_lt_of_le hp_pos hle
    have hcenter :
        partialAvg k =
          (Finset.Icc (k / 2) k).centerMass
            (fun n ↦ γ n / ‖constraintSeq n‖)
            (fun n ↦ (xSeq n : E)) :=
      partialAverageEqCenterMassOfActiveWindow
        (X := X) (g := g) (xSel := xSel) (lam0 := lam0) hactive
    -- Route correction: pass to the `centerMass` interface first, then use convex feasibility of `X`.
    exact hcenter ▸
      h_problem.feasible_convex.centerMass_mem
        hweights_nonneg hweights_pos (fun n hn ↦ (xSeq n).property)

/-- Helper for Theorem 8.48: any feasible dual multiplier pairs with the constraint vector by at
most the Euclidean norm of the positive constraint violation. -/
private lemma dualFeasiblePairing_le_positiveConstraintViolation
    {x : E} {lam : Λ} (hLam : lam ∈ dual_problem_feasible_set m) :
    ∑ i, lam i * g i x ≤ ‖lam‖ * positive_constraint_violation gVec x := by
  let posVec : Λ := WithLp.toLp 2 ((gVec x)⁺)
  have hLam_nonneg : ∀ i : Fin m, 0 ≤ lam i := mem_dual_problem_feasible_set.mp hLam
  have hcoord_le :
      ∀ i : Fin m, lam i * g i x ≤ lam i * posVec i := by
    intro i
    have hg_le : g i x ≤ max (g i x) 0 := le_max_left _ _
    have hmul :=
      mul_le_mul_of_nonneg_left hg_le (hLam_nonneg i)
    simpa [posVec] using hmul
  have hsum_le :
      ∑ i, lam i * g i x ≤ ∑ i, lam i * posVec i := by
    exact Finset.sum_le_sum fun i _ ↦ hcoord_le i
  have hinner :
      ∑ i, lam i * posVec i = inner ℝ lam posVec := by
    have hinner' : inner ℝ lam posVec = ∑ i, posVec i * lam i := by
      -- Mathlib's `EuclideanSpace` inner product is indexed in the `y * star x` order.
      simpa [dotProduct, posVec] using
        (EuclideanSpace.inner_eq_star_dotProduct (x := lam) (y := posVec))
    -- Commute the real coordinates once, then rewrite with the canonical inner-product formula.
    calc
      ∑ i, lam i * posVec i = ∑ i, posVec i * lam i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
      _ = inner ℝ lam posVec := by
          simpa using hinner'.symm
  -- Route correction: isolate the sum-to-inner normalization here so later proofs only use the
  -- clean Euclidean bound against `positive_constraint_violation`.
  calc
    ∑ i, lam i * g i x ≤ ∑ i, lam i * posVec i := hsum_le
    _ = inner ℝ lam posVec := hinner
    _ ≤ ‖lam‖ * ‖posVec‖ := real_inner_le_norm _ _
    _ = ‖lam‖ * positive_constraint_violation gVec x := by
          rw [positive_constraint_violation_def]

/-- Helper for Theorem 8.48: the Slater ratio bounds the positive-part constraint violation from
below through an optimal dual multiplier, so every feasible point satisfies the support inequality
`0 ≤ f x - fOpt + α * positive_constraint_violation g x`. -/
lemma slaterRatio_supportsPositiveConstraintViolation
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    {x : E} (hx : x ∈ X) :
    0 ≤ f x - fOpt + α * positive_constraint_violation gVec x := by
  obtain ⟨lamStar, hlamStar_feasible, hlamStar_max, hqStar⟩ :=
    existsDualOptimalMultiplier_eq_fOpt
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) h_problem
  have hq_le_lagE :
      (fOpt : EReal) ≤
        ((lagrangian f (dual_constraint_vector g) lamStar x : ℝ) : EReal) := by
    -- Evaluate the dual objective at the feasible point `x`.
    have hq_le_lag :
        lagrangian_dual_objective X f (dual_constraint_vector g) lamStar ≤
          ((lagrangian f (dual_constraint_vector g) lamStar x : ℝ) : EReal) := by
      rw [lagrangian_dual_objective_eq_sInf]
      exact sInf_le <| Set.mem_image_of_mem
        (fun y : E ↦ ((lagrangian f (dual_constraint_vector g) lamStar y : ℝ) : EReal)) hx
    simpa [hqStar] using hq_le_lag
  have hq_le_lag :
      fOpt ≤ lagrangian f (dual_constraint_vector g) lamStar x := by
    exact_mod_cast hq_le_lagE
  have hpair :
      ∑ i, lamStar i * g i x ≤ ‖lamStar‖ * positive_constraint_violation gVec x :=
    dualFeasiblePairing_le_positiveConstraintViolation
      (g := g) (x := x) hlamStar_feasible
  have hnorm :
      ‖lamStar‖ ≤ α := by
    simpa using
      (norm_le_div_strict_feasibility_margin_of_dual_optimal_multiplier
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
        h_problem hxBar hgBar ⟨hlamStar_feasible, hlamStar_max⟩)
  have hviolation_nonneg : 0 ≤ positive_constraint_violation gVec x := by
    simp [positive_constraint_violation_def]
  have hlag :
      fOpt ≤ f x + ∑ i, lamStar i * g i x := by
    simpa [lagrangian_apply, dotProduct] using hq_le_lag
  have hsupport :
      fOpt ≤ f x + α * positive_constraint_violation gVec x := by
    have hscaled :
        ‖lamStar‖ * positive_constraint_violation gVec x ≤
          α * positive_constraint_violation gVec x :=
      mul_le_mul_of_nonneg_right hnorm hviolation_nonneg
    linarith
  -- Rearranging the optimal-multiplier support bound gives the desired nonnegative expression.
  linarith

/-- Helper for Theorem 8.48: the suffix average satisfies the objective-gap half of the
`O(1 / √k)` estimate, which is the `α = 0` branch of the main theorem. -/
lemma partialAverageObjectiveGapLeRateBase
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) (qOpt : EReal))
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    {k : ℕ} (hk : 2 ≤ k) :
    f (partialAvg k) - fOpt ≤
      (2 * L * (M ^ (2 : ℕ) + Real.log 3)) / Real.sqrt ((k : ℝ) + 2) := by
  have hk_div_le : k / 2 ≤ k := by
    omega
  have hL_nonneg : 0 ≤ L := by
    have hbound0 := h_constraint_bound (xSeq 0 : E) (xSeq 0).property
    exact le_trans (norm_nonneg _) hbound0
  have hLhalf_nonneg : 0 ≤ L / 2 := by
    positivity
  have hstepsize_le : ∀ n : ℕ, γ n ≤ 1 := by
    intro n
    have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) + 1) := by
      positivity
    have hsqrt_ge_one : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)]
    exact (div_le_iff₀ hsqrt_pos).2 <| by simpa using hsqrt_ge_one
  have hmult :
      ‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ ≤ M := by
    simpa using
      (dual_projected_subgradient_multiplier_norm_le_uniform_bound
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) (qOpt := qOpt) (L := L)
        (γ₀ := 1) xSel γ lam0
        h_problem h_admissible h_constraint_bound hstepsize_le hdual_value hxBar hgBar (k / 2))
  have hbase :
      f (partialAvg k) - fOpt ≤
        (L / 2) *
          (‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ ^ (2 : ℕ) +
              Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc (k / 2) k) γ := by
    by_cases hzero : ∃ n ∈ Finset.Icc (k / 2) k, constraintSeq n = 0
    · rcases hzero with ⟨n, hn, hconstraint⟩
      have hnk : n ≤ k := (Finset.mem_Icc.mp hn).2
      have hcurrent :
          constraintSeq k = 0 := by
        exact constraintSeqEqZeroOfLeOfConstraintEqZero
          (X := X) (g := g) xSel γ lam0 hnk hconstraint
      have havg :=
        dual_projected_subgradient_partial_average_iterate_eq_current_of_exists_constraint_eq_zero
          (X := X) (g := g) xSel γ lam0 (k := k) ⟨n, hn, hconstraint⟩
      have hwindow :
          f (xSeq k : E) - fOpt + 0 * positive_constraint_violation gVec (xSeq k : E) ≤
            (L / 2) *
              ((‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ + 0) ^
                    (2 : ℕ) +
                  Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
                Finset.sum (Finset.Icc (k / 2) k) γ := by
        exact
          windowPenalizedGapLeOfCurrentConstraintEqZero
            (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) (L := L)
            xSel γ lam0
            h_problem h_admissible h_constraint_bound
            (p := k / 2) (k := k) hk_div_le hcurrent 0
      -- On the zero branch, the suffix average is the current iterate and the penalty term vanishes.
      have hwindow' := hwindow
      rw [← havg] at hwindow'
      simpa [dual_projected_subgradient_method_zero] using hwindow'
    · have hactive : ∀ n ∈ Finset.Icc (k / 2) k, constraintSeq n ≠ 0 := by
        intro n hn
        exact fun hconstraint ↦ hzero ⟨n, hn, hconstraint⟩
      have hzeroMultiplier :
          dual_projected_subgradient_multiplier_vector (fun _ ↦ 0 : Fin m → NNReal) = 0 := by
        -- Normalize the zero test multiplier once so the active-window estimate matches the target.
        ext i
        simp [dual_projected_subgradient_multiplier_vector]
      have hwindowRaw :=
        windowGapWithTestMultiplierLeOfActiveWindow
          (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) (L := L)
          xSel γ lam0
          h_problem h_admissible h_constraint_bound
          (p := k / 2) (k := k) hk_div_le hactive (fun _ ↦ 0)
      have hwindow :
          f (Finset.sum (Finset.Icc (k / 2) k) fun n ↦
                ((γ n / ‖constraintSeq n‖) /
                  Finset.sum (Finset.Icc (k / 2) k) fun j ↦ γ j / ‖constraintSeq j‖) •
                    (xSeq n : E)) -
              fOpt ≤
            (L / 2) *
              (‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ ^ (2 : ℕ) +
                Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
              Finset.sum (Finset.Icc (k / 2) k) γ := by
        -- Expose the zero test multiplier before simplifying the norm term.
        simpa [hzeroMultiplier] using hwindowRaw
      have hbridge :=
        dual_projected_subgradient_partial_average_iterate_eq_weighted_sum
          (X := X) (g := g) xSel γ lam0 (k := k) hactive
      -- On the active branch, keep the repaired average in the weighted-window normal form.
      have hwindow' := hwindow
      rw [← hbridge] at hwindow'
      linarith
  have hsumγ_pos : 0 < Finset.sum (Finset.Icc (k / 2) k) γ := by
    have hp_mem : k / 2 ∈ Finset.Icc (k / 2) k := Finset.mem_Icc.mpr ⟨le_rfl, hk_div_le⟩
    have hle :
        γ (k / 2) ≤ Finset.sum (Finset.Icc (k / 2) k) γ :=
      Finset.single_le_sum
        (fun n _ ↦ le_of_lt
          (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) xSel γ h_admissible n))
        hp_mem
    exact lt_of_lt_of_le
      (dual_projected_subgradient_method_stepsize_pos
        (X := X) (g := g) xSel γ h_admissible (k / 2))
      hle
  have hnum_le :
      ‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ ^ (2 : ℕ) +
          Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ)) ≤
        M ^ (2 : ℕ) + Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ)) := by
    exact add_le_add
      (pow_le_pow_left₀ (norm_nonneg _) hmult 2)
      le_rfl
  have hquot_le :
      (‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ ^ (2 : ℕ) +
          Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc (k / 2) k) γ ≤
        (M ^ (2 : ℕ) + Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
          Finset.sum (Finset.Icc (k / 2) k) γ := by
    exact div_le_div_of_nonneg_right hnum_le (le_of_lt hsumγ_pos)
  have hreplace :
      (L / 2) *
          (‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ ^ (2 : ℕ) +
              Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc (k / 2) k) γ ≤
        (L / 2) *
          (M ^ (2 : ℕ) + Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc (k / 2) k) γ := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hquot_le hLhalf_nonneg)
  have hscaled :=
    scaledPartialTailRatioLeRateConstant
      (L := L) hL_nonneg (M ^ (2 : ℕ)) (sq_nonneg M) k
  -- Replace `‖λ^[k/2]‖` by the uniform bound `M`, then collapse the half-tail sums to `log 3`.
  exact le_trans hbase <| le_trans hreplace <| by
    simpa [partialGammaSqSum_eq_harmonicHalfTailSum] using hscaled

/-- Helper for Theorem 8.48: the suffix average satisfies the penalized estimate corresponding to
equation (8.89) with penalty coefficient `2 * α`. -/
lemma partialAveragePenalizedGapLeRate
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) (qOpt : EReal))
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    (hAlpha : 0 < α)
    {k : ℕ} (hk : 2 ≤ k) :
    f (partialAvg k) - fOpt + 2 * α * positive_constraint_violation gVec (partialAvg k) ≤
      C / Real.sqrt ((k : ℝ) + 2) := by
  have hL_nonneg : 0 ≤ L := by
    have hbound0 := h_constraint_bound (xSeq 0 : E) (xSeq 0).property
    exact le_trans (norm_nonneg _) hbound0
  have hLhalf_nonneg : 0 ≤ L / 2 := by
    positivity
  have hstepsize_le : ∀ n : ℕ, γ n ≤ 1 := by
    intro n
    have hsqrt_pos : 0 < Real.sqrt ((n : ℝ) + 1) := by
      positivity
    have hsqrt_ge_one : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
      nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) + 1 by positivity)]
    exact (div_le_iff₀ hsqrt_pos).2 <| by simpa using hsqrt_ge_one
  have hmult :
      ‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ ≤ M := by
    simpa using
      (dual_projected_subgradient_multiplier_norm_le_uniform_bound
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) (qOpt := qOpt) (L := L)
        (γ₀ := 1) xSel γ lam0
        h_problem h_admissible h_constraint_bound hstepsize_le hdual_value hxBar hgBar (k / 2))
  have hgap :
      f (partialAvg k) - fOpt + 2 * α * positive_constraint_violation gVec (partialAvg k) ≤
        (L / 2) *
          ((‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ + 2 * α) ^
                (2 : ℕ) +
              Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc (k / 2) k) γ := by
    exact
      dual_projected_subgradient_partial_average_gap_le
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) (L := L) xSel γ lam0
        h_problem h_admissible h_constraint_bound
        (by nlinarith) hk
  have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg _) hmult
  have hsumγ_pos : 0 < Finset.sum (Finset.Icc (k / 2) k) γ := by
    have hk_div_le : k / 2 ≤ k := by
      omega
    have hp_mem : k / 2 ∈ Finset.Icc (k / 2) k := Finset.mem_Icc.mpr ⟨le_rfl, hk_div_le⟩
    have hle :
        γ (k / 2) ≤ Finset.sum (Finset.Icc (k / 2) k) γ :=
      Finset.single_le_sum
        (fun n _ ↦ le_of_lt
          (dual_projected_subgradient_method_stepsize_pos
            (X := X) (g := g) xSel γ h_admissible n))
        hp_mem
    exact lt_of_lt_of_le
      (dual_projected_subgradient_method_stepsize_pos
        (X := X) (g := g) xSel γ h_admissible (k / 2))
      hle
  have hnum_le :
      (‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ + 2 * α) ^ (2 : ℕ) +
          Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ)) ≤
        (M + 2 * α) ^ (2 : ℕ) +
          Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ)) := by
    have hshift_le : ‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ + 2 * α ≤
        M + 2 * α := by
      linarith
    have hshift_nonneg :
        0 ≤ ‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ + 2 * α := by
      nlinarith [norm_nonneg
        (dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))), hAlpha]
    exact add_le_add
      (pow_le_pow_left₀ hshift_nonneg hshift_le 2)
      le_rfl
  have hquot_le :
      ((‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ + 2 * α) ^ (2 : ℕ) +
          Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc (k / 2) k) γ ≤
        ((M + 2 * α) ^ (2 : ℕ) +
            Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
          Finset.sum (Finset.Icc (k / 2) k) γ := by
    exact div_le_div_of_nonneg_right hnum_le (le_of_lt hsumγ_pos)
  have hreplace :
      (L / 2) *
          ((‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖ + 2 * α) ^
                (2 : ℕ) +
              Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc (k / 2) k) γ ≤
        (L / 2) *
          ((M + 2 * α) ^ (2 : ℕ) +
              Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ (γ n) ^ (2 : ℕ))) /
            Finset.sum (Finset.Icc (k / 2) k) γ := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (mul_le_mul_of_nonneg_left hquot_le hLhalf_nonneg)
  have hscaled :=
    scaledPartialTailRatioLeRateConstant
      (L := L) hL_nonneg ((M + 2 * α) ^ (2 : ℕ)) (sq_nonneg (M + 2 * α)) k
  -- Replace the suffix multiplier norm by `M`, then use the half-tail ratio estimate to expose `C`.
  exact le_trans hgap <| le_trans hreplace <| by
    simpa [dual_projected_subgradient_partial_average_rate_constant, partialGammaSqSum_eq_harmonicHalfTailSum]
      using hscaled

-- Proof sketch: apply
-- `dual_projected_subgradient_partial_average_gap_le` with `ρ = 2 * α` and the concrete
-- stepsize rule `γ_n = 1 / √(n + 1)`. Use
-- `dual_projected_subgradient_multiplier_norm_le_uniform_bound` to replace
-- `‖dual_projected_subgradient_multiplier_vector (lamSeq (k / 2))‖` by `M` using the canonical
-- dual-optimal-value hypothesis from Theorem 8.20, and then apply
-- `harmonic_half_tail_ratio_le_log_three_bound` with `D = (M + 2 * α) ^ 2` to obtain the
-- explicit `O(1 / √k)` constant. Finally package the two displayed bounds as a single `max`
-- estimate, following the textbook derivation from the penalized inequality and the dual-optimal
-- multiplier norm bound supplied by Corollary 8.43.
/-- Theorem 8.48: for the partial averaging iterate generated by the dual projected subgradient
method with stepsizes `γ_k = 1 / √(k + 1)`, both the objective gap and the scaled constraint
violation decay at rate `O(1 / √k)`; equivalently, the maximum of
`f(x^(k)) - fOpt` and `α * positive_constraint_violation g (x^(k))` is bounded by the explicit
constant built from the source quantities `M` and `α`. -/
theorem dual_projected_subgradient_partial_average_rate_max_le
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) (qOpt : EReal))
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    {k : ℕ} (hk : 2 ≤ k) :
    max
        (f (partialAvg k) - fOpt)
        (α * positive_constraint_violation (fun y i ↦ g i y) (partialAvg k)) ≤
      C / Real.sqrt ((k : ℝ) + 2) := by
  have hmargin_pos : 0 < strict_feasibility_margin g xBar :=
    strict_feasibility_margin_pos (g := g) hgBar
  have hxBar_feasible : xBar ∈ dual_projected_subgradient_feasible_set X g := by
    exact (mem_dual_projected_subgradient_feasible_set).2
      ⟨hxBar, fun i ↦ le_of_lt (hgBar i)⟩
  have hfOpt_le_fxBar : fOpt ≤ f xBar := by
    exact h_problem.optimal_value_isGLB.1 <| Set.mem_image_of_mem f hxBar_feasible
  have hAlpha_nonneg : 0 ≤ α := by
    exact div_nonneg (sub_nonneg.mpr hfOpt_le_fxBar) (le_of_lt hmargin_pos)
  have hL_nonneg : 0 ≤ L := by
    have hbound0 := h_constraint_bound (xSeq 0 : E) (xSeq 0).property
    exact le_trans (norm_nonneg _) hbound0
  have hrhs_nonneg : 0 ≤ C / Real.sqrt ((k : ℝ) + 2) := by
    have hlog_nonneg : 0 ≤ Real.log 3 := by
      exact Real.log_nonneg (by norm_num)
    have hnum_nonneg :
        0 ≤ 2 * L * ((M + 2 * α) ^ (2 : ℕ) + Real.log 3) := by
      have hinner_nonneg : 0 ≤ (M + 2 * α) ^ (2 : ℕ) + Real.log 3 := by
        nlinarith
      nlinarith
    have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 2) := by
      positivity
    simpa [dual_projected_subgradient_partial_average_rate_constant] using
      (div_nonneg hnum_nonneg (le_of_lt hsqrt_pos))
  by_cases hAlpha0 : α = 0
  · have hobj :=
      partialAverageObjectiveGapLeRateBase
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) (qOpt := qOpt) (L := L)
        (xSel := xSel) (lam0 := lam0)
        h_problem h_admissible h_constraint_bound hdual_value hxBar hgBar hk
    have hC :
        C = (2 * L * (M ^ (2 : ℕ) + Real.log 3)) := by
      rw [dual_projected_subgradient_partial_average_rate_constant, hAlpha0]
      ring
    have hobj' : f (partialAvg k) - fOpt ≤ C / Real.sqrt ((k : ℝ) + 2) := by
      rw [hC]
      simpa using hobj
    -- The `α = 0` branch needs only the objective estimate and nonnegativity of the shared rhs.
    rw [hAlpha0]
    exact max_le_iff.mpr ⟨hobj', by simpa using hrhs_nonneg⟩
  · have hAlpha : 0 < α := lt_of_le_of_ne hAlpha_nonneg (by simpa [eq_comm] using hAlpha0)
    have hpen :=
      partialAveragePenalizedGapLeRate
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) (qOpt := qOpt) (L := L)
        (xSel := xSel) (lam0 := lam0)
        h_problem h_admissible h_constraint_bound hdual_value hxBar hgBar hAlpha hk
    have hmem :=
      partialAverageMem
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
        (xSel := xSel) (lam0 := lam0) h_problem h_admissible (k := k)
    have hsupport :=
      slaterRatio_supportsPositiveConstraintViolation
        (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt)
        h_problem hxBar hgBar hmem
    have hviolation_nonneg :
        0 ≤ positive_constraint_violation gVec (partialAvg k) := by
      simp [positive_constraint_violation_def]
    have hobj :
        f (partialAvg k) - fOpt ≤ C / Real.sqrt ((k : ℝ) + 2) := by
      have hpenalty_nonneg :
          0 ≤ 2 * α * positive_constraint_violation gVec (partialAvg k) := by
        nlinarith
      linarith
    have hviol :
        α * positive_constraint_violation gVec (partialAvg k) ≤ C / Real.sqrt ((k : ℝ) + 2) := by
      linarith [hpen, show
        0 ≤ f (partialAvg k) - fOpt + α * positive_constraint_violation gVec (partialAvg k) by
          simpa using hsupport]
    -- The positive-`α` branch combines the penalized suffix estimate with the Slater support bound.
    simpa using max_le_iff.mpr ⟨hobj, hviol⟩

-- Proof sketch: apply `le_trans` with `le_max_left _ _` to the max bound from
-- `dual_projected_subgradient_partial_average_rate_max_le`.
/-- The partial averaging iterate satisfies the objective-gap estimate (8.86). -/
theorem dual_projected_subgradient_partial_average_objective_gap_le
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) (qOpt : EReal))
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    {k : ℕ} (hk : 2 ≤ k) :
    f (partialAvg k) - fOpt ≤ C / Real.sqrt ((k : ℝ) + 2) := by
  -- Project the objective-gap coordinate from the max estimate.
  exact le_trans (le_max_left _ _)
    (dual_projected_subgradient_partial_average_rate_max_le
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) (qOpt := qOpt) (L := L)
      (xSel := xSel) (lam0 := lam0)
      h_problem h_admissible h_constraint_bound hdual_value hxBar hgBar hk)

-- Proof sketch: extract the second component of
-- `dual_projected_subgradient_partial_average_rate_max_le` via `le_max_right _ _`, then rewrite
-- `α` by its defining formula
-- `(f xBar - fOpt) / strict_feasibility_margin g xBar` to obtain exactly the displayed bound
-- (8.87).
/-- If the Slater ratio `α` is positive, the partial averaging iterate satisfies the
constraint-violation estimate (8.87). -/
theorem dual_projected_subgradient_partial_average_constraint_norm_le
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    (h_admissible : dual_projected_subgradient_method_is_admissible X f g xSel γ)
    (h_constraint_bound :
      ∀ x ∈ X, ‖dual_projected_subgradient_constraint_vector g x‖ ≤ L)
    (hdual_value : IsLUB (q '' dual_problem_feasible_set m) (qOpt : EReal))
    (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    (hAlpha : 0 < α)
    {k : ℕ} (hk : 2 ≤ k) :
    positive_constraint_violation (fun y i ↦ g i y) (partialAvg k) ≤
      C / (α * Real.sqrt ((k : ℝ) + 2)) := by
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 2) := by
    positivity
  have hmain :=
    dual_projected_subgradient_partial_average_rate_max_le
      (X := X) (XStar := XStar) (f := f) (g := g) (fOpt := fOpt) (qOpt := qOpt) (L := L)
      (xSel := xSel) (lam0 := lam0)
      h_problem h_admissible h_constraint_bound hdual_value hxBar hgBar hk
  have hscaled :
      α * positive_constraint_violation (fun y i ↦ g i y) (partialAvg k) ≤
        C / Real.sqrt ((k : ℝ) + 2) := by
    exact le_trans (le_max_right _ _) hmain
  have hdiv :
      positive_constraint_violation (fun y i ↦ g i y) (partialAvg k) ≤
        (C / Real.sqrt ((k : ℝ) + 2)) / α := by
    exact (le_div_iff₀ hAlpha).2 <| by simpa [mul_comm] using hscaled
  -- Rewrite the divided bound into the displayed denominator `α * √(k + 2)`.
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

end
