/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_41
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped BigOperators DeltaN WithTopConvexAnalysis

/- Proposition 3.36 lies in the chapter's unconstrained subgradient-method / finite-prefix
stepsize-bound domain.

Sampled owner-style declarations:
- `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in `Theorem_3_44`, the chapter
  owner surface for real-valued whole-space subgradients, written here as `∂[Set.univ] f(x)`;
- `bestFunctionValueUpTo` in `Definition_3_55`, the chapter owner for best-so-far sampled values;
- `deltaN` and `deltaN_apply` in `Definition_3_41`, the chapter owner and evaluation bridge for
  the finite-horizon stepsize scalar `Δ_N(h₀, ..., h_N)`;
- `bestFunctionValueGapUpTo_le_lipschitz_mul_stepsize_ratio` in `Theorem_3_2_2`, the chapter's
  owner sampled-gap estimate written on the `bestFunctionValueUpTo` / `deltaN` surface.

Best owner abstraction:
- source-facing: the constant-stepsize sampled-gap bound for the unconstrained subgradient method;
- core/canonical: `bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N` together with the finite-prefix
  scalar owner `deltaN N R`;
- bridge/view: the constant stepsize prefix `fun _ ↦ ε / M`.

Primitive data:
- the objective `f`;
- the iterate sequence `xSeq`;
- the chosen whole-space subgradient selection `g`;
- the minimizing point `xStar`;
- the initial radius bound `‖xSeq 0 - xStar‖ ≤ R`;
- the constant stepsize `ε / M²`.

Derived API:
- the best sampled value `bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N`;
- the textbook constant-stepsize bound
  `M^2 * R^2 / (2 * ε * N) + ε / 2` for `N ≥ 1`;
- the auxiliary `ε`-accuracy threshold corollary.

The source tree is unavailable in this workspace, so this repair follows the runner-supplied
Proposition 3.36 data together with the semantic-defect report: the threshold
`N ≥ M² * R² / ε²` and the finite-prefix bound
`M² * R² / (2 * ε * N) + ε / 2` are mutually consistent with the raw subgradient update
`x_{i+1} = x_i - (ε / M²) • g_i`, so this file repairs the recurrence surface to that standard
scaling.
-/

section ConstantStepsize

variable (f : E → ℝ) (xStar : E) (R M ε : ℝ)
variable (xSeq g : ℕ → E)

/-- Helper for Proposition 3.36: a whole-space subgradient at `y` bounds the objective gap to
`xStar` by the corresponding inner product. -/
lemma subgradientGapLeInnerToMinimizer
    {y g0 : E}
    (hg0 : g0 ∈ ∂[Set.univ] f(y)) :
    f y - f xStar ≤ inner ℝ g0 (y - xStar) := by
  -- Evaluate the whole-space support inequality at the comparison point `xStar`.
  have hsupport :=
    (mem_subdifferentialWithin_iff.mp hg0).2 (by simp : xStar ∈ Set.univ)
  have hsupport' : f xStar ≥ f y + inner ℝ g0 (xStar - y) := by
    simpa using hsupport
  have hinner : inner ℝ g0 (xStar - y) = -inner ℝ g0 (y - xStar) := by
    rw [show xStar - y = -(y - xStar) by abel_nf, inner_neg_right]
  linarith

/-- Helper for Proposition 3.36: one constant-step subgradient update bounds the current gap by
the squared-distance drop plus the constant stepsize error term. -/
lemma constantStepsizeGapLeDistanceDrop
    (hM : 0 < M) (hε : 0 < ε)
    (hxSeq_succ : ∀ i, xSeq (i + 1) = xSeq i - (ε / M ^ (2 : ℕ)) • g i)
    (h_subgradient : ∀ i, g i ∈ ∂[Set.univ] f((xSeq i)))
    (h_subgradient_bound : ∀ i, ‖g i‖ ≤ M)
    (i : ℕ) :
    f (xSeq i) - f xStar ≤
      (M ^ (2 : ℕ) / (2 * ε)) *
          (‖xSeq i - xStar‖ ^ (2 : ℕ) - ‖xSeq (i + 1) - xStar‖ ^ (2 : ℕ)) +
        ε / 2 := by
  let α : ℝ := ε / M ^ (2 : ℕ)
  let gap : ℝ := f (xSeq i) - f xStar
  let dNow : ℝ := ‖xSeq i - xStar‖ ^ (2 : ℕ)
  let dNext : ℝ := ‖xSeq (i + 1) - xStar‖ ^ (2 : ℕ)
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    positivity
  have hgap_le :
      gap ≤ inner ℝ (g i) (xSeq i - xStar) := by
    simpa [gap] using
      subgradientGapLeInnerToMinimizer (f := f) (xStar := xStar) (hg0 := h_subgradient i)
  have hgap_le' :
      gap ≤ inner ℝ (xSeq i - xStar) (g i) := by
    simpa [real_inner_comm] using hgap_le
  have hnorm_sq_le : ‖g i‖ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
    simpa [pow_two] using
      (sq_le_sq₀ (norm_nonneg _) (le_of_lt hM)).2 (h_subgradient_bound i)
  have hexpand :
      dNext =
        dNow - 2 * α * inner ℝ (xSeq i - xStar) (g i) + α ^ (2 : ℕ) * ‖g i‖ ^ (2 : ℕ) := by
    -- Expand the explicit squared norm of the constant-step update.
    calc
      dNext
          = ‖(xSeq i - α • g i) - xStar‖ ^ (2 : ℕ) := by
              simp [dNext, α, hxSeq_succ i]
      _ = ‖(xSeq i - xStar) - α • g i‖ ^ (2 : ℕ) := by
            congr 1
            abel_nf
      _ = ‖xSeq i - xStar‖ ^ (2 : ℕ) -
            2 * inner ℝ (xSeq i - xStar) (α • g i) +
            ‖α • g i‖ ^ (2 : ℕ) := by
            simpa using norm_sub_sq_real (xSeq i - xStar) (α • g i)
      _ = dNow - 2 * α * inner ℝ (xSeq i - xStar) (g i) +
            α ^ (2 : ℕ) * ‖g i‖ ^ (2 : ℕ) := by
            dsimp [dNow]
            rw [real_inner_smul_right]
            rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
            ring
  have hdist_bound :
      dNext ≤ dNow - 2 * α * gap + α ^ (2 : ℕ) * M ^ (2 : ℕ) := by
    -- Replace the inner product by the objective gap and the subgradient norm by `M`.
    rw [hexpand]
    have hinner_term :
        -2 * α * inner ℝ (xSeq i - xStar) (g i) ≤ -2 * α * gap := by
      have hscaled_gap :=
        mul_le_mul_of_nonneg_left hgap_le' (show 0 ≤ 2 * α by positivity)
      have hneg := neg_le_neg hscaled_gap
      simpa [neg_mul, mul_assoc, mul_left_comm, mul_comm] using hneg
    have hquad_term :
        α ^ (2 : ℕ) * ‖g i‖ ^ (2 : ℕ) ≤ α ^ (2 : ℕ) * M ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hnorm_sq_le (show 0 ≤ α ^ (2 : ℕ) by positivity)
    nlinarith
  have hmain :
      2 * ε * gap ≤
        M ^ (2 : ℕ) * (‖xSeq i - xStar‖ ^ (2 : ℕ) - ‖xSeq (i + 1) - xStar‖ ^ (2 : ℕ)) +
          ε ^ (2 : ℕ) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hdist_bound (show 0 ≤ M ^ (2 : ℕ) by positivity)
    dsimp [α, gap, dNow, dNext] at hmul
    field_simp [pow_two, hM.ne'] at hmul
    nlinarith
  have hgoal_scaled :
      2 * ε * gap ≤
        2 * ε *
          ((M ^ (2 : ℕ) / (2 * ε)) *
              (‖xSeq i - xStar‖ ^ (2 : ℕ) - ‖xSeq (i + 1) - xStar‖ ^ (2 : ℕ)) +
            ε / 2) := by
    calc
      2 * ε * gap
          ≤ M ^ (2 : ℕ) * (‖xSeq i - xStar‖ ^ (2 : ℕ) - ‖xSeq (i + 1) - xStar‖ ^ (2 : ℕ)) +
              ε ^ (2 : ℕ) := hmain
      _ = 2 * ε *
            ((M ^ (2 : ℕ) / (2 * ε)) *
                (‖xSeq i - xStar‖ ^ (2 : ℕ) - ‖xSeq (i + 1) - xStar‖ ^ (2 : ℕ)) +
              ε / 2) := by
            field_simp [pow_two, hε.ne']
  nlinarith [hgoal_scaled]

/-- Helper for Proposition 3.36: summing the one-step estimate over the first `N` updates yields a
prefix budget with the terminal squared distance kept explicit. -/
lemma sumPrefixGapsLeDistanceBudget
    (hM : 0 < M) (hε : 0 < ε)
    (hxSeq_succ : ∀ i, xSeq (i + 1) = xSeq i - (ε / M ^ (2 : ℕ)) • g i)
    (h_subgradient : ∀ i, g i ∈ ∂[Set.univ] f((xSeq i)))
    (h_subgradient_bound : ∀ i, ‖g i‖ ≤ M)
    (N : ℕ) :
    Finset.sum (Finset.range N) (fun i ↦ f (xSeq i) - f xStar) ≤
      (M ^ (2 : ℕ) / (2 * ε)) *
          (‖xSeq 0 - xStar‖ ^ (2 : ℕ) - ‖xSeq N - xStar‖ ^ (2 : ℕ)) +
        (N : ℝ) * ε / 2 := by
  let A : ℝ := M ^ (2 : ℕ) / (2 * ε)
  induction N with
  | zero =>
      -- The empty prefix has zero gap sum and zero budget.
      simp
  | succ N ih =>
      have hstep :=
        constantStepsizeGapLeDistanceDrop
          (f := f) (xStar := xStar) (M := M) (ε := ε) (xSeq := xSeq) (g := g)
          hM hε hxSeq_succ h_subgradient h_subgradient_bound N
      have hcombine :
          Finset.sum (Finset.range (N + 1)) (fun i ↦ f (xSeq i) - f xStar) ≤
            A * (‖xSeq 0 - xStar‖ ^ (2 : ℕ) - ‖xSeq (N + 1) - xStar‖ ^ (2 : ℕ)) +
              ((N + 1 : ℕ) : ℝ) * ε / 2 := by
        rw [Finset.sum_range_succ]
        dsimp [A] at ih hstep ⊢
        have hadd := add_le_add ih hstep
        calc
          Finset.sum (Finset.range N) (fun i ↦ f (xSeq i) - f xStar) + (f (xSeq N) - f xStar)
              ≤ M ^ (2 : ℕ) / (2 * ε) * (‖xSeq 0 - xStar‖ ^ (2 : ℕ) - ‖xSeq N - xStar‖ ^ (2 : ℕ)) +
                  (N : ℝ) * ε / 2 +
                (M ^ (2 : ℕ) / (2 * ε) * (‖xSeq N - xStar‖ ^ (2 : ℕ) -
                    ‖xSeq (N + 1) - xStar‖ ^ (2 : ℕ)) +
                  ε / 2) := hadd
          _ = M ^ (2 : ℕ) / (2 * ε) * (‖xSeq 0 - xStar‖ ^ (2 : ℕ) -
                  ‖xSeq (N + 1) - xStar‖ ^ (2 : ℕ)) +
                ((N + 1 : ℕ) : ℝ) * ε / 2 := by
                  norm_num [Nat.cast_add]
                  ring_nf
      simpa using hcombine

/-- Helper for Proposition 3.36: dropping the nonnegative terminal squared-distance term turns the
prefix budget into the textbook constant-stepsize error bound. -/
lemma sumPrefixGapsLeConstantStepsizeBudget
    (hM : 0 < M) (hε : 0 < ε)
    (hxSeq_succ : ∀ i, xSeq (i + 1) = xSeq i - (ε / M ^ (2 : ℕ)) • g i)
    (h_subgradient : ∀ i, g i ∈ ∂[Set.univ] f((xSeq i)))
    (h_subgradient_bound : ∀ i, ‖g i‖ ≤ M)
    (N : ℕ) :
    Finset.sum (Finset.range N) (fun i ↦ f (xSeq i) - f xStar) ≤
      M ^ (2 : ℕ) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ) / (2 * ε) + (N : ℝ) * ε / 2 := by
  let A : ℝ := M ^ (2 : ℕ) / (2 * ε)
  have hraw :=
    sumPrefixGapsLeDistanceBudget
      (f := f) (xStar := xStar) (M := M) (ε := ε) (xSeq := xSeq) (g := g)
      hM hε hxSeq_succ h_subgradient h_subgradient_bound N
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hdist_nonneg : 0 ≤ ‖xSeq N - xStar‖ ^ (2 : ℕ) := by
    positivity
  have hdrop :
      A * (‖xSeq 0 - xStar‖ ^ (2 : ℕ) - ‖xSeq N - xStar‖ ^ (2 : ℕ)) ≤
        A * ‖xSeq 0 - xStar‖ ^ (2 : ℕ) := by
    nlinarith
  calc
    Finset.sum (Finset.range N) (fun i ↦ f (xSeq i) - f xStar)
        ≤ A * (‖xSeq 0 - xStar‖ ^ (2 : ℕ) - ‖xSeq N - xStar‖ ^ (2 : ℕ)) +
            (N : ℝ) * ε / 2 := hraw
    _ ≤ A * ‖xSeq 0 - xStar‖ ^ (2 : ℕ) + (N : ℝ) * ε / 2 := by
          nlinarith
    _ = M ^ (2 : ℕ) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ) / (2 * ε) + (N : ℝ) * ε / 2 := by
          simp [A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 3.36: the first `N` sampled gaps dominate `N` copies of the best
sampled gap up to iteration `N`. -/
lemma bestObjectiveGapMulLeSumPrefixGaps
    (N : ℕ) :
    (N : ℝ) * (bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N - f xStar) ≤
      Finset.sum (Finset.range N) (fun i ↦ f (xSeq i) - f xStar) := by
  -- Compare the sampled minimum with each of the first `N` sampled objective values.
  calc
    (N : ℝ) * (bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N - f xStar)
        = Finset.sum (Finset.range N)
            (fun _i ↦ bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N - f xStar) := by
            simp
            ring
    _ ≤ Finset.sum (Finset.range N) (fun i ↦ f (xSeq i) - f xStar) := by
          refine Finset.sum_le_sum ?_
          intro i hi
          exact sub_le_sub_right
            (bestFunctionValueUpTo_le
              ⟨i, Nat.lt_succ_of_lt (Finset.mem_range.mp hi)⟩) _

/-- Helper for Proposition 3.36: the threshold `M² * R² / ε² ≤ N` implies the first term of the
constant-step bound is at most `ε / 2`. -/
lemma constantStepsizeThresholdTermLeHalfEps
    {N : ℕ}
    (hε : 0 < ε) (hN : 1 ≤ N)
    (h_threshold : M ^ (2 : ℕ) * R ^ (2 : ℕ) / ε ^ (2 : ℕ) ≤ N) :
    M ^ (2 : ℕ) * R ^ (2 : ℕ) / (2 * ε * N) ≤ ε / 2 := by
  have hN_real : 0 < (N : ℝ) := by
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hε_sq_pos : 0 < ε ^ (2 : ℕ) := by
    positivity
  have hthreshold' : M ^ (2 : ℕ) * R ^ (2 : ℕ) ≤ (N : ℝ) * ε ^ (2 : ℕ) := by
    exact (div_le_iff₀ hε_sq_pos).mp (by simpa using h_threshold)
  have hmul :
      M ^ (2 : ℕ) * R ^ (2 : ℕ) ≤ (ε / 2) * (2 * ε * N) := by
    nlinarith
  exact (div_le_iff₀ (show 0 < 2 * ε * N by positivity)).2 hmul

/-- Proposition 3.36: if `f` is convex on the ambient space,
`x_{i+1} = x_i - (ε / M²) • g_i`, each `g_i` is a subgradient of `f` at `x_i`
with `‖g_i‖ ≤ M`, and a chosen minimizer `xStar` satisfies `‖x₀ - xStar‖ ≤ R`, then the best
sampled objective value `bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N` among `x₀, …, x_N`
satisfies the textbook constant-stepsize estimate
`M^2 * R^2 / (2 * ε * N) + ε / 2` for every integer `N ≥ 1`. -/
-- Semantic recall: chapter precedent and mathlib use `ConvexOn ℝ Set.univ f` for whole-space
-- convexity, matching the source hypothesis "let `f : ℝⁿ → ℝ` be a convex function"; a
-- `lean_leansearch` query found no more canonical owner theorem for this exact subgradient bound,
-- so the chapter-local surface remains the governing API precedent.
-- Proof sketch: expand `‖xSeq (i + 1) - xStar‖²`, use convexity plus the subgradient inequality at
-- `xSeq i` with comparison point `xStar`, and bound the raw step through `‖g i‖ ≤ M`.
-- Summing the one-step recursion over the first `N` steps and specializing the constant stepsize
-- `ε / M²` yields `M² * R² / (2 * ε * N) + ε / 2`.
theorem subgradientMethod_bestObjectiveValue_sub_le_of_constant_stepsize
    (hM : 0 < M) (hε : 0 < ε)
    (h_convex : ConvexOn ℝ Set.univ f)
    (hxStar_min : IsMinOn f Set.univ xStar)
    (hxSeq_zero_dist : ‖xSeq 0 - xStar‖ ≤ R)
    (hxSeq_succ : ∀ i, xSeq (i + 1) = xSeq i - (ε / M ^ (2 : ℕ)) • g i)
    (h_subgradient : ∀ i, g i ∈ ∂[Set.univ] f((xSeq i)))
    (h_subgradient_bound : ∀ i, ‖g i‖ ≤ M)
    (N : ℕ) (hN : 1 ≤ N) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N - f xStar ≤
      M ^ (2 : ℕ) * R ^ (2 : ℕ) / (2 * ε * N) + ε / 2 := by
  let gapBest : ℝ := bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N - f xStar
  have hN_real : 0 < (N : ℝ) := by
    exact Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hR_nonneg : 0 ≤ R := by
    exact le_trans (norm_nonneg _) hxSeq_zero_dist
  have hdist0_sq_le : ‖xSeq 0 - xStar‖ ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
    simpa [pow_two] using
      (sq_le_sq₀ (norm_nonneg _) hR_nonneg).2 hxSeq_zero_dist
  have hsum :
      Finset.sum (Finset.range N) (fun i ↦ f (xSeq i) - f xStar) ≤
        M ^ (2 : ℕ) * R ^ (2 : ℕ) / (2 * ε) + (N : ℝ) * ε / 2 := by
    have hprefix :=
      sumPrefixGapsLeConstantStepsizeBudget
        (f := f) (xStar := xStar) (M := M) (ε := ε) (xSeq := xSeq) (g := g)
        hM hε hxSeq_succ h_subgradient h_subgradient_bound N
    have hscale_nonneg : 0 ≤ M ^ (2 : ℕ) / (2 * ε) := by
      positivity
    have hradius :
        M ^ (2 : ℕ) * ‖xSeq 0 - xStar‖ ^ (2 : ℕ) / (2 * ε) ≤
          M ^ (2 : ℕ) * R ^ (2 : ℕ) / (2 * ε) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hdist0_sq_le hscale_nonneg
    exact hprefix.trans <|
      by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hradius ((N : ℝ) * ε / 2)
  have hbest_mul :
      (N : ℝ) * gapBest ≤
        (N : ℝ) *
          (M ^ (2 : ℕ) * R ^ (2 : ℕ) / (2 * ε * N) + ε / 2) := by
    calc
      (N : ℝ) * gapBest
          ≤ Finset.sum (Finset.range N) (fun i ↦ f (xSeq i) - f xStar) := by
              simpa [gapBest] using
                bestObjectiveGapMulLeSumPrefixGaps
                  (f := f) (xStar := xStar) (xSeq := xSeq) N
      _ ≤ M ^ (2 : ℕ) * R ^ (2 : ℕ) / (2 * ε) + (N : ℝ) * ε / 2 := hsum
      _ = (N : ℝ) *
            (M ^ (2 : ℕ) * R ^ (2 : ℕ) / (2 * ε * N) + ε / 2) := by
            field_simp [hN_real.ne', hε.ne']
  nlinarith [hbest_mul]

/-- Auxiliary threshold corollary: if the iteration count is at least
`M² * R² / ε²`, then the constant-step subgradient bound gives an `ε`-accurate sampled objective
value. -/
-- Proof sketch: combine
-- `subgradientMethod_bestObjectiveValue_sub_le_of_constant_stepsize` with the threshold estimate
-- `M² * R² / (2 * ε * N) ≤ ε / 2`, obtained from `M² * R² / ε² ≤ N`, and add the
-- `ε / 2` term.
theorem subgradientMethod_bestObjectiveValue_sub_le_eps_of_constant_stepsize_threshold
    (hM : 0 < M) (hε : 0 < ε)
    (h_convex : ConvexOn ℝ Set.univ f)
    (hxStar_min : IsMinOn f Set.univ xStar)
    (hxSeq_zero_dist : ‖xSeq 0 - xStar‖ ≤ R)
    (hxSeq_succ : ∀ i, xSeq (i + 1) = xSeq i - (ε / M ^ (2 : ℕ)) • g i)
    (h_subgradient : ∀ i, g i ∈ ∂[Set.univ] f((xSeq i)))
    (h_subgradient_bound : ∀ i, ‖g i‖ ≤ M)
    (N : ℕ)
    (h_threshold : M ^ (2 : ℕ) * R ^ (2 : ℕ) / ε ^ (2 : ℕ) ≤ N) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N - f xStar ≤ ε := by
  by_cases hN0 : N = 0
  · -- When `N = 0`, the threshold forces `R = 0`, so the initial point is already optimal.
    subst hN0
    have hratio_nonneg : 0 ≤ M ^ (2 : ℕ) * R ^ (2 : ℕ) / ε ^ (2 : ℕ) := by
      positivity
    have hratio_eq : M ^ (2 : ℕ) * R ^ (2 : ℕ) / ε ^ (2 : ℕ) = 0 := by
      exact le_antisymm (by simpa using h_threshold) hratio_nonneg
    have hnum_eq : M ^ (2 : ℕ) * R ^ (2 : ℕ) = 0 := by
      exact (div_eq_zero_iff.mp hratio_eq).resolve_right (by positivity : ε ^ (2 : ℕ) ≠ 0)
    have hR_sq_eq : R ^ (2 : ℕ) = 0 := by
      exact (mul_eq_zero.mp hnum_eq).resolve_left (by positivity : M ^ (2 : ℕ) ≠ 0)
    have hR_eq : R = 0 := by
      nlinarith [sq_nonneg R, hR_sq_eq]
    have hdist_eq : ‖xSeq 0 - xStar‖ = 0 := by
      exact le_antisymm (by simpa [hR_eq] using hxSeq_zero_dist) (norm_nonneg _)
    have hx0_eq : xSeq 0 = xStar := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hdist_eq)
    simpa [bestFunctionValueUpTo, hx0_eq] using (show (0 : ℝ) ≤ ε by linarith)
  · -- For `N ≥ 1`, combine the main theorem with the threshold estimate on the first term.
    have hN : 1 ≤ N := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN0)
    have hmain :=
      subgradientMethod_bestObjectiveValue_sub_le_of_constant_stepsize
        (f := f) (xStar := xStar) (R := R) (M := M) (ε := ε) (xSeq := xSeq) (g := g)
        hM hε h_convex hxStar_min hxSeq_zero_dist hxSeq_succ h_subgradient h_subgradient_bound N hN
    have hhalf :=
      constantStepsizeThresholdTermLeHalfEps
        (M := M) (R := R) (ε := ε) hε hN h_threshold
    linarith

end ConstantStepsize

end
