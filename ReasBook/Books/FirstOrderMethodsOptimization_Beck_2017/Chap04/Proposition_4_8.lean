/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 4.8 is `source-facing` in the Chapter 4 conjugacy API. The chapter owner
abstraction for Fenchel conjugates is already `conjugate_function` from Definition 4.1, so this
file keeps only the negative-log barrier and its conjugacy formulas rather than a parallel local
copy of the owner definition. -/
recall conjugate_function_primal
recall conjugate_function_primal_apply

/-- The negative-log barrier, equal to `-log x` on the positive ray and `∞` on the nonpositive
half-line. -/
def negative_log_barrier : ℝ → EReal :=
  fun x ↦ if 0 < x then ((-Real.log x : ℝ) : EReal) else ⊤

/-- On the positive ray, `negative_log_barrier` equals `-log x`. -/
@[simp] theorem negative_log_barrier_of_pos {x : ℝ} (hx : 0 < x) :
    negative_log_barrier x = ((-Real.log x : ℝ) : EReal) := by
  simp [negative_log_barrier, hx]

/-- On the nonpositive ray, `negative_log_barrier` equals `∞`. -/
@[simp] theorem negative_log_barrier_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    negative_log_barrier x = ⊤ := by
  simp [negative_log_barrier, not_lt.mpr hx]

/-- Helper for Proposition 4.8: the conjugate-defining range for `negative_log_barrier` splits
into the `⊥` contribution from the nonpositive half-line and the logarithmic objective on
`Set.Ioi 0`. -/
lemma negativeLogBarrierPairingRange_eq_insertBotImage
    (y : ℝ) :
    Set.range
        (fun x : ℝ ↦ (((InnerProductSpace.toDualMap ℝ ℝ y) x : ℝ) : EReal) -
          negative_log_barrier x) =
      insert ⊥ ((fun x : ℝ ↦ ((x * y + Real.log x : ℝ) : EReal)) '' Set.Ioi (0 : ℝ)) := by
  -- Compare the conjugate-defining range pointwise, splitting the source variable by positivity.
  ext z
  constructor
  · intro hz
    rcases hz with ⟨x, rfl⟩
    by_cases hx : 0 < x
    · right
      refine ⟨x, hx, ?_⟩
      -- On the positive ray, subtracting `-log x` yields the finite real objective.
      change ((x * y + Real.log x : ℝ) : EReal) =
        (((InnerProductSpace.toDualMap ℝ ℝ y) x : ℝ) : EReal) - negative_log_barrier x
      rw [negative_log_barrier_of_pos hx, ← EReal.coe_sub]
      congr 1
      have hinner' : inner ℝ y x = x * y := by
        rfl
      have hinner : inner ℝ y x = y * x := by
        simpa [mul_comm] using hinner'
      calc
        x * y + Real.log x = y * x - -Real.log x := by ring
        _ = inner ℝ y x - -Real.log x := by rw [hinner]
    · left
      have hx' : x ≤ 0 := le_of_not_gt hx
      -- On the nonpositive half-line, the barrier is `⊤`, so the contribution is exactly `⊥`.
      simp [negative_log_barrier, hx, InnerProductSpace.toDualMap_apply_apply]
  · intro hz
    rcases hz with rfl | hz
    · refine ⟨0, ?_⟩
      have hzero : ¬ 0 < (0 : ℝ) := by
        exact lt_irrefl 0
      -- The point `x = 0` already realizes the `⊥` contribution.
      simp [negative_log_barrier, hzero, InnerProductSpace.toDualMap_apply_apply]
    · rcases hz with ⟨x, hx, rfl⟩
      refine ⟨x, ?_⟩
      -- A positive-ray point already appears in the original range with the same value.
      change ((((InnerProductSpace.toDualMap ℝ ℝ y) x : ℝ) : EReal) - negative_log_barrier x =
        ((x * y + Real.log x : ℝ) : EReal))
      rw [negative_log_barrier_of_pos hx, ← EReal.coe_sub]
      congr 1
      have hinner' : inner ℝ y x = x * y := by
        rfl
      have hinner : inner ℝ y x = y * x := by
        simpa [mul_comm] using hinner'
      calc
        inner ℝ y x - -Real.log x = y * x + Real.log x := by
          rw [hinner]
          ring
        _ = x * y + Real.log x := by
          ring

-- Proof sketch: unfold the primal-space Fenchel conjugate `(negative_log_barrier∗)`. On the
-- positive ray the barrier contributes `-(-log x) = log x`, while on the nonpositive half-line the
-- term `(x * y : EReal) - ⊤` is `⊥`, so those points do not affect the supremum. Re-express the
-- remaining supremum as the image of `Set.Ioi 0`.
/-- The scalar Fenchel conjugate `(negative_log_barrier∗) y` is the supremum of `x * y + log x`
over the positive ray. -/
theorem negative_log_barrier_conjugate_eq_sSup_Ioi (y : ℝ) :
    (negative_log_barrier∗) y =
      sSup ((fun x : ℝ ↦ ((x * y + Real.log x : ℝ) : EReal)) '' Set.Ioi (0 : ℝ)) := by
  -- Unfold the canonical conjugate and take the supremum of the normalized range formula.
  simpa [conjugate_function_primal_apply, conjugate_function_apply, sSup_insert] using
    congrArg sSup (negativeLogBarrierPairingRange_eq_insertBotImage y)

/-- Helper for Proposition 4.8: when `y < 0`, the candidate point `x0 = -1 / y` lies in
`Set.Ioi 0` and evaluates the logarithmic objective to `-1 - log (-y)`. -/
lemma negativeLogBarrierObjectiveAtCriticalPoint
    (y : ℝ) (hy : y < 0) :
    let x0 := -1 / y
    x0 ∈ Set.Ioi (0 : ℝ) ∧ x0 * y + Real.log x0 = -1 - Real.log (-y) := by
  let x0 : ℝ := -1 / y
  have hx0_pos : 0 < x0 := by
    -- The explicit critical point is positive because both numerator and denominator are negative.
    dsimp [x0]
    exact div_pos_of_neg_of_neg (by norm_num) hy
  have hx0_mul : x0 * y = -1 := by
    -- Multiplying the critical point back by `y` collapses the reciprocal.
    dsimp [x0]
    field_simp [hy.ne]
  have hx0_eq_inv : x0 = (-y)⁻¹ := by
    -- Rewrite the critical point into the inverse form used by `Real.log_inv`.
    calc
      x0 = (-1 : ℝ) / y := by
        rfl
      _ = (-1 : ℝ) * y⁻¹ := by
        rw [div_eq_mul_inv]
      _ = -(y⁻¹) := by
        ring
      _ = (-y)⁻¹ := by
        rw [inv_neg]
  have hx0_log : Real.log x0 = -Real.log (-y) := by
    -- The logarithm evaluates by passing to the inverse of `-y`.
    calc
      Real.log x0 = Real.log ((-y)⁻¹) := by
        rw [hx0_eq_inv]
      _ = -Real.log (-y) := by
        rw [Real.log_inv]
  refine ⟨hx0_pos, ?_⟩
  -- Evaluating the objective at `x0` gives the claimed closed form.
  calc
    x0 * y + Real.log x0 = -1 + -Real.log (-y) := by
      rw [hx0_mul, hx0_log]
    _ = -1 - Real.log (-y) := by
      ring

/-- Helper for Proposition 4.8: when `y < 0`, every positive `x` satisfies
`x * y + log x ≤ -1 - log (-y)`. -/
lemma negativeLogBarrierObjective_le_conjugateValue_of_neg
    (y x : ℝ) (hy : y < 0) (hx : x ∈ Set.Ioi (0 : ℝ)) :
    x * y + Real.log x ≤ -1 - Real.log (-y) := by
  have hyneg : 0 < -y := by
    linarith
  have hmul_pos : 0 < x * (-y) := by
    exact mul_pos hx hyneg
  have hlog :
      Real.log x + Real.log (-y) ≤ -(x * y) - 1 := by
    -- Apply `log u ≤ u - 1` to `u = x * (-y)` and normalize the resulting expression.
    calc
      Real.log x + Real.log (-y) = Real.log (x * (-y)) := by
        rw [← Real.log_mul hx.ne' hyneg.ne']
      _ ≤ x * (-y) - 1 := Real.log_le_sub_one_of_pos hmul_pos
      _ = -(x * y) - 1 := by
        ring
  linarith

/-- Helper for Proposition 4.8: when `y < 0`, the positive-ray image of the logarithmic objective
has greatest element `-1 - log (-y)`. -/
lemma negativeLogBarrierObjectiveEReal_isGreatest_of_neg
    (y : ℝ) (hy : y < 0) :
    IsGreatest
      ((fun x : ℝ ↦ ((x * y + Real.log x : ℝ) : EReal)) '' Set.Ioi (0 : ℝ))
      (((-1 - Real.log (-y) : ℝ) : EReal)) := by
  have hcrit := negativeLogBarrierObjectiveAtCriticalPoint y hy
  dsimp at hcrit
  rcases hcrit with ⟨hx0_mem, hx0_eval⟩
  let x0 : ℝ := -1 / y
  refine ⟨?_, ?_⟩
  · refine ⟨x0, hx0_mem, ?_⟩
    -- The explicit critical point attains the candidate greatest value.
    simpa [x0] using congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hx0_eval
  · intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    -- Every other positive point is bounded above by the same value.
    change (((x * y + Real.log x : ℝ) : EReal) ≤
      (((-1 - Real.log (-y) : ℝ) : EReal)))
    exact_mod_cast negativeLogBarrierObjective_le_conjugateValue_of_neg y x hy hx

/-- Helper for Proposition 4.8: when `0 ≤ y`, the logarithmic objective on `Set.Ioi 0` lies above
every real threshold. -/
lemma negativeLogBarrierObjectiveAboveAnyReal_of_nonneg
    (y : ℝ) (hy0 : 0 ≤ y) :
    ∀ z : ℝ, ∃ x ∈ Set.Ioi (0 : ℝ), z < x * y + Real.log x := by
  intro z
  let x : ℝ := Real.exp (z + 1)
  refine ⟨x, ?_, ?_⟩
  · -- The exponential witness lies on the positive ray.
    dsimp [x]
    exact Real.exp_pos (z + 1)
  · have hxlog : Real.log x = z + 1 := by
      -- The logarithm cancels the exponential witness exactly.
      dsimp [x]
      rw [Real.log_exp]
    have hxy_nonneg : 0 ≤ x * y := by
      have hx_nonneg : 0 ≤ x := le_of_lt (Real.exp_pos (z + 1))
      exact mul_nonneg hx_nonneg hy0
    -- The logarithmic part already exceeds `z`, and the linear part is nonnegative.
    calc
      z < Real.log x := by
        rw [hxlog]
        linarith
      _ ≤ x * y + Real.log x := by
        linarith

-- Proof sketch: use `negative_log_barrier_conjugate_eq_sSup_Ioi`. In the negative branch, the
-- inequality `log u ≤ u - 1` with `u = x * (-y)` gives the global upper bound, and the explicit
-- point `x = -1 / y` attains it. In the nonnegative branch, the witness `x = exp (z + 1)` shows
-- the objective is cofinal in `ℝ`, so the conjugate value is `⊤`.
/-- Proposition 4.8: the scalar Fenchel conjugate `(negative_log_barrier∗) y` equals
`-1 - log (-y)` for `y < 0` and equals `∞` for `y ≥ 0`. -/
theorem negative_log_barrier_conjugate_eq (y : ℝ) :
    (negative_log_barrier∗) y =
      if y < 0 then ((-1 - Real.log (-y) : ℝ) : EReal) else ⊤ := by
  rw [negative_log_barrier_conjugate_eq_sSup_Ioi]
  by_cases hy : y < 0
  · -- In the negative branch, the image set has an explicit greatest element.
    simpa [hy] using (negativeLogBarrierObjectiveEReal_isGreatest_of_neg y hy).csSup_eq
  · have hy0 : 0 ≤ y := by
      linarith
    have hsSup_top :
        sSup ((fun x : ℝ ↦ ((x * y + Real.log x : ℝ) : EReal)) '' Set.Ioi (0 : ℝ)) = ⊤ := by
      rw [sSup_eq_top]
      intro b hb
      -- Reduce the extended-real threshold to a real one, then use the cofinal witness.
      rcases EReal.lt_iff_exists_real_btwn.mp hb with ⟨z, hbz, hzt⟩
      rcases negativeLogBarrierObjectiveAboveAnyReal_of_nonneg y hy0 z with ⟨x, hx, hzx⟩
      refine ⟨((x * y + Real.log x : ℝ) : EReal), ⟨x, hx, rfl⟩, ?_⟩
      exact hbz.trans <| by
        exact_mod_cast hzx
    -- The nonnegative branch is unbounded above, so the conjugate equals `⊤`.
    simpa [hy] using hsSup_top

end
