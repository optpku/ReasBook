/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped BigOperators

/- Proposition 4.17 is a `source-facing` conjugacy computation for the concrete log-sum-exp
function on `ℝ^n`. The chapter `core/canonical` owner declaration for the entropy-valued
right-hand side is already `negative_entropy_on_stdSimplex` from Proposition 4.16, built on the
Fenchel conjugate owner `conjugate_function` from Definition 4.1. This file therefore states the
conjugate formula directly using that named entropy object rather than restating its coordinate
definition inline. -/

section

variable {n : ℕ}

local notation "E" => Fin n → ℝ

/-- The log-sum-exp function `x ↦ log (∑ j, exp (x_j))` on `ℝ^n`, regarded as an
`EReal`-valued function so that its Fenchel conjugate is expressed by `conjugate_function`. -/
def log_sum_exp_function : E → EReal :=
  fun x ↦ ((Real.log (∑ j : Fin n, Real.exp (x j)) : ℝ) : EReal)

-- Proof sketch: unfold `log_sum_exp_function`; the statement is exactly its defining coordinate
-- formula cast from `ℝ` to `EReal`.
/-- Evaluating `log_sum_exp_function` at `x` gives `log (∑ j, exp (x_j))`, viewed in `EReal`. -/
@[simp] theorem log_sum_exp_function_apply (x : E) :
    log_sum_exp_function x = ((Real.log (∑ j : Fin n, Real.exp (x j)) : ℝ) : EReal) :=
  rfl

variable [NeZero n]

/-- Helper for Proposition 4.17: `negative_entropy_on_stdSimplex n` is proper because it never
takes the value `⊥` and is finite at the softmax point of the zero vector. -/
private theorem negativeEntropyOnStdSimplex_isProper :
    IsProperExtendedRealFunction (negative_entropy_on_stdSimplex n) := by
  refine ⟨?_, ?_⟩
  · -- The entropy extension only takes finite values on the simplex and `⊤` off it.
    intro x
    by_cases hx : x ∈ stdSimplex ℝ (Fin n)
    · rw [negative_entropy_on_stdSimplex_of_mem (n := n) hx]
      exact EReal.coe_ne_bot _
    · rw [negative_entropy_on_stdSimplex_of_not_mem (n := n) hx]
      exact top_ne_bot
  · -- The softmax point of the zero vector belongs to the simplex, so the value is finite there.
    refine ⟨softmax_point (fun _ : Fin n ↦ 0), ?_⟩
    simpa [effective_domain] using
      (show negative_entropy_on_stdSimplex n (softmax_point (fun _ : Fin n ↦ 0)) < ⊤ by
        rw [negative_entropy_on_stdSimplex_of_mem (n := n)
          (softmax_point_mem_stdSimplex (fun _ ↦ 0))]
        exact EReal.coe_lt_top _)

/-- Helper for Proposition 4.17: on simplex points, every affine-minus-log-sum-exp value is
bounded above by the entropy sum `∑ i, y i * log (y i)`. -/
private theorem logSumExpObjective_le_negativeEntropy_of_memStdSimplex
    {y x : E} (hy : y ∈ stdSimplex ℝ (Fin n)) :
    (((dotProductEquiv ℝ (Fin n) y x : ℝ) : EReal) - log_sum_exp_function x) ≤
      ((∑ i, y i * Real.log (y i) : ℝ) : EReal) := by
  -- Apply Fenchel's inequality to the conjugate pair from Proposition 4.16.
  have hFenchel :
      (((dotProductEquiv ℝ (Fin n) y x : ℝ) : EReal)) ≤
        negative_entropy_on_stdSimplex n y +
          conjugate_function (negative_entropy_on_stdSimplex n) (dotProductEquiv ℝ (Fin n) x) := by
    simpa [add_comm, add_left_comm, add_assoc, dotProductEquiv, dotProduct, mul_comm] using
      (fenchel_inequality (negative_entropy_on_stdSimplex n) y
        (dotProductEquiv ℝ (Fin n) x) negativeEntropyOnStdSimplex_isProper)
  rw [negative_entropy_on_stdSimplex_of_mem hy,
    negative_entropy_on_stdSimplex_conjugate_eq_log_sum_exp] at hFenchel
  have hpair :
      (dotProductEquiv ℝ (Fin n) y x : ℝ) ≤
        (∑ i, y i * Real.log (y i)) + Real.log (∑ j : Fin n, Real.exp (x j)) := by
    exact_mod_cast hFenchel
  have hreal :
      (dotProductEquiv ℝ (Fin n) y x : ℝ) - Real.log (∑ j : Fin n, Real.exp (x j)) ≤
        ∑ i, y i * Real.log (y i) := by
    linarith
  -- Convert the real inequality back to the `EReal`-valued conjugate integrand.
  rw [log_sum_exp_function_apply, ← EReal.coe_sub]
  exact_mod_cast hreal

/-- Helper for Proposition 4.17: a constant vector `x_i = c` has log-sum-exp value
`c + log n`. -/
private theorem logSumExpOnConstVector (c : ℝ) :
    log_sum_exp_function (fun _ : Fin n ↦ c) = ((c + Real.log (n : ℝ) : ℝ) : EReal) := by
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hsum :
      ∑ j : Fin n, Real.exp ((fun _ : Fin n ↦ c) j) = (n : ℝ) * Real.exp c := by
    simp
  -- Rewrite the finite sum of equal exponentials as a product and simplify the logarithm.
  rw [log_sum_exp_function_apply, hsum, Real.log_mul (show (n : ℝ) ≠ 0 by exact_mod_cast NeZero.ne n)
    (Real.exp_ne_zero c), Real.log_exp]
  ring

/-- Helper for Proposition 4.17: the conjugate objective on a constant vector reduces to the
linear slope `c * (∑ i, y i - 1)` minus the offset `log n`. -/
private theorem constantVectorObjective_value
    (y : E) (c : ℝ) :
    (((dotProductEquiv ℝ (Fin n) y) (fun _ : Fin n ↦ c) : ℝ) : EReal) -
        log_sum_exp_function (fun _ : Fin n ↦ c) =
      (((c * (∑ i, y i - 1) - Real.log (n : ℝ) : ℝ)) : EReal) := by
  have hdot :
      ((dotProductEquiv ℝ (Fin n) y) (fun _ : Fin n ↦ c) : ℝ) = c * ∑ i, y i := by
    -- Expand the dot product and factor out the constant coordinate value.
    calc
      ((dotProductEquiv ℝ (Fin n) y) (fun _ : Fin n ↦ c) : ℝ)
          = dotProduct y (fun _ : Fin n ↦ c) := by
              simp [dotProductEquiv]
      _ = ∑ i, y i * c := by
            simp [dotProduct]
      _ = (∑ i, y i) * c := by
            rw [Finset.sum_mul]
      _ = c * ∑ i, y i := by
            ring
  -- Normalize both finite `EReal` terms to the same real arithmetic expression.
  rw [logSumExpOnConstVector]
  change (((((dotProductEquiv ℝ (Fin n) y) (fun _ : Fin n ↦ c) : ℝ) - (c + Real.log (n : ℝ)) :
      ℝ) : EReal) =
    (((c * (∑ i, y i - 1) - Real.log (n : ℝ) : ℝ)) : EReal))
  exact_mod_cast by
    rw [hdot]
    ring

/-- Helper for Proposition 4.17: every strict lower real bound below the entropy value on the
simplex is exceeded by an explicit logarithmic witness. -/
private theorem existsLogSumExpWitness_gt_of_ltEntropy_onStdSimplex
    {y : E} (hy : y ∈ stdSimplex ℝ (Fin n)) {r : ℝ}
    (hr : r < ∑ i, y i * Real.log (y i)) :
    ∃ x : E, (r : EReal) < (((dotProductEquiv ℝ (Fin n) y x : ℝ) : EReal) - log_sum_exp_function x) := by
  let entropy : ℝ := ∑ i, y i * Real.log (y i)
  let gap : ℝ := entropy - r
  have hgap : 0 < gap := by
    dsimp [gap, entropy]
    linarith
  let ε : ℝ := gap / (2 * (n : ℝ))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    positivity
  let x : E := fun i ↦ if y i = 0 then Real.log ε else Real.log (y i)
  have hdot :
      (dotProductEquiv ℝ (Fin n) y x : ℝ) = entropy := by
    -- Zero coordinates contribute nothing, while positive coordinates contribute `y i * log (y i)`.
    calc
      (dotProductEquiv ℝ (Fin n) y x : ℝ) = dotProduct y x := by
        simp [dotProductEquiv]
      _ = ∑ i, y i * x i := by
        simp [dotProduct]
      _ = ∑ i, y i * Real.log (y i) := by
        refine Finset.sum_congr rfl ?_
        intro i _
        by_cases hyi : y i = 0
        · simp [x, hyi]
        · simp [x, hyi]
      _ = entropy := rfl
  have hsumexp_pos : 0 < ∑ i : Fin n, Real.exp (x i) := by
    let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
    refine lt_of_lt_of_le (Real.exp_pos (x i0)) ?_
    exact Finset.single_le_sum (fun i _ ↦ le_of_lt (Real.exp_pos (x i))) (by simp)
  have hsumexp_le : ∑ i : Fin n, Real.exp (x i) ≤ 1 + (n : ℝ) * ε := by
    -- Each exponential term is bounded by the corresponding simplex weight plus the uniform slack `ε`.
    calc
      ∑ i : Fin n, Real.exp (x i) ≤ ∑ i : Fin n, (y i + ε) := by
        refine Finset.sum_le_sum ?_
        intro i _
        by_cases hyi : y i = 0
        · simp [x, hyi, Real.exp_log hε_pos]
        · have hyi_pos : 0 < y i := lt_of_le_of_ne (hy.1 i) (Ne.symm hyi)
          have hterm : Real.exp (x i) = y i := by
            simp [x, hyi, Real.exp_log hyi_pos]
          rw [hterm]
          linarith
      _ = (∑ i : Fin n, y i) + ∑ _ : Fin n, ε := by
        rw [Finset.sum_add_distrib]
      _ = 1 + (n : ℝ) * ε := by
        simp [hy.2]
  have hs_lt_gap : (n : ℝ) * ε < gap := by
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    have hs_eq : (n : ℝ) * ε = gap / 2 := by
      dsimp [ε]
      field_simp [hn_pos.ne']
    rw [hs_eq]
    linarith
  have hlog_le : Real.log (∑ i : Fin n, Real.exp (x i)) ≤ (n : ℝ) * ε := by
    calc
      Real.log (∑ i : Fin n, Real.exp (x i)) ≤ Real.log (1 + (n : ℝ) * ε) := by
        exact Real.log_le_log hsumexp_pos hsumexp_le
      _ ≤ (n : ℝ) * ε := by
        have hpos : 0 < 1 + (n : ℝ) * ε := by positivity
        simpa using Real.log_le_sub_one_of_pos hpos
  have hreal :
      r < (dotProductEquiv ℝ (Fin n) y x : ℝ) - Real.log (∑ i : Fin n, Real.exp (x i)) := by
    -- The entropy gap dominates the logarithmic normalization slack.
    rw [hdot]
    dsimp [gap, entropy] at hgap ⊢
    linarith
  refine ⟨x, ?_⟩
  -- Repackage the real objective estimate as an `EReal` inequality in the conjugate range.
  rw [log_sum_exp_function_apply, ← EReal.coe_sub]
  exact_mod_cast hreal

/-- Helper for Proposition 4.17: outside the simplex, the defining supremum for the conjugate of
`log_sum_exp_function` is unbounded above, so the conjugate value is `⊤`. -/
private theorem logSumExpConjugate_eq_top_of_notMemStdSimplex
    {y : E} (hy : y ∉ stdSimplex ℝ (Fin n)) :
    conjugate_function log_sum_exp_function (dotProductEquiv ℝ (Fin n) y) = ⊤ := by
  rw [conjugate_function_apply, EReal.eq_top_iff_forall_lt]
  intro b
  by_cases hsum : ∑ i, y i = 1
  · have hneg : ∃ j : Fin n, y j < 0 := by
      by_contra hneg
      apply hy
      refine ⟨?_, hsum⟩
      intro i
      exact le_of_not_gt (fun hi ↦ hneg ⟨i, hi⟩)
    rcases hneg with ⟨j, hyj⟩
    let gap : ℝ := -y j
    have hgap : 0 < gap := by
      dsimp [gap]
      linarith
    obtain ⟨m, hm⟩ := exists_nat_gt ((b + Real.log (n : ℝ)) / gap)
    have hb_lt : b < (m : ℝ) * gap - Real.log (n : ℝ) := by
      have hm' : (b + Real.log (n : ℝ)) / gap < (m : ℝ) := by
        exact_mod_cast hm
      have hscaled : b + Real.log (n : ℝ) < (m : ℝ) * gap := by
        exact (div_lt_iff₀ hgap).1 hm'
      linarith
    let x : E := Pi.single j (-(m : ℝ))
    have hdot :
        (dotProductEquiv ℝ (Fin n) y x : ℝ) = (m : ℝ) * gap := by
      -- Only the negative coordinate contributes on the single-coordinate ray.
      calc
        (dotProductEquiv ℝ (Fin n) y x : ℝ) = dotProduct y x := by
          simp [dotProductEquiv]
        _ = ∑ i : Fin n, y i * x i := by
              simp [dotProduct]
        _ = y j * (-(m : ℝ)) := by
              rw [Finset.sum_eq_single j]
              · simp [x]
              · intro i _ hij
                simp [x, hij]
              · intro hj
                exact (hj (Finset.mem_univ j)).elim
        _ = (m : ℝ) * gap := by
              dsimp [gap]
              ring
    have hsumexp_pos : 0 < ∑ i : Fin n, Real.exp (x i) := by
      let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
      refine lt_of_lt_of_le (Real.exp_pos (x i0)) ?_
      exact Finset.single_le_sum (fun i _ ↦ le_of_lt (Real.exp_pos (x i))) (by simp)
    have hsumexp_le : ∑ i : Fin n, Real.exp (x i) ≤ (n : ℝ) := by
      -- Every coordinate of the chosen ray is nonpositive, so each exponential is at most `1`.
      calc
        ∑ i : Fin n, Real.exp (x i) ≤ ∑ i : Fin n, (1 : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro i _
          by_cases hij : i = j
          · have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
            have hnonpos : x i ≤ 0 := by
              simp [x, hij, hm_nonneg]
            exact by
              simpa using (Real.exp_le_exp.mpr hnonpos)
          · simp [x, hij]
        _ = (n : ℝ) := by simp
    have hlog_le : Real.log (∑ i : Fin n, Real.exp (x i)) ≤ Real.log (n : ℝ) := by
      exact Real.log_le_log hsumexp_pos hsumexp_le
    have hreal :
        b < (dotProductEquiv ℝ (Fin n) y x : ℝ) - Real.log (∑ i : Fin n, Real.exp (x i)) := by
      rw [hdot]
      linarith
    have hterm_lt :
        (b : EReal) <
          (((dotProductEquiv ℝ (Fin n) y x : ℝ) : EReal) - log_sum_exp_function x) := by
      rw [log_sum_exp_function_apply, ← EReal.coe_sub]
      exact_mod_cast hreal
    exact lt_of_lt_of_le hterm_lt (le_sSup (Set.mem_range.mpr ⟨x, rfl⟩))
  · have hsum_lt_or_gt : ∑ i, y i < 1 ∨ 1 < ∑ i, y i := by
      exact lt_or_gt_of_ne hsum
    rcases hsum_lt_or_gt with hsum_lt | hsum_gt
    · let gap : ℝ := 1 - ∑ i, y i
      have hgap : 0 < gap := by
        dsimp [gap]
        linarith
      obtain ⟨m, hm⟩ := exists_nat_gt ((b + Real.log (n : ℝ)) / gap)
      have hb_lt : b < (m : ℝ) * gap - Real.log (n : ℝ) := by
        have hm' : (b + Real.log (n : ℝ)) / gap < (m : ℝ) := by
          exact_mod_cast hm
        have hscaled : b + Real.log (n : ℝ) < (m : ℝ) * gap := by
          exact (div_lt_iff₀ hgap).1 hm'
        linarith
      let x : E := fun _ ↦ -(m : ℝ)
      have hvalue :
          (((dotProductEquiv ℝ (Fin n) y x : ℝ) : EReal) - log_sum_exp_function x) =
            (((m : ℝ) * gap - Real.log (n : ℝ) : ℝ) : EReal) := by
        calc
          (((dotProductEquiv ℝ (Fin n) y x : ℝ) : EReal) - log_sum_exp_function x)
              = (((-(m : ℝ)) * (∑ i, y i - 1) - Real.log (n : ℝ) : ℝ) : EReal) := by
                  simpa [x] using constantVectorObjective_value (n := n) y (-(m : ℝ))
          _ = (((m : ℝ) * gap - Real.log (n : ℝ) : ℝ) : EReal) := by
                congr 1
                dsimp [gap]
                ring
      refine lt_of_lt_of_le ?_ (le_sSup (Set.mem_range.mpr ⟨x, rfl⟩))
      calc
        (b : EReal) < (((m : ℝ) * gap - Real.log (n : ℝ) : ℝ) : EReal) := by
              exact_mod_cast hb_lt
        _ = (((dotProductEquiv ℝ (Fin n) y x : ℝ) : EReal) - log_sum_exp_function x) := by
              simpa using hvalue.symm
    · let gap : ℝ := ∑ i, y i - 1
      have hgap : 0 < gap := by
        dsimp [gap]
        linarith
      obtain ⟨m, hm⟩ := exists_nat_gt ((b + Real.log (n : ℝ)) / gap)
      have hb_lt : b < (m : ℝ) * gap - Real.log (n : ℝ) := by
        have hm' : (b + Real.log (n : ℝ)) / gap < (m : ℝ) := by
          exact_mod_cast hm
        have hscaled : b + Real.log (n : ℝ) < (m : ℝ) * gap := by
          exact (div_lt_iff₀ hgap).1 hm'
        linarith
      let x : E := fun _ ↦ (m : ℝ)
      have hvalue :
          (((dotProductEquiv ℝ (Fin n) y x : ℝ) : EReal) - log_sum_exp_function x) =
            (((m : ℝ) * gap - Real.log (n : ℝ) : ℝ) : EReal) := by
        calc
          (((dotProductEquiv ℝ (Fin n) y x : ℝ) : EReal) - log_sum_exp_function x)
              = (((m : ℝ) * (∑ i, y i - 1) - Real.log (n : ℝ) : ℝ) : EReal) := by
                  simpa [x] using constantVectorObjective_value (n := n) y (m : ℝ)
          _ = (((m : ℝ) * gap - Real.log (n : ℝ) : ℝ) : EReal) := by
                dsimp [gap]
      refine lt_of_lt_of_le ?_ (le_sSup (Set.mem_range.mpr ⟨x, rfl⟩))
      calc
        (b : EReal) < (((m : ℝ) * gap - Real.log (n : ℝ) : ℝ) : EReal) := by
              exact_mod_cast hb_lt
        _ = (((dotProductEquiv ℝ (Fin n) y x : ℝ) : EReal) - log_sum_exp_function x) := by
              simpa using hvalue.symm

-- Proof sketch: if `y ∉ stdSimplex ℝ (Fin n)`, either `∑ i, y i ≠ 1` or some coordinate is
-- negative; in each case a one-parameter family of test points makes the affine term minus
-- `log_sum_exp_function` diverge to `∞`. If `y ∈ stdSimplex ℝ (Fin n)`, rewrite the objective
-- using the softmax probabilities `p_i(x) = exp (x_i) / ∑ j, exp (x_j)`, reduce the supremum to
-- `sup_{p ∈ Δ_n} ∑ i, y_i log p_i`, and maximize it at `p = y` via Gibbs' inequality, using
-- `Real.log 0 = 0` for the convention `0 log 0 = 0`.
/-- Proposition 4.17: the Fenchel conjugate of the log-sum-exp function on `ℝ^n`, evaluated via
the Euclidean pairing `dotProductEquiv`, is the simplex-constrained negative entropy
`negative_entropy_on_stdSimplex n`. Equivalently, this is the entropy expression
`∑ i, y_i log y_i` on the standard simplex `Δ_n = stdSimplex ℝ (Fin n)` and `∞` outside the
simplex. -/
theorem log_sum_exp_function_conjugate :
    (fun y : E ↦ conjugate_function log_sum_exp_function (dotProductEquiv ℝ (Fin n) y)) =
      negative_entropy_on_stdSimplex n := by
  funext y
  by_cases hy : y ∈ stdSimplex ℝ (Fin n)
  · -- On the simplex, identify the supremum with the entropy value using upper and lower witnesses.
    rw [conjugate_function_apply, negative_entropy_on_stdSimplex_of_mem hy]
    refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
    · rintro a ⟨x, rfl⟩
      exact logSumExpObjective_le_negativeEntropy_of_memStdSimplex (n := n) (y := y) (x := x) hy
    · intro w hw
      obtain ⟨r, hwr, hrw⟩ := EReal.exists_between_coe_real hw
      have hr :
          r < ∑ i, y i * Real.log (y i) := by
        exact_mod_cast hrw
      rcases existsLogSumExpWitness_gt_of_ltEntropy_onStdSimplex (n := n) (y := y) hy hr with
        ⟨x, hx⟩
      refine ⟨_, Set.mem_range.mpr ⟨x, rfl⟩, ?_⟩
      exact hwr.trans hx
  · -- Outside the simplex, the conjugate is unbounded above by the textbook ray arguments.
    rw [negative_entropy_on_stdSimplex_of_not_mem hy]
    exact logSumExpConjugate_eq_top_of_notMemStdSimplex (n := n) hy

/-- Pointwise form of Proposition 4.17. -/
theorem log_sum_exp_function_conjugate_eq (y : E) :
    conjugate_function log_sum_exp_function (dotProductEquiv ℝ (Fin n) y) =
      negative_entropy_on_stdSimplex n y := by
  simpa using congrArg (fun f : E → EReal ↦ f y) log_sum_exp_function_conjugate

/-- On `stdSimplex ℝ (Fin n)`, the conjugate of `log_sum_exp_function` is the entropy sum
`∑ i, y i * log (y i)`. -/
@[simp] theorem log_sum_exp_function_conjugate_of_mem
    {y : E} (hy : y ∈ stdSimplex ℝ (Fin n)) :
    conjugate_function log_sum_exp_function (dotProductEquiv ℝ (Fin n) y) =
      ((∑ i, y i * Real.log (y i) : ℝ) : EReal) := by
  rw [log_sum_exp_function_conjugate_eq]
  simpa using negative_entropy_on_stdSimplex_of_mem hy

/-- Outside `stdSimplex ℝ (Fin n)`, the conjugate of `log_sum_exp_function` is `∞`. -/
@[simp] theorem log_sum_exp_function_conjugate_of_not_mem
    {y : E} (hy : y ∉ stdSimplex ℝ (Fin n)) :
    conjugate_function log_sum_exp_function (dotProductEquiv ℝ (Fin n) y) = ⊤ := by
  rw [log_sum_exp_function_conjugate_eq]
  simpa using negative_entropy_on_stdSimplex_of_not_mem hy

end
