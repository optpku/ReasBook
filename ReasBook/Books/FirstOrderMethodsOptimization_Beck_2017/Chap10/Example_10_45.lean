/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_23
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Proposition_5_8
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_43
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Example_10_44

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Example 10.45 is `source-facing` in Chapter 10's smoothing API: it introduces the shifted
log-sum-exp smoothing of the coordinatewise maximum on Euclidean `ℝ^n`. The best
`core/canonical` owner for the log-sum-exp part is Chapter 4's
`log_sum_exp_function : (Fin n → ℝ) → EReal`, while Definition 10.43 owns the smooth-approximation
predicate. The public source-facing smoothing is therefore kept as its own owner here, but only as
a thin Euclidean `bridge/view` obtained by scaling and shifting that earlier owner. -/

/-- The shifted log-sum-exp smoothing
`x ↦ μ log (∑ i, exp (x_i / μ)) - μ log n` of the coordinatewise maximum on `ℝ^n`. -/
def shifted_log_sum_exp_smoothing (μ : PosReal) : E → ℝ :=
  fun x ↦
    (μ : ℝ) * (log_sum_exp_function (fun i ↦ x i / (μ : ℝ))).toReal -
      (μ : ℝ) * Real.log (n : ℝ)

/-- Evaluating `shifted_log_sum_exp_smoothing μ` at `x` gives the shifted log-sum-exp formula from
Example 10.45. -/
@[simp] theorem shifted_log_sum_exp_smoothing_apply (μ : PosReal) (x : E) :
    shifted_log_sum_exp_smoothing μ x =
      (μ : ℝ) * Real.log (∑ i : Fin n, Real.exp (x i / (μ : ℝ))) -
        (μ : ℝ) * Real.log (n : ℝ) := by
  simp [shifted_log_sum_exp_smoothing, log_sum_exp_function]

-- Proof sketch: from `0 < n` deduce `1 ≤ (n : ℝ)`, then apply `Real.log_nonneg`.
/-- Helper for Example 10.45: the logarithm of the coordinate count is nonnegative whenever
`n > 0`. -/
lemma log_nat_nonneg_of_pos (hn : 0 < n) : 0 ≤ Real.log (n : ℝ) := by
  -- Cast the cardinality lower bound to `ℝ`, then use monotonicity of `log` on `[1, ∞)`.
  have hnR : 1 ≤ (n : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hn
  exact Real.log_nonneg hnR

/-- The nonnegative parameter `log n` attached to the coordinate count when `n > 0`. -/
def log_cardinality_nonneg (hn : 0 < n) : NNReal :=
  ⟨Real.log (n : ℝ), log_nat_nonneg_of_pos hn⟩

/-- Coercing `log_cardinality_nonneg` to `ℝ` recovers `log n`. -/
@[simp] theorem coe_log_cardinality_nonneg (hn : 0 < n) :
    (log_cardinality_nonneg hn : ℝ) = Real.log (n : ℝ) :=
  rfl

-- Proof sketch: for `n > 1`, cast `1 < n` to `1 < (n : ℝ)` and apply `Real.log_pos`.
/-- Helper for Example 10.45: the logarithm of the coordinate count is positive whenever
`n > 1`. -/
lemma log_nat_pos_of_one_lt (hn : 1 < n) : 0 < Real.log (n : ℝ) := by
  -- After coercing the strict lower bound to `ℝ`, positivity of `log` is immediate.
  have hnR : 1 < (n : ℝ) := by
    exact_mod_cast hn
  exact Real.log_pos hnR

/-- The positive parameter `log n` attached to the coordinate count when `n > 1`. -/
def log_cardinality_posreal (hn : 1 < n) : PosReal :=
  ⟨Real.log (n : ℝ), log_nat_pos_of_one_lt hn⟩

/-- Coercing `log_cardinality_posreal` to `ℝ` recovers `log n`. -/
@[simp] theorem coe_log_cardinality_posreal (hn : 1 < n) :
    ((log_cardinality_posreal hn : PosReal) : ℝ) = Real.log (n : ℝ) :=
  rfl

/-- Helper for Example 10.45: the real-valued log-sum-exp function is convex on all of
`EuclideanSpace ℝ (Fin n)` when `n > 0`. -/
lemma log_sum_exp_function_toReal_convexOn (hn : 0 < n) :
    ConvexOn ℝ Set.univ (fun x : E ↦ (log_sum_exp_function x).toReal) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let f : E → EReal := fun x ↦ negative_entropy_on_stdSimplex n x.ofLp
  have hstar_eq : (f∗) = fun x : E ↦ log_sum_exp_function x.ofLp := by
    funext x
    have htransport :
        conjugate_function f (InnerProductSpace.toDualMap ℝ E x) =
          conjugate_function (negative_entropy_on_stdSimplex n)
            (dotProductEquiv ℝ (Fin n) x.ofLp) := by
      -- Rewrite the Euclidean conjugate through the coordinate model `x.ofLp`.
      rw [conjugate_function_apply, conjugate_function_apply]
      congr 1
      ext a
      constructor
      · rintro ⟨y, rfl⟩
        refine ⟨y.ofLp, ?_⟩
        simp [f]
        refine congrArg
          (fun r : ℝ ↦ ((r : EReal) - negative_entropy_on_stdSimplex n y.ofLp)) ?_
        rw [← WithLp.toLp_ofLp (2 : ENNReal) y]
        simpa [dotProduct_comm] using (EuclideanSpace.inner_toLp_toLp x.ofLp y.ofLp).symm
      · rintro ⟨z, rfl⟩
        refine ⟨WithLp.toLp 2 z, ?_⟩
        rw [WithLp.ofLp_toLp]
        simp [f]
        refine congrArg
          (fun r : ℝ ↦ ((r : EReal) - negative_entropy_on_stdSimplex n z)) ?_
        simpa [dotProduct_comm] using (EuclideanSpace.inner_toLp_toLp x.ofLp z)
    calc
      (f∗) x = conjugate_function f (InnerProductSpace.toDualMap ℝ E x) := by
        rfl
      _ =
          conjugate_function (negative_entropy_on_stdSimplex n)
            (dotProductEquiv ℝ (Fin n) x.ofLp) := htransport
      _ = log_sum_exp_function x.ofLp := by
            simpa [log_sum_exp_function] using
              negative_entropy_on_stdSimplex_conjugate_eq_log_sum_exp x.ofLp
  have hconvex : is_convex_function (f∗) :=
    (conjugate_function_closed_and_convex f).2
  have hne_bot :
      ∀ x ∈ effective_domain (f∗),
        (f∗) x ≠ ⊥ := by
    intro x hx
    -- After rewriting to log-sum-exp, the value is a real cast and cannot be `-∞`.
    rw [hstar_eq]
    simp [log_sum_exp_function]
  have hdomain : effective_domain (f∗) = Set.univ := by
    ext x
    -- The log-sum-exp model is finite everywhere, so its effective domain is all of `E`.
    rw [mem_effective_domain, hstar_eq]
    simp [log_sum_exp_function]
  have hconv_toReal :
      ConvexOn ℝ (effective_domain (f∗)) (fun x : E ↦ (f∗ x).toReal) :=
    convexOn_toReal_of_is_convex_function hconvex hne_bot
  convert hconv_toReal using 1
  · simp [hdomain]
  · ext x
    rw [hstar_eq]

/-- Helper for Example 10.45: the coordinatewise maximum lies between the shifted and unshifted
log-sum-exp expressions. -/
lemma log_sum_exp_max_bounds (hn : 0 < n) (μ : PosReal) (z : Fin n → ℝ) :
    ((μ : ℝ) * Real.log (∑ i : Fin n, Real.exp (z i / (μ : ℝ))) -
        (μ : ℝ) * Real.log (n : ℝ) ≤ coordinatewiseMax z) ∧
      (coordinatewiseMax z ≤
        (μ : ℝ) * Real.log (∑ i : Fin n, Real.exp (z i / (μ : ℝ)))) := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  have hμ_pos : 0 < (μ : ℝ) := PosReal.coe_pos μ
  have hμ_nonneg : 0 ≤ (μ : ℝ) := le_of_lt hμ_pos
  have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt hμ_pos
  obtain ⟨i0, hi0⟩ := Finite.exists_max z
  have hmax_finset :
      coordinatewiseMax z = (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty z := by
    rw [coordinatewiseMax, ← Finset.sup'_univ_eq_ciSup]
  have hmax_eq : coordinatewiseMax z = z i0 := by
    rw [hmax_finset]
    refine le_antisymm ?_ ?_
    · exact
        Finset.sup'_le Finset.univ_nonempty z (fun i hi ↦ hi0 i)
    · exact
        Finset.le_sup' z (Finset.mem_univ i0)
  have hcoord_le : ∀ i : Fin n, z i ≤ coordinatewiseMax z := by
    intro i
    rw [hmax_finset]
    exact
      Finset.le_sup' z (Finset.mem_univ i)
  let g : Fin n → ℝ := fun i ↦ Real.exp (z i / (μ : ℝ))
  have hg_nonneg : ∀ i : Fin n, 0 ≤ g i := by
    intro i
    exact le_of_lt (Real.exp_pos _)
  have hsingle_le_sum : g i0 ≤ ∑ i : Fin n, g i := by
    exact Finset.single_le_sum (fun j _ ↦ hg_nonneg j) (Finset.mem_univ i0)
  have hsum_pos_g : 0 < ∑ i : Fin n, g i := by
    -- A single positive exponential term already forces the full sum to be positive.
    calc
      0 < Real.exp (z i0 / (μ : ℝ)) := Real.exp_pos _
      _ = g i0 := by
            simp [g]
      _ ≤ ∑ i : Fin n, g i := hsingle_le_sum
  have hsum_pos : 0 < ∑ i : Fin n, Real.exp (z i / (μ : ℝ)) := by
    simpa [g] using hsum_pos_g
  have hsum_le :
      ∑ i : Fin n, Real.exp (z i / (μ : ℝ)) ≤
        (n : ℝ) * Real.exp (coordinatewiseMax z / (μ : ℝ)) := by
    -- Bounding each summand by the exponential of the maximal coordinate gives the textbook upper
    -- estimate on the sum.
    calc
      ∑ i : Fin n, Real.exp (z i / (μ : ℝ))
          ≤ ∑ i : Fin n, Real.exp (coordinatewiseMax z / (μ : ℝ)) := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact Real.exp_le_exp.mpr <|
                div_le_div_of_nonneg_right (hcoord_le i) hμ_nonneg
      _ = (n : ℝ) * Real.exp (coordinatewiseMax z / (μ : ℝ)) := by
            simp
  have hterm_le_sum_g :
      g i0 ≤ ∑ i : Fin n, g i := hsingle_le_sum
  have hterm_le_sum :
      Real.exp (coordinatewiseMax z / (μ : ℝ)) ≤
        ∑ i : Fin n, Real.exp (z i / (μ : ℝ)) := by
    -- The maximizing coordinate contributes one term of the exponential sum.
    have hterm_le_sum_g' :
        Real.exp (coordinatewiseMax z / (μ : ℝ)) ≤ ∑ i : Fin n, g i := by
      calc
        Real.exp (coordinatewiseMax z / (μ : ℝ)) = Real.exp (z i0 / (μ : ℝ)) := by
          rw [hmax_eq]
        _ = g i0 := by
          simp [g]
        _ ≤ ∑ i : Fin n, g i := hterm_le_sum_g
    simpa [g] using hterm_le_sum_g'
  constructor
  · -- The full sum is at most `n * exp(max / μ)`, so the shifted log-sum-exp stays below the max.
    have hlog_le :
        Real.log (∑ i : Fin n, Real.exp (z i / (μ : ℝ))) ≤
          Real.log ((n : ℝ) * Real.exp (coordinatewiseMax z / (μ : ℝ))) := by
      exact Real.log_le_log hsum_pos hsum_le
    calc
      (μ : ℝ) * Real.log (∑ i : Fin n, Real.exp (z i / (μ : ℝ))) -
          (μ : ℝ) * Real.log (n : ℝ)
          ≤
            (μ : ℝ) * Real.log ((n : ℝ) * Real.exp (coordinatewiseMax z / (μ : ℝ))) -
              (μ : ℝ) * Real.log (n : ℝ) := by
                gcongr
      _ =
          (μ : ℝ) * (Real.log (n : ℝ) + coordinatewiseMax z / (μ : ℝ)) -
            (μ : ℝ) * Real.log (n : ℝ) := by
              rw [Real.log_mul
                (show (n : ℝ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hn))
                (Real.exp_pos _).ne', Real.log_exp]
      _ = coordinatewiseMax z := by
            field_simp [hμ_ne]
            ring
  · -- The maximizing exponential term is contained in the sum, so the max is below the log-sum-exp.
    have hlog_ge :
        coordinatewiseMax z / (μ : ℝ) ≤
          Real.log (∑ i : Fin n, Real.exp (z i / (μ : ℝ))) := by
      have hlog_term :
          Real.log (Real.exp (coordinatewiseMax z / (μ : ℝ))) ≤
            Real.log (∑ i : Fin n, Real.exp (z i / (μ : ℝ))) := by
        exact Real.log_le_log (Real.exp_pos _) hterm_le_sum
      simpa [Real.log_exp] using hlog_term
    calc
      coordinatewiseMax z = (μ : ℝ) * (coordinatewiseMax z / (μ : ℝ)) := by
        field_simp [hμ_ne]
      _ ≤ (μ : ℝ) * Real.log (∑ i : Fin n, Real.exp (z i / (μ : ℝ))) := by
            gcongr

/-- Helper for Example 10.45: the shifted log-sum-exp smoothing stays below the coordinatewise
maximum and differs from it by at most `μ log n`. -/
lemma shifted_log_sum_exp_smoothing_bounds (hn : 0 < n) (μ : PosReal) (x : E) :
    shifted_log_sum_exp_smoothing μ x ≤ coordinatewiseMax x ∧
      coordinatewiseMax x ≤
        shifted_log_sum_exp_smoothing μ x + (log_cardinality_nonneg hn : ℝ) * (μ : ℝ) := by
  rcases log_sum_exp_max_bounds hn μ x with ⟨hlower, hupper⟩
  constructor
  · -- Expanding the definition turns the first coordinate lemma into the lower approximation bound.
    simpa [shifted_log_sum_exp_smoothing_apply, coe_log_cardinality_nonneg] using hlower
  · -- The upper approximation bound is the same inequality after adding back the shift `μ log n`.
    rw [shifted_log_sum_exp_smoothing_apply, coe_log_cardinality_nonneg]
    linarith

/-- Helper for Example 10.45: scaling the input by `1 / μ` and the output by `μ` transports the
Chapter 5 log-sum-exp smoothness estimate to the exact constant `1 / μ`. -/
lemma shifted_log_sum_exp_smoothing_is_inv_mu_smooth (μ : PosReal) :
    is_l_smooth_on (shifted_log_sum_exp_smoothing μ : E → ℝ) Set.univ (1 / PosReal.toNNReal μ) := by
  let Aμ : E →L[ℝ] E := ((1 / (μ : ℝ)) : ℝ) • ContinuousLinearMap.id ℝ E
  have hpre :
      is_l_smooth_on
        (fun x : E ↦ (log_sum_exp_function (((1 / (μ : ℝ)) • x).ofLp)).toReal)
        Set.univ
        (1 * ‖Aμ‖₊ ^ (2 : ℕ)) := by
    -- Proposition 5.8 gives the base log-sum-exp model, and the dilation contributes `‖Aμ‖²`.
    simpa [Aμ, ContinuousLinearMap.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      Example_10_44.is_l_smooth_on_precompose_continuousLinearMap
        Aμ
        (fun z : E ↦ (log_sum_exp_function z).toReal)
        (log_sum_exp_l2_function_is_one_smooth n)
  have hscaled :
      is_l_smooth_on
        (fun x : E ↦
          (μ : ℝ) * (log_sum_exp_function (((1 / (μ : ℝ)) • x).ofLp)).toReal -
            (μ : ℝ) * Real.log (n : ℝ))
        Set.univ
        (Real.toNNReal (μ : ℝ) * (1 * ‖Aμ‖₊ ^ (2 : ℕ))) := by
    -- Multiplying by `μ` rescales the smoothness constant once, and subtracting `μ log n`
    -- leaves the derivative Lipschitz bound unchanged.
    exact Example_10_44.is_l_smooth_on_const_mul_sub_const
      (μ : ℝ)
      ((μ : ℝ) * Real.log (n : ℝ))
      (le_of_lt (PosReal.coe_pos μ))
      hpre
  have hAμ_norm_le : ‖Aμ‖ ≤ (μ : ℝ)⁻¹ := by
    -- The dilation `x ↦ x / μ` has operator norm at most `1 / μ`.
    calc
      ‖Aμ‖ = ‖(1 / (μ : ℝ))‖ * ‖ContinuousLinearMap.id ℝ E‖ := by
            change ‖((1 / (μ : ℝ)) • ContinuousLinearMap.id ℝ E)‖ =
              ‖(1 / (μ : ℝ))‖ * ‖ContinuousLinearMap.id ℝ E‖
            rw [norm_smul]
      _ ≤ (μ : ℝ)⁻¹ * 1 := by
            rw [Real.norm_of_nonneg (le_of_lt (one_div_pos.mpr (PosReal.coe_pos μ)))]
            have hid_le : ‖(ContinuousLinearMap.id ℝ E : E →L[ℝ] E)‖ ≤ 1 :=
              (ContinuousLinearMap.norm_id_le :
                ‖(ContinuousLinearMap.id ℝ E : E →L[ℝ] E)‖ ≤ 1)
            calc
              (1 / (μ : ℝ)) * ‖(ContinuousLinearMap.id ℝ E : E →L[ℝ] E)‖ ≤
                  (1 / (μ : ℝ)) * 1 := by
                    exact
                      mul_le_mul_of_nonneg_left
                        hid_le
                        (le_of_lt (one_div_pos.mpr (PosReal.coe_pos μ)))
              _ = (μ : ℝ)⁻¹ * 1 := by ring
      _ = (μ : ℝ)⁻¹ := by simp
  have hconst_le :
      Real.toNNReal (μ : ℝ) * ‖Aμ‖₊ ^ (2 : ℕ) ≤
        (1 : NNReal) / PosReal.toNNReal μ := by
    -- The transported constant is bounded above by the target textbook constant `1 / μ`.
    have hbound_real :
        (((Real.toNNReal (μ : ℝ) * ‖Aμ‖₊ ^ (2 : ℕ) : NNReal) : ℝ)) ≤
          ((((1 : NNReal) / PosReal.toNNReal μ : NNReal) : ℝ)) := by
      have hμ_nonneg : 0 ≤ (μ : ℝ) := le_of_lt (PosReal.coe_pos μ)
      have hAμ_sq_le : ‖Aμ‖ ^ (2 : ℕ) ≤ ((μ : ℝ)⁻¹) ^ (2 : ℕ) := by
        nlinarith [hAμ_norm_le, norm_nonneg Aμ]
      have hμ_ne : (μ : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos μ)
      calc
        (((Real.toNNReal (μ : ℝ) * ‖Aμ‖₊ ^ (2 : ℕ) : NNReal) : ℝ))
            = (Real.toNNReal (μ : ℝ) : ℝ) * (((‖Aμ‖₊ ^ (2 : ℕ) : NNReal) : ℝ)) := by
                rw [NNReal.coe_mul]
        _ = (μ : ℝ) * ‖Aμ‖ ^ (2 : ℕ) := by
              rw [Real.toNNReal_of_nonneg hμ_nonneg, NNReal.coe_pow]
              change (μ : ℝ) * ((‖Aμ‖₊ : NNReal) : ℝ) ^ (2 : ℕ) = (μ : ℝ) * ‖Aμ‖ ^ (2 : ℕ)
              rfl
        _ ≤ (μ : ℝ) * ((μ : ℝ)⁻¹) ^ (2 : ℕ) := by
              gcongr
        _ = (μ : ℝ)⁻¹ := by
              field_simp [hμ_ne]
        _ = ((((1 : NNReal) / PosReal.toNNReal μ : NNReal) : ℝ)) := by
              simp [PosReal.coe_toNNReal, div_eq_mul_inv]
    exact_mod_cast hbound_real
  have hsmooth :
      is_l_smooth_on
        (fun x : E ↦
          (μ : ℝ) * (log_sum_exp_function (((1 / (μ : ℝ)) • x).ofLp)).toReal -
            (μ : ℝ) * Real.log (n : ℝ))
        Set.univ
        ((1 : NNReal) / PosReal.toNNReal μ) :=
    Example_10_44.is_l_smooth_on_mono hscaled (by simpa [one_mul] using hconst_le)
  have hfun :
      shifted_log_sum_exp_smoothing μ =
        (fun x : E ↦
          (μ : ℝ) * (log_sum_exp_function (((1 / (μ : ℝ)) • x).ofLp)).toReal -
            (μ : ℝ) * Real.log (n : ℝ)) := by
    funext x
    -- Route correction: rewrite the source formula through the scaled identity map
    -- instead of normalizing `fderiv` across coordinate coercions.
    have harg :
        (fun i : Fin n ↦ x i / (μ : ℝ)) = (((1 / (μ : ℝ)) • x).ofLp) := by
      ext i
      simp [div_eq_mul_inv, mul_comm]
    simp [shifted_log_sum_exp_smoothing, harg]
  simpa [hfun] using hsmooth

-- Proof sketch: the lower and upper approximation bounds are the standard log-sum-exp estimates
-- for the maximum. For smoothness, rewrite
-- `shifted_log_sum_exp_smoothing μ x = μ * log (∑ i, exp (x_i / μ)) - μ log n`
-- and transport Proposition 5.8 along the scaling map `x ↦ x / μ`; the additive constant
-- `- μ log n` does not affect the derivative Lipschitz bound.
/-- Example 10.45: for `n > 0`, the shifted log-sum-exp function gives a `1 / μ`-smooth
approximation of the coordinatewise maximum on `ℝ^n` with nonnegative error parameter `log n`. -/
theorem coordinatewise_max_shifted_log_sum_exp_is_smooth_approximation_nonneg
    (hn : 0 < n) (μ : PosReal) :
    IsSmoothApproximationNonneg
      (fun x : E ↦ coordinatewiseMax x)
      (shifted_log_sum_exp_smoothing μ : E → ℝ)
      1
      (log_cardinality_nonneg hn)
      μ := by
  have hpreconv :
      ConvexOn ℝ Set.univ
        (fun x : E ↦ (log_sum_exp_function (((1 / (μ : ℝ)) • x).ofLp)).toReal) := by
    -- Route correction: transport convexity through the scaling affine map instead of building a
    -- bespoke Euclidean conjugacy bridge.
    simpa [Function.comp, LinearMap.coe_toAffineMap, DistribSMul.toLinearMap_apply] using
      (log_sum_exp_function_toReal_convexOn hn).comp_affineMap
        (DistribSMul.toLinearMap ℝ E ((1 / (μ : ℝ)) : ℝ)).toAffineMap
  have hfun :
      shifted_log_sum_exp_smoothing μ =
        (fun x : E ↦
          (μ : ℝ) * (log_sum_exp_function (((1 / (μ : ℝ)) • x).ofLp)).toReal -
            (μ : ℝ) * Real.log (n : ℝ)) := by
    funext x
    -- Match the source formula with the scaled coordinate presentation used by `hpreconv`.
    have harg :
        (fun i : Fin n ↦ x i / (μ : ℝ)) = (((1 / (μ : ℝ)) • x).ofLp) := by
      ext i
      simp [div_eq_mul_inv, mul_comm]
    simp [shifted_log_sum_exp_smoothing, harg]
  have hconv :
      ConvexOn ℝ Set.univ (shifted_log_sum_exp_smoothing μ : E → ℝ) := by
    -- Positive scaling preserves convexity, and the final shift is an additive constant.
    simpa [hfun, sub_eq_add_neg] using
      (hpreconv.smul (le_of_lt (PosReal.coe_pos μ))).add_const
        (-(μ : ℝ) * Real.log (n : ℝ))
  refine ⟨hconv, ?_, ?_, ?_⟩
  · intro x
    -- The lower approximation inequality is exactly the first pointwise bound.
    exact (shifted_log_sum_exp_smoothing_bounds hn μ x).1
  · intro x
    -- The upper approximation inequality is exactly the second pointwise bound.
    exact (shifted_log_sum_exp_smoothing_bounds hn μ x).2
  · -- Smoothness comes from the scaled Chapter 5 log-sum-exp model.
    simpa using shifted_log_sum_exp_smoothing_is_inv_mu_smooth μ

-- Proof sketch: start from the nonnegative-parameter approximation theorem above. When `n > 1`,
-- `log n` is positive, so the error constant upgrades to the positive parameter
-- `log_cardinality_posreal hn`.
/-- When `n > 1`, the shifted log-sum-exp smoothing fits the chapter owner
`IsSmoothApproximation` with parameters `(1, log n)`. -/
theorem coordinatewise_max_shifted_log_sum_exp_is_smooth_approximation
    (hn : 1 < n) (μ : PosReal) :
    IsSmoothApproximation
      (fun x : E ↦ coordinatewiseMax x)
      (shifted_log_sum_exp_smoothing μ : E → ℝ)
      1 (log_cardinality_posreal hn) μ := by
  -- The only change from the nonnegative formulation is upgrading the error parameter from
  -- `NNReal` to `PosReal`.
  simpa [IsSmoothApproximation, log_cardinality_nonneg, log_cardinality_posreal] using
    (coordinatewise_max_shifted_log_sum_exp_is_smooth_approximation_nonneg
      (Nat.lt_trans Nat.zero_lt_one hn) μ)

-- Proof sketch: combine convexity of `fun x : E ↦ coordinatewiseMax x` with the preceding
-- explicit approximation theorem for each positive `μ`. The latter supplies the required witness
-- function
-- `shifted_log_sum_exp_smoothing μ`.
/-- Under the chapter's strictly positive error-parameter convention, the coordinatewise maximum on
`ℝ^n` is `(1, log n)`-smoothable whenever `n > 1`. -/
theorem coordinatewise_max_is_one_log_cardinality_smoothable (hn : 1 < n) :
    is_smoothable
      (fun x : E ↦ coordinatewiseMax x)
      1 (log_cardinality_posreal hn) := by
  -- For each positive smoothing parameter, choose the shifted log-sum-exp witness from the
  -- preceding approximation theorem.
  intro μ
  refine ⟨shifted_log_sum_exp_smoothing μ, ?_⟩
  exact coordinatewise_max_shifted_log_sum_exp_is_smooth_approximation hn μ

end
