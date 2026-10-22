/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap11.Algorithm_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_5
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_6
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_7
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_5
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_6

set_option relaxedAutoImplicit true

noncomputable section

universe v

open Metric
open scoped Gradient

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, CompleteSpace (Ei i)] [∀ i, ProperSpace (Ei i)]
variable [Nonempty (Fin p)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}

/- Theorem 11.7 is `source-facing`: it gives the convex CBPG objective-gap rate. The owner
abstractions already live upstream:
- `CyclicBlockProximalGradientConvexAssumptions` is the Chapter 11 source-facing problem owner;
- `cyclic_block_proximal_gradient_method` is the owner of the CBPG outer iterates;
- `cbpg_quadratic_gap_constant` is the canonical Chapter 11 coefficient
  `L_min / (2 p (L_f + L_max)^2 R_α^2)`;
- `nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence` and
  `nonnegative_sequence_le_epsilon_of_quadratic_step_recurrence` are the scalar recurrence owners
  from Lemma 11.7.

Primitive data are therefore only the convex CBPG assumptions and the canonical initial datum
`x0 ∈ effective_domain (separableSum g)`. The objective gap is derived API, and the passage from
the CBPG step estimate to the scalar recurrence is a `bridge/view`, not a second wrapper owner. -/

section

variable
  (hconvex : CyclicBlockProximalGradientConvexAssumptions
    f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

local notation "hproblem" =>
  hconvex.toBlockProximalGradientAssumptions
local notation "x0I" =>
  hconvex.interior_effective_domain_point x0

set_option quotPrecheck false in
local notation "x[" k "]" =>
  cyclic_block_proximal_gradient_method hproblem x0I k
set_option quotPrecheck false in
local notation "x[" k "," i "]" =>
  cyclic_block_proximal_gradient_inner_iterate hproblem x[k] i
local notation "F" =>
  composite_model_objective f (separableSum g)
local notation "toPiLp" =>
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
set_option quotPrecheck false in
local notation "x₂[" k "]" => toPiLp x[k]
local notation "XStar₂" => toPiLp '' XStar
set_option quotPrecheck false in
local notation "Δ[" k "]" => (F x[k]).toReal - FOpt
set_option quotPrecheck false in
local notation "RadiusBound" =>
  fun Rα : PosReal ↦
    ∀ ⦃x⦄,
      F x ≤ F x[0] →
      infDist (toPiLp x) XStar₂ ≤ Rα
set_option quotPrecheck false in
local notation "GapBound[" Rα "," k "]" =>
  max
    (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) * Δ[0])
    (4 / (cbpg_quadratic_gap_constant Lf Li Rα * ((k - 1 : ℕ) : ℝ)))
set_option quotPrecheck false in
local notation "IterationThreshold[" Rα "," ε "]" =>
  max
      ((2 / Real.log 2) *
        (Real.log (Δ[0]) + Real.log (1 / (ε : ℝ))))
      (4 / (cbpg_quadratic_gap_constant Lf Li Rα * (ε : ℝ))) +
    1

-- Match the singleton-coordinate owner in Lemma 11.5 definitionally.
local instance theorem11_7_decidableEqFin : DecidableEq (Fin p) := Classical.decEq _

/-- Helper for Theorem 11.7: every auxiliary iterate `x^{k,m}` with `m ≤ p` remains in the
effective domain of the block-separable regularizer. -/
lemma cbpg_inner_stage_mem_effective_domain
    (k : ℕ) (m : ℕ) (hm : m ≤ p) :
    x[k, m] ∈ effective_domain (separableSum g) := by
  -- Reuse the owner-level CBPG domain propagation from Lemma 11.4.
  simpa using cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k m hm

/-- Helper for Theorem 11.7: every outer CBPG iterate remains in the effective domain of the
block-separable regularizer. -/
lemma cbpg_outer_iterate_mem_effective_domain
    (k : ℕ) :
    x[k] ∈ effective_domain (separableSum g) := by
  -- The outer iterate is the zeroth inner stage in the owner recursion.
  simpa using cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k 0 (Nat.zero_le p)

/-- Helper for Theorem 11.7: every CBPG objective value along the outer sequence is finite. -/
lemma cbpg_outer_objective_value_finite
    (k : ℕ) :
    F x[k] ≠ ⊤ ∧ F x[k] ≠ ⊥ := by
  -- This is exactly the finiteness interface already proved for CBPG outer iterates.
  simpa using cbpg_objective_value_finite hproblem x0 k

/-- Helper for Theorem 11.7: the quadratic CBPG gap coefficient is positive for every positive
radius parameter. -/
lemma cbpg_quadratic_gap_constant_pos
    (Rα : PosReal) :
    0 < cbpg_quadratic_gap_constant Lf Li Rα := by
  obtain ⟨i⟩ := ‹Nonempty (Fin p)›
  -- The denominator is the positive product from the textbook coefficient.
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i.1) i.2)
  have hLf_nonneg : 0 ≤ (Lf : ℝ) := by
    exact_mod_cast Lf.2
  have hmax_pos : 0 < ((cbpg_max_block_stepsize Li : PosReal) : ℝ) :=
    PosReal.coe_pos (cbpg_max_block_stepsize Li)
  have hsum_pos :
      0 < (Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ) :=
    add_pos_of_nonneg_of_pos hLf_nonneg hmax_pos
  have hsum_sq_pos :
      0 <
        (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) := by
    positivity
  have hR_sq_pos : 0 < ((Rα : ℝ) ^ (2 : ℕ)) := by
    have hR_pos : 0 < (Rα : ℝ) := PosReal.coe_pos Rα
    nlinarith [sq_pos_of_pos hR_pos]
  have hdenom_pos :
      0 <
        2 * (p : ℝ) *
          (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) *
          ((Rα : ℝ) ^ (2 : ℕ)) := by
    have hfront_pos : 0 < 2 * (p : ℝ) := by
      positivity
    have hleft_pos :
        0 <
          2 * (p : ℝ) *
            (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) :=
      mul_pos hfront_pos hsum_sq_pos
    exact mul_pos hleft_pos hR_sq_pos
  -- The numerator is the positive owner `L_min`.
  rw [cbpg_quadratic_gap_constant_def]
  exact div_pos (PosReal.coe_pos (cbpg_min_block_stepsize Li)) hdenom_pos

include hconvex x0

/-- Helper for Theorem 11.7: every CBPG objective value along the outer sequence is finite from
above. -/
lemma cbpg_objective_value_ne_top
    (k : ℕ) :
    F x[k] ≠ ⊤ :=
  (cbpg_outer_objective_value_finite (hconvex := hconvex) (x0 := x0) k).1

/-- Helper for Theorem 11.7: every CBPG objective value along the outer sequence is finite from
below. -/
lemma cbpg_objective_value_ne_bot
    (k : ℕ) :
    F x[k] ≠ ⊥ :=
  (cbpg_outer_objective_value_finite (hconvex := hconvex) (x0 := x0) k).2

/-- Helper for Theorem 11.7: the CBPG objective gap sequence is nonnegative. -/
lemma cbpg_objective_gap_nonneg
    (k : ℕ) :
    0 ≤ Δ[k] := by
  have hlower : (FOpt : EReal) ≤ F x[k] :=
    (hproblem).optimal_value_isGLB.1 ⟨x[k], rfl⟩
  have hreal : FOpt ≤ (F x[k]).toReal :=
    EReal.toReal_le_toReal
      hlower
      (by simp)
      (cbpg_objective_value_ne_top (hconvex := hconvex) (x0 := x0) k)
  -- The real-valued gap is the finite objective value minus the optimal lower bound.
  exact sub_nonneg.mpr hreal

/-- Helper for Theorem 11.7: once the two consecutive objective values are known to be finite,
their EReal difference is the coercion of the corresponding real difference. -/
lemma cbpg_objective_step_decrease_real_form
    (k : ℕ) :
    F x[k] - F x[k + 1] =
      ((((F x[k]).toReal - (F x[k + 1]).toReal : ℝ)) : EReal) := by
  have hk_val : F x[k] = ((((F x[k]).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal
        (cbpg_objective_value_ne_top (hconvex := hconvex) (x0 := x0) k)
        (cbpg_objective_value_ne_bot (hconvex := hconvex) (x0 := x0) k)).symm
  have hk1_val : F x[k + 1] = ((((F x[k + 1]).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal
        (cbpg_objective_value_ne_top (hconvex := hconvex) (x0 := x0) (k + 1))
        (cbpg_objective_value_ne_bot (hconvex := hconvex) (x0 := x0) (k + 1))).symm
  -- After rewriting both finite values as real coercions, subtraction is purely real.
  rw [hk_val, hk1_val, EReal.coe_sub]
  simp

/-- Helper for Theorem 11.7: subtracting two consecutive gaps cancels the common optimal-value
offset and leaves the real difference of the corresponding objective values. -/
lemma cbpg_objective_gap_difference_eq_toReal_difference
    (k : ℕ) :
    Δ[k] - Δ[k + 1] =
      (F x[k]).toReal - (F x[k + 1]).toReal := by
  -- Expanding both gaps shows the common `FOpt` terms cancel.
  ring

/-- Helper for Theorem 11.7: every optimizer in `XStar` attains the optimal objective value
`FOpt`. -/
lemma cbpg_objective_eq_optimal_value_of_mem_optimal_set
    {xStar : (i : Fin p) → Ei i}
    (hxStar : xStar ∈ XStar) :
    F xStar = (FOpt : EReal) := by
  -- Route correction: normalize optimizer values directly through the owner optimal-set
  -- characterization instead of rebuilding this identity inside the one-step recurrence proof.
  apply le_antisymm
  · exact (hproblem).optimal_value_isGLB.2 <| by
      rintro _ ⟨y, rfl⟩
      have hxOpt : xStar ∈ unconstrained_problem_solutions F := by
        rw [← (hproblem).optimal_set_eq]
        exact hxStar
      exact (mem_unconstrained_problem_solutions_iff_forall_le.mp hxOpt) y
  · exact (hproblem).optimal_value_isGLB.1 ⟨xStar, rfl⟩

/-- Helper for Theorem 11.7: every optimizer has finite separable penalty value, hence belongs to
the effective domain of `separableSum g`. -/
lemma cbpg_mem_effective_domain_of_mem_optimal_set
    {xStar : (i : Fin p) → Ei i}
    (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain (separableSum g) := by
  have hFxStar :
      F xStar = (FOpt : EReal) :=
    cbpg_objective_eq_optimal_value_of_mem_optimal_set
      (hconvex := hconvex)
      (x0 := x0)
      hxStar
  have hg_ne_top :
      separableSum g xStar ≠ ⊤ := by
    -- If the separable penalty were `⊤`, then the composite objective would also be `⊤`,
    -- contradicting the finite optimizer value.
    intro hg_top
    have htop : F xStar = ⊤ := by
      calc
        F xStar = f xStar + separableSum g xStar := by
          rw [composite_model_objective_apply]
        _ = f xStar + ⊤ := by rw [hg_top]
        _ = ⊤ := EReal.add_top_of_ne_bot ((hproblem).toIsBlockProximalGradientProblem.f_ne_bot xStar)
    rw [htop] at hFxStar
    exact EReal.coe_ne_top FOpt hFxStar.symm
  -- The optimizer value is finite from above, so it lies in the effective domain of `∑ g_i`.
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_ne_top)

/-- Helper for Theorem 11.7: the `PiLp` sufficient-decrease estimate from Lemma 11.4 also implies
the raw ambient one-step decrease bound required by Lemma 11.6. -/
lemma cbpg_step_decrease_bound
    (k : ℕ) :
    cbpgStepDecreaseBound Li
      (fun z : PiLp 2 Ei ↦ F z)
      (fun m ↦ x₂[m]) k := by
  -- Lemma 11.4 already states sufficient decrease in the canonical Euclidean product norm.
  simpa using cbpg_sufficient_decrease_outer_step hproblem x0 k

/-- Helper for Theorem 11.7: the final residual tuple at outer step `k`, formed by transporting
the stagewise prox residuals to the final point `x^{k+1}`. -/
abbrev cbpg_final_residual
    (k : ℕ) : (i : Fin p) → Ei i :=
  fun j ↦
    block_gradient j x[k + 1] - block_gradient j x[k, j.1] +
      G[Li j; (hproblem).toIsBlockProximalGradientProblem] x[k, j.1] j

/-- Helper for Theorem 11.7: at every feasible point, the composite objective equals the
coercion of the real sum of the smooth term and the blockwise penalty values. -/
lemma cbpg_objective_eq_real_sum_of_mem_effective_domain
    {xPoint : (i : Fin p) → Ei i}
    (hxPoint : xPoint ∈ effective_domain (separableSum g)) :
    F xPoint =
      ((((f xPoint).toReal + (∑ j, (g j (xPoint j)).toReal) : ℝ)) : EReal) := by
  have hxf :
      xPoint ∈ effective_domain f := by
    -- Feasibility for the block-separable penalty places the point in the effective domain of `f`.
    exact
      interior_subset
        (IsBlockProximalGradientProblem.mem_interior_effective_domain_of_mem_g_effective_domain
          (hproblem).toIsBlockProximalGradientProblem hxPoint)
  have hfx_val :
      f xPoint = ((((f xPoint).toReal : ℝ)) : EReal) := by
    -- The smooth term is finite on that effective domain, so it can be rewritten through `toReal`.
    exact
      (EReal.coe_toReal
        (mem_effective_domain.mp hxf).ne
        ((hproblem).toIsBlockProximalGradientProblem.f_ne_bot xPoint)).symm
  -- Normalize the separable term through the Chapter 11 finite-value sum formula.
  rw [composite_model_objective_apply, hfx_val,
    IsBlockProximalGradientProblem.separableSumEqCoeToRealSum
      (hproblem).toIsBlockProximalGradientProblem
      hxPoint]
  simp [EReal.coe_add]

/-- Helper for Theorem 11.7: once block `j` is updated during the `k`-th cycle, later block
updates leave the `j`-th coordinate unchanged until the outer successor `x^{k+1}`. -/
lemma cbpg_stage_updated_coordinate_eq_later_stage
    (k : ℕ) (j : Fin p) {m : ℕ}
    (hj : j.1 + 1 ≤ m) (hm : m ≤ p) :
    x[k, m] j = x[k, j.1 + 1] j := by
  have hsuffix :
      ∀ r : ℕ, j.1 + 1 + r ≤ p →
        x[k, j.1 + 1 + r] j = x[k, j.1 + 1] j := by
    intro r hr
    induction r with
    | zero =>
        simp
    | succ r ihr =>
        have hstage_lt : j.1 + 1 + r < p := Nat.lt_of_succ_le hr
        let jr : Fin p := ⟨j.1 + 1 + r, hstage_lt⟩
        have hsucc :
            x[k, j.1 + 1 + r + 1] =
              block_coordinate_update
                x[k, j.1 + 1 + r]
                jr
                ((hproblem).toIsBlockProximalGradientProblem.prox_point
                    (Li jr) jr x[k, j.1 + 1 + r] -
                  x[k, j.1 + 1 + r] jr) := by
          -- The next auxiliary stage updates only the currently active block `jr`.
          simpa [jr, block_coordinate_update] using
            cyclic_block_proximal_gradient_method_inner_succ hproblem x0I k hstage_lt
        have hne : j ≠ jr := by
          intro hEq
          have hval : j.1 = j.1 + 1 + r := by
            simpa [jr] using congrArg Fin.val hEq
          omega
        calc
          x[k, j.1 + 1 + (r + 1)] j =
              block_coordinate_update
                x[k, j.1 + 1 + r]
                jr
                ((hproblem).toIsBlockProximalGradientProblem.prox_point
                    (Li jr) jr x[k, j.1 + 1 + r] -
                  x[k, j.1 + 1 + r] jr) j := by
            have hcoord := congrArg (fun z : (i : Fin p) → Ei i ↦ z j) hsucc
            simpa [Nat.add_assoc] using hcoord
          _ = x[k, j.1 + 1 + r] j := by
            simp [block_coordinate_update_apply_ne, hne]
          _ = x[k, j.1 + 1] j := by
            exact ihr (Nat.le_of_succ_le hr)
  let r : ℕ := m - (j.1 + 1)
  have hr : j.1 + 1 + r = m := by
    dsimp [r]
    exact Nat.add_sub_of_le hj
  -- Reindex the later stage `m` as the updated stage plus a suffix length.
  simpa [r, hr] using hsuffix r (by simpa [hr] using hm)

/-- Helper for Theorem 11.7: after block `j` is updated, its value persists to the full outer
successor `x^{k+1}`. -/
lemma cbpg_stage_updated_coordinate_eq_outer_successor
    (k : ℕ) (j : Fin p) :
    x[k, j.1 + 1] j = x[k + 1] j := by
  have hstable :
      x[k, p] j = x[k, j.1 + 1] j :=
    cbpg_stage_updated_coordinate_eq_later_stage
      (hconvex := hconvex)
      (x0 := x0)
      (k := k)
      (j := j)
      (m := p)
      (Nat.succ_le_of_lt j.2)
      (Nat.le_refl p)
  -- The outer successor is the terminal auxiliary stage.
  calc
    x[k, j.1 + 1] j = x[k, p] j := by
      exact hstable.symm
    _ = x[k + 1] j := by
      rw [cyclic_block_proximal_gradient_method_succ]

/-- Helper for Theorem 11.7: the final residual coordinate splits into the stage residual plus the
smooth-gradient drift from the stage point to the outer successor. -/
lemma cbpg_final_residual_coordinate_eq_stage_residual_plus_drift
    (k : ℕ) (j : Fin p) :
    cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j =
      G[Li j; (hproblem).toIsBlockProximalGradientProblem] x[k, j.1] j +
        (block_gradient j x[k + 1] - block_gradient j x[k, j.1]) := by
  -- Expand the residual definition and regroup the stage term with the smooth-gradient drift.
  dsimp [cbpg_final_residual]
  abel

/-- Helper for Theorem 11.7: the suffix displacement from the stage point `x^{k,j}` to the outer
successor is coordinatewise dominated by the full outer-step displacement. -/
lemma cbpg_suffix_displacement_norm_le_outer_step_norm
    (k : ℕ) (j : Fin p) :
    ‖x[k, j.1] - x[k + 1]‖ ≤ ‖x[k] - x[k + 1]‖ := by
  suffices hnn : ‖x[k, j.1] - x[k + 1]‖₊ ≤ ‖x[k] - x[k + 1]‖₊ by
    exact_mod_cast hnn
  rw [Pi.nnnorm_def, Pi.nnnorm_def]
  refine Finset.sup_le ?_
  intro i hi
  by_cases hij : i.1 < j.1
  · have hstage_eq :
        x[k, j.1] i = x[k, i.1 + 1] i :=
      cbpg_stage_updated_coordinate_eq_later_stage
        (hconvex := hconvex)
        (x0 := x0)
        (k := k)
        (j := i)
        (m := j.1)
        (Nat.succ_le_of_lt hij)
        (Nat.le_of_lt j.2)
    have houter_eq :
        x[k, i.1 + 1] i = x[k + 1] i :=
      cbpg_stage_updated_coordinate_eq_outer_successor
        (hconvex := hconvex)
        (x0 := x0)
        k
        i
    -- Earlier coordinates have already stabilized to the outer successor, so the suffix vector
    -- vanishes there.
    simp [hstage_eq, houter_eq]
  · have hstage_eq :
        x[k, j.1] i = x[k] i := by
      exact
        cbpg_auxiliary_iterate_apply_eq_outer_iterate
          hproblem
          x0
          k
          j.1
          i
          (le_of_not_gt hij)
    -- Later coordinates still agree with `x^k`, so the suffix displacement is exactly the
    -- corresponding outer-step coordinate.
    simpa [hstage_eq] using
      (Finset.le_sup (s := (Finset.univ : Finset (Fin p)))
        (f := fun i ↦ ‖(x[k] - x[k + 1]) i‖₊) (Finset.mem_univ i))

/-- On a finite family, the canonical Euclidean product norm is at most `√p` times the raw
product sup norm. -/
lemma toPiLp_norm_le_sqrt_card_mul_raw_norm
    (v : (i : Fin p) → Ei i) :
    ‖toPiLp v‖ ≤ Real.sqrt p * ‖v‖ := by
  have hcoord :
      ∀ i : Fin p, ‖v i‖ ^ (2 : ℕ) ≤ ‖v‖ ^ (2 : ℕ) := by
    intro i
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm v i) 2
  have hsum :
      (∑ i : Fin p, ‖v i‖ ^ (2 : ℕ)) ≤
        ∑ _i : Fin p, ‖v‖ ^ (2 : ℕ) :=
    Finset.sum_le_sum fun i _ ↦ hcoord i
  have hsq :
      ‖toPiLp v‖ ^ (2 : ℕ) ≤ (p : ℝ) * ‖v‖ ^ (2 : ℕ) := by
    rw [PiLp.norm_sq_eq_of_L2]
    simpa [Finset.card_univ] using hsum
  have hsqrt_sq : (Real.sqrt (p : ℝ)) ^ (2 : ℕ) = (p : ℝ) := by
    exact Real.sq_sqrt (Nat.cast_nonneg p)
  have hrhs_nonneg : 0 ≤ Real.sqrt (p : ℝ) * ‖v‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [hsq, hsqrt_sq, norm_nonneg (toPiLp v)]

/-- The same suffix-displacement comparison in the canonical `PiLp 2` norm used by the
Chapter 11 smoothness owner. -/
lemma cbpg_suffix_displacement_toPiLp_norm_le_outer_step
    (k : ℕ) (j : Fin p) :
    ‖toPiLp x[k, j.1] - toPiLp x[k + 1]‖ ≤
      ‖toPiLp x[k] - toPiLp x[k + 1]‖ := by
  have hsq :
      ‖toPiLp x[k, j.1] - toPiLp x[k + 1]‖ ^ (2 : ℕ) ≤
        ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) := by
    rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_le_sum ?_
    intro i hi
    by_cases hij : i.1 < j.1
    · have hstage_eq :
          x[k, j.1] i = x[k, i.1 + 1] i :=
        cbpg_stage_updated_coordinate_eq_later_stage
          (hconvex := hconvex)
          (x0 := x0)
          (k := k)
          (j := i)
          (m := j.1)
          (Nat.succ_le_of_lt hij)
          (Nat.le_of_lt j.2)
      have houter_eq :
          x[k, i.1 + 1] i = x[k + 1] i :=
        cbpg_stage_updated_coordinate_eq_outer_successor
          (hconvex := hconvex)
          (x0 := x0)
          k
          i
      simp [hstage_eq, houter_eq]
    · have hstage_eq :
          x[k, j.1] i = x[k] i :=
        cbpg_auxiliary_iterate_apply_eq_outer_iterate
          hproblem
          x0
          k
          j.1
          i
          (le_of_not_gt hij)
      simp [hstage_eq]
  nlinarith [hsq,
    norm_nonneg (toPiLp x[k, j.1] - toPiLp x[k + 1]),
    norm_nonneg (toPiLp x[k] - toPiLp x[k + 1])]

/-- Helper for Theorem 11.7: each final residual coordinate is bounded by the full outer-step norm
with the exact textbook coefficient `L_f + L_max`. -/
lemma cbpg_final_residual_coordinate_norm_le_lf_plus_lmax_mul_outer_step
    (k : ℕ) (j : Fin p) :
    ‖cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j‖ ≤
      ((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) * ‖x₂[k] - x₂[k + 1]‖ := by
  have hxkp1_g :
      x[k + 1] ∈ effective_domain (separableSum g) :=
    cbpg_outer_iterate_mem_effective_domain
      (hconvex := hconvex)
      (x0 := x0)
      (k + 1)
  have hxkp1_int :
      x[k + 1] ∈ interior (effective_domain f) :=
    IsBlockProximalGradientProblem.mem_interior_effective_domain_of_mem_g_effective_domain
      (hproblem).toIsBlockProximalGradientProblem hxkp1_g
  have hxstage_g :
      x[k, j.1] ∈ effective_domain (separableSum g) :=
    cbpg_inner_stage_mem_effective_domain
      (hconvex := hconvex)
      (x0 := x0)
      k
      j.1
      (Nat.le_of_lt j.2)
  have hxstage_int :
      x[k, j.1] ∈ interior (effective_domain f) :=
    IsBlockProximalGradientProblem.mem_interior_effective_domain_of_mem_g_effective_domain
      (hproblem).toIsBlockProximalGradientProblem hxstage_g
  have hdrift_base :
      ‖block_gradient j x[k + 1] - block_gradient j x[k, j.1]‖ ≤
        (Lf : ℝ) *
          ‖ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei) x[k + 1] -
            ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
              x[k, j.1]‖ :=
    cbpg_block_gradient_difference_le_lf_mul_toPiLp_norm
      hproblem
      j
      x[k + 1]
      x[k, j.1]
      hxkp1_int
      hxstage_int
  have hdrift :
      ‖block_gradient j x[k + 1] - block_gradient j x[k, j.1]‖ ≤
        (Lf : ℝ) * ‖x₂[k] - x₂[k + 1]‖ := by
    have hsuffix :=
      cbpg_suffix_displacement_toPiLp_norm_le_outer_step
        (hconvex := hconvex)
        (x0 := x0)
        k
        j
    have hLf_nonneg : 0 ≤ (Lf : ℝ) := by
      exact_mod_cast Lf.2
    have hsuffix' :
        ‖ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei) x[k + 1] -
            ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
              x[k, j.1]‖ ≤
          ‖ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei) x[k] -
            ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
              x[k + 1]‖ := by
      simpa [norm_sub_rev] using hsuffix
    exact hdrift_base.trans <| mul_le_mul_of_nonneg_left hsuffix' hLf_nonneg
  have hbefore_eq :
      x[k, j.1] j = x[k] j := by
    exact
      cbpg_auxiliary_iterate_apply_eq_outer_iterate
        hproblem
        x0
        k
        j.1
        j
        (le_rfl)
  have hafter_eq :
      x[k, j.1 + 1] j = x[k + 1] j :=
    cbpg_stage_updated_coordinate_eq_outer_successor
      (hconvex := hconvex)
      (x0 := x0)
      k
      j
  have hsucc :
      x[k, j.1 + 1] =
        block_coordinate_update
          x[k, j.1]
          j
          ((hproblem).toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] -
            x[k, j.1] j) := by
    -- The active block update is exactly the canonical prox step at stage `j`.
    simpa [block_coordinate_update] using
      cyclic_block_proximal_gradient_method_inner_succ hproblem x0I k j.2
  have hprox :
      (hproblem).toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] =
        x[k, j.1 + 1] j := by
    have hcoord := congrArg (fun z : (i : Fin p) → Ei i ↦ z j) hsucc
    simpa [block_coordinate_update] using hcoord.symm
  have hstage_coord :
      G[Li j; (hproblem).toIsBlockProximalGradientProblem] x[k, j.1] j =
        (Li j : ℝ) • (x[k] j - x[k + 1] j) := by
    -- Route correction: rewrite the stage residual directly as the updated-block difference in
    -- outer coordinates, instead of hiding this identity inside the final square-sum proof.
    calc
      G[Li j; (hproblem).toIsBlockProximalGradientProblem] x[k, j.1] j =
          (Li j : ℝ) •
            (x[k, j.1] j -
              (hproblem).toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1]) := by
        simpa using
          (hproblem).toIsBlockProximalGradientProblem.gradient_mapping_def
            (Li j) x[k, j.1] j
      _ = (Li j : ℝ) • (x[k, j.1] j - x[k, j.1 + 1] j) := by
        rw [hprox]
      _ = (Li j : ℝ) • (x[k] j - x[k + 1] j) := by
        rw [hbefore_eq, hafter_eq]
  have hLj_le_max :
      (Li j : ℝ) ≤ ((cbpg_max_block_stepsize Li : PosReal) : ℝ) := by
    rw [cbpg_max_block_stepsize_def]
    exact Finset.le_sup' (s := (Finset.univ : Finset (Fin p))) (f := Li) (Finset.mem_univ j)
  have hstage :
      ‖G[Li j; (hproblem).toIsBlockProximalGradientProblem] x[k, j.1] j‖ ≤
        ((cbpg_max_block_stepsize Li : PosReal) : ℝ) * ‖x₂[k] - x₂[k + 1]‖ := by
    calc
      ‖G[Li j; (hproblem).toIsBlockProximalGradientProblem] x[k, j.1] j‖ =
          (Li j : ℝ) * ‖x[k] j - x[k + 1] j‖ := by
        rw [hstage_coord, norm_smul, Real.norm_of_nonneg (le_of_lt (Li j).2)]
      _ ≤ (Li j : ℝ) * ‖x₂[k] - x₂[k + 1]‖ := by
        exact mul_le_mul_of_nonneg_left
          (by simpa using PiLp.norm_apply_le (x₂[k] - x₂[k + 1]) j)
          (le_of_lt (PosReal.coe_pos (Li j)))
      _ ≤ ((cbpg_max_block_stepsize Li : PosReal) : ℝ) * ‖x₂[k] - x₂[k + 1]‖ := by
        gcongr
  -- Combine the stage residual estimate with the smooth-gradient drift estimate.
  calc
    ‖cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j‖ ≤
        ‖G[Li j; (hproblem).toIsBlockProximalGradientProblem] x[k, j.1] j‖ +
          ‖block_gradient j x[k + 1] - block_gradient j x[k, j.1]‖ := by
      rw [cbpg_final_residual_coordinate_eq_stage_residual_plus_drift
        (hconvex := hconvex) (x0 := x0) k j]
      exact norm_add_le _ _
    _ ≤
        ((cbpg_max_block_stepsize Li : PosReal) : ℝ) * ‖x₂[k] - x₂[k + 1]‖ +
          (Lf : ℝ) * ‖x₂[k] - x₂[k + 1]‖ := by
      exact add_le_add hstage hdrift
    _ =
        ((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) *
          ‖x₂[k] - x₂[k + 1]‖ := by
      ring

/-- Helper for Theorem 11.7: the stagewise prox optimality condition yields a public one-block
subgradient certificate for the final residual coordinate at `x^{k+1}`. -/
lemma cbpg_final_residual_coordinate_mem_euclideanSubdifferential
    (k : ℕ) (j : Fin p) :
    cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
        block_gradient j x[k + 1] ∈
      euclideanSubdifferential (g j) (x[k + 1] j) := by
  let M : PosReal := Li j
  let xStage : (i : Fin p) → Ei i := x[k, j.1]
  let xNext : Ei j := x[k, j.1 + 1] j
  have hxNext :
      xNext = (hproblem).toIsBlockProximalGradientProblem.prox_point M j xStage := by
    have hsucc :
        x[k, j.1 + 1] =
          block_coordinate_update
            xStage
            j
            ((hproblem).toIsBlockProximalGradientProblem.prox_point M j xStage - xStage j) := by
      -- The active-block auxiliary successor is exactly the owner one-block prox update.
      simpa [xStage, M, block_coordinate_update] using
        cyclic_block_proximal_gradient_method_inner_succ hproblem x0I k j.2
    -- Reading the active coordinate of that block update recovers the prox point itself.
    simpa [xNext, xStage, M, block_coordinate_update] using congrArg (fun z ↦ z j) hsucc
  have hprox_eq :
      prox[((((1 / M : PosReal) : EReal) • g j))]
          (xStage j - (1 / M : ℝ) • block_gradient j xStage) = {xNext} := by
    -- The one-block prox owner packages the updated block value as a singleton prox set.
    rw [hxNext]
    exact (hproblem).toIsBlockProximalGradientProblem.prox_point_eq_singleton M j xStage
  have hscaled :=
    scaled_function_proper_closed_convex_of_pos
      (g j)
      ((hproblem).block_g_proper j)
      ((hproblem).block_g_closed j)
      ((hproblem).block_g_convex j)
      (1 / M)
  have hprox_sub :
      InnerProductSpace.toDualMap ℝ (Ei j)
          ((xStage j - (1 / M : ℝ) • block_gradient j xStage) - xNext) ∈
        strongDualSubdifferential ((((1 / M : PosReal) : EReal) • g j)) xNext := by
    -- Convert the prox singleton description into the standard owner subgradient certificate.
    exact
      (prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
        ((((1 / M : PosReal) : EReal) • g j))
        hscaled.1
        hscaled.2.2
        (xStage j - (1 / M : ℝ) • block_gradient j xStage)
        xNext).mp hprox_eq
  have hscaled_sub :
      (InnerProductSpace.toDualMap ℝ (Ei j)
          (G[M; (hproblem).toIsBlockProximalGradientProblem] xStage j - block_gradient j xStage) :
            Module.Dual ℝ (Ei j)) ∈
        subdifferential (g j) xNext := by
    have hM0 : (M : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos M)
    let v : Ei j :=
      G[M; (hproblem).toIsBlockProximalGradientProblem] xStage j -
        block_gradient j xStage
    have hvec :
        (xStage j - (1 / M : ℝ) • block_gradient j xStage) - xNext =
          (1 / M : ℝ) • v := by
      dsimp [v]
      rw [hxNext]
      simp [smul_sub, smul_smul, one_div, hM0, sub_eq_add_neg]
      abel
    have hsub_scaled :
        (InnerProductSpace.toDualMap ℝ (Ei j) ((1 / M : ℝ) • v) :
            Module.Dual ℝ (Ei j)) ∈
          subdifferential ((((1 / M : PosReal) : EReal) • g j)) xNext := by
      rw [mem_strongDualSubdifferential] at hprox_sub
      rw [← hvec]
      exact hprox_sub
    have htransport :=
      (mem_subdifferential_pos_real_mul_iff
        (g j)
        (1 / M : ℝ)
        (one_div_pos.mpr (PosReal.coe_pos M))
        xNext
        (InnerProductSpace.toDualMap ℝ (Ei j) ((1 / M : ℝ) • v))).mp hsub_scaled
    simpa [v, smul_smul, one_div, hM0, inv_mul_cancel₀] using htransport
  have hstage_mem :
      G[M; (hproblem).toIsBlockProximalGradientProblem] xStage j - block_gradient j xStage ∈
        euclideanSubdifferential (g j) xNext := by
    -- Pass from the owner dual subgradient to the Euclidean/vector-side subgradient.
    rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential]
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hscaled_sub
  have hresidual_eq :
      cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j - block_gradient j x[k + 1] =
        G[M; (hproblem).toIsBlockProximalGradientProblem] xStage j - block_gradient j xStage := by
    -- After subtracting the final smooth gradient, only the stagewise prox residual remains.
    dsimp [cbpg_final_residual, M, xStage]
    abel
  have hpoint :
      xNext = x[k + 1] j := by
    -- The updated coordinate persists until the end of the full outer cycle.
    simpa [xNext] using
      cbpg_stage_updated_coordinate_eq_outer_successor
        (hconvex := hconvex)
        (x0 := x0)
        k
        j
  -- Rewrite both the base point and the residual vector into the final-iterate formulation.
  simpa [hresidual_eq, hpoint] using hstage_mem

/-- Helper for Theorem 11.7: the CBPG outer objective values form an antitone sequence. -/
lemma cbpg_objective_values_antitone :
    Antitone (fun k ↦ F x[k]) := by
  -- The one-step monotonicity theorem from Theorem 11.5 upgrades to the full outer sequence.
  exact antitone_nat_of_succ_le fun k ↦
    cbpg_objective_step_monotone hproblem x0 k

/-- The ambient Fréchet derivative decomposes into the finite sum of the prescribed block
gradient pairings.  This formulation avoids requiring an inner-product instance on the raw
function type; the Euclidean geometry remains owned by the block spaces and `PiLp 2`. -/
lemma cbpg_fderiv_apply_eq_sum_block_pairings
    {xPoint d : (i : Fin p) → Ei i}
    (hxPoint : xPoint ∈ interior (effective_domain f)) :
    (fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) xPoint) d =
      ∑ i, inner ℝ (block_gradient i xPoint) (d i) := by
  have hcoord :
      ∀ j : Fin p,
        (fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) xPoint)
            (Pi.single j (d j)) =
          inner ℝ (block_gradient j xPoint) (d j) := by
    intro j
    have hcomp := fderiv_comp_single_eq_block_toDual hproblem j xPoint hxPoint
    have happly := congrArg (fun A : Ei j →L[ℝ] ℝ ↦ A (d j)) hcomp
    simpa [ContinuousLinearMap.comp_apply, InnerProductSpace.toDualMap_apply_apply] using happly
  have hsplit : d = ∑ i, Pi.single i (d i) := by
    ext i
    rw [Finset.sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hij : i ≠ j := by
        intro hijEq
        exact hji hijEq.symm
      simp [Pi.single_eq_of_ne hij]
    · simp
  calc
    (fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) xPoint) d =
        (fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) xPoint)
          (∑ i, Pi.single i (d i)) := by
      exact congrArg
        (fun z : (i : Fin p) → Ei i ↦
          (fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) xPoint) z)
        hsplit
    _ = ∑ i,
          (fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) xPoint)
            (Pi.single i (d i)) := by rw [map_sum]
    _ = ∑ i, inner ℝ (block_gradient i xPoint) (d i) := by
      exact Finset.sum_congr rfl fun i _ ↦ hcoord i

/-- Convexity of the smooth term bounds its block-gradient support sum at any interior point. -/
lemma cbpg_convex_support_sum_at_point
    {xPoint xStar : (i : Fin p) → Ei i}
    (hxPoint : xPoint ∈ interior (effective_domain f))
    (hxStar : xStar ∈ effective_domain f) :
    ∑ i, inner ℝ (block_gradient i xPoint) (xStar i - xPoint i) ≤
      (f xStar).toReal - (f xPoint).toReal := by
  have hdiffAt :
      DifferentiableAt ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) xPoint := by
    exact
      ((hproblem).f_toReal_differentiableOn_interior_effective_domain xPoint hxPoint).differentiableAt
        (isOpen_interior.mem_nhds hxPoint)
  have hconv :
      ConvexOn ℝ (effective_domain f) (fun y ↦ (f y).toReal) :=
    convexOn_toReal_of_is_convex_function
      (hconvex).f_convex
      (fun y _ ↦ (hproblem).toIsBlockProximalGradientProblem.f_ne_bot y)
  let line : ℝ →ᵃ[ℝ] ((i : Fin p) → Ei i) := AffineMap.lineMap xPoint xStar
  let φ : ℝ → ℝ := fun t ↦ (f (line t)).toReal
  have hφ_convex : ConvexOn ℝ (line ⁻¹' effective_domain f) φ := by
    simpa [φ, line] using hconv.comp_affineMap line
  have hφ_zero : (0 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using interior_subset hxPoint
  have hφ_one : (1 : ℝ) ∈ line ⁻¹' effective_domain f := by
    simpa [line] using hxStar
  have hφ_deriv :
      HasDerivAt φ
        ((fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) xPoint)
          (xStar - xPoint)) 0 := by
    have hbase :
        HasFDerivAt
          (fun y : (i : Fin p) → Ei i ↦ (f y).toReal)
          (fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) xPoint)
          (line 0) := by
      simpa [line] using hdiffAt.hasFDerivAt
    have hline : HasDerivAt line (xStar - xPoint) 0 := by
      simpa [line] using
        (show HasDerivAt (AffineMap.lineMap xPoint xStar) (xStar - xPoint) (0 : ℝ) from
          AffineMap.hasDerivAt_lineMap)
    simpa [φ, line] using HasFDerivAt.comp_hasDerivAt (x := 0) hbase hline
  have hsecant :=
    hφ_convex.le_slope_of_hasDerivAt hφ_zero hφ_one zero_lt_one hφ_deriv
  have hsecant' :
      (fderiv ℝ (fun y : (i : Fin p) → Ei i ↦ (f y).toReal) xPoint)
          (xStar - xPoint) ≤
        (f xStar).toReal - (f xPoint).toReal := by
    simpa [φ, line, slope] using hsecant
  rw [cbpg_fderiv_apply_eq_sum_block_pairings
    (hconvex := hconvex) (x0 := x0) hxPoint] at hsecant'
  exact hsecant'

/-- Helper for Theorem 11.7: the source residual at `x^{k+1}` controls the objective gap against
any fixed optimizer. -/
lemma cbpg_objective_gap_le_final_residual_mul_dist
    {xStar : (i : Fin p) → Ei i}
    (hxStar : xStar ∈ XStar)
    (k : ℕ) :
    Δ[k + 1] ≤
      ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ *
        dist x₂[k + 1] (toPiLp xStar) :=
  by
  have hxkp1_g :
      x[k + 1] ∈ effective_domain (separableSum g) :=
    cbpg_outer_iterate_mem_effective_domain
      (hconvex := hconvex)
      (x0 := x0)
      (k + 1)
  have hxkp1_int :
      x[k + 1] ∈ interior (effective_domain f) := by
    -- The final outer iterate stays in the smooth interior because its separable penalty is finite.
    exact
      IsBlockProximalGradientProblem.mem_interior_effective_domain_of_mem_g_effective_domain
        (hproblem).toIsBlockProximalGradientProblem hxkp1_g
  have hxkp1_f :
      x[k + 1] ∈ effective_domain f := interior_subset hxkp1_int
  have hxStar_g :
      xStar ∈ effective_domain (separableSum g) :=
    cbpg_mem_effective_domain_of_mem_optimal_set
      (hconvex := hconvex)
      (x0 := x0)
      hxStar
  have hxStar_f :
      xStar ∈ effective_domain f := by
    -- Every optimizer is also feasible for the smooth term.
    exact
      interior_subset
        (IsBlockProximalGradientProblem.mem_interior_effective_domain_of_mem_g_effective_domain
          (hproblem).toIsBlockProximalGradientProblem hxStar_g)
  have hsupport :=
    cbpg_convex_support_sum_at_point
      (hconvex := hconvex) (x0 := x0) hxkp1_int hxStar_f
  have hsupport_f :
      (f x[k + 1]).toReal - (f xStar).toReal ≤
        ∑ i, inner ℝ (block_gradient i x[k + 1]) (x[k + 1] i - xStar i) := by
    have hsum_neg :
        (∑ i, inner ℝ (block_gradient i x[k + 1]) (x[k + 1] i - xStar i)) =
          -(∑ i, inner ℝ (block_gradient i x[k + 1]) (xStar i - x[k + 1] i)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [← inner_neg_right]
      congr 1
      abel
    rw [hsum_neg]
    linarith [neg_le_neg hsupport]
  have hblock_gap :
      ∀ j : Fin p,
        (g j (x[k + 1] j)).toReal - (g j (xStar j)).toReal ≤
          inner ℝ
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
              block_gradient j x[k + 1])
            (x[k + 1] j - xStar j) := by
    intro j
    have hxkp1j :
        x[k + 1] j ∈ effective_domain (g j) := by
      exact
        block_mem_effective_domain_of_mem_separableSum_effective_domain
          g
          (hproblem).block_g_proper
          hxkp1_g
          j
    have hxStarj :
        xStar j ∈ effective_domain (g j) := by
      exact
        block_mem_effective_domain_of_mem_separableSum_effective_domain
          g
          (hproblem).block_g_proper
          hxStar_g
          j
    have hmem :
        cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
            block_gradient j x[k + 1] ∈
          euclideanSubdifferential (g j) (x[k + 1] j) :=
      cbpg_final_residual_coordinate_mem_euclideanSubdifferential
        (hconvex := hconvex)
        (x0 := x0)
        k
        j
    have hsub :
        (InnerProductSpace.toDualMap ℝ (Ei j)
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
              block_gradient j x[k + 1])) (xStar j - x[k + 1] j) ≤
          (g j (xStar j)).toReal - (g j (x[k + 1] j)).toReal := by
      rw [mem_euclideanSubdifferential_iff, mem_strongDualSubdifferential] at hmem
      exact
        subgradient_eval_le_toReal_sub
          (g j)
          (x[k + 1] j)
          (xStar j)
          (fun z hz ↦ ((hproblem).block_g_proper j).ne_bot z)
          hxkp1j
          hxStarj
          (by simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hmem)
    have hbase :
        (g j (x[k + 1] j)).toReal - (g j (xStar j)).toReal ≤
          -inner ℝ
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
              block_gradient j x[k + 1])
            (xStar j - x[k + 1] j) := by
      calc
        (g j (x[k + 1] j)).toReal - (g j (xStar j)).toReal =
            -((g j (xStar j)).toReal - (g j (x[k + 1] j)).toReal) := by ring
        _ ≤
            -(InnerProductSpace.toDualMap ℝ (Ei j)
                (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
                  block_gradient j x[k + 1]))
                (xStar j - x[k + 1] j) := neg_le_neg hsub
        _ =
            -inner ℝ
              (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
                block_gradient j x[k + 1])
              (xStar j - x[k + 1] j) := by
          rw [InnerProductSpace.toDualMap_apply_apply]
    calc
      (g j (x[k + 1] j)).toReal - (g j (xStar j)).toReal ≤
          -inner ℝ
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
              block_gradient j x[k + 1])
            (xStar j - x[k + 1] j) := hbase
      _ = inner ℝ
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
              block_gradient j x[k + 1])
            (x[k + 1] j - xStar j) := by
        rw [← inner_neg_right]
        congr 1
        abel
  have hsupport_g :
      (∑ j, ((g j (x[k + 1] j)).toReal - (g j (xStar j)).toReal)) ≤
        ∑ j,
          inner ℝ
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
              block_gradient j x[k + 1])
            (x[k + 1] j - xStar j) := by
    -- Sum the blockwise subgradient inequalities over the whole coordinate family.
    exact Finset.sum_le_sum fun j _ ↦ hblock_gap j
  have hsum_residual :
      (∑ i, inner ℝ (block_gradient i x[k + 1]) (x[k + 1] i - xStar i)) +
          (∑ j,
            inner ℝ
              (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
                block_gradient j x[k + 1])
              (x[k + 1] j - xStar j)) =
        ∑ j,
          inner ℝ
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j)
            (x[k + 1] j - xStar j) := by
    -- The smooth-gradient contribution and the correction term recombine into the final residual.
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [inner_sub_left]
    ring
  have hxkp1_obj :
      F x[k + 1] =
        ((((f x[k + 1]).toReal + (∑ j, (g j (x[k + 1] j)).toReal) : ℝ)) : EReal) :=
    cbpg_objective_eq_real_sum_of_mem_effective_domain
      (hconvex := hconvex)
      (x0 := x0)
      hxkp1_g
  have hxStar_obj :
      F xStar =
        ((((f xStar).toReal + (∑ j, (g j (xStar j)).toReal) : ℝ)) : EReal) :=
    cbpg_objective_eq_real_sum_of_mem_effective_domain
      (hconvex := hconvex)
      (x0 := x0)
      hxStar_g
  have hsum_xkp1 :
      (F x[k + 1]).toReal =
        (f x[k + 1]).toReal + ∑ j, (g j (x[k + 1] j)).toReal := by
    simpa using congrArg EReal.toReal hxkp1_obj
  have hsum_xStar :
      (f xStar).toReal + ∑ j, (g j (xStar j)).toReal = FOpt := by
    have hFxStar :
        F xStar = (FOpt : EReal) :=
      cbpg_objective_eq_optimal_value_of_mem_optimal_set
        (hconvex := hconvex)
        (x0 := x0)
        hxStar
    have hreal :
        ((((f xStar).toReal + (∑ j, (g j (xStar j)).toReal) : ℝ)) : EReal) =
          (FOpt : EReal) := by
      calc
        ((((f xStar).toReal + (∑ j, (g j (xStar j)).toReal) : ℝ)) : EReal) =
            F xStar := by
          symm
          exact hxStar_obj
        _ = (FOpt : EReal) := hFxStar
    simpa using congrArg EReal.toReal hreal
  have hgap_sum :
      Δ[k + 1] =
        (f x[k + 1]).toReal - (f xStar).toReal +
          ∑ j, ((g j (x[k + 1] j)).toReal - (g j (xStar j)).toReal) := by
    -- Rewrite the objective gap through the real smooth term and the real blockwise penalty sum.
    calc
      Δ[k + 1] = (F x[k + 1]).toReal - FOpt := by rfl
      _ = (F x[k + 1]).toReal -
            ((f xStar).toReal + ∑ j, (g j (xStar j)).toReal) := by
          rw [hsum_xStar]
      _ =
          ((f x[k + 1]).toReal + ∑ j, (g j (x[k + 1] j)).toReal) -
            ((f xStar).toReal + ∑ j, (g j (xStar j)).toReal) := by
          rw [hsum_xkp1]
      _ =
          (f x[k + 1]).toReal - (f xStar).toReal +
            ∑ j, ((g j (x[k + 1] j)).toReal - (g j (xStar j)).toReal) := by
          rw [Finset.sum_sub_distrib]
          ring
  have hsum_gap :
      Δ[k + 1] ≤
        ∑ j,
          inner ℝ
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j)
            (x[k + 1] j - xStar j) := by
    -- Combine the smooth convex support inequality and the blockwise penalty inequalities.
    rw [hgap_sum]
    have hpair :
        (f x[k + 1]).toReal - (f xStar).toReal +
            ∑ j, ((g j (x[k + 1] j)).toReal - (g j (xStar j)).toReal) ≤
          (∑ i, inner ℝ (block_gradient i x[k + 1]) (x[k + 1] i - xStar i)) +
            (∑ j,
              inner ℝ
                (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
                  block_gradient j x[k + 1])
                (x[k + 1] j - xStar j)) := by
      linarith [hsupport_f, hsupport_g]
    calc
      (f x[k + 1]).toReal - (f xStar).toReal +
          ∑ j, ((g j (x[k + 1] j)).toReal - (g j (xStar j)).toReal) ≤
        (∑ i, inner ℝ (block_gradient i x[k + 1]) (x[k + 1] i - xStar i)) +
          (∑ j,
            inner ℝ
              (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j -
                block_gradient j x[k + 1])
              (x[k + 1] j - xStar j)) := hpair
      _ =
        ∑ j,
          inner ℝ
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j)
            (x[k + 1] j - xStar j) := hsum_residual
  have hinner_residual :
      ∑ j,
          inner ℝ
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j)
            (x[k + 1] j - xStar j) =
        inner ℝ
          (ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k))
          (ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
            (x[k + 1] - xStar)) := by
    -- Expand the canonical `PiLp` inner product coordinatewise.
    symm
    rw [PiLp.inner_apply]
    rfl
  have hcs :
      inner ℝ
          (ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k))
          (ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
            (x[k + 1] - xStar)) ≤
        ‖ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ *
          ‖ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
              (x[k + 1] - xStar)‖ := by
    -- Apply Cauchy-Schwarz in the canonical Hilbert-product owner.
    exact
      real_inner_le_norm
        (ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
          (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k))
        (ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
          (x[k + 1] - xStar))
  have hnorm_residual :
      ‖ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
          (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ =
        ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ := by
    rfl
  have hnorm_dist :
      ‖ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
          (x[k + 1] - xStar)‖ =
        dist x₂[k + 1] (toPiLp xStar) := by
    simp [dist_eq_norm]
  calc
    Δ[k + 1] ≤
        ∑ j,
          inner ℝ
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j)
            (x[k + 1] j - xStar j) := hsum_gap
    _ =
        inner ℝ
          (ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k))
          (ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
            (x[k + 1] - xStar)) := hinner_residual
    _ ≤
        ‖ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
            (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ *
          ‖ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
              (x[k + 1] - xStar)‖ := hcs
    _ =
        ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ *
          dist x₂[k + 1] (toPiLp xStar) := by
      rw [hnorm_residual, hnorm_dist]

/-- Helper for Theorem 11.7: passing from a fixed optimizer to the optimal set upgrades the
pointwise residual-gap estimate to the `infDist` formulation used by the radius bound. -/
lemma cbpg_objective_gap_le_final_residual_mul_infDist
    (k : ℕ) :
    Δ[k + 1] ≤
      ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ *
        infDist x₂[k + 1] XStar₂ := by
  by_cases hzero :
      ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ = 0
  · rcases (hconvex).optimal_set_nonempty with ⟨xStar, hxStar⟩
    have hgap_zero :
        Δ[k + 1] ≤ 0 := by
      -- If the residual norm vanishes, the fixed-optimizer estimate collapses the gap to zero.
      have hgap := cbpg_objective_gap_le_final_residual_mul_dist
          (hconvex := hconvex)
          (x0 := x0)
          hxStar
          k
      rw [hzero, zero_mul] at hgap
      exact hgap
    rw [hzero, zero_mul]
    exact hgap_zero
  · have hnorm_pos :
        0 < ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ := by
      have hne :
          0 ≠ ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ := by
        intro hnorm
        exact hzero hnorm.symm
      exact lt_of_le_of_ne (norm_nonneg _) hne
    have hscaled_le_dist :
        ∀ {xStar : (i : Fin p) → Ei i}, xStar ∈ XStar →
          Δ[k + 1] /
              ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ ≤
            dist x₂[k + 1] (toPiLp xStar) := by
      intro xStar hxStar
      -- Divide the pointwise optimizer estimate by the positive residual norm.
      have hgap :=
        cbpg_objective_gap_le_final_residual_mul_dist
          (hconvex := hconvex)
          (x0 := x0)
          hxStar
          k
      exact (div_le_iff₀ hnorm_pos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hgap
    have hscaled_le_infDist :
        Δ[k + 1] /
            ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ ≤
          infDist x₂[k + 1] XStar₂ := by
      -- The divided estimate holds against every optimizer, so it holds against the infimum
      -- distance to the optimal set.
      have hXStar₂ : (XStar₂).Nonempty :=
        (hconvex).optimal_set_nonempty.image toPiLp
      exact (Metric.le_infDist hXStar₂).2 <| by
        intro xStar₂ hxStar₂
        rcases hxStar₂ with ⟨xStar, hxStar, rfl⟩
        exact hscaled_le_dist hxStar
    have hmul :
        (Δ[k + 1] /
            ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖) *
            ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ ≤
          infDist x₂[k + 1] XStar₂ *
            ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ := by
      exact mul_le_mul_of_nonneg_right hscaled_le_infDist (norm_nonneg _)
    calc
      Δ[k + 1] =
          (Δ[k + 1] /
              ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖) *
            ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ := by
        field_simp [hzero]
      _ ≤ infDist x₂[k + 1] XStar₂ *
            ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ := hmul
      _ = ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ *
            infDist x₂[k + 1] XStar₂ := by ring

/-- Helper for Theorem 11.7: the final residual norm is controlled by the full outer-step
displacement with the exact textbook `(L_f + L_max)` coefficient. -/
lemma cbpg_final_residual_norm_sq_le_outer_step
    (k : ℕ) :
    ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ ^ (2 : ℕ) ≤
      (p : ℝ) *
        (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) *
        ‖x₂[k] - x₂[k + 1]‖ ^ (2 : ℕ) := by
  let C : ℝ := (Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)
  let s : ℝ := ‖x₂[k] - x₂[k + 1]‖
  have hpilp_sq :
      ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ ^ (2 : ℕ) =
        Finset.sum Finset.univ
          (fun j : Fin p ↦ ‖cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j‖ ^ (2 : ℕ)) := by
    -- Expand the canonical `L²` norm of the residual tuple as the sum of the squared coordinates.
    simpa using
      (PiLp.norm_sq_eq_of_L2
        (fun j : Fin p ↦ Ei j)
        (toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)))
  have hcoord_sq :
      ∀ j : Fin p,
        ‖cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j‖ ^ (2 : ℕ) ≤
          (C * s) ^ (2 : ℕ) := by
    intro j
    exact
      pow_le_pow_left₀
        (norm_nonneg _)
        (cbpg_final_residual_coordinate_norm_le_lf_plus_lmax_mul_outer_step
          (hconvex := hconvex)
          (x0 := x0)
          k
          j)
        2
  have hsum :
      Finset.sum Finset.univ
          (fun j : Fin p ↦ ‖cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j‖ ^ (2 : ℕ)) ≤
        Finset.sum Finset.univ (fun _ : Fin p ↦ (C * s) ^ (2 : ℕ)) := by
    -- Sum the uniform coordinatewise residual bound over all blocks.
    exact Finset.sum_le_sum fun j _ ↦ hcoord_sq j
  -- Finish by transporting to `PiLp`, summing the coordinate bounds, and expanding the constant.
  calc
    ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ ^ (2 : ℕ) =
        Finset.sum Finset.univ
          (fun j : Fin p ↦ ‖cbpg_final_residual (hconvex := hconvex) (x0 := x0) k j‖ ^ (2 : ℕ)) := by
      exact hpilp_sq
    _ ≤ Finset.sum Finset.univ (fun _ : Fin p ↦ (C * s) ^ (2 : ℕ)) := hsum
    _ = (p : ℝ) * (C * s) ^ (2 : ℕ) := by
      simp [Finset.card_univ, C, s, mul_assoc, mul_left_comm, mul_comm]
    _ = (p : ℝ) * (C ^ (2 : ℕ)) * (s ^ (2 : ℕ)) := by
      rw [pow_two, pow_two]
      ring
    _ =
        (p : ℝ) *
          (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) *
          ‖x₂[k] - x₂[k + 1]‖ ^ (2 : ℕ) := by
      rfl

/-- Helper for Theorem 11.7: the radius bound yields the quadratic objective-gap estimate from
Lemma 11.6. -/
lemma cbpg_objective_gap_sq_bound_of_radius_bound
    (Rα : PosReal)
    (hRα : RadiusBound Rα)
    (k : ℕ) :
    cbpgObjectiveGapSqBound Lf Li Rα
      (fun z : PiLp 2 Ei ↦ F z) (fun m ↦ x₂[m]) FOpt k := by
  have hanti :
      Antitone (fun n ↦ F x[n]) :=
    cbpg_objective_values_antitone
      (hconvex := hconvex)
      (x0 := x0)
  have hxk_le_x0 :
      F x[k + 1] ≤ F x[0] := by
    -- The full outer sequence stays in the initial sublevel set because the objective is
    -- antitone along CBPG iterates.
    simpa using hanti (Nat.zero_le (k + 1))
  have hinfDist_le :
      infDist x₂[k + 1] XStar₂ ≤ Rα :=
    hRα hxk_le_x0
  have hgap_inf :
      Δ[k + 1] ≤
        ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ *
          infDist x₂[k + 1] XStar₂ :=
    cbpg_objective_gap_le_final_residual_mul_infDist
      (hconvex := hconvex)
      (x0 := x0)
      k
  have hgap_radius :
      Δ[k + 1] ≤
        ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ * (Rα : ℝ) := by
    -- The radius bound upgrades the `infDist` term to the textbook radius `R_α`.
    calc
      Δ[k + 1] ≤
          ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ *
            infDist x₂[k + 1] XStar₂ := hgap_inf
      _ ≤ ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ * (Rα : ℝ) := by
        exact mul_le_mul_of_nonneg_left hinfDist_le (norm_nonneg _)
  have hgap_nonneg :
      0 ≤ Δ[k + 1] :=
    cbpg_objective_gap_nonneg
      (hconvex := hconvex)
      (x0 := x0)
      (k + 1)
  have hresidual_nonneg :
      0 ≤ ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ :=
    norm_nonneg _
  have hgap_sq :
      Δ[k + 1] ^ (2 : ℕ) ≤
        ((Rα : ℝ) ^ (2 : ℕ)) *
          ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ ^ (2 : ℕ) := by
    -- Squaring the radius estimate is valid because all factors are nonnegative.
    nlinarith [hgap_radius, hgap_nonneg, hresidual_nonneg, PosReal.coe_pos Rα]
  have hresidual_sq :
      ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ ^ (2 : ℕ) ≤
        (p : ℝ) *
          (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) *
          ‖x₂[k] - x₂[k + 1]‖ ^ (2 : ℕ) :=
    cbpg_final_residual_norm_sq_le_outer_step
      (hconvex := hconvex)
      (x0 := x0)
      k
  have hR_sq_nonneg : 0 ≤ ((Rα : ℝ) ^ (2 : ℕ)) := by
    positivity
  have hscaled :
      ((Rα : ℝ) ^ (2 : ℕ)) *
          ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ ^ (2 : ℕ) ≤
        ((Rα : ℝ) ^ (2 : ℕ)) *
          ((p : ℝ) *
            (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) *
            ‖x₂[k] - x₂[k + 1]‖ ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hresidual_sq hR_sq_nonneg
  -- Route correction: the final bridge now follows the source structure explicitly,
  -- separating the optimizer-distance estimate from the residual-norm estimate.
  calc
    ((F x[k + 1]).toReal - FOpt) ^ (2 : ℕ) = Δ[k + 1] ^ (2 : ℕ) := by
      rfl
    _ ≤
        ((Rα : ℝ) ^ (2 : ℕ)) *
          ‖toPiLp (cbpg_final_residual (hconvex := hconvex) (x0 := x0) k)‖ ^ (2 : ℕ) := hgap_sq
    _ ≤
        ((Rα : ℝ) ^ (2 : ℕ)) *
          ((p : ℝ) *
            (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) *
            ‖x₂[k] - x₂[k + 1]‖ ^ (2 : ℕ)) := hscaled
    _ =
        (p : ℝ) *
          (((Lf : ℝ) + ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) ^ (2 : ℕ)) *
          ((Rα : ℝ) ^ (2 : ℕ)) *
          ‖x₂[k] - x₂[k + 1]‖ ^ (2 : ℕ) := by ring

-- TODO: derive the scalar recurrence from the CBPG sufficient-decrease estimate by bridging
-- through the local gap-square lemma above and the real/EReal comparison lemmas above.
/-- Helper for Theorem 11.7: the one-step CBPG decrease estimate induces the scalar quadratic
recurrence for the objective-gap sequence. -/
lemma cbpg_objective_gap_step_recurrence
    (Rα : PosReal)
    (hRα : RadiusBound Rα)
    (k : ℕ) :
    Δ[k] - Δ[k + 1] ≥
      cbpg_quadratic_gap_constant Lf Li Rα * (Δ[k + 1] ^ (2 : ℕ)) := by
  have hgapSq :
      cbpgObjectiveGapSqBound Lf Li Rα
        (fun z : PiLp 2 Ei ↦ F z) (fun m ↦ x₂[m]) FOpt k :=
    cbpg_objective_gap_sq_bound_of_radius_bound
      (hconvex := hconvex)
      (x0 := x0)
      Rα
      hRα
      k
  have hstep :
      cbpgStepDecreaseBound Li
        (fun z : PiLp 2 Ei ↦ F z) (fun m ↦ x₂[m]) k :=
    cbpg_step_decrease_bound
      (hconvex := hconvex)
      (x0 := x0)
      k
  have hdropE :
      F x[k] - F x[k + 1] ≥
        (((cbpg_quadratic_gap_constant Lf Li Rα *
            (((F x[k + 1]).toReal - FOpt) ^ (2 : ℕ)) : ℝ) : EReal)) := by
    exact
      @cbpg_step_decrease_ge_sq_objective_gap
        p _ (PiLp 2 Ei) _ Lf Li
        (fun z : PiLp 2 Ei ↦ F z)
        (fun m ↦ x₂[m])
        FOpt Rα k hgapSq hstep
  have hdrop_real :
      (F x[k]).toReal - (F x[k + 1]).toReal ≥
        cbpg_quadratic_gap_constant Lf Li Rα *
          (((F x[k + 1]).toReal - FOpt) ^ (2 : ℕ)) := by
    -- Rewrite the finite objective drop into the real form before comparing coefficients.
    rw [cbpg_objective_step_decrease_real_form (hconvex := hconvex) (x0 := x0) k] at hdropE
    exact EReal.coe_le_coe_iff.mp hdropE
  rw [cbpg_objective_gap_difference_eq_toReal_difference
    (hconvex := hconvex) (x0 := x0) k]
  exact hdrop_real

-- TODO: package the radius witness supplied by Theorem 11.6 at the initial objective level
-- `F x[0]` into the `RadiusBound` formulation used by the scalar recurrence theorem.
/-- Helper for Theorem 11.7: the convex CBPG assumptions supply a radius controlling the initial
sublevel set through the distance-to-`XStar` formulation used in Lemma 11.6. -/
lemma cbpg_exists_initial_sublevel_radius :
    ∃ Rα : PosReal, RadiusBound Rα := by
  let α0 : PosReal :=
    ⟨max (F x[0]).toReal 0 + 1,
      add_pos_of_nonneg_of_pos (le_max_right (F x[0]).toReal 0) zero_lt_one⟩
  have hα0 :
      F x[0] ≤ (((α0 : ℝ)) : EReal) := by
    have htop := cbpg_objective_value_ne_top (hconvex := hconvex) (x0 := x0) 0
    have hbot := cbpg_objective_value_ne_bot (hconvex := hconvex) (x0 := x0) 0
    -- Compare the finite initial objective value with the positive level `α0`.
    calc
      F x[0] = ((((F x[0]).toReal : ℝ)) : EReal) :=
        (EReal.coe_toReal htop hbot).symm
      _ ≤ (((α0 : ℝ)) : EReal) := by
        refine EReal.coe_le_coe ?_
        have hmax : (F x[0]).toReal ≤ max (F x[0]).toReal 0 := le_max_left _ _
        change (F x[0]).toReal ≤ max (F x[0]).toReal 0 + 1
        exact hmax.trans (by linarith)
  obtain ⟨Rraw, hRraw⟩ :=
    (hconvex).bounded_sublevel_distance_to_each_optimal_point α0
  obtain ⟨i⟩ := ‹Nonempty (Fin p)›
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast (lt_of_le_of_lt (Nat.zero_le i.1) i.2)
  let c : PosReal := ⟨Real.sqrt (p : ℝ), Real.sqrt_pos.2 hp_pos⟩
  let Rα : PosReal :=
    ⟨(c : ℝ) * (Rraw : ℝ), mul_pos (PosReal.coe_pos c) (PosReal.coe_pos Rraw)⟩
  rcases (hconvex).optimal_set_nonempty with ⟨xStar, hxStar⟩
  refine ⟨Rα, ?_⟩
  intro xPoint hxPoint
  have hraw : ‖xPoint - xStar‖ ≤ (Rraw : ℝ) :=
    hRraw (hxPoint.trans hα0) hxStar
  refine (infDist_le_dist_of_mem (show toPiLp xStar ∈ XStar₂ from ⟨xStar, hxStar, rfl⟩)).trans ?_
  calc
    dist (toPiLp xPoint) (toPiLp xStar) = ‖toPiLp (xPoint - xStar)‖ := by
      simp [dist_eq_norm]
    _ ≤ Real.sqrt (p : ℝ) * ‖xPoint - xStar‖ :=
      toPiLp_norm_le_sqrt_card_mul_raw_norm
        (hconvex := hconvex) (x0 := x0) (xPoint - xStar)
    _ ≤ Real.sqrt (p : ℝ) * (Rraw : ℝ) := by
      exact mul_le_mul_of_nonneg_left hraw (Real.sqrt_nonneg _)
    _ = (Rα : ℝ) := by rfl

-- TODO: rewrite the scalar recurrence coefficient `γ = c⁻¹` into the textbook denominator
-- `4 / (c t)` before feeding the bound back into the Chapter 11 statement.
/-- Helper for Theorem 11.7: after setting the scalar recurrence parameter to the reciprocal of
the CBPG quadratic-gap coefficient, the sublinear term from Lemma 11.7 rewrites to the textbook
quantity `4 / (c t)`. -/
lemma cbpg_sublinear_term_eq
    (Rα : PosReal) (t : ℝ) :
    let γ : PosReal :=
      ⟨(cbpg_quadratic_gap_constant Lf Li Rα)⁻¹,
        inv_pos.mpr
          (cbpg_quadratic_gap_constant_pos
            Rα)⟩
    4 * (γ : ℝ) / t =
      4 / (cbpg_quadratic_gap_constant Lf Li Rα * t) := by
  dsimp
  by_cases ht : t = 0
  · -- When `t = 0`, both rational expressions are definitionally zero.
    simp [ht]
  · have hc_ne : cbpg_quadratic_gap_constant Lf Li Rα ≠ 0 :=
      (cbpg_quadratic_gap_constant_pos
        Rα).ne'
    -- For nonzero denominators, this is the textbook reciprocal identity.
    field_simp [hc_ne, ht]

-- TODO: package the quadratic recurrence with the reciprocal parameter `γ` so both closing
-- applications of Lemma 11.7 can reuse the same scalar hypothesis verbatim.
/-- Helper for Theorem 11.7: packaging the quadratic recurrence with the reciprocal parameter
`γ` gives the exact scalar hypothesis required by Lemma 11.7. -/
lemma cbpg_objective_gap_step_recurrence_with_gamma
    (Rα : PosReal)
    (hRα : RadiusBound Rα) :
    let γ : PosReal :=
      ⟨(cbpg_quadratic_gap_constant Lf Li Rα)⁻¹,
        inv_pos.mpr
          (cbpg_quadratic_gap_constant_pos
            Rα)⟩
    ∀ n : ℕ,
      Δ[n] - Δ[n + 1] ≥
        (1 / (γ : ℝ)) * (Δ[n + 1] ^ (2 : ℕ)) := by
  intro γ n
  -- Rewrite the quadratic coefficient as the reciprocal parameter used by Lemma 11.7.
  simpa [γ, one_div] using
    cbpg_objective_gap_step_recurrence
      (hconvex := hconvex)
      (x0 := x0)
      Rα hRα n

-- TODO: apply `nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence`
-- to `a n = Δ[n]` once the quadratic one-step recurrence has been established.
/-- If a radius `R_α` bounds the distance from the initial sublevel set
`{x | F(x) ≤ F(x^0)}` to the optimal set `X^*`, then the objective gap at iteration `k ≥ 2`
is bounded by the maximum of the geometric term
`(1 / 2)^((k - 1) / 2) (F(x^0) - F_opt)` and the sublinear term
`8 p (L_f + L_max)^2 R_α^2 / (L_min (k - 1))`. -/
theorem cbpg_objective_gap_le_max_geometric_or_sublinear_of_initial_sublevel_radius
    (Rα : PosReal)
    (hRα : RadiusBound Rα)
    (k : ℕ) (hk : 2 ≤ k) :
    Δ[k] ≤ GapBound[Rα,k] := by
  let γ : PosReal :=
    ⟨(cbpg_quadratic_gap_constant Lf Li Rα)⁻¹,
      inv_pos.mpr
        (cbpg_quadratic_gap_constant_pos
          Rα)⟩
  have hstep :
      ∀ n : ℕ,
        Δ[n] - Δ[n + 1] ≥
          (1 / (γ : ℝ)) * (Δ[n + 1] ^ (2 : ℕ)) := by
    -- Reuse the packaged reciprocal-parameter recurrence required by Lemma 11.7.
    simpa [γ] using
      cbpg_objective_gap_step_recurrence_with_gamma
        (hconvex := hconvex)
        (x0 := x0)
        Rα hRα
  have hmain :=
    nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
      (a := fun n ↦ Δ[n])
      (γ := γ)
      (cbpg_objective_gap_nonneg (hconvex := hconvex) (x0 := x0))
      hstep
      hk
  have hcoeff :
      4 * (γ : ℝ) / (((k - 1 : ℕ) : ℝ)) =
        4 / (cbpg_quadratic_gap_constant Lf Li Rα * (((k - 1 : ℕ) : ℝ))) := by
    simpa [γ] using
      cbpg_sublinear_term_eq
        (hconvex := hconvex)
        (x0 := x0)
        (Rα := Rα)
        (t := (((k - 1 : ℕ) : ℝ)))
  -- Lemma 11.7 gives the scalar max bound; the last step rewrites its sublinear branch.
  calc
    Δ[k] ≤
        max
          (((1 / 2 : ℝ) ^ (((k - 1 : ℕ) : ℝ) / 2)) * Δ[0])
          (4 * (γ : ℝ) / (((k - 1 : ℕ) : ℝ))) := hmain
    _ = GapBound[Rα,k] := by
      rw [hcoeff]

-- TODO: obtain the initial-sublevel radius witness from Theorem 11.6 and apply the explicit
-- radius version of the CBPG gap bound.
/-- Theorem 11.7 (1): under Assumptions 11.1 and 11.15, there exists a radius `R_α` together with
the corresponding initial-sublevel distance witness such that the CBPG objective gap at
iteration `k ≥ 2` is bounded by the maximum of the geometric and sublinear terms with that
`R_α`. -/
theorem cbpg_objective_gap_le_max_geometric_or_sublinear
    (k : ℕ) (hk : 2 ≤ k) :
    ∃ Rα : PosReal,
      RadiusBound Rα ∧
      Δ[k] ≤ GapBound[Rα,k] := by
  rcases cbpg_exists_initial_sublevel_radius
      (hconvex := hconvex) (x0 := x0) with ⟨Rα, hRα⟩
  refine ⟨Rα, hRα, ?_⟩
  -- Specialize the explicit-radius bound to the initial-sublevel witness.
  exact
    cbpg_objective_gap_le_max_geometric_or_sublinear_of_initial_sublevel_radius
      (hconvex := hconvex)
      (x0 := x0)
      Rα hRα k hk

-- TODO: reuse the same scalar recurrence and Chapter 11 epsilon-threshold lemma once the
-- recurrence proof is in place.
/-- If a radius `R_α` controls the initial sublevel set and the iteration index `n` satisfies the
textbook lower bound involving `ε`, then the CBPG objective gap at step `n` is at most `ε`. -/
theorem cbpg_objective_gap_le_of_iteration_count_bound_of_initial_sublevel_radius
    (Rα : PosReal)
    (hRα : RadiusBound Rα)
    (ε : PosReal) (n : ℕ)
    (hn : IterationThreshold[Rα,ε] ≤ (n : ℝ)) :
    Δ[n] ≤ ε := by
  let γ : PosReal :=
    ⟨(cbpg_quadratic_gap_constant Lf Li Rα)⁻¹,
      inv_pos.mpr
        (cbpg_quadratic_gap_constant_pos
          Rα)⟩
  have hstep :
      ∀ m : ℕ,
        Δ[m] - Δ[m + 1] ≥
          (1 / (γ : ℝ)) * (Δ[m + 1] ^ (2 : ℕ)) := by
    -- Reuse the packaged reciprocal-parameter recurrence from the first rate estimate.
    simpa [γ] using
      cbpg_objective_gap_step_recurrence_with_gamma
        (hconvex := hconvex)
        (x0 := x0)
        Rα hRα
  have hcoeff :
      4 * (γ : ℝ) / (ε : ℝ) =
        4 / (cbpg_quadratic_gap_constant Lf Li Rα * (ε : ℝ)) := by
    simpa [γ] using
      cbpg_sublinear_term_eq
        (hconvex := hconvex)
        (x0 := x0)
        (Rα := Rα)
        (t := (ε : ℝ))
  have hn' :
      max
          ((2 / Real.log 2) * (Real.log (Δ[0]) + Real.log (1 / (ε : ℝ))))
          (4 * (γ : ℝ) / (ε : ℝ)) +
        1 ≤
        (n : ℝ) := by
    rw [hcoeff]
    exact hn
  -- Invoke the scalar epsilon-threshold lemma on the objective-gap sequence.
  exact
    nonnegative_sequence_le_epsilon_of_quadratic_step_recurrence
      (a := fun m ↦ Δ[m])
      (γ := γ)
      (cbpg_objective_gap_nonneg (hconvex := hconvex) (x0 := x0))
      hstep
      ε
      hn'

-- TODO: extract the initial-sublevel radius witness from Theorem 11.6 and specialize the
-- explicit-radius epsilon-complexity estimate to that witness.
/-- Theorem 11.7 (2): under Assumptions 11.1 and 11.15, there exists a radius `R_α` together with
the corresponding initial-sublevel distance witness such that, whenever the iteration index `n`
satisfies the textbook lower bound with that `R_α`, the objective gap at step `n` is at most
`ε`. -/
theorem cbpg_objective_gap_le_of_iteration_count_bound
    (ε : PosReal) (n : ℕ) :
    ∃ Rα : PosReal,
      RadiusBound Rα ∧
      (IterationThreshold[Rα,ε] ≤ (n : ℝ) →
        Δ[n] ≤ ε) := by
  rcases cbpg_exists_initial_sublevel_radius
      (hconvex := hconvex) (x0 := x0) with ⟨Rα, hRα⟩
  refine ⟨Rα, hRα, ?_⟩
  intro hn
  -- Reuse the explicit-radius epsilon bound with the chosen initial-sublevel witness.
  exact
    cbpg_objective_gap_le_of_iteration_count_bound_of_initial_sublevel_radius
      (hconvex := hconvex)
      (x0 := x0)
      Rα hRα ε n hn

end

end
