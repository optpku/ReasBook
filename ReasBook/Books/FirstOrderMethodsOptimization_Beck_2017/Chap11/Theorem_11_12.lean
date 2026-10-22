/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_10
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_9
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_6
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_5
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Lemma_11_1
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_1
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Theorem_11_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe v

open scoped Gradient Pointwise BigOperators

section

/-- Helper for Theorem 11.12: a real-valued antitone sequence that is bounded below has
successive differences converging to `0`. -/
private lemma objective_gap_tendsto_zero_of_antitone_bddBelow
    {φ : ℕ → ℝ}
    (hanti : Antitone φ)
    (hbelow : BddBelow (Set.range φ)) :
    Filter.Tendsto (fun k ↦ φ k - φ (k + 1)) Filter.atTop (nhds 0) := by
  let ℓ : ℝ := ⨅ k, φ k
  have hobj :
      Filter.Tendsto (fun k ↦ φ k) Filter.atTop (nhds ℓ) :=
    tendsto_atTop_ciInf hanti hbelow
  have hobj_shift :
      Filter.Tendsto (fun k ↦ φ (k + 1)) Filter.atTop (nhds ℓ) := by
    have hshift :
        Filter.Tendsto (fun k : ℕ ↦ k + 1) Filter.atTop Filter.atTop :=
      (show StrictMono (fun k : ℕ ↦ k + 1) from
        fun a b hab ↦ Nat.add_lt_add_right hab 1).tendsto_atTop
    simpa [ℓ] using hobj.comp hshift
  -- Subtracting the shifted copy leaves a sequence converging to `ℓ - ℓ = 0`.
  simpa [ℓ] using hobj.sub hobj_shift

/-- Helper for Theorem 11.12: summing one-step real objective drops over a prefix telescopes to
the gap between the initial and terminal objective values. -/
private lemma proximal_gradient_real_objective_telescope
    (φ : ℕ → ℝ) (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ φ n - φ (n + 1)) =
      φ 0 - φ (k + 1) := by
  have htel := Finset.sum_range_sub φ (k + 1)
  calc
    Finset.sum (Finset.range (k + 1)) (fun n ↦ φ n - φ (n + 1)) =
        Finset.sum (Finset.range (k + 1)) (fun n ↦ -(φ (n + 1) - φ n)) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      ring
    _ = -Finset.sum (Finset.range (k + 1)) (fun n ↦ φ (n + 1) - φ n) := by
      rw [Finset.sum_neg_distrib]
    _ = -(φ (k + 1) - φ 0) := by
      rw [htel]
    _ = φ 0 - φ (k + 1) := by
      ring

/-- Helper for Theorem 11.12: if a positive scalar multiple of squared norms tends to `0`, then
the underlying vector sequence tends to `0`. -/
private lemma tendsto_zero_of_scaled_sq_norm_tendsto_zero
    {E : Type*} [NormedAddCommGroup E]
    {u : ℕ → E} {c : ℝ}
    (hc : 0 < c)
    (hscaled :
      Filter.Tendsto (fun k ↦ c * ‖u k‖ ^ (2 : ℕ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  have hsq_eq :
      (fun k ↦ ‖u k‖ ^ (2 : ℕ)) =
        fun k ↦ (1 / c) * (c * ‖u k‖ ^ (2 : ℕ)) := by
    funext k
    field_simp [hc.ne']
  have hsq_tendsto_zero :
      Filter.Tendsto (fun k ↦ ‖u k‖ ^ (2 : ℕ)) Filter.atTop (nhds 0) := by
    rw [hsq_eq]
    simpa using hscaled.const_mul (1 / c)
  have hsqrt_tendsto_zero :
      Filter.Tendsto (fun k ↦ Real.sqrt (‖u k‖ ^ (2 : ℕ))) Filter.atTop (nhds 0) := by
    let hsqrt_cont : ContinuousAt Real.sqrt 0 := Real.continuous_sqrt.continuousAt
    simpa only [Function.comp, Real.sqrt_zero] using hsqrt_cont.tendsto.comp hsq_tendsto_zero
  have hnorm_eq_sqrt :
      ∀ k, ‖u k‖ = Real.sqrt (‖u k‖ ^ (2 : ℕ)) := by
    intro k
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    exact norm_nonneg _
  have hnorm_tendsto_zero :
      Filter.Tendsto (fun k ↦ ‖u k‖) Filter.atTop (nhds 0) := by
    have hEq :
        (fun k ↦ ‖u k‖) = fun k ↦ Real.sqrt (‖u k‖ ^ (2 : ℕ)) := by
      funext k
      exact hnorm_eq_sqrt k
    rw [hEq]
    exact hsqrt_tendsto_zero
  -- Convergence in norm to zero is equivalent to convergence of the vector sequence to `0`.
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  simpa using hnorm_tendsto_zero

/-- Helper for Theorem 11.12: lower semicontinuity bounds the value at the limit point by the
`liminf` along any convergent sequence. -/
private lemma lowerSemicontinuous_value_le_liminf_along_sequence
    {E : Type*} [TopologicalSpace E]
    {h : E → EReal} (hclosed : LowerSemicontinuous h) {z : ℕ → E} {xBar : E}
    (hz : Filter.Tendsto z Filter.atTop (nhds xBar)) :
    h xBar ≤ Filter.liminf (fun n ↦ h (z n)) Filter.atTop := by
  calc
    h xBar ≤ Filter.liminf h (nhds xBar) := hclosed.le_liminf xBar
    _ ≤ Filter.liminf h (Filter.map z Filter.atTop) := Filter.liminf_le_liminf_of_le hz
    _ = Filter.liminf (fun n ↦ h (z n)) Filter.atTop := by
      rw [← Filter.liminf_comp]
      rfl

/-- Helper for Theorem 11.12: an eventual upper bound by a constant forces the `liminf` to stay
below that same constant. -/
private lemma liminf_le_constant_of_eventually_le_ereal
    {u : ℕ → EReal} {c : EReal} (huc : ∀ᶠ k in Filter.atTop, u k ≤ c) :
    Filter.liminf u Filter.atTop ≤ c := by
  exact Filter.liminf_le_of_le (f := Filter.atTop) (u := u) (a := c) (hf := by isBoundedDefault)
    fun b hb ↦ by
    rcases (hb.and huc).exists with ⟨k, hbk, hkc⟩
    exact le_trans hbk hkc

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

section

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}
variable [Nonempty (Fin p)]

variable (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

/- Theorem 11.12 is `source-facing`: it states asymptotic properties of the CBPG outer sequence.
Domain sampling against the surrounding Chapter 11 files identifies the relevant owner
abstractions:
- `IsBlockProximalGradientProblem.interior_effective_domain_point` from Definition 11.4 is the
  canonical bridge from the primitive initial datum `x0 ∈ effective_domain (separableSum g)` to
  the initial interior-domain point needed by the CBPG iterate owner;
- `IsBlockProximalGradientProblem.gradient_mapping`, used through the owner notation
  `G[L; hproblem.toIsBlockProximalGradientProblem]`, is the canonical Chapter 11 residual owner
  attached to the block data;
- `cyclic_block_proximal_gradient_method` from Algorithm 11.4 is the owner of the outer-iterate
  sequence;
- the textbook constants `L_min` and `L_max` are written below by their finite infimum/supremum
  formulas on the block stepsize family `i ↦ L_i`; the coefficient `C` from Theorem 11.12 is
  then expressed by its explicit textbook formula without importing the proof-heavy
  sufficient-decrease file.

Layer triage:
- `source-facing`: the vanishing-residual, best-residual, and cluster-point stationarity
  consequences below;
- `core/canonical`: the effective-domain initial datum together with the canonical bridge
  `x0 ↦ x0I`;
- `bridge/view`: any proof-level passage between this residual tuple and equivalent full-gradient
  presentations. -/

local notation "x0I" => hproblem.interior_effective_domain_point x0
local notation "x[" k "]" =>
  cyclic_block_proximal_gradient_method hproblem x0I k
local notation "hcore" => hproblem.toIsBlockProximalGradientProblem
local notation "Lmin" => cbpg_min_block_stepsize Li
local notation "F" => composite_model_objective f (separableSum g)
local notation "Ccbpg" => cbpg_sufficient_decrease_constant Lf Li
local notation "toPiLp" =>
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
set_option quotPrecheck false in
local notation "Gcbpg" =>
  fun k ↦ toPiLp (fun i ↦ G[Lmin; hcore] x[k] i)
local notation "Rcbpg" =>
  fun k ↦ best_achieved_function_value (fun y ↦ ‖y‖) Gcbpg k

omit [Nonempty (Fin p)] in
/-- Helper for Theorem 11.12: every outer CBPG iterate remains in the effective domain of the
block-separable regularizer. -/
private lemma cbpg_outer_iterate_mem_effective_domain
    (k : ℕ) :
    x[k] ∈ effective_domain (separableSum g) := by
  -- The outer iterate is the zeroth auxiliary stage in the cyclic owner recursion.
  simpa using cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k 0 (Nat.zero_le p)

/-- Helper for Theorem 11.12: rewriting the Chapter 11 sufficient-decrease inequality through the
finite objective-gap identity yields the real-layer estimate used in clauses (a) and (b). -/
lemma cbpg_real_sufficient_decrease_gradient_mapping
    (k : ℕ) :
    (Ccbpg / (p : ℝ)) * ‖Gcbpg k‖ ^ (2 : ℕ) ≤
      (F x[k]).toReal - (F x[k + 1]).toReal := by
  -- Convert the owner-level `EReal` sufficient-decrease bound to a real inequality in one step.
  have hstep :
      ((((Ccbpg / (p : ℝ)) * ‖Gcbpg k‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
        F x[k] - F x[k + 1] := by
    simpa using cbpg_sufficient_decrease_gradient_mapping hproblem x0 k
  rw [cbpg_objective_gap_eq_coe_toReal_sub hproblem x0 k] at hstep
  exact EReal.coe_le_coe_iff.mp hstep

/-- Helper for Theorem 11.12: the squared running-best residual on a prefix is bounded above by
the sum of the squared residuals on that prefix. -/
lemma cbpg_best_gradient_mapping_sq_mul_prefix_length_le_sum
    (k : ℕ) :
    (k + 1 : ℝ) * Rcbpg k ^ (2 : ℕ) ≤
      Finset.sum (Finset.range (k + 1))
        (fun n ↦ ‖Gcbpg n‖ ^ (2 : ℕ)) := by
  have hbest_nonneg : 0 ≤ Rcbpg k := by
    -- The running minimum is attained by one prefix residual norm and is therefore nonnegative.
    change 0 ≤ best_achieved_function_value (fun y ↦ ‖y‖) Gcbpg k
    unfold best_achieved_function_value
    have hmem :=
      Finset.min'_mem
        ((Finset.range (k + 1)).image fun n ↦ ‖Gcbpg n‖)
        (objective_value_prefix_nonempty (fun y ↦ ‖y‖) Gcbpg k)
    rcases Finset.mem_image.mp hmem with ⟨n, _, hn⟩
    rw [← hn]
    exact norm_nonneg _
  have hpointwise :
      ∀ n ∈ Finset.range (k + 1),
        Rcbpg k ^ (2 : ℕ) ≤ ‖Gcbpg n‖ ^ (2 : ℕ) := by
    intro n hn
    have hbest_le :=
      best_achieved_function_value_le_objective_value
        (f := fun y ↦ ‖y‖) Gcbpg k n hn
    nlinarith [hbest_nonneg, norm_nonneg (Gcbpg n), hbest_le]
  -- Summing the pointwise lower bound across the whole prefix gives the structural estimate.
  calc
    (k + 1 : ℝ) * Rcbpg k ^ (2 : ℕ) =
        Finset.sum (Finset.range (k + 1)) (fun _ ↦ Rcbpg k ^ (2 : ℕ)) := by
      simp
    _ ≤ Finset.sum (Finset.range (k + 1))
          (fun n ↦ ‖Gcbpg n‖ ^ (2 : ℕ)) := by
      exact Finset.sum_le_sum hpointwise

-- Proof sketch: combine the Chapter 11 sufficient-decrease estimate with monotonicity of the
-- `‖toPiLp (G_{L_min}(x^k))‖² / p`. Since `F(x^k)` is nonincreasing and bounded below by
-- `F_opt`, the consecutive differences tend to `0`, forcing the canonical block `L²` residual
-- sequence to converge to `0`.
/-- Theorem 11.12 (1): clause (a). Under Assumption 11.1, the Chapter 11 residual tuple
`i ↦ G^i_{L_min}(x^k)`, viewed in the canonical block `L²` owner `PiLp (2 : ENNReal) Ei`,
converges to `0` along the outer iterates. -/
theorem cbpg_gradient_mapping_tendsto_zero :
    Filter.Tendsto Gcbpg Filter.atTop (nhds 0) := by
  let φ : ℕ → ℝ := fun k ↦ (F x[k]).toReal
  have hanti : Antitone φ := by
    -- The composite objective is monotone in `EReal`, so its finite real representatives are
    -- antitone as well.
    refine antitone_nat_of_succ_le ?_
    intro k
    exact
      EReal.toReal_le_toReal
        (cbpg_objective_step_monotone hproblem x0 k)
        (cbpg_objective_value_finite hproblem x0 (k + 1)).2
        (cbpg_objective_value_finite hproblem x0 k).1
  have hbelow : BddBelow (Set.range φ) := by
    refine ⟨FOpt, ?_⟩
    intro y hy
    rcases hy with ⟨k, rfl⟩
    exact
      EReal.toReal_le_toReal
        (hproblem.optimal_value_isGLB.1 ⟨x[k], rfl⟩)
        (by simp)
        (cbpg_objective_value_finite hproblem x0 k).1
  have hgap_tendsto_zero :
      Filter.Tendsto
        (fun k ↦ (F x[k]).toReal - (F x[k + 1]).toReal)
        Filter.atTop
        (nhds 0) :=
    objective_gap_tendsto_zero_of_antitone_bddBelow hanti hbelow
  have hconst_pos : 0 < Ccbpg / (p : ℝ) := by
    have hC_pos : 0 < Ccbpg := by
      let A : ℝ :=
        (Lf : ℝ) +
          2 * ((cbpg_max_block_stepsize Li : PosReal) : ℝ) +
            Real.sqrt
              (((cbpg_min_block_stepsize Li : PosReal) : ℝ) *
                ((cbpg_max_block_stepsize Li : PosReal) : ℝ))
      have hA_pos : 0 < A := by
        have hLf_nonneg : 0 ≤ (Lf : ℝ) := by positivity
        have hLmax_pos : 0 < ((cbpg_max_block_stepsize Li : PosReal) : ℝ) :=
          PosReal.coe_pos (cbpg_max_block_stepsize Li)
        have hsqrt_nonneg :
            0 ≤
              Real.sqrt
                (((cbpg_min_block_stepsize Li : PosReal) : ℝ) *
                  ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) :=
          Real.sqrt_nonneg _
        dsimp [A]
        linarith
      rw [cbpg_sufficient_decrease_constant_def]
      have hden_pos : 0 < 2 * A ^ (2 : ℕ) := by
        positivity
      simpa [A] using
        div_pos (PosReal.coe_pos (cbpg_min_block_stepsize Li)) hden_pos
    have hp_pos : 0 < (p : ℝ) := by
      simpa [Fintype.card_fin] using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin p)›)
    exact div_pos hC_pos hp_pos
  have hscaled_tendsto_zero :
      Filter.Tendsto
        (fun k ↦ (Ccbpg / (p : ℝ)) * ‖Gcbpg k‖ ^ (2 : ℕ))
        Filter.atTop
        (nhds 0) := by
    -- The scaled squared residuals are squeezed between `0` and the vanishing objective gaps.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hgap_tendsto_zero
      ?_
      ?_
    · intro k
      exact mul_nonneg (le_of_lt hconst_pos) (sq_nonneg ‖Gcbpg k‖)
    · intro k
      exact cbpg_real_sufficient_decrease_gradient_mapping hproblem x0 k
  -- A positive coefficient in front of `‖Gcbpg k‖²` can be cancelled after taking square roots.
  exact tendsto_zero_of_scaled_sq_norm_tendsto_zero hconst_pos hscaled_tendsto_zero

-- Proof sketch: sum the sufficient-decrease inequality over `n = 0, ..., k`,
-- telescope the objective values, bound the sum below by `(k + 1)` times the squared running
-- minimum of the canonical block `L²` residual norms, and then clear square roots to obtain the
-- source-facing rate.
/-- Theorem 11.12 (2): clause (b). The running minimum of
`‖toPiLp (i ↦ G^i_{L_min}(x^n))‖` over `0 ≤ n ≤ k` satisfies the textbook complexity estimate
`min_{0 ≤ n ≤ k} ‖toPiLp (i ↦ G^i_{L_min}(x^n))‖ ≤
sqrt (p (F(x^0) - F_opt)) / sqrt (C (k + 1))`. -/
theorem cbpg_best_gradient_mapping_norm_le_rate
    (k : ℕ) :
    Rcbpg k ≤
      Real.sqrt ((p : ℝ) * ((F x0).toReal - FOpt)) /
        Real.sqrt (Ccbpg * (k + 1 : ℝ)) := by
  have hC_pos : 0 < Ccbpg := by
    let A : ℝ :=
      (Lf : ℝ) +
        2 * ((cbpg_max_block_stepsize Li : PosReal) : ℝ) +
          Real.sqrt
            (((cbpg_min_block_stepsize Li : PosReal) : ℝ) *
              ((cbpg_max_block_stepsize Li : PosReal) : ℝ))
    have hA_pos : 0 < A := by
      have hLf_nonneg : 0 ≤ (Lf : ℝ) := by positivity
      have hLmax_pos : 0 < ((cbpg_max_block_stepsize Li : PosReal) : ℝ) :=
        PosReal.coe_pos (cbpg_max_block_stepsize Li)
      have hsqrt_nonneg :
          0 ≤
            Real.sqrt
              (((cbpg_min_block_stepsize Li : PosReal) : ℝ) *
                ((cbpg_max_block_stepsize Li : PosReal) : ℝ)) :=
        Real.sqrt_nonneg _
      dsimp [A]
      linarith
    rw [cbpg_sufficient_decrease_constant_def]
    have hden_pos : 0 < 2 * A ^ (2 : ℕ) := by
      positivity
    simpa [A] using
      div_pos (PosReal.coe_pos (cbpg_min_block_stepsize Li)) hden_pos
  have hp_pos : 0 < (p : ℝ) := by
    simpa [Fintype.card_fin] using (Fintype.card_pos_iff.mpr ‹Nonempty (Fin p)›)
  have hsum_decrease :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ (Ccbpg / (p : ℝ)) * ‖Gcbpg n‖ ^ (2 : ℕ)) ≤
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ (F x[n]).toReal - (F x[n + 1]).toReal) := by
    -- Sum the real sufficient-decrease estimate over the whole prefix.
    refine Finset.sum_le_sum ?_
    intro n hn
    exact cbpg_real_sufficient_decrease_gradient_mapping hproblem x0 n
  have htail_ge :
      FOpt ≤ (F x[k + 1]).toReal := by
    exact
      EReal.toReal_le_toReal
        (hproblem.optimal_value_isGLB.1 ⟨x[k + 1], rfl⟩)
        (by simp)
        (cbpg_objective_value_finite hproblem x0 (k + 1)).1
  have hprefix_best :
      (Ccbpg / (p : ℝ)) * ((k + 1 : ℝ) * Rcbpg k ^ (2 : ℕ)) ≤
        (F x[0]).toReal - FOpt := by
    have hprefix_best_to_tail :
        (Ccbpg / (p : ℝ)) * ((k + 1 : ℝ) * Rcbpg k ^ (2 : ℕ)) ≤
          (F x[0]).toReal - (F x[k + 1]).toReal := by
      -- Combine the running-best bound with the telescoping sufficient-decrease sum.
      calc
        (Ccbpg / (p : ℝ)) * ((k + 1 : ℝ) * Rcbpg k ^ (2 : ℕ)) ≤
            (Ccbpg / (p : ℝ)) *
              Finset.sum (Finset.range (k + 1))
                (fun n ↦ ‖Gcbpg n‖ ^ (2 : ℕ)) := by
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_left
              (cbpg_best_gradient_mapping_sq_mul_prefix_length_le_sum hproblem x0 k)
              (le_of_lt (div_pos hC_pos hp_pos)))
        _ = Finset.sum (Finset.range (k + 1))
              (fun n ↦ (Ccbpg / (p : ℝ)) * ‖Gcbpg n‖ ^ (2 : ℕ)) := by
          rw [Finset.mul_sum]
        _ ≤ Finset.sum (Finset.range (k + 1))
              (fun n ↦ (F x[n]).toReal - (F x[n + 1]).toReal) := hsum_decrease
        _ = (F x[0]).toReal - (F x[k + 1]).toReal := by
          simpa using proximal_gradient_real_objective_telescope
            (fun n ↦ (F x[n]).toReal) k
    nlinarith
  have hsq_gap :
      Ccbpg * ((k + 1 : ℝ) * Rcbpg k ^ (2 : ℕ)) ≤
        (p : ℝ) * ((F x0).toReal - FOpt) := by
    -- Multiply the prefix estimate by `p` to match the textbook numerator and denominator.
    calc
      Ccbpg * ((k + 1 : ℝ) * Rcbpg k ^ (2 : ℕ)) =
          (p : ℝ) * ((Ccbpg / (p : ℝ)) * ((k + 1 : ℝ) * Rcbpg k ^ (2 : ℕ))) := by
        field_simp [hp_pos.ne']
      _ ≤ (p : ℝ) * ((F x0).toReal - FOpt) := by
        exact mul_le_mul_of_nonneg_left hprefix_best (le_of_lt hp_pos)
  have hbest_nonneg : 0 ≤ Rcbpg k := by
    change 0 ≤ best_achieved_function_value (fun y ↦ ‖y‖) Gcbpg k
    unfold best_achieved_function_value
    have hmem :=
      Finset.min'_mem
        ((Finset.range (k + 1)).image fun n ↦ ‖Gcbpg n‖)
        (objective_value_prefix_nonempty (fun y ↦ ‖y‖) Gcbpg k)
    rcases Finset.mem_image.mp hmem with ⟨n, _, hn⟩
    rw [← hn]
    exact norm_nonneg _
  have hgap_nonneg : 0 ≤ (p : ℝ) * ((F x0).toReal - FOpt) := by
    have hbase_nonneg : 0 ≤ (F x0).toReal - FOpt := by
      exact sub_nonneg.mpr <|
        EReal.toReal_le_toReal
          (hproblem.optimal_value_isGLB.1 ⟨x[0], rfl⟩)
          (by simp)
          (cbpg_objective_value_finite hproblem x0 0).1
    exact mul_nonneg (le_of_lt hp_pos) hbase_nonneg
  have hden_pos : 0 < Ccbpg * (k + 1 : ℝ) := by
    exact mul_pos hC_pos (by positivity)
  -- Route correction: isolate the squared estimate first, then take square roots in one step.
  rw [le_div_iff₀ (Real.sqrt_pos.2 hden_pos)]
  have hsqrt_den_sq :
      Real.sqrt (Ccbpg * (k + 1 : ℝ)) ^ (2 : ℕ) = Ccbpg * (k + 1 : ℝ) := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hden_pos)
  have hsqrt_gap_sq :
      Real.sqrt ((p : ℝ) * ((F x0).toReal - FOpt)) ^ (2 : ℕ) =
        (p : ℝ) * ((F x0).toReal - FOpt) := by
    simpa [pow_two] using Real.sq_sqrt hgap_nonneg
  have hsq :
      (Rcbpg k * Real.sqrt (Ccbpg * (k + 1 : ℝ))) ^ (2 : ℕ) ≤
        Real.sqrt ((p : ℝ) * ((F x0).toReal - FOpt)) ^ (2 : ℕ) := by
    -- Squaring both sides reduces the claimed rate to the already established prefix inequality.
    nlinarith [hsq_gap, hsqrt_den_sq, hsqrt_gap_sq]
  have hleft_nonneg : 0 ≤ Rcbpg k * Real.sqrt (Ccbpg * (k + 1 : ℝ)) := by
    exact mul_nonneg hbest_nonneg (Real.sqrt_nonneg _)
  have hright_nonneg : 0 ≤ Real.sqrt ((p : ℝ) * ((F x0).toReal - FOpt)) := by
    exact Real.sqrt_nonneg _
  -- Nonnegativity lets the squared comparison recover the displayed rate bound.
  nlinarith [hsq, hleft_nonneg, hright_nonneg]

end

section

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}
variable [Nonempty (Fin p)]
variable [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
variable [FiniteDimensional ℝ ((i : Fin p) → Ei i)]

instance : ProperSpace ((i : Fin p) → Ei i) := by
  infer_instance

variable (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

local notation "x0I" => hproblem.interior_effective_domain_point x0
local notation "xSeq" => cyclic_block_proximal_gradient_method hproblem x0I
local notation "x[" k "]" =>
  cyclic_block_proximal_gradient_method hproblem x0I k
local notation "hcore" => hproblem.toIsBlockProximalGradientProblem
local notation "Lmin" => cbpg_min_block_stepsize Li
local notation "toPiLp" =>
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
local notation "F" => composite_model_objective f (separableSum g)
set_option quotPrecheck false in
local notation "Gcbpg" =>
  fun k ↦ toPiLp (fun i ↦ G[Lmin; hcore] x[k] i)
local instance theorem11_12_decidableEqFin : DecidableEq (Fin p) := Classical.decEq _

-- Proof sketch: apply Theorem 11.1 with the constant block stepsize family
-- `M i = cbpg_min_block_stepsize Li`. Along a subsequence `x^{k_j} → xBar`, clause (1) gives
-- the vanishing of the Chapter 11 block owner `G^i_{L_min}(x^{k_j})` for every block `i`; the
-- block-Lipschitz data in `hproblem` lets these one-block residuals pass to the limit at `xBar`,
-- yielding `G^i_{L_min}(xBar) = 0` for all `i`, which is exactly the stationarity criterion from
-- Theorem 11.1.
omit [Nonempty (Fin p)] [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
  [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 11.12: a cluster point of the CBPG outer sequence remains in the effective
domain of the block-separable regularizer because the full objective `F = f + separableSum g` is
lower semicontinuous and all iterate objective values stay below the finite initial value. -/
lemma cbpg_cluster_point_mem_effective_domain
    {xBar : (i : Fin p) → Ei i}
    (hxBar : MapClusterPt xBar Filter.atTop xSeq) :
    xBar ∈ effective_domain (separableSum g) := by
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hxBar
  have hF_closed : LowerSemicontinuous F := by
    -- Lower semicontinuity of `f` and `separableSum g` combines to the full objective.
    refine hproblem.f_closed.add' hproblem.separableSum_closed ?_
    intro z
    exact
      EReal.continuousAt_add
        (.inr ((separableSum_proper g hproblem.block_g_proper).ne_bot z))
        (.inl (hproblem.f_ne_bot z))
  have hanti : Antitone (fun k ↦ F x[k]) := by
    -- The one-step monotonicity owner upgrades to an antitone objective sequence.
    refine antitone_nat_of_succ_le ?_
    intro k
    exact cbpg_objective_step_monotone hproblem x0 k
  have hxBar_obj :
      F xBar ≤ Filter.liminf (fun n ↦ F x[ψ n]) Filter.atTop :=
    lowerSemicontinuous_value_le_liminf_along_sequence
      (h := F)
      hF_closed
      hψtendsto
  have hliminf_le :
      Filter.liminf (fun n ↦ F x[ψ n]) Filter.atTop ≤ F x[0] := by
    refine liminf_le_constant_of_eventually_le_ereal ?_
    exact Filter.Eventually.of_forall fun n ↦ hanti (Nat.zero_le (ψ n))
  have hxBar_obj_finite :
      F xBar < ⊤ := by
    -- The lower-semicontinuity bound keeps the cluster-point objective below the finite initial
    -- value.
    exact
      lt_of_le_of_lt
        (le_trans hxBar_obj hliminf_le)
        (lt_top_iff_ne_top.mpr (cbpg_objective_value_finite hproblem x0 0).1)
  have hsum_ne_top : separableSum g xBar ≠ ⊤ := by
    intro htop
    have hF_top : F xBar = ⊤ := by
      calc
        F xBar = f xBar + separableSum g xBar := by
          rw [composite_model_objective_apply]
        _ = f xBar + ⊤ := by rw [htop]
        _ = ⊤ := EReal.add_top_of_ne_bot (hproblem.f_ne_bot xBar)
    simp [hF_top] at hxBar_obj_finite
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hsum_ne_top)

omit [Nonempty (Fin p)] [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
  [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 11.12: on the interior effective domain, the block residual satisfies the
textbook continuity estimate
`‖G^i_M(x) - G^i_M(y)‖ ≤ (2 M + L_f) ‖x - y‖` when distances are measured in the canonical
transported `PiLp` norm. -/
lemma cbpg_partial_gradient_mapping_difference_le_textbook_rhs
    (M : PosReal) (i : Fin p)
    {x y : (j : Fin p) → Ei j}
    (hx : x ∈ interior (effective_domain f))
    (hy : y ∈ interior (effective_domain f)) :
    ‖G[M; hcore] x i - G[M; hcore] y i‖ ≤
      (((2 : ℝ) * (M : ℝ)) + (Lf : ℝ)) * ‖toPiLp x - toPiLp y‖ := by
  let zx : Ei i := x i - (1 / (M : ℝ)) • block_gradient i x
  let zy : Ei i := y i - (1 / (M : ℝ)) • block_gradient i y
  let ux : Ei i := IsBlockProximalGradientProblem.prox_point hcore M i x
  let uy : Ei i := IsBlockProximalGradientProblem.prox_point hcore M i y
  have hscaled :=
    scaled_function_proper_closed_convex_of_pos
      (g i)
      (hproblem.block_g_proper i)
      (hproblem.block_g_closed i)
      (hproblem.block_g_convex i)
      (1 / M)
  have hprox_x :
      prox[((((1 / M : PosReal) : EReal) • g i))] zx = {ux} := by
    -- Expand the owner-level prox point at `x` back to the singleton prox set.
    simpa [zx, ux] using
      IsBlockProximalGradientProblem.prox_point_eq_singleton hcore M i x
  have hprox_y :
      prox[((((1 / M : PosReal) : EReal) • g i))] zy = {uy} := by
    -- The same singleton prox description holds at `y`.
    simpa [zy, uy] using
      IsBlockProximalGradientProblem.prox_point_eq_singleton hcore M i y
  have hprox_nonexp :
      ‖ux - uy‖ ≤ ‖zx - zy‖ := by
    -- Proximal nonexpansiveness controls the prox-point drift by the forward-point drift.
    exact
      prox_eq_singleton_nonexpansive
        (f := ((((1 / M : PosReal) : EReal) • g i)))
        zx
        zy
        ux
        uy
        hscaled.1
        hscaled.2.1
        hscaled.2.2
        hprox_x
        hprox_y
  have hcoord :
      ‖x i - y i‖ ≤ ‖toPiLp x - toPiLp y‖ := by
    -- Each block coordinate is dominated by the transported `PiLp` norm.
    simpa [map_sub, PiLp.coe_symm_continuousLinearEquiv] using
      (PiLp.norm_apply_le (toPiLp x - toPiLp y) i)
  have hblock :
      ‖block_gradient i x - block_gradient i y‖ ≤
        (Lf : ℝ) * ‖toPiLp x - toPiLp y‖ :=
    cbpg_block_gradient_difference_le_lf_mul_toPiLp_norm
      hproblem
      i
      x
      y
      hx
      hy
  have hforward :
      ‖zx - zy‖ ≤
        ‖x i - y i‖ + (1 / (M : ℝ)) * ‖block_gradient i x - block_gradient i y‖ := by
    have hrepr :
        zx - zy =
          (x i - y i) -
            (1 / (M : ℝ)) • (block_gradient i x - block_gradient i y) := by
      dsimp [zx, zy]
      rw [smul_sub]
      abel
    rw [hrepr]
    calc
      ‖(x i - y i) - (1 / (M : ℝ)) • (block_gradient i x - block_gradient i y)‖
          ≤ ‖x i - y i‖ + ‖(1 / (M : ℝ)) • (block_gradient i x - block_gradient i y)‖ := by
            exact norm_sub_le _ _
      _ = ‖x i - y i‖ + (1 / (M : ℝ)) * ‖block_gradient i x - block_gradient i y‖ := by
            have hMinv_nonneg : 0 ≤ (1 / (M : ℝ)) := by
              exact le_of_lt (one_div_pos.mpr M.2)
            rw [norm_smul, Real.norm_of_nonneg hMinv_nonneg]
  have hgrad_map :
      G[M; hcore] x i - G[M; hcore] y i =
        (M : ℝ) • ((x i - y i) - (ux - uy)) := by
    -- Rewrite both residuals by their defining prox-point formulas and collect terms.
    calc
      G[M; hcore] x i - G[M; hcore] y i =
          (M : ℝ) • (x i - ux) - (M : ℝ) • (y i - uy) := by
        rw [IsBlockProximalGradientProblem.gradient_mapping_def hcore M x i,
          IsBlockProximalGradientProblem.gradient_mapping_def hcore M y i]
      _ = (M : ℝ) • ((x i - ux) - (y i - uy)) := by
        rw [← smul_sub]
      _ = (M : ℝ) • ((x i - y i) - (ux - uy)) := by
        congr 1
        abel
  have hM_nonneg : 0 ≤ (M : ℝ) := le_of_lt M.2
  have hM_ne : (M : ℝ) ≠ 0 := ne_of_gt M.2
  have hfirst :
      ‖G[M; hcore] x i - G[M; hcore] y i‖ ≤
        (M : ℝ) * (‖x i - y i‖ + ‖ux - uy‖) := by
    calc
      ‖G[M; hcore] x i - G[M; hcore] y i‖ =
          ‖(M : ℝ) • ((x i - y i) - (ux - uy))‖ := by
        rw [hgrad_map]
      _ = (M : ℝ) * ‖(x i - y i) - (ux - uy)‖ := by
        rw [norm_smul, Real.norm_of_nonneg hM_nonneg]
      _ ≤ (M : ℝ) * (‖x i - y i‖ + ‖ux - uy‖) := by
        gcongr
        exact norm_sub_le _ _
  have hsecond :
      ‖G[M; hcore] x i - G[M; hcore] y i‖ ≤
        (M : ℝ) *
          (‖x i - y i‖ +
            (‖x i - y i‖ + (1 / (M : ℝ)) * ‖block_gradient i x - block_gradient i y‖)) := by
    refine hfirst.trans ?_
    gcongr
    exact hprox_nonexp.trans hforward
  calc
    ‖G[M; hcore] x i - G[M; hcore] y i‖ ≤
        (M : ℝ) *
          (‖x i - y i‖ +
            (‖x i - y i‖ + (1 / (M : ℝ)) * ‖block_gradient i x - block_gradient i y‖)) := hsecond
    _ = ((2 : ℝ) * (M : ℝ)) * ‖x i - y i‖ + ‖block_gradient i x - block_gradient i y‖ := by
      field_simp [hM_ne]
      ring
    _ ≤ ((2 : ℝ) * (M : ℝ)) * ‖toPiLp x - toPiLp y‖ + (Lf : ℝ) * ‖toPiLp x - toPiLp y‖ := by
      gcongr
    _ = (((2 : ℝ) * (M : ℝ)) + (Lf : ℝ)) * ‖toPiLp x - toPiLp y‖ := by
      ring

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
  [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 11.12: once a cluster point is known to remain feasible, the blockwise
residuals vanish there by passing clause (1) to the subsequence limit through the textbook
continuity estimate. -/
lemma coordinate_residual_tendsto_zero_of_pilp_residual_tendsto_zero
    {ψ : ℕ → ℕ}
    (hψmono : StrictMono ψ) :
    ∀ i : Fin p,
      Filter.Tendsto
        (fun n ↦ G[Lmin; hcore] x[ψ n] i)
        Filter.atTop
        (nhds 0) := by
  intro i
  have hsubseq :
      Filter.Tendsto (fun n ↦ Gcbpg (ψ n)) Filter.atTop (nhds 0) := by
    -- Clause (1) is stable under passage to the cluster subsequence.
    exact
      (cbpg_gradient_mapping_tendsto_zero (hproblem := hproblem) (x0 := x0)).comp
        hψmono.tendsto_atTop
  have hnorm :
      Filter.Tendsto (fun n ↦ ‖Gcbpg (ψ n)‖) Filter.atTop (nhds 0) := by
    simpa using hsubseq.norm
  have hcoord_norm :
      Filter.Tendsto
        (fun n ↦ ‖G[Lmin; hcore] x[ψ n] i‖)
        Filter.atTop
        (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hnorm
      ?_
      ?_
    · intro n
      exact norm_nonneg _
    · intro n
      change ‖G[Lmin; hcore] x[ψ n] i‖ ≤ ‖Gcbpg (ψ n)‖
      simpa [PiLp.coe_symm_continuousLinearEquiv] using
        (PiLp.norm_apply_le (Gcbpg (ψ n)) i)
  -- Coordinate norms are dominated by the `PiLp` norm, so the block residual itself tends to `0`.
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  simpa using hcoord_norm

omit [∀ i, ProperSpace (Ei i)] [Nonempty (Fin p)]
  [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
  [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 11.12: transporting a raw interior-domain point through the canonical
`toPiLp` equivalence preserves membership in the ambient `PiLp` interior effective domain
`interior (effective_domain (fun z ↦ f z))`. -/
lemma toPiLp_mem_interior_effective_domain
    {x : (i : Fin p) → Ei i}
    (hx : x ∈ interior (effective_domain f)) :
    (WithLp.toLp 2 x : PiLp 2 Ei) ∈
      interior (effective_domain (fun z : PiLp 2 Ei ↦ f z)) := by
  let e : ((i : Fin p) → Ei i) ≃L[ℝ] PiLp 2 Ei :=
    ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
  have heff :
      e '' effective_domain f =
        effective_domain (fun z : PiLp 2 Ei ↦ f z) := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [e, effective_domain, mem_effective_domain, PiLp.coe_symm_continuousLinearEquiv]
        using hy
    · intro hz
      refine ⟨(PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei) z, ?_, ?_⟩
      · simpa [effective_domain, mem_effective_domain, PiLp.coe_continuousLinearEquiv] using hz
      · simp [e]
  have hinterior :
      e '' interior (effective_domain f) = interior (e '' effective_domain f) := by
    simpa [e] using e.toHomeomorph.image_interior (effective_domain f)
  have hx_image :
      (WithLp.toLp 2 x : PiLp 2 Ei) ∈ e '' interior (effective_domain f) := by
    exact ⟨x, hx, rfl⟩
  rw [hinterior, heff] at hx_image
  simpa using hx_image

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)] in
/-- Helper for Theorem 11.12: blockwise vanishing of the Chapter 11 residuals forces vanishing of
the aggregate Chapter 10 gradient mapping on the canonical `PiLp` owner. -/
lemma aggregate_gradient_mapping_eq_zero_of_block_zero
    {x : (i : Fin p) → Ei i}
    (hx : x ∈ effective_domain (separableSum g))
    (hzero : ∀ i : Fin p, G[Lmin; hcore] x i = 0) :
    hproblem.aggregate_gradient_mapping Lmin (WithLp.toLp 2 x) = 0 := by
  letI : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li := hproblem
  letI : FiniteDimensional ℝ (PiLp 2 Ei) :=
    FiniteDimensional.of_injective
      (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).toLinearMap
      (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei).injective
  letI : ProperSpace (PiLp 2 Ei) := by
    infer_instance
  have hx_int :
      x ∈ interior (effective_domain f) :=
    IsBlockProximalGradientProblem.mem_interior_effective_domain_of_mem_g_effective_domain
      hcore
      hx
  -- The canonical Lemma 11.1 tuple identity turns blockwise zero residuals into aggregate zero.
  calc
    hproblem.aggregate_gradient_mapping Lmin (WithLp.toLp 2 x) =
        WithLp.toLp 2 (fun i ↦ G[Lmin; hcore] x i) := by
      simpa using
        (BlockProximalGradientAssumptions.gradient_mapping_eq_block_partial_gradient_mapping_tuple
          (hproblem := hproblem)
          Lmin
          x
          hx_int)
    _ = 0 := by
      ext i
      simpa [IsBlockProximalGradientProblem.gradient_mapping_def] using hzero i

/-- Helper for Theorem 11.12: if every block residual vanishes at a feasible point, then the
point is stationary for the CBPG composite model. -/
lemma cbpg_block_residual_zero_implies_stationary
    {x : (i : Fin p) → Ei i}
    (hx : x ∈ effective_domain (separableSum g))
    (hzero : ∀ i : Fin p, G[Lmin; hcore] x i = 0) :
    @is_stationary_point
      ((i : Fin p) → Ei i)
      _ _ (rawTupleFiniteDimensional (ι := Fin p) (Ei := Ei))
      f
      (separableSum g)
      x := by
  -- Reuse the Chapter 11 stationarity criterion instead of rebuilding the raw-dual decomposition.
  exact
    (is_stationary_point_iff_coordinatewise_negative_block_gradient_mem_euclideanSubdifferential
      (f := f)
      (g := g)
      (block_gradient := block_gradient)
      hproblem.f_proper
      hproblem.block_g_proper
      hproblem.block_g_closed
      hproblem.block_g_convex
      hproblem.f_closed
      hproblem.f_effective_domain_convex
      hproblem.g_effective_domain_subset_interior_f_effective_domain
      hproblem.f_toReal_differentiableOn_interior_effective_domain
      hproblem.block_partial_gradient_spec
      x).2
      (fun i ↦
        (blockResidual_eq_zero_iff_negativeBlockGradient_memEuclideanSubdifferential
          hcore
          Lmin
          x
          i).1
          (hzero i))

omit [InnerProductSpace ℝ ((i : Fin p) → Ei i)]
  [FiniteDimensional ℝ ((i : Fin p) → Ei i)] in
lemma cbpg_cluster_limit_block_residual_eq_zero
    {xBar : (i : Fin p) → Ei i}
    (hxBar : MapClusterPt xBar Filter.atTop xSeq) :
    ∀ i : Fin p, G[Lmin; hcore] xBar i = 0
    := by
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hxBar
  have hxBar_g :
      xBar ∈ effective_domain (separableSum g) :=
    cbpg_cluster_point_mem_effective_domain (hproblem := hproblem) (x0 := x0) hxBar
  have hxBar_int :
      xBar ∈ interior (effective_domain f) :=
    IsBlockProximalGradientProblem.mem_interior_effective_domain_of_mem_g_effective_domain
      hcore
      hxBar_g
  have hcoord_zero :
      ∀ i : Fin p,
        Filter.Tendsto
          (fun n ↦ G[Lmin; hcore] x[ψ n] i)
          Filter.atTop
          (nhds 0) :=
    coordinate_residual_tendsto_zero_of_pilp_residual_tendsto_zero
      (hproblem := hproblem)
      (x0 := x0)
      hψmono
  have htoPiLp_tendsto :
      Filter.Tendsto (fun n ↦ toPiLp x[ψ n]) Filter.atTop (nhds (toPiLp xBar)) := by
    -- The cluster subsequence converges in the transported `PiLp` ambient model as well.
    exact
      ((ContinuousLinearEquiv.symm
          (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)).continuous.continuousAt.tendsto).comp
        hψtendsto
  intro i
  have hxpsi_int :
      ∀ n : ℕ, x[ψ n] ∈ interior (effective_domain f) := by
    intro n
    exact
      IsBlockProximalGradientProblem.mem_interior_effective_domain_of_mem_g_effective_domain
        hcore
        (cbpg_outer_iterate_mem_effective_domain (hproblem := hproblem) (x0 := x0) (ψ n))
  have hdrift_tendsto_zero :
      Filter.Tendsto
        (fun n ↦
          ((((2 : ℝ) * (Lmin : ℝ)) + (Lf : ℝ)) *
            ‖toPiLp xBar - toPiLp x[ψ n]‖))
        Filter.atTop
        (nhds 0) := by
    have hdiff_tendsto_zero :
        Filter.Tendsto
          (fun n ↦ toPiLp xBar - toPiLp x[ψ n])
          Filter.atTop
          (nhds 0) := by
      have hdiff :
          Filter.Tendsto
            (fun n ↦ toPiLp xBar - toPiLp x[ψ n])
            Filter.atTop
            (nhds (toPiLp xBar - toPiLp xBar)) := by
        exact tendsto_const_nhds.sub htoPiLp_tendsto
      simpa using hdiff
    have hnorm_tendsto_zero :
        Filter.Tendsto
          (fun n ↦ ‖toPiLp xBar - toPiLp x[ψ n]‖)
          Filter.atTop
          (nhds 0) := by
      simpa using hdiff_tendsto_zero.norm
    -- The continuity term vanishes because the cluster subsequence converges to `xBar`.
    simpa using hnorm_tendsto_zero.const_mul ((((2 : ℝ) * (Lmin : ℝ)) + (Lf : ℝ)))
  have hcoord_norm_tendsto_zero :
      Filter.Tendsto
        (fun n ↦ ‖G[Lmin; hcore] x[ψ n] i‖)
        Filter.atTop
        (nhds 0) := by
    -- The block residual itself tends to `0`, so its norm does as well.
    simpa using (hcoord_zero i).norm
  have hrhs_tendsto_zero :
      Filter.Tendsto
        (fun n ↦
          ((((2 : ℝ) * (Lmin : ℝ)) + (Lf : ℝ)) *
            ‖toPiLp xBar - toPiLp x[ψ n]‖) +
            ‖G[Lmin; hcore] x[ψ n] i‖)
        Filter.atTop
        (nhds 0) := by
    simpa using hdrift_tendsto_zero.add hcoord_norm_tendsto_zero
  have hconst_tendsto_zero :
      Filter.Tendsto (fun _ : ℕ ↦ ‖G[Lmin; hcore] xBar i‖) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds
      hrhs_tendsto_zero
      ?_
      ?_
    · intro n
      exact norm_nonneg _
    · intro n
      have hdist :
          ‖G[Lmin; hcore] xBar i - G[Lmin; hcore] x[ψ n] i‖ ≤
            ((((2 : ℝ) * (Lmin : ℝ)) + (Lf : ℝ)) *
              ‖toPiLp xBar - toPiLp x[ψ n]‖) := by
        simpa [norm_sub_rev] using
          cbpg_partial_gradient_mapping_difference_le_textbook_rhs
            (hproblem := hproblem)
            (M := Lmin)
            i
            (x := xBar)
            (y := x[ψ n])
            hxBar_int
            (hxpsi_int n)
      have htriangle :
          ‖G[Lmin; hcore] xBar i‖ ≤
            ‖G[Lmin; hcore] xBar i - G[Lmin; hcore] x[ψ n] i‖ +
              ‖G[Lmin; hcore] x[ψ n] i‖ := by
        -- Rewrite the residual at `xBar` as the sum of a drift term and the subsequence residual.
        simpa [sub_eq_add_neg, add_assoc] using
          (norm_add_le
            (G[Lmin; hcore] xBar i - G[Lmin; hcore] x[ψ n] i)
            (G[Lmin; hcore] x[ψ n] i))
      exact htriangle.trans <| by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right hdist ‖G[Lmin; hcore] x[ψ n] i‖
  have hnorm_zero :
      ‖G[Lmin; hcore] xBar i‖ = 0 := by
    exact tendsto_nhds_unique tendsto_const_nhds hconst_tendsto_zero
  exact norm_eq_zero.mp hnorm_zero

/-- Theorem 11.12 (3): clause (c). Every sequential limit point of the CBPG outer sequence is a
stationary point of the composite problem with smooth term `f` and block-separable regularizer
`x ↦ ∑ i, g_i(x_i)`. -/
theorem cbpg_cluster_point_is_stationary
    {xBar : (i : Fin p) → Ei i}
    (hxBar : MapClusterPt xBar Filter.atTop xSeq) :
    @is_stationary_point
      ((i : Fin p) → Ei i)
      _ _ (rawTupleFiniteDimensional (ι := Fin p) (Ei := Ei))
      f
      (separableSum g)
      xBar := by
  have hxBar_g :
      xBar ∈ effective_domain (separableSum g) :=
    cbpg_cluster_point_mem_effective_domain (hproblem := hproblem) (x0 := x0) hxBar
  have hzero :
      ∀ i : Fin p, G[Lmin; hcore] xBar i = 0 :=
    cbpg_cluster_limit_block_residual_eq_zero (hproblem := hproblem) (x0 := x0) hxBar
  -- The cluster-point residual vanishes blockwise, so the canonical stationary-point criterion
  -- closes the argument.
  exact
    cbpg_block_residual_zero_implies_stationary
      (hproblem := hproblem)
      hxBar_g
      hzero

end

end

end
