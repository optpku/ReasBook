/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Algorithm_11_4
import FirstOrderMethodsOptimization_Beck_2017.Chap11.Proposition_11_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped BigOperators Gradient

section

variable {p : ℕ} {Ei : Fin p → Type v}
variable [∀ i, NormedAddCommGroup (Ei i)] [∀ i, InnerProductSpace ℝ (Ei i)]
variable [∀ i, ProperSpace (Ei i)]

variable {f : ((i : Fin p) → Ei i) → EReal} {g : (i : Fin p) → Ei i → EReal}
variable {block_gradient : (i : Fin p) → ((j : Fin p) → Ei j) → Ei i}
variable {XStar : Set ((i : Fin p) → Ei i)} {FOpt : ℝ}
variable {Lf : NNReal} {Li : (i : Fin p) → PosReal}

/- Lemma 11.4 is a `bridge/view` file in the Chapter 11 CBPG domain.

Domain sampling against the surrounding owner declarations identifies:
- `cyclic_block_proximal_gradient_method` and
  `cyclic_block_proximal_gradient_inner_iterate` from Algorithm 11.4 as the iterate owners;
- the one-block sufficient-decrease owner from Lemma 11.3 as the source-faithful route for
  parts (a) and (b), once that upstream file is available in a compilable state;
- `PiLp (2 : ENNReal) Ei` together with `PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei` as the
  canonical Hilbert-product owner for the full-cycle norm in equation (11.11).

Primitive data here are only the Chapter 11 CBPG assumption package, the initial effective-domain
point, and the finite block-step family `Li`. The decrease statements below are derived API on the
CBPG iterates, so the public surface should reuse the block owner directly and keep the block
index at the canonical `Fin p` level rather than as a natural number plus a separate bound proof.
For the outer-step estimate, the norm must live on the canonical `L²` product owner rather than
on the raw dependent-function sup norm.
-/

section

variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The minimum block Lipschitz constant `L_min = min_i L_i` of a nonempty finite block family
`i ↦ L_i`. -/
def cbpg_min_block_stepsize (Li : ι → PosReal) : PosReal :=
  Finset.univ.inf' Finset.univ_nonempty Li

/-- The maximum block Lipschitz constant `L_max = max_i L_i` of a nonempty finite block family
`i ↦ L_i`. -/
def cbpg_max_block_stepsize (Li : ι → PosReal) : PosReal :=
  Finset.univ.sup' Finset.univ_nonempty Li

/-- Expanding `cbpg_max_block_stepsize` yields the finite maximum of the block constants
`i ↦ L_i`. -/
theorem cbpg_max_block_stepsize_def (Li : ι → PosReal) :
    cbpg_max_block_stepsize Li =
      Finset.univ.sup' Finset.univ_nonempty Li :=
  rfl

end

section

variable (hproblem : BlockProximalGradientAssumptions f g block_gradient XStar FOpt Lf Li)
variable (x0 : effective_domain (separableSum g))

local notation "F" => composite_model_objective f (separableSum g)
local notation "Lmin" => cbpg_min_block_stepsize Li
local notation "toPiLp" =>
  ContinuousLinearEquiv.symm (PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei)
local notation "x0'" => hproblem.interior_effective_domain_point x0
local notation "x[" k "]" =>
  cyclic_block_proximal_gradient_method hproblem x0' k
local notation "x[" k "," i "]" =>
  cyclic_block_proximal_gradient_inner_iterate hproblem x[k] i

/-- Helper for Lemma 11.4: a single auxiliary CBPG step changes only its active block in the raw
product coordinates. -/
lemma cbpg_stage_difference_single
    (k : ℕ) (j : Fin p) :
    x[k, j.1] - x[k, j.1 + 1] =
      Pi.single j (x[k, j.1] j - x[k, j.1 + 1] j) := by
  have hsucc :
      x[k, j.1 + 1] =
        block_coordinate_update
          x[k, j.1]
          j
          (hproblem.toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] -
            x[k, j.1] j) := by
    -- The next auxiliary stage is exactly the owner one-block update in block `j`.
    simpa [block_coordinate_update] using
      cyclic_block_proximal_gradient_method_inner_succ hproblem x0' k j.2
  -- Coordinatewise, only the active block contributes to the stage difference.
  rw [hsucc]
  ext i
  by_cases hij : i = j
  · subst i
    simp [block_coordinate_update]
  · simp [block_coordinate_update, hij]

/-- Helper for Lemma 11.4: the raw-product norm of one auxiliary step is exactly the norm of its
updated block difference. -/
lemma cbpg_auxiliary_step_norm_eq_block_norm
    (k : ℕ) (j : Fin p) :
    ‖x[k, j.1] - x[k, j.1 + 1]‖ =
      ‖x[k, j.1] j - x[k, j.1 + 1] j‖ := by
  -- A singleton raw-product vector has norm equal to the norm of its active entry.
  rw [cbpg_stage_difference_single hproblem x0 k j]
  simpa using (Pi.norm_single (x[k, j.1] j - x[k, j.1 + 1] j))

/-- Helper for Lemma 11.4: after transporting to the canonical `PiLp` product, a single auxiliary
step is still supported on only its active block. -/
lemma cbpg_stage_difference_toPiLp_single
    (k : ℕ) (j : Fin p) :
    toPiLp x[k, j.1] - toPiLp x[k, j.1 + 1] =
      PiLp.single (2 : ENNReal) j (x[k, j.1] j - x[k, j.1 + 1] j) := by
  have hsucc :
      x[k, j.1 + 1] =
        block_coordinate_update
          x[k, j.1]
          j
          (hproblem.toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] -
            x[k, j.1] j) := by
    -- Use the owner one-block update formula for the next auxiliary stage.
    simpa [block_coordinate_update] using
      cyclic_block_proximal_gradient_method_inner_succ hproblem x0' k j.2
  -- Transporting to `PiLp` preserves the same singleton support pattern.
  ext i
  rw [hsucc]
  by_cases hij : i = j
  · subst i
    simp [block_coordinate_update]
  · simp [block_coordinate_update, hij]

/-- Helper for Lemma 11.4: if the outer iterate `x^k` lies in the effective domain, then every
auxiliary inner stage `x^{k,m}` with `m ≤ p` also lies in the effective domain. -/
lemma cbpg_auxiliary_iterate_mem_effective_domain_of_outer_iterate
    (k : ℕ)
    (hxk : x[k] ∈ effective_domain (separableSum g))
    (m : ℕ) (hm : m ≤ p) :
    x[k, m] ∈ effective_domain (separableSum g) := by
  induction m with
  | zero =>
      -- The zeroth inner stage is the current outer iterate itself.
      simpa using hxk
  | succ m ihm =>
      have hm_lt : m < p := Nat.lt_of_succ_le hm
      have hm_le : m ≤ p := Nat.le_of_lt hm_lt
      let jm : Fin p := ⟨m, hm_lt⟩
      let xm : effective_domain (separableSum g) :=
        ⟨x[k, m], ihm hm_le⟩
      have hsucc :
          x[k, m + 1] =
            block_coordinate_update
              x[k, m]
              jm
              (hproblem.toIsBlockProximalGradientProblem.prox_point (Li jm) jm x[k, m] -
                x[k, m] jm) := by
        -- The successor inner stage is exactly the owner one-block prox update.
        simpa [block_coordinate_update] using
          cyclic_block_proximal_gradient_method_inner_succ hproblem x0' k hm_lt
      have hnext :
          block_coordinate_update
              x[k, m]
              jm
              (hproblem.toIsBlockProximalGradientProblem.prox_point (Li jm) jm x[k, m] -
                x[k, m] jm) ∈
            effective_domain (separableSum g) := by
        -- Domain membership propagates through one owner-level prox update.
        simpa [xm] using
          hproblem.block_coordinate_update_prox_point_mem_effective_domain
            (Li jm)
            xm
            jm
      rw [hsucc]
      exact hnext

/-- Helper for Lemma 11.4: every auxiliary iterate `x^{k,m}` with `m ≤ p` stays in the effective
domain of the block-separable regularizer. -/
lemma cbpg_auxiliary_iterate_mem_effective_domain
    (k : ℕ) (m : ℕ) (hm : m ≤ p) :
    x[k, m] ∈ effective_domain (separableSum g) := by
  induction k generalizing m with
  | zero =>
      have hx0 : x[0] ∈ effective_domain (separableSum g) := by
        -- The initial outer iterate is the given starting point in the effective domain.
        simpa using x0.2
      exact
        cbpg_auxiliary_iterate_mem_effective_domain_of_outer_iterate
          hproblem
          x0
          0
          hx0
          m
          hm
  | succ k ih =>
      have hxsucc : x[k + 1] ∈ effective_domain (separableSum g) := by
        -- The next outer iterate is the terminal inner stage of the previous cycle.
        rw [cyclic_block_proximal_gradient_method_succ]
        exact ih p (Nat.le_refl _)
      exact
        cbpg_auxiliary_iterate_mem_effective_domain_of_outer_iterate
          hproblem
          x0
          (k + 1)
          hxsucc
          m
          hm

/-- Helper for Lemma 11.4: the transported outer-step difference is the telescoping sum of the
transported auxiliary stage differences. -/
lemma cbpg_outer_step_toPiLp_eq_sum_stage_differences
    (k : ℕ) :
    toPiLp x[k] - toPiLp x[k + 1] =
      Finset.sum (Finset.range p) (fun n ↦ toPiLp x[k, n] - toPiLp x[k, n + 1]) := by
  have hprefix :
      ∀ n : ℕ,
        n ≤ p →
          toPiLp x[k] - toPiLp x[k, n] =
            Finset.sum (Finset.range n) (fun m ↦ toPiLp x[k, m] - toPiLp x[k, m + 1]) := by
    intro n hn
    induction n with
    | zero =>
        -- The empty prefix contributes no stage differences.
        simp
    | succ n ihn =>
        have hn_le : n ≤ p := Nat.le_of_succ_le hn
        -- Extend the telescoping identity by one more stage difference.
        calc
          toPiLp x[k] - toPiLp x[k, n + 1] =
              (toPiLp x[k] - toPiLp x[k, n]) +
                (toPiLp x[k, n] - toPiLp x[k, n + 1]) := by
            simpa using
              (sub_add_sub_cancel
                (toPiLp x[k])
                (toPiLp x[k, n])
                (toPiLp x[k, n + 1])).symm
          _ =
              Finset.sum (Finset.range n) (fun m ↦ toPiLp x[k, m] - toPiLp x[k, m + 1]) +
                (toPiLp x[k, n] - toPiLp x[k, n + 1]) := by
            rw [ihn hn_le]
          _ =
              Finset.sum (Finset.range (n + 1))
                (fun m ↦ toPiLp x[k, m] - toPiLp x[k, m + 1]) := by
            rw [Finset.sum_range_succ]
  -- Apply the prefix telescoping identity at the full cycle length `p`.
  calc
    toPiLp x[k] - toPiLp x[k + 1] = toPiLp x[k] - toPiLp x[k, p] := by
      rw [cyclic_block_proximal_gradient_method_succ]
    _ =
        Finset.sum (Finset.range p) (fun n ↦ toPiLp x[k, n] - toPiLp x[k, n + 1]) := by
      exact hprefix p (Nat.le_refl _)

/-- Helper for Lemma 11.4: the squared `PiLp` norm of one outer CBPG step is the sum of the
squared norms of the auxiliary one-block steps. -/
lemma cbpg_outer_step_sq_norm_eq_sum_auxiliary_sq_norm
    (k : ℕ) :
    ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) =
      Finset.sum Finset.univ (fun j : Fin p ↦ ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
  have hsum_single :
      Finset.sum (Finset.range p) (fun n ↦ toPiLp x[k, n] - toPiLp x[k, n + 1]) =
        Finset.sum Finset.univ
          (fun j : Fin p ↦
            PiLp.single (2 : ENNReal) j (x[k, j.1] j - x[k, j.1 + 1] j)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact cbpg_stage_difference_toPiLp_single hproblem x0 k j
  -- Rewrite the outer step as a sum of singleton-supported `PiLp` vectors, then expand the
  -- `L²` norm coordinatewise.
  calc
    ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) =
        ‖Finset.sum Finset.univ
            (fun j : Fin p ↦
              PiLp.single (2 : ENNReal) j (x[k, j.1] j - x[k, j.1 + 1] j))‖ ^ (2 : ℕ) := by
      rw [cbpg_outer_step_toPiLp_eq_sum_stage_differences, hsum_single]
    _ =
        Finset.sum Finset.univ
          (fun j : Fin p ↦ ‖x[k, j.1] j - x[k, j.1 + 1] j‖ ^ (2 : ℕ)) := by
      simpa [PiLp.single_eq_same] using
        (PiLp.norm_sq_eq_of_L2
          (fun i : Fin p ↦ Ei i)
          (Finset.sum Finset.univ
            (fun j : Fin p ↦
              PiLp.single (2 : ENNReal) j (x[k, j.1] j - x[k, j.1 + 1] j))))
    _ =
        Finset.sum Finset.univ
          (fun j : Fin p ↦ ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [cbpg_auxiliary_step_norm_eq_block_norm]

-- Proof sketch: apply the Chapter 11 one-block sufficient-decrease owner
-- `BlockProximalGradientAssumptions.block_partial_gradient_sufficient_decrease` to the current
-- auxiliary state `x^{k,j}` with block index `j` and stepsize `L_j`, then rewrite the updated
-- point as the next auxiliary state `x^{k,j+1}`.
/-- Lemma 11.4 (1): for part (a), the objective decrease across one cyclic block update satisfies
equation (11.9),
`F(x^{k,j}) - F(x^{k,j+1}) ≥ (1 / (2 L_j)) ‖G_{L_j}^j(x^{k,j})‖^2`. -/
theorem cbpg_auxiliary_sufficient_decrease_gradient_mapping
    (k : ℕ) (j : Fin p) :
    F x[k, j.1] - F x[k, j.1 + 1] ≥
      ((((1 : ℝ) / (2 * (Li j : ℝ))) *
          ‖G[Li j; (hproblem.toIsBlockProximalGradientProblem)] x[k, j.1] j‖ ^
            (2 : ℕ) : ℝ) : EReal) :=
  by
  let xj : effective_domain (separableSum g) :=
    ⟨x[k, j.1], cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k j.1 (Nat.le_of_lt j.2)⟩
  have hsucc :
      x[k, j.1 + 1] =
        block_coordinate_update
          x[k, j.1]
          j
          (hproblem.toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] -
            x[k, j.1] j) := by
    -- The next auxiliary stage is the canonical one-block prox update.
    simpa [block_coordinate_update] using
      cyclic_block_proximal_gradient_method_inner_succ hproblem x0' k j.2
  -- Apply the owner one-block sufficient-decrease theorem at the current auxiliary iterate.
  simpa [xj, hsucc] using
    hproblem.block_partial_gradient_sufficient_decrease j xj

-- Proof sketch: apply Proposition 11.1 to the auxiliary state `x^{k,j}`, then identify the
-- resulting one-block update with the next auxiliary iterate `x^{k,j+1}`.
/-- Lemma 11.4 (2): for part (a), equation (11.10) gives the equivalent step-norm form
`F(x^{k,j}) - F(x^{k,j+1}) ≥ (L_j / 2) ‖x^{k,j} - x^{k,j+1}‖^2`. -/
theorem cbpg_auxiliary_sufficient_decrease_step_norm
    (k : ℕ) (j : Fin p) :
    F x[k, j.1] - F x[k, j.1 + 1] ≥
      ((((Li j : ℝ) / 2) *
          ‖x[k, j.1] - x[k, j.1 + 1]‖ ^
            (2 : ℕ) : ℝ) : EReal) := by
  let xj : effective_domain (separableSum g) :=
    ⟨x[k, j.1], cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k j.1 (Nat.le_of_lt j.2)⟩
  have hsucc :
      x[k, j.1 + 1] =
        block_coordinate_update
          x[k, j.1]
          j
          (hproblem.toIsBlockProximalGradientProblem.prox_point (Li j) j x[k, j.1] -
            x[k, j.1] j) := by
    -- The stage update matches the proposition's one-block update owner.
    simpa [block_coordinate_update] using
      cyclic_block_proximal_gradient_method_inner_succ hproblem x0' k j.2
  -- Reuse Proposition 11.1 at the auxiliary iterate and rewrite its updated point.
  simpa [xj, hsucc] using
    hproblem.block_partial_gradient_sufficient_decrease_step_norm j xj

-- Proof sketch: sum the one-block inequality from equation (11.10) over one full cycle
-- `j = 0, ..., p - 1`, bound each coefficient below by `L_min`, and use that the block updates
-- are orthogonal across the canonical `L²` block product, so the squared norms telescope to
-- `‖x₂^k - x₂^(k+1)‖^2`.
/-- Helper for Lemma 11.4: every outer CBPG objective value is finite, so it is neither `⊤` nor
`⊥`. -/
lemma cbpg_objective_value_finite
    (k : ℕ) :
    F x[k] ≠ ⊤ ∧ F x[k] ≠ ⊥ := by
  have hxg : x[k] ∈ effective_domain (separableSum g) := by
    simpa using cbpg_auxiliary_iterate_mem_effective_domain hproblem x0 k 0 (Nat.zero_le p)
  have hxf : x[k] ∈ effective_domain f := by
    -- Effective-domain compatibility makes `f` finite at every CBPG outer iterate.
    exact interior_subset (hproblem.g_effective_domain_subset_interior_f_effective_domain hxg)
  have hf_top : f x[k] ≠ ⊤ := (mem_effective_domain.mp hxf).ne
  have hg_top : separableSum g x[k] ≠ ⊤ := (mem_effective_domain.mp hxg).ne
  have hf_bot : f x[k] ≠ ⊥ := hproblem.f_ne_bot (x[k])
  have hg_bot : separableSum g x[k] ≠ ⊥ := by
    -- Proper block penalties keep the separable regularizer away from `-∞`.
    rw [separableSum_apply]
    exact ereal_sum_ne_bot Finset.univ
      (fun i ↦ g i (x[k] i))
      (fun i _ ↦ (hproblem.block_g_proper i).ne_bot _)
  constructor
  · simpa [composite_model_objective] using EReal.add_ne_top hf_top hg_top
  · simpa [composite_model_objective] using EReal.add_ne_bot_iff.mpr ⟨hf_bot, hg_bot⟩

/-- Helper for Lemma 11.4: the first `n` auxiliary stage decreases telescope additively into the
full outer-cycle decrease. -/
lemma cbpg_outer_cycle_partial_additive_telescope
    (k n : ℕ) (hn : n ≤ p) :
    (Finset.sum (Finset.range n)
        (fun m ↦
          if hm : m < p then
            ((((Li ⟨m, hm⟩ : ℝ) / 2) *
                ‖x[k, m] - x[k, m + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)
          else 0)) +
        F x[k, n] ≤
      F x[k] := by
  let δ : ℕ → EReal := fun m ↦
    if hm : m < p then
      ((((Li ⟨m, hm⟩ : ℝ) / 2) *
          ‖x[k, m] - x[k, m + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)
    else 0
  -- Build the full-cycle estimate prefix-by-prefix so Lean never normalizes the whole sum at once.
  induction n with
  | zero =>
      simpa [δ]
  | succ n ihn =>
      have hn_le : n ≤ p := Nat.le_of_succ_le hn
      have hn_lt : n < p := Nat.lt_of_succ_le hn
      have hprefix :
          Finset.sum (Finset.range n) δ + F x[k, n] ≤ F x[k] := by
        exact ihn hn_le
      have hstage_sub :
          δ n ≤ F x[k, n] - F x[k, n + 1] := by
        -- Convert the stagewise sufficient decrease into the prefix summand shape `δ n`.
        simpa [δ, hn_lt] using
          (cbpg_auxiliary_sufficient_decrease_step_norm hproblem x0 k ⟨n, hn_lt⟩ :
            F x[k, n] - F x[k, n + 1] ≥
              ((((Li ⟨n, hn_lt⟩ : ℝ) / 2) *
                  ‖x[k, n] - x[k, n + 1]‖ ^ (2 : ℕ) : ℝ) : EReal))
      have hstage :
          δ n + F x[k, n + 1] ≤ F x[k, n] := by
        -- Rewrite the stage estimate in additive form before appending it to the prefix.
        exact EReal.add_le_of_le_sub hstage_sub
      calc
        (Finset.sum (Finset.range (n + 1)) δ) + F x[k, n + 1] =
            Finset.sum (Finset.range n) δ + (δ n + F x[k, n + 1]) := by
          rw [Finset.sum_range_succ]
          abel
        _ ≤ Finset.sum (Finset.range n) δ + F x[k, n] := by
          calc
            Finset.sum (Finset.range n) δ + (δ n + F x[k, n + 1]) =
                (δ n + F x[k, n + 1]) + Finset.sum (Finset.range n) δ := by
              abel
            _ ≤ F x[k, n] + Finset.sum (Finset.range n) δ := by
              exact add_le_add_left hstage (Finset.sum (Finset.range n) δ)
            _ = Finset.sum (Finset.range n) δ + F x[k, n] := by
              abel
        _ ≤ F x[k] := hprefix

/-- Helper for Lemma 11.4: summing the stagewise additive telescope across all `p` blocks gives
the full outer-cycle additive decrease inequality. -/
lemma cbpg_outer_cycle_additive_telescope
    (k : ℕ) :
    (Finset.sum Finset.univ
        (fun j : Fin p ↦
          ((((Li j : ℝ) / 2) *
              ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal))) +
        F x[k + 1] ≤
      F x[k] := by
  have hpartial :=
    cbpg_outer_cycle_partial_additive_telescope hproblem x0 k p (Nat.le_refl p)
  let φ : ℕ → EReal := fun m ↦
    if hm : m < p then
      ((((Li ⟨m, hm⟩ : ℝ) / 2) *
          ‖x[k, m] - x[k, m + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)
    else 0
  have hsum :
      Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((((Li j : ℝ) / 2) *
                ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)) =
        Finset.sum (Finset.range p)
          φ := by
    simpa [φ] using (Fin.sum_univ_eq_sum_range φ p)
  -- Replace the prefix range sum with the canonical `Fin p` sum and identify `x[k,p] = x[k+1]`.
  calc
    (Finset.sum Finset.univ
        (fun j : Fin p ↦
          ((((Li j : ℝ) / 2) *
              ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal))) +
        F x[k + 1] =
        (Finset.sum (Finset.range p) φ) +
          F x[k, p] := by
      rw [hsum, cyclic_block_proximal_gradient_method_succ]
    _ ≤ F x[k] := by
      simpa [φ] using hpartial

/-- Helper for Lemma 11.4: replacing each block coefficient `L_j / 2` by the smaller common
coefficient `L_min / 2` yields a lower bound for the full-cycle quadratic term. -/
lemma cbpg_outer_cycle_real_coefficient_bound
    [Nonempty (Fin p)]
    (k : ℕ) :
    ((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) ≤
      Finset.sum Finset.univ
        (fun j : Fin p ↦
          ((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
  -- First rewrite the outer-step norm square as the sum of the orthogonal stage norms.
  calc
    ((Lmin : ℝ) / 2) * ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) =
        ((Lmin : ℝ) / 2) *
          Finset.sum Finset.univ
            (fun j : Fin p ↦ ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
      rw [cbpg_outer_step_sq_norm_eq_sum_auxiliary_sq_norm]
    _ =
        Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((Lmin : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
      rw [Finset.mul_sum]
    _ ≤
        Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) := by
      refine Finset.sum_le_sum ?_
      intro j hj
      have hLmin_le_pos : Lmin ≤ Li j := by
        simpa [cbpg_min_block_stepsize] using
          (Finset.inf'_le Li (Finset.mem_univ j))
      have hLmin_le : (Lmin : ℝ) ≤ (Li j : ℝ) := by
        exact_mod_cast hLmin_le_pos
      have hcoeff : ((Lmin : ℝ) / 2) ≤ ((Li j : ℝ) / 2) := by
        exact div_le_div_of_nonneg_right hLmin_le (by norm_num)
      have hsq_nonneg : 0 ≤ ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) := by
        positivity
      exact mul_le_mul_of_nonneg_right hcoeff hsq_nonneg

/-- Helper for Lemma 11.4: the real coefficient comparison can be transported once into `EReal`
before composing it with the additive telescope. -/
lemma cbpg_outer_cycle_ereal_coefficient_bound
    [Nonempty (Fin p)]
    (k : ℕ) :
    ((((Lmin : ℝ) / 2) *
        ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      Finset.sum Finset.univ
        (fun j : Fin p ↦
          ((((Li j : ℝ) / 2) *
              ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
  -- Keep the real algebra separate and cast it only once into the `EReal` additive telescope.
  have hreal :=
    cbpg_outer_cycle_real_coefficient_bound hproblem x0 k
  have hsum :
      (((Finset.sum Finset.univ
            (fun j : Fin p ↦
              ((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) : ℝ) : EReal)) =
        Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((((Li j : ℝ) / 2) *
                ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)) := by
    exact
      map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal)
        (fun j : Fin p ↦
          ((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ))
        Finset.univ
  have hcast :
      ((((Lmin : ℝ) / 2) *
          ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        (((Finset.sum Finset.univ
              (fun j : Fin p ↦
                ((Li j : ℝ) / 2) * ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ)) : ℝ) : EReal)) := by
    exact_mod_cast hreal
  exact hcast.trans_eq hsum

/-- Lemma 11.4 (3): for part (b), the objective decrease across one full CBPG cycle satisfies
equation (11.11), expressed on the canonical Hilbert-product owner
`PiLp (2 : ENNReal) Ei` identified with the raw block tuple by
`PiLp.continuousLinearEquiv (2 : ENNReal) ℝ Ei`,
`F(x^k) - F(x^{k+1}) ≥ (L_min / 2) ‖x₂^k - x₂^(k+1)‖^2`. -/
theorem cbpg_sufficient_decrease_outer_step
    [Nonempty (Fin p)]
    (k : ℕ) :
    F x[k] - F x[k + 1] ≥
      ((((Lmin : ℝ) / 2) *
          ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Route correction: the final `EReal` subtraction is postponed until the last line, after the
  -- additive telescope and the real coefficient comparison have already been separated.
  have hcoeff :
      ((((Lmin : ℝ) / 2) *
          ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((((Li j : ℝ) / 2) *
                ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal)) :=
    cbpg_outer_cycle_ereal_coefficient_bound hproblem x0 k
  have htelescope :
      (Finset.sum Finset.univ
          (fun j : Fin p ↦
            ((((Li j : ℝ) / 2) *
                ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal))) +
          F x[k + 1] ≤
        F x[k] :=
    cbpg_outer_cycle_additive_telescope hproblem x0 k
  have hadd :
      ((((Lmin : ℝ) / 2) *
          ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) +
        F x[k + 1] ≤
      F x[k] := by
    calc
      ((((Lmin : ℝ) / 2) *
            ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) +
          F x[k + 1] ≤
          (Finset.sum Finset.univ
              (fun j : Fin p ↦
                ((((Li j : ℝ) / 2) *
                    ‖x[k, j.1] - x[k, j.1 + 1]‖ ^ (2 : ℕ) : ℝ) : EReal))) +
            F x[k + 1] := by
        simpa [add_assoc, add_left_comm, add_comm] using
          add_le_add_left hcoeff (F x[k + 1])
      _ ≤ F x[k] := htelescope
  have hfinite : F x[k + 1] ≠ ⊤ ∧ F x[k + 1] ≠ ⊥ :=
    cbpg_objective_value_finite hproblem x0 (k + 1)
  -- Convert the additive estimate back to the stated subtraction form only at the end.
  have hsub :
      ((((Lmin : ℝ) / 2) *
          ‖toPiLp x[k] - toPiLp x[k + 1]‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        F x[k] - F x[k + 1] := by
    exact (EReal.le_sub_iff_add_le (.inl hfinite.2) (.inl hfinite.1)).2 hadd
  simpa using hsub

end

end
