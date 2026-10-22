/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.MonotoneConvergence
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Lemma_2_2_6
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_5_1

noncomputable section

open Filter
open scoped Topology

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Chapter 3 level set `L(x₀) = {x ∈ D | f x ≤ f x₀}`. -/
def negativeCurvatureLevelSet (D : Set E) (f : E → ℝ) (x₀ : E) : Set E :=
  {x | x ∈ D ∧ f x ≤ f x₀}

/-- The quadratic search path `x + a • d + a^2 • s` underlying the Chapter 3
negative-curvature line-search updates. -/
def negativeCurvatureSearchPath (x s d : E) (a : ℝ) : E :=
  x + a • d + a ^ (2 : ℕ) • s

/-- The Chapter 3 trial point is the quadratic search path sampled at the
backtracking steplength `a = γ^i`. -/
abbrev negativeCurvatureTrialPoint (x s d : E) (γ : ℝ) (i : ℕ) : E :=
  negativeCurvatureSearchPath x s d (γ ^ i)

@[simp] theorem negativeCurvatureTrialPoint_eq_searchPath
    (x s d : E) (γ : ℝ) (i : ℕ) :
    negativeCurvatureTrialPoint x s d γ i =
      negativeCurvatureSearchPath x s d (γ ^ i) :=
  rfl

end

-- Domain sampling pass:
-- * primary domain: smooth unconstrained optimization with negative-curvature backtracking
--   line search on a real Hilbert space;
-- * sampled source/core owners: `IsDescentPairAt` and `hessianQuadraticAt` from
--   `Definition_3_5_1`, and the explicit iterate/step-size theorem surfaces in
--   `Theorem_3_1_4` and `Theorem_3_1_6`;
-- * source-facing owner introduced here: the sequence-level backtracking predicate
--   `IsNegativeCurvatureLineSearchSequence`;
-- * bridge/view comparison: the finite-dimensional algorithm-run owner in
--   `Algorithm_3_5_4` is a separate realization layer, not the owner for the present
--   Hilbert-space convergence theorem.

section NegativeCurvatureDirectionMethod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The concrete step rule and sufficient-decrease test used in the negative curvature
direction method. -/
def IsNegativeCurvatureLineSearchSequence
    (f : E → ℝ) (x s d : ℕ → E) (backtrackingExponent : ℕ → ℕ)
    (x₀ : E) (ρ γ : ℝ) : Prop :=
  ρ ∈ Set.Ioo (0 : ℝ) 1 ∧
    γ ∈ Set.Ioo (0 : ℝ) 1 ∧
    x 0 = x₀ ∧
    ∀ k,
      x (k + 1) =
        negativeCurvatureTrialPoint (x k) (s k) (d k) γ (backtrackingExponent k) ∧
        f (x (k + 1)) ≤
          f (x k) + ρ * (γ ^ (2 * backtrackingExponent k : ℕ)) *
            (inner ℝ (s k) (gradient f (x k)) +
              (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k)) ∧
        ∀ j < backtrackingExponent k,
          f (negativeCurvatureTrialPoint (x k) (s k) (d k) γ j) >
            f (x k) + ρ * (γ ^ (2 * j : ℕ)) *
              (inner ℝ (s k) (gradient f (x k)) +
                (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k))

/-- Unfolding formula for `IsNegativeCurvatureLineSearchSequence`. -/
theorem isNegativeCurvatureLineSearchSequence_iff
    (f : E → ℝ) (x s d : ℕ → E) (backtrackingExponent : ℕ → ℕ)
    (x₀ : E) (ρ γ : ℝ) :
    IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ ↔
      ρ ∈ Set.Ioo (0 : ℝ) 1 ∧
        γ ∈ Set.Ioo (0 : ℝ) 1 ∧
        x 0 = x₀ ∧
        ∀ k,
          x (k + 1) =
            negativeCurvatureTrialPoint (x k) (s k) (d k) γ (backtrackingExponent k) ∧
            f (x (k + 1)) ≤
              f (x k) + ρ * (γ ^ (2 * backtrackingExponent k : ℕ)) *
                (inner ℝ (s k) (gradient f (x k)) +
                  (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k)) ∧
            ∀ j < backtrackingExponent k,
              f (negativeCurvatureTrialPoint (x k) (s k) (d k) γ j) >
                f (x k) + ρ * (γ ^ (2 * j : ℕ)) *
                    (inner ℝ (s k) (gradient f (x k)) +
                      (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k)) :=
  Iff.rfl

namespace IsNegativeCurvatureLineSearchSequence

/-- A source-faithful backtracking line-search sequence starts at the prescribed initial point
`x₀`. -/
theorem start_eq {f : E → ℝ} {x s d : ℕ → E} {backtrackingExponent : ℕ → ℕ}
    {x₀ : E} {ρ γ : ℝ}
    (h : IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ) :
    x 0 = x₀ := by
  rcases h with ⟨_, _, hx₀, _⟩
  exact hx₀

end IsNegativeCurvatureLineSearchSequence

variable (D : Set E) (f : E → ℝ) (x s d : ℕ → E) (backtrackingExponent : ℕ → ℕ)
  (x₀ : E) (ρ γ : ℝ)
variable (hD_open : IsOpen D)
variable (hC2 : ContDiffOn ℝ 2 f D)
variable (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
variable (hx_mem : ∀ k, x k ∈ D)
variable (hs_bounded : Bornology.IsBounded (Set.range s))
variable (hd_bounded : Bornology.IsBounded (Set.range d))
variable (hLineSearch :
  IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
variable (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))

/-- Helper for Chapter03 Theorem 3.5.6: the accepted sufficient-decrease step never increases the
objective value. -/
lemma negativeCurvature_objective_step_le
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))
    (k : ℕ) :
    f (x (k + 1)) ≤ f (x k) := by
  rcases hLineSearch with ⟨hρ, hγ, _, hstep⟩
  rcases hstep k with ⟨_, haccept, _⟩
  have hmodel_nonpos :
      inner ℝ (s k) (gradient f (x k)) +
          (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k) ≤
        0 := by
    -- Both pieces of the model term are nonpositive for a descent pair.
    have hleft_nonpos :
        inner ℝ (s k) (gradient f (x k)) ≤ 0 :=
      IsDescentPairAt.inner_left_nonpos (hDescentPair k)
    have hcurv_nonpos :
        hessianQuadraticAt f (x k) (d k) ≤ 0 :=
      IsDescentPairAt.hessianQuadratic_nonpos (hDescentPair k)
    nlinarith
  have hscale_nonneg :
      0 ≤ ρ * (γ ^ (2 * backtrackingExponent k : ℕ)) := by
    -- The backtracking parameters lie in `(0,1)`, so the scaling factor is nonnegative.
    exact mul_nonneg (le_of_lt hρ.1) (pow_nonneg (le_of_lt hγ.1) _)
  have hdrop_nonpos :
      ρ * (γ ^ (2 * backtrackingExponent k : ℕ)) *
          (inner ℝ (s k) (gradient f (x k)) +
            (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k)) ≤
        0 := by
    exact mul_nonpos_of_nonneg_of_nonpos hscale_nonneg hmodel_nonpos
  -- The accepted decrease inequality plus the nonpositive model term gives monotonicity.
  linarith

/-- Helper for Chapter03 Theorem 3.5.6: every iterate stays in the compact level set determined
by the starting point. -/
lemma negativeCurvature_iterates_mem_levelSet
    (hx_mem : ∀ k, x k ∈ D)
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)) :
    ∀ k, x k ∈ negativeCurvatureLevelSet D f x₀ := by
  intro k
  induction k with
  | zero =>
      -- The starting iterate is `x₀`, so it belongs to its own level set.
      exact ⟨hx_mem 0, by
        simp [IsNegativeCurvatureLineSearchSequence.start_eq (h := hLineSearch)]⟩
  | succ k hk =>
      -- Monotonicity propagates the level-set bound from step `k` to step `k + 1`.
      exact ⟨hx_mem (k + 1), le_trans
        (negativeCurvature_objective_step_le
          (f := f) (x := x) (s := s) (d := d)
          (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
          hLineSearch hDescentPair k)
        hk.2⟩

/-- Helper for Chapter03 Theorem 3.5.6: the objective values form an antitone sequence. -/
lemma negativeCurvature_objective_antitone
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)) :
    Antitone (fun k : ℕ ↦ f (x k)) := by
  -- One-step decrease upgrades to antitonicity on `ℕ`.
  refine antitone_nat_of_succ_le fun k ↦ ?_
  exact negativeCurvature_objective_step_le
    (f := f) (x := x) (s := s) (d := d)
    (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
    hLineSearch hDescentPair k

/-- Helper for Chapter03 Theorem 3.5.6: compactness of the level set prevents the objective
sequence from tending to `-∞`. -/
lemma negativeCurvature_objective_not_tendsto_atBot
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
    (hx_mem : ∀ k, x k ∈ D)
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)) :
    ¬ Tendsto (fun k : ℕ ↦ f (x k)) atTop atBot := by
  have hcont_D : ContinuousOn f D := hC2.continuousOn
  have hcont_level : ContinuousOn f (negativeCurvatureLevelSet D f x₀) := by
    -- Restrict the ambient `C²` hypothesis from `D` to the compact level set.
    exact ContinuousOn.mono hcont_D fun _ hx ↦ hx.1
  rcases IsCompact.bddBelow_image hLevelSetCompact hcont_level with ⟨m, hm⟩
  intro hbot
  rw [tendsto_atTop_atBot] at hbot
  rcases hbot (m - 1) with ⟨N, hN⟩
  have hmemN :
      x N ∈ negativeCurvatureLevelSet D f x₀ :=
    negativeCurvature_iterates_mem_levelSet
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hx_mem hLineSearch hDescentPair N
  have hmN : m ≤ f (x N) := by
    exact hm ⟨x N, hmemN, rfl⟩
  have hbotN : f (x N) ≤ m - 1 := hN N le_rfl
  linarith

/-- Helper for Chapter03 Theorem 3.5.6: the successive objective decreases converge to `0`. -/
lemma negativeCurvature_decrease_gap_tendsto_zero
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
    (hx_mem : ∀ k, x k ∈ D)
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)) :
    Tendsto (fun k ↦ f (x k) - f (x (k + 1))) atTop (nhds 0) := by
  have hanti :
      Antitone (fun k : ℕ ↦ f (x k)) :=
    negativeCurvature_objective_antitone
      (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hLineSearch hDescentPair
  rcases tendsto_atTop_of_antitone hanti with hbot | ⟨l, hl⟩
  · exact False.elim (negativeCurvature_objective_not_tendsto_atBot
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hC2 hLevelSetCompact hx_mem hLineSearch hDescentPair hbot)
  · have hl_shift : Tendsto (fun k : ℕ ↦ f (x (k + 1))) atTop (nhds l) :=
      hl.comp (tendsto_add_atTop_nat 1)
    -- Subtracting the shifted convergent sequence yields the vanishing one-step decrease.
    simpa using hl.sub hl_shift

/-- Helper for Chapter03 Theorem 3.5.6: the combined first- and second-order model term used in
the source sufficient-decrease estimate. -/
abbrev negativeCurvatureModelTerm (k : ℕ) : ℝ :=
  -(inner ℝ (s k) (gradient f (x k)) +
      (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k))

/-- Helper for Chapter03 Theorem 3.5.6: every source model term is nonnegative for a descent
pair. -/
lemma negativeCurvature_model_term_nonneg
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))
    (k : ℕ) :
    0 ≤ negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k := by
  have hleft_nonpos :
      inner ℝ (s k) (gradient f (x k)) ≤ 0 :=
    IsDescentPairAt.inner_left_nonpos (hDescentPair k)
  have hcurv_nonpos :
      hessianQuadraticAt f (x k) (d k) ≤ 0 :=
    IsDescentPairAt.hessianQuadratic_nonpos (hDescentPair k)
  -- Negating the nonpositive first- and second-order contribution gives a nonnegative model term.
  dsimp [negativeCurvatureModelTerm]
  linarith

/-- Helper for Chapter03 Theorem 3.5.6: in the bounded-exponent branch of the textbook proof,
the accepted sufficient decrease bounds each objective gap below by a fixed multiple of the
model term. -/
lemma negativeCurvature_bounded_exponent_branch_forces_gap
    (ε : ℝ) (β : ℕ) {φ : ℕ → ℕ}
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))
    (hε : ∀ k, ε ≤ negativeCurvatureModelTerm
      (f := f) (x := x) (s := s) (d := d) (φ k))
    (hβ : ∀ k, backtrackingExponent (φ k) ≤ β)
    (k : ℕ) :
    ρ * γ ^ (2 * β : ℕ) * ε ≤ f (x (φ k)) - f (x (φ k + 1)) := by
  rcases hLineSearch with ⟨hρ, hγ, _, hstep⟩
  rcases hstep (φ k) with ⟨_, haccept, _⟩
  have hmodel_nonneg :
      0 ≤ negativeCurvatureModelTerm
        (f := f) (x := x) (s := s) (d := d) (φ k) :=
    negativeCurvature_model_term_nonneg
      (f := f) (x := x) (s := s) (d := d) hDescentPair (φ k)
  have hpow :
      γ ^ (2 * β : ℕ) ≤ γ ^ (2 * backtrackingExponent (φ k) : ℕ) := by
    -- With `0 < γ < 1`, larger exponents only decrease the backtracking factor.
    exact (pow_right_strictAnti₀ hγ.1 hγ.2).le_iff_ge.2 (Nat.mul_le_mul_left 2 (hβ k))
  have hscale :
      ρ * γ ^ (2 * β : ℕ) * ε ≤
        ρ * γ ^ (2 * backtrackingExponent (φ k) : ℕ) *
          negativeCurvatureModelTerm
            (f := f) (x := x) (s := s) (d := d) (φ k) := by
    have hργ_nonneg : 0 ≤ ρ * γ ^ (2 * β : ℕ) := by
      exact mul_nonneg hρ.1.le (pow_nonneg hγ.1.le _)
    have hργmono :
        ρ * γ ^ (2 * β : ℕ) ≤ ρ * γ ^ (2 * backtrackingExponent (φ k) : ℕ) := by
      exact mul_le_mul_of_nonneg_left hpow hρ.1.le
    calc
      ρ * γ ^ (2 * β : ℕ) * ε
          ≤ ρ * γ ^ (2 * β : ℕ) *
              negativeCurvatureModelTerm
                (f := f) (x := x) (s := s) (d := d) (φ k) := by
              exact mul_le_mul_of_nonneg_left (hε k) hργ_nonneg
      _ ≤ ρ * γ ^ (2 * backtrackingExponent (φ k) : ℕ) *
            negativeCurvatureModelTerm
              (f := f) (x := x) (s := s) (d := d) (φ k) := by
            exact mul_le_mul_of_nonneg_right hργmono hmodel_nonneg
  have hgap :
      ρ * γ ^ (2 * backtrackingExponent (φ k) : ℕ) *
          negativeCurvatureModelTerm
            (f := f) (x := x) (s := s) (d := d) (φ k) ≤
        f (x (φ k)) - f (x (φ k + 1)) := by
    -- Rewrite the accepted decrease step in terms of the nonnegative model term.
    dsimp [negativeCurvatureModelTerm] at *
    linarith
  -- Chaining the fixed lower bound with the accepted decrease gives the source gap estimate.
  exact le_trans hscale hgap

/-- Helper for Chapter03 Theorem 3.5.6: an unbounded sequence of accepted exponents admits a
strictly monotone subsequence along which the exponents tend to `atTop`. -/
lemma unbounded_nat_subsequence_tendsto_atTop
    {u : ℕ → ℕ} (hu_unbounded : ¬ BddAbove (Set.range u)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ Tendsto (u ∘ ψ) atTop atTop := by
  have hcofinal :
      ∀ N M : ℕ, ∃ n > M, N ≤ u n := by
    intro N M
    by_contra hfail
    push Not at hfail
    have hprefix_bdd : BddAbove (u '' Set.Iic M) :=
      ((Set.finite_Iic M).image u).bddAbove
    have htail_bdd : BddAbove (Set.Iio N : Set ℕ) := bddAbove_Iio
    have hsubset : Set.range u ⊆ u '' Set.Iic M ∪ Set.Iio N := by
      intro y hy
      rcases hy with ⟨n, rfl⟩
      by_cases hn : n ≤ M
      · -- Indices in the finite prefix land in the bounded image of `Iic M`.
        exact Or.inl ⟨n, hn, rfl⟩
      · -- Indices in the tail satisfy the negated cofinality assumption.
        exact Or.inr (hfail n (lt_of_not_ge hn))
    exact hu_unbounded ((BddAbove.union hprefix_bdd htail_bdd).mono hsubset)
  have hfrequent_large : ∀ N : ℕ, ∃ᶠ n in atTop, N ≤ u n := by
    intro N
    rw [frequently_atTop']
    intro M
    obtain ⟨n, hnM, hNu⟩ := hcofinal N M
    exact ⟨n, hnM, hNu⟩
  obtain ⟨ψ, hψmono, hψlarge⟩ := extraction_forall_of_frequently hfrequent_large
  refine ⟨ψ, hψmono, ?_⟩
  -- The extracted subsequence pointwise dominates the identity, hence tends to `atTop`.
  exact tendsto_atTop_mono (fun n ↦ hψlarge n) tendsto_id

/-- Helper for Chapter03 Theorem 3.5.6: in the unbounded-exponent branch, the last rejected step
already forces the normalized quadratic-path expression to dominate the model term. -/
lemma negativeCurvature_rejected_step_model_lower_bound
    (k : ℕ) (hkexp : 0 < backtrackingExponent k)
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))
    {a : ℝ} (ha : a = γ ^ (backtrackingExponent k - 1)) :
    (1 - ρ) * negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k ≤
      (f (negativeCurvatureSearchPath (x k) (s k) (d k) a) - f (x k)
        - a * inner ℝ (d k) (gradient f (x k))
        + a ^ (2 : ℕ) * negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k) /
          a ^ (2 : ℕ) := by
  rcases hLineSearch with ⟨hρ, hγ, _, hstep⟩
  rcases hstep k with ⟨_, _, hreject⟩
  have ha_pos : 0 < a := by
    -- The rejected exponent still uses a positive backtracking factor.
    rw [ha]
    exact pow_pos hγ.1 _
  have hsq_pos : 0 < a ^ (2 : ℕ) := by
    positivity
  have hright_nonpos :
      inner ℝ (d k) (gradient f (x k)) ≤ 0 := by
    rcases hDescentPair k with hpair | hpair
    · exact hpair.inner_right_nonpos
    · exact hpair.inner_right_nonpos
  have hreject_step :
      f (negativeCurvatureSearchPath (x k) (s k) (d k) a) >
        f (x k) + ρ * a ^ (2 : ℕ) *
          (inner ℝ (s k) (gradient f (x k)) +
            (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k)) := by
    -- Use the defining rejected-step inequality at exponent `backtrackingExponent k - 1`.
    have hraw := hreject (backtrackingExponent k - 1) (Nat.sub_lt hkexp (by decide))
    simpa [negativeCurvatureTrialPoint_eq_searchPath, ha, pow_mul, Nat.mul_comm,
      Nat.mul_left_comm, Nat.mul_assoc] using hraw
  have hnum_lower :
      ((1 - ρ) * negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k) *
          a ^ (2 : ℕ) ≤
        f (negativeCurvatureSearchPath (x k) (s k) (d k) a) - f (x k)
          - a * inner ℝ (d k) (gradient f (x k))
          + a ^ (2 : ℕ) * negativeCurvatureModelTerm
              (f := f) (x := x) (s := s) (d := d) k := by
    -- The rejected inequality gives the `ρ`-part, and the linear `d`-term is nonnegative after
    -- moving it to the left-hand side.
    dsimp [negativeCurvatureModelTerm] at *
    have hlinear_nonneg :
        0 ≤ -a * inner ℝ (d k) (gradient f (x k)) := by
      have : 0 ≤ a * (-inner ℝ (d k) (gradient f (x k))) := by
        exact mul_nonneg ha_pos.le (by linarith)
      linarith
    linarith
  -- Divide the source lower bound by the positive square `a^2`.
  exact (le_div_iff₀ hsq_pos).2 <| by
    simpa [mul_assoc, mul_left_comm, mul_comm]
      using hnum_lower

/-- Helper for Chapter03 Theorem 3.5.6: the quadratic search path can be rewritten as a linear
step from `x` in the perturbed direction `d + a • s`. -/
lemma negativeCurvature_searchPath_eq_add_smul_perturbedDirection
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x s d : E) (a : ℝ) :
    negativeCurvatureSearchPath x s d a = x + a • (d + a • s) := by
  -- This normalization matches the Chapter 2 line-search Taylor formula input.
  calc
    negativeCurvatureSearchPath x s d a = x + a • d + a ^ (2 : ℕ) • s := rfl
    _ = x + (a • d + a • (a • s)) := by
      simp [pow_two, smul_smul, add_assoc]
    _ = x + a • (d + a • s) := by
      simp [smul_add]

/-- Helper for Chapter03 Theorem 3.5.6: one uniform small step size keeps every quadratic trial
segment inside `D` and keeps the perturbed directions in a fixed closed ball. -/
lemma negativeCurvature_small_step_control
    (hD_open : IsOpen D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
    (hx_mem : ∀ k, x k ∈ D)
    (hs_bounded : Bornology.IsBounded (Set.range s))
    (hd_bounded : Bornology.IsBounded (Set.range d))
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)) :
    ∃ δ > 0, ∃ R ≥ 0, ∀ k {a : ℝ}, 0 ≤ a → a ≤ δ →
      segment ℝ (x k) (negativeCurvatureSearchPath (x k) (s k) (d k) a) ⊆ D ∧
        ‖d k + a • s k‖ ≤ R := by
  have hlevel_subset :
      negativeCurvatureLevelSet D f x₀ ⊆ D := fun _ hx ↦ hx.1
  obtain ⟨δ₀, hδ₀_pos, hδ₀_subset⟩ :=
    hLevelSetCompact.exists_cthickening_subset_open hD_open hlevel_subset
  obtain ⟨Rs, hRs_ball⟩ := hs_bounded.subset_closedBall (0 : E)
  obtain ⟨Rd, hRd_ball⟩ := hd_bounded.subset_closedBall (0 : E)
  have hRs_nonneg : 0 ≤ Rs := by
    have hs0 : s 0 ∈ Metric.closedBall (0 : E) Rs := hRs_ball ⟨0, rfl⟩
    have hs0' : ‖s 0‖ ≤ Rs := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hs0
    exact le_trans (norm_nonneg _) hs0'
  have hRd_nonneg : 0 ≤ Rd := by
    have hd0 : d 0 ∈ Metric.closedBall (0 : E) Rd := hRd_ball ⟨0, rfl⟩
    have hd0' : ‖d 0‖ ≤ Rd := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hd0
    exact le_trans (norm_nonneg _) hd0'
  let R : ℝ := max 1 (Rd + Rs)
  let δ : ℝ := min 1 (δ₀ / R)
  have hR_pos : 0 < R := by
    dsimp [R]
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (Rd + Rs))
  have hR_nonneg : 0 ≤ R := hR_pos.le
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min zero_lt_one (div_pos hδ₀_pos hR_pos)
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδ_mul_R_le : δ * R ≤ δ₀ := by
    have hδ_le : δ ≤ δ₀ / R := by
      dsimp [δ]
      exact min_le_right _ _
    exact (le_div_iff₀ hR_pos).1 hδ_le
  refine ⟨δ, hδ_pos, R, hR_nonneg, ?_⟩
  intro k a ha_nonneg ha_le
  have hk_level :
      x k ∈ negativeCurvatureLevelSet D f x₀ :=
    negativeCurvature_iterates_mem_levelSet
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hx_mem hLineSearch hDescentPair k
  have hs_norm :
      ‖s k‖ ≤ Rs := by
    have hs_mem : s k ∈ Metric.closedBall (0 : E) Rs := hRs_ball ⟨k, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hs_mem
  have hd_norm :
      ‖d k‖ ≤ Rd := by
    have hd_mem : d k ∈ Metric.closedBall (0 : E) Rd := hRd_ball ⟨k, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hd_mem
  have hvec_bound :
      ‖d k + a • s k‖ ≤ R := by
    have hnorm :
        ‖d k + a • s k‖ ≤ ‖d k‖ + ‖a • s k‖ :=
      norm_add_le _ _
    have has_le_one : a ≤ 1 := le_trans ha_le hδ_le_one
    calc
      ‖d k + a • s k‖ ≤ ‖d k‖ + ‖a • s k‖ := hnorm
      _ = ‖d k‖ + a * ‖s k‖ := by rw [norm_smul, Real.norm_of_nonneg ha_nonneg]
      _ ≤ Rd + a * Rs := by
        exact add_le_add hd_norm (mul_le_mul_of_nonneg_left hs_norm ha_nonneg)
      _ ≤ Rd + 1 * Rs := by
        have hm : a * Rs ≤ 1 * Rs :=
          mul_le_mul_of_nonneg_right has_le_one hRs_nonneg
        linarith
      _ ≤ R := by
        dsimp [R]
        have hsum : Rd + Rs ≤ max 1 (Rd + Rs) := le_max_right 1 (Rd + Rs)
        linarith
  have hstep_norm :
      ‖negativeCurvatureSearchPath (x k) (s k) (d k) a - x k‖ ≤ δ₀ := by
    calc
      ‖negativeCurvatureSearchPath (x k) (s k) (d k) a - x k‖
          = ‖a • (d k + a • s k)‖ := by
              rw [negativeCurvature_searchPath_eq_add_smul_perturbedDirection]
              simp
      _ = a * ‖d k + a • s k‖ := by
            rw [norm_smul, Real.norm_of_nonneg ha_nonneg]
      _ ≤ a * R := mul_le_mul_of_nonneg_left hvec_bound ha_nonneg
      _ ≤ δ * R := mul_le_mul_of_nonneg_right ha_le hR_nonneg
      _ ≤ δ₀ := hδ_mul_R_le
  constructor
  · -- The whole trial segment stays in the compact thickening around the level set.
    intro y hy
    have hy_ball : y ∈ Metric.closedBall (x k) δ₀ := by
      rw [Metric.mem_closedBall]
      simpa [dist_eq_norm] using (norm_sub_le_of_mem_segment hy).trans hstep_norm
    exact hδ₀_subset <| (Metric.closedBall_subset_cthickening hk_level δ₀) hy_ball
  · -- The perturbed directions remain uniformly bounded for all small trial steps.
    exact hvec_bound

/-- Helper for Chapter03 Theorem 3.5.6: Taylor's integral formula along the quadratic search path
rewrites the rejected-step numerator as the source `a²` remainder minus the base Hessian term. -/
lemma negativeCurvature_searchPath_taylor_remainder_formula
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (k : ℕ) {a : ℝ}
    (hsegment : segment ℝ (x k) (negativeCurvatureSearchPath (x k) (s k) (d k) a) ⊆ D) :
    f (negativeCurvatureSearchPath (x k) (s k) (d k) a) - f (x k)
      - a * inner ℝ (d k) (gradient f (x k))
      + a ^ (2 : ℕ) * negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k
      =
      a ^ (2 : ℕ) *
        ((∫ t in 0..1,
            (1 - t) *
              inner ℝ (d k + a • s k)
                ((fderiv ℝ (gradient f) (x k + (t * a) • (d k + a • s k)))
                  (d k + a • s k)))
          - (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k)) := by
  let v : E := d k + a • s k
  let remainder : ℝ :=
    ∫ t in 0..1,
      (1 - t) *
        inner ℝ v ((fderiv ℝ (gradient f) (x k + (t * a) • v)) v)
  have hsegment' : segment ℝ (x k) (x k + a • v) ⊆ D := by
    -- Normalize the quadratic path to the Chapter 2 ray `x + a • v`.
    simpa [v, negativeCurvature_searchPath_eq_add_smul_perturbedDirection] using hsegment
  have hTaylor :
      f (negativeCurvatureSearchPath (x k) (s k) (d k) a) =
        f (x k) + a * inner ℝ (gradient f (x k)) v + a ^ (2 : ℕ) * remainder := by
    -- Apply the Chapter 2 integral Taylor formula to the normalized ray.
    simpa [v, remainder, lineSearchObjective_apply,
      negativeCurvature_searchPath_eq_add_smul_perturbedDirection]
      using
        (lineTaylorFormula_withIntegralHessianRemainder
          (D := D) f (x k) v a hD_open hsegment' hC2)
  have hpair_expand :
      inner ℝ (gradient f (x k)) v =
        inner ℝ (d k) (gradient f (x k)) + a * inner ℝ (s k) (gradient f (x k)) := by
    -- Expand the perturbed direction into the source `d_k` and `a s_k` pieces.
    calc
      inner ℝ (gradient f (x k)) v = inner ℝ v (gradient f (x k)) := by
        rw [real_inner_comm]
      _ = inner ℝ (d k + a • s k) (gradient f (x k)) := by
        rfl
      _ = inner ℝ (d k) (gradient f (x k)) + inner ℝ (a • s k) (gradient f (x k)) := by
        rw [inner_add_left]
      _ = inner ℝ (d k) (gradient f (x k)) + a * inner ℝ (s k) (gradient f (x k)) := by
        simp
  -- Cancel the linear `d_k` term and the `a² * ⟪s_k, g_k⟫` contribution against the model term.
  calc
    f (negativeCurvatureSearchPath (x k) (s k) (d k) a) - f (x k)
        - a * inner ℝ (d k) (gradient f (x k))
        + a ^ (2 : ℕ) * negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k
        =
        (a * inner ℝ (gradient f (x k)) v + a ^ (2 : ℕ) * remainder)
          - a * inner ℝ (d k) (gradient f (x k))
          + a ^ (2 : ℕ) * negativeCurvatureModelTerm
              (f := f) (x := x) (s := s) (d := d) k := by
          linarith [hTaylor]
    _ = a ^ (2 : ℕ) * remainder
          - (1 / 2 : ℝ) * a ^ (2 : ℕ) * hessianQuadraticAt f (x k) (d k) := by
          rw [hpair_expand]
          dsimp [negativeCurvatureModelTerm]
          ring
    _ = a ^ (2 : ℕ) *
          (remainder - (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k)) := by
          ring
    _ = a ^ (2 : ℕ) *
          ((∫ t in 0..1,
              (1 - t) *
                inner ℝ (d k + a • s k)
                  ((fderiv ℝ (gradient f) (x k + (t * a) • (d k + a • s k)))
                    (d k + a • s k)))
            - (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k)) := by
          rfl

/-- Helper for Chapter03 Theorem 3.5.6: points on the normalized quadratic ray are points of the
corresponding search-path segment. -/
lemma negativeCurvature_searchPath_segmentPoint_mem
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x s d : ℕ → E)
    (k : ℕ) (a t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    x k + (t * a) • (d k + a • s k) ∈
      segment ℝ (x k) (negativeCurvatureSearchPath (x k) (s k) (d k) a) := by
  -- Rewrite the quadratic path endpoint into the normalized ray and use the standard segment
  -- parameterization by `lineMap`.
  have hmem :
      AffineMap.lineMap (x k) (negativeCurvatureSearchPath (x k) (s k) (d k) a) t ∈
        segment ℝ (x k) (negativeCurvatureSearchPath (x k) (s k) (d k) a) :=
    lineMap_mem_segment ℝ (x k) (negativeCurvatureSearchPath (x k) (s k) (d k) a) ht
  simpa [negativeCurvature_searchPath_eq_add_smul_perturbedDirection,
    AffineMap.lineMap_apply_module', smul_smul, mul_comm, mul_left_comm, mul_assoc,
    add_comm] using hmem

/-- Helper for Chapter03 Theorem 3.5.6: the scalar Taylor weight integrates to `1/2` on
`[0,1]`. -/
lemma negativeCurvature_weightIntegral_one_sub :
    (∫ t in (0 : ℝ)..1, (1 - t : ℝ)) = (1 / 2 : ℝ) := by
  -- Evaluate the scalar weight once so later remainder bounds can rewrite by a named lemma.
  calc
    ∫ t in (0 : ℝ)..1, (1 - t : ℝ)
        = ∫ t in (0 : ℝ)..1, ((1 : ℝ) - t) := by
            rfl
    _ = (∫ _ in (0 : ℝ)..1, (1 : ℝ)) - ∫ t in (0 : ℝ)..1, t := by
          rw [intervalIntegral.integral_sub]
          · exact Continuous.intervalIntegrable (by fun_prop) 0 1
          · exact Continuous.intervalIntegrable (by fun_prop) 0 1
    _ = (1 : ℝ) - (1 / 2 : ℝ) := by
          rw [integral_one, integral_id]
          norm_num
    _ = (1 / 2 : ℝ) := by
          norm_num

/-- Helper for Chapter03 Theorem 3.5.6: a constant Hessian contribution factors out of the
weighted interval integral. -/
lemma negativeCurvature_constantHessian_weightedIntegral
    (k : ℕ) (a : ℝ) :
    ∫ t in (0 : ℝ)..1,
        (1 - t) *
          inner ℝ (d k + a • s k)
            ((fderiv ℝ (gradient f) (x k)) (d k + a • s k))
      =
      (1 / 2 : ℝ) *
        inner ℝ (d k + a • s k)
          ((fderiv ℝ (gradient f) (x k)) (d k + a • s k)) := by
  let c : ℝ :=
    inner ℝ (d k + a • s k)
      ((fderiv ℝ (gradient f) (x k)) (d k + a • s k))
  -- Pull the constant quadratic form outside the integral and use the scalar weight identity.
  calc
    ∫ t in (0 : ℝ)..1,
        (1 - t) *
          inner ℝ (d k + a • s k)
            ((fderiv ℝ (gradient f) (x k)) (d k + a • s k))
        =
        ∫ t in (0 : ℝ)..1, c * (1 - t) := by
          apply intervalIntegral.integral_congr_ae
          filter_upwards with t
          simp [c, mul_comm]
    _ = c * ∫ t in (0 : ℝ)..1, (1 - t : ℝ) := by
          rw [intervalIntegral.integral_const_mul]
    _ = c * (1 / 2 : ℝ) := by
          rw [negativeCurvature_weightIntegral_one_sub]
    _ = (1 / 2 : ℝ) *
          inner ℝ (d k + a • s k)
            ((fderiv ℝ (gradient f) (x k)) (d k + a • s k)) := by
          simp [c, mul_comm]

/-- Helper for Chapter03 Theorem 3.5.6: after dividing by `a²`, the quadratic-path Taylor
remainder separates into a nearby-Hessian integral term and a base-point quadratic perturbation. -/
lemma negativeCurvature_normalizedRemainder_integral_form
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (k : ℕ) {a : ℝ} (ha : 0 < a)
    (hsegment : segment ℝ (x k) (negativeCurvatureSearchPath (x k) (s k) (d k) a) ⊆ D) :
    |(f (negativeCurvatureSearchPath (x k) (s k) (d k) a) - f (x k)
        - a * inner ℝ (d k) (gradient f (x k))
        + a ^ (2 : ℕ) * negativeCurvatureModelTerm
            (f := f) (x := x) (s := s) (d := d) k) / a ^ (2 : ℕ)|
      ≤
      |∫ t in 0..1,
          (1 - t) *
            inner ℝ (d k + a • s k)
              (((fderiv ℝ (gradient f) (x k + (t * a) • (d k + a • s k)))
                  - fderiv ℝ (gradient f) (x k))
                (d k + a • s k))|
        +
      |(1 / 2 : ℝ) *
          (inner ℝ (d k + a • s k)
              ((fderiv ℝ (gradient f) (x k)) (d k + a • s k))
            - hessianQuadraticAt f (x k) (d k))| := by
  let v : E := d k + a • s k
  let Hx : E →L[ℝ] E := fderiv ℝ (gradient f) (x k)
  let Ht : ℝ → E →L[ℝ] E := fun t ↦ fderiv ℝ (gradient f) (x k + (t * a) • v)
  have hsq_ne : a ^ (2 : ℕ) ≠ 0 := by
    positivity
  have hHess_cont : ContinuousOn (fun z ↦ fderiv ℝ (gradient f) z) D := by
    -- Rebuild the Hessian-field continuity locally so this helper stays dependency-closed.
    have hC1fderiv : ContDiffOn ℝ 1 (fderiv ℝ f) D := by
      simpa using hC2.fderiv_of_isOpen hD_open (by norm_num)
    have hC1grad : ContDiffOn ℝ 1 (gradient f) D := by
      change ContDiffOn ℝ 1
        (fun z ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z)) D
      exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn hC1fderiv
    exact hC1grad.continuousOn_fderiv_of_isOpen hD_open le_rfl
  have hHt_cont : ContinuousOn (fun t : ℝ ↦ Ht t) (Set.Icc (0 : ℝ) 1) := by
    -- Keep the Hessian field on the normalized segment, where `C²` gives continuity.
    refine hHess_cont.comp ?_ ?_
    · fun_prop
    · intro t ht
      exact hsegment <|
        negativeCurvature_searchPath_segmentPoint_mem
          (x := x) (s := s) (d := d) k a t ht
  have hdiffInt :
      IntervalIntegrable
        (fun t : ℝ ↦
          (1 - t) * inner ℝ v (((Ht t) - Hx) v))
        MeasureTheory.volume 0 1 := by
    -- The nearby-Hessian integrand is continuous on `[0,1]`, hence interval integrable.
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    have hEval :
        ContinuousOn (fun t : ℝ ↦ (((Ht t) - Hx) v)) (Set.Icc (0 : ℝ) 1) := by
      exact ContinuousOn.clm_apply (hHt_cont.sub continuousOn_const) continuousOn_const
    exact (continuousOn_const.sub continuousOn_id).mul (continuousOn_const.inner hEval)
  have hconstInt :
      IntervalIntegrable
        (fun t : ℝ ↦
          (1 - t) * inner ℝ v (Hx v))
        MeasureTheory.volume 0 1 := by
    -- The frozen-Hessian integrand is constant in the operator slot.
    exact Continuous.intervalIntegrable (by fun_prop) 0 1
  have hquot :
      (f (negativeCurvatureSearchPath (x k) (s k) (d k) a) - f (x k)
          - a * inner ℝ (d k) (gradient f (x k))
          + a ^ (2 : ℕ) * negativeCurvatureModelTerm
              (f := f) (x := x) (s := s) (d := d) k) /
        a ^ (2 : ℕ)
        =
      (∫ t in 0..1, (1 - t) * inner ℝ v ((Ht t) v))
        - (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k) := by
    -- Divide the exact Taylor remainder identity by the positive square `a²`.
    rw [negativeCurvature_searchPath_taylor_remainder_formula
      (D := D) (f := f) (x := x) (s := s) (d := d)
      hD_open hC2 k hsegment]
    simpa [v, Ht] using (mul_div_cancel_left₀
      ((∫ t in 0..1,
          (1 - t) *
            inner ℝ v ((Ht t) v))
        - (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k))
      hsq_ne)
  have hsplit :
      (∫ t in 0..1, (1 - t) * inner ℝ v ((Ht t) v))
        =
      (∫ t in 0..1, (1 - t) * inner ℝ v (((Ht t) - Hx) v))
        +
      ∫ t in 0..1, (1 - t) * inner ℝ v (Hx v) := by
    -- Split the Hessian into its nearby variation and the frozen base-point contribution.
    calc
      (∫ t in 0..1, (1 - t) * inner ℝ v ((Ht t) v))
          =
        ∫ t in 0..1,
          ((1 - t) * inner ℝ v (((Ht t) - Hx) v)
            + (1 - t) * inner ℝ v (Hx v)) := by
              apply intervalIntegral.integral_congr
              intro t ht
              calc
                (1 - t) * inner ℝ v ((Ht t) v)
                    = (1 - t) * inner ℝ v ((((Ht t) - Hx) v) + Hx v) := by
                        simp [Ht, Hx, sub_eq_add_neg, add_assoc]
                _ = (1 - t) * inner ℝ v (((Ht t) - Hx) v) +
                      (1 - t) * inner ℝ v (Hx v) := by
                        rw [inner_add_right, mul_add]
      _ =
        (∫ t in 0..1, (1 - t) * inner ℝ v (((Ht t) - Hx) v))
          + ∫ t in 0..1, (1 - t) * inner ℝ v (Hx v) := by
            rw [intervalIntegral.integral_add hdiffInt hconstInt]
  have hconst :
      ∫ t in 0..1, (1 - t) * inner ℝ v (Hx v)
        =
      (1 / 2 : ℝ) * inner ℝ v (Hx v) := by
    -- The frozen quadratic term factors out against the scalar weight integral.
    simpa [v, Hx] using
      negativeCurvature_constantHessian_weightedIntegral
        (f := f) (x := x) (s := s) (d := d) k a
  have hdecomp :
      (f (negativeCurvatureSearchPath (x k) (s k) (d k) a) - f (x k)
          - a * inner ℝ (d k) (gradient f (x k))
          + a ^ (2 : ℕ) * negativeCurvatureModelTerm
              (f := f) (x := x) (s := s) (d := d) k) /
        a ^ (2 : ℕ)
        =
      (∫ t in 0..1, (1 - t) * inner ℝ v (((Ht t) - Hx) v))
        +
      ((1 / 2 : ℝ) * inner ℝ v (Hx v)
        - (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k)) := by
    -- This is the bound-friendly remainder decomposition used by the later smallness estimate.
    calc
      (f (negativeCurvatureSearchPath (x k) (s k) (d k) a) - f (x k)
          - a * inner ℝ (d k) (gradient f (x k))
          + a ^ (2 : ℕ) * negativeCurvatureModelTerm
              (f := f) (x := x) (s := s) (d := d) k) /
        a ^ (2 : ℕ)
          =
        (∫ t in 0..1, (1 - t) * inner ℝ v ((Ht t) v))
          - (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k) := hquot
      _ =
        ((∫ t in 0..1, (1 - t) * inner ℝ v (((Ht t) - Hx) v))
          + ∫ t in 0..1, (1 - t) * inner ℝ v (Hx v))
          - (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k) := by
            rw [hsplit]
      _ =
        (∫ t in 0..1, (1 - t) * inner ℝ v (((Ht t) - Hx) v))
          + ((1 / 2 : ℝ) * inner ℝ v (Hx v)
              - (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k)) := by
            rw [hconst]
            ring
  -- Route correction: replace the brittle exact normal form with the stable two-piece bound.
  calc
    |(f (negativeCurvatureSearchPath (x k) (s k) (d k) a) - f (x k)
        - a * inner ℝ (d k) (gradient f (x k))
        + a ^ (2 : ℕ) * negativeCurvatureModelTerm
            (f := f) (x := x) (s := s) (d := d) k) / a ^ (2 : ℕ)|
        =
      |(∫ t in 0..1, (1 - t) * inner ℝ v (((Ht t) - Hx) v))
        + ((1 / 2 : ℝ) * inner ℝ v (Hx v)
            - (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k))| := by
          rw [hdecomp]
    _ ≤
      |∫ t in 0..1, (1 - t) * inner ℝ v (((Ht t) - Hx) v)| +
      |(1 / 2 : ℝ) * inner ℝ v (Hx v)
        - (1 / 2 : ℝ) * hessianQuadraticAt f (x k) (d k)| := by
          exact abs_add_le _ _
    _ ≤
      |∫ t in 0..1, (1 - t) * inner ℝ v (((Ht t) - Hx) v)| +
      |(1 / 2 : ℝ) *
          (inner ℝ v (Hx v) - hessianQuadraticAt f (x k) (d k))| := by
          rw [mul_sub]

/-- Helper for Chapter03 Theorem 3.5.6: the Hessian operator field
`x ↦ fderiv ℝ (gradient f) x` is continuous on the open domain `D`. -/
lemma negativeCurvature_hessianField_continuousOn
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D) :
    ContinuousOn (fun z ↦ fderiv ℝ (gradient f) z) D := by
  have hC1fderiv : ContDiffOn ℝ 1 (fderiv ℝ f) D := by
    -- Differentiate the `C²` objective once on the open domain.
    simpa using hC2.fderiv_of_isOpen hD_open (by norm_num)
  have hC1grad : ContDiffOn ℝ 1 (gradient f) D := by
    -- Rewrite the gradient as the Riesz representative of the Fréchet derivative.
    change ContDiffOn ℝ 1
      (fun z ↦ (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f z)) D
    exact (InnerProductSpace.toDual ℝ E).symm.contDiff.comp_contDiffOn hC1fderiv
  -- Differentiate the `C¹` gradient field once more to obtain continuity of the Hessian field.
  exact hC1grad.continuousOn_fderiv_of_isOpen hD_open le_rfl

/-- Helper for Chapter03 Theorem 3.5.6: compactness of the level set gives a uniform operator
norm bound for the Hessian field at all base points `x_k`. -/
lemma negativeCurvature_hessian_bound_on_levelSet
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀)) :
    ∃ M ≥ 0, ∀ {x'}, x' ∈ negativeCurvatureLevelSet D f x₀ →
      ‖fderiv ℝ (gradient f) x'‖ ≤ M := by
  have hcont_level :
      ContinuousOn (fun z ↦ fderiv ℝ (gradient f) z)
        (negativeCurvatureLevelSet D f x₀) := by
    -- Restrict the continuous Hessian field from `D` to the compact level set.
    exact
      (negativeCurvature_hessianField_continuousOn
        (D := D) (f := f)
        hD_open hC2).mono fun _ hx ↦ hx.1
  rcases hLevelSetCompact.exists_bound_of_continuousOn hcont_level with ⟨M, hM⟩
  refine ⟨max M 0, le_max_right _ _, ?_⟩
  intro x' hx'
  exact le_trans (hM x' hx') (le_max_left _ _)

/-- Helper for Chapter03 Theorem 3.5.6: continuity of the Hessian field on an open neighborhood
of the compact level set gives one uniform nearby operator-norm estimate. -/
lemma negativeCurvature_hessianField_near_levelSet
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀)) :
    ∀ ε > 0, ∃ δ > 0, ∀ {x' y' : E},
      x' ∈ negativeCurvatureLevelSet D f x₀ →
      dist y' x' ≤ δ →
      ‖fderiv ℝ (gradient f) y' - fderiv ℝ (gradient f) x'‖ ≤ ε := by
  intro ε hε
  let H : E → E →L[ℝ] E := fun z ↦ fderiv ℝ (gradient f) z
  have hcontAt :
      ∀ z ∈ negativeCurvatureLevelSet D f x₀, ContinuousAt H z := by
    intro z hz
    have hcont :
        ContinuousOn H D :=
      negativeCurvature_hessianField_continuousOn (D := D) (f := f) hD_open hC2
    exact hcont.continuousAt (hD_open.mem_nhds hz.1)
  have huniform :=
    hLevelSetCompact.uniformContinuousAt_of_continuousAt H hcontAt (Metric.dist_mem_uniformity hε)
  rcases Metric.mem_uniformity_dist.mp huniform with ⟨δ₀, hδ₀_pos, hδ₀⟩
  refine ⟨δ₀ / 2, half_pos hδ₀_pos, ?_⟩
  intro x' y' hx' hdist
  have hdist_lt : dist y' x' < δ₀ := lt_of_le_of_lt hdist (half_lt_self hδ₀_pos)
  have hdist_lt' : dist x' y' < δ₀ := by
    simpa [dist_comm] using hdist_lt
  have hclose : dist (H x') (H y') < ε := hδ₀ hdist_lt' hx'
  -- The entourage estimate is symmetric in the metric codomain, so it gives the desired norm bound.
  have hclose' : dist (H y') (H x') < ε := by
    simpa [dist_comm] using hclose
  have hclose'' : ‖fderiv ℝ (gradient f) y' - fderiv ℝ (gradient f) x'‖ < ε := by
    simpa [H, dist_eq_norm] using hclose'
  exact hclose''.le


/-- Helper for Chapter03 Theorem 3.5.6: if the nonnegative model term does not converge to `0`,
then some positive lower bound survives along a strictly monotone subsequence. -/
lemma negativeCurvature_modelTermSubsequence_ge_of_not_tendsto_zero
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))
    (hNot :
      ¬ Tendsto
        (fun k ↦ negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k)
        atTop (nhds 0)) :
    ∃ ε > 0, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ n, ε ≤ negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) (φ n) := by
  have hNotMetric :
      ¬ Tendsto
        (fun k ↦ negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k)
        atTop (nhds (0 : ℝ)) := hNot
  rw [Metric.tendsto_nhds] at hNotMetric
  push Not at hNotMetric
  rcases hNotMetric with ⟨ε, hε, hfreq⟩
  have hfreq_ge :
      ∃ᶠ k : ℕ in atTop,
        ε ≤ negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k := by
    refine hfreq.mono ?_
    intro k hk
    have hk' :
        ε ≤
          |negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k| := by
      simpa [Real.dist_eq] using hk
    have hnonneg :
        0 ≤ negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k :=
      negativeCurvature_model_term_nonneg
        (f := f) (x := x) (s := s) (d := d) hDescentPair k
    exact by
      rwa [abs_of_nonneg hnonneg] at hk'
  obtain ⟨φ, hφmono, hφfreq⟩ := extraction_of_frequently_atTop hfreq_ge
  refine ⟨ε, hε, φ, hφmono, ?_⟩
  intro n
  exact hφfreq n

/-- Helper for Chapter03 Theorem 3.5.6: the nearby-Hessian part of the normalized Taylor
remainder is uniformly small for all sufficiently small trial steps. -/
lemma negativeCurvature_nearbyHessianIntegral_small
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
    (hx_mem : ∀ k, x k ∈ D)
    (hs_bounded : Bornology.IsBounded (Set.range s))
    (hd_bounded : Bornology.IsBounded (Set.range d))
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)) :
    ∀ ε > 0, ∃ δ > 0, ∀ k {a : ℝ}, 0 < a → a ≤ δ →
      |∫ t in 0..1,
          (1 - t) *
            inner ℝ (d k + a • s k)
              (((fderiv ℝ (gradient f) (x k + (t * a) • (d k + a • s k)))
                  - fderiv ℝ (gradient f) (x k))
                (d k + a • s k))| ≤ ε := by
  intro ε hε
  obtain ⟨δ₀, hδ₀_pos, R, hR_nonneg, hstep⟩ :=
    negativeCurvature_small_step_control
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hD_open hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  let η : ℝ := ε / (R ^ (2 : ℕ) + 1)
  have hη_pos : 0 < η := by
    dsimp [η]
    positivity
  obtain ⟨δ₁, hδ₁_pos, hnear⟩ :=
    negativeCurvature_hessianField_near_levelSet
      (D := D) (f := f) (x₀ := x₀)
      hD_open hC2 hLevelSetCompact η hη_pos
  let δ : ℝ := min δ₀ (δ₁ / (R + 1))
  have hR_add_pos : 0 < R + 1 := by linarith
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min hδ₀_pos (div_pos hδ₁_pos hR_add_pos)
  refine ⟨δ, hδ_pos, ?_⟩
  intro k a ha ha_le
  let v : E := d k + a • s k
  let Hx : E →L[ℝ] E := fderiv ℝ (gradient f) (x k)
  let Ht : ℝ → E →L[ℝ] E := fun t ↦ fderiv ℝ (gradient f) (x k + (t * a) • v)
  have ha_le_δ₀ : a ≤ δ₀ := by
    exact le_trans ha_le (min_le_left _ _)
  have ha_le_δ₁ : a ≤ δ₁ / (R + 1) := by
    exact le_trans ha_le (min_le_right _ _)
  rcases hstep k ha.le ha_le_δ₀ with ⟨hsegment, hv_bound⟩
  have hk_level :
      x k ∈ negativeCurvatureLevelSet D f x₀ :=
    negativeCurvature_iterates_mem_levelSet
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hx_mem hLineSearch hDescentPair k
  have hHess_cont :
      ContinuousOn (fun z ↦ fderiv ℝ (gradient f) z) D :=
    negativeCurvature_hessianField_continuousOn
      (D := D) (f := f)
      hD_open hC2
  have hHt_cont : ContinuousOn (fun t : ℝ ↦ Ht t) (Set.Icc (0 : ℝ) 1) := by
    -- Keep the Hessian field on the normalized segment where Taylor's formula lives.
    refine hHess_cont.comp ?_ ?_
    · fun_prop
    · intro t ht
      exact hsegment <|
        negativeCurvature_searchPath_segmentPoint_mem
          (x := x) (s := s) (d := d) k a t ht
  have hF_cont :
      ContinuousOn
        (fun t : ℝ ↦
          (1 - t) * inner ℝ v (((Ht t) - Hx) v))
        (Set.Icc (0 : ℝ) 1) := by
    -- The nearby-Hessian integrand is continuous on `[0,1]`.
    have hEval :
        ContinuousOn (fun t : ℝ ↦ (((Ht t) - Hx) v)) (Set.Icc (0 : ℝ) 1) := by
      exact ContinuousOn.clm_apply (hHt_cont.sub continuousOn_const) continuousOn_const
    exact (continuousOn_const.sub continuousOn_id).mul (continuousOn_const.inner hEval)
  have hAbsInt :
      IntervalIntegrable
        (fun t : ℝ ↦
          |(1 - t) * inner ℝ v (((Ht t) - Hx) v)|)
        MeasureTheory.volume 0 1 := by
    -- Absolute values preserve continuity, hence interval integrability.
    apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
    exact hF_cont.abs
  have hBoundInt :
      IntervalIntegrable
        (fun t : ℝ ↦ (1 - t) * (η * R ^ (2 : ℕ)))
        MeasureTheory.volume 0 1 := by
    -- The comparison function is a scalar multiple of the fixed weight `1 - t`.
    exact Continuous.intervalIntegrable (by fun_prop) 0 1
  have hpointDist :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        dist (x k + (t * a) • v) (x k) ≤ δ₁ := by
    intro t ht
    have hmem :
        x k + (t * a) • v ∈
          segment ℝ (x k) (negativeCurvatureSearchPath (x k) (s k) (d k) a) := by
      simpa [v] using
        negativeCurvature_searchPath_segmentPoint_mem
          (x := x) (s := s) (d := d) k a t ht
    have hendpoint :
        ‖negativeCurvatureSearchPath (x k) (s k) (d k) a - x k‖ ≤ a * R := by
      calc
        ‖negativeCurvatureSearchPath (x k) (s k) (d k) a - x k‖
            = ‖a • v‖ := by
                rw [negativeCurvature_searchPath_eq_add_smul_perturbedDirection]
                simp [v]
        _ = a * ‖v‖ := by
              rw [norm_smul, Real.norm_of_nonneg ha.le]
        _ ≤ a * R := by
              gcongr
    calc
      dist (x k + (t * a) • v) (x k)
          = ‖(x k + (t * a) • v) - x k‖ := by
              rw [dist_eq_norm]
      _ ≤ ‖negativeCurvatureSearchPath (x k) (s k) (d k) a - x k‖ := by
            simpa [sub_eq_add_neg] using norm_sub_le_of_mem_segment hmem
      _ ≤ a * R := hendpoint
      _ ≤ a * (R + 1) := by
            gcongr
            linarith
      _ ≤ δ * (R + 1) := by
            gcongr
      _ ≤ (δ₁ / (R + 1)) * (R + 1) := by
            exact mul_le_mul_of_nonneg_right (min_le_right _ _) hR_add_pos.le
      _ = δ₁ := by
            field_simp [hR_add_pos.ne']
  have hpointBound :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |(1 - t) * inner ℝ v (((Ht t) - Hx) v)| ≤
          (1 - t) * (η * R ^ (2 : ℕ)) := by
    intro t ht
    have ht_weight_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hHt_norm :
        ‖Ht t - Hx‖ ≤ η := by
      exact hnear hk_level (hpointDist t ht)
    have hinner :
        |inner ℝ v (((Ht t) - Hx) v)| ≤ η * R ^ (2 : ℕ) := by
      calc
        |inner ℝ v (((Ht t) - Hx) v)|
            ≤ ‖v‖ * ‖((Ht t) - Hx) v‖ := by
                simpa [Real.norm_eq_abs] using
                  (norm_inner_le_norm (𝕜 := ℝ) v (((Ht t) - Hx) v))
        _ ≤ ‖v‖ * (‖Ht t - Hx‖ * ‖v‖) := by
              gcongr
              exact (Ht t - Hx).le_opNorm v
        _ ≤ R * (η * R) := by
              gcongr
        _ = η * R ^ (2 : ℕ) := by
              ring
    calc
      |(1 - t) * inner ℝ v (((Ht t) - Hx) v)|
          = |1 - t| * |inner ℝ v (((Ht t) - Hx) v)| := by
              rw [abs_mul]
      _ = (1 - t) * |inner ℝ v (((Ht t) - Hx) v)| := by
            rw [abs_of_nonneg ht_weight_nonneg]
      _ ≤ (1 - t) * (η * R ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hinner ht_weight_nonneg
  have hmono :
      ∫ t in 0..1,
          |(1 - t) * inner ℝ v (((Ht t) - Hx) v)|
        ≤
      ∫ t in 0..1, (1 - t) * (η * R ^ (2 : ℕ)) := by
    -- Compare the absolute integrand with its uniform scalar upper bound.
    exact intervalIntegral.integral_mono_on zero_le_one hAbsInt hBoundInt hpointBound
  have hweight :
      ∫ t in 0..1, (1 - t) * (η * R ^ (2 : ℕ))
        = (η * R ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
    -- The scalar bound factors through the already-computed weight integral.
    calc
      ∫ t in 0..1, (1 - t) * (η * R ^ (2 : ℕ))
          = ∫ t in 0..1, (η * R ^ (2 : ℕ)) * (1 - t : ℝ) := by
              apply intervalIntegral.integral_congr
              intro t ht
              ring
      _ = (η * R ^ (2 : ℕ)) * ∫ t in 0..1, (1 - t : ℝ) := by
            rw [intervalIntegral.integral_const_mul]
      _ = (η * R ^ (2 : ℕ)) * (1 / 2 : ℝ) := by
            rw [negativeCurvature_weightIntegral_one_sub]
  have hweight_le : (η * R ^ (2 : ℕ)) * (1 / 2 : ℝ) ≤ ε := by
    -- The modulus `η = ε / (R² + 1)` is chosen so that the resulting bound stays below `ε`.
    have hη_bound : η * R ^ (2 : ℕ) ≤ ε := by
      have hden_pos : 0 < R ^ (2 : ℕ) + 1 := by positivity
      have hmul :
          (ε / (R ^ (2 : ℕ) + 1)) * R ^ (2 : ℕ) ≤
            (ε / (R ^ (2 : ℕ) + 1)) * (R ^ (2 : ℕ) + 1) := by
        apply mul_le_mul_of_nonneg_left
        · nlinarith [sq_nonneg R]
        · positivity
      have hcancel :
          (ε / (R ^ (2 : ℕ) + 1)) * (R ^ (2 : ℕ) + 1) = ε := by
        field_simp [hden_pos.ne']
      simpa [η, hcancel] using hmul
    calc
      (η * R ^ (2 : ℕ)) * (1 / 2 : ℝ) ≤ η * R ^ (2 : ℕ) := by
        nlinarith [hη_bound, hε]
      _ ≤ ε := hη_bound
  calc
    |∫ t in 0..1,
        (1 - t) * inner ℝ (d k + a • s k)
          (((fderiv ℝ (gradient f) (x k + (t * a) • (d k + a • s k)))
              - fderiv ℝ (gradient f) (x k))
            (d k + a • s k))|
        =
      |∫ t in 0..1, (1 - t) * inner ℝ v (((Ht t) - Hx) v)| := by
          simp [v, Ht, Hx]
    _ ≤
      ∫ t in 0..1, |(1 - t) * inner ℝ v (((Ht t) - Hx) v)| := by
        exact intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in 0..1, (1 - t) * (η * R ^ (2 : ℕ)) := hmono
    _ = (η * R ^ (2 : ℕ)) * (1 / 2 : ℝ) := hweight
    _ ≤ ε := hweight_le

/-- Helper for Chapter03 Theorem 3.5.6: the frozen base-Hessian quadratic perturbation is
uniformly small for all sufficiently small trial steps. -/
lemma negativeCurvature_baseQuadraticPerturbation_small
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
    (hx_mem : ∀ k, x k ∈ D)
    (hs_bounded : Bornology.IsBounded (Set.range s))
    (hd_bounded : Bornology.IsBounded (Set.range d))
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)) :
    ∀ ε > 0, ∃ δ > 0, ∀ k {a : ℝ}, 0 ≤ a → a ≤ δ →
      |(1 / 2 : ℝ) *
          (inner ℝ (d k + a • s k)
              ((fderiv ℝ (gradient f) (x k)) (d k + a • s k))
            - hessianQuadraticAt f (x k) (d k))| ≤ ε := by
  intro ε hε
  obtain ⟨Rs, hRs_ball⟩ := hs_bounded.subset_closedBall (0 : E)
  obtain ⟨Rd, hRd_ball⟩ := hd_bounded.subset_closedBall (0 : E)
  have hRs_nonneg : 0 ≤ Rs := by
    have hs0 : s 0 ∈ Metric.closedBall (0 : E) Rs := hRs_ball ⟨0, rfl⟩
    have hs0' : ‖s 0‖ ≤ Rs := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hs0
    exact le_trans (norm_nonneg _) hs0'
  have hRd_nonneg : 0 ≤ Rd := by
    have hd0 : d 0 ∈ Metric.closedBall (0 : E) Rd := hRd_ball ⟨0, rfl⟩
    have hd0' : ‖d 0‖ ≤ Rd := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hd0
    exact le_trans (norm_nonneg _) hd0'
  obtain ⟨M, hM_nonneg, hM_bound⟩ :=
    negativeCurvature_hessian_bound_on_levelSet
      (D := D) (f := f) (x₀ := x₀)
      hD_open hC2 hLevelSetCompact
  let C : ℝ := Rd * (M * Rs) + Rs * (M * Rd) + Rs * (M * Rs)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  let δ : ℝ := min 1 (ε / (C + 1))
  have hC_add_pos : 0 < C + 1 := by linarith
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    exact lt_min zero_lt_one (div_pos hε hC_add_pos)
  refine ⟨δ, hδ_pos, ?_⟩
  intro k a ha_nonneg ha_le
  let v : E := d k + a • s k
  let Hx : E →L[ℝ] E := fderiv ℝ (gradient f) (x k)
  have hk_level :
      x k ∈ negativeCurvatureLevelSet D f x₀ :=
    negativeCurvature_iterates_mem_levelSet
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hx_mem hLineSearch hDescentPair k
  have hs_norm : ‖s k‖ ≤ Rs := by
    have hs_mem : s k ∈ Metric.closedBall (0 : E) Rs := hRs_ball ⟨k, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hs_mem
  have hd_norm : ‖d k‖ ≤ Rd := by
    have hd_mem : d k ∈ Metric.closedBall (0 : E) Rd := hRd_ball ⟨k, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using hd_mem
  have hHx_norm : ‖Hx‖ ≤ M := by
    exact hM_bound hk_level
  have ha_le_one : a ≤ 1 := by
    exact le_trans ha_le (min_le_left _ _)
  have hcrossLeft :
      |inner ℝ (d k) (Hx (a • s k))| ≤ a * (Rd * (M * Rs)) := by
    -- Bound the mixed term with `d_k` on the left by the operator norm of the base Hessian.
    calc
      |inner ℝ (d k) (Hx (a • s k))|
          ≤ ‖d k‖ * ‖Hx (a • s k)‖ := by
              simpa [Real.norm_eq_abs] using
                (norm_inner_le_norm (𝕜 := ℝ) (d k) (Hx (a • s k)))
      _ ≤ ‖d k‖ * (‖Hx‖ * ‖a • s k‖) := by
            gcongr
            exact Hx.le_opNorm (a • s k)
      _ = ‖d k‖ * (‖Hx‖ * (a * ‖s k‖)) := by
            rw [norm_smul, Real.norm_of_nonneg ha_nonneg]
      _ ≤ Rd * (M * (a * Rs)) := by
            gcongr
      _ = a * (Rd * (M * Rs)) := by
            ring
  have hcrossRight :
      |inner ℝ (a • s k) (Hx (d k))| ≤ a * (Rs * (M * Rd)) := by
    -- Bound the symmetric mixed term with `a • s_k` on the left.
    calc
      |inner ℝ (a • s k) (Hx (d k))|
          ≤ ‖a • s k‖ * ‖Hx (d k)‖ := by
              simpa [Real.norm_eq_abs] using
                (norm_inner_le_norm (𝕜 := ℝ) (a • s k) (Hx (d k)))
      _ ≤ ‖a • s k‖ * (‖Hx‖ * ‖d k‖) := by
            gcongr
            exact Hx.le_opNorm (d k)
      _ = (a * ‖s k‖) * (‖Hx‖ * ‖d k‖) := by
            rw [norm_smul, Real.norm_of_nonneg ha_nonneg]
      _ ≤ (a * Rs) * (M * Rd) := by
            gcongr
      _ = a * (Rs * (M * Rd)) := by
            ring
  have hquadratic :
      |inner ℝ (a • s k) (Hx (a • s k))| ≤ a * (Rs * (M * Rs)) := by
    -- The pure `a²` term is controlled by `a ≤ 1`.
    calc
      |inner ℝ (a • s k) (Hx (a • s k))|
          ≤ ‖a • s k‖ * ‖Hx (a • s k)‖ := by
              simpa [Real.norm_eq_abs] using
                (norm_inner_le_norm (𝕜 := ℝ) (a • s k) (Hx (a • s k)))
      _ ≤ ‖a • s k‖ * (‖Hx‖ * ‖a • s k‖) := by
            gcongr
            exact Hx.le_opNorm (a • s k)
      _ = (a * ‖s k‖) * (‖Hx‖ * (a * ‖s k‖)) := by
            simp [norm_smul, Real.norm_of_nonneg ha_nonneg]
      _ ≤ (a * Rs) * (M * (a * Rs)) := by
            gcongr
      _ = a * a * (Rs * (M * Rs)) := by
            ring
      _ ≤ a * (Rs * (M * Rs)) := by
            have hRsMRs_nonneg : 0 ≤ Rs * (M * Rs) := by positivity
            have haa : a * a ≤ a := by nlinarith [ha_nonneg, ha_le_one]
            simpa [mul_assoc] using mul_le_mul_of_nonneg_right haa hRsMRs_nonneg
  have hexpand :
      inner ℝ v (Hx v) - hessianQuadraticAt f (x k) (d k)
        =
      inner ℝ (d k) (Hx (a • s k))
        + inner ℝ (a • s k) (Hx (d k))
        + inner ℝ (a • s k) (Hx (a • s k)) := by
    -- Route correction: expand around `v = d_k + a s_k` instead of forcing a fragile normal form.
    calc
      inner ℝ v (Hx v) - hessianQuadraticAt f (x k) (d k)
          =
        inner ℝ (d k + a • s k) (Hx (d k) + Hx (a • s k))
          - inner ℝ (d k) (Hx (d k)) := by
              simp [v, Hx, hessianQuadraticAt, hessianAt]
      _ =
        inner ℝ (d k) (Hx (a • s k))
          + inner ℝ (a • s k) (Hx (d k))
          + inner ℝ (a • s k) (Hx (a • s k)) := by
              simp [inner_add_left, inner_add_right, sub_eq_add_neg, add_assoc, add_left_comm]
              ring
  have hdiff :
      |inner ℝ v (Hx v) - hessianQuadraticAt f (x k) (d k)| ≤ a * C := by
    -- Triangle inequality reduces the perturbation to the three algebraic pieces above.
    calc
      |inner ℝ v (Hx v) - hessianQuadraticAt f (x k) (d k)|
          =
        |(inner ℝ (d k) (Hx (a • s k)) + inner ℝ (a • s k) (Hx (d k)))
          + inner ℝ (a • s k) (Hx (a • s k))| := by
              rw [hexpand]
      _ ≤
        |inner ℝ (d k) (Hx (a • s k)) + inner ℝ (a • s k) (Hx (d k))|
          + |inner ℝ (a • s k) (Hx (a • s k))| := by
              exact abs_add_le _ _
      _ ≤
        (|inner ℝ (d k) (Hx (a • s k))| + |inner ℝ (a • s k) (Hx (d k))|)
          + |inner ℝ (a • s k) (Hx (a • s k))| := by
              gcongr
              exact abs_add_le _ _
      _ ≤
        (a * (Rd * (M * Rs)) + a * (Rs * (M * Rd)))
          + a * (Rs * (M * Rs)) := by
              gcongr
      _ = a * C := by
            ring
  have hscaled :
      |(1 / 2 : ℝ) *
          (inner ℝ v (Hx v) - hessianQuadraticAt f (x k) (d k))| ≤
        a * C := by
    -- The front factor `1/2` only improves the perturbation estimate.
    calc
      |(1 / 2 : ℝ) * (inner ℝ v (Hx v) - hessianQuadraticAt f (x k) (d k))|
          = (1 / 2 : ℝ) * |inner ℝ v (Hx v) - hessianQuadraticAt f (x k) (d k)| := by
              rw [abs_mul, abs_of_nonneg (by norm_num)]
      _ ≤ (1 / 2 : ℝ) * (a * C) := by
            gcongr
      _ ≤ a * C := by
            nlinarith [ha_nonneg, hC_nonneg]
  calc
    |(1 / 2 : ℝ) *
        (inner ℝ (d k + a • s k)
            ((fderiv ℝ (gradient f) (x k)) (d k + a • s k))
          - hessianQuadraticAt f (x k) (d k))|
        =
      |(1 / 2 : ℝ) * (inner ℝ v (Hx v) - hessianQuadraticAt f (x k) (d k))| := by
          simp [v, Hx]
    _ ≤ a * C := hscaled
    _ ≤ δ * C := by
          gcongr
    _ ≤ δ * (C + 1) := by
          nlinarith [hδ_pos.le, hC_nonneg]
    _ ≤ (ε / (C + 1)) * (C + 1) := by
          exact mul_le_mul_of_nonneg_right (min_le_right _ _) hC_add_pos.le
    _ = ε := by
          field_simp [hC_add_pos.ne']

/-- Helper for Chapter03 Theorem 3.5.6: after dividing by `a²`, the Taylor remainder along a
small rejected quadratic trial step is uniformly small on the compact level-set neighborhood. -/
lemma negativeCurvature_normalizedRemainder_small
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
    (hx_mem : ∀ k, x k ∈ D)
    (hs_bounded : Bornology.IsBounded (Set.range s))
    (hd_bounded : Bornology.IsBounded (Set.range d))
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)) :
    ∀ ε > 0, ∃ δ > 0, ∀ k {a : ℝ}, 0 < a → a ≤ δ →
      |(f (negativeCurvatureSearchPath (x k) (s k) (d k) a) - f (x k)
          - a * inner ℝ (d k) (gradient f (x k))
          + a ^ (2 : ℕ) * negativeCurvatureModelTerm
              (f := f) (x := x) (s := s) (d := d) k) / a ^ (2 : ℕ)| ≤ ε := by
  intro ε hε
  obtain ⟨δ₀, hδ₀_pos, R, hR_nonneg, hstep⟩ :=
    negativeCurvature_small_step_control
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hD_open hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ :=
    negativeCurvature_nearbyHessianIntegral_small
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hD_open hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
      (ε / 2) (by positivity)
  obtain ⟨δ₂, hδ₂_pos, hδ₂⟩ :=
    negativeCurvature_baseQuadraticPerturbation_small
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hD_open hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
      (ε / 2) (by positivity)
  refine ⟨min δ₀ (min δ₁ δ₂), lt_min hδ₀_pos (lt_min hδ₁_pos hδ₂_pos), ?_⟩
  intro k a ha ha_le
  have ha_le_δ₀ : a ≤ δ₀ := by
    exact le_trans ha_le (min_le_left _ _)
  have ha_le_δ₁ : a ≤ δ₁ := by
    exact le_trans ha_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have ha_le_δ₂ : a ≤ δ₂ := by
    exact le_trans ha_le (le_trans (min_le_right _ _) (min_le_right _ _))
  have hsmallStep :=
    hδ₁ k ha ha_le_δ₁
  have hbaseStep :=
    hδ₂ k ha.le ha_le_δ₂
  rcases hstep k ha.le ha_le_δ₀ with ⟨hsegment, _⟩
  -- Route correction: assemble the two analytic estimates instead of reviving the old exact
  -- post-division scalar normalization.
  calc
    |(f (negativeCurvatureSearchPath (x k) (s k) (d k) a) - f (x k)
        - a * inner ℝ (d k) (gradient f (x k))
        + a ^ (2 : ℕ) * negativeCurvatureModelTerm
            (f := f) (x := x) (s := s) (d := d) k) / a ^ (2 : ℕ)|
        ≤
      |∫ t in 0..1,
          (1 - t) *
            inner ℝ (d k + a • s k)
              (((fderiv ℝ (gradient f) (x k + (t * a) • (d k + a • s k)))
                  - fderiv ℝ (gradient f) (x k))
                (d k + a • s k))|
        +
      |(1 / 2 : ℝ) *
          (inner ℝ (d k + a • s k)
              ((fderiv ℝ (gradient f) (x k)) (d k + a • s k))
            - hessianQuadraticAt f (x k) (d k))| := by
          exact negativeCurvature_normalizedRemainder_integral_form
            (D := D) (f := f) (x := x) (s := s) (d := d)
            hD_open hC2 k ha hsegment
    _ ≤ ε / 2 + ε / 2 := by
          gcongr
    _ = ε := by ring

/-- Helper for Chapter03 Theorem 3.5.6: a bad subsequence with uniformly bounded backtracking
exponents contradicts the fact that the accepted objective gaps tend to `0`. -/
lemma negativeCurvature_boundedExponentBranch_contradiction
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
    (hx_mem : ∀ k, x k ∈ D)
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))
    {ε : ℝ} {β : ℕ} {φ : ℕ → ℕ}
    (hε_pos : 0 < ε)
    (hφmono : StrictMono φ)
    (hφlb : ∀ n, ε ≤ negativeCurvatureModelTerm
      (f := f) (x := x) (s := s) (d := d) (φ n))
    (hβ : ∀ n, backtrackingExponent (φ n) ≤ β) :
    False := by
  have hLineSearchSeq := hLineSearch
  rcases hLineSearch with ⟨hρ, hγ, _, _⟩
  have hgap :
      Tendsto (fun k ↦ f (x (k)) - f (x (k + 1))) atTop (nhds 0) :=
    negativeCurvature_decrease_gap_tendsto_zero
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hC2 hLevelSetCompact hx_mem hLineSearchSeq hDescentPair
  have hgapSub :
      Tendsto (fun n ↦ f (x (φ n)) - f (x (φ n + 1))) atTop (nhds 0) :=
    hgap.comp hφmono.tendsto_atTop
  let c : ℝ := ρ * γ ^ (2 * β : ℕ) * ε
  have hc_pos : 0 < c := by
    -- The source fixed-gap constant is positive because `ρ`, `γ`, and `ε` are positive.
    dsimp [c]
    have hpow_pos : 0 < γ ^ (2 * β : ℕ) := pow_pos hγ.1 _
    exact mul_pos (mul_pos hρ.1 hpow_pos) hε_pos
  rw [Metric.tendsto_nhds] at hgapSub
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hgapSub c hc_pos)
  set gap : ℝ := f (x (φ N)) - f (x (φ N + 1))
  have hgap_small : |gap| < c := by
    -- The subsequence of accepted gaps must still converge to `0`.
    simpa [gap, Real.dist_eq] using hN N le_rfl
  have hgap_lower : c ≤ gap := by
    -- The bounded branch of the source argument gives a uniform positive lower gap.
    simpa [c, gap] using
      negativeCurvature_bounded_exponent_branch_forces_gap
        (f := f) (x := x) (s := s) (d := d)
        (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
        ε β hLineSearchSeq hDescentPair hφlb hβ N
  have hgap_nonneg : 0 ≤ gap := le_trans hc_pos.le hgap_lower
  have hgap_abs : c ≤ |gap| := by
    -- Since the gap is nonnegative, the absolute value does not change it.
    simpa [abs_of_nonneg hgap_nonneg] using hgap_lower
  exact (not_lt_of_ge hgap_abs) hgap_small

/-- Helper for Chapter03 Theorem 3.5.6: if the accepted exponents on a subsequence tend to
`atTop`, then the rejected step sizes `γ^(i_k - 1)` are eventually positive and arbitrarily
small. -/
lemma negativeCurvature_rejectedStepSize_eventually_pos_le
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    {κ : ℕ → ℕ}
    (hκexp : Tendsto (fun n ↦ backtrackingExponent (κ n)) atTop atTop)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      0 < γ ^ (backtrackingExponent (κ n) - 1) ∧
        γ ^ (backtrackingExponent (κ n) - 1) ≤ δ := by
  rcases hLineSearch with ⟨_, hγ, _, _⟩
  have hpow :
      Tendsto (fun n : ℕ ↦ γ ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hγ.1) hγ.2
  rw [Metric.tendsto_nhds] at hpow
  have hpow_eventually : ∀ᶠ m in atTop, γ ^ m < δ := by
    -- The geometric tail `γ^m` tends to `0`, so it eventually falls below `δ`.
    refine (hpow δ hδ).mono ?_
    intro m hm
    have hm' : |γ ^ m| < δ := by
      simpa [Real.dist_eq] using hm
    simpa [abs_of_nonneg (pow_nonneg hγ.1.le _)] using hm'
  obtain ⟨N, hNpow⟩ := Filter.eventually_atTop.1 hpow_eventually
  have hexp_eventually : ∀ᶠ n in atTop, N + 1 ≤ backtrackingExponent (κ n) :=
    (tendsto_atTop.1 hκexp) (N + 1)
  refine hexp_eventually.mono ?_
  intro n hn
  have hN_le_pred : N ≤ backtrackingExponent (κ n) - 1 := by
    -- One step beyond `N` on the exponent scale is enough to compare with `γ^N`.
    omega
  have hpow_mono :
      γ ^ (backtrackingExponent (κ n) - 1) ≤ γ ^ N :=
    (pow_right_strictAnti₀ hγ.1 hγ.2).le_iff_ge.2 hN_le_pred
  have hpowN : γ ^ N < δ := hNpow N le_rfl
  constructor
  · -- Every rejected step size is still positive because `0 < γ`.
    exact pow_pos hγ.1 _
  · exact le_of_lt (lt_of_le_of_lt hpow_mono hpowN)

/-- Helper for Chapter03 Theorem 3.5.6: on a subsequence with unbounded accepted exponents, the
rejected-step lower bound contradicts the uniform smallness of the normalized Taylor remainder. -/
lemma negativeCurvature_unboundedExponentBranch_contradiction
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
    (hx_mem : ∀ k, x k ∈ D)
    (hs_bounded : Bornology.IsBounded (Set.range s))
    (hd_bounded : Bornology.IsBounded (Set.range d))
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))
    {ε : ℝ} {κ : ℕ → ℕ}
    (hε_pos : 0 < ε)
    (hκexp : Tendsto (fun n ↦ backtrackingExponent (κ n)) atTop atTop)
    (hκlb : ∀ n, ε ≤ negativeCurvatureModelTerm
      (f := f) (x := x) (s := s) (d := d) (κ n)) :
    False := by
  have hLineSearchSeq := hLineSearch
  rcases hLineSearch with ⟨hρ, _, _, _⟩
  let η : ℝ := ((1 - ρ) * ε) / 2
  have hη_pos : 0 < η := by
    -- The contradiction budget is positive because `ρ ∈ (0,1)` and `ε > 0`.
    dsimp [η]
    have h1ρ_pos : 0 < 1 - ρ := sub_pos.mpr hρ.2
    exact div_pos (mul_pos h1ρ_pos hε_pos) two_pos
  obtain ⟨δ, hδ_pos, hδ⟩ :=
    negativeCurvature_normalizedRemainder_small
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hD_open hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearchSeq hDescentPair
      η hη_pos
  have hstep_eventually :
      ∀ᶠ n in atTop,
        0 < γ ^ (backtrackingExponent (κ n) - 1) ∧
          γ ^ (backtrackingExponent (κ n) - 1) ≤ δ :=
    negativeCurvature_rejectedStepSize_eventually_pos_le
      (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hLineSearchSeq hκexp hδ_pos
  have hkexp_eventually : ∀ᶠ n in atTop, 0 < backtrackingExponent (κ n) := by
    -- Tending to `atTop` forces the accepted exponents to be eventually positive.
    refine ((tendsto_atTop.1 hκexp) 1).mono ?_
    intro n hn
    exact Nat.succ_le_iff.mp hn
  obtain ⟨N, hN⟩ :=
    Filter.eventually_atTop.1 (hstep_eventually.and hkexp_eventually)
  have hbudget_pos : 0 < (1 - ρ) * ε := by
    have h1ρ_pos : 0 < 1 - ρ := sub_pos.mpr hρ.2
    exact mul_pos h1ρ_pos hε_pos
  have hscale_nonneg : 0 ≤ 1 - ρ := by
    exact sub_nonneg.mpr hρ.2.le
  have htail := hN N le_rfl
  rcases htail with ⟨hstepN, hkexpN⟩
  set a : ℝ := γ ^ (backtrackingExponent (κ N) - 1) with ha
  set expr : ℝ :=
      (f (negativeCurvatureSearchPath (x (κ N)) (s (κ N)) (d (κ N)) a)
          - f (x (κ N))
          - a * inner ℝ (d (κ N)) (gradient f (x (κ N)))
          + a ^ (2 : ℕ) * negativeCurvatureModelTerm
              (f := f) (x := x) (s := s) (d := d) (κ N)) /
        a ^ (2 : ℕ) with hexpr
  have ha_pos : 0 < a := by
    -- The chosen rejected step size lies on the positive geometric scale.
    simpa [ha] using hstepN.1
  have ha_le : a ≤ δ := by
    simpa [ha] using hstepN.2
  have hrem : |expr| ≤ η := by
    simpa [expr, hexpr] using hδ (κ N) ha_pos ha_le
  have hmodel_lower :
      (1 - ρ) * negativeCurvatureModelTerm
          (f := f) (x := x) (s := s) (d := d) (κ N) ≤
        expr := by
    simpa [expr, hexpr] using
    negativeCurvature_rejected_step_model_lower_bound
      (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      (κ N) hkexpN hLineSearchSeq hDescentPair ha
  have hlower :
      (1 - ρ) * ε ≤ expr := by
    -- Multiply the uniform model lower bound by the positive factor `1 - ρ`.
    exact le_trans (mul_le_mul_of_nonneg_left (hκlb N) hscale_nonneg) hmodel_lower
  have hexpr_nonneg : 0 ≤ expr :=
    le_trans hbudget_pos.le hlower
  have hupper : expr ≤ η := by
    -- The normalized remainder bound controls the same expression from above.
    exact (abs_le.mp hrem).2
  have hupper' : expr ≤ ((1 - ρ) * ε) / 2 := by
    simpa [η] using hupper
  exact by
    -- The lower bound `(1 - ρ) ε` cannot fit under half of itself.
    nlinarith

/-- Chapter03 Theorem 3.5.6: once the source two-case backtracking argument is carried out, the
combined model term converges to `0`; the two source conclusions then follow by squeezing the
first- and second-order terms against this quantity. -/
lemma negativeCurvature_model_term_tendsto_zero
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
    (hx_mem : ∀ k, x k ∈ D)
    (hs_bounded : Bornology.IsBounded (Set.range s))
    (hd_bounded : Bornology.IsBounded (Set.range d))
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)) :
    Tendsto (fun k ↦ negativeCurvatureModelTerm
      (f := f) (x := x) (s := s) (d := d) k) atTop (nhds 0) := by
  -- Route correction: the normalized remainder estimate is now available, so the remaining work
  -- is purely the source two-branch subsequence contradiction.
  by_contra hNot
  obtain ⟨ε, hε_pos, φ, hφmono, hφlb⟩ :=
    negativeCurvature_modelTermSubsequence_ge_of_not_tendsto_zero
      (f := f) (x := x) (s := s) (d := d) hDescentPair hNot
  by_cases hbdd : BddAbove (Set.range fun n ↦ backtrackingExponent (φ n))
  · rcases hbdd with ⟨β, hβ⟩
    -- The bounded branch reproduces the textbook fixed-gap contradiction.
    exact negativeCurvature_boundedExponentBranch_contradiction
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hC2 hLevelSetCompact hx_mem hLineSearch hDescentPair hε_pos hφmono hφlb
      (fun n ↦ hβ ⟨n, rfl⟩)
  · obtain ⟨ψ, _, hψexp⟩ :=
      unbounded_nat_subsequence_tendsto_atTop
        (u := fun n ↦ backtrackingExponent (φ n)) hbdd
    let κ : ℕ → ℕ := fun n ↦ φ (ψ n)
    have hκexp : Tendsto (fun n ↦ backtrackingExponent (κ n)) atTop atTop := by
      -- Reindex the unbounded exponent branch onto a single common subsequence.
      change Tendsto (((fun n ↦ backtrackingExponent (φ n)) ∘ ψ)) atTop atTop
      simpa [κ, Function.comp] using hψexp
    have hκlb : ∀ n, ε ≤ negativeCurvatureModelTerm
        (f := f) (x := x) (s := s) (d := d) (κ n) := by
      -- The positive model lower bound persists along the refined subsequence.
      intro n
      exact hφlb (ψ n)
    exact negativeCurvature_unboundedExponentBranch_contradiction
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hD_open hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
      hε_pos hκexp hκlb

/-- Helper for Chapter03 Theorem 3.5.6: the negative first-order pairing is squeezed by the
combined model term. -/
lemma negativeCurvature_neg_gradientPairing_bounds
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))
    (k : ℕ) :
    0 ≤ -inner ℝ (s k) (gradient f (x k)) ∧
      -inner ℝ (s k) (gradient f (x k)) ≤
        negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k := by
  have hleft_nonpos :
      inner ℝ (s k) (gradient f (x k)) ≤ 0 :=
    IsDescentPairAt.inner_left_nonpos (hDescentPair k)
  have hcurv_nonpos :
      hessianQuadraticAt f (x k) (d k) ≤ 0 :=
    IsDescentPairAt.hessianQuadratic_nonpos (hDescentPair k)
  constructor
  · -- Negating the nonpositive gradient pairing makes it nonnegative.
    linarith
  · -- The curvature contribution only increases the nonnegative model term.
    dsimp [negativeCurvatureModelTerm]
    linarith

/-- Helper for Chapter03 Theorem 3.5.6: the negative curvature quadratic term is controlled by
twice the combined model term. -/
lemma negativeCurvature_neg_curvature_bounds
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))
    (k : ℕ) :
    0 ≤ -hessianQuadraticAt f (x k) (d k) ∧
      -hessianQuadraticAt f (x k) (d k) ≤
        2 * negativeCurvatureModelTerm (f := f) (x := x) (s := s) (d := d) k := by
  have hleft_nonpos :
      inner ℝ (s k) (gradient f (x k)) ≤ 0 :=
    IsDescentPairAt.inner_left_nonpos (hDescentPair k)
  have hcurv_nonpos :
      hessianQuadraticAt f (x k) (d k) ≤ 0 :=
    IsDescentPairAt.hessianQuadratic_nonpos (hDescentPair k)
  constructor
  · -- Negating the nonpositive quadratic term makes it nonnegative.
    linarith
  · -- Doubling the model term absorbs the curvature contribution.
    dsimp [negativeCurvatureModelTerm]
    linarith

/-- First conclusion of Chapter03 Theorem 3.5.6: formalized on a real inner product space `E`,
this is the
source statement for the negative-curvature direction method on `ℝⁿ`. Assume `f` is twice
continuously differentiable on the open set `D`, the level set `{x ∈ D | f x ≤ f x₀}` is
compact. If the iterates `x_k` stay in `D`, the search sequences `s_k` and `d_k` are
bounded, each pair `(s_k, d_k)` is an admissible descent pair at `x_k`, and the
backtracking exponents satisfy `(3.5.30)` and `(3.5.31)`, then `g_kᵀ s_k → 0`, written in
Lean as `inner ℝ (s k) (gradient f (x k)) → 0`. -/
theorem negativeCurvatureDirectionMethod_gradientPairing_tendsto_zero
    (D : Set E) (f : E → ℝ) (x s d : ℕ → E) (backtrackingExponent : ℕ → ℕ)
    (x₀ : E) (ρ γ : ℝ)
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
    (hx_mem : ∀ k, x k ∈ D)
    (hs_bounded : Bornology.IsBounded (Set.range s))
    (hd_bounded : Bornology.IsBounded (Set.range d))
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)) :
    Tendsto (fun k ↦ inner ℝ (s k) (gradient f (x k))) atTop (nhds 0) := by
  -- Follow the source through the combined model term, then squeeze the first-order term.
  have hmodel :
      Tendsto (fun k ↦ negativeCurvatureModelTerm
        (f := f) (x := x) (s := s) (d := d) k) atTop (nhds 0) :=
    negativeCurvature_model_term_tendsto_zero
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hD_open hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  have hneg_pairing :
      Tendsto (fun k ↦ -inner ℝ (s k) (gradient f (x k))) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmodel
      (fun k ↦
        (negativeCurvature_neg_gradientPairing_bounds
          (f := f) (x := x) (s := s) (d := d) hDescentPair k).1)
      (fun k ↦
        (negativeCurvature_neg_gradientPairing_bounds
          (f := f) (x := x) (s := s) (d := d) hDescentPair k).2)
  -- Negating the squeezed nonnegative sequence recovers the stated convergence.
  simpa using hneg_pairing.neg

/-- Second conclusion of Chapter03 Theorem 3.5.6: under the same hypotheses on `x`, `s`, `d`,
`ρ`, and `γ`,
the curvature terms `d_kᵀ G_k d_k` converge to `0`, written in Lean as
`hessianQuadraticAt f (x k) (d k) → 0`. -/
theorem negativeCurvatureDirectionMethod_curvature_tendsto_zero
    (D : Set E) (f : E → ℝ) (x s d : ℕ → E) (backtrackingExponent : ℕ → ℕ)
    (x₀ : E) (ρ γ : ℝ)
    (hD_open : IsOpen D)
    (hC2 : ContDiffOn ℝ 2 f D)
    (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
    (hx_mem : ∀ k, x k ∈ D)
    (hs_bounded : Bornology.IsBounded (Set.range s))
    (hd_bounded : Bornology.IsBounded (Set.range d))
    (hLineSearch :
      IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
    (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k)) :
    Tendsto (fun k ↦ hessianQuadraticAt f (x k) (d k)) atTop (nhds 0) := by
  -- Reuse the same source model term and squeeze the quadratic contribution.
  have hmodel :
      Tendsto (fun k ↦ negativeCurvatureModelTerm
        (f := f) (x := x) (s := s) (d := d) k) atTop (nhds 0) :=
    negativeCurvature_model_term_tendsto_zero
      (D := D) (f := f) (x := x) (s := s) (d := d)
      (backtrackingExponent := backtrackingExponent) (x₀ := x₀) (ρ := ρ) (γ := γ)
      hD_open hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  have htwo_model :
      Tendsto (fun k ↦ 2 * negativeCurvatureModelTerm
        (f := f) (x := x) (s := s) (d := d) k) atTop (nhds 0) := by
    -- Scaling a null sequence by a constant preserves convergence to `0`.
    simpa using tendsto_const_nhds.mul hmodel
  have hneg_curvature :
      Tendsto (fun k ↦ -hessianQuadraticAt f (x k) (d k)) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htwo_model
      (fun k ↦
        (negativeCurvature_neg_curvature_bounds
          (f := f) (x := x) (s := s) (d := d) hDescentPair k).1)
      (fun k ↦
        (negativeCurvature_neg_curvature_bounds
          (f := f) (x := x) (s := s) (d := d) hDescentPair k).2)
  -- Negating back yields the claimed convergence of the quadratic terms themselves.
  simpa using hneg_curvature.neg

end NegativeCurvatureDirectionMethod
