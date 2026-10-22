/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap08.Example_8_27
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_16
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_42
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_4_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Corollary_17_48
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

/-- A reset-walk parameter sequence is a sequence of one-step upward-jump probabilities `p_n`
lying in the interval `[0, 1]`. -/
def IsResetWalkProbabilitySequence (p : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 ≤ p n ∧ p n ≤ 1

/-- The source data of the reset walk: a probability sequence `(p_n)` for the upward move
`n ↦ n + 1`, with reset probability `1 - p_n`. -/
abbrev ResetWalkParameters := {p : ℕ → ℝ // IsResetWalkProbabilitySequence p}

instance : CoeFun ResetWalkParameters (fun _ ↦ ℕ → ℝ) :=
  ⟨Subtype.val⟩

/- Layering for Example 17.52:
- source-facing data: the probability sequence `(p_n)`, its prefix products, and the chain-level
  recurrence criteria for realizations of the reset walk;
- core/canonical owner: the stochastic matrix `resetWalkTransitionMatrix p`, its discrete kernel
  `resetWalkKernel p`, and invariant measures expressed by `Kernel.Invariant`;
- bridge/view data: the weighted counting measure attached to the explicit singleton masses
  `c ∏_{k < n} p_k`. -/

/-- The stochastic transition matrix of the upward-jump/reset-to-zero chain determined by the
probability sequence `(p_n)`. -/
def resetWalkTransitionMatrix (p : ResetWalkParameters) : ℕ → ℕ → ℝ≥0∞ :=
  fun x y ↦
    if y = x + 1 then
      ENNReal.ofReal (p x)
    else if y = 0 then
      ENNReal.ofReal (1 - p x)
    else
      0

-- Proof sketch: unfold `resetWalkTransitionMatrix`; this is exactly the piecewise definition of
-- the example's one-step probabilities.
/-- Evaluating the reset-walk transition matrix reproduces the textbook piecewise formula. -/
theorem resetWalkTransitionMatrix_apply (p : ResetWalkParameters) (x y : ℕ) :
    resetWalkTransitionMatrix p x y =
      if y = x + 1 then ENNReal.ofReal (p x) else
        if y = 0 then ENNReal.ofReal (1 - p x) else 0 := rfl

-- Proof sketch: for the row at `x`, only the entries at `x + 1` and `0` are nonzero, and their
-- masses are `p_x` and `1 - p_x`, which add up to `1`.
/-- The reset-walk transition matrix is stochastic. -/
theorem resetWalkTransitionMatrix_isStochasticMatrix (p : ResetWalkParameters) :
    IsStochasticMatrix (resetWalkTransitionMatrix p) := by
  intro x
  have hp_nonneg : 0 ≤ p x := (p.property x).1
  have hp_le_one : p x ≤ 1 := (p.property x).2
  have hxsucc : x + 1 ≠ 0 := Nat.succ_ne_zero x
  have hdecomp :
      ∀ y : ℕ,
        resetWalkTransitionMatrix p x y =
          (if y = x + 1 then ENNReal.ofReal (p x) else 0) +
            (if y = 0 then ENNReal.ofReal (1 - p x) else 0) := by
    intro y
    by_cases hysucc : y = x + 1
    · simp [resetWalkTransitionMatrix, hysucc, hxsucc]
    · by_cases hy0 : y = 0
      · simp [resetWalkTransitionMatrix, hysucc, hy0]
      · simp [resetWalkTransitionMatrix, hysucc, hy0]
  -- Proof comment: the only nonzero entries in row `x` occur at `x + 1` and `0`.
  calc
    ∑' y : ℕ, resetWalkTransitionMatrix p x y
      = ∑' y : ℕ,
          ((if y = x + 1 then ENNReal.ofReal (p x) else 0) +
            (if y = 0 then ENNReal.ofReal (1 - p x) else 0)) := by
          refine tsum_congr fun y ↦ hdecomp y
    _ = (∑' y : ℕ, if y = x + 1 then ENNReal.ofReal (p x) else 0) +
          ∑' y : ℕ, if y = 0 then ENNReal.ofReal (1 - p x) else 0 := by
          rw [ENNReal.tsum_add]
    _ = ENNReal.ofReal (p x) + ENNReal.ofReal (1 - p x) := by
          simp [tsum_eq_single, hxsucc]
    _ = ENNReal.ofReal (p x + (1 - p x)) := by
          simpa [add_assoc] using
            (ENNReal.ofReal_add hp_nonneg (sub_nonneg.mpr hp_le_one)).symm
    _ = 1 := by
          simp

/-- The chapter-canonical discrete kernel attached to the reset walk. -/
def resetWalkKernel (p : ResetWalkParameters) : Kernel ℕ ℕ :=
  discreteMatrixKernel (resetWalkTransitionMatrix p)

/-- The reset-walk kernel carries the canonical Markov-kernel instance. -/
instance (p : ResetWalkParameters) : IsMarkovKernel (resetWalkKernel p) :=
  discreteMatrixKernel_isMarkovKernel _ (resetWalkTransitionMatrix_isStochasticMatrix p)

/-- The finite prefix product `∏_{k=0}^{n-1} p_k`. -/
def resetWalkPrefixProduct (p : ResetWalkParameters) (n : ℕ) : ℝ :=
  Finset.prod (Finset.range n) p

-- Proof sketch: every factor `p_k` is nonnegative, so the finite product is nonnegative.
/-- The reset-walk prefix products are nonnegative. -/
theorem resetWalkPrefixProduct_nonneg (p : ResetWalkParameters) (n : ℕ) :
    0 ≤ resetWalkPrefixProduct p n := by
  -- Proof comment: every factor `p k` lies in `[0, 1]`, so the finite product is nonnegative.
  exact Finset.prod_nonneg fun k _ ↦ (p.property k).1

/-- Helper for Example 17.52: if every step probability `p_n` is strictly positive, then every
finite prefix product is strictly positive as well. -/
lemma resetWalkPrefixProduct_pos
    (p : ResetWalkParameters) (hp : ∀ n : ℕ, 0 < p n) (n : ℕ) :
    0 < resetWalkPrefixProduct p n := by
  -- Proof comment: the prefix product is a finite product of strictly positive factors.
  exact Finset.prod_pos fun k _ ↦ hp k

/-- The `ℝ≥0∞`-valued prefix product attached to the reset walk. -/
def resetWalkPrefixProductENNReal (p : ResetWalkParameters) (n : ℕ) : ℝ≥0∞ :=
  ((show NNReal from ⟨resetWalkPrefixProduct p n, resetWalkPrefixProduct_nonneg p n⟩) : ℝ≥0∞)

/-- Helper for Example 17.52: the `ℝ≥0∞` prefix product is just the `ofReal` image of the
underlying nonnegative real product. -/
lemma resetWalkPrefixProductENNReal_eq_ofReal
    (p : ResetWalkParameters) (n : ℕ) :
    resetWalkPrefixProductENNReal p n = ENNReal.ofReal (resetWalkPrefixProduct p n) := by
  -- Proof comment: both sides are the canonical `ℝ≥0∞` coercion of the same nonnegative real.
  simpa [resetWalkPrefixProductENNReal] using
    (ENNReal.coe_nnreal_eq
      (show NNReal from ⟨resetWalkPrefixProduct p n, resetWalkPrefixProduct_nonneg p n⟩))

-- Proof sketch: unfold `resetWalkPrefixProduct`; the empty product equals `1`.
/-- The zeroth prefix product is `1`. -/
theorem resetWalkPrefixProduct_zero (p : ResetWalkParameters) :
    resetWalkPrefixProduct p 0 = 1 := by
  simp [resetWalkPrefixProduct]

-- Proof sketch: unfold `resetWalkPrefixProduct`; extending the range from `n` to `n + 1`
-- multiplies by the new factor `p n`.
/-- The prefix products satisfy the one-step recursion `a_{n+1} = a_n p_n`. -/
theorem resetWalkPrefixProduct_succ (p : ResetWalkParameters) (n : ℕ) :
    resetWalkPrefixProduct p (n + 1) = resetWalkPrefixProduct p n * p n := by
  simp [resetWalkPrefixProduct, Finset.prod_range_succ]

/-- The series `M = ∑_{n=0}^∞ ∏_{k=0}^{n-1} p_k` attached to the chain, taken in `ℝ≥0∞` so that
divergent cases retain the value `∞`. -/
def resetWalkMassSeries (p : ResetWalkParameters) : ℝ≥0∞ :=
  ∑' n : ℕ, resetWalkPrefixProductENNReal p n

-- Proof sketch: unfold `resetWalkMassSeries`; it is defined as the `ℝ≥0∞`-sum of the
-- prefix-product sequence.
/-- The extended mass series is the `ℝ≥0∞`-sum of the reset-walk prefix products. -/
theorem resetWalkMassSeries_eq_tsum (p : ResetWalkParameters) :
    resetWalkMassSeries p = ∑' n : ℕ, resetWalkPrefixProductENNReal p n := rfl

/-- The explicit singleton-mass profile `μ {n} = c ∏_{k < n} p_k` attached to an initial mass
`c`. -/
def resetWalkInvariantMass (p : ResetWalkParameters) (c : ℝ≥0∞) : ℕ → ℝ≥0∞ :=
  fun n ↦ c * resetWalkPrefixProductENNReal p n

/-- The weighted counting measure on `ℕ` with singleton masses
`resetWalkInvariantMass p c`. -/
def resetWalkInvariantMeasure (p : ResetWalkParameters) (c : ℝ≥0∞) : Measure ℕ :=
  Measure.count.withDensity (resetWalkInvariantMass p c)

-- Proof sketch: unfold `resetWalkInvariantMass`; the singleton mass at `n` is the initial mass
-- `c` multiplied by the prefix product up to `n - 1`.
/-- The explicit singleton-mass profile is given pointwise by the prefix-product formula. -/
theorem resetWalkInvariantMass_apply (p : ResetWalkParameters) (c : ℝ≥0∞) (n : ℕ) :
    resetWalkInvariantMass p c n = c * resetWalkPrefixProductENNReal p n := rfl

-- Proof sketch: on the discrete state space `ℕ`, `Measure.count.withDensity` evaluates on a
-- singleton `{n}` as the density value at `n`.
/-- The weighted counting measure `resetWalkInvariantMeasure p c` has singleton mass
`resetWalkInvariantMass p c n` at `{n}`. -/
theorem resetWalkInvariantMeasure_apply_singleton
    (p : ResetWalkParameters) (c : ℝ≥0∞) (n : ℕ) :
    resetWalkInvariantMeasure p c {n} = resetWalkInvariantMass p c n := by
  -- Proof comment: on the discrete state space `ℕ`, `withDensity` over counting measure
  -- evaluates a singleton by the density at that state.
  rw [resetWalkInvariantMeasure, withDensity_apply _ (measurableSet_singleton n),
    ← lintegral_indicator (measurableSet_singleton n), lintegral_count]
  simp [resetWalkInvariantMass]

/-- Helper for Example 17.52: the `ℝ≥0∞`-valued prefix products satisfy the same one-step
recursion as the underlying real prefix products. -/
lemma resetWalkPrefixProductENNReal_succ
    (p : ResetWalkParameters) (n : ℕ) :
    resetWalkPrefixProductENNReal p (n + 1) =
      resetWalkPrefixProductENNReal p n * ENNReal.ofReal (p n) := by
  -- Proof comment: move the real recursion through `ENNReal.ofReal` using nonnegativity of both
  -- factors.
  have hleft :
      resetWalkPrefixProductENNReal p (n + 1) =
        ((show NNReal from
          ⟨resetWalkPrefixProduct p n * p n,
            mul_nonneg (resetWalkPrefixProduct_nonneg p n) (p.property n).1⟩) : ℝ≥0∞) := by
    simp [resetWalkPrefixProductENNReal, resetWalkPrefixProduct_succ]
  calc
    resetWalkPrefixProductENNReal p (n + 1)
      = ((show NNReal from
          ⟨resetWalkPrefixProduct p n * p n,
            mul_nonneg (resetWalkPrefixProduct_nonneg p n) (p.property n).1⟩) : ℝ≥0∞) := hleft
    _ = resetWalkPrefixProductENNReal p n * ENNReal.ofReal (p n) := by
          let a : NNReal := ⟨resetWalkPrefixProduct p n, resetWalkPrefixProduct_nonneg p n⟩
          let b : NNReal := ⟨p n, (p.property n).1⟩
          calc
            ((show NNReal from
                ⟨resetWalkPrefixProduct p n * p n,
                  mul_nonneg (resetWalkPrefixProduct_nonneg p n) (p.property n).1⟩) : ℝ≥0∞)
              = ((a * b : NNReal) : ℝ≥0∞) := by
                  rfl
            _ = (a : ℝ≥0∞) * (b : ℝ≥0∞) := by
                  simpa using (ENNReal.coe_mul a b)
            _ = (a : ℝ≥0∞) * ENNReal.ofReal (p n) := by
                  have hb : (b : ℝ≥0∞) = ENNReal.ofReal (p n) := by
                    simpa [b] using (ENNReal.coe_nnreal_eq b)
                  rw [hb]
            _ = resetWalkPrefixProductENNReal p n * ENNReal.ofReal (p n) := by
                  simp [a, resetWalkPrefixProductENNReal]

/-- Helper for Example 17.52: evaluating the reset-walk transition matrix at target `0` produces
the reset probability `1 - p_y`. -/
lemma resetWalkTransitionMatrix_apply_zero
    (p : ResetWalkParameters) (y : ℕ) :
    resetWalkTransitionMatrix p y 0 = ENNReal.ofReal (1 - p y) := by
  -- Proof comment: `0` can never be the successor target `y + 1`, so only the reset branch
  -- remains.
  rw [resetWalkTransitionMatrix]
  simp

/-- Helper for Example 17.52: the only incoming edge to `n + 1` comes from the predecessor `n`. -/
lemma resetWalkTransitionMatrix_apply_succ
    (p : ResetWalkParameters) (n y : ℕ) :
    resetWalkTransitionMatrix p y (n + 1) = if y = n then ENNReal.ofReal (p n) else 0 := by
  by_cases hy : y = n
  · -- Proof comment: at the predecessor `n`, the upward-jump branch contributes exactly `p_n`.
    subst hy
    simp [resetWalkTransitionMatrix]
  · -- Proof comment: away from the predecessor, neither the successor branch nor the reset branch
    -- reaches `n + 1`.
    have hsucc : n + 1 ≠ y + 1 := by
      intro h
      exact hy (Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using h.symm))
    have hyn : n ≠ y := by
      simpa [eq_comm] using hy
    simp [resetWalkTransitionMatrix, hsucc, hy, hyn]

/-- Helper for Example 17.52: on the countable discrete state space `ℕ`, invariance of the
reset-walk kernel is equivalent to the singleton balance equations. -/
lemma resetWalkKernel_invariant_iff_singletonBalance
    (p : ResetWalkParameters) (μ : Measure ℕ) :
    Kernel.Invariant (resetWalkKernel p) μ ↔
      ∀ x : ℕ, ∑' y : ℕ, μ {y} * resetWalkTransitionMatrix p y x = μ {x} := by
  constructor
  · intro h x
    -- Proof comment: evaluate the invariant-measure identity on the singleton `{x}`.
    have hx :
        (μ.bind (resetWalkKernel p)) ({x} : Set ℕ) = μ ({x} : Set ℕ) :=
      congrArg (fun ν : Measure ℕ ↦ ν ({x} : Set ℕ)) h
    simpa [resetWalkKernel, comp_discreteMatrixKernel_apply_singleton_eq_tsum] using hx
  · intro h
    -- Proof comment: on `ℕ`, equality of all singleton masses determines the measure.
    refine Measure.ext_of_singleton fun x ↦ ?_
    simpa [resetWalkKernel, comp_discreteMatrixKernel_apply_singleton_eq_tsum] using h x

-- Proof sketch: evaluate the stationarity equation on singletons. The resulting recursion
-- `μ {n + 1} = p_n μ {n}` forces the singleton masses to match the explicit prefix-product
-- profile with `c = μ {0}`.
/-- Any invariant measure for the reset walk is determined by its singleton mass at `0` and the
prefix-product formula. -/
theorem invariant_singletonMass_eq_resetWalkInvariantMass
    (p : ResetWalkParameters) (μ : Measure ℕ) (hμ : Kernel.Invariant (resetWalkKernel p) μ)
    (n : ℕ) :
    μ {n} = resetWalkInvariantMass p (μ {0}) n := by
  have hbalance := (resetWalkKernel_invariant_iff_singletonBalance p μ).mp hμ
  induction n with
  | zero =>
      -- Proof comment: the explicit profile is normalized so that the zeroth singleton mass is
      -- exactly the chosen base mass `μ {0}`.
      change μ {0} = μ {0} * ((1 : NNReal) : ℝ≥0∞)
      simp
  | succ n ih =>
      -- Proof comment: at target `n + 1`, only the predecessor `n` can contribute incoming mass.
      calc
        μ ({n + 1} : Set ℕ)
          = ∑' y : ℕ, μ {y} * resetWalkTransitionMatrix p y (n + 1) := by
              symm
              exact hbalance (n + 1)
        _ = ∑' y : ℕ, μ {y} * (if y = n then ENNReal.ofReal (p n) else 0) := by
              refine tsum_congr fun y ↦ ?_
              rw [resetWalkTransitionMatrix_apply_succ]
        _ = μ {n} * ENNReal.ofReal (p n) := by
              simp [tsum_eq_single n]
        _ = resetWalkInvariantMass p (μ {0}) n * ENNReal.ofReal (p n) := by
              rw [ih]
        _ = resetWalkInvariantMass p (μ {0}) (n + 1) := by
              rw [resetWalkInvariantMass_apply, resetWalkInvariantMass_apply,
                resetWalkPrefixProductENNReal_succ, mul_assoc]

/-- Helper for Example 17.52: the finite defect sums telescope to `1 - ∏_{k < N} p_k`. -/
lemma resetWalkDefect_sum_eq_one_sub_prefixProduct
    (p : ResetWalkParameters) (N : ℕ) :
    Finset.sum (Finset.range N) (fun k ↦ (1 - p k) * resetWalkPrefixProduct p k) =
      1 - resetWalkPrefixProduct p N := by
  induction N with
  | zero =>
      -- Proof comment: the empty defect sum is `0`, and the zeroth prefix product is `1`.
      simp [resetWalkPrefixProduct_zero]
  | succ N ih =>
      -- Proof comment: add the next defect term and collapse the algebra with the prefix-product
      -- recursion `a_{N+1} = a_N p_N`.
      calc
        Finset.sum (Finset.range (N + 1)) (fun k ↦ (1 - p k) * resetWalkPrefixProduct p k)
          = Finset.sum (Finset.range N) (fun k ↦ (1 - p k) * resetWalkPrefixProduct p k) +
              (1 - p N) * resetWalkPrefixProduct p N := by
                rw [Finset.sum_range_succ]
        _ = 1 - resetWalkPrefixProduct p N + (1 - p N) * resetWalkPrefixProduct p N := by
              rw [ih]
        _ = 1 - (resetWalkPrefixProduct p N * p N) := by
              ring
        _ = 1 - resetWalkPrefixProduct p (N + 1) := by
              rw [resetWalkPrefixProduct_succ]

/-- Helper for Example 17.52: the finite prefix products converge to the infinite product
`∏' n, p n`. -/
lemma resetWalkPrefixProduct_tendsto_tprod
    (p : ResetWalkParameters) :
    Filter.Tendsto (fun N : ℕ ↦ resetWalkPrefixProduct p N) Filter.atTop
      (𝓝 (∏' n : ℕ, p n)) := by
  let q : ℕ → NNReal := fun n ↦ ⟨p n, (p.property n).1⟩
  have hq_le_one : ∀ n : ℕ, q n ≤ 1 := fun n ↦ by
    exact (p.property n).2
  have hq_multipliable : Multipliable q := by
    -- Proof comment: nonnegative factors bounded by `1` are multipliable in `ℝ≥0`.
    let s : Set NNReal := Set.range fun t : Finset ℕ ↦ ∏ i ∈ t, q i
    have hs_nonempty : s.Nonempty := by
      refine ⟨1, ?_⟩
      refine ⟨∅, ?_⟩
      simp [s]
    have hs_bddBelow : BddBelow s := ⟨0, by
      rintro _ ⟨t, rfl⟩
      exact zero_le _⟩
    refine ⟨sInf s, ?_⟩
    exact hasProd_of_isGLB_of_le_one _
      hq_le_one (isGLB_csInf hs_nonempty hs_bddBelow)
  have hq_real :
      Filter.Tendsto (fun N : ℕ ↦ ∏ i ∈ Finset.range N, (q i : ℝ)) Filter.atTop
        (𝓝 (∏' n : ℕ, (q n : ℝ))) := by
    -- Proof comment: transport the convergent `ℝ≥0` product to `ℝ`.
    exact (hq_multipliable.map NNReal.toRealHom NNReal.continuous_coe).tendsto_prod_tprod_nat
  simpa [q, resetWalkPrefixProduct]
    using hq_real

/-- Helper for Example 17.52: the defect series has sum `1 - ∏' n, p n`. -/
lemma resetWalkDefectHasSum
    (p : ResetWalkParameters) :
    HasSum (fun n : ℕ ↦ (1 - p n) * resetWalkPrefixProduct p n) (1 - ∏' n : ℕ, p n) := by
  have hdefect_nonneg : ∀ n : ℕ, 0 ≤ (1 - p n) * resetWalkPrefixProduct p n := fun n ↦ by
    exact mul_nonneg (sub_nonneg.mpr (p.property n).2) (resetWalkPrefixProduct_nonneg p n)
  rw [hasSum_iff_tendsto_nat_of_nonneg hdefect_nonneg]
  -- Proof comment: the finite telescope already identifies every partial sum.
  have hlimit :
      Filter.Tendsto (fun N : ℕ ↦ 1 - resetWalkPrefixProduct p N) Filter.atTop
        (𝓝 (1 - ∏' n : ℕ, p n)) :=
    tendsto_const_nhds.sub (resetWalkPrefixProduct_tendsto_tprod p)
  simpa [resetWalkDefect_sum_eq_one_sub_prefixProduct] using hlimit

/-- Helper for Example 17.52: the infinite product `∏' p_n` is bounded above by every finite
prefix product. -/
lemma resetWalk_tprod_le_prefixProduct
    (p : ResetWalkParameters) (n : ℕ) :
    ∏' k : ℕ, p k ≤ resetWalkPrefixProduct p n := by
  have hdefect_nonneg : ∀ k : ℕ, 0 ≤ (1 - p k) * resetWalkPrefixProduct p k := fun k ↦ by
    exact mul_nonneg (sub_nonneg.mpr (p.property k).2) (resetWalkPrefixProduct_nonneg p k)
  have hpartial :
      Finset.sum (Finset.range n) (fun k ↦ (1 - p k) * resetWalkPrefixProduct p k) ≤
        ∑' k : ℕ, (1 - p k) * resetWalkPrefixProduct p k :=
    Summable.sum_le_tsum (Finset.range n) (fun k _ ↦ hdefect_nonneg k)
      (resetWalkDefectHasSum p).summable
  -- Proof comment: compare the finite and infinite telescope sums and then rearrange.
  rw [(resetWalkDefectHasSum p).tsum_eq, resetWalkDefect_sum_eq_one_sub_prefixProduct] at hpartial
  linarith

/-- Helper for Example 17.52: if the infinite product `∏' p_n` is strictly positive, then the
defect series `∑ (1 - p_n)` is summable. -/
lemma summable_one_sub_of_resetWalk_tprod_pos
    (p : ResetWalkParameters) (hprod : 0 < ∏' n : ℕ, p n) :
    Summable (fun n : ℕ ↦ 1 - p n) := by
  have hscaled :
      Summable (fun n : ℕ ↦ (∏' k : ℕ, p k) * (1 - p n)) := by
    -- Proof comment: compare the scaled defect terms against the summable telescope series.
    refine Summable.of_nonneg_of_le
      (fun n ↦ mul_nonneg hprod.le (sub_nonneg.mpr (p.property n).2)) ?_
      (resetWalkDefectHasSum p).summable
    intro n
    calc
      (∏' k : ℕ, p k) * (1 - p n)
        ≤ resetWalkPrefixProduct p n * (1 - p n) := by
            exact mul_le_mul_of_nonneg_right
              (resetWalk_tprod_le_prefixProduct p n) (sub_nonneg.mpr (p.property n).2)
      _ = (1 - p n) * resetWalkPrefixProduct p n := by ring
  -- Proof comment: divide out the fixed positive factor `∏' p_n`.
  exact (summable_mul_left_iff (ne_of_gt hprod)).1 hscaled

-- Proof sketch: for the weighted counting measure with singleton masses
-- `c ∏_{k < n} p_k`, the singleton balance equation is automatic away from `0`. At `0`, the
-- stationarity equation becomes `c = c * (1 - ∏' n, p n)`, so vanishing of the infinite product
-- is exactly the remaining condition. Finiteness of `c` matters only for later finite-measure
-- statements, not for invariance itself.
/-- If the infinite product `∏' n, p n` vanishes, then the weighted counting measure with
singleton masses `c ∏_{k < n} p_k` is invariant for the reset-walk kernel. -/
theorem resetWalkInvariantMeasure_isInvariant
    (p : ResetWalkParameters) (c : ℝ≥0∞)
    (hprod : ∏' n : ℕ, p n = 0) :
    Kernel.Invariant (resetWalkKernel p) (resetWalkInvariantMeasure p c) := by
  apply (resetWalkKernel_invariant_iff_singletonBalance p _).2
  intro x
  cases x with
  | zero =>
      have hdefect_nonneg : ∀ n : ℕ, 0 ≤ (1 - p n) * resetWalkPrefixProduct p n := fun n ↦ by
        exact mul_nonneg (sub_nonneg.mpr (p.property n).2) (resetWalkPrefixProduct_nonneg p n)
      have hdefect_tsum :
          ∑' n : ℕ, ENNReal.ofReal ((1 - p n) * resetWalkPrefixProduct p n) =
            ENNReal.ofReal (1 - ∏' n : ℕ, p n) := by
        -- Proof comment: convert the real-valued defect `HasSum` into the `ℝ≥0∞` sum used by the
        -- singleton balance at state `0`.
        rw [← ENNReal.ofReal_tsum_of_nonneg hdefect_nonneg (resetWalkDefectHasSum p).summable,
          (resetWalkDefectHasSum p).tsum_eq]
      -- Proof comment: at state `0`, every row contributes its reset mass `(1 - p_y)`.
      calc
        ∑' y : ℕ,
            resetWalkInvariantMeasure p c {y} * resetWalkTransitionMatrix p y 0
          = ∑' y : ℕ, c * ENNReal.ofReal ((1 - p y) * resetWalkPrefixProduct p y) := by
              refine tsum_congr fun y ↦ ?_
              calc
                resetWalkInvariantMeasure p c {y} * resetWalkTransitionMatrix p y 0
                  = (c * resetWalkPrefixProductENNReal p y) * ENNReal.ofReal (1 - p y) := by
                      rw [resetWalkInvariantMeasure_apply_singleton, resetWalkInvariantMass_apply,
                        resetWalkTransitionMatrix_apply_zero]
                _ = c * ENNReal.ofReal (resetWalkPrefixProduct p y * (1 - p y)) := by
                      rw [mul_assoc]
                      congr 1
                      rw [resetWalkPrefixProductENNReal_eq_ofReal]
                      rw [ENNReal.ofReal_mul (resetWalkPrefixProduct_nonneg p y)]
                _ = c * ENNReal.ofReal ((1 - p y) * resetWalkPrefixProduct p y) := by
                      simp [mul_comm]
        _ = c * ∑' y : ℕ, ENNReal.ofReal ((1 - p y) * resetWalkPrefixProduct p y) := by
              rw [ENNReal.tsum_mul_left]
        _ = c * ENNReal.ofReal (1 - ∏' n : ℕ, p n) := by
              rw [hdefect_tsum]
        _ = c * resetWalkPrefixProductENNReal p 0 := by
              rw [resetWalkPrefixProductENNReal_eq_ofReal]
              simp [hprod, resetWalkPrefixProduct_zero]
        _ = resetWalkInvariantMeasure p c ({0} : Set ℕ) := by
              rw [resetWalkInvariantMeasure_apply_singleton, resetWalkInvariantMass_apply]

  | succ n =>
      -- Proof comment: at state `n + 1`, the only incoming edge comes from `n`.
      calc
        ∑' y : ℕ,
            resetWalkInvariantMeasure p c {y} * resetWalkTransitionMatrix p y (n + 1)
          = ∑' y : ℕ,
              resetWalkInvariantMeasure p c {y} *
                (if y = n then ENNReal.ofReal (p n) else 0) := by
                  refine tsum_congr fun y ↦ ?_
                  rw [resetWalkTransitionMatrix_apply_succ]
        _ = resetWalkInvariantMeasure p c {n} * ENNReal.ofReal (p n) := by
              simp [tsum_eq_single n]
        _ = c * resetWalkPrefixProductENNReal p (n + 1) := by
              rw [resetWalkInvariantMeasure_apply_singleton, resetWalkInvariantMass_apply,
                resetWalkPrefixProductENNReal_succ, mul_assoc]
        _ = resetWalkInvariantMeasure p c ({n + 1} : Set ℕ) := by
              rw [resetWalkInvariantMeasure_apply_singleton, resetWalkInvariantMass_apply]

/-- Helper for Example 17.52: the explicit invariant measure has total mass
`c * resetWalkMassSeries p`. -/
lemma resetWalkInvariantMeasure_univ
    (p : ResetWalkParameters) (c : ℝ≥0∞) :
    resetWalkInvariantMeasure p c Set.univ = c * resetWalkMassSeries p := by
  -- Proof comment: evaluate the weighted counting measure on `Set.univ` and rewrite the resulting
  -- counting integral as the `ℝ≥0∞` series of singleton masses.
  calc
    resetWalkInvariantMeasure p c Set.univ
      = ∫⁻ a in Set.univ, resetWalkInvariantMass p c a ∂Measure.count := by
          rw [resetWalkInvariantMeasure, withDensity_apply _ MeasurableSet.univ]
    _ = ∫⁻ a, resetWalkInvariantMass p c a ∂Measure.count := by
          simp
    _ = c * resetWalkMassSeries p := by
          rw [lintegral_count]
          simp [resetWalkInvariantMass, resetWalkMassSeries, ENNReal.tsum_mul_left, mul_comm,
            mul_left_comm, mul_assoc]

/-- Helper for Example 17.52: any invariant measure has total mass `μ {0} * resetWalkMassSeries p`
because its singleton masses are forced by the prefix-product recursion. -/
lemma invariantMeasure_univ_eq_singletonZero_mul_massSeries
    (p : ResetWalkParameters) (μ : Measure ℕ)
    (hμ : Kernel.Invariant (resetWalkKernel p) μ) :
    μ Set.univ = μ {0} * resetWalkMassSeries p := by
  have hEq : μ = resetWalkInvariantMeasure p (μ {0}) := by
    -- Proof comment: on the discrete state space `ℕ`, equality of all singleton masses fixes the
    -- whole measure.
    refine Measure.ext_of_singleton fun n ↦ ?_
    calc
      μ ({n} : Set ℕ) = resetWalkInvariantMass p (μ {0}) n := by
          simpa [resetWalkInvariantMass] using
            invariant_singletonMass_eq_resetWalkInvariantMass p μ hμ n
      _ = resetWalkInvariantMeasure p (μ {0}) ({n} : Set ℕ) := by
          rw [resetWalkInvariantMeasure_apply_singleton]
  have hunivEq :
      μ Set.univ = resetWalkInvariantMeasure p (μ {0}) Set.univ :=
    congrArg (fun ν : Measure ℕ ↦ ν Set.univ) hEq
  calc
    μ Set.univ = resetWalkInvariantMeasure p (μ {0}) Set.univ := hunivEq
    _ = μ {0} * resetWalkMassSeries p := resetWalkInvariantMeasure_univ p (μ {0})

-- Proof sketch: any invariant measure is determined by its singleton mass at `0`, and evaluating
-- the invariant equation at `{0}` shows that a positive finite value of `μ {0}` is possible
-- exactly when `∏' n, p n = 0`. Conversely, if the product vanishes then the weighted counting
-- measure with `c = 1` is invariant.
/-- Helper for Example 17.52: for the chain on `ℕ` with transition probabilities
`p(x,x+1)=p_x` and `p(x,0)=1-p_x`, there exists an invariant measure with positive finite
singleton mass at `0` if and only if the infinite product `∏' n, p n` is `0`. -/
theorem exists_nontrivial_resetWalkInvariantMeasure_iff_tprod_eq_zero
    (p : ResetWalkParameters) :
    (∃ μ : Measure ℕ, 0 < μ {0} ∧ μ {0} < ∞ ∧ Kernel.Invariant (resetWalkKernel p) μ) ↔
      ∏' n : ℕ, p n = 0 := by
  constructor
  · rintro ⟨μ, hμ0_pos, hμ0_lt_top, hμinv⟩
    have hbalance0 := (resetWalkKernel_invariant_iff_singletonBalance p μ).mp hμinv 0
    have hdefect_nonneg : ∀ n : ℕ, 0 ≤ (1 - p n) * resetWalkPrefixProduct p n := fun n ↦ by
      exact mul_nonneg (sub_nonneg.mpr (p.property n).2) (resetWalkPrefixProduct_nonneg p n)
    have hdefect_tsum :
        ∑' n : ℕ, ENNReal.ofReal ((1 - p n) * resetWalkPrefixProduct p n) =
          ENNReal.ofReal (1 - ∏' n : ℕ, p n) := by
      -- Proof comment: this is the `ℝ≥0∞` version of the infinite telescope.
      rw [← ENNReal.ofReal_tsum_of_nonneg hdefect_nonneg (resetWalkDefectHasSum p).summable,
        (resetWalkDefectHasSum p).tsum_eq]
    have hrewrite :
        ∑' y : ℕ, μ {y} * resetWalkTransitionMatrix p y 0 =
          μ {0} * ENNReal.ofReal (1 - ∏' n : ℕ, p n) := by
      -- Proof comment: rewrite each singleton mass through the explicit invariant-mass profile and
      -- then collapse the resulting defect series.
      calc
        ∑' y : ℕ, μ {y} * resetWalkTransitionMatrix p y 0
          = ∑' y : ℕ, μ {0} * ENNReal.ofReal ((1 - p y) * resetWalkPrefixProduct p y) := by
              refine tsum_congr fun y ↦ ?_
              calc
                μ {y} * resetWalkTransitionMatrix p y 0
                  = resetWalkInvariantMass p (μ {0}) y * resetWalkTransitionMatrix p y 0 := by
                      rw [← invariant_singletonMass_eq_resetWalkInvariantMass p μ hμinv y]
                _ = (μ {0} * resetWalkPrefixProductENNReal p y) * ENNReal.ofReal (1 - p y) := by
                      rw [resetWalkInvariantMass_apply, resetWalkTransitionMatrix_apply_zero]
                _ = μ {0} * ENNReal.ofReal (resetWalkPrefixProduct p y * (1 - p y)) := by
                      rw [mul_assoc]
                      congr 1
                      rw [resetWalkPrefixProductENNReal_eq_ofReal]
                      rw [ENNReal.ofReal_mul (resetWalkPrefixProduct_nonneg p y)]
                _ = μ {0} * ENNReal.ofReal ((1 - p y) * resetWalkPrefixProduct p y) := by
                      simp [mul_comm]
        _ = μ {0} * ∑' y : ℕ, ENNReal.ofReal ((1 - p y) * resetWalkPrefixProduct p y) := by
              rw [ENNReal.tsum_mul_left]
        _ = μ {0} * ENNReal.ofReal (1 - ∏' n : ℕ, p n) := by
              rw [hdefect_tsum]
    rw [hrewrite] at hbalance0
    have hfactor :
        μ {0} * ENNReal.ofReal (1 - ∏' n : ℕ, p n) = μ {0} * 1 := by
      simpa using hbalance0
    have hinner :
        ENNReal.ofReal (1 - ∏' n : ℕ, p n) = 1 :=
      (ENNReal.mul_right_inj hμ0_pos.ne' (ne_of_lt hμ0_lt_top)).mp hfactor
    have hone : 1 - ∏' n : ℕ, p n = 1 := by
      simpa using hinner
    linarith
  · intro hprod
    refine ⟨resetWalkInvariantMeasure p 1, ?_, ?_, resetWalkInvariantMeasure_isInvariant p 1 hprod⟩
    · -- Proof comment: choosing base mass `c = 1` gives positive singleton mass at `0`.
      have hmass0 : resetWalkInvariantMeasure p 1 ({0} : Set ℕ) = 1 := by
        rw [resetWalkInvariantMeasure_apply_singleton, resetWalkInvariantMass_apply]
        simp [resetWalkPrefixProduct_zero, resetWalkPrefixProductENNReal]
        rfl
      rw [hmass0]
      exact zero_lt_one
    · -- Proof comment: the same singleton mass is finite because it is exactly `1`.
      rw [resetWalkInvariantMeasure_apply_singleton, resetWalkInvariantMass_apply]
      simp [resetWalkPrefixProduct_zero, resetWalkPrefixProductENNReal]

-- Proof sketch: under `0 < p_n ≤ 1`, the logarithmic criterion for infinite products identifies
-- vanishing of `∏' n, p n` with divergence of the nonnegative defect series `∑ (1 - p_n)`.
/-- Vanishing of the infinite product is equivalent to divergence of the defect series
`∑ (1 - p_n)`. Here divergence is expressed as non-summability. -/
theorem resetWalk_tprod_eq_zero_iff_not_summable_one_sub
    (p : ResetWalkParameters) (hp : ∀ n : ℕ, 0 < p n) :
    (∏' n : ℕ, p n = 0) ↔ ¬ Summable (fun n : ℕ ↦ 1 - p n) := by
  constructor
  · intro hprod hsumm
    have hfactor_ne : ∀ n : ℕ, 1 + -(1 - p n) ≠ 0 := by
      intro n
      rw [show 1 + -(1 - p n) = p n by ring]
      exact ne_of_gt (hp n)
    have hnorm :
        Summable (fun n : ℕ ↦ ‖-(1 - p n)‖) := by
      simpa using hsumm.neg.norm
    have htprod_ne :
        ∏' n : ℕ, (1 + -(1 - p n)) ≠ 0 :=
      tprod_one_add_ne_zero_of_summable hfactor_ne hnorm
    have hprod' : ∏' n : ℕ, (1 + -(1 - p n)) = 0 := by
      simpa using hprod
    exact htprod_ne hprod'
  · intro hsumm
    by_contra hprod
    have hprod_ne : ∏' n : ℕ, p n ≠ 0 := hprod
    have hnonneg : 0 ≤ ∏' n : ℕ, p n :=
      ge_of_tendsto' (resetWalkPrefixProduct_tendsto_tprod p)
        (fun n ↦ resetWalkPrefixProduct_nonneg p n)
    have hpos : 0 < ∏' n : ℕ, p n :=
      lt_of_le_of_ne hnonneg hprod_ne.symm
    exact hsumm (summable_one_sub_of_resetWalk_tprod_pos p hpos)

-- Proof sketch: use the explicit formula `μ {n} = μ {0} * ∏_{k < n} p_k`; once the total mass is
-- finite, the singleton mass `μ {0}` is automatically finite, so finiteness of the whole measure
-- is equivalent to summability of the prefix-product sequence.
/-- A nontrivial invariant measure is finite exactly when the prefix-product series
`∑ ∏_{k < n} p_k` converges. -/
theorem exists_finite_nontrivial_resetWalkInvariantMeasure_iff_summable_prefixProducts
    (p : ResetWalkParameters) :
    (∃ μ : Measure ℕ, 0 < μ {0} ∧ Kernel.Invariant (resetWalkKernel p) μ ∧ μ Set.univ < ∞) ↔
      Summable (resetWalkPrefixProduct p) := by
  constructor
  · rintro ⟨μ, hμ0_pos, hμinv, hμ_univ_lt_top⟩
    have hseries_lt_top : resetWalkMassSeries p < ∞ := by
      have hmass :
          μ {0} * resetWalkMassSeries p < ∞ := by
        simpa [invariantMeasure_univ_eq_singletonZero_mul_massSeries p μ hμinv] using hμ_univ_lt_top
      rcases (ENNReal.mul_lt_top_iff).mp hmass with hfinite | hμ0_zero | hseries_zero
      · exact hfinite.2
      · exact (hμ0_pos.ne' hμ0_zero).elim
      · simpa [hseries_zero]
    have hsummableNN :
        Summable (fun n : ℕ ↦
          (show NNReal from
            ⟨resetWalkPrefixProduct p n, resetWalkPrefixProduct_nonneg p n⟩)) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable]
      simpa [resetWalkMassSeries, resetWalkPrefixProductENNReal] using hseries_lt_top.ne
    -- Proof comment: the `ℝ≥0∞` mass series is exactly the `ℝ` series of the same nonnegative
    -- prefix products.
    simpa using (NNReal.summable_coe.2 hsummableNN)
  · intro hsummable
    have hsummableNN :
        Summable (fun n : ℕ ↦
          (show NNReal from
            ⟨resetWalkPrefixProduct p n, resetWalkPrefixProduct_nonneg p n⟩)) := by
      simpa using (NNReal.summable_mk (resetWalkPrefixProduct_nonneg p)).2 hsummable
    have hzero_tendstoNN :
        Filter.Tendsto
          (fun n : ℕ ↦
            (show NNReal from
              ⟨resetWalkPrefixProduct p n, resetWalkPrefixProduct_nonneg p n⟩))
          Filter.atTop (𝓝 0) :=
      NNReal.tendsto_atTop_zero_of_summable hsummableNN
    have hzero_tendsto :
        Filter.Tendsto (fun n : ℕ ↦ resetWalkPrefixProduct p n) Filter.atTop (𝓝 0) := by
      simpa using (NNReal.tendsto_coe.2 hzero_tendstoNN)
    have hprod : ∏' n : ℕ, p n = 0 :=
      tendsto_nhds_unique (resetWalkPrefixProduct_tendsto_tprod p) hzero_tendsto
    have hmass_lt_top : resetWalkMassSeries p < ∞ := by
      rw [lt_top_iff_ne_top, resetWalkMassSeries_eq_tsum]
      simpa [resetWalkPrefixProductENNReal] using
        (ENNReal.tsum_coe_ne_top_iff_summable.2 hsummableNN)
    refine ⟨resetWalkInvariantMeasure p 1, ?_, resetWalkInvariantMeasure_isInvariant p 1 hprod, ?_⟩
    · -- Proof comment: again choose unit base mass at `0`.
      have hmass0 : resetWalkInvariantMeasure p 1 ({0} : Set ℕ) = 1 := by
        rw [resetWalkInvariantMeasure_apply_singleton, resetWalkInvariantMass_apply]
        simp [resetWalkPrefixProduct_zero, resetWalkPrefixProductENNReal]
        rfl
      rw [hmass0]
      exact zero_lt_one
    · -- Proof comment: finite total mass is exactly the finiteness of the mass series.
      simpa [resetWalkInvariantMeasure_univ] using hmass_lt_top

section ResetWalkRealization

variable {Ω : Type u} [MeasurableSpace Ω]
variable {p : ResetWalkParameters} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ resetWalkKernel p ^ n) P X]

/-- Helper for Example 17.52: starting from `0`, the `n`-step kernel puts exactly the prefix
product mass on the singleton `{n}`. -/
lemma resetWalkKernelPow_apply_zero_singleton
    (p : ResetWalkParameters) (n : ℕ) :
    ((resetWalkKernel p ^ n) 0) ({n} : Set ℕ) = resetWalkPrefixProductENNReal p n := by
  induction n with
  | zero =>
      -- Proof comment: the time-zero kernel is the identity, so `{0}` has mass `1`.
      change (Kernel.id 0) ({0} : Set ℕ) = (1 : ℝ≥0∞)
      simp [Kernel.id_apply, resetWalkPrefixProductENNReal]
  | succ n ih =>
      have hpow :
          resetWalkKernel p ^ (n + 1) = resetWalkKernel p ∘ₖ (resetWalkKernel p ^ n) := by
        simpa [pow_one, Nat.one_add] using (ProbabilityTheory.Kernel.pow_add (resetWalkKernel p) 1 n)
      -- Proof comment: compose one more reset-walk step and keep only the predecessor `n`.
      calc
        ((resetWalkKernel p ^ (n + 1)) 0) ({n + 1} : Set ℕ)
          = (resetWalkKernel p ∘ₘ ((resetWalkKernel p ^ n) 0)) ({n + 1} : Set ℕ) := by
              rw [hpow, Kernel.comp_apply]
        _ = ∑' y : ℕ, ((resetWalkKernel p ^ n) 0) {y} * resetWalkTransitionMatrix p y (n + 1) := by
              simpa [resetWalkKernel, comp_discreteMatrixKernel_apply_singleton_eq_tsum]
      -- Route correction: the singleton computation needs the standard `tsum_eq_single` collapse.
      have hcollapse :
          ∑' y : ℕ, ((resetWalkKernel p ^ n) 0) {y} * resetWalkTransitionMatrix p y (n + 1) =
            ((resetWalkKernel p ^ n) 0) {n} * ENNReal.ofReal (p n) := by
        calc
          ∑' y : ℕ, ((resetWalkKernel p ^ n) 0) {y} * resetWalkTransitionMatrix p y (n + 1)
            = ∑' y : ℕ,
                ((resetWalkKernel p ^ n) 0) {y} *
                  (if y = n then ENNReal.ofReal (p n) else 0) := by
                    refine tsum_congr fun y ↦ ?_
                    rw [resetWalkTransitionMatrix_apply_succ]
          _ = ((resetWalkKernel p ^ n) 0) {n} * ENNReal.ofReal (p n) := by
                simp [tsum_eq_single n]
      exact hcollapse.trans (by rw [ih, resetWalkPrefixProductENNReal_succ])

/-- Helper for Example 17.52: if every `p_n` is positive, then starting from `0` the realized
reset walk hits any target state `x` with positive probability. -/
lemma resetWalk_everHitsProbabilityPosFromZero
    (hp : ∀ n : ℕ, 0 < p n) {x : ℕ} (hx : x ≠ 0) :
    0 < (F[P, X]) 0 x := by
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ resetWalkKernel p ^ n) P X := inferInstance
  let hproc : IsStochasticProcess X := fun n ↦ hReal.measurable_process n
  have hxpos : 0 < x := Nat.pos_iff_ne_zero.mpr hx
  have hstep :
      0 < ((resetWalkKernel p ^ x) 0) ({x} : Set ℕ) := by
    rw [resetWalkKernelPow_apply_zero_singleton]
    rw [resetWalkPrefixProductENNReal_eq_ofReal]
    exact ENNReal.ofReal_pos.mpr (resetWalkPrefixProduct_pos p hp x)
  have hgreen : 0 < (G[P, X; 1]) 0 x :=
    greenFunctionFrom_one_pos_of_posStepMass P X hxpos hstep
  exact (greenFunctionFrom_one_pos_iff_everHitsProbability_pos P X hproc 0 x).1 hgreen

/-- Helper for Example 17.52: if a history event already pins down the state at time `n`,
intersecting it with a deterministic future singleton event factors through the corresponding
transition mass. -/
private lemma resetWalkMeasure_inter_prefix_stepEvent_eq_mulLocal
    {x y z : ℕ} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
      (((resetWalkKernel p ^ m) y) ({z} : Set ℕ)).toReal * (P x : Measure Ω).real A := by
  let μ : Measure Ω := P x
  let hReal : IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X := inferInstance
  let B : Set Ω := X (n + m) ⁻¹' ({z} : Set ℕ)
  have hB_meas : MeasurableSet B := by
    simpa [B] using (hReal.measurable_process (n + m)) (MeasurableSet.singleton z)
  have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    refine iSup₂_le fun k hk ↦ ?_
    exact (hReal.measurable_process k).comap_le
  have hA_measAmbient : MeasurableSet A := by
    -- Proof comment: the generated history filtration is contained in the ambient sigma-algebra.
    exact hFiltration_le (s := A) hA_meas
  have hMarkovGenerated :
      μ⟦B | generatedFiltrationSpace X n⟧ =ᵐ[μ]
        fun ω ↦ (((resetWalkKernel p ^ m) (X n ω)) ({z} : Set ℕ)).toReal := by
    simpa [μ, B, add_comm] using
      hReal.markov_property x (A := ({z} : Set ℕ)) (MeasurableSet.singleton z) n m
  have hIndicatorIntegrable : Integrable (B.indicator (fun _ ↦ (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hB_meas
  -- Proof comment: integrate the Markov-property conditional expectation over the history event
  -- and then freeze the current state to `y` on `A`.
  calc
    μ.real (A ∩ {ω | X (n + m) ω = z}) =
        ∫ ω in A, (μ⟦B | generatedFiltrationSpace X n⟧) ω ∂ μ := by
          rw [setIntegral_condExp hFiltration_le hIndicatorIntegrable hA_meas,
            ← integral_indicator hA_measAmbient]
          symm
          simpa [B, Set.indicator_indicator, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
            smul_eq_mul] using integral_indicator_const (1 : ℝ) (hA_measAmbient.inter hB_meas)
    _ = ∫ ω in A, (((resetWalkKernel p ^ m) (X n ω)) ({z} : Set ℕ)).toReal ∂ μ := by
          exact integral_congr_ae hMarkovGenerated.restrict
    _ = ∫ _ in A, (((resetWalkKernel p ^ m) y) ({z} : Set ℕ)).toReal ∂ μ := by
          refine integral_congr_ae ?_
          filter_upwards [self_mem_ae_restrict (μ := μ) (s := A) hA_measAmbient] with ω hω
          have hω : X n ω = y := hA_sub hω
          rw [hω]
    _ = (((resetWalkKernel p ^ m) y) ({z} : Set ℕ)).toReal * μ.real A := by
          rw [setIntegral_const, smul_eq_mul, mul_comm]

/-- Helper for Example 17.52: the same deterministic-time singleton factorization is cleaner in
raw `Measure` (`ℝ≥0∞`) form. -/
private lemma resetWalkMeasure_inter_prefix_stepEvent_eq_mul_ennrealLocal
    {x y z : ℕ} {A : Set Ω} {n m : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
      ((resetWalkKernel p ^ m) y ({z} : Set ℕ)) * (P x : Measure Ω) A := by
  have hstep :
      (P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z}) =
        (((resetWalkKernel p ^ m) y) ({z} : Set ℕ)).toReal * (P x : Measure Ω).real A :=
    resetWalkMeasure_inter_prefix_stepEvent_eq_mulLocal
      (p := p) (P := P) (X := X) hA_meas hA_sub
  have hleft_ne_top :
      (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) ≠ ⊤ :=
    measure_ne_top _ _
  have hkernel_ne_top : ((resetWalkKernel p ^ m) y) ({z} : Set ℕ) ≠ ⊤ :=
    measure_ne_top _ _
  have hA_ne_top : (P x : Measure Ω) A ≠ ⊤ :=
    measure_ne_top _ _
  -- Proof comment: convert the real-valued equality back into `ENNReal`.
  calc
    (P x : Measure Ω) (A ∩ {ω | X (n + m) ω = z}) =
        ENNReal.ofReal ((P x : Measure Ω).real (A ∩ {ω | X (n + m) ω = z})) := by
          symm
          exact ENNReal.ofReal_toReal hleft_ne_top
    _ =
        ENNReal.ofReal
          ((((resetWalkKernel p ^ m) y) ({z} : Set ℕ)).toReal * (P x : Measure Ω).real A) := by
          rw [hstep]
    _ = ((resetWalkKernel p ^ m) y ({z} : Set ℕ)) * (P x : Measure Ω) A := by
          rw [ENNReal.ofReal_mul]
          · rw [ENNReal.ofReal_toReal hkernel_ne_top]
            change ((resetWalkKernel p ^ m) y ({z} : Set ℕ)) *
                ENNReal.ofReal (((P x : Measure Ω) A).toReal) =
              ((resetWalkKernel p ^ m) y ({z} : Set ℕ)) * (P x : Measure Ω) A
            rw [ENNReal.ofReal_toReal hA_ne_top]
          · positivity

/-- Helper for Example 17.52: the generated history filtration grows with time. -/
private lemma resetWalkGeneratedFiltrationSpace_monoLocal
    (Y : ℕ → Ω → ℕ) {s t : ℕ} (hst : s ≤ t) :
    generatedFiltrationSpace Y s ≤ generatedFiltrationSpace Y t := by
  refine iSup₂_le fun r hr ↦ ?_
  exact le_iSup_of_le r <| le_iSup_of_le (hr.trans hst) le_rfl

/-- Helper for Example 17.52: `resetWalkFuturePrefixEventLocal X n f` fixes a finite future path
after time `n`. -/
private def resetWalkFuturePrefixEventLocal (Y : ℕ → Ω → ℕ) (n : ℕ) {M : ℕ}
    (f : Fin (M + 1) → ℕ) : Set Ω :=
  {ω | ∀ i : Fin (M + 1), Y (n + (i : ℕ)) ω = f i}

/-- Helper for Example 17.52: finite future-prefix events are measurable. -/
private lemma resetWalkMeasurableSet_futurePrefixEventLocal
    {p : ResetWalkParameters} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
    [IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X]
    {M n : ℕ} (f : Fin (M + 1) → ℕ) :
    MeasurableSet (resetWalkFuturePrefixEventLocal X n f) := by
  let hReal : IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X := inferInstance
  have hEq :
      resetWalkFuturePrefixEventLocal X n f =
        ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [resetWalkFuturePrefixEventLocal]
  rw [hEq]
  refine MeasurableSet.iInter fun i ↦ ?_
  simpa [Set.preimage] using
    (hReal.measurable_process (n + (i : ℕ))) (MeasurableSet.singleton (f i))

/-- Helper for Example 17.52: a finite future-prefix event is measurable in the history
filtration at its terminal time. -/
private lemma resetWalkMeasurableSet_futurePrefixEventGeneratedLocal
    {p : ResetWalkParameters} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
    [IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X]
    {M n : ℕ} (f : Fin (M + 1) → ℕ) :
    MeasurableSet[generatedFiltrationSpace X (n + M)] (resetWalkFuturePrefixEventLocal X n f) := by
  have hEq :
      resetWalkFuturePrefixEventLocal X n f =
        ⋂ i : Fin (M + 1), {ω | X (n + (i : ℕ)) ω = f i} := by
    ext ω
    simp [resetWalkFuturePrefixEventLocal]
  rw [hEq]
  refine MeasurableSet.iInter fun i ↦ ?_
  have hXi : Measurable[generatedFiltrationSpace X (n + M)] (X (n + (i : ℕ))) := by
    refine Measurable.of_comap_le ?_
    exact
      le_iSup_of_le (n + (i : ℕ)) <|
        le_iSup_of_le (Nat.add_le_add_left (Nat.le_of_lt_succ i.2) n) le_rfl
  simpa [Set.preimage] using hXi (MeasurableSet.singleton (f i))

/-- Helper for Example 17.52: at horizon `0`, a future-prefix event is just the current state
event. -/
private lemma resetWalkFuturePrefixEvent_zero_eq_stateEventLocal
    (Y : ℕ → Ω → ℕ) (n : ℕ) (f : Fin 1 → ℕ) :
    resetWalkFuturePrefixEventLocal Y n f = {ω | Y n ω = f 0} := by
  ext ω
  simp [resetWalkFuturePrefixEventLocal]

/-- Helper for Example 17.52: a longer future-prefix event splits into its shorter prefix and the
terminal one-step state constraint. -/
private lemma resetWalkFuturePrefixEvent_succ_eqLocal
    (Y : ℕ → Ω → ℕ) {M n : ℕ} (f : Fin (M + 2) → ℕ) :
    resetWalkFuturePrefixEventLocal Y n f =
      resetWalkFuturePrefixEventLocal Y n (fun i : Fin (M + 1) ↦ f i.castSucc) ∩
        {ω | Y (n + (M + 1)) ω = f (Fin.last (M + 1))} := by
  ext ω
  constructor
  · intro hω
    refine ⟨?_, ?_⟩
    · intro i
      simpa [resetWalkFuturePrefixEventLocal] using hω i.castSucc
    · simpa [resetWalkFuturePrefixEventLocal] using hω (Fin.last (M + 1))
  · rintro ⟨hωPrefix, hωLast⟩
    intro i
    by_cases hi : i = Fin.last (M + 1)
    · subst hi
      simpa [resetWalkFuturePrefixEventLocal] using hωLast
    · obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      simpa [resetWalkFuturePrefixEventLocal] using hωPrefix j

/-- Helper for Example 17.52: a future-prefix event determines its terminal state. -/
private lemma resetWalkFuturePrefixEvent_terminal_subsetLocal
    (Y : ℕ → Ω → ℕ) {M n : ℕ} (f : Fin (M + 1) → ℕ) :
    resetWalkFuturePrefixEventLocal Y n f ⊆ {ω | Y (n + M) ω = f (Fin.last M)} := by
  intro ω hω
  simpa [resetWalkFuturePrefixEventLocal] using hω (Fin.last M)

/-- Helper for Example 17.52: once a history event pins down the present state, intersecting it
with a finite future-prefix event factors through the restarted path law from that state. -/
private lemma resetWalkMeasure_inter_prefix_futurePrefixEvent_eq_mulLocal
    {p : ResetWalkParameters} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
    [IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X]
    {x y : ℕ} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y})
    (f : Fin (M + 1) → ℕ) :
    (P x : Measure Ω) (A ∩ resetWalkFuturePrefixEventLocal X n f) =
      (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
  induction M with
  | zero =>
      let hReal : IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X := inferInstance
      have hright_eval :
          (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 f) = if f 0 = y then 1 else 0 := by
        rw [resetWalkFuturePrefixEvent_zero_eq_stateEventLocal (Y := X) (n := 0) f]
        have hpreimage : {ω | X 0 ω = f 0} = X 0 ⁻¹' ({f 0} : Set ℕ) := by
          ext ω
          simp
        rw [hpreimage]
        rw [← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton (f 0))]
        rw [hReal.initial_eq y]
        by_cases hf0 : f 0 = y <;> simp [hf0]
      by_cases hf0 : f 0 = y
      · have hleft_eq : A ∩ resetWalkFuturePrefixEventLocal X n f = A := by
          ext ω
          constructor
          · intro hω
            exact hω.1
          · intro hω
            refine ⟨hω, ?_⟩
            rw [resetWalkFuturePrefixEvent_zero_eq_stateEventLocal (Y := X) (n := n) f]
            simpa [hf0] using hA_sub hω
        calc
          (P x : Measure Ω) (A ∩ resetWalkFuturePrefixEventLocal X n f) = (P x : Measure Ω) A := by
            rw [hleft_eq]
          _ = 1 * (P x : Measure Ω) A := by rw [one_mul]
          _ = (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
            rw [hright_eval, if_pos hf0]
      · have hleft_eq : A ∩ resetWalkFuturePrefixEventLocal X n f = ∅ := by
          ext ω
          constructor
          · rintro ⟨hωA, hωf⟩
            rw [resetWalkFuturePrefixEvent_zero_eq_stateEventLocal (Y := X) (n := n) f] at hωf
            exact hf0 (hωf.symm.trans (hA_sub hωA))
          · intro hω
            exact False.elim (by simpa using hω)
        calc
          (P x : Measure Ω) (A ∩ resetWalkFuturePrefixEventLocal X n f) = 0 := by
            simp [hleft_eq]
          _ = (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
            rw [hright_eval, if_neg hf0]
            simp
  | succ M ih =>
      let g : Fin (M + 1) → ℕ := fun i ↦ f i.castSucc
      let B : Set Ω := A ∩ resetWalkFuturePrefixEventLocal X n g
      have hA_meas_big : MeasurableSet[generatedFiltrationSpace X (n + M)] A := by
        let hmono :
            generatedFiltrationSpace X n ≤ generatedFiltrationSpace X (n + M) :=
          resetWalkGeneratedFiltrationSpace_monoLocal
            (Y := X) (s := n) (t := n + M) (Nat.le_add_right n M)
        exact hmono (s := A) hA_meas
      have hB_meas : MeasurableSet[generatedFiltrationSpace X (n + M)] B := by
        exact hA_meas_big.inter
          (resetWalkMeasurableSet_futurePrefixEventGeneratedLocal
            (p := p) (P := P) (X := X) (n := n) g)
      have hB_sub : B ⊆ {ω | X (n + M) ω = g (Fin.last M)} := by
        intro ω hω
        exact resetWalkFuturePrefixEvent_terminal_subsetLocal (Y := X) (n := n) g hω.2
      have hleft_step :
          (P x : Measure Ω) (A ∩ resetWalkFuturePrefixEventLocal X n f) =
            ((resetWalkKernel p ^ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P x : Measure Ω) B := by
        calc
          (P x : Measure Ω) (A ∩ resetWalkFuturePrefixEventLocal X n f) =
              (P x : Measure Ω)
                (B ∩ {ω | X ((n + M) + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [B, g, resetWalkFuturePrefixEvent_succ_eqLocal, Nat.add_assoc,
                    Set.inter_assoc, Set.inter_left_comm, Set.inter_comm]
          _ =
              ((resetWalkKernel p ^ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set ℕ)) *
                (P x : Measure Ω) B := by
                  simpa [B] using
                    resetWalkMeasure_inter_prefix_stepEvent_eq_mul_ennrealLocal
                      (p := p) (P := P) (X := X)
                      (x := x) (y := g (Fin.last M)) (z := f (Fin.last (M + 1)))
                      (A := B) (n := n + M) (m := 1) hB_meas hB_sub
      have hg_meas :
          MeasurableSet[generatedFiltrationSpace X M] (resetWalkFuturePrefixEventLocal X 0 g) := by
        have htmp :
            MeasurableSet[generatedFiltrationSpace X (0 + M)] (resetWalkFuturePrefixEventLocal X 0 g) :=
          resetWalkMeasurableSet_futurePrefixEventGeneratedLocal
            (p := p) (P := P) (X := X) (n := 0) g
        convert htmp using 1 <;> simp [zero_add]
      have hg_sub : resetWalkFuturePrefixEventLocal X 0 g ⊆ {ω | X M ω = g (Fin.last M)} := by
        have htmp :
            resetWalkFuturePrefixEventLocal X 0 g ⊆ {ω | X (0 + M) ω = g (Fin.last M)} :=
          resetWalkFuturePrefixEvent_terminal_subsetLocal (Y := X) (n := 0) g
        simpa [zero_add] using htmp
      have hright_step :
          (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 f) =
            ((resetWalkKernel p ^ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 g) := by
        calc
          (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 f) =
              (P y : Measure Ω)
                (resetWalkFuturePrefixEventLocal X 0 g ∩
                  {ω | X (M + 1) ω = f (Fin.last (M + 1))}) := by
                  simp [g, resetWalkFuturePrefixEvent_succ_eqLocal, Nat.add_assoc, Set.inter_assoc,
                    Set.inter_left_comm, Set.inter_comm]
          _ =
              ((resetWalkKernel p ^ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set ℕ)) *
                (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 g) := by
                  simpa using
                    resetWalkMeasure_inter_prefix_stepEvent_eq_mul_ennrealLocal
                      (p := p) (P := P) (X := X)
                      (x := y) (y := g (Fin.last M)) (z := f (Fin.last (M + 1)))
                      (A := resetWalkFuturePrefixEventLocal X 0 g) (n := M) (m := 1) hg_meas hg_sub
      -- Proof comment: split off the terminal coordinate of the future path and reuse the
      -- induction hypothesis on the shorter prefix.
      calc
        (P x : Measure Ω) (A ∩ resetWalkFuturePrefixEventLocal X n f) =
            ((resetWalkKernel p ^ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P x : Measure Ω) B := hleft_step
        _ =
            ((resetWalkKernel p ^ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set ℕ)) *
              ((P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 g) * (P x : Measure Ω) A) := by
                rw [ih g]
        _ =
            (((resetWalkKernel p ^ 1) (g (Fin.last M)) ({f (Fin.last (M + 1))} : Set ℕ)) *
              (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 g)) * (P x : Measure Ω) A := by
                rw [mul_assoc]
        _ = (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 f) * (P x : Measure Ω) A := by
              rw [hright_step]

/-- Helper for Example 17.52: finite no-hit horizons are measurable. -/
private lemma resetWalkMeasurableSet_noHitHorizonLocal
    {p : ResetWalkParameters} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
    [IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X]
    (y n M : ℕ) :
    MeasurableSet (noHitHorizonLocal X y n M) := by
  let hReal : IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X := inferInstance
  have hEq :
      noHitHorizonLocal X y n M =
        ⋂ m ∈ Finset.Icc 1 M, {ω | X (n + m) ω ≠ y} := by
    ext ω
    simp [noHitHorizonLocal]
  rw [hEq]
  refine MeasurableSet.iInter fun m ↦ ?_
  refine MeasurableSet.iInter fun _hm ↦ ?_
  exact ((hReal.measurable_process (n + m)) (MeasurableSet.singleton y)).compl

/-- Helper for Example 17.52: once the current state is fixed to `y`, intersecting with a
finite no-hit horizon away from `0` factors through the restarted law from `y`. -/
private lemma resetWalkMeasure_inter_prefix_noHitHorizon_targetZero_eq_mulLocal
    {p : ResetWalkParameters} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
    [IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X]
    {x y : ℕ} {A : Set Ω} {n M : ℕ}
    (hA_meas : MeasurableSet[generatedFiltrationSpace X n] A)
    (hA_sub : A ⊆ {ω | X n ω = y}) :
    (P x : Measure Ω) (A ∩ noHitHorizonLocal X 0 n M) =
      (P y : Measure Ω) (noHitHorizonLocal X 0 0 M) * (P x : Measure Ω) A := by
  classical
  let μx : Measure Ω := P x
  let T := {f : Fin (M + 1) → ℕ // ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0}
  let hReal : IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X := inferInstance
  have hA_ambient : MeasurableSet A := by
    have hFiltration_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
      refine iSup₂_le fun k hk ↦ ?_
      exact (hReal.measurable_process k).comap_le
    exact hFiltration_le (s := A) hA_meas
  have hleft_union :
      A ∩ noHitHorizonLocal X 0 n M = ⋃ f : T, A ∩ resetWalkFuturePrefixEventLocal X n f.1 := by
    ext ω
    constructor
    · rintro ⟨hωA, hωNoHit⟩
      let f : Fin (M + 1) → ℕ := fun i ↦ X (n + (i : ℕ)) ω
      have hf : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0 := by
        intro i hi
        exact hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
      refine Set.mem_iUnion.2 ⟨⟨f, hf⟩, ?_⟩
      refine ⟨hωA, ?_⟩
      intro i
      rfl
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨f, hωf⟩
      refine ⟨hωf.1, ?_⟩
      intro m hm hmM
      let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
      have hpath : X (n + m) ω = f.1 i := by
        simpa [resetWalkFuturePrefixEventLocal, i] using hωf.2 i
      exact hpath.trans_ne (f.2 i hm)
  have hright_union :
      noHitHorizonLocal X 0 0 M = ⋃ f : T, resetWalkFuturePrefixEventLocal X 0 f.1 := by
    ext ω
    constructor
    · intro hωNoHit
      let f : Fin (M + 1) → ℕ := fun i ↦ X (i : ℕ) ω
      have hf : ∀ i : Fin (M + 1), 0 < (i : ℕ) → f i ≠ 0 := by
        intro i hi
        simpa [f, zero_add] using hωNoHit (i : ℕ) hi (Nat.le_of_lt_succ i.2)
      refine Set.mem_iUnion.2 ⟨⟨f, hf⟩, ?_⟩
      intro i
      simp [f, zero_add]
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨f, hωf⟩
      intro m hm hmM
      let i : Fin (M + 1) := ⟨m, Nat.lt_succ_of_le hmM⟩
      have hpath : X (0 + m) ω = f.1 i := by
        simpa [resetWalkFuturePrefixEventLocal, i, zero_add] using hωf i
      exact hpath.trans_ne (f.2 i hm)
  have hpairwise_left :
      Pairwise (fun f g : T ↦ Disjoint (A ∩ resetWalkFuturePrefixEventLocal X n f.1)
        (A ∩ resetWalkFuturePrefixEventLocal X n g.1)) := by
    intro f g hfg
    refine Set.disjoint_left.2 ?_
    intro ω hωf hωg
    have hEq : f.1 = g.1 := by
      funext i
      exact (hωf.2 i).symm.trans (hωg.2 i)
    exact hfg (Subtype.ext hEq)
  have hpairwise_right :
      Pairwise (fun f g : T ↦ Disjoint (resetWalkFuturePrefixEventLocal X 0 f.1)
        (resetWalkFuturePrefixEventLocal X 0 g.1)) := by
    intro f g hfg
    refine Set.disjoint_left.2 ?_
    intro ω hωf hωg
    have hEq : f.1 = g.1 := by
      funext i
      exact (hωf i).symm.trans (hωg i)
    exact hfg (Subtype.ext hEq)
  have hleft_sum :
      μx (A ∩ noHitHorizonLocal X 0 n M) =
        ∑' f : T, μx (A ∩ resetWalkFuturePrefixEventLocal X n f.1) := by
    rw [hleft_union, measure_iUnion hpairwise_left]
    intro f
    exact hA_ambient.inter
      (resetWalkMeasurableSet_futurePrefixEventLocal
        (p := p) (P := P) (X := X) (n := n) f.1)
  have hright_sum :
      (P y : Measure Ω) (noHitHorizonLocal X 0 0 M) =
        ∑' f : T, (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 f.1) := by
    rw [hright_union, measure_iUnion hpairwise_right]
    intro f
    exact resetWalkMeasurableSet_futurePrefixEventLocal
      (p := p) (P := P) (X := X) (n := 0) f.1
  -- Proof comment: partition the finite no-hit event by the exact future path and factor each
  -- cylinder set through the restarted law from the pinned current state `y`.
  calc
    μx (A ∩ noHitHorizonLocal X 0 n M) =
        ∑' f : T, μx (A ∩ resetWalkFuturePrefixEventLocal X n f.1) := hleft_sum
    _ = ∑' f : T, (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 f.1) * μx A := by
          refine tsum_congr fun f ↦ ?_
          exact resetWalkMeasure_inter_prefix_futurePrefixEvent_eq_mulLocal
            (p := p) (P := P) (X := X) hA_meas hA_sub f.1
    _ = (∑' f : T, (P y : Measure Ω) (resetWalkFuturePrefixEventLocal X 0 f.1)) * μx A := by
          rw [ENNReal.tsum_mul_right]
    _ = (P y : Measure Ω) (noHitHorizonLocal X 0 0 M) * μx A := by
          rw [← hright_sum]

/-- Helper for Example 17.52: the one-step state slice has exactly the mass prescribed by the
reset-walk transition matrix. -/
lemma resetWalkTimeOne_stateEvent
    (x y : ℕ) :
    (P x : Measure Ω) {ω | X 1 ω = y} = resetWalkTransitionMatrix p x y := by
  let hReal : IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X := inferInstance
  have hTransition :
      ((P x : Measure Ω).map (X 1)) ({y} : Set ℕ) =
        ((resetWalkKernel p ^ 1) x) ({y} : Set ℕ) :=
    congrArg (fun μ : Measure ℕ ↦ μ ({y} : Set ℕ)) (hReal.transition_eq x 1)
  have hKernel :
      resetWalkKernel p x ({y} : Set ℕ) = resetWalkTransitionMatrix p x y := by
    rw [resetWalkKernel, discreteMatrixKernel_apply, Measure.sum_apply _ (measurableSet_singleton y)]
    simpa using
      (Measure.sum_smul_dirac_singleton
        (f := fun z : ℕ ↦ resetWalkTransitionMatrix p x z) (a := y))
  rw [pow_one, hKernel] at hTransition
  -- Proof comment: the time-one marginal is exactly the one-step kernel row.
  simpa [Measure.map_apply, hReal.measurable_process 1] using hTransition

/-- Helper for Example 17.52: a zero-based no-hit horizon is exactly the tail event of the first
positive return time to `0`. -/
lemma resetWalkNoHitHorizon_zero_eq_firstReturnTail
    (n : ℕ) :
    noHitHorizonLocal X 0 0 n = {ω | (n : ℕ∞) < (τ_[X, 0]^1) ω} := by
  -- Proof comment: avoiding `0` at times `1, …, n` is exactly the statement that the first
  -- positive return time to `0` is strictly larger than `n`.
  ext ω
  constructor
  · intro hω
    change (n : ℕ∞) < (τ_[X, 0]^1) ω
    by_contra hle
    have hle' : (τ_[X, 0]^1) ω ≤ n := le_of_not_gt hle
    rcases (firstReturnTime_le_iffLocal (X := X) 0 n ω).1 hle' with ⟨j, hj, hjEq⟩
    exact hω j hj.1 hj.2 (by simpa [zero_add] using hjEq)
  · intro hω
    intro m hm hmN hmEq
    have hle : (τ_[X, 0]^1) ω ≤ n :=
      (firstReturnTime_le_iffLocal (X := X) 0 n ω).2
        ⟨m, ⟨hm, hmN⟩, by simpa [zero_add] using hmEq⟩
    exact not_lt_of_ge hle hω

/-- Helper for Example 17.52: after one successful jump to `s + 1`, the remaining no-hit horizon
factors through the restarted law from `s + 1`. -/
lemma resetWalkNoHitAfterSuccessor_eq_mul
    {p : ResetWalkParameters} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
    [IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X]
    (s M : ℕ) :
    (P s : Measure Ω) ({ω | X 1 ω = s + 1} ∩ noHitHorizonLocal X 0 1 M) =
      (P (s + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
        (P s : Measure Ω) {ω | X 1 ω = s + 1} := by
  have hA_meas : MeasurableSet[generatedFiltrationSpace X 1] {ω | X 1 ω = s + 1} := by
    have hX1 : Measurable[generatedFiltrationSpace X 1] (X 1) := by
      refine Measurable.of_comap_le ?_
      exact le_iSup_of_le 1 <| le_iSup_of_le le_rfl le_rfl
    simpa [Set.preimage] using hX1 (MeasurableSet.singleton (s + 1))
  have hA_sub : {ω | X 1 ω = s + 1} ⊆ {ω | X 1 ω = s + 1} := by
    intro ω hω
    exact hω
  -- Proof comment: this is the target-zero specialization of the finite no-hit factorization.
  exact resetWalkMeasure_inter_prefix_noHitHorizon_targetZero_eq_mulLocal
    (p := p) (P := P) (X := X)
    (x := s) (y := s + 1) (A := {ω | X 1 ω = s + 1})
    (n := 1) (M := M) hA_meas hA_sub

/-- Helper for Example 17.52: finite no-hit horizons split according to the state visited at
time `1`. -/
private theorem resetWalkNoHitHorizon_stepDecomposition
    {p : ResetWalkParameters} {P : ℕ → ProbabilityMeasure Ω} {X : ℕ → Ω → ℕ}
    [IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X]
    (start M : ℕ) :
    (P start : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
      ∑' z : ℕ,
        (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
          (P start : Measure Ω) {ω | X 1 ω = z + 1} := by
  let A : ℕ → Set Ω := fun z ↦ {ω | X 1 ω = z + 1}
  have hsplit :
      noHitHorizonLocal X 0 0 (M + 1) =
        ⋃ z : ℕ, A z ∩ noHitHorizonLocal X 0 1 M := by
    ext ω
    constructor
    · intro hω
      have hstep_ne_zero : X 1 ω ≠ 0 := by
        exact hω 1 (by simp) (by omega)
      rcases Nat.exists_eq_succ_of_ne_zero hstep_ne_zero with ⟨z, hz⟩
      refine Set.mem_iUnion.2 ⟨z, ?_⟩
      refine ⟨by simpa [A, hz], ?_⟩
      intro m hm hmM
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hω (m + 1) (by omega) (by omega)
    · intro hω
      rcases Set.mem_iUnion.1 hω with ⟨z, hωz⟩
      rcases hωz with ⟨hz, htail⟩
      intro m hm hmM
      cases m with
      | zero =>
          omega
      | succ m =>
          cases m with
          | zero =>
              have hstep_ne_zero : X 1 ω ≠ 0 := by
                rw [hz]
                omega
              simpa using hstep_ne_zero
          | succ k =>
              have htail' : X (1 + (k + 1)) ω ≠ 0 := htail (k + 1) (by simp) (by omega)
              simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.succ_eq_add_one] using
                htail'
  have hpairwise :
      Pairwise (fun z w : ℕ ↦ Disjoint (A z ∩ noHitHorizonLocal X 0 1 M)
        (A w ∩ noHitHorizonLocal X 0 1 M)) := by
    intro z w hzw
    refine Set.disjoint_left.2 ?_
    intro ω hωz hωw
    have : z + 1 = w + 1 := hωz.1.symm.trans hωw.1
    exact hzw (Nat.succ.inj this)
  have hmeas :
      ∀ z : ℕ, MeasurableSet (A z ∩ noHitHorizonLocal X 0 1 M) := by
    intro z
    let hReal : IsMarkovProcessRealization (fun k : ℕ ↦ resetWalkKernel p ^ k) P X := inferInstance
    exact
      (hReal.measurable_process 1 (measurableSet_singleton (z + 1))).inter
        (resetWalkMeasurableSet_noHitHorizonLocal
          (p := p) (P := P) (X := X) 0 1 M)
  have hslices :
      ∀ z : ℕ,
        (P start : Measure Ω) (A z ∩ noHitHorizonLocal X 0 1 M) =
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            (P start : Measure Ω) (A z) := by
    intro z
    have hA_meas : MeasurableSet[generatedFiltrationSpace X 1] (A z) := by
      have hX1 : Measurable[generatedFiltrationSpace X 1] (X 1) := by
        refine Measurable.of_comap_le ?_
        exact le_iSup_of_le 1 <| le_iSup_of_le le_rfl le_rfl
      simpa [A, Set.preimage] using hX1 (MeasurableSet.singleton (z + 1))
    have hA_sub : A z ⊆ {ω | X 1 ω = z + 1} := by
      intro ω hω
      exact hω
    exact resetWalkMeasure_inter_prefix_noHitHorizon_targetZero_eq_mulLocal
      (p := p) (P := P) (X := X)
      (x := start) (y := z + 1) (A := A z)
      (n := 1) (M := M) hA_meas hA_sub
  calc
    (P start : Measure Ω) (noHitHorizonLocal X 0 0 (M + 1)) =
        (P start : Measure Ω) (⋃ z : ℕ, A z ∩ noHitHorizonLocal X 0 1 M) := by
          rw [hsplit]
    _ = ∑' z : ℕ, (P start : Measure Ω) (A z ∩ noHitHorizonLocal X 0 1 M) := by
          rw [measure_iUnion hpairwise]
          exact hmeas
    _ = ∑' z : ℕ,
          (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 M) *
            (P start : Measure Ω) (A z) := by
              refine tsum_congr fun z ↦ hslices z

/-- Helper for Example 17.52: the finite no-hit horizon started from `s` is exactly the shifted
prefix product `∏_{k < n} p (s + k)`. -/
lemma resetWalkNoHitHorizon_eq_shiftedPrefixProduct
    (s n : ℕ) :
    (P s : Measure Ω) (noHitHorizonLocal X 0 0 n) =
      ENNReal.ofReal (Finset.prod (Finset.range n) fun k ↦ p (s + k)) := by
  induction n generalizing s with
  | zero =>
      have hset : noHitHorizonLocal X 0 0 0 = Set.univ := by
        ext ω
        constructor
        · intro _
          simp
        · intro _
          intro m hm1 hm0 hmEq
          omega
      -- Proof comment: a horizon of length `0` imposes no constraint, so the probability is `1`.
      simp [hset]
  | succ n ih =>
      have hdecomp :
          (P s : Measure Ω) (noHitHorizonLocal X 0 0 (n + 1)) =
            ∑' z : ℕ,
              (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 n) *
                (P s : Measure Ω) {ω | X 1 ω = z + 1} := by
        exact resetWalkNoHitHorizon_stepDecomposition (p := p) (P := P) (X := X) s n
      calc
        (P s : Measure Ω) (noHitHorizonLocal X 0 0 (n + 1)) =
            ∑' z : ℕ,
              (P (z + 1) : Measure Ω) (noHitHorizonLocal X 0 0 n) *
                (P s : Measure Ω) {ω | X 1 ω = z + 1} := hdecomp
        _ = ∑' z : ℕ,
              ENNReal.ofReal (Finset.prod (Finset.range n) fun k ↦ p (z + 1 + k)) *
                (P s : Measure Ω) {ω | X 1 ω = z + 1} := by
                refine tsum_congr fun z ↦ ?_
                rw [ih (z + 1)]
        _ = ENNReal.ofReal (Finset.prod (Finset.range n) fun k ↦ p (s + 1 + k)) *
              (P s : Measure Ω) {ω | X 1 ω = s + 1} := by
                refine tsum_eq_single s ?_
                intro z hz
                have hz_zero : (P s : Measure Ω) {ω | X 1 ω = z + 1} = 0 := by
                  have hsz : s ≠ z := by simpa [eq_comm] using hz
                  rw [resetWalkTimeOne_stateEvent (p := p) (P := P) (X := X) (x := s) (y := z + 1)]
                  rw [resetWalkTransitionMatrix_apply_succ (p := p) (n := z) (y := s)]
                  simp [hsz]
                simp [hz_zero]
        _ =
            ENNReal.ofReal (Finset.prod (Finset.range n) fun k ↦ p (s + 1 + k)) *
              ENNReal.ofReal (p s) := by
                rw [resetWalkTimeOne_stateEvent (p := p) (P := P) (X := X) (x := s) (y := s + 1)]
                rw [resetWalkTransitionMatrix_apply_succ (p := p) (n := s) (y := s)]
                simp
        _ =
            ENNReal.ofReal
              ((Finset.prod (Finset.range n) fun k ↦ p (s + 1 + k)) * p s) := by
              rw [ENNReal.ofReal_mul]
              exact Finset.prod_nonneg fun k hk ↦ (p.property (s + 1 + k)).1
        _ = ENNReal.ofReal (Finset.prod (Finset.range (n + 1)) fun k ↦ p (s + k)) := by
              congr 1
              rw [Finset.prod_range_succ' (f := fun k ↦ p (s + k))]
              simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Helper for Example 17.52: the first-return tail probabilities at state `0` are exactly the
explicit prefix products of the reset-walk parameters. -/
lemma resetWalkFirstReturnTail_zero_eq_prefixProduct
    (n : ℕ) :
    (P 0 : Measure Ω) {ω | (n : ℕ∞) < (τ_[X, 0]^1) ω} =
      resetWalkPrefixProductENNReal p n := by
      -- Proof comment: rewrite the tail event as the corresponding zero-based no-hit horizon and
      -- then specialize the shifted-product formula at `s = 0`.
  rw [← resetWalkNoHitHorizon_zero_eq_firstReturnTail (X := X) (n := n)]
  rw [resetWalkNoHitHorizon_eq_shiftedPrefixProduct (p := p) (P := P) (X := X) (s := 0) (n := n)]
  rw [resetWalkPrefixProductENNReal_eq_ofReal, resetWalkPrefixProduct]
  congr 1
  refine Finset.prod_congr rfl ?_
  intro k hk
  simp

-- Proof sketch: for the reset walk, Example 17.52 identifies recurrence with the vanishing of the
-- infinite product `∏' n, p n`; combine that with
-- `resetWalk_tprod_eq_zero_iff_not_summable_one_sub`. The positivity hypothesis makes the
-- realization irreducible in the source sense, so the chain-level criterion is faithful to the
-- textbook statement.
/-- Example 17.52: under the natural realization of the reset walk with
`0 < p_n`, the chain is recurrent exactly when the defect series
`∑ (1 - p_n)` diverges, written here as non-summability. -/
theorem resetWalk_isRecurrentMarkovChain_iff_not_summable_one_sub
    (hp : ∀ n : ℕ, 0 < p n) :
    IsRecurrentMarkovChain P X ↔ ¬ Summable (fun n : ℕ ↦ 1 - p n) := by
  let hReal : IsMarkovProcessRealization (fun n : ℕ ↦ resetWalkKernel p ^ n) P X := inferInstance
  constructor
  · intro hrec
    classical
    have hrec0 : IsRecurrentState P X 0 := hrec 0
    have hμinv :
        Kernel.Invariant ((fun n : ℕ ↦ resetWalkKernel p ^ n) 1) ((μ[P, X] 0) : Measure ℕ) := by
      simpa using
        recurrentState_returnCycleOccupationMeasure_comp_eq
          (κ := fun n : ℕ ↦ resetWalkKernel p ^ n) (P := P) (X := X) hrec0
    have hμ0_eq :
        ((μ[P, X] 0 : Measure ℕ) ({0} : Set ℕ)) = 1 := by
      -- Proof comment: time `0` contributes mass `1`, and later diagonal slices vanish because
      -- they would contradict the defining inequality `m < τ_[X,0]^1`.
      rw [returnCycleOccupationMeasure_apply_singleton, returnCycleOccupationMass,
        ENNReal.tsum_eq_add_tsum_ite 0]
      have hterm0 :
          (P 0 : Measure Ω) {ω | X 0 ω = 0 ∧ ((0 : ℕ) : ℕ∞) < (τ_[X, 0]^1) ω} = 1 := by
        have hinit :
            (P 0 : Measure Ω) {ω | X 0 ω = 0} = 1 := by
          have hpreimage : {ω | X 0 ω = 0} = X 0 ⁻¹' ({0} : Set ℕ) := by
            ext ω
            simp
          rw [
            hpreimage,
            ← Measure.map_apply (hReal.measurable_process 0) (MeasurableSet.singleton 0)
          ]
          rw [hReal.initial_eq 0]
          simp
        have hτpos : ∀ ω : Ω, (0 : ℕ∞) < (τ_[X, 0]^1) ω := by
          intro ω
          have hτge1 : (1 : ℕ∞) ≤ (τ_[X, 0]^1) ω := by
            simpa [iteratedEntranceTime_one] using
              (show (1 : ℕ) ≤ MeasureTheory.hittingAfter X ({0} : Set ℕ) 1 ω from
                le_hittingAfter ω)
          exact lt_of_lt_of_le (by simp) hτge1
        have hEq :
            {ω | X 0 ω = 0 ∧ ((0 : ℕ) : ℕ∞) < (τ_[X, 0]^1) ω} = {ω | X 0 ω = 0} := by
          ext ω
          simp [hτpos ω]
        rw [hEq]
        exact hinit
      have htailZero :
          ∀ i : ℕ,
            (if i = 0 then 0
            else (P 0 : Measure Ω) {ω | X i ω = 0 ∧ (i : ℕ∞) < (τ_[X, 0]^1) ω}) = 0 := by
        intro i
        by_cases hi : i = 0
        · simp [hi]
        · rcases Nat.exists_eq_succ_of_ne_zero hi with ⟨n, rfl⟩
          have hempty :
              {ω | X (n + 1) ω = 0 ∧ (((n + 1 : ℕ) : ℕ∞) < (τ_[X, 0]^1) ω)} = ∅ := by
            ext ω
            constructor
            · intro hω
              have hle :
                  (τ_[X, 0]^1) ω ≤ n + 1 := by
                simpa [iteratedEntranceTime_one] using
                  (MeasureTheory.hittingAfter_le_of_mem (by simp)
                    (by simpa [Set.mem_singleton_iff] using hω.1))
              exact False.elim ((not_lt_of_ge hle) hω.2)
            · simp
          rw [hempty]
          simp
      have htailEq :
          (∑' i : ℕ,
            if i = 0 then 0
            else (P 0 : Measure Ω) {ω | X i ω = 0 ∧ (i : ℕ∞) < (τ_[X, 0]^1) ω}) = 0 :=
        ENNReal.tsum_eq_zero.2 htailZero
      rw [hterm0]
      have hsum :
          (1 : ℝ≥0∞) +
            (∑' i : ℕ,
              if i = 0 then 0
              else (P 0 : Measure Ω) {ω | X i ω = 0 ∧ (i : ℕ∞) < (τ_[X, 0]^1) ω}) =
            ((1 : ℝ≥0∞) + 0) := by
        rw [htailEq]
      simpa using hsum
    have hμ0_pos : 0 < ((μ[P, X] 0 : Measure ℕ) ({0} : Set ℕ)) := by
      rw [hμ0_eq]
      exact zero_lt_one
    have hμ0_lt_top : ((μ[P, X] 0 : Measure ℕ) ({0} : Set ℕ)) < ∞ := by
      rw [hμ0_eq]
      simp
    have hprod :
        ∏' n : ℕ, p n = 0 :=
      (exists_nontrivial_resetWalkInvariantMeasure_iff_tprod_eq_zero p).1
        ⟨(μ[P, X] 0 : Measure ℕ), hμ0_pos, hμ0_lt_top, by simpa [pow_one] using hμinv⟩
    exact (resetWalk_tprod_eq_zero_iff_not_summable_one_sub p hp).1 hprod
  · intro hnotSummable
    have hprod : ∏' n : ℕ, p n = 0 :=
      (resetWalk_tprod_eq_zero_iff_not_summable_one_sub p hp).2 hnotSummable
    have hrec0 : IsRecurrentState P X 0 := by
      let tailEvent : ℕ → Set Ω := fun n ↦ {ω | (n : ℕ∞) < (τ_[X, 0]^1) ω}
      have htail_antitone : Antitone tailEvent := by
        intro m n hmn ω hω
        have hω' : (n : ℕ∞) < (τ_[X, 0]^1) ω := by
          simpa [tailEvent] using hω
        simpa [tailEvent] using lt_of_le_of_lt (by exact_mod_cast hmn) hω'
      have htail_tendsto :
          Filter.Tendsto (fun n ↦ (P 0 : Measure Ω) (tailEvent n)) Filter.atTop
            (nhds ((P 0 : Measure Ω) (⋂ n : ℕ, tailEvent n))) := by
        simpa [tailEvent] using
          tendsto_measure_iInter_atTop (μ := (P 0 : Measure Ω))
            (fun n ↦
              (measurableSet_firstReturnTimeTailLocal
                (κ := fun k : ℕ ↦ resetWalkKernel p ^ k) (P := P) (X := X) 0 n).nullMeasurableSet)
            htail_antitone
            ⟨0, measure_ne_top _ _⟩
      have hprefix_tendsto :
          Filter.Tendsto (fun n : ℕ ↦ (P 0 : Measure Ω) (tailEvent n)) Filter.atTop
            (𝓝 (ENNReal.ofReal (∏' n : ℕ, p n))) := by
        have hreal_tendsto :
            Filter.Tendsto (fun n : ℕ ↦ ENNReal.ofReal (resetWalkPrefixProduct p n)) Filter.atTop
              (𝓝 (ENNReal.ofReal (∏' n : ℕ, p n))) :=
          ENNReal.continuous_ofReal.continuousAt.tendsto.comp
            (resetWalkPrefixProduct_tendsto_tprod p)
        have htailEq :
            (fun n : ℕ ↦ (P 0 : Measure Ω) (tailEvent n)) =
              fun n : ℕ ↦ ENNReal.ofReal (resetWalkPrefixProduct p n) := by
          funext n
          simpa [tailEvent, resetWalkPrefixProductENNReal_eq_ofReal] using
            resetWalkFirstReturnTail_zero_eq_prefixProduct (p := p) (P := P) (X := X) n
        simpa [htailEq] using hreal_tendsto
      have hescape_meas :
          (P 0 : Measure Ω) (⋂ n : ℕ, tailEvent n) = 0 := by
        rw [tendsto_nhds_unique htail_tendsto hprefix_tendsto, hprod]
        simp
      have hescape_eq :
          (⋂ n : ℕ, tailEvent n) = {ω | (τ_[X, 0]^1) ω = ⊤} := by
        ext ω
        constructor
        · intro hω
          by_contra htop
          have hfinite : (((τ_[X, 0]^1) ω).toNat : ℕ∞) = (τ_[X, 0]^1) ω :=
            (ENat.coe_toNat_eq_self).2 htop
          have hlt : (((τ_[X, 0]^1) ω).toNat : ℕ∞) < (τ_[X, 0]^1) ω := by
            simpa [tailEvent] using Set.mem_iInter.1 hω ((τ_[X, 0]^1) ω).toNat
          rw [← hfinite] at hlt
          exact lt_irrefl _ hlt
        · intro hω
          refine Set.mem_iInter.2 ?_
          intro n
          have hω_top : (τ_[X, 0]^1) ω = ⊤ := by simpa using hω
          simpa [tailEvent, hω_top]
      have hfinite_meas :
          MeasurableSet {ω | (τ_[X, 0]^1) ω < ⊤} :=
        measurableSet_firstReturnTimeFinite
          (κ := fun k : ℕ ↦ resetWalkKernel p ^ k) (P := P) (X := X) 0
      have hfinite_prob :
          (P 0 : Measure Ω) {ω | (τ_[X, 0]^1) ω < ⊤} = 1 := by
        have hcompl :
            {ω | (τ_[X, 0]^1) ω < ⊤}ᶜ = {ω | (τ_[X, 0]^1) ω = ⊤} := by
          ext ω
          simp [lt_top_iff_ne_top]
        have hadd := prob_add_prob_compl (μ := (P 0 : Measure Ω)) hfinite_meas
        rw [hcompl, ← hescape_eq, hescape_meas, add_zero] at hadd
        simpa using hadd
      have hhit :
          (P 0 : Measure Ω) {ω | ∃ n : ℕ, 0 < n ∧ X n ω = 0} = 1 := by
        have hEq : {ω | ∃ n : ℕ, 0 < n ∧ X n ω = 0} = {ω | (τ_[X, 0]^1) ω < ⊤} := by
          ext ω
          simpa [iteratedEntranceTime_one] using (hittingAfter_singleton_lt_top_iff X 0 ω).symm
        rw [hEq]
        exact hfinite_prob
      -- Proof comment: the escape event has measure zero, so the positive-time return event has
      -- probability one and hence `0` is recurrent.
      rw [IsRecurrentState, everHitsProbability_def]
      exact (ENNReal.toReal_eq_one_iff _).2 hhit
    intro x
    by_cases hx : x = 0
    · simpa [hx] using hrec0
    · exact
        isRecurrentState_of_isRecurrentState_of_everHitsProbability_pos
          (κ := fun n : ℕ ↦ resetWalkKernel p ^ n) (P := P) (X := X)
          hrec0 (resetWalk_everHitsProbabilityPosFromZero (p := p) (P := P) (X := X) hp hx)

-- Proof sketch: under `0 < p_n`, the reset walk is irreducible, so positive recurrence is
-- equivalent to existence of a finite invariant measure. The explicit invariant-measure formula
-- above shows that this happens exactly when the prefix-product mass series is finite.
/-- Helper for Example 17.52: under the natural realization of the reset walk with
`0 < p_n`, the chain is positive recurrent exactly when the mass series
`M = ∑_{n=0}^\infty ∏_{k=0}^{n-1} p_k` is finite. -/
theorem resetWalk_isPositiveRecurrentMarkovChain_iff_massSeries_lt_top
    (hp : ∀ n : ℕ, 0 < p n) :
    IsPositiveRecurrentMarkovChain P X ↔ resetWalkMassSeries p < ∞ := by
  constructor
  · intro hX
    obtain ⟨π, hπinv, hπ0_pos⟩ :=
      existsInvariantDistributionAtPositiveRecurrentState
        (κ := fun n : ℕ ↦ resetWalkKernel p ^ n) (P := P) (X := X) 0 (hX 0)
    have hπinv_one : Kernel.Invariant (resetWalkKernel p) (π : Measure ℕ) := by
      simpa [pow_one] using hπinv
    have hmass :
        (π : Measure ℕ) {0} * resetWalkMassSeries p < ∞ := by
      have hEq :
          (π : Measure ℕ) {0} * resetWalkMassSeries p = 1 := by
        calc
          (π : Measure ℕ) {0} * resetWalkMassSeries p
            = (π : Measure ℕ) Set.univ := by
                symm
                exact
                  invariantMeasure_univ_eq_singletonZero_mul_massSeries
                    p (π : Measure ℕ) hπinv_one
          _ = 1 := by simp
      simp [hEq]
    rcases (ENNReal.mul_lt_top_iff).mp hmass with hfinite | hzero | hseries_zero
    · exact hfinite.2
    · exact (hπ0_pos.ne' hzero).elim
    · simp [hseries_zero]
  · intro hmass_lt_top
    have hsummableNN :
        Summable (fun n : ℕ ↦
          (show NNReal from
            ⟨resetWalkPrefixProduct p n, resetWalkPrefixProduct_nonneg p n⟩)) := by
      rw [← ENNReal.tsum_coe_ne_top_iff_summable]
      simpa [resetWalkMassSeries, resetWalkPrefixProductENNReal] using hmass_lt_top.ne
    have hsummable : Summable (resetWalkPrefixProduct p) :=
      NNReal.summable_coe.2 hsummableNN
    obtain ⟨μ, hμ0_pos, hμinv, hμ_univ_lt_top⟩ :=
      (exists_finite_nontrivial_resetWalkInvariantMeasure_iff_summable_prefixProducts p).2 hsummable
    have hμ_univ_pos : 0 < μ Set.univ := by
      exact lt_of_lt_of_le hμ0_pos (MeasureTheory.measure_mono (by simp))
    let π : ProbabilityMeasure ℕ :=
      ⟨(μ Set.univ)⁻¹ • μ, by
        refine isProbabilityMeasure_iff.2 ?_
        rw [Measure.smul_apply]
        exact ENNReal.inv_mul_cancel hμ_univ_pos.ne' (ne_of_lt hμ_univ_lt_top)⟩
    have hπinv :
        Kernel.Invariant ((fun n : ℕ ↦ resetWalkKernel p ^ n) 1) (π : Measure ℕ) := by
      simpa [π, pow_one] using
        (kernelInvariant_smul
          (κ := fun n : ℕ ↦ resetWalkKernel p ^ n)
          (μ := μ) (a := (μ Set.univ)⁻¹) (by simpa [pow_one] using hμinv))
    have hπ0_pos : 0 < (π : Measure ℕ) ({0} : Set ℕ) := by
      change 0 < (((μ Set.univ)⁻¹ : ℝ≥0∞) • μ) ({0} : Set ℕ)
      rw [Measure.smul_apply]
      exact ENNReal.mul_pos
        (by simp [hμ_univ_pos.ne', hμ_univ_lt_top.ne])
        hμ0_pos.ne'
    have hpos0 : IsPositiveRecurrentState P X 0 :=
      isPositiveRecurrentState_of_invariantDistribution_singleton_pos
        (κ := fun n : ℕ ↦ resetWalkKernel p ^ n) (P := P) (X := X) hπinv hπ0_pos
    intro x
    by_cases hx : x = 0
    · simpa [hx] using hpos0
    · exact
        isPositiveRecurrentState_of_isPositiveRecurrentState_of_everHitsProbability_pos
          (κ := fun n : ℕ ↦ resetWalkKernel p ^ n) (P := P) (X := X)
          hpos0 (resetWalk_everHitsProbabilityPosFromZero (p := p) (P := P) (X := X) hp hx)

end ResetWalkRealization

/-- Helper for Example 17.52: each prefix product is bounded by the exponential majorant from the
textbook criterion `(⋄)`. -/
lemma resetWalkPrefixProduct_le_exp_neg_sum_one_sub
    (p : ResetWalkParameters) (n : ℕ) :
    resetWalkPrefixProduct p n ≤
      Real.exp (-Finset.sum (Finset.range n) (fun k ↦ 1 - p k)) := by
  induction n with
  | zero =>
      -- Proof comment: both sides are `1` at the empty product / empty sum stage.
      simp [resetWalkPrefixProduct_zero]
  | succ n ih =>
      -- Route correction: instead of expanding the whole series comparison directly, first prove a
      -- pointwise multiplicative estimate and then feed it into `Summable.of_nonneg_of_le`.
      have hstep : p n ≤ Real.exp (-(1 - p n)) := by
        simpa using Real.one_sub_le_exp_neg (1 - p n)
      calc
        resetWalkPrefixProduct p (n + 1)
          = resetWalkPrefixProduct p n * p n := by
              rw [resetWalkPrefixProduct_succ]
        _ ≤ resetWalkPrefixProduct p n * Real.exp (-(1 - p n)) := by
              exact mul_le_mul_of_nonneg_left hstep (resetWalkPrefixProduct_nonneg p n)
        _ ≤ Real.exp (-Finset.sum (Finset.range n) (fun k ↦ 1 - p k)) *
              Real.exp (-(1 - p n)) := by
                exact mul_le_mul_of_nonneg_right ih (Real.exp_pos _).le
        _ = Real.exp (-(Finset.sum (Finset.range n) (fun k ↦ 1 - p k) + (1 - p n))) := by
              rw [← Real.exp_add]
              congr 1
              ring
        _ = Real.exp (-Finset.sum (Finset.range (n + 1)) (fun k ↦ 1 - p k)) := by
              rw [Finset.sum_range_succ]

-- Proof sketch: compare `∏_{k < n} p_k` with the exponential bound
-- `exp (- ∑_{k < n} (1 - p_k))`; summability of the latter implies summability of the former.
/-- The exponential summability condition from the example is sufficient for convergence of the
prefix-product series. -/
theorem summable_resetWalkPrefixProduct_of_summable_exp_neg_sum_one_sub
    (p : ResetWalkParameters) (hp : ∀ n : ℕ, 0 < p n)
    (h : Summable (fun n : ℕ ↦ Real.exp (-Finset.sum (Finset.range n) (fun k ↦ 1 - p k)))) :
    Summable (resetWalkPrefixProduct p) := by
  have hp_nonneg : ∀ n : ℕ, 0 ≤ p n := fun n ↦ le_of_lt (hp n)
  -- Proof comment: the textbook exponential majorant dominates every nonnegative prefix product
  -- term, so summability follows by comparison.
  refine Summable.of_nonneg_of_le (resetWalkPrefixProduct_nonneg p) ?_ h
  intro n
  exact resetWalkPrefixProduct_le_exp_neg_sum_one_sub p n

end ProbabilityTheory
