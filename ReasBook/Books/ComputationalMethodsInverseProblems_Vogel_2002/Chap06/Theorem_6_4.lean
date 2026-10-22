/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_24
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_29
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Exercise_2_17
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Theorem_2_30
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Assumption_6_3_extra_2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Exercise_6_9.WeakContinuity
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Lemma_6_3
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap06.Lemma_6_3.Approximation

public section

open Filter
open scoped Topology

universe u v

namespace OutputLeastSquares.MinimizingSequence

variable {Q : Type u} {Y : Type v}
variable [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
variable {F : Q → Y} {Fn : ℕ → Q → Y} {T : ℕ → Q → ℝ}
variable {C : ℕ → Set Q} {q : ℕ → Q} {d : ℕ → Y} {J : Q → ℝ}
variable {α δ : ℕ → ℝ} {qTrue : Q}

omit [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [InnerProductSpace ℝ Y] in
/-- Helper for Theorem 6.4: the penalty values `J (q n)` are bounded above along a minimizing
sequence. -/
lemma penaltyRange_bddAbove
    (hMin : MinimizingSequence F Fn T C q d J α δ qTrue) :
    BddAbove (Set.range fun n ↦ J (q n)) := by
  -- Bound the error-ratio term first and then absorb the fixed penalty at `qTrue`.
  rcases hMin.regularization.tendstoErrorSqDivAlpha.bddAbove_range with ⟨A, hA⟩
  refine ⟨A + J qTrue, ?_⟩
  rintro _ ⟨n, rfl⟩
  calc
    J (q n) ≤ δ n ^ 2 / α n + J qTrue :=
      penaltyBounded (F := F) (Fn := Fn) (T := T) (C := C) (q := q) (d := d) (J := J)
        (α := α) (δ := δ) (qTrue := qTrue) hMin n
    _ ≤ A + J qTrue := by
      linarith [hA ⟨n, rfl⟩]

/-- Helper for Theorem 6.4: a norm bound on the minimizing sequence gives a uniform lower bound for
`J (q n)`. -/
lemma exists_penaltyLowerBound_of_normBound
    (hJ_wlsc : weakLowerSemicontinuous J) (hJ_coercive : coercive J)
    {R : ℝ} (hR : ∀ n, ‖q n‖ ≤ R) :
    ∃ m, ∀ n, m ≤ J (q n) := by
  -- Minimize `J` on the closed ball that contains the whole sequence.
  let s : Set Q := Metric.closedBall (0 : Q) R
  have hs_nonempty : s.Nonempty := ⟨q 0, by simpa [s] using hR 0⟩
  have hs_closed : IsClosed s := by
    simpa [s] using Metric.isClosed_closedBall
  have hs_convex : Convex ℝ s := by
    simpa [s] using convex_closedBall (0 : Q) R
  obtain ⟨qMin, _, hqMin⟩ :=
    exists_isMinOn_of_weakLowerSemicontinuous_of_coercive J hs_nonempty hs_closed hs_convex
      hJ_wlsc hJ_coercive
  refine ⟨J qMin, ?_⟩
  intro n
  -- Evaluate the minimizing property at the sequence element `q n`.
  have hq_mem : q n ∈ s := by
    simpa [s] using hR n
  exact (isMinOn_iff.mp hqMin) (q n) hq_mem

omit [NormedAddCommGroup Q] [InnerProductSpace ℝ Q] [CompleteSpace Q] [InnerProductSpace ℝ Y] in
/-- Helper for Theorem 6.4: a uniform lower bound on `J (q n)` is enough to force the residual
`‖F (q n) - d n‖` to vanish. -/
lemma residualTendstoZero_of_penaltyLowerBound
    (hMin : MinimizingSequence F Fn T C q d J α δ qTrue)
    (hJ_lower : ∃ m, ∀ n, m ≤ J (q n)) :
    Tendsto (fun n ↦ ‖F (q n) - d n‖) atTop (𝓝 0) := by
  rcases hJ_lower with ⟨m, hm⟩
  -- Route correction: replace Lemma 6.3's unavailable nonnegativity hypothesis by a lower bound
  -- on `J` over the bounded minimizing sequence.
  have h_truePenalty :
      Tendsto (fun n ↦ α n * (J qTrue - m)) atTop (𝓝 0) := by
    simpa using hMin.regularization.tendstoAlpha.mul_const (J qTrue - m)
  have h_upper :
      Tendsto (fun n ↦ δ n ^ 2 + α n * (J qTrue - m)) atTop (𝓝 0) := by
    simpa using
      (deltaSqTendstoZero (F := F) (Fn := Fn) (T := T) (C := C) (q := q) (d := d) (J := J)
        (α := α) (δ := δ) (qTrue := qTrue) hMin).add h_truePenalty
  have h_sq_upper :
      ∀ n, ‖F (q n) - d n‖ ^ 2 ≤ δ n ^ 2 + α n * (J qTrue - m) := by
    intro n
    -- Rewrite the minimizing property and then substitute the lower bound `m ≤ J (q n)`.
    have h_min := hMin.objective_le_true n
    simp only [hMin.objective_eq, hMin.q_residual_eq, hMin.qTrue_residual_eq] at h_min
    rw [← hMin.delta_eq n] at h_min
    have h_scaled : α n * m ≤ α n * J (q n) := by
      exact mul_le_mul_of_nonneg_left (hm n) (le_of_lt (hMin.alpha_pos n))
    linarith
  have h_sq :
      Tendsto (fun n ↦ ‖F (q n) - d n‖ ^ 2) atTop (𝓝 0) := by
    -- Squeeze the squared residual between `0` and the upper bound that tends to `0`.
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper ?_ h_sq_upper
    intro n
    exact sq_nonneg _
  -- Apply `sqrt` to recover convergence of the residual itself.
  simpa [Real.sqrt_sq (norm_nonneg _)] using h_sq.sqrt

/-- Theorem 6.4. If
`hMin : MinimizingSequence F Fn T C q d J α δ qTrue` records the
shared Chapter 6 minimizing-sequence setup, with
`hMin.regularization : RegularizationParameterAssumptions α δ` encoding the asymptotic
clauses `(6.33)` and `(6.34)` as `Tendsto α atTop (𝓝 0)` and
`Tendsto (fun n ↦ δ n ^ 2 / α n) atTop (𝓝 0)`, `J` is weakly lower semicontinuous and
coercive, `F` is weakly continuous, and `(6.37)` holds at `qTrue`, then `q` admits a
weakly convergent subsequence with weak limit `qTrue`. -/
theorem exists_strictMono_subseq_weakSeqTendsto
    (hMin : MinimizingSequence F Fn T C q d J α δ qTrue)
    (hJ_wlsc : weakLowerSemicontinuous J)
    (hJ_coercive : coercive J)
    (hF_weak : Continuous (toWeakMap F))
    (h_ident : IsIdentifiableAt F qTrue) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ weakSeqTendsto (q ∘ φ) qTrue := by
  -- First combine the penalty estimate with coercivity to bound the minimizing sequence.
  have hJ_bdd :
      BddAbove (Set.range fun n ↦ J (q n)) :=
    penaltyRange_bddAbove (F := F) (Fn := Fn) (T := T) (C := C) (q := q) (d := d) (J := J)
      (α := α) (δ := δ) (qTrue := qTrue) hMin
  obtain ⟨R, hR⟩ :=
    exists_norm_le_of_coercive_of_bddAbove (J := J) (f := q) hJ_coercive hJ_bdd
  obtain ⟨φ, hφ, qStar, hqWeak⟩ :=
    exists_strictMono_subseq_weakSeqTendsto_of_bounded (f := q) ⟨R, hR⟩
  -- Recover the lower bound on `J` needed to reproduce the residual-vanishing argument.
  have hJ_lower :
      ∃ m, ∀ n, m ≤ J (q n) :=
    exists_penaltyLowerBound_of_normBound (J := J) (q := q) hJ_wlsc hJ_coercive hR
  have hResidualZero :
      Tendsto (fun n ↦ ‖F (q n) - d n‖) atTop (𝓝 0) :=
    residualTendstoZero_of_penaltyLowerBound (F := F) (Fn := Fn) (T := T) (C := C) (q := q)
      (d := d) (J := J) (α := α) (δ := δ) (qTrue := qTrue) hMin hJ_lower
  have hDeltaZero : Tendsto δ atTop (𝓝 0) := by
    -- The data-error sequence is nonnegative because it is the true residual norm.
    have hDeltaNonneg : ∀ n, 0 ≤ δ n := by
      intro n
      rw [hMin.delta_eq n]
      exact norm_nonneg _
    simpa [Real.sqrt_sq (hDeltaNonneg _)] using
      (deltaSqTendstoZero (F := F) (Fn := Fn) (T := T) (C := C) (q := q) (d := d) (J := J)
        (α := α) (δ := δ) (qTrue := qTrue) hMin).sqrt
  have hResidualSubseq :
      Tendsto (fun n ↦ ‖F (q (φ n)) - d (φ n)‖) atTop (𝓝 0) :=
    hResidualZero.comp hφ.tendsto_atTop
  have hDeltaSubseq :
      Tendsto (fun n ↦ δ (φ n)) atTop (𝓝 0) :=
    hDeltaZero.comp hφ.tendsto_atTop
  have hForwardNorm :
      Tendsto (fun n ↦ ‖F (q (φ n)) - F qTrue‖) atTop (𝓝 0) := by
    -- The triangle inequality compares the forward error with the residual and the data error.
    have h_upper :
        Tendsto (fun n ↦ ‖F (q (φ n)) - d (φ n)‖ + δ (φ n)) atTop (𝓝 0) :=
      by simpa using hResidualSubseq.add hDeltaSubseq
    have h_triangle :
        ∀ n, ‖F (q (φ n)) - F qTrue‖ ≤ ‖F (q (φ n)) - d (φ n)‖ + δ (φ n) := by
      intro n
      simpa [dist_eq_norm, hMin.delta_eq (φ n), norm_sub_rev] using
        dist_triangle (F (q (φ n))) (d (φ n)) (F qTrue)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_upper ?_ h_triangle
    intro n
    exact norm_nonneg _
  have hForwardStrong :
      Tendsto (fun n ↦ F (q (φ n))) atTop (𝓝 (F qTrue)) := by
    -- Norm convergence identifies the strong limit of the forward images.
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa using hForwardNorm
  have hForwardWeakStar :
      weakSeqTendsto (fun n ↦ F (q (φ n))) (F qStar) := by
    -- Weak continuity transports the weakly convergent subsequence through `F`.
    simpa [Function.comp_def] using Continuous.weakSeqTendsto_toWeakMap hF_weak hqWeak
  have hForwardWeakTrue :
      weakSeqTendsto (fun n ↦ F (q (φ n))) (F qTrue) := by
    -- Strong convergence implies weak convergence for the same subsequence.
    exact weakSeqTendsto_of_tendsto hForwardStrong
  have hForwardEq : F qStar = F qTrue := by
    -- Uniqueness of limits in `WeakSpace ℝ Y` identifies the weak image limit.
    rw [weakSeqTendsto_iff] at hForwardWeakStar hForwardWeakTrue
    exact (toWeakSpace ℝ Y).injective
      (tendsto_nhds_unique hForwardWeakStar hForwardWeakTrue)
  have hqStar : qStar = qTrue :=
    h_ident.eq_of_apply_eq hForwardEq
  -- Rewrite the weak limit of the subsequence using identifiability.
  exact ⟨φ, hφ, hqStar ▸ hqWeak⟩

/-- Theorem 6.4 under the stronger hypothesis that `F` is injective. -/
theorem exists_strictMono_subseq_weakSeqTendsto_of_injective
    (hMin : MinimizingSequence F Fn T C q d J α δ qTrue)
    (hJ_wlsc : weakLowerSemicontinuous J)
    (hJ_coercive : coercive J)
    (hF_weak : Continuous (toWeakMap F))
    (hF_injective : Function.Injective F) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ weakSeqTendsto (q ∘ φ) qTrue :=
  exists_strictMono_subseq_weakSeqTendsto hMin hJ_wlsc hJ_coercive hF_weak
    (hF_injective.isIdentifiableAt qTrue)

end OutputLeastSquares.MinimizingSequence
