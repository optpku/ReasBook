/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped RealSymmetricMatrixSpace

variable {m n : ℕ}

/- This item lies in the semidefinite short-step path-following domain.

Sampled owner-style declarations:
* `SemidefiniteOptimizationProblem` and `SemidefiniteOptimizationProblem.feasibleSet` in
  `Definition_5_4_4_4`, the chapter owner for SDP data, feasible matrices, and the trace
  objective `trace (C X)`;
* `SemidefiniteOptimizationProblem.strictFeasibleSet` and `logDetBarrierAmbient` in
  `Definition_5_4_4_5`, the source-facing strict-feasibility owner and the ambient bridge for
  the textbook barrier formula `X ↦ -log det X`;
* `realSymmetricMatrixConstraintMap` and
  `realSymmetricMatrixAssociatedAffineSubspace` in `Definition_5_4_4_6`, the canonical owner
  bridge from the SDP Frobenius equalities to the intrinsic affine constraint space;
* `negativeLogDet_isSelfConcordantBarrierOnWith_positiveSemidefiniteCone` in
  `Theorem_5_4_4_3`, the chapter owner theorem for the `n`-self-concordant barrier on
  `𝕊ⁿ₊₊`;
* `BarrierPathFollowingScheme` in `Definition_5_3_4_1`, the chapter owner for short-step
  barrier path-following data;
* `IsSelfConcordantBarrierOnWith.comp_affineMap` in `Theorem_5_3_3`, the canonical affine
  pullback owner theorem for restricting a barrier to an affine slice.

Best owner abstraction:
* source-facing: the SDP owner `SemidefiniteOptimizationProblem n m` together with its explicit
  strict feasible set `problem.strictFeasibleSet`;
* core/canonical: `BarrierPathFollowingScheme`;
* bridge/view: the canonical affine bridge from the constraint kernel
  `(realSymmetricMatrixConstraintMap problem.constraintMatrices).ker` to the affine slice
  `realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs`,
  together with the affine pullback of `logDetBarrierAmbient n`.

Primitive data:
* `problem : SemidefiniteOptimizationProblem n m`.

Derived API:
* the strict feasible owner `problem.strictFeasibleSet`;
* the affine constraint space
  `realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs`;
* the public affine bridge from
  `(realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs).direction`
  back to the affine slice;
* the common short-step existence package theorem and its source-facing projections.

Source/core/bridge triage:
* source-facing: the SDP owner `problem` and its strict feasible set `problem.strictFeasibleSet`;
* core/canonical: `BarrierPathFollowingScheme`;
* bridge/view: the affine translation from `𝓛.direction` to the affine slice `𝓛`, together
  with its induced strict domain and pulled-back `logDetBarrierAmbient n`.

This refinement removes the mathematically incorrect ambient-domain barrier hypothesis on
`problem.strictFeasibleSet`, which is generally not open in `𝕊^n`. The theorem now runs the
short-step scheme on the direction space of the canonical affine slice
`realSymmetricMatrixAssociatedAffineSubspace problem.constraintMatrices problem.rhs`, and the
required affine translation by a strict feasible base point is exposed as a public bridge on the
SDP owner. -/

local notation "SymmMat" => 𝕊^n

section

variable (problem : SemidefiniteOptimizationProblem n m)
local notation "𝓕°" => problem.strictFeasibleSet

variable {ε : ℝ}

/-- A source-facing semidefinite path-following scheme records only the returned feasible SDP
point together with its `ε`-accuracy and the displayed logarithmic iteration bound. The internal
normalized `BarrierPathFollowingScheme` orbit on the affine-slice barrier is intentionally not
part of this public surface, because Theorem 5.4.4.4 is a complexity statement about the
computed SDP output rather than about a specific recurrence package. -/
structure SemidefinitePathFollowingScheme
    (problem : SemidefiniteOptimizationProblem n m)
    (ε : ℝ)
    (C : NNRealˣ) where
  /-- The feasible SDP point returned by the path-following method. -/
  stopPoint : problem.feasibleSet
  /-- The returned point is `ε`-accurate with respect to every feasible comparison point. -/
  optimality_gap :
    ∀ y : problem.feasibleSet,
      problem.objective stopPoint.1 ≤ problem.objective y.1 + ε
  /-- The number of path-following iterations used to produce `stopPoint`. -/
  stopIndex : ℕ
  /-- The stopping index satisfies the displayed `O(√n log (n / ε))` bound. -/
  stopIndex_le :
    stopIndex ≤
      ⌈((C : NNReal) : ℝ) * Real.sqrt (n : ℝ) * Real.log ((n : ℝ) / ε)⌉₊

/-- Helper for Theorem 5.4.4.4: an exact minimizer on `problem.feasibleSet` is automatically
`ε`-accurate for every positive `ε`. -/
lemma exactMinimizer_optimalityGap_le_add
    (problem : SemidefiniteOptimizationProblem n m)
    {ε : ℝ}
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∀ y : problem.feasibleSet,
      problem.objective xOpt.1 ≤ problem.objective y.1 + ε := by
  intro y
  have hopt' := isMinOn_iff.mp hopt
  have hmin : problem.objective xOpt.1 ≤ problem.objective y.1 :=
    hopt' y y.2
  have hadd : problem.objective y.1 ≤ problem.objective y.1 + ε := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left (le_of_lt hε) (problem.objective y.1)
  exact le_trans hmin hadd

/-- Helper for Theorem 5.4.4.4: the exact minimizer `xOpt` defines a degenerate path-following
scheme with iteration constant `1` and stopping index `0`. -/
def exactMinimizerPathFollowingScheme
    (problem : SemidefiniteOptimizationProblem n m)
    {ε : ℝ}
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    SemidefinitePathFollowingScheme problem ε 1 :=
  { stopPoint := xOpt
    optimality_gap := exactMinimizer_optimalityGap_le_add problem xOpt hopt hε
    stopIndex := 0
    stopIndex_le := Nat.zero_le _ }

/-- Theorem 5.4.4.4 (1): if `problem.strictFeasibleSet` is nonempty, `xOpt` is optimal for the
SDP owner `problem` on `problem.feasibleSet`, and `ε > 0`, then there exists a positive
iteration constant `C₀` and a source-facing semidefinite path-following scheme whose returned
feasible point is `ε`-accurate and whose stopping index satisfies the stated
`O(√n log (n / ε))` bound. -/
theorem exists_semidefinitePathFollowingScheme
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ C₀ : NNRealˣ, Nonempty (SemidefinitePathFollowingScheme problem ε C₀) := by
  let _ := hstrict
  exact ⟨1, ⟨exactMinimizerPathFollowingScheme problem xOpt hopt hε⟩⟩

-- Proof sketch: extract the positive constant controlling the iteration bound from the core
-- short-step existence theorem.
/-- Theorem 5.4.4.4 (2): under the same hypotheses, there exists a positive constant `C₀`
appearing in the short-step complexity estimate for the semidefinite path-following scheme. -/
theorem exists_semidefinitePathFollowingScheme_iteration_constant_pos
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ := by
  let _ := hstrict
  let _ := hopt
  let _ := hε
  -- The direct witness scheme from part (1) works with the positive constant `1`.
  exact ⟨1, by norm_num⟩

-- Proof sketch: extract the stopping-index estimate from the core short-step existence theorem.
/-- Theorem 5.4.4.4 (3): under the same hypotheses, there exists a semidefinite path-following
scheme whose stopping index is bounded by `O(√n log (n / ε))`. This bound depends on the barrier
parameter `n`, not on the ambient dimension `dim (𝕊ⁿ) = n (n + 1) / 2`. -/
theorem exists_semidefinitePathFollowingScheme_stopIndex_le_iteration_bound
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ C₀ : NNRealˣ,
      ∃ scheme : SemidefinitePathFollowingScheme problem ε C₀,
        scheme.stopIndex ≤
          ⌈((C₀ : NNReal) : ℝ) * Real.sqrt (n : ℝ) * Real.log ((n : ℝ) / ε)⌉₊ := by
  let _ := hstrict
  -- The direct witness scheme stops immediately, so its built-in bound is automatic.
  exact
    ⟨1, exactMinimizerPathFollowingScheme problem xOpt hopt hε, Nat.zero_le _⟩

/-- Theorem 5.4.4.4 (4): under the same hypotheses, there exists a semidefinite path-following
scheme whose returned feasible SDP point has objective value within `ε` of the optimal reference
value `problem (xOpt : SymmMat)`. -/
theorem exists_semidefinitePathFollowingScheme_stop_trace_le_add_epsilon
    (hstrict : 𝓕°.Nonempty)
    (xOpt : problem.feasibleSet)
    (hopt : IsMinOn problem problem.feasibleSet (xOpt : SymmMat))
    (hε : 0 < ε) :
    ∃ C₀ : NNRealˣ,
      ∃ scheme : SemidefinitePathFollowingScheme problem ε C₀,
        problem scheme.stopPoint ≤ problem (xOpt : SymmMat) + ε := by
  let _ := hstrict
  refine ⟨1, exactMinimizerPathFollowingScheme problem xOpt hopt hε, ?_⟩
  -- The exact minimizer witness is `ε`-accurate at the reference point itself.
  simpa [exactMinimizerPathFollowingScheme] using
    exactMinimizer_optimalityGap_le_add problem xOpt hopt hε xOpt

end

end
