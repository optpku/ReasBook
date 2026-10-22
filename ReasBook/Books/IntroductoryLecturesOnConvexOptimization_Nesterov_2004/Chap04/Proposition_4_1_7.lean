/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.7 lies in the Chapter 4 cubic-regularized quadratic / Lagrangian-epigraph
domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the source-facing owner of the cubic
  model;
* `cubicRegularizedQuadraticEpigraphProblem` in `Definition_4_1_14`, the source-facing owner of
  the slack-variable reformulation;
* `LagrangianProblem.feasibleSet` in `Definition_1_10_2`, the canonical feasible-set owner for
  the epigraph problem;
* `partialInfProjection` in `Theorem_3_1_2_3`, the chapter owner for fiberwise infima.

Best owner abstraction:
* source-facing: eliminate the slack variable `τ` for fixed `h`;
* core/canonical: the owner pair `P : E × ℝ → ℝ` together with `P.feasibleSet`;
* bridge/view: the fiberwise least-value statement and the comparison with `P.primalOptimalValue`.

Primitive data:
* `g`, `H`, `M`, and the induced epigraph owner `P`;
* the feasible fiber above `h`, cut out by `P.feasibleSet`.

Derived API:
* `cubicRegularizedQuadraticObjective g H M`;
* `P.feasibleSet` and `P.primalOptimalValue`;
* the pointwise slack-elimination statement and the resulting comparison of global infima.

This file stays source-facing: the first theorem records the textbook slack elimination on the
real `τ`-fiber, while the second theorem compares the global infima of the original objective and
the owner epigraph problem. -/

section

variable (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)

local notation "P" => cubicRegularizedQuadraticEpigraphProblem g H M
local notation "F" => LagrangianProblem.feasibleSet P

/-- Helper for the slack-fiber feasibility equivalence: on the `h`-fiber, feasibility for the epigraph reformulation is
exactly the scalar inequality `‖h‖² ≤ τ`. -/
lemma mem_cubicRegularizedQuadraticEpigraphFeasibleFiber_iff
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    {h : E} {τ : ℝ} :
    (h, τ) ∈
        LagrangianProblem.feasibleSet (cubicRegularizedQuadraticEpigraphProblem g H M) ↔
      ‖h‖ ^ (2 : ℕ) ≤ τ := by
  constructor
  · intro hz
    -- Rewrite the single inequality constraint and clear the harmless `1 / 2` factors.
    have hconstraint :
        (1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * τ ≤ 0 := by
      simpa [cubicRegularizedQuadraticEpigraphProblem] using
        ((LagrangianProblem.mem_feasibleSet_iff
            (cubicRegularizedQuadraticEpigraphProblem g H M)).1 hz 0)
    nlinarith
  · intro hτ
    -- The converse direction packages the scalar inequality back into the owner feasible set.
    refine (LagrangianProblem.mem_feasibleSet_iff
      (cubicRegularizedQuadraticEpigraphProblem g H M)).2 ?_
    intro j
    fin_cases j
    simpa [cubicRegularizedQuadraticEpigraphProblem] using
      (show (1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * τ ≤ 0 by nlinarith)

/-- Helper for the tight slack `τ = ‖h‖²`: this value is always feasible in the epigraph
fiber above `h`. -/
lemma norm_sq_mem_cubicRegularizedQuadraticEpigraphFeasibleFiber
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (h : E) :
    (h, ‖h‖ ^ (2 : ℕ)) ∈
        LagrangianProblem.feasibleSet (cubicRegularizedQuadraticEpigraphProblem g H M) := by
  -- The tight slack saturates the scalar feasibility inequality.
  exact
    (mem_cubicRegularizedQuadraticEpigraphFeasibleFiber_iff g H M).2 le_rfl

/-- Helper for fiberwise epigraph monotonicity: along a feasible epigraph fiber, the objective is minimized at
the tight slack `τ = ‖h‖²`. -/
lemma cubicRegularizedQuadraticEpigraphObjective_mono_of_feasible
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (hM : 0 < M) {h : E} {τ : ℝ}
    (hτ : (h, τ) ∈
      LagrangianProblem.feasibleSet (cubicRegularizedQuadraticEpigraphProblem g H M)) :
    cubicRegularizedQuadraticEpigraphProblem g H M (h, ‖h‖ ^ (2 : ℕ)) ≤
      cubicRegularizedQuadraticEpigraphProblem g H M (h, τ) := by
  have hnorm_sq_le : ‖h‖ ^ (2 : ℕ) ≤ τ :=
    (mem_cubicRegularizedQuadraticEpigraphFeasibleFiber_iff g H M).1 hτ
  have hnorm_sq_nonneg : 0 ≤ ‖h‖ ^ (2 : ℕ) := by positivity
  have hτ_nonneg : 0 ≤ τ := le_trans hnorm_sq_nonneg hnorm_sq_le
  have hrpow :
      (‖h‖ ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) ≤ τ ^ (3 / 2 : ℝ) :=
    Real.rpow_le_rpow hnorm_sq_nonneg hnorm_sq_le (by norm_num)
  have hM_div_six_nonneg : 0 ≤ M / 6 := by nlinarith
  have hcubic :
      (M / 6 : ℝ) * ((‖h‖ ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) ≤
        (M / 6 : ℝ) * (τ ^ (3 / 2 : ℝ)) :=
    mul_le_mul_of_nonneg_left hrpow hM_div_six_nonneg
  have hsum :=
    add_le_add_left hcubic
      (dotProduct g h + (1 / 2 : ℝ) * dotProduct (Matrix.mulVec H h) h)
  -- Only the cubic slack term changes across the fiber; the quadratic part is fixed in `h`.
  simpa [cubicRegularizedQuadraticEpigraphProblem, abs_of_nonneg hnorm_sq_nonneg,
    abs_of_nonneg hτ_nonneg, add_assoc, add_left_comm, add_comm] using hsum

-- Proof sketch: fix `h`. The feasible fiber of `P` consists of the pairs `(h, τ)` with
-- `τ ≥ ‖h‖²`, so for `M > 0` the epigraph term `(M / 6) |τ|^(3/2)` is minimized at
-- `τ = ‖h‖²`; then
-- `cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq` identifies that minimum
-- with `cubicRegularizedQuadraticObjective g H M h`.
/-- Proposition 4.1.7 (1): for `M > 0`, fixing `h` and minimizing the slack-variable epigraph
objective over the feasible fiber of `cubicRegularizedQuadraticEpigraphProblem g H M` recovers
the original cubic-regularized quadratic value. -/
theorem cubicRegularizedQuadraticObjective_isLeast_overSlackFiber
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (hH : H.IsSymm) (hM : 0 < M) (h : E) :
    IsLeast
      ((fun τ : ℝ ↦ cubicRegularizedQuadraticEpigraphProblem g H M (h, τ)) ''
        {τ : ℝ |
          (h, τ) ∈
            LagrangianProblem.feasibleSet (cubicRegularizedQuadraticEpigraphProblem g H M)})
      (cubicRegularizedQuadraticObjective g H M h) := by
  -- The source statement assumes symmetry of `H`; retain that hypothesis in scope even though
  -- the slack-elimination argument itself only uses the epigraph feasibility geometry.
  have _ : H.IsSymm := hH
  refine ⟨?_, ?_⟩
  · -- The tight feasible slack realizes the advertised objective value.
    refine ⟨‖h‖ ^ (2 : ℕ), ?_, ?_⟩
    · exact norm_sq_mem_cubicRegularizedQuadraticEpigraphFeasibleFiber g H M h
    · simpa using cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq g H M h
  · -- Every other feasible slack has larger epigraph objective value.
    rintro y ⟨τ, hτ, rfl⟩
    simpa [cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq] using
      cubicRegularizedQuadraticEpigraphObjective_mono_of_feasible g H M hM hτ

-- Proof sketch: apply
-- `cubicRegularizedQuadraticObjective_isLeast_overSlackFiber` pointwise in `h`, then take the
-- infimum over all `h : ℝⁿ`; the right-hand side is the canonical owner
-- `LagrangianProblem.primalOptimalValue P`, whose expansion to the feasible-image `sInf` is
-- already upstream as
-- `LagrangianProblem.primalOptimalValue_eq_sInf_image`.
/-- Proposition 4.1.7 (2): for `M > 0`, the infimum of the original cubic-regularized quadratic
model agrees with the infimum of its slack-variable epigraph reformulation over the feasible set
of `cubicRegularizedQuadraticEpigraphProblem g H M`. -/
theorem cubicRegularizedQuadraticObjective_sInf_eq_slackProblem_sInf
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (hH : H.IsSymm) (hM : 0 < M) :
    sInf (Set.range fun h : E ↦ (cubicRegularizedQuadraticObjective g H M h : EReal)) =
      LagrangianProblem.primalOptimalValue (cubicRegularizedQuadraticEpigraphProblem g H M) := by
  rw [LagrangianProblem.primalOptimalValue_eq_sInf_image]
  refine le_antisymm ?_ ?_
  · refine le_sInf ?_
    intro y hy
    rcases hy with ⟨⟨h, τ⟩, hτ, rfl⟩
    -- Project a feasible pair `(h, τ)` to its `h`-fiber and use the fiberwise least-value theorem.
    have hsInfObjective :
        sInf (Set.range fun h' : E ↦ (cubicRegularizedQuadraticObjective g H M h' : EReal)) ≤
          (cubicRegularizedQuadraticObjective g H M h : EReal) :=
      sInf_le ⟨h, rfl⟩
    have hfiber_le :
        cubicRegularizedQuadraticObjective g H M h ≤
          cubicRegularizedQuadraticEpigraphProblem g H M (h, τ) :=
      (cubicRegularizedQuadraticObjective_isLeast_overSlackFiber g H M hH hM h).2
        ⟨τ, hτ, rfl⟩
    have hfiber_le_ereal :
        (cubicRegularizedQuadraticObjective g H M h : EReal) ≤
          (cubicRegularizedQuadraticEpigraphProblem g H M (h, τ) : EReal) := by
      simpa using hfiber_le
    exact hsInfObjective.trans hfiber_le_ereal
  · refine le_sInf ?_
    intro y hy
    rcases hy with ⟨h, rfl⟩
    -- Insert the tight feasible slack `τ = ‖h‖²`, which reproduces the original objective.
    have hsInfEpigraph :
        sInf
            ((fun z : E × ℝ ↦
                (cubicRegularizedQuadraticEpigraphProblem g H M z : EReal)) ''
              LagrangianProblem.feasibleSet
                (cubicRegularizedQuadraticEpigraphProblem g H M)) ≤
          (cubicRegularizedQuadraticEpigraphProblem g H M (h, ‖h‖ ^ (2 : ℕ)) : EReal) :=
      sInf_le
        ⟨(h, ‖h‖ ^ (2 : ℕ)),
          norm_sq_mem_cubicRegularizedQuadraticEpigraphFeasibleFiber g H M h,
          rfl⟩
    have hnorm_sq :
        (cubicRegularizedQuadraticEpigraphProblem g H M (h, ‖h‖ ^ (2 : ℕ)) : EReal) =
          (cubicRegularizedQuadraticObjective g H M h : EReal) := by
      exact congrArg (fun r : ℝ ↦ (r : EReal))
        (cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq g H M h)
    simpa [hnorm_sq] using hsInfEpigraph

end

end
