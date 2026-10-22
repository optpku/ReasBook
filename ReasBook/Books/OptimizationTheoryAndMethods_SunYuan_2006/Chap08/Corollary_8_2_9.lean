/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_8
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7

noncomputable section

section Chapter08Corollary829

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

namespace ConstrainedOptimizationProblem

/-- Helper for Chapter08 Corollary 8.2.9: under `problem.LfcqAt xStar`, every active constraint
of `problem` at `xStar` is differentiable. -/
theorem hasActiveConstraintGradientsAt_of_lfcqAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (h_lfcq : problem.LfcqAt xStar) :
    problem.HasActiveConstraintGradientsAt xStar := by
  intro i hi
  -- Rewrite the active constraint to its linear representative and use differentiability of the
  -- associated continuous linear map.
  rcases h_lfcq.constraint_eq_linearMap_of_mem hi with ⟨ci, hci⟩
  let cci : Point →L[ℝ] ℝ := ⟨ci, ci.continuous_of_finiteDimensional⟩
  simpa [hci, cci] using cci.differentiableAt

/-- Helper for Chapter08 Corollary 8.2.9: along an active-constraint ray, LFCQ rewrites the
constraint value exactly as `t` times the linearized pairing. -/
theorem constraint_eq_smul_linearizedPairing_of_mem_activeConstraint
    (problem : ConstrainedOptimizationProblem n m E I) (xStar d : Point)
    (hxStar : xStar ∈ problem)
    (h_lfcq : problem.LfcqAt xStar) {i : Fin m}
    (hi : i ∈ problem.activeConstraintIndexSet xStar) (t : ℝ) :
    problem.constraint i (xStar + t • d) = t * problem.linearizedConstraintPairing xStar d i := by
  -- Replace the active constraint with its linear representative and then normalize both sides.
  rcases h_lfcq.constraint_eq_linearMap_of_mem hi with ⟨ci, hci⟩
  have hx_zero : problem.constraint i xStar = 0 := by
    rcases (problem.mem_activeConstraintIndexSet_iff xStar i).1 hi with hi_eq | hi_ineq
    · exact (problem.mem_iff xStar).1 hxStar |>.1 i hi_eq
    · exact hi_ineq.2
  let cci : Point →L[ℝ] ℝ := ⟨ci, ci.continuous_of_finiteDimensional⟩
  have hpair :
      problem.linearizedConstraintPairing xStar d i = ci d := by
    -- The Fréchet derivative of the linear representative is the representative itself.
    have hderiv :
        fderiv ℝ (problem.constraint i) xStar = cci := by
      rw [hci]
      simpa [cci] using cci.fderiv (x := xStar)
    simpa [problem.linearizedConstraintPairing_eq, cci] using
      congrArg (fun g : Point →L[ℝ] ℝ ↦ g d) hderiv
  have hx_zero' : ci xStar = 0 := by
    simpa [hci] using hx_zero
  calc
    problem.constraint i (xStar + t • d)
        = ci (xStar + t • d) := by simpa [hci]
    _ = ci xStar + t * ci d := by simp
    _ = t * ci d := by rw [hx_zero', zero_add]
    _ = t * problem.linearizedConstraintPairing xStar d i := by rw [hpair]

/-- Helper for Chapter08 Corollary 8.2.9: an inactive inequality remains nonnegative on a short
segment because it has strictly positive slack at `xStar` and is continuous there. -/
theorem inactiveIneq_nonneg_on_small_segment
    (problem : ConstrainedOptimizationProblem n m E I) (xStar d : Point)
    (hxStar : xStar ∈ problem)
    (h_constraints : problem.HasConstraintGradientsAt xStar) {i : Fin m}
    (hi : i ∈ problem.ineqIndices)
    (hi_not_active : i ∉ problem.activeConstraintIndexSet xStar) :
    ∃ δi > 0, ∀ t ∈ Set.Icc (0 : ℝ) δi,
      0 ≤ problem.constraint i (xStar + t • d) := by
  have hpos : 0 < problem.constraint i xStar :=
    (problem.not_mem_activeConstraintIndexSet_iff hxStar i).1 hi_not_active |>.2
  have hpos0 : 0 < (fun t : ℝ ↦ problem.constraint i (xStar + t • d)) 0 := by
    simpa using hpos
  have hcont :
      ContinuousAt (fun t : ℝ ↦ problem.constraint i (xStar + t • d)) 0 := by
    -- Compose continuity of the constraint at `xStar` with the affine ray `t ↦ xStar + t • d`.
    have hray : ContinuousAt (fun t : ℝ ↦ xStar + t • d) 0 := by
      change ContinuousAt ((fun t : ℝ ↦ xStar) + fun t : ℝ ↦ t • d) 0
      exact continuous_const.add (continuous_id.smul continuous_const) |>.continuousAt
    have hconstraint0 : ContinuousAt (problem.constraint i) ((fun t : ℝ ↦ xStar + t • d) 0) := by
      simpa using (h_constraints i).continuousAt
    exact ContinuousAt.comp hconstraint0 hray
  have hpos_event :
      ∀ᶠ t in nhds (0 : ℝ), 0 < problem.constraint i (xStar + t • d) :=
    hcont (lt_mem_nhds hpos0)
  rcases Metric.mem_nhds_iff.mp hpos_event with ⟨ε, hε_pos, hε_ball⟩
  refine ⟨ε / 2, by positivity, ?_⟩
  intro t ht
  have ht_ball : t ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have ht_lt : t < ε := by linarith [ht.2]
    simpa [abs_of_nonneg ht.1] using ht_lt
  exact (hε_ball ht_ball).le

/-- Helper for Chapter08 Corollary 8.2.9: every nonzero linearized feasible direction becomes a
source feasible direction under LFCQ. -/
theorem isFeasibleDirectionAt_of_mem_linearizedFeasibleDirectionSet_of_ne_of_lfcqAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar d : Point)
    (hxStar : xStar ∈ problem)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_lfcq : problem.LfcqAt xStar)
    (hd : d ∈ problem.linearizedFeasibleDirectionSet xStar) (hd_ne : d ≠ 0) :
    IsFeasibleDirectionAt problem.feasibleSet xStar d := by
  rw [problem.mem_linearizedFeasibleDirectionSet_iff_explicit] at hd
  rcases hd with ⟨_, _, h_eq, h_activeIneq⟩
  -- Build one short positive radius for each inactive inequality.
  classical
  have h_radius :
      ∀ i : Fin m,
        i ∈ problem.ineqIndices →
          i ∉ problem.activeConstraintIndexSet xStar →
            ∃ δi > 0, ∀ t ∈ Set.Icc (0 : ℝ) δi,
              0 ≤ problem.constraint i (xStar + t • d) := by
    intro i hi hi_not_active
    exact problem.inactiveIneq_nonneg_on_small_segment xStar d hxStar h_constraints hi hi_not_active
  let radius : Fin m → ℝ := fun i ↦
    if h : i ∈ problem.ineqIndices ∧ i ∉ problem.activeConstraintIndexSet xStar then
      Classical.choose (h_radius i h.1 h.2)
    else
      1
  have hradius_pos : ∀ i : Fin m, 0 < radius i := by
    intro i
    by_cases hi : i ∈ problem.ineqIndices ∧ i ∉ problem.activeConstraintIndexSet xStar
    · simpa [radius, hi] using (Classical.choose_spec (h_radius i hi.1 hi.2)).1
    · simp [radius, hi]
  have hradius_mem :
      ∀ {i : Fin m}, i ∈ problem.ineqIndices →
        i ∉ problem.activeConstraintIndexSet xStar →
          ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) (radius i) →
            0 ≤ problem.constraint i (xStar + t • d) := by
    intro i hi hi_not_active t ht
    have hi' : i ∈ problem.ineqIndices ∧ i ∉ problem.activeConstraintIndexSet xStar :=
      ⟨hi, hi_not_active⟩
    have ht' : t ∈ Set.Icc (0 : ℝ) (Classical.choose (h_radius i hi hi_not_active)) := by
      simpa [radius, hi'] using ht
    exact (Classical.choose_spec (h_radius i hi hi_not_active)).2 t ht'
  let inactive : Finset (Fin m) :=
    Finset.univ.filter (fun i ↦ i ∈ problem.ineqIndices ∧
      i ∉ problem.activeConstraintIndexSet xStar)
  let radii : Finset ℝ := insert 1 (inactive.image radius)
  let δ : ℝ := radii.min' (by simp [radii])
  have hδ_pos : 0 < δ := by
    -- The inserted radius `1` handles the degenerate case with no inactive inequalities.
    rw [show δ = radii.min' (by simp [radii]) by rfl, Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · norm_num
    · rcases Finset.mem_image.1 hy with ⟨i, hi_mem, rfl⟩
      exact hradius_pos i
  refine ⟨hd_ne, ⟨δ, hδ_pos, ?_⟩⟩
  intro t ht
  -- Check the equality and inequality constraints separately on the short feasible ray.
  rw [problem.feasibleSet_eq_setOf_mem, Set.mem_setOf_eq, problem.mem_iff]
  constructor
  · intro i hi_eq
    have hi_active :
        i ∈ problem.activeConstraintIndexSet xStar :=
      (problem.mem_activeConstraintIndexSet_iff xStar i).2 (Or.inl hi_eq)
    rw [problem.constraint_eq_smul_linearizedPairing_of_mem_activeConstraint xStar d hxStar
      h_lfcq hi_active t, h_eq i hi_eq, mul_zero]
  · intro i hi_ineq
    by_cases hi_active : i ∈ problem.activeConstraintIndexSet xStar
    · have hi_not_eq : i ∉ problem.eqIndices := by
        have hdisj : Disjoint problem.eqIndices problem.ineqIndices := by
          simpa [ConstrainedOptimizationProblem.eqIndices,
            ConstrainedOptimizationProblem.ineqIndices] using
            problem.eqIndices_disjoint_ineqIndices
        exact Set.disjoint_right.mp hdisj hi_ineq
      have hi_activeIneq : i ∈ problem.activeIneqIndexSet xStar := by
        rcases (problem.mem_activeConstraintIndexSet_iff xStar i).1 hi_active with hi_eq | hi'
        · exact False.elim (hi_not_eq hi_eq)
        · exact hi'
      rw [problem.constraint_eq_smul_linearizedPairing_of_mem_activeConstraint xStar d hxStar
        h_lfcq hi_active t]
      exact mul_nonneg ht.1 (h_activeIneq i hi_activeIneq)
    · have hi_mem : i ∈ inactive := by
        exact Finset.mem_filter.2 ⟨Finset.mem_univ i, hi_ineq, hi_active⟩
      have hδ_le : δ ≤ radius i := by
        exact Finset.min'_le radii (radius i) <|
          Finset.mem_insert.2 <| Or.inr <|
            Finset.mem_image.2 ⟨i, hi_mem, rfl⟩
      exact hradius_mem hi_ineq hi_active ⟨ht.1, le_trans ht.2 hδ_le⟩

/-- Under `problem.LfcqAt xStar`, the Chapter 8
constraint qualification `problem.ConstraintQualificationAt xStar` holds at the feasible point
`xStar`, provided all constraints are differentiable at `xStar`. -/
theorem constraintQualificationAt_of_lfcqAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_lfcq : problem.LfcqAt xStar) :
    problem.ConstraintQualificationAt xStar := by
  rw [problem.constraintQualificationAt_iff]
  ext d
  constructor
  · intro hd
    -- The forward inclusion is the existing Chapter 8 tangent-to-linearized bridge.
    exact sequentialFeasibleDirections_subset_linearizedFeasibleDirectionSet
      problem xStar hxStar (problem.hasActiveConstraintGradientsAt_of_lfcqAt xStar h_lfcq) hd
  · intro hd
    by_cases hd_zero : d = 0
    · subst d
      -- The zero direction is always in the positive tangent cone at a feasible base point.
      exact (mem_posTangentConeAt_iff_exists_seq_pos).2 <|
        ⟨fun _ ↦ (0 : Point), fun k ↦ 1 / ((k : ℝ) + 1), by
            intro k
            positivity, by
            intro k
            simpa [smul_zero, problem.feasibleSet_eq_setOf_mem] using hxStar, by
            exact
              (tendsto_const_nhds :
                Filter.Tendsto (fun _ : ℕ ↦ (0 : Point)) Filter.atTop (nhds (0 : Point))), by
            exact
              (tendsto_one_div_add_atTop_nhds_zero_nat :
                Filter.Tendsto (fun k : ℕ ↦ 1 / ((k : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ)))⟩
    · exact
        (problem.isFeasibleDirectionAt_of_mem_linearizedFeasibleDirectionSet_of_ne_of_lfcqAt
          xStar d hxStar h_constraints h_lfcq hd hd_zero).mem_posTangentConeAt

end ConstrainedOptimizationProblem

/-- Chapter08 Corollary 8.2.9: under the standing differentiability setup of the Chapter 8 KKT
theorem, if `xStar` is a feasible local minimizer of `problem` and the linear function
constraint qualification `problem.LfcqAt xStar` holds,
then `xStar` admits a KKT multiplier vector for `problem`. -/
theorem exists_isKKTPoint_of_isLocalMinOn_of_lfcqAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_lfcq : problem.LfcqAt xStar) :
    ∃ lamStar : Fin m → ℝ, problem.IsKKTPoint xStar lamStar :=
  exists_isKKTPoint_of_isLocalMinOn_of_constraintQualificationAt problem xStar hxStar
    h_localMin h_objective h_constraints
    (problem.constraintQualificationAt_of_lfcqAt xStar hxStar h_constraints h_lfcq)

end Chapter08Corollary829
