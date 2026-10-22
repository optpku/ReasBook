/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_3
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Algorithm_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_1_1
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_4
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Definition_12_5
import FirstOrderMethodsOptimization_Beck_2017.Chap12.Theorem_12_8
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped Gradient
open InnerProductSpace (toDualMap)

section

variable {E : Type u} {V : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
variable (f : E → EReal) (g : V → EReal) (A : E →ₗ[ℝ] V)

-- Local declaration justification (source-local notation): the Chapter 12 split dual terms and
-- dual objective appear verbatim in every public statement in this file, and keeping the notation
-- file-local avoids introducing one-off public aliases for these already canonical owners.
local notation "F" => fun z : V ↦ dual_based_proximal_gradient_dual_F_term f A (toDualMap ℝ V z)
local notation "G" => fun z : V ↦ dual_based_proximal_gradient_dual_G_term g (toDualMap ℝ V z)
local notation "gradF" => fun z : V ↦ ∇ (fun z' : V ↦ EReal.toReal (F z')) z
local notation "q" => dual_based_proximal_gradient_lagrange_dual_objective_primal f g A
local notation "qOpt" => dual_based_proximal_gradient_lagrange_dual_problem_value f g A

/- Theorem 12.9 uses the same source-facing versus core/canonical split as Theorem 12.10.

The canonical reusable rate is stated for the Algorithm 12.3 dual trajectory owner
`IsFastDualProximalGradientDualTrajectory`. The source-facing Algorithm 12.4 trajectory owner
`IsFastDualProximalGradientPrimalTrajectory` appears only through the transport theorem below and
the labeled wrapper theorem. -/

/-- A fast dual proximal-gradient primal trajectory canonically determines the corresponding fast
dual proximal-gradient dual trajectory for the Chapter 12 split dual terms `F` and `G`. -/
theorem IsFastDualProximalGradientPrimalTrajectory.toDualTrajectory
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {y0 : V} {u : ℕ → E} {y w : ℕ → V} {t : ℕ → ℝ}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (htraj : IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t) :
    IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ G gradF L y0 y w := by
  let Fexp : V → EReal := fun z ↦ (f∗) (A.adjoint z)
  let Gexp : V → EReal := fun z ↦ (g∗) (-z)
  let gradFexp : V → V := fun z ↦ ∇ (fun z' : V ↦ (Fexp z').toReal) z
  have hF_eq : F = Fexp := by
    funext z
    exact dual_based_proximal_gradient_dual_F_primal_apply f A z
  have hG_eq : G = Gexp := by
    funext z
    exact dual_based_proximal_gradient_dual_G_primal_apply g z
  have hFreal_eq :
      (fun z : V ↦ (F z).toReal) = fun z ↦ (Fexp z).toReal := by
    funext z
    simpa [Fexp] using
      congrArg EReal.toReal (dual_based_proximal_gradient_dual_F_primal_apply f A z)
  have hgradF_eq : gradF = gradFexp := by
    funext z
    exact congrArg (fun φ : V → ℝ ↦ ∇ φ z) hFreal_eq
  refine
    IsFastDualProximalGradientDualTrajectory.ofSourceMomentum
      htraj.y_zero
      htraj.w_zero
      ?_
      ?_
  · intro k
    have huk_eq :
        u k = ∇ (fun z : E ↦ ((f∗) z).toReal) (A.adjoint (w k)) :=
      dualPrimalArgmax_eqConjugateGradient
        f
        g
        A
        h_problem
        (htraj.primal_step k)
    have hy_step :
        y (k + 1) ∈
          dual_proximal_gradient_primal_y_step
            g
            A
            (∇ (fun z : E ↦ ((f∗) z).toReal) (A.adjoint (w k)))
            (w k)
            (L : PosReal) := by
      simpa [huk_eq] using htraj.dual_step k
    have hy_dual :
        y (k + 1) ∈
          dual_based_proximal_gradient_dual_step
            Gexp
            gradFexp
            (L : PosReal)
            (w k) := by
      simpa [Gexp, gradFexp, Fexp] using
        (dualBasedDualStep_iff_memDualPrimalYStepZeroShift
          f
          g
          A
          h_problem
          (y (k + 1))
          (w k)
          (L : PosReal)).2 hy_step
    rw [hG_eq, hgradF_eq]
    exact hy_dual
  · intro k
    simpa [htraj.momentum_eqFistaSequence k, htraj.momentum_eqFistaSequence (k + 1)] using
      htraj.momentum_step k

/-- Helper for Theorem 12.9: the canonical momentum recursion satisfies the exact quadratic
identity `t_(k+1)^2 - t_(k+1) = t_k^2`. -/
lemma fistaMomentumQuadraticIdentity (k : ℕ) :
    fista_momentum_sequence (k + 1) ^ (2 : ℕ) - fista_momentum_sequence (k + 1) =
      fista_momentum_sequence k ^ (2 : ℕ) := by
  -- Normalize the scalar recursion once before using it in the Lyapunov telescope.
  rw [fista_momentum_sequence_succ, fista_momentum_update_eq]
  have hrad : 0 ≤ 1 + 4 * fista_momentum_sequence k ^ (2 : ℕ) := by
    positivity
  have hsq :
      (Real.sqrt (1 + 4 * fista_momentum_sequence k ^ (2 : ℕ))) ^ (2 : ℕ) =
        1 + 4 * fista_momentum_sequence k ^ (2 : ℕ) := by
    nlinarith [Real.sq_sqrt hrad]
  nlinarith [hsq]

/-- Helper for Theorem 12.9: rewriting `qOpt - q yBar` to the Chapter 12 split objective gap
only requires the standard `-q` normalization and finiteness of `qOpt`. -/
lemma dualObjectiveGap_eq_splitObjectiveGap
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (yStar : V)
    (hyStar : q yStar = qOpt)
    (yBar : V) :
    qOpt - q yBar =
      composite_model_objective F G yBar - (((-EReal.toReal qOpt : ℝ)) : EReal) := by
  have hqOpt_ne_top : qOpt ≠ ⊤ := by
    -- The optimal dual value is finite because it is attained at `yStar`.
    rw [← hyStar]
    exact
      dualObjective_ne_top
        (f := f)
        (g := g)
        (A := A)
        σ
        h_problem.toIsProperExtendedRealFunction
        h_problem.f_closed
        h_problem.f_strongly_convex
        h_problem.g_proper
        h_problem.g_convex
        yStar
  have hqOpt_ne_bot : qOpt ≠ ⊥ := by
    -- Properness of the dual objective supplies a finite lower witness, so `qOpt` cannot be `⊥`.
    rcases
        exists_dualObjective_ne_bot
          (f := f)
          (g := g)
          (A := A)
          σ
          h_problem.toIsProperExtendedRealFunction
          h_problem.f_closed
          h_problem.f_strongly_convex
          h_problem.g_proper
          h_problem.g_convex with
      ⟨yWitness, hyWitness⟩
    have hyWitness_le : q yWitness ≤ qOpt :=
      dualObjective_le_dualProblemValue (f := f) (g := g) (A := A) yWitness
    intro hqOpt_bot
    rw [hqOpt_bot] at hyWitness_le
    exact hyWitness (le_bot_iff.mp hyWitness_le)
  have hneg_qOpt_coe :
      (((-EReal.toReal qOpt : ℝ)) : EReal) = -qOpt := by
    -- Coercing the finite optimal value to `ℝ` commutes with negation in `EReal`.
    simpa using congrArg Neg.neg (EReal.coe_toReal hqOpt_ne_top hqOpt_ne_bot)
  calc
    qOpt - q yBar =
        composite_model_objective F G yBar - (((-EReal.toReal qOpt : ℝ)) : EReal) := by
      rw [dualCompositeObjective_eq_negDualObjective
          (f := f)
          (g := g)
          (A := A)
          σ
          h_problem.toIsProperExtendedRealFunction
          h_problem.f_closed
          h_problem.f_strongly_convex
          h_problem.g_proper
          h_problem.g_convex
          yBar,
        hneg_qOpt_coe]
      simp [sub_eq_add_neg, add_comm]

/-- Helper for Theorem 12.9: each accelerated dual iterate is exactly the Chapter 10 prox-gradient
point generated from the extrapolated base `w n`. -/
lemma shiftedDualExactProxPoint
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    [IsProperExtendedRealFunction G]
    [Fact (LowerSemicontinuous G)]
    [Fact (is_convex_function G)]
    {y0 : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ G gradF L y0 y w)
    (n : ℕ) :
    y (n + 1) = T[(L : PosReal); (fun z : V ↦ (F z).toReal), G] (w n) := by
  have hsingleton :
      dual_based_proximal_gradient_dual_step G gradF (L : PosReal) (w n) =
        {T[(L : PosReal); (fun z : V ↦ (F z).toReal), G] (w n)} := by
    -- The Chapter 12 dual step is definitionally the Chapter 10 forward prox-point singleton.
    simpa [dual_based_proximal_gradient_dual_step, proximal_gradient_step] using
      (prox_grad_operator_eq_singleton
        (f := (fun z : V ↦ (((F z).toReal : ℝ) : EReal)))
        (g := G)
        (L := (L : PosReal))
        (x := interior_effective_domain_point_of_real
          (fun z : V ↦ (F z).toReal)
          (w n)))
  have hstep : y (n + 1) ∈ dual_based_proximal_gradient_dual_step G gradF (L : PosReal) (w n) :=
    htraj.dual_step n
  rw [hsingleton] at hstep
  simpa using hstep

/-- Helper for Theorem 12.9: every positive accelerated dual iterate lies in the effective domain
of the nonsmooth split term `G`. -/
lemma shiftedDualPositiveIterate_memEffectiveDomainG
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    [IsProperExtendedRealFunction G]
    [Fact (LowerSemicontinuous G)]
    [Fact (is_convex_function G)]
    {y0 : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ G gradF L y0 y w)
    (n : ℕ) :
    y (n + 1) ∈ effective_domain G := by
  -- Read the iterate as the exact prox-gradient point and then apply the standard domain lemma.
  rw [shiftedDualExactProxPoint (f := f) (g := g) (A := A) htraj n]
  simpa using
    (prox_grad_step_mem_effective_domain_g
      (f := fun z : V ↦ (((F z).toReal : ℝ) : EReal))
      (g := G)
      (y := interior_effective_domain_point_of_real
        (fun z : V ↦ (F z).toReal)
        (w n))
      (L := (L : PosReal)))

/-- Helper for Theorem 12.9: the smooth dual term `F` is finite everywhere, so its effective
domain is all of `V`. -/
lemma shiftedDualSmoothEffectiveDomain_eq_univ
    (σ : PosReal)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    effective_domain F = Set.univ := by
  ext z
  constructor
  · intro _
    simp
  · intro _
    have harg :
        A.dualMap ↑((toDualMap ℝ V) z) = ↑((toDualMap ℝ E) (A.adjoint z)) := by
      ext x
      simpa [InnerProductSpace.toDualMap_apply_apply, real_inner_comm] using
        (LinearMap.adjoint_inner_left A x z).symm
    have hF_top :
        F z < ⊤ := by
      simpa [dual_based_proximal_gradient_dual_F_term, harg] using
        (dual_based_proximal_gradient_dual_F_primal_finite_valued
          (σ := σ)
          (f := f)
          (A := A)
          h_problem.toIsProperExtendedRealFunction
          h_problem.f_closed
          h_problem.f_strongly_convex
          z).2
    exact mem_effective_domain.mpr hF_top

/-- Helper for Theorem 12.9: the shifted Lyapunov residual
`u^0 = y^0 - yStar` and
`u^(k+1) = t_k y^(k+1) - (yStar + (t_k - 1) y^k)`. -/
def shiftedDualResidualToOptimum (y : ℕ → V) (yStar : V) : ℕ → V
  | 0 => y 0 - yStar
  | k + 1 =>
      (fista_momentum_sequence k : ℝ) • y (k + 1) -
        (yStar + (fista_momentum_sequence k - 1) • y k)

/-- Helper for Theorem 12.9: every FISTA momentum value is at least `1`, so the reciprocal
coefficient used in the comparison point lies in `[0, 1]`. -/
lemma shiftedDualOneLeMomentum (k : ℕ) : 1 ≤ fista_momentum_sequence k := by
  -- Lemma 10.33 gives the sharper lower bound `t_k ≥ (k + 2) / 2`.
  have hlinear :
      ((k : ℝ) + 2) / 2 ≤ fista_momentum_sequence k := by
    exact
      fista_momentum_sequence_lower_bound
        fista_momentum_sequence_zero
        fista_momentum_sequence_succ
        k
  have hone : (1 : ℝ) ≤ fista_momentum_sequence k := by
    have hk_nonneg : (0 : ℝ) ≤ k := by positivity
    have hbase : (1 : ℝ) ≤ ((k : ℝ) + 2) / 2 := by nlinarith
    exact le_trans hbase hlinear
  exact hone

/-- Helper for Theorem 12.9: every FISTA momentum reciprocal lies in the convex-combination
interval `[0, 1]`. -/
lemma shiftedDualOneDivMomentum_mem_Icc (k : ℕ) :
    ((fista_momentum_sequence k)⁻¹ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  have hone : (1 : ℝ) ≤ fista_momentum_sequence k := shiftedDualOneLeMomentum k
  have hpos : 0 < fista_momentum_sequence k := lt_of_lt_of_le zero_lt_one hone
  constructor
  · exact inv_nonneg.mpr (le_of_lt hpos)
  · have hrecip : 1 / fista_momentum_sequence k ≤ 1 / (1 : ℝ) :=
      one_div_le_one_div_of_le zero_lt_one hone
    simpa [one_div] using hrecip

/-- Helper for Theorem 12.9: an optimal dual point has finite `G`-value on the minimization
view, hence belongs to `effective_domain G`. -/
lemma shiftedDualOptimalPoint_memEffectiveDomainG
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {yStar : V}
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (hyStarMin :
      yStar ∈ unconstrained_problem_solutions (composite_model_objective F G)) :
    yStar ∈ effective_domain G := by
  let Obj := composite_model_objective F G
  letI :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions Obj)
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)) := hminproblem
  have hyStar_value :
      Obj yStar = (((-EReal.toReal qOpt : ℝ)) : EReal) :=
    IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
      hminproblem
      hyStarMin
  have hGy_top : G yStar ≠ ⊤ := by
    -- A finite optimal objective cannot contain an infinite `G` contribution.
    intro hGy_top
    have hObj_top : Obj yStar = ⊤ := by
      dsimp [Obj]
      have hsum :=
        congrArg
          (fun s : EReal =>
            dual_based_proximal_gradient_dual_F_term f A (toDualMap ℝ V yStar) + s)
          hGy_top
      have htop :
          dual_based_proximal_gradient_dual_F_term f A (toDualMap ℝ V yStar) + ⊤ = ⊤ := by
        simpa using
          EReal.add_top_of_ne_bot
            (hminproblem.f_ne_bot yStar)
      exact hsum.trans htop
    rw [hObj_top] at hyStar_value
    exact EReal.coe_ne_top _ hyStar_value.symm
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hGy_top)

/-- Helper for Theorem 12.9: scaling the displacement from the shifted comparison point clears the
reciprocal coefficient and exposes the affine vector used in the Lyapunov balance. -/
lemma shiftedDualScaledSubComparisonPoint
    (y : ℕ → V) (yStar point : V) (k : ℕ) :
    let θ : ℝ := (fista_momentum_sequence k)⁻¹
    let c : V := θ • yStar + (1 - θ) • y k
    (fista_momentum_sequence k : ℝ) • (point - c) =
      (fista_momentum_sequence k : ℝ) • point -
        (yStar + (fista_momentum_sequence k - 1) • y k) := by
  have htk_pos : 0 < fista_momentum_sequence k := by
    exact lt_of_lt_of_le zero_lt_one (shiftedDualOneLeMomentum k)
  have hθ :
      (fista_momentum_sequence k : ℝ) * (fista_momentum_sequence k)⁻¹ = 1 := by
    exact mul_inv_cancel₀ htk_pos.ne'
  have hycoeff :
      (fista_momentum_sequence k : ℝ) * (1 - (fista_momentum_sequence k)⁻¹) =
        fista_momentum_sequence k - 1 := by
    calc
      (fista_momentum_sequence k : ℝ) * (1 - (fista_momentum_sequence k)⁻¹) =
          (fista_momentum_sequence k : ℝ) -
            (fista_momentum_sequence k : ℝ) * (fista_momentum_sequence k)⁻¹ := by
        ring
      _ = fista_momentum_sequence k - 1 := by rw [hθ]
  -- Expand the comparison point once before collecting the cleared scalar coefficients.
  dsimp
  rw [smul_sub, smul_add]
  simp_rw [smul_smul]
  rw [hθ, hycoeff]
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 12.9: the shifted extrapolation formula rewrites the pre-step vector at
index `n` as the previous Lyapunov residual `u^n`. -/
lemma shiftedDualPrestepVector_eq_previousResidual
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    {y0 yStar : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ G gradF L y0 y w)
    (n : ℕ) (hn : 1 ≤ n) :
    (fista_momentum_sequence n : ℝ) • w n -
        (yStar + (fista_momentum_sequence n - 1) • y n) =
      shiftedDualResidualToOptimum y yStar n := by
  rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
  have ht_pos : 0 < fista_momentum_sequence (m + 1) := by
    exact lt_of_lt_of_le zero_lt_one (shiftedDualOneLeMomentum (m + 1))
  have ht_ne : fista_momentum_sequence (m + 1) ≠ 0 := ht_pos.ne'
  have hcoef_next :
      (fista_momentum_sequence (m + 1) : ℝ) *
          ((fista_momentum_sequence m - 1) / fista_momentum_sequence (m + 1)) =
        fista_momentum_sequence m - 1 := by
    field_simp [ht_ne]
  have hcoef_next' :
      (fista_momentum_sequence (1 + m) : ℝ) *
          ((fista_momentum_sequence m - 1) / fista_momentum_sequence (m + 1)) =
        fista_momentum_sequence m - 1 := by
    simpa [Nat.add_comm] using hcoef_next
  have hstep :
      w (1 + m) =
        y (1 + m) +
          ((fista_momentum_sequence m - 1) / fista_momentum_sequence (m + 1)) •
            (y (1 + m) - y m) := by
    simpa [Nat.add_comm] using htraj.momentum_step m
  -- Expand the shifted momentum step once before collapsing both scalar coefficients.
  rw [hstep]
  simp_rw [smul_add, smul_sub, smul_smul]
  simp_rw [hcoef_next']
  simp [shiftedDualResidualToOptimum, sub_eq_add_neg, add_left_comm, add_comm]
  module

/-- Helper for Theorem 12.9: the shifted comparison point satisfies the direct convex upper bound
on the Chapter 12 split objective. -/
lemma shiftedDualCombinationObjectiveUpperBoundReal
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {y : ℕ → V} {yStar : V}
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (hyStarMin :
      yStar ∈ unconstrained_problem_solutions (composite_model_objective F G))
    {n : ℕ}
    (hyEffn : y n ∈ effective_domain G) :
    let Obj := composite_model_objective F G
    let θ : ℝ := (fista_momentum_sequence n)⁻¹
    let c : V := θ • yStar + (1 - θ) • y n
    (Obj c).toReal ≤
      θ * (-EReal.toReal qOpt) + (1 - θ) * (Obj (y n)).toReal := by
  let Obj := composite_model_objective F G
  letI :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions Obj)
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)) := hminproblem
  letI : IsProperExtendedRealFunction G := hminproblem.g_proper
  let θ : ℝ := (fista_momentum_sequence n)⁻¹
  let c : V := θ • yStar + (1 - θ) • y n
  have hyStarEff : yStar ∈ effective_domain G :=
    shiftedDualOptimalPoint_memEffectiveDomainG
      (f := f)
      (g := g)
      (A := A)
      hminproblem
      hyStarMin
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    -- The FISTA reciprocal is the exact convex-combination weight from the source comparison point.
    simpa [θ] using shiftedDualOneDivMomentum_mem_Icc (k := n)
  have hθ_nonneg : 0 ≤ θ := hθ_mem.1
  have hone_sub_nonneg : 0 ≤ 1 - θ := sub_nonneg.mpr hθ_mem.2
  have hθ_sum : θ + (1 - θ) = 1 := by
    ring
  have hcEff : c ∈ effective_domain G := by
    -- Convexity of `G` keeps the shifted comparison point finite-valued.
    exact
      combo_mem_effective_domain_of_is_convex_function
        hminproblem.g_convex
        hyStarEff
        hyEffn
        hθ_mem
  have hFeff_univ :
      effective_domain F = Set.univ :=
    shiftedDualSmoothEffectiveDomain_eq_univ
      (f := f)
      (g := g)
      (A := A)
      σ
      h_problem
  letI : IsProperExtendedRealFunction F := by
    refine ⟨?_, ?_⟩
    · intro z
      rw [dual_based_proximal_gradient_dual_F_primal_apply (f := f) (A := A) (y := z)]
      exact
        (dual_based_proximal_gradient_dual_F_primal_finite_valued
          (f := f)
          (A := A)
          σ
          h_problem.toIsProperExtendedRealFunction
          h_problem.f_closed
          h_problem.f_strongly_convex
          z).1
    · exact ⟨0, by rw [hFeff_univ]; simp⟩
  have hc_obj :
      Obj c = ((((F c).toReal + (G c).toReal : ℝ)) : EReal) := by
    simpa [Obj] using
      (objectiveEqReal_of_memEffectiveDomainG (hproblem := hminproblem) hcEff)
  have hyn_obj :
      Obj (y n) = ((((F (y n)).toReal + (G (y n)).toReal : ℝ)) : EReal) := by
    simpa [Obj] using
      (objectiveEqReal_of_memEffectiveDomainG (hproblem := hminproblem) hyEffn)
  have hc_toReal :
      (Obj c).toReal = (F c).toReal + (G c).toReal := by
    -- Rewrite the split objective on the real surface once the `G` value is known to be finite.
    rw [hc_obj, EReal.toReal_coe]
  have hyn_toReal :
      (Obj (y n)).toReal = (F (y n)).toReal + (G (y n)).toReal := by
    -- The iterate surface uses the same finite-value normalization.
    rw [hyn_obj, EReal.toReal_coe]
  have hyStar_toReal :
      (F yStar).toReal + (G yStar).toReal = -EReal.toReal qOpt := by
    have hyStar_value :
        Obj yStar = (((-EReal.toReal qOpt : ℝ)) : EReal) :=
      IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
        hminproblem
        hyStarMin
    have hyStar_value' :
        ((((F yStar).toReal + (G yStar).toReal : ℝ)) : EReal) =
          (((-EReal.toReal qOpt : ℝ)) : EReal) := by
      rw [← hyStar_value]
      simpa [Obj] using
        (objectiveEqReal_of_memEffectiveDomainG (hproblem := hminproblem) hyStarEff).symm
    exact EReal.coe_eq_coe_iff.mp hyStar_value'
  have hyStarFeff : yStar ∈ effective_domain F := by
    rw [hFeff_univ]
    simp
  have hynFeff : y n ∈ effective_domain F := by
    rw [hFeff_univ]
    simp
  have hcFeff : c ∈ effective_domain F := by
    rw [hFeff_univ]
    simp
  have hyStarF_val :
      F yStar = ((((F yStar).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hyStarFeff).ne (hminproblem.f_ne_bot yStar)).symm
  have hynF_val :
      F (y n) = ((((F (y n)).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hynFeff).ne (hminproblem.f_ne_bot (y n))).symm
  have hcF_val :
      F c = ((((F c).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hcFeff).ne (hminproblem.f_ne_bot c)).symm
  have hyStarG_val :
      G yStar = ((((G yStar).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hyStarEff).ne (hminproblem.g_proper.ne_bot yStar)).symm
  have hynG_val :
      G (y n) = ((((G (y n)).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hyEffn).ne (hminproblem.g_proper.ne_bot (y n))).symm
  have hcG_val :
      G c = ((((G c).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hcEff).ne (hminproblem.g_proper.ne_bot c)).symm
  have hF_convexE :
      F c ≤
        (θ : EReal) * F yStar +
          (((1 - θ : ℝ) : EReal)) * F (y n) := by
    -- Convexity of the smooth term applies on the same affine segment because `F` is finite everywhere.
    simpa [c, θ, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (is_convex_function_iff_segment_ineq.mp hminproblem.f_convex)
        yStar
        hyStarFeff
        (y n)
        hynFeff
        hθ_mem
  have hF_convex :
      (F c).toReal ≤ θ * (F yStar).toReal + (1 - θ) * (F (y n)).toReal := by
    have hF_convex' : ((((F c).toReal : ℝ)) : EReal) ≤
        ((((θ * (F yStar).toReal + (1 - θ) * (F (y n)).toReal : ℝ)) : EReal)) := by
      rw [hcF_val, hyStarF_val, hynF_val] at hF_convexE
      simpa [EReal.coe_add, EReal.coe_mul] using hF_convexE
    exact EReal.coe_le_coe_iff.mp hF_convex'
  have hG_convexE :
      G c ≤
        (θ : EReal) * G yStar +
          (((1 - θ : ℝ) : EReal)) * G (y n) := by
    -- Jensen's inequality for `G` is used on the identical comparison point.
    simpa [c, θ, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (is_convex_function_iff_segment_ineq.mp hminproblem.g_convex)
        yStar
        hyStarEff
        (y n)
        hyEffn
        hθ_mem
  have hG_convex :
      (G c).toReal ≤ θ * (G yStar).toReal + (1 - θ) * (G (y n)).toReal := by
    have hG_convex' : ((((G c).toReal : ℝ)) : EReal) ≤
        ((((θ * (G yStar).toReal + (1 - θ) * (G (y n)).toReal : ℝ)) : EReal)) := by
      rw [hcG_val, hyStarG_val, hynG_val] at hG_convexE
      simpa [EReal.coe_add, EReal.coe_mul] using hG_convexE
    exact EReal.coe_le_coe_iff.mp hG_convex'
  have hupper_real :
      (Obj c).toReal ≤
        θ * (-EReal.toReal qOpt) + (1 - θ) * (Obj (y n)).toReal := by
    -- Add the smooth and nonsmooth convexity bounds, then replace the optimizer value by `-qOpt`.
    rw [hc_toReal, hyn_toReal]
    nlinarith [hF_convex, hG_convex, hyStar_toReal]
  simpa [Obj, θ, c] using hupper_real

/-- Helper for Theorem 12.9: subtracting the next iterate value from the comparison-point upper
bound produces the real-valued gap estimate used in the raw Lyapunov balance. -/
lemma shiftedDualComparisonGapUpperBoundReal
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {y : ℕ → V} {yStar : V}
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (hyStarMin :
      yStar ∈ unconstrained_problem_solutions (composite_model_objective F G))
    {n : ℕ}
    (hyEffn : y n ∈ effective_domain G) :
    let Obj := composite_model_objective F G
    let FOptR : ℝ := -EReal.toReal qOpt
    let vR : ℕ → ℝ := fun m ↦ (Obj (y m)).toReal - FOptR
    let θ : ℝ := (fista_momentum_sequence n)⁻¹
    let c : V := θ • yStar + (1 - θ) • y n
    (Obj c).toReal - (Obj (y (n + 1))).toReal ≤
      (1 - θ) * vR n - vR (n + 1) := by
  let Obj := composite_model_objective F G
  let FOptR : ℝ := -EReal.toReal qOpt
  let vR : ℕ → ℝ := fun m ↦ (Obj (y m)).toReal - FOptR
  let θ : ℝ := (fista_momentum_sequence n)⁻¹
  let c : V := θ • yStar + (1 - θ) • y n
  have hupper :
      (Obj c).toReal ≤
        θ * FOptR + (1 - θ) * (Obj (y n)).toReal := by
    -- Reuse the direct convex upper bound before packaging it as a gap estimate.
    simpa [Obj, FOptR, θ, c] using
      shiftedDualCombinationObjectiveUpperBoundReal
        (f := f)
        (g := g)
        (A := A)
        (σ := σ)
        (L := L)
        h_problem
        (y := y)
        (yStar := yStar)
        hminproblem
        hyStarMin
        (n := n)
        hyEffn
  have htarget :
      (Obj c).toReal - (Obj (y (n + 1))).toReal ≤
        (1 - θ) * vR n - vR (n + 1) := by
    calc
      (Obj c).toReal - (Obj (y (n + 1))).toReal ≤
          (θ * FOptR + (1 - θ) * (Obj (y n)).toReal) - (Obj (y (n + 1))).toReal := by
        linarith
      _ = (1 - θ) * vR n - vR (n + 1) := by
        simp [vR, FOptR]
        ring
  simpa [Obj, FOptR, vR, θ, c] using htarget

/-- Helper for Theorem 12.9: the Chapter 12 dual regularizer `G` inherits properness, lower
semicontinuity, and convexity from the primal regularizer `g`. -/
lemma shiftedDualRegularizerProperties
    {σ : PosReal}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ) :
    IsProperExtendedRealFunction G ∧ LowerSemicontinuous G ∧ is_convex_function G := by
  have hG_eq : G = fun z : V ↦ (g∗) (-z) := by
    funext z
    exact dual_based_proximal_gradient_dual_G_primal_apply g z
  refine ⟨?_, ?_, ?_⟩
  · -- Properness is the standard Chapter 12 dual-regularizer bridge.
    simpa [hG_eq] using
      (dual_based_proximal_gradient_dual_G_primal_proper
        (g := g)
        h_problem.g_proper
        h_problem.g_convex)
  · -- Lower semicontinuity is packaged together with convexity for the dual regularizer owner.
    simpa [hG_eq] using
      (dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).1
  · -- The same package also provides convexity on the dual side.
    simpa [hG_eq] using
      (dual_based_proximal_gradient_dual_G_primal_closed_and_convex (g := g)).2

/-- Helper for Theorem 12.9: the smooth split term `F` is finite everywhere, so it agrees with
its real-valued lift coerced back to `EReal`. -/
lemma shiftedDualSmoothTerm_eq_coeToReal
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (z : V) :
    F z = ((((F z).toReal : ℝ)) : EReal) := by
  have hz_eff : z ∈ effective_domain F := by
    rw [shiftedDualSmoothEffectiveDomain_eq_univ
      (f := f)
      (g := g)
      (A := A)
      σ
      h_problem]
    simp
  exact
    (EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne (hminproblem.f_ne_bot z)).symm

/-- Helper for Theorem 12.9: replacing the smooth split term `F` by its real-valued lift does not
change the composite objective. -/
lemma shiftedDualLiftedObjective_eqObjective
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (z : V) :
    composite_model_objective
        (fun x : V ↦ (((F x).toReal : ℝ) : EReal))
        G
        z =
      composite_model_objective F G z := by
  -- Rewrite only the smooth summand; the regularizer term is unchanged.
  calc
    composite_model_objective
        (fun x : V ↦ (((F x).toReal : ℝ) : EReal))
        G
        z =
      ((((F z).toReal : ℝ) : EReal) + G z) := by
        simp [composite_model_objective_apply]
    _ = F z + G z := by
      rw [← shiftedDualSmoothTerm_eq_coeToReal
        (f := f) (g := g) (A := A) (σ := σ) (L := L) h_problem hminproblem z]
    _ = composite_model_objective F G z := by
      simp [composite_model_objective_apply]

/-- Helper for Theorem 12.9: the constant smoothness parameter `L` satisfies the Chapter 10 B2
acceptance predicate at every Chapter 12 base point. -/
lemma shiftedDualAcceptedAtBasePoint
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    [IsProperExtendedRealFunction G]
    [Fact (LowerSemicontinuous G)]
    [Fact (is_convex_function G)]
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (yBase : V) :
    proximal_gradient_backtracking_B2_accepts
      (fun z : V ↦ (((F z).toReal : ℝ) : EReal))
      G
      (L : PosReal)
      (interior_effective_domain_point_of_real
        (fun z : V ↦ (F z).toReal)
        yBase) := by
  let yI :=
    interior_effective_domain_point_of_real
      (fun z : V ↦ (F z).toReal)
      yBase
  let xNext : V := T[(L : PosReal); (fun z : V ↦ (F z).toReal), G] yBase
  have hsmooth :
      is_l_smooth_on
        (fun z : V ↦ (F z).toReal)
        Set.univ
        (PosReal.toNNReal (L : PosReal)) := by
    have hsmoothInterior := hminproblem.f_toReal_smooth_on_interior_effective_domain
    -- The smooth dual term is finite everywhere, so the Chapter 10 smoothness field lives on `univ`.
    rw [shiftedDualSmoothEffectiveDomain_eq_univ
      (f := f) (g := g) (A := A) σ h_problem] at hsmoothInterior
    simpa using hsmoothInterior
  have hy_mem : yBase ∈ Set.univ := by simp
  have hxNext_mem : xNext ∈ Set.univ := by simp
  have hdescent :
      (F xNext).toReal ≤
        (F yBase).toReal +
          inner ℝ (∇ (fun z : V ↦ (F z).toReal) yBase) (xNext - yBase) +
          ((L : ℝ) / 2) * ‖xNext - yBase‖ ^ (2 : ℕ) := by
    -- Global smoothness supplies the real-valued upper model at the chosen Chapter 12 base point.
    simpa [xNext, yI, PosReal.coe_toNNReal, norm_sub_rev] using
      (is_l_smooth_on_descent_lemma convex_univ hsmooth hy_mem hxNext_mem)
  -- Repackage the real upper-model inequality as the owner-level B2 acceptance predicate.
  refine
    (proximal_gradient_backtracking_B2_accepts_iff
      (fun z : V ↦ (((F z).toReal : ℝ) : EReal))
      G
      (L : PosReal)
      yI).2 ?_
  exact EReal.coe_le_coe_iff.mpr <| by
    simpa [xNext, yI, Function.toEReal, add_assoc] using hdescent

/-- Helper for Theorem 12.9: convexity of the smooth split term makes the real-surface
prox-gradient linearization defect nonnegative at every base point. -/
lemma shiftedDualLinearizationDefectNonneg
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (xPoint yPoint : V) :
    (0 : EReal) ≤
      ℓ[(fun z : V ↦ (((F z).toReal : ℝ) : EReal)), xPoint,
        interior_effective_domain_point_of_real (fun z : V ↦ (F z).toReal) yPoint] := by
  let yI : interior (effective_domain F) := by
    refine ⟨yPoint, ?_⟩
    rw [shiftedDualSmoothEffectiveDomain_eq_univ
      (f := f) (g := g) (A := A) σ h_problem]
    simp
  have hxPoint_eff : xPoint ∈ effective_domain F := by
    rw [shiftedDualSmoothEffectiveDomain_eq_univ
      (f := f) (g := g) (A := A) σ h_problem]
    simp
  have hdefect :
      (0 : EReal) ≤ ℓ[F, xPoint, yI] := by
    -- Convexity of the Chapter 12 smooth term gives the same supporting-hyperplane defect bound.
    exact
      convexLinearizationDefect_nonneg
        (hproblem := hminproblem)
        hxPoint_eff
        yI
  have hxPoint_coe :
      F xPoint = ((((F xPoint).toReal : ℝ)) : EReal) :=
    shiftedDualSmoothTerm_eq_coeToReal
      (f := f) (g := g) (A := A) (σ := σ) (L := L) h_problem hminproblem xPoint
  have hyPoint_coe :
      F yPoint = ((((F yPoint).toReal : ℝ)) : EReal) :=
    shiftedDualSmoothTerm_eq_coeToReal
      (f := f) (g := g) (A := A) (σ := σ) (L := L) h_problem hminproblem yPoint
  have hdefect' := hdefect
  rw [prox_gradient_linearization_defect_eq] at hdefect'
  have hyI_coe :
      F ↑yI = ((((F yPoint).toReal : ℝ)) : EReal) := by
    simpa [yI] using hyPoint_coe
  have hxPoint_coe' :
      dual_based_proximal_gradient_dual_F_term f A ↑((toDualMap ℝ V) xPoint) =
        ((((F xPoint).toReal : ℝ)) : EReal) := by
    simpa using hxPoint_coe
  have hyI_coe' :
      dual_based_proximal_gradient_dual_F_term f A ↑((toDualMap ℝ V) ↑yI) =
        ((((F yPoint).toReal : ℝ)) : EReal) := by
    simpa [yI] using hyI_coe
  rw [hxPoint_coe', hyI_coe'] at hdefect'
  -- The lifted smooth-term spelling evaluates to the same real defect at the same base point.
  simpa [yI, interior_effective_domain_point_of_real, prox_gradient_linearization_defect_eq,
    Function.toEReal, EReal.coe_sub] using
    hdefect'

/-- Helper for Theorem 12.9: once the comparison point has finite `G`-value, the fundamental
prox-gradient inequality can be read directly on the real line. -/
lemma shiftedDualProxGapRealOfFiniteValues
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    [IsProperExtendedRealFunction G]
    [Fact (LowerSemicontinuous G)]
    [Fact (is_convex_function G)]
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (xPoint yPoint : V)
    (hxPoint : xPoint ∈ effective_domain G)
    (hmodel :
      proximal_gradient_backtracking_B2_accepts
        (fun z : V ↦ (((F z).toReal : ℝ) : EReal))
        G
        (L : PosReal)
        (interior_effective_domain_point_of_real
          (fun z : V ↦ (F z).toReal)
          yPoint)) :
    let Obj := composite_model_objective F G
    let zPlus : V := T[(L : PosReal); (fun z : V ↦ (F z).toReal), G] yPoint
    ((L : ℝ) / 2) * ‖xPoint - zPlus‖ ^ (2 : ℕ) -
        ((L : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) ≤
      (Obj xPoint).toReal - (Obj zPlus).toReal := by
  let Obj := composite_model_objective F G
  let ObjLift :=
    composite_model_objective
      (fun z : V ↦ (((F z).toReal : ℝ) : EReal))
      G
  let yI :=
    interior_effective_domain_point_of_real
      (fun z : V ↦ (F z).toReal)
      yPoint
  let zPlus : V := T[(L : PosReal); (fun z : V ↦ (F z).toReal), G] yPoint
  have hzPlus :
      zPlus ∈ effective_domain G := by
    -- The prox-gradient step from the Chapter 12 base point always lands in `effective_domain G`.
    simpa [zPlus, yI, prox_gradient_operator_apply] using
      (prox_grad_step_mem_effective_domain_g
        (f := fun z : V ↦ (((F z).toReal : ℝ) : EReal))
        (g := G)
        (y := yI)
        (L := (L : PosReal)))
  have hfund :
      ((((L : ℝ) / 2) * ‖xPoint - zPlus‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ) : EReal) +
          ℓ[(fun z : V ↦ (((F z).toReal : ℝ) : EReal)), xPoint, yI] ≤
        ObjLift xPoint - ObjLift zPlus := by
    -- Specialize the fundamental prox-gradient inequality at the comparison point `xPoint`.
    simpa [ObjLift, zPlus, yI] using
      (fundamental_prox_grad_inequality
        (f := fun z : V ↦ (((F z).toReal : ℝ) : EReal))
        (g := G)
        (x := xPoint)
        (y := yI)
        (L := (L : PosReal))
        hmodel)
  have hlin_nonneg :
      (0 : EReal) ≤
        ℓ[(fun z : V ↦ (((F z).toReal : ℝ) : EReal)), xPoint, yI] := by
    -- Convexity of the smooth dual term lets us drop the linearization defect.
    simpa [yI] using
      shiftedDualLinearizationDefectNonneg
        (f := f)
        (g := g)
        (A := A)
        (σ := σ)
        (L := L)
        h_problem
        hminproblem
        xPoint
        yPoint
  have hgapE :
      ((((L : ℝ) / 2) * ‖xPoint - zPlus‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        ObjLift xPoint - ObjLift zPlus := by
    have hinsert :
        ((((L : ℝ) / 2) * ‖xPoint - zPlus‖ ^ (2 : ℕ) -
              ((L : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
          ((((L : ℝ) / 2) * ‖xPoint - zPlus‖ ^ (2 : ℕ) -
                ((L : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ) : EReal) +
            ℓ[(fun z : V ↦ (((F z).toReal : ℝ) : EReal)), xPoint, yI] := by
      simpa [zero_add, add_assoc, add_left_comm, add_comm] using
        add_le_add_left hlin_nonneg
          ((((L : ℝ) / 2) * ‖xPoint - zPlus‖ ^ (2 : ℕ) -
              ((L : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ) : EReal)
    exact le_trans hinsert hfund
  have hgapEObj :
      ((((L : ℝ) / 2) * ‖xPoint - zPlus‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        Obj xPoint - Obj zPlus := by
    have hGx_coe :
        G xPoint = ((((G xPoint).toReal : ℝ)) : EReal) := by
      exact
        (EReal.coe_toReal (mem_effective_domain.mp hxPoint).ne
          (hminproblem.g_proper.ne_bot xPoint)).symm
    have hGz_coe :
        G zPlus = ((((G zPlus).toReal : ℝ)) : EReal) := by
      exact
        (EReal.coe_toReal (mem_effective_domain.mp hzPlus).ne
          (hminproblem.g_proper.ne_bot zPlus)).symm
    have hObj_x :
        ((((F xPoint).toReal : ℝ)) : EReal) + G xPoint = Obj xPoint := by
      rw [hGx_coe]
      symm
      simpa [Obj, composite_model_objective_apply, EReal.coe_add] using
        (objectiveEqReal_of_memEffectiveDomainG (hproblem := hminproblem) hxPoint)
    have hObj_z :
        ((((F zPlus).toReal : ℝ)) : EReal) + G zPlus = Obj zPlus := by
      rw [hGz_coe]
      symm
      simpa [Obj, composite_model_objective_apply, EReal.coe_add] using
        (objectiveEqReal_of_memEffectiveDomainG (hproblem := hminproblem) hzPlus)
    have hObjLift_x : ObjLift xPoint = Obj xPoint := by
      simpa [ObjLift] using hObj_x
    have hObjLift_z : ObjLift zPlus = Obj zPlus := by
      simpa [ObjLift] using hObj_z
    change
      ((((L : ℝ) / 2) * ‖xPoint - zPlus‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        ObjLift xPoint - ObjLift zPlus at hgapE
    rw [hObjLift_x, hObjLift_z] at hgapE
    exact hgapE
  have hxPoint_coe :
      Obj xPoint = ((((Obj xPoint).toReal : ℝ)) : EReal) := by
    have hxPoint_toReal :
        (Obj xPoint).toReal = (F xPoint).toReal + (G xPoint).toReal := by
      change
        (composite_model_objective F G xPoint).toReal =
          (F xPoint).toReal + (G xPoint).toReal
      have hObj_eq :=
        objectiveEqReal_of_memEffectiveDomainG (hproblem := hminproblem) hxPoint
      rw [hObj_eq]
      simpa [EReal.coe_add] using
        (EReal.toReal_coe ((F xPoint).toReal + (G xPoint).toReal))
    rw [hxPoint_toReal]
    have hGx_coe :
        G xPoint = ((((G xPoint).toReal : ℝ)) : EReal) := by
      exact
        (EReal.coe_toReal (mem_effective_domain.mp hxPoint).ne
          (hminproblem.g_proper.ne_bot xPoint)).symm
    rw [hGx_coe]
    simpa [Obj, composite_model_objective_apply, EReal.coe_add] using
      (objectiveEqReal_of_memEffectiveDomainG (hproblem := hminproblem) hxPoint)
  have hzPlus_coe :
      Obj zPlus = ((((Obj zPlus).toReal : ℝ)) : EReal) := by
    have hzPlus_toReal :
        (Obj zPlus).toReal = (F zPlus).toReal + (G zPlus).toReal := by
      change
        (composite_model_objective F G zPlus).toReal =
          (F zPlus).toReal + (G zPlus).toReal
      have hObj_eq :=
        objectiveEqReal_of_memEffectiveDomainG (hproblem := hminproblem) hzPlus
      rw [hObj_eq]
      simpa [EReal.coe_add] using
        (EReal.toReal_coe ((F zPlus).toReal + (G zPlus).toReal))
    rw [hzPlus_toReal]
    have hGz_coe :
        G zPlus = ((((G zPlus).toReal : ℝ)) : EReal) := by
      exact
        (EReal.coe_toReal (mem_effective_domain.mp hzPlus).ne
          (hminproblem.g_proper.ne_bot zPlus)).symm
    rw [hGz_coe]
    simpa [Obj, composite_model_objective_apply, EReal.coe_add] using
      (objectiveEqReal_of_memEffectiveDomainG (hproblem := hminproblem) hzPlus)
  have hgapE' :
      ((((L : ℝ) / 2) * ‖xPoint - zPlus‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖xPoint - yPoint‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        ((((Obj xPoint).toReal - (Obj zPlus).toReal : ℝ)) : EReal) := by
    rw [hxPoint_coe, hzPlus_coe, EReal.coe_sub] at hgapEObj
    simpa [EReal.coe_sub] using hgapEObj
  exact EReal.coe_le_coe_iff.mp hgapE'

/-- Helper for Theorem 12.9: specializing the prox-gradient inequality at the shifted comparison
point gives the accepted-step gap estimate on the literal Chapter 12 owner. -/
lemma shiftedDualGapToComparisonAtWReal
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {y0 : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ G gradF L y0 y w)
    {yStar : V}
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (hyStarMin :
      yStar ∈ unconstrained_problem_solutions (composite_model_objective F G))
    {n : ℕ}
    (hn : 1 ≤ n)
    (hyEffn : y n ∈ effective_domain G) :
    let Obj := composite_model_objective F G
    let θ : ℝ := (fista_momentum_sequence n)⁻¹
    let c : V := θ • yStar + (1 - θ) • y n
    ((L : ℝ) / 2) * ‖c - y (n + 1)‖ ^ (2 : ℕ) -
        ((L : ℝ) / 2) * ‖c - w n‖ ^ (2 : ℕ) ≤
      (Obj c).toReal - (Obj (y (n + 1))).toReal := by
  let Obj := composite_model_objective F G
  let θ : ℝ := (fista_momentum_sequence n)⁻¹
  let c : V := θ • yStar + (1 - θ) • y n
  letI : IsProperExtendedRealFunction G := hminproblem.g_proper
  letI : Fact (LowerSemicontinuous G) := ⟨hminproblem.g_closed⟩
  letI : Fact (is_convex_function G) := ⟨hminproblem.g_convex⟩
  have hyStarEff : yStar ∈ effective_domain G :=
    shiftedDualOptimalPoint_memEffectiveDomainG
      (f := f)
      (g := g)
      (A := A)
      (L := L)
      hminproblem
      hyStarMin
  have hθ_mem : θ ∈ Set.Icc (0 : ℝ) 1 := by
    -- The comparison point uses the standard reciprocal momentum weight.
    simpa [θ] using shiftedDualOneDivMomentum_mem_Icc (k := n)
  have hcEff : c ∈ effective_domain G := by
    -- Convexity of `G` keeps the comparison point finite-valued.
    exact
      combo_mem_effective_domain_of_is_convex_function
        hminproblem.g_convex
        hyStarEff
        hyEffn
        hθ_mem
  have haccept :
      proximal_gradient_backtracking_B2_accepts
        (fun z : V ↦ (((F z).toReal : ℝ) : EReal))
        G
        (L : PosReal)
        (interior_effective_domain_point_of_real
          (fun z : V ↦ (F z).toReal)
          (w n)) :=
    shiftedDualAcceptedAtBasePoint
      (f := f)
      (g := g)
      (A := A)
      (σ := σ)
      (L := L)
      h_problem
      hminproblem
      (w n)
  -- Specialize the finite-value prox-gap estimate at the shifted comparison point `c_n`.
  simpa [Obj, θ, c,
    shiftedDualExactProxPoint (f := f) (g := g) (A := A) htraj n] using
    (shiftedDualProxGapRealOfFiniteValues
      (f := f)
      (g := g)
      (A := A)
      (σ := σ)
      (L := L)
      h_problem
      hminproblem
      (xPoint := c)
      (yPoint := w n)
      hcEff
      haccept)

/-- Helper for Theorem 12.9: scaling the accepted comparison-point gap by `t_n^2` yields the raw
real-valued Lyapunov balance on the truthful Chapter 12 owner. -/
lemma shiftedDualRawBalanceReal
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {y0 : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ G gradF L y0 y w)
    {yStar : V}
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (hyStarMin :
      yStar ∈ unconstrained_problem_solutions (composite_model_objective F G))
    {n : ℕ}
    (hn : 1 ≤ n)
    (hyEffn : y n ∈ effective_domain G) :
    let Obj := composite_model_objective F G
    let FOptR : ℝ := -EReal.toReal qOpt
    let vR : ℕ → ℝ := fun m ↦ (Obj (y m)).toReal - FOptR
    let pre : V :=
      (fista_momentum_sequence n : ℝ) • w n -
        (yStar + (fista_momentum_sequence n - 1) • y n)
    ‖shiftedDualResidualToOptimum y yStar (n + 1)‖ ^ (2 : ℕ) +
        (2 / (L : ℝ)) * fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) ≤
      ‖pre‖ ^ (2 : ℕ) +
        (2 / (L : ℝ)) *
          (fista_momentum_sequence n ^ (2 : ℕ) - fista_momentum_sequence n) * vR n := by
  let Obj := composite_model_objective F G
  let FOptR : ℝ := -EReal.toReal qOpt
  let vR : ℕ → ℝ := fun m ↦ (Obj (y m)).toReal - FOptR
  let θ : ℝ := (fista_momentum_sequence n)⁻¹
  let c : V := θ • yStar + (1 - θ) • y n
  let pre : V :=
    (fista_momentum_sequence n : ℝ) • w n -
      (yStar + (fista_momentum_sequence n - 1) • y n)
  let t : ℝ := fista_momentum_sequence n
  have hgap :
      ((L : ℝ) / 2) * ‖c - y (n + 1)‖ ^ (2 : ℕ) -
          ((L : ℝ) / 2) * ‖c - w n‖ ^ (2 : ℕ) ≤
        (1 - θ) * vR n - vR (n + 1) := by
    exact
      le_trans
        (shiftedDualGapToComparisonAtWReal
          (f := f)
          (g := g)
          (A := A)
          (σ := σ)
          (L := L)
          h_problem
          htraj
          hminproblem
          hyStarMin
          (n := n)
          hn
          hyEffn)
        (shiftedDualComparisonGapUpperBoundReal
          (f := f)
          (g := g)
          (A := A)
          (σ := σ)
          (L := L)
          h_problem
          (y := y)
          (yStar := yStar)
          hminproblem
          hyStarMin
          (n := n)
          hyEffn)
  have hL_pos : 0 < (L : ℝ) := (L : PosReal).2
  have ht_pos : 0 < t := by
    simpa [t] using lt_of_lt_of_le zero_lt_one (shiftedDualOneLeMomentum n)
  have hscaled :
      (2 / (L : ℝ)) * t ^ (2 : ℕ) *
          (((L : ℝ) / 2) * ‖c - y (n + 1)‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖c - w n‖ ^ (2 : ℕ)) ≤
        (2 / (L : ℝ)) * t ^ (2 : ℕ) * ((1 - θ) * vR n - vR (n + 1)) := by
    exact mul_le_mul_of_nonneg_left hgap (by positivity)
  have hresidual_vec :
      t • (y (n + 1) - c) =
        shiftedDualResidualToOptimum y yStar (n + 1) := by
    -- Clear the reciprocal comparison-point coefficient at the next iterate.
    simpa [t, c, shiftedDualResidualToOptimum] using
      (shiftedDualScaledSubComparisonPoint
        (y := y)
        (yStar := yStar)
        (point := y (n + 1))
        (k := n))
  have hpre_vec :
      t • (w n - c) = pre := by
    -- The same affine rewrite identifies the pre-step vector at the base point `w n`.
    simpa [t, c, pre] using
      (shiftedDualScaledSubComparisonPoint
        (y := y)
        (yStar := yStar)
        (point := w n)
        (k := n))
  have hresidual_norm :
      ‖shiftedDualResidualToOptimum y yStar (n + 1)‖ ^ (2 : ℕ) =
        t ^ (2 : ℕ) * ‖c - y (n + 1)‖ ^ (2 : ℕ) := by
    -- Squaring the cleared vector identity rewrites the comparison norm to the residual norm.
    rw [← hresidual_vec, norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos), norm_sub_rev]
    ring
  have hpre_norm :
      ‖pre‖ ^ (2 : ℕ) = t ^ (2 : ℕ) * ‖c - w n‖ ^ (2 : ℕ) := by
    -- The pre-step norm is the same scaled comparison norm at the base point `w n`.
    rw [← hpre_vec, norm_smul, Real.norm_of_nonneg (le_of_lt ht_pos), norm_sub_rev]
    ring
  have hθ_coeff :
      t ^ (2 : ℕ) * (1 - θ) = t ^ (2 : ℕ) - t := by
    -- The reciprocal momentum weight is exactly `1 / t_n`.
    have hθ :
        t * θ = 1 := by
      dsimp [t, θ]
      exact mul_inv_cancel₀ ht_pos.ne'
    nlinarith
  have hscaled' :
      ‖shiftedDualResidualToOptimum y yStar (n + 1)‖ ^ (2 : ℕ) - ‖pre‖ ^ (2 : ℕ) ≤
        (2 / (L : ℝ)) * (t ^ (2 : ℕ) - t) * vR n -
          (2 / (L : ℝ)) * t ^ (2 : ℕ) * vR (n + 1) := by
    have hleft :
        (2 / (L : ℝ)) * t ^ (2 : ℕ) *
            (((L : ℝ) / 2) * ‖c - y (n + 1)‖ ^ (2 : ℕ) -
              ((L : ℝ) / 2) * ‖c - w n‖ ^ (2 : ℕ)) =
          ‖shiftedDualResidualToOptimum y yStar (n + 1)‖ ^ (2 : ℕ) - ‖pre‖ ^ (2 : ℕ) := by
      calc
        (2 / (L : ℝ)) * t ^ (2 : ℕ) *
            (((L : ℝ) / 2) * ‖c - y (n + 1)‖ ^ (2 : ℕ) -
              ((L : ℝ) / 2) * ‖c - w n‖ ^ (2 : ℕ)) =
          t ^ (2 : ℕ) * ‖c - y (n + 1)‖ ^ (2 : ℕ) -
            t ^ (2 : ℕ) * ‖c - w n‖ ^ (2 : ℕ) := by
            field_simp [hL_pos.ne']
        _ = ‖shiftedDualResidualToOptimum y yStar (n + 1)‖ ^ (2 : ℕ) - ‖pre‖ ^ (2 : ℕ) := by
            rw [← hresidual_norm, ← hpre_norm]
    have hright :
        (2 / (L : ℝ)) * t ^ (2 : ℕ) * ((1 - θ) * vR n - vR (n + 1)) =
          (2 / (L : ℝ)) * (t ^ (2 : ℕ) - t) * vR n -
            (2 / (L : ℝ)) * t ^ (2 : ℕ) * vR (n + 1) := by
      calc
        (2 / (L : ℝ)) * t ^ (2 : ℕ) * ((1 - θ) * vR n - vR (n + 1)) =
          (2 / (L : ℝ)) * (t ^ (2 : ℕ) * (1 - θ) * vR n - t ^ (2 : ℕ) * vR (n + 1)) := by
            ring
        _ = (2 / (L : ℝ)) * ((t ^ (2 : ℕ) - t) * vR n - t ^ (2 : ℕ) * vR (n + 1)) := by
            rw [hθ_coeff]
        _ = (2 / (L : ℝ)) * (t ^ (2 : ℕ) - t) * vR n -
              (2 / (L : ℝ)) * t ^ (2 : ℕ) * vR (n + 1) := by
            ring
    rw [hleft, hright] at hscaled
    exact hscaled
  -- Move the scaled next-step gap to the left and the predecessor packet to the right.
  nlinarith [hscaled']

/-- Helper for Theorem 12.9: the first positive Lyapunov energy is controlled directly by the
initial distance to the optimizer. -/
lemma shiftedDualInitialEnergyBound
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {y0 : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ G gradF L y0 y w)
    {yStar : V}
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (hyStarMin :
      yStar ∈ unconstrained_problem_solutions (composite_model_objective F G)) :
    let Obj := composite_model_objective F G
    let FOptR : ℝ := -EReal.toReal qOpt
    let vR : ℕ → ℝ := fun m ↦ (Obj (y m)).toReal - FOptR
    ‖shiftedDualResidualToOptimum y yStar 1‖ ^ (2 : ℕ) +
        (2 / (L : ℝ)) * vR 1 ≤
      ‖y0 - yStar‖ ^ (2 : ℕ) := by
  let Obj := composite_model_objective F G
  let FOptR : ℝ := -EReal.toReal qOpt
  let vR : ℕ → ℝ := fun m ↦ (Obj (y m)).toReal - FOptR
  letI : IsProperExtendedRealFunction G := hminproblem.g_proper
  letI : Fact (LowerSemicontinuous G) := ⟨hminproblem.g_closed⟩
  letI : Fact (is_convex_function G) := ⟨hminproblem.g_convex⟩
  have hyStarEff : yStar ∈ effective_domain G :=
    shiftedDualOptimalPoint_memEffectiveDomainG
      (f := f)
      (g := g)
      (A := A)
      (L := L)
      hminproblem
      hyStarMin
  have haccept :
      proximal_gradient_backtracking_B2_accepts
        (fun z : V ↦ (((F z).toReal : ℝ) : EReal))
        G
        (L : PosReal)
        (interior_effective_domain_point_of_real
          (fun z : V ↦ (F z).toReal)
          y0) :=
    shiftedDualAcceptedAtBasePoint
      (f := f)
      (g := g)
      (A := A)
      (σ := σ)
      (L := L)
      h_problem
      hminproblem
      y0
  have hy1_eq :
      y 1 =
        T[(L : PosReal); (fun z : V ↦ (F z).toReal), G] y0 := by
    simpa [htraj.w_zero] using shiftedDualExactProxPoint (f := f) (g := g) (A := A) htraj 0
  have hObj_star :
      Obj yStar = (FOptR : EReal) :=
    hminproblem.objective_eq_optimalValue_of_mem_optimalSet hyStarMin
  have hObj_star_toReal :
      (Obj yStar).toReal = FOptR := by
    rw [hObj_star]
    simp [FOptR]
  have hgap0' :
      ((L : ℝ) / 2) * ‖yStar - y 1‖ ^ (2 : ℕ) -
          ((L : ℝ) / 2) * ‖yStar - y0‖ ^ (2 : ℕ) ≤
        FOptR - (Obj (y 1)).toReal := by
    -- Specialize the finite-value prox-gap estimate at the optimizer and rewrite the optimal value.
    have hprox_gap :=
      shiftedDualProxGapRealOfFiniteValues
        (f := f)
        (g := g)
        (A := A)
        (σ := σ)
        (L := L)
        h_problem
        hminproblem
        (xPoint := yStar)
        (yPoint := y0)
        hyStarEff
        haccept
    change
      ((L : ℝ) / 2) * ‖yStar -
            T[(L : PosReal); (fun z : V ↦ (F z).toReal), G] y0‖ ^ (2 : ℕ) -
          ((L : ℝ) / 2) * ‖yStar - y0‖ ^ (2 : ℕ) ≤
        (Obj yStar).toReal -
          (Obj (T[(L : PosReal); (fun z : V ↦ (F z).toReal), G] y0)).toReal at hprox_gap
    rw [hObj_star_toReal, ← hy1_eq] at hprox_gap
    exact hprox_gap
  have hgap0 :
      ((L : ℝ) / 2) * ‖yStar - y 1‖ ^ (2 : ℕ) ≤
        -vR 1 + ((L : ℝ) / 2) * ‖yStar - y0‖ ^ (2 : ℕ) := by
    nlinarith [hgap0']
  have hgap :
      ((L : ℝ) / 2) * ‖yStar - y 1‖ ^ (2 : ℕ) -
          ((L : ℝ) / 2) * ‖yStar - y0‖ ^ (2 : ℕ) ≤
        -vR 1 := by
    nlinarith [hgap0]
  have hL_pos : 0 < (L : ℝ) := (L : PosReal).2
  have hresidual_one :
      shiftedDualResidualToOptimum y yStar 1 = y 1 - yStar := by
    -- The first momentum value is `t₀ = 1`, so the first residual is just `y¹ - y*`.
    simp [shiftedDualResidualToOptimum]
  have hseed :
      ((L : ℝ) / 2) * ‖shiftedDualResidualToOptimum y yStar 1‖ ^ (2 : ℕ) + vR 1 ≤
        ((L : ℝ) / 2) * ‖y0 - yStar‖ ^ (2 : ℕ) := by
    have hgap_norm :
        ((L : ℝ) / 2) * ‖shiftedDualResidualToOptimum y yStar 1‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖y0 - yStar‖ ^ (2 : ℕ) ≤
          -vR 1 := by
      simpa [hresidual_one, norm_sub_rev] using hgap
    nlinarith [hgap_norm]
  have hseed' :
      (L : ℝ) * ‖shiftedDualResidualToOptimum y yStar 1‖ ^ (2 : ℕ) + 2 * vR 1 ≤
        (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) := by
    nlinarith [hseed]
  have hseed_scaled :
      ‖shiftedDualResidualToOptimum y yStar 1‖ ^ (2 : ℕ) +
          (2 / (L : ℝ)) * vR 1 ≤
        ‖y0 - yStar‖ ^ (2 : ℕ) := by
    have hmul :
        (L : ℝ) *
            (‖shiftedDualResidualToOptimum y yStar 1‖ ^ (2 : ℕ) +
              (2 / (L : ℝ)) * vR 1) ≤
          (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) := by
      have hleft :
          (L : ℝ) *
              (‖shiftedDualResidualToOptimum y yStar 1‖ ^ (2 : ℕ) +
                (2 / (L : ℝ)) * vR 1) =
            (L : ℝ) * ‖shiftedDualResidualToOptimum y yStar 1‖ ^ (2 : ℕ) + 2 * vR 1 := by
        field_simp [hL_pos.ne']
      rw [hleft]
      exact hseed'
    nlinarith [hmul, hL_pos]
  exact hseed_scaled

/-- Helper for Theorem 12.9: after rewriting the honest pre-step vector as the previous residual,
the Chapter 12 Lyapunov energy decreases at every positive index. -/
lemma shiftedDualLyapunovEnergyStep
    {σ : PosReal}
    {L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ}
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    {y0 : V} {y w : ℕ → V}
    (htraj : IsFastDualProximalGradientDualTrajectory
      A.toContinuousLinearMap σ G gradF L y0 y w)
    {yStar : V}
    (hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)))
    (hyStarMin :
      yStar ∈ unconstrained_problem_solutions (composite_model_objective F G))
    {n : ℕ}
    (hn : 1 ≤ n)
    (hyEffn : y n ∈ effective_domain G) :
    let Obj := composite_model_objective F G
    let FOptR : ℝ := -EReal.toReal qOpt
    let vR : ℕ → ℝ := fun m ↦ (Obj (y m)).toReal - FOptR
    ‖shiftedDualResidualToOptimum y yStar (n + 1)‖ ^ (2 : ℕ) +
        (2 / (L : ℝ)) * fista_momentum_sequence n ^ (2 : ℕ) * vR (n + 1) ≤
      ‖shiftedDualResidualToOptimum y yStar n‖ ^ (2 : ℕ) +
        (2 / (L : ℝ)) * fista_momentum_sequence (n - 1) ^ (2 : ℕ) * vR n := by
  let Obj := composite_model_objective F G
  let FOptR : ℝ := -EReal.toReal qOpt
  let vR : ℕ → ℝ := fun m ↦ (Obj (y m)).toReal - FOptR
  have hquad :
      fista_momentum_sequence n ^ (2 : ℕ) - fista_momentum_sequence n =
        fista_momentum_sequence (n - 1) ^ (2 : ℕ) := by
    rcases Nat.exists_eq_add_of_le hn with ⟨m, rfl⟩
    simpa [Nat.add_comm] using fistaMomentumQuadraticIdentity (k := m)
  -- Rewrite the pre-step packet to the previous residual and collapse the momentum coefficient.
  simpa [Obj, FOptR, vR, hquad,
    shiftedDualPrestepVector_eq_previousResidual
      (f := f) (g := g) (A := A) (L := L) htraj n hn] using
    (shiftedDualRawBalanceReal
      (f := f)
      (g := g)
      (A := A)
      (σ := σ)
      (L := L)
      h_problem
      htraj
      hminproblem
      hyStarMin
      (n := n)
      hn
      hyEffn)

/-- Helper for Theorem 12.9: the only remaining structural blocker is the direct accelerated
Lyapunov rate on the truthful Chapter 12 split-objective owner. -/
lemma shiftedDualSplitObjectiveGap_le
    (σ : PosReal)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y0 : V) (y w : ℕ → V)
    (htraj : IsFastDualProximalGradientDualTrajectory A.toContinuousLinearMap σ G gradF L y0 y w)
    (yStar : V)
    (hyStar : q yStar = qOpt)
    (k : ℕ) (hk : 1 ≤ k) :
    composite_model_objective
        F
        G
        (y k) - (((-EReal.toReal qOpt : ℝ)) : EReal) ≤
      ((2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) /
          ((k + 1 : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) := by
  let hminproblem :
      IsConvexCompositeSmoothMinimizationProblem
        F
        G
        (unconstrained_problem_solutions (composite_model_objective F G))
        (-EReal.toReal qOpt)
        (PosReal.toNNReal (L : PosReal)) :=
    dualMinimizationView_isConvexCompositeSmoothMinimizationProblem
      (f := f)
      (g := g)
      (A := A)
      σ
      h_problem.toIsProperExtendedRealFunction
      h_problem.f_closed
      h_problem.f_strongly_convex
      h_problem.g_proper
      h_problem.g_convex
      L
      hyStar
  have hyStarMin :
      yStar ∈ unconstrained_problem_solutions (composite_model_objective F G) :=
    optimalDualPoint_mem_unconstrainedSolutionsMinimizationView
      (f := f)
      (g := g)
      (A := A)
      σ
      h_problem.toIsProperExtendedRealFunction
      h_problem.f_closed
      h_problem.f_strongly_convex
      h_problem.g_proper
      h_problem.g_convex
      hyStar
  let Obj := composite_model_objective F G
  let FOptR : ℝ := -EReal.toReal qOpt
  let vR : ℕ → ℝ := fun m ↦ (Obj (y m)).toReal - FOptR
  let energy : ℕ → ℝ := fun m ↦
    ‖shiftedDualResidualToOptimum y yStar m‖ ^ (2 : ℕ) +
      (2 / (L : ℝ)) * fista_momentum_sequence (m - 1) ^ (2 : ℕ) * vR m
  letI : IsProperExtendedRealFunction G := hminproblem.g_proper
  letI : Fact (LowerSemicontinuous G) := ⟨hminproblem.g_closed⟩
  letI : Fact (is_convex_function G) := ⟨hminproblem.g_convex⟩
  have hyEffPos : ∀ m : ℕ, 1 ≤ m → y m ∈ effective_domain G := by
    intro m hm
    rcases Nat.exists_eq_add_of_le hm with ⟨j, rfl⟩
    simpa [Nat.add_comm] using
      shiftedDualPositiveIterate_memEffectiveDomainG
        (f := f)
        (g := g)
        (A := A)
        (L := L)
        htraj
        j
  have hbase :
      energy 1 ≤ ‖y0 - yStar‖ ^ (2 : ℕ) := by
    -- The first positive energy is controlled directly by the initial distance.
    simpa [energy, Obj, FOptR, vR] using
      (shiftedDualInitialEnergyBound
        (f := f)
        (g := g)
        (A := A)
        (σ := σ)
        (L := L)
        h_problem
        htraj
        hminproblem
        hyStarMin)
  have hstep :
      ∀ m : ℕ, 1 ≤ m → energy (m + 1) ≤ energy m := by
    intro m hm
    -- Each positive Lyapunov packet decreases by the one-step energy inequality.
    simpa [energy, Obj, FOptR, vR] using
      (shiftedDualLyapunovEnergyStep
        (f := f)
        (g := g)
        (A := A)
        (σ := σ)
        (L := L)
        h_problem
        htraj
        hminproblem
        hyStarMin
        (n := m)
        hm
        (hyEffPos m hm))
  have henergySucc : ∀ j : ℕ, energy (j + 1) ≤ ‖y0 - yStar‖ ^ (2 : ℕ) := by
    intro j
    induction j with
    | zero =>
        simpa using hbase
    | succ j ih =>
        have hstep' : energy (j + 2) ≤ energy (j + 1) := by
          have hj_pos : 1 ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
          simpa [Nat.add_assoc] using hstep (j + 1) hj_pos
        exact le_trans hstep' ih
  rcases Nat.exists_eq_add_of_le hk with ⟨j, rfl⟩
  have hyEffk : y (j + 1) ∈ effective_domain G := by
    exact hyEffPos (j + 1) (Nat.succ_le_succ (Nat.zero_le j))
  have henergy :
      energy (j + 1) ≤ ‖y0 - yStar‖ ^ (2 : ℕ) := henergySucc j
  have hnorm_nonneg :
      0 ≤ ‖shiftedDualResidualToOptimum y yStar (j + 1)‖ ^ (2 : ℕ) := by
    positivity
  have hL_pos : 0 < (L : ℝ) := (L : PosReal).2
  have hvR_nonneg : 0 ≤ vR (j + 1) := by
    exact sub_nonneg.mpr (toReal_ge_FOpt_of_memEffectiveDomainG (hproblem := hminproblem) hyEffk)
  have htk_lower :
      ((j : ℝ) + 2) / 2 ≤ fista_momentum_sequence j := by
    exact
      fista_momentum_sequence_lower_bound
        fista_momentum_sequence_zero
        fista_momentum_sequence_succ
        j
  have hscaled_gap :
      (2 / (L : ℝ)) * fista_momentum_sequence j ^ (2 : ℕ) * vR (j + 1) ≤
        ‖y0 - yStar‖ ^ (2 : ℕ) := by
    -- Discard the nonnegative residual term from the Lyapunov energy packet.
    exact le_trans (le_add_of_nonneg_left hnorm_nonneg) henergy
  have hmid_nonneg : 0 ≤ ((j : ℝ) + 2) / 2 := by
    positivity
  have htk_nonneg : 0 ≤ fista_momentum_sequence j := by
    exact le_trans hmid_nonneg htk_lower
  have hsq_lower :
      (((j : ℝ) + 2) / 2) ^ (2 : ℕ) ≤ fista_momentum_sequence j ^ (2 : ℕ) := by
    nlinarith [htk_lower, htk_nonneg]
  have hscaled_lower :
      (2 / (L : ℝ)) * (((j : ℝ) + 2) / 2) ^ (2 : ℕ) * vR (j + 1) ≤
        (2 / (L : ℝ)) * fista_momentum_sequence j ^ (2 : ℕ) * vR (j + 1) := by
    have hcoeff_nonneg : 0 ≤ (2 / (L : ℝ)) := by
      positivity
    have hmul :
        (((j : ℝ) + 2) / 2) ^ (2 : ℕ) * vR (j + 1) ≤
          fista_momentum_sequence j ^ (2 : ℕ) * vR (j + 1) := by
      exact mul_le_mul_of_nonneg_right hsq_lower hvR_nonneg
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hmul hcoeff_nonneg)
  have hscaled_mid :
      (2 / (L : ℝ)) * (((j : ℝ) + 2) / 2) ^ (2 : ℕ) * vR (j + 1) ≤
        ‖y0 - yStar‖ ^ (2 : ℕ) := by
    exact le_trans hscaled_lower hscaled_gap
  have hgap_real :
      vR (j + 1) ≤
        2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / (((j : ℝ) + 2) ^ (2 : ℕ)) := by
    -- Compare the momentum factor with `((j + 2) / 2)^2` before clearing the scalar coefficient.
    have hcoef_pos :
        0 < (2 / (L : ℝ)) * (((j : ℝ) + 2) / 2) ^ (2 : ℕ) := by
      positivity
    have hgap_div :
        vR (j + 1) ≤
          ‖y0 - yStar‖ ^ (2 : ℕ) /
            ((2 / (L : ℝ)) * (((j : ℝ) + 2) / 2) ^ (2 : ℕ)) := by
      exact (le_div_iff₀ hcoef_pos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled_mid
    have hj_sq_ne : (((j : ℝ) + 2) ^ (2 : ℕ)) ≠ 0 := by
      positivity
    have hcoef_simplify :
        ‖y0 - yStar‖ ^ (2 : ℕ) /
            ((2 / (L : ℝ)) * (((j : ℝ) + 2) / 2) ^ (2 : ℕ)) =
          2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) / (((j : ℝ) + 2) ^ (2 : ℕ)) := by
      field_simp [hL_pos.ne', hj_sq_ne]
    simpa [hcoef_simplify] using hgap_div
  have hgap_ereal :
      composite_model_objective F G (y (j + 1)) - (((-EReal.toReal qOpt : ℝ)) : EReal) ≤
        ((2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) /
            (((j : ℝ) + 2) ^ (2 : ℕ)) : ℝ) : EReal) := by
    -- Rewrite the split-objective gap to its real representative and insert the `O(1/k^2)` bound.
    rw [← objectiveMinusFOpt_eq_coe_sub_toReal_of_memEffectiveDomainG (hproblem := hminproblem) hyEffk]
    exact_mod_cast hgap_real
  simpa [Nat.cast_add, Nat.cast_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
    add_comm, add_left_comm, add_assoc, one_add_one_eq_two] using hgap_ereal

theorem fast_dual_proximal_gradient_dual_objective_gap_le_of_dual_trajectory
    (σ : PosReal)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y0 : V) (y w : ℕ → V)
    (htraj : IsFastDualProximalGradientDualTrajectory A.toContinuousLinearMap σ G gradF L y0 y w)
    (yStar : V)
    (hyStar : q yStar = qOpt)
    (k : ℕ) (hk : 1 ≤ k) :
    qOpt - q (y k) ≤
      ((2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) /
          ((k + 1 : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) := by
  have hgap :
      composite_model_objective
          F
          G
          (y k) -
        (((-EReal.toReal qOpt : ℝ)) : EReal) ≤
      ((2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) /
          ((k + 1 : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) :=
    shiftedDualSplitObjectiveGap_le
      (f := f)
      (g := g)
      (A := A)
      σ
      L
      h_problem
      y0
      y
      w
      htraj
      yStar
      hyStar
      k
      hk
  -- Rewrite the direct split-objective gap back to the displayed dual objective gap.
  rw [dualObjectiveGap_eq_splitObjectiveGap
    (f := f) (g := g) (A := A) σ h_problem yStar hyStar (y k)]
  exact hgap

/-- Theorem 12.9: under Assumption 12.1, if `(u k, y k, w k, t k)` is generated by the fast dual
proximal-gradient method with constant parameter `L`, then every iterate with `1 ≤ k` satisfies
`qOpt - q (y k) ≤ 2 L ‖y0 - yStar‖^2 / (k + 1)^2` for every optimal dual point `yStar`. -/
theorem fast_dual_proximal_gradient_dual_objective_gap_le
    (σ : PosReal)
    (L : DualBasedProximalGradientDualStepsizeParameter A.toContinuousLinearMap σ)
    (h_problem : IsDualBasedProximalGradientProblem f g A σ)
    (y0 : V) (u : ℕ → E) (y w : ℕ → V) (t : ℕ → ℝ)
    (htraj : IsFastDualProximalGradientPrimalTrajectory f g A σ L y0 u y w t)
    (yStar : V)
    (hyStar : q yStar = qOpt)
    (k : ℕ) (hk : 1 ≤ k) :
    qOpt - q (y k) ≤
      ((2 * (L : ℝ) * ‖y0 - yStar‖ ^ (2 : ℕ) /
          ((k + 1 : ℝ) ^ (2 : ℕ)) : ℝ) : EReal) := by
  simpa using
    fast_dual_proximal_gradient_dual_objective_gap_le_of_dual_trajectory
      f
      g
      A
      σ
      L
      h_problem
      y0
      y
      w
      (IsFastDualProximalGradientPrimalTrajectory.toDualTrajectory
        f
        g
        A
        h_problem
        htraj)
      yStar
      hyStar
      k
      hk

end
