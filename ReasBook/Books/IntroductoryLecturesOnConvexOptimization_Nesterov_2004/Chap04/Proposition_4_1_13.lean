/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Proposition_1_9_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open Filter

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 4.1.13 lies in the cubic-regularized quadratic / scalar-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticObjective` in `Theorem_4_1_11`, the chapter owner of the primal cubic
  model;
* `cubicRegularizedQuadraticDualFunction` and `cubicRegularizedQuadraticDualDomain` in
  `Theorem_4_1_11`, the chapter owners of the scalar dual value and its effective domain;
* `cubicRegularizedQuadraticScalarDualFunction_eq_sInf_quadratic` in `Proposition_4_1_8`, the
  bridge that eliminates the slack variable and reduces the dual value to the shifted quadratic
  subproblem;
* `Matrix.leastEigenvalue` and the notation `λ_min(H)` in `Definition_4_1_6`, the chapter owner
  for the least-eigenvalue quantity of a real matrix;
* `quadraticObjective` in `Chap01/Definition_1_9_1`, the owner of the shifted quadratic
  `h ↦ ⟪g, h⟫ + (1 / 2) ⟪(H + λ I) h, h⟫`.

Best owner abstraction:
* source-facing: the first-order optimality identity and primal-minimizer statement attached to a
  dual maximizer `λ*`;
* core/canonical: `cubicRegularizedQuadraticObjective`, `cubicRegularizedQuadraticDualFunction`,
  `cubicRegularizedQuadraticDualDomain`, the shifted quadratic `quadraticObjective 0 g
  (H + λ • I)`, and the spectral interior condition `-λ_min(H) < λ`;
* bridge/view: the explicit resolvent point `-((H + λ I)⁻¹).mulVec g`.

Primitive data:
* `g`, `H`, `M`, the symmetry hypothesis `H.IsSymm`, and the shifted matrix `H + λ I`;
* dual optimality on `cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)`.

Derived API:
* the explicit resolvent point above;
* the norm identity `‖h*‖ = (2 / M) λ*`;
* the global primal minimizer statement for that same `h*`.

Source/core/bridge triage:
* source-facing: the two textbook consequences for a dual maximizer `λ*`;
* core/canonical: the existing objective/dual owner family from `Theorem_4_1_11`;
* bridge/view: the resolvent formula expressing the source point as `-A⁻¹ g`.

This file therefore stays at the theorem layer and does not introduce a second local owner for the
dual problem or the shifted quadratic subproblem. -/

section

variable (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)

local notation "Dplus" => cubicRegularizedQuadraticDualDomain g H M ∩ Set.Ici (0 : ℝ)
local notation "A" lam => H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)
local notation "resolvent" lam => -Matrix.mulVec ((A lam)⁻¹) g
local notation "penalty" =>
  fun lam : ℝ ↦ (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)

include g H M

variable {lamStar : ℝ}
variable (hM : 0 < M) (hH : H.IsSymm)
variable (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar)
variable (hlam : -λ_min(H) < lamStar)

/-- Helper for Proposition 4.1.13: the interior spectral condition makes the shifted Hessian
positive definite. -/
lemma shifted_hessian_posDef_of_interior
    {lam : ℝ} (hH : H.IsSymm) (hlam : -λ_min(H) < lam) :
    (A lam).PosDef := by
  classical
  have hShiftHerm : (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
    -- Turn the real symmetric shifted Hessian into the Hermitian object required by the spectral
    -- positivity API.
    simpa [Matrix.IsHermitian, Matrix.IsSymm, add_comm] using
      hH.add ((Matrix.isSymm_one : (1 : Matrix (Fin n) (Fin n) ℝ).IsSymm).smul lam)
  refine hShiftHerm.posDef_iff_eigenvalues_pos.mpr ?_
  intro i
  have hμ :
      hShiftHerm.eigenvalues i ∈
        spectrum ℝ (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) :=
    hShiftHerm.eigenvalues_mem_spectrum_real i
  have hshift : hShiftHerm.eigenvalues i - lam ∈ spectrum ℝ H := by
    -- Translate the shifted-spectrum membership back to the original Hessian by subtracting the
    -- scalar shift.
    exact (spectrum.add_mem_add_iff
      (a := H) (r := hShiftHerm.eigenvalues i - lam) (s := lam)).mp <|
        by
          simpa [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, add_assoc, add_left_comm,
            add_comm] using hμ
  have hmin_le : λ_min(H) ≤ hShiftHerm.eigenvalues i - lam := by
    -- The least eigenvalue is the infimum of the real spectrum, so it is bounded above by every
    -- spectral value.
    exact csInf_le H.finite_real_spectrum.bddBelow hshift
  linarith

/-- Helper for Proposition 4.1.13: the resolvent is the global minimizer of the shifted
quadratic owner. -/
lemma resolvent_isMinOn_shiftedQuadratic
    {lam : ℝ} (hH : H.IsSymm) (hlam : -λ_min(H) < lam) :
    IsMinOn (quadraticObjective 0 g (A lam)) Set.univ (resolvent lam) := by
  let problem : UnconstrainedQuadraticMinimizationProblem n :=
    { α := 0
      a := g
      «A» := H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)
      posDef := shifted_hessian_posDef_of_interior H hH hlam }
  -- Package the shifted quadratic into the Chapter 1 owner and reuse its canonical minimizer
  -- theorem, then rewrite the owner minimizer to the displayed resolvent point.
  simpa [problem, UnconstrainedQuadraticMinimizationProblem.minimizer, Matrix.toLpLin_apply] using
    (UnconstrainedQuadraticMinimizationProblem.minimizer_isMinOn problem)

/-- Helper for Proposition 4.1.13: imposing the tight slack `τ = ‖h‖²` turns the scalar
Lagrangian back into the primal cubic objective. -/
lemma scalarLagrangian_at_norm_sq_eq_objective
    (h : E) (lam : ℝ) :
    cubicRegularizedQuadraticScalarLagrangian g H M h (‖h‖ ^ (2 : ℕ)) lam =
      cubicRegularizedQuadraticObjective g H M h := by
  have hpow : ((‖h‖ ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ)) = ‖h‖ ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg h) 2 (3 / 2 : ℝ)]
    norm_num
  -- At tight slack, the multiplier term vanishes and only the primal cubic objective remains.
  rw [cubicRegularizedQuadraticScalarLagrangian, cubicRegularizedQuadraticObjective_apply]
  have hlin :
      lam * ((1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ)) = 0 := by
    ring
  rw [hlin]
  simp [hpow]

/-- Helper for Proposition 4.1.13: at an interior multiplier, the resolvent point and the slack
minimizer solve the epigraph Lagrangian subproblem. -/
lemma resolventTauCertificate_mem_lagrangianMinimizers
    {lam : ℝ} (hM : 0 < M) (hH : H.IsSymm) (hlam : -λ_min(H) < lam) :
    (resolvent lam, cubicRegularizedQuadraticTauMinimizer M lam) ∈
      (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangianMinimizers
        (EuclideanSpace.single 0 lam) := by
  -- Split the packaged Lagrangian into the shifted quadratic term and the scalar `τ`-term.
  rw [LagrangianProblem.mem_lagrangianMinimizers_iff, isMinOn_univ_iff]
  intro y
  have hquad_le :
      quadraticObjective 0 g (A lam) (resolvent lam) ≤
        quadraticObjective 0 g (A lam) y.1 := by
    exact (isMinOn_univ_iff.mp
      (resolvent_isMinOn_shiftedQuadratic (g := g) (H := H) (M := M) hH hlam)) y.1
  have htau_le :
      (M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) -
          (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam ≤
        (M / 6 : ℝ) * |y.2| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * y.2 := by
    exact (isMinOn_univ_iff.mp (cubicRegularizedQuadraticTauMinimizer_isMinOn M hM lam)) y.2
  have hsum :
      quadraticObjective 0 g (A lam) (resolvent lam) +
          ((M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) -
            (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam) ≤
        quadraticObjective 0 g (A lam) y.1 +
          ((M / 6 : ℝ) * |y.2| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * y.2) :=
    add_le_add hquad_le htau_le
  -- Reassemble the two one-variable minima into the packaged Lagrangian inequality.
  simpa [cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq,
    cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term] using hsum

/-- Helper for Proposition 4.1.13: the scalar dual value at an interior multiplier is the shifted
quadratic value at the resolvent minus the explicit cubic penalty. -/
lemma dualFunction_eq_resolventValue_of_interior
    {lam : ℝ} (hM : 0 < M) (hH : H.IsSymm) (hlam : -λ_min(H) < lam) :
    cubicRegularizedQuadraticDualFunction g H M lam =
      ((quadraticObjective 0 g (A lam) (resolvent lam) - penalty lam : ℝ) : EReal) := by
  let τ := cubicRegularizedQuadraticTauMinimizer M lam
  have hx :
      (resolvent lam, τ) ∈
        (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangianMinimizers
          (EuclideanSpace.single 0 lam) := by
    simpa [τ] using
      resolventTauCertificate_mem_lagrangianMinimizers
        (hM := hM) (hH := hH) (hlam := hlam)
  -- Evaluate the epigraph dual owner at the explicit interior Lagrangian minimizer.
  calc
    cubicRegularizedQuadraticDualFunction g H M lam =
        (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
          (EuclideanSpace.single 0 lam) := by
            rw [cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction]
    _ = ((cubicRegularizedQuadraticEpigraphProblem g H M).lagrangian
          (resolvent lam, τ) (EuclideanSpace.single 0 lam) : EReal) := by
            simpa using
              (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction_eq_lagrangian hx
    _ = (cubicRegularizedQuadraticScalarLagrangian g H M (resolvent lam) τ lam : EReal) := by
          exact congrArg (fun t : ℝ ↦ (t : EReal))
            (cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq g H M
              (resolvent lam) τ lam)
    _ = ((quadraticObjective 0 g (A lam) (resolvent lam) +
            ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) : ℝ) : EReal) := by
          exact congrArg (fun t : ℝ ↦ (t : EReal))
            (cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term
              g H M (resolvent lam) τ lam)
    _ = ((quadraticObjective 0 g (A lam) (resolvent lam) - penalty lam : ℝ) : EReal) := by
          refine congrArg (fun t : ℝ ↦ (t : EReal)) ?_
          rw [cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM]
          ring

/-- Helper for Proposition 4.1.13: changing the scalar shift from `lam` to `μ` adds exactly
`((μ - lam) / 2) ‖h‖²` to the quadratic objective at a fixed point `h`. -/
lemma quadraticObjective_shift_parameter_eq
    (h : E) (lam μ : ℝ) :
    quadraticObjective 0 g (A μ) h =
      quadraticObjective 0 g (A lam) h + ((μ - lam) / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) := by
  -- Expand both shifted quadratics and isolate the identity-matrix contribution.
  rw [quadraticObjective_zero_eq_dotProduct, quadraticObjective_zero_eq_dotProduct]
  have hnorm : dotProduct h h = ‖h‖ ^ (2 : ℕ) := by
    have hdot := (EuclideanSpace.inner_eq_star_dotProduct h h).symm
    simp at hdot
    exact hdot.trans (real_inner_self_eq_norm_sq h)
  simp [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hnorm, add_assoc,
    add_left_comm, add_comm, sub_eq_add_neg, mul_add]
  ring

/-- Helper for Proposition 4.1.13: the resolvent depends continuously on the scalar multiplier at
every interior point where the shifted Hessian is invertible. -/
lemma resolvent_continuousAt
    (hH : H.IsSymm) (hlam : -λ_min(H) < lamStar) :
    ContinuousAt (fun lam : ℝ ↦ resolvent lam) lamStar := by
  let shift : ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun lam : ℝ ↦ H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)
  have hdet_ne : (A lamStar).det ≠ 0 := by
    -- The interior spectral hypothesis puts the shifted Hessian in the positive-definite region,
    -- so its determinant is strictly positive.
    exact (shifted_hessian_posDef_of_interior (H := H) hH hlam).det_pos.ne'
  have hshift :
      ContinuousAt shift lamStar := by
    -- The shifted Hessian path is affine in the scalar parameter.
    exact (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
  have hRingInv :
      ContinuousAt Ring.inverse (shift lamStar).det := by
    -- Over `ℝ`, continuity of `Ring.inverse` at a nonzero point is the usual inverse continuity.
    simpa [Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ hdet_ne : ContinuousAt (fun x : ℝ ↦ x⁻¹) (shift lamStar).det)
  have hInv :
      ContinuousAt (fun lam : ℝ ↦ (shift lam)⁻¹) lamStar := by
    -- Compose matrix inversion continuity at the base matrix with the affine shifted-Hessian path.
    have hInvAt : ContinuousAt Inv.inv (shift lamStar) := by
      simpa [shift] using continuousAt_matrix_inv (shift lamStar) hRingInv
    have hInvBase :
        ContinuousAt (Inv.inv ∘ shift) lamStar := by
      exact hInvAt.comp_of_eq hshift rfl
    simpa [Function.comp] using hInvBase
  let gFun : Fin n → ℝ := fun i : Fin n ↦ g i
  have hmulVec :
      Continuous
        (fun p : Matrix (Fin n) (Fin n) ℝ × (Fin n → ℝ) ↦ Matrix.mulVec p.1 p.2) := by
    -- `mulVec` is jointly continuous in the matrix and vector entries.
    simpa using
      (continuous_fst.matrix_mulVec continuous_snd)
  have hMul :
      ContinuousAt (fun lam : ℝ ↦ Matrix.mulVec ((shift lam)⁻¹) gFun) lamStar := by
    -- Freeze the vector `g` and compose the joint `mulVec` continuity with the inverse matrix
    -- path.
    exact hmulVec.continuousAt.comp (hInv.prodMk continuousAt_const)
  -- Route correction: use the matrix continuity API directly instead of coordinatewise transport.
  change
    ContinuousAt
      (fun lam : ℝ ↦ WithLp.toLp 2 (-Matrix.mulVec ((shift lam)⁻¹) gFun)) lamStar
  simpa [shift, gFun] using
    ((PiLp.continuous_toLp 2 (fun _ : Fin n ↦ ℝ)).continuousAt.comp hMul.neg)

/-- Helper for Proposition 4.1.13: dual maximality forces the resolvent norm square at any other
interior nonnegative multiplier `μ` to be controlled by the explicit cubic penalty increment. -/
lemma dualMaximizer_controls_resolventNormSq
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    {μ : ℝ} (hμ_nonneg : 0 ≤ μ) (hμ_int : -λ_min(H) < μ) :
    ((μ - lamStar) / 2 : ℝ) * ‖resolvent μ‖ ^ (2 : ℕ) ≤ penalty μ - penalty lamStar := by
  have hμ_mem : μ ∈ Dplus := by
    constructor
    · -- The interior resolvent formula shows that the dual value at `μ` is finite, hence `μ`
      -- lies in the dual domain.
      rw [mem_cubicRegularizedQuadraticDualDomain_iff]
      rw [dualFunction_eq_resolventValue_of_interior
        (M := M) (H := H) (lam := μ) hM hH hμ_int]
      exact EReal.bot_lt_coe _
    · exact hμ_nonneg
  have hmax' := hmax
  rw [isMaxOn_iff] at hmax'
  have hdual_le :
      cubicRegularizedQuadraticDualFunction g H M μ ≤
        cubicRegularizedQuadraticDualFunction g H M lamStar :=
    hmax' μ hμ_mem
  have hvalue_le :
      quadraticObjective 0 g (A μ) (resolvent μ) - penalty μ ≤
        quadraticObjective 0 g (A lamStar) (resolvent lamStar) - penalty lamStar := by
    -- Rewrite both dual values through the explicit interior resolvent formula and compare in `ℝ`.
    rw [dualFunction_eq_resolventValue_of_interior
      (M := M) (H := H) (lam := μ) hM hH hμ_int,
      dualFunction_eq_resolventValue_of_interior
      (M := M) (H := H) (lam := lamStar) hM hH hlam] at hdual_le
    exact EReal.coe_le_coe_iff.mp hdual_le
  have hmin_lamStar :
      quadraticObjective 0 g (A lamStar) (resolvent lamStar) ≤
        quadraticObjective 0 g (A lamStar) (resolvent μ) := by
    -- At the maximizing multiplier `λ*`, the owner-level shifted quadratic is minimized by the
    -- corresponding resolvent point.
    exact (isMinOn_univ_iff.mp
      (resolvent_isMinOn_shiftedQuadratic (g := g) (H := H) (M := M) hH hlam))
      (resolvent μ)
  have hcompare :
      quadraticObjective 0 g (A μ) (resolvent μ) - penalty μ ≤
        quadraticObjective 0 g (A lamStar) (resolvent μ) - penalty lamStar := by
    exact le_trans hvalue_le (sub_le_sub_right hmin_lamStar _)
  have hshift :
      quadraticObjective 0 g (A μ) (resolvent μ) =
        quadraticObjective 0 g (A lamStar) (resolvent μ) +
          ((μ - lamStar) / 2 : ℝ) * ‖resolvent μ‖ ^ (2 : ℕ) :=
    quadraticObjective_shift_parameter_eq
      (g := g) (H := H) (M := M) (h := resolvent μ) lamStar μ
  -- After rewriting the shifted quadratic, only a scalar rearrangement remains.
  rw [hshift] at hcompare
  linarith

/-- Helper for Proposition 4.1.13: on the nonnegative half-line, the cubic penalty increment over
`lam + t` factors through the positive step `t`. -/
lemma cubicPenalty_add_eq_factor
    {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) :
    penalty (lam + t) - penalty lam =
      t * ((2 / (3 * M ^ (2 : ℕ)) : ℝ) *
        (3 * lam ^ (2 : ℕ) + 3 * lam * t + t ^ (2 : ℕ))) := by
  -- On `ℝ₊`, the absolute values disappear and the cubic difference factors algebraically.
  simp [abs_of_nonneg (add_nonneg hlam ht), abs_of_nonneg hlam]
  ring

/-- Helper for Proposition 4.1.13: on the nonnegative half-line, the cubic penalty decrement over
`lam - t` factors through the positive step `t`. -/
lemma cubicPenalty_sub_eq_factor
    {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 ≤ t) (htle : t ≤ lam) :
    penalty lam - penalty (lam - t) =
      t * ((2 / (3 * M ^ (2 : ℕ)) : ℝ) *
        (3 * lam ^ (2 : ℕ) - 3 * lam * t + t ^ (2 : ℕ))) := by
  -- On the interval `[0, lam]`, the absolute values again disappear and the cubic difference
  -- factors algebraically.
  simp [abs_of_nonneg hlam, abs_of_nonneg (sub_nonneg.mpr htle)]
  ring

-- Proof sketch: since `λ*` maximizes `ψ` on `Dplus`, the Hessian is symmetric, and
-- `λ* > -λ_min(H)`, the shifted quadratic owner lies in the positive-definite spectral region.
-- Differentiate the explicit formula for the dual value at interior points, use the resolvent
-- identity for the minimizing `h`-subproblem, and solve `ψ'(λ*) = 0` for the norm of the
-- resolvent point `-((A λ*)⁻¹).mulVec g`.
/-- Proposition 4.1.13: if `λ*` maximizes the dual function `ψ` over `dom ψ ∩ ℝ₊` and the
shifted symmetric Hessian lies in the interior region `λ* > -λ_min(H)`, then the
scalar first-order optimality condition holds:
`‖-(H + λ* I)⁻¹ g‖ = (2 / M) λ*`. -/
theorem cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    : ‖resolvent lamStar‖ = (2 / M : ℝ) * lamStar := by
  have hlam_nonneg : 0 ≤ lamStar := by
    simpa using hmax.1.2
  have hnormHalfCont :
      ContinuousAt (fun lam : ℝ ↦ (1 / 2 : ℝ) * ‖resolvent lam‖ ^ (2 : ℕ)) lamStar := by
    -- Route correction: compare nearby dual values through the explicit resolvent formula and use
    -- continuity of the resolvent, rather than differentiating the dual function directly.
    exact continuousAt_const.mul ((resolvent_continuousAt
      (H := H) hH hlam).norm.pow 2)
  rcases eq_or_lt_of_le hlam_nonneg with rfl | hlam_pos
  · have hlhs :
        Tendsto (fun t : ℝ ↦ (1 / 2 : ℝ) * ‖resolvent t‖ ^ (2 : ℕ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((1 / 2 : ℝ) * ‖resolvent 0‖ ^ (2 : ℕ))) := by
      simpa using hnormHalfCont.tendsto.mono_left nhdsWithin_le_nhds
    have hrhs :
        Tendsto (fun t : ℝ ↦ (2 / (3 * M ^ (2 : ℕ)) : ℝ) * t ^ (2 : ℕ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hcont :
          ContinuousAt (fun t : ℝ ↦ (2 / (3 * M ^ (2 : ℕ)) : ℝ) * t ^ (2 : ℕ)) 0 := by
        continuity
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hbound_eventually :
        ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (1 / 2 : ℝ) * ‖resolvent t‖ ^ (2 : ℕ) ≤
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * t ^ (2 : ℕ) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hineq :
          (t / 2 : ℝ) * ‖resolvent t‖ ^ (2 : ℕ) ≤ penalty t - penalty 0 := by
        simpa using
          dualMaximizer_controls_resolventNormSq
            (H := H) (M := M) (lamStar := 0) hM hH hmax hlam
            (μ := t) (le_of_lt ht) (by
              have ht0 : 0 < t := ht
              nlinarith [hlam, ht0])
      have hpenalty :
          penalty t - penalty 0 =
            t * ((2 / (3 * M ^ (2 : ℕ)) : ℝ) * t ^ (2 : ℕ)) := by
        rw [cubicPenalty_add_eq_factor (M := M) (lam := 0) (t := t)
          (hlam := le_rfl) (ht := le_of_lt ht)]
        ring
      rw [hpenalty] at hineq
      nlinarith [hineq, ht]
    have hhalf_le_zero :
        (1 / 2 : ℝ) * ‖resolvent 0‖ ^ (2 : ℕ) ≤ 0 :=
      le_of_tendsto_of_tendsto' hlhs hrhs hbound_eventually
    have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖resolvent 0‖ ^ (2 : ℕ) := by
      positivity
    have hsq_zero : ‖resolvent 0‖ ^ (2 : ℕ) = 0 := by
      nlinarith [hhalf_le_zero, hhalf_nonneg]
    have hnorm_zero : ‖resolvent 0‖ = 0 := by
      exact sq_eq_zero_iff.mp <| by simpa [pow_two] using hsq_zero
    simp [hnorm_zero]
  · let c : ℝ := (2 / (3 * M ^ (2 : ℕ)) : ℝ) * (3 * lamStar ^ (2 : ℕ))
    have hleft :
        Tendsto (fun t : ℝ ↦ (1 / 2 : ℝ) * ‖resolvent (lamStar - t)‖ ^ (2 : ℕ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((1 / 2 : ℝ) * ‖resolvent lamStar‖ ^ (2 : ℕ))) := by
      have hshiftCont : ContinuousAt (fun t : ℝ ↦ lamStar - t) 0 := by
        exact continuousAt_const.sub continuousAt_id
      simpa using (hnormHalfCont.comp hshiftCont).tendsto.mono_left nhdsWithin_le_nhds
    have hright :
        Tendsto (fun t : ℝ ↦ (1 / 2 : ℝ) * ‖resolvent (lamStar + t)‖ ^ (2 : ℕ))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0))
          (nhds ((1 / 2 : ℝ) * ‖resolvent lamStar‖ ^ (2 : ℕ))) := by
      have hshiftCont : ContinuousAt (fun t : ℝ ↦ lamStar + t) 0 := by
        exact continuousAt_const.add continuousAt_id
      simpa using (hnormHalfCont.comp hshiftCont).tendsto.mono_left nhdsWithin_le_nhds
    have hleftPoly :
        Tendsto
          (fun t : ℝ ↦ (2 / (3 * M ^ (2 : ℕ)) : ℝ) *
            (3 * lamStar ^ (2 : ℕ) - 3 * lamStar * t + t ^ (2 : ℕ)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) := by
      have hlin0 :
          ContinuousAt (fun t : ℝ ↦ lamStar * t) 0 := by
        exact continuousAt_const.mul continuousAt_id
      have hlin :
          ContinuousAt (fun t : ℝ ↦ (3 : ℝ) * lamStar * t) 0 := by
        simpa [mul_assoc] using (continuousAt_const.mul hlin0 :
          ContinuousAt (fun t : ℝ ↦ (3 : ℝ) * (lamStar * t)) 0)
      have hsq :
          ContinuousAt (fun t : ℝ ↦ t ^ (2 : ℕ)) 0 := by
        simpa [pow_two] using (continuousAt_id.mul continuousAt_id)
      have hcont :
          ContinuousAt
            (fun t : ℝ ↦ (2 / (3 * M ^ (2 : ℕ)) : ℝ) *
              (3 * lamStar ^ (2 : ℕ) - 3 * lamStar * t + t ^ (2 : ℕ))) 0 := by
        exact continuousAt_const.mul ((continuousAt_const.sub hlin).add hsq)
      simpa [c] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hrightPoly :
        Tendsto
          (fun t : ℝ ↦ (2 / (3 * M ^ (2 : ℕ)) : ℝ) *
            (3 * lamStar ^ (2 : ℕ) + 3 * lamStar * t + t ^ (2 : ℕ)))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds c) := by
      have hlin0 :
          ContinuousAt (fun t : ℝ ↦ lamStar * t) 0 := by
        exact continuousAt_const.mul continuousAt_id
      have hlin :
          ContinuousAt (fun t : ℝ ↦ (3 : ℝ) * lamStar * t) 0 := by
        simpa [mul_assoc] using (continuousAt_const.mul hlin0 :
          ContinuousAt (fun t : ℝ ↦ (3 : ℝ) * (lamStar * t)) 0)
      have hsq :
          ContinuousAt (fun t : ℝ ↦ t ^ (2 : ℕ)) 0 := by
        simpa [pow_two] using (continuousAt_id.mul continuousAt_id)
      have hcont :
          ContinuousAt
            (fun t : ℝ ↦ (2 / (3 * M ^ (2 : ℕ)) : ℝ) *
              (3 * lamStar ^ (2 : ℕ) + 3 * lamStar * t + t ^ (2 : ℕ))) 0 := by
        exact continuousAt_const.mul ((continuousAt_const.add hlin).add hsq)
      simpa [c] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    have hsmall : {t : ℝ | t < lamStar} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hlam_pos)
    have hinterior_small : {t : ℝ | t < lamStar + λ_min(H)} ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      have hgap_pos : 0 < lamStar + λ_min(H) := by
        nlinarith [hlam]
      exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hgap_pos)
    have hleft_eventually :
        ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (2 / (3 * M ^ (2 : ℕ)) : ℝ) *
              (3 * lamStar ^ (2 : ℕ) - 3 * lamStar * t + t ^ (2 : ℕ)) ≤
            (1 / 2 : ℝ) * ‖resolvent (lamStar - t)‖ ^ (2 : ℕ) := by
      filter_upwards [self_mem_nhdsWithin, hsmall, hinterior_small] with t ht htlt htgap
      have ht0 : 0 < t := ht
      have hμ_nonneg : 0 ≤ lamStar - t := by
        nlinarith
      have hμ_int : -λ_min(H) < lamStar - t := by
        nlinarith
      have hineq :
          ((lamStar - t - lamStar) / 2 : ℝ) * ‖resolvent (lamStar - t)‖ ^ (2 : ℕ) ≤
            penalty (lamStar - t) - penalty lamStar := by
        simpa using
          dualMaximizer_controls_resolventNormSq
            (H := H) (M := M) (lamStar := lamStar) hM hH hmax hlam
            (μ := lamStar - t) hμ_nonneg hμ_int
      have hpenalty :
          penalty lamStar - penalty (lamStar - t) =
            t * ((2 / (3 * M ^ (2 : ℕ)) : ℝ) *
              (3 * lamStar ^ (2 : ℕ) - 3 * lamStar * t + t ^ (2 : ℕ))) := by
        exact cubicPenalty_sub_eq_factor
          (M := M) (lam := lamStar) (t := t) (hlam := hlam_nonneg)
          (ht := le_of_lt ht) (htle := le_of_lt htlt)
      rw [hpenalty] at hineq
      nlinarith [hineq, ht0]
    have hright_eventually :
        ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (1 / 2 : ℝ) * ‖resolvent (lamStar + t)‖ ^ (2 : ℕ) ≤
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) *
              (3 * lamStar ^ (2 : ℕ) + 3 * lamStar * t + t ^ (2 : ℕ)) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := ht
      have hμ_nonneg : 0 ≤ lamStar + t := by
        nlinarith [hlam_nonneg, ht0]
      have hμ_int : -λ_min(H) < lamStar + t := by
        nlinarith [hlam, ht0]
      have hineq :
          ((lamStar + t - lamStar) / 2 : ℝ) * ‖resolvent (lamStar + t)‖ ^ (2 : ℕ) ≤
            penalty (lamStar + t) - penalty lamStar := by
        simpa using
          dualMaximizer_controls_resolventNormSq
            (H := H) (M := M) (lamStar := lamStar) hM hH hmax hlam
            (μ := lamStar + t) hμ_nonneg hμ_int
      have hpenalty :
          penalty (lamStar + t) - penalty lamStar =
            t * ((2 / (3 * M ^ (2 : ℕ)) : ℝ) *
              (3 * lamStar ^ (2 : ℕ) + 3 * lamStar * t + t ^ (2 : ℕ))) := by
        exact cubicPenalty_add_eq_factor
          (M := M) (lam := lamStar) (t := t) (hlam := hlam_nonneg)
          (ht := le_of_lt ht)
      rw [hpenalty] at hineq
      nlinarith [hineq, ht0]
    have hleft_le :
        c ≤ (1 / 2 : ℝ) * ‖resolvent lamStar‖ ^ (2 : ℕ) :=
      le_of_tendsto_of_tendsto' hleftPoly hleft hleft_eventually
    have hright_le :
        (1 / 2 : ℝ) * ‖resolvent lamStar‖ ^ (2 : ℕ) ≤ c :=
      le_of_tendsto_of_tendsto' hright hrightPoly hright_eventually
    have hhalf_eq :
        (1 / 2 : ℝ) * ‖resolvent lamStar‖ ^ (2 : ℕ) = c :=
      le_antisymm hright_le hleft_le
    have hsq :
        ‖resolvent lamStar‖ ^ (2 : ℕ) = ((2 / M : ℝ) * lamStar) ^ (2 : ℕ) := by
      have hc :
          c = (1 / 2 : ℝ) * ((2 / M : ℝ) * lamStar) ^ (2 : ℕ) := by
        dsimp [c]
        field_simp [hM.ne']
      rw [hc] at hhalf_eq
      nlinarith
    have hsqrt := congrArg Real.sqrt hsq
    have hrhs_nonneg : 0 ≤ (2 / M : ℝ) * lamStar := by
      positivity
    simpa [pow_two, abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrhs_nonneg] using hsqrt

-- Proof sketch: minimize the quadratic `h`-subproblem in the Lagrangian at the maximizing
-- multiplier `λ*`; the symmetry and spectral-interior hypotheses place `H + λ* I` in the
-- positive-definite quadratic region, so the unique minimizer is `-(H + λ* I)⁻¹ g`. Then
-- combine strong duality at `λ*` with the first-order condition from
-- `cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer` to conclude that this resolvent
-- point globally minimizes the primal cubic-regularized quadratic objective.
/-- Under the hypotheses of Proposition 4.1.13, the corresponding resolvent point
`-(H + λ* I)⁻¹ g` is a global minimizer of the primal cubic-regularized quadratic objective. -/
theorem cubicRegularizedQuadratic_resolvent_isMinimizer_of_dualMaximizer
    (hM : 0 < M) (hH : H.IsSymm)
    (hmax : IsMaxOn (cubicRegularizedQuadraticDualFunction g H M) Dplus lamStar)
    (hlam : -λ_min(H) < lamStar)
    :
    IsMinOn (cubicRegularizedQuadraticObjective g H M) Set.univ
      (resolvent lamStar) := by
  -- Compare the shifted quadratic terms at the resolvent and at an arbitrary point `h`.
  rw [isMinOn_univ_iff]
  intro h
  have hlam_nonneg : 0 ≤ lamStar := by
    simpa using hmax.1.2
  let τStar := cubicRegularizedQuadraticTauMinimizer M lamStar
  have hq :
      quadraticObjective 0 g (A lamStar) (resolvent lamStar) ≤
        quadraticObjective 0 g (A lamStar) h := by
    exact (isMinOn_univ_iff.mp
      (resolvent_isMinOn_shiftedQuadratic (g := g) (H := H) (M := M) hH hlam)) h
  have hτ :
      (M / 6 : ℝ) * |τStar| ^ (3 / 2 : ℝ) - (lamStar / 2 : ℝ) * τStar ≤
        (M / 6 : ℝ) * |‖h‖ ^ (2 : ℕ)| ^ (3 / 2 : ℝ) -
          (lamStar / 2 : ℝ) * (‖h‖ ^ (2 : ℕ)) := by
    exact (isMinOn_univ_iff.mp (cubicRegularizedQuadraticTauMinimizer_isMinOn M hM lamStar))
      (‖h‖ ^ (2 : ℕ))
  have hsum :
      cubicRegularizedQuadraticScalarLagrangian g H M (resolvent lamStar) τStar lamStar ≤
        cubicRegularizedQuadraticScalarLagrangian g H M h (‖h‖ ^ (2 : ℕ)) lamStar := by
    -- Add the quadratic optimality inequality and the scalar slack optimality inequality.
    rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term,
      cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term]
    exact add_le_add hq hτ
  have hτStar_eq :
      τStar = ‖resolvent lamStar‖ ^ (2 : ℕ) := by
    -- The norm identity from the first theorem makes the slack minimizer tight at the resolvent.
    have hnorm :
        ‖resolvent lamStar‖ = (2 / M : ℝ) * lamStar :=
      cubicRegularizedQuadratic_resolvent_norm_eq_of_dualMaximizer
        hM hH hmax hlam
    calc
      τStar = ((2 / M : ℝ) * lamStar) ^ (2 : ℕ) := by
        dsimp [τStar]
        rw [cubicRegularizedQuadraticTauMinimizer_def, abs_of_nonneg hlam_nonneg]
        field_simp [hM.ne']
        ring
      _ = ‖resolvent lamStar‖ ^ (2 : ℕ) := by
        rw [← hnorm]
  -- Rewrite both scalar Lagrangian values at tight slack and recover the primal objective.
  calc
    cubicRegularizedQuadraticObjective g H M (resolvent lamStar)
        = cubicRegularizedQuadraticScalarLagrangian g H M (resolvent lamStar) τStar lamStar := by
            rw [hτStar_eq]
            symm
            exact scalarLagrangian_at_norm_sq_eq_objective
              (g := g) (H := H) (M := M) (resolvent lamStar) lamStar
    _ ≤ cubicRegularizedQuadraticScalarLagrangian g H M h (‖h‖ ^ (2 : ℕ)) lamStar := hsum
    _ = cubicRegularizedQuadraticObjective g H M h := by
          exact scalarLagrangian_at_norm_sq_eq_objective
            (g := g) (H := H) (M := M) h lamStar

end
