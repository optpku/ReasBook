/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_9_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The cubic-regularized quadratic objective
`v(h) = ⟪g, h⟫ + (1 / 2) ⟪H h, h⟫ + (M / 6) ‖h‖^3`. -/
def cubicRegularizedQuadraticObjective
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) : E → ℝ :=
  fun h ↦
    dotProduct g h +
      (1 / 2 : ℝ) * dotProduct (H.mulVec h) h +
        (M / 6 : ℝ) * ‖h‖ ^ (3 : ℕ)

/-- Evaluating `cubicRegularizedQuadraticObjective g H M` recovers the displayed formula for
`v(h)`. -/
theorem cubicRegularizedQuadraticObjective_apply
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) :
    cubicRegularizedQuadraticObjective g H M h =
      dotProduct g h +
        (1 / 2 : ℝ) * dotProduct (H.mulVec h) h +
          (M / 6 : ℝ) * ‖h‖ ^ (3 : ℕ) :=
  rfl

/-- The scalar epigraph Lagrangian `𝓛(h, τ, λ)` for the cubic-regularized quadratic model. -/
def cubicRegularizedQuadraticScalarLagrangian
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) (τ lam : ℝ) : ℝ :=
  dotProduct g h +
    (1 / 2 : ℝ) * dotProduct (H.mulVec h) h +
      (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) +
        lam * ((1 / 2 : ℝ) * ‖h‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * τ)

/-- The scalar dual function `ψ(λ)` obtained by infimizing the epigraph Lagrangian over
`(h, τ) ∈ ℝⁿ × ℝ`. -/
def cubicRegularizedQuadraticDualFunction
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (lam : ℝ) : EReal :=
  sInf (Set.range fun z : E × ℝ ↦
    (cubicRegularizedQuadraticScalarLagrangian g H M z.1 z.2 lam : EReal))

/-- Expanding `cubicRegularizedQuadraticDualFunction g H M lam` gives the infimum definition of
`ψ(λ)`. -/
theorem cubicRegularizedQuadraticDualFunction_eq_sInf
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M lam : ℝ) :
    cubicRegularizedQuadraticDualFunction g H M lam =
      sInf (Set.range fun z : E × ℝ ↦
        (cubicRegularizedQuadraticScalarLagrangian g H M z.1 z.2 lam : EReal)) :=
  rfl

/-- The effective domain `dom ψ = {λ | ψ(λ) > -∞}` of the scalar dual function. -/
def cubicRegularizedQuadraticDualDomain
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) : Set ℝ :=
  { lam | ⊥ < cubicRegularizedQuadraticDualFunction g H M lam }

/-- Membership in `cubicRegularizedQuadraticDualDomain g H M` means exactly that the dual value
`ψ(λ)` is finite from below. -/
theorem mem_cubicRegularizedQuadraticDualDomain_iff
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M lam : ℝ) :
    lam ∈ cubicRegularizedQuadraticDualDomain g H M ↔
      ⊥ < cubicRegularizedQuadraticDualFunction g H M lam :=
  Iff.rfl

/-- The explicit slack-variable minimizer `τ(λ) = 4 λ |λ| / M²`. -/
def cubicRegularizedQuadraticTauMinimizer
    (M lam : ℝ) : ℝ :=
  (4 : ℝ) * lam * |lam| / M ^ (2 : ℕ)

/-- Expanding `cubicRegularizedQuadraticTauMinimizer M lam` recovers the formula
`4 λ |λ| / M²`. -/
theorem cubicRegularizedQuadraticTauMinimizer_def
    (M lam : ℝ) :
    cubicRegularizedQuadraticTauMinimizer M lam =
      (4 : ℝ) * lam * |lam| / M ^ (2 : ℕ) :=
  rfl

/-- Helper for Definition 4.1.14: the zero-offset quadratic owner agrees with the displayed
coordinate formula `⟪g, h⟫ + (1 / 2) ⟪Ah, h⟫`. -/
lemma quadraticObjective_zero_eq_dotProduct
    (g : E) (A : Matrix (Fin n) (Fin n) ℝ) (h : E) :
    quadraticObjective 0 g A h =
      dotProduct g h + (1 / 2 : ℝ) * dotProduct (A.mulVec h) h := by
  -- Convert the abstract inner products in `quadraticObjective` to the coordinate `dotProduct`
  -- form used by the scalar Lagrangian.
  rw [quadraticObjective]
  have hg : inner ℝ g h = dotProduct g h := by
    simpa [dotProduct_comm] using (EuclideanSpace.inner_eq_star_dotProduct g h)
  have hA : inner ℝ (A.toEuclideanLin h) h = dotProduct (A.mulVec h) h := by
    simpa [Matrix.toLpLin_apply, dotProduct_comm] using
      (EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin h) h)
  rw [hg, hA]
  ring

/-- Helper for Definition 4.1.14: the scalar Lagrangian splits into the shifted quadratic
`q_λ(h)` plus the pure slack-variable objective. -/
lemma cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) (τ lam : ℝ) :
    cubicRegularizedQuadraticScalarLagrangian g H M h τ lam =
      quadraticObjective 0 g (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h +
        ((M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ) := by
  -- Separate the `h`-dependent quadratic part from the scalar `τ`-objective.
  rw [cubicRegularizedQuadraticScalarLagrangian, quadraticObjective_zero_eq_dotProduct]
  have hnorm : dotProduct h h = ‖h‖ ^ (2 : ℕ) := by
    -- The identity-matrix contribution is exactly the Euclidean norm square.
    have hdot := (EuclideanSpace.inner_eq_star_dotProduct h h).symm
    simp at hdot
    exact hdot.trans (real_inner_self_eq_norm_sq h)
  simp [Matrix.add_mulVec, Matrix.smul_mulVec, hnorm, add_assoc, add_left_comm, add_comm,
    sub_eq_add_neg, mul_add]
  ring

/-- Helper for Definition 4.1.14: the slack objective is bounded below by the explicit cubic
penalty `-(2 / (3 M²)) |λ|³`. -/
lemma cubicRegularizedQuadraticTauObjective_ge_minValue
    (M : ℝ) (lam : ℝ) (hM : 0 < M) (τ : ℝ) :
    -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
      (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ := by
  -- First dominate the linear term by replacing `lam * τ` with `|lam| * |τ|`.
  have hlin : -(|lam| / 2 : ℝ) * |τ| ≤ -(lam / 2 : ℝ) * τ := by
    have hmul : lam * τ ≤ |lam| * |τ| := by
      calc
        lam * τ ≤ |lam * τ| := le_abs_self _
        _ = |lam| * |τ| := by rw [abs_mul]
    nlinarith
  let s : ℝ := Real.sqrt |τ|
  have hpow : |τ| ^ (3 / 2 : ℝ) = s ^ (3 : ℕ) := by
    -- Rewrite the `3 / 2` power as a cubic in `sqrt |τ|`.
    calc
      |τ| ^ (3 / 2 : ℝ) = (|τ| ^ (1 / 2 : ℝ)) ^ (3 : ℝ) := by
        rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * 3 by norm_num, Real.rpow_mul (abs_nonneg τ)]
      _ = s ^ (3 : ℕ) := by
        simp [s, Real.sqrt_eq_rpow]
  have hs_sq : s ^ (2 : ℕ) = |τ| := by
    -- `s = sqrt |τ|` was chosen precisely so that its square recovers `|τ|`.
    dsimp [s]
    exact Real.sq_sqrt (abs_nonneg τ)
  have hpoly :
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
        (M / 6 : ℝ) * s ^ (3 : ℕ) - (|lam| / 2 : ℝ) * s ^ (2 : ℕ) := by
    -- The remaining inequality is the nonnegativity of a factored cubic polynomial.
    have hnonneg : 0 ≤ (M / 6 : ℝ) * (s - 2 * |lam| / M) ^ (2 : ℕ) * (s + |lam| / M) := by
      positivity
    have hidentity :
        (M / 6 : ℝ) * (s - 2 * |lam| / M) ^ (2 : ℕ) * (s + |lam| / M) =
          (M / 6 : ℝ) * s ^ (3 : ℕ) - (|lam| / 2 : ℝ) * s ^ (2 : ℕ) +
            (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ) := by
      field_simp [hM.ne']
      ring
    nlinarith
  have hpoly' :
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) ≤
        (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (|lam| / 2 : ℝ) * |τ| := by
    rw [hpow, ← hs_sq]
    exact hpoly
  nlinarith

/-- Helper for Definition 4.1.14: the explicit slack minimizer attains the lower-bound value
`-(2 / (3 M²)) |λ|³`. -/
lemma cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer
    (M : ℝ) (lam : ℝ) (hM : 0 < M) :
    (M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) -
        (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
      -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) := by
  have habs :
      |cubicRegularizedQuadraticTauMinimizer M lam| = ((2 : ℝ) * |lam| / M) ^ (2 : ℕ) := by
    -- The minimizer has squared magnitude `(2 |λ| / M)²`.
    rw [cubicRegularizedQuadraticTauMinimizer, abs_div, abs_mul, abs_mul,
      abs_of_nonneg (by positivity), abs_abs, abs_of_pos (pow_pos hM 2)]
    field_simp [hM.ne']
    ring_nf
  have hpow :
      |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) =
        ((2 : ℝ) * |lam| / M) ^ (3 : ℕ) := by
    -- Raising that squared magnitude to `3 / 2` gives the expected cubic term.
    rw [habs]
    calc
      (((2 : ℝ) * |lam| / M) ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) =
          (((2 : ℝ) * |lam| / M) ^ (1 : ℕ) : ℝ) ^ (3 : ℕ) := by
        rw [← Real.rpow_natCast_mul (by positivity : 0 ≤ (2 : ℝ) * |lam| / M) 2 (3 / 2 : ℝ)]
        norm_num
      _ = ((2 : ℝ) * |lam| / M) ^ (3 : ℕ) := by ring
  have hlamtau :
      lam * cubicRegularizedQuadraticTauMinimizer M lam =
        |lam| * (((2 : ℝ) * |lam| / M) ^ (2 : ℕ)) := by
    -- The minimizer has the same sign as `lam`, so the linear term also depends only on `|lam|`.
    rw [cubicRegularizedQuadraticTauMinimizer]
    field_simp [hM.ne']
    ring_nf
    rw [← sq_abs lam]
    ring
  have hlinterm :
      (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
        (|lam| / 2 : ℝ) * (((2 : ℝ) * |lam| / M) ^ (2 : ℕ)) := by
    nlinarith [hlamtau]
  rw [hpow, hlinterm]
  field_simp [hM.ne']
  ring

-- Proof sketch: minimize the scalar function
-- `τ ↦ (M / 6) |τ|^(3 / 2) - (lam / 2) τ` directly; the critical point is the explicit owner
-- `cubicRegularizedQuadraticTauMinimizer M lam`, and convexity yields global minimality.
/-- For `M > 0`, the scalar function
`τ ↦ (M / 6) |τ|^(3 / 2) - (lam / 2) τ` is minimized at
`cubicRegularizedQuadraticTauMinimizer M lam`. -/
theorem cubicRegularizedQuadraticTauMinimizer_isMinOn
    (M : ℝ) (hM : 0 < M) (lam : ℝ) :
    IsMinOn
      (fun τ : ℝ ↦
        (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ)
      Set.univ
      (cubicRegularizedQuadraticTauMinimizer M lam) := by
  rw [isMinOn_univ_iff]
  intro τ
  -- Compare every slack value with the explicit minimum value attained at `τ(λ)`.
  calc
    (M / 6 : ℝ) * |cubicRegularizedQuadraticTauMinimizer M lam| ^ (3 / 2 : ℝ) -
        (lam / 2 : ℝ) * cubicRegularizedQuadraticTauMinimizer M lam =
        -((2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)) :=
      cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM
    _ ≤ (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ :=
      cubicRegularizedQuadraticTauObjective_ge_minValue M lam hM τ

/-- Definition 4.1.14: the auxiliary cubic subproblem is encoded by the equivalent one-constraint
epigraph Lagrangian problem with objective `\tilde v(h, τ) = ⟪g, h⟫ + (1 / 2) ⟪H h, h⟫ +
(M / 6) |τ|^{3/2}` and constraint `(1 / 2) ‖h‖² - (1 / 2) τ ≤ 0`; its generic Lagrangian and the
downstream scalar dual function are derived from this owner. -/
def cubicRegularizedQuadraticEpigraphProblem
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) : LagrangianProblem (E × ℝ) 1 :=
  { objective := fun z ↦
      dotProduct g z.1 +
        (1 / 2 : ℝ) * dotProduct (H.mulVec z.1) z.1 +
          (M / 6 : ℝ) * |z.2| ^ (3 / 2 : ℝ)
    constraints := fun _ z ↦ (1 / 2 : ℝ) * ‖z.1‖ ^ (2 : ℕ) - (1 / 2 : ℝ) * z.2 }

-- Proof sketch: unfold `cubicRegularizedQuadraticEpigraphProblem`,
-- and reuse the canonical single-constraint expansion
-- `LagrangianProblem.lagrangian_single_eq`.
/-- Expanding the epigraph problem Lagrangian recovers
`\tilde v(h, τ) + λ ((1 / 2) ‖h‖² - (1 / 2) τ)`. -/
theorem cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) (τ lam : ℝ) :
    (cubicRegularizedQuadraticEpigraphProblem g H M).lagrangian (h, τ)
        (single 0 lam) =
      cubicRegularizedQuadraticScalarLagrangian g H M h τ lam := by
  simp [cubicRegularizedQuadraticEpigraphProblem, cubicRegularizedQuadraticScalarLagrangian,
    LagrangianProblem.lagrangian_single_eq]

-- Proof sketch: evaluate the epigraph objective at the tight slack `τ = ‖h‖²` and simplify
-- `|‖h‖²|^(3/2)` to `‖h‖^3` using the nonnegative real-power identity for `‖h‖`.
/-- At the tight epigraph value `τ = ‖h‖²`, the epigraph objective recovers the displayed cubic
subproblem objective `⟪g, h⟫ + (1 / 2) ⟪H h, h⟫ + (M / 6) ‖h‖^3`. -/
theorem cubicRegularizedQuadraticEpigraphObjective_eq_formula_at_norm_sq
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M : ℝ) (h : E) :
    cubicRegularizedQuadraticEpigraphProblem g H M (h, ‖h‖ ^ (2 : ℕ)) =
      cubicRegularizedQuadraticObjective g H M h := by
  have hpow : (‖h‖ ^ (2 : ℕ) : ℝ) ^ (3 / 2 : ℝ) = ‖h‖ ^ (3 : ℕ) := by
    rw [← Real.rpow_natCast_mul (norm_nonneg h) 2 (3 / 2 : ℝ)]
    norm_num
  rw [cubicRegularizedQuadraticObjective_apply]
  simp [cubicRegularizedQuadraticEpigraphProblem, hpow]

-- Proof sketch: eliminating the slack variable shows that the cubic penalty contributes only a
-- finite additive constant, so the effective dual domain is controlled exactly by boundedness
-- below of the shifted quadratic form `q_λ`. This is the canonical bridge reused downstream in
-- Proposition 4.1.8 and its diagonal specialization.
/-- The effective domain of the scalar dual function consists exactly of those multipliers `λ`
for which the shifted quadratic objective `q_λ` is bounded below. -/
theorem cubicRegularizedQuadraticScalarDualDomain_eq
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) {M : ℝ}
    (hM : 0 < M) :
    cubicRegularizedQuadraticDualDomain g H M =
      { lam |
        BddBelow
          (Set.range
            (quadraticObjective 0 g
              (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)))) } := by
  ext lam
  constructor
  · intro hdom
    change ⊥ < cubicRegularizedQuadraticDualFunction g H M lam at hdom
    let κ : ℝ := (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)
    refine ⟨(cubicRegularizedQuadraticDualFunction g H M lam).toReal + κ, ?_⟩
    rintro y ⟨h, rfl⟩
    have hsle : cubicRegularizedQuadraticDualFunction g H M lam ≤
        (cubicRegularizedQuadraticScalarLagrangian g H M h
          (cubicRegularizedQuadraticTauMinimizer M lam) lam : EReal) := by
      -- Evaluate the infimum at the explicit slack minimizer.
      rw [cubicRegularizedQuadraticDualFunction]
      exact sInf_le ⟨(h, cubicRegularizedQuadraticTauMinimizer M lam), rfl⟩
    have hsle_real :
        (cubicRegularizedQuadraticDualFunction g H M lam).toReal ≤
          cubicRegularizedQuadraticScalarLagrangian g H M h
            (cubicRegularizedQuadraticTauMinimizer M lam) lam :=
      EReal.toReal_le_toReal hsle (ne_of_gt hdom) (EReal.coe_ne_top _)
    have hvalue :
        cubicRegularizedQuadraticScalarLagrangian g H M h
            (cubicRegularizedQuadraticTauMinimizer M lam) lam =
          quadraticObjective 0 g (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h - κ := by
      -- After minimizing over `τ`, only the shifted quadratic in `h` remains.
      dsimp [κ]
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term,
        cubicRegularizedQuadraticTauObjective_eq_minValue_at_minimizer M lam hM]
      ring
    rw [hvalue] at hsle_real
    dsimp [κ]
    nlinarith
  · rintro ⟨b, hb⟩
    change ⊥ < cubicRegularizedQuadraticDualFunction g H M lam
    let κ : ℝ := (2 / (3 * M ^ (2 : ℕ)) : ℝ) * |lam| ^ (3 : ℕ)
    refine lt_of_lt_of_le (EReal.bot_lt_coe (b - κ)) ?_
    rw [cubicRegularizedQuadraticDualFunction]
    refine le_sInf ?_
    rintro y ⟨⟨h, τ⟩, rfl⟩
    have hq : b ≤ quadraticObjective 0 g (H + lam • (1 : Matrix (Fin n) (Fin n) ℝ)) h :=
      hb ⟨h, rfl⟩
    have hτ : -κ ≤ (M / 6 : ℝ) * |τ| ^ (3 / 2 : ℝ) - (lam / 2 : ℝ) * τ := by
      -- The slack-variable objective is always at least the explicit minimum value.
      dsimp [κ]
      simpa using cubicRegularizedQuadraticTauObjective_ge_minValue M lam hM τ
    have hsum : b - κ ≤ cubicRegularizedQuadraticScalarLagrangian g H M h τ lam := by
      -- Combine the quadratic lower bound with the universal scalar lower bound.
      rw [cubicRegularizedQuadraticScalarLagrangian_eq_shiftedQuadratic_add_tau_term]
      nlinarith
    exact EReal.coe_le_coe_iff.2 hsum
