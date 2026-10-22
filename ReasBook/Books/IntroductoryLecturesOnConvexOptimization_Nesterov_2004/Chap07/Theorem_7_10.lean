/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_35
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open MeasureTheory
open scoped EllipsoidNotation MatrixOrder PositiveDefMatrixNorm

variable {n : ℕ} {m : ℕ+}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ
local notation "PosMatₙ" => { G : Matₙ // Matrix.PosDef G }

/- Theorem 7.10 lies in Chapter 7's sign-invariant diagonal-rounding / stopping-time domain.

Sampled owner-style declarations:
- `signSymmetricConvexHull` and `averageDiagonalSquare` in `Definition_7_35.lean`, the Chapter 7
  owners for the source hull `Conv ⋃ᵢ B(aᵢ)` and its canonical diagonal initialization;
- `ellipsoidBoxInterpolationMatrix` and `ellipsoidBoxLogVolumePotential` in
  `Definition_7_34.lean`, the source-facing one-step matrix update and its logarithmic potential;
- `ellipsoidBoxAlphaStar`, `ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison`, and
  `ellipsoidBoxGammaComparison_neg` in `Lemma_7_7.lean`, the canonical Chapter 7 step-size and
  potential-comparison API;
- `CentralSymmetricRoundingMethod` in `Algorithm_7_5.lean` and
  `CentralSymmetricRoundingMethod.stoppingIndex_le` in `Theorem_7_6.lean`, the nearby owner-level
  pattern where the algorithm object carries the primitive iteration data and the stopping time is
  derived canonically as a first-hit index.

Best owner abstraction:
- source-facing: the sign-invariant rounding method itself, with the canonical initialization
  `D₀ = averageDiagonalSquare a` and the recursive update scheme `(7.2.18)`;
- core/canonical: `signSymmetricConvexHull`, `averageDiagonalSquare`,
  `ellipsoidBoxInterpolationMatrix`, `ellipsoidBoxAlphaStar`, and
  `ellipsoidBoxLogVolumePotential`;
- bridge/view: the potential-drop comparison from Lemma 7.7, applied along the continuing
  iterations of the method.

Primitive data:
- the generating family `a₁, …, aₘ`;
- the current-state dual-norm maximizer choice on positive-definite matrices;
- the positivity of the canonical initial matrix and of each recursive update step.

Derived API:
- the recursive positive-definite orbit `D₀, D₁, …` with
  `D₀ = averageDiagonalSquare a` and
  `Dₖ₊₁ = ellipsoidBoxInterpolationMatrix Dₖ gₖ αₖ`;
- the chosen points `gₖ`;
- the dual radius `rₖ = max {‖g‖*_{Dₖ} | g ∈ signSymmetricConvexHull a}` realized by `gₖ`;
- the step size `αₖ = ellipsoidBoxAlphaStar Dₖ gₖ`;
- the one-step logarithmic drop `ellipsoidBoxLogVolumePotential Dₖ gₖ αₖ`;
- the stopping criterion `rₖ ≤ γ √n` and its canonical first stopping time.

The previous version used a public wrapper whose primitive fields were arbitrary sequences. This
refinement follows the Chapter 7 iterate-owner pattern instead: the public owner is the recursive
sign-invariant algorithm itself, the maximizer property is primitive owner data rather than a
downstream theorem hypothesis, and the matrix/radius/stopping-time API is derived canonically from
that recursion.
-/

section PotentialDrop

variable {potential : ℕ → ℝ}

-- Proof sketch: iterate `hstep` to obtain `potential k ≤ potential 0 - k * drop` for every
-- `k ≤ T`, then combine the terminal lower bound `0 ≤ potential T` with the initial upper bound
-- `potential 0 ≤ B` to conclude `T * drop ≤ B`.
/-- A potential sequence that starts below an explicit bound `B`, stays nonnegative at a terminal
time `T`, and decreases by at least a fixed positive amount `δ` at every step before `T` must
satisfy `T ≤ δ⁻¹ B`. -/
theorem stoppingTime_le_of_positive_drop
    (T : ℕ)
    (B drop : ℝ)
    (hdrop : 0 < drop)
    (hinitial : potential 0 ≤ B)
    (hterminal : 0 ≤ potential T)
    (hstep :
      ∀ k : ℕ, k < T →
        potential (k + 1) ≤ potential k - drop) :
    (T : ℝ) ≤ drop⁻¹ * B := by
  have htelescoping :
      ∀ k : ℕ, k ≤ T →
        potential k ≤ potential 0 - (k : ℝ) * drop := by
    intro k
    induction k with
    | zero =>
        intro _
        simp
    | succ k ih =>
        intro hk
        have hk_lt : k < T := Nat.lt_of_succ_le hk
        have hk_le : k ≤ T := Nat.le_of_lt hk_lt
        have hstepk := hstep k hk_lt
        have hprev := ih hk_le
        have hcast : (((k + 1 : ℕ) : ℝ)) * drop = (k : ℝ) * drop + drop := by
          norm_num [add_mul, mul_add, add_comm, add_left_comm, add_assoc]
        -- Add the next uniform decrease to the telescoped prefix estimate.
        linarith
  have hfinal := htelescoping T le_rfl
  have hbudget : (T : ℝ) * drop ≤ B := by
    -- The terminal nonnegativity and initial upper bound squeeze the total drop.
    linarith
  -- Divide by the positive drop to recover the stopping-time bound.
  simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
    (le_div_iff₀ hdrop).2 hbudget

end PotentialDrop

/-- A sign-invariant diagonal rounding algorithm for the family `a₁, …, aₘ` is determined by the
canonical initial matrix `D₀ = averageDiagonalSquare a`, a choice of a current dual-norm
maximizer `gₖ ∈ signSymmetricConvexHull a` from each positive-definite matrix state, the
requirement that the Chapter 7 update `(7.2.18)` stays positive definite, and the intrinsic
Chapter 7 containments that every unit ellipsoid `W₁(Dₖ)` along the recursive orbit stays in the
generated sign-symmetric hull while that hull remains inside the initial outer ellipsoid
`W[m √n](D₀)`. The actual orbit `D₀, D₁, …`, the chosen points `g₀, g₁, …`, and the stopping
time for the radius threshold are derived recursively from this source-facing owner.
-/
structure SignInvariantRoundingAlgorithm where
  /-- The generating family `a₁, …, aₘ`. -/
  vectors : Fin (m : ℕ) → EuclideanSpace ℝ (Fin n)
  /-- The canonical initial matrix `D₀ = averageDiagonalSquare a` is positive definite. -/
  initial_posDef : (averageDiagonalSquare vectors).PosDef
  /-- The current-state choice of the point `gₖ ∈ signSymmetricConvexHull a`. -/
  selectMaximizer : PosMatₙ → Eₙ
  /-- Every chosen point lies in the generated sign-symmetric hull and maximizes the current
  `G`-dual norm there. -/
  selectMaximizer_spec :
    ∀ G : PosMatₙ,
      selectMaximizer G ∈ signSymmetricConvexHull vectors ∧
        IsMaxOn (fun g : Eₙ ↦ ‖g‖[G,*]) (signSymmetricConvexHull vectors) (selectMaximizer G)
  /-- The recursive update `(7.2.18)` remains positive definite at every positive-definite state.
  -/
  step_posDef :
    ∀ G : PosMatₙ,
      (ellipsoidBoxInterpolationMatrix G.1 (selectMaximizer G)
        (ellipsoidBoxAlphaStar G.1 G.2 (selectMaximizer G))).PosDef
  /-- Every unit ellipsoid along the recursive Chapter 7 orbit stays in the generated
  sign-symmetric hull. -/
  unit_subset_generatedSet :
    ∀ k : ℕ,
      W[1]((((fun G : PosMatₙ ↦
          ⟨ellipsoidBoxInterpolationMatrix G.1 (selectMaximizer G)
              (ellipsoidBoxAlphaStar G.1 G.2 (selectMaximizer G)),
            step_posDef G⟩)^[k])
        ⟨averageDiagonalSquare vectors, initial_posDef⟩).1) ⊆ signSymmetricConvexHull vectors
  /-- The generated sign-symmetric hull is contained in the initial outer ellipsoid
  `W[m √n](D₀)`. -/
  generatedSet_subset_initialOuter :
    signSymmetricConvexHull vectors ⊆
      centeredMatrixEllipsoid (averageDiagonalSquare vectors) ((m : ℝ) * Real.sqrt (n : ℝ))

namespace SignInvariantRoundingAlgorithm

local notation "SignAlg" => @SignInvariantRoundingAlgorithm n m

/-- The sign-symmetric hull generated by the input family `a₁, …, aₘ`. -/
def generatedSet (algorithm : SignAlg) : Set Eₙ :=
  signSymmetricConvexHull algorithm.vectors

/-- The current positive-definite matrix owner at stage `0`. -/
def initialMatrix (algorithm : SignAlg) : PosMatₙ :=
  ⟨averageDiagonalSquare algorithm.vectors, algorithm.initial_posDef⟩

/-- The Chapter 7 step size `α*(D, g)` attached to a positive-definite matrix state `D` and its
selected maximizer `g`. -/
def stepAlpha
    (algorithm : SignAlg) (G : PosMatₙ) : ℝ :=
  ellipsoidBoxAlphaStar G.1 G.2 (algorithm.selectMaximizer G)

/-- The one-step recursive update `(7.2.18)` on positive-definite matrix states. -/
def step
    (algorithm : SignAlg) (G : PosMatₙ) : PosMatₙ :=
  ⟨ellipsoidBoxInterpolationMatrix G.1 (algorithm.selectMaximizer G) (algorithm.stepAlpha G),
    algorithm.step_posDef G⟩

/-- The recursive positive-definite matrix orbit `D₀, D₁, D₂, ...` generated by the sign-
invariant rounding update. -/
def currentMatrix
    (algorithm : SignAlg) : ℕ → PosMatₙ :=
  fun k ↦ (algorithm.step^[k]) (algorithm.initialMatrix)

/-- A sign-invariant rounding algorithm can be used as its underlying matrix orbit
`D₀, D₁, D₂, ...`. -/
instance : CoeFun SignAlg (fun _ ↦ ℕ → Matₙ) where
  coe algorithm k := (algorithm.currentMatrix k).1

/-- The algorithm starts from the canonical Chapter 7 initialization
`D₀ = averageDiagonalSquare a`. -/
@[simp] theorem matrix_zero
    (algorithm : SignAlg) :
    algorithm 0 = averageDiagonalSquare algorithm.vectors :=
  rfl

/-- The recursive orbit at stage `0` is the canonical initial positive-definite matrix owner. -/
@[simp] theorem currentMatrix_zero
    (algorithm : SignAlg) :
    algorithm.currentMatrix 0 = algorithm.initialMatrix :=
  rfl

/-- Every unit ellipsoid `W₁(Dₖ)` along the recursive sign-invariant orbit stays in the generated
sign-symmetric hull. -/
theorem unit_ellipsoid_subset_generatedSet
    (algorithm : SignAlg) (k : ℕ) :
    W[1]((algorithm k)) ⊆ generatedSet algorithm := by
  simpa [currentMatrix, initialMatrix, step, stepAlpha, generatedSet] using
    algorithm.unit_subset_generatedSet k

/-- The generated sign-symmetric hull lies in the initial outer ellipsoid `W[m √n](D₀)`. -/
theorem generatedSet_subset_initial_outer_ellipsoid
    (algorithm : SignAlg) :
    generatedSet algorithm ⊆
      centeredMatrixEllipsoid (algorithm 0) ((m : ℝ) * Real.sqrt (n : ℝ)) := by
  simpa [generatedSet, matrix_zero] using algorithm.generatedSet_subset_initialOuter

/-- The chosen point `gₖ` at stage `k` is the state-dependent maximizer selected from `Dₖ`. -/
def maximizer (algorithm : SignAlg) (k : ℕ) : Eₙ :=
  algorithm.selectMaximizer (algorithm.currentMatrix k)

/-- Every chosen point belongs to the generated sign-symmetric hull. -/
theorem maximizer_mem_generatedSet
    (algorithm : SignAlg) (k : ℕ) :
    algorithm.maximizer k ∈ generatedSet algorithm :=
  (algorithm.selectMaximizer_spec (algorithm.currentMatrix k)).1

/-- At stage `k`, the chosen point maximizes the current dual norm on the generated
sign-symmetric hull. -/
theorem maximizer_isMaxOn_generatedSet
    (algorithm : SignAlg) (k : ℕ) :
    IsMaxOn
      (fun g : Eₙ ↦ ‖g‖[algorithm.currentMatrix k,*])
      (generatedSet algorithm)
      (algorithm.maximizer k) :=
  (algorithm.selectMaximizer_spec (algorithm.currentMatrix k)).2

/-- The recursive matrix orbit satisfies the Chapter 7 successor update `(7.2.18)`. -/
theorem matrix_succ
    (algorithm : SignAlg) (k : ℕ) :
    algorithm (k + 1) =
      ellipsoidBoxInterpolationMatrix (algorithm k) (algorithm.maximizer k)
        (algorithm.stepAlpha (algorithm.currentMatrix k)) := by
  simpa [currentMatrix, step, stepAlpha, maximizer] using
    congrArg Subtype.val
      (Function.iterate_succ_apply' algorithm.step k algorithm.initialMatrix)

/-- The positive-definite matrix owner at stage `k + 1` is obtained by one application of the
recursive update step. -/
theorem currentMatrix_succ
    (algorithm : SignAlg) (k : ℕ) :
    algorithm.currentMatrix (k + 1) = algorithm.step (algorithm.currentMatrix k) := by
  simpa [currentMatrix] using
    Function.iterate_succ_apply' algorithm.step k algorithm.initialMatrix

/-- The Chapter 7 step size `αₖ = α*(Dₖ, gₖ)`. -/
def alpha (algorithm : SignAlg) (k : ℕ) : ℝ :=
  algorithm.stepAlpha (algorithm.currentMatrix k)

/-- The maximal dual radius `rₖ = max {‖g‖*_{Dₖ} | g ∈ signSymmetricConvexHull a}` realized by
the chosen maximizer `gₖ`. -/
def radius (algorithm : SignAlg) (k : ℕ) : ℝ :=
  ‖algorithm.maximizer k‖[algorithm.currentMatrix k,*]

/-- Every point of the generated sign-symmetric hull has current dual norm at most the stage-`k`
radius. -/
theorem dualNorm_le_radius
    (algorithm : SignAlg) (k : ℕ) {g : Eₙ}
    (hg : g ∈ generatedSet algorithm) :
    ‖g‖[algorithm.currentMatrix k,*] ≤ algorithm.radius k :=
  (algorithm.maximizer_isMaxOn_generatedSet k) hg

/-- The one-step logarithmic potential contribution at stage `k`. -/
def potentialStep (algorithm : SignAlg) (k : ℕ) : ℝ :=
  ellipsoidBoxLogVolumePotential (algorithm k) (algorithm.maximizer k) (algorithm.alpha k)

/-- The remaining logarithmic-volume budget
`B - (log det Dₖ - log det D₀)` at stage `k`, measured against the canonical matrix orbit of the
sign-invariant rounding algorithm. -/
def remainingLogVolumeBudget
    (algorithm : SignAlg) (B : ℝ) (k : ℕ) : ℝ :=
  B - (Real.log (Matrix.det (algorithm k)) - Real.log (Matrix.det (algorithm 0)))

/-- At stage `0`, the remaining logarithmic-volume budget is exactly the initial budget `B`. -/
@[simp] theorem remainingLogVolumeBudget_zero
    (algorithm : SignAlg) (B : ℝ) :
    algorithm.remainingLogVolumeBudget B 0 = B := by
  simp [remainingLogVolumeBudget]

/-- Helper for Theorem 7.10: every matrix in the recursive sign-invariant orbit is diagonal. -/
theorem matrix_isDiag
    (algorithm : SignAlg) (k : ℕ) :
    (algorithm k).IsDiag := by
  induction k with
  | zero =>
      -- The canonical initialization is a diagonal matrix by construction.
      rw [matrix_zero, averageDiagonalSquare_eq_diagonal]
      simp
  | succ k ih =>
      -- The Chapter 7 update itself is a diagonal interpolation matrix.
      rw [matrix_succ]
      simp [ellipsoidBoxInterpolationMatrix]

/-- Advancing one sign-invariant rounding step decreases the remaining logarithmic-volume budget by
exactly the Chapter 7 one-step potential `ellipsoidBoxLogVolumePotential Dₖ gₖ αₖ`. -/
theorem remainingLogVolumeBudget_succ
    (algorithm : SignAlg) (B : ℝ) (k : ℕ) :
    algorithm.remainingLogVolumeBudget B (k + 1) =
      algorithm.remainingLogVolumeBudget B k + algorithm.potentialStep k := by
  -- Rewrite the interpolation path at `α = 0` back to the current diagonal matrix `Dₖ`.
  have hinterpolation_zero :
      ellipsoidBoxInterpolationMatrix (algorithm k) (algorithm.maximizer k) 0 = algorithm k := by
    rw [ellipsoidBoxInterpolationMatrix]
    simpa using (algorithm.matrix_isDiag k).diagonal_diag
  have hdet_current_ne : Matrix.det (algorithm k) ≠ 0 :=
    (algorithm.currentMatrix k).2.det_pos.ne'
  have hdet_next_ne :
      Matrix.det
          (ellipsoidBoxInterpolationMatrix (algorithm k) (algorithm.maximizer k)
            (algorithm.stepAlpha (algorithm.currentMatrix k))) ≠ 0 :=
    (algorithm.step_posDef (algorithm.currentMatrix k)).det_pos.ne'
  -- The recurrence is the telescoping identity for the logarithmic determinant ratio.
  rw [remainingLogVolumeBudget, remainingLogVolumeBudget, potentialStep,
    alpha, ellipsoidBoxLogVolumePotential_def, algorithm.matrix_succ, hinterpolation_zero]
  rw [Real.log_div hdet_current_ne hdet_next_ne]
  ring_nf

/-- Helper for Theorem 7.10: a factorization `A = Bᴴ * B` rewrites the quadratic form of `A`
as the Euclidean norm of `B x`. -/
private theorem sqrtInnerEqEuclideanImageNorm
    (A B : Matrix (Fin n) (Fin n) ℝ) (hAeq : A = Bᴴ * B) (x : Eₙ) :
    Real.sqrt (inner ℝ (A.toEuclideanLin x) x) = ‖B.toEuclideanLin x‖ := by
  have hquad : inner ℝ (A.toEuclideanLin x) x = ‖B.toEuclideanLin x‖ ^ (2 : ℕ) := by
    calc
      inner ℝ (A.toEuclideanLin x) x = dotProduct x.ofLp (A *ᵥ x.ofLp) := by
        simpa only [Matrix.ofLp_toLpLin] using
          (EuclideanSpace.inner_eq_star_dotProduct (A.toEuclideanLin x) x)
      _ = dotProduct x.ofLp ((Bᴴ * B) *ᵥ x.ofLp) := by
        rw [hAeq]
      _ = dotProduct (B *ᵥ x.ofLp) (B *ᵥ x.ofLp) := by
        rw [dotProduct_comm]
        rw [dotProduct_comm, ← mulVec_mulVec, dotProduct_mulVec, vecMul_conjTranspose]
        simp
      _ = ‖B.toEuclideanLin x‖ ^ (2 : ℕ) := by
        have hraw :=
          EuclideanSpace.inner_eq_star_dotProduct (B.toEuclideanLin x) (B.toEuclideanLin x)
        simp only [Matrix.ofLp_toLpLin] at hraw
        have hnorm :
            inner ℝ (B.toEuclideanLin x) (B.toEuclideanLin x) =
              ‖B.toEuclideanLin x‖ ^ (2 : ℕ) := by
          simp
        exact hraw.symm.trans hnorm
  rw [hquad, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- Helper for Theorem 7.10: centered matrix ellipsoids have volume
`√det(G)` times the Euclidean closed-ball volume of the same radius. -/
private theorem centeredMatrixEllipsoid_volume
    (G : Matₙ) (hG : G.PosDef) {r : ℝ} (_hr : 0 ≤ r) :
    volume (W[r](G)) =
      ENNReal.ofReal (Real.sqrt G.det) * volume (Metric.closedBall (0 : Eₙ) r) := by
  obtain ⟨B, hBunit, hBself, hfactor⟩ :=
    (CStarAlgebra.isStrictlyPositive_iff_exists_isUnit_and_isSelfAdjoint_and_eq_mul_self).mp
      hG.isStrictlyPositive
  have hInvFactor : G⁻¹ = B⁻¹ᴴ * B⁻¹ := by
    -- Inverting `G = Bᴴ * B` produces the linear model for the centered ellipsoid.
    calc
      G⁻¹ = (B * B)⁻¹ := by
        rw [hfactor]
      _ = B⁻¹ * B⁻¹ := by
        rw [Matrix.mul_inv_rev]
      _ = B⁻¹ᴴ * B⁻¹ := by
        congr 1
        rw [Matrix.conjTranspose_nonsing_inv]
        simpa using congrArg Inv.inv hBself.symm
  have hzero :
      W[r](G) = ((B⁻¹).toEuclideanLin) ⁻¹' Metric.closedBall (0 : Eₙ) r := by
    -- The centered ellipsoid is exactly the inverse image of the Euclidean radius-`r` ball.
    ext y
    rw [mem_centeredMatrixEllipsoid_iff]
    simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right]
    have hsqrt := sqrtInnerEqEuclideanImageNorm G⁻¹ B⁻¹ hInvFactor y
    simpa [hsqrt]
  have hdetLinInv :
      LinearMap.det ((B⁻¹).toEuclideanLin : Eₙ →ₗ[ℝ] Eₙ) = (B.det)⁻¹ := by
    -- Identify the determinant of the Euclidean linear map with the determinant of its matrix.
    calc
      LinearMap.det ((B⁻¹).toEuclideanLin : Eₙ →ₗ[ℝ] Eₙ) = (B⁻¹).det := by
        simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using
          (LinearMap.det_toMatrix ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis)
            ((B⁻¹).toEuclideanLin : Eₙ →ₗ[ℝ] Eₙ)).symm
      _ = (B.det)⁻¹ := by
        simpa using (Matrix.det_nonsing_inv B)
  have hBdet : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBunit
  have hdetLinInv_ne :
      LinearMap.det ((B⁻¹).toEuclideanLin : Eₙ →ₗ[ℝ] Eₙ) ≠ 0 := by
    rw [hdetLinInv]
    exact inv_ne_zero hBdet.ne_zero
  have hdet_abs :
      |(LinearMap.det ((B⁻¹).toEuclideanLin : Eₙ →ₗ[ℝ] Eₙ))⁻¹| = |B.det| := by
    rw [hdetLinInv]
    simp
  have hBdet_abs : |B.det| = Real.sqrt G.det := by
    rw [hfactor, Matrix.det_mul]
    simpa [pow_two, mul_comm] using (Real.sqrt_sq_eq_abs B.det).symm
  calc
    volume (W[r](G))
        = volume (((B⁻¹).toEuclideanLin) ⁻¹' Metric.closedBall (0 : Eₙ) r) := by
            rw [hzero]
    _ =
        ENNReal.ofReal |(LinearMap.det ((B⁻¹).toEuclideanLin : Eₙ →ₗ[ℝ] Eₙ))⁻¹| *
          volume (Metric.closedBall (0 : Eₙ) r) := by
            rw [MeasureTheory.Measure.addHaar_preimage_linearMap volume hdetLinInv_ne]
    _ = ENNReal.ofReal |B.det| * volume (Metric.closedBall (0 : Eₙ) r) := by
          rw [hdet_abs]
    _ = ENNReal.ofReal (Real.sqrt G.det) * volume (Metric.closedBall (0 : Eₙ) r) := by
          rw [hBdet_abs]

/-- Helper for Theorem 7.10: the centered ellipsoid volume identity in real-valued form. -/
private theorem centeredMatrixEllipsoidVolume_toReal
    (G : Matₙ) (hG : G.PosDef) {r : ℝ} (hr : 0 ≤ r) :
    (volume (W[r](G))).toReal =
      Real.sqrt G.det * (volume (Metric.closedBall (0 : Eₙ) r)).toReal := by
  rw [centeredMatrixEllipsoid_volume G hG hr, ENNReal.toReal_mul, ENNReal.toReal_ofReal]
  simp

/-- Helper for Theorem 7.10: Euclidean closed-ball volumes scale by `r ^ n` in `ℝⁿ`. -/
private theorem closedBallVolume_toReal_eq_pow
    (hn : 1 ≤ n) {r : ℝ} (hr : 0 ≤ r) :
    (volume (Metric.closedBall (0 : Eₙ) r)).toReal =
      r ^ n * (volume (Metric.closedBall (0 : Eₙ) 1)).toReal := by
  letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.succ_le_iff.mp hn)
  -- Compare the explicit volume formulas for the radius-`r` and radius-`1` Euclidean balls.
  rw [EuclideanSpace.volume_closedBall, EuclideanSpace.volume_closedBall]
  simp [hr]

/-- The stopping criterion from Theorem 7.10: the stage-`k` dual radius is at most `γ √n`. -/
def stoppingCriterion (algorithm : SignAlg) (γ : ℝ) (k : ℕ) : Prop :=
  algorithm.radius k ≤ γ * Real.sqrt (n : ℝ)

/-- The algorithm terminates once some iterate satisfies the radius threshold `rₖ ≤ γ √n`. -/
def Terminates (algorithm : SignAlg) (γ : ℝ) : Prop :=
  ∃ k : ℕ, algorithm.stoppingCriterion γ k

/-- The canonical stopping time is the first iterate satisfying the stopping criterion
`rₖ ≤ γ √n`. -/
noncomputable def stoppingTime
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) : ℕ := by
  classical
  exact Nat.find hTerminate

/-- The first stopping time is least with respect to the radius threshold. -/
theorem stoppingTime_isLeast
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) :
    IsLeast {k : ℕ | algorithm.stoppingCriterion γ k} (algorithm.stoppingTime hTerminate) := by
  classical
  simpa [stoppingTime, Terminates] using Nat.isLeast_find hTerminate

/-- The stopping test succeeds at the canonical stopping time. -/
theorem stoppingTime_spec
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) :
    algorithm.stoppingCriterion γ (algorithm.stoppingTime hTerminate) :=
  (algorithm.stoppingTime_isLeast hTerminate).1

/-- No earlier stage satisfies the stopping criterion. -/
theorem stoppingTime_min
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) {k : ℕ}
    (hk : k < algorithm.stoppingTime hTerminate) :
    ¬ algorithm.stoppingCriterion γ k := by
  exact fun hkStop ↦
    (not_le_of_gt hk) ((algorithm.stoppingTime_isLeast hTerminate).2 hkStop)

/-- Before the canonical stopping time, the current dual radius is strictly larger than
`γ √n`. -/
theorem threshold_lt_radius_of_lt_stoppingTime
    (algorithm : SignAlg) {γ : ℝ} (hTerminate : algorithm.Terminates γ) {k : ℕ}
    (hk : k < algorithm.stoppingTime hTerminate) :
    γ * Real.sqrt (n : ℝ) < algorithm.radius k := by
  exact lt_of_not_ge <| by
    simpa [stoppingCriterion] using algorithm.stoppingTime_min hTerminate hk

/-- Helper for Theorem 7.10: a genuinely continuing iterate packages `γ` into the interval
required by Lemma 7.7's comparison estimate. -/
theorem gamma_mem_comparison_interval_of_continuing
    (algorithm : SignAlg)
    (γ : ℝ) (hn : 1 ≤ n)
    (hγ : Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) ≤ γ)
    {k : ℕ}
    (hcontinue : γ * Real.sqrt (n : ℝ) < algorithm.radius k) :
    γ ∈ Set.Ioc (1 : ℝ) (algorithm.radius k / Real.sqrt (n : ℝ)) := by
  have hn_nat_pos : 0 < n := lt_of_lt_of_le Nat.succ_pos' hn
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hn_nat_pos)
  have hgamma_gt_one : 1 < γ := by
    have hsqrt_lower : 1 < Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) := by
      rw [← Real.sqrt_one]
      apply Real.sqrt_lt_sqrt
      · positivity
      · nlinarith [one_div_pos.mpr hsqrt_n_pos]
    exact lt_of_lt_of_le hsqrt_lower hγ
  have hupper_lt : γ < algorithm.radius k / Real.sqrt (n : ℝ) := by
    exact (lt_div_iff₀ hsqrt_n_pos).2 hcontinue
  exact ⟨hgamma_gt_one, le_of_lt hupper_lt⟩

/-- Helper for Theorem 7.10: every iterate before the stopping time satisfies the Lemma 7.7
comparison bound for the one-step logarithmic potential. -/
theorem potentialStep_le_comparison_of_continuing
    (algorithm : SignAlg)
    (γ : ℝ) (hn : 1 ≤ n)
    (hγ : Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) ≤ γ)
    {k : ℕ}
    (hcontinue : γ * Real.sqrt (n : ℝ) < algorithm.radius k) :
    algorithm.potentialStep k ≤
      Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)) -
        (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) := by
  have hgamma_mem :=
    algorithm.gamma_mem_comparison_interval_of_continuing γ hn hγ hcontinue
  have hn_nat_pos : 0 < n := lt_of_lt_of_le Nat.succ_pos' hn
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hn_nat_pos)
  have hsqrt_lt : Real.sqrt (n : ℝ) < algorithm.radius k := by
    have hgamma_gt_one : 1 < γ := hgamma_mem.1
    have hscaled : Real.sqrt (n : ℝ) < γ * Real.sqrt (n : ℝ) := by
      nlinarith
    exact lt_trans hscaled hcontinue
  have hradius_sq : (n : ℝ) < algorithm.radius k ^ (2 : ℕ) := by
    have hsq : (Real.sqrt (n : ℝ)) ^ (2 : ℕ) < algorithm.radius k ^ (2 : ℕ) := by
      nlinarith [hsqrt_n_pos, hsqrt_lt]
    simpa [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)] using hsq
  -- Translate the owner-side continuing-step data into Lemma 7.7's diagonal comparison API.
  simpa [potentialStep, alpha, stepAlpha, radius] using
    ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison
      (algorithm k) (algorithm.matrix_isDiag k) (algorithm.currentMatrix k).2
      (algorithm.maximizer k) hradius_sq γ hgamma_mem

/-- Helper for Theorem 7.10: the displayed lower bound on `γ` makes the comparison drop
strictly positive. -/
theorem comparisonDrop_pos_of_lowerBound
    (γ : ℝ) (hn : 1 ≤ n)
    (hγ : Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) ≤ γ) :
    0 <
      ((γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) -
        Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ))) := by
  have hn_nat_pos : 0 < n := lt_of_lt_of_le Nat.succ_pos' hn
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast hn_nat_pos)
  have hgamma_gt_one : 1 < γ := by
    have hsqrt_lower : 1 < Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) := by
      rw [← Real.sqrt_one]
      apply Real.sqrt_lt_sqrt
      · positivity
      · nlinarith [one_div_pos.mpr hsqrt_n_pos]
    exact lt_of_lt_of_le hsqrt_lower hγ
  -- Lemma 7.7 gives the comparison term as a strictly negative number.
  have hneg := ellipsoidBoxGammaComparison_neg γ hgamma_gt_one
  linarith

/-- Helper for Theorem 7.10: every iterate before the stopping time satisfies the Lemma 7.7
comparison bound for the one-step logarithmic potential. -/
theorem potentialStep_le_neg_drop_of_lt_stoppingTime
    (algorithm : SignAlg)
    (γ : ℝ) (hn : 1 ≤ n)
    (hγ : Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) ≤ γ)
    (hTerminate : algorithm.Terminates γ)
    {k : ℕ}
    (hk : k < algorithm.stoppingTime hTerminate) :
    algorithm.potentialStep k ≤
      Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)) -
        (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) := by
  -- Before the first stopping time, the current iterate is still genuinely continuing.
  exact algorithm.potentialStep_le_comparison_of_continuing γ hn hγ
    (algorithm.threshold_lt_radius_of_lt_stoppingTime hTerminate hk)

/-- Helper for Theorem 7.10: before the stopping time, each recursive step decreases the
remaining logarithmic-volume budget by at least the uniform comparison drop. -/
theorem remainingLogVolumeBudget_succ_le_sub_drop_of_lt_stoppingTime
    (algorithm : SignAlg)
    (B γ : ℝ) (hn : 1 ≤ n)
    (hγ : Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) ≤ γ)
    (hTerminate : algorithm.Terminates γ)
    {k : ℕ}
    (hk : k < algorithm.stoppingTime hTerminate) :
    algorithm.remainingLogVolumeBudget B (k + 1) ≤
      algorithm.remainingLogVolumeBudget B k -
        ((γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) -
          Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ))) := by
  -- Rewrite the successor budget as the current budget plus the one-step potential.
  rw [algorithm.remainingLogVolumeBudget_succ]
  have hpotential :=
    algorithm.potentialStep_le_neg_drop_of_lt_stoppingTime γ hn hγ hTerminate hk
  linarith

/-- Helper for Theorem 7.10: telescoping the uniform drop along the continuing prefix bounds the
remaining logarithmic-volume budget at every index up to the stopping time. -/
theorem remainingLogVolumeBudget_le_initial_sub_mul_drop_upto_stoppingTime
    (algorithm : SignAlg)
    (B γ : ℝ) (hn : 1 ≤ n)
    (hγ : Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) ≤ γ)
    (hTerminate : algorithm.Terminates γ) :
    ∀ k : ℕ,
      k ≤ algorithm.stoppingTime hTerminate →
        algorithm.remainingLogVolumeBudget B k ≤
          B - (k : ℝ) *
            ((γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) -
              Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ))) := by
  intro k
  induction k with
  | zero =>
      intro _
      -- The telescoping estimate starts from the exact initial budget identity.
      simp
  | succ k ih =>
      intro hk
      have hk_lt : k < algorithm.stoppingTime hTerminate := Nat.lt_of_succ_le hk
      have hk_le : k ≤ algorithm.stoppingTime hTerminate := Nat.le_of_lt hk_lt
      have hstep :=
        algorithm.remainingLogVolumeBudget_succ_le_sub_drop_of_lt_stoppingTime
          B γ hn hγ hTerminate hk_lt
      have hprev := ih hk_le
      have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
        norm_num
      -- Combine the one-step descent with the induction hypothesis and rewrite the scalar cast.
      rw [hcast]
      linarith

/-- Helper for Theorem 7.10: the intrinsic Chapter 7 containments built into the sign-invariant
scheme imply that the complexity budget `n (log n + 2 log m)` stays nonnegative at every time. -/
theorem remainingLogVolumeBudget_nonneg_at_time
    (algorithm : SignAlg)
    (hn : 1 ≤ n) (T : ℕ) :
    0 ≤
      algorithm.remainingLogVolumeBudget
        ((n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ)))
        T := by
  let R : ℝ := (m : ℝ) * Real.sqrt (n : ℝ)
  have hmatrix0_pos : (algorithm 0).PosDef := by
    simpa [matrix_zero] using algorithm.initial_posDef
  have hcontain :
      centeredMatrixEllipsoid (algorithm T) 1 ⊆
        centeredMatrixEllipsoid (algorithm 0) R := by
    exact Set.Subset.trans
      (algorithm.unit_ellipsoid_subset_generatedSet T)
      algorithm.generatedSet_subset_initial_outer_ellipsoid
  have hR_nonneg : 0 ≤ R := by
    dsimp [R]
    positivity
  have hvol_right_lt_top :
      volume (centeredMatrixEllipsoid (algorithm 0) R) < ⊤ := by
    rw [centeredMatrixEllipsoid_volume (algorithm 0) hmatrix0_pos hR_nonneg]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top
  have hvol_mono :
      volume (centeredMatrixEllipsoid (algorithm T) 1) ≤
        volume (centeredMatrixEllipsoid (algorithm 0) R) :=
    measure_mono hcontain
  have hvol_mono_toReal :
      (volume (centeredMatrixEllipsoid (algorithm T) 1)).toReal ≤
        (volume (centeredMatrixEllipsoid (algorithm 0) R)).toReal :=
    ENNReal.toReal_mono hvol_right_lt_top.ne hvol_mono
  rw [centeredMatrixEllipsoidVolume_toReal (algorithm T) (algorithm.currentMatrix T).2
      (show (0 : ℝ) ≤ 1 by positivity),
    centeredMatrixEllipsoidVolume_toReal (algorithm 0) hmatrix0_pos hR_nonneg] at hvol_mono_toReal
  rw [closedBallVolume_toReal_eq_pow hn hR_nonneg] at hvol_mono_toReal
  have hball_one_pos : 0 < (volume (Metric.closedBall (0 : Eₙ) 1)).toReal := by
    exact ENNReal.toReal_pos (Metric.measure_closedBall_pos volume (0 : Eₙ) zero_lt_one).ne'
      measure_closedBall_lt_top.ne
  have hsqrt_le :
      Real.sqrt (Matrix.det (algorithm T)) ≤
        R ^ n * Real.sqrt (Matrix.det (algorithm 0)) := by
    have hcancel :
        Real.sqrt (Matrix.det (algorithm T)) *
            (volume (Metric.closedBall (0 : Eₙ) 1)).toReal ≤
          (R ^ n * Real.sqrt (Matrix.det (algorithm 0))) *
            (volume (Metric.closedBall (0 : Eₙ) 1)).toReal := by
      simpa [R, mul_assoc, mul_left_comm, mul_comm] using hvol_mono_toReal
    exact le_of_mul_le_mul_right hcancel hball_one_pos
  have hdetT_pos : 0 < Matrix.det (algorithm T) := (algorithm.currentMatrix T).2.det_pos
  have hdet0_pos : 0 < Matrix.det (algorithm 0) := hmatrix0_pos.det_pos
  have hsqrtT_pos : 0 < Real.sqrt (Matrix.det (algorithm T)) := by
    exact Real.sqrt_pos.mpr hdetT_pos
  have hsqrt0_pos : 0 < Real.sqrt (Matrix.det (algorithm 0)) := by
    exact Real.sqrt_pos.mpr hdet0_pos
  have hR_pos : 0 < R := by
    have hrhs_pos : 0 < R ^ n * Real.sqrt (Matrix.det (algorithm 0)) :=
      lt_of_lt_of_le hsqrtT_pos hsqrt_le
    by_cases hR0 : R = 0
    · have hn_pos : 0 < n := by
        exact_mod_cast hn
      simp [R, hR0, hn_pos.ne'] at hrhs_pos
    · exact lt_of_le_of_ne hR_nonneg (Ne.symm hR0)
  have hlog_sqrt_le :
      Real.log (Real.sqrt (Matrix.det (algorithm T))) ≤
        Real.log (R ^ n * Real.sqrt (Matrix.det (algorithm 0))) := by
    exact Real.log_le_log hsqrtT_pos hsqrt_le
  have hlog_expand :
      Real.log (R ^ n * Real.sqrt (Matrix.det (algorithm 0))) =
        (n : ℝ) * Real.log R + Real.log (Real.sqrt (Matrix.det (algorithm 0))) := by
    rw [Real.log_mul (pow_ne_zero n hR_pos.ne') hsqrt0_pos.ne', Real.log_pow]
  have hhalf :
      Real.log (Matrix.det (algorithm T)) / 2 ≤
        (n : ℝ) * Real.log R + Real.log (Matrix.det (algorithm 0)) / 2 := by
    rw [hlog_expand, Real.log_sqrt hdetT_pos.le, Real.log_sqrt hdet0_pos.le] at hlog_sqrt_le
    simpa using hlog_sqrt_le
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    exact Real.sqrt_pos.2 (by exact_mod_cast (lt_of_lt_of_le Nat.succ_pos' hn))
  have hbudget_rewrite :
      2 * (n : ℝ) * Real.log R =
        (n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ)) := by
    have hm_pos : 0 < (m : ℝ) := by
      exact_mod_cast m.pos
    have hlog_mul :
        Real.log R = Real.log (m : ℝ) + Real.log (Real.sqrt (n : ℝ)) := by
      dsimp [R]
      rw [Real.log_mul hm_pos.ne' hsqrt_n_pos.ne']
    have hlog_sqrt :
        2 * Real.log (Real.sqrt (n : ℝ)) = Real.log (n : ℝ) := by
      rw [Real.log_sqrt (show 0 ≤ (n : ℝ) by positivity)]
      ring
    calc
      2 * (n : ℝ) * Real.log R
          = 2 * (n : ℝ) * (Real.log (m : ℝ) + Real.log (Real.sqrt (n : ℝ))) := by
              rw [hlog_mul]
      _ = (n : ℝ) * (2 * Real.log (m : ℝ) + 2 * Real.log (Real.sqrt (n : ℝ))) := by
            ring
      _ = (n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ)) := by
            rw [hlog_sqrt]
            ring
  have hlogdet_upper :
      Real.log (Matrix.det (algorithm T)) - Real.log (Matrix.det (algorithm 0)) ≤
        (n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ)) := by
    have hupper_aux :
        Real.log (Matrix.det (algorithm T)) - Real.log (Matrix.det (algorithm 0)) ≤
          2 * (n : ℝ) * Real.log R := by
      linarith
    rw [hbudget_rewrite] at hupper_aux
    exact hupper_aux
  -- Convert the determinant-growth bound back into the remaining-budget formulation.
  change 0 ≤
    ((n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ)) -
      (Real.log (Matrix.det (algorithm T)) - Real.log (Matrix.det (algorithm 0))))
  exact sub_nonneg.mpr hlogdet_upper

/-- Helper for Theorem 7.10: the intrinsic Chapter 7 containments built into the sign-invariant
scheme imply that the complexity budget `n (log n + 2 log m)` stays nonnegative at the canonical
stopping time. Equivalently, `log det D_T - log det D₀ ≤ n (log n + 2 log m)` at the first
accepted iterate `T`. -/
theorem complexityBudget_nonneg_at_stoppingTime
    (algorithm : SignAlg)
    (γ : ℝ) (hn : 1 ≤ n)
    (hTerminate : algorithm.Terminates γ) :
    0 ≤
      algorithm.remainingLogVolumeBudget
        ((n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ)))
        (algorithm.stoppingTime hTerminate) := by
  -- The all-times budget bound can be specialized to the canonical first stopping time.
  simpa using
    algorithm.remainingLogVolumeBudget_nonneg_at_time hn (algorithm.stoppingTime hTerminate)

/-- Helper for Theorem 7.10: the lower bound on `γ` forces the sign-invariant rounding scheme to
terminate. -/
theorem terminates_of_gammaLowerBound
    (algorithm : SignAlg)
    (γ : ℝ) (hn : 1 ≤ n)
    (hγ : Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) ≤ γ) :
    algorithm.Terminates γ := by
  let drop : ℝ :=
    (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) -
      Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ))
  let B : ℝ := (n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ))
  have hdrop : 0 < drop := comparisonDrop_pos_of_lowerBound γ hn hγ
  by_contra hnot
  let T : ℕ := Nat.floor (drop⁻¹ * B) + 1
  have hcontinue : ∀ k : ℕ, γ * Real.sqrt (n : ℝ) < algorithm.radius k := by
    intro k
    by_contra hk
    exact hnot ⟨k, by simpa [stoppingCriterion] using (le_of_not_gt hk)⟩
  have hinitial : algorithm.remainingLogVolumeBudget B 0 ≤ B := by
    simp
  have hterminal : 0 ≤ algorithm.remainingLogVolumeBudget B T := by
    simpa [B, T] using algorithm.remainingLogVolumeBudget_nonneg_at_time hn T
  have hstep :
      ∀ k : ℕ, k < T →
        algorithm.remainingLogVolumeBudget B (k + 1) ≤
          algorithm.remainingLogVolumeBudget B k - drop := by
    intro k hk
    rw [algorithm.remainingLogVolumeBudget_succ]
    have hpotential :=
      algorithm.potentialStep_le_comparison_of_continuing γ hn hγ (hcontinue k)
    linarith
  have hbound :=
    stoppingTime_le_of_positive_drop
      (potential := algorithm.remainingLogVolumeBudget B)
      T B drop hdrop hinitial hterminal hstep
  have hfloor : drop⁻¹ * B < (T : ℝ) := by
    simpa [T] using Nat.lt_floor_add_one (drop⁻¹ * B)
  -- The floor-chosen time is strictly larger than `drop⁻¹ * B`, contradicting the telescoped bound.
  linarith

/-- Theorem 7.10: assume `n ≥ 1`, let `m : ℕ+`, and assume
`γ ≥ √(1 + 1 / √n)`. Then the Chapter 7 sign-invariant recursive rounding scheme `(7.2.18)`
encoded by `algorithm` terminates after at most
`[(γ² - 1) / γ² - log (1 + (γ² - 1) / γ²)]⁻¹ n (log n + 2 log m)` iterations. -/
theorem stoppingTime_le
    (algorithm : SignAlg)
    (γ : ℝ) (hn : 1 ≤ n)
    (hγ : Real.sqrt (1 + 1 / Real.sqrt (n : ℝ)) ≤ γ)
    :
    ∃ hTerminate : algorithm.Terminates γ,
      (algorithm.stoppingTime hTerminate : ℝ) ≤
        (((γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) -
            Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)))⁻¹ *
          (n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ))) := by
  let drop : ℝ :=
    (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) -
      Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ))
  let B : ℝ := (n : ℝ) * (Real.log (n : ℝ) + 2 * Real.log (m : ℝ))
  have hTerminate : algorithm.Terminates γ :=
    algorithm.terminates_of_gammaLowerBound γ hn hγ
  refine ⟨hTerminate, ?_⟩
  have hdrop : 0 < drop := comparisonDrop_pos_of_lowerBound γ hn hγ
  have hinitial : algorithm.remainingLogVolumeBudget B 0 ≤ B := by
    simp
  have hterminal : 0 ≤
      algorithm.remainingLogVolumeBudget B (algorithm.stoppingTime hTerminate) := by
    simpa [B] using
      algorithm.remainingLogVolumeBudget_nonneg_at_time hn (algorithm.stoppingTime hTerminate)
  have hstep :
      ∀ k : ℕ, k < algorithm.stoppingTime hTerminate →
        algorithm.remainingLogVolumeBudget B (k + 1) ≤
          algorithm.remainingLogVolumeBudget B k - drop := by
    intro k hk
    rw [algorithm.remainingLogVolumeBudget_succ]
    have hpotential :=
      algorithm.potentialStep_le_neg_drop_of_lt_stoppingTime γ hn hγ hTerminate hk
    linarith
  -- Apply the generic positive-drop stopping bound at the canonical first stopping time.
  simpa [drop, B, mul_assoc] using
    (stoppingTime_le_of_positive_drop
      (potential := algorithm.remainingLogVolumeBudget B)
      (algorithm.stoppingTime hTerminate) B drop hdrop hinitial hterminal hstep)

end SignInvariantRoundingAlgorithm

end
