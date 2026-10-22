/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Calculus.LocalExtr.LineDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Algorithm_9_7_1

open Matrix

noncomputable section

-- Domain-style sampling for this file:
-- * primary domain: linear-program primal-dual interior-point central-path data
-- * sampled Chapter 9 owners:
--   - `PrimalDualState`, `IsStrictlyPositive`, and `strictlyFeasibleSet`
--     from `Algorithm_9_7_1`
--   - the residual-map formulation `residualCentralPath` from `Definition_9_7_extra_2`
-- * owner decision:
--   - core/canonical owner: `strictlyFeasibleSet A b c` on `PrimalDualState n m`
--   - source-facing bridge here: `IsCentralPathPoint A b c τ point`
-- * primitive data already owned upstream: affine primal-dual feasibility and strict positivity
-- * derived data added here: the constant complementarity condition `x i * s i = τ`

section

variable {n m : ℕ}

local notation "PrimalPoint" => EuclideanSpace ℝ (Fin n)
local notation "DualPoint" => EuclideanSpace ℝ (Fin m)
local notation "ConstraintMatrix" => Matrix (Fin m) (Fin n) ℝ

/-- A triple `(x, λ, s)` is a `τ`-central-path point when it satisfies the affine primal-dual
equations together with the coordinatewise complementarity condition `x i * s i = τ` and strict
positivity of `x` and `s`. -/
def IsCentralPathPoint
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint) (τ : ℝ)
    (point : PrimalDualState n m) : Prop :=
  point ∈ strictlyFeasibleSet A b c ∧
    ∀ i, point.x i * point.s i = τ

/-- The residual map whose vanishing and constant complementarity vector encode the central-path
system. It packages the dual residual, the primal residual, and the coordinatewise products
`x i * s i`. -/
def centralResidualMap
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    (point : PrimalDualState n m) : PrimalDualState n m where
  x := WithLp.toLp 2 <| A.transpose.mulVec point.lam + point.s - c
  lam := WithLp.toLp 2 <| A.mulVec point.x - b
  s := WithLp.toLp 2 <| fun i ↦ point.x i * point.s i

@[simp] theorem centralResidualMap_x_apply
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    (point : PrimalDualState n m) (i : Fin n) :
    (centralResidualMap A b c point).x i =
      (A.transpose.mulVec point.lam) i + point.s i - c i :=
  rfl

@[simp] theorem centralResidualMap_lam_apply
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    (point : PrimalDualState n m) (i : Fin m) :
    (centralResidualMap A b c point).lam i =
      (A.mulVec point.x) i - b i :=
  rfl

@[simp] theorem centralResidualMap_s_apply
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    (point : PrimalDualState n m) (i : Fin n) :
    (centralResidualMap A b c point).s i = point.x i * point.s i :=
  rfl

/-- Definition component of Chapter09 Definition 9.7-extra-1: the central path `𝒞` of the
linear-program data
`(A, b, c)` is the set of primal-dual-slack triples `(x, λ, s)` for which there exists some
parameter `τ > 0` such that `(x, λ, s)` is a `τ`-central-path point. -/
def centralPath
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint) : Set (PrimalDualState n m) :=
  {point | ∃ τ > 0, IsCentralPathPoint A b c τ point}

#print axioms centralPath

/-- Membership in `centralPath A b c` means that the point satisfies the `τ`-central-path system
for some positive parameter `τ`. -/
theorem mem_centralPath_iff
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint) (point : PrimalDualState n m) :
    point ∈ centralPath A b c ↔ ∃ τ > 0, IsCentralPathPoint A b c τ point := by
  rfl

/-- Helper for Chapter09 Definition 9.7-extra-1: if two positive pairs
`(x₁, s₁)` and `(x₂, s₂)` have the same product `τ`, then the negative of the
mixed difference term is the scaled square `(τ * (x₁ - x₂)^2) / (x₁ * x₂)`. -/
lemma negSubMulSub_eq_tau_mul_sq_div
    {τ x₁ x₂ s₁ s₂ : ℝ}
    (hx₁ : 0 < x₁) (hx₂ : 0 < x₂)
    (h₁ : x₁ * s₁ = τ) (h₂ : x₂ * s₂ = τ) :
    -((x₁ - x₂) * (s₁ - s₂)) = τ * (x₁ - x₂)^2 / (x₁ * x₂) := by
  have hx₁ne : x₁ ≠ 0 := hx₁.ne'
  have hx₂ne : x₂ ≠ 0 := hx₂.ne'
  -- Rewrite each slack coordinate as `τ / x` before clearing denominators.
  have hs₁ : s₁ = τ / x₁ := by
    apply (eq_div_iff hx₁ne).2
    simpa [mul_comm] using h₁
  have hs₂ : s₂ = τ / x₂ := by
    apply (eq_div_iff hx₂ne).2
    simpa [mul_comm] using h₂
  rw [hs₁, hs₂]
  field_simp [hx₁ne, hx₂ne]
  ring

/-- Helper for Chapter09 Definition 9.7-extra-1: if every positive `τ` admits a unique
`τ`-central-path point, then specializing to `τ = 1` already yields a strictly feasible point. -/
lemma strictlyFeasibleSet_nonempty_of_forall_existsUniqueCentral
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint) :
    (∀ τ : ℝ, 0 < τ → ∃! point : PrimalDualState n m, IsCentralPathPoint A b c τ point) →
      (strictlyFeasibleSet A b c).Nonempty := by
  intro hCentral
  -- The `τ = 1` witness is automatically strictly feasible.
  rcases hCentral 1 zero_lt_one with ⟨point, hPoint, _⟩
  exact ⟨point, hPoint.1⟩

/-- Helper for Chapter09 Definition 9.7-extra-1: two `τ`-central-path points coincide once
`λ ↦ Aᵀ λ` is injective. The affine equations force an orthogonality relation, and the common
complementarity value then collapses each coordinate difference. -/
lemma centralPathPoint_eq_of_sameTau
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    (τ : ℝ) (p q : PrimalDualState n m)
    (hAT : Function.Injective A.transpose.mulVec)
    (hp : IsCentralPathPoint A b c τ p)
    (hq : IsCentralPathPoint A b c τ q) :
    p = q := by
  rcases hp with ⟨hpMem, hpTau⟩
  rcases hq with ⟨hqMem, hqTau⟩
  rcases (mem_strictlyFeasibleSet_iff A b c p).1 hpMem with
    ⟨hpAx, hpDual, hpPosx, hpPoss⟩
  rcases (mem_strictlyFeasibleSet_iff A b c q).1 hqMem with
    ⟨hqAx, hqDual, hqPosx, hqPoss⟩
  -- Subtract the primal feasibility equations to get a zero right-hand side.
  have hAx : A.mulVec (fun i : Fin n ↦ p.x i - q.x i) = 0 := by
    ext i
    simpa [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib] using
      sub_eq_zero.mpr ((congr_fun hpAx i).trans (congr_fun hqAx i).symm)
  -- Subtract the dual feasibility equations to express the slack difference through `Aᵀ`.
  have hsumEq : A.transpose.mulVec p.lam + p.s = A.transpose.mulVec q.lam + q.s := by
    rw [hpDual, hqDual]
  have hATsub :
      A.transpose.mulVec (fun i : Fin m ↦ p.lam i - q.lam i) =
        fun i : Fin n ↦ q.s i - p.s i := by
    ext i
    have hi : (∑ x, A x i * p.lam x) + p.s i = (∑ x, A x i * q.lam x) + q.s i := by
      simpa [Matrix.mulVec, dotProduct] using congr_fun hsumEq i
    simpa [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib] using
      (show
        (∑ x, A x i * p.lam x) - (∑ x, A x i * q.lam x) = q.s i - p.s i by
        linarith)
  have hsSub :
      (fun i : Fin n ↦ p.s i - q.s i) =
        fun i : Fin n ↦ -((A.transpose.mulVec (fun i : Fin m ↦ p.lam i - q.lam i)) i) := by
    funext i
    have hi := congr_fun hATsub i
    linarith
  -- Pair the dual-difference identity with the primal-difference identity via dot products.
  have hdotZero :
      ((fun i : Fin n ↦ p.x i - q.x i) ⬝ᵥ fun i : Fin n ↦ p.s i - q.s i) = 0 := by
    calc
      ((fun i : Fin n ↦ p.x i - q.x i) ⬝ᵥ fun i : Fin n ↦ p.s i - q.s i)
          = ((fun i : Fin n ↦ p.x i - q.x i) ⬝ᵥ
              fun i : Fin n ↦
                -((A.transpose.mulVec (fun i : Fin m ↦ p.lam i - q.lam i)) i)) := by
              rw [hsSub]
      _ = -(((fun i : Fin n ↦ p.x i - q.x i) ⬝ᵥ
            (A.transpose.mulVec (fun i : Fin m ↦ p.lam i - q.lam i)))) := by
            simp [dotProduct]
      _ = -((A.mulVec (fun i : Fin n ↦ p.x i - q.x i)) ⬝ᵥ
            (fun i : Fin m ↦ p.lam i - q.lam i)) := by
            rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = -(0 ⬝ᵥ (fun i : Fin m ↦ p.lam i - q.lam i)) := by
            rw [hAx]
      _ = 0 := by
            simp
  have hsumZero : ∑ i, -((p.x i - q.x i) * (p.s i - q.s i)) = 0 := by
    simpa [dotProduct] using congrArg Neg.neg hdotZero
  -- Each coordinate contribution is nonnegative after the sign flip.
  have htermNonneg : ∀ i : Fin n, 0 ≤ -((p.x i - q.x i) * (p.s i - q.s i)) := by
    intro i
    have hτpos : 0 < τ := by
      nlinarith [hpPosx i, hpPoss i, hpTau i]
    rw [negSubMulSub_eq_tau_mul_sq_div (hpPosx i) (hqPosx i) (hpTau i) (hqTau i)]
    exact div_nonneg (mul_nonneg hτpos.le (sq_nonneg _))
      (mul_nonneg (hpPosx i).le (hqPosx i).le)
  have htermZero : ∀ i : Fin n, -((p.x i - q.x i) * (p.s i - q.s i)) = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ ↦ htermNonneg j).1
      hsumZero i (Finset.mem_univ i)
  -- The coordinatewise square formula forces `x` to agree componentwise.
  have hxEq : p.x = q.x := by
    ext i
    have hFormula := negSubMulSub_eq_tau_mul_sq_div
      (hpPosx i) (hqPosx i) (hpTau i) (hqTau i)
    have hzeroDiv : τ * (p.x i - q.x i)^2 / (p.x i * q.x i) = 0 := by
      simpa [hFormula] using htermZero i
    have hnumZero : τ * (p.x i - q.x i)^2 = 0 := by
      exact (div_eq_zero_iff.mp hzeroDiv).resolve_right
        (mul_ne_zero (hpPosx i).ne' (hqPosx i).ne')
    have hτpos : 0 < τ := by
      nlinarith [hpPosx i, hpPoss i, hpTau i]
    have hsqZero : (p.x i - q.x i)^2 = 0 := by
      exact (eq_zero_or_eq_zero_of_mul_eq_zero hnumZero).resolve_left hτpos.ne'
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsqZero)
  -- Once `x` is fixed, the common product `x_i s_i = τ` fixes `s` as well.
  have hsEq : p.s = q.s := by
    ext i
    have hxi : p.x i = q.x i := by
      simpa using congrArg (fun x : PrimalPoint ↦ x i) hxEq
    have hmul : p.x i * p.s i = p.x i * q.s i := by
      calc
        p.x i * p.s i = τ := hpTau i
        _ = q.x i * q.s i := (hqTau i).symm
        _ = p.x i * q.s i := by rw [← hxi]
    exact mul_left_cancel₀ (hpPosx i).ne' hmul
  -- Injectivity of `λ ↦ Aᵀ λ` recovers the multiplier component.
  have hlamEqFun : p.lam.ofLp = q.lam.ofLp := by
    apply hAT
    simpa [hsEq] using hsumEq
  have hlamEq : p.lam = q.lam := by
    ext i
    exact congr_fun hlamEqFun i
  cases p
  cases q
  simp at hxEq hlamEq hsEq
  simp [hxEq, hlamEq, hsEq]

/-- Helper for Chapter09 Definition 9.7-extra-1: a vector orthogonal to every feasible direction
`d` with `A.mulVec d = 0` lies in the range of `Aᵀ`. -/
lemma mem_range_transpose_of_barrierOrthogonalKernel
    (A : ConstraintMatrix) (g : PrimalPoint)
    (hg : ∀ d : PrimalPoint, A.mulVec d = 0 → g ⬝ᵥ d = 0) :
    ∃ lam : DualPoint, A.transpose.mulVec lam = g := by
  let T : PrimalPoint →ₗ[ℝ] DualPoint := Matrix.toEuclideanLin A
  have hgOrth : g ∈ T.kerᗮ := by
    rw [Submodule.mem_orthogonal']
    intro d hd
    have hd0 : A.mulVec d = 0 := by
      simpa [T, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using hd
    -- Convert the kernel orthogonality goal back to the dot product used by the barrier route.
    simpa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] using hg d hd0
  rw [LinearMap.orthogonal_ker] at hgOrth
  have hadj : LinearMap.adjoint T = Matrix.toEuclideanLin A.transpose := by
    dsimp [T]
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
  rcases hgOrth with ⟨lam, hlam⟩
  refine ⟨lam, ?_⟩
  -- The Euclidean linear map associated to `Aᵀ` is exactly `A.transpose.mulVec`.
  rw [hadj] at hlam
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using congrArg WithLp.ofLp hlam

/-- Helper for Chapter09 Definition 9.7-extra-1: once a positive primal feasible point `x`
produces a transpose-range certificate for `c - τ / x`, one can reconstruct a `τ`-central-path
point by defining the slack coordinates as `s i = τ / x i`. -/
lemma exists_centralPathPoint_of_primalFeasiblePoint_and_transposeRange
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint) {τ : ℝ}
    (hτ : 0 < τ) {x : PrimalPoint}
    (hxA : A.mulVec x = b) (hxPos : IsStrictlyPositive x)
    (hRange : ∃ lam : DualPoint, A.transpose.mulVec lam = fun i ↦ c i - τ / x i) :
    ∃ point : PrimalDualState n m, IsCentralPathPoint A b c τ point := by
  rcases hRange with ⟨lam, hlam⟩
  let s : PrimalPoint := WithLp.toLp 2 <| fun i ↦ τ / x i
  let point : PrimalDualState n m := ⟨x, lam, s⟩
  have hsPos : IsStrictlyPositive s := by
    intro i
    simpa [s] using div_pos hτ (hxPos i)
  refine ⟨point, ?_⟩
  constructor
  · rw [mem_strictlyFeasibleSet_iff]
    refine ⟨hxA, ?_, hxPos, hsPos⟩
    -- The transpose-range witness is exactly the dual-feasibility equation for `point`.
    ext i
    have hi := congr_fun hlam i
    simp [point, s] at hi ⊢
    linarith
  · intro i
    have hxi : x i ≠ 0 := (hxPos i).ne'
    -- The chosen slack `s i = τ / x i` enforces the constant complementarity product.
    calc
      point.x i * point.s i = x i * (τ / x i) := by
        simp [point, s]
      _ = τ := by
        field_simp [hxi]

/-- Helper for Chapter09 Definition 9.7-extra-1: on the affine slice `A.mulVec x = b`, a strict
feasible witness rewrites the linear term `c ⬝ᵥ x` as a constant part `z0.lam ⬝ᵥ b` plus the slack
term `z0.s ⬝ᵥ x`. -/
lemma dotProduct_eq_strictFeasible_linearTerm
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    {z0 : PrimalDualState n m} (hz0 : z0 ∈ strictlyFeasibleSet A b c)
    {x : PrimalPoint} (hxA : A.mulVec x = b) :
    c ⬝ᵥ x = z0.lam ⬝ᵥ b + z0.s ⬝ᵥ x := by
  rcases (mem_strictlyFeasibleSet_iff A b c z0).1 hz0 with ⟨_, hz0Dual, _, _⟩
  -- Rewrite `c` through the strict-feasible dual equation, then move `Aᵀ` across the dot product.
  calc
    c ⬝ᵥ x = (A.transpose.mulVec z0.lam) ⬝ᵥ x + z0.s ⬝ᵥ x := by
      rw [← hz0Dual, add_dotProduct]
    _ = x ⬝ᵥ (A.transpose.mulVec z0.lam) + z0.s ⬝ᵥ x := by
      rw [dotProduct_comm]
    _ = (A.mulVec x) ⬝ᵥ z0.lam + z0.s ⬝ᵥ x := by
      rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    _ = z0.lam ⬝ᵥ b + z0.s ⬝ᵥ x := by
      rw [hxA, dotProduct_comm]

/-- Helper for Chapter09 Definition 9.7-extra-1: the affine primal slice used in the
logarithmic-barrier existence route. -/
def primalFeasibleSlice
    (A : ConstraintMatrix) (b : DualPoint) : Set PrimalPoint :=
  {x | A.mulVec x = b ∧ IsStrictlyPositive x}

/-- Helper for Chapter09 Definition 9.7-extra-1: the primal logarithmic-barrier objective on
the affine slice `A x = b`. -/
def primalBarrierObjective
    (τ : ℝ) (c : PrimalPoint) (x : PrimalPoint) : ℝ :=
  c.ofLp ⬝ᵥ x.ofLp - τ * ∑ i, Real.log (x i)

/-- Helper for Chapter09 Definition 9.7-extra-1: the compact coordinate box used to trap a
barrier sublevel. -/
def primalCoordinateBox
    (ℓ u : Fin n → ℝ) : Set PrimalPoint :=
  {x | ∀ i, x i ∈ Set.Icc (ℓ i) (u i)}

/-- Helper for Chapter09 Definition 9.7-extra-1: the barrier sublevel through a strict-feasible
witness `z0.x`. -/
def primalBarrierSublevel
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    (τ : ℝ) (z0 : PrimalDualState n m) : Set PrimalPoint :=
  {x |
    x ∈ primalFeasibleSlice A b ∧
      primalBarrierObjective τ c x ≤ primalBarrierObjective τ c z0.x}

/-- Helper for Chapter09 Definition 9.7-extra-1: on the affine slice `A x = b`, the primal
barrier objective splits into the strict-feasible constant `z0.lam ⬝ᵥ b` plus the scalar barrier
sum with coefficients `z0.s i`. -/
lemma primalBarrierObjective_eq_strictFeasibleBarrierSum
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    {τ : ℝ} {z0 : PrimalDualState n m} (hz0 : z0 ∈ strictlyFeasibleSet A b c)
    {x : PrimalPoint} (hxA : A.mulVec x = b) :
    primalBarrierObjective τ c x =
      z0.lam ⬝ᵥ b + ∑ i, (z0.s i * x i - τ * Real.log (x i)) := by
  -- Rewrite the linear term `c ⬝ᵥ x` through the strict-feasible dual witness.
  rw [primalBarrierObjective, dotProduct_eq_strictFeasible_linearTerm A b c hz0 hxA, dotProduct]
  -- Then regroup the finite sum into the barrier summands coordinatewise.
  have hdot : z0.s ⬝ᵥ x = ∑ i, z0.s i * x i := by
    rw [dotProduct]
  calc
    z0.lam ⬝ᵥ b + z0.s ⬝ᵥ x - τ * ∑ i, Real.log (x i)
        = z0.lam ⬝ᵥ b + (z0.s ⬝ᵥ x - τ * ∑ i, Real.log (x i)) := by ring
    _ = z0.lam ⬝ᵥ b + (∑ i, z0.s i * x i - τ * ∑ i, Real.log (x i)) := by
          rw [hdot]
    _ = z0.lam ⬝ᵥ b + ∑ i, (z0.s i * x i - τ * Real.log (x i)) := by
          congr 1
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Helper for Chapter09 Definition 9.7-extra-1: the coordinate box on `PrimalPoint` is the
image of the ordinary function-space box under `WithLp.toLp 2`. -/
lemma primalCoordinateBox_eq_image
    (ℓ u : Fin n → ℝ) :
    primalCoordinateBox ℓ u = WithLp.toLp 2 '' Set.univ.pi (fun i => Set.Icc (ℓ i) (u i)) := by
  ext x
  constructor
  · intro hx
    refine ⟨x.ofLp, ?_, ?_⟩
    · intro i hi
      exact hx i
    · simp
  · rintro ⟨y, hy, rfl⟩
    intro i
    exact hy i (by simp)

/-- Helper for Chapter09 Definition 9.7-extra-1: every coordinate box is compact because it is
the continuous image of a compact function-space product of closed intervals. -/
lemma primalCoordinateBox_isCompact
    (ℓ u : Fin n → ℝ) :
    IsCompact (primalCoordinateBox ℓ u) := by
  rw [primalCoordinateBox_eq_image]
  have hcont : Continuous (WithLp.toLp 2 : (Fin n → ℝ) → PrimalPoint) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).symm.continuous
  exact (isCompact_univ_pi fun i => isCompact_Icc).image_of_continuousOn hcont.continuousOn

/-- Helper for Chapter09 Definition 9.7-extra-1: the scalar barrier term
`t ↦ a * t - τ * log t` is bounded below by its value at the minimizer `τ / a`. -/
lemma scalarLinearMinusLog_lowerBound
    {a τ t : ℝ} (ha : 0 < a) (hτ : 0 < τ) (ht : 0 < t) :
    τ * (1 + Real.log (a / τ)) ≤ a * t - τ * Real.log t := by
  have hu : 0 < a * t / τ := by
    positivity
  have hlog : Real.log (a * t / τ) ≤ a * t / τ - 1 := Real.log_le_sub_one_of_pos hu
  have hsplit : Real.log (a * t / τ) = Real.log (a / τ) + Real.log t := by
    have hrew : a * t / τ = (a / τ) * t := by
      field_simp [hτ.ne']
    rw [hrew, Real.log_mul (div_pos ha hτ).ne' ht.ne']
  rw [hsplit] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog hτ.le
  have hright : τ * (a * t / τ - 1) = a * t - τ := by
    field_simp [hτ.ne']
  rw [hright] at hmul
  nlinarith

/-- Helper for Chapter09 Definition 9.7-extra-1: every scalar sublevel of the barrier term
`t ↦ a * t - τ * log t` with `a, τ > 0` is trapped in a positive closed interval. The lower bound
comes from `log t → -∞` as `t → 0+`, while the upper bound uses the global estimate
`log t ≤ ε t - 1 - log ε`. -/
lemma scalarLinearMinusLog_sublevel_subset_Icc
    {a τ M : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
    ∃ ℓ u : ℝ, 0 < ℓ ∧
      ∀ {t : ℝ}, 0 < t → a * t - τ * Real.log t ≤ M → t ∈ Set.Icc ℓ u := by
  have hlogSmall :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), Real.log t < -((|M| + 1) / τ) := by
    exact Real.tendsto_log_nhdsGT_zero.eventually_lt_atBot _
  rcases Metric.mem_nhdsWithin_iff.1 hlogSmall with ⟨δ, hδ, hδlog⟩
  let ε : ℝ := a / (2 * τ)
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  let K : ℝ := τ * (1 + Real.log ε)
  let u : ℝ := (|M| + |K| + 1) / (a / 2)
  refine ⟨δ / 2, u, by positivity, ?_⟩
  intro t ht hsub
  have htLower : δ / 2 ≤ t := by
    by_contra hlt
    have htBall : t ∈ Metric.ball (0 : ℝ) δ := by
      have hAbs : |t| < δ := by
        simpa [abs_of_pos ht] using (show t < δ by linarith)
      simpa [Metric.mem_ball, Real.dist_eq] using hAbs
    have htLog : Real.log t < -((|M| + 1) / τ) := hδlog ⟨htBall, ht⟩
    -- Near `0+`, the logarithmic term dominates and forces the barrier above the target level.
    have hlarge : M < a * t - τ * Real.log t := by
      have hnonneg : 0 ≤ a * t := by positivity
      have hlogPart : |M| + 1 < -τ * Real.log t := by
        have htLog' : Real.log t < (-(|M| + 1)) / τ := by
          have hrewrite : -((|M| + 1) / τ) = (-(|M| + 1)) / τ := by ring
          exact hrewrite ▸ htLog
        have hmul : τ * Real.log t < -(|M| + 1) := by
          simpa [mul_comm] using (lt_div_iff₀ hτ).1 htLog'
        linarith
      linarith [le_abs_self M, hnonneg, hlogPart]
    linarith
  have hlogLinear : Real.log t ≤ ε * t - 1 - Real.log ε := by
    have hεt : 0 < ε * t := mul_pos hε ht
    have hscaled : Real.log (ε * t) ≤ ε * t - 1 := Real.log_le_sub_one_of_pos hεt
    have hsplit : Real.log (ε * t) = Real.log ε + Real.log t := by
      rw [Real.log_mul hε.ne' ht.ne']
    linarith
  -- Away from `0`, the barrier grows at least linearly because the logarithm is sublinear.
  have hbarrierLower : a / 2 * t + K ≤ a * t - τ * Real.log t := by
    have hεmul : τ * ε = a / 2 := by
      dsimp [ε]
      field_simp [hτ.ne']
    have haEq : a = 2 * τ * ε := by
      nlinarith [hεmul]
    calc
      a / 2 * t + K = τ * ε * t + τ * (1 + Real.log ε) := by
        dsimp [K]
        rw [← hεmul]
      _ = a * t - τ * (ε * t - 1 - Real.log ε) := by
        rw [haEq]
        ring
      _ ≤ a * t - τ * Real.log t := by
        nlinarith [hlogLinear, hτ]
  have hcore : a / 2 * t ≤ |M| + |K| := by
    have hMK : a / 2 * t + K ≤ M := le_trans hbarrierLower hsub
    have hMabs : M ≤ |M| := le_abs_self M
    have hKabs : -K ≤ |K| := neg_le_abs K
    linarith
  have htUpper : t ≤ u := by
    have hhalf : 0 < a / 2 := by positivity
    have hcore' : a / 2 * t ≤ |M| + |K| + 1 := by linarith
    exact (le_div_iff₀ hhalf).2 (by simpa [mul_comm] using hcore')
  exact ⟨htLower, htUpper⟩

/-- Helper for Chapter09 Definition 9.7-extra-1: the logarithmic-barrier objective is continuous
on any coordinate box whose lower bounds stay strictly positive. -/
lemma primalBarrierObjective_continuousOn_box
    (τ : ℝ) (c : PrimalPoint) {ℓ u : Fin n → ℝ}
    (hℓ : ∀ i, 0 < ℓ i) :
    ContinuousOn (primalBarrierObjective τ c) (primalCoordinateBox ℓ u) := by
  classical
  have hcoordCont : ∀ i : Fin n, Continuous (fun x : PrimalPoint => x.ofLp i) := by
    intro i
    exact (continuous_apply i).comp (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n => ℝ))
  have hlinear :
      ContinuousOn (fun x : PrimalPoint => c.ofLp ⬝ᵥ x.ofLp) (primalCoordinateBox ℓ u) := by
    simpa [dotProduct] using
      (continuousOn_finsetSum Finset.univ fun i _ =>
        ((continuous_const.mul (hcoordCont i)).continuousOn :
          ContinuousOn (fun x : PrimalPoint => c.ofLp i * x.ofLp i) (primalCoordinateBox ℓ u)))
  have hlogsum :
      ContinuousOn (fun x : PrimalPoint => ∑ i, Real.log (x.ofLp i)) (primalCoordinateBox ℓ u) := by
    refine continuousOn_finsetSum Finset.univ ?_
    intro i _
    refine (Real.continuousOn_log.comp (hcoordCont i).continuousOn ?_)
    intro x hx
    exact (ne_of_gt (lt_of_lt_of_le (hℓ i) (hx i).1))
  -- The barrier objective is the difference of the continuous linear term and the log-sum term.
  change ContinuousOn
      (fun x : PrimalPoint => c.ofLp ⬝ᵥ x.ofLp - τ * ∑ i, Real.log (x.ofLp i))
      (primalCoordinateBox ℓ u)
  exact hlinear.sub (continuousOn_const.mul hlogsum)

/-- Helper for Chapter09 Definition 9.7-extra-1: a strict-feasible witness turns the primal
barrier sublevel through `z0.x` into a compact coordinate box. -/
lemma primalBarrierSublevel_subset_box
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    {τ : ℝ} {z0 : PrimalDualState n m} (hz0 : z0 ∈ strictlyFeasibleSet A b c)
    (hτ : 0 < τ) :
    ∃ ℓ u : Fin n → ℝ, (∀ i, 0 < ℓ i) ∧
      primalBarrierSublevel A b c τ z0 ⊆ primalCoordinateBox ℓ u := by
  classical
  rcases (mem_strictlyFeasibleSet_iff A b c z0).1 hz0 with
    ⟨_, _, _, hz0Poss⟩
  let lower : Fin n → ℝ := fun i ↦ τ * (1 + Real.log (z0.s i / τ))
  let bound : Fin n → ℝ := fun i ↦
    primalBarrierObjective τ c z0.x - z0.lam ⬝ᵥ b -
      Finset.sum (Finset.univ.erase i) lower
  have hlower :
      ∀ i : Fin n, ∀ {t : ℝ}, 0 < t → lower i ≤ z0.s i * t - τ * Real.log t := by
    intro i t ht
    simpa [lower] using scalarLinearMinusLog_lowerBound (hz0Poss i) hτ ht
  have hinterval :
      ∀ i : Fin n,
        ∃ ℓ u : ℝ, 0 < ℓ ∧
          ∀ {t : ℝ}, 0 < t → z0.s i * t - τ * Real.log t ≤ bound i → t ∈ Set.Icc ℓ u := by
    intro i
    simpa [bound] using scalarLinearMinusLog_sublevel_subset_Icc (hz0Poss i) hτ
  choose ℓ u hℓ hbound using hinterval
  refine ⟨ℓ, u, hℓ, ?_⟩
  intro x hx
  rcases hx with ⟨hxSlice, hxObj⟩
  rcases hxSlice with ⟨hxA, hxPos⟩
  intro i
  let term : Fin n → ℝ := fun j ↦ z0.s j * x j - τ * Real.log (x j)
  have hsumUpper :
      z0.lam ⬝ᵥ b + ∑ j, term j ≤ primalBarrierObjective τ c z0.x := by
    -- Rewrite the barrier objective on the affine slice to expose the scalar summands.
    simpa [term, primalBarrierObjective_eq_strictFeasibleBarrierSum A b c hz0 hxA] using hxObj
  have hsumSplit :
      ∑ j, term j = term i + Finset.sum (Finset.univ.erase i) term := by
    simpa [term, add_comm] using
      (Finset.sum_erase_add (s := Finset.univ) (f := term) (a := i)
        (by simp : i ∈ Finset.univ)).symm
  have hothersLower :
      Finset.sum (Finset.univ.erase i) lower ≤ Finset.sum (Finset.univ.erase i) term := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hlower j (hxPos j)
  have htermUpper :
      z0.s i * x i - τ * Real.log (x i) ≤ bound i := by
    have hsumUpper' := hsumUpper
    rw [hsumSplit] at hsumUpper'
    have hsumUpper'' :
        z0.lam ⬝ᵥ b + (term i + Finset.sum (Finset.univ.erase i) term) ≤
          primalBarrierObjective τ c z0.x := hsumUpper'
    -- Lower-bounding the other coordinates isolates the `i`-th scalar barrier term.
    have hrest :
        z0.lam ⬝ᵥ b + (term i + Finset.sum (Finset.univ.erase i) lower) ≤
          primalBarrierObjective τ c z0.x := by
      linarith
    have htermUpper' : term i ≤ bound i := by
      linarith
    simpa [term] using htermUpper'
  exact hbound i (hxPos i) htermUpper

/-- Helper for Chapter09 Definition 9.7-extra-1: the barrier sublevel through a strict-feasible
witness is compact once it is trapped in a positive coordinate box. -/
lemma primalBarrierSublevel_isCompact
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    {τ : ℝ} {z0 : PrimalDualState n m} (hz0 : z0 ∈ strictlyFeasibleSet A b c)
    (hτ : 0 < τ) :
    IsCompact (primalBarrierSublevel A b c τ z0) := by
  classical
  rcases primalBarrierSublevel_subset_box A b c hz0 hτ with ⟨ℓ, u, hℓ, hsub⟩
  let box : Set PrimalPoint := primalCoordinateBox ℓ u
  let objSet : Set PrimalPoint :=
    {x | primalBarrierObjective τ c x ≤ primalBarrierObjective τ c z0.x}
  let affineSet : Set PrimalPoint := {x | A.mulVec x = b}
  have hboxCompact : IsCompact box := primalCoordinateBox_isCompact ℓ u
  have hboxClosed : IsClosed box := hboxCompact.isClosed
  have hobjClosed : IsClosed (box ∩ objSet) := by
    -- The barrier objective is continuous on the positive box, so the box-restricted sublevel is
    -- closed there.
    simpa [box, objSet, Set.preimage] using
      (primalBarrierObjective_continuousOn_box τ c hℓ).preimage_isClosed_of_isClosed
        hboxClosed isClosed_Iic
  have haffineClosed : IsClosed affineSet := by
    have hAcont : Continuous (fun x : PrimalPoint => A.mulVec x) := by
      simpa using
        (Continuous.matrix_mulVec (A := fun _ : PrimalPoint => A)
          continuous_const
          ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin n => ℝ))))
    simpa [affineSet, Set.preimage] using isClosed_singleton.preimage hAcont
  have hclosed :
      IsClosed ((box ∩ objSet) ∩ affineSet) := hobjClosed.inter haffineClosed
  have hEq :
      primalBarrierSublevel A b c τ z0 = (box ∩ objSet) ∩ affineSet := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨hxSlice, hxObj⟩
      rcases hxSlice with ⟨hxA, hxPos⟩
      exact ⟨⟨hsub ⟨⟨hxA, hxPos⟩, hxObj⟩, hxObj⟩, hxA⟩
    · rintro ⟨⟨hxBox, hxObj⟩, hxA⟩
      have hxPos : IsStrictlyPositive x := by
        intro i
        exact lt_of_lt_of_le (hℓ i) (hxBox i).1
      exact ⟨⟨hxA, hxPos⟩, hxObj⟩
  -- The sublevel is a closed subset of the compact coordinate box.
  rw [hEq]
  exact hboxCompact.of_isClosed_subset hclosed (fun x hx ↦ hx.1.1)

/-- Helper for Chapter09 Definition 9.7-extra-1: the primal logarithmic barrier attains a
minimum on the affine strictly-positive slice whenever that slice is nonempty. -/
lemma exists_primalBarrierMinimizer
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    {τ : ℝ} {z0 : PrimalDualState n m} (hz0 : z0 ∈ strictlyFeasibleSet A b c)
    (hτ : 0 < τ) :
    ∃ xτ : PrimalPoint,
      A.mulVec xτ = b ∧
        IsStrictlyPositive xτ ∧
        IsMinOn (primalBarrierObjective τ c) (primalFeasibleSlice A b) xτ := by
  classical
  rcases (mem_strictlyFeasibleSet_iff A b c z0).1 hz0 with
    ⟨hz0Ax, _, hz0Posx, _⟩
  have hz0Sublevel : z0.x ∈ primalBarrierSublevel A b c τ z0 := by
    exact ⟨⟨hz0Ax, hz0Posx⟩, le_rfl⟩
  rcases primalBarrierSublevel_subset_box A b c hz0 hτ with ⟨ℓ, u, hℓ, hsub⟩
  have hcontSublevel :
      ContinuousOn (primalBarrierObjective τ c) (primalBarrierSublevel A b c τ z0) :=
    (primalBarrierObjective_continuousOn_box τ c hℓ).mono hsub
  rcases (primalBarrierSublevel_isCompact A b c hz0 hτ).exists_isMinOn
      ⟨z0.x, hz0Sublevel⟩ hcontSublevel with ⟨xτ, hxτSublevel, hxτMin⟩
  rcases hxτSublevel with ⟨hxτSlice, hxτObj⟩
  rcases hxτSlice with ⟨hxτA, hxτPos⟩
  refine ⟨xτ, hxτA, hxτPos, ?_⟩
  change primalFeasibleSlice A b ⊆
      {x | primalBarrierObjective τ c xτ ≤ primalBarrierObjective τ c x}
  intro y hy
  by_cases hySublevel : y ∈ primalBarrierSublevel A b c τ z0
  · exact hxτMin hySublevel
  · have hyObjGt : primalBarrierObjective τ c z0.x < primalBarrierObjective τ c y := by
      by_contra hyNotGt
      exact hySublevel ⟨hy, le_of_not_gt hyNotGt⟩
    -- Outside the chosen sublevel, the objective is already larger than the barrier value at
    -- `z0.x`, while the minimizer lies below that reference value.
    exact le_trans hxτObj (le_of_lt hyObjGt)

/-- Helper for Chapter09 Definition 9.7-extra-1: a kernel direction through a strictly positive
primal feasible point stays inside the affine strictly-positive slice for all sufficiently small
line parameters. -/
lemma eventually_mem_primalFeasibleSlice_add_smul_of_kernel
    (A : ConstraintMatrix) (b : DualPoint) {x d : PrimalPoint}
    (hxA : A.mulVec x = b) (hxPos : IsStrictlyPositive x) (hdA : A.mulVec d = 0) :
    ∀ᶠ t : ℝ in nhds 0, x + t • d ∈ primalFeasibleSlice A b := by
  have hcoord : ∀ i : Fin n, ∀ᶠ t : ℝ in nhds 0, 0 < (x + t • d : PrimalPoint) i := by
    intro i
    let coord : ℝ → ℝ := fun t ↦ (x + t • d : PrimalPoint) i
    have hcoordCont : Continuous coord := by
      change Continuous (fun t : ℝ ↦ x i + t * d i)
      exact continuous_const.add (continuous_id.mul continuous_const)
    have hEventually :
        ∀ᶠ t : ℝ in nhds 0, coord t ∈ Set.Ioi 0 :=
      hcoordCont.continuousAt.preimage_mem_nhds
        (isOpen_Ioi.mem_nhds (by simpa [coord] using hxPos i))
    -- Continuity preserves strict positivity of each coordinate near `t = 0`.
    simpa [coord] using hEventually
  have hPos : ∀ᶠ t : ℝ in nhds 0, IsStrictlyPositive (x + t • d) := by
    simpa [IsStrictlyPositive] using
      (Finset.univ.eventually_all.2 fun i _ ↦ hcoord i)
  filter_upwards [hPos] with t htPos
  constructor
  · -- The affine equation is preserved exactly along kernel directions.
    calc
      A.mulVec (x + t • d) = A.mulVec x + t • A.mulVec d := by
        rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = b + t • 0 := by rw [hxA, hdA]
      _ = b := by simp
  · exact htPos

/-- Helper for Chapter09 Definition 9.7-extra-1: the line derivative of the primal logarithmic
barrier at a strictly positive point is the reduced-cost dot product `⟪c - τ / x, d⟫`. -/
lemma hasLineDerivAt_primalBarrierObjective
    {τ : ℝ} (c : PrimalPoint) {x d : PrimalPoint}
    (hxPos : IsStrictlyPositive x) :
    HasLineDerivAt ℝ (primalBarrierObjective τ c)
      (((fun i ↦ c i - τ / x i) ⬝ᵥ d)) x d := by
  have hcoord :
      ∀ i : Fin n,
        HasDerivAt
          (fun t : ℝ ↦ c i * (x i + t * d i) - τ * Real.log (x i + t * d i))
          (c i * d i - τ * (d i / x i)) 0 := by
    intro i
    have hConst : HasDerivAt (fun _ : ℝ ↦ x i) 0 0 := by
      simpa using (hasDerivAt_const (x := (0 : ℝ)) (c := x i))
    have hMul : HasDerivAt (fun t : ℝ ↦ t * d i) (d i) 0 := by
      simpa using (hasDerivAt_id' (x := (0 : ℝ))).mul_const (d i)
    have hArg : HasDerivAt (fun t : ℝ ↦ x i + t * d i) (d i) 0 := by
      change HasDerivAt ((fun _ : ℝ ↦ x i) + fun t : ℝ ↦ t * d i) (d i) 0
      simpa using hConst.add hMul
    have hLog : HasDerivAt (fun t : ℝ ↦ Real.log (x i + t * d i)) (d i / x i) 0 := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        hArg.log (by simpa using (hxPos i).ne')
    -- Differentiate the linear and logarithmic pieces separately before subtracting them.
    change
      HasDerivAt
        ((fun t : ℝ ↦ c i * (x i + t * d i)) - fun t : ℝ ↦ τ * Real.log (x i + t * d i))
        (c i * d i - τ * (d i / x i)) 0
    exact (hArg.const_mul (c i)).sub (hLog.const_mul τ)
  have hsum :
      HasDerivAt
        (fun t : ℝ ↦ ∑ i, (c i * (x i + t * d i) - τ * Real.log (x i + t * d i)))
        (∑ i, (c i * d i - τ * (d i / x i))) 0 := by
    simpa using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hcoord i)
  have hpath :
      HasDerivAt (fun t : ℝ ↦ primalBarrierObjective τ c (x + t • d))
        (∑ i, (c i * d i - τ * (d i / x i))) 0 := by
    convert hsum using 1
    · ext t
      simp [primalBarrierObjective, dotProduct, ← Finset.mul_sum, Finset.sum_sub_distrib]
  have hvalue :
      (∑ i, (c i * d i - τ * (d i / x i))) = ((fun i ↦ c i - τ / x i) ⬝ᵥ d) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hxi : x i ≠ 0 := (hxPos i).ne'
    field_simp [hxi]
  -- Repackage the scalar path derivative as a line derivative at `x` along `d`.
  exact hvalue ▸ (by simpa [HasLineDerivAt] using hpath)

/-- Helper for Chapter09 Definition 9.7-extra-1: a minimizer of the primal barrier on the affine
strictly-positive slice has reduced cost orthogonal to every feasible direction in `ker A`. -/
lemma barrierReducedCost_orthogonalKernel_of_isMinOn
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint) {τ : ℝ} {xτ : PrimalPoint}
    (hxτA : A.mulVec xτ = b) (hxτPos : IsStrictlyPositive xτ)
    (hxτMin : IsMinOn (primalBarrierObjective τ c) (primalFeasibleSlice A b) xτ) :
    ∀ d : PrimalPoint, A.mulVec d = 0 → ((fun i ↦ c i - τ / xτ i) ⬝ᵥ d = 0) := by
  intro d hdA
  have hEventually :
      ∀ᶠ t : ℝ in nhds 0, xτ + t • d ∈ primalFeasibleSlice A b :=
    eventually_mem_primalFeasibleSlice_add_smul_of_kernel A b hxτA hxτPos hdA
  have hDeriv :
      HasLineDerivAt ℝ (primalBarrierObjective τ c)
        (((fun i ↦ c i - τ / xτ i) ⬝ᵥ d)) xτ d :=
    hasLineDerivAt_primalBarrierObjective c hxτPos
  -- The on-slice line-derivative vanishes at a minimizer.
  exact hxτMin.hasLineDerivAt_eq_zero hDeriv hEventually

/-- Chapter09 Definition 9.7-extra-1: if the strictly feasible set is nonempty, then
for each `τ > 0` there exists a `τ`-central-path point. -/
lemma exists_centralPathPoint_of_nonempty_strictlyFeasibleSet
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint) :
    (strictlyFeasibleSet A b c).Nonempty →
      ∀ {τ : ℝ}, 0 < τ → ∃ point : PrimalDualState n m, IsCentralPathPoint A b c τ point := by
  intro hFeasible τ hτ
  rcases hFeasible with ⟨z0, hz0⟩
  rcases exists_primalBarrierMinimizer A b c hz0 hτ with
    ⟨xτ, hxτA, hxτPos, hxτMin⟩
  -- Route correction: the earlier route stalled before first-order optimality. The compact
  -- minimizer now feeds directly into the line-derivative orthogonality lemma on `ker A`.
  have hOrth :
      ∀ d : PrimalPoint, A.mulVec d = 0 → ((fun i ↦ c i - τ / xτ i) ⬝ᵥ d = 0) :=
    barrierReducedCost_orthogonalKernel_of_isMinOn A b c hxτA hxτPos hxτMin
  let reducedCost : PrimalPoint := WithLp.toLp 2 <| fun i ↦ c i - τ / xτ i
  rcases mem_range_transpose_of_barrierOrthogonalKernel
      A reducedCost (by
        intro d hd
        simpa [reducedCost] using hOrth d hd) with ⟨lam, hlam⟩
  -- The reduced-cost range certificate reconstructs the full `τ`-central-path point.
  exact exists_centralPathPoint_of_primalFeasiblePoint_and_transposeRange
    A b c hτ hxτA hxτPos ⟨lam, by simpa [reducedCost] using hlam⟩

/-- If `λ ↦ Aᵀ λ` is injective, then for each `τ > 0` the `τ`-central-path point is defined
uniquely if and only if the strictly feasible set `𝓕ᵒ` is nonempty. This is the conditional
companion for the uniqueness sentence in Chapter09 Definition 9.7-extra-1. -/
theorem existsUnique_centralPathPoint_iff_nonempty_strictlyFeasibleSet_of_transpose_mulVec_injective
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    (hAT : Function.Injective A.transpose.mulVec) :
    (∀ τ : ℝ, 0 < τ → ∃! point : PrimalDualState n m, IsCentralPathPoint A b c τ point) ↔
      (strictlyFeasibleSet A b c).Nonempty := by
  constructor
  · intro hCentral
    -- The forward implication is the easy `τ = 1` specialization.
    exact strictlyFeasibleSet_nonempty_of_forall_existsUniqueCentral A b c hCentral
  · intro hFeasible τ hτ
    -- Combine the isolated existence step with the algebraic uniqueness lemma.
    rcases exists_centralPathPoint_of_nonempty_strictlyFeasibleSet A b c hFeasible hτ with
      ⟨point, hPoint⟩
    refine ⟨point, hPoint, ?_⟩
    intro q hq
    exact (centralPathPoint_eq_of_sameTau A b c τ point q hAT hPoint hq).symm

/-- Residual formulation for Chapter09 Definition 9.7-extra-1: equivalently, a `τ`-central-path
point is a strictly
feasible point whose complementarity residual coordinates all equal `τ`; the affine residual
components are already part of `strictlyFeasibleSet A b c`. -/
theorem isCentralPathPoint_iff_mem_strictlyFeasibleSet_and_centralResidualMap_s
    (A : ConstraintMatrix) (b : DualPoint) (c : PrimalPoint)
    (τ : ℝ) (point : PrimalDualState n m) :
    IsCentralPathPoint A b c τ point ↔
      point ∈ strictlyFeasibleSet A b c ∧
        (∀ i, (centralResidualMap A b c point).s i = τ) := by
  constructor
  · rintro ⟨hMem, hComp⟩
    constructor
    · exact hMem
    · intro i
      -- The `s`-component of `centralResidualMap` is the coordinatewise product `x_i s_i`.
      simpa using hComp i
  · rintro ⟨hMem, hComp⟩
    constructor
    · exact hMem
    · intro i
      -- Reinterpret the constant residual coordinate as the complementarity equation.
      simpa using hComp i

end
