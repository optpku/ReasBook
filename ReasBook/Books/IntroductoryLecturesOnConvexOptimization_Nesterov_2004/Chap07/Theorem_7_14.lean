/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_29
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Lemma_5_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_50
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_11
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_56

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ConstrainedArgmin DikinEllipsoidNotation Gradient HessianDualLocalNorm
  HessianLocalNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Helper for Theorem 7.14: the reciprocal of a positive real is nonnegative. -/
private theorem one_div_nonneg_of_pos {x : ℝ} (hx : 0 < x) : 0 ≤ 1 / x :=
  one_div_nonneg.mpr hx.le

/-- Helper for Theorem 7.14: the dual update `s ↦ s + λ ∇f(u^*_β(s))` used by the local
barrier-subgradient owner layer. -/
def dualBarrierSubgradientUpdate
    {P : Set E}
    (uStar : {β : ℝ // 0 < β} → StrongDual ℝ E → P)
    (dualSubgradient : P → StrongDual ℝ E)
    (β : {β : ℝ // 0 < β}) (stepSize : ℝ)
    (s : StrongDual ℝ E) : StrongDual ℝ E :=
  s + stepSize • dualSubgradient (uStar β s)

/-- Helper for Theorem 7.14: the local owner for Algorithm 7.12 data, isolated here so this file
does not depend on the currently broken upstream `Algorithm_7_12` module. -/
structure DualBarrierSubgradientMethod (P : Set E) (f : E → ℝ) where
  /-- Helper for Theorem 7.14: the barrier/prox term used in the auxiliary maximization problem
  `Argmaxβ`. -/
  F : E → ℝ
  /-- Helper for Theorem 7.14: the canonical auxiliary maximizer `u^*_β(s)`. -/
  uStar : {β : ℝ // 0 < β} → StrongDual ℝ E → P
  /-- Helper for Theorem 7.14: each chosen point is the canonical maximizer of `Argmaxβ`. -/
  uStar_argmax :
    ∀ (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E),
      (uStar β s : E) ∈ Argmaxβ P F β s
  /-- Helper for Theorem 7.14: the chosen auxiliary maximizer is unique. -/
  uStar_unique :
    ∀ (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) {u : E},
      u ∈ Argmaxβ P F β s → u = (uStar β s : E)
  /-- Helper for Theorem 7.14: the objective `f` is concave on the feasible set. -/
  concaveOn_objective : ConcaveOn ℝ P f
  /-- Helper for Theorem 7.14: the available primal subgradient vector `x ↦ ∇f(x)` on `P`. -/
  subgradient : P → E
  /-- Helper for Theorem 7.14: each chosen vector is a genuine concave subgradient. -/
  subgradient_spec :
    ∀ x : P, IsConcaveSubgradientAt f (x : E) (subgradient x)
  /-- Helper for Theorem 7.14: the positive barrier parameters `β₀, β₁, ...`. -/
  beta : ℕ → {β : ℝ // 0 < β}
  /-- Helper for Theorem 7.14: the positive step sizes `λ₀, λ₁, ...`. -/
  stepSize : ℕ → {t : ℝ // 0 < t}

/-- Helper for Theorem 7.14: the generic gap function
`ℓ_k(y) = ∑_{i=0}^k λ_i ⟪g_i, y - x_i⟫`. -/
def barrierSubgradientGapFunction
    {P : Set E} (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ) : P → ℝ :=
  fun y ↦
    ∑ i ∈ Finset.range (k + 1), lam i * inner ℝ (subgradient i) ((y : E) - (x i : E))

/-- Helper for Theorem 7.14: the maximal gap `ℓ_k⋆` as a Chapter 7 supremum owner. -/
def barrierSubgradientMaximalGap
    {P : Set E} (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ) : EReal :=
  maximalValueOn (Set.univ : Set P) (barrierSubgradientGapFunction x subgradient lam k)

/-- Helper for Theorem 7.14: the partial weight sum `S_k = ∑_{i=0}^k λ_i`. -/
def barrierSubgradientWeightSum (lam : ℕ → ℝ) (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun i ↦ lam i

/-- Helper for Theorem 7.14: expanding `barrierSubgradientWeightSum λ k` gives the finite sum
`∑_{i=0}^k λ_i`. -/
theorem barrierSubgradientWeightSum_def (lam : ℕ → ℝ) (k : ℕ) :
    barrierSubgradientWeightSum lam k =
      Finset.sum (Finset.range (k + 1)) fun i ↦ lam i :=
  rfl

/-- Helper for Theorem 7.14: evaluating `barrierSubgradientGapFunction x g λ k` at `y ∈ P` gives
the defining weighted affine sum. -/
theorem barrierSubgradientGapFunction_apply
    {P : Set E} (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ) (y : P) :
    barrierSubgradientGapFunction x subgradient lam k y =
      ∑ i ∈ Finset.range (k + 1), lam i * inner ℝ (subgradient i) ((y : E) - (x i : E)) :=
  rfl

/-- Helper for Theorem 7.14: expanding `barrierSubgradientMaximalGap x g λ k` exposes the
faithful `EReal` supremum of the gap function. -/
theorem barrierSubgradientMaximalGap_def
    {P : Set E} (x : ℕ → P) (subgradient : ℕ → E) (lam : ℕ → ℝ) (k : ℕ) :
    barrierSubgradientMaximalGap x subgradient lam k =
      sSup
        (Set.range
          fun y : P ↦ ((barrierSubgradientGapFunction x subgradient lam k y : ℝ) : EReal)) := by
  rw [barrierSubgradientMaximalGap, maximalValueOn_eq_sSup_image]
  simp

namespace DualBarrierSubgradientMethod

/-- Helper for Theorem 7.14: the StrongDual-valued bridge of the primal subgradient field. -/
def dualSubgradient
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) : P → StrongDual ℝ E :=
  fun x ↦ InnerProductSpace.toDualMap ℝ E (method.subgradient x)

/-- Helper for Theorem 7.14: the dual orbit `s₀, s₁, ...` of the local Algorithm 7.12 owner. -/
def dualIterate
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) : ℕ → StrongDual ℝ E
  | 0 => 0
  | k + 1 =>
      dualBarrierSubgradientUpdate method.uStar method.dualSubgradient
        (method.beta k) (method.stepSize k : ℝ) (dualIterate method k)

/-- Helper for Theorem 7.14: the primal iterate `x_k = u^*_{β_k}(s_k)`. -/
def iterate
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) : P :=
  method.uStar (method.beta k) (method.dualIterate k)

/-- Helper for Theorem 7.14: a method can be used as its primal iterate sequence. -/
instance
    {P : Set E} {f : E → ℝ} :
    CoeFun (DualBarrierSubgradientMethod P f) (fun _ ↦ ℕ → P) where
  coe method := method.iterate

/-- Helper for Theorem 7.14: evaluating `method.dualSubgradient x` applies the Riesz map to the
primal subgradient vector. -/
theorem dualSubgradient_eq
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (x : P) :
    method.dualSubgradient x = InnerProductSpace.toDualMap ℝ E (method.subgradient x) :=
  rfl

/-- Helper for Theorem 7.14: the recursive dual orbit starts from `s₀ = 0`. -/
@[simp] theorem dualIterate_zero
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) :
    method.dualIterate 0 = 0 :=
  rfl

/-- Helper for Theorem 7.14: the recursive dual orbit satisfies its one-step update. -/
@[simp] theorem dualIterate_succ
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) :
    method.dualIterate (k + 1) =
      dualBarrierSubgradientUpdate method.uStar method.dualSubgradient
        (method.beta k) (method.stepSize k : ℝ) (method.dualIterate k) :=
  rfl

/-- Helper for Theorem 7.14: evaluating `method.iterate k` recovers the textbook formula
`x_k = u^*_{β_k}(s_k)`. -/
theorem iterate_eq
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) :
    method.iterate k = method.uStar (method.beta k) (method.dualIterate k) :=
  rfl

/-- Helper for Theorem 7.14: the auxiliary point `u^*_β(s)` attains the maximum of the textbook
shifted score. -/
theorem uStar_isMaxOn
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f)
    (x0 : E) (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) :
    IsMaxOn
      (fun v : E ↦ s (v - x0) - β * (method.F v - method.F x0))
      P
      (method.uStar β s) := by
  have hu : (method.uStar β s : E) ∈ Argmaxβ P method.F β s :=
    method.uStar_argmax β s
  rw [Argmaxβ, mem_smoothedPrimalObjectiveArgmax_iff] at hu
  rcases hu with ⟨_, hmax⟩
  have hscore :
      IsMaxOn (fun v : E ↦ s v - β * method.F v) P (method.uStar β s : E) := by
    have hmaximand :
        smoothedPrimalObjectiveMaximand
            (ContinuousLinearMap.id ℝ (StrongDual ℝ E))
            0
            method.F
            (β : ℝ)
            s =
          (fun v : E ↦ s v - β * method.F v) := by
      funext v
      simp [smoothedPrimalObjectiveMaximand]
    simpa [hmaximand] using hmax
  exact
    (isMaxOn_shifted_score_iff_textbook_payoff
      P method.F x0 β s (method.uStar β s : E)).mp hscore

/-- Helper for Theorem 7.14: the chosen primal subgradient vector along the iterate sequence. -/
def iterateSubgradient
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) : ℕ → E :=
  fun k ↦ method.subgradient (method k)

/-- Helper for Theorem 7.14: evaluating `method.iterateSubgradient k` reads the chosen
subgradient at the iterate `x_k`. -/
theorem iterateSubgradient_eq
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) :
    method.iterateSubgradient k = method.subgradient (method k) :=
  rfl

/-- Helper for Theorem 7.14: the dual recursion can be written as
`s_{k+1} = s_k + λ_k ∇f(x_k)`. -/
theorem dualIterate_succ_eq
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) :
    method.dualIterate (k + 1) =
      method.dualIterate k + (method.stepSize k : ℝ) • method.dualSubgradient (method.iterate k) := by
  simp [DualBarrierSubgradientMethod.iterate, dualBarrierSubgradientUpdate]

/-- Helper for Theorem 7.14: the method-specific gap function `ℓ_k`. -/
def gapFunction
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) : P → ℝ :=
  barrierSubgradientGapFunction method method.iterateSubgradient
    (fun i ↦ (method.stepSize i : ℝ)) k

/-- Helper for Theorem 7.14: evaluating `method.gapFunction k` gives the weighted affine sum. -/
theorem gapFunction_apply
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) (y : P) :
    method.gapFunction k y =
      ∑ i ∈ Finset.range (k + 1),
        (method.stepSize i : ℝ) * inner ℝ (method.iterateSubgradient i) ((y : E) - (method i : E)) :=
  rfl

/-- Helper for Theorem 7.14: the method-specific maximal gap `ℓ_k⋆`. -/
def maximalGap
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) : EReal :=
  barrierSubgradientMaximalGap method method.iterateSubgradient
    (fun i ↦ (method.stepSize i : ℝ)) k

/-- Helper for Theorem 7.14: expanding `method.maximalGap k` returns the generic maximal-gap
owner applied to the method data. -/
theorem maximalGap_eq
    {P : Set E} {f : E → ℝ}
    (method : DualBarrierSubgradientMethod P f) (k : ℕ) :
    method.maximalGap k =
      barrierSubgradientMaximalGap method method.iterateSubgradient
        (fun i ↦ (method.stepSize i : ℝ)) k :=
  rfl

section

variable {P : Set E} {f : E → ℝ}
variable (method : DualBarrierSubgradientMethod P f)

/-- Helper for Theorem 7.14: a minimizer on an open self-concordant domain is stationary. -/
private theorem gradient_eq_zero_at_selfconcordant_minimizer
    [IsStandardSelfConcordantOn P method.F]
    (xStar : P) (hmin : IsMinOn method.F P (xStar : E)) :
    ∇ method.F (xStar : E) = 0 := by
  let hstd : IsStandardSelfConcordantOn P method.F := inferInstance
  have hlocal : IsLocalMin method.F (xStar : E) :=
    hmin.isLocalMin (hstd.isOpen_domain.mem_nhds xStar.2)
  exact isLocalMin_gradient_eq_zero hlocal

/-- Helper for Theorem 7.14: a feasible stationary point minimizes a standard self-concordant
objective on its open convex domain. -/
private theorem stationaryPoint_isMinOn
    {g : E → ℝ} [IsStandardSelfConcordantOn P g]
    {xStar : E} (hxStar : xStar ∈ P) (hgrad : ∇ g xStar = 0) :
    IsMinOn g P xStar := by
  let hself : IsSelfConcordantOnWith P (1 : NNReal) g := inferInstance
  have hcontDiff : ContDiffAt ℝ 3 g xStar :=
    hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hxStar)
  have hdiff : DifferentiableAt ℝ g xStar := by
    exact hcontDiff.differentiableAt (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  -- Invoke the Chapter 2 variational characterization directly at the stationary point.
  rw [hself.convexOn.isMinOn_iff_gradient_variational_inequality hxStar hdiff]
  intro y hy
  simp [hgrad]

/-- Helper for Theorem 7.14: the initial iterate `method 0` is the constrained minimizer of the
barrier on `P`. -/
private theorem initial_iterate_is_barrier_argmin
    [IsStandardSelfConcordantOn P method.F] :
    (method 0 : E) ∈ argmin[P] method.F := by
  -- At `s = 0`, the chosen point `u^*_{β₀}(0) = method 0` maximizes `-β₀ (F(v) - F(x₀))`.
  refine mem_constrainedArgmin_iff.mpr ⟨(method 0).2, ?_⟩
  refine isMinOn_iff.mpr ?_
  intro y hy
  have hmax :=
    method.uStar_isMaxOn (x0 := (method 0 : E)) (β := method.beta 0) (s := 0)
  have hy' := (isMaxOn_iff.mp hmax) y hy
  -- Simplifying the zero-dual objective turns the maximality statement into `F(x₀) ≤ F(y)`.
  have hscaled :
      -((method.beta 0 : ℝ) * (method.F y - method.F (method 0 : E))) ≤
        -((method.beta 0 : ℝ) * (method.F (method 0 : E) - method.F (method 0 : E))) := by
    simpa [DualBarrierSubgradientMethod.iterate_eq, DualBarrierSubgradientMethod.dualIterate_zero] using
      hy'
  have hscaled' : -((method.beta 0 : ℝ) * (method.F y - method.F (method 0 : E))) ≤ 0 := by
    simpa using hscaled
  have hmul_nonneg :
      0 ≤ (method.beta 0 : ℝ) * (method.F y - method.F (method 0 : E)) := by
    linarith
  have hdiff_nonneg : 0 ≤ method.F y - method.F (method 0 : E) := by
    exact nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hmul_nonneg) (method.beta 0).2
  linarith

/-- Helper for Theorem 7.14: evaluating the aggregated dual iterate at `v` gives the weighted sum
of dual-subgradient pairings through stage `k`. -/
private theorem dualIterate_apply_eq_weighted_sum
    (v : E) (k : ℕ) :
    method.dualIterate (k + 1) v =
      ∑ i ∈ Finset.range (k + 1),
        (method.stepSize i : ℝ) * method.dualSubgradient (method i) v := by
  induction k with
  | zero =>
      -- The first dual iterate is exactly the first weighted dual subgradient.
      rw [method.dualIterate_succ_eq, method.dualIterate_zero]
      simp [DualBarrierSubgradientMethod.iterate_eq]
  | succ k ih =>
      -- The recursive update appends the `(k + 1)`-st weighted dual subgradient term.
      rw [method.dualIterate_succ_eq, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, ih, Finset.sum_range_succ]
      simpa [Finset.sum_range_succ, smul_eq_mul, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 7.14: the affine gap function is the aggregated dual functional
`y ↦ s_(k+1)(y - x₀)` minus the base-point correction coming from the iterates `x_i`. -/
private theorem aggregated_affine_gap_decomposition
    (k : ℕ) (y : P) :
    method.gapFunction k y =
      method.dualIterate (k + 1) ((y : E) - (method 0 : E)) -
        ∑ i ∈ Finset.range (k + 1),
          (method.stepSize i : ℝ) *
            method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) := by
  -- Rewrite each affine summand relative to the base point `x₀ = method 0`.
  rw [method.gapFunction_apply]
  calc
    ∑ i ∈ Finset.range (k + 1),
        (method.stepSize i : ℝ) *
          inner ℝ (method.iterateSubgradient i) ((y : E) - (method i : E)) =
      ∑ i ∈ Finset.range (k + 1),
        ((method.stepSize i : ℝ) *
            method.dualSubgradient (method i) ((y : E) - (method 0 : E)) -
          (method.stepSize i : ℝ) *
            method.dualSubgradient (method i) ((method i : E) - (method 0 : E))) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        -- The dual subgradient is linear, so the displacement `y - x_i` splits as
        -- `(y - x₀) - (x_i - x₀)`.
        have hsplit :
            ((y : E) - (method i : E)) =
              ((y : E) - (method 0 : E)) - ((method i : E) - (method 0 : E)) := by
          abel
        rw [hsplit, inner_sub_right, mul_sub]
        simp [DualBarrierSubgradientMethod.dualSubgradient_eq,
          DualBarrierSubgradientMethod.iterateSubgradient_eq,
          InnerProductSpace.toDual_apply_apply]
    _ =
      (∑ i ∈ Finset.range (k + 1),
          (method.stepSize i : ℝ) *
            method.dualSubgradient (method i) ((y : E) - (method 0 : E))) -
        ∑ i ∈ Finset.range (k + 1),
          (method.stepSize i : ℝ) *
            method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) := by
        rw [Finset.sum_sub_distrib]
    _ =
      method.dualIterate (k + 1) ((y : E) - (method 0 : E)) -
        ∑ i ∈ Finset.range (k + 1),
          (method.stepSize i : ℝ) *
            method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) := by
        rw [← method.dualIterate_apply_eq_weighted_sum ((y : E) - (method 0 : E)) k]

/-- The barrier owner supplies Hessian positivity at every iterate of the method. -/
theorem iterate_hessian_isPositive
    [IsStandardSelfConcordantOn P method.F] (i : ℕ) :
    (hessian method.F (method i : E)).IsPositive :=
  (inferInstance : IsStandardSelfConcordantOn P method.F).hessian_isPositive (method i).2

/-- Helper for Theorem 7.14: every feasible point is the exact `Argmaxβ` point for the dual
covector induced by its own barrier gradient. -/
private theorem selfGradientPoint_mem_argmax
    (ν : NNReal) [IsSelfConcordantBarrierOnWith P ν method.F]
    (x : P) (β : {β : ℝ // 0 < β}) :
    let s : StrongDual ℝ E := ((β : ℝ) • (InnerProductSpace.toDualMap ℝ E) (∇ method.F (x : E)))
    (x : E) ∈ Argmaxβ P method.F β s := by
  intro s
  let c : E := -∇ method.F (x : E)
  have hmin :
      IsMinOn (centralPathPenaltyObjective c method.F (1 : ℝ)) P (x : E) := by
    letI : IsStandardSelfConcordantOn P (centralPathPenaltyObjective c method.F (1 : ℝ)) :=
      centralPathPenaltyObjective_isStandardSelfConcordantOn
        (dom := P) (ν := ν) (F := method.F) c ⟨1, by norm_num⟩
    have hdiff : DifferentiableAt ℝ method.F (x : E) := by
      let hstd : IsStandardSelfConcordantOn P method.F := inferInstance
      exact
        (hstd.contDiffOn.contDiffAt (hstd.isOpen_domain.mem_nhds x.2)).differentiableAt
          (by norm_num)
    have hstationary :
        ∇ (centralPathPenaltyObjective c method.F (1 : ℝ)) (x : E) = 0 := by
      -- The frozen penalty tilt is chosen so that its gradient vanishes exactly at `x`.
      rw [(hasGradientAt_centralPathPenaltyObjective c method.F (1 : ℝ) hdiff).gradient]
      simp [c]
    exact stationaryPoint_isMinOn x.2 hstationary
  have hx0_argmin : (method 0 : E) ∈ argmin[P] method.F :=
    method.initial_iterate_is_barrier_argmin
  have hx0_argmin_int : (method 0 : E) ∈ argmin[P ∩ interior P] method.F := by
    let hstd : IsStandardSelfConcordantOn P method.F := inferInstance
    simpa [hstd.isOpen_domain.interior_eq] using hx0_argmin
  have hscore_eq (z : E) :
      s (z - (method 0 : E)) - (β : ℝ) * (method.F z - method.F (method 0 : E)) =
        (-s (method 0 : E) + (β : ℝ) * method.F (method 0 : E)) -
          (β : ℝ) * centralPathPenaltyObjective c method.F (1 : ℝ) z := by
    -- Rewrite the Chapter 7 maximization score as a constant minus the frozen penalty objective.
    rw [centralPathPenaltyObjective_apply, map_sub]
    simp [s, c, ContinuousLinearMap.smul_apply, InnerProductSpace.toDual_apply_apply]
    ring
  rw [mem_Argmaxβ_iff hx0_argmin_int]
  refine ⟨x.2, ?_⟩
  refine isMaxOn_iff.mpr ?_
  intro y hy
  have hymin := (isMinOn_iff.mp hmin) y hy
  -- The exact penalty minimizer `x` is therefore the maximizer of the equivalent shifted score.
  rw [hscore_eq, hscore_eq]
  nlinarith [show 0 < (β : ℝ) from β.2, hymin]

/-- Helper for Theorem 7.14: if the barrier Hessian vanishes on a direction at an active
`u^*_β(s)` point, then the whole affine line through that point stays in `P` and the barrier value
is constant along the line. -/
private theorem uStar_zeroCurvatureLine_value_eq
    (ν : NNReal) [IsSelfConcordantBarrierOnWith P ν method.F]
    (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) (v : E)
    (hzero : inner ℝ v ((hessian method.F (method.uStar β s : E)) v) = 0) :
    ∀ τ : ℝ,
      (method.uStar β s : E) + τ • v ∈ P ∧
        method.F ((method.uStar β s : E) + τ • v) = method.F (method.uStar β s : E) := by
  let u : E := method.uStar β s
  let hbarrier : IsSelfConcordantBarrierOnWith P ν method.F := inferInstance
  let hstd : IsStandardSelfConcordantOn P method.F := inferInstance
  have hu_mem : u ∈ P := (method.uStar β s).2
  have hline_mem : ∀ τ : ℝ, u + τ • v ∈ P := by
    intro τ
    -- Zero quadratic curvature keeps the whole affine line inside the open barrier domain.
    exact
      IsSelfConcordantOn.affine_line_mem_dom_of_zero_quadratic_form
        (dom := P) (f := method.F) (Mf := (1 : NNReal)) hstd (by norm_num) hu_mem hzero τ
  let line : ℝ →ᵃ[ℝ] E := AffineMap.lineMap u (u + v)
  have hline_apply : ∀ τ : ℝ, line τ = u + τ • v := by
    intro τ
    calc
      line τ = (1 - τ) • u + τ • (u + v) := by
        simp [line, AffineMap.lineMap_apply_module]
      _ = ((1 - τ) • u + τ • u) + τ • v := by
        rw [smul_add, add_assoc]
      _ = u + τ • v := by
        rw [← add_smul, show (1 - τ : ℝ) + τ = 1 by ring, one_smul]
  have hline_preimage : line ⁻¹' P = Set.univ := by
    ext τ
    simp [hline_apply τ, hline_mem τ]
  let φ : ℝ → ℝ := method.F ∘ line
  have hlineBarrier : IsSelfConcordantBarrierOnWith Set.univ ν φ := by
    -- Pull the barrier owner back along the affine line through `u`.
    simpa [φ, hline_preimage] using hbarrier.comp_affineMap line
  have hφ_diff : Differentiable ℝ φ := by
    intro τ
    -- The scalar line slice inherits the `C³` regularity carried by the barrier owner.
    exact
      (hlineBarrier.toIsStandardSelfConcordantOn.contDiffOn.contDiffAt
        (hlineBarrier.toIsStandardSelfConcordantOn.isOpen_domain.mem_nhds (by simp))).differentiableAt
        (by norm_num)
  have hderiv_zero : ∀ τ : ℝ, deriv φ τ = 0 := by
    intro τ
    have hnonpos_pos :
        inner ℝ (∇ φ τ) (1 : ℝ) ≤ 0 := by
      exact hlineBarrier.inner_gradient_nonpos_of_recession_direction
        (h := (1 : ℝ))
        (by
          intro s hs α hα
          simp)
        (by simp)
    have hnonpos_neg :
        inner ℝ (∇ φ τ) (-1 : ℝ) ≤ 0 := by
      exact hlineBarrier.inner_gradient_nonpos_of_recession_direction
        (h := (-1 : ℝ))
        (by
          intro s hs α hα
          simp)
        (by simp)
    have hle : deriv φ τ ≤ 0 := by
      have hnonpos_pos' : inner ℝ (deriv φ τ) (1 : ℝ) ≤ 0 := by
        simpa [gradient_eq_deriv'] using hnonpos_pos
      have hinner_one : inner ℝ (deriv φ τ) (1 : ℝ) = deriv φ τ := by
        convert (RCLike.inner_apply (deriv φ τ) (1 : ℝ)) using 1
        simp
      nlinarith [hinner_one, hnonpos_pos']
    have hge : 0 ≤ deriv φ τ := by
      have hneg : -deriv φ τ ≤ 0 := by
        have hnonpos_neg' : inner ℝ (deriv φ τ) (-1 : ℝ) ≤ 0 := by
          simpa [gradient_eq_deriv'] using hnonpos_neg
        have hinner_neg_one : inner ℝ (deriv φ τ) (-1 : ℝ) = -deriv φ τ := by
          convert (RCLike.inner_apply (deriv φ τ) (-1 : ℝ)) using 1
          simp
        nlinarith [hinner_neg_one, hnonpos_neg']
      exact neg_nonpos.mp hneg
    linarith
  have hmono : Monotone φ :=
    monotone_of_deriv_nonneg hφ_diff fun τ ↦ by
      rw [hderiv_zero τ]
  have hanti : Antitone φ :=
    antitone_of_deriv_nonpos hφ_diff fun τ ↦ by
      rw [hderiv_zero τ]
  intro τ
  refine ⟨by simpa [u] using hline_mem τ, ?_⟩
  have hconst : φ τ = φ 0 := by
    by_cases hτ : 0 ≤ τ
    · exact le_antisymm (hanti hτ) (hmono hτ)
    · have hτ' : τ ≤ 0 := le_of_not_ge hτ
      exact le_antisymm (hmono hτ') (hanti hτ')
  -- Evaluate the constant scalar slice at `τ` and at the base point `0`.
  simpa [φ, u, hline_apply τ, hline_apply 0] using hconst

/-- Helper for Theorem 7.14: uniqueness of the active maximizer forces strict positivity of the
barrier Hessian quadratic form at every `u^*_β(s)` point. -/
private theorem uStar_hessianQuadratic_pos
    (ν : NNReal) [IsSelfConcordantBarrierOnWith P ν method.F]
    (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) :
    ∀ v : E, v ≠ 0 →
      0 < inner ℝ v ((hessian method.F (method.uStar β s : E)) v) := by
  intro v hv
  let u : E := method.uStar β s
  have hnonneg :
      0 ≤ inner ℝ v ((hessian method.F u) v) :=
    (inferInstance : IsStandardSelfConcordantOn P method.F).hessian_posSemidef
      (method.uStar β s).2 v
  by_contra hnot_pos
  have hzero : inner ℝ v ((hessian method.F u) v) = 0 :=
    le_antisymm (not_lt.mp hnot_pos) hnonneg
  have hline :=
    method.uStar_zeroCurvatureLine_value_eq ν β s v hzero
  have hplus_mem : u + v ∈ P := by
    simpa [u] using (hline 1).1
  have hminus_mem : u - v ∈ P := by
    simpa [u, sub_eq_add_neg] using (hline (-1)).1
  have hplus_F : method.F (u + v) = method.F u := by
    simpa [u] using (hline 1).2
  have hminus_F : method.F (u - v) = method.F u := by
    simpa [u, sub_eq_add_neg] using (hline (-1)).2
  let x0 : E := method 0
  let payoff : E → ℝ := fun z ↦ s (z - x0) - (β : ℝ) * (method.F z - method.F x0)
  have hx0_argmin : x0 ∈ argmin[P] method.F :=
    method.initial_iterate_is_barrier_argmin
  have hx0_argmin_int : x0 ∈ argmin[P ∩ interior P] method.F := by
    let hstd : IsStandardSelfConcordantOn P method.F := inferInstance
    simpa [hstd.isOpen_domain.interior_eq, x0] using hx0_argmin
  have hmax : IsMaxOn payoff P u := by
    -- View `u = u^*_β(s)` through the canonical shifted-score maximization owner.
    simpa [payoff, u, x0] using method.uStar_isMaxOn (x0 := x0) (β := β) (s := s)
  have hs_nonpos : s v ≤ 0 := by
    have hraw := (isMaxOn_iff.mp hmax) (u + v) hplus_mem
    have hdisp : u + v - x0 = (u - x0) + v := by
      abel
    -- Comparing the active maximizer to the forward line point isolates `s v`.
    simpa [payoff, hplus_F, hdisp, map_add, x0, u] using hraw
  have hs_nonneg : 0 ≤ s v := by
    have hraw := (isMaxOn_iff.mp hmax) (u - v) hminus_mem
    have hdisp : u - v - x0 = (u - x0) - v := by
      abel
    have hneg : -(s v) ≤ 0 := by
      simpa [payoff, hminus_F, hdisp, map_sub, x0, u] using hraw
    exact neg_nonpos.mp hneg
  have hs_zero : s v = 0 := by
    linarith
  have hplus_max : IsMaxOn payoff P (u + v) := by
    refine isMaxOn_iff.mpr ?_
    intro y hy
    have hy_le := (isMaxOn_iff.mp hmax) y hy
    have hplus_value : payoff (u + v) = payoff u := by
      have hdisp : u + v - x0 = (u - x0) + v := by
        abel
      -- Once `s v = 0`, the whole forward line point attains the same shifted payoff.
      simpa [payoff, hplus_F, hdisp, map_add, hs_zero, x0, u]
    calc
      payoff y ≤ payoff u := hy_le
      _ = payoff (u + v) := hplus_value.symm
  have hplus_argmax : u + v ∈ Argmaxβ P method.F β s := by
    rw [mem_Argmaxβ_iff hx0_argmin_int]
    exact ⟨hplus_mem, hplus_max⟩
  have hEq : u + v = u := method.uStar_unique β s hplus_argmax
  have hv_zero : v = 0 := by
    have hsub := congrArg (fun z : E ↦ z - u) hEq
    simpa using hsub
  exact hv hv_zero

/-- Helper for Theorem 7.14: the Hessian at every active `u^*_β(s)` point is nondegenerate. -/
private theorem uStar_hessianDetNeZero
    (ν : NNReal) [IsSelfConcordantBarrierOnWith P ν method.F]
    (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) :
    (hessian method.F (method.uStar β s : E)).det ≠ 0 := by
  rw [ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot]
  intro hker
  obtain ⟨v, hv_mem, hv_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hpos :
      0 < inner ℝ v ((hessian method.F (method.uStar β s : E)) v) :=
    method.uStar_hessianQuadratic_pos ν β s v hv_ne
  have hzero_apply : hessian method.F (method.uStar β s : E) v = 0 := hv_mem
  have hzero_lt : 0 < (0 : ℝ) := by
    simpa [hzero_apply] using hpos
  exact lt_irrefl 0 hzero_lt

/-- Helper for Theorem 7.14: every feasible point inherits Hessian nondegeneracy by viewing it as
the exact `u^*_β(s)` point for its own gradient-induced covector. -/
private theorem barrierHessianDetNeZero
    (ν : NNReal) [IsSelfConcordantBarrierOnWith P ν method.F] {x : P} :
    (hessian method.F (x : E)).det ≠ 0 := by
  let β := method.beta 0
  let s : StrongDual ℝ E := ((β : ℝ) • (InnerProductSpace.toDualMap ℝ E) (∇ method.F (x : E)))
  have hx_argmax : (x : E) ∈ Argmaxβ P method.F β s := by
    -- Realize the current point `x` itself as the exact Chapter 7 maximizer for its own
    -- gradient-induced covector.
    simpa [β, s] using method.selfGradientPoint_mem_argmax ν x β
  have hx_eq : (x : E) = (method.uStar β s : E) :=
    method.uStar_unique β s hx_argmax
  -- Reduce the global determinant claim to the already proved nondegeneracy at active `uStar`
  -- points.
  exact hx_eq ▸ method.uStar_hessianDetNeZero ν β s

/-- Helper for Theorem 7.14: the barrier gradient vanishes at the initial iterate `method 0`
because that iterate is the analytic center of `method.F` on `P`. -/
private theorem initial_iterate_gradient_eq_zero
    [IsStandardSelfConcordantOn P method.F] :
    ∇ method.F (method 0 : E) = 0 := by
  -- Convert the already established constrained barrier minimizer into the standard stationary
  -- point statement on the open barrier domain.
  have hx0_argmin : (method 0 : E) ∈ argmin[P] method.F :=
    method.initial_iterate_is_barrier_argmin
  exact
    gradient_eq_zero_at_selfconcordant_minimizer (method := method)
      (method 0)
      ((mem_constrainedArgmin_iff.mp hx0_argmin).2)

/-- Helper for Theorem 7.14: each iterate `method i = u^*_{βᵢ}(sᵢ)` is the minimizer of the
Chapter 5 penalty objective whose tilt is the Riesz representative of `sᵢ / βᵢ`. -/
private theorem iteratePenaltyObjective_isMinOn
    (i : ℕ) :
    let β := method.beta i
    let s := method.dualIterate i
    let c : E := -((β : ℝ)⁻¹) • (InnerProductSpace.toDual ℝ E).symm s
    IsMinOn (centralPathPenaltyObjective c method.F (1 : ℝ)) P (method i : E) := by
  dsimp
  let β := method.beta i
  let s := method.dualIterate i
  let c : E := -((β : ℝ)⁻¹) • (InnerProductSpace.toDual ℝ E).symm s
  let x0 : E := method 0
  have hmax :
      IsMaxOn
        (fun v : E ↦ s (v - x0) - (β : ℝ) * (method.F v - method.F x0))
        P
        (method i : E) := by
    -- The iterate owner is the canonical maximizer of the Chapter 7 smoothed support problem.
    simpa [DualBarrierSubgradientMethod.iterate, β, s, x0] using
      method.uStar_isMaxOn (x0 := x0) (β := β) (s := s)
  have hscore_eq (z : E) :
      s (z - x0) - (β : ℝ) * (method.F z - method.F x0) =
        (-s x0 + (β : ℝ) * method.F x0) -
          (β : ℝ) * centralPathPenaltyObjective c method.F (1 : ℝ) z := by
    -- Expand the Chapter 7 score and collect it as a constant minus `βᵢ` times the Chapter 5
    -- penalty objective with the exact dual tilt.
    have hinner : inner ℝ c z = -((β : ℝ)⁻¹) * s z := by
      calc
        inner ℝ c z = inner ℝ (-((β : ℝ)⁻¹) • (InnerProductSpace.toDual ℝ E).symm s) z := by
          rfl
        _ =
            (starRingEnd ℝ) (-((β : ℝ)⁻¹)) *
              inner ℝ ((InnerProductSpace.toDual ℝ E).symm s) z := by
          rw [inner_smul_left]
        _ = -((β : ℝ)⁻¹) * inner ℝ ((InnerProductSpace.toDual ℝ E).symm s) z := by
          simp
        _ = -((β : ℝ)⁻¹) * s z := by
          rw [InnerProductSpace.toDual_symm_apply]
    rw [centralPathPenaltyObjective_apply]
    rw [hinner]
    rw [map_sub, mul_sub]
    field_simp [β.2.ne']
    ring
  refine isMinOn_iff.mpr ?_
  intro y hy
  have hymax := (isMaxOn_iff.mp hmax) y hy
  -- Rewriting both sides by the same affine shift turns the maximizer inequality into
  -- minimization of the penalty objective.
  rw [hscore_eq, hscore_eq] at hymax
  nlinarith [show 0 < (β : ℝ) from β.2, hymax]

/-- Helper for Theorem 7.14: the barrier gradient at `method i` is exactly the primal image of
the scaled dual iterate `sᵢ / βᵢ`. -/
private theorem iteratePenaltyStationarity_eq_scaledDualIterate
    [IsStandardSelfConcordantOn P method.F]
    (i : ℕ) :
    (InnerProductSpace.toDualMap ℝ E) (∇ method.F (method i : E)) =
      ((method.beta i : ℝ)⁻¹) • method.dualIterate i := by
  let β := method.beta i
  let s := method.dualIterate i
  let c : E := -((β : ℝ)⁻¹) • (InnerProductSpace.toDual ℝ E).symm s
  let hstd : IsStandardSelfConcordantOn P method.F := inferInstance
  have hmin : IsMinOn (centralPathPenaltyObjective c method.F (1 : ℝ)) P (method i : E) := by
    -- Reuse the exact penalty-objective reformulation of the iterate owner.
    simpa [β, s, c] using method.iteratePenaltyObjective_isMinOn i
  have hdiff : DifferentiableAt ℝ method.F (method i : E) := by
    -- The barrier is differentiable at every iterate because the barrier domain is open.
    exact
      (hstd.contDiffOn.contDiffAt (hstd.isOpen_domain.mem_nhds (method i).2)).differentiableAt
        (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hlocal :
      IsLocalMin (centralPathPenaltyObjective c method.F (1 : ℝ)) (method i : E) :=
    hmin.isLocalMin (hstd.isOpen_domain.mem_nhds (method i).2)
  have hgradzero :
      ∇ (centralPathPenaltyObjective c method.F (1 : ℝ)) (method i : E) = 0 :=
    isLocalMin_gradient_eq_zero hlocal
  have hgrad :
      ∇ (centralPathPenaltyObjective c method.F (1 : ℝ)) (method i : E) =
        (1 : ℝ) • c + ∇ method.F (method i : E) :=
    (hasGradientAt_centralPathPenaltyObjective c method.F (1 : ℝ) hdiff).gradient
  have hstationary : c + ∇ method.F (method i : E) = 0 := by
    rw [hgrad] at hgradzero
    simpa [one_smul] using hgradzero
  have hvector :
      ∇ method.F (method i : E) = ((β : ℝ)⁻¹) • (InnerProductSpace.toDual ℝ E).symm s := by
    -- Read the zero-gradient equation in the positive orientation.
    have hstationary' : ∇ method.F (method i : E) + c = 0 := by
      simpa [add_comm] using hstationary
    have hneg : ∇ method.F (method i : E) = -c := eq_neg_of_add_eq_zero_left hstationary'
    simpa [β, s, c] using hneg
  -- Push the vector identity back through the Riesz map to obtain the exact covector spelling.
  simpa [β, s, InnerProductSpace.toDual_apply_eq_toDualMap_apply] using
    congrArg (InnerProductSpace.toDual ℝ E) hvector

/-- The accumulated barrier error term
`A_k = ∑_{i=0}^k β_i ω_* ((λ_i / β_i) ‖g_i‖*_(x_i))` for the actual Chapter 7 method data, where
`g_i` is the chosen subgradient at the iterate `x_i = method i`. The hypothesis `hω` records the
domain condition needed to evaluate `ω_*` at each stage. -/
def accumulatedOmegaStarError
    [IsStandardSelfConcordantOn P method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun i ↦
    let δi :=
      HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
        (method.iterate_hessian_isPositive i) (hH i)
        (method.dualSubgradient (method i))
    let τi : Set.Iio (1 : ℝ) := ⟨
      (method.stepSize i : ℝ) * δi / method.beta i,
      by
        have hlt : (method.stepSize i : ℝ) * δi < (method.beta i : ℝ) := by
          simpa [δi] using hω i
        exact (div_lt_iff₀ (method.beta i).2).2 (by simpa using hlt)⟩
    (method.beta i : ℝ) * selfConcordantOmegaStar τi

/-- Evaluating `method.accumulatedOmegaStarError hH hω k` gives the finite sum
`∑_{i=0}^k β_i ω_* ((λ_i / β_i) ‖g_i‖*_(x_i))` attached to the actual method data. -/
theorem accumulatedOmegaStarError_def
    [IsStandardSelfConcordantOn P method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (k : ℕ) :
    method.accumulatedOmegaStarError hH hω k =
      Finset.sum (Finset.range (k + 1)) fun i ↦
        let δi :=
          HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
            (method.iterate_hessian_isPositive i) (hH i)
            (method.dualSubgradient (method i))
        let τi : Set.Iio (1 : ℝ) := ⟨
          (method.stepSize i : ℝ) * δi / method.beta i,
          by
            exact
              (div_lt_iff₀ (method.beta i).2).2 (by
                simpa [δi] using hω i)⟩
        (method.beta i : ℝ) * selfConcordantOmegaStar τi :=
  rfl

/-- Helper for Theorem 7.14: an `EReal` upper bound for `method.maximalGap k` follows from a
pointwise real upper bound for `method.gapFunction k`. -/
private theorem maximalGap_le_of_gapFunction_bound
    (k : ℕ) {B : ℝ}
    (hB : ∀ y : P, method.gapFunction k y ≤ B) :
    method.maximalGap k ≤ (B : EReal) := by
  -- Rewrite the maximal-gap owner as the supremum of the gap-function image over `P`.
  rw [method.maximalGap_eq, barrierSubgradientMaximalGap_def]
  refine sSup_le ?_
  rintro _ ⟨y, rfl⟩
  -- Each image point is controlled by the assumed real pointwise bound.
  have hy : (((method.gapFunction k y : ℝ) : EReal) ≤ (B : EReal)) := by
    exact_mod_cast hB y
  simpa using hy

/-- Helper for Theorem 7.14: once the Chapter 7 pointwise affine/barrier estimate controls
`s_(k+1)(y - x₀)`, the fixed base-point correction stays outside the supremum defining
`method.maximalGap k`. -/
private theorem maximalGap_le_of_dualIterate_pointwise_bound
    (k : ℕ) {B : ℝ}
    (hB :
      ∀ y : P,
        method.dualIterate (k + 1) ((y : E) - (method 0 : E)) ≤ B) :
    method.maximalGap k ≤
      ((B -
          ∑ i ∈ Finset.range (k + 1),
            (method.stepSize i : ℝ) *
              method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) : ℝ) :
        EReal) := by
  -- Apply the generic `sSup` bridge to the affine-gap decomposition from Step 1.
  refine method.maximalGap_le_of_gapFunction_bound k ?_
  intro y
  -- The decomposition isolates the common correction term from the `y`-dependent affine piece.
  rw [method.aggregated_affine_gap_decomposition k y]
  linarith [hB y]

/-- Helper for Theorem 7.14: evaluating `Uβ` at the canonical maximizer `u^*_β(s)` rewrites the
smoothed support-function value as the attained Chapter 7 payoff at that maximizer. -/
private theorem uβ_value_at_uStar
    (β : {β : ℝ // 0 < β}) (s : StrongDual ℝ E) :
    Uβ P method.F (method 0 : E) β s =
      s ((method.uStar β s : E) - (method 0 : E)) -
        (β : ℝ) * (method.F (method.uStar β s : E) - method.F (method 0 : E)) := by
  let score : E → ℝ := fun v ↦ s v - (β : ℝ) * method.F v
  have hpayoff_max :
      IsMaxOn
        (fun v : E ↦
          s (v - (method 0 : E)) -
            (β : ℝ) * (method.F v - method.F (method 0 : E)))
        P
        (method.uStar β s : E) :=
    method.uStar_isMaxOn (x0 := (method 0 : E)) (β := β) (s := s)
  have hscore_max : IsMaxOn score P (method.uStar β s : E) := by
    -- Remove the constant base-point shift from the textbook payoff.
    exact
      (isMaxOn_shifted_score_iff_textbook_payoff
        (hatP := P) (F := method.F) (x0 := (method 0 : E))
        (β := β) (s := s) (u := (method.uStar β s : E))).2 hpayoff_max
  have hscore_mem : score (method.uStar β s : E) ∈ score '' P := by
    refine Set.mem_image_of_mem score ?_
    exact (method.uStar β s).2
  have hscore_nonempty : (score '' P).Nonempty := by
    exact ⟨score (method.uStar β s : E), hscore_mem⟩
  have hscore_sSup :
      sSup (score '' P) = score (method.uStar β s : E) := by
    -- The attained maximizer identifies the conditional supremum of the score image.
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hscore_nonempty ?_ ?_
    · intro a ha
      rcases ha with ⟨u, hu, rfl⟩
      exact (isMaxOn_iff.mp hscore_max) u hu
    · intro w hw
      refine ⟨score (method.uStar β s : E), hscore_mem, hw⟩
  -- Expand `Uβ`, replace the score supremum by the attained value, and collect the base-point
  -- shift into the textbook payoff at `method i`.
  calc
    Uβ P method.F (method 0 : E) β s
        = -s (method 0 : E) +
            (β : ℝ) * method.F (method 0 : E) +
              sSup (score '' P) := by
            rw [Uβ_apply]
    _ = -s (method 0 : E) +
          (β : ℝ) * method.F (method 0 : E) +
            score (method.uStar β s : E) := by
          rw [hscore_sSup]
    _ =
        s ((method.uStar β s : E) - (method 0 : E)) -
          (β : ℝ) * (method.F (method.uStar β s : E) - method.F (method 0 : E)) := by
          simpa [score, add_comm, add_left_comm, add_assoc, sub_eq_add_neg,
            mul_comm, mul_left_comm, mul_assoc] using
            (support_payoff_eq_shifted_score
              (F := method.F) (x0 := (method 0 : E))
              (β := β) (s := s) (method.uStar β s : E)).symm

/-- Helper for Theorem 7.14: evaluating `Uβ` at the actual method iterate rewrites the smoothed
support-function value as the attained Chapter 7 payoff at `method i`. -/
private theorem uβ_value_at_iterate
    (i : ℕ) :
    Uβ P method.F (method 0 : E) (method.beta i) (method.dualIterate i) =
      method.dualIterate i ((method i : E) - (method 0 : E)) -
        (method.beta i : ℝ) * (method.F (method i : E) - method.F (method 0 : E)) := by
  -- Specialize the general attained-value adapter to the method's canonical pair
  -- `(β_i, s_i)` where `method i = u^*_{β_i}(s_i)`.
  simpa [DualBarrierSubgradientMethod.iterate] using
    method.uβ_value_at_uStar (method.beta i) (method.dualIterate i)

/-- Helper for Theorem 7.14: the smoothed payoff value `Uβ` at stage `i` is nonnegative because
the feasible base point `method 0` already gives value `0`. -/
private theorem uβ_value_nonneg
    (i : ℕ) :
    0 ≤ Uβ P method.F (method 0 : E) (method.beta i) (method.dualIterate i) := by
  have hmax :
      IsMaxOn
        (fun v : E ↦
          method.dualIterate i (v - (method 0 : E)) -
            (method.beta i : ℝ) * (method.F v - method.F (method 0 : E)))
        P
        (method i : E) :=
    method.uStar_isMaxOn (x0 := (method 0 : E)) (β := method.beta i) (s := method.dualIterate i)
  -- Evaluate the attained maximizer against the base point `x₀ = method 0`.
  have hx0_le :
      method.dualIterate i ((method 0 : E) - (method 0 : E)) -
          (method.beta i : ℝ) * (method.F (method 0 : E) - method.F (method 0 : E)) ≤
        method.dualIterate i ((method i : E) - (method 0 : E)) -
          (method.beta i : ℝ) * (method.F (method i : E) - method.F (method 0 : E)) :=
    (isMaxOn_iff.mp hmax) (method 0 : E) (method 0).2
  rw [method.uβ_value_at_iterate i]
  simpa using hx0_le

/-- Helper for Theorem 7.14: increasing the smoothing parameter from `β_i` to `β_(i+1)` can only
decrease the smoothed value at the fixed dual point `s_(i+1)` because `method 0` minimizes the
barrier term on `P`. -/
private theorem uβ_next_smoothing_le_current_smoothing
    [IsStandardSelfConcordantOn P method.F]
    (hβ_mono : ∀ i : ℕ, (method.beta i : ℝ) ≤ method.beta (i + 1))
    (i : ℕ) :
    Uβ P method.F (method 0 : E) (method.beta (i + 1)) (method.dualIterate (i + 1)) ≤
      Uβ P method.F (method 0 : E) (method.beta i) (method.dualIterate (i + 1)) := by
  have hx0_argmin : (method 0 : E) ∈ argmin[P] method.F :=
    method.initial_iterate_is_barrier_argmin
  have hpenalty_nonneg :
      0 ≤ method.F (method (i + 1) : E) - method.F (method 0 : E) := by
    rcases mem_constrainedArgmin_iff.mp hx0_argmin with ⟨_, hx0_min⟩
    exact sub_nonneg.mpr ((isMinOn_iff.mp hx0_min) (method (i + 1) : E) (method (i + 1)).2)
  calc
    Uβ P method.F (method 0 : E) (method.beta (i + 1)) (method.dualIterate (i + 1))
        =
      method.dualIterate (i + 1) ((method (i + 1) : E) - (method 0 : E)) -
        (method.beta (i + 1) : ℝ) * (method.F (method (i + 1) : E) - method.F (method 0 : E)) := by
          rw [method.uβ_value_at_iterate (i + 1)]
    _ ≤
      method.dualIterate (i + 1) ((method (i + 1) : E) - (method 0 : E)) -
        (method.beta i : ℝ) * (method.F (method (i + 1) : E) - method.F (method 0 : E)) := by
          nlinarith [hβ_mono i, hpenalty_nonneg]
    _ ≤ Uβ P method.F (method 0 : E) (method.beta i) (method.dualIterate (i + 1)) := by
          have hmax :
              IsMaxOn
                (fun v : E ↦
                  method.dualIterate (i + 1) (v - (method 0 : E)) -
                    (method.beta i : ℝ) * (method.F v - method.F (method 0 : E)))
                P
                (method.uStar (method.beta i) (method.dualIterate (i + 1)) : E) :=
            method.uStar_isMaxOn (x0 := (method 0 : E))
              (β := method.beta i) (s := method.dualIterate (i + 1))
          have hle :=
            (isMaxOn_iff.mp hmax) (method (i + 1) : E) (method (i + 1)).2
          rw [method.uβ_value_at_uStar (method.beta i) (method.dualIterate (i + 1))]
          simpa using hle

/-- Helper for Theorem 7.14: one Chapter 7 update step increases the corrected smoothed value by
at most the single-step `β_i ω_*` contribution. -/
private theorem regularized_value_increment_le_omegaStar_step
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (hβ_mono : ∀ i : ℕ, (method.beta i : ℝ) ≤ method.beta (i + 1))
    (i : ℕ) :
    let correctionPrefix : ℕ → ℝ := fun n ↦
      ∑ j ∈ Finset.range n,
        (method.stepSize j : ℝ) *
          method.dualSubgradient (method j) ((method j : E) - (method 0 : E))
    let δi :=
      HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
        (method.iterate_hessian_isPositive i) (hH i)
        (method.dualSubgradient (method i))
    let τi : Set.Iio (1 : ℝ) := ⟨
      (method.stepSize i : ℝ) * δi / method.beta i,
      by
        have hlt : (method.stepSize i : ℝ) * δi < (method.beta i : ℝ) := by
          simpa [δi] using hω i
        exact (div_lt_iff₀ (method.beta i).2).2 (by simpa using hlt)⟩
    Uβ P method.F (method 0 : E) (method.beta (i + 1)) (method.dualIterate (i + 1)) -
        correctionPrefix (i + 1) ≤
      Uβ P method.F (method 0 : E) (method.beta i) (method.dualIterate i) -
        correctionPrefix i +
        (method.beta i : ℝ) * selfConcordantOmegaStar τi := by
  intro correctionPrefix δi τi
  let g : StrongDual ℝ E := (method.stepSize i : ℝ) • method.dualSubgradient (method i)
  let hstd : IsStandardSelfConcordantOn P method.F := inferInstance
  let hstdInt : IsStandardSelfConcordantOn (interior P) method.F := by
    simpa [hstd.isOpen_domain.interior_eq] using hstd
  letI : IsStandardSelfConcordantOn (interior P) method.F := hstdInt
  have hP_int : P ⊆ interior P := by
    -- The barrier domain is open, so the support-function smoothing theorem can work over
    -- `interior P` without changing the feasible set.
    intro x hx
    simpa [hstd.isOpen_domain.interior_eq] using hx
  have hx_argmax :
      (method i : E) ∈ Argmaxβ P method.F (method.beta i) (method.dualIterate i) := by
    -- The method iterate `xᵢ` is the canonical maximizer of the stage-`i` smoothed score.
    simpa [DualBarrierSubgradientMethod.iterate] using
      method.uStar_argmax (method.beta i) (method.dualIterate i)
  have hx_unique :
      ∀ u : E, u ∈ Argmaxβ P method.F (method.beta i) (method.dualIterate i) → u = (method i : E) := by
    intro u hu
    -- Uniqueness of the canonical maximizer lets Lemma 7.10 identify the derivative at `sᵢ`.
    simpa [DualBarrierSubgradientMethod.iterate] using
      method.uStar_unique (method.beta i) (method.dualIterate i) hu
  have hx_int : (method i : E) ∈ interior P := hP_int (method i).2
  have hPosInt : (hessian method.F (method i : E)).IsPositive :=
    (inferInstance : IsStandardSelfConcordantOn (interior P) method.F).hessian_isPositive hx_int
  have hg_eq :
      supportFunctionApproximationDualLocalNormAt
          (hatP := P) (Q := P) (F := method.F)
          (β := method.beta i) hx_argmax hP_int (hH i) g =
        (method.stepSize i : ℝ) * δi := by
    -- Positive homogeneity of the Chapter 5 dual local norm identifies the perturbation norm
    -- with the scalar step size times the stage-`i` local norm `δᵢ`.
    dsimp [supportFunctionApproximationDualLocalNormAt, g, δi]
    simpa [HessianDualLocalNorm.ofDetNeZero_def, dualLocalNorm_def, smul_eq_mul] using
      dualLocalNorm_smul_nonneg method.F (method i : E) hPosInt
        (hessian_isInvertible_of_det_ne_zero (hH i))
        (method.dualSubgradient (method i))
        (show 0 ≤ (method.stepSize i : ℝ) from (method.stepSize i).2.le)
  have hg :
      supportFunctionApproximationDualLocalNormAt
          (hatP := P) (Q := P) (F := method.F)
          (β := method.beta i) hx_argmax hP_int (hH i) g <
        (method.beta i : ℝ) := by
    -- Rewriting the perturbation norm by `hg_eq` reduces admissibility exactly to `hω i`.
    rw [hg_eq]
    simpa [δi] using hω i
  have hupper_raw' :
      Uβ P method.F (method 0 : E) (method.beta i) (method.dualIterate i + g) ≤
        Uβ P method.F (method 0 : E) (method.beta i) (method.dualIterate i) +
          g ((method i : E) - (method 0 : E)) +
          (method.beta i : ℝ) * selfConcordantOmegaStar τi := by
    -- Now rewrite the Lemma 7.10 remainder term through the explicit norm identity `hg_eq`.
    simpa [hg_eq, τi, selfConcordantOmegaStar] using
      (smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound
        (hatP := P) (Q := P) (F := method.F) (x0 := (method 0 : E))
        (β := method.beta i) (s := method.dualIterate i) (x := (method i : E))
        hx_argmax hx_unique hP_int (hH i)).2 g hg
  have hupper :
      Uβ P method.F (method 0 : E) (method.beta i) (method.dualIterate (i + 1)) ≤
        Uβ P method.F (method 0 : E) (method.beta i) (method.dualIterate i) +
          (method.stepSize i : ℝ) *
            method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) +
          (method.beta i : ℝ) * selfConcordantOmegaStar τi := by
    -- Rewriting `sᵢ + g` as `sᵢ₊₁` gives the one-step `ω_*` model on the fixed smoothing
    -- parameter `βᵢ`.
    rw [method.dualIterate_succ_eq i]
    simpa [g, ContinuousLinearMap.smul_apply, mul_assoc, mul_left_comm, mul_comm] using hupper_raw'
  have hsmoothing :
      Uβ P method.F (method 0 : E) (method.beta (i + 1)) (method.dualIterate (i + 1)) ≤
        Uβ P method.F (method 0 : E) (method.beta i) (method.dualIterate (i + 1)) :=
    method.uβ_next_smoothing_le_current_smoothing hβ_mono i
  have hcombined :
      Uβ P method.F (method 0 : E) (method.beta (i + 1)) (method.dualIterate (i + 1)) ≤
        Uβ P method.F (method 0 : E) (method.beta i) (method.dualIterate i) +
          (method.stepSize i : ℝ) *
            method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) +
          (method.beta i : ℝ) * selfConcordantOmegaStar τi := by
    -- The monotonicity in `β` feeds the stage-`i` upper model into the corrected-value telescope.
    exact le_trans hsmoothing hupper
  have hprefix :
      correctionPrefix (i + 1) =
        correctionPrefix i +
          (method.stepSize i : ℝ) *
            method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) := by
    -- Expanding the last correction term isolates the single step that cancels against the
    -- linear part of the `ω_*` upper model.
    simp [correctionPrefix, Finset.sum_range_succ]
  rw [hprefix]
  linarith

/-- Helper for Theorem 7.14: telescoping the one-step Chapter 7 estimate controls the corrected
smoothed value by the accumulated `ω_*` error sum `A_k`. -/
private theorem regularized_value_minus_correction_le_accumulated_omegaStar
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (hβ_mono : ∀ i : ℕ, (method.beta i : ℝ) ≤ method.beta (i + 1))
    (k : ℕ) :
    let correctionPrefix : ℕ → ℝ := fun n ↦
      ∑ j ∈ Finset.range n,
        (method.stepSize j : ℝ) *
          method.dualSubgradient (method j) ((method j : E) - (method 0 : E))
    Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1)) -
        correctionPrefix (k + 1) ≤
      method.accumulatedOmegaStarError hH hω k := by
  intro correctionPrefix
  induction k with
  | zero =>
      have hstep :=
        method.regularized_value_increment_le_omegaStar_step ν hH hω hβ_mono 0
      have hzero :
          Uβ P method.F (method 0 : E) (method.beta 0) (method.dualIterate 0) = 0 := by
        have hx0_argmin : (method 0 : E) ∈ argmin[P] method.F :=
          method.initial_iterate_is_barrier_argmin
        have hu_argmin :
            method.F (method.uStar (method.beta 0) 0 : E) ≤ method.F (method 0 : E) := by
          have hmax :=
            method.uStar_isMaxOn
              (x0 := (method 0 : E)) (β := method.beta 0) (s := 0)
          have hx0_max := (isMaxOn_iff.mp hmax) (method 0 : E) (method 0).2
          -- Evaluating the zero-covector payoff at the analytic center leaves only the barrier gap.
          have hscaled :
              0 ≤
                -((method.beta 0 : ℝ) *
                  (method.F (method.uStar (method.beta 0) 0 : E) - method.F (method 0 : E))) := by
            simpa using hx0_max
          have hmul :
              (method.beta 0 : ℝ) *
                  (method.F (method.uStar (method.beta 0) 0 : E) - method.F (method 0 : E)) ≤ 0 := by
            linarith
          nlinarith [show 0 < (method.beta 0 : ℝ) from (method.beta 0).2, hmul]
        have hx0_le :
            method.F (method 0 : E) ≤ method.F (method.uStar (method.beta 0) 0 : E) := by
          exact (mem_constrainedArgmin_iff.mp hx0_argmin).2 (method.uStar (method.beta 0) 0).2
        have hF_eq : method.F (method.uStar (method.beta 0) 0 : E) = method.F (method 0 : E) :=
          le_antisymm hu_argmin hx0_le
        -- Rewrite the attained smoothed value at the zero covector and collapse the vanishing gap.
        simpa [method.dualIterate_zero, hF_eq] using
          method.uβ_value_at_uStar (method.beta 0) (0 : StrongDual ℝ E)
      -- The base case is exactly the first one-step estimate because the zero-covector value and
      -- the empty correction prefix both vanish.
      rw [method.accumulatedOmegaStarError_def hH hω 0]
      simpa [correctionPrefix, Finset.sum_range_succ, hzero] using hstep
  | succ k ih =>
      let δi :=
        HessianDualLocalNorm.ofDetNeZero method.F (method (k + 1) : E)
          (method.iterate_hessian_isPositive (k + 1)) (hH (k + 1))
          (method.dualSubgradient (method (k + 1)))
      let τi : Set.Iio (1 : ℝ) := ⟨
        (method.stepSize (k + 1) : ℝ) * δi / method.beta (k + 1),
        by
          have hlt :
              (method.stepSize (k + 1) : ℝ) * δi < (method.beta (k + 1) : ℝ) := by
            simpa [δi] using hω (k + 1)
          exact (div_lt_iff₀ (method.beta (k + 1)).2).2 (by simpa using hlt)⟩
      let stepTerm : ℝ := (method.beta (k + 1) : ℝ) * selfConcordantOmegaStar τi
      have hstep :=
        method.regularized_value_increment_le_omegaStar_step ν hH hω hβ_mono (k + 1)
      have htail :
          Uβ P method.F (method 0 : E) (method.beta (k + 2)) (method.dualIterate (k + 2)) -
              correctionPrefix (k + 2) ≤
            method.accumulatedOmegaStarError hH hω k + stepTerm := by
        -- First append the new one-step `ω_*` contribution to the previously telescoped prefix.
        have ih' :
            Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1)) -
                correctionPrefix (k + 1) + stepTerm ≤
              method.accumulatedOmegaStarError hH hω k + stepTerm :=
          add_le_add_right ih stepTerm
        exact le_trans hstep ih'
      -- Rewrite the extended finite sum with `Finset.range_succ` so the appended step matches the
      -- final term of `A_(k+1)`.
      rw [method.accumulatedOmegaStarError_def hH hω (k + 1)]
      simpa [correctionPrefix, Finset.sum_range_succ, δi, τi, stepTerm, add_assoc, add_left_comm,
        add_comm] using htail

/-- Helper for Theorem 7.14: the initial analytic center `method 0` satisfies the standard
barrier segment bound toward every feasible point `y ∈ P`. -/
private theorem segment_barrier_bound_from_initial_argmin
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (y : P) {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    method.F ((method 0 : E) + α • ((y : E) - (method 0 : E))) ≤
      method.F (method 0 : E) - (ν : ℝ) * Real.log (1 - α) := by
  let hF : IsSelfConcordantBarrierOnWith P ν method.F := inferInstance
  -- Apply the Chapter 5 segment estimate at the initial barrier minimizer `method 0`.
  exact
    hF.segment_upper_bound_log_one_sub
      (x := (method 0 : E)) (y := (y : E)) (method 0).2 y.2 hα

/-- Helper for Theorem 7.14: every feasible segment point from the initial iterate `method 0`
produces the Chapter 7 regularized-gap inequality for the dual iterate `s_(k+1)`. -/
private theorem dualIterate_segment_regularized_gap_bound
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) (y : P) {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    α * method.dualIterate (k + 1) ((y : E) - (method 0 : E)) +
        (method.beta (k + 1) : ℝ) * (ν : ℝ) * Real.log (1 - α) ≤
      Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1)) := by
  let ℓ : AffineMap ℝ E ℝ := (method.dualIterate (k + 1)).toAffineMap
  have hconv : Convex ℝ P :=
    (inferInstance : IsStandardSelfConcordantOn P method.F).convex_domain
  have hxBeta_max :
      IsMaxOn
        (affineBarrierRegularizedPayoff (method 0 : E) (method.beta (k + 1) : ℝ) ℓ method.F)
        P
        (method (k + 1) : E) := by
    have hpayoff_max :=
      method.uStar_isMaxOn (x0 := (method 0 : E)) (β := method.beta (k + 1))
        (s := method.dualIterate (k + 1))
    -- Rewrite the method's canonical maximizer statement into the affine-payoff owner.
    refine isMaxOn_iff.mpr ?_
    intro v hv
    have hvmax := (isMaxOn_iff.mp hpayoff_max) v hv
    dsimp [ℓ] at hvmax ⊢
    simpa [DualBarrierSubgradientMethod.iterate, affineBarrierRegularizedPayoff_def, map_sub,
      sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hvmax
  have hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃a : ℝ⦄, a ∈ Set.Ico (0 : ℝ) 1 →
        (method 0 : E) + a • (x - (method 0 : E)) ∈ P := by
    intro x hx a ha
    have hline_mem : AffineMap.lineMap (method 0 : E) x a ∈ P := by
      -- Convexity of the barrier domain keeps the whole open segment inside `P`.
      simpa [AffineMap.lineMap_apply_module] using
        hconv.lineMap_mem (method 0).2 hx ⟨ha.1, ha.2.le⟩
    simpa [AffineMap.lineMap_apply_module', add_comm] using hline_mem
  have hsegment :
      α * (ℓ (y : E) - ℓ (method 0 : E)) +
          (method.beta (k + 1) : ℝ) * (ν : ℝ) * Real.log (1 - α) ≤
        affineBarrierRegularizedPayoff (method 0 : E) (method.beta (k + 1) : ℝ) ℓ method.F
            (method (k + 1) : E) -
          ℓ (method 0 : E) := by
    -- Feed the convex-domain segment membership and the barrier segment estimate into Lemma 7.11.
    simpa [mul_assoc] using
      regularized_gap_bound_along_segment
        (x0 := (method 0 : E))
        (β := (method.beta (k + 1) : ℝ))
        (ℓ := ℓ)
        (F := method.F)
        (P := P)
        (xStar := (y : E))
        (xBeta := (method (k + 1) : E))
        (v := (ν : ℝ))
        (method.beta (k + 1)).2
        y.2
        hxBeta_max
        hsegment_mem
        (fun {x} hx {a} ha ↦ method.segment_barrier_bound_from_initial_argmin ν ⟨x, hx⟩ ha)
        hα
  -- Rewrite the affine gap and the smoothed payoff into the Chapter 7 method notation.
  calc
    α * method.dualIterate (k + 1) ((y : E) - (method 0 : E)) +
        (method.beta (k + 1) : ℝ) * (ν : ℝ) * Real.log (1 - α)
        ≤
      affineBarrierRegularizedPayoff (method 0 : E) (method.beta (k + 1) : ℝ) ℓ method.F
          (method (k + 1) : E) -
        ℓ (method 0 : E) := by
          simpa [ℓ, map_sub, mul_assoc, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
            using hsegment
    _ = Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1)) := by
          simpa [ℓ, affineBarrierRegularizedPayoff_def, map_sub, sub_eq_add_neg, add_comm,
            add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
            (method.uβ_value_at_iterate (k + 1)).symm

/-- Helper for Theorem 7.14: the exact maximizer for the frozen initial linear functional
`S • method.dualSubgradient (method 0)` is equivalently a minimizer of the Chapter 5 penalty
objective with `c = -S • method.iterateSubgradient 0` and `t = 1 / β`. -/
private theorem initialPenaltyObjective_isMinOn_uStar_of_scaled_initialSubgradient
    (β : {β : ℝ // 0 < β}) (τ : Set.Ici (0 : ℝ)) :
    let sτ : StrongDual ℝ E := ((β : ℝ) * (τ : ℝ)) • method.dualSubgradient (method 0)
    IsMinOn
      (centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F (τ : ℝ))
      P
      (method.uStar β sτ : E) := by
  dsimp
  let x0 : E := method 0
  let sτ : StrongDual ℝ E := ((β : ℝ) * (τ : ℝ)) • method.dualSubgradient (method 0)
  let c : E := -(method.iterateSubgradient 0)
  have hmax :
      IsMaxOn
        (fun v : E ↦
          sτ (v - x0) -
            (β : ℝ) * (method.F v - method.F x0))
        P
        (method.uStar β sτ : E) :=
    method.uStar_isMaxOn (x0 := x0) (β := β) (s := sτ)
  have hscore_eq (z : E) :
      sτ (z - x0) - (β : ℝ) * (method.F z - method.F x0) =
        (-sτ x0 + (β : ℝ) * method.F x0) -
          (β : ℝ) * centralPathPenaltyObjective c method.F (τ : ℝ) z := by
    -- Expand the frozen score and collect it as a constant minus `β` times the Chapter 5 owner.
    rw [centralPathPenaltyObjective_apply, map_sub]
    simp [sτ, c, x0, ContinuousLinearMap.smul_apply,
      DualBarrierSubgradientMethod.dualSubgradient_eq,
      DualBarrierSubgradientMethod.iterateSubgradient_eq,
      InnerProductSpace.toDual_apply_apply]
    ring
  refine isMinOn_iff.mpr ?_
  intro y hy
  have hymax := (isMaxOn_iff.mp hmax) y hy
  -- Rewriting both sides by the common affine shift turns the maximizer inequality into
  -- minimization of the penalty objective.
  rw [hscore_eq, hscore_eq] at hymax
  have hscaled :
      (β : ℝ) * centralPathPenaltyObjective c method.F (τ : ℝ) (method.uStar β sτ : E) ≤
        (β : ℝ) * centralPathPenaltyObjective c method.F (τ : ℝ) y := by
    nlinarith
  exact le_of_mul_le_mul_left hscaled β.2

/-- Helper for Theorem 7.14: for the frozen initial covector, the ray
`τ ↦ u^*_β((βτ) g₀)` is a genuine Chapter 5 central path. -/
private theorem initialPenaltyRay_isCentralPath
    (k : ℕ) :
    let β := method.beta (k + 1)
    let yStar : Set.Ici (0 : ℝ) → P := fun τ ↦
      method.uStar β (((β : ℝ) * (τ : ℝ)) • method.dualSubgradient (method 0))
    IsCentralPath P (-(method.iterateSubgradient 0)) method.F yStar := by
  dsimp
  intro τ
  -- The scaled frozen `uStar` points minimize the corresponding penalty objective at each `τ`.
  simpa using
    method.initialPenaltyObjective_isMinOn_uStar_of_scaled_initialSubgradient
      (β := method.beta (k + 1)) τ

/-- Helper for Theorem 7.14: the frozen initial ray starts at the analytic center, so the
corresponding smoothed value at slope `0` is exactly `0`. -/
private theorem frozenInitialRay_zeroValue
    [IsStandardSelfConcordantOn P method.F]
    (k : ℕ) :
    let β := method.beta (k + 1)
    Uβ P method.F (method 0 : E) β 0 = 0 := by
  dsimp
  let β := method.beta (k + 1)
  have hx0_argmin : (method 0 : E) ∈ argmin[P] method.F :=
    method.initial_iterate_is_barrier_argmin
  have hu_argmin :
      method.F (method.uStar β 0 : E) ≤ method.F (method 0 : E) := by
    have hmax := method.uStar_isMaxOn (x0 := (method 0 : E)) (β := β) (s := 0)
    have hx0_max := (isMaxOn_iff.mp hmax) (method 0 : E) (method 0).2
    -- Evaluate the frozen payoff at the base point to read off the barrier comparison.
    have hscaled :
        0 ≤ -((β : ℝ) * (method.F (method.uStar β 0 : E) - method.F (method 0 : E))) := by
      simpa using hx0_max
    have hmul :
        (β : ℝ) * (method.F (method.uStar β 0 : E) - method.F (method 0 : E)) ≤ 0 := by
      linarith
    nlinarith [show 0 < (β : ℝ) from β.2, hmul]
  have hx0_le :
      method.F (method 0 : E) ≤ method.F (method.uStar β 0 : E) := by
    exact (mem_constrainedArgmin_iff.mp hx0_argmin).2 (method.uStar β 0).2
  have hF_eq : method.F (method.uStar β 0 : E) = method.F (method 0 : E) :=
    le_antisymm hu_argmin hx0_le
  -- Rewrite the attained `Uβ` value at the frozen start point and collapse the vanishing barrier
  -- difference.
  simpa [hF_eq] using method.uβ_value_at_uStar β (0 : StrongDual ℝ E)

/-- Helper for Theorem 7.14: the frozen initial-covector ray satisfies the exact Chapter 5
stationarity identity `∇ F (y(τ)) = τ g₀`. -/
private theorem initialPenaltyRay_stationarity
    [IsStandardSelfConcordantOn P method.F]
    (k : ℕ) (τ : Set.Ici (0 : ℝ)) :
    let β := method.beta (k + 1)
    let yτ : P := method.uStar β (((β : ℝ) * (τ : ℝ)) • method.dualSubgradient (method 0))
    ∇ method.F (yτ : E) = (τ : ℝ) • method.iterateSubgradient 0 := by
  dsimp
  let yStar : Set.Ici (0 : ℝ) → P := fun t ↦
    method.uStar (method.beta (k + 1))
      (((method.beta (k + 1) : ℝ) * (t : ℝ)) • method.dualSubgradient (method 0))
  let hstd : IsStandardSelfConcordantOn P method.F := inferInstance
  have hdiff : DifferentiableAt ℝ method.F (yStar τ : E) := by
    -- The central-path stationarity owner only needs differentiability of `F` at the active ray
    -- point, which comes from standard self-concordance on the open barrier domain.
    exact
      (hstd.contDiffOn.contDiffAt (hstd.isOpen_domain.mem_nhds (yStar τ).2)).differentiableAt
        (by norm_num : (3 : WithTop ℕ∞) ≠ 0)
  have hzero :
      (τ : ℝ) • (-(method.iterateSubgradient 0)) + ∇ method.F (yStar τ : E) = 0 :=
    centralPath_stationarity_eq_zero
      P (-(method.iterateSubgradient 0)) method.F yStar
      (method.initialPenaltyRay_isCentralPath k) τ
      (hstd.isOpen_domain.mem_nhds (yStar τ).2)
      hdiff
  -- Rearranging the stationarity equation isolates the frozen initial covector on the right.
  calc
    ∇ method.F (yStar τ : E) = -((τ : ℝ) • (-(method.iterateSubgradient 0))) := by
      simpa using (eq_neg_of_add_eq_zero_left hzero).symm
    _ = (τ : ℝ) • method.iterateSubgradient 0 := by
      simp

/-- Helper for Theorem 7.14: along the frozen initial-covector ray, the local dual norm of the
fixed initial covector is bounded by `√ν / τ`. -/
private theorem initialPenaltyRay_objectiveVectorNorm_le_sqrtDiv
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) (τ : Set.Ioi (0 : ℝ)) :
    let β := method.beta (k + 1)
    let yτ : P := method.uStar β (((β : ℝ) * (τ : ℝ)) • method.dualSubgradient (method 0))
    HessianDualLocalNorm.ofDetNeZero method.F (yτ : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 yτ.2)
      (method.uStar_hessianDetNeZero ν β (((β : ℝ) * (τ : ℝ)) • method.dualSubgradient (method 0)))
      (method.dualSubgradient (method 0)) ≤
      Real.sqrt (ν : ℝ) / (τ : ℝ) := by
  dsimp
  let β := method.beta (k + 1)
  let yτ : P := method.uStar β (((β : ℝ) * (τ : ℝ)) • method.dualSubgradient (method 0))
  have hPosY : (hessian method.F (yτ : E)).IsPositive :=
    IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 yτ.2
  have hτ_pos : 0 < (τ : ℝ) := τ.2
  have hdet :
      (fderiv ℝ (∇ method.F) (yτ : E)).det ≠ 0 :=
    by simpa [β, yτ] using
      method.uStar_hessianDetNeZero ν β (((β : ℝ) * (τ : ℝ)) • method.dualSubgradient (method 0))
  have hgrad_bound :
      HessianDualLocalNorm.ofDetNeZero method.F (yτ : E)
        hPosY hdet
        ((InnerProductSpace.toDualMap ℝ E) (∇ method.F (yτ : E))) ≤
        Real.sqrt (ν : ℝ) :=
    barrier_gradient_hessianDualLocalNorm_ofDetNeZero_le_sqrt
      (dom := P) (ν := ν) (F := method.F) (x := yτ) hdet
  have hstationary :
      ∇ method.F (yτ : E) = (τ : ℝ) • method.iterateSubgradient 0 := by
    -- The frozen ray is an exact central path, so its gradient is the time-scaled initial
    -- objective vector.
    simpa [β, yτ] using
      method.initialPenaltyRay_stationarity k ⟨(τ : ℝ), le_of_lt hτ_pos⟩
  have hscaled_grad :
      HessianDualLocalNorm.ofDetNeZero method.F (yτ : E)
        hPosY hdet
        (((τ : ℝ)) • method.dualSubgradient (method 0)) ≤
        Real.sqrt (ν : ℝ) := by
    simpa [HessianDualLocalNorm.ofDetNeZero_def, hstationary,
      DualBarrierSubgradientMethod.dualSubgradient_eq,
      DualBarrierSubgradientMethod.iterateSubgradient_eq, smul_eq_mul,
      mul_assoc, mul_left_comm, mul_comm] using hgrad_bound
  have hsmul :
      HessianDualLocalNorm.ofDetNeZero method.F (yτ : E)
        hPosY hdet
        (((τ : ℝ)) • method.dualSubgradient (method 0)) =
        (τ : ℝ) *
          HessianDualLocalNorm.ofDetNeZero method.F (yτ : E)
            hPosY hdet
            (method.dualSubgradient (method 0)) := by
    -- Positive homogeneity pulls the positive time parameter out of the local dual norm.
    simpa [HessianDualLocalNorm.ofDetNeZero_def] using
      dualLocalNorm_smul_nonneg method.F (yτ : E)
        hPosY
        (hessian_isInvertible_of_det_ne_zero hdet)
        (method.dualSubgradient (method 0))
        (le_of_lt hτ_pos)
  have hobjective :
      (τ : ℝ) *
          HessianDualLocalNorm.ofDetNeZero method.F (yτ : E)
            (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 yτ.2) hdet
            (method.dualSubgradient (method 0)) ≤
        Real.sqrt (ν : ℝ) := by
    rwa [hsmul] at hscaled_grad
  -- Divide by the positive time parameter to isolate the frozen initial covector.
  exact (le_div_iff₀ hτ_pos).2 (by simpa [mul_comm] using hobjective)

/-- Helper for Theorem 7.14: one admissible frozen-ray step satisfies the Chapter 7 `ω_*`
upper model at the active frozen maximizer. -/
private theorem initialPenaltyRay_valueIncrement_le_omegaStar
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) {τ τ' : ℝ}
    (hτ : 0 < τ) (hτ_le : τ ≤ τ')
    (hsmall : (τ' - τ) * (Real.sqrt (ν : ℝ) / τ) < 1) :
    let β := method.beta (k + 1)
    let sτ : StrongDual ℝ E := ((β : ℝ) * τ) • method.dualSubgradient (method 0)
    let sτ' : StrongDual ℝ E := ((β : ℝ) * τ') • method.dualSubgradient (method 0)
    let yτ : P := method.uStar β sτ
    let δτ :=
      HessianDualLocalNorm.ofDetNeZero method.F (yτ : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 yτ.2)
        (method.uStar_hessianDetNeZero ν β sτ)
        (method.dualSubgradient (method 0))
    let η : Set.Iio (1 : ℝ) := ⟨(τ' - τ) * δτ, by
      have hδ :
          δτ ≤ Real.sqrt (ν : ℝ) / τ := by
        simpa [β, yτ, δτ] using
          method.initialPenaltyRay_objectiveVectorNorm_le_sqrtDiv ν k ⟨τ, hτ⟩
      have hτdiff_nonneg : 0 ≤ τ' - τ := sub_nonneg.mpr hτ_le
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hδ hτdiff_nonneg) hsmall⟩
    Uβ P method.F (method 0 : E) β sτ' ≤
      Uβ P method.F (method 0 : E) β sτ +
        ((β : ℝ) * (τ' - τ)) *
          method.dualSubgradient (method 0) ((yτ : E) - (method 0 : E)) +
        (β : ℝ) * selfConcordantOmegaStar η := by
  dsimp
  let β := method.beta (k + 1)
  let sτ : StrongDual ℝ E := ((β : ℝ) * τ) • method.dualSubgradient (method 0)
  let sτ' : StrongDual ℝ E := ((β : ℝ) * τ') • method.dualSubgradient (method 0)
  let yτ : P := method.uStar β sτ
  let δτ :=
    HessianDualLocalNorm.ofDetNeZero method.F (yτ : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 yτ.2)
      (method.uStar_hessianDetNeZero ν β sτ)
      (method.dualSubgradient (method 0))
  let η : Set.Iio (1 : ℝ) := ⟨(τ' - τ) * δτ, by
    have hδ :
        δτ ≤ Real.sqrt (ν : ℝ) / τ := by
      simpa [β, yτ, δτ] using
        method.initialPenaltyRay_objectiveVectorNorm_le_sqrtDiv ν k ⟨τ, hτ⟩
    have hτdiff_nonneg : 0 ≤ τ' - τ := sub_nonneg.mpr hτ_le
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hδ hτdiff_nonneg) hsmall⟩
  let g : StrongDual ℝ E := ((β : ℝ) * (τ' - τ)) • method.dualSubgradient (method 0)
  let hstd : IsStandardSelfConcordantOn P method.F := inferInstance
  let hstdInt : IsStandardSelfConcordantOn (interior P) method.F := by
    simpa [hstd.isOpen_domain.interior_eq] using hstd
  letI : IsStandardSelfConcordantOn (interior P) method.F := hstdInt
  have hyτ_argmax : (yτ : E) ∈ Argmaxβ P method.F β sτ := by
    simpa [β, sτ, yτ] using method.uStar_argmax β sτ
  have hyτ_unique : ∀ u : E, u ∈ Argmaxβ P method.F β sτ → u = (yτ : E) := by
    intro u hu
    simpa [β, sτ, yτ] using method.uStar_unique β sτ hu
  have hP_int : P ⊆ interior P := by
    intro x hx
    simpa [hstd.isOpen_domain.interior_eq] using hx
  have hdet :
      (hessian method.F (yτ : E)).det ≠ 0 :=
    by simpa [yτ, sτ] using method.uStar_hessianDetNeZero ν β sτ
  have hg_norm :
      supportFunctionApproximationDualLocalNormAt
        (hatP := P) (Q := P) (F := method.F) (β := β)
        hyτ_argmax hP_int hdet g =
        (β : ℝ) * ((τ' - τ) * δτ) := by
    have hscalar_nonneg : 0 ≤ (β : ℝ) * (τ' - τ) :=
      mul_nonneg β.2.le (sub_nonneg.mpr hτ_le)
    -- The perturbation is a positive scalar multiple of the fixed initial covector.
    simpa [supportFunctionApproximationDualLocalNormAt, g, δτ, hP_int, hstdInt, mul_assoc,
      mul_left_comm, mul_comm, smul_eq_mul] using
      dualLocalNorm_smul_nonneg method.F (yτ : E)
        ((inferInstance : IsStandardSelfConcordantOn (interior P) method.F).hessian_isPositive
          (hP_int yτ.2))
        (hessian_isInvertible_of_det_ne_zero hdet)
        (method.dualSubgradient (method 0))
        hscalar_nonneg
  have hg :
      supportFunctionApproximationDualLocalNormAt
        (hatP := P) (Q := P) (F := method.F) (β := β)
        hyτ_argmax hP_int hdet g < (β : ℝ) := by
    -- The local norm estimate from the previous lemma makes this ray increment admissible.
    rw [hg_norm]
    have hη_lt : ((τ' - τ) * δτ) < 1 := η.2
    have hβ_mul : (β : ℝ) * ((τ' - τ) * δτ) < (β : ℝ) * 1 :=
      mul_lt_mul_of_pos_left hη_lt β.2
    simpa using hβ_mul
  have hupper_raw :=
    (smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound
      (hatP := P) (Q := P) (F := method.F) (x0 := (method 0 : E))
      (β := β) (s := sτ) (x := (yτ : E))
      hyτ_argmax hyτ_unique hP_int hdet).2 g hg
  -- Rewrite the abstract perturbation `g` as the concrete ray increment from `τ` to `τ'`.
  simpa [g, sτ, sτ', yτ, δτ, η, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
    mul_assoc, mul_left_comm, mul_comm, ContinuousLinearMap.smul_apply] using hupper_raw

/-- Helper for Theorem 7.14: the exact maximizer for the frozen initial linear functional
`S • method.dualSubgradient (method 0)` is equivalently a minimizer of the Chapter 5 penalty
objective with `c = -S • method.iterateSubgradient 0` and `t = 1 / β`. -/
private theorem initialPenaltyObjective_isMinOn_uStar
    (k : ℕ) :
    let β := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / (β : ℝ), one_div_nonneg_of_pos β.2⟩
    IsMinOn (centralPathPenaltyObjective c method.F t) P (method.uStar β s0 : E) := by
  dsimp
  let x0 : E := method 0
  let β := method.beta (k + 1)
  let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
  let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
  let c : E := -(S : ℝ) • method.iterateSubgradient 0
  let t : Set.Ici (0 : ℝ) := ⟨1 / (β : ℝ), one_div_nonneg_of_pos β.2⟩
  have hmax :
      IsMaxOn
        (fun v : E ↦
          s0 (v - x0) -
            (β : ℝ) * (method.F v - method.F x0))
        P
        (method.uStar β s0 : E) :=
    method.uStar_isMaxOn (x0 := x0) (β := β) (s := s0)
  have hscore_eq (z : E) :
      s0 (z - x0) - (β : ℝ) * (method.F z - method.F x0) =
        (β : ℝ) * method.F x0 - (β : ℝ) * centralPathPenaltyObjective c method.F t z := by
    -- Expand the frozen Chapter 7 score and rewrite it as a constant minus `β` times the
    -- Chapter 5 penalty objective.
    rw [centralPathPenaltyObjective_apply]
    simp [s0, c, t, x0, β, S, ContinuousLinearMap.smul_apply,
      DualBarrierSubgradientMethod.dualSubgradient_eq,
      DualBarrierSubgradientMethod.iterateSubgradient_eq,
      InnerProductSpace.toDual_apply_apply]
    ring
  refine isMinOn_iff.mpr ?_
  intro y hy
  have hymax := (isMaxOn_iff.mp hmax) y hy
  rw [hscore_eq, hscore_eq] at hymax
  linarith [show 0 < (β : ℝ) from β.2]

/-- Helper for Theorem 7.14: at the analytic center `x₀ = method 0`, the frozen Chapter 5
residual for the initial covector simplifies to the scalar `(S / β) δ₀`. -/
private theorem initialPenaltyApproxCenterResidualEq
    [IsStandardSelfConcordantOn P method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
      (method.iterate_hessian_isPositive 0) (hH 0)
      ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (method 0 : E))) =
      (S / β) * δ0 := by
  let β : ℝ := method.beta (k + 1)
  let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
  let c : E := -(S : ℝ) • method.iterateSubgradient 0
  let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
    have hβ : 0 < β := by
      simpa [β] using (method.beta (k + 1)).2
    exact one_div_nonneg_of_pos hβ⟩
  let δ0 :=
    HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
      (method.iterate_hessian_isPositive 0) (hH 0)
      (method.dualSubgradient (method 0))
  have hgrad_zero : ∇ method.F (method 0 : E) = 0 :=
    method.initial_iterate_gradient_eq_zero
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    rw [barrierSubgradientWeightSum_def]
    exact Finset.sum_nonneg fun i hi ↦ (method.stepSize i).2.le
  have hcovector :
      (InnerProductSpace.toDualMap ℝ E) ((t : ℝ) • c) =
        -((S / β) : ℝ) • method.dualSubgradient (method 0) := by
    -- Rewrite the frozen residual vector as the negative scalar multiple of the initial
    -- subgradient covector.
    dsimp [t, c, S, β]
    simp [DualBarrierSubgradientMethod.dualSubgradient_eq,
      DualBarrierSubgradientMethod.iterateSubgradient_eq,
      smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hsmul :
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (((S / β) : ℝ) • method.dualSubgradient (method 0)) =
        (S / β) * δ0 := by
    -- Positive homogeneity extracts the nonnegative scalar `S / β`.
    simpa [δ0, HessianDualLocalNorm.ofDetNeZero, smul_eq_mul] using
      dualLocalNorm_smul_nonneg method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0)
        (hessian_isInvertible_of_det_ne_zero (hH 0))
        (method.dualSubgradient (method 0))
        (show 0 ≤ S / β by exact div_nonneg hS_nonneg hβ_pos.le)
  -- Insert the vanishing gradient and normalize the remaining covector by evenness plus
  -- positive homogeneity of the Hessian dual local norm.
  rw [hgrad_zero, add_zero, hcovector]
  rw [show -((S / β : ℝ) • method.dualSubgradient (method 0)) =
      -(((S / β : ℝ)) • method.dualSubgradient (method 0)) by simp]
  rw [hessianDualLocalNorm_ofDetNeZero_neg
    (method.iterate_hessian_isPositive 0) (hH 0)]
  exact hsmul

/-- Helper for Theorem 7.14: at the analytic center `x₀ = method 0`, the frozen Chapter 5
residual at an arbitrary ray time `τ` simplifies to the scalar `τ δ₀`. -/
private theorem initialPenaltyRayResidualEq
    [IsStandardSelfConcordantOn P method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    ∀ {τ : ℝ}, 0 ≤ τ →
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        ((InnerProductSpace.toDualMap ℝ E)
          ((τ : ℝ) • (-(method.iterateSubgradient 0)) + ∇ method.F (method 0 : E))) =
        τ * δ0 := by
  intro δ0 τ hτ
  have hgrad_zero : ∇ method.F (method 0 : E) = 0 :=
    method.initial_iterate_gradient_eq_zero
  have hcovector :
      (InnerProductSpace.toDualMap ℝ E) ((τ : ℝ) • (-(method.iterateSubgradient 0))) =
        -((τ : ℝ) • method.dualSubgradient (method 0)) := by
    -- Rewrite the frozen residual vector as the negative time-scaled initial covector.
    simp [DualBarrierSubgradientMethod.dualSubgradient_eq,
      DualBarrierSubgradientMethod.iterateSubgradient_eq]
  have hsmul :
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        ((τ : ℝ) • method.dualSubgradient (method 0)) =
        τ * δ0 := by
    -- Positive homogeneity extracts the nonnegative ray time from the local dual norm.
    simpa [δ0, HessianDualLocalNorm.ofDetNeZero, smul_eq_mul] using
      dualLocalNorm_smul_nonneg method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0)
        (hessian_isInvertible_of_det_ne_zero (hH 0))
        (method.dualSubgradient (method 0))
        hτ
  -- Insert the vanishing analytic-center gradient and normalize the remaining covector by
  -- evenness plus positive homogeneity of the Hessian dual local norm.
  rw [hgrad_zero, add_zero, hcovector]
  rw [hessianDualLocalNorm_ofDetNeZero_neg
    (method.iterate_hessian_isPositive 0) (hH 0)]
  exact hsmul

/-- Helper for Theorem 7.14: on the frozen initial ray, the smoothed value `Uβ` is exactly the
barrier parameter times the Chapter 5 penalty-objective gap between `method 0` and the exact
central-path point at time `τ`. -/
private theorem frozenInitialRayValue_eq_scaled_penaltyGap
    (k : ℕ) {τ : ℝ} :
    let β := method.beta (k + 1)
    let sτ : StrongDual ℝ E := ((β : ℝ) * τ) • method.dualSubgradient (method 0)
    let yτ : P := method.uStar β sτ
    let c : E := -(method.iterateSubgradient 0)
    Uβ P method.F (method 0 : E) β sτ =
      (β : ℝ) *
        (centralPathPenaltyObjective c method.F τ (method 0 : E) -
          centralPathPenaltyObjective c method.F τ (yτ : E)) := by
  dsimp
  let β := method.beta (k + 1)
  let sτ : StrongDual ℝ E := ((β : ℝ) * τ) • method.dualSubgradient (method 0)
  let yτ : P := method.uStar β sτ
  let c : E := -(method.iterateSubgradient 0)
  calc
    Uβ P method.F (method 0 : E) β sτ =
        sτ ((yτ : E) - (method 0 : E)) -
          (β : ℝ) * (method.F (yτ : E) - method.F (method 0 : E)) := by
          -- First rewrite `Uβ` at the exact frozen maximizer supplied by `uStar`.
          simpa [β, sτ, yτ] using method.uβ_value_at_uStar β sτ
    _ =
        (β : ℝ) *
          (centralPathPenaltyObjective c method.F τ (method 0 : E) -
            centralPathPenaltyObjective c method.F τ (yτ : E)) := by
          -- Then expand the penalty objective and collect the common factor `β`.
          rw [centralPathPenaltyObjective_apply, centralPathPenaltyObjective_apply]
          simp [sτ, c, DualBarrierSubgradientMethod.dualSubgradient_eq,
            DualBarrierSubgradientMethod.iterateSubgradient_eq,
            InnerProductSpace.toDual_apply_apply]
          ring

/-- Helper for Theorem 7.14: the frozen full-step value `Uβ(..., S • g₀)` is the same scaled
Chapter 5 penalty gap, specialized to the ray time `τ = S / β`. -/
private theorem frozenInitialPenaltyValue_eq_scaled_penaltyGap
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
    let xPath : P := method.uStar (method.beta (k + 1)) s0
    let c : E := -(method.iterateSubgradient 0)
    Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 =
      β *
        (centralPathPenaltyObjective c method.F (S / β) (method 0 : E) -
          centralPathPenaltyObjective c method.F (S / β) (xPath : E)) := by
  dsimp
  let βSub := method.beta (k + 1)
  let β : ℝ := βSub
  let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
  let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
  let xPath : P := method.uStar βSub s0
  let c : E := -(method.iterateSubgradient 0)
  have hβ : 0 < β := by
    simpa [β] using βSub.2
  -- Specialize the ray-time bridge at `τ = S / β`, where `((β : ℝ) * τ) • g₀ = S • g₀`.
  simpa [β, S, s0, xPath, c, smul_smul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm,
    hβ.ne'] using
    (method.frozenInitialRayValue_eq_scaled_penaltyGap k
      (τ := S / β))

/-- Helper for Theorem 7.14: the frozen initial-covector ray satisfies the same Chapter 7
`β ω_*` value bound at every admissible ray time `τ`. This packages the zero-start owner setup
once so the remaining proof only has to supply the missing `ν`-weighted upgrade. -/
private theorem frozenInitialRayValue_le_omegaStar
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β := method.beta (k + 1)
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    ∀ {τ : ℝ}, 0 ≤ τ → τ * δ0 < 1 →
      Uβ P method.F (method 0 : E) β (((β : ℝ) * τ) • method.dualSubgradient (method 0)) ≤
        (β : ℝ) * selfConcordantOmegaStar ⟨τ * δ0, by assumption⟩ := by
  intro β δ0 τ hτ_nonneg hτ_small
  let x0 : E := method 0
  let sτ : StrongDual ℝ E := ((β : ℝ) * τ) • method.dualSubgradient (method 0)
  let hstd : IsStandardSelfConcordantOn P method.F := inferInstance
  let hstdInt : IsStandardSelfConcordantOn (interior P) method.F := by
    simpa [hstd.isOpen_domain.interior_eq] using hstd
  letI : IsStandardSelfConcordantOn (interior P) method.F := hstdInt
  have hx0_argmin : x0 ∈ argmin[P] method.F :=
    method.initial_iterate_is_barrier_argmin
  have hx0_argmax : x0 ∈ Argmaxβ P method.F β 0 := by
    rw [mem_Argmaxβ_iff hx0_argmin]
    refine ⟨(method 0).2, ?_⟩
    refine isMaxOn_iff.mpr ?_
    intro y hy
    have hy_min : method.F x0 ≤ method.F y :=
      (mem_constrainedArgmin_iff.mp hx0_argmin).2 y hy
    have hscaled_nonneg : 0 ≤ (β : ℝ) * (method.F y - method.F x0) := by
      exact mul_nonneg β.2.le (sub_nonneg.mpr hy_min)
    -- The zero covector turns the smoothed score into the negated barrier difference.
    linarith
  have hu0 :
      (x0 : E) = (method.uStar β (0 : StrongDual ℝ E) : E) :=
    method.uStar_unique β 0 hx0_argmax
  have hP_int : P ⊆ interior P := by
    intro x hx
    simpa [hstd.isOpen_domain.interior_eq] using hx
  have hdet0 :
      (hessian method.F (method.uStar β (0 : StrongDual ℝ E) : E)).det ≠ 0 := by
    simpa [x0] using hH 0
  have hsτ_norm :
      supportFunctionApproximationDualLocalNormAt
          (hatP := P) (Q := P) (F := method.F) (β := β)
          (method.uStar_argmax β 0) hP_int hdet0 sτ =
        (β : ℝ) * (τ * δ0) := by
    have hscalar_nonneg : 0 ≤ (β : ℝ) * τ := mul_nonneg β.2.le hτ_nonneg
    -- Rewrite the frozen perturbation at `τ` back to the initial iterate and extract the
    -- nonnegative scalar `(β τ)`.
    simpa [supportFunctionApproximationDualLocalNormAt, x0, sτ, δ0, hu0,
      HessianDualLocalNorm.ofDetNeZero, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
      dualLocalNorm_smul_nonneg method.F (method.uStar β (0 : StrongDual ℝ E) : E)
        (hstdInt.hessian_isPositive (hP_int (method.uStar β (0 : StrongDual ℝ E)).2))
        (hessian_isInvertible_of_det_ne_zero hdet0)
        (method.dualSubgradient (method 0))
        hscalar_nonneg
  have hsτ_small :
      supportFunctionApproximationDualLocalNormAt
          (hatP := P) (Q := P) (F := method.F) (β := β)
          (method.uStar_argmax β 0) hP_int hdet0 sτ < (β : ℝ) := by
    rw [hsτ_norm]
    have hβ_mul :
        (β : ℝ) * (τ * δ0) < (β : ℝ) * 1 := by
      exact mul_lt_mul_of_pos_left hτ_small β.2
    simpa [mul_assoc] using hβ_mul
  have hupper_raw :=
    (smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound
      (hatP := P) (Q := P) (F := method.F) (x0 := x0)
      (β := β) (s := 0) (x := (method.uStar β (0 : StrongDual ℝ E) : E))
      (method.uStar_argmax β 0)
      (fun u hu ↦ method.uStar_unique β 0 hu) hP_int hdet0).2 sτ hsτ_small
  have hupper :
      Uβ P method.F x0 β sτ ≤
        Uβ P method.F x0 β 0 +
          sτ ((method.uStar β (0 : StrongDual ℝ E) : E) - x0) +
          (β : ℝ) * selfConcordantOmegaStar ⟨τ * δ0, hτ_small⟩ := by
    -- The general `ω_*` upper model collapses to the frozen ray scalar `τ δ₀`.
    simpa [x0, sτ, hsτ_norm, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hupper_raw
  have hzero_value : Uβ P method.F x0 β 0 = 0 := by
    simpa [x0] using method.frozenInitialRay_zeroValue k
  have hzero_shift :
      sτ ((method.uStar β (0 : StrongDual ℝ E) : E) - x0) = 0 := by
    simpa [x0, sτ, hu0]
  -- Both the starting smoothed value and the frozen linear shift vanish at the analytic center.
  calc
    Uβ P method.F x0 β sτ ≤
        Uβ P method.F x0 β 0 +
          sτ ((method.uStar β (0 : StrongDual ℝ E) : E) - x0) +
          (β : ℝ) * selfConcordantOmegaStar ⟨τ * δ0, hτ_small⟩ := hupper
    _ = (β : ℝ) * selfConcordantOmegaStar ⟨τ * δ0, hτ_small⟩ := by
          rw [hzero_value, hzero_shift]
          ring

/-- Helper for Theorem 7.14: a single admissible frozen step from the zero covector to
`S • method.dualSubgradient (method 0)` bounds the frozen smoothed value by the corresponding
`β ω_*` term. -/
private theorem frozenInitialPenaltyValue_le_omegaStar
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
    ∀ hρ : (S / β) * δ0 < 1,
      Uβ P method.F (method 0 : E) β s0 ≤
        (β : ℝ) * selfConcordantOmegaStar ⟨(S / β) * δ0, hρ⟩ := by
  intro β S δ0 s0 hρ
  let x0 : E := method 0
  let hstd : IsStandardSelfConcordantOn P method.F := inferInstance
  let hstdInt : IsStandardSelfConcordantOn (interior P) method.F := by
    simpa [hstd.isOpen_domain.interior_eq] using hstd
  letI : IsStandardSelfConcordantOn (interior P) method.F := hstdInt
  have hx0_argmin : x0 ∈ argmin[P] method.F :=
    method.initial_iterate_is_barrier_argmin
  have hx0_argmax : x0 ∈ Argmaxβ P method.F β 0 := by
    rw [mem_Argmaxβ_iff hx0_argmin]
    refine ⟨(method 0).2, ?_⟩
    refine isMaxOn_iff.mpr ?_
    intro y hy
    have hy_min : method.F x0 ≤ method.F y :=
      (mem_constrainedArgmin_iff.mp hx0_argmin).2 y hy
    have hscaled_nonneg : 0 ≤ (β : ℝ) * (method.F y - method.F x0) := by
      exact mul_nonneg β.2.le (sub_nonneg.mpr hy_min)
    -- The zero covector turns the smoothed score into the negated barrier difference.
    linarith
  have hu0 :
      (x0 : E) = (method.uStar β (0 : StrongDual ℝ E) : E) :=
    method.uStar_unique β 0 hx0_argmax
  have hP_int : P ⊆ interior P := by
    intro x hx
    simpa [hstd.isOpen_domain.interior_eq] using hx
  have hdet0 :
      (hessian method.F (method.uStar β (0 : StrongDual ℝ E) : E)).det ≠ 0 := by
    simpa [x0] using hH 0
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    rw [barrierSubgradientWeightSum_def]
    exact Finset.sum_nonneg fun i hi ↦ (method.stepSize i).2.le
  have hs0_norm :
      supportFunctionApproximationDualLocalNormAt
          (hatP := P) (Q := P) (F := method.F) (β := β)
          (method.uStar_argmax β 0) hP_int hdet0 s0 =
        S * δ0 := by
    -- Rewrite the frozen perturbation at `τ = 0` back to the initial iterate and extract the
    -- nonnegative scalar `S`.
    simpa [supportFunctionApproximationDualLocalNormAt, x0, s0, δ0, hu0,
      HessianDualLocalNorm.ofDetNeZero, smul_eq_mul] using
      dualLocalNorm_smul_nonneg method.F (method.uStar β (0 : StrongDual ℝ E) : E)
        (hstdInt.hessian_isPositive (hP_int (method.uStar β (0 : StrongDual ℝ E)).2))
        (hessian_isInvertible_of_det_ne_zero hdet0)
        (method.dualSubgradient (method 0))
        hS_nonneg
  have hs0_small :
      supportFunctionApproximationDualLocalNormAt
          (hatP := P) (Q := P) (F := method.F) (β := β)
          (method.uStar_argmax β 0) hP_int hdet0 s0 < (β : ℝ) := by
    rw [hs0_norm]
    have hρ_div : (S * δ0) / β < 1 := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hρ
    exact (div_lt_iff₀ β.2).1 (by simpa using hρ_div)
  have hupper_raw :=
    (smoothSupportFunctionApproximation_hasFDerivAt_and_omegaStar_upper_bound
      (hatP := P) (Q := P) (F := method.F) (x0 := x0)
      (β := β) (s := 0) (x := (method.uStar β (0 : StrongDual ℝ E) : E))
      (method.uStar_argmax β 0)
      (fun u hu ↦ method.uStar_unique β 0 hu) hP_int hdet0).2 s0 hs0_small
  have hupper :
      Uβ P method.F x0 β s0 ≤
        Uβ P method.F x0 β 0 +
          s0 ((method.uStar β (0 : StrongDual ℝ E) : E) - x0) +
          (β : ℝ) * selfConcordantOmegaStar ⟨(S / β) * δ0, hρ⟩ := by
    -- The general `ω_*` upper model collapses to the frozen scalar `ρ = (S / β) δ₀`.
    simpa [x0, hs0_norm, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hupper_raw
  have hzero_value : Uβ P method.F x0 β 0 = 0 := by
    simpa [x0] using method.frozenInitialRay_zeroValue k
  have hzero_shift :
      s0 ((method.uStar β (0 : StrongDual ℝ E) : E) - x0) = 0 := by
    simpa [x0, s0, hu0]
  -- Both the starting smoothed value and the frozen linear shift vanish at the analytic center.
  calc
    Uβ P method.F x0 β s0 ≤
        Uβ P method.F x0 β 0 +
          s0 ((method.uStar β (0 : StrongDual ℝ E) : E) - x0) +
          (β : ℝ) * selfConcordantOmegaStar ⟨(S / β) * δ0, hρ⟩ := hupper
    _ = (β : ℝ) * selfConcordantOmegaStar ⟨(S / β) * δ0, hρ⟩ := by
          rw [hzero_value, hzero_shift]
          ring

/-- Helper for Theorem 7.14: rewriting the frozen-ray `Uβ` estimate through the Chapter 5
penalty objective removes the outer barrier parameter factor and exposes the exact penalty gap
along the initial ray. -/
private theorem frozenInitialRayPenaltyGap_le_omegaStar
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β := method.beta (k + 1)
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    ∀ {τ : ℝ}, 0 ≤ τ → τ * δ0 < 1 →
      let yτ : P := method.uStar β (((β : ℝ) * τ) • method.dualSubgradient (method 0))
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ (yτ : E) ≤
          selfConcordantOmegaStar ⟨τ * δ0, by assumption⟩ := by
  intro β δ0 τ hτ_nonneg hτ_small yτ
  have hβ_pos : 0 < (β : ℝ) := by
    simpa [β] using (method.beta (k + 1)).2
  have hvalue :
      Uβ P method.F (method 0 : E) β (((β : ℝ) * τ) • method.dualSubgradient (method 0)) ≤
        (β : ℝ) * selfConcordantOmegaStar ⟨τ * δ0, hτ_small⟩ := by
    -- Start from the already-proved frozen-ray `Uβ` upper model at time `τ`.
    simpa [β, δ0] using
      method.frozenInitialRayValue_le_omegaStar ν hH k
        (τ := τ) hτ_nonneg hτ_small
  have hgap_scaled :
      (β : ℝ) *
          (centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
              (method 0 : E) -
            centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
              (yτ : E)) ≤
        (β : ℝ) * selfConcordantOmegaStar ⟨τ * δ0, hτ_small⟩ := by
    -- Rewrite the frozen smoothed value into the exact penalty-gap normal form.
    rw [method.frozenInitialRayValue_eq_scaled_penaltyGap k (τ := τ)] at hvalue
    simpa [β, yτ] using hvalue
  -- Divide out the positive barrier parameter to recover the bare penalty gap.
  exact (mul_le_mul_left hβ_pos).mp hgap_scaled

/-- Helper for Theorem 7.14: the full frozen step `S • method.dualSubgradient (method 0)` has the
same penalty-gap normal form, specialized to the ray time `τ = S / β`. -/
private theorem frozenInitialPenaltyGap_le_omegaStar
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    ∀ hρ : (S / β) * δ0 < 1,
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F (S / β)
          (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F (S / β)
          (xPath : E) ≤
          selfConcordantOmegaStar ⟨(S / β) * δ0, hρ⟩ := by
  intro β S δ0 xPath hρ
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hvalue :
      Uβ P method.F (method 0 : E) (method.beta (k + 1))
          (S • method.dualSubgradient (method 0)) ≤
        β * selfConcordantOmegaStar ⟨(S / β) * δ0, hρ⟩ := by
    -- Specialize the one-step frozen value bound at the full time `S / β`.
    simpa [β, S, δ0] using
      method.frozenInitialPenaltyValue_le_omegaStar ν hH k hρ
  have hgap_scaled :
      β *
          (centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F (S / β)
              (method 0 : E) -
            centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F (S / β)
              (xPath : E)) ≤
        β * selfConcordantOmegaStar ⟨(S / β) * δ0, hρ⟩ := by
    -- Rewrite the full-step `Uβ` value through the frozen penalty-gap bridge.
    rw [method.frozenInitialPenaltyValue_eq_scaled_penaltyGap k] at hvalue
    simpa [β, S, xPath] using hvalue
  -- Again divide out the positive barrier parameter.
  exact (mul_le_mul_left hβ_pos).mp hgap_scaled

/-- Helper for Theorem 7.14: the positive seed time `τ₀ = 1 / (3 δ₀)` lies on the admissible
frozen ray and yields the canonical `ω_*(1 / 3)` penalty-gap estimate. -/
private theorem frozenInitialRaySeedPenaltyGap_le_omegaStarThird
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β := method.beta (k + 1)
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let τ0 : ℝ := 1 / (3 * δ0)
    ∀ hδ0 : 0 < δ0,
      let yτ0 : P := method.uStar β (((β : ℝ) * τ0) • method.dualSubgradient (method 0))
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ0 (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ0 (yτ0 : E) ≤
          selfConcordantOmegaStar ⟨(1 / 3 : ℝ), by norm_num⟩ := by
  intro β δ0 τ0 hδ0 yτ0
  have hτ0_nonneg : 0 ≤ τ0 := by
    -- The normalized seed time is positive once `δ₀ > 0`.
    dsimp [τ0]
    positivity
  have hτ0_eq : τ0 * δ0 = (1 / 3 : ℝ) := by
    -- Normalize the seed-time residual exactly once.
    dsimp [τ0]
    field_simp [hδ0.ne']
    ring
  have hτ0_small : τ0 * δ0 < 1 := by
    rw [hτ0_eq]
    norm_num
  have hgap :
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ0 (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ0 (yτ0 : E) ≤
          selfConcordantOmegaStar ⟨τ0 * δ0, hτ0_small⟩ := by
    -- Specialize the generic frozen-ray penalty-gap theorem at the seed time `τ₀`.
    simpa [β, τ0, yτ0] using
      frozenInitialRayPenaltyGap_le_omegaStar (method := method) ν hH k
        (τ := τ0) hτ0_nonneg hτ0_small
  -- Replace the normalized residual `τ₀ δ₀` by the canonical scalar `1 / 3`.
  simpa [hτ0_eq] using hgap

/-- Helper for Theorem 7.14: rewriting the seed penalty-gap estimate back to the frozen `Uβ`
surface gives a direct bound for the canonical seed covector at `τ₀ = 1 / (3 δ₀)`. -/
private theorem frozenInitialRaySeedValue_le_betaOmegaStarThird
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β := method.beta (k + 1)
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let τ0 : ℝ := 1 / (3 * δ0)
    let sτ0 : StrongDual ℝ E := ((β : ℝ) * τ0) • method.dualSubgradient (method 0)
    ∀ hδ0 : 0 < δ0,
      Uβ P method.F (method 0 : E) β sτ0 ≤
        (β : ℝ) * selfConcordantOmegaStar ⟨(1 / 3 : ℝ), by norm_num⟩ := by
  intro β δ0 τ0 sτ0 hδ0
  let yτ0 : P := method.uStar β sτ0
  have hβ_pos : 0 < (β : ℝ) := by
    simpa [β] using (method.beta (k + 1)).2
  have hgap :
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ0 (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ0
          (yτ0 : E) ≤
          selfConcordantOmegaStar ⟨(1 / 3 : ℝ), by norm_num⟩ := by
    -- Reuse the already normalized seed-time penalty-gap estimate on the exact central-path point.
    simpa [β, δ0, τ0, sτ0, yτ0] using
      frozenInitialRaySeedPenaltyGap_le_omegaStarThird (method := method) ν hH k hδ0
  have hscaled :
      (β : ℝ) *
          (centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ0
              (method 0 : E) -
            centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ0
              (yτ0 : E)) ≤
        (β : ℝ) * selfConcordantOmegaStar ⟨(1 / 3 : ℝ), by norm_num⟩ := by
    -- Multiply the seed penalty-gap estimate by the positive barrier parameter.
    exact mul_le_mul_of_nonneg_left hgap hβ_pos.le
  -- Rewrite the frozen `Uβ` value at `τ₀` into the same penalty-gap normal form.
  calc
    Uβ P method.F (method 0 : E) β sτ0 =
        (β : ℝ) *
          (centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ0
              (method 0 : E) -
            centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ0
              (yτ0 : E)) := by
          simpa [β, τ0, sτ0, yτ0] using
            method.frozenInitialRayValue_eq_scaled_penaltyGap k (τ := τ0)
    _ ≤ (β : ℝ) * selfConcordantOmegaStar ⟨(1 / 3 : ℝ), by norm_num⟩ := hscaled

/-- Helper for Theorem 7.14: the scalar seed value `ω_*(1 / 3)` is bounded by the explicit
constant `1 / 12`. -/
private theorem omegaStarThird_le_one_twelfth :
    selfConcordantOmegaStar ⟨(1 / 3 : ℝ), by norm_num⟩ ≤ (1 / 12 : ℝ) := by
  -- Specialize the standard raw `ω_*` upper bound at the canonical seed residual `1 / 3`.
  simpa [selfConcordantOmegaStar_apply] using
    (omegaStarUpperBoundRaw (τ := (1 / 3 : ℝ)) (by norm_num) (by norm_num : (1 / 3 : ℝ) < 1))

/-- Helper for Theorem 7.14: the canonical seed covector on the frozen initial ray already has
the explicit owner-level value bound `β / 12`. -/
private theorem frozenInitialRaySeedValue_le_betaTwelfth
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β := method.beta (k + 1)
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let τ0 : ℝ := 1 / (3 * δ0)
    let sτ0 : StrongDual ℝ E := ((β : ℝ) * τ0) • method.dualSubgradient (method 0)
    ∀ hδ0 : 0 < δ0,
      Uβ P method.F (method 0 : E) β sτ0 ≤ (β : ℝ) / 12 := by
  intro β δ0 τ0 sτ0 hδ0
  have hseed :
      Uβ P method.F (method 0 : E) β sτ0 ≤
        (β : ℝ) * selfConcordantOmegaStar ⟨(1 / 3 : ℝ), by norm_num⟩ := by
    -- Start from the normalized seed-value inequality already proved on the frozen `Uβ` surface.
    simpa [β, δ0, τ0, sτ0] using
      method.frozenInitialRaySeedValue_le_betaOmegaStarThird ν hH k hδ0
  have hscaled :
      (β : ℝ) * selfConcordantOmegaStar ⟨(1 / 3 : ℝ), by norm_num⟩ ≤
        (β : ℝ) * (1 / 12 : ℝ) := by
    -- Scale the explicit scalar `ω_*(1 / 3)` bound by the nonnegative barrier parameter `β`.
    exact mul_le_mul_of_nonneg_left omegaStarThird_le_one_twelfth (by positivity : 0 ≤ (β : ℝ))
  calc
    Uβ P method.F (method 0 : E) β sτ0 ≤
        (β : ℝ) * selfConcordantOmegaStar ⟨(1 / 3 : ℝ), by norm_num⟩ := hseed
    _ ≤ (β : ℝ) * (1 / 12 : ℝ) := hscaled
    _ = (β : ℝ) / 12 := by ring

/-- Helper for Theorem 7.14: the weighted barycenter of the iterates is a feasible point of the
barrier domain. -/
private theorem iterate_centerMass_mem_domain
    [IsStandardSelfConcordantOn P method.F]
    (k : ℕ) :
    let xBar :=
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E))
    xBar ∈ P := by
  let xBar :=
    (Finset.range (k + 1)).centerMass
      (fun i ↦ (method.stepSize i : ℝ))
      (fun i ↦ (method i : E))
  let weights : ℕ → ℝ := fun i ↦ (method.stepSize i : ℝ)
  have hconv : Convex ℝ P :=
    (inferInstance : IsStandardSelfConcordantOn P method.F).convex_domain
  have hweights_nonneg :
      ∀ i ∈ Finset.range (k + 1), 0 ≤ weights i := by
    intro i hi
    exact (method.stepSize i).2.le
  have hweights_pos :
      0 < ∑ i ∈ Finset.range (k + 1), weights i := by
    have hzero_mem : 0 ∈ Finset.range (k + 1) := by
      simp
    have hzero_le :
        weights 0 ≤ ∑ i ∈ Finset.range (k + 1), weights i := by
      simpa [weights] using Finset.single_le_sum hweights_nonneg hzero_mem
    exact lt_of_lt_of_le (method.stepSize 0).2 hzero_le
  -- Convexity keeps the weighted center of mass of feasible iterates inside `P`.
  simpa [xBar, weights] using
    hconv.centerMass_mem hweights_nonneg hweights_pos fun i hi ↦ (method i).2

/-- Helper for Theorem 7.14: the frozen initial-correction term is exactly the negative linear
gap of the frozen penalty vector between the iterate barycenter and the initial iterate. -/
private theorem frozenPenaltyLinearGap_eq_neg_initialCorrection
    (k : ℕ) :
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    inner ℝ c (xBar : E) - inner ℝ c (method 0 : E) =
      -(S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E))) := by
  dsimp
  -- Expand the frozen penalty vector and collect the common scale into the Chapter 7 correction
  -- term at the barycenter.
  simp [DualBarrierSubgradientMethod.dualSubgradient_eq,
    DualBarrierSubgradientMethod.iterateSubgradient_eq,
    InnerProductSpace.toDual_apply_apply]
  ring

/-- Helper for Theorem 7.14: rewriting the same frozen linear gap in the positive orientation
gives the initial-correction term directly as `⟪c, x₀⟫ - ⟪c, x̄⟫`. -/
private theorem initialCorrection_eq_frozenPenaltyLinearGap
    (k : ℕ) :
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) =
      inner ℝ c (method 0 : E) - inner ℝ c (xBar : E) := by
  dsimp
  -- Rewrite the existing negative-gap identity into the target positive orientation.
  have hgap := method.frozenPenaltyLinearGap_eq_neg_initialCorrection k
  linarith

/-- Helper for Theorem 7.14: the frozen initial correction telescopes through the exact frozen
central-path point `xPath` into an `x₀ → xPath` part and an `xPath → x̄` part. -/
private theorem initialCorrection_split_through_path
    (k : ℕ) :
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) =
      (inner ℝ c (method 0 : E) - inner ℝ c (xPath : E)) +
        (inner ℝ c (xPath : E) - inner ℝ c (xBar : E)) := by
  dsimp
  -- First put the initial correction into the positive frozen linear-gap form, then split at
  -- the exact frozen path point `xPath`.
  rw [method.initialCorrection_eq_frozenPenaltyLinearGap k]
  ring

/-- Helper for Theorem 7.14: once the frozen penalty residual at the barycenter is bounded by some
`ε < 1`, the Chapter 5 approximate-center theorem gives the corresponding frozen objective-gap
estimate without further owner setup. -/
private theorem frozenPenaltyApproximateCenter_objectiveGap_le_ofDetWitness
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) {ε : ℝ}
    (hε : ε < 1)
    (xOpt : closure P)
    (hopt :
      let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
      let c : E := -(S : ℝ) • method.iterateSubgradient 0
      ∀ y : closure P, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    (hxBarH :
      let xBar : P := ⟨
        (Finset.range (k + 1)).centerMass
          (fun i ↦ (method.stepSize i : ℝ))
          (fun i ↦ (method i : E)),
        iterate_centerMass_mem_domain (method := method) k⟩
      (fderiv ℝ (∇ method.F) (xBar : E)).det ≠ 0)
    (happrox :
      let β : ℝ := method.beta (k + 1)
      let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
      let c : E := -(S : ℝ) • method.iterateSubgradient 0
      let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
        have hβ : 0 < β := by
          simpa [β] using (method.beta (k + 1)).2
        exact one_div_nonneg_of_pos hβ⟩
      let xBar : P := ⟨
        (Finset.range (k + 1)).centerMass
          (fun i ↦ (method.stepSize i : ℝ))
          (fun i ↦ (method i : E)),
        iterate_centerMass_mem_domain (method := method) k⟩
      HessianDualLocalNorm.ofDetNeZero method.F (xBar : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xBar.2) hxBarH
        ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (xBar : E))) ≤ ε) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    inner ℝ c (xBar : E) - inner ℝ c (xOpt : E) ≤
      ((ν : ℝ) + ((ε + Real.sqrt (ν : ℝ)) * ε) / (1 - ε)) / (t : ℝ) := by
  dsimp at hopt hxBarH happrox ⊢
  let β := method.beta (k + 1)
  let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
  let c : E := -(S : ℝ) • method.iterateSubgradient 0
  let t : Set.Ici (0 : ℝ) := ⟨1 / (β : ℝ), one_div_nonneg_of_pos (by
    simpa [β] using (method.beta (k + 1)).2)⟩
  let xPath : P := method.uStar β (S • method.dualSubgradient (method 0))
  let xBar : P := ⟨
    (Finset.range (k + 1)).centerMass
      (fun i ↦ (method.stepSize i : ℝ))
      (fun i ↦ (method i : E)),
    iterate_centerMass_mem_domain (method := method) k⟩
  have ht : 0 < (t : ℝ) := by
    positivity
  have hpath : IsMinOn (centralPathPenaltyObjective c method.F t) P (xPath : E) := by
    -- The frozen Chapter 7 maximizer is the exact Chapter 5 path point for the frozen penalty
    -- objective.
    simpa [β, S, c, t, xPath] using method.initialPenaltyObjective_isMinOn_uStar k
  -- Feed the frozen-data minimizer and the explicit determinant witness into the Chapter 5
  -- objective-gap theorem.
  simpa [β, S, c, t, xBar] using
    centralPathApproximateCenter_objectiveGap_le_barrierParameter_add_error_div
      (dom := P) (ν := ν) (F := method.F) c t ht hε xOpt hopt hpath hxBarH happrox

/-- Helper for Theorem 7.14: once the frozen penalty residual at the barycenter is bounded by some
`ε < 1`, the Chapter 5 approximate-center theorem gives the corresponding frozen objective-gap
estimate without further owner setup. -/
private theorem frozenPenaltyApproximateCenter_objectiveGap_le
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) {ε : ℝ}
    (hε : ε < 1)
    (xOpt : closure P)
    (hopt :
      let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
      let c : E := -(S : ℝ) • method.iterateSubgradient 0
      ∀ y : closure P, inner ℝ c (xOpt : E) ≤ inner ℝ c (y : E))
    (happrox :
      let β : ℝ := method.beta (k + 1)
      let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
      let c : E := -(S : ℝ) • method.iterateSubgradient 0
      let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
        have hβ : 0 < β := by
          simpa [β] using (method.beta (k + 1)).2
        exact one_div_nonneg_of_pos hβ⟩
      let xBar : P := ⟨
        (Finset.range (k + 1)).centerMass
          (fun i ↦ (method.stepSize i : ℝ))
          (fun i ↦ (method i : E)),
        iterate_centerMass_mem_domain (method := method) k⟩
      HessianDualLocalNorm.ofDetNeZero method.F (xBar : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xBar.2)
        (method.barrierHessianDetNeZero ν (x := xBar))
        ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (xBar : E))) ≤ ε) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    inner ℝ c (xBar : E) - inner ℝ c (xOpt : E) ≤
      ((ν : ℝ) + ((ε + Real.sqrt (ν : ℝ)) * ε) / (1 - ε)) / (t : ℝ) := by
  -- Route correction: keep the explicit `xBar` determinant witness separate, then delegate to the
  -- witness-parametrized Chapter 5 adapter.
  simpa using
    frozenPenaltyApproximateCenter_objectiveGap_le_ofDetWitness
      (method := method) ν k hε xOpt hopt
      (hxBarH := by
        dsimp
        exact method.barrierHessianDetNeZero ν (x := ⟨
          (Finset.range (k + 1)).centerMass
            (fun i ↦ (method.stepSize i : ℝ))
            (fun i ↦ (method i : E)),
          iterate_centerMass_mem_domain (method := method) k⟩))
      happrox

/-- Helper for Theorem 7.14: specializing the Chapter 5 objective-correction theorem to the
frozen pair `(xBar, xPath)` turns a residual bound at `xBar` into the corresponding one-sided
linear correction estimate toward the exact frozen path point. -/
private theorem centerMassPathObjectiveCorrection_le_errorDiv_ofDetWitness
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) {ε : ℝ} (hε : ε < 1) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    (hxBarH : (fderiv ℝ (∇ method.F) (xBar : E)).det ≠ 0) →
    HessianDualLocalNorm.ofDetNeZero method.F (xBar : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xBar.2)
      hxBarH
      ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (xBar : E))) ≤ ε →
      inner ℝ c (xBar : E) - inner ℝ c (xPath : E) ≤
        β * (((ε + Real.sqrt (ν : ℝ)) * ε) / (1 - ε)) := by
  intro β S c t xBar xPath hxBarH happrox
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have ht : 0 < (t : ℝ) := by
    positivity
  have hpath : IsMinOn (centralPathPenaltyObjective c method.F t) P (xPath : E) := by
    -- Reuse the exact frozen maximizer/minimizer bridge at the frozen data `(c, t)`.
    simpa [β, S, c, t, xPath] using method.initialPenaltyObjective_isMinOn_uStar k
  have hraw :
      inner ℝ c (xBar : E) - inner ℝ c (xPath : E) ≤
        ((ε + Real.sqrt (ν : ℝ)) / (t : ℝ)) * (ε / (1 - ε)) := by
    -- Apply the Chapter 5 correction theorem exactly at the barycenter approximate center.
    exact
      centralPathPenalty_objectiveCorrection_le_error_div
        (dom := P) (ν := ν) (F := method.F) c t (β := ε) ht hε hpath hxBarH happrox
  have hrewrite :
      ((ε + Real.sqrt (ν : ℝ)) / (t : ℝ)) * (ε / (1 - ε)) =
        β * (((ε + Real.sqrt (ν : ℝ)) * ε) / (1 - ε)) := by
    -- Normalize the frozen time `t = 1 / β` back to the Chapter 7 scalar `β`.
    dsimp [t]
    field_simp [hβ_pos.ne', sub_ne_zero.mpr (ne_of_lt hε)]
    ring
  calc
    inner ℝ c (xBar : E) - inner ℝ c (xPath : E) ≤
        ((ε + Real.sqrt (ν : ℝ)) / (t : ℝ)) * (ε / (1 - ε)) := hraw
    _ = β * (((ε + Real.sqrt (ν : ℝ)) * ε) / (1 - ε)) := hrewrite

/-- Helper for Theorem 7.14: specializing the Chapter 5 objective-correction theorem to the
frozen pair `(xBar, xPath)` turns a residual bound at `xBar` into the corresponding one-sided
linear correction estimate toward the exact frozen path point. -/
private theorem centerMassPathObjectiveCorrection_le_errorDiv
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) {ε : ℝ} (hε : ε < 1) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    HessianDualLocalNorm.ofDetNeZero method.F (xBar : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xBar.2)
      (method.barrierHessianDetNeZero ν (x := xBar))
      ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (xBar : E))) ≤ ε →
      inner ℝ c (xBar : E) - inner ℝ c (xPath : E) ≤
        β * (((ε + Real.sqrt (ν : ℝ)) * ε) / (1 - ε)) := by
  intro β S c t xBar xPath happrox
  -- Route correction: keep the determinant witness explicit in the core adapter, and let this
  -- legacy wrapper provide it from the old placeholder route.
  simpa using
    centerMassPathObjectiveCorrection_le_errorDiv_ofDetWitness
      (method := method) ν k hε
      (β := β) (S := S) (c := c) (t := t) (xBar := xBar) (xPath := xPath)
      (hxBarH := method.barrierHessianDetNeZero ν (x := xBar))
      happrox

/-- Helper for Theorem 7.14: the standard square-to-log bridge used after the fixed-`y`
segment estimate. -/
private theorem log_gap_term_le_of_square_gap_bound
    {a b c : ℝ} (ha_nonneg : 0 ≤ a) (hc : 0 < c)
    (ha : a ≤ (Real.sqrt b + Real.sqrt c) ^ (2 : ℕ)) :
    max (Real.log (a / c)) 0 ≤ 2 * Real.log (1 + Real.sqrt (b / c)) := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (b / c) := Real.sqrt_nonneg _
  have hone_le : 1 ≤ 1 + Real.sqrt (b / c) := by
    linarith
  have hs_pos : 0 < 1 + Real.sqrt (b / c) := by
    positivity
  have hrhs_nonneg : 0 ≤ 2 * Real.log (1 + Real.sqrt (b / c)) := by
    have hlog_nonneg : 0 ≤ Real.log (1 + Real.sqrt (b / c)) :=
      Real.log_nonneg hone_le
    nlinarith
  have hsqrtc_pos : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsqrtc_ne : Real.sqrt c ≠ 0 := hsqrtc_pos.ne'
  have hdiv :
      a / c ≤ (1 + Real.sqrt (b / c)) ^ (2 : ℕ) := by
    -- Normalize the square bound by the positive quantity `c`.
    calc
      a / c ≤ ((Real.sqrt b + Real.sqrt c) ^ (2 : ℕ)) / c := by
        exact div_le_div_of_nonneg_right ha hc.le
      _ = ((Real.sqrt b + Real.sqrt c) ^ (2 : ℕ)) / (Real.sqrt c) ^ (2 : ℕ) := by
        rw [Real.sq_sqrt hc.le]
      _ = ((Real.sqrt b + Real.sqrt c) / Real.sqrt c) ^ (2 : ℕ) := by
        field_simp [pow_two, hsqrtc_ne]
      _ = (Real.sqrt b / Real.sqrt c + 1) ^ (2 : ℕ) := by
        congr 1
        field_simp [hsqrtc_ne]
      _ = (Real.sqrt (b / c) + 1) ^ (2 : ℕ) := by
        rw [Real.sqrt_div' b hc.le]
      _ = (1 + Real.sqrt (b / c)) ^ (2 : ℕ) := by
        ring
  by_cases hpos : 0 < a / c
  · -- In the positive case, compare logarithms after the normalization above.
    refine (max_le_iff.mpr ?_)
    constructor
    · calc
        Real.log (a / c) ≤ Real.log ((1 + Real.sqrt (b / c)) ^ (2 : ℕ)) :=
          Real.log_le_log hpos hdiv
        _ = Real.log ((1 + Real.sqrt (b / c)) * (1 + Real.sqrt (b / c))) := by
          rw [pow_two]
        _ = Real.log (1 + Real.sqrt (b / c)) + Real.log (1 + Real.sqrt (b / c)) := by
          rw [Real.log_mul hs_pos.ne' hs_pos.ne']
        _ = 2 * Real.log (1 + Real.sqrt (b / c)) := by
          ring
    · exact hrhs_nonneg
  · have hnonpos : a / c ≤ 0 := le_of_not_gt hpos
    have hquot_nonneg : 0 ≤ a / c := by
      exact div_nonneg ha_nonneg hc.le
    have hquot_zero : a / c = 0 := le_antisymm hnonpos hquot_nonneg
    have hlog_zero : Real.log (a / c) = 0 := by
      simp [hquot_zero]
    simpa [hlog_zero] using hrhs_nonneg

/-- Helper for Theorem 7.14: optimizing the fixed-`y` segment inequality in the large-gap regime
produces the standard logarithmic control of the dual iterate. -/
private theorem pointwise_dualIterate_log_gap_from_segment_barrier
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hν : 0 < (ν : ℝ))
    (k : ℕ) (y : P) :
    method.dualIterate (k + 1) ((y : E) - (method 0 : E)) ≤
      Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1)) +
        (method.beta (k + 1) : ℝ) * (ν : ℝ) *
          (1 +
            max
              (Real.log
                (method.dualIterate (k + 1) ((y : E) - (method 0 : E)) /
                  ((method.beta (k + 1) : ℝ) * (ν : ℝ))))
              0) := by
  let Δ : ℝ := method.dualIterate (k + 1) ((y : E) - (method 0 : E))
  let A : ℝ := Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1))
  let c : ℝ := (method.beta (k + 1) : ℝ) * (ν : ℝ)
  have hc : 0 < c := by
    simpa [c] using mul_pos (method.beta (k + 1)).2 hν
  by_cases hsmall : Δ ≤ c
  · -- In the small-gap regime, the positive correction term already dominates the affine gap.
    have hA_nonneg : 0 ≤ A := by
      simpa [A] using method.uβ_value_nonneg (k + 1)
    have hmax_nonneg : 0 ≤ max (Real.log (Δ / c)) 0 := le_max_right _ _
    have htail_nonneg : 0 ≤ c * max (Real.log (Δ / c)) 0 := by
      exact mul_nonneg hc.le hmax_nonneg
    have hgap : Δ ≤ A + c * (1 + max (Real.log (Δ / c)) 0) := by
      linarith
    simpa [Δ, A, c] using hgap
  · -- Otherwise choose `α = 1 - c / Δ` in the verified segment inequality.
    have hlarge : c < Δ := lt_of_not_ge hsmall
    have hΔ_pos : 0 < Δ := lt_trans hc hlarge
    let α : ℝ := 1 - c / Δ
    have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · have hdiv_lt_one : c / Δ < 1 := by
          rw [div_lt_iff₀ hΔ_pos]
          simpa using hlarge
        dsimp [α]
        linarith
      · have hdiv_pos : 0 < c / Δ := div_pos hc hΔ_pos
        dsimp [α]
        linarith
    have hαineq : α * Δ + c * Real.log (1 - α) ≤ A := by
      simpa [Δ, A, c] using
        method.dualIterate_segment_regularized_gap_bound ν k y hα_mem
    have hone_sub : 1 - α = c / Δ := by
      dsimp [α]
      ring
    -- This choice of `α` converts the segment inequality into the standard log form.
    have hrewrite :
        α * Δ + c * Real.log (1 - α) = Δ - c - c * Real.log (Δ / c) := by
      calc
        α * Δ + c * Real.log (1 - α)
            = (1 - c / Δ) * Δ + c * Real.log (c / Δ) := by
                rw [hone_sub]
        _ = Δ - c + c * Real.log (c / Δ) := by
              field_simp [hΔ_pos.ne']
        _ = Δ - c - c * Real.log (Δ / c) := by
              rw [Real.log_div hc.ne' hΔ_pos.ne', Real.log_div hΔ_pos.ne' hc.ne']
              ring
    have hlog_nonneg : 0 ≤ Real.log (Δ / c) := by
      have hratio_gt_one : 1 < Δ / c := by
        rw [one_lt_div hc]
        simpa using hlarge
      exact Real.log_nonneg hratio_gt_one.le
    have hgap : Δ ≤ A + c * (1 + Real.log (Δ / c)) := by
      rw [hrewrite] at hαineq
      linarith
    have hgap' : Δ ≤ A + c * (1 + max (Real.log (Δ / c)) 0) := by
      simpa [max_eq_left hlog_nonneg] using hgap
    simpa [Δ, A, c] using hgap'

/-- Helper for Theorem 7.14: the same optimized segment argument also yields the square-gap bound
needed to replace the implicit logarithmic term by the explicit `sqrt` expression. -/
private theorem pointwise_dualIterate_square_gap_from_segment_barrier
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hν : 0 < (ν : ℝ))
    (k : ℕ) (y : P) :
    method.dualIterate (k + 1) ((y : E) - (method 0 : E)) ≤
      (Real.sqrt
          (Uβ P method.F (method 0 : E) (method.beta (k + 1))
            (method.dualIterate (k + 1))) +
        Real.sqrt ((method.beta (k + 1) : ℝ) * (ν : ℝ))) ^ (2 : ℕ) := by
  let Δ : ℝ := method.dualIterate (k + 1) ((y : E) - (method 0 : E))
  let A : ℝ := Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1))
  let c : ℝ := (method.beta (k + 1) : ℝ) * (ν : ℝ)
  have hc : 0 < c := by
    simpa [c] using mul_pos (method.beta (k + 1)).2 hν
  have hA : 0 ≤ A := by
    simpa [A] using method.uβ_value_nonneg (k + 1)
  by_cases hsmall : Δ ≤ c
  · -- If the affine gap is already at most `c = β_(k+1) ν`, the square bound is immediate.
    have hc_bound : c ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      nlinarith [hA, hc.le, Real.sq_sqrt hA, Real.sq_sqrt hc.le,
        Real.sqrt_nonneg A, Real.sqrt_nonneg c]
    have hbound : Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      linarith
    simpa [Δ, A, c] using hbound
  · -- Otherwise choose `1 - α = sqrt c / sqrt Δ` and use `-log (1 - α) ≤ α / (1 - α)`.
    have hlarge : c < Δ := lt_of_not_ge hsmall
    have hΔ_pos : 0 < Δ := lt_trans hc hlarge
    let α : ℝ := 1 - Real.sqrt c / Real.sqrt Δ
    have hsqrt_ratio_lt_one : Real.sqrt c / Real.sqrt Δ < 1 := by
      have hsqrt_lt : Real.sqrt c < Real.sqrt Δ := Real.sqrt_lt_sqrt hc.le hlarge
      exact (div_lt_one (Real.sqrt_pos.2 hΔ_pos)).2 hsqrt_lt
    have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · dsimp [α]
        linarith
      · dsimp [α]
        have hratio_pos : 0 < Real.sqrt c / Real.sqrt Δ := by
          positivity
        linarith
    have hsegment : α * Δ + c * Real.log (1 - α) ≤ A := by
      simpa [Δ, A, c] using
        method.dualIterate_segment_regularized_gap_bound ν k y hα_mem
    have hone_sub_alpha : 1 - α = Real.sqrt c / Real.sqrt Δ := by
      dsimp [α]
      ring
    have hlog_bound : -Real.log (1 - α) ≤ α / (1 - α) :=
      neg_log_one_sub_le_div_of_mem_Ico hα_mem
    have hlog_term : -c * Real.log (1 - α) ≤ c * α / (1 - α) := by
      have hmul := mul_le_mul_of_nonneg_left hlog_bound hc.le
      have hmul' : c * (-Real.log (1 - α)) ≤ c * (α / (1 - α)) := hmul
      convert hmul' using 1
      · ring
      · ring
    have hmain : α * Δ - c * α / (1 - α) ≤ A := by
      nlinarith [hsegment, hlog_term]
    -- Rewrite the square-root choice of `α` into the exact quadratic expression.
    have hexpr :
        α * Δ - c * α / (1 - α) = (Real.sqrt Δ - Real.sqrt c) ^ (2 : ℕ) := by
      let s : ℝ := Real.sqrt Δ
      let t : ℝ := Real.sqrt c
      have hs_pos : 0 < s := by
        dsimp [s]
        exact Real.sqrt_pos.2 hΔ_pos
      have ht_pos : 0 < t := by
        dsimp [t]
        exact Real.sqrt_pos.2 hc
      have hs_ne : s ≠ 0 := hs_pos.ne'
      have ht_ne : t ≠ 0 := ht_pos.ne'
      have hα_def : α = 1 - t / s := by
        dsimp [α, s, t]
      have hΔ_sq : Δ = s ^ (2 : ℕ) := by
        dsimp [s]
        simpa [pow_two] using (Real.sq_sqrt hΔ_pos.le).symm
      have hc_sq : c = t ^ (2 : ℕ) := by
        dsimp [t]
        simpa [pow_two] using (Real.sq_sqrt hc.le).symm
      have hexpr_st :
          α * Δ - c * α / (1 - α) = (s - t) ^ (2 : ℕ) := by
        rw [hα_def, hΔ_sq, hc_sq]
        have hdenom : 1 - (1 - t / s) = t / s := by
          ring
        rw [hdenom]
        field_simp [hs_ne, ht_ne]
      simpa [s, t] using hexpr_st
    have hsquare : (Real.sqrt Δ - Real.sqrt c) ^ (2 : ℕ) ≤ A := by
      rw [← hexpr]
      exact hmain
    have hsqrt_sub_nonneg : 0 ≤ Real.sqrt Δ - Real.sqrt c := by
      exact sub_nonneg.mpr (Real.sqrt_le_sqrt hlarge.le)
    have hsqrt_le : Real.sqrt Δ - Real.sqrt c ≤ Real.sqrt A := by
      exact (Real.le_sqrt hsqrt_sub_nonneg hA).2 (by simpa [pow_two] using hsquare)
    have hsqrt_sum : Real.sqrt Δ ≤ Real.sqrt A + Real.sqrt c := by
      linarith
    have hbound : Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      have hsum_nonneg : 0 ≤ Real.sqrt A + Real.sqrt c := by
        positivity
      have hsq' : (Real.sqrt Δ) ^ (2 : ℕ) ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
        nlinarith [hsqrt_sum, hsum_nonneg, Real.sqrt_nonneg Δ]
      simpa [pow_two, Real.sq_sqrt hΔ_pos.le] using hsq'
    simpa [Δ, A, c] using hbound

/-- Helper for Theorem 7.14: once the fixed-`y` segment inequality is optimized and the square-gap
bridge is inserted, the dual iterate is controlled by the explicit Chapter 7 logarithmic term in
`Uβ`. -/
private theorem pointwise_dualIterate_bound_from_segment_barrier
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hν : 0 < (ν : ℝ))
    (k : ℕ) (y : P) :
    method.dualIterate (k + 1) ((y : E) - (method 0 : E)) ≤
      Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1)) +
        (method.beta (k + 1) : ℝ) * (ν : ℝ) *
          (1 +
            2 * Real.log
              (1 +
                Real.sqrt
                  (Uβ P method.F (method 0 : E) (method.beta (k + 1))
                    (method.dualIterate (k + 1)) /
                    ((method.beta (k + 1) : ℝ) * (ν : ℝ))))) := by
  let Δ : ℝ := method.dualIterate (k + 1) ((y : E) - (method 0 : E))
  let A : ℝ := Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1))
  let c : ℝ := (method.beta (k + 1) : ℝ) * (ν : ℝ)
  have hc : 0 < c := by
    simpa [c] using mul_pos (method.beta (k + 1)).2 hν
  have hA : 0 ≤ A := by
    simpa [A] using method.uβ_value_nonneg (k + 1)
  have hlogGap :
      Δ ≤ A + c * (1 + max (Real.log (Δ / c)) 0) := by
    simpa [Δ, A, c] using
      method.pointwise_dualIterate_log_gap_from_segment_barrier ν hν k y
  have hsquareGap : Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
    simpa [Δ, A, c] using
      method.pointwise_dualIterate_square_gap_from_segment_barrier ν hν k y
  by_cases hΔ_nonneg : 0 ≤ Δ
  · -- Upgrade the implicit `max(log(Δ / c), 0)` term to the explicit square-root expression.
    have hlogTerm :
        max (Real.log (Δ / c)) 0 ≤ 2 * Real.log (1 + Real.sqrt (A / c)) :=
      log_gap_term_le_of_square_gap_bound hΔ_nonneg hc hsquareGap
    have herror :
        c * (1 + max (Real.log (Δ / c)) 0) ≤
          c * (1 + 2 * Real.log (1 + Real.sqrt (A / c))) := by
      have hinside :
          1 + max (Real.log (Δ / c)) 0 ≤
            1 + 2 * Real.log (1 + Real.sqrt (A / c)) := by
        linarith
      exact mul_le_mul_of_nonneg_left hinside hc.le
    calc
      Δ ≤ A + c * (1 + max (Real.log (Δ / c)) 0) := hlogGap
      _ ≤ A + c * (1 + 2 * Real.log (1 + Real.sqrt (A / c))) := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left herror A
  · -- If the affine gap is already nonpositive, the right-hand side is nonnegative.
    have hΔ_nonpos : Δ ≤ 0 := le_of_not_ge hΔ_nonneg
    have hlog_nonneg : 0 ≤ Real.log (1 + Real.sqrt (A / c)) := by
      have hone_le : 1 ≤ 1 + Real.sqrt (A / c) := by
        have hsqrt_nonneg : 0 ≤ Real.sqrt (A / c) := Real.sqrt_nonneg _
        linarith
      exact Real.log_nonneg hone_le
    have hrhs_nonneg : 0 ≤ A + c * (1 + 2 * Real.log (1 + Real.sqrt (A / c))) := by
      have hinside_nonneg : 0 ≤ 1 + 2 * Real.log (1 + Real.sqrt (A / c)) := by
        nlinarith
      have hterm_nonneg : 0 ≤ c * (1 + 2 * Real.log (1 + Real.sqrt (A / c))) := by
        exact mul_nonneg hc.le hinside_nonneg
      linarith
    exact le_trans hΔ_nonpos hrhs_nonneg

/-- Helper for Theorem 7.14: when the barrier parameter vanishes, the segment inequality already
forces every affine gap `s_(k+1)(y - x₀)` below the smoothed value `Uβ`, so the Chapter 7
telescope closes directly without any logarithmic correction term. -/
private theorem maximalGap_zero_barrier_parameter_branch
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hν0 : ν = 0)
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (hβ_mono : ∀ i : ℕ, (method.beta i : ℝ) ≤ method.beta (i + 1))
    (k : ℕ) :
    method.maximalGap k ≤ method.accumulatedOmegaStarError hH hω k := by
  let U :=
    Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1))
  let correction : ℝ :=
    ∑ i ∈ Finset.range (k + 1),
      (method.stepSize i : ℝ) *
        method.dualSubgradient (method i) ((method i : E) - (method 0 : E))
  have hpointwise :
      ∀ y : P, method.dualIterate (k + 1) ((y : E) - (method 0 : E)) ≤ U := by
    intro y
    let Δ : ℝ := method.dualIterate (k + 1) ((y : E) - (method 0 : E))
    by_cases hΔU : Δ ≤ U
    · simpa [Δ, U] using hΔU
    · have hU_nonneg : 0 ≤ U := by
        simpa [U] using method.uβ_value_nonneg (k + 1)
      have hU_lt_Δ : U < Δ := lt_of_not_ge hΔU
      have hΔ_pos : 0 < Δ := lt_of_le_of_lt hU_nonneg hU_lt_Δ
      let α : ℝ := (U + Δ) / (2 * Δ)
      have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := by
        constructor
        · have hnum_nonneg : 0 ≤ U + Δ := by
            linarith
          have hden_nonneg : 0 ≤ 2 * Δ := by
            linarith
          exact div_nonneg hnum_nonneg hden_nonneg
        · have hden_pos : 0 < 2 * Δ := by
            linarith
          have hnum_lt_den : U + Δ < 2 * Δ := by
            linarith
          exact (div_lt_iff₀ hden_pos).2 hnum_lt_den
      have hsegment : α * Δ ≤ U := by
        -- With `ν = 0`, the barrier correction in the segment inequality disappears.
        have hseg := method.dualIterate_segment_regularized_gap_bound ν k y hα_mem
        simpa [Δ, U, α, hν0, mul_assoc, mul_left_comm, mul_comm] using hseg
      have hα_mul : α * Δ = (U + Δ) / 2 := by
        dsimp [α]
        field_simp [hΔ_pos.ne']
        ring
      have hcontr : False := by
        rw [hα_mul] at hsegment
        linarith
      exact False.elim hcontr
  have hgap :
      method.maximalGap k ≤ ((U - correction : ℝ) : EReal) := by
    -- The pointwise `Δ ≤ U` bound feeds directly into the `sSup` bridge for `method.maximalGap`.
    exact method.maximalGap_le_of_dualIterate_pointwise_bound k hpointwise
  have hregularized :
      U - correction ≤ method.accumulatedOmegaStarError hH hω k := by
    -- The Chapter 7 telescope already controls the corrected smoothed value by `A_k`.
    simpa [U, correction] using
      method.regularized_value_minus_correction_le_accumulated_omegaStar
        ν hH hω hβ_mono k
  have hregularized_ereal :
      ((U - correction : ℝ) : EReal) ≤
        (method.accumulatedOmegaStarError hH hω k : EReal) := by
    exact_mod_cast hregularized
  exact le_trans hgap hregularized_ereal

/-- Helper for Theorem 7.14: concavity lets the correction prefix be dominated by the fixed
initial owner evaluated at the iterate barycenter. -/
private theorem correction_prefix_le_initial_linear_at_centerMass
    [IsStandardSelfConcordantOn P method.F]
    (k : ℕ) :
    let x0 : E := method 0
    let g0 := method.dualSubgradient (method 0)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    ∑ i ∈ Finset.range (k + 1),
      (method.stepSize i : ℝ) *
        method.dualSubgradient (method i) ((method i : E) - x0) ≤
      S * g0 ((xBar : E) - x0) := by
  let x0 : E := method 0
  let g0 := method.dualSubgradient (method 0)
  let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
  let xBar : P := ⟨
    (Finset.range (k + 1)).centerMass
      (fun i ↦ (method.stepSize i : ℝ))
      (fun i ↦ (method i : E)),
    iterate_centerMass_mem_domain (method := method) k⟩
  have hS_pos : 0 < S := by
    dsimp [S]
    have hzero_mem : 0 ∈ Finset.range (k + 1) := by
      simp
    have hzero_le :
        (method.stepSize 0 : ℝ) ≤
          ∑ i ∈ Finset.range (k + 1), (method.stepSize i : ℝ) := by
      simpa using
        Finset.single_le_sum
          (fun i hi ↦ (method.stepSize i).2.le)
          hzero_mem
    exact lt_of_lt_of_le (method.stepSize 0).2 hzero_le
  have hterm_le :
      ∀ i ∈ Finset.range (k + 1),
        (method.stepSize i : ℝ) *
            method.dualSubgradient (method i) ((method i : E) - x0) ≤
          (method.stepSize i : ℝ) * g0 ((method i : E) - x0) := by
    intro i hi
    have hgi :=
      (isConcaveSubgradientAt_iff f (method i : E) (method.subgradient (method i))).1
        (method.subgradient_spec (method i))
    have hg0 :=
      (isConcaveSubgradientAt_iff f x0 (method.subgradient (method 0))).1
        (method.subgradient_spec (method 0))
    have hleft :
        method.dualSubgradient (method i) ((method i : E) - x0) ≤
          f (method i : E) - f x0 := by
      have hsupport :
          f x0 ≤
            f (method i : E) +
              method.dualSubgradient (method i) (x0 - (method i : E)) := by
        simpa [DualBarrierSubgradientMethod.dualSubgradient_eq,
          InnerProductSpace.toDual_apply_apply] using hgi x0
      rw [show x0 - (method i : E) = -((method i : E) - x0) by abel,
        map_neg] at hsupport
      linarith
    have hright :
        f (method i : E) - f x0 ≤ g0 ((method i : E) - x0) := by
      have hsupport :
          f (method i : E) ≤ f x0 + g0 ((method i : E) - x0) := by
        simpa [x0, g0, DualBarrierSubgradientMethod.dualSubgradient_eq,
          InnerProductSpace.toDual_apply_apply] using hg0 (method i : E)
      linarith
    exact mul_le_mul_of_nonneg_left (le_trans hleft hright) (method.stepSize i).2.le
  have hsum_le :
      ∑ i ∈ Finset.range (k + 1),
        (method.stepSize i : ℝ) *
          method.dualSubgradient (method i) ((method i : E) - x0) ≤
        ∑ i ∈ Finset.range (k + 1),
          (method.stepSize i : ℝ) * g0 ((method i : E) - x0) := by
    exact Finset.sum_le_sum hterm_le
  have hxBar_smul :
      S • (xBar : E) =
        ∑ i ∈ Finset.range (k + 1), (method.stepSize i : ℝ) • (method i : E) := by
    -- Expand the center of mass and cancel the positive total weight `S`.
    dsimp [S, xBar]
    rw [barrierSubgradientWeightSum_def, Finset.centerMass, smul_smul, inv_mul_cancel₀ hS_pos.ne',
      one_smul]
  have hxBar_sub_smul :
      S • ((xBar : E) - x0) =
        ∑ i ∈ Finset.range (k + 1),
          (method.stepSize i : ℝ) • ((method i : E) - x0) := by
    have hx0_smul :
        S • x0 = ∑ i ∈ Finset.range (k + 1), (method.stepSize i : ℝ) • x0 := by
      dsimp [S]
      rw [barrierSubgradientWeightSum_def, Finset.sum_smul]
    -- Push the common base point `x₀` through the weighted average.
    calc
      S • ((xBar : E) - x0)
          = S • (xBar : E) - S • x0 := by rw [smul_sub]
      _ =
          ∑ i ∈ Finset.range (k + 1), (method.stepSize i : ℝ) • (method i : E) -
            S • x0 := by rw [hxBar_smul]
      _ =
          ∑ i ∈ Finset.range (k + 1), (method.stepSize i : ℝ) • (method i : E) -
            ∑ i ∈ Finset.range (k + 1), (method.stepSize i : ℝ) • x0 := by
              rw [hx0_smul]
      _ =
          ∑ i ∈ Finset.range (k + 1),
            ((method.stepSize i : ℝ) • (method i : E) -
              (method.stepSize i : ℝ) • x0) := by
              rw [Finset.sum_sub_distrib]
      _ =
          ∑ i ∈ Finset.range (k + 1),
            (method.stepSize i : ℝ) • ((method i : E) - x0) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [smul_sub]
  have happly :
      S * g0 ((xBar : E) - x0) =
        ∑ i ∈ Finset.range (k + 1),
          (method.stepSize i : ℝ) * g0 ((method i : E) - x0) := by
    -- Apply the fixed initial owner to the barycenter identity.
    simpa using congrArg g0 hxBar_sub_smul
  calc
    ∑ i ∈ Finset.range (k + 1),
      (method.stepSize i : ℝ) *
        method.dualSubgradient (method i) ((method i : E) - x0)
        ≤
      ∑ i ∈ Finset.range (k + 1),
        (method.stepSize i : ℝ) * g0 ((method i : E) - x0) := hsum_le
    _ = S * g0 ((xBar : E) - x0) := happly.symm

/-- Helper for Theorem 7.14: the iterate barycenter stays within the standard analytic-center
radius `ν + 2 √ν` around the initial iterate `method 0`. -/
private theorem initialCenterMassLocalNorm_le_barrierParameter_addTwoSqrt
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F] (k : ℕ) :
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    ‖(xBar : E) - (method 0 : E)‖[method.F; (method 0 : E)] ≤
      (ν : ℝ) + 2 * Real.sqrt (ν : ℝ) := by
  let xBar : P := ⟨
    (Finset.range (k + 1)).centerMass
      (fun i ↦ (method.stepSize i : ℝ))
      (fun i ↦ (method i : E)),
    iterate_centerMass_mem_domain (method := method) k⟩
  have hgrad_zero : ∇ method.F (method 0 : E) = 0 :=
    method.initial_iterate_gradient_eq_zero
  have hinner_nonneg :
      inner ℝ (∇ method.F (method 0 : E)) ((xBar : E) - (method 0 : E)) ≥ 0 := by
    simpa [hgrad_zero]
  -- The initial iterate is an analytic center, so the Chapter 5 radius theorem applies directly
  -- to the barycenter of the iterates.
  simpa [xBar] using
    (inferInstance : IsSelfConcordantBarrierOnWith P ν method.F)
      .hessianLocalNorm_sub_le_barrierParameter_add_two_sqrt_of_gradient_inner_nonneg
        (x := (method 0 : E))
        (y := (xBar : E))
        (hx := (method 0).2)
        (hy := xBar.2)
        hinner_nonneg

/-- Helper for Theorem 7.14: barycenter compression plus the Chapter 5 analytic-center radius
estimate yields a linear bound for the correction prefix. -/
private theorem initialCorrectionLinearControl
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let x0 : E := method 0
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F x0
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    ∑ i ∈ Finset.range (k + 1),
      (method.stepSize i : ℝ) *
        method.dualSubgradient (method i) ((method i : E) - x0) ≤
      S * δ0 * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) := by
  let x0 : E := method 0
  let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
  let δ0 :=
    HessianDualLocalNorm.ofDetNeZero method.F x0
      (method.iterate_hessian_isPositive 0) (hH 0)
      (method.dualSubgradient (method 0))
  let xBar : P := ⟨
    (Finset.range (k + 1)).centerMass
      (fun i ↦ (method.stepSize i : ℝ))
      (fun i ↦ (method i : E)),
    iterate_centerMass_mem_domain (method := method) k⟩
  have hprefix :
      ∑ i ∈ Finset.range (k + 1),
        (method.stepSize i : ℝ) *
          method.dualSubgradient (method i) ((method i : E) - x0) ≤
        S * method.dualSubgradient (method 0) ((xBar : E) - x0) := by
    -- First compress the moving correction prefix to the frozen initial covector at the
    -- iterate barycenter.
    simpa [x0, S, xBar] using
      correction_prefix_le_initial_linear_at_centerMass (method := method) k
  have hpair :
      method.dualSubgradient (method 0) ((xBar : E) - x0) ≤
        δ0 * ‖(xBar : E) - x0‖[method.F; x0] := by
    have habs :
        |inner ℝ (method.iterateSubgradient 0) ((xBar : E) - x0)| ≤
          δ0 * ‖(xBar : E) - x0‖[method.F; x0] := by
      -- Evaluate the fixed initial covector by the Chapter 5 dual/local Cauchy inequality.
      simpa [x0, δ0, DualBarrierSubgradientMethod.dualSubgradient_eq,
        DualBarrierSubgradientMethod.iterateSubgradient_eq,
        InnerProductSpace.toDual_apply_apply] using
        abs_inner_le_hessianDualLocalNorm_mul_hessianLocalNorm_of_detNeZero
          (F := method.F)
          (x := x0)
          (v := method.iterateSubgradient 0)
          (z := (xBar : E) - x0)
          (method.iterate_hessian_isPositive 0)
          (hH 0)
    exact le_trans (le_abs_self _) habs
  have hlocal :
      ‖(xBar : E) - x0‖[method.F; x0] ≤ (ν : ℝ) + 2 * Real.sqrt (ν : ℝ) := by
    -- The barycenter lies in the analytic-center radius ball around `method 0`.
    simpa [x0, xBar] using method.initialCenterMassLocalNorm_le_barrierParameter_addTwoSqrt ν k
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    rw [barrierSubgradientWeightSum_def]
    exact Finset.sum_nonneg fun i hi ↦ (method.stepSize i).2.le
  have hδ0_nonneg : 0 ≤ δ0 := by
    -- The Hessian dual local norm at the initial iterate is nonnegative.
    dsimp [δ0]
    exact dualLocalNorm_nonneg method.F x0
      (method.iterate_hessian_isPositive 0)
      (hessian_isInvertible_of_det_ne_zero (hH 0))
      (method.dualSubgradient (method 0))
  have hpair_scaled :
      S * method.dualSubgradient (method 0) ((xBar : E) - x0) ≤
        S * (δ0 * ‖(xBar : E) - x0‖[method.F; x0]) := by
    exact mul_le_mul_of_nonneg_left hpair hS_nonneg
  have hlocal_scaled :
      S * (δ0 * ‖(xBar : E) - x0‖[method.F; x0]) ≤
        S * (δ0 * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ))) := by
    have hδ0_scaled :
        δ0 * ‖(xBar : E) - x0‖[method.F; x0] ≤
          δ0 * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hlocal hδ0_nonneg
    exact mul_le_mul_of_nonneg_left hδ0_scaled hS_nonneg
  exact le_trans hprefix <| le_trans hpair_scaled <| by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hlocal_scaled

/-- Helper for Theorem 7.14: the optimized segment argument for the frozen initial covector
controls the barycenter correction by the corresponding frozen smoothed value. -/
private theorem initialFrozenLinearFunctional_squareAtCenterMass
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hν : 0 < (ν : ℝ))
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
      (Real.sqrt (Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0) +
        Real.sqrt (β * (ν : ℝ))) ^ (2 : ℕ) := by
  let x0 : E := method 0
  let βSub := method.beta (k + 1)
  let β : ℝ := βSub
  let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
  let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
  let xBar : P := ⟨
    (Finset.range (k + 1)).centerMass
      (fun i ↦ (method.stepSize i : ℝ))
      (fun i ↦ (method i : E)),
    iterate_centerMass_mem_domain (method := method) k⟩
  let ℓ : AffineMap ℝ E ℝ := s0.toAffineMap
  let Δ : ℝ := S * method.dualSubgradient (method 0) ((xBar : E) - x0)
  let A : ℝ := Uβ P method.F x0 βSub s0
  let c : ℝ := β * (ν : ℝ)
  have hβ : 0 < β := by
    simpa [β] using βSub.2
  have hc : 0 < c := by
    simpa [c] using mul_pos hβ hν
  have hx0_argmin : x0 ∈ argmin[P] method.F :=
    method.initial_iterate_is_barrier_argmin
  have hpayoff_max :
      IsMaxOn
        (fun v : E ↦
          s0 (v - x0) -
            β * (method.F v - method.F x0))
        P
        (method.uStar βSub s0 : E) := by
    simpa [x0, β] using method.uStar_isMaxOn (x0 := x0) (β := βSub) (s := s0)
  have hscore_max :
      IsMaxOn (fun v : E ↦ s0 v - β * method.F v) P (method.uStar βSub s0 : E) := by
    exact
      (isMaxOn_shifted_score_iff_textbook_payoff
        (hatP := P) (F := method.F) (x0 := x0) (β := βSub) (s := s0)
        (u := (method.uStar βSub s0 : E))).2 hpayoff_max
  have hxBeta_max :
      IsMaxOn (affineBarrierRegularizedPayoff x0 β ℓ method.F) P (method.uStar βSub s0 : E) := by
    refine isMaxOn_iff.mpr ?_
    intro y hy
    have hymax := (isMaxOn_iff.mp hpayoff_max) y hy
    -- Reinsert the common base-point constant to move from the shifted score to the Chapter 7
    -- regularized payoff owner.
    simpa [ℓ, x0, β, affineBarrierRegularizedPayoff_def, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hymax
  have hA_nonneg : 0 ≤ A := by
    simpa [A] using method.uβ_value_nonneg (k + 1)
  have hconv : Convex ℝ P :=
    (inferInstance : IsStandardSelfConcordantOn P method.F).convex_domain
  have hsegment_mem :
      ∀ ⦃x : E⦄, x ∈ P → ∀ ⦃a : ℝ⦄, a ∈ Set.Ico (0 : ℝ) 1 →
        x0 + a • (x - x0) ∈ P := by
    intro x hx a ha
    have hline_mem : AffineMap.lineMap x0 x a ∈ P := by
      -- Convexity keeps the full chord from the initial iterate to any feasible point in `P`.
      simpa [AffineMap.lineMap_apply_module] using
        hconv.lineMap_mem (method 0).2 hx ⟨ha.1, ha.2.le⟩
    simpa [AffineMap.lineMap_apply_module', add_comm, x0] using hline_mem
  by_cases hsmall : Δ ≤ c
  · -- If the frozen affine gap is already below `β ν`, the quadratic bound is immediate.
    have hc_bound : c ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      nlinarith [hA_nonneg, hc.le, Real.sq_sqrt hA_nonneg, Real.sq_sqrt hc.le,
        Real.sqrt_nonneg A, Real.sqrt_nonneg c]
    have hbound : Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      linarith
    simpa [Δ, A, c, β, S, s0, xBar] using hbound
  · -- Otherwise optimize the segment inequality at `1 - α = sqrt(c / Δ)`.
    have hlarge : c < Δ := lt_of_not_ge hsmall
    have hΔ_pos : 0 < Δ := lt_trans hc hlarge
    let α : ℝ := 1 - Real.sqrt c / Real.sqrt Δ
    have hsqrt_ratio_lt_one : Real.sqrt c / Real.sqrt Δ < 1 := by
      have hsqrt_lt : Real.sqrt c < Real.sqrt Δ := Real.sqrt_lt_sqrt hc.le hlarge
      exact (div_lt_one (Real.sqrt_pos.2 hΔ_pos)).2 hsqrt_lt
    have hα_mem : α ∈ Set.Ico (0 : ℝ) 1 := by
      constructor
      · dsimp [α]
        linarith
      · dsimp [α]
        have hratio_pos : 0 < Real.sqrt c / Real.sqrt Δ := by
          positivity
        linarith
    have hsegment :
        α * Δ + c * Real.log (1 - α) ≤ A := by
      have hraw :=
        regularized_gap_bound_along_segment
          (x0 := x0) (β := β) (ℓ := ℓ) (F := method.F) (P := P)
          (xStar := (xBar : E)) (xBeta := (method.uStar βSub s0 : E)) (v := (ν : ℝ))
          hβ xBar.2 hxBeta_max hsegment_mem
          (fun {x} hx {a} ha ↦ method.segment_barrier_bound_from_initial_argmin ν ⟨x, hx⟩ ha)
          hα_mem
      -- Rewrite the generic regularized-gap inequality into the frozen `Uβ` surface.
      simpa [Δ, A, c, ℓ, x0, β, S, s0, xBar, method.uβ_value_at_uStar βSub s0, map_sub,
        affineBarrierRegularizedPayoff_def, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using hraw
    have hone_sub_alpha : 1 - α = Real.sqrt c / Real.sqrt Δ := by
      dsimp [α]
      ring
    have hlog_bound : -Real.log (1 - α) ≤ α / (1 - α) :=
      neg_log_one_sub_le_div_of_mem_Ico hα_mem
    have hlog_term : -c * Real.log (1 - α) ≤ c * α / (1 - α) := by
      have hmul := mul_le_mul_of_nonneg_left hlog_bound hc.le
      have hmul' : c * (-Real.log (1 - α)) ≤ c * (α / (1 - α)) := hmul
      convert hmul' using 1
      · ring
      · ring
    have hmain : α * Δ - c * α / (1 - α) ≤ A := by
      nlinarith [hsegment, hlog_term]
    -- Rewrite the optimized scalar choice into the explicit square-gap expression.
    have hexpr :
        α * Δ - c * α / (1 - α) = (Real.sqrt Δ - Real.sqrt c) ^ (2 : ℕ) := by
      let s : ℝ := Real.sqrt Δ
      let t : ℝ := Real.sqrt c
      have hs_pos : 0 < s := by
        dsimp [s]
        exact Real.sqrt_pos.2 hΔ_pos
      have ht_pos : 0 < t := by
        dsimp [t]
        exact Real.sqrt_pos.2 hc
      have hs_ne : s ≠ 0 := hs_pos.ne'
      have ht_ne : t ≠ 0 := ht_pos.ne'
      have hα_def : α = 1 - t / s := by
        dsimp [α, s, t]
      have hΔ_sq : Δ = s ^ (2 : ℕ) := by
        dsimp [s]
        simpa [pow_two] using (Real.sq_sqrt hΔ_pos.le).symm
      have hc_sq : c = t ^ (2 : ℕ) := by
        dsimp [t]
        simpa [pow_two] using (Real.sq_sqrt hc.le).symm
      have hexpr_st :
          α * Δ - c * α / (1 - α) = (s - t) ^ (2 : ℕ) := by
        rw [hα_def, hΔ_sq, hc_sq]
        have hdenom : 1 - (1 - t / s) = t / s := by
          ring
        rw [hdenom]
        field_simp [hs_ne, ht_ne]
      simpa [s, t] using hexpr_st
    have hsquare : (Real.sqrt Δ - Real.sqrt c) ^ (2 : ℕ) ≤ A := by
      rw [← hexpr]
      exact hmain
    have hsqrt_sub_nonneg : 0 ≤ Real.sqrt Δ - Real.sqrt c := by
      exact sub_nonneg.mpr (Real.sqrt_le_sqrt hlarge.le)
    have hsqrt_le : Real.sqrt Δ - Real.sqrt c ≤ Real.sqrt A := by
      exact (Real.le_sqrt hsqrt_sub_nonneg hA_nonneg).2 (by simpa [pow_two] using hsquare)
    have hsqrt_sum : Real.sqrt Δ ≤ Real.sqrt A + Real.sqrt c := by
      linarith
    have hbound : Δ ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
      have hsum_nonneg : 0 ≤ Real.sqrt A + Real.sqrt c := by
        positivity
      have hsq' : (Real.sqrt Δ) ^ (2 : ℕ) ≤ (Real.sqrt A + Real.sqrt c) ^ (2 : ℕ) := by
        nlinarith [hsqrt_sum, hsum_nonneg, Real.sqrt_nonneg Δ]
      simpa [pow_two, Real.sq_sqrt hΔ_pos.le] using hsq'
    simpa [Δ, A, c, β, S, s0, xBar] using hbound

/-- Helper for Theorem 7.14: the exact frozen residual at `method 0` turns the
`x₀ → xPath` linear term into a quadratic `ρ² / (1 - ρ)` bound. -/
private theorem frozenInitialPathLinearGap_le_rhoSquareDiv
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    let ρ : ℝ := (S / β) * δ0
    ρ < 1 →
      inner ℝ c (method 0 : E) - inner ℝ c (xPath : E) ≤
        β * (ρ ^ (2 : ℕ) / (1 - ρ)) := by
  intro β S δ0 c t xPath ρ hρ
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    rw [barrierSubgradientWeightSum_def]
    exact Finset.sum_nonneg fun i hi ↦ (method.stepSize i).2.le
  have hδ0_nonneg : 0 ≤ δ0 := by
    -- The frozen initial dual local norm is nonnegative by construction.
    dsimp [δ0]
    exact dualLocalNorm_nonneg method.F (method 0 : E)
      (method.iterate_hessian_isPositive 0)
      (hessian_isInvertible_of_det_ne_zero (hH 0))
      (method.dualSubgradient (method 0))
  have hpath :
      IsMinOn (centralPathPenaltyObjective c method.F t) P (xPath : E) := by
    -- Reuse the frozen-maximizer/penalty-minimizer bridge at the exact frozen data.
    simpa [β, S, c, t, xPath] using method.initialPenaltyObjective_isMinOn_uStar k
  have happrox :
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (method 0 : E))) ≤ ρ := by
    -- The residual at the analytic center is exactly `ρ`.
    rw [method.initialPenaltyApproxCenterResidualEq hH k]
  have hdist :
      ‖(method 0 : E) - (xPath : E)‖[method.F; (method 0 : E)] ≤ ρ / (1 - ρ) := by
    -- Apply the Chapter 5 local-distance theorem at `x = method 0`.
    exact
      centralPathPenalty_localNorm_distance_le_beta_div_one_sub
        (dom := P) (ν := ν) (F := method.F) c t hρ hpath (hH 0) happrox
  have hc_norm :
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        ((InnerProductSpace.toDualMap ℝ E) c) =
        S * δ0 := by
    have hcovector :
        (InnerProductSpace.toDualMap ℝ E) c =
          -((S : ℝ) • method.dualSubgradient (method 0)) := by
      -- Rewrite the frozen penalty vector as the negative scaled initial covector.
      simp [c, DualBarrierSubgradientMethod.dualSubgradient_eq,
        DualBarrierSubgradientMethod.iterateSubgradient_eq]
    have hsmul :
        HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
          (method.iterate_hessian_isPositive 0) (hH 0)
          ((S : ℝ) • method.dualSubgradient (method 0)) =
          S * δ0 := by
      -- Positive homogeneity extracts the nonnegative scalar `S`.
      simpa [δ0, HessianDualLocalNorm.ofDetNeZero, smul_eq_mul] using
        dualLocalNorm_smul_nonneg method.F (method 0 : E)
          (method.iterate_hessian_isPositive 0)
          (hessian_isInvertible_of_det_ne_zero (hH 0))
          (method.dualSubgradient (method 0))
          hS_nonneg
    rw [hcovector, hessianDualLocalNorm_ofDetNeZero_neg
      (method.iterate_hessian_isPositive 0) (hH 0)]
    exact hsmul
  have hpair :
      inner ℝ c (method 0 : E) - inner ℝ c (xPath : E) ≤
        S * δ0 * (ρ / (1 - ρ)) := by
    have habs :
        |inner ℝ c ((method 0 : E) - (xPath : E))| ≤
          HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
            (method.iterate_hessian_isPositive 0) (hH 0)
            ((InnerProductSpace.toDualMap ℝ E) c) *
              ‖(method 0 : E) - (xPath : E)‖[method.F; (method 0 : E)] := by
      -- Dual/local Cauchy converts the frozen linear term into dual norm times distance.
      simpa using
        abs_inner_le_hessianDualLocalNorm_mul_hessianLocalNorm_of_detNeZero
          (F := method.F)
          (x := (method 0 : E))
          (v := c)
          (z := (method 0 : E) - (xPath : E))
          (method.iterate_hessian_isPositive 0)
          (hH 0)
    have hscaled :
        HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
          (method.iterate_hessian_isPositive 0) (hH 0)
          ((InnerProductSpace.toDualMap ℝ E) c) *
            ‖(method 0 : E) - (xPath : E)‖[method.F; (method 0 : E)] ≤
          S * δ0 * (ρ / (1 - ρ)) := by
      rw [hc_norm]
      exact mul_le_mul_of_nonneg_left hdist (mul_nonneg hS_nonneg hδ0_nonneg)
    calc
      inner ℝ c (method 0 : E) - inner ℝ c (xPath : E) =
          inner ℝ c ((method 0 : E) - (xPath : E)) := by
            rw [inner_sub_right]
      _ ≤ |inner ℝ c ((method 0 : E) - (xPath : E))| := le_abs_self _
      _ ≤ HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
            (method.iterate_hessian_isPositive 0) (hH 0)
            ((InnerProductSpace.toDualMap ℝ E) c) *
              ‖(method 0 : E) - (xPath : E)‖[method.F; (method 0 : E)] := habs
      _ ≤ S * δ0 * (ρ / (1 - ρ)) := hscaled
  have hrewrite : S * δ0 = β * ρ := by
    -- Replace `S δ₀` by the normalized parameter `β ρ`.
    dsimp [ρ]
    field_simp [hβ_pos.ne']
    ring
  calc
    inner ℝ c (method 0 : E) - inner ℝ c (xPath : E) ≤
        S * δ0 * (ρ / (1 - ρ)) := hpair
    _ = β * (ρ ^ (2 : ℕ) / (1 - ρ)) := by
        rw [hrewrite]
        ring

/-- Helper for Theorem 7.14: the exact frozen path point `xPath` is within the canonical
Chapter 5 distance `ρ / (1 - ρ)` from the initial analytic center `method 0`. -/
private theorem frozenInitialPathDistance_le_rhoDivOneSub
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    let ρ : ℝ := (S / β) * δ0
    ρ < 1 →
      ‖(method 0 : E) - (xPath : E)‖[method.F; (method 0 : E)] ≤ ρ / (1 - ρ) := by
  intro β S δ0 c t xPath ρ hρ
  have hpath :
      IsMinOn (centralPathPenaltyObjective c method.F t) P (xPath : E) := by
    -- Reuse the exact frozen maximizer/minimizer bridge at the frozen data.
    simpa [β, S, c, t, xPath] using method.initialPenaltyObjective_isMinOn_uStar k
  have happrox :
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (method 0 : E))) ≤ ρ := by
    -- The residual at the analytic center is exactly the normalized frozen scale `ρ`.
    rw [method.initialPenaltyApproxCenterResidualEq hH k]
  -- Apply the canonical Chapter 5 approximate-center distance theorem at `x = method 0`.
  exact
    centralPathPenalty_localNorm_distance_le_beta_div_one_sub
      (dom := P) (ν := ν) (F := method.F) c t hρ hpath (hH 0) happrox

/-- Helper for Theorem 7.14: the exact frozen path point `xPath` satisfies the Chapter 5
stationarity identity `∇ F(xPath) = (S / β) g₀`. -/
private theorem frozenPathStationarity_eq_scaledInitialSubgradient
    [IsStandardSelfConcordantOn P method.F]
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    ∇ method.F (xPath : E) = (S / β : ℝ) • method.iterateSubgradient 0 := by
  intro β S xPath
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    rw [barrierSubgradientWeightSum_def]
    exact Finset.sum_nonneg fun i hi ↦ (method.stepSize i).2.le
  -- Instantiate the frozen initial ray at the exact time `τ = S / β`.
  simpa [β, S, xPath, smul_smul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hβ_pos.ne']
    using method.initialPenaltyRay_stationarity k
      ⟨S / β, (div_nonneg hS_nonneg hβ_pos.le)⟩

/-- Helper for Theorem 7.14: the frozen Chapter 5 residual at the barycenter is exactly the
gradient gap between `xBar` and the frozen path point `xPath`. -/
private theorem centerMassFrozenResidual_eq_gradientGap
    [IsStandardSelfConcordantOn P method.F]
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    ((t : ℝ) • c) + ∇ method.F (xBar : E) =
      ∇ method.F (xBar : E) - ∇ method.F (xPath : E) := by
  intro β S c t xBar xPath
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hpath :
      ∇ method.F (xPath : E) = (S / β : ℝ) • method.iterateSubgradient 0 := by
    -- Reuse the exact frozen-ray stationarity at the full time `S / β`.
    simpa [β, S, xPath] using method.frozenPathStationarity_eq_scaledInitialSubgradient k
  have hscale :
      ((t : ℝ) • c : E) = -((S / β : ℝ) • method.iterateSubgradient 0) := by
    -- Normalize the frozen penalty vector once so the residual becomes a gradient difference.
    have hcoeff : ((t : ℝ) * (-(S : ℝ))) = -(S / β) := by
      dsimp [t]
      field_simp [hβ_pos.ne']
      ring
    simp [c, hcoeff, smul_smul]
  -- Rewrite the frozen penalty vector as the negative path gradient and collect terms.
  calc
    ((t : ℝ) • c) + ∇ method.F (xBar : E)
        = -((S / β : ℝ) • method.iterateSubgradient 0) + ∇ method.F (xBar : E) := by
            rw [hscale]
    _ = -(∇ method.F (xPath : E)) + ∇ method.F (xBar : E) := by
          rw [hpath]
    _ = ∇ method.F (xBar : E) - ∇ method.F (xPath : E) := by
          abel

/-- Helper for Theorem 7.14: after rewriting the frozen barycenter residual as a gradient gap,
the corresponding Hessian dual local norm is literally the same owner expression. -/
private theorem centerMassFrozenResidual_dualNorm_eq_gradientGap
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    [IsStandardSelfConcordantOn P method.F]
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      method.iterate_centerMass_mem_domain k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    HessianDualLocalNorm.ofDetNeZero method.F (xBar : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xBar.2)
      (method.barrierHessianDetNeZero ν (x := xBar))
      ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (xBar : E))) =
    HessianDualLocalNorm.ofDetNeZero method.F (xBar : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xBar.2)
      (method.barrierHessianDetNeZero ν (x := xBar))
      ((InnerProductSpace.toDualMap ℝ E) (∇ method.F (xBar : E) - ∇ method.F (xPath : E))) := by
  intro β S c t xBar xPath
  -- Rewrite the residual vector first; the dual-norm owner is unchanged afterwards.
  rw [centerMassFrozenResidual_eq_gradientGap (method := method) k]

/-- Helper for Theorem 7.14: the frozen residual pairing at `(xBar, xPath)` is exactly the
canonical gradient-gap pairing on the same chord. -/
private theorem centerMassPathResidualPairing_eq_gradientGap
    [IsStandardSelfConcordantOn P method.F]
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      method.iterate_centerMass_mem_domain k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    inner ℝ (((t : ℝ) • c) + ∇ method.F (xBar : E)) ((xBar : E) - (xPath : E)) =
      inner ℝ (∇ method.F (xBar : E) - ∇ method.F (xPath : E)) ((xBar : E) - (xPath : E)) := by
  intro β S c t xBar xPath
  -- Rewrite only the residual vector; the chord is already in the desired normal form.
  rw [centerMassFrozenResidual_eq_gradientGap (method := method) k]

/-- Helper for Theorem 7.14: in the large-`ρ` branch, the initial frozen dual norm `δ₀` is
strictly positive. -/
private theorem largeRho_initialDualNorm_pos
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let ρ : ℝ := (S / β) * δ0
    1 / 3 ≤ ρ → 0 < δ0 := by
  intro β S δ0 ρ hρ
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hS_pos : 0 < S := by
    dsimp [S]
    have hzero_mem : 0 ∈ Finset.range (k + 1) := by simp
    have hzero_le :
        (method.stepSize 0 : ℝ) ≤
          ∑ i ∈ Finset.range (k + 1), (method.stepSize i : ℝ) := by
      simpa using
        Finset.single_le_sum
          (fun i hi ↦ (method.stepSize i).2.le)
          hzero_mem
    exact lt_of_lt_of_le (method.stepSize 0).2 hzero_le
  have hρ_pos : 0 < ρ := by
    linarith
  have hS_div_β_pos : 0 < S / β := by
    exact div_pos hS_pos hβ_pos
  -- The factor `S / β` is positive in the large branch, so a nonpositive `δ₀` would force
  -- `ρ ≤ 0`, contradicting `ρ ≥ 1 / 3`.
  by_contra hδ0_nonpos
  have hδ0_le : δ0 ≤ 0 := le_of_not_gt hδ0_nonpos
  have hρ_nonpos : ρ ≤ 0 := by
    dsimp [ρ]
    exact mul_nonpos_of_nonneg_of_nonpos hS_div_β_pos.le hδ0_le
  linarith

/-- Helper for Theorem 7.14: the large-branch seed time `τ₀ = 1 / (3 δ₀)` is normalized so that
`τ₀ δ₀ = 1 / 3`. -/
private theorem seedTime_mul_initialDualNorm_eq_third
    {δ0 : ℝ} (hδ0 : 0 < δ0) :
    (1 / (3 * δ0 : ℝ)) * δ0 = (1 / 3 : ℝ) := by
  -- Clear the positive denominator once so later large-branch scalar rewrites can reuse it.
  field_simp [hδ0.ne']

/-- Helper for Theorem 7.14: dividing the final frozen time `S / β` by the seed time
`1 / (3 δ₀)` produces the normalized large-branch ratio `3 ρ`. -/
private theorem finalTimeDivSeedTime_eq_threeRho
    {β S δ0 : ℝ} (hβ : 0 < β) (hδ0 : 0 < δ0) :
    (S / β) / (1 / (3 * δ0 : ℝ)) = 3 * ((S / β) * δ0) := by
  -- This is the scalar normal form used by the large-branch telescope.
  field_simp [hβ.ne', hδ0.ne']

/-- Helper for Theorem 7.14: subtracting the seed normalization from the final-time ratio leaves
exactly the large-branch excess factor `3 ρ - 1`. -/
private theorem finalTimeDivSeedTime_sub_one_eq_threeRho_sub_one
    {β S δ0 : ℝ} (hβ : 0 < β) (hδ0 : 0 < δ0) :
    (S / β) / (1 / (3 * δ0 : ℝ)) - 1 = 3 * ((S / β) * δ0) - 1 := by
  -- Reuse the canonical final/seed time ratio and strip the common base term `1`.
  rw [finalTimeDivSeedTime_eq_threeRho (β := β) (S := S) (δ0 := δ0) hβ hδ0]
  ring

/-- Helper for Theorem 7.14: the final frozen covector `S • g₀` is the initial-ray covector at
time `S / β`. -/
private theorem finalFrozenCovector_eq_rayAtFinalTime
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
    s0 = ((method.beta (k + 1) : ℝ) * (S / β)) • method.dualSubgradient (method 0) := by
  intro β S s0
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  -- Normalize the scalar coefficient so the final covector lives on the same ray as the seed.
  dsimp [s0]
  congr 1
  field_simp [hβ_pos.ne']
  ring

/-- Helper for Theorem 7.14: in the large-`ρ` branch, the seed time `τ₀ = 1 / (3 δ₀)` lies
before the final frozen time `S / β`. -/
private theorem largeRho_seedTime_le_finalTime
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let ρ : ℝ := (S / β) * δ0
    let τ0 : ℝ := 1 / (3 * δ0)
    1 / 3 ≤ ρ → τ0 ≤ S / β := by
  intro β S δ0 ρ τ0 hρ
  have hδ0_pos : 0 < δ0 := by
    -- First isolate the positivity of the frozen initial dual norm from the large-`ρ` hypothesis.
    simpa [β, S, δ0, ρ] using method.largeRho_initialDualNorm_pos ν hH k hρ
  have hineq :
      (1 / 3 : ℝ) / δ0 ≤ S / β := by
    -- Divide the large-branch inequality `1 / 3 ≤ (S / β) δ₀` by the positive factor `δ₀`.
    exact (div_le_iff₀ hδ0_pos).2 <| by
      simpa [ρ, mul_comm, mul_left_comm, mul_assoc] using hρ
  have hτ0_eq : τ0 = (1 / 3 : ℝ) / δ0 := by
    dsimp [τ0]
    field_simp [hδ0_pos.ne']
  simpa [hτ0_eq] using hineq

/-- Helper for Theorem 7.14: at the threshold value `ρ = 1 / 3`, the final frozen time `S / β`
coincides exactly with the normalized seed time `τ₀ = 1 / (3 δ₀)`. -/
private theorem largeRho_threshold_finalTime_eq_seedTime
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let ρ : ℝ := (S / β) * δ0
    let τ0 : ℝ := 1 / (3 * δ0)
    ρ = 1 / 3 → S / β = τ0 := by
  intro β S δ0 ρ τ0 hρ_eq
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hρ_ge : (1 / 3 : ℝ) ≤ ρ := by
    linarith [hρ_eq]
  have hδ0_pos : 0 < δ0 := by
    -- The threshold branch is still a large-`ρ` configuration, so the frozen initial norm is
    -- strictly positive.
    simpa [β, S, δ0, ρ] using method.largeRho_initialDualNorm_pos ν hH k hρ_ge
  have hratio :
      (S / β) / τ0 = 1 := by
    -- Normalize the final/seed time ratio, then specialize the large-branch scalar `3 * ρ`
    -- to the threshold value `1`.
    calc
      (S / β) / τ0 = 3 * ρ := by
        simpa [ρ, τ0] using
          finalTimeDivSeedTime_eq_threeRho
            (β := β) (S := S) (δ0 := δ0) hβ_pos hδ0_pos
      _ = 1 := by
        linarith [hρ_eq]
  have hτ0_pos : 0 < τ0 := by
    -- The normalized seed time is positive because `δ₀` is positive in the threshold branch.
    dsimp [τ0]
    positivity
  exact (div_eq_iff hτ0_pos.ne').1 <| by simpa using hratio

/-- Helper for Theorem 7.14: at the threshold value `ρ = 1 / 3`, the final frozen covector
`S • g₀` is exactly the same point on the initial ray as the seed covector at time `τ₀`. -/
private theorem largeRho_threshold_finalCovector_eq_seedCovector
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let ρ : ℝ := (S / β) * δ0
    let τ0 : ℝ := 1 / (3 * δ0)
    let sτ0 : StrongDual ℝ E := ((method.beta (k + 1) : ℝ) * τ0) • method.dualSubgradient (method 0)
    let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
    ρ = 1 / 3 → s0 = sτ0 := by
  intro β S δ0 ρ τ0 sτ0 s0 hρ_eq
  have htime :
      S / β = τ0 := by
    -- First normalize the threshold branch to the equal-time identity.
    simpa [β, S, δ0, ρ, τ0] using
      method.largeRho_threshold_finalTime_eq_seedTime ν hH k hρ_eq
  calc
    s0 = ((method.beta (k + 1) : ℝ) * (S / β)) • method.dualSubgradient (method 0) := by
      -- Rewrite the final covector onto the canonical frozen initial ray.
      simpa [β, S, s0] using finalFrozenCovector_eq_rayAtFinalTime (method := method) k
    _ = ((method.beta (k + 1) : ℝ) * τ0) • method.dualSubgradient (method 0) := by
      rw [htime]
    _ = sτ0 := by
      simp [sτ0]

/-- Helper for Theorem 7.14: the new small-`ρ` transport route first needs the barycenter to lie
in the initial open Dikin ellipsoid, so this theorem isolates that exact admissibility premise. -/
private theorem centerMass_mem_initialOpenDikinEllipsoid_of_smallRho
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let ρ : ℝ := (S / β) * δ0
    ρ < 1 / 3 →
      ‖(xBar : E) - (method 0 : E)‖[method.F; (method 0 : E)] ≤ ρ →
      (xBar : E) ∈ W⁰[method.F; (method 0 : E)](1) := by
  intro β S δ0 xBar ρ hρ hxBar_local
  -- Route correction: once the barycenter local norm is controlled by `ρ < 1 / 3`, admissibility
  -- is just the canonical open-Dikin membership rewrite at radius `1`.
  refine (mem_openDikinEllipsoid_iff method.F (method 0 : E) (xBar : E) 1).2 ?_
  have hρ_lt_one : ρ < 1 := by
    linarith
  -- The small-branch scalar hypothesis is stronger than the unit Dikin threshold.
  exact lt_of_le_of_lt hxBar_local hρ_lt_one

/-- Helper for Theorem 7.14: once the barycenter local norm is bounded by `r ≤ ρ < 1 / 3`,
the transported base residual `ρ / (1 - r)` together with the averaged-Hessian remainder
`r² / (1 - r)` already fits inside the target small-branch budget `3 ρ`. -/
private theorem smallRhoTransportBudget_le_threeRho
    {ρ r : ℝ} (hρ : ρ < 1 / 3) (hr_nonneg : 0 ≤ r) (hr_le : r ≤ ρ) :
    ρ / (1 - r) + r ^ (2 : ℕ) / (1 - r) ≤ 3 * ρ := by
  have hρ_nonneg : 0 ≤ ρ := le_trans hr_nonneg hr_le
  have hr_lt_one : r < 1 := by
    linarith
  have hden_pos : 0 < 1 - r := by
    linarith
  have hcombine :
      ρ / (1 - r) + r ^ (2 : ℕ) / (1 - r) = (ρ + r ^ (2 : ℕ)) / (1 - r) := by
    -- Put the two transport terms over the common positive denominator `1 - r`.
    field_simp [hden_pos.ne']
  have hbudget :
      ρ + r ^ (2 : ℕ) ≤ (3 * ρ) * (1 - r) := by
    -- The side conditions `r ≤ ρ < 1 / 3` are exactly what makes the small-branch budget fit.
    nlinarith
  rw [hcombine]
  -- Divide the verified numerator budget by the positive denominator.
  exact (div_le_iff₀ hden_pos).2 hbudget

/-- Helper for Theorem 7.14: the frozen initial pairing at the iterate barycenter is controlled
by the normalized Chapter 7 scale `β ρ` times the base local norm of `xBar - x₀`. -/
private theorem centerMassGradientPairing_le_initialScale
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let ρ : ℝ := (S / β) * δ0
    S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
      β * ρ *
        hessianLocalNorm method.F (method 0 : E) ((xBar : E) - (method 0 : E)) := by
  intro β S δ0 xBar ρ
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    rw [barrierSubgradientWeightSum_def]
    exact Finset.sum_nonneg fun i hi ↦ (method.stepSize i).2.le
  have hpair :
      method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        δ0 * hessianLocalNorm method.F (method 0 : E) ((xBar : E) - (method 0 : E)) := by
    have habs :
        |inner ℝ (method.iterateSubgradient 0) ((xBar : E) - (method 0 : E))| ≤
          δ0 * hessianLocalNorm method.F (method 0 : E) ((xBar : E) - (method 0 : E)) := by
      -- Evaluate the fixed initial covector by the Chapter 5 dual/local Cauchy inequality.
      simpa [δ0, DualBarrierSubgradientMethod.dualSubgradient_eq,
        DualBarrierSubgradientMethod.iterateSubgradient_eq,
        InnerProductSpace.toDual_apply_apply] using
        abs_inner_le_hessianDualLocalNorm_mul_hessianLocalNorm_of_detNeZero
          (F := method.F)
          (x := (method 0 : E))
          (v := method.iterateSubgradient 0)
          (z := (xBar : E) - (method 0 : E))
          (method.iterate_hessian_isPositive 0)
          (hH 0)
    -- Drop the absolute value to retain the directional pairing needed in the small branch.
    exact le_trans (le_abs_self _) habs
  have hscaled :
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        S * (δ0 * hessianLocalNorm method.F (method 0 : E) ((xBar : E) - (method 0 : E))) := by
    -- Scale the pairing estimate by the nonnegative total weight `S`.
    exact mul_le_mul_of_nonneg_left hpair hS_nonneg
  have hrewrite : S * δ0 = β * ρ := by
    -- Normalize the frozen scale into the Chapter 7 parameter `ρ`.
    dsimp [ρ]
    field_simp [hβ_pos.ne']
  calc
    S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        S * (δ0 * hessianLocalNorm method.F (method 0 : E) ((xBar : E) - (method 0 : E))) :=
          hscaled
    _ = (S * δ0) * hessianLocalNorm method.F (method 0 : E) ((xBar : E) - (method 0 : E)) := by
          ring
    _ = β * ρ * hessianLocalNorm method.F (method 0 : E) ((xBar : E) - (method 0 : E)) := by
          rw [hrewrite]

/-- Helper for Theorem 7.14: at the frozen parameter `t = 1 / β`, the signed linear correction
from `xBar` to `xPath` is exactly the penalty-objective gap minus the barrier gap. -/
private theorem centerMassPathSignedCorrection_eq_penaltyGap_sub_barrierGap
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    inner ℝ c (xPath : E) - inner ℝ c (xBar : E) =
      β * (centralPathPenaltyObjective c method.F (t : ℝ) (xPath : E) -
          centralPathPenaltyObjective c method.F (t : ℝ) (xBar : E)) -
        β * (method.F (xPath : E) - method.F (xBar : E)) := by
  intro β S c t xBar xPath
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  -- Expand the frozen penalty objective on both endpoints and collect the common barrier terms.
  rw [centralPathPenaltyObjective_apply, centralPathPenaltyObjective_apply]
  dsimp [t]
  field_simp [hβ_pos.ne']
  ring

/-- Helper for Theorem 7.14: the signed correction `xPath → xBar` is controlled by the barrier
increment because `xPath` minimizes the frozen penalty objective. -/
private theorem centerMassPathSignedCorrection_le_barrierGap
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    inner ℝ c (xPath : E) - inner ℝ c (xBar : E) ≤
      β * (method.F (xBar : E) - method.F (xPath : E)) := by
  intro β S c t xBar xPath
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hpath :
      IsMinOn (centralPathPenaltyObjective c method.F t) P (xPath : E) := by
    -- Reuse the frozen maximizer/minimizer bridge instead of re-encoding the path point.
    simpa [β, S, c, t, xPath] using method.initialPenaltyObjective_isMinOn_uStar k
  have hpen :
      centralPathPenaltyObjective c method.F (t : ℝ) (xPath : E) ≤
        centralPathPenaltyObjective c method.F (t : ℝ) (xBar : E) := by
    -- The exact frozen path point minimizes the penalty objective among all feasible points.
    exact (isMinOn_iff.mp hpath) (xBar : E) xBar.2
  have hpen_scaled :
      β * (centralPathPenaltyObjective c method.F (t : ℝ) (xPath : E) -
          centralPathPenaltyObjective c method.F (t : ℝ) (xBar : E)) ≤ 0 := by
    -- Scale the nonpositive penalty gap by the positive frozen weight `β`.
    exact mul_nonpos_of_nonneg_of_nonpos hβ_pos.le (sub_nonpos.mpr hpen)
  calc
    inner ℝ c (xPath : E) - inner ℝ c (xBar : E)
        =
      β * (centralPathPenaltyObjective c method.F (t : ℝ) (xPath : E) -
          centralPathPenaltyObjective c method.F (t : ℝ) (xBar : E)) -
        β * (method.F (xPath : E) - method.F (xBar : E)) := by
          simpa [β, S, c, t, xBar, xPath] using
            centerMassPathSignedCorrection_eq_penaltyGap_sub_barrierGap (method := method) k
    _ ≤ 0 - β * (method.F (xPath : E) - method.F (xBar : E)) := by
          linarith
    _ = β * (method.F (xBar : E) - method.F (xPath : E)) := by
          ring

/-- Helper for Theorem 7.14: any frozen residual bound `≤ ε < 1` at the barycenter upgrades
the exact path point `xPath` to the corresponding Chapter 5 local-distance estimate. -/
private theorem centerMassPathDistance_le_errorDiv
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) {ε : ℝ} (hε : ε < 1) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    HessianDualLocalNorm.ofDetNeZero method.F (xBar : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xBar.2)
      (method.barrierHessianDetNeZero ν (x := xBar))
      ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (xBar : E))) ≤ ε →
      ‖(xBar : E) - (xPath : E)‖[method.F; (xBar : E)] ≤ ε / (1 - ε) := by
  intro β S c t xBar xPath happrox
  have hpath : IsMinOn (centralPathPenaltyObjective c method.F t) P (xPath : E) := by
    -- Reuse the frozen maximizer/minimizer bridge at the exact barycenter/path pair.
    simpa [β, S, c, t, xPath] using method.initialPenaltyObjective_isMinOn_uStar k
  have hxH : (fderiv ℝ (∇ method.F) (xBar : E)).det ≠ 0 :=
    method.barrierHessianDetNeZero ν (x := xBar)
  -- Feed the frozen residual bound directly into the Chapter 5 local-distance theorem.
  simpa using
    centralPathPenalty_localNorm_distance_le_beta_div_one_sub
      (dom := P) (ν := ν) (F := method.F) c t hε
      (xPath := xPath) (x := xBar) hpath hxH happrox

/-- Helper for Theorem 7.14: once the frozen residual at `xBar` is bounded by the normalized
scale `ρ`, the barycenter-to-path distance is exactly the Chapter 5 radius `ρ / (1 - ρ)`. -/
private theorem centerMassPathDistance_le_rhoDivOneSub_ofResidual
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    let ρ : ℝ := (S / β) * δ0
    ρ < 1 →
      HessianDualLocalNorm.ofDetNeZero method.F (xBar : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xBar.2)
        (method.barrierHessianDetNeZero ν (x := xBar))
        ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (xBar : E))) ≤ ρ →
      ‖(xBar : E) - (xPath : E)‖[method.F; (xBar : E)] ≤ ρ / (1 - ρ) := by
  intro β S δ0 c t xBar xPath ρ hρ happrox
  -- Feed the normalized residual hypothesis directly into the existing distance adapter.
  simpa [β, S, c, t, xBar, xPath, ρ] using
    centerMassPathDistance_le_errorDiv (method := method) ν k (ε := ρ) hρ happrox

/-- Helper for Theorem 7.14: in the small-`ρ` branch, a barycenter residual bound `≤ ρ` is
already enough to invoke the Chapter 5 distance adapter at the frozen pair `(xBar, xPath)`. -/
private theorem centerMassPathDistance_le_rhoDivOneSub
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    let ρ : ℝ := (S / β) * δ0
    ρ < 1 / 3 →
      HessianDualLocalNorm.ofDetNeZero method.F (xBar : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xBar.2)
        (method.barrierHessianDetNeZero ν (x := xBar))
        ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (xBar : E))) ≤ ρ →
      ‖(xBar : E) - (xPath : E)‖[method.F; (xBar : E)] ≤ ρ / (1 - ρ) := by
  intro β S δ0 c t xBar xPath ρ hρ happrox
  have hρ_lt_one : ρ < 1 := by
    -- The small-branch cutoff is stronger than the unit-radius hypothesis of the distance owner.
    linarith
  -- Feed the small-`ρ` residual estimate directly into the existing Chapter 5 distance adapter.
  simpa [β, S, δ0, c, t, xBar, xPath, ρ] using
    centerMassPathDistance_le_rhoDivOneSub_ofResidual
      (method := method) ν hH k hρ_lt_one happrox

/-- Helper for Theorem 7.14: any frozen residual bound `≤ ε` at the barycenter gives the
corresponding Chapter 5 residual-pairing estimate against the exact path point `xPath`. -/
private theorem centerMassPathResidualPairing_le_errorMulDistance
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) {ε : ℝ} :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    HessianDualLocalNorm.ofDetNeZero method.F (xBar : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 xBar.2)
      (method.barrierHessianDetNeZero ν (x := xBar))
      ((InnerProductSpace.toDualMap ℝ E) (((t : ℝ) • c) + ∇ method.F (xBar : E))) ≤ ε →
      inner ℝ (((t : ℝ) • c) + ∇ method.F (xBar : E)) ((xBar : E) - (xPath : E)) ≤
        ε * ‖(xBar : E) - (xPath : E)‖[method.F; (xBar : E)] := by
  intro β S c t xBar xPath happrox
  have hxH : (fderiv ℝ (∇ method.F) (xBar : E)).det ≠ 0 :=
    method.barrierHessianDetNeZero ν (x := xBar)
  -- This is the direct residual-pairing consequence of the frozen approximate-center bound.
  simpa using
    centralPathPenalty_residual_pairing_le_beta_mul_distance
      (dom := P) (ν := ν) (F := method.F) c t
      (β := ε) (xPath := xPath) (x := xBar) hxH happrox

/-- Helper for Theorem 7.14: once the barycenter residual pairing is already bounded by
`ρ ‖xBar - xPath‖[F; xBar]`, the generic Chapter 5 lower-pairing theorem yields the exact
distance control `ρ / (1 - ρ)` to the frozen path point `xPath`. -/
private theorem centerMassPathDistance_le_rhoDivOneSub_fromPairing
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
    let ρ : ℝ := (S / β) * δ0
    ρ < 1 / 3 →
      inner ℝ (((t : ℝ) • c) + ∇ method.F (xBar : E)) ((xBar : E) - (xPath : E)) ≤
        ρ * ‖(xBar : E) - (xPath : E)‖[method.F; (xBar : E)] →
      ‖(xBar : E) - (xPath : E)‖[method.F; (xBar : E)] ≤ ρ / (1 - ρ) := by
  intro β S δ0 c t xBar xPath ρ hρ hpair
  let r : ℝ := ‖(xBar : E) - (xPath : E)‖[method.F; (xBar : E)]
  have hβ_pos : 0 < β := by
    -- The frozen barrier weight stays positive at the final index.
    simpa [β] using (method.beta (k + 1)).2
  have hS_nonneg : 0 ≤ S := by
    -- The accumulated step-size weight is nonnegative.
    dsimp [S]
    rw [barrierSubgradientWeightSum_def]
    exact Finset.sum_nonneg fun i hi ↦ (method.stepSize i).2.le
  have hδ0_nonneg : 0 ≤ δ0 := by
    -- The initial dual local norm is nonnegative by construction.
    dsimp [δ0]
    exact dualLocalNorm_nonneg method.F (method 0 : E)
      (method.iterate_hessian_isPositive 0)
      (hessian_isInvertible_of_det_ne_zero (hH 0))
      (method.dualSubgradient (method 0))
  have hρ_nonneg : 0 ≤ ρ := by
    -- The normalized frozen scale inherits nonnegativity from `S`, `β`, and `δ₀`.
    dsimp [ρ]
    exact mul_nonneg (div_nonneg hS_nonneg hβ_pos.le) hδ0_nonneg
  have hρ_lt_one : ρ < 1 := by
    -- The small-branch cutoff is stronger than the Chapter 5 unit-radius hypothesis.
    linarith
  have hpath : IsMinOn (centralPathPenaltyObjective c method.F t) P (xPath : E) := by
    -- Reuse the exact frozen minimizer owner for the penalty objective at `(c, t)`.
    simpa [β, S, c, t, xPath] using method.initialPenaltyObjective_isMinOn_uStar k
  have hr_nonneg : 0 ≤ r := by
    -- Local norms are nonnegative.
    simpa [r] using hessianLocalNorm_nonneg method.F (xBar : E) ((xBar : E) - (xPath : E))
  have hlower :
      r ^ (2 : ℕ) / (1 + r) ≤
        inner ℝ (((t : ℝ) • c) + ∇ method.F (xBar : E)) ((xBar : E) - (xPath : E)) := by
    -- The Chapter 5 lower-pairing theorem is the exact owner for the frozen barycenter/path pair.
    simpa [r] using
      centralPathPenalty_gradient_pairing_lower_to_minimizer
        (dom := P) (ν := ν) (F := method.F) c t (xPath := xPath) (x := xBar) hpath
  have hupper :
      inner ℝ (((t : ℝ) • c) + ∇ method.F (xBar : E)) ((xBar : E) - (xPath : E)) ≤ ρ * r := by
    -- Rewrite the assumed upper pairing bound on the exact same local-distance variable `r`.
    simpa [r] using hpair
  have hmain : r ^ (2 : ℕ) / (1 + r) ≤ ρ * r := le_trans hlower hupper
  have hgoal : r ≤ ρ / (1 - ρ) := by
    by_cases hr_zero : r = 0
    · have : 0 ≤ ρ / (1 - ρ) := by
        exact div_nonneg hρ_nonneg (sub_pos.mpr hρ_lt_one).le
      simpa [r, hr_zero] using this
    · have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_zero)
      have hden_pos : 0 < 1 + r := by positivity
      have hcross : (1 - ρ) * r ≤ ρ := by
        have hmain' : r ^ (2 : ℕ) ≤ ρ * r * (1 + r) := by
          exact (div_le_iff₀ hden_pos).1 hmain
        -- Clear the positive factor `r` to recover the scalar Chapter 5 radius inequality.
        nlinarith
      exact (le_div_iff₀ (sub_pos.mpr hρ_lt_one)).2 (by simpa [mul_comm] using hcross)
  simpa [r] using hgoal

/-- Helper for Theorem 7.14: before the small-`ρ` branch closes on the final quadratic model,
the split correction already reduces to the exact `x₀ → xPath` bound plus the barrier gap from
`xPath` to the barycenter. -/
private theorem centerMassPenaltyGap_le_pathLinear_plus_barrierGap
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      method.iterate_centerMass_mem_domain k⟩
    let ρ : ℝ := (S / β) * δ0
    ρ < 1 / 3 →
      let c : E := -(S : ℝ) • method.iterateSubgradient 0
      let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
        have hβ : 0 < β := by
          simpa [β] using (method.beta (k + 1)).2
        exact one_div_nonneg_of_pos hβ⟩
      let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
      (inner ℝ c (method 0 : E) - inner ℝ c (xPath : E)) +
        (inner ℝ c (xPath : E) - inner ℝ c (xBar : E)) ≤
        β * (ρ ^ (2 : ℕ) / (1 - ρ)) +
          β * (method.F (xBar : E) - method.F (xPath : E)) := by
  intro β S δ0 xBar ρ hρ c t xPath
  have hρ_lt_one : ρ < 1 := by
    -- The small-branch hypothesis is stronger than the Chapter 5 cutoff needed for the exact
    -- frozen path estimate.
    linarith
  have hpathLinear :
      inner ℝ c (method 0 : E) - inner ℝ c (xPath : E) ≤
        β * (ρ ^ (2 : ℕ) / (1 - ρ)) := by
    -- Reuse the already closed `x₀ → xPath` term on the exact frozen path.
    simpa [β, S, δ0, c, t, xPath, ρ] using
      method.frozenInitialPathLinearGap_le_rhoSquareDiv ν hH k hρ_lt_one
  have hbarrierGap :
      inner ℝ c (xPath : E) - inner ℝ c (xBar : E) ≤
        β * (method.F (xBar : E) - method.F (xPath : E)) := by
    -- The remaining `xPath → x̄` term is already controlled by the exact frozen barrier gap.
    simpa [β, S, c, t, xBar, xPath] using
      method.centerMassPathSignedCorrection_le_barrierGap k
  -- Add the exact path term and the barrier-gap term before the final small-branch cleanup.
  linarith

/-- Helper for Theorem 7.14: once the barycenter already satisfies the initial local-norm bound
`‖xBar - x₀‖[F; x₀] ≤ ρ`, the small-`ρ` branch closes by combining the frozen `Uβ` value bound
with the direct Taylor upper bound for `F (xBar) - F (x₀)`. -/
private theorem centerMassPenaltyGap_le_smallRhoModelDirect_ofInitialNorm
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hν_one : 1 ≤ (ν : ℝ))
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      method.iterate_centerMass_mem_domain k⟩
    let ρ : ℝ := (S / β) * δ0
    ρ < 1 / 3 →
      ‖(xBar : E) - (method 0 : E)‖[method.F; (method 0 : E)] ≤ ρ →
      let c : E := -(S : ℝ) • method.iterateSubgradient 0
      let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
        have hβ : 0 < β := by
          simpa [β] using (method.beta (k + 1)).2
        exact one_div_nonneg_of_pos hβ⟩
      let xPath : P := method.uStar (method.beta (k + 1)) (S • method.dualSubgradient (method 0))
        (inner ℝ c (method 0 : E) - inner ℝ c (xPath : E)) +
        (inner ℝ c (xPath : E) - inner ℝ c (xBar : E)) ≤
        β * (ν : ℝ) * (3 * ρ) ^ (2 : ℕ) := by
  intro β S δ0 xBar ρ hρ hxBarLocal c t xPath
  let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hr_nonneg :
      0 ≤ ‖(xBar : E) - (method 0 : E)‖[method.F; (method 0 : E)] := by
    exact hessianLocalNorm_nonneg method.F (method 0 : E) ((xBar : E) - (method 0 : E))
  have hρ_nonneg : 0 ≤ ρ := le_trans hr_nonneg hxBarLocal
  have hρ_lt_one : ρ < 1 := by
    -- The small-branch cutoff is stronger than the unit Dikin threshold used below.
    linarith
  have hxBar_dikin : (xBar : E) ∈ W⁰[method.F; (method 0 : E)](1) := by
    -- Convert the assumed initial local-norm bound into the canonical Dikin membership form.
    refine (mem_openDikinEllipsoid_iff method.F (method 0 : E) (xBar : E) 1).2 ?_
    exact lt_of_le_of_lt hxBarLocal hρ_lt_one
  have hgrad_zero : ∇ method.F (method 0 : E) = 0 :=
    method.initial_iterate_gradient_eq_zero
  have hvalue_raw :
      Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 ≤
        β * selfConcordantOmegaStar ⟨ρ, hρ_lt_one⟩ := by
    -- The full frozen covector already satisfies the one-step `β ω_*` bound at radius `ρ`.
    simpa [β, S, δ0, ρ, s0] using
      method.frozenInitialPenaltyValue_le_omegaStar ν hH k hρ_lt_one
  have hvalue :
      Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 ≤
        β * (ρ ^ (2 : ℕ) / (2 * (1 - ρ))) := by
    have hω_upper :
        selfConcordantOmegaStar ⟨ρ, hρ_lt_one⟩ ≤
          ρ ^ (2 : ℕ) / (2 * (1 - ρ)) := by
      -- Replace `ω_* (ρ)` by the standard quadratic upper bound on `[0, 1)`.
      simpa [selfConcordantOmegaStar_apply] using
        omegaStarUpperBoundRaw hρ_nonneg hρ_lt_one
    exact le_trans hvalue_raw <| by
      gcongr
  let rawTau : Set.Iio (1 : ℝ) :=
    selfConcordantOmegaStarArg 1
      ‖(xBar : E) - (method 0 : E)‖[method.F; (method 0 : E)]
      (lt_of_le_of_lt hxBarLocal hρ_lt_one)
  have hbarrier_raw :
      method.F (xBar : E) ≤ method.F (method 0 : E) + selfConcordantOmegaStar rawTau := by
    have hupper_raw :
        method.F (xBar : E) ≤
          method.F (method 0 : E) +
            inner ℝ (∇ method.F (method 0 : E)) ((xBar : E) - (method 0 : E)) +
            selfConcordantOmegaStar rawTau := by
      -- Apply the Chapter 5 Taylor upper bound at the analytic center in the base metric.
      simpa [rawTau] using
        (IsSelfConcordantOnWith.localNorm_taylor_upper_bound_with_selfConcordantOmegaStar
          (dom := P) (Mf := (1 : NNReal)) (f := method.F) inferInstance
          (x := (method 0 : E)) (y := (xBar : E)) (method 0).2 hxBar_dikin)
    -- The analytic-center gradient vanishes, so the linear Taylor term disappears.
    simpa [hgrad_zero] using hupper_raw
  have hbarrier :
      method.F (xBar : E) - method.F (method 0 : E) ≤
        ρ ^ (2 : ℕ) / (2 * (1 - ρ)) := by
    have hr_lt_one :
        ‖(xBar : E) - (method 0 : E)‖[method.F; (method 0 : E)] < 1 := by
      exact lt_of_le_of_lt hxBarLocal hρ_lt_one
    have hω_raw :
        selfConcordantOmegaStar rawTau ≤
          ‖(xBar : E) - (method 0 : E)‖[method.F; (method 0 : E)] ^ (2 : ℕ) /
            (2 * (1 - ‖(xBar : E) - (method 0 : E)‖[method.F; (method 0 : E)])) := by
      -- Bound the exact remainder at `xBar` by the canonical quadratic fraction in its base norm.
      simpa [rawTau] using
        (selfConcordantOmegaStar_bounds hr_nonneg hr_lt_one).2
    have hfrac :
        ‖(xBar : E) - (method 0 : E)‖[method.F; (method 0 : E)] ^ (2 : ℕ) /
            (2 * (1 - ‖(xBar : E) - (method 0 : E)‖[method.F; (method 0 : E)])) ≤
          ρ ^ (2 : ℕ) / (2 * (1 - ρ)) := by
      have hden_xBar :
          0 < 2 * (1 - ‖(xBar : E) - (method 0 : E)‖[method.F; (method 0 : E)]) := by
        linarith
      have hden_ρ : 0 < 2 * (1 - ρ) := by
        linarith
      -- The scalar map `r ↦ r² / (2 (1 - r))` is increasing on `[0, 1)`.
      exact (div_le_div_iff hden_xBar hden_ρ).2 <| by
        nlinarith
    linarith
  have hcorrection :
      (inner ℝ c (method 0 : E) - inner ℝ c (xPath : E)) +
          (inner ℝ c (xPath : E) - inner ℝ c (xBar : E)) ≤
        Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 +
          β * (method.F (xBar : E) - method.F (method 0 : E)) := by
    have hscore :
        S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) -
            β * (method.F (xBar : E) - method.F (method 0 : E)) ≤
          Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 := by
      have hmax :
          IsMaxOn
            (fun v : E ↦
              s0 (v - (method 0 : E)) -
                β * (method.F v - method.F (method 0 : E)))
            P
            (xPath : E) := by
        -- View the exact frozen point `xPath` through the canonical `Uβ` maximizer owner.
        simpa [β, S, s0, xPath] using
          method.uStar_isMaxOn (x0 := (method 0 : E))
            (β := method.beta (k + 1)) (s := s0)
      -- Evaluate the maximizer inequality at the feasible barycenter `xBar`.
      simpa [β, S, s0, xPath] using
        (isMaxOn_iff.mp hmax) (xBar : E) xBar.2
    have hsplit :
        S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) =
          (inner ℝ c (method 0 : E) - inner ℝ c (xPath : E)) +
            (inner ℝ c (xPath : E) - inner ℝ c (xBar : E)) := by
      -- Rewrite the correction prefix through the exact frozen path point.
      simpa [S, c, xBar, xPath] using method.initialCorrection_split_through_path k
    linarith
  have hscaled :
      Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 +
          β * (method.F (xBar : E) - method.F (method 0 : E)) ≤
        β * (ν : ℝ) * (3 * ρ) ^ (2 : ℕ) := by
    have hmain :
        ρ ^ (2 : ℕ) / (2 * (1 - ρ)) + ρ ^ (2 : ℕ) / (2 * (1 - ρ)) ≤
          (ν : ℝ) * (3 * ρ) ^ (2 : ℕ) := by
      -- After both `ω_*` terms are collapsed to the same quadratic fraction, the small-branch
      -- cutoff `ρ < 1 / 3` and `ν ≥ 1` absorb the remainder into `ν (3 ρ)²`.
      nlinarith
    have hβ_scale :
        β * (ρ ^ (2 : ℕ) / (2 * (1 - ρ))) +
            β * (ρ ^ (2 : ℕ) / (2 * (1 - ρ))) ≤
          β * ((ν : ℝ) * (3 * ρ) ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left hmain hβ_pos.le
    linarith [hvalue, hbarrier, hβ_pos.le]
  exact le_trans hcorrection hscaled

/-- Helper for Theorem 7.14: evaluating the frozen full-step payoff at the barycenter already
places the initial penalty gap under the same quadratic `ρ`-model as the exact frozen path
value. This isolates the value-side part of the missing initial local-norm bridge. -/
private theorem centerMassInitialPenaltyGap_le_quadraticModel
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      method.iterate_centerMass_mem_domain k⟩
    let ρ : ℝ := (S / β) * δ0
    ρ < 1 / 3 →
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) -
        β * (method.F (xBar : E) - method.F (method 0 : E)) ≤
      β * (ρ ^ (2 : ℕ) / (2 * (1 - ρ))) := by
  intro β S δ0 xBar ρ hρ
  let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
  let xPath : P := method.uStar (method.beta (k + 1)) s0
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    rw [barrierSubgradientWeightSum_def]
    exact Finset.sum_nonneg fun i hi ↦ (method.stepSize i).2.le
  have hδ0_nonneg : 0 ≤ δ0 := by
    -- The frozen initial dual local norm is nonnegative by construction.
    dsimp [δ0]
    exact dualLocalNorm_nonneg method.F (method 0 : E)
      (method.iterate_hessian_isPositive 0)
      (hessian_isInvertible_of_det_ne_zero (hH 0))
      (method.dualSubgradient (method 0))
  have hρ_nonneg : 0 ≤ ρ := by
    -- The normalized frozen residual is nonnegative because all of its scalar factors are.
    dsimp [ρ]
    exact mul_nonneg (div_nonneg hS_nonneg hβ_pos.le) hδ0_nonneg
  have hρ_lt_one : ρ < 1 := by
    -- The small-branch cutoff is stronger than the Chapter 5 unit-radius requirement.
    linarith
  have hscore :
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) -
          β * (method.F (xBar : E) - method.F (method 0 : E)) ≤
        Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 := by
    have hmax :
        IsMaxOn
          (fun v : E ↦
            s0 (v - (method 0 : E)) -
              β * (method.F v - method.F (method 0 : E)))
          P
          (xPath : E) := by
      -- View the exact frozen point `xPath` through the canonical `Uβ` maximizer owner.
      simpa [β, S, s0, xPath] using
        method.uStar_isMaxOn (x0 := (method 0 : E))
          (β := method.beta (k + 1)) (s := s0)
    -- Evaluate the frozen payoff upper bound at the feasible barycenter `xBar`.
    simpa [β, S, s0, xPath] using
      (isMaxOn_iff.mp hmax) (xBar : E) xBar.2
  have hvalue_raw :
      Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 ≤
        β * selfConcordantOmegaStar ⟨ρ, hρ_lt_one⟩ := by
    -- The exact frozen full-step value already satisfies the canonical `β ω_* (ρ)` bound.
    simpa [β, S, δ0, ρ, s0] using
      method.frozenInitialPenaltyValue_le_omegaStar ν hH k hρ_lt_one
  have hω_upper :
      selfConcordantOmegaStar ⟨ρ, hρ_lt_one⟩ ≤
        ρ ^ (2 : ℕ) / (2 * (1 - ρ)) := by
    -- Replace `ω_* (ρ)` by the standard quadratic upper bound on `[0, 1)`.
    simpa [selfConcordantOmegaStar_apply] using omegaStarUpperBoundRaw hρ_nonneg hρ_lt_one
  have hvalue :
      Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 ≤
        β * (ρ ^ (2 : ℕ) / (2 * (1 - ρ))) := by
    exact le_trans hvalue_raw <| by
      gcongr
  exact le_trans hscore hvalue

/-- Helper for Theorem 7.14: on `[0, 1)`, the scalar model
`t ↦ t ^ 2 / (2 * (1 - t))` is increasing, so comparing the two quadratic normal forms already
forces the corresponding radii to compare. -/
private theorem quadraticDivOneSub_le_iff
    {r ρ : ℝ}
    (hr_nonneg : 0 ≤ r) (hρ_nonneg : 0 ≤ ρ)
    (hr_lt_one : r < 1) (hρ_lt_one : ρ < 1)
    (hquad :
      r ^ (2 : ℕ) / (2 * (1 - r)) ≤ ρ ^ (2 : ℕ) / (2 * (1 - ρ))) :
    r ≤ ρ := by
  have hr_den : 0 < 2 * (1 - r) := by
    -- The quadratic normal form is only used inside the unit Dikin radius.
    linarith
  have hρ_den : 0 < 2 * (1 - ρ) := by
    -- The comparison radius `ρ` also stays in the same admissible scalar range.
    linarith
  have hcross :
      r ^ (2 : ℕ) * (2 * (1 - ρ)) ≤ ρ ^ (2 : ℕ) * (2 * (1 - r)) := by
    -- Clear the positive denominators before handing the scalar comparison to `nlinarith`.
    exact (div_le_div_iff hr_den hρ_den).1 hquad
  have hcross' :
      r ^ (2 : ℕ) * (1 - ρ) ≤ ρ ^ (2 : ℕ) * (1 - r) := by
    -- Strip the common positive factor `2`.
    nlinarith
  -- The remaining inequality is polynomial on the region `0 ≤ r, ρ < 1`.
  nlinarith [hcross']

/-- Helper for Theorem 7.14: the remaining missing ingredient is the barycenter-side lower model
for the frozen initial penalty gap. Once this lower quadratic estimate is available, the
small-`ρ` closeout is just a scalar comparison against the already-proved upper model. -/
private theorem centerMassInitialPenaltyGap_eq_scaled_penaltyObjectiveGap
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      method.iterate_centerMass_mem_domain k⟩
    S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) -
        β * (method.F (xBar : E) - method.F (method 0 : E)) =
      β *
        (centralPathPenaltyObjective c method.F (t : ℝ) (method 0 : E) -
          centralPathPenaltyObjective c method.F (t : ℝ) (xBar : E)) := by
  intro β S c t xBar
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  -- Expand the frozen penalty objective on both endpoints and collect the common factor `β`.
  rw [centralPathPenaltyObjective_apply, centralPathPenaltyObjective_apply]
  dsimp [t]
  field_simp [hβ_pos.ne']
  simp [c, DualBarrierSubgradientMethod.dualSubgradient_eq,
    DualBarrierSubgradientMethod.iterateSubgradient_eq,
    InnerProductSpace.toDual_apply_apply]
  ring

/-- Helper for Theorem 7.14: the frozen initial correction equals the increment of the fixed
barycenter penalty gap between the zero-time barrier objective and the frozen final time. -/
private theorem centerMassInitialCorrection_eq_scaledPenaltyIncrement
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let c : E := -(S : ℝ) • method.iterateSubgradient 0
    let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
      have hβ : 0 < β := by
        simpa [β] using (method.beta (k + 1)).2
      exact one_div_nonneg_of_pos hβ⟩
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      method.iterate_centerMass_mem_domain k⟩
    S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) =
      β *
        ((centralPathPenaltyObjective c method.F (t : ℝ) (method 0 : E) -
            centralPathPenaltyObjective c method.F (t : ℝ) (xBar : E)) -
          (centralPathPenaltyObjective c method.F 0 (method 0 : E) -
            centralPathPenaltyObjective c method.F 0 (xBar : E))) := by
  intro β S c t xBar
  have hscaledGap :
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) -
          β * (method.F (xBar : E) - method.F (method 0 : E)) =
        β *
          (centralPathPenaltyObjective c method.F (t : ℝ) (method 0 : E) -
            centralPathPenaltyObjective c method.F (t : ℝ) (xBar : E)) := by
    -- Start from the existing frozen penalty-gap normal form at the barycenter.
    simpa [β, S, c, t, xBar] using
      centerMassInitialPenaltyGap_eq_scaled_penaltyObjectiveGap (method := method) k
  have hzeroGap :
      centralPathPenaltyObjective c method.F 0 (method 0 : E) -
          centralPathPenaltyObjective c method.F 0 (xBar : E) =
        method.F (method 0 : E) - method.F (xBar : E) := by
    -- At time `0`, the penalty objective reduces to the barrier value itself.
    rw [centralPathPenaltyObjective_apply, centralPathPenaltyObjective_apply]
    simp
  -- Replace the time-zero penalty gap by the barrier difference so the left side becomes the
  -- raw Chapter 7 initial correction term.
  linarith

/-- Helper for Theorem 7.14: the small-`ρ` branch should now be proved directly on the fixed
barycenter penalty-gap increment, not through the obsolete local-norm bridge. -/
private theorem smallRho_initialCorrectionSquareControl_viaFrozenRayPartition
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hν_one : 1 ≤ (ν : ℝ))
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let ρ : ℝ := (S / β) * δ0
    ρ < 1 / 3 →
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        β * (ν : ℝ) * (3 * ρ) ^ (2 : ℕ) := by
  intro β S δ0 xBar ρ hρ
  let c : E := -(S : ℝ) • method.iterateSubgradient 0
  let t : Set.Ici (0 : ℝ) := ⟨1 / β, by
    have hβ : 0 < β := by
      simpa [β] using (method.beta (k + 1)).2
    exact one_div_nonneg_of_pos hβ⟩
  have hβ_pos : 0 < β := by
    -- The frozen barrier parameter stays positive at the final stage.
    simpa [β] using (method.beta (k + 1)).2
  have hρ_lt_one : ρ < 1 := by
    -- The small-branch cutoff is stronger than the unit-radius hypotheses used by the ray step.
    linarith
  have hincrement :
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) =
        β *
          ((centralPathPenaltyObjective c method.F (t : ℝ) (method 0 : E) -
              centralPathPenaltyObjective c method.F (t : ℝ) (xBar : E)) -
            (centralPathPenaltyObjective c method.F 0 (method 0 : E) -
              centralPathPenaltyObjective c method.F 0 (xBar : E))) := by
    -- Rewrite the target directly as a frozen penalty-gap increment at the fixed barycenter.
    simpa [β, S, c, t, xBar] using
      centerMassInitialCorrection_eq_scaledPenaltyIncrement (method := method) k
  let _ := hν_one
  let _ := hH
  let _ := hρ_lt_one
  let _ := hβ_pos
  let _ := hincrement
  -- Route correction: the old `xBar -> xPath -> x0` local-norm detour has been removed. The
  -- stabilized frontier is the direct fixed-barycenter increment theorem above.
  -- TODO: move the frozen-ray step and affine ratio-partition block ahead of this theorem, then
  -- telescope the exact penalty-gap increments from time `0` to `S / β` on the normal form
  -- supplied by `hincrement`.
  sorry

/-- Helper for Theorem 7.14: the small-`ρ` branch reduces to a frozen approximate-center estimate
for the barycenter and the corresponding Chapter 5 quadratic correction bound. -/
private theorem smallRho_initialCorrectionSquareControl
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hν_one : 1 ≤ (ν : ℝ))
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let ρ : ℝ := (S / β) * δ0
    ρ < 1 / 3 →
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        β * (ν : ℝ) * (3 * ρ) ^ (2 : ℕ) := by
  intro β S δ0 xBar ρ hρ
  -- Route correction: the small branch now delegates directly to the fixed-barycenter
  -- penalty-increment theorem instead of routing through the obsolete local-norm sink.
  simpa [β, S, δ0, xBar, ρ] using
    smallRho_initialCorrectionSquareControl_viaFrozenRayPartition
      (method := method) ν hH hν_one k hρ

/-- Helper for Theorem 7.14: one admissible frozen-ray step rewrites the Chapter 7
`Uβ`-increment estimate as the corresponding penalty-gap increment at the same base point. -/
private theorem frozenInitialRayPenaltyGapStep_le_linearPlusOmega
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) {τ τ' : ℝ}
    (hτ : 0 < τ) (hτ_le : τ ≤ τ')
    (hsmall : (τ' - τ) * (Real.sqrt (ν : ℝ) / τ) < 1) :
    let β := method.beta (k + 1)
    let yτ : P := method.uStar β (((β : ℝ) * τ) • method.dualSubgradient (method 0))
    let yτ' : P := method.uStar β (((β : ℝ) * τ') • method.dualSubgradient (method 0))
    let δτ :=
      HessianDualLocalNorm.ofDetNeZero method.F (yτ : E)
        (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 yτ.2)
        (method.uStar_hessianDetNeZero ν β (((β : ℝ) * τ) • method.dualSubgradient (method 0)))
        (method.dualSubgradient (method 0))
    let η : Set.Iio (1 : ℝ) := ⟨(τ' - τ) * δτ, by
      have hδ :
          δτ ≤ Real.sqrt (ν : ℝ) / τ := by
        simpa [β, yτ, δτ] using
          method.initialPenaltyRay_objectiveVectorNorm_le_sqrtDiv ν k ⟨τ, hτ⟩
      have hτdiff_nonneg : 0 ≤ τ' - τ := sub_nonneg.mpr hτ_le
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hδ hτdiff_nonneg) hsmall⟩
    centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
        (method 0 : E) -
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
        (yτ' : E) ≤
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
          (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
          (yτ : E) +
        (τ' - τ) * method.dualSubgradient (method 0) ((yτ : E) - (method 0 : E)) +
        selfConcordantOmegaStar η := by
  intro β yτ yτ' δτ η
  have hβ_pos : 0 < (β : ℝ) := by
    simpa [β] using (method.beta (k + 1)).2
  have hvalue :
      Uβ P method.F (method 0 : E) β (((β : ℝ) * τ') • method.dualSubgradient (method 0)) ≤
        Uβ P method.F (method 0 : E) β (((β : ℝ) * τ) • method.dualSubgradient (method 0)) +
          ((β : ℝ) * (τ' - τ)) *
            method.dualSubgradient (method 0) ((yτ : E) - (method 0 : E)) +
          (β : ℝ) * selfConcordantOmegaStar η := by
    -- Start from the already proved one-step `Uβ` model on the frozen initial ray.
    simpa [β, yτ, yτ', δτ, η] using
      method.initialPenaltyRay_valueIncrement_le_omegaStar ν k hτ hτ_le hsmall
  have hscaled :
      (β : ℝ) *
          (centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
              (method 0 : E) -
            centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
              (yτ' : E)) ≤
        (β : ℝ) *
          (centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
              (method 0 : E) -
            centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
              (yτ : E) +
            (τ' - τ) * method.dualSubgradient (method 0) ((yτ : E) - (method 0 : E)) +
            selfConcordantOmegaStar η) := by
    -- Rewrite the two frozen `Uβ` values through the exact penalty-gap normal form and factor
    -- the common positive scalar `β`.
    rw [method.frozenInitialRayValue_eq_scaled_penaltyGap k (τ := τ')] at hvalue
    rw [method.frozenInitialRayValue_eq_scaled_penaltyGap k (τ := τ)] at hvalue
    simpa [β, yτ, yτ', mul_add, add_comm, add_left_comm, add_assoc, mul_assoc,
      mul_left_comm, mul_comm] using hvalue
  -- Divide out the positive barrier parameter to recover the bare penalty-gap increment.
  exact (mul_le_mul_left hβ_pos).mp hscaled

/-- Helper for Theorem 7.14: if one frozen-ray increment has normalized size at most `1 / 2`,
its penalty-gap increase is bounded by the corresponding quadratic ratio model. -/
private theorem frozenInitialRayPenaltyGapStep_le_linearPlusRatioSquare
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) {τ τ' : ℝ}
    (hτ : 0 < τ) (hτ_le : τ ≤ τ')
    (hsmall : (τ' - τ) * (Real.sqrt (ν : ℝ) / τ) ≤ 1 / 2) :
    let β := method.beta (k + 1)
    let yτ : P := method.uStar β (((β : ℝ) * τ) • method.dualSubgradient (method 0))
    let yτ' : P := method.uStar β (((β : ℝ) * τ') • method.dualSubgradient (method 0))
    centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
        (method 0 : E) -
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
        (yτ' : E) ≤
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
          (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
          (yτ : E) +
        (τ' - τ) * method.dualSubgradient (method 0) ((yτ : E) - (method 0 : E)) +
        (ν : ℝ) * ((τ' - τ) / τ) ^ (2 : ℕ) := by
  intro β yτ yτ'
  let δτ :=
    HessianDualLocalNorm.ofDetNeZero method.F (yτ : E)
      (IsSelfConcordantOnWith.hessian_isPositive_of_mem 1 yτ.2)
      (method.uStar_hessianDetNeZero ν β (((β : ℝ) * τ) • method.dualSubgradient (method 0)))
      (method.dualSubgradient (method 0))
  let η : Set.Iio (1 : ℝ) := ⟨(τ' - τ) * δτ, by
    have hδ :
        δτ ≤ Real.sqrt (ν : ℝ) / τ := by
      simpa [β, yτ, δτ] using
        method.initialPenaltyRay_objectiveVectorNorm_le_sqrtDiv ν k ⟨τ, hτ⟩
    have hτdiff_nonneg : 0 ≤ τ' - τ := sub_nonneg.mpr hτ_le
    have hsmall_lt_one : (τ' - τ) * (Real.sqrt (ν : ℝ) / τ) < 1 := by
      linarith
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hδ hτdiff_nonneg) hsmall_lt_one⟩
  have hstep :
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
          (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
          (yτ' : E) ≤
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
            (method 0 : E) -
          centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
            (yτ : E) +
          (τ' - τ) * method.dualSubgradient (method 0) ((yτ : E) - (method 0 : E)) +
          selfConcordantOmegaStar η := by
    have hsmall_lt_one : (τ' - τ) * (Real.sqrt (ν : ℝ) / τ) < 1 := by
      linarith
    -- First rewrite the admissible one-step estimate on the penalty-gap surface.
    simpa [β, yτ, yτ', δτ, η] using
      frozenInitialRayPenaltyGapStep_le_linearPlusOmega (method := method) ν k hτ hτ_le
        hsmall_lt_one
  have hη_nonneg : 0 ≤ (η : ℝ) := by
    exact mul_nonneg (sub_nonneg.mpr hτ_le) (by
      dsimp [δτ]
      rw [HessianDualLocalNorm.ofDetNeZero_def]
      exact Real.sqrt_nonneg _)
  have hη_le_half : (η : ℝ) ≤ 1 / 2 := by
    have hδ :
        δτ ≤ Real.sqrt (ν : ℝ) / τ := by
      simpa [β, yτ, δτ] using
        method.initialPenaltyRay_objectiveVectorNorm_le_sqrtDiv ν k ⟨τ, hτ⟩
    have hτdiff_nonneg : 0 ≤ τ' - τ := sub_nonneg.mpr hτ_le
    exact le_trans (mul_le_mul_of_nonneg_left hδ hτdiff_nonneg) hsmall
  have hω_eta :
      selfConcordantOmegaStar η ≤
        (ν : ℝ) * ((τ' - τ) / τ) ^ (2 : ℕ) := by
    have hω_sq :
        selfConcordantOmegaStar η ≤ ((η : ℝ)) ^ (2 : ℕ) := by
      have hω_raw :
          selfConcordantOmegaStar η ≤ ((η : ℝ) ^ (2 : ℕ)) / (2 * (1 - (η : ℝ))) := by
        simpa [selfConcordantOmegaStar_apply] using omegaStarUpperBoundRaw hη_nonneg η.2
      have hden_ge_one : 1 ≤ 2 * (1 - (η : ℝ)) := by
        linarith
      have hfrac_le : ((η : ℝ) ^ (2 : ℕ)) / (2 * (1 - (η : ℝ))) ≤ ((η : ℝ)) ^ (2 : ℕ) := by
        by_cases hη_zero : (η : ℝ) ^ (2 : ℕ) = 0
        · simp [hη_zero]
        · have hηsq_nonneg : 0 ≤ ((η : ℝ)) ^ (2 : ℕ) := sq_nonneg _
          have hinv_le_one : (2 * (1 - (η : ℝ)))⁻¹ ≤ (1 : ℝ) := by
            have hden_pos : 0 < 2 * (1 - (η : ℝ)) := by linarith
            exact (inv_le_one₀ hden_pos).2 hden_ge_one
          have hmul :=
            mul_le_mul_of_nonneg_left hinv_le_one hηsq_nonneg
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
      exact le_trans hω_raw hfrac_le
    have hη_sq :
        ((η : ℝ)) ^ (2 : ℕ) ≤ (ν : ℝ) * ((τ' - τ) / τ) ^ (2 : ℕ) := by
      have hδ :
          δτ ≤ Real.sqrt (ν : ℝ) / τ := by
        simpa [β, yτ, δτ] using
          method.initialPenaltyRay_objectiveVectorNorm_le_sqrtDiv ν k ⟨τ, hτ⟩
      have hτdiff_nonneg : 0 ≤ τ' - τ := sub_nonneg.mpr hτ_le
      have hτ_nonneg : 0 ≤ τ := le_of_lt hτ
      have hbase :
          (η : ℝ) ≤ (τ' - τ) * (Real.sqrt (ν : ℝ) / τ) := by
        exact mul_le_mul_of_nonneg_left hδ hτdiff_nonneg
      have hbase_nonneg : 0 ≤ (τ' - τ) * (Real.sqrt (ν : ℝ) / τ) := by
        positivity
      have hsquare :
          ((η : ℝ)) ^ (2 : ℕ) ≤ ((τ' - τ) * (Real.sqrt (ν : ℝ) / τ)) ^ (2 : ℕ) := by
        nlinarith [hbase, hη_nonneg, hbase_nonneg]
      calc
        ((η : ℝ)) ^ (2 : ℕ) ≤ ((τ' - τ) * (Real.sqrt (ν : ℝ) / τ)) ^ (2 : ℕ) := hsquare
        _ = (ν : ℝ) * ((τ' - τ) / τ) ^ (2 : ℕ) := by
          have hν_nonneg : 0 ≤ (ν : ℝ) := by exact_mod_cast ν.2
          rw [show ((τ' - τ) * (Real.sqrt (ν : ℝ) / τ)) ^ (2 : ℕ) =
              ((τ' - τ) / τ) ^ (2 : ℕ) * (Real.sqrt (ν : ℝ)) ^ (2 : ℕ) by ring]
          rw [Real.sq_sqrt hν_nonneg]
          ring
    exact le_trans hω_sq hη_sq
  -- Replace the `ω_*` remainder by the quadratic ratio model for this normalized step.
  exact le_trans hstep <| by
    gcongr

/-- Helper for Theorem 7.14: changing the frozen ray time from `τ` to `τ'` while keeping the old
maximizer `yτ` fixed adds exactly the displayed linear increment. -/
private theorem frozenInitialRayPenaltyGap_sameTimeShift
    (k : ℕ) {τ τ' : ℝ} :
    let yτ : P := method.uStar (method.beta (k + 1))
      (((method.beta (k + 1) : ℝ) * τ) • method.dualSubgradient (method 0))
    centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
        (method 0 : E) -
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
        (yτ : E) =
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
          (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
          (yτ : E) +
        (τ' - τ) * method.dualSubgradient (method 0) ((yτ : E) - (method 0 : E)) := by
  intro yτ
  -- Expand the two frozen penalty gaps and collect the pure time-shift term at the fixed point
  -- `yτ`.
  rw [centralPathPenaltyObjective_apply, centralPathPenaltyObjective_apply,
    centralPathPenaltyObjective_apply, centralPathPenaltyObjective_apply]
  simp [DualBarrierSubgradientMethod.dualSubgradient_eq,
    DualBarrierSubgradientMethod.iterateSubgradient_eq, InnerProductSpace.toDual_apply_apply]
  ring

/-- Helper for Theorem 7.14: after absorbing the fixed-point time-shift identity, one admissible
frozen-ray step is controlled purely by the quadratic ratio remainder. -/
private theorem frozenInitialRayPenaltyGapStep_le_sameTimeRatioSquare
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (k : ℕ) {τ τ' : ℝ}
    (hτ : 0 < τ) (hτ_le : τ ≤ τ')
    (hsmall : (τ' - τ) * (Real.sqrt (ν : ℝ) / τ) ≤ 1 / 2) :
    let β := method.beta (k + 1)
    let yτ : P := method.uStar β (((β : ℝ) * τ) • method.dualSubgradient (method 0))
    let yτ' : P := method.uStar β (((β : ℝ) * τ') • method.dualSubgradient (method 0))
    centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
        (method 0 : E) -
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
        (yτ' : E) ≤
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
          (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
          (yτ : E) +
        (ν : ℝ) * ((τ' - τ) / τ) ^ (2 : ℕ) := by
  intro β yτ yτ'
  have hstep :
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
          (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
          (yτ' : E) ≤
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
            (method 0 : E) -
          centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
            (yτ : E) +
          (τ' - τ) * method.dualSubgradient (method 0) ((yτ : E) - (method 0 : E)) +
          (ν : ℝ) * ((τ' - τ) / τ) ^ (2 : ℕ) := by
    -- First package the one-step frozen-ray estimate with the quadratic ratio remainder.
    simpa [β, yτ, yτ'] using
      frozenInitialRayPenaltyGapStep_le_linearPlusRatioSquare
        (method := method) ν k hτ hτ_le hsmall
  have hshift :
      centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
          (method 0 : E) -
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ'
          (yτ : E) =
        centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
            (method 0 : E) -
          centralPathPenaltyObjective (-(method.iterateSubgradient 0)) method.F τ
            (yτ : E) +
          (τ' - τ) * method.dualSubgradient (method 0) ((yτ : E) - (method 0 : E)) := by
    -- Rewrite the fixed old maximizer `yτ` at the new time `τ'` so the linear increment
    -- disappears from the one-step bound.
    simpa [β, yτ] using
      frozenInitialRayPenaltyGap_sameTimeShift (method := method) k (τ := τ) (τ' := τ')
  rw [hshift] at hstep
  exact hstep

/-- Helper for Theorem 7.14: a ratio increment on the frozen initial ray of size at most
`1 / (2 * √ν)` gives the normalized admissibility bound needed for one strict large-branch step. -/
private theorem frozenInitialRayRatioIncrement_admissible
    (ν : NNReal) (hν : 0 < (ν : ℝ))
    {r r' : ℝ} (hr : 1 ≤ r)
    (hstep : r' - r ≤ 1 / (2 * Real.sqrt (ν : ℝ))) :
    (r' - r) * (Real.sqrt (ν : ℝ) / r) ≤ 1 / 2 := by
  have hsqrt_pos : 0 < Real.sqrt (ν : ℝ) := Real.sqrt_pos.2 hν
  have hsqrt_nonneg : 0 ≤ Real.sqrt (ν : ℝ) := hsqrt_pos.le
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hfactor_nonneg : 0 ≤ Real.sqrt (ν : ℝ) / r := by
    positivity
  have hmain :
      (r' - r) * (Real.sqrt (ν : ℝ) / r) ≤
        (1 / (2 * Real.sqrt (ν : ℝ))) * (Real.sqrt (ν : ℝ) / r) := by
    -- Multiply the ratio-step cap by the nonnegative normalization factor `√ν / r`.
    exact mul_le_mul_of_nonneg_right hstep hfactor_nonneg
  have hrecip_le_one : 1 / r ≤ (1 : ℝ) := by
    -- The ratio parametrization starts at `r = 1`, so dividing by `r` can only shrink.
    exact one_div_le_one_div_of_le hr_pos hr
  have hfactor_le :
      Real.sqrt (ν : ℝ) / r ≤ Real.sqrt (ν : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_left hrecip_le_one hsqrt_nonneg
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hcoeff_nonneg : 0 ≤ 1 / (2 * Real.sqrt (ν : ℝ)) := by
    positivity
  have hupper :
      (1 / (2 * Real.sqrt (ν : ℝ))) * (Real.sqrt (ν : ℝ) / r) ≤
        (1 / (2 * Real.sqrt (ν : ℝ))) * Real.sqrt (ν : ℝ) := by
    -- After pulling out the step cap, only the harmless factor `1 / r ≤ 1` remains.
    exact mul_le_mul_of_nonneg_left hfactor_le hcoeff_nonneg
  calc
    (r' - r) * (Real.sqrt (ν : ℝ) / r) ≤
        (1 / (2 * Real.sqrt (ν : ℝ))) * (Real.sqrt (ν : ℝ) / r) := hmain
    _ ≤ (1 / (2 * Real.sqrt (ν : ℝ))) * Real.sqrt (ν : ℝ) := hupper
    _ = 1 / 2 := by
          field_simp [hsqrt_pos.ne']
          ring

/-- Helper for Theorem 7.14: rewriting a strict large-branch step by `τ = τ₀ r` reduces the
admissibility inequality to the pure ratio estimate above. -/
private theorem frozenInitialRayRatioStepAdmissible
    (ν : NNReal) (hν : 0 < (ν : ℝ))
    {τ0 r r' : ℝ} (hτ0 : 0 < τ0) (hr : 1 ≤ r)
    (hstep : r' - r ≤ 1 / (2 * Real.sqrt (ν : ℝ))) :
    (τ0 * r' - τ0 * r) * (Real.sqrt (ν : ℝ) / (τ0 * r)) ≤ 1 / 2 := by
  have hr_pos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hrewrite :
      (τ0 * r' - τ0 * r) * (Real.sqrt (ν : ℝ) / (τ0 * r)) =
        (r' - r) * (Real.sqrt (ν : ℝ) / r) := by
    -- Cancel the common positive seed time `τ₀` so the step depends only on the ratio variables.
    field_simp [hτ0.ne', hr_pos.ne']
    ring
  rw [hrewrite]
  -- The normalized ratio step is now exactly the previously proved scalar admissibility bound.
  exact frozenInitialRayRatioIncrement_admissible ν hν hr hstep

/-- Helper for Theorem 7.14: the canonical affine partition of `[1, R]` has the expected
endpoints and a constant mesh `(R - 1) / N` on every subinterval. -/
private theorem affineRatioPartition_endpoints_and_step
    {R : ℝ} (hR : 1 ≤ R) {N : ℕ} (hN : 0 < N) :
    let r : ℕ → ℝ := fun j ↦ 1 + (j : ℝ) * ((R - 1) / N)
    r 0 = 1 ∧
      r N = R ∧
      ∀ j < N, 1 ≤ r j ∧ r (j + 1) - r j = (R - 1) / N := by
  intro r
  have hN_ne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  have hstep_nonneg : 0 ≤ (R - 1) / N := by
    have hR_sub_nonneg : 0 ≤ R - 1 := by
      linarith
    exact div_nonneg hR_sub_nonneg (show 0 ≤ (N : ℝ) by positivity)
  refine ⟨by simp [r], ?_, ?_⟩
  · -- Clear the positive denominator once to recover the right endpoint `R`.
    have hcancel : (N : ℝ) * ((R - 1) / N) = R - 1 := by
      field_simp [hN_ne]
      ring
    calc
      r N = 1 + (N : ℝ) * ((R - 1) / N) := by simp [r]
      _ = 1 + (R - 1) := by rw [hcancel]
      _ = R := by ring
  · intro j hj
    constructor
    · -- Every interior ratio-partition node stays to the right of the base point `1`.
      have hj_nonneg : 0 ≤ (j : ℝ) := by positivity
      calc
        1 ≤ 1 + (j : ℝ) * ((R - 1) / N) := by
              have hmul_nonneg :
                  0 ≤ (j : ℝ) * ((R - 1) / N) := mul_nonneg hj_nonneg hstep_nonneg
              linarith
        _ = r j := by simp [r]
    · -- Consecutive partition nodes differ by the constant affine mesh.
      calc
        r (j + 1) - r j =
            (1 + ((j + 1 : ℕ) : ℝ) * ((R - 1) / N)) -
              (1 + (j : ℝ) * ((R - 1) / N)) := by
                simp [r]
        _ = (R - 1) / N := by ring

/-- Helper for Theorem 7.14: once the affine partition mesh is chosen below the normalized
admissibility threshold, every ratio substep satisfies the one-step large-branch hypothesis. -/
private theorem affineRatioPartition_step_le_admissible
    (ν : NNReal) (hν : 0 < (ν : ℝ))
    {R : ℝ} (hR : 1 ≤ R) {N : ℕ} (hN : 0 < N)
    (hmesh : (R - 1) / N ≤ 1 / (2 * Real.sqrt (ν : ℝ))) :
    let r : ℕ → ℝ := fun j ↦ 1 + (j : ℝ) * ((R - 1) / N)
    ∀ j < N, r (j + 1) - r j ≤ 1 / (2 * Real.sqrt (ν : ℝ)) := by
  intro r j hj
  have hstep :
      r (j + 1) - r j = (R - 1) / N := by
    have hbasic := affineRatioPartition_endpoints_and_step (R := R) hR hN
    simpa [r] using (hbasic.2.2 j hj).2
  -- The affine partition uses the same mesh on every step, so the global mesh bound suffices.
  rw [hstep]
  exact hmesh

/-- Helper for Theorem 7.14: summing the constant mesh of the affine ratio partition recovers the
total ratio growth `R - 1`. -/
private theorem affineRatioPartition_sum_mesh_eq_total
    {R : ℝ} {N : ℕ} (hN : 0 < N) :
    ∑ _j ∈ Finset.range N, ((R - 1) / N : ℝ) = R - 1 := by
  have hN_ne : (N : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)
  -- Expand the constant sum once, then clear the positive denominator `N`.
  calc
    ∑ _j ∈ Finset.range N, ((R - 1) / N : ℝ) =
        ∑ _j in Finset.range N, ((R - 1) / N : ℝ) := by
          simp
    _ = (N : ℝ) * ((R - 1) / N) := by
          simp
    _ = R - 1 := by
          field_simp [hN_ne]
          ring

/-- Helper for Theorem 7.14: the total quadratic mesh budget of the affine ratio partition is
bounded by the square of the full ratio excess `R - 1`. -/
private theorem affineRatioPartition_sum_meshSquare_le_totalSquare
    {R : ℝ} {N : ℕ} (hN : 0 < N) :
    ∑ _j ∈ Finset.range N, (((R - 1) / N : ℝ) ^ (2 : ℕ)) ≤ (R - 1) ^ (2 : ℕ) := by
  have hN_pos : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hN_ge_one : (1 : ℝ) ≤ N := by
    exact_mod_cast Nat.succ_le_of_lt hN
  -- The partition has `N` copies of the same squared mesh, so only the factor `1 / N ≤ 1`
  -- remains after cancellation.
  calc
    ∑ _j ∈ Finset.range N, (((R - 1) / N : ℝ) ^ (2 : ℕ)) =
        ∑ _j in Finset.range N, (((R - 1) / N : ℝ) ^ (2 : ℕ)) := by
          simp
    _ = (N : ℝ) * (((R - 1) / N : ℝ) ^ (2 : ℕ)) := by
          simp
    _ ≤ (R - 1) ^ (2 : ℕ) := by
          have hmain :
              (N : ℝ) * ((((R - 1) / N : ℝ)) ^ (2 : ℕ)) =
                ((R - 1) ^ (2 : ℕ)) / N := by
            field_simp [hN_pos.ne']
            ring
          rw [hmain]
          exact (div_le_iff₀ hN_pos).2 <| by
            nlinarith

/-- Helper for Theorem 7.14: every ratio interval `[1, R]` admits an explicit affine partition
whose constant mesh is below the admissibility threshold `1 / (2 * √ν)`. -/
private theorem affineRatioPartition_meshExists
    (ν : NNReal) (hν : 0 < (ν : ℝ))
    {R : ℝ} (hR : 1 ≤ R) :
    ∃ N : ℕ, 0 < N ∧ (R - 1) / N ≤ 1 / (2 * Real.sqrt (ν : ℝ)) := by
  let N : ℕ := max 1 (Nat.ceil (2 * Real.sqrt (ν : ℝ) * (R - 1)))
  refine ⟨N, ?_, ?_⟩
  · -- The explicit partition size is at least `1`, so the affine mesh is well-defined.
    dsimp [N]
    exact lt_of_lt_of_le zero_lt_one (Nat.le_max_left 1 _)
  · have hR_sub_nonneg : 0 ≤ R - 1 := by
      linarith
    have hsqrt_pos : 0 < Real.sqrt (ν : ℝ) := Real.sqrt_pos.2 hν
    have hden_pos : 0 < 2 * Real.sqrt (ν : ℝ) := by
      positivity
    have hN_pos : 0 < N := by
      dsimp [N]
      exact lt_of_lt_of_le zero_lt_one (Nat.le_max_left 1 _)
    have hN_real_pos : (0 : ℝ) < N := by
      exact_mod_cast hN_pos
    have hceil_le : 2 * Real.sqrt (ν : ℝ) * (R - 1) ≤ N := by
      have hceil :
          2 * Real.sqrt (ν : ℝ) * (R - 1) ≤
            Nat.ceil (2 * Real.sqrt (ν : ℝ) * (R - 1)) := by
        exact Nat.le_ceil _
      have hmax :
          (Nat.ceil (2 * Real.sqrt (ν : ℝ) * (R - 1)) : ℝ) ≤ N := by
        exact_mod_cast Nat.le_max_right 1 (Nat.ceil (2 * Real.sqrt (ν : ℝ) * (R - 1)))
      exact le_trans hceil hmax
    have hscaled :
        R - 1 ≤ N / (2 * Real.sqrt (ν : ℝ)) := by
      exact (le_div_iff₀ hden_pos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hceil_le
    -- Divide once more by the positive partition size to obtain the mesh bound.
    exact (div_le_iff₀ hN_real_pos).2 <| by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- Helper for Theorem 7.14: in the threshold case `ρ = 1 / 3`, once the final covector is
identified with the seed covector, the remaining task is to convert the seed value cap `β / 12`
into the exact initial-correction bound `≤ β * ν`. -/
private theorem thresholdInitialCorrection_le_of_one_le
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hboundary : HasBarrierBoundaryGrowthOn P method.F)
    (hfront : (frontier P).Nonempty)
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let ρ : ℝ := (S / β) * δ0
    ρ = 1 / 3 →
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        β * (ν : ℝ) := by
  intro β S δ0 xBar ρ hρ_eq
  have hν_one : 1 ≤ (ν : ℝ) := by
    exact_mod_cast
      IsSelfConcordantBarrierOnWith.one_le_parameter_of_nonempty_boundaryGrowth
        (dom := P) (ν := ν) (F := method.F)
        ⟨(method 0 : E), (method 0).2⟩ hfront inferInstance hboundary
  have hlinear :
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        S * δ0 * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) := by
    -- Start from the existing source-facing linear control of the initial correction term.
    simpa [β, S, δ0, xBar] using method.initialCorrectionLinearControl ν hH k
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hsqrt_le : Real.sqrt (ν : ℝ) ≤ (ν : ℝ) := by
    have hν_nonneg : 0 ≤ (ν : ℝ) := by
      exact_mod_cast ν.2
    have hsqrt_nonneg : 0 ≤ Real.sqrt (ν : ℝ) := Real.sqrt_nonneg _
    -- The threshold scalar cleanup only needs the standard consequence `√ν ≤ ν` of `1 ≤ ν`.
    nlinarith [Real.sq_sqrt hν_nonneg, hν_one]
  have hcoeff :
      (ν : ℝ) + 2 * Real.sqrt (ν : ℝ) ≤ 3 * (ν : ℝ) := by
    -- Collapse the analytic-center radius factor to `3 ν` once `ν ≥ 1`.
    nlinarith
  have hscalar :
      ρ * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) ≤ (ν : ℝ) := by
    -- Insert the threshold normalization `ρ = 1 / 3` only at the last scalar step.
    rw [hρ_eq]
    nlinarith
  have hscaled :
      S * δ0 * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) ≤ β * (ν : ℝ) := by
    have hρ_rewrite :
        S * δ0 * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) =
          β * (ρ * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ))) := by
      -- Rewrite the frozen scalar `S δ₀` as `β ρ` before applying the threshold scalar bound.
      dsimp [ρ]
      field_simp [hβ_pos.ne']
      ring
    calc
      S * δ0 * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ))
          = β * (ρ * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ))) := hρ_rewrite
      _ ≤ β * (ν : ℝ) := by
            exact mul_le_mul_of_nonneg_left hscalar hβ_pos.le
  exact le_trans hlinear hscaled

/-- Helper for Theorem 7.14: in the threshold case `ρ = 1 / 3`, once the final covector is
identified with the seed covector, the remaining task is to convert the seed value cap `β / 12`
into the exact initial-correction bound `≤ β * ν`. -/
private theorem thresholdSeedValue_to_initialCorrectionReduction
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
    Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 ≤ β / 12 →
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        β / 12 + β * (method.F (xBar : E) - method.F (method 0 : E)) := by
  intro β S xBar s0 hseed
  have hmax :
      IsMaxOn
        (fun v : E ↦
          s0 (v - (method 0 : E)) -
            β * (method.F v - method.F (method 0 : E)))
        P
        (method.uStar (method.beta (k + 1)) s0) := by
    -- Evaluate the threshold branch on the frozen initial score surface before inserting the
    -- seed-value cap.
    simpa [β, s0] using
      method.uStar_isMaxOn (x0 := (method 0 : E)) (β := method.beta (k + 1)) (s := s0)
  have hpoint :
      s0 ((xBar : E) - (method 0 : E)) -
          β * (method.F (xBar : E) - method.F (method 0 : E)) ≤
        Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 := by
    have hraw := (isMaxOn_iff.mp hmax) (xBar : E) xBar.2
    simpa [β, s0, method.uβ_value_at_uStar (method.beta (k + 1)) s0] using hraw
  have hrewrite :
      s0 ((xBar : E) - (method 0 : E)) =
        S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) := by
    -- Expand the frozen final covector into the initial-correction scalar.
    simp [s0, ContinuousLinearMap.smul_apply]
  rw [hrewrite] at hpoint
  linarith

/-- Helper for Theorem 7.14: in the threshold case `ρ = 1 / 3`, once the final covector is
identified with the seed covector, the remaining task is to convert the seed value cap `β / 12`
into the exact initial-correction bound `≤ β * ν`. -/
private theorem thresholdSeedValue_le_initialCorrection
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hboundary : HasBarrierBoundaryGrowthOn P method.F)
    (hfront : (frontier P).Nonempty)
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let ρ : ℝ := (S / β) * δ0
    let s0 : StrongDual ℝ E := S • method.dualSubgradient (method 0)
    ρ = 1 / 3 →
      Uβ P method.F (method 0 : E) (method.beta (k + 1)) s0 ≤ β / 12 →
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        β * (ν : ℝ) := by
  intro β S δ0 xBar ρ s0 hρ_eq hseed
  -- Route correction: the threshold branch no longer needs the seed-value detour because the
  -- direct `ρ = 1 / 3` scalar control is already available.
  let _ := hseed
  simpa [β, S, δ0, xBar, ρ] using
    thresholdInitialCorrection_le_of_one_le
      (method := method) ν hboundary hfront hH k hρ_eq

/-- Helper for Theorem 7.14: the large-`ρ` positive-`ν` branch reduces to a seeded frozen-ray
tail estimate and the existing square-gap bridge at the barycenter. -/
private theorem largeRho_initialCorrectionSquareControlOfPositiveNu
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hboundary : HasBarrierBoundaryGrowthOn P method.F)
    (hfront : (frontier P).Nonempty)
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hν : 0 < (ν : ℝ))
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    let ρ : ℝ := (S / β) * δ0
    1 / 3 ≤ ρ →
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        β * (ν : ℝ) * (3 * ρ) ^ (2 : ℕ) := by
  intro β S δ0 xBar ρ hρ
  have hν_one : 1 ≤ (ν : ℝ) := by
    exact_mod_cast
      IsSelfConcordantBarrierOnWith.one_le_parameter_of_nonempty_boundaryGrowth
        (dom := P) (ν := ν) (F := method.F)
        ⟨(method 0 : E), (method 0).2⟩ hfront inferInstance hboundary
  have hlinear :
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        S * δ0 * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) := by
    -- Start from the existing Chapter 5 linear control of the fixed initial correction.
    simpa [β, S, δ0, xBar] using method.initialCorrectionLinearControl ν hH k
  have hβ_pos : 0 < β := by
    simpa [β] using (method.beta (k + 1)).2
  have hν_nonneg : 0 ≤ (ν : ℝ) := by
    exact_mod_cast ν.2
  have hρ_nonneg : 0 ≤ ρ := by
    linarith
  have hsqrt_le : Real.sqrt (ν : ℝ) ≤ (ν : ℝ) := by
    -- Boundary growth still forces `ν ≥ 1`, so `√ν ≤ ν`.
    nlinarith [Real.sq_sqrt hν_nonneg, hν_one]
  have hcoeff :
      (ν : ℝ) + 2 * Real.sqrt (ν : ℝ) ≤ 3 * (ν : ℝ) := by
    -- Collapse the analytic-center radius factor to `3 ν` once `ν ≥ 1`.
    nlinarith
  have hscalar :
      ρ * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) ≤
        (ν : ℝ) * (3 * ρ) ^ (2 : ℕ) := by
    have hthreeρ_ge_one : 1 ≤ 3 * ρ := by
      linarith
    -- In the large branch, the linear factor `ρ` is dominated by the quadratic scale `(3 ρ)^2`.
    nlinarith [hcoeff, hν_nonneg, hρ_nonneg, hthreeρ_ge_one]
  have hscaled :
      S * δ0 * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) ≤
        β * (ν : ℝ) * (3 * ρ) ^ (2 : ℕ) := by
    have hρ_rewrite :
        S * δ0 * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) =
          β * (ρ * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ))) := by
      -- Rewrite the frozen scalar `S δ₀` as `β ρ` before the large-branch scalar cleanup.
      dsimp [ρ]
      field_simp [hβ_pos.ne']
      ring
    calc
      S * δ0 * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ))
          = β * (ρ * ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ))) := hρ_rewrite
      _ ≤ β * ((ν : ℝ) * (3 * ρ) ^ (2 : ℕ)) := by
            exact mul_le_mul_of_nonneg_left hscalar hβ_pos.le
      _ = β * (ν : ℝ) * (3 * ρ) ^ (2 : ℕ) := by ring
  exact le_trans hlinear hscaled

/-- Helper for Theorem 7.14: once the frozen-ray `ω_*` increment lemma is telescoped along a
small-step partition of `[0, ρ]`, it yields the desired quadratic control of the barycenter term.
-/
private theorem initialCorrectionSquareControl_ofFrozenRayPartition
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hboundary : HasBarrierBoundaryGrowthOn P method.F)
    (hfront : (frontier P).Nonempty)
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    let xBar : P := ⟨
      (Finset.range (k + 1)).centerMass
        (fun i ↦ (method.stepSize i : ℝ))
        (fun i ↦ (method i : E)),
      iterate_centerMass_mem_domain (method := method) k⟩
    S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
      β * (ν : ℝ) * (3 * ((S / β) * δ0)) ^ (2 : ℕ) := by
  intro β S δ0 xBar
  have hν_one : 1 ≤ (ν : ℝ) := by
    exact_mod_cast
      IsSelfConcordantBarrierOnWith.one_le_parameter_of_nonempty_boundaryGrowth
        (dom := P) (ν := ν) (F := method.F)
        ⟨(method 0 : E), (method 0).2⟩ hfront inferInstance hboundary
  have hν : 0 < (ν : ℝ) := by
    linarith
  let ρ : ℝ := (S / β) * δ0
  by_cases hsmall : ρ < 1 / 3
  · -- The small branch uses the frozen approximate-center model already proved above.
    simpa [β, S, δ0, xBar, ρ] using
      smallRho_initialCorrectionSquareControl (method := method) ν hH hν_one k hsmall
  · have hlarge : 1 / 3 ≤ ρ := by
      linarith
    -- Route correction: the large branch now closes directly from the linear control theorem.
    simpa [β, S, δ0, xBar, ρ] using
      largeRho_initialCorrectionSquareControlOfPositiveNu
        (method := method) ν hboundary hfront hH hν k hlarge

/-- Helper for Theorem 7.14: the remaining source-faithful positive-`ν` blocker is the Chapter 5
quadratic control of the fixed initial-center correction prefix. -/
private theorem initial_correction_square_control
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hboundary : HasBarrierBoundaryGrowthOn P method.F)
    (hfront : (frontier P).Nonempty)
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (k : ℕ) :
    let β : ℝ := method.beta (k + 1)
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    ∑ i ∈ Finset.range (k + 1),
      (method.stepSize i : ℝ) *
        method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) ≤
      β * (ν : ℝ) * (3 * ((S / β) * δ0)) ^ (2 : ℕ) := by
  intro β S δ0
  let xBar : P := ⟨
    (Finset.range (k + 1)).centerMass
      (fun i ↦ (method.stepSize i : ℝ))
      (fun i ↦ (method i : E)),
    iterate_centerMass_mem_domain (method := method) k⟩
  have hprefix :
      ∑ i ∈ Finset.range (k + 1),
        (method.stepSize i : ℝ) *
          method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) ≤
        S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) := by
    -- First compress the moving correction prefix to the fixed initial covector at the barycenter.
    simpa [xBar] using correction_prefix_le_initial_linear_at_centerMass (method := method) k
  have hcenter :
      S * method.dualSubgradient (method 0) ((xBar : E) - (method 0 : E)) ≤
        β * (ν : ℝ) * (3 * ((S / β) * δ0)) ^ (2 : ℕ) := by
    -- The branch merger already supplies the exact quadratic control at the barycenter.
    simpa [β, S, δ0, xBar] using
      initialCorrectionSquareControl_ofFrozenRayPartition
        (method := method) ν hboundary hfront hH k
  exact le_trans hprefix hcenter

/-- Helper for Theorem 7.14: once `U` is bounded by `A + c d²`, monotonicity of `sqrt` and `log`
upgrades the implicit logarithmic term to the displayed explicit expression. -/
private theorem log_cleanup_after_correction
    {A U c d : ℝ}
    (hc : 0 < c) (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hU : U ≤ A + c * d ^ (2 : ℕ)) :
    c * (1 + 2 * Real.log (1 + Real.sqrt (U / c))) ≤
      c * (1 + 2 * Real.log (1 + Real.sqrt (A / c) + d)) := by
  have hA_div_nonneg : 0 ≤ A / c := by
    exact div_nonneg hA hc.le
  have hU_div :
      U / c ≤ A / c + d ^ (2 : ℕ) := by
    calc
      U / c ≤ (A + c * d ^ (2 : ℕ)) / c := by
        exact div_le_div_of_nonneg_right hU hc.le
      _ = A / c + d ^ (2 : ℕ) := by
        field_simp [hc.ne']
  have hsqrt_bound :
      Real.sqrt (U / c) ≤ Real.sqrt (A / c) + d := by
    calc
      Real.sqrt (U / c) ≤ Real.sqrt (A / c + d ^ (2 : ℕ)) := by
        exact Real.sqrt_le_sqrt hU_div
      _ ≤ Real.sqrt (A / c) + Real.sqrt (d ^ (2 : ℕ)) := by
        simpa using Real.sqrt_add_le (A / c) (d ^ (2 : ℕ))
      _ = Real.sqrt (A / c) + d := by
        simpa [abs_of_nonneg hd] using congrArg (fun t : ℝ ↦ Real.sqrt t) (show d ^ (2 : ℕ) = d ^ 2 by rfl)
  have hleft_pos : 0 < 1 + Real.sqrt (U / c) := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (U / c) := Real.sqrt_nonneg _
    linarith
  have hright_pos : 0 < 1 + Real.sqrt (A / c) + d := by
    have hsqrt_nonneg : 0 ≤ Real.sqrt (A / c) := Real.sqrt_nonneg _
    linarith
  have hlog :
      Real.log (1 + Real.sqrt (U / c)) ≤
        Real.log (1 + Real.sqrt (A / c) + d) := by
    apply Real.log_le_log hleft_pos
    linarith
  have hinside :
      1 + 2 * Real.log (1 + Real.sqrt (U / c)) ≤
        1 + 2 * Real.log (1 + Real.sqrt (A / c) + d) := by
    linarith
  exact mul_le_mul_of_nonneg_left hinside hc.le

/-- Theorem 7.14: if `method.F` is a genuine self-concordant barrier on `P` in the source sense,
so in particular it has the boundary-growth property `HasBarrierBoundaryGrowthOn P method.F`
and `P` has nonempty frontier,
and the barrier-subgradient iterates `x_k ∈ P` have local ratios
`(λ_k / β_k) ‖g_k‖*_(x_k) < 1` and the smoothing parameters satisfy `β_k ≤ β_{k+1}`, then
for every `k ≥ 0` the maximal-gap owner `method.maximalGap k` is bounded by
`A_k + β_{k+1} ν [1 + 2 log (1 + sqrt (A_k / (β_{k+1} ν)) + 3 (S_k / β_{k+1}) ‖g₀‖*_(x₀))]`,
where `x₀ = method 0`, `g₀` is the chosen subgradient at `x₀`,
`S_k = ∑_{i=0}^k λ_i`, and
`A_k = ∑_{i=0}^k β_i ω_* ((λ_i / β_i) ‖g_i‖*_(x_i))`. -/
theorem maximalGap_upper_bound
    (ν : NNReal)
    [IsSelfConcordantBarrierOnWith P ν method.F]
    (hboundary : HasBarrierBoundaryGrowthOn P method.F)
    (hfront : (frontier P).Nonempty)
    (hH : ∀ i : ℕ, (hessian method.F (method i : E)).det ≠ 0)
    (hω :
      ∀ i : ℕ,
        (method.stepSize i : ℝ) *
            HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
              (method.iterate_hessian_isPositive i) (hH i)
              (method.dualSubgradient (method i)) <
          method.beta i)
    (hβ_mono : ∀ i : ℕ, (method.beta i : ℝ) ≤ method.beta (i + 1))
    (k : ℕ) :
    let A := method.accumulatedOmegaStarError hH hω k
    let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
    let δ0 :=
      HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0)
        (method.dualSubgradient (method 0))
    method.maximalGap k ≤
      A +
        (method.beta (k + 1) : ℝ) * (ν : ℝ) *
          (1 +
            2 * Real.log
              (1 +
                Real.sqrt (A / ((method.beta (k + 1) : ℝ) * (ν : ℝ))) +
                3 * ((S / (method.beta (k + 1) : ℝ)) * δ0))) := by
  let _ := hboundary
  -- Route correction: the source-faithful proof factors through the aggregated affine functional
  -- controlled by `s_(k+1) = method.dualIterate (k + 1)`, not through an induction on
  -- `method.maximalGap` itself.
  let A := method.accumulatedOmegaStarError hH hω k
  let S := barrierSubgradientWeightSum (fun i ↦ (method.stepSize i : ℝ)) k
  let δ0 :=
    HessianDualLocalNorm.ofDetNeZero method.F (method 0 : E)
      (method.iterate_hessian_isPositive 0) (hH 0)
      (method.dualSubgradient (method 0))
  have hx0_argmin : (method 0 : E) ∈ argmin[P] method.F :=
    method.initial_iterate_is_barrier_argmin
  have hgap_decomp :
      ∀ y : P,
        method.gapFunction k y =
          method.dualIterate (k + 1) ((y : E) - (method 0 : E)) -
            ∑ i ∈ Finset.range (k + 1),
              (method.stepSize i : ℝ) *
                method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) :=
    method.aggregated_affine_gap_decomposition k
  have hsup_bridge :
      ∀ {B : ℝ},
        (∀ y : P, method.dualIterate (k + 1) ((y : E) - (method 0 : E)) ≤ B) →
          method.maximalGap k ≤
            ((B -
                ∑ i ∈ Finset.range (k + 1),
                  (method.stepSize i : ℝ) *
                    method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) : ℝ) :
              EReal) :=
    fun {B} hB ↦ method.maximalGap_le_of_dualIterate_pointwise_bound k hB
  have hsegment_gap :
      ∀ y : P, ∀ {α : ℝ}, α ∈ Set.Ico (0 : ℝ) 1 →
        α * method.dualIterate (k + 1) ((y : E) - (method 0 : E)) +
            (method.beta (k + 1) : ℝ) * (ν : ℝ) * Real.log (1 - α) ≤
          Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1)) :=
    fun y hα ↦ method.dualIterate_segment_regularized_gap_bound ν k y hα
  have hpointwise_if_pos :
      ∀ hν : 0 < (ν : ℝ), ∀ y : P,
        method.dualIterate (k + 1) ((y : E) - (method 0 : E)) ≤
          Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1)) +
            (method.beta (k + 1) : ℝ) * (ν : ℝ) *
              (1 +
                2 * Real.log
                  (1 +
                    Real.sqrt
                      (Uβ P method.F (method 0 : E) (method.beta (k + 1))
                        (method.dualIterate (k + 1)) /
                        ((method.beta (k + 1) : ℝ) * (ν : ℝ))))) :=
    fun hν y ↦ method.pointwise_dualIterate_bound_from_segment_barrier ν hν k y
  have hmaxGap_if_pos :
      ∀ hν : 0 < (ν : ℝ),
        method.maximalGap k ≤
          ((Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1)) +
                (method.beta (k + 1) : ℝ) * (ν : ℝ) *
                  (1 +
                    2 * Real.log
                      (1 +
                        Real.sqrt
                          (Uβ P method.F (method 0 : E) (method.beta (k + 1))
                            (method.dualIterate (k + 1)) /
                            ((method.beta (k + 1) : ℝ) * (ν : ℝ)))) -
              ∑ i ∈ Finset.range (k + 1),
                (method.stepSize i : ℝ) *
                  method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) :
              ℝ) :
            EReal) := by
    intro hν
    exact hsup_bridge (hpointwise_if_pos hν)
  have hregularized_value :
      Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1)) -
          ∑ i ∈ Finset.range (k + 1),
            (method.stepSize i : ℝ) *
              method.dualSubgradient (method i) ((method i : E) - (method 0 : E)) ≤
        A := by
    -- The Chapter 7 telescope is now reduced to the accumulated `ω_*` error sum `A_k`.
    simpa [A] using
      method.regularized_value_minus_correction_le_accumulated_omegaStar
        ν hH hω hβ_mono k
  by_cases hν0 : ν = 0
  · -- The zero-parameter branch closes immediately because the segment inequality loses its
    -- logarithmic penalty term, so `method.maximalGap k` is already bounded by `A_k`.
    have hzero : method.maximalGap k ≤ A := by
      simpa [A] using
        method.maximalGap_zero_barrier_parameter_branch ν hν0 hH hω hβ_mono k
    simpa [A, S, δ0, hν0] using hzero
  · have hν : 0 < (ν : ℝ) := by
      have hν_nnreal : 0 < ν := by
        exact pos_iff_ne_zero.mpr hν0
      simpa using hν_nnreal
    have hmaxGap_pos := hmaxGap_if_pos hν
    let U :=
      Uβ P method.F (method 0 : E) (method.beta (k + 1)) (method.dualIterate (k + 1))
    let correction : ℝ :=
      ∑ i ∈ Finset.range (k + 1),
        (method.stepSize i : ℝ) *
          method.dualSubgradient (method i) ((method i : E) - (method 0 : E))
    let c : ℝ := (method.beta (k + 1) : ℝ) * (ν : ℝ)
    let d : ℝ := 3 * ((S / (method.beta (k + 1) : ℝ)) * δ0)
    have hc : 0 < c := by
      simpa [c] using mul_pos (method.beta (k + 1)).2 hν
    have hcorrection :
        correction ≤ c * d ^ (2 : ℕ) := by
      -- This is the only remaining source-faithful blocker from the Chapter 5 owner estimate.
      simpa [correction, c, d] using
        method.initial_correction_square_control ν hboundary hfront hH k
    have hU_bound : U ≤ A + c * d ^ (2 : ℕ) := by
      -- Combine the Chapter 7 telescope with the fixed correction estimate.
      linarith [hregularized_value, hcorrection]
    have hA_nonneg : 0 ≤ A := by
      -- Each `β_i ω_* (...)` summand in `A_k` is nonnegative.
      rw [A, method.accumulatedOmegaStarError_def]
      refine Finset.sum_nonneg ?_
      intro i hi
      dsimp
      let δi :=
        HessianDualLocalNorm.ofDetNeZero method.F (method i : E)
          (method.iterate_hessian_isPositive i) (hH i)
          (method.dualSubgradient (method i))
      have hδi_nonneg : 0 ≤ δi := by
        dsimp [δi]
        exact dualLocalNorm_nonneg method.F (method i : E)
          (method.iterate_hessian_isPositive i) (hH i) (method.dualSubgradient (method i))
      let τi : Set.Iio (1 : ℝ) := ⟨
        (method.stepSize i : ℝ) * δi / method.beta i,
        by
          have hlt : (method.stepSize i : ℝ) * δi < (method.beta i : ℝ) := by
            simpa [δi] using hω i
          exact (div_lt_iff₀ (method.beta i).2).2 (by simpa using hlt)⟩
      have hω_nonneg : 0 ≤ selfConcordantOmegaStar τi := by
        rw [selfConcordantOmegaStar_apply]
        have hlog_le : Real.log (1 - (τi : ℝ)) ≤ -(τi : ℝ) := by
          have hpos : 0 < 1 - (τi : ℝ) := sub_pos.mpr τi.2
          simpa using Real.log_le_sub_one_of_pos hpos
        linarith
      exact mul_nonneg (method.beta i).2.le hω_nonneg
    have hS_nonneg : 0 ≤ S := by
      dsimp [S]
      rw [barrierSubgradientWeightSum_def]
      exact Finset.sum_nonneg fun i hi ↦ (method.stepSize i).2.le
    have hδ0_nonneg : 0 ≤ δ0 := by
      exact dualLocalNorm_nonneg method.F (method 0 : E)
        (method.iterate_hessian_isPositive 0) (hH 0) (method.dualSubgradient (method 0))
    have hd_nonneg : 0 ≤ d := by
      dsimp [d]
      nlinarith
    have hlog_term :
        c * (1 + 2 * Real.log (1 + Real.sqrt (U / c))) ≤
          c * (1 + 2 * Real.log (1 + Real.sqrt (A / c) + d)) := by
      exact log_cleanup_after_correction hc hA_nonneg hd_nonneg hU_bound
    have hmain :
        U + c * (1 + 2 * Real.log (1 + Real.sqrt (U / c))) - correction ≤
          A + c * (1 + 2 * Real.log (1 + Real.sqrt (A / c) + d)) := by
      -- Add the logarithmic term to the Chapter 7 telescope and then replace `sqrt (U / c)` by
      -- the explicit `sqrt (A / c) + d`.
      linarith [hregularized_value, hlog_term]
    have hmain_ereal :
        ((U + c * (1 + 2 * Real.log (1 + Real.sqrt (U / c))) - correction : ℝ) : EReal) ≤
          ((A + c * (1 + 2 * Real.log (1 + Real.sqrt (A / c) + d)) : ℝ) : EReal) := by
      exact_mod_cast hmain
    refine le_trans ?_ hmain_ereal
    simpa [U, correction, c] using hmaxGap_pos

end

end DualBarrierSubgradientMethod
