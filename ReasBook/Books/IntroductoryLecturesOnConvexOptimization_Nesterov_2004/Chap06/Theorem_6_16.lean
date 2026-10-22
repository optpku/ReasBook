/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Algorithm_6_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators ConstrainedArgmin Gradient WeightSequenceNotation WithTopConvexAnalysis

universe u

namespace SecondOrderLocalModel

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 6.16 lies in the Chapter 6 second-order composite trust-region domain.

Mandatory owner-style sampling before refining:
- `CompositeTrustRegionContractionMethod` in `Algorithm_6_6`, the chapter's recursive owner for
  method `(6.4.50)`;
- `secondOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the canonical quadratic Taylor-model
  owner;
- `contractedCompositeSecondOrderModel` in `Algorithm_6_6`, the chapter owner of the contracted
  quadratic composite subproblem;
- `ConditionalGradientContraction.estimatingFunctionalSequence` in `Theorem_6_14`, the chapter
  owner for recursive estimating-function families.

Best owner abstraction:
- source-facing: this theorem's second-order estimating function, error recursion, and
  second-order optimality measure on the finite feasible domain;
- core/canonical: `CompositeTrustRegionContractionMethod`, `secondOrderTaylorModelAt`,
  `contractedCompositeSecondOrderModel`, and
  `ConditionalGradientContraction.estimatingFunctionalSequence`;
- bridge/view: the finite-value representative `withTopRealPart problem.nonsmoothPart` and the
  iterate restriction to `Q ∩ dom Ψ`.

Primitive data:
- the ambient composite problem `problem`;
- the initial feasible point `x0`;
- the recursive method owner `method : CompositeTrustRegionContractionMethod problem x0`.

Derived API:
- the specialized estimating sequence for the initial model
  `f + withTopRealPart Ψ`;
- the recursive second-order error term;
- the source-facing second-order optimality measure on `Q ∩ dom Ψ`. -/

/-- The increment added at step `t + 1` to the second-order error term `\hat C_{ν,t}`. -/
def secondOrderErrorIncrement
    (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) (t : ℕ) : ℝ :=
  (a (t + 1) * a (t + 1) / A[a]((t + 1))) *
      (Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) +
    (a (t + 1) * a (t + 1) / ((2 : ℝ) * A[a]((t + 1)))) * L * D * D

/-- Expanding `secondOrderErrorIncrement a L Hν D ν t` gives the `H_ν D^{2+ν}` and `L D^2`
contributions added at step `t + 1`, with the canonical Chapter 6 denominator `A[a](t + 1)`. -/
theorem secondOrderErrorIncrement_apply
    (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) (t : ℕ) :
    secondOrderErrorIncrement a L Hν D ν t =
      (a (t + 1) * a (t + 1) / A[a]((t + 1))) *
          (Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) +
        (a (t + 1) * a (t + 1) / ((2 : ℝ) * A[a]((t + 1)))) * L * D * D :=
  rfl

/-- The recursive error term `\hat C_{ν,t}` for the second-order local-model method, using the
canonical accumulated weights `A[a](t)`. -/
def secondOrderError
    (initialError : ℝ) (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) : ℕ → ℝ
  | 0 => initialError
  | t + 1 => secondOrderError initialError a L Hν D ν t +
      secondOrderErrorIncrement a L Hν D ν t

/-- The second-order error term starts from the prescribed initial gap. -/
theorem secondOrderError_zero
    (initialError : ℝ) (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) :
    secondOrderError initialError a L Hν D ν 0 = initialError :=
  rfl

/-- The recursive step for `\hat C_{ν,t}` adds the increment from
`secondOrderErrorIncrement a L Hν D ν t`. -/
theorem secondOrderError_succ
    (initialError : ℝ) (a : ℕ → ℝ) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) (t : ℕ) :
    secondOrderError initialError a L Hν D ν (t + 1) =
      secondOrderError initialError a L Hν D ν t +
        secondOrderErrorIncrement a L Hν D ν t :=
  rfl

/-- The second-order optimality measure `θ(x)` is the maximal decrease predicted by the canonical
second-order Taylor model of `f` plus the regularizer gap at a finite feasible point
`x ∈ Q ∩ dom Ψ`, recorded in `EReal` so the owner remains faithful even when the supremum is not
bounded above in `ℝ`. -/
def secondOrderOptimalityMeasure
    (Q : Set E) (f : E → ℝ) (Ψ : E → WithTop ℝ) :
    ((Q ∩ dom Ψ : Set E)) → EReal :=
  fun x ↦
    sSup ((fun y : E ↦
      (((f x + withTopRealPart Ψ x) -
            (secondOrderTaylorModelAt f x y + withTopRealPart Ψ y) : ℝ) : EReal)) ''
      (Q ∩ dom Ψ))

namespace SecondOrderOptimalityMeasureNotation

/- Source-facing Lean notation for the textbook second-order optimality measure `θ(x)` with the
ambient feasible set and composite objective data fixed by the surrounding context. -/
scoped notation:max "θ[" Q ", " f ", " Ψ "](" x:arg ")" =>
  secondOrderOptimalityMeasure Q f Ψ x

end SecondOrderOptimalityMeasureNotation

open scoped SecondOrderOptimalityMeasureNotation

/-- Expanding `θ[Q, f, Ψ](x)` gives the defining `EReal` supremum of the canonical second-order
Taylor-model decrease over the finite feasible domain `Q ∩ dom Ψ`. -/
theorem secondOrderOptimalityMeasure_def
    (Q : Set E) (f : E → ℝ) (Ψ : E → WithTop ℝ) (x : (Q ∩ dom Ψ : Set E)) :
    θ[Q, f, Ψ](x) =
      sSup ((fun y : E ↦
        (((f x + withTopRealPart Ψ x) -
              (secondOrderTaylorModelAt f x y + withTopRealPart Ψ y) : ℝ) : EReal)) ''
        (Q ∩ dom Ψ)) :=
  rfl

section Method

variable {problem : CompositeConvexMinimizationProblem E} {x0 : problem.feasibleSet}

/-- Every iterate lies in the finite-value domain `Q ∩ dom Ψ`, because the method stays in `Q`
and `Ψ` is finite on `Q` by the owner hypothesis `ClosedConvexOn Q Ψ`. -/
theorem iterate_mem_optimalityDomain
    (method : CompositeTrustRegionContractionMethod problem x0) (t : ℕ) :
    method t ∈ problem.feasibleSet ∩ dom problem.nonsmoothPart := by
  exact ⟨method.iterates_mem_feasibleSet t,
    problem.nonsmoothPart_closedConvex.subset_withTopEffectiveDomain
      (method.iterates_mem_feasibleSet t)⟩

/-- The estimating sequence `φ_t` attached to Algorithm 6.6, obtained by specializing the
chapter owner `estimatingFunctionalSequence` to the initial model
`f + withTopRealPart Ψ`. -/
def estimatingFunction
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ) :
    ℕ → E → ℝ :=
  ConditionalGradientContraction.estimatingFunctionalSequence
    a
    (fun x ↦ problem.smoothPart x + withTopRealPart problem.nonsmoothPart x)
    problem.smoothPart
    (fun x ↦ InnerProductSpace.toDualMap ℝ E (∇ problem.smoothPart x))
    (withTopRealPart problem.nonsmoothPart)
    method

/-- The estimating sequence starts from `φ₀(x) = a₀ \bar f(x)`. -/
theorem estimatingFunction_zero
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ) :
    estimatingFunction method a 0 =
      fun x ↦ a 0 * (problem.smoothPart x + withTopRealPart problem.nonsmoothPart x) :=
  rfl

/-- The recursive step of the estimating sequence is
`φ_{t+1}(x) = φ_t(x) + a_{t+1} [f(x_t) + ⟪∇ f(x_t), x - x_t⟫ + Ψ(x)]`. -/
theorem estimatingFunction_succ
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ) (t : ℕ) :
    estimatingFunction method a (t + 1) =
      fun x ↦
        estimatingFunction method a t x +
          a (t + 1) *
            (problem.smoothPart (method t) +
              inner ℝ (∇ problem.smoothPart (method t)) (x - method t) +
              withTopRealPart problem.nonsmoothPart x) :=
  rfl

/-- The canonical error sequence `\hat C_{ν,t}` anchored at the baseline point `xStar`. -/
def errorTerm
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ)
    (xStar : E) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) : ℕ → ℝ :=
  secondOrderError
    (a 0 *
      ((problem.smoothPart (method 0) + withTopRealPart problem.nonsmoothPart (method 0)) -
        (problem.smoothPart xStar + withTopRealPart problem.nonsmoothPart xStar)))
    a L Hν D ν

/-- Expanding `errorTerm method a xStar L Hν D ν` gives the recursive second-order error term
starting from the weighted initial objective gap at `x₀` relative to `xStar`. -/
theorem errorTerm_def
    (method : CompositeTrustRegionContractionMethod problem x0) (a : ℕ → ℝ)
    (xStar : E) (L Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1) :
    errorTerm method a xStar L Hν D ν =
      secondOrderError
        (a 0 *
          ((problem.smoothPart (method 0) + withTopRealPart problem.nonsmoothPart (method 0)) -
            (problem.smoothPart xStar + withTopRealPart problem.nonsmoothPart xStar)))
        a L Hν D ν :=
  rfl

/-- Helper for Theorem 6.16: every successor iterate lies within `τ_t D` of the current iterate,
because Algorithm 6.6 keeps the next point in the contracted feasible set. -/
private lemma secondOrderSuccessorNormLeStepSizeMulDiameter
    (method : CompositeTrustRegionContractionMethod problem x0) {D : ℝ}
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (t : ℕ) :
    ‖method (t + 1) - method t‖ ≤ method.stepSize t * D := by
  let τ := method.stepSize t
  have hτ_nonneg : 0 ≤ τ := (method.stepSize_mem_Ioc t).1.le
  rcases (mem_contractedFeasibleSet_iff.mp
    (method.iterates_succ_mem_and_isMinOn t).1) with ⟨y, hy, hyEq⟩
  -- Rewrite the successor displacement through the contracted-feasible-set witness.
  calc
    ‖method (t + 1) - method t‖ = ‖τ • (y - method t)‖ := by
      rw [hyEq]
      dsimp [τ]
      simp [sub_eq_add_neg, smul_add, add_smul, add_left_comm, add_comm]
    _ = τ * ‖y - method t‖ := by
      simpa [Real.norm_of_nonneg hτ_nonneg] using norm_smul τ (y - method t)
    _ ≤ τ * D := by
      exact mul_le_mul_of_nonneg_left (hdiam hy (method.iterates_mem_feasibleSet t)) hτ_nonneg

/-- Helper for Theorem 6.16: a uniform real bound on the quadratic comparison gap packages
directly into an `EReal` upper bound for `θ[problem.feasibleSet, problem.smoothPart,
problem.nonsmoothPart](method t)`. -/
private lemma secondOrderOptimalityMeasure_le_of_realBound
    (method : CompositeTrustRegionContractionMethod problem x0) (t : ℕ) {B : ℝ}
    (hB :
      ∀ y : E, y ∈ problem.feasibleSet →
        (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (secondOrderTaylorModelAt problem.smoothPart (method t) y +
              withTopRealPart problem.nonsmoothPart y) ≤
          B) :
    θ[problem.feasibleSet, problem.smoothPart, problem.nonsmoothPart](
        ⟨method t, iterate_mem_optimalityDomain method t⟩) ≤
      (B : EReal) := by
  -- Rewrite `θ` to its defining supremum and bound each feasible-domain term by the same real
  -- constant `B`.
  rw [secondOrderOptimalityMeasure_def]
  refine sSup_le ?_
  intro y hy
  rcases hy with ⟨z, hz, rfl⟩
  change (((problem.smoothPart (method t) +
        withTopRealPart problem.nonsmoothPart (method t) -
          (secondOrderTaylorModelAt problem.smoothPart (method t) z +
            withTopRealPart problem.nonsmoothPart z) : ℝ) : EReal)) ≤
      (B : EReal)
  exact_mod_cast hB z hz.1

/-- Helper for Theorem 6.16: the successor accumulated weight splits as
`A[a](t + 1) = A[a](t) + a (t + 1)`. -/
private lemma accumulatedWeights_succ
    (a : ℕ → ℝ) (t : ℕ) :
    accumulatedWeights a (t + 1) = A[a](t) + a (t + 1) := by
  -- Expand both accumulated weights and peel off the last summand.
  rw [accumulatedWeights_apply, accumulatedWeights_apply, Finset.sum_range_succ]

/-- Helper for Theorem 6.16: positive weights force every accumulated weight `A[a](t)` to be
strictly positive. -/
private lemma accumulatedWeights_pos
    (a : ℕ → ℝ) (ha_pos : ∀ t : ℕ, 0 < a t) :
    ∀ t : ℕ, 0 < A[a](t) := by
  intro t
  induction t with
  | zero =>
      -- At the initial index, the accumulated weight is exactly `a₀`.
      simpa [accumulatedWeights_apply] using ha_pos 0
  | succ t ih =>
      -- Each successor accumulated weight adds the positive term `a_{t+1}`.
      rw [accumulatedWeights_succ]
      linarith [ih, ha_pos (t + 1)]

/-- Helper for Theorem 6.16: after rewriting `τ[a](t) = a (t + 1) / A[a](t + 1)`, multiplying a
convex-combination step by `A[a](t + 1)` recovers the canonical weighted successor form. -/
private lemma successor_weighted_average_rescaling
    (a : ℕ → ℝ) (ha_pos : ∀ t : ℕ, 0 < a t) (t : ℕ) (u v : ℝ) :
    accumulatedWeights a (t + 1) * ((1 - τ[a](t)) * u + τ[a](t) * v) =
      accumulatedWeights a t * u + a (t + 1) * v := by
  have hA_pos : 0 < accumulatedWeights a (t + 1) :=
    accumulatedWeights_pos a ha_pos (t + 1)
  have hA_ne : accumulatedWeights a (t + 1) ≠ 0 := hA_pos.ne'
  -- Route correction: rewrite the coefficient once, then clear the denominator by field
  -- arithmetic instead of repeatedly normalizing `τ[a](t)` in the main proof.
  rw [weightCoefficient_apply]
  field_simp [hA_ne]
  rw [accumulatedWeights_succ]
  ring_nf

/-- Helper for Theorem 6.16: the weighted quadratic successor increment is exactly
`(a (t + 1)^2 / (2 * A[a](t + 1))) * L * D^2`. -/
private lemma weightCoefficient_square_rescaling
    (a : ℕ → ℝ) (ha_pos : ∀ t : ℕ, 0 < a t) (L D : ℝ) (t : ℕ) :
    accumulatedWeights a (t + 1) *
        ((τ[a](t)) ^ (2 : ℕ) * ((L / 2) * D * D)) =
      (a (t + 1) * a (t + 1) / ((2 : ℝ) * accumulatedWeights a (t + 1))) * L * D * D := by
  have hA_pos : 0 < accumulatedWeights a (t + 1) :=
    accumulatedWeights_pos a ha_pos (t + 1)
  have hA_ne : accumulatedWeights a (t + 1) ≠ 0 := hA_pos.ne'
  -- Rewrite `τ_t` by its defining quotient and clear denominators once.
  rw [weightCoefficient_apply]
  field_simp [hA_ne]

/-- Helper for Theorem 6.16: since `τ[a](t) ∈ (0, 1]`, its `2 + ν` power is bounded by `τ[a](t)^2`
for every `ν ∈ [0, 1]`. -/
private lemma weightCoefficient_rpow_le_sq
    (a : ℕ → ℝ) (ha_pos : ∀ t : ℕ, 0 < a t) (ν : Set.Icc (0 : ℝ) 1) (t : ℕ) :
    Real.rpow (τ[a](t)) (2 + (ν : ℝ)) ≤ (τ[a](t)) ^ (2 : ℕ) := by
  have hA_pos : 0 < accumulatedWeights a (t + 1) :=
    accumulatedWeights_pos a ha_pos (t + 1)
  have hτ_pos : 0 < τ[a](t) := by
    rw [weightCoefficient_apply]
    exact div_pos (ha_pos (t + 1)) hA_pos
  have hτ_nonneg : 0 ≤ τ[a](t) := hτ_pos.le
  have hτ_le_one : τ[a](t) ≤ 1 := by
    rw [weightCoefficient_apply]
    refine (div_le_one hA_pos).2 ?_
    have hAprev_nonneg : 0 ≤ accumulatedWeights a t :=
      (accumulatedWeights_pos a ha_pos t).le
    rw [accumulatedWeights_succ]
    linarith [ha_pos (t + 1), hAprev_nonneg]
  have hν_nonneg : 0 ≤ (ν : ℝ) := ν.2.1
  have hpow_le_one : Real.rpow (τ[a](t)) (ν : ℝ) ≤ 1 := by
    exact Real.rpow_le_one hτ_nonneg hτ_le_one hν_nonneg
  have hpow_two : Real.rpow (τ[a](t)) (2 : ℝ) = (τ[a](t)) ^ (2 : ℕ) := by
    simpa using (Real.rpow_natCast (τ[a](t)) 2)
  have hsplit :
      Real.rpow (τ[a](t)) (2 + (ν : ℝ)) =
        (τ[a](t)) ^ (2 : ℕ) * Real.rpow (τ[a](t)) (ν : ℝ) := by
    calc
      Real.rpow (τ[a](t)) (2 + (ν : ℝ)) =
          Real.rpow (τ[a](t)) (2 : ℝ) * Real.rpow (τ[a](t)) (ν : ℝ) := by
            simpa using (Real.rpow_add hτ_pos (2 : ℝ) (ν : ℝ))
      _ = (τ[a](t)) ^ (2 : ℕ) * Real.rpow (τ[a](t)) (ν : ℝ) := by
            rw [hpow_two]
  rw [hsplit]
  nlinarith

/-- Helper for Theorem 6.16: after weakening `τ[a](t)^(2 + ν)` to `τ[a](t)^2`, multiplying by
`A[a](t + 1)` yields the exact `Hν D^(2+ν)` term in `secondOrderErrorIncrement`. -/
private lemma weightCoefficient_holder_rescaling
    (a : ℕ → ℝ) (ha_pos : ∀ t : ℕ, 0 < a t)
    (Hν D : ℝ) (ν : Set.Icc (0 : ℝ) 1)
    (hHν_nonneg : 0 ≤ Hν) (hD_nonneg : 0 ≤ D) (t : ℕ) :
    accumulatedWeights a (t + 1) *
        (((Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) *
            Real.rpow (τ[a](t)) (2 + (ν : ℝ))) : ℝ) ≤
      (a (t + 1) * a (t + 1) / accumulatedWeights a (t + 1)) *
        (Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) := by
  have hA_nonneg : 0 ≤ accumulatedWeights a (t + 1) :=
    (accumulatedWeights_pos a ha_pos (t + 1)).le
  have hconst_nonneg :
      0 ≤ Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
    have hν1_pos : 0 < 1 + (ν : ℝ) := by
      linarith [ν.2.1]
    have hν2_pos : 0 < 2 + (ν : ℝ) := by
      linarith [ν.2.1]
    have hdenom_pos : 0 < ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
      positivity
    have hrpow_nonneg : 0 ≤ Real.rpow D (2 + (ν : ℝ)) := Real.rpow_nonneg hD_nonneg _
    positivity
  have hpow_le := weightCoefficient_rpow_le_sq a ha_pos ν t
  have hmul_le :
      accumulatedWeights a (t + 1) *
          (((Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) *
              Real.rpow (τ[a](t)) (2 + (ν : ℝ))) : ℝ) ≤
        accumulatedWeights a (t + 1) *
          (((Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) *
              (τ[a](t)) ^ (2 : ℕ)) : ℝ) := by
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpow_le hconst_nonneg) hA_nonneg
  have hA_pos : 0 < accumulatedWeights a (t + 1) :=
    accumulatedWeights_pos a ha_pos (t + 1)
  have hA_ne : accumulatedWeights a (t + 1) ≠ 0 := hA_pos.ne'
  have hrewrite :
      accumulatedWeights a (t + 1) *
          (((Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) *
              (τ[a](t)) ^ (2 : ℕ)) : ℝ) =
        (a (t + 1) * a (t + 1) / accumulatedWeights a (t + 1)) *
          (Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) := by
    rw [weightCoefficient_apply]
    field_simp [hA_ne]
  exact hmul_le.trans_eq hrewrite

/-- Helper for Theorem 6.16: evaluating the frozen quadratic model at the contracted comparison
point produces the affine model plus the explicit `L D^2 τ_t^2 / 2` error term. -/
private lemma contractedSecondOrderModel_le_affineModel_addQuadraticError
    (method : CompositeTrustRegionContractionMethod problem x0) {L D : ℝ}
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (h_hessian_bound : ∀ t : ℕ, ‖hessian problem.smoothPart (method t)‖ ≤ L)
    (t : ℕ) {x : E} (hx : x ∈ problem.feasibleSet) :
    let τ := method.stepSize t
    let z : E := (1 - τ) • method t + τ • x
    secondOrderTaylorModelAt problem.smoothPart (method t) z +
        withTopRealPart problem.nonsmoothPart z ≤
      (1 - τ) *
          (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) +
        τ *
          (problem.smoothPart (method t) +
            inner ℝ (∇ problem.smoothPart (method t)) (x - method t) +
            withTopRealPart problem.nonsmoothPart x) +
        (L / 2) * τ ^ (2 : ℕ) * D * D := by
  set τ := method.stepSize t
  set z : E := (1 - τ) • method t + τ • x
  let d : E := x - method t
  have hτ_nonneg : 0 ≤ τ := by
    simpa [τ] using (method.stepSize_mem_Ioc t).1.le
  have hτ_le_one : τ ≤ 1 := by
    simpa [τ] using (method.stepSize_mem_Ioc t).2
  have h_one_sub_nonneg : 0 ≤ 1 - τ := sub_nonneg.mpr hτ_le_one
  have hsum_tau : 1 - τ + τ = 1 := by ring
  have hD_nonneg : 0 ≤ D := by
    have hzero := hdiam (method.iterates_mem_feasibleSet t) (method.iterates_mem_feasibleSet t)
    simpa using hzero
  have hL_nonneg : 0 ≤ L := by
    exact le_trans (norm_nonneg _) (h_hessian_bound t)
  have hz_sub : z - method t = τ • d := by
    -- Normalize the contracted point to a scalar multiple of the feasible direction.
    simp [z, d, sub_eq_add_neg, smul_add, add_smul, smul_sub, add_assoc, add_left_comm, add_comm]
  have hz_linear :
      inner ℝ (∇ problem.smoothPart (method t)) (z - method t) =
        τ * inner ℝ (∇ problem.smoothPart (method t)) d := by
    -- The linear Taylor term scales exactly with the contraction factor.
    rw [hz_sub]
    rw [inner_smul_right]
  have hpsi :
      withTopRealPart problem.nonsmoothPart z ≤
        (1 - τ) * withTopRealPart problem.nonsmoothPart (method t) +
          τ * withTopRealPart problem.nonsmoothPart x := by
    -- Convexity controls the finite real part of the nonsmooth term at the contracted point.
    simpa [z] using
      problem.nonsmoothPart_closedConvex.convexOn_withTopRealPart.2
        (method.iterates_mem_feasibleSet t) hx h_one_sub_nonneg hτ_nonneg hsum_tau
  have hd_norm_le : ‖d‖ ≤ D := by
    simpa [d] using hdiam hx (method.iterates_mem_feasibleSet t)
  have hquad_core :
      inner ℝ (hessian problem.smoothPart (method t) d) d ≤ L * D * D := by
    have hnorm_le :
        ‖hessian problem.smoothPart (method t) d‖ ≤ L * ‖d‖ := by
      calc
        ‖hessian problem.smoothPart (method t) d‖ ≤
            ‖hessian problem.smoothPart (method t)‖ * ‖d‖ :=
          (hessian problem.smoothPart (method t)).le_opNorm d
        _ ≤ L * ‖d‖ := by
          exact mul_le_mul_of_nonneg_right (h_hessian_bound t) (norm_nonneg d)
    have hnorm_inner :
        ‖inner ℝ (hessian problem.smoothPart (method t) d) d‖ ≤
          ‖hessian problem.smoothPart (method t) d‖ * ‖d‖ := by
      exact norm_inner_le_norm (hessian problem.smoothPart (method t) d) d
    have habs :
        |inner ℝ (hessian problem.smoothPart (method t) d) d| ≤ L * ‖d‖ * ‖d‖ := by
      calc
        |inner ℝ (hessian problem.smoothPart (method t) d) d| ≤
            ‖hessian problem.smoothPart (method t) d‖ * ‖d‖ :=
          by simpa [Real.norm_eq_abs] using hnorm_inner
        _ ≤ (L * ‖d‖) * ‖d‖ := by
          exact mul_le_mul_of_nonneg_right hnorm_le (norm_nonneg d)
        _ = L * ‖d‖ * ‖d‖ := by ring
    have hinner_le :
        inner ℝ (hessian problem.smoothPart (method t) d) d ≤ L * ‖d‖ * ‖d‖ := by
      exact le_trans (le_abs_self _) habs
    have hsq_le : ‖d‖ * ‖d‖ ≤ D * D := by
      nlinarith [hd_norm_le, hD_nonneg, norm_nonneg d]
    nlinarith [hinner_le, hsq_le, hL_nonneg]
  have hquad :
      (1 / 2 : ℝ) *
          inner ℝ (hessian problem.smoothPart (method t) (z - method t)) (z - method t) ≤
        (L / 2) * τ ^ (2 : ℕ) * D * D := by
    have hscale :
        inner ℝ (hessian problem.smoothPart (method t) (z - method t)) (z - method t) =
          τ ^ (2 : ℕ) * inner ℝ (hessian problem.smoothPart (method t) d) d := by
      rw [hz_sub]
      rw [map_smul, inner_smul_left, inner_smul_right]
      simpa [pow_two, mul_assoc]
    rw [hscale]
    nlinarith [hquad_core, hτ_nonneg]
  -- Combine the exact Taylor expansion, convexity of `Ψ`, and the operator-norm quadratic bound.
  calc
    secondOrderTaylorModelAt problem.smoothPart (method t) z +
        withTopRealPart problem.nonsmoothPart z =
      problem.smoothPart (method t) +
        inner ℝ (∇ problem.smoothPart (method t)) (z - method t) +
        (1 / 2 : ℝ) *
          inner ℝ (hessian problem.smoothPart (method t) (z - method t)) (z - method t) +
        withTopRealPart problem.nonsmoothPart z := by
          rw [secondOrderTaylorModelAt_apply]
    _ ≤
      problem.smoothPart (method t) +
        τ * inner ℝ (∇ problem.smoothPart (method t)) d +
        (L / 2) * τ ^ (2 : ℕ) * D * D +
        ((1 - τ) * withTopRealPart problem.nonsmoothPart (method t) +
          τ * withTopRealPart problem.nonsmoothPart x) := by
          rw [hz_linear]
          linarith
    _ =
      (1 - τ) *
          (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) +
        τ *
          (problem.smoothPart (method t) +
            inner ℝ (∇ problem.smoothPart (method t)) (x - method t) +
            withTopRealPart problem.nonsmoothPart x) +
        (L / 2) * τ ^ (2 : ℕ) * D * D := by
          dsimp [d]
          ring

/-- Helper for Theorem 6.16: the minimizer of the contracted quadratic composite subproblem can
be read on the finite real Taylor-model surface once both points are known to lie in `dom Ψ`. -/
private lemma contractedCompositeModel_realMinBridge
    (method : CompositeTrustRegionContractionMethod problem x0) (t : ℕ) {z : E}
    (hz : z ∈ contractedFeasibleSet problem.feasibleSet (method t) (method.stepSize t)) :
    secondOrderTaylorModelAt problem.smoothPart (method t) (method (t + 1)) +
        withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
      secondOrderTaylorModelAt problem.smoothPart (method t) z +
        withTopRealPart problem.nonsmoothPart z := by
  have hnext_dom :
      method (t + 1) ∈ dom problem.nonsmoothPart :=
    problem.nonsmoothPart_closedConvex.subset_withTopEffectiveDomain
      (method.iterates_mem_feasibleSet (t + 1))
  have hz_mem : z ∈ problem.feasibleSet := by
    rcases mem_contractedFeasibleSet_iff.mp hz with ⟨y, hy, rfl⟩
    have hτ := method.stepSize_mem_Ioc t
    -- The contracted feasible set is built from feasible convex combinations.
    simpa [AffineMap.lineMap_apply_module] using
      problem.feasibleSet_convex.lineMap_mem
        (method.iterates_mem_feasibleSet t) hy ⟨hτ.1.le, hτ.2⟩
  have hz_dom :
      z ∈ dom problem.nonsmoothPart :=
    problem.nonsmoothPart_closedConvex.subset_withTopEffectiveDomain hz_mem
  have hmin_withTop :=
    (isMinOn_iff.mp (method.iterates_succ_mem_and_isMinOn t).2) z hz
  rw [contractedCompositeSecondOrderModel_apply, contractedCompositeSecondOrderModel_apply] at hmin_withTop
  rw [← coe_withTopRealPart hnext_dom, ← coe_withTopRealPart hz_dom] at hmin_withTop
  have hmin_real_coe :
      (((inner ℝ (∇ problem.smoothPart (method t)) (method (t + 1) - method t) +
              (1 / 2 : ℝ) *
                inner ℝ
                  (hessian problem.smoothPart (method t) (method (t + 1) - method t))
                  (method (t + 1) - method t) +
              withTopRealPart problem.nonsmoothPart (method (t + 1)) : ℝ) : WithTop ℝ)) ≤
        (((inner ℝ (∇ problem.smoothPart (method t)) (z - method t) +
              (1 / 2 : ℝ) *
                inner ℝ (hessian problem.smoothPart (method t) (z - method t)) (z - method t) +
              withTopRealPart problem.nonsmoothPart z : ℝ) : WithTop ℝ)) := by
    -- Read the minimizing-property inequality on the finite `ℝ` surface of the nonsmooth term.
    simpa [add_assoc, add_left_comm, add_comm] using hmin_withTop
  have hmin_real :
      inner ℝ (∇ problem.smoothPart (method t)) (method (t + 1) - method t) +
          (1 / 2 : ℝ) *
            inner ℝ
              (hessian problem.smoothPart (method t) (method (t + 1) - method t))
              (method (t + 1) - method t) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
        inner ℝ (∇ problem.smoothPart (method t)) (z - method t) +
          (1 / 2 : ℝ) *
            inner ℝ (hessian problem.smoothPart (method t) (z - method t)) (z - method t) +
          withTopRealPart problem.nonsmoothPart z := by
    exact_mod_cast hmin_real_coe
  -- Add back the frozen value `f(x_t)` to recover the full Taylor-model comparison.
  have hshifted := add_le_add_left hmin_real (problem.smoothPart (method t))
  simpa [secondOrderTaylorModelAt_apply, add_assoc, add_left_comm, add_comm] using hshifted

/-- Helper for Theorem 6.16: after using the minimizing property of the contracted quadratic
subproblem and the upper-model remainder at the actual successor, one obtains the weighted
successor inequality needed for the estimating-sequence induction. -/
private lemma weightedSecondOrderObjective_stepBound
    (method : CompositeTrustRegionContractionMethod problem x0)
    (a : ℕ → ℝ) {L Hν D : ℝ} (ν : Set.Icc (0 : ℝ) 1)
    (hHν_nonneg : 0 ≤ Hν)
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (h_hessian_bound : ∀ t : ℕ, ‖hessian problem.smoothPart (method t)‖ ≤ L)
    (h_upper_model :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet →
        problem.smoothPart y ≤
          secondOrderTaylorModelAt problem.smoothPart x y +
            Hν * Real.rpow ‖y - x‖ (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ))))
    (t : ℕ) {x : E} (hx : x ∈ problem.feasibleSet) :
    accumulatedWeights a (t + 1) *
        (problem.smoothPart (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1))) ≤
      accumulatedWeights a t *
          (problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) +
        a (t + 1) *
          (problem.smoothPart (method t) +
            inner ℝ (∇ problem.smoothPart (method t)) (x - method t) +
            withTopRealPart problem.nonsmoothPart x) +
        secondOrderErrorIncrement a L Hν D ν t := by
  let τ := method.stepSize t
  let u :=
    problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)
  let w :=
    problem.smoothPart (method t) +
      inner ℝ (∇ problem.smoothPart (method t)) (x - method t) +
      withTopRealPart problem.nonsmoothPart x
  let z : E := (1 - τ) • method t + τ • x
  let holderCoeff : ℝ :=
    Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))
  have hA_pos : 0 < accumulatedWeights a (t + 1) :=
    accumulatedWeights_pos a ha_pos (t + 1)
  have hA_nonneg : 0 ≤ accumulatedWeights a (t + 1) := hA_pos.le
  have hτ_pos : 0 < τ := by
    simpa [τ] using (method.stepSize_mem_Ioc t).1
  have hτ_nonneg : 0 ≤ τ := hτ_pos.le
  have hτ_le_one : τ ≤ 1 := by
    simpa [τ] using (method.stepSize_mem_Ioc t).2
  have hD_nonneg : 0 ≤ D := by
    have hzero := hdiam (method.iterates_mem_feasibleSet t) (method.iterates_mem_feasibleSet t)
    simpa using hzero
  have hnorm_le :
      ‖method (t + 1) - method t‖ ≤ τ * D := by
    simpa [τ] using secondOrderSuccessorNormLeStepSizeMulDiameter method hdiam t
  have hpow_le :
      Real.rpow ‖method (t + 1) - method t‖ (2 + (ν : ℝ)) ≤
        Real.rpow (τ * D) (2 + (ν : ℝ)) := by
    exact Real.rpow_le_rpow (norm_nonneg _) hnorm_le (by linarith [ν.2.1])
  have hpow_mul :
      Real.rpow (τ * D) (2 + (ν : ℝ)) =
        Real.rpow D (2 + (ν : ℝ)) * Real.rpow τ (2 + (ν : ℝ)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.mul_rpow hD_nonneg hτ_nonneg : Real.rpow (D * τ) (2 + (ν : ℝ)) =
        Real.rpow D (2 + (ν : ℝ)) * Real.rpow τ (2 + (ν : ℝ)))
  have hholder_remainder :
      Hν * Real.rpow ‖method (t + 1) - method t‖ (2 + (ν : ℝ)) /
          ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) ≤
        holderCoeff * Real.rpow τ (2 + (ν : ℝ)) := by
    -- Bound the Hölder remainder at the actual successor by the diameter-scaled power of `τ_t`.
    calc
      Hν * Real.rpow ‖method (t + 1) - method t‖ (2 + (ν : ℝ)) /
          ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) ≤
        Hν * Real.rpow (τ * D) (2 + (ν : ℝ)) /
          ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
            have hdenom_pos : 0 < ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
              nlinarith [ν.2.1]
            have hcoeff_nonneg :
                0 ≤ Hν / ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
              exact div_nonneg hHν_nonneg hdenom_pos.le
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hpow_le hcoeff_nonneg
      _ = Hν * (Real.rpow D (2 + (ν : ℝ)) * Real.rpow τ (2 + (ν : ℝ))) /
            ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
            rw [hpow_mul]
      _ = holderCoeff * Real.rpow τ (2 + (ν : ℝ)) := by
            dsimp [holderCoeff]
            ring
  have hz_contracted :
      z ∈ contractedFeasibleSet problem.feasibleSet (method t) τ := by
    -- The comparison point is exactly the contracted feasible interpolation toward `x`.
    exact mem_contractedFeasibleSet_iff.mpr ⟨x, hx, by simp [z]⟩
  have hmin_real :
      secondOrderTaylorModelAt problem.smoothPart (method t) (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
        secondOrderTaylorModelAt problem.smoothPart (method t) z +
          withTopRealPart problem.nonsmoothPart z := by
    simpa [τ] using contractedCompositeModel_realMinBridge method t hz_contracted
  have hcontracted :
      secondOrderTaylorModelAt problem.smoothPart (method t) z +
          withTopRealPart problem.nonsmoothPart z ≤
        (1 - τ) * u + τ * w + (L / 2) * τ ^ (2 : ℕ) * D * D := by
    -- Rewrite the contracted comparison point on the affine-plus-quadratic surface.
    simpa [τ, z, u, w] using
      contractedSecondOrderModel_le_affineModel_addQuadraticError
        method hdiam h_hessian_bound t hx
  have hsucc_upper :
      problem.smoothPart (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
        secondOrderTaylorModelAt problem.smoothPart (method t) (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) +
          holderCoeff * Real.rpow τ (2 + (ν : ℝ)) := by
    -- Apply the given upper-model bound at the successor and then replace the displacement by
    -- the diameter-scaled `τ_t` bound.
    have hsmooth :=
      h_upper_model (method.iterates_mem_feasibleSet t) (method.iterates_mem_feasibleSet (t + 1))
    have hsmooth_shift :
        problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
          secondOrderTaylorModelAt problem.smoothPart (method t) (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1)) +
            Hν * Real.rpow ‖method (t + 1) - method t‖ (2 + (ν : ℝ)) /
              ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
      linarith
    have hholder_shift :
        secondOrderTaylorModelAt problem.smoothPart (method t) (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1)) +
            Hν * Real.rpow ‖method (t + 1) - method t‖ (2 + (ν : ℝ)) /
              ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) ≤
          secondOrderTaylorModelAt problem.smoothPart (method t) (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1)) +
            holderCoeff * Real.rpow τ (2 + (ν : ℝ)) := by
      linarith [hholder_remainder]
    exact hsmooth_shift.trans hholder_shift
  have hnormalized :
      problem.smoothPart (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
        (1 - τ) * u + τ * w +
          holderCoeff * Real.rpow τ (2 + (ν : ℝ)) +
          (L / 2) * τ ^ (2 : ℕ) * D * D := by
    -- Separate the minimizing-property bridge from the remainder bounds before rescaling.
    exact le_trans hsucc_upper (by linarith [hmin_real, hcontracted])
  have hscaled := mul_le_mul_of_nonneg_left hnormalized hA_nonneg
  have hτ_step : τ = τ[a](t) := by
    simpa [τ] using h_step t
  have hsplit :
      accumulatedWeights a (t + 1) *
          ((1 - τ[a](t)) * u + τ[a](t) * w +
            holderCoeff * Real.rpow (τ[a](t)) (2 + (ν : ℝ)) +
            (L / 2) * (τ[a](t)) ^ (2 : ℕ) * D * D) =
        accumulatedWeights a (t + 1) * ((1 - τ[a](t)) * u + τ[a](t) * w) +
          accumulatedWeights a (t + 1) *
            (holderCoeff * Real.rpow (τ[a](t)) (2 + (ν : ℝ))) +
          accumulatedWeights a (t + 1) *
            ((τ[a](t)) ^ (2 : ℕ) * ((L / 2) * D * D)) := by
    -- Split the single normalized successor bound into the affine, Hölder, and quadratic pieces
    -- consumed by the scalar rescaling lemmas.
    dsimp [holderCoeff]
    ring
  have hscaled_split :
      accumulatedWeights a (t + 1) *
          (problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1))) ≤
        accumulatedWeights a (t + 1) * ((1 - τ[a](t)) * u + τ[a](t) * w) +
          accumulatedWeights a (t + 1) *
            (holderCoeff * Real.rpow (τ[a](t)) (2 + (ν : ℝ))) +
          accumulatedWeights a (t + 1) *
            ((τ[a](t)) ^ (2 : ℕ) * ((L / 2) * D * D)) := by
    calc
      accumulatedWeights a (t + 1) *
          (problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1))) ≤
        accumulatedWeights a (t + 1) *
          ((1 - τ[a](t)) * u + τ[a](t) * w +
            holderCoeff * Real.rpow (τ[a](t)) (2 + (ν : ℝ)) +
            (L / 2) * (τ[a](t)) ^ (2 : ℕ) * D * D) := by
          simpa [hτ_step] using hscaled
      _ =
        accumulatedWeights a (t + 1) * ((1 - τ[a](t)) * u + τ[a](t) * w) +
          accumulatedWeights a (t + 1) *
            (holderCoeff * Real.rpow (τ[a](t)) (2 + (ν : ℝ))) +
          accumulatedWeights a (t + 1) *
            ((τ[a](t)) ^ (2 : ℕ) * ((L / 2) * D * D)) := hsplit
  have hholder_step :
      accumulatedWeights a (t + 1) *
          (holderCoeff * Real.rpow (τ[a](t)) (2 + (ν : ℝ))) ≤
        (a (t + 1) * a (t + 1) / accumulatedWeights a (t + 1)) * holderCoeff := by
    simpa [holderCoeff] using
      weightCoefficient_holder_rescaling a ha_pos Hν D ν hHν_nonneg hD_nonneg t
  have hafter_holder :
      accumulatedWeights a (t + 1) *
          (problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1))) ≤
        accumulatedWeights a (t + 1) * ((1 - τ[a](t)) * u + τ[a](t) * w) +
          (a (t + 1) * a (t + 1) / accumulatedWeights a (t + 1)) * holderCoeff +
          accumulatedWeights a (t + 1) *
            ((τ[a](t)) ^ (2 : ℕ) * ((L / 2) * D * D)) := by
    exact le_trans hscaled_split (by linarith [hholder_step])
  calc
    accumulatedWeights a (t + 1) *
        (problem.smoothPart (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1))) ≤
      accumulatedWeights a (t + 1) * ((1 - τ[a](t)) * u + τ[a](t) * w) +
        (a (t + 1) * a (t + 1) / accumulatedWeights a (t + 1)) * holderCoeff +
        accumulatedWeights a (t + 1) *
          ((τ[a](t)) ^ (2 : ℕ) * ((L / 2) * D * D)) := hafter_holder
    _ =
      accumulatedWeights a t *
          (problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) +
        a (t + 1) *
          (problem.smoothPart (method t) +
            inner ℝ (∇ problem.smoothPart (method t)) (x - method t) +
            withTopRealPart problem.nonsmoothPart x) +
        (a (t + 1) * a (t + 1) / accumulatedWeights a (t + 1)) * holderCoeff +
        accumulatedWeights a (t + 1) *
          ((τ[a](t)) ^ (2 : ℕ) * ((L / 2) * D * D)) := by
            rw [successor_weighted_average_rescaling a ha_pos t u w]
    _ =
      accumulatedWeights a t *
          (problem.smoothPart (method t) +
            withTopRealPart problem.nonsmoothPart (method t)) +
        a (t + 1) *
          (problem.smoothPart (method t) +
            inner ℝ (∇ problem.smoothPart (method t)) (x - method t) +
            withTopRealPart problem.nonsmoothPart x) +
        secondOrderErrorIncrement a L Hν D ν t := by
            rw [weightCoefficient_square_rescaling a ha_pos L D t]
            simp [secondOrderErrorIncrement, secondOrderErrorIncrement_apply, holderCoeff,
              add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Theorem 6.16: the one-dimensional feasible slice
`s ↦ f((1 - s) x_t + s y)` has monotone within-derivative on `[0, 1]`. -/
private lemma feasibleSegmentSlice_derivWithin_monotone
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    MonotoneOn
      (derivWithin
        (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
        (Set.Icc (0 : ℝ) 1))
      (Set.Icc (0 : ℝ) 1) := by
  let x := method t
  let seg : ℝ → E := AffineMap.lineMap x y
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (seg s)
  have hseg : Set.MapsTo seg I problem.feasibleSet := by
    intro s hs
    exact problem.feasibleSet_convex.lineMap_mem (method.iterates_mem_feasibleSet t) hy hs
  have hseg_c1 :
      ConvexC1On (seg ⁻¹' problem.feasibleSet) ψ := by
    -- Precompose the Chapter 3 `C¹` convex owner with the affine segment map once.
    simpa [x, seg, ψ] using
      problem.smoothPart_convexC1.comp_continuousAffineMap
        ⟨AffineMap.lineMap x y, AffineMap.lineMap_continuous⟩
  have hψ_conv :
      ConvexOn ℝ I ψ := by
    -- Restrict the preimage-domain convex slice back to the concrete interval `[0, 1]`.
    refine (convexC1On_convexOn hseg_c1).subset ?_ (convex_Icc (0 : ℝ) 1)
    intro s hs
    exact hseg hs
  have hψ_contDiff :
      ContDiffOn ℝ 1 ψ I :=
    (convexC1On_contDiffOn hseg_c1).mono (by
      intro s hs
      exact hseg hs)
  have hψ_diff :
      DifferentiableOn ℝ ψ I :=
    hψ_contDiff.differentiableOn (by simp)
  -- Convexity on `[0, 1]` now upgrades directly to monotonicity of the within-derivative.
  simpa [I, ψ] using hψ_conv.monotoneOn_derivWithin hψ_diff

/-- Helper for Theorem 6.16: convexity of the feasible scalar slice forces the left-endpoint
second within-derivative on `[0, 1]` to be nonnegative. -/
private lemma feasibleSegmentSlice_secondDerivWithin_zero_nonneg
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    0 ≤
      derivWithin
        (derivWithin
          (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
          (Set.Icc (0 : ℝ) 1))
        (Set.Icc (0 : ℝ) 1) 0 := by
  have hmono :=
    feasibleSegmentSlice_derivWithin_monotone method t hy
  -- Apply the one-dimensional monotonicity-to-nonnegativity bridge at the left endpoint.
  simpa using
    (hmono.derivWithin_nonneg :
      0 ≤
        derivWithin
          (derivWithin
            (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
            (Set.Icc (0 : ℝ) 1))
          (Set.Icc (0 : ℝ) 1) 0)

/-- Helper for Theorem 6.16: the feasible directional-derivative field along the segment from
`x_t` to a feasible comparison point is monotone on `[0, 1]`. -/
private lemma feasibleSegmentSlice_derivWithin_Icc_eq_fderivWithin
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Icc (0 : ℝ) 1)
        s =
      fderivWithin ℝ problem.smoothPart problem.feasibleSet
        (AffineMap.lineMap (method t) y s)
        (y - method t) := by
  let x := method t
  let d : E := y - x
  let seg : ℝ → E := AffineMap.lineMap x y
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let ψ : ℝ → ℝ := fun r ↦ problem.smoothPart (seg r)
  have hseg : Set.MapsTo seg I problem.feasibleSet := by
    intro r hr
    exact problem.feasibleSet_convex.lineMap_mem (method.iterates_mem_feasibleSet t) hy hr
  have hdiff : DifferentiableOn ℝ problem.smoothPart problem.feasibleSet :=
    method.objective_contDiffOn.differentiableOn (by norm_num)
  have hderiv :
      HasDerivWithinAt ψ
        (fderivWithin ℝ problem.smoothPart problem.feasibleSet (seg s) d)
        I
        s := by
    -- Differentiate the scalar feasible slice through the affine segment parameterization.
    simpa [ψ, seg, d] using
      (hdiff _ (hseg hs)).hasFDerivWithinAt.comp_hasDerivWithinAt s
        AffineMap.hasDerivWithinAt_lineMap hseg
  -- Read the derivative value on `[0, 1]` from the chain-rule computation above.
  exact hderiv.derivWithin (uniqueDiffOn_Icc zero_lt_one s hs)

/-- Helper for Theorem 6.16: on a short right neighborhood of `0`, the one-sided slice derivative
on `Set.Ici 0` agrees with the `[0, 1]` derivative owner. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eq_Icc_on_shortNeighborhood
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          s) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))]
      (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Icc (0 : ℝ) 1)
          s) := by
  -- On any point `s < 1`, the owners `Ici 0` and `Icc 0 1` coincide on a full neighborhood of
  -- `s`, so the scalar within-derivative is unchanged by switching between them.
  filter_upwards [inter_mem_nhdsWithin (Set.Ici (0 : ℝ)) (Iio_mem_nhds zero_lt_one)] with s hs
  rcases hs with ⟨hs0, hs_lt⟩
  have hsets : Set.Ici (0 : ℝ) =ᶠ[nhds s] Set.Icc (0 : ℝ) 1 := by
    filter_upwards [Iio_mem_nhds hs_lt] with r hr
    apply propext
    constructor
    · intro hr0
      have hr' : r < 1 := hr
      exact ⟨hr0, hr'.le⟩
    · intro hrIcc
      exact hrIcc.1
  -- Route correction: use the local set congruence directly instead of trying to globalize
  -- `UniqueDiffOn` on the feasible set.
  exact derivWithin_congr_set hsets

/-- Helper for Theorem 6.16: on a short right neighborhood of `0`, the one-sided slice derivative
matches the feasible Fréchet derivative evaluated on the segment direction. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eventuallyEq_fderivWithin
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          s) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))]
      (fun s : ℝ ↦
        fderivWithin ℝ problem.smoothPart problem.feasibleSet
          (AffineMap.lineMap (method t) y s)
          (y - method t)) := by
  -- First transport the one-sided derivative to the fixed owner `[0, 1]`, then read it through
  -- the already-proved chain-rule formula on the feasible segment.
  filter_upwards [feasibleSegmentSlice_derivWithin_Ici_eq_Icc_on_shortNeighborhood
      method t hy, inter_mem_nhdsWithin (Set.Ici (0 : ℝ)) (Iio_mem_nhds zero_lt_one)] with
      s hs_eq hs
  rcases hs with ⟨hs0, hs_lt⟩
  have hs : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs0, hs_lt.le⟩
  calc
    derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Ici (0 : ℝ))
        s =
      derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Icc (0 : ℝ) 1)
        s := hs_eq
    _ =
      fderivWithin ℝ problem.smoothPart problem.feasibleSet
        (AffineMap.lineMap (method t) y s)
        (y - method t) :=
      feasibleSegmentSlice_derivWithin_Icc_eq_fderivWithin method t hy hs

/-- Helper for Theorem 6.16: the feasible directional-derivative field along the segment from
`x_t` to a feasible comparison point is monotone on `[0, 1]`. -/
private lemma feasibleSegmentDirectionalDerivative_monotone
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    MonotoneOn
      (fun s : ℝ ↦
        fderivWithin ℝ problem.smoothPart problem.feasibleSet
          (AffineMap.lineMap (method t) y s) (y - method t))
      (Set.Icc (0 : ℝ) 1) := by
  let x := method t
  let d : E := y - x
  let seg : ℝ → E := AffineMap.lineMap x y
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (seg s)
  have hseg : Set.MapsTo seg I problem.feasibleSet := by
    intro s hs
    exact problem.feasibleSet_convex.lineMap_mem (method.iterates_mem_feasibleSet t) hy hs
  have hdiff : DifferentiableOn ℝ problem.smoothPart problem.feasibleSet :=
    method.objective_contDiffOn.differentiableOn (by norm_num)
  have hmono :=
    feasibleSegmentSlice_derivWithin_monotone method t hy
  intro s₁ hs₁ s₂ hs₂ hs₁₂
  -- Reuse the already-stable scalar slice monotonicity after rewriting each endpoint value.
  calc
    (fun s : ℝ ↦
        fderivWithin ℝ problem.smoothPart problem.feasibleSet (AffineMap.lineMap x y s) d) s₁
        = derivWithin ψ I s₁ := by
            symm
            exact feasibleSegmentSlice_derivWithin_Icc_eq_fderivWithin method t hy hs₁
    _ ≤ derivWithin ψ I s₂ := hmono hs₁ hs₂ hs₁₂
    _ =
        (fun s : ℝ ↦
          fderivWithin ℝ problem.smoothPart problem.feasibleSet (AffineMap.lineMap x y s) d) s₂ := by
            exact feasibleSegmentSlice_derivWithin_Icc_eq_fderivWithin method t hy hs₂

/-- Helper for Theorem 6.16: at an interior segment point, the scalar slice derivative and the
intrinsic feasible line derivative are the same directional derivative viewed in two owner APIs.
-/
private lemma feasibleSegmentSlice_derivWithin_Icc_eq_lineDerivWithin_of_mem_Ioo
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Icc (0 : ℝ) 1)
        s =
      lineDerivWithin ℝ problem.smoothPart problem.feasibleSet
        (AffineMap.lineMap (method t) y s)
        (y - method t) := by
  let x := method t
  let d : E := y - x
  let seg : ℝ → E := AffineMap.lineMap x y
  let ψ : ℝ → ℝ := fun r ↦ problem.smoothPart (seg r)
  let T : Set ℝ := (fun u : ℝ ↦ seg s + u • d) ⁻¹' problem.feasibleSet
  have hseg : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) problem.feasibleSet := by
    intro r hr
    exact problem.feasibleSet_convex.lineMap_mem (method.iterates_mem_feasibleSet t) hy hr
  have hdiff :
      DifferentiableWithinAt ℝ problem.smoothPart problem.feasibleSet (seg s) := by
    have hs_mem : seg s ∈ problem.feasibleSet := hseg ⟨hs.1.le, hs.2.le⟩
    exact (method.objective_contDiffOn.differentiableOn (by norm_num)) _ hs_mem
  have hsliceWithin :
      HasDerivWithinAt ψ
        (fderivWithin ℝ problem.smoothPart problem.feasibleSet (seg s) d)
        (Set.Icc (0 : ℝ) 1)
        s := by
    -- Read the scalar slice derivative from the ambient within-derivative at the interior point.
    simpa [ψ, seg, d] using
      hdiff.hasFDerivWithinAt.comp_hasDerivWithinAt s
        AffineMap.hasDerivWithinAt_lineMap hseg
  have hslice :
      HasDerivAt ψ
        (fderivWithin ℝ problem.smoothPart problem.feasibleSet (seg s) d)
        s := by
    -- Interior points of `[0, 1]` allow us to forget the interval owner.
    exact hsliceWithin.hasDerivAt (Icc_mem_nhds hs.1 hs.2)
  have hshift :
      ∀ u : ℝ, seg s + u • d = seg (s + u) := by
    intro u
    -- Normalize the translated base point back to the same affine segment parameterization.
    calc
      seg s + u • d = (AffineMap.lineMap x y) s + u • d := by
        rfl
      _ = s • d + x + u • d := by
        simp [seg, d, AffineMap.lineMap_apply_module']
      _ = (s + u) • d + x := by
        simp [add_smul, add_assoc, add_comm]
      _ = (AffineMap.lineMap x y) (s + u) := by
        simp [d, AffineMap.lineMap_apply_module']
      _ = seg (s + u) := by
        rfl
  have hT_subset : Set.Icc (-s) (1 - s) ⊆ T := by
    intro u hu
    have hsu : s + u ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · linarith [hu.1]
      · linarith [hu.2]
    -- Every short translated step stays on the feasible segment between `x_t` and `y`.
    simpa [T, hshift u] using hseg hsu
  have hT_mem : T ∈ nhds (0 : ℝ) := by
    have hIcc_mem : Set.Icc (-s) (1 - s) ∈ nhds (0 : ℝ) := by
      exact Icc_mem_nhds (by linarith [hs.1]) (by linarith [hs.2])
    exact Filter.mem_of_superset hIcc_mem hT_subset
  have hlineWithin :
      HasDerivWithinAt
        (fun u : ℝ ↦ problem.smoothPart (seg s + u • d))
        (fderivWithin ℝ problem.smoothPart problem.feasibleSet (seg s) d)
        T
        0 := by
    -- The intrinsic feasible line derivative is computed by the same within-derivative value.
    simpa [HasLineDerivWithinAt, T, seg, d] using
      hdiff.hasFDerivWithinAt.hasLineDerivWithinAt d
  have hline :
      HasDerivAt
        (fun u : ℝ ↦ problem.smoothPart (seg s + u • d))
        (fderivWithin ℝ problem.smoothPart problem.feasibleSet (seg s) d)
        0 := by
    -- On the short translated neighborhood, the feasible owner becomes an honest neighborhood.
    exact hlineWithin.hasDerivAt hT_mem
  -- Compare the two ordinary derivatives after translating the scalar slice by `s`.
  calc
    derivWithin ψ (Set.Icc (0 : ℝ) 1) s = deriv ψ s := by
      rw [derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
    _ = fderivWithin ℝ problem.smoothPart problem.feasibleSet (seg s) d := hslice.deriv
    _ = deriv (fun u : ℝ ↦ problem.smoothPart (seg s + u • d)) 0 := hline.deriv.symm
    _ =
      lineDerivWithin ℝ problem.smoothPart problem.feasibleSet (seg s) d := by
        simpa [lineDerivWithin, T] using
          (derivWithin_of_mem_nhds
            (f := fun u : ℝ ↦ problem.smoothPart (seg s + u • d))
            (s := T)
            (x := (0 : ℝ))
            hT_mem).symm

/-- Helper for Theorem 6.16: on a punctured short right neighborhood of `0`, the one-sided slice
derivative already agrees with the intrinsic feasible line-derivative owner. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eventuallyEq_lineDerivWithin_right
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          s) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      (fun s : ℝ ↦
        lineDerivWithin ℝ problem.smoothPart problem.feasibleSet
          (AffineMap.lineMap (method t) y s)
          (y - method t)) := by
  have hshort :
      (fun s : ℝ ↦
          derivWithin
            (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
            (Set.Ici (0 : ℝ))
            s) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
        (fun s : ℝ ↦
          derivWithin
            (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
            (Set.Icc (0 : ℝ) 1)
            s) := by
    exact
      (feasibleSegmentSlice_derivWithin_Ici_eq_Icc_on_shortNeighborhood method t hy).filter_mono
        (nhdsWithin_mono (0 : ℝ) (by
          intro s hs
          simpa using hs.le))
  filter_upwards
      [hshort,
        inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) (Iio_mem_nhds zero_lt_one)] with
      s hs_eq hs
  have hs : s ∈ Set.Ioo (0 : ℝ) 1 := hs
  -- Away from the endpoint itself, the fixed one-sided owner is already the intrinsic line owner.
  calc
    derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Ici (0 : ℝ))
        s =
      derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Icc (0 : ℝ) 1)
        s := hs_eq
    _ =
      lineDerivWithin ℝ problem.smoothPart problem.feasibleSet
        (AffineMap.lineMap (method t) y s)
        (y - method t) :=
      feasibleSegmentSlice_derivWithin_Icc_eq_lineDerivWithin_of_mem_Ioo method t hy hs

/-- Helper for Theorem 6.16: if the ambient gradient is not differentiable at a feasible point,
the totalized ambient Hessian there is the zero operator. -/
private lemma hessian_eq_zero_of_not_differentiableAt_gradient
    {x : E} (hgrad : ¬ DifferentiableAt ℝ (∇ problem.smoothPart) x) :
    hessian problem.smoothPart x = 0 := by
  -- The ambient Hessian is defined as the Fréchet derivative of the gradient, so the totalized
  -- `fderiv = 0` convention closes the nondifferentiable branch immediately.
  simpa [hessian] using fderiv_zero_of_not_differentiableAt hgrad

/-- Helper for Theorem 6.16: at the left endpoint `0`, the fixed interval owner
`Set.Icc (0 : ℝ) 1` and the one-sided owner `Set.Ici (0 : ℝ)` define the same second iterated
derivative for the feasible scalar slice. -/
private lemma feasibleSegmentSlice_secondIteratedDerivWithin_Icc_eq_Ici
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} :
    iteratedDerivWithin 2
        (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
        (Set.Icc (0 : ℝ) 1) 0 =
      iteratedDerivWithin 2
        (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
        (Set.Ici (0 : ℝ)) 0 := by
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (AffineMap.lineMap (method t) y s)
  have hsets : Set.Icc (0 : ℝ) 1 =ᶠ[nhds (0 : ℝ)] Set.Ici (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds zero_lt_one] with s hs_lt
    apply propext
    constructor
    · intro hs
      exact hs.1
    · intro hs
      have hs_lt' : s < 1 := hs_lt
      exact ⟨hs, hs_lt'.le⟩
  have hIcc :
      iteratedDerivWithin 2 ψ (Set.Icc (0 : ℝ) 1) 0 =
        derivWithin (derivWithin ψ (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [iteratedDerivWithin_succ]
  have hIci :
      iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 =
        derivWithin (derivWithin ψ (Set.Ici (0 : ℝ))) (Set.Ici (0 : ℝ)) 0 := by
    simpa [iteratedDerivWithin_succ]
  rw [hIcc, hIci]
  have houter_set :
      derivWithin (derivWithin ψ (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1) 0 =
        derivWithin (derivWithin ψ (Set.Icc (0 : ℝ) 1)) (Set.Ici (0 : ℝ)) 0 :=
    derivWithin_congr_set hsets
  have hfun :
      (fun s : ℝ ↦ derivWithin ψ (Set.Ici (0 : ℝ)) s) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))]
        (fun s : ℝ ↦ derivWithin ψ (Set.Icc (0 : ℝ) 1) s) := by
    filter_upwards [inter_mem_nhdsWithin (Set.Ici (0 : ℝ)) (Iio_mem_nhds zero_lt_one)] with
        s hs
    rcases hs with ⟨hs0, hs_lt⟩
    have hlocal : Set.Ici (0 : ℝ) =ᶠ[nhds s] Set.Icc (0 : ℝ) 1 := by
      filter_upwards [Iio_mem_nhds hs_lt] with r hr
      apply propext
      constructor
      · intro hr0
        have hr' : r < 1 := hr
        exact ⟨hr0, hr'.le⟩
      · intro hrIcc
        exact hrIcc.1
    exact derivWithin_congr_set hlocal
  have houter_fun :
      derivWithin (derivWithin ψ (Set.Ici (0 : ℝ))) (Set.Ici (0 : ℝ)) 0 =
        derivWithin (derivWithin ψ (Set.Icc (0 : ℝ) 1)) (Set.Ici (0 : ℝ)) 0 :=
    (by
      simpa [ψ] using
        (Filter.EventuallyEq.derivWithin_eq_of_mem
          (s := Set.Ici (0 : ℝ))
          (x := (0 : ℝ))
          (f₁ := fun s : ℝ ↦ derivWithin ψ (Set.Ici (0 : ℝ)) s)
          (f := fun s : ℝ ↦ derivWithin ψ (Set.Icc (0 : ℝ) 1) s)
          hfun
          (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ))))
  calc
    derivWithin (derivWithin ψ (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1) 0 =
    derivWithin (derivWithin ψ (Set.Icc (0 : ℝ) 1)) (Set.Ici (0 : ℝ)) 0 := houter_set
    _ = derivWithin (derivWithin ψ (Set.Ici (0 : ℝ))) (Set.Ici (0 : ℝ)) 0 := houter_fun.symm

/-- Helper for Theorem 6.16: the scalar slice of `problem.smoothPart` along the feasible segment
from `x_t` to `y` is `C²` on the fixed interval `[0, 1]`. -/
private lemma feasibleSegmentSlice_contDiffOn_Icc
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    ContDiffOn ℝ 2
      (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
      (Set.Icc (0 : ℝ) 1) := by
  let x := method t
  let seg : ℝ → E := AffineMap.lineMap x y
  have hseg : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) problem.feasibleSet := by
    intro s hs
    exact problem.feasibleSet_convex.lineMap_mem (method.iterates_mem_feasibleSet t) hy hs
  have hAffine : ContDiffOn ℝ 2 seg (Set.Icc (0 : ℝ) 1) := by
    -- The line-map parameterization is an affine `C²` map on the whole scalar interval.
    simpa [seg, ContinuousAffineMap.coe_lineMap_eq] using
      (ContinuousAffineMap.lineMap (R := ℝ) x y).contDiff.contDiffOn
  -- Compose the owner's `C²` regularity with the fixed feasible segment.
  simpa [seg] using method.objective_contDiffOn.comp hAffine hseg

/-- Helper for Theorem 6.16: the `[0, 1]`-owned derivative field of the feasible scalar slice is
continuous on the whole segment, including the endpoint `0`. -/
private lemma feasibleSegmentSlice_derivWithin_Icc_continuousOn
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    ContinuousOn
      (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Icc (0 : ℝ) 1)
          s)
      (Set.Icc (0 : ℝ) 1) := by
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (AffineMap.lineMap (method t) y s)
  have hψ :
      ContDiffOn ℝ 2 ψ (Set.Icc (0 : ℝ) 1) :=
    feasibleSegmentSlice_contDiffOn_Icc method t hy
  -- The one-dimensional `C²` slice has a continuous derivative field on `[0, 1]`.
  simpa [ψ] using
    hψ.continuousOn_derivWithin (uniqueDiffOn_Icc zero_lt_one) (by norm_num)

/-- Helper for Theorem 6.16: transporting the derivative owner from `[0, 1]` to `Set.Ici 0`
preserves continuity of the scalar slice derivative at the endpoint `0`. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_continuousWithinAtZero
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    ContinuousWithinAt
      (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          s)
      (Set.Ici (0 : ℝ))
      0 := by
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (AffineMap.lineMap (method t) y s)
  have hIcc :
      ContinuousWithinAt (fun s : ℝ ↦ derivWithin ψ (Set.Icc (0 : ℝ) 1) s) (Set.Icc (0 : ℝ) 1) 0 :=
    (feasibleSegmentSlice_derivWithin_Icc_continuousOn method t hy).continuousWithinAt
      (by simp)
  have hsets : Set.Icc (0 : ℝ) 1 =ᶠ[nhds (0 : ℝ)] Set.Ici (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds zero_lt_one] with s hs_lt
    apply propext
    constructor
    · intro hs
      exact hs.1
    · intro hs
      exact ⟨hs, hs_lt.le⟩
  have hIcc' :
      ContinuousWithinAt (fun s : ℝ ↦ derivWithin ψ (Set.Icc (0 : ℝ) 1) s) (Set.Ici (0 : ℝ)) 0 :=
    hIcc.congr_set hsets
  -- Switch the derivative owner near `0` using the already-stable short-neighborhood transport.
  exact
    ContinuousWithinAt.congr_of_eventuallyEq_of_mem hIcc'
      (by
        simpa [ψ] using
          feasibleSegmentSlice_derivWithin_Ici_eq_Icc_on_shortNeighborhood method t hy)
      (by simp)

/-- Helper for Theorem 6.16: differentiating the scalarized ambient gradient line on the forward
ray `Set.Ici 0` recovers the Hessian quadratic form at the base point. -/
private lemma scalarizedGradientLineHasDerivWithinAtZero
    {x d : E}
    (hgrad : DifferentiableAt ℝ (∇ problem.smoothPart) x) :
    HasDerivWithinAt
      (fun s : ℝ ↦ inner ℝ (∇ problem.smoothPart (x + s • d)) d)
      (inner ℝ (hessian problem.smoothPart x d) d)
      (Set.Ici (0 : ℝ))
      0 := by
  let φ : E →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) d
  have hline : HasDerivAt (fun s : ℝ ↦ x + s • d) d 0 := by
    -- Differentiate the affine ray `s ↦ x + s • d` once and freeze that shape for the chain rule.
    simpa [one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have hgradAt :
      HasFDerivAt (∇ problem.smoothPart)
        (hessian problem.smoothPart (x + (0 : ℝ) • d))
        (x + (0 : ℝ) • d) := by
    simpa [hessian, zero_smul] using hgrad.hasFDerivAt
  have hgradLine :
      HasFDerivAt
        (fun s : ℝ ↦ ∇ problem.smoothPart (x + s • d))
        ((hessian problem.smoothPart x).comp (ContinuousLinearMap.toSpanSingleton ℝ d))
        0 := by
    -- Compose the ambient derivative of the gradient with the affine-ray derivative.
    simpa [zero_smul] using (hgradAt.comp 0 hline.hasFDerivAt)
  have hscalar :
      HasFDerivAt
        (fun s : ℝ ↦ φ (∇ problem.smoothPart (x + s • d)))
        (φ.comp ((hessian problem.smoothPart x).comp
          (ContinuousLinearMap.toSpanSingleton ℝ d)))
        0 := by
    -- Postcompose the gradient line with the fixed inner-product functional `z ↦ ⟪z, d⟫`.
    simpa [φ] using (φ.hasFDerivAt.comp 0 hgradLine)
  have hderivAt :
      HasDerivAt
        (fun s : ℝ ↦ inner ℝ (∇ problem.smoothPart (x + s • d)) d)
        (inner ℝ (hessian problem.smoothPart x d) d)
        0 := by
    simpa [φ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hscalar.hasDerivAt
  exact hderivAt.hasDerivWithinAt

/-- Helper for Theorem 6.16: differentiability of the totalized ambient gradient at `x` makes the
totalized Fréchet derivative field differentiable at `x`. -/
private lemma fderivDifferentiableAt_of_gradientDifferentiableAt
    {x : E}
    (hgrad : DifferentiableAt ℝ (∇ problem.smoothPart) x) :
    DifferentiableAt ℝ (fderiv ℝ problem.smoothPart) x := by
  -- Route correction: rewrite the totalized Fréchet derivative field through the forward Riesz
  -- map instead of trying to recover ambient differentiability of `smoothPart` near `x`.
  simpa [gradient] using
    (((InnerProductSpace.toDual ℝ E).symm).comp_differentiableAt_iff).1 hgrad

/-- Helper for Theorem 6.16: after rewriting the totalized derivative field through the ambient
gradient, the scalar line `s ↦ fderiv f (x + s • d) d` has the same endpoint derivative as the
scalarized gradient pairing. -/
private lemma scalarizedFDerivFieldHasDerivWithinAtZero
    {x d : E}
    (hgrad : DifferentiableAt ℝ (∇ problem.smoothPart) x) :
    HasDerivWithinAt
      (fun s : ℝ ↦ fderiv ℝ problem.smoothPart (x + s • d) d)
      (inner ℝ (hessian problem.smoothPart x d) d)
      (Set.Ici (0 : ℝ))
      0 := by
  -- Evaluate the totalized Fréchet derivative on `d` and rewrite it through the gradient owner.
  simpa [gradient, InnerProductSpace.toDualMap_apply_apply] using
    scalarizedGradientLineHasDerivWithinAtZero (x := x) (d := d) hgrad

/-- Helper for Theorem 6.16: if the feasible-line preimage is an actual neighborhood of `0`,
then the intrinsic feasible line derivative agrees with the ambient scalarized gradient pairing. -/
private lemma lineDerivWithin_eq_scalarGradientPairing_of_preimage_mem_nhds
    {x d : E} (hdiff : DifferentiableAt ℝ problem.smoothPart x)
    (hpre :
      ((fun u : ℝ ↦ x + u • d) ⁻¹' problem.feasibleSet) ∈ nhds (0 : ℝ)) :
    lineDerivWithin ℝ problem.smoothPart problem.feasibleSet x d =
      inner ℝ (∇ problem.smoothPart x) d := by
  let T : Set ℝ := (fun u : ℝ ↦ x + u • d) ⁻¹' problem.feasibleSet
  have hlineValue :
      lineDerivWithin ℝ problem.smoothPart problem.feasibleSet x d =
        deriv (fun u : ℝ ↦ problem.smoothPart (x + u • d)) 0 := by
    -- Because the line-preimage is a true neighborhood of `0`, the intrinsic owner is invisible
    -- to the one-dimensional derivative.
    simpa [lineDerivWithin, T] using
      (derivWithin_of_mem_nhds
        (f := fun u : ℝ ↦ problem.smoothPart (x + u • d))
        (s := T)
        (x := (0 : ℝ))
        hpre)
  have hlineDeriv :
      deriv (fun u : ℝ ↦ problem.smoothPart (x + u • d)) 0 =
        fderiv ℝ problem.smoothPart x d := by
    -- The ambient line restriction differentiates by the usual chain rule at the base point.
    simpa using hdiff.lineDeriv_eq_fderiv (v := d)
  -- Finish by rewriting the ambient Fréchet derivative as pairing against `∇ problem.smoothPart x`.
  calc
    lineDerivWithin ℝ problem.smoothPart problem.feasibleSet x d =
      deriv (fun u : ℝ ↦ problem.smoothPart (x + u • d)) 0 := hlineValue
    _ = fderiv ℝ problem.smoothPart x d := hlineDeriv
    _ = inner ℝ (∇ problem.smoothPart x) d := by
      simpa using (inner_gradient_left (y := d) hdiff).symm

/-- Helper for Theorem 6.16: at an interior segment point, translating a small amount along the
feasible direction stays on the same feasible segment, so the line-preimage owner is a neighborhood
of `0`. -/
private lemma feasibleSegmentLinePreimage_mem_nhds_zero_of_mem_Ioo
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    ((fun u : ℝ ↦
        AffineMap.lineMap (method t) y s + u • (y - method t)) ⁻¹' problem.feasibleSet) ∈
      nhds (0 : ℝ) := by
  let x := method t
  let d : E := y - x
  let seg : ℝ → E := AffineMap.lineMap x y
  let T : Set ℝ := (fun u : ℝ ↦ seg s + u • d) ⁻¹' problem.feasibleSet
  have hseg : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) problem.feasibleSet := by
    intro r hr
    exact problem.feasibleSet_convex.lineMap_mem (method.iterates_mem_feasibleSet t) hy hr
  have hshift :
      ∀ u : ℝ, seg s + u • d = seg (s + u) := by
    intro u
    -- Normalize the translated base point back to the original affine-segment parameterization.
    calc
      seg s + u • d = (AffineMap.lineMap x y) s + u • d := by
        rfl
      _ = s • d + x + u • d := by
        simp [seg, d, AffineMap.lineMap_apply_module']
      _ = (s + u) • d + x := by
        simp [add_smul, add_assoc, add_comm]
      _ = (AffineMap.lineMap x y) (s + u) := by
        simp [d, AffineMap.lineMap_apply_module']
      _ = seg (s + u) := by
        rfl
  have hT_subset : Set.Icc (-s) (1 - s) ⊆ T := by
    intro u hu
    have hsu : s + u ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨?_, ?_⟩
      · linarith [hu.1]
      · linarith [hu.2]
    -- Every short translated step remains on the feasible segment joining `x_t` and `y`.
    simpa [T, hshift u] using hseg hsu
  have hIcc_mem : Set.Icc (-s) (1 - s) ∈ nhds (0 : ℝ) := by
    exact Icc_mem_nhds (by linarith [hs.1]) (by linarith [hs.2])
  exact Filter.mem_of_superset hIcc_mem hT_subset

/-- Helper for Theorem 6.16: away from the left endpoint, the intrinsic feasible line derivative
along the segment agrees with the ordinary ambient line derivative because the feasible owner is a
true neighborhood of the translated parameter `0`. -/
private lemma feasibleSegmentLineDerivWithin_eventuallyEq_lineDeriv_right
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    (fun s : ℝ ↦
        lineDerivWithin ℝ problem.smoothPart problem.feasibleSet
          (AffineMap.lineMap (method t) y s)
          (y - method t)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      (fun s : ℝ ↦
        lineDeriv ℝ problem.smoothPart
          (AffineMap.lineMap (method t) y s)
          (y - method t)) := by
  filter_upwards [inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) (Iio_mem_nhds zero_lt_one)] with
      s hs
  rcases hs with ⟨hs_pos, hs_lt⟩
  have hs : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs_pos, hs_lt⟩
  let x := AffineMap.lineMap (method t) y s
  let d : E := y - method t
  let T : Set ℝ := (fun u : ℝ ↦ x + u • d) ⁻¹' problem.feasibleSet
  have hpre : T ∈ nhds (0 : ℝ) := by
    -- Interior segment points inherit a full translated feasible interval around the line origin.
    simpa [x, d, T] using
      feasibleSegmentLinePreimage_mem_nhds_zero_of_mem_Ioo method t hy hs
  -- Once the translated feasible owner is a neighborhood, `derivWithin` collapses to `deriv`.
  simpa [lineDerivWithin, lineDeriv, x, d, T] using
    (derivWithin_of_mem_nhds
      (f := fun u : ℝ ↦ problem.smoothPart (x + u • d))
      (s := T)
      (x := (0 : ℝ))
      hpre)

/-- Helper for Theorem 6.16: on a punctured short right neighborhood of `0`, the one-sided scalar
slice derivative already agrees with the ordinary ambient line derivative written in the translated
ray normal form `x_t + s • (y - x_t)`. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eventuallyEq_directionalLineDeriv_right
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          s) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      (fun s : ℝ ↦
        lineDeriv ℝ problem.smoothPart
          (method t + s • (y - method t))
          (y - method t)) := by
  -- First collapse the fixed one-sided owner to the ordinary ambient line derivative on interior
  -- segment points.
  refine (feasibleSegmentSlice_derivWithin_Ici_eventuallyEq_lineDerivWithin_right method t hy).trans
    ?_
  refine (feasibleSegmentLineDerivWithin_eventuallyEq_lineDeriv_right method t hy).trans ?_
  -- Then normalize the segment base point to the translated-ray spelling used by the Hessian API.
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Theorem 6.16: the degree-2 Taylor polynomial of the feasible scalar slice on the
fixed interval `[0, 1]` expands using the one-sided endpoint derivatives on `Set.Ici 0`. -/
private lemma feasibleSegmentSlice_leftEndpointTaylorWithinEvalTwoEq
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) (y : E) (a : ℝ) :
    taylorWithinEval
        (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
        2
        (Set.Icc (0 : ℝ) 1)
        0
        a =
      problem.smoothPart (method t) +
        a *
          derivWithin
            (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
            (Set.Ici (0 : ℝ))
            0 +
        (a ^ (2 : ℕ) / 2) *
          iteratedDerivWithin
            2
            (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
            (Set.Ici (0 : ℝ))
            0 := by
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (AffineMap.lineMap (method t) y s)
  have hsets : Set.Icc (0 : ℝ) 1 =ᶠ[nhds (0 : ℝ)] Set.Ici (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds zero_lt_one] with s hs_lt
    apply propext
    constructor
    · intro hs
      exact hs.1
    · intro hs
      exact ⟨hs, hs_lt.le⟩
  have hderiv :
      derivWithin ψ (Set.Icc (0 : ℝ) 1) 0 =
        derivWithin ψ (Set.Ici (0 : ℝ)) 0 :=
    derivWithin_congr_set hsets
  -- Expand the quadratic Taylor polynomial once, then transport both endpoint coefficients to the
  -- fixed one-sided owner `Set.Ici 0`.
  rw [taylorWithinEval_succ, taylorWithinEval_succ, taylor_within_zero_eval]
  simp only [Nat.factorial_zero, Nat.factorial_one, Nat.cast_zero, Nat.cast_one, zero_add, one_mul,
    sub_zero]
  have hderiv' :
      iteratedDerivWithin 1 ψ (Set.Icc (0 : ℝ) 1) 0 =
        derivWithin ψ (Set.Ici (0 : ℝ)) 0 := by
    simpa [iteratedDerivWithin_succ] using hderiv
  rw [hderiv', feasibleSegmentSlice_secondIteratedDerivWithin_Icc_eq_Ici (method := method)
    (t := t) (y := y)]
  simp [ψ]
  ring_nf <;> tauto

/-- Helper for Theorem 6.16: at the base point `s = 0`, the one-sided slice derivative on
`Set.Ici 0` is exactly the canonical feasible Fréchet derivative at `x_t` in direction
`y - x_t`. -/
private lemma feasibleSegmentSlice_derivWithinIci_zero_eq_directionalLinearTerm
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    derivWithin
        (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
        (Set.Ici (0 : ℝ))
        0 =
      fderivWithin ℝ problem.smoothPart problem.feasibleSet
        (method t)
        (y - method t) := by
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (AffineMap.lineMap (method t) y s)
  have hsets : Set.Icc (0 : ℝ) 1 =ᶠ[nhds (0 : ℝ)] Set.Ici (0 : ℝ) := by
    filter_upwards [Iio_mem_nhds zero_lt_one] with s hs_lt
    apply propext
    constructor
    · intro hs
      exact hs.1
    · intro hs
      exact ⟨hs, hs_lt.le⟩
  have howner :
      derivWithin ψ (Set.Ici (0 : ℝ)) 0 =
        derivWithin ψ (Set.Icc (0 : ℝ) 1) 0 := by
    -- The two scalar owners agree on a neighborhood of the left endpoint.
    simpa [ψ] using (derivWithin_congr_set hsets).symm
  -- Read the basepoint derivative through the already-stable chain-rule formula on `[0, 1]`.
  calc
    derivWithin ψ (Set.Ici (0 : ℝ)) 0 =
      derivWithin ψ (Set.Icc (0 : ℝ) 1) 0 := howner
    _ =
      fderivWithin ℝ problem.smoothPart problem.feasibleSet
        (AffineMap.lineMap (method t) y 0)
        (y - method t) :=
      feasibleSegmentSlice_derivWithin_Icc_eq_fderivWithin method t hy (by simp)
    _ =
      fderivWithin ℝ problem.smoothPart problem.feasibleSet
        (method t)
        (y - method t) := by
      simp

/-- Helper for Theorem 6.16: the left-endpoint one-sided slice derivative is the canonical
within-gradient pairing on the feasible owner. -/
private lemma feasibleSegmentSlice_derivWithinIci_zero_eq_gradientWithinPairing
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    derivWithin
        (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
        (Set.Ici (0 : ℝ))
        0 =
      inner ℝ (gradientWithin problem.smoothPart problem.feasibleSet (method t)) (y - method t) := by
  -- Read the endpoint derivative through the canonical feasible Fréchet derivative first.
  rw [feasibleSegmentSlice_derivWithinIci_zero_eq_directionalLinearTerm method t hy]
  -- Then unfold `gradientWithin`: it is just the inverse Riesz image of the feasible derivative.
  simpa [gradientWithin] using
    (InnerProductSpace.toDual_symm_apply
      (x := y - method t)
      (y := fderivWithin ℝ problem.smoothPart problem.feasibleSet (method t))).symm

/-- Helper for Theorem 6.16: once the canonical feasible derivative at `x_t` is identified with
the ambient gradient dual, the one-sided slice derivative at `0` becomes the ambient gradient
pairing in the feasible direction. -/
private lemma feasibleSegmentSlice_derivWithinIci_zero_eq_ambientGradientPairing_of_fderivWithinEq
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet)
    (hgradient :
      fderivWithin ℝ problem.smoothPart problem.feasibleSet (method t) =
        InnerProductSpace.toDualMap ℝ E (∇ problem.smoothPart (method t))) :
    derivWithin
        (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
        (Set.Ici (0 : ℝ))
        0 =
      inner ℝ (∇ problem.smoothPart (method t)) (y - method t) := by
  -- First read the endpoint derivative through the already-stable feasible-owner formula.
  rw [feasibleSegmentSlice_derivWithinIci_zero_eq_directionalLinearTerm method t hy]
  -- Then evaluate the identified dual map on the segment direction.
  simpa [InnerProductSpace.toDualMap_apply_apply] using
    congrArg (fun L : E →L[ℝ] ℝ ↦ L (y - method t)) hgradient

/-- Helper for Theorem 6.16: the quadratic Taylor quotient of the feasible scalar slice tends to
half of its one-sided second endpoint derivative on `Set.Ici 0`. -/
private lemma feasibleSegmentSlice_quadraticCoeff_tendsto_halfSecondDeriv
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    Filter.Tendsto
      (fun a : ℝ ↦
        ((problem.smoothPart (AffineMap.lineMap (method t) y a) -
              (problem.smoothPart (method t) +
                a *
                  derivWithin
                    (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
                    (Set.Ici (0 : ℝ))
                    0)) /
            a ^ (2 : ℕ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds
        ((1 / 2 : ℝ) *
          iteratedDerivWithin
            2
            (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
            (Set.Ici (0 : ℝ))
            0)) := by
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (AffineMap.lineMap (method t) y s)
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let R2 : ℝ → ℝ := fun a ↦ (ψ a - taylorWithinEval ψ 2 I 0 a) / a ^ (2 : ℕ)
  have hψ :
      ContDiffOn ℝ 2 ψ I :=
    feasibleSegmentSlice_contDiffOn_Icc method t hy
  have hR2_tendsto :
      Filter.Tendsto R2 (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))) (nhds 0) := by
    have hbase := Real.taylor_tendsto (s := I) (x₀ := (0 : ℝ))
      (convex_Icc (0 : ℝ) 1) (by simp [I]) hψ
    have hsmall : I ∈ nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) := by
      -- Restrict the fixed-interval Taylor limit to the right-neighborhood filter at `0`.
      refine Filter.mem_of_superset
        (Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)))
        ?_
      intro x hx
      rcases hx with ⟨hxpos, hxlt⟩
      exact ⟨le_of_lt hxpos, le_of_lt hxlt⟩
    exact Filter.Tendsto.mono_left (by simpa [R2, I] using hbase) <|
      (nhdsWithin_le_iff).2 hsmall
  have hrewrite :
      R2 =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
        fun a : ℝ ↦
          ((problem.smoothPart (AffineMap.lineMap (method t) y a) -
                (problem.smoothPart (method t) +
                  a *
                    derivWithin
                      (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
                      (Set.Ici (0 : ℝ))
                      0)) /
              a ^ (2 : ℕ)) -
            (1 / 2 : ℝ) *
              iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have ha_ne : a ≠ 0 := ne_of_gt ha
    dsimp [R2]
    rw [feasibleSegmentSlice_leftEndpointTaylorWithinEvalTwoEq method t y a]
    field_simp [ha_ne]
    ring
  have hmain :
      Filter.Tendsto
        (fun a : ℝ ↦
          ((problem.smoothPart (AffineMap.lineMap (method t) y a) -
                (problem.smoothPart (method t) +
                  a *
                    derivWithin
                      (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
                      (Set.Ici (0 : ℝ))
                      0)) /
              a ^ (2 : ℕ)) -
            (1 / 2 : ℝ) *
              iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds 0) := by
    exact hR2_tendsto.congr' hrewrite
  -- Rewrite the shifted quotient limit back to the displayed half-second-derivative target.
  let c : ℝ := (1 / 2 : ℝ) * iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0
  have hshift :
      Filter.Tendsto
        (fun a : ℝ ↦
          (((problem.smoothPart (AffineMap.lineMap (method t) y a) -
                  (problem.smoothPart (method t) +
                    a *
                      derivWithin
                        (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
                        (Set.Ici (0 : ℝ))
                        0)) /
            a ^ (2 : ℕ)) -
          c) + c)
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (0 + c)) := by
    have hc :
        Filter.Tendsto (fun _ : ℝ ↦ c)
          (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
          (nhds c) := tendsto_const_nhds
    simpa [c] using hmain.add hc
  convert hshift using 1
  · funext a
    ring
  · simp [c, ψ]

/-- Helper for Theorem 6.16: rewriting the feasible slice through `AffineMap.lineMap` gives the
ambient directional slice `x_t + s • (y - x_t)`. -/
private lemma feasibleSegmentSlice_eq_directionalSlice
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) (y : E) :
    (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s)) =
      fun s : ℝ ↦ problem.smoothPart (method t + s • (y - method t)) := by
  -- Normalize the affine segment to the ambient translated-ray spelling used by the Hessian API.
  funext s
  simp [AffineMap.lineMap_apply_module', add_comm]

/-- Helper for Theorem 6.16: the scalarized ambient gradient line is continuous from the feasible
right-hand owner once its one-sided derivative at `0` is known. -/
private lemma scalarizedGradientLine_continuousWithinAtZero
    {x d : E}
    (hgrad : DifferentiableAt ℝ (∇ problem.smoothPart) x) :
    ContinuousWithinAt
      (fun s : ℝ ↦ inner ℝ (∇ problem.smoothPart (x + s • d)) d)
      (Set.Ici (0 : ℝ))
      0 := by
  -- Package the derivative computation as the continuity fact needed by the endpoint-limit route.
  exact (scalarizedGradientLineHasDerivWithinAtZero (x := x) (d := d) hgrad).continuousWithinAt

/-- Helper for Theorem 6.16: evaluating the one-sided derivative of the scalarized ambient
gradient line at `0` reads off the Hessian quadratic form. -/
private lemma scalarizedGradientLine_derivWithinAtZero_eq_hessianQuadraticForm
    {x d : E}
    (hgrad : DifferentiableAt ℝ (∇ problem.smoothPart) x) :
    derivWithin
        (fun s : ℝ ↦ inner ℝ (∇ problem.smoothPart (x + s • d)) d)
        (Set.Ici (0 : ℝ))
        0 =
      inner ℝ (hessian problem.smoothPart x d) d := by
  -- Read the derivative value directly from the already-stable one-sided `HasDerivWithinAt`
  -- theorem for the scalarized ambient gradient line.
  exact
    (scalarizedGradientLineHasDerivWithinAtZero (x := x) (d := d) hgrad).derivWithin
      (uniqueDiffWithinAt_Ici (0 : ℝ))

/-- Helper for Theorem 6.16: the one-sided derivative of the ambient directional slice at the
base point is the ambient gradient pairing with the slice direction. -/
private lemma directionalSlice_derivWithinIci_zero_eq_ambientGradientPairing
    {x d : E} (hdiff : DifferentiableAt ℝ problem.smoothPart x) :
    derivWithin
        (fun s : ℝ ↦ problem.smoothPart (x + s • d))
        (Set.Ici (0 : ℝ))
        0 =
      inner ℝ (∇ problem.smoothPart x) d := by
  have hline :
      HasDerivAt
        (fun s : ℝ ↦ problem.smoothPart (x + s • d))
        (fderiv ℝ problem.smoothPart x d)
        0 := by
    -- Differentiate the ambient affine ray by the ordinary chain rule first.
    simpa using hdiff.hasFDerivAt.hasLineDerivAt d
  -- Then read the one-sided derivative value through the ambient gradient pairing identity.
  calc
    derivWithin
        (fun s : ℝ ↦ problem.smoothPart (x + s • d))
        (Set.Ici (0 : ℝ))
        0 =
      fderiv ℝ problem.smoothPart x d := by
        exact hline.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici (0 : ℝ))
    _ = inner ℝ (∇ problem.smoothPart x) d := by
        simpa using (inner_gradient_left (y := d) hdiff).symm

/-- Helper for Theorem 6.16: shifting the base point of the ambient `lineDeriv` field along a
fixed ray is the same as differentiating one fixed scalar directional slice at the shifted scalar
parameter. -/
private lemma directionalLineDeriv_eq_deriv_directionalSliceShift
    {x d : E} :
    (fun s : ℝ ↦ lineDeriv ℝ problem.smoothPart (x + s • d) d) =
      fun s : ℝ ↦ deriv (fun r : ℝ ↦ problem.smoothPart (x + r • d)) s := by
  -- Recenter every shifted base point back to the single scalar slice `r ↦ f (x + r • d)`.
  funext s
  let φ : ℝ → ℝ := fun r ↦ problem.smoothPart (x + r • d)
  calc
    lineDeriv ℝ problem.smoothPart (x + s • d) d =
      deriv (fun r : ℝ ↦ problem.smoothPart ((x + s • d) + r • d)) 0 := by
        simp [lineDeriv]
    _ = deriv (fun r : ℝ ↦ φ (r + s)) 0 := by
        congr 1
        funext r
        simp [φ, add_smul, add_assoc, add_left_comm, add_comm]
    _ = deriv φ s := by
        simpa [φ] using deriv_comp_add_const φ s 0

/-- Helper for Theorem 6.16: at any interior parameter `0 < s < 1`, the one-sided feasible slice
derivative already agrees with the ordinary derivative of the ambient directional slice. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eq_deriv_directionalSlice_of_mem_Ioo
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Ici (0 : ℝ))
        s =
      deriv
        (fun r : ℝ ↦ problem.smoothPart (method t + r • (y - method t)))
        s := by
  let ψ : ℝ → ℝ := fun r ↦ problem.smoothPart (AffineMap.lineMap (method t) y r)
  have hsets : Set.Ici (0 : ℝ) =ᶠ[nhds s] Set.Icc (0 : ℝ) 1 := by
    filter_upwards [Iio_mem_nhds hs.2] with r hr
    apply propext
    constructor
    · intro hr0
      exact ⟨hr0, hr.le⟩
    · intro hrIcc
      exact hrIcc.1
  -- First switch the owner from `Set.Ici 0` to the interior interval owner `[0, 1]`.
  calc
    derivWithin ψ (Set.Ici (0 : ℝ)) s =
      derivWithin ψ (Set.Icc (0 : ℝ) 1) s := by
        exact derivWithin_congr_set hsets
    _ = deriv ψ s := by
        rw [derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)]
    _ =
      deriv
        (fun r : ℝ ↦ problem.smoothPart (method t + r • (y - method t)))
        s := by
        -- Expand the local slice alias before normalizing to the translated-ray spelling.
        change
          deriv (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r)) s =
            deriv
              (fun r : ℝ ↦ problem.smoothPart (method t + r • (y - method t)))
              s
        rw [feasibleSegmentSlice_eq_directionalSlice method t y]

/-- Helper for Theorem 6.16: on a punctured short right neighborhood of `0`, the one-sided
feasible slice derivative agrees with the ordinary derivative of the ambient directional slice. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eventuallyEq_deriv_directionalSlice_right
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          s) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
      (fun s : ℝ ↦
        deriv
          (fun r : ℝ ↦ problem.smoothPart (method t + r • (y - method t)))
          s) := by
  filter_upwards [inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) (Iio_mem_nhds zero_lt_one)] with
      s hs
  have hs' : s ∈ Set.Ioo (0 : ℝ) 1 := hs
  -- Away from the endpoint, the feasible-owner derivative is already the ambient slice derivative.
  exact feasibleSegmentSlice_derivWithin_Ici_eq_deriv_directionalSlice_of_mem_Ioo
    (method := method) (t := t) hy hs'

/-- Helper for Theorem 6.16: at any interior parameter `0 < s < 1`, the one-sided feasible slice
derivative is already the ambient directional derivative based at the shifted segment point. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eq_directionalLineDeriv_of_mem_Ioo
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Ici (0 : ℝ))
        s =
      lineDeriv ℝ problem.smoothPart
        (method t + s • (y - method t))
        (y - method t) := by
  -- First rewrite the one-sided feasible slice derivative to the ordinary derivative of the
  -- translated ambient slice.
  calc
    derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Ici (0 : ℝ))
        s =
      deriv
        (fun r : ℝ ↦ problem.smoothPart (method t + r • (y - method t)))
        s :=
      feasibleSegmentSlice_derivWithin_Ici_eq_deriv_directionalSlice_of_mem_Ioo
        (method := method) (t := t) hy hs
    _ =
      lineDeriv ℝ problem.smoothPart
        (method t + s • (y - method t))
        (y - method t) := by
        -- Then recenter the shifted base point back to the fixed directional-slice spelling.
        symm
        simpa using
          congrArg (fun f : ℝ → ℝ ↦ f s)
            (directionalLineDeriv_eq_deriv_directionalSliceShift
              (x := method t) (d := y - method t))

/-- Helper for Theorem 6.16: at any interior segment parameter `0 < s < 1`, the one-sided slice
derivative is already the canonical feasible within-gradient pairing with the segment direction. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eq_gradientWithinPairing_of_mem_Ioo
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Ici (0 : ℝ))
        s =
      inner ℝ
        (gradientWithin problem.smoothPart problem.feasibleSet
          (AffineMap.lineMap (method t) y s))
        (y - method t) := by
  let ψ : ℝ → ℝ := fun r ↦ problem.smoothPart (AffineMap.lineMap (method t) y r)
  have hsets : Set.Ici (0 : ℝ) =ᶠ[nhds s] Set.Icc (0 : ℝ) 1 := by
    filter_upwards [Iio_mem_nhds hs.2] with r hr
    apply propext
    constructor
    · intro hr0
      exact ⟨hr0, hr.le⟩
    · intro hrIcc
      exact hrIcc.1
  -- First switch back to the fixed segment owner `[0, 1]` at the interior point.
  calc
    derivWithin ψ (Set.Ici (0 : ℝ)) s =
      derivWithin ψ (Set.Icc (0 : ℝ) 1) s := by
        exact derivWithin_congr_set hsets
    _ =
      fderivWithin ℝ problem.smoothPart problem.feasibleSet
        (AffineMap.lineMap (method t) y s)
        (y - method t) :=
      feasibleSegmentSlice_derivWithin_Icc_eq_fderivWithin
        (method := method) (t := t) hy ⟨hs.1.le, hs.2.le⟩
    _ =
      inner ℝ
        (gradientWithin problem.smoothPart problem.feasibleSet
          (AffineMap.lineMap (method t) y s))
        (y - method t) := by
        -- Then unfold `gradientWithin`: it is the Riesz representative of the feasible derivative.
        simpa [gradientWithin] using
          (InnerProductSpace.toDual_symm_apply
            (x := y - method t)
            (y := fderivWithin ℝ problem.smoothPart problem.feasibleSet
              (AffineMap.lineMap (method t) y s))).symm

/-- Helper for Theorem 6.16: on the one-sided owner `Set.Ici 0`, the feasible slice derivative
field is already the canonical feasible within-gradient pairing along the segment direction. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eventuallyEq_gradientWithinPairing
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          s) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))]
      (fun s : ℝ ↦
        inner ℝ
          (gradientWithin problem.smoothPart problem.feasibleSet
            (AffineMap.lineMap (method t) y s))
          (y - method t)) := by
  -- First rewrite the slice derivative through the canonical feasible Fréchet derivative owner.
  refine (feasibleSegmentSlice_derivWithin_Ici_eventuallyEq_fderivWithin method t hy).trans ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  -- Then unfold `gradientWithin`: it is the Riesz representative of that feasible derivative.
  simpa [gradientWithin] using
    (InnerProductSpace.toDual_symm_apply
      (x := y - method t)
      (y := fderivWithin ℝ problem.smoothPart problem.feasibleSet
        (AffineMap.lineMap (method t) y s))).symm

/-- Helper for Theorem 6.16: freezing the owner to `[0, 1]` lets the endpoint derivative of the
scalar slice derivative field be read directly from the ambient Hessian quadratic form. -/
private lemma feasibleSegmentSlice_derivWithinIcc_hasDerivWithinAtZero_raw
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    HasDerivWithinAt
      (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Icc (0 : ℝ) 1)
          s)
      (derivWithin
        (fun s : ℝ ↦
          derivWithin
            (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
            (Set.Icc (0 : ℝ) 1)
            s)
        (Set.Icc (0 : ℝ) 1)
        0)
      (Set.Ici (0 : ℝ))
      0 := by
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (AffineMap.lineMap (method t) y s)
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  have hψ : ContDiffOn ℝ 2 ψ I :=
    feasibleSegmentSlice_contDiffOn_Icc method t hy
  have hψ0 : ContDiffWithinAt ℝ 2 ψ I 0 :=
    hψ.contDiffWithinAt (by simp [I])
  have hfield :
      ContDiffWithinAt ℝ 1 (fun s : ℝ ↦ derivWithin ψ I s) I 0 := by
    -- Differentiate the fixed-owner scalar slice once on `[0, 1]`.
    simpa [I] using
      hψ0.derivWithin (uniqueDiffOn_Icc zero_lt_one) (by norm_num) (by simp [I])
  have hIcc :
      HasDerivWithinAt
        (fun s : ℝ ↦ derivWithin ψ I s)
        (derivWithin (fun s : ℝ ↦ derivWithin ψ I s) I 0)
        I
        0 := by
    -- A one-dimensional `C¹` field carries its within derivative as the endpoint derivative.
    exact (hfield.differentiableWithinAt (by norm_num)).hasDerivWithinAt
  -- The fixed interval `[0, 1]` is a right-neighborhood inside `Set.Ici 0` at the endpoint `0`.
  simpa [I, ψ] using hIcc.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE zero_lt_one)

/-- Helper for Theorem 6.16: the outer endpoint derivative of the fixed-owner slice profile can
be transported from `[0, 1]` to the one-sided owner `Set.Ici 0`. -/
private lemma feasibleSegmentSlice_outerDerivWithin_Icc_eq_Ici
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) (y : E) :
    derivWithin
        (fun s : ℝ ↦
          derivWithin
            (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
            (Set.Icc (0 : ℝ) 1)
            s)
        (Set.Icc (0 : ℝ) 1)
        0 =
      derivWithin
        (fun s : ℝ ↦
          derivWithin
            (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
            (Set.Ici (0 : ℝ))
            s)
        (Set.Ici (0 : ℝ))
        0 := by
  -- Route correction: reuse the already-proved second-derivative owner transport instead of
  -- redoing the outer-derivative congruence locally.
  simpa [iteratedDerivWithin_succ] using
    feasibleSegmentSlice_secondIteratedDerivWithin_Icc_eq_Ici
      (method := method) (t := t) (y := y)

/-- Helper for Theorem 6.16: the one-sided derivative profile on `Set.Ici 0` already has an
endpoint derivative; only its value still needs to be identified. -/
private lemma feasibleSegmentSlice_derivWithinIci_hasDerivWithinAtZero_raw
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    HasDerivWithinAt
      (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          s)
      (derivWithin
        (fun s : ℝ ↦
          derivWithin
            (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
            (Set.Ici (0 : ℝ))
            s)
        (Set.Ici (0 : ℝ))
        0)
      (Set.Ici (0 : ℝ))
      0 := by
  let profileIcc : ℝ → ℝ := fun s ↦
    derivWithin
      (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
      (Set.Icc (0 : ℝ) 1)
      s
  let profileIci : ℝ → ℝ := fun s ↦
    derivWithin
      (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
      (Set.Ici (0 : ℝ))
      s
  have hraw :
      HasDerivWithinAt
        profileIcc
        (derivWithin profileIcc (Set.Icc (0 : ℝ) 1) 0)
        (Set.Ici (0 : ℝ))
        0 :=
    feasibleSegmentSlice_derivWithinIcc_hasDerivWithinAtZero_raw method t hy
  have htransport :
      HasDerivWithinAt
        profileIci
        (derivWithin profileIcc (Set.Icc (0 : ℝ) 1) 0)
        (Set.Ici (0 : ℝ))
        0 := by
    have hfields : profileIci =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))] profileIcc := by
      simpa [profileIcc, profileIci] using
        feasibleSegmentSlice_derivWithin_Ici_eq_Icc_on_shortNeighborhood method t hy
    -- Switch only the derivative-field owner; the outer derivative value is rewritten afterwards.
    exact hraw.congr_of_eventuallyEq_of_mem hfields (by simp)
  -- Route correction: move derivative existence to `Set.Ici 0` first, then identify its value in
  -- a separate scalar bridge rather than comparing vector fields on the whole one-sided owner.
  simpa [profileIcc, profileIci,
    feasibleSegmentSlice_outerDerivWithin_Icc_eq_Ici (method := method) (t := t) (y := y)] using
    htransport

/-- Helper for Theorem 6.16: on the one-sided owner `Set.Ici 0`, the outer derivative of the
slice-derivative profile is already the derivative of the canonical feasible directional field. -/
private lemma feasibleSegmentSlice_outerDerivWithin_Ici_eq_feasibleDirectionalField
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    derivWithin
        (fun s : ℝ ↦
          derivWithin
            (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
            (Set.Ici (0 : ℝ))
            s)
        (Set.Ici (0 : ℝ))
        0 =
      derivWithin
        (fun s : ℝ ↦
          fderivWithin ℝ problem.smoothPart problem.feasibleSet
            (AffineMap.lineMap (method t) y s)
            (y - method t))
        (Set.Ici (0 : ℝ))
        0 := by
  -- Once the slice derivative has been normalized on the same owner, the outer derivative can be
  -- read through the feasible directional field without any more owner transport.
  exact Filter.EventuallyEq.derivWithin_eq_of_mem
    (feasibleSegmentSlice_derivWithin_Ici_eventuallyEq_fderivWithin method t hy)
    (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ))

/-- Helper for Theorem 6.16: at the level of derivative values, the one-sided outer derivative of
the feasible slice profile should match the ambient scalarized gradient line at `0`. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eq_directionalSliceProfile
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) (y : E) :
    (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          s) =
      fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (method t + r • (y - method t)))
          (Set.Ici (0 : ℝ))
          s := by
  -- Rewrite the scalar slice once at the function level, then keep the ambient ray spelling for
  -- all later one-sided derivative arguments.
  funext s
  rw [feasibleSegmentSlice_eq_directionalSlice method t y]

/-- Helper for Theorem 6.16: the outer one-sided derivative of the feasible slice profile can be
rewritten entirely in the ambient directional-slice spelling before any curvature comparison. -/
private lemma feasibleSegmentSlice_outerDerivWithin_Ici_eq_directionalSliceOuterProfile
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) (y : E) :
    derivWithin
        (fun s : ℝ ↦
          derivWithin
            (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
            (Set.Ici (0 : ℝ))
            s)
        (Set.Ici (0 : ℝ))
        0 =
      derivWithin
        (fun s : ℝ ↦
          derivWithin
            (fun r : ℝ ↦ problem.smoothPart (method t + r • (y - method t)))
            (Set.Ici (0 : ℝ))
            s)
        (Set.Ici (0 : ℝ))
        0 := by
  -- After the first-derivative profile is rewritten globally, the outer derivative value follows
  -- from the same owner with no additional transport.
  rw [feasibleSegmentSlice_derivWithin_Ici_eq_directionalSliceProfile method t y]

/-- Helper for Theorem 6.16: once the one-sided derivative field of the feasible scalar slice is
identified on `Set.Ici 0` with the ambient scalarized gradient line, the endpoint second
derivative is exactly the Hessian quadratic form. -/
private lemma feasibleSegmentSlice_iteratedDerivWithinTwo_eq_hessianQuadraticForm_of_eventuallyEq
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) (y : E)
    (hgrad : DifferentiableAt ℝ (∇ problem.smoothPart) (method t))
    (heq :
      (fun s : ℝ ↦
          derivWithin
            (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
            (Set.Ici (0 : ℝ))
            s) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))]
        (fun s : ℝ ↦
          inner ℝ (∇ problem.smoothPart (method t + s • (y - method t))) (y - method t))) :
    iteratedDerivWithin
        2
        (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
        (Set.Ici (0 : ℝ))
        0 =
      inner ℝ (hessian problem.smoothPart (method t) (y - method t)) (y - method t) := by
  let d : E := y - method t
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (AffineMap.lineMap (method t) y s)
  have houter :
      derivWithin (fun s : ℝ ↦ derivWithin ψ (Set.Ici (0 : ℝ)) s) (Set.Ici (0 : ℝ)) 0 =
        derivWithin (fun s : ℝ ↦ inner ℝ (∇ problem.smoothPart (method t + s • d)) d)
          (Set.Ici (0 : ℝ)) 0 := by
    -- Once the first-derivative field is normalized on the one-sided owner, the outer derivative
    -- can be read through the same normalized scalar field.
    simpa [ψ, d] using heq.derivWithin_eq_of_mem (by simp : (0 : ℝ) ∈ Set.Ici (0 : ℝ))
  -- Route correction: after the derivative-field normalization, only the scalarized ambient
  -- gradient line remains, and its one-sided derivative is already the Hessian quadratic form.
  calc
    iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 =
      derivWithin (fun s : ℝ ↦ derivWithin ψ (Set.Ici (0 : ℝ)) s) (Set.Ici (0 : ℝ)) 0 := by
        simp [iteratedDerivWithin_succ]
    _ =
      derivWithin (fun s : ℝ ↦ inner ℝ (∇ problem.smoothPart (method t + s • d)) d)
        (Set.Ici (0 : ℝ)) 0 := houter
    _ = inner ℝ (hessian problem.smoothPart (method t) d) d :=
      scalarizedGradientLine_derivWithinAtZero_eq_hessianQuadraticForm
        (x := method t) (d := d) hgrad

/-- Helper for Theorem 6.16: an eventual equality on the punctured right neighborhood together
with equality at `0` upgrades to an eventual equality on `Set.Ici 0`. -/
private lemma eventuallyEq_Ici_of_eventuallyEq_Ioi_of_eq_zero
    {f g : ℝ → ℝ}
    (hzero : f 0 = g 0)
    (hright : f =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))] g) :
    f =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))] g := by
  rw [Filter.EventuallyEq] at hright ⊢
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hright with ⟨U, hU_nhds, hU_sub⟩
  refine mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr ⟨U, hU_nhds, ?_⟩
  intro s hs
  rcases hs with ⟨hsU, hsIci⟩
  have hs_nonneg : 0 ≤ s := by
    simpa using hsIci
  rcases lt_or_eq_of_le hs_nonneg with hs_pos | rfl
  · exact hU_sub ⟨hsU, hs_pos⟩
  · simpa [hzero]

/-- Helper for Theorem 6.16: at any interior segment parameter `0 < s < 1`, the one-sided
feasible slice derivative is already the ambient gradient pairing at the shifted segment point. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eq_ambientGradientPairing_of_mem_Ioo
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet)
    {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Ici (0 : ℝ))
        s =
      inner ℝ (∇ problem.smoothPart (method t + s • (y - method t))) (y - method t) := by
  let d : E := y - method t
  have hs_mem : method t + s • d ∈ problem.feasibleSet := by
    simpa [d, AffineMap.lineMap_apply_module', add_comm] using
      problem.feasibleSet_convex.lineMap_mem (method.iterates_mem_feasibleSet t) hy
        ⟨hs.1.le, hs.2.le⟩
  have hdiffs : DifferentiableAt ℝ problem.smoothPart (method t + s • d) :=
    (method.objective_contDiffOn.differentiableOn (by norm_num)) _ hs_mem
  calc
    derivWithin
        (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
        (Set.Ici (0 : ℝ))
        s =
      lineDeriv ℝ problem.smoothPart (method t + s • d) d :=
        feasibleSegmentSlice_derivWithin_Ici_eq_directionalLineDeriv_of_mem_Ioo
          (method := method) (t := t) hy hs
    _ = fderiv ℝ problem.smoothPart (method t + s • d) d := by
        simpa using hdiffs.lineDeriv_eq_fderiv (v := d)
    _ = inner ℝ (∇ problem.smoothPart (method t + s • d)) d := by
        simpa using (inner_gradient_left (y := d) hdiffs).symm

/-- Helper for Theorem 6.16: on the one-sided owner `Set.Ici 0`, the feasible slice derivative
already agrees with the ambient scalarized gradient line along the same feasible segment. -/
private lemma feasibleSegmentSlice_derivWithin_Ici_eventuallyEq_ambientGradientPairing
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    (fun s : ℝ ↦
        derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          s) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ici (0 : ℝ))]
      (fun s : ℝ ↦
        inner ℝ (∇ problem.smoothPart (method t + s • (y - method t))) (y - method t)) := by
  let d : E := y - method t
  have hdiff0 : DifferentiableAt ℝ problem.smoothPart (method t) :=
    (method.objective_contDiffOn.differentiableOn (by norm_num)) _
      (method.iterates_mem_feasibleSet t)
  have hzero :
      derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          0 =
        inner ℝ (∇ problem.smoothPart (method t + (0 : ℝ) • d)) d := by
    calc
      derivWithin
          (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
          (Set.Ici (0 : ℝ))
          0 =
        derivWithin
          (fun s : ℝ ↦ problem.smoothPart (method t + s • d))
          (Set.Ici (0 : ℝ))
          0 := by
            rw [feasibleSegmentSlice_eq_directionalSlice method t y]
      _ = inner ℝ (∇ problem.smoothPart (method t)) d :=
        directionalSlice_derivWithinIci_zero_eq_ambientGradientPairing hdiff0
      _ = inner ℝ (∇ problem.smoothPart (method t + (0 : ℝ) • d)) d := by
        simp
  have hright :
      (fun s : ℝ ↦
          derivWithin
            (fun r : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y r))
            (Set.Ici (0 : ℝ))
            s) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
        (fun s : ℝ ↦
          inner ℝ (∇ problem.smoothPart (method t + s • (y - method t))) (y - method t)) := by
    filter_upwards [inter_mem_nhdsWithin (Set.Ioi (0 : ℝ)) (Iio_mem_nhds zero_lt_one)] with
        s hs
    have hs' : s ∈ Set.Ioo (0 : ℝ) 1 := hs
    exact feasibleSegmentSlice_derivWithin_Ici_eq_ambientGradientPairing_of_mem_Ioo
      (method := method) (t := t) hy hs'
  exact eventuallyEq_Ici_of_eventuallyEq_Ioi_of_eq_zero hzero hright

/-- Helper for Theorem 6.16: in the ambient-gradient differentiable branch, the quadratic Taylor
coefficient of the feasible scalar slice should agree with half of the ambient Hessian quadratic
form along the feasible direction. -/
private lemma feasibleSegmentSlice_iteratedDerivWithinTwo_eq_hessianQuadraticForm
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet)
    (hgrad : DifferentiableAt ℝ (∇ problem.smoothPart) (method t)) :
    iteratedDerivWithin
        2
        (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
        (Set.Ici (0 : ℝ))
        0 =
      inner ℝ (hessian problem.smoothPart (method t) (y - method t)) (y - method t) := by
  exact feasibleSegmentSlice_iteratedDerivWithinTwo_eq_hessianQuadraticForm_of_eventuallyEq
    (method := method) (t := t) (y := y) hgrad
    (feasibleSegmentSlice_derivWithin_Ici_eventuallyEq_ambientGradientPairing
      (method := method) (t := t) hy)

/-- Helper for Theorem 6.16: in the ambient-gradient differentiable branch, the quadratic Taylor
coefficient of the feasible scalar slice should agree with half of the ambient Hessian quadratic
form along the feasible direction. -/
private lemma feasibleSegmentSlice_quadraticCoeff_tendsto_halfHessian_of_gradientDifferentiable
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet)
    (hgrad : DifferentiableAt ℝ (∇ problem.smoothPart) (method t)) :
    Filter.Tendsto
      (fun a : ℝ ↦
        ((problem.smoothPart (AffineMap.lineMap (method t) y a) -
              (problem.smoothPart (method t) +
                a *
                  derivWithin
                    (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
                    (Set.Ici (0 : ℝ))
                    0)) /
            a ^ (2 : ℕ)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds
        ((1 / 2 : ℝ) *
          inner ℝ (hessian problem.smoothPart (method t) (y - method t)) (y - method t))) := by
  -- Once the one-sided curvature identity is available, the Taylor-quotient limit is just the
  -- existing half-second-derivative limit with its endpoint value rewritten.
  simpa [feasibleSegmentSlice_iteratedDerivWithinTwo_eq_hessianQuadraticForm
    (method := method) (t := t) (y := y) hy hgrad] using
    feasibleSegmentSlice_quadraticCoeff_tendsto_halfSecondDeriv method t hy

/-- Helper for Theorem 6.16: in the ambient-gradient differentiable branch, the left-endpoint
second within-derivative of the feasible scalar slice should agree with the ambient Hessian
quadratic form along the feasible direction. -/
private lemma feasibleSegmentSlice_secondDerivWithin_zero_eq_hessianQuadraticForm_of_gradientDifferentiable
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet)
    (hgrad : DifferentiableAt ℝ (∇ problem.smoothPart) (method t)) :
    derivWithin
        (derivWithin
          (fun s : ℝ ↦ problem.smoothPart (AffineMap.lineMap (method t) y s))
          (Set.Icc (0 : ℝ) 1))
        (Set.Icc (0 : ℝ) 1) 0 =
      inner ℝ (hessian problem.smoothPart (method t) (y - method t)) (y - method t) := by
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (AffineMap.lineMap (method t) y s)
  have hhalfSecond :=
    feasibleSegmentSlice_quadraticCoeff_tendsto_halfSecondDeriv method t hy
  have hhalfHessian :=
    feasibleSegmentSlice_quadraticCoeff_tendsto_halfHessian_of_gradientDifferentiable
      method t hy hgrad
  have hIci :
      iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 =
        inner ℝ (hessian problem.smoothPart (method t) (y - method t)) (y - method t) := by
    have hhalfEq :
        (1 / 2 : ℝ) * iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 =
          (1 / 2 : ℝ) *
            inner ℝ (hessian problem.smoothPart (method t) (y - method t)) (y - method t) :=
      tendsto_nhds_unique hhalfSecond hhalfHessian
    linarith
  -- Transport the stabilized endpoint identity from `Set.Ici 0` back to the original `Set.Icc`
  -- owner used by the scalar slice monotonicity proof.
  calc
    derivWithin (derivWithin ψ (Set.Icc (0 : ℝ) 1)) (Set.Icc (0 : ℝ) 1) 0 =
      iteratedDerivWithin 2 ψ (Set.Icc (0 : ℝ) 1) 0 := by
        simp [iteratedDerivWithin_succ]
    _ =
      iteratedDerivWithin 2 ψ (Set.Ici (0 : ℝ)) 0 :=
        feasibleSegmentSlice_secondIteratedDerivWithin_Icc_eq_Ici (method := method) (t := t)
          (y := y)
    _ =
      inner ℝ (hessian problem.smoothPart (method t) (y - method t)) (y - method t) := hIci

private lemma hessianQuadraticForm_nonnegAlongFeasibleDirection
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    0 ≤ inner ℝ (hessian problem.smoothPart (method t) (y - method t)) (y - method t) := by
  let x := method t
  let d : E := y - x
  let seg : ℝ → E := AffineMap.lineMap x y
  let I : Set ℝ := Set.Icc (0 : ℝ) 1
  let ψ : ℝ → ℝ := fun s ↦ problem.smoothPart (seg s)
  have hsecond_nonneg :
      0 ≤ derivWithin (derivWithin ψ I) I 0 := by
    -- The scalar feasible slice already has nonnegative left-endpoint curvature on `[0, 1]`.
    simpa [x, seg, I, ψ] using
      feasibleSegmentSlice_secondDerivWithin_zero_nonneg method t hy
  by_cases hgrad : DifferentiableAt ℝ (∇ problem.smoothPart) x
  · -- In the differentiable branch, rewrite the stable slice curvature through the isolated
    -- endpoint bridge back to the ambient Hessian quadratic form.
    rw [← feasibleSegmentSlice_secondDerivWithin_zero_eq_hessianQuadraticForm_of_gradientDifferentiable
      method t hy hgrad]
    exact hsecond_nonneg
  · -- In the nondifferentiable branch, the totalized ambient Hessian is zero.
    rw [hessian_eq_zero_of_not_differentiableAt_gradient hgrad]
    simp

/-- Helper for Theorem 6.16: contracting toward a feasible comparison point scales the full
second-order composite gap by at least the step size `τ_t`. -/
private lemma contractedSecondOrderGapAlongSegment_ge_stepSizeMulGap
    (method : CompositeTrustRegionContractionMethod problem x0)
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    let τ := method.stepSize t
    let z : E := (1 - τ) • method t + τ • y
    (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
        (secondOrderTaylorModelAt problem.smoothPart (method t) z +
          withTopRealPart problem.nonsmoothPart z) ≥
      τ *
        ((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
          (secondOrderTaylorModelAt problem.smoothPart (method t) y +
            withTopRealPart problem.nonsmoothPart y)) := by
  let τ := method.stepSize t
  let z : E := (1 - τ) • method t + τ • y
  let d : E := y - method t
  have hτ_nonneg : 0 ≤ τ := by
    simpa [τ] using (method.stepSize_mem_Ioc t).1.le
  have hτ_le_one : τ ≤ 1 := by
    simpa [τ] using (method.stepSize_mem_Ioc t).2
  have hτ_sq_le : τ ^ (2 : ℕ) ≤ τ := by
    nlinarith [hτ_nonneg, hτ_le_one]
  have h_one_sub_nonneg : 0 ≤ 1 - τ := sub_nonneg.mpr hτ_le_one
  have hsum_tau : 1 - τ + τ = 1 := by ring
  have hz_sub : z - method t = τ • d := by
    -- Normalize the contracted comparison point to the single feasible direction `d`.
    simp [z, d, sub_eq_add_neg, smul_add, add_smul, smul_sub, add_assoc, add_left_comm,
      add_comm]
  have hz_linear :
      inner ℝ (∇ problem.smoothPart (method t)) (z - method t) =
        τ * inner ℝ (∇ problem.smoothPart (method t)) d := by
    -- The linear Taylor term scales exactly with the contraction factor.
    rw [hz_sub, inner_smul_right]
  have hpsi :
      withTopRealPart problem.nonsmoothPart z ≤
        (1 - τ) * withTopRealPart problem.nonsmoothPart (method t) +
          τ * withTopRealPart problem.nonsmoothPart y := by
    -- Convexity controls the regularizer on the contracted segment point.
    simpa [z] using
      problem.nonsmoothPart_closedConvex.convexOn_withTopRealPart.2
        (method.iterates_mem_feasibleSet t) hy h_one_sub_nonneg hτ_nonneg hsum_tau
  have hquad_nonneg :
      0 ≤ inner ℝ (hessian problem.smoothPart (method t) d) d := by
    simpa [d] using
      hessianQuadraticForm_nonnegAlongFeasibleDirection method t hy
  have hquad_scale :
      (1 / 2 : ℝ) *
          inner ℝ (hessian problem.smoothPart (method t) (z - method t)) (z - method t) ≤
        τ * ((1 / 2 : ℝ) * inner ℝ (hessian problem.smoothPart (method t) d) d) := by
    have hscale :
        inner ℝ (hessian problem.smoothPart (method t) (z - method t)) (z - method t) =
          τ ^ (2 : ℕ) * inner ℝ (hessian problem.smoothPart (method t) d) d := by
      rw [hz_sub, map_smul, inner_smul_left, inner_smul_right]
      simpa [pow_two, mul_assoc]
    rw [hscale]
    nlinarith
  have hcontracted_model :
      secondOrderTaylorModelAt problem.smoothPart (method t) z +
          withTopRealPart problem.nonsmoothPart z ≤
        (1 - τ) *
            (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) +
          τ *
            (secondOrderTaylorModelAt problem.smoothPart (method t) y +
              withTopRealPart problem.nonsmoothPart y) := by
    have hpre :
        secondOrderTaylorModelAt problem.smoothPart (method t) z +
            withTopRealPart problem.nonsmoothPart z ≤
          problem.smoothPart (method t) +
            τ * inner ℝ (∇ problem.smoothPart (method t)) d +
            τ * ((1 / 2 : ℝ) * inner ℝ (hessian problem.smoothPart (method t) d) d) +
            ((1 - τ) * withTopRealPart problem.nonsmoothPart (method t) +
              τ * withTopRealPart problem.nonsmoothPart y) := by
      -- Expand the quadratic model once, then insert the Hessian and regularizer bounds.
      rw [secondOrderTaylorModelAt_apply, hz_linear]
      linarith
    calc
      secondOrderTaylorModelAt problem.smoothPart (method t) z +
          withTopRealPart problem.nonsmoothPart z ≤
        problem.smoothPart (method t) +
          τ * inner ℝ (∇ problem.smoothPart (method t)) d +
          τ * ((1 / 2 : ℝ) * inner ℝ (hessian problem.smoothPart (method t) d) d) +
          ((1 - τ) * withTopRealPart problem.nonsmoothPart (method t) +
            τ * withTopRealPart problem.nonsmoothPart y) := hpre
      _ =
        (1 - τ) *
            (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) +
          τ *
            (secondOrderTaylorModelAt problem.smoothPart (method t) y +
              withTopRealPart problem.nonsmoothPart y) := by
            rw [secondOrderTaylorModelAt_apply]
            dsimp [d]
            ring
  -- Rearrange the contracted-model comparison into the exact gap-scaling inequality.
  have hgap :
      (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
          (secondOrderTaylorModelAt problem.smoothPart (method t) z +
            withTopRealPart problem.nonsmoothPart z) ≥
        (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
          ((1 - τ) *
              (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) +
            τ *
              (secondOrderTaylorModelAt problem.smoothPart (method t) y +
                withTopRealPart problem.nonsmoothPart y)) := by
    linarith
  have hrewrite :
      (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
          ((1 - τ) *
              (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) +
            τ *
              (secondOrderTaylorModelAt problem.smoothPart (method t) y +
                withTopRealPart problem.nonsmoothPart y)) =
        τ *
          ((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (secondOrderTaylorModelAt problem.smoothPart (method t) y +
              withTopRealPart problem.nonsmoothPart y)) := by
    ring
  rw [hrewrite] at hgap
  simpa [τ, z] using hgap

/-- Helper for Theorem 6.16: every feasible comparison point yields a real one-step drop bound
against its second-order composite gap, up to the Hölder remainder. -/
private lemma objectiveDrop_ge_stepSizeMulSecondOrderGap_subHolderError
    (method : CompositeTrustRegionContractionMethod problem x0)
    {Hν D : ℝ} (ν : Set.Icc (0 : ℝ) 1)
    (hHν_nonneg : 0 ≤ Hν)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (h_upper_model :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet →
        problem.smoothPart y ≤
          secondOrderTaylorModelAt problem.smoothPart x y +
            Hν * Real.rpow ‖y - x‖ (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ))))
    (t : ℕ) {y : E} (hy : y ∈ problem.feasibleSet) :
    ((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
          (problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) ≥
      method.stepSize t *
          ((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (secondOrderTaylorModelAt problem.smoothPart (method t) y +
              withTopRealPart problem.nonsmoothPart y)) -
        ((Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) *
          Real.rpow (method.stepSize t) (2 + (ν : ℝ))) := by
  let τ := method.stepSize t
  let z : E := (1 - τ) • method t + τ • y
  let holderCoeff : ℝ :=
    Hν * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))
  have hτ_pos : 0 < τ := by
    simpa [τ] using (method.stepSize_mem_Ioc t).1
  have hτ_nonneg : 0 ≤ τ := hτ_pos.le
  have hD_nonneg : 0 ≤ D := by
    have hzero := hdiam (method.iterates_mem_feasibleSet t) (method.iterates_mem_feasibleSet t)
    simpa using hzero
  have hnorm_le :
      ‖method (t + 1) - method t‖ ≤ τ * D := by
    simpa [τ] using secondOrderSuccessorNormLeStepSizeMulDiameter method hdiam t
  have hpow_le :
      Real.rpow ‖method (t + 1) - method t‖ (2 + (ν : ℝ)) ≤
        Real.rpow (τ * D) (2 + (ν : ℝ)) := by
    exact Real.rpow_le_rpow (norm_nonneg _) hnorm_le (by linarith [ν.2.1])
  have hpow_mul :
      Real.rpow (τ * D) (2 + (ν : ℝ)) =
        Real.rpow D (2 + (ν : ℝ)) * Real.rpow τ (2 + (ν : ℝ)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.mul_rpow hD_nonneg hτ_nonneg : Real.rpow (D * τ) (2 + (ν : ℝ)) =
        Real.rpow D (2 + (ν : ℝ)) * Real.rpow τ (2 + (ν : ℝ)))
  have hholder_remainder :
      Hν * Real.rpow ‖method (t + 1) - method t‖ (2 + (ν : ℝ)) /
          ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) ≤
        holderCoeff * Real.rpow τ (2 + (ν : ℝ)) := by
    -- Bound the successor-model remainder by the diameter-scaled power of the step size.
    calc
      Hν * Real.rpow ‖method (t + 1) - method t‖ (2 + (ν : ℝ)) /
          ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) ≤
        Hν * Real.rpow (τ * D) (2 + (ν : ℝ)) /
          ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
            have hdenom_pos : 0 < ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
              nlinarith [ν.2.1]
            have hcoeff_nonneg :
                0 ≤ Hν / ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
              exact div_nonneg hHν_nonneg hdenom_pos.le
            simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
              mul_le_mul_of_nonneg_left hpow_le hcoeff_nonneg
      _ = Hν * (Real.rpow D (2 + (ν : ℝ)) * Real.rpow τ (2 + (ν : ℝ))) /
            ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
            rw [hpow_mul]
      _ = holderCoeff * Real.rpow τ (2 + (ν : ℝ)) := by
            dsimp [holderCoeff]
            ring
  have hz_contracted :
      z ∈ contractedFeasibleSet problem.feasibleSet (method t) τ := by
    -- The feasible comparison point `y` induces the contracted witness used by the subproblem.
    exact mem_contractedFeasibleSet_iff.mpr ⟨y, hy, by simp [z]⟩
  have hmin_real :
      secondOrderTaylorModelAt problem.smoothPart (method t) (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
        secondOrderTaylorModelAt problem.smoothPart (method t) z +
          withTopRealPart problem.nonsmoothPart z := by
    simpa [τ] using contractedCompositeModel_realMinBridge method t hz_contracted
  have hsucc_upper :
      problem.smoothPart (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
        secondOrderTaylorModelAt problem.smoothPart (method t) (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) +
          holderCoeff * Real.rpow τ (2 + (ν : ℝ)) := by
    have hsmooth :=
      h_upper_model (method.iterates_mem_feasibleSet t) (method.iterates_mem_feasibleSet (t + 1))
    have hsmooth_shift :
        problem.smoothPart (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
          secondOrderTaylorModelAt problem.smoothPart (method t) (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1)) +
            Hν * Real.rpow ‖method (t + 1) - method t‖ (2 + (ν : ℝ)) /
              ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) := by
      -- Add the nonsmooth term to the upper-model comparison at the actual successor.
      linarith
    have hholder_shift :
        secondOrderTaylorModelAt problem.smoothPart (method t) (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1)) +
            Hν * Real.rpow ‖method (t + 1) - method t‖ (2 + (ν : ℝ)) /
              ((1 + (ν : ℝ)) * (2 + (ν : ℝ))) ≤
          secondOrderTaylorModelAt problem.smoothPart (method t) (method (t + 1)) +
            withTopRealPart problem.nonsmoothPart (method (t + 1)) +
            holderCoeff * Real.rpow τ (2 + (ν : ℝ)) := by
      linarith [hholder_remainder]
    exact hsmooth_shift.trans hholder_shift
  have hcontracted_gap :
      (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
          (secondOrderTaylorModelAt problem.smoothPart (method t) z +
            withTopRealPart problem.nonsmoothPart z) ≥
        τ *
          ((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (secondOrderTaylorModelAt problem.smoothPart (method t) y +
              withTopRealPart problem.nonsmoothPart y)) := by
    simpa [τ, z] using
      contractedSecondOrderGapAlongSegment_ge_stepSizeMulGap method t hy
  -- Combine the upper-model comparison at the successor with the contracted-gap scaling.
  have hsucc_contracted :
      problem.smoothPart (method (t + 1)) +
          withTopRealPart problem.nonsmoothPart (method (t + 1)) ≤
        secondOrderTaylorModelAt problem.smoothPart (method t) z +
          withTopRealPart problem.nonsmoothPart z +
          holderCoeff * Real.rpow τ (2 + (ν : ℝ)) := by
    linarith [hsucc_upper, hmin_real]
  have hdrop_lower :
      ((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (problem.smoothPart (method (t + 1)) +
              withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) ≥
        ((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (secondOrderTaylorModelAt problem.smoothPart (method t) z +
              withTopRealPart problem.nonsmoothPart z +
              holderCoeff * Real.rpow τ (2 + (ν : ℝ))) : ℝ) := by
    linarith
  have hcontracted_err :
      ((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (secondOrderTaylorModelAt problem.smoothPart (method t) z +
              withTopRealPart problem.nonsmoothPart z +
              holderCoeff * Real.rpow τ (2 + (ν : ℝ))) : ℝ) ≥
        τ *
            ((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
              (secondOrderTaylorModelAt problem.smoothPart (method t) y +
                withTopRealPart problem.nonsmoothPart y)) -
          holderCoeff * Real.rpow τ (2 + (ν : ℝ)) := by
    linarith [hcontracted_gap]
  dsimp [τ, z, holderCoeff] at hdrop_lower hcontracted_err ⊢
  exact le_trans hcontracted_err hdrop_lower

-- Proof sketch: combine the local quadratic-model minimizing property from
-- `CompositeTrustRegionContractionMethod.iterates_succ_mem_and_isMinOn` with the update formula
-- `x_{t+1} = (1 - τ_t) x_t + τ_t v_t`, use the quadratic upper-model assumption with Hölder
-- remainder and the operator-norm bound on the canonical Hessian to control the estimating-
-- sequence error, and then rewrite the second displayed inequality through the source-facing
-- second-order optimality measure on `Q ∩ dom Ψ`.
/-- Equation `(6.4.55)` in Theorem 6.16: for every `ν ∈ [0, 1]`, the estimating-sequence bound
`A_t \bar f(x_t) ≤ φ_t(x) + \hat C_{ν,t}` holds for all `t ≥ 0` and `x ∈ Q`. -/
theorem estimating_function_bound
    (method : CompositeTrustRegionContractionMethod problem x0)
    (a : ℕ → ℝ) {L D : ℝ} (Hν : NNReal) (xStar : E)
    (ν : Set.Icc (0 : ℝ) 1)
    (hxStar :
      xStar ∈
        argmin[problem.feasibleSet]
          (fun x ↦ problem.smoothPart x + withTopRealPart problem.nonsmoothPart x))
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (h_hessian_bound : ∀ t : ℕ, ‖hessian problem.smoothPart (method t)‖ ≤ L)
    (h_upper_model :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet →
        problem.smoothPart y ≤
          secondOrderTaylorModelAt problem.smoothPart x y +
            (Hν : ℝ) * Real.rpow ‖y - x‖ (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) :
    ∀ t : ℕ, ∀ x : E, x ∈ problem.feasibleSet →
      A[a](t) *
          (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) ≤
        estimatingFunction method a t x + errorTerm method a xStar L (Hν : ℝ) D ν t := by
  rcases mem_constrainedArgmin_iff.mp hxStar with ⟨_, hxStar_min⟩
  intro t
  induction t with
  | zero =>
      intro x hx
      have ha0_nonneg : 0 ≤ a 0 := (ha_pos 0).le
      have hxStar_le :
          problem.smoothPart xStar + withTopRealPart problem.nonsmoothPart xStar ≤
            problem.smoothPart x + withTopRealPart problem.nonsmoothPart x := by
        exact (isMinOn_iff.mp hxStar_min) x hx
      have hbase_gap :
          problem.smoothPart (method 0) + withTopRealPart problem.nonsmoothPart (method 0) ≤
            problem.smoothPart x + withTopRealPart problem.nonsmoothPart x +
              ((problem.smoothPart (method 0) + withTopRealPart problem.nonsmoothPart (method 0)) -
                (problem.smoothPart xStar + withTopRealPart problem.nonsmoothPart xStar)) := by
        linarith
      have hbase_scaled := mul_le_mul_of_nonneg_left hbase_gap ha0_nonneg
      -- The initial stage uses only the minimizing property of `xStar` and the explicit initial
      -- error term.
      calc
        A[a](0) *
            (problem.smoothPart (method 0) +
              withTopRealPart problem.nonsmoothPart (method 0)) ≤
          a 0 *
            (problem.smoothPart x + withTopRealPart problem.nonsmoothPart x +
              ((problem.smoothPart (method 0) + withTopRealPart problem.nonsmoothPart (method 0)) -
                (problem.smoothPart xStar + withTopRealPart problem.nonsmoothPart xStar))) := by
              simpa [accumulatedWeights_apply] using hbase_scaled
        _ =
          estimatingFunction method a 0 x + errorTerm method a xStar L (Hν : ℝ) D ν 0 := by
              rw [estimatingFunction_zero, errorTerm_def, secondOrderError_zero]
              ring
  | succ t ih =>
      intro x hx
      let stepTerm :=
        a (t + 1) *
          (problem.smoothPart (method t) +
            inner ℝ (∇ problem.smoothPart (method t)) (x - method t) +
            withTopRealPart problem.nonsmoothPart x)
      let inc := secondOrderErrorIncrement a L (Hν : ℝ) D ν t
      have hstep :=
        weightedSecondOrderObjective_stepBound method a ν Hν.2 ha_pos h_step hdiam
          h_hessian_bound h_upper_model t hx
      have hcombine :
          accumulatedWeights a t *
              (problem.smoothPart (method t) +
                withTopRealPart problem.nonsmoothPart (method t)) +
            stepTerm + inc ≤
          estimatingFunction method a t x + errorTerm method a xStar L (Hν : ℝ) D ν t +
            stepTerm + inc := by
        have hih_step_raw :
            accumulatedWeights a t *
                (problem.smoothPart (method t) +
                  withTopRealPart problem.nonsmoothPart (method t)) + stepTerm ≤
              estimatingFunction method a t x + errorTerm method a xStar L (Hν : ℝ) D ν t +
                stepTerm := by
          simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right (ih x hx) stepTerm
        have hcombine_raw :
            inc +
                (accumulatedWeights a t *
                    (problem.smoothPart (method t) +
                      withTopRealPart problem.nonsmoothPart (method t)) + stepTerm) ≤
              inc +
                (estimatingFunction method a t x + errorTerm method a xStar L (Hν : ℝ) D ν t +
                  stepTerm) := by
          exact add_le_add_right hih_step_raw inc
        -- Add the same scalar increment to both sides after the induction step.
        simpa [add_assoc, add_left_comm, add_comm] using hcombine_raw
      have hstep' :
          accumulatedWeights a (t + 1) *
              (problem.smoothPart (method (t + 1)) +
                withTopRealPart problem.nonsmoothPart (method (t + 1))) ≤
            accumulatedWeights a t *
                (problem.smoothPart (method t) +
                  withTopRealPart problem.nonsmoothPart (method t)) +
              stepTerm + inc := by
        simpa [stepTerm, inc] using hstep
      have hfinal :
          accumulatedWeights a (t + 1) *
              (problem.smoothPart (method (t + 1)) +
                withTopRealPart problem.nonsmoothPart (method (t + 1))) ≤
            estimatingFunction method a t x + errorTerm method a xStar L (Hν : ℝ) D ν t +
              stepTerm + inc := by
        exact le_trans hstep' hcombine
      -- The successor step is the one-step weighted bound followed by one unfolding of the two
      -- recursive owner surfaces.
      simpa [estimatingFunction_succ, errorTerm_def, secondOrderError_succ, stepTerm, inc,
        add_assoc, add_left_comm, add_comm] using hfinal

/-- Equation `(6.4.56)` in Theorem 6.16: for every `t ≥ 0`, the one-step decrease satisfies the
canonical `EReal`-valued objective-drop inequality, keeping the internal owner
`secondOrderOptimalityMeasure` on its native value layer. -/
theorem objective_drop_lower_bound
    (method : CompositeTrustRegionContractionMethod problem x0)
    {D : ℝ} (Hν : NNReal)
    (ν : Set.Icc (0 : ℝ) 1)
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (h_upper_model :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet →
        problem.smoothPart y ≤
          secondOrderTaylorModelAt problem.smoothPart x y +
            (Hν : ℝ) * Real.rpow ‖y - x‖ (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) :
    ∀ t : ℕ,
      (((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (problem.smoothPart (method (t + 1)) +
              withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) ≥
        (method.stepSize t : EReal) *
            θ[problem.feasibleSet, problem.smoothPart, problem.nonsmoothPart](
              ⟨method t, iterate_mem_optimalityDomain method t⟩) -
          ((((Hν : ℝ) * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) *
            Real.rpow (method.stepSize t) (2 + (ν : ℝ)) : ℝ) : EReal) := by
  intro t
  let drop : ℝ :=
    (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
      (problem.smoothPart (method (t + 1)) +
        withTopRealPart problem.nonsmoothPart (method (t + 1)))
  let err : ℝ :=
    (((Hν : ℝ) * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) *
      Real.rpow (method.stepSize t) (2 + (ν : ℝ)))
  have hτ_pos : 0 < method.stepSize t := (method.stepSize_mem_Ioc t).1
  have hτE_pos : 0 < (method.stepSize t : EReal) := by
    exact_mod_cast hτ_pos
  have hτE_top : (method.stepSize t : EReal) ≠ ⊤ := by
    simp
  have hgap_div :
      θ[problem.feasibleSet, problem.smoothPart, problem.nonsmoothPart](
          ⟨method t, iterate_mem_optimalityDomain method t⟩) ≤
        ((((drop + err) / method.stepSize t : ℝ) : EReal)) := by
    -- Package the pointwise real drop estimate into a uniform `EReal` upper bound on `θ(x_t)`.
    refine secondOrderOptimalityMeasure_le_of_realBound (method := method) t ?_
    intro y hy
    have hy_drop :=
      objectiveDrop_ge_stepSizeMulSecondOrderGap_subHolderError
        method ν Hν.2 hdiam h_upper_model t hy
    dsimp [drop, err] at hy_drop ⊢
    exact (le_div_iff₀ hτ_pos).2 (by linarith)
  have hmul :
      θ[problem.feasibleSet, problem.smoothPart, problem.nonsmoothPart](
          ⟨method t, iterate_mem_optimalityDomain method t⟩) *
          (method.stepSize t : EReal) ≤
        (drop : EReal) + (err : EReal) := by
    -- Move from the divided bound to the scaled gap bound using positivity of the step size.
    have hgap_div' :
        θ[problem.feasibleSet, problem.smoothPart, problem.nonsmoothPart](
            ⟨method t, iterate_mem_optimalityDomain method t⟩) ≤
          ((drop : EReal) + (err : EReal)) / (method.stepSize t : EReal) := by
      simpa [EReal.coe_div, EReal.coe_add] using hgap_div
    exact (EReal.le_div_iff_mul_le hτE_pos hτE_top).1 hgap_div'
  have hsub :
      (method.stepSize t : EReal) *
            θ[problem.feasibleSet, problem.smoothPart, problem.nonsmoothPart](
              ⟨method t, iterate_mem_optimalityDomain method t⟩) -
          (err : EReal) ≤
        (drop : EReal) := by
    -- Rearrange the scaled gap estimate into the textbook lower-bound form.
    exact EReal.sub_le_of_le_add (by simpa [add_comm, mul_comm] using hmul)
  simpa [drop, err, mul_comm] using hsub

-- Source-facing split: expose `(6.4.55)` and `(6.4.56)` separately, and package them together in
-- the full textbook theorem.
/-- Theorem 6.16: if `{x_t}` is generated by method `(6.4.50)`, then for every `ν ∈ [0, 1]`,
every integer `t ≥ 0`, and every `x ∈ Q`, the estimating-sequence bound `(6.4.55)` holds;
moreover, for every integer `t ≥ 0`, the objective-drop inequality `(6.4.56)` holds. -/
theorem estimating_function_bound_and_objective_drop
    (method : CompositeTrustRegionContractionMethod problem x0)
    (a : ℕ → ℝ) {L D : ℝ} (Hν : NNReal) (xStar : E)
    (ν : Set.Icc (0 : ℝ) 1)
    (hxStar :
      xStar ∈
        argmin[problem.feasibleSet]
          (fun x ↦ problem.smoothPart x + withTopRealPart problem.nonsmoothPart x))
    (ha_pos : ∀ t : ℕ, 0 < a t)
    (h_step : ∀ t : ℕ, method.stepSize t = τ[a](t))
    (hdiam :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet → ‖x - y‖ ≤ D)
    (h_hessian_bound : ∀ t : ℕ, ‖hessian problem.smoothPart (method t)‖ ≤ L)
    (h_upper_model :
      ∀ ⦃x y : E⦄, x ∈ problem.feasibleSet → y ∈ problem.feasibleSet →
        problem.smoothPart y ≤
          secondOrderTaylorModelAt problem.smoothPart x y +
            (Hν : ℝ) * Real.rpow ‖y - x‖ (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) :
    (∀ t : ℕ, ∀ x : E, x ∈ problem.feasibleSet →
      A[a](t) *
          (problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) ≤
        estimatingFunction method a t x + errorTerm method a xStar L (Hν : ℝ) D ν t) ∧
    (∀ t : ℕ,
      (((problem.smoothPart (method t) + withTopRealPart problem.nonsmoothPart (method t)) -
            (problem.smoothPart (method (t + 1)) +
              withTopRealPart problem.nonsmoothPart (method (t + 1))) : ℝ) : EReal) ≥
        (method.stepSize t : EReal) *
            θ[problem.feasibleSet, problem.smoothPart, problem.nonsmoothPart](
              ⟨method t, iterate_mem_optimalityDomain method t⟩) -
          ((((Hν : ℝ) * Real.rpow D (2 + (ν : ℝ)) / ((1 + (ν : ℝ)) * (2 + (ν : ℝ)))) *
            Real.rpow (method.stepSize t) (2 + (ν : ℝ)) : ℝ) : EReal)) := by
  constructor
  · -- The first displayed inequality is exactly the already-proved estimating-sequence bound.
    exact estimating_function_bound method a Hν xStar ν hxStar ha_pos h_step hdiam
      h_hessian_bound h_upper_model
  · -- The second displayed inequality is the `EReal` objective-drop theorem just proved above.
    exact objective_drop_lower_bound method Hν ν hdiam h_upper_model

end Method

end SecondOrderLocalModel

end
