/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_3

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators

noncomputable section

/- Proposition 4.14 is `source-facing` in the Chapter 4 conjugacy API. The `core/canonical`
owner abstraction is `conjugate_function` from Definition 4.1, and the relevant `bridge/view`
owner is `conjugate_function_separable_sum_eq_sum_conjugate_function` from Theorem 4.3. The only
primitive local data are the scalar and coordinatewise negative-entropy integrands; the scalar and
Euclidean primal conjugacy formulas are derived from the chapter owner notation `f∗` rather than
stored as parallel dual-space wrappers. -/

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

recall conjugate_function_primal_apply

/-- The scalar negative-entropy integrand `t ↦ t log t` on `[0, ∞)`, extended by `∞` on the
negative ray. -/
def negative_entropy_scalar : ℝ → EReal :=
  fun t ↦ if 0 ≤ t then ((t * Real.log t : ℝ) : EReal) else ⊤

/-- On the nonnegative ray, `negative_entropy_scalar` is the finite value `t log t`. -/
@[simp] theorem negative_entropy_scalar_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    negative_entropy_scalar t = ((t * Real.log t : ℝ) : EReal) := by
  simp [negative_entropy_scalar, ht]

/-- On the negative ray, `negative_entropy_scalar` takes the value `∞`. -/
@[simp] theorem negative_entropy_scalar_of_neg {t : ℝ} (ht : t < 0) :
    negative_entropy_scalar t = ⊤ := by
  simp [negative_entropy_scalar, not_le_of_gt ht]

/-- The coordinatewise negative entropy on `ℝ^n`, modeled as `Fin n → ℝ` and extended by `∞`
outside the nonnegative orthant. -/
def negative_entropy_function (n : ℕ) : EuclideanSpace ℝ (Fin n) → EReal :=
  fun x ↦ ∑ i : Fin n, negative_entropy_scalar (x i)

/-- Evaluating `negative_entropy_function n` at `x` sums the scalar negative-entropy integrand over
the coordinates. -/
@[simp] theorem negative_entropy_function_apply (x : E) :
    negative_entropy_function n x = ∑ i, negative_entropy_scalar (x i) :=
  rfl

/-- Helper for Proposition 4.14: the scalar negative-entropy integrand is proper, so the
coordinatewise separable-sum conjugacy theorem applies to it. -/
lemma negativeEntropyScalar_isProper : IsProperExtendedRealFunction negative_entropy_scalar := by
  refine ⟨?_, ?_⟩
  · -- The scalar integrand only takes finite real values or `∞`, never `-∞`.
    intro t
    by_cases ht : 0 ≤ t
    · rw [negative_entropy_scalar_of_nonneg ht]
      simpa using (EReal.coe_ne_bot (t * Real.log t))
    · rw [negative_entropy_scalar_of_neg (lt_of_not_ge ht)]
      simp
  · -- The point `t = 1` lies in the effective domain and gives a finite value.
    refine ⟨1, ?_⟩
    rw [mem_effective_domain, negative_entropy_scalar_of_nonneg]
    · simp
    · norm_num

/-- Helper for Proposition 4.14: the scalar Fenchel objective is globally bounded above by
`exp (s - 1)` on the nonnegative ray. -/
lemma negativeEntropyObjective_le_expShift {s t : ℝ} (ht : 0 ≤ t) :
    s * t - t * Real.log t ≤ Real.exp (s - 1) := by
  by_cases hzero : t = 0
  · -- At the boundary point `t = 0`, the objective is `0`, so positivity of the exponential
    -- closes the estimate.
    subst hzero
    simpa using le_of_lt (Real.exp_pos (s - 1))
  · -- For `t > 0`, apply `log u ≤ u - 1` to `u = exp (s - 1) / t`.
    have ht_pos : 0 < t := lt_of_le_of_ne ht (by simpa [eq_comm] using hzero)
    have hquot_pos : 0 < Real.exp (s - 1) / t := by
      exact div_pos (Real.exp_pos (s - 1)) ht_pos
    have hlog := Real.log_le_sub_one_of_pos hquot_pos
    have hmul : t * Real.log (Real.exp (s - 1) / t) ≤ t * (Real.exp (s - 1) / t - 1) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_right hlog ht
    have hlog_div : Real.log (Real.exp (s - 1) / t) = (s - 1) - Real.log t := by
      rw [Real.log_div (Real.exp_ne_zero (s - 1)) hzero, Real.log_exp]
    have hbound : t * ((s - 1) - Real.log t) ≤ Real.exp (s - 1) - t := by
      calc
        t * ((s - 1) - Real.log t) = t * Real.log (Real.exp (s - 1) / t) := by
          rw [hlog_div]
        _ ≤ t * (Real.exp (s - 1) / t - 1) := hmul
        _ = Real.exp (s - 1) - t := by
          calc
            t * (Real.exp (s - 1) / t - 1) = t * (Real.exp (s - 1) / t) - t := by ring
            _ = Real.exp (s - 1) - t := by rw [mul_div_cancel₀ _ hzero]
    have hadd : t * ((s - 1) - Real.log t) + t ≤ Real.exp (s - 1) - t + t := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hbound t
    calc
      s * t - t * Real.log t = t * ((s - 1) - Real.log t) + t := by ring
      _ ≤ Real.exp (s - 1) - t + t := hadd
      _ = Real.exp (s - 1) := by ring

/-- Helper for Proposition 4.14: the scalar Fenchel objective attains the value `exp (s - 1)` at
the point `t = exp (s - 1)`. -/
lemma negativeEntropyObjective_eq_expShift_atExp (s : ℝ) :
    s * Real.exp (s - 1) - Real.exp (s - 1) * Real.log (Real.exp (s - 1)) =
      Real.exp (s - 1) := by
  -- Evaluate the objective at the candidate optimizer and simplify with `log (exp z) = z`.
  rw [Real.log_exp]
  ring

/-- Helper for Proposition 4.14: on `ℝ`, the Riesz-map pairing is ordinary multiplication. -/
lemma realToDualMap_apply_eq_mul (s t : ℝ) :
    ((InnerProductSpace.toDualMap ℝ ℝ) s) t = s * t := by
  simpa using (RCLike.inner_apply' s t)

/-- Helper for Proposition 4.14: the scalar Fenchel objective range has greatest element
`exp (s - 1)` after coercing to `EReal`. -/
lemma negativeEntropyScalarObjectiveEReal_isGreatest (s : ℝ) :
    IsGreatest
      (Set.range
        (fun t : ℝ ↦ ((((InnerProductSpace.toDualMap ℝ ℝ) s) t : ℝ) : EReal) -
          negative_entropy_scalar t))
      (((Real.exp (s - 1) : ℝ) : EReal)) := by
  refine ⟨?_, ?_⟩
  · -- The exponential point realizes the equality case from the scalar evaluation helper.
    refine ⟨Real.exp (s - 1), ?_⟩
    change
      ((((InnerProductSpace.toDualMap ℝ ℝ) s) (Real.exp (s - 1)) : ℝ) : EReal) -
        negative_entropy_scalar (Real.exp (s - 1)) =
          ((Real.exp (s - 1) : ℝ) : EReal)
    have hexp_nonneg : 0 ≤ Real.exp (s - 1) := le_of_lt (Real.exp_pos (s - 1))
    rw [negative_entropy_scalar_of_nonneg hexp_nonneg]
    rw [realToDualMap_apply_eq_mul, ← EReal.coe_sub]
    exact congrArg (fun t : ℝ ↦ (t : EReal))
      (negativeEntropyObjective_eq_expShift_atExp s)
  · -- Negative inputs give `⊥`, and nonnegative inputs are controlled by the real inequality.
    intro z hz
    rcases hz with ⟨t, rfl⟩
    change ((((InnerProductSpace.toDualMap ℝ ℝ) s) t : ℝ) : EReal) - negative_entropy_scalar t ≤
      ((Real.exp (s - 1) : ℝ) : EReal)
    by_cases ht : 0 ≤ t
    · rw [negative_entropy_scalar_of_nonneg ht]
      rw [realToDualMap_apply_eq_mul, ← EReal.coe_sub]
      exact_mod_cast negativeEntropyObjective_le_expShift (s := s) ht
    · rw [negative_entropy_scalar_of_neg (lt_of_not_ge ht), EReal.sub_top]
      simp

-- Proof sketch: compute the supremum defining `(negative_entropy_scalar∗) s`. On `[0, ∞)`,
-- maximize `t ↦ s * t - t * log t`; its derivative vanishes at `t = exp (s - 1)`, the second
-- derivative is negative, and the boundary value at `t = 0` is smaller, so the supremum equals
-- `exp (s - 1)`.
/-- Helper for Proposition 4.14: the scalar Fenchel conjugate of the negative-entropy integrand is
`s ↦ exp (s - 1)`. -/
theorem negative_entropy_scalar_conjugate_eq (s : ℝ) :
    (negative_entropy_scalar∗) s = ((Real.exp (s - 1) : ℝ) : EReal) := by
  -- Rewrite the primal conjugate as the `EReal` supremum of the scalar Fenchel objective.
  rw [conjugate_function_primal_apply, conjugate_function_apply]
  -- The scalar optimization helper identifies that supremum with its greatest value.
  exact (negativeEntropyScalarObjectiveEReal_isGreatest s).csSup_eq

-- Proof sketch: view `negative_entropy_function` as the finite separable sum
-- `x ↦ ∑ i, negative_entropy_scalar (x i)` on `Fin n → ℝ` and apply
-- `conjugate_function_separable_sum_eq_sum_conjugate_function` to the coordinate dual family
-- `fun i ↦ LinearMap.toSpanSingleton ℝ ℝ (y i)`. The resulting product dual is exactly the
-- Euclidean pairing dual `dotProductEquiv ℝ (Fin n) y`, and the scalar summands are identified
-- with `(negative_entropy_scalar∗) (y i)` via `conjugate_function_primal_apply`.
/-- Helper for Proposition 4.14: on `ℝ^n`, modeled as `Fin n → ℝ`, the primal Fenchel conjugate
of the coordinatewise negative entropy is the sum of the scalar conjugates on the coordinates. -/
theorem negative_entropy_function_conjugate_eq_sum_scalar_conjugates
    (y : E) :
    ((negative_entropy_function n)∗) y = ∑ i, (negative_entropy_scalar∗) (y i) :=
  by
  rw [conjugate_function_primal_apply]
  -- Package the Euclidean pairing as a coordinate dual on `EuclideanSpace ℝ (Fin n)`.
  let coordinateDual : Module.Dual ℝ E :=
    { toFun := fun x ↦ dotProduct y.ofLp x.ofLp
      map_add' := by
        intro x z
        simp [dotProduct_add]
      map_smul' := by
        intro a x
        simp [dotProduct_smul] }
  have hdual : ((InnerProductSpace.toDualMap ℝ E) y : Module.Dual ℝ E) = coordinateDual := by
    ext x
    suffices hinner : inner ℝ y x = y.ofLp ⬝ᵥ x.ofLp by
      simpa [coordinateDual, InnerProductSpace.toDualMap_apply_apply] using hinner
    calc
      inner ℝ y x = x.ofLp ⬝ᵥ y.ofLp := by
        simpa using (EuclideanSpace.inner_eq_star_dotProduct (x := y) (y := x))
      _ = y.ofLp ⬝ᵥ x.ofLp := dotProduct_comm _ _
  rw [hdual]
  have hcoord :
      conjugate_function (negative_entropy_function n) coordinateDual =
        conjugate_function (fun x : Fin n → ℝ ↦ ∑ i, negative_entropy_scalar (x i))
          (dotProductEquiv ℝ (Fin n) y.ofLp) := by
    -- Unfold both conjugates and transport the attainable-value range through `ofLp`/`toLp`.
    rw [conjugate_function_apply, conjugate_function_apply]
    let primalObj : E → EReal :=
      fun x ↦ (coordinateDual x : EReal) - negative_entropy_function n x
    let coordObj : (Fin n → ℝ) → EReal :=
      fun x ↦ (((dotProductEquiv ℝ (Fin n) y.ofLp) x : ℝ) : EReal) -
        ∑ i, negative_entropy_scalar (x i)
    have hprimal_coord : ∀ x : E, primalObj x = coordObj x.ofLp := by
      intro x
      simp [primalObj, coordObj, coordinateDual, negative_entropy_function, dotProductEquiv]
    have hcoord_primal : ∀ x : Fin n → ℝ, primalObj (WithLp.toLp 2 x) = coordObj x := by
      intro x
      simpa [WithLp.ofLp_toLp] using hprimal_coord (WithLp.toLp 2 x)
    have hrange : Set.range primalObj = Set.range coordObj := by
      ext r
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.ofLp, hprimal_coord x⟩
      · rintro ⟨x, rfl⟩
        exact ⟨WithLp.toLp 2 x, hcoord_primal x⟩
    rw [hrange]
  have hsep :=
    conjugate_function_separable_sum_eq_sum_conjugate_function
      (f := fun _ : Fin n ↦ negative_entropy_scalar)
      (h_proper := fun _ : Fin n ↦ negativeEntropyScalar_isProper)
      (y := fun i : Fin n ↦ LinearMap.toSpanSingleton ℝ ℝ (y i))
  rw [lsum_toSpanSingleton_eq_dotProductEquiv] at hsep
  -- The coordinate-side separable-sum theorem now applies directly.
  calc
    conjugate_function (negative_entropy_function n) coordinateDual
        = conjugate_function (fun x : Fin n → ℝ ↦ ∑ i, negative_entropy_scalar (x i))
            (dotProductEquiv ℝ (Fin n) y.ofLp) := hcoord
    _ =
        ∑ i, conjugate_function negative_entropy_scalar
          (LinearMap.toSpanSingleton ℝ ℝ (y i)) := hsep
    _ = ∑ i, (negative_entropy_scalar∗) (y i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [conjugate_function_primal_apply]
      congr 1

-- Proof sketch: combine `negative_entropy_function_conjugate_eq_sum_scalar_conjugates` with the
-- scalar formula `negative_entropy_scalar_conjugate_eq`, and simplify the finite sum.
/-- Proposition 4.14: the conjugate of the coordinatewise negative entropy on `ℝ^n` is the sum of
the exponentials `exp (y_i - 1)` over the coordinates. -/
theorem negative_entropy_function_conjugate_eq_sum_exp
    (y : E) :
    ((negative_entropy_function n)∗) y = ∑ i, ((Real.exp (y i - 1) : ℝ) : EReal) := by
  -- Replace each scalar conjugate term by the scalar exponential formula.
  rw [negative_entropy_function_conjugate_eq_sum_scalar_conjugates]
  -- The remaining finite sum simplifies coordinatewise by the scalar conjugate theorem.
  simp [negative_entropy_scalar_conjugate_eq]

end

end
