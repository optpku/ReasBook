/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30

open scoped Gradient lp StrongConvexSmooth

noncomputable section

local notation "ℝ∞" => ℓ²(ℕ, ℝ)
local notation "I∞" => ContinuousLinearMap.id ℝ ℝ∞
local notation "e1" => (lp.single 2 0 (1 : ℝ) : ℝ∞)

/-
Primary domain: first-order lower-complexity bounds for smooth strongly convex minimization on
the Hilbert space `ℝ∞ = ℓ²(ℕ, ℝ)`.

Relevant owner-style declarations sampled before refining this file:
* `SatisfiesSpanCondition` from `Definition_2_9`, viewed on iterate families
  `(ℝ∞ → ℝ) → ℝ∞ → ℕ → ℝ∞`
* `nesterovLowerBoundOperatorObjective` from `Proposition_2_7`, the chapter's canonical
  `ℓ²` hard-instance objective
* `nesterovLowerBoundOperatorObjective_mem_S11` from `Proposition_2_7`,
  which gives the objective-class membership on the source-facing surface `𝓢[μ, μ * Qf]¹¹`
* `IsStrongConvexSmoothObjective.translate` from `Definition_2_17`, the owner-side translation
  bridge for whole-space strongly convex smooth objectives

Source/core/bridge triage:
* source-facing: Theorem 2.14's existential lower-bound statement
* core/canonical: the owner objective `nesterovLowerBoundOperatorObjective μ Qf`, used through
  its explicit translation by the prescribed initial point `x0`
* bridge/view: packaging that translated owner objective as an existential witness `∃ f`

Best owner abstractions:
* the hard-instance objective `nesterovLowerBoundOperatorObjective μ Qf`
* the iterate-family predicate `SatisfiesSpanCondition method`

Primitive data:
* the translated owner hard-instance objective
  `fun x ↦ nesterovLowerBoundOperatorObjective μ Qf (x - x0)`
* one minimizing point `xStar`

Derived API:
* membership of the translated hard instance in `(𝓢[μ, μ * Qf]¹¹ : Set (ℝ∞ → ℝ))`
* uniqueness of the minimizer, coming from strong convexity
* the two iteratewise lower bounds for every span-condition method

Accordingly, the core theorem below is stated directly for the owner hard instance, and
Theorem 2.14 is the source-facing existential bridge obtained by packaging its explicit
translation by `x0`.
-/

/-- Helper for Theorem 2.14: the geometric ratio attached to the condition number `Q_f`. -/
private def geometricRatio (Qf : ℝ) : ℝ :=
  (Real.sqrt Qf - 1) / (Real.sqrt Qf + 1)

/-- Helper for Theorem 2.14: the geometric ratio
`q = (√Q_f - 1) / (√Q_f + 1)` lies in `(0, 1)`, and the coordinate profile
`n ↦ q^(n + 1)` defines an `ℓ²` vector. -/
-- Proof sketch: `1 < Q_f` implies `1 < √Q_f`, so the ratio is positive and strictly below `1`.
-- Then `‖q^(n+1)‖²` is a geometric series with ratio `q² < 1`, hence summable.
private theorem geometric_ratio_bounds_and_memlp
    (Qf : ℝ) (hQf : 1 < Qf) :
    0 < geometricRatio Qf ∧ geometricRatio Qf < 1 ∧
      Memℓp (fun n : ℕ ↦ geometricRatio Qf ^ (n + 1)) 2 := by
  let q := geometricRatio Qf
  have hs : 1 < Real.sqrt Qf := by
    exact (Real.lt_sqrt (show 0 ≤ (1 : ℝ) by positivity)).2 (by simpa using hQf)
  have hden : 0 < Real.sqrt Qf + 1 := by
    linarith
  have hq_pos : 0 < q := by
    -- The source ratio has positive numerator and denominator once `Q_f > 1`.
    dsimp [q, geometricRatio]
    refine div_pos ?_ hden
    linarith
  have hq_lt : q < 1 := by
    -- The numerator is strictly smaller than the denominator, so the ratio is below `1`.
    dsimp [q, geometricRatio]
    have hnum_lt_den : Real.sqrt Qf - 1 < Real.sqrt Qf + 1 := by
      linarith
    exact (div_lt_one hden).2 hnum_lt_den
  have hsum : Summable (fun n : ℕ => ‖q ^ (n + 1)‖ ^ (2 : ℝ)) := by
    have hq_sq_lt : q ^ (2 : ℕ) < 1 := by
      nlinarith [hq_pos, hq_lt]
    have hgeom : Summable (fun n : ℕ => (q ^ (2 : ℕ)) ^ (n + 1)) := by
      -- The squared coordinates form a shifted geometric series with ratio `q²`.
      refine (summable_nat_add_iff 1).2 ?_
      exact summable_geometric_of_lt_one (pow_nonneg hq_pos.le _) hq_sq_lt
    refine hgeom.congr ?_
    intro n
    have hqpow : 0 ≤ q ^ (n + 1) := pow_nonneg hq_pos.le _
    -- Normalize the `Memℓp` summand to the usual geometric term `(q²)^(n+1)`.
    have hpow : (q ^ (2 : ℕ)) ^ (n + 1) = (q ^ (n + 1)) ^ (2 : ℕ) := by
      calc
        (q ^ (2 : ℕ)) ^ (n + 1) = q ^ (2 * (n + 1)) := by
          rw [pow_mul]
        _ = q ^ ((n + 1) * 2) := by
          rw [Nat.mul_comm]
        _ = (q ^ (n + 1)) ^ (2 : ℕ) := by
          rw [pow_mul]
    simpa [Real.norm_eq_abs, abs_of_nonneg hq_pos.le, abs_of_nonneg hqpow] using hpow
  exact ⟨hq_pos, hq_lt, memℓp_gen hsum⟩

/-- Helper for Theorem 2.14: the geometric minimizer profile `n ↦ q^(n+1)` as an `ℓ²` vector. -/
private def geometricPoint (Qf : ℝ) (hQf : 1 < Qf) : ℝ∞ :=
  ⟨fun n : ℕ ↦ geometricRatio Qf ^ (n + 1), (geometric_ratio_bounds_and_memlp Qf hQf).2.2⟩

/-- Helper for Theorem 2.14: the geometric ratio satisfies the stationary-system scalar identity
`4 q / (Q_f - 1) = (1 - q)^2`. -/
-- Proof sketch: write `q = (s - 1) / (s + 1)` with `s = √Q_f`, rewrite `Q_f` as `s²`, and clear
-- denominators. The result is the algebraic normalization used in the coordinatewise stationary
-- equations.
private theorem geometric_ratio_scaled_identity
    (Qf : ℝ) (hQf : 1 < Qf) :
    4 * geometricRatio Qf / (Qf - 1) = (1 - geometricRatio Qf) ^ (2 : ℕ) := by
  let s := Real.sqrt Qf
  have hs_gt1 : 1 < s := by
    dsimp [s]
    exact (Real.lt_sqrt (show 0 ≤ (1 : ℝ) by positivity)).2 (by simpa using hQf)
  have hs_nonneg : 0 ≤ s := le_of_lt (lt_trans zero_lt_one hs_gt1)
  have hs_ne : s + 1 ≠ 0 := by
    linarith
  have hs_sq : s ^ 2 = Qf := by
    dsimp [s]
    nlinarith [Real.sq_sqrt (show 0 ≤ Qf by linarith)]
  have hs_sq_sub_ne : s ^ 2 - 1 ≠ 0 := by
    nlinarith
  have hsqrtsq : Real.sqrt (s ^ 2) = s := by
    simpa [abs_of_nonneg hs_nonneg] using Real.sqrt_sq_eq_abs s
  simp [geometricRatio]
  rw [← hs_sq, hsqrtsq]
  field_simp [hs_ne, hs_sq_sub_ne]
  ring

/-- Helper for Theorem 2.14: the geometric profile `n ↦ q^(n+1)` is the global minimizer of the
untranslated lower-bound objective. -/
-- Proof sketch: place the geometric point in `ℓ²`, verify that it solves the stationary linear
-- system from Proposition 2.7 coordinatewise, and then invoke the Proposition 2.7 equivalence
-- between stationarity and global minimality.
private theorem geometric_point_isMinOn_lower_bound_objective
    (μ Qf : ℝ) (hμ : 0 < μ) (hQf : 1 < Qf) :
    IsMinOn (nesterovLowerBoundOperatorObjective μ Qf) Set.univ (geometricPoint Qf hQf) := by
  have hlinear :
      (nesterovLowerBoundTridiagonalOperator +
          (4 / (Qf - 1)) • ContinuousLinearMap.id ℝ ℝ∞) (geometricPoint Qf hQf) =
        lp.single 2 0 (1 : ℝ) := by
    -- The geometric profile solves the Proposition 2.7 stationary system coordinatewise.
    ext n
    cases n with
    | zero =>
        have hscaled := geometric_ratio_scaled_identity Qf hQf
        have hscaled' :
            (4 / (Qf - 1)) * geometricRatio Qf = (1 - geometricRatio Qf) ^ (2 : ℕ) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
        have hhead :
            2 * geometricRatio Qf - geometricRatio Qf ^ (2 : ℕ) +
                (4 / (Qf - 1)) * geometricRatio Qf =
              1 := by
          rw [hscaled']
          ring
        change
          nesterovLowerBoundTridiagonalOperator (geometricPoint Qf hQf) 0 +
              ((4 / (Qf - 1)) • geometricPoint Qf hQf) 0 =
            1
        simpa [geometricPoint, nesterovLowerBoundTridiagonalOperator_apply_zero, pow_two] using
          hhead
    | succ n =>
        have hscaled := geometric_ratio_scaled_identity Qf hQf
        have hscaled' :
            (4 / (Qf - 1)) * geometricRatio Qf = (1 - geometricRatio Qf) ^ (2 : ℕ) := by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
        have htail :
            -geometricRatio Qf ^ (n + 1) + 2 * geometricRatio Qf ^ (n + 2) -
                geometricRatio Qf ^ (n + 3) +
                (4 / (Qf - 1)) * geometricRatio Qf ^ (n + 2) =
              0 := by
          have hcoeff :
              -1 + 2 * geometricRatio Qf - geometricRatio Qf ^ (2 : ℕ) +
                  (4 / (Qf - 1)) * geometricRatio Qf =
                0 := by
            rw [hscaled']
            ring
          calc
            -geometricRatio Qf ^ (n + 1) + 2 * geometricRatio Qf ^ (n + 2) -
                geometricRatio Qf ^ (n + 3) +
                (4 / (Qf - 1)) * geometricRatio Qf ^ (n + 2) =
                  geometricRatio Qf ^ (n + 1) *
                    (-1 + 2 * geometricRatio Qf - geometricRatio Qf ^ (2 : ℕ) +
                      (4 / (Qf - 1)) * geometricRatio Qf) := by
                  rw [show n + 2 = (n + 1) + 1 by omega, pow_add,
                    show n + 3 = (n + 1) + 2 by omega, pow_add]
                  ring
            _ = 0 := by rw [hcoeff]; ring
        change
          nesterovLowerBoundTridiagonalOperator (geometricPoint Qf hQf) (n + 1) +
              ((4 / (Qf - 1)) • geometricPoint Qf hQf) (n + 1) =
            0
        simpa [geometricPoint, nesterovLowerBoundTridiagonalOperator_apply_succ, lp.single] using
          htail
  have hgrad_zero :
      ∇ (nesterovLowerBoundOperatorObjective μ Qf) (geometricPoint Qf hQf) = 0 := by
    -- Proposition 2.7 turns the stationary linear system into gradient vanishing.
    rw [nesterovLowerBoundOperatorObjective_gradient_eq_zero_iff_linear_system μ Qf hμ hQf]
    exact hlinear
  -- The owner minimizer criterion now closes the untranslated hard-instance proof.
  rw [nesterovLowerBoundOperatorObjective_isMinOn_iff_gradient_eq_zero μ Qf hμ hQf.le]
  exact hgrad_zero

-- The remaining gradient computation is organized in three stable stages: first isolate the
-- tridiagonal coordinate, then package the full affine expression, and finally specialize the
-- vector-valued gradient formula.
/-- Helper for Theorem 2.14: scaling the tridiagonal operator scales each successor coordinate by
the same scalar. -/
-- Proof sketch: evaluate the scaled operator at `x`, rewrite the scalar action on the resulting
-- `ℓ²` vector, and then read off the successor coordinate using the tridiagonal coordinate
-- formula.
private theorem scaled_tridiagonal_coordinate_apply_succ
    (a : ℝ) (x : ℝ∞) (n : ℕ) :
    (((a • nesterovLowerBoundTridiagonalOperator) x) (n + 1)) =
      a * (-x n + 2 * x (n + 1) - x (n + 2)) := by
  have hsmul :
      (a • nesterovLowerBoundTridiagonalOperator) x =
        a • nesterovLowerBoundTridiagonalOperator x := by
    rw [ContinuousLinearMap.smul_apply]
  rw [hsmul]
  -- Rewrite the scalar action on the `ℓ²` vector before exposing the tridiagonal coordinate.
  change a * nesterovLowerBoundTridiagonalOperator x (n + 1) = _
  rw [nesterovLowerBoundTridiagonalOperator_apply_succ]

/-- Helper for Theorem 2.14: the affine gradient expression from Proposition 2.7 has the expected
successor-coordinate form. -/
-- Proof sketch: expand the affine map at `x`, use the previous tridiagonal-coordinate adapter for
-- the operator term, rewrite the identity term coordinatewise, and note that the `e₁` term
-- vanishes at every successor coordinate.
private theorem lower_bound_gradient_affine_apply_succ
    (μ Qf : ℝ) (x : ℝ∞) (n : ℕ) :
    (((((μ * (Qf - 1) / 4) • nesterovLowerBoundTridiagonalOperator) + μ • I∞) x -
        (μ * (Qf - 1) / 4) • e1) (n + 1)) =
      (μ * (Qf - 1) / 4) * (-x n + 2 * x (n + 1) - x (n + 2)) + μ * x (n + 1) := by
  let c : ℝ := μ * (Qf - 1) / 4
  have hadd :
      (((c • nesterovLowerBoundTridiagonalOperator) + μ • I∞) x) =
        (c • nesterovLowerBoundTridiagonalOperator) x + (μ • I∞) x := by
    rw [ContinuousLinearMap.add_apply]
  have hid : (μ • I∞) x = μ • x := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  rw [show (((((μ * (Qf - 1) / 4) • nesterovLowerBoundTridiagonalOperator) + μ • I∞) x -
        (μ * (Qf - 1) / 4) • e1) (n + 1)) =
      ((((c • nesterovLowerBoundTridiagonalOperator) + μ • I∞) x - c • e1) (n + 1)) by
      rfl]
  rw [hadd, hid]
  -- Evaluate the affine expression coordinatewise and separate the vanishing `e₁` tail term.
  change
    (((c • nesterovLowerBoundTridiagonalOperator) x) (n + 1) + (μ • x) (n + 1) -
        (c • e1) (n + 1)) =
      _
  rw [scaled_tridiagonal_coordinate_apply_succ c x n]
  change c * (-x n + 2 * x (n + 1) - x (n + 2)) + μ * x (n + 1) - (c • e1) (n + 1) = _
  have he1 : (c • e1) (n + 1) = 0 := by
    change (c • (lp.single 2 0 (1 : ℝ) : ℝ∞)) (n + 1) = 0
    simp
  rw [he1]
  simp [c]

/-- Helper for Theorem 2.14: every successor coordinate of the lower-bound gradient has the
tridiagonal form from Proposition 2.7. -/
-- Proof sketch: specialize the explicit gradient formula from Proposition 2.7 at coordinate
-- `n + 1`; the `lp.single` term vanishes there, so only the tridiagonal coordinate and the
-- diagonal `μ x_{n+1}` term remain.
private theorem lower_bound_gradient_apply_succ
    (μ Qf : ℝ) (x : ℝ∞) (n : ℕ) :
    ∇ (nesterovLowerBoundOperatorObjective μ Qf) x (n + 1) =
      (μ * (Qf - 1) / 4) * (-x n + 2 * x (n + 1) - x (n + 2)) + μ * x (n + 1) := by
  have hcoord := congrArg (fun y : ℝ∞ ↦ y (n + 1))
    (nesterovLowerBoundOperatorObjective_gradient_eq μ Qf x)
  -- Route correction: first pass to the successor coordinate, then invoke the affine adapter.
  simpa using hcoord.trans (lower_bound_gradient_affine_apply_succ μ Qf x n)

/-- Helper for Theorem 2.14: translating the hard instance by `x₀` shifts gradient evaluation
from `x` to `x - x₀`. -/
-- Proof sketch: differentiate the untranslated objective at `x - x₀`, compose with the ambient
-- translation map, and read off the translated gradient by uniqueness.
private theorem translated_nesterovLowerBoundOperatorObjective_gradient_eq
    (x0 : ℝ∞) (μ Qf : ℝ) (hμ : 0 < μ) (hQf : 1 < Qf) (x : ℝ∞) :
    ∇ (fun y ↦ nesterovLowerBoundOperatorObjective μ Qf (y - x0)) x =
      ∇ (nesterovLowerBoundOperatorObjective μ Qf) (x - x0) := by
  let g : ℝ∞ → ℝ := nesterovLowerBoundOperatorObjective μ Qf
  have hg : ContDiff ℝ 1 g := by
    exact (mem_S11_iff.mp (nesterovLowerBoundOperatorObjective_mem_S11 μ Qf hμ hQf.le)).contDiff
  -- Compose the owner objective with the affine translation `y ↦ y - x₀`.
  have hx : HasGradientAt g (∇ g (x - x0)) (x - x0) :=
    hg.differentiable_one (x - x0) |>.hasGradientAt
  have hsub : HasFDerivAt (fun y : ℝ∞ ↦ y - x0) (ContinuousLinearMap.id ℝ ℝ∞) x := by
    simpa using (hasFDerivAt_id x).sub_const x0
  have htranslate : HasGradientAt (fun y : ℝ∞ ↦ g (y - x0)) (∇ g (x - x0)) x := by
    simpa [g, Function.comp_def] using (hx.hasFDerivAt.comp x hsub).hasGradientAt
  simpa [g] using htranslate.gradient

/-- Helper for Theorem 2.14: if an untranslated point vanishes from index `j` onward, then the
gradient vanishes from index `j + 1` onward. -/
-- Proof sketch: use the explicit tridiagonal gradient formula from Proposition 2.7. Every tail
-- coordinate `n + 1` depends only on the three neighboring coordinates `n`, `n + 1`, and
-- `n + 2`, so a zero tail propagates one step forward.
private theorem lower_bound_gradient_eq_zero_of_zero_tail
    (μ Qf : ℝ) {j n : ℕ} (hjn : j ≤ n)
    {x : ℝ∞} (hx : ∀ m : ℕ, j ≤ m → x m = 0) :
    ∇ (nesterovLowerBoundOperatorObjective μ Qf) x (n + 1) = 0 := by
  have hxn : x n = 0 := hx n hjn
  have hxn1 : x (n + 1) = 0 := hx (n + 1) (Nat.le_trans hjn (Nat.le_succ n))
  have hxn2 : x (n + 2) = 0 := by
    exact hx (n + 2) (Nat.le_trans hjn (Nat.le_succ_of_le (Nat.le_succ n)))
  -- The successor-coordinate formula only sees three tail coordinates, all of which vanish.
  rw [lower_bound_gradient_apply_succ μ Qf x n]
  simp [hxn, hxn1, hxn2]

/-- Helper for Theorem 2.14: the translated hard-instance gradient has the same one-step tail
propagation as the untranslated objective. -/
-- Proof sketch: first rewrite the translated gradient as the untranslated gradient at `x - x₀`,
-- then apply the previous zero-tail propagation lemma.
private theorem translated_lower_bound_gradient_eq_zero_of_zero_tail
    (x0 : ℝ∞) (μ Qf : ℝ) (hμ : 0 < μ) (hQf : 1 < Qf)
    {j n : ℕ} (hjn : j ≤ n) {x : ℝ∞}
    (hx : ∀ m : ℕ, j ≤ m → (x - x0) m = 0) :
    ∇ (fun y ↦ nesterovLowerBoundOperatorObjective μ Qf (y - x0)) x (n + 1) = 0 := by
  rw [translated_nesterovLowerBoundOperatorObjective_gradient_eq x0 μ Qf hμ hQf x]
  exact lower_bound_gradient_eq_zero_of_zero_tail μ Qf hjn hx

/-- Helper for Theorem 2.14: every span-condition iterate difference for the translated hard
instance has a zero tail past its iterate index. -/
-- Proof sketch: induct on the iterate index. The span condition writes the next iterate
-- difference as a linear combination of earlier gradients, and the translated gradient-support
-- lemma shows that each earlier gradient already vanishes in the required tail coordinate.
private theorem span_condition_iterate_sub_eq_zero_of_ge
    (x0 : ℝ∞) (μ Qf : ℝ) (hμ : 0 < μ) (hQf : 1 < Qf)
    (method : (ℝ∞ → ℝ) → ℝ∞ → ℕ → ℝ∞) (hmethod : SatisfiesSpanCondition method) :
    ∀ {j n : ℕ},
      j ≤ n →
        (method (fun x ↦ nesterovLowerBoundOperatorObjective μ Qf (x - x0)) x0 j - x0) n = 0 := by
  let f : ℝ∞ → ℝ := fun x ↦ nesterovLowerBoundOperatorObjective μ Qf (x - x0)
  have hf_mem : f ∈ 𝓢[μ, μ * Qf]¹¹ := by
    exact mem_S11_iff.mpr
      ((mem_S11_iff.mp (nesterovLowerBoundOperatorObjective_mem_S11 μ Qf hμ hQf.le)).translate x0)
  have hf : ContDiff ℝ 1 f := (mem_S11_iff.mp hf_mem).contDiff
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro n hjn
      cases j with
      | zero =>
          -- The span condition fixes the zeroth iterate at the initialization point.
          have hzero : method f x0 0 = x0 :=
            SatisfiesSpanCondition.zero_eq hmethod f hf x0
          have hzero' :
              method (fun x ↦ nesterovLowerBoundOperatorObjective μ Qf (x - x0)) x0 0 = x0 := by
            simpa [f] using hzero
          change method (fun x ↦ nesterovLowerBoundOperatorObjective μ Qf (x - x0)) x0 0 n - x0 n = 0
          rw [hzero']
          ring
      | succ j =>
          have hspan :
              method f x0 (j + 1) - x0 ∈
                Submodule.span ℝ (Set.range fun i : Fin (j + 1) ↦ ∇ f (method f x0 i)) :=
            SatisfiesSpanCondition.sub_mem_span hmethod f hf x0 (j + 1)
          have hgenerator :
              ∀ i : Fin (j + 1), (∇ f (method f x0 i)) n = 0 := by
            intro i
            cases n with
            | zero =>
                cases (Nat.not_succ_le_zero j hjn)
            | succ m =>
                have hi_lt : i.1 < j + 1 := i.2
                have hi_le : i.1 ≤ m := by
                  omega
                have htail :
                    ∀ t : ℕ, i.1 ≤ t → (method f x0 i.1 - x0) t = 0 := by
                  intro t hit
                  exact ih i.1 hi_lt (n := t) hit
                -- Earlier iterate differences already have zero tail, so their gradients vanish
                -- one coordinate later.
                simpa [f] using
                  translated_lower_bound_gradient_eq_zero_of_zero_tail
                    x0 μ Qf hμ hQf (j := i.1) (n := m) hi_le
                    (x := method f x0 i.1) htail
          -- The next iterate difference lies in the span of generators whose `n`th coordinate
          -- already vanishes, so the same holds for the whole span element.
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hspan
          · intro z hz
            rcases hz with ⟨i, rfl⟩
            exact hgenerator i
          · rfl
          · intro a b ha hb ha_zero hb_zero
            change a n + b n = 0
            simp [ha_zero, hb_zero]
          · intro c z hz hz_zero
            change c * z n = 0
            simp [hz_zero]

/-- Helper for Theorem 2.14: the geometric minimizer tail from index `k` onward is exactly
`q^(2k)` times the full squared norm. -/
-- Proof sketch: rewrite the squared norm of `geometricPoint Q_f` as the geometric series
-- `∑ q^(2(n+1))`, then shift the index by `k` and factor out the common multiplier `q^(2k)`.
private theorem geometric_tail_sqnorm_shift
    (Qf : ℝ) (hQf : 1 < Qf) (k : ℕ) :
    ∑' n : ℕ, ‖geometricPoint Qf hQf (n + k)‖ ^ (2 : ℕ) =
      geometricRatio Qf ^ (2 * k) * ‖geometricPoint Qf hQf‖ ^ (2 : ℕ) := by
  let q := geometricRatio Qf
  have hq_pos : 0 < q := (geometric_ratio_bounds_and_memlp Qf hQf).1
  calc
    ∑' n : ℕ, ‖geometricPoint Qf hQf (n + k)‖ ^ (2 : ℕ) =
        ∑' n : ℕ, geometricRatio Qf ^ (2 * k) * ‖geometricPoint Qf hQf n‖ ^ (2 : ℕ) := by
          refine tsum_congr ?_
          intro n
          -- Factor the fixed prefix `q^k` out of each shifted coordinate.
          simp only [Real.norm_eq_abs]
          dsimp [geometricPoint]
          rw [abs_of_nonneg (pow_nonneg hq_pos.le _), abs_of_nonneg (pow_nonneg hq_pos.le _)]
          change (q ^ (n + k + 1)) ^ (2 : ℕ) = q ^ (2 * k) * (q ^ (n + 1)) ^ (2 : ℕ)
          rw [show n + k + 1 = k + (n + 1) by omega, pow_add]
          ring_nf
    _ = geometricRatio Qf ^ (2 * k) * ∑' n : ℕ, ‖geometricPoint Qf hQf n‖ ^ (2 : ℕ) := by
          rw [tsum_mul_left]
    _ = geometricRatio Qf ^ (2 * k) * ‖geometricPoint Qf hQf‖ ^ (2 : ℕ) := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            congrArg (fun t : ℝ => geometricRatio Qf ^ (2 * k) * t)
              (lp.norm_rpow_eq_tsum (by norm_num) (geometricPoint Qf hQf)).symm

/-- Helper for Theorem 2.14: translating a minimizer of the untranslated hard instance by `x₀`
gives a minimizer of the translated objective. -/
-- Proof sketch: rewrite the translated objective at `x` as the untranslated objective at
-- `x - x₀`, then reuse the minimizing property of `zStar`.
private theorem lower_bound_objective_translate_isMinOn
    (x0 : ℝ∞) (μ Qf : ℝ) {zStar : ℝ∞}
    (hzStar : IsMinOn (nesterovLowerBoundOperatorObjective μ Qf) Set.univ zStar) :
    IsMinOn (fun x ↦ nesterovLowerBoundOperatorObjective μ Qf (x - x0)) Set.univ (x0 + zStar) := by
  rw [isMinOn_univ_iff]
  intro x
  rw [isMinOn_univ_iff] at hzStar
  -- Translating the argument reduces the minimizer comparison to the untranslated objective.
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzStar (x - x0)

/-- Helper for Theorem 2.14: a vector whose coordinates vanish from `k` onward stays at least the
geometric tail norm away from the geometric minimizer profile. -/
-- Proof sketch: identify the tail coordinates of `y - zStar` with `-zStar`, drop the nonnegative
-- head terms from the `ℓ²` norm series, and factor the remaining geometric tail as
-- `q^(2k) ‖zStar‖²`.
private theorem geometric_tail_sqdist_lower_bound_of_zero_tail
    (Qf : ℝ) (hQf : 1 < Qf) :
    ∀ {k : ℕ} {y : ℝ∞}, (∀ n : ℕ, k ≤ n → y n = 0) →
      geometricRatio Qf ^ (2 * k) * ‖geometricPoint Qf hQf‖ ^ (2 : ℕ) ≤
        ‖y - geometricPoint Qf hQf‖ ^ (2 : ℕ) := by
  intro k y hy
  let head : ℝ := Finset.sum (Finset.range k) fun i => ‖(y - geometricPoint Qf hQf) i‖ ^ (2 : ℕ)
  let tail : ℝ := ∑' n : ℕ, ‖(y - geometricPoint Qf hQf) (n + k)‖ ^ (2 : ℕ)
  have hsum : Summable (fun n : ℕ => ‖(y - geometricPoint Qf hQf) n‖ ^ (2 : ℕ)) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (lp.memℓp (y - geometricPoint Qf hQf)).summable (by norm_num)
  have htail_eq :
      tail = ∑' n : ℕ, ‖geometricPoint Qf hQf (n + k)‖ ^ (2 : ℕ) := by
    dsimp [tail]
    refine tsum_congr ?_
    intro n
    have hy_tail : y (n + k) = 0 := hy (n + k) (by omega)
    have hcoord : (y - geometricPoint Qf hQf) (n + k) = -geometricPoint Qf hQf (n + k) := by
      change y (n + k) - geometricPoint Qf hQf (n + k) = -geometricPoint Qf hQf (n + k)
      rw [hy_tail]
      ring
    have hcoord_sq :
        ((y - geometricPoint Qf hQf) (n + k)) ^ (2 : ℕ) =
          (geometricPoint Qf hQf (n + k)) ^ (2 : ℕ) := by
      rw [hcoord]
      ring
    -- On the tail, the iterate vanishes, so the distance coordinate is exactly `-z*`.
    simpa [Real.norm_eq_abs, sq_abs] using hcoord_sq
  have hhead_nonneg : 0 ≤ head := by
    dsimp [head]
    exact Finset.sum_nonneg fun i _ ↦ by positivity
  have hnorm :
      ‖y - geometricPoint Qf hQf‖ ^ (2 : ℕ) =
        ∑' x : ℕ, ‖(y - geometricPoint Qf hQf) x‖ ^ (2 : ℕ) := by
    simpa using (lp.norm_rpow_eq_tsum (by norm_num) (y - geometricPoint Qf hQf))
  have hsplit : head + tail = ‖y - geometricPoint Qf hQf‖ ^ (2 : ℕ) := by
    calc
      head + tail =
          ∑' x : ℕ, ‖(y - geometricPoint Qf hQf) x‖ ^ (2 : ℕ) := by
            dsimp [head, tail]
            simpa using (hsum.sum_add_tsum_nat_add k)
      _ = ‖y - geometricPoint Qf hQf‖ ^ (2 : ℕ) := by
            exact hnorm.symm
  have htail_le :
      tail ≤ ‖y - geometricPoint Qf hQf‖ ^ (2 : ℕ) := by
    have hle : tail ≤ head + tail := by
      linarith
    exact hle.trans_eq hsplit
  calc
    geometricRatio Qf ^ (2 * k) * ‖geometricPoint Qf hQf‖ ^ (2 : ℕ) = tail := by
      rw [htail_eq]
      symm
      exact geometric_tail_sqnorm_shift Qf hQf k
    _ ≤ ‖y - geometricPoint Qf hQf‖ ^ (2 : ℕ) := htail_le

/-- Core/canonical form of Theorem 2.14: after translating the chapter owner objective
`nesterovLowerBoundOperatorObjective μ Qf` so that the prescribed initial point is `x₀`, the full
owner data consist of objective-class membership together with one minimizing point realizing the
lower bounds. -/
-- Proof sketch: translate the canonical lower-bound objective from `Proposition_2_7` by `x0`.
-- The translated objective stays in `𝓢[μ, μ * Qf]¹¹`, and its minimizing point has the same
-- geometric-tail profile as the canonical one, so any span-condition method stays at distance at
-- least `q^k ‖x₀ - x*‖` from that minimizer at step `k`. The owner strong convexity then upgrades
-- the distance estimate to the objective-gap estimate.
theorem nesterovLowerBoundOperatorObjective_translate_with_firstOrder_lower_bound
    (x0 : ℝ∞) (μ Qf : ℝ) (hμ : 0 < μ) (hQf : 1 < Qf) :
    let q := (Real.sqrt Qf - 1) / (Real.sqrt Qf + 1)
    let f : ℝ∞ → ℝ := fun x ↦ nesterovLowerBoundOperatorObjective μ Qf (x - x0)
    f ∈ 𝓢[μ, μ * Qf]¹¹ ∧
      ∃ xStar : ℝ∞,
        IsMinOn f Set.univ xStar ∧
          ∀ method : (ℝ∞ → ℝ) → ℝ∞ → ℕ → ℝ∞,
            SatisfiesSpanCondition method →
              ∀ k : ℕ,
                let xk := method f x0 k
                q ^ (2 * k) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤ ‖xk - xStar‖ ^ (2 : ℕ) ∧
                  (μ / 2) * q ^ (2 * k) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤
                    f xk - f xStar := by
  dsimp
  let q := (Real.sqrt Qf - 1) / (Real.sqrt Qf + 1)
  let zStar : ℝ∞ := ⟨fun n : ℕ ↦ q ^ (n + 1), (geometric_ratio_bounds_and_memlp Qf hQf).2.2⟩
  let f : ℝ∞ → ℝ := fun x ↦ nesterovLowerBoundOperatorObjective μ Qf (x - x0)
  let xStar : ℝ∞ := x0 + zStar
  have hf0 :
      IsStrongConvexSmoothObjective μ (μ * Qf) (nesterovLowerBoundOperatorObjective μ Qf) :=
    mem_S11_iff.mp (nesterovLowerBoundOperatorObjective_mem_S11 μ Qf hμ hQf.le)
  have hf : f ∈ 𝓢[μ, μ * Qf]¹¹ := by
    exact mem_S11_iff.mpr (hf0.translate x0)
  have hzStar :
      IsMinOn (nesterovLowerBoundOperatorObjective μ Qf) Set.univ zStar := by
    simpa [q, zStar] using geometric_point_isMinOn_lower_bound_objective μ Qf hμ hQf
  have hxStar : IsMinOn f Set.univ xStar := by
    simpa [f, xStar, zStar] using lower_bound_objective_translate_isMinOn x0 μ Qf hzStar
  refine ⟨hf, xStar, hxStar, ?_⟩
  intro method hmethod k
  let xk : ℝ∞ := method f x0 k
  have htail : ∀ n : ℕ, k ≤ n → (xk - x0) n = 0 := by
    intro n hkn
    simpa [xk, f] using
      span_condition_iterate_sub_eq_zero_of_ge x0 μ Qf hμ hQf method hmethod (j := k) hkn
  have hdist_shift :
      q ^ (2 * k) * ‖zStar‖ ^ (2 : ℕ) ≤ ‖(xk - x0) - zStar‖ ^ (2 : ℕ) := by
    simpa [q, zStar] using geometric_tail_sqdist_lower_bound_of_zero_tail Qf hQf htail
  have hx0dist : ‖x0 - xStar‖ ^ (2 : ℕ) = ‖zStar‖ ^ (2 : ℕ) := by
    simp [xStar, zStar, sub_eq_add_neg, add_comm]
  have hxkdist : ‖xk - xStar‖ ^ (2 : ℕ) = ‖(xk - x0) - zStar‖ ^ (2 : ℕ) := by
    simp [xk, xStar, zStar, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  constructor
  · -- The iterate has a zero tail from index `k` onward, so its distance to the geometric
    -- minimizer controls the full translated distance.
    rw [hx0dist, hxkdist]
    exact hdist_shift
  · -- Strong convexity upgrades the distance lower bound to the objective-gap lower bound.
    have hdist :
        q ^ (2 * k) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤ ‖xk - xStar‖ ^ (2 : ℕ) := by
      rw [hx0dist, hxkdist]
      exact hdist_shift
    have hquad :
        f xk ≥ f xStar + (μ / 2) * ‖xk - xStar‖ ^ (2 : ℕ) :=
      (mem_S11_iff.mp hf).strongConvexOn.quadratic_growth_of_isMinOn hxStar xk
    nlinarith [hμ, hdist, hquad]

/-- Theorem 2.14: for every initial point `x₀ ∈ ℝ∞`, every `μ > 0`, and every condition number
`Q_f > 1`, setting `L := μ Q_f` and
`q := (√Q_f - 1) / (√Q_f + 1)`, there exists a function
`f ∈ 𝓢^{∞,1}_{μ,L}(ℝ∞)` together with a minimizing point `x*`; uniqueness of the minimizer is a
derived consequence of strong convexity, so the statement is expressed with `IsMinOn` rather than
a separate uniqueness wrapper. Every first-order method satisfying Assumption 2.1.4 obeys the
geometric lower bounds `‖x_k - x*‖² ≥ q^(2k) ‖x₀ - x*‖²` and
`f(x_k) - f(x*) ≥ (μ / 2) q^(2k) ‖x₀ - x*‖²` for all `k ≥ 0`. -/
-- Proof sketch: use Nesterov's quadratic hard instance on `ℓ²(ℕ, ℝ)` with condition number
-- `Qf`, then translate it so that the prescribed initial point is `x0`. The span condition forces
-- the `k`-th iterate to lie in the subspace generated by the first `k` coordinates, while the
-- optimizer has a geometric tail of ratio `q`; the tail norm yields the distance lower bound, and
-- strong convexity upgrades it to the objective lower bound.
theorem exists_rinfty_hard_instance_with_firstOrder_lower_bound
    (x0 : ℝ∞) (μ Qf : ℝ) (hμ : 0 < μ) (hQf : 1 < Qf) :
    let L := μ * Qf
    let q := (Real.sqrt Qf - 1) / (Real.sqrt Qf + 1)
    ∃ f : ℝ∞ → ℝ,
      ∃ xStar : ℝ∞,
          f ∈ 𝓢[μ, L]¹¹ ∧
          IsMinOn f Set.univ xStar ∧
          ∀ method : (ℝ∞ → ℝ) → ℝ∞ → ℕ → ℝ∞,
            SatisfiesSpanCondition method →
              ∀ k : ℕ,
                let xk := method f x0 k
                q ^ (2 * k) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤ ‖xk - xStar‖ ^ (2 : ℕ) ∧
                  (μ / 2) * q ^ (2 * k) * ‖x0 - xStar‖ ^ (2 : ℕ) ≤
                    f xk - f xStar := by
  dsimp
  rcases
      nesterovLowerBoundOperatorObjective_translate_with_firstOrder_lower_bound
        x0 μ Qf hμ hQf with
    ⟨hf, xStar, hxStar, hlower⟩
  exact ⟨_, xStar, hf, hxStar, hlower⟩

end
