/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_5_6

noncomputable section

open Filter
open scoped Topology

section NegativeCurvatureDirectionMethod

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling pass:
-- * primary domain: smooth unconstrained optimization with negative-curvature backtracking
--   line search on a real Hilbert space;
-- * sampled owner declarations in this domain:
--   `negativeCurvatureLevelSet` and `IsNegativeCurvatureLineSearchSequence` from
--   `Theorem_3_5_6`,
--   and `IsDescentPairAt.inner_left_nonpos` / `IsDescentPairAt.hessianQuadratic_nonpos` from
--   `Definition_3_5_1`;
-- * owner abstraction used here: the canonical sequence owner from `Theorem_3_5_6`;
-- * primitive data added by Theorem 3.5.8: only the quantitative bounds `(3.5.47)` and
--   `(3.5.48)`;
-- * derived API: the two norm-convergence consequences `s_k → 0` and `d_k → 0`.

private theorem tendsto_zero_of_mul_sq_le_of_tendsto_zero
    {a : ℝ} (ha : 0 < a) {u v : ℕ → ℝ}
    (hbound : ∀ k, a * u k ^ 2 ≤ v k)
    (hv : Tendsto v atTop (nhds 0)) :
    Tendsto u atTop (nhds 0) := by
  have hau_sq : Tendsto (fun k ↦ a * u k ^ 2) atTop (nhds 0) := by
    refine squeeze_zero ?_ hbound hv
    intro k
    positivity
  have hu_sq : Tendsto (fun k ↦ u k ^ 2) atTop (nhds 0) := by
    simpa [one_div, ha.ne', mul_assoc] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ 1 / a) atTop (nhds (1 / a))).mul hau_sq)
  have hu_abs : Tendsto (fun k ↦ |u k|) atTop (nhds 0) := by
    simpa [Real.sqrt_sq_eq_abs] using Filter.Tendsto.sqrt hu_sq
  exact (tendsto_zero_iff_abs_tendsto_zero _).2 hu_abs

variable (D : Set E) (f : E → ℝ) (x s d : ℕ → E) (backtrackingExponent : ℕ → ℕ)
  (x₀ : E) (ρ γ : ℝ)
variable (hD : IsOpen D) (hC2 : ContDiffOn ℝ 2 f D)
variable (hLevelSetCompact : IsCompact (negativeCurvatureLevelSet D f x₀))
variable (hx_mem : ∀ k, x k ∈ D)
variable (hs_bounded : Bornology.IsBounded (Set.range s))
variable (hd_bounded : Bornology.IsBounded (Set.range d))
variable (hLineSearch :
  IsNegativeCurvatureLineSearchSequence f x s d backtrackingExponent x₀ ρ γ)
variable (hDescentPair : ∀ k, IsDescentPairAt f (x k) (s k) (d k))

include D f x s d backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair

/-- Chapter03 Theorem 3.5.8 (1): formalized on a real inner product space `E`, assume
`f` has two continuous derivatives on the open set `D`, and the level set
`{x ∈ D | f x ≤ f x₀}` is compact.
If a source-faithful run of the negative-curvature direction method satisfies the
additional quantitative bounds `(3.5.47)` and `(3.5.48)`, then `s_k → 0`. -/
theorem negativeCurvatureDirectionMethod_s_tendsto_zero
    (c₁ : ℝ)
    (hc₁ : 0 < c₁)
    (hDescentLowerBound :
      ∀ k, c₁ * ‖s k‖ ^ 2 ≤ -inner ℝ (s k) (gradient f (x k))) :
    Tendsto s atTop (nhds 0) := by
  have hpair :
      Tendsto (fun k ↦ inner ℝ (s k) (gradient f (x k))) atTop (nhds 0) :=
    negativeCurvatureDirectionMethod_gradientPairing_tendsto_zero
      D f x s d backtrackingExponent x₀ ρ γ
      hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  have hs_norm :
      Tendsto (fun k ↦ ‖s k‖) atTop (nhds 0) :=
    tendsto_zero_of_mul_sq_le_of_tendsto_zero hc₁
      hDescentLowerBound
      (by simpa using hpair.neg)
  exact tendsto_zero_iff_norm_tendsto_zero.2 hs_norm

/-- Chapter03 Theorem 3.5.8 (2): under the same hypotheses, `d_k → 0`. -/
theorem negativeCurvatureDirectionMethod_d_tendsto_zero
    (c₂ : ℝ)
    (hc₂ : 0 < c₂)
    (hCurvatureUpperBound :
      ∀ k, hessianQuadraticAt f (x k) (d k) ≤ -c₂ * ‖d k‖ ^ 2) :
    Tendsto d atTop (nhds 0) := by
  have hcurvature :
      Tendsto (fun k ↦ hessianQuadraticAt f (x k) (d k)) atTop (nhds 0) :=
    negativeCurvatureDirectionMethod_curvature_tendsto_zero
      D f x s d backtrackingExponent x₀ ρ γ
      hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair
  have hd_norm :
      Tendsto (fun k ↦ ‖d k‖) atTop (nhds 0) :=
    tendsto_zero_of_mul_sq_le_of_tendsto_zero hc₂
      (fun k ↦ by
        have hk := hCurvatureUpperBound k
        have hk' := neg_le_neg hk
        simpa [neg_mul] using hk')
      (by simpa using hcurvature.neg)
  exact tendsto_zero_iff_norm_tendsto_zero.2 hd_norm

omit D f x s d backtrackingExponent x₀ ρ γ
  hD hC2 hLevelSetCompact hx_mem hs_bounded hd_bounded hLineSearch hDescentPair

end NegativeCurvatureDirectionMethod
