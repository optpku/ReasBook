/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_8
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_7

noncomputable section

open ProperCone
open scoped Gradient HessianLocalNorm

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

noncomputable local instance instLocalChap05_Theorem_5_4_6_121 : SeminormedAddCommGroup (E₂ × E₃) :=
  WithLp.seminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_122 : NormedAddCommGroup (E₂ × E₃) :=
  WithLp.normedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_123 : NormedSpace ℝ (E₂ × E₃) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instInnerProductSpaceChap05_Theorem_5_4_6_121 : InnerProductSpace ℝ (E₂ × E₃) where
  inner x y := inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  norm_sq_eq_re_inner x := by
    rw [WithLp.norm_seminormedAddCommGroupToProd 2 E₂ E₃ x]
    exact InnerProductSpace.norm_sq_eq_re_inner (WithLp.toLp 2 x)
  conj_inner_symm x y := by
    change inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 x) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_comm (WithLp.toLp 2 x) (WithLp.toLp 2 y)
  add_left x y z := by
    change inner ℝ (WithLp.toLp 2 x + WithLp.toLp 2 y) (WithLp.toLp 2 z) =
      inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 z) +
        inner ℝ (WithLp.toLp 2 y) (WithLp.toLp 2 z)
    simpa using inner_add_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) (WithLp.toLp 2 z)
  smul_left x y r := by
    change inner ℝ (r • WithLp.toLp 2 x) (WithLp.toLp 2 y) =
      r * inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y)
    simpa using real_inner_smul_left (WithLp.toLp 2 x) (WithLp.toLp 2 y) r

noncomputable local instance instLocalChap05_Theorem_5_4_6_124 : CompleteSpace (E₂ × E₃) := inferInstance

/- Theorem 5.4.6.12 lies in the subsection's fixed-`z` slice self-concordance domain.

Sampled owner declarations:
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the source-facing barrier owner on
  `E₁ × E₃`;
* `compositionPotential_thirdDirectionalDerivative_le_selfConcordant_sigma_bound` from
  `Theorem_5_4_6_10`, the subsection owner upper bound for the composition-potential slice;
* `coneCompositionBarrier_slice_secondDirectionalDerivative_ge_sigmaSum_add_betaSq_sigmaThree`
  from `Theorem_5_4_6_11`, the slice-level second-derivative owner for the same barrier slice;
* `IsBetaCompatibleWith` from `Definition_5_4_6_2`, the compatibility owner supplying the hidden
  `β ≥ 1`, `C³`, and barrier inputs used by the slice estimates;
* `IsStandardSelfConcordantOn` from `Definition_5_1_1`, the chapter owner for the standard
  self-concordance hypothesis on `Φ`.

Source/core/bridge triage:
* source-facing: the fixed-`z` slice
  `x' ↦ coneCompositionBarrier F Φ ξ β (x', z)`;
* core/canonical: `thirdDirectionalDerivative` and `secondDirectionalDerivative`;
* bridge/view: the `D₃` upper bound from `Theorem_5_4_6_10`, the `D₂` lower bound from
  `Theorem_5_4_6_11`, and the compatibility-owner projections used to recover their hidden local
  hypotheses.

Primitive data:
* `F`, `Φ`, `ξ`, `β`, `x`, `z`, `h`;
* standard self-concordance of `Φ` on `interior Q₂` at `(ξ x, z)`;
* the lifted-direction local-norm bound and the dual-cone gradient hypothesis;
* the compatibility owner `IsBetaCompatibleWith Q₁ K F β ξ`.

Derived API:
* the slice self-concordance inequality
  `D₃ ≤ 2 D₂^(3/2)` for `x' ↦ coneCompositionBarrier F Φ ξ β (x', z)`.

This theorem should therefore sit directly on the existing `coneCompositionBarrier` slice owner
and depend on the slice-level `D₂` theorem from `5.4.6.11`, rather than reaching back to the
earlier sigma decomposition theorem and reassembling the barrier slice data locally. -/

section

variable (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂) (β : NNReal)
  (x : E₁) (z : E₃) (h : E₁)

local notation "ψ" => fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)
local notation "Ψ" => fun x' : E₁ ↦ coneCompositionBarrier F Φ ξ β (x', z)

-- Proof sketch: combine the third-derivative sigma bound from
-- `compositionPotential_thirdDirectionalDerivative_le_selfConcordant_sigma_bound` with the
-- second-derivative lower bound coming from a local reconstruction of the `D₂` slice estimate,
-- then apply the scalar inequality `t * (3 * s - t^2) ≤ 2 * s^(3/2)` to the resulting
-- `σ₁`, `σ₂`, `σ₃` expression.

/-- Helper for Theorem 5.4.6.12: positivity of the Hessian at `(ξ x, z)` makes the lifted
quadratic term `σ₁` nonnegative. -/
private theorem compositionPotentialSigmaOne_nonneg_of_hessian_positive
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x h : E₁} {z : E₃}
    (hH : (hessian Φ (ξ x, z)).IsPositive) :
    0 ≤ compositionPotentialSigmaOne Φ ξ x z h := by
  -- Unfold `σ₁` and read it as a positive Hessian quadratic form.
  rw [compositionPotentialSigmaOne_def]
  exact hH.inner_nonneg_right (fderiv ℝ ξ x h, (0 : E₃))

/-- Helper for Theorem 5.4.6.12: the assumed local-norm control already forces `σ₂` to be
nonnegative. -/
private theorem compositionPotentialSigmaTwo_nonneg_of_local_norm_bound
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x h : E₁} {z : E₃}
    (hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x h‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z h) :
    0 ≤ compositionPotentialSigmaTwo Φ ξ x z h := by
  -- The Hessian local norm is nonnegative, so any upper bound for it is nonnegative as well.
  exact le_trans
    (hessianLocalNorm_nonneg Φ (ξ x, z) (-compositionSecondLiftedDirectionDerivative ξ x h))
    hneg_liftedDirectionDerivative_le_sigmaTwo

/-- Helper for Theorem 5.4.6.12: squaring the Hessian local norm recovers the corresponding
Hessian quadratic form. -/
private theorem sq_hessianLocalNorm_eq_inner_hessian_apply
    {Φ : E₂ × E₃ → ℝ} {p u : E₂ × E₃}
    (hH : (hessian Φ p).IsPositive) :
    ‖u‖[Φ; p] ^ (2 : ℕ) = inner ℝ u (hessian Φ p u) := by
  -- Positivity of the Hessian gives the nonnegativity needed to square the local norm.
  have hquad : 0 ≤ inner ℝ u (hessian Φ p u) := hH.inner_nonneg_right u
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Theorem 5.4.6.12: a positive Hessian controls the squared mixed pairing by the
product of the corresponding diagonal quadratic forms. -/
private theorem sq_abs_inner_hessian_apply_le_hessian_quadratic_mul
    {Φ : E₂ × E₃ → ℝ} {p u v : E₂ × E₃}
    (hH : (hessian Φ p).IsPositive) :
    |inner ℝ (hessian Φ p u) v| ^ (2 : ℕ) ≤
      inner ℝ u (hessian Φ p u) * inner ℝ v (hessian Φ p v) := by
  letI : NormedSpace ℝ (E₂ × E₃) := InnerProductSpace.toNormedSpace
  let A := hessian Φ p
  have hApos : A.IsPositive := by
    simpa [A] using hH
  let a : ℝ := inner ℝ (A v) v
  let b : ℝ := 2 * inner ℝ (A u) v
  let c : ℝ := inner ℝ (A u) u
  have hpoly : ∀ α : ℝ, 0 ≤ a * (α * α) + b * α + c := by
    intro α
    have hnonneg := hApos.inner_nonneg_left (u + α • v)
    have hsmul : A (α • v) = α • A v := by
      exact A.map_smul α v
    -- Expanding the positive quadratic form on `u + α • v` exposes the discriminant bound.
    rw [show inner ℝ (A (u + α • v)) (u + α • v) = a * (α * α) + b * α + c by
      dsimp [a, b, c]
      calc
        inner ℝ (A (u + α • v)) (u + α • v)
            = inner ℝ (A u + α • A v) (u + α • v) := by
              rw [A.map_add, hsmul]
        _ = (inner ℝ (A u) u + inner ℝ (A u) (α • v)) +
              (inner ℝ (α • A v) u + inner ℝ (α • A v) (α • v)) := by
                rw [inner_add_right, inner_add_left, inner_add_left]
                ring
        _ = inner ℝ (A u) u + inner ℝ (A u) (α • v) +
              inner ℝ (α • A v) u + inner ℝ (α • A v) (α • v) := by
                ring_nf
        _ = inner ℝ (A u) u + α * inner ℝ (A u) v + α * inner ℝ (A v) u +
              (α * α) * inner ℝ (A v) v := by
                have huv : inner ℝ (A u) (α • v) = α * inner ℝ (A u) v := by
                  simpa using real_inner_smul_right (A u) v α
                have hvu : inner ℝ (α • A v) u = α * inner ℝ (A v) u := by
                  simpa using real_inner_smul_left (A v) u α
                have hvv :
                    inner ℝ (α • A v) (α • v) = (α * α) * inner ℝ (A v) v := by
                  rw [real_inner_smul_left, real_inner_smul_right]
                  ring
                rw [huv, hvu, hvv]
        _ = inner ℝ (A u) u + α * inner ℝ (A u) v + α * inner ℝ (A u) v +
              (α * α) * inner ℝ (A v) v := by
                rw [show inner ℝ (A v) u = inner ℝ (A u) v by
                  calc
                    inner ℝ (A v) u = inner ℝ v (A u) := hApos.inner_left_eq_inner_right v u
                    _ = inner ℝ (A u) v := by simp [real_inner_comm]]
        _ = a * (α * α) + b * α + c := by
                dsimp [a, b, c]
                ring] at hnonneg
    exact hnonneg
  have hdiscr : discrim a b c ≤ 0 := discrim_le_zero hpoly
  -- The nonpositive discriminant is exactly the Cauchy--Schwarz inequality for the Hessian form.
  have hsq : (inner ℝ (A u) v) ^ (2 : ℕ) ≤ a * c := by
    rw [discrim, sq] at hdiscr
    dsimp [b] at hdiscr
    nlinarith
  have hu_symm : inner ℝ (A u) u = inner ℝ u (A u) := by
    simpa using hApos.inner_left_eq_inner_right u u
  have hv_symm : inner ℝ (A v) v = inner ℝ v (A v) := by
    simpa using hApos.inner_left_eq_inner_right v v
  simpa [A, sq_abs, a, c, hu_symm, hv_symm, mul_comm, mul_left_comm, mul_assoc] using hsq

/-
Helper warning cleanup: these ambient instances are not used by the theorem below.
-/
/-- Helper for Theorem 5.4.6.12: a positive Hessian controls the mixed pairing by the product of
the induced local norms. -/
private theorem abs_inner_hessian_apply_le_hessianLocalNorm_mul
    {Φ : E₂ × E₃ → ℝ} {p u v : E₂ × E₃}
    (hH : (hessian Φ p).IsPositive) :
    |inner ℝ (hessian Φ p u) v| ≤ ‖u‖[Φ; p] * ‖v‖[Φ; p] := by
  have hsq :=
    sq_abs_inner_hessian_apply_le_hessian_quadratic_mul
      (Φ := Φ) (p := p) (u := u) (v := v) hH
  have hu_nonneg : 0 ≤ ‖u‖[Φ; p] := hessianLocalNorm_nonneg Φ p u
  have hv_nonneg : 0 ≤ ‖v‖[Φ; p] := hessianLocalNorm_nonneg Φ p v
  have hsq_norm :
      |inner ℝ (hessian Φ p u) v| ^ (2 : ℕ) ≤ (‖u‖[Φ; p] * ‖v‖[Φ; p]) ^ (2 : ℕ) := by
    -- Rewrite the diagonal quadratic terms back into the local norm surface.
    calc
      |inner ℝ (hessian Φ p u) v| ^ (2 : ℕ) ≤
          inner ℝ u (hessian Φ p u) * inner ℝ v (hessian Φ p v) :=
        hsq
      _ = ‖u‖[Φ; p] ^ (2 : ℕ) * ‖v‖[Φ; p] ^ (2 : ℕ) := by
        rw [← sq_hessianLocalNorm_eq_inner_hessian_apply (Φ := Φ) (p := p) (u := u) hH,
          ← sq_hessianLocalNorm_eq_inner_hessian_apply (Φ := Φ) (p := p) (u := v) hH]
      _ = (‖u‖[Φ; p] * ‖v‖[Φ; p]) ^ (2 : ℕ) := by
        ring
  have hprod_nonneg : 0 ≤ ‖u‖[Φ; p] * ‖v‖[Φ; p] := mul_nonneg hu_nonneg hv_nonneg
  -- Nonnegativity of the local norms lets the squared estimate descend to the unsquared one.
  exact (sq_le_sq₀ (abs_nonneg _) hprod_nonneg).mp hsq_norm

/-- Helper for Theorem 5.4.6.12: the lifted first derivative direction has local norm
`σ₁^(1/2)`. -/
private theorem lifted_direction_hessianLocalNorm_eq_sqrt_sigmaOne
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x h : E₁} {z : E₃} :
    ‖(fderiv ℝ ξ x h, (0 : E₃))‖[Φ; (ξ x, z)] =
      Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h) := by
  -- Both sides are definitional presentations of the same Hessian quadratic form.
  rw [hessianLocalNorm_def, compositionPotentialSigmaOne_def]

/-- Helper for Theorem 5.4.6.12: the mixed Hessian pairing in the third-derivative decomposition
is bounded by `σ₁^(1/2)` times the local norm of the lifted second derivative direction. -/
private theorem cross_term_le_sqrt_sigmaOne_mul_neg_lifted_localNorm
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x h : E₁} {z : E₃}
    (hH : (hessian Φ (ξ x, z)).IsPositive) :
    inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x h, (0 : E₃)))
        (compositionSecondLiftedDirectionDerivative ξ x h) ≤
      Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h) *
        ‖-compositionSecondLiftedDirectionDerivative ξ x h‖[Φ; (ξ x, z)] := by
  have habs :=
    abs_inner_hessian_apply_le_hessianLocalNorm_mul
      (Φ := Φ) (p := (ξ x, z)) (u := (fderiv ℝ ξ x h, (0 : E₃)))
      (v := -compositionSecondLiftedDirectionDerivative ξ x h) hH
  have hone_sided :
      inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x h, (0 : E₃)))
          (compositionSecondLiftedDirectionDerivative ξ x h) ≤
        ‖(fderiv ℝ ξ x h, (0 : E₃))‖[Φ; (ξ x, z)] *
          ‖-compositionSecondLiftedDirectionDerivative ξ x h‖[Φ; (ξ x, z)] := by
    have habs' :
        |inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x h, (0 : E₃)))
            (compositionSecondLiftedDirectionDerivative ξ x h)| ≤
          ‖(fderiv ℝ ξ x h, (0 : E₃))‖[Φ; (ξ x, z)] *
            ‖-compositionSecondLiftedDirectionDerivative ξ x h‖[Φ; (ξ x, z)] := by
      have habs'' := habs
      rw [inner_neg_right, abs_neg] at habs''
      exact habs''
    -- Drop the absolute value on the left by the standard one-sided estimate.
    refine le_trans (le_abs_self _) ?_
    exact habs'
  rw [lifted_direction_hessianLocalNorm_eq_sqrt_sigmaOne] at hone_sided
  exact hone_sided

/-- Helper for Theorem 5.4.6.12: the mixed Hessian term is bounded by `σ₁^(1/2) σ₂`. -/
private theorem compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo_local
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x h : E₁} {z : E₃}
    (hH : (hessian Φ (ξ x, z)).IsPositive)
    (hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x h‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z h) :
    inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x h, (0 : E₃)))
        (compositionSecondLiftedDirectionDerivative ξ x h) ≤
      Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h) *
        compositionPotentialSigmaTwo Φ ξ x z h := by
  have hcross :=
    cross_term_le_sqrt_sigmaOne_mul_neg_lifted_localNorm
      (ξ := ξ) (x := x) (h := h) (z := z) hH
  -- Insert the given owner-level bound on the lifted second derivative direction.
  calc
    inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x h, (0 : E₃)))
        (compositionSecondLiftedDirectionDerivative ξ x h) ≤
      Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h) *
        ‖-compositionSecondLiftedDirectionDerivative ξ x h‖[Φ; (ξ x, z)] :=
      hcross
    _ ≤ Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h) *
          compositionPotentialSigmaTwo Φ ξ x z h := by
      exact mul_le_mul_of_nonneg_left
        hneg_liftedDirectionDerivative_le_sigmaTwo
        (Real.sqrt_nonneg _)

/-- Helper for Theorem 5.4.6.12: the compatibility owner bounds the pairing with
`D³ξ(x)[h, h, h]` by `3 β σ₂ σ₃^(1/2)`. -/
private theorem yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility_local
    {Q₁ : Set E₁} {K : ConvexCone ℝ E₂} {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ}
    {β : NNReal} {ξ : E₁ → E₂} {x h : E₁} {z : E₃}
    (hξ : IsBetaCompatibleWith Q₁ K F β ξ)
    (hx : x ∈ interior Q₁)
    (hneg_yGradient_mem_innerDual :
      -∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x) ∈ innerDual (K : Set E₂)) :
    inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
        (vectorThirdDirectionalDerivative ξ x h) ≤
      3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z h *
        Real.sqrt (sigmaThree F x h) := by
  let g : E₂ := ∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x)
  let s : E₂ :=
    (3 * (β : ℝ) * ‖h‖[F; x]) • (-vectorSecondDirectionalDerivative ξ x h) +
      vectorThirdDirectionalDerivative ξ x h
  have hs : s ∈ K := by
    -- The sign-reversed compatibility inequality is exactly the cone membership we need.
    simpa [s] using hξ.compatibility_bound_sign_reversal hx h
  rw [mem_innerDual] at hneg_yGradient_mem_innerDual
  have hpair : inner ℝ g s ≤ 0 :=
    by simpa [g, real_inner_comm] using hneg_yGradient_mem_innerDual hs
  -- Unfold the source-facing scalar names and isolate the target pairing term.
  dsimp [g, s] at hpair ⊢
  rw [inner_add_right, inner_smul_right, inner_neg_right] at hpair
  rw [compositionPotentialSigmaTwo_def]
  rw [sqrt_sigmaThree]
  linarith

/-- Helper for Theorem 5.4.6.12: the missing `5.4.6.10` owner can be reconstructed locally from
the available decomposition, cross-term, and compatibility bounds. -/
private theorem compositionPotential_thirdDirectionalDerivative_le_selfConcordant_sigma_bound_local
    {dom : Set (E₂ × E₃)} {Q₁ : Set E₁} {K : ConvexCone ℝ E₂}
    {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {β : NNReal} {x h : E₁} {z : E₃}
    (hξ : ContDiffAt ℝ 3 ξ x)
    (hΦ_self : IsStandardSelfConcordantOn dom Φ)
    (hyz : (ξ x, z) ∈ dom)
    (hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x h‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z h)
    (hξ_compat : IsBetaCompatibleWith Q₁ K F β ξ)
    (hx : x ∈ interior Q₁)
    (hneg_yGradient_mem_innerDual :
      -∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x) ∈ innerDual (K : Set E₂)) :
    thirdDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x h ≤
      2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h)) ^ (3 : ℕ) +
        3 * Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h) *
          compositionPotentialSigmaTwo Φ ξ x z h +
        3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z h *
          Real.sqrt (sigmaThree F x h) := by
  -- Route correction: `Theorem_5_4_6_10.olean` is unavailable in this workspace, so rebuild the
  -- same owner-level estimate directly from the lower-level subsection theorems.
  letI : NormedSpace ℝ (E₂ × E₃) := InnerProductSpace.toNormedSpace
  letI : Module ℝ (E₂ × E₃) := NormedSpace.toModule
  letI : SMul ℝ (E₂ × E₃) := (show Module ℝ (E₂ × E₃) from inferInstance).toSMul
  let l : E₂ × E₃ := (fderiv ℝ ξ x h, 0)
  have hΦ : ContDiffAt ℝ 3 Φ (ξ x, z) := by
    exact hΦ_self.contDiffOn.contDiffAt (hΦ_self.isOpen_domain.mem_nhds hyz)
  have hThirdDecomp :
      thirdDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x h =
        thirdDirectionalDerivative Φ (ξ x, z) l +
          (3 : ℝ) * inner ℝ (hessian Φ (ξ x, z) l)
            (compositionSecondLiftedDirectionDerivative ξ x h) +
          inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
            (vectorThirdDirectionalDerivative ξ x h) := by
    simpa [l] using compositionPotential_thirdDirectionalDerivative_eq hξ hΦ
  have hThirdAbs :
      |thirdDirectionalDerivative Φ (ξ x, z) l| ≤
        2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h)) ^ (3 : ℕ) := by
    -- Standard self-concordance controls the pure third derivative term of `Φ`.
    simpa [compositionPotentialSigmaOne_def, hessianLocalNorm_def] using
      hΦ_self.third_deriv_bound hyz l
  have hThird :
      thirdDirectionalDerivative Φ (ξ x, z) l ≤
        2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h)) ^ (3 : ℕ) :=
    le_trans (le_abs_self _) hThirdAbs
  have hH : (hessian Φ (ξ x, z)).IsPositive :=
    hΦ_self.hessian_isPositive hyz
  have hCrossBound :
      inner ℝ (hessian Φ (ξ x, z) l) (compositionSecondLiftedDirectionDerivative ξ x h) ≤
        Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h) *
          compositionPotentialSigmaTwo Φ ξ x z h := by
    -- Apply the local Hessian-metric Cauchy--Schwarz estimate for the mixed term.
    simpa [l] using
      compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo_local
        (ξ := ξ) (x := x) (h := h) (z := z) hH
        hneg_liftedDirectionDerivative_le_sigmaTwo
  have hBetaBound :
      inner ℝ (∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x))
          (vectorThirdDirectionalDerivative ξ x h) ≤
        3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z h *
          Real.sqrt (sigmaThree F x h) :=
    yGradient_pairing_vectorThirdDirectionalDerivative_le_of_betaCompatibility_local
      hξ_compat hx hneg_yGradient_mem_innerDual
  -- Assemble the third-derivative decomposition with the three owner-level bounds.
  rw [hThirdDecomp]
  linarith [hThird, hCrossBound, hBetaBound]

/-- Helper for Theorem 5.4.6.12: the frozen `z`-coordinate of the slice is `C³`. -/
private theorem fixedZCoordinateContDiffAtThree
    {x : E₁} {z : E₃} :
    ContDiffAt ℝ 3 (fun _ : E₁ ↦ z) x := by
  -- The frozen `z`-coordinate is constant along the slice.
  simpa using (contDiffAt_const : ContDiffAt ℝ 3 (fun _ : E₁ ↦ z) x)

/-- Helper for Theorem 5.4.6.12: ambient `C³` regularity of `Φ` transfers to the fixed-`z`
left slice `y' ↦ Φ (y', z)`. -/
private theorem fixedZSliceContDiffAtThree
    {Φ : E₂ × E₃ → ℝ} {y : E₂} {z : E₃}
    (hΦ : ContDiffAt ℝ 3 Φ (y, z)) :
    ContDiffAt ℝ 3 (fun y' : E₂ ↦ Φ (y', z)) y := by
  let inl : E₂ →L[ℝ] E₂ × E₃ := ContinuousLinearMap.inl ℝ E₂ E₃
  have hembed : ContDiffAt ℝ 3 (fun y' : E₂ ↦ inl y' + ((0 : E₂), z)) y := by
    -- The fixed-`z` embedding is affine-linear in the free `y` coordinate.
    exact inl.contDiff.contDiffAt.add contDiffAt_const
  have hΦ_embed : ContDiffAt ℝ 3 Φ (inl y + ((0 : E₂), z)) := by
    -- Normalize the embedded point back to the source pair `(y, z)`.
    simpa [inl] using hΦ
  -- Compose `Φ` with the affine embedding `y' ↦ (y', z)`.
  simpa [inl, Function.comp] using ContDiffAt.comp (x := y) hΦ_embed hembed

/-- Helper for Theorem 5.4.6.12: the fixed-`z` slice of `compositionPotential` is `C³` whenever
the ambient potential is `C³` at `(ξ x, z)` and `ξ` is `C³` at `x`. -/
private theorem compositionPotentialSliceContDiffAtThree
    {Q₂ : Set (E₂ × E₃)}
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x : E₁} {z : E₃}
    (hΦ : IsStandardSelfConcordantOn (interior Q₂) Φ)
    (hyz : (ξ x, z) ∈ interior Q₂)
    (hξ3 : ContDiffAt ℝ 3 ξ x) :
    ContDiffAt ℝ 3 (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x := by
  have hΦ3 : ContDiffAt ℝ 3 Φ (ξ x, z) := by
    -- Standard self-concordance supplies the ambient `C³` witness at interior points.
    exact hΦ.contDiffOn.contDiffAt (hΦ.isOpen_domain.mem_nhds hyz)
  have hg3 : ContDiffAt ℝ 3 (fun y' : E₂ ↦ Φ (y', z)) (ξ x) := by
    -- Freeze `z` first so the outer map lives on `E₂` without any product-instance ambiguity.
    exact fixedZSliceContDiffAtThree (Φ := Φ) (y := ξ x) (z := z) hΦ3
  -- Compose the `C³` fixed-`z` slice with `ξ`.
  simpa [compositionPotential] using hg3.comp x hξ3

/-- Helper for Theorem 5.4.6.12: the fixed-`z` slice of `coneCompositionBarrier` splits its third
directional derivative into the composition-potential part and the scaled barrier part. -/
private theorem
    coneCompositionBarrierSliceThirdDirectionalDerivativeEqCompositionPotentialAddBetaCubeThird
    {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {β : NNReal} {x h : E₁} {z : E₃}
    (hψ3 : ContDiffAt ℝ 3 (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x)
    (hF3 : ContDiffAt ℝ 3 F x) :
    thirdDirectionalDerivative
        (fun x' : E₁ ↦ coneCompositionBarrier F Φ ξ β (x', z)) x h =
      thirdDirectionalDerivative (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x h +
        ((β : ℝ) ^ (3 : ℕ)) * thirdDirectionalDerivative F x h := by
  have hψ_slice :
      ContDiffAt ℝ 3
        (directionalSlice (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x h) 0 := by
    have hline : ContDiffAt ℝ 3 (fun t : ℝ ↦ x + t • h) 0 :=
      contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    have hψ_at_line :
        ContDiffAt ℝ 3 (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z))
          ((fun t : ℝ ↦ x + t • h) 0) := by
      simpa using hψ3
    simpa [directionalSlice] using hψ_at_line.comp 0 hline
  have hF_slice : ContDiffAt ℝ 3 (directionalSlice F x h) 0 := by
    have hline : ContDiffAt ℝ 3 (fun t : ℝ ↦ x + t • h) 0 :=
      contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
    have hF_at_line : ContDiffAt ℝ 3 F ((fun t : ℝ ↦ x + t • h) 0) := by
      simpa using hF3
    simpa [directionalSlice] using hF_at_line.comp 0 hline
  let g : ℝ → ℝ := ((β : ℝ) ^ (3 : ℕ)) • directionalSlice F x h
  have hg : ContDiffAt ℝ 3 g 0 := by
    simpa [g] using ContDiffAt.const_smul ((β : ℝ) ^ (3 : ℕ)) hF_slice
  have hslice :
      directionalSlice (fun x' : E₁ ↦ coneCompositionBarrier F Φ ξ β (x', z)) x h =
        directionalSlice (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x h + g := by
    -- Unfold the slice owner and isolate the scaled barrier summand.
    funext t
    simp [g, directionalSlice, coneCompositionBarrier, compositionPotential, smul_eq_mul]
  -- Differentiate the slice decomposition termwise.
  rw [thirdDirectionalDerivative, hslice, iteratedDeriv_add hψ_slice hg]
  simp [g, thirdDirectionalDerivative, smul_eq_mul]

/-- Helper for Theorem 5.4.6.12: the scaled barrier part of the slice satisfies the standard
cubic self-concordance bound. -/
private theorem coneCompositionBarrierSliceBarrierThirdBound
    {Q₁ : Set E₁} {F : E₁ → ℝ} {β : NNReal} {x h : E₁}
    (hF_self : IsStandardSelfConcordantOn (interior Q₁) F)
    (hx : x ∈ interior Q₁) :
    ((β : ℝ) ^ (3 : ℕ)) * thirdDirectionalDerivative F x h ≤
      2 * ((β : ℝ) * Real.sqrt (sigmaThree F x h)) ^ (3 : ℕ) := by
  have hF_third_abs :
      |thirdDirectionalDerivative F x h| ≤
        2 * (Real.sqrt (sigmaThree F x h)) ^ (3 : ℕ) := by
    -- Standard self-concordance of the barrier controls the pure third derivative term.
    simpa using hF_self.third_deriv_bound hx h
  have hβ_cube_nonneg : 0 ≤ ((β : ℝ) ^ (3 : ℕ)) := by
    positivity
  calc
    ((β : ℝ) ^ (3 : ℕ)) * thirdDirectionalDerivative F x h
        ≤ ((β : ℝ) ^ (3 : ℕ)) * |thirdDirectionalDerivative F x h| := by
            gcongr
            exact le_abs_self _
    _ ≤ ((β : ℝ) ^ (3 : ℕ)) * (2 * (Real.sqrt (sigmaThree F x h)) ^ (3 : ℕ)) := by
          exact mul_le_mul_of_nonneg_left hF_third_abs hβ_cube_nonneg
    _ = 2 * ((β : ℝ) * Real.sqrt (sigmaThree F x h)) ^ (3 : ℕ) := by
      ring

/-- Helper for Theorem 5.4.6.12: the sigma-expression from the composition part together with the
scaled barrier term is controlled by the cube of the total square-root sum. -/
private theorem third_derivative_sigma_expression_add_barrier_le_two_sqrt_sum_cubed
    {a b c u : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hu : 0 ≤ u) :
    2 * (Real.sqrt a) ^ (3 : ℕ) +
        3 * Real.sqrt a * b +
        3 * u * b * Real.sqrt c +
        2 * (u * Real.sqrt c) ^ (3 : ℕ) ≤
      2 * (Real.sqrt (a + b + u ^ (2 : ℕ) * c)) ^ (3 : ℕ) := by
  let p := Real.sqrt a
  let q := u * Real.sqrt c
  let s := a + b + u ^ (2 : ℕ) * c
  let t := p + q
  have hp : 0 ≤ p := by
    exact Real.sqrt_nonneg a
  have hq : 0 ≤ q := by
    exact mul_nonneg hu (Real.sqrt_nonneg c)
  have hs : 0 ≤ s := by
    dsimp [s]
    nlinarith
  have hs_eq : s = p ^ (2 : ℕ) + b + q ^ (2 : ℕ) := by
    -- Rewrite `s` in the polynomial variables `p = √a` and `q = u √c`.
    have ha_sq : a = p ^ (2 : ℕ) := by
      dsimp [p]
      symm
      simpa using Real.sq_sqrt ha
    have hq_sq : q ^ (2 : ℕ) = u ^ (2 : ℕ) * c := by
      dsimp [q]
      calc
        (u * Real.sqrt c) ^ (2 : ℕ) = u ^ (2 : ℕ) * (Real.sqrt c) ^ (2 : ℕ) := by
          ring
        _ = u ^ (2 : ℕ) * c := by
          rw [Real.sq_sqrt hc]
    dsimp [s]
    nlinarith [ha_sq, hq_sq]
  have ht_eq :
      t * (3 * s - t ^ (2 : ℕ)) =
        2 * p ^ (3 : ℕ) + 3 * p * b + 3 * b * q + 2 * q ^ (3 : ℕ) := by
    -- The left-hand side is exactly the textbook scalar expression in the variables `p` and `q`.
    dsimp [t]
    rw [hs_eq]
    ring
  have hfactor :
      2 * (Real.sqrt s) ^ (3 : ℕ) - t * (3 * s - t ^ (2 : ℕ)) =
        (Real.sqrt s - t) ^ (2 : ℕ) * (2 * Real.sqrt s + t) := by
    -- Factoring against `r = √s` produces a manifestly nonnegative remainder.
    have hs_sq : s = (Real.sqrt s) ^ (2 : ℕ) := by
      symm
      simpa using Real.sq_sqrt hs
    have hfactor' :
        2 * (Real.sqrt s) ^ (3 : ℕ) -
            t * (3 * ((Real.sqrt s) ^ (2 : ℕ)) - t ^ (2 : ℕ)) =
          (Real.sqrt s - t) ^ (2 : ℕ) * (2 * Real.sqrt s + t) := by
      ring
    rw [← hs_sq] at hfactor'
    exact hfactor'
  have hfactor_nonneg :
      0 ≤ (Real.sqrt s - t) ^ (2 : ℕ) * (2 * Real.sqrt s + t) := by
    refine mul_nonneg (sq_nonneg _) ?_
    nlinarith [Real.sqrt_nonneg s, hp, hq]
  have hbase : t * (3 * s - t ^ (2 : ℕ)) ≤ 2 * (Real.sqrt s) ^ (3 : ℕ) := by
    nlinarith [hfactor_nonneg, hfactor]
  -- Substitute back the sigma data.
  calc
    2 * (Real.sqrt a) ^ (3 : ℕ) +
        3 * Real.sqrt a * b +
        3 * u * b * Real.sqrt c +
        2 * (u * Real.sqrt c) ^ (3 : ℕ)
        =
          2 * p ^ (3 : ℕ) + 3 * p * b + 3 * b * q + 2 * q ^ (3 : ℕ) := by
            dsimp [p, q]
            ring
    _ = t * (3 * s - t ^ (2 : ℕ)) := by
      rw [ht_eq]
    _ ≤ 2 * (Real.sqrt s) ^ (3 : ℕ) :=
      hbase
    _ = 2 * (Real.sqrt (a + b + u ^ (2 : ℕ) * c)) ^ (3 : ℕ) := by
      dsimp [s]

/-- Theorem 5.4.6.12: assume `Φ` is standard self-concordant at `(ξ x, z)`, `ξ` is
`β`-compatible with the barrier `F` on `Q₁`, and the local hypotheses used in
Theorem 5.4.6.10 hold for the slice `x' ↦ compositionPotential Φ ξ (x', z)`. The hidden
`β ≥ 1`, `C³`, and barrier inputs needed for the slice second-derivative estimate come from the
compatibility owner `hξ_compat`. Then the slice
`Ψ(x') = coneCompositionBarrier F Φ ξ β (x', z)` satisfies the third-derivative inequality
`D₃ ≤ 2 D₂^(3/2)` at `x` in direction `h`. -/
theorem coneCompositionBarrier_slice_selfConcordant_bound
    {Q₁ : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
    (hΦ : IsStandardSelfConcordantOn (interior Q₂) Φ)
    (hyz : (ξ x, z) ∈ interior Q₂)
    (hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x h‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z h)
    (hξ_compat : IsBetaCompatibleWith Q₁ K F β ξ)
    (hx : x ∈ interior Q₁)
    (hneg_yGradient_mem_innerDual :
      -∇ (fun y : E₂ ↦ Φ (y, z)) (ξ x) ∈ innerDual (K : Set E₂)) :
    thirdDirectionalDerivative Ψ x h ≤
      2 * (Real.sqrt (secondDirectionalDerivative Ψ x h)) ^ (3 : ℕ) := by
  rcases hξ_compat.selfConcordantBarrier with ⟨ν, hFbarrier⟩
  let hF_self : IsStandardSelfConcordantOn (interior Q₁) F :=
    hFbarrier.toIsStandardSelfConcordantOn
  have hβ : 1 ≤ β := hξ_compat.one_le_parameter
  have hβ_nonneg : 0 ≤ (β : ℝ) := by
    exact_mod_cast β.2
  have hξ3 : ContDiffAt ℝ 3 ξ x := by
    -- The compatibility owner packages the `C³` regularity of `ξ` on the barrier domain.
    exact hξ_compat.contDiffOn.contDiffAt (isOpen_interior.mem_nhds hx)
  have hξ2 : ContDiffAt ℝ 2 ξ x :=
    hξ3.of_le (by norm_num)
  have hF3 : ContDiffAt ℝ 3 F x := by
    -- The barrier hidden in `hξ_compat` provides the third-order regularity of `F`.
    exact hF_self.contDiffOn.contDiffAt (hF_self.isOpen_domain.mem_nhds hx)
  have hψ3 : ContDiffAt ℝ 3 (fun x' : E₁ ↦ compositionPotential Φ ξ (x', z)) x := by
    -- Route correction: isolate the ambient-product `C³` slice transport as the only remaining
    -- bridge instead of repeating the same instance-sensitive construction twice.
    exact compositionPotentialSliceContDiffAtThree (Φ := Φ) (ξ := ξ) (x := x) (z := z) hΦ hyz hξ3
  have hΨ_third_eq :
      thirdDirectionalDerivative Ψ x h =
        thirdDirectionalDerivative ψ x h +
          ((β : ℝ) ^ (3 : ℕ)) * thirdDirectionalDerivative F x h := by
    -- Route correction: keep the slice decomposition in a small owner-level helper instead of
    -- rebuilding it inline in the main theorem.
    exact
      coneCompositionBarrierSliceThirdDirectionalDerivativeEqCompositionPotentialAddBetaCubeThird
        (Φ := Φ) (ξ := ξ) (β := β) (x := x) (z := z) (h := h) hψ3 hF3
  have hcomp_bound :
      thirdDirectionalDerivative ψ x h ≤
        2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h)) ^ (3 : ℕ) +
          3 * Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h) *
            compositionPotentialSigmaTwo Φ ξ x z h +
          3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z h *
            Real.sqrt (sigmaThree F x h) := by
    -- Reconstruct the slice `D₃` bound locally because the upstream owner module is unavailable.
    exact compositionPotential_thirdDirectionalDerivative_le_selfConcordant_sigma_bound_local
      hξ3 hΦ hyz hneg_liftedDirectionDerivative_le_sigmaTwo hξ_compat hx
      hneg_yGradient_mem_innerDual
  have hbarrier_bound :
      ((β : ℝ) ^ (3 : ℕ)) * thirdDirectionalDerivative F x h ≤
        2 * ((β : ℝ) * Real.sqrt (sigmaThree F x h)) ^ (3 : ℕ) := by
    -- Use the dedicated owner-level helper for the barrier contribution.
    exact coneCompositionBarrierSliceBarrierThirdBound (β := β) (x := x) (h := h) hF_self hx
  have hσ₁_nonneg :
      0 ≤ compositionPotentialSigmaOne Φ ξ x z h := by
    -- The Hessian positivity inherited from `Φ` controls the first sigma term.
    exact compositionPotentialSigmaOne_nonneg_of_hessian_positive
      (hΦ.hessian_isPositive hyz)
  have hσ₂_nonneg :
      0 ≤ compositionPotentialSigmaTwo Φ ξ x z h := by
    -- The specialized local-norm hypothesis already forces the second sigma term to be nonnegative.
    exact compositionPotentialSigmaTwo_nonneg_of_local_norm_bound
      hneg_liftedDirectionDerivative_le_sigmaTwo
  have hσ₃_nonneg : 0 ≤ sigmaThree F x h :=
    sigmaThree_nonneg F x h
  have hscalar :
      2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h)) ^ (3 : ℕ) +
          3 * Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h) *
            compositionPotentialSigmaTwo Φ ξ x z h +
          3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z h *
            Real.sqrt (sigmaThree F x h) +
          2 * ((β : ℝ) * Real.sqrt (sigmaThree F x h)) ^ (3 : ℕ) ≤
        2 *
          (Real.sqrt
            (compositionPotentialSigmaOne Φ ξ x z h +
              compositionPotentialSigmaTwo Φ ξ x z h +
              (β : ℝ) ^ (2 : ℕ) * sigmaThree F x h)) ^ (3 : ℕ) := by
    -- The scalar endgame is the textbook inequality `t (3 s - t^2) ≤ 2 s^(3/2)`.
    exact third_derivative_sigma_expression_add_barrier_le_two_sqrt_sum_cubed
      hσ₁_nonneg hσ₂_nonneg hσ₃_nonneg hβ_nonneg
  have hD₂_sigma :
      compositionPotentialSigmaOne Φ ξ x z h +
          compositionPotentialSigmaTwo Φ ξ x z h +
          (β : ℝ) ^ (2 : ℕ) * sigmaThree F x h ≤
        secondDirectionalDerivative Ψ x h := by
    have hF_sigma : secondDirectionalDerivative F x h = sigmaThree F x h := by
      have hF2 : ContDiffAt ℝ 2 F x := hF3.of_le (by norm_num)
      have hF_diff : DifferentiableAt ℝ F x := hF3.differentiableAt (by norm_num)
      have hF_fderiv : ContDiffAt ℝ 1 (fderiv ℝ F) x := by
        simpa using hF2.fderiv_right_succ
      have hgrad : DifferentiableAt ℝ (∇ F) x := by
        simpa [gradient] using
          (InnerProductSpace.toDual ℝ E₁).symm.differentiableAt.comp x
            (hF_fderiv.differentiableAt (by norm_num))
      rw [secondDirectionalDerivative_eq_hessian_quadratic_form hF_diff hgrad]
      symm
      exact sigmaThree_eq_inner_hessian F x h (hF_self.hessian_posSemidef hx h)
    have hΦ2 : ContDiffAt ℝ 2 Φ (ξ x, z) := by
      -- Feed the ambient `Φ` regularity theorem the product-point witness it actually expects.
      exact (hΦ.contDiffOn.contDiffAt (hΦ.isOpen_domain.mem_nhds hyz)).of_le (by norm_num)
    have hψ2 : ContDiffAt ℝ 2 ψ x :=
      hψ3.of_le (by norm_num)
    have hψ_slice : ContDiffAt ℝ 2 (directionalSlice ψ x h) 0 := by
      have hline : ContDiffAt ℝ 2 (fun t : ℝ ↦ x + t • h) 0 :=
        contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
      have hψ' : ContDiffAt ℝ 2 ψ ((fun t : ℝ ↦ x + t • h) 0) := by
        simpa using hψ2
      simpa [directionalSlice] using hψ'.comp 0 hline
    have hF2 : ContDiffAt ℝ 2 F x := hF3.of_le (by norm_num)
    have hF_slice : ContDiffAt ℝ 2 (directionalSlice F x h) 0 := by
      have hline : ContDiffAt ℝ 2 (fun t : ℝ ↦ x + t • h) 0 :=
        contDiffAt_const.add (contDiffAt_id.smul contDiffAt_const)
      have hF' : ContDiffAt ℝ 2 F ((fun t : ℝ ↦ x + t • h) 0) := by
        simpa using hF2
      simpa [directionalSlice] using hF'.comp 0 hline
    let g : ℝ → ℝ := ((β : ℝ) ^ 3) • directionalSlice F x h
    have hg : ContDiffAt ℝ 2 g 0 := by
      simpa [g] using ContDiffAt.const_smul ((β : ℝ) ^ 3) hF_slice
    have hslice : directionalSlice Ψ x h = directionalSlice ψ x h + g := by
      funext t
      simp [g, directionalSlice, coneCompositionBarrier, compositionPotential, smul_eq_mul]
    have hD₂_decomp :
        secondDirectionalDerivative Ψ x h =
          secondDirectionalDerivative ψ x h + ((β : ℝ) ^ 3) * sigmaThree F x h := by
      rw [secondDirectionalDerivative, hslice, iteratedDeriv_add hψ_slice hg]
      simp only [g, iteratedDeriv_const_smul_field]
      rw [show iteratedDeriv 2 (directionalSlice F x h) 0 = secondDirectionalDerivative F x h by
        rfl]
      rw [hF_sigma]
      rfl
    rw [
      hD₂_decomp,
      compositionPotential_secondDirectionalDerivative_eq_sigmaOne_add_sigmaTwo hξ2 hΦ2
    ]
    have hβsq : ((β : ℝ) ^ 2) ≤ (β : ℝ) ^ 3 := by
      nlinarith
    have hmul :
        ((β : ℝ) ^ 2) * sigmaThree F x h ≤ ((β : ℝ) ^ 3) * sigmaThree F x h :=
      mul_le_mul_of_nonneg_right hβsq (sigmaThree_nonneg F x h)
    linarith
  have hsqrt_mono :
      Real.sqrt
          (compositionPotentialSigmaOne Φ ξ x z h +
            compositionPotentialSigmaTwo Φ ξ x z h +
            (β : ℝ) ^ (2 : ℕ) * sigmaThree F x h) ≤
        Real.sqrt (secondDirectionalDerivative Ψ x h) := by
    exact Real.sqrt_le_sqrt hD₂_sigma
  have hpow_mono :
      (Real.sqrt
          (compositionPotentialSigmaOne Φ ξ x z h +
            compositionPotentialSigmaTwo Φ ξ x z h +
            (β : ℝ) ^ (2 : ℕ) * sigmaThree F x h)) ^ (3 : ℕ) ≤
        (Real.sqrt (secondDirectionalDerivative Ψ x h)) ^ (3 : ℕ) := by
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_mono 3
  -- Assemble the slice decomposition, the two derivative estimates, and the scalar endgame.
  calc
    thirdDirectionalDerivative Ψ x h
        = thirdDirectionalDerivative ψ x h +
            ((β : ℝ) ^ (3 : ℕ)) * thirdDirectionalDerivative F x h := hΨ_third_eq
    _ ≤
        (2 * (Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h)) ^ (3 : ℕ) +
            3 * Real.sqrt (compositionPotentialSigmaOne Φ ξ x z h) *
              compositionPotentialSigmaTwo Φ ξ x z h +
            3 * (β : ℝ) * compositionPotentialSigmaTwo Φ ξ x z h *
              Real.sqrt (sigmaThree F x h)) +
          2 * ((β : ℝ) * Real.sqrt (sigmaThree F x h)) ^ (3 : ℕ) := by
            linarith [hcomp_bound, hbarrier_bound]
    _ ≤
        2 *
          (Real.sqrt
            (compositionPotentialSigmaOne Φ ξ x z h +
              compositionPotentialSigmaTwo Φ ξ x z h +
              (β : ℝ) ^ (2 : ℕ) * sigmaThree F x h)) ^ (3 : ℕ) := by
            simpa [add_assoc, add_left_comm, add_comm] using hscalar
    _ ≤ 2 * (Real.sqrt (secondDirectionalDerivative Ψ x h)) ^ (3 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hpow_mono (by norm_num)

end
