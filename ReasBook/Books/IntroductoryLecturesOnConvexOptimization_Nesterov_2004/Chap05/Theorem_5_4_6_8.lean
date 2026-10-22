/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_6_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient HessianLocalNorm
open Set Topology

noncomputable section

universe u v w

/- Theorem 5.4.6.8 lies in the subsection's composed Hessian / local-norm domain.

Sampled owner declarations:
* `hessian` in `Chap01/Definition_1_4_16`, the canonical owner for `∇² Φ`;
* `hessianLocalNorm` / `‖h‖[Φ; p]` in `Definition_5_1_1`, the canonical owner for the square root
  of the Hessian quadratic form;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the subsection owner for the source
  assumption that `(5.3.13)` holds for `Φ` on `interior Q₂`;
* `IsSelfConcordantOnWith.hessian_isPositive` and
  `IsSelfConcordantBarrierOnWith.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction`
  from `Definition_5_1_1` / `Corollary_5_3_2`, the canonical bridges from the barrier owner to
  pointwise Hessian positivity and the local-norm recession estimate;
* `compositionPotentialSigmaOne` and `compositionPotentialSigmaTwo` in `Theorem_5_4_6_5`, the
  source-facing `σ₁` and `σ₂` terms in the subsection;
* `compositionSecondLiftedDirectionDerivative` in `Definition_5_4_6_7`, the bridge realizing the
  lifted derivative direction `l' = (D²ξ(x)[d, d], 0)`.

Source/core/bridge triage:
* source-facing: the cross-term estimate `⟪∇² Φ(ξ(x), z) l, l'⟫ ≤ σ₁^(1/2) σ₂`;
* core/canonical: the barrier owner on `interior Q₂`, `hessian Φ (ξ x, z)`, and
  `‖·‖[Φ; (ξ x, z)]`;
* bridge/view: the canonical lifted pair `(fderiv ℝ ξ x d, 0)` and
  `compositionSecondLiftedDirectionDerivative ξ x d`.

Primitive data:
* the map `ξ`, point `x`, direction `d`, auxiliary point `z`, and set `Q₂`;
* convexity of `Q₂`, a barrier owner for `Φ` on `interior Q₂`, membership `(ξ x, z) ∈ interior Q₂`,
  and the source recession-direction hypothesis for `-l'` on `Q₂`.

Derived API:
* the lifted direction `l = (Dξ(x)[d], 0)`;
* the source-facing scalar terms `σ₁` and `σ₂`;
* the pointwise Hessian positivity and local-norm estimate derived from the source barrier and
  recession assumptions.

The public statement should therefore stay source-facing on `Q₂`, the barrier owner for
`interior Q₂`, and the recession-direction hypothesis on `-l'`; the pointwise Hessian-positivity
and local-norm bounds are downstream owner-level consequences, not primitive public inputs. -/

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [InnerProductSpace ℝ E₂] [CompleteSpace E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace ℝ E₃] [CompleteSpace E₃]

-- Semantic recall: `ProdL2` provides the canonical `L²` product geometry; this file matches the
-- same `WithLp 2`-transported product structure used by `compositionPotentialSigmaOne`.
noncomputable local instance instLocalChap05_Theorem_5_4_6_81 : SeminormedAddCommGroup (E₂ × E₃) :=
  WithLp.seminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_82 : NormedAddCommGroup (E₂ × E₃) :=
  WithLp.normedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instLocalChap05_Theorem_5_4_6_83 : NormedSpace ℝ (E₂ × E₃) :=
  WithLp.normedSpaceSeminormedAddCommGroupToProd 2 E₂ E₃

noncomputable local instance instInnerProductSpaceChap05_Theorem_5_4_6_81 : InnerProductSpace ℝ (E₂ × E₃) where
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

noncomputable local instance instLocalChap05_Theorem_5_4_6_84 : CompleteSpace (E₂ × E₃) := inferInstance

/-- Helper for Theorem 5.4.6.8: squaring the Hessian local norm at a positive Hessian recovers
the underlying Hessian quadratic form. -/
private theorem sq_hessianLocalNorm_eq_inner_hessian_apply
    {Φ : E₂ × E₃ → ℝ} {p u : E₂ × E₃}
    (hH : (hessian Φ p).IsPositive) :
    ‖u‖[Φ; p] ^ (2 : ℕ) = inner ℝ u (hessian Φ p u) := by
  -- Positivity of the Hessian supplies the nonnegativity needed to square the local norm.
  have hquad : 0 ≤ inner ℝ u (hessian Φ p u) := hH.inner_nonneg_right u
  simpa [hessianLocalNorm_def] using Real.sq_sqrt hquad

/-- Helper for Theorem 5.4.6.8: a positive Hessian controls the squared mixed pairing by the
product of its diagonal quadratic forms. -/
private theorem sq_abs_inner_hessian_apply_le_hessian_quadratic_mul
    {Φ : E₂ × E₃ → ℝ} {p u v : E₂ × E₃}
    (hH : (hessian Φ p).IsPositive) :
    |inner ℝ (hessian Φ p u) v| ^ (2 : ℕ) ≤
      inner ℝ u (hessian Φ p u) * inner ℝ v (hessian Φ p v) := by
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

/-- Helper for Theorem 5.4.6.8: the mixed Hessian pairing is bounded by the product of the
Hessian local norms. -/
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

/-- Helper for Theorem 5.4.6.8: the lifted first derivative direction has Hessian local norm
`σ₁^(1/2)`. -/
private theorem lifted_direction_hessianLocalNorm_eq_sqrt_sigmaOne
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃} :
    ‖(fderiv ℝ ξ x d, (0 : E₃))‖[Φ; (ξ x, z)] =
      Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) := by
  -- Both sides are definitional presentations of the same Hessian quadratic form.
  rw [hessianLocalNorm_def, compositionPotentialSigmaOne_def]

/-- Helper for Theorem 5.4.6.8: the cross term is bounded by `σ₁^(1/2)` times the local norm of
the negative lifted second derivative direction. -/
private theorem cross_term_le_sqrt_sigmaOne_mul_neg_lifted_localNorm
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hH : (hessian Φ (ξ x, z)).IsPositive) :
    inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃)))
        (compositionSecondLiftedDirectionDerivative ξ x d) ≤
      Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) *
        ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)] := by
  have habs :=
    abs_inner_hessian_apply_le_hessianLocalNorm_mul
      (Φ := Φ) (p := (ξ x, z)) (u := (fderiv ℝ ξ x d, (0 : E₃)))
      (v := -compositionSecondLiftedDirectionDerivative ξ x d) hH
  have hone_sided :
      inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃)))
          (compositionSecondLiftedDirectionDerivative ξ x d) ≤
        ‖(fderiv ℝ ξ x d, (0 : E₃))‖[Φ; (ξ x, z)] *
          ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)] := by
    have habs' :
        |inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃)))
            (compositionSecondLiftedDirectionDerivative ξ x d)| ≤
          ‖(fderiv ℝ ξ x d, (0 : E₃))‖[Φ; (ξ x, z)] *
            ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)] := by
      have habs'' := habs
      rw [inner_neg_right, abs_neg] at habs''
      exact habs''
    -- Drop the absolute value on the left by the standard one-sided estimate.
    refine le_trans (le_abs_self _) ?_
    exact habs'
  rw [lifted_direction_hessianLocalNorm_eq_sqrt_sigmaOne] at hone_sided
  exact hone_sided

/-- Reusable owner-level bridge: if the Hessian of `Φ` is positive at `(ξ(x), z)` and the
negative lifted second derivative direction has local norm at most `σ₂`, then the mixed Hessian
cross term is bounded by `σ₁^(1/2) σ₂`. -/
theorem compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo_of_hessianPositive
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hH : (hessian Φ (ξ x, z)).IsPositive)
    (hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z d) :
    inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃)))
        (compositionSecondLiftedDirectionDerivative ξ x d) ≤
      Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) *
        compositionPotentialSigmaTwo Φ ξ x z d := by
  have hcross :=
    cross_term_le_sqrt_sigmaOne_mul_neg_lifted_localNorm
      (ξ := ξ) (x := x) (d := d) (z := z) hH
  -- Insert the given owner-level bound on the lifted second derivative direction.
  calc
    inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃)))
        (compositionSecondLiftedDirectionDerivative ξ x d) ≤
      Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) *
        ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)] :=
      hcross
    _ ≤ Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) *
          compositionPotentialSigmaTwo Φ ξ x z d := by
      exact mul_le_mul_of_nonneg_left
        hneg_liftedDirectionDerivative_le_sigmaTwo
        (Real.sqrt_nonneg _)

/-- Helper for Theorem 5.4.6.8: a recession direction of `Q₂` also preserves `interior Q₂`. -/
private theorem recessionDirection_add_smul_mem_interior
    {Q₂ : Set (E₂ × E₃)} {q : E₂ × E₃}
    (hQ₂_convex : Convex ℝ Q₂)
    (hrecession : ∀ ⦃p : E₂ × E₃⦄, p ∈ Q₂ → ∀ τ : ℝ, 0 ≤ τ → p + τ • q ∈ Q₂)
    {p : E₂ × E₃} (hp : p ∈ interior Q₂) {τ : ℝ} (hτ : 0 ≤ τ) :
    p + τ • q ∈ interior Q₂ := by
  let y : E₂ × E₃ := p + (2 * τ) • q
  have hy_mem : y ∈ Q₂ := by
    -- The recession hypothesis places the doubled forward step back in `Q₂`.
    simpa [y] using hrecession (interior_subset hp) (2 * τ) (by positivity)
  have hp_as_shift : y + (-(2 * τ)) • q ∈ interior Q₂ := by
    -- Shifting the doubled point back by the same amount recovers the original interior point.
    convert hp using 1
    simp [y, add_assoc]
  have hmid :=
    hQ₂_convex.add_smul_mem_interior hy_mem hp_as_shift
      (by norm_num : (1 / 2 : ℝ) ∈ Set.Ioc 0 1)
  have hsum : (2 * τ) • q + -τ • q = τ • q := by
    rw [← add_smul]
    ring_nf
  -- The midpoint of the doubled forward step and the original interior point is the desired point.
  convert hmid using 1
  rw [show y = p + (2 * τ) • q by rfl, smul_smul]
  have hcoeff : (1 / 2 : ℝ) * (-(2 * τ)) = -τ := by
    ring_nf
  rw [hcoeff]
  simpa [y, add_assoc] using congrArg (fun v : E₂ × E₃ ↦ p + v) hsum.symm

/-- Helper for Theorem 5.4.6.8: the barrier-owner pairing with the negative lifted second
direction is exactly the source-facing scalar `σ₂`. -/
private theorem negLiftedDirectionDerivative_gradientPair_eq_sigmaTwo
    {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hΦdiff : DifferentiableAt ℝ Φ (ξ x, z)) :
    inner ℝ (-∇ Φ (ξ x, z)) (-compositionSecondLiftedDirectionDerivative ξ x d) =
      compositionPotentialSigmaTwo Φ ξ x z d := by
  have hline :
      lineDeriv ℝ Φ (ξ x, z) (compositionSecondLiftedDirectionDerivative ξ x d) =
        compositionPotentialSigmaTwo Φ ξ x z d := by
    -- Specializing the product directional-derivative formula to `ξ = id` and direction `(s, 0)`
    -- turns the ambient derivative pairing into the `σ₂` expression.
    simpa [compositionPotential, compositionSecondLiftedDirectionDerivative,
      compositionPotentialSigmaTwo_def] using
      (compositionPotential_lineDeriv_eq_sum_partialGradient_pairings
        (Φ := Φ) (ξ := fun y : E₂ ↦ y) (x := ξ x)
        (h := vectorSecondDirectionalDerivative ξ x d) (z := z) (v := (0 : E₃))
        differentiableAt_id hΦdiff)
  calc
    inner ℝ (-∇ Φ (ξ x, z)) (-compositionSecondLiftedDirectionDerivative ξ x d)
        = inner ℝ (∇ Φ (ξ x, z)) (compositionSecondLiftedDirectionDerivative ξ x d) := by
            rw [compositionSecondLiftedDirectionDerivative, inner_neg_left, inner_neg_right]
            ring
    _ = lineDeriv ℝ Φ (ξ x, z) (compositionSecondLiftedDirectionDerivative ξ x d) := by
      symm
      rw [hΦdiff.lineDeriv_eq_fderiv, ← inner_gradient_left hΦdiff]
    _ = compositionPotentialSigmaTwo Φ ξ x z d := hline

-- Proof sketch: derive pointwise Hessian positivity at `(ξ(x), z)` from the self-concordant
-- barrier owner on `interior Q₂`, transfer the recession-direction hypothesis on `-l'` from `Q₂`
-- to `interior Q₂` using convexity, apply
-- `hessianLocalNorm_le_neg_gradient_inner_of_recession_direction` to obtain
-- `‖-l'‖[Φ; (ξ(x), z)] ≤ σ₂`, and then invoke
-- `compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo_of_hessianPositive`.
/-- Theorem 5.4.6.8: if `-l'` is a recession direction of `Q₂` and `Φ` is some
self-concordant barrier on `interior Q₂`, then at every `(ξ(x), z) ∈ interior Q₂` the cross
Hessian term
`⟪∇² Φ(ξ(x), z) (Dξ(x)[d], 0), Dl(x)[d]⟫` is bounded above by `σ₁^(1/2) σ₂`, where
`Dl(x)[d] = compositionSecondLiftedDirectionDerivative ξ x d`,
`σ₁ = ⟪∇² Φ(ξ(x), z) (Dξ(x)[d], 0), (Dξ(x)[d], 0)⟫`, and
`σ₂ = ⟪∇ᵧ Φ(ξ(x), z), D²ξ(x)[d, d]⟫`. -/
theorem compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo
    {Q₂ : Set (E₂ × E₃)} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂} {x d : E₁} {z : E₃}
    (hQ₂_convex : Convex ℝ Q₂)
    (hΦ : ∃ μ : NNReal, IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hyz : (ξ x, z) ∈ interior Q₂)
    (hrecession :
      ∀ ⦃p : E₂ × E₃⦄, p ∈ Q₂ → ∀ τ : ℝ, 0 ≤ τ →
        p + τ • (-compositionSecondLiftedDirectionDerivative ξ x d) ∈ Q₂) :
    inner ℝ (hessian Φ (ξ x, z) (fderiv ℝ ξ x d, (0 : E₃)))
        (compositionSecondLiftedDirectionDerivative ξ x d) ≤
      Real.sqrt (compositionPotentialSigmaOne Φ ξ x z d) *
        compositionPotentialSigmaTwo Φ ξ x z d := by
  rcases hΦ with ⟨μ, hΦμ⟩
  let hself : IsStandardSelfConcordantOn (interior Q₂) Φ :=
    hΦμ.toIsStandardSelfConcordantOn
  have hH : (hessian Φ (ξ x, z)).IsPositive :=
    hself.hessian_isPositive hyz
  have hΦdiff : DifferentiableAt ℝ Φ (ξ x, z) := by
    -- The barrier owner gives smoothness on the open barrier domain.
    exact (hself.contDiffOn.contDiffAt (hself.isOpen_domain.mem_nhds hyz)).differentiableAt
      (by norm_num)
  have hrecessionInterior :
      ∀ ⦃p : E₂ × E₃⦄, p ∈ interior Q₂ → ∀ τ : ℝ, 0 ≤ τ →
        p + τ • (-compositionSecondLiftedDirectionDerivative ξ x d) ∈ interior Q₂ := by
    intro p hp τ hτ
    -- Convexity upgrades the recession hypothesis from `Q₂` to `interior Q₂`.
    exact recessionDirection_add_smul_mem_interior hQ₂_convex hrecession hp hτ
  have hneg_liftedDirectionDerivative_le_sigmaTwo :
      ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)] ≤
        compositionPotentialSigmaTwo Φ ξ x z d := by
    -- The barrier recession estimate produces the local-norm bound, then the gradient pairing
    -- is rewritten to the source-facing `σ₂`.
    calc
      ‖-compositionSecondLiftedDirectionDerivative ξ x d‖[Φ; (ξ x, z)] ≤
          inner ℝ (-∇ Φ (ξ x, z)) (-compositionSecondLiftedDirectionDerivative ξ x d) :=
        hΦμ.hessianLocalNorm_le_neg_gradient_inner_of_recession_direction
          hrecessionInterior hyz
      _ = compositionPotentialSigmaTwo Φ ξ x z d :=
        negLiftedDirectionDerivative_gradientPair_eq_sigmaTwo (ξ := ξ) (x := x) (d := d)
          (z := z) hΦdiff
  -- Assemble the local Hessian-metric cross-term bound with the barrier-owner local-norm bound.
  exact compositionPotential_crossTerm_le_sqrt_sigmaOne_mul_sigmaTwo_of_hessianPositive
    (ξ := ξ) (x := x) (d := d) (z := z) hH
    hneg_liftedDirectionDerivative_le_sigmaTwo

end
