/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_42
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f g : E → EReal} {Lf : NNReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/-
Lemma 10.10 is `source-facing`: it asserts Lipschitz regularity of the Chapter 10 owner
`gradient_mapping`. The canonical abstraction for that regularity is mathlib's `LipschitzWith`,
while the residual map itself remains the source-facing owner `G[L, f, g]`.
-/

-- Proof sketch: use the nonexpansiveness of the proximal map defining `T_L`, estimate
-- `‖T_L(x) - T_L(y)‖` by the distance between the two forward-gradient points, and then use the
-- `L_f`-Lipschitz control of `∇ (f.toReal)` on `interior (effective_domain f)` from `hf_smooth`.
/-- Lemma 10.10 (1): for a proper closed convex `g` and an `L_f`-smooth extended-real-valued
function `f` on `interior (effective_domain f)`, the gradient mapping `G_L` is
`(2L + L_f)`-Lipschitz on `interior (effective_domain f)`. -/
theorem gradient_mapping_lipschitz
    (hf_smooth :
      is_l_smooth_on (fun x ↦ (f x).toReal) (interior (effective_domain f)) Lf)
    (L : PosReal) :
    LipschitzWith (2 * PosReal.toNNReal L + Lf) (G[L, f, g]) := by
  -- First identify the Chapter 10 prox-grad update with the singleton proximal point of the
  -- scaled penalty at the forward-gradient input.
  have prox_grad_operator_eq_scaled_prox_singleton :
      ∀ x : interior (effective_domain f),
        prox[((((1 / L : PosReal) : EReal) • g))]
            ((x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E)) =
          {T[L, f, g] x} := by
    intro x
    -- Unfold the Chapter 10 step owner to expose the Chapter 6 proximal singleton theorem.
    simpa [proximal_gradient_step] using
      (prox_grad_operator_eq_singleton f g L x)
  -- Then transfer Chapter 6 proximal nonexpansiveness to the Chapter 10 prox-grad operator.
  have prox_grad_operator_norm_sub_le_forward_point :
      ∀ x y : interior (effective_domain f),
        ‖T[L, f, g] x - T[L, f, g] y‖ ≤
          ‖(((x : E) - (1 / L : ℝ) • ∇ (fun z ↦ (f z).toReal) (x : E)) -
              ((y : E) - (1 / L : ℝ) • ∇ (fun z ↦ (f z).toReal) (y : E)))‖ := by
    intro x y
    let hg_closed : LowerSemicontinuous g := Fact.out
    let hg_convex : is_convex_function g := Fact.out
    let hg_scaled :=
      scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / L)
    -- Apply the Chapter 6 nonexpansiveness theorem to the two singleton proximal points.
    simpa using
      (@prox_eq_singleton_nonexpansive E _ _
        ((((1 / L : PosReal) : EReal) • g))
        ((x : E) - (1 / L : ℝ) • ∇ (fun z ↦ (f z).toReal) (x : E))
        ((y : E) - (1 / L : ℝ) • ∇ (fun z ↦ (f z).toReal) (y : E))
        (T[L, f, g] x)
        (T[L, f, g] y)
        hg_scaled.1
        hg_scaled.2.1
        hg_scaled.2.2
        (prox_grad_operator_eq_scaled_prox_singleton x)
        (prox_grad_operator_eq_scaled_prox_singleton y))
  -- Finally estimate the forward-gradient points using the `L_f`-Lipschitz gradient bound.
  have forward_gradient_point_norm_sub_le :
      ∀ x y : interior (effective_domain f),
        ‖(((x : E) - (1 / L : ℝ) • ∇ (fun z ↦ (f z).toReal) (x : E)) -
            ((y : E) - (1 / L : ℝ) • ∇ (fun z ↦ (f z).toReal) (y : E)))‖ ≤
          (1 + (Lf : ℝ) / (L : ℝ)) * ‖(x : E) - y‖ := by
    rw [is_l_smooth_on_iff_forall_norm_sub_le] at hf_smooth
    intro x y
    have hgrad :
        ‖∇ (fun z ↦ (f z).toReal) (x : E) - ∇ (fun z ↦ (f z).toReal) (y : E)‖ ≤
          (Lf : ℝ) * ‖(x : E) - y‖ :=
      hf_smooth.2 (x : E) x.2 (y : E) y.2
    have hLinv_nonneg : 0 ≤ (1 / (L : ℝ)) := by
      exact le_of_lt (one_div_pos.mpr L.2)
    have hscaled :
        ‖(1 / (L : ℝ)) •
            (∇ (fun z ↦ (f z).toReal) (x : E) -
              ∇ (fun z ↦ (f z).toReal) (y : E))‖ ≤
          ((Lf : ℝ) / (L : ℝ)) * ‖(x : E) - y‖ := by
      calc
        ‖(1 / (L : ℝ)) •
            (∇ (fun z ↦ (f z).toReal) (x : E) -
              ∇ (fun z ↦ (f z).toReal) (y : E))‖
            = (1 / (L : ℝ)) *
                ‖∇ (fun z ↦ (f z).toReal) (x : E) -
                    ∇ (fun z ↦ (f z).toReal) (y : E)‖ := by
              rw [norm_smul, Real.norm_of_nonneg hLinv_nonneg]
        _ ≤ (1 / (L : ℝ)) * ((Lf : ℝ) * ‖(x : E) - y‖) := by
              gcongr
        _ = ((Lf : ℝ) / (L : ℝ)) * ‖(x : E) - y‖ := by
              ring
    -- Split the forward-point difference into the identity part plus the scaled gradient gap.
    calc
      ‖(((x : E) - (1 / L : ℝ) • ∇ (fun z ↦ (f z).toReal) (x : E)) -
            ((y : E) - (1 / L : ℝ) • ∇ (fun z ↦ (f z).toReal) (y : E)))‖
          ≤ ‖(x : E) - y‖ +
              ‖(1 / (L : ℝ)) •
                (∇ (fun z ↦ (f z).toReal) (x : E) -
                  ∇ (fun z ↦ (f z).toReal) (y : E))‖ := by
            simpa [smul_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
              (norm_sub_le
                ((x : E) - y)
                ((1 / (L : ℝ)) •
                  (∇ (fun z ↦ (f z).toReal) (x : E) -
                    ∇ (fun z ↦ (f z).toReal) (y : E))))
      _ ≤ ‖(x : E) - y‖ + (((Lf : ℝ) / (L : ℝ)) * ‖(x : E) - y‖) := by
            gcongr
      _ = (1 + (Lf : ℝ) / (L : ℝ)) * ‖(x : E) - y‖ := by
            ring
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  have hL_nonneg : 0 ≤ (L : ℝ) := le_of_lt L.2
  have hcoeff_nonneg : 0 ≤ ((2 : ℝ) * (L : ℝ) + (Lf : ℝ)) := by
    positivity
  have hstep :
      ‖T[L, f, g] x - T[L, f, g] y‖ ≤
        (1 + (Lf : ℝ) / (L : ℝ)) * ‖(x : E) - y‖ := by
    exact le_trans
      (prox_grad_operator_norm_sub_le_forward_point x y)
      (forward_gradient_point_norm_sub_le x y)
  have hresidual :
      ‖G[L, f, g] x - G[L, f, g] y‖ ≤
        (((2 : ℝ) * (L : ℝ)) + (Lf : ℝ)) * ‖(x : E) - y‖ := by
    -- Rewrite `G_L` as `L • (id - T_L)` and then use the two previously established bounds.
    rw [gradient_mapping_apply, gradient_mapping_apply]
    calc
      ‖(L : ℝ) • ((x : E) - T[L, f, g] x) - (L : ℝ) • ((y : E) - T[L, f, g] y)‖
          = (L : ℝ) * ‖((x : E) - y) - (T[L, f, g] x - T[L, f, g] y)‖ := by
            rw [← smul_sub, norm_smul, Real.norm_of_nonneg hL_nonneg]
            congr 1
            abel
      _ ≤ (L : ℝ) * (‖(x : E) - y‖ + ‖T[L, f, g] x - T[L, f, g] y‖) := by
            gcongr
            exact norm_sub_le ((x : E) - y) (T[L, f, g] x - T[L, f, g] y)
      _ ≤ (L : ℝ) * (‖(x : E) - y‖ + (1 + (Lf : ℝ) / (L : ℝ)) * ‖(x : E) - y‖) := by
            gcongr
      _ = (((2 : ℝ) * (L : ℝ)) + (Lf : ℝ)) * ‖(x : E) - y‖ := by
            field_simp [show (L : ℝ) ≠ 0 from L.2.ne']
            ring
  simpa [Subtype.dist_eq, dist_eq_norm, Real.toNNReal_of_nonneg hcoeff_nonneg] using hresidual

-- Proof sketch: specialize `gradient_mapping_lipschitz` to the positive smoothness parameter `L`;
-- the coefficient `(2L + L)` simplifies to `3L`. The theorem surface keeps that specialization on
-- the chapter's canonical positive-parameter owner `PosReal`, rather than spelling the stepsize as
-- a proof-packed subtype literal.
/-- Lemma 10.10 (2): when the smoothness constant is represented by a positive parameter `L`, the
gradient mapping `G_L` is `3L`-Lipschitz on `interior (effective_domain f)`. -/
theorem gradient_mapping_lipschitz_at_smoothness_constant
    (L : PosReal)
    (hf_smooth :
      is_l_smooth_on (fun x ↦ (f x).toReal) (interior (effective_domain f))
        (PosReal.toNNReal L)) :
    LipschitzWith (3 * PosReal.toNNReal L) (G[L, f, g]) := by
  have hcoeff :
      3 * PosReal.toNNReal L =
        2 * PosReal.toNNReal L + PosReal.toNNReal L := by
    ext
    ring_nf
  rw [hcoeff]
  exact gradient_mapping_lipschitz hf_smooth L

end
