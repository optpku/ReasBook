/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Algorithm 10.66 is a `bridge/view` item in the Chapter 10 inner-product proximal-gradient API.

Domain sampling in the surrounding proximal-gradient layer identifies:
- `proximal_gradient_step` from Algorithm 10.1 as the `core/canonical` owner of one Euclidean
  prox-gradient update;
- `is_differentiable_at` from Definition 3.10 as the chapter owner for when the displayed
  derivative at `x^k` is the genuine textbook gradient;
- `IsMinOn` and `PosReal` as the canonical argmin and positive-curvature owners.

Primitive data for the bridge are only:
- the current iterate `x^k`;
- the positive curvature parameter `L_k`;
- the chapter owner hypothesis `is_differentiable_at f xk`, which packages exactly the finite
  domain and differentiability conditions needed for the source-facing quadratic model
  `proximal_gradient_curvature_model f g xk Lk`.

Derived API:
- the source-facing Euclidean model `proximal_gradient_curvature_model f g xk Lk`;
- a single argmin reformulation of the existing owner `proximal_gradient_step` through that
  model, with the quadratic coefficient written as `L_k / 2` and the constant term kept in the
  source-facing form `f(x^k)`.

So the public entry should remain a thin bridge theorem on the existing prox-step owner, rather
than a second update-rule wrapper or a low-level finiteness interface. -/

/-- The Euclidean prox-gradient curvature model at `x^k` with curvature parameter `L_k`. -/
def proximal_gradient_curvature_model (f g : E → EReal) (xk : E) (Lk : PosReal) : E → EReal :=
  fun x ↦
    ((f xk +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x - xk) : ℝ) : EReal)) +
      g x) +
      (((((Lk : ℝ) / 2) * ‖x - xk‖ ^ (2 : ℕ)) : ℝ) : EReal)

-- Proof sketch: unfold `proximal_gradient_curvature_model`; the statement is exactly the defining
-- formula of the Euclidean prox-gradient model.
/-- Evaluating `proximal_gradient_curvature_model f g xk Lk` at `x` expands to
`f(x^k) + ⟪∇ f(x^k), x - x^k⟫ + g(x) + (L_k / 2) ‖x - x^k‖²`. -/
@[simp] theorem proximal_gradient_curvature_model_apply
    (f g : E → EReal) (xk x : E) (Lk : PosReal) :
    proximal_gradient_curvature_model f g xk Lk x =
      ((f xk +
          ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x - xk) : ℝ) : EReal)) +
        g x) +
        (((((Lk : ℝ) / 2) * ‖x - xk‖ ^ (2 : ℕ)) : ℝ) : EReal) :=
  rfl

/-- Helper for Algorithm 10.66: the shifted quadratic term in the forward proximal objective
expands into the quadratic model at `xk`, the gradient pairing term, and an `x`-independent
constant. -/
lemma forward_shift_norm_sq_expansion
    (xk x gradk : E) (α : ℝ) :
    ‖x - (xk - α • gradk)‖ ^ (2 : ℕ) =
      ‖x - xk‖ ^ (2 : ℕ) + 2 * α * inner ℝ gradk (x - xk) + ‖α • gradk‖ ^ (2 : ℕ) := by
  -- Rewrite the shifted difference into the sum used by `norm_add_sq_real`.
  calc
    ‖x - (xk - α • gradk)‖ ^ (2 : ℕ) = ‖(x - xk) + α • gradk‖ ^ (2 : ℕ) := by
      congr 1
      abel
    _ = ‖x - xk‖ ^ (2 : ℕ) + inner ℝ (x - xk) (α • gradk) * 2 + ‖α • gradk‖ ^ (2 : ℕ) := by
      -- This is the standard real inner-product norm expansion.
      simpa [mul_comm] using norm_add_sq_real (x - xk) (α • gradk)
    _ = ‖x - xk‖ ^ (2 : ℕ) + 2 * α * inner ℝ gradk (x - xk) + ‖α • gradk‖ ^ (2 : ℕ) := by
      -- Expand the squared norm and rewrite the inner product into the textbook orientation.
      rw [real_inner_smul_right, real_inner_comm]
      ring

/-- Helper for Algorithm 10.66: multiplying an objective by a positive real scalar and adding a
finite real constant preserves its global minimizers over `Set.univ`. -/
lemma isMinOn_univ_iff_of_pos_mul_add_const
    {φ ψ : E → EReal} {z : E} {a c : ℝ} (ha : 0 < a)
    (hobj : ∀ x, φ x = (((a : ℝ) : EReal) * ψ x) + (c : EReal)) :
    IsMinOn φ Set.univ z ↔ IsMinOn ψ Set.univ z := by
  have hscale_pos : 0 < ((a : ℝ) : EReal) := by
    exact_mod_cast ha
  have hscale_top : ((a : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hscale_bot : ((a : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hscale_zero : ((a : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast ha.ne'
  rw [isMinOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro hz x
    -- Cancel the additive constant, then divide by the positive scale.
    have hzx := hz x
    rw [hobj z, hobj x] at hzx
    have hscaled :
        (((a : ℝ) : EReal) * ψ z) ≤ (((a : ℝ) : EReal) * ψ x) :=
      ((EReal.addLECancellable_coe c).add_le_add_iff_right).mp hzx
    have hdiv :
        ((((a : ℝ) : EReal) * ψ z) / ((a : ℝ) : EReal)) ≤
          ((((a : ℝ) : EReal) * ψ x) / ((a : ℝ) : EReal)) :=
      EReal.monotone_div_right_of_nonneg hscale_pos.le hscaled
    rw [mul_comm (((a : ℝ) : EReal)) (ψ z), mul_comm (((a : ℝ) : EReal)) (ψ x)] at hdiv
    rw [← EReal.mul_div_right, ← EReal.mul_div_right,
      EReal.div_mul_cancel hscale_bot hscale_top hscale_zero,
      EReal.div_mul_cancel hscale_bot hscale_top hscale_zero] at hdiv
    exact hdiv
  · intro hz x
    -- Multiply the minimizing inequality by the nonnegative scale and reinsert the constant.
    have hscaled :
        (((a : ℝ) : EReal) * ψ z) ≤ (((a : ℝ) : EReal) * ψ x) :=
      mul_le_mul_of_nonneg_left (hz x) hscale_pos.le
    have hshifted := ((EReal.addLECancellable_coe c).add_le_add_iff_right).mpr hscaled
    calc
      φ z = (((a : ℝ) : EReal) * ψ z) + (c : EReal) := hobj z
      _ ≤ (((a : ℝ) : EReal) * ψ x) + (c : EReal) := hshifted
      _ = φ x := (hobj x).symm

/-- Helper for Algorithm 10.66: the forward proximal objective used in
`proximal_gradient_step` is a positive scalar multiple of the Euclidean curvature model plus an
`x`-independent finite constant. -/
lemma proximal_gradient_forward_objective_eq_scaled_curvature_model
    {f g : E → EReal} {xk : E} {Lk : PosReal}
    (hfxk : is_differentiable_at f xk) :
    ∃ c : ℝ, ∀ x,
      proximal_objective ((((1 / Lk : PosReal) : EReal) • g))
          (xk - (1 / (Lk : ℝ)) • ∇ (fun y ↦ (f y).toReal) xk) x =
        ((((1 / (Lk : ℝ)) : ℝ) : EReal) * proximal_gradient_curvature_model f g xk Lk x) +
          (c : EReal) := by
  let α : ℝ := 1 / (Lk : ℝ)
  let gradk : E := ∇ (fun y ↦ (f y).toReal) xk
  let c : ℝ := ((1 / 2 : ℝ) * ‖α • gradk‖ ^ (2 : ℕ)) - α * (f xk).toReal
  refine ⟨c, ?_⟩
  intro x
  have hxk_finite : xk ∈ finite_domain f := interior_subset hfxk.1
  have hxk_top : f xk ≠ ⊤ := (mem_finite_domain.mp hxk_finite).1.ne
  have hxk_bot : f xk ≠ ⊥ := (mem_finite_domain.mp hxk_finite).2
  have hxk_value : (((f xk).toReal : ℝ) : EReal) = f xk :=
    EReal.coe_toReal hxk_top hxk_bot
  have hLk_ne : (Lk : ℝ) ≠ 0 := ne_of_gt (PosReal.coe_pos Lk)
  have hscale : α * ((Lk : ℝ) / 2) = 1 / 2 := by
    calc
      α * ((Lk : ℝ) / 2) = ((1 / (Lk : ℝ)) * (Lk : ℝ)) / 2 := by
        dsimp [α]
        ring
      _ = 1 / 2 := by
        rw [one_div, inv_mul_cancel₀ hLk_ne]
  have hquadratic :
      ((1 / 2 : ℝ) *
          (‖x - xk‖ ^ (2 : ℕ) + 2 * α * inner ℝ gradk (x - xk) + ‖α • gradk‖ ^ (2 : ℕ))) =
        (1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) +
          α * inner ℝ gradk (x - xk) +
          (1 / 2 : ℝ) * ‖α • gradk‖ ^ (2 : ℕ) := by
    ring
  have hreal :
      (1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) +
          α * inner ℝ gradk (x - xk) +
          (1 / 2 : ℝ) * ‖α • gradk‖ ^ (2 : ℕ) =
        α * ((f xk).toReal + inner ℝ gradk (x - xk) + ((Lk : ℝ) / 2) * ‖x - xk‖ ^ (2 : ℕ)) + c := by
    -- Collect the `x`-dependent terms into the scaled curvature model and leave the remainder as
    -- the constant term `c`.
    have hquadratic_scale :
        (1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) =
          α * (((Lk : ℝ) / 2) * ‖x - xk‖ ^ (2 : ℕ)) := by
      calc
        (1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) = (α * ((Lk : ℝ) / 2)) * ‖x - xk‖ ^ (2 : ℕ) := by
          rw [hscale]
        _ = α * (((Lk : ℝ) / 2) * ‖x - xk‖ ^ (2 : ℕ)) := by
          ring
    rw [hquadratic_scale]
    dsimp [c]
    ring
  have hquadratic_ereal := congrArg (fun t : ℝ ↦ (t : EReal)) hquadratic
  have hreal_ereal := congrArg (fun t : ℝ ↦ (t : EReal)) hreal
  -- Rewrite the forward proximal objective and then match the remaining real terms.
  calc
    proximal_objective ((((1 / Lk : PosReal) : EReal) • g))
        (xk - (1 / (Lk : ℝ)) • ∇ (fun y ↦ (f y).toReal) xk) x =
      (((α : ℝ) : EReal) * g x) +
        ((((1 / 2 : ℝ) * ‖x - xk‖ ^ (2 : ℕ) +
            α * inner ℝ gradk (x - xk) +
            (1 / 2 : ℝ) * ‖α • gradk‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
      -- Expand the shifted quadratic penalty around the forward point.
      rw [proximal_objective_apply, Pi.smul_apply, smul_eq_mul,
        forward_shift_norm_sq_expansion xk x gradk α]
      exact congrArg (fun t : EReal ↦ (((α : ℝ) : EReal) * g x) + t) hquadratic_ereal
    _ =
      ((α : ℝ) : EReal) * g x +
        (((α * ((f xk).toReal + inner ℝ gradk (x - xk) +
            ((Lk : ℝ) / 2) * ‖x - xk‖ ^ (2 : ℕ)) + c : ℝ) : EReal)) := by
      exact congrArg (fun t : EReal ↦ (((α : ℝ) : EReal) * g x) + t) hreal_ereal
    _ =
      ((((1 / (Lk : ℝ)) : ℝ) : EReal) * proximal_gradient_curvature_model f g xk Lk x) +
        (c : EReal) := by
      -- Rewrite the remaining real expression into the scaled curvature model.
      have hscale_nonneg : 0 ≤ ((((1 / (Lk : ℝ)) : ℝ) : EReal)) := by
        exact_mod_cast one_div_nonneg.mpr Lk.2.le
      have hscale_ne_top : ((((1 / (Lk : ℝ)) : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top _
      let scale : EReal := (((1 / (Lk : ℝ)) : ℝ) : EReal)
      let innerTerm : EReal := ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x - xk) : ℝ) : EReal)
      let quadTerm : EReal := (((((Lk : ℝ) / 2) * ‖x - xk‖ ^ (2 : ℕ)) : ℝ) : EReal)
      simp [α, gradk, c, proximal_gradient_curvature_model_apply, hxk_value, EReal.coe_add,
        EReal.coe_mul, sub_eq_add_neg, scale, innerTerm, quadTerm]
      have hdistrib :
          scale * (f xk + innerTerm + g x + quadTerm) =
            scale * g x + scale * (f xk + innerTerm + quadTerm) := by
        calc
          scale * (f xk + innerTerm + g x + quadTerm) =
              scale * ((f xk + innerTerm + quadTerm) + g x) := by
            simp [add_assoc, add_left_comm, add_comm]
          _ = scale * (f xk + innerTerm + quadTerm) + scale * g x := by
            exact EReal.left_distrib_of_nonneg_of_ne_top hscale_nonneg hscale_ne_top _ _
          _ = scale * g x + scale * (f xk + innerTerm + quadTerm) := by
            simp [add_assoc, add_left_comm, add_comm]
      have hdistrib_explicit :
          ((((1 / (Lk : ℝ)) : ℝ) : EReal) *
              (f xk +
                ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x - xk) : ℝ) : EReal) +
                g x +
                (((((Lk : ℝ) / 2) * ‖x - xk‖ ^ (2 : ℕ)) : ℝ) : EReal))) =
            ((((1 / (Lk : ℝ)) : ℝ) : EReal) * g x) +
              ((((1 / (Lk : ℝ)) : ℝ) : EReal) *
                (f xk +
                  ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x - xk) : ℝ) : EReal) +
                  (((((Lk : ℝ) / 2) * ‖x - xk‖ ^ (2 : ℕ)) : ℝ) : EReal))) := by
        simpa [scale, innerTerm, quadTerm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
          hdistrib
      have hdistrib_target :
          ((((1 / (Lk : ℝ)) : ℝ) : EReal) *
              (f xk +
                ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x + -xk) : ℝ) : EReal) +
                g x +
                (((((Lk : ℝ) / 2) * ‖x + -xk‖ ^ (2 : ℕ)) : ℝ) : EReal))) =
            ((((1 / (Lk : ℝ)) : ℝ) : EReal) * g x) +
              ((((1 / (Lk : ℝ)) : ℝ) : EReal) *
                (f xk +
                  ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x + -xk) : ℝ) : EReal) +
                  (((((Lk : ℝ) / 2) * ‖x + -xk‖ ^ (2 : ℕ)) : ℝ) : EReal))) := by
        simpa [sub_eq_add_neg] using hdistrib_explicit
      let tail : EReal :=
        (((((1 / 2 : ℝ) * ‖(1 / (Lk : ℝ)) • ∇ (fun y ↦ (f y).toReal) xk‖ ^ (2 : ℕ)) : ℝ) :
          EReal)) + -(((((1 / (Lk : ℝ)) : ℝ) : EReal) * f xk))
      have htail :
          ((((1 / (Lk : ℝ)) : ℝ) : EReal) * g x) +
              ((((1 / (Lk : ℝ)) : ℝ) : EReal) *
                  (f xk +
                    ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x + -xk) : ℝ) : EReal) +
                    (((((Lk : ℝ) / 2) * ‖x + -xk‖ ^ (2 : ℕ)) : ℝ) : EReal))) +
                tail =
            ((((1 / (Lk : ℝ)) : ℝ) : EReal) *
                (f xk +
                  ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x + -xk) : ℝ) : EReal) +
                  g x +
                  (((((Lk : ℝ) / 2) * ‖x + -xk‖ ^ (2 : ℕ)) : ℝ) : EReal))) +
              tail := by
        simpa [add_assoc] using congrArg (fun t : EReal ↦ t + tail) hdistrib_target.symm
      simpa [tail, add_assoc] using htail

-- Proof sketch: expand membership in `proximal_gradient_step f g xk Lk`, rewrite the scaled
-- proximal objective at the forward point, and cancel the positive scalar factor `Lk` together
-- with the additive constant independent of the minimization variable. The Chapter 3 hypothesis
-- `is_differentiable_at f xk` is the source-facing owner recording that the displayed gradient is
-- the genuine textbook gradient at `x^k`, while also supplying the local finiteness of `f xk`
-- needed to keep the constant term in the canonical source form `f xk`.
/-- Algorithm 10.66: a point `x^(k+1)` is a valid proximal-gradient update from `x^k` with
curvature parameter `L_k` exactly when it globally minimizes the linearized quadratic model
`x ↦ f(x^k) + ⟪∇ f(x^k), x - x^k⟫ + g(x) + (L_k / 2) ‖x - x^k‖²` whenever `f` is differentiable
at `x^k` in the Chapter 3 sense, so the displayed gradient is the genuine textbook gradient
there. -/
theorem mem_proximal_gradient_step_iff_isMinOn_curvature_model
    {f g : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hfxk : is_differentiable_at f xk) :
    xNext ∈ proximal_gradient_step f g xk Lk ↔
      IsMinOn (proximal_gradient_curvature_model f g xk Lk) Set.univ xNext := by
  rcases proximal_gradient_forward_objective_eq_scaled_curvature_model
      (f := f) (g := g) (xk := xk) (Lk := Lk) hfxk with ⟨c, hobjective⟩
  -- Convert proximal-step membership to global minimization of the forward proximal objective.
  rw [mem_proximal_gradient_step_iff, mem_proximal_mapping_iff]
  -- Then remove the positive scalar and additive constant from the objective.
  exact
    isMinOn_univ_iff_of_pos_mul_add_const
      (z := xNext) (a := 1 / (Lk : ℝ)) (c := c) (one_div_pos.mpr Lk.2) hobjective

end
