/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SeminormDualNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Primary domain: first-order consequences of strong convexity on real inner-product spaces, with
the later dual-norm bounds living on the finite-dimensional separated-seminorm layer.

Sampled owner-style declarations before refining this file:
* mathlib `StrongConvexOn`
* project `StrongConvexOnWith` in `Definition_2_14`
* project `StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt` in `Definition_2_14`
* project `Seminorm.inner_le_dualNorm_mul` in `Definition_2_5`

Source/core/bridge triage:
* source-facing: the three displayed inequalities of Theorem 2.11
* core/canonical: `StrongConvexOnWith p μ Set.univ f`
* bridge/view: `StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt` and the
  finite-dimensional dual pairing estimate `Seminorm.inner_le_dualNorm_mul`

Primitive data:
* `hf_strong : StrongConvexOnWith p μ Set.univ f`
* local pointwise differentiability / gradient witnesses at the evaluation points `x` and `y`
* only for the later dual-norm inequalities: the finite-dimensional real inner-product-space
  structure and the separation hypothesis `[Seminorm.IsNorm p]`

Derived API:
* `hf_strong.lower_tangent_quadratic_of_hasGradientAt`
* `DifferentiableAt.hasGradientAt`
* the strong-monotonicity pairing estimate obtained by adding the lower-tangent inequalities at
  `(x, y)` and `(y, x)`
* `Seminorm.inner_le_dualNorm_mul` for the later dual-norm comparisons
-/

namespace StrongConvexOnWith

section Pairing

variable [CompleteSpace E]

variable {p : Seminorm ℝ E} {μ : ℝ} {f : E → ℝ}

/-- Strong convexity with respect to `p` forces the gradient pairing to dominate `μ` times the
squared `p`-distance. This is the core bridge behind the displayed dual-norm consequences below.
-/
-- Proof sketch: apply `lower_tangent_quadratic_of_hasGradientAt` at `(x, y)` and `(y, x)`, add the
-- two inequalities, and simplify the linear terms.
theorem pairing_lower_bound
    (hf_strong : StrongConvexOnWith p μ Set.univ f)
    (x y : E) (hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y) :
    μ * (p (x - y)) ^ 2 ≤ inner ℝ (∇ f x - ∇ f y) (x - y) := by
  -- Apply the lower tangent inequality at both endpoint orders.
  have hxy :=
    StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt (hf := hf_strong)
      (x := x) (y := y) (g := ∇ f x) (by trivial) (by trivial) hx.hasGradientAt
  have hyx :=
    StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt (hf := hf_strong)
      (x := y) (y := x) (g := ∇ f y) (by trivial) (by trivial) hy.hasGradientAt
  -- Rewrite the seminorm term from `p (y - x)` back to `p (x - y)` before adding.
  have hp_rev : p (y - x) = p (x - y) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (map_neg_eq_map p (x - y))
  rw [hp_rev] at hxy
  have hsum :
      μ * (p (x - y)) ^ 2 ≤
        -(inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y)) := by
    nlinarith [hxy, hyx]
  -- Rewrite the sum of the two linear terms as the single gradient pairing.
  have hpair :
      -(inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y)) =
        inner ℝ (∇ f x - ∇ f y) (x - y) := by
    calc
      -(inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f y) (x - y))
          = inner ℝ (∇ f x) (x - y) - inner ℝ (∇ f y) (x - y) := by
              have hxswap : inner ℝ (∇ f x) (y - x) = -inner ℝ (∇ f x) (x - y) := by
                have hvec : y - x = -(x - y) := by
                  abel
                rw [hvec, inner_neg_right]
              rw [hxswap]
              ring
      _ = inner ℝ (∇ f x - ∇ f y) (x - y) := by
            rw [inner_sub_left]
  -- The linear terms collapse to the single gradient pairing.
  rwa [hpair] at hsum

end Pairing

section DualNorm

variable [FiniteDimensional ℝ E]

local instance finiteDimensionalComplete : CompleteSpace E := FiniteDimensional.complete ℝ E

variable {p : Seminorm ℝ E} [Seminorm.IsNorm p] {μ : ℝ} {f : E → ℝ}

/-- Theorem 2.11 (1): if a `μ`-strongly convex function has gradients at `x` and `y`, then its
value at `y` is bounded above by the tangent model at `x` plus a quadratic term in the dual norm
of the gradient difference. Here strong convexity is the whole-space specialization
`StrongConvexOnWith p μ Set.univ f`. -/
-- Proof sketch: apply strong convexity to the translated function
-- `v ↦ f v - ⟪∇ f x, v⟫`, observe that `x` is its minimizer, and compute the optimal value of the
-- resulting quadratic lower bound using the dual norm.
theorem tangent_upper_bound_by_dualNorm
    (hf_strong : StrongConvexOnWith p μ Set.univ f)
    (x y : E) (_hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y) :
    f y ≤ f x + inner ℝ (∇ f x) (y - x) +
      (1 / (2 * μ)) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
  have hμ : 0 < μ := hf_strong.2.1
  -- Start from the lower tangent inequality at base point `y`.
  have hlower :=
    StrongConvexOnWith.lower_tangent_quadratic_of_hasGradientAt (hf := hf_strong)
      (x := y) (y := x) (g := ∇ f y) (by trivial) (by trivial) hy.hasGradientAt
  -- Control the residual pairing by dual Cauchy.
  have hinner :
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
        ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
    Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
  let a : ℝ := ‖∇ f x - ∇ f y‖[p,*]
  let s : ℝ := p (x - y)
  -- Complete the square in the scalar variables `a` and `s`.
  have hsquare : 0 ≤ (a - μ * s) ^ 2 := sq_nonneg (a - μ * s)
  have htwoμ_pos : 0 < 2 * μ := by
    positivity
  have hscaled : (2 * μ) * (a * s - (μ / 2) * s ^ 2) ≤ a ^ 2 := by
    nlinarith [hsquare]
  have hscalar :
      a * s - (μ / 2) * s ^ 2 ≤ (1 / (2 * μ)) * a ^ 2 := by
    have htmp : a * s - (μ / 2) * s ^ 2 ≤ (2 * μ)⁻¹ * a ^ 2 :=
      (le_inv_mul_iff₀ htwoμ_pos).2 hscaled
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using htmp
  have hestimate :
      inner ℝ (∇ f x - ∇ f y) (x - y) - (μ / 2) * (p (x - y)) ^ 2 ≤
        (1 / (2 * μ)) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
    calc
      inner ℝ (∇ f x - ∇ f y) (x - y) - (μ / 2) * (p (x - y)) ^ 2
          ≤ ‖∇ f x - ∇ f y‖[p,*] * p (x - y) - (μ / 2) * (p (x - y)) ^ 2 := by
            linarith
      _ ≤ (1 / (2 * μ)) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
            simpa [a, s] using hscalar
  have hxswap : inner ℝ (∇ f x) (y - x) = -inner ℝ (∇ f x) (x - y) := by
    have hvec : y - x = -(x - y) := by
      abel
    rw [hvec, inner_neg_right]
  have hlin :
      inner ℝ (∇ f x) (y - x) + inner ℝ (∇ f x - ∇ f y) (x - y) =
        -inner ℝ (∇ f y) (x - y) := by
    rw [inner_sub_left, hxswap]
    ring
  have hrew :
      f y ≤ f x + inner ℝ (∇ f x) (y - x) +
        (inner ℝ (∇ f x - ∇ f y) (x - y) - (μ / 2) * (p (x - y)) ^ 2) := by
    -- Rewrite the base-point gradient term from `∇ f y` to `∇ f x`.
    nlinarith [hlower, hlin]
  exact hrew.trans <| by
    gcongr

/-- Theorem 2.11 (2): the gradient pairing is bounded above by `μ⁻¹` times the squared dual norm
of the gradient difference. -/
-- Proof sketch: add the inequality from `tangent_upper_bound_by_dualNorm` to the same inequality
-- with `x` and `y` interchanged, then simplify the linear terms.
theorem gradient_pairing_le_dualNorm_sq
    (hf_strong : StrongConvexOnWith p μ Set.univ f)
    (x y : E) (hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y) :
    inner ℝ (∇ f x - ∇ f y) (x - y) ≤
      (1 / μ) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
  have hμ : 0 < μ := hf_strong.2.1
  -- Combine the strong lower pairing bound with dual Cauchy.
  have hlower := StrongConvexOnWith.pairing_lower_bound hf_strong x y hx hy
  have hupper :
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
        ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
    Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
  by_cases hxy : x = y
  · subst hxy
    have hzero : ‖(0 : E)‖[p,*] = 0 := by
      rw [Seminorm.dualNorm_apply]
      have himage :
          (fun a : E ↦ inner ℝ (0 : E) a) '' {x : E | p x ≤ 1} = ({0} : Set ℝ) := by
        ext t
        constructor
        · rintro ⟨z, -, rfl⟩
          simp
        · rintro rfl
          refine ⟨0, ?_, by simp⟩
          simp
      rw [himage]
      simp
    simp [hzero]
  · have hsub_ne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hp_pos : 0 < p (x - y) := Seminorm.map_pos_of_ne_zero p hsub_ne
    have hsandwich :
        μ * (p (x - y)) ^ 2 ≤ ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
      hlower.trans hupper
    have hgrad : μ * p (x - y) ≤ ‖∇ f x - ∇ f y‖[p,*] := by
      nlinarith [hsandwich, hp_pos]
    have hdual_nonneg : 0 ≤ ‖∇ f x - ∇ f y‖[p,*] := by
      nlinarith [hgrad, hμ, hp_pos]
    have hp_le :
        p (x - y) ≤ ‖∇ f x - ∇ f y‖[p,*] / μ := by
      refine (le_div_iff₀ hμ).2 ?_
      simpa [mul_comm] using hgrad
    have hnorm_mul :
        ‖∇ f x - ∇ f y‖[p,*] * p (x - y) ≤
          (1 / μ) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
      calc
        ‖∇ f x - ∇ f y‖[p,*] * p (x - y) ≤
            ‖∇ f x - ∇ f y‖[p,*] * (‖∇ f x - ∇ f y‖[p,*] / μ) := by
              exact mul_le_mul_of_nonneg_left hp_le hdual_nonneg
        _ = (1 / μ) * ‖∇ f x - ∇ f y‖[p,*] ^ 2 := by
              ring_nf
    -- Substitute the gradient-difference norm bound back into the upper pairing estimate.
    exact hupper.trans hnorm_mul

/-- Theorem 2.11 (3): the dual norm of the gradient difference dominates `μ` times the primal norm
of the displacement. -/
-- Proof sketch: combine `pairing_lower_bound` with the dual Cauchy--Schwarz inequality
-- `⟪g, z⟫ ≤ ‖g‖_* ‖z‖`, then cancel the common factor `p (x - y)`.
theorem le_dualNorm_gradient_sub
    (hf_strong : StrongConvexOnWith p μ Set.univ f)
    (x y : E) (hx : DifferentiableAt ℝ f x) (hy : DifferentiableAt ℝ f y) :
    μ * p (x - y) ≤ ‖∇ f x - ∇ f y‖[p,*] := by
  -- Sandwich the gradient pairing between the strong lower bound and dual Cauchy.
  have hlower := StrongConvexOnWith.pairing_lower_bound (hf_strong := hf_strong) x y hx hy
  have hupper :
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
        ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
    Seminorm.inner_le_dualNorm_mul p (x - y) (∇ f x - ∇ f y)
  by_cases hxy : x = y
  · subst hxy
    have hzero : ‖(0 : E)‖[p,*] = 0 := by
      rw [Seminorm.dualNorm_apply]
      have himage :
          (fun a : E ↦ inner ℝ (0 : E) a) '' {x : E | p x ≤ 1} = ({0} : Set ℝ) := by
        ext t
        constructor
        · rintro ⟨z, -, rfl⟩
          simp
        · rintro rfl
          refine ⟨0, ?_, by simp⟩
          simp
      rw [himage]
      simp
    simp [hzero]
  · have hsub_ne : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hp_pos : 0 < p (x - y) := Seminorm.map_pos_of_ne_zero p hsub_ne
    have hsandwich :
        μ * (p (x - y)) ^ 2 ≤ ‖∇ f x - ∇ f y‖[p,*] * p (x - y) :=
      hlower.trans hupper
    -- Cancel the positive factor `p (x - y)` on both sides.
    nlinarith [hsandwich, hp_pos]

end DualNorm

end StrongConvexOnWith

end
