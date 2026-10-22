/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace (toDualMap)
open scoped Gradient

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (f : E → EReal) (μ : PosReal)

recall effective_domain
recall is_convex_function
recall subdifferential
recall strongDualSubdifferential
recall prox_singleton_implies_effective_domain_and_inner_support
recall prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
recall toDualMap_sub_mem_strongDualSubdifferential_iff_forall_inner_le

/- Definition 6.10 is `bridge/view`.

Domain sampling in the local Moreau-envelope calculus identifies the owner abstraction already
upstream:

- `M[μ, f]` from Definition 6.7 is the source-facing Moreau-envelope owner;
- `moreau_envelope_eq_of_scaled_prox_eq_singleton` from Definition 6.7 is the canonical bridge
  from the set-valued proximal owner to the minimizing Moreau-envelope point;
- `moreau_envelope_eq_real_of_proper_convex` from Theorem 6.55 supplies the everywhere-finite
  real-valued view of that owner;
- `HasGradientAt` and `∇` are the canonical differential owners for the source-facing gradient
  formula.

The primitive data here are therefore only `f`, `μ`, `x`, and the singleton proximal point `u`.
The gradient formula is derived through the chapter's existing set-valued proximal API, not by
introducing a parallel single-valued proximal operator. -/

/-- Helper for Definition 6.10: positive scaling preserves properness of an extended-real-valued
function. -/
lemma scaled_function_proper_of_pos
    (hf_proper : IsProperExtendedRealFunction f) :
    IsProperExtendedRealFunction (((μ : EReal) • f)) := by
  have hμ_nonneg : (0 : EReal) ≤ (μ : ℝ) := by
    exact_mod_cast μ.2.le
  refine ⟨?_, ?_⟩
  · intro x
    -- A positive finite scalar cannot create the value `⊥`.
    rw [Pi.smul_apply, smul_eq_mul]
    exact
      (EReal.mul_ne_bot _ _).2
        ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (hf_proper.ne_bot x),
          Or.inl (EReal.coe_ne_top _), Or.inl hμ_nonneg⟩
  · rcases hf_proper.effective_domain_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    -- A finite point of `f` stays finite after multiplication by `μ > 0`.
    rw [mem_effective_domain, Pi.smul_apply, smul_eq_mul]
    exact
      lt_top_iff_ne_top.mpr <|
        (EReal.mul_ne_top _ _).2
          ⟨Or.inl (EReal.coe_ne_bot _), Or.inl hμ_nonneg,
            Or.inl (EReal.coe_ne_top _), Or.inr (mem_effective_domain.mp hx).ne⟩

/-- Helper for Definition 6.10: finiteness for the positively scaled function is equivalent to
finiteness for the original function. -/
lemma mem_effective_domain_scaled_function_iff
    (hf_proper : IsProperExtendedRealFunction f) (x : E) :
    x ∈ effective_domain (((μ : EReal) • f)) ↔ x ∈ effective_domain f := by
  constructor
  · intro hx
    rw [mem_effective_domain] at hx ⊢
    refine lt_top_iff_ne_top.mpr ?_
    intro hfx_top
    have hx_top : (((μ : EReal) • f) x) = ⊤ := by
      rw [Pi.smul_apply, smul_eq_mul, hfx_top]
      exact EReal.coe_mul_top_of_pos μ.2
    exact (lt_irrefl (⊤ : EReal)) (hx_top ▸ hx)
  · intro hx
    rw [mem_effective_domain] at hx ⊢
    rw [Pi.smul_apply, smul_eq_mul]
    exact
      lt_top_iff_ne_top.mpr <|
        (EReal.mul_ne_top _ _).2
          ⟨Or.inl (EReal.coe_ne_bot _),
            Or.inl (by exact_mod_cast μ.2.le : (0 : EReal) ≤ (μ : ℝ)),
            Or.inl (EReal.coe_ne_top _), Or.inr hx.ne⟩

/-- Helper for Definition 6.10: at every finite point of `f`, applying `toReal` to the positively
scaled function simply multiplies the finite real value by `μ`. -/
lemma scaled_function_value_toReal_eq_mul
    (y : E) (hy : y ∈ effective_domain f) :
    ((((μ : EReal) • f) y).toReal) = (μ : ℝ) * (f y).toReal := by
  -- Rewrite the scaled value pointwise and use the multiplicative `toReal` identity.
  rw [Pi.smul_apply, smul_eq_mul, EReal.toReal_mul, EReal.toReal_coe]

/-- Helper for Definition 6.10: positive scaling preserves convexity. -/
lemma scaled_function_convex_of_pos
    (hf_proper : IsProperExtendedRealFunction f) (hf_convex : is_convex_function f) :
    is_convex_function (((μ : EReal) • f)) := by
  -- Use the epigraph definition, then rescale the second coordinate by `μ`.
  rw [is_convex_function]
  intro p hp q hq a b ha hb hab
  have hp0 : ((μ : EReal) • f) p.1 ≤ (p.2 : EReal) := by
    simpa [Set.mem_setOf_eq] using hp
  have hq0 : ((μ : EReal) • f) q.1 ≤ (q.2 : EReal) := by
    simpa [Set.mem_setOf_eq] using hq
  have hμ_pos : (0 : EReal) < (μ : ℝ) := by
    exact_mod_cast (show 0 < (μ : ℝ) from μ.2)
  have hμ_top : ((μ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hp' : (p.1, p.2 / (μ : ℝ)) ∈ {r : E × ℝ | f r.1 ≤ (r.2 : EReal)} := by
    -- Endpoint membership for the scaled epigraph is equivalent to membership in the original one.
    rw [Set.mem_setOf_eq, EReal.coe_div]
    rw [Pi.smul_apply, smul_eq_mul] at hp0
    exact (EReal.le_div_iff_mul_le hμ_pos hμ_top).2 (by simpa [mul_comm] using hp0)
  have hq' : (q.1, q.2 / (μ : ℝ)) ∈ {r : E × ℝ | f r.1 ≤ (r.2 : EReal)} := by
    rw [Set.mem_setOf_eq, EReal.coe_div]
    rw [Pi.smul_apply, smul_eq_mul] at hq0
    exact (EReal.le_div_iff_mul_le hμ_pos hμ_top).2 (by simpa [mul_comm] using hq0)
  have hcombo := hf_convex hp' hq' ha hb hab
  have hdivr :
      a * (p.2 / (μ : ℝ)) + b * (q.2 / (μ : ℝ)) =
        (a * p.2 + b * q.2) / (μ : ℝ) := by
    field_simp [(show 0 < (μ : ℝ) from μ.2).ne']
  have hcombo' :
      f (a • p.1 + b • q.1) ≤ ((((a * p.2 + b * q.2) / (μ : ℝ) : ℝ)) : EReal) := by
    simpa [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hdivr] using hcombo
  rw [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
  rw [EReal.coe_div] at hcombo'
  have hscaled := (EReal.le_div_iff_mul_le hμ_pos hμ_top).1 hcombo'
  simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    hscaled

/-- Helper for Definition 6.10: the singleton proximal point of the scaled function induces the
affine lower-support inequality for `f` with slope `(1 / μ) • (x - u)`. -/
lemma scaled_prox_singleton_support_of_proper_convex
    (hf_proper : IsProperExtendedRealFunction f) (hf_convex : is_convex_function f) (x u : E)
    (hprox : prox[((μ : EReal) • f)] x = {u}) :
    u ∈ effective_domain f ∧
      ∀ y ∈ effective_domain f,
        ((inner ℝ ((1 / μ : ℝ) • (x - u)) (y - u) : ℝ) : EReal) ≤ f y - f u := by
  let g : E → EReal := ((μ : EReal) • f)
  have hg_proper : IsProperExtendedRealFunction g :=
    scaled_function_proper_of_pos f μ hf_proper
  have hg_convex : is_convex_function g :=
    scaled_function_convex_of_pos f μ hf_proper hf_convex
  rcases prox_singleton_implies_effective_domain_and_inner_support
      g hg_proper hg_convex x u hprox with
    ⟨hu_eff_g, hsupport_g⟩
  have hu_eff : u ∈ effective_domain f :=
    (mem_effective_domain_scaled_function_iff f μ hf_proper u).mp hu_eff_g
  refine ⟨hu_eff, ?_⟩
  intro y hy_eff
  have hy_eff_g : y ∈ effective_domain g :=
    (mem_effective_domain_scaled_function_iff f μ hf_proper y).mpr hy_eff
  have hu_val :
      f u = (((f u).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u)).symm
  have hy_val :
      f y = (((f y).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hy_eff).ne (hf_proper.ne_bot y)).symm
  have hu_scaled_val :
      g u = ((((μ : ℝ) * (f u).toReal : ℝ)) : EReal) := by
    have htoReal : (g u).toReal = (μ : ℝ) * (f u).toReal := by
      simpa [g] using scaled_function_value_toReal_eq_mul (f := f) (μ := μ) u hu_eff
    calc
      g u = (((g u).toReal : ℝ) : EReal) := by
        rw [EReal.coe_toReal (mem_effective_domain.mp hu_eff_g).ne (hg_proper.ne_bot u)]
      _ = ((((μ : ℝ) * (f u).toReal : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) htoReal
  have hy_scaled_val :
      g y = ((((μ : ℝ) * (f y).toReal : ℝ)) : EReal) := by
    have htoReal : (g y).toReal = (μ : ℝ) * (f y).toReal := by
      simpa [g] using scaled_function_value_toReal_eq_mul (f := f) (μ := μ) y hy_eff
    calc
      g y = (((g y).toReal : ℝ) : EReal) := by
        rw [EReal.coe_toReal (mem_effective_domain.mp hy_eff_g).ne (hg_proper.ne_bot y)]
      _ = ((((μ : ℝ) * (f y).toReal : ℝ)) : EReal) := by
        exact congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) htoReal
  have hsupport_real :
      inner ℝ (x - u) (y - u) ≤ (μ : ℝ) * ((f y).toReal - (f u).toReal) := by
    have hsupportE := hsupport_g y hy_eff_g
    rw [hu_scaled_val, hy_scaled_val] at hsupportE
    have hsupportE' :
        (((inner ℝ (x - u) (y - u) : ℝ)) : EReal) ≤
          ((((μ : ℝ) * ((f y).toReal - (f u).toReal) : ℝ)) : EReal) := by
      simpa [EReal.coe_sub, mul_sub_left_distrib] using hsupportE
    exact EReal.coe_le_coe_iff.mp hsupportE'
  have hsupport_div :
      inner ℝ ((1 / μ : ℝ) • (x - u)) (y - u) ≤ (f y).toReal - (f u).toReal := by
    have hscaled :
        (1 / μ : ℝ) * inner ℝ (x - u) (y - u) ≤
          (1 / μ : ℝ) * ((μ : ℝ) * ((f y).toReal - (f u).toReal)) := by
      exact
        mul_le_mul_of_nonneg_left hsupport_real
          (by
            simpa [one_div] using
              inv_nonneg.mpr (show 0 ≤ (μ : ℝ) by exact le_of_lt μ.2))
    have hcancel :
        (1 / μ : ℝ) * ((μ : ℝ) * ((f y).toReal - (f u).toReal)) =
          (f y).toReal - (f u).toReal := by
      field_simp [show (μ : ℝ) ≠ 0 by exact_mod_cast μ.2.ne']
    rw [show inner ℝ ((1 / μ : ℝ) • (x - u)) (y - u) =
        (1 / μ : ℝ) * inner ℝ (x - u) (y - u) by
        simpa using inner_smul_left (x - u) (y - u) (1 / μ : ℝ)]
    rw [hcancel] at hscaled
    exact hscaled
  have hsupport_realE :
      (((inner ℝ ((1 / μ : ℝ) • (x - u)) (y - u) : ℝ)) : EReal) ≤
        (((((f y).toReal - (f u).toReal : ℝ)) : EReal)) :=
    EReal.coe_le_coe hsupport_div
  rw [hy_val, hu_val]
  simpa [EReal.coe_sub] using hsupport_realE

/-- Helper for Definition 6.10: rewriting the Moreau quadratic penalty at a fixed proximal point
produces the affine tangent term plus a quadratic remainder in `y - x`. -/
lemma quadratic_penalty_expand_at_fixed_point (x y u : E) :
    (1 / (2 * μ : ℝ)) * ‖y - u‖ ^ (2 : ℕ) =
      (1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) +
        inner ℝ ((1 / μ : ℝ) • (x - u)) (y - x) +
        (1 / (2 * μ : ℝ)) * ‖y - x‖ ^ (2 : ℕ) := by
  -- Rescale the Chapter 6 quadratic translation identity by the positive parameter `μ`.
  have hbase :
      (1 / (2 : ℝ)) * ‖y - u‖ ^ (2 : ℕ) =
        (1 / (2 : ℝ)) * ‖x - u‖ ^ (2 : ℕ) + inner ℝ (x - u) (y - x) +
          (1 / (2 : ℝ)) * ‖y - x‖ ^ (2 : ℕ) :=
    quadratic_translate_identity u x y
  have hscaled := congrArg (fun t : ℝ => (1 / μ : ℝ) * t) hbase
  simpa [inner_smul_left, mul_add, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
    hscaled

/-- Helper for Definition 6.10: after inserting the affine lower support for `f`, the remaining
quadratic term is a completed square and is therefore nonnegative. -/
lemma quadratic_completion_lower_bound (x y u v : E) :
    inner ℝ ((1 / μ : ℝ) • (x - u)) (v - u) +
        (1 / (2 * μ : ℝ)) * ‖y - v‖ ^ (2 : ℕ) =
      (1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) +
        inner ℝ ((1 / μ : ℝ) • (x - u)) (y - x) +
        (1 / (2 * μ : ℝ)) * ‖v - (u + (y - x))‖ ^ (2 : ℕ) := by
  -- Translate the residual by `w := v - (u + (y - x))` and expand the square.
  have hvu : v - u = (y - x) + (v - (u + (y - x))) := by
    abel
  have hyv : y - v = (x - u) - (v - (u + (y - x))) := by
    abel
  have hsq :
      ‖y - v‖ ^ (2 : ℕ) =
        ‖x - u‖ ^ (2 : ℕ) - 2 * inner ℝ (x - u) (v - (u + (y - x))) +
          ‖v - (u + (y - x))‖ ^ (2 : ℕ) := by
    rw [hyv, norm_sub_sq_real]
  have hsq_scaled := congrArg (fun t : ℝ => (1 / (2 * μ : ℝ)) * t) hsq
  have hinner :
      inner ℝ ((1 / μ : ℝ) • (x - u)) (v - u) =
        inner ℝ ((1 / μ : ℝ) • (x - u)) (y - x) +
          inner ℝ ((1 / μ : ℝ) • (x - u)) (v - (u + (y - x))) := by
    rw [hvu, inner_add_right]
  have hsmul :
      inner ℝ ((1 / μ : ℝ) • (x - u)) (v - (u + (y - x))) =
        (1 / μ : ℝ) * inner ℝ (x - u) (v - (u + (y - x))) := by
    simpa using inner_smul_left (x - u) (v - (u + (y - x))) (1 / μ : ℝ)
  rw [hinner, hsmul]
  have hcancel :
      (1 / (2 * μ : ℝ)) * (2 * inner ℝ (x - u) (v - (u + (y - x)))) =
        (1 / μ : ℝ) * inner ℝ (x - u) (v - (u + (y - x))) := by
    field_simp [show (μ : ℝ) ≠ 0 by exact_mod_cast μ.2.ne']
  nlinarith [hsq_scaled, hcancel]

/-- Helper for Definition 6.10: an `EReal` value trapped between two finite real bounds is finite,
and its `toReal` lies between those bounds. -/
lemma finite_ereal_sandwich_toReal_bounds {z : EReal} {a b : ℝ}
    (ha : ((a : ℝ) : EReal) ≤ z) (hb : z ≤ ((b : ℝ) : EReal)) :
    z ≠ ⊥ ∧ z ≠ ⊤ ∧ a ≤ z.toReal ∧ z.toReal ≤ b := by
  -- The finite lower and upper bounds exclude `⊥` and `⊤`, so `toReal` is order-compatible.
  have hz_bot : z ≠ ⊥ := by
    intro hz_bot
    rw [hz_bot] at ha
    exact (not_le_of_gt (EReal.bot_lt_coe a)) ha
  have hz_top : z ≠ ⊤ := by
    intro hz_top
    rw [hz_top] at hb
    exact (not_le_of_gt (EReal.coe_lt_top b)) hb
  have hleft : a ≤ z.toReal := by
    simpa using EReal.toReal_le_toReal ha (EReal.coe_ne_bot a) hz_top
  have hright : z.toReal ≤ b := by
    simpa using EReal.toReal_le_toReal hb hz_bot (EReal.coe_ne_top b)
  exact ⟨hz_bot, hz_top, hleft, hright⟩

/-- Helper for Definition 6.10: the singleton proximal point yields a two-sided quadratic bound
for the real-valued Moreau-envelope remainder at `x`. -/
lemma moreau_envelope_toReal_remainder_bounds_of_scaled_prox_eq_singleton
    (hf_proper : IsProperExtendedRealFunction f) (hf_convex : is_convex_function f) (x u : E)
    (hprox : prox[((μ : EReal) • f)] x = {u}) :
    let F : E → ℝ := fun y ↦ (M[μ, f] y).toReal
    let g : E := (1 / μ : ℝ) • (x - u)
    ∀ h : E,
      0 ≤ F (x + h) - F x - inner ℝ g h ∧
        F (x + h) - F x - inner ℝ g h ≤ (1 / (2 * μ : ℝ)) * ‖h‖ ^ (2 : ℕ) := by
  -- Build the real remainder bound from the fixed-point `EReal` sandwich around `u`.
  dsimp
  rcases scaled_prox_singleton_support_of_proper_convex
      (f := f) (μ := μ) hf_proper hf_convex x u hprox with
    ⟨hu_eff, hsupport⟩
  have hu_val :
      f u = (((f u).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u)).symm
  have hbase_toReal :
      (M[μ, f] x).toReal =
        (f u).toReal + (1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) := by
    -- At the base point, the singleton proximal formula identifies the Moreau value with a
    -- finite affine-quadratic expression.
    have hu_top : f u ≠ ⊤ := (mem_effective_domain.mp hu_eff).ne
    have hu_bot : f u ≠ ⊥ := hf_proper.ne_bot u
    calc
      (M[μ, f] x).toReal =
          (f u + ((((1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) : ℝ)) : EReal)).toReal := by
        rw [moreau_envelope_eq_of_scaled_prox_eq_singleton hprox]
      _ = (f u).toReal +
            ((((1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) : ℝ) : EReal)).toReal := by
        rw [EReal.toReal_add hu_top hu_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)]
      _ = (f u).toReal + (1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) := by
        rw [EReal.toReal_coe]
  intro h
  have hlowerE :
      ((((f u).toReal + (1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) +
          inner ℝ ((1 / μ : ℝ) • (x - u)) h : ℝ)) : EReal) ≤
        M[μ, f] (x + h) := by
    -- The lower bound comes from the affine support inequality plus nonnegativity of the
    -- completed square in the penalized objective.
    rw [moreau_envelope_apply]
    refine le_iInf ?_
    intro v
    by_cases hv_eff : v ∈ effective_domain f
    · have hv_val :
          f v = (((f v).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (mem_effective_domain.mp hv_eff).ne (hf_proper.ne_bot v)).symm
      have hsupport_add :
          (((inner ℝ ((1 / μ : ℝ) • (x - u)) (v - u) : ℝ)) : EReal) + f u ≤ f v := by
        exact
          (EReal.le_sub_iff_add_le (.inl (hf_proper.ne_bot u))
            (.inl (mem_effective_domain.mp hu_eff).ne)).1 (hsupport v hv_eff)
      have hquadE :
          ((((inner ℝ ((1 / μ : ℝ) • (x - u)) (v - u) +
              (1 / (2 * μ : ℝ)) * ‖(x + h) - v‖ ^ (2 : ℕ) : ℝ)) : EReal)) =
            ((((1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) +
                inner ℝ ((1 / μ : ℝ) • (x - u)) h +
                (1 / (2 * μ : ℝ)) * ‖v - (u + h)‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
        exact
          congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) <|
            by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (quadratic_completion_lower_bound
                  (μ := μ) x (x + h) u v)
      have hquad_le :
          ((((1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) +
              inner ℝ ((1 / μ : ℝ) • (x - u)) h : ℝ)) : EReal) ≤
            ((((inner ℝ ((1 / μ : ℝ) • (x - u)) (v - u) +
                (1 / (2 * μ : ℝ)) * ‖(x + h) - v‖ ^ (2 : ℕ) : ℝ)) : EReal)) := by
        rw [hquadE]
        exact EReal.coe_le_coe <| by
          have hμ_pos : (0 : ℝ) < (μ : ℝ) := μ.2
          have htwoμ_pos : 0 < (2 * μ : ℝ) := by
            nlinarith
          have hcoeff_nonneg : 0 ≤ (1 / (2 * μ : ℝ)) := by
            exact le_of_lt (one_div_pos.mpr htwoμ_pos)
          have hres_nonneg :
              0 ≤ (1 / (2 * μ : ℝ)) * ‖v - (u + h)‖ ^ (2 : ℕ) := by
            exact mul_nonneg hcoeff_nonneg (pow_nonneg (norm_nonneg _) _)
          linarith
      have hstep₁ :
          ((((f u).toReal + (1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) +
              inner ℝ ((1 / μ : ℝ) • (x - u)) h : ℝ)) : EReal) ≤
            f u +
              ((((inner ℝ ((1 / μ : ℝ) • (x - u)) (v - u) +
                  (1 / (2 * μ : ℝ)) * ‖(x + h) - v‖ ^ (2 : ℕ) : ℝ)) : EReal)) := by
        rw [hu_val]
        simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using
          add_le_add_left hquad_le ((((f u).toReal : ℝ) : EReal))
      have hstep₂ :
          f u +
              ((((inner ℝ ((1 / μ : ℝ) • (x - u)) (v - u) +
                  (1 / (2 * μ : ℝ)) * ‖(x + h) - v‖ ^ (2 : ℕ) : ℝ)) : EReal)) ≤
            f v + ((((1 / (2 * μ : ℝ)) * ‖(x + h) - v‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
        have hsupport_q :=
          add_le_add_right hsupport_add
            ((((1 / (2 * μ : ℝ)) * ‖(x + h) - v‖ ^ (2 : ℕ) : ℝ)) : EReal)
        simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hsupport_q
      exact le_trans hstep₁ hstep₂
    · have hv_top : f v = ⊤ := by
        by_contra hfv_top
        exact hv_eff (mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hfv_top))
      rw [hv_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
      exact le_top
  have hupperE :
      M[μ, f] (x + h) ≤
        ((((f u).toReal + (1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) +
            inner ℝ ((1 / μ : ℝ) • (x - u)) h +
            (1 / (2 * μ : ℝ)) * ‖h‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
    -- The upper bound comes from evaluating the Moreau infimum at the frozen proximal point `u`.
    calc
      M[μ, f] (x + h) ≤
          f u + ((((1 / (2 * μ : ℝ)) * ‖(x + h) - u‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
        rw [moreau_envelope_apply]
        exact iInf_le _ u
      _ = ((((f u).toReal + (1 / (2 * μ : ℝ)) * ‖x - u‖ ^ (2 : ℕ) +
            inner ℝ ((1 / μ : ℝ) • (x - u)) h +
            (1 / (2 * μ : ℝ)) * ‖h‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
        rw [hu_val]
        exact
          congrArg (fun r : ℝ ↦ ((r : ℝ) : EReal)) <|
            by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
                (quadratic_penalty_expand_at_fixed_point
                  (μ := μ) x (x + h) u)
  rcases finite_ereal_sandwich_toReal_bounds hlowerE hupperE with
    ⟨_, _, hlower, hupper⟩
  have hlower' :
      (M[μ, f] x).toReal + inner ℝ ((1 / μ : ℝ) • (x - u)) h ≤
        (M[μ, f] (x + h)).toReal := by
    rw [hbase_toReal]
    simpa [add_assoc, add_left_comm, add_comm] using hlower
  have hupper' :
      (M[μ, f] (x + h)).toReal ≤
        (M[μ, f] x).toReal + inner ℝ ((1 / μ : ℝ) • (x - u)) h +
          (1 / (2 * μ : ℝ)) * ‖h‖ ^ (2 : ℕ) := by
    rw [hbase_toReal]
    simpa [add_assoc, add_left_comm, add_comm] using hupper
  constructor
  · -- Rearranging the lower affine bound gives nonnegativity of the remainder.
    linarith
  · -- Rearranging the upper affine bound controls the remainder by the quadratic term.
    linarith

/-- Helper for Definition 6.10: an `ℝ`-valued remainder bounded by a quadratic term is little-o of
the identity near the origin. -/
lemma quad_remainder_isLittleO_of_two_sided_bound {R : E → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hR : ∀ h, 0 ≤ R h ∧ R h ≤ c * ‖h‖ ^ (2 : ℕ)) :
    R =o[nhds 0] fun h : E => h := by
  -- First record the quadratic bound as a global `O(‖h‖²)` estimate, then compose with the
  -- standard `‖h‖² = o(h)` asymptotic.
  have hBigO : R =O[nhds 0] fun h : E ↦ ‖h‖ ^ (2 : ℕ) := by
    refine Asymptotics.IsBigO.of_bound c (Filter.Eventually.of_forall ?_)
    intro h
    rcases hR h with ⟨hR_nonneg, hR_le⟩
    simpa [Real.norm_eq_abs, abs_of_nonneg hR_nonneg] using hR_le
  exact hBigO.trans_isLittleO
    (Asymptotics.isLittleO_norm_pow_id (E' := E) (n := 2) (by norm_num))

-- Proof sketch: use the singleton proximal hypothesis to identify `u` as the minimizing point in
-- the Moreau-envelope formula, use `moreau_envelope_eq_real_of_proper_convex` to pass to the
-- real-valued owner `y ↦ (M[μ, f] y).toReal`, and differentiate the quadratic penalty to obtain
-- `(1 / μ) • (x - u)`.
/-- The real-valued Moreau envelope has gradient `(1 / μ) • (x - u)` at `x` whenever `u` is the
unique proximal point of the scaled function `μ f` at `x`. -/
theorem hasGradientAt_moreau_envelope_toReal_of_scaled_prox_eq_singleton
    (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f) (x u : E)
    (hprox : prox[((μ : EReal) • f)] x = {u}) :
    HasGradientAt (fun y ↦ (M[μ, f] y).toReal) ((1 / μ : ℝ) • (x - u)) x := by
  -- Route correction: the intended proof no longer uses proximal points near `x`.
  -- It should combine:
  -- 1. `scaled_prox_singleton_support_of_proper_convex` for the affine lower support;
  -- 2. `quadratic_penalty_expand_at_fixed_point` for the frozen-point upper model;
  -- 3. `quadratic_completion_lower_bound` to show the remainder is nonnegative; and
  -- 4. `hasGradientAt_iff_isLittleO_nhds_zero` after bounding the remainder by `O(‖h‖²)`.
  -- The new route packages the coercion work into a quadratic remainder lemma before invoking the
  -- standard gradient/little-o characterization.
  rw [hasGradientAt_iff_isLittleO_nhds_zero]
  have hR :
      ∀ h : E,
        0 ≤
            (M[μ, f] (x + h)).toReal - (M[μ, f] x).toReal -
              inner ℝ ((1 / μ : ℝ) • (x - u)) h ∧
          (M[μ, f] (x + h)).toReal - (M[μ, f] x).toReal -
              inner ℝ ((1 / μ : ℝ) • (x - u)) h ≤
            (1 / (2 * μ : ℝ)) * ‖h‖ ^ (2 : ℕ) :=
    moreau_envelope_toReal_remainder_bounds_of_scaled_prox_eq_singleton
      (f := f) (μ := μ) hf_proper hf_convex x u hprox
  exact
    quad_remainder_isLittleO_of_two_sided_bound
      (E := E) (c := (1 / (2 * μ : ℝ)))
      (by
        have hμ_pos : (0 : ℝ) < μ := μ.2
        positivity) hR

-- Proof sketch: apply `HasGradientAt.gradient` to
-- `hasGradientAt_moreau_envelope_toReal_of_scaled_prox_eq_singleton`.
/-- Definition 6.10: if `u` is the unique proximal point of the scaled function `μ f` at `x`,
then the gradient of the real-valued Moreau envelope at `x` is `(1 / μ) • (x - u)`. This is the
chapter's singleton-valued rendering of the textbook formula
`∇ M_f^μ(x) = (1 / μ) (x - prox_{μ f}(x))`. -/
theorem moreau_envelope_gradient_formula_of_scaled_prox_eq_singleton
    (hf_proper : IsProperExtendedRealFunction f) (hf_closed : LowerSemicontinuous f)
    (hf_convex : is_convex_function f) (x u : E)
    (hprox : prox[((μ : EReal) • f)] x = {u}) :
    ∇ (fun y ↦ (M[μ, f] y).toReal) x = (1 / μ : ℝ) • (x - u) :=
  (hasGradientAt_moreau_envelope_toReal_of_scaled_prox_eq_singleton
    f μ hf_proper hf_closed hf_convex x u hprox).gradient

end
