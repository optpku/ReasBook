/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_6
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_10
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Theorem_9_12.Objective

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Algorithm 10.67 has two local layers.

- `source-facing`: the one-step update predicate from the chapter text;
- `core/canonical`: Chapter 9's `mirror_c_update_objective`;
- `bridge/view`: the later Hilbert-space Bregman rewrite of that objective.

Domain sampling in the surrounding project points to:
- `mirror_c_update_objective` from Definition 9.6 as the owner of the specialized one-step
  Mirror-C minimization problem;
- `IsMinOn` for the argmin clause;
- `PosReal` for the positive curvature parameter `L_k`.

The source-facing owner here specializes the Chapter 9 Mirror-C objective to the functional
`fderiv ℝ (fun y ↦ (f y).toReal) xk` and reciprocal curvature `(Lk : ℝ)⁻¹`, but unlike the earlier
totalized set-valued draft it keeps the Chapter 3 regularity clause
`is_differentiable_at f xk` explicit in the owner itself. This is the primitive data needed for
the displayed derivative to have its genuine textbook meaning. The Bregman rewrite is derived API
and is kept separate in the stronger inner-product section below.

Semantic search note: `lean_leansearch` only surfaced the generic `IsMinOn` API here, so the
owner/API repair below follows the existing Chapter 3 and Chapter 9 declarations imported in this
file. -/

/-- Algorithm 10.67: a point `x⁺` is an admissible next iterate of the non-Euclidean
proximal-gradient method from `x^k` with curvature parameter `L_k` when `f` is differentiable at
`x^k` in the Chapter 3 sense, `x⁺` lies in the finite-valued domain of `ω`, and `x⁺` minimizes
the Chapter 9 Mirror-C update objective specialized to the functional `f'(x^k)` and reciprocal
curvature `(Lk : ℝ)⁻¹` over that finite-valued domain. -/
class non_euclidean_proximal_gradient_step
    (f g ω : E → EReal) (xk : E) (Lk : PosReal) (xNext : E) : Prop where
  differentiable : is_differentiable_at f xk
  mem_finite_domain : xNext ∈ finite_domain ω
  minimizer :
    IsMinOn
      (mirror_c_update_objective g ω xk
        (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
      (finite_domain ω) xNext

/-- The Algorithm 10.67 step predicate is proof-irrelevant in the current context. -/
instance non_euclidean_proximal_gradient_step.instSubsingleton
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    : Subsingleton (non_euclidean_proximal_gradient_step f g ω xk Lk xNext) :=
  inferInstance

/-- The non-Euclidean proximal-gradient step predicate is exactly the conjunction of the
Chapter 3 differentiability condition at `x^k`, the finite-domain guard on `x⁺`, and the
canonical Mirror-C minimizer condition for `x⁺` on `finite_domain ω`. -/
@[simp] theorem non_euclidean_proximal_gradient_step_iff
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal} :
    non_euclidean_proximal_gradient_step f g ω xk Lk xNext ↔
      is_differentiable_at f xk ∧
      xNext ∈ finite_domain ω ∧
      IsMinOn
        (mirror_c_update_objective g ω xk
          (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
        (finite_domain ω) xNext :=
  by
    constructor
    · intro hstep
      -- Unpack the source-facing owner into its three stored fields.
      exact ⟨hstep.differentiable, hstep.mem_finite_domain, hstep.minimizer⟩
    · rintro ⟨hdiff, hxNext, hmin⟩
      -- Repackage the same data into the owner predicate.
      exact ⟨hdiff, hxNext, hmin⟩

/-- A non-Euclidean proximal-gradient step starts at a differentiability point of `f`. -/
theorem non_euclidean_proximal_gradient_step.differentiable_at
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hstep : non_euclidean_proximal_gradient_step f g ω xk Lk xNext) :
    is_differentiable_at f xk :=
  by
    -- Read the differentiability clause directly from the owner fields.
    exact hstep.differentiable

/-- A non-Euclidean proximal-gradient step is a global minimizer of the specialized Mirror-C
objective on `finite_domain ω`. -/
theorem non_euclidean_proximal_gradient_step.isMinOn
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hstep : non_euclidean_proximal_gradient_step f g ω xk Lk xNext) :
    IsMinOn
      (mirror_c_update_objective g ω xk
        (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
      (finite_domain ω) xNext :=
  by
    -- Read the minimizer clause directly from the owner fields.
    exact hstep.minimizer

end

section

open scoped Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The remainder of the file is a `bridge/view` layer.

The owner abstraction is still `mirror_c_update_objective`, but rewriting it into the textbook
Bregman model is already controlled upstream by Text 9.10. The source-facing textbook reading now
needs the explicit differentiability hypothesis
`hfxk : is_differentiable_at f xk`, so the displayed first-order term uses the genuine textbook
derivative of `f` at `x^k` and the added constant `f xk` is finite.

The Bregman model is therefore derived API for the same owner rather than a second root
definition. The Bregman-distance term itself is reused through Chapter 9's totalized owner `B[ω]`;
Text 9.10 compares the resulting minimizers only on `finite_domain ω`, so the candidate point
must carry that guard explicitly in the bridge API below. -/

-- Proof sketch: first apply the owner-level Chapter 9 bridge
-- `isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_form` with
-- `s = fderiv ℝ (fun y ↦ (f y).toReal) xk` and `t = (Lk : ℝ)⁻¹`. Then use `hfxk` to rewrite the
-- linear term through the genuine gradient `∇ (fun y ↦ (f y).toReal) xk`, multiply the objective
-- by the positive constant `Lk`, and add the `x`-independent finite constant `f xk`.

omit [CompleteSpace E] in
/-- Helper for Algorithm 10.67: differentiability at `x^k` forces `f xk` to be a finite
extended-real value, so it can be rewritten through `toReal`. -/
lemma differentiable_at_value_eq_coe_toReal
    {f : E → EReal} {xk : E} (hfxk : is_differentiable_at f xk) :
    f xk = (((f xk).toReal : ℝ) : EReal) := by
  -- Differentiability places `xk` in the interior of `finite_domain f`, hence at a finite value.
  have hxk_mem : xk ∈ finite_domain f := interior_subset hfxk.1
  exact (EReal.coe_toReal (mem_effective_domain.mp hxk_mem.1).ne hxk_mem.2).symm

/-- Helper for Algorithm 10.67: in the Hilbert-space setting, the displayed derivative acts by
the gradient pairing. -/
lemma fderiv_toReal_apply_eq_inner_gradient
    {f : E → EReal} {xk x : E} (hfxk : is_differentiable_at f xk) :
    fderiv ℝ (fun y ↦ (f y).toReal) xk x =
      inner ℝ (∇ (fun y ↦ (f y).toReal) xk) x := by
  -- In a Hilbert space the Fréchet derivative acts by pairing with the gradient.
  simpa using (HasGradientAt.fderiv_apply hfxk.2.hasGradientAt : _)

/-- Helper for Algorithm 10.67: the Chapter 9 Bregman-form objective specialized to the derivative
of `f` at `x^k` and reciprocal curvature `(L_k)⁻¹`. -/
def scaled_bregman_objective
    (f g ω : E → EReal) (xk : E) (Lk : PosReal) : E → EReal :=
  secondProxObjective
    (fun x ↦
      ((((Lk : ℝ)⁻¹ * fderiv ℝ (fun y ↦ (f y).toReal) xk x : ℝ) : EReal) +
        (((Lk : ℝ)⁻¹ : EReal) * g x)))
    ω xk

/-- Evaluating `scaled_bregman_objective` at `x` gives the specialized Chapter 9 Bregman-form
integrand. -/
@[simp] theorem scaled_bregman_objective_apply
    (f g ω : E → EReal) (xk x : E) (Lk : PosReal) :
    scaled_bregman_objective f g ω xk Lk x =
      ((((Lk : ℝ)⁻¹ * fderiv ℝ (fun y ↦ (f y).toReal) xk x : ℝ) : EReal) +
        (((Lk : ℝ)⁻¹ : EReal) * g x) +
        ((B[ω] x xk : ℝ) : EReal)) :=
  rfl

/-- Helper for Algorithm 10.67: the textbook non-Euclidean proximal-gradient local model. -/
def non_euclidean_textbook_model
    (f g ω : E → EReal) (xk : E) (Lk : PosReal) : E → EReal :=
  fun x ↦
    ((f xk +
        ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x - xk) : ℝ) : EReal)) +
      g x) +
      (((Lk : ℝ) * B[ω] x xk : ℝ) : EReal)

/-- Evaluating `non_euclidean_textbook_model` at `x` gives the displayed Bregman-regularized
first-order model from Algorithm 10.67. -/
@[simp] theorem non_euclidean_textbook_model_apply
    (f g ω : E → EReal) (xk x : E) (Lk : PosReal) :
    non_euclidean_textbook_model f g ω xk Lk x =
      ((f xk +
          ((inner ℝ (∇ (fun y ↦ (f y).toReal) xk) (x - xk) : ℝ) : EReal)) +
        g x) +
        (((Lk : ℝ) * B[ω] x xk : ℝ) : EReal) :=
  rfl

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Helper for Algorithm 10.67: multiplying an objective by a positive real scalar and adding a
finite real constant preserves its minimizers on any fixed set. -/
lemma isMinOn_iff_of_pos_mul_add_constant
    {φ ψ : E → EReal} {s : Set E} {z : E} {a c : ℝ} (ha : 0 < a)
    (hobj : ∀ x, φ x = (((a : ℝ) : EReal) * ψ x) + (c : EReal)) :
    IsMinOn φ s z ↔ IsMinOn ψ s z := by
  have hscale_pos : 0 < ((a : ℝ) : EReal) := by
    exact_mod_cast ha
  have hscale_top : ((a : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hscale_bot : ((a : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hscale_zero : ((a : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast ha.ne'
  rw [isMinOn_iff, isMinOn_iff]
  constructor
  · intro hz y hy
    -- Cancel the common additive constant and divide by the positive scale.
    have hzy := hz y hy
    rw [hobj z, hobj y] at hzy
    have hscaled :
        (((a : ℝ) : EReal) * ψ z) ≤ (((a : ℝ) : EReal) * ψ y) :=
      ((EReal.addLECancellable_coe c).add_le_add_iff_right).mp hzy
    have hdiv :
        ((((a : ℝ) : EReal) * ψ z) / ((a : ℝ) : EReal)) ≤
          ((((a : ℝ) : EReal) * ψ y) / ((a : ℝ) : EReal)) :=
      EReal.monotone_div_right_of_nonneg hscale_pos.le hscaled
    rw [mul_comm (((a : ℝ) : EReal)) (ψ z), mul_comm (((a : ℝ) : EReal)) (ψ y)] at hdiv
    rw [← EReal.mul_div_right, ← EReal.mul_div_right,
      EReal.div_mul_cancel hscale_bot hscale_top hscale_zero,
      EReal.div_mul_cancel hscale_bot hscale_top hscale_zero] at hdiv
    exact hdiv
  · intro hz y hy
    -- Reinsert the positive scale and then add back the constant shift.
    have hscaled :
        (((a : ℝ) : EReal) * ψ z) ≤ (((a : ℝ) : EReal) * ψ y) :=
      mul_le_mul_of_nonneg_left (hz y hy) hscale_pos.le
    have hshifted := ((EReal.addLECancellable_coe c).add_le_add_iff_right).mpr hscaled
    calc
      φ z = (((a : ℝ) : EReal) * ψ z) + (c : EReal) := hobj z
      _ ≤ (((a : ℝ) : EReal) * ψ y) + (c : EReal) := hshifted
      _ = φ y := (hobj y).symm

/-- Helper for Algorithm 10.67: the textbook non-Euclidean proximal-gradient model is an
`x`-independent finite constant plus the positive scalar `L_k` times the Chapter 9 Bregman-form
objective specialized to `f'(x^k)` and `(L_k)⁻¹`. -/
lemma non_euclidean_model_eq_constant_add_scaled_bregman_objective
    (f g ω : E → EReal) (xk x : E) (Lk : PosReal)
    (hfxk : is_differentiable_at f xk) :
    non_euclidean_textbook_model f g ω xk Lk x =
      (((f xk).toReal - inner ℝ (∇ (fun y ↦ (f y).toReal) xk) xk : ℝ) : EReal) +
        (((Lk : ℝ) : EReal) * scaled_bregman_objective f g ω xk Lk x) := by
  let gradk : E := ∇ (fun y ↦ (f y).toReal) xk
  have hL_nonneg : (0 : EReal) ≤ ((Lk : ℝ) : EReal) := by
    exact_mod_cast (PosReal.coe_pos Lk).le
  have hL_ne_top : ((Lk : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hL_ne_zero : (Lk : ℝ) ≠ 0 := (PosReal.coe_pos Lk).ne'
  have hlinear :
      fderiv ℝ (fun y ↦ (f y).toReal) xk x = inner ℝ gradk x := by
    simpa [gradk] using fderiv_toReal_apply_eq_inner_gradient (x := x) hfxk
  have hscaled :
      (((Lk : ℝ) : EReal) * scaled_bregman_objective f g ω xk Lk x) =
        ((inner ℝ gradk x : ℝ) : EReal) + g x + (((Lk : ℝ) * B[ω] x xk : ℝ) : EReal) := by
    let a : EReal := (((Lk : ℝ)⁻¹ : EReal) * ((inner ℝ gradk x : ℝ) : EReal))
    let b : EReal := (((Lk : ℝ)⁻¹ : EReal) * g x)
    let c : EReal := ((B[ω] x xk : ℝ) : EReal)
    have hrecip_cast :
        (((Lk : ℝ) : EReal) * (((Lk : ℝ)⁻¹ : EReal))) = 1 := by
      simpa [EReal.coe_mul] using
        congrArg (fun t : ℝ ↦ (t : EReal)) (mul_inv_cancel₀ hL_ne_zero)
    have hfirst :
        (((Lk : ℝ) : EReal) * a) =
          ((inner ℝ gradk x : ℝ) : EReal) := by
      dsimp [a]
      rw [← mul_assoc, hrecip_cast, one_mul]
    have hsecond :
        (((Lk : ℝ) : EReal) * (((Lk : ℝ)⁻¹ : EReal) * g x)) = g x := by
      calc
        (((Lk : ℝ) : EReal) * (((Lk : ℝ)⁻¹ : EReal) * g x)) =
            ((((Lk : ℝ) : EReal) * (((Lk : ℝ)⁻¹ : EReal))) * g x) := by
              rw [← mul_assoc]
        _ = g x := by
              rw [hrecip_cast, one_mul]
    have hdistrib1 :
        (((Lk : ℝ) : EReal) * (a + b + c)) =
          (((Lk : ℝ) : EReal) * (a + b)) + (((Lk : ℝ) : EReal) * c) := by
      rw [EReal.left_distrib_of_nonneg_of_ne_top hL_nonneg hL_ne_top]
    have hdistrib2 :
        (((Lk : ℝ) : EReal) * (a + b)) =
          (((Lk : ℝ) : EReal) * a) + (((Lk : ℝ) : EReal) * b) := by
      rw [EReal.left_distrib_of_nonneg_of_ne_top hL_nonneg hL_ne_top]
    -- Expand the scaled Chapter 9 objective and cancel the reciprocal curvature.
    calc
      (((Lk : ℝ) : EReal) * scaled_bregman_objective f g ω xk Lk x) =
          (((Lk : ℝ) : EReal) * (a + b + c)) := by
            simp [scaled_bregman_objective_apply, hlinear, a, b, c, EReal.coe_mul, EReal.coe_inv]
      _ =
          ((((Lk : ℝ) : EReal) * a) +
            (((Lk : ℝ) : EReal) * b)) +
              (((Lk : ℝ) : EReal) * c) := by
                rw [hdistrib1, hdistrib2]
      _ = ((inner ℝ gradk x : ℝ) : EReal) + g x + (((Lk : ℝ) * B[ω] x xk : ℝ) : EReal) := by
            dsimp [a, b, c]
            rw [hfirst, hsecond]
  have hsub :
      inner ℝ gradk (x - xk) = inner ℝ gradk x - inner ℝ gradk xk := by
    simpa [sub_eq_add_neg] using inner_sub_right gradk x xk
  -- Normalize the textbook model to the same finite-constant-plus-scaled-objective form.
  symm
  calc
    (((f xk).toReal - inner ℝ (∇ (fun y ↦ (f y).toReal) xk) xk : ℝ) : EReal) +
        (((Lk : ℝ) : EReal) * scaled_bregman_objective f g ω xk Lk x) =
      (((f xk).toReal - inner ℝ gradk xk : ℝ) : EReal) +
        (((inner ℝ gradk x : ℝ) : EReal) + g x + (((Lk : ℝ) * B[ω] x xk : ℝ) : EReal)) := by
          rw [hscaled]
    _ = non_euclidean_textbook_model f g ω xk Lk x := by
          rw [non_euclidean_textbook_model_apply, differentiable_at_value_eq_coe_toReal hfxk, hsub]
          simp [gradk, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Algorithm 10.67: positive affine rescaling transports `IsMinOn` from the Chapter 9
Bregman-form objective to the textbook non-Euclidean proximal-gradient model and back on
`finite_domain ω`. -/
lemma isMinOn_scaled_bregman_objective_iff_isMinOn_non_euclidean_model
    (f g ω : E → EReal) (xk xNext : E) (Lk : PosReal)
    (hfxk : is_differentiable_at f xk) :
    IsMinOn (scaled_bregman_objective f g ω xk Lk) (finite_domain ω) xNext ↔
      IsMinOn (non_euclidean_textbook_model f g ω xk Lk) (finite_domain ω) xNext := by
  -- Positive affine rescaling preserves minimizers on the finite-domain set.
  exact
    (isMinOn_iff_of_pos_mul_add_constant
      (φ := non_euclidean_textbook_model f g ω xk Lk)
      (ψ := scaled_bregman_objective f g ω xk Lk)
      (s := finite_domain ω) (z := xNext)
      (a := (Lk : ℝ))
      (c := (f xk).toReal - inner ℝ (∇ (fun y ↦ (f y).toReal) xk) xk)
      (PosReal.coe_pos Lk)
      (fun x ↦ by
        simpa [add_comm] using
          non_euclidean_model_eq_constant_add_scaled_bregman_objective
            f g ω xk x Lk hfxk)).symm

/-- Helper for Algorithm 10.67: outside `effective_domain g`, the scaled Chapter 9 Bregman-form
objective is forced to `⊤`. -/
lemma scaled_bregman_objective_eq_top_of_not_mem_effective_domain
    (f g ω : E → EReal) (xk y : E) (Lk : PosReal)
    (hy : y ∉ effective_domain g) :
    scaled_bregman_objective f g ω xk Lk y = ⊤ := by
  have hgy_top : g y = ⊤ := by
    exact le_antisymm le_top (not_lt.mp (by simpa using hy))
  have hscaled_top :
      (((Lk : ℝ)⁻¹ : EReal) * (⊤ : EReal)) = ⊤ := by
    simpa using EReal.coe_mul_top_of_pos (inv_pos.mpr (PosReal.coe_pos Lk))
  -- Once the `g` term is `⊤`, the remaining finite casts cannot change that.
  rw [scaled_bregman_objective_apply, hgy_top, hscaled_top]
  rw [EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
  rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]

/-- Helper for Algorithm 10.67: at the current iterate `x^k`, the scaled Bregman objective is
strictly below `⊤` whenever `x^k ∈ effective_domain g`. -/
lemma scaled_bregman_objective_lt_top_at_current_iterate
    (f g ω : E → EReal) (xk : E) (Lk : PosReal)
    (hxk : xk ∈ effective_domain g) :
    scaled_bregman_objective f g ω xk Lk xk < ⊤ := by
  have hscale_nonneg : (0 : EReal) ≤ ((((Lk : ℝ)⁻¹ : ℝ) : EReal)) := by
    exact_mod_cast inv_nonneg.mpr (PosReal.coe_pos Lk).le
  have hscaled_ne_top :
      ((((Lk : ℝ)⁻¹ : EReal) * g xk) ≠ ⊤) := by
    exact
      (EReal.mul_ne_top _ _).2
        ⟨Or.inl (EReal.coe_ne_bot _), Or.inl hscale_nonneg,
          Or.inl (EReal.coe_ne_top _), Or.inr (mem_effective_domain.mp hxk).ne⟩
  -- On the diagonal the Bregman term vanishes, so only one finite cast and the scaled `g` term
  -- remain.
  rw [scaled_bregman_objective_apply, bregmanDistance_self_eq_zero]
  refine EReal.add_lt_top ?_ (EReal.coe_ne_top _)
  exact EReal.add_ne_top (EReal.coe_ne_top _) hscaled_ne_top

omit [CompleteSpace E] in
/-- Helper for Algorithm 10.67: under the Bregman-potential hypotheses, any point in
`effective_domain g` automatically lies in `finite_domain ω`. -/
lemma mem_finite_domain_of_mem_effective_domain
    {g ω : E → EReal} (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    {x : E} (hx : x ∈ effective_domain g) :
    x ∈ finite_domain ω := by
  -- The potential hypothesis supplies both membership in `dom(ω)` and exclusion of `⊥`.
  exact ⟨hω.subset_effective_domain hx, hω.toIsProperExtendedRealFunction.ne_bot x⟩

/-- Helper for Algorithm 10.67: under the Bregman-potential hypotheses, minimizing the scaled
Chapter 9 Bregman-form objective on `finite_domain ω` is equivalent to minimizing it on all of
`E`, together with membership in `effective_domain g`. -/
lemma isMinOn_scaled_bregman_objective_finiteDomain_iff_mem_effectiveDomain_and_isMinOn_univ
    (f g ω : E → EReal) (xk xNext : E) (Lk : PosReal)
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω) :
    IsMinOn (scaled_bregman_objective f g ω xk Lk) (finite_domain ω) xNext ↔
      xNext ∈ effective_domain g ∧
        IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xNext := by
  constructor
  · intro hmin
    have hxkω_fin : xk ∈ finite_domain ω := by
      -- Upgrade the current iterate from `effective_domain g` to the finite domain of `ω`.
      exact mem_finite_domain_of_mem_effective_domain hω hxk.1
    have hxnext_lt_top :
        scaled_bregman_objective f g ω xk Lk xNext < ⊤ := by
      -- Compare the minimizer with the current iterate, whose objective value is strictly below
      -- `⊤`.
      exact
        lt_of_le_of_lt
          ((isMinOn_iff.mp hmin) xk hxkω_fin)
          (scaled_bregman_objective_lt_top_at_current_iterate f g ω xk Lk hxk.1)
    have hxNext_eff : xNext ∈ effective_domain g := by
      by_contra hxNext_eff
      have htop :
          scaled_bregman_objective f g ω xk Lk xNext = ⊤ :=
        scaled_bregman_objective_eq_top_of_not_mem_effective_domain f g ω xk xNext Lk hxNext_eff
      exact (lt_top_iff_ne_top.mp hxnext_lt_top) htop
    refine ⟨hxNext_eff, ?_⟩
    rw [isMinOn_univ_iff]
    intro y
    by_cases hy : y ∈ effective_domain g
    · -- On feasible comparison points, `hω` upgrades the domain witness to `finite_domain ω`.
      have hyω_fin : y ∈ finite_domain ω := by
        exact mem_finite_domain_of_mem_effective_domain hω hy
      exact (isMinOn_iff.mp hmin) y hyω_fin
    · -- Outside `effective_domain g`, the objective is `⊤`, so the inequality is automatic.
      rw [scaled_bregman_objective_eq_top_of_not_mem_effective_domain f g ω xk y Lk hy]
      exact le_top
  · rintro ⟨hxNext_eff, hmin⟩
    -- Restrict the global minimizing inequality back to `finite_domain ω`.
    rw [isMinOn_iff]
    intro y hy
    exact (isMinOn_univ_iff.mp hmin) y

/-- If `f` is differentiable at `x^k` in the Chapter 3 sense, then the specialized Mirror-C owner
for Algorithm 10.67 has exactly the same minimizers as the textbook Bregman-regularized local
model `non_euclidean_textbook_model f g ω xk Lk` on `finite_domain ω`. -/
theorem isMinOn_mirror_c_update_objective_iff_isMinOn_non_euclidean_proximal_gradient_model
    (f g ω : E → EReal) (xk xNext : E) (Lk : PosReal)
    (hfxk : is_differentiable_at f xk) (hxNext : xNext ∈ finite_domain ω) :
    IsMinOn
      (mirror_c_update_objective g ω xk
        (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
      (finite_domain ω) xNext ↔
      IsMinOn (non_euclidean_textbook_model f g ω xk Lk) (finite_domain ω) xNext :=
  by
    -- First pass through the Chapter 9 Bregman-form bridge, then rescale to the textbook model.
    calc
      IsMinOn
          (mirror_c_update_objective g ω xk
            (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹))
          (finite_domain ω) xNext ↔
        IsMinOn (scaled_bregman_objective f g ω xk Lk) (finite_domain ω) xNext := by
          simpa [scaled_bregman_objective] using
            isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_form
              g ω xk xNext (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹) hxNext
      _ ↔ IsMinOn (non_euclidean_textbook_model f g ω xk Lk) (finite_domain ω) xNext :=
        isMinOn_scaled_bregman_objective_iff_isMinOn_non_euclidean_model f g ω xk xNext Lk hfxk

/-- Helper for Algorithm 10.67: the same positive-affine transport also identifies the scaled
Chapter 9 objective with the textbook model on the unconstrained set `Set.univ`. -/
lemma isMinOn_scaled_bregman_objective_iff_isMinOn_non_euclidean_model_univ
    (f g ω : E → EReal) (xk xNext : E) (Lk : PosReal)
    (hfxk : is_differentiable_at f xk) :
    IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xNext ↔
      IsMinOn (non_euclidean_textbook_model f g ω xk Lk) Set.univ xNext := by
  -- Reuse the generic positive-affine minimizer transport on the unconstrained set.
  exact
    (isMinOn_iff_of_pos_mul_add_constant
      (φ := non_euclidean_textbook_model f g ω xk Lk)
      (ψ := scaled_bregman_objective f g ω xk Lk)
      (s := Set.univ) (z := xNext)
      (a := (Lk : ℝ))
      (c := (f xk).toReal - inner ℝ (∇ (fun y ↦ (f y).toReal) xk) xk)
      (PosReal.coe_pos Lk)
      (fun x ↦ by
        simpa [add_comm] using
          non_euclidean_model_eq_constant_add_scaled_bregman_objective
            f g ω xk x Lk hfxk)).symm

/-- Under the Chapter 3 differentiability hypothesis, Algorithm 10.67 is equivalent to minimizing
the textbook Bregman-regularized local model `non_euclidean_textbook_model f g ω xk Lk` on
`finite_domain ω`, together with the explicit finite-domain guard on `x⁺`. -/
theorem non_euclidean_proximal_gradient_step_iff_isMinOn_non_euclidean_proximal_gradient_model
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hfxk : is_differentiable_at f xk) :
    non_euclidean_proximal_gradient_step f g ω xk Lk xNext ↔
      xNext ∈ finite_domain ω ∧
        IsMinOn (non_euclidean_textbook_model f g ω xk Lk) (finite_domain ω) xNext := by
  rw [non_euclidean_proximal_gradient_step_iff]
  constructor
  · rintro ⟨_, hxNext, hmin⟩
    -- Replace the Mirror-C minimizer clause by the textbook-model one on `finite_domain ω`.
    exact
      ⟨hxNext,
        (isMinOn_mirror_c_update_objective_iff_isMinOn_non_euclidean_proximal_gradient_model
          f g ω xk xNext Lk hfxk hxNext).mp hmin⟩
  · rintro ⟨hxNext, hmin⟩
    -- Repackage the same minimizing point back into the source-facing owner surface.
    exact
      ⟨hfxk, hxNext,
        (isMinOn_mirror_c_update_objective_iff_isMinOn_non_euclidean_proximal_gradient_model
          f g ω xk xNext Lk hfxk hxNext).mpr hmin⟩

/-- Algorithm 10.67: under the Chapter 9 Bregman-potential hypotheses on `ω` over
`effective_domain g` and the current-iterate domain clause, admissible next iterates are exactly
the points in `effective_domain g` that minimize `non_euclidean_textbook_model f g ω xk Lk` on
`Set.univ`. -/
theorem
    non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_textbook_model_univ
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hfxk : is_differentiable_at f xk)
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω) :
    non_euclidean_proximal_gradient_step f g ω xk Lk xNext ↔
      xNext ∈ effective_domain g ∧
        IsMinOn (non_euclidean_textbook_model f g ω xk Lk) Set.univ xNext := by
  -- Route correction: use the already-stabilized scaled-objective `Set.univ` bridge first, then
  -- convert the minimizer predicate through the positive affine identity.
  constructor
  · intro hstep
    rcases (non_euclidean_proximal_gradient_step_iff.mp hstep) with ⟨_, hxNext_fin, hmin⟩
    have hscaled_finite :
        IsMinOn (scaled_bregman_objective f g ω xk Lk) (finite_domain ω) xNext := by
      simpa [scaled_bregman_objective] using
        (isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_form
          g ω xk xNext (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹) hxNext_fin).mp hmin
    rcases
        (isMinOn_scaled_bregman_objective_finiteDomain_iff_mem_effectiveDomain_and_isMinOn_univ
          f g ω xk xNext Lk hω hxk).mp hscaled_finite with
      ⟨hxNext_eff, hmin_scaled⟩
    exact
      ⟨hxNext_eff,
        (isMinOn_scaled_bregman_objective_iff_isMinOn_non_euclidean_model_univ
          f g ω xk xNext Lk hfxk).mp hmin_scaled⟩
  · rintro ⟨hxNext_eff, hmin_model⟩
    have hmin_scaled_univ :
        IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xNext :=
      (isMinOn_scaled_bregman_objective_iff_isMinOn_non_euclidean_model_univ
        f g ω xk xNext Lk hfxk).mpr hmin_model
    have hmin_scaled_finite :
        IsMinOn (scaled_bregman_objective f g ω xk Lk) (finite_domain ω) xNext := by
      exact
        (isMinOn_scaled_bregman_objective_finiteDomain_iff_mem_effectiveDomain_and_isMinOn_univ
          f g ω xk xNext Lk hω hxk).mpr ⟨hxNext_eff, hmin_scaled_univ⟩
    have hxNext_fin : xNext ∈ finite_domain ω := by
      -- Convert the `effective_domain g` witness back to the finite-domain guard used by the owner.
      exact mem_finite_domain_of_mem_effective_domain hω hxNext_eff
    refine (non_euclidean_proximal_gradient_step_iff).mpr ?_
    refine ⟨hfxk, hxNext_fin, ?_⟩
    simpa [scaled_bregman_objective] using
      (isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_form
        g ω xk xNext (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹) hxNext_fin).mpr
        hmin_scaled_finite

/-- Helper for Algorithm 10.67: a short-name compatibility alias for the canonical unconstrained
textbook-model characterization of admissible next iterates. -/
theorem non_euclidean_proximal_gradient_step_iff_textbook_model_argmin
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hfxk : is_differentiable_at f xk)
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω) :
    non_euclidean_proximal_gradient_step f g ω xk Lk xNext ↔
      xNext ∈ effective_domain g ∧
        IsMinOn (non_euclidean_textbook_model f g ω xk Lk) Set.univ xNext := by
  -- This short label theorem forwards to the canonical chapter API.
  exact
    non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_textbook_model_univ
      hω hfxk hxk

/-- Helper for Algorithm 10.67: under the Bregman-potential and current-iterate hypotheses, every
admissible non-Euclidean proximal-gradient step lands in `effective_domain g`. -/
theorem non_euclidean_proximal_gradient_step.mem_effective_domain
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω)
    (hstep : non_euclidean_proximal_gradient_step f g ω xk Lk xNext) :
    xNext ∈ effective_domain g := by
  -- Feed the step's built-in differentiability witness into the canonical unconstrained
  -- characterization, then project the domain membership conclusion.
  exact
    ((non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_textbook_model_univ
      (f := f) (g := g) (ω := ω) (xk := xk) (xNext := xNext) (Lk := Lk)
      hω hstep.differentiable_at hxk).mp hstep).1

/-- Helper for Algorithm 10.67: under the Bregman-potential and current-iterate hypotheses, every
admissible non-Euclidean proximal-gradient step is a global minimizer of the textbook model on
`Set.univ`. -/
theorem non_euclidean_proximal_gradient_step.isMinOn_textbook_model_univ
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω)
    (hstep : non_euclidean_proximal_gradient_step f g ω xk Lk xNext) :
    IsMinOn (non_euclidean_textbook_model f g ω xk Lk) Set.univ xNext := by
  -- The same unconstrained characterization also packages the global minimizer clause.
  exact
    ((non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_textbook_model_univ
      (f := f) (g := g) (ω := ω) (xk := xk) (xNext := xNext) (Lk := Lk)
      hω hstep.differentiable_at hxk).mp hstep).2

/-- Helper for Algorithm 10.67: a short-name compatibility alias for the canonical unconstrained
textbook-model characterization of admissible next iterates. -/
theorem non_euclidean_proximal_gradient_step_iff_textbook_model_univ
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hfxk : is_differentiable_at f xk)
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω) :
    non_euclidean_proximal_gradient_step f g ω xk Lk xNext ↔
      xNext ∈ effective_domain g ∧
        IsMinOn (non_euclidean_textbook_model f g ω xk Lk) Set.univ xNext := by
  -- This short-name alias forwards to the canonical theorem used by downstream API.
  exact
    non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_textbook_model_univ
      hω hfxk hxk

/-- Under the same Bregman-potential and current-iterate domain hypotheses, Algorithm 10.67 can
equivalently be used through the unconstrained Chapter 9 Bregman-form objective:
the next iterate lies in `effective_domain g` and minimizes
`scaled_bregman_objective f g ω xk Lk` on `Set.univ`. -/
theorem
    non_euclidean_proximal_gradient_step_iff_mem_effective_domain_and_isMinOn_scaled_objective_univ
    {f g ω : E → EReal} {xk xNext : E} {Lk : PosReal}
    (hω : IsBregmanPotentialOn ω (effective_domain g) (1 : ℝ))
    (hfxk : is_differentiable_at f xk)
    (hxk : xk ∈ effective_domain g ∩ subdifferential_domain ω) :
    non_euclidean_proximal_gradient_step f g ω xk Lk xNext ↔
      xNext ∈ effective_domain g ∧
        IsMinOn (scaled_bregman_objective f g ω xk Lk) Set.univ xNext := by
  rw [non_euclidean_proximal_gradient_step_iff]
  constructor
  · rintro ⟨_, hxNext, hmin⟩
    -- Convert the source-facing Mirror-C minimizer into the scaled Chapter 9 objective, then
    -- transport that minimizer from `finite_domain ω` to `Set.univ`.
    have hscaled_finite :
        IsMinOn (scaled_bregman_objective f g ω xk Lk) (finite_domain ω) xNext := by
      simpa [scaled_bregman_objective] using
        (isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_form
          g ω xk xNext (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹) hxNext).mp hmin
    exact
      (isMinOn_scaled_bregman_objective_finiteDomain_iff_mem_effectiveDomain_and_isMinOn_univ
        f g ω xk xNext Lk hω hxk).mp hscaled_finite
  · rintro ⟨hxNext_eff, hmin⟩
    have hxNext_fin : xNext ∈ finite_domain ω := by
      -- Feasibility for `g` upgrades to feasibility for `ω` via the Bregman-potential owner.
      exact mem_finite_domain_of_mem_effective_domain hω hxNext_eff
    have hscaled_finite :
        IsMinOn (scaled_bregman_objective f g ω xk Lk) (finite_domain ω) xNext := by
      exact
        (isMinOn_scaled_bregman_objective_finiteDomain_iff_mem_effectiveDomain_and_isMinOn_univ
          f g ω xk xNext Lk hω hxk).mpr ⟨hxNext_eff, hmin⟩
    -- Repackage the finite-domain scaled minimizer back into the Mirror-C owner.
    refine ⟨hfxk, hxNext_fin, ?_⟩
    simpa [scaled_bregman_objective] using
      (isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_form
        g ω xk xNext (fderiv ℝ (fun y ↦ (f y).toReal) xk) ((Lk : ℝ)⁻¹) hxNext_fin).mpr
        hscaled_finite

end
