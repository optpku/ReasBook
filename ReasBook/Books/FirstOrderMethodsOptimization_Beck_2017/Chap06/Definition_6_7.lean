/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

/-- Positive real parameters used by the chapter's source-facing smoothing owners. -/
abbrev PosReal := Set.Ioi (0 : ℝ)

namespace PosReal

/-- The canonical coercion-free bridge from the chapter's positive real parameters to `NNReal`. -/
def toNNReal (x : PosReal) : NNReal :=
  ⟨x, x.2.le⟩

instance : One PosReal := ⟨1, by simp⟩

instance : Add PosReal := ⟨fun x y ↦ ⟨(x : ℝ) + y, by simpa using add_pos x.2 y.2⟩⟩

instance : Inv PosReal := ⟨fun x ↦ ⟨(x : ℝ)⁻¹, by
  change 0 < ((x : ℝ)⁻¹)
  have hx : 0 < x.1 := x.2
  exact inv_pos.mpr hx⟩⟩

instance : Div PosReal := ⟨fun x y ↦ ⟨(x : ℝ) / y, by simpa using div_pos x.2 y.2⟩⟩

@[simp, norm_cast] theorem coe_one : ((1 : PosReal) : ℝ) = 1 := by
  rfl

@[simp, norm_cast] theorem coe_add (x y : PosReal) : ((x + y : PosReal) : ℝ) = (x : ℝ) + y := by
  cases x
  cases y
  rfl

@[simp, norm_cast] theorem coe_inv (x : PosReal) : ((x⁻¹ : PosReal) : ℝ) = (x : ℝ)⁻¹ := by
  cases x
  rfl

@[simp, norm_cast] theorem coe_div (x y : PosReal) : ((x / y : PosReal) : ℝ) = (x : ℝ) / y := by
  cases x
  cases y
  rfl

@[simp] theorem coe_pos (x : PosReal) : 0 < (x : ℝ) := x.2

@[simp] theorem coe_toNNReal (x : PosReal) : ((PosReal.toNNReal x : NNReal) : ℝ) = x := rfl

end PosReal

section

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 6.7 is `source-facing`: the chapter already owns the set-valued proximal mapping
`prox[...]`, and Chapter 2 already owns `infimal_convolution` as the canonical pointwise-infimum
operator. The new owner here is the Moreau-envelope value function itself, with the quadratic
kernel as its only primitive auxiliary data. The textbook relation with `prox_{μ f}(x)` is then
recorded through a bridge theorem rather than by introducing a parallel single-valued proximal
operator. Since the textbook Moreau parameter is genuinely positive data, the owner parameter is a
positive real rather than a bare scalar together with a separate proof. -/

/-- The quadratic kernel `ω_μ` used in the Moreau envelope for a positive parameter `μ`:
`ω_μ x = (1 / (2 * μ)) ‖x‖²`, viewed in `EReal`. -/
def moreau_quadratic_kernel (μ : PosReal) : E → EReal :=
  fun x ↦ ((((1 / (2 * μ) : ℝ) * ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal)

@[inherit_doc] notation "ω(" μ ")" => moreau_quadratic_kernel μ

-- Proof sketch: unfold `moreau_quadratic_kernel`; the displayed formula is exactly the defining
-- quadratic penalty.
/-- Evaluating `ω(μ)` at `x` gives `(1 / (2 * μ)) ‖x‖²` in `EReal`. -/
@[simp] theorem moreau_quadratic_kernel_apply (μ : PosReal) (x : E) :
    ω(μ) x = ((((1 / (2 * μ) : ℝ) * ‖x‖ ^ (2 : ℕ)) : ℝ) : EReal) :=
  rfl

/-- Definition 6.7: the Moreau envelope of `f` with positive smoothing parameter `μ` is the
pointwise infimum of the penalized objective `u ↦ f u + (1 / (2 * μ)) ‖x - u‖²`. -/
def moreau_envelope (μ : PosReal) (f : E → EReal) : E → EReal :=
  f □ ω(μ)

/-- Textbook notation for the Moreau envelope with smoothing parameter `μ`. -/
notation "M[" μ ", " f "]" => moreau_envelope μ f

-- Proof sketch: unfold `moreau_envelope` and apply the owner-level formula
-- `infimal_convolution_apply`; the quadratic kernel then expands to the displayed penalty.
/-- Evaluating the Moreau envelope at `x` gives the infimum of its penalized objective over all
points `u`. -/
@[simp] theorem moreau_envelope_apply (μ : PosReal) (f : E → EReal) (x : E) :
    M[μ, f] x =
      ⨅ u : E, f u + ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  simp [moreau_envelope, infimal_convolution_apply]

/-- Helper for Definition 6.7: dividing the scaled proximal objective by `μ` gives exactly the
Moreau penalized objective. -/
lemma scaled_proximal_objective_div_eq_moreau_penalty {f : E → EReal} {μ : PosReal}
    {x v : E} :
    proximal_objective (((μ : EReal) • f)) x v / ((μ : ℝ) : EReal) =
      f v + ((((1 / (2 * μ) : ℝ) * ‖x - v‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  have hμ_nonneg : 0 ≤ ((μ : ℝ) : EReal) := by
    exact_mod_cast μ.2.le
  have hμ_top : ((μ : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
  have hμ_bot : ((μ : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot _
  have hμ_zero : ((μ : ℝ) : EReal) ≠ 0 := by
    exact_mod_cast μ.2.ne'
  -- Divide the scaled objective termwise, then cancel the positive factor `μ` on `f`.
  rw [proximal_objective_apply, Pi.smul_apply, smul_eq_mul,
    EReal.add_div_of_nonneg_right hμ_nonneg]
  rw [mul_comm (((μ : ℝ) : EReal)) (f v), ← EReal.mul_div_right,
    EReal.div_mul_cancel hμ_bot hμ_top hμ_zero]
  -- The remaining quadratic term is the Moreau penalty after rewriting the coefficient.
  have hquad :
      (((((1 / 2 : ℝ) * ‖v - x‖ ^ (2 : ℕ)) : ℝ) : EReal) / ((μ : ℝ) : EReal)) =
        ((((1 / (2 * μ) : ℝ) * ‖x - v‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
    rw [norm_sub_rev, div_eq_mul_inv]
    have hcoeff :
        ((((1 / (2 * μ) : ℝ) * ‖x - v‖ ^ (2 : ℕ)) : ℝ) : EReal) =
          (((μ : ℝ) : EReal)⁻¹ * (((((1 / 2 : ℝ) * ‖x - v‖ ^ (2 : ℕ)) : ℝ) : EReal))) := by
      norm_num [EReal.coe_mul, EReal.coe_inv, EReal.coe_pow]
      rw [mul_assoc]
    rw [hcoeff]
    ac_rfl
  rw [hquad]

/-- Helper for Definition 6.7: any point of the scaled proximal set minimizes the Moreau
penalized objective. -/
lemma isMinOn_moreau_penalty_of_mem_scaled_prox {f : E → EReal} {μ : PosReal} {x u : E}
    (hu : u ∈ prox[((μ : EReal) • f)] x) :
    IsMinOn (fun v : E ↦ f v + ((((1 / (2 * μ) : ℝ) * ‖x - v‖ ^ (2 : ℕ)) : ℝ) : EReal))
      Set.univ u := by
  rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
  rw [isMinOn_univ_iff]
  intro v
  -- Start from the scaled proximal minimizer inequality.
  have huv_scaled :
      proximal_objective (((μ : EReal) • f)) x u ≤ proximal_objective (((μ : EReal) • f)) x v :=
    hu v
  -- Division by the positive parameter preserves the order.
  have huv_div :
      proximal_objective (((μ : EReal) • f)) x u / ((μ : ℝ) : EReal) ≤
        proximal_objective (((μ : EReal) • f)) x v / ((μ : ℝ) : EReal) := by
    exact EReal.monotone_div_right_of_nonneg (by exact_mod_cast μ.2.le) huv_scaled
  -- Rewrite both divided objectives into the Moreau penalized objective.
  rw [scaled_proximal_objective_div_eq_moreau_penalty,
    scaled_proximal_objective_div_eq_moreau_penalty] at huv_div
  exact huv_div

-- Proof sketch: membership in `prox[((μ : EReal) • f)] x` means that `u` minimizes the
-- scaled objective `v ↦ μ * f v + (1 / 2) ‖x - v‖²`. Since `μ` is positive by type, this
-- objective is a positive scalar multiple of the penalized objective in
-- `moreau_envelope_apply`, so the minimizers coincide. Evaluating the infimum at that minimizing
-- point yields the displayed formula.
/-- Any point of the scaled proximal set realizes the Moreau-envelope value. This is the canonical
bridge from the chapter's set-valued proximal mapping to the textbook Moreau-envelope formula. -/
theorem moreau_envelope_eq_of_mem_scaled_prox {f : E → EReal} {μ : PosReal} {x u : E}
    (hu : u ∈ prox[((μ : EReal) • f)] x) :
    M[μ, f] x = f u + ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- First identify `u` as a minimizer of the Moreau penalized objective.
  have hmin :
      IsMinOn (fun v : E ↦ f v + ((((1 / (2 * μ) : ℝ) * ‖x - v‖ ^ (2 : ℕ)) : ℝ) : EReal))
        Set.univ u :=
    isMinOn_moreau_penalty_of_mem_scaled_prox hu
  -- Then evaluate the infimum at that minimizing point.
  rw [moreau_envelope_apply]
  simpa [iInf_subtype] using IsMinOn.iInf_eq (by simp) hmin

-- Proof sketch: the singleton hypothesis gives `u ∈ prox[((μ : EReal) • f)] x`; then
-- apply `moreau_envelope_eq_of_mem_scaled_prox`.
/-- If the scaled proximal set at `x` is the singleton `{u}`, then the Moreau envelope at `x` is
the value of the penalized objective at `u`. When Theorem 6.3 supplies this singleton proximal
set for proper closed convex data, this is exactly the textbook identity
`M_f^μ(x) = f(u) + (1 / (2 * μ)) ‖x - u‖²` with `u = prox_{μ f}(x)`. -/
theorem moreau_envelope_eq_of_scaled_prox_eq_singleton {f : E → EReal} {μ : PosReal}
    {x u : E} (hprox : prox[((μ : EReal) • f)] x = {u}) :
    M[μ, f] x = f u + ((((1 / (2 * μ) : ℝ) * ‖x - u‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
  -- The singleton hypothesis supplies the required proximal-set membership.
  have hu : u ∈ prox[((μ : EReal) • f)] x := by
    simp [hprox]
  exact moreau_envelope_eq_of_mem_scaled_prox hu

end
