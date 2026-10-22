/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 9.10 is a `bridge/view` item in the Chapter 9 Mirror-C/Bregman domain.
Domain sampling points to these existing owners:
- `mirror_c_update_objective` from Definition 9.6 for the source-facing one-step Mirror-C update;
- `mirror_c_problem_functional` from Definition 9.6 for the linear perturbation term;
- Chapter 9's canonical Bregman owner `bregmanDistance` / `B[ω]` from Definition 9.2;
- the defining equations `mirror_c_update_objective_apply` and `bregmanDistance_def`, which already
  encode the gradient term through the canonical owners.

The layer split is therefore:
- `source-facing`: `mirror_c_update_objective`;
- `core/canonical`: `B[ω]`;
- `bridge/view`: the equation-(9.33) rewrite showing that adding an `x`-independent constant turns
  the source-facing owner into the Bregman-form objective.

The primitive data are only the canonical Mirror-C owner from Definition 9.6 and the canonical
Bregman owner from Definition 9.2. This file remains a bridge/view rewrite of those definitions,
but because `B[ω]` is totalized through `(ω x).toReal`, the equation `(9.33)` surface is
source-faithful only on `finite_domain ω`. Accordingly, the bridge records the equation-(9.33)
objective on that finite-valued domain rather than introducing a second totalized wrapper. -/

-- Proof sketch: expand `mirror_c_update_objective`, rewrite the derivative term at `xk` as the
-- gradient pairing `⟪∇ω(xk), x⟫`, expand `B[ω] x xk`, and cancel the `x`-independent constant
-- `ω(xk) - ⟪∇ω(xk), xk⟫`. Because `B[ω]` uses `(ω x).toReal`, this direct calculation is
-- source-faithful only on `finite_domain ω`. The required rewrite is therefore recorded as an
-- `EqOn` there using `mirror_c_update_objective_apply`,
-- `mirror_c_problem_functional_apply`, and `bregmanDistance_def`.
/-- Helper for Text 9.10: the real-valued Mirror-C linear term together with the finite-domain
potential correction is exactly the Bregman-form scalar part of equation `(9.33)`. -/
lemma mirrorCUpdateBregmanRealIdentity
    (ω : E → EReal) (xk x : E) (s : StrongDual ℝ E) (t : ℝ) :
    mirror_c_problem_functional ω xk s t x + (ω x).toReal +
      (inner ℝ (∇ (fun y ↦ (ω y).toReal) xk) xk - (ω xk).toReal) =
        t * s x + B[ω] x xk := by
  have hgrad_x :
      inner ℝ (∇ (fun y ↦ (ω y).toReal) xk) x =
        fderiv ℝ (fun y ↦ (ω y).toReal) xk x := by
    -- Read the gradient as the Riesz representative of the Fréchet derivative at `xk`.
    rw [gradient]
    exact
      (InnerProductSpace.toDual_symm_apply
        (𝕜 := ℝ)
        (E := E)
        (x := x)
        (y := fderiv ℝ (fun y ↦ (ω y).toReal) xk))
  -- Expand both owners once, split the Bregman displacement pairing, and cancel the constants.
  rw [mirror_c_problem_functional_apply, bregmanDistance_def, inner_sub_right, ← hgrad_x]
  ring

/-- Adding the constant `⟪∇ω(x^k), x^k⟫ - ω(x^k)` rewrites the canonical Mirror-C owner from
equation `(9.32)` into the equation `(9.33)` Bregman form
`x ↦ ⟪t s, x⟫ + t g(x) + B_ω(x, x^k)` on `finite_domain ω`. -/
theorem mirror_c_update_objective_add_constant_eq_bregman_form
    (g ω : E → EReal) (xk : E) (s : StrongDual ℝ E) (t : ℝ) :
    Set.EqOn
      (fun x ↦
        mirror_c_update_objective g ω xk s t x +
          Real.toEReal (inner ℝ (∇ (fun y ↦ (ω y).toReal) xk) xk - (ω xk).toReal))
      (fun x ↦
        Real.toEReal (t * s x) + (t : EReal) * g x + Real.toEReal (B[ω] x xk))
      (finite_domain ω) := by
  intro x hx
  have hx_eff : x ∈ effective_domain ω := (mem_finite_domain.mp hx).1
  have hx_ne_top : ω x ≠ ⊤ := (mem_effective_domain.mp hx_eff).ne
  have hx_ne_bot : ω x ≠ ⊥ := (mem_finite_domain.mp hx).2
  have hx_real :
      ω x = Real.toEReal ((ω x).toReal) := by
    -- On `finite_domain ω`, the potential value is represented by its real part.
    simpa using (EReal.coe_toReal hx_ne_top hx_ne_bot).symm
  have hreal :
      mirror_c_problem_functional ω xk s t x + (ω x).toReal +
        (inner ℝ (∇ (fun y ↦ (ω y).toReal) xk) xk - (ω xk).toReal) =
          t * s x + B[ω] x xk :=
    mirrorCUpdateBregmanRealIdentity (ω := ω) (xk := xk) (x := x) (s := s) (t := t)
  -- Replace the finite `ω x` value by its real cast, then lift the scalar identity to `EReal`.
  dsimp
  rw [hx_real]
  simpa [mirror_c_problem_functional_apply, EReal.coe_add, add_assoc, add_left_comm, add_comm]
    using
    congrArg (fun r : ℝ ↦ (r : EReal) + (t : EReal) * g x) hreal

/-- Evaluating the equation `(9.33)` bridge at a point `x` yields the explicit Bregman-form
integrand, provided `x ∈ finite_domain ω`. This is the pointwise companion to
`mirror_c_update_objective_add_constant_eq_bregman_form`. -/
theorem mirror_c_update_objective_add_constant_eq_bregman_form_apply
    (g ω : E → EReal) (xk x : E) (s : StrongDual ℝ E) (t : ℝ)
    (hx : x ∈ finite_domain ω) :
    mirror_c_update_objective g ω xk s t x +
      Real.toEReal (inner ℝ (∇ (fun y ↦ (ω y).toReal) xk) xk - (ω xk).toReal) =
      Real.toEReal (t * s x) + (t : EReal) * g x + Real.toEReal (B[ω] x xk) := by
  simpa using
    mirror_c_update_objective_add_constant_eq_bregman_form g ω xk s t hx

-- Mathlib recall used here: `isMinOn_iff` only compares values on the minimization set; it does
-- not by itself record that the chosen minimizer belongs to that set.
--
-- Proof sketch: rewrite the equation-(9.33) objective pointwise using
-- `mirror_c_update_objective_add_constant_eq_bregman_form_apply`; then the constant shift leaves
-- minimizers unchanged on the finite-valued part of `ω`. Because `B[ω]` totalizes `toReal`,
-- restricting both objectives to `finite_domain ω` is the source-faithful equation-(9.33) owner.
-- To compare `IsMinOn` across that `EqOn`, the candidate point must also lie in `finite_domain ω`;
-- otherwise the two objectives can disagree at the witness itself and create spurious minimizers.
/-- Text 9.10: the Mirror-C update formula can be rewritten from the linearized objective
in equation `(9.32)` to the Bregman-distance objective in equation `(9.33)` without changing the
set of minimizers on the finite-valued domain of `ω`, provided the chosen minimizer itself lies in
that domain. -/
theorem isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_form
    (g ω : E → EReal) (xk xNext : E) (s : StrongDual ℝ E) (t : ℝ)
    (hxNext : xNext ∈ finite_domain ω) :
    IsMinOn (mirror_c_update_objective g ω xk s t) (finite_domain ω) xNext ↔
      IsMinOn
        (fun x ↦ Real.toEReal (t * s x) + (t : EReal) * g x + Real.toEReal (B[ω] x xk))
        (finite_domain ω) xNext := by
  let c : ℝ :=
    inner ℝ (∇ (fun y ↦ (ω y).toReal) xk) xk - (ω xk).toReal
  constructor
  · intro h
    rw [isMinOn_iff] at h ⊢
    intro y hy
    have hxEq :
        mirror_c_update_objective g ω xk s t xNext + (c : EReal) =
          Real.toEReal (t * s xNext) + (t : EReal) * g xNext +
            Real.toEReal (B[ω] xNext xk) := by
      -- Rewrite the objective at the candidate point by the finite-domain bridge.
      simpa [c] using
        mirror_c_update_objective_add_constant_eq_bregman_form_apply
          (g := g) (ω := ω) (xk := xk) (x := xNext) (s := s) (t := t) hxNext
    have hyEq :
        mirror_c_update_objective g ω xk s t y + (c : EReal) =
          Real.toEReal (t * s y) + (t : EReal) * g y + Real.toEReal (B[ω] y xk) := by
      -- The same bridge applies to every comparison point in `finite_domain ω`.
      simpa [c] using
        mirror_c_update_objective_add_constant_eq_bregman_form_apply
          (g := g) (ω := ω) (xk := xk) (x := y) (s := s) (t := t) hy
    -- Adding the same finite constant preserves the minimizing inequality.
    have hshift :
        mirror_c_update_objective g ω xk s t xNext + (c : EReal) ≤
          mirror_c_update_objective g ω xk s t y + (c : EReal) := by
      simpa [add_assoc, add_left_comm, add_comm] using add_le_add_right (h y hy) (c : EReal)
    rw [hxEq, hyEq] at hshift
    exact hshift
  · intro h
    rw [isMinOn_iff] at h ⊢
    intro y hy
    have hxEq :
        mirror_c_update_objective g ω xk s t xNext + (c : EReal) =
          Real.toEReal (t * s xNext) + (t : EReal) * g xNext +
            Real.toEReal (B[ω] xNext xk) := by
      -- Reuse the same pointwise bridge at the candidate point.
      simpa [c] using
        mirror_c_update_objective_add_constant_eq_bregman_form_apply
          (g := g) (ω := ω) (xk := xk) (x := xNext) (s := s) (t := t) hxNext
    have hyEq :
        mirror_c_update_objective g ω xk s t y + (c : EReal) =
          Real.toEReal (t * s y) + (t : EReal) * g y + Real.toEReal (B[ω] y xk) := by
      -- Reuse the same pointwise bridge at the comparison point.
      simpa [c] using
        mirror_c_update_objective_add_constant_eq_bregman_form_apply
          (g := g) (ω := ω) (xk := xk) (x := y) (s := s) (t := t) hy
    have hshift :
        mirror_c_update_objective g ω xk s t xNext + (c : EReal) ≤
          mirror_c_update_objective g ω xk s t y + (c : EReal) := by
      -- Rewrite the Bregman-form inequality back to the source-facing owner.
      rw [hxEq, hyEq]
      exact h y hy
    exact (EReal.addLECancellable_coe c).add_le_add_iff_right.mp hshift

/-- If the candidate point is already known to lie in `finite_domain ω`, then Text 9.10 reduces
to the expected pointwise comparison of the equation `(9.32)` and `(9.33)` objectives on that
domain. -/
theorem isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_form_of_mem
    (g ω : E → EReal) (xk xNext : E) (s : StrongDual ℝ E) (t : ℝ)
    (hxNext : xNext ∈ finite_domain ω) :
    IsMinOn (mirror_c_update_objective g ω xk s t) (finite_domain ω) xNext ↔
      IsMinOn
        (fun x ↦ Real.toEReal (t * s x) + (t : EReal) * g x + Real.toEReal (B[ω] x xk))
        (finite_domain ω) xNext := by
  -- This companion theorem is exactly the main equivalence with the membership witness exposed.
  simpa using
    isMinOn_mirror_c_update_objective_iff_isMinOn_bregman_form
      (g := g) (ω := ω) (xk := xk) (xNext := xNext) (s := s) (t := t) hxNext

end
