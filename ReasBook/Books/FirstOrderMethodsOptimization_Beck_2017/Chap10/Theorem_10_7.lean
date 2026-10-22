/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_14
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open InnerProductSpace (toDual toDualMap)
open scoped Gradient Pointwise

/-
Theorem 10.7 lives in the Chapter 10 proximal-gradient/Chapter 3 stationarity interface.

- `core/canonical`: `gradient_mapping` from Definition 10.5, `prox_grad_operator`/`T[...]` from
  Definition 10.9, and `is_stationary_point` from Definition 3.17.
- `bridge/view`: this file, which identifies vanishing prox-grad residuals with the Chapter 3
  stationarity owner, and specializes the zero-penalty case to the ambient gradient.

The primitive data are therefore just the existing owners. The zero-penalty theorem should reuse
the Chapter 6 singleton proximal computation `prox_zero_eq_singleton` instead of introducing any
parallel single-valued update definition.
-/

section ZeroPenalty

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

-- Proof sketch: the constant zero function never takes the value `⊥`, every point lies in its
-- effective domain, it is continuous as an `EReal`-valued constant function, and its real-valued
-- restriction is convex on `Set.univ`.
omit [InnerProductSpace ℝ E] [ProperSpace E] in
local instance zero_isProperExtendedRealFunction :
    IsProperExtendedRealFunction (0 : E → EReal) := by
  refine
    { ne_bot := ?_
      effective_domain_nonempty := ?_ }
  · intro x
    simp
  · refine ⟨0, ?_⟩
    simp [effective_domain]

omit [InnerProductSpace ℝ E] [ProperSpace E] in
local instance zero_factLowerSemicontinuous : Fact (LowerSemicontinuous (0 : E → EReal)) := by
  refine ⟨?_⟩
  simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : E ↦ (0 : EReal)))

omit [ProperSpace E] in
local instance zero_factIsConvexFunction : Fact (is_convex_function (0 : E → EReal)) := by
  refine ⟨?_⟩
  refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
  · intro x hx
    simp
  · simpa [effective_domain] using
      (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))

-- Proof sketch: specialize the Chapter 10 owner `gradient_mapping` to the zero penalty and use
-- the Chapter 6 owner theorem `prox_zero_eq_singleton`, so `T_L^{f,0}(x) = x - (1 / L) ∇ f(x)`.
-- The residual `L • (x - T_L(x))` then collapses formally to the ambient gradient term
-- `∇ (fun y ↦ (f y).toReal) (x : E)`.
/-- Theorem 10.7 (1): specializing the Chapter 10 gradient mapping to the zero penalty `g₀ = 0`
recovers the ambient gradient of `f.toReal` on `interior (effective_domain f)`. -/
theorem gradient_mapping_zero_penalty_eq_gradient
    (f : E → EReal) (L : PosReal) (x : interior (effective_domain f)) :
    G[L, f, 0] x =
      ∇ (fun y ↦ (f y).toReal) (x : E) := by
  have hstep :
      proximal_gradient_step f (0 : E → EReal) (x : E) L =
        {(x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E)} := by
    simpa [proximal_gradient_step] using
      (prox_zero_eq_singleton ((x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E)))
  have hT :
      T[L, f, 0] x =
        (x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E) := by
    apply Set.singleton_injective
    calc
      {T[L, f, 0] x} = proximal_gradient_step f (0 : E → EReal) (x : E) L := by
        symm
        simpa using prox_grad_operator_eq_singleton f (0 : E → EReal) L x
      _ = {(x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E)} := hstep
  have hL :
      ((L : ℝ) * (1 / L : ℝ)) = 1 := by
    field_simp [show (L : ℝ) ≠ 0 by exact (PosReal.coe_pos L).ne']
  calc
    G[L, f, 0] x = (L : ℝ) • ((x : E) - T[L, f, 0] x) :=
      gradient_mapping_apply f (0 : E → EReal) L x
    _ = (L : ℝ) • ((1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E)) := by
      rw [hT]
      simp
    _ = ∇ (fun y ↦ (f y).toReal) (x : E) := by
      rw [smul_smul, hL, one_smul]

end ZeroPenalty

section StationaryPoint

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f g : E → EReal} [IsProperExtendedRealFunction g]
  [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]

/-- Helper for Theorem 10.7: vanishing of the gradient mapping is exactly the fixed-point
equation for the prox-grad operator. -/
private lemma gradient_mapping_eq_zero_iff_fixed_point
    (L : PosReal) (x : interior (effective_domain f)) :
    G[L, f, g] x = 0 ↔
      T[L, f, g] x = (x : E) := by
  constructor
  · intro hG
    -- The residual can vanish only if the prox-grad displacement itself is zero.
    rw [gradient_mapping_apply] at hG
    have hsub : ((x : E) - T[L, f, g] x) = 0 := by
      rcases smul_eq_zero.mp hG with hL | hsub
      · exact False.elim ((PosReal.coe_pos L).ne' hL)
      · exact hsub
    exact sub_eq_zero.mp hsub |> Eq.symm
  · intro hT
    -- Conversely, a fixed point makes the residual formula collapse to zero immediately.
    rw [gradient_mapping_apply, hT]
    simp

/-- Helper for Theorem 10.7: the scaled subgradient condition from the prox theorem is equivalent
to the unscaled stationary-point subgradient condition. -/
private lemma scaled_neg_gradient_mem_scaled_subdifferential_iff
    (L : PosReal) (x : E) :
    (((1 / L : ℝ) •
        (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : Module.Dual ℝ E)) :
          Module.Dual ℝ E) ∈
      subdifferential ((((1 / L : PosReal) : EReal) • g)) x ↔
        (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : Module.Dual ℝ E) ∈
          subdifferential g x := by
  have hL_pos : 0 < (1 / L : ℝ) := one_div_pos.mpr (PosReal.coe_pos L)
  have hscaled :
      subdifferential ((((1 / L : PosReal) : EReal) • g)) x =
        (1 / L : ℝ) • subdifferential g x := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (subdifferential_pos_real_mul g (1 / L : ℝ) hL_pos x)
  have hL_ne : (1 / L : ℝ) ≠ 0 := ne_of_gt hL_pos
  have hmul_inv : ((L : ℝ) * (L : ℝ)⁻¹) = 1 := by
    exact mul_inv_cancel₀ (PosReal.coe_pos L).ne'
  -- Rewrite the scaled subdifferential as a pointwise scalar multiple and cancel the scalar.
  constructor
  · intro hmem
    rw [hscaled, Set.mem_smul_set_iff_inv_smul_mem₀ hL_ne
      (subdifferential g x)
      ((1 / L : ℝ) • (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : Module.Dual ℝ E))] at hmem
    simpa [one_div, smul_smul, hmul_inv] using hmem
  · intro hmem
    rw [hscaled, Set.mem_smul_set_iff_inv_smul_mem₀ hL_ne
      (subdifferential g x)
      ((1 / L : ℝ) • (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) x) : Module.Dual ℝ E))]
    simpa [one_div, smul_smul, hmul_inv] using hmem

/-- Helper for Theorem 10.7: a singleton prox-grad step at `x` is equivalent to the negative
gradient belonging to the subdifferential of `g` at `x`. -/
private lemma proximal_gradient_step_eq_singleton_self_iff_neg_gradient_mem_subdifferential
    (L : PosReal) (x : interior (effective_domain f)) :
    proximal_gradient_step f g (x : E) L = {(x : E)} ↔
      (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) (x : E)) : Module.Dual ℝ E) ∈
        subdifferential g (x : E) := by
  let hg_closed : LowerSemicontinuous g := Fact.out
  let hg_convex : is_convex_function g := Fact.out
  let hg_scaled :=
    scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / L)
  -- Apply the second prox theorem to the scaled penalty at the forward gradient point.
  have hprox :
      proximal_gradient_step f g (x : E) L = {(x : E)} ↔
        toDualMap ℝ E
            (((x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E)) - (x : E)) ∈
          strongDualSubdifferential ((((1 / L : PosReal) : EReal) • g)) (x : E) := by
    simpa [proximal_gradient_step] using
      (prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
        ((((1 / L : PosReal) : EReal) • g))
        hg_scaled.1 hg_scaled.2.2
        ((x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E))
        (x : E))
  have hsub :
      proximal_gradient_step f g (x : E) L = {(x : E)} ↔
        (((1 / L : ℝ) •
            (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) (x : E)) : Module.Dual ℝ E)) :
              Module.Dual ℝ E) ∈
          subdifferential ((((1 / L : PosReal) : EReal) • g)) (x : E) := by
    -- Route correction: rewrite the strong-dual conclusion into the Chapter 3 subdifferential
    -- owner before removing the positive scaling factor.
    simpa [mem_strongDualSubdifferential, InnerProductSpace.toDual_apply_eq_toDualMap_apply,
      sub_eq_add_neg, smul_neg, neg_smul] using hprox
  calc
    proximal_gradient_step f g (x : E) L = {(x : E)} ↔
        (((1 / L : ℝ) •
            (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) (x : E)) : Module.Dual ℝ E)) :
              Module.Dual ℝ E) ∈
          subdifferential ((((1 / L : PosReal) : EReal) • g)) (x : E) := hsub
    _ ↔
        (-toDual ℝ E (∇ (fun y ↦ (f y).toReal) (x : E)) : Module.Dual ℝ E) ∈
          subdifferential g (x : E) :=
      scaled_neg_gradient_mem_scaled_subdifferential_iff L (x : E)

-- Proof sketch: expand `G[L, f, g] xStar = 0` into the fixed-point condition
-- `xStar = T_L^{f,g}(xStar)`. Then use the singleton bridge for `T[L, f, g]` and the proximal
-- optimality condition to rewrite that fixed-point equation as the Chapter 3 owner
-- `is_stationary_point f g (xStar : E)`.
/-- Theorem 10.7 (2): for a proper closed convex penalty `g` and a differentiable point
`xStar ∈ interior (effective_domain f)`, the gradient mapping vanishes at `xStar` if and only if
`xStar` is a stationary point of the composite problem `f + g`. -/
theorem gradient_mapping_eq_zero_iff_is_stationary_point
    (L : PosReal) (xStar : interior (effective_domain f))
    (hdiff : is_differentiable_at f (xStar : E)) :
    G[L, f, g] xStar = 0 ↔
      is_stationary_point f g (xStar : E) := by
  rw [is_stationary_point_iff]
  constructor
  · intro hG
    have hfixed :
        T[L, f, g] xStar = (xStar : E) :=
      (gradient_mapping_eq_zero_iff_fixed_point L xStar).mp hG
    have hstep :
        proximal_gradient_step f g (xStar : E) L = {(xStar : E)} := by
      -- The fixed-point form is converted back to the textbook singleton proximal step.
      calc
        proximal_gradient_step f g (xStar : E) L = {T[L, f, g] xStar} := by
          simpa using prox_grad_operator_eq_singleton f g L xStar
        _ = {(xStar : E)} := by rw [hfixed]
    -- The second prox theorem now gives the subgradient part of stationarity.
    exact
      ⟨hdiff,
        (proximal_gradient_step_eq_singleton_self_iff_neg_gradient_mem_subdifferential
          L xStar).mp hstep⟩
  · rintro ⟨_, hstationary⟩
    have hstep :
        proximal_gradient_step f g (xStar : E) L = {(xStar : E)} :=
      (proximal_gradient_step_eq_singleton_self_iff_neg_gradient_mem_subdifferential
        L xStar).mpr hstationary
    have hfixed :
        T[L, f, g] xStar = (xStar : E) := by
      -- Singleton identification recovers the prox-grad fixed-point equation.
      apply Set.singleton_injective
      calc
        {T[L, f, g] xStar} = proximal_gradient_step f g (xStar : E) L := by
          symm
          simpa using prox_grad_operator_eq_singleton f g L xStar
        _ = {(xStar : E)} := hstep
    -- Returning through the residual/fixed-point equivalence closes the loop.
    exact
      (gradient_mapping_eq_zero_iff_fixed_point L xStar).mpr hfixed

end StationaryPoint
