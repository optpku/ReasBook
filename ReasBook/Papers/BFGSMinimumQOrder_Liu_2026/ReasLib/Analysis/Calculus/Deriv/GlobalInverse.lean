module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.MetricSpace.Antilipschitz
public import Mathlib.Analysis.Calculus.ContDiff.Operations

public section

open Filter
open scoped NNReal Topology

namespace Real

/-- A differentiable real function with a uniform positive lower derivative bound is
strictly increasing. -/
theorem strictMono_of_pos_le_deriv {f : ℝ → ℝ} {lower : ℝ≥0}
    (hf : Differentiable ℝ f) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) :
    StrictMono f := by
  have hlower : (0 : ℝ) < lower := by exact_mod_cast h_lower_pos
  apply strictMono_of_hasDerivAt_pos (fun x ↦ (hf x).hasDerivAt)
  intro x
  exact hlower.trans_le (h_lower x)

/-- A differentiable real function with a uniform positive lower derivative bound tends
to `atTop` at `atTop`. -/
theorem tendsto_atTop_of_pos_le_deriv {f : ℝ → ℝ} {lower : ℝ≥0}
    (hf : Differentiable ℝ f) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) :
    Tendsto f atTop atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  have hlower : (0 : ℝ) < lower := mod_cast h_lower_pos
  filter_upwards [eventually_ge_atTop (max 0 ((b - f 0) / (lower : ℝ)))] with x hx
  have hx0 : 0 ≤ x := (le_max_left _ _).trans hx
  have hxdiv : (b - f 0) / (lower : ℝ) ≤ x := (le_max_right _ _).trans hx
  have hslope := mul_sub_le_image_sub_of_le_deriv hf h_lower hx0
  have hmul : b - f 0 ≤ x * (lower : ℝ) := (div_le_iff₀ hlower).mp hxdiv
  nlinarith

/-- A differentiable real function with a uniform positive lower derivative bound tends
to `atBot` at `atBot`. -/
theorem tendsto_atBot_of_pos_le_deriv {f : ℝ → ℝ} {lower : ℝ≥0}
    (hf : Differentiable ℝ f) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) :
    Tendsto f atBot atBot := by
  refine Filter.tendsto_atBot.2 ?_
  intro b
  have hlower : (0 : ℝ) < lower := mod_cast h_lower_pos
  filter_upwards [eventually_le_atBot (min 0 ((b - f 0) / (lower : ℝ)))] with x hx
  have hx0 : x ≤ 0 := hx.trans (min_le_left _ _)
  have hxdiv : x ≤ (b - f 0) / (lower : ℝ) := hx.trans (min_le_right _ _)
  have hslope := mul_sub_le_image_sub_of_le_deriv hf h_lower hx0
  have hmul : x * (lower : ℝ) ≤ b - f 0 := (le_div_iff₀ hlower).mp hxdiv
  nlinarith

/-- A differentiable real function with a uniform positive lower derivative bound is
surjective. -/
theorem surjective_of_pos_le_deriv {f : ℝ → ℝ} {lower : ℝ≥0}
    (hf : Differentiable ℝ f) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) :
    Function.Surjective f := by
  exact hf.continuous.surjective
    (tendsto_atTop_of_pos_le_deriv hf h_lower_pos h_lower)
    (tendsto_atBot_of_pos_le_deriv hf h_lower_pos h_lower)

/-- A differentiable real function with a uniform positive lower derivative bound is
bijective. -/
theorem bijective_of_pos_le_deriv {f : ℝ → ℝ} {lower : ℝ≥0}
    (hf : Differentiable ℝ f) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) :
    Function.Bijective f := by
  exact ⟨(strictMono_of_pos_le_deriv hf h_lower_pos h_lower).injective,
    surjective_of_pos_le_deriv hf h_lower_pos h_lower⟩

/-- A positive derivative lower bound `lower` gives the reciprocal antilipschitz
constant `lower⁻¹`. -/
theorem antilipschitzWith_inv_of_pos_le_deriv {f : ℝ → ℝ} {lower : ℝ≥0}
    (hf : Differentiable ℝ f) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) :
    AntilipschitzWith lower⁻¹ f := by
  have hlower : (0 : ℝ) < lower := mod_cast h_lower_pos
  have hmono := (strictMono_of_pos_le_deriv hf h_lower_pos h_lower).monotone
  apply AntilipschitzWith.of_le_mul_dist
  have hordered : ∀ ⦃x y : ℝ⦄, x ≤ y →
      dist x y ≤ (lower⁻¹ : ℝ≥0) * dist (f x) (f y) := by
    intro x y hxy
    have hslope := mul_sub_le_image_sub_of_le_deriv hf h_lower hxy
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr (hmono hxy)), NNReal.coe_inv, inv_mul_eq_div]
    exact (le_div_iff₀ hlower).2 (by nlinarith)
  intro x y
  rcases le_total x y with hxy | hyx
  · exact hordered hxy
  · simpa [dist_comm] using hordered hyx

/-- The `Function.invFun` of a function with positive derivative lower bound `lower` is
`lower⁻¹`-Lipschitz. -/
theorem lipschitzWith_invFun_of_pos_le_deriv {f : ℝ → ℝ} {lower : ℝ≥0}
    (hf : Differentiable ℝ f) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) :
    LipschitzWith lower⁻¹ (Function.invFun f) := by
  exact (antilipschitzWith_inv_of_pos_le_deriv hf h_lower_pos h_lower).to_rightInverse
    (Function.rightInverse_invFun
      (surjective_of_pos_le_deriv hf h_lower_pos h_lower))

/-- At every positive finite smoothness order, `Function.invFun` inherits the forward
map's `ContDiff` regularity. -/
theorem contDiff_invFun_of_pos_le_deriv {n : ℕ} {f : ℝ → ℝ} {lower : ℝ≥0}
    (hf : ContDiff ℝ n f) (hn : 1 ≤ n) (h_lower_pos : 0 < lower)
    (h_lower : ∀ x, (lower : ℝ) ≤ deriv f x) :
    ContDiff ℝ n (Function.invFun f) := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hdiff : Differentiable ℝ f := hf.differentiable (by simpa using hn0)
  have hbij := bijective_of_pos_le_deriv hdiff h_lower_pos h_lower
  have hinv_cont : Continuous (Function.invFun f) :=
    (lipschitzWith_invFun_of_pos_le_deriv hdiff h_lower_pos h_lower).continuous
  have hinv_eq : (Equiv.ofBijective f hbij).symm = Function.invFun f := by
    funext y
    apply hbij.1
    change (Equiv.ofBijective f hbij) ((Equiv.ofBijective f hbij).symm y) =
      f (Function.invFun f y)
    rw [Equiv.apply_symm_apply, Function.rightInverse_invFun hbij.2 y]
  let e : ℝ ≃ₜ ℝ :=
    { Equiv.ofBijective f hbij with
      continuous_toFun := hdiff.continuous
      continuous_invFun := by simpa [hinv_eq] using hinv_cont }
  rw [← hinv_eq]
  change ContDiff ℝ n (e.symm : ℝ → ℝ)
  apply e.contDiff_symm_deriv (f' := deriv f)
  · intro x
    have hlower : (0 : ℝ) < lower := by exact_mod_cast h_lower_pos
    exact ne_of_gt (hlower.trans_le (h_lower x))
  · intro x
    simpa [e] using (hdiff x).hasDerivAt
  · simpa [e] using hf

end Real
