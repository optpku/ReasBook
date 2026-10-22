/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Theorem 3.1.21 lies in the chapter's extended-valued homogeneous-subdifferential domain.

Primary domain:
- convex analysis of `ℝ ∪ {+∞}`-valued functions on real inner-product spaces, with effective
  domains and subgradients.

Relevant owner-style declarations sampled before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite real part of a `WithTop ℝ`-valued function;
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner API for
  unconstrained subgradients;
- `IsPositivelyHomogeneousOn` in `Definition_3_1_7`, the chapter owner for positive homogeneity on
  a cone;
- `SMulMemClass.smul_mem`, the canonical closure API on cone-shaped domains.

Best owner abstraction:
- `IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f)`.

Primitive data:
- an extended-valued function `f : E → WithTop ℝ`;
- a degree `p : ℝ`;
- the source-facing homogeneity owner on the effective domain;
- a subgradient witness `hg : g ∈ ∂ f(x)`.

Derived API:
- closure of `dom f` under nonnegative scaling from `hhom.smul_mem`;
- the rescaling identity for `withTopRealPart f` from `hhom.map_smul`.

Source/core/bridge triage:
- source-facing: Euler's identity for subgradients of an extended-valued homogeneous function;
- core/canonical: the chapter owners `subdifferential` and `IsPositivelyHomogeneousOn`;
- bridge/view: `dom f` and `withTopRealPart f` from `Definition_3_3`.

The previous version introduced a second public homogeneity predicate specialized to effective
domains, together with projection lemmas that duplicated the already canonical owner
`IsPositivelyHomogeneousOn`. This file now states the theorem directly on the chapter owner
abstraction, leaving the effective-domain view as the canonical specialization
`s = dom f, f = withTopRealPart f` rather than as a parallel API root.
-/

-- The theorem uses the standard ray argument, so the dedicated helpers below first rewrite the
-- homogeneous scaling law and then package the right- and left-slope estimates separately.
/-- Helper for Theorem 3.1.21: nonnegative rescaling on the effective domain rewrites
`withTopRealPart f` exactly by the homogeneous degree law. -/
lemma withTopRealPart_map_smul_of_nonneg
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x : E} (hx : x ∈ dom f) {τ : ℝ} (hτ : 0 ≤ τ) :
    withTopRealPart f (τ • x) = τ ^ p * withTopRealPart f x := by
  -- Repackage the scalar as an `NNReal` so the owner homogeneity API applies verbatim.
  simpa using hhom.map_smul hx ⟨τ, hτ⟩

/-- Helper for Theorem 3.1.21: evaluating the subgradient inequality at the ray point `τ • x`
produces the scalar inequality that drives Euler's identity. -/
lemma subgradient_ray_inequality
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x g : E} (hg : g ∈ ∂ f(x)) {τ : ℝ} (hτ : 0 ≤ τ) :
    τ ^ p * withTopRealPart f x ≥ withTopRealPart f x + (τ - 1) * inner ℝ g x := by
  have hx_dom : x ∈ dom f := (mem_subdifferential_iff.mp hg).mem_dom
  have hτx_dom : τ • x ∈ dom f := hhom.smul_mem hx_dom ⟨τ, hτ⟩
  have hsub :
      f (τ • x) ≥ f x + (inner ℝ g (τ • x - x) : WithTop ℝ) :=
    (mem_subdifferential_iff.mp hg).2 hτx_dom
  -- Convert the owner inequality from `WithTop ℝ` back to the finite real part on the domain.
  rw [← coe_withTopRealPart hτx_dom, ← coe_withTopRealPart hx_dom] at hsub
  have hmap : withTopRealPart f (τ • x) = τ ^ p * withTopRealPart f x :=
    withTopRealPart_map_smul_of_nonneg hhom hx_dom hτ
  have hinner : inner ℝ g (τ • x - x) = (τ - 1) * inner ℝ g x := by
    -- Along the ray, the displacement from `x` is the scalar multiple `(τ - 1) • x`.
    calc
      inner ℝ g (τ • x - x) = inner ℝ g ((τ - 1) • x) := by
        congr 1
        simpa [sub_eq_add_neg, one_smul] using (add_smul τ (-1 : ℝ) x).symm
      _ = (τ - 1) * inner ℝ g x := by
        simp [inner_smul_right]
  rw [hmap, hinner] at hsub
  exact_mod_cast hsub

/-- Helper for Theorem 3.1.21: the shifted power profile `t ↦ (1 + t)^p * fx` has derivative
`p * fx` at `t = 0`. -/
lemma one_add_rpow_mul_hasDerivAt_zero {p fx : ℝ} :
    HasDerivAt (fun t : ℝ ↦ (1 + t) ^ p * fx) (p * fx) 0 := by
  have hshift : HasDerivAt (fun t : ℝ ↦ t + 1) 1 0 := by
    -- The shift `t ↦ t + 1` moves the source limit from `τ = 1` to `t = 0`.
    simpa using (hasDerivAt_id 0).add_const (1 : ℝ)
  have hpow : HasDerivAt (fun t : ℝ ↦ (1 + t) ^ p) p 0 := by
    -- Differentiate the power function at `1` and compose with the shift.
    have hcomp :
        HasDerivAt ((fun s : ℝ ↦ s ^ p) ∘ fun t : ℝ ↦ t + 1)
          (p * 1 ^ (p - 1) * 1) 0 := by
      exact HasDerivAt.comp_of_eq
        (x := 0)
        (y := (1 : ℝ))
        (h := fun t : ℝ ↦ t + 1)
        (h₂ := fun s : ℝ ↦ s ^ p)
        (h' := (1 : ℝ))
        (h₂' := p * 1 ^ (p - 1))
        (hh₂ := Real.hasDerivAt_rpow_const (x := 1) (p := p) (Or.inl one_ne_zero))
        (hh := hshift)
        (by simp)
    simpa [Function.comp, mul_comm, mul_left_comm, mul_assoc,
      add_comm, add_left_comm, add_assoc] using hcomp
  -- Multiplying by the constant finite value `fx` gives the scalar profile used in the slope
  -- limits.
  simpa [mul_comm, mul_left_comm, mul_assoc] using hpow.mul_const fx

/-- Helper for Theorem 3.1.21: the `τ > 1` side of the ray inequality gives the upper bound
`⟪g, x⟫ ≤ p * withTopRealPart f x`. -/
lemma inner_le_degree_mul_value
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x g : E} (hg : g ∈ ∂ f(x)) :
    inner ℝ g x ≤ p * withTopRealPart f x := by
  let w : ℝ → ℝ := fun t ↦ (1 + t) ^ p * withTopRealPart f x
  have hw : HasDerivAt w (p * withTopRealPart f x) 0 := by
    -- Shift the quotient from `τ = 1` to `t = 0` so the right-hand derivative theorem applies.
    simpa [w] using one_add_rpow_mul_hasDerivAt_zero (p := p) (fx := withTopRealPart f x)
  have hslope :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        inner ℝ g x ≤ t⁻¹ * (w (0 + t) - w 0) := by
    filter_upwards [Ioc_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    have hτ : 0 ≤ 1 + t := by
      nlinarith [ht.1]
    have hineq : w t ≥ w 0 + t * inner ℝ g x := by
      -- Reuse the ray inequality at `τ = 1 + t`.
      have := subgradient_ray_inequality hhom hg hτ
      simpa [w] using this
    have hdiff : t * inner ℝ g x ≤ w t - w 0 := by
      linarith
    have hquot : inner ℝ g x ≤ (w t - w 0) / t := by
      exact (le_div_iff₀ ht.1).2 (by simpa [mul_comm] using hdiff)
    simpa [div_eq_mul_inv, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using
      hquot
  exact ge_of_tendsto hw.tendsto_slope_zero_right hslope

/-- Helper for Theorem 3.1.21: the `τ < 1` side of the ray inequality gives the lower bound
`p * withTopRealPart f x ≤ ⟪g, x⟫`. -/
lemma degree_mul_value_le_inner
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x g : E} (hg : g ∈ ∂ f(x)) :
    p * withTopRealPart f x ≤ inner ℝ g x := by
  let w : ℝ → ℝ := fun t ↦ (1 + t) ^ p * withTopRealPart f x
  have hw : HasDerivAt w (p * withTopRealPart f x) 0 := by
    -- The same shifted profile controls the left-hand slope as `t ↑ 0`.
    simpa [w] using one_add_rpow_mul_hasDerivAt_zero (p := p) (fx := withTopRealPart f x)
  have hslope :
      ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Iio 0),
        t⁻¹ * (w (0 + t) - w 0) ≤ inner ℝ g x := by
    filter_upwards [Ico_mem_nhdsLT (show (-1 : ℝ) < 0 by norm_num)] with t ht
    have hτ : 0 ≤ 1 + t := by
      nlinarith [ht.1]
    have hineq : w t ≥ w 0 + t * inner ℝ g x := by
      -- Reuse the same ray inequality, now with a negative increment `t`.
      have := subgradient_ray_inequality hhom hg hτ
      simpa [w] using this
    have hdiff : t * inner ℝ g x ≤ w t - w 0 := by
      linarith
    have hquot : (w t - w 0) / t ≤ inner ℝ g x := by
      exact (div_le_iff_of_neg ht.2).2 (by simpa [mul_comm] using hdiff)
    simpa [div_eq_mul_inv, sub_eq_add_neg, add_comm, mul_comm, mul_left_comm, mul_assoc] using
      hquot
  exact le_of_tendsto hw.tendsto_slope_zero_left hslope

/-- Theorem 3.1.21: if an `ℝ ∪ {+∞}`-valued function is homogeneous of degree `p` on its
effective domain, then every subgradient `g ∈ ∂ f(x)` satisfies `⟪g, x⟫ = p f(x)` on the finite
real part of `f`. -/
-- Proof sketch: apply the subgradient inequality to the points `τ • x` along the ray through
-- `x`, then rewrite the function values using the homogeneity assumption. Dividing by `τ - 1` for
-- `τ > 1` and `0 ≤ τ < 1` yields opposite inequalities for `inner ℝ g x`; passing to the limit
-- `τ → 1` gives `inner ℝ g x = p * withTopRealPart f x`.
theorem euler_homogeneous_function_theorem
    {f : E → WithTop ℝ} {p : ℝ}
    (hhom : IsPositivelyHomogeneousOn p (dom f) (withTopRealPart f))
    {x g : E} (hg : g ∈ ∂ f(x)) :
    inner ℝ g x = p * withTopRealPart f x := by
  -- The right- and left-hand slope limits give matching upper and lower bounds.
  exact le_antisymm (inner_le_degree_mul_value hhom hg) (degree_mul_value_le_inner hhom hg)

end
