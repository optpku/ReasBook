/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_35
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Corollary 10.8 is `source-facing`.

Domain sampling in the local Chapter 10 owner ecosystem:
- `IsCompositeSmoothMinimizationProblem` from Definition 10.3 separates the primitive smooth-term
  hypothesis `f_ne_bot : ∀ y, f y ≠ ⊥` from the derived properness of `f`;
- `effective_domain` and `finite_domain` from Chapters 2 and 3 are the canonical domain owners for
  extended-real functions;
- `is_differentiable_at` from Definition 3.10 is the Chapter 3 owner notion used by Theorem 10.7.

This file remains `source-facing`, so it should use only the primitive smooth-term data actually
needed here: `f` never takes the value `⊥`. The nonempty-domain part of properness is derived
elsewhere in Chapter 10 from properness of `g` and the domain-inclusion hypothesis, so keeping full
properness of `f` in these local statements would overstate the source mathematics. -/

-- Proof sketch: use `is_l_smooth_on_iff` on `interior (effective_domain f)` to obtain
-- differentiability of `fun y ↦ (f y).toReal` at `x`, and use the no-`⊥` hypothesis to rewrite
-- the Chapter 3 finite-domain interior condition as `x ∈ interior (effective_domain f)`.
/-- An extended-real-valued function that never takes the value `-∞` and is smooth on
`interior (effective_domain f)` is differentiable there in the Chapter 3 sense. -/
theorem is_differentiable_at_of_mem_interior_effective_domain
    {f : E → EReal} (hf_ne_bot : ∀ y, f y ≠ ⊥) {Lf : NNReal}
    (hf_smooth : is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : E} (hx : x ∈ interior (effective_domain f)) :
    is_differentiable_at f x := by
  simpa [is_differentiable_at, finite_domain_eq_effective_domain hf_ne_bot] using
    ⟨hx, hf_smooth.1 x hx⟩

end

section

variable {E : Type u}
variable {f g : E → EReal}

local notation "F" => composite_model_objective f g

-- Proof sketch: the forward implication is restriction of a global minimizer. For the converse,
-- if `y ∉ effective_domain g`, then `g y = ⊤`, and the no-`⊥` hypothesis on `f` gives
-- `f y ≠ ⊥`, hence
-- `f y + g y = ⊤`; therefore points outside `effective_domain g` cannot improve the objective.
/-- If the smooth term never takes the value `-∞`, then minimizing `f + g` over all of `E` is
equivalent to minimizing it on `effective_domain g`, because the composite objective is `⊤`
outside `effective_domain g`. -/
theorem isMinOn_composite_model_objective_univ_iff_isMinOn_effective_domain
    (hf_ne_bot : ∀ y, f y ≠ ⊥) {xStar : E} :
    IsMinOn F Set.univ xStar ↔ IsMinOn F (effective_domain g) xStar := by
  rw [isMinOn_univ_iff, isMinOn_iff]
  constructor
  · intro hxMin y _
    exact hxMin y
  · intro hxMin y
    by_cases hy : y ∈ effective_domain g
    · exact hxMin y hy
    · have hgy_top : g y = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa using hy))
      have hobjective_top : F y = ⊤ := by
        simp [hgy_top, hf_ne_bot y]
      rw [hobjective_top]
      exact le_top

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: send `xStar ∈ effective_domain g` into `interior (effective_domain f)` using the
-- domain-inclusion hypothesis, use smoothness plus the no-`⊥` hypothesis to obtain
-- `is_differentiable_at f xStar`, apply Theorem 10.7 to rewrite vanishing of the gradient
-- mapping as stationarity, then
-- apply Theorem 3.35 and the domain-restriction lemma above to identify stationarity with global
-- optimality of the composite objective.
/-- Corollary 10.8: if `g` is proper, closed, and convex, `effective_domain g ⊆ interior
(effective_domain f)`, `f` never takes the value `-∞`, `f` is `L_f`-smooth on
`interior (effective_domain f)`, and `f` is convex, then for `xStar ∈ effective_domain g`, the
gradient mapping vanishes at `xStar` if and only if `xStar` is a global minimizer of the
composite objective `F(x) = f(x) + g(x)`. -/
theorem gradient_mapping_eq_zero_iff_optimal_composite_model_objective
    (f g : E → EReal) (hf_ne_bot : ∀ y, f y ≠ ⊥)
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (Lf : NNReal)
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    (hf_convex : is_convex_function f) (L : PosReal) {xStar : E}
    (hxStar : xStar ∈ effective_domain g) :
    G[L, f, g] ⟨xStar, hg_effective_domain_subset_interior_f_effective_domain hxStar⟩ = 0 ↔
      IsMinOn (composite_model_objective f g) Set.univ xStar := by
  let xStarInterior :=
    (⟨xStar, hg_effective_domain_subset_interior_f_effective_domain hxStar⟩ :
      interior (effective_domain f))
  have hdiff : is_differentiable_at f xStar :=
    is_differentiable_at_of_mem_interior_effective_domain
      hf_ne_bot
      hf_toReal_smooth_on_interior_effective_domain
      xStarInterior.property
  have hf_effective_domain_nonempty : (effective_domain f).Nonempty := by
    rcases (inferInstance : IsProperExtendedRealFunction g).effective_domain_nonempty with
      ⟨x, hx⟩
    exact ⟨x, interior_subset (hg_effective_domain_subset_interior_f_effective_domain hx)⟩
  letI : IsProperExtendedRealFunction f :=
    { ne_bot := hf_ne_bot
      effective_domain_nonempty := hf_effective_domain_nonempty }
  have hgradient :
      G[L, f, g] xStarInterior = 0 ↔ is_stationary_point f g xStar := by
    have hgradient' :
        G[L, f, g] xStarInterior = 0 ↔ is_stationary_point f g (xStarInterior : E) :=
      gradient_mapping_eq_zero_iff_is_stationary_point L xStarInterior hdiff
    simpa [xStarInterior] using hgradient'
  have hfproper : IsProperExtendedRealFunction f := inferInstance
  have hg_convex : is_convex_function g := ‹Fact (is_convex_function g)›.1
  have hfinite_dom :
      effective_domain g ⊆ interior (finite_domain f) := by
    simpa [finite_domain_eq_effective_domain hf_ne_bot] using
      hg_effective_domain_subset_interior_f_effective_domain
  have hoptimal :
      IsMinOn (composite_model_objective f g) (effective_domain g) xStar ↔
        is_stationary_point f g xStar := by
    simpa [isMinOn_composite_model_objective_iff] using
      (isMinOn_iff_is_stationary_point
        hfproper
        (inferInstance : IsProperExtendedRealFunction g)
        hg_convex
        hfinite_dom
        hxStar
        hdiff
        hf_convex)
  calc
    G[L, f, g] ⟨xStar, hg_effective_domain_subset_interior_f_effective_domain hxStar⟩ = 0 ↔
        is_stationary_point f g xStar := by
          simpa [xStarInterior] using hgradient
    _ ↔ IsMinOn (composite_model_objective f g) (effective_domain g) xStar := hoptimal.symm
    _ ↔ IsMinOn (composite_model_objective f g) Set.univ xStar :=
      (isMinOn_composite_model_objective_univ_iff_isMinOn_effective_domain hf_ne_bot).symm

end
