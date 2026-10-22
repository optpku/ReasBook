/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {g ω : E → EReal} {σ : ℝ}

/- Domain sampling for Theorem 9.24:
- `source-facing`: the textbook Mirror-C auxiliary problem with linear perturbation `x ↦ a x`;
- `core/canonical`: Chapter 9's owner theorem `existsUnique_composite_minimizer_mem_domains`
  applied to `ψ x = ((a x : ℝ) : EReal) + g x`;
- `bridge/view`: no separate owner is needed here, because the linear perturbation is primitive
  data and the displayed objective is just the direct specialization of the composite owner.

The primitive data are therefore exactly `a`, `g`, and the Bregman-potential hypothesis on `ω`
over `effective_domain g`, together with the intrinsic-interior qualification needed by
`Lemma_9_7` to conclude membership in `subdifferential_domain ω`. A standalone local objective
wrapper would duplicate the chapter owner surface without adding mathematical content, so the
public theorem below keeps the objective in its canonical specialized form. -/

/-- Helper for Theorem 9.24: adding the finite linear perturbation `x ↦ ((a x : ℝ) : EReal)`
does not change the effective domain of `g`. -/
private theorem dualLinearPerturbation_effectiveDomain_eq
    (a : StrongDual ℝ E) (g : E → EReal) :
    effective_domain (fun x ↦ ((a x : ℝ) : EReal) + g x) = effective_domain g := by
  ext x
  constructor
  · -- Recover `x ∈ dom(g)` by ruling out `g x = ⊤` inside the finite sum.
    intro hx
    rw [mem_effective_domain] at hx ⊢
    by_contra hgx_top
    have hgx_eq_top : g x = ⊤ := by
      exact top_unique (le_of_not_gt hgx_top)
    have hsum_eq_top : ((a x : ℝ) : EReal) + g x = ⊤ := by
      simp [hgx_eq_top, EReal.add_top_of_ne_bot, EReal.coe_ne_bot]
    exact (ne_of_lt hx) hsum_eq_top
  · -- The linear perturbation is finite everywhere, so finiteness of `g x` transfers directly.
    intro hx
    rw [mem_effective_domain] at hx ⊢
    exact EReal.add_lt_top (EReal.coe_ne_top (a x)) hx.ne

/-- Helper for Theorem 9.24: the finite linear perturbation of a proper extended-real-valued
function is still proper. -/
private theorem dualLinearPerturbation_isProper
    (a : StrongDual ℝ E) (hg_proper : IsProperExtendedRealFunction g) :
    IsProperExtendedRealFunction (fun x ↦ ((a x : ℝ) : EReal) + g x) := by
  constructor
  · -- Pointwise `-∞` is impossible because both summands are never `-∞`.
    intro x
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot (a x), hg_proper.ne_bot x⟩
  · -- Nonempty effective domain is preserved by the domain-identification helper above.
    rcases hg_proper.effective_domain_nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    simpa [dualLinearPerturbation_effectiveDomain_eq (a := a) (g := g)] using hx

/-- Helper for Theorem 9.24: the finite linear perturbation of a convex function is convex. -/
private theorem dualLinearPerturbation_isConvexFunction
    (a : StrongDual ℝ E) (hg_convex : is_convex_function g)
    (hg_proper : IsProperExtendedRealFunction g) :
    is_convex_function (fun x ↦ ((a x : ℝ) : EReal) + g x) := by
  -- A continuous linear functional is affine, hence convex on all of `E`.
  have hlinearConvex : ConvexOn ℝ Set.univ (fun x : E ↦ a x) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ α β hα hβ hαβ
    refine le_of_eq ?_
    simp [smul_eq_mul, map_add]
  have hlinearConvexEReal :
      is_convex_function (fun x ↦ ((a x : ℝ) : EReal)) :=
    Function.toEReal_isConvexFunction hlinearConvex
  -- Combine the convex finite linear term with the convex penalty `g`.
  simpa [Pi.add_apply] using
    is_convex_function_pointwise_add hlinearConvexEReal hg_convex
      (fun x ↦ EReal.coe_ne_bot (a x)) hg_proper.ne_bot

/-- Helper for Theorem 9.24: the finite linear perturbation of a lower semicontinuous function
remains lower semicontinuous. -/
private theorem dualLinearPerturbation_lowerSemicontinuous
    (a : StrongDual ℝ E) (hg_closed : LowerSemicontinuous g) :
    LowerSemicontinuous (fun x ↦ ((a x : ℝ) : EReal) + g x) := by
  -- The lifted linear term is continuous, hence lower semicontinuous.
  have hlinear_closed :
      LowerSemicontinuous (fun x ↦ ((a x : ℝ) : EReal)) :=
    Function.toEReal_lowerSemicontinuous_of_continuous a.continuous
  have hsum_closed :
      LowerSemicontinuous ((fun x ↦ ((a x : ℝ) : EReal)) + g) := by
    -- Addition is continuous at every point because the linear term is always finite.
    refine hlinear_closed.add' hg_closed ?_
    intro x
    exact EReal.continuousAt_add (.inl (EReal.coe_ne_top (a x))) (.inl (EReal.coe_ne_bot (a x)))
  simpa [Pi.add_apply] using hsum_closed

variable [FiniteDimensional ℝ E]

-- Proof sketch: specialize the domain-membership companion from Lemma 9.7 to the perturbed
-- objective `x ↦ ((a x : ℝ) : EReal) + g x`, using that a continuous linear functional is finite
-- everywhere and preserves the effective domain and convexity hypotheses of `g`.
/-- Companion to Theorem 9.24: any global minimizer of the Mirror-C auxiliary objective
`x ↦ ⟨a, x⟩ + g(x) + ω(x)` lies in `dom(g) ∩ dom(∂ ω)`. -/
theorem mirror_c_problem_minimizer_mem_domains
    (a : StrongDual ℝ E) (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hqual :
      (intrinsicInterior ℝ (effective_domain g) ∩
        intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    (hg_proper : IsProperExtendedRealFunction g) (hg_convex : is_convex_function g)
    {xStar : E}
    (hxStar : IsMinOn (fun x ↦ ((a x : ℝ) : EReal) + g x + ω x) Set.univ xStar) :
    xStar ∈ effective_domain g ∩ subdifferential_domain ω := by
  let ψ : E → EReal := fun x ↦ ((a x : ℝ) : EReal) + g x
  have hψ_dom : effective_domain ψ = effective_domain g := by
    simpa [ψ] using dualLinearPerturbation_effectiveDomain_eq (a := a) (g := g)
  have hωψ : IsBregmanPotentialOn ω (effective_domain ψ) σ := by
    -- Transport the Bregman-potential hypothesis across the unchanged effective domain.
    simpa [hψ_dom] using hω
  have hψ_proper : IsProperExtendedRealFunction ψ := by
    -- Properness is stable under finite linear perturbations.
    simpa [ψ] using dualLinearPerturbation_isProper (g := g) a hg_proper
  have hψ_convex : is_convex_function ψ := by
    -- Convexity is the pointwise sum of the convex linear term and the convex penalty.
    simpa [ψ] using dualLinearPerturbation_isConvexFunction (g := g) a hg_convex hg_proper
  -- Apply Lemma 9.7 in its canonical owner form and rewrite back to `dom(g)`.
  simpa [ψ, Pi.add_apply, hψ_dom] using
    composite_minimizer_mem_domains hωψ hψ_proper hψ_convex
      (by simpa [hψ_dom] using hqual) hxStar

-- Proof sketch: apply Lemma 9.7 to the perturbed function
-- `ψ(x) = ((a x : ℝ) : EReal) + g(x)`. A continuous linear functional is finite, proper, closed,
-- and convex, so adding it to `g` preserves the hypotheses required by Lemma 9.7 and leaves the
-- effective domain equal to `effective_domain g`.
/-- Theorem 9.24: if `g` is proper, closed, and convex, and `ω` is a Bregman potential on
`dom(g)`, and `intrinsicInterior ℝ (dom(g)) ∩ intrinsicInterior ℝ (dom(ω))` is nonempty, then the
Mirror-C auxiliary problem
`min_x {⟨a, x⟩ + g(x) + ω(x)}` has a unique minimizer in
`dom(g) ∩ dom(∂ ω)`. -/
theorem existsUnique_mirror_c_problem_minimizer_mem_domains
    (a : StrongDual ℝ E) (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hqual :
      (intrinsicInterior ℝ (effective_domain g) ∩
        intrinsicInterior ℝ (effective_domain ω)).Nonempty)
    (hg_proper : IsProperExtendedRealFunction g) (hg_closed : LowerSemicontinuous g)
    (hg_convex : is_convex_function g) :
    ∃! xStar : E,
      IsMinOn (fun x ↦ ((a x : ℝ) : EReal) + g x + ω x) Set.univ xStar ∧
        xStar ∈ effective_domain g ∩ subdifferential_domain ω := by
  let ψ : E → EReal := fun x ↦ ((a x : ℝ) : EReal) + g x
  have hψ_dom : effective_domain ψ = effective_domain g := by
    simpa [ψ] using dualLinearPerturbation_effectiveDomain_eq (a := a) (g := g)
  have hωψ : IsBregmanPotentialOn ω (effective_domain ψ) σ := by
    -- The Bregman-potential owner hypothesis is unchanged after rewriting the domain.
    simpa [hψ_dom] using hω
  have hψ_proper : IsProperExtendedRealFunction ψ := by
    -- Properness again comes from the finite linear perturbation helper.
    simpa [ψ] using dualLinearPerturbation_isProper (g := g) a hg_proper
  have hψ_closed : LowerSemicontinuous ψ := by
    -- Lower semicontinuity is preserved because the perturbation is continuous.
    simpa [ψ] using dualLinearPerturbation_lowerSemicontinuous (g := g) a hg_closed
  have hψ_convex : is_convex_function ψ := by
    -- Convexity is preserved by the same finite linear perturbation.
    simpa [ψ] using dualLinearPerturbation_isConvexFunction (g := g) a hg_convex hg_proper
  rcases existsUnique_composite_minimizer_mem_domains hωψ hψ_proper hψ_closed hψ_convex
      (by simpa [hψ_dom] using hqual) with
    ⟨xStar, hxStar, huniq⟩
  refine ⟨xStar, ?_, ?_⟩
  · -- Rewrite the canonical owner conclusion back to the source-facing objective.
    simpa [ψ, Pi.add_apply, hψ_dom] using hxStar
  · intro y hy
    -- Uniqueness depends only on the canonical owner problem, so the same witness identifies `y`.
    apply huniq
    simpa [ψ, Pi.add_apply, hψ_dom] using hy
