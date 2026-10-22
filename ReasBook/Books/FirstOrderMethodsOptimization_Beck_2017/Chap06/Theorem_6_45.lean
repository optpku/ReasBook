/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_2
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_7
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_10
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Theorem_4_15
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_12
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_30
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_39

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open InnerProductSpace (toDualMap)
open scoped Pointwise

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Theorem 6.45 is `source-facing` in the proximal-operator chapter: it is also the reusable
owner-level Moreau decomposition in the local API, with Theorem 6.44 as the exact `λ = 1`
specialization. Domain sampling in the chapter gives the owner chain:

- `prox[...]` from Definition 6.1 as the `core/canonical` proximal owner,
- `conjugate_function`/`f∗` from Definition 4.1 as the `core/canonical` Fenchel owner and its
  primal-space surface,
- `prox_eq_singleton_of_proper_closed_convex` from Theorem 6.3 as the chapter's existence/uniqueness
  owner for proximal points on the ambient space,
- `conjugate_function_primal_pos_real_mul` from Proposition 4.7 and
  `proximal_mapping_smul_precompose_inv_smul` from Theorem 6.12 as the two scaling bridges.

Primitive data: `f`, the proper/closed/convex hypotheses, the positive scale `lam : PosReal`,
and `x`.
Derived API: the scaled conjugate rewrite and the proximal transport needed to express the textbook
`λ`-parameter formula directly on the owner surface.

The textbook writes a single-valued identity, so the canonical chapter-level rendering is the
singleton identity for the pointwise sum set. -/
recall conjugate_function_primal
recall fenchel_inequality
recall conjugate_function_primal_pos_real_mul
recall pairing_eq_add_conjugate_iff_mem_subdifferential
recall isProperExtendedRealFunction_conjugate_function
recall proximal_mapping_smul_precompose_inv_smul
recall scaled_function_proper_closed_convex_of_pos
recall prox_eq_singleton_of_proper_closed_convex
recall prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
recall prox_singleton_implies_effective_domain_and_inner_support
recall prox_eq_singleton_of_effective_domain_and_inner_support

/-- Helper for Theorem 6.45: the primal-space Fenchel conjugate of a proper convex function is
again proper. -/
lemma conjugate_function_primal_proper_of_proper_convex
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_convex : is_convex_function f) :
    IsProperExtendedRealFunction (f∗) := by
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_locallyCompactSpace ℝ
  let hconj_proper := isProperExtendedRealFunction_conjugate_function f hf_proper hf_convex
  refine ⟨?_, ?_⟩
  · -- The primal conjugate never takes the value `⊥` because the dual conjugate does not.
    intro x
    simpa [conjugate_function_primal_apply] using hconj_proper.ne_bot (toDualMap ℝ E x)
  · -- A finite dual point pulls back along the Riesz equivalence to a finite primal point.
    rcases hconj_proper.effective_domain_nonempty with ⟨y, hy⟩
    let y' : StrongDual ℝ E := LinearMap.toContinuousLinearMap y
    rcases (InnerProductSpace.toDual ℝ E).surjective y' with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    change conjugate_function f (y' : Module.Dual ℝ E) < ⊤ at hy
    simpa [conjugate_function_primal_apply] using hx ▸ hy

/-- Helper for Theorem 6.45: if `u` is the proximal point of the scaled function `λ f` at `x`,
then the proximal point of its conjugate is the residual `x - u`. -/
lemma prox_scaled_function_conjugate_eq_singleton_residual
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (lam : PosReal) (x u : E) (hprox : prox[((lam : EReal) • f)] x = {u}) :
    prox[(((lam : EReal) • f)∗)] x = {x - u} := by
  let g : E → EReal := ((lam : EReal) • f)
  have hprox_g : prox[g] x = {u} := by
    simpa [g] using hprox
  rcases scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam with
    ⟨hg_proper, _, hg_convex⟩
  have hu_eff :
      u ∈ effective_domain g :=
    (prox_singleton_implies_effective_domain_and_inner_support g hg_proper hg_convex x u hprox_g).1
  have hu_val : g u = (((g u).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hg_proper.ne_bot u)).symm
  have hsub :
      toDualMap ℝ E (x - u) ∈ strongDualSubdifferential g u := by
    -- The primal proximal singleton gives the canonical residual subgradient.
    exact
      (prox_eq_singleton_iff_toDualMap_sub_mem_strongDualSubdifferential
        g hg_proper hg_convex x u).mp hprox_g
  have hsub' :
      (toDualMap ℝ E (x - u) : Module.Dual ℝ E) ∈ subdifferential g u := by
    simpa [mem_strongDualSubdifferential] using hsub
  have hfenchel_eq :
      (toDualMap ℝ E (x - u) u : EReal) = g u + conjugate_function g (toDualMap ℝ E (x - u)) := by
    -- The residual subgradient is exactly the Fenchel--Young equality case for `g`.
    exact
      (pairing_eq_add_conjugate_iff_mem_subdifferential
        g hg_proper.ne_bot u (toDualMap ℝ E (x - u))).2 hsub'
  have hdual_point_eq :
      (g∗) (x - u) = (((inner ℝ (x - u) u - (g u).toReal : ℝ)) : EReal) := by
    -- Rewrite the equality case into an explicit finite formula for the conjugate value.
    rw [conjugate_function_primal_apply]
    rw [hu_val] at hfenchel_eq
    have hsum :
        conjugate_function g (toDualMap ℝ E (x - u)) + (((g u).toReal : ℝ) : EReal) =
          (toDualMap ℝ E (x - u) u : EReal) := by
      rw [add_comm]
      exact hfenchel_eq.symm
    have htmp :
        conjugate_function g (toDualMap ℝ E (x - u)) =
          (toDualMap ℝ E (x - u) u : EReal) - (((g u).toReal : ℝ) : EReal) := by
      calc
        conjugate_function g (toDualMap ℝ E (x - u))
            = conjugate_function g (toDualMap ℝ E (x - u)) +
                (((g u).toReal : ℝ) : EReal) - (((g u).toReal : ℝ) : EReal) := by
                  simpa using
                    (EReal.add_sub_cancel_right
                      (a := conjugate_function g (toDualMap ℝ E (x - u)))
                      (b := (g u).toReal)).symm
        _ = (toDualMap ℝ E (x - u) u : EReal) - (((g u).toReal : ℝ) : EReal) := by
              rw [hsum]
    have htmp' :
        conjugate_function g (toDualMap ℝ E (x - u)) =
          ((inner ℝ (x - u) u : ℝ) : EReal) - (((g u).toReal : ℝ) : EReal) := by
      simpa only [InnerProductSpace.toDualMap_apply_apply] using htmp
    simpa only [EReal.coe_sub] using htmp'
  have hx_sub_u_eff : x - u ∈ effective_domain (g∗) := by
    -- The equality above shows the conjugate value at `x - u` is finite.
    rw [mem_effective_domain, hdual_point_eq]
    exact EReal.coe_lt_top _
  have hg_dual_proper : IsProperExtendedRealFunction (g∗) :=
    conjugate_function_primal_proper_of_proper_convex g hg_proper hg_convex
  have hx_sub_u_val : (g∗) (x - u) = ((((g∗) (x - u)).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hx_sub_u_eff).ne
        (hg_dual_proper.ne_bot (x - u))).symm
  have hsupport_dual :
      ∀ z ∈ effective_domain (g∗),
        ((inner ℝ (x - (x - u)) (z - (x - u)) : ℝ) : EReal) ≤ (g∗) z - (g∗) (x - u) := by
    intro z hz_eff
    have hz_val : (g∗) z = ((((g∗) z).toReal : ℝ) : EReal) := by
      exact
        (EReal.coe_toReal (mem_effective_domain.mp hz_eff).ne
          (hg_dual_proper.ne_bot z)).symm
    have hfenchel_z :
        ((inner ℝ z u : ℝ) : EReal) ≤ g u + (g∗) z := by
      -- Fenchel inequality bounds every dual value above by the primal-conjugate sum.
      simpa [ge_iff_le, add_comm, conjugate_function_primal_apply,
        InnerProductSpace.toDualMap_apply_apply] using
        (fenchel_inequality g u (toDualMap ℝ E z) hg_proper)
    have hfenchel_z_real :
        inner ℝ z u ≤ (g u).toReal + ((g∗) z).toReal := by
      rw [hu_val, hz_val, ← EReal.coe_add] at hfenchel_z
      exact EReal.coe_le_coe_iff.mp hfenchel_z
    have hx_sub_u_real :
        ((g∗) (x - u)).toReal = inner ℝ (x - u) u - (g u).toReal := by
      exact congrArg EReal.toReal hdual_point_eq
    have hinner_sub :
        inner ℝ u (z - (x - u)) = inner ℝ z u - inner ℝ (x - u) u := by
      rw [inner_sub_right, real_inner_comm u z, real_inner_comm u (x - u)]
    have hsupport_real :
        inner ℝ u (z - (x - u)) ≤ ((g∗) z).toReal - ((g∗) (x - u)).toReal := by
      nlinarith [hfenchel_z_real, hx_sub_u_real, hinner_sub]
    have hsupport_realE :
        ((inner ℝ u (z - (x - u)) : ℝ) : EReal) ≤
          (((((g∗) z).toReal - ((g∗) (x - u)).toReal : ℝ)) : EReal) :=
      EReal.coe_le_coe hsupport_real
    rw [hz_val, hx_sub_u_val]
    simpa [EReal.coe_sub, sub_sub_cancel] using hsupport_realE
  -- The Chapter 6 support-inequality criterion now recovers the dual proximal singleton.
  simpa [g] using
    prox_eq_singleton_of_effective_domain_and_inner_support
      (g∗) hg_dual_proper x (x - u) hx_sub_u_eff hsupport_dual

-- Proof sketch: argue directly on the scaled problem `λ f`. Rewrite `(λ f)^*` using the Chapter 4
-- positive-scaling conjugacy formula and transport its proximal mapping with Theorem 6.12, which
-- turns `prox[(λ f)^*] x` into the set `λ • prox[f^* / λ] (λ⁻¹ • x)`. The same proximal/Fenchel
-- optimality argument as in the unscaled case then yields the singleton identity.
/-- Theorem 6.45: extended Moreau decomposition. On a proper real inner product space, for a
proper closed convex function `f` and a positive scalar `λ`, encoded by `lam : PosReal`, the
pointwise sum of the proximal set of `λ f` at `x` and `λ` times the
proximal set of `f^* / λ` at `x / λ` is the singleton `{x}`. This is the set-valued owner-level
form of `prox_{λ f}(x) + λ prox_{f^* / λ}(x / λ) = x`. -/
theorem prox_scaled_conjugate_sum_eq_singleton
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (lam : PosReal) (x : E) :
    prox[((lam : EReal) • f)] x +
      (lam : ℝ) • prox[fun y ↦ (f∗) y / (lam : EReal)] ((lam : ℝ)⁻¹ • x) = {x} := by
  rcases scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam with
    ⟨hscaled_proper, hscaled_closed, hscaled_convex⟩
  rcases prox_eq_singleton_of_proper_closed_convex (((lam : EReal) • f))
      hscaled_proper hscaled_closed hscaled_convex x with
    ⟨u, hu⟩
  have hdual_singleton :
      prox[(((lam : EReal) • f)∗)] x = {x - u} :=
    prox_scaled_function_conjugate_eq_singleton_residual
      f hf_proper hf_closed hf_convex lam x u hu
  have hdual_transport :
      (lam : ℝ) • prox[fun y ↦ (f∗) y / (lam : EReal)] ((lam : ℝ)⁻¹ • x) = {x - u} := by
    -- Rewrite the dual scaled objective into the Chapter 6 transport form.
    calc
      (lam : ℝ) • prox[fun y ↦ (f∗) y / (lam : EReal)] ((lam : ℝ)⁻¹ • x)
          = prox[(((lam : EReal) • f)∗)] x := by
            symm
            rw [conjugate_function_primal_pos_real_mul f (lam : ℝ) lam.2]
            simpa [smul_eq_mul] using
              proximal_mapping_smul_precompose_inv_smul (g := f∗) (lam := (lam : ℝ))
                (ne_of_gt lam.2) x
      _ = {x - u} := hdual_singleton
  -- Once both proximal sets are singletons, the set sum is the singleton `{x}`.
  calc
    prox[((lam : EReal) • f)] x +
        (lam : ℝ) • prox[fun y ↦ (f∗) y / (lam : EReal)] ((lam : ℝ)⁻¹ • x)
        = {u} + {x - u} := by rw [hu, hdual_transport]
    _ = {x} := by
      ext z
      simp [sub_eq_add_neg, add_left_comm]

end
