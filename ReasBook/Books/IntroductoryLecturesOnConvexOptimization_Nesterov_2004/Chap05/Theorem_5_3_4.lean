/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology
open scoped Gradient HessianLocalNorm

noncomputable section

universe u

/- Theorem 5.3.4 lies in the Chapter 5 self-concordant sublevel-barrier domain.

Sampled owner-style declarations in this domain:
* `sublevelLogBarrier` from `Theorem_5_1_4`, the source-facing owner for barriers
  `x ↦ -log (β - f x)`;
* `sublevelLogBarrier_isSelfConcordantOnWith` and
  `IsSelfConcordantOnWith.sublevelLogBarrier_gradient_inner_sq_le` from `Theorem_5_1_4`, the
  canonical self-
  concordance and local-norm-square owners for the strict sublevel barrier;
* `IsSelfConcordantOnWith.pos_smul` from `Corollary_5_1_3`, the owner-level rescaling theorem for
  self-concordant functions;
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for barrier
  parameter data;
* `_root_.barrier_parameter_bound_iff_gradient_inner_sq_le` from `Proposition_5_3_3`, the
  canonical bridge from the squared Hessian-gradient estimate to the barrier owner inequality.

Source/core/bridge triage:
* source-facing: the scaled logarithmic barrier `x ↦ -ν log (β - f x)` on the strict level set;
* core/canonical: `IsSelfConcordantOnWith` and `IsSelfConcordantBarrierOnWith`;
* bridge/view: the lower-bound estimate `fStar ≤ f x ≤ β`, used only to identify the owner
  constant from Theorem 5.1.4 with the textbook expression.

Primitive data:
* the source-facing owner `sublevelLogBarrier f β`;
* the self-concordance witness `hself : IsSelfConcordantOnWith dom Mf f`;
* the lower bound `h_lower` and the parameter comparison `hν`.

Derived API:
* the strict sublevel domain itself, kept as the direct set-builder owner used in Theorem 5.1.4;
* standard self-concordance of the scaled barrier, derived by combining
  `sublevelLogBarrier_isSelfConcordantOnWith` with `IsSelfConcordantOnWith.pos_smul`;
* the barrier inequality, obtained from the canonical Proposition 5.3.3 bridge together with the
  owner-level local-norm-square estimate from `Theorem_5_1_4`, instead of a second local barrier
  wrapper.

This file therefore keeps the source-facing scaled logarithmic barrier, but removes the duplicate
wheel proof route in favor of the chapter owners already established upstream. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Proof sketch: apply Theorem 5.1.4 to `φ x = -log (β - f x)` to obtain self-concordance of `φ`
-- on the strict sublevel domain. If `ν = 0`, then the lower bound and the parameter inequality
-- force the strict sublevel domain to be empty, so the barrier statement is vacuous. If `ν > 0`,
-- pick a point in the strict sublevel domain to deduce `β - fStar > 0`, rewrite the owner
-- constant from Theorem 5.1.4 without `Real.toNNReal`, rescale by `ν`, and use Corollary 5.1.3
-- to make the self-concordance constant standard. Finally, Proposition 5.3.3 upgrades the
-- Hessian-gradient inequality from Theorem 5.1.4 to the barrier parameter bound with parameter
-- `ν`.
/-- Theorem 5.3.4: if `f` is self-concordant on `dom` with constant `M_f` and if `f x ≥ f^*` on
`dom`, then for every `ν ≥ 1 + M_f^2 (β - f^*)` the scaled logarithmic barrier
`x ↦ -ν log (β - f x)` is a `ν`-self-concordant barrier on the strict level-set domain
`{x ∈ dom | f x < β}`. -/
theorem sublevelLogBarrier_smul_isSelfConcordantBarrierOnWith
    {dom : Set E} {Mf ν : NNReal} {f : E → ℝ} {β fStar : ℝ}
    (hself : IsSelfConcordantOnWith dom Mf f)
    (h_lower : ∀ ⦃x : E⦄, x ∈ dom → fStar ≤ f x)
    (hν : 1 + (Mf : ℝ) ^ (2 : ℕ) * (β - fStar) ≤ (ν : ℝ)) :
    IsSelfConcordantBarrierOnWith
      {x : E | x ∈ dom ∧ f x < β}
      ν
      ((ν : ℝ) • sublevelLogBarrier f β) := by
  let strictDom : Set E := {x : E | x ∈ dom ∧ f x < β}
  let barrier := sublevelLogBarrier f β
  change IsSelfConcordantBarrierOnWith strictDom ν ((ν : ℝ) • barrier)
  let c : NNReal := NNReal.sqrt (1 + Mf ^ (2 : ℕ) * Real.toNNReal (β - fStar))
  letI : IsSelfConcordantOnWith dom Mf f := hself
  have hsub :
      IsSelfConcordantOnWith strictDom c barrier := by
    simpa [strictDom, barrier, c] using
      sublevelLogBarrier_isSelfConcordantOnWith hself β fStar h_lower
  have hbarrier_bound {x : E} (hx : x ∈ strictDom) (u : E) :
      2 * inner ℝ (∇ (((ν : ℝ) • barrier)) x) u -
          inner ℝ u (hessian (((ν : ℝ) • barrier)) x u) ≤ (ν : ℝ) := by
    have hx_dom : x ∈ dom := hx.1
    have hx_strict : x ∈ strictDom := hx
    have hsub_pos :
        (hessian barrier x).IsPositive :=
      hsub.hessian_isPositive hx_strict
    have hbarrier_one :
        ∀ v : E,
          2 * inner ℝ (∇ barrier x) v -
              inner ℝ v (hessian barrier x v) ≤ ((1 : NNReal) : ℝ) := by
      refine (barrier_parameter_bound_iff_gradient_inner_sq_le hsub_pos).2 ?_
      intro v
      simpa [barrier] using
        (hself.sublevelLogBarrier_gradient_inner_sq_le β hx_dom hx.2 :
          (inner ℝ (∇ barrier x) v) ^ (2 : ℕ) ≤ ‖v‖[barrier; x] ^ (2 : ℕ))
    have hgrad_smul :
        ∇ ((ν : ℝ) • barrier) =
          (ν : ℝ) • ∇ barrier := by
      funext y
      unfold gradient
      rw [fderiv_const_smul_field]
      exact
        (InnerProductSpace.toDual ℝ E).symm.map_smul (ν : ℝ)
          (fderiv ℝ barrier y)
    have hhess_smul :
        hessian ((ν : ℝ) • barrier) =
          (ν : ℝ) • hessian barrier := by
      funext y
      unfold hessian
      rw [hgrad_smul, fderiv_const_smul_field]
    rw [hgrad_smul, hhess_smul]
    simp only [Pi.smul_apply, ContinuousLinearMap.smul_apply, inner_smul_left, inner_smul_right]
    have hu : 2 * inner ℝ (∇ barrier x) u - inner ℝ u (hessian barrier x u) ≤ (1 : ℝ) := by
      simpa using hbarrier_one u
    calc
      2 * ((ν : ℝ) * inner ℝ (∇ barrier x) u) -
          (ν : ℝ) * inner ℝ u (hessian barrier x u)
          =
            (ν : ℝ) *
              (2 * inner ℝ (∇ barrier x) u - inner ℝ u (hessian barrier x u)) := by
            ring
      _ ≤ (ν : ℝ) * 1 := by
        gcongr
      _ = (ν : ℝ) := by ring
  have hstd :
      IsStandardSelfConcordantOn strictDom ((ν : ℝ) • barrier) := by
    by_cases hstrict_nonempty : strictDom.Nonempty
    · rcases hstrict_nonempty with ⟨x₀, hx₀⟩
      have hβfStar_pos : 0 < β - fStar := by
        nlinarith [h_lower hx₀.1, hx₀.2]
      have hβfStar_nonneg : 0 ≤ β - fStar := le_of_lt hβfStar_pos
      have hMf_term_nonneg : 0 ≤ (Mf : ℝ) ^ (2 : ℕ) * (β - fStar) := by
        positivity
      have hν_pos_real : (0 : ℝ) < (ν : ℝ) := by
        nlinarith [hν, hMf_term_nonneg]
      have hν_pos : 0 < ν := by
        exact_mod_cast hν_pos_real
      have hν_nnreal : 1 + Mf ^ (2 : ℕ) * Real.toNNReal (β - fStar) ≤ ν := by
        rw [Real.toNNReal_of_nonneg hβfStar_nonneg]
        exact_mod_cast hν
      let νu : NNRealˣ := Units.mk0 ν hν_pos.ne'
      letI : IsSelfConcordantOnWith strictDom c barrier := hsub
      have hscaled :
          IsSelfConcordantOnWith strictDom (c / NNReal.sqrt ν)
            ((ν : ℝ) • barrier) := by
        simpa [barrier, c] using
          IsSelfConcordantOnWith.pos_smul hsub νu
      have hscale_le : c / NNReal.sqrt ν ≤ 1 := by
        have hsqrt_le : c ≤ NNReal.sqrt ν := by
          dsimp [c]
          exact (NNReal.sqrt_le_sqrt).2 hν_nnreal
        exact (div_le_one (NNReal.sqrt_pos.2 hν_pos)).2 hsqrt_le
      simpa using hscaled.of_le hscale_le
    · have hstrict_empty : strictDom = ∅ := by
        exact Set.not_nonempty_iff_eq_empty.mp hstrict_nonempty
      refine
        { isOpen_domain := by simp [hstrict_empty]
          contDiffOn := by simp [hstrict_empty]
          convexOn := by
            refine ⟨by simpa [hstrict_empty] using (convex_empty : Convex ℝ (∅ : Set E)), ?_⟩
            intro x hx
            exact (hstrict_empty ▸ hx).elim
          third_deriv_bound := ?_ }
      intro x hx u
      exact (hstrict_empty ▸ hx).elim
  refine
    { toIsStandardSelfConcordantOn := hstd
      barrier_parameter_bound := ?_ }
  intro x hx u
  exact hbarrier_bound hx u
