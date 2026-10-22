/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Corollary_5_3_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BInducedNorm Gradient HessianDualLocalNorm

noncomputable section

universe u

open InnerProductSpace

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-
Lemma 5.3.3 lies in the Chapter 5 self-concordant-barrier / auxiliary-central-path /
analytic-center dual-norm domain.

Sampled owner declarations in this domain:
* `IsCentralPath` in `Definition_5_3_6_1`, the chapter owner for the auxiliary central path;
* `centralPath_stationarity_eq_zero` in `Proposition_5_3_1`, the canonical bridge from
  `IsCentralPath` to the pathwise stationarity equation;
* `IsSelfConcordantBarrierOnWith.dualLocalNorm_le_barrierParameter_add_two_sqrt_mul_of_isMinOn`
  in `Corollary_5_3_4`, the analytic-center comparison theorem for Hessian dual local norms;
* `HessianDualLocalNorm.ofPosDefMem` in `Definition_5_0_20`, the domain-level bridge to the local
  dual norm.

Best owner abstraction:
* source-facing: the dual-local-norm estimate along the auxiliary central path;
* core/canonical: the analytic-center comparison theorem under the barrier owner;
* bridge/view: the central-path stationarity identity and nonnegative scalar homogeneity of the
  induced dual norm.

Primitive data:
* the barrier owner and positive-definite-Hessian owner on `dom`;
* the initial point `y0`, the path `yStar`, and the analytic center `xFStar`;
* the analytic-center witness `IsMinOn F dom (xFStar : E)`;
* the source-facing path hypothesis `IsCentralPath dom (-∇ F (y0 : E)) F yStar`.

Derived API:
* the gradient identity `∇ F (yStar t : E) = (t : ℝ) • ∇ F (y0 : E)`;
* the pointwise dual-local-norm bound at `yStar t`;
* the owner-level homogeneity bridge `dualLocalNorm_smul_nonneg`.

Source/core/bridge triage:
* source-facing: the present lemma on the auxiliary central path owner;
* core/canonical: the analytic-center dual-local-norm comparison theorem;
* bridge/view: the local derivation of the gradient-scaling identity and owner-level scalar
  homogeneity.
-/

-- Proof sketch: Proposition 5.3.1 gives
-- `(t : ℝ) • (-∇ F(y₀)) + ∇ F(y*(t)) = 0` along the auxiliary central path, hence
-- `∇ F (y*(t)) = t • ∇ F(y₀)`. Apply
-- `IsSelfConcordantBarrierOnWith.dualLocalNorm_le_barrierParameter_add_two_sqrt_mul_of_isMinOn`
-- at the point
-- `y*(t)` with analytic center `x_F^*`, then use the positive homogeneity of the Hessian dual
-- norm and the nonnegativity built into `t : Set.Ici (0 : ℝ)` to pull out the factor `t`.
namespace IsSelfConcordantBarrierOnWith

/-- Lemma 5.3.3: along an auxiliary central path `y*(t)` for a bounded
`ν`-self-concordant barrier, the dual local norm of the gradient at time `t ≥ 0` is bounded by
`(ν + 2 √ν)` times the dual local norm of the initial gradient at the analytic center `x_F^*`,
multiplied by `t`. -/
theorem dualLocalNorm_gradient_auxiliaryCentralPath_le_barrierParameter_add_two_sqrt_mul_initial
    {dom : Set E} {ν : NNReal} {F : E → ℝ}
    (hF : IsSelfConcordantBarrierOnWith dom ν F)
    [HasPositiveDefiniteHessianOn dom F]
    (y0 : dom) (yStar : Set.Ici (0 : ℝ) → dom)
    (xFStar : dom) (hxFStar : IsMinOn F dom (xFStar : E))
    (hpath : IsCentralPath dom (-∇ F (y0 : E)) F yStar)
    (t : Set.Ici (0 : ℝ)) :
    HessianDualLocalNorm.ofPosDefMem F (yStar t).2 (toDual ℝ E (∇ F (yStar t : E))) ≤
      (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
          HessianDualLocalNorm.ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E)))) *
        (t : ℝ) := by
  letI : IsSelfConcordantBarrierOnWith dom ν F := hF
  let hstd : IsStandardSelfConcordantOn dom F := inferInstance
  have hdiff : DifferentiableOn ℝ F dom := by
    intro x hx
    exact (hstd.contDiffOn x hx).differentiableWithinAt (by norm_num)
  have hgrad (s : Set.Ici (0 : ℝ)) :
      ∇ F (yStar s : E) = (s : ℝ) • ∇ F (y0 : E) := by
    have hzero :
        (s : ℝ) • (-∇ F (y0 : E)) + ∇ F (yStar s : E) = 0 :=
      centralPath_stationarity_eq_zero
        dom (-∇ F (y0 : E)) F yStar hpath s
        (hstd.isOpen_domain.mem_nhds (yStar s).2)
        ((hdiff (yStar s : E) (yStar s).2).differentiableAt
          (hstd.isOpen_domain.mem_nhds (yStar s).2))
    calc
      ∇ F (yStar s : E) = -((s : ℝ) • (-∇ F (y0 : E))) := by
        simpa using (eq_neg_of_add_eq_zero_left hzero).symm
      _ = (s : ℝ) • ∇ F (y0 : E) := by simp
  have hsmul :
      HessianDualLocalNorm.ofPosDefMem F xFStar.2 (toDual ℝ E ((t : ℝ) • ∇ F (y0 : E))) =
        (t : ℝ) *
          HessianDualLocalNorm.ofPosDefMem F xFStar.2 (toDual ℝ E (∇ F (y0 : E))) := by
    simpa [HessianDualLocalNorm.ofPosDefMem] using
      dualLocalNorm_smul_nonneg F (xFStar : E)
        (HasPositiveDefiniteHessianOn.hessian_isPositive_of_mem xFStar.2)
        (hessian_isInvertible_of_det_ne_zero
          (HasPositiveDefiniteHessianOn.hessian_det_ne_zero_of_mem xFStar.2))
        (toDual ℝ E (∇ F (y0 : E))) t.2
  calc
    HessianDualLocalNorm.ofPosDefMem F (yStar t).2 (toDual ℝ E (∇ F (yStar t : E))) =
        HessianDualLocalNorm.ofPosDefMem F (yStar t).2
          (toDual ℝ E ((t : ℝ) • ∇ F (y0 : E))) := by
      rw [hgrad t]
    _ ≤ ((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
          HessianDualLocalNorm.ofPosDefMem F xFStar.2
            (toDual ℝ E ((t : ℝ) • ∇ F (y0 : E))) :=
      hF.dualLocalNorm_le_barrierParameter_add_two_sqrt_mul_of_isMinOn
        xFStar hxFStar (yStar t) ((t : ℝ) • ∇ F (y0 : E))
    _ = (((ν : ℝ) + 2 * Real.sqrt (ν : ℝ)) *
          HessianDualLocalNorm.ofPosDefMem F xFStar.2
            (toDual ℝ E (∇ F (y0 : E)))) *
          (t : ℝ) := by
      rw [hsmul]
      ring_nf

end IsSelfConcordantBarrierOnWith

end
