/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_19

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped SupportFunction
open scoped SeminormDualNorm
open scoped WithTopConvexAnalysis

universe u

/- Proposition 3.20 lies in the chapter's dual-norm / subdifferential domain.

Sampled owner-style declarations:
- `supportFunction` and `supportFunction_apply` from `Definition_3_9`, the chapter owner for
  support functions;
- `Seminorm.dualNorm` and `Seminorm.dualNorm_apply` from `Definition_3_20`, the chapter recall of
  the dual-norm owner;
- `IsSubgradientAt`, `subdifferential`, and `mem_subdifferential_iff` from `Definition_3_1_5`, the
  chapter owners for extended-valued subgradients;
- `Seminorm.closedConvexFunction` from `Proposition_3_6` and
  `isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous` from
  `Proposition_3_19`, the upstream Chapter 3 owners that make the support-function statement a
  consequence of convexity plus positive homogeneity rather than a standalone duplicate duality
  theorem.

Best owner abstraction:
- `ξ[Q]` for the support function of a set `Q`;
- `Seminorm.dualNorm p` for the dual norm;
- `∂ f(x)` for the subdifferential statement.

Primitive data:
- a seminorm `p : Seminorm ℝ E`;
- the ambient real inner-product-space structure on `E`;
- the separation hypothesis `[p.IsNorm]` only for the dual-norm formulas;
- finite-dimensionality only for the source-facing dual-ball reformulations and for the
  finite-dimensional owner theorem identifying `p` with the support function of `∂p(0)`.

Derived API:
- the intrinsic origin-subdifferential formula for the lifted real-valued seminorm, derived
  directly from `mem_subdifferential_iff`;
- the owner-level support-function formula for `p` against its origin subdifferential;
- the source-facing dual-unit-ball reformulations of those two intrinsic statements.

Source/core/bridge triage:
- source-facing: the dual-unit-ball support-function and origin-subdifferential formulas;
- core/canonical: `subdifferential` together with the owner-level support-function statement on
  `∂ (fun y ↦ (p y : WithTop ℝ))(0)`;
- bridge/view: the intrinsic inequality description `{g | ∀ y, inner ℝ g y ≤ p y}` and its
  finite-dimensional dual-ball reformulation `{g | ‖g‖[p,*] ≤ 1}`.

This refinement removes the duplicate local effective-domain and subgradient API and rewrites the
proposition directly in the chapter owner vocabulary. The support-function part now passes first
through the canonical Chapter 3 owner `∂ (fun y ↦ (p y : WithTop ℝ))(0)`, so the finite-dimensional
source-facing dual-ball statement is only a bridge theorem rather than a second root description.
For the subdifferential part, the intrinsic inequality characterization `∀ y, ⟪g, y⟫ ≤ p y` is
the mathematically sound bridge on an arbitrary real inner-product space, while the closed dual
unit ball remains the finite-dimensional source-facing reformulation that additionally uses
`[p.IsNorm]`. -/

open Seminorm

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (p : Seminorm ℝ E)

/-- Helper for Proposition 3.20: a seminorm is positively homogeneous of degree `1` on all of
the ambient space. -/
lemma seminorm_isPositivelyHomogeneousOn_univ :
    IsPositivelyHomogeneousOn 1 Set.univ p := by
  refine ⟨?_, ?_⟩
  · intro y hy τ
    simp
  · intro y hy τ
    -- Rewrite the seminorm scaling law into the chapter's positive-homogeneity interface.
    simpa [Real.rpow_one, NNReal.smul_def, smul_eq_mul, Real.norm_of_nonneg τ.2] using
      (map_smul_eq_mul p (τ : ℝ) y)

/-- Proposition 3.20 (2), intrinsic owner form: the subdifferential of the seminorm at the
origin consists exactly of the vectors whose pairing with every `y` is bounded by `p y`. -/
-- Proof sketch: unfold `subdifferential` at `0` via `mem_subdifferential_iff`. Since the lifted
-- seminorm takes finite values everywhere and `p 0 = 0`, the supporting-nesterovHyperplane inequality is
-- exactly `⟪g, y⟫ ≤ p y` for every `y`.
theorem subdifferential_seminorm_at_zero_eq_inner_le :
    ∂ (fun y : E ↦ (p y : WithTop ℝ))(0) = {g | ∀ y : E, inner ℝ g y ≤ p y} := by
  ext g
  rw [mem_subdifferential_coe_real_iff]
  -- At the origin, the owner subgradient inequality is exactly the textbook pairing bound.
  constructor
  · intro hg y
    have hy := hg y
    simpa [map_zero p] using hy
  · intro hg y
    have hy := hg y
    simpa [map_zero p] using hy

/-- Proposition 3.20 (1), core/canonical owner form: on a finite-dimensional real inner-product
space, a seminorm is the support function of its origin subdifferential. -/
-- Proof sketch: `Seminorm.closedConvexFunction` supplies the convex owner data for the lifted
-- seminorm, and positive homogeneity comes directly from `Seminorm.map_smul_eq_mul`. Apply
-- `isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous` to the real-valued
-- seminorm `p` and rewrite the resulting `IsGreatest` statement as a support-function equality.
theorem supportFunction_subdifferential_seminorm_at_zero_eq
    [FiniteDimensional ℝ E] (x : E) :
    ξ[∂ (fun y : E ↦ (p y : WithTop ℝ))(0)] x = (p x : EReal) := by
  have hmax_real :
      IsGreatest ((fun g : E ↦ inner ℝ g x) '' ∂ (fun y : E ↦ (p y : WithTop ℝ))(0)) (p x) :=
    isGreatest_pairing_image_subdifferential_zero_of_convex_posHomogeneous
      (f := p) (hf_convex := p.convexOn)
      (hf_hom := seminorm_isPositivelyHomogeneousOn_univ (p := p)) x
  have hmax_ereal :
      IsGreatest
        ((fun g : E ↦ (inner ℝ g x : EReal)) '' ∂ (fun y : E ↦ (p y : WithTop ℝ))(0))
        (p x : EReal) := by
    -- Convert the real maximizer statement into the `EReal` support-function codomain.
    simpa only [Set.image_image] using
      (EReal.coe_strictMono.map_isGreatest).2 hmax_real
  -- The support function is precisely the supremum of the same pairing image.
  rw [supportFunction_apply]
  exact hmax_ereal.csSup_eq

/-- Proposition 3.20 (2), source-facing finite-dimensional form: the subdifferential of the
seminorm at the origin is exactly the closed unit ball of the dual norm. -/
-- Proof sketch: combine `subdifferential_seminorm_at_zero_eq_inner_le` with the finite-dimensional
-- equivalence between the intrinsic inequalities `∀ y, ⟪g, y⟫ ≤ p y` and the dual-ball condition
-- `‖g‖[p,*] ≤ 1`.
theorem subdifferential_seminorm_at_zero_eq_dualNorm_closedUnitBall
    [p.IsNorm] [FiniteDimensional ℝ E] :
    ∂ (fun y : E ↦ (p y : WithTop ℝ))(0) = {g | ‖g‖[p,*] ≤ 1} := by
  ext g
  rw [subdifferential_seminorm_at_zero_eq_inner_le (p := p)]
  change (∀ y : E, inner ℝ g y ≤ p y) ↔ ‖g‖[p,*] ≤ 1
  -- Rewrite the intrinsic support inequalities through the dual-norm owner formula.
  constructor
  · intro hg
    rw [Seminorm.dualNorm_apply]
    refine csSup_le ?_ ?_
    · refine ⟨0, ?_⟩
      refine ⟨0, ?_, ?_⟩
      · simp [map_zero p]
      · simp
    · rintro z ⟨y, hy, rfl⟩
      exact (hg y).trans hy
  · intro hg y
    calc
      inner ℝ g y ≤ ‖g‖[p,*] * p y := Seminorm.inner_le_dualNorm_mul p y g
      _ ≤ 1 * p y := mul_le_mul_of_nonneg_right hg (by positivity)
      _ = p y := by ring

/-- Proposition 3.20 (1), source-facing finite-dimensional form: the original seminorm is the
support function of the closed unit ball of its dual norm. -/
-- Proof sketch: rewrite the support set in
-- `supportFunction_subdifferential_seminorm_at_zero_eq` using
-- `subdifferential_seminorm_at_zero_eq_dualNorm_closedUnitBall`.
theorem supportFunction_dualNorm_closedUnitBall_eq [p.IsNorm] [FiniteDimensional ℝ E] (x : E) :
    ξ[{g : E | ‖g‖[p,*] ≤ 1}] x = (p x : EReal) := by
  -- Replace the source-facing dual ball by the canonical origin subdifferential from above.
  rw [← subdifferential_seminorm_at_zero_eq_dualNorm_closedUnitBall (p := p)]
  exact supportFunction_subdifferential_seminorm_at_zero_eq (p := p) x

end
