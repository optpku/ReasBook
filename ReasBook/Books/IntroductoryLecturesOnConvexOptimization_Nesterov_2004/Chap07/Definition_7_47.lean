/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_52

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section Oracle

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 7.47 lies in the chapter's oracle / barrier-evaluation domain.

Sampled owner-style declarations:
- `linearOptimizationOracleObjective` in `Chap06/Theorem_6_11`, the chapter owner of affine-plus-
  regularizer oracle objectives on a feasible subtype;
- `IsLinearOptimizationOracle` in `Chap06/Definition_6_52`, the chapter owner for oracle
  selections built from the canonical argmin surface;
- `IsSelfConcordantBarrierOnWith` in `Chap05/Definition_5_3_2`, the chapter owner for
  self-concordant barriers on the intrinsic domain `interior Q`;
- `IsBarrierFunctionOn` in `Chap01/Definition_1_10_18`, the project owner pattern that keeps the
  barrier value map on `interior Q` central;
- `hessian` in `Chap01/Definition_1_4_16`, the project owner for the second derivative on real
  inner-product spaces.

Best owner abstraction:
- source-facing: the linear-maximization oracle, proximal linear-maximization oracle, and the
  barrier-oracle outputs from Definition 7.47;
- core/canonical: `IsLinearOptimizationOracle` for the first two items, and
  `IsSelfConcordantBarrierOnWith (interior Q) ν F` together with the canonical barrier-value,
  gradient, and Hessian maps on `interior Q` for the third;
- bridge/view: the sign flip from maximization to minimization, and the owner-level derivative
  lemmas attached to the canonical barrier restriction.

Primitive data:
- for the first two items, only a candidate selection `StrongDual ℝ E → Q`;
- for the barrier item, no extra public data beyond the ambient barrier function and its canonical
  owner hypothesis.

Derived API:
- the max-attainment statements, derived from `IsLinearOptimizationOracle` after a sign flip;
- the barrier-value map `x ↦ F x` on `interior Q`;
- the first- and second-derivative bridge lemmas on the intrinsic domain.

Source/core/bridge triage:
- source-facing: `IsLinearMaximizationOracle`, `IsProximalLinearMaximizationOracle`, and the
  barrier-oracle outputs of Definition 7.47(3);
- core/canonical: `IsLinearOptimizationOracle`,
  `IsSelfConcordantBarrierOnWith (interior Q) ν F`, and the intrinsic barrier restriction
  `fun x : interior Q ↦ F x`;
- bridge/view: `IsLinearMaximizationOracle.isMaxOn`,
  `IsProximalLinearMaximizationOracle.isMaxOn`, and the owner-level derivative lemmas for
  self-concordant barriers.

The previous file duplicated the Chapter 6 oracle owner by packaging a map and its specification
into new wrapper structures, and it repackaged barrier values and derivatives into a public
structure even though the ambient function `F` and the Chapter 5 barrier owner already determine
those outputs canonically on `interior Q`. This refinement keeps the source semantics unchanged
while moving the first two notions onto the existing Chapter 6 owner and expressing the third item
directly through the established barrier/differential owners instead of a parallel wrapper API.
-/

/-- Definition 7.47 (1): a linear maximization oracle over `Q` is a feasible selection
`c ↦ x*(c)` whose sign-flipped outputs form a Chapter 6 linear optimization oracle for the zero
regularizer on the feasible subtype `Q`. Equivalently, `oracle c` attains the maximum of
`x ↦ c x` on `Q`. -/
def IsLinearMaximizationOracle
    (Q : Set E) (oracle : StrongDual ℝ E → Q) : Prop :=
  IsLinearOptimizationOracle (fun _ : Q ↦ (0 : ℝ)) fun c ↦ oracle (-c)

namespace IsLinearMaximizationOracle

/-- Evaluating a linear maximization oracle at `c` yields a feasible maximizer of `x ↦ c x` on
`Q`. -/
theorem isMaxOn
    {Q : Set E} {oracle : StrongDual ℝ E → Q}
    (horacle : IsLinearMaximizationOracle Q oracle) (c : StrongDual ℝ E) :
    IsMaxOn (fun x ↦ c x) Q (oracle c) := by
  have hmin :
      IsMinOn (linearOptimizationOracleObjective (-c) (fun _ : Q ↦ (0 : ℝ))) Set.univ
        (oracle c) := by
    simpa [IsLinearMaximizationOracle] using
      (IsLinearOptimizationOracle.isMinOn horacle (-c))
  have hmax :
      IsMaxOn (fun x : Q ↦ c x) Set.univ (oracle c) := by
    simpa [linearOptimizationOracleObjective] using hmin.neg
  rw [isMaxOn_iff]
  intro x hx
  exact isMaxOn_univ_iff.mp hmax ⟨x, hx⟩

end IsLinearMaximizationOracle

/-- Definition 7.47 (2): for a prox function `d` on `Q`, a proximal linear maximization oracle is
a feasible selection whose sign-flipped outputs form a Chapter 6 linear optimization oracle for
the regularizer `x ↦ d x` on the feasible subtype `Q`. Equivalently, `oracle c` attains the
maximum of `x ↦ c x - d x` on `Q`. -/
def IsProximalLinearMaximizationOracle
    (Q : Set E) (d : E → ℝ) (oracle : StrongDual ℝ E → Q) : Prop :=
  IsLinearOptimizationOracle (fun x : Q ↦ d x) fun c ↦ oracle (-c)

namespace IsProximalLinearMaximizationOracle

/-- Evaluating a proximal linear maximization oracle at `c` yields a feasible maximizer of
`x ↦ c x - d x` on `Q`. -/
theorem isMaxOn
    {Q : Set E} {d : E → ℝ} {oracle : StrongDual ℝ E → Q}
    (horacle : IsProximalLinearMaximizationOracle Q d oracle) (c : StrongDual ℝ E) :
    IsMaxOn (fun x ↦ c x - d x) Q (oracle c) := by
  have hmin :
      IsMinOn (linearOptimizationOracleObjective (-c) fun x : Q ↦ d x) Set.univ
        (oracle c) := by
    simpa [IsProximalLinearMaximizationOracle] using
      (IsLinearOptimizationOracle.isMinOn horacle (-c))
  have hmax :
      IsMaxOn (fun x : Q ↦ c x - d x) Set.univ (oracle c) := by
    simpa [linearOptimizationOracleObjective, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hmin.neg
  rw [isMaxOn_iff]
  intro x hx
  exact isMaxOn_univ_iff.mp hmax ⟨x, hx⟩

end IsProximalLinearMaximizationOracle

end Oracle

section Barrier

open scoped Gradient

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : Set E} {ν : NNReal} {F : E → ℝ}

/- Definition 7.47 (3): for a self-concordant barrier `F` on `Q`, the barrier-oracle outputs are
the already canonical intrinsic barrier data on `interior Q`: the value restriction
`x ↦ F x`, the gradient map `x ↦ ∇ F x`, and the Hessian map `x ↦ hessian F x`, under the owner
hypothesis `IsSelfConcordantBarrierOnWith (interior Q) ν F`. -/
set_option linter.hashCommand false in
#check (fun x : interior Q ↦ F x)

set_option linter.hashCommand false in
#check (fun x : interior Q ↦ ∇ F x)

set_option linter.hashCommand false in
#check (fun x : interior Q ↦ hessian F x)

namespace IsSelfConcordantBarrierOnWith

/-- A self-concordant barrier has the canonical gradient witness at every interior point of its
domain. -/
theorem hasGradientAt
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F) (x : interior Q) :
    HasGradientAt F (∇ F x) x := by
  let hstd : IsStandardSelfConcordantOn (interior Q) F := hF.toIsStandardSelfConcordantOn
  have hcont :
      ContDiffAt ℝ 1 F x :=
    (hstd.contDiffOn.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).contDiffAt
      (hstd.isOpen_domain.mem_nhds x.property)
  exact (hcont.differentiableAt (by norm_num)).hasGradientAt

/-- A self-concordant barrier has the canonical Hessian witness as the derivative of its gradient
at every interior point of its domain. -/
theorem hasFDerivAt_gradient
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F) (x : interior Q) :
    HasFDerivAt (∇ F) (hessian F x) x := by
  let hstd : IsStandardSelfConcordantOn (interior Q) F := hF.toIsStandardSelfConcordantOn
  have hfderiv : DifferentiableAt ℝ (fderiv ℝ F) (x : E) := by
    exact
      ((hstd.contDiffOn.fderiv_of_isOpen hstd.isOpen_domain
        (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 3)).differentiableOn
        (by simp) x x.property).differentiableAt (hstd.isOpen_domain.mem_nhds x.property)
  have hgrad : DifferentiableAt ℝ (∇ F) (x : E) := by
    unfold gradient
    simpa using ((InnerProductSpace.toDual ℝ E).symm.differentiableAt.comp (x : E) hfderiv)
  simpa [hessian] using hgrad.hasFDerivAt

end IsSelfConcordantBarrierOnWith

end Barrier

end
