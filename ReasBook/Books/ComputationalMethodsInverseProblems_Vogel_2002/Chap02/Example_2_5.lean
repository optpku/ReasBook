/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Notation_2_1
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_5.SmoothNegativeLaplacian
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_13.Sobolev
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.InnerProductSpace.LinearPMap
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

public section

/-!
Partial source-facing statement file for this source item.

The source splits into three layers. The smooth negative-Laplacian formula from
`(2.10)` now has a faithful directly importable Lean owner in
`Book.Ch2.Example_2_5.SmoothNegativeLaplacian`. The domain-local `H¹(Ω)` owner
from `(2.9)` and the extension claim `L : H¹(Ω) → L²(Ω)` with norm,
self-adjointness, and positivity properties remain unresolved in the current
repository snapshot, because the exact owner, the minimal explicit `Ω`
hypotheses, and the intended operator domain/boundary conditions are not yet
fixed.
-/

noncomputable section

section

variable {d : ℕ}
variable (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d)))

/- 
Example 2.5. Main labeled source-facing blocker entry.

The source combines three layers: the `H¹(Ω)` inner-product/closure
construction from `(2.9)`, the smooth negative-Laplacian formula from `(2.10)`,
and the extension claim `L : H¹(Ω) → L²(Ω)` with norm, self-adjointness, and
positivity properties. The current repository snapshot still does not expose
the authoritative domain-local `H¹(Ω)` owner or the exact operator realization
with the explicit `Ω` hypotheses needed to state clauses `(1)` and `(3)`
faithfully. This file therefore remains explicitly blocked upstream on those
layers. The declarations and `#check` commands below record only the verified
smooth-core formula layer and backend anchors.
-/

/- Example 2.5 (1). The source first introduces a domain-local `H¹(Ω)` inner
product and defines `H¹(Ω)` as the completion/closure of `C¹(Ω)` for the
associated norm.

The current repository snapshot exposes the verified source-facing ingredients
`C¹(Ω)`, `VariationalRegularization.domainMeasure Ω`, and the canonical
`MeasureTheory.Lp ℝ 2 (VariationalRegularization.domainMeasure Ω)` surface for
`L²(Ω)`, but it still does not expose the exact domain-local `H¹(Ω)` owner
induced by `(2.9)`. The `#check` commands immediately below record only these
verified anchors and do not guess the unresolved owner.
-/
#check C¹((Ω : Set (EuclideanSpace ℝ (Fin d))))
#check VariationalRegularization.domainMeasure
#check (MeasureTheory.Lp ℝ 2 (VariationalRegularization.domainMeasure Ω))

/- Example 2.5 (2). For smooth `f`, the source defines the pointwise negative
Laplacian formula `(2.10)`.

The current repository snapshot already exposes a faithful reusable owner for
this clause in `smoothNegativeLaplacianWithin Ω`, together with its pointwise
evaluation lemma and the underlying `InnerProductSpace.laplacianWithin`
backend. The `#check` commands immediately below record exactly this verified
formula layer and do not mix in the later extension claim.
-/
#check (smoothNegativeLaplacianWithin Ω)
#check (smoothNegativeLaplacianWithin_apply Ω)

/- Additional local support check for the verified smooth backend. -/
#check
  (fun (f : EuclideanSpace ℝ (Fin d) → ℝ) ↦
    -InnerProductSpace.laplacianWithin f Ω)

/- Example 2.5 (3). The source finally asserts that the negative Laplacian has
an extension `L : H¹(Ω) → L²(Ω)` with `‖L‖ = 1`, and that this operator is
self-adjoint and positive semidefinite.

The current repository snapshot still does not expose the exact domain-local
`H¹(Ω)` owner or the exact operator realization together with the minimal
explicit `Ω` regularity and domain/boundary assumptions needed to state that
claim faithfully. This clause therefore remains unresolved rather than
semantically approved. The target file records only verified operator-theory
anchors for the future faithful realization, listed below outside the `Ω`
section because they do not depend on the domain parameter.
-/

end

/-
Verified global anchors for the unresolved `H¹(Ω)` and operator layers used in
this item.
-/
#check Set.contDiffOne

/-
Analogue only: `VariationalRegularization.W11` is the repository's current
domain-local weak first-order Sobolev owner, but it is `W¹,¹(Ω)`, not the
source `H¹(Ω)`.
-/
#check VariationalRegularization.W11

/-
Analogue only for the source's closure language: this density theorem lives in
`Lp`, not in a domain-local `H¹(Ω)` owner.
-/
#check MeasureTheory.Lp.dense_hasCompactSupport_contDiff

/-
Analogue only: `TemperedDistribution.MemSobolev` is a whole-space Sobolev
owner, not the domain-local `H¹(Ω)` required by the source.
-/
#check TemperedDistribution.MemSobolev

/-
Smooth pointwise backend only: `InnerProductSpace.laplacianWithin` provides the
pointwise Laplacian on sets, not the extended operator asserted by the source.
-/
#check InnerProductSpace.laplacianWithin

/-
Operator-theory anchors only: these are generic positivity/self-adjointness and
dense-domain APIs for whichever precise operator owner is later chosen.
-/
#check LinearPMap
#check ContinuousLinearMap.isPositive_iff'
#check ContinuousLinearMap.IsPositive.isSelfAdjoint
#check IsSelfAdjoint.dense_domain
