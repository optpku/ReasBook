/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_13.Sobolev
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Distribution.Sobolev
public import Mathlib.Analysis.Normed.Lp.SmoothApprox

public section

/- Notation 8.4-extra-1.

This source paragraph mixes standing assumptions on a general domain
`Ω ⊆ EuclideanSpace ℝ (Fin d)`, the notation `∇`, the compactly supported `C¹`
vector-field space `C₀¹(Ω; EuclideanSpace ℝ (Fin d))`, the coordinate
divergence formula, the Euclidean norm, and the Sobolev space `W¹,¹(Ω)`. The
current Chapter 8 API now provides the source-facing domain owner
`domainMeasure Ω`, the raw compactly supported `C¹` vector-field owner
`TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1`, the extra admissibility owner
`AdmissibleTestField Ω` for the additional pointwise bound `‖v x‖ ≤ 1`, the
coordinate divergence `admissibleDivergence`, and the domain-local Sobolev
owner `W11 Ω` with notation `W¹,¹(Ω)`. This file is therefore a thin bridge to
those owners, together with the generic mathlib anchors `gradient`,
`MeasureTheory.Lp.dense_hasCompactSupport_contDiff`, and
`TemperedDistribution.MemSobolev`.

The density theorem and `TemperedDistribution.MemSobolev` remain analogue-only
checks: they support the source's closure language and whole-space Sobolev
background, but neither replaces the Chapter 8 domain-local owner `W¹,¹(Ω)`.
-/

namespace VariationalRegularization

variable {d : ℕ}
variable {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}

/- Notation 8.4-extra-1. Main labeled source-facing bridge.

The `#check` commands below record the canonical owners already available for
the paragraph's gradient notation, the raw compactly supported `C¹`
vector-field space `C₀¹(Ω; EuclideanSpace ℝ (Fin d))`, the extra admissibility
bound `‖v x‖ ≤ 1`, coordinate divergence, restricted-domain measure, and the
Chapter 8 domain-local Sobolev surface `W¹,¹(Ω)`.
-/

#check gradient
#check domainMeasure
#check (TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1)
#check AdmissibleTestField Ω
#check AdmissibleTestField.toTestFunction
#check AdmissibleTestField.ofTestFunction
#check AdmissibleTestField.norm_le_one
#check AdmissibleTestField.spec
#check admissibleDivergence
#check W¹,¹(Ω)
#check W11.pairing_eq_neg_integral_inner

/-
Analogue only for the source's closure wording: this density theorem lives in
`Lp`, not in the Chapter 8 owner `W¹,¹(Ω)` itself.
-/
#check MeasureTheory.Lp.dense_hasCompactSupport_contDiff

/-
Analogue only: `TemperedDistribution.MemSobolev` is a whole-space Sobolev owner,
not the domain-local Chapter 8 owner `W¹,¹(Ω)`.
-/
#check TemperedDistribution.MemSobolev

end VariationalRegularization
