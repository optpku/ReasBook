/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_18
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set Topology

universe u v w

variable {E₁ : Type u} {E₂ : Type v} {E₃ : Type w}
  [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]

/- This file lies in the subsection's cone-composition self-concordant-barrier domain.

Sampled owner declarations:
* `coneCompositionFeasibleSet` from `Definition_5_4_6_3`, the source-facing feasible-set owner
  for the composed cone constraint;
* `coneCompositionBarrier` from `Definition_5_4_6_5`, the source-facing barrier owner on
  `E₁ × E₃`;
* `IsSelfConcordantBarrierOnWith (interior Q) ν F` and
  `IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ`, the genuine barrier hypotheses on the
  intrinsic domains where the source evaluates `F` and `Φ`;
* `coneCompositionBarrier_slice_selfConcordant_bound` from `Theorem_5_4_6_12`, the slice-level
  self-concordance estimate feeding this global barrier statement.

Best owner abstraction:
* source-facing current-file status:
  `coneCompositionBarrier_isSelfConcordantBarrierOnWith_onFeasibleInterior`, the direct textbook
  barrier theorem for the ambient formula `coneCompositionBarrier F Φ ξ β` on
  `interior (coneCompositionFeasibleSet Q K ξ Q₂)`;
* auxiliary current-file owner/API:
  `coneCompositionBarrier_sourceBarrierOnFeasibleInterior`, the surrogate owner retained as
  graph-admissible diagnostic/proof-route API around the textbook statement,
  the proposition shorthand `coneCompositionBarrier_sourceBarrierSurrogateStatement` for the
  conservative surrogate owner,
  together with
  the intrinsic graph-admissible feasible-interior continuous-map owner
  `coneCompositionBarrier_isSelfConcordantBarrierForWith β hξ_concave hF hΦ :
    C(
      interior (coneCompositionFeasibleSet Q K ξ Q₂) ∩
        (fun q : E₁ × E₃ ↦ (ξ q.1, q.2)) ⁻¹' interior Q₂,
      ℝ)`,
  together with the expanded-set theorem
  `coneCompositionBarrier_isSelfConcordantBarrierOnWith_on_graphAdmissibleInterior`, which package
  the ambient formula on the same intrinsic admissible domain where the outer barrier hypotheses
  are directly available, the auxiliary surrogate owner
  `IsConeCompositionBarrierSourceBarrierOnFeasibleInterior` with its constructor theorem
  `IsConeCompositionSourceBarrierExtensionOnFeasibleInterior.toSourceBarrierOnFeasibleInterior`,
  and the bridge-hypothesis compatibility helper
  `coneCompositionBarrier_isSelfConcordantBarrierOnWith_onFeasibleInterior_of_graphInterior`,
  which isolates the extra interior-image bridge
  `hgraph_interior`;
* bridge/view: the pointwise comparison lemmas identifying that intrinsic owner with the ambient
  formula `coneCompositionBarrier F Φ ξ β`.

Primitive data:
* the cone-concavity owner `IsThreeTimesContDiffConcaveOnWith Q K ξ`;
* the compatibility owner `IsBetaCompatibleWith Q K F β ξ`;
* the genuine barrier owners on `interior Q` and `interior Q₂`;
* closedness and convexity of `Q₂`, and the recession-direction hypothesis for `K × {0}`.

Derived API:
* the direct textbook theorem on the full feasible interior;
* the feasible-set graph-domain bridge under the recession hypothesis;
* the conservative surrogate proposition owner together with the auxiliary graph-admissible
  theorem and the ambient-extension API;
* the auxiliary full-feasible-interior compatibility helper with an explicit graph-interior bridge
  hypothesis;
* the intrinsic continuous-map helper and the private graph-interior compatibility route;
* the smaller graph-domain helpers;
* the counterexample showing why a proof route through graph-preimage interiors alone is too weak
  to justify evaluating `Φ` on `interior Q₂`.

Semantic recall via `lean_leansearch` timed out on this nonstandard barrier-composition query, so
the owner choice below is driven by the local chapter API and the source statement. The auxiliary
graph-admissible and ambient-extension theorems remain in the file as diagnostic/proof-route
scaffolding around the source-incomplete label block and the auxiliary surrogate theorem.
-/

section

variable {Q : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
  {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂}
  {β μ ν : NNReal}

section ProductAmbient

variable [InnerProductSpace ℝ (E₁ × E₃)] [CompleteSpace (E₁ × E₃)]
variable [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)]

omit [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [InnerProductSpace ℝ (E₁ × E₃)] [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)] in
/-- Helper for the repaired cone-composition barrier theorem: the recession hypothesis moves any
feasible witness
`(y, z) ∈ Q₂` along the cone direction `ξ x - y` to the graph point `(ξ x, z)`, so every point
of `coneCompositionFeasibleSet` satisfies the source graph condition. -/
private theorem graph_point_mem_of_mem_coneCompositionFeasibleSet
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_hp : p ∈ Q₂) (τ : ℝ) (_hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂)
    {p : E₁ × E₃}
    (hp : p ∈ coneCompositionFeasibleSet Q K ξ Q₂) :
    p.1 ∈ Q ∧ (ξ p.1, p.2) ∈ Q₂ := sorry

omit [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [InnerProductSpace ℝ (E₁ × E₃)] [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)] in
/-- Helper for the repaired cone-composition barrier theorem: every point of
`coneCompositionFeasibleSet` satisfies the graph
condition `x ∈ Q` and `(ξ x, z) ∈ Q₂`. -/
private theorem mem_coneCompositionFeasibleSet_iff_graph_point
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_hp : p ∈ Q₂) (τ : ℝ) (_hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂)
    {p : E₁ × E₃} :
    p ∈ coneCompositionFeasibleSet Q K ξ Q₂ → p.1 ∈ Q ∧ (ξ p.1, p.2) ∈ Q₂ := sorry

omit [NormedAddCommGroup E₁] [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [InnerProductSpace ℝ (E₁ × E₃)] [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)] in
/-- Under the recession hypothesis and the explicit reflexivity fact `0 ∈ K`, the
cone-composition feasible set is exactly the graph-side constraint set
`{q | q.1 ∈ Q ∧ (ξ q.1, q.2) ∈ Q₂}` appearing in the source theorem. -/
theorem coneCompositionFeasibleSet_eq_graphConstraintSet
    (hK_zero : (0 : E₂) ∈ (K : Set E₂))
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_ : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_ : p ∈ Q₂) (τ : ℝ) (_ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂) :
    coneCompositionFeasibleSet Q K ξ Q₂ =
      {q : E₁ × E₃ | q.1 ∈ Q ∧ (ξ q.1, q.2) ∈ Q₂} := sorry

omit [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [InnerProductSpace ℝ (E₁ × E₃)] [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)] in
/-- Helper for the repaired cone-composition barrier theorem: every interior point of the composed
feasible set projects to
the interior of `Q`. This is the part of the source route that survives from the graph rewrite
without requiring any openness of `x ↦ ξ x`. -/
private theorem fst_mem_interior_of_mem_interior_coneCompositionFeasibleSet
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_hp : p ∈ Q₂) (τ : ℝ) (_hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂)
    {p : E₁ × E₃}
    (hp : p ∈ interior (coneCompositionFeasibleSet Q K ξ Q₂)) :
    p.1 ∈ interior Q := sorry

omit [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [InnerProductSpace ℝ (E₁ × E₃)] [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)] in
/-- Helper for the repaired cone-composition barrier theorem: every interior point of the composed
feasible set already
satisfies the graph condition itself, so the evaluation point `(ξ x, z)` lies in `Q₂`. This is
the strongest pointwise domain fact available before one proves any interior-mapping statement
for `x ↦ (ξ x, z)`. -/
private theorem graph_point_mem_of_mem_interior_coneCompositionFeasibleSet
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_hp : p ∈ Q₂) (τ : ℝ) (_hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂)
    {p : E₁ × E₃}
    (hp : p ∈ interior (coneCompositionFeasibleSet Q K ξ Q₂)) :
    p.1 ∈ interior Q ∧ (ξ p.1, p.2) ∈ Q₂ := sorry

omit [InnerProductSpace ℝ E₁] [CompleteSpace E₁]
  [InnerProductSpace ℝ (E₁ × E₃)] [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)] in
/-- Helper for the repaired cone-composition barrier theorem: an interior point of the composed
feasible set lies in the
interior of the pullback of `Q₂` along `(x, z) ↦ (ξ x, z)`. This is the strongest domain fact
available from the graph rewrite without any openness assumption on `ξ`. -/
private theorem mem_interior_graph_preimage_of_mem_interior_coneCompositionFeasibleSet
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_hp : p ∈ Q₂) (τ : ℝ) (_hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂)
    {p : E₁ × E₃}
    (hp : p ∈ interior (coneCompositionFeasibleSet Q K ξ Q₂)) :
    p ∈ interior ((fun q : E₁ × E₃ ↦ (ξ q.1, q.2)) ⁻¹' Q₂) := sorry

omit [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)] in
/-- Helper for the repaired cone-composition barrier theorem: a recession direction of `Q₂` also
preserves `interior Q₂`. -/
private theorem recessionDirection_add_smul_mem_interior
    {q : E₂ × E₃}
    (hQ₂_convex : Convex ℝ Q₂)
    (hrecession : ∀ ⦃p : E₂ × E₃⦄, p ∈ Q₂ → ∀ τ : ℝ, 0 ≤ τ → p + τ • q ∈ Q₂)
    {p : E₂ × E₃} (hp : p ∈ interior Q₂) {τ : ℝ} (hτ : 0 ≤ τ) :
    p + τ • q ∈ interior Q₂ := sorry

omit [CompleteSpace E₁] in
/-- Helper for the repaired cone-composition barrier theorem: concavity of `ξ` rewrites the
chapter's within-domain second
derivative condition to the global repeated derivative `vectorSecondDirectionalDerivative ξ x h`.
-/
private theorem negVectorSecondDirectionalDerivative_mem_of_mem_interior
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    {x : E₁} (hx : x ∈ interior Q) (h : E₁) :
    -vectorSecondDirectionalDerivative ξ x h ∈ K := sorry

omit [CompleteSpace E₁] [InnerProductSpace ℝ (E₁ × E₃)] [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)] in
/-- Helper for the repaired cone-composition barrier theorem: the lifted direction
`-compositionSecondLiftedDirectionDerivative ξ x h = (-D²ξ(x)[h,h], 0)` is a recession direction
of `Q₂` once `-D²ξ(x)[h,h] ∈ K`. -/
private theorem negLiftedDirectionDerivative_recessionOnQ₂
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_hp : p ∈ Q₂) (τ : ℝ) (_hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂)
    {x : E₁} (hx : x ∈ interior Q) (h : E₁) :
    ∀ ⦃p : E₂ × E₃⦄, p ∈ Q₂ → ∀ τ : ℝ, 0 ≤ τ →
      p + τ • (-compositionSecondLiftedDirectionDerivative ξ x h) ∈ Q₂ := sorry

omit [CompleteSpace E₁] [InnerProductSpace ℝ (E₁ × E₃)] [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)] in
/-- Helper for the repaired cone-composition barrier theorem: the same lifted direction preserves
the barrier domain
`interior Q₂`. -/
private theorem negLiftedDirectionDerivative_recessionOnInteriorQ₂
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hQ₂_convex : Convex ℝ Q₂)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_hp : p ∈ Q₂) (τ : ℝ) (_hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂)
    {x : E₁} (hx : x ∈ interior Q) (h : E₁) :
    ∀ ⦃p : E₂ × E₃⦄, p ∈ interior Q₂ → ∀ τ : ℝ, 0 ≤ τ →
      p + τ • (-compositionSecondLiftedDirectionDerivative ξ x h) ∈ interior Q₂ := sorry

omit [CompleteSpace E₁] [InnerProductSpace ℝ (E₁ × E₃)] [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)] in
/-- Helper for the repaired cone-composition barrier theorem: the graph map `(x, z) ↦ (ξ x, z)`
is `C³` on the region where
its first coordinate stays in `interior Q`. -/
private theorem graphMap_contDiffOn_fstInterior
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ) :
    ContDiffOn ℝ 3 (fun q : E₁ × E₃ ↦ (ξ q.1, q.2))
      ((Prod.fst : E₁ × E₃ → E₁) ⁻¹' interior Q) := sorry

omit [InnerProductSpace ℝ (E₁ × E₃)] [CompleteSpace (E₁ × E₃)]
  [InnerProductSpace ℝ (E₂ × E₃)] [CompleteSpace (E₂ × E₃)] in
/-- Helper for the repaired cone-composition barrier theorem: once the domain bridge provides
`q.1 ∈ interior Q` and `(ξ q.1, q.2) ∈ interior Q₂`, the regularity inputs needed for the
future composition step are already available on that repaired domain. -/
private theorem coneCompositionBarrier_contDiffOn_on_repaired_domain
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F) :
    ContDiffOn ℝ 3 (fun q : E₁ × E₃ ↦ (ξ q.1, q.2))
        {q : E₁ × E₃ | q.1 ∈ interior Q ∧ (ξ q.1, q.2) ∈ interior Q₂} ∧
      ContDiffOn ℝ 3 (fun q : E₁ × E₃ ↦ F q.1)
        {q : E₁ × E₃ | q.1 ∈ interior Q ∧ (ξ q.1, q.2) ∈ interior Q₂} := sorry

end ProductAmbient

/- The current chapter owners still encode barriers as ambient maps `E → ℝ`, but the source uses
`F` and `Φ` intrinsically on the barrier sets `Q` and `Q₂`. The next helper records the local
open-domain obstruction: interior membership in a graph preimage does not by itself force the
graph point into `interior Q₂`. It is therefore only diagnostic evidence that any intrinsic
full-feasible-set owner must be bridged to the ambient formula more carefully than the naive
graph-preimage argument. -/
/-- Helper for the repaired cone-composition barrier theorem: interior membership in a graph
preimage does not force the graph
point into the interior of the target set. This counterexample explains why the present ambient
total-function statement cannot recover the `interior Q₂` hypothesis needed to apply `hΦ`. -/
private theorem graphPreimageInteriorDoesNotForceImageInterior :
    let graphMap : ℝ × ℝ → ℝ × ℝ := fun q ↦ (0, q.2)
    let Q₂ : Set (ℝ × ℝ) := (Prod.fst : ℝ × ℝ → ℝ) ⁻¹' Set.Iic (0 : ℝ)
    ((0, 0) : ℝ × ℝ) ∈ interior (graphMap ⁻¹' Q₂) ∧
      graphMap (0, 0) ∉ interior Q₂ := sorry

/-- Helper for the repaired cone-composition barrier theorem: if one additionally knows that every
interior feasible point
maps into `interior Q₂`, then the ambient total-function owner is available directly on the open
feasible-set domain. This remains a compatibility helper for one direct proof route; the public
theorems below keep the source-facing composed barrier and its Chapter 5/Chapter 1 owners as the
main API. -/
private theorem coneCompositionBarrier_isSelfConcordantBarrierOnWith_of_graphInterior_aux
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hξ_compat : IsBetaCompatibleWith Q K F β ξ)
    (hQ₂_closed : IsClosed Q₂)
    (hQ₂_convex : Convex ℝ Q₂)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_ : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_ : p ∈ Q₂) (τ : ℝ) (_ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂)
    (hgraph_interior :
      ∀ ⦃p : E₁ × E₃⦄, p ∈ interior (coneCompositionFeasibleSet Q K ξ Q₂) →
        (ξ p.1, p.2) ∈ interior Q₂) :
    IsSelfConcordantBarrierOnWith
      (interior (coneCompositionFeasibleSet Q K ξ Q₂))
      (μ + β ^ 3 * ν)
      (coneCompositionBarrier F Φ ξ β) := sorry

/-- Helper owner for the repaired cone-composition barrier theorem: the ambient formula
`Ψ(x, z) = Φ (ξ x, z) + β^3 F x` packaged as a continuous map on the graph-admissible feasible
interior
`interior (coneCompositionFeasibleSet Q K ξ Q₂) ∩
  (fun q : E₁ × E₃ ↦ (ξ q.1, q.2)) ⁻¹' interior Q₂`,
where the outer barrier hypotheses on `Φ` apply. -/
def coneCompositionBarrier_isSelfConcordantBarrierForWith
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (β : NNReal)
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ) :
    C(
      (interior (coneCompositionFeasibleSet Q K ξ Q₂) ∩
        (fun q : E₁ × E₃ ↦ (ξ q.1, q.2)) ⁻¹' interior Q₂ : Set (E₁ × E₃)),
      ℝ) where
  toFun q := coneCompositionBarrier F Φ ξ β q.1
  continuous_toFun := sorry

omit [NormedSpace ℝ E₃] in
/-- Companion for the repaired intrinsic owner: it evaluates pointwise to the
ambient cone-composition barrier formula on its graph-admissible domain. -/
@[simp] theorem coneCompositionBarrier_isSelfConcordantBarrierForWith_def
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (q :
      (interior (coneCompositionFeasibleSet Q K ξ Q₂) ∩
        (fun p : E₁ × E₃ ↦ (ξ p.1, p.2)) ⁻¹' interior Q₂ : Set (E₁ × E₃))) :
    coneCompositionBarrier_isSelfConcordantBarrierForWith β hξ_concave hF hΦ q =
      coneCompositionBarrier F Φ ξ β q := sorry

/-- Companion for the repaired intrinsic owner: the intrinsic restricted-domain owner has the
expected
graph-admissible barrier formula as its underlying function. -/
@[simp] theorem coneCompositionBarrier_isSelfConcordantBarrierForWith_toFun
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ) :
    (coneCompositionBarrier_isSelfConcordantBarrierForWith
        β hξ_concave hF hΦ).toFun =
      fun q ↦ coneCompositionBarrier F Φ ξ β q.1 := sorry

/-- Companion for the repaired intrinsic owner: it agrees pointwise with the
ambient cone-composition barrier on its graph-admissible domain. -/
theorem coneCompositionBarrier_isSelfConcordantBarrierForWith_eqOn_graphInterior
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ) :
    Set.EqOn
      (coneCompositionBarrier_isSelfConcordantBarrierForWith
        β hξ_concave hF hΦ)
      (fun q ↦ coneCompositionBarrier F Φ ξ β q.1)
      Set.univ := sorry

omit [NormedSpace ℝ E₃] in
/-- Companion for the repaired intrinsic owner: on a graph-admissible feasible-interior point, the
intrinsic
restricted-domain owner evaluates to the ambient cone-composition barrier formula. -/
@[simp] theorem coneCompositionBarrier_isSelfConcordantBarrierForWith_spec
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (q :
      (interior (coneCompositionFeasibleSet Q K ξ Q₂) ∩
        (fun p : E₁ × E₃ ↦ (ξ p.1, p.2)) ⁻¹' interior Q₂ : Set (E₁ × E₃))) :
    coneCompositionBarrier_isSelfConcordantBarrierForWith β hξ_concave hF hΦ q =
      coneCompositionBarrier F Φ ξ β q := sorry

omit [NormedSpace ℝ E₃] in
/-- Companion for the repaired intrinsic owner: on a graph-admissible feasible-interior point, the
intrinsic
restricted-domain owner evaluates to the ambient cone-composition barrier formula. -/
@[simp] theorem coneCompositionBarrier_isSelfConcordantBarrierForWith_apply
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (q :
      (interior (coneCompositionFeasibleSet Q K ξ Q₂) ∩
        (fun p : E₁ × E₃ ↦ (ξ p.1, p.2)) ⁻¹' interior Q₂ : Set (E₁ × E₃))) :
    coneCompositionBarrier_isSelfConcordantBarrierForWith β hξ_concave hF hΦ q =
      coneCompositionBarrier F Φ ξ β q := sorry

/-- Auxiliary graph-admissible theorem: in the present Chapter 5 ambient-owner API, the source
formula
`Ψ(x, z) = Φ (ξ x, z) + β^3 F x` is recorded on the graph-admissible feasible interior
`interior (coneCompositionFeasibleSet Q K ξ Q₂) ∩
  (fun q : E₁ × E₃ ↦ (ξ q.1, q.2)) ⁻¹' interior Q₂`,
so `Φ` is evaluated only where its self-concordant-barrier hypotheses apply. This is the
auxiliary graph-region bridge used to expose the full source-feasible-set barrier owner below. -/
theorem coneCompositionBarrier_isSelfConcordantBarrierOnWith_on_graphAdmissibleInterior
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hξ_compat : IsBetaCompatibleWith Q K F β ξ)
    (hQ₂_closed : IsClosed Q₂)
    (hQ₂_convex : Convex ℝ Q₂)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (hp : p ∈ Q₂) (τ : ℝ) (hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂) :
    IsSelfConcordantBarrierOnWith
      (interior (coneCompositionFeasibleSet Q K ξ Q₂) ∩
        (fun q : E₁ × E₃ ↦ (ξ q.1, q.2)) ⁻¹' interior Q₂)
      (μ + β ^ 3 * ν)
      (coneCompositionBarrier F Φ ξ β) := sorry

/-- Canonical feasible-interior restriction of the named textbook formula
`coneCompositionBarrier F Φ ξ β`. This is the intrinsic continuous-map owner used for the
full-feasible-set barrier-function clause of the auxiliary source-barrier surrogate owner. -/
def coneCompositionBarrierOnFeasibleInterior
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (Q : Set E₁) (Q₂ : Set (E₂ × E₃)) (K : ConvexCone ℝ E₂)
    (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂)
    (β : NNReal) :
    C(interior (coneCompositionFeasibleSet Q K ξ Q₂), ℝ) where
  toFun q := coneCompositionBarrier F Φ ξ β q.1
  continuous_toFun := sorry

omit [NormedSpace ℝ E₃] in
/-- Companion for the canonical feasible-interior restriction: it evaluates pointwise to the
ambient textbook formula. -/
@[simp] theorem coneCompositionBarrierOnFeasibleInterior_apply
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (q : interior (coneCompositionFeasibleSet Q K ξ Q₂)) :
    coneCompositionBarrierOnFeasibleInterior Q Q₂ K F Φ ξ β q =
      coneCompositionBarrier F Φ ξ β q := sorry

/-- The graph-admissible feasible interior for the cone-composition barrier: these are the
interior feasible points whose graph image lies in `interior Q₂`, so the outer barrier `Φ`
is evaluated on its intrinsic barrier domain. -/
def coneCompositionGraphAdmissibleInterior
    (Q : Set E₁) (Q₂ : Set (E₂ × E₃)) (K : ConvexCone ℝ E₂)
    (ξ : E₁ → E₂) :
    Set (E₁ × E₃) :=
  interior (coneCompositionFeasibleSet Q K ξ Q₂) ∩
    (fun q : E₁ × E₃ ↦ (ξ q.1, q.2)) ⁻¹' interior Q₂

/-- The same graph-admissible condition, but expressed on the intrinsic feasible-interior subtype
used by `IsBarrierFunctionOn`. -/
def coneCompositionGraphAdmissibleInteriorInFeasibleInterior
    (Q : Set E₁) (Q₂ : Set (E₂ × E₃)) (K : ConvexCone ℝ E₂)
    (ξ : E₁ → E₂) :
    Set (interior (coneCompositionFeasibleSet Q K ξ Q₂)) :=
  { q | (ξ q.1.1, q.1.2) ∈ interior Q₂ }

/-- Auxiliary owner for the conservative source-barrier surrogate: an ambient extension `Ψ`
together with an intrinsic feasible-
interior representative `Ψfeas` packages the source-faithful barrier statement when both agree
with the textbook cone-composition formula on the graph-admissible feasible interior where the
outer barrier hypotheses on `Φ` apply, `Ψfeas` is a barrier function on the full feasible set,
and `Ψ` is `(μ + β^3 ν)`-self-concordant on that graph-admissible interior. -/
def IsConeCompositionSourceBarrierExtensionOnFeasibleInterior
    [InnerProductSpace ℝ (E₁ × E₃)]
    [CompleteSpace (E₁ × E₃)]
    [InnerProductSpace ℝ (E₂ × E₃)]
    [CompleteSpace (E₂ × E₃)]
    (Q : Set E₁) (Q₂ : Set (E₂ × E₃)) (K : ConvexCone ℝ E₂)
    (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂)
    (β μ ν : NNReal)
    (Ψ : E₁ × E₃ → ℝ)
    (Ψfeas :
      { ψ : C(interior (coneCompositionFeasibleSet Q K ξ Q₂), ℝ) //
          Set.EqOn ψ
            (coneCompositionBarrierOnFeasibleInterior Q Q₂ K F Φ ξ β)
            (coneCompositionGraphAdmissibleInteriorInFeasibleInterior Q Q₂ K ξ) }) : Prop :=
  Set.EqOn Ψ (coneCompositionBarrier F Φ ξ β)
    (coneCompositionGraphAdmissibleInterior Q Q₂ K ξ) ∧
  IsBarrierFunctionOn
    (coneCompositionFeasibleSet Q K ξ Q₂)
    Ψfeas.1 ∧
  IsSelfConcordantBarrierOnWith
    (coneCompositionGraphAdmissibleInterior Q Q₂ K ξ)
    (μ + β ^ 3 * ν)
    Ψ

/-- Auxiliary source-barrier surrogate owner: there exists a barrier-function owner on the full
feasible set whose intrinsic feasible-interior values agree with the textbook cone-composition
formula on the graph-admissible feasible interior, and there exists an ambient self-concordant
extension on that same graph-admissible interior with the same agreement there. This keeps the
textbook formula available without forcing boundary values of `Φ`
outside `interior Q₂` into the public owner. -/
class IsConeCompositionBarrierSourceBarrierOnFeasibleInterior
    [InnerProductSpace ℝ (E₁ × E₃)]
    [CompleteSpace (E₁ × E₃)]
    [InnerProductSpace ℝ (E₂ × E₃)]
    [CompleteSpace (E₂ × E₃)]
    (Q : Set E₁) (Q₂ : Set (E₂ × E₃)) (K : ConvexCone ℝ E₂)
    (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂)
    (β μ ν : NNReal) : Prop where
  exists_barrierFunctionOn :
    ∃ Ψfeas :
      { ψ : C(interior (coneCompositionFeasibleSet Q K ξ Q₂), ℝ) //
          Set.EqOn ψ
            (coneCompositionBarrierOnFeasibleInterior Q Q₂ K F Φ ξ β)
            (coneCompositionGraphAdmissibleInteriorInFeasibleInterior Q Q₂ K ξ) },
      IsBarrierFunctionOn
        (coneCompositionFeasibleSet Q K ξ Q₂)
        Ψfeas.1
  exists_graphAdmissibleSelfConcordantExtension :
    ∃ Ψ : E₁ × E₃ → ℝ,
      Set.EqOn Ψ (coneCompositionBarrier F Φ ξ β)
        (coneCompositionGraphAdmissibleInterior Q Q₂ K ξ) ∧
      IsSelfConcordantBarrierOnWith
        (coneCompositionGraphAdmissibleInterior Q Q₂ K ξ)
        (μ + β ^ 3 * ν)
        Ψ

omit [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [NormedSpace ℝ E₃] in
/-- Companion for the auxiliary surrogate owner: it consists of the canonical feasible-interior
barrier-function existence statement together with a graph-admissible self-concordant extension,
both agreeing with the textbook cone-composition formula where `(ξ x, z) ∈ interior Q₂`. -/
theorem isConeCompositionBarrierSourceBarrierOnFeasibleInterior_iff
    [InnerProductSpace ℝ (E₁ × E₃)]
    [CompleteSpace (E₁ × E₃)]
    [InnerProductSpace ℝ (E₂ × E₃)]
    [CompleteSpace (E₂ × E₃)]
    (Q : Set E₁) (Q₂ : Set (E₂ × E₃)) (K : ConvexCone ℝ E₂)
    (F : E₁ → ℝ) (Φ : E₂ × E₃ → ℝ) (ξ : E₁ → E₂)
    (β μ ν : NNReal) :
    IsConeCompositionBarrierSourceBarrierOnFeasibleInterior
        Q Q₂ K F Φ ξ β μ ν ↔
      (∃ Ψfeas :
        { ψ : C(interior (coneCompositionFeasibleSet Q K ξ Q₂), ℝ) //
            Set.EqOn ψ
              (coneCompositionBarrierOnFeasibleInterior Q Q₂ K F Φ ξ β)
              (coneCompositionGraphAdmissibleInteriorInFeasibleInterior Q Q₂ K ξ) },
          IsBarrierFunctionOn
            (coneCompositionFeasibleSet Q K ξ Q₂)
            Ψfeas.1) ∧
        ∃ Ψ : E₁ × E₃ → ℝ,
          Set.EqOn Ψ (coneCompositionBarrier F Φ ξ β)
            (coneCompositionGraphAdmissibleInterior Q Q₂ K ξ) ∧
          IsSelfConcordantBarrierOnWith
            (coneCompositionGraphAdmissibleInterior Q Q₂ K ξ)
            (μ + β ^ 3 * ν)
            Ψ :=
  sorry

omit [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [NormedSpace ℝ E₃] in
/-- Companion for the auxiliary surrogate owner: it exposes the graph-admissible self-concordant
extension data together with agreement with the exact textbook formula on that graph-admissible
feasible interior. -/
theorem
    IsConeCompositionBarrierSourceBarrierOnFeasibleInterior.graphAdmissibleSelfConcordantExtension
    [InnerProductSpace ℝ (E₁ × E₃)]
    [CompleteSpace (E₁ × E₃)]
    [InnerProductSpace ℝ (E₂ × E₃)]
    [CompleteSpace (E₂ × E₃)]
    {Q : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
    {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂}
    {β μ ν : NNReal}
    (h :
      IsConeCompositionBarrierSourceBarrierOnFeasibleInterior
        Q Q₂ K F Φ ξ β μ ν) :
    ∃ Ψ : E₁ × E₃ → ℝ,
      Set.EqOn Ψ (coneCompositionBarrier F Φ ξ β)
        (coneCompositionGraphAdmissibleInterior Q Q₂ K ξ) ∧
      IsSelfConcordantBarrierOnWith
        (coneCompositionGraphAdmissibleInterior Q Q₂ K ξ)
        (μ + β ^ 3 * ν)
        Ψ :=
  sorry

omit [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [NormedSpace ℝ E₃] in
/-- Companion for the auxiliary surrogate owner: it exposes a full-feasible-set
barrier-function witness whose intrinsic feasible-interior values agree with the textbook
cone-composition formula on the graph-admissible feasible interior. -/
theorem IsConeCompositionBarrierSourceBarrierOnFeasibleInterior.barrierFunctionOn
    [InnerProductSpace ℝ (E₁ × E₃)]
    [CompleteSpace (E₁ × E₃)]
    [InnerProductSpace ℝ (E₂ × E₃)]
    [CompleteSpace (E₂ × E₃)]
    {Q : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
    {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂}
    {β μ ν : NNReal}
    (h :
      IsConeCompositionBarrierSourceBarrierOnFeasibleInterior
        Q Q₂ K F Φ ξ β μ ν) :
    ∃ Ψfeas :
      { ψ : C(interior (coneCompositionFeasibleSet Q K ξ Q₂), ℝ) //
          Set.EqOn ψ
            (coneCompositionBarrierOnFeasibleInterior Q Q₂ K F Φ ξ β)
            (coneCompositionGraphAdmissibleInteriorInFeasibleInterior Q Q₂ K ξ) },
      IsBarrierFunctionOn
        (coneCompositionFeasibleSet Q K ξ Q₂)
        Ψfeas.1 :=
  sorry

omit [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [NormedSpace ℝ E₃] in
/-- Compatibility companion for the auxiliary surrogate owner: it also supplies the old existential
barrier-function packaging after forgetting the graph-admissible agreement witness. -/
theorem IsConeCompositionBarrierSourceBarrierOnFeasibleInterior.exists_barrierFunctionWitness
    [InnerProductSpace ℝ (E₁ × E₃)]
    [CompleteSpace (E₁ × E₃)]
    [InnerProductSpace ℝ (E₂ × E₃)]
    [CompleteSpace (E₂ × E₃)]
    {Q : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
    {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂}
    {β μ ν : NNReal}
    (h :
      IsConeCompositionBarrierSourceBarrierOnFeasibleInterior
        Q Q₂ K F Φ ξ β μ ν) :
    ∃ Ψfeas : C(interior (coneCompositionFeasibleSet Q K ξ Q₂), ℝ),
      IsBarrierFunctionOn
        (coneCompositionFeasibleSet Q K ξ Q₂)
        Ψfeas :=
  sorry

omit [InnerProductSpace ℝ E₁] [CompleteSpace E₁] [NormedSpace ℝ E₃] in
/-- Bridge from the auxiliary ambient-extension helper infrastructure to the repaired
surrogate owner: once the helper extension data already agrees with the textbook formula on
the graph-admissible feasible interior, it yields the full-feasible-set barrier package attached
to the named textbook formula. -/
theorem IsConeCompositionSourceBarrierExtensionOnFeasibleInterior.toSourceBarrierOnFeasibleInterior
    [InnerProductSpace ℝ (E₁ × E₃)]
    [CompleteSpace (E₁ × E₃)]
    [InnerProductSpace ℝ (E₂ × E₃)]
    [CompleteSpace (E₂ × E₃)]
    {Q : Set E₁} {Q₂ : Set (E₂ × E₃)} {K : ConvexCone ℝ E₂}
    {F : E₁ → ℝ} {Φ : E₂ × E₃ → ℝ} {ξ : E₁ → E₂}
    {β μ ν : NNReal}
    {Ψ : E₁ × E₃ → ℝ}
    {Ψfeas :
      { ψ : C(interior (coneCompositionFeasibleSet Q K ξ Q₂), ℝ) //
          Set.EqOn ψ
            (coneCompositionBarrierOnFeasibleInterior Q Q₂ K F Φ ξ β)
            (coneCompositionGraphAdmissibleInteriorInFeasibleInterior Q Q₂ K ξ) }}
    (hext :
      IsConeCompositionSourceBarrierExtensionOnFeasibleInterior
        Q Q₂ K F Φ ξ β μ ν Ψ Ψfeas) :
    IsConeCompositionBarrierSourceBarrierOnFeasibleInterior
      Q Q₂ K F Φ ξ β μ ν := sorry

/-- Auxiliary conservative proposition shorthand for the surrogate owner retained in this file.
It packages the current graph-admissible replacement API without making that surrogate owner the
label-carrying source theorem. -/
abbrev coneCompositionBarrier_sourceBarrierSurrogateStatement
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hξ_compat : IsBetaCompatibleWith Q K F β ξ)
    (hQ₂_closed : IsClosed Q₂)
    (hQ₂_convex : Convex ℝ Q₂)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_ : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_ : p ∈ Q₂) (τ : ℝ) (_ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂) : Prop :=
    by
      let _ := instProd23Inner
      let _ := instProd23Complete
      let _ := hξ_concave
      let _ := hξ_compat
      let _ := hQ₂_closed
      let _ := hQ₂_convex
      let _ := hF
      let _ := hΦ
      let _ := hK_recession
      exact
        IsConeCompositionBarrierSourceBarrierOnFeasibleInterior
          Q Q₂ K F Φ ξ β μ ν

/-- Companion for the auxiliary surrogate proposition shorthand: unfolding it recovers the
surrogate owner used in the current Chapter 5 API. -/
@[simp] theorem coneCompositionBarrier_sourceBarrierSurrogateStatement_iff
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hξ_compat : IsBetaCompatibleWith Q K F β ξ)
    (hQ₂_closed : IsClosed Q₂)
    (hQ₂_convex : Convex ℝ Q₂)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (_ : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (_ : p ∈ Q₂) (τ : ℝ) (_ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂) :
    coneCompositionBarrier_sourceBarrierSurrogateStatement
        hξ_concave hξ_compat hQ₂_closed hQ₂_convex hF hΦ hK_recession ↔
      IsConeCompositionBarrierSourceBarrierOnFeasibleInterior
        Q Q₂ K F Φ ξ β μ ν :=
  Iff.rfl

/-- Auxiliary surrogate theorem retained in the current Chapter 5 API: under the textbook
hypotheses, one can package a barrier-function witness on the full cone-composition feasible set
together with agreement with the exact textbook formula on the graph-admissible feasible interior
where the outer barrier hypotheses on `Φ` apply. -/
theorem coneCompositionBarrier_sourceBarrierOnFeasibleInterior
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hξ_compat : IsBetaCompatibleWith Q K F β ξ)
    (hQ₂_closed : IsClosed Q₂)
    (hQ₂_convex : Convex ℝ Q₂)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (hp : p ∈ Q₂) (τ : ℝ) (hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂) :
    IsConeCompositionBarrierSourceBarrierOnFeasibleInterior
      Q Q₂ K F Φ ξ β μ ν := sorry

/-- Theorem 5.4.6.13: under the textbook hypotheses, the ambient Chapter 5 owner
`coneCompositionBarrier F Φ ξ β` is a self-concordant barrier on the full feasible interior
`interior (coneCompositionFeasibleSet Q K ξ Q₂)`. -/
theorem coneCompositionBarrier_isSelfConcordantBarrierOnWith_onFeasibleInterior
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hξ_compat : IsBetaCompatibleWith Q K F β ξ)
    (hQ₂_closed : IsClosed Q₂)
    (hQ₂_convex : Convex ℝ Q₂)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (hp : p ∈ Q₂) (τ : ℝ) (hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂) :
    IsSelfConcordantBarrierOnWith
      (interior (coneCompositionFeasibleSet Q K ξ Q₂))
      (μ + β ^ 3 * ν)
      (coneCompositionBarrier F Φ ξ β) := sorry

/-- Auxiliary compatibility theorem: if one additionally knows that every interior feasible point
maps into `interior Q₂`, then the same ambient Chapter 5 owner
`coneCompositionBarrier F Φ ξ β` is a self-concordant barrier on the full feasible interior
`interior (coneCompositionFeasibleSet Q K ξ Q₂)`. This explicit bridge hypothesis isolates one
proof route but is not part of the textbook statement. -/
theorem coneCompositionBarrier_isSelfConcordantBarrierOnWith_onFeasibleInterior_of_graphInterior
    [instProd13Inner : InnerProductSpace ℝ (E₁ × E₃)]
    [instProd13Complete : CompleteSpace (E₁ × E₃)]
    [instProd23Inner : InnerProductSpace ℝ (E₂ × E₃)]
    [instProd23Complete : CompleteSpace (E₂ × E₃)]
    (hξ_concave : IsThreeTimesContDiffConcaveOnWith Q K ξ)
    (hξ_compat : IsBetaCompatibleWith Q K F β ξ)
    (hQ₂_closed : IsClosed Q₂)
    (hQ₂_convex : Convex ℝ Q₂)
    (hF : IsSelfConcordantBarrierOnWith (interior Q) ν F)
    (hΦ : IsSelfConcordantBarrierOnWith (interior Q₂) μ Φ)
    (hK_recession :
      ∀ ⦃s : E₂⦄ (hs : s ∈ (K : Set E₂)) ⦃p : E₂ × E₃⦄
        (hp : p ∈ Q₂) (τ : ℝ) (hτ : 0 ≤ τ),
          p + τ • (s, (0 : E₃)) ∈ Q₂)
    (hgraph_interior :
      ∀ ⦃p : E₁ × E₃⦄, p ∈ interior (coneCompositionFeasibleSet Q K ξ Q₂) →
        (ξ p.1, p.2) ∈ interior Q₂) :
    IsSelfConcordantBarrierOnWith
      (interior (coneCompositionFeasibleSet Q K ξ Q₂))
      (μ + β ^ 3 * ν)
      (coneCompositionBarrier F Φ ξ β) := sorry

end

end
