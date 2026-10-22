/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Example_5_3_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Proposition_5_3_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_1_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section FunctionalConstraintStandardFormBarrier

variable {X : Type u} {m : ℕ}

local notation "StdPoint" => ℝ × ℝ × X
local notation "PairPoint" => X × ℝ
local notation "StatePoint" => ℝ × X
local notation "PairPointL2" => WithLp 2 PairPoint
local notation "StatePointL2" => WithLp 2 StatePoint
local notation "StdPointL2" => WithLp 2 (ℝ × StatePointL2)
local notation "ofPairPoint" => (WithLp.ofLp : PairPointL2 → PairPoint)
local notation "ofStatePoint" => (WithLp.ofLp : StatePointL2 → StatePoint)
local notation "ofStdPoint" =>
  (Prod.map id ofStatePoint) ∘ (WithLp.ofLp : StdPointL2 → ℝ × StatePointL2)

/- Proposition 5.3.6.2 lies in the chapter's self-concordant-barrier / standard-form lifting
domain.

Sampled owner declarations in this domain:
* `IsSelfConcordantBarrierOnWith` from `Definition_5_3_2`, the chapter owner for
  self-concordant barriers;
* `IsSelfConcordantBarrierOnWith.add` from `Theorem_5_3_2`, the canonical barrier-sum theorem;
* `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap` from `Theorem_5_3_3`, the canonical
  affine-pullback theorem for barriers over complete real inner-product spaces;
* `strictConstrainedEpigraph` from `Theorem_5_3_5`, the source-facing strict epigraph owner
  reused by the objective and functional-constraint barrier hypotheses;
* mathlib `WithLp 2 (X × ℝ)` and `WithLp 2 (ℝ × WithLp 2 (ℝ × X))` together with `WithLp.ofLp`,
  the canonical `L²` pair/triple owners and their bridge back to the raw textbook coordinates;
* `epigraphLogBarrier_isSelfConcordantBarrierOnWith` from `Theorem_5_3_5`, the Chapter 5
  strict-epigraph barrier theorem over that owner.

Source/core/bridge triage:
* source-facing: the standard-form barrier on triples `(ξ, κ, x)`;
* core/canonical: `IsSelfConcordantBarrierOnWith` on the canonical `L²` pair/triple owners
  `WithLp 2 (X × ℝ)` and `WithLp 2 (ℝ × WithLp 2 (ℝ × X))`;
* bridge/view: the raw-pair/raw-triple formulas transported to those owners through
  `WithLp.ofLp`.

Primitive data:
* the ambient feasible set `Q`;
* the objective and constraint functions `f₀`, `fⱼ`;
* the barrier data `FQ`, `F₀`, `Fⱼ`;
* the scalar upper bound `xiBar`.

Derived API:
* the source-facing barrier formula itself;
* its evaluation lemma;
* the standard-form barrier theorem, which consumes the canonical `L²` pair-owner barrier data on
  the strict epigraphs and realizes the standard-form owner on the canonical `L²` triple space.

This refinement therefore keeps the source-facing barrier formula and domain on the raw textbook
spaces, reuses the strict-epigraph owner from `Theorem_5_3_5` instead of restating its
set-builder, and presents the numbered theorem entirely on the canonical `WithLp.ofLp` owner
surface rather than mixing raw-pair barrier hypotheses with a separate ad hoc triple transport. -/

/-- The strict domain on which the standard-form logarithmic barrier is defined: the ambient
constraint `x ∈ Q`, the strict epigraph inequalities `f₀(x) < ξ` and `fⱼ(x) < κ`, and the two
strict slack inequalities `ξ < ξBar` and `κ < 0`. -/
def functionalConstraintStandardFormBarrierDomain
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (xiBar : ℝ) :
    Set StdPoint :=
  {p | p.1 < xiBar} ∩
    {p | p.2.1 < 0} ∩
    (fun p : StdPoint ↦ p.2.2) ⁻¹' Q ∩
    (fun p : StdPoint ↦ (p.2.2, p.1)) ⁻¹'
      strictConstrainedEpigraph (Set.univ : Set X) f0 ∩
    {p | ∀ j : Fin m,
      p ∈ (fun q : StdPoint ↦ (q.2.2, q.2.1)) ⁻¹'
        strictConstrainedEpigraph (Set.univ : Set X) (fj j)}

/-- Membership in the standard-form barrier domain means that every logarithmic slack is strictly
positive and that the base point lies in `Q`. -/
@[simp] theorem mem_functionalConstraintStandardFormBarrierDomain_iff
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ} {xiBar : ℝ} {p : StdPoint} :
    p ∈ functionalConstraintStandardFormBarrierDomain Q f0 fj xiBar ↔
      p.1 < xiBar ∧
        p.2.1 < 0 ∧
        p.2.2 ∈ Q ∧
        f0 p.2.2 < p.1 ∧
        ∀ j : Fin m, fj j p.2.2 < p.2.1 := by
  simp [functionalConstraintStandardFormBarrierDomain, and_assoc]

/-- Every point of the strict barrier domain is feasible for the closed standard-form
reformulation. -/
theorem functionalConstraintStandardFormBarrierDomain_subset_feasibleSet
    (Q : Set X) (f0 : X → ℝ) (fj : Fin m → X → ℝ) (xiBar : ℝ) :
    functionalConstraintStandardFormBarrierDomain Q f0 fj xiBar ⊆
      (functionalConstraintStandardFormProblem Q f0 fj xiBar).feasibleSet := by
  intro p hp
  rcases mem_functionalConstraintStandardFormBarrierDomain_iff.mp hp with
    ⟨hxi, hkappa, hxQ, hf0, hfj⟩
  exact mem_functionalConstraintStandardFormProblem_feasibleSet_iff.mpr
    ⟨le_of_lt hxi, le_of_lt hkappa, hxQ, le_of_lt hf0, fun j ↦ le_of_lt (hfj j)⟩

/-- The explicit barrier obtained by adding the barrier on `Q`, the epigraph barrier for the
objective, the epigraph barriers for the functional constraints, and the two logarithmic slack
terms for `ξ < ξBar` and `κ < 0`. -/
def functionalConstraintStandardFormBarrier
    (FQ : X → ℝ) (F0 : X × ℝ → ℝ) (Fj : Fin m → X × ℝ → ℝ) (xiBar : ℝ) :
    StdPoint → ℝ :=
  fun p ↦
    FQ p.2.2 +
      F0 (p.2.2, p.1) +
        (∑ j : Fin m, Fj j (p.2.2, p.2.1)) +
          sublevelLogBarrier (fun q : StdPoint ↦ q.1) xiBar p +
            sublevelLogBarrier (fun q : StdPoint ↦ q.2.1) 0 p

/-- Evaluating `functionalConstraintStandardFormBarrier` reproduces the textbook barrier formula
`F_Q(x) + F₀(x, ξ) + ∑ⱼ Fⱼ(x, κ) - log (ξBar - ξ) - log (-κ)`. -/
@[simp]
theorem functionalConstraintStandardFormBarrier_apply
    (FQ : X → ℝ) (F0 : X × ℝ → ℝ) (Fj : Fin m → X × ℝ → ℝ) (xiBar : ℝ)
    (p : StdPoint) :
    functionalConstraintStandardFormBarrier FQ F0 Fj xiBar p =
      FQ p.2.2 +
        F0 (p.2.2, p.1) +
          (∑ j : Fin m, Fj j (p.2.2, p.2.1)) -
            Real.log (xiBar - p.1) - Real.log (-p.2.1) := by
  simp [functionalConstraintStandardFormBarrier, sublevelLogBarrier, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm]

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- Helper for Proposition 5.3.6.2: the canonical `WithLp` bridge from the state owner
`StatePointL2` to the raw pair `(κ, x)`. -/
private def ofStateContinuousAffine : StatePointL2 →ᴬ[ℝ] StatePoint :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ X).toContinuousLinearMap).toContinuousAffineMap

/-- Helper for Proposition 5.3.6.2: evaluating the state bridge recovers `ofStatePoint`. -/
@[simp] private theorem ofStateContinuousAffine_apply (z : StatePointL2) :
    ofStateContinuousAffine z = ofStatePoint z :=
  rfl

/-- Helper for Proposition 5.3.6.2: the canonical `WithLp` bridge from the triple owner to the raw
triple `(ξ, κ, x)`. -/
private def ofStdContinuousAffine : StdPointL2 →ᴬ[ℝ] StdPoint :=
  let raw : StdPointL2 →L[ℝ] (ℝ × StatePointL2) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ StatePointL2).toContinuousLinearMap
  let xi : StdPointL2 →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ StatePointL2).comp raw
  let state : StdPointL2 →L[ℝ] StatePoint :=
    ofStateContinuousAffine.contLinear.comp
      ((ContinuousLinearMap.snd ℝ ℝ StatePointL2).comp raw)
  (xi.prod state).toContinuousAffineMap

/-- Helper for Proposition 5.3.6.2: evaluating the triple bridge recovers `ofStdPoint`. -/
@[simp] private theorem ofStdContinuousAffine_apply (z : StdPointL2) :
    ofStdContinuousAffine z = ofStdPoint z := by
  -- Unfold the bridge and simplify the nested `WithLp` product equivalences.
  change ofStdContinuousAffine z = (z.fst, WithLp.ofLp z.snd)
  simp [ofStdContinuousAffine, ofStateContinuousAffine]

/-- Helper for Proposition 5.3.6.2: a raw pair `(x, t)` can be re-embedded in the canonical
`WithLp` pair owner. -/
private def toPairPointContinuousAffine : PairPoint →ᴬ[ℝ] PairPointL2 :=
  ((WithLp.prodContinuousLinearEquiv 2 ℝ X ℝ).symm.toContinuousLinearMap).toContinuousAffineMap

/-- Helper for Proposition 5.3.6.2: applying `ofPairPoint` after the raw-pair embedding is the
identity. -/
@[simp] private theorem ofPairPoint_toPairPointContinuousAffine_apply (p : PairPoint) :
    ofPairPoint (toPairPointContinuousAffine p) = p := by
  rfl

/-- Helper for Proposition 5.3.6.2: projection of the triple owner to the raw decision variable
`x`. -/
private def xProjectionMap : StdPointL2 →ᴬ[ℝ] X :=
  let xLinear : StdPoint →L[ℝ] X :=
    (ContinuousLinearMap.snd ℝ ℝ X).comp (ContinuousLinearMap.snd ℝ ℝ StatePoint)
  xLinear.toContinuousAffineMap.comp ofStdContinuousAffine

/-- Helper for Proposition 5.3.6.2: the `x`-projection reads off the third raw coordinate. -/
@[simp] private theorem xProjectionMap_apply (z : StdPointL2) :
    xProjectionMap z = (ofStdPoint z).2.2 := by
  -- Expand the projection through the triple bridge and simplify coordinates.
  simp [xProjectionMap]

/-- Helper for Proposition 5.3.6.2: projection of the triple owner to the canonical pair owner
carrying `(x, ξ)`. -/
private def objectivePairMap : StdPointL2 →ᴬ[ℝ] PairPointL2 :=
  let xLinear : StdPoint →L[ℝ] X :=
    (ContinuousLinearMap.snd ℝ ℝ X).comp (ContinuousLinearMap.snd ℝ ℝ StatePoint)
  let xiLinear : StdPoint →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ StatePoint
  toPairPointContinuousAffine.comp
    ((xLinear.prod xiLinear).toContinuousAffineMap.comp ofStdContinuousAffine)

/-- Helper for Proposition 5.3.6.2: the objective-pair projection reads off `(x, ξ)`. -/
@[simp] private theorem objectivePairMap_apply (z : StdPointL2) :
    ofPairPoint (objectivePairMap z) = ((ofStdPoint z).2.2, (ofStdPoint z).1) := by
  -- The objective pair is exactly the `(x, ξ)` coordinate pair of the raw triple.
  simp [objectivePairMap]

/-- Helper for Proposition 5.3.6.2: projection of the triple owner to the canonical pair owner
carrying `(x, κ)`. -/
private def constraintPairMap : StdPointL2 →ᴬ[ℝ] PairPointL2 :=
  let xLinear : StdPoint →L[ℝ] X :=
    (ContinuousLinearMap.snd ℝ ℝ X).comp (ContinuousLinearMap.snd ℝ ℝ StatePoint)
  let kappaLinear : StdPoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ X).comp (ContinuousLinearMap.snd ℝ ℝ StatePoint)
  toPairPointContinuousAffine.comp
    ((xLinear.prod kappaLinear).toContinuousAffineMap.comp ofStdContinuousAffine)

/-- Helper for Proposition 5.3.6.2: the constraint-pair projection reads off `(x, κ)`. -/
@[simp] private theorem constraintPairMap_apply (z : StdPointL2) :
    ofPairPoint (constraintPairMap z) = ((ofStdPoint z).2.2, (ofStdPoint z).2.1) := by
  -- The constraint pair is exactly the `(x, κ)` coordinate pair of the raw triple.
  simp [constraintPairMap]

/-- Helper for Proposition 5.3.6.2: the upper-slack map `ξBar - ξ` viewed as a continuous affine
map on the canonical triple owner. -/
private def xiSlackMap (xiBar : ℝ) : StdPointL2 →ᴬ[ℝ] ℝ :=
  let xiLinear : StdPoint →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ StatePoint
  ((-xiLinear).toContinuousAffineMap.comp ofStdContinuousAffine) +ᵥ
    ContinuousAffineMap.const ℝ StdPointL2 xiBar

/-- Helper for Proposition 5.3.6.2: the upper-slack map evaluates to `ξBar - ξ`. -/
@[simp] private theorem xiSlackMap_apply (xiBar : ℝ) (z : StdPointL2) :
    xiSlackMap xiBar z = xiBar - (ofStdPoint z).1 := by
  -- Normalize the affine translation so the slack is written in textbook form.
  simp [xiSlackMap, sub_eq_add_neg]
  ring

/-- Helper for Proposition 5.3.6.2: the negative-`κ` slack map viewed on the canonical triple
owner. -/
private def kappaSlackMap : StdPointL2 →ᴬ[ℝ] ℝ :=
  let kappaLinear : StdPoint →L[ℝ] ℝ :=
    (ContinuousLinearMap.fst ℝ ℝ X).comp (ContinuousLinearMap.snd ℝ ℝ StatePoint)
  (-kappaLinear).toContinuousAffineMap.comp ofStdContinuousAffine

/-- Helper for Proposition 5.3.6.2: the negative-`κ` slack map evaluates to `-κ`. -/
@[simp] private theorem kappaSlackMap_apply (z : StdPointL2) :
    kappaSlackMap z = -(ofStdPoint z).2.1 := by
  simp [kappaSlackMap]

/-- Helper for Proposition 5.3.6.2: the empty finite family contributes the zero barrier on the
entire triple owner. -/
private theorem zero_isSelfConcordantBarrierOnWith_univ :
    IsSelfConcordantBarrierOnWith (Set.univ : Set StdPointL2) 0
      (fun _ : StdPointL2 ↦ (0 : ℝ)) := by
  have hself :
      IsSelfConcordantOnWith (Set.univ : Set StdPointL2) 0
        (fun _ : StdPointL2 ↦ (0 : ℝ)) := by
    -- Reuse the canonical zero-quadratic self-concordance theorem.
    simpa [quadraticAffineObjective] using
      (quadraticAffineObjective_isSelfConcordantOnWith_zero
        (E := StdPointL2) 0 (0 : StdPointL2) (0 : StdPointL2 →L[ℝ] StdPointL2)
        ContinuousLinearMap.isPositive_zero)
  refine
    { toIsStandardSelfConcordantOn := ?_
      barrier_parameter_bound := ?_ }
  · -- The zero function is the zero quadratic-affine objective on the whole space.
    exact hself.of_le (by norm_num)
  · -- Its barrier parameter is exactly zero because both gradient and Hessian vanish.
    intro x hx u
    have hA :
        IsSelfAdjoint (0 : StdPointL2 →L[ℝ] StdPointL2) := by
      simpa using (IsSelfAdjoint.zero : IsSelfAdjoint (0 : StdPointL2 →L[ℝ] StdPointL2))
    have hgrad :
        gradient (fun _ : StdPointL2 ↦ (0 : ℝ)) = fun _ : StdPointL2 ↦ (0 : StdPointL2) := by
      simpa [quadraticAffineObjective] using
        quadraticAffineObjective_gradient_eq 0 (0 : StdPointL2)
          (0 : StdPointL2 →L[ℝ] StdPointL2) hA
    have hhess :
        hessian (fun _ : StdPointL2 ↦ (0 : ℝ)) x = 0 := by
      simpa [quadraticAffineObjective] using
        quadraticAffineObjective_hessian_eq 0 (0 : StdPointL2)
          (0 : StdPointL2 →L[ℝ] StdPointL2) hA x
    rw [hgrad, hhess]
    simp

/-- Helper for Proposition 5.3.6.2: each functional-constraint epigraph barrier pulls back along
the canonical projection `(ξ, κ, x) ↦ (x, κ)`. -/
private theorem constraint_term_isSelfConcordantBarrierOnWith
    {fj : Fin m → X → ℝ} {Fj : Fin m → X × ℝ → ℝ} {vj : Fin m → NNReal}
    (hFj : ∀ j : Fin m,
      IsSelfConcordantBarrierOnWith
        (ofPairPoint ⁻¹' strictConstrainedEpigraph (Set.univ : Set X) (fj j))
        (vj j) (Fj j ∘ ofPairPoint))
  (j : Fin m) :
    IsSelfConcordantBarrierOnWith
      (ofStdPoint ⁻¹' {p : StdPoint | fj j p.2.2 < p.2.1})
      (vj j)
      (fun z : StdPointL2 ↦ Fj j ((ofStdPoint z).2.2, (ofStdPoint z).2.1)) := by
  -- Pull back the `j`-th pair-owner barrier along the `(x, κ)` projection.
  have hpull :
      IsSelfConcordantBarrierOnWith
        (constraintPairMap ⁻¹'
          (ofPairPoint ⁻¹' strictConstrainedEpigraph (Set.univ : Set X) (fj j)))
        (vj j)
        ((Fj j ∘ ofPairPoint) ∘ constraintPairMap) := by
    simpa using (hFj j).comp_continuousAffineMap constraintPairMap
  -- Normalize the pulled-back domain and formula to the raw textbook coordinates.
  simpa [Set.preimage, Function.comp, mem_strictConstrainedEpigraph_iff] using hpull

/-- Helper for Proposition 5.3.6.2: the finite family `s` imposes exactly those functional
constraints whose indices lie in `s`. -/
private def constraintFamilyDomain
    (fj : Fin m → X → ℝ) (s : Finset (Fin m)) : Set StdPoint :=
  {p : StdPoint | ∀ j : Fin m, j ∈ s → fj j p.2.2 < p.2.1}

/-- Helper for Proposition 5.3.6.2: the finite family of functional-constraint barriers adds over
any finite set of indices. -/
private theorem constraint_sum_isSelfConcordantBarrierOnWith
    {fj : Fin m → X → ℝ} {Fj : Fin m → X × ℝ → ℝ} {vj : Fin m → NNReal}
    (hFj : ∀ j : Fin m,
      IsSelfConcordantBarrierOnWith
        (ofPairPoint ⁻¹' strictConstrainedEpigraph (Set.univ : Set X) (fj j))
        (vj j) (Fj j ∘ ofPairPoint))
    (s : Finset (Fin m)) :
    IsSelfConcordantBarrierOnWith
      (ofStdPoint ⁻¹' constraintFamilyDomain fj s)
      (s.sum vj)
      (fun z : StdPointL2 ↦ s.sum (fun j ↦ Fj j ((ofStdPoint z).2.2, (ofStdPoint z).2.1))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- The empty family has trivial domain and zero barrier term.
      simpa [constraintFamilyDomain] using zero_isSelfConcordantBarrierOnWith_univ (X := X)
  | @insert j s hj hs =>
      -- Add the new `j`-term to the already packaged finite family.
      have hterm := constraint_term_isSelfConcordantBarrierOnWith (hFj := hFj) j
      have hadd := hterm.add hs
      -- Rewrite the finite-family domain and sum into the `Finset.insert` form.
      simpa [constraintFamilyDomain, Finset.sum_insert hj, Finset.mem_insert, Set.preimage,
        and_assoc, and_left_comm, and_comm, forall_or_left] using hadd

/-- Helper for Proposition 5.3.6.2: the logarithmic slack `-\log (ξBar - ξ)` is the affine
pullback of the scalar `-\log` barrier on `(0, ∞)`. -/
private theorem xi_slack_isSelfConcordantBarrierOnWith (xiBar : ℝ) :
    IsSelfConcordantBarrierOnWith
      (ofStdPoint ⁻¹' {p : StdPoint | p.1 < xiBar})
      1
      (fun z : StdPointL2 ↦ -Real.log (xiBar - (ofStdPoint z).1)) := by
  let g : StdPointL2 →ᴬ[ℝ] ℝ := xiSlackMap xiBar
  -- Pull back the scalar `-\log` barrier along the affine slack map `ξBar - ξ`.
  have hpull :
      IsSelfConcordantBarrierOnWith
        (Set.preimage g (Set.Ioi (0 : ℝ)))
        1
        ((fun x : ℝ ↦ -Real.log x) ∘ g) := by
    simpa using
      (IsSelfConcordantBarrierOnWith.comp_continuousAffineMap
        (E := StdPointL2) (E₁ := ℝ)
        negLog_isSelfConcordantBarrierOnWith_nonnegativeRay
        g)
  have hdom :
      Set.preimage g (Set.Ioi (0 : ℝ)) =
        (ofStdPoint ⁻¹' {p : StdPoint | p.1 < xiBar}) := by
    ext z
    simp [g, Set.preimage]
  have hfun :
      ((fun x : ℝ ↦ -Real.log x) ∘ g) =
        (fun z : StdPointL2 ↦ -Real.log (xiBar - (ofStdPoint z).1)) := by
    funext z
    simp [g, Function.comp]
  -- Rewrite the pullback domain and function into the source-facing slack formula.
  simpa [hdom, hfun] using hpull

/-- Helper for Proposition 5.3.6.2: the logarithmic slack `-\log (-κ)` is the affine pullback of
the scalar `-\log` barrier on `(0, ∞)`. -/
private theorem kappa_slack_isSelfConcordantBarrierOnWith :
    IsSelfConcordantBarrierOnWith
      (ofStdPoint ⁻¹' {p : StdPoint | p.2.1 < 0})
      1
      (fun z : StdPointL2 ↦ -Real.log (-(ofStdPoint z).2.1)) := by
  let g : StdPointL2 →ᴬ[ℝ] ℝ := kappaSlackMap
  -- Pull back the scalar `-\log` barrier along the affine slack map `-κ`.
  have hpull :
      IsSelfConcordantBarrierOnWith
        (Set.preimage g (Set.Ioi (0 : ℝ)))
        1
        ((fun x : ℝ ↦ -Real.log x) ∘ g) := by
    simpa using
      (IsSelfConcordantBarrierOnWith.comp_continuousAffineMap
        (E := StdPointL2) (E₁ := ℝ)
        negLog_isSelfConcordantBarrierOnWith_nonnegativeRay
        g)
  have hdom :
      Set.preimage g (Set.Ioi (0 : ℝ)) =
        (ofStdPoint ⁻¹' {p : StdPoint | p.2.1 < 0}) := by
    ext z
    simp [g, Set.preimage]
  have hfun :
      ((fun x : ℝ ↦ -Real.log x) ∘ g) =
        (fun z : StdPointL2 ↦ -Real.log (-(ofStdPoint z).2.1)) := by
    funext z
    simp [g, Function.comp]
  -- Rewrite the pullback domain and function into the source-facing slack formula.
  simpa [hdom, hfun] using hpull

/-- Helper for Proposition 5.3.6.2: the nested intersection of the five component domains and the
nested sum of their five barrier functions normalize to the source-facing standard-form owners. -/
private theorem functionalConstraintStandardFormBarrier_components_eq
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ}
    {FQ : X → ℝ} {F0 : X × ℝ → ℝ} {Fj : Fin m → X × ℝ → ℝ} {xiBar : ℝ} :
    (((((ofStdPoint ⁻¹' {p : StdPoint | p.2.2 ∈ Q}) ∩
        (ofStdPoint ⁻¹' {p : StdPoint | f0 p.2.2 < p.1})) ∩
        (ofStdPoint ⁻¹' {p : StdPoint | ∀ j : Fin m, fj j p.2.2 < p.2.1})) ∩
        (ofStdPoint ⁻¹' {p : StdPoint | p.1 < xiBar})) ∩
        (ofStdPoint ⁻¹' {p : StdPoint | p.2.1 < 0}) =
      ofStdPoint ⁻¹' functionalConstraintStandardFormBarrierDomain Q f0 fj xiBar) ∧
    (((((fun z : StdPointL2 ↦ FQ (ofStdPoint z).2.2) +
        (fun z : StdPointL2 ↦ F0 ((ofStdPoint z).2.2, (ofStdPoint z).1))) +
        (fun z : StdPointL2 ↦ ∑ j : Fin m, Fj j ((ofStdPoint z).2.2, (ofStdPoint z).2.1))) +
        (fun z : StdPointL2 ↦ -Real.log (xiBar - (ofStdPoint z).1))) +
        (fun z : StdPointL2 ↦ -Real.log (-(ofStdPoint z).2.1)) =
      functionalConstraintStandardFormBarrier FQ F0 Fj xiBar ∘ ofStdPoint) := by
  constructor
  · -- The five component inequalities are exactly the defining inequalities of the barrier domain.
    ext z
    simp [mem_functionalConstraintStandardFormBarrierDomain_iff, and_assoc, and_left_comm,
      and_comm]
  · -- Expanding the source-facing barrier formula recovers the nested sum of the five pieces.
    funext z
    simp [functionalConstraintStandardFormBarrier_apply, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm]

-- Proof sketch: view each summand as a self-concordant barrier on the reformulated feasible set:
-- `FQ` is pulled back along the coordinate projection `(ξ, κ, x) ↦ x`, `F₀` is pulled back
-- along `(ξ, κ, x) ↦ (x, ξ)`, and each `Fⱼ` is pulled back along `(ξ, κ, x) ↦ (x, κ)` using the
-- canonical owner theorem `IsSelfConcordantBarrierOnWith.comp_continuousAffineMap`. The two
-- logarithmic
-- slack terms are the standard one-dimensional barriers pulled back from `x ↦ -log x`. Repeated
-- application of `IsSelfConcordantBarrierOnWith.add` then yields the parameter sum
-- `vQ + v₀ + ∑ⱼ vⱼ + 2`.
/-- Proposition 5.3.6.2: if `F_Q` is a self-concordant barrier for `Q`, if `F₀` is a
self-concordant barrier on the canonical `L²` pair owner over the strict epigraph of `f₀`, and
if each `Fⱼ` is a self-concordant barrier on the canonical `L²` pair owner over the strict
epigraph of `fⱼ`, then
`F_Q(x) + F₀(x, ξ) + ∑ⱼ Fⱼ(x, κ) - log (ξBar - ξ) - log (-κ)` is a self-concordant barrier for
the strict reformulated barrier domain `ξ < ξBar`, `κ < 0`, `x ∈ Q`, `f₀(x) < ξ`, `fⱼ(x) < κ`,
which sits inside the closed feasible set of Proposition `5.3.6.1`, with parameter
`v_Q + v₀ + ∑ⱼ vⱼ + 2`, all viewed on the canonical `L²` owners through `WithLp.ofLp`. -/
theorem functionalConstraintStandardFormBarrier_isSelfConcordantBarrierOnWith
    {Q : Set X} {f0 : X → ℝ} {fj : Fin m → X → ℝ}
    {FQ : X → ℝ} {F0 : X × ℝ → ℝ} {Fj : Fin m → X × ℝ → ℝ}
    {xiBar : ℝ} {vQ v0 : NNReal} {vj : Fin m → NNReal}
    (hFQ : IsSelfConcordantBarrierOnWith Q vQ FQ)
    (hF0 : IsSelfConcordantBarrierOnWith
      (ofPairPoint ⁻¹' strictConstrainedEpigraph (Set.univ : Set X) f0)
      v0 (F0 ∘ ofPairPoint))
    (hFj : ∀ j : Fin m,
      IsSelfConcordantBarrierOnWith
        (ofPairPoint ⁻¹' strictConstrainedEpigraph (Set.univ : Set X) (fj j))
        (vj j) (Fj j ∘ ofPairPoint)) :
    IsSelfConcordantBarrierOnWith
      (ofStdPoint ⁻¹'
        functionalConstraintStandardFormBarrierDomain Q f0 fj xiBar)
      (vQ + v0 + (∑ j : Fin m, vj j) + 2)
      (functionalConstraintStandardFormBarrier FQ F0 Fj xiBar ∘ ofStdPoint) := by
  -- Pull the barrier on `Q` back along the coordinate projection `(ξ, κ, x) ↦ x`.
  have hQ :
      IsSelfConcordantBarrierOnWith
        (ofStdPoint ⁻¹' {p : StdPoint | p.2.2 ∈ Q})
        vQ
        (fun z : StdPointL2 ↦ FQ (ofStdPoint z).2.2) := by
    have hpull :
        IsSelfConcordantBarrierOnWith
          (xProjectionMap ⁻¹' Q)
          vQ
          (FQ ∘ xProjectionMap) := by
      simpa using hFQ.comp_continuousAffineMap xProjectionMap
    simpa [Set.preimage, Function.comp] using hpull
  -- Pull the objective epigraph barrier back along `(ξ, κ, x) ↦ (x, ξ)`.
  have h0 :
      IsSelfConcordantBarrierOnWith
        (ofStdPoint ⁻¹' {p : StdPoint | f0 p.2.2 < p.1})
        v0
        (fun z : StdPointL2 ↦ F0 ((ofStdPoint z).2.2, (ofStdPoint z).1)) := by
    have hpull :
        IsSelfConcordantBarrierOnWith
          (objectivePairMap ⁻¹'
            (ofPairPoint ⁻¹' strictConstrainedEpigraph (Set.univ : Set X) f0))
          v0
          ((F0 ∘ ofPairPoint) ∘ objectivePairMap) := by
      simpa using hF0.comp_continuousAffineMap objectivePairMap
    simpa [Set.preimage, Function.comp, mem_strictConstrainedEpigraph_iff] using hpull
  -- Package the finite family of functional-constraint barriers into one barrier theorem.
  have hconstraints :
      IsSelfConcordantBarrierOnWith
        (ofStdPoint ⁻¹' {p : StdPoint | ∀ j : Fin m, fj j p.2.2 < p.2.1})
        (∑ j : Fin m, vj j)
        (fun z : StdPointL2 ↦ ∑ j : Fin m, Fj j ((ofStdPoint z).2.2, (ofStdPoint z).2.1)) := by
    simpa [constraintFamilyDomain] using
      constraint_sum_isSelfConcordantBarrierOnWith (hFj := hFj) Finset.univ
  -- Pull back the two scalar slack barriers for `ξ < ξBar` and `κ < 0`.
  have hxi := xi_slack_isSelfConcordantBarrierOnWith (X := X) xiBar
  have hkappa := kappa_slack_isSelfConcordantBarrierOnWith (X := X)
  -- Add the five component barriers in the same order as the source proof.
  have hsum :=
    (((hQ.add h0).add hconstraints).add hxi).add hkappa
  have hν :
      ((((vQ + v0) + ∑ j : Fin m, vj j) + 1) + 1) =
        vQ + v0 + (∑ j : Fin m, vj j) + 2 := by
    ext
    norm_num [add_assoc]
  rcases
      functionalConstraintStandardFormBarrier_components_eq
        (Q := Q) (f0 := f0) (fj := fj) (FQ := FQ) (F0 := F0) (Fj := Fj) (xiBar := xiBar) with
    ⟨hdom, hfun⟩
  -- Normalize the combined component barrier back to the source-facing standard-form barrier.
  have hsum' :
      IsSelfConcordantBarrierOnWith
        (ofStdPoint ⁻¹' functionalConstraintStandardFormBarrierDomain Q f0 fj xiBar)
        ((((vQ + v0) + ∑ j : Fin m, vj j) + 1) + 1)
        (functionalConstraintStandardFormBarrier FQ F0 Fj xiBar ∘ ofStdPoint) := by
    convert hsum using 1
    · ext z
      simp [functionalConstraintStandardFormBarrierDomain, mem_strictConstrainedEpigraph_iff,
        and_assoc, and_left_comm, and_comm]
    · funext z
      simp [functionalConstraintStandardFormBarrier, sublevelLogBarrier, Function.comp,
        sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  simpa [hν] using hsum'

end FunctionalConstraintStandardFormBarrier
