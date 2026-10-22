/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_56

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {E₁ : Type v}
variable {P : Set E} {Ω : Set E₁}

/- Definition 7.63 lies in the chapter's saddle-slice / primal-dual value domain.

Mandatory domain-style sampling before refinement:
- `SaddlePointRepresentation` and `SaddlePointRepresentation.objective_eq` in
  `Chap07/Definition_7_59`, the attained-inner-minimum owner for saddle representations;
- `partialInfProjection` in `Chap03/Theorem_3_1_2_3`, the canonical owner of unconstrained
  fiberwise infima in `EReal`;
- `maximalValueOn` in `Chap07/Definition_7_56`, the chapter owner of maximization values in
  `EReal`;
- `StructuredObjectiveModel.objective` and `StructuredObjectiveModel.adjointObjective` in
  `Chap06/Definition_6_6`, the nearby saddle-slice owners for `sup` and `inf` values.

Best owner abstraction:
- source-facing: the primal and dual slice-value owners attached to a raw saddle map `Ψ₀`;
- core/canonical: `partialInfProjection (Set.univ : Set (P × Ω))` for the primal infimum and
  `maximalValueOn (Set.univ : Set P)` for the dual supremum;
- bridge/view: the `sInf` / `sSup` slice-expansion theorems below.

Primitive data:
- the saddle map `Ψ₀ : Ω → P → ℝ`.

Derived API:
- the faithful `EReal`-valued primal objective `saddlePointObjective Ψ₀`;
- the faithful `EReal`-valued dual function `saddlePointDualFunction Ψ₀`.

Source/core/bridge triage:
- source-facing: the two slice-value functions from Definition 7.63;
- core/canonical: `partialInfProjection` and `maximalValueOn` at the faithful `EReal` layer;
- bridge/view: the evaluation lemmas below.

Definition 7.63 does not assume the inner minima are attained, so the stronger Chapter 7 owner
`SaddlePointRepresentation` from Definition 7.59 is not the main entry here. The previous public
definitions recreated raw real-valued `sInf` / `sSup` slice functions, which loses the chapter's
faithful treatment of empty or unbounded fibers. This refinement keeps the source-facing names but
places them directly on the canonical `EReal` owners `partialInfProjection` and
`maximalValueOn`; the textbook slice formulas remain only as expansion theorems.
-/

/-- Definition 7.63 (1): for a saddle-function model `Ψ₀ : Ω × P → ℝ`, the associated primal
objective is the lower value `ψ(x) = inf_{u ∈ Ω} Ψ₀(u, x)`, formalized through the canonical
infimal-projection owner on `EReal` so empty or unbounded-below slices are represented
faithfully. -/
def saddlePointObjective (Ψ₀ : Ω → P → ℝ) : P → EReal :=
  partialInfProjection (Set.univ : Set (P × Ω))
    (fun z : P × Ω ↦ (Ψ₀ z.2 z.1 : EReal))

-- Proof sketch: unfold `saddlePointObjective`; this is exactly the unconstrained
-- `partialInfProjection` of the `EReal`-valued saddle map on `P × Ω`.
/-- Expanding `saddlePointObjective` identifies it with the chapter's canonical infimal-projection
owner on the unconstrained product domain `P × Ω`. -/
theorem saddlePointObjective_def (Ψ₀ : Ω → P → ℝ) :
    saddlePointObjective Ψ₀ =
      partialInfProjection (Set.univ : Set (P × Ω))
        (fun z : P × Ω ↦ (Ψ₀ z.2 z.1 : EReal)) :=
  rfl

-- Proof sketch: unfold `saddlePointObjective`, then apply
-- `partialInfProjection_eq_sInf` and identify the corresponding fiber with the range of
-- `fun u ↦ (Ψ₀ u x : EReal)`.
/-- Evaluating `saddlePointObjective Ψ₀` at `x` gives the infimum of the `u`-slice of `Ψ₀`
over `Ω`, viewed in `EReal`. -/
@[simp] theorem saddlePointObjective_apply (Ψ₀ : Ω → P → ℝ) (x : P) :
    saddlePointObjective Ψ₀ x = sInf (Set.range fun u : Ω ↦ (Ψ₀ u x : EReal)) := by
  rw [saddlePointObjective_def, partialInfProjection_eq_sInf]
  congr 1
  ext y
  constructor
  · rintro ⟨⟨x', u⟩, hz, rfl⟩
    simp only [Set.mem_univ, true_and] at hz
    rcases hz with ⟨_, rfl⟩
    exact ⟨u, rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨⟨x, u⟩, by simp, rfl⟩

/-- Definition 7.63 (2): for a saddle-function model `Ψ₀ : Ω × P → ℝ`, the associated dual
function is the upper value `ψ⋆(u) = sup_{x ∈ P} Ψ₀(u, x)`, formalized through the Chapter 7
maximal-value owner on `EReal` so empty or unbounded-above slices are represented faithfully. -/
def saddlePointDualFunction (Ψ₀ : Ω → P → ℝ) : Ω → EReal :=
  fun u ↦ maximalValueOn (Set.univ : Set P) (Ψ₀ u)

-- Proof sketch: unfold `saddlePointDualFunction`; this is exactly the chapter's canonical
-- maximization owner applied to each `u`-slice on the unconstrained set `P`.
/-- Expanding `saddlePointDualFunction` identifies it with the chapter's canonical maximal-value
owner applied to each primal slice of the saddle map. -/
theorem saddlePointDualFunction_def (Ψ₀ : Ω → P → ℝ) :
    saddlePointDualFunction Ψ₀ = fun u ↦ maximalValueOn (Set.univ : Set P) (Ψ₀ u) :=
  rfl

-- Proof sketch: unfold `saddlePointDualFunction`, then use
-- `maximalValueOn_eq_sSup_image` and simplify the image of `Set.univ` to the range of
-- `fun x ↦ (Ψ₀ u x : EReal)`.
/-- Evaluating `saddlePointDualFunction Ψ₀` at `u` gives the supremum of the `x`-slice of `Ψ₀`
over `P`, viewed in `EReal`. -/
@[simp] theorem saddlePointDualFunction_apply (Ψ₀ : Ω → P → ℝ) (u : Ω) :
    saddlePointDualFunction Ψ₀ u = sSup (Set.range fun x : P ↦ (Ψ₀ u x : EReal)) := by
  simp [saddlePointDualFunction, maximalValueOn_eq_sSup_image]

end
