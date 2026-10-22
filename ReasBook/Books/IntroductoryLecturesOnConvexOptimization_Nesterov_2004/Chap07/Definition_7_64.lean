/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [SMul ℝ E]

local notation "P" => ℝ × E

/- Definition 7.64 lies in the chapter's perspective-transform / logarithmic-penalty domain.

Sampled owner-style declarations:
- `perspectiveTransform` in `Chap03/Remark_3_1_2_3`, the project owner for the scaled-input term
  `(τ, x) ↦ τ f (τ⁻¹ • x)` on the ambient pair space `ℝ × E`;
- `perspectiveTransform_apply_of_pos` in `Chap03/Remark_3_1_2_3`, the canonical evaluation bridge
  on the positive slice `τ > 0`;
- `Definition_7_5`, which already refines Chapter 7 perspective formulas to that same owner on
  `ℝ × E`;
- `logarithmicTransform` in `Definition_7_62`, the nearby owner for the additive `log` term.

Best owner abstraction:
- source-facing: the dual objective `η`;
- core/canonical: the ambient pair type `ℝ × E` together with the admissibility predicate
  `0 < τ ∧ τ⁻¹ • v ∈ Ω`;
- bridge/view: the coordinate evaluation theorem below.

Primitive data:
- the set `Ω : Set E`;
- the dual function `ψ⋆ : Ω → ℝ`;
- an admissible ambient pair `(τ, v)` with `0 < τ` and `τ⁻¹ • v ∈ Ω`.

Derived API:
- the objective value `η(τ, v) = -1 - log τ + τ ψ⋆(τ⁻¹ • v)`;
- the coordinate evaluation theorem.

Source/core/bridge triage:
- source-facing: `dualObjectiveViaPerspectiveTransform`;
- core/canonical: the ambient owner `P = ℝ × E` with its admissible subtype;
- bridge/view: `dualObjectiveViaPerspectiveTransform_apply`.

The previous file introduced a bespoke structure `PerspectiveDualVector` whose fields were only the
ambient pair coordinates together with the admissibility proof. That is duplicate packaging: the
mathematics already lives on the canonical pair owner `ℝ × E`, and the only extra data is the
predicate that the pair is admissible for `ψ⋆`.
-/

/-- Definition 7.64: for a dual vector `w = (τ, v)` with `τ > 0` and `τ⁻¹ • v ∈ Ω`, the dual
objective via the perspective transform of `ψ⋆ : Ω → ℝ` is
`η(w) = -1 - log τ + τ ψ⋆(τ⁻¹ • v)`. -/
def dualObjectiveViaPerspectiveTransform
    {Ω : Set E} (ψStar : Ω → ℝ) :
    {w : P // 0 < w.1 ∧ w.1⁻¹ • w.2 ∈ Ω} → ℝ
  | ⟨(τ, v), ⟨_, hmem⟩⟩ => -1 - Real.log τ + τ * ψStar ⟨τ⁻¹ • v, hmem⟩

/-- Expanding `dualObjectiveViaPerspectiveTransform` at an admissible dual vector gives the
textbook formula for `η(τ, v)`. -/
theorem dualObjectiveViaPerspectiveTransform_def
    {Ω : Set E} (ψStar : Ω → ℝ) (τ : ℝ) (v : E)
    (hτ : 0 < τ) (hmem : τ⁻¹ • v ∈ Ω) :
    dualObjectiveViaPerspectiveTransform ψStar ⟨(τ, v), ⟨hτ, hmem⟩⟩ =
      -1 - Real.log τ + τ * ψStar ⟨τ⁻¹ • v, hmem⟩ :=
  rfl

/-- Evaluating `dualObjectiveViaPerspectiveTransform` at an admissible dual vector recovers the
formula `-1 - log τ + τ ψ⋆(τ⁻¹ • v)`. -/
@[simp] theorem dualObjectiveViaPerspectiveTransform_apply
    {Ω : Set E} (ψStar : Ω → ℝ) (τ : ℝ) (v : E)
    (hτ : 0 < τ) (hmem : τ⁻¹ • v ∈ Ω) :
    dualObjectiveViaPerspectiveTransform ψStar ⟨(τ, v), ⟨hτ, hmem⟩⟩ =
      -1 - Real.log τ + τ * ψStar ⟨τ⁻¹ • v, hmem⟩ :=
  dualObjectiveViaPerspectiveTransform_def ψStar τ v hτ hmem
