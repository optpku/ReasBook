/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_18

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {m k : ℕ}
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Definition 3.79 lies in the complete-data finite max-affine model domain on a real
inner-product space. The textbook `ℝⁿ` case is recovered by
`E := EuclideanSpace ℝ (Fin n)`.

Sampled owner-style declarations:
- `maxTypeObjective` in `Chap02/Lemma_2_18`, the project owner for pointwise maxima of nonempty
  finite families;
- `maxTypeObjective_apply` in `Chap02/Lemma_2_18`, the bridge exposing the finite-maximum
  formula;
- `nonsmoothModel` in `Chap03/Lemma_3_3_2`, the sampled single-function max-affine owner;
- `nonsmoothModel_apply` in `Chap03/Lemma_3_3_2`, its pointwise bridge.

Best owner abstraction:
- `maxTypeObjective`.

Primitive data:
- the component family `f : Fin m → E → ℝ`;
- the sampled points `xSample : Fin (k + 1) → E`;
- the chosen vectors `subgradient : Fin (k + 1) → Fin m → E`.

Derived API:
- the complete model `completeModel f xSample subgradient`, expressed as the finite maximum over
  the canonical product index `Fin (k + 1) × Fin m` through `maxTypeObjective`;
- the explicit pair-indexed `Finset.sup'` expansion from `completeModel_apply`.

Source/core/bridge triage:
- source-facing: `completeModel f xSample subgradient`;
- core/canonical: `maxTypeObjective`;
- bridge/view: `completeModel_apply`.

The nearby owner `nonsmoothModel` is not exact here: Definition 3.79 carries a genuine two-indexed
family of affine minorants `fᵢ(xⱼ) + ⟪gᵢ(xⱼ), x - xⱼ⟫`, not a single function with one sampled
slope at each point. The source-facing construction is therefore kept, but its finite-maximum
structure is expressed directly through the project owner `maxTypeObjective` on the product index
of sampled pairs rather than through an extra nested local max layer. The ambient space is kept at
the owner level of a real inner-product space because the definition uses only affine minorants
and `inner ℝ`, not coordinates.
-/

section

variable [NeZero m] (f : Fin m → E → ℝ) (xSample : Fin (k + 1) → E)
variable (subgradient : Fin (k + 1) → Fin m → E)

/-- Definition 3.79: for a nonempty finite family `f₁, …, f_m`, sample points `x₀, …, x_k`,
and chosen vectors `g_i(x_j)`, the complete model is the maximum over all sampled affine
minorants `f_i(x_j) + ⟪g_i(x_j), x - x_j⟫`. The associated pointwise maximum function
`\bar f(x) = max_i f_i(x)` is already the owner `maxTypeObjective f`. -/
abbrev completeModel : E → ℝ :=
  maxTypeObjective fun ji : Fin (k + 1) × Fin m ↦
    fun x ↦
      f ji.2 (xSample ji.1) + inner ℝ (subgradient ji.1 ji.2) (x - xSample ji.1)

/-- The complete model is exactly the finite maximum of the sampled affine minorants indexed by
all pairs `(j, i)` of samples and components. -/
theorem completeModel_apply (x : E) :
    completeModel f xSample subgradient x =
      Finset.univ.sup' Finset.univ_nonempty
        (fun ji : Fin (k + 1) × Fin m ↦
          f ji.2 (xSample ji.1) + inner ℝ (subgradient ji.1 ji.2) (x - xSample ji.1)) :=
  maxTypeObjective_apply _ x

end

end
