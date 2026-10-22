/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

variable {ι : Type v} [Fintype ι]
variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-
Proposition 3.27 lies in the chapter's weighted affine-minorant / attained-infimum domain.

Sampled owner-style declarations:
- the mathlib additive and module structure on `E →ᵃ[ℝ] ℝ`, whose canonical owner for the
  aggregated affine model is the finite sum `∑ i, α i • ℓ i`;
- `sampledAffineMinorant` in `Nesterov.Chap03.Proposition_3_26`, the chapter owner for one
  sampled affine minorant in `(y, g, f)` coordinates;
- `sum_smul_sampledAffineMinorant_le` in `Nesterov.Chap03.Proposition_3_26`, the chapter
  lower-bound theorem for the corresponding weighted affine-map sum;
- `IsLeast.csInf_eq` in mathlib, the attained-infimum bridge used by the minimum-form corollary.

Best owner abstraction:
- source-facing: the weighted average of finitely many affine minorants;
- core/canonical: an affine lower model `model : E →ᵃ[ℝ] ℝ` together with its least value on `P`;
- bridge/view: the weighted sum `∑ i, α i • ℓ i`, and the sampled-coordinate API from
  Proposition 3.26 when the affine pieces come from sampled subgradients.

Primitive data:
- a finite index type `ι`;
- weights `α : ι → ℝ`;
- affine minorants `ℓ : ι → E →ᵃ[ℝ] ℝ`;
- an affine lower model `model : E →ᵃ[ℝ] ℝ`;
- the feasible set `P` and objective `f`.

Derived API:
- the aggregated model `∑ i, α i • ℓ i`;
- its feasible-value image `((∑ i, α i • ℓ i) '' P)`;
- the attained-infimum identity from `IsLeast.csInf_eq`.

Source/core/bridge triage:
- source-facing: Proposition 3.27's approximate-optimality estimate for a weighted affine lower
  model;
- core/canonical: the attained affine lower-model theorem stated for
  `model : E →ᵃ[ℝ] ℝ`;
- bridge/view: the weighted-sum specialization and the corollary that rewrites the `sInf` bound
  using an attained minimum of `f`.

The previous version introduced a second public wrapper for the affine-map sum itself. That
wrapper carried no extra mathematics beyond the canonical affine-map sum, and it kept redundant
`Fin (N + 1)` indexing, strict-positivity assumptions, and feasibility guards that do not affect
the statements. This refinement also separates the primitive affine lower model from the derived
weighted presentation: the core theorem now works directly with the affine-map owner, and the
weighted statements are thin bridge lemmas over an arbitrary finite index type.
-/

/-- Evaluating a finite weighted sum of affine maps gives the corresponding weighted sum of their
pointwise values. -/
theorem sum_smul_affine_apply
    (α : ι → ℝ) (ℓ : ι → E →ᵃ[ℝ] ℝ) (x : E) :
    (∑ i, α i • ℓ i) x = ∑ i, α i * ℓ i x := by
  classical
  let s : Finset ι := Finset.univ
  change (s.sum fun i ↦ α i • ℓ i) x = s.sum fun i ↦ α i * ℓ i x
  clear_value s
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert i s his ih =>
      simp [his, ih, smul_eq_mul]

/-- If an affine lower model `model` lies below `f` on the feasible set `P`, then any point whose
objective value is within `rN` of the least feasible value of `model` is within `rN` of the
infimum of `f` over `P`. -/
-- Proof sketch: every feasible value of `model` is a lower bound for the corresponding feasible
-- value of `f`. If `xAgg` attains the least feasible value of `model`, then `model xAgg` is a
-- lower bound for the entire image `f '' P`, hence for `sInf (f '' P)`. Combine that lower bound
-- with `f xN ≤ model xAgg + rN`.
theorem approximate_optimality_of_affineModel
    {P : Set E} {f : E → ℝ} (model : E →ᵃ[ℝ] ℝ)
    (h_lower : ∀ x, x ∈ P → model x ≤ f x)
    {xAgg xN : E} {rN : ℝ}
    (hmodel_min : IsLeast (model '' P) (model xAgg))
    (happrox : f xN ≤ model xAgg + rN) :
    f xN ≤ sInf (f '' P) + rN := by
  obtain ⟨x₀, hx₀, _⟩ := hmodel_min.1
  have h_nonempty : Set.Nonempty (f '' P) := ⟨f x₀, ⟨x₀, hx₀, rfl⟩⟩
  have hmodel_le_sInf : model xAgg ≤ sInf (f '' P) := by
    refine le_csInf h_nonempty ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (hmodel_min.2 ⟨x, hx, rfl⟩).trans (h_lower x hx)
  calc
    f xN ≤ model xAgg + rN := happrox
    _ ≤ sInf (f '' P) + rN := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left hmodel_le_sInf rN

/-- Proposition 3.27: if affine minorants `ℓ i` lie below `f` on the feasible set `P`, then any
point whose objective value is within `rN` of a minimizer of their weighted sum is within `rN` of
the infimum of `f` over `P`. -/
-- Proof sketch: the weighted sum `∑ i, α i • ℓ i` also lies below `f` on `P`, because evaluating
-- that affine map gives `∑ i, α i * ℓ i x`, each summand is bounded by `α i * f x`, and
-- `∑ i, α i = 1`. Since `xAgg` minimizes the weighted sum on `P`, the model value at `xAgg`
-- is a lower bound for every value in `f '' P`, hence also for `sInf (f '' P)`. Combine that
-- lower bound with the assumed estimate `f xN ≤ (∑ i, α i • ℓ i) xAgg + rN`.
theorem approximate_optimality_of_sum_smul_affine
    {P : Set E} {f : E → ℝ}
    (α : ι → ℝ) (ℓ : ι → E →ᵃ[ℝ] ℝ)
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1)
    (h_lower : ∀ i x, x ∈ P → ℓ i x ≤ f x)
    {xAgg xN : E} {rN : ℝ}
    (hagg_min : IsLeast (((∑ i, α i • ℓ i : E →ᵃ[ℝ] ℝ) '' P)) ((∑ i, α i • ℓ i) xAgg))
    (happrox : f xN ≤ (∑ i, α i • ℓ i) xAgg + rN) :
    f xN ≤ sInf (f '' P) + rN := by
  have h_model_lower :
      ∀ x, x ∈ P → (∑ i, α i • ℓ i) x ≤ f x := by
    intro x hx
    calc
      (∑ i, α i • ℓ i) x = ∑ i, α i * ℓ i x := sum_smul_affine_apply α ℓ x
      _ ≤ ∑ i, α i * f x := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact mul_le_mul_of_nonneg_left (h_lower i x hx) (hα_nonneg i)
      _ = (∑ i, α i) * f x := by rw [Finset.sum_mul]
      _ = f x := by rw [hα_sum, one_mul]
  exact
    approximate_optimality_of_affineModel
      (∑ i, α i • ℓ i) h_model_lower hagg_min happrox

/-- If the feasible objective `f` attains its minimum on `P`, an approximate minimizer of any
affine lower model with attained least feasible value is within `rN` of that minimum value. -/
-- Proof sketch: apply `approximate_optimality_of_affineModel` to obtain the bound by
-- `sInf (f '' P) + rN`, then rewrite `sInf (f '' P)` as `f xStar` via `IsLeast.csInf_eq`.
theorem approximate_optimality_of_affineModel_of_hasMinimum
    {P : Set E} {f : E → ℝ} (model : E →ᵃ[ℝ] ℝ)
    (h_lower : ∀ x, x ∈ P → model x ≤ f x)
    {xAgg xN xStar : E} {rN : ℝ}
    (hmodel_min : IsLeast (model '' P) (model xAgg))
    (happrox : f xN ≤ model xAgg + rN)
    (hf_min : IsLeast (f '' P) (f xStar)) :
    f xN ≤ f xStar + rN := by
  simpa [hf_min.csInf_eq] using
    approximate_optimality_of_affineModel model h_lower hmodel_min happrox

/-- If the feasible objective `f` attains its minimum on `P`, the weighted affine-model estimate
gives the corresponding bound above the minimum value of `f`. -/
-- Proof sketch: apply `approximate_optimality_of_sum_smul_affine` to obtain the bound by
-- `sInf (f '' P) + rN`, then rewrite `sInf (f '' P)` as `f xStar` via `IsLeast.csInf_eq`.
theorem approximate_optimality_of_sum_smul_affine_of_hasMinimum
    {P : Set E} {f : E → ℝ}
    (α : ι → ℝ) (ℓ : ι → E →ᵃ[ℝ] ℝ)
    (hα_nonneg : ∀ i, 0 ≤ α i) (hα_sum : ∑ i, α i = 1)
    (h_lower : ∀ i x, x ∈ P → ℓ i x ≤ f x)
    {xAgg xN xStar : E} {rN : ℝ}
    (hagg_min : IsLeast (((∑ i, α i • ℓ i : E →ᵃ[ℝ] ℝ) '' P)) ((∑ i, α i • ℓ i) xAgg))
    (happrox : f xN ≤ (∑ i, α i • ℓ i) xAgg + rN)
    (hf_min : IsLeast (f '' P) (f xStar)) :
    f xN ≤ f xStar + rN := by
  simpa [hf_min.csInf_eq] using
    approximate_optimality_of_sum_smul_affine
      α ℓ hα_nonneg hα_sum h_lower hagg_min happrox

end
