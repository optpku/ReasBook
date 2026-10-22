/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology
open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Lemma 1.9.5 lies in first-order optimality over affine search spaces in a real Hilbert space.

Sampled owner declarations in this domain:
* `posTangentConeAt` and `mem_posTangentConeAt_of_frequently_mem`;
* `AffineSubspace.vadd_mem_of_mem_direction`;
* `gradientMethod`, whose chapter owner abstraction already lives on a real inner-product space;
* `gradient_mem_adjoint_range_of_isLocalMinOn_linearLevelSet`, which exposes the same first-order
  optimality pattern with only pointwise differentiability;
* `IsLocalMinOn.hasFDerivWithinAt_eq_zero`;
* `AffineSubspace.mk'` and `AffineSubspace.direction_mk'`.

Best owner abstraction:
* an affine subspace `s : AffineSubspace ℝ E` together with its direction `s.direction`,
  viewed through the canonical tangent-cone/Fermat optimality API.

Primitive data:
* the objective `f` and the trajectory `x`;
* differentiability of `f` at the iterates where the displayed gradients occur;
* for each positive stage `k`, the feasibility/minimizer datum on the affine search space.

Derived API:
* the owner-side fact that `∇ f (x k)` is orthogonal to every vector in the direction of the
  stage-`k` affine search space;
* the source-facing pairwise orthogonality of distinct trajectory gradients.

Source/core/bridge triage:
* source-facing: pairwise orthogonality of distinct gradients along the trajectory;
* core/canonical: first-order optimality on an affine subspace `s` via `posTangentConeAt`, and
  the owner theorem for a family `searchSpace : ℕ → AffineSubspace ℝ E`;
* bridge/view: specialization of the owner statement to the textbook search space
  `x₀ + span {∇ f(x₀), …, ∇ f(xₖ₋₁)}`.
-/

/-- If `x` minimizes `f` on an affine subspace `s`, then the gradient at `x` is orthogonal to
every vector in the direction of `s`. -/
theorem inner_gradient_eq_zero_of_mem_direction_of_isMinOn_affineSubspace
    {f : E → ℝ} {x : E} {s : AffineSubspace ℝ E}
    (hf : DifferentiableAt ℝ f x) (hx : x ∈ s) (hmin : IsMinOn f (s : Set E) x)
    {v : E} (hv : v ∈ s.direction) :
    inner ℝ (∇ f x) v = 0 := by
  have hv_eventually :
      ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • v ∈ (s : Set E) := by
    filter_upwards with t
    simpa [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction (s.direction.smul_mem t hv) hx
  have hv_pos :
      v ∈ posTangentConeAt (s : Set E) x := by
    exact mem_posTangentConeAt_of_frequently_mem hv_eventually.frequently
  have hnegv_eventually :
      ∀ᶠ t : ℝ in 𝓝[>] 0, x + t • (-v) ∈ (s : Set E) := by
    filter_upwards with t
    simpa [vadd_eq_add, add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction
        (s.direction.smul_mem t (Submodule.neg_mem _ hv)) hx
  have hnegv_pos :
      -v ∈ posTangentConeAt (s : Set E) x := by
    exact mem_posTangentConeAt_of_frequently_mem hnegv_eventually.frequently
  have hderiv :
      (fderiv ℝ f x : E →L[ℝ] ℝ) v = 0 := by
    exact
      hmin.localize.hasFDerivWithinAt_eq_zero
        hf.hasFDerivAt.hasFDerivWithinAt hv_pos hnegv_pos
  simpa [hf.hasGradientAt.fderiv_apply] using hderiv

/-- If each positive stage `x k` minimizes `f` on an affine search space `searchSpace k`, and
every earlier gradient lies in the direction of every later search space, then gradients at
distinct stages are orthogonal. -/
-- Proof sketch: for `a < b`, apply first-order optimality on the stage-`b` affine subspace to the
-- direction vector `∇ f (x a)`. The reverse order is the same identity after commuting the real
-- inner product.
theorem gradients_pairwise_orthogonal_of_isMinOn_affineSearchSpaces
    (f : E → ℝ) (x : ℕ → E) (searchSpace : ℕ → AffineSubspace ℝ E)
    (hdiff : ∀ k : ℕ, DifferentiableAt ℝ f (x k))
    (hdir : ∀ {a b : ℕ}, a < b → ∇ f (x a) ∈ (searchSpace b).direction)
    (hmin : ∀ k : ℕ, 0 < k →
      x k ∈ searchSpace k ∧ IsMinOn f (searchSpace k : Set E) (x k))
    {k i : ℕ} (hki : k ≠ i) :
    inner ℝ (∇ f (x k)) (∇ f (x i)) = 0 := by
  have hlt : ∀ {a b : ℕ}, a < b → inner ℝ (∇ f (x b)) (∇ f (x a)) = 0 := by
    intro a b hab
    have hbmin := hmin b (Nat.zero_lt_of_lt hab)
    exact
      inner_gradient_eq_zero_of_mem_direction_of_isMinOn_affineSubspace
        (hdiff b) hbmin.1 hbmin.2 (hdir hab)
  rcases lt_or_gt_of_ne hki with hki | hki
  · simpa [real_inner_comm] using hlt hki
  · exact hlt hki

/-- Lemma 1.9.5: if each iterate `xₖ` with `k > 0` lies in and minimizes `f` on the affine
subspace `x₀ + span {∇ f(x₀), …, ∇ f(xₖ₋₁)}`, then the gradients at distinct iterates are
orthogonal. -/
-- Proof sketch: specialize
-- `gradients_pairwise_orthogonal_of_isMinOn_affineSearchSpaces` to the textbook search space
-- `x₀ + span {∇ f(x₀), …, ∇ f(xₖ₋₁)}`, where membership of earlier gradients in the later search
-- directions is the tautological `Submodule.subset_span` fact.
theorem gradients_pairwise_orthogonal_of_isMinOn_affineSpan_gradients
    (f : E → ℝ) (x : ℕ → E)
    (hdiff : ∀ k : ℕ, DifferentiableAt ℝ f (x k))
    (hmin : ∀ k : ℕ, 0 < k →
      let searchSpace : AffineSubspace ℝ E :=
        AffineSubspace.mk' (x 0)
          (Submodule.span ℝ (Set.range fun j : Fin k ↦ ∇ f (x j)))
      x k ∈ searchSpace ∧ IsMinOn f (searchSpace : Set E) (x k))
    {k i : ℕ} (hki : k ≠ i) :
    inner ℝ (∇ f (x k)) (∇ f (x i)) = 0 := by
  let searchSpace : ℕ → AffineSubspace ℝ E := fun k ↦
      AffineSubspace.mk' (x 0)
        (Submodule.span ℝ (Set.range fun j : Fin k ↦ ∇ f (x j)))
  have hdir : ∀ {a b : ℕ}, a < b → ∇ f (x a) ∈ (searchSpace b).direction := by
    intro a b hab
    simpa [searchSpace] using
      (Submodule.subset_span ⟨⟨a, hab⟩, rfl⟩ :
        ∇ f (x a) ∈ Submodule.span ℝ (Set.range fun j : Fin b ↦ ∇ f (x j)))
  have hmin' : ∀ k : ℕ, 0 < k →
      x k ∈ searchSpace k ∧ IsMinOn f (searchSpace k : Set E) (x k) := by
    intro k hk
    simpa [searchSpace] using hmin k hk
  exact
    gradients_pairwise_orthogonal_of_isMinOn_affineSearchSpaces
      f x searchSpace hdiff hdir hmin' hki
