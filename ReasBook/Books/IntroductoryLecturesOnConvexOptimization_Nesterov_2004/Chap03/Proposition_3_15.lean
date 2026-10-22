/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Set
open EuclideanSpace
open scoped WithTopConvexAnalysis

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 3.15 lies in the chapter's Euclidean coordinatewise-maximum / subdifferential
domain.

Relevant owner-style declarations sampled before refinement:
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`;
- `pointwiseSupremumOn` in `PointwiseSupremumOn` and
  `activePointwiseSupremumOnIndices` in `Lemma_3_1_14`, the chapter owners for pointwise suprema
  and their active-index sets;
- `subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials` in
  `Lemma_3_13`, the finite active-family subdifferential formula.

Best owner abstraction:
- source-facing: Proposition 3.15 as the Euclidean coordinate-family specialization of the finite
  `Set.univ` supremum;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `subdifferential`.

Primitive data:
- the positive-dimension witness `hn : 0 < n`, which supplies the nonempty finite index type
  `Fin n`;
- the coordinate projection family `fun y i ↦ (y i : WithTop ℝ)`.

Derived API:
- the active-coordinate set
  `activePointwiseSupremumOnIndices (Set.univ : Set (Fin n))
    (fun y i ↦ (y i : WithTop ℝ)) x`;
- the convex-hull description of the subdifferential by active basis vectors.

Source/core/bridge triage:
- source-facing: the Euclidean coordinatewise-maximum specialization of Proposition 3.15;
- core/canonical: `pointwiseSupremumOn`, `activePointwiseSupremumOnIndices`, `subdifferential`;
- bridge/view: the coordinate projection family and the active-basis embedding
  `i ↦ EuclideanSpace.single i 1`.

The earlier refinement duplicated the chapter finite-maximum owner with separate public
`coordinatewiseMaximum` and `activeCoordinateIndices` wrappers. This file now states the two
propositions directly on the chapter owners `pointwiseSupremumOn` and
`activePointwiseSupremumOnIndices`, using the source-facing hypothesis `hn : 0 < n` only to
supply the local `Nonempty (Fin n)` instance required by the finite `Set.univ` specialization.
-/

local notation "coordinateFamily" =>
  (fun y : E ↦ fun i ↦ (y i : WithTop ℝ))

section

variable (hn : 0 < n)

local instance instLocalChap03_Proposition_3_151 : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩

/-- Helper for Proposition 3.15: the coordinatewise maximum has full effective domain, so every
point lies in the interior of its domain. -/
lemma coordinatewiseMaximum_interior_dom_eq_univ
    (hn : 0 < n) :
    interior (dom (pointwiseSupremumOn (Set.univ : Set (Fin n)) coordinateFamily)) = Set.univ := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- The finite `Set.univ` supremum is finite exactly when each coordinate slice is finite.
  simpa [withTopEffectiveDomain] using
    (interior_dom_pointwiseSupremumOn_univ (ι := Fin n) (φ := coordinateFamily))

/-- Helper for Proposition 3.15: each coordinate slice has singleton subdifferential equal to the
corresponding standard basis vector. -/
lemma coordinate_slice_subdifferential_eq_singleton_basis
    (i : Fin n) (x : E) :
    ∂ (fun y : E ↦ (y i : WithTop ℝ))(x) = {single i (1 : ℝ)} := by
  have hconv :
      ConvexOn ℝ (dom (fun y : E ↦ (y i : WithTop ℝ)))
        (withTopRealPart (fun y : E ↦ (y i : WithTop ℝ))) := by
    -- The `i`-th coordinate map is linear, hence convex on all of `E`.
    simpa [withTopEffectiveDomain, withTopRealPart] using
      (EuclideanSpace.projₗ i).convexOn convex_univ
  have hgrad :
      HasGradientAt (withTopRealPart (fun y : E ↦ (y i : WithTop ℝ)))
        (single i (1 : ℝ)) x := by
    -- Identify the Fréchet derivative of the coordinate projection with pairing against `e_i`.
    rw [hasGradientAt_iff_hasFDerivAt]
    have hderiv :
        HasFDerivAt (fun y : E ↦ y i) (EuclideanSpace.proj i : E →L[ℝ] ℝ) x := by
      simpa using (EuclideanSpace.proj i : E →L[ℝ] ℝ).hasFDerivAt
    have hdual :
        (EuclideanSpace.proj i : E →L[ℝ] ℝ) =
          InnerProductSpace.toDual ℝ E (single i (1 : ℝ)) := by
      ext y
      simpa using (EuclideanSpace.inner_single_left i (1 : ℝ) y).symm
    simpa [withTopRealPart] using hderiv.congr_fderiv hdual
  have hx : x ∈ interior (dom (fun y : E ↦ (y i : WithTop ℝ))) := by
    -- A real-valued coordinate slice is finite everywhere.
    simp [withTopEffectiveDomain]
  exact subdifferential_eq_singleton_of_hasGradientAt hconv hx hgrad

/-- Helper for Proposition 3.15: each coordinate slice is a closed convex function. -/
lemma coordinate_slice_closedConvexFunction
    (i : Fin n) :
    ClosedConvexFunction (fun y : E ↦ (y i : WithTop ℝ)) := by
  -- Package linearity and continuity of the coordinate projection into the chapter owner API.
  apply closedConvexFunction_coe_of_convexOn_continuous
  · simpa using (EuclideanSpace.projₗ i).convexOn convex_univ
  · simpa using (EuclideanSpace.proj i : E →L[ℝ] ℝ).continuous

/-- Helper for Proposition 3.15: at the origin every coordinate attains the common maximum `0`,
so every index is active. -/
lemma active_coordinateFamily_zero_eq_univ
    (hn : 0 < n) :
    activePointwiseSupremumOnIndices
        (Set.univ : Set (Fin n)) coordinateFamily (0 : E) =
      Set.univ := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  ext i
  -- At `0`, each coordinate slice and the finite supremum both evaluate to `0`.
  rw [mem_activePointwiseSupremumOnIndices_univ_iff, pointwiseSupremumOn_univ_eq_sup']
  simp

/-- Helper for Proposition 3.15: rewriting the active slice-subgradient union replaces each slice
subdifferential by the corresponding basis vector. -/
lemma active_slice_subgradient_set_eq_activeBasisImage
    (x : E) :
    {g | ∃ i : Fin n,
        i ∈ activePointwiseSupremumOnIndices (Set.univ : Set (Fin n)) coordinateFamily x ∧
          g ∈ ∂ (fun y : E ↦ (y i : WithTop ℝ))(x)} =
      ((fun i : Fin n ↦ single i (1 : ℝ)) ''
        activePointwiseSupremumOnIndices (Set.univ : Set (Fin n)) coordinateFamily x) := by
  ext g
  constructor
  · rintro ⟨i, hi, hg⟩
    -- Each active slice contributes only the singleton `{e_i}`.
    rw [coordinate_slice_subdifferential_eq_singleton_basis] at hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact ⟨i, hi, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    -- Conversely, every active basis vector comes from the matching active slice.
    refine ⟨i, hi, ?_⟩
    rw [coordinate_slice_subdifferential_eq_singleton_basis]
    simp

/-- Proposition 3.15: the convex subdifferential of the coordinatewise maximum
`x ↦ max_{1 ≤ i ≤ n} x^{(i)}` is the convex hull of the standard basis vectors indexed by the
active coordinates of `x`. -/
-- Proof sketch: one inclusion writes a convex combination of active basis vectors and checks the
-- subgradient inequality coordinatewise, using that active coordinates realize the maximum at
-- `x`. For the reverse inclusion, test a subgradient against perturbations in coordinate
-- directions to show its coordinates are nonnegative, vanish off the active set, and sum to `1`;
-- this identifies the subgradient as a convex combination of the active basis vectors.
theorem subdifferential_coordinatewiseMaximum_eq_convexHull_activeBasis
    (hn : 0 < n)
    (x : E) :
    ∂ (pointwiseSupremumOn (Set.univ : Set (Fin n)) coordinateFamily)(x) =
      convexHull ℝ
        ((fun i : Fin n ↦ single i (1 : ℝ)) ''
          activePointwiseSupremumOnIndices (Set.univ : Set (Fin n)) coordinateFamily x) := by
  let _ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  -- Route correction: the positivity witness must be explicit in the theorem binder, because the
  -- source theorem specializes a nonempty finite supremum.
  have hx :
      x ∈ interior (dom (pointwiseSupremumOn (Set.univ : Set (Fin n)) coordinateFamily)) := by
    -- The coordinatewise maximum is finite everywhere on `E`.
    rw [coordinatewiseMaximum_interior_dom_eq_univ (hn := hn)]
    simp
  have hmain :=
    subdifferential_pointwiseSupremumOn_univ_eq_convexHull_activeSubdifferentials
      (ι := Fin n) (φ := coordinateFamily)
      (fun i ↦ coordinate_slice_closedConvexFunction i) hx
  -- Rewrite the abstract active slice-subgradient hull to the active basis-vector hull.
  rw [hmain, active_slice_subgradient_set_eq_activeBasisImage]

/-- At the origin, every coordinate is active, so the subdifferential of the coordinatewise
maximum is the convex hull of all standard basis vectors, i.e. the standard simplex in `ℝⁿ`. -/
-- Proof sketch: specialize
-- `subdifferential_coordinatewiseMaximum_eq_convexHull_activeBasis` to `x = 0` and observe that
-- all coordinates of `0` equal the common maximum value `0`, so the active-index set is all of
-- `Fin n`.
theorem subdifferential_coordinatewiseMaximum_zero_eq_convexHull_basis
    (hn : 0 < n)
    :
    ∂ (pointwiseSupremumOn (Set.univ : Set (Fin n)) coordinateFamily)((0 : E)) =
      convexHull ℝ (Set.range fun i : Fin n ↦ single i (1 : ℝ)) := by
  -- Specialize the general active-basis formula at the origin.
  rw [subdifferential_coordinatewiseMaximum_eq_convexHull_activeBasis (hn := hn) (x := (0 : E))]
  -- At `0`, the active set is all of `Fin n`, so the image is the full basis range.
  rw [active_coordinateFamily_zero_eq_univ (hn := hn)]
  simp [Set.image_univ]

end

end
