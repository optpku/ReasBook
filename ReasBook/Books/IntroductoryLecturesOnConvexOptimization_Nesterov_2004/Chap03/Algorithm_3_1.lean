/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_35
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_40
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_28

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "e[" i "]" => EuclideanSpace.single i (1 : ℝ)

/- Primary domain: Nemirovski hard-instance active-set selection together with the chapter's
first-order oracle and answer-map shapes.

Sampled owner-style declarations:
* `f_k`
* `first_k_coordinate_max`
* `FirstKIndex`, `firstKCoordinateFamily`
* `activePointwiseSupremumOnIndices`
* `FirstOrderOracle` in `Nesterov.Chap03.Definition_3_40`
* `subdifferential_f_k_eq_affineImage_convexHull_activeBasis` in
  `Nesterov.Chap03.Proposition_3_28`
* the direct first-order answer-map shape `E → ℝ × E` recalled in
  `Nesterov.Chap01.Definition_1_2_9`

Best owner abstraction:
* source-facing owner: the direct answer map `E → ℝ × E` sending `x` to the hard-instance value
  and the chosen subgradient;
* core/canonical: the nonnegative-parameter owner
  `FirstOrderOracle (f_k n k μ γ)` together with `f_k`,
  `first_k_coordinate_max`, `firstKCoordinateFamily`, `activePointwiseSupremumOnIndices`, and
  `subdifferential_f_k_eq_affineImage_convexHull_activeBasis`;
* bridge/view: the least-active-index choice inside the active-index set of the restricted
  coordinate family, plus the pair-valued answer map induced by the owner oracle.

Primitive data:
* the least active index map `resistingOracleIndex : E → FirstKIndex n k`
* the chosen subgradient field
  `resistingSubgradient : E → E`

Derived API:
* the owner oracle
  `resistingFirstOrderOracle : 0 ≤ μ → 0 ≤ γ → FirstOrderOracle (f_k n k μ γ)`
* the source-facing answer map `resistingOracle : E → ℝ × E`

Source/core/bridge triage:
* `source-facing`: `resistingOracle`
* `core/canonical`: `resistingFirstOrderOracle`, `f_k`, `first_k_coordinate_max`,
  `firstKCoordinateFamily`, `activePointwiseSupremumOnIndices`
* `bridge/view`: `resistingOracleIndex`, `resistingSubgradient`, and the pair-valued reply
  obtained from the owner oracle

This file therefore derives the finite choice mechanism internally from
`activePointwiseSupremumOnIndices (Set.univ : Set (FirstKIndex n k))
  (firstKCoordinateFamily n k) x`
instead of rebuilding a private `Fin k` prefix model. It reuses the chapter owner
`FirstOrderOracle` only at the nonnegative-parameter subgradient-validity layer supplied by
Proposition 3.28, takes the chosen vector field as primitive data, and keeps the textbook
pair-valued reply as the source-facing bridge `E → ℝ × E`. -/

/-- At least one prefix index attains the maximum among the first `k` coordinates. -/
-- Proof sketch: a finite supremum over a nonempty finite set is attained by some element of that
-- set.
private theorem activePrefixIndices_nonempty
    (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (x : E) :
    letI : Nonempty (FirstKIndex n k) := firstKIndex_nonempty hk hkn
    (activePointwiseSupremumOnIndices
      (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x).Nonempty := by
  letI : Nonempty (FirstKIndex n k) := firstKIndex_nonempty hk hkn
  -- Reuse the Proposition 3.28 attainment lemma in the local instance shape expected here.
  simpa using active_prefix_indices_nonempty (n := n) (k := k) hk hkn x

/-- The resisting oracle chooses the least active index, matching the scan order of the textbook
algorithm. -/
def resistingOracleIndex
    (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) : E → FirstKIndex n k := fun x ↦
  letI : Nonempty (FirstKIndex n k) := firstKIndex_nonempty hk hkn
  (activePointwiseSupremumOnIndices
    (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x).toFinite.toFinset.min' <|
    by simpa using activePrefixIndices_nonempty k hk hkn x

/-- The coordinate chosen by the resisting oracle attains the maximum among the first `k`
coordinates of `x`. -/
-- Proof sketch: the chosen index belongs to the active-index set of the canonical restricted
-- coordinate family, so
-- `mem_activePointwiseSupremumOnIndices_firstKCoordinateFamily_iff` identifies its coordinate
-- with `first_k_coordinate_max n k x`.
theorem resistingOracleIndex_coordinate_eq_first_k_coordinate_max
    (k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (x : E) :
    x (resistingOracleIndex k hk hkn x).1 = first_k_coordinate_max n k x := by
  letI : Nonempty (FirstKIndex n k) := firstKIndex_nonempty hk hkn
  let S : Set (FirstKIndex n k) :=
    activePointwiseSupremumOnIndices
      (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x
  have hS : S.Nonempty := by
    -- The active prefix set is nonempty, so the `min'` index used by the oracle is defined.
    simpa [S] using activePrefixIndices_nonempty (n := n) k hk hkn x
  have hmem : (resistingOracleIndex k hk hkn x) ∈ S := by
    have hmemFinset :
        ((S.toFinite.toFinset.min' (by simpa [S] using hS)) : FirstKIndex n k) ∈
          S.toFinite.toFinset := by
      -- The least element chosen by `Finset.min'` belongs to the active finite set.
      exact Finset.min'_mem _ _
    simpa [resistingOracleIndex, S] using hmemFinset
  -- Membership in the active restricted-coordinate set identifies the selected coordinate value.
  exact mem_activePointwiseSupremumOnIndices_firstKCoordinateFamily_iff.mp hmem

/-- The chosen vector returned by the resisting construction is `μ x + γ e_{i*}`, where `i*`
is the least active prefix index. -/
def resistingSubgradient
    (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (μ γ : ℝ) : E → E := fun x ↦
  μ • x + γ • e[(resistingOracleIndex k hk hkn x).1]

/-- Evaluating the chosen resisting subgradient field gives the textbook vector
`μ x + γ e_{i*}`. -/
@[simp] theorem resistingSubgradient_apply
    (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (μ γ : ℝ) (x : E) :
    resistingSubgradient k hk hkn μ γ x =
      μ • x + γ • e[(resistingOracleIndex k hk hkn x).1] :=
  rfl

/-- Algorithm 3.1: the resisting oracle for `f_k` sends `x ∈ ℝⁿ` to the pair consisting of the
Nemirovski hard-instance value `f_k(x)` and the vector `γ e_{i*} + μ x`, where `i*` is the least
index among `1, ..., k` attaining the maximum prefix coordinate. -/
def resistingOracle
    (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (μ γ : ℝ) : E → ℝ × E := fun x ↦
  (f_k n k μ γ x, resistingSubgradient k hk hkn μ γ x)

/-- For the nonnegative hard-instance parameters `μ` and `γ`, the chosen resisting vector field
is a subgradient of `f_k` at the query point. -/
-- Proof sketch: apply Proposition 3.28. The chosen index is active, so the basis vector
-- `e_{i*}` belongs to the active-basis image and hence to its convex hull; therefore
-- `μ • x + γ • e_{i*}` belongs to the affine image describing `∂ f_k(x)`.
theorem resistingSubgradient_isSubgradientAt
    (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (μ γ : ℝ)
    (hμ : 0 ≤ μ) (hγ : 0 ≤ γ) (x : E) :
    IsSubgradientAt (fun y : E ↦ (f_k n k μ γ y : WithTop ℝ)) x
      (resistingSubgradient k hk hkn μ γ x) := by
  letI : Nonempty (FirstKIndex n k) := firstKIndex_nonempty hk hkn
  have hi_active :
      resistingOracleIndex k hk hkn x ∈
        activePointwiseSupremumOnIndices
          (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x := by
    -- The oracle index is active because its coordinate realizes the first-`k` maximum.
    exact mem_activePointwiseSupremumOnIndices_firstKCoordinateFamily_iff.mpr
      (resistingOracleIndex_coordinate_eq_first_k_coordinate_max (n := n) k hk hkn x)
  have hbasis :
      e[(resistingOracleIndex k hk hkn x).1] ∈
        ((fun i : FirstKIndex n k ↦ e[i.1]) ''
          activePointwiseSupremumOnIndices
            (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x) := by
    -- The active index contributes its standard basis vector to the active-basis image.
    exact Set.mem_image_of_mem (fun i : FirstKIndex n k ↦ e[i.1]) hi_active
  have hhull :
      e[(resistingOracleIndex k hk hkn x).1] ∈
        convexHull ℝ
          ((fun i : FirstKIndex n k ↦ e[i.1]) ''
            activePointwiseSupremumOnIndices
              (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x) := by
    -- Every active basis vector lies in the convex hull generated by the active basis image.
    exact subset_convexHull ℝ _ hbasis
  have hmem :
      resistingSubgradient k hk hkn μ γ x ∈
        (fun v : E ↦ μ • x + γ • v) ''
          convexHull ℝ
            ((fun i : FirstKIndex n k ↦ e[i.1]) ''
              activePointwiseSupremumOnIndices
                (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x) := by
    -- The resisting vector is the affine image of that active basis vector.
    exact ⟨e[(resistingOracleIndex k hk hkn x).1], hhull, by
      simp [resistingSubgradient]⟩
  have hsub :
      resistingSubgradient k hk hkn μ γ x ∈
        subdifferential (fun y : E ↦ (f_k n k μ γ y : WithTop ℝ)) x := by
    -- Proposition 3.28 identifies the full subdifferential with this affine image.
    rw [subdifferential_f_k_eq_affineImage_convexHull_activeBasis (n := n)
      (k := k) μ γ hk hkn hμ hγ x]
    exact hmem
  exact mem_subdifferential_iff.mp hsub

/-- For nonnegative hard-instance parameters, the resisting reply defines the chapter owner
first-order oracle for `f_k`. -/
def resistingFirstOrderOracle
    (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (μ γ : ℝ)
    (hμ : 0 ≤ μ) (hγ : 0 ≤ γ) :
    FirstOrderOracle (f_k n k μ γ) where
  subgradient := resistingSubgradient k hk hkn μ γ
  subgradient_spec x := resistingSubgradient_isSubgradientAt k hk hkn μ γ hμ hγ x

/-- Under the nonnegative-parameter owner hypotheses, the source-facing pair-valued resisting
reply is exactly the canonical answer of the chapter `FirstOrderOracle`. -/
@[simp] theorem resistingOracle_eq_answer
    (k : ℕ) (hk : 0 < k) (hkn : k ≤ n) (μ γ : ℝ)
    (hμ : 0 ≤ μ) (hγ : 0 ≤ γ) (x : E) :
    resistingOracle k hk hkn μ γ x =
      (resistingFirstOrderOracle k hk hkn μ γ hμ hγ).answer x :=
  rfl
end
