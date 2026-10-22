/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-
Definition 3.35 lies in the finite-dimensional Euclidean Nemirovski hard-instance domain.

Primary domain:
- the nonsmooth strongly-convex hard-instance objective on `ℝⁿ` and the chapter's finite-family
  pointwise-supremum owner for its prefix-coordinate term.

Sampled owner-style declarations:
- `pointwiseSupremumOn` in `Chap03/PointwiseSupremumOn`, the chapter owner for subset-indexed
  pointwise suprema;
- `activePointwiseSupremumOnIndices` in `Chap03/Lemma_3_1_14`, the matching active-index owner
  used later for the prefix-coordinate view;
- `subdifferential_coordinatewiseMaximum_eq_convexHull_activeBasis` in `Chap03/Proposition_3_15`,
  the coordinate-maximum specialization that later feeds the Nemirovski subdifferential formula;
- the hard-instance minimizer API in `Chap03/Proposition_3_30`, which should depend on the owner
  objective rather than define it.

Best owner abstraction:
- source-facing: `f_k`
- core/canonical support: `pointwiseSupremumOn` and `activePointwiseSupremumOnIndices`

Primitive data:
- the ambient dimension `n`
- the active-coordinate length `k`
- the hard-instance parameters `μ` and `γ`

Derived API:
- the prefix-index type `FirstKIndex`
- the restricted coordinate family `firstKCoordinateFamily`
- the real-valued bridge `first_k_coordinate_max`
- the active-index and active-basis descriptions obtained from the generic pointwise-supremum
  owner and used in later Chapter 3 oracle files
- the minimizer and optimal-value API in `Proposition_3_30`

Source/core/bridge triage:
- source-facing: the textbook hard-instance objective `f_k`
- core/canonical: `pointwiseSupremumOn` and `activePointwiseSupremumOnIndices` for the
  prefix-coordinate family
- bridge/view: the real-valued prefix maximum `first_k_coordinate_max`

The earlier refinement put the source-facing owner `f_k` in the later proposition file
`Proposition_3_30` and left this definition file as a recall. That owner direction was wrong:
Definition 3.35 is the place where the hard objective itself is introduced, while
`Proposition_3_30` should only add the explicit minimizer and optimal-value API. This file
therefore owns the source-facing objective `f_k`, but its prefix-coordinate term is now a thin
bridge of the chapter pointwise-supremum owner rather than a separate set-theoretic supremum.
-/

section PrefixCoordinates

variable {n k : ℕ}

/-- The indices of the first `k` coordinates inside `Fin n`. -/
abbrev FirstKIndex (n k : ℕ) := {i : Fin n // i.1 < k}

/-- The coordinate family restricted to the first `k` coordinates of `ℝ^n`. -/
def firstKCoordinateFamily (n k : ℕ) :
    EuclideanSpace ℝ (Fin n) → FirstKIndex n k → WithTop ℝ :=
  fun x i ↦ (x i.1 : WithTop ℝ)

/-- The type of first-`k` coordinate indices is nonempty whenever `0 < k ≤ n`. -/
theorem firstKIndex_nonempty (hk : 0 < k) (hkn : k ≤ n) :
    Nonempty (FirstKIndex n k) := by
  exact ⟨⟨⟨0, lt_of_lt_of_le hk hkn⟩, hk⟩⟩

attribute [local instance] Classical.propDecidable

/-- The maximum among the first `k` coordinates of a vector in `ℝ^n`, viewed as the real-valued
bridge of the chapter `Set.univ` pointwise-supremum specialization on the restricted coordinate
family. -/
def first_k_coordinate_max (n k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  if h : Nonempty (FirstKIndex n k) then
    let _ : Nonempty (FirstKIndex n k) := h
    (pointwiseSupremumOn (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x).untopD 0
  else
    0

/-- Helper for Definition 3.35: in the nonempty prefix case, the chapter pointwise-supremum owner
for the restricted coordinate family is finite. -/
lemma pointwiseSupremumOn_univ_firstKCoordinateFamily_lt_top
    [Nonempty (FirstKIndex n k)] (x : EuclideanSpace ℝ (Fin n)) :
    pointwiseSupremumOn (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x <
      (⊤ : WithTop ℝ) := by
  -- Rewrite the owner supremum as the usual finite supremum over the prefix coordinates.
  rw [pointwiseSupremumOn_univ_eq_sup']
  -- Every restricted coordinate slice is a coerced real number, hence strictly below `⊤`.
  have hlt :
      Finset.univ.sup' Finset.univ_nonempty (firstKCoordinateFamily n k x) < (⊤ : WithTop ℝ) ↔
        ∀ i ∈ Finset.univ, firstKCoordinateFamily n k x i < ⊤ := by
    rw [Finset.sup'_lt_iff]
  exact hlt.mpr fun i hi ↦ by
    simp [firstKCoordinateFamily]

/-- When `FirstKIndex n k` is nonempty, the `Set.univ` specialization of the chapter pointwise
supremum owner for the restricted coordinate family is the coercion of
`first_k_coordinate_max`. -/
theorem coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ
    [Nonempty (FirstKIndex n k)] (x : EuclideanSpace ℝ (Fin n)) :
    ((first_k_coordinate_max n k x : ℝ) : WithTop ℝ) =
      pointwiseSupremumOn (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x := by
  -- Rewrite `first_k_coordinate_max` into its nonempty branch.
  let h : Nonempty (FirstKIndex n k) := inferInstance
  rw [first_k_coordinate_max, dif_pos h]
  simp only
  let s : WithTop ℝ :=
    pointwiseSupremumOn (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x
  have hfinite :
      s < (⊤ : WithTop ℝ) := by
    simpa [s] using pointwiseSupremumOn_univ_firstKCoordinateFamily_lt_top (n := n) (k := k) x
  have hne : s ≠ (⊤ : WithTop ℝ) :=
    ne_of_lt hfinite
  -- Finiteness lets `untopD` recover the original `WithTop` value.
  change ↑(s.untopD 0) = s
  cases hs : s
  · exact (hne hs).elim
  · simp

/-- When `FirstKIndex n k` is nonempty, a prefix index is active exactly when its coordinate
attains `first_k_coordinate_max n k x`. -/
@[simp] theorem mem_activePointwiseSupremumOnIndices_firstKCoordinateFamily_iff
    [Nonempty (FirstKIndex n k)] {x : EuclideanSpace ℝ (Fin n)} {i : FirstKIndex n k} :
    i ∈ activePointwiseSupremumOnIndices
      (Set.univ : Set (FirstKIndex n k)) (firstKCoordinateFamily n k) x ↔
      x i.1 = first_k_coordinate_max n k x := by
  -- Activity on `Set.univ` means that the slice attains the owner supremum value.
  rw [mem_activePointwiseSupremumOnIndices_univ_iff]
  constructor
  · intro hi
    -- Unfold the restricted-coordinate family to return to the textbook coordinate equality.
    rw [← coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ (n := n) (k := k) (x := x)] at hi
    simpa [firstKCoordinateFamily] using hi
  · intro hi
    rw [← coe_first_k_coordinate_max_eq_pointwiseSupremumOn_univ (n := n) (k := k) (x := x)]
    -- The converse is the same rewrite in the opposite direction.
    simpa [firstKCoordinateFamily] using hi

end PrefixCoordinates

/-- Definition 3.35: the Nemirovski hard-instance objective
`f_k(x) = (μ / 2) ‖x‖^2 + γ max{x^(1), …, x^(k)}` on `ℝ^n`. -/
def f_k (n k : ℕ) (μ γ : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (μ / 2) * ‖x‖ ^ 2 + γ * first_k_coordinate_max n k x

/-- Unfolding `f_k` gives its quadratic-plus-prefix-maximum formula. -/
-- Proof sketch: this is the defining equation of `f_k`, so the claim is by unfolding the
-- definition.
@[simp] theorem f_k_def
    (n k : ℕ) (μ γ : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    f_k n k μ γ x =
      (μ / 2) * ‖x‖ ^ 2 + γ * first_k_coordinate_max n k x :=
  rfl
