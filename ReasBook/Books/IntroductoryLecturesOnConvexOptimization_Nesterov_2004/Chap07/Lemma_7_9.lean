/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_29
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_33

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (positiveOrthant)
open Matrix
open scoped BigOperators EllipsoidNotation SymmetricBox

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 7.9 lies in Chapter 7's diagonal ellipsoid / symmetric-box rounding domain.

Sampled owner-style declarations:
- `symmetricBox` with notation `B(g)` in `Chap07/Definition_7_33`, the chapter owner for
  coordinate boxes;
- `mem_symmetricBox_iff_abs_le` in `Chap07/Definition_7_33`, the owner theorem for the textbook
  absolute-value membership view of `B(a)`;
- `matrixEllipsoid` with centered notation `W[r](G)` in `Chap07/Definition_7_26`, the chapter
  owner for ellipsoids;
- `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, the chapter owner for centered
  `γ √n`-ellipsoidal roundings;
- `EuclideanSpace.positiveOrthant` and `EuclideanSpace.mem_positiveOrthant_iff` in
  `Chap01/Definition_1_10_2`, the canonical positivity owner for the semiaxis vector.

Best owner abstraction:
- source-facing: the symmetric-box sandwich hypothesis and the resulting diagonal ellipsoidal
  rounding;
- core/canonical: `positiveOrthant`, `B(g)`, `W[r](G)`, and `IsEllipsoidalRounding`;
- bridge/view: the coordinate membership theorems specialized to `B(a)` and
  `W[r](Matrix.diagonal fun i ↦ (a i)^2)`.

Primitive data:
- the semiaxis vector `a : E`;
- a set `C : Set E`;
- a dilation factor `m : ℝ`.

Derived API:
- the inner box `B(a)` and outer box `B(m • a)`, read through
  `mem_symmetricBox_iff_abs_le`;
- the diagonal shape matrix `Matrix.diagonal fun i ↦ (a i)^2`, whose semiaxes are `a i`;
- the centered rounding datum
  `IsEllipsoidalRounding C m (Matrix.diagonal fun i ↦ (a i)^2)`;
- the inner and outer ellipsoid containments recovered canonically from that owner.

Source/core/bridge triage:
- source-facing: the sandwich theorem below;
- core/canonical: `positiveOrthant`, `B(g)`, `mem_symmetricBox_iff_abs_le`, `W[r](G)`, and
  `IsEllipsoidalRounding`;
- bridge/view: the diagonal-square ellipsoid membership theorem specialized to
  `W[r](Matrix.diagonal fun i ↦ (a i)^2)`.

This refinement deletes the local duplicate box-membership theorem and reuses the Chapter 7 box
owner `B(·)` together with `mem_symmetricBox_iff_abs_le` directly. The main theorem is now stated
through the Chapter 7 rounding owner `IsEllipsoidalRounding` instead of exposing its positive
definiteness and ellipsoid containments as a parallel conjunction, while the ambient dimension now
matches the chapter owners at `{n : ℕ}` instead of unnecessarily strengthening to `ℕ+`.
-/

/-- Helper for Lemma 7.9: the diagonal-square shape matrix with semiaxes `a`. -/
abbrev diagonalSquareMatrix (a : E) : Mat :=
  diagonal fun i ↦ (a i) ^ (2 : ℕ)

-- Proof sketch: specialize the centered ellipsoid owner `W[r](G)` to the diagonal-square matrix
-- `G = D²` with `D = diag(d)`, then expand the inverse diagonal quadratic form.
/-- Membership in the diagonal ellipsoid with shape matrix `D²`, where `D = diag(d)`, is exactly
the coordinate inequality `sqrt (∑ i, (x i / d i)^2) ≤ r` when the semiaxes `d i` are positive.
-/
theorem mem_diagonalSquareEllipsoid_iff
    (a : E) (ha : a ∈ positiveOrthant n) (r : ℝ) (x : E) :
    x ∈ W[r]((diagonalSquareMatrix a)) ↔
      Real.sqrt (∑ i, (x i / a i) ^ (2 : ℕ)) ≤ r := by
  -- Expand the centered ellipsoid owner into its defining inverse quadratic form.
  rw [mem_centeredMatrixEllipsoid_iff]
  -- Route correction: replace the brittle one-line `simpa` with an explicit diagonal inverse
  -- expansion before simplifying the remaining one-coordinate identity.
  have hinner_eq_dotProduct :
      inner ℝ ((diagonalSquareMatrix a)⁻¹.toEuclideanLin x) x =
        x.ofLp ⬝ᵥ ((diagonalSquareMatrix a)⁻¹ *ᵥ x.ofLp) := by
    simpa only [Matrix.ofLp_toLpLin] using
      (EuclideanSpace.inner_eq_star_dotProduct (((diagonalSquareMatrix a)⁻¹).toEuclideanLin x) x).symm
  rw [hinner_eq_dotProduct, Matrix.inv_diagonal, Matrix.dotProduct_mulVec]
  simp [diagonalSquareMatrix, Matrix.vecMul, dotProduct, Matrix.diagonal]
  have hsum_eq :
      ∑ i : Fin n, x i * Ring.inverse (fun j : Fin n ↦ (a j) ^ (2 : ℕ)) i * x i =
        ∑ i : Fin n, (x i / a i) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hai : 0 < a i := (EuclideanSpace.mem_positiveOrthant_iff.mp ha) i
    have hfun_inv :
        Ring.inverse (fun j : Fin n ↦ (a j) ^ (2 : ℕ)) i = ((a i) ^ (2 : ℕ))⁻¹ := by
      have hunit_fun : IsUnit (fun j : Fin n ↦ (a j) ^ (2 : ℕ)) :=
        Pi.isUnit_iff.mpr fun j ↦
          isUnit_iff_ne_zero.mpr <| pow_ne_zero 2 (ne_of_gt ((EuclideanSpace.mem_positiveOrthant_iff.mp ha) j))
      rw [Ring.inverse, dif_pos hunit_fun]
      simpa using hunit_fun.val_inv_apply i
    rw [hfun_inv]
    field_simp [pow_two, hai.ne']
  simpa [hsum_eq]

/-- Helper for Lemma 7.9: in positive dimension, a box sandwich `B(a) ⊆ C ⊆ B(m • a)` forces the
outer scaling factor to satisfy `1 ≤ m`. -/
lemma box_scale_one_le_of_sandwich
    [Nonempty (Fin n)] (a : E) (ha : a ∈ positiveOrthant n) {m : ℝ} {C : Set E}
    (h_left : B(a) ⊆ C)
    (h_right : C ⊆ B((m • a))) :
    1 ≤ m := by
  classical
  let i : Fin n := Classical.choice inferInstance
  have ha_box : a ∈ B(a) := by
    -- The semiaxis vector lies in its own symmetric box coordinatewise.
    rw [mem_symmetricBox_iff_abs_le]
    intro j
    have haj : 0 < a j := (EuclideanSpace.mem_positiveOrthant_iff.mp ha) j
    simpa [abs_of_pos haj] using le_rfl (a j)
  have ha_outer : a ∈ B((m • a)) := h_right (h_left ha_box)
  have hai : 0 < a i := (EuclideanSpace.mem_positiveOrthant_iff.mp ha) i
  have ha_outer_bounds : ∀ j, |a j| ≤ (m • a) j :=
    mem_symmetricBox_iff_abs_le.mp ha_outer
  have hai_le : a i ≤ m * a i := by
    -- Reading the outer box membership at a single positive coordinate isolates the scalar bound.
    simpa [abs_of_pos hai, Pi.smul_apply] using ha_outer_bounds i
  have hdiv : a i / a i ≤ m := (_root_.div_le_iff₀ hai).2 hai_le
  simpa [ne_of_gt hai] using hdiv

/-- Helper for Lemma 7.9: the unit diagonal ellipsoid `W[1](diag(a^2))` is contained in the
matching symmetric box `B(a)` whenever the semiaxes are positive. -/
lemma unit_diagonalSquareEllipsoid_subset_symmetricBox
    (a : E) (ha : a ∈ positiveOrthant n) :
    W[1]((diagonalSquareMatrix a)) ⊆ B(a) := by
  intro x hx
  rw [mem_symmetricBox_iff_abs_le]
  intro i
  have hai : 0 < a i := (EuclideanSpace.mem_positiveOrthant_iff.mp ha) i
  have hx_radius :
      Real.sqrt (∑ j, (x j / a j) ^ (2 : ℕ)) ≤ 1 :=
    (mem_diagonalSquareEllipsoid_iff a ha 1 x).mp hx
  have hsum_le_one : ∑ j, (x j / a j) ^ (2 : ℕ) ≤ 1 := by
    -- Squaring the radius-one bound turns the ellipsoid inequality into a sum-of-squares bound.
    rw [Real.sqrt_le_iff] at hx_radius
    simpa using hx_radius
  have hcoord_sq : (x i / a i) ^ (2 : ℕ) ≤ 1 := by
    -- Each nonnegative coordinate square is bounded by the full nonnegative sum.
    have hnonneg : ∀ j : Fin n, 0 ≤ (x j / a j) ^ (2 : ℕ) := by
      intro j
      positivity
    calc
      (x i / a i) ^ (2 : ℕ) ≤ ∑ j, (x j / a j) ^ (2 : ℕ) := by
        exact Finset.single_le_sum (fun j _ ↦ hnonneg j) (by simp)
      _ ≤ 1 := hsum_le_one
  have habs_div_sq : (|x i| / a i) ^ (2 : ℕ) ≤ 1 := by
    -- Rewriting through absolute values prepares the final linear inequality in `|x i|`.
    have habs_div_sq_eq : (|x i| / a i) ^ (2 : ℕ) = (x i / a i) ^ (2 : ℕ) := by
      rw [show |x i| / a i = |x i / a i| by rw [abs_div, abs_of_pos hai], sq_abs]
    rw [habs_div_sq_eq]
    exact hcoord_sq
  have habs_div_le_one : |x i| / a i ≤ 1 := by
    have habs_div_nonneg : 0 ≤ |x i| / a i := by positivity
    nlinarith
  -- Multiply back by the positive semiaxis length to recover the box inequality.
  have habs_le : |x i| ≤ 1 * a i := (_root_.div_le_iff₀ hai).mp habs_div_le_one
  simpa using habs_le

/-- Helper for Lemma 7.9: if `x` lies in the symmetric box `B(m • a)` with positive semiaxes and
`m ≥ 0`, then `x` lies in the outer diagonal ellipsoid `W[m √n](diag(a^2))`. -/
lemma symmetricBox_subset_outer_diagonalSquareEllipsoid
    (a : E) (ha : a ∈ positiveOrthant n) {m : ℝ} (hm : 0 ≤ m) :
    B((m • a)) ⊆ W[(m * Real.sqrt (n : ℝ))]((diagonalSquareMatrix a)) := by
  intro x hx
  rw [mem_diagonalSquareEllipsoid_iff a ha]
  have hx_box : ∀ i, |x i| ≤ m * a i := by
    -- Read the symmetric-box hypothesis coordinatewise.
    rw [mem_symmetricBox_iff_abs_le] at hx
    simpa [Pi.smul_apply] using hx
  have hcoord_sq : ∀ i : Fin n, (x i / a i) ^ (2 : ℕ) ≤ m ^ (2 : ℕ) := by
    intro i
    have hai : 0 < a i := (EuclideanSpace.mem_positiveOrthant_iff.mp ha) i
    have habs_div_le_m : |x i| / a i ≤ m := (_root_.div_le_iff₀ hai).2 (hx_box i)
    have habs_div_sq : (|x i| / a i) ^ (2 : ℕ) ≤ m ^ (2 : ℕ) := by
      have habs_div_nonneg : 0 ≤ |x i| / a i := by positivity
      nlinarith
    -- The square only depends on the absolute value of the quotient.
    have habs_div_sq_eq : (|x i| / a i) ^ (2 : ℕ) = (x i / a i) ^ (2 : ℕ) := by
      rw [show |x i| / a i = |x i / a i| by rw [abs_div, abs_of_pos hai], sq_abs]
    rw [habs_div_sq_eq] at habs_div_sq
    exact habs_div_sq
  have hsum_sq :
      ∑ i, (x i / a i) ^ (2 : ℕ) ≤ (m * Real.sqrt (n : ℝ)) ^ (2 : ℕ) := by
    have hsqrt_sq : (Real.sqrt (n : ℝ)) ^ (2 : ℕ) = (n : ℝ) := by
      rw [Real.sq_sqrt]
      positivity
    -- Summing the coordinatewise estimate gives the textbook `n * m²` bound.
    calc
      ∑ i, (x i / a i) ^ (2 : ℕ) ≤ ∑ i : Fin n, m ^ (2 : ℕ) := by
        exact Finset.sum_le_sum fun i _ ↦ hcoord_sq i
      _ = (n : ℝ) * m ^ (2 : ℕ) := by simp
      _ = (Real.sqrt (n : ℝ)) ^ (2 : ℕ) * m ^ (2 : ℕ) := by rw [hsqrt_sq]
      _ = (m * Real.sqrt (n : ℝ)) ^ (2 : ℕ) := by ring
  -- Reintroduce the square root now that the right-hand side is visibly nonnegative.
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · exact hsum_sq

-- Proof sketch: the inner containment `W[1](D²) ⊆ B(d)` is the coordinatewise estimate
-- `|x i| / d i ≤ 1` obtained by bounding each nonnegative summand in
-- `∑ i, (x i / d i)^2 ≤ 1`. For the outer containment, `x ∈ B(m d)` gives
-- `|x i| / d i ≤ m` for each coordinate, so
-- `∑ i, (x i / d i)^2 ≤ n * m^2`, equivalently
-- `sqrt (∑ i, (x i / d i)^2) ≤ m * sqrt n`.
/-- Lemma 7.9: if a set `C` lies between the boxes `B(d)` and `B(m d)`, where the semiaxes `d i`
are positive, then `C` lies between the corresponding diagonal ellipsoids
`W₁(D²)` and `W_{m √n}(D²)`, where `D = diag(d)`. Equivalently, the diagonal-square matrix
`D²` is an ellipsoidal rounding of `C` with parameter `m`. -/
theorem symmetricBox_sandwich_implies_diagonalEllipsoid_sandwich
    (a : E) (ha : a ∈ positiveOrthant n) {m : ℝ} {C : Set E}
    (h_left : B(a) ⊆ C)
    (h_right : C ⊆ B((m • a))) :
    IsEllipsoidalRounding C m (diagonalSquareMatrix a) := by
  have hPosDef : (diagonalSquareMatrix a).PosDef := by
    -- Positive diagonal entries make the diagonal square matrix positive definite.
    exact Matrix.PosDef.diagonal (n := Fin n) (R := ℝ)
      (d := fun i ↦ (a i) ^ (2 : ℕ)) (by
        intro i
        simpa [pow_two] using sq_pos_of_pos ((EuclideanSpace.mem_positiveOrthant_iff.mp ha) i))
  have hinner_box :
      W[1]((diagonalSquareMatrix a)) ⊆ B(a) :=
    unit_diagonalSquareEllipsoid_subset_symmetricBox a ha
  have hinner :
      W[1]((diagonalSquareMatrix a)) ⊆ C := by
    -- Compose the inner ellipsoid-to-box inclusion with the left sandwich hypothesis.
    intro x hx
    exact h_left (hinner_box hx)
  cases isEmpty_or_nonempty (Fin n) with
  | inl h_empty =>
      letI := h_empty
      have houter :
          C ⊆ W[(m * Real.sqrt (n : ℝ))]((diagonalSquareMatrix a)) := by
        intro x hx
        -- In zero dimension every point is `0`, so the outer ellipsoid condition is immediate.
        have hn : n = 0 := by
          cases n with
          | zero =>
              rfl
          | succ k =>
              exact (h_empty.false ⟨0, Nat.succ_pos k⟩).elim
        have hx0 : x = 0 := Subsingleton.elim _ _
        subst hx0
        rw [mem_diagonalSquareEllipsoid_iff a ha]
        simpa [hn]
      refine ⟨hPosDef, ?_⟩
      refine ⟨?_, houter⟩
      simpa [centeredMatrixEllipsoid_one_eq_affineEllipsoid] using hinner
  | inr h_nonempty =>
      letI := h_nonempty
      have hm_one : 1 ≤ m := box_scale_one_le_of_sandwich a ha h_left h_right
      have hm_nonneg : 0 ≤ m := le_trans (by norm_num) hm_one
      have houter_box :
          B((m • a)) ⊆ W[(m * Real.sqrt (n : ℝ))]((diagonalSquareMatrix a)) :=
        symmetricBox_subset_outer_diagonalSquareEllipsoid a ha hm_nonneg
      have houter :
          C ⊆ W[(m * Real.sqrt (n : ℝ))]((diagonalSquareMatrix a)) := by
        -- Compose the right sandwich hypothesis with the outer box-to-ellipsoid inclusion.
        intro x hx
        exact houter_box (h_right hx)
      refine ⟨hPosDef, ?_⟩
      refine ⟨?_, houter⟩
      simpa [centeredMatrixEllipsoid_one_eq_affineEllipsoid] using hinner

end
