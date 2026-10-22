/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_17

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp ofLp)
open scoped BigOperators
open InnerProductSpace (toDualMap)

universe u

section

variable {ι : Type u} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/- Proposition 3.23 is `source-facing`: the textbook formula is a vector-side description of the
subdifferential of the coordinatewise maximum on `ℝ^n`. The chapter owner bridge for that
vector-side view is already `euclideanSubdifferentialAt` from Theorem 3.4, so the main
declarations below use that owner directly. The continuous-dual image equalities are kept only as
thin companion reformulations. -/
-- Semantic recall note: `lean_leansearch` returned only generic simplex APIs, so this
-- coordinatewise-max subdifferential statement remains chapter-local.

/-- The max function on a finite coordinate space, specializing to `x ↦ max_i x i` on `ℝ^n`. -/
noncomputable def coordinatewiseMax (x : ι → ℝ) : ℝ :=
  ⨆ i : ι, x i

/-- The face of the standard simplex supported on the active coordinates of `x`, namely the
indices `i` with `coordinatewiseMax x = x i`. -/
def activeCoordinateFace (x : ι → ℝ) : Set (ι → ℝ) :=
  {l | l ∈ stdSimplex ℝ ι ∧ ∀ i, coordinatewiseMax x ≠ x i → l i = 0}

-- Proof sketch: unfold `activeCoordinateFace`; membership is exactly the conjunction that `λ`
-- lies in the standard simplex and vanishes on every inactive coordinate.
/-- Membership in `activeCoordinateFace x` means belonging to the standard simplex and being
supported on the active coordinates of `x`. -/
@[simp] theorem mem_activeCoordinateFace_iff {x l : ι → ℝ} :
    l ∈ activeCoordinateFace x ↔
      l ∈ stdSimplex ℝ ι ∧ ∀ i, coordinatewiseMax x ≠ x i → l i = 0 := by
  -- Unfolding the owner definition exposes exactly the simplex and inactive-support clauses.
  rfl

section

variable [Nonempty ι]

/-- On a nonempty finite coordinate space, `coordinatewiseMax x` is the ordinary finite maximum
over `Finset.univ`. -/
theorem coordinatewiseMax_eq_sup' (x : ι → ℝ) :
    coordinatewiseMax x = (Finset.univ : Finset ι).sup' Finset.univ_nonempty x := by
  rw [coordinatewiseMax, ← Finset.sup'_univ_eq_ciSup]

omit [Fintype ι] in
/- Helper for Proposition 3.23: every coordinate of `x` is bounded above by
`coordinatewiseMax x`. -/
theorem le_coordinatewiseMax [Finite ι] (x : ι → ℝ) (i : ι) :
    x i ≤ coordinatewiseMax x := by
  let _ : Fintype ι := Fintype.ofFinite ι
  -- Rewrite the coordinatewise maximum as the finite supremum over `Finset.univ`.
  rw [coordinatewiseMax_eq_sup']
  exact Finset.le_sup' x (Finset.mem_univ i)

omit [Fintype ι] in
/- Helper for Proposition 3.23: adding a constant to every coordinate translates the
coordinatewise maximum by the same constant. -/
theorem coordinatewiseMax_add_const [Finite ι] (x : ι → ℝ) (t : ℝ) :
    coordinatewiseMax (fun i ↦ x i + t) = coordinatewiseMax x + t := by
  let _ : Fintype ι := Fintype.ofFinite ι
  -- The finite supremum commutes with translation in the ordered additive group `ℝ`.
  rw [coordinatewiseMax_eq_sup', coordinatewiseMax_eq_sup']
  simpa using
    (Finset.sup'_add Finset.univ x t Finset.univ_nonempty).symm

/-- For a constant coordinate vector, every coordinate is active, so the active face is the whole
standard simplex. -/
@[simp] theorem activeCoordinateFace_const_eq_stdSimplex (α : ℝ) :
    activeCoordinateFace (fun _ : ι ↦ α) = stdSimplex ℝ ι := by
  ext l
  simp [activeCoordinateFace, coordinatewiseMax_eq_sup']

-- Proof sketch: apply the max rule for subdifferentials to the coordinate projections
-- `x ↦ x i`. Each coordinate map has singleton Euclidean subdifferential given by the
-- corresponding standard basis vector, so the subdifferential of
-- the maximum is the convex hull of the active basis vectors, equivalently the active face of the
-- standard simplex.

/-- Helper for Proposition 3.23: any point of the active coordinate face gives a valid Euclidean
subgradient of the coordinatewise maximum. -/
private lemma toLp_mem_euclideanSubdifferentialAt_coordinatewiseMax_of_mem_activeCoordinateFace
    {x lam : ι → ℝ}
    (hlam : lam ∈ activeCoordinateFace x) :
    toLp 2 lam ∈ euclideanSubdifferentialAt
      (fun y : E ↦ coordinatewiseMax (ofLp y)) (toLp 2 x) := by
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff]
  rcases mem_activeCoordinateFace_iff.mp hlam with ⟨hSimplex, hInactive⟩
  intro y
  have hnonneg : ∀ i, 0 ≤ lam i := fun i ↦ hSimplex.1 i
  have hsum_one : ∑ i, lam i = 1 := hSimplex.2
  have hy_weighted :
      ∑ i, lam i * ofLp y i ≤ coordinatewiseMax (ofLp y) := by
    -- Each coordinate is bounded by the global maximum, so the weighted average is as well.
    calc
      ∑ i, lam i * ofLp y i ≤ ∑ i, lam i * coordinatewiseMax (ofLp y) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact mul_le_mul_of_nonneg_left (le_coordinatewiseMax (ofLp y) i) (hnonneg i)
      _ = (∑ i, lam i) * coordinatewiseMax (ofLp y) := by
        rw [Finset.sum_mul]
      _ = coordinatewiseMax (ofLp y) := by rw [hsum_one, one_mul]
  have hx_weighted :
      ∑ i, lam i * x i = coordinatewiseMax x := by
    -- Inactive coordinates have zero weight, while active coordinates equal the maximum.
    calc
      ∑ i, lam i * x i = ∑ i, lam i * coordinatewiseMax x := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hactive : coordinatewiseMax x = x i
        · rw [hactive]
        · simp [hInactive i hactive]
      _ = (∑ i, lam i) * coordinatewiseMax x := by
        rw [Finset.sum_mul]
      _ = coordinatewiseMax x := by rw [hsum_one, one_mul]
  have hpair_bound :
      (toDualMap ℝ E (toLp 2 lam)) (y - toLp 2 x) ≤
        coordinatewiseMax (ofLp y) - coordinatewiseMax x := by
    -- Rewrite the pairing as the difference of the two weighted sums and compare each part.
    rw [coordinatePairing_toLp_sub]
    calc
      ∑ i, lam i * (ofLp y i - ofLp (toLp 2 x) i)
          = ∑ i, (lam i * ofLp y i - lam i * x i) := by
              simp [mul_sub]
      _ = ∑ i, lam i * ofLp y i - ∑ i, lam i * x i := by
            rw [Finset.sum_sub_distrib]
      _ ≤ coordinatewiseMax (ofLp y) - coordinatewiseMax x := by
            rw [hx_weighted]
            linarith
  -- Combine the weighted-sum estimate with the exact active-face value at `x`.
  have hy' :
      coordinatewiseMax x + (toDualMap ℝ E (toLp 2 lam)) (y - toLp 2 x) ≤
        coordinatewiseMax (ofLp y) := by
    linarith
  simpa [WithLp.ofLp_toLp, ge_iff_le] using hy'

/-- Helper for Proposition 3.23: every Euclidean subgradient of the coordinatewise maximum has
nonnegative coefficients summing to `1`, and inactive coordinates carry zero mass. -/
private lemma ofLp_mem_activeCoordinateFace_of_mem_euclideanSubdifferentialAt_coordinatewiseMax
    {x z : E}
    (hz : z ∈ euclideanSubdifferentialAt (fun y : E ↦ coordinatewiseMax (ofLp y)) x) :
    ofLp z ∈ activeCoordinateFace (ofLp x) := by
  classical
  rw [mem_activeCoordinateFace_iff]
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff] at hz
  have hsum_le : ∑ i, ofLp z i ≤ 1 := by
    -- Test the subgradient inequality on the uniform shift `x + 1`.
    have hy :=
      hz (toLp 2 fun i : ι ↦ ofLp x i + 1)
    have hy' :
        coordinatewiseMax (fun i : ι ↦ ofLp x i + 1) ≥
          coordinatewiseMax (ofLp x) +
            (toDualMap ℝ E z) (toLp 2 (fun i : ι ↦ ofLp x i + 1) - x) := by
      simpa [WithLp.ofLp_toLp] using hy
    have hpair :
        (toDualMap ℝ E z) (toLp 2 (fun i : ι ↦ ofLp x i + 1) - x) =
          ∑ i, ofLp z i := by
      calc
        (toDualMap ℝ E z) (toLp 2 (fun i : ι ↦ ofLp x i + 1) - x)
            = ∑ i, ofLp z i * ((ofLp x i + 1) - ofLp x i) := by
                simpa [WithLp.ofLp_toLp] using
                  (coordinatePairing_toLp_sub :
                    (toDualMap ℝ E (toLp 2 (ofLp z)))
                        (toLp 2 (fun i : ι ↦ ofLp x i + 1) - x) =
                      ∑ i, ofLp z i * ((ofLp x i + 1) - ofLp x i))
        _ = ∑ i, ofLp z i := by simp
    rw [coordinatewiseMax_add_const] at hy'
    rw [hpair] at hy'
    linarith
  have hsum_ge : 1 ≤ ∑ i, ofLp z i := by
    -- Test the subgradient inequality on the uniform shift `x - 1`.
    have hy :=
      hz (toLp 2 fun i : ι ↦ ofLp x i + (-1))
    have hy' :
        coordinatewiseMax (fun i : ι ↦ ofLp x i + (-1)) ≥
          coordinatewiseMax (ofLp x) +
            (toDualMap ℝ E z) (toLp 2 (fun i : ι ↦ ofLp x i + (-1)) - x) := by
      simpa [WithLp.ofLp_toLp] using hy
    have hpair :
        (toDualMap ℝ E z) (toLp 2 (fun i : ι ↦ ofLp x i + (-1)) - x) =
          -∑ i, ofLp z i := by
      calc
        (toDualMap ℝ E z) (toLp 2 (fun i : ι ↦ ofLp x i + (-1)) - x)
            = ∑ i, ofLp z i * ((ofLp x i + (-1)) - ofLp x i) := by
                simpa [WithLp.ofLp_toLp] using
                  (coordinatePairing_toLp_sub :
                    (toDualMap ℝ E (toLp 2 (ofLp z)))
                        (toLp 2 (fun i : ι ↦ ofLp x i + (-1)) - x) =
                      ∑ i, ofLp z i * ((ofLp x i + (-1)) - ofLp x i))
        _ = -∑ i, ofLp z i := by
              simp
    rw [coordinatewiseMax_add_const] at hy'
    rw [hpair] at hy'
    linarith
  have hsum_one : ∑ i, ofLp z i = 1 := by
    linarith
  have hnonneg : ∀ i, 0 ≤ ofLp z i := by
    intro i
    -- Lower the `i`-th coordinate by `1`; the maximum cannot increase.
    let yi : E := toLp 2 (Function.update (ofLp x) i (ofLp x i - 1))
    have hy := hz yi
    have hmax_le :
        coordinatewiseMax (Function.update (ofLp x) i (ofLp x i - 1)) ≤
          coordinatewiseMax (ofLp x) := by
      rw [coordinatewiseMax_eq_sup' (Function.update (ofLp x) i (ofLp x i - 1))]
      refine Finset.sup'_le Finset.univ_nonempty
        (Function.update (ofLp x) i (ofLp x i - 1)) ?_
      intro j hj
      by_cases hji : j = i
      · have hxi : ofLp x j ≤ coordinatewiseMax (ofLp x) :=
          le_coordinatewiseMax (ofLp x) j
        simp [Function.update, hji] at hxi ⊢
        linarith
      · simpa [Function.update, hji] using le_coordinatewiseMax (ofLp x) j
    have hpair :
        (toDualMap ℝ E z) (yi - x) = -ofLp z i := by
      calc
        (toDualMap ℝ E z) (yi - x)
            = ∑ j, ofLp z j * (Function.update (ofLp x) i (ofLp x i - 1) j - ofLp x j) := by
                simpa [yi, WithLp.ofLp_toLp] using
                  (coordinatePairing_toLp_sub :
                    (toDualMap ℝ E (toLp 2 (ofLp z))) (yi - x) =
                      ∑ j, ofLp z j *
                        (Function.update (ofLp x) i (ofLp x i - 1) j - ofLp x j))
        _ = ofLp z i * ((ofLp x i - 1) - ofLp x i) := by
              rw [Finset.sum_eq_single i]
              · simp [Function.update]
              · intro j hj hji
                simp [Function.update, hji]
              · simp
        _ = -ofLp z i := by ring
    have hy' :
        coordinatewiseMax (Function.update (ofLp x) i (ofLp x i - 1)) ≥
          coordinatewiseMax (ofLp x) + (toDualMap ℝ E z) (yi - x) := by
      simpa [yi, WithLp.ofLp_toLp] using hy
    rw [hpair] at hy'
    have hbound : coordinatewiseMax (ofLp x) - ofLp z i ≤ coordinatewiseMax (ofLp x) := by
      linarith [hy', hmax_le]
    linarith
  refine ⟨?_, ?_⟩
  · -- The previous tests exactly recover the simplex constraints.
    exact ⟨hnonneg, hsum_one⟩
  · intro i hiInactive
    -- Raise an inactive coordinate by half its gap; the maximum stays unchanged.
    let gap : ℝ := coordinatewiseMax (ofLp x) - ofLp x i
    have hgap_pos : 0 < gap := by
      have hxi := le_coordinatewiseMax (ofLp x) i
      have hne : ofLp x i ≠ coordinatewiseMax (ofLp x) := by
        intro hEq
        exact hiInactive hEq.symm
      have hx_lt : ofLp x i < coordinatewiseMax (ofLp x) :=
        lt_of_le_of_ne hxi hne
      dsimp [gap]
      linarith
    let t : ℝ := gap / 2
    have ht_nonneg : 0 ≤ t := by
      dsimp [t]
      linarith
    let yi : E := toLp 2 (Function.update (ofLp x) i (ofLp x i + t))
    have hy := hz yi
    have hmax_eq :
        coordinatewiseMax (Function.update (ofLp x) i (ofLp x i + t)) =
          coordinatewiseMax (ofLp x) := by
      apply le_antisymm
      · rw [coordinatewiseMax_eq_sup' (Function.update (ofLp x) i (ofLp x i + t))]
        refine Finset.sup'_le Finset.univ_nonempty
          (Function.update (ofLp x) i (ofLp x i + t)) ?_
        intro j hj
        by_cases hji : j = i
        · have hbound : ofLp x i + t ≤ coordinatewiseMax (ofLp x) := by
            dsimp [t, gap]
            linarith
          simpa [Function.update, hji] using hbound
        · simpa [Function.update, hji] using le_coordinatewiseMax (ofLp x) j
      · rw [coordinatewiseMax_eq_sup' (ofLp x)]
        refine Finset.sup'_le Finset.univ_nonempty (ofLp x) ?_
        intro j hj
        have hsup :
            Function.update (ofLp x) i (ofLp x i + t) j ≤
              coordinatewiseMax (Function.update (ofLp x) i (ofLp x i + t)) := by
          rw [coordinatewiseMax_eq_sup' (Function.update (ofLp x) i (ofLp x i + t))]
          exact Finset.le_sup' (Function.update (ofLp x) i (ofLp x i + t))
            (Finset.mem_univ j)
        by_cases hji : j = i
        · have hle : ofLp x j ≤ Function.update (ofLp x) i (ofLp x i + t) j := by
            simp [Function.update, hji, ht_nonneg]
          exact le_trans hle hsup
        · have hle : ofLp x j ≤ Function.update (ofLp x) i (ofLp x i + t) j := by
            simp [Function.update, hji]
          exact le_trans hle hsup
    have hpair :
        (toDualMap ℝ E z) (yi - x) = ofLp z i * t := by
      calc
        (toDualMap ℝ E z) (yi - x)
            = ∑ j, ofLp z j * (Function.update (ofLp x) i (ofLp x i + t) j - ofLp x j) := by
                simpa [yi, WithLp.ofLp_toLp] using
                  (coordinatePairing_toLp_sub :
                    (toDualMap ℝ E (toLp 2 (ofLp z))) (yi - x) =
                      ∑ j, ofLp z j *
                        (Function.update (ofLp x) i (ofLp x i + t) j - ofLp x j))
        _ = ofLp z i * ((ofLp x i + t) - ofLp x i) := by
              rw [Finset.sum_eq_single i]
              · simp [Function.update]
              · intro j hj hji
                simp [Function.update, hji]
              · simp
        _ = ofLp z i * t := by ring
    have hy' :
        coordinatewiseMax (Function.update (ofLp x) i (ofLp x i + t)) ≥
          coordinatewiseMax (ofLp x) + (toDualMap ℝ E z) (yi - x) := by
      simpa [yi, WithLp.ofLp_toLp] using hy
    rw [hmax_eq, hpair] at hy'
    have hz_nonpos : ofLp z i ≤ 0 := by
      have ht_pos : 0 < t := by
        dsimp [t]
        linarith
      have hmul_nonpos : ofLp z i * t ≤ 0 := by
        linarith
      by_cases hzi : 0 < ofLp z i
      · have hmul_pos : 0 < ofLp z i * t := mul_pos hzi ht_pos
        linarith
      · exact le_of_not_gt hzi
    exact le_antisymm hz_nonpos (hnonneg i)

/-- Proposition 3.23 [Subdifferential of the max function]: the Euclidean/vector-side
subdifferential of the coordinatewise maximum on `ℝ^n` is exactly the face of the standard simplex
supported on the active coordinates. -/
theorem euclidean_subdifferentialAt_coordinatewiseMax_eq_activeCoordinateFace
    (x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ coordinatewiseMax (ofLp y)) x =
      toLp 2 '' activeCoordinateFace (ofLp x) := by
  ext z
  constructor
  · intro hz
    refine ⟨ofLp z, ?_, by simp⟩
    -- Convert the Euclidean subgradient directly into the active-face constraints.
    exact
      ofLp_mem_activeCoordinateFace_of_mem_euclideanSubdifferentialAt_coordinatewiseMax hz
  · rintro ⟨w, hw, rfl⟩
    -- Reassemble any active-face coefficient vector into the Euclidean subgradient.
    exact
      toLp_mem_euclideanSubdifferentialAt_coordinatewiseMax_of_mem_activeCoordinateFace hw

/-- Membership form of Proposition 3.23 at a coordinate vector `x : ι → ℝ`. This is the
source-facing statement: a Euclidean vector `z` is a subgradient of `y ↦ max_i y i` at `x`
exactly when its coordinate vector lies in the active face of the simplex at `x`. -/
theorem mem_euclideanSubdifferentialAt_coordinatewiseMax_toLp_iff
    {x : ι → ℝ} {z : E} :
    z ∈ euclideanSubdifferentialAt (fun y : E ↦ coordinatewiseMax (ofLp y)) (toLp 2 x) ↔
      ofLp z ∈ activeCoordinateFace x := by
  constructor
  · intro hz
    simpa [WithLp.ofLp_toLp] using
      (ofLp_mem_activeCoordinateFace_of_mem_euclideanSubdifferentialAt_coordinatewiseMax hz)
  · intro hz
    simpa [WithLp.ofLp_toLp] using
      (toLp_mem_euclideanSubdifferentialAt_coordinatewiseMax_of_mem_activeCoordinateFace hz)

/-- Continuous-dual reformulation of Proposition 3.23 obtained by applying the canonical Riesz
map to the vector-side active face. -/
theorem subdifferentialAt_coordinatewiseMax_eq_image_activeCoordinateFace
    (x : E) :
    subdifferentialAt (fun y : E ↦ coordinatewiseMax (ofLp y)) x =
      toDualMap ℝ E '' (toLp 2 '' activeCoordinateFace (ofLp x)) := by
  ext g
  constructor
  · intro hg
    obtain ⟨z, rfl⟩ := (InnerProductSpace.toDual ℝ E).surjective g
    have hz :
        z ∈ euclideanSubdifferentialAt (fun y : E ↦ coordinatewiseMax (ofLp y)) x := by
      simpa [mem_euclideanSubdifferentialAt_iff] using hg
    rw [euclidean_subdifferentialAt_coordinatewiseMax_eq_activeCoordinateFace] at hz
    rcases hz with ⟨w, hw, rfl⟩
    exact ⟨toLp 2 w, ⟨w, hw, rfl⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    have hz' :
        z ∈ euclideanSubdifferentialAt (fun y : E ↦ coordinatewiseMax (ofLp y)) x := by
      rw [euclidean_subdifferentialAt_coordinatewiseMax_eq_activeCoordinateFace]
      exact hz
    simpa [mem_euclideanSubdifferentialAt_iff] using hz'

-- Proof sketch: if `x = fun _ ↦ α`, then every coordinate is active, so
-- `activeCoordinateFace x` is the whole standard simplex. Substitute this into the preceding
-- proposition.
/-- At a constant vector `α e`, every coordinate is active, so the vector-side subdifferential of
the max function is the whole standard simplex. -/
theorem euclidean_subdifferentialAt_coordinatewiseMax_const_eq_stdSimplex
    (α : ℝ) :
    euclideanSubdifferentialAt
        (fun y : E ↦ coordinatewiseMax (ofLp y))
        (toLp 2 fun _ : ι ↦ α) =
      toLp 2 '' (stdSimplex ℝ ι : Set (ι → ℝ)) := by
  -- Rewrite the main theorem at the constant vector and collapse the active face to the simplex.
  simpa [activeCoordinateFace_const_eq_stdSimplex] using
    (euclidean_subdifferentialAt_coordinatewiseMax_eq_activeCoordinateFace
      (toLp 2 fun _ : ι ↦ α))

/-- Continuous-dual reformulation of the constant-vector case of Proposition 3.23. -/
theorem subdifferentialAt_coordinatewiseMax_const_eq_image_stdSimplex
    (α : ℝ) :
    subdifferentialAt
        (fun y : E ↦ coordinatewiseMax (ofLp y))
        (toLp 2 fun _ : ι ↦ α) =
      toDualMap ℝ E '' (toLp 2 '' (stdSimplex ℝ ι : Set (ι → ℝ))) := by
  -- The dual-side constant-vector case is the corresponding specialization of the image theorem.
  simpa [activeCoordinateFace_const_eq_stdSimplex] using
    (subdifferentialAt_coordinatewiseMax_eq_image_activeCoordinateFace
      (toLp 2 fun _ : ι ↦ α))

end

end
