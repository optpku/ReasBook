/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_27
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_16
import FirstOrderMethodsOptimization_Beck_2017.Chap06.EuclideanL1Norm

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (ofLp toLp)
open scoped BigOperators

universe u

section

variable {ι : Type u}

/- This item is a `bridge/view` statement in the chapter Euclidean subdifferential API. The
owner abstraction is `subdifferentialAt` from Theorem 3.4, and its canonical vector-side bridge is
`euclideanSubdifferentialAt`. The only source-facing content here is the coordinate sign-cube
description of that owner set for the `ℓ₁` norm, now written through mathlib's canonical
`WithLp 1` norm on finite products, so the theorem should use the bridge directly rather than
re-expand the `toDualMap` preimage by hand. -/

recall euclideanSubdifferentialAt

-- Semantic recall note: `lean_leansearch` produced only generic absolute-value derivative facts,
-- not a reusable local `ℓ₁` subgradient formula, so this item stays source-facing.

/-- The coordinatewise sign cube describing the source-facing `ℓ₁`
subgradients of the coordinate vector `x`. -/
def l1CoordinateSubgradientVectors (x : ι → ℝ) : Set (ι → ℝ) :=
  {z : ι → ℝ |
    (∀ i, x i ≠ 0 → z i = Real.sign (x i)) ∧
      ∀ i, x i = 0 → |z i| ≤ 1}

/-- Membership in `l1CoordinateSubgradientVectors x` means matching the coordinatewise sign on the
nonzero coordinates of `x` and staying in `[-1, 1]` on the zero coordinates. -/
@[simp] theorem mem_l1CoordinateSubgradientVectors_iff
    {x z : ι → ℝ} :
    z ∈ l1CoordinateSubgradientVectors x ↔
      (∀ i, x i ≠ 0 → z i = Real.sign (x i)) ∧
        ∀ i, x i = 0 → |z i| ≤ 1 :=
  Iff.rfl

end

section

variable {n : ℕ}

/-- The canonical coordinatewise sign vector belongs to the coordinate description of the `ℓ₁`
subdifferential. -/
theorem sign_vector_mem_l1CoordinateSubgradientVectors (x : Fin n → ℝ) :
    sgn x ∈ l1CoordinateSubgradientVectors x := by
  rw [mem_l1CoordinateSubgradientVectors_iff]
  constructor
  · -- On nonzero coordinates, `sgn` matches the scalar sign function.
    intro i hxi
    by_cases hnonneg : 0 ≤ x i
    · have hpos : 0 < x i := by
        exact lt_of_le_of_ne hnonneg (by simpa using hxi.symm)
      simp [sgn_apply, hnonneg, Real.sign_of_pos hpos]
    · have hneg : x i < 0 := lt_of_not_ge hnonneg
      simp [sgn_apply, hnonneg, Real.sign_of_neg hneg]
  · -- At zero coordinates, `sgn` takes the value `1`, which lies in `[-1, 1]`.
    intro i hxi
    simp [sgn_apply, hxi]

end

section

variable {ι : Type u}

/-- Helper for Proposition 3.17: the coordinate sign-cube condition is equivalent to requiring
that every coordinate belongs to the scalar subdifferential of `t ↦ |t|`. -/
lemma mem_l1CoordinateSubgradientVectors_iff_forall_coordinateScalarSubgradient
    {x w : ι → ℝ} :
    w ∈ l1CoordinateSubgradientVectors x ↔
      ∀ i, w i ∈ euclideanSubdifferentialAt (fun t : ℝ ↦ |t|) (x i) := by
  rw [mem_l1CoordinateSubgradientVectors_iff]
  constructor
  · rintro ⟨hsign, hzero⟩ i
    rw [mem_euclideanSubdifferentialAt_abs_iff_sign_or_bound]
    constructor
    · exact hsign i
    · exact hzero i
  · intro hw
    constructor
    · intro i hx
      -- The nonzero coordinates must equal the scalar sign.
      exact (mem_euclideanSubdifferentialAt_abs_iff_sign_or_bound.mp (hw i)).1 hx
    · intro i hx
      -- The zero coordinates must stay inside the scalar interval `[-1, 1]`.
      exact (mem_euclideanSubdifferentialAt_abs_iff_sign_or_bound.mp (hw i)).2 hx

end

section

variable {ι : Type u} [Fintype ι]

open InnerProductSpace (toDualMap)

local notation "E" => EuclideanSpace ℝ ι

-- Proof sketch: write the `ℓ₁` norm on `ℝ^n` as the finite sum of the coordinate functions
-- `y ↦ |y i|`, apply the finite-dimensional sum rule for subdifferentials, and use the
-- callable scalar companion `mem_euclideanSubdifferentialAt_abs_iff_sign_or_bound` from
-- Proposition 3.16 on each coordinate. The resulting statement is expressed directly through the
-- chapter bridge
-- `euclideanSubdifferentialAt`, with the objective written via the canonical Chapter 6 owner
-- `EuclideanSpace.l1Norm`, i.e. `‖·‖₁`, on finite products.

/-- Helper for Proposition 3.17: the Euclidean/Riesz pairing with `toLp 2 w` is the coordinate
sum `∑ i, w i * (ofLp y i - ofLp x i)`. -/
lemma coordinatePairing_toLp_sub
    {x y : E} {w : ι → ℝ} :
    (toDualMap ℝ E (toLp 2 w)) (y - x) =
      ∑ i, w i * (ofLp y i - ofLp x i) := by
  -- Expand the pairing to the Euclidean dot product in coordinates.
  rw [InnerProductSpace.toDualMap_apply_apply, PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro i hi
  calc
    inner ℝ ((toLp 2 w).ofLp i) ((y - x).ofLp i)
        = ((toLp 2 w).ofLp i) * ((y - x).ofLp i) := by
            exact RCLike.inner_apply' _ _
    _ = w i * (ofLp y i - ofLp x i) := by
          simp

/-- Helper for Proposition 3.17: every global Euclidean subgradient of the
`ℓ₁` norm restricts to a scalar subgradient of `t ↦ |t|` on each coordinate. -/
lemma coordinateScalarSubgradientOfL1Subgradient
    {x z : E} (hz : z ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖y‖₁) x) (i : ι) :
    ofLp z i ∈ euclideanSubdifferentialAt (fun t : ℝ ↦ |t|) (ofLp x i) := by
  classical
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff]
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff] at hz
  intro s
  -- Test the global supporting inequality on vectors that vary only at coordinate `i`.
  let y : E := toLp 2 (Function.update (ofLp x) i s)
  let rest : ℝ := Finset.sum (Finset.univ.erase i) (fun j ↦ |ofLp x j|)
  have hy := hz y
  have hrest_update :
      Finset.sum (Finset.univ.erase i) (fun j ↦ |Function.update (ofLp x) i s j|) = rest := by
    unfold rest
    refine Finset.sum_congr rfl ?_
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp [Function.update, hji]
  have hnorm_y_sum :
      rest + |s| = ∑ j, |Function.update (ofLp x) i s j| := by
    calc
      rest + |s|
          = Finset.sum (Finset.univ.erase i) (fun j ↦ |Function.update (ofLp x) i s j|)
              + |Function.update (ofLp x) i s i| := by
                rw [← hrest_update]
                simp [Function.update]
      _ = ∑ j, |Function.update (ofLp x) i s j| := by
            exact Finset.sum_erase_add (Finset.univ)
              (fun j ↦ |Function.update (ofLp x) i s j|) (Finset.mem_univ i)
  have hnorm_y : ‖y‖₁ = rest + |s| := by
    -- The updated vector keeps all untouched coordinates inside the common remainder `rest`.
    rw [EuclideanSpace.l1Norm_eq_sum_abs]
    simpa [y] using hnorm_y_sum.symm
  have hnorm_x_sum :
      rest + |ofLp x i| = ∑ j, |ofLp x j| := by
    calc
      rest + |ofLp x i|
          = Finset.sum (Finset.univ.erase i) (fun j ↦ |ofLp x j|) + |ofLp x i| := by
              simp [rest]
      _ = ∑ j, |ofLp x j| := by
            exact Finset.sum_erase_add (Finset.univ)
              (fun j ↦ |ofLp x j|) (Finset.mem_univ i)
  have hnorm_x : ‖x‖₁ = rest + |ofLp x i| := by
    -- Split off the `i`-th coordinate from the original `ℓ₁` norm as well.
    rw [EuclideanSpace.l1Norm_eq_sum_abs]
    exact hnorm_x_sum.symm
  have hpair :
      (toDualMap ℝ E z) (y - x) = ofLp z i * (s - ofLp x i) := by
    -- All untouched coordinates contribute zero to the displacement pairing.
    have hpair_sum :
        ∑ j, ofLp z j * (Function.update (ofLp x) i s j - ofLp x j) =
          ofLp z i * (s - ofLp x i) := by
      let f : ι → ℝ := fun j ↦
        ofLp z j * (Function.update (ofLp x) i s j - ofLp x j)
      have hzero :
          Finset.sum (Finset.univ.erase i) f = 0 := by
        refine Finset.sum_eq_zero ?_
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [Function.update, hji]
      have hsplit :
          ∑ j, f j = Finset.sum (Finset.univ.erase i) f + f i := by
        exact (Finset.sum_erase_add (Finset.univ) f (Finset.mem_univ i)).symm
      calc
        ∑ j, ofLp z j * (Function.update (ofLp x) i s j - ofLp x j)
            = ∑ j, f j := by
                rfl
        _ = Finset.sum (Finset.univ.erase i) f + f i := hsplit
        _ = ofLp z i * (s - ofLp x i) := by
              rw [hzero]
              simp [f, Function.update]
    have hpair_coord :
        (toDualMap ℝ E (toLp 2 (ofLp z))) (y - x) =
          ∑ j, ofLp z j * (ofLp y j - ofLp x j) :=
      coordinatePairing_toLp_sub
    calc
      (toDualMap ℝ E z) (y - x)
          = ∑ j, ofLp z j * (Function.update (ofLp x) i s j - ofLp x j) := by
              simpa [y] using hpair_coord
      _ = ofLp z i * (s - ofLp x i) := hpair_sum
  have hy' :
      |ofLp x i| + ofLp z i * (s - ofLp x i) ≤ |s| := by
    -- After normalizing the shared remainder, only the scalar coordinate inequality remains.
    have hrest :
        rest + (|ofLp x i| + ofLp z i * (s - ofLp x i)) ≤ rest + |s| := by
      simpa [hnorm_y, hnorm_x, hpair, add_assoc, add_left_comm, add_comm] using hy
    exact (add_le_add_iff_left rest).mp hrest
  have hinner_scalar :
      inner ℝ (ofLp z i) (s - ofLp x i) = ofLp z i * (s - ofLp x i) := by
    simpa using (RCLike.inner_apply' (ofLp z i) (s - ofLp x i))
  simpa [InnerProductSpace.toDualMap_apply_apply, hinner_scalar, mul_comm] using hy'

/-- Helper for Proposition 3.17: if every coordinate of `w` is a scalar subgradient of `t ↦ |t|`
at the corresponding coordinate of `x`, then `toLp 2 w` is a Euclidean subgradient of the `ℓ₁`
norm at `x`. -/
lemma toLp_mem_euclideanSubdifferentialAt_l1Norm_of_forall_coordinateScalarSubgradient
    {x : E} {w : ι → ℝ}
    (hw : ∀ i, w i ∈ euclideanSubdifferentialAt (fun t : ℝ ↦ |t|) (ofLp x i)) :
    toLp 2 w ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖y‖₁) x := by
  rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
    mem_subdifferential, is_subgradient_at_coe_iff]
  intro y
  have hcoord :
      ∀ i, |ofLp x i| + w i * (ofLp y i - ofLp x i) ≤ |ofLp y i| := by
    intro i
    have hwi := hw i
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
      mem_subdifferential, is_subgradient_at_coe_iff] at hwi
    -- Specialize the scalar supporting inequality at the `i`-th coordinate of `y`.
    have hinner : inner ℝ (w i) (ofLp y i - ofLp x i) =
        w i * (ofLp y i - ofLp x i) := by
      simpa using (RCLike.inner_apply' (w i) (ofLp y i - ofLp x i))
    have hwi' :
        |ofLp y i| ≥ |ofLp x i| + inner ℝ (w i) (ofLp y i - ofLp x i) := by
      simpa [InnerProductSpace.toDualMap_apply_apply] using hwi (ofLp y i)
    simpa [ge_iff_le, hinner, mul_comm] using hwi'
  have hsum :
      ∑ i, (|ofLp x i| + w i * (ofLp y i - ofLp x i)) ≤ ∑ i, |ofLp y i| := by
    -- Summing the scalar inequalities reassembles the global `ℓ₁` inequality.
    exact Finset.sum_le_sum fun i _ ↦ hcoord i
  have hy :
      ‖x‖₁ + (toDualMap ℝ E (toLp 2 w)) (y - x) ≤ ‖y‖₁ := by
    calc
      ‖x‖₁ + (toDualMap ℝ E (toLp 2 w)) (y - x)
          = ∑ i, |ofLp x i| + ∑ i, w i * (ofLp y i - ofLp x i) := by
              rw [EuclideanSpace.l1Norm_eq_sum_abs, coordinatePairing_toLp_sub]
      _ = ∑ i, (|ofLp x i| + w i * (ofLp y i - ofLp x i)) := by
            rw [Finset.sum_add_distrib]
      _ ≤ ∑ i, |ofLp y i| := hsum
      _ = ‖y‖₁ := by
            rw [EuclideanSpace.l1Norm_eq_sum_abs]
  simpa [ge_iff_le] using hy

/-- Proposition 3.17: for the `ℓ₁` norm
`f(x) = ‖x‖₁ = ∑ i, |ofLp x i|` on `E = EuclideanSpace ℝ ι`, the
Euclidean/vector-side subdifferential consists exactly of the vectors in
`toLp 2 '' l1CoordinateSubgradientVectors (ofLp x)`, i.e. the vectors whose coordinate
representatives equal `Real.sign (ofLp x i)` on the nonzero coordinates of `x` and lie in
`[-1, 1]` on the zero coordinates. -/
theorem subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints
    (x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ ‖y‖₁) x =
      toLp 2 '' l1CoordinateSubgradientVectors (ofLp x) := by
  ext z
  constructor
  · intro hz
    refine ⟨ofLp z, ?_, by simp⟩
    -- Convert the global Euclidean subgradient into coordinatewise scalar subgradients.
    rw [mem_l1CoordinateSubgradientVectors_iff_forall_coordinateScalarSubgradient]
    intro i
    exact coordinateScalarSubgradientOfL1Subgradient hz i
  · rintro ⟨w, hw, rfl⟩
    -- Reassemble the scalar absolute-value subgradients into the full `ℓ₁` subgradient.
    rw [mem_l1CoordinateSubgradientVectors_iff_forall_coordinateScalarSubgradient] at hw
    exact
      toLp_mem_euclideanSubdifferentialAt_l1Norm_of_forall_coordinateScalarSubgradient hw

/-- The Euclidean/vector-side `ℓ₁` subdifferential is the source-facing
coordinate sign cube after passing from a Euclidean vector to its coordinate
representative. -/
@[simp] theorem
    mem_euclideanSubdifferentialAt_l1_norm_iff_ofLp_mem_l1CoordinateSubgradientVectors
    {x z : E} :
    z ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖y‖₁) x ↔
      ofLp z ∈ l1CoordinateSubgradientVectors (ofLp x) := by
  rw [subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa using hw
  · intro hz
    exact ⟨ofLp z, hz, by simp⟩

/-- Membership in the Euclidean/vector-side subdifferential of the `ℓ₁` norm is exactly the
coordinatewise sign-cube condition. This is the callable companion form of
`subdifferentialAt_l1_norm_eq_coordinatewise_sign_constraints`. -/
@[simp] theorem mem_euclideanSubdifferentialAt_l1_norm_iff
    {x z : E} :
    z ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖y‖₁) x ↔
      (∀ i, ofLp x i ≠ 0 → ofLp z i = Real.sign (ofLp x i)) ∧
        ∀ i, ofLp x i = 0 → |ofLp z i| ≤ 1 := by
  rw [mem_euclideanSubdifferentialAt_l1_norm_iff_ofLp_mem_l1CoordinateSubgradientVectors,
    mem_l1CoordinateSubgradientVectors_iff]

end
