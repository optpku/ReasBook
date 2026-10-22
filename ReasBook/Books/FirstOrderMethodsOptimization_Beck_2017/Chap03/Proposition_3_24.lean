/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_23
import FirstOrderMethodsOptimization_Beck_2017.Chap06.EuclideanL1Norm

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp ofLp)
open scoped BigOperators
open InnerProductSpace (toDualMap)

universe u

section

variable {ι : Type u} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/-- Helper for Proposition 3.24: every coordinate of a finite real-valued function is bounded by
its `ℓ∞` norm. -/
lemma abs_le_pi_norm (a : ι → ℝ) (i : ι) :
    |a i| ≤ ‖a‖ := by
  -- Rewrite the sup norm as the finite supremum of coordinate norms.
  have hcoord_nnnorm : ‖a i‖₊ ≤ ‖a‖₊ := by
    rw [Pi.nnnorm_def]
    let f : ι → NNReal := fun j ↦ ‖a j‖₊
    change f i ≤ Finset.univ.sup f
    exact Finset.le_sup (by simp)
  have hcoord : ‖a i‖ ≤ ‖a‖ := by
    exact_mod_cast hcoord_nnnorm
  simpa [Real.norm_eq_abs] using hcoord

/-- Helper for Proposition 3.24: coordinatewise bounds by `1` imply an `ℓ∞` norm bound by `1`. -/
lemma piNorm_le_one_of_abs_le_one
    {a : ι → ℝ} (ha : ∀ i, |a i| ≤ 1) :
    ‖a‖ ≤ 1 := by
  -- Reassemble the sup bound from the coordinatewise inequalities.
  have hnnnorm : ‖a‖₊ ≤ 1 := by
    rw [Pi.nnnorm_def]
    refine Finset.sup_le ?_
    intro i hi
    have hcoord : ‖a i‖ ≤ 1 := by
      simpa [Real.norm_eq_abs] using ha i
    exact_mod_cast hcoord
  exact_mod_cast hnnnorm

/-- Helper for Proposition 3.24: in `ℝ`, multiplying by `Real.sign` recovers the absolute value.
-/
lemma real_sign_mul_self
    (t : ℝ) :
    Real.sign t * t = |t| := by
  -- Split into the negative, zero, and positive scalar cases.
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · simp [Real.sign_of_neg hneg, abs_of_neg hneg]
  · simp
  · simp [Real.sign_of_pos hpos, abs_of_pos hpos]

/-- Helper for Proposition 3.24: the Euclidean/Riesz pairing is the coordinate dot product. -/
private lemma toDualMap_apply_eq_dotProduct (u v : E) :
    ((toDualMap ℝ E v) u : ℝ) = dotProduct (ofLp u) (ofLp v) := by
  -- Convert the Euclidean inner product to coordinates.
  simpa [InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
    (EuclideanSpace.inner_toLp_toLp (ofLp v) (ofLp u))

/-- Helper for Proposition 3.24: pairing against a translated point splits into a dot-product
difference. -/
lemma toDualMap_apply_sub_eq_dotProduct_sub
    (x z y : E) :
    ((toDualMap ℝ E z) (y - x) : ℝ) =
      dotProduct (ofLp y) (ofLp z) - dotProduct (ofLp x) (ofLp z) := by
  -- Expand the pairing on the translated vector and separate the two dot products.
  rw [toDualMap_apply_eq_dotProduct]
  simp [sub_eq_add_neg, add_dotProduct, neg_dotProduct]

/-- Helper for Proposition 3.24: in `ℝ≥0`, a maximizing coordinate realizes the finite supremum
of the coordinate norms. -/
lemma finiteSupNnnormEqOfCoordinateMaximizer
    (a : ι → ℝ) (i : ι) (hmax : ∀ j : ι, |a j| ≤ |a i|) :
    Finset.univ.sup (fun j : ι ↦ ‖a j‖₊) = ‖a i‖₊ := by
  -- Compare the finite supremum directly with the chosen maximizing coordinate.
  refine le_antisymm (Finset.sup_le ?_) ?_
  · intro j hj
    exact_mod_cast hmax j
  · let f : ι → NNReal := fun j ↦ ‖a j‖₊
    change f i ≤ Finset.univ.sup f
    exact Finset.le_sup (by simp)

section NonemptyIndex

variable [Nonempty ι]

omit [Nonempty ι] in
/-- Helper for Proposition 3.24: a coordinate maximizing `|a i|` realizes the `ℓ∞` norm of `a`.
-/
lemma piNorm_eq_abs_of_coordinateMaximizer
    (a : ι → ℝ) (i : ι) (hmax : ∀ j : ι, |a j| ≤ |a i|) :
    ‖a‖ = |a i| := by
  -- Rewrite the `ℓ∞` norm as the finite supremum of the coordinate norms.
  rw [Pi.norm_def, finiteSupNnnormEqOfCoordinateMaximizer a i hmax]
  simp [Real.norm_eq_abs]

/-- Helper for Proposition 3.24: `coordinatewiseMax (fun i ↦ |x i|)` is the ambient `ℓ∞` norm.
-/
lemma coordinatewiseMax_abs_eq_linf (x : E) :
    coordinatewiseMax (fun i ↦ |ofLp x i|) = ‖ofLp x‖ := by
  classical
  -- Choose a coordinate with maximal absolute value and compare both max descriptions to it.
  obtain ⟨i, hi⟩ :=
    Finset.exists_maximalFor
      (fun j : ι ↦ ‖ofLp x j‖₊) Finset.univ Finset.univ_nonempty
  have hmax : ∀ j : ι, |ofLp x j| ≤ |ofLp x i| := by
    intro j
    have hle_nnnorm : ‖ofLp x j‖₊ ≤ ‖ofLp x i‖₊ :=
      hi.le (by simp)
    have hle_norm : ‖ofLp x j‖ ≤ ‖ofLp x i‖ := by
      exact_mod_cast hle_nnnorm
    simpa [Real.norm_eq_abs] using hle_norm
  calc
    coordinatewiseMax (fun j ↦ |ofLp x j|) = |ofLp x i| := by
      rw [coordinatewiseMax_eq_sup']
      refine le_antisymm ?_ ?_
      · exact
          Finset.sup'_le Finset.univ_nonempty (fun j : ι ↦ |ofLp x j|) <|
            by
              intro j hj
              exact hmax j
      · exact
          Finset.le_sup' (fun j : ι ↦ |ofLp x j|) (Finset.mem_univ i)
    _ = ‖ofLp x‖ := (piNorm_eq_abs_of_coordinateMaximizer (ofLp x) i hmax).symm

end NonemptyIndex

/-- Helper for Proposition 3.24: an `ℓ₁`-unit vector pairs with every `ℓ∞` vector by at most the
`ℓ∞` norm. -/
lemma dotProduct_le_linf_of_l1_norm_le_one
    (z : E) (hz : ‖z‖₁ ≤ 1) (v : ι → ℝ) :
    dotProduct v (ofLp z) ≤ ‖v‖ := by
  -- Bound each coordinate contribution by the sup norm and then sum the `ℓ₁` coefficients.
  have hnorm_l1 : ‖z‖₁ = ∑ i, |ofLp z i| := by
    change ‖z‖₁ = ∑ i, |z i|
    exact EuclideanSpace.l1Norm_eq_sum_abs z
  calc
    dotProduct v (ofLp z) = ∑ i, v i * ofLp z i := by
      rfl
    _ ≤ ∑ i, |v i| * |ofLp z i| := by
      refine Finset.sum_le_sum ?_
      intro i hi
      simpa [abs_mul] using (le_abs_self (v i * ofLp z i))
    _ ≤ ∑ i, ‖v‖ * |ofLp z i| := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact mul_le_mul_of_nonneg_right (abs_le_pi_norm v i) (abs_nonneg _)
    _ = ‖v‖ * ∑ i, |ofLp z i| := by
      rw [Finset.mul_sum]
    _ = ‖v‖ * ‖z‖₁ := by
      rw [hnorm_l1]
    _ ≤ ‖v‖ * 1 := by
      gcongr
    _ = ‖v‖ := by
      ring

/-- Helper for Proposition 3.24: a vector whose pairing is bounded by the `ℓ∞` norm has `ℓ₁`
norm at most `1`. -/
lemma l1_norm_le_one_of_dotProduct_le_linf
    (z : E) (hz : ∀ v : ι → ℝ, dotProduct v (ofLp z) ≤ ‖v‖) :
    ‖z‖₁ ≤ 1 := by
  -- Test the support inequality on the coordinatewise sign vector of `z`.
  have hsign_norm : ‖fun i : ι ↦ Real.sign (ofLp z i)‖ ≤ 1 := by
    refine piNorm_le_one_of_abs_le_one ?_
    intro i
    rcases lt_trichotomy (ofLp z i) 0 with hneg | hzero | hpos
    · simp [Real.sign_of_neg hneg]
    · simp [hzero]
    · simp [Real.sign_of_pos hpos]
  have hpair :
      dotProduct (fun i : ι ↦ Real.sign (ofLp z i)) (ofLp z) =
        ‖z‖₁ := by
    calc
      dotProduct (fun i : ι ↦ Real.sign (ofLp z i)) (ofLp z) =
          ∑ i, Real.sign (ofLp z i) * ofLp z i := by
            rfl
      _ = ∑ i, |ofLp z i| := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact real_sign_mul_self (ofLp z i)
      _ = ‖z‖₁ := by
            exact (EuclideanSpace.l1Norm_eq_sum_abs z).symm
  calc
    ‖z‖₁ =
        dotProduct (fun i : ι ↦ Real.sign (ofLp z i)) (ofLp z) := hpair.symm
    _ ≤ ‖fun i : ι ↦ Real.sign (ofLp z i)‖ := hz _
    _ ≤ 1 := hsign_norm

/-- Helper for Proposition 3.24: Euclidean subgradients of `x ↦ ‖ofLp x‖` are exactly the
`ℓ₁`-unit vectors that attain the support value at the base point. -/
lemma mem_euclideanSubdifferentialAt_linf_iff
    {x z : E} :
    z ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖ofLp y‖) x ↔
      ‖z‖₁ ≤ 1 ∧ (toDualMap ℝ E z) x = ‖ofLp x‖ := by
  constructor
  · intro hz
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
      mem_subdifferential, is_subgradient_at_coe_iff] at hz
    -- Test the subgradient inequality at `0` and `2 • x` to recover the support equality.
    have hzero : ‖ofLp (0 : E)‖ ≥ ‖ofLp x‖ + (toDualMap ℝ E z) (0 - x) := hz 0
    have hge : ‖ofLp x‖ ≤ (toDualMap ℝ E z) x := by
      have hzero' : 0 ≥ ‖ofLp x‖ - (toDualMap ℝ E z) x := by
        simpa using hzero
      linarith
    have htwo : ‖ofLp ((2 : ℝ) • x)‖ ≥ ‖ofLp x‖ + (toDualMap ℝ E z) ((2 : ℝ) • x - x) := by
      simpa using hz ((2 : ℝ) • x)
    have hle : (toDualMap ℝ E z) x ≤ ‖ofLp x‖ := by
      have htwo' : ‖ofLp x + ofLp x‖ ≥ ‖ofLp x‖ + (toDualMap ℝ E z) x := by
        simpa [two_smul] using htwo
      have hnorm2 : ‖ofLp x + ofLp x‖ = 2 * ‖ofLp x‖ := by
        simpa [two_smul] using (norm_smul (2 : ℝ) (ofLp x))
      have htwo'' : 2 * ‖ofLp x‖ ≥ ‖ofLp x‖ + (toDualMap ℝ E z) x := by
        rw [← hnorm2]
        exact htwo'
      linarith
    have hpairEq : (toDualMap ℝ E z) x = ‖ofLp x‖ := le_antisymm hle hge
    -- Rewrite the translated affine inequality as the dual support bound.
    have hsupport : ∀ v : ι → ℝ, dotProduct v (ofLp z) ≤ ‖v‖ := by
      intro v
      have hv : ‖ofLp (toLp 2 v)‖ ≥ ‖ofLp x‖ + (toDualMap ℝ E z) (toLp 2 v - x) := by
        simpa using hz (toLp 2 v)
      have hpairv :
          (toDualMap ℝ E z) (toLp 2 v - x) =
            dotProduct v (ofLp z) - ‖ofLp x‖ := by
        calc
          (toDualMap ℝ E z) (toLp 2 v - x) =
              dotProduct (ofLp (toLp 2 v)) (ofLp z) - dotProduct (ofLp x) (ofLp z) := by
                simpa using toDualMap_apply_sub_eq_dotProduct_sub x z (toLp 2 v)
          _ = dotProduct v (ofLp z) - dotProduct (ofLp x) (ofLp z) := by
                simp
          _ = dotProduct v (ofLp z) - (toDualMap ℝ E z) x := by
                rw [toDualMap_apply_eq_dotProduct]
          _ = dotProduct v (ofLp z) - ‖ofLp x‖ := by
                rw [hpairEq]
      calc
        dotProduct v (ofLp z) = ‖ofLp x‖ + (toDualMap ℝ E z) (toLp 2 v - x) := by
          rw [hpairv]
          ring
        _ ≤ ‖ofLp (toLp 2 v)‖ := hv
        _ = ‖v‖ := by
          simp
    exact ⟨l1_norm_le_one_of_dotProduct_le_linf z hsupport, hpairEq⟩
  · rintro ⟨hzNorm, hpairEq⟩
    rw [mem_euclideanSubdifferentialAt_iff, subdifferentialAt, mem_strongDualSubdifferential,
      mem_subdifferential, is_subgradient_at_coe_iff]
    intro y
    -- Combine the dual support bound with the attained support value at `x`.
    have hySupport : dotProduct (ofLp y) (ofLp z) ≤ ‖ofLp y‖ :=
      dotProduct_le_linf_of_l1_norm_le_one z hzNorm (ofLp y)
    have hpairy :
        (toDualMap ℝ E z) (y - x) = dotProduct (ofLp y) (ofLp z) - ‖ofLp x‖ := by
      calc
        (toDualMap ℝ E z) (y - x) =
            dotProduct (ofLp y) (ofLp z) - dotProduct (ofLp x) (ofLp z) := by
              simpa using toDualMap_apply_sub_eq_dotProduct_sub x z y
        _ = dotProduct (ofLp y) (ofLp z) - (toDualMap ℝ E z) x := by
              rw [toDualMap_apply_eq_dotProduct]
        _ = dotProduct (ofLp y) (ofLp z) - ‖ofLp x‖ := by
              rw [hpairEq]
    calc
      ‖ofLp y‖ ≥ dotProduct (ofLp y) (ofLp z) := hySupport
      _ = ‖ofLp x‖ + (toDualMap ℝ E z) (y - x) := by
            rw [hpairy]
            ring

/-- Helper for Proposition 3.24: at the origin, membership in the `ℓ∞` subdifferential is exactly
the `ℓ₁` unit-ball condition. -/
lemma mem_euclideanSubdifferentialAt_linf_zero_iff_l1_norm_le_one
    {z : E} :
    z ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖ofLp y‖) (0 : E) ↔
      ‖z‖₁ ≤ 1 := by
  -- Specialize the support-value characterization to the origin.
  rw [mem_euclideanSubdifferentialAt_linf_iff]
  simp

omit [Fintype ι] in
/-- Helper for Proposition 3.24: a nonzero coordinate vector forces the index type to be
nonempty. -/
lemma nonemptyIndex_of_ne_zero
    {x : E} (hx : x ≠ 0) :
    Nonempty ι := by
  classical
  by_contra hι
  apply hx
  ext i
  exact (hι ⟨i⟩).elim

/-- Helper for Proposition 3.24: any signed active-coordinate simplex vector is a valid Euclidean
subgradient of the `ℓ∞` norm. -/
lemma signedActiveVector_mem_euclideanSubdifferentialAt_linf_of_mem_activeCoordinateFace
    {x : E} (hx : x ≠ 0) {coeff : ι → ℝ}
    (hcoeff : coeff ∈ activeCoordinateFace (fun i ↦ |ofLp x i|)) :
    toLp 2 (fun i ↦ coeff i * Real.sign (ofLp x i)) ∈
      euclideanSubdifferentialAt (fun y : E ↦ ‖ofLp y‖) x := by
  classical
  letI : Nonempty ι := nonemptyIndex_of_ne_zero hx
  rcases mem_activeCoordinateFace_iff.mp hcoeff with ⟨hSimplex, hInactive⟩
  -- First check the `ℓ₁` unit-ball constraint on the signed vector.
  have hzNorm :
      ‖toLp 1 (ofLp (toLp 2 fun i ↦ coeff i * Real.sign (ofLp x i)))‖ ≤ 1 := by
    calc
      ‖toLp 1 (ofLp (toLp 2 fun i ↦ coeff i * Real.sign (ofLp x i)))‖ =
          ∑ i, |coeff i * Real.sign (ofLp x i)| := by
            simp [Real.norm_eq_abs, PiLp.norm_eq_of_L1]
      _ ≤ ∑ i, coeff i := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hcoeff_nonneg : 0 ≤ coeff i := hSimplex.1 i
            have hsign_le_one : |Real.sign (ofLp x i)| ≤ 1 := by
              rcases lt_trichotomy (ofLp x i) 0 with hneg | hzero | hpos
              · simp [Real.sign_of_neg hneg]
              · simp [hzero]
              · simp [Real.sign_of_pos hpos]
            calc
              |coeff i * Real.sign (ofLp x i)| = coeff i * |Real.sign (ofLp x i)| := by
                rw [abs_mul, abs_of_nonneg hcoeff_nonneg]
              _ ≤ coeff i * 1 := mul_le_mul_of_nonneg_left hsign_le_one hcoeff_nonneg
              _ = coeff i := by ring
      _ = 1 := hSimplex.2
  -- Then compute the supporting value exactly on the active coordinates.
  have hweighted :
      ∑ i, coeff i * |ofLp x i| = coordinatewiseMax (fun i ↦ |ofLp x i|) := by
    calc
      ∑ i, coeff i * |ofLp x i| =
          ∑ i, coeff i * coordinatewiseMax (fun j ↦ |ofLp x j|) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            by_cases hactive : coordinatewiseMax (fun j ↦ |ofLp x j|) = |ofLp x i|
            · rw [hactive]
            · simp [hInactive i hactive]
      _ = (∑ i, coeff i) * coordinatewiseMax (fun j ↦ |ofLp x j|) := by
            rw [Finset.sum_mul]
      _ = coordinatewiseMax (fun i ↦ |ofLp x i|) := by
            rw [hSimplex.2, one_mul]
  have hpair :
      (toDualMap ℝ E (toLp 2 fun i ↦ coeff i * Real.sign (ofLp x i))) x = ‖ofLp x‖ := by
    -- Rewrite the pairing as the weighted sum of the active absolute values.
    calc
      (toDualMap ℝ E (toLp 2 fun i ↦ coeff i * Real.sign (ofLp x i))) x =
          dotProduct (ofLp x) (fun i ↦ coeff i * Real.sign (ofLp x i)) := by
            rw [toDualMap_apply_eq_dotProduct]
      _ = ∑ i, coeff i * |ofLp x i| := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              ofLp x i * (coeff i * Real.sign (ofLp x i)) =
                  coeff i * (Real.sign (ofLp x i) * ofLp x i) := by
                    ring
              _ = coeff i * |ofLp x i| := by
                    rw [real_sign_mul_self]
      _ = coordinatewiseMax (fun i ↦ |ofLp x i|) := hweighted
      _ = ‖ofLp x‖ := coordinatewiseMax_abs_eq_linf x
  rw [mem_euclideanSubdifferentialAt_linf_iff]
  exact ⟨hzNorm, hpair⟩

/-- Helper for Proposition 3.24: a nonzero Euclidean subgradient of the `ℓ∞` norm is obtained by
taking the absolute coefficients, which form the active-coordinate simplex face. -/
lemma absCoeff_mem_activeCoordinateFace_of_mem_euclideanSubdifferentialAt_linf
    {x z : E} (hx : x ≠ 0)
    (hz : z ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖ofLp y‖) x) :
    let coeff : ι → ℝ := fun i ↦ |ofLp z i|
    coeff ∈ activeCoordinateFace (fun i ↦ |ofLp x i|) ∧
      z = toLp 2 (fun i ↦ coeff i * Real.sign (ofLp x i)) := by
  classical
  letI : Nonempty ι := nonemptyIndex_of_ne_zero hx
  let coeff : ι → ℝ := fun i ↦ |ofLp z i|
  rw [mem_euclideanSubdifferentialAt_linf_iff] at hz
  have hz' := hz
  have hzNorm : ‖z‖₁ ≤ 1 := hz'.1
  have hpair : dotProduct (ofLp x) (ofLp z) = ‖ofLp x‖ := by
    simpa [toDualMap_apply_eq_dotProduct] using hz'.2
  have hxnorm_pos : 0 < ‖ofLp x‖ := by
    have hx' : ofLp x ≠ 0 := by
      simpa using hx
    exact norm_pos_iff.mpr hx'
  have hsum_coeff_le_one : ∑ i, coeff i ≤ 1 := by
    have hnorm_l1 : ‖z‖₁ = ∑ i, coeff i := by
      change ‖z‖₁ = ∑ i, |z i|
      exact EuclideanSpace.l1Norm_eq_sum_abs z
    rw [hnorm_l1] at hzNorm
    exact hzNorm
  have hdot_le :
      dotProduct (ofLp x) (ofLp z) ≤ ∑ i, |ofLp x i| * coeff i := by
    -- Replace each coordinate product by its absolute value.
    calc
      dotProduct (ofLp x) (ofLp z) = ∑ i, ofLp x i * ofLp z i := by
        rfl
      _ ≤ ∑ i, |ofLp x i| * coeff i := by
            refine Finset.sum_le_sum ?_
            intro i hi
            dsimp [coeff]
            simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using
              (le_abs_self (ofLp x i * ofLp z i))
  have habs_le :
      ∑ i, |ofLp x i| * coeff i ≤ ‖ofLp x‖ * ∑ i, coeff i := by
    -- Bound each active absolute value by the ambient `ℓ∞` norm.
    calc
      ∑ i, |ofLp x i| * coeff i ≤ ∑ i, ‖ofLp x‖ * coeff i := by
            refine Finset.sum_le_sum ?_
            intro i hi
            dsimp [coeff]
            exact mul_le_mul_of_nonneg_right (abs_le_pi_norm (ofLp x) i) (abs_nonneg _)
      _ = ‖ofLp x‖ * ∑ i, coeff i := by
            rw [Finset.mul_sum]
  have hsum_coeff_eq_one : ∑ i, coeff i = 1 := by
    have hge_one : 1 ≤ ∑ i, coeff i := by
      have hbound : ‖ofLp x‖ ≤ ‖ofLp x‖ * ∑ i, coeff i := by
        exact le_trans (by simpa [hpair] using hdot_le) habs_le
      nlinarith
    linarith
  have hsum_abs_eq : ∑ i, |ofLp x i| * coeff i = ‖ofLp x‖ := by
    refine le_antisymm ?_ ?_
    · calc
        ∑ i, |ofLp x i| * coeff i ≤ ‖ofLp x‖ * ∑ i, coeff i := habs_le
        _ = ‖ofLp x‖ := by
              rw [hsum_coeff_eq_one, mul_one]
    · simpa [hpair] using hdot_le
  have hgap_zero :
      ∀ i, coeff i * (‖ofLp x‖ - |ofLp x i|) = 0 := by
    -- Equality in the weighted upper bound forces every inactive coefficient to vanish.
    have hnonneg :
        ∀ i, 0 ≤ coeff i * (‖ofLp x‖ - |ofLp x i|) := by
      intro i
      dsimp [coeff]
      exact mul_nonneg (abs_nonneg _) (sub_nonneg.mpr (abs_le_pi_norm (ofLp x) i))
    have hsum_zero :
        ∑ i, coeff i * (‖ofLp x‖ - |ofLp x i|) = 0 := by
      calc
        ∑ i, coeff i * (‖ofLp x‖ - |ofLp x i|) =
            ∑ i, (coeff i * ‖ofLp x‖ - coeff i * |ofLp x i|) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = ∑ i, coeff i * ‖ofLp x‖ - ∑ i, coeff i * |ofLp x i| := by
              rw [Finset.sum_sub_distrib]
        _ = ‖ofLp x‖ * ∑ i, coeff i - ∑ i, |ofLp x i| * coeff i := by
              simp_rw [mul_comm (coeff _) ‖ofLp x‖, mul_comm (coeff _) (|ofLp x _|)]
              rw [Finset.mul_sum]
        _ = 0 := by
              rw [hsum_coeff_eq_one, hsum_abs_eq]
              ring
    have hgap_fun : (fun i ↦ coeff i * (‖ofLp x‖ - |ofLp x i|)) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum_zero
    intro i
    exact congrFun hgap_fun i
  have hsignGap_zero :
      ∀ i, |ofLp x i| * coeff i - ofLp x i * ofLp z i = 0 := by
    -- Equality in the absolute-value bound fixes the sign on every active coordinate.
    have hnonneg :
        ∀ i, 0 ≤ |ofLp x i| * coeff i - ofLp x i * ofLp z i := by
      intro i
      dsimp [coeff]
      exact sub_nonneg.mpr <| by
        simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using
          (le_abs_self (ofLp x i * ofLp z i))
    have hsum_zero :
        ∑ i, (|ofLp x i| * coeff i - ofLp x i * ofLp z i) = 0 := by
      have hsum_prod : ∑ i, ofLp x i * ofLp z i = ‖ofLp x‖ := by
        simpa [dotProduct] using hpair
      calc
        ∑ i, (|ofLp x i| * coeff i - ofLp x i * ofLp z i) =
            ∑ i, |ofLp x i| * coeff i - ∑ i, ofLp x i * ofLp z i := by
              rw [Finset.sum_sub_distrib]
        _ = 0 := by
              rw [hsum_abs_eq, hsum_prod]
              simp
    have hsign_fun : (fun i ↦ |ofLp x i| * coeff i - ofLp x i * ofLp z i) = 0 :=
      (Fintype.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum_zero
    intro i
    exact congrFun hsign_fun i
  have hcoeff_face : coeff ∈ activeCoordinateFace (fun i ↦ |ofLp x i|) := by
    rw [mem_activeCoordinateFace_iff]
    refine ⟨?_, ?_⟩
    · -- The absolute coefficients form a simplex vector.
      exact ⟨fun i ↦ abs_nonneg _, hsum_coeff_eq_one⟩
    · intro i hiInactive
      have hneqNorm : |ofLp x i| ≠ ‖ofLp x‖ := by
        intro hEq
        apply hiInactive
        calc
          coordinatewiseMax (fun j ↦ |ofLp x j|) = ‖ofLp x‖ := coordinatewiseMax_abs_eq_linf x
          _ = |ofLp x i| := hEq.symm
      have hlt : |ofLp x i| < ‖ofLp x‖ :=
        lt_of_le_of_ne (abs_le_pi_norm (ofLp x) i) hneqNorm
      have hgap_pos : 0 < ‖ofLp x‖ - |ofLp x i| := sub_pos.mpr hlt
      rcases mul_eq_zero.mp (hgap_zero i) with hcoeff_zero | hgap_eq_zero
      · exact hcoeff_zero
      · linarith
  have hz_coord :
      ∀ i, ofLp z i = coeff i * Real.sign (ofLp x i) := by
    intro i
    by_cases hactive : coordinatewiseMax (fun j ↦ |ofLp x j|) = |ofLp x i|
    · -- On an active coordinate, equality in the product bound forces the correct sign.
      have hxi_ne : ofLp x i ≠ 0 := by
        apply abs_ne_zero.mp
        have hpos : 0 < |ofLp x i| := by
          calc
            0 < coordinatewiseMax (fun j ↦ |ofLp x j|) := by
                  simpa [coordinatewiseMax_abs_eq_linf x] using hxnorm_pos
            _ = |ofLp x i| := hactive
        exact hpos.ne'
      have hprod_eq : |ofLp x i| * coeff i = ofLp x i * ofLp z i := by
        linarith [hsignGap_zero i]
      have htarget :
          (coeff i * Real.sign (ofLp x i)) * ofLp x i = ofLp z i * ofLp x i := by
        calc
          (coeff i * Real.sign (ofLp x i)) * ofLp x i = coeff i * |ofLp x i| := by
                rw [mul_assoc, real_sign_mul_self]
          _ = ofLp z i * ofLp x i := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using hprod_eq
      exact (mul_right_cancel₀ hxi_ne htarget).symm
    · -- On an inactive coordinate, the coefficient and the coordinate both vanish.
      have hcoeff_zero : coeff i = 0 := by
        exact hcoeff_face.2 i hactive
      have hz_zero : ofLp z i = 0 := by
        exact abs_eq_zero.mp (by simpa [coeff] using hcoeff_zero)
      simp [coeff, hcoeff_zero, hz_zero]
  -- Repackage the recovered absolute coefficients and sign constraints.
  dsimp [coeff]
  refine ⟨hcoeff_face, ?_⟩
  ext i
  simpa using hz_coord i

/- Proposition 3.24 is a `bridge/view` item for the Chapter 3 owner `subdifferentialAt`, and its
public vector-side owner is `euclideanSubdifferentialAt`. Proposition 3.23 already identifies the
coordinatewise-max Euclidean subdifferential with `activeCoordinateFace`; the only additional
source-facing content here is the signed active-coordinate description of the `ℓ∞`
subdifferential. The zero case is stated directly using the canonical Euclidean `ℓ₁` unit ball on
`ℝ^n`, so no extra wrapper is introduced. -/
-- Semantic recall note: `lean_leansearch` returned no specialized reusable theorem for this
-- `ℓ∞` subdifferential formula, so the statement stays chapter-local via Proposition 3.23.

-- Proof sketch: on `Fin n → ℝ`, the ambient norm is the `ℓ∞` norm, so the objective is
-- `x ↦ ‖x‖ = max_i |x i|`. Apply the max rule to the family `x ↦ |x i|` and use Proposition 3.23
-- for the resulting active simplex face. At `x = 0`, every coordinate is active and the convex hull
-- of the signed coordinate vectors is exactly the canonical Euclidean `ℓ₁` unit ball
-- `{z | ‖z‖₁ ≤ 1}`.
/-- Proposition 3.24: for `f(x) = ‖x‖∞ = ‖x‖` on `ℝ^n = Fin n → ℝ`, the Euclidean/vector-side
subdifferential is the `ℓ₁` unit ball `{z | ‖z‖₁ ≤ 1}` at the origin, and away from the
origin it is the set of convex
combinations `∑_{i ∈ I(x)} λ_i sign (x_i) e_i` supported on the active coordinates
`I(x) = {i | |x i| = ‖x‖∞}`. -/
theorem euclidean_subdifferentialAt_linf_eq_piecewise
    (x : E) :
    euclideanSubdifferentialAt (fun y : E ↦ ‖ofLp y‖) x =
      if x = 0 then
        {z : E | ‖z‖₁ ≤ 1}
      else
        (fun coeff : ι → ℝ ↦ toLp 2 fun i ↦ coeff i * Real.sign (ofLp x i)) ''
          activeCoordinateFace (fun i ↦ |ofLp x i|) := by
  by_cases hx : x = 0
  · -- The origin branch is exactly the `ℓ₁` unit-ball characterization.
    subst x
    rw [if_pos rfl]
    ext z
    exact mem_euclideanSubdifferentialAt_linf_zero_iff_l1_norm_le_one
  · -- Away from the origin, convert both directions through the signed active-face helpers.
    rw [if_neg hx]
    ext z
    constructor
    · intro hz
      have hz' :=
        absCoeff_mem_activeCoordinateFace_of_mem_euclideanSubdifferentialAt_linf
          hx hz
      dsimp at hz'
      rcases hz' with ⟨hcoeff, hzEq⟩
      refine ⟨fun i ↦ |ofLp z i|, hcoeff, hzEq.symm⟩
    · rintro ⟨coeff, hcoeff, rfl⟩
      exact
        signedActiveVector_mem_euclideanSubdifferentialAt_linf_of_mem_activeCoordinateFace
          hx hcoeff

/-- Away from the origin, membership in the Euclidean/vector-side subdifferential of `x ↦ ‖x‖∞`
is exactly the signed active-coordinate parametrization from Proposition 3.23. -/
theorem mem_euclideanSubdifferentialAt_linf_iff_exists_signed_activeCoordinateFace
    {x z : E} (hx : x ≠ 0) :
    z ∈ euclideanSubdifferentialAt (fun y : E ↦ ‖ofLp y‖) x ↔
      ∃ coeff : ι → ℝ,
        coeff ∈ activeCoordinateFace (fun i ↦ |ofLp x i|) ∧
          z = toLp 2 (fun i ↦ coeff i * Real.sign (ofLp x i)) := by
  rw [euclidean_subdifferentialAt_linf_eq_piecewise x, if_neg hx, Set.mem_image]
  constructor
  · rintro ⟨coeff, hcoeff, hz⟩
    exact ⟨coeff, hcoeff, hz.symm⟩
  · rintro ⟨coeff, hcoeff, hz⟩
    exact ⟨coeff, hcoeff, hz.symm⟩

/-- At the origin, the Euclidean/vector-side subdifferential of `x ↦ ‖x‖∞` is the canonical
`ℓ₁` unit ball in `EuclideanSpace ℝ ι`. -/
@[simp] theorem euclidean_subdifferentialAt_linf_zero_eq_l1_unitBall :
    euclideanSubdifferentialAt (fun y : E ↦ ‖ofLp y‖) (0 : E) =
      {z : E | ‖z‖₁ ≤ 1} := by
  simpa using euclidean_subdifferentialAt_linf_eq_piecewise (0 : E)

/-- Away from the origin, the Euclidean/vector-side subdifferential of `x ↦ ‖x‖∞` is the signed
active-coordinate face from Proposition 3.23. -/
theorem euclidean_subdifferentialAt_linf_eq_signed_activeCoordinateFace
    (x : E) (hx : x ≠ 0) :
    euclideanSubdifferentialAt (fun y : E ↦ ‖ofLp y‖) x =
      (fun coeff : ι → ℝ ↦ toLp 2 fun i ↦ coeff i * Real.sign (ofLp x i)) ''
        activeCoordinateFace (fun i ↦ |ofLp x i|) := by
  simpa [hx] using euclidean_subdifferentialAt_linf_eq_piecewise x

end
