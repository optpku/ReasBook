/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Example_6_25
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_28

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

section

variable {I : Type u}

local notation "L2" => lp (fun _ : I ↦ ℝ) 2

/-- The coordinatewise nonnegative cone in `ℓ²(I, ℝ)`. -/
def l2PositiveOrthant (I : Type u) : Set (lp (fun _ : I ↦ ℝ) 2) :=
  {y | ∀ i, 0 ≤ y i}

-- Proof sketch: for every coordinate, `|max (x i) 0| ≤ |x i|`; compare the defining `ℓ²`-series
-- termwise with that of `x` and apply the domination criterion for `Memℓp`.
/-- The coordinatewise positive part of a square-summable real family is again square-summable. -/
theorem memℓp_max_zero (x : L2) :
    Memℓp (fun i ↦ max (x i) 0) 2 := by
  -- Rewrite the positive part as the average of the vector and its coordinatewise absolute value.
  have hxmem : Memℓp (fun i ↦ x i) 2 := x.2
  have hp : 0 < ENNReal.toReal (2 : ENNReal) := by
    norm_num
  have hsumm : Summable (fun i ↦ ‖x i‖ ^ (2 : ℝ)) := by
    simpa using hxmem.summable hp
  have habs : Memℓp (fun i ↦ |x i|) 2 := by
    apply memℓp_gen
    simpa [Real.norm_eq_abs] using hsumm
  have hadd : Memℓp (fun i ↦ x i + |x i|) 2 := hxmem.add habs
  have hsmul : Memℓp (fun i ↦ (2 : ℝ)⁻¹ * (x i + |x i|)) 2 := hadd.const_mul ((2 : ℝ)⁻¹)
  -- Simplify the coordinate formula back to `max (x i) 0`.
  convert hsmul using 1
  funext i
  rw [sup_eq_half_smul_add_add_abs_sub' ℝ]
  simp [sub_eq_add_neg, add_comm]

/-- The coordinatewise positive part of an `ℓ²` vector. -/
def l2PositivePart (x : L2) : L2 :=
  ⟨fun i ↦ max (x i) 0, memℓp_max_zero x⟩

-- Proof sketch: unfold `l2PositivePart`; the subtype is built from the function
-- `fun i ↦ max (x i) 0`, so evaluation at each coordinate gives that same value.
/-- The coordinates of the positive-part vector are the positive parts of the original
coordinates. -/
theorem l2PositivePart_apply (x : L2) (i : I) :
    l2PositivePart x i = max (x i) 0 := by
  -- Unfolding the subtype definition exposes the coordinate formula immediately.
  rfl

-- Proof sketch: the zero vector has every coordinate equal to `0`, hence it belongs to the
-- coordinatewise nonnegative cone.
/-- The coordinatewise nonnegative cone in `ℓ²(I, ℝ)` is nonempty. -/
theorem l2PositiveOrthant_nonempty : Set.Nonempty (l2PositiveOrthant I) := by
  -- The zero vector lies in the orthant coordinatewise.
  refine ⟨(0 : L2), ?_⟩
  intro i
  change (0 : ℝ) ≤ (0 : ℝ)
  exact le_rfl

-- Proof sketch: write the orthant as the intersection of the closed half-spaces
-- `{y | 0 ≤ y i}` over all coordinates, using continuity of each coordinate functional.
/-- The coordinatewise nonnegative cone in `ℓ²(I, ℝ)` is closed. -/
theorem l2PositiveOrthant_isClosed : IsClosed (l2PositiveOrthant I) := by
  -- Each coordinate half-space is closed, and arbitrary intersections of closed sets stay closed.
  have hclosed : IsClosed (⋂ i : I, {y : L2 | 0 ≤ y i}) := by
    refine isClosed_iInter fun i ↦ ?_
    have hcont : Continuous fun y : L2 ↦ y i := by
      exact (continuous_apply i).comp (lp.uniformContinuous_coe (p := (2 : ENNReal))).continuous
    simpa using isClosed_le continuous_const hcont
  -- The intersection description is exactly the defining coordinatewise predicate.
  convert hclosed using 1
  ext y
  simp [l2PositiveOrthant]

-- Proof sketch: coordinatewise nonnegativity is preserved under convex combinations, so the
-- orthant is convex.
/-- The coordinatewise nonnegative cone in `ℓ²(I, ℝ)` is convex. -/
theorem l2PositiveOrthant_convex : Convex ℝ (l2PositiveOrthant I) := by
  -- Check the convexity inequality coordinatewise.
  intro x hx y hy a b ha hb hab i
  simpa [smul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    add_nonneg (mul_nonneg ha (hx i)) (mul_nonneg hb (hy i))

/-- Helper for Example 6.29: the positive orthant is closed under addition. -/
private theorem l2PositiveOrthant_add_mem {x y : L2}
    (hx : x ∈ l2PositiveOrthant I) (hy : y ∈ l2PositiveOrthant I) :
    x + y ∈ l2PositiveOrthant I := by
  -- Add the coordinatewise inequalities.
  intro i
  exact add_nonneg (hx i) (hy i)

/-- Helper for Example 6.29: positive scalar multiples stay in the positive orthant. -/
private theorem l2PositiveOrthant_pos_smul_mem {a : ℝ} (ha : 0 < a) {x : L2}
    (hx : x ∈ l2PositiveOrthant I) :
    a • x ∈ l2PositiveOrthant I := by
  -- Multiply each coordinate inequality by the positive scalar.
  intro i
  exact mul_nonneg (le_of_lt ha) (hx i)

/-- Helper for Example 6.29: the positive part of an `ℓ²` vector lies in the positive orthant. -/
private theorem l2PositivePart_mem (x : L2) :
    l2PositivePart x ∈ l2PositiveOrthant I := by
  -- Every coordinate is a maximum with `0`, hence nonnegative.
  intro i
  rw [l2PositivePart_apply]
  exact le_max_right (x i) (0 : ℝ)

/-- Helper for Example 6.29: the negated residual of the positive-part decomposition lies in the
positive orthant. -/
private theorem neg_sub_l2PositivePart_mem (x : L2) :
    -(x - l2PositivePart x) ∈ l2PositiveOrthant I := by
  -- Coordinatewise, the negated residual is either `-x i` or `0`.
  intro i
  have hcoord : (-(x - l2PositivePart x)) i = l2PositivePart x i - x i := by
    calc
      (-(x - l2PositivePart x)) i = -((x - l2PositivePart x) i) := by rfl
      _ = -(x i - l2PositivePart x i) := by rfl
      _ = l2PositivePart x i - x i := by ring
  rw [hcoord]
  by_cases hxi : x i ≤ 0
  · have hneg : 0 ≤ -(x i) := neg_nonneg.mpr hxi
    rw [l2PositivePart_apply, max_eq_right hxi]
    simpa [sub_eq_add_neg] using hneg
  · have hxi_nonneg : 0 ≤ x i := le_of_lt (lt_of_not_ge hxi)
    rw [l2PositivePart_apply, max_eq_left hxi_nonneg]
    simp

/-- Helper for Example 6.29: the positive part is orthogonal to the residual of the
positive-part decomposition. -/
private theorem inner_sub_l2PositivePart_l2PositivePart_eq_zero (x : L2) :
    ⟪x - l2PositivePart x, l2PositivePart x⟫_ℝ = 0 := by
  -- Expand the inner product into coordinates and show each term vanishes separately.
  rw [lp.inner_eq_tsum]
  have hterms : ∀ i, ⟪(x - l2PositivePart x) i, l2PositivePart x i⟫_ℝ = 0 := by
    intro i
    have hcoord : (x - l2PositivePart x) i = x i - l2PositivePart x i := by
      rfl
    rw [hcoord]
    by_cases hxi : x i ≤ 0
    · rw [l2PositivePart_apply, max_eq_right hxi]
      simp
    · have hxi_nonneg : 0 ≤ x i := le_of_lt (lt_of_not_ge hxi)
      rw [l2PositivePart_apply, max_eq_left hxi_nonneg]
      simp
  have hfun :
      (fun i ↦ ⟪(x - l2PositivePart x) i, l2PositivePart x i⟫_ℝ) = 0 := by
    funext i
    exact hterms i
  rw [hfun]
  exact tsum_zero

-- Proof sketch: apply Proposition 6.28 to the closed convex cone `K`. By Example 6.25, the dual
-- cone of `K` is `K` itself, so the residual `x - P x` lies in the negative orthant while `P x`
-- lies in the positive orthant. These complementary sign conditions and the orthogonality relation
-- force each coordinate of `P x` to equal `max (x i) 0`.
/-- Example 6.29: the metric projection onto the coordinatewise nonnegative cone in `ℓ²(I, ℝ)` is
the coordinatewise positive part. -/
theorem projectionPoint_l2PositiveOrthant_eq_positivePart (x : L2) :
    projectionPoint (l2PositiveOrthant I)
      (isChebyshev_of_nonempty_isClosed_convex
        l2PositiveOrthant_nonempty
        l2PositiveOrthant_isClosed
        l2PositiveOrthant_convex) x =
      l2PositivePart x := by
  let C : ConvexCone ℝ L2 :=
    { carrier := l2PositiveOrthant I
      smul_mem' := fun {_} ha {_} hx ↦ l2PositiveOrthant_pos_smul_mem (I := I) ha hx
      add_mem' := fun {_} hx {_} hy ↦ l2PositiveOrthant_add_mem (I := I) hx hy }
  let K : ProperCone ℝ L2 :=
    ⟨C.toPointedCone <|
        ConvexCone.Pointed.of_nonempty_of_isClosed
          l2PositiveOrthant_nonempty
          l2PositiveOrthant_isClosed,
      l2PositiveOrthant_isClosed⟩
  -- Route correction: use Proposition 6.28 backwards on the explicit positive-part decomposition.
  have hp_mem : l2PositivePart x ∈ (K : Set L2) := by
    simpa [K, C, l2PositiveOrthant] using l2PositivePart_mem (I := I) x
  have horth : ⟪x - l2PositivePart x, l2PositivePart x⟫_ℝ = 0 :=
    inner_sub_l2PositivePart_l2PositivePart_eq_zero (I := I) x
  let S : Set L2 := l2PositiveOrthant I
  have hpolarSetS : x - l2PositivePart x ∈ Set.polarCone S := by
    have hself : S = Set.dualCone S := by
      simpa [S] using (Set.isSelfDual_iff.mp ell2PositiveOrthant_isSelfDual)
    have hdual :
        -(x - l2PositivePart x) ∈ Set.dualCone S := by
      rw [← hself]
      simpa [S] using neg_sub_l2PositivePart_mem (I := I) x
    rw [Set.mem_dualCone_iff] at hdual
    simpa using hdual
  have hpolar : x - l2PositivePart x ∈ Set.polarCone (K : Set L2) := by
    simpa [K, C, S, l2PositiveOrthant] using hpolarSetS
  have hproj :
      l2PositivePart x =
        projectionPoint (K : Set L2) (properConeProjectionChebyshev K) x :=
    eq_projectionPoint_on_properCone_of_mem_of_inner_eq_zero_of_sub_mem_polarCone
      K hp_mem horth hpolar
  -- The proper-cone carrier is definitionally the target orthant, so the projection formulas agree.
  simpa [properConeProjectionChebyshev, K, C, l2PositiveOrthant] using hproj.symm

end
