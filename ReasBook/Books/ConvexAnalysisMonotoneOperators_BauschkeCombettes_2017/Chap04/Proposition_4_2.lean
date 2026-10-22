/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped RealInnerProductSpace

universe u

section

variable {E : Type u} {D : Set E}

/-- The fixed points of a map `T : D → E` relative to its domain `D`. -/
def fixedPointsWithin (T : D → E) : Set D :=
  {y | T y = (y : E)}

/-- Membership in `fixedPointsWithin T` means that `T` fixes the point in `D`. -/
-- Proof sketch: unfold `fixedPointsWithin`; the defining predicate is exactly `T y = y`.
@[simp] theorem mem_fixedPointsWithin_iff (T : D → E) {y : D} :
    y ∈ fixedPointsWithin T ↔ T y = (y : E) := by
  -- This is exactly the defining predicate of `fixedPointsWithin`.
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D : Set E}

/-- The inner-product inequality from Proposition 4.2 (iii). -/
def tx_norm_sq_le_inner_on_fixedPoints (T : D → E) : Prop :=
  ∀ x y : D, T y = (y : E) →
    ‖T x - (y : E)‖ ^ 2 ≤ ⟪(x : E) - (y : E), T x - (y : E)⟫

/-- The inner-product inequality from Proposition 4.2 (iv). -/
def inner_yTx_xTx_nonpos_on_fixedPoints (T : D → E) : Prop :=
  ∀ x y : D, T y = (y : E) →
    ⟪(y : E) - T x, (x : E) - T x⟫ ≤ 0

/-- The inner-product inequality from Proposition 4.2 (v). -/
def displacement_norm_sq_le_inner_on_fixedPoints (T : D → E) : Prop :=
  ∀ x y : D, T y = (y : E) →
    ‖T x - (x : E)‖ ^ 2 ≤ ⟪(y : E) - (x : E), T x - (x : E)⟫

/-- The reflected map `2T - Id` has the same fixed points as `T`. -/
lemma reflectedMap_eq_self_iff (T : D → E) {y : D} :
    (2 : ℝ) • T y - (y : E) = (y : E) ↔ T y = (y : E) := by
  constructor
  · intro hy
    have hzero : (2 : ℝ) • (T y - (y : E)) = 0 := by
      calc
        (2 : ℝ) • (T y - (y : E)) = (2 : ℝ) • T y - (2 : ℝ) • (y : E) := by
          rw [smul_sub]
        _ = ((2 : ℝ) • T y - (y : E)) - (y : E) := by
          simp [two_smul, sub_eq_add_neg, add_assoc]
        _ = 0 := by rw [hy, sub_self]
    rcases smul_eq_zero.mp hzero with htwo | hsub
    · norm_num at htwo
    · exact sub_eq_zero.mp hsub
  · intro hy
    simp [hy, two_smul]

/-- Helper for Proposition 4.2: clause (i) is equivalent to clause (iii) by expanding
`x - y = (x - T x) + (T x - y)`. -/
-- Proof sketch: expand `‖x - y‖ ^ 2` with `norm_add_sq_real`, rewrite
-- `⟪x - y, T x - y⟫` using the same decomposition, and compare the resulting real inequalities.
lemma isFirmlyQuasinonexpansiveOn_iff_tx_norm_sq_le_inner_on_fixedPoints
    (T : D → E) :
    IsFirmlyQuasinonexpansiveOn T ↔ tx_norm_sq_le_inner_on_fixedPoints T := by
  constructor
  · intro hFirm x y hy
    let a : E := (x : E) - T x
    let b : E := T x - (y : E)
    have hdecomp : a + b = (x : E) - (y : E) := by
      -- Reassociate the difference into the source-proof decomposition.
      simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hnorm :
        ‖(x : E) - (y : E)‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- Expanding the squared norm isolates the cross term `⟪a, b⟫`.
      simpa [hdecomp] using norm_add_sq_real a b
    have hinner : ⟪(x : E) - (y : E), b⟫ = ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- The clause (iii) inner product is the same cross term plus `‖b‖^2`.
      calc
        ⟪(x : E) - (y : E), b⟫ = ⟪a + b, b⟫ := by rw [hdecomp]
        _ = ⟪a, b⟫ + ⟪b, b⟫ := by rw [inner_add_left]
        _ = ⟪a, b⟫ + ‖b‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hFirm' : ‖b‖ ^ 2 + ‖a‖ ^ 2 ≤ ‖(x : E) - (y : E)‖ ^ 2 := by
      simpa [a, b, add_comm, add_left_comm, add_assoc] using hFirm x y hy
    -- The quadratic expansion shows that the missing slack is exactly `2 * ⟪a, b⟫`.
    nlinarith [hFirm', hnorm, hinner]
  · intro hTx x y hy
    let a : E := (x : E) - T x
    let b : E := T x - (y : E)
    have hdecomp : a + b = (x : E) - (y : E) := by
      -- Reassociate the difference into the source-proof decomposition.
      simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hnorm :
        ‖(x : E) - (y : E)‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- Expanding the squared norm isolates the same cross term as above.
      simpa [hdecomp] using norm_add_sq_real a b
    have hinner : ⟪(x : E) - (y : E), b⟫ = ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- Rewriting clause (iii) into the `a`/`b` coordinates makes the reversal identical.
      calc
        ⟪(x : E) - (y : E), b⟫ = ⟪a + b, b⟫ := by rw [hdecomp]
        _ = ⟪a, b⟫ + ⟪b, b⟫ := by rw [inner_add_left]
        _ = ⟪a, b⟫ + ‖b‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hTx' : ‖b‖ ^ 2 ≤ ⟪(x : E) - (y : E), b⟫ := by
      simpa [b] using hTx x y hy
    -- Reversing the expansion recovers the firm quasinonexpansive inequality.
    nlinarith [hTx', hnorm, hinner]

/-- Helper for Proposition 4.2: clause (iii) is equivalent to clause (iv) by a sign change in the
cross term. -/
-- Proof sketch: rewrite `⟪x - y, T x - y⟫` using `x - y = (x - T x) + (T x - y)`, and rewrite
-- `⟪y - T x, x - T x⟫` as the negative of the same cross term.
lemma tx_norm_sq_le_inner_on_fixedPoints_iff_inner_yTx_xTx_nonpos_on_fixedPoints
    (T : D → E) :
    tx_norm_sq_le_inner_on_fixedPoints T ↔ inner_yTx_xTx_nonpos_on_fixedPoints T := by
  constructor
  · intro hTx x y hy
    let a : E := (x : E) - T x
    let b : E := T x - (y : E)
    have hdecomp : a + b = (x : E) - (y : E) := by
      -- Use the same decomposition as in the `(i) ↔ (iii)` step.
      simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hinner : ⟪(x : E) - (y : E), b⟫ = ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- Clause (iii) differs from `0 ≤ ⟪a, b⟫` only by the `‖b‖^2` term.
      calc
        ⟪(x : E) - (y : E), b⟫ = ⟪a + b, b⟫ := by rw [hdecomp]
        _ = ⟪a, b⟫ + ⟪b, b⟫ := by rw [inner_add_left]
        _ = ⟪a, b⟫ + ‖b‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hsign : ⟪(y : E) - T x, (x : E) - T x⟫ = -⟪a, b⟫ := by
      -- Clause (iv) is the nonpositivity of the same cross term with the opposite sign.
      calc
        ⟪(y : E) - T x, (x : E) - T x⟫ = ⟪-b, a⟫ := by simp [a, b]
        _ = -⟪b, a⟫ := by rw [inner_neg_left]
        _ = -⟪a, b⟫ := by rw [real_inner_comm]
    have hTx' : ‖b‖ ^ 2 ≤ ⟪(x : E) - (y : E), b⟫ := by
      simpa [b] using hTx x y hy
    -- Both clauses reduce to the sign of `⟪a, b⟫`.
    nlinarith [hTx', hinner, hsign]
  · intro hInner x y hy
    let a : E := (x : E) - T x
    let b : E := T x - (y : E)
    have hdecomp : a + b = (x : E) - (y : E) := by
      -- Use the same decomposition as in the forward direction.
      simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hinner : ⟪(x : E) - (y : E), b⟫ = ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- Clause (iii) still differs from `0 ≤ ⟪a, b⟫` only by `‖b‖^2`.
      calc
        ⟪(x : E) - (y : E), b⟫ = ⟪a + b, b⟫ := by rw [hdecomp]
        _ = ⟪a, b⟫ + ⟪b, b⟫ := by rw [inner_add_left]
        _ = ⟪a, b⟫ + ‖b‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hsign : ⟪(y : E) - T x, (x : E) - T x⟫ = -⟪a, b⟫ := by
      -- Clause (iv) is the same scalar inequality with the sign flipped.
      calc
        ⟪(y : E) - T x, (x : E) - T x⟫ = ⟪-b, a⟫ := by simp [a, b]
        _ = -⟪b, a⟫ := by rw [inner_neg_left]
        _ = -⟪a, b⟫ := by rw [real_inner_comm]
    have hInner' : ⟪(y : E) - T x, (x : E) - T x⟫ ≤ 0 := by
      simpa using hInner x y hy
    -- Reversing the sign change recovers clause (iii).
    nlinarith [hInner', hinner, hsign]

/-- Helper for Proposition 4.2: clause (iv) is equivalent to clause (v) by expanding
`y - T x = (y - x) + (x - T x)`. -/
-- Proof sketch: expand the left inner product in clause (iv), identify the self-inner-product
-- with `‖x - T x‖^2`, and rewrite `T x - x = - (x - T x)`.
lemma inner_yTx_xTx_nonpos_on_fixedPoints_iff_displacement_norm_sq_le_inner_on_fixedPoints
    (T : D → E) :
    inner_yTx_xTx_nonpos_on_fixedPoints T ↔
      displacement_norm_sq_le_inner_on_fixedPoints T := by
  constructor
  · intro hInner x y hy
    let a : E := (x : E) - T x
    have hsplit : (y : E) - T x = ((y : E) - (x : E)) + a := by
      -- This is the source-proof decomposition for clause (iv).
      dsimp [a]
      abel_nf
    have hrewrite :
        ⟪(y : E) - T x, (x : E) - T x⟫ =
          ⟪(y : E) - (x : E), a⟫ + ‖a‖ ^ 2 := by
      -- Expanding clause (iv) isolates the displacement norm term.
      calc
        ⟪(y : E) - T x, (x : E) - T x⟫ = ⟪((y : E) - (x : E)) + a, a⟫ := by
          rw [hsplit]
        _ = ⟪(y : E) - (x : E), a⟫ + ⟪a, a⟫ := by rw [inner_add_left]
        _ = ⟪(y : E) - (x : E), a⟫ + ‖a‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hsign : ⟪(y : E) - (x : E), T x - (x : E)⟫ = -⟪(y : E) - (x : E), a⟫ := by
      -- The target clause uses `T x - x`, which is the negative of `a`.
      calc
        ⟪(y : E) - (x : E), T x - (x : E)⟫ = ⟪(y : E) - (x : E), -a⟫ := by
          simp [a]
        _ = -⟪(y : E) - (x : E), a⟫ := by rw [inner_neg_right]
    have hInner' : ⟪(y : E) - T x, (x : E) - T x⟫ ≤ 0 := by
      simpa using hInner x y hy
    have ha : ‖a‖ ^ 2 ≤ ⟪(y : E) - (x : E), T x - (x : E)⟫ := by
      -- Rearranging the expanded clause (iv) yields exactly clause (v) in `a`-coordinates.
      nlinarith [hInner', hrewrite, hsign]
    simpa [a, norm_sub_rev] using ha
  · intro hDisp x y hy
    let a : E := (x : E) - T x
    have hsplit : (y : E) - T x = ((y : E) - (x : E)) + a := by
      -- Use the same decomposition as in the forward direction.
      dsimp [a]
      abel_nf
    have hrewrite :
        ⟪(y : E) - T x, (x : E) - T x⟫ =
          ⟪(y : E) - (x : E), a⟫ + ‖a‖ ^ 2 := by
      -- Expanding clause (iv) isolates the same displacement norm term.
      calc
        ⟪(y : E) - T x, (x : E) - T x⟫ = ⟪((y : E) - (x : E)) + a, a⟫ := by
          rw [hsplit]
        _ = ⟪(y : E) - (x : E), a⟫ + ⟪a, a⟫ := by rw [inner_add_left]
        _ = ⟪(y : E) - (x : E), a⟫ + ‖a‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hsign : ⟪(y : E) - (x : E), T x - (x : E)⟫ = -⟪(y : E) - (x : E), a⟫ := by
      -- Rewrite the clause (v) inner product back to `a`.
      calc
        ⟪(y : E) - (x : E), T x - (x : E)⟫ = ⟪(y : E) - (x : E), -a⟫ := by
          simp [a]
        _ = -⟪(y : E) - (x : E), a⟫ := by rw [inner_neg_right]
    have ha : ‖a‖ ^ 2 ≤ ⟪(y : E) - (x : E), T x - (x : E)⟫ := by
      simpa [a, norm_sub_rev] using hDisp x y hy
    -- Reversing the rearrangement recovers clause (iv).
    nlinarith [ha, hrewrite, hsign]

/-- Helper for Proposition 4.2: clause (ii) is equivalent to clause (iii) via the reflection
identity from Lemma 2.17. -/
-- Proof sketch: rewrite `((2T - Id) x) - y` as `2 • (T x - y) - (x - y)`, square the norm
-- inequality, and use `norm_sq_sub_norm_sq_reflection_eq_four_mul`.
lemma isQuasinonexpansiveOn_reflectedMap_iff_tx_norm_sq_le_inner_on_fixedPoints
    (T : D → E) :
    IsQuasinonexpansiveOn (fun x : D ↦ (2 : ℝ) • T x - (x : E)) ↔
      tx_norm_sq_le_inner_on_fixedPoints T := by
  constructor
  · intro hRef x y hy
    let u : E := (x : E) - (y : E)
    let v : E := T x - (y : E)
    have hyRef : ((2 : ℝ) • T y - (y : E)) = (y : E) :=
      (reflectedMap_eq_self_iff T).2 hy
    have hreflect : ((2 : ℝ) • T x - (x : E)) - (y : E) = (2 : ℝ) • v - u := by
      -- Center the reflected map at the fixed point `y`.
      dsimp [u, v]
      rw [two_smul, two_smul]
      abel_nf
    have hnorm : ‖(2 : ℝ) • v - u‖ ≤ ‖u‖ := by
      simpa [hreflect, u, v] using hRef x y hyRef
    have hsq : ‖(2 : ℝ) • v - u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
    have hgap :
        ‖u‖ ^ 2 - ‖(2 : ℝ) • v - u‖ ^ 2 = 4 * (⟪u, v⟫ - ‖v‖ ^ 2) := by
      -- The reflected norm gap is exactly the clause (iii) scalar gap.
      simpa using norm_sq_sub_norm_sq_reflection_eq_four_mul u v
    have huv : ‖v‖ ^ 2 ≤ ⟪u, v⟫ := by
      -- The nonexpansive estimate is exactly nonnegativity of the reflected norm gap.
      nlinarith [hsq, hgap]
    simpa [u, v] using huv
  · intro hTx x y hy
    let u : E := (x : E) - (y : E)
    let v : E := T x - (y : E)
    have hyT : T y = (y : E) :=
      (reflectedMap_eq_self_iff T).1 hy
    have hreflect : ((2 : ℝ) • T x - (x : E)) - (y : E) = (2 : ℝ) • v - u := by
      -- Center the reflected map at the same fixed point `y`.
      dsimp [u, v]
      rw [two_smul, two_smul]
      abel_nf
    have huv : ‖v‖ ^ 2 ≤ ⟪u, v⟫ := by
      simpa [u, v] using hTx x y hyT
    have hgap :
        ‖u‖ ^ 2 - ‖(2 : ℝ) • v - u‖ ^ 2 = 4 * (⟪u, v⟫ - ‖v‖ ^ 2) := by
      -- The same reflected norm identity converts clause (iii) back into the norm gap.
      simpa using norm_sq_sub_norm_sq_reflection_eq_four_mul u v
    have hsq : ‖(2 : ℝ) • v - u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      -- The clause (iii) inequality makes the reflected norm gap nonnegative.
      nlinarith [huv, hgap]
    have hnorm : ‖(2 : ℝ) • v - u‖ ≤ ‖u‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
    simpa [hreflect, u, v] using hnorm

/-- Proposition 4.2: for a map `T : D → E`, firm quasinonexpansiveness, quasinonexpansiveness of
the reflected map `2T - Id`, and the three equivalent fixed-point inner-product inequalities
from (iii), (iv), and (v) are all equivalent. -/
-- Proof sketch: prove `(i) ↔ (iii)` by expanding `‖x - y‖ ^ 2`, prove `(iii) ↔ (iv)` and
-- `(iv) ↔ (v)` by rearranging inner products, and prove `(ii) ↔ (iii)` by expanding the square
-- of `‖(2T - Id) x - y‖`.
theorem firmly_quasinonexpansive_on_tfae (T : D → E) :
    [ IsFirmlyQuasinonexpansiveOn T,
      IsQuasinonexpansiveOn (fun x : D ↦ (2 : ℝ) • T x - (x : E)),
      tx_norm_sq_le_inner_on_fixedPoints T,
      inner_yTx_xTx_nonpos_on_fixedPoints T,
      displacement_norm_sq_le_inner_on_fixedPoints T ].TFAE := by
  -- Route correction: use clause (iii) as the hub so each source-proof rewrite is isolated once.
  tfae_have 1 ↔ 3 := by
    -- Expand `x - y = (x - T x) + (T x - y)` to compare clauses (i) and (iii).
    exact isFirmlyQuasinonexpansiveOn_iff_tx_norm_sq_le_inner_on_fixedPoints T
  tfae_have 3 ↔ 4 := by
    -- Rewrite clause (iv) as the sign change of the cross term from clause (iii).
    exact tx_norm_sq_le_inner_on_fixedPoints_iff_inner_yTx_xTx_nonpos_on_fixedPoints T
  tfae_have 4 ↔ 5 := by
    -- Expand `y - T x = (y - x) + (x - T x)` to compare clauses (iv) and (v).
    exact inner_yTx_xTx_nonpos_on_fixedPoints_iff_displacement_norm_sq_le_inner_on_fixedPoints T
  tfae_have 2 ↔ 3 := by
    -- Lemma 2.17 identifies the reflected norm gap with the clause (iii) scalar gap.
    exact isQuasinonexpansiveOn_reflectedMap_iff_tx_norm_sq_le_inner_on_fixedPoints T
  tfae_finish

end
