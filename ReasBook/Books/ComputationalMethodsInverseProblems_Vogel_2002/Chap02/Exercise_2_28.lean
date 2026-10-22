/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A1.ClosedConvex
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Assumption_A2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Notation_2_4

public section

noncomputable section

open scoped ContinuousLinearMap

universe u v

namespace ContinuousLinearMap

variable {H₁ : Type u} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁] [CompleteSpace H₁]
variable {H₂ : Type v} [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [CompleteSpace H₂]

/-- Helper for Exercise 2.28: expanding `‖x + τ • y‖ ^ 2` isolates its constant, mixed,
and quadratic parts. -/
lemma normSq_add_smul_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y : E) (τ : ℝ) :
    ‖x + τ • y‖ ^ 2 = ‖x‖ ^ 2 + τ * (inner ℝ x y + inner ℝ y x) + τ ^ 2 * ‖y‖ ^ 2 := by
  -- Expand the square through the inner product, then collect the scalar coefficients.
  calc
    ‖x + τ • y‖ ^ 2 = inner ℝ (x + τ • y) (x + τ • y) := by
      rw [real_inner_self_eq_norm_sq]
    _ = inner ℝ x x + inner ℝ x (τ • y) + (inner ℝ (τ • y) x + inner ℝ (τ • y) (τ • y)) := by
      rw [inner_add_left, inner_add_right, inner_add_right]
    _ = ‖x‖ ^ 2 + τ * (inner ℝ x y + inner ℝ y x) + τ ^ 2 * ‖y‖ ^ 2 := by
      rw [real_inner_self_eq_norm_sq, real_inner_smul_right, real_inner_smul_left,
        real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      ring

/-- Helper for Exercise 2.28: self-adjointness lets the penalty cross term move across the
inner product. -/
lemma inner_apply_swap_of_isSelfAdjoint
    (L : H₁ →L[ℝ] H₁) (hSelf : IsSelfAdjoint L) (x y : H₁) :
    inner ℝ (L y) x = inner ℝ (L x) y := by
  -- Move `L` across the inner product through the adjoint, then use self-adjointness.
  calc
    inner ℝ (L y) x = inner ℝ y (L.adjoint x) := by
      rw [← ContinuousLinearMap.adjoint_inner_right]
    _ = inner ℝ y (L x) := by
      rw [hSelf.adjoint_eq]
    _ = inner ℝ (L x) y := by
      rw [real_inner_comm]

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Helper for Exercise 2.28: the residual quadratic term has the expected Jensen gap
`a * b * ‖K (x - y)‖ ^ 2 / 2`. -/
lemma residualJensenGap_eq
    (K : H₁ →L[ℝ] H₂) (g : H₂) {a b : ℝ} (hab : a + b = 1) (x y : H₁) :
    a * (‖K x - g‖ ^ 2 / 2) + b * (‖K y - g‖ ^ 2 / 2) - ‖K (a • x + b • y) - g‖ ^ 2 / 2 =
      a * b * ‖K (x - y)‖ ^ 2 / 2 := by
  let u : H₂ := K y - g
  let w : H₂ := K (x - y)
  let c : ℝ := inner ℝ u w + inner ℝ w u
  have hb : b = 1 - a := by
    linarith
  have hx : K x - g = u + w := by
    -- Rewrite the `x` residual relative to the `y` residual plus the displacement.
    simp [u, w, sub_eq_add_neg, map_sub, add_assoc, add_left_comm, add_comm]
  have hcombo : K (a • x + b • y) - g = u + a • w := by
    -- The convex combination residual is the base residual plus the scaled displacement.
    calc
      K (a • x + b • y) - g = a • K x + (1 - a) • K y - g := by
        rw [hb]
        simp [map_add]
      _ = AffineMap.lineMap (K y) (K x) a - g := by
        rw [add_comm, AffineMap.lineMap_apply_module]
      _ = K y + a • (K x - K y) - g := by
        rw [AffineMap.lineMap_apply_module']
        repeat rw [sub_eq_add_neg]
        ac_rfl
      _ = u + a • w := by
        dsimp [u, w]
        rw [map_sub]
        repeat rw [sub_eq_add_neg]
        ac_rfl
  have hNormX : ‖K x - g‖ ^ 2 = ‖u‖ ^ 2 + c + ‖w‖ ^ 2 := by
    -- Expand the displaced residual square at coefficient `1`.
    rw [hx]
    simpa [c] using (normSq_add_smul_eq u w 1)
  have hNormCombo : ‖K (a • x + b • y) - g‖ ^ 2 = ‖u‖ ^ 2 + a * c + a ^ 2 * ‖w‖ ^ 2 := by
    -- Expand the convex-combination residual square at coefficient `a`.
    rw [hcombo]
    simpa [c] using (normSq_add_smul_eq u w a)
  -- Compare the two expansions and collapse the coefficients with `a + b = 1`.
  calc
    a * (‖K x - g‖ ^ 2 / 2) + b * (‖K y - g‖ ^ 2 / 2) - ‖K (a • x + b • y) - g‖ ^ 2 / 2
        = (a * (‖u‖ ^ 2 + c + ‖w‖ ^ 2) + b * ‖u‖ ^ 2 - (‖u‖ ^ 2 + a * c + a ^ 2 * ‖w‖ ^ 2))
            / 2 := by
            rw [hNormX, hNormCombo]
            simp [u]
            ring
    _ = a * b * ‖w‖ ^ 2 / 2 := by
      rw [hb]
      ring
    _ = a * b * ‖K (x - y)‖ ^ 2 / 2 := by
      rfl

/-- Helper for Exercise 2.28: the quadratic penalty term of a self-adjoint operator has the
expected Jensen gap. -/
lemma penaltyJensenGap_eq
    (L : H₁ →L[ℝ] H₁) (hSelf : IsSelfAdjoint L) {a b : ℝ} (hab : a + b = 1) (x y : H₁) :
    a * inner ℝ (L x) x + b * inner ℝ (L y) y - inner ℝ (L (a • x + b • y)) (a • x + b • y) =
      a * b * inner ℝ (L (x - y)) (x - y) := by
  let u : H₁ := y
  let w : H₁ := x - y
  let q : ℝ := inner ℝ (L u) u
  let r : ℝ := inner ℝ (L u) w + inner ℝ (L w) u
  let s : ℝ := inner ℝ (L w) w
  have hb : b = 1 - a := by
    linarith
  have hx : x = u + w := by
    -- Decompose `x` into the base point `y` plus the displacement `x - y`.
    simp [u, w, sub_eq_add_neg]
  have hcombo : a • x + b • y = u + a • w := by
    -- Rewrite the convex combination as the same base point plus a scaled displacement.
    calc
      a • x + b • y = a • x + (1 - a) • y := by rw [hb]
      _ = AffineMap.lineMap y x a := by
        rw [add_comm, AffineMap.lineMap_apply_module]
      _ = y + a • (x - y) := by
        rw [AffineMap.lineMap_apply_module', add_comm]
      _ = u + a • w := by
        simp [u, w]
  have hswap : inner ℝ (L w) u = inner ℝ (L u) w :=
    inner_apply_swap_of_isSelfAdjoint L hSelf u w
  have hPenaltyX : inner ℝ (L x) x = q + r + s := by
    -- Expand the penalty at `x = u + w` and rewrite the mixed term symmetrically.
    rw [hx]
    calc
      inner ℝ (L (u + w)) (u + w)
          = inner ℝ (L u) u + inner ℝ (L w) u + (inner ℝ (L u) w + inner ℝ (L w) w) := by
              simp [map_add, inner_add_left, inner_add_right]
      _ = q + r + s := by
        dsimp [q, r, s]
        rw [hswap]
        ring
  have hPenaltyCombo :
      inner ℝ (L (a • x + b • y)) (a • x + b • y) = q + a * r + a ^ 2 * s := by
    -- Expand the penalty at the scaled displacement `u + a • w`.
    rw [hcombo]
    calc
      inner ℝ (L (u + a • w)) (u + a • w)
          = inner ℝ (L u) u + inner ℝ (L u) (a • w)
              + inner ℝ (L (a • w)) u + inner ℝ (L (a • w)) (a • w) := by
                simp [map_add, inner_add_left, inner_add_right]
                ring
      _ = q + a * r + a ^ 2 * s := by
        rw [map_smul, real_inner_smul_right, real_inner_smul_left, real_inner_smul_left,
          real_inner_smul_right]
        simp [q, r, s]
        ring
  -- Compare the two quadratic expansions and collect the remaining coefficient.
  calc
    a * inner ℝ (L x) x + b * inner ℝ (L y) y - inner ℝ (L (a • x + b • y)) (a • x + b • y)
        = a * (q + r + s) + b * q - (q + a * r + a ^ 2 * s) := by
            rw [hPenaltyX, hPenaltyCombo]
    _ = a * b * s := by
      rw [hb]
      ring
    _ = a * b * inner ℝ (L (x - y)) (x - y) := by
      rfl

omit [CompleteSpace H₁] [CompleteSpace H₂] in
/-- Helper for Exercise 2.28: the data-misfit term `f ↦ ‖K f - g‖ ^ 2 / 2` is convex on
all of `H₁`. -/
lemma dataMisfit_convexOn_univ
    (K : H₁ →L[ℝ] H₂) (g : H₂) :
    ConvexOn ℝ Set.univ (fun f ↦ ‖K f - g‖ ^ 2 / 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- The Jensen gap identity reduces convexity to nonnegativity of a norm square.
  have hGap := residualJensenGap_eq K g hab x y
  have hNonneg : 0 ≤ a * b * ‖K (x - y)‖ ^ 2 / 2 := by
    exact div_nonneg (mul_nonneg (mul_nonneg ha hb) (sq_nonneg ‖K (x - y)‖)) zero_le_two
  change ‖K (a • x + b • y) - g‖ ^ 2 / 2 ≤ a * (‖K x - g‖ ^ 2 / 2) + b * (‖K y - g‖ ^ 2 / 2)
  have hRewrite :
      ‖K (a • x + b • y) - g‖ ^ 2 / 2
        = a * (‖K x - g‖ ^ 2 / 2) + b * (‖K y - g‖ ^ 2 / 2) - a * b * ‖K (x - y)‖ ^ 2 / 2 := by
    linarith
  rw [hRewrite]
  linarith

/-- Helper for Exercise 2.28: a positive quadratic form `f ↦ inner ℝ (L f) f` is convex on
all of `H₁`. -/
lemma positiveQuadraticForm_convexOn_univ
    (L : H₁ →L[ℝ] H₁) (hPos : L.IsPositive) :
    ConvexOn ℝ Set.univ (fun f ↦ inner ℝ (L f) f) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  -- The Jensen gap becomes the quadratic form applied to the displacement `x - y`.
  have hGap := penaltyJensenGap_eq L hPos.isSelfAdjoint hab x y
  have hNonneg : 0 ≤ a * b * inner ℝ (L (x - y)) (x - y) := by
    exact mul_nonneg (mul_nonneg ha hb) (hPos.inner_nonneg_left (x - y))
  change inner ℝ (L (a • x + b • y)) (a • x + b • y) ≤
    a * inner ℝ (L x) x + b * inner ℝ (L y) y
  have hRewrite :
      inner ℝ (L (a • x + b • y)) (a • x + b • y)
        = a * inner ℝ (L x) x + b * inner ℝ (L y) y - a * b * inner ℝ (L (x - y)) (x - y) := by
    linarith
  rw [hRewrite]
  linarith

omit [CompleteSpace H₂] in
/-- Under Assumption A2 and `α > 0`, the quadratic Tikhonov functional is convex on all of `H₁`.
This is the canonical global convexity statement behind Exercise 2.28; the source-facing theorem
below is its restriction to a feasible set `C`. -/
theorem tikhonovFunctional_convexOn_univ
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (g : H₂) {α : ℝ}
    (hL : SelfAdjointStronglyPositive L) (hα : 0 < α) :
    ConvexOn ℝ Set.univ (fun f ↦ T[K, L]_α(f; g)) := by
  have hResidual : ConvexOn ℝ Set.univ (fun f ↦ ‖K f - g‖ ^ 2 / 2) :=
    dataMisfit_convexOn_univ K g
  have hPenalty : ConvexOn ℝ Set.univ (fun f ↦ inner ℝ (L f) f) :=
    positiveQuadraticForm_convexOn_univ L hL.isPositive
  have hScaledPenalty : ConvexOn ℝ Set.univ (fun f ↦ α * inner ℝ (L f) f) :=
    hPenalty.smul (le_of_lt hα)
  -- Assemble the objective from the residual and the scaled positive quadratic penalty.
  refine (hResidual.add hScaledPenalty).congr ?_
  intro f hf
  symm
  exact ContinuousLinearMap.tikhonovFunctional_def K L g α f

omit [CompleteSpace H₂] in
/-- Exercise 2.28. Under the Chapter 2 setup `A1` and `A2`, the quadratic Tikhonov
functional `(2.54)` is convex on any convex feasible set `C`. The closedness packaged by
`Set.ClosedConvex C` in Assumption A1 is not needed for convexity itself. In the existing
Chapter 2 owner, `(2.54)` is written as `T[K, L]_α(f; g)`, i.e. canonically
`K.tikhonovFunctional L g α`, or equivalently
`f ↦ ‖K f - g‖ ^ 2 / 2 + α * inner ℝ (L f) f`. -/
theorem tikhonovFunctional_convexOn
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (C : Set H₁) (g : H₂) {α : ℝ}
    (hC : Convex ℝ C) (hL : SelfAdjointStronglyPositive L) (hα : 0 < α) :
    ConvexOn ℝ C (fun f ↦ T[K, L]_α(f; g)) := by
  -- Restrict the global convexity statement from `Set.univ` to the feasible set `C`.
  exact (tikhonovFunctional_convexOn_univ K L g hL hα).subset (by
    intro x hx
    trivial) hC

omit [CompleteSpace H₂] in
/-- Assumption A1 packages the feasible-set hypothesis as `Set.ClosedConvex C`; this
source-facing companion recovers Exercise 2.28 from that chapter-local predicate. -/
theorem tikhonovFunctional_convexOn_of_closedConvex
    (K : H₁ →L[ℝ] H₂) (L : H₁ →L[ℝ] H₁) (C : Set H₁) (g : H₂) {α : ℝ}
    (hC : Set.ClosedConvex C) (hL : SelfAdjointStronglyPositive L) (hα : 0 < α) :
    ConvexOn ℝ C (fun f ↦ T[K, L]_α(f; g)) := by
  exact tikhonovFunctional_convexOn K L C g hC.convex hL hα

end ContinuousLinearMap
