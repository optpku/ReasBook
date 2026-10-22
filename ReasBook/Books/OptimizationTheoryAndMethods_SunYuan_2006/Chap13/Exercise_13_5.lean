/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Radon
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.PosDef

open Matrix Filter

-- Domain-style sampling for Exercise 13.5:
-- * primary domain: finite real symmetric matrix quadratic forms;
-- * source-facing layer from the textbook: a cover presentation saying that, for each `x`, one
--   of the two quadratic forms `x ↦ xᵀ C x` or `x ↦ xᵀ D x` is nonnegative;
-- * core/canonical owner: `Matrix.PosSemidef`;
-- * sampled canonical declarations in this domain:
--   `Matrix.PosSemidef`,
--   `Matrix.posSemidef_iff_dotProduct_mulVec`,
--   `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`,
--   `Matrix.PosSemidef.dotProduct_mulVec_nonneg`;
-- * layer triage:
--   - core/canonical owner: the positive-semidefinite matrix predicate;
--   - bridge/view: a set-cover hypothesis implying the pointwise disjunctive nonnegativity used
--     by the main statement;
-- * primitive data for the owner-level theorem: only `C`, `D`, their symmetry, and the pointwise
--   disjunction `0 ≤ xᵀ C x ∨ 0 ≤ xᵀ D x`;
-- * derived API: the cover-based source presentation.

section

variable {ι : Type*} [Fintype ι]

/-- Helper for Chapter13 Exercise 13.5: `quadraticEval M x` is the quadratic scalar `xᵀ M x`
written as a dot product against `M.mulVec x`. -/
def quadraticEval (M : Matrix ι ι ℝ) (x : ι → ℝ) : ℝ :=
  dotProduct x (M.mulVec x)

/-- Helper for Chapter13 Exercise 13.5: `goodParameterSet C D x` is the set of parameters
`t ∈ [0,1]` for which the quadratic form of `t • C + (1 - t) • D` is nonnegative at `x`. -/
def goodParameterSet (C D : Matrix ι ι ℝ) (x : ι → ℝ) : Set ℝ :=
  Set.Icc (0 : ℝ) 1 ∩ { t : ℝ | 0 ≤ quadraticEval (t • C + (1 - t) • D) x }

/-- Helper for Chapter13 Exercise 13.5: evaluating the quadratic form of the convex combination
matrix at a fixed vector is affine in the parameter `t`. -/
lemma convexCombinationQuadratic_eval (C D : Matrix ι ι ℝ) (t : ℝ) (x : ι → ℝ) :
    quadraticEval (t • C + (1 - t) • D) x =
      t * quadraticEval C x + (1 - t) * quadraticEval D x := by
  -- Expand the matrix-vector action so the scalar affine dependence on `t` is explicit.
  simp [quadraticEval, add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul]

/-- Helper for Chapter13 Exercise 13.5: each single-vector parameter set is nonempty because one
of the two endpoint matrices is already nonnegative at that vector. -/
lemma goodParameterSet_nonempty
    (C D : Matrix ι ι ℝ)
    (h_nonneg :
      ∀ x : ι → ℝ, 0 ≤ quadraticEval C x ∨ 0 ≤ quadraticEval D x)
    (x : ι → ℝ) :
    (goodParameterSet C D x).Nonempty := by
  rcases h_nonneg x with hxC | hxD
  · refine ⟨1, ?_⟩
    constructor
    · simp
    · simpa [convexCombinationQuadratic_eval] using hxC
  · refine ⟨0, ?_⟩
    constructor
    · simp
    · simpa [convexCombinationQuadratic_eval] using hxD

/-- Helper for Chapter13 Exercise 13.5: each single-vector parameter set is compact because it is
a closed subset of the compact interval `[0,1]`. -/
lemma goodParameterSet_compact (C D : Matrix ι ι ℝ) (x : ι → ℝ) :
    IsCompact (goodParameterSet C D x) := by
  set qC : ℝ := quadraticEval C x
  set qD : ℝ := quadraticEval D x
  have hEq :
      goodParameterSet C D x =
        Set.Icc (0 : ℝ) 1 ∩ { t : ℝ | 0 ≤ t * qC + (1 - t) * qD } := by
    ext t
    simp [goodParameterSet, qC, qD, convexCombinationQuadratic_eval]
  rw [hEq]
  have hcont : Continuous fun t : ℝ ↦ t * qC + (1 - t) * qD := by
    exact (continuous_id.mul continuous_const).add
      ((continuous_const.sub continuous_id).mul continuous_const)
  -- The affine inequality cuts out a closed half-line inside the compact interval `[0,1]`.
  exact IsCompact.of_isClosed_subset isCompact_Icc
    (isClosed_Icc.inter (isClosed_Ici.preimage hcont))
    fun _ ht ↦ ht.1

/-- Helper for Chapter13 Exercise 13.5: each single-vector parameter set is convex because the
defining inequality is affine in `t`. -/
lemma goodParameterSet_convex (C D : Matrix ι ι ℝ) (x : ι → ℝ) :
    Convex ℝ (goodParameterSet C D x) := by
  set qC : ℝ := quadraticEval C x
  set qD : ℝ := quadraticEval D x
  have hEq :
      goodParameterSet C D x =
        Set.Icc (0 : ℝ) 1 ∩ { t : ℝ | 0 ≤ t * qC + (1 - t) * qD } := by
    ext t
    simp [goodParameterSet, qC, qD, convexCombinationQuadratic_eval]
  rw [hEq]
  refine (convex_Icc (0 : ℝ) 1).inter ?_
  intro a ha b hb u v hu hv huv
  simp only [Set.mem_setOf_eq, smul_eq_mul] at ha hb ⊢
  -- The defining inequality is affine in the parameter, so it is preserved by convex mixtures.
  have h_affine :
      (u * a + v * b) * qC + (1 - (u * a + v * b)) * qD =
        u * (a * qC + (1 - a) * qD) + v * (b * qC + (1 - b) * qD) := by
    calc
      (u * a + v * b) * qC + (1 - (u * a + v * b)) * qD
          = (u * a + v * b) * qC + ((u + v) - (u * a + v * b)) * qD := by
              rw [huv]
      _ = u * (a * qC + (1 - a) * qD) + v * (b * qC + (1 - b) * qD) := by
            ring
  rw [h_affine]
  nlinarith

/-- Helper for Chapter13 Exercise 13.5: conjugating by a two-column matrix transports the ambient
quadratic evaluation to a literal `Fin 2` quadratic evaluation. -/
lemma quadraticEval_mulVec_eq
    (C : Matrix ι ι ℝ) (P : Matrix ι (Fin 2) ℝ) (u : Fin 2 → ℝ) :
    quadraticEval C (P.mulVec u) = quadraticEval (P.transpose * C * P) u := by
  -- Rewrite the ambient quadratic form through the matrix-conjugation identity on `Fin 2`.
  simp [quadraticEval, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

/-- Helper for Chapter13 Exercise 13.5: on the affine chart `![r, 1]`, a `Fin 2` quadratic form
expands to an explicit real quadratic polynomial. -/
lemma quadraticEval_finTwo_line (M : Matrix (Fin 2) (Fin 2) ℝ) (r : ℝ) :
    quadraticEval M ![r, 1] = M 0 0 * r ^ 2 + (M 0 1 + M 1 0) * r + M 1 1 := by
  -- Expand the `Fin 2` dot product and collect the coefficients of `r`.
  simp [quadraticEval, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Helper for Chapter13 Exercise 13.5: evaluating on the first basis vector reads off the
`(0,0)` entry of a `Fin 2` matrix. -/
lemma quadraticEval_finTwo_axisLeft (M : Matrix (Fin 2) (Fin 2) ℝ) :
    quadraticEval M ![1, 0] = M 0 0 := by
  -- The first basis vector kills every term except the top-left matrix entry.
  simp [quadraticEval, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Helper for Chapter13 Exercise 13.5: evaluating on the second basis vector reads off the
`(1,1)` entry of a `Fin 2` matrix. -/
lemma quadraticEval_finTwo_axisRight (M : Matrix (Fin 2) (Fin 2) ℝ) :
    quadraticEval M ![0, 1] = M 1 1 := by
  -- The second basis vector kills every term except the bottom-right matrix entry.
  simp [quadraticEval, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Helper for Chapter13 Exercise 13.5: quadratic evaluation is homogeneous of degree `2`. -/
lemma quadraticEval_smul (M : Matrix (Fin 2) (Fin 2) ℝ) (a : ℝ) (u : Fin 2 → ℝ) :
    quadraticEval M (a • u) = a ^ 2 * quadraticEval M u := by
  -- Pull the scalar through both vector slots of the quadratic evaluation.
  calc
    quadraticEval M (a • u) = dotProduct (a • u) (a • M.mulVec u) := by
      rw [quadraticEval, Matrix.mulVec_smul]
    _ = a * (a * dotProduct u (M.mulVec u)) := by
          simp [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    _ = a ^ 2 * quadraticEval M u := by
          simp [quadraticEval]
          ring_nf

/-- Helper for Chapter13 Exercise 13.5: if the second coordinate vanishes, a `Fin 2` vector is a
scalar multiple of the first basis vector. -/
lemma finTwo_eq_smul_axisLeft_of_second_eq_zero
    (u : Fin 2 → ℝ) (hu : u 1 = 0) :
    u = (u 0) • ![1, 0] := by
  -- Expanding the two coordinates shows that only the first basis direction remains.
  ext i
  fin_cases i <;> simp [hu]

/-- Helper for Chapter13 Exercise 13.5: if the second coordinate is nonzero, a `Fin 2` vector is
a scalar multiple of a point on the affine chart `![r, 1]`. -/
lemma finTwo_eq_smul_line_of_second_ne_zero
    (u : Fin 2 → ℝ) (hu : u 1 ≠ 0) :
    u = (u 1) • ![u 0 / u 1, 1] := by
  -- Normalize by the second coordinate so the remaining direction lies on the affine chart.
  ext i
  fin_cases i
  · have hmul : u 1 * (u 0 / u 1) = u 0 := by
      field_simp [hu]
    simp [hmul]
  · simp

/-- Helper for Chapter13 Exercise 13.5: a globally nonnegative real quadratic has nonnegative
leading coefficient. -/
lemma leadingCoeff_nonneg_of_forall_nonnegQuadratic
    (a b c : ℝ) (h : ∀ r : ℝ, 0 ≤ a * r ^ 2 + b * r + c) :
    0 ≤ a := by
  by_contra ha
  have ha' : a < 0 := lt_of_not_ge ha
  have htend : Tendsto (fun x : ℝ ↦ (a * x + b) * x + c) atTop atBot :=
    tendsto_atBot_add_const_right _ c <|
      (tendsto_atBot_add_const_right _ b (tendsto_id.const_mul_atTop_of_neg ha')).atBot_mul_atTop₀
        tendsto_id
  -- A negative leading coefficient forces the quadratic to tend to `-∞` along `atTop`.
  rcases (htend.eventually (eventually_lt_atBot 0)).exists with ⟨x, hx⟩
  exact (h x).not_gt <| by
    simpa [pow_two, mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm] using hx

/-- Helper for Chapter13 Exercise 13.5: evaluating a globally nonnegative quadratic at `0` gives a
nonnegative constant coefficient. -/
lemma constantCoeff_nonneg_of_forall_nonnegQuadratic
    (a b c : ℝ) (h : ∀ r : ℝ, 0 ≤ a * r ^ 2 + b * r + c) :
    0 ≤ c := by
  -- The affine chart point `r = 0` reads off the constant term.
  simpa using h 0

/-- Helper for Chapter13 Exercise 13.5: when the endpoint values have opposite signs, the
admissible parameters are exactly an upper cut in `t`. -/
lemma realQuadraticAdmissibleParameterCut_upper
    {qC qD t : ℝ} (hqC : qC < 0) (hqD : 0 ≤ qD) :
    (0 ≤ t * qC + (1 - t) * qD) ↔ t ≤ qD / (qD - qC) := by
  have hden : 0 < qD - qC := by
    linarith
  constructor
  · intro ht
    refine (le_div_iff₀ hden).2 ?_
    -- Move the sign-opposite inequality to the positive denominator `qD - qC`.
    linarith
  · intro ht
    have hmul : t * (qD - qC) ≤ qD := (le_div_iff₀ hden).1 ht
    -- Expanding the denominator inequality recovers the original affine constraint.
    linarith

/-- Helper for Chapter13 Exercise 13.5: when the endpoint values have opposite signs, the
admissible parameters are exactly a lower cut in `t`. -/
lemma realQuadraticAdmissibleParameterCut_lower
    {qC qD t : ℝ} (hqD : qD < 0) (hqC : 0 ≤ qC) :
    (0 ≤ t * qC + (1 - t) * qD) ↔ qD / (qD - qC) ≤ t := by
  have hden : 0 < qC - qD := by
    linarith
  have hcut :
      (-qD) / (qC - qD) = qD / (qD - qC) := by
    field_simp [show qC - qD ≠ 0 by linarith, show qD - qC ≠ 0 by linarith]
    ring
  constructor
  · intro ht
    have hmul : -qD ≤ t * (qC - qD) := by
      linarith
    have ht' : (-qD) / (qC - qD) ≤ t := (div_le_iff₀ hden).2 hmul
    -- Rewrite the normalized threshold back to the source-facing denominator `qD - qC`.
    simpa [hcut] using ht'
  · intro ht
    have ht' : (-qD) / (qC - qD) ≤ t := by
      simpa [hcut] using ht
    have hmul : -qD ≤ t * (qC - qD) := (div_le_iff₀ hden).1 ht'
    -- Expanding the lower cut recovers the original affine constraint.
    linarith

/-- Helper for Chapter13 Exercise 13.5: a quadratic with nonnegative leading coefficient,
nonnegative constant term, and nonpositive discriminant is globally nonnegative. -/
lemma quadraticNonneg_of_nonnegLeading_of_nonnegConst_of_discrim_nonpos
    {A B C : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hdisc : discrim A B C ≤ 0) :
    ∀ r : ℝ, 0 ≤ A * r ^ 2 + B * r + C := by
  intro r
  rcases eq_or_lt_of_le hA with rfl | hApos
  · have hBsq : B ^ 2 ≤ 0 := by
      simpa [discrim] using hdisc
    have hB : B = 0 := by
      nlinarith [sq_nonneg B]
    -- In the linear-degenerate case, the discriminant forces the slope to vanish.
    simpa [hB] using hC
  have hmain : 0 ≤ (2 * A * r + B) ^ 2 - discrim A B C := by
    have hsq : 0 ≤ (2 * A * r + B) ^ 2 := sq_nonneg _
    linarith
  have hiden :
      4 * A * (A * r ^ 2 + B * r + C) = (2 * A * r + B) ^ 2 - discrim A B C := by
    rw [discrim]
    ring
  have hnonneg : 0 ≤ 4 * A * (A * r ^ 2 + B * r + C) := by
    rw [hiden]
    exact hmain
  -- After completing the square, divide by the positive scalar `4 * A`.
  nlinarith

/-- Helper for Chapter13 Exercise 13.5: when the discriminant is a square, the quadratic factors
through the two corresponding roots. -/
lemma quadraticFactorization_of_discrim_eq_sq
    {a b c s x : ℝ} (ha : a ≠ 0) (hdisc : discrim a b c = s * s) :
    a * x ^ 2 + b * x + c =
      a * (x - (-b - s) / (2 * a)) * (x - (-b + s) / (2 * a)) := by
  -- Rewrite the discriminant identity into the explicit root factorization.
  rw [discrim] at hdisc
  field_simp [ha] at hdisc ⊢
  ring_nf at hdisc ⊢
  linarith

/-- Helper for Chapter13 Exercise 13.5: a positive-leading quadratic that is negative somewhere
must have strictly positive discriminant. -/
lemma discrim_pos_of_posLeading_of_negValue
    {a b c r0 : ℝ} (ha : 0 < a) (hneg : a * r0 ^ 2 + b * r0 + c < 0) :
    0 < discrim a b c := by
  have hiden :
      (2 * a * r0 + b) ^ 2 - discrim a b c =
        4 * a * (a * r0 ^ 2 + b * r0 + c) := by
    -- Completing the square isolates the discriminant from a single negative witness.
    rw [discrim]
    ring
  have hlt : (2 * a * r0 + b) ^ 2 - discrim a b c < 0 := by
    rw [hiden]
    nlinarith
  have hsquare : 0 ≤ (2 * a * r0 + b) ^ 2 := sq_nonneg _
  -- The square term is nonnegative, so the discriminant must dominate it strictly.
  linarith

/-- Helper for Chapter13 Exercise 13.5: the negative set of an upward-opening quadratic with a
negative witness is exactly the open interval between its two discriminant roots. -/
lemma quadratic_neg_iff_mem_Ioo_of_posLeading
    {a b c r : ℝ} (ha : 0 < a) (hdisc : 0 < discrim a b c) :
    a * r ^ 2 + b * r + c < 0 ↔
      (-b - Real.sqrt (discrim a b c)) / (2 * a) < r ∧
        r < (-b + Real.sqrt (discrim a b c)) / (2 * a) := by
  let u := (-b - Real.sqrt (discrim a b c)) / (2 * a)
  let v := (-b + Real.sqrt (discrim a b c)) / (2 * a)
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hdisc_nonneg : 0 ≤ discrim a b c := le_of_lt hdisc
  have hsq :
      discrim a b c = Real.sqrt (discrim a b c) * Real.sqrt (discrim a b c) := by
    -- Over `ℝ`, the positive discriminant has the expected square root square.
    rw [← sq, Real.sq_sqrt hdisc_nonneg]
  have hfac : a * r ^ 2 + b * r + c = a * (r - u) * (r - v) := by
    -- Factor through the two ordered discriminant roots.
    dsimp [u, v]
    simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using
      quadraticFactorization_of_discrim_eq_sq
        (a := a) (b := b) (c := c) (s := Real.sqrt (discrim a b c)) (x := r) ha0 hsq
  have huv : u ≤ v := by
    -- The positive denominator preserves the natural order of the two roots.
    apply le_of_not_gt
    intro hgt
    have hsqrt : 0 < Real.sqrt (discrim a b c) := Real.sqrt_pos.mpr hdisc
    have hden0 : 2 * a ≠ 0 := by positivity
    have hgt' := hgt
    dsimp [u, v] at hgt'
    field_simp [hden0] at hgt'
    nlinarith
  have hmain : a * (r - u) * (r - v) < 0 ↔ u < r ∧ r < v := by
    constructor
    · intro hlt
      have hmul : (r - u) * (r - v) < 0 := by
        nlinarith
      -- Between the ordered roots the two linear factors have opposite signs.
      exact (sub_mul_sub_neg_iff r huv).1 hmul
    · intro hmid
      have hmul : (r - u) * (r - v) < 0 := (sub_mul_sub_neg_iff r huv).2 hmid
      -- Multiplying by the positive leading coefficient preserves negativity.
      nlinarith
  -- Substitute the factorization back into the original quadratic.
  simpa [u, v, hfac] using hmain

/-- Helper for Chapter13 Exercise 13.5: a down-opening quadratic that is nonnegative at two
distinct points must have strictly positive discriminant. -/
lemma discrim_pos_of_negLeading_of_two_nonnegValues
    {a b c r1 r2 : ℝ} (ha : a < 0) (hr : r1 ≠ r2)
    (h1 : 0 ≤ a * r1 ^ 2 + b * r1 + c) (h2 : 0 ≤ a * r2 ^ 2 + b * r2 + c) :
    0 < discrim a b c := by
  have hiden1 :
      (2 * a * r1 + b) ^ 2 - discrim a b c =
        4 * a * (a * r1 ^ 2 + b * r1 + c) := by
    -- Completing the square turns a nonnegative value into an upper bound on the discriminant.
    rw [discrim]
    ring
  have hiden2 :
      (2 * a * r2 + b) ^ 2 - discrim a b c =
        4 * a * (a * r2 ^ 2 + b * r2 + c) := by
    -- The same identity at the second point will rule out the double-root case.
    rw [discrim]
    ring
  have hle1 : (2 * a * r1 + b) ^ 2 ≤ discrim a b c := by
    have htmp : (2 * a * r1 + b) ^ 2 - discrim a b c ≤ 0 := by
      rw [hiden1]
      nlinarith
    linarith
  have hle2 : (2 * a * r2 + b) ^ 2 ≤ discrim a b c := by
    have htmp : (2 * a * r2 + b) ^ 2 - discrim a b c ≤ 0 := by
      rw [hiden2]
      nlinarith
    linarith
  have hnonneg : 0 ≤ discrim a b c := le_trans (sq_nonneg (2 * a * r1 + b)) hle1
  by_contra hdisc
  have hzero : discrim a b c = 0 := by
    linarith
  have hsq1 : (2 * a * r1 + b) ^ 2 = 0 := by
    linarith [sq_nonneg (2 * a * r1 + b), hle1]
  have hsq2 : (2 * a * r2 + b) ^ 2 = 0 := by
    linarith [sq_nonneg (2 * a * r2 + b), hle2]
  have hz1 : 2 * a * r1 + b = 0 := sq_eq_zero_iff.mp hsq1
  have hz2 : 2 * a * r2 + b = 0 := sq_eq_zero_iff.mp hsq2
  have hEq : r1 = r2 := by
    nlinarith
  exact hr hEq

/-- Helper for Chapter13 Exercise 13.5: once the discriminant is strictly positive, the negative
set of a down-opening quadratic is exactly the union of the two exterior rays outside its roots. -/
lemma quadratic_neg_iff_mem_Iio_union_Ioi_of_negLeading_of_posDiscrim
    {a b c r : ℝ} (ha : a < 0) (hdisc : 0 < discrim a b c) :
    a * r ^ 2 + b * r + c < 0 ↔
      r < (-b + Real.sqrt (discrim a b c)) / (2 * a) ∨
        (-b - Real.sqrt (discrim a b c)) / (2 * a) < r := by
  let u := (-b + Real.sqrt (discrim a b c)) / (2 * a)
  let v := (-b - Real.sqrt (discrim a b c)) / (2 * a)
  have ha0 : a ≠ 0 := ne_of_lt ha
  have hdisc_nonneg : 0 ≤ discrim a b c := le_of_lt hdisc
  have hsq :
      discrim a b c = Real.sqrt (discrim a b c) * Real.sqrt (discrim a b c) := by
    -- Over `ℝ`, the positive discriminant is the square of its real square root.
    rw [← sq, Real.sq_sqrt hdisc_nonneg]
  have hfac : a * r ^ 2 + b * r + c = a * (r - u) * (r - v) := by
    -- Rewrite through the two real roots, ordered for the negative-leading sign analysis.
    dsimp [u, v]
    simpa [pow_two, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using
      quadraticFactorization_of_discrim_eq_sq
        (a := a) (b := b) (c := c) (s := Real.sqrt (discrim a b c)) (x := r) ha0 hsq
  have huv : u ≤ v := by
    -- Because the denominator is negative, the `+sqrt` root is the left endpoint.
    apply le_of_not_gt
    intro hgt
    have hsqrt : 0 < Real.sqrt (discrim a b c) := Real.sqrt_pos.mpr hdisc
    have hden : 2 * a < 0 := by
      nlinarith
    have hnum : -b + Real.sqrt (discrim a b c) < -b - Real.sqrt (discrim a b c) := by
      dsimp [u, v] at hgt
      exact (div_lt_div_right_of_neg hden).1 hgt
    nlinarith
  have hmain : a * (r - u) * (r - v) < 0 ↔ r < u ∨ v < r := by
    constructor
    · intro hlt
      have hmul : 0 < (r - u) * (r - v) := by
        nlinarith
      -- Outside the ordered root interval the two linear factors have the same sign.
      exact (sub_mul_sub_pos_iff r huv).1 hmul
    · intro hmid
      have hmul : 0 < (r - u) * (r - v) := (sub_mul_sub_pos_iff r huv).2 hmid
      -- Multiplying by the negative leading coefficient flips positivity into negativity.
      nlinarith
  -- Substitute the factorization back into the original quadratic.
  simpa [u, v, hfac] using hmain

/-- Helper for Chapter13 Exercise 13.5: the source disjunction means the two negative sets never
meet. -/
lemma quadraticNegativeSets_disjoint
    (aC bC cC aD bD cD : ℝ)
    (h_nonneg :
      ∀ r : ℝ, 0 ≤ aC * r ^ 2 + bC * r + cC ∨ 0 ≤ aD * r ^ 2 + bD * r + cD) :
    Disjoint
      {r : ℝ | aC * r ^ 2 + bC * r + cC < 0}
      {r : ℝ | aD * r ^ 2 + bD * r + cD < 0} := by
  -- Any common point of the two negative sets would contradict the source disjunction at that `r`.
  refine Set.disjoint_left.2 ?_
  intro r hrC hrD
  rcases h_nonneg r with hC | hD
  · exact (not_le_of_gt hrC) hC
  · exact (not_le_of_gt hrD) hD

/-- Helper for Chapter13 Exercise 13.5: the two discriminant roots of a nondegenerate quadratic
are genuine zeros of the quadratic polynomial. -/
lemma quadratic_eq_zero_at_discrimRoots
    {a b c : ℝ} (ha : a ≠ 0) (hdisc : 0 ≤ discrim a b c) :
    a * (((-b - Real.sqrt (discrim a b c)) / (2 * a)) ^ 2) +
        b * (((-b - Real.sqrt (discrim a b c)) / (2 * a))) + c = 0 ∧
      a * (((-b + Real.sqrt (discrim a b c)) / (2 * a)) ^ 2) +
        b * (((-b + Real.sqrt (discrim a b c)) / (2 * a))) + c = 0 := by
  have hsq :
      discrim a b c = Real.sqrt (discrim a b c) * Real.sqrt (discrim a b c) := by
    -- The nonnegative discriminant is the square of its real square root.
    rw [← sq, Real.sq_sqrt hdisc]
  constructor
  · let u := (-b - Real.sqrt (discrim a b c)) / (2 * a)
    let v := (-b + Real.sqrt (discrim a b c)) / (2 * a)
    have hfac :=
      quadraticFactorization_of_discrim_eq_sq
        (a := a) (b := b) (c := c) (s := Real.sqrt (discrim a b c)) (x := u) ha hsq
    -- Substitute the left root into the factorization formula.
    simpa [u, v] using hfac
  · let u := (-b - Real.sqrt (discrim a b c)) / (2 * a)
    let v := (-b + Real.sqrt (discrim a b c)) / (2 * a)
    have hfac :=
      quadraticFactorization_of_discrim_eq_sq
        (a := a) (b := b) (c := c) (s := Real.sqrt (discrim a b c)) (x := v) ha hsq
    -- Substitute the right root into the factorization formula.
    simpa [u, v] using hfac

/-- Helper for Chapter13 Exercise 13.5: a down-opening quadratic is eventually negative on the
right tail. -/
lemma exists_right_tail_negative_of_negLeading
    {a b c : ℝ} (ha : a < 0) :
    ∃ R : ℝ, ∀ r ≥ R, a * r ^ 2 + b * r + c < 0 := by
  have htend : Tendsto (fun x : ℝ ↦ (a * x + b) * x + c) atTop atBot :=
    tendsto_atBot_add_const_right _ c <|
      (tendsto_atBot_add_const_right _ b (tendsto_id.const_mul_atTop_of_neg ha)).atBot_mul_atTop₀
        tendsto_id
  -- The negative leading coefficient forces the polynomial to stay below `0` far to the right.
  rcases (eventually_atTop.1 (htend.eventually (eventually_lt_atBot 0))) with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  intro r hr
  have hr' := hR r hr
  simpa [pow_two, mul_add, add_mul, mul_assoc, add_assoc, add_left_comm, add_comm] using hr'

/-- Helper for Chapter13 Exercise 13.5: a down-opening quadratic is eventually negative on the
left tail as well. -/
lemma exists_left_tail_negative_of_negLeading
    {a b c : ℝ} (ha : a < 0) :
    ∃ R : ℝ, ∀ r ≤ R, a * r ^ 2 + b * r + c < 0 := by
  rcases exists_right_tail_negative_of_negLeading (a := a) (b := -b) (c := c) ha with
      ⟨R, hR⟩
  refine ⟨-R, ?_⟩
  intro r hr
  have hRr : -r ≥ R := by
    linarith
  have hneg := hR (-r) hRr
  -- Reflecting the variable turns the left tail into the right tail of the reflected polynomial.
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hneg

/-- Helper for Chapter13 Exercise 13.5: an affine function with positive slope is negative exactly
to the left of its root. -/
lemma affine_neg_iff_lt_root_of_posSlope
    {b c r : ℝ} (hb : 0 < b) :
    b * r + c < 0 ↔ r < -c / b := by
  constructor
  · intro h
    have hmul : r * b < -c := by
      linarith
    exact (lt_div_iff₀ hb).2 hmul
  · intro h
    have hmul : r * b < -c := (lt_div_iff₀ hb).1 h
    linarith

/-- Helper for Chapter13 Exercise 13.5: an affine function with negative slope is negative exactly
to the right of its root. -/
lemma affine_neg_iff_root_lt_of_negSlope
    {b c r : ℝ} (hb : b < 0) :
    b * r + c < 0 ↔ -c / b < r := by
  constructor
  · intro h
    have hmul : r * b < -c := by
      linarith
    exact (div_lt_iff_of_neg hb).2 hmul
  · intro h
    have hmul : r * b < -c := (div_lt_iff_of_neg hb).1 h
    linarith

/-- Helper for Chapter13 Exercise 13.5: if one quadratic has zero leading coefficient and is
negative somewhere, then the disjunctive nonnegativity hypothesis rules out a companion quadratic
with negative leading coefficient. -/
lemma negLeading_impossible_of_affineDisjunctive
    (bC cC aD bD cD : ℝ) (haD : aD < 0)
    (h_nonneg :
      ∀ r : ℝ, 0 ≤ bC * r + cC ∨ 0 ≤ aD * r ^ 2 + bD * r + cD)
    (hCneg : ∃ r, bC * r + cC < 0) :
    False := by
  rcases hCneg with ⟨r0, hr0⟩
  by_cases hbC : bC = 0
  · have hcC : cC < 0 := by
      simpa [hbC] using hr0
    rcases exists_right_tail_negative_of_negLeading (a := aD) (b := bD) (c := cD) haD with
        ⟨R, hR⟩
    have hCbad : bC * R + cC < 0 := by
      simpa [hbC] using hcC
    have hDbad : aD * R ^ 2 + bD * R + cD < 0 := hR R le_rfl
    rcases h_nonneg R with hC | hD
    · exact (not_le_of_gt hCbad) hC
    · exact (not_le_of_gt hDbad) hD
  have hbCsign : 0 < bC ∨ bC < 0 := by
    exact lt_or_gt_of_ne hbC |> Or.symm
  rcases hbCsign with hbCpos | hbCneg
  · rcases exists_left_tail_negative_of_negLeading (a := aD) (b := bD) (c := cD) haD with
        ⟨R, hR⟩
    let root : ℝ := -cC / bC
    let r : ℝ := min (root - 1) R
    have hr_lt_root : r < root := by
      dsimp [r, root]
      nlinarith [min_le_left (root - 1) R]
    have hCbad : bC * r + cC < 0 := (affine_neg_iff_lt_root_of_posSlope hbCpos).2 hr_lt_root
    have hr_le_R : r ≤ R := by
      dsimp [r]
      exact min_le_right _ _
    have hDbad : aD * r ^ 2 + bD * r + cD < 0 := hR r hr_le_R
    rcases h_nonneg r with hC | hD
    · exact (not_le_of_gt hCbad) hC
    · exact (not_le_of_gt hDbad) hD
  · rcases exists_right_tail_negative_of_negLeading (a := aD) (b := bD) (c := cD) haD with
        ⟨R, hR⟩
    let root : ℝ := -cC / bC
    let r : ℝ := max (root + 1) R
    have hroot_lt_r : root < r := by
      dsimp [r, root]
      nlinarith [le_max_left (root + 1) R]
    have hCbad : bC * r + cC < 0 := (affine_neg_iff_root_lt_of_negSlope hbCneg).2 hroot_lt_r
    have hR_le_r : R ≤ r := by
      dsimp [r]
      exact le_max_right _ _
    have hDbad : aD * r ^ 2 + bD * r + cD < 0 := hR r hR_le_r
    rcases h_nonneg r with hC | hD
    · exact (not_le_of_gt hCbad) hC
    · exact (not_le_of_gt hDbad) hD

/-- Helper for Chapter13 Exercise 13.5: a quadratic polynomial can be rewritten in the root-basis
coordinates associated to two marked points `u` and `v`. -/
lemma quadraticRootBasis_eq
    (a b c u v r : ℝ) :
    (v - u) ^ 2 * (a * r ^ 2 + b * r + c) =
      (a * u ^ 2 + b * u + c) * (v - r) ^ 2 +
        (a * v ^ 2 + b * v + c) * (r - u) ^ 2 +
        ((a * u ^ 2 + b * u + c) + (a * v ^ 2 + b * v + c) - a * (v - u) ^ 2) *
          (v - r) * (r - u) := by
  -- Expanding both sides shows that this is a pure polynomial identity.
  ring

/-- Helper for Chapter13 Exercise 13.5: the standard `2 × 2` PSD inequality gives nonnegativity
of the corresponding root-basis quadratic expression. -/
lemma rootBasisNonneg_of_psd
    {A B m x y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hm : m ^ 2 ≤ A * B) :
    0 ≤ A * x ^ 2 + 2 * m * x * y + B * y ^ 2 := by
  have hC : 0 ≤ B * y ^ 2 := by
    nlinarith [hB, sq_nonneg y]
  have hdisc : discrim A (2 * m * y) (B * y ^ 2) ≤ 0 := by
    -- The determinant condition is exactly the nonpositive discriminant of the one-variable slice.
    rw [discrim]
    nlinarith [hm, sq_nonneg y]
  have hpoly :=
    quadraticNonneg_of_nonnegLeading_of_nonnegConst_of_discrim_nonpos
      (A := A) (B := 2 * m * y) (C := B * y ^ 2) hA hC hdisc x
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hpoly

/-- Helper for Chapter13 Exercise 13.5: after normalizing `r = (1 - s) * u + s * v`,
nonnegativity on `[u, v]` becomes a copositive root-basis slice on `[0, 1]`. -/
lemma rootBasisSliceNonneg_of_nonnegOnIcc
    {a b c u v : ℝ} (huv : u < v)
    (h_nonneg : ∀ r ∈ Set.Icc u v, 0 ≤ a * r ^ 2 + b * r + c) :
    let qU := a * u ^ 2 + b * u + c
    let qV := a * v ^ 2 + b * v + c
    let m := (qU + qV - a * (v - u) ^ 2) / 2
    ∀ s ∈ Set.Icc (0 : ℝ) 1, 0 ≤ qU * (1 - s) ^ 2 + 2 * m * s * (1 - s) + qV * s ^ 2 := by
  -- Route correction: normalize the interval to `[0,1]` first, then use one root-basis rewrite
  -- instead of repeating the same raw-coordinate polynomial algebra.
  dsimp
  set qU : ℝ := a * u ^ 2 + b * u + c
  set qV : ℝ := a * v ^ 2 + b * v + c
  set m : ℝ := (qU + qV - a * (v - u) ^ 2) / 2
  intro s hs
  let r : ℝ := (1 - s) * u + s * v
  have hr : r ∈ Set.Icc u v := by
    dsimp [r]
    constructor <;> nlinarith [huv, hs.1, hs.2]
  have hr_nonneg : 0 ≤ a * r ^ 2 + b * r + c := h_nonneg r hr
  have hrewrite :
      (v - u) ^ 2 * (a * r ^ 2 + b * r + c) =
        (v - u) ^ 2 * (qU * (1 - s) ^ 2 + 2 * m * s * (1 - s) + qV * s ^ 2) := by
    -- Rewrite the quadratic in the root basis and then substitute `r = (1 - s)u + sv`.
    calc
      (v - u) ^ 2 * (a * r ^ 2 + b * r + c)
          = qU * (v - r) ^ 2 + qV * (r - u) ^ 2 + (2 * m) * (v - r) * (r - u) := by
              simpa [qU, qV, m, two_mul] using quadraticRootBasis_eq a b c u v r
      _ = (v - u) ^ 2 * (qU * (1 - s) ^ 2 + 2 * m * s * (1 - s) + qV * s ^ 2) := by
            dsimp [r]
            ring
  have hscaled :
      0 ≤ (v - u) ^ 2 * (qU * (1 - s) ^ 2 + 2 * m * s * (1 - s) + qV * s ^ 2) := by
    rw [← hrewrite]
    nlinarith [sq_nonneg (v - u), hr_nonneg]
  have hvu_sq_pos : 0 < (v - u) ^ 2 := by
    have hvu_ne : v - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huv)
    exact sq_pos_of_ne_zero hvu_ne
  -- Divide out the positive square factor to recover the normalized slice inequality.
  nlinarith

/-- Helper for Chapter13 Exercise 13.5: nonnegativity of a quadratic on a closed interval forces
the root-basis off-diagonal coefficient to satisfy the copositivity bound. -/
lemma rootBasisOffDiagBound_of_nonnegOnIcc
    {a b c u v : ℝ} (huv : u < v)
    (h_nonneg : ∀ r ∈ Set.Icc u v, 0 ≤ a * r ^ 2 + b * r + c) :
    let qU := a * u ^ 2 + b * u + c
    let qV := a * v ^ 2 + b * v + c
    let m := (qU + qV - a * (v - u) ^ 2) / 2
    0 ≤ qU ∧ 0 ≤ qV ∧ -m ≤ Real.sqrt (qU * qV) := by
  -- Route correction: use the normalized `[0,1]` slice and then handle the positive/degenerate
  -- endpoint cases separately, instead of reopening the raw root-coordinate algebra.
  dsimp
  set qU : ℝ := a * u ^ 2 + b * u + c
  set qV : ℝ := a * v ^ 2 + b * v + c
  set m : ℝ := (qU + qV - a * (v - u) ^ 2) / 2
  have hslice :=
    rootBasisSliceNonneg_of_nonnegOnIcc (a := a) (b := b) (c := c) huv h_nonneg
  change 0 ≤ qU ∧ 0 ≤ qV ∧ -m ≤ Real.sqrt (qU * qV)
  have hqU : 0 ≤ qU := by
    simpa using hslice 0 (by simp)
  have hqV : 0 ≤ qV := by
    simpa using hslice 1 (by simp)
  refine ⟨hqU, hqV, ?_⟩
  by_cases hqU0 : qU = 0
  · by_cases hqV0 : qV = 0
    · have hmid := hslice (1 / 2) (by constructor <;> norm_num)
      have hm_half_nonneg :
          0 ≤ 0 * (1 - 1 / 2) ^ 2 + 2 * m * (1 / 2) * (1 - 1 / 2) + 0 * (1 / 2) ^ 2 := by
        simpa [qU, qV, m, hqU0, hqV0] using hmid
      norm_num at hm_half_nonneg
      have hm_nonneg : 0 ≤ m := by
        nlinarith
      have hsqrt_zero : Real.sqrt (qU * qV) = 0 := by simp [hqU0, hqV0]
      rw [hsqrt_zero]
      nlinarith
    · have hqV_pos : 0 < qV := lt_of_le_of_ne hqV (by simpa [eq_comm] using hqV0)
      by_contra hbound
      have hm_neg : m < 0 := by
        have hsqrt_zero : Real.sqrt (qU * qV) = 0 := by simp [hqU0]
        rw [hsqrt_zero] at hbound
        linarith
      let s : ℝ := -m / (qV - 2 * m)
      have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · dsimp [s]
          apply div_nonneg <;> linarith
        · have hden_pos : 0 < qV - 2 * m := by
            linarith
          change -m / (qV - 2 * m) ≤ 1
          exact (div_le_iff₀ hden_pos).2 (by linarith)
      have hs_nonneg := hslice s hs_mem
      have hs_pos : 0 < s := by
        dsimp [s]
        have hden_pos : 0 < qV - 2 * m := by
          linarith
        exact div_pos (by linarith) hden_pos
      have hinner : 2 * m * (1 - s) + qV * s = m := by
        have hden_ne : qV - 2 * m ≠ 0 := by
          linarith
        have hs_mul : s * (qV - 2 * m) = -m := by
          let d : ℝ := qV - 2 * m
          calc
            s * (qV - 2 * m) = (-m / d) * d := by rfl
            _ = (-m * d⁻¹) * d := by simp [div_eq_mul_inv]
            _ = -m * (d⁻¹ * d) := by ring
            _ = -m * 1 := by rw [inv_mul_cancel₀ hden_ne]
            _ = -m := by ring
        nlinarith [hs_mul]
      have hformula : qU * (1 - s) ^ 2 + 2 * m * s * (1 - s) + qV * s ^ 2 = s * m := by
        rw [hqU0]
        calc
          0 * (1 - s) ^ 2 + 2 * m * s * (1 - s) + qV * s ^ 2 = s * (2 * m * (1 - s) + qV * s) := by
              ring
          _ = s * m := by rw [hinner]
      have hs_bad : qU * (1 - s) ^ 2 + 2 * m * s * (1 - s) + qV * s ^ 2 < 0 := by
        rw [hformula]
        exact mul_neg_of_pos_of_neg hs_pos hm_neg
      exact (not_le_of_gt hs_bad) hs_nonneg
  · have hqU_pos : 0 < qU := lt_of_le_of_ne hqU (by simpa [eq_comm] using hqU0)
    by_cases hqV0 : qV = 0
    · by_contra hbound
      have hm_neg : m < 0 := by
        have hsqrt_zero : Real.sqrt (qU * qV) = 0 := by simp [hqV0]
        rw [hsqrt_zero] at hbound
        linarith
      let s : ℝ := (qU - m) / (qU - 2 * m)
      have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · dsimp [s]
          apply div_nonneg <;> linarith
        · have hden_pos : 0 < qU - 2 * m := by
            linarith
          change (qU - m) / (qU - 2 * m) ≤ 1
          exact (div_le_iff₀ hden_pos).2 (by linarith)
      have hs_nonneg := hslice s hs_mem
      have hs_lt : s < 1 := by
        dsimp [s]
        have hden_pos : 0 < qU - 2 * m := by
          linarith
        refine (div_lt_iff₀ hden_pos).2 ?_
        linarith
      have h1s_pos : 0 < 1 - s := by
        linarith
      have hinner : qU * (1 - s) + 2 * m * s = m := by
        have hden_ne : qU - 2 * m ≠ 0 := by
          linarith
        have hs_mul : s * (qU - 2 * m) = qU - m := by
          let d : ℝ := qU - 2 * m
          calc
            s * (qU - 2 * m) = ((qU - m) / d) * d := by rfl
            _ = ((qU - m) * d⁻¹) * d := by simp [div_eq_mul_inv]
            _ = (qU - m) * (d⁻¹ * d) := by ring
            _ = (qU - m) * 1 := by rw [inv_mul_cancel₀ hden_ne]
            _ = qU - m := by ring
        nlinarith [hs_mul]
      have hformula : qU * (1 - s) ^ 2 + 2 * m * s * (1 - s) + qV * s ^ 2 = (1 - s) * m := by
        rw [hqV0]
        calc
          qU * (1 - s) ^ 2 + 2 * m * s * (1 - s) + 0 * s ^ 2
              = (1 - s) * (qU * (1 - s) + 2 * m * s) := by
              ring
          _ = (1 - s) * m := by rw [hinner]
      have hs_bad : qU * (1 - s) ^ 2 + 2 * m * s * (1 - s) + qV * s ^ 2 < 0 := by
        rw [hformula]
        exact mul_neg_of_pos_of_neg h1s_pos hm_neg
      exact (not_le_of_gt hs_bad) hs_nonneg
    · have hqV_pos : 0 < qV := lt_of_le_of_ne hqV (by simpa [eq_comm] using hqV0)
      by_contra hbound
      have hsqrt_bad : m + Real.sqrt (qU * qV) < 0 := by
        linarith
      let s : ℝ := Real.sqrt qU / (Real.sqrt qU + Real.sqrt qV)
      have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · apply div_nonneg
          · exact Real.sqrt_nonneg _
          · positivity
        · have hden_pos : 0 < Real.sqrt qU + Real.sqrt qV := by
            positivity
          change Real.sqrt qU / (Real.sqrt qU + Real.sqrt qV) ≤ 1
          exact (div_le_iff₀ hden_pos).2 (by linarith [Real.sqrt_nonneg qV])
      let α : ℝ := Real.sqrt qU
      let β : ℝ := Real.sqrt qV
      have hα_sq : α ^ 2 = qU := by
        dsimp [α]
        rw [Real.sq_sqrt hqU]
      have hβ_sq : β ^ 2 = qV := by
        dsimp [β]
        rw [Real.sq_sqrt hqV]
      have hs_eq : s = α / (α + β) := by
        rfl
      have h1s_eq : 1 - s = β / (α + β) := by
        dsimp [s, α, β]
        have hden_ne : Real.sqrt qU + Real.sqrt qV ≠ 0 := by
          positivity
        field_simp [hden_ne]
        ring
      have hs_nonneg := hslice s hs_mem
      have hscaled :
          (α + β) ^ 2 *
              (qU * (1 - s) ^ 2 + 2 * m * s * (1 - s) + qV * s ^ 2) =
            2 * α * β * (m + α * β) := by
        rw [hs_eq, h1s_eq]
        have hden_ne : α + β ≠ 0 := by
          positivity
        field_simp [hden_ne]
        nlinarith [hα_sq, hβ_sq]
      have hscaled_nonneg :
          0 ≤ (α + β) ^ 2 *
            (qU * (1 - s) ^ 2 + 2 * m * s * (1 - s) + qV * s ^ 2) := by
        exact mul_nonneg (sq_nonneg (α + β)) hs_nonneg
      have hsqrt_mul : Real.sqrt (qU * qV) = α * β := by
        dsimp [α, β]
        rw [Real.sqrt_mul hqU]
      have hsqrt_bad' : m + α * β < 0 := by
        simpa [hsqrt_mul] using hsqrt_bad
      have hscaled_neg :
          2 * α * β * (m + α * β) < 0 := by
        have hα_pos : 0 < α := by
          dsimp [α]
          exact Real.sqrt_pos.mpr hqU_pos
        have hβ_pos : 0 < β := by
          dsimp [β]
          exact Real.sqrt_pos.mpr hqV_pos
        exact mul_neg_of_pos_of_neg (by positivity) hsqrt_bad'
      rw [hscaled] at hscaled_nonneg
      exact (not_le_of_gt hscaled_neg) hscaled_nonneg

/-- Helper for Chapter13 Exercise 13.5: endpoint/root-basis data satisfying the `2 × 2` PSD
bound forces the corresponding quadratic to be globally nonnegative. -/
lemma quadraticNonneg_of_rootBasisData
    {a b c u v A B M : ℝ} (huv : u < v)
    (hu_eval : a * u ^ 2 + b * u + c = A)
    (hv_eval : a * v ^ 2 + b * v + c = B)
    (hm_eval : A + B - a * (v - u) ^ 2 = 2 * M)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hm : M ^ 2 ≤ A * B) :
    ∀ r : ℝ, 0 ≤ a * r ^ 2 + b * r + c := by
  intro r
  have hcore :
      0 ≤ A * (v - r) ^ 2 + 2 * M * (v - r) * (r - u) + B * (r - u) ^ 2 := by
    exact rootBasisNonneg_of_psd (hA := hA) (hB := hB) (hm := hm)
  have hrepr :
      (v - u) ^ 2 * (a * r ^ 2 + b * r + c) =
        A * (v - r) ^ 2 + B * (r - u) ^ 2 + (A + B - a * (v - u) ^ 2) * (v - r) * (r - u) := by
    calc
      (v - u) ^ 2 * (a * r ^ 2 + b * r + c)
          = (a * u ^ 2 + b * u + c) * (v - r) ^ 2 +
              (a * v ^ 2 + b * v + c) * (r - u) ^ 2 +
                ((a * u ^ 2 + b * u + c) + (a * v ^ 2 + b * v + c) -
                  a * (v - u) ^ 2) * (v - r) * (r - u) := by
              simpa using quadraticRootBasis_eq a b c u v r
      _ = A * (v - r) ^ 2 + B * (r - u) ^ 2 + (A + B - a * (v - u) ^ 2) * (v - r) * (r - u) := by
            rw [hu_eval, hv_eval]
  have hscaled :
      0 ≤ (v - u) ^ 2 * (a * r ^ 2 + b * r + c) := by
    rw [hrepr, hm_eval]
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hvu_sq_pos : 0 < (v - u) ^ 2 := by
    have hvu_ne : v - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huv)
    exact sq_pos_of_ne_zero hvu_ne
  exact nonneg_of_mul_nonneg_right hscaled hvu_sq_pos

/-- Helper for Chapter13 Exercise 13.5: when the first affine function has positive slope and the
second has negative slope, the slope-canceling parameter yields a globally nonnegative convex
combination. -/
lemma existsParameter_nonnegOnAffineFunctions_of_pos_neg
    (bC cC bD cD : ℝ) (hbC : 0 < bC) (hbD : bD < 0)
    (h_nonneg : ∀ r : ℝ, 0 ≤ bC * r + cC ∨ 0 ≤ bD * r + cD) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      t * bC + (1 - t) * bD = 0 ∧
        ∀ r : ℝ, 0 ≤ (t * bC + (1 - t) * bD) * r + (t * cC + (1 - t) * cD) := by
  -- Route correction: compare the two affine roots by a midpoint contradiction, then evaluate the
  -- slope-canceled combination at the left root so no separate constant-term algebra is needed.
  let rC : ℝ := -cC / bC
  let rD : ℝ := -cD / bD
  have hrC_le_rD : rC ≤ rD := by
    by_contra hlt
    let r : ℝ := (rC + rD) / 2
    have hr_lt_rC : r < rC := by
      dsimp [r]
      nlinarith
    have hrD_lt_r : rD < r := by
      dsimp [r]
      nlinarith
    have hCbad : bC * r + cC < 0 := (affine_neg_iff_lt_root_of_posSlope hbC).2 hr_lt_rC
    have hDbad : bD * r + cD < 0 := (affine_neg_iff_root_lt_of_negSlope hbD).2 hrD_lt_r
    rcases h_nonneg r with hC | hD
    · exact (not_le_of_gt hCbad) hC
    · exact (not_le_of_gt hDbad) hD
  let t : ℝ := -bD / (bC - bD)
  have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [t]
      apply div_nonneg <;> linarith
    · have hden_pos : 0 < bC - bD := by
        linarith
      change -bD / (bC - bD) ≤ 1
      exact (div_le_iff₀ hden_pos).2 (by linarith)
  have hslope : t * bC + (1 - t) * bD = 0 := by
    dsimp [t]
    have hden_ne : bC - bD ≠ 0 := by
      linarith
    field_simp [hden_ne]
    ring
  have hD_at_rC : 0 ≤ bD * rC + cD := by
    by_contra hneg
    have : rD < rC := (affine_neg_iff_root_lt_of_negSlope hbD).1 (by linarith)
    exact (not_lt_of_ge hrC_le_rD) this
  have hconst_nonneg : 0 ≤ t * cC + (1 - t) * cD := by
    have hC_root : bC * rC + cC = 0 := by
      change bC * (-cC / bC) + cC = 0
      field_simp [hbC.ne']
      ring
    have hslope' : t * bC = -(1 - t) * bD := by
      linarith [hslope]
    have hconst_eval : t * cC + (1 - t) * cD = (1 - t) * (bD * rC + cD) := by
      calc
        t * cC + (1 - t) * cD = t * (-bC * rC) + (1 - t) * cD := by
            nlinarith [hC_root]
        _ = -(t * bC) * rC + (1 - t) * cD := by ring
        _ = (1 - t) * bD * rC + (1 - t) * cD := by
            rw [hslope']
            ring
        _ = (1 - t) * (bD * rC + cD) := by ring
    rw [hconst_eval]
    have h1t_nonneg : 0 ≤ 1 - t := by
      linarith [ht_mem.2]
    exact mul_nonneg h1t_nonneg hD_at_rC
  refine ⟨t, ht_mem, hslope, ?_⟩
  intro r
  -- After canceling the slope, the convex combination is the same nonnegative constant for every
  -- `r`.
  simpa [hslope] using hconst_nonneg

/-- Helper for Chapter13 Exercise 13.5: in the double-affine branch, a slope-canceling convex
combination is globally nonnegative. -/
lemma existsParameter_nonnegOnAffineFunctions
    (bC cC bD cD : ℝ)
    (h_nonneg : ∀ r : ℝ, 0 ≤ bC * r + cC ∨ 0 ≤ bD * r + cD)
    (hCneg : ∃ r, bC * r + cC < 0)
    (hDneg : ∃ r, bD * r + cD < 0) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      t * bC + (1 - t) * bD = 0 ∧
        ∀ r : ℝ, 0 ≤ (t * bC + (1 - t) * bD) * r + (t * cC + (1 - t) * cD) := by
  -- Route correction: first rule out zero and same-sign slopes, then call the ordered `(+,-)`
  -- lemma directly or after swapping the two affine functions.
  have hbC_ne : bC ≠ 0 := by
    intro hbC
    rcases hCneg with ⟨r0, hr0⟩
    have hcC_neg : cC < 0 := by
      simpa [hbC] using hr0
    have hD_global : ∀ r : ℝ, 0 ≤ bD * r + cD := by
      intro r
      have hCbad : bC * r + cC < 0 := by
        simpa [hbC] using hcC_neg
      rcases h_nonneg r with hC | hD
      · exact False.elim ((not_le_of_gt hCbad) hC)
      · exact hD
    rcases hDneg with ⟨r, hr⟩
    exact (not_le_of_gt hr) (hD_global r)
  have hbD_ne : bD ≠ 0 := by
    intro hbD
    rcases hDneg with ⟨r0, hr0⟩
    have hcD_neg : cD < 0 := by
      simpa [hbD] using hr0
    have hC_global : ∀ r : ℝ, 0 ≤ bC * r + cC := by
      intro r
      have hDbad : bD * r + cD < 0 := by
        simpa [hbD] using hcD_neg
      rcases h_nonneg r with hC | hD
      · exact hC
      · exact False.elim ((not_le_of_gt hDbad) hD)
    rcases hCneg with ⟨r, hr⟩
    exact (not_le_of_gt hr) (hC_global r)
  have hbC_sign : 0 < bC ∨ bC < 0 := by
    exact lt_or_gt_of_ne hbC_ne |> Or.symm
  have hbD_sign : 0 < bD ∨ bD < 0 := by
    exact lt_or_gt_of_ne hbD_ne |> Or.symm
  rcases hbC_sign with hbC_pos | hbC_neg
  · rcases hbD_sign with hbD_pos | hbD_neg
    · let rC : ℝ := -cC / bC
      let rD : ℝ := -cD / bD
      let r : ℝ := min (rC - 1) (rD - 1)
      have hr_lt_rC : r < rC := by
        dsimp [r]
        nlinarith [min_le_left (rC - 1) (rD - 1)]
      have hr_lt_rD : r < rD := by
        dsimp [r]
        nlinarith [min_le_right (rC - 1) (rD - 1)]
      have hCbad : bC * r + cC < 0 := (affine_neg_iff_lt_root_of_posSlope hbC_pos).2 hr_lt_rC
      have hDbad : bD * r + cD < 0 := (affine_neg_iff_lt_root_of_posSlope hbD_pos).2 hr_lt_rD
      rcases h_nonneg r with hC | hD
      · exact False.elim ((not_le_of_gt hCbad) hC)
      · exact False.elim ((not_le_of_gt hDbad) hD)
    · exact existsParameter_nonnegOnAffineFunctions_of_pos_neg
        bC cC bD cD hbC_pos hbD_neg h_nonneg
  · rcases hbD_sign with hbD_pos | hbD_neg
    · rcases existsParameter_nonnegOnAffineFunctions_of_pos_neg
          bD cD bC cC hbD_pos hbC_neg (fun r ↦ by simpa [or_comm] using h_nonneg r) with
            ⟨s, hs, hslope, hsnonneg⟩
      refine ⟨1 - s, ?_, ?_, ?_⟩
      constructor
      · linarith [hs.2]
      · linarith [hs.1]
      · simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
          mul_comm] using hslope
      · intro r
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
          mul_comm] using hsnonneg r
    · let rC : ℝ := -cC / bC
      let rD : ℝ := -cD / bD
      let r : ℝ := max (rC + 1) (rD + 1)
      have hrC_lt_r : rC < r := by
        dsimp [r]
        nlinarith [le_max_left (rC + 1) (rD + 1)]
      have hrD_lt_r : rD < r := by
        dsimp [r]
        nlinarith [le_max_right (rC + 1) (rD + 1)]
      have hCbad : bC * r + cC < 0 := (affine_neg_iff_root_lt_of_negSlope hbC_neg).2 hrC_lt_r
      have hDbad : bD * r + cD < 0 := (affine_neg_iff_root_lt_of_negSlope hbD_neg).2 hrD_lt_r
      rcases h_nonneg r with hC | hD
      · exact False.elim ((not_le_of_gt hCbad) hC)
      · exact False.elim ((not_le_of_gt hDbad) hD)

/-- Helper for Chapter13 Exercise 13.5: when the first quadratic has positive leading
coefficient and is negative somewhere, the source disjunction yields an explicit parameter whose
convex combination is globally nonnegative. -/
lemma existsParameter_nonnegOnRealQuadratics_of_posLeading
    (aC bC cC aD bD cD : ℝ) (hposC : 0 < aC)
    (h_nonneg :
      ∀ r : ℝ, 0 ≤ aC * r ^ 2 + bC * r + cC ∨ 0 ≤ aD * r ^ 2 + bD * r + cD)
    (hCneg : ∃ r, aC * r ^ 2 + bC * r + cC < 0) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ t * aC + (1 - t) * aD ∧
        ∀ r : ℝ,
          0 ≤
            (t * aC + (1 - t) * aD) * r ^ 2 +
              (t * bC + (1 - t) * bD) * r +
              (t * cC + (1 - t) * cD) := by
  -- Route correction: isolate the root interval where `qC` is negative, prove `qD ≥ 0` on the
  -- closed interval by continuity at the endpoints, then choose the determinant-zero root-basis
  -- parameter for the convex combination.
  rcases hCneg with ⟨r0, hr0⟩
  have hdisc : 0 < discrim aC bC cC :=
    discrim_pos_of_posLeading_of_negValue hposC hr0
  let u : ℝ := (-bC - Real.sqrt (discrim aC bC cC)) / (2 * aC)
  let v : ℝ := (-bC + Real.sqrt (discrim aC bC cC)) / (2 * aC)
  have huv : u < v := by
    dsimp [u, v]
    have hden_pos : 0 < 2 * aC := by positivity
    exact (div_lt_div_iff_of_pos_right hden_pos).2 (by nlinarith [Real.sqrt_pos.mpr hdisc])
  have hroots :=
    quadratic_eq_zero_at_discrimRoots
      (a := aC) (b := bC) (c := cC) (ne_of_gt hposC) (le_of_lt hdisc)
  have hCu : aC * u ^ 2 + bC * u + cC = 0 := by
    simpa [u, v] using hroots.1
  have hCv : aC * v ^ 2 + bC * v + cC = 0 := by
    simpa [u, v] using hroots.2
  let qD : ℝ → ℝ := fun r ↦ aD * r ^ 2 + bD * r + cD
  have hqD_cont : Continuous qD := by
    dsimp [qD]
    continuity
  have hD_nonneg_Ioo : ∀ r ∈ Set.Ioo u v, 0 ≤ qD r := by
    intro r hr
    have hCbad : aC * r ^ 2 + bC * r + cC < 0 :=
      (quadratic_neg_iff_mem_Ioo_of_posLeading hposC hdisc).2 hr
    rcases h_nonneg r with hC | hD
    · exact False.elim ((not_le_of_gt hCbad) hC)
    · simpa [qD] using hD
  have hD_nonneg_Icc : ∀ r ∈ Set.Icc u v, 0 ≤ qD r := by
    have hclosed : IsClosed {r : ℝ | 0 ≤ qD r} := isClosed_Ici.preimage hqD_cont
    have hsubset : Set.Ioo u v ⊆ {r : ℝ | 0 ≤ qD r} := by
      intro r hr
      exact hD_nonneg_Ioo r hr
    have hclosure_subset : closure (Set.Ioo u v) ⊆ {r : ℝ | 0 ≤ qD r} :=
      closure_minimal hsubset hclosed
    intro r hr
    have hr_closure : r ∈ closure (Set.Ioo u v) := by
      rw [closure_Ioo (ne_of_lt huv)]
      exact hr
    exact hclosure_subset hr_closure
  set qU : ℝ := qD u
  set qV : ℝ := qD v
  set m : ℝ := (qU + qV - aD * (v - u) ^ 2) / 2
  have hbound :=
    rootBasisOffDiagBound_of_nonnegOnIcc (a := aD) (b := bD) (c := cD) huv
      (by
        intro r hr
        simpa [qD] using hD_nonneg_Icc r hr)
  change 0 ≤ qU ∧ 0 ≤ qV ∧ -m ≤ Real.sqrt (qU * qV) at hbound
  rcases hbound with ⟨hqU, hqV, hm_bound⟩
  let s : ℝ := Real.sqrt (qU * qV)
  let k : ℝ := aC * (v - u) ^ 2 / 2
  have hk_pos : 0 < k := by
    dsimp [k]
    have hvu_sq_pos : 0 < (v - u) ^ 2 := by
      have hvu_ne : v - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huv)
      exact sq_pos_of_ne_zero hvu_ne
    positivity
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Real.sqrt_nonneg _
  have hnum_nonneg : 0 ≤ m + s := by
    linarith
  let t : ℝ := (m + s) / (k + m + s)
  have hden_pos : 0 < k + m + s := by
    linarith
  have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · dsimp [t]
      exact div_nonneg hnum_nonneg hden_pos.le
    · change (m + s) / (k + m + s) ≤ 1
      exact (div_le_iff₀ hden_pos).2 (by linarith)
  have h1t_nonneg : 0 ≤ 1 - t := by
    linarith [ht_mem.2]
  have hmT : -t * k + (1 - t) * m = -(1 - t) * s := by
    have hden_ne : k + m + s ≠ 0 := by
      linarith
    dsimp [t]
    field_simp [hden_ne]
    ring
  let aT : ℝ := t * aC + (1 - t) * aD
  let bT : ℝ := t * bC + (1 - t) * bD
  let cT : ℝ := t * cC + (1 - t) * cD
  have hu_eval : aT * u ^ 2 + bT * u + cT = (1 - t) * qU := by
    dsimp [aT, bT, cT, qU, qD]
    nlinarith [hCu]
  have hv_eval : aT * v ^ 2 + bT * v + cT = (1 - t) * qV := by
    dsimp [aT, bT, cT, qV, qD]
    nlinarith [hCv]
  have hm_eval :
      (1 - t) * qU + (1 - t) * qV - aT * (v - u) ^ 2 = 2 * (-(1 - t) * s) := by
    calc
      (1 - t) * qU + (1 - t) * qV - aT * (v - u) ^ 2 = 2 * (-t * k + (1 - t) * m) := by
          dsimp [aT, k, m]
          ring
      _ = 2 * (-(1 - t) * s) := by
          rw [hmT]
  have hs_sq : s ^ 2 = qU * qV := by
    dsimp [s]
    rw [Real.sq_sqrt]
    nlinarith [hqU, hqV]
  have hdet :
      (-(1 - t) * s) ^ 2 ≤ ((1 - t) * qU) * ((1 - t) * qV) := by
    refine le_of_eq ?_
    calc
      (-(1 - t) * s) ^ 2 = (1 - t) ^ 2 * s ^ 2 := by ring
      _ = (1 - t) ^ 2 * (qU * qV) := by rw [hs_sq]
      _ = ((1 - t) * qU) * ((1 - t) * qV) := by ring
  have hglobal : ∀ r : ℝ, 0 ≤ aT * r ^ 2 + bT * r + cT :=
    quadraticNonneg_of_rootBasisData (a := aT) (b := bT) (c := cT) huv hu_eval hv_eval hm_eval
      (mul_nonneg h1t_nonneg hqU) (mul_nonneg h1t_nonneg hqV) hdet
  have haT_nonneg : 0 ≤ aT := by
    exact leadingCoeff_nonneg_of_forall_nonnegQuadratic aT bT cT hglobal
  refine ⟨t, ht_mem, ?_, ?_⟩
  · simpa [aT] using haT_nonneg
  · intro r
    simpa [aT, bT, cT] using hglobal r

/-- Helper for Chapter13 Exercise 13.5: after removing the endpoint branches, the remaining core is
to choose a parameter from the interval cuts determined by the disjoint negative sets of the two
quadratics. -/
lemma existsParameter_nonnegOnRealQuadratics_core
    (aC bC cC aD bD cD : ℝ)
    (h_nonneg :
      ∀ r : ℝ, 0 ≤ aC * r ^ 2 + bC * r + cC ∨ 0 ≤ aD * r ^ 2 + bD * r + cD)
    (h_axis : 0 ≤ aC ∨ 0 ≤ aD)
    (hCneg : ∃ r, aC * r ^ 2 + bC * r + cC < 0)
    (hDneg : ∃ r, aD * r ^ 2 + bD * r + cD < 0) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ t * aC + (1 - t) * aD ∧
        ∀ r : ℝ,
          0 ≤
            (t * aC + (1 - t) * aD) * r ^ 2 +
              (t * bC + (1 - t) * bD) * r +
              (t * cC + (1 - t) * cD) := by
  -- Route correction: dispatch by the sign of the leading coefficients, then use either the
  -- root-basis PSD construction, its swapped copy, or the pure affine slope-cancellation branch.
  by_cases hposC : 0 < aC
  · exact existsParameter_nonnegOnRealQuadratics_of_posLeading
      aC bC cC aD bD cD hposC h_nonneg hCneg
  by_cases hposD : 0 < aD
  · rcases existsParameter_nonnegOnRealQuadratics_of_posLeading
        aD bD cD aC bC cC hposD (fun r ↦ by simpa [or_comm] using h_nonneg r) hDneg with
          ⟨s, hs, hslead, hsnonneg⟩
    refine ⟨1 - s, ?_, ?_, ?_⟩
    constructor
    · linarith [hs.2]
    · linarith [hs.1]
    · simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hslead
    · intro r
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
        mul_assoc] using hsnonneg r
  rcases h_axis with haCnonneg | haDnonneg
  · have haC0 : aC = 0 := by
      linarith
    have haD0 : aD = 0 := by
      by_contra hne
      have haDne : aD ≠ 0 := by
        simpa using hne
      have haDlt : aD < 0 := by
        rcases lt_or_gt_of_ne haDne with hlt | hgt
        · exact hlt
        · exact False.elim (hposD hgt)
      exact negLeading_impossible_of_affineDisjunctive
        bC cC aD bD cD haDlt
        (by intro r; simpa [haC0] using h_nonneg r)
        (by simpa [haC0] using hCneg)
    rcases existsParameter_nonnegOnAffineFunctions bC cC bD cD
        (by intro r; simpa [haC0, haD0] using h_nonneg r)
        (by simpa [haC0] using hCneg)
        (by simpa [haD0] using hDneg) with
          ⟨t, ht, hslope, hline⟩
    refine ⟨t, ht, ?_, ?_⟩
    · simp [haC0, haD0]
    · intro r
      simpa [haC0, haD0] using hline r
  · have haD0 : aD = 0 := by
      linarith
    have haC0 : aC = 0 := by
      by_contra hne
      have haCne : aC ≠ 0 := by
        simpa using hne
      have haClt : aC < 0 := by
        rcases lt_or_gt_of_ne haCne with hlt | hgt
        · exact hlt
        · exact False.elim (hposC hgt)
      exact negLeading_impossible_of_affineDisjunctive
        bD cD aC bC cC haClt
        (by
          intro r
          simpa [haD0, or_comm] using h_nonneg r)
        (by simpa [haD0] using hDneg)
    rcases existsParameter_nonnegOnAffineFunctions bC cC bD cD
        (by intro r; simpa [haC0, haD0] using h_nonneg r)
        (by simpa [haC0] using hCneg)
        (by simpa [haD0] using hDneg) with
          ⟨t, ht, hslope, hline⟩
    refine ⟨t, ht, ?_, ?_⟩
    · simp [haC0, haD0]
    · intro r
      simpa [haC0, haD0] using hline r

/-- Helper for Chapter13 Exercise 13.5: the remaining low-dimensional blocker is the companion
theorem about two real quadratics on the affine chart. -/
lemma existsParameter_nonnegOnRealQuadratics
    (aC bC cC aD bD cD : ℝ)
    (h_nonneg :
      ∀ r : ℝ, 0 ≤ aC * r ^ 2 + bC * r + cC ∨ 0 ≤ aD * r ^ 2 + bD * r + cD)
    (h_axis : 0 ≤ aC ∨ 0 ≤ aD) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ t * aC + (1 - t) * aD ∧
        ∀ r : ℝ,
          0 ≤
            (t * aC + (1 - t) * aD) * r ^ 2 +
              (t * bC + (1 - t) * bD) * r +
              (t * cC + (1 - t) * cD) := by
  by_cases hCglobal : ∀ r : ℝ, 0 ≤ aC * r ^ 2 + bC * r + cC
  · refine ⟨1, by simp, ?_, ?_⟩
    · -- The endpoint branch `t = 1` keeps the `C`-quadratic unchanged.
      simpa using leadingCoeff_nonneg_of_forall_nonnegQuadratic aC bC cC hCglobal
    · -- Once `qC` is globally nonnegative, the chart conclusion is immediate.
      simpa using hCglobal
  by_cases hDglobal : ∀ r : ℝ, 0 ≤ aD * r ^ 2 + bD * r + cD
  · refine ⟨0, by simp, ?_, ?_⟩
    · -- The endpoint branch `t = 0` keeps the `D`-quadratic unchanged.
      simpa using leadingCoeff_nonneg_of_forall_nonnegQuadratic aD bD cD hDglobal
    · -- Once `qD` is globally nonnegative, the chart conclusion is immediate.
      simpa using hDglobal
  have hCneg : ∃ r, aC * r ^ 2 + bC * r + cC < 0 := by
    simpa using hCglobal
  have hDneg : ∃ r, aD * r ^ 2 + bD * r + cD < 0 := by
    simpa using hDglobal
  -- The remaining branch is now isolated to the genuine interval-cut core.
  exact existsParameter_nonnegOnRealQuadratics_core
    aC bC cC aD bD cD h_nonneg h_axis hCneg hDneg

/-- Helper for Chapter13 Exercise 13.5: the only remaining low-dimensional core is the literal
`Fin 2` Yuan-lemma statement. -/
lemma existsParameter_nonnegOnFinTwo
    (C D : Matrix (Fin 2) (Fin 2) ℝ)
    (h_nonneg :
      ∀ u : Fin 2 → ℝ, 0 ≤ quadraticEval C u ∨ 0 ≤ quadraticEval D u) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, ∀ u : Fin 2 → ℝ,
      0 ≤ quadraticEval (t • C + (1 - t) • D) u := by
  have h_axis :
      0 ≤ C 0 0 ∨ 0 ≤ D 0 0 := by
    -- The basis vector `![1, 0]` reads off the leading coefficients on the affine chart.
    simpa [quadraticEval_finTwo_axisLeft] using h_nonneg ![1, 0]
  have h_line :
      ∀ r : ℝ,
        0 ≤ C 0 0 * r ^ 2 + (C 0 1 + C 1 0) * r + C 1 1 ∨
          0 ≤ D 0 0 * r ^ 2 + (D 0 1 + D 1 0) * r + D 1 1 := by
    intro r
    -- On the affine chart `![r, 1]`, the matrix quadratic form becomes an explicit real
    -- quadratic polynomial in `r`.
    simpa [quadraticEval_finTwo_line] using h_nonneg ![r, 1]
  rcases existsParameter_nonnegOnRealQuadratics
      (aC := C 0 0) (bC := C 0 1 + C 1 0) (cC := C 1 1)
      (aD := D 0 0) (bD := D 0 1 + D 1 0) (cD := D 1 1)
      h_line h_axis with ⟨t, ht, ht_axis, ht_line⟩
  refine ⟨t, ht, ?_⟩
  intro u
  by_cases hu : u 1 = 0
  · have hu_axis : u = (u 0) • ![1, 0] :=
      finTwo_eq_smul_axisLeft_of_second_eq_zero u hu
    have h_axis_eval :
        0 ≤ quadraticEval (t • C + (1 - t) • D) ![1, 0] := by
      -- The leading-coefficient inequality is exactly the axis evaluation.
      simpa [quadraticEval_finTwo_axisLeft] using ht_axis
    -- After normalizing to the axis, homogeneity transfers the nonnegativity to `u`.
    rw [hu_axis, quadraticEval_smul]
    nlinarith [sq_nonneg (u 0), h_axis_eval]
  · have hu_line : u = (u 1) • ![u 0 / u 1, 1] :=
      finTwo_eq_smul_line_of_second_ne_zero u hu
    have h_cross :
        t * (C 0 1 + C 1 0) + (1 - t) * (D 0 1 + D 1 0) =
          (t * C 0 1 + (1 - t) * D 0 1) + (t * C 1 0 + (1 - t) * D 1 0) := by
      ring
    have h_line_eval :
        0 ≤ quadraticEval (t • C + (1 - t) • D) ![u 0 / u 1, 1] := by
      -- The real-quadratic companion theorem handles the normalized affine chart.
      simpa [quadraticEval_finTwo_line, h_cross, add_assoc, add_left_comm, add_comm] using
        ht_line (u 0 / u 1)
    -- Homogeneity now pushes the chart estimate back to the original vector.
    rw [hu_line, quadraticEval_smul]
    nlinarith [sq_nonneg (u 1), h_line_eval]

/-- Helper for Chapter13 Exercise 13.5: the global Helly step only needs pairwise intersections of
the one-dimensional parameter sets. -/
lemma existsParameter_nonnegOn_pair
    (C D : Matrix ι ι ℝ)
    (h_nonneg :
      ∀ x : ι → ℝ, 0 ≤ quadraticEval C x ∨ 0 ≤ quadraticEval D x)
    (x y : ι → ℝ) :
    (goodParameterSet C D x ∩ goodParameterSet C D y).Nonempty := by
  classical
  -- Route correction: abandon the old `Submodule.span` restriction route and transport directly to
  -- the literal `Fin 2` problem built from the two columns `x` and `y`.
  let P : Matrix ι (Fin 2) ℝ := fun i ↦ ![x i, y i]
  have h_nonneg_finTwo :
      ∀ u : Fin 2 → ℝ,
        0 ≤ quadraticEval (P.transpose * C * P) u ∨
          0 ≤ quadraticEval (P.transpose * D * P) u := by
    intro u
    -- Push the ambient disjunction hypothesis through the conjugation identity.
    simpa [quadraticEval_mulVec_eq, P] using h_nonneg (P.mulVec u)
  rcases existsParameter_nonnegOnFinTwo (P.transpose * C * P) (P.transpose * D * P)
      h_nonneg_finTwo with ⟨t, ht, ht_nonneg⟩
  have hmul_basisLeft : P.mulVec ![1, 0] = x := by
    -- The first basis vector of `Fin 2` selects the first column `x`.
    ext i
    simp [P, Matrix.mulVec]
  have hmul_basisRight : P.mulVec ![0, 1] = y := by
    -- The second basis vector of `Fin 2` selects the second column `y`.
    ext i
    simp [P, Matrix.mulVec]
  have hconj_eval (u : Fin 2 → ℝ) :
      quadraticEval (t • (P.transpose * C * P) + (1 - t) • (P.transpose * D * P)) u =
        quadraticEval (t • C + (1 - t) • D) (P.mulVec u) := by
    -- Move the convex combination across the conjugation and then use the transport lemma.
    simpa [Matrix.mul_add, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
      using
        (quadraticEval_mulVec_eq (C := t • C + (1 - t) • D) (P := P) (u := u)).symm
  refine ⟨t, ?_⟩
  constructor
  · refine ⟨ht, ?_⟩
    -- Evaluating the transported witness on `![1, 0]` returns the original vector `x`.
    simpa [goodParameterSet, hconj_eval, hmul_basisLeft] using ht_nonneg ![1, 0]
  · refine ⟨ht, ?_⟩
    -- Evaluating the transported witness on `![0, 1]` returns the original vector `y`.
    simpa [goodParameterSet, hconj_eval, hmul_basisRight] using ht_nonneg ![0, 1]

/-- Helper for Chapter13 Exercise 13.5: Helly on the line only asks for nonempty intersections of
subfamilies of size at most `2`, so the finite-intersection input reduces to the `0`, `1`, and `2`
point cases. -/
lemma goodParameterSet_finiteIntersection_two
    (C D : Matrix ι ι ℝ)
    (h_nonneg :
      ∀ x : ι → ℝ, 0 ≤ quadraticEval C x ∨ 0 ≤ quadraticEval D x) :
    ∀ I : Finset (ι → ℝ), I.card ≤ 2 → (⋂ x ∈ I, goodParameterSet C D x).Nonempty := by
  classical
  intro I hI
  have hI' : I.card ≤ 2 := by
    simpa using hI
  by_cases h0 : I.card = 0
  · have hIeq : I = ∅ := Finset.card_eq_zero.mp h0
    subst I
    -- The empty intersection is the whole parameter line.
    simp
  by_cases h1 : I.card = 1
  · obtain ⟨x, hIeq⟩ := Finset.card_eq_one.mp h1
    subst I
    -- A singleton subfamily is handled by the endpoint witness for that vector.
    simpa using goodParameterSet_nonempty C D h_nonneg x
  have h2 : I.card = 2 := by
    omega
  obtain ⟨x, y, hxy, hIeq⟩ := Finset.card_eq_two.mp h2
  subst I
  -- The only nontrivial Helly case is the dedicated two-point intersection lemma.
  simpa [Finset.mem_insert, Finset.mem_singleton, hxy, Set.inter_assoc, Set.inter_left_comm,
    Set.inter_comm] using existsParameter_nonnegOn_pair C D h_nonneg x y

/-- Helper for Chapter13 Exercise 13.5: Helly's theorem on the parameter line `[0,1]` upgrades the
pairwise intersection statement to a single parameter working for every vector. -/
lemma existsCommonParameter_nonnegOn_all
    (C D : Matrix ι ι ℝ)
    (h_nonneg :
      ∀ x : ι → ℝ, 0 ≤ quadraticEval C x ∨ 0 ≤ quadraticEval D x) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, ∀ x : ι → ℝ, 0 ≤ quadraticEval (t • C + (1 - t) • D) x := by
  -- Helly on the one-dimensional parameter space upgrades the finite-intersection input to a
  -- single parameter that works for every vector simultaneously.
  obtain ⟨t, ht⟩ :=
    Convex.helly_theorem_compact'
      (F := fun x : ι → ℝ ↦ goodParameterSet C D x)
      (h_convex := goodParameterSet_convex C D)
      (h_compact := goodParameterSet_compact C D)
      (h_inter := by
        intro I hI
        exact goodParameterSet_finiteIntersection_two C D h_nonneg I (by simpa using hI))
  have ht_all : ∀ x : ι → ℝ, t ∈ goodParameterSet C D x := by
    simpa using ht
  refine ⟨t, (ht_all 0).1, ?_⟩
  intro x
  exact (ht_all x).2

/-- Helper for Chapter13 Exercise 13.5: the source cover hypothesis reduces to the owner-level
pointwise disjunction that at least one of the two quadratic forms is nonnegative at each vector. -/
theorem exists_posSemidef_convexCombination_of_quadratic_nonneg
    (C D : Matrix ι ι ℝ) (hC_symm : C.IsSymm) (hD_symm : D.IsSymm)
    (h_nonneg :
      ∀ x : ι → ℝ, 0 ≤ dotProduct x (C.mulVec x) ∨ 0 ≤ dotProduct x (D.mulVec x)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, (t • C + (1 - t) • D).PosSemidef := by
  rcases existsCommonParameter_nonnegOn_all C D h_nonneg with ⟨t, ht, ht_nonneg⟩
  refine ⟨t, ht, ?_⟩
  have hsymm : (t • C + (1 - t) • D).IsSymm := (hC_symm.smul t).add (hD_symm.smul (1 - t))
  have hherm : (t • C + (1 - t) • D).IsHermitian := by
    simpa [isHermitian_iff_isSymm] using hsymm
  -- Once the common parameter is found, the PSD conclusion is the standard matrix criterion.
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm ?_
  intro x
  simpa [quadraticEval] using ht_nonneg x

/-- Chapter13 Exercise 13.5: let `C, D : Matrix ι ι ℝ` be symmetric. If `A ∪ B = Set.univ`,
`x ↦ xᵀ C x` is nonnegative on `A`, and `x ↦ xᵀ D x` is nonnegative on `B`, then there exists
`t ∈ Set.Icc (0 : ℝ) 1` such that `t • C + (1 - t) • D` is positive semidefinite. The closedness
assumption from the source statement is not needed for this reduction. -/
theorem exists_posSemidef_convexCombination_of_quadratic_nonneg_on_cover
    (C D : Matrix ι ι ℝ) (hC_symm : C.IsSymm) (hD_symm : D.IsSymm)
    (A B : Set (ι → ℝ)) (h_cover : A ∪ B = Set.univ)
    (hC_nonneg : ∀ x ∈ A, 0 ≤ dotProduct x (C.mulVec x))
    (hD_nonneg : ∀ x ∈ B, 0 ≤ dotProduct x (D.mulVec x)) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, (t • C + (1 - t) • D).PosSemidef := by
  refine exists_posSemidef_convexCombination_of_quadratic_nonneg C D hC_symm hD_symm ?_
  intro x
  have hx : x ∈ A ∪ B := by
    rw [h_cover]
    simp
  rcases hx with hxA | hxB
  · exact Or.inl (hC_nonneg x hxA)
  · exact Or.inr (hD_nonneg x hxB)

end
