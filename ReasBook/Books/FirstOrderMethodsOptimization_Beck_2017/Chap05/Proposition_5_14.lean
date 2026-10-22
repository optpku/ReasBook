/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Proposition_4_16

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp (ofLp)

noncomputable section

section

variable {n : ℕ}

local notation "Δ" => stdSimplex ℝ (Fin n)
local notation "E₁" => WithLp 1 (Fin n → ℝ)
local notation "E₂" => EuclideanSpace ℝ (Fin n)
local notation "Δ₁" => Set.preimage (ofLp : E₁ → Fin n → ℝ) Δ
local notation "Δ₂" => Set.preimage (ofLp : E₂ → Fin n → ℝ) Δ

/- Proposition 5.14 is `source-facing`: the primitive data are the negative entropy on the
standard simplex and the `ℓ₁`/`ℓ₂` ambient norms. The Chapter 4 owner
`negative_entropy_on_stdSimplex` already packages the canonical simplex entropy as an
extended-real-valued function, while mathlib's `StrongConvexOn` is the canonical owner for the
real-valued strong-convexity conclusion used here. This file therefore reuses the Chapter 4 owner
directly and exposes only the simplex-branch `.toReal` companion API needed downstream. -/

/-- On simplex points, the real-valued branch of `negative_entropy_on_stdSimplex` is the usual
coordinatewise negative-entropy sum. -/
@[simp] theorem negative_entropy_on_stdSimplex_toReal_of_mem
    {x : Fin n → ℝ} (hx : x ∈ Δ) :
    (negative_entropy_on_stdSimplex n x).toReal = ∑ i, x i * Real.log (x i) := by
  rw [negative_entropy_on_stdSimplex_of_mem hx]
  simp

/-- Helper for Proposition 5.14: the scalar entropy correction `x ↦ x log x - x² / 2` is convex
on `[0,1]`. -/
lemma convexOn_mul_log_sub_half_sq :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun x : ℝ ↦ x * Real.log x - x ^ (2 : ℕ) / 2) := by
  let f : ℝ → ℝ := fun x : ℝ ↦ x * Real.log x - x ^ (2 : ℕ) / 2
  let f' : ℝ → ℝ := fun x : ℝ ↦ Real.log x + 1 - x
  let f'' : ℝ → ℝ := fun x : ℝ ↦ x⁻¹ - 1
  -- Route correction: the Euclidean statement only needs a coordinatewise convexity bridge,
  -- so we avoid the more delicate segment-Hessian argument reserved for the `ℓ₁` modulus.
  change ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f
  refine
    convexOn_of_hasDerivWithinAt2_nonneg
      (D := Set.Icc (0 : ℝ) 1) (f := f) (f' := f') (f'' := f'')
      (convex_Icc (0 : ℝ) 1) ?_ ?_ ?_ ?_
  · -- Continuity combines the standard `x log x` extension at `0` with polynomial continuity.
    have hMulLog : Continuous fun x : ℝ ↦ x * Real.log x := Real.continuous_mul_log
    have hSquare : Continuous fun x : ℝ ↦ x ^ (2 : ℕ) / 2 := by
      continuity
    simpa [f] using (hMulLog.sub hSquare).continuousOn
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa using hx
    have hx0 : x ≠ 0 := hx'.1.ne'
    -- Differentiate the entropy term and the quadratic correction separately.
    have hMulLog :
        HasDerivAt (fun y : ℝ ↦ y * Real.log y) (Real.log x + 1) x :=
      Real.hasDerivAt_mul_log hx0
    have hSquare :
        HasDerivAt (fun y : ℝ ↦ y ^ (2 : ℕ) / 2) x x := by
      simpa [pow_two] using (hasDerivAt_pow 2 x).div_const (2 : ℝ)
    simpa [f, f', sub_eq_add_neg] using (hMulLog.sub hSquare).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa using hx
    have hx0 : x ≠ 0 := hx'.1.ne'
    -- The derivative `log x + 1 - x` has derivative `x⁻¹ - 1` on `(0,1)`.
    have hDeriv :
        HasDerivAt (fun y : ℝ ↦ Real.log y + 1 - y) (x⁻¹ - 1) x := by
      simpa [sub_eq_add_neg] using
        (((Real.hasDerivAt_log hx0).add_const (1 : ℝ)).sub (hasDerivAt_id x))
    simpa [f', f''] using hDeriv.hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa using hx
    have hInv : 1 ≤ x⁻¹ := (one_le_inv₀ hx'.1).2 (le_of_lt hx'.2)
    exact sub_nonneg.mpr hInv

/-- Helper for Proposition 5.14: under `a + b = 1`, the weighted square defect of two scalars is
`a * b * (u - v)^2`. -/
lemma weighted_square_defect_eq
    {a b u v : ℝ} (hab : a + b = 1) :
    a * u ^ (2 : ℕ) + b * v ^ (2 : ℕ) - (a * u + b * v) ^ (2 : ℕ) =
      a * b * (u - v) ^ (2 : ℕ) := by
  have hb' : b = 1 - a := by
    linarith
  rw [hb']
  ring

/-- Helper for Proposition 5.14: convexity of `x ↦ x log x - x² / 2` on `[0,1]` yields the
coordinatewise entropy gap with the exact quadratic defect. -/
lemma coordEntropyGap_ge_weightedSquareDefect
    {u v a b : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ((a * u + b * v) * Real.log (a * u + b * v)) + (a * b / 2) * (u - v) ^ (2 : ℕ) ≤
      a * (u * Real.log u) + b * (v * Real.log v) := by
  -- Apply convexity of the scalar entropy correction at the weighted midpoint.
  have hconv := convexOn_mul_log_sub_half_sq.2 hu hv ha hb hab
  simp only [smul_eq_mul] at hconv
  -- Rewrite the quadratic correction in the same normal form as the convexity inequality.
  have hsq :=
    congrArg (fun t : ℝ ↦ t / 2) (weighted_square_defect_eq (a := a) (b := b) (u := u) (v := v) hab)
  -- Rearranging the two scalar identities leaves exactly the desired Jensen gap.
  linarith

/-- Helper for Proposition 5.14: the simplex negative entropy satisfies the Euclidean Jensen gap
with modulus `1` in raw coordinates. -/
lemma entropyJensenGap_ge_l2Square
    {x y : Fin n → ℝ} (hx : x ∈ Δ) (hy : y ∈ Δ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (negative_entropy_on_stdSimplex n (a • x + b • y)).toReal +
        (a * b / 2) * ∑ i, (x i - y i) ^ (2 : ℕ) ≤
      a * (negative_entropy_on_stdSimplex n x).toReal +
        b * (negative_entropy_on_stdSimplex n y).toReal := by
  -- First place every entropy term on the simplex branch and record that the convex combination
  -- stays in the simplex.
  have hxy : a • x + b • y ∈ Δ :=
    (convex_stdSimplex (𝕜 := ℝ) (ι := Fin n)) hx hy ha hb hab
  rw [negative_entropy_on_stdSimplex_toReal_of_mem hxy]
  rw [negative_entropy_on_stdSimplex_toReal_of_mem hx]
  rw [negative_entropy_on_stdSimplex_toReal_of_mem hy]
  -- Each coordinate of a simplex point belongs to `[0,1]`, so the scalar bridge applies pointwise.
  have hcoord :
      ∀ i : Fin n,
        (((a * x i + b * y i) * Real.log (a * x i + b * y i)) +
            (a * b / 2) * (x i - y i) ^ (2 : ℕ)) ≤
          a * (x i * Real.log (x i)) + b * (y i * Real.log (y i)) := by
    intro i
    exact
      coordEntropyGap_ge_weightedSquareDefect
        (u := x i) (v := y i)
        (mem_Icc_of_mem_stdSimplex hx i)
        (mem_Icc_of_mem_stdSimplex hy i)
        ha hb hab
  -- Summing the coordinate inequalities gives the raw Euclidean Jensen gap.
  have hsum :
      ∑ i, (((a * x i + b * y i) * Real.log (a * x i + b * y i)) +
        (a * b / 2) * (x i - y i) ^ (2 : ℕ)) ≤
        ∑ i, (a * (x i * Real.log (x i)) + b * (y i * Real.log (y i))) := by
    exact Finset.sum_le_sum fun i _ ↦ hcoord i
  calc
    ∑ i, (a • x + b • y) i * Real.log ((a • x + b • y) i) + (a * b / 2) * ∑ i, (x i - y i) ^ (2 : ℕ)
        = ∑ i, (((a * x i + b * y i) * Real.log (a * x i + b * y i)) +
            (a * b / 2) * (x i - y i) ^ (2 : ℕ)) := by
            simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ i, (a * (x i * Real.log (x i)) + b * (y i * Real.log (y i))) := hsum
    _ = a * ∑ i, x i * Real.log (x i) + b * ∑ i, y i * Real.log (y i) := by
          simp [Finset.sum_add_distrib, Finset.mul_sum]

/-- Helper for Proposition 5.14: if two simplex coordinates sum to zero, then each coordinate
vanishes. -/
lemma simplexCoords_eq_zero_of_add_eq_zero
    {x y : Fin n → ℝ} (hx : x ∈ Δ) (hy : y ∈ Δ) {i : Fin n}
    (hxy : x i + y i = 0) : x i = 0 ∧ y i = 0 := by
  -- Each simplex coordinate is nonnegative, so a zero sum forces both summands to vanish.
  have hx_nonneg : 0 ≤ x i := (mem_Icc_of_mem_stdSimplex hx i).1
  have hy_nonneg : 0 ≤ y i := (mem_Icc_of_mem_stdSimplex hy i).1
  constructor <;> linarith

/-- Helper for Proposition 5.14: the fixed active support of a simplex segment carries all of the
segment mass. -/
lemma segmentSupportSum_eq_one
    {x y : Fin n → ℝ} (hx : x ∈ Δ) (hy : y ∈ Δ) (t : ℝ) :
    Finset.sum (Finset.univ.filter (fun i ↦ x i + y i ≠ 0))
      (fun i ↦ (1 - t) * x i + t * y i) = 1 := by
  -- Split `Finset.univ` into the active support and its zero complement.
  have hfull :
      ∑ i : Fin n, ((1 - t) * x i + t * y i) = 1 := by
    calc
      ∑ i : Fin n, ((1 - t) * x i + t * y i)
          = (1 - t) * ∑ i : Fin n, x i + t * ∑ i : Fin n, y i := by
              simp [Finset.mul_sum, Finset.sum_add_distrib]
      _ = (1 - t) * 1 + t * 1 := by rw [hx.2, hy.2]
      _ = 1 := by ring
  have hzero :
      Finset.sum (Finset.univ.filter (fun i ↦ ¬ (x i + y i ≠ 0)))
        (fun i ↦ (1 - t) * x i + t * y i) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hxy : x i + y i = 0 := by
      simpa using (Finset.mem_filter.mp hi).2
    rcases simplexCoords_eq_zero_of_add_eq_zero hx hy hxy with ⟨hx0, hy0⟩
    simp [hx0, hy0]
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun i : Fin n ↦ x i + y i ≠ 0)
      (f := fun i : Fin n ↦ ((1 - t) * x i + t * y i))
  rw [hzero, add_zero] at hsplit
  simpa using hsplit.trans hfull

/-- Helper for Proposition 5.14: on the fixed active support, every interior segment coordinate is
strictly positive. -/
lemma segmentCoordinate_pos_of_mem_support
    {x y : Fin n → ℝ} (hx : x ∈ Δ) (hy : y ∈ Δ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) {i : Fin n}
    (hi : i ∈ Finset.univ.filter (fun j ↦ x j + y j ≠ 0)) :
    0 < (1 - t) * x i + t * y i := by
  -- Route correction: expose support positivity directly before using Titu's lemma, instead of
  -- re-deriving it inside each reciprocal-form proof step.
  have hx_nonneg : 0 ≤ x i := (mem_Icc_of_mem_stdSimplex hx i).1
  have hy_nonneg : 0 ≤ y i := (mem_Icc_of_mem_stdSimplex hy i).1
  have hti : 0 < t := ht.1
  have hone_sub_t : 0 < 1 - t := by linarith [ht.2]
  have hsum_ne : x i + y i ≠ 0 := by
    simpa using (Finset.mem_filter.mp hi).2
  by_cases hx0 : x i = 0
  · have hy0 : y i ≠ 0 := by
      intro hy0
      exact hsum_ne (by simp [hx0, hy0])
    have hy_pos : 0 < y i := lt_of_le_of_ne hy_nonneg (Ne.symm hy0)
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg hone_sub_t.le hx_nonneg)
      (mul_pos hti hy_pos)
  · have hx_pos : 0 < x i := lt_of_le_of_ne hx_nonneg (Ne.symm hx0)
    exact add_pos_of_pos_of_nonneg
      (mul_pos hone_sub_t hx_pos)
      (mul_nonneg hti.le hy_nonneg)

/-- Helper for Proposition 5.14: Titu's lemma on the fixed active support yields the global
`ℓ₁`-square reciprocal-form bound along simplex segments. -/
lemma weightedL1Square_le_segmentReciprocalForm
    {x y : Fin n → ℝ} (hx : x ∈ Δ) (hy : y ∈ Δ) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∑ i : Fin n, |y i - x i|) ^ (2 : ℕ) ≤
      Finset.sum (Finset.univ.filter (fun i ↦ x i + y i ≠ 0))
        (fun i ↦ |y i - x i| ^ (2 : ℕ) / ((1 - t) * x i + t * y i)) := by
  set s : Finset (Fin n) := Finset.univ.filter (fun i ↦ x i + y i ≠ 0) with hs
  have hs_pos :
      ∀ i ∈ s, 0 < ((1 - t) * x i + t * y i) := by
    intro i hi
    simpa [hs] using segmentCoordinate_pos_of_mem_support hx hy ht hi
  have hs_abs :
      Finset.sum s (fun i ↦ |y i - x i|) = ∑ i : Fin n, |y i - x i| := by
    have hzero :
        Finset.sum (Finset.univ.filter (fun i ↦ ¬ (x i + y i ≠ 0)))
          (fun i ↦ |y i - x i|) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      have hxy : x i + y i = 0 := by
        simpa using (Finset.mem_filter.mp hi).2
      rcases simplexCoords_eq_zero_of_add_eq_zero hx hy hxy with ⟨hx0, hy0⟩
      simp [hx0, hy0]
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun i : Fin n ↦ x i + y i ≠ 0)
        (f := fun i : Fin n ↦ |y i - x i|)
    rw [hzero, add_zero] at hsplit
    simpa [hs] using hsplit
  have hs_sum :
      Finset.sum s (fun i ↦ ((1 - t) * x i + t * y i)) = 1 := by
    simpa [hs] using segmentSupportSum_eq_one hx hy t
  have hsq :
      (Finset.sum s (fun i ↦ |y i - x i|)) ^ (2 : ℕ) /
          Finset.sum s (fun i ↦ ((1 - t) * x i + t * y i)) ≤
        Finset.sum s (fun i ↦ |y i - x i| ^ (2 : ℕ) / ((1 - t) * x i + t * y i)) := by
    exact
      Finset.sq_sum_div_le_sum_sq_div
        (s := s) (f := fun i ↦ |y i - x i|) hs_pos
  rw [hs_sum, div_one, hs_abs] at hsq
  simpa [hs] using hsq

/-- Helper for Proposition 5.14: restricting the entropy sum to the fixed active support does not
change its value along the simplex segment, because the complement coordinates stay equal to `0`.
-/
lemma segmentEntropySum_eq_fullEntropySum
    {x y : Fin n → ℝ} (hx : x ∈ Δ) (hy : y ∈ Δ) (t : ℝ) :
    Finset.sum (Finset.univ.filter (fun i ↦ x i + y i ≠ 0))
      (fun i ↦ (((1 - t) * x i + t * y i) * Real.log ((1 - t) * x i + t * y i))) =
      ∑ i : Fin n, (((1 - t) * x i + t * y i) * Real.log ((1 - t) * x i + t * y i)) := by
  -- Split `Finset.univ` into the active support and its zero complement.
  have hzero :
      Finset.sum (Finset.univ.filter (fun i ↦ ¬ (x i + y i ≠ 0)))
        (fun i ↦ (((1 - t) * x i + t * y i) * Real.log ((1 - t) * x i + t * y i))) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    have hxy : x i + y i = 0 := by
      simpa using (Finset.mem_filter.mp hi).2
    rcases simplexCoords_eq_zero_of_add_eq_zero hx hy hxy with ⟨hx0, hy0⟩
    simp [hx0, hy0]
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not
      (s := Finset.univ) (p := fun i : Fin n ↦ x i + y i ≠ 0)
      (f := fun i : Fin n ↦ (((1 - t) * x i + t * y i) * Real.log ((1 - t) * x i + t * y i)))
  rw [hzero, add_zero] at hsplit
  simpa using hsplit

/-- Helper for Proposition 5.14: on the active support, the coordinate slice
`t ↦ ((1 - t) x_i + t y_i) log ((1 - t) x_i + t y_i)` admits explicit first and second
derivatives on the interior of `[0, 1]`. -/
lemma segmentCoordMulLog_hasDerivWithinAt2
    {x y : Fin n → ℝ} (hx : x ∈ Δ) (hy : y ∈ Δ) {i : Fin n}
    (hi : i ∈ Finset.univ.filter (fun j ↦ x j + y j ≠ 0))
    {t : ℝ} (ht : t ∈ interior (Set.Icc (0 : ℝ) 1)) :
    HasDerivWithinAt
        (fun u : ℝ ↦
          (((1 - u) * x i + u * y i) * Real.log ((1 - u) * x i + u * y i)))
        ((Real.log ((1 - t) * x i + t * y i) + 1) * (y i - x i))
        (interior (Set.Icc (0 : ℝ) 1)) t
      ∧
      HasDerivWithinAt
        (fun u : ℝ ↦ (Real.log ((1 - u) * x i + u * y i) + 1) * (y i - x i))
        ((y i - x i) ^ (2 : ℕ) / ((1 - t) * x i + t * y i))
        (interior (Set.Icc (0 : ℝ) 1)) t := by
  have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
    simpa [interior_Icc] using ht
  have hpos :
      0 < (1 - t) * x i + t * y i := segmentCoordinate_pos_of_mem_support hx hy ht' hi
  have hne : (1 - t) * x i + t * y i ≠ 0 := hpos.ne'
  have hsegment :
      HasDerivWithinAt
        (fun u : ℝ ↦ (1 - u) * x i + u * y i)
        (y i - x i)
        (interior (Set.Icc (0 : ℝ) 1)) t := by
    -- Differentiate the affine coordinate map once and reuse it in both derivative formulas.
    have hsegmentAt :
        HasDerivAt (fun u : ℝ ↦ (1 - u) * x i + u * y i) (y i - x i) t := by
      have hleft : HasDerivAt (fun u : ℝ ↦ (1 - u) * x i) (-x i) t := by
        simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
          (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).mul_const (x i))
      have hright : HasDerivAt (fun u : ℝ ↦ u * y i) (y i) t := by
        simpa [mul_comm] using ((hasDerivAt_id t).mul_const (y i))
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hleft.add hright
    exact hsegmentAt.hasDerivWithinAt
  constructor
  · -- Compose `u ↦ u log u` with the affine segment coordinate.
    have hMulLog :
        HasDerivAt (fun u : ℝ ↦ u * Real.log u)
          (Real.log ((1 - t) * x i + t * y i) + 1)
          ((1 - t) * x i + t * y i) := Real.hasDerivAt_mul_log hne
    simpa using hMulLog.comp_hasDerivWithinAt t hsegment
  · -- Differentiate the logarithmic gradient factor and keep the constant direction outside.
    have hLog :
        HasDerivAt (fun u : ℝ ↦ Real.log u + 1)
          (((1 - t) * x i + t * y i)⁻¹)
          ((1 - t) * x i + t * y i) := by
      simpa using (Real.hasDerivAt_log hne).add_const (1 : ℝ)
    have hlogComp :
        HasDerivWithinAt
          (fun u : ℝ ↦ Real.log ((1 - u) * x i + u * y i))
          ((((1 - t) * x i + t * y i)⁻¹) * (y i - x i))
          (interior (Set.Icc (0 : ℝ) 1)) t := by
      simpa using (Real.hasDerivAt_log hne).comp_hasDerivWithinAt t hsegment
    have hcomp :
        HasDerivWithinAt
          (fun u : ℝ ↦ Real.log ((1 - u) * x i + u * y i) + 1)
          ((((1 - t) * x i + t * y i)⁻¹) * (y i - x i))
          (interior (Set.Icc (0 : ℝ) 1)) t := by
      simpa using hlogComp.add_const (1 : ℝ)
    simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      hcomp.mul_const (y i - x i)

/-- Helper for Proposition 5.14: the active-support entropy slice corrected by the
`ℓ₁`-quadratic term is convex on `[0, 1]`. -/
lemma entropySliceConvexOn_activeSupport
    {x y : Fin n → ℝ} (hx : x ∈ Δ) (hy : y ∈ Δ) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t : ℝ ↦
        Finset.sum (Finset.univ.filter (fun i ↦ x i + y i ≠ 0))
          (fun i ↦ (((1 - t) * x i + t * y i) * Real.log ((1 - t) * x i + t * y i))) +
          (t * (1 - t) / 2) * (∑ i : Fin n, |x i - y i|) ^ (2 : ℕ)) := by
  let s : Finset (Fin n) := Finset.univ.filter (fun i ↦ x i + y i ≠ 0)
  let Lsq : ℝ := (∑ i : Fin n, |x i - y i|) ^ (2 : ℕ)
  -- Route correction: use the corrected slice with `+ (t * (1 - t) / 2) * Lsq`, whose second
  -- derivative is `entropy'' - Lsq` and is therefore controlled by the reciprocal-form estimate.
  refine
    convexOn_of_hasDerivWithinAt2_nonneg
      (D := Set.Icc (0 : ℝ) 1)
      (f := fun t : ℝ ↦
        Finset.sum s (fun i ↦ (((1 - t) * x i + t * y i) * Real.log ((1 - t) * x i + t * y i))) +
          (t * (1 - t) / 2) * Lsq)
      (f' := fun t : ℝ ↦
        Finset.sum s
          (fun i ↦ (Real.log ((1 - t) * x i + t * y i) + 1) * (y i - x i)) +
          ((1 - 2 * t) / 2) * Lsq)
      (f'' := fun t : ℝ ↦
        Finset.sum s (fun i ↦ (y i - x i) ^ (2 : ℕ) / ((1 - t) * x i + t * y i)) - Lsq)
      (convex_Icc (0 : ℝ) 1) ?_ ?_ ?_ ?_
  · -- Continuity is coordinatewise: each entropy summand is continuous, and so is the quadratic
    -- correction.
    have hsum :
        ContinuousOn
          (fun t : ℝ ↦
            Finset.sum s
              (fun i ↦ (((1 - t) * x i + t * y i) * Real.log ((1 - t) * x i + t * y i))))
          (Set.Icc (0 : ℝ) 1) := by
      refine continuousOn_finset_sum _ ?_
      intro i hi
      have hsegmentCont : Continuous fun u : ℝ ↦ (1 - u) * x i + u * y i := by
        continuity
      simpa using (Real.Continuous.mul_log hsegmentCont).continuousOn
    have hquad : ContinuousOn (fun t : ℝ ↦ (t * (1 - t) / 2) * Lsq) (Set.Icc (0 : ℝ) 1) := by
      have hquadCont : Continuous fun t : ℝ ↦ (t * (1 - t) / 2) * Lsq := by
        continuity
      exact hquadCont.continuousOn
    simpa [s, Lsq] using hsum.add hquad
  · intro t ht
    -- Sum the coordinate derivatives and add the explicit quadratic correction derivative.
    have hsum :
        HasDerivWithinAt
          (fun u : ℝ ↦
            Finset.sum s
              (fun i ↦ (((1 - u) * x i + u * y i) * Real.log ((1 - u) * x i + u * y i))))
          (Finset.sum s
            (fun i ↦ (Real.log ((1 - t) * x i + t * y i) + 1) * (y i - x i)))
          (interior (Set.Icc (0 : ℝ) 1)) t := by
      have hsumFun :
          Finset.sum s
              (fun i ↦ fun u : ℝ ↦
                (((1 - u) * x i + u * y i) * Real.log ((1 - u) * x i + u * y i))) =
            fun u : ℝ ↦
              Finset.sum s
                (fun i ↦ (((1 - u) * x i + u * y i) * Real.log ((1 - u) * x i + u * y i))) := by
        funext u
        simp [Finset.sum_apply]
      have hsumRaw :
          HasDerivWithinAt
            (Finset.sum s
              (fun i ↦ fun u : ℝ ↦
                (((1 - u) * x i + u * y i) * Real.log ((1 - u) * x i + u * y i))))
            (Finset.sum s
              (fun i ↦ (Real.log ((1 - t) * x i + t * y i) + 1) * (y i - x i)))
            (interior (Set.Icc (0 : ℝ) 1)) t :=
        HasDerivWithinAt.sum
          (u := s)
          (s := interior (Set.Icc (0 : ℝ) 1))
          (x := t)
          (A := fun i u ↦ (((1 - u) * x i + u * y i) * Real.log ((1 - u) * x i + u * y i)))
          (A' := fun i ↦ (Real.log ((1 - t) * x i + t * y i) + 1) * (y i - x i))
          (fun i hi ↦
            (segmentCoordMulLog_hasDerivWithinAt2 hx hy
              (show i ∈ s by simpa [s] using hi) ht).1)
      rw [hsumFun] at hsumRaw
      exact hsumRaw
    have hquad :
        HasDerivWithinAt
          (fun u : ℝ ↦ (u * (1 - u) / 2) * Lsq)
          (((1 - 2 * t) / 2) * Lsq)
          (interior (Set.Icc (0 : ℝ) 1)) t := by
      -- Differentiate the scalar quadratic correction explicitly.
      have hquadAt :
          HasDerivAt
            (fun u : ℝ ↦ (u * (1 - u) / 2) * Lsq)
            (((1 - 2 * t) / 2) * Lsq) t := by
        have hbase :
            HasDerivAt (fun u : ℝ ↦ u * (1 - u) / 2) ((1 - 2 * t) / 2) t := by
          have hmul : HasDerivAt (fun u : ℝ ↦ u * (1 - u)) (1 - 2 * t) t := by
            have hsub : HasDerivAt (fun u : ℝ ↦ u - u ^ (2 : ℕ)) (1 - 2 * t) t := by
              simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
                (hasDerivAt_id t).sub ((hasDerivAt_id t).pow 2)
            convert hsub using 1
            funext u
            ring
          simpa using hmul.div_const (2 : ℝ)
        simpa using hbase.mul_const Lsq
      simpa using hquadAt.hasDerivWithinAt
    simpa [s, Lsq] using hsum.add hquad
  · intro t ht
    -- Differentiate the first-derivative formula once more and record the constant second
    -- derivative of the quadratic correction.
    have hsum :
        HasDerivWithinAt
          (fun u : ℝ ↦
            Finset.sum s
              (fun i ↦ (Real.log ((1 - u) * x i + u * y i) + 1) * (y i - x i)))
          (Finset.sum s (fun i ↦ (y i - x i) ^ (2 : ℕ) / ((1 - t) * x i + t * y i)))
          (interior (Set.Icc (0 : ℝ) 1)) t := by
      have hsumFun :
          Finset.sum s
              (fun i ↦ fun u : ℝ ↦ (Real.log ((1 - u) * x i + u * y i) + 1) * (y i - x i)) =
            fun u : ℝ ↦
              Finset.sum s (fun i ↦ (Real.log ((1 - u) * x i + u * y i) + 1) * (y i - x i)) := by
        funext u
        simp [Finset.sum_apply]
      have hsumRaw :
          HasDerivWithinAt
            (Finset.sum s
              (fun i ↦ fun u : ℝ ↦ (Real.log ((1 - u) * x i + u * y i) + 1) * (y i - x i)))
            (Finset.sum s (fun i ↦ (y i - x i) ^ (2 : ℕ) / ((1 - t) * x i + t * y i)))
            (interior (Set.Icc (0 : ℝ) 1)) t :=
        HasDerivWithinAt.sum
          (u := s)
          (s := interior (Set.Icc (0 : ℝ) 1))
          (x := t)
          (A := fun i u ↦ (Real.log ((1 - u) * x i + u * y i) + 1) * (y i - x i))
          (A' := fun i ↦ (y i - x i) ^ (2 : ℕ) / ((1 - t) * x i + t * y i))
          (fun i hi ↦
            (segmentCoordMulLog_hasDerivWithinAt2 hx hy
              (show i ∈ s by simpa [s] using hi) ht).2)
      rw [hsumFun] at hsumRaw
      exact hsumRaw
    have hquad :
        HasDerivWithinAt
          (fun u : ℝ ↦ ((1 - 2 * u) / 2) * Lsq)
          (-Lsq)
          (interior (Set.Icc (0 : ℝ) 1)) t := by
      -- The derivative of `((1 - 2u) / 2) * Lsq` is the constant `-Lsq`.
      have hquadAt :
          HasDerivAt (fun u : ℝ ↦ ((1 - 2 * u) / 2) * Lsq) (-Lsq) t := by
        have hbase : HasDerivAt (fun u : ℝ ↦ (1 - 2 * u) / 2) (-1) t := by
          have hnum : HasDerivAt (fun u : ℝ ↦ 1 - 2 * u) (-2) t := by
            simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using
              (hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).const_mul (2 : ℝ))
          simpa using hnum.div_const (2 : ℝ)
        simpa using hbase.mul_const Lsq
      simpa using hquadAt.hasDerivWithinAt
    simpa [s, Lsq, sub_eq_add_neg] using hsum.add hquad
  · intro t ht
    have ht' : t ∈ Set.Ioo (0 : ℝ) 1 := by
      simpa [interior_Icc] using ht
    have hbound :=
      weightedL1Square_le_segmentReciprocalForm (n := n) (x := x) (y := y) hx hy ht'
    -- Rewrite the reciprocal-form bound into the precise second-derivative normal form.
    have hrewrite :
        Finset.sum s (fun i ↦ (y i - x i) ^ (2 : ℕ) / ((1 - t) * x i + t * y i))
          =
        Finset.sum (Finset.univ.filter (fun i ↦ x i + y i ≠ 0))
          (fun i ↦ |y i - x i| ^ (2 : ℕ) / ((1 - t) * x i + t * y i)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [sq_abs]
    change 0 ≤ Finset.sum s (fun i ↦ (y i - x i) ^ (2 : ℕ) / ((1 - t) * x i + t * y i)) - Lsq
    rw [show Lsq = (∑ i : Fin n, |y i - x i|) ^ (2 : ℕ) by
        simp [Lsq, abs_sub_comm], hrewrite]
    exact sub_nonneg.mpr hbound

/-- Helper for Proposition 5.14: the simplex negative entropy satisfies the raw `ℓ₁` Jensen gap
with modulus `1` in coordinates. -/
lemma entropyJensenGap_ge_l1Square
    {x y : Fin n → ℝ} (hx : x ∈ Δ) (hy : y ∈ Δ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (negative_entropy_on_stdSimplex n (a • x + b • y)).toReal +
        (a * b / 2) * (∑ i : Fin n, |x i - y i|) ^ (2 : ℕ) ≤
      a * (negative_entropy_on_stdSimplex n x).toReal +
        b * (negative_entropy_on_stdSimplex n y).toReal := by
  let s : Finset (Fin n) := Finset.univ.filter (fun i ↦ x i + y i ≠ 0)
  let Lsq : ℝ := (∑ i : Fin n, |x i - y i|) ^ (2 : ℕ)
  let φ : ℝ → ℝ := fun t : ℝ ↦
    Finset.sum s
      (fun i ↦ (((1 - t) * x i + t * y i) * Real.log ((1 - t) * x i + t * y i))) +
      (t * (1 - t) / 2) * Lsq
  have ha' : a = 1 - b := by
    linarith
  have hxy : a • x + b • y ∈ Δ :=
    (convex_stdSimplex (𝕜 := ℝ) (ι := Fin n)) hx hy ha hb hab
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) φ := by
    -- Use the corrected slice convexity statement proved on the fixed active support.
    simpa [φ, s, Lsq] using entropySliceConvexOn_activeSupport (n := n) hx hy
  have hphi : φ b ≤ a * φ 0 + b * φ 1 := by
    simpa [φ, smul_eq_mul] using hconv.2 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
      (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp) ha hb hab
  have hphi' :
      (negative_entropy_on_stdSimplex n (a • x + b • y)).toReal + (b * (1 - b) / 2) * Lsq ≤
        a * (negative_entropy_on_stdSimplex n x).toReal +
          b * (negative_entropy_on_stdSimplex n y).toReal := by
    -- Rewrite the slice values at `0`, `1`, and `b` back to the simplex entropy terms.
    have hmidEntropy :
        Finset.sum s
          (fun i ↦ (((1 - b) * x i + b * y i) * Real.log ((1 - b) * x i + b * y i))) =
            (negative_entropy_on_stdSimplex n (a • x + b • y)).toReal := by
      calc
        Finset.sum s
            (fun i ↦ (((1 - b) * x i + b * y i) * Real.log ((1 - b) * x i + b * y i)))
            = ∑ i : Fin n, (((1 - b) * x i + b * y i) * Real.log ((1 - b) * x i + b * y i)) := by
                simpa [s] using segmentEntropySum_eq_fullEntropySum (n := n) hx hy b
        _ = (negative_entropy_on_stdSimplex n ((1 - b) • x + b • y)).toReal := by
              rw [negative_entropy_on_stdSimplex_toReal_of_mem
                ((convex_stdSimplex (𝕜 := ℝ) (ι := Fin n)) hx hy
                  (by linarith [hb]) hb (by ring))]
              simp [smul_eq_mul]
        _ = (negative_entropy_on_stdSimplex n (a • x + b • y)).toReal := by
              have hsegEq : ((1 - b) • x + b • y) = a • x + b • y := by
                funext i
                simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha']
              simp [hsegEq]
    have hxEntropy :
        Finset.sum s (fun i ↦ (x i * Real.log (x i))) =
          (negative_entropy_on_stdSimplex n x).toReal := by
      calc
        Finset.sum s (fun i ↦ (x i * Real.log (x i)))
            = ∑ i : Fin n, x i * Real.log (x i) := by
                simpa [s] using segmentEntropySum_eq_fullEntropySum (n := n) hx hy (0 : ℝ)
        _ = (negative_entropy_on_stdSimplex n x).toReal := by
              rw [negative_entropy_on_stdSimplex_toReal_of_mem hx]
    have hyEntropy :
        Finset.sum s (fun i ↦ (y i * Real.log (y i))) =
          (negative_entropy_on_stdSimplex n y).toReal := by
      calc
        Finset.sum s (fun i ↦ (y i * Real.log (y i)))
            = ∑ i : Fin n, y i * Real.log (y i) := by
                simpa [s] using segmentEntropySum_eq_fullEntropySum (n := n) hx hy (1 : ℝ)
        _ = (negative_entropy_on_stdSimplex n y).toReal := by
              rw [negative_entropy_on_stdSimplex_toReal_of_mem hy]
    have hphi'' : φ b ≤
        a * (negative_entropy_on_stdSimplex n x).toReal +
          b * (negative_entropy_on_stdSimplex n y).toReal := by
      simpa [φ, Lsq, s, hxEntropy, hyEntropy] using hphi
    simpa [φ, Lsq, s, hmidEntropy] using hphi''
  have hquad : (b * (1 - b) / 2) * Lsq = (a * b / 2) * Lsq := by
    rw [← ha']
    ring
  simpa [hquad] using hphi'

-- Proof sketch: restrict the Chapter 4 extension-by-`∞` to the simplex, where
-- `negative_entropy_on_stdSimplex_toReal_of_mem` identifies it with the finite entropy sum.
-- Compute the Hessian on the relative interior as the diagonal form with entries `(x i)⁻¹`, then
-- use the weighted Cauchy-Schwarz inequality on tangent directions to obtain the quadratic lower
-- bound by the `ℓ₁` norm.
/-- Proposition 5.14 (1): the negative entropy on the unit simplex is `1`-strongly convex with
respect to the `l_1` norm, stated in the canonical real-valued form on the simplex itself. -/
theorem negative_entropy_on_stdSimplex_is_one_strongly_convex_l1 :
    StrongConvexOn
      Δ₁
      1
      (fun x : E₁ ↦
        (negative_entropy_on_stdSimplex n ((ofLp : E₁ → Fin n → ℝ) x)).toReal) := by
  refine ⟨?_, ?_⟩
  · -- Convex combinations in `WithLp 1` stay in the simplex after forgetting the `ℓ₁` normed
    -- wrapper, exactly as in the Euclidean branch.
    intro x hx y hy a b ha hb hab
    change ofLp (a • x + b • y) ∈ Δ
    simpa [WithLp.ofLp_add, WithLp.ofLp_smul] using
      ((convex_stdSimplex (𝕜 := ℝ) (ι := Fin n)) hx hy ha hb hab)
  · -- Consume the raw coordinate Jensen gap and rewrite the ambient `ℓ₁` norm only in the last
    -- line of the proof.
    intro x hx y hy a b ha hb hab
    have hraw :=
      entropyJensenGap_ge_l1Square
        (n := n) (x := ofLp x) (y := ofLp y) hx hy ha hb hab
    have hnorm :
        ‖x - y‖ ^ (2 : ℕ) = (∑ i : Fin n, |ofLp (x - y) i|) ^ (2 : ℕ) := by
      rw [PiLp.norm_eq_of_L1]
      simp [Real.norm_eq_abs]
    have hraw' :
        (negative_entropy_on_stdSimplex n ((ofLp : E₁ → Fin n → ℝ) (a • x + b • y))).toReal +
            (a * b / 2) * ‖x - y‖ ^ (2 : ℕ) ≤
          a * (negative_entropy_on_stdSimplex n ((ofLp : E₁ → Fin n → ℝ) x)).toReal +
            b * (negative_entropy_on_stdSimplex n ((ofLp : E₁ → Fin n → ℝ) y)).toReal := by
      rw [hnorm]
      simpa [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sub] using hraw
    have hfinal :
        (negative_entropy_on_stdSimplex n (ofLp (a • x + b • y))).toReal ≤
          a * (negative_entropy_on_stdSimplex n (ofLp x)).toReal +
            b * (negative_entropy_on_stdSimplex n (ofLp y)).toReal -
              a * b * ((1 : ℝ) / 2 * ‖x - y‖ ^ (2 : ℕ)) := by
      linarith
    simpa [smul_eq_mul] using hfinal

-- Proof sketch: use the same Hessian formula as in the `ℓ₁` statement and combine the tangent
-- lower bound by `‖h‖₁²` with the norm comparison `‖h‖₂ ≤ ‖h‖₁`. This yields the same modulus `1`
-- for the Euclidean norm on the simplex.
/-- Proposition 5.14 (2): the negative entropy on the unit simplex is `1`-strongly convex with
respect to the `l_2` norm, stated in the canonical real-valued form on the simplex itself. -/
theorem negative_entropy_on_stdSimplex_is_one_strongly_convex_l2 :
    StrongConvexOn
      Δ₂
      1
      (fun x : E₂ ↦
        (negative_entropy_on_stdSimplex n ((ofLp : E₂ → Fin n → ℝ) x)).toReal) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy a b ha hb hab
    change ofLp (a • x + b • y) ∈ Δ
    simpa [WithLp.ofLp_add, WithLp.ofLp_smul] using
      ((convex_stdSimplex (𝕜 := ℝ) (ι := Fin n)) hx hy ha hb hab)
  · intro x hx y hy a b ha hb hab
    have hraw :=
      entropyJensenGap_ge_l2Square
        (n := n) (x := ofLp x) (y := ofLp y) hx hy ha hb hab
    have hnorm :
        ‖x - y‖ ^ (2 : ℕ) = ∑ i, (ofLp (x - y) i) ^ (2 : ℕ) := by
      simpa using EuclideanSpace.real_norm_sq_eq (x - y)
    have hraw' :
        (negative_entropy_on_stdSimplex n ((ofLp : E₂ → Fin n → ℝ) (a • x + b • y))).toReal +
            (a * b / 2) * ‖x - y‖ ^ (2 : ℕ) ≤
          a * (negative_entropy_on_stdSimplex n ((ofLp : E₂ → Fin n → ℝ) x)).toReal +
            b * (negative_entropy_on_stdSimplex n ((ofLp : E₂ → Fin n → ℝ) y)).toReal := by
      rw [hnorm]
      simpa [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_sub] using hraw
    have hfinal :
        (negative_entropy_on_stdSimplex n (ofLp (a • x + b • y))).toReal ≤
          a * (negative_entropy_on_stdSimplex n (ofLp x)).toReal +
            b * (negative_entropy_on_stdSimplex n (ofLp y)).toReal -
              a * b * ((1 : ℝ) / 2 * ‖x - y‖ ^ (2 : ℕ)) := by
      linarith
    simpa [smul_eq_mul] using hfinal

end
