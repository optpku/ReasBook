/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_12

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

/-- The slope of the linear interpolant on the `k`th interval `[a_k, a_{k+1}]`. -/
noncomputable def polygonalSegmentSlope (a y : ℕ → ℝ) (k : ℕ) : ℝ :=
  (y (k + 1) - y k) / (a (k + 1) - a k)

/-- The coefficient `p_{k+1} = a_{k+1}(m_{k+2} - m_{k+1})` used in Example 15.15, with the terminal
slope interpreted as `0`. -/
noncomputable def polygonalWeight (a y : ℕ → ℝ) (n k : ℕ) : ℝ :=
  a (k + 1) *
    ((if _ : k + 1 < n then polygonalSegmentSlope a y (k + 1) else 0) -
      polygonalSegmentSlope a y k)

/-- A real-valued function is the polygonal interpolant from this example if it takes the
prescribed nodal values, is affine on each interpolation interval, vanishes outside `[-a_n, a_n]`,
and is even. -/
def IsEvenPolygonalInterpolant (n : ℕ) (a y : ℕ → ℝ) (φ : ℝ → ℝ) : Prop :=
  (∀ k ≤ n, φ (a k) = y k) ∧
    (∀ k < n,
      EqOn φ (fun x ↦ y k + polygonalSegmentSlope a y k * (x - a k)) (Icc (a k) (a (k + 1)))) ∧
    (∀ ⦃x : ℝ⦄, a n < |x| → φ x = 0) ∧
    Function.Even φ

-- Proof sketch: read off the first field of `IsEvenPolygonalInterpolant`.
/-- A polygonal interpolant takes the prescribed values at the interpolation nodes. -/
theorem isEvenPolygonalInterpolant_apply_nodes {n : ℕ} {a y : ℕ → ℝ} {φ : ℝ → ℝ}
    (hφ : IsEvenPolygonalInterpolant n a y φ) {k : ℕ} (hk : k ≤ n) :
    φ (a k) = y k :=
  hφ.1 k hk

/-- The explicit convex combination of the triangular measures appearing in Example 15.15. -/
noncomputable def polygonalCharacteristicMeasure (n : ℕ) (a y : ℕ → ℝ) : Measure ℝ :=
  Finset.sum (Finset.range n) fun k ↦
    ENNReal.ofReal (polygonalWeight a y n k) • triangularCharacteristicMeasure (a (k + 1))

/-- Helper for Example 15.15: the real tent-function combination attached to the polygonal
coefficients `polygonalWeight a y n k`. -/
noncomputable def polygonalTentCombination (n : ℕ) (a y : ℕ → ℝ) (t : ℝ) : ℝ :=
  Finset.sum (Finset.range n) fun k ↦
    polygonalWeight a y n k * max (1 - |t| / a (k + 1)) 0

/-- Helper for Example 15.15: the interpolation nodes `a i` are monotone on `0, …, n`. -/
lemma polygonalNode_mono {n : ℕ} {a : ℕ → ℝ}
    (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1)) :
    ∀ {i j : ℕ}, j ≤ n → i ≤ j → a i ≤ a j := by
  intro i j hj hij
  induction hij with
  | refl =>
      -- Proof comment: the endpoint case is immediate.
      exact le_rfl
  | @step j hij ih =>
      -- Proof comment: append one strict node step to the already established chain.
      have hj' : j ≤ n := by omega
      have hstep : j < n := by omega
      exact le_trans (ih hj') (le_of_lt (ha_strict hstep))

/-- Helper for Example 15.15: the interpolation nodes `a i` are strictly increasing on
`0, …, n`. -/
lemma polygonalNode_lt {n : ℕ} {a : ℕ → ℝ}
    (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1)) :
    ∀ {i j : ℕ}, j ≤ n → i < j → a i < a j := by
  intro i j hj hij
  have hstep : a i < a (i + 1) := ha_strict (lt_of_lt_of_le hij hj)
  exact lt_of_lt_of_le hstep
    (polygonalNode_mono ha_strict hj (Nat.succ_le_of_lt hij))

/-- Helper for Example 15.15: every positive-index node up to `n` is positive. -/
lemma polygonalNode_pos {n : ℕ} {a : ℕ → ℝ} (ha0 : a 0 = 0)
    (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1)) :
    ∀ {k : ℕ}, k ≤ n → 0 < k → 0 < a k := by
  intro k hk hk0
  rw [← ha0]
  exact polygonalNode_lt ha_strict hk hk0

/-- Helper for Example 15.15: the triangular law from Theorem 15.12 is a probability measure. -/
lemma triangularCharacteristicMeasure_isProbability {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (triangularCharacteristicMeasure r) := by
  -- Evaluating the characteristic function at `0` fixes the total mass.
  rw [MeasureTheory.isProbabilityMeasure_iff_real, ← Complex.ofReal_inj]
  simpa [MeasureTheory.charFun_zero, hr.ne', hr.le] using
    charFun_triangularCharacteristicMeasure r hr 0

/-- Helper for Example 15.15: the oscillatory kernel `x ↦ exp (t * x * I)` is integrable against
every finite measure on `ℝ`. -/
lemma integrableComplexExpKernel (μ : Measure ℝ) [IsFiniteMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ ↦ Complex.exp ((t * x : ℝ) * Complex.I)) μ := by
  -- Proof comment: the oscillatory kernel has constant norm `1`, so boundedness over a finite
  -- measure gives integrability immediately.
  refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x ↦ ?_)
  simpa using (le_of_eq (Complex.norm_exp_ofReal_mul_I (t * x)))

/-- Helper for Example 15.15: multiplying a secant slope by its interval length recovers the
corresponding nodal increment. -/
lemma polygonalSegmentSlope_mul_sub (a y : ℕ → ℝ) {k : ℕ}
    (hk : a k < a (k + 1)) :
    polygonalSegmentSlope a y k * (a (k + 1) - a k) = y (k + 1) - y k := by
  -- This is the defining cancellation of the denominator in the secant slope.
  unfold polygonalSegmentSlope
  field_simp [sub_ne_zero.mpr hk.ne']

/-- Helper for Example 15.15: dividing the coefficient `polygonalWeight a y n k` by the node
`a (k + 1)` removes the prefactor `a (k + 1)`. -/
lemma polygonalWeight_div_node (n : ℕ) (a y : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1)) {k : ℕ} (hk : k < n) :
    polygonalWeight a y n k / a (k + 1) =
      (if k + 1 < n then polygonalSegmentSlope a y (k + 1) else 0) -
        polygonalSegmentSlope a y k := by
  -- Positivity of the node lets us cancel the denominator exactly.
  have hpos : 0 < a (k + 1) :=
    polygonalNode_pos ha0 ha_strict (Nat.succ_le_of_lt hk) (Nat.succ_pos _)
  unfold polygonalWeight
  field_simp [hpos.ne']
  split_ifs <;> rfl

/-- Helper for Example 15.15: convexity forces every polygonal mixture weight to be nonnegative. -/
lemma polygonalWeight_nonneg
    (n : ℕ) (a y : ℕ → ℝ) (φ : ℝ → ℝ)
    (ha0 : a 0 = 0) (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    (hyn : y n = 0) (hφ : IsEvenPolygonalInterpolant n a y φ) (hconvex : ConvexOn ℝ (Ici 0) φ)
    {k : ℕ} (hk : k < n) :
    0 ≤ polygonalWeight a y n k := by
  have hnode_nonneg : ∀ {j : ℕ}, j ≤ n → 0 ≤ a j := by
    intro j hj
    rw [← ha0]
    exact polygonalNode_mono ha_strict hj (Nat.zero_le _)
  have hnode_pos : 0 < a (k + 1) :=
    polygonalNode_pos ha0 ha_strict (Nat.succ_le_of_lt hk) (Nat.succ_pos _)
  by_cases hk_next : k + 1 < n
  · -- Proof comment: away from the final node, convexity says successive secant slopes increase.
    have hslope_raw :=
      hconvex.slope_mono_adjacent
        (show a k ∈ Ici 0 from hnode_nonneg (Nat.le_of_lt hk))
        (show a (k + 2) ∈ Ici 0 from hnode_nonneg (Nat.succ_le_of_lt hk_next))
        (ha_strict hk) (ha_strict hk_next)
    have hslope :
        polygonalSegmentSlope a y k ≤ polygonalSegmentSlope a y (k + 1) := by
      calc
        polygonalSegmentSlope a y k
            = (φ (a (k + 1)) - φ (a k)) / (a (k + 1) - a k) := by
                rw [polygonalSegmentSlope,
                  isEvenPolygonalInterpolant_apply_nodes hφ (k := k) (Nat.le_of_lt hk),
                  isEvenPolygonalInterpolant_apply_nodes hφ (k := k + 1) (Nat.succ_le_of_lt hk)]
        _ ≤ (φ (a (k + 2)) - φ (a (k + 1))) / (a (k + 2) - a (k + 1)) := hslope_raw
        _ = polygonalSegmentSlope a y (k + 1) := by
              rw [polygonalSegmentSlope,
                isEvenPolygonalInterpolant_apply_nodes hφ (k := k + 1) (Nat.succ_le_of_lt hk),
                isEvenPolygonalInterpolant_apply_nodes hφ (k := k + 2) (Nat.succ_le_of_lt hk_next)]
    have hcoeff_nonneg :
        0 ≤ a (k + 1) * (polygonalSegmentSlope a y (k + 1) - polygonalSegmentSlope a y k) :=
      mul_nonneg (le_of_lt hnode_pos) (sub_nonneg.mpr hslope)
    simpa [polygonalWeight, hk_next] using hcoeff_nonneg
  · -- Proof comment: at the last interval, compare the final secant slope to the zero slope
    -- beyond `a n`, where the support condition forces the function to vanish.
    have hk_last : k + 1 = n := by
      omega
    have hxn_nonneg : 0 ≤ a n := hnode_nonneg le_rfl
    have hφ_an : φ (a n) = 0 := by
      simpa [hyn] using isEvenPolygonalInterpolant_apply_nodes hφ (k := n) le_rfl
    have hφ_after : φ (a n + 1) = 0 := by
      have hafter_nonneg : 0 ≤ a n + 1 := by linarith
      have hafter_abs : a n < |a n + 1| := by
        rw [abs_of_nonneg hafter_nonneg]
        linarith
      exact hφ.2.2.1 hafter_abs
    have hslope_raw :=
      hconvex.slope_mono_adjacent
        (show a k ∈ Ici 0 from hnode_nonneg (Nat.le_of_lt hk))
        (show a n + 1 ∈ Ici 0 by
          change 0 ≤ a n + 1
          linarith)
        (by simpa [hk_last] using ha_strict hk)
        (by linarith)
    have hslope :
        polygonalSegmentSlope a y k ≤ 0 := by
      calc
        polygonalSegmentSlope a y k
            = (φ (a n) - φ (a k)) / (a n - a k) := by
                rw [polygonalSegmentSlope, hk_last, hyn, hφ_an,
                  isEvenPolygonalInterpolant_apply_nodes hφ (k := k) (Nat.le_of_lt hk)]
        _ ≤ (φ (a n + 1) - φ (a n)) / (a n + 1 - a n) := hslope_raw
        _ = 0 := by rw [hφ_after, hφ_an]; ring
    have hcoeff_nonneg :
        0 ≤ a (k + 1) * (0 - polygonalSegmentSlope a y k) := by
      refine mul_nonneg (le_of_lt hnode_pos) ?_
      linarith
    simpa [polygonalWeight, hk_next] using hcoeff_nonneg

/-- Helper for Example 15.15: the characteristic function of the finite polygonal mixture is the
explicit real tent sum. -/
lemma charFun_polygonalCharacteristicMeasure_formula
    (n : ℕ) (a y : ℕ → ℝ) (φ : ℝ → ℝ)
    (ha0 : a 0 = 0) (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    (hyn : y n = 0) (hφ : IsEvenPolygonalInterpolant n a y φ) (hconvex : ConvexOn ℝ (Ici 0) φ)
    (t : ℝ) :
    charFun (polygonalCharacteristicMeasure n a y) t = (polygonalTentCombination n a y t : ℂ) :=
  by
    -- Proof comment: first expand the characteristic-function integral over the finite weighted
    -- sum of measures, then rewrite each triangular summand with the localized tent formula.
    have hInt :
        ∀ k ∈ Finset.range n,
          Integrable
            (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
            (ENNReal.ofReal (polygonalWeight a y n k) •
              triangularCharacteristicMeasure (a (k + 1))) := by
      intro k hk
      have hk_lt : k < n := Finset.mem_range.mp hk
      have hpos : 0 < a (k + 1) :=
        polygonalNode_pos ha0 ha_strict (Nat.succ_le_of_lt hk_lt) (Nat.succ_pos _)
      letI : IsProbabilityMeasure (triangularCharacteristicMeasure (a (k + 1))) :=
        triangularCharacteristicMeasure_isProbability hpos
      letI :
          IsFiniteMeasure
            (ENNReal.ofReal (polygonalWeight a y n k) •
              triangularCharacteristicMeasure (a (k + 1))) :=
        Measure.smul_finite (triangularCharacteristicMeasure (a (k + 1))) (by simp)
      simpa using
        integrableComplexExpKernel
          (μ := ENNReal.ofReal (polygonalWeight a y n k) •
            triangularCharacteristicMeasure (a (k + 1))) t
    have hsum :
        ∫ x, Complex.exp (t * x * Complex.I) ∂polygonalCharacteristicMeasure n a y =
          ∑ k ∈ Finset.range n,
            ∫ x, Complex.exp (t * x * Complex.I) ∂(
              ENNReal.ofReal (polygonalWeight a y n k) •
                triangularCharacteristicMeasure (a (k + 1))) := by
      simpa [polygonalCharacteristicMeasure] using
        (MeasureTheory.integral_finset_sum_measure
          (f := fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
          (μ := fun k ↦
            ENNReal.ofReal (polygonalWeight a y n k) •
              triangularCharacteristicMeasure (a (k + 1)))
          (s := Finset.range n)
          hInt)
    rw [MeasureTheory.charFun_apply_real, hsum]
    calc
      ∑ k ∈ Finset.range n,
          ∫ x, Complex.exp (t * x * Complex.I) ∂(
            ENNReal.ofReal (polygonalWeight a y n k) •
              triangularCharacteristicMeasure (a (k + 1))) =
        ∑ k ∈ Finset.range n,
          (((polygonalWeight a y n k : ℝ) : ℂ) *
            charFun (triangularCharacteristicMeasure (a (k + 1))) t) := by
              apply Finset.sum_congr rfl
              intro k hk
              have hk_lt : k < n := Finset.mem_range.mp hk
              have hweight_nonneg :
                  0 ≤ polygonalWeight a y n k :=
                polygonalWeight_nonneg n a y φ ha0 ha_strict hyn hφ hconvex hk_lt
              rw [MeasureTheory.integral_smul_measure, ← MeasureTheory.charFun_apply_real]
              rw [ENNReal.toReal_ofReal hweight_nonneg]
              change
                ((polygonalWeight a y n k : ℂ) *
                    charFun (triangularCharacteristicMeasure (a (k + 1))) t) =
                  ((polygonalWeight a y n k : ℂ) *
                    charFun (triangularCharacteristicMeasure (a (k + 1))) t)
              rfl
      _ = ∑ k ∈ Finset.range n,
            (((polygonalWeight a y n k : ℝ) : ℂ) *
              ((max (1 - |t| / a (k + 1)) 0 : ℝ) : ℂ)) := by
                apply Finset.sum_congr rfl
                intro k hk
                have hk_lt : k < n := Finset.mem_range.mp hk
                have hpos : 0 < a (k + 1) :=
                  polygonalNode_pos ha0 ha_strict (Nat.succ_le_of_lt hk_lt) (Nat.succ_pos _)
                rw [charFun_triangularCharacteristicMeasure (a (k + 1)) hpos t]
      _ = (polygonalTentCombination n a y t : ℂ) := by
            simp [polygonalTentCombination, mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Example 15.15: the tail sum of the normalized polygonal weights telescopes to the
negative of the left endpoint slope. -/
lemma polygonalWeight_tail_div_sum
    (n : ℕ) (a y : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    {k : ℕ} (hk : k < n) :
    Finset.sum (Finset.Ico k n) (fun j ↦ polygonalWeight a y n j / a (j + 1)) =
      -polygonalSegmentSlope a y k := by
  -- Proof comment: rewrite each normalized weight as the difference of two consecutive terms of
  -- the truncated slope sequence, then telescope over `Ico k n`.
  let truncatedSlope : ℕ → ℝ :=
    fun j ↦ if j < n then polygonalSegmentSlope a y j else 0
  have hweight :
      ∀ j ∈ Finset.Ico k n,
        polygonalWeight a y n j / a (j + 1) =
          truncatedSlope (j + 1) - truncatedSlope j := by
    intro j hj
    have hj_lt : j < n := (Finset.mem_Ico.mp hj).2
    rw [polygonalWeight_div_node n a y ha0 ha_strict hj_lt]
    rw [show truncatedSlope (j + 1) =
      (if j + 1 < n then polygonalSegmentSlope a y (j + 1) else 0) by
        rfl]
    rw [show truncatedSlope j = polygonalSegmentSlope a y j by
      simp [truncatedSlope, hj_lt]]
  have htel :
      ∀ m, k ≤ m →
        ∑ j ∈ Finset.Ico k m, (truncatedSlope (j + 1) - truncatedSlope j) =
          truncatedSlope m - truncatedSlope k := by
    intro m hkm
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkm
    induction d with
    | zero =>
        simp
    | succ d ih =>
        -- Proof comment: peel off the last interval and apply the induction hypothesis.
        have hkd : k ≤ k + d := Nat.le_add_right k d
        rw [show k + (d + 1) = (k + d) + 1 by omega, Finset.sum_Ico_succ_top hkd, ih hkd]
        ring
  calc
    Finset.sum (Finset.Ico k n) (fun j ↦ polygonalWeight a y n j / a (j + 1)) =
        ∑ j ∈ Finset.Ico k n, (truncatedSlope (j + 1) - truncatedSlope j) := by
          apply Finset.sum_congr rfl
          intro j hj
          exact hweight j hj
    _ = truncatedSlope n - truncatedSlope k := htel n (Nat.le_of_lt hk)
    _ = -polygonalSegmentSlope a y k := by
          simp [truncatedSlope, hk]

/-- Helper for Example 15.15: on each interpolation interval, the tent combination has the correct
secant slope. -/
lemma polygonalTentCombination_affine
    (n : ℕ) (a y : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    {k : ℕ} (hk : k < n) {x : ℝ} (hx : x ∈ Icc (a k) (a (k + 1))) :
    polygonalTentCombination n a y x =
      polygonalTentCombination n a y (a k) + polygonalSegmentSlope a y k * (x - a k) := by
  -- Proof comment: on the interval `[a k, a (k + 1)]`, all prefix tent kernels vanish and each
  -- surviving tail kernel becomes the affine expression `1 - z / a (j + 1)`.
  have hak_nonneg : 0 ≤ a k := by
    rw [← ha0]
    exact polygonalNode_mono ha_strict (Nat.le_of_lt hk) (Nat.zero_le _)
  have tailFormula :
      ∀ {z : ℝ}, z ∈ Icc (a k) (a (k + 1)) →
        polygonalTentCombination n a y z =
          ∑ j ∈ Finset.Ico k n, polygonalWeight a y n j * (1 - z / a (j + 1)) := by
    intro z hz
    have hz_nonneg : 0 ≤ z := le_trans hak_nonneg hz.1
    unfold polygonalTentCombination
    rw [← Finset.sum_range_add_sum_Ico
      (fun j ↦ polygonalWeight a y n j * max (1 - |z| / a (j + 1)) 0)
      (Nat.le_of_lt hk)]
    have hprefix :
        ∑ j ∈ Finset.range k, polygonalWeight a y n j * max (1 - |z| / a (j + 1)) 0 = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have hj_lt : j < k := Finset.mem_range.mp hj
      have hj_lt_n : j < n := lt_trans hj_lt hk
      have hpos : 0 < a (j + 1) :=
        polygonalNode_pos ha0 ha_strict (Nat.succ_le_of_lt hj_lt_n) (Nat.succ_pos _)
      have hnode : a (j + 1) ≤ a k :=
        polygonalNode_mono ha_strict (Nat.le_of_lt hk) (Nat.succ_le_of_lt hj_lt)
      have hnode_le_z : a (j + 1) ≤ z := le_trans hnode hz.1
      have hratio : 1 ≤ z / a (j + 1) := by
        rw [one_le_div hpos]
        exact hnode_le_z
      have hkernel : max (1 - |z| / a (j + 1)) 0 = 0 := by
        rw [abs_of_nonneg hz_nonneg, max_eq_right]
        linarith
      rw [hkernel, mul_zero]
    rw [hprefix, zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    rcases Finset.mem_Ico.mp hj with ⟨hkj, hjn⟩
    have hpos : 0 < a (j + 1) :=
      polygonalNode_pos ha0 ha_strict (Nat.succ_le_of_lt hjn) (Nat.succ_pos _)
    have hupper : z ≤ a (j + 1) := by
      exact le_trans hz.2
        (polygonalNode_mono ha_strict (Nat.succ_le_of_lt hjn) (Nat.succ_le_succ hkj))
    have hkernel : max (1 - |z| / a (j + 1)) 0 = 1 - z / a (j + 1) := by
      rw [abs_of_nonneg hz_nonneg, max_eq_left]
      rw [sub_nonneg]
      rw [div_le_one hpos]
      exact hupper
    rw [hkernel]
  have htail_x :
      polygonalTentCombination n a y x =
        ∑ j ∈ Finset.Ico k n, polygonalWeight a y n j * (1 - x / a (j + 1)) :=
    tailFormula hx
  have htail_node :
      polygonalTentCombination n a y (a k) =
        ∑ j ∈ Finset.Ico k n, polygonalWeight a y n j * (1 - a k / a (j + 1)) := by
    refine tailFormula ?_
    exact ⟨le_rfl, le_of_lt (ha_strict hk)⟩
  calc
    polygonalTentCombination n a y x =
        ∑ j ∈ Finset.Ico k n, polygonalWeight a y n j * (1 - x / a (j + 1)) := htail_x
    _ = ∑ j ∈ Finset.Ico k n,
          (polygonalWeight a y n j * (1 - a k / a (j + 1)) -
            (polygonalWeight a y n j / a (j + 1)) * (x - a k)) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
    _ = (∑ j ∈ Finset.Ico k n, polygonalWeight a y n j * (1 - a k / a (j + 1))) -
          (∑ j ∈ Finset.Ico k n, polygonalWeight a y n j / a (j + 1)) * (x - a k) := by
            rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ = (∑ j ∈ Finset.Ico k n, polygonalWeight a y n j * (1 - a k / a (j + 1))) -
          (-polygonalSegmentSlope a y k) * (x - a k) := by
            rw [polygonalWeight_tail_div_sum n a y ha0 ha_strict hk]
    _ = polygonalTentCombination n a y (a k) + polygonalSegmentSlope a y k * (x - a k) := by
          rw [htail_node]
          ring

/-- Helper for Example 15.15: the tent combination takes the prescribed values at all
interpolation nodes. -/
lemma polygonalTentCombination_apply_nodes
    (n : ℕ) (a y : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    (hyn : y n = 0) :
    ∀ k ≤ n, polygonalTentCombination n a y (a k) = y k := by
  intro k hk
  have hbase : polygonalTentCombination n a y (a n) = y n := by
    -- At the last node every tent function vanishes, so the sum collapses to `0 = y n`.
    have han_nonneg : 0 ≤ a n := by
      rw [← ha0]
      exact polygonalNode_mono ha_strict (le_rfl : n ≤ n) (Nat.zero_le _)
    have hzero : polygonalTentCombination n a y (a n) = 0 := by
      unfold polygonalTentCombination
      rw [Finset.sum_eq_zero]
      intro j hj
      have hj_lt : j < n := Finset.mem_range.mp hj
      have hnode : a (j + 1) ≤ a n :=
        polygonalNode_mono ha_strict (le_rfl : n ≤ n) (Nat.succ_le_of_lt hj_lt)
      have hpos : 0 < a (j + 1) :=
        polygonalNode_pos ha0 ha_strict (Nat.succ_le_of_lt hj_lt) (Nat.succ_pos _)
      have hratio : 1 ≤ a n / a (j + 1) := by
        rw [one_le_div hpos]
        linarith
      have htent : max (1 - |a n| / a (j + 1)) 0 = 0 := by
        rw [abs_of_nonneg han_nonneg, max_eq_right]
        linarith
      rw [htent, mul_zero]
    simpa [hyn] using hzero
  -- Descend from the terminal node and recover each previous value from the affine formula.
  refine Nat.decreasingInduction
    (motive := fun m _ ↦ polygonalTentCombination n a y (a m) = y m)
    (fun m hm ih ↦ ?_) hbase hk
  have h_aff :
      polygonalTentCombination n a y (a (m + 1)) =
        polygonalTentCombination n a y (a m) +
          polygonalSegmentSlope a y m * (a (m + 1) - a m) := by
    -- Evaluating the interval formula at the right endpoint gives the discrete recursion.
    simpa using
      polygonalTentCombination_affine n a y ha0 ha_strict hm
        (x := a (m + 1)) ⟨le_of_lt (ha_strict hm), le_rfl⟩
  calc
    polygonalTentCombination n a y (a m)
        = polygonalTentCombination n a y (a (m + 1)) -
            polygonalSegmentSlope a y m * (a (m + 1) - a m) := by
              linarith
    _ = y (m + 1) - (y (m + 1) - y m) := by
          rw [ih, polygonalSegmentSlope_mul_sub a y (ha_strict hm)]
    _ = y m := by ring

/-- Helper for Example 15.15: the tent combination itself is an even polygonal interpolant with
the prescribed nodes and support. -/
lemma polygonalTentCombination_isEvenPolygonalInterpolant
    (n : ℕ) (a y : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    (hyn : y n = 0) :
    IsEvenPolygonalInterpolant n a y (polygonalTentCombination n a y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- The reverse-induction lemma supplies all nodal values.
    exact polygonalTentCombination_apply_nodes n a y ha0 ha_strict hyn
  · intro k hk x hx
    -- On each interval the tent sum matches the affine interpolant with the correct left value.
    rw [polygonalTentCombination_affine n a y ha0 ha_strict hk hx]
    rw [polygonalTentCombination_apply_nodes n a y ha0 ha_strict hyn k (Nat.le_of_lt hk)]
  · intro x hx
    -- Outside `[-a n, a n]` every tent kernel vanishes because `a (k + 1) ≤ a n < |x|`.
    unfold polygonalTentCombination
    rw [Finset.sum_eq_zero]
    intro j hj
    have hj_lt : j < n := Finset.mem_range.mp hj
    have hnode : a (j + 1) ≤ a n :=
      polygonalNode_mono ha_strict (le_rfl : n ≤ n) (Nat.succ_le_of_lt hj_lt)
    have hpos : 0 < a (j + 1) :=
      polygonalNode_pos ha0 ha_strict (Nat.succ_le_of_lt hj_lt) (Nat.succ_pos _)
    have hratio : 1 ≤ |x| / a (j + 1) := by
      rw [one_le_div hpos]
      linarith
    have htent : max (1 - |x| / a (j + 1)) 0 = 0 := by
      rw [max_eq_right]
      linarith
    rw [htent, mul_zero]
  · intro x
    -- Evenness is immediate because every summand depends on `x` only through `|x|`.
    simp [polygonalTentCombination, abs_neg]

/-- Helper for Example 15.15: every point of `[0, a n)` belongs to some interpolation interval
`[a k, a (k + 1)]`. -/
lemma exists_polygonalInterval
    (n : ℕ) (a : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    (hn : 0 < n) {x : ℝ} (hx0 : 0 ≤ x) (hxn : x < a n) :
    ∃ k < n, x ∈ Icc (a k) (a (k + 1)) := by
  classical
  -- Proof comment: choose the largest node still at or below `x`; its successor must then sit
  -- above `x`.
  let k := Nat.findGreatest (fun m : ℕ ↦ a m ≤ x) n
  have hk_le : k ≤ n := Nat.findGreatest_le (P := fun m : ℕ ↦ a m ≤ x) n
  have hk_lower : a k ≤ x :=
    Nat.findGreatest_spec (P := fun m : ℕ ↦ a m ≤ x) (Nat.zero_le n) (by simpa [ha0] using hx0)
  have hk_lt : k < n := by
    refine lt_of_le_of_ne hk_le ?_
    intro hk_eq
    exact (not_le_of_gt hxn) (hk_eq ▸ hk_lower)
  have hk_upper : x ≤ a (k + 1) := by
    by_contra hupper
    have hk1_lower : a (k + 1) ≤ x := le_of_lt (lt_of_not_ge hupper)
    have : k + 1 ≤ k :=
      Nat.le_findGreatest (P := fun m : ℕ ↦ a m ≤ x) (Nat.succ_le_of_lt hk_lt) hk1_lower
    exact Nat.not_succ_le_self k this
  exact ⟨k, hk_lt, ⟨hk_lower, hk_upper⟩⟩

/-- Helper for Example 15.15: the polygonal interpolant with the prescribed intervals, support,
and evenness is unique. -/
lemma eq_of_isEvenPolygonalInterpolant
    (n : ℕ) (a y : ℕ → ℝ) (ha0 : a 0 = 0)
    (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    {ψ₁ ψ₂ : ℝ → ℝ}
    (hψ₁ : IsEvenPolygonalInterpolant n a y ψ₁)
    (hψ₂ : IsEvenPolygonalInterpolant n a y ψ₂) :
    ψ₁ = ψ₂ := by
  by_cases hn : n = 0
  · -- When `n = 0`, both functions agree at `0` and vanish away from `0`.
    ext x
    by_cases hx : x = 0
    · subst hx
      simpa [hn, ha0] using
        (isEvenPolygonalInterpolant_apply_nodes hψ₁ (k := 0) (by omega)).trans
          (isEvenPolygonalInterpolant_apply_nodes hψ₂ (k := 0) (by omega)).symm
    · have houtside : a n < |x| := by
        simp [hn, ha0, abs_pos, hx]
      rw [hψ₁.2.2.1 houtside, hψ₂.2.2.1 houtside]
  · have hn_pos : 0 < n := Nat.pos_iff_ne_zero.mpr hn
    have hnonneg :
        ∀ {x : ℝ}, 0 ≤ x → x ≤ a n → ψ₁ x = ψ₂ x := by
      intro x hx0 hxn_le
      by_cases hxn : x = a n
      · rw [hxn, isEvenPolygonalInterpolant_apply_nodes hψ₁ le_rfl,
          isEvenPolygonalInterpolant_apply_nodes hψ₂ le_rfl]
      · have hxn_lt : x < a n := lt_of_le_of_ne hxn_le hxn
        obtain ⟨k, hk, hxk⟩ := exists_polygonalInterval n a ha0 ha_strict hn_pos hx0 hxn_lt
        exact (hψ₁.2.1 k hk hxk).trans (hψ₂.2.1 k hk hxk).symm
    ext x
    by_cases houtside : a n < |x|
    · rw [hψ₁.2.2.1 houtside, hψ₂.2.2.1 houtside]
    · have hinside : |x| ≤ a n := le_of_not_gt houtside
      by_cases hx0 : 0 ≤ x
      · exact hnonneg hx0 (by simpa [abs_of_nonneg hx0] using hinside)
      · have hx_neg : x < 0 := lt_of_not_ge hx0
        have hneg_nonneg : 0 ≤ -x := by linarith
        have hneg_le : -x ≤ a n := by
          simpa [abs_of_neg hx_neg] using hinside
        have hneg_eq : ψ₁ (-x) = ψ₂ (-x) := hnonneg hneg_nonneg hneg_le
        calc
          ψ₁ x = ψ₁ (-x) := by symm; exact hψ₁.2.2.2 x
          _ = ψ₂ (-x) := hneg_eq
          _ = ψ₂ x := hψ₂.2.2.2 x

-- Proof sketch: first show from convexity on `[0, ∞)` that the slopes
-- `polygonalSegmentSlope a y k` are nondecreasing, so the coefficients `polygonalWeight a y n k`
-- are nonnegative and sum to `1`. Then apply `charFun_triangularCharacteristicMeasure` to each
-- summand, evaluate the finite weighted sum at the interpolation nodes by partial summation, and
-- conclude by linearity on each interval, evenness, and the compact support condition.
/-- The explicit polygonal measure from Example 15.15 is a probability measure. -/
theorem isProbabilityMeasure_polygonalCharacteristicMeasure
    (n : ℕ) (a y : ℕ → ℝ) (φ : ℝ → ℝ)
    (ha0 : a 0 = 0) (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    (hy0 : y 0 = 1) (hyn : y n = 0)
    (hφ : IsEvenPolygonalInterpolant n a y φ) (hconvex : ConvexOn ℝ (Ici 0) φ) :
    IsProbabilityMeasure (polygonalCharacteristicMeasure n a y) := by
  have htent : IsEvenPolygonalInterpolant n a y (polygonalTentCombination n a y) :=
    polygonalTentCombination_isEvenPolygonalInterpolant n a y ha0 ha_strict hyn
  have hEq : polygonalTentCombination n a y = φ :=
    eq_of_isEvenPolygonalInterpolant n a y ha0 ha_strict htent hφ
  have hφ0 : φ 0 = 1 := by
    simpa [ha0, hy0] using isEvenPolygonalInterpolant_apply_nodes hφ (k := 0) (Nat.zero_le n)
  -- Evaluate the characteristic-function identity at `0` to recover total mass `1`.
  rw [MeasureTheory.isProbabilityMeasure_iff_real, ← Complex.ofReal_inj, ← MeasureTheory.charFun_zero]
  calc
    charFun (polygonalCharacteristicMeasure n a y) 0 =
        (polygonalTentCombination n a y 0 : ℂ) := by
          simpa using
            charFun_polygonalCharacteristicMeasure_formula n a y φ ha0 ha_strict hyn hφ hconvex 0
    _ = (φ 0 : ℂ) := by
          simpa using congrArg (fun f : ℝ → ℝ ↦ (f 0 : ℂ)) hEq
    _ = 1 := by simpa [hφ0]

/-- The characteristic function of the explicit polygonal measure from Example 15.15 is the
polygonal interpolant `φ`. -/
theorem charFun_polygonalCharacteristicMeasure_eq
    (n : ℕ) (a y : ℕ → ℝ) (φ : ℝ → ℝ)
    (ha0 : a 0 = 0) (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    (hy0 : y 0 = 1) (hyn : y n = 0)
    (hφ : IsEvenPolygonalInterpolant n a y φ) (hconvex : ConvexOn ℝ (Ici 0) φ) :
    ∀ t : ℝ, charFun (polygonalCharacteristicMeasure n a y) t = (φ t : ℂ) := by
  have htent : IsEvenPolygonalInterpolant n a y (polygonalTentCombination n a y) :=
    polygonalTentCombination_isEvenPolygonalInterpolant n a y ha0 ha_strict hyn
  have hEq : polygonalTentCombination n a y = φ :=
    eq_of_isEvenPolygonalInterpolant n a y ha0 ha_strict htent hφ
  intro t
  -- The explicit tent-sum characteristic function agrees with `φ` by uniqueness.
  calc
    charFun (polygonalCharacteristicMeasure n a y) t =
        (polygonalTentCombination n a y t : ℂ) := by
          exact charFun_polygonalCharacteristicMeasure_formula n a y φ ha0 ha_strict hyn hφ hconvex t
    _ = (φ t : ℂ) := by
          simpa using congrArg (fun f : ℝ → ℝ ↦ (f t : ℂ)) hEq

/-- Example 15.15: an even compactly supported polygonal function on `ℝ` with vertices
`(a_k, y_k)`, linear interpolation on each interval, and convexity on `[0, ∞)` is the
characteristic function of the explicitly constructed probability measure
`polygonalCharacteristicMeasure n a y`. -/
theorem convexPolygonalInterpolant_isCharacteristicFunction
    (n : ℕ) (a y : ℕ → ℝ) (φ : ℝ → ℝ)
    (ha0 : a 0 = 0) (ha_strict : ∀ ⦃k : ℕ⦄, k < n → a k < a (k + 1))
    (hy0 : y 0 = 1) (hyn : y n = 0)
    (hφ : IsEvenPolygonalInterpolant n a y φ) (hconvex : ConvexOn ℝ (Ici 0) φ) :
    IsProbabilityMeasure (polygonalCharacteristicMeasure n a y) ∧
      ∀ t : ℝ, charFun (polygonalCharacteristicMeasure n a y) t = (φ t : ℂ) := by
  exact ⟨
    isProbabilityMeasure_polygonalCharacteristicMeasure n a y φ ha0 ha_strict hy0 hyn hφ hconvex,
    charFun_polygonalCharacteristicMeasure_eq n a y φ ha0 ha_strict hy0 hyn hφ hconvex
  ⟩
