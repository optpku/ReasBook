/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_14

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators ENNReal InnerProductSpace

namespace EuclideanSpace

/-- The coordinate `ℓ^p` norm on the canonical Euclidean model `ℝ^N`. -/
noncomputable def lpNorm (N : ℕ) (p : ℝ≥0∞) : EuclideanSpace ℝ (Fin N) → ℝ :=
  fun x ↦ ‖WithLp.toLp p ((EuclideanSpace.equiv (Fin N) ℝ) x)‖

/- The textbook coordinate `ℓ^p` norm on `ℝ^N` is written `‖x‖_[p]`. -/
notation "‖" x "‖_[" p "]" => EuclideanSpace.lpNorm _ p x

/-- Evaluating `EuclideanSpace.lpNorm N p` recovers the usual `WithLp` coordinate formula. -/
@[simp] theorem lpNorm_apply
    (N : ℕ) (p : ℝ≥0∞) (x : EuclideanSpace ℝ (Fin N)) :
    ‖x‖_[p] = ‖WithLp.toLp p ((EuclideanSpace.equiv (Fin N) ℝ) x)‖ :=
  rfl

end EuclideanSpace

namespace Set

section

/-- The closed unit ball of the `ℓ^p` norm on `ℝ^N`, viewed inside the canonical Euclidean space
`EuclideanSpace ℝ (Fin N)`. -/
noncomputable def lpClosedUnitBall (N : ℕ) (p : ℝ≥0∞) :
    Set (EuclideanSpace ℝ (Fin N)) :=
  {x | ‖x‖_[p] ≤ 1}

-- Proof sketch: unfold `Set.lpClosedUnitBall`.
/-- A vector belongs to the `ℓ^p` closed unit ball exactly when its coordinate `ℓ^p` norm is at
most `1`. -/
theorem mem_lpClosedUnitBall_iff {N : ℕ} {p : ℝ≥0∞} {x : EuclideanSpace ℝ (Fin N)} :
    x ∈ lpClosedUnitBall N p ↔ ‖x‖_[p] ≤ 1 := by
  -- This is exactly the defining predicate of `lpClosedUnitBall`.
  rfl

/-- Helper for Exercise 7.9: in Euclidean coordinates over `ℝ`, the inner product is the usual
dot product. -/
private theorem inner_eq_coord_dotProduct {N : ℕ} (x y : EuclideanSpace ℝ (Fin N)) :
    ⟪x, y⟫_ℝ =
      dotProduct ((EuclideanSpace.equiv (Fin N) ℝ) x) ((EuclideanSpace.equiv (Fin N) ℝ) y) := by
  -- Move from the bundled Euclidean space to coordinate functions.
  simpa [dotProduct_comm] using EuclideanSpace.inner_eq_star_dotProduct x y

/-- Helper for Exercise 7.9: multiplying a real number by its sign recovers its absolute value. -/
private theorem real_sign_mul_self_eq_abs (r : ℝ) : Real.sign r * r = |r| := by
  -- Check the three sign cases separately.
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · rw [Real.sign_of_neg hr, abs_of_neg hr]
    ring
  · simp
  · rw [Real.sign_of_pos hr, abs_of_pos hr, one_mul]

/-- Helper for Exercise 7.9: the sign of a real number has norm at most `1`. -/
private theorem real_norm_sign_le_one (r : ℝ) : ‖Real.sign r‖ ≤ 1 := by
  -- The sign can only be `-1`, `0`, or `1`.
  rcases Real.sign_apply_eq r with hneg | hzero | hpos
  · rw [hneg]
    norm_num
  · rw [hzero]
    norm_num
  · rw [hpos]
    norm_num

/-- Helper for Exercise 7.9: finite-dimensional Hölder inequality in `WithLp` coordinates. -/
private theorem holder_sum_abs_mul_le_withLpNorm_mul_conjNorm
    {N : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (x y : Fin N → ℝ) :
    ∑ i, |x i * y i| ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp p.conjExponent y‖ := by
  -- Rewrite the endpoint norms explicitly, then use the finite-sum Hölder inequality.
  have hx₁ : ‖WithLp.toLp 1 x‖ = ∑ i, |x i| := by
    simpa [Real.norm_eq_abs] using PiLp.norm_eq_of_L1 (WithLp.toLp 1 x)
  have hy₁ : ‖WithLp.toLp 1 y‖ = ∑ i, |y i| := by
    simpa [Real.norm_eq_abs] using PiLp.norm_eq_of_L1 (WithLp.toLp 1 y)
  rcases (show 1 ≤ p from Fact.out).eq_or_lt with rfl | hp'
  · calc
      ∑ i, |x i * y i| = ∑ i, |x i| * |y i| := by simp [abs_mul]
      _ ≤ ∑ i, |x i| * ‖WithLp.toLp ∞ y‖ := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        exact mul_le_mul_of_nonneg_left
          (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp ∞ y) i)
          (abs_nonneg (x i))
      _ = (∑ i, |x i|) * ‖WithLp.toLp ∞ y‖ := by rw [Finset.sum_mul]
      _ = ‖WithLp.toLp 1 x‖ * ‖WithLp.toLp ∞ y‖ := by rw [← hx₁]
      _ = ‖WithLp.toLp 1 x‖ * ‖WithLp.toLp (ENNReal.conjExponent 1) y‖ := by
        rw [show ENNReal.conjExponent 1 = ∞ by simp [ENNReal.conjExponent]]
  · rcases eq_or_ne p ∞ with rfl | hp_top
    · calc
        ∑ i, |x i * y i| = ∑ i, |x i| * |y i| := by simp [abs_mul]
        _ ≤ ∑ i, ‖WithLp.toLp ∞ x‖ * |y i| := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          exact mul_le_mul_of_nonneg_right
            (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (WithLp.toLp ∞ x) i)
            (abs_nonneg (y i))
        _ = ‖WithLp.toLp ∞ x‖ * ∑ i, |y i| := by rw [Finset.mul_sum]
        _ = ‖WithLp.toLp ∞ x‖ * ‖WithLp.toLp 1 y‖ := by rw [hy₁]
        _ = ‖WithLp.toLp ∞ x‖ * ‖WithLp.toLp (ENNReal.conjExponent ∞) y‖ := by
          rw [show ENNReal.conjExponent ∞ = 1 by simp [ENNReal.conjExponent]]
    · have hp_toReal : 1 < p.toReal := by
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp'
      have hpq : p.toReal.HolderConjugate p.conjExponent.toReal :=
        ENNReal.HolderConjugate.toReal hp_toReal
      have hx :
          ‖WithLp.toLp p x‖ = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) := by
        simpa [Real.norm_eq_abs] using
          PiLp.norm_eq_sum (lt_trans zero_lt_one hp_toReal) (WithLp.toLp p x)
      have hy :
          ‖WithLp.toLp p.conjExponent y‖ =
            (∑ i, |y i| ^ p.conjExponent.toReal) ^ (1 / p.conjExponent.toReal) := by
        simpa [Real.norm_eq_abs] using
          PiLp.norm_eq_sum hpq.symm.pos (WithLp.toLp p.conjExponent y)
      calc
        ∑ i, |x i * y i| = ∑ i, |x i| * |y i| := by simp [abs_mul]
        _ ≤ (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) *
              (∑ i, |y i| ^ p.conjExponent.toReal) ^ (1 / p.conjExponent.toReal) := by
          simpa using
            (Real.inner_le_Lp_mul_Lq Finset.univ (fun i ↦ |x i|) (fun i ↦ |y i|) hpq)
        _ = ‖WithLp.toLp p x‖ * ‖WithLp.toLp p.conjExponent y‖ := by rw [hx, hy]

/-- Helper for Exercise 7.9: Hölder bounds the dot product by the product of the `ℓ^p` and
conjugate `ℓ^q` norms. -/
private theorem dotProduct_le_withLpNorm_mul_conjNorm
    {N : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (x y : Fin N → ℝ) :
    dotProduct x y ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp p.conjExponent y‖ := by
  -- First dominate the dot product by the sum of absolute coordinate products.
  calc
    dotProduct x y = ∑ i, x i * y i := rfl
    _ ≤ ∑ i, |x i * y i| := by
      exact Finset.sum_le_sum fun i _ ↦ le_abs_self (x i * y i)
    _ ≤ ‖WithLp.toLp p x‖ * ‖WithLp.toLp p.conjExponent y‖ :=
      holder_sum_abs_mul_le_withLpNorm_mul_conjNorm p x y

/-- Helper for Exercise 7.9: when `p = 1`, a signed coordinate vector at a maximal coordinate
attains the `ℓ^∞` support value. -/
private theorem exists_mem_lpClosedUnitBall_inner_eq_conjNorm_p_eq_one
    {N : ℕ} (y : EuclideanSpace ℝ (Fin N)) :
    ∃ x ∈ lpClosedUnitBall N 1,
      ⟪x, y⟫_ℝ = ‖WithLp.toLp ∞ ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ := by
  classical
  rcases isEmpty_or_nonempty (Fin N) with hι | hι
  · letI : IsEmpty (Fin N) := hι
    -- In the zero-dimensional case, every vector is zero, so the support value is zero.
    refine ⟨0, ?_, ?_⟩
    · rw [mem_lpClosedUnitBall_iff]
      simp
    · have hy : y = 0 := Subsingleton.elim _ _
      subst hy
      simp
  · letI : Nonempty (Fin N) := hι
    let coordY : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) y
    let s : Finset NNReal := Finset.univ.image fun i : Fin N => ‖coordY i‖₊
    let hs : s.Nonempty := by
      rcases hι with ⟨i⟩
      exact ⟨‖coordY i‖₊, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
    let M : NNReal := s.max' hs
    obtain ⟨i0, hi0eq⟩ : ∃ i0 : Fin N, ‖coordY i0‖₊ = M := by
      have hMmem : M ∈ s := Finset.max'_mem s hs
      rcases Finset.mem_image.mp hMmem with ⟨i0, _, hi0eq⟩
      exact ⟨i0, hi0eq⟩
    let a : Fin N → ℝ := fun i => if i = i0 then Real.sign (coordY i0) else 0
    let x : EuclideanSpace ℝ (Fin N) := (EuclideanSpace.equiv (Fin N) ℝ).symm a
    refine ⟨x, ?_, ?_⟩
    · -- The signed basis vector has `ℓ¹` norm exactly `|sign|`, hence at most one.
      rw [mem_lpClosedUnitBall_iff]
      change ‖WithLp.toLp 1 a‖ ≤ 1
      have ha : a = Pi.single i0 (Real.sign (coordY i0)) := by
        funext i
        by_cases hi : i = i0
        · subst hi
          simp [a, Pi.single]
        · simp [a, hi, Pi.single]
      rw [ha]
      simpa using real_norm_sign_le_one (coordY i0)
    · -- The inner product equals the maximal coordinate magnitude, which is the `ℓ^∞` norm.
      rw [inner_eq_coord_dotProduct]
      change dotProduct a coordY = ‖WithLp.toLp ∞ coordY‖
      have hdot : dotProduct a coordY = |coordY i0| := by
        rw [dotProduct]
        simp [a, real_sign_mul_self_eq_abs]
      have hsup_le : Finset.univ.sup (fun i : Fin N => ‖coordY i‖₊) ≤ M := by
        refine Finset.sup_le fun i _ ↦ ?_
        simpa [M] using
          (Finset.le_max' s ‖coordY i‖₊ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      have hM_le : M ≤ Finset.univ.sup (fun i : Fin N => ‖coordY i‖₊) := by
        rw [← hi0eq]
        exact Finset.le_sup (f := fun i : Fin N => ‖coordY i‖₊) (Finset.mem_univ i0)
      have hsup_eq : Finset.univ.sup (fun i : Fin N => ‖coordY i‖₊) = M :=
        le_antisymm hsup_le hM_le
      have habs : |coordY i0| = (M : ℝ) := by
        simpa [Real.norm_eq_abs] using congrArg (fun t : NNReal => (t : ℝ)) hi0eq
      have hnorm : ‖WithLp.toLp ∞ coordY‖ = (M : ℝ) := by
        rw [PiLp.norm_toLp, Pi.norm_def, hsup_eq]
      exact hdot.trans (habs.trans hnorm.symm)

/-- Helper for Exercise 7.9: when `p = ∞`, the coordinatewise sign vector attains the `ℓ¹`
support value. -/
private theorem exists_mem_lpClosedUnitBall_inner_eq_conjNorm_p_eq_top
    {N : ℕ} (y : EuclideanSpace ℝ (Fin N)) :
    ∃ x ∈ lpClosedUnitBall N ∞,
      ⟪x, y⟫_ℝ = ‖WithLp.toLp 1 ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ := by
  let coordY : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) y
  let a : Fin N → ℝ := fun i => Real.sign (coordY i)
  let x : EuclideanSpace ℝ (Fin N) := (EuclideanSpace.equiv (Fin N) ℝ).symm a
  refine ⟨x, ?_, ?_⟩
  · -- Every coordinate of the sign vector has norm at most one, so its `ℓ^∞` norm is at most one.
    rw [mem_lpClosedUnitBall_iff]
    change ‖WithLp.toLp ∞ a‖ ≤ 1
    rw [PiLp.norm_toLp, Pi.norm_def]
    exact_mod_cast Finset.sup_le fun i _ ↦ by
      simpa [a] using real_norm_sign_le_one (coordY i)
  · -- The sign vector turns the inner product into the sum of coordinate absolute values.
    rw [inner_eq_coord_dotProduct]
    change dotProduct a coordY = ‖WithLp.toLp 1 coordY‖
    rw [PiLp.norm_eq_of_L1]
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact real_sign_mul_self_eq_abs (coordY i)

/-- Helper for Exercise 7.9: in the strict Hölder regime, the maximizing `NNReal` witness from
`NNReal.isGreatest_Lp` yields a signed real vector in the `ℓ^p` unit ball attaining the
conjugate `ℓ^q` norm. -/
private theorem exists_mem_lpClosedUnitBall_inner_eq_conjNorm_of_one_lt_toReal
    {N : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp_top : p ≠ ∞) (hp_gt : 1 < p.toReal)
    (y : EuclideanSpace ℝ (Fin N)) :
    ∃ x ∈ lpClosedUnitBall N p,
      ⟪x, y⟫_ℝ = ‖WithLp.toLp p.conjExponent ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ := by
  have hp_ne_top : p ≠ ∞ := hp_top
  let coordY : Fin N → ℝ := (EuclideanSpace.equiv (Fin N) ℝ) y
  let f : Fin N → NNReal := fun i => ‖coordY i‖₊
  let q : ℝ := p.conjExponent.toReal
  have hpq : q.HolderConjugate p.toReal := by
    simpa [q] using (ENNReal.HolderConjugate.toReal hp_gt).symm
  have hgreatest := NNReal.isGreatest_Lp (s := Finset.univ) f hpq
  rcases hgreatest.1 with ⟨g, hg, hEq⟩
  let a : Fin N → ℝ := fun i => if coordY i = 0 then 0 else Real.sign (coordY i) * g i
  let x : EuclideanSpace ℝ (Fin N) := (EuclideanSpace.equiv (Fin N) ℝ).symm a
  refine ⟨x, ?_, ?_⟩
  · -- The signed maximizer stays in the `ℓ^p` ball because its coordinate magnitudes are bounded
    -- by the `NNReal` witness from `isGreatest_Lp`.
    rw [mem_lpClosedUnitBall_iff]
    change ‖WithLp.toLp p a‖ ≤ 1
    have hp_pos : 0 < p.toReal := lt_trans zero_lt_one hp_gt
    rw [PiLp.norm_eq_sum hp_pos]
    have hpow_le :
        (∑ i, |a i| ^ p.toReal) ≤ ∑ i, (g i : ℝ) ^ p.toReal := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      have hle : |a i| ≤ g i := by
        by_cases hzi : coordY i = 0
        · simp [a, hzi]
        · calc
            |a i| = |Real.sign (coordY i) * g i| := by simp [a, hzi]
            _ = |Real.sign (coordY i)| * g i := by
              rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg (g i))]
            _ ≤ 1 * g i := by
              gcongr
              rcases Real.sign_apply_eq (coordY i) with hs | hs | hs <;> simp [hs]
            _ = g i := by ring
      exact Real.rpow_le_rpow (abs_nonneg _) hle (by positivity)
    have hg_real : (∑ i, (g i : ℝ) ^ p.toReal) ≤ 1 := by
      exact_mod_cast hg
    have hsum_le : (∑ i, |a i| ^ p.toReal) ≤ 1 := hpow_le.trans hg_real
    have hnorm_le :=
      Real.rpow_le_rpow
        (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg _) _)
        hsum_le
        (by positivity : 0 ≤ 1 / p.toReal)
    simpa using hnorm_le
  · -- Route correction: use `NNReal.isGreatest_Lp` on the nonnegative coordinate magnitudes,
    -- then restore signs only after obtaining the maximizing absolute-value witness.
    rw [inner_eq_coord_dotProduct]
    change dotProduct a coordY = ‖WithLp.toLp p.conjExponent coordY‖
    have hdot :
        dotProduct a coordY = ∑ i, (f i : ℝ) * g i := by
      rw [dotProduct]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases hzi : coordY i = 0
      · simp [a, f, hzi]
      · calc
          a i * coordY i = (Real.sign (coordY i) * g i) * coordY i := by simp [a, hzi]
          _ = (Real.sign (coordY i) * coordY i) * g i := by ring
          _ = |coordY i| * g i := by rw [real_sign_mul_self_eq_abs]
          _ = (f i : ℝ) * g i := by
            change |coordY i| * g i = ‖coordY i‖ * g i
            rw [Real.norm_eq_abs]
    have hEq_real : ∑ i, (f i : ℝ) * g i = (∑ i, (f i : ℝ) ^ q) ^ (1 / q) := by
      exact_mod_cast hEq
    have hq_pos : 0 < p.conjExponent.toReal := by
      simpa [q] using hpq.pos
    have hnorm_q : ‖WithLp.toLp p.conjExponent coordY‖ = (∑ i, (f i : ℝ) ^ q) ^ (1 / q) := by
      simpa [f, q, Real.norm_eq_abs] using
        (PiLp.norm_eq_sum (p := p.conjExponent) (β := fun _ : Fin N => ℝ) hq_pos
          (WithLp.toLp p.conjExponent coordY))
    exact hdot.trans (hEq_real.trans hnorm_q.symm)

/-- Helper for Exercise 7.9: the support functional of the `ℓ^p` unit ball attains the conjugate
`ℓ^q` norm. -/
private theorem exists_mem_lpClosedUnitBall_inner_eq_conjNorm
    {N : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (y : EuclideanSpace ℝ (Fin N)) :
    ∃ x ∈ lpClosedUnitBall N p,
      ⟪x, y⟫_ℝ = ‖WithLp.toLp p.conjExponent ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ := by
  -- Split the support-attainment argument into the endpoint witnesses and the strict Hölder case.
  rcases eq_or_ne p 1 with rfl | hp_ne_one
  · obtain ⟨x, hx, hxy⟩ := exists_mem_lpClosedUnitBall_inner_eq_conjNorm_p_eq_one y
    have hconj : ENNReal.conjExponent 1 = ∞ := by
      simp [ENNReal.conjExponent]
    refine ⟨x, hx, ?_⟩
    calc
      ⟪x, y⟫_ℝ = ‖WithLp.toLp ∞ ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ := hxy
      _ = ‖(EuclideanSpace.equiv (Fin N) ℝ) y‖ := by
        exact PiLp.norm_toLp ((EuclideanSpace.equiv (Fin N) ℝ) y)
      _ = ‖WithLp.toLp (ENNReal.conjExponent 1) ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ := by
        rw [hconj]
        exact (PiLp.norm_toLp ((EuclideanSpace.equiv (Fin N) ℝ) y)).symm
  · rcases eq_or_ne p ∞ with rfl | hp_top
    · obtain ⟨x, hx, hxy⟩ := exists_mem_lpClosedUnitBall_inner_eq_conjNorm_p_eq_top y
      have hconj : ENNReal.conjExponent ∞ = 1 := by
        simp [ENNReal.conjExponent]
      refine ⟨x, hx, ?_⟩
      calc
        ⟪x, y⟫_ℝ = ‖WithLp.toLp 1 ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ := hxy
        _ = ‖WithLp.toLp (ENNReal.conjExponent ∞) ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ := by
          rw [hconj]
    · have hp_one_lt : (1 : ℝ≥0∞) < p := lt_of_le_of_ne Fact.out (by simpa using hp_ne_one.symm)
      have hp_gt : 1 < p.toReal := by
        rw [← ENNReal.toReal_one]
        exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp_one_lt
      simpa using
        exists_mem_lpClosedUnitBall_inner_eq_conjNorm_of_one_lt_toReal p hp_top hp_gt y

/-- Helper for Exercise 7.9: a vector is in the polar of the `ℓ^p` unit ball exactly when its
conjugate `ℓ^q` norm is at most `1`. -/
private theorem forall_inner_le_one_on_lpClosedUnitBall_iff
    {N : ℕ} (p : ℝ≥0∞) [Fact (1 ≤ p)] (y : EuclideanSpace ℝ (Fin N)) :
    (∀ x ∈ lpClosedUnitBall N p, ⟪x, y⟫_ℝ ≤ 1) ↔
      ‖WithLp.toLp p.conjExponent ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ ≤ 1 := by
  constructor
  · intro hy
    -- Evaluate the assumed bound at a support-attaining witness to recover the conjugate norm.
    obtain ⟨x, hx, hxy⟩ := exists_mem_lpClosedUnitBall_inner_eq_conjNorm p y
    simpa [hxy] using hy x hx
  · intro hy x hx
    -- Hölder's inequality bounds every inner product by the product of the two relevant norms.
    rw [inner_eq_coord_dotProduct]
    letI : Fact (1 ≤ p.conjExponent) := ⟨ENNReal.HolderConjugate.one_le p.conjExponent p⟩
    have hy_nonneg :
        0 ≤ ‖WithLp.toLp p.conjExponent ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ := by
      exact norm_nonneg _
    have hholder :=
      dotProduct_le_withLpNorm_mul_conjNorm p
        ((EuclideanSpace.equiv (Fin N) ℝ) x) ((EuclideanSpace.equiv (Fin N) ℝ) y)
    rw [mem_lpClosedUnitBall_iff] at hx
    calc
      dotProduct ((EuclideanSpace.equiv (Fin N) ℝ) x) ((EuclideanSpace.equiv (Fin N) ℝ) y)
          ≤ ‖WithLp.toLp p ((EuclideanSpace.equiv (Fin N) ℝ) x)‖ *
              ‖WithLp.toLp p.conjExponent ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ := hholder
      _ ≤ 1 * ‖WithLp.toLp p.conjExponent ((EuclideanSpace.equiv (Fin N) ℝ) y)‖ := by
        exact mul_le_mul_of_nonneg_right hx hy_nonneg
      _ ≤ 1 * 1 := by
        exact mul_le_mul_of_nonneg_left hy (by norm_num)
      _ = 1 := by norm_num

-- Proof sketch: rewrite membership in the polar set using
-- `mem_polarSet_iff_forall_inner_le_one`, identify the support functional of the `ℓ^p` unit ball
-- with the `ℓ^q` norm by Hölder's inequality, and transport the coordinate formula through
-- `EuclideanSpace.equiv`, where `q = p.conjExponent`.
/-- The polar set of the `ℓ^p` closed unit ball in `ℝ^N` is exactly the set of vectors whose
coordinate `ℓ^q` norm is at most `1`, where `q = p.conjExponent`. -/
theorem polarSet_lpClosedUnitBall_eq_setOf_conjNorm_le_one
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (lpClosedUnitBall N p)ᵒ⊙ =
      {y : EuclideanSpace ℝ (Fin N) |
        EuclideanSpace.lpNorm N p.conjExponent y ≤ 1} := by
  ext y
  -- Rewrite polar membership pointwise, then identify the support value with the conjugate norm.
  rw [mem_polarSet_iff_forall_inner_le_one, mem_setOf_eq,
    forall_inner_le_one_on_lpClosedUnitBall_iff p y, EuclideanSpace.lpNorm]

-- Proof sketch: combine
-- `polarSet_lpClosedUnitBall_eq_setOf_conjNorm_le_one` with the definition of the conjugate
-- exponent unit ball.
/-- Exercise 7.9: the polar set of the `ℓ^p` closed unit ball in `ℝ^N` is the conjugate
`ℓ^q` closed unit ball, not the singleton `{0}`. -/
theorem polarSet_lpClosedUnitBall_eq_conj_unitBall
    (N : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    (lpClosedUnitBall N p)ᵒ⊙ = lpClosedUnitBall N p.conjExponent := by
  ext y
  -- The intermediate set-of-norm description is exactly the conjugate unit ball definition.
  rw [polarSet_lpClosedUnitBall_eq_setOf_conjNorm_le_one, mem_setOf_eq, mem_lpClosedUnitBall_iff]

end

end Set
