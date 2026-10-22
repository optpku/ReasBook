/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4.Conjugate
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_6
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Example_8_6.Penalty

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- Helper for Exercise 8.8: when `‖y‖ ≤ 1`, each affine-quadratic integrand
term for `huberPenalty ε` is bounded above by `(ε / 2) * ‖y‖ ^ 2`. -/
private lemma innerSubHuberPenaltyLeQuadraticOfNormLeOne
    (ε : ℝ) (hε : 0 < ε) (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 1) :
    ∀ x : EuclideanSpace ℝ (Fin d),
      inner ℝ x y - huberPenalty ε x ≤ (ε / 2) * ‖y‖ ^ 2 := by
  intro x
  have hinner : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  rw [huberPenalty_def ε x]
  by_cases hx : ‖x‖ ≤ ε
  · -- On the quadratic branch, a completed square gives the bound.
    have hstep :
        inner ℝ x y - ‖x‖ ^ 2 / (2 * ε) ≤ ‖x‖ * ‖y‖ - ‖x‖ ^ 2 / (2 * ε) := by
      nlinarith
    have hquad :
        ‖x‖ * ‖y‖ - ‖x‖ ^ 2 / (2 * ε) ≤ (ε / 2) * ‖y‖ ^ 2 := by
      have hεne : ε ≠ 0 := ne_of_gt hε
      field_simp [hεne]
      nlinarith [sq_nonneg (‖x‖ - ε * ‖y‖)]
    rw [if_pos hx]
    exact hstep.trans hquad
  · -- On the affine branch, combine `‖y‖ ≤ 1` with the square `(‖y‖ - 1)^2`.
    have hx' : ε < ‖x‖ := lt_of_not_ge hx
    have hstep :
        inner ℝ x y - (‖x‖ - ε / 2) ≤ ‖x‖ * ‖y‖ - (‖x‖ - ε / 2) := by
      nlinarith
    have haffine :
        ‖x‖ * ‖y‖ - (‖x‖ - ε / 2) ≤ (ε / 2) * ‖y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖y‖ - 1), hε, hx', hy]
    rw [if_neg hx]
    exact hstep.trans haffine

/-- Helper for Exercise 8.8: the witness `x = ε • y` attains the finite
conjugate value when `‖y‖ ≤ 1`. -/
private lemma innerSubHuberPenaltyAtEpsSmul
    (ε : ℝ) (hε : 0 < ε) (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 1) :
    inner ℝ (ε • y) y - huberPenalty ε (ε • y) = (ε / 2) * ‖y‖ ^ 2 := by
  have hwitnessNorm : ‖ε • y‖ ≤ ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    nlinarith
  have hbranch : huberPenalty ε (ε • y) = ‖ε • y‖ ^ 2 / (2 * ε) := by
    -- The explicit witness stays inside the quadratic branch.
    rw [huberPenalty_def ε (ε • y)]
    simp [hwitnessNorm]
  -- Evaluate the integrand at the explicit optimizer and simplify the norm terms.
  calc
    inner ℝ (ε • y) y - huberPenalty ε (ε • y)
        = ε * inner ℝ y y - ‖ε • y‖ ^ 2 / (2 * ε) := by
            rw [real_inner_smul_left, hbranch]
    _ = ε * ‖y‖ ^ 2 - ‖ε • y‖ ^ 2 / (2 * ε) := by
          rw [real_inner_self_eq_norm_sq]
    _ = ε * ‖y‖ ^ 2 - (ε * ‖y‖) ^ 2 / (2 * ε) := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    _ = (ε / 2) * ‖y‖ ^ 2 := by
          have hεne : ε ≠ 0 := ne_of_gt hε
          field_simp [hεne]
          ring

/-- Helper for Exercise 8.8: when `1 < ‖y‖`, the affine branch along the ray
`t • NormedSpace.normalize y` eventually exceeds any prescribed threshold. -/
private lemma existsInnerSubHuberPenaltyGtOfOneLtNorm
    (ε : ℝ) (hε : 0 < ε) (y : EuclideanSpace ℝ (Fin d)) (hy : 1 < ‖y‖) :
    ∀ M : ℝ, ∃ x : EuclideanSpace ℝ (Fin d), M < inner ℝ x y - huberPenalty ε x := by
  intro M
  have hy' : 0 < ‖y‖ - 1 := sub_pos.mpr hy
  have hynz : y ≠ 0 := by
    intro hy0
    have : ¬ (1 < ‖(0 : EuclideanSpace ℝ (Fin d))‖) := by simp
    exact this (by simpa [hy0] using hy)
  let t : ℝ := max ε ((M - ε / 2) / (‖y‖ - 1)) + 1
  have htε : ε < t := by
    dsimp [t]
    nlinarith [le_max_left ε ((M - ε / 2) / (‖y‖ - 1))]
  have htbound : (M - ε / 2) / (‖y‖ - 1) < t := by
    dsimp [t]
    nlinarith [le_max_right ε ((M - ε / 2) / (‖y‖ - 1))]
  have htpos : 0 < t := lt_trans hε htε
  have hnorm : ‖t • NormedSpace.normalize y‖ = t := by
    -- The normalize witness has unit norm because `y ≠ 0`.
    rw [norm_smul, Real.norm_eq_abs, NormedSpace.norm_normalize hynz, abs_of_pos htpos,
      mul_one]
  have hbranch : huberPenalty ε (t • NormedSpace.normalize y) = t - ε / 2 := by
    -- Once the witness norm exceeds `ε`, the affine branch applies.
    rw [huberPenalty_def ε (t • NormedSpace.normalize y)]
    simp [hnorm, not_le_of_gt htε]
  have hnormalize :
      inner ℝ (NormedSpace.normalize y) y = ‖y‖ := by
    simpa [real_inner_comm] using inner_eq_norm_of_normalize y
  have hvalue :
      inner ℝ (t • NormedSpace.normalize y) y -
          huberPenalty ε (t • NormedSpace.normalize y) =
        t * (‖y‖ - 1) + ε / 2 := by
    -- The affine branch reduces the ray value to a linear function of `t`.
    calc
      inner ℝ (t • NormedSpace.normalize y) y -
          huberPenalty ε (t • NormedSpace.normalize y)
          = t * inner ℝ (NormedSpace.normalize y) y - (t - ε / 2) := by
              rw [real_inner_smul_left, hbranch]
      _ = t * ‖y‖ - (t - ε / 2) := by
            rw [hnormalize]
      _ = t * (‖y‖ - 1) + ε / 2 := by
            ring
  have hlarge : M < t * (‖y‖ - 1) + ε / 2 := by
    have hmul : M - ε / 2 < t * (‖y‖ - 1) := by
      rwa [div_lt_iff₀ hy'] at htbound
    nlinarith
  -- The chosen ray point forces the integrand above the arbitrary level `M`.
  refine ⟨t • NormedSpace.normalize y, ?_⟩
  rw [hvalue]
  exact hlarge

/-- The whole-space conjugate functional of `huberPenalty ε` is the supremum
from Exercise 8.8. -/
theorem huberPenalty_conjugateFunctional_univ_def
    (ε : ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    conjugateFunctional Set.univ (huberPenalty ε) y =
      sSup (Set.range fun x : EuclideanSpace ℝ (Fin d) ↦
        ((inner ℝ x y - huberPenalty ε x : ℝ) : EReal)) := by
  simpa using conjugateFunctional_univ_eq_sSup_range (φ := huberPenalty ε) y

/-- Exercise 8.8 (1). For `0 < ε` and `‖y‖ ≤ 1`, the whole-space conjugate
functional of `huberPenalty ε` at `y` is `(ε / 2) * ‖y‖ ^ 2`. -/
theorem huberPenalty_conjugateFunctional_eq_of_norm_le_one
    (ε : ℝ) (hε : 0 < ε) (y : EuclideanSpace ℝ (Fin d)) (hy : ‖y‖ ≤ 1) :
    conjugateFunctional Set.univ (huberPenalty ε) y =
      (((ε / 2) * ‖y‖ ^ 2 : ℝ) : EReal) := by
  rw [huberPenalty_conjugateFunctional_univ_def]
  refine le_antisymm ?_ ?_
  · -- Every point of the range is controlled by the pointwise upper bound.
    refine sSup_le fun z hz ↦ ?_
    rcases hz with ⟨x, rfl⟩
    exact EReal.coe_le_coe (innerSubHuberPenaltyLeQuadraticOfNormLeOne ε hε y hy x)
  · -- The explicit witness `ε • y` attains the claimed value.
    refine le_sSup ?_
    refine ⟨ε • y, ?_⟩
    simp [innerSubHuberPenaltyAtEpsSmul ε hε y hy]

/-- Exercise 8.8 (2). For `0 < ε` and `1 < ‖y‖`, the whole-space conjugate
functional of `huberPenalty ε` at `y` is `⊤`. -/
theorem huberPenalty_conjugateFunctional_eq_top_of_one_lt_norm
    (ε : ℝ) (hε : 0 < ε) (y : EuclideanSpace ℝ (Fin d)) (hy : 1 < ‖y‖) :
    conjugateFunctional Set.univ (huberPenalty ε) y = ⊤ := by
  rw [huberPenalty_conjugateFunctional_univ_def, EReal.eq_top_iff_forall_lt]
  intro M
  rcases existsInnerSubHuberPenaltyGtOfOneLtNorm ε hε y hy M with ⟨x, hx⟩
  -- A real witness above `M` yields an `EReal` witness below the supremum.
  refine lt_of_lt_of_le ?_ (le_sSup ⟨x, rfl⟩)
  exact EReal.coe_lt_coe hx

/-- For `0 < ε`, the conjugate set of `huberPenalty ε` on `Set.univ` is exactly
the closed unit ball. -/
theorem huberPenalty_mem_conjugateSet_iff_norm_le_one
    (ε : ℝ) (hε : 0 < ε) (y : EuclideanSpace ℝ (Fin d)) :
    y ∈ conjugateSet Set.univ (huberPenalty ε) ↔ ‖y‖ ≤ 1 := by
  rw [mem_conjugateSet_iff]
  constructor
  · -- A finite conjugate value cannot coincide with the `⊤` case.
    intro hyfin
    by_contra hy
    have hy' : 1 < ‖y‖ := lt_of_not_ge hy
    rw [huberPenalty_conjugateFunctional_eq_top_of_one_lt_norm ε hε y hy'] at hyfin
    simp at hyfin
  · -- Inside the closed unit ball, the finite-value formula is automatically below `⊤`.
    intro hy
    rw [huberPenalty_conjugateFunctional_eq_of_norm_le_one ε hε y hy]
    exact EReal.coe_lt_top ((ε / 2) * ‖y‖ ^ 2 : ℝ)

end VariationalRegularization
