/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

/- Proposition 4.10 is `source-facing`: its main content is that the scalar Fenchel objective
`x ↦ x * y - |x|^p / p` attains its maximum. The `core/canonical` owner abstraction for Chapter 4
conjugacy statements is `conjugate_function`, and the reusable scalar-facing `bridge/view` surface
in this chapter is its primal notation `f∗`. There is no additional primitive data here beyond
that source integrand; the conjugacy formula below is derived API for downstream reuse. -/
recall conjugate_function_primal
recall conjugate_function_primal_apply

-- Proof sketch: rewrite the objective as the equality case of Young's inequality for the
-- Hölder-conjugate exponents `p` and `q`. The upper bound comes from `Real.young_inequality`,
-- and equality is attained at `x = sign y * |y| ^ (q - 1)`.
/-- Helper for Proposition 4.10: Young's inequality rearranged into the scalar
Fenchel upper bound. -/
lemma powerAbsoluteObjective_le_conjugateValue {p q x y : ℝ} (hpq : p.HolderConjugate q) :
    x * y - (|x| ^ p) / p ≤ (|y| ^ q) / q := by
  -- Rearranging Young's inequality gives the uniform upper bound on the objective.
  have hYoung := Real.young_inequality x y hpq
  linarith

/-- Helper for Proposition 4.10: the sign-based extremizer has absolute value `|y| ^ (q - 1)`. -/
lemma powerAbsoluteSignExtremizerAbs {p q y : ℝ} (hpq : p.HolderConjugate q) :
    |Real.sign y * |y| ^ (q - 1)| = |y| ^ (q - 1) := by
  -- The sign contributes only an absolute value of `1`, with a separate zero case.
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg y) _)]
  by_cases hy : y = 0
  · simp [hy, hpq.symm.sub_one_ne_zero]
  · rcases Real.sign_apply_eq_of_ne_zero y hy with hsign | hsign <;> simp [hsign]

/-- Helper for Proposition 4.10: the sign extremizer attains the conjugate value. -/
lemma powerAbsoluteObjective_eq_conjugateValue_atSignExtremizer {p q y : ℝ}
    (hpq : p.HolderConjugate q) :
    Real.sign y * |y| ^ (q - 1) * y - (|Real.sign y * |y| ^ (q - 1)| ^ p) / p =
      (|y| ^ q) / q := by
  -- Route correction: evaluate the explicit sign-based extremizer directly instead of using the
  -- source derivative argument, because Young's inequality already provides the sharp bound.
  have hpow : (|y| ^ (q - 1)) ^ p = |y| ^ q := by
    rw [← Real.rpow_mul (abs_nonneg y)]
    simp [hpq.symm.sub_one_mul_conj]
  have hsign : Real.sign y * y = |y| := by
    rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [Real.sign_of_neg hy, abs_of_neg hy]
      ring
    · simp
    · rw [Real.sign_of_pos hy, abs_of_nonneg hy.le]
      ring
  have hmul : Real.sign y * |y| ^ (q - 1) * y = |y| ^ q := by
    calc
      Real.sign y * |y| ^ (q - 1) * y = |y| ^ (q - 1) * (Real.sign y * y) := by ring
      _ = |y| ^ (q - 1) * |y| := by rw [hsign]
      _ = |y| ^ ((q - 1) + 1) := by
        symm
        have hAdd : |y| ^ ((q - 1) + 1) = |y| ^ (q - 1) * |y| ^ (1 : ℝ) :=
          Real.rpow_add_of_nonneg (x := |y|) (y := q - 1) (z := 1)
            (abs_nonneg y) hpq.symm.sub_one_pos.le zero_le_one
        simpa [Real.rpow_one] using hAdd
      _ = |y| ^ q := by ring_nf
  have habs : |Real.sign y * |y| ^ (q - 1)| ^ p = |y| ^ q := by
    rw [powerAbsoluteSignExtremizerAbs hpq, hpow]
  have hcoeff : (1 - 1 / p) * |y| ^ q = (1 / q) * |y| ^ q := by
    have hInv := congrArg (fun t : ℝ ↦ t * |y| ^ q) hpq.one_sub_inv
    simpa [one_div] using hInv
  calc
    Real.sign y * |y| ^ (q - 1) * y - (|Real.sign y * |y| ^ (q - 1)| ^ p) / p
        = |y| ^ q - (|y| ^ q) / p := by rw [hmul, habs]
    _ = (1 - 1 / p) * |y| ^ q := by ring
    _ = (1 / q) * |y| ^ q := hcoeff
    _ = (|y| ^ q) / q := by ring

/-- Helper for Proposition 4.10: coercing the real attainment theorem to `EReal` preserves the
greatest element. -/
lemma powerAbsoluteObjectiveEReal_isGreatest {p q y : ℝ} (hpq : p.HolderConjugate q) :
    IsGreatest (Set.range (fun x : ℝ ↦ ((x * y - (|x| ^ p) / p : ℝ) : EReal)))
      (((|y| ^ q) / q : ℝ) : EReal) := by
  refine ⟨?_, ?_⟩
  · -- The same sign extremizer witnesses attainment after coercing to `EReal`.
    refine ⟨Real.sign y * |y| ^ (q - 1), ?_⟩
    exact congrArg (fun t : ℝ ↦ (t : EReal)) <| by
      exact powerAbsoluteObjective_eq_conjugateValue_atSignExtremizer (hpq := hpq) (y := y)
  · -- Order preservation under coercion transfers the real upper bound to the `EReal` range.
    intro z hz
    rcases hz with ⟨x, rfl⟩
    change (((x * y - (|x| ^ p) / p : ℝ) : EReal) ≤ (((|y| ^ q) / q : ℝ) : EReal))
    exact_mod_cast powerAbsoluteObjective_le_conjugateValue (hpq := hpq) (x := x) (y := y)

/-- Proposition 4.10: for the function `f(x) = |x|^p / p` with Hölder-conjugate exponent `q`,
the maximum of `x ↦ x * y - |x|^p / p` is `|y|^q / q`. Equivalently, the conjugate of
`x ↦ |x|^p / p` is `y ↦ |y|^q / q`. -/
theorem power_absolute_function_conjugate_isGreatest {p q : ℝ} (hpq : p.HolderConjugate q)
    (y : ℝ) :
    IsGreatest (Set.range fun x : ℝ ↦ x * y - (|x| ^ p) / p) ((|y| ^ q) / q) := by
  refine ⟨?_, ?_⟩
  · -- The sign extremizer realizes the equality case of Young's inequality.
    refine ⟨Real.sign y * |y| ^ (q - 1), ?_⟩
    exact powerAbsoluteObjective_eq_conjugateValue_atSignExtremizer (hpq := hpq) (y := y)
  · -- Every other value is bounded above by the same Young-inequality estimate.
    intro z hz
    rcases hz with ⟨x, rfl⟩
    exact powerAbsoluteObjective_le_conjugateValue (hpq := hpq) (x := x) (y := y)

-- Proof sketch: rewrite the primal conjugate notation through
-- `conjugate_function_primal_apply`, then identify the resulting defining `sSup` with the
-- greatest value from `power_absolute_function_conjugate_isGreatest`.
/-- Companion bridge theorem: for `f(x) = |x|^p / p`, the Chapter 4 primal Fenchel conjugate `f∗`
on `ℝ` is `y ↦ |y|^q / q`. -/
theorem power_absolute_function_conjugate_eq {p q : ℝ} (hpq : p.HolderConjugate q) (y : ℝ) :
    ((fun x : ℝ ↦ (((|x| ^ p) / p : ℝ) : EReal))∗) y =
      (((|y| ^ q) / q : ℝ) : EReal) := by
  -- Rewrite the primal conjugate into the EReal supremum of the scalar Fenchel objective.
  rw [conjugate_function_primal_apply, conjugate_function_apply]
  have hinner : ∀ x : ℝ, inner ℝ x y = x * y := fun x ↦ by
    simpa using (RCLike.inner_apply' x y : inner ℝ x y = x * y)
  have hobj :
      (fun x : ℝ ↦ ((((InnerProductSpace.toDualMap ℝ ℝ) y) x : ℝ) : EReal) -
        ((((|x| ^ p) / p : ℝ) : EReal))) =
        (fun x : ℝ ↦ ((x * y - (|x| ^ p) / p : ℝ) : EReal)) := by
    -- Normalize the dual pairing on `ℝ` to the scalar product `x * y`.
    funext x
    rw [InnerProductSpace.toDualMap_apply_apply, real_inner_comm, hinner, EReal.coe_sub]
  change sSup (Set.range (fun x : ℝ ↦ ((((InnerProductSpace.toDualMap ℝ ℝ) y) x : ℝ) : EReal) -
    ((((|x| ^ p) / p : ℝ) : EReal)))) = (((|y| ^ q) / q : ℝ) : EReal)
  rw [hobj]
  -- The EReal supremum is the greatest element supplied by the real optimization theorem.
  exact (powerAbsoluteObjectiveEReal_isGreatest (hpq := hpq) (y := y)).csSup_eq

end
