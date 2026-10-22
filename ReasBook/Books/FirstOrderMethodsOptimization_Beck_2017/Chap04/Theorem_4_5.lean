/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- Helper for Theorem 4.5: the real inner product on scalars is ordinary multiplication. -/
lemma realInnerEqMul (a b : ℝ) : inner ℝ a b = a * b := by
  change b * a = a * b
  ring

/-- Helper for Theorem 4.5: the scalar conjugate objective is the supremum of
`x ↦ x * y - exp x`. -/
lemma expConjugateObjective_eq_sSup
    (y : ℝ) :
    ((fun x : ℝ ↦ (Real.exp x : EReal))∗) y =
      sSup (Set.range fun x : ℝ ↦ (((x * y - Real.exp x : ℝ)) : EReal)) := by
  -- Rewrite the chapter owner to its defining supremum and normalize the scalar pairing.
  rw [conjugate_function_primal_apply, conjugate_function_apply]
  apply congrArg sSup
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine Set.mem_range.mpr ⟨x, ?_⟩
    simp [InnerProductSpace.toDualMap_apply_apply, realInnerEqMul, mul_comm]
  · rintro ⟨x, rfl⟩
    refine Set.mem_range.mpr ⟨x, ?_⟩
    simp [InnerProductSpace.toDualMap_apply_apply, realInnerEqMul, mul_comm]

/-- Helper for Theorem 4.5: on the positive ray, the scalar objective
`x * y - exp x` is bounded above by `y * log y - y`. -/
lemma expObjective_le_of_pos
    {x y : ℝ} (hy : 0 < y) :
    (((x * y - Real.exp x : ℝ)) : EReal) ≤ ((y * Real.log y - y : ℝ) : EReal) := by
  -- Use the supporting-line inequality `1 + t ≤ exp t` at `t = x - log y`.
  have hExp := Real.add_one_le_exp (x - Real.log y)
  have hMul :
      y * (x - Real.log y + 1) ≤ y * Real.exp (x - Real.log y) :=
    mul_le_mul_of_nonneg_left hExp (le_of_lt hy)
  have hExpEval : y * Real.exp (x - Real.log y) = Real.exp x := by
    calc
      y * Real.exp (x - Real.log y)
          = Real.exp (Real.log y) * Real.exp (x - Real.log y) := by
              rw [Real.exp_log hy]
      _ = Real.exp (Real.log y + (x - Real.log y)) := by
            rw [← Real.exp_add]
      _ = Real.exp x := by
            ring_nf
  have hReal : x * y - y * Real.log y + y ≤ Real.exp x := by
    calc
      x * y - y * Real.log y + y = y * (x - Real.log y + 1) := by
        ring
      _ ≤ y * Real.exp (x - Real.log y) := hMul
      _ = Real.exp x := hExpEval
  have hFinal : x * y - Real.exp x ≤ y * Real.log y - y := by
    linarith
  exact_mod_cast hFinal

/-- Helper for Theorem 4.5: for `y > 0`, the scalar conjugate objective attains the value
`y * log y - y` at `x = log y`. -/
lemma expConjugateObjective_eq_of_pos
    {y : ℝ} (hy : 0 < y) :
    ((fun x : ℝ ↦ (Real.exp x : EReal))∗) y = ((y * Real.log y - y : ℝ) : EReal) := by
  -- Bound the supremum above by the tangent-line estimate and then evaluate at `x = log y`.
  rw [expConjugateObjective_eq_sSup]
  refine le_antisymm ?_ ?_
  · refine sSup_le ?_
    rintro z ⟨x, rfl⟩
    exact expObjective_le_of_pos hy
  · refine le_sSup ?_
    refine Set.mem_range.mpr ⟨Real.log y, ?_⟩
    have hReal : Real.log y * y - Real.exp (Real.log y) = y * Real.log y - y := by
      rw [Real.exp_log hy]
      ring
    exact_mod_cast hReal

/-- Helper for Theorem 4.5: at `y = 0`, the scalar conjugate objective has supremum `0`. -/
lemma expConjugateObjective_eq_zero :
    ((fun x : ℝ ↦ (Real.exp x : EReal))∗) 0 = (0 : EReal) := by
  -- Every value is at most `0`, and logarithmic witnesses approach `0` from below.
  rw [expConjugateObjective_eq_sSup]
  refine sSup_eq_of_forall_le_of_forall_lt_exists_gt ?_ ?_
  · rintro a ⟨x, rfl⟩
    have hExpNonneg : 0 ≤ Real.exp x := le_of_lt (Real.exp_pos x)
    have hReal : x * 0 - Real.exp x ≤ 0 := by
      nlinarith
    change (((x * 0 - Real.exp x : ℝ)) : EReal) ≤ 0
    exact_mod_cast hReal
  · intro w hw
    obtain ⟨r, hwr, hr0⟩ := EReal.exists_between_coe_real hw
    have hrNeg : r < 0 := by
      exact_mod_cast hr0
    have hPos : 0 < (-r) / 2 := by
      linarith
    refine ⟨(((Real.log ((-r) / 2)) * 0 - Real.exp (Real.log ((-r) / 2)) : ℝ) : EReal),
      Set.mem_range.mpr ⟨Real.log ((-r) / 2), rfl⟩, ?_⟩
    have hrHalf : r < r / 2 := by
      linarith
    have hValue : (Real.log ((-r) / 2)) * 0 - Real.exp (Real.log ((-r) / 2)) = r / 2 := by
      rw [mul_zero, zero_sub, Real.exp_log hPos]
      ring
    calc
      w < (r : EReal) := hwr
      _ < ((r / 2 : ℝ) : EReal) := by
            exact_mod_cast hrHalf
      _ = (((Real.log ((-r) / 2)) * 0 - Real.exp (Real.log ((-r) / 2)) : ℝ) : EReal) := by
            exact_mod_cast hValue.symm

/-- Helper for Theorem 4.5: for `y < 0`, the scalar conjugate objective is unbounded above and
its supremum is `⊤`. -/
lemma expConjugateObjective_eq_top_of_neg
    {y : ℝ} (hy : y < 0) :
    ((fun x : ℝ ↦ (Real.exp x : EReal))∗) y = ⊤ := by
  -- Send `x` to `-∞` explicitly so that `x * y` dominates the exponentially small correction.
  rw [expConjugateObjective_eq_sSup]
  refine (sSup_eq_top).2 ?_
  intro b hb
  obtain ⟨r, hbr, _⟩ := EReal.exists_between_coe_real hb
  let x : ℝ := min (-1) ((r + 1) / y)
  refine ⟨(((x * y - Real.exp x : ℝ)) : EReal), Set.mem_range.mpr ⟨x, rfl⟩, ?_⟩
  have hy_ne : y ≠ 0 := ne_of_lt hy
  have hxyLower : r + 1 ≤ x * y := by
    have hMul : ((r + 1) / y) * y ≤ x * y :=
      mul_le_mul_of_nonpos_right (min_le_right _ _) (le_of_lt hy)
    have hDivMul : ((r + 1) / y) * y = r + 1 := by
      field_simp [hy_ne]
    simpa [hDivMul] using hMul
  have hx_lt_zero : x < 0 := by
    calc
      x ≤ -1 := min_le_left _ _
      _ < 0 := by norm_num
  have hExpLtOne : Real.exp x < 1 := Real.exp_lt_one_iff.mpr hx_lt_zero
  have hReal : r < x * y - Real.exp x := by
    have hStep : r ≤ x * y - 1 := by
      linarith
    have hImprove : x * y - 1 < x * y - Real.exp x := by
      linarith
    exact lt_of_le_of_lt hStep hImprove
  calc
    b < (r : EReal) := hbr
    _ < (((x * y - Real.exp x : ℝ)) : EReal) := by
          exact_mod_cast hReal

/- Theorem 4.5 is `source-facing`: it identifies the scalar primal-space conjugate of
`x ↦ exp x`. The `core/canonical` owner abstraction is the chapter Fenchel conjugate pair
`conjugate_function` / `conjugate_function_primal` from Definition 4.1. There is no additional
primitive data here beyond that owner specialization. -/

-- Proof sketch: for `y < 0`, send `x → -∞` to make `x * y - exp x` tend to `+∞`, so the supremum
-- is `⊤`. For `y = 0`, the supremum is `0`, approached as `x → -∞`. For `y > 0`, differentiate
-- `x ↦ x * y - exp x`, identify the unique critical point `x = log y`, and evaluate there to get
-- `y * log y - y`. Since `Real.log 0 = 0`, the same formula covers the case `y = 0`.
/-- Theorem 4.5: the primal Fenchel conjugate of `x ↦ exp x` is `y log y - y` for `y ≥ 0`, and
`⊤` for `y < 0`. The convention `0 log 0 = 0` is encoded by `Real.log 0 = 0`. -/
theorem exp_conjugate_function_eq
    (y : ℝ) :
    ((fun x : ℝ ↦ (Real.exp x : EReal))∗) y =
      if 0 ≤ y then ((y * Real.log y - y : ℝ) : EReal) else ⊤ := by
  -- Split into the sign cases from the textbook proof and reuse the branch computations above.
  by_cases hy : 0 ≤ y
  · by_cases hy0 : y = 0
    · subst hy0
      simp [expConjugateObjective_eq_zero]
    · have hyPos : 0 < y := lt_of_le_of_ne hy (by simpa [eq_comm] using hy0)
      simpa [hy] using expConjugateObjective_eq_of_pos hyPos
  · have hyNeg : y < 0 := lt_of_not_ge hy
    simpa [hy] using expConjugateObjective_eq_top_of_neg hyNeg

/-- On the nonnegative ray, the conjugate of `x ↦ exp x` is the real-valued branch
`y log y - y`. -/
theorem exp_conjugate_function_eq_of_nonneg
    {y : ℝ} (hy : 0 ≤ y) :
    ((fun x : ℝ ↦ (Real.exp x : EReal))∗) y = ((y * Real.log y - y : ℝ) : EReal) := by
  simpa [hy] using exp_conjugate_function_eq y

/-- On the negative ray, the conjugate of `x ↦ exp x` is `⊤`. -/
theorem exp_conjugate_function_eq_of_neg
    {y : ℝ} (hy : y < 0) :
    ((fun x : ℝ ↦ (Real.exp x : EReal))∗) y = ⊤ := by
  simpa [show ¬ 0 ≤ y from not_le.mpr hy] using exp_conjugate_function_eq y
