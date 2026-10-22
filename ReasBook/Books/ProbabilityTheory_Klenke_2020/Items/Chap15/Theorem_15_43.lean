/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Lemma_15_30

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

namespace RealRandomVariableArray

section

variable (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ]
variable [A.IsIndependent μ] [A.IsCentered μ] [A.IsNormed μ]

/-- Helper for Theorem 15.43: under the independent centered normed hypotheses, every row sum has
variance `1`. -/
private lemma rowSumVarianceEqOne
    (n : ℕ) :
    Var[A.rowSum n; μ] = 1 := by
  -- Proof comment: pairwise independence of the row entries lets us rewrite the row-sum variance
  -- as the sum of the entry variances, and the normed-array hypothesis normalizes that sum to `1`.
  have hPairwise : Pairwise fun i j : Fin (A.rowLength n) ↦ A n i ⟂ᵢ[μ] A n j := by
    intro i j hij
    exact (RealRandomVariableArray.IsIndependent.rowwise (A := A) (μ := μ) n).indepFun hij
  calc
    Var[A.rowSum n; μ] = ∑ i : Fin (A.rowLength n), Var[A n i; μ] := by
      simpa [RealRandomVariableArray.rowSum] using
        ProbabilityTheory.IndepFun.variance_sum
          (μ := μ) (X := fun i : Fin (A.rowLength n) ↦ A n i) (s := Finset.univ)
          (hs := fun i _ ↦ RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := μ) n i)
          (by
            intro i _ j _ hij
            exact hPairwise hij)
    _ = 1 := RealRandomVariableArray.IsNormed.variance_sum_eq_one (A := A) (μ := μ) n

/-- Helper for Theorem 15.43: after normalizing `Var[A.rowSum n; μ] = 1`, the owner Lindeberg
quantity is exactly the textbook truncated second-moment sum. -/
private lemma lindebergFunction_eq_rowTruncatedSecondMoment
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    A.lindebergFunction μ ε n =
      ∑ i : Fin (A.rowLength n),
        ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
  -- Proof comment: replace the normalization variance by `1`, then rewrite the truncation event
  -- `ε^2 < Xₙ,ᵢ^2` as the absolute-value tail event `ε < |Xₙ,ᵢ|`.
  rw [RealRandomVariableArray.lindebergFunction_def]
  rw [rowSumVarianceEqOne (A := A) (μ := μ) n, inv_one, one_mul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hs :
      {ω | ε ^ 2 * (1 : ℝ) < (A n i ω) ^ 2} = {ω | ε < |A n i ω|} := by
    ext ω
    simp [sq_lt_sq, abs_of_pos hε]
  rw [hs]

-- Proof sketch: under the independent, centered, and normed hypotheses, the normalization in
-- `Definition_15_40` is the textbook normalization from Theorem 15.43, so the canonical
-- Lindeberg condition is equivalent to the vanishing of the rowwise truncated second moments for
-- every fixed threshold `ε > 0`.
/-- Under the independent, centered, and normed hypotheses of Theorem 15.43, the canonical
Lindeberg condition from Definition 15.40 is equivalent to the vanishing of the rowwise truncated
second moments for every fixed threshold `ε > 0`. -/
theorem satisfiesLindebergCondition_iff
    :
    A.SatisfiesLindebergCondition μ ↔
      ∀ ⦃ε : ℝ⦄, 0 < ε →
        Tendsto
          (fun n ↦
            ∑ i : Fin (A.rowLength n),
              ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ)
          atTop (𝓝 0) := by
  constructor
  · intro hLindeberg ε hε
    -- Proof comment: rewrite the owner Lindeberg quantity into the textbook truncated
    -- second-moment expression row by row, then use the defining convergence field.
    simpa [lindebergFunction_eq_rowTruncatedSecondMoment (A := A) (μ := μ) hε] using
      hLindeberg.lindeberg_tendsto hε
  · intro hTrunc
    -- Proof comment: the converse direction packages the same rowwise rewrite into the owner
    -- `SatisfiesLindebergCondition` structure.
    refine
      { toIsCentered := inferInstance
        memLp_two := RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := μ)
        lindeberg_tendsto := ?_ }
    intro ε hε
    simpa [lindebergFunction_eq_rowTruncatedSecondMoment (A := A) (μ := μ) hε] using hTrunc hε

/-- Helper for Theorem 15.43: each tail probability in a fixed row is controlled by the matching
truncated second moment via the elementary bound `1 ≤ ε⁻¹^2 * x^2` on the tail event
`{ω | ε < |A n i ω|}`. -/
private lemma tailProbLeScaledTruncatedSecondMoment
    {ε : ℝ} (hε : 0 < ε) (n : ℕ) (i : Fin (A.rowLength n)) :
    μ {ω | ε < |A n i ω|} ≤
      ENNReal.ofReal
        (ε⁻¹ ^ (2 : ℕ) *
          ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ) := by
  let s : Set Ω := {ω | ε < |A n i ω|}
  have hs : MeasurableSet s := by
    -- Proof comment: the tail event is measurable because each array entry is measurable.
    exact measurableSet_lt measurable_const (measurable_abs.comp (A.measurable_entry n i))
  have hsqInt : Integrable (fun ω ↦ (A n i ω) ^ (2 : ℕ)) μ := by
    simpa using
      (RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := μ) n i).integrable_sq
  have hLeftInt : Integrable (Set.indicator s (fun _ : Ω ↦ (1 : ℝ))) μ := by
    exact (integrable_const (1 : ℝ)).indicator hs
  have hRightInt :
      Integrable (Set.indicator s (fun ω ↦ ε⁻¹ ^ (2 : ℕ) * (A n i ω) ^ (2 : ℕ))) μ := by
    exact (hsqInt.const_mul (ε⁻¹ ^ (2 : ℕ))).indicator hs
  have hPointwise :
      ∀ᵐ ω ∂μ,
        Set.indicator s (fun _ : Ω ↦ (1 : ℝ)) ω ≤
          Set.indicator s (fun ω ↦ ε⁻¹ ^ (2 : ℕ) * (A n i ω) ^ (2 : ℕ)) ω := by
    refine Filter.Eventually.of_forall fun ω ↦ ?_
    by_cases hω : ω ∈ s
    · have hTail : ε < |A n i ω| := hω
      have hsq_abs : ε ^ (2 : ℕ) < |A n i ω| ^ (2 : ℕ) := by
        nlinarith [hε, abs_nonneg (A n i ω), hTail]
      have hsq : ε ^ (2 : ℕ) < (A n i ω) ^ (2 : ℕ) := by
        simpa [sq_abs] using hsq_abs
      have hone : (1 : ℝ) ≤ (ε ^ (2 : ℕ))⁻¹ * (A n i ω) ^ (2 : ℕ) := by
        have hεsq : 0 < ε ^ (2 : ℕ) := by positivity
        have hdiv : (1 : ℝ) < (A n i ω) ^ (2 : ℕ) / (ε ^ (2 : ℕ)) := by
          exact (one_lt_div hεsq).2 hsq
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv.le
      simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (show Set.indicator s (fun _ : Ω ↦ (1 : ℝ)) ω ≤
            Set.indicator s (fun ω ↦ ε⁻¹ ^ (2 : ℕ) * (A n i ω) ^ (2 : ℕ)) ω by
          simp [s, hω, hone])
    · simp [s, hω]
  have hMono :
      ∫ ω, Set.indicator s (fun _ : Ω ↦ (1 : ℝ)) ω ∂μ ≤
        ∫ ω, Set.indicator s (fun ω ↦ ε⁻¹ ^ (2 : ℕ) * (A n i ω) ^ (2 : ℕ)) ω ∂μ := by
    exact integral_mono_ae hLeftInt hRightInt hPointwise
  have hRightEq :
      ∫ ω, Set.indicator s (fun ω ↦ ε⁻¹ ^ (2 : ℕ) * (A n i ω) ^ (2 : ℕ)) ω ∂μ =
        ε⁻¹ ^ (2 : ℕ) *
          ∫ ω, Set.indicator s (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω ∂μ := by
    have hRewrite :
        Set.indicator s (fun ω ↦ ε⁻¹ ^ (2 : ℕ) * (A n i ω) ^ (2 : ℕ)) =
          fun ω ↦ ε⁻¹ ^ (2 : ℕ) * Set.indicator s (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω := by
      funext ω
      by_cases hω : ω ∈ s <;> simp [hω]
    rw [hRewrite, integral_const_mul]
  have hTruncNonneg :
      0 ≤ ∫ ω, Set.indicator s (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω ∂μ := by
    exact integral_nonneg fun ω ↦ by
      by_cases hω : ω ∈ s <;> simp [hω, sq_nonneg]
  have hScaledNonneg :
      0 ≤ ε⁻¹ ^ (2 : ℕ) *
        ∫ ω, Set.indicator s (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω ∂μ := by
    positivity
  have hToReal :
      μ.real s ≤
        ε⁻¹ ^ (2 : ℕ) *
          ∫ ω, Set.indicator s (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω ∂μ := by
    calc
      μ.real s = ∫ ω, Set.indicator s (fun _ : Ω ↦ (1 : ℝ)) ω ∂μ := by
        symm
        simpa using (MeasureTheory.integral_indicator_one (μ := μ) (s := s) hs)
      _ ≤ ∫ ω, Set.indicator s (fun ω ↦ ε⁻¹ ^ (2 : ℕ) * (A n i ω) ^ (2 : ℕ)) ω ∂μ := hMono
      _ = ε⁻¹ ^ (2 : ℕ) *
            ∫ ω, Set.indicator s (fun ω ↦ (A n i ω) ^ (2 : ℕ)) ω ∂μ := hRightEq
  refine ENNReal.le_ofReal_iff_toReal_le (measure_ne_top μ s) hScaledNonneg |>.2 ?_
  simpa [s] using hToReal

/-- Helper for Theorem 15.43: the truncated-second-moment formulation of the Lindeberg condition
forces the null-array tails to vanish rowwise. -/
private lemma isNull_of_satisfiesLindebergCondition
    (hLindeberg : A.SatisfiesLindebergCondition μ) :
    A.IsNull μ := by
  refine
    { toIsCentered := inferInstance
      asymptotically_negligible := ?_ }
  intro ε hε
  let c : ℝ := ε⁻¹ ^ (2 : ℕ)
  have hTrunc :=
    (satisfiesLindebergCondition_iff (A := A) (μ := μ)).1 hLindeberg hε
  have hBound :
      ∀ n, (⨆ i : Fin (A.rowLength n), μ {ω | ε < |A n i ω|}) ≤
        ENNReal.ofReal
          (c *
            ∑ i : Fin (A.rowLength n),
              ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ) := by
    intro n
    refine iSup_le fun i ↦ ?_
    have hTail :=
      tailProbLeScaledTruncatedSecondMoment (A := A) (μ := μ) hε n i
    have hNonnegTerm :
        ∀ j : Fin (A.rowLength n), 0 ≤
          ∫ ω, Set.indicator {ω | ε < |A n j ω|} (fun ω ↦ (A n j ω) ^ 2) ω ∂μ := by
      intro j
      exact integral_nonneg fun ω ↦ by
        by_cases hω : ε < |A n j ω| <;> simp [hω, sq_nonneg]
    have hTermLe :
        ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ ≤
          ∑ j : Fin (A.rowLength n),
            ∫ ω, Set.indicator {ω | ε < |A n j ω|} (fun ω ↦ (A n j ω) ^ 2) ω ∂μ := by
      exact Finset.single_le_sum (fun j _ ↦ hNonnegTerm j) (Finset.mem_univ i)
    have hScaledLe :
        c *
            ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ ≤
          c *
            ∑ j : Fin (A.rowLength n),
              ∫ ω, Set.indicator {ω | ε < |A n j ω|} (fun ω ↦ (A n j ω) ^ 2) ω ∂μ := by
      have hc_nonneg : 0 ≤ c := by
        dsimp [c]
        positivity
      gcongr
    exact hTail.trans (ENNReal.ofReal_le_ofReal hScaledLe)
  have hUpperReal :
      Tendsto
        (fun n ↦
          c *
            ∑ i : Fin (A.rowLength n),
              ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ)
        atTop (𝓝 0) := by
    simpa [c] using (tendsto_const_nhds.mul hTrunc)
  have hUpper :
      Tendsto
        (fun n ↦
          ENNReal.ofReal
            (c *
              ∑ i : Fin (A.rowLength n),
                ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ))
        atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hUpperReal
  exact
    tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hUpper
      (fun n ↦ bot_le)
      hBound

/-- Helper for Theorem 15.43: the characteristic function of a row sum factors into the product of
the entry characteristic functions in that row. -/
private lemma rowSumLaw_charFun_eq_prod_entryCharFun
    (n : ℕ) (t : ℝ) :
    charFun (A.rowSumLaw μ n : Measure ℝ) t =
      ∏ i : Fin (A.rowLength n), charFun (μ.map (A n i)) t := by
  -- Proof comment: rewrite the row-sum law as the pushforward of the actual row sum, then apply
  -- the finite-family characteristic-function factorization from rowwise independence.
  rw [A.rowSumLaw_toMeasure μ n]
  have hrow : A.rowSum n = fun ω ↦ ∑ i : Fin (A.rowLength n), A n i ω := by
    funext ω
    simp [RealRandomVariableArray.rowSum, Finset.sum_apply]
  rw [hrow]
  simpa using congrFun
    ((RealRandomVariableArray.IsIndependent.rowwise (A := A) (μ := μ) n).charFun_map_fun_sum_eq_prod
      (fun i ↦ (A.measurable_entry n i).aemeasurable)) t

/-- Helper for Theorem 15.43: weak convergence of the row-sum laws to `𝒩(0,1)` yields the
expected pointwise characteristic-function limit. -/
private lemma rowSumLaw_charFun_tendsto_gaussian
    (hGaussian :
      Tendsto (A.rowSumLaw μ) atTop
        (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))))
    (t : ℝ) :
    Tendsto
      (fun n ↦ charFun (A.rowSumLaw μ n : Measure ℝ) t)
      atTop
      (𝓝 (Complex.exp (-(t ^ 2 / 2 : ℝ)))) := by
  -- Proof comment: this is the direct characteristic-function consequence of weak convergence.
  simpa [ProbabilityTheory.charFun_gaussianReal, neg_div] using
    (ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hGaussian t)

/-- Helper for Theorem 15.43: the centered quadratic kernel whose weighted-row-law integrals are
exactly the middle terms `φₙ,ᵢ(t) - 1`. -/
private def centeredQuadraticCharFunKernel (t : ℝ) : ℝ → ℂ :=
  fun x ↦
    if x = 0 then
      (-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)
    else
      (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)) /
        (((x : ℂ) ^ (2 : ℕ)))

/-- Helper for Theorem 15.43: the centered quadratic kernel takes the Gaussian exponent value
`-t^2 / 2` at `0`. -/
private lemma centeredQuadraticCharFunKernel_apply_zero (t : ℝ) :
    centeredQuadraticCharFunKernel t 0 = (-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
  -- Proof comment: this is the zero branch of the defining `if`.
  simp [centeredQuadraticCharFunKernel]

/-- Helper for Theorem 15.43: away from `0`, the centered quadratic kernel is the explicit
quadratic remainder `(exp(itx) - 1 - itx) / x^2`. -/
private lemma centeredQuadraticCharFunKernel_apply_ne_zero
    (t x : ℝ) (hx : x ≠ 0) :
    centeredQuadraticCharFunKernel t x =
      (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)) /
        (((x : ℂ) ^ (2 : ℕ))) := by
  -- Proof comment: away from the origin, the defining `if` collapses to the explicit formula.
  simp [centeredQuadraticCharFunKernel, hx]

/-- Helper for Theorem 15.43: multiplying the centered quadratic kernel by `x^2` recovers the
centered exponential increment exactly. -/
private lemma centeredQuadraticCharFunKernel_mul_sq
    (t x : ℝ) :
    centeredQuadraticCharFunKernel t x * (((x : ℂ) ^ (2 : ℕ))) =
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ) := by
  by_cases hx : x = 0
  · -- Proof comment: at the origin both sides vanish because the quadratic factor kills the
    -- continuous extension value and the centered increment is zero.
    simp [centeredQuadraticCharFunKernel, hx]
  · -- Proof comment: away from `0`, the explicit denominator cancels against `x^2`.
    have hxC : ((x : ℂ)) ≠ 0 := by
      exact_mod_cast hx
    rw [centeredQuadraticCharFunKernel_apply_ne_zero (t := t) (x := x) hx]
    field_simp [pow_ne_zero 2 hxC]

/-- Helper for Theorem 15.43: the third-order Taylor remainder of
`Complex.exp ((((t * x : ℝ) : ℂ) * Complex.I))`. -/
private def centeredQuadraticCharFunKernelTaylorRemainder (t x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) -
    Finset.sum (Finset.range 3)
      (fun m ↦ ((((t * x : ℝ) : ℂ) * Complex.I) ^ m) / m.factorial)

/-- Helper for Theorem 15.43: the cubic Taylor polynomial of `exp ((((t * x : ℝ) : ℂ) * I))`
has the canonical textbook normal form `1 + i t x - t² x² / 2`. -/
private lemma centeredQuadraticCharFunKernelTaylorPolynomial_eval
    (t x : ℝ) :
    Finset.sum (Finset.range 3)
      (fun m ↦ ((((t * x : ℝ) : ℂ) * Complex.I) ^ m) / m.factorial) =
        1 + (((t * x : ℝ) : ℂ) * Complex.I) - ((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
  -- Proof comment: expand the three Taylor terms `m = 0, 1, 2` once and freeze that normal form
  -- so the later quotient rewrite does not keep rediscovering it by ad hoc simplification.
  have hI : Complex.I * Complex.I = -(1 : ℂ) := by
    calc
      Complex.I * Complex.I = Complex.I ^ (2 : ℕ) := by simp [pow_two]
      _ = -(1 : ℂ) := Complex.I_sq
  have hI2 (z : ℂ) : Complex.I * (Complex.I * z) = -z := by
    calc
      Complex.I * (Complex.I * z) = (Complex.I * Complex.I) * z := by ring
      _ = -(1 : ℂ) * z := by rw [hI]
      _ = -z := by ring
  simp [Finset.sum_range_succ, pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm,
    mul_comm, sub_eq_add_neg]
  rw [hI2]

/-- Helper for Theorem 15.43: away from `0`, subtracting the origin value rewrites the centered
quadratic kernel as the third-order Taylor remainder divided by `x^2`. -/
private lemma centeredQuadraticCharFunKernel_sub_apply_zero_eq_taylorRemainderDiv
    (t x : ℝ) (hx : x ≠ 0) :
    centeredQuadraticCharFunKernel t x - centeredQuadraticCharFunKernel t 0 =
      centeredQuadraticCharFunKernelTaylorRemainder t x /
        (((x : ℂ) ^ (2 : ℕ))) := by
  have hxC : ((x : ℂ) ^ (2 : ℕ)) ≠ 0 := by
    exact pow_ne_zero 2 (by exact_mod_cast hx)
  have hTaylor :
      Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ) +
          (((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ)) =
        centeredQuadraticCharFunKernelTaylorRemainder t x := by
    -- Proof comment: rewrite the truncated Taylor sum into the fixed polynomial normal form and
    -- then collect terms in the numerator.
    rw [centeredQuadraticCharFunKernelTaylorRemainder,
      centeredQuadraticCharFunKernelTaylorPolynomial_eval (t := t) (x := x)]
    ring
  calc
    centeredQuadraticCharFunKernel t x - centeredQuadraticCharFunKernel t 0 =
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)) /
            (((x : ℂ) ^ (2 : ℕ))) +
          ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ) := by
            rw [centeredQuadraticCharFunKernel_apply_ne_zero (t := t) (x := x) hx,
              centeredQuadraticCharFunKernel_apply_zero]
            ring
    _ =
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ) +
            ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ) * (((x : ℂ) ^ (2 : ℕ)))) /
          (((x : ℂ) ^ (2 : ℕ))) := by
            let a : ℂ :=
              Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)
            let b : ℂ := ((x : ℂ) ^ (2 : ℕ))
            let c : ℂ := ((t ^ (2 : ℕ) / 2 : ℝ) : ℂ)
            change a / b + c = (a + c * b) / b
            rw [div_eq_mul_inv, div_eq_mul_inv, add_mul]
            congr 1
            calc
              c = c * (b * b⁻¹) := by simp [b, hxC]
              _ = c * b * b⁻¹ := by ring
    _ =
        (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ) +
            (((t ^ (2 : ℕ) * x ^ (2 : ℕ) / 2 : ℝ) : ℂ))) /
          (((x : ℂ) ^ (2 : ℕ))) := by
            simp [div_eq_mul_inv, pow_two, sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm]
    _ = centeredQuadraticCharFunKernelTaylorRemainder t x /
          (((x : ℂ) ^ (2 : ℕ))) := by
            rw [hTaylor]

/-- Helper for Theorem 15.43: near `0`, the centered quadratic kernel differs from its value at
`0` by at most a linear multiple of `|x|`. -/
private lemma norm_centeredQuadraticCharFunKernel_sub_apply_zero_le
    (t x : ℝ) (hx : x ≠ 0) :
    ‖centeredQuadraticCharFunKernel t x - centeredQuadraticCharFunKernel t 0‖ ≤
      |t| ^ (3 : ℕ) * |x| / 6 := by
  have hxC : ((x : ℂ) ^ (2 : ℕ)) ≠ 0 := by
    exact pow_ne_zero 2 (by exact_mod_cast hx)
  have hxabs : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hRemainder :
      ‖centeredQuadraticCharFunKernelTaylorRemainder t x‖ ≤ |t * x| ^ (3 : ℕ) / 6 := by
    -- Proof comment: the owner Taylor-remainder lemma is exactly the cubic bound needed after
    -- the quotient normalization at the origin.
    simpa [centeredQuadraticCharFunKernelTaylorRemainder, mul_assoc] using
      norm_exp_mul_I_sub_taylor_sum_le (t := t * x) (n := 3)
  calc
    ‖centeredQuadraticCharFunKernel t x - centeredQuadraticCharFunKernel t 0‖ =
        ‖centeredQuadraticCharFunKernelTaylorRemainder t x / (((x : ℂ) ^ (2 : ℕ)))‖ := by
          rw [centeredQuadraticCharFunKernel_sub_apply_zero_eq_taylorRemainderDiv
            (t := t) (x := x) hx]
    _ = ‖centeredQuadraticCharFunKernelTaylorRemainder t x‖ / ‖((x : ℂ) ^ (2 : ℕ))‖ := by
          rw [norm_div]
    _ ≤ (|t * x| ^ (3 : ℕ) / 6) / |x| ^ (2 : ℕ) := by
          have hNormDen : ‖((x : ℂ) ^ (2 : ℕ))‖ = |x| ^ (2 : ℕ) := by
            simp [Complex.norm_real, Real.norm_eq_abs]
          rw [hNormDen]
          gcongr
    _ = (|t| ^ (3 : ℕ) * |x| ^ (3 : ℕ) / 6) / |x| ^ (2 : ℕ) := by
          rw [abs_mul, mul_pow]
    _ = |t| ^ (3 : ℕ) * |x| / 6 := by
          field_simp [hxabs]

/-- Helper for Theorem 15.43: the centered quadratic kernel is continuous on `ℝ`. -/
private lemma continuous_centeredQuadraticCharFunKernel
    (t : ℝ) :
    Continuous (centeredQuadraticCharFunKernel t) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  by_cases hx : x = 0
  · -- Proof comment: the Taylor remainder estimate makes the quadratic kernel converge to its
    -- prescribed continuous extension at the origin.
    subst hx
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    by_cases ht : t = 0
    · refine Filter.Eventually.of_forall fun y ↦ ?_
      simpa [centeredQuadraticCharFunKernel, ht, dist_eq_norm] using hε
    · have ht3pos : 0 < |t| ^ (3 : ℕ) / 6 := by
        have htnorm : 0 < |t| := abs_pos.mpr ht
        positivity
      have hδpos : 0 < ε / (|t| ^ (3 : ℕ) / 6) := by positivity
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with y hy
      by_cases hy0 : y = 0
      · simpa [hy0, dist_eq_norm] using hε
      · have hbound :=
          norm_centeredQuadraticCharFunKernel_sub_apply_zero_le (t := t) (x := y) hy0
        have hyabs : |y| < ε / (|t| ^ (3 : ℕ) / 6) := by
          simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using hy
        calc
          dist (centeredQuadraticCharFunKernel t y) (centeredQuadraticCharFunKernel t 0) =
              ‖centeredQuadraticCharFunKernel t y - centeredQuadraticCharFunKernel t 0‖ := by
                simp [dist_eq_norm]
          _ ≤ |t| ^ (3 : ℕ) * |y| / 6 := hbound
          _ < |t| ^ (3 : ℕ) * (ε / (|t| ^ (3 : ℕ) / 6)) / 6 := by
                gcongr
          _ = ε := by
                field_simp [ht3pos.ne']
  · -- Proof comment: away from the origin, the kernel is the quotient of continuous functions
    -- with a nonvanishing denominator.
    have hdenom_ne : (((x : ℂ) ^ (2 : ℕ))) ≠ 0 := by
      exact pow_ne_zero 2 (by exact_mod_cast hx)
    have hEventually :
        centeredQuadraticCharFunKernel t =ᶠ[𝓝 x]
          fun y : ℝ ↦
            (Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * y : ℝ)) /
              (((y : ℂ) ^ (2 : ℕ))) := by
      filter_upwards [Metric.ball_mem_nhds x (half_pos (abs_pos.mpr hx))] with y hy
      have hy0 : y ≠ 0 := by
        have hdist : |y - x| < |x| / 2 := by
          simpa [Metric.mem_ball, Real.dist_eq] using hy
        intro hy0
        subst hy0
        have hxlt : |x| < |x| / 2 := by simpa [abs_sub_comm] using hdist
        linarith [abs_nonneg x]
      simp [centeredQuadraticCharFunKernel, hy0]
    have hnum :
        Continuous fun y : ℝ ↦
          Complex.exp (((t * y : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * y : ℝ) := by
      fun_prop
    have hden : Continuous fun y : ℝ ↦ ((y : ℂ) ^ (2 : ℕ)) := by
      fun_prop
    exact (hnum.continuousAt.div hden.continuousAt hdenom_ne).congr hEventually.symm

/-- Helper for Theorem 15.43: the range of the centered quadratic kernel is bounded. -/
private lemma isBounded_range_centeredQuadraticCharFunKernel
    (t : ℝ) :
    Bornology.IsBounded (Set.range (centeredQuadraticCharFunKernel t)) := by
  -- Proof comment: continuity bounds the kernel on the compact core `[-1,1]`, while outside that
  -- core the explicit denominator gives a uniform `O(1)` bound.
  obtain ⟨Ccore, hcore⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (f := centeredQuadraticCharFunKernel t)
      (continuous_centeredQuadraticCharFunKernel (t := t)).continuousOn
  refine (isBounded_iff_forall_norm_le).2 ?_
  refine ⟨max Ccore (2 + |t|), ?_⟩
  intro z hz
  rcases hz with ⟨x, rfl⟩
  by_cases hx : |x| ≤ 1
  · have hx_mem : x ∈ Set.Icc (-1 : ℝ) 1 := by
      simpa [abs_le] using hx
    exact (hcore x hx_mem).trans (le_max_left _ _)
  · have hx1 : 1 ≤ |x| := by linarith
    by_cases hx0 : x = 0
    · exfalso
      have hnot : ¬ (1 ≤ (0 : ℝ)) := by norm_num
      exact hnot (by simpa [hx0] using hx1)
    · rw [centeredQuadraticCharFunKernel_apply_ne_zero (t := t) (x := x) hx0]
      have hexp : ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤ 2 := by
        calc
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ ≤
              ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ + ‖(1 : ℂ)‖ := by
                simpa using norm_sub_le (Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)) (1 : ℂ)
          _ = 2 := by
                rw [show ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)‖ = 1 by
                  simpa [mul_assoc] using Complex.norm_exp_ofReal_mul_I (t * x)]
                norm_num
      have hlin : ‖Complex.I * (t * x : ℝ)‖ ≤ |t| * |x| := by
        simp [norm_mul, Complex.norm_I, Real.norm_eq_abs, abs_mul]
      have hxnorm : ‖((x : ℂ) ^ (2 : ℕ))‖ = |x| ^ (2 : ℕ) := by
        simp [Complex.norm_real, Real.norm_eq_abs]
      have hxabs0 : |x| ≠ 0 := abs_ne_zero.mpr hx0
      have hnum2 :
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)‖ ≤
            2 + |t| * |x| := by
        calc
          ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)‖ ≤
              ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1‖ + ‖Complex.I * (t * x : ℝ)‖ := by
                exact norm_sub_le _ _
          _ ≤ 2 + |t| * |x| := by nlinarith
      calc
        ‖(Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)) /
            (((x : ℂ) ^ (2 : ℕ)))‖
            = ‖Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (t * x : ℝ)‖ /
                ‖((x : ℂ) ^ (2 : ℕ))‖ := by
                  rw [norm_div]
        _ ≤ (2 + |t| * |x|) / (|x| ^ (2 : ℕ)) := by
              rw [hxnorm]
              gcongr
        _ = 2 / (|x| ^ (2 : ℕ)) + |t| / |x| := by
              field_simp [hxabs0]
        _ ≤ 2 + |t| := by
              have hx_sq : 1 ≤ |x| ^ (2 : ℕ) := by nlinarith
              have htwo : 2 / (|x| ^ (2 : ℕ)) ≤ 2 := by
                have hpos : 0 < |x| ^ (2 : ℕ) := by positivity
                rw [div_le_iff₀ hpos]
                nlinarith
              have hdivt : |t| / |x| ≤ |t| := by
                have hpos1 : (0 : ℝ) < 1 := by positivity
                have hInv : 1 / |x| ≤ 1 := by
                  simpa using (one_div_le_one_div_of_le hpos1 hx1)
                calc
                  |t| / |x| = |t| * (1 / |x|) := by ring
                  _ ≤ |t| * 1 := by
                        gcongr
                  _ = |t| := by ring
              linarith
        _ ≤ max Ccore (2 + |t|) := le_max_right _ _

/-- Helper for Theorem 15.43: the centered quadratic kernel is canonically a bounded continuous
test function on `ℝ`. -/
private def centeredQuadraticCharFunKernelBCF (t : ℝ) : BoundedContinuousFunction ℝ ℂ :=
  { toContinuousMap := ⟨centeredQuadraticCharFunKernel t,
      continuous_centeredQuadraticCharFunKernel (t := t)⟩
    map_bounded' := Metric.isBounded_range_iff.1
      (isBounded_range_centeredQuadraticCharFunKernel (t := t)) }

/-- Helper for Theorem 15.43: coercing the bundled centered quadratic kernel recovers the explicit
function. -/
@[simp] private lemma coe_centeredQuadraticCharFunKernelBCF (t : ℝ) :
    (centeredQuadraticCharFunKernelBCF t : ℝ → ℂ) = centeredQuadraticCharFunKernel t := rfl

/-- Helper for Theorem 15.43: the canonical owner measure on `ℝ` that records the `n`-th row by
weighting each entry law with the quadratic density `x ↦ x^2`. -/
private def varianceWeightedRowMeasure
    (n : ℕ) :
    Measure ℝ :=
  ∑ i : Fin (A.rowLength n),
    (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)

/-- Helper for Theorem 15.43: the threshold `-1` sees the whole real line because absolute values
are always nonnegative. -/
private lemma negOne_lt_abs_univ : {x : ℝ | (-1 : ℝ) < |x|} = Set.univ := by
  -- Proof comment: `|x|` is always at least `0`, so the inequality `-1 < |x|` is automatic.
  refine Set.eq_univ_of_forall ?_
  intro x
  have hneg : (-1 : ℝ) < 0 := by norm_num
  exact lt_of_lt_of_le hneg (abs_nonneg x)

/-- Helper for Theorem 15.43: the owner measure tail outside `(-ε, ε)` is exactly the textbook
truncated second-moment sum in row `n`. -/
private lemma varianceWeightedRowMeasure_tail_eq
    (ε : ℝ) (n : ℕ) :
    (A.varianceWeightedRowMeasure μ n).real {x | ε < |x|} =
      ∑ i : Fin (A.rowLength n),
        ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
  classical
  let s : Set ℝ := {x | ε < |x|}
  have hs : MeasurableSet s := by
    -- Proof comment: the tail set is measurable because `x ↦ |x|` is measurable.
    exact measurableSet_lt measurable_const measurable_abs
  -- Proof comment: expand the finite owner measure sum and rewrite each summand on the tail set
  -- back to the corresponding truncated second moment.
  rw [varianceWeightedRowMeasure, Measure.real_def]
  have hsum :
      ((∑ i : Fin (A.rowLength n),
          (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal =
        ∑ i : Fin (A.rowLength n),
          (((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal := by
    calc
      ((∑ i : Fin (A.rowLength n),
          (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal =
          (∑ i : Fin (A.rowLength n),
            ((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal := by
            simpa using
              congrArg ENNReal.toReal
                (Measure.sum_apply
                  (f := fun i : Fin (A.rowLength n) ↦
                    (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i))
                  hs)
      _ = ∑ i : Fin (A.rowLength n),
            (((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal := by
            rw [ENNReal.toReal_sum]
            intro i hi
            have hSqInt : HasFiniteIntegral (fun ω ↦ (A n i ω) ^ 2) μ := by
              have hIntegrableSq : Integrable (fun ω ↦ (A n i ω) ^ 2) μ := by
                simpa using
                  (RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := μ) n i).integrable_sq
              exact hIntegrableSq.hasFiniteIntegral
            letI :
                IsFiniteMeasure (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)) :=
              MeasureTheory.isFiniteMeasure_withDensity_ofReal hSqInt
            exact measure_ne_top _ _
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hs_pre : MeasurableSet ((A n i) ⁻¹' s) := (A.measurable_entry n i) hs
  have hDensity_meas :
      AEMeasurable (fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)) (μ.restrict ((A n i) ⁻¹' s)) := by
    exact (((A.measurable_entry n i).pow_const 2).ennreal_ofReal.aemeasurable).restrict
  have hDensity_lt_top :
      ∀ᵐ ω ∂(μ.restrict ((A n i) ⁻¹' s)), ENNReal.ofReal ((A n i ω) ^ 2) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ by simp
  calc
    ((((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) s).toReal) =
        (∫⁻ ω in (A n i) ⁻¹' s, ENNReal.ofReal ((A n i ω) ^ 2) ∂μ).toReal := by
          rw [Measure.map_apply (A.measurable_entry n i) hs, withDensity_apply _ hs_pre]
    _ = ∫ ω in (A n i) ⁻¹' s, (A n i ω) ^ 2 ∂μ := by
          -- Proof comment: the density is finite everywhere, so `integral_toReal` converts the
          -- lower integral on the restricted measure into the corresponding set integral.
          simpa [ENNReal.toReal_ofReal, sq_nonneg] using
            (MeasureTheory.integral_toReal (μ := μ.restrict ((A n i) ⁻¹' s))
              hDensity_meas hDensity_lt_top).symm
    _ = ∫ ω, Set.indicator ((A n i) ⁻¹' s) (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
          rw [MeasureTheory.integral_indicator hs_pre]
    _ = ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
          simp [s]

/-- Helper for Theorem 15.43: the canonical owner measure has total mass `1`, so it can be viewed
as a probability law. -/
private lemma varianceWeightedRowMeasure_real_univ
    (n : ℕ) :
    (A.varianceWeightedRowMeasure μ n).real Set.univ = 1 := by
  have hTail :=
    varianceWeightedRowMeasure_tail_eq (A := A) (μ := μ) (-1) n
  rw [negOne_lt_abs_univ] at hTail
  -- Proof comment: at threshold `-1`, the tail set is all of `ℝ`, so the owner measure mass is
  -- the sum of the entry second moments; centeredness then identifies these with the entry
  -- variances, and the normed-array hypothesis normalizes the row sum to `1`.
  calc
    (A.varianceWeightedRowMeasure μ n).real Set.univ =
        ∑ i : Fin (A.rowLength n),
          ∫ ω, Set.indicator {ω | (-1 : ℝ) < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
          simpa [negOne_lt_abs_univ] using hTail
    _ =
        ∑ i : Fin (A.rowLength n), ∫ ω, (A n i ω) ^ 2 ∂μ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hAll : {ω : Ω | (-1 : ℝ) < |A n i ω|} = Set.univ := by
            refine Set.eq_univ_of_forall fun ω ↦ ?_
            have hneg : (-1 : ℝ) < 0 := by norm_num
            exact lt_of_lt_of_le hneg (abs_nonneg (A n i ω))
          simp [hAll]
    _ = ∑ i : Fin (A.rowLength n), Var[A n i; μ] := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          exact
            (ProbabilityTheory.variance_of_integral_eq_zero
              (A.measurable_entry n i).aemeasurable
              (RealRandomVariableArray.IsCentered.expectation_eq_zero
                (A := A) (μ := μ) n i)).symm
    _ = 1 := RealRandomVariableArray.IsNormed.variance_sum_eq_one (A := A) (μ := μ) n

/-- Helper for Theorem 15.43: each owner measure can be packaged as a probability measure because
its total mass is `1`. -/
private lemma varianceWeightedRowMeasure_isProbabilityMeasure
    (n : ℕ) :
    IsProbabilityMeasure (A.varianceWeightedRowMeasure μ n) := by
  rw [MeasureTheory.isProbabilityMeasure_iff_real]
  exact varianceWeightedRowMeasure_real_univ (A := A) (μ := μ) n

/-- Helper for Theorem 15.43: the canonical owner probability law attached to row `n`. -/
private def varianceWeightedRowLaw
    (n : ℕ) :
    ProbabilityMeasure ℝ :=
  ⟨A.varianceWeightedRowMeasure μ n,
    varianceWeightedRowMeasure_isProbabilityMeasure (A := A) (μ := μ) n⟩

/-- Helper for Theorem 15.43: coercing the owner probability law back to a measure recovers the
underlying weighted-row measure. -/
@[simp] private theorem varianceWeightedRowLaw_toMeasure
    (n : ℕ) :
    (A.varianceWeightedRowLaw μ n : Measure ℝ) = A.varianceWeightedRowMeasure μ n :=
  rfl

/-- Helper for Theorem 15.43: rewrite the weighted-entry kernel integral as a source-variable
integral against `μ`, with the quadratic weight moved into the integrand. -/
private lemma integral_centeredQuadraticCharFunKernel_weightedEntry_eq_sourceIntegral
    (n : ℕ) (i : Fin (A.rowLength n)) (t : ℝ) :
    ∫ x, centeredQuadraticCharFunKernelBCF t x
      ∂(((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) : Measure ℝ) =
        ∫ ω, centeredQuadraticCharFunKernel t (A n i ω) * (((A n i ω : ℂ) ^ (2 : ℕ))) ∂μ := by
  have hKernelMap :
      AEStronglyMeasurable (centeredQuadraticCharFunKernelBCF t : ℝ → ℂ)
        (Measure.map (A n i) (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2))) := by
    exact
      (centeredQuadraticCharFunKernelBCF t).continuous.stronglyMeasurable.aestronglyMeasurable
  have hDensityMeas :
      Measurable (fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)) := by
    exact ((A.measurable_entry n i).pow_const 2).ennreal_ofReal
  have hDensityFinite :
      ∀ᵐ ω ∂μ, ENNReal.ofReal ((A n i ω) ^ 2) < ⊤ :=
    Filter.Eventually.of_forall fun _ ↦ by simp
  -- Proof comment: first remove the pushforward, then rewrite the `withDensity` integral as a
  -- source integral with the quadratic weight moved into the integrand.
  rw [integral_map (A.measurable_entry n i).aemeasurable hKernelMap]
  rw [integral_withDensity_eq_integral_toReal_smul hDensityMeas hDensityFinite]
  refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
  change
    (((ENNReal.ofReal ((A n i ω) ^ 2)).toReal : ℝ) • centeredQuadraticCharFunKernel t (A n i ω)) =
      centeredQuadraticCharFunKernel t (A n i ω) * (((A n i ω : ℂ) ^ (2 : ℕ)))
  rw [ENNReal.toReal_ofReal (sq_nonneg (A n i ω)), Complex.real_smul]
  simpa [pow_two, mul_comm]

/-- Helper for Theorem 15.43: one weighted entry law integrates the centered quadratic kernel to
the corresponding characteristic-function increment `φₙ,ᵢ(t) - 1`. -/
private lemma entryCharFunSubOne_eq_integral_centeredQuadraticCharFunKernelBCF_weightedEntry
    (n : ℕ) (i : Fin (A.rowLength n)) (t : ℝ) :
    ∫ x, centeredQuadraticCharFunKernelBCF t x
      ∂(((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) : Measure ℝ) =
        charFun (μ.map (A n i)) t - 1 := by
  have hTransport :=
    integral_centeredQuadraticCharFunKernel_weightedEntry_eq_sourceIntegral
      (A := A) (μ := μ) n i t
  have hEntryInt :
      Integrable (fun ω ↦ (A n i ω : ℂ)) μ :=
    (RealRandomVariableArray.IsCentered.integrable (A := A) (μ := μ) n i).ofReal
  have hLinearInt :
      Integrable (fun ω ↦ Complex.I * (t * A n i ω : ℝ)) μ := by
    have hConst :
        Integrable (fun ω ↦ (Complex.I * (t : ℂ)) * (A n i ω : ℂ)) μ :=
      hEntryInt.const_mul (Complex.I * (t : ℂ))
    simpa [mul_assoc, mul_left_comm, mul_comm] using hConst
  have hExpKernelMeas :
      Measurable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I)) := by
    refine Complex.measurable_exp.comp ?_
    simpa using
      (Complex.measurable_ofReal.comp ((A.measurable_entry n i).const_mul t)).mul_const Complex.I
  have hExpKernelInt :
      Integrable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I)) μ := by
    refine Integrable.of_bound hExpKernelMeas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (t * A n i ω)).le
  have hExpSubOneInt :
      Integrable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I) - 1) μ :=
    hExpKernelInt.sub (integrable_const 1)
  have hMeanZero :
      ∫ ω, Complex.I * (t * A n i ω : ℝ) ∂μ = 0 := by
    have hOfReal :
        ∫ ω, (A n i ω : ℂ) ∂μ = ((∫ ω, A n i ω ∂μ : ℝ) : ℂ) := by
      simpa using (integral_ofReal (μ := μ) (f := fun ω ↦ A n i ω))
    -- Proof comment: convert the complex linear term into a scalar multiple of the centered entry
    -- expectation and then use the centeredness hypothesis.
    calc
      ∫ ω, Complex.I * (t * A n i ω : ℝ) ∂μ =
          ∫ ω, (Complex.I * (t : ℂ)) * (A n i ω : ℂ) ∂μ := by
            congr with ω
            simp [mul_assoc]
      _ = (Complex.I * (t : ℂ)) * ∫ ω, (A n i ω : ℂ) ∂μ := by
            simpa using
              (integral_const_mul (μ := μ) (Complex.I * (t : ℂ))
                (fun ω ↦ (A n i ω : ℂ)))
      _ = (Complex.I * (t : ℂ)) * ((∫ ω, A n i ω ∂μ : ℝ) : ℂ) := by
            rw [hOfReal]
      _ = 0 := by
            simp [RealRandomVariableArray.IsCentered.expectation_eq_zero
              (A := A) (μ := μ) n i]
  have hKernelMap :
      AEStronglyMeasurable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
        (Measure.map (A n i) μ) := by
    refine (Complex.measurable_exp.comp ?_).aestronglyMeasurable
    simpa using
      (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const Complex.I
  -- Route correction: after the transport lemma, remove the denominator pointwise with
  -- `centeredQuadraticCharFunKernel_mul_sq` and only then identify the remaining source integral
  -- with `φₙ,ᵢ(t) - 1`.
  calc
    ∫ x, centeredQuadraticCharFunKernelBCF t x
        ∂(((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) : Measure ℝ) =
        ∫ ω, centeredQuadraticCharFunKernel t (A n i ω) * (((A n i ω : ℂ) ^ (2 : ℕ))) ∂μ :=
          hTransport
    _ = ∫ ω,
          (Complex.exp (t * A n i ω * Complex.I) - 1 - Complex.I * (t * A n i ω : ℝ)) ∂μ := by
          refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
          simpa using centeredQuadraticCharFunKernel_mul_sq (t := t) (x := A n i ω)
    _ = ∫ ω, (Complex.exp (t * A n i ω * Complex.I) - 1) ∂μ := by
          rw [integral_sub hExpSubOneInt hLinearInt, hMeanZero, sub_zero]
    _ = ∫ ω, Complex.exp (t * A n i ω * Complex.I) ∂μ - 1 := by
          symm
          rw [integral_sub hExpKernelInt (integrable_const 1)]
          simp
    _ = charFun (μ.map (A n i)) t - 1 := by
          rw [MeasureTheory.charFun_apply_real]
          rw [integral_map (A.measurable_entry n i).aemeasurable hKernelMap]

/-- Helper for Theorem 15.43: the full middle object `∑ (φₙ,ᵢ(t) - 1)` is exactly one integral
against the variance-weighted row law. -/
private lemma sumEntryCharFunSubOne_eq_integral_centeredQuadraticCharFunKernelBCF_varianceWeightedRowLaw
    (n : ℕ) (t : ℝ) :
    ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1) =
      ∫ x, centeredQuadraticCharFunKernelBCF t x ∂(A.varianceWeightedRowLaw μ n : Measure ℝ) := by
  calc
    ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1) =
        ∑ i : Fin (A.rowLength n),
          ∫ x, centeredQuadraticCharFunKernelBCF t x
            ∂(((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) : Measure ℝ) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          symm
          exact
            entryCharFunSubOne_eq_integral_centeredQuadraticCharFunKernelBCF_weightedEntry
              (A := A) (μ := μ) n i t
    _ = ∫ x, centeredQuadraticCharFunKernelBCF t x ∂(A.varianceWeightedRowLaw μ n : Measure ℝ) := by
          rw [varianceWeightedRowLaw_toMeasure, varianceWeightedRowMeasure]
          symm
          refine integral_finset_sum_measure ?_
          intro i hi
          have hSqInt : HasFiniteIntegral (fun ω ↦ (A n i ω) ^ 2) μ := by
            have hIntegrableSq : Integrable (fun ω ↦ (A n i ω) ^ 2) μ := by
              simpa using
                (RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := μ) n i).integrable_sq
            exact hIntegrableSq.hasFiniteIntegral
          letI :
              IsFiniteMeasure (μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)) :=
            MeasureTheory.isFiniteMeasure_withDensity_ofReal hSqInt
          exact
            BoundedContinuousFunction.integrable
              (μ := (((μ.withDensity fun ω ↦ ENNReal.ofReal ((A n i ω) ^ 2)).map (A n i)) :
                Measure ℝ))
              (centeredQuadraticCharFunKernelBCF t)

/-- Helper for Theorem 15.43: convergence of the variance-weighted row laws to `δ₀` transports
directly to the middle-object limit `∑ (φₙ,ᵢ(t) - 1) → -t²/2`. -/
private lemma sumEntryCharFunSubOne_tendsto_gaussianExponent_of_varianceWeightedRowLaw
    (t : ℝ)
    (hWeighted :
      Tendsto (fun n ↦ A.varianceWeightedRowLaw μ n) atTop (𝓝 (diracProba (0 : ℝ)))) :
    Tendsto
      (fun n ↦ ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1))
      atTop
      (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
  have hIntegral :
      Tendsto
        (fun n ↦ ∫ x, centeredQuadraticCharFunKernelBCF t x
          ∂(A.varianceWeightedRowLaw μ n : Measure ℝ))
        atTop
        (𝓝
          (∫ x, centeredQuadraticCharFunKernelBCF t x
            ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ))) := by
    exact
      (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).1 hWeighted
        (centeredQuadraticCharFunKernelBCF t)
  have hDirac :
      (∫ x, centeredQuadraticCharFunKernelBCF t x
        ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) =
        ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
    -- Proof comment: the Dirac limit evaluates the bounded continuous kernel at `0`.
    rw [show (((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = Measure.dirac (0 : ℝ)
      by rfl]
    simp [centeredQuadraticCharFunKernel_apply_zero]
  have hIntegral' :
      Tendsto
        (fun n ↦ ∫ x, centeredQuadraticCharFunKernelBCF t x
          ∂(A.varianceWeightedRowLaw μ n : Measure ℝ))
        atTop
        (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
    convert hIntegral using 1
    exact congrArg nhds hDirac.symm
  have hEq :
      (fun n ↦ ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)) =
        fun n ↦ ∫ x, centeredQuadraticCharFunKernelBCF t x
          ∂(A.varianceWeightedRowLaw μ n : Measure ℝ) := by
    funext n
    exact
      sumEntryCharFunSubOne_eq_integral_centeredQuadraticCharFunKernelBCF_varianceWeightedRowLaw
        (A := A) (μ := μ) n t
  -- Proof comment: combine the rowwise integral identity with the bounded-continuous transport of
  -- weak convergence to `δ₀`.
  rw [hEq]
  exact hIntegral'

/-- Helper for Theorem 15.43: the owner probability law has the same tail formula as the
underlying weighted-row measure. -/
private lemma varianceWeightedRowLaw_tail_eq
    (ε : ℝ) (n : ℕ) :
    (A.varianceWeightedRowLaw μ n : Measure ℝ).real {x | ε < |x|} =
      ∑ i : Fin (A.rowLength n),
        ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ := by
  -- Proof comment: this is only the coercion rewrite from the owner law back to its measure.
  simpa [varianceWeightedRowLaw_toMeasure (A := A) (μ := μ) n] using
    varianceWeightedRowMeasure_tail_eq (A := A) (μ := μ) ε n

/-- Helper for Theorem 15.43: the Lindeberg condition already forces the canonical owner-law tails
to vanish outside every neighborhood of `0`. -/
private lemma varianceWeightedRowLaw_tail_tendsto_zero_of_satisfiesLindebergCondition
    (hLindeberg : A.SatisfiesLindebergCondition μ)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n ↦ (A.varianceWeightedRowLaw μ n : Measure ℝ).real {x | ε < |x|})
      atTop (𝓝 0) := by
  -- Proof comment: the owner-law tail formula is exactly the textbook truncated second-moment
  -- expression, so the vanishing follows directly from the previously established criterion.
  have hEq :
      (fun n ↦ (A.varianceWeightedRowLaw μ n : Measure ℝ).real {x | ε < |x|}) =
        (fun n ↦
          ∑ i : Fin (A.rowLength n),
            ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ) := by
    funext n
    exact varianceWeightedRowLaw_tail_eq (A := A) (μ := μ) ε n
  rw [hEq]
  exact (satisfiesLindebergCondition_iff (A := A) (μ := μ)).1 hLindeberg hε

/-- Helper for Theorem 15.43: if a sequence of probability laws on `ℝ` puts asymptotically all of
its mass inside every neighborhood of `0`, then it integrates each bounded continuous test
function to its value at `0`. -/
private lemma tendsto_integral_boundedContinuous_of_tail_tendsto_zero
    {ν : ℕ → ProbabilityMeasure ℝ}
    (hTail : ∀ ⦃ε : ℝ⦄, 0 < ε →
      Tendsto (fun n ↦ (ν n : Measure ℝ).real {x | ε < |x|}) atTop (𝓝 0))
    (f : BoundedContinuousFunction ℝ ℂ) :
    Tendsto (fun n ↦ ∫ x, f x ∂(ν n : Measure ℝ)) atTop (𝓝 (f 0)) := by
  let g : BoundedContinuousFunction ℝ ℂ := f - BoundedContinuousFunction.const ℝ (f 0)
  have hg0 : g 0 = 0 := by
    -- Proof comment: after subtracting the limit value, the centered test function vanishes at
    -- the target point `0`.
    simp [g]
  have hIntegralEq :
      (fun n ↦ ∫ x, f x ∂(ν n : Measure ℝ)) =
        fun n ↦ ∫ x, g x ∂(ν n : Measure ℝ) + f 0 := by
    funext n
    have hgInt : Integrable g (ν n : Measure ℝ) :=
      BoundedContinuousFunction.integrable (μ := (ν n : Measure ℝ)) g
    have hConstInt : Integrable (fun _ : ℝ ↦ (f 0 : ℂ)) (ν n : Measure ℝ) :=
      integrable_const _
    -- Proof comment: split `f` into its centered part and the constant value `f 0`.
    calc
      ∫ x, f x ∂(ν n : Measure ℝ) = ∫ x, (g x + f 0) ∂(ν n : Measure ℝ) := by
        congr 1 with x
        simp [g]
      _ = ∫ x, g x ∂(ν n : Measure ℝ) + ∫ x, (f 0 : ℂ) ∂(ν n : Measure ℝ) := by
        rw [integral_add hgInt hConstInt]
      _ = ∫ x, g x ∂(ν n : Measure ℝ) + f 0 := by
        simp
  rw [hIntegralEq]
  have hCentered :
      Tendsto (fun n ↦ ∫ x, g x ∂(ν n : Measure ℝ)) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 ?_
    intro ε hε
    obtain ⟨δ, hδpos, hδ⟩ :=
      Metric.continuousAt_iff.1 g.continuous.continuousAt (ε / 4) (by positivity)
    let r : ℝ := δ / 2
    let s : Set ℝ := {x | r < |x|}
    have hrpos : 0 < r := by
      -- Proof comment: shrink the continuity neighborhood so that the complement of the tail set
      -- stays inside the continuity control ball around `0`.
      dsimp [r]
      exact half_pos hδpos
    have hs : MeasurableSet s := by
      exact measurableSet_lt measurable_const measurable_abs
    let C : ℝ := ‖g‖ + 1
    have hCpos : 0 < C := by
      dsimp [C]
      positivity
    have hTailSmall : ∀ᶠ n in atTop, (ν n : Measure ℝ).real s < ε / (4 * C) := by
      have hTail' : Tendsto (fun n ↦ (ν n : Measure ℝ).real s) atTop (𝓝 0) := by
        simpa [s, r] using hTail hrpos
      exact hTail' (Iio_mem_nhds (by positivity : 0 < ε / (4 * C)))
    filter_upwards [hTailSmall] with n hn
    have hgInt : Integrable g (ν n : Measure ℝ) :=
      BoundedContinuousFunction.integrable (μ := (ν n : Measure ℝ)) g
    have hs_lt_top : (ν n : Measure ℝ) s < ⊤ := by
      simp [s]
    have hscompl_lt_top : (ν n : Measure ℝ) sᶜ < ⊤ := by
      simp [s]
    have hSmallOnCompl : ∀ x ∈ sᶜ, ‖g x‖ ≤ ε / 4 := by
      intro x hx
      have hxle : |x| ≤ r := by
        dsimp [s] at hx
        exact le_of_not_gt hx
      have hrlt : r < δ := by
        dsimp [r]
        linarith
      have hxdist : dist x 0 < δ := by
        simpa [Real.dist_eq, abs_sub_comm] using lt_of_le_of_lt hxle hrlt
      have hxcont : dist (g x) (g 0) < ε / 4 := hδ hxdist
      -- Proof comment: points outside the tail set stay in the continuity neighborhood where the
      -- centered test function is uniformly small.
      simpa [hg0, dist_eq_norm] using le_of_lt hxcont
    have hTailIntegral :
        ‖∫ x in s, g x ∂(ν n : Measure ℝ)‖ < ε / 4 := by
      have hBase :
          ‖∫ x in s, g x ∂(ν n : Measure ℝ)‖ ≤ ‖g‖ * (ν n : Measure ℝ).real s :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const hs_lt_top
          (fun x _ ↦ BoundedContinuousFunction.norm_coe_le_norm g x)
      have hCmul :
          ‖g‖ * (ν n : Measure ℝ).real s ≤ C * (ν n : Measure ℝ).real s := by
        dsimp [C]
        gcongr
        linarith
      have hScaled :
          C * (ν n : Measure ℝ).real s < C * (ε / (4 * C)) := by
        gcongr
      have hRewrite : C * (ε / (4 * C)) = ε / 4 := by
        field_simp [hCpos.ne']
      exact lt_of_le_of_lt (hBase.trans hCmul) (hScaled.trans_eq hRewrite)
    have hComplIntegral :
        ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ ≤ ε / 4 := by
      have hBase :
          ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ ≤
            (ε / 4) * (ν n : Measure ℝ).real sᶜ :=
        MeasureTheory.norm_setIntegral_le_of_norm_le_const hscompl_lt_top hSmallOnCompl
      have hMassLeOne : (ν n : Measure ℝ).real sᶜ ≤ 1 := by
        calc
          (ν n : Measure ℝ).real sᶜ ≤ (ν n : Measure ℝ).real Set.univ := by
            exact MeasureTheory.measureReal_mono (by intro x _; simp)
          _ = 1 := by
            simp
      calc
        ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ ≤ (ε / 4) * (ν n : Measure ℝ).real sᶜ := hBase
        _ ≤ (ε / 4) * 1 := by
          gcongr
        _ = ε / 4 := by ring
    have hSplit := (integral_add_compl hs hgInt).symm
    -- Proof comment: split the centered integral into the small tail part and the uniformly small
    -- near-zero part, then add the two bounds.
    calc
      dist (∫ x, g x ∂(ν n : Measure ℝ)) 0 = ‖∫ x, g x ∂(ν n : Measure ℝ)‖ := by
        simp [dist_eq_norm]
      _ = ‖∫ x in s, g x ∂(ν n : Measure ℝ) + ∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ := by
        rw [← hSplit]
      _ ≤ ‖∫ x in s, g x ∂(ν n : Measure ℝ)‖ + ‖∫ x in sᶜ, g x ∂(ν n : Measure ℝ)‖ := by
        exact norm_add_le _ _
      _ ≤ ε / 4 + ε / 4 := by
        linarith [le_of_lt hTailIntegral, hComplIntegral]
      _ = ε / 2 := by ring
      _ < ε := by linarith
  simpa [zero_add] using hCentered.add tendsto_const_nhds

/-- Helper for Theorem 15.43: vanishing tails outside every neighborhood of `0` force weak
convergence to the Dirac probability measure at `0`. -/
private lemma tendsto_diracProba_zero_of_tail_tendsto_zero
    {ν : ℕ → ProbabilityMeasure ℝ}
    (hTail : ∀ ⦃ε : ℝ⦄, 0 < ε →
      Tendsto (fun n ↦ (ν n : Measure ℝ).real {x | ε < |x|}) atTop (𝓝 0)) :
    Tendsto ν atTop (𝓝 (diracProba (0 : ℝ))) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ]
  intro f
  have hIntegral :=
    tendsto_integral_boundedContinuous_of_tail_tendsto_zero hTail f
  have hDirac :
      (∫ x, f x ∂((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = f 0 := by
    rw [show (((diracProba (0 : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ)) = Measure.dirac (0 : ℝ)
      by rfl]
    rw [integral_dirac]
  convert hIntegral using 1
  exact congrArg nhds hDirac

/-- Helper for Theorem 15.43: the Lindeberg condition already implies weak convergence of the
canonical weighted-row laws to `diracProba 0`. -/
private lemma varianceWeightedRowLaw_tendsto_diracZero_of_satisfiesLindebergCondition
    (hLindeberg : A.SatisfiesLindebergCondition μ) :
    Tendsto (fun n ↦ A.varianceWeightedRowLaw μ n) atTop (𝓝 (diracProba (0 : ℝ))) := by
  -- Proof comment: once the weighted-row tails vanish outside every neighborhood of `0`, the
  -- generic bounded-continuous test-function lemma identifies the weak limit as `δ₀`.
  refine tendsto_diracProba_zero_of_tail_tendsto_zero ?_
  intro ε hε
  exact
    varianceWeightedRowLaw_tail_tendsto_zero_of_satisfiesLindebergCondition
      (A := A) (μ := μ) hLindeberg hε

/-- Helper for Theorem 15.43: for a fixed frequency `t`, a null array makes the entry
characteristic functions uniformly close to `1` across each row. -/
private lemma eventually_entryCharFunSubOne_le_of_isNull
    (hNull : A.IsNull μ)
    (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in atTop,
      ∀ i : Fin (A.rowLength n), ‖charFun (μ.map (A n i)) t - 1‖ ≤ δ := by
  let η : ℝ := δ / (4 * (|t| + 1))
  have hη : 0 < η := by
    dsimp [η]
    positivity
  have hTailSmall :
      ∀ᶠ n in atTop,
        ⨆ i : Fin (A.rowLength n), μ {ω | η < |A n i ω|} ≤ ENNReal.ofReal (δ / 4) := by
    -- Proof comment: use the null-array tail criterion at the cutoff `η`.
    have hTail := hNull.asymptotically_negligible hη
    exact hTail.eventually (Iic_mem_nhds <| by
      exact ENNReal.ofReal_pos.2 (by positivity : 0 < δ / 4))
  filter_upwards [hTailSmall] with n hnTail i
  let s : Set Ω := {ω | η < |A n i ω|}
  let f : Ω → ℂ := fun ω ↦ Complex.exp (t * A n i ω * Complex.I) - 1
  have hs : MeasurableSet s := by
    -- Proof comment: the tail event is measurable because the array entry is measurable.
    exact measurableSet_lt measurable_const (A.measurable_entry n i).norm
  have htail_real : μ.real s ≤ δ / 4 := by
    -- Proof comment: specialize the rowwise null-array supremum bound to the chosen entry.
    refine ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ δ / 4) ?_
    exact le_trans (le_iSup (fun j : Fin (A.rowLength n) ↦ μ {ω | η < |A n j ω|}) i) hnTail
  have hgood_const : |t| * η ≤ δ / 4 := by
    have ht_le : |t| ≤ |t| + 1 := by linarith
    calc
      |t| * η ≤ (|t| + 1) * η := by gcongr
      _ = δ / 4 := by
            dsimp [η]
            field_simp
  have hpoint_two : ∀ ω, ‖f ω‖ ≤ 2 := by
    intro ω
    have hnorm_exp : ‖Complex.exp (t * A n i ω * Complex.I)‖ = 1 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (t * A n i ω))
    calc
      ‖f ω‖ = ‖Complex.exp (t * A n i ω * Complex.I) - 1‖ := by rfl
      _ ≤ ‖Complex.exp (t * A n i ω * Complex.I)‖ + ‖(1 : ℂ)‖ := by
            simpa using norm_sub_le (Complex.exp (t * A n i ω * Complex.I)) (1 : ℂ)
      _ = 2 := by
            rw [hnorm_exp]
            norm_num
  have hgood_point : ∀ ω ∈ sᶜ, ‖f ω‖ ≤ |t| * η := by
    intro ω hω
    have hω_le : |A n i ω| ≤ η := by
      exact le_of_not_gt <| by simpa [s] using hω
    calc
      ‖f ω‖ = ‖Complex.exp (t * A n i ω * Complex.I) - 1‖ := by rfl
      _ ≤ |t * A n i ω| := by
            simpa [mul_assoc, mul_left_comm, mul_comm, Real.norm_eq_abs] using
              (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t * A n i ω))
      _ = |t| * |A n i ω| := by rw [abs_mul]
      _ ≤ |t| * η := by gcongr
  have htail_int : ‖∫ ω in s, f ω ∂μ‖ ≤ δ / 2 := by
    -- Proof comment: on the tail set the integrand is bounded by `2`, so its integral is
    -- controlled by the tail probability.
    calc
      ‖∫ ω in s, f ω ∂μ‖ ≤ 2 * μ.real s := by
        exact
          norm_setIntegral_le_of_norm_le_const
            (μ := μ) (s := s) (f := f) (by simp) fun ω _ ↦ hpoint_two ω
      _ ≤ 2 * (δ / 4) := by gcongr
      _ = δ / 2 := by ring
  have hgood_int : ‖∫ ω in sᶜ, f ω ∂μ‖ ≤ δ / 4 := by
    -- Proof comment: on the complement of the tail set, the small-entry estimate bounds the
    -- characteristic-function defect by `|t| * η`.
    calc
      ‖∫ ω in sᶜ, f ω ∂μ‖ ≤ (|t| * η) * μ.real sᶜ := by
        exact
          norm_setIntegral_le_of_norm_le_const
            (μ := μ) (s := sᶜ) (f := f) (by simp) hgood_point
      _ ≤ (|t| * η) * 1 := by
        gcongr
        exact measureReal_le_one
      _ = |t| * η := by ring
      _ ≤ δ / 4 := hgood_const
  have hexp_int : Integrable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I)) μ := by
    have hmeas :
        Measurable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I)) := by
      refine Complex.measurable_exp.comp ?_
      simpa using
        (Complex.measurable_ofReal.comp ((A.measurable_entry n i).const_mul t)).mul_const
          Complex.I
    refine Integrable.of_bound hmeas.aestronglyMeasurable 1 ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hnorm_exp : ‖Complex.exp (t * A n i ω * Complex.I)‖ = 1 := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.norm_exp_ofReal_mul_I (t * A n i ω))
    simpa [hnorm_exp]
  have hf_int : Integrable f μ := by
    exact hexp_int.sub (integrable_const 1)
  have hchar_split :
      charFun (μ.map (A n i)) t - 1 = ∫ ω in s, f ω ∂μ + ∫ ω in sᶜ, f ω ∂μ := by
    have hconst : (∫ ω, (1 : ℂ) ∂μ) = 1 := by simp
    have hkernel_meas :
        AEStronglyMeasurable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
          (Measure.map (A n i) μ) := by
      refine (Complex.measurable_exp.comp ?_).aestronglyMeasurable
      simpa using
        (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const Complex.I
    -- Proof comment: rewrite the entry characteristic function as the integral of `f`, then split
    -- it into the tail and small-entry regions.
    rw [MeasureTheory.charFun_apply_real]
    rw [integral_map (A.measurable_entry n i).aemeasurable hkernel_meas]
    rw [← hconst, ← integral_sub hexp_int (integrable_const 1)]
    simpa [f] using (integral_add_compl hs hf_int).symm
  calc
    ‖charFun (μ.map (A n i)) t - 1‖ =
        ‖∫ ω in s, f ω ∂μ + ∫ ω in sᶜ, f ω ∂μ‖ := by
          rw [hchar_split]
    _ ≤ ‖∫ ω in s, f ω ∂μ‖ + ‖∫ ω in sᶜ, f ω ∂μ‖ := by
          exact norm_add_le _ _
    _ ≤ δ / 2 + δ / 4 := by
          gcongr
    _ ≤ δ := by
          linarith

/-- Helper for Theorem 15.43: for a fixed frequency `t`, a null array makes the entry
characteristic functions uniformly close to `1` across each row. -/
private lemma entryCharFunSubOneSup_tendstoZero_of_isNull
    (hNull : A.IsNull μ) (t : ℝ) :
    Tendsto
      (fun n ↦ ⨆ i : Fin (A.rowLength n), ‖charFun (μ.map (A n i)) t - 1‖)
      atTop (𝓝 0) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  have hHalf : 0 < ε / 2 := by positivity
  filter_upwards [eventually_entryCharFunSubOne_le_of_isNull
    (A := A) (μ := μ) hNull t hHalf] with n hn
  have hsup_le :
      (⨆ i : Fin (A.rowLength n), ‖charFun (μ.map (A n i)) t - 1‖) ≤ ε / 2 := by
    -- Proof comment: normalize the finite supremum to `Finset.sup'` and bound each row entry by
    -- the eventual `ε / 2` control.
    by_cases hempty : IsEmpty (Fin (A.rowLength n))
    · letI := hempty
      simp
      positivity
    · letI : Nonempty (Fin (A.rowLength n)) := not_isEmpty_iff.mp hempty
      rw [← Finset.sup'_univ_eq_ciSup]
      exact Finset.sup'_le Finset.univ_nonempty _ fun i _ ↦ hn i
  have hsup_nonneg :
      0 ≤ ⨆ i : Fin (A.rowLength n), ‖charFun (μ.map (A n i)) t - 1‖ := by
    -- Proof comment: every row defect is a norm, so the finite supremum is nonnegative.
    by_cases hempty : IsEmpty (Fin (A.rowLength n))
    · letI := hempty
      simp
    · letI : Nonempty (Fin (A.rowLength n)) := not_isEmpty_iff.mp hempty
      let i0 : Fin (A.rowLength n) := Classical.choice ‹Nonempty (Fin (A.rowLength n))›
      rw [← Finset.sup'_univ_eq_ciSup]
      have hle :
          ‖charFun (μ.map (A n i0)) t - 1‖ ≤
            Finset.univ.sup' Finset.univ_nonempty
              (fun i : Fin (A.rowLength n) ↦ ‖charFun (μ.map (A n i)) t - 1‖) := by
        exact
          Finset.le_sup' (f := fun i : Fin (A.rowLength n) ↦
            ‖charFun (μ.map (A n i)) t - 1‖) (Finset.mem_univ i0)
      exact le_trans (norm_nonneg _) hle
  simpa [Real.dist_eq, abs_of_nonneg hsup_nonneg] using
    lt_of_le_of_lt hsup_le (by linarith : ε / 2 < ε)

/-- Helper for Theorem 15.43: after centering removes the linear term, the rowwise sum of the
entry characteristic-function defects is bounded by `t^2 / 2`. -/
private lemma sumNormEntryCharFunSubOne_le_halfSq
    (n : ℕ) (t : ℝ) :
    ∑ i : Fin (A.rowLength n), ‖charFun (μ.map (A n i)) t - 1‖ ≤ t ^ (2 : ℕ) / 2 := by
  -- Proof comment: bound each entry defect by the quadratic Taylor remainder and then sum the
  -- resulting variance contributions across the row.
  calc
    ∑ i : Fin (A.rowLength n), ‖charFun (μ.map (A n i)) t - 1‖
        ≤ ∑ i : Fin (A.rowLength n), (t ^ (2 : ℕ) / 2) * Var[A n i; μ] := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hExpKernelMeas :
              Measurable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I)) := by
            refine Complex.measurable_exp.comp ?_
            simpa using
              (Complex.measurable_ofReal.comp ((A.measurable_entry n i).const_mul t)).mul_const
                Complex.I
          have hExpInt :
              Integrable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I) - 1) μ := by
            refine Integrable.of_bound (hExpKernelMeas.sub measurable_const).aestronglyMeasurable
              2 ?_
            filter_upwards with ω
            have htri :
                ‖Complex.exp (t * A n i ω * Complex.I) - 1‖ ≤
                  ‖Complex.exp (t * A n i ω * Complex.I)‖ + ‖(1 : ℂ)‖ := by
              simpa using norm_sub_le (Complex.exp (t * A n i ω * Complex.I)) (1 : ℂ)
            have hexp_norm : ‖Complex.exp (t * A n i ω * Complex.I)‖ = 1 := by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                Complex.norm_exp_ofReal_mul_I (t * A n i ω)
            have hbound : ‖Complex.exp (t * A n i ω * Complex.I)‖ + ‖(1 : ℂ)‖ ≤ 2 := by
              norm_num [hexp_norm]
            exact le_trans htri hbound
          have hEntryInt :
              Integrable (fun ω ↦ (A n i ω : ℂ)) μ :=
            (RealRandomVariableArray.IsCentered.integrable (A := A) (μ := μ) n i).ofReal
          have hLinearInt :
              Integrable (fun ω ↦ Complex.I * (t * A n i ω : ℝ)) μ := by
            have hConst :
                Integrable (fun ω ↦ (Complex.I * (t : ℂ)) * (A n i ω : ℂ)) μ :=
              hEntryInt.const_mul (Complex.I * (t : ℂ))
            simpa [mul_assoc, mul_left_comm, mul_comm] using hConst
          have hMeanZero :
              ∫ ω, Complex.I * (t * A n i ω : ℝ) ∂μ = 0 := by
            have hOfReal :
                ∫ ω, (A n i ω : ℂ) ∂μ = ((∫ ω, A n i ω ∂μ : ℝ) : ℂ) := by
              simpa using (integral_ofReal (μ := μ) (f := fun ω ↦ A n i ω))
            calc
              ∫ ω, Complex.I * (t * A n i ω : ℝ) ∂μ =
                  ∫ ω, (Complex.I * (t : ℂ)) * (A n i ω : ℂ) ∂μ := by
                    congr with ω
                    simp [mul_assoc]
              _ = (Complex.I * (t : ℂ)) * ∫ ω, (A n i ω : ℂ) ∂μ := by
                    simpa using
                      (integral_const_mul (μ := μ) (Complex.I * (t : ℂ))
                        (fun ω ↦ (A n i ω : ℂ)))
              _ = (Complex.I * (t : ℂ)) * ((∫ ω, A n i ω ∂μ : ℝ) : ℂ) := by
                    rw [hOfReal]
              _ = 0 := by
                    simp [RealRandomVariableArray.IsCentered.expectation_eq_zero
                      (A := A) (μ := μ) n i]
          have hExpKernelInt :
              Integrable (fun ω ↦ Complex.exp (t * A n i ω * Complex.I)) μ := by
            refine Integrable.of_bound hExpKernelMeas.aestronglyMeasurable 1 ?_
            exact Filter.Eventually.of_forall fun ω ↦ by
              simpa [mul_assoc, mul_left_comm, mul_comm] using
                (Complex.norm_exp_ofReal_mul_I (t * A n i ω)).le
          have hKernelMap :
              AEStronglyMeasurable (fun x : ℝ ↦ Complex.exp (t * x * Complex.I))
                (Measure.map (A n i) μ) := by
            refine (Complex.measurable_exp.comp ?_).aestronglyMeasurable
            simpa using
              (Complex.measurable_ofReal.comp (measurable_const.mul measurable_id)).mul_const
                Complex.I
          have hRemainderEq :
              charFun (μ.map (A n i)) t - 1 =
                ∫ ω,
                  (Complex.exp (t * A n i ω * Complex.I) - 1 -
                    Complex.I * (t * A n i ω : ℝ)) ∂μ := by
            calc
              charFun (μ.map (A n i)) t - 1 =
                  ∫ ω, Complex.exp (t * A n i ω * Complex.I) ∂μ - 1 := by
                    rw [MeasureTheory.charFun_apply_real]
                    rw [integral_map (A.measurable_entry n i).aemeasurable hKernelMap]
              _ = ∫ ω, Complex.exp (t * A n i ω * Complex.I) ∂μ - ∫ x, (1 : ℂ) ∂μ := by
                    rw [integral_const]
                    simp
              _ = ∫ ω, (Complex.exp (t * A n i ω * Complex.I) - 1) ∂μ := by
                    symm
                    rw [integral_sub hExpKernelInt (integrable_const 1)]
              _ =
                  ∫ ω, (Complex.exp (t * A n i ω * Complex.I) - 1) ∂μ -
                    ∫ ω, Complex.I * (t * A n i ω : ℝ) ∂μ := by
                      rw [hMeanZero, sub_zero]
              _ = ∫ ω,
                    (Complex.exp (t * A n i ω * Complex.I) - 1 -
                      Complex.I * (t * A n i ω : ℝ)) ∂μ := by
                      symm
                      rw [integral_sub hExpInt hLinearInt]
          rw [hRemainderEq]
          let g : Ω → ℝ := fun ω ↦ |t * A n i ω| ^ (2 : ℕ) / 2
          have hg_eq :
              g = fun ω ↦ (t ^ (2 : ℕ) / 2) * (A n i ω) ^ (2 : ℕ) := by
            funext ω
            dsimp [g]
            have hsq :
                |t * A n i ω| ^ (2 : ℕ) = t ^ (2 : ℕ) * (A n i ω) ^ (2 : ℕ) := by
              rw [abs_mul, mul_pow, sq_abs, sq_abs]
            exact by
              simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
                congrArg (fun x : ℝ ↦ x / 2) hsq
          have hg : Integrable g μ := by
            rw [hg_eq]
            have hsqInt : Integrable (fun ω ↦ (A n i ω) ^ (2 : ℕ)) μ := by
              simpa using
                (RealRandomVariableArray.IsNormed.memLp_two (A := A) (μ := μ) n i).integrable_sq
            exact hsqInt.const_mul _
          have hpointwise :
              ∀ᵐ ω ∂μ,
                ‖Complex.exp (t * A n i ω * Complex.I) - 1 -
                    Complex.I * (t * A n i ω : ℝ)‖ ≤
                  g ω := by
            refine Filter.Eventually.of_forall fun ω ↦ ?_
            dsimp [g]
            simpa [Finset.sum_range_succ, pow_two, sub_eq_add_neg, add_assoc, add_left_comm,
              add_comm, mul_assoc, mul_left_comm, mul_comm] using
              norm_exp_mul_I_sub_taylor_sum_le (t := t * A n i ω) (n := 2)
          calc
            ‖∫ ω,
                (Complex.exp (t * A n i ω * Complex.I) - 1 -
                  Complex.I * (t * A n i ω : ℝ)) ∂μ‖
                ≤ ∫ ω, g ω ∂μ := by
                  exact MeasureTheory.norm_integral_le_of_norm_le hg hpointwise
            _ = (t ^ (2 : ℕ) / 2) * ∫ ω, (A n i ω) ^ (2 : ℕ) ∂μ := by
                  rw [hg_eq, integral_const_mul]
            _ = (t ^ (2 : ℕ) / 2) * Var[A n i; μ] := by
                  congr 1
                  exact
                    (ProbabilityTheory.variance_of_integral_eq_zero
                      (A.measurable_entry n i).aemeasurable
                      (RealRandomVariableArray.IsCentered.expectation_eq_zero
                        (A := A) (μ := μ) n i)).symm
    _ = (t ^ (2 : ℕ) / 2) * ∑ i : Fin (A.rowLength n), Var[A n i; μ] := by
          rw [Finset.mul_sum]
    _ = t ^ (2 : ℕ) / 2 := by
          rw [RealRandomVariableArray.IsNormed.variance_sum_eq_one (A := A) (μ := μ) n, mul_one]

/-- Helper for Theorem 15.43: under the null-array hypothesis, the first-order logarithmic
remainder `Σ log φₙ,i(t) - Σ (φₙ,i(t) - 1)` tends to `0` at each fixed frequency. -/
private lemma sumLogEntryCharFun_sub_sumEntryCharFunSubOne_tendstoZero_of_isNull
    (hNull : A.IsNull μ) (t : ℝ) :
    Tendsto
      (fun n ↦
        ‖(∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) -
            ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)‖)
      atTop
      (𝓝 0) := by
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  let B : ℝ := t ^ (2 : ℕ) / 2 + 1
  let δ : ℝ := min (1 / 2 : ℝ) (ε / (2 * B))
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδhalf : δ ≤ 1 / 2 := by
    dsimp [δ]
    exact min_le_left _ _
  have hδbound : δ ≤ ε / (2 * B) := by
    dsimp [δ]
    exact min_le_right _ _
  filter_upwards [eventually_entryCharFunSubOne_le_of_isNull
    (A := A) (μ := μ) hNull t hδpos] with n hn
  let z : Fin (A.rowLength n) → ℂ := fun i ↦ charFun (μ.map (A n i)) t
  have hterm :
      ∀ i : Fin (A.rowLength n),
        ‖Complex.log (z i) - (z i - 1)‖ ≤ δ * ‖z i - 1‖ := by
    intro i
    have hz_lt_one : ‖z i - 1‖ < 1 := by
      have hquarter : (1 / 2 : ℝ) < 1 := by norm_num
      exact lt_of_le_of_lt (hn i) (lt_of_le_of_lt hδhalf hquarter)
    calc
      ‖Complex.log (z i) - (z i - 1)‖ =
          ‖Complex.log (1 + (z i - 1)) - (z i - 1)‖ := by
            congr 1
            ring
      _ ≤ ‖z i - 1‖ ^ (2 : ℕ) * (1 - ‖z i - 1‖)⁻¹ / 2 := by
            exact Complex.norm_log_one_add_sub_self_le hz_lt_one
      _ ≤ ‖z i - 1‖ ^ (2 : ℕ) := by
            have hhalf : ‖z i - 1‖ ≤ 1 / 2 := le_trans (hn i) hδhalf
            have hInv : (1 - ‖z i - 1‖)⁻¹ ≤ 2 := by
              have hge : (1 / 2 : ℝ) ≤ 1 - ‖z i - 1‖ := by linarith
              have htmp : 1 / (1 - ‖z i - 1‖) ≤ (1 / (1 / 2 : ℝ)) := by
                exact one_div_le_one_div_of_le (by norm_num : 0 < (1 / 2 : ℝ)) hge
              simpa using htmp
            nlinarith [norm_nonneg (z i - 1)]
      _ ≤ δ * ‖z i - 1‖ := by
            nlinarith [hn i, norm_nonneg (z i - 1)]
  have hsum :
      ∑ i : Fin (A.rowLength n), ‖Complex.log (z i) - (z i - 1)‖ ≤
        δ * ∑ i : Fin (A.rowLength n), ‖z i - 1‖ := by
    calc
      ∑ i : Fin (A.rowLength n), ‖Complex.log (z i) - (z i - 1)‖ ≤
          ∑ i : Fin (A.rowLength n), δ * ‖z i - 1‖ := by
            exact Finset.sum_le_sum fun i _ ↦ hterm i
      _ = δ * ∑ i : Fin (A.rowLength n), ‖z i - 1‖ := by
            rw [Finset.mul_sum]
  have hBudget :
      ∑ i : Fin (A.rowLength n), ‖z i - 1‖ ≤ t ^ (2 : ℕ) / 2 := by
    simpa [z] using sumNormEntryCharFunSubOne_le_halfSq (A := A) (μ := μ) n t
  have hCoreLeB : t ^ (2 : ℕ) / 2 ≤ B := by
    dsimp [B]
    linarith
  have hδB : δ * B ≤ ε / 2 := by
    calc
      δ * B ≤ (ε / (2 * B)) * B := by
            gcongr
      _ = ε / 2 := by
            field_simp [hBpos.ne']
  have hBound :
      ‖(∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) -
          ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)‖ < ε := by
    calc
      ‖(∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) -
          ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)‖
          = ‖∑ i : Fin (A.rowLength n),
              (Complex.log (z i) - (z i - 1))‖ := by
                rw [Finset.sum_sub_distrib]
                simp [z]
      _ ≤ ∑ i : Fin (A.rowLength n), ‖Complex.log (z i) - (z i - 1)‖ := by
            simpa using
              (norm_sum_le (s := Finset.univ)
                (f := fun i : Fin (A.rowLength n) ↦ Complex.log (z i) - (z i - 1)))
      _ ≤ δ * ∑ i : Fin (A.rowLength n), ‖z i - 1‖ := hsum
      _ ≤ δ * (t ^ (2 : ℕ) / 2) := by
            gcongr
      _ ≤ δ * B := by
            gcongr
      _ ≤ ε / 2 := hδB
      _ < ε := by
            linarith
  simpa [Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using hBound

/-- Helper for Theorem 15.43: once every entry characteristic function stays in the principal
ball around `1`, the row-sum characteristic function is exactly `exp` of the sum of entry logs. -/
private lemma rowSumCharFun_eq_exp_sumLog_eventually_of_isNull
    (hNull : A.IsNull μ) (t : ℝ) :
    ∀ᶠ n in atTop,
      charFun (A.rowSumLaw μ n : Measure ℝ) t =
        Complex.exp
          (∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) := by
  have hQuarter :
      ∀ᶠ n in atTop,
        ∀ i : Fin (A.rowLength n), ‖charFun (μ.map (A n i)) t - 1‖ ≤ (1 / 4 : ℝ) := by
    exact eventually_entryCharFunSubOne_le_of_isNull
      (A := A) (μ := μ) hNull t (by positivity)
  filter_upwards [hQuarter] with n hn
  have hentry_ne :
      ∀ i : Fin (A.rowLength n), charFun (μ.map (A n i)) t ≠ 0 := by
    intro i hzero
    have hone : ‖charFun (μ.map (A n i)) t - 1‖ = 1 := by
      simp [hzero]
    have hsmall : ‖charFun (μ.map (A n i)) t - 1‖ < 1 / 2 := by
      exact lt_of_le_of_lt (hn i) (by norm_num)
    linarith
  -- Route correction: the theorem only needs the row-level exponential bridge; we postpone the
  -- stronger principal-branch identity for `Complex.log (charFun(rowSum))`.
  calc
    charFun (A.rowSumLaw μ n : Measure ℝ) t =
        ∏ i : Fin (A.rowLength n), charFun (μ.map (A n i)) t := by
          exact rowSumLaw_charFun_eq_prod_entryCharFun (A := A) (μ := μ) n t
    _ = ∏ i : Fin (A.rowLength n), Complex.exp (Complex.log (charFun (μ.map (A n i)) t)) := by
          refine Finset.prod_congr rfl fun i _ ↦ ?_
          symm
          exact Complex.exp_log (hentry_ne i)
    _ = Complex.exp
          (∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)) := by
          symm
          exact Complex.exp_sum _ _

/-- Helper for Theorem 15.43: at the single frequency `t = 1`, the null-array control and the
quadratic rowwise bound keep the whole sum of entry logarithms inside the principal strip, so the
row-sum logarithm is eventually the sum of the entry logarithms. -/
private lemma rowSumLawLog_eq_sumLogEntryCharFun_eventually_at_one_of_isNull
    (hNull : A.IsNull μ) :
    ∀ᶠ n in atTop,
      Complex.log (charFun (A.rowSumLaw μ n : Measure ℝ) (1 : ℝ)) =
        ∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) (1 : ℝ)) := by
  let s : ℕ → ℂ := fun n ↦
    ∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) (1 : ℝ))
  let u : ℕ → ℂ := fun n ↦
    ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) (1 : ℝ) - 1)
  have hBridge :=
    rowSumCharFun_eq_exp_sumLog_eventually_of_isNull (A := A) (μ := μ) hNull (1 : ℝ)
  have hSmallRem :
      ∀ᶠ n in atTop, ‖s n - u n‖ < 1 / 4 := by
    have hRem :=
      sumLogEntryCharFun_sub_sumEntryCharFunSubOne_tendstoZero_of_isNull
        (A := A) (μ := μ) hNull (1 : ℝ)
    exact hRem (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have hCoreBound : ∀ n : ℕ, ‖u n‖ ≤ 1 / 2 := by
    intro n
    calc
      ‖u n‖ ≤
          ∑ i : Fin (A.rowLength n), ‖charFun (μ.map (A n i)) (1 : ℝ) - 1‖ := by
            simpa [u] using
              (norm_sum_le (s := Finset.univ)
                (f := fun i : Fin (A.rowLength n) ↦
                  charFun (μ.map (A n i)) (1 : ℝ) - 1))
      _ ≤ (1 : ℝ) ^ (2 : ℕ) / 2 := by
            simpa [u] using sumNormEntryCharFunSubOne_le_halfSq (A := A) (μ := μ) n (1 : ℝ)
      _ = 1 / 2 := by norm_num
  filter_upwards [hBridge, hSmallRem] with n hnBridge hnSmall
  have hNorm : ‖s n‖ < 1 := by
    have hTriangle : ‖s n‖ ≤ ‖s n - u n‖ + ‖u n‖ := by
      have hsdecomp : s n - u n + u n = s n := sub_add_cancel (s n) (u n)
      calc
        ‖s n‖ = ‖s n - u n + u n‖ := by
          exact congrArg norm hsdecomp.symm
        _ ≤ ‖s n - u n‖ + ‖u n‖ := norm_add_le _ _
    calc
      ‖s n‖ ≤ ‖s n - u n‖ + ‖u n‖ := hTriangle
      _ < 1 / 4 + 1 / 2 := by linarith [hnSmall, hCoreBound n]
      _ < 1 := by norm_num
  have himAbs : |(s n).im| < 1 := lt_of_le_of_lt (Complex.abs_im_le_norm _) hNorm
  have himLower : -Real.pi < (s n).im := by
    have him : -1 < (s n).im := (abs_lt.mp himAbs).1
    linarith [Real.pi_gt_three]
  have himUpper : (s n).im ≤ Real.pi := by
    have him : (s n).im < 1 := (abs_lt.mp himAbs).2
    linarith [Real.pi_gt_three]
  -- Proof comment: the row-level exponential bridge is already available, so the only remaining
  -- work is to certify that the exponent stays in the principal strip and apply `Complex.log_exp`.
  calc
    Complex.log (charFun (A.rowSumLaw μ n : Measure ℝ) (1 : ℝ)) =
        Complex.log (Complex.exp (s n)) := by
          rw [hnBridge]
    _ = s n := Complex.log_exp himLower himUpper
    _ = ∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) (1 : ℝ)) := rfl

/-- Helper for Theorem 15.43: the real-part gap between the centered quadratic kernel at `1` and
its value at `0` is the explicit nonnegative function vanishing only at the origin. -/
private def centeredQuadraticCharFunKernelReGap : ℝ → ℝ :=
  fun x ↦ (centeredQuadraticCharFunKernel 1 x).re - (centeredQuadraticCharFunKernel 1 0).re

/-- Helper for Theorem 15.43: the real-part kernel gap vanishes at `0`. -/
private lemma centeredQuadraticCharFunKernelReGap_apply_zero :
    centeredQuadraticCharFunKernelReGap 0 = 0 := by
  -- Proof comment: the gap compares the kernel with itself at the origin.
  simp [centeredQuadraticCharFunKernelReGap]

/-- Helper for Theorem 15.43: away from `0`, the real-part kernel gap is the explicit scalar
function `(cos x - 1) / x^2 + 1/2`. -/
private lemma centeredQuadraticCharFunKernelReGap_apply_ne_zero
    {x : ℝ} (hx : x ≠ 0) :
    centeredQuadraticCharFunKernelReGap x = (Real.cos x - 1) / x ^ (2 : ℕ) + 1 / 2 := by
  -- Route correction: the real-part gap is read directly from the explicit nonzero kernel formula,
  -- not from the Taylor remainder used for continuity at the origin.
  have hxpow : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
  have hpowC : ((x : ℂ) ^ (2 : ℕ)) = ((x ^ (2 : ℕ) : ℝ) : ℂ) := by
    simp
  have hExpRe : (Complex.exp (((x : ℝ) : ℂ) * Complex.I)).re = Real.cos x := by
    simpa using Complex.exp_ofReal_mul_I_re x
  have hQuotient :
      (((Complex.exp (((x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (x : ℝ)) /
          (((x : ℂ) ^ (2 : ℕ)))).re) = (Real.cos x - 1) / x ^ (2 : ℕ) := by
    have hNumRe :
        (Complex.exp (((x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (x : ℝ)).re =
          Real.cos x - 1 := by
      rw [Complex.sub_re, Complex.sub_re]
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, hExpRe]
    rw [hpowC, Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im, hNumRe]
    simp
    field_simp [hxpow]
  calc
    centeredQuadraticCharFunKernelReGap x =
        (((Complex.exp (((x : ℝ) : ℂ) * Complex.I) - 1 - Complex.I * (x : ℝ)) /
            (((x : ℂ) ^ (2 : ℕ)))).re) - (-(1 ^ (2 : ℕ) / 2 : ℝ)) := by
              simp [centeredQuadraticCharFunKernelReGap,
                centeredQuadraticCharFunKernel_apply_ne_zero (t := 1) (x := x) hx,
                centeredQuadraticCharFunKernel_apply_zero]
    _ = (Real.cos x - 1) / x ^ (2 : ℕ) + 1 / 2 := by
          rw [hQuotient]
          norm_num

/-- Helper for Theorem 15.43: the real-part kernel gap is nonnegative everywhere. -/
private lemma centeredQuadraticCharFunKernelReGap_nonneg
    (x : ℝ) :
    0 ≤ centeredQuadraticCharFunKernelReGap x := by
  by_cases hx : x = 0
  · -- Proof comment: at the origin the gap vanishes exactly.
    rw [hx, centeredQuadraticCharFunKernelReGap_apply_zero]
  · rw [centeredQuadraticCharFunKernelReGap_apply_ne_zero hx]
    have hnum : 0 ≤ Real.cos x - 1 + x ^ (2 : ℕ) / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := x)]
    have hxpow_nonneg : 0 ≤ x ^ (2 : ℕ) := by positivity
    -- Proof comment: the explicit formula is a positive denominator times the nonnegative
    -- remainder from the cosine quadratic lower bound.
    calc
      0 ≤ (Real.cos x - 1 + x ^ (2 : ℕ) / 2) / x ^ (2 : ℕ) := by
            exact div_nonneg hnum hxpow_nonneg
      _ = (Real.cos x - 1) / x ^ (2 : ℕ) + 1 / 2 := by
            have hxpow : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
            field_simp [hxpow]

/-- Helper for Theorem 15.43: the real-part kernel gap is strictly positive away from `0`. -/
private lemma centeredQuadraticCharFunKernelReGap_pos
    {x : ℝ} (hx : x ≠ 0) :
    0 < centeredQuadraticCharFunKernelReGap x := by
  rw [centeredQuadraticCharFunKernelReGap_apply_ne_zero hx]
  have hnum : 0 < Real.cos x - 1 + x ^ (2 : ℕ) / 2 := by
    linarith [Real.one_sub_sq_div_two_lt_cos (x := x) hx]
  have hxpow_pos : 0 < x ^ (2 : ℕ) := by positivity
  -- Proof comment: strict positivity comes from the strict cosine remainder bound away from `0`.
  calc
    0 < (Real.cos x - 1 + x ^ (2 : ℕ) / 2) / x ^ (2 : ℕ) := by
          exact div_pos hnum hxpow_pos
    _ = (Real.cos x - 1) / x ^ (2 : ℕ) + 1 / 2 := by
          have hxpow : x ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hx
          field_simp [hxpow]

/-- Helper for Theorem 15.43: the real-part kernel gap inherits continuity from the complex
kernel. -/
private lemma continuous_centeredQuadraticCharFunKernelReGap :
    Continuous centeredQuadraticCharFunKernelReGap := by
  -- Proof comment: the gap is just the real part of the continuous complex kernel minus a
  -- constant value at the origin.
  simpa [centeredQuadraticCharFunKernelReGap] using
    (Complex.continuous_re.comp (continuous_centeredQuadraticCharFunKernel (t := 1))).sub
      continuous_const

/-- Helper for Theorem 15.43: the real-part kernel gap has uniformly bounded oscillation. -/
private lemma centeredQuadraticCharFunKernelReGap_dist_bound :
    ∃ C : ℝ, ∀ x y : ℝ, dist (centeredQuadraticCharFunKernelReGap x)
      (centeredQuadraticCharFunKernelReGap y) ≤ C := by
  obtain ⟨C, hC⟩ :=
    Metric.isBounded_range_iff.1 (isBounded_range_centeredQuadraticCharFunKernel (t := 1))
  have hGapBound : ∀ x : ℝ, |centeredQuadraticCharFunKernelReGap x| ≤ C := by
    intro x
    calc
      |centeredQuadraticCharFunKernelReGap x| =
          |((centeredQuadraticCharFunKernel 1 x - centeredQuadraticCharFunKernel 1 0).re)| := by
            simp [centeredQuadraticCharFunKernelReGap, Complex.sub_re]
      _ ≤ ‖centeredQuadraticCharFunKernel 1 x - centeredQuadraticCharFunKernel 1 0‖ := by
            simpa using
              (Complex.abs_re_le_norm
                (centeredQuadraticCharFunKernel 1 x - centeredQuadraticCharFunKernel 1 0))
      _ = dist (centeredQuadraticCharFunKernel 1 x) (centeredQuadraticCharFunKernel 1 0) := by
            simp [dist_eq_norm]
      _ ≤ C := hC x 0
  refine ⟨2 * C, ?_⟩
  intro x y
  calc
    dist (centeredQuadraticCharFunKernelReGap x) (centeredQuadraticCharFunKernelReGap y) =
        |centeredQuadraticCharFunKernelReGap x - centeredQuadraticCharFunKernelReGap y| := by
          simp [Real.dist_eq]
    _ ≤ |centeredQuadraticCharFunKernelReGap x| + |centeredQuadraticCharFunKernelReGap y| := by
          simpa [sub_eq_add_neg] using
            (abs_sub_le (centeredQuadraticCharFunKernelReGap x) 0
              (centeredQuadraticCharFunKernelReGap y))
    _ ≤ C + C := by
          gcongr <;> exact hGapBound _
    _ = 2 * C := by ring

/-- Helper for Theorem 15.43: the real-part kernel gap is a bounded continuous test function on
`ℝ`. -/
private def centeredQuadraticCharFunKernelReGapBCF : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨centeredQuadraticCharFunKernelReGap, continuous_centeredQuadraticCharFunKernelReGap⟩
    (centeredQuadraticCharFunKernelReGap_dist_bound.choose)
    (centeredQuadraticCharFunKernelReGap_dist_bound.choose_spec)

/-- Helper for Theorem 15.43: every tail `{x | ε < |x|}` sees a uniform positive lower bound for
the real-part kernel gap. -/
private lemma centeredQuadraticCharFunKernelReGap_pos_on_tail
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ x : ℝ, ε < |x| → c ≤ centeredQuadraticCharFunKernelReGap x := by
  let R : ℝ := max ε 4
  have hRgeε : ε ≤ R := le_max_left ε 4
  have hRge4 : (4 : ℝ) ≤ R := le_max_right ε 4
  have hCont : Continuous centeredQuadraticCharFunKernelReGap :=
    continuous_centeredQuadraticCharFunKernelReGap
  obtain ⟨xPos, hxPosMem, hxPosMin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc ε R)).exists_isMinOn
      ⟨ε, by simp [R, hRgeε]⟩
      hCont.continuousOn
  obtain ⟨xNeg, hxNegMem, hxNegMin⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (-R) (-ε))).exists_isMinOn
      ⟨-ε, by simp [R, hRgeε]⟩
      hCont.continuousOn
  have hPosLower :
      ∀ x ∈ Set.Icc ε R,
        centeredQuadraticCharFunKernelReGap xPos ≤ centeredQuadraticCharFunKernelReGap x := by
    intro x hx
    exact hxPosMin hx
  have hNegLower :
      ∀ x ∈ Set.Icc (-R) (-ε),
        centeredQuadraticCharFunKernelReGap xNeg ≤ centeredQuadraticCharFunKernelReGap x := by
    intro x hx
    exact hxNegMin hx
  have hPosPos : 0 < centeredQuadraticCharFunKernelReGap xPos := by
    have hxPosNe : xPos ≠ 0 := by
      linarith [hε, hxPosMem.1]
    exact centeredQuadraticCharFunKernelReGap_pos hxPosNe
  have hNegPos : 0 < centeredQuadraticCharFunKernelReGap xNeg := by
    have hxNegNe : xNeg ≠ 0 := by
      linarith [hε, hxNegMem.2]
    exact centeredQuadraticCharFunKernelReGap_pos hxNegNe
  let c : ℝ := min (centeredQuadraticCharFunKernelReGap xPos)
    (min (centeredQuadraticCharFunKernelReGap xNeg) (1 / 8 : ℝ))
  have hc : 0 < c := by
    dsimp [c]
    refine lt_min hPosPos ?_
    refine lt_min hNegPos ?_
    norm_num
  refine ⟨c, hc, ?_⟩
  intro x hxTail
  by_cases hFar : R < |x|
  · have hAbsPos : 0 < |x| := lt_trans (lt_of_lt_of_le (by norm_num) hRge4) hFar
    have hx0 : x ≠ 0 := abs_pos.mp hAbsPos
    have hsqPos : 0 < x ^ (2 : ℕ) := by positivity
    have hsqGe : (16 : ℝ) ≤ x ^ (2 : ℕ) := by
      have hAbsGe : (4 : ℝ) ≤ |x| := le_trans hRge4 (le_of_lt hFar)
      nlinarith [sq_abs x, hAbsGe]
    have hInv : (1 : ℝ) / x ^ (2 : ℕ) ≤ 1 / 16 := by
      exact one_div_le_one_div_of_le (by norm_num : 0 < (16 : ℝ)) hsqGe
    have hTwoDiv : (2 : ℝ) / x ^ (2 : ℕ) ≤ 1 / 8 := by
      calc
        (2 : ℝ) / x ^ (2 : ℕ) = 2 * ((1 : ℝ) / x ^ (2 : ℕ)) := by
          field_simp [hx0, hx0, hx0, hx0]
        _ ≤ 2 * (1 / 16) := by
          gcongr
        _ = 1 / 8 := by norm_num
    have hCosLower : (-2 : ℝ) ≤ Real.cos x - 1 := by
      linarith [Real.neg_one_le_cos x]
    have hDivLower : (-2 : ℝ) / x ^ (2 : ℕ) ≤ (Real.cos x - 1) / x ^ (2 : ℕ) := by
      exact div_le_div_of_nonneg_right hCosLower hsqPos.le
    have hGapLower : -(1 / 8 : ℝ) ≤ (Real.cos x - 1) / x ^ (2 : ℕ) := by
      have hAux : -(1 / 8 : ℝ) ≤ (-2 : ℝ) / x ^ (2 : ℕ) := by
        simpa [neg_div] using neg_le_neg hTwoDiv
      exact le_trans hAux hDivLower
    have hcLe : c ≤ (1 / 8 : ℝ) := by
      dsimp [c]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
    -- Proof comment: far from the origin, the explicit gap formula has the uniform bound
    -- `gap(x) ≥ 1 / 2 - 2 / x^2 ≥ 1 / 8`.
    calc
      c ≤ (1 / 8 : ℝ) := hcLe
      _ ≤ centeredQuadraticCharFunKernelReGap x := by
        rw [centeredQuadraticCharFunKernelReGap_apply_ne_zero hx0]
        linarith
  · have hAbsLe : |x| ≤ R := le_of_not_gt hFar
    by_cases hxNonneg : 0 ≤ x
    · have hxMem : x ∈ Set.Icc ε R := by
        constructor
        · have : ε < x := by simpa [abs_of_nonneg hxNonneg] using hxTail
          linarith
        · simpa [abs_of_nonneg hxNonneg] using hAbsLe
      have hcLe : c ≤ centeredQuadraticCharFunKernelReGap xPos := by
        dsimp [c]
        exact min_le_left _ _
      exact le_trans hcLe (hPosLower x hxMem)
    · have hxNeg : x < 0 := lt_of_not_ge hxNonneg
      have hxMem : x ∈ Set.Icc (-R) (-ε) := by
        constructor
        · have : -x ≤ R := by simpa [abs_of_neg hxNeg] using hAbsLe
          linarith
        · have : ε < -x := by simpa [abs_of_neg hxNeg] using hxTail
          linarith
      have hcLe : c ≤ centeredQuadraticCharFunKernelReGap xNeg := by
        dsimp [c]
        exact le_trans (min_le_right _ _) (min_le_left _ _)
      exact le_trans hcLe (hNegLower x hxMem)

/-- Helper for Theorem 15.43: integrating the real-part kernel gap is the same as taking the
real part of the complex kernel integral and adding back the origin value `1 / 2`. -/
private lemma integral_centeredQuadraticCharFunKernelReGapBCF_eq_re_kernelIntegral_add_half
    (n : ℕ) :
    ∫ x, centeredQuadraticCharFunKernelReGapBCF x
      ∂(A.varianceWeightedRowLaw μ n : Measure ℝ) =
      (∫ x, centeredQuadraticCharFunKernelBCF 1 x
        ∂(A.varianceWeightedRowLaw μ n : Measure ℝ)).re + 1 / 2 := by
  let ν : Measure ℝ := (A.varianceWeightedRowLaw μ n : Measure ℝ)
  have hKernelInt :
      Integrable (fun x : ℝ ↦ centeredQuadraticCharFunKernelBCF 1 x) ν :=
    BoundedContinuousFunction.integrable (μ := ν) (centeredQuadraticCharFunKernelBCF 1)
  have hReInt :
      Integrable (fun x : ℝ ↦ (centeredQuadraticCharFunKernelBCF 1 x : ℂ).re) ν :=
    hKernelInt.re
  -- Proof comment: convert the real-valued gap back into the real part of the complex kernel, then
  -- move `re` through the integral and use the explicit origin value `-1/2`.
  change ∫ x, centeredQuadraticCharFunKernelReGap x ∂ν =
    (∫ x, centeredQuadraticCharFunKernelBCF 1 x ∂ν).re + 1 / 2
  calc
    ∫ x, centeredQuadraticCharFunKernelReGap x ∂ν =
        ∫ x, ((centeredQuadraticCharFunKernelBCF 1 x : ℂ).re -
          (centeredQuadraticCharFunKernel 1 0).re) ∂ν := by
            simp [centeredQuadraticCharFunKernelReGap]
    _ = ∫ x, (centeredQuadraticCharFunKernelBCF 1 x : ℂ).re ∂ν -
          ∫ x, (centeredQuadraticCharFunKernel 1 0).re ∂ν := by
            rw [integral_sub hReInt (integrable_const _)]
    _ = ∫ x, (centeredQuadraticCharFunKernelBCF 1 x : ℂ).re ∂ν -
          (centeredQuadraticCharFunKernel 1 0).re := by
            rw [integral_const]
            simp [ν, varianceWeightedRowMeasure_real_univ (A := A) (μ := μ) n]
    _ = (∫ x, centeredQuadraticCharFunKernelBCF 1 x ∂ν).re -
          (centeredQuadraticCharFunKernel 1 0).re := by
            congr 1
            exact integral_re hKernelInt
    _ = (∫ x, centeredQuadraticCharFunKernelBCF 1 x ∂ν).re + 1 / 2 := by
          simp [centeredQuadraticCharFunKernel_apply_zero]

/-- Helper for Theorem 15.43: a uniform positive lower bound for the real-part kernel gap on a
tail set forces the corresponding tail mass to be bounded by the full gap integral. -/
private lemma tailMeasure_le_gapIntegral
    {ε c : ℝ}
    (hcTail : ∀ x : ℝ, ε < |x| → c ≤ centeredQuadraticCharFunKernelReGap x)
    (n : ℕ) :
    c * (A.varianceWeightedRowLaw μ n : Measure ℝ).real {x | ε < |x|} ≤
      ∫ x, centeredQuadraticCharFunKernelReGapBCF x
        ∂(A.varianceWeightedRowLaw μ n : Measure ℝ) := by
  let ν : Measure ℝ := (A.varianceWeightedRowLaw μ n : Measure ℝ)
  let s : Set ℝ := {x | ε < |x|}
  have hs : MeasurableSet s := by
    exact measurableSet_lt measurable_const measurable_abs
  have hLeftInt : Integrable (s.indicator fun _ : ℝ ↦ c) ν := by
    exact (integrable_const c).indicator hs
  have hRightInt : Integrable centeredQuadraticCharFunKernelReGap ν := by
    exact BoundedContinuousFunction.integrable (μ := ν) centeredQuadraticCharFunKernelReGapBCF
  have hPointwise :
      ∀ᵐ x ∂ν, s.indicator (fun _ : ℝ ↦ c) x ≤ centeredQuadraticCharFunKernelReGap x := by
    refine Filter.Eventually.of_forall fun x ↦ ?_
    by_cases hx : x ∈ s
    · exact by simpa [s, hx] using hcTail x hx
    · simp [s, hx, centeredQuadraticCharFunKernelReGap_nonneg]
  have hMono :
      ∫ x, s.indicator (fun _ : ℝ ↦ c) x ∂ν ≤
        ∫ x, centeredQuadraticCharFunKernelReGap x ∂ν := by
    exact integral_mono_ae hLeftInt hRightInt hPointwise
  -- Proof comment: compare the tail indicator against the nonnegative gap pointwise, then rewrite
  -- the indicator integral back as the tail mass multiplied by the uniform lower bound `c`.
  calc
    c * ν.real s = ∫ x, s.indicator (fun _ : ℝ ↦ c) x ∂ν := by
          rw [mul_comm]
          symm
          simpa [s, smul_eq_mul] using integral_indicator_const c hs
    _ ≤ ∫ x, centeredQuadraticCharFunKernelReGap x ∂ν := hMono
    _ = ∫ x, centeredQuadraticCharFunKernelReGapBCF x ∂ν := rfl

/-- Helper for Theorem 15.43: a single-frequency middle-object limit at `t = 1` already forces
the tails of the variance-weighted row laws to vanish outside every neighborhood of `0`. -/
private lemma varianceWeightedRowLaw_tail_tendsto_zero_of_sumEntryCharFunSubOne_at_one
    (hSum1 :
      Tendsto
        (fun n ↦ ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) (1 : ℝ) - 1))
        atTop
        (𝓝 ((-(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ))))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto
      (fun n ↦ (A.varianceWeightedRowLaw μ n : Measure ℝ).real {x | ε < |x|})
      atTop
      (𝓝 0) := by
  obtain ⟨c, hc, hcTail⟩ :=
    centeredQuadraticCharFunKernelReGap_pos_on_tail hε
  have hKernel :
      Tendsto
        (fun n ↦
          ∫ x, centeredQuadraticCharFunKernelBCF 1 x
            ∂(A.varianceWeightedRowLaw μ n : Measure ℝ))
        atTop
        (𝓝 ((-(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
    have hEq :
        (fun n ↦
          ∫ x, centeredQuadraticCharFunKernelBCF 1 x
            ∂(A.varianceWeightedRowLaw μ n : Measure ℝ)) =
          (fun n ↦
            ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) (1 : ℝ) - 1)) := by
      funext n
      symm
      exact
        sumEntryCharFunSubOne_eq_integral_centeredQuadraticCharFunKernelBCF_varianceWeightedRowLaw
          (A := A) (μ := μ) (t := 1) n
    rw [hEq]
    exact hSum1
  have hGapIntegral :
      Tendsto
        (fun n ↦
          ∫ x, centeredQuadraticCharFunKernelReGapBCF x
            ∂(A.varianceWeightedRowLaw μ n : Measure ℝ))
        atTop
        (𝓝 0) := by
    have hRe :
        Tendsto
          (fun n ↦
            (∫ x, centeredQuadraticCharFunKernelBCF 1 x
              ∂(A.varianceWeightedRowLaw μ n : Measure ℝ)).re)
          atTop
          (𝓝 (((-(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ)).re)) :=
      Complex.continuous_re.continuousAt.tendsto.comp hKernel
    have hEq :
        (fun n ↦
          ∫ x, centeredQuadraticCharFunKernelReGapBCF x
            ∂(A.varianceWeightedRowLaw μ n : Measure ℝ)) =
          (fun n ↦
            (∫ x, centeredQuadraticCharFunKernelBCF 1 x
              ∂(A.varianceWeightedRowLaw μ n : Measure ℝ)).re + 1 / 2) := by
      funext n
      simpa using
        integral_centeredQuadraticCharFunKernelReGapBCF_eq_re_kernelIntegral_add_half
          (A := A) (μ := μ) n
    rw [hEq]
    have hAdd :
        Tendsto
          (fun n ↦
            (∫ x, centeredQuadraticCharFunKernelBCF 1 x
              ∂(A.varianceWeightedRowLaw μ n : Measure ℝ)).re + 1 / 2)
          atTop
          (𝓝 (((( -(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ)).re) + 1 / 2)) :=
      hRe.add tendsto_const_nhds
    simpa using hAdd
  have hScaled :
      Tendsto
        (fun n ↦ c * (A.varianceWeightedRowLaw μ n : Measure ℝ).real {x | ε < |x|})
        atTop
        (𝓝 0) := by
    refine
      tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hGapIntegral ?_ ?_
    · intro n
      positivity
    · intro n
      exact tailMeasure_le_gapIntegral (A := A) (μ := μ) hcTail n
  -- Proof comment: once the gap integral tends to `0`, the positive tail lower bound turns the
  -- weighted-row tail mass into a squeezed scalar multiple that also tends to `0`.
  simpa [hc.ne', mul_assoc, mul_left_comm, mul_comm] using hScaled.const_mul c⁻¹

/-- Helper for Theorem 15.43: once the single-frequency kernel gap drives every weighted-row tail
to `0`, the weighted-row laws converge weakly to `δ₀`. -/
private lemma varianceWeightedRowLaw_tendsto_diracZero_of_sumEntryCharFunSubOne_at_one
    (hSum1 :
      Tendsto
        (fun n ↦ ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) (1 : ℝ) - 1))
        atTop
        (𝓝 ((-(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ)))) :
    Tendsto (fun n ↦ A.varianceWeightedRowLaw μ n) atTop (𝓝 (diracProba (0 : ℝ))) := by
  -- Proof comment: the single-frequency tail-collapse lemma already gives the tail criterion from
  -- which the generic bounded-continuous test-function argument identifies the weak limit as `δ₀`.
  refine tendsto_diracProba_zero_of_tail_tendsto_zero ?_
  intro ε hε
  exact
    varianceWeightedRowLaw_tail_tendsto_zero_of_sumEntryCharFunSubOne_at_one
      (A := A) (μ := μ) hSum1 hε

/-- Helper for Theorem 15.43: the Lindeberg condition implies both the null-array property and
weak convergence of the row-sum laws to `𝒩(0, 1)`. -/
private lemma satisfiesLindebergCondition_imp_isNull_and_rowSumLaw_tendsto_gaussian
    (hLindeberg : A.SatisfiesLindebergCondition μ) :
    A.IsNull μ ∧
      Tendsto (A.rowSumLaw μ) atTop
        (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) := by
  have hNull : A.IsNull μ :=
    isNull_of_satisfiesLindebergCondition (A := A) (μ := μ) hLindeberg
  have hWeighted :
      Tendsto (fun n ↦ A.varianceWeightedRowLaw μ n) atTop (𝓝 (diracProba (0 : ℝ))) :=
    varianceWeightedRowLaw_tendsto_diracZero_of_satisfiesLindebergCondition
      (A := A) (μ := μ) hLindeberg
  refine ⟨hNull, ?_⟩
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  let s : ℕ → ℂ := fun n ↦
    ∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) t)
  let u : ℕ → ℂ := fun n ↦
    ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) t - 1)
  have hMiddle :
      Tendsto u atTop (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
    simpa [u] using
      sumEntryCharFunSubOne_tendsto_gaussianExponent_of_varianceWeightedRowLaw
        (A := A) (μ := μ) t hWeighted
  have hDiffZero :
      Tendsto (fun n ↦ s n - u n) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simpa [s, u] using
      sumLogEntryCharFun_sub_sumEntryCharFunSubOne_tendstoZero_of_isNull
        (A := A) (μ := μ) hNull t
  have hSumLogs :
      Tendsto s atTop (𝓝 ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
    have hsdecomp : s = fun n ↦ (s n - u n) + u n := by
      funext n
      exact (sub_add_cancel (s n) (u n)).symm
    rw [hsdecomp]
    simpa using hDiffZero.add hMiddle
  have hExp :
      Tendsto (fun n ↦ Complex.exp (s n)) atTop
        (𝓝 (Complex.exp ((-(t ^ (2 : ℕ) / 2 : ℝ) : ℂ)))) := by
    exact Complex.continuous_exp.continuousAt.tendsto.comp hSumLogs
  have hBridge :
      (fun n ↦ charFun (A.rowSumLaw μ n : Measure ℝ) t) =ᶠ[atTop]
        fun n ↦ Complex.exp (s n) :=
    rowSumCharFun_eq_exp_sumLog_eventually_of_isNull (A := A) (μ := μ) hNull t
  -- Proof comment: the forward implication combines the middle-object limit with the logarithmic
  -- linearization remainder and the row-level exponential bridge.
  simpa [s, ProbabilityTheory.charFun_gaussianReal, neg_div] using hExp.congr' hBridge.symm

/-- Helper for Theorem 15.43: the null-array condition together with Gaussian weak convergence of
the row sums implies the Lindeberg condition. -/
private lemma isNull_and_rowSumLaw_tendsto_gaussian_imp_satisfiesLindebergCondition
    (hConclusion :
      A.IsNull μ ∧
        Tendsto (A.rowSumLaw μ) atTop
          (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)))) :
    A.SatisfiesLindebergCondition μ := by
  rcases hConclusion with ⟨hNull, hGaussian⟩
  let s : ℕ → ℂ := fun n ↦
    ∑ i : Fin (A.rowLength n), Complex.log (charFun (μ.map (A n i)) (1 : ℝ))
  let u : ℕ → ℂ := fun n ↦
    ∑ i : Fin (A.rowLength n), (charFun (μ.map (A n i)) (1 : ℝ) - 1)
  have hRowChar :
      Tendsto
        (fun n ↦ charFun (A.rowSumLaw μ n : Measure ℝ) (1 : ℝ))
        atTop
        (𝓝 (Complex.exp ((-(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ)))) :=
    rowSumLaw_charFun_tendsto_gaussian (A := A) (μ := μ) hGaussian (1 : ℝ)
  have hMem :
      Complex.exp ((-(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ)) ∈ Complex.slitPlane := by
    simpa using
      (Complex.ofReal_mem_slitPlane.2
        (Real.exp_pos (-(1 ^ (2 : ℕ) / 2 : ℝ))))
  have hLogEval :
      Complex.log (Complex.exp (-(1 ^ (2 : ℕ) / 2 : ℝ))) =
        ((-(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
    calc
      Complex.log (Complex.exp (-(1 ^ (2 : ℕ) / 2 : ℝ))) =
          Complex.log (((Real.exp (-(1 ^ (2 : ℕ) / 2 : ℝ))) : ℝ) : ℂ) := by
            simp
      _ = (((Real.exp (-(1 ^ (2 : ℕ) / 2 : ℝ))).log : ℝ) : ℂ) := by
            symm
            exact Complex.ofReal_log (show 0 ≤ Real.exp (-(1 ^ (2 : ℕ) / 2 : ℝ)) by positivity)
      _ = ((-(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ)) := by
            simp
  have hRowLog :
      Tendsto
        (fun n ↦ Complex.log (charFun (A.rowSumLaw μ n : Measure ℝ) (1 : ℝ)))
        atTop
        (𝓝 ((-(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
    rw [← hLogEval]
    exact hRowChar.clog hMem
  have hSumLogs :
      Tendsto s atTop (𝓝 ((-(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
    exact
      hRowLog.congr'
        (rowSumLawLog_eq_sumLogEntryCharFun_eventually_at_one_of_isNull
          (A := A) (μ := μ) hNull)
  have hDiffZero :
      Tendsto (fun n ↦ s n - u n) atTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    simpa [s, u] using
      sumLogEntryCharFun_sub_sumEntryCharFunSubOne_tendstoZero_of_isNull
        (A := A) (μ := μ) hNull (1 : ℝ)
  have hSum1 :
      Tendsto u atTop (𝓝 ((-(1 ^ (2 : ℕ) / 2 : ℝ) : ℂ))) := by
    have huEq : u = fun n ↦ s n - (s n - u n) := by
      funext n
      exact (sub_sub_cancel (s n) (u n)).symm
    rw [huEq]
    simpa using hSumLogs.sub hDiffZero
  refine (satisfiesLindebergCondition_iff (A := A) (μ := μ)).2 ?_
  intro ε hε
  have hTail :
      Tendsto
        (fun n ↦ (A.varianceWeightedRowLaw μ n : Measure ℝ).real {x | ε < |x|})
        atTop
        (𝓝 0) :=
    varianceWeightedRowLaw_tail_tendsto_zero_of_sumEntryCharFunSubOne_at_one
      (A := A) (μ := μ) hSum1 hε
  have hEq :
      (fun n ↦ (A.varianceWeightedRowLaw μ n : Measure ℝ).real {x | ε < |x|}) =
        (fun n ↦
          ∑ i : Fin (A.rowLength n),
            ∫ ω, Set.indicator {ω | ε < |A n i ω|} (fun ω ↦ (A n i ω) ^ 2) ω ∂μ) := by
    funext n
    exact varianceWeightedRowLaw_tail_eq (A := A) (μ := μ) ε n
  rw [hEq] at hTail
  exact hTail

-- Proof sketch: for `(i) → (ii)`, apply the Lindeberg--Feller characteristic-function argument to
-- the independent centered normed row sums to obtain convergence in distribution to the standard
-- Gaussian, and use the same truncation estimates to deduce the null-array property. For
-- `(ii) → (i)`, combine weak convergence of the laws of the row sums with the null-array
-- hypothesis and the preceding truncation criterion to recover the canonical Lindeberg condition.
/-- Theorem 15.43: for an independent centered and normed array of real random variables, the
Lindeberg condition is equivalent to saying that the array is null and that the laws of the row
sums converge weakly to the standard Gaussian law `𝒩(0, 1)`. -/
theorem lindeberg_feller_central_limit_theorem
    :
    A.SatisfiesLindebergCondition μ ↔
      A.IsNull μ ∧
        Tendsto (A.rowSumLaw μ) atTop
          (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) := by
  constructor
  · intro hLindeberg
    exact
      satisfiesLindebergCondition_imp_isNull_and_rowSumLaw_tendsto_gaussian
        (A := A) (μ := μ) hLindeberg
  · intro hConclusion
    exact
      isNull_and_rowSumLaw_tendsto_gaussian_imp_satisfiesLindebergCondition
        (A := A) (μ := μ) hConclusion

end

end RealRandomVariableArray
