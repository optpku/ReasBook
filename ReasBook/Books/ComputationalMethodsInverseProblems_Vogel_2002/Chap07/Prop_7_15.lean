/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Objective
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.OptimalIndex
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Lemma_7_14
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.SingularSystem
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace TsvdEstimation

universe u v w

section Proposition

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
variable (K : ℕ → H →L[ℝ] F)
variable (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
variable (h_length : ∀ n, (S n).length = ⊤)
variable (fTrue : H) (b c p q σ : ℝ)
variable (η : ℕ → Ω → F)
variable (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
variable (n mStar : ℕ)
variable (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
variable (h_noise_memLp : ∀ k, MeasureTheory.MemLp (η k) 2 μ)
variable (h_noise_meanZero : ∀ k, ∫ ω, η k ω ∂μ = 0)
variable
  (h_noise_modeVariance :
    ∀ k i,
      ∫ ω,
        (inner ℝ ((S k).leftBasis ((S k).natIndex (h_length k) i) : F) (η k ω)) ^ 2 ∂μ =
          σ ^ 2 / (k : ℝ))
variable
  (h_singularDecay :
    ∀ k, (S k).HasAlgebraicSingularValueSquareDecay (h_length k) c p)
variable
  (h_fourierDecay :
    ∀ k, (S k).HasAlgebraicFourierCoefficientSquareDecay (h_length k) fTrue b q)
variable (h_tsvd : IsTsvdReconstructionFamily K S h_length Rtsvd)
variable
  (h_min :
    IsMinOn
      (expectedSqErrorObjective μ K Rtsvd fTrue η n)
      (admissibleIndexSet n)
      mStar)
  (hm_pos : 0 < mStar)
  (hm_lt : mStar < n)

include h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd h_min hm_pos hm_lt

/-- Helper for Proposition 7.15: truncating TSVD from `m - 1` to `m` adds
exactly the new singular mode. -/
theorem tsvdReconstructionStep_apply
    {m : ℕ} (hm : 0 < m) (g : F) :
    Rtsvd n m g =
      Rtsvd n (m - 1) g +
        (((1 / (S n).singularValue ((S n).natIndex (h_length n) (m - 1))) *
            inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) g) •
          ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H)) := by
  -- Expand the `m`-mode truncation as the predecessor block plus its last term.
  rw [h_tsvd n m g, ← Nat.succ_pred_eq_of_pos hm, Finset.sum_range_succ]
  simpa using (h_tsvd n (m - 1) g).symm

/-- Helper for Proposition 7.15: the predecessor TSVD truncation has zero
coefficient in the newly added singular mode. -/
theorem inner_stepMode_reconstructionPrev_eq_zero
    {m : ℕ} (hm : 0 < m) (g : F) :
    inner ℝ
      ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H)
      (Rtsvd n (m - 1) g) = 0 := by
  -- Expand the predecessor truncation and kill each summand by orthogonality.
  rw [h_tsvd n (m - 1) g, inner_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hi_lt : i < m - 1 := Finset.mem_range.mp hi
  have hij :
      (S n).natIndex (h_length n) (m - 1) ≠ (S n).natIndex (h_length n) i := by
    intro hEq
    exact (ne_of_lt ((S n).natIndex_strictMono (h_length n) hi_lt)) hEq.symm
  have horth :
      inner ℝ
        ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H)
        ((S n).rightBasis ((S n).natIndex (h_length n) i) : H) = 0 := by
    simpa using (S n).rightBasis.orthonormal.2 hij
  rw [inner_smul_right, horth]
  simp

/-- Helper for Proposition 7.15: the new TSVD mode recovers the true-signal
coefficient from the exact datum `K n fTrue`. -/
theorem stepMode_signalCoefficient_eq
    {m : ℕ} (hm : 0 < m) :
    (1 / (S n).singularValue ((S n).natIndex (h_length n) (m - 1))) *
        inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) ((K n) fTrue) =
      inner ℝ ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H) fTrue := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  have hs_ne : (S n).singularValue j ≠ 0 := ne_of_gt ((S n).singularValue_pos j)
  have hcoeff :
      inner ℝ ((S n).leftBasis j : F) ((K n) fTrue) =
        (S n).singularValue j * inner ℝ ((S n).rightBasis j : H) fTrue := by
    -- Move `K n` across the inner product and use the singular-system axiom.
    rw [← ContinuousLinearMap.adjoint_inner_left (K n) fTrue ((S n).leftBasis j : F),
      (S n).adjoint_map_left j, real_inner_smul_left]
    simp
  have hmain :
      (1 / (S n).singularValue j) * inner ℝ ((S n).leftBasis j : F) ((K n) fTrue) =
        inner ℝ ((S n).rightBasis j : H) fTrue := by
    rw [hcoeff]
    field_simp [hs_ne]
  simpa [j] using hmain

/-- Helper for Proposition 7.15: the predecessor TSVD error carries exactly the
negative true-signal coefficient in the next singular mode. -/
theorem previousError_stepModeCoefficient_eq_negSignal
    {m : ℕ} (hm : 0 < m) (ω : Ω) :
    inner ℝ ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H)
      (FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω)) =
      -inner ℝ ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H) fTrue := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  let u : H := ((S n).rightBasis j : H)
  have hprev_zero :
      inner ℝ u (Rtsvd n (m - 1) ((K n) fTrue + η n ω)) = 0 := by
    -- The predecessor truncation never contains the newly added singular mode.
    simpa [j, u] using
      (inner_stepMode_reconstructionPrev_eq_zero
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
        (Rtsvd := Rtsvd) (n := n) (m := m) (mStar := mStar)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
        hm ((K n) fTrue + η n ω))
  -- Expand the error and use the vanishing predecessor coefficient.
  rw [FilterRegularization.estimationError_def, inner_sub_right, hprev_zero, zero_sub]

/-- Helper for Proposition 7.15: the consecutive TSVD errors differ only in the
current singular mode after extracting one common orthogonal remainder. -/
theorem backwardErrors_commonRemainder
    {m : ℕ} (hm : 0 < m) (ω : Ω) :
    ∃ r : H,
      inner ℝ ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H) r = 0 ∧
      FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω) =
        r +
          (-(inner ℝ ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H) fTrue)) •
            ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H) ∧
      FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω) =
        r +
          (((1 / (S n).singularValue ((S n).natIndex (h_length n) (m - 1))) *
              inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) (η n ω)) •
            ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H)) := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  let u : H := ((S n).rightBasis j : H)
  let v : F := ((S n).leftBasis j : F)
  let a : ℝ := inner ℝ u fTrue
  let ξ : ℝ := (1 / (S n).singularValue j) * inner ℝ v (η n ω)
  let ePrev : H :=
    FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω)
  let r : H := ePrev + a • u
  refine ⟨r, ?_, ?_, ?_⟩
  ·
    have hu_norm : ‖u‖ = 1 := by
      simpa [u] using (S n).rightBasis.orthonormal.norm_eq_one j
    have huu : inner ℝ u u = 1 := by
      rw [real_inner_self_eq_norm_sq, hu_norm]
      norm_num
    -- The common remainder is orthogonal to the new mode by construction.
    calc
      inner ℝ u r = inner ℝ u ePrev + inner ℝ u (a • u) := by
        simp [r, inner_add_right]
      _ = -a + a * inner ℝ u u := by
        rw [previousError_stepModeCoefficient_eq_negSignal
          (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
          (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
          (Rtsvd := Rtsvd) (n := n) (mStar := mStar)
          (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
          (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
          (h_noise_modeVariance := h_noise_modeVariance)
          (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
          (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
          hm ω, inner_smul_right]
      _ = 0 := by rw [huu]; ring
  ·
    -- Repackage the predecessor error around the orthogonal remainder.
    calc
      FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω)
          = ePrev := by rfl
      _ = ePrev + 0 := by simp
      _ = r +
            (-(inner ℝ ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H) fTrue)) •
              ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H) := by
            simp [r, a, u, j, add_assoc]
  ·
    have hcurr :
        FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω) =
          ePrev + (a + ξ) • u := by
      -- Route correction: normalize the one-step TSVD update before touching norms.
      calc
        FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω)
            = Rtsvd n m ((K n) fTrue + η n ω) - fTrue := by
                rw [FilterRegularization.estimationError_def]
        _ = Rtsvd n (m - 1) ((K n) fTrue + η n ω) +
              (((1 / (S n).singularValue j) *
                  inner ℝ v ((K n) fTrue + η n ω)) • u) - fTrue := by
                rw [tsvdReconstructionStep_apply
                  (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
                  (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
                  (Rtsvd := Rtsvd) (n := n) (m := m) (mStar := mStar)
                  (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
                  (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
                  (h_noise_modeVariance := h_noise_modeVariance)
                  (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
                  (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
                  hm ((K n) fTrue + η n ω)]
        _ = ePrev + (((1 / (S n).singularValue j) *
              inner ℝ v ((K n) fTrue + η n ω)) • u) := by
              simp [ePrev, FilterRegularization.estimationError_def, sub_eq_add_neg,
                add_assoc, add_left_comm, add_comm]
        _ = ePrev + (a + ξ) • u := by
              rw [inner_add_right, mul_add, add_smul,
                stepMode_signalCoefficient_eq
                  (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
                  (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
                  (Rtsvd := Rtsvd) (n := n) (mStar := mStar)
                  (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
                  (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
                  (h_noise_modeVariance := h_noise_modeVariance)
                  (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
                  (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
                  hm]
              simpa [a, ξ, u, v, j, add_smul]
    -- Rewrite the current error using the same remainder.
    calc
      FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω)
          = ePrev + (a + ξ) • u := hcurr
      _ = r + ξ • u := by
            simp [r, add_assoc, add_left_comm, add_comm, add_smul]

/-- Helper for Proposition 7.15: pointwise, the backward TSVD error step is a
single deterministic-minus-variance contribution from the newly added mode. -/
theorem backwardErrorStep_pointwise
    {m : ℕ} (hm : 0 < m) (ω : Ω) :
    ‖FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω)‖ ^ 2 -
        ‖FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω)‖ ^ 2 =
      -(inner ℝ ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H) fTrue) ^ 2 +
        ((inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) (η n ω)) ^ 2) /
          ((S n).singularValue ((S n).natIndex (h_length n) (m - 1)) ^ 2) := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  let u : H := ((S n).rightBasis j : H)
  let v : F := ((S n).leftBasis j : F)
  let a : ℝ := inner ℝ u fTrue
  let ξ : ℝ := (1 / (S n).singularValue j) * inner ℝ v (η n ω)
  obtain ⟨r, hr_orth, hPrev, hCurr⟩ :=
    backwardErrors_commonRemainder
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (m := m) (mStar := mStar)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
      hm ω
  have hu_norm : ‖u‖ = 1 := by
    simpa [u] using (S n).rightBasis.orthonormal.norm_eq_one j
  have hScalarNorm (t : ℝ) : ‖t • u‖ ^ 2 = t ^ 2 := by
    -- Unit basis vectors turn scalar multiples into scalar squares.
    rw [norm_smul, hu_norm]
    simp [pow_two, Real.norm_eq_abs]
  have hPrevInner : inner ℝ r ((-a) • u) = 0 := by
    rw [inner_smul_right, real_inner_comm, hr_orth]
    simp
  have hCurrInner : inner ℝ r (ξ • u) = 0 := by
    rw [inner_smul_right, real_inner_comm, hr_orth]
    simp
  have hPrevNorm :
      ‖r + (-a) • u‖ ^ 2 = ‖r‖ ^ 2 + a ^ 2 := by
    calc
      ‖r + (-a) • u‖ ^ 2 = ‖r‖ ^ 2 + ‖(-a) • u‖ ^ 2 := by
        simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero r ((-a) • u) hPrevInner
      _ = ‖r‖ ^ 2 + (-a) ^ 2 := by rw [hScalarNorm (-a)]
      _ = ‖r‖ ^ 2 + a ^ 2 := by ring
  have hCurrNorm :
      ‖r + ξ • u‖ ^ 2 = ‖r‖ ^ 2 + ξ ^ 2 := by
    calc
      ‖r + ξ • u‖ ^ 2 = ‖r‖ ^ 2 + ‖ξ • u‖ ^ 2 := by
        simpa [pow_two] using
          norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero r (ξ • u) hCurrInner
      _ = ‖r‖ ^ 2 + ξ ^ 2 := by rw [hScalarNorm ξ]
  have hs_ne : (S n).singularValue j ≠ 0 := ne_of_gt ((S n).singularValue_pos j)
  -- Route correction: consume the common-remainder interface instead of
  -- reopening both TSVD sums inside the norm computation.
  calc
    ‖FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω)‖ ^ 2 -
        ‖FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω)‖ ^ 2
        = (‖r‖ ^ 2 + ξ ^ 2) - (‖r‖ ^ 2 + a ^ 2) := by rw [hCurr, hPrev, hCurrNorm, hPrevNorm]
    _ = -(a ^ 2) + ξ ^ 2 := by ring
    _ = -(a ^ 2) +
          (((1 / (S n).singularValue j) * inner ℝ v (η n ω)) ^ 2) := by
          simp [ξ]
    _ = -(a ^ 2) +
          ((inner ℝ v (η n ω)) ^ 2) / ((S n).singularValue j ^ 2) := by
          field_simp [hs_ne]
    _ = -(inner ℝ ((S n).rightBasis ((S n).natIndex (h_length n) (m - 1)) : H) fTrue) ^ 2 +
          ((inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) (m - 1)) : F) (η n ω)) ^ 2) /
            ((S n).singularValue ((S n).natIndex (h_length n) (m - 1)) ^ 2) := by
          simp [a, u, v, j]

/-- Helper for Proposition 7.15: the backward TSVD objective step is the
single-mode scalar increment from `(7.59)`. -/
theorem expectedSqErrorObjective_backwardStep_eq
    {m : ℕ} (hm : 0 < m) :
    expectedSqErrorObjective μ K Rtsvd fTrue η n m -
        expectedSqErrorObjective μ K Rtsvd fTrue η n (m - 1) =
      -b * (m : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (m : ℝ) ^ p := by
  let j : (S n).Index := (S n).natIndex (h_length n) (m - 1)
  let u : H := ((S n).rightBasis j : H)
  let v : F := ((S n).leftBasis j : F)
  let a : ℝ := inner ℝ u fTrue
  let s : ℝ := (S n).singularValue j
  have hErrorMemLp (k : ℕ) :
      MeasureTheory.MemLp
        (fun ω ↦ FilterRegularization.estimationError (Rtsvd n k) (K n) fTrue (η n ω)) 2 μ := by
    have hNoiseImage :
        MeasureTheory.MemLp (fun ω ↦ Rtsvd n k (η n ω)) 2 μ := by
      -- The reconstruction applied to the noise is still an `L²` random field.
      simpa using (h_noise_memLp n).continuousLinearMap_comp (Rtsvd n k)
    have hConst :
        MeasureTheory.MemLp (fun _ : Ω ↦ Rtsvd n k ((K n) fTrue) - fTrue) 2 μ := by
      simpa using
        (MeasureTheory.memLp_const
          (α := Ω) (μ := μ) (p := (2 : ENNReal))
          (c := Rtsvd n k ((K n) fTrue) - fTrue))
    -- Rewrite the estimation error as a fixed bias plus the linear noise image.
    convert hConst.add hNoiseImage using 1
    funext ω
    simp [FilterRegularization.estimationError_def, sub_eq_add_neg, add_assoc,
      add_left_comm, add_comm, map_add]
  have hCurrInt :
      MeasureTheory.Integrable
        (fun ω ↦ ‖FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω)‖ ^ 2) μ :=
    MeasureTheory.MemLp.integrable_norm_pow (p := 2) (hErrorMemLp m) (by decide)
  have hPrevInt :
      MeasureTheory.Integrable
        (fun ω ↦ ‖FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω)‖ ^ 2) μ :=
    MeasureTheory.MemLp.integrable_norm_pow (p := 2) (hErrorMemLp (m - 1)) (by decide)
  have hConstInt : MeasureTheory.Integrable (fun _ : Ω ↦ (-(a ^ 2) : ℝ)) μ :=
    MeasureTheory.integrable_const _
  have hNoiseModeLp : MeasureTheory.MemLp (fun ω ↦ inner ℝ v (η n ω)) 2 μ := by
    simpa [v] using MeasureTheory.MemLp.const_inner v (h_noise_memLp n)
  have hNoiseModeSqInt :
      MeasureTheory.Integrable (fun ω ↦ (inner ℝ v (η n ω)) ^ 2) μ :=
    MeasureTheory.MemLp.integrable_sq hNoiseModeLp
  have hVarInt :
      MeasureTheory.Integrable
        (fun ω ↦ ((inner ℝ v (η n ω)) ^ 2) / (s ^ 2)) μ := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hNoiseModeSqInt.const_mul ((s ^ 2)⁻¹)
  have hSplitIntegral :
      ∫ ω, (-(a ^ 2) : ℝ) + ((inner ℝ v (η n ω)) ^ 2) / (s ^ 2) ∂μ =
        ∫ _ : Ω, (-(a ^ 2) : ℝ) ∂μ +
          ∫ ω, ((inner ℝ v (η n ω)) ^ 2) / (s ^ 2) ∂μ := by
    simpa using
      (MeasureTheory.integral_add
        (μ := μ)
        (f := fun _ : Ω ↦ (-(a ^ 2) : ℝ))
        (g := fun ω ↦ ((inner ℝ v (η n ω)) ^ 2) / (s ^ 2))
        hConstInt hVarInt)
  have hVariance :
      ∫ ω, ((inner ℝ v (η n ω)) ^ 2) / (s ^ 2) ∂μ =
        (σ ^ 2 / (n : ℝ)) * (1 / s ^ 2) := by
    calc
      ∫ ω, ((inner ℝ v (η n ω)) ^ 2) / (s ^ 2) ∂μ
          = ∫ ω, (1 / s ^ 2) * ((inner ℝ v (η n ω)) ^ 2) ∂μ := by
              congr 1
              funext ω
              simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = (1 / s ^ 2) * ∫ ω, (inner ℝ v (η n ω)) ^ 2 ∂μ := by
            rw [MeasureTheory.integral_const_mul]
      _ = (1 / s ^ 2) * (σ ^ 2 / (n : ℝ)) := by
            rw [h_noise_modeVariance n (m - 1)]
      _ = (σ ^ 2 / (n : ℝ)) * (1 / s ^ 2) := by ring
  have ha_sq : a ^ 2 = b * (m : ℝ) ^ (-q) := by
    -- The deterministic mode coefficient is exactly the Chapter 7 Fourier profile.
    simpa [a, u, j] using (h_fourierDecay n ⟨m, hm⟩)
  have hs_sq : s ^ 2 = c * (m : ℝ) ^ (-p) := by
    -- The singular value is exactly the Chapter 7 algebraic decay profile.
    simpa [s, j] using (h_singularDecay n ⟨m, hm⟩)
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  have hp_ne : p ≠ 0 := by linarith
  have hNoiseTerm :
      (σ ^ 2 / (n : ℝ)) * (1 / s ^ 2) =
        ((σ ^ 2) / (n : ℝ)) * (1 / c) * (m : ℝ) ^ p := by
    rw [hs_sq, Real.rpow_neg hm_nonneg]
    field_simp [h_c.ne', Real.rpow_ne_zero hm_nonneg hp_ne]
  have hPointwise :
      (fun ω ↦
        ‖FilterRegularization.estimationError (Rtsvd n m) (K n) fTrue (η n ω)‖ ^ 2 -
          ‖FilterRegularization.estimationError (Rtsvd n (m - 1)) (K n) fTrue (η n ω)‖ ^ 2) =
        fun ω ↦ -(a ^ 2) + ((inner ℝ v (η n ω)) ^ 2) / (s ^ 2) := by
    funext ω
    simpa [a, s, u, v, j] using
      (backwardErrorStep_pointwise
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
        (Rtsvd := Rtsvd) (n := n) (mStar := mStar)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
        hm ω)
  -- Route correction: the expectation proof only integrates the already-normalized
  -- pointwise identity, then substitutes the scalar decay laws.
  rw [expectedSqErrorObjective_apply, expectedSqErrorObjective_apply,
    FilterRegularization.expectedSqEstimationError_def,
    FilterRegularization.expectedSqEstimationError_def]
  rw [← MeasureTheory.integral_sub hCurrInt hPrevInt]
  rw [hPointwise]
  have hConstEval : ∫ _ : Ω, (-(a ^ 2) : ℝ) ∂μ = -(a ^ 2) := by
    simp [MeasureTheory.integral_const]
  rw [hSplitIntegral, hVariance, hConstEval]
  calc
    -(a ^ 2) + (σ ^ 2 / (n : ℝ)) * (1 / s ^ 2)
        = -(b * (m : ℝ) ^ (-q)) + (σ ^ 2 / (n : ℝ)) * (1 / s ^ 2) := by rw [ha_sq]
    _ = -b * (m : ℝ) ^ (-q) + (σ ^ 2 / (n : ℝ)) * (1 / s ^ 2) := by ring
    _ = -b * (m : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (m : ℝ) ^ p := by
          rw [hNoiseTerm]

/-- Helper for Proposition 7.15: the forward difference is the backward-step
formula evaluated at the successor truncation index. -/
theorem expectedSqErrorObjective_forwardStep_eq :
    fwdDiff 1 (expectedSqErrorObjective μ K Rtsvd fTrue η n) mStar =
      -b * ((mStar + 1 : ℕ) : ℝ) ^ (-q) +
        ((σ ^ 2) / (n : ℝ)) * (1 / c) * ((mStar + 1 : ℕ) : ℝ) ^ p := by
  -- Rewrite the forward difference as the successor backward step.
  rw [fwdDiff]
  simpa using
    (expectedSqErrorObjective_backwardStep_eq
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (m := mStar + 1)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
      (hm := Nat.succ_pos _))

/-- Helper for Proposition 7.15: a nonpositive step expression forces the
benchmark upper bound from `(7.61)`. -/
theorem stepExpr_nonpos_implies_benchmarkUpper
    {x : ℝ} (hx_pos : 0 < x) (hn_pos : 0 < n)
    (h_step :
      -b * x ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p ≤ 0) :
    x ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) := by
  have hpq_pos : 0 < p + q := by
    linarith
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hratio_pos : 0 < ((σ ^ 2) / (n : ℝ)) := by
    positivity
  have hstep_mul :
      (((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p) * x ^ q ≤
        (b * x ^ (-q)) * x ^ q := by
    -- Multiply the step inequality by the positive factor `x ^ q`.
    have hmain :
        ((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p ≤ b * x ^ (-q) := by
      linarith
    exact mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg hx_nonneg q)
  have hpow_le :
      x ^ (p + q) ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) := by
    have haux :
        (((σ ^ 2) / (n : ℝ)) * (1 / c)) * x ^ (p + q) ≤ b := by
      calc
        (((σ ^ 2) / (n : ℝ)) * (1 / c)) * x ^ (p + q)
            = ((((σ ^ 2) / (n : ℝ)) * (1 / c)) * x ^ p) * x ^ q := by
                rw [Real.rpow_add hx_pos]
                ring_nf
        _ ≤ (b * x ^ (-q)) * x ^ q := hstep_mul
        _ = b * (x ^ (-q) * x ^ q) := by rw [mul_assoc]
        _ = b * x ^ 0 := by
              rw [← Real.rpow_add hx_pos (-q) q, show -q + q = (0 : ℝ) by ring]
              norm_num
        _ = b := by simp
    have hdiv :
        x ^ (p + q) ≤ b / (((σ ^ 2) / (n : ℝ)) * (1 / c)) := by
      exact (le_div_iff₀ (show 0 < ((σ ^ 2) / (n : ℝ)) * (1 / c) by positivity)).2 <|
        by simpa [mul_comm, mul_left_comm, mul_assoc] using haux
    calc
      x ^ (p + q) ≤ b / (((σ ^ 2) / (n : ℝ)) * (1 / c)) := hdiv
      _ = (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) := by
            field_simp [h_b.ne', h_c.ne', h_σ.ne', hn_pos.ne']
  have hroot :
      x ≤ ((((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) ^ ((p + q)⁻¹)) := by
    -- Take the positive `(p + q)`-th root of the power inequality.
    simpa [one_div] using
      (Real.le_rpow_inv_iff_of_pos
        (show 0 ≤ x by exact hx_nonneg)
        (show 0 ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) by positivity)
        hpq_pos).2 hpow_le
  simpa [one_div, Real.rpow_neg_eq_inv_rpow] using hroot

/-- Helper for Proposition 7.15: a nonnegative step expression forces the
benchmark lower bound from `(7.61)`. -/
theorem stepExpr_nonneg_implies_benchmarkLower
    {x : ℝ} (hx_pos : 0 < x) (hn_pos : 0 < n)
    (h_step :
      0 ≤ -b * x ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p) :
    (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) ≤ x := by
  have hpq_pos : 0 < p + q := by
    linarith
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hratio_pos : 0 < ((σ ^ 2) / (n : ℝ)) := by
    positivity
  have hstep_mul :
      (b * x ^ (-q)) * x ^ q ≤
        (((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p) * x ^ q := by
    -- Multiply the reversed step inequality by the positive factor `x ^ q`.
    have hmain :
        b * x ^ (-q) ≤ ((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p := by
      linarith
    exact mul_le_mul_of_nonneg_right hmain (Real.rpow_nonneg hx_nonneg q)
  have hpow_le :
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) ≤ x ^ (p + q) := by
    have haux :
        b ≤ (((σ ^ 2) / (n : ℝ)) * (1 / c)) * x ^ (p + q) := by
      calc
        b = b * x ^ 0 := by simp
        _ = b * (x ^ (-q) * x ^ q) := by
              rw [← Real.rpow_add hx_pos (-q) q, show -q + q = (0 : ℝ) by ring]
              norm_num
        _ = (b * x ^ (-q)) * x ^ q := by rw [mul_assoc]
        _ ≤ (((σ ^ 2) / (n : ℝ)) * (1 / c) * x ^ p) * x ^ q := hstep_mul
        _ = (((σ ^ 2) / (n : ℝ)) * (1 / c)) * x ^ (p + q) := by
              rw [Real.rpow_add hx_pos]
              ring_nf
    have hdiv :
        b / (((σ ^ 2) / (n : ℝ)) * (1 / c)) ≤ x ^ (p + q) := by
      exact (div_le_iff₀ (show 0 < ((σ ^ 2) / (n : ℝ)) * (1 / c) by positivity)).2 <|
        by simpa [mul_comm, mul_left_comm, mul_assoc] using haux
    calc
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹)
          = b / (((σ ^ 2) / (n : ℝ)) * (1 / c)) := by
              field_simp [h_b.ne', h_c.ne', h_σ.ne', hn_pos.ne']
      _ ≤ x ^ (p + q) := hdiv
  have hroot :
      ((((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) ^ ((p + q)⁻¹)) ≤ x := by
    -- Convert the power inequality back to a bound on `x`.
    simpa [one_div] using
      (Real.rpow_inv_le_iff_of_pos
        (show 0 ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ)))⁻¹) by positivity)
        (show 0 ≤ x by exact hx_nonneg)
        hpq_pos).2 hpow_le
  simpa [one_div, Real.rpow_neg_eq_inv_rpow] using hroot

/-- prop_7_15

Proposition 7.15 (1). For an interior minimizer `mStar` of the concrete TSVD
expected squared estimation-error objective on the source admissible set
`𝒵(n) = admissibleIndexSet n`, the backward discrete difference has the
explicit Chapter 7 formula `(7.59)` and is nonpositive. -/
theorem backwardDiffNonpos :
    expectedSqErrorObjective μ K Rtsvd fTrue η n mStar -
        expectedSqErrorObjective μ K Rtsvd fTrue η n (mStar - 1) =
      -b * (mStar : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (mStar : ℝ) ^ p ∧
        -b * (mStar : ℝ) ^ (-q) + ((σ ^ 2) / (n : ℝ)) * (1 / c) * (mStar : ℝ) ^ p ≤ 0 := by
  constructor
  · -- Read off the explicit backward-step formula at the minimizer.
    exact
      expectedSqErrorObjective_backwardStep_eq
        (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
        (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
        (Rtsvd := Rtsvd) (n := n) (m := mStar)
        (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
        (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
        (h_noise_modeVariance := h_noise_modeVariance)
        (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
        (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
        (hm := hm_pos)
  · -- Lemma 7.14 turns interior minimality into the sign of the backward step.
    have h_min_icc :
        IsMinOn (expectedSqErrorObjective μ K Rtsvd fTrue η n) (Set.Icc 0 n) mStar := by
      simpa [admissibleIndexSet] using h_min
    rw [← expectedSqErrorObjective_backwardStep_eq
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (m := mStar)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
      (hm := hm_pos)]
    exact backwardDiff_nonpos_of_isMinOn
      (expectedSqErrorObjective μ K Rtsvd fTrue η n) n mStar h_min_icc hm_lt

/-- Proposition 7.15 (2). For the same interior minimizer `mStar`, the forward
discrete difference has the explicit Chapter 7 formula `(7.60)` and is
nonnegative. -/
theorem forwardDiffNonneg :
    fwdDiff 1 (expectedSqErrorObjective μ K Rtsvd fTrue η n) mStar =
      -b * ((mStar + 1 : ℕ) : ℝ) ^ (-q) +
        ((σ ^ 2) / (n : ℝ)) * (1 / c) * ((mStar + 1 : ℕ) : ℝ) ^ p ∧
        0 ≤
          -b * ((mStar + 1 : ℕ) : ℝ) ^ (-q) +
            ((σ ^ 2) / (n : ℝ)) * (1 / c) * ((mStar + 1 : ℕ) : ℝ) ^ p := by
  constructor
  · -- Rewrite the forward step through the successor backward-step identity.
    exact expectedSqErrorObjective_forwardStep_eq
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (mStar := mStar)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
  · -- Lemma 7.14 turns interior minimality into the sign of the forward step.
    have h_min_icc :
        IsMinOn (expectedSqErrorObjective μ K Rtsvd fTrue η n) (Set.Icc 0 n) mStar := by
      simpa [admissibleIndexSet] using h_min
    rw [← expectedSqErrorObjective_forwardStep_eq
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
      (Rtsvd := Rtsvd) (n := n) (mStar := mStar)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)]
    exact forwardDiff_nonneg_of_isMinOn
      (expectedSqErrorObjective μ K Rtsvd fTrue η n) n mStar h_min_icc hm_lt

/-- Proposition 7.15 (3). The interior TSVD minimizer `mStar` lies above the
lower endpoint in the two-sided benchmark bound `(7.61)`. -/
theorem optimalIndexLowerBound :
    -1 +
        (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) ≤
      (mStar : ℝ) := by
  have hn_pos : 0 < n := lt_trans hm_pos hm_lt
  have h_forward := (forwardDiffNonneg
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
    (Rtsvd := Rtsvd) (n := n) (mStar := mStar)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)).2
  have hbenchmark :
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) ≤
        (((mStar + 1 : ℕ) : ℝ)) := by
    -- Apply the scalar lower benchmark to the successor forward step.
    exact stepExpr_nonneg_implies_benchmarkLower
      (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
      (η := η) (Rtsvd := Rtsvd) (mStar := mStar)
      (b := b) (c := c) (p := p) (q := q) (σ := σ) (n := n)
      (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
      (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
      (h_noise_modeVariance := h_noise_modeVariance)
      (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
      (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
      (x := ((mStar + 1 : ℕ) : ℝ)) (hx_pos := by positivity) (hn_pos := hn_pos)
      (h_step := h_forward)
  -- Subtract the successor `1` from the real bound.
  have hsucc : (((mStar + 1 : ℕ) : ℝ)) = (mStar : ℝ) + 1 := by
    norm_num
  linarith [hbenchmark, hsucc]

/-- Proposition 7.15 (4). The same interior TSVD minimizer `mStar` lies below
the upper endpoint in the two-sided benchmark bound `(7.61)`. -/
theorem optimalIndexUpperBound :
    (mStar : ℝ) ≤
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) := by
  have hn_pos : 0 < n := lt_trans hm_pos hm_lt
  have h_backward := (backwardDiffNonpos
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
    (Rtsvd := Rtsvd) (n := n) (mStar := mStar)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)).2
  -- Apply the scalar upper benchmark to the backward step at `mStar`.
  exact stepExpr_nonpos_implies_benchmarkUpper
    (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
    (η := η) (Rtsvd := Rtsvd) (mStar := mStar)
    (b := b) (c := c) (p := p) (q := q) (σ := σ) (n := n)
    (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
    (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
    (h_noise_modeVariance := h_noise_modeVariance)
    (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
    (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
    (x := mStar) (hx_pos := by exact_mod_cast hm_pos) (hn_pos := hn_pos)
    (h_step := h_backward)

/-- Companion to Proposition 7.15. The interior minimizer lies in the
one-step neighborhood of the canonical benchmark floor `optimalIndex b c p q σ
n`. -/
theorem interiorMinimizer_eq_optimalIndex :
    optimalIndex b c p q σ n - 1 ≤ mStar ∧ mStar ≤ optimalIndex b c p q σ n := by
  have hprofile_eq :
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) =
        ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
    -- Normalize the benchmark expression to the explicit floor profile.
    calc
      (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q))))
          = (1 / (b * c) : ℝ) ^ (-(1 / (p + q))) *
              (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
                rw [Real.mul_rpow (by positivity) (by positivity)]
      _ = (((1 / (b * c) : ℝ)⁻¹) ^ (1 / (p + q))) *
            (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
              rw [Real.rpow_neg_eq_inv_rpow]
      _ = ((b * c) ^ (1 / (p + q))) *
            (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
              rw [one_div, inv_inv]
  have hprofile_nonneg :
      0 ≤ ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
    positivity
  constructor
  · have hreal :
        ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) ≤
          (mStar : ℝ) + 1 := by
      have hlow :
          -1 + (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) ≤ (mStar : ℝ) :=
        optimalIndexLowerBound
          (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
          (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
          (Rtsvd := Rtsvd) (n := n) (mStar := mStar)
          (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
          (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
          (h_noise_modeVariance := h_noise_modeVariance)
          (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
          (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
      have hq :
          (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) ≤ (mStar : ℝ) + 1 := by
        linarith
      calc
        ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q))))
            = (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) := by
                symm
                exact hprofile_eq
        _ ≤ (mStar : ℝ) + 1 := hq
    have hrealNat :
        ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) ≤
          (((mStar + 1 : ℕ) : ℝ)) := by
      simpa using hreal
    have hfloor_le :
        optimalIndex b c p q σ n ≤ mStar + 1 := by
      rw [optimalIndex_def]
      exact Nat.floor_le_of_le hrealNat
    -- Convert the successor bound to the claimed one-step neighborhood.
    exact (Nat.sub_le_iff_le_add).2 <| by simpa [Nat.add_comm] using hfloor_le
  · have hreal :
        (mStar : ℝ) ≤
          ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := by
      have hupp :
          (mStar : ℝ) ≤
            (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) :=
        optimalIndexUpperBound
          (μ := μ) (K := K) (S := S) (h_length := h_length) (fTrue := fTrue)
          (b := b) (c := c) (p := p) (q := q) (σ := σ) (η := η)
          (Rtsvd := Rtsvd) (n := n) (mStar := mStar)
          (h_b := h_b) (h_c := h_c) (h_p := h_p) (h_q := h_q) (h_σ := h_σ)
          (h_noise_memLp := h_noise_memLp) (h_noise_meanZero := h_noise_meanZero)
          (h_noise_modeVariance := h_noise_modeVariance)
          (h_singularDecay := h_singularDecay) (h_fourierDecay := h_fourierDecay)
          (h_tsvd := h_tsvd) (h_min := h_min) (hm_pos := hm_pos) (hm_lt := hm_lt)
      calc
        (mStar : ℝ)
            ≤ (((1 / (b * c)) * ((σ ^ 2) / (n : ℝ))) ^ (-(1 / (p + q)))) := hupp
        _ = ((b * c) ^ (1 / (p + q))) * (((σ ^ 2) / (n : ℝ)) ^ (-(1 / (p + q)))) := hprofile_eq
    -- The upper real bound places `mStar` below the defining floor.
    rw [optimalIndex_def]
    exact (Nat.le_floor_iff hprofile_nonneg).2 hreal

omit h_b h_c h_p h_q h_σ h_noise_memLp h_noise_meanZero h_noise_modeVariance
  h_singularDecay h_fourierDecay h_tsvd h_min hm_pos hm_lt

end Proposition

end TsvdEstimation
