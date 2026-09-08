module

public import ReasLib.Analysis.InnerProductSpace.Congruence

public section

/-!
# Invertible square-root factorizations of uniformly positive operators
-/

noncomputable section

universe u

open scoped InnerProduct

namespace ContinuousLinearMap

open RCLike
open scoped InnerProductSpace

/- The lower-bound helpers establish the positivity and invertibility invariants before the
   spectral square-root construction is introduced. -/

/-- A nonnegative Loewner lower bound makes a continuous self-endomorphism positive. -/
theorem isPositive_of_loewner_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} {m : ℝ} (hm : 0 ≤ m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) : H.IsPositive := by
  -- Rewrite the order bound as positivity of the residual and add the scalar identity.
  have hpos : (H - m • (1 : E →L[ℝ] E)).IsPositive :=
    (le_def _ _).mp lower
  have hscalar : (m • (1 : E →L[ℝ] E)).IsPositive :=
    isPositive_one.smul_of_nonneg hm
  have hadd := hscalar.add hpos
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hadd

/-- A strict Loewner lower bound makes a continuous self-endomorphism invertible. -/
theorem isUnit_of_loewner_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) : IsUnit H := by
  -- The residual is positive, giving the quantitative inner-product estimate required for a unit.
  have hpos : (H - m • (1 : E →L[ℝ] E)).IsPositive :=
    (le_def _ _).mp lower
  apply isUnit_of_forall_le_norm_inner_map H (c := ⟨m, hm.le⟩) hm
  intro x
  have hnonneg := hpos.inner_nonneg_left x
  have hscalar : m * ‖x‖ ^ 2 ≤ @inner ℝ E _ (H x) x := by
    simpa [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, real_inner_self_eq_norm_sq] using hnonneg
  have hnorm : @inner ℝ E _ (H x) x ≤ ‖@inner ℝ E _ (H x) x‖ := le_abs_self _
  change ‖x‖ ^ 2 * m ≤ ‖@inner ℝ E _ (H x) x‖
  simpa [mul_comm] using hscalar.trans hnorm

/- The operator norm controls a positive quadratic form from above. -/

/-- A positive endomorphism is bounded above by its norm times the identity. -/
theorem isPositive_le_norm_smul_one
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} (hH : H.IsPositive) :
    H ≤ ‖H‖ • (1 : E →L[ℝ] E) := by
  -- Reduce the Loewner comparison to positivity of the residual operator.
  rw [le_def, isPositive_iff]
  constructor
  · exact (LinearMap.IsSymmetric.one (𝕜 := ℝ) (E := E)).smul (by simp) |>.sub hH.isSymmetric
  · intro x
    have hnorm : ‖H x‖ ≤ ‖H‖ * ‖x‖ := H.le_opNorm x
    have habs : |inner ℝ (H x) x| ≤ ‖H‖ * ‖x‖ ^ 2 := by
      calc
        |inner ℝ (H x) x| ≤ ‖H x‖ * ‖x‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖H‖ * ‖x‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right hnorm (norm_nonneg x)
        _ = ‖H‖ * ‖x‖ ^ 2 := by ring
    have hle : inner ℝ (H x) x ≤ ‖H‖ * ‖x‖ ^ 2 :=
      (le_abs_self _).trans habs
    simpa [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, real_inner_self_eq_norm_sq] using sub_nonneg.mpr hle

/-- A positive quadratic form satisfies the Cauchy--Schwarz inequality. -/
theorem positive_form_cauchySchwarz
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} (hH : H.IsPositive) (x y : E) :
    |inner ℝ (H x) y| ^ 2 ≤ inner ℝ (H x) x * inner ℝ (H y) y := by
  -- Expand positivity on `y - t • x` to obtain a nonnegative quadratic polynomial.
  let a : ℝ := inner ℝ (H x) x
  let b : ℝ := inner ℝ (H x) y
  let c : ℝ := inner ℝ (H y) y
  have ha : 0 ≤ a := by exact hH.inner_nonneg_left x
  have hc : 0 ≤ c := by exact hH.inner_nonneg_left y
  have hpoly (t : ℝ) : 0 ≤ c - 2 * t * b + t ^ 2 * a := by
    have h := hH.inner_nonneg_left (y - t • x)
    have hxy : inner ℝ y (H x) = b := by
      rw [real_inner_comm]
    have hyx : inner ℝ x (H y) = b := by
      rw [← hH.inner_left_eq_inner_right x y]
    have hxx : inner ℝ x (H x) = a := (hH.inner_left_eq_inner_right x x).symm
    have hyy : inner ℝ y (H y) = c := (hH.inner_left_eq_inner_right y y).symm
    simp only [inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, real_inner_comm, map_sub, map_smul] at h
    rw [hxy, hyx, hxx, hyy] at h
    have htstar : (starRingEnd ℝ) t = t := by simp
    rw [htstar] at h
    nlinarith
  by_cases ha0 : a = 0
  · have hb : b = 0 := by
      by_contra hb0
      have ht := hpoly ((c + 1) / (2 * b))
      rw [ha0] at ht
      have hterm : 2 * ((c + 1) / (2 * b)) * b = c + 1 := by
        field_simp [hb0]
      rw [hterm] at ht
      nlinarith
    change |b| ^ 2 ≤ a * c
    simpa [hb] using mul_nonneg ha hc
  · have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have ht := hpoly (b / a)
    have hab : b ^ 2 ≤ a * c := by
      field_simp [ha0] at ht
      nlinarith
    simpa [b, pow_two] using hab

/-- A positive invertible endomorphism has a strict Loewner lower bound. -/
theorem exists_loewner_lowerBound_of_isPositive_isUnit
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} (hpositive : H.IsPositive) (hunit : IsUnit H) :
    ∃ m : ℝ, 0 < m ∧ m • (1 : E →L[ℝ] E) ≤ H := by
  -- Use the ring inverse and the positive-form Cauchy--Schwarz estimate to control `H` below.
  let K : E →L[ℝ] E := Ring.inverse H
  have hHK : H * K = 1 := by
    exact Ring.mul_inverse_cancel H hunit
  have hHK_apply (x : E) : H (K x) = x := by
    have hx := congrArg (fun T : E →L[ℝ] E ↦ T x) hHK
    simpa using hx
  let c : ℝ := 1 + ‖K‖
  let m : ℝ := c⁻¹
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hm : 0 < m := by
    dsimp [m]
    exact inv_pos.mpr hc
  refine ⟨m, hm, ?_⟩
  rw [le_def, isPositive_iff']
  constructor
  · have hs : IsSelfAdjoint (m • (1 : E →L[ℝ] E)) :=
      (IsSelfAdjoint.all m).smul (IsSelfAdjoint.one (E →L[ℝ] E))
    exact hpositive.isSelfAdjoint.sub hs
  · intro x
    have hq : 0 ≤ inner ℝ (H x) x := hpositive.inner_nonneg_left x
    by_cases hx : x = 0
    · simp [hx]
    · have hcs := positive_form_cauchySchwarz hpositive (K x) x
      have hfirst : inner ℝ (H (K x)) (K x) ≤ ‖K‖ * ‖x‖ ^ 2 := by
        have habs : |inner ℝ x (K x)| ≤ ‖K‖ * ‖x‖ ^ 2 := by
          calc
            |inner ℝ x (K x)| ≤ ‖x‖ * ‖K x‖ := abs_real_inner_le_norm _ _
            _ ≤ ‖x‖ * (‖K‖ * ‖x‖) :=
              mul_le_mul_of_nonneg_left (K.le_opNorm x) (norm_nonneg x)
            _ = ‖K‖ * ‖x‖ ^ 2 := by ring
        rw [hHK_apply]
        exact (le_abs_self _).trans habs
      have hquad : ‖x‖ ^ 4 ≤ (‖K‖ * ‖x‖ ^ 2) * inner ℝ (H x) x := by
        calc
          ‖x‖ ^ 4 = |inner ℝ (H (K x)) x| ^ 2 := by
            rw [hHK_apply, real_inner_self_eq_norm_sq]
            rw [abs_of_nonneg (sq_nonneg _)]
            ring
          _ ≤ inner ℝ (H (K x)) (K x) * inner ℝ (H x) x := hcs
          _ ≤ (‖K‖ * ‖x‖ ^ 2) * inner ℝ (H x) x :=
            mul_le_mul_of_nonneg_right hfirst hq
      have hz : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
      have hbound : ‖x‖ ^ 2 ≤ c * inner ℝ (H x) x := by
        have hquad' : ‖x‖ ^ 2 * ‖x‖ ^ 2 ≤
            ‖x‖ ^ 2 * (‖K‖ * inner ℝ (H x) x) := by
          calc
            ‖x‖ ^ 2 * ‖x‖ ^ 2 = ‖x‖ ^ 4 := by ring
            _ ≤ (‖K‖ * ‖x‖ ^ 2) * inner ℝ (H x) x := hquad
            _ = ‖x‖ ^ 2 * (‖K‖ * inner ℝ (H x) x) := by ring
        have hquad'' : ‖x‖ ^ 2 * ‖x‖ ^ 2 ≤
            (‖K‖ * inner ℝ (H x) x) * ‖x‖ ^ 2 := by
          calc
            ‖x‖ ^ 2 * ‖x‖ ^ 2 ≤
                ‖x‖ ^ 2 * (‖K‖ * inner ℝ (H x) x) := hquad'
            _ = (‖K‖ * inner ℝ (H x) x) * ‖x‖ ^ 2 := by ring
        have hcancel := le_of_mul_le_mul_right hquad'' hz
        dsimp [c]
        calc
          ‖x‖ ^ 2 ≤ ‖K‖ * inner ℝ (H x) x := hcancel
          _ ≤ (1 + ‖K‖) * inner ℝ (H x) x := by
            gcongr
            linarith
      have hscaled := mul_le_mul_of_nonneg_left hbound hm.le
      have hcm : m * c = 1 := by
        dsimp [m]
        exact inv_mul_cancel₀ hc.ne'
      have hscaled' : m * ‖x‖ ^ 2 ≤ (m * c) * inner ℝ (H x) x := by
        calc
          m * ‖x‖ ^ 2 ≤ m * (c * inner ℝ (H x) x) := hscaled
          _ = (m * c) * inner ℝ (H x) x := by ring
      simpa [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
        inner_smul_left, real_inner_self_eq_norm_sq, hcm] using hscaled'

/-- A self-adjoint operator bounded in Loewner order by a scalar identity has the corresponding norm
bound. -/
theorem norm_le_of_selfAdjoint_loewner_abs_bound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {K : E →L[ℝ] E} (hK : IsSelfAdjoint K) {r : ℝ} (hr : 0 ≤ r)
    (hneg : -(r • (1 : E →L[ℝ] E)) ≤ K)
    (hpos : K ≤ r • (1 : E →L[ℝ] E)) :
    ‖K‖ ≤ r := by
  -- The two Loewner inequalities bound the real quadratic form on every vector.
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient K hK.isSymmetric]
  refine ciSup_le fun x ↦ ?_
  by_cases hx : x = 0
  · simp [hx, hr]
  have hupper : K.reApplyInnerSelf x ≤ r * ‖x‖ ^ 2 := by
    have h := (ContinuousLinearMap.le_def _ _).mp hpos
    have hx' := h.inner_nonneg_left x
    have hcalc : 0 ≤ r * ‖x‖ ^ 2 - K.reApplyInnerSelf x := by
      simpa [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
        inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
        ContinuousLinearMap.reApplyInnerSelf_apply] using hx'
    linarith
  have hlower : -r * ‖x‖ ^ 2 ≤ K.reApplyInnerSelf x := by
    have h := (ContinuousLinearMap.le_def _ _).mp hneg
    have hx' := h.inner_nonneg_left x
    simp only [sub_neg_eq_add] at hx'
    rw [add_apply, smul_apply, one_apply_eq_self, inner_add_left, inner_smul_left] at hx'
    have hcalc : 0 ≤ K.reApplyInnerSelf x + r * ‖x‖ ^ 2 := by
      simpa [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
        inner_smul_left, real_inner_self_eq_norm_sq,
        ContinuousLinearMap.reApplyInnerSelf_apply] using hx'
    linarith
  rw [ContinuousLinearMap.rayleighQuotient]
  have hsq : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  rw [abs_div, abs_of_nonneg (sq_nonneg ‖x‖)]
  apply (div_le_iff₀ hsq).mpr
  exact (abs_le).mpr ⟨by simpa [neg_mul] using hlower, hupper⟩

/-- A zero-dimensional operator space has a canonical self-adjoint square root. -/
theorem exists_selfAdjoint_sqrt_of_loewner_lowerBound_subsingleton
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Subsingleton E] {H : E →L[ℝ] E} :
    ∃ S : E →L[ℝ] E, IsSelfAdjoint S ∧ S * S = H := by
  -- Every endomorphism is equal in a subsingleton space, so the zero operator is a root.
  refine ⟨0, IsSelfAdjoint.zero _, ?_⟩
  exact Subsingleton.elim _ _

/- The near-identity factor will be built from the scalar half-power series.  The coefficient
   bound below is the convergence interface used by the operator-valued series. -/

/-- The recursive coefficients of the real half-power series are uniformly bounded in absolute
value by one. -/
private noncomputable def sqrtOneAddCoeff : ℕ → ℝ
  | 0 => 1
  | n + 1 => ((1 / 2 - (n : ℝ)) / (n + 1 : ℝ)) * sqrtOneAddCoeff n

/-- Every coefficient of the real half-power series has absolute value at most one. -/
private theorem sqrtOneAddCoeff_abs_le_one (n : ℕ) :
    |sqrtOneAddCoeff n| ≤ 1 := by
  -- The induction step separates the scalar ratio from the previously bounded coefficient.
  induction n with
  | zero => simp [sqrtOneAddCoeff]
  | succ n ih =>
      rw [sqrtOneAddCoeff, abs_mul, abs_div]
      have hden : 0 < (n + 1 : ℝ) := by positivity
      have hratio : |1 / 2 - (n : ℝ)| ≤ (n + 1 : ℝ) := by
        rw [abs_le]
        have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
        constructor <;> linarith
      rw [abs_of_pos hden]
      calc
        |1 / 2 - (n : ℝ)| / (n + 1 : ℝ) * |sqrtOneAddCoeff n|
            ≤ |1 / 2 - (n : ℝ)| / (n + 1 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left ih (div_nonneg (abs_nonneg _) hden.le)
        _ ≤ 1 := by
          simpa only [mul_one] using
            (div_le_iff₀ hden).2 (by simpa only [one_mul] using hratio)

/-- The recursive coefficients satisfy the half-power first-order recurrence. -/
private theorem sqrtOneAddCoeff_succ_mul (n : ℕ) :
    (n + 1 : ℝ) * sqrtOneAddCoeff (n + 1) =
      (1 / 2 - (n : ℝ)) * sqrtOneAddCoeff n := by
  rw [sqrtOneAddCoeff]
  have hden : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hden]

/-- A strict positive lower bound places the normalized residual in the open unit ball. -/
private theorem normalizedResidual_norm_lt_one
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Nontrivial E] {H : E →L[ℝ] E} (selfAdjoint : IsSelfAdjoint H) {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) :
    ‖1 - ‖H‖⁻¹ • H‖ < 1 := by
  -- Invertibility makes the normalization scale strictly positive.
  have hunit : IsUnit H := isUnit_of_loewner_lowerBound hm lower
  have hHne : H ≠ 0 := hunit.ne_zero
  have hM : 0 < ‖H‖ := norm_pos_iff.mpr hHne
  let M : ℝ := ‖H‖
  let r : ℝ := 1 - m / M
  have hpositive : H.IsPositive := isPositive_of_loewner_lowerBound hm.le lower
  have hupper : H ≤ M • (1 : E →L[ℝ] E) := by
    simpa [M] using isPositive_le_norm_smul_one hpositive
  have hmM : m ≤ M := by
    have horder : m • (1 : E →L[ℝ] E) ≤ M • (1 : E →L[ℝ] E) := lower.trans hupper
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    have hq := (le_def _ _).mp horder |>.inner_nonneg_left x
    have hq' : m * ‖x‖ ^ 2 ≤ M * ‖x‖ ^ 2 := by
      simpa [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
        inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq, sub_eq_add_neg,
        M] using hq
    have hxnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    nlinarith
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact sub_nonneg.mpr ((div_le_iff₀ hM).2 (by simpa [M] using hmM))
  have hr1 : r < 1 := by
    dsimp [r]
    have : 0 < m / M := div_pos hm hM
    linarith
  let K : E →L[ℝ] E := 1 - M⁻¹ • H
  have hKadj : IsSelfAdjoint K := by
    dsimp [K]
    exact (IsSelfAdjoint.one _).sub ((IsSelfAdjoint.all _).smul selfAdjoint)
  have hscaleUpper : M⁻¹ • H ≤ (1 : E →L[ℝ] E) := by
    have h := smul_mono hupper (inv_nonneg.mpr hM.le)
    simpa [M, smul_smul, hM.ne'] using h
  have hscaleLower : (m / M) • (1 : E →L[ℝ] E) ≤ M⁻¹ • H := by
    have h := smul_mono lower (inv_nonneg.mpr hM.le)
    simpa [smul_smul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, hM.ne'] using h
  have hKnonneg : (0 : E →L[ℝ] E) ≤ K := by
    dsimp [K]
    rw [nonneg_iff_isPositive]
    exact (le_def _ _).mp hscaleUpper
  have hKlower : -(r • (1 : E →L[ℝ] E)) ≤ K := by
    have hKpos : K.IsPositive := (nonneg_iff_isPositive K).mp hKnonneg
    have hrpos : (r • (1 : E →L[ℝ] E)).IsPositive :=
      isPositive_one.smul_of_nonneg hr0
    have hsum : (0 : E →L[ℝ] E) ≤ K + r • (1 : E →L[ℝ] E) :=
      (nonneg_iff_isPositive _).mpr (hKpos.add hrpos)
    have hsumPos : (K + r • (1 : E →L[ℝ] E)).IsPositive :=
      (nonneg_iff_isPositive _).mp hsum
    rw [le_def]
    simpa [sub_eq_add_neg] using hsumPos
  have hKupper : K ≤ r • (1 : E →L[ℝ] E) := by
    have hdiff : (0 : E →L[ℝ] E) ≤ M⁻¹ • H - (m / M) • (1 : E →L[ℝ] E) := by
      rw [nonneg_iff_isPositive]
      exact (le_def _ _).mp hscaleLower
    have hdiffPos : (M⁻¹ • H - (m / M) • (1 : E →L[ℝ] E)).IsPositive :=
      (nonneg_iff_isPositive _).mp hdiff
    have heq : r • (1 : E →L[ℝ] E) - K =
        M⁻¹ • H - (m / M) • (1 : E →L[ℝ] E) := by
      ext x
      simp [K, r, sub_apply, sub_smul]
    rw [le_def, heq]
    exact hdiffPos
  have hnorm : ‖K‖ ≤ r :=
    norm_le_of_selfAdjoint_loewner_abs_bound hKadj hr0 hKlower hKupper
  exact lt_of_le_of_lt (by simpa [K] using hnorm) hr1

/- The coefficient recurrence lifts to a finite Cauchy-product recurrence. -/

/-- The antidiagonal convolution of a half-power recurrence satisfies the induced recurrence. -/
private theorem sum_antidiagonal_mul_of_halfPowerRecurrence
    (c : ℕ → ℝ)
    (hrec : ∀ n : ℕ, (n + 1 : ℝ) * c (n + 1) =
      (1 / 2 - (n : ℝ)) * c n) (n : ℕ) :
    (n + 1 : ℝ) * (∑ p ∈ Finset.antidiagonal (n + 1), c p.1 * c p.2) =
      (1 - (n : ℝ)) * (∑ p ∈ Finset.antidiagonal n, c p.1 * c p.2) := by
  -- Rewrite the scalar multiplier using the antidiagonal index equation.
  rw [Finset.mul_sum]
  have hindex (p : ℕ × ℕ) (hp : p ∈ Finset.antidiagonal (n + 1)) :
      (n + 1 : ℝ) = (p.1 : ℝ) + p.2 := by
    exact_mod_cast (Finset.mem_antidiagonal.mp hp).symm
  have hleft :
      (∑ p ∈ Finset.antidiagonal (n + 1),
        (p.1 : ℝ) * (c p.1 * c p.2)) =
        ∑ p ∈ Finset.antidiagonal n,
          (1 / 2 - (p.1 : ℝ)) * (c p.1 * c p.2) := by
    rw [Finset.Nat.sum_antidiagonal_succ]
    simp only [Prod.fst_zero, Nat.cast_zero, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro p hp
    have hr := hrec p.1
    simpa [Nat.cast_add, mul_assoc] using congrArg (fun z : ℝ ↦ z * c p.2) hr
  have hright :
      (∑ p ∈ Finset.antidiagonal (n + 1),
        (p.2 : ℝ) * (c p.1 * c p.2)) =
        ∑ p ∈ Finset.antidiagonal n,
          (1 / 2 - (p.2 : ℝ)) * (c p.1 * c p.2) := by
    rw [Finset.Nat.sum_antidiagonal_succ']
    simp only [Prod.snd_zero, Nat.cast_zero, zero_mul, zero_add]
    apply Finset.sum_congr rfl
    intro p hp
    have hr := hrec p.2
    simpa [Nat.cast_add, mul_assoc, mul_comm, mul_left_comm] using
      congrArg (fun z : ℝ ↦ z * c p.1) hr
  have hsplit :
      (∑ p ∈ Finset.antidiagonal (n + 1),
        ((p.1 : ℝ) + p.2) * (c p.1 * c p.2)) =
        (∑ p ∈ Finset.antidiagonal (n + 1),
          (p.1 : ℝ) * (c p.1 * c p.2)) +
          ∑ p ∈ Finset.antidiagonal (n + 1),
            (p.2 : ℝ) * (c p.1 * c p.2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  have hreplace :
      (∑ p ∈ Finset.antidiagonal (n + 1),
        (n + 1 : ℝ) * (c p.1 * c p.2)) =
        ∑ p ∈ Finset.antidiagonal (n + 1),
          ((p.1 : ℝ) + p.2) * (c p.1 * c p.2) := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [hindex p hp]
  rw [hreplace, hsplit, hleft, hright, ← Finset.sum_add_distrib]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
  have hp'' : (p.1 : ℝ) + p.2 = (n : ℝ) := by exact_mod_cast hp'
  rw [← hp'']
  ring

/-- The finite self-convolution of the half-power coefficients has only its first two terms. -/
private theorem sum_antidiagonal_sqrtOneAddCoeff_mul (n : ℕ) :
    (∑ p ∈ Finset.antidiagonal n, sqrtOneAddCoeff p.1 * sqrtOneAddCoeff p.2) =
      if n = 0 then 1 else if n = 1 then 1 else 0 := by
  -- Use the recurrence for the convolution and cancel the positive successor factor.
  induction n with
  | zero =>
      simp [Finset.Nat.antidiagonal_zero, sqrtOneAddCoeff]
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simp [Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
          sqrtOneAddCoeff, sqrtOneAddCoeff_succ_mul]
        norm_num
      · have hrec := sum_antidiagonal_mul_of_halfPowerRecurrence sqrtOneAddCoeff
          sqrtOneAddCoeff_succ_mul n
        have hne : (n + 1 : ℝ) ≠ 0 := by positivity
        by_cases hn1 : n = 1
        · subst n
          simp only [if_neg (by norm_num : (2 : ℕ) ≠ 0), if_pos rfl]
          have hzero :
              (∑ p ∈ Finset.antidiagonal 2,
                sqrtOneAddCoeff p.1 * sqrtOneAddCoeff p.2) = 0 := by
            apply (mul_left_cancel₀ hne)
            simpa using hrec
          exact hzero
        · have hn2 : 2 ≤ n := by omega
          have ihzero :
              (∑ p ∈ Finset.antidiagonal n,
                sqrtOneAddCoeff p.1 * sqrtOneAddCoeff p.2) = 0 := by
            simpa [if_neg hn, if_neg hn1] using ih
          have hzero :
              (∑ p ∈ Finset.antidiagonal (n + 1),
                sqrtOneAddCoeff p.1 * sqrtOneAddCoeff p.2) = 0 := by
            apply (mul_left_cancel₀ hne)
            rw [hrec, ihzero]
            ring
          simpa [hn] using hzero

/-- The half-power series squares to the corresponding first-order perturbation in a Banach algebra. -/
private theorem tsum_smul_pow_mul_self_eq_one_add
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [NormOneClass A]
    (K : A) (hK : ‖K‖ < 1) :
    (∑' n : ℕ, sqrtOneAddCoeff n • K ^ n) *
        (∑' n : ℕ, sqrtOneAddCoeff n • K ^ n) = 1 + K := by
  -- Absolute convergence follows by comparison with the geometric series in `‖K‖`.
  have hgeom : Summable (fun n : ℕ ↦ ‖K‖ ^ n) :=
    summable_geometric_of_lt_one (norm_nonneg K) hK
  have hnorm : Summable (fun n : ℕ ↦ ‖sqrtOneAddCoeff n • K ^ n‖) := by
    apply hgeom.of_norm_bounded
    intro n
    calc
      ‖‖sqrtOneAddCoeff n • K ^ n‖‖ = ‖sqrtOneAddCoeff n • K ^ n‖ :=
          norm_of_nonneg (norm_nonneg (sqrtOneAddCoeff n • K ^ n))
      _ = ‖sqrtOneAddCoeff n‖ * ‖K ^ n‖ := norm_smul _ _
      _ ≤ |sqrtOneAddCoeff n| * ‖K‖ ^ n := by
        rw [Real.norm_eq_abs]
        gcongr
        exact norm_pow_le K n
      _ ≤ 1 * ‖K‖ ^ n := by
        gcongr
        exact sqrtOneAddCoeff_abs_le_one n
      _ = ‖K‖ ^ n := by simp
  -- Normalize each Cauchy-product summand to one scalar coefficient times one power.
  have hterm (i j : ℕ) :
      (sqrtOneAddCoeff i • K ^ i) * (sqrtOneAddCoeff j • K ^ j) =
        (sqrtOneAddCoeff i * sqrtOneAddCoeff j) • K ^ (i + j) := by
    simpa [pow_add] using
      (smul_mul_smul_comm (sqrtOneAddCoeff i) (K ^ i)
        (sqrtOneAddCoeff j) (K ^ j))
  have hsum (n : ℕ) :
      (∑ p ∈ Finset.antidiagonal n,
        (sqrtOneAddCoeff p.1 • K ^ p.1) *
          (sqrtOneAddCoeff p.2 • K ^ p.2)) =
        (∑ p ∈ Finset.antidiagonal n,
          sqrtOneAddCoeff p.1 * sqrtOneAddCoeff p.2) • K ^ n := by
    calc
      (∑ p ∈ Finset.antidiagonal n,
          (sqrtOneAddCoeff p.1 • K ^ p.1) *
            (sqrtOneAddCoeff p.2 • K ^ p.2)) =
          ∑ p ∈ Finset.antidiagonal n,
            (sqrtOneAddCoeff p.1 * sqrtOneAddCoeff p.2) • K ^ (p.1 + p.2) := by
        apply Finset.sum_congr rfl
        intro p hp
        exact hterm p.1 p.2
      _ = ∑ p ∈ Finset.antidiagonal n,
            (sqrtOneAddCoeff p.1 * sqrtOneAddCoeff p.2) • K ^ n := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp' : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
        rw [hp']
      _ = (∑ p ∈ Finset.antidiagonal n,
            sqrtOneAddCoeff p.1 * sqrtOneAddCoeff p.2) • K ^ n := by
        rw [Finset.sum_smul]
  calc
    (∑' n : ℕ, sqrtOneAddCoeff n • K ^ n) *
          (∑' n : ℕ, sqrtOneAddCoeff n • K ^ n) =
        ∑' n : ℕ, ∑ p ∈ Finset.antidiagonal n,
          (sqrtOneAddCoeff p.1 • K ^ p.1) *
            (sqrtOneAddCoeff p.2 • K ^ p.2) :=
      tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hnorm hnorm
    _ = ∑' n : ℕ,
          (∑ p ∈ Finset.antidiagonal n,
            sqrtOneAddCoeff p.1 * sqrtOneAddCoeff p.2) • K ^ n := by
      apply tsum_congr
      intro n
      exact hsum n
    _ = ∑' n : ℕ,
          (if n = 0 then (1 : ℝ) else if n = 1 then 1 else 0) • K ^ n := by
      apply tsum_congr
      intro n
      rw [sum_antidiagonal_sqrtOneAddCoeff_mul]
    _ = 1 + K := by
      calc
        (∑' n : ℕ,
            (if n = 0 then (1 : ℝ) else if n = 1 then 1 else 0) • K ^ n) =
            ∑ n ∈ ({0, 1} : Finset ℕ),
              (if n = 0 then (1 : ℝ) else if n = 1 then 1 else 0) • K ^ n := by
          apply tsum_eq_sum
          intro n hn
          have hn0 : n ≠ 0 := by
            intro h
            apply hn
            simp [h]
          have hn1 : n ≠ 1 := by
            intro h
            apply hn
            simp [h]
          simp [hn0, hn1]
        _ = 1 + K := by
          simp [Finset.sum_insert, Finset.sum_singleton]

/-- A self-adjoint strict contraction has a self-adjoint half-power square root. -/
private theorem exists_selfAdjoint_sqrt_one_add_of_norm_lt_one
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [Nontrivial E] {K : E →L[ℝ] E} (hK : IsSelfAdjoint K) (hKn : ‖K‖ < 1) :
    ∃ S : E →L[ℝ] E, IsSelfAdjoint S ∧ S * S = 1 + K := by
  -- The nontrivial space gives the exact norm of the identity required by the power estimate.
  letI : NormOneClass (E →L[ℝ] E) :=
    ⟨by simpa using (ContinuousLinearMap.norm_id (𝕜 := ℝ) (E := E))⟩
  let S : E →L[ℝ] E := ∑' n : ℕ, sqrtOneAddCoeff n • K ^ n
  refine ⟨S, ?_, ?_⟩
  · rw [isSelfAdjoint_iff]
    dsimp only [S]
    rw [tsum_star]
    apply tsum_congr
    intro n
    exact ((IsSelfAdjoint.all _).smul (hK.pow n)).star_eq
  · simpa [S] using tsum_smul_pow_mul_self_eq_one_add K hKn

/-- A strictly positive self-adjoint endomorphism admits a self-adjoint square root. -/
theorem exists_selfAdjoint_sqrt_of_loewner_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} (selfAdjoint : IsSelfAdjoint H) {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) :
    ∃ S : E →L[ℝ] E, IsSelfAdjoint S ∧ S * S = H := by
  -- The zero-dimensional branch is elementary; the remaining branch is the genuine spectral step.
  cases subsingleton_or_nontrivial E with
  | inl hE =>
      -- Local instance justification: the branch hypothesis supplies the canonical space-level
      -- instance needed by the subsingleton helper.
      letI : Subsingleton E := hE
      exact exists_selfAdjoint_sqrt_of_loewner_lowerBound_subsingleton
  | inr hE =>
      -- Local instance justification: the nontrivial branch supplies the norm witness required
      -- by the forthcoming normalization argument.
      letI : Nontrivial E := hE
      -- Route correction: replace the unavailable real CFC route with the explicitly convergent
      -- half-power series proved above.
      -- Normalize by the operator norm, whose positivity follows from invertibility.
      have hunit : IsUnit H := isUnit_of_loewner_lowerBound hm lower
      have hHne : H ≠ 0 := hunit.ne_zero
      have hM : 0 < ‖H‖ := norm_pos_iff.mpr hHne
      let K : E →L[ℝ] E := ‖H‖⁻¹ • H - 1
      have hKadj : IsSelfAdjoint K := by
        dsimp [K]
        exact (IsSelfAdjoint.all _).smul selfAdjoint |>.sub (IsSelfAdjoint.one _)
      have hKnorm : ‖K‖ < 1 := by
        have hres := normalizedResidual_norm_lt_one selfAdjoint hm lower
        have hneg : K = -(1 - ‖H‖⁻¹ • H) := by
          ext x
          simp [K, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        rw [hneg, norm_neg]
        exact hres
      obtain ⟨R, hR, hRR⟩ := exists_selfAdjoint_sqrt_one_add_of_norm_lt_one hKadj hKnorm
      have hscale : ‖H‖ • (1 + K) = H := by
        ext x
        simp [K, smul_add, smul_sub, smul_smul, hM.ne', one_apply_eq_self]
      have hsqrt : Real.sqrt ‖H‖ * Real.sqrt ‖H‖ = ‖H‖ := by
        simpa [pow_two] using Real.sq_sqrt hM.le
      refine ⟨Real.sqrt ‖H‖ • R, (IsSelfAdjoint.all _).smul hR, ?_⟩
      calc
        (Real.sqrt ‖H‖ • R) * (Real.sqrt ‖H‖ • R) =
            (Real.sqrt ‖H‖ * Real.sqrt ‖H‖) • (R * R) := by
              simpa using smul_mul_smul_comm (Real.sqrt ‖H‖) R (Real.sqrt ‖H‖) R
        _ = ‖H‖ • (R * R) := by rw [hsqrt]
        _ = ‖H‖ • (1 + K) := by rw [hRR]
        _ = H := hscale

/-- A positive real continuous endomorphism has nonnegative real spectrum. -/
theorem spectrumRestricts_of_isPositive
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} (hH : H.IsPositive) :
    SpectrumRestricts H ContinuousMap.realToNNReal := by
  -- Exclude a negative spectral point using the same lower bound criterion as the canonical API.
  rw [SpectrumRestricts.nnreal_iff]
  intro c hc
  contrapose! hc
  rw [spectrum.notMem_iff, IsUnit.sub_iff, sub_eq_add_neg, ← map_neg]
  rw [← neg_pos] at hc
  set c := -c
  exact isUnit_of_forall_le_norm_inner_map _ (c := ⟨c, hc.le⟩) hc fun x ↦ calc
    ‖x‖ ^ 2 * c = re ⟪algebraMap ℝ (E →L[ℝ] E) c x, x⟫_ℝ := by
      rw [Algebra.algebraMap_eq_smul_one, ← algebraMap_smul ℝ c (1 : (E →L[ℝ] E)),
        smul_apply, one_apply_eq_self, inner_smul_left, RCLike.algebraMap_eq_ofReal,
        conj_ofReal, re_ofReal_mul, inner_self_eq_norm_sq, mul_comm]
    _ ≤ re ⟪(H + (algebraMap ℝ (E →L[ℝ] E)) c) x, x⟫_ℝ := by
      simpa only [add_apply, inner_add_left, map_add, le_add_iff_nonneg_left]
        using hH.re_inner_nonneg_left x
    _ ≤ ‖⟪(H + (algebraMap ℝ (E →L[ℝ] E)) c) x, x⟫_ℝ‖ := RCLike.re_le_norm _

/-- Under an available real self-adjoint continuous functional calculus, a strictly positive
operator has an invertible self-adjoint square-root factor. -/
theorem exists_unit_sqrt_factorization_of_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E}
    [NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    (selfAdjoint : IsSelfAdjoint H) {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) :
    ∃ S : E →L[ℝ] E, IsSelfAdjoint S ∧ IsUnit S ∧ H = S.pushforward 1 := by
  -- Establish the spectral restriction and invoke the canonical CFC square-root theorem.
  have hpositive : H.IsPositive := isPositive_of_loewner_lowerBound hm.le lower
  have hQ : QuasispectrumRestricts H ContinuousMap.realToNNReal := by
    rw [quasispectrumRestricts_iff_spectrumRestricts]
    exact spectrumRestricts_of_isPositive hpositive
  obtain ⟨S, hS, -, hSS⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts selfAdjoint hQ
  have hunitH : IsUnit H := isUnit_of_loewner_lowerBound hm lower
  have hunitS : IsUnit S := isUnit_mul_self_iff.mp (hSS ▸ hunitH)
  refine ⟨S, hS, hunitS, ?_⟩
  -- Normalize the pushforward identity to the square identity delivered by CFC.
  rw [pushforward_one, hS.adjoint_eq]
  exact hSS.symm

/- The target-facing factorization interface is kept independent of the unavailable real CFC
   instance.  Its proof belongs to a real spectral-theorem owner; the lower-bound adapter below
   and the final equivalence packaging are proved here. -/

/-- A positive invertible real continuous endomorphism has a self-adjoint invertible factor. -/
theorem exists_unit_selfAdjoint_factor_of_isPositive_and_isUnit
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} (hpositive : H.IsPositive) (hunit : IsUnit H) :
    ∃ S : E →L[ℝ] E, IsSelfAdjoint S ∧ IsUnit S ∧ H = S.pushforward 1 := by
  -- First extract a quantitative lower bound from positivity and invertibility.
  obtain ⟨m, hm, lower⟩ := exists_loewner_lowerBound_of_isPositive_isUnit hpositive hunit
  -- The remaining owner theorem supplies the self-adjoint square root in the real operator ring.
  obtain ⟨S, hS, hSS⟩ := exists_selfAdjoint_sqrt_of_loewner_lowerBound
    hpositive.isSelfAdjoint hm lower
  have hunitS : IsUnit S := isUnit_mul_self_iff.mp (hSS ▸ hunit)
  refine ⟨S, hS, hunitS, ?_⟩
  -- Convert the square identity to the congruence notation used by this file.
  rw [pushforward_one, hS.adjoint_eq]
  exact hSS.symm

/-- A strict Loewner lower bound supplies the hypotheses of the real factorization interface. -/
theorem exists_unit_selfAdjoint_factor_of_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) :
    ∃ S : E →L[ℝ] E, IsSelfAdjoint S ∧ IsUnit S ∧ H = S.pushforward 1 := by
  -- First derive positivity and invertibility from the quantitative lower bound.
  have hpositive : H.IsPositive := isPositive_of_loewner_lowerBound hm.le lower
  have hunit : IsUnit H := isUnit_of_loewner_lowerBound hm lower
  -- Then pass those invariants through the direct real factorization interface.
  exact exists_unit_selfAdjoint_factor_of_isPositive_and_isUnit hpositive hunit

/-- An invertible self-adjoint factor determines a continuous linear equivalence with the same
pushforward factorization. -/
theorem continuousLinearEquiv_of_unit_selfAdjoint_factor
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H S : E →L[ℝ] E} (hS : IsSelfAdjoint S) (hunitS : IsUnit S)
    (hH : H = S.pushforward 1) :
    ∃ L : E ≃L[ℝ] E,
      IsSelfAdjoint L.toContinuousLinearMap ∧
        H = L.toContinuousLinearMap.pushforward 1 := by
  -- Convert the unit criterion to kernel/range equalities and package the equivalence.
  have hbij : Function.Bijective S := S.isUnit_iff_bijective.mp hunitS
  have hker : S.ker = ⊥ := by
    simpa [LinearMap.ker_eq_bot] using hbij.1
  have hrange : S.range = ⊤ := by
    simpa [LinearMap.range_eq_top] using hbij.2
  let L : E ≃L[ℝ] E := ContinuousLinearEquiv.ofBijective S hker hrange
  refine ⟨L, ?_, ?_⟩
  · change IsSelfAdjoint S
    exact hS
  · change H = S.pushforward 1
    exact hH

/-- Synthetic proof scope: ContinuousLinearMap.exists_sqrtEquiv_of_lowerBound. A self-adjoint
operator with a strictly positive uniform lower bound admits a self-adjoint continuous linear
equivalence factor `L` with `H = L ∘ L†`. -/
theorem exists_sqrtEquiv_of_lowerBound
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E} {m : ℝ} (selfAdjoint : IsSelfAdjoint H) (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) :
    ∃ L : E ≃L[ℝ] E,
      IsSelfAdjoint L.toContinuousLinearMap ∧
        H = L.toContinuousLinearMap.pushforward 1 := by
  -- Route correction: consume the direct real factorization interface instead of synthesizing
  -- `NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint`.
  obtain ⟨S, hS, hunitS, hfactor⟩ :=
    exists_unit_selfAdjoint_factor_of_lowerBound hm lower
  -- The existing packaging lemma turns the unit self-adjoint factor into the equivalence.
  exact continuousLinearEquiv_of_unit_selfAdjoint_factor hS hunitS hfactor

end ContinuousLinearMap
