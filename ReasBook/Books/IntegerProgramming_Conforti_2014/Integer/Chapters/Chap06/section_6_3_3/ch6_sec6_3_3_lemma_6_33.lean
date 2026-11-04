/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3.ch6_sec6_3_definition_6_3_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_3_2.ch6_sec6_3_2_lemma_6_29

-- Declarations for this item will be appended below by the statement pipeline.

section Lemma633

variable {q : ℕ}

local notation "Rq" => Fin q → ℝ
local notation "Qq" => Fin q → ℚ
local notation "NatAssignment" => Rq →₀ ℕ
local notation "ContAssignment" => Rq →₀ NNReal

/-- Helper for Lemma 6.33: resetting only `ψ 0` to `0` preserves mixed validity because the
origin contributes nothing to the balance vector. -/
lemma mixedIntegerValidPairResetPsiZero
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ) :
    IsValidGomoryJohnsonPair f π (fun r ↦ if r = 0 then 0 else ψ r) := by
  classical
  let ρ : Rq → ℝ := fun r ↦ if r = 0 then 0 else ψ r
  refine
    { nonneg := hπψ.nonneg
      one_le := ?_ }
  intro x y hxy
  let y' : ContAssignment := y.erase 0
  have hvec_zero (s : Rq) : ((0 : NNReal) : ℝ) • s = 0 := by
    simp
  have hψ_zero (s : Rq) : ψ s * ((0 : NNReal) : ℝ) = 0 := by
    simp
  have hρ_zero (s : Rq) : ρ s * ((0 : NNReal) : ℝ) = 0 := by
    simp [ρ]
  have hxy_balance : (x, y') ∈ mixed_integer_relaxation_set f := by
    -- Erasing the origin from the continuous part keeps the mixed balance unchanged.
    rw [mem_mixed_integer_relaxation_set_iff] at hxy ⊢
    rcases hxy with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hy_sum :
        y'.sum (fun r a ↦ (a : ℝ) • r) = y.sum (fun r a ↦ (a : ℝ) • r) := by
      have hsum :
          y.sum (fun r a ↦ (a : ℝ) • r) =
            y'.sum (fun r a ↦ (a : ℝ) • r) + (y 0 : ℝ) • (0 : Rq) := by
        simpa [y', add_comm, add_left_comm, add_assoc] using
          (Finsupp.add_sum_erase' y 0 (fun r a ↦ (a : ℝ) • r) hvec_zero).symm
      simpa using hsum.symm
    calc
      f + x.sum (fun r n ↦ (n : ℝ) • r) + y'.sum (fun r a ↦ (a : ℝ) • r) =
          f + x.sum (fun r n ↦ (n : ℝ) • r) + y.sum (fun r a ↦ (a : ℝ) • r) := by
            rw [hy_sum]
      _ = fun i ↦ (z i : ℝ) := hz
  have hcut_eq :
      x.sum (fun r n ↦ π r * (n : ℝ)) + y.sum (fun r a ↦ ρ r * (a : ℝ)) =
        x.sum (fun r n ↦ π r * (n : ℝ)) + y'.sum (fun r a ↦ ψ r * (a : ℝ)) := by
    have hy_erase :
        (y.erase 0).sum (fun r a ↦ ρ r * (a : ℝ)) =
          (y.erase 0).sum (fun r a ↦ ψ r * (a : ℝ)) := by
      refine continuousAssignmentSumEqOfEqOnSupport (y := y.erase 0) (ρ := ρ) (ψ := ψ) ?_
      intro s hs
      have hs_ne : s ≠ 0 := by
        intro hs_eq
        subst hs_eq
        simp at hs
      simp [ρ, hs_ne]
    have hy_sum :
        y.sum (fun r a ↦ ρ r * (a : ℝ)) =
          y'.sum (fun r a ↦ ψ r * (a : ℝ)) := by
      calc
        y.sum (fun r a ↦ ρ r * (a : ℝ)) =
            (y.erase 0).sum (fun r a ↦ ρ r * (a : ℝ)) + ρ 0 * (y 0 : ℝ) := by
              simpa [y', add_comm, add_left_comm, add_assoc] using
                (Finsupp.add_sum_erase' y 0 (fun r a ↦ ρ r * (a : ℝ)) hρ_zero).symm
        _ = (y.erase 0).sum (fun r a ↦ ψ r * (a : ℝ)) := by
              simpa [ρ] using hy_erase
        _ = y'.sum (fun r a ↦ ψ r * (a : ℝ)) := by
              rfl
    rw [hy_sum]
  calc
    1 ≤ x.sum (fun r n ↦ π r * (n : ℝ)) + y'.sum (fun r a ↦ ψ r * (a : ℝ)) :=
      hπψ.one_le hxy_balance
    _ = x.sum (fun r n ↦ π r * (n : ℝ)) + y.sum (fun r a ↦ ρ r * (a : ℝ)) := by
      rw [hcut_eq]

/-- Helper for Lemma 6.33: splitting the continuous coefficient at `r₁ + r₂` into coefficients at
`r₁` and `r₂` preserves mixed validity. -/
lemma mixedIntegerValidPairLowerPsiAtSum
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ)
    (r₁ r₂ : Rq) :
    IsValidGomoryJohnsonPair f π (fun r ↦ if r = r₁ + r₂ then ψ r₁ + ψ r₂ else ψ r) := by
  classical
  let ρ : Rq → ℝ := fun r ↦ if r = r₁ + r₂ then ψ r₁ + ψ r₂ else ψ r
  refine
    { nonneg := hπψ.nonneg
      one_le := ?_ }
  intro x y hxy
  let g : Rq := f + x.sum (fun r n ↦ (n : ℝ) • r)
  let a : NNReal := y (r₁ + r₂)
  let y' : ContAssignment :=
    y.erase (r₁ + r₂) + Finsupp.single r₁ a + Finsupp.single r₂ a
  have hy_feasible : IsContinuousInfiniteRelaxationFeasible g y := by
    refine ⟨?_⟩
    simpa [g, mixed_integer_relaxation_set, continuous_infinite_balance, add_assoc, add_left_comm]
      using hxy
  have hy'_balance :
      continuous_infinite_balance g y' = continuous_infinite_balance g y := by
    -- Freeze the integer part inside the shift vector `g`.
    simpa [g, y', a] using
      continuousInfiniteSplitBalance (f := g) (x := y) (r₁ := r₁) (r₂ := r₂)
  have hxy' : (x, y') ∈ mixed_integer_relaxation_set f := by
    rw [mem_mixed_integer_relaxation_set_iff]
    rcases hy_feasible.balance_mem_integerVectors with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      f + x.sum (fun r n ↦ (n : ℝ) • r) + y'.sum (fun r b ↦ (b : ℝ) • r) =
          continuous_infinite_balance g y' := by
            simp [g, continuous_infinite_balance, add_assoc]
      _ = continuous_infinite_balance g y := hy'_balance
      _ = f + x.sum (fun r n ↦ (n : ℝ) • r) + y.sum (fun r b ↦ (b : ℝ) • r) := by
            simp [g, continuous_infinite_balance, add_assoc]
      _ = fun i ↦ (z i : ℝ) := by
            simpa using hz.symm
  have hsum_support :
      y.sum (fun s b ↦ ρ s * (b : ℝ)) =
        y.sum (fun s b ↦ ψ s * (b : ℝ)) +
          (a : ℝ) * (ψ r₁ + ψ r₂ - ψ (r₁ + r₂)) := by
    -- Isolate the changed coefficient before comparing `ρ` and `ψ`.
    have hρ_zero (s : Rq) : ρ s * ((0 : NNReal) : ℝ) = 0 := by
      simp [ρ]
    have hψ_zero (s : Rq) : ψ s * ((0 : NNReal) : ℝ) = 0 := by
      simp
    rw [← Finsupp.add_sum_erase' y (r₁ + r₂) (fun s b ↦ ρ s * (b : ℝ)) hρ_zero]
    rw [← Finsupp.add_sum_erase' y (r₁ + r₂) (fun s b ↦ ψ s * (b : ℝ)) hψ_zero]
    have herase_eq :
        (y.erase (r₁ + r₂)).sum (fun s b ↦ ρ s * (b : ℝ)) =
          (y.erase (r₁ + r₂)).sum (fun s b ↦ ψ s * (b : ℝ)) := by
      refine continuousAssignmentSumEqOfEqOnSupport (y := y.erase (r₁ + r₂)) (ρ := ρ) (ψ := ψ) ?_
      intro s hs
      have hs_ne : s ≠ r₁ + r₂ := by
        intro hs_eq
        subst hs_eq
        simp at hs
      simp [ρ, hs_ne]
    rw [herase_eq]
    simp [ρ, a]
    ring
  have hy_sum :
      y'.sum (fun s b ↦ ψ s * (b : ℝ)) =
        y.sum (fun s b ↦ ψ s * (b : ℝ)) +
          (a : ℝ) * (ψ r₁ + ψ r₂ - ψ (r₁ + r₂)) := by
    -- The split weighted-sum bridge gives the same correction term.
    simpa [y', a, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      continuousInfiniteSplitWeightedSum (ρ := ψ) (x := y) (r₁ := r₁) (r₂ := r₂)
  calc
    1 ≤ x.sum (fun r n ↦ π r * (n : ℝ)) + y'.sum (fun r b ↦ ψ r * (b : ℝ)) :=
      hπψ.one_le hxy'
    _ = x.sum (fun r n ↦ π r * (n : ℝ)) + y.sum (fun r b ↦ ρ r * (b : ℝ)) := by
      rw [hy_sum, hsum_support]

/-- Helper for Lemma 6.33: moving the continuous coefficient at `r` to `c • r` with scale
`c⁻¹` preserves mixed validity. -/
lemma mixedIntegerValidPairLowerPsiAtSmul
    {f : Rq} {π ψ : Rq → ℝ} {r : Rq} {c : ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ)
    (hc : 0 < c) (hfix : c • r ≠ r) :
    IsValidGomoryJohnsonPair f π (fun s ↦ if s = r then c⁻¹ * ψ (c • r) else ψ s) := by
  classical
  let ρ : Rq → ℝ := fun s ↦ if s = r then c⁻¹ * ψ (c • r) else ψ s
  refine
    { nonneg := hπψ.nonneg
      one_le := ?_ }
  intro x y hxy
  let g : Rq := f + x.sum (fun s n ↦ (n : ℝ) • s)
  let a : NNReal := y r
  let cInv : NNReal := ⟨c⁻¹, le_of_lt (inv_pos.mpr hc)⟩
  let y' : ContAssignment := y.erase r + Finsupp.single (c • r) (cInv * a)
  have hy_feasible : IsContinuousInfiniteRelaxationFeasible g y := by
    refine ⟨?_⟩
    simpa [g, mixed_integer_relaxation_set, continuous_infinite_balance, add_assoc, add_left_comm]
      using hxy
  have hy'_balance :
      continuous_infinite_balance g y' =
        continuous_infinite_balance g y + (a : ℝ) • (c⁻¹ • (c • r) - r) := by
    -- Freeze the integer part inside the shift vector `g`.
    simpa [g, y', a, cInv] using
      continuousInfiniteScaledTransferBalance (f := g) (x := y) (r := r) (c := c) hc hfix
  have hscale : c⁻¹ • (c • r) = r := by
    rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  have hxy' : (x, y') ∈ mixed_integer_relaxation_set f := by
    rw [mem_mixed_integer_relaxation_set_iff]
    rcases hy_feasible.balance_mem_integerVectors with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    calc
      f + x.sum (fun s n ↦ (n : ℝ) • s) + y'.sum (fun s b ↦ (b : ℝ) • s) =
          continuous_infinite_balance g y' := by
            simp [g, continuous_infinite_balance, add_assoc]
      _ = continuous_infinite_balance g y := by
            simpa [hy'_balance, hscale]
      _ = f + x.sum (fun s n ↦ (n : ℝ) • s) + y.sum (fun s b ↦ (b : ℝ) • s) := by
            simp [g, continuous_infinite_balance, add_assoc]
      _ = fun i ↦ (z i : ℝ) := by
            simpa using hz.symm
  have hsum_support :
      y.sum (fun s b ↦ ρ s * (b : ℝ)) =
        y.sum (fun s b ↦ ψ s * (b : ℝ)) +
          (a : ℝ) * (c⁻¹ * ψ (c • r) - ψ r) := by
    -- Isolate the changed coefficient before comparing `ρ` and `ψ`.
    have hρ_zero (s : Rq) : ρ s * ((0 : NNReal) : ℝ) = 0 := by
      simp [ρ]
    have hψ_zero (s : Rq) : ψ s * ((0 : NNReal) : ℝ) = 0 := by
      simp
    rw [← Finsupp.add_sum_erase' y r (fun s b ↦ ρ s * (b : ℝ)) hρ_zero]
    rw [← Finsupp.add_sum_erase' y r (fun s b ↦ ψ s * (b : ℝ)) hψ_zero]
    have herase_eq :
        (y.erase r).sum (fun s b ↦ ρ s * (b : ℝ)) =
          (y.erase r).sum (fun s b ↦ ψ s * (b : ℝ)) := by
      refine continuousAssignmentSumEqOfEqOnSupport (y := y.erase r) (ρ := ρ) (ψ := ψ) ?_
      intro s hs
      have hs_ne : s ≠ r := by
        intro hs_eq
        subst hs_eq
        simp at hs
      simp [ρ, hs_ne]
    rw [herase_eq]
    simp [ρ, a]
    ring
  have hy_sum :
      y'.sum (fun s b ↦ ψ s * (b : ℝ)) =
        y.sum (fun s b ↦ ψ s * (b : ℝ)) +
          (a : ℝ) * (c⁻¹ * ψ (c • r) - ψ r) := by
    -- The scaled-transfer bridge gives the same correction term.
    simpa [y', a, cInv, mul_comm, mul_left_comm, mul_assoc] using
      continuousInfiniteScaledTransferWeightedSum
        (ρ := ψ) (x := y) (r := r) (c := c) hc hfix
  calc
    1 ≤ x.sum (fun s n ↦ π s * (n : ℝ)) + y'.sum (fun s b ↦ ψ s * (b : ℝ)) :=
      hπψ.one_le hxy'
    _ = x.sum (fun s n ↦ π s * (n : ℝ)) + y.sum (fun s b ↦ ρ s * (b : ℝ)) := by
      rw [hy_sum, hsum_support]

/-- Helper for Lemma 6.33: minimality forces `ψ 0 = 0` by forbidding the reset of the origin
coefficient to zero. -/
lemma minimalValidGomoryJohnsonPairPsiMapZero
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    ψ 0 = 0 := by
  let ρ : Rq → ℝ := fun r ↦ if r = 0 then 0 else ψ r
  have hψ0_nonneg : 0 ≤ ψ 0 := by
    let r0 : Qq := 0
    change 0 ≤ ψ ((fun _ ↦ (0 : ℝ)) : Rq)
    simpa [r0] using
      (continuousInfiniteValidFunctionNonnegOnRationalVectors
        hπψ.toContinuousValidFunction r0)
  have hρvalid : IsValidGomoryJohnsonPair f π ρ := by
    -- Route correction: lower only the continuous coefficient at the origin.
    simpa [ρ] using mixedIntegerValidPairResetPsiZero hπψ.toIsValidGomoryJohnsonPair
  have hρle : ∀ r : Rq, ρ r ≤ ψ r := by
    intro r
    by_cases hr : r = 0
    · simpa [ρ, hr] using hψ0_nonneg
    · simp [ρ, hr]
  have heq := hπψ.eq_of_le hρvalid (fun r ↦ le_rfl) hρle
  have hpoint := congrArg (fun τ : Rq → ℝ ↦ τ 0) heq.2
  simpa [ρ] using hpoint.symm

/-- Helper for Lemma 6.33: every minimal Gomory--Johnson pair has subadditive `ψ`. -/
lemma minimalValidGomoryJohnsonPairPsiSubadditive
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    ψ.Subadditive := by
  intro r₁ r₂
  by_contra hlt
  let ρ : Rq → ℝ := fun r ↦ if r = r₁ + r₂ then ψ r₁ + ψ r₂ else ψ r
  have hρvalid : IsValidGomoryJohnsonPair f π ρ := by
    -- Lower only the continuous coefficient at `r₁ + r₂`.
    simpa [ρ] using mixedIntegerValidPairLowerPsiAtSum hπψ.toIsValidGomoryJohnsonPair r₁ r₂
  have hρle : ∀ r : Rq, ρ r ≤ ψ r := by
    intro r
    by_cases hr : r = r₁ + r₂
    · have hstrict : ψ r₁ + ψ r₂ < ψ (r₁ + r₂) := lt_of_not_ge hlt
      simpa [ρ, hr] using le_of_lt hstrict
    · simp [ρ, hr]
  have heq := hπψ.eq_of_le hρvalid (fun r ↦ le_rfl) hρle
  have hpoint := congrArg (fun τ : Rq → ℝ ↦ τ (r₁ + r₂)) heq.2
  have hcontr : ψ r₁ + ψ r₂ = ψ (r₁ + r₂) := by
    simpa [ρ] using hpoint
  linarith

/-- Helper for Lemma 6.33: every minimal Gomory--Johnson pair has positively homogeneous `ψ`. -/
lemma minimalValidGomoryJohnsonPairPsiPositivelyHomogeneous
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    ψ.PositivelyHomogeneous := by
  intro r c hc
  by_cases hr : r = 0
  · -- The origin case reduces to `ψ 0 = 0`.
    simp [hr, minimalValidGomoryJohnsonPairPsiMapZero hπψ]
  by_cases hc1 : c = 1
  · simp [hc1]
  let t : Rq := c • r
  have hfix : t ≠ r := by
    intro hfix
    apply hr
    ext i
    have hi := congrArg (fun u : Rq ↦ u i) hfix
    have hi' : c * r i = r i := by
      simpa [t, Pi.smul_apply, smul_eq_mul] using hi
    have hmul : (c - 1) * r i = 0 := by
      linarith
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hc1)
  let ρ₁ : Rq → ℝ := fun s ↦ if s = r then c⁻¹ * ψ t else ψ s
  have hρ₁valid : IsValidGomoryJohnsonPair f π ρ₁ := by
    -- Lower the continuous coefficient at `r`.
    simpa [ρ₁, t] using
      mixedIntegerValidPairLowerPsiAtSmul hπψ.toIsValidGomoryJohnsonPair (r := r) (c := c) hc hfix
  have hfirst : ψ r ≤ c⁻¹ * ψ t := by
    by_contra hlt
    have hρ₁le : ∀ s : Rq, ρ₁ s ≤ ψ s := by
      intro s
      by_cases hs : s = r
      · have hstrict : c⁻¹ * ψ t < ψ r := lt_of_not_ge hlt
        simpa [ρ₁, hs] using le_of_lt hstrict
      · simp [ρ₁, hs]
    have heq := hπψ.eq_of_le hρ₁valid (fun s ↦ le_rfl) hρ₁le
    have hpoint := congrArg (fun τ : Rq → ℝ ↦ τ r) heq.2
    have hcontr : c⁻¹ * ψ t = ψ r := by
      simpa [ρ₁] using hpoint
    exact (lt_of_not_ge hlt).ne hcontr
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hc
  have hfixInv : c⁻¹ • t ≠ t := by
    intro h
    have hr_eq_t : r = t := by
      calc
        r = c⁻¹ • t := by
          simp [t, smul_smul, inv_mul_cancel₀ (ne_of_gt hc)]
        _ = t := h
    exact hfix hr_eq_t.symm
  let ρ₂ : Rq → ℝ := fun s ↦ if s = t then c * ψ r else ψ s
  have hρ₂valid : IsValidGomoryJohnsonPair f π ρ₂ := by
    -- Apply the same scaling argument at `t = c • r` with scalar `c⁻¹`.
    have hscaleInv : c⁻¹ • t = r := by
      simp [t, smul_smul, inv_mul_cancel₀ (ne_of_gt hc)]
    simpa [ρ₂, t, inv_inv, hscaleInv] using
      mixedIntegerValidPairLowerPsiAtSmul
        hπψ.toIsValidGomoryJohnsonPair (r := t) (c := c⁻¹) hcinv hfixInv
  have hsecond : ψ t ≤ c * ψ r := by
    by_contra hlt
    have hρ₂le : ∀ s : Rq, ρ₂ s ≤ ψ s := by
      intro s
      by_cases hs : s = t
      · have hstrict : c * ψ r < ψ t := lt_of_not_ge hlt
        simpa [ρ₂, hs] using le_of_lt hstrict
      · simp [ρ₂, hs]
    have heq := hπψ.eq_of_le hρ₂valid (fun s ↦ le_rfl) hρ₂le
    have hpoint := congrArg (fun τ : Rq → ℝ ↦ τ t) heq.2
    have hcontr : c * ψ r = ψ t := by
      simpa [ρ₂] using hpoint
    exact (lt_of_not_ge hlt).ne hcontr
  have hfirst' : c * ψ r ≤ ψ t := by
    calc
      c * ψ r ≤ c * (c⁻¹ * ψ t) :=
        mul_le_mul_of_nonneg_left hfirst (le_of_lt hc)
      _ = ψ t := by
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hc), one_mul]
  simpa [t, mul_comm] using le_antisymm hsecond hfirst'

/-- Helper for Lemma 6.33: every minimal Gomory--Johnson pair has sublinear `ψ`. -/
lemma minimalValidGomoryJohnsonPairPsiSublinear
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    ψ.Sublinear := by
  -- Package the mixed subadditivity and homogeneity arguments.
  refine ⟨?_, ?_⟩
  · exact minimalValidGomoryJohnsonPairPsiSubadditive hπψ
  · exact minimalValidGomoryJohnsonPairPsiPositivelyHomogeneous hπψ

/-- Helper for Lemma 6.33: every minimal Gomory--Johnson pair has pointwise nonnegative `ψ`. -/
lemma minimalValidGomoryJohnsonPairPsiNonnegative
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ)
    (r : Rq) :
    0 ≤ ψ r := by
  -- First obtain continuity from the mixed sublinear package, then extend rational nonnegativity.
  have hsublinear : ψ.Sublinear := minimalValidGomoryJohnsonPairPsiSublinear hπψ
  have hcont : Continuous ψ := Function.Sublinear.continuous hsublinear
  let φ : Qq → Rq := fun s i ↦ (s i : ℝ)
  have hDense : DenseRange φ := DenseRange.piMap fun _ ↦ Rat.denseRange_cast
  have hClosed : IsClosed {s : Rq | 0 ≤ ψ s} := by
    simpa using isClosed_Ici.preimage hcont
  have hSubset : Set.range φ ⊆ {s : Rq | 0 ≤ ψ s} := by
    rintro _ ⟨s, rfl⟩
    exact continuousInfiniteValidFunctionNonnegOnRationalVectors
      hπψ.toContinuousValidFunction s
  have hClosureSubset : closure (Set.range φ) ⊆ {s : Rq | 0 ≤ ψ s} :=
    closure_minimal hSubset hClosed
  have hr_closure : r ∈ closure (Set.range φ) := by
    simp [hDense.closure_range]
  exact hClosureSubset hr_closure

/-- Helper for Lemma 6.33: lowering `π r₀` to `ψ r₀` preserves mixed validity once `ψ r₀` is
known to be nonnegative. -/
lemma mixedIntegerValidPairLowerPiAtPointToPsi
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsValidGomoryJohnsonPair f π ψ)
    (r₀ : Rq) (hψr₀ : 0 ≤ ψ r₀) :
    IsValidGomoryJohnsonPair f (fun r ↦ if r = r₀ then ψ r₀ else π r) ψ := by
  classical
  let ρ : Rq → ℝ := fun r ↦ if r = r₀ then ψ r₀ else π r
  refine
    { nonneg := ?_
      one_le := ?_ }
  · -- Only the integer coefficient at `r₀` changes.
    intro r
    by_cases hr : r = r₀
    · simpa [ρ, hr] using hψr₀
    · simpa [ρ, hr] using hπψ.nonneg r
  · intro x y hxy
    let x' : NatAssignment := x.erase r₀
    let y' : ContAssignment := y + Finsupp.single r₀ (x r₀ : NNReal)
    have hvec_zero (s : Rq) : ((0 : ℕ) : ℝ) • s = 0 := by
      simp
    have hsum_zero (s : Rq) : ψ s * ((0 : NNReal) : ℝ) = 0 := by
      simp
    have hρ_zero (s : Rq) : ρ s * ((0 : ℕ) : ℝ) = 0 := by
      simp [ρ]
    have hxy_balance : (x', y') ∈ mixed_integer_relaxation_set f := by
      -- Remove the integer mass at `r₀` and add it back continuously.
      rw [mem_mixed_integer_relaxation_set_iff] at hxy ⊢
      rcases hxy with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      have hx_sum :
          x.sum (fun r n ↦ (n : ℝ) • r) =
            x'.sum (fun r n ↦ (n : ℝ) • r) + (x r₀ : ℝ) • r₀ := by
        simpa [x', add_comm, add_left_comm, add_assoc] using
          (Finsupp.add_sum_erase' x r₀ (fun r n ↦ (n : ℝ) • r) hvec_zero).symm
      have hy_sum :
          y'.sum (fun r a ↦ (a : ℝ) • r) =
            y.sum (fun r a ↦ (a : ℝ) • r) + (x r₀ : ℝ) • r₀ := by
        have hsingle :
            (Finsupp.single r₀ (x r₀ : NNReal)).sum (fun r a ↦ (a : ℝ) • r) =
              (x r₀ : ℝ) • r₀ := by
          rw [Finsupp.sum_single_index]
          · simp
          · simpa using hsum_zero r₀
        dsimp [y']
        rw [Finsupp.sum_add_index]
        · simpa [hsingle]
        · simpa using hsum_zero r₀
        · intro s a b₁ b₂
          simp [NNReal.coe_add, add_smul]
      calc
        f + x'.sum (fun r n ↦ (n : ℝ) • r) + y'.sum (fun r a ↦ (a : ℝ) • r) =
            f + x.sum (fun r n ↦ (n : ℝ) • r) + y.sum (fun r a ↦ (a : ℝ) • r) := by
              rw [hx_sum, hy_sum]
              abel
        _ = fun i ↦ (z i : ℝ) := hz
    have hcut_eq :
        x.sum (fun r n ↦ ρ r * (n : ℝ)) + y.sum (fun r a ↦ ψ r * (a : ℝ)) =
          x'.sum (fun r n ↦ π r * (n : ℝ)) + y'.sum (fun r a ↦ ψ r * (a : ℝ)) := by
      have hx_erase :
          x'.sum (fun r n ↦ ρ r * (n : ℝ)) =
            x'.sum (fun r n ↦ π r * (n : ℝ)) := by
        refine Finset.sum_congr rfl ?_
        intro s hs
        have hs_ne : s ≠ r₀ := by
          intro hs_eq
          subst hs_eq
          simp [x'] at hs
        simp [ρ, hs_ne]
      have hx_sum :
          x.sum (fun r n ↦ ρ r * (n : ℝ)) =
            x'.sum (fun r n ↦ π r * (n : ℝ)) + ψ r₀ * (x r₀ : ℝ) := by
        calc
          x.sum (fun r n ↦ ρ r * (n : ℝ)) =
              x'.sum (fun r n ↦ ρ r * (n : ℝ)) + ρ r₀ * (x r₀ : ℝ) := by
                simpa [x', add_comm, add_left_comm, add_assoc] using
                  (Finsupp.add_sum_erase' x r₀ (fun r n ↦ ρ r * (n : ℝ)) hρ_zero).symm
          _ = x'.sum (fun r n ↦ π r * (n : ℝ)) + ψ r₀ * (x r₀ : ℝ) := by
                simpa [ρ] using congrArg (fun t : ℝ ↦ t + ψ r₀ * (x r₀ : ℝ)) hx_erase
      have hy_sum :
          y'.sum (fun r a ↦ ψ r * (a : ℝ)) =
            y.sum (fun r a ↦ ψ r * (a : ℝ)) + ψ r₀ * (x r₀ : ℝ) := by
        have hsingle :
            (Finsupp.single r₀ (x r₀ : NNReal)).sum (fun r a ↦ ψ r * (a : ℝ)) =
              ψ r₀ * (x r₀ : ℝ) := by
          rw [Finsupp.sum_single_index]
          · simp
          · simpa using hsum_zero r₀
        dsimp [y']
        rw [Finsupp.sum_add_index]
        · simpa [hsingle]
        · simpa using hsum_zero r₀
        · intro s a b₁ b₂
          simp [NNReal.coe_add, left_distrib]
      calc
        x.sum (fun r n ↦ ρ r * (n : ℝ)) + y.sum (fun r a ↦ ψ r * (a : ℝ)) =
            x'.sum (fun r n ↦ π r * (n : ℝ)) + ψ r₀ * (x r₀ : ℝ) +
              y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
              rw [hx_sum]
        _ = x'.sum (fun r n ↦ π r * (n : ℝ)) + y'.sum (fun r a ↦ ψ r * (a : ℝ)) := by
              rw [hy_sum]
              ring
    calc
      1 ≤ x'.sum (fun r n ↦ π r * (n : ℝ)) + y'.sum (fun r a ↦ ψ r * (a : ℝ)) :=
        hπψ.one_le hxy_balance
      _ = x.sum (fun r n ↦ ρ r * (n : ℝ)) + y.sum (fun r a ↦ ψ r * (a : ℝ)) := by
        rw [hcut_eq]

/-- Lemma 6.33 (1). Let `(π, ψ)` be a minimal valid function for `M_f`. Then `π ≤ ψ`. -/
theorem minimal_valid_gomory_johnson_pair_pi_le_psi
    (f : Rq) (π ψ : Rq → ℝ)
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    π ≤ ψ := by
  intro r₀
  by_contra hgt
  let ρ : Rq → ℝ := fun r ↦ if r = r₀ then ψ r₀ else π r
  have hρvalid : IsValidGomoryJohnsonPair f ρ ψ := by
    -- Lower the integer coefficient at `r₀`, now using the earlier proof that `ψ r₀ ≥ 0`.
    simpa [ρ] using
      mixedIntegerValidPairLowerPiAtPointToPsi
        hπψ.toIsValidGomoryJohnsonPair r₀
        (minimalValidGomoryJohnsonPairPsiNonnegative hπψ r₀)
  have hρle : ∀ r : Rq, ρ r ≤ π r := by
    intro r
    by_cases hr : r = r₀
    · have hstrict : ψ r₀ < π r₀ := lt_of_not_ge hgt
      simpa [ρ, hr] using le_of_lt hstrict
    · simp [ρ, hr]
  have heq := hπψ.eq_of_le hρvalid hρle (fun r ↦ le_rfl)
  have hpoint := congrArg (fun τ : Rq → ℝ ↦ τ r₀) heq.1
  have hcontr : ψ r₀ = π r₀ := by
    simpa [ρ] using hpoint
  exact (lt_of_not_ge hgt).ne hcontr

namespace IsMinimalValidGomoryJohnsonPair

/-- Helper for Lemma 6.33: a minimal Gomory--Johnson pair restricts to a valid function on the
continuous relaxation. -/
theorem toContinuousValidFunction
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    IsValidFunctionForContinuousInfiniteRelaxation f ψ :=
  hπψ.toIsValidGomoryJohnsonPair.toContinuousValidFunction

end IsMinimalValidGomoryJohnsonPair

/-- Lemma 6.33 (2). Let `(π, ψ)` be a minimal valid function for `M_f`. Then `ψ` is pointwise
nonnegative. -/
theorem minimal_valid_gomory_johnson_pair_psi_nonnegative
    (f : Rq) (π ψ : Rq → ℝ)
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ)
    (r : Rq) :
    0 ≤ ψ r :=
  minimalValidGomoryJohnsonPairPsiNonnegative hπψ r

/-- Lemma 6.33 (3). Let `(π, ψ)` be a minimal valid function for `M_f`. Then `ψ` is sublinear. -/
theorem minimal_valid_gomory_johnson_pair_psi_sublinear
    (f : Rq) (π ψ : Rq → ℝ)
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    ψ.Sublinear :=
  minimalValidGomoryJohnsonPairPsiSublinear hπψ

namespace IsMinimalValidGomoryJohnsonPair

/-- Lemma 6.33 (1) in callable namespace form. -/
theorem pi_le_psi
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    π ≤ ψ :=
  minimal_valid_gomory_johnson_pair_pi_le_psi f π ψ hπψ

/-- A minimal Gomory--Johnson pair has pointwise nonnegative `ψ`. -/
theorem psi_nonnegative
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) (r : Rq) :
    0 ≤ ψ r :=
  minimal_valid_gomory_johnson_pair_psi_nonnegative f π ψ hπψ r

/-- A minimal Gomory--Johnson pair has sublinear `ψ`. -/
theorem psi_sublinear
    {f : Rq} {π ψ : Rq → ℝ}
    (hπψ : IsMinimalValidGomoryJohnsonPair f π ψ) :
    ψ.Sublinear :=
  minimal_valid_gomory_johnson_pair_psi_sublinear f π ψ hπψ

end IsMinimalValidGomoryJohnsonPair

end Lemma633
