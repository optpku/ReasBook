/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Corollary_9_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators InnerProductSpace

universe u v

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {I : Type v}

/-- Helper for Example 9.13: precomposition with a continuous linear map preserves `γ`. -/
theorem mem_gamma_comp_continuousLinearMap_local
    {K : Type*} {L : Type*}
    [NormedAddCommGroup K] [NormedSpace ℝ K]
    [NormedAddCommGroup L] [NormedSpace ℝ L]
    (f : L → EReal) (T : K →L[ℝ] L) (hf : f ∈ gamma L) :
    f ∘ T ∈ gamma K := by
  rw [mem_gamma_iff] at hf ⊢
  rcases hf with ⟨hf_convex, hf_lsc⟩
  refine ⟨?_, ?_⟩
  · -- Jensen convexity is preserved because linear maps commute with affine combinations.
    intro x y a ha0 ha1
    simpa [Function.comp, map_add, map_smul] using
      hf_convex (x := T x) (y := T y) (a := a) ha0 ha1
  · -- Lower semicontinuity is preserved under composition with the continuous map `T`.
    exact hf_lsc.comp T.continuous

-- Proof sketch: `hφ_zero` and `hφ_nonneg` imply that every coordinate term
-- `φ i ⟪x, e i⟫_ℝ` is nonnegative. Then every finite partial sum is nonnegative, so the finite
-- branch or supremum branch of `familySum` is strictly above `⊥`.
/-- The source-defined coordinate sum attached to a nonnegative family `φ i` never attains `-∞`. -/
theorem innerProductFamilySum_mem_Ioi_bot
    (e : I → H) (φ : I → ℝ → Set.Ioi (⊥ : EReal))
    (hφ_zero : ∀ i, (φ i 0 : EReal) = 0)
    (hφ_nonneg : ∀ i t, (φ i 0 : EReal) ≤ (φ i t : EReal))
    (x : H) :
    familySum (fun i y ↦ (φ i ⟪y, e i⟫_ℝ : EReal)) x ∈ Set.Ioi (⊥ : EReal) := by
  classical
  have hnonneg :
      (0 : EReal) ≤ familySum (fun i y ↦ (φ i ⟪y, e i⟫_ℝ : EReal)) x := by
    by_cases hI : Finite I
    · let _ : Finite I := hI
      let _ : Fintype I := Fintype.ofFinite I
      -- In the finite case, `familySum` is the ordinary finite sum of nonnegative terms.
      have hsum : (0 : EReal) ≤ ∑ i, (φ i ⟪x, e i⟫_ℝ : EReal) := by
        exact Finset.sum_nonneg fun i _ ↦ by
          simpa [hφ_zero i] using hφ_nonneg i ⟪x, e i⟫_ℝ
      simpa [familySum, hI] using hsum
    · -- In the infinite case, it is enough to exhibit one nonempty partial sum above `0`.
      rw [familySum_eq_iSup_nonemptyFinitePartialSums
        (fun i y ↦ (φ i ⟪y, e i⟫_ℝ : EReal)) hI]
      have hI_nonempty : Nonempty I := by
        by_cases hne : Nonempty I
        · exact hne
        · haveI : IsEmpty I := not_nonempty_iff.mp hne
          haveI : Fintype I := Fintype.ofIsEmpty
          exact False.elim (hI (Finite.of_fintype I))
      obtain ⟨i₀⟩ := hI_nonempty
      let J : {s : Finset I // s.Nonempty} := ⟨{i₀}, by simp⟩
      have hJ_nonneg :
          (0 : EReal) ≤
            Finset.sum (J : Finset I) (fun i ↦ (φ i ⟪x, e i⟫_ℝ : EReal)) := by
        -- Every term in the chosen nonempty finite sum is nonnegative.
        exact Finset.sum_nonneg fun i _ ↦ by
          simpa [hφ_zero i] using hφ_nonneg i ⟪x, e i⟫_ℝ
      exact hJ_nonneg.trans (le_iSup (fun J : {s : Finset I // s.Nonempty} ↦
        Finset.sum (J : Finset I) (fun i ↦ (φ i ⟪x, e i⟫_ℝ : EReal))) J)
  -- Any value bounded below by `0` is strictly above `⊥`.
  exact lt_of_lt_of_le (by simp : (⊥ : EReal) < 0) hnonneg

/-- The `]-∞,+∞]`-valued function obtained by summing the coordinate functions
`x ↦ φ i ⟪x, e i⟫_ℝ` via the Chapter 9 family-sum construction. -/
noncomputable def innerProductSeriesFunction
    (e : I → H) (φ : I → ℝ → Set.Ioi (⊥ : EReal))
    (hφ_zero : ∀ i, (φ i 0 : EReal) = 0)
    (hφ_nonneg : ∀ i t, (φ i 0 : EReal) ≤ (φ i t : EReal)) :
    H → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    ⟨familySum (fun i y ↦ (φ i ⟪y, e i⟫_ℝ : EReal)) x,
      innerProductFamilySum_mem_Ioi_bot e φ hφ_zero hφ_nonneg x⟩

/-- Coercing `innerProductSeriesFunction` to `EReal` recovers the family sum of the coordinate
values. -/
@[simp] theorem innerProductSeriesFunction_apply
    (e : I → H) (φ : I → ℝ → Set.Ioi (⊥ : EReal))
    (hφ_zero : ∀ i, (φ i 0 : EReal) = 0)
    (hφ_nonneg : ∀ i t, (φ i 0 : EReal) ≤ (φ i t : EReal))
    (x : H) :
    (innerProductSeriesFunction e φ hφ_zero hφ_nonneg x : EReal) =
      familySum (fun i y ↦ (φ i ⟪y, e i⟫_ℝ : EReal)) x := rfl

/-- Helper for Example 9.13: each coordinate function `x ↦ φ i ⟪x, e i⟫_ℝ` belongs to `γ(H)`. -/
theorem innerProductCoordinate_mem_gamma
    (e : I → H) (φ : I → ℝ → Set.Ioi (⊥ : EReal))
    (hφ : ∀ i, φ i ∈ Γ₀(ℝ)) (i : I) :
    (fun x : H ↦ (φ i ⟪x, e i⟫_ℝ : EReal)) ∈ gamma H := by
  have hbase : (φ i).asEReal ∈ gamma ℝ :=
    asEReal_mem_gamma_of_mem_gammaZero (hφ i)
  have hcomp : (φ i).asEReal ∘ InnerProductSpace.toDual ℝ H (e i) ∈ gamma H :=
    mem_gamma_comp_continuousLinearMap_local
      (φ i).asEReal (InnerProductSpace.toDual ℝ H (e i)) hbase
  have hfun :
      ((φ i).asEReal ∘ InnerProductSpace.toDual ℝ H (e i)) =
        (fun x : H ↦ (φ i ⟪x, e i⟫_ℝ : EReal)) := by
    ext x
    simp [Function.comp, InnerProductSpace.toDual_apply_apply, real_inner_comm]
  -- Specialize the general composition lemma to the inner-product coordinate map.
  rw [hfun] at hcomp
  exact hcomp

/-- Helper for Example 9.13: the coordinate-sum function takes the value `0` at the origin. -/
theorem innerProductSeriesFunction_zero
    (e : I → H) (φ : I → ℝ → Set.Ioi (⊥ : EReal))
    (hφ_zero : ∀ i, (φ i 0 : EReal) = 0)
    (hφ_nonneg : ∀ i t, (φ i 0 : EReal) ≤ (φ i t : EReal)) :
    (innerProductSeriesFunction e φ hφ_zero hφ_nonneg 0 : EReal) = 0 := by
  classical
  -- Reduce to the family-sum definition and evaluate every coordinate term at `0`.
  rw [innerProductSeriesFunction_apply]
  by_cases hI : Finite I
  · let _ : Finite I := hI
    let _ : Fintype I := Fintype.ofFinite I
    have hsum :
        (familySum (fun i y ↦ (φ i ⟪y, e i⟫_ℝ : EReal)) 0 : EReal) =
          ∑ i, (φ i ⟪(0 : H), e i⟫_ℝ : EReal) := by
      simp [familySum, hI]
    rw [hsum]
    simp [hφ_zero]
  · rw [familySum_eq_iSup_nonemptyFinitePartialSums
      (fun i y ↦ (φ i ⟪y, e i⟫_ℝ : EReal)) hI]
    have hI_nonempty : Nonempty I := by
      by_cases hne : Nonempty I
      · exact hne
      · haveI : IsEmpty I := not_nonempty_iff.mp hne
        haveI : Fintype I := Fintype.ofIsEmpty
        exact False.elim (hI (Finite.of_fintype I))
    obtain ⟨i₀⟩ := hI_nonempty
    let J : {s : Finset I // s.Nonempty} := ⟨{i₀}, by simp⟩
    refine le_antisymm ?_ ?_
    · refine iSup_le fun J ↦ ?_
      simp [hφ_zero]
    · have hJ :
          (0 : EReal) ≤
            Finset.sum (J : Finset I) (fun i ↦ (φ i ⟪(0 : H), e i⟫_ℝ : EReal)) := by
        simp [J, hφ_zero]
      exact hJ.trans (le_iSup (fun J : {s : Finset I // s.Nonempty} ↦
        Finset.sum (J : Finset I) (fun i ↦ (φ i ⟪(0 : H), e i⟫_ℝ : EReal))) J)

-- Proof sketch: for each `i`, compose `φ i ∈ Γ₀(ℝ)` with the continuous linear functional
-- `x ↦ ⟪x, e i⟫_ℝ` to obtain a member of `Γ₀(H)`. The assumptions `φ i(0) = 0` and
-- `φ i(0) ≤ φ i(t)` make each coordinate function pointwise nonnegative, so Corollary 9.4
-- applies to the resulting family.
/-- Example 9.13: if each `φ i` belongs to `Γ₀(ℝ)` and satisfies `φ i ≥ φ i(0) = 0`, then the
function obtained by summing the coordinate values `φ i ⟪x, e i⟫_ℝ` belongs to `Γ₀(H)`. -/
theorem innerProductSeriesFunction_mem_gammaZero
    (e : I → H) (φ : I → ℝ → Set.Ioi (⊥ : EReal))
    (hφ : ∀ i, φ i ∈ Γ₀(ℝ))
    (hφ_zero : ∀ i, (φ i 0 : EReal) = 0)
    (hφ_nonneg : ∀ i t, (φ i 0 : EReal) ≤ (φ i t : EReal)) :
    innerProductSeriesFunction e φ hφ_zero hφ_nonneg ∈ Γ₀(H) := by
  have hsum_gamma :
      familySum (fun i y ↦ (φ i ⟪y, e i⟫_ℝ : EReal)) ∈ gamma H := by
    -- Each coordinate term lies in `γ(H)`, and the family is pointwise nonnegative.
    refine familySum_mem_gamma
      (fun i y ↦ (φ i ⟪y, e i⟫_ℝ : EReal))
      (fun i ↦ innerProductCoordinate_mem_gamma e φ hφ i)
      (Or.inr ?_)
    intro i x
    simpa [hφ_zero i] using hφ_nonneg i ⟪x, e i⟫_ℝ
  have hsum_convex :
      IsConvex (familySum (fun i y ↦ (φ i ⟪y, e i⟫_ℝ : EReal))) :=
    (mem_gamma_iff _).mp hsum_gamma |>.1
  have hsum_lsc :
      LowerSemicontinuous (familySum (fun i y ↦ (φ i ⟪y, e i⟫_ℝ : EReal))) :=
    (mem_gamma_iff _).mp hsum_gamma |>.2
  rw [mem_gammaZero_iff]
  refine ⟨?_, ?_⟩
  · -- Lower semicontinuity is already part of the `gamma` conclusion.
    simpa [innerProductSeriesFunction_apply] using hsum_lsc
  · refine ⟨?_, subset_rfl, ?_⟩
    · -- The origin provides a concrete point of the effective domain.
      refine ⟨0, ?_⟩
      rw [mem_effectiveDomain_iff, innerProductSeriesFunction_zero e φ hφ_zero hφ_nonneg]
      exact EReal.coe_lt_top 0
    · intro x hx y hy a ha0 ha1
      -- Restrict the global Jensen inequality from `gamma` to the effective domain.
      simpa [innerProductSeriesFunction_apply] using
        hsum_convex (x := x) (y := y) (a := a) ha0.le ha1.le

end ERealFunction
