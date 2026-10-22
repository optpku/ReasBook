/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_49

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise Set

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: the singleton hypothesis on `C` identifies `A + N[C]` with the canonical owner
-- `ofFunction C T + N[C]`, since the normal cone is empty off `C`. Extend the continuous subtype
-- map `T : C → H` to an ambient map that agrees with it on `C`, derive Rockafellar
-- hemicontinuity on `C`, apply Proposition 20.49 to the restricted singleton operator, and then
-- rewrite the result back to `A + N[C]`.
/-- Corollary 20.50: if `C` is a nonempty closed convex subset of a real Hilbert space, if `A` is
a set-valued operator, and if `A` coincides on `C` with a continuous single-valued map whose
restricted singleton-valued operator is monotone, then `A + N[C]` is maximally monotone. -/
theorem add_normalCone_isMaximallyMonotone_of_monotone_of_eq_singleton_continuous
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (A : SetValuedOperator H H) (T : C → H) (hT_mono : (ofFunction C T).IsMonotone)
    (hA_eq : ∀ x : C, A x = ({T x} : Set H)) (hT_cont : Continuous T) :
    Maximal IsMonotone (A + N[C]) := by
  let T' : H → H := Function.extend Subtype.val T (fun _ ↦ (0 : H))
  have hT'_restrict : C.restrict T' = T := by
    funext x
    change T' x = T x
    exact Subtype.val_injective.extend_apply T (fun _ ↦ (0 : H)) x
  have hT'_cont : ContinuousOn T' C := by
    rw [continuousOn_iff_continuous_restrict]
    simpa [hT'_restrict] using hT_cont
  have hT'_ofFunction : ofFunction C (fun x : C ↦ T' x) = ofFunction C T := by
    ext x u
    by_cases hx : x ∈ C
    · have hTx : T' x = T ⟨x, hx⟩ := by
        simpa [T'] using
          (Subtype.val_injective.extend_apply T (fun _ ↦ (0 : H)) ⟨x, hx⟩)
      simp [ofFunction_apply_of_mem, hx, hTx]
    · simp [ofFunction_apply_of_not_mem, hx]
  have hT'_mono : (ofFunction C (fun x : C ↦ T' x)).IsMonotone := by
    simpa [hT'_ofFunction] using hT_mono
  have hT'_hemi : T'.IsHemicontinuousOn C := by
    intro x y z
    let γ : ℝ → H := AffineMap.lineMap (x : H) y
    have hγ_cont : Continuous γ := AffineMap.lineMap_continuous
    have hγ_maps : Set.MapsTo γ (Set.Icc (0 : ℝ) 1) C := hC_convex.mapsTo_lineMap x.2 y.2
    have hTγ_cont : ContinuousOn (T' ∘ γ) (Set.Icc (0 : ℝ) 1) := by
      exact hT'_cont.comp hγ_cont.continuousOn hγ_maps
    have hinner_cont :
        ContinuousOn (fun α : ℝ ↦ ⟪z, T' (γ α)⟫_ℝ) (Set.Icc (0 : ℝ) 1) :=
      continuousOn_const.inner hTγ_cont
    have hinner_zero :
        ContinuousWithinAt (fun α : ℝ ↦ ⟪z, T' (γ α)⟫_ℝ) (Set.Icc (0 : ℝ) 1) 0 :=
      hinner_cont 0 <| by simp
    have hIcc : Set.Icc (0 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := by
      refine mem_nhdsWithin_iff_exists_mem_nhds_inter.2 ?_
      refine ⟨Set.Iio (1 : ℝ), Iio_mem_nhds zero_lt_one, ?_⟩
      intro α hα
      exact ⟨le_of_lt hα.2, le_of_lt hα.1⟩
    simpa [Function.IsHemicontinuousOn, ContinuousWithinAt, γ, AffineMap.lineMap_apply_module] using
      hinner_zero.mono_of_mem_nhdsWithin hIcc
  have hsum :
      A + N[C] = ofFunction C T + N[C] := by
    ext x u
    by_cases hx : x ∈ C
    · have hAx : A x = ({T ⟨x, hx⟩} : Set H) := hA_eq ⟨x, hx⟩
      simp [hAx, ofFunction_apply_of_mem, hx]
    · simp [ofFunction_apply_of_not_mem, Set.normalCone_of_not_mem, hx]
  simpa [hsum, hT'_ofFunction] using
    Function.ofFunction_add_normalCone_isMaximallyMonotone_of_monotoneOn_hemicontinuousOn
      hC_nonempty hC_closed hC_convex T' hT'_mono hT'_hemi

end SetValuedOperator
