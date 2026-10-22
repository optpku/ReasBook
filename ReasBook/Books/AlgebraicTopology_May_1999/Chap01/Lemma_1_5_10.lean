/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Definition_1_5_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Path.Homotopic.Quotient

/-- Lemma 1.5.10: the lift-index map `j : π₁(S¹, 1) → ℤ`, represented by
`circleFundamentalGroupLiftIndex`, is injective. -/
-- Proof sketch: represent loop classes by actual loops, lift both loops through the covering map
-- `Real.fourierChar : ℝ → S¹` starting at `0`, and use equality of lift indices to identify their
-- endpoints. Since `ℝ` is simply connected, the two lifted paths are homotopic; mapping that
-- homotopy down to `S¹` shows the original loops are homotopic.
theorem circleFundamentalGroupLiftIndex_injective :
    Function.Injective circleFundamentalGroupLiftIndex := by
  change Function.Injective
    (fun γ : Path.Homotopic.Quotient (1 : Circle) (1 : Circle) ↦
      circleFundamentalGroupLiftIndex γ)
  intro γ₀ γ₁ hγ
  revert hγ
  refine Quotient.inductionOn₂ γ₀ γ₁ ?_
  intro p₀ p₁ h
  let expMap : C(ℝ, Circle) := ⟨Real.fourierChar, Real.continuous_fourierChar⟩
  let g₀ : Path (0 : ℝ) ((circleFundamentalGroupLiftIndex ⟦p₀⟧ : ℤ) : ℝ) :=
    { toContinuousMap :=
        real_fourierChar_isCoveringMap.liftPath p₀.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero p₀)
      source' := by
        simpa using real_fourierChar_isCoveringMap.liftPath_zero p₀.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero p₀)
      target' := by
        symm
        simpa using circleFundamentalGroupLiftIndex_spec p₀ }
  let g₁ : Path (0 : ℝ) ((circleFundamentalGroupLiftIndex ⟦p₁⟧ : ℤ) : ℝ) :=
    { toContinuousMap :=
        real_fourierChar_isCoveringMap.liftPath p₁.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero p₁)
      source' := by
        simpa using real_fourierChar_isCoveringMap.liftPath_zero p₁.toContinuousMap 0
          (circle_path_start_eq_fourierChar_zero p₁)
      target' := by
        symm
        simpa using circleFundamentalGroupLiftIndex_spec p₁ }
  have hcast :
      (((circleFundamentalGroupLiftIndex ⟦p₀⟧ : ℤ) : ℝ)) =
        (((circleFundamentalGroupLiftIndex ⟦p₁⟧ : ℤ) : ℝ)) := by
    exact congrArg (fun n : ℤ ↦ (n : ℝ)) h
  let g₁' : Path (0 : ℝ) ((circleFundamentalGroupLiftIndex ⟦p₀⟧ : ℤ) : ℝ) :=
    Path.cast g₁ rfl hcast
  have hhom : g₀.Homotopic g₁' := SimplyConnectedSpace.paths_homotopic g₀ g₁'
  have hstart : expMap 0 = (1 : Circle) := by
    simp [expMap]
  have hend : expMap (((circleFundamentalGroupLiftIndex ⟦p₀⟧ : ℤ) : ℝ)) = (1 : Circle) := by
    change Real.fourierChar (((circleFundamentalGroupLiftIndex ⟦p₀⟧ : ℤ) : ℝ)) = (1 : Circle)
    simpa [Real.fourierChar_apply', mul_assoc, mul_comm, mul_left_comm] using
      Circle.exp_two_pi_mul_int (circleFundamentalGroupLiftIndex ⟦p₀⟧)
  have hmap :
      (Path.cast (g₀.map expMap.continuous) hstart.symm hend.symm).Homotopic
        (Path.cast (g₁'.map expMap.continuous) hstart.symm hend.symm) := by
    simpa [hstart, hend] using Path.Homotopic.map hhom expMap
  have hg₀ : Path.cast (g₀.map expMap.continuous) hstart.symm hend.symm = p₀ := by
    apply Path.ext
    funext s
    exact congrFun (real_fourierChar_isCoveringMap.liftPath_lifts p₀.toContinuousMap 0
      (circle_path_start_eq_fourierChar_zero p₀)) s
  have hg₁ : Path.cast (g₁'.map expMap.continuous) hstart.symm hend.symm = p₁ := by
    apply Path.ext
    funext s
    change Real.fourierChar (g₁ s) = p₁ s
    exact congrFun (real_fourierChar_isCoveringMap.liftPath_lifts p₁.toContinuousMap 0
      (circle_path_start_eq_fourierChar_zero p₁)) s
  rw [← hg₀, ← hg₁]
  exact eq.2 hmap
