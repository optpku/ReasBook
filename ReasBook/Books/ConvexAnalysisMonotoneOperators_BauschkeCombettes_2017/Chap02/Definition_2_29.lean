/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v w

/-- Definition 2.29: for a real or complex Hilbert space `E`, the Hilbert space endowed with its
weak topology is the canonical mathlib type `WeakSpace 𝕜 E`, namely `E` equipped with the coarsest
topology making all continuous linear functionals continuous. -/
-- Proof sketch: use the defining induced-topology characterization of `WeakSpace 𝕜 E`; continuity
-- into the weak topology is equivalent to continuity after composing with every weak evaluation
-- map, and these evaluation maps are exactly `x ↦ l x` for `l : WeakDual 𝕜 E`.
theorem continuous_iff_forall_weakDual_apply
    {𝕜 : Type u} {E : Type v} {α : Type w} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [TopologicalSpace α] {f : α → WeakSpace 𝕜 E} :
    Continuous f ↔
      ∀ l : WeakDual 𝕜 E, Continuous fun a ↦ l ((toWeakSpace 𝕜 E).symm (f a)) := by
  constructor
  · intro hf l
    simpa only [LinearMap.flip_apply, topDualPairing_apply, toWeakSpace] using
      (WeakBilin.eval_continuous ((topDualPairing 𝕜 E).flip) l).comp hf
  · intro h
    exact WeakBilin.continuous_of_continuous_eval ((topDualPairing 𝕜 E).flip) fun l ↦ by
      simpa only [LinearMap.flip_apply, topDualPairing_apply, toWeakSpace] using h l

/-- For a Hilbert space with its weak topology, each scalar-valued inner-product functional
`x ↦ ⟪x, y⟫` is continuous. -/
-- Proof sketch: transport `x` back to `E` using `(toWeakSpace 𝕜 E).symm`, write the resulting map
-- as scalar conjugation composed with evaluation at `InnerProductSpace.toDual 𝕜 E y`, and then use
-- the defining continuity of evaluations on `WeakSpace 𝕜 E`.
private lemma continuous_inner_right
    {𝕜 : Type u} {E : Type v} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace E] (y : E) :
    Continuous fun x : WeakSpace 𝕜 E ↦ inner 𝕜 ((toWeakSpace 𝕜 E).symm x) y := by
  have hEval :
      Continuous fun x : WeakSpace 𝕜 E ↦
        InnerProductSpace.toDual 𝕜 E y ((toWeakSpace 𝕜 E).symm x) := by
    simpa only [LinearMap.flip_apply, topDualPairing_apply, toWeakSpace,
      InnerProductSpace.toDual_apply_apply] using
      WeakBilin.eval_continuous ((topDualPairing 𝕜 E).flip) (InnerProductSpace.toDual 𝕜 E y)
  have hconj :
      Continuous fun x : WeakSpace 𝕜 E ↦
        starRingEnd 𝕜 (InnerProductSpace.toDual 𝕜 E y ((toWeakSpace 𝕜 E).symm x)) :=
    RCLike.continuous_conj.comp hEval
  convert hconj using 1
  ext x
  simp [InnerProductSpace.toDual_apply_apply, inner_conj_symm]

/-- A map into a Hilbert space equipped with its weak topology is continuous exactly when all of
its scalar inner products against fixed vectors are continuous. -/
-- Proof sketch: one direction composes with `weakSpace_continuous_inner_right`; for the converse,
-- recover continuity of all weak evaluation maps via Fréchet-Riesz, expressing each continuous
-- linear functional as `x ↦ conj (⟪x, y⟫)` for a suitable `y`.
theorem continuous_iff_forall_inner_right
    {𝕜 : Type u} {E : Type v} {α : Type w} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] [TopologicalSpace α] {f : α → WeakSpace 𝕜 E} :
    Continuous f ↔
      ∀ y : E, Continuous fun a ↦ inner 𝕜 ((toWeakSpace 𝕜 E).symm (f a)) y := by
  constructor
  · intro hf y
    exact (continuous_inner_right y).comp hf
  · intro h
    rw [continuous_iff_forall_weakDual_apply]
    intro l
    let y : E := (InnerProductSpace.toDual 𝕜 E).symm (WeakDual.toStrongDual l)
    have hy :
        Continuous fun a ↦ inner 𝕜 ((toWeakSpace 𝕜 E).symm (f a)) y :=
      h y
    have hconj :
        Continuous fun a ↦ starRingEnd 𝕜 (inner 𝕜 ((toWeakSpace 𝕜 E).symm (f a)) y) :=
      RCLike.continuous_conj.comp hy
    simpa only [y, WeakDual.toStrongDual_apply, InnerProductSpace.toDual_symm_apply,
      inner_conj_symm] using hconj
