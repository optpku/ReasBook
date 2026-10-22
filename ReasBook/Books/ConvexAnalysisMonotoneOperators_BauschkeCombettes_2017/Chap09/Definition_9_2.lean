/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

namespace ERealFunction

variable {H : Type u}

/-- Jensen convexity for an extended-real-valued function on a real module. -/
def IsConvex [AddCommMonoid H] [Module ℝ H] (f : H → EReal) : Prop :=
  ∀ ⦃x y : H⦄ ⦃a : ℝ⦄, 0 ≤ a → a ≤ 1 →
    f (a • x + (1 - a) • y) ≤ (a : EReal) * f x + (1 - a : EReal) * f y

/-- Definition 9.2: `gamma H` is the textbook class `Γ(ℋ)` of extended-real-valued functions on a
real sequential topological module that are convex and lower semicontinuous. -/
def gamma (H : Type u) [TopologicalSpace H] [SequentialSpace H] [AddCommMonoid H] [Module ℝ H] :
    Set (H → EReal) :=
  {f | IsConvex f ∧ LowerSemicontinuous f}

notation "Γ(" H ")" => gamma H

/-- Membership in `Γ(H)` means Jensen convexity and lower semicontinuity. -/
-- Proof sketch: unfold `gamma`.
theorem mem_gamma_iff [TopologicalSpace H] [SequentialSpace H] [AddCommMonoid H] [Module ℝ H]
    (f : H → EReal) :
    f ∈ Γ(H) ↔ IsConvex f ∧ LowerSemicontinuous f := by
  -- Unfold `gamma` so that membership is exactly the pair of textbook conditions.
  rfl

/-- Multiplying a member of `Γ(ℋ)` by a nonnegative real scalar again yields a member of
`Γ(ℋ)`. -/
theorem const_mul_mem_gamma_of_nonneg
    [TopologicalSpace H] [SequentialSpace H] [AddCommMonoid H] [Module ℝ H]
    {f : H → EReal} (hf : f ∈ Γ(H)) {a : ℝ} (ha : 0 ≤ a) :
    (fun x ↦ (a : EReal) * f x) ∈ Γ(H) := by
  rw [mem_gamma_iff] at hf ⊢
  rcases hf with ⟨hf_convex, hf_lsc⟩
  refine ⟨?_, ?_⟩
  · intro x y b hb0 hb1
    calc
      (a : EReal) * f (b • x + (1 - b) • y) ≤
          (a : EReal) * ((b : EReal) * f x + (1 - b : EReal) * f y) := by
            exact mul_le_mul_of_nonneg_left (hf_convex hb0 hb1) (by exact_mod_cast ha)
      _ = (b : EReal) * ((a : EReal) * f x) + (1 - b : EReal) * ((a : EReal) * f y) := by
            rw [EReal.left_distrib_of_nonneg_of_ne_top (by exact_mod_cast ha) (EReal.coe_ne_top a)]
            congr 1 <;> ac_rfl
  · rw [lowerSemicontinuous_iff_le_liminf]
    intro x
    have haE : (0 : EReal) ≤ (a : EReal) := by
      exact_mod_cast ha
    calc
      (a : EReal) * f x ≤ (a : EReal) * Filter.liminf f (nhds x) :=
        (monotone_mul_left_of_nonneg haE) (hf_lsc.le_liminf x)
      _ = Filter.liminf (fun y ↦ (a : EReal) * f y) (nhds x) := by
        symm
        exact EReal.liminf_const_mul_of_nonneg_of_ne_top haE (EReal.coe_ne_top a)

/-- Helper for Definition 9.2: on a sequential space, lower semicontinuity is equivalent to the
sequential liminf inequality along convergent sequences. -/
-- Proof sketch: compare the neighborhood liminf with the sequence liminf in one direction, and
-- recover lower semicontinuity from sequentially closed sublevel sets in the other direction.
theorem lowerSemicontinuous_iff_seq_tendsto_le_liminf [TopologicalSpace H] [SequentialSpace H]
    (f : H → EReal) :
    LowerSemicontinuous f ↔
      ∀ ⦃x : H⦄ ⦃u : ℕ → H⦄,
        Tendsto u atTop (nhds x) → f x ≤ liminf (f ∘ u) atTop := by
  constructor
  · intro hf x u hu
    -- Compare the ambient neighborhood filter with the sequence filter induced by `u`.
    calc
      f x ≤ liminf f (nhds x) := hf.le_liminf x
      _ ≤ liminf f (Filter.map u atTop) := Filter.liminf_le_liminf_of_le hu
      _ = liminf (f ∘ u) atTop := by rw [Filter.liminf_comp]
  · intro hseq
    -- Route correction: prove lower semicontinuity through closed sublevel sets.
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro y
    apply IsSeqClosed.isClosed
    intro u x hu hx
    -- The sequence criterion controls the limit from below.
    have h_liminf : f x ≤ liminf (f ∘ u) atTop := hseq hx
    -- The pointwise bound along the sequence forces the liminf below the same level.
    have h_le_y : liminf (f ∘ u) atTop ≤ y := by
      refine Filter.liminf_le_of_le ?_ ?_
      · exact by isBoundedDefault
      · intro b hb
        let ⟨n, hbn, hun⟩ := (hb.and (Eventually.of_forall hu)).exists
        exact hbn.trans hun
    exact h_liminf.trans h_le_y

/-- Membership in `Γ(H)` is equivalent to Jensen convexity together with the sequential liminf
criterion for lower semicontinuity. -/
-- Proof sketch: combine `mem_gamma_iff` with
-- the sequential characterization of lower semicontinuity on sequential spaces.
theorem mem_gamma_iff_seq_tendsto_le_liminf
    [TopologicalSpace H] [SequentialSpace H] [AddCommMonoid H] [Module ℝ H]
    (f : H → EReal) :
    f ∈ Γ(H) ↔
      IsConvex f ∧
        ∀ ⦃x : H⦄ ⦃u : ℕ → H⦄,
          Tendsto u atTop (nhds x) → f x ≤ liminf (f ∘ u) atTop := by
  -- Unfold `gamma`, then replace lower semicontinuity by the sequential criterion.
  rw [mem_gamma_iff, lowerSemicontinuous_iff_seq_tendsto_le_liminf]

end ERealFunction
