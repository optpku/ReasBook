/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/- Remark 9.27: For discrete-time filtrations indexed by `ℕ`, `ℕ₀`, or `ℤ`, it suffices to
verify the defining martingale equality or the submartingale/supermartingale inequality only for
one-step transitions `t = s + 1`; the tower property then propagates the relation to arbitrary
later times. In Lean, `ℕ₀` is `ℕ`, and mathlib packages this one-step reduction for the canonical
`ℕ`-indexed filtration by `martingale_nat`, with the submartingale and supermartingale variants
recalled below. The `ℤ`-indexed companions are added afterwards as thin bridge lemmas over the
same owner predicates. -/
recall martingale_nat

/- The one-step conditional-expectation inequality on `ℕ` is enough to build a submartingale. -/
recall submartingale_nat

/- The one-step conditional-expectation inequality on `ℕ` is enough to build a supermartingale. -/
recall supermartingale_nat

universe u v

variable {Ω : Type u} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {ℱ : Filtration ℤ m0} {f : ℤ → Ω → E}

/-- The `ℤ`-indexed analogue of `martingale_nat`: for integer-indexed discrete-time filtrations,
the one-step martingale identity already implies the full martingale property. -/
theorem martingale_int (hadp : StronglyAdapted ℱ f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, f i =ᵐ[μ] μ[f (i + 1) | ℱ i]) :
    Martingale f ℱ μ := by
  refine ⟨hadp, fun i j hij ↦ ?_⟩
  induction j, hij using Int.le_induction with
  | base =>
      refine ae_of_all _ fun _ ↦ ?_
      rw [condExp_of_stronglyMeasurable (ℱ.le i) (hadp i) (hint i)]
  | succ k hik hk =>
      filter_upwards [hk, condExp_congr_ae (hf k), ℱ.condExp_condExp (f (k + 1)) hik]
        with ω hω₁ hω₂ hω₃
      rw [← hω₁, hω₂, hω₃]

variable [PartialOrder E] [IsOrderedAddMonoid E] [ClosedIciTopology E] [IsOrderedModule ℝ E]

/-- The `ℤ`-indexed analogue of `submartingale_nat`: it is enough to check the one-step
submartingale inequality for consecutive integers. -/
theorem submartingale_int (hadp : StronglyAdapted ℱ f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, f i ≤ᵐ[μ] μ[f (i + 1) | ℱ i]) :
    Submartingale f ℱ μ := by
  refine ⟨hadp, fun i j hij ↦ ?_, hint⟩
  induction j, hij using Int.le_induction with
  | base =>
      refine ae_of_all _ fun _ ↦ ?_
      rw [condExp_of_stronglyMeasurable (ℱ.le i) (hadp i) (hint i)]
  | succ k hik hk =>
      filter_upwards [hk, condExp_mono (hint k) integrable_condExp (hf k),
        ℱ.condExp_condExp (f (k + 1)) hik] with ω hω₁ hω₂ hω₃
      grw [hω₁, hω₂, hω₃]

/-- The `ℤ`-indexed analogue of `supermartingale_nat`: it is enough to check the one-step
supermartingale inequality for consecutive integers. -/
theorem supermartingale_int (hadp : StronglyAdapted ℱ f) (hint : ∀ i, Integrable (f i) μ)
    (hf : ∀ i, μ[f (i + 1) | ℱ i] ≤ᵐ[μ] f i) :
    Supermartingale f ℱ μ := by
  rw [← neg_neg f]
  refine (submartingale_int hadp.neg (fun i ↦ (hint i).neg) fun i ↦
    Filter.EventuallyLE.trans ?_ (condExp_neg ..).symm.le).neg
  filter_upwards [hf i] with x hx using neg_le_neg hx
