/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.FiniteDimensionalKernel

-- Declarations for this support file are maintained manually for Theorem 14.47 proof rescue.

open MeasureTheory ProbabilityTheory Finset
open scoped ProbabilityTheory
open FiniteDimensionalKernelLocal

noncomputable section

universe u

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E] [PolishSpace E]

/-- Helper for Theorem 14.47: the finite-dimensional coordinate projection of a path indexed by
`NNReal`. -/
def supportFiniteDimensionalProjection {n : ℕ} (times : Fin (n + 1) → NNReal) :
    (NNReal → E) → Fin (n + 1) → E :=
  fun ω i ↦ ω (times i)

/-- Helper for Theorem 14.47: finite-dimensional projections of the canonical path space are
measurable. -/
theorem measurable_supportFiniteDimensionalProjection {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Measurable
      (supportFiniteDimensionalProjection times : (NNReal → E) → Fin (n + 1) → E) := by
  -- Proof comment: each output coordinate is evaluation at one fixed time.
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact measurable_pi_apply (times i)

/-- Helper for Theorem 14.47: `Finset.Iic n` is canonically equivalent to `Fin (n + 1)`. -/
private def iicEquivFin (n : ℕ) : Finset.Iic n ≃ Fin (n + 1) where
  toFun i := ⟨i.1, Nat.lt_succ_of_le <| Finset.mem_Iic.mp i.2⟩
  invFun i := ⟨i.1, Finset.mem_Iic.mpr <| Nat.le_of_lt_succ i.2⟩
  left_inv i := by
    cases i
    rfl
  right_inv i := by
    cases i
    rfl

/-- Helper for Theorem 14.47: reindex a `Fin` time tuple as an ordered `Iic` chain. -/
private def orderedTimeChain {n : ℕ} (times : Fin (n + 1) → NNReal) :
    Π _ : Finset.Iic n, NNReal :=
  fun i ↦ times (iicEquivFin n i)

/-- Helper for Theorem 14.47: strict monotonicity transfers across the `Iic` reindexing. -/
private theorem orderedTimeChain_strictMono {n : ℕ} {times : Fin (n + 1) → NNReal}
    (htimes : StrictMono times) :
    StrictMono (orderedTimeChain times) := by
  -- Proof comment: the `Iic`/`Fin` reindexing preserves the order relation.
  intro i j hij
  exact htimes (by simpa [orderedTimeChain, iicEquivFin] using hij)

/-- Helper for Theorem 14.47: the ordered finite-dimensional distribution kernel attached to a
Markov semigroup along a strictly increasing time tuple. -/
def supportMarkovSemigroupFiniteDimKernel (κ : NNReal → Kernel E E) {n : ℕ}
    (times : Fin (n + 1) → NNReal) (htimes : StrictMono times) :
    Kernel E (Fin (n + 1) → E) :=
  (consistentFamilyFiniteDimensionalKernel (fun {s t : NNReal} _ ↦ κ (t - s))
      (orderedTimeChain times) (orderedTimeChain_strictMono htimes)).map
    (fun x i ↦ x ((iicEquivFin n).symm i))

/-- Helper for Theorem 14.47: the missing Chapter 14 path-measure existence theorem isolated from
the broken `Theorem_14_42` transport block. -/
theorem existsUnique_markovPathMeasure
    (κ : NNReal → Kernel E E) [IsMarkovSemigroup κ] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    ∃! pathMeasure : Measure (NNReal → E),
      IsProbabilityMeasure pathMeasure ∧
        ∀ {n : ℕ} (times : Fin (n + 1) → NNReal),
          times 0 = 0 → ∀ htimes : StrictMono times,
            pathMeasure.map (supportFiniteDimensionalProjection times) =
              supportMarkovSemigroupFiniteDimKernel κ times htimes ∘ₘ μ := by
  -- Route correction: `Corollary_14_44` currently imports the non-compiling `Theorem_14_42`.
  -- TODO: rebuild this theorem from the projective-limit path-kernel route or directly from
  -- the `trajMeasure` finite-marginal API, then remove this placeholder.
  sorry
