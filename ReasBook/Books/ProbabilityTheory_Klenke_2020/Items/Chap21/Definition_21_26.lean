/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Definition_14_40
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped NNReal Topology ZeroAtInfty

noncomputable section

universe u

variable {E : Type u} [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

namespace ProbabilityTheory

/-- A Feller semigroup on a Borel topological state space, in the sense of Definition 21.26, is a
Markov semigroup of transition kernels whose kernel expectation operators preserve real-valued
`C₀(E)` and converge pointwise to the identity as `t → 0`. -/
class IsFellerSemigroup (κ : NNReal → Kernel E E) : Prop extends IsMarkovSemigroup κ where
  /-- For every `t` and `f : C₀(E, ℝ)`, the kernel expectation `x ↦ ∫ y, f y ∂ κ t x` is
  continuous. -/
  mapZeroAtInfty_continuous (t : NNReal) (f : C₀(E, ℝ)) :
    Continuous fun x ↦ ∫ y, f y ∂ κ t x
  /-- For every `t` and `f : C₀(E, ℝ)`, the kernel expectation `x ↦ ∫ y, f y ∂ κ t x` vanishes at
  infinity. -/
  mapZeroAtInfty_zeroAtInfty (t : NNReal) (f : C₀(E, ℝ)) :
    Tendsto (fun x ↦ ∫ y, f y ∂ κ t x) (cocompact E) (𝓝 0)
  /-- For every `f : C₀(E, ℝ)` and `x : E`, the kernel expectation converges to `f x` as
  `t → 0`. -/
  continuousAt_zero (f : C₀(E, ℝ)) (x : E) :
    Tendsto (fun t : NNReal ↦ ∫ y, f y ∂ κ t x) (𝓝 0) (𝓝 (f x))

/-- Helper for Definition 21.26: integrating a `C₀(E, ℝ)` function against the identity kernel
recovers evaluation at the base point. -/
@[simp] theorem integral_idKernel_eq (f : C₀(E, ℝ)) (x : E) :
    ∫ y, f y ∂ (Kernel.id : Kernel E E) x = f x := by
  rw [Kernel.id_apply]
  simpa using integral_dirac' f x f.continuous.stronglyMeasurable

/-- Definition 21.26: the constant identity kernel family `t ↦ Kernel.id` is a Feller semigroup,
so the defining axioms are realized by the trivial Markov evolution. -/
instance instIsFellerSemigroupId :
    IsFellerSemigroup (fun _ : NNReal ↦ (Kernel.id : Kernel E E)) where
  isMarkovKernel t := by
    simpa using (inferInstance : IsMarkovKernel (Kernel.id : Kernel E E))
  zero_eq := rfl
  comp_eq s t := by
    simp
  mapZeroAtInfty_continuous t f := by
    simpa only [integral_idKernel_eq] using f.continuous
  mapZeroAtInfty_zeroAtInfty t f := by
    simpa only [integral_idKernel_eq] using f.zero_at_infty'
  continuousAt_zero f x := by
    simpa only [integral_idKernel_eq] using
      (tendsto_const_nhds : Tendsto (fun _ : NNReal ↦ f x) (𝓝 0) (𝓝 (f x)))

namespace IsFellerSemigroup

variable {κ : NNReal → Kernel E E} [hκ : IsFellerSemigroup κ]

/-- The canonical action of a Feller semigroup on `C₀(E, ℝ)` is given by kernel expectation. -/
def mapZeroAtInfty (κ : NNReal → Kernel E E) [IsFellerSemigroup κ]
    (t : NNReal) (f : C₀(E, ℝ)) : C₀(E, ℝ) :=
  let hκ : IsFellerSemigroup κ := inferInstance
  { toFun := fun x ↦ ∫ y, f y ∂ κ t x
    continuous_toFun := hκ.mapZeroAtInfty_continuous t f
    zero_at_infty' := hκ.mapZeroAtInfty_zeroAtInfty t f }

omit [BorelSpace E] in
/-- Evaluating the Feller operator at `x` gives the kernel expectation against the row `κ t x`. -/
@[simp] theorem mapZeroAtInfty_apply (t : NNReal) (f : C₀(E, ℝ)) (x : E) :
    mapZeroAtInfty κ t f x = ∫ y, f y ∂ κ t x :=
  rfl

omit [BorelSpace E] in
/-- Evaluated at a fixed state `x`, the Feller operators converge to `f x` as `t → 0`. -/
theorem tendsto_mapZeroAtInfty_zero_apply (f : C₀(E, ℝ)) (x : E) :
    Tendsto (fun t : NNReal ↦ mapZeroAtInfty κ t f x) (𝓝 0) (𝓝 (f x)) := by
  simpa [mapZeroAtInfty_apply] using hκ.continuousAt_zero f x

end IsFellerSemigroup

end ProbabilityTheory
