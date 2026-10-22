/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_36
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Exercise_17_6_6
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_11
import Mathlib

open MeasureTheory ProbabilityTheory ProbabilityTheory.Kernel
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u}

/- Layering for Theorem 19.12:
- `IsReversible`, `Invariant`, and `IsRandomWalkWithWeights` are the core/canonical owner
  abstractions for reversibility, invariant measures, and conductance walks.
- the source-facing content of part (1) is the specific reversible weight family
  `C(x,y) = p(x,y) π({x})`, together with its symmetry and vertex-weight formula.
- `reversibleMarkovChainWeights p π` is the bridge/view turning a reversible chain and reversing
  measure into those textbook edge weights.
- the stronger owner-level upgrade to `IsRandomWalkWithWeights` is auxiliary: it additionally
  needs finite positive singleton masses so that the row-normalization formula is defined
  canonically in `ℝ≥0∞`. -/

/-- The edge-weight function attached to a transition matrix `p` and a measure `π`, with
`C(x,y) = p(x,y) π({x})`. -/
@[simp]
def reversibleMarkovChainWeights [MeasurableSpace E] [MeasurableSingletonClass E]
    (p : E → E → ℝ≥0∞) (π : Measure E) : E → E → ℝ≥0∞ :=
  fun x y ↦ p x y * π {x}

/-- Scaling the reversing measure scales the attached edge-weight family by the same factor. -/
theorem reversibleMarkovChainWeights_smul_measure
    [MeasurableSpace E] [MeasurableSingletonClass E]
    (p : E → E → ℝ≥0∞) (π : Measure E) (c : ℝ≥0∞) :
    reversibleMarkovChainWeights p (c • π) = c • reversibleMarkovChainWeights p π := by
  ext x y
  simp [reversibleMarkovChainWeights, mul_left_comm]

section

variable [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]

-- Proof sketch: the factor `π {x}` is constant in the `y`-sum defining the conductance at `x`, so
-- stochasticity rewrites `∑' y, p x y * π {x}` as `(∑' y, p x y) * π {x} = π {x}`.
/-- The conductance of the reversible-chain weights at `x` is the singleton mass `π({x})`. -/
@[simp]
theorem conductance_reversibleMarkovChainWeights
    {p : E → E → ℝ≥0∞} {π : Measure E}
    (hp : IsStochasticMatrix p) (x : E) :
    conductance (reversibleMarkovChainWeights p π) x = π {x} := by
  simp [conductance, reversibleMarkovChainWeights, ENNReal.tsum_mul_right, hp x]

-- Proof sketch: evaluating the discrete matrix kernel on a singleton keeps only the matching
-- Dirac-mass term in the row measure.
/-- Helper for Theorem 19.12: `discreteMatrixKernel p x` evaluates on `{y}` to the matrix entry
`p x y`. -/
theorem discreteMatrixKernel_singletonEqEntry
    {p : E → E → ℝ≥0∞} (x y : E) :
    discreteMatrixKernel p x ({y} : Set E) = p x y := by
  -- Proof comment: expand the row kernel as a sum of weighted Dirac masses and keep the unique
  -- singleton contribution.
  rw [discreteMatrixKernel_apply]
  simpa using
    (Measure.sum_smul_dirac_singleton (f := fun z : E ↦ p x z) (a := y))

-- Proof sketch: specialize setwise reversibility to the singleton sets `{x}` and `{y}` and then
-- rewrite both restricted integrals explicitly.
/-- Helper for Theorem 19.12: reversibility of `discreteMatrixKernel p` yields the singleton
detailed-balance identity `p x y * π {x} = p y x * π {y}`. -/
theorem reversibleSingletonBalance
    {p : E → E → ℝ≥0∞} {π : Measure E}
    (hπ_rev : IsReversible (discreteMatrixKernel p) π) :
    ∀ x y : E, p x y * π {x} = p y x * π {y} := by
  intro x y
  have hxy :=
    hπ_rev (A := ({x} : Set E)) (B := ({y} : Set E))
      (measurableSet_singleton x) (measurableSet_singleton y)
  -- Proof comment: the owner reversibility identity on singleton sets is exactly the textbook
  -- entrywise detailed-balance equation.
  rw [MeasureTheory.lintegral_singleton, MeasureTheory.lintegral_singleton] at hxy
  rw [discreteMatrixKernel_singletonEqEntry, discreteMatrixKernel_singletonEqEntry] at hxy
  simpa [mul_comm] using hxy

-- Proof sketch: apply detailed balance to singleton sets `{x}` and `{y}`.
/-- The reversible-chain edge weights `C(x,y) = p(x,y) π({x})` are symmetric. -/
theorem reversibleMarkovChainWeights_symmetric
    {p : E → E → ℝ≥0∞} {π : Measure E}
    (hπ_rev : IsReversible (discreteMatrixKernel p) π) :
    ∀ x y : E,
      reversibleMarkovChainWeights p π x y = reversibleMarkovChainWeights p π y x := by
  intro x y
  -- Route correction: replace the imported detailed-balance bridge with the local singleton
  -- specialization of `Kernel.IsReversible`.
  simpa [reversibleMarkovChainWeights] using reversibleSingletonBalance hπ_rev x y

-- Proof sketch: combine the symmetry theorem above with the conductance identity
-- `conductance (reversibleMarkovChainWeights p π) x = π {x}`.
/-- Theorem 19.12 (1): for a reversible discrete-time chain, the attached weights
`C(x,y) = p(x,y) π({x})` are symmetric and have vertex weight
`∑' y, C(x,y) = π({x})`. -/
theorem reversibleMarkovChain_weights
    {p : E → E → ℝ≥0∞} {π : Measure E}
    (hp : IsStochasticMatrix p)
    (hπ_rev : IsReversible (discreteMatrixKernel p) π) :
    (∀ x y : E,
        reversibleMarkovChainWeights p π x y = reversibleMarkovChainWeights p π y x) ∧
      ∀ x : E, conductance (reversibleMarkovChainWeights p π) x = π {x} :=
  ⟨reversibleMarkovChainWeights_symmetric hπ_rev, conductance_reversibleMarkovChainWeights hp⟩

-- Proof sketch: after rewriting the conductance as `π {x}`, finite positivity of `π {x}` lets the
-- factor `π {x}` cancel in `(p x y * π {x}) / π {x}`.
/-- The reversible-chain weights recover the transition matrix when the singleton masses of `π`
are finite and positive. -/
theorem reversibleMarkovChainWeights_transition_eq
    {p : E → E → ℝ≥0∞} {π : Measure E}
    (hp : IsStochasticMatrix p) (hπ_finite : ∀ x : E, π {x} < ∞)
    (hπ_pos : ∀ x : E, 0 < π {x}) :
    ∀ x y : E,
      p x y = reversibleMarkovChainWeights p π x y /
        conductance (reversibleMarkovChainWeights p π) x := by
  intro x y
  rw [conductance_reversibleMarkovChainWeights hp x, reversibleMarkovChainWeights, mul_div_assoc,
    ENNReal.div_self (ne_of_gt (hπ_pos x)) (ne_of_lt (hπ_finite x)), mul_one]

-- Proof sketch: Theorem 19.12 (1) gives the source-facing symmetric weight family and its vertex
-- weights. The finite positive singleton-mass assumptions upgrade that data to the owner
-- predicate `IsRandomWalkWithWeights` by supplying the row-normalization formula.
/-- Auxiliary bridge: a reversible chain with finite positive singleton masses is a random walk
with weights `C(x,y) = p(x,y) π({x})` in the sense of Definition 19.11. -/
theorem reversibleMarkovChain_isRandomWalkWithWeights_of_singleton_finite_pos
    {p : E → E → ℝ≥0∞} {π : Measure E}
    (hp : IsStochasticMatrix p) (hπ_finite : ∀ x : E, π {x} < ∞)
    (hπ_pos : ∀ x : E, 0 < π {x})
    (hπ_rev : IsReversible (discreteMatrixKernel p) π) :
    IsRandomWalkWithWeights p (reversibleMarkovChainWeights p π) where
  isStochastic := hp
  symmetric := reversibleMarkovChainWeights_symmetric hπ_rev
  transition_eq := reversibleMarkovChainWeights_transition_eq hp hπ_finite hπ_pos

section

variable {p : E → E → ℝ≥0∞} {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
variable [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]

-- Proof sketch: first apply the Chapter 17 uniqueness-up-to-scale statement for nonzero invariant
-- measures of an irreducible recurrent chain to the source-facing reversible measure `π` and the
-- comparison invariant measure `ν`; this gives `ν = c • π` for some `c > 0`.
-- Then substitute this identity into `reversibleMarkovChainWeights`; scalar multiplication of the
-- measure scales each singleton mass and therefore scales the whole weight function by `c`.
/-- Theorem 19.12 (2): if the chain is irreducible and recurrent, then the weight family attached
to the reversible measure `π` is unique up to the same positive factor as any other nonzero
invariant measure. -/
theorem reversibleMarkovChainWeights_areProportional_of_irreducible_recurrent
    (hirr : IsIrreducibleMarkovChain P X) (hrec : IsRecurrentMarkovChain P X) {π ν : Measure E}
    (hπ_rev : IsReversible (discreteMatrixKernel p) π)
    (hν_inv : Invariant (discreteMatrixKernel p) ν)
    (hπ_ne : π ≠ 0) (hν_ne : ν ≠ 0) :
    ∃ c : ℝ≥0∞, 0 < c ∧
      reversibleMarkovChainWeights p ν = c • reversibleMarkovChainWeights p π := by
  have hrealization :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  let _ : IsMarkovKernel (discreteMatrixKernel p) := by
    simpa using hrealization.semigroup.isMarkovKernel 1
  -- Route correction: use the invariant-measure uniqueness theorem directly instead of importing
  -- the broken reversible-measure bridge from `Remark_19_9`.
  rcases invariantMeasures_unique_up_to_scale_of_irreducible_recurrent hirr hrec
      hπ_rev.invariant hν_inv hπ_ne hν_ne with ⟨c, hc, hν_smul⟩
  refine ⟨c, hc, ?_⟩
  -- Then transport the measure scaling identity to the associated edge-weight family.
  simpa [hν_smul] using reversibleMarkovChainWeights_smul_measure p π c

end

end

end ProbabilityTheory
