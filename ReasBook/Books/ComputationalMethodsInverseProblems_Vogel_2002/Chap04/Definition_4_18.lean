/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

public section

noncomputable section

open scoped BigOperators

namespace ProbabilityTheory.JointPmf

universe u v w

variable {Ω : Type u} {α : Type v} {β : Type w}

/-- Helper for Definition 4.18: the joint mass at `(x, y)` agrees with the probability of the
point event `{ω | X ω = x ∧ Y ω = y}` when `(X, Y)` has law `joint`. -/
theorem apply_eq_prob
    [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {μ : MeasureTheory.Measure Ω} {X : Ω → α} {Y : Ω → β}
    (joint : PMF (α × β))
    (hLaw : ProbabilityTheory.HasLaw (fun ω ↦ (X ω, Y ω)) joint.toMeasure μ)
    (x : α) (y : β) :
    joint (x, y) = μ {ω | X ω = x ∧ Y ω = y} := by
  -- Evaluate the law of `(X, Y)` on the singleton event `{(x, y)}`.
  have hSingleton :
      μ {ω | (X ω, Y ω) = (x, y)} = joint.toMeasure {(x, y)} :=
    hLaw.measure_eq (p := fun z ↦ z = (x, y)) (measurableSet_singleton (x, y))
  -- Rewrite the singleton mass of the PMF and simplify pair equality componentwise.
  rw [joint.toMeasure_apply_singleton (x, y) (measurableSet_singleton (x, y))] at hSingleton
  simpa [Prod.mk.injEq] using hSingleton.symm

/-- Helper for Definition 4.18: the first marginal PMF of a joint PMF on `α × β`. -/
def fstMarginal (joint : PMF (α × β)) : PMF α :=
  PMF.map Prod.fst joint

/-- Helper for Definition 4.18: the measure underlying `fstMarginal joint` is the pushforward of
`joint.toMeasure` along `Prod.fst`. -/
theorem fstMarginal_toMeasure [MeasurableSpace α] [MeasurableSpace β]
    (joint : PMF (α × β)) :
    (fstMarginal joint).toMeasure = joint.toMeasure.map Prod.fst := by
  exact (PMF.toMeasure_map Prod.fst joint measurable_fst).symm

/-- Helper for Definition 4.18: the pointwise formula for the first marginal, obtained by summing
the joint mass over `y`. -/
theorem fstMarginal_apply (joint : PMF (α × β)) (x : α) :
    fstMarginal joint x = ∑' y, joint (x, y) := by
  -- Expand the mapped PMF and separate the product sum into `x` and `y` coordinates.
  rw [fstMarginal, PMF.map_apply, ENNReal.tsum_prod']
  -- Only the fiber with first coordinate equal to `x` survives.
  refine (tsum_eq_single x ?_).trans ?_
  · intro x' hx'
    rw [ENNReal.tsum_eq_zero]
    intro y
    have hxx' : x ≠ x' := fun h => hx' h.symm
    simp [hxx']
  · simp

/-- Helper for Definition 4.18: the sum of the fiber `y ↦ joint (x, y)` equals the first
marginal at `x`. -/
theorem tsum_fiber_eq_fstMarginal (joint : PMF (α × β)) (x : α) :
    ∑' y, joint (x, y) = fstMarginal joint x := by
  -- This is exactly the first marginal formula rewritten symmetrically.
  exact (fstMarginal_apply joint x).symm

/-- Helper for Definition 4.18: a nonzero first marginal forces the `y`-fiber sum at `x` to be
nonzero. -/
theorem tsum_fiber_ne_zero (joint : PMF (α × β)) (x : α) (hx : fstMarginal joint x ≠ 0) :
    ∑' y, joint (x, y) ≠ 0 := by
  -- Rewrite the fiber sum as the first marginal at `x`.
  simpa [tsum_fiber_eq_fstMarginal] using hx

/-- Helper for Definition 4.18: the `y`-fiber sum of a joint PMF is finite in `ℝ≥0∞`. -/
theorem tsum_fiber_ne_top (joint : PMF (α × β)) (x : α) :
    ∑' y, joint (x, y) ≠ ⊤ := by
  -- Rewrite the fiber sum as a PMF value, which is never `⊤`.
  simpa [tsum_fiber_eq_fstMarginal] using (fstMarginal joint).apply_ne_top x

/-- Helper for Definition 4.18: the second marginal PMF of a joint PMF on `α × β`. -/
def sndMarginal (joint : PMF (α × β)) : PMF β :=
  PMF.map Prod.snd joint

/-- Helper for Definition 4.18: the measure underlying `sndMarginal joint` is the pushforward of
`joint.toMeasure` along `Prod.snd`. -/
theorem sndMarginal_toMeasure [MeasurableSpace α] [MeasurableSpace β]
    (joint : PMF (α × β)) :
    (sndMarginal joint).toMeasure = joint.toMeasure.map Prod.snd := by
  exact (PMF.toMeasure_map Prod.snd joint measurable_snd).symm

/-- Helper for Definition 4.18: the pointwise formula for the second marginal, obtained by summing
the joint mass over `x`. -/
theorem sndMarginal_apply (joint : PMF (α × β)) (y : β) :
    sndMarginal joint y = ∑' x, joint (x, y) := by
  -- Expand the mapped PMF and separate the product sum into `x` and `y` coordinates.
  rw [sndMarginal, PMF.map_apply, ENNReal.tsum_prod']
  -- Only the fiber with second coordinate equal to `y` survives.
  congr 1
  funext x
  refine (tsum_eq_single y ?_).trans ?_
  · intro y' hy'
    have hyy' : y ≠ y' := fun h => hy' h.symm
    simp [hyy']
  · simp

/-- Helper for Definition 4.18: the conditional PMF of `Y` given the event `X = x`, assuming the
first marginal at `x` is nonzero. -/
def condSndGivenFst (joint : PMF (α × β)) (x : α) (hx : fstMarginal joint x ≠ 0) : PMF β :=
  PMF.normalize
    (fun y ↦ joint (x, y))
    (tsum_fiber_ne_zero joint x hx)
    (tsum_fiber_ne_top joint x)

/-- Definition 4.18: the defining ratio formula for the conditional PMF of `Y` given `X = x`. -/
theorem condSndGivenFst_apply
    (joint : PMF (α × β)) (x : α) (hx : fstMarginal joint x ≠ 0) (y : β) :
    condSndGivenFst joint x hx y = joint (x, y) / fstMarginal joint x := by
  -- Expand the normalization and identify its normalizing constant with the first marginal.
  rw [condSndGivenFst, PMF.normalize_apply, tsum_fiber_eq_fstMarginal, div_eq_mul_inv]

end ProbabilityTheory.JointPmf
