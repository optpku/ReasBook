/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Fourier.Operators

@[expose] public section

namespace ADMM.UnitCircle.Fourier

open MeasureTheory

noncomputable section

theorem transform_zero_ae :
    transform 0 =ᵐ[AddCircle.haarAddCircle] (fun _ ↦ (0 : ℂ)) := by
  rw [map_zero]
  exact Lp.coeFn_zero _ _ _

theorem transform_finsetSum_ae {ι : Type*} (s : Finset ι) (f : ι → TimeSequence) :
    transform (∑ i ∈ s, f i) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ ∑ i ∈ s, transform (f i) t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using transform_zero_ae
  | insert i s hi ih =>
    filter_upwards [transform_add_ae (f i) (∑ j ∈ s, f j), ih] with t ha hs
    simpa only [Finset.sum_insert hi, ha, hs]

def backwardDifference (α : ℝ) (j : ℕ) (x : TimeSequence) : TimeSequence :=
  x - ((α : ℂ) ^ j) • delay (j : ℤ) x

def forwardDifference (α : ℝ) (j : ℕ) (x : TimeSequence) : TimeSequence :=
  ((α : ℂ) ^ (2 * j)) • x - ((α : ℂ) ^ j) • delay (-(j : ℤ)) x

theorem transform_backwardDifference_ae (α : ℝ) (j : ℕ) (x : TimeSequence) :
    transform (backwardDifference α j x) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ (1 - (α : ℂ) ^ j * ((circlePoint t)⁻¹) ^ j) * transform x t) := by
  filter_upwards [transform_sub_ae x (((α : ℂ) ^ j) • delay (j : ℤ) x),
    transform_smul_ae ((α : ℂ) ^ j) (delay (j : ℤ) x),
    transform_delay_ae (j : ℤ) x] with t hsub hs hd
  change transform (x - ((α : ℂ) ^ j) • delay (j : ℤ) x) t = _
  rw [hsub, hs, hd, backward_character]
  ring

theorem transform_forwardDifference_ae (α : ℝ) (j : ℕ) (x : TimeSequence) :
    transform (forwardDifference α j x) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ ((α : ℂ) ^ (2 * j) - (α : ℂ) ^ j * circlePoint t ^ j) * transform x t) := by
  filter_upwards [transform_sub_ae (((α : ℂ) ^ (2 * j)) • x)
      (((α : ℂ) ^ j) • delay (-(j : ℤ)) x),
    transform_smul_ae ((α : ℂ) ^ (2 * j)) x,
    transform_smul_ae ((α : ℂ) ^ j) (delay (-(j : ℤ)) x),
    transform_delay_ae (-(j : ℤ)) x] with t hsub hs₁ hs₂ hd
  change transform (((α : ℂ) ^ (2 * j)) • x -
    ((α : ℂ) ^ j) • delay (-(j : ℤ)) x) t = _
  rw [hsub, hs₁, hs₂, hd, forward_character]
  ring

def lagTerm {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ) (b : Fin 2)
    (i : Fin ℓ) (x : TimeSequence) : TimeSequence :=
  (c.backward b i : ℂ) • backwardDifference α (i.val + 1) x +
    (c.forward b i : ℂ) • forwardDifference α (i.val + 1) x

def lagOperator {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (b : Fin 2) (x : TimeSequence) : TimeSequence :=
  (c.omega : ℂ) • x + ∑ i, lagTerm c α b i x

theorem transform_lagTerm_ae {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (b : Fin 2) (i : Fin ℓ) (x : TimeSequence) :
    transform (lagTerm c α b i x) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ ((c.backward b i : ℂ) *
        (1 - (α : ℂ) ^ (i.val + 1) * ((circlePoint t)⁻¹) ^ (i.val + 1)) +
        (c.forward b i : ℂ) * ((α : ℂ) ^ (2 * (i.val + 1)) -
          (α : ℂ) ^ (i.val + 1) * circlePoint t ^ (i.val + 1))) * transform x t) := by
  filter_upwards [transform_add_ae
      ((c.backward b i : ℂ) • backwardDifference α (i.val + 1) x)
      ((c.forward b i : ℂ) • forwardDifference α (i.val + 1) x),
    transform_smul_ae (c.backward b i : ℂ) (backwardDifference α (i.val + 1) x),
    transform_smul_ae (c.forward b i : ℂ) (forwardDifference α (i.val + 1) x),
    transform_backwardDifference_ae α (i.val + 1) x,
    transform_forwardDifference_ae α (i.val + 1) x] with t ha hs₁ hs₂ hb hf
  change transform ((c.backward b i : ℂ) • backwardDifference α (i.val + 1) x +
    (c.forward b i : ℂ) • forwardDifference α (i.val + 1) x) t = _
  rw [ha, hs₁, hs₂, hb, hf]
  ring

/-- The actual finite lag operator has exactly the manuscript's discounted symbol. -/
theorem transform_lagOperator_ae {ℓ : ℕ} (c : LagWeights ℓ) (α : ℝ)
    (b : Fin 2) (x : TimeSequence) :
    transform (lagOperator c α b x) =ᵐ[AddCircle.haarAddCircle]
      (fun t ↦ lagMultiplier c α (circlePoint t) b * transform x t) := by
  have hi := Filter.eventually_all.mpr (fun i ↦ transform_lagTerm_ae c α b i x)
  filter_upwards [transform_add_ae ((c.omega : ℂ) • x) (∑ i, lagTerm c α b i x),
    transform_smul_ae (c.omega : ℂ) x,
    transform_finsetSum_ae Finset.univ (fun i ↦ lagTerm c α b i x), hi] with t ha hs hsum hterm
  change transform ((c.omega : ℂ) • x + ∑ i, lagTerm c α b i x) t = _
  rw [ha, hs, hsum]
  simp only [hterm, lagMultiplier, add_mul, Finset.sum_mul]

end

end ADMM.UnitCircle.Fourier
