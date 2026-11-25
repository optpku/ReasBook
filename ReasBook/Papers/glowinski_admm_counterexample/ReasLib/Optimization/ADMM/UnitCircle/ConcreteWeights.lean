/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ADMM.RefinedEndpoint.DataChecks
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Symbol

@[expose] public section

open scoped BigOperators

namespace ADMM.UnitCircle

namespace Concrete

/-- The block numbering in the two-by-two symbol agrees with the original
finite-memory labels used by the exact JSON data. -/
def blockOfIndex (b : Fin 2) : ADMM.FiniteMemory.Block :=
  if b = 0 then .F else .J

@[simp] theorem blockOfIndex_zero : blockOfIndex 0 = .F := rfl

@[simp] theorem blockOfIndex_one : blockOfIndex 1 = .J := rfl

/-- Sum all exact entries with a prescribed signed lag. Summing rather than
choosing an entry makes the interpretation faithful even before uniqueness of
the JSON keys has been separately established. -/
def rationalLagCoefficient (b : Fin 2) (j : ℤ) : ℚ :=
  ((ADMM.RefinedEndpoint.Data.lagWeights.filter
    (fun e ↦ decide (e.block = blockOfIndex b ∧ e.lag = j))).map
      ADMM.RefinedEndpoint.Data.LagWeight.coefficient).sum

/-- Every lookup is nonnegative because the exact input coefficients are. -/
theorem rationalLagCoefficient_nonneg (b : Fin 2) (j : ℤ) :
    0 ≤ rationalLagCoefficient b j := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨e, he, hxe⟩ := List.mem_map.mp hx
  rw [← hxe]
  exact ADMM.RefinedEndpoint.Data.coefficient_nonnegative e
    (List.mem_filter.mp he).1

/-- The rational version of the manuscript's signed first moment. -/
def rationalFirstMoment (b : Fin 2) : ℚ :=
  ∑ i : Fin ADMM.RefinedEndpoint.Data.historyLength,
    (i.val + 1 : ℚ) *
      (rationalLagCoefficient b (-(i.val + 1 : ℤ)) -
        rationalLagCoefficient b (i.val + 1 : ℤ))

end Concrete

/-- The actual real lag-weight data used by the unit-circle supply symbol.
All coefficients are obtained from the pinned rational input, with no repeated
numeric literals and no numerical approximation. -/
noncomputable def paperWeights : LagWeights ADMM.RefinedEndpoint.Data.historyLength where
  backward b i := Concrete.rationalLagCoefficient b (-(i.val + 1 : ℤ))
  forward b i := Concrete.rationalLagCoefficient b (i.val + 1 : ℤ)
  omega := ADMM.RefinedEndpoint.Data.omega
  epsilon := ADMM.RefinedEndpoint.Data.epsilon
  backward_nonneg b i := Rat.cast_nonneg.mpr
    (Concrete.rationalLagCoefficient_nonneg b (-(i.val + 1 : ℤ)))
  forward_nonneg b i := Rat.cast_nonneg.mpr
    (Concrete.rationalLagCoefficient_nonneg b (i.val + 1 : ℤ))
  omega_pos := Rat.cast_pos.mpr ADMM.RefinedEndpoint.Data.omega_pos
  epsilon_pos := Rat.cast_pos.mpr ADMM.RefinedEndpoint.Data.epsilon_pos

/-- Exact agreement of the real backward weights with the rational lookups. -/
@[simp] theorem paperWeights_backward (b : Fin 2)
    (i : Fin ADMM.RefinedEndpoint.Data.historyLength) :
    paperWeights.backward b i =
      (Concrete.rationalLagCoefficient b (-(i.val + 1 : ℤ)) : ℝ) := rfl

/-- Exact agreement of the real forward weights with the rational lookups. -/
@[simp] theorem paperWeights_forward (b : Fin 2)
    (i : Fin ADMM.RefinedEndpoint.Data.historyLength) :
    paperWeights.forward b i =
      (Concrete.rationalLagCoefficient b (i.val + 1 : ℤ) : ℝ) := rfl

/-- Casting preserves the finite signed moment exactly. The generic regrouping
and transport of the balanced-moment certificate are in `MomentRegrouping`. -/
theorem firstMoment_paperWeights (b : Fin 2) :
    firstMoment paperWeights b = (Concrete.rationalFirstMoment b : ℝ) := by
  simp [firstMoment, Concrete.rationalFirstMoment, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_sub, Rat.cast_add]

end ADMM.UnitCircle
