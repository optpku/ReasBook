module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import ReasLib.Analysis.InnerProductSpace.PositiveLowerBound

public section

noncomputable section

universe u

open scoped InnerProduct NNReal

namespace ContinuousLinearMap

/-- A real continuous functional calculus turns a strict Loewner lower bound into an invertible
self-adjoint square-root factor whose pushforward of the identity is the original operator. -/
theorem exists_sqrt_factorization_of_lowerBound_of_cfc
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E}
    [NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    (selfAdjoint : IsSelfAdjoint H) {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) :
    ∃ S : E →L[ℝ] E, IsSelfAdjoint S ∧ IsUnit S ∧ H = S.pushforward 1 := by
  have hpositive : H.IsPositive :=
    isPositive_of_loewner_lowerBound hm.le lower
  have hQ : QuasispectrumRestricts H ContinuousMap.realToNNReal := by
    rw [quasispectrumRestricts_iff_spectrumRestricts]
    exact hpositive.spectrumRestricts
  obtain ⟨S, hS, -, hSS⟩ :=
    CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts selfAdjoint hQ
  have hunitH : IsUnit H := isUnit_of_loewner_lowerBound hm lower
  have hunitS : IsUnit S := isUnit_mul_self_iff.mp (hSS ▸ hunitH)
  refine ⟨S, hS, hunitS, ?_⟩
  rw [pushforward_one, hS.adjoint_eq]
  exact hSS.symm

end ContinuousLinearMap
