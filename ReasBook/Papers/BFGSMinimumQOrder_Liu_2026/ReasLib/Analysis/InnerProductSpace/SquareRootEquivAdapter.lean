module

public import Mathlib.Analysis.Normed.Operator.Banach
public import ReasLib.Analysis.InnerProductSpace.SquareRootAdapter

public section

noncomputable section

universe u

open scoped InnerProduct NNReal

namespace ContinuousLinearMap

/-- A CFC square-root factorization can be upgraded from an invertible operator to a
continuous linear equivalence with the same self-adjoint pushforward identity. -/
theorem exists_sqrtEquiv_of_lowerBound_of_cfc
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {H : E →L[ℝ] E}
    [NonUnitalContinuousFunctionalCalculus ℝ (E →L[ℝ] E) IsSelfAdjoint]
    {m : ℝ} (selfAdjoint : IsSelfAdjoint H) (hm : 0 < m)
    (lower : m • (1 : E →L[ℝ] E) ≤ H) :
    ∃ L : E ≃L[ℝ] E,
      IsSelfAdjoint L.toContinuousLinearMap ∧
        H = L.toContinuousLinearMap.pushforward 1 := by
  obtain ⟨S, hSadj, hSunit, hH⟩ :=
    exists_sqrt_factorization_of_lowerBound_of_cfc selfAdjoint hm lower
  have hbij : Function.Bijective S := S.isUnit_iff_bijective.mp hSunit
  have hker : S.ker = ⊥ := by
    simpa [LinearMap.ker_eq_bot] using hbij.1
  have hrange : S.range = ⊤ := by
    simpa [LinearMap.range_eq_top] using hbij.2
  let L : E ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofBijective S hker hrange
  refine ⟨L, ?_, ?_⟩
  · change IsSelfAdjoint S
    exact hSadj
  · change H = S.pushforward 1
    exact hH

end ContinuousLinearMap
