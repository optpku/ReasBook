module

public import ReasLib.Analysis.Asymptotics.UniformRemainder.Algebra
import Mathlib.Analysis.Asymptotics.Lemmas

public section

open Filter
open scoped Topology

namespace DFP.TwoLeg

/-- A cubic factorization turns an order-five residual into an order-eight residual.
The factorization is stated on the germ at zero, so it can be supplied by an
independent analytic or algebraic calculation. -/
theorem isBigO_of_cubic_factorization
    {F : ℝ × ℝ × ℝ → ℝ} {p h p₀ h₀ r : ℝ → ℝ}
    (hfactor : ∀ᶠ ε in 𝓝 0,
      F (ε, p ε, h ε) - F (ε, p₀ ε, h₀ ε) = ε ^ 3 * r ε)
    (hr : r =O[𝓝 0] (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦ F (ε, p ε, h ε) - F (ε, p₀ ε, h₀ ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
  have hscale : (fun ε : ℝ ↦ ε ^ 3) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3) :=
    Asymptotics.isBigO_refl (fun ε : ℝ ↦ ε ^ 3) (𝓝 0)
  have hproduct : (fun ε : ℝ ↦ ε ^ 3 * r ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3 * ε ^ 5) := hscale.mul hr
  have hproduct' : (fun ε : ℝ ↦ ε ^ 3 * r ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
    simpa only [← pow_add, Nat.reduceAdd] using hproduct
  have hfactor' : (fun ε : ℝ ↦ ε ^ 3 * r ε) =ᶠ[𝓝 0]
      (fun ε : ℝ ↦ F (ε, p ε, h ε) - F (ε, p₀ ε, h₀ ε)) :=
    hfactor.mono (fun ε hε ↦ hε.symm)
  exact hproduct'.congr' hfactor' (Filter.EventuallyEq.rfl)

/-- A weighted linear coordinate factorization propagates fifth-order coordinate
errors to an eighth-order observable error.  The coefficient bounds are explicit
Big-O hypotheses, leaving any required smoothness or derivative argument to the
caller that establishes the factorization. -/
theorem isBigO_of_cubic_coordinate_factorization
    {F : ℝ × ℝ × ℝ → ℝ}
    {p h p₀ h₀ A B : ℝ → ℝ}
    (hfactor : ∀ᶠ ε in 𝓝 0,
      F (ε, p ε, h ε) - F (ε, p₀ ε, h₀ ε) =
        ε ^ 3 * (A ε * (p ε - p₀ ε) + B ε * (h ε - h₀ ε)))
    (hA : A =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)))
    (hB : B =O[𝓝 0] (fun _ : ℝ ↦ (1 : ℝ)))
    (hp : (fun ε : ℝ ↦ p ε - p₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))
    (hh : (fun ε : ℝ ↦ h ε - h₀ ε) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦ F (ε, p ε, h ε) - F (ε, p₀ ε, h₀ ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8) := by
  have hApRaw := hA.mul hp
  have hAp : (fun ε : ℝ ↦ A ε * (p ε - p₀ ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [one_mul] using hApRaw
  have hBhRaw := hB.mul hh
  have hBh : (fun ε : ℝ ↦ B ε * (h ε - h₀ ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := by
    simpa only [one_mul] using hBhRaw
  have hresidual : (fun ε : ℝ ↦
      A ε * (p ε - p₀ ε) + B ε * (h ε - h₀ ε)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) := hAp.add hBh
  exact isBigO_of_cubic_factorization hfactor hresidual

end DFP.TwoLeg
