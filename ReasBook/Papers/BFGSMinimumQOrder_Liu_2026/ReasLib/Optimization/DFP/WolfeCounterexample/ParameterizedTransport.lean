module

public import ReasLib.Optimization.DFP.WolfeCounterexample.ParameterizedPlanar
public import ReasLib.Optimization.DFP.StrongWolfeCounterexample
import Mathlib.Tactic

/-!
# All-dimensional parameterized strong-Wolfe certificates

The planar construction is extended by an identity quadratic block and then
pulled back along the canonical finite-index linear isometry equivalence.  The
line-search coefficients remain symbolic throughout this transport.  More
precisely, with `m = n - 2` and `2 + m = n`, the proof uses
`e : Fin n ≃ Fin 2 ⊕ Fin m` and
`LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e`.  The identity block preserves the
Hessian interval because `1 / 2 ≤ 1 ≤ 3 / 2`, and the final isometric pullback
preserves both that interval and the strong-Wolfe certificate.
-/

public section

noncomputable section

open scoped Topology

namespace DFP

/-- TASK-09: A parameterized planar strong-Wolfe counterexample extends to every
finite dimension `n ≥ 2` with the same Hessian bounds and Wolfe coefficients. -/
theorem existsStrongWolfeCounterexample_of_dimension_ge_two
    (n : ℕ) (hn : 2 ≤ n) {c₁ c₂ : ℝ}
    (hc₁_pos : 0 < c₁) (hc₁_lt_two_thirds : c₁ < 2 / 3)
    (hc₂_ge_two_thirds : (2 / 3 : ℝ) ≤ c₂) (hc₂_lt_one : c₂ < 1) :
    Nonempty (DFP.StrongWolfeCounterexample
      (Fin n) (1 / 2) (3 / 2) c₁ c₂) := by
  classical
  obtain ⟨cPlanar⟩ := existsPlanarStrongWolfeCounterexample
    hc₁_pos hc₁_lt_two_thirds hc₂_ge_two_thirds hc₂_lt_one
  let m : ℕ := n - 2
  have hLowerIdentity : (1 / 2 : ℝ) ≤ 1 := by
    norm_num
  have hIdentityUpper : (1 : ℝ) ≤ 3 / 2 := by
    norm_num
  obtain ⟨cSum⟩ := DFP.StrongWolfeCounterexample.orthogonalSum
    (κ := Fin m) cPlanar hLowerIdentity hIdentityUpper
  have hdimension : 2 + m = n := by
    dsimp only [m]
    omega
  let e : Fin n ≃ Fin 2 ⊕ Fin m :=
    (finCongr hdimension.symm).trans finSumFinEquiv.symm
  let Q : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 2 ⊕ Fin m) :=
    LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e
  have hLowerNonnegative : (0 : ℝ) ≤ 1 / 2 := by
    norm_num
  have hUpperNonnegative : (0 : ℝ) ≤ 3 / 2 := by
    norm_num
  exact DFP.StrongWolfeCounterexample.pullback_linearIsometryEquiv cSum Q
    hLowerNonnegative hUpperNonnegative

end DFP
