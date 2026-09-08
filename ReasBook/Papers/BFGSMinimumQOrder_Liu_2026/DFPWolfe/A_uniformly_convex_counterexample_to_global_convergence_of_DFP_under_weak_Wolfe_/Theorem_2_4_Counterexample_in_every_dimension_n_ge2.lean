module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Theorem_2_3_Uniformly_convex_weak_Wolfe_DFP_counterexample_in_dimension_two
public import ReasLib.Optimization.DFP.WolfeCounterexample.Transport

public section

noncomputable section

namespace DFP

/-- The paper's fixed constants specialize the reusable weak-Wolfe
counterexample certificate. -/
abbrev WeakWolfeCounterexample (ι : Type u) [Fintype ι] :=
  DFP.WolfeCounterexample ι (1 / 2) (3 / 2) (1 / 4) (3 / 4)

/-- Theorem 2.4 (Counterexample in every dimension $n\ge2$): for every `n` with
`2 ≤ n`, there is a globally `C²` objective on `EuclideanSpace ℝ (Fin n)` with
Hessian between `(1 / 2)I` and `(3 / 2)I`, and a positive-step inverse-form DFP
trajectory satisfying weak Wolfe with `(1 / 4, 3 / 4)` whose gradient norms tend to
a positive limit. -/
theorem existsWeakWolfeCounterexample (n : ℕ) (hn : 2 ≤ n) :
    Nonempty (WeakWolfeCounterexample (Fin n)) := by
  classical
  obtain ⟨cPlanar⟩ := existsPlanarWeakWolfeCounterexample
  let m : ℕ := n - 2
  have hLowerIdentity : (1 / 2 : ℝ) ≤ 1 := by
    norm_num
  have hIdentityUpper : (1 : ℝ) ≤ 3 / 2 := by
    norm_num
  obtain ⟨cSum⟩ := DFP.WolfeCounterexample.orthogonalSum
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
  exact DFP.WolfeCounterexample.pullback_linearIsometryEquiv cSum Q
    hLowerNonnegative hUpperNonnegative

end DFP
