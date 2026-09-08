module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import ReasLib.LinearAlgebra.Matrix.PosDef.Operator
public import ReasLib.Optimization.DFP.Operator.Orbit
public import ReasLib.Optimization.DFP.Orbit
import Mathlib.Tactic.Abel

public section

/-!
# Matrix adapters for coordinate-free DFP orbits
-/

noncomputable section

universe u v

open scoped Matrix

namespace Matrix

/-- The Euclidean operator represented by a matrix DFP update is the coordinate-free operator
DFP update. -/
theorem toEuclideanCLM_inverseDFPUpdate {n : Type u} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (s y : EuclideanSpace ℝ n) :
    toEuclideanCLM (n := n) (𝕜 := ℝ)
        (inverseDFPUpdate H (WithLp.ofLp s) (WithLp.ofLp y)) =
      DFP.Operator.inverseUpdate (toEuclideanCLM (n := n) (𝕜 := ℝ) H) s y := by
  have hrank (u v : EuclideanSpace ℝ n) :
      (toEuclideanCLM : Matrix n n ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n).symm
          (InnerProductSpace.rankOne ℝ u v) =
        Matrix.vecMulVec u.ofLp v.ofLp := by
    have hrepr (A : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :
        (toEuclideanCLM : Matrix n n ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n).symm A =
          Matrix.toEuclideanLin.symm A.toLinearMap := by
      apply EquivLike.injective (toEuclideanCLM : Matrix n n ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)
      apply ContinuousLinearMap.ext
      intro z
      apply (WithLp.ofLp_injective 2)
      simp only [Matrix.ofLp_toEuclideanCLM]
      rfl
    rw [hrepr]
    simpa using (InnerProductSpace.symm_toEuclideanLin_rankOne u v)
  apply EquivLike.injective ((toEuclideanCLM : Matrix n n ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n).symm)
  simp only [StarAlgEquiv.symm_apply_apply]
  have hupdate :
      DFP.Operator.inverseUpdate (toEuclideanCLM (n := n) (𝕜 := ℝ) H) s y =
        toEuclideanCLM (n := n) (𝕜 := ℝ) H -
            (inner ℝ y ((toEuclideanCLM (n := n) (𝕜 := ℝ) H) y))⁻¹ •
              InnerProductSpace.rankOne ℝ
                ((toEuclideanCLM (n := n) (𝕜 := ℝ) H) y)
                ((ContinuousLinearMap.adjoint
                  (toEuclideanCLM (n := n) (𝕜 := ℝ) H)) y) +
          (inner ℝ s y)⁻¹ • InnerProductSpace.rankOne ℝ s s := by
    apply ContinuousLinearMap.ext
    intro x
    rw [DFP.Operator.inverseUpdate_apply]
    simp [InnerProductSpace.rankOne_apply, smul_smul]
  rw [hupdate]
  simp only [map_sub, map_add, map_smul]
  rw [hrank, hrank]
  have hadj (A : Matrix n n ℝ) :
      ContinuousLinearMap.adjoint ((toEuclideanCLM : Matrix n n ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) A) =
        (toEuclideanCLM : Matrix n n ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) A.transpose := by
    apply ContinuousLinearMap.coe_injective
    change (ContinuousLinearMap.adjoint ((toEuclideanCLM : Matrix n n ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) A)).toLinearMap =
      ((toEuclideanCLM : Matrix n n ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) A.transpose).toLinearMap
    rw [← ContinuousLinearMap.adjoint_toLinearMap]
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  have hinner (u v : EuclideanSpace ℝ n) :
      inner ℝ u v = u.ofLp ⬝ᵥ v.ofLp := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [star_trivial, dotProduct_comm]
  rw [hadj]
  rw [Matrix.ofLp_toEuclideanCLM, Matrix.ofLp_toEuclideanCLM]
  rw [hinner]
  apply Matrix.ext
  intro i j
  rw [Matrix.inverseDFPUpdate_apply]
  rw [hinner]
  simp only [StarAlgEquiv.symm_apply_apply, Matrix.ofLp_toEuclideanCLM,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  rw [← Matrix.vecMul_transpose H.transpose y.ofLp]
  simp

end Matrix

namespace DFP.IsOrbit

/-- A matrix-valued Euclidean DFP orbit induces the coordinate-free operator orbit. -/
theorem toOperator {n : Type u} [Fintype n] [DecidableEq n]
    {f : EuclideanSpace ℝ n → ℝ} {alpha : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ n} {H : ℕ → Matrix n n ℝ}
    (h : DFP.IsOrbit f alpha x g H) :
    DFP.Operator.IsOrbit f alpha x g
      (fun k ↦ Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (H k)) := by
  have hsteps (k : ℕ) :
      DFP.Operator.steps alpha
          (fun j ↦ Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (H j)) g k =
        DFP.steps alpha (DFP.directions H g) k := by
    rw [DFP.Operator.steps_apply, DFP.Operator.step_apply,
      DFP.Operator.direction_apply, DFP.steps_apply, DFP.directions_apply]
    apply congrArg (fun z : EuclideanSpace ℝ n ↦ alpha k • (-z))
    apply WithLp.ofLp_injective 2
    simp only [Matrix.ofLp_toEuclideanCLM]
  have hgrad (k : ℕ) :
      DFP.Operator.gradientChanges g k = DFP.gradientChanges g k := by
    rw [DFP.Operator.gradientChanges_apply, DFP.Operator.gradientChange_apply,
      DFP.gradientChanges_apply]
  constructor
  · exact h.stepLengthPos
  · exact h.gradientAt
  · intro k
    simpa only [hsteps k] using h.pointSucc k
  · intro k
    calc
      Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (H (k + 1)) =
          Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)
            (Matrix.inverseDFPUpdate (H k)
              (WithLp.ofLp (DFP.steps alpha (DFP.directions H g) k))
              (WithLp.ofLp (DFP.gradientChanges g k))) :=
        congrArg (fun A : Matrix n n ℝ ↦
          Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A) (h.inverseHessianSucc k)
      _ = DFP.Operator.inverseUpdate
          (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (H k))
          (DFP.steps alpha (DFP.directions H g) k)
          (DFP.gradientChanges g k) :=
        Matrix.toEuclideanCLM_inverseDFPUpdate _ _ _
      _ = DFP.Operator.inverseUpdate
          (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (H k))
          (DFP.Operator.steps alpha
            (fun j ↦ Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) (H j)) g k)
          (DFP.Operator.gradientChanges g k) := by
        rw [hsteps, hgrad]

end DFP.IsOrbit

namespace DFP.Operator.IsOrbit

/-- A coordinate-free DFP orbit on Euclidean space induces a matrix-valued orbit in the
canonical orthonormal basis. -/
theorem toMatrix {n : Type u} [Fintype n] [DecidableEq n]
    {f : EuclideanSpace ℝ n → ℝ} {alpha : ℕ → ℝ}
    {x g : ℕ → EuclideanSpace ℝ n}
    {H : ℕ → EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n}
    (h : DFP.Operator.IsOrbit f alpha x g H) :
    DFP.IsOrbit f alpha x g
      (fun k ↦ (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).symm (H k)) := by
  have hsteps (k : ℕ) :
      DFP.steps alpha
          (DFP.directions
            (fun j ↦ (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)).symm (H j)) g) k =
        DFP.Operator.steps alpha H g k := by
    rw [DFP.steps_apply, DFP.directions_apply, DFP.Operator.steps_apply,
      DFP.Operator.step_apply, DFP.Operator.direction_apply]
    apply congrArg (fun z : EuclideanSpace ℝ n ↦ alpha k • (-z))
    apply WithLp.ofLp_injective 2
    rw [← Matrix.ofLp_toEuclideanCLM]
    simp only [StarAlgEquiv.apply_symm_apply]
  have hgrad (k : ℕ) :
      DFP.gradientChanges g k = DFP.Operator.gradientChanges g k := by
    rw [DFP.gradientChanges_apply, DFP.Operator.gradientChanges_apply,
      DFP.Operator.gradientChange_apply]
  constructor
  · exact h.stepLengthPos
  · exact h.gradientAt
  · intro k
    simpa only [hsteps k] using h.pointSucc k
  · intro k
    apply EquivLike.injective (Matrix.toEuclideanCLM : Matrix n n ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)
    rw [StarAlgEquiv.apply_symm_apply]
    rw [Matrix.toEuclideanCLM_inverseDFPUpdate]
    rw [StarAlgEquiv.apply_symm_apply, hsteps, hgrad]
    exact h.inverseHessianSucc k

end DFP.Operator.IsOrbit

namespace DFP.InverseIteration

/-- Pulling an inverse-form DFP iteration back through a linear isometry transports its
points, gradients, and inverse Hessians to the new Euclidean coordinates. -/
noncomputable def pullback_linearIsometryEquiv
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    DFP.InverseIteration κ := by
  have hQfun :
      (Q.toContinuousLinearEquiv :
        EuclideanSpace ℝ κ → EuclideanSpace ℝ ι) = Q := rfl
  have hQsymmfun :
      (Q.toContinuousLinearEquiv.symm :
        EuclideanSpace ℝ ι → EuclideanSpace ℝ κ) = Q.symm := rfl
  have hQapply (z : EuclideanSpace ℝ κ) :
      Q.toContinuousLinearEquiv z = Q z := rfl
  have hQcoe :
      ((Q : EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ ι) :
        EuclideanSpace ℝ κ → EuclideanSpace ℝ ι) = Q := rfl
  have hQsymmCoe :
      ((Q.symm : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ) :
        EuclideanSpace ℝ ι → EuclideanSpace ℝ κ) = Q.symm := rfl
  let f : EuclideanSpace ℝ κ → ℝ :=
    it.objective ∘ Q.toContinuousLinearEquiv
  let α : ℕ → ℝ := it.stepLength
  let x : ℕ → EuclideanSpace ℝ κ := fun k ↦ Q.symm (it.point k)
  let g : ℕ → EuclideanSpace ℝ κ :=
    fun k ↦ Q.symm (DFP.gradients it.objective it.point k)
  let H : ℕ → Matrix κ κ ℝ := fun k ↦
    (Matrix.toEuclideanCLM : Matrix κ κ ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ).symm
      (Q.toContinuousLinearEquiv.symm.toContinuousLinearMap.pushforward
        ((Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
          EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
            (it.inverseHessian k)))
  have hPullRaw :=
    (((it.isOrbit hStep).toOperator).pullback Q.toContinuousLinearEquiv).toMatrix
  have hPull : DFP.IsOrbit f α x g H := by
    simpa only [f, α, x, g, H, hQfun, hQsymmfun,
      hQcoe, hQsymmCoe, hQapply, Q.adjoint_eq_symm] using hPullRaw
  have hPosDef (k : ℕ) : (H k).PosDef := by
    dsimp only [H]
    exact Matrix.PosDef.congr_linearIsometryEquiv
      (it.inverseHessianPosDef k) Q
  have hStepPulled (k : ℕ) :
      DFP.steps α (DFP.directions H g) k =
        Q.symm
          (DFP.steps it.stepLength
            (DFP.directions it.inverseHessian
              (DFP.gradients it.objective it.point)) k) := by
    calc
      DFP.steps α (DFP.directions H g) k = x (k + 1) - x k := by
        rw [hPull.pointSucc k]
        abel
      _ = Q.symm (it.point (k + 1) - it.point k) := by
        dsimp only [x]
        rw [map_sub]
      _ = Q.symm
          (DFP.steps it.stepLength
            (DFP.directions it.inverseHessian
              (DFP.gradients it.objective it.point)) k) := by
        congr 1
        rw [it.pointSucc k]
        abel
  have hChangePulled (k : ℕ) :
      DFP.gradientChanges g k =
        Q.symm (DFP.gradientChanges
          (DFP.gradients it.objective it.point) k) := by
    rw [DFP.gradientChanges_apply, DFP.gradientChanges_apply]
    dsimp only [g]
    rw [map_sub]
  have hSecantDenominator (k : ℕ) :
      WithLp.ofLp (DFP.steps α (DFP.directions H g) k) ⬝ᵥ
        WithLp.ofLp (DFP.gradientChanges g k) ≠ 0 := by
    let s := DFP.steps it.stepLength
      (DFP.directions it.inverseHessian
        (DFP.gradients it.objective it.point)) k
    let y := DFP.gradientChanges (DFP.gradients it.objective it.point) k
    have hdotReverse :
        WithLp.ofLp (Q.symm y) ⬝ᵥ WithLp.ofLp (Q.symm s) =
          WithLp.ofLp y ⬝ᵥ WithLp.ofLp s := by
      have hinner := Q.symm.inner_map_map s y
      simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial] using hinner
    have hdot :
        WithLp.ofLp (Q.symm s) ⬝ᵥ WithLp.ofLp (Q.symm y) =
          WithLp.ofLp s ⬝ᵥ WithLp.ofLp y := by
      calc
        _ = WithLp.ofLp (Q.symm y) ⬝ᵥ WithLp.ofLp (Q.symm s) :=
          dotProduct_comm _ _
        _ = WithLp.ofLp y ⬝ᵥ WithLp.ofLp s := hdotReverse
        _ = _ := dotProduct_comm _ _
    rw [hStepPulled, hChangePulled]
    simpa only [s, y, hdot] using it.secantDenominatorNe k
  exact hPull.toInverseIteration hPosDef hSecantDenominator

/-- Pullback through a linear isometry precomposes the iteration objective by that
isometry. -/
@[simp]
theorem pullback_linearIsometryEquiv_objective
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (it.pullback_linearIsometryEquiv hStep Q).objective =
      it.objective ∘ Q := by
  rw [pullback_linearIsometryEquiv, DFP.IsOrbit.toInverseIteration_objective]
  rfl

/-- Pullback through a linear isometry leaves the step-length sequence unchanged. -/
@[simp]
theorem pullback_linearIsometryEquiv_stepLength
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    (it.pullback_linearIsometryEquiv hStep Q).stepLength = it.stepLength := by
  rw [pullback_linearIsometryEquiv, DFP.IsOrbit.toInverseIteration_stepLength]

/-- Pullback through a linear isometry applies the inverse isometry to every point. -/
@[simp]
theorem pullback_linearIsometryEquiv_point
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (k : ℕ) :
    (it.pullback_linearIsometryEquiv hStep Q).point k = Q.symm (it.point k) := by
  rw [pullback_linearIsometryEquiv, DFP.IsOrbit.toInverseIteration_point]

/-- Pullback through a linear isometry represents the conjugated inverse-Hessian
operator in the target's canonical Euclidean basis. -/
@[simp]
theorem pullback_linearIsometryEquiv_inverseHessian
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (k : ℕ) :
    (it.pullback_linearIsometryEquiv hStep Q).inverseHessian k =
      (Matrix.toEuclideanCLM : Matrix κ κ ℝ ≃⋆ₐ[ℝ]
        EuclideanSpace ℝ κ →L[ℝ] EuclideanSpace ℝ κ).symm
        (Q.toContinuousLinearEquiv.symm.toContinuousLinearMap.pushforward
          ((Matrix.toEuclideanCLM : Matrix ι ι ℝ ≃⋆ₐ[ℝ]
            EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
              (it.inverseHessian k))) := by
  rw [pullback_linearIsometryEquiv,
    DFP.IsOrbit.toInverseIteration_inverseHessian]

/-- The canonical gradient sequence of an isometric pullback is obtained by applying
the inverse isometry to the original canonical gradients. -/
@[simp]
theorem pullback_linearIsometryEquiv_gradients
    {ι : Type u} {κ : Type v}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (it : DFP.InverseIteration ι) (hStep : ∀ k, 0 < it.stepLength k)
    (Q : EuclideanSpace ℝ κ ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    DFP.gradients (it.pullback_linearIsometryEquiv hStep Q).objective
        (it.pullback_linearIsometryEquiv hStep Q).point =
      fun k ↦ Q.symm (DFP.gradients it.objective it.point k) := by
  funext k
  rw [DFP.gradients_apply, pullback_linearIsometryEquiv_objective,
    pullback_linearIsometryEquiv_point]
  have hstart : Q (Q.symm (it.point k)) = it.point k :=
    Q.apply_symm_apply (it.point k)
  have hgradient := Q.toContinuousLinearEquiv.comp_right_gradient
    it.objective (Q.symm (it.point k))
  simpa [Function.comp_def, hstart, Q.adjoint_eq_symm,
    DFP.gradients_apply] using hgradient

end DFP.InverseIteration
