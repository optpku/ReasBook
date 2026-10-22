/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.StrictProjectionCycle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

open scoped RealInnerProductSpace

namespace ConsensusADMM.ProjectionCycle

universe u
variable {N : ℕ} {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Equal-norm, nonzero, distinct vectors strictly support their own finite hull. -/
theorem strictNonselfSupports_self {p : ZMod N → E}
    (hinj : Function.Injective p) (hnonzero : ∀ i, p i ≠ 0)
    (hnorm : ∀ i j, ‖p i‖ = ‖p j‖) : StrictNonselfSupports p p := by
  intro i
  refine ⟨real_inner_self_pos.mpr (hnonzero i), fun j hji ↦ ?_⟩
  have hd : p i - p j ≠ 0 := sub_ne_zero.mpr (fun h ↦ hji (hinj h).symm)
  have hdist := real_inner_self_pos.mpr hd
  have hnormsq : inner ℝ (p i) (p i) = inner ℝ (p j) (p j) := by
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hnorm i j]
  simp only [inner_sub_left, inner_sub_right, real_inner_comm (p j) (p i)] at hdist ⊢
  linarith

/-- Successor invariance on a cyclic index makes any scalar statistic constant. -/
theorem cyclic_statistic_constant [NeZero N] {α : Type*} (f : ZMod N → α)
    (hstep : ∀ i, f (i + 1) = f i) : ∀ i j, f i = f j := by
  have hnat : ∀ k : ℕ, f (k : ZMod N) = f 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k hk => simpa [Nat.cast_add, Nat.cast_one] using (hstep (k : ZMod N)).trans hk
  intro i j
  simpa using (hnat i.val).trans (hnat j.val).symm

/-- Subtracting an isometry from a scalar multiple of identity is injective
when the scalar has absolute value different from one. -/
theorem scalar_sub_isometry_injective (U : E ≃ₗᵢ[ℝ] E) (c : ℝ)
    (hc : |c| ≠ 1) : Function.Injective (c • (LinearMap.id : E →ₗ[ℝ] E) - U.toLinearMap) := by
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  have hrel : c • x = U x := sub_eq_zero.mp hx
  have hnorm := congrArg norm hrel
  rw [norm_smul, Real.norm_eq_abs, U.norm_map] at hnorm
  have hzero : ‖x‖ = 0 := by
    apply (mul_eq_zero.mp (show (|c| - 1) * ‖x‖ = 0 by nlinarith)).resolve_left
    exact sub_ne_zero.mpr hc
  exact norm_eq_zero.mp hzero

noncomputable section

variable [NeZero N]

/-- The orthogonal coordinate permutation advancing one cyclic basis vector. -/
def auxiliaryShift : EuclideanSpace ℝ (ZMod N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (ZMod N) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.addRight (1 : ZMod N))

/-- Coordinate basis vectors advance under the auxiliary shift. -/
theorem auxiliaryShift_single (i : ZMod N) :
    auxiliaryShift (EuclideanSpace.single i (1 : ℝ)) =
      EuclideanSpace.single (i + 1) (1 : ℝ) := by
  exact EuclideanSpace.piLpCongrLeft_single (Equiv.addRight (1 : ZMod N)) i 1

/-- Coordinate basis vectors retreat under the inverse auxiliary shift. -/
theorem auxiliaryShift_symm_single (i : ZMod N) :
    auxiliaryShift.symm (EuclideanSpace.single i (1 : ℝ)) =
      EuclideanSpace.single (i - 1) (1 : ℝ) := by
  apply auxiliaryShift.injective
  rw [LinearIsometryEquiv.apply_symm_apply, auxiliaryShift_single, sub_add_cancel]

/-- Invertible predecessor resolvent on the auxiliary coordinate space. -/
def auxiliaryResolvent (c : ℝ) (hc : |c| ≠ 1) :
    EuclideanSpace ℝ (ZMod N) ≃ₗ[ℝ] EuclideanSpace ℝ (ZMod N) :=
  LinearEquiv.ofInjectiveEndo
    (c • LinearMap.id - auxiliaryShift.symm.toLinearMap)
    (scalar_sub_isometry_injective (auxiliaryShift (N := N)).symm c hc)

/-- Evaluation of the predecessor resolvent. -/
theorem auxiliaryResolvent_apply (c : ℝ) (hc : |c| ≠ 1)
    (x : EuclideanSpace ℝ (ZMod N)) :
    auxiliaryResolvent c hc x = c • x - auxiliaryShift.symm x := rfl

/-- The resolvent commutes with cyclic shifts. -/
theorem auxiliaryResolvent_shift (c : ℝ) (hc : |c| ≠ 1)
    (x : EuclideanSpace ℝ (ZMod N)) :
    auxiliaryResolvent c hc (auxiliaryShift x) =
      auxiliaryShift (auxiliaryResolvent c hc x) := by
  simp [auxiliaryResolvent_apply]

/-- The inverse resolvent also commutes with cyclic shifts. -/
theorem auxiliaryResolvent_symm_shift (c : ℝ) (hc : |c| ≠ 1)
    (x : EuclideanSpace ℝ (ZMod N)) :
    (auxiliaryResolvent c hc).symm (auxiliaryShift x) =
      auxiliaryShift ((auxiliaryResolvent c hc).symm x) := by
  apply (auxiliaryResolvent c hc).injective
  rw [LinearEquiv.apply_symm_apply, auxiliaryResolvent_shift,
    LinearEquiv.apply_symm_apply]

/-- An auxiliary first-block vertex map with first normal equal to its vertex. -/
def auxiliaryFirstMap (γ : ℝ) :
    EuclideanSpace ℝ (ZMod N) →ₗ[ℝ] EuclideanSpace ℝ (ZMod N) :=
  (auxiliaryResolvent 2 (by norm_num)).symm.toLinearMap.comp
    ((-auxiliaryShift.symm.toLinearMap).comp
      ((1 + γ) • LinearMap.id - auxiliaryShift.symm.toLinearMap))

/-- The auxiliary first-block vertex map is injective for positive factors. -/
theorem auxiliaryFirstMap_injective {γ : ℝ} (hγ : 0 < γ) :
    Function.Injective (auxiliaryFirstMap (N := N) γ) := by
  apply (auxiliaryResolvent 2 (by norm_num)).symm.injective.comp
  apply (neg_injective.comp auxiliaryShift.symm.injective).comp
  apply scalar_sub_isometry_injective (auxiliaryShift (N := N)).symm (1 + γ)
  rw [abs_of_pos (by linarith)]
  linarith

/-- The auxiliary first-block vertex map respects the phase shift. -/
theorem auxiliaryFirstMap_shift (γ : ℝ) (x : EuclideanSpace ℝ (ZMod N)) :
    auxiliaryFirstMap γ (auxiliaryShift x) = auxiliaryShift (auxiliaryFirstMap γ x) := by
  change (auxiliaryResolvent 2 (by norm_num)).symm
      (-auxiliaryShift.symm ((1 + γ) • auxiliaryShift x - auxiliaryShift.symm (auxiliaryShift x))) =
    auxiliaryShift ((auxiliaryResolvent 2 (by norm_num)).symm
      (-auxiliaryShift.symm ((1 + γ) • x - auxiliaryShift.symm x)))
  rw [show -auxiliaryShift.symm ((1 + γ) • auxiliaryShift x -
      auxiliaryShift.symm (auxiliaryShift x)) =
      auxiliaryShift (-auxiliaryShift.symm ((1 + γ) • x - auxiliaryShift.symm x)) by simp]
  exact auxiliaryResolvent_symm_shift 2 (by norm_num) _

/-- Auxiliary phase families that make the first block strict. -/
def auxiliaryFirstEta (γ : ℝ) (i : ZMod N) : EuclideanSpace ℝ (ZMod N) :=
  auxiliaryFirstMap γ (EuclideanSpace.single i 1) - EuclideanSpace.single i 1 +
    EuclideanSpace.single (i - 1) 1

/-- Auxiliary multipliers use the coordinate basis scaled by the factor. -/
def auxiliaryNu (γ : ℝ) (i : ZMod N) : EuclideanSpace ℝ (ZMod N) :=
  γ • EuclideanSpace.single i 1

/-- Auxiliary phase families that make the second block strict. -/
def auxiliarySecondEta (γ : ℝ) (i : ZMod N) : EuclideanSpace ℝ (ZMod N) :=
  EuclideanSpace.single i 1 + (γ - 1) • EuclideanSpace.single (i - 1) 1

omit [NeZero N] in
/-- Auxiliary residuals are the difference of adjacent coordinate vectors. -/
theorem auxiliary_residual {γ : ℝ} (hγ : γ ≠ 0) (i : ZMod N) :
    residual γ (auxiliaryNu γ) i =
      EuclideanSpace.single i 1 - EuclideanSpace.single (i - 1) 1 := by
  simp [residual, auxiliaryNu, ← smul_sub, smul_smul, hγ]

/-- Auxiliary second-block normals agree with their second-block vertices. -/
theorem auxiliary_secondNormal {γ : ℝ} (hγ : γ ≠ 0) (i : ZMod N) :
    secondNormal γ (auxiliaryNu γ) i = auxiliarySecondEta γ i := by
  rw [secondNormal, auxiliary_residual hγ]
  simp only [auxiliaryNu, auxiliarySecondEta, sub_smul, one_smul]
  abel

/-- The first auxiliary vertex has the prescribed invertible coefficient map. -/
theorem auxiliary_firstVertex {γ : ℝ} (hγ : γ ≠ 0) (i : ZMod N) :
    xVertex γ (auxiliaryFirstEta γ) (auxiliaryNu γ) i =
      auxiliaryFirstMap γ (EuclideanSpace.single i 1) := by
  rw [xVertex, auxiliary_residual hγ, auxiliaryFirstEta]
  abel

/-- Cyclic symmetry of the first auxiliary construction. -/
theorem auxiliary_first_symmetry (γ : ℝ) :
    HasOrthogonalCyclicSymmetry (auxiliaryFirstEta (N := N) γ) (auxiliaryNu γ) := by
  refine ⟨auxiliaryShift, fun i ↦ ⟨?_, ?_⟩⟩
  · simp only [auxiliaryFirstEta, map_add, map_sub, ← auxiliaryFirstMap_shift,
      auxiliaryShift_single]
    simp
  · simp [auxiliaryNu, auxiliaryShift_single]

/-- Cyclic symmetry of the second auxiliary construction. -/
theorem auxiliary_second_symmetry (γ : ℝ) :
    HasOrthogonalCyclicSymmetry (auxiliarySecondEta (N := N) γ) (auxiliaryNu γ) := by
  refine ⟨auxiliaryShift, fun i ↦ ⟨?_, ?_⟩⟩
  · simp [auxiliarySecondEta, auxiliaryShift_single]
  · simp [auxiliaryNu, auxiliaryShift_single]

/-- The first auxiliary normal equals the first vertex, by the resolvent equation. -/
theorem auxiliary_firstNormal {γ : ℝ} (hγ : γ ≠ 0) (i : ZMod N) :
    firstNormal γ (auxiliaryFirstEta γ) (auxiliaryNu γ) i =
      auxiliaryFirstMap γ (EuclideanSpace.single i 1) := by
  let e := EuclideanSpace.single i (1 : ℝ)
  let x := auxiliaryFirstMap γ e
  have hprev : auxiliaryFirstMap γ (EuclideanSpace.single (i - 1) 1) =
      auxiliaryShift.symm x := by
    apply auxiliaryShift.injective
    rw [← auxiliaryFirstMap_shift, auxiliaryShift_single, sub_add_cancel,
      LinearIsometryEquiv.apply_symm_apply]
  have hres : (2 : ℝ) • x - auxiliaryShift.symm x =
      -auxiliaryShift.symm ((1 + γ) • e - auxiliaryShift.symm e) := by
    change auxiliaryResolvent 2 (by norm_num)
      ((auxiliaryResolvent 2 (by norm_num)).symm _) = _
    exact LinearEquiv.apply_symm_apply _ _
  rw [firstNormal, auxiliary_firstVertex hγ]
  change auxiliaryFirstEta γ (i - 1) - auxiliaryNu γ (i - 1) - x = x
  rw [auxiliaryFirstEta, hprev, auxiliaryNu]
  apply sub_eq_zero.mp
  have halg : (auxiliaryShift.symm x - EuclideanSpace.single (i - 1) 1 +
      EuclideanSpace.single (i - 1 - 1) 1 - γ • EuclideanSpace.single (i - 1) 1 - x) - x =
      -(((2 : ℝ) • x - auxiliaryShift.symm x) -
        (-auxiliaryShift.symm ((1 + γ) • e - auxiliaryShift.symm e))) := by
    simp only [map_sub, map_add, map_smul, e, auxiliaryShift_symm_single, add_smul, one_smul,
      two_smul]
    abel
  rw [halg, hres, sub_self, neg_zero]

/-- The first auxiliary block has all origin and nonself margins strictly positive. -/
theorem auxiliary_first_strict {γ : ℝ} (hγ : 0 < γ) :
    StrictNonselfSupports (xVertex γ (auxiliaryFirstEta (N := N) γ) (auxiliaryNu γ))
      (firstNormal γ (auxiliaryFirstEta γ) (auxiliaryNu γ)) := by
  have hx : xVertex γ (auxiliaryFirstEta (N := N) γ) (auxiliaryNu γ) =
      fun i ↦ auxiliaryFirstMap γ (EuclideanSpace.single i 1) :=
    funext (auxiliary_firstVertex hγ.ne')
  have ha : firstNormal γ (auxiliaryFirstEta (N := N) γ) (auxiliaryNu γ) =
      fun i ↦ auxiliaryFirstMap γ (EuclideanSpace.single i 1) :=
    funext (auxiliary_firstNormal hγ.ne')
  rw [hx, ha]
  apply strictNonselfSupports_self
  · exact (auxiliaryFirstMap_injective hγ).comp
      EuclideanSpace.orthonormal_single.linearIndependent.injective
  · intro i hi
    have hz : EuclideanSpace.single i (1 : ℝ) = 0 :=
      (auxiliaryFirstMap_injective hγ) (by simpa using hi)
    exact EuclideanSpace.orthonormal_single.ne_zero i hz
  · apply cyclic_statistic_constant
    intro i
    rw [← auxiliaryShift_single, auxiliaryFirstMap_shift, LinearIsometryEquiv.norm_map]

/-- The second auxiliary block has all origin and nonself margins strictly positive. -/
theorem auxiliary_second_strict {γ : ℝ} (hγ : 0 < γ) (hγtwo : γ < 2) :
    StrictNonselfSupports (auxiliarySecondEta (N := N) γ) (secondNormal γ (auxiliaryNu γ)) := by
  have hc : secondNormal γ (auxiliaryNu (N := N) γ) = auxiliarySecondEta γ :=
    funext (auxiliary_secondNormal hγ.ne')
  rw [hc]
  let L : EuclideanSpace ℝ (ZMod N) →ₗ[ℝ] EuclideanSpace ℝ (ZMod N) :=
    LinearMap.id + (γ - 1) • auxiliaryShift.symm.toLinearMap
  have hL : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    have hrel : x = -((γ - 1) • auxiliaryShift.symm x) := eq_neg_of_add_eq_zero_left hx
    have hnorm := congrArg norm hrel
    rw [norm_neg, norm_smul, Real.norm_eq_abs, LinearIsometryEquiv.norm_map] at hnorm
    have hlt : |γ - 1| < 1 := abs_lt.mpr ⟨by linarith, by linarith⟩
    have hz : ‖x‖ = 0 := by nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hz
  have hformula (i : ZMod N) : auxiliarySecondEta γ i = L (EuclideanSpace.single i 1) := by
    simp [auxiliarySecondEta, L, auxiliaryShift_symm_single]
  apply strictNonselfSupports_self
  · intro i j hij
    simp only [hformula] at hij
    exact EuclideanSpace.orthonormal_single.linearIndependent.injective (hL hij)
  · intro i hi
    rw [hformula] at hi
    have hz : EuclideanSpace.single i (1 : ℝ) = 0 := hL (by simpa using hi)
    exact EuclideanSpace.orthonormal_single.ne_zero i hz
  · apply cyclic_statistic_constant
    intro i
    have hshift : auxiliaryShift (auxiliarySecondEta γ i) = auxiliarySecondEta γ (i + 1) := by
      simp [auxiliarySecondEta, auxiliaryShift_single]
    rw [← hshift, LinearIsometryEquiv.norm_map]

end
end ConsensusADMM.ProjectionCycle
