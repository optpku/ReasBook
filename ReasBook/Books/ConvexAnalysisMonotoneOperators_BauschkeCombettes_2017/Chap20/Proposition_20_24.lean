/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_23
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Definition_20_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

noncomputable section

namespace ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem isCoercive_toSesqForm_of_isStronglyMonotone
    (U : H →L[ℝ] H) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    IsCoercive (ContinuousLinearMap.toSesqForm U) := by
  refine ⟨α, hU_strong.pos, ?_⟩
  intro x
  change α * ‖x‖ * ‖x‖ ≤ ⟪x, U x⟫_ℝ
  simpa [pow_two, real_inner_comm, mul_assoc] using hU_strong.ineq x

variable [CompleteSpace H]

theorem coerciveEquivOfToSesqForm_eq_of_isSelfAdjoint_of_isStronglyMonotone
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    (((isCoercive_toSesqForm_of_isStronglyMonotone U hU_strong).continuousLinearEquivOfBilin :
        H ≃L[ℝ] H) : H →L[ℝ] H) = U := by
  ext x
  symm
  exact IsCoercive.unique_continuousLinearEquivOfBilin
    (isCoercive_toSesqForm_of_isStronglyMonotone U hU_strong)
    (fun y ↦ by
      calc
        ⟪U x, y⟫_ℝ = ⟪x, U y⟫_ℝ := by
          simpa using hU_self.isSymmetric x y
        _ = ((ContinuousLinearMap.toSesqForm U) x) y := by
          rfl)

theorem isInvertible_of_isStronglyMonotone
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    U.IsInvertible := by
  refine ⟨(isCoercive_toSesqForm_of_isStronglyMonotone U hU_strong).continuousLinearEquivOfBilin,
    ?_⟩
  simpa using coerciveEquivOfToSesqForm_eq_of_isSelfAdjoint_of_isStronglyMonotone
    U hU_self hU_strong

theorem inverse_eq_coerciveEquiv_symm_of_isSelfAdjoint_of_isStronglyMonotone
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    U.inverse =
      ((
        (isCoercive_toSesqForm_of_isStronglyMonotone U hU_strong).continuousLinearEquivOfBilin
      ).symm : H →L[ℝ] H) := by
  let E := (isCoercive_toSesqForm_of_isStronglyMonotone U hU_strong).continuousLinearEquivOfBilin
  simpa [E, coerciveEquivOfToSesqForm_eq_of_isSelfAdjoint_of_isStronglyMonotone
    U hU_self hU_strong] using
    (ContinuousLinearMap.inverse_equiv E)

theorem inner_inverse_map_eq_inner_of_isSelfAdjoint_of_isStronglyMonotone
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) (x y : H) :
    ⟪U.inverse x, U y⟫_ℝ = ⟪x, y⟫_ℝ := by
  have hU_inv : U.IsInvertible := isInvertible_of_isStronglyMonotone U hU_self hU_strong
  calc
    ⟪U.inverse x, U y⟫_ℝ = ⟪U (U.inverse x), y⟫_ℝ := by
      simpa using (hU_self.isSymmetric (U.inverse x) y).symm
    _ = ⟪x, y⟫_ℝ := by
      simp [ContinuousLinearMap.IsInvertible.self_apply_inverse hU_inv]

theorem inner_inverse_sub_map_sub_eq_inner_sub_of_isSelfAdjoint_of_isStronglyMonotone
    (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) (x y u v : H) :
    ⟪U.inverse (x - y), U u - U v⟫_ℝ = ⟪x - y, u - v⟫_ℝ := by
  simpa [map_sub] using
    inner_inverse_map_eq_inner_of_isSelfAdjoint_of_isStronglyMonotone
      U hU_self hU_strong (x - y) (u - v)

/-- The renormed Hilbert space `K` from Proposition 20.24, defined on the same vectors as `H`
with inner product `(x, y) ↦ ⟪U⁻¹ x, y⟫_ℝ`. -/
structure Renormed (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) where
  /-- The underlying vector in the original Hilbert space `H`. -/
  down : H

namespace Renormed

variable (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α)

instance instCoe : CoeOut (Renormed U hU_self hU_strong) H := ⟨Renormed.down⟩

/-- The identity-on-vectors map from `H` to the renormed Hilbert space `K`. -/
def up (x : H) : Renormed U hU_self hU_strong := ⟨x⟩

@[simp] theorem down_up (x : H) :
    ((up U hU_self hU_strong x : Renormed U hU_self hU_strong) : H) = x :=
  rfl

@[simp] theorem up_down (x : Renormed U hU_self hU_strong) :
    up U hU_self hU_strong (x : H) = x := by
  cases x
  rfl

@[ext] theorem ext {x y : Renormed U hU_self hU_strong} (hxy : (x : H) = (y : H)) : x = y := by
  cases x
  cases y
  simpa using hxy

/-- The underlying bijection between the renormed Hilbert space `K` and the original space `H`. -/
def equiv : Renormed U hU_self hU_strong ≃ H where
  toFun x := x
  invFun := up U hU_self hU_strong
  left_inv := up_down U hU_self hU_strong
  right_inv := down_up U hU_self hU_strong

instance instAddCommGroup : AddCommGroup (Renormed U hU_self hU_strong) :=
  (equiv U hU_self hU_strong).addCommGroup

instance instModule : Module ℝ (Renormed U hU_self hU_strong) where
  smul r x := up U hU_self hU_strong (r • (x : H))
  one_smul x := by
    apply ext
    change (1 : ℝ) • (x : H) = (x : H)
    simp
  mul_smul r s x := by
    apply ext
    change (r * s) • (x : H) = r • (s • (x : H))
    simpa using (mul_smul r s (x : H))
  smul_zero r := by
    apply ext
    change r • (0 : H) = (0 : H)
    simp
  smul_add r x y := by
    apply ext
    change r • ((x : H) + (y : H)) = r • (x : H) + r • (y : H)
    simp
  add_smul r s x := by
    apply ext
    change (r + s) • (x : H) = r • (x : H) + s • (x : H)
    simpa using (add_smul r s (x : H))
  zero_smul x := by
    apply ext
    change (0 : ℝ) • (x : H) = (0 : H)
    simp

@[reducible] def innerProductSpaceCore
    : InnerProductSpace.Core ℝ (Renormed U hU_self hU_strong) where
  inner x y := ⟪U.inverse (x : H), (y : H)⟫_ℝ
  conj_inner_symm x y := by
    change ⟪U.inverse (y : H), (x : H)⟫_ℝ = ⟪U.inverse (x : H), (y : H)⟫_ℝ
    have hU_inv : U.IsInvertible := isInvertible_of_isStronglyMonotone U hU_self hU_strong
    calc
      ⟪U.inverse (y : H), (x : H)⟫_ℝ = ⟪U.inverse (y : H), U (U.inverse (x : H))⟫_ℝ := by
        simp [ContinuousLinearMap.IsInvertible.self_apply_inverse hU_inv]
      _ = ⟪U (U.inverse (y : H)), U.inverse (x : H)⟫_ℝ := by
        simpa using (hU_self.isSymmetric (U.inverse (y : H)) (U.inverse (x : H))).symm
      _ = ⟪U.inverse (x : H), (y : H)⟫_ℝ := by
        simp [real_inner_comm, ContinuousLinearMap.IsInvertible.self_apply_inverse hU_inv]
  re_inner_nonneg x := by
    let z : H := U.inverse (x : H)
    have hineq : 0 ≤ α * ‖z‖ * ‖z‖ := by
      nlinarith [hU_strong.pos, sq_nonneg ‖z‖]
    have hmono : α * ‖z‖ * ‖z‖ ≤ ⟪z, U z⟫_ℝ := by
      simpa [pow_two, mul_assoc, real_inner_comm] using hU_strong.ineq z
    calc
      0 ≤ α * ‖z‖ * ‖z‖ := hineq
      _ ≤ ⟪z, U z⟫_ℝ := hmono
      _ = ⟪U.inverse (x : H), (x : H)⟫_ℝ := by
        simp [z,
          ContinuousLinearMap.IsInvertible.self_apply_inverse
            (isInvertible_of_isStronglyMonotone U hU_self hU_strong)]
  add_left x y z := by
    change ⟪U.inverse (x + y), (z : H)⟫_ℝ = ⟪U.inverse x, (z : H)⟫_ℝ + ⟪U.inverse y, (z : H)⟫_ℝ
    have hxy := U.inverse.map_add x y
    have hz :
        ⟪U.inverse x + U.inverse y, (z : H)⟫_ℝ =
          ⟪U.inverse x, (z : H)⟫_ℝ + ⟪U.inverse y, (z : H)⟫_ℝ := by
      simpa using inner_add_left (U.inverse x) (U.inverse y) (z : H)
    have hxy' :
        inner ℝ (U.inverse (x + y)) (z : H) =
          inner ℝ (U.inverse x + U.inverse y) (z : H) :=
      congrArg (fun t : H ↦ inner ℝ t (z : H)) hxy
    calc
      ⟪U.inverse (x + y), (z : H)⟫_ℝ = ⟪U.inverse x + U.inverse y, (z : H)⟫_ℝ := by
        exact hxy'
      _ = ⟪U.inverse x, (z : H)⟫_ℝ + ⟪U.inverse y, (z : H)⟫_ℝ := hz
  smul_left x y r := by
    change
      ⟪U.inverse ((r • x : Renormed U hU_self hU_strong) : H), (y : H)⟫_ℝ =
        (starRingEnd ℝ) r * ⟪U.inverse (x : H), (y : H)⟫_ℝ
    have hx := U.inverse.map_smul r x
    have hy :
        ⟪r • U.inverse x, (y : H)⟫_ℝ = (starRingEnd ℝ) r * ⟪U.inverse x, (y : H)⟫_ℝ := by
      simpa using real_inner_smul_left (U.inverse x) (y : H) r
    have hx' :
        inner ℝ (U.inverse (r • x)) (y : H) =
          inner ℝ (r • U.inverse x) (y : H) :=
      congrArg (fun t : H ↦ inner ℝ t (y : H)) hx
    calc
      ⟪U.inverse (r • x), (y : H)⟫_ℝ = ⟪r • U.inverse x, (y : H)⟫_ℝ := by
        exact hx'
      _ = r * ⟪U.inverse x, (y : H)⟫_ℝ := hy
  definite x hx := by
    let z : H := U.inverse (x : H)
    have hU_inv : U.IsInvertible := isInvertible_of_isStronglyMonotone U hU_self hU_strong
    have hz_sq_le : α * ‖z‖ * ‖z‖ ≤ 0 := by
      calc
        α * ‖z‖ * ‖z‖ ≤ ⟪z, U z⟫_ℝ := by
          simpa [pow_two, mul_assoc, real_inner_comm] using hU_strong.ineq z
        _ = 0 := by
          simpa [z,
            ContinuousLinearMap.IsInvertible.self_apply_inverse hU_inv] using hx
    have hz_sq_eq : ‖z‖ * ‖z‖ = 0 := by
      nlinarith [hU_strong.pos, hz_sq_le, sq_nonneg ‖z‖]
    have hz : z = 0 := by
      have hz_norm : ‖z‖ = 0 := by
        nlinarith [hz_sq_eq, norm_nonneg z]
      exact norm_eq_zero.mp hz_norm
    ext
    calc
      (x : H) = U z := by
        simp [z, ContinuousLinearMap.IsInvertible.self_apply_inverse hU_inv]
      _ = 0 := by simp [hz]

instance instInnerProductSpaceCore : InnerProductSpace.Core ℝ (Renormed U hU_self hU_strong) :=
  innerProductSpaceCore U hU_self hU_strong

instance instNormedAddCommGroup : NormedAddCommGroup (Renormed U hU_self hU_strong) := by
  let cd : InnerProductSpace.Core ℝ (Renormed U hU_self hU_strong) :=
    innerProductSpaceCore U hU_self hU_strong
  exact cd.toNormedAddCommGroup

instance instInnerProductSpace : InnerProductSpace ℝ (Renormed U hU_self hU_strong) := by
  letI : InnerProductSpace.Core ℝ (Renormed U hU_self hU_strong) :=
    innerProductSpaceCore U hU_self hU_strong
  exact InnerProductSpace.ofCore inferInstance

private theorem norm_sq_eq_inner_inverse
    (x : Renormed U hU_self hU_strong) :
    ‖x‖ ^ 2 = ⟪U.inverse (x : H), (x : H)⟫_ℝ := by
  calc
    ‖x‖ ^ 2 = ⟪x, x⟫_ℝ := (real_inner_self_eq_norm_sq x).symm
    _ = ⟪U.inverse (x : H), (x : H)⟫_ℝ := rfl

private theorem norm_le_sqrt_inverse_norm_mul_original_norm
    (x : Renormed U hU_self hU_strong) :
    ‖x‖ ≤ Real.sqrt ‖U.inverse‖ * ‖(x : H)‖ := by
  have hsq :
      ‖x‖ ^ 2 ≤ ‖U.inverse‖ * ‖(x : H)‖ ^ 2 := by
    calc
      ‖x‖ ^ 2 = ⟪U.inverse (x : H), (x : H)⟫_ℝ :=
        norm_sq_eq_inner_inverse U hU_self hU_strong x
      _ ≤ ‖U.inverse (x : H)‖ * ‖(x : H)‖ := real_inner_le_norm _ _
      _ ≤ (‖U.inverse‖ * ‖(x : H)‖) * ‖(x : H)‖ := by
        gcongr
        exact U.inverse.le_opNorm (x : H)
      _ = ‖U.inverse‖ * ‖(x : H)‖ ^ 2 := by ring
  have hsq' : ‖x‖ ^ 2 ≤ (Real.sqrt ‖U.inverse‖ * ‖(x : H)‖) ^ 2 := by
    have hsqrt' :
        (Real.sqrt ‖U.inverse‖ * ‖(x : H)‖) ^ 2 = ‖U.inverse‖ * ‖(x : H)‖ ^ 2 := by
      calc
        (Real.sqrt ‖U.inverse‖ * ‖(x : H)‖) ^ 2 =
            (Real.sqrt ‖U.inverse‖) ^ 2 * ‖(x : H)‖ ^ 2 := by ring
        _ = ‖U.inverse‖ * ‖(x : H)‖ ^ 2 := by
          have hsqU : (Real.sqrt ‖U.inverse‖) ^ 2 = ‖U.inverse‖ := by
            exact Real.sq_sqrt (show 0 ≤ ‖U.inverse‖ from norm_nonneg _)
          exact congrArg (fun t : ℝ ↦ t * ‖(x : H)‖ ^ 2) hsqU
    calc
      ‖x‖ ^ 2 ≤ ‖U.inverse‖ * ‖(x : H)‖ ^ 2 := hsq
      _ = (Real.sqrt ‖U.inverse‖ * ‖(x : H)‖) ^ 2 := by
        rw [← hsqrt']
  exact (sq_le_sq₀ (norm_nonneg x) (by positivity)).1 hsq'

private theorem original_norm_le_opNorm_div_sqrt_mul_norm
    (x : Renormed U hU_self hU_strong) :
    ‖(x : H)‖ ≤ ‖U‖ / Real.sqrt α * ‖x‖ := by
  have hU_inv : U.IsInvertible := isInvertible_of_isStronglyMonotone U hU_self hU_strong
  let z : H := U.inverse (x : H)
  have hz_sq :
      α * ‖z‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    calc
      α * ‖z‖ ^ 2 ≤ ⟪z, U z⟫_ℝ := by
        simpa [pow_two, mul_assoc, real_inner_comm] using hU_strong.ineq z
      _ = ⟪U.inverse (x : H), (x : H)⟫_ℝ := by
        simp [z,
          ContinuousLinearMap.IsInvertible.self_apply_inverse hU_inv]
      _ = ‖x‖ ^ 2 := by
        symm
        exact norm_sq_eq_inner_inverse U hU_self hU_strong x
  have hx_le : ‖(x : H)‖ ≤ ‖U‖ * ‖z‖ := by
    calc
      ‖(x : H)‖ = ‖U z‖ := by
        simp [z, ContinuousLinearMap.IsInvertible.self_apply_inverse hU_inv]
      _ ≤ ‖U‖ * ‖z‖ := U.le_opNorm z
  have hz_le : Real.sqrt α * ‖z‖ ≤ ‖x‖ := by
    have hsq :
        (Real.sqrt α * ‖z‖) ^ 2 ≤ ‖x‖ ^ 2 := by
      have hsqrt : (Real.sqrt α) ^ 2 = α := by
        rw [Real.sq_sqrt (le_of_lt hU_strong.pos)]
      nlinarith [hz_sq, hsqrt]
    exact (sq_le_sq₀ (by positivity) (norm_nonneg x)).1 hsq
  have hsqrtα : Real.sqrt α ≠ 0 := by
    exact (Real.sqrt_ne_zero (le_of_lt hU_strong.pos)).2 hU_strong.pos.ne'
  calc
    ‖(x : H)‖ ≤ ‖U‖ * ‖z‖ := hx_le
    _ = (‖U‖ / Real.sqrt α) * (Real.sqrt α * ‖z‖) := by
      field_simp [hsqrtα]
    _ ≤ (‖U‖ / Real.sqrt α) * ‖x‖ := by
      gcongr

instance instCompleteSpace
    : CompleteSpace (Renormed U hU_self hU_strong) := by
  have hanti : AntilipschitzWith ⟨Real.sqrt ‖U.inverse‖, Real.sqrt_nonneg _⟩
      (fun x : Renormed U hU_self hU_strong ↦ (x : H)) := by
    rw [antilipschitzWith_iff_le_mul_dist]
    intro x y
    simpa [dist_eq_norm] using
      norm_le_sqrt_inverse_norm_mul_original_norm U hU_self hU_strong (x - y)
  have hlip : LipschitzWith ⟨‖U‖ / Real.sqrt α, by positivity⟩
      (fun x : Renormed U hU_self hU_strong ↦ (x : H)) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [dist_eq_norm] using
      original_norm_le_opNorm_div_sqrt_mul_norm U hU_self hU_strong (x - y)
  let e : Renormed U hU_self hU_strong ≃ᵤ H :=
    (equiv U hU_self hU_strong).toUniformEquivOfIsUniformInducing
      (hanti.isUniformInducing hlip.uniformContinuous)
  exact e.completeSpace_iff.2 inferInstance

end Renormed

end ContinuousLinearMap

namespace SetValuedOperator

open ContinuousLinearMap

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Reinterpret a set-valued operator on `H` as one on the renormed Hilbert space from
Proposition 20.24. This is a pure change of ambient inner product, not a new operator. -/
def renormed (A : SetValuedOperator H H) (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U)
    {α : ℝ} (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    SetValuedOperator
      (ContinuousLinearMap.Renormed U hU_self hU_strong)
      (ContinuousLinearMap.Renormed U hU_self hU_strong) :=
  fun x ↦ { u : ContinuousLinearMap.Renormed U hU_self hU_strong | (u : H) ∈ A (x : H) }

@[simp] theorem renormed_apply (A : SetValuedOperator H H) (U : H →L[ℝ] H)
    (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α)
    (x : ContinuousLinearMap.Renormed U hU_self hU_strong) :
    A.renormed U hU_self hU_strong x =
      { u : ContinuousLinearMap.Renormed U hU_self hU_strong | (u : H) ∈ A (x : H) } :=
  rfl

@[simp] theorem up_mem_renormed_iff (A : SetValuedOperator H H) (U : H →L[ℝ] H)
    (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α)
    (x u : H) :
    (ContinuousLinearMap.Renormed.up U hU_self hU_strong u :
        ContinuousLinearMap.Renormed U hU_self hU_strong) ∈
      A.renormed U hU_self hU_strong (ContinuousLinearMap.Renormed.up U hU_self hU_strong x) ↔
        u ∈ A x :=
  Iff.rfl

@[simp] theorem mem_comp_toSetValuedOperator_iff_inverse_mem_of_isStronglyMonotone
    (A : SetValuedOperator H H) (U : H →L[ℝ] H) {α : ℝ}
    (hU_self : IsSelfAdjoint U) (hU_strong : U.toLinearMap.IsStronglyMonotone α) (x u : H) :
    u ∈ (((U : H → H).toSetValuedOperator.comp A) : SetValuedOperator H H) x ↔
      U.inverse u ∈ A x := by
  have hU_inv : U.IsInvertible := ContinuousLinearMap.isInvertible_of_isStronglyMonotone
    U hU_self hU_strong
  rw [SetValuedOperator.mem_comp]
  constructor
  · rintro ⟨v, hv, huv⟩
    rw [Function.toSetValuedOperator_apply] at huv
    rw [Set.mem_singleton_iff] at huv
    subst huv
    simpa [ContinuousLinearMap.IsInvertible.inverse_apply_self hU_inv] using hv
  · intro hu
    refine ⟨U.inverse u, hu, ?_⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
    simp [ContinuousLinearMap.IsInvertible.self_apply_inverse hU_inv]

/-- The canonical owner `Maximal IsMonotone` on the renormed Hilbert space from
Proposition 20.24 unfolds to the source pairing formula
`⟪U⁻¹ (x - y), u - v⟫_ℝ`. -/
theorem isMaximallyMonotone_renormed_iff
    (A : SetValuedOperator H H) (U : H →L[ℝ] H) (hU_self : IsSelfAdjoint U) {α : ℝ}
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    Maximal IsMonotone (A.renormed U hU_self hU_strong) ↔
      ∀ x u : H, u ∈ A x ↔
        ∀ ⦃y v : H⦄, v ∈ A y →
          0 ≤ ⟪U.inverse (x - y), u - v⟫_ℝ := by
  rw [SetValuedOperator.maximal_iff_mem_iff]
  constructor
  · intro h x u
    constructor
    · intro hu y v hv
      have hxy' := (h (ContinuousLinearMap.Renormed.up U hU_self hU_strong x)
          (ContinuousLinearMap.Renormed.up U hU_self hU_strong u)).1
        (by simpa using hu) (by simpa using hv)
      change 0 ≤ ⟪U.inverse (x - y), u - v⟫_ℝ at hxy'
      exact hxy'
    · intro hu
      refine (h (ContinuousLinearMap.Renormed.up U hU_self hU_strong x)
          (ContinuousLinearMap.Renormed.up U hU_self hU_strong u)).2 ?_
      intro y v hv
      change 0 ≤ ⟪U.inverse (x - (y : H)), u - (v : H)⟫_ℝ
      exact hu (show (v : H) ∈ A (y : H) from hv)
  · intro h x u
    have hxu : (u : H) ∈ A (x : H) ↔
        ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ ⟪U.inverse ((x : H) - y), (u : H) - v⟫_ℝ := by
      exact h (x : H) (u : H)
    constructor
    · intro hu y v hv
      have huv := hxu.1 hu (show (v : H) ∈ A (y : H) from hv)
      change 0 ≤ ⟪U.inverse ((x : H) - (y : H)), (u : H) - (v : H)⟫_ℝ
      exact huv
    · intro hu
      refine hxu.2 ?_
      intro y v hv
      have hv' :
          (ContinuousLinearMap.Renormed.up U hU_self hU_strong v :
            ContinuousLinearMap.Renormed U hU_self hU_strong) ∈
            A.renormed U hU_self hU_strong
              (ContinuousLinearMap.Renormed.up U hU_self hU_strong y) := by
        simpa using hv
      have huv := hu hv'
      change 0 ≤ ⟪U.inverse ((x : H) - y), (u : H) - v⟫_ℝ at huv
      exact huv

/-- Proposition 20.24: if `A` is maximally monotone and `U` is self-adjoint and strongly
monotone, then the operator `U A = ((U : H → H).toSetValuedOperator.comp A)` is maximally monotone
on the renormed Hilbert space `ContinuousLinearMap.Renormed U hU_self hU_strong` whose inner
product is
`(x, y) ↦ ⟪U⁻¹ x, y⟫_ℝ`. The companion theorem
`isMaximallyMonotone_renormed_iff` rewrites this canonical maximal-monotonicity statement back
into the source pairing formula. -/
theorem comp_isMaximallyMonotone_of_isSelfAdjoint_of_isStronglyMonotone
    (A : SetValuedOperator H H) (U : H →L[ℝ] H) (α : ℝ)
    (hA : Maximal IsMonotone A) (hU_self : IsSelfAdjoint U)
    (hU_strong : U.toLinearMap.IsStronglyMonotone α) :
    Maximal IsMonotone
      (((U : H → H).toSetValuedOperator.comp A).renormed U hU_self hU_strong) := by
  have hU_inv : U.IsInvertible := ContinuousLinearMap.isInvertible_of_isStronglyMonotone
    U hU_self hU_strong
  rw [isMaximallyMonotone_renormed_iff _ U hU_self hU_strong]
  intro x u
  constructor
  · intro hu y v hv
    have hu' : U.inverse u ∈ A x := by
      rwa [mem_comp_toSetValuedOperator_iff_inverse_mem_of_isStronglyMonotone A U hU_self
        hU_strong] at hu
    have hv' : U.inverse v ∈ A y := by
      rwa [mem_comp_toSetValuedOperator_iff_inverse_mem_of_isStronglyMonotone A U hU_self
        hU_strong] at hv
    have hxy : 0 ≤ ⟪x - y, U.inverse u - U.inverse v⟫_ℝ :=
      (SetValuedOperator.Maximal.mem_iff hA x (U.inverse u)).1 hu' hv'
    have hbridge :=
      inner_inverse_sub_map_sub_eq_inner_sub_of_isSelfAdjoint_of_isStronglyMonotone
        U hU_self hU_strong (x - y) 0 (U.inverse u) (U.inverse v)
    have hxy' : 0 ≤ ⟪U.inverse (x - y), U (U.inverse u) - U (U.inverse v)⟫_ℝ := by
      rw [show ⟪U.inverse (x - y), U (U.inverse u) - U (U.inverse v)⟫_ℝ =
            ⟪x - y, U.inverse u - U.inverse v⟫_ℝ by simpa using hbridge]
      exact hxy
    simpa [ContinuousLinearMap.IsInvertible.self_apply_inverse hU_inv] using hxy'
  · intro hu
    have hu' : ∀ ⦃y v : H⦄, v ∈ A y → 0 ≤ ⟪x - y, U.inverse u - v⟫_ℝ := by
      intro y v hv
      have hvU : U v ∈ (((U : H → H).toSetValuedOperator.comp A) : SetValuedOperator H H) y := by
        rw [mem_comp_toSetValuedOperator_iff_inverse_mem_of_isStronglyMonotone A U hU_self
          hU_strong]
        simpa [ContinuousLinearMap.IsInvertible.inverse_apply_self hU_inv] using hv
      have huv : 0 ≤ ⟪U.inverse (x - y), u - U v⟫_ℝ := hu hvU
      have hbridge :=
        inner_inverse_sub_map_sub_eq_inner_sub_of_isSelfAdjoint_of_isStronglyMonotone
          U hU_self hU_strong (x - y) 0 (U.inverse u) v
      have huv' : 0 ≤ ⟪U.inverse (x - y), U (U.inverse u) - U v⟫_ℝ := by
        simpa [ContinuousLinearMap.IsInvertible.self_apply_inverse hU_inv] using huv
      rw [show ⟪U.inverse (x - y), U (U.inverse u) - U v⟫_ℝ =
          ⟪x - y, U.inverse u - v⟫_ℝ by simpa using hbridge] at huv'
      exact huv'
    have huA : U.inverse u ∈ A x :=
      (SetValuedOperator.Maximal.mem_iff hA x (U.inverse u)).2 hu'
    rw [mem_comp_toSetValuedOperator_iff_inverse_mem_of_isStronglyMonotone A U hU_self
      hU_strong]
    exact huA

end SetValuedOperator
