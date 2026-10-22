/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_13
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_50
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_22
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_40

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction
open Filter
open scoped InnerProductSpace SetValuedOperator Topology

universe u

noncomputable section

namespace HilbertBasis

local notation "L2" => lp (fun _ : ℕ ↦ ℝ) 2

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: use `0 ≤ β n ≤ 1` to bound `‖β n * x n‖^2` by `‖x n‖^2`, then apply the
-- summability characterization of `Memℓp` for `p = 2`.
private theorem diagonalForward_mem_lp (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : L2) :
    Memℓp (fun n ↦ (β n : ℝ) * x n) 2 := sorry

private def diagonalForward (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : L2) : L2 :=
  ⟨fun n ↦ (β n : ℝ) * x n, diagonalForward_mem_lp β hβ_le_one x⟩

private def diagonalForwardLinearMap (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) : L2 →ₗ[ℝ] L2 where
  toFun := diagonalForward β hβ_le_one
  map_add' x y := by
    ext n
    change (β n : ℝ) * (x n + y n) = (β n : ℝ) * x n + (β n : ℝ) * y n
    ring
  map_smul' a x := by
    ext n
    change (β n : ℝ) * (a * x n) = a * ((β n : ℝ) * x n)
    ring

private theorem norm_diagonalForward_le (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : L2) :
    ‖diagonalForward β hβ_le_one x‖ ≤ ‖x‖ := by
  refine lp.norm_le_of_forall_sum_le ?_ (norm_nonneg _) ?_
  · norm_num
  intro s
  calc
    ∑ i ∈ s, ‖diagonalForward β hβ_le_one x i‖ ^ (2 : ENNReal).toReal
      ≤ ∑ i ∈ s, ‖x i‖ ^ (2 : ENNReal).toReal := by
        refine Finset.sum_le_sum fun i _ ↦ ?_
        have hβ_nonneg : 0 ≤ (β i : ℝ) := (β i : NNReal).2
        have hβ_norm_le : ‖(β i : ℝ)‖ ≤ 1 := by
          simpa [Real.norm_of_nonneg hβ_nonneg] using
            (show (β i : ℝ) ≤ 1 from by exact_mod_cast hβ_le_one i)
        have hmul : ‖(β i : ℝ) * x i‖ ≤ ‖x i‖ := by
          calc
            ‖(β i : ℝ) * x i‖ = ‖(β i : ℝ)‖ * ‖x i‖ := by rw [norm_mul]
            _ ≤ 1 * ‖x i‖ := by gcongr
            _ = ‖x i‖ := by ring
        simpa [diagonalForward] using pow_le_pow_left₀ (norm_nonneg _) hmul 2
    _ ≤ ‖x‖ ^ (2 : ENNReal).toReal := lp.sum_rpow_le_norm_rpow (by norm_num) x s

private def diagonalForwardContinuousLinearMap (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) : L2 →L[ℝ] L2 :=
  (diagonalForwardLinearMap β hβ_le_one).mkContinuous 1 fun x ↦ by
    simpa using norm_diagonalForward_le β hβ_le_one x

/-- The diagonal operator `B` of Example 20.41, written as a bounded linear operator in
Hilbert-basis coordinates. -/
def diagonalForwardOperator (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) : H →L[ℝ] H :=
  let e := b.repr.toContinuousLinearEquiv
  let eMap : H →L[ℝ] L2 := e
  let eInvMap : L2 →L[ℝ] H := e.symm
  let D := diagonalForwardContinuousLinearMap β hβ_le_one
  (eInvMap.comp D).comp eMap

-- Proof sketch: in Hilbert-basis coordinates, `b n` is the `n`th unit vector, so the diagonal
-- multiplier scales that coordinate by `β n` and leaves all others zero.
/-- The weighted diagonal operator sends the basis vector `b n` to `β n • b n`. -/
theorem diagonalForwardOperator_apply_basis (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (n : ℕ) :
    diagonalForwardOperator b β hβ_le_one (b n) = (β n : ℝ) • b n := sorry

-- Proof sketch: transport `diagonalForwardOperator` to the diagonal multiplier on `ℓ²`, whose
-- matrix in the standard basis has real diagonal entries `β n`; such a diagonal operator equals
-- its adjoint, and conjugation by the Hilbert-basis equivalence preserves self-adjointness.
/-- The diagonal operator `B` of Example 20.41 is self-adjoint. -/
theorem diagonalForwardOperator_isSelfAdjoint [CompleteSpace H]
    (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    IsSelfAdjoint (diagonalForwardOperator b β hβ_le_one) := sorry

-- Proof sketch: in Hilbert-basis coordinates, `diagonalForwardOperator` is multiplication by the
-- nonnegative diagonal sequence `β`; hence `⟪B x, x⟫ = ∑ β n * ‖x n‖^2 ≥ 0`.
/-- The diagonal operator `B` is monotone. -/
theorem diagonalForwardOperator_isMonotone (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    (diagonalForwardOperator b β hβ_le_one).toLinearMap.IsMonotone := sorry

-- Proof sketch: Example 20.34 applies to bounded linear operators. Once `B` is identified as a
-- monotone bounded linear map, its associated singleton-valued set-valued operator is maximally
-- monotone.
/-- The diagonal operator `B` is maximally monotone as a singleton-valued set-valued operator. -/
theorem diagonalForwardOperator_isMaximallyMonotone (b : HilbertBasis ℕ ℝ H)
    (β : ℕ → NNRealˣ) (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    Maximal SetValuedOperator.IsMonotone
      (diagonalForwardOperator b β hβ_le_one).toSetValuedOperator := by
  simpa using
    ContinuousLinearMap.toSetValuedOperator_isMaximallyMonotone_of_isMonotone
      (diagonalForwardOperator b β hβ_le_one)
      (diagonalForwardOperator_isMonotone b β hβ_le_one)

/-- The dense proper linear subspace that forms the domain of the inverse diagonal operator. -/
def diagonalInverseDomain (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ) : Submodule ℝ H where
  carrier := {x | Memℓp (fun n ↦ (β n : ℝ)⁻¹ * b.repr x n) 2}
  zero_mem' := sorry
  add_mem' := by
    intro x y hx hy
    sorry
  smul_mem' := by
    intro a x hx
    sorry

/-- Membership in the inverse diagonal domain means square summability of the inverse-weighted
coordinate sequence. -/
@[simp] theorem mem_diagonalInverseDomain (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ) (x : H) :
    x ∈ diagonalInverseDomain b β ↔ Memℓp (fun n ↦ (β n : ℝ)⁻¹ * b.repr x n) 2 :=
  Iff.rfl

private def diagonalInverseCoordinates (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (x : diagonalInverseDomain b β) : L2 :=
  ⟨fun n ↦ (β n : ℝ)⁻¹ * b.repr x.1 n, x.2⟩

/-- The linear map `A` of Example 20.41 on its dense proper domain. -/
def diagonalInverseLinearMap (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ) :
    diagonalInverseDomain b β →ₗ[ℝ] H where
  toFun := fun x ↦ b.repr.symm (diagonalInverseCoordinates b β x)
  map_add' := by
    intro x y
    sorry
  map_smul' := by
    intro a x
    sorry

/-- The source-facing inverse operator `A = B⁻¹` of Example 20.41. -/
def diagonalInverseOperator (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) : SetValuedOperator H H :=
  ((diagonalForwardOperator b β hβ_le_one).toSetValuedOperator)⁻¹

-- Proof sketch: in Hilbert-basis coordinates, `B` maps `x` to the sequence `β n * x n`, so its
-- range consists exactly of those vectors whose inverse-weighted coordinates remain square
-- summable. That is precisely the defining condition for `diagonalInverseDomain`.
/-- The coordinate domain of the inverse diagonal operator is exactly the range of `B`. -/
theorem diagonalInverseDomain_eq_range_diagonalForwardOperator
    (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    diagonalInverseDomain b β = (diagonalForwardOperator b β hβ_le_one).toLinearMap.range := sorry

/-- Every value of the diagonal operator `B` lies in the domain of its inverse `A`. -/
theorem diagonalForwardOperator_mem_diagonalInverseDomain (b : HilbertBasis ℕ ℝ H)
    (β : ℕ → NNRealˣ) (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : H) :
    diagonalForwardOperator b β hβ_le_one x ∈ diagonalInverseDomain b β := by
  rw [diagonalInverseDomain_eq_range_diagonalForwardOperator b β hβ_le_one]
  exact LinearMap.mem_range_self _ x

-- Proof sketch: in coordinates, `A` multiplies by `β n⁻¹` on the range of `B`, so applying `A`
-- after `B` cancels the diagonal weights coordinatewise.
/-- On the range of `B`, the inverse diagonal operator `A` satisfies `A (B x) = x`. -/
theorem diagonalInverseLinearMap_apply_diagonalForwardOperator
    (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : H) :
    diagonalInverseLinearMap b β
      ⟨diagonalForwardOperator b β hβ_le_one x,
        diagonalForwardOperator_mem_diagonalInverseDomain b β hβ_le_one x⟩ = x := sorry

-- Proof sketch: if `x` already lies in `diagonalInverseDomain`, then its coordinates are
-- inverse-weighted square summable. Applying `A` multiplies by `β n⁻¹`, and applying `B` then
-- multiplies by `β n`, so the two maps cancel on the domain.
/-- On its natural domain, the inverse diagonal operator `A` satisfies `B (A x) = x`. -/
theorem diagonalForwardOperator_apply_diagonalInverseLinearMap
    (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) (x : diagonalInverseDomain b β) :
    diagonalForwardOperator b β hβ_le_one (diagonalInverseLinearMap b β x) = x := sorry

-- Proof sketch: the previous range and inverse laws identify the singleton-valued operator
-- induced by `A` with the graph-inverse of the singleton-valued operator induced by `B`.
/-- The source-facing inverse operator agrees with the coordinate presentation on its natural
domain. -/
theorem diagonalInverseOperator_eq_ofFunction
    (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    diagonalInverseOperator b β hβ_le_one =
      SetValuedOperator.ofFunction (diagonalInverseDomain b β : Set H)
        (diagonalInverseLinearMap b β) := sorry

/-- Example 20.41 states `dom A = ran B` for the inverse operator `A = B⁻¹`. -/
theorem diagonalInverseOperator_dom_eq_range_diagonalForwardOperator
    (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    (diagonalInverseOperator b β hβ_le_one).dom =
      (diagonalForwardOperator b β hβ_le_one).toLinearMap.range := by
  calc
    (diagonalInverseOperator b β hβ_le_one).dom =
        (SetValuedOperator.ofFunction (diagonalInverseDomain b β : Set H)
          (diagonalInverseLinearMap b β)).dom := by
          exact congrArg SetValuedOperator.dom (diagonalInverseOperator_eq_ofFunction b β hβ_le_one)
    _ = (diagonalInverseDomain b β : Set H) := by
      ext x
      constructor
      · intro hxdom
        rcases (SetValuedOperator.mem_dom_iff _ _).mp hxdom with ⟨y, hy⟩
        by_cases hx : x ∈ diagonalInverseDomain b β
        · exact hx
        · rw [SetValuedOperator.ofFunction_apply_of_not_mem _ _ hx] at hy
          exact False.elim (Set.notMem_empty y hy)
      · intro hx
        rw [SetValuedOperator.mem_dom_iff]
        refine ⟨diagonalInverseLinearMap b β ⟨x, hx⟩, ?_⟩
        rw [SetValuedOperator.ofFunction_apply_of_mem _ _ hx]
        simp
    _ = ((diagonalForwardOperator b β hβ_le_one).toLinearMap.range : Set H) := by
      exact congrArg (fun D : Submodule ℝ H ↦ (D : Set H))
        (diagonalInverseDomain_eq_range_diagonalForwardOperator b β hβ_le_one)

/-- The inverse diagonal operator is at most single-valued. -/
theorem diagonalInverseOperator_isAtMostSingleValued (b : HilbertBasis ℕ ℝ H)
    (β : ℕ → NNRealˣ) (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    SetValuedOperator.IsAtMostSingleValued (diagonalInverseOperator b β hβ_le_one) := by
  rw [diagonalInverseOperator_eq_ofFunction b β hβ_le_one]
  simpa using
    SetValuedOperator.isAtMostSingleValued_ofFunction
      (diagonalInverseDomain b β : Set H) (diagonalInverseLinearMap b β)

-- Proof sketch: the previous bridge theorem identifies the inverse diagonal operator with `B⁻¹`;
-- Proposition 20.22 then transports maximal monotonicity from the maximally monotone operator
-- induced by `B`.
/-- The inverse diagonal operator is maximally monotone under the weighted Hilbert-basis
hypotheses from Example 20.41. -/
theorem diagonalInverseOperator_isMaximallyMonotone (b : HilbertBasis ℕ ℝ H)
    (β : ℕ → NNRealˣ) (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1) :
    Maximal SetValuedOperator.IsMonotone (diagonalInverseOperator b β hβ_le_one) := by
  simpa [diagonalInverseOperator] using
    SetValuedOperator.Maximal.inverse
      (diagonalForwardOperator_isMaximallyMonotone b β hβ_le_one)

section

variable [CompleteSpace H]

-- Proof sketch: for `β n > 0`, the inverse-weighted coordinates of `β n • b n` are zero except
-- at the `n`th slot, where the value is `1`; this is the standard basis vector of `ℓ²`.
/-- Each weighted basis vector `β n • b n` belongs to the inverse diagonal domain. -/
theorem smul_basis_mem_diagonalInverseDomain (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (n : ℕ) :
    (β n : ℝ) • b n ∈ diagonalInverseDomain b β := sorry

-- Proof sketch: the vectors `β n • b n` all lie in the domain and span the same linear span as
-- the basis vectors `b n`, since each `β n` is nonzero. The closed span of the Hilbert basis is
-- all of `H`, so the domain is dense.
/-- The inverse diagonal domain is dense when all weights are strictly positive. -/
theorem diagonalInverseDomain_dense (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ) :
    Dense ((diagonalInverseDomain b β : Submodule ℝ H) : Set H) := sorry

-- Proof sketch: if the inverse diagonal domain were all of `H`, then every basis vector would lie
-- in it, so `‖(β n)⁻¹ • b n‖ = β n⁻¹` would stay bounded. This contradicts `β n → 0`, which forces
-- `β n⁻¹ → +∞` along the basis vectors.
/-- The inverse diagonal domain is proper when the positive weights decrease to `0`. -/
theorem diagonalInverseDomain_ne_univ (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_tendsto : Tendsto (fun n ↦ (β n : ℝ)) atTop (𝓝 0)) :
    ((diagonalInverseDomain b β : Submodule ℝ H) : Set H) ≠ Set.univ := sorry

-- Proof sketch: a dense linear subspace with nonempty interior is all of `H`; since the domain is
-- dense and proper, its interior must be empty.
/-- A dense proper linear subspace of the Hilbert space has empty interior, applied to the inverse
diagonal domain. -/
theorem diagonalInverseDomain_interior_eq_empty (b : HilbertBasis ℕ ℝ H)
    (β : ℕ → NNRealˣ)
    (hdense : Dense ((diagonalInverseDomain b β : Submodule ℝ H) : Set H))
    (hproper : ((diagonalInverseDomain b β : Submodule ℝ H) : Set H) ≠ Set.univ) :
    interior ((diagonalInverseDomain b β : Submodule ℝ H) : Set H) = ∅ := sorry

-- Proof sketch: in Hilbert-basis coordinates, both inner products expand as the same series
-- `∑ (β n : ℝ)⁻¹ * x n * y n`, so the inverse diagonal map is symmetric on its domain.
/-- In Hilbert-basis coordinates, the inverse diagonal map is symmetric on its natural domain. -/
theorem diagonalInverseLinearMap_isSymmetric
    (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (x y : diagonalInverseDomain b β) :
    ⟪(x : H), diagonalInverseLinearMap b β y⟫_ℝ =
      ⟪diagonalInverseLinearMap b β x, (y : H)⟫_ℝ := sorry

-- Proof sketch: in coordinates, `diagonalInverseLinearMap` multiplies by the positive sequence
-- `(β n : ℝ)⁻¹`, so the pointwise monotonicity inequality is a sum of nonnegative terms.
/-- The inverse diagonal map is monotone on its natural domain. -/
theorem diagonalInverseLinearMap_isMonotone
    (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ) :
    (SetValuedOperator.ofFunction (diagonalInverseDomain b β : Set H)
      (diagonalInverseLinearMap b β)).IsMonotone := sorry

-- Proof sketch: Proposition 20.40 (2) applies directly to the primitive data
-- `diagonalInverseDomain b β` and `diagonalInverseLinearMap b β`; the only input is that the
-- inverse diagonal map is symmetric and monotone, which uses positivity of `(β n : ℝ)⁻¹` but not
-- the forward-operator bound `β n ≤ 1`.
/-- The canonical potential attached to the inverse diagonal operator belongs to `Γ₀(H)`. -/
theorem diagonalInversePotential_mem_gammaZero (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    :
    SetValuedOperator.supremalPotential
        (diagonalInverseDomain b β) (diagonalInverseLinearMap b β) ∈ Γ₀(H) := sorry

-- Proof sketch: apply Proposition 20.40 (3) to the subspace `diagonalInverseDomain b β` and the
-- symmetric linear map `diagonalInverseLinearMap b β`; the needed maximal monotonicity of `A`
-- comes from `diagonalInverseOperator_isMaximallyMonotone`, which identifies its graph with the
-- subdifferential of the associated supremal potential.
/-- The subdifferential of the canonical potential is exactly the inverse diagonal operator. -/
theorem subdifferential_diagonalInversePotential_eq
    (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hβ_le_one : ∀ n, (β n : NNReal) ≤ 1)
    :
    ∂ (SetValuedOperator.supremalPotential
      (diagonalInverseDomain b β) (diagonalInverseLinearMap b β)) =
        diagonalInverseOperator b β hβ_le_one := sorry

/-- For the inverse diagonal operator of Example 20.41, the canonical potential is finite exactly
on the inverse-domain subspace. -/
theorem effectiveDomain_diagonalInversePotential_eq
    (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ) :
    effectiveDomain
        (SetValuedOperator.supremalPotential
          (diagonalInverseDomain b β) (diagonalInverseLinearMap b β)) =
      (diagonalInverseDomain b β : Set H) := sorry

-- Proof sketch: for a linear subspace `D`, the translated set `D - {x}` is again `D` at every
-- point `x ∈ D`, so `x ∈ core D` would force `cone D = univ`. For a proper submodule this is
-- impossible, because `cone D = D`.
/-- The inverse diagonal domain has empty algebraic core as soon as it is a proper subspace. -/
theorem diagonalInverseDomain_core_eq_empty (b : HilbertBasis ℕ ℝ H)
    (β : ℕ → NNRealˣ)
    (hproper : ((diagonalInverseDomain b β : Submodule ℝ H) : Set H) ≠ Set.univ) :
    Set.core ((diagonalInverseDomain b β : Submodule ℝ H) : Set H) = ∅ := sorry

-- Proof sketch: if the source `]-∞,+∞]`-valued potential were Gâteaux differentiable at some `x`,
-- then the canonical Chapter 17 owner theorem would place `x` in
-- `core (effectiveDomain f)`. For this diagonal inverse example, the effective domain is exactly
-- `diagonalInverseDomain b β`, while the empty-interior hypothesis forces that submodule to be
-- proper, hence to have empty algebraic core. This contradiction rules out Gâteaux
-- differentiability at every point.
/-- The canonical potential of the inverse diagonal map is nowhere Gâteaux differentiable
in the source Chapter 17 `]-∞,+∞]`-valued sense once the inverse diagonal domain has empty
interior. -/
theorem diagonalInversePotential_nowhere_gateauxDifferentiable
    (b : HilbertBasis ℕ ℝ H) (β : ℕ → NNRealˣ)
    (hinterior : interior ((diagonalInverseDomain b β : Submodule ℝ H) : Set H) = ∅)
    (x : H) :
    ¬ GateauxDifferentiableAt
      (SetValuedOperator.supremalPotential
        (diagonalInverseDomain b β) (diagonalInverseLinearMap b β)) x := sorry

end

end HilbertBasis
