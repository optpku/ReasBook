/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Tensor4

open scoped BigOperators

noncomputable section

section

variable {n p : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this file:
-- * `Chapter06.Tensor4`: source-facing fourth-order tensor vocabulary now lives in the reusable
--   chapter owner file as coordinate tensors with the intended Frobenius/Hilbert norm.
-- * `Chapter06.Definition_6_3_1`: `ThirdOrderTensor` is the chapter's matching source-facing
--   tensor owner pattern, so the quartic owner should stay at the same coordinate level.
-- * `Mathlib.Analysis.InnerProductSpace.PiL2`: `PiLp 2` / `WithLp.toLp 2` is the core/canonical
--   Hilbert-space owner for finite coordinate arrays, which induces the tensor Frobenius norm.
-- * `Tensor4.rankOne`, `Tensor4.apply`, `Tensor4.frobeniusNorm`, and `Tensor4.IsSymmetric` are
--   derived API on that owner, so this theorem file only keeps the quartic interpolation data.

open scoped Tensor4

/-- The quartic Gram matrix with entries `(s i)ᵀ (s j)` raised to the fourth power. -/
def quarticGramMatrix (s : Fin p → Point) : Matrix (Fin p) (Fin p) ℝ :=
  fun i j ↦ (inner ℝ (s i) (s j)) ^ 4

/-- The explicit coefficient vector `γ = M⁻¹ β` attached to the quartic Gram matrix `M`. -/
def quarticTensorGramInverseCoefficients (s : Fin p → Point) (β : EuclideanSpace ℝ (Fin p)) :
    EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 <| (quarticGramMatrix s)⁻¹.mulVec β

/-- The explicit tensor `∑ k, γ[k] (s_k ⊗ s_k ⊗ s_k ⊗ s_k)` from Theorem 6.3.4. -/
def quarticTensorCombination (s : Fin p → Point) (γ : EuclideanSpace ℝ (Fin p)) :
    Tensor4 n :=
  ∑ k, γ k • ⟪s k, s k, s k, s k⟫₄

/-- The interpolation condition `V[s_k, s_k, s_k, s_k] = β[k]` on the data sites `s`. -/
def quarticTensorInterpolates
    (s : Fin p → Point) (β : EuclideanSpace ℝ (Fin p)) (V : Tensor4 n) : Prop :=
  ∀ k, V.apply (s k) (s k) (s k) (s k) = β k

/-- The explicit tensor `Vc = ∑ k, γ[k] (s_k ⊗ s_k ⊗ s_k ⊗ s_k)` with
`γ = (quarticGramMatrix s)⁻¹ β`. This is the source-facing tensor `V_c` from
Theorem 6.3.4. -/
def quarticTensorGramInverseCombination (s : Fin p → Point) (β : EuclideanSpace ℝ (Fin p)) :
    Tensor4 n :=
  quarticTensorCombination s (quarticTensorGramInverseCoefficients s β)

/-- The feasible set of symmetric fourth-order tensors interpolating the data `β` on the sites
`s`. -/
def quarticTensorFeasibleSet
    (s : Fin p → Point) (β : EuclideanSpace ℝ (Fin p)) : Set (Tensor4 n) :=
  {V | V.IsSymmetric ∧ quarticTensorInterpolates s β V}

/-- Helper for Chapter06 Theorem 6.3.4: the nested `PiLp` owner for flattening a fourth-order
coordinate tensor into a Hilbert-space vector. -/
abbrev QuarticTensorFlattened (n : ℕ) := Tensor4.Flattened n

/-- Helper for Chapter06 Theorem 6.3.4: flatten a fourth-order tensor into the nested `PiLp`
owner that carries the coordinatewise Hilbert-space structure used by the source proof. -/
def quarticTensorFlatten (V : Tensor4 n) : QuarticTensorFlattened n := Tensor4.flatten V

/-- Helper for Chapter06 Theorem 6.3.4: the stated Frobenius norm is the norm of the canonical
flattened Hilbert-space vector used in the source least-norm proof. -/
lemma quarticTensorFrobeniusNorm_eq_flatten_norm
    (V : Tensor4 n) :
    V.frobeniusNorm = ‖quarticTensorFlatten V‖ := by
  -- The upstream `Tensor4` API now owns the canonical flattening/norm bridge, so the theorem file
  -- only needs this local alias.
  simpa [quarticTensorFlatten] using Tensor4.frobeniusNorm_eq_flatten_norm V

/-- Helper for Chapter06 Theorem 6.3.4: the canonical flattening does not change tensor
coordinates; it only repackages them into the nested `PiLp` owner. -/
@[simp] lemma quarticTensorFlatten_apply
    (V : Tensor4 n) (i j k l : Fin n) :
    ((((quarticTensorFlatten V).ofLp i).ofLp j).ofLp k).ofLp l = V i j k l := by
  simpa [quarticTensorFlatten] using Tensor4.flatten_apply V i j k l

/-- Helper for Chapter06 Theorem 6.3.4: flattening is coordinatewise, so it preserves tensor
subtraction exactly. -/
lemma quarticTensorFlatten_sub
    (V W : Tensor4 n) :
    quarticTensorFlatten (V - W) = quarticTensorFlatten V - quarticTensorFlatten W := by
  -- Extensionality reduces the subtraction identity to the coordinate arrays.
  ext i j k l
  simp [quarticTensorFlatten, Tensor4.flatten]

/-- Helper for Chapter06 Theorem 6.3.4: the flattened inner product with a rank-one tensor agrees
with the source contraction `V[s,s,s,s]`. -/
lemma quarticTensorFlatten_rankOne_inner
    (u v w x : Point) (V : Tensor4 n) :
    inner ℝ (quarticTensorFlatten (⟪u, v, w, x⟫₄ : Tensor4 n)) (quarticTensorFlatten V) =
      V.apply u v w x := by
  -- Expand the nested `PiLp` inner product and identify it with the tensor contraction.
  rw [quarticTensorFlatten, quarticTensorFlatten, Tensor4.apply_eq, PiLp.inner_apply]
  simp_rw [Tensor4.flatten, PiLp.inner_apply]
  simp [Tensor4.rankOne_apply, mul_assoc]

/-- Helper for Chapter06 Theorem 6.3.4: the quartic Gram matrix is the ordinary Gram matrix of
flattened quartic rank-one tensors. -/
lemma quarticGramMatrix_eq_gram
    (s : Fin p → Point) :
    quarticGramMatrix s =
      Matrix.gram ℝ (fun k : Fin p ↦
        quarticTensorFlatten (⟪s k, s k, s k, s k⟫₄ : Tensor4 n)) := by
  ext i j
  -- Route correction: rewrite the Gram entry through the flattened rank-one inner product, so the
  -- quartic power comes from `Tensor4.apply_rankOne` instead of a brittle coordinate expansion.
  rw [quarticGramMatrix, Matrix.gram_apply, quarticTensorFlatten_rankOne_inner]
  symm
  simpa [pow_succ, pow_two, mul_assoc, real_inner_comm] using
    Tensor4.apply_rankOne (s j) (s j) (s j) (s j) (s i) (s i) (s i) (s i)

/-- Helper for Chapter06 Theorem 6.3.4: the flattened quartic rank-one family is linearly
independent whenever the sampling sites are linearly independent. -/
lemma linearIndependent_flattened_quartic_rankOne_family
    (s : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    LinearIndependent ℝ
      (fun k : Fin p ↦ quarticTensorFlatten (⟪s k, s k, s k, s k⟫₄ : Tensor4 n)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro x hx j
  by_contra hxj
  -- Fixing three coordinates reduces a vanishing quartic combination to a vanishing linear
  -- combination of the original vectors `s i`.
  have hcomb (a b c : Fin n) : ∑ i, (x i * s i a * s i b * s i c) • s i = 0 := by
    ext d
    have h := congrArg (fun T => T a b c d) hx
    simpa [quarticTensorFlatten, Tensor4.flatten, Tensor4.rankOne_apply, Pi.smul_apply,
      mul_assoc, mul_left_comm, mul_comm] using h
  have hcoeff : ∀ a b c, ∀ i, x i * s i a * s i b * s i c = 0 := by
    intro a b c
    exact (Fintype.linearIndependent_iff.mp hlin) _ (hcomb a b c)
  have hs_nonzero : ∃ a, s j a ≠ 0 := by
    by_contra hs
    apply hlin.ne_zero j
    ext a
    by_contra hza
    exact hs ⟨a, hza⟩
  rcases hs_nonzero with ⟨a, ha⟩
  have hxmul : x j * (s j a) ^ 3 = 0 := by
    simpa [pow_succ, pow_two, mul_assoc] using hcoeff a a a j
  exact hxj ((mul_eq_zero.mp hxmul).resolve_right (pow_ne_zero 3 ha))

/-- Helper for Chapter06 Theorem 6.3.4: the quartic Gram matrix is positive definite under the
source hypothesis that the sampling sites are linearly independent. -/
lemma quarticGramMatrix_posDef
    (s : Fin p → Point) (hlin : LinearIndependent ℝ s) :
    (quarticGramMatrix s).PosDef := by
  -- After identifying the matrix as a Gram matrix, the standard positive-definiteness criterion
  -- finishes the source full-row-rank step.
  rw [quarticGramMatrix_eq_gram]
  exact Matrix.posDef_gram_of_linearIndependent
    (linearIndependent_flattened_quartic_rankOne_family s hlin)

/-- Helper for Chapter06 Theorem 6.3.4: the explicit quartic combination is symmetric because each
rank-one summand uses the same vector in all four slots. -/
lemma quarticTensorCombination_isSymmetric
    (s : Fin p → Point) (γ : EuclideanSpace ℝ (Fin p)) :
    (quarticTensorCombination s γ).IsSymmetric := by
  -- Check symmetry on adjacent transpositions and reduce each component equality to commutativity
  -- of scalar multiplication.
  rw [Tensor4.isSymmetric_iff_adjacent_transpositions]
  refine ⟨?_, ?_, ?_⟩
  · intro i j k l
    simp [quarticTensorCombination, Tensor4.rankOne_apply, mul_assoc, mul_comm]
  · intro i j k l
    simp [quarticTensorCombination, Tensor4.rankOne_apply, mul_assoc, mul_left_comm, mul_comm]
  · intro i j k l
    simp [quarticTensorCombination, Tensor4.rankOne_apply, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Chapter06 Theorem 6.3.4: flattening the explicit quartic combination turns it into
that same coefficient-weighted sum in the Hilbert-space owner. -/
lemma quarticTensorFlatten_combination_eq_sum
    (s : Fin p → Point) (γ : EuclideanSpace ℝ (Fin p)) :
    quarticTensorFlatten (quarticTensorCombination s γ) =
      ∑ k, γ k • quarticTensorFlatten (⟪s k, s k, s k, s k⟫₄ : Tensor4 n) := by
  -- Extensionality on the nested `PiLp` coordinates reduces flattening to the tensor definition.
  ext i j k l
  simp [quarticTensorFlatten, quarticTensorCombination, Pi.smul_apply]

/-- Helper for Chapter06 Theorem 6.3.4: the inner product of the flattened quartic combination
with a residual tensor is the coefficient-weighted sum of the residual sample values. -/
lemma quarticTensorFlatten_combination_inner_residual_eq_sum
    (s : Fin p → Point) (γ : EuclideanSpace ℝ (Fin p)) (R : Tensor4 n) :
    inner ℝ (quarticTensorFlatten (quarticTensorCombination s γ)) (quarticTensorFlatten R) =
      ∑ k, γ k * R.apply (s k) (s k) (s k) (s k) := by
  -- Rewrite the flattened combination as a sum and evaluate each rank-one summand by the source
  -- contraction identity.
  rw [quarticTensorFlatten_combination_eq_sum, sum_inner]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [real_inner_smul_left, quarticTensorFlatten_rankOne_inner]

/-- Helper for Chapter06 Theorem 6.3.4: evaluating the explicit quartic combination at a data site
recovers the corresponding quartic Gram-matrix row applied to the coefficient vector. -/
lemma quarticTensorCombination_apply_self
    (s : Fin p → Point) (γ : EuclideanSpace ℝ (Fin p)) (i : Fin p) :
    (quarticTensorCombination s γ).apply (s i) (s i) (s i) (s i) =
      ((quarticGramMatrix s).mulVec γ) i := by
  -- Move to the flattened Hilbert-space owner, expand the coefficient-weighted sum there, and
  -- evaluate each rank-one inner product by the quartic Gram entry formula.
  calc
    (quarticTensorCombination s γ).apply (s i) (s i) (s i) (s i) =
        inner ℝ (quarticTensorFlatten (⟪s i, s i, s i, s i⟫₄ : Tensor4 n))
          (quarticTensorFlatten (quarticTensorCombination s γ)) := by
      symm
      exact quarticTensorFlatten_rankOne_inner (s i) (s i) (s i) (s i)
        (quarticTensorCombination s γ)
    _ = inner ℝ (quarticTensorFlatten (⟪s i, s i, s i, s i⟫₄ : Tensor4 n))
          (∑ k, γ k • quarticTensorFlatten (⟪s k, s k, s k, s k⟫₄ : Tensor4 n)) := by
      rw [quarticTensorFlatten_combination_eq_sum]
    _ = ∑ k, γ k * inner ℝ (quarticTensorFlatten (⟪s i, s i, s i, s i⟫₄ : Tensor4 n))
          (quarticTensorFlatten (⟪s k, s k, s k, s k⟫₄ : Tensor4 n)) := by
      rw [inner_sum]
      simp [real_inner_smul_right]
    _ = ((quarticGramMatrix s).mulVec γ) i := by
      rw [Matrix.mulVec, dotProduct]
      simp [quarticGramMatrix, quarticTensorFlatten_rankOne_inner, Tensor4.apply_rankOne,
        real_inner_comm, pow_succ, mul_comm]

/-- Expanding `quarticTensorGramInverseCombination s β` gives the source formula
`∑ k, γ[k] (s_k ⊗ s_k ⊗ s_k ⊗ s_k)` with `γ = M⁻¹ β` and `M = quarticGramMatrix s`. -/
theorem quarticTensorGramInverseCombination_eq_sum
    (s : Fin p → Point) (β : EuclideanSpace ℝ (Fin p)) :
    quarticTensorGramInverseCombination s β =
      ∑ k, (quarticTensorGramInverseCoefficients s β) k • ⟪s k, s k, s k, s k⟫₄ := by
  -- This is just the defining expansion of `quarticTensorGramInverseCombination`.
  rfl

/-- Under `LinearIndependent ℝ s`, the explicit candidate
`quarticTensorGramInverseCombination s β` lies in the quartic interpolation feasible set. -/
theorem quarticTensorGramInverseCombination_mem_feasibleSet
    (s : Fin p → Point) (β : EuclideanSpace ℝ (Fin p))
    (hlin : LinearIndependent ℝ s) :
    quarticTensorGramInverseCombination s β ∈ quarticTensorFeasibleSet s β := by
  refine ⟨quarticTensorCombination_isSymmetric s _, ?_⟩
  -- The interpolation equations are exactly the linear system `quarticGramMatrix s * γ = β`.
  intro i
  have hMatrixUnit : IsUnit (quarticGramMatrix s) := (quarticGramMatrix_posDef s hlin).isUnit
  have hdetUnit : IsUnit (quarticGramMatrix s).det :=
    (Matrix.isUnit_iff_isUnit_det (quarticGramMatrix s)).mp hMatrixUnit
  calc
    (quarticTensorGramInverseCombination s β).apply (s i) (s i) (s i) (s i)
        = ((quarticGramMatrix s).mulVec (quarticTensorGramInverseCoefficients s β)) i :=
      quarticTensorCombination_apply_self s _ i
    _ = (((quarticGramMatrix s) * (quarticGramMatrix s)⁻¹).mulVec β) i := by
      simp [quarticTensorGramInverseCoefficients, Matrix.mulVec_mulVec]
    _ = β i := by
      rw [Matrix.mul_nonsing_inv _ hdetUnit, Matrix.one_mulVec]

/-- Helper for Chapter06 Theorem 6.3.4: any feasible residual is orthogonal in the flattened
Hilbert-space owner to the explicit Gram-inverse quartic combination. -/
lemma quarticTensorGramInverseCombination_flatten_orthogonal_residual
    (s : Fin p → Point) (β : EuclideanSpace ℝ (Fin p))
    (hlin : LinearIndependent ℝ s) {V : Tensor4 n}
    (hV : V ∈ quarticTensorFeasibleSet s β) :
    inner ℝ (quarticTensorFlatten (quarticTensorGramInverseCombination s β))
      (quarticTensorFlatten (V - quarticTensorGramInverseCombination s β)) = 0 := by
  rcases hV with ⟨_, hVInterpolates⟩
  rcases quarticTensorGramInverseCombination_mem_feasibleSet s β hlin with ⟨_, hVcInterpolates⟩
  -- Rewrite the inner product as a coefficient-weighted sum of residual sample values.
  rw [quarticTensorGramInverseCombination, quarticTensorFlatten_combination_inner_residual_eq_sum]
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  -- Both feasible tensors satisfy the same interpolation equations, so the residual vanishes on
  -- every sampled quartic direction.
  have hResidual :
      (V - quarticTensorGramInverseCombination s β).apply (s k) (s k) (s k) (s k) = 0 := by
    calc
      (V - quarticTensorGramInverseCombination s β).apply (s k) (s k) (s k) (s k)
          = V.apply (s k) (s k) (s k) (s k) -
              (quarticTensorGramInverseCombination s β).apply (s k) (s k) (s k) (s k) := by
        simp [Tensor4.apply_eq, sub_mul, Finset.sum_sub_distrib]
      _ = β k - β k := by rw [hVInterpolates k, hVcInterpolates k]
      _ = 0 := sub_self _
  have hResidualCombination :
      (V - quarticTensorCombination s (quarticTensorGramInverseCoefficients s β)).apply
          (s k) (s k) (s k) (s k) = 0 := by
    simpa [quarticTensorGramInverseCombination] using hResidual
  rw [hResidualCombination]
  ring

/-- Under `LinearIndependent ℝ s`, the explicit candidate
`quarticTensorGramInverseCombination s β` is a least-Frobenius-norm point of the quartic
interpolation feasible set. -/
theorem quarticTensorGramInverseCombination_isMinOn_feasibleSet
    (s : Fin p → Point) (β : EuclideanSpace ℝ (Fin p))
    (hlin : LinearIndependent ℝ s) :
    IsMinOn (fun V ↦ V.frobeniusNorm) (quarticTensorFeasibleSet s β)
      (quarticTensorGramInverseCombination s β) := by
  rw [isMinOn_iff]
  intro V hV
  let Vc := quarticTensorGramInverseCombination s β
  let R := V - Vc
  have horth :
      inner ℝ (quarticTensorFlatten Vc) (quarticTensorFlatten R) = 0 := by
    -- The source residual is orthogonal to the explicit Gram-inverse solution in the flattened
    -- Hilbert-space owner.
    simpa [Vc, R] using
      quarticTensorGramInverseCombination_flatten_orthogonal_residual s β hlin hV
  have hflatten_add :
      quarticTensorFlatten V = quarticTensorFlatten Vc + quarticTensorFlatten R := by
    -- Route correction: the source proof works with `V = Vc + R`, where `R = V - Vc`, so we
    -- rewrite flattening through subtraction before invoking Pythagoras.
    have hflatten_sub' :
        quarticTensorFlatten R = quarticTensorFlatten V - quarticTensorFlatten Vc := by
      simpa [R] using quarticTensorFlatten_sub V Vc
    calc
      quarticTensorFlatten V = quarticTensorFlatten Vc + (quarticTensorFlatten V - quarticTensorFlatten Vc) := by
        simp [sub_eq_add_neg, add_left_comm]
      _ = quarticTensorFlatten Vc + quarticTensorFlatten R := by
        rw [hflatten_sub'.symm]
  have hpyth :
      ‖quarticTensorFlatten Vc + quarticTensorFlatten R‖ *
          ‖quarticTensorFlatten Vc + quarticTensorFlatten R‖ =
        ‖quarticTensorFlatten Vc‖ * ‖quarticTensorFlatten Vc‖ +
          ‖quarticTensorFlatten R‖ * ‖quarticTensorFlatten R‖ := by
    -- Orthogonality gives the Hilbert-space Pythagoras identity in the flattened owner.
    exact norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hmul_le :
      ‖quarticTensorFlatten Vc‖ * ‖quarticTensorFlatten Vc‖ ≤
        ‖quarticTensorFlatten V‖ * ‖quarticTensorFlatten V‖ := by
    -- The residual norm contributes a nonnegative term, so the candidate norm square is minimal.
    calc
      ‖quarticTensorFlatten Vc‖ * ‖quarticTensorFlatten Vc‖ ≤
          ‖quarticTensorFlatten Vc‖ * ‖quarticTensorFlatten Vc‖ +
            ‖quarticTensorFlatten R‖ * ‖quarticTensorFlatten R‖ := by
        exact le_add_of_nonneg_right (mul_self_nonneg ‖quarticTensorFlatten R‖)
      _ = ‖quarticTensorFlatten Vc + quarticTensorFlatten R‖ *
            ‖quarticTensorFlatten Vc + quarticTensorFlatten R‖ := by
        symm
        exact hpyth
      _ = ‖quarticTensorFlatten V‖ * ‖quarticTensorFlatten V‖ := by
        rw [← hflatten_add]
  have hnorm_flat :
      ‖quarticTensorFlatten Vc‖ ≤ ‖quarticTensorFlatten V‖ := by
    -- Since both norms are nonnegative reals, the squared inequality descends to the norms.
    have habs :
        |‖quarticTensorFlatten Vc‖| ≤ |‖quarticTensorFlatten V‖| :=
      (abs_le_iff_mul_self_le).2 hmul_le
    simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using habs
  -- Rewrite the source Hilbert-space norm inequality back to the stated Frobenius norm objective.
  calc
    Vc.frobeniusNorm = ‖quarticTensorFlatten Vc‖ := quarticTensorFrobeniusNorm_eq_flatten_norm Vc
    _ ≤ ‖quarticTensorFlatten V‖ := hnorm_flat
    _ = V.frobeniusNorm := by
      symm
      exact quarticTensorFrobeniusNorm_eq_flatten_norm V

/-- Chapter06 Theorem 6.3.4: let `p ≤ n`, let `s : Fin p → ℝⁿ` be linearly independent, and let
`β : ℝᵖ`. If `M[i,j] = ((s i)ᵀ (s j))^4` and `γ = M⁻¹ β`, then the solution of `(6.3.41)` is
`V_c = ∑ k, γ[k] (s k ⊗ s k ⊗ s k ⊗ s k)`. As in Theorem 6.3.3, the source side condition
`p ≤ n` is redundant once `s` is linearly independent, so the Lean statement packages the
solution claim as feasibility plus least-Frobenius-norm optimality for the explicit tensor
`quarticTensorGramInverseCombination s β`. -/
theorem quarticTensorLeastNormSolution_isMinOn
    (s : Fin p → Point) (β : EuclideanSpace ℝ (Fin p))
    (hlin : LinearIndependent ℝ s) :
    let Vc := quarticTensorGramInverseCombination s β
    Vc ∈ quarticTensorFeasibleSet s β ∧
      IsMinOn (fun V ↦ V.frobeniusNorm) (quarticTensorFeasibleSet s β) Vc := by
  refine ⟨quarticTensorGramInverseCombination_mem_feasibleSet s β hlin, ?_⟩
  exact quarticTensorGramInverseCombination_isMinOn_feasibleSet s β hlin

end
