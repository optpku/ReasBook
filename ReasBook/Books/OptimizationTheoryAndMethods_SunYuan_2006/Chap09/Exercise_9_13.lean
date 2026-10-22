/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.Rank
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_3_2

open Matrix

noncomputable section

section

variable {𝕜 : Type*} [Field 𝕜] {m n : ℕ}

local notation "HessianMatrix" => Matrix (Fin n) (Fin n) 𝕜
local notation "ConstraintMatrix" => Matrix (Fin m) (Fin n) 𝕜
local notation "ReducedBasisMatrix" => Matrix (Fin n) (Fin (n - m)) 𝕜
local notation "PrimalPoint" => Fin n → 𝕜
local notation "DualPoint" => Fin m → 𝕜
local notation "ReducedPoint" => Fin (n - m) → 𝕜

-- Domain-style sampling for this file:
-- * primary domain: KKT block-matrix nonsingularity via reduced-null-space compression.
-- * core/canonical owners inspected: the Chapter 9 owners `kktMatrix` and
--   `IsReducedNullMatrix`, together with mathlib's block-matrix constructor
--   `Matrix.fromBlocks` and matrix rank owner `Matrix.rank`.
-- * source/core/bridge triage: this exercise is source-facing, while `IsReducedNullMatrix`
--   is the core owner for the null-space data and the displayed block matrix is the direct
--   `kktMatrix B (-Aᵀ)` specialization.
-- * primitive data vs derived API: the primitive data here are the block matrix and the
--   reduced-null-space owner hypothesis; the nonsingularity equivalence is derived API.

/-- Helper for Chapter09 Exercise 9.13: a rectangular matrix with full column rank has injective
`mulVec`. -/
lemma injective_mulVec_of_rank_eq_width
    {r c : ℕ}
    (M : Matrix (Fin r) (Fin c) 𝕜)
    (hM : Matrix.rank M = c) :
    Function.Injective M.mulVec := by
  -- Full column rank is exactly linear independence of the columns, which is the stable `mulVec`
  -- injectivity API for rectangular matrices.
  rw [Matrix.mulVec_injective_iff]
  rw [linearIndependent_iff_card_eq_finrank_span]
  simpa [Matrix.rank_eq_finrank_span_cols, Set.finrank] using hM.symm

/-- Helper for Chapter09 Exercise 9.13: the reduced-null-space hypothesis for `Aᵀ` rewrites to
the matrix identity `A * Z = 0`. -/
lemma constraint_mul_reducedBasis_eq_zero
    (A : ConstraintMatrix)
    (Z : ReducedBasisMatrix)
    (hZ : IsReducedNullMatrix Aᵀ Z) :
    A * Z = 0 := by
  -- Test each column of `A * Z` on the corresponding basis vector so that `hZ.mem_ker` applies
  -- directly.
  ext i j
  have hColumn : (A * Z).col j = 0 := by
    calc
      (A * Z).col j = (A * Z).mulVec (Pi.single j 1) := by
        symm
        exact Matrix.mulVec_single_one (A * Z) j
      _ = A.mulVec (Z.mulVec (Pi.single j 1)) := by
        symm
        exact Matrix.mulVec_mulVec (Pi.single j 1) A Z
      _ = 0 := by
        simpa [Matrix.mulVec_single_one] using hZ.mem_ker (Pi.single j 1)
  simpa using congrArg (fun c => c i) hColumn

/-- Helper for Chapter09 Exercise 9.13: the reduced-null-space basis `Z` parametrizes exactly the
kernel of the constraint map `A`. -/
lemma reducedBasis_range_eq_ker_constraint
    (A : ConstraintMatrix)
    (Z : ReducedBasisMatrix)
    (hZ : IsReducedNullMatrix Aᵀ Z) :
    LinearMap.range (Matrix.toLin' Z) = LinearMap.ker (Matrix.toLin' A) := by
  -- This is the source statement that `Z` spans `ker A`, expressed in the linear-map owners used
  -- by the matrix-rank API.
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    rw [LinearMap.mem_ker]
    simpa [Matrix.toLin'_apply] using hZ.mem_ker u
  · intro hp
    rw [LinearMap.mem_ker] at hp
    obtain ⟨u, hu⟩ := hZ.eq_mulVec p (by simpa [Matrix.toLin'_apply] using hp)
    exact ⟨u, hu⟩

/-- Helper for Chapter09 Exercise 9.13: full row rank of `A` and the reduced-null-space property
force `Z.mulVec` to be injective. -/
lemma reducedBasis_mulVec_injective
    (A : ConstraintMatrix)
    (Z : ReducedBasisMatrix)
    (hA : Matrix.rank A = m)
    (hZ : IsReducedNullMatrix Aᵀ Z) :
    Function.Injective Z.mulVec := by
  have hRangeEq : LinearMap.range (Matrix.toLin' Z) = LinearMap.ker (Matrix.toLin' A) :=
    reducedBasis_range_eq_ker_constraint A Z hZ
  have hRangeA : Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' A)) = m := by
    rw [Matrix.range_toLin', ← Matrix.rank_eq_finrank_span_cols]
    exact hA
  have hdim : Module.finrank 𝕜 PrimalPoint = n := by
    simpa using Module.finrank_fintype_fun_eq_card (R := 𝕜) (η := Fin n)
  have hKerA_sum : Module.finrank 𝕜 (LinearMap.ker (Matrix.toLin' A)) + m = n := by
    simpa [add_comm, hRangeA, hdim] using
      LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' A)
  have hKerA : Module.finrank 𝕜 (LinearMap.ker (Matrix.toLin' A)) = n - m :=
    Nat.eq_sub_of_add_eq hKerA_sum
  have hRangeZ : Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' Z)) = n - m := by
    rw [hRangeEq]
    exact hKerA
  have hRankZ : Matrix.rank Z = n - m := by
    rw [Matrix.range_toLin'] at hRangeZ
    rw [Matrix.rank_eq_finrank_span_cols]
    exact hRangeZ
  -- Once the range count matches the number of reduced coordinates, the rectangular injectivity
  -- lemma closes the null-space coordinate map.
  exact injective_mulVec_of_rank_eq_width Z hRankZ

/-- Helper for Chapter09 Exercise 9.13: the orthogonal complement identity
`range(Aᵀ) = ker(Zᵀ)` coming from `A * Z = 0` and the full-row-rank dimension count. -/
lemma range_transpose_eq_ker_reducedBasis_transpose
    (A : ConstraintMatrix)
    (Z : ReducedBasisMatrix)
    (hA : Matrix.rank A = m)
    (hZ : IsReducedNullMatrix Aᵀ Z) :
    LinearMap.range (Matrix.toLin' Aᵀ) = LinearMap.ker (Matrix.toLin' Zᵀ) := by
  have hAZ : A * Z = 0 := constraint_mul_reducedBasis_eq_zero A Z hZ
  have hZTA : Zᵀ * Aᵀ = 0 := by
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hAZ
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro p ⟨lam, rfl⟩
    rw [LinearMap.mem_ker]
    calc
      Matrix.toLin' Zᵀ (Matrix.toLin' Aᵀ lam) = Zᵀ.mulVec (Aᵀ.mulVec lam) := by
        simp [Matrix.toLin'_apply]
      _ = (Zᵀ * Aᵀ).mulVec lam := by
        exact Matrix.mulVec_mulVec lam Zᵀ Aᵀ
      _ = 0 := by simp [hZTA]
  · have hRangeAT : Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' Aᵀ)) = m := by
      rw [Matrix.range_toLin', ← Matrix.rank_eq_finrank_span_cols]
      simpa [Matrix.rank_transpose] using hA
    have hZInj : Function.Injective Z.mulVec := reducedBasis_mulVec_injective A Z hA hZ
    have hToLinZInj : Function.Injective (Matrix.toLin' Z) := by
      intro u₁ u₂ hEq
      exact hZInj (by simpa [Matrix.toLin'_apply] using hEq)
    have hRangeZT : Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' Zᵀ)) = n - m := by
      have hRangeZ : Module.finrank 𝕜 (LinearMap.range (Matrix.toLin' Z)) = n - m := by
        simpa using LinearMap.finrank_range_of_inj hToLinZInj
      have hRankZ : Matrix.rank Z = n - m := by
        rw [Matrix.range_toLin'] at hRangeZ
        rw [Matrix.rank_eq_finrank_span_cols]
        exact hRangeZ
      rw [Matrix.range_toLin', ← Matrix.rank_eq_finrank_span_cols]
      simpa [Matrix.rank_transpose] using hRankZ
    have hdim : Module.finrank 𝕜 PrimalPoint = n := by
      simpa using Module.finrank_fintype_fun_eq_card (R := 𝕜) (η := Fin n)
    have hKerZT_sum :
        Module.finrank 𝕜 (LinearMap.ker (Matrix.toLin' Zᵀ)) + (n - m) = n := by
      simpa [add_comm, hRangeZT, hdim] using
        LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' Zᵀ)
    have hKerZT : Module.finrank 𝕜 (LinearMap.ker (Matrix.toLin' Zᵀ)) = m := by
      have hmn : m ≤ n := by
        rw [← hA]
        exact Matrix.rank_le_width A
      have hKerZT' :
          Module.finrank 𝕜 (LinearMap.ker (Matrix.toLin' Zᵀ)) = n - (n - m) :=
        Nat.eq_sub_of_add_eq hKerZT_sum
      simpa [Nat.sub_sub_self hmn] using hKerZT'
    exact hRangeAT.trans hKerZT.symm

/-- Chapter09 Exercise 9.13: if `A : 𝕜^(m × n)` has full row rank and `Z` is a reduced-null-space
matrix for `Aᵀ`, then the block matrix `[[B, Aᵀ], [A, 0]] = kktMatrix B (-Aᵀ)` is nonsingular if
and only if `Zᵀ B Z` is nonsingular. This packages the textbook null-space assumptions through the
Chapter 9 owner `IsReducedNullMatrix Aᵀ Z`. -/
theorem blockMatrix_isUnit_iff_compression_isUnit
    (B : HessianMatrix)
    (A : ConstraintMatrix)
    (Z : ReducedBasisMatrix)
    (hA : Matrix.rank A = m)
    (hZ : IsReducedNullMatrix Aᵀ Z) :
    IsUnit (kktMatrix B (-Aᵀ)) ↔
      IsUnit (Zᵀ * B * Z) := by
  constructor
  · intro hKKT
    apply (Matrix.mulVec_injective_iff_isUnit).mp
    intro u₁ u₂ hu
    let u : ReducedPoint := u₁ - u₂
    have huZero : (Zᵀ * B * Z).mulVec u = 0 := by
      simpa [u, Matrix.mulVec_sub, hu]
    let p : PrimalPoint := Z.mulVec u
    have hpCompressed : Zᵀ.mulVec (B.mulVec p) = 0 := by
      -- Compress the reduced-Hessian kernel equation back to the primal-space vector `p = Z u`.
      calc
        Zᵀ.mulVec (B.mulVec p) = (Zᵀ * B * Z).mulVec u := by
          dsimp [p]
          rw [Matrix.mul_assoc]
          symm
          simp [Matrix.mulVec_mulVec]
        _ = 0 := huZero
    have hpMemKer : B.mulVec p ∈ LinearMap.ker (Matrix.toLin' Zᵀ) := by
      rw [LinearMap.mem_ker]
      simpa [Matrix.toLin'_apply] using hpCompressed
    have hRangeEq : LinearMap.range (Matrix.toLin' Aᵀ) = LinearMap.ker (Matrix.toLin' Zᵀ) :=
      range_transpose_eq_ker_reducedBasis_transpose A Z hA hZ
    have hNegMemRange : -B.mulVec p ∈ LinearMap.range (Matrix.toLin' Aᵀ) := by
      simpa [hRangeEq] using Submodule.neg_mem (LinearMap.ker (Matrix.toLin' Zᵀ)) hpMemKer
    obtain ⟨lam, hlam⟩ := hNegMemRange
    have hLam : Aᵀ.mulVec lam = -B.mulVec p := by
      simpa [Matrix.toLin'_apply] using hlam
    have hPrimal : B.mulVec p + Aᵀ.mulVec lam = 0 := by
      -- The range/ker complement produces the Lagrange multiplier that closes the primal block.
      rw [hLam]
      simp
    have hDual : A.mulVec p = 0 := by
      -- The reduced-null-space condition keeps `p` inside `ker A`.
      dsimp [p]
      simpa using hZ.mem_ker u
    have hKernel :
        (kktMatrix B (-Aᵀ)).mulVec (Sum.elim p lam) = 0 := by
      -- Route correction: the proof uses the source block equations directly instead of switching
      -- to a determinant argument.
      ext i <;> cases i with
      | inl i =>
          simpa [kktMatrix, sub_eq_add_neg, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using
            congrFun hPrimal i
      | inr i =>
          simpa [kktMatrix, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using congrFun hDual i
    have hKKTInj : Function.Injective (kktMatrix B (-Aᵀ)).mulVec :=
      (Matrix.mulVec_injective_iff_isUnit).2 hKKT
    have hPairZero : Sum.elim p lam = 0 := hKKTInj (by simpa using hKernel)
    have hpZero : p = 0 := by
      funext i
      simpa [p] using congrFun hPairZero (Sum.inl i)
    have hZInj : Function.Injective Z.mulVec := reducedBasis_mulVec_injective A Z hA hZ
    have huEqZero : u = 0 := hZInj (by simpa [p] using hpZero)
    simpa [u] using sub_eq_zero.mp huEqZero
  · intro hReduced
    apply (Matrix.mulVec_injective_iff_isUnit).mp
    intro y₁ y₂ hy
    let y : Sum (Fin n) (Fin m) → 𝕜 := y₁ - y₂
    have hyZero : (kktMatrix B (-Aᵀ)).mulVec y = 0 := by
      simpa [y, Matrix.mulVec_sub, hy]
    let p : PrimalPoint := y ∘ Sum.inl
    let lam : DualPoint := y ∘ Sum.inr
    have hyDecomp : y = Sum.elim p lam := by
      funext i
      cases i <;> rfl
    have hPrimal : B.mulVec p + Aᵀ.mulVec lam = 0 := by
      -- Split the block equation into its primal component and normalize the signs coming from
      -- `kktMatrix B (-Aᵀ)`.
      ext i
      have hi : (kktMatrix B (-Aᵀ)).mulVec (Sum.elim p lam) (Sum.inl i) = 0 := by
        simpa [hyDecomp] using congrFun hyZero (Sum.inl i)
      simpa [kktMatrix, sub_eq_add_neg, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using hi
    have hDual : A.mulVec p = 0 := by
      -- The lower block recovers the original constraint equation `A p = 0`.
      ext i
      have hi : (kktMatrix B (-Aᵀ)).mulVec (Sum.elim p lam) (Sum.inr i) = 0 := by
        simpa [hyDecomp] using congrFun hyZero (Sum.inr i)
      simpa [kktMatrix, Matrix.fromBlocks_mulVec, Matrix.neg_mulVec] using hi
    obtain ⟨u, hu⟩ := hZ.eq_mulVec p hDual
    have hAZ : A * Z = 0 := constraint_mul_reducedBasis_eq_zero A Z hZ
    have hZAT : Zᵀ * Aᵀ = 0 := by
      simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hAZ
    have hCompressed : (Zᵀ * B * Z).mulVec u = 0 := by
      -- Compress the primal block by `Zᵀ` and eliminate the mixed term with `Zᵀ Aᵀ = 0`.
      calc
        (Zᵀ * B * Z).mulVec u = Zᵀ.mulVec (B.mulVec (Z.mulVec u)) := by
          rw [Matrix.mul_assoc]
          simp [Matrix.mulVec_mulVec]
        _ = Zᵀ.mulVec (B.mulVec p) := by simp [hu]
        _ = Zᵀ.mulVec (-(Aᵀ.mulVec lam)) := by
          rw [eq_neg_of_add_eq_zero_left hPrimal]
        _ = -(Zᵀ.mulVec (Aᵀ.mulVec lam)) := by
          rw [Matrix.mulVec_neg]
        _ = -((Zᵀ * Aᵀ).mulVec lam) := by
          simp [Matrix.mulVec_mulVec]
        _ = 0 := by simp [hZAT]
    have hReducedInj : Function.Injective (Zᵀ * B * Z).mulVec :=
      (Matrix.mulVec_injective_iff_isUnit).2 hReduced
    have huZero : u = 0 := hReducedInj (by simpa using hCompressed)
    have hpZero : p = 0 := by
      simpa [huZero] using hu.symm
    have hAtransInj : Function.Injective Aᵀ.mulVec := by
      apply injective_mulVec_of_rank_eq_width
      simpa [Matrix.rank_transpose] using hA
    have hLamZero : lam = 0 := by
      apply hAtransInj
      simpa [hpZero] using hPrimal
    have hyEqZero : y = 0 := by
      calc
        y = Sum.elim p lam := hyDecomp
        _ = 0 := by
          ext i <;> cases i <;> simp [hpZero, hLamZero]
    exact sub_eq_zero.mp (by simpa [y] using hyEqZero)

end
