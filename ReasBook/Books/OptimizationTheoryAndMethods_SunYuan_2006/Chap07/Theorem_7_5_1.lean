/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_1_10

open Matrix
open scoped Matrix.Norms.Frobenius

noncomputable section

/-
Domain sampling for this item:
- primary domain: weighted least-change quasi-Newton Hessian updates on real square matrices;
- sampled owner declarations in the same domain:
  `weightedFrobeniusNorm` from Chapter 1 for the weighted Frobenius objective,
  `symmetrizedBroydenLimit` from Chapter 5 for the general symmetric rank-two Hessian update,
  and its Chapter 5 specializations such as `powellSymmetricBroydenUpdate`;
- source/core/bridge triage:
  the theorem below is source-facing,
  `symmetrizedBroydenLimit` and `weightedFrobeniusNorm` are the core/canonical owners,
  and the Chapter 7 least-squares vector `v` is only source-side secant data fed into that owner;
- primitive data here: the current matrix `B`, secant data `s v y`, and the weight matrix `T`;
- derived API removed from this file: the duplicate local update formula and the duplicate local
  weighted Frobenius wrapper.

This file therefore keeps only the source-facing minimization theorem and reuses the existing
Chapter 1 and Chapter 5 owners directly.
-/

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Chapter07 Theorem 7.5.1: a positive-definite weight matrix `T` carrying
`(T * Tᵀ).mulVec s` to `v` also satisfies the Chapter 5 secant bridge
`T⁻¹.mulVec v = T.mulVec s`. -/
lemma nonsingInvMulVec_v_eq_mulVec_s_of_posDef
    {T : MatrixN} {s v : Point}
    (hTpos : T.PosDef) (hTv : (T * Tᵀ).mulVec s = v) :
    T⁻¹.mulVec v = T.mulVec s := by
  -- Rewrite the source relation through `T⁻¹`; positive definiteness supplies the inverse data.
  have hTsymm : T.IsSymm := by
    simpa [Matrix.isHermitian_iff_isSymm] using hTpos.isHermitian
  -- Local instance justification (matrix inversion): `Matrix.inv_mulVec_eq_vec` needs
  -- `[Invertible T]`, and positive definiteness gives the canonical invertibility witness.
  let _ := hTpos.isUnit.invertible
  calc
    T⁻¹.mulVec v = T⁻¹.mulVec ((T * Tᵀ).mulVec s) := by rw [hTv]
    _ = (T⁻¹ * (T * Tᵀ)).mulVec s := by rw [Matrix.mulVec_mulVec]
    _ = ((T⁻¹ * T) * Tᵀ).mulVec s := by rw [Matrix.mul_assoc]
    _ = Tᵀ.mulVec s := by simp [Matrix.inv_mul_of_invertible]
    _ = T.mulVec s := by simpa [hTsymm.eq]

/-- Helper for Chapter07 Theorem 7.5.1: translating a Chapter 7 competitor by subtracting the
base matrix `B` converts its feasibility condition into the Chapter 5 zero-base symmetric secant
condition with right-hand side `y - B.mulVec s`. -/
lemma weightedLeastChangeFeasible_iff_zeroBase
    (B Bnext : MatrixN) (s y : Point) :
    ((Bnext - B).IsSymm ∧ Bnext.mulVec s = y) ↔
      ((Bnext - B).IsSymm ∧
        satisfiesQuasiNewtonEquationHessianForm (Bnext - B).toEuclideanLin s
          (y - Matrix.toEuclideanLin B s)) := by
  constructor
  · intro h
    rcases h with ⟨hSymm, hSecant⟩
    refine ⟨hSymm, ?_⟩
    -- Rewrite the secant equation for the increment matrix `Bnext - B`.
    refine satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff.mpr ?_
    calc
      (Bnext - B).mulVec s.ofLp = Bnext.mulVec s.ofLp - B.mulVec s.ofLp := by
        simp [Matrix.sub_mulVec]
      _ = y.ofLp - B.mulVec s.ofLp := by rw [hSecant]
      _ = (y - Matrix.toEuclideanLin B s).ofLp := by
        simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  · intro h
    rcases h with ⟨hSymm, hSecant⟩
    refine ⟨hSymm, ?_⟩
    -- Convert the zero-base secant equation back to the original Chapter 7 surface.
    have hMulVec :
        (Bnext - B).mulVec s.ofLp = (y - Matrix.toEuclideanLin B s).ofLp :=
      satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff.mp hSecant
    have hAddMulVec :
        Bnext.mulVec s.ofLp = (Bnext - B).mulVec s.ofLp + B.mulVec s.ofLp := by
      have hSubMulVec :
          (Bnext - B).mulVec s.ofLp = Bnext.mulVec s.ofLp - B.mulVec s.ofLp := by
        simp [Matrix.sub_mulVec]
      have hShift := congrArg (fun z ↦ z + B.mulVec s.ofLp) hSubMulVec
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hShift.symm
    calc
      Bnext.mulVec s.ofLp = (Bnext - B).mulVec s.ofLp + B.mulVec s.ofLp := hAddMulVec
      _ = (y - Matrix.toEuclideanLin B s).ofLp + B.mulVec s.ofLp := by rw [hMulVec]
      _ = y.ofLp := by
        simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, sub_eq_add_neg, add_assoc, add_left_comm,
          add_comm]

/-- Helper for Chapter07 Theorem 7.5.1: subtracting the base matrix from the Chapter 7 update
normalizes it to the Chapter 5 zero-base symmetrized Broyden limit with right-hand side
`y - B.mulVec s`. -/
lemma symmetrizedBroydenLimit_sub_eq_zeroBase
    (B : MatrixN) (s y v : Point) :
    symmetrizedBroydenLimit B s y v - B =
      symmetrizedBroydenLimit (0 : MatrixN) s (y - Matrix.toEuclideanLin B s) v := by
  -- Unfold the explicit owner once; afterwards both sides are syntactically the same correction.
  ext i j
  simp [symmetrizedBroydenLimit, Matrix.toEuclideanLin, Matrix.toLpLin_apply, sub_eq_add_neg]
  ring

/-- Chapter07 Theorem 7.5.1: for the Chapter 7 secant vector `v`, if `0 < dotProduct s v`, `T`
is positive definite, and `(T * Tᵀ).mulVec s = v`, then the update in `(7.5.11)`, namely the
Chapter 5 owner `symmetrizedBroydenLimit B s y v`, is the unique minimizer of the weighted
Frobenius change `weightedFrobeniusNorm T⁻¹ (Bnext - B)` among matrices `Bnext` whose change
from `B` is symmetric and that satisfy the secant equation `Bnext.mulVec s = y`. -/
theorem weightedLeastChangeHessianUpdate_isUniqueMinimizer
    (B T : MatrixN) (s v y : Point)
    (hsv : 0 < dotProduct s v)
    (hTpos : T.PosDef)
    (hTv : (T * Tᵀ).mulVec s = v) :
    let Bbar := symmetrizedBroydenLimit B s y v
    let δ : MatrixN → ℝ := weightedFrobeniusNorm T⁻¹
    let feasibleSet : Set MatrixN := {Bnext | (Bnext - B).IsSymm ∧ Bnext.mulVec s = y}
    Bbar ∈ feasibleSet ∧
      IsMinOn (fun Bnext ↦ δ (Bnext - B)) feasibleSet Bbar ∧
      ∀ Bnext ∈ feasibleSet, δ (Bnext - B) = δ (Bbar - B) → Bnext = Bbar := by
  dsimp
  let r : Point := y - Matrix.toEuclideanLin B s
  let Δbar : MatrixN := symmetrizedBroydenLimit (0 : MatrixN) s r v
  let zeroBaseFeasibleSet : Set MatrixN :=
    {Δ | Δ.IsSymm ∧ satisfiesQuasiNewtonEquationHessianForm Δ.toEuclideanLin s r}
  have hvs : 0 < dotProduct v s := by
    simpa [dotProduct_comm] using hsv
  have hvs_ne : dotProduct v s ≠ 0 := by
    linarith
  have hTsymm : T.IsSymm := by
    simpa [Matrix.isHermitian_iff_isSymm] using hTpos.isHermitian
  have hTinvSymm : (T⁻¹).IsSymm := hTsymm.inv
  have hTdet : IsUnit T.det := T.isUnit_iff_isUnit_det.mp hTpos.isUnit
  have hTinvDet : IsUnit (T⁻¹).det := Matrix.isUnit_nonsing_inv_det (A := T) hTdet
  have hTinvv : T⁻¹.mulVec v = T.mulVec s :=
    nonsingInvMulVec_v_eq_mulVec_s_of_posDef hTpos hTv
  have hMc : T⁻¹.mulVec v = (T⁻¹)⁻¹.mulVec s := by
    -- Rewrite the Chapter 7 weight identity into the exact Chapter 5 hypothesis.
    calc
      T⁻¹.mulVec v = T.mulVec s := hTinvv
      _ = (T⁻¹)⁻¹.mulVec s := by
        rw [Matrix.nonsing_inv_nonsing_inv (A := T) hTdet]
  have hDeltaEq :
      symmetrizedBroydenLimit B s y v - B = Δbar := by
    -- Identify the Chapter 7 correction with the Chapter 5 zero-base owner.
    simpa [Δbar, r] using symmetrizedBroydenLimit_sub_eq_zeroBase B s y v
  have hDeltaFeasible :
      Δbar ∈ zeroBaseFeasibleSet := by
    refine ⟨?_, ?_⟩
    · -- The zero-base owner is symmetric because the zero matrix is symmetric.
      simpa [Δbar] using
        (symmetrizedBroydenLimit_isSymm (B := (0 : MatrixN)) (by simp) s r v)
    · -- The zero-base owner satisfies the zero-base secant equation.
      refine satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff.mpr ?_
      have hMul :
          Matrix.toEuclideanLin (symmetrizedBroydenLimit (0 : MatrixN) s r v) s = r :=
        symmetrizedBroydenLimit_mulVec (B := (0 : MatrixN)) (s := s) (y := r) (c := v) hvs_ne
      simpa [Δbar, Matrix.toEuclideanLin, Matrix.toLpLin_apply] using congrArg WithLp.ofLp hMul
  have hMapsTo :
      Set.MapsTo (fun Bnext : MatrixN ↦ Bnext - B)
        {Bnext | (Bnext - B).IsSymm ∧ Bnext.mulVec s = y}
        zeroBaseFeasibleSet := by
    intro Bnext hBnext
    exact (weightedLeastChangeFeasible_iff_zeroBase B Bnext s y).mp hBnext
  have hMinZero :
      IsMinOn (fun Δ : MatrixN ↦ weightedFrobeniusNorm T⁻¹ Δ) zeroBaseFeasibleSet Δbar := by
    -- Apply the Chapter 5 weighted least-change theorem to the zero-base correction problem.
    simpa [zeroBaseFeasibleSet, Δbar, r, sub_zero] using
      (symmetrizedBroydenLimit_isMinOn_weightedFrobeniusSymmetricSecantSet
        (B := (0 : MatrixN)) (M := T⁻¹) (c := v) (s := s) (y := r)
        (hB := by simp) (hM := hTinvSymm) (hMdet := hTinvDet)
        (hcs := hvs) (hMc := hMc))
  have hBbarMem :
      symmetrizedBroydenLimit B s y v ∈ {Bnext | (Bnext - B).IsSymm ∧ Bnext.mulVec s = y} := by
    -- Transport the zero-base feasibility back to the original Chapter 7 variables.
    refine (weightedLeastChangeFeasible_iff_zeroBase B (symmetrizedBroydenLimit B s y v) s y).mpr ?_
    simpa [zeroBaseFeasibleSet, hDeltaEq] using hDeltaFeasible
  have hMinTarget :
      IsMinOn
        (fun Bnext : MatrixN ↦ weightedFrobeniusNorm T⁻¹ (Bnext - B))
        {Bnext | (Bnext - B).IsSymm ∧ Bnext.mulVec s = y}
        (symmetrizedBroydenLimit B s y v) := by
    -- Pull back the zero-base minimizer along `Bnext ↦ Bnext - B`.
    convert hMinZero.comp_mapsTo hMapsTo hDeltaEq using 1
    ext Bnext
    rfl
  refine ⟨hBbarMem, hMinTarget, ?_⟩
  intro Bnext hBnext hEq
  have hBnextZero :
      (Bnext - B) ∈ zeroBaseFeasibleSet :=
    hMapsTo hBnext
  have hDeltaUnique :
      Bnext - B = Δbar := by
    -- Equality of the weighted objectives forces equality with the zero-base minimizer.
    apply symmetrizedBroydenLimit_weightedFrobenius_eq_imp
      (B := (0 : MatrixN)) (M := T⁻¹) (c := v) (s := s) (y := r)
      (hB := by simp) (hM := hTinvSymm) (hMdet := hTinvDet)
      (hcs := hvs) (hMc := hMc)
    · exact hBnextZero.1
    · exact hBnextZero.2
    · simpa [Δbar, r, hDeltaEq, sub_zero] using hEq
  -- Add back the base matrix to recover equality of the original Chapter 7 competitors.
  have hShifted :
      Bnext = Δbar + B := by
    have := congrArg (fun X : MatrixN ↦ X + B) hDeltaUnique
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
  calc
    Bnext = Δbar + B := hShifted
    _ = symmetrizedBroydenLimit B s y v := by
      have := congrArg (fun X : MatrixN ↦ X + B) hDeltaEq.symm
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this

end
