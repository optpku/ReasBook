/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_34
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open Matrix
open scoped BigOperators EllipsoidNotation Pointwise PositiveDefMatrixNorm SupportFunction
  SymmetricBox

variable {n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 7.7 lies in Chapter 7's diagonal ellipsoid / dual-norm comparison domain.

Sampled owner-style declarations:
- `Matrix.IsDiag` and `Matrix.PosDef` in mathlib's diagonal / positive-definite matrix API, the
  canonical matrix-level owners for diagonal positive-definite matrices;
- `positiveDefMatrixNorm` and its dual notation `‖g‖[G,*]` in `Definition_7_23`, the core owner
  for the weighted dual norm;
- `matrixEllipsoid` with centered notation `W[r](G)` in `Definition_7_26`, the chapter owner for
  ellipsoids;
- `ellipsoidBoxGeneratedConvexSet`, `ellipsoidBoxInterpolationMatrix`, and
  `ellipsoidBoxLogVolumePotential` in `Definition_7_34`, the source-facing owners introduced for
  the present geometric construction.

Best owner abstraction:
- source-facing: `ellipsoidBoxAlphaStar` and the four theorem-level consequences of Lemma 7.7;
- core/canonical: `Matrix.PosDef`, `‖g‖[G,*]`, `W[r](G)`, and
  `ellipsoidBoxLogVolumePotential`;
- bridge/view: the explicit formula for `α*` and the scalar logarithmic comparison expression used
  in parts (3) and (4).

Primitive data:
- a matrix `D : Matₙ`;
- its positive-definiteness proof when the dual norm is used;
- a vector `g : Eₙ`;
- scalar parameters `α` and `γ`.

Derived API:
- the dual-norm square `‖g‖[⟨D, hDpos⟩,*] ^ 2` is derived from the upstream owner and is not kept
  as a separate public definition;
- the source-facing critical value `α*`;
- the theorem-level logarithmic comparison bounds used in parts (3) and (4).

Source/core/bridge triage:
- source-facing: `ellipsoidBoxAlphaStar`;
- core/canonical: `⟨D, hDpos⟩`, `W[r](G)`, `ellipsoidBoxLogVolumePotential`;
- bridge/view: the theorem-level inequalities below.

This refinement removes the duplicate public scalar wrapper for `‖g‖*_D²` and rewrites the target
file directly against the canonical dual-norm owner supplied upstream. -/

/-- The critical value `α* = (S - n) / ((2 S - n) S)` used in the sign-invariant rounding step,
where `S = ‖g‖[⟨D, hDpos⟩,*]^2`. -/
def ellipsoidBoxAlphaStar
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) : ℝ :=
  (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ) - (n : ℝ)) /
    ((((2 : ℝ) * (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ))) - (n : ℝ)) *
      (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)))

-- Proof sketch: unfold `ellipsoidBoxAlphaStar`.
/-- Expanding `ellipsoidBoxAlphaStar d g` gives the closed formula
`(S - n) / ((2 S - n) S)` with `S = ‖g‖[⟨D, hDpos⟩,*]^2`. -/
theorem ellipsoidBoxAlphaStar_eq
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) :
    ellipsoidBoxAlphaStar D hDpos g =
      (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ) - (n : ℝ)) /
        ((((2 : ℝ) * (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ))) - (n : ℝ)) *
          (‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ))) :=
  rfl

-- Proof sketch: write `S = ‖g‖[d.toPositiveDefMatrix,*]^2`. The hypothesis `S > n` gives
-- positivity of the numerator and denominator in the defining formula for `α*`; if `n = 0`, then
-- `α* = 1 / (2 S)`, while if `0 < n`, `ellipsoidBoxAlphaStar_mem_Ioc_inv_dim` yields
-- `0 < α* ≤ 1 / n ≤ 1`. In either case `α* ∈ [0, 1)`.
/-- Under `S > n`, the canonical value `α*` lies in the half-open unit interval `[0, 1)`. -/
theorem ellipsoidBoxAlphaStar_mem_halfOpenUnitInterval
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ)
    (hS : (n : ℝ) < ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)) :
    ellipsoidBoxAlphaStar D hDpos g ∈ Set.Ico (0 : ℝ) 1 := by
  let S : ℝ := ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)
  have hSgt : (n : ℝ) < S := hS
  have hn_pos : 0 < n := by
    by_contra hn_pos
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn_pos
    have hg_zero : g = 0 := by
      ext i
      have : False := by
        simpa [hn_zero] using i.2
      exact False.elim this
    have hnormsq_zero : S = 0 := by
      dsimp [S]
      -- The zero vector has zero weighted dual norm, so its squared norm is also zero.
      have hdual_zero : ‖(0 : Eₙ)‖[⟨D, hDpos⟩,*] = 0 := by
        rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
        simp
      simpa [hg_zero, hdual_zero]
    have : ¬ ((n : ℝ) < S) := by
      simpa [hn_zero, hnormsq_zero]
    exact this hS
  have hSpos : 0 < S := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    linarith
  have htwoS_sub_pos : 0 < (2 : ℝ) * S - (n : ℝ) := by
    nlinarith
  have hden_pos : 0 < (((2 : ℝ) * S - (n : ℝ)) * S) := by
    exact mul_pos htwoS_sub_pos hSpos
  have hα_pos : 0 < ellipsoidBoxAlphaStar D hDpos g := by
    -- The source hypothesis `S > n` makes both numerator and denominator positive.
    rw [ellipsoidBoxAlphaStar_eq]
    exact div_pos (sub_pos.mpr hSgt) hden_pos
  have hfactor_gt_one : 1 < (2 : ℝ) * S - (n : ℝ) := by
    have hnone_le : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn_pos
    linarith
  have hα_lt_one : ellipsoidBoxAlphaStar D hDpos g < 1 := by
    -- Compare the defining numerator with the denominator through `S = ‖g‖*_D²`.
    rw [ellipsoidBoxAlphaStar_eq]
    have hnum_lt_den :
        S - (n : ℝ) < (((2 : ℝ) * S - (n : ℝ)) * S) := by
      have hn_real_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
      have hnum_lt_S : S - (n : ℝ) < S := by
        linarith
      have hS_lt_den : S < (((2 : ℝ) * S - (n : ℝ)) * S) := by
        have := mul_lt_mul_of_pos_right hfactor_gt_one hSpos
        simpa [one_mul] using this
      exact lt_trans hnum_lt_S hS_lt_den
    exact (div_lt_one hden_pos).2 hnum_lt_den
  exact ⟨hα_pos.le, hα_lt_one⟩

-- Semantic recall check: `Definition_7_26` only exposes the ordinary ellipsoid owner `W[r](G)`
-- via `G⁻¹`, so the `α = 1` boundary from the source must be modeled explicitly as a degenerate
-- endpoint rather than by feeding a singular matrix into that owner.
/-- The closed interpolation family from Lemma 7.7 (1), where the boundary value `α = 1` is read
as the degenerate box `B(|g|)` rather than the ordinary inverse-matrix ellipsoid owner. -/
def ellipsoidBoxClosedInterpolationSection
    (D : Matₙ) (g : Eₙ) (α : ℝ) : Set Eₙ :=
  if α = 1 then
    B(|g|)
  else
    W[1]((ellipsoidBoxInterpolationMatrix D g α))

/-- At the source boundary `α = 1`, the closed interpolation family is exactly the box `B(|g|)`.
-/
@[simp] theorem ellipsoidBoxClosedInterpolationSection_one
    (D : Matₙ) (g : Eₙ) :
    ellipsoidBoxClosedInterpolationSection D g 1 = B(|g|) := by
  simp [ellipsoidBoxClosedInterpolationSection]

/-- Away from the degenerate boundary `α = 1`, the closed interpolation family is the ordinary
centered ellipsoid `W₁(G(α))`. -/
theorem ellipsoidBoxClosedInterpolationSection_eq_centeredMatrixEllipsoid
    (D : Matₙ) (g : Eₙ) {α : ℝ} (hα : α ≠ 1) :
    ellipsoidBoxClosedInterpolationSection D g α =
      W[1]((ellipsoidBoxInterpolationMatrix D g α)) := by
  simp [ellipsoidBoxClosedInterpolationSection, hα]

/-- Helper for Lemma 7.7: the coordinatewise absolute-value map on `Eₙ`. -/
def coordwiseAbs (x : Eₙ) : Eₙ :=
  WithLp.toLp 2 fun i ↦ |x i|

/-- Helper for Lemma 7.7: the coordinates of `coordwiseAbs x` are the absolute values of the
coordinates of `x`. -/
@[simp] theorem coordwiseAbs_apply (x : Eₙ) (i : Fin n) :
    coordwiseAbs x i = |x i| := by
  simp [coordwiseAbs]

/-- Helper for Lemma 7.7: coordinatewise absolute value lands in the nonnegative orthant. -/
theorem coordwiseAbs_mem_nonnegativeOrthant (x : Eₙ) :
    coordwiseAbs x ∈ nonnegativeOrthant n := by
  intro i
  simp [coordwiseAbs]

/-- Helper for Lemma 7.7: nonnegative vectors are fixed by coordinatewise absolute value. -/
theorem coordwiseAbs_eq_self_of_mem_nonnegativeOrthant {x : Eₙ}
    (hx : x ∈ nonnegativeOrthant n) :
    coordwiseAbs x = x := by
  ext i
  simp [coordwiseAbs, abs_of_nonneg (hx i)]

/-- Helper for Lemma 7.7: squaring the weighted `D`-norm recovers the corresponding quadratic
form. -/
theorem positiveDefMatrixNorm_sq_eq_matrix_quadratic
    {D : Matₙ} (hDpos : D.PosDef) (z : Eₙ) :
    ‖z‖[⟨D, hDpos⟩] ^ (2 : ℕ) =
      inner ℝ ((Matrix.toEuclideanLin D) z) z := by
  -- Rewrite the norm through its square-root definition and then square it back.
  have hPosLin : (Matrix.toEuclideanLin D).IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hDpos.posSemidef
  have hnonneg : 0 ≤ inner ℝ ((Matrix.toEuclideanLin D) z) z := by
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right z
  rw [positiveDefMatrixNorm_def]
  exact Real.sq_sqrt hnonneg

/-- Helper for Lemma 7.7: diagonal weighted norms are unchanged by coordinatewise absolute
value. -/
theorem positiveDefMatrixNorm_coordwiseAbs_eq_of_isDiag
    {D : Matₙ} (hDdiag : D.IsDiag) (hDpos : D.PosDef) (z : Eₙ) :
    ‖coordwiseAbs z‖[⟨D, hDpos⟩] = ‖z‖[⟨D, hDpos⟩] := by
  -- Compare the squared norms first, where diagonality makes the quadratic forms identical.
  have hsq :
      ‖coordwiseAbs z‖[⟨D, hDpos⟩] ^ (2 : ℕ) = ‖z‖[⟨D, hDpos⟩] ^ (2 : ℕ) := by
    rw [positiveDefMatrixNorm_sq_eq_matrix_quadratic hDpos (coordwiseAbs z)]
    rw [positiveDefMatrixNorm_sq_eq_matrix_quadratic hDpos z]
    have hdiag_eq : D = diagonal D.diag := by
      simpa using hDdiag.diagonal_diag.symm
    rw [hdiag_eq]
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hmul :
        (D i i * |z.ofLp i|) * |z.ofLp i| = (D i i * z.ofLp i) * z.ofLp i := by
      calc
        (D i i * |z.ofLp i|) * |z.ofLp i|
            = D i i * (|z.ofLp i| * |z.ofLp i|) := by ring
        _ = D i i * (z.ofLp i * z.ofLp i) := by
              simpa [pow_two] using congrArg (fun t : ℝ ↦ D i i * t) (sq_abs (z.ofLp i))
        _ = (D i i * z.ofLp i) * z.ofLp i := by ring
    have hmul_inner :
        inner ℝ (D i i * |z.ofLp i|) |z.ofLp i| =
          inner ℝ (D i i * z.ofLp i) (z.ofLp i) := by
      rw [real_inner_eq_re_inner, real_inner_eq_re_inner]
      simpa [RCLike.inner_apply, mul_comm, mul_left_comm, mul_assoc] using hmul
    simpa [coordwiseAbs, Matrix.toEuclideanLin_apply, Matrix.mulVec_diagonal] using hmul_inner
  rcases eq_or_eq_neg_of_sq_eq_sq ‖coordwiseAbs z‖[⟨D, hDpos⟩] ‖z‖[⟨D, hDpos⟩] hsq with hEq | hEq
  · exact hEq
  · have hleft_nonneg : 0 ≤ ‖coordwiseAbs z‖[⟨D, hDpos⟩] := by positivity
    have hright_nonneg : 0 ≤ ‖z‖[⟨D, hDpos⟩] := by positivity
    nlinarith

/-- Helper for Lemma 7.7: the inverse matrix cancels the original Euclidean linear action. -/
theorem nonsingInv_toEuclideanLin_comp
    {D : Matₙ} (hDpos : D.PosDef) (x : Eₙ) :
    (D⁻¹).toEuclideanLin (D.toEuclideanLin x) = x := by
  -- Convert both linear maps back to matrix multiplication and use the inverse identity.
  have hDdet : IsUnit D.det := isUnit_iff_ne_zero.mpr (ne_of_gt hDpos.det_pos)
  have hmul : D⁻¹ * D = 1 := Matrix.nonsing_inv_mul D hDdet
  ext i
  simp [Matrix.mulVec_mulVec, hmul]

/-- Helper for Lemma 7.7: every primal `D`-norm is attained as a support value on the unit
ellipsoid `W[1](D)`. -/
theorem exists_inner_ellipsoid_point_attaining_positiveDefMatrixNorm
    {D : Matₙ} (hDpos : D.PosDef) (x : Eₙ) :
    ∃ y : Eₙ, y ∈ W[1](D) ∧ inner ℝ y x = ‖x‖[⟨D, hDpos⟩] := by
  by_cases hx : x = 0
  · refine ⟨0, ?_, ?_⟩
    · rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hDpos]
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
      simp
    · simp [hx]
  · let G : {G : Matₙ // G.PosDef} := ⟨D, hDpos⟩
    let p : ℝ := ‖x‖[G]
    let y : Eₙ := p⁻¹ • D.toEuclideanLin x
    have hp_pos : 0 < p := by
      dsimp [p]
      exact Seminorm.map_pos_of_ne_zero (positiveDefMatrixNorm D hDpos) hx
    have hquadratic_nonneg : 0 ≤ inner ℝ (D.toEuclideanLin x) x := by
      have hPosLin : D.toEuclideanLin.IsPositive :=
        Matrix.isPositive_toEuclideanLin_iff.mpr hDpos.posSemidef
      simpa [real_inner_comm] using hPosLin.inner_nonneg_right x
    have hp_sq : p ^ (2 : ℕ) = inner ℝ (D.toEuclideanLin x) x := by
      dsimp [p]
      rw [positiveDefMatrixNorm_def G x, Real.sq_sqrt hquadratic_nonneg]
    have hy_inv : (D⁻¹).toEuclideanLin y = p⁻¹ • x := by
      -- The inverse action removes the `D` factor in the explicit witness.
      dsimp [y]
      rw [LinearMap.map_smul, nonsingInv_toEuclideanLin_comp hDpos x]
    refine ⟨y, ?_, ?_⟩
    · rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hDpos]
      have hunit :
          p⁻¹ * (p⁻¹ * inner ℝ (D.toEuclideanLin x) x) = 1 := by
        rw [← hp_sq, pow_two]
        field_simp [hp_pos.ne']
      have hy_dual : ‖y‖[G,*] = 1 := by
        rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
        calc
          Real.sqrt (inner ℝ y ((D⁻¹).toEuclideanLin y))
              = Real.sqrt (p⁻¹ * (p⁻¹ * inner ℝ (D.toEuclideanLin x) x)) := by
                  rw [hy_inv]
                  dsimp [y]
                  rw [real_inner_smul_left, real_inner_smul_right]
          _ = Real.sqrt 1 := by rw [hunit]
          _ = 1 := by simp
      simpa [G] using hy_dual.le
    · -- The same normalization makes the pairing equal to the primal norm.
      calc
        inner ℝ y x = p⁻¹ * inner ℝ (D.toEuclideanLin x) x := by
            dsimp [y]
            rw [real_inner_smul_left]
        _ = p⁻¹ * p ^ (2 : ℕ) := by rw [hp_sq]
        _ = p := by
            rw [pow_two]
            field_simp [hp_pos.ne']
        _ = ‖x‖[G] := by rfl

/-- Helper for Lemma 7.7: the support function of `W[1](D)` is the primal `D`-norm. -/
theorem supportFunction_centeredMatrixEllipsoid_eq_coe_primalNorm
    (D : Matₙ) (hDpos : D.PosDef) (x : Eₙ) :
    ξ[W[1](D)] x = ((‖x‖[⟨D, hDpos⟩] : ℝ) : EReal) := by
  let G : {G : Matₙ // G.PosDef} := ⟨D, hDpos⟩
  have hnorm_nonneg : 0 ≤ ‖x‖[G] := by
    positivity
  have hupper : ξ[W[1](D)] x ≤ ((‖x‖[G] : ℝ) : EReal) := by
    -- Every ellipsoid point contributes at most the primal norm by the dual pairing estimate.
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy_dual : ‖y‖[G,*] ≤ 1 := by
      rwa [mem_centeredMatrixEllipsoid_iff_dualNorm_le hDpos] at hy
    calc
      ((inner ℝ y x : ℝ) : EReal) ≤ ((‖y‖[G,*] * ‖x‖[G] : ℝ) : EReal) := by
        exact_mod_cast
          (Seminorm.inner_le_dualNorm_mul (positiveDefMatrixNorm D hDpos) x y)
      _ ≤ ((1 * ‖x‖[G] : ℝ) : EReal) := by
        exact_mod_cast (mul_le_mul_of_nonneg_right hy_dual hnorm_nonneg)
      _ = ((‖x‖[G] : ℝ) : EReal) := by ring
  rcases exists_inner_ellipsoid_point_attaining_positiveDefMatrixNorm hDpos x with ⟨y, hy, hyEq⟩
  have hlower : ((‖x‖[G] : ℝ) : EReal) ≤ ξ[W[1](D)] x := by
    -- The explicit maximizing witness realizes the primal norm as a support value.
    rw [supportFunction_apply]
    simpa [hyEq] using
      (le_sSup ⟨y, hy, rfl⟩ :
        (((inner ℝ y x : ℝ) : EReal) ≤
          sSup ((fun g : Eₙ ↦ ((inner ℝ g x : ℝ) : EReal)) '' W[1](D))))
  simpa [G] using le_antisymm hupper hlower

/-- Helper for Lemma 7.7: the support function of the symmetric box `B(|g|)` is the linear form
`x ↦ ⟪|g|, |x|⟫`. -/
theorem supportFunction_symmetricBoxAbs_eq_coe_inner_coordwiseAbs
    (g x : Eₙ) :
    ξ[(symmetricBox (coordwiseAbs g) : Set Eₙ)] x =
      ((inner ℝ (coordwiseAbs g) (coordwiseAbs x) : ℝ) : EReal) := by
  have hupper :
      ξ[(symmetricBox (coordwiseAbs g) : Set Eₙ)] x ≤
        ((inner ℝ (coordwiseAbs g) (coordwiseAbs x) : ℝ) : EReal) := by
    -- The box constraints bound each coordinate contribution by `|g i| |x i|`.
    rw [supportFunction_apply]
    refine sSup_le ?_
    rintro _ ⟨s, hs, rfl⟩
    have hsabs : ∀ i : Fin n, |s i| ≤ coordwiseAbs g i :=
      mem_symmetricBox_iff_abs_le.mp hs
    have hcoord :
        inner ℝ s x ≤ inner ℝ (coordwiseAbs g) (coordwiseAbs x) := by
      rw [PiLp.inner_apply, PiLp.inner_apply]
      refine Finset.sum_le_sum ?_
      intro i hi
      have hsgi : |s i| ≤ |g i| := by
        simpa [coordwiseAbs] using hsabs i
      calc
        x.ofLp i * s.ofLp i ≤ |x.ofLp i * s.ofLp i| := le_abs_self _
        _ = |x.ofLp i| * |s.ofLp i| := by rw [abs_mul]
        _ ≤ |x.ofLp i| * |g i| := by
              exact mul_le_mul_of_nonneg_left hsgi (abs_nonneg _)
        _ = (coordwiseAbs x).ofLp i * (coordwiseAbs g).ofLp i := by
              simp [coordwiseAbs, mul_comm]
    change
      (((inner ℝ s x : ℝ) : EReal) ≤
        ((inner ℝ (coordwiseAbs g) (coordwiseAbs x) : ℝ) : EReal))
    exact_mod_cast hcoord
  let s : Eₙ := WithLp.toLp 2 fun i ↦ (SignType.sign (x i) : ℝ) * |g i|
  have hs_box : s ∈ symmetricBox (coordwiseAbs g) := by
    -- The sign choice stays in the box because each coordinate still has size `|g i|`.
    rw [mem_symmetricBox_iff_abs_le]
    intro i
    dsimp [s]
    rcases lt_trichotomy (x i) 0 with hneg | hzero | hpos
    · simp [coordwiseAbs, hneg]
    · simp [coordwiseAbs, hzero]
    · simp [coordwiseAbs, hpos]
  have hs_eq :
      inner ℝ s x = inner ℝ (coordwiseAbs g) (coordwiseAbs x) := by
    -- The same sign choice turns each coordinate contribution into `|g i| |x i|`.
    rw [PiLp.inner_apply, PiLp.inner_apply]
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [s]
    calc
      x.ofLp i * ((SignType.sign (x i) : ℝ) * |g i|) =
          (x i * (SignType.sign (x i) : ℝ)) * |g i| := by ring
      _ = |x i| * |g i| := by simpa using congrArg (fun t : ℝ ↦ t * |g i|) (self_mul_sign (x i))
      _ = (coordwiseAbs x).ofLp i * (coordwiseAbs g).ofLp i := by
            simp [coordwiseAbs, mul_comm]
  have hlower :
      ((inner ℝ (coordwiseAbs g) (coordwiseAbs x) : ℝ) : EReal) ≤
        ξ[(symmetricBox (coordwiseAbs g) : Set Eₙ)] x := by
    -- The support supremum is attained by the coordinatewise sign witness above.
    rw [supportFunction_apply]
    simpa [hs_eq] using
      (le_sSup ⟨s, hs_box, rfl⟩ :
        (((inner ℝ s x : ℝ) : EReal) ≤
          sSup ((fun y : Eₙ ↦ ((inner ℝ y x : ℝ) : EReal)) ''
            (symmetricBox (coordwiseAbs g) : Set Eₙ))))
  exact le_antisymm hupper hlower

/-- Helper for Lemma 7.7: the support function of `Conv(W₁(D) ∪ B(|g|))` is the maximum of the
`D`-primal norm and the box support `⟪|g|, |x|⟫`. -/
theorem supportFunction_ellipsoidBoxGeneratedConvexSet_toReal_eq_max
    (D : Matₙ) (hDpos : D.PosDef) (g x : Eₙ) :
    (ξ[ellipsoidBoxGeneratedConvexSet D g] x).toReal =
      max ‖x‖[⟨D, hDpos⟩] (inner ℝ (coordwiseAbs g) (coordwiseAbs x)) := by
  -- Assemble the generated-set support formula from the two owner-level support identities.
  have hbox : (B(|g|) : Set Eₙ) = symmetricBox (coordwiseAbs g) := by
    ext s
    simp [coordwiseAbs]
  have hsupport :
      ξ[ellipsoidBoxGeneratedConvexSet D g] x =
        max (((‖x‖[⟨D, hDpos⟩] : ℝ) : EReal))
          (((inner ℝ (coordwiseAbs g) (coordwiseAbs x) : ℝ) : EReal)) := by
    rw [ellipsoidBoxGeneratedConvexSet_def, supportFunction_convexHull_union_eq_max]
    rw [hbox]
    rw [supportFunction_centeredMatrixEllipsoid_eq_coe_primalNorm,
      supportFunction_symmetricBoxAbs_eq_coe_inner_coordwiseAbs]
  simpa using congrArg EReal.toReal hsupport

/-- Helper for Lemma 7.7: the interpolation matrix `G(α)` is positive definite on
`α ∈ [0, 1)`. -/
theorem ellipsoidBoxInterpolationMatrix_posDef
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) (α : ℝ)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    (ellipsoidBoxInterpolationMatrix D g α).PosDef := by
  -- Reuse the canonical positivity owner from Definition 7.34.
  simpa using ellipsoidBoxInterpolationMatrix_posDefIco D hDpos g α hα

/-- Helper for Lemma 7.7: squaring the `G(α)`-primal norm splits into the base `D`-term and the
coordinate square correction. -/
theorem ellipsoidBoxInterpolation_primalNorm_sq_eq_combo
    (D : Matₙ) (hDdiag : D.IsDiag) (hDpos : D.PosDef) (g x : Eₙ) (α : ℝ)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    ‖x‖[⟨ellipsoidBoxInterpolationMatrix D g α,
      ellipsoidBoxInterpolationMatrix_posDef D hDpos g α hα⟩] ^ (2 : ℕ) =
      (1 - α) * ‖x‖[⟨D, hDpos⟩] ^ (2 : ℕ) +
        α * ∑ i : Fin n, ((g i) * x i) ^ (2 : ℕ) := by
  -- Rewrite both squared norms as their quadratic forms, then expand the diagonal actions.
  rw [positiveDefMatrixNorm_sq_eq_matrix_quadratic
    (ellipsoidBoxInterpolationMatrix_posDef D hDpos g α hα) x]
  rw [positiveDefMatrixNorm_sq_eq_matrix_quadratic hDpos x]
  have hdiag_eq : D = diagonal D.diag := by
    simpa using hDdiag.diagonal_diag.symm
  rw [hdiag_eq]
  rw [PiLp.inner_apply, PiLp.inner_apply]
  calc
    ∑ i : Fin n,
        inner ℝ
          (((toEuclideanLin
              (ellipsoidBoxInterpolationMatrix (diagonal D.diag) g α)) x).ofLp i)
          (x.ofLp i)
        =
          ∑ i : Fin n,
            ((1 - α) *
                inner ℝ (((toEuclideanLin (diagonal D.diag)) x).ofLp i) (x.ofLp i) +
              α * (g i * x i) ^ (2 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [ellipsoidBoxInterpolationMatrix, Matrix.toEuclideanLin_apply,
              Matrix.mulVec_diagonal, real_inner_eq_re_inner, RCLike.inner_apply]
            ring
    _ =
        (1 - α) *
            ∑ i : Fin n,
              inner ℝ (((toEuclideanLin (diagonal D.diag)) x).ofLp i) (x.ofLp i) +
          α * ∑ i : Fin n, (g i * x i) ^ (2 : ℕ) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]

/-- Helper for Lemma 7.7: on the nonnegative orthant, the interpolation primal norm is dominated
by the support of `Conv(W₁(D) ∪ B(|g|))`. -/
theorem interpolationPrimalNorm_le_generatedSupport_on_nonnegativeOrthant
    (D : Matₙ) (hDdiag : D.IsDiag) (hDpos : D.PosDef) (g : Eₙ) (α : ℝ)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) {x : Eₙ} (hx : x ∈ nonnegativeOrthant n) :
    ‖x‖[⟨ellipsoidBoxInterpolationMatrix D g α,
      ellipsoidBoxInterpolationMatrix_posDef D hDpos g α hα⟩] ≤
      (ξ[ellipsoidBoxGeneratedConvexSet D g] x).toReal :=
by
  let m : ℝ := max ‖x‖[⟨D, hDpos⟩] (inner ℝ (coordwiseAbs g) x)
  have hx_abs : coordwiseAbs x = x :=
    coordwiseAbs_eq_self_of_mem_nonnegativeOrthant hx
  have hbox_nonneg : 0 ≤ inner ℝ (coordwiseAbs g) x := by
    -- On the nonnegative orthant each coordinate contribution to the box support is nonnegative.
    rw [PiLp.inner_apply]
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg (hx i) (abs_nonneg (g i))
  have hm_nonneg : 0 ≤ m := by
    dsimp [m]
    have hnorm_nonneg : 0 ≤ ‖x‖[⟨D, hDpos⟩] := by positivity
    exact le_trans hnorm_nonneg (le_max_left _ _)
  have hsupport :
      (ξ[ellipsoidBoxGeneratedConvexSet D g] x).toReal = m := by
    -- On the orthant the support formula simplifies because `coordwiseAbs x = x`.
    dsimp [m]
    rw [supportFunction_ellipsoidBoxGeneratedConvexSet_toReal_eq_max D hDpos g x]
    simpa [hx_abs]
  have hbase_le_m : ‖x‖[⟨D, hDpos⟩] ≤ m := by
    exact le_max_left _ _
  have hsq_base : ‖x‖[⟨D, hDpos⟩] ^ (2 : ℕ) ≤ m ^ (2 : ℕ) := by
    have hnorm_nonneg : 0 ≤ ‖x‖[⟨D, hDpos⟩] := by positivity
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg hnorm_nonneg, abs_of_nonneg hm_nonneg] using hbase_le_m
  have hbox_le_m : inner ℝ (coordwiseAbs g) x ≤ m := by
    exact le_max_right _ _
  have hsq_box :
      (inner ℝ (coordwiseAbs g) x) ^ (2 : ℕ) ≤ m ^ (2 : ℕ) := by
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg hbox_nonneg, abs_of_nonneg hm_nonneg] using hbox_le_m
  have hcoord_nonneg :
      ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ coordwiseAbs g i * x i := by
    intro i hi
    exact mul_nonneg (abs_nonneg (g i)) (hx i)
  have hcoord_sq :
      ∑ i : Fin n, (g i * x i) ^ (2 : ℕ) ≤ (inner ℝ (coordwiseAbs g) x) ^ (2 : ℕ) := by
    have hterm_eq :
        ∑ i : Fin n, (g i * x i) ^ (2 : ℕ) =
          ∑ i : Fin n, (coordwiseAbs g i * x i) ^ (2 : ℕ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      calc
        (g i * x i) ^ (2 : ℕ) = (g i) ^ (2 : ℕ) * (x i) ^ (2 : ℕ) := by ring
        _ = (|g i|) ^ (2 : ℕ) * (x i) ^ (2 : ℕ) := by rw [sq_abs]
        _ = (x i) ^ (2 : ℕ) * (|g i|) ^ (2 : ℕ) := by ring
        _ = (x i) ^ (2 : ℕ) * (coordwiseAbs g i) ^ (2 : ℕ) := by
              simp [coordwiseAbs]
        _ = (coordwiseAbs g i * x i) ^ (2 : ℕ) := by ring
    have hinner_eq :
        ∑ i : Fin n, coordwiseAbs g i * x i = inner ℝ (coordwiseAbs g) x := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [coordwiseAbs, real_inner_eq_re_inner, RCLike.inner_apply, mul_comm]
    calc
      ∑ i : Fin n, (g i * x i) ^ (2 : ℕ)
          = ∑ i : Fin n, (coordwiseAbs g i * x i) ^ (2 : ℕ) := hterm_eq
      _ ≤ (∑ i : Fin n, coordwiseAbs g i * x i) ^ (2 : ℕ) := by
            simpa using
              (Finset.sum_sq_le_sq_sum_of_nonneg
                (s := Finset.univ) (f := fun i : Fin n ↦ coordwiseAbs g i * x i) hcoord_nonneg)
      _ = (inner ℝ (coordwiseAbs g) x) ^ (2 : ℕ) := by
            rw [hinner_eq]
  have hα_nonneg : 0 ≤ α := hα.1
  have hone_sub_nonneg : 0 ≤ 1 - α := by
    linarith [hα.2]
  have hsq :
      ‖x‖[⟨ellipsoidBoxInterpolationMatrix D g α,
        ellipsoidBoxInterpolationMatrix_posDef D hDpos g α hα⟩] ^ (2 : ℕ) ≤
        m ^ (2 : ℕ) := by
    -- Bound the two pieces of the quadratic decomposition by the same orthant support maximum.
    calc
      ‖x‖[⟨ellipsoidBoxInterpolationMatrix D g α,
        ellipsoidBoxInterpolationMatrix_posDef D hDpos g α hα⟩] ^ (2 : ℕ)
          = (1 - α) * ‖x‖[⟨D, hDpos⟩] ^ (2 : ℕ) +
              α * ∑ i : Fin n, (g i * x i) ^ (2 : ℕ) := by
                simpa using
                  ellipsoidBoxInterpolation_primalNorm_sq_eq_combo
                    D hDdiag hDpos g x α hα
      _ ≤ (1 - α) * m ^ (2 : ℕ) + α * m ^ (2 : ℕ) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hsq_base hone_sub_nonneg)
              (mul_le_mul_of_nonneg_left (le_trans hcoord_sq hsq_box) hα_nonneg)
      _ = m ^ (2 : ℕ) := by ring
  -- Compare squares and then replace the auxiliary maximum by the support value itself.
  have hle_m :
      ‖x‖[⟨ellipsoidBoxInterpolationMatrix D g α,
        ellipsoidBoxInterpolationMatrix_posDef D hDpos g α hα⟩] ≤ m :=
    le_of_sq_le_sq hsq hm_nonneg
  rw [hsupport]
  exact hle_m

/-- Helper for Lemma 7.7: the convex join of two compact subsets of `Eₙ` is compact. -/
private lemma convexJoin_isCompact_of_compact
    {s t : Set Eₙ} (hs : IsCompact s) (ht : IsCompact t) :
    IsCompact (convexJoin ℝ s t) := by
  let f : ℝ × (Eₙ × Eₙ) → Eₙ := fun p ↦ (1 - p.1) • p.2.1 + p.1 • p.2.2
  -- Route correction: realize the convex join as a continuous image of the compact parameter box.
  have hf : Continuous f := by
    refine ((continuous_const.sub continuous_fst).smul continuous_snd.fst).add ?_
    exact continuous_fst.smul continuous_snd.snd
  have himage :
      convexJoin ℝ s t = f '' (Set.Icc (0 : ℝ) 1 ×ˢ (s ×ˢ t)) := by
    ext z
    constructor
    · intro hz
      rcases mem_convexJoin.mp hz with ⟨x, hx, y, hy, hseg⟩
      rw [segment_eq_image] at hseg
      rcases hseg with ⟨θ, hθ, hzθ⟩
      refine ⟨⟨θ, (x, y)⟩, ?_, ?_⟩
      · exact ⟨hθ, hx, hy⟩
      · simpa [f] using hzθ
    · rintro ⟨⟨θ, x, y⟩, hmem, rfl⟩
      rcases hmem with ⟨hθ, hx, hy⟩
      refine mem_convexJoin.mpr ⟨x, hx, y, hy, ?_⟩
      rw [segment_eq_image]
      exact ⟨θ, hθ, by simp [f]⟩
  -- Compactness follows from compactness of the interval and the two factors.
  rw [himage]
  exact (isCompact_Icc.prod (hs.prod ht)).image hf

/-- Helper for Lemma 7.7: centered positive-definite ellipsoids are compact. -/
private lemma centeredMatrixEllipsoid_isCompact_of_posDef
    (D : Matₙ) (hDpos : D.PosDef) :
    IsCompact (W[1](D) : Set Eₙ) := by
  have hclosed : IsClosed (E(D, (0 : Eₙ)) : Set Eₙ) := by
    -- The defining quadratic form is continuous, so the unit sublevel set is closed.
    refine isClosed_le ?_ continuous_const
    have hlin :
        Continuous fun x : Eₙ ↦ (D⁻¹).toEuclideanLin (x - (0 : Eₙ)) :=
      (LinearMap.continuous_of_finiteDimensional ((D⁻¹).toEuclideanLin)).comp
        (continuous_id.sub continuous_const)
    have hsub : Continuous fun x : Eₙ ↦ x - (0 : Eₙ) :=
      continuous_id.sub continuous_const
    simpa [affineEllipsoid] using hlin.inner hsub
  have hcompactAffine : IsCompact (E(D, (0 : Eₙ)) : Set Eₙ) :=
    Metric.isCompact_of_isClosed_isBounded hclosed
      (affineEllipsoid_bounded D (0 : Eₙ) hDpos)
  simpa [centeredMatrixEllipsoid_one_eq_affineEllipsoid] using hcompactAffine

/-- Helper for Lemma 7.7: symmetric boxes are convex. -/
private lemma symmetricBox_abs_convex (g : Eₙ) :
    Convex ℝ (B(|g|) : Set Eₙ) := by
  intro x hx y hy a b ha hb hab
  rw [mem_symmetricBox_iff_abs_le] at hx hy ⊢
  intro i
  -- Each coordinate stays within the same absolute-value bound under convex combinations.
  calc
    |(a • x + b • y : Eₙ) i|
        = |a * x i + b * y i| := by simp [Pi.smul_apply]
    _ ≤ |a * x i| + |b * y i| := by simpa using abs_add_le (a * x i) (b * y i)
    _ = a * |x i| + b * |y i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * |g i| + b * |g i| := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hx i) ha)
            (mul_le_mul_of_nonneg_left (hy i) hb)
    _ = |g i| := by
          rw [← add_mul, hab, one_mul]

/-- Helper for Lemma 7.7: the symmetric box `B(|g|)` is compact as a finite product of compact
intervals. -/
private lemma symmetricBox_abs_isCompact (g : Eₙ) :
    IsCompact (B(|g|) : Set Eₙ) := by
  let boxSet : Set (Fin n → ℝ) :=
    Set.univ.pi fun i : Fin n ↦ Set.Icc (-(|g i|)) (|g i|)
  have hbox :
      (B(|g|) : Set Eₙ) = WithLp.toLp 2 '' boxSet := by
    ext x
    constructor
    · intro hx
      refine ⟨x.ofLp, ?_, ?_⟩
      · intro i hi
        simpa [boxSet, Set.mem_Icc] using (mem_symmetricBox_iff.mp hx i)
      · simpa using (WithLp.toLp_ofLp (p := (2 : ENNReal)) x)
    · rintro ⟨u, hu, rfl⟩
      rw [mem_symmetricBox_iff_abs_le]
      intro i
      have hui := hu i (by simp)
      simpa [boxSet, Set.mem_Icc, abs_le] using hui
  rw [hbox]
  exact (isCompact_univ_pi fun _ ↦ isCompact_Icc).image (PiLp.continuous_toLp 2 _)

/-- Helper for Lemma 7.7: the generated convex set `Conv(W₁(D) ∪ B(|g|))` is compact. -/
private lemma ellipsoidBoxGeneratedConvexSet_isCompact
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) :
    IsCompact (ellipsoidBoxGeneratedConvexSet D g) := by
  have hEllipsoidCompact : IsCompact (W[1](D) : Set Eₙ) :=
    centeredMatrixEllipsoid_isCompact_of_posDef D hDpos
  have hEllipsoidConvex : Convex ℝ (W[1](D) : Set Eₙ) := by
    let p : Seminorm ℝ Eₙ := positiveDefMatrixNorm D⁻¹ hDpos.inv
    have hclosedBall : p.closedBall (0 : Eₙ) 1 = (W[1](D) : Set Eₙ) := by
      ext x
      rw [Seminorm.mem_closedBall_zero, mem_centeredMatrixEllipsoid_iff]
      rw [show p x = Real.sqrt (inner ℝ ((Matrix.toEuclideanLin D⁻¹) x) x) by
        simpa [p] using positiveDefMatrixNorm_def ⟨D⁻¹, hDpos.inv⟩ x]
    exact hclosedBall.symm ▸ p.convex_closedBall (0 : Eₙ) 1
  have hEllipsoidNonempty : (W[1](D) : Set Eₙ).Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hDpos]
    rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
    simp
  have hBoxCompact : IsCompact (B(|g|) : Set Eₙ) := symmetricBox_abs_isCompact g
  have hBoxConvex : Convex ℝ (B(|g|) : Set Eₙ) := symmetricBox_abs_convex g
  have hBoxNonempty : (B(|g|) : Set Eₙ).Nonempty := by
    refine ⟨0, ?_⟩
    rw [mem_symmetricBox_iff_abs_le]
    intro i
    simp
  -- Route correction: package the generator hull as a convex join of two compact convex pieces.
  rw [ellipsoidBoxGeneratedConvexSet_def,
    convexHull_union hEllipsoidNonempty hBoxNonempty, hEllipsoidConvex.convexHull_eq,
    hBoxConvex.convexHull_eq]
  exact convexJoin_isCompact_of_compact hEllipsoidCompact hBoxCompact

/-- Helper for Lemma 7.7: the interpolation matrix is diagonal. -/
private lemma ellipsoidBoxInterpolationMatrix_isDiag
    (D : Matₙ) (g : Eₙ) (α : ℝ) :
    (ellipsoidBoxInterpolationMatrix D g α).IsDiag := by
  intro i j hij
  simp [ellipsoidBoxInterpolationMatrix, hij]

/-- Helper for Lemma 7.7: the orthant support estimate extends to every direction by replacing the
direction with its coordinatewise absolute value. -/
private lemma interpolationPrimalNorm_le_generatedSupport
    (D : Matₙ) (hDdiag : D.IsDiag) (hDpos : D.PosDef) (g : Eₙ) (α : ℝ)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) (x : Eₙ) :
    ‖x‖[⟨ellipsoidBoxInterpolationMatrix D g α,
      ellipsoidBoxInterpolationMatrix_posDef D hDpos g α hα⟩] ≤
      (ξ[ellipsoidBoxGeneratedConvexSet D g] x).toReal := by
  let Gα : {G : Matₙ // G.PosDef} :=
    ⟨ellipsoidBoxInterpolationMatrix D g α,
      ellipsoidBoxInterpolationMatrix_posDef D hDpos g α hα⟩
  have hGdiag : (ellipsoidBoxInterpolationMatrix D g α).IsDiag :=
    ellipsoidBoxInterpolationMatrix_isDiag D g α
  have hnorm_abs :
      ‖coordwiseAbs x‖[Gα] = ‖x‖[Gα] := by
    simpa [Gα] using
      positiveDefMatrixNorm_coordwiseAbs_eq_of_isDiag hGdiag
        (ellipsoidBoxInterpolationMatrix_posDef D hDpos g α hα) x
  have hsupport_abs :
      (ξ[ellipsoidBoxGeneratedConvexSet D g] (coordwiseAbs x)).toReal =
        (ξ[ellipsoidBoxGeneratedConvexSet D g] x).toReal := by
    -- The owner-level support formula already depends only on coordinatewise absolute values.
    rw [supportFunction_ellipsoidBoxGeneratedConvexSet_toReal_eq_max D hDpos g (coordwiseAbs x),
      supportFunction_ellipsoidBoxGeneratedConvexSet_toReal_eq_max D hDpos g x]
    have hbase_abs :
        ‖coordwiseAbs x‖[⟨D, hDpos⟩] = ‖x‖[⟨D, hDpos⟩] :=
      positiveDefMatrixNorm_coordwiseAbs_eq_of_isDiag hDdiag hDpos x
    rw [hbase_abs]
    simp [coordwiseAbs]
  have horth :
      ‖coordwiseAbs x‖[Gα] ≤
        (ξ[ellipsoidBoxGeneratedConvexSet D g] (coordwiseAbs x)).toReal :=
    interpolationPrimalNorm_le_generatedSupport_on_nonnegativeOrthant
      D hDdiag hDpos g α hα (coordwiseAbs_mem_nonnegativeOrthant x)
  -- Transfer the orthant estimate back to the original direction.
  calc
    ‖x‖[Gα] = ‖coordwiseAbs x‖[Gα] := hnorm_abs.symm
    _ ≤ (ξ[ellipsoidBoxGeneratedConvexSet D g] (coordwiseAbs x)).toReal := horth
    _ = (ξ[ellipsoidBoxGeneratedConvexSet D g] x).toReal := hsupport_abs

-- Proof sketch: in the source's diagonal positive-definite regime, compare the Minkowski
-- functional of the centered ellipsoid with shape matrix `(1 - α) D + α D²(g)` to the support
-- function of `Conv(W₁(D) ∪ B(|g|))`, using the coordinatewise bound
-- `(∑ i (g i * |x i|)^2) ≤ (∑ i g i * |x i|)^2`.
/-- Helper for Lemma 7.7 (1): on the open part of the interval, the unit ellipsoid with
interpolation matrix `G(α) = (1 - α) D + α D²(g)` is contained in
`C = Conv(W₁(D) ∪ B(|g|))`. -/
theorem centeredMatrixEllipsoid_halfOpenInterpolation_subset_ellipsoidBoxGeneratedConvexSet
    (D : Matₙ) (hDdiag : D.IsDiag) (hDpos : D.PosDef) (g : Eₙ) (α : ℝ)
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    W[1]((ellipsoidBoxInterpolationMatrix D g α)) ⊆
      ellipsoidBoxGeneratedConvexSet D g := by
  have hC_nonempty : (ellipsoidBoxGeneratedConvexSet D g).Nonempty := by
    refine ⟨0, ?_⟩
    rw [ellipsoidBoxGeneratedConvexSet_def]
    exact subset_convexHull ℝ _ (Or.inl <| by
      rw [mem_centeredMatrixEllipsoid_iff_dualNorm_le hDpos]
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
      simp)
  have hC_closed : IsClosed (ellipsoidBoxGeneratedConvexSet D g) :=
    (ellipsoidBoxGeneratedConvexSet_isCompact D hDpos g).isClosed
  have hC_convex : Convex ℝ (ellipsoidBoxGeneratedConvexSet D g) := by
    simpa [ellipsoidBoxGeneratedConvexSet_def] using
      (convex_convexHull ℝ (W[1](D) ∪ B(|g|)))
  let Gα : {G : Matₙ // G.PosDef} :=
    ⟨ellipsoidBoxInterpolationMatrix D g α,
      ellipsoidBoxInterpolationMatrix_posDef D hDpos g α hα⟩
  -- Route correction: once the arbitrary-direction support bound is available, the inclusion is
  -- the standard support-function wrapper from Theorem 3.17.
  refine subset_of_supportFunction_le_on_domain
    (centeredMatrixEllipsoid (ellipsoidBoxInterpolationMatrix D g α) 1)
    (ellipsoidBoxGeneratedConvexSet D g) hC_nonempty hC_closed hC_convex ?_
  intro x hxdom
  rw [supportFunction_centeredMatrixEllipsoid_eq_coe_primalNorm
    (ellipsoidBoxInterpolationMatrix D g α)
    (ellipsoidBoxInterpolationMatrix_posDef D hDpos g α hα)]
  change (((‖x‖[Gα] : ℝ) : EReal) ≤ ξ[ellipsoidBoxGeneratedConvexSet D g] x)
  rw [mem_extendedRealEffectiveDomain_iff] at hxdom
  rw [← EReal.coe_toReal hxdom.1 hxdom.2]
  exact_mod_cast interpolationPrimalNorm_le_generatedSupport D hDdiag hDpos g α hα x

/-- Helper for Lemma 7.7 (1): the symmetric box `B(|g|)` is contained in the generated convex set
`C = Conv(W₁(D) ∪ B(|g|))`. -/
theorem symmetricBox_subset_ellipsoidBoxGeneratedConvexSet
    (D : Matₙ) (g : Eₙ) :
    B(|g|) ⊆ ellipsoidBoxGeneratedConvexSet D g := by
  -- The box is one of the generators of the defining convex hull.
  rw [ellipsoidBoxGeneratedConvexSet_def]
  intro x hx
  exact subset_convexHull ℝ (W[1](D) ∪ B(|g|)) (Or.inr hx)

/-- First conclusion of Lemma 7.7: for every `α ∈ [0, 1]`, the interpolation ellipsoid
`W₁(G(α))` is contained
in `C = Conv(W₁(D) ∪ B(|g|))`, with the source boundary `α = 1` interpreted as the degenerate
box `B(|g|)`. -/
theorem centeredMatrixEllipsoid_closedInterpolation_subset_ellipsoidBoxGeneratedConvexSet
    (D : Matₙ) (hDdiag : D.IsDiag) (hDpos : D.PosDef) (g : Eₙ) (α : ℝ)
    (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    ellipsoidBoxClosedInterpolationSection D g α ⊆
      ellipsoidBoxGeneratedConvexSet D g := by
  -- Split the closed interval into the degenerate endpoint `α = 1` and the open branch.
  by_cases hα_one : α = 1
  · rw [hα_one, ellipsoidBoxClosedInterpolationSection_one]
    exact symmetricBox_subset_ellipsoidBoxGeneratedConvexSet D g
  · rw [ellipsoidBoxClosedInterpolationSection_eq_centeredMatrixEllipsoid D g hα_one]
    refine centeredMatrixEllipsoid_halfOpenInterpolation_subset_ellipsoidBoxGeneratedConvexSet
      D hDdiag hDpos g α ?_
    exact ⟨hα.1, lt_of_le_of_ne hα.2 hα_one⟩

-- Proof sketch: write `S = ‖g‖[d.toPositiveDefMatrix,*]^2`; the hypothesis `S > n` gives
-- positivity of the numerator, and the algebraic inequality
-- `ellipsoidBoxAlphaStar d g ≤ 1 / n` reduces to `0 ≤ 2 S^2 - n S + n^2`.
/-- Second conclusion of Lemma 7.7: if `S = ‖g‖*_D² > n`, then the critical value
`α* = (S - n) / ((2 S - n) S)` lies in the interval `(0, 1 / n]`. -/
theorem ellipsoidBoxAlphaStar_mem_Ioc_inv_dim
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ)
    (hS : (n : ℝ) < ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)) :
    ellipsoidBoxAlphaStar D hDpos g ∈ Set.Ioc (0 : ℝ) (1 / (n : ℝ)) := by
  let S : ℝ := ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)
  have hSgt : (n : ℝ) < S := hS
  by_cases hn_zero : n = 0
  · have hg_zero : g = 0 := by
      ext i
      have : False := by
        simpa [hn_zero] using i.2
      exact False.elim this
    have hnormsq_zero : S = 0 := by
      dsimp [S]
      -- The zero vector has zero weighted dual norm, so its squared norm is also zero.
      have hdual_zero : ‖(0 : Eₙ)‖[⟨D, hDpos⟩,*] = 0 := by
        rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
        simp
      simpa [hg_zero, hdual_zero]
    have : ¬ ((n : ℝ) < S) := by
      simpa [hn_zero, hnormsq_zero]
    exact False.elim (this hSgt)
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero hn_zero
  have hSpos : 0 < S := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    linarith
  have htwoS_sub_pos : 0 < (2 : ℝ) * S - (n : ℝ) := by
    nlinarith
  have hden_pos : 0 < (((2 : ℝ) * S - (n : ℝ)) * S) := by
    exact mul_pos htwoS_sub_pos hSpos
  constructor
  · -- The source hypothesis `S > n` makes both numerator and denominator positive.
    rw [ellipsoidBoxAlphaStar_eq]
    exact div_pos (sub_pos.mpr hSgt) hden_pos
  · -- After clearing the positive denominators, the bound is a quadratic inequality in `S`.
    have hquadratic_nonneg :
        0 ≤ 2 * S ^ (2 : ℕ) - 2 * (n : ℝ) * S + (n : ℝ) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (S - (n : ℝ)), sq_nonneg S]
    have hcross :
        (S - (n : ℝ)) * (n : ℝ) ≤ 1 * (((2 : ℝ) * S - (n : ℝ)) * S) := by
      nlinarith
    have hle :
        (S - (n : ℝ)) / (((2 : ℝ) * S - (n : ℝ)) * S) ≤ 1 / (n : ℝ) := by
      exact (div_le_div_iff₀ hden_pos hn_pos).2 hcross
    simpa [ellipsoidBoxAlphaStar_eq, S] using hle

/-- Helper for Lemma 7.7: if each factor is `m + v i` with `m, v i ≥ 0`, then the full product
dominates the extreme-profile lower bound `m ^ card + m ^ (card - 1) * ∑ v i`. -/
private lemma addPowMulSum_le_prod_add
    {ι : Type*} (s : Finset ι) {m : ℝ} (hm : 0 < m) {v : ι → ℝ}
    (hv : ∀ i ∈ s, 0 ≤ v i) :
    m ^ s.card + m ^ (s.card - 1) * Finset.sum s v ≤
      Finset.prod s (fun i ↦ m + v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha hs =>
      have hva : 0 ≤ v a := hv a (Finset.mem_insert_self a s)
      have hvs : ∀ i ∈ s, 0 ≤ v i := by
        intro i hi
        exact hv i (Finset.mem_insert_of_mem hi)
      have hsum_nonneg : 0 ≤ Finset.sum s v := by
        exact Finset.sum_nonneg hvs
      have hm_pow_nonneg : 0 ≤ m ^ (s.card - 1) := by
        exact pow_nonneg hm.le _
      have hm_pow_le :
          m ^ s.card ≤ Finset.prod s (fun i ↦ m + v i) := by
        have hle_aux :
            m ^ s.card ≤
              m ^ s.card + m ^ (s.card - 1) * Finset.sum s v := by
          nlinarith
        exact le_trans hle_aux (hs hvs)
      have hsplit :
          m ^ (s.card + 1) + m ^ ((s.card + 1) - 1) * Finset.sum (insert a s) v =
            m * (m ^ s.card + m ^ (s.card - 1) * Finset.sum s v) + v a * m ^ s.card := by
        rw [Finset.sum_insert ha]
        by_cases hs0 : s.card = 0
        · have hs_eq : s = ∅ := Finset.card_eq_zero.mp hs0
          subst hs_eq
          simp
        · have hspos : 0 < s.card := Nat.pos_of_ne_zero hs0
          have hmcard :
              m ^ s.card = m * m ^ (s.card - 1) := by
            calc
              m ^ s.card = m ^ ((s.card - 1) + 1) := by
                  congr
                  exact (Nat.sub_add_cancel (Nat.succ_le_of_lt hspos)).symm
              _ = m * m ^ (s.card - 1) := by rw [pow_succ']
          have hmcard' :
              m ^ s.card * Finset.sum s v = m * (m ^ (s.card - 1) * Finset.sum s v) := by
            rw [hmcard]
            ring
          rw [Nat.add_sub_cancel]
          calc
            m ^ (s.card + 1) + m ^ s.card * (v a + Finset.sum s v)
                = m * m ^ s.card + m ^ s.card * v a + m ^ s.card * Finset.sum s v := by
                    rw [pow_succ]
                    ring
            _ = m * m ^ s.card + m ^ s.card * v a + m * (m ^ (s.card - 1) * Finset.sum s v) := by
                  rw [hmcard']
            _ = m * (m ^ s.card + m ^ (s.card - 1) * Finset.sum s v) + v a * m ^ s.card := by
                  ring
      have hstep1 :
          m ^ (s.card + 1) + m ^ ((s.card + 1) - 1) * Finset.sum (insert a s) v
            ≤ m * Finset.prod s (fun i ↦ m + v i) + v a * m ^ s.card := by
        rw [hsplit]
        exact add_le_add (mul_le_mul_of_nonneg_left (hs hvs) hm.le) le_rfl
      have hstep2 :
          m * Finset.prod s (fun i ↦ m + v i) + v a * m ^ s.card
            ≤ m * Finset.prod s (fun i ↦ m + v i) + v a * Finset.prod s (fun i ↦ m + v i) := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hm_pow_le hva) _
      have hstep3 :
          m * Finset.prod s (fun i ↦ m + v i) + v a * Finset.prod s (fun i ↦ m + v i) =
            Finset.prod (insert a s) (fun i ↦ m + v i) := by
        simp [Finset.prod_insert, ha]
        ring
      have hcard : (insert a s).card = s.card + 1 := by
        simp [ha]
      simpa [hcard] using
        (le_trans hstep1 <| le_trans hstep2 <| le_of_eq hstep3)

/-- Helper for Lemma 7.7: each coordinate ratio `(g i)^2 / Dᵢᵢ` is nonnegative. -/
private lemma ellipsoidBoxCoordinateRatio_nonneg
    (D : Matₙ) (hDpos : D.PosDef) (g : Eₙ) (i : Fin n) :
    0 ≤ ellipsoidBoxCoordinateRatio D g i := by
  rw [ellipsoidBoxCoordinateRatio]
  exact div_nonneg (sq_nonneg _) hDpos.diag_pos.le

/-- Helper for Lemma 7.7: for diagonal `D`, the squared dual norm is the sum of the coordinate
ratios. -/
private lemma dualNormSq_eq_sum_coordinateRatio
    (D : Matₙ) (hDdiag : D.IsDiag) (hDpos : D.PosDef) (g : Eₙ) :
    ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ) = ∑ i : Fin n, ellipsoidBoxCoordinateRatio D g i := by
  have hdiag_eq : D = diagonal D.diag := by
    simpa using hDdiag.diagonal_diag.symm
  have hinner_nonneg : 0 ≤ inner ℝ ((D⁻¹).toEuclideanLin g) g := by
    have hPosLin : (D⁻¹).toEuclideanLin.IsPositive :=
      Matrix.isPositive_toEuclideanLin_iff.mpr hDpos.inv.posSemidef
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right g
  have hinner_nonneg' : 0 ≤ inner ℝ g ((D⁻¹).toEuclideanLin g) := by
    simpa [real_inner_comm] using hinner_nonneg
  rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv, Real.sq_sqrt hinner_nonneg']
  rw [hdiag_eq, Matrix.inv_diagonal, PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hDii_ne : D i i ≠ 0 := hDpos.diag_pos.ne'
  have hdiag_inv :
      Ring.inverse D.diag i = (D i i)⁻¹ := by
    have hunit_diag : IsUnit D.diag := by
      refine Pi.isUnit_iff.mpr ?_
      intro j
      exact isUnit_iff_ne_zero.mpr (ne_of_gt (hDpos.diag_pos (i := j)))
    rw [Ring.inverse, dif_pos hunit_diag]
    simpa using hunit_diag.val_inv_apply i
  simp [Matrix.toEuclideanLin_apply, Matrix.mulVec_diagonal, real_inner_eq_re_inner,
    RCLike.inner_apply, hdiag_inv, ellipsoidBoxCoordinateRatio, div_eq_mul_inv]
  field_simp [hDii_ne]

/-- Helper for Lemma 7.7: the singular logarithmic term is controlled by `α / (1 - α)` on
`[0, 1)`. -/
private lemma negLogOneSub_le_div_of_mem_Ico'
    {α : ℝ} (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    -Real.log (1 - α) ≤ α / (1 - α) := by
  have hone_sub_pos : 0 < 1 - α := by
    linarith [hα.2]
  have hlog_aux :
      -Real.log (1 - α) ≤ (1 - α)⁻¹ - 1 := by
    -- Rewrite through `log ((1 - α)⁻¹)` so that the basic logarithmic bound applies.
    simpa [Real.log_inv] using
      (Real.log_le_sub_one_of_pos (x := (1 - α)⁻¹) (inv_pos.mpr hone_sub_pos))
  have hrewrite : (1 - α)⁻¹ - 1 = α / (1 - α) := by
    field_simp [hone_sub_pos.ne']
    ring
  rwa [hrewrite] at hlog_aux

/-- Helper for Lemma 7.7: the map `u ↦ log (1 + u) - u` is antitone on `u ≥ 0`. -/
private lemma logOneAdd_sub_self_antitone
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    Real.log (1 + v) - v ≤ Real.log (1 + u) - u := by
  have huv_nonneg : 0 ≤ v - u := sub_nonneg.mpr huv
  have hu1_pos : 0 < 1 + u := by linarith
  have hv1_pos : 0 < 1 + v := by linarith
  have hratio_pos : 0 < (1 + v) / (1 + u) := div_pos hv1_pos hu1_pos
  have hratio_le :
      Real.log ((1 + v) / (1 + u)) ≤ (v - u) / (1 + u) := by
    have hlog := Real.log_le_sub_one_of_pos hratio_pos
    have hratio_eq :
        (1 + v) / (1 + u) - 1 = (v - u) / (1 + u) := by
      field_simp [hu1_pos.ne']
      ring
    simpa [hratio_eq] using hlog
  have hratio_simple : (v - u) / (1 + u) ≤ v - u := by
    have hden_ge_one : 1 ≤ 1 + u := by linarith
    exact (div_le_self huv_nonneg hden_ge_one)
  have hlog_diff :
      Real.log (1 + v) - Real.log (1 + u) ≤ v - u := by
    rw [← Real.log_div hv1_pos.ne' hu1_pos.ne']
    exact le_trans hratio_le hratio_simple
  linarith

/-- Helper for Lemma 7.7: the rational correction terms at `α*` are dominated by the same
correction terms written in the scalar variable `uS = (S - n) / S`. -/
private lemma alphaStarRationalComparison_le_uS
    {S αStar uS : ℝ} (hn_pos : 0 < n) (hSgt : (n : ℝ) < S)
    (hα_eq :
      αStar =
        (S - (n : ℝ)) / ((((2 : ℝ) * S) - (n : ℝ)) * S))
    (huS_eq : uS = (S - (n : ℝ)) / S) :
    ((n : ℝ) - 1) * (αStar / (1 - αStar)) -
        (2 * (αStar * (S - 1)) / (2 + αStar * (S - 1))) ≤
      -uS + 2 * uS / (uS + 2) := by
  -- Normalize both scalar parameters to explicit formulas in `S` before clearing denominators.
  have hn_real_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos
  have hSpos : 0 < S := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    linarith
  let t : ℝ := S - (n : ℝ)
  have ht_pos : 0 < t := by
    dsimp [t]
    linarith
  have hone_le : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.succ_le_of_lt hn_pos
  have hS_eq : S = (n : ℝ) + t := by
    dsimp [t]
    linarith
  have hden₁ : 0 < (n : ℝ) + t := by
    linarith
  have hden₂ : 0 < 2 * (n : ℝ) + 3 * t := by
    nlinarith
  have hnp2t_pos : 0 < (n : ℝ) + 2 * t := by
    nlinarith
  let A : ℝ := (n : ℝ) ^ (2 : ℕ) + 3 * (n : ℝ) * t + 2 * t ^ (2 : ℕ) - t
  let B : ℝ := 2 * (n : ℝ) ^ (2 : ℕ) + 7 * (n : ℝ) * t + 5 * t ^ (2 : ℕ) - t
  have hApos : 0 < A := by
    dsimp [A]
    nlinarith
  have hBpos : 0 < B := by
    dsimp [B]
    nlinarith
  subst αStar
  subst uS
  have hα_closed :
      (S - (n : ℝ)) / ((((2 : ℝ) * S) - (n : ℝ)) * S) =
        t / (((n : ℝ) + 2 * t) * ((n : ℝ) + t)) := by
    rw [hS_eq]
    field_simp [hden₁.ne', hnp2t_pos.ne']
    have hden_eq : ((n : ℝ) + t) * 2 - (n : ℝ) = (n : ℝ) + t * 2 := by
      ring
    have hnp2t_pos' : 0 < (n : ℝ) + t * 2 := by
      nlinarith
    have hnum_eq :
        ((n : ℝ) + t - (n : ℝ)) * ((n : ℝ) + t * 2) =
          t * ((n : ℝ) + t * 2) := by
      ring
    rw [hden_eq, hnum_eq, mul_div_assoc, div_self hnp2t_pos'.ne', mul_one]
  have hu_closed :
      (S - (n : ℝ)) / S = t / ((n : ℝ) + t) := by
    rw [hS_eq]
    field_simp [hden₁.ne']
    ring_nf
  rw [hα_closed, hu_closed]
  rw [hS_eq]
  have hαratio :
      (t / (((n : ℝ) + 2 * t) * ((n : ℝ) + t))) /
          (1 - t / (((n : ℝ) + 2 * t) * ((n : ℝ) + t))) =
        t / A := by
    have hA_den :
        ((n : ℝ) + t * 2) * ((n : ℝ) + t) - t = A := by
      dsimp [A]
      ring
    field_simp [hden₁.ne', hnp2t_pos.ne', hApos.ne']
    rw [hA_den]
    exact div_self hApos.ne'
  have hsecond :
      2 *
            ((t / (((n : ℝ) + 2 * t) * ((n : ℝ) + t))) *
              (((n : ℝ) + t) - 1)) /
          (2 + (t / (((n : ℝ) + 2 * t) * ((n : ℝ) + t))) * (((n : ℝ) + t) - 1)) =
        2 * t * (((n : ℝ) + t) - 1) / B := by
    have hB_den :
        2 * ((n : ℝ) + 2 * t) * ((n : ℝ) + t) + t * (((n : ℝ) + t) - 1) = B := by
      dsimp [B]
      ring
    field_simp [hden₁.ne', hnp2t_pos.ne', hBpos.ne']
    rw [hB_den]
    rw [mul_div_assoc, div_self hBpos.ne', mul_one]
  have hu_term :
      2 * (t / ((n : ℝ) + t)) / (t / ((n : ℝ) + t) + 2) =
        2 * t / (2 * (n : ℝ) + 3 * t) := by
    field_simp [hden₁.ne', hden₂.ne']
    ring_nf
  rw [hαratio, hsecond, hu_term]
  field_simp [hden₁.ne', hden₂.ne', hApos.ne', hBpos.ne']
  let P : ℝ :=
    2 * (n : ℝ) ^ (3 : ℕ) * t + 6 * (n : ℝ) ^ (2 : ℕ) * t ^ (2 : ℕ) +
      (n : ℝ) ^ (2 : ℕ) * t + 2 * (n : ℝ) ^ (2 : ℕ) +
        6 * (n : ℝ) * t ^ (3 : ℕ) + 5 * (n : ℝ) * t ^ (2 : ℕ) +
          5 * (n : ℝ) * t + 2 * t ^ (4 : ℕ) + 4 * t ^ (3 : ℕ) + 2 * t ^ (2 : ℕ)
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    positivity
  have hbound :
      ((n : ℝ) + t) *
          (((n : ℝ) - 1) * B - A * 2 * ((n : ℝ) + t - 1)) *
        (2 * (n : ℝ) + 3 * t) ≤
        A * B * (-(2 * (n : ℝ) + 3 * t) + 2 * ((n : ℝ) + t)) := by
    have hcompare :
        ((n : ℝ) + t) *
            (((n : ℝ) - 1) * B - A * 2 * ((n : ℝ) + t - 1)) *
          (2 * (n : ℝ) + 3 * t) -
          A * B * (-(2 * (n : ℝ) + 3 * t) + 2 * ((n : ℝ) + t)) =
          -t * P := by
      dsimp [A, B, P]
      ring
    have hcompare_nonpos :
        ((n : ℝ) + t) *
            (((n : ℝ) - 1) * B - A * 2 * ((n : ℝ) + t - 1)) *
          (2 * (n : ℝ) + 3 * t) -
          A * B * (-(2 * (n : ℝ) + 3 * t) + 2 * ((n : ℝ) + t)) ≤ 0 := by
      rw [hcompare]
      have htp_nonneg : 0 ≤ t * P := mul_nonneg ht_pos.le hP_nonneg
      nlinarith
    simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hcompare_nonpos
  simpa [two_mul, mul_comm, mul_left_comm, mul_assoc] using hbound

-- Proof sketch: combine the self-concordant upper estimate for `V(α)` with the choice
-- `α = ellipsoidBoxAlphaStar d g`, rewrite the resulting scalar bound in terms of
-- `S = ‖g‖[d.toPositiveDefMatrix,*]^2`, and then use the interval hypothesis
-- `1 < γ ≤ ‖g‖[d.toPositiveDefMatrix,*] / √n` under the source hypothesis `S > n`. This yields
-- the comparison with
-- `log (1 + (γ² - 1) / γ²) - (γ² - 1) / γ²`.
/-- Helper for Lemma 7.7: if `S = ‖g‖*_D² > n` and `1 < γ ≤ ‖g‖*_D / √n`, then the logarithmic
potential at `α*` is bounded above by the scalar
comparison term `log (1 + (γ² - 1) / γ²) - (γ² - 1) / γ²`. -/
theorem ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison
    (D : Matₙ) (hDdiag : D.IsDiag) (hDpos : D.PosDef) (g : Eₙ)
    (hS : (n : ℝ) < ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)) (γ : ℝ)
    (hγ :
      γ ∈
        Set.Ioc
          (1 : ℝ)
          (‖g‖[⟨D, hDpos⟩,*] / Real.sqrt (n : ℝ))) :
    ellipsoidBoxLogVolumePotential D g (ellipsoidBoxAlphaStar D hDpos g) ≤
      Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)) -
        (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) := by
  let S : ℝ := ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)
  let αStar : ℝ := ellipsoidBoxAlphaStar D hDpos g
  let uS : ℝ := (S - (n : ℝ)) / S
  have hSgt : (n : ℝ) < S := hS
  have hSpos : 0 < S := by
    have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
    linarith
  have hn_pos : 0 < n := by
    by_contra hn_pos
    have hn_zero : n = 0 := Nat.eq_zero_of_not_pos hn_pos
    have hg_zero : g = 0 := by
      ext i
      have : False := by
        simpa [hn_zero] using i.2
      exact False.elim this
    have hnorm_zero : S = 0 := by
      dsimp [S]
      have hdual_zero : ‖(0 : Eₙ)‖[⟨D, hDpos⟩,*] = 0 := by
        rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
        simp
      simpa [hg_zero, hdual_zero]
    have : ¬ ((n : ℝ) < S) := by
      simpa [hn_zero, hnorm_zero]
    exact this hSgt
  have hn_real_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn_pos
  have hαmem : αStar ∈ Set.Ico (0 : ℝ) 1 :=
    ellipsoidBoxAlphaStar_mem_halfOpenUnitInterval D hDpos g hS
  have hα_nonneg : 0 ≤ αStar := hαmem.1
  have hone_sub_pos : 0 < 1 - αStar := by
    linarith [hαmem.2]
  have hratio_sum :
      ∑ i : Fin n, ellipsoidBoxCoordinateRatio D g i = S := by
    simpa [S] using (dualNormSq_eq_sum_coordinateRatio D hDdiag hDpos g).symm
  have hprod_lower :
      (1 - αStar) ^ n +
          (1 - αStar) ^ (n - 1) *
            ∑ i : Fin n, αStar * ellipsoidBoxCoordinateRatio D g i
        ≤
          ∏ i : Fin n, (1 - αStar + αStar * ellipsoidBoxCoordinateRatio D g i) := by
    simpa using
      addPowMulSum_le_prod_add Finset.univ hone_sub_pos
        (fun i _ ↦ mul_nonneg hα_nonneg (ellipsoidBoxCoordinateRatio_nonneg D hDpos g i))
  have hsum_scaled :
      ∑ i : Fin n, αStar * ellipsoidBoxCoordinateRatio D g i = αStar * S := by
    simpa [Finset.mul_sum] using congrArg (fun t : ℝ ↦ αStar * t) hratio_sum
  have hprod_lower' :
      (1 - αStar) ^ (n - 1) * (1 + αStar * (S - 1))
        ≤
          ∏ i : Fin n, (1 + αStar * (ellipsoidBoxCoordinateRatio D g i - 1)) := by
    have hpow_step :
        (1 - αStar) ^ n = (1 - αStar) ^ (n - 1) * (1 - αStar) := by
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos) with ⟨k, rfl⟩
      simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
    calc
      (1 - αStar) ^ (n - 1) * (1 + αStar * (S - 1))
          = (1 - αStar) ^ n +
              (1 - αStar) ^ (n - 1) *
                ∑ i : Fin n, αStar * ellipsoidBoxCoordinateRatio D g i := by
                  rw [hsum_scaled, hpow_step]
                  ring
      _ ≤ ∏ i : Fin n, (1 - αStar + αStar * ellipsoidBoxCoordinateRatio D g i) := hprod_lower
      _ = ∏ i : Fin n, (1 + αStar * (ellipsoidBoxCoordinateRatio D g i - 1)) := by
            refine Finset.prod_congr rfl ?_
            intro i hi
            ring
  have harg_pos :
      0 < 1 + αStar * (S - 1) := by
    have hαS_nonneg : 0 ≤ αStar * S := mul_nonneg hα_nonneg hSpos.le
    nlinarith
  have hlog_extreme :
      (((n : ℝ) - 1) * Real.log (1 - αStar) +
          Real.log (1 + αStar * (S - 1))) ≤
        ∑ i : Fin n, Real.log (1 + αStar * (ellipsoidBoxCoordinateRatio D g i - 1)) := by
    have hpow_pos : 0 < (1 - αStar) ^ (n - 1) := pow_pos hone_sub_pos _
    have hprod_pos :
        0 < ∏ i : Fin n, (1 + αStar * (ellipsoidBoxCoordinateRatio D g i - 1)) := by
      refine Finset.prod_pos ?_
      intro i hi
      exact one_add_alpha_coordinateRatio_sub_one_pos D hDpos g αStar hαmem i
    have hlog_le :
        Real.log ((1 - αStar) ^ (n - 1) * (1 + αStar * (S - 1))) ≤
          Real.log (∏ i : Fin n, (1 + αStar * (ellipsoidBoxCoordinateRatio D g i - 1))) := by
      exact Real.log_le_log (mul_pos hpow_pos harg_pos) hprod_lower'
    have hleft :
        Real.log ((1 - αStar) ^ (n - 1) * (1 + αStar * (S - 1))) =
          (((n : ℝ) - 1) * Real.log (1 - αStar) +
            Real.log (1 + αStar * (S - 1))) := by
      have hlog_pow :
          Real.log ((1 - αStar) ^ (n - 1)) = ((n : ℝ) - 1) * Real.log (1 - αStar) := by
        rw [← Real.rpow_natCast (1 - αStar) (n - 1), Real.log_rpow hone_sub_pos]
        norm_num [Nat.cast_sub (Nat.succ_le_of_lt hn_pos)]
      rw [Real.log_mul hpow_pos.ne' harg_pos.ne']
      rw [hlog_pow]
    have hright :
        Real.log (∏ i : Fin n, (1 + αStar * (ellipsoidBoxCoordinateRatio D g i - 1))) =
          ∑ i : Fin n, Real.log (1 + αStar * (ellipsoidBoxCoordinateRatio D g i - 1)) := by
      exact Real.log_prod fun i _ ↦
        (one_add_alpha_coordinateRatio_sub_one_pos D hDpos g αStar hαmem i).ne'
    rwa [hleft, hright] at hlog_le
  have hupper_extreme :
      ellipsoidBoxLogVolumePotential D g αStar ≤
        -((((n : ℝ) - 1) * Real.log (1 - αStar)) +
          Real.log (1 + αStar * (S - 1))) := by
    rw [ellipsoidBoxLogVolumePotential_eq D hDpos g αStar hαmem]
    linarith
  have hfirst_term :
      -(((n : ℝ) - 1) * Real.log (1 - αStar)) ≤
        ((n : ℝ) - 1) * (αStar / (1 - αStar)) := by
    have hbase := negLogOneSub_le_div_of_mem_Ico' hαmem
    have hn1_nonneg : 0 ≤ (n : ℝ) - 1 := by
      have hone_le : (1 : ℝ) ≤ n := by
        exact_mod_cast Nat.succ_le_of_lt hn_pos
      linarith
    have hmul := mul_le_mul_of_nonneg_left hbase hn1_nonneg
    simpa [neg_mul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmul
  have hsecond_term :
      -Real.log (1 + αStar * (S - 1)) ≤
        -(2 * (αStar * (S - 1)) / (2 + αStar * (S - 1))) := by
    have hσ : 0 ≤ αStar * (S - 1) := by
      have hS_minus_one : 0 ≤ S - 1 := by
        have hnone_le : (1 : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hn_pos
        linarith
      exact mul_nonneg hα_nonneg hS_minus_one
    have hlog :
        2 * (αStar * (S - 1)) / (2 + αStar * (S - 1)) ≤
          Real.log (1 + αStar * (S - 1)) := by
      simpa [add_comm] using Real.le_log_one_add_of_nonneg hσ
    linarith
  have hscalar_uS :
      -((((n : ℝ) - 1) * Real.log (1 - αStar)) +
          Real.log (1 + αStar * (S - 1))) ≤
        Real.log (1 + uS) - uS := by
    have huS_nonneg : 0 ≤ uS := by
      dsimp [uS]
      exact div_nonneg (sub_nonneg.mpr hSgt.le) hSpos.le
    have hlog_uS : 2 * uS / (uS + 2) ≤ Real.log (1 + uS) :=
      Real.le_log_one_add_of_nonneg huS_nonneg
    have hrational :
        ((n : ℝ) - 1) * (αStar / (1 - αStar)) -
            (2 * (αStar * (S - 1)) / (2 + αStar * (S - 1))) ≤
          -uS + 2 * uS / (uS + 2) := by
      -- Route correction: isolate the `α*`-to-`uS` algebra before combining it with the log bound.
      have hα_eq :
          αStar =
            (S - (n : ℝ)) / ((((2 : ℝ) * S) - (n : ℝ)) * S) := by
        simpa [αStar, S] using ellipsoidBoxAlphaStar_eq D hDpos g
      have huS_eq : uS = (S - (n : ℝ)) / S := by
        rfl
      exact alphaStarRationalComparison_le_uS hn_pos hSgt hα_eq huS_eq
    linarith
  have hupper_uS :
      ellipsoidBoxLogVolumePotential D g αStar ≤ Real.log (1 + uS) - uS :=
    le_trans hupper_extreme <| le_trans (by linarith [hfirst_term, hsecond_term]) hscalar_uS
  let uγ : ℝ := (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)
  have hγ_pos : 0 < γ := lt_trans zero_lt_one hγ.1
  have huγ_nonneg : 0 ≤ uγ := by
    dsimp [uγ]
    refine div_nonneg ?_ (by positivity)
    nlinarith [hγ.1]
  have hsqrt_n_pos : 0 < Real.sqrt (n : ℝ) := by
    exact Real.sqrt_pos.2 hn_real_pos
  have hγ_sq_le : γ ^ (2 : ℕ) ≤ S / (n : ℝ) := by
    have hsq :
        γ ^ (2 : ℕ) ≤ (‖g‖[⟨D, hDpos⟩,*] / Real.sqrt (n : ℝ)) ^ (2 : ℕ) := by
      nlinarith [hγ.2]
    calc
      γ ^ (2 : ℕ) ≤ (‖g‖[⟨D, hDpos⟩,*] / Real.sqrt (n : ℝ)) ^ (2 : ℕ) := hsq
      _ = S / (n : ℝ) := by
            dsimp [S]
            rw [pow_two]
            field_simp [hsqrt_n_pos.ne']
            rw [Real.sq_sqrt hn_real_pos.le]
  have huγ_le_uS : uγ ≤ uS := by
    have hγsq_pos : 0 < γ ^ (2 : ℕ) := by positivity
    have hratio_inv : (n : ℝ) / S ≤ 1 / γ ^ (2 : ℕ) := by
      have hrecip : 1 / (S / (n : ℝ)) ≤ 1 / γ ^ (2 : ℕ) :=
        one_div_le_one_div_of_le hγsq_pos hγ_sq_le
      simpa [one_div, div_eq_mul_inv, hSpos.ne', hn_real_pos.ne', mul_comm, mul_left_comm,
        mul_assoc] using hrecip
    have huγ_eq : uγ = 1 - 1 / γ ^ (2 : ℕ) := by
      dsimp [uγ]
      field_simp [(pow_ne_zero _ (ne_of_gt hγ_pos))]
    have huS_eq : uS = 1 - (n : ℝ) / S := by
      dsimp [uS]
      field_simp [hSpos.ne']
    rw [huγ_eq, huS_eq]
    linarith
  have hmono :
      Real.log (1 + uS) - uS ≤ Real.log (1 + uγ) - uγ :=
    logOneAdd_sub_self_antitone huγ_nonneg huγ_le_uS
  -- Finish by passing from the endpoint parameter `uS` to the displayed `γ` parameter.
  exact le_trans hupper_uS <| by
    simpa [uγ] using hmono

-- Proof sketch: set `u = (γ² - 1) / γ²`; the assumption `γ > 1` gives `u > 0`, and the standard
-- inequality `log (1 + u) < u` yields the strict negativity.
/-- Helper for Lemma 7.7: for every `γ > 1`, the comparison term
`log (1 + (γ² - 1) / γ²) - (γ² - 1) / γ²` is strictly negative. -/
theorem ellipsoidBoxGammaComparison_neg
    (γ : ℝ) (hγ : 1 < γ) :
    Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)) -
        (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) < 0 := by
  let u : ℝ := (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)
  have hγ_pos : 0 < γ := by
    linarith
  have hγsq_pos : 0 < γ ^ (2 : ℕ) := by
    positivity
  have hu_pos : 0 < u := by
    -- The comparison parameter is positive once `γ > 1`.
    dsimp [u]
    refine div_pos ?_ hγsq_pos
    nlinarith [hγ]
  have hlog_lt : Real.log (1 + u) < u := by
    -- Apply the standard scalar inequality `log x < x - 1` at `x = 1 + u`.
    have hone_pos : 0 < 1 + u := by
      linarith
    have hone_ne : 1 + u ≠ 1 := by
      linarith
    simpa using Real.log_lt_sub_one_of_pos hone_pos hone_ne
  -- Rewriting through `u` turns the target into the same strict scalar inequality.
  change Real.log (1 + u) - u < 0
  linarith

/-- Lemma 7.7 (3): assume `S = ‖g‖*_D² > n`, and let
`α* = (S - n) / ((2 S - n) S)`. Then for every
`γ ∈ (1, ‖g‖*_D / √n]`, the logarithmic potential at `α*` satisfies
`V(α*) ≤ log (1 + (γ² - 1) / γ²) - (γ² - 1) / γ² < 0`. -/
theorem ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison_and_lt_zero
    (D : Matₙ) (hDdiag : D.IsDiag) (hDpos : D.PosDef) (g : Eₙ)
    (hS : (n : ℝ) < ‖g‖[⟨D, hDpos⟩,*] ^ (2 : ℕ)) (γ : ℝ)
    (hγ :
      γ ∈
        Set.Ioc
          (1 : ℝ)
          (‖g‖[⟨D, hDpos⟩,*] / Real.sqrt (n : ℝ))) :
    ellipsoidBoxLogVolumePotential D g (ellipsoidBoxAlphaStar D hDpos g) ≤
      Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)) -
        (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) ∧
    Real.log (1 + (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)) -
        (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) < 0 := by
  constructor
  · -- Reuse the scalar comparison theorem once the potential term is already normalized at `α*`.
    exact ellipsoidBoxLogVolumePotential_alphaStar_le_gammaComparison D hDdiag hDpos g hS γ hγ
  · -- The displayed comparison term is strictly negative for every `γ > 1`.
    exact ellipsoidBoxGammaComparison_neg γ hγ.1

end
