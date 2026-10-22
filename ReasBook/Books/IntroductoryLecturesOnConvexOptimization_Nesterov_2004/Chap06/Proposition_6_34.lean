/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_0_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_10

-- Declarations for this item will be appended below by the statement pipeline.

open RealSymmetricMatrixSpace
open scoped Gradient
open scoped MatrixOrder
open scoped RealSymmetricMatrixSpace

noncomputable section

variable {n : ℕ}

local notation "SymmMat" => 𝕊^n
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Proposition 6.34: use the Frobenius normed-group structure on ambient matrices
when importing the Chapter 6 trace-power calculus back to `SymmMat`. -/
local instance propositionSixThirtyFourAmbientMatrixNormedAddCommGroup : NormedAddCommGroup Mat :=
  Matrix.frobeniusNormedAddCommGroup

/-- Helper for Proposition 6.34: scalar multiplication on ambient matrices is measured with the
Frobenius norm during the local `SymmMat` calculus arguments. -/
local instance propositionSixThirtyFourAmbientMatrixNormedSpace : NormedSpace ℝ Mat :=
  Matrix.frobeniusNormedSpace

/-- Helper for Proposition 6.34: the ambient matrix ring carries the Frobenius-compatible normed
ring structure used by the local derivative API. -/
local instance propositionSixThirtyFourAmbientMatrixNormedRing : NormedRing Mat :=
  Matrix.frobeniusNormedRing

/-- Helper for Proposition 6.34: the ambient matrix algebra over `ℝ` carries the Frobenius
normed-algebra structure used by the imported Chapter 6 proofs. -/
local instance propositionSixThirtyFourAmbientMatrixNormedAlgebra : NormedAlgebra ℝ Mat :=
  Matrix.frobeniusNormedAlgebra

attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedAddCommGroup
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixNormedSpace
attribute [local instance 1001] RealSymmetricMatrixSpace.symmetricMatrixInnerProductSpace
attribute [local instance 900] RealSymmetricMatrixSpace.symmetricMatrixCompleteSpace

/-- Helper for Proposition 6.34: finite Hölder yields the weighted geometric mean estimate for a
sum of nonnegative terms. -/
private lemma weightedGeometricMeanSum_le
    (t : Finset (Fin n)) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (u v : Fin n → ℝ) (hu : ∀ i ∈ t, 0 ≤ u i) (hv : ∀ i ∈ t, 0 ≤ v i) :
    ∑ i ∈ t, (u i) ^ a * (v i) ^ b ≤ (∑ i ∈ t, u i) ^ a * (∑ i ∈ t, v i) ^ b := by
  let p : ℝ := 1 / a
  let q : ℝ := 1 / b
  have ha_lt_one : a < 1 := by
    nlinarith [hb, hab]
  have hpq : p.HolderConjugate q := by
    refine Real.holderConjugate_iff.mpr ?_
    constructor
    · dsimp [p]
      simpa [one_div] using (one_lt_inv₀ ha).2 ha_lt_one
    · dsimp [p, q]
      field_simp [ha.ne', hb.ne']
      nlinarith [hab]
  have hHolder :
      ∑ i ∈ t, (u i) ^ a * (v i) ^ b ≤
        (∑ i ∈ t, ((u i) ^ a) ^ p) ^ (1 / p) * (∑ i ∈ t, ((v i) ^ b) ^ q) ^ (1 / q) :=
    Real.inner_le_Lp_mul_Lq_of_nonneg t hpq
      (by intro i hi; exact Real.rpow_nonneg (hu i hi) _)
      (by intro i hi; exact Real.rpow_nonneg (hv i hi) _)
  have hsum_u : ∑ i ∈ t, ((u i) ^ a) ^ p = ∑ i ∈ t, u i := by
    -- The conjugate exponent `p = 1 / a` cancels the power `a`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [p]
    rw [← Real.rpow_mul (hu i hi)]
    field_simp [ha.ne']
    rw [Real.rpow_one]
  have hsum_v : ∑ i ∈ t, ((v i) ^ b) ^ q = ∑ i ∈ t, v i := by
    -- The same cancellation holds on the `v`-side with exponent `q = 1 / b`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    dsimp [q]
    rw [← Real.rpow_mul (hv i hi)]
    field_simp [hb.ne']
    rw [Real.rpow_one]
  have hp_inv : 1 / p = a := by
    dsimp [p]
    field_simp [ha.ne']
  have hq_inv : 1 / q = b := by
    dsimp [q]
    field_simp [hb.ne']
  rw [hsum_u, hsum_v, hp_inv, hq_inv] at hHolder
  simpa using hHolder

/-- Helper for Proposition 6.34: the absolute values of the ordered eigenvalues of `X`. -/
private abbrev absEig (X : SymmMat) : Fin n → ℝ :=
  fun i ↦ |eigenvalues X i|

/-- Helper for Proposition 6.34: tracing the Hermitian functional calculus of a symmetric matrix
applies the scalar function to the ordered eigenvalues and sums the result. -/
private theorem trace_cfc_eq_sum_map_eigenvalues
    (Q : SymmMat) (f : ℝ → ℝ) :
    Matrix.trace ((isHermitian Q).cfc f) = ∑ i : Fin n, f (eigenvalues Q i) := by
  -- Rewrite the matrix functional calculus into the diagonal eigenbasis model.
  rw [Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [Function.comp]

/-- Helper for Proposition 6.34: the even power sum of the absolute-value eigenvalues is the
Chapter 6 power-trace owner `π[2p]`. -/
private theorem absEig_evenPowerSum_eq_powerTrace
    (p : ℕ+) (X : SymmMat) :
    (∑ i : Fin n, absEig X i ^ (2 * (p : ℕ))) = π[2 * (p : ℕ)] X := by
  -- The even power erases the absolute values, so the sum can be rewritten on the original
  -- eigenvalues of `X` before collapsing back to the trace-power owner `π[2p]`.
  calc
    ∑ i : Fin n, absEig X i ^ (2 * (p : ℕ))
      = ∑ i : Fin n, (eigenvalues X i) ^ (2 * (p : ℕ)) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          dsimp [absEig]
          rw [pow_mul, pow_mul]
          exact congrArg (fun y : ℝ ↦ y ^ (p : ℕ)) (sq_abs (eigenvalues X i))
    _ = Matrix.trace ((isHermitian X).cfc (fun x : ℝ ↦ x ^ (2 * (p : ℕ)))) := by
          symm
          exact
            trace_cfc_eq_sum_map_eigenvalues X (fun x : ℝ ↦ x ^ (2 * (p : ℕ)))
    _ = Matrix.trace (cfc (fun x : ℝ ↦ x ^ (2 * (p : ℕ))) (X : Mat)) := by
          rw [(isHermitian X).cfc_eq]
    _ = Matrix.trace ((X : Mat) ^ (2 * (p : ℕ))) := by
          simpa using congrArg (fun A : Mat ↦ Matrix.trace A)
            (cfc_pow_id (X : Mat) (2 * (p : ℕ))
              (isHermitian X : IsSelfAdjoint (X : Mat)))
    _ = π[2 * (p : ℕ)] X := by
          rw [RealSymmetricMatrixSpace.powerTrace_def]

/-- Helper for Proposition 6.34: on the local Frobenius owner stack, the trace-power map
`X ↦ π[k] X = Trace (X^k)` is `C²` at every point. -/
private lemma powerTraceContDiffAtLocal
    (k : ℕ) (X : SymmMat) :
    ContDiffAt ℝ 2 (π[k] : SymmMat → ℝ) X := by
  rcases k with _ | k
  · have hconst :
        (π[0] : SymmMat → ℝ) = fun _ : SymmMat ↦ (n : ℝ) := by
      funext Y
      simp [RealSymmetricMatrixSpace.powerTrace_def]
    rw [hconst]
    exact (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : SymmMat ↦ (n : ℝ)) X)
  · have hcont : ContDiff ℝ 2 (π[k + 1] : SymmMat → ℝ) := by
      -- Proposition 6.33 already proves the `C²` regularity on the exact `SymmMat` owner.
      simpa using powerTrace_contDiff (n := n) (k + 1) (Nat.succ_le_succ (Nat.zero_le _))
    exact hcont.contDiffAt

/-- Helper for Proposition 6.34: on this file's local Frobenius owner stack, the Chapter 6
trace-power Hessian bound from Theorem 6.9 holds verbatim. -/
private theorem powerTraceIteratedFDerivTwoLeAbsEigenvaluePairingLocal
    (k : ℕ) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (π[k] : SymmMat → ℝ) X ![H, H] ≤
      (((k * (k - 1) : ℕ) : ℝ) *
        ∑ i : Fin n,
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
            (k - 2)) *
              (((Matrix.nonneg_iff_posSemidef.mp
                  (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
                (2 : ℕ))) := by
  -- Theorem 6.9 already states the Frobenius Hessian bound on the same symmetric-matrix owner.
  simpa using powerTrace_iteratedFDeriv_two_le_absEigenvaluePairing (n := n) k X H

/- Proposition 6.34 is source-faithful only when the Hessian is taken for the smoothing
functional `Y ↦ (1 / 2 : ℝ) * (π[2 * (p : ℕ)] Y)^(1 / p) = (1 / 2) ‖λ(Y)‖_(2p)^2`.
`Definition_6_44` already formalizes this owner as `squaredLpMatrixNormSmoothing`, so the main
labeled theorem below uses that source-facing declaration directly and keeps only the right-hand
side in the equivalent `Real.rpow` form.
Semantic recall note: `lean_leansearch` exposed only generic second-derivative APIs, so
`iteratedFDeriv ℝ 2` remains the right public Hessian surface here.
-/

-- Proof sketch: differentiate the source smoothing owner
-- `F_p(Y) = (1 / 2 : ℝ) * (π[2 * (p : ℕ)] Y)^(1 / p) = (1 / 2) * ‖λ(Y)‖_(2p)^2`
-- twice at `X`, evaluate the resulting Hessian on `![H, H]`, and bound it by the source quantity
-- `(2p - 1) * ‖λ(H)‖_(2p)^2 = (2p - 1) * (π[2p] H)^(1 / p)`.

/-- Helper for Proposition 6.34: the even trace power `π[2p] X` is always nonnegative. -/
private lemma evenPowerTraceNonneg
    (p : ℕ+) (X : SymmMat) :
    0 ≤ π[2 * (p : ℕ)] X := by
  -- Rewrite `π[2p] X` as the Frobenius self-pairing of `X ^ p`.
  have hpow_symm :
      (((X ^ (p : ℕ) : SymmMat) : Mat).transpose) = (((X ^ (p : ℕ) : SymmMat) : Mat)) := by
    simpa using (RealSymmetricMatrixSpace.isSymm (X ^ (p : ℕ))).eq
  calc
    0 ≤ ⟪X ^ (p : ℕ), X ^ (p : ℕ)⟫_F := frobeniusInner_self_nonneg (X ^ (p : ℕ))
    _ = Matrix.trace
          ((((X ^ (p : ℕ) : SymmMat) : Mat).transpose) * (((X ^ (p : ℕ) : SymmMat) : Mat))) := by
            rw [RealSymmetricMatrixSpace.frobeniusInner_def]
    _ = Matrix.trace
          ((((X ^ (p : ℕ) : SymmMat) : Mat)) * (((X ^ (p : ℕ) : SymmMat) : Mat))) := by
            rw [hpow_symm]
    _ = Matrix.trace (((X : Mat) ^ (p : ℕ)) * ((X : Mat) ^ (p : ℕ))) := by
          rfl
    _ = Matrix.trace ((X : Mat) ^ (2 * (p : ℕ))) := by
          rw [two_mul, ← pow_add]
    _ = π[2 * (p : ℕ)] X := by
          rw [RealSymmetricMatrixSpace.powerTrace_def]

/-- Helper for Proposition 6.34: the even trace power `π[2p] X` vanishes exactly at the zero
matrix. -/
private lemma evenPowerTrace_eq_zero_iff
    (p : ℕ+) (X : SymmMat) :
    π[2 * (p : ℕ)] X = 0 ↔ X = 0 := by
  constructor
  · intro hX
    have hsum :
        ∑ i : Fin n, absEig X i ^ (2 * (p : ℕ)) = 0 := by
      simpa [absEig_evenPowerSum_eq_powerTrace (p := p) X] using hX
    have habs_zero : ∀ i : Fin n, absEig X i = 0 := by
      intro i
      have hterm_zero :
          absEig X i ^ (2 * (p : ℕ)) = 0 := by
        exact
          (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ by positivity)).mp hsum i
            (Finset.mem_univ i)
      exact (pow_eq_zero_iff (by positivity : (2 * (p : ℕ)) ≠ 0)).mp hterm_zero
    have heigs_zero : (isHermitian X).eigenvalues = 0 := by
      funext i
      exact abs_eq_zero.mp (by simpa [absEig] using habs_zero i)
    -- Once every eigenvalue is zero, the Hermitian matrix itself is zero.
    have hmat_zero : (X : Mat) = 0 := (isHermitian X).eigenvalues_eq_zero_iff.mp heigs_zero
    ext i j
    simpa using congrArg (fun M : Mat ↦ M i j) hmat_zero
  · intro hX
    subst hX
    -- The even trace power of the zero matrix is immediate from the defining trace formula.
    simp [RealSymmetricMatrixSpace.powerTrace_def]

/-- Helper for Proposition 6.34: along a scalar ray, the Chapter 6 smoothing owner is exactly a
quadratic function of the scalar parameter. -/
private lemma squaredLpMatrixNormSmoothing_smul
    (p : ℕ+) (t : ℝ) (H : SymmMat) :
    squaredLpMatrixNormSmoothing p (t • H) =
      ((1 / 2 : ℝ) * (t ^ (2 : ℕ))) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast p.pos
  have hp_ne : (p : ℝ) ≠ 0 := hp_pos.ne'
  have hpowerTrace_smul :
      π[2 * (p : ℕ)] (t • H) = (t ^ (2 * (p : ℕ))) * π[2 * (p : ℕ)] H := by
    -- Pull the scalar through the even matrix power and then through the trace.
    rw [RealSymmetricMatrixSpace.powerTrace_def, RealSymmetricMatrixSpace.powerTrace_def]
    change Matrix.trace ((t • (H : Mat)) ^ (2 * (p : ℕ))) =
      (t ^ (2 * (p : ℕ))) * Matrix.trace ((H : Mat) ^ (2 * (p : ℕ)))
    rw [smul_pow]
    simp [Matrix.trace_smul]
  have htpow_rpow :
      Real.rpow (t ^ (2 * (p : ℕ))) (1 / (p : ℝ)) = t ^ (2 : ℕ) := by
    -- The even scalar power is `(t²)^p`, so the outer `rpow` collapses back to `t²`.
    calc
      Real.rpow (t ^ (2 * (p : ℕ))) (1 / (p : ℝ))
          = Real.rpow ((t ^ (2 : ℕ)) ^ (p : ℕ)) (1 / (p : ℝ)) := by
              rw [pow_mul]
      _ = Real.rpow (t ^ (2 : ℕ)) ((p : ℕ) * (1 / (p : ℝ))) := by
            simpa [Real.rpow_natCast] using
              (Real.rpow_natCast_mul (sq_nonneg t) (p : ℕ) (1 / (p : ℝ))).symm
      _ = Real.rpow (t ^ (2 : ℕ)) 1 := by
            congr 2
            field_simp [hp_ne]
      _ = t ^ (2 : ℕ) := by
            simp
  -- Rewrite the source owner through `π[2p]` and separate the two nonnegative factors.
  rw [squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace, hpowerTrace_smul]
  calc
    (1 / 2 : ℝ) * Real.rpow ((t ^ (2 * (p : ℕ))) * π[2 * (p : ℕ)] H) (1 / (p : ℝ))
        = (1 / 2 : ℝ) *
            (Real.rpow (t ^ (2 * (p : ℕ))) (1 / (p : ℝ)) *
              Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ))) := by
                have htnonneg : 0 ≤ t ^ (2 * (p : ℕ)) := by
                  have : 0 ≤ (t ^ (2 : ℕ)) ^ (p : ℕ) := by positivity
                  simpa [pow_mul] using this
                simpa using congrArg (fun x : ℝ ↦ (1 / 2 : ℝ) * x) <|
                  (Real.mul_rpow htnonneg (evenPowerTraceNonneg p H))
    _ = ((1 / 2 : ℝ) * (t ^ (2 : ℕ))) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
          rw [htpow_rpow]
          ring

/-- Helper for Proposition 6.34: when `p = 1`, the smoothing owner is exactly half the quadratic
trace-power owner `π[2]`. -/
private lemma squaredLpMatrixNormSmoothing_eq_half_powerTraceTwo_of_one
    (X : SymmMat) :
    squaredLpMatrixNormSmoothing 1 X = (1 / 2 : ℝ) * π[2] X := by
  -- For `p = 1`, the outer exponent is `1`, so the Chapter 6 bridge collapses to `π[2]`.
  rw [squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace]
  simp

/-- Helper for Proposition 6.34: the quadratic trace-power owner `π[2]` is the Frobenius norm
square on `𝕊^n`. -/
private lemma powerTrace_two_eq_norm_sq
    (X : SymmMat) :
    π[2] X = ‖X‖ ^ (2 : ℕ) := by
  -- Route correction: compare both sides through the ambient Frobenius norm formula, avoiding any
  -- extra inner-product owner synthesis on the symmetric subtype.
  have hsymm : ((X : Mat)).transpose = (X : Mat) := by
    simpa [Matrix.IsSymm] using (RealSymmetricMatrixSpace.isSymm X).eq
  let s : ℝ := ∑ i : Fin n, ∑ j : Fin n, ‖(X : Mat) i j‖ ^ (2 : ℝ)
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ by positivity
  calc
    π[2] X = Matrix.trace (((X : Mat)).transpose * (X : Mat)) := by
      rw [RealSymmetricMatrixSpace.powerTrace_def]
      simp [pow_two, hsymm]
    _ = s := by
      dsimp [s]
      rw [Matrix.trace, Finset.sum_comm]
      simp [Matrix.diag, Matrix.mul_apply, pow_two, Real.rpow_natCast, sq_abs]
    _ = ‖X‖ ^ (2 : ℕ) := by
      change s = ‖(X : Mat)‖ ^ (2 : ℕ)
      rw [Matrix.frobenius_norm_def]
      rw [show ∑ i : Fin n, ∑ j : Fin n, ‖(X : Mat) i j‖ ^ (2 : ℝ) = s by rfl]
      symm
      calc
        (s ^ (1 / (2 : ℝ))) ^ (2 : ℕ) = s ^ ((1 / (2 : ℝ)) * (2 : ℕ)) := by
          simpa using (Real.rpow_mul_natCast hs_nonneg (1 / (2 : ℝ)) 2).symm
        _ = s ^ (1 : ℝ) := by norm_num
        _ = s := by simp

/-- Helper for Proposition 6.34: when `p = 1`, the smoothing owner is exactly the quadratic
half-norm-square functional. -/
private lemma squaredLpMatrixNormSmoothing_eq_halfNormSq_of_one :
    squaredLpMatrixNormSmoothing 1 = fun Y : SymmMat ↦ (1 / 2 : ℝ) * ‖Y‖ ^ (2 : ℕ) := by
  -- Rewrite the Chapter 6 owner through `π[2]` and then collapse `π[2]` to the Frobenius norm
  -- square.
  funext Y
  rw [squaredLpMatrixNormSmoothing_eq_half_powerTraceTwo_of_one, powerTrace_two_eq_norm_sq]

/-- Helper for Proposition 6.34: when `n ≤ 1`, the smoothing owner is exactly the quadratic
half-norm-square functional for every positive integer `p`. -/
private lemma squaredLpMatrixNormSmoothing_eq_halfNormSq_of_smallDimension
    (p : ℕ+) (hn : n ≤ 1) :
    squaredLpMatrixNormSmoothing p = fun Y : SymmMat ↦ (1 / 2 : ℝ) * ‖Y‖ ^ (2 : ℕ) := by
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast p.pos
  have hp_ne : (p : ℝ) ≠ 0 := hp_pos.ne'
  have hn_cases : n = 0 ∨ n = 1 := by
    omega
  rcases hn_cases with rfl | rfl
  · funext Y
    -- In dimension `0`, the symmetric matrix space is trivial, so both sides vanish.
    have hY : Y = 0 := Subsingleton.elim _ _
    simp [hY, squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace]
  · funext Y
    have hpowerTrace :
        π[2 * (p : ℕ)] Y = absEig Y 0 ^ (2 * (p : ℕ)) := by
      -- In dimension `1`, the even power trace is the single absolute eigenvalue power.
      rw [← absEig_evenPowerSum_eq_powerTrace p Y]
      simp
    have hnorm :
        ‖Y‖ ^ (2 : ℕ) = absEig Y 0 ^ (2 : ℕ) := by
      -- The same one-dimensional collapse identifies the Frobenius norm square.
      have htwo : (∑ i : Fin 1, absEig Y i ^ (2 : ℕ)) = π[2] Y := by
        simpa using (absEig_evenPowerSum_eq_powerTrace (1 : ℕ+) Y)
      rw [← powerTrace_two_eq_norm_sq, ← htwo]
      simp
    have hcollapse :
        Real.rpow (absEig Y 0 ^ (2 * (p : ℕ))) (1 / (p : ℝ)) = absEig Y 0 ^ (2 : ℕ) := by
      -- The single even eigenvalue power is `(|λ₀|²)^p`, so the outer `rpow` cancels it.
      have hsquare_nonneg : 0 ≤ absEig Y 0 ^ (2 : ℕ) := by
        positivity
      calc
        Real.rpow (absEig Y 0 ^ (2 * (p : ℕ))) (1 / (p : ℝ))
            = Real.rpow ((absEig Y 0 ^ (2 : ℕ)) ^ (p : ℕ)) (1 / (p : ℝ)) := by
                rw [pow_mul]
        _ = Real.rpow (absEig Y 0 ^ (2 : ℕ)) (((p : ℕ) : ℝ) * (1 / (p : ℝ))) := by
              simpa [Real.rpow_natCast] using
                (Real.rpow_natCast_mul hsquare_nonneg (p : ℕ) (1 / (p : ℝ))).symm
        _ = Real.rpow (absEig Y 0 ^ (2 : ℕ)) 1 := by
              congr 2
              field_simp [hp_ne]
        _ = absEig Y 0 ^ (2 : ℕ) := by
              simp
    -- Rewrite the source owner through the one-dimensional spectral collapse.
    rw [squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace, hpowerTrace, hnorm, hcollapse]

/-- Helper for Proposition 6.34: in dimension `n ≤ 1`, the trace-power factor on the right-hand
side is exactly the Frobenius norm square. -/
private lemma rpow_powerTrace_eq_normSq_of_smallDimension
    (p : ℕ+) (hn : n ≤ 1) (X : SymmMat) :
    Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ)) = ‖X‖ ^ (2 : ℕ) := by
  have hsmall :
      squaredLpMatrixNormSmoothing p X = (1 / 2 : ℝ) * ‖X‖ ^ (2 : ℕ) := by
    exact congrArg (fun f : SymmMat → ℝ ↦ f X)
      (squaredLpMatrixNormSmoothing_eq_halfNormSq_of_smallDimension p hn)
  rw [squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace] at hsmall
  -- Cancel the common factor `1 / 2` to recover the norm-square identity.
  have hscaled := congrArg (fun z : ℝ ↦ (2 : ℝ) * z) hsmall
  simpa [mul_assoc] using hscaled

/-- Helper for Proposition 6.34: the Schatten-type factor
`(π[2p] X)^(1 / p)` is bounded above by the Frobenius norm square. -/
private lemma rpow_powerTrace_le_normSq
    (p : ℕ+) (X : SymmMat) :
    Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ)) ≤ ‖X‖ ^ (2 : ℕ) := by
  let a : Fin n → ℝ := fun i ↦ absEig X i ^ (2 : ℕ)
  let s : ℝ := ∑ i : Fin n, a i
  have hp_pos : 0 < (p : ℝ) := by
    exact_mod_cast p.pos
  have hp_ne : (p : ℝ) ≠ 0 := hp_pos.ne'
  have hp_nat_pos : 1 ≤ (p : ℕ) := Nat.succ_le_of_lt p.pos
  have ha_nonneg : ∀ i : Fin n, 0 ≤ a i := by
    intro i
    dsimp [a]
    positivity
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    exact Finset.sum_nonneg fun i _ ↦ ha_nonneg i
  have hs_eq_normSq : s = ‖X‖ ^ (2 : ℕ) := by
    -- Rewrite the sum of squared absolute eigenvalues through `π[2]`.
    calc
      s = ∑ i : Fin n, absEig X i ^ (2 : ℕ) := by
            rfl
      _ = π[2] X := by
            simpa using (absEig_evenPowerSum_eq_powerTrace (1 : ℕ+) X)
      _ = ‖X‖ ^ (2 : ℕ) := powerTrace_two_eq_norm_sq X
  have hsum_pow_le :
      ∑ i : Fin n, a i ^ (p : ℕ) ≤ s ^ (p : ℕ) := by
    have hp_sub : (p : ℕ) = ((p : ℕ) - 1) + 1 := (Nat.sub_add_cancel hp_nat_pos).symm
    have hpoint :
        ∀ i : Fin n, a i ^ (p : ℕ) ≤ s ^ ((p : ℕ) - 1) * a i := by
      intro i
      have hi_le : a i ≤ s := by
        dsimp [s]
        exact Finset.single_le_sum (fun j _ ↦ ha_nonneg j) (by simp)
      have hp_simpl : ((p : ℕ) - 1 + 1 - 1) = (p : ℕ) - 1 := by
        omega
      calc
        a i ^ (p : ℕ) = a i ^ ((p : ℕ) - 1) * a i := by
          rw [hp_sub, pow_add, pow_one]
          rw [hp_simpl]
        _ ≤ s ^ ((p : ℕ) - 1) * a i := by
          exact mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (ha_nonneg i) hi_le ((p : ℕ) - 1))
            (ha_nonneg i)
    calc
      ∑ i : Fin n, a i ^ (p : ℕ) ≤ ∑ i : Fin n, s ^ ((p : ℕ) - 1) * a i := by
            exact Finset.sum_le_sum fun i _ ↦ hpoint i
      _ = s ^ ((p : ℕ) - 1) * ∑ i : Fin n, a i := by
            rw [Finset.mul_sum]
      _ = s ^ (p : ℕ) := by
            have hp_simpl : ((p : ℕ) - 1 + 1 - 1) = (p : ℕ) - 1 := by
              omega
            rw [show ∑ i : Fin n, a i = s by rfl]
            rw [hp_sub, pow_add, pow_one]
            rw [hp_simpl]
  have hsump_eq :
      ∑ i : Fin n, a i ^ (p : ℕ) = π[2 * (p : ℕ)] X := by
    calc
      ∑ i : Fin n, a i ^ (p : ℕ)
          = ∑ i : Fin n, absEig X i ^ (2 * (p : ℕ)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              dsimp [a]
              rw [pow_mul]
      _ = π[2 * (p : ℕ)] X := absEig_evenPowerSum_eq_powerTrace p X
  have hpow_le :
      (Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ))) ^ (p : ℕ) ≤ (‖X‖ ^ (2 : ℕ)) ^ (p : ℕ) := by
    calc
      (Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ))) ^ (p : ℕ)
          = π[2 * (p : ℕ)] X := by
              have hπ_nonneg : 0 ≤ π[2 * (p : ℕ)] X := evenPowerTraceNonneg p X
              calc
                (Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ))) ^ (p : ℕ)
                    = Real.rpow (π[2 * (p : ℕ)] X) ((1 / (p : ℝ)) * (p : ℕ)) := by
                        symm
                        simpa using
                          (Real.rpow_mul_natCast hπ_nonneg (1 / (p : ℝ)) (p : ℕ))
                _ = Real.rpow (π[2 * (p : ℕ)] X) 1 := by
                      congr 2
                      field_simp [hp_ne]
                _ = π[2 * (p : ℕ)] X := by
                      simp
      _ = ∑ i : Fin n, a i ^ (p : ℕ) := by
            rw [← hsump_eq]
      _ ≤ s ^ (p : ℕ) := hsum_pow_le
      _ = (‖X‖ ^ (2 : ℕ)) ^ (p : ℕ) := by
            rw [hs_eq_normSq]
  exact le_of_pow_le_pow_left₀ (Nat.pos_iff_ne_zero.mp p.pos) (by positivity) hpow_le

/-- Helper for Proposition 6.34: the Chapter 6 smoothing owner is bounded above by half the
quadratic Frobenius norm square. -/
private lemma squaredLpMatrixNormSmoothing_le_half_normSq
    (p : ℕ+) (X : SymmMat) :
    squaredLpMatrixNormSmoothing p X ≤ (1 / 2 : ℝ) * ‖X‖ ^ (2 : ℕ) := by
  -- Rewrite through `π[2p]` and apply the norm-square majorization above.
  rw [squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace]
  exact mul_le_mul_of_nonneg_left (rpow_powerTrace_le_normSq p X) (by norm_num)

/-- Helper for Proposition 6.34: the smoothing owner has zero Fréchet derivative at the origin
because its remainder is quadratically small there. -/
private lemma squaredLpMatrixNormSmoothing_hasFDerivAt_zero
    (p : ℕ+) :
    HasFDerivAt (squaredLpMatrixNormSmoothing p) (0 : SymmMat →L[ℝ] ℝ) (0 : SymmMat) := by
  have hzero : squaredLpMatrixNormSmoothing p (0 : SymmMat) = 0 := by
    -- At the zero matrix, the nonnegative trace-power base vanishes, so the smoothing owner does
    -- as well.
    rw [squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace]
    have hp_inv_pos : 0 < 1 / (p : ℝ) := by
      exact one_div_pos.mpr (by exact_mod_cast p.pos)
    rw [RealSymmetricMatrixSpace.powerTrace_def]
    simp
  -- The quadratic remainder estimate upgrades to a little-o estimate of order `‖X‖`.
  refine
    (hasFDerivAt_iff_isLittleO_nhds_zero
      (f := squaredLpMatrixNormSmoothing p)
      (f' := (0 : SymmMat →L[ℝ] ℝ))
      (x := (0 : SymmMat))).2 ?_
  have hbigO :
      (fun X : SymmMat ↦
        squaredLpMatrixNormSmoothing p ((0 : SymmMat) + X) -
          squaredLpMatrixNormSmoothing p (0 : SymmMat) -
          (0 : SymmMat →L[ℝ] ℝ) X) =O[nhds (0 : SymmMat)]
        fun X : SymmMat ↦ (‖X‖ ^ (2 : ℕ) : ℝ) := by
    refine Asymptotics.IsBigO.of_bound (1 / 2 : ℝ) ?_
    filter_upwards [Filter.Eventually.of_forall fun X : SymmMat ↦
      squaredLpMatrixNormSmoothing_le_half_normSq p X] with X hX
    have hFX_nonneg : 0 ≤ squaredLpMatrixNormSmoothing p X := by
      rw [squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace]
      exact mul_nonneg (by norm_num) (Real.rpow_nonneg (evenPowerTraceNonneg p X) _)
    have hpow_nonneg : 0 ≤ (‖X‖ ^ (2 : ℕ) : ℝ) := by
      positivity
    simpa [hzero, Real.norm_of_nonneg hFX_nonneg, Real.norm_of_nonneg hpow_nonneg] using hX
  exact hbigO.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)

/-- Helper for Proposition 6.34: at every nonzero point on a ray through the origin, evaluating
the Fréchet derivative on the ray direction gives the derivative of the explicit quadratic ray
formula. -/
private lemma fderivAlongRay_apply_eq_mul_rpowPowerTrace
    (p : ℕ+) {H : SymmMat} (hH : π[2 * (p : ℕ)] H ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    (fderiv ℝ (squaredLpMatrixNormSmoothing p) (t • H)) H =
      t * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
  -- Route correction: stay on the `fderiv`/`lineDeriv` owner instead of passing through
  -- `gradient` and the subtype Hilbert-space interface.
  let c : ℝ := Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ))
  have hk : 1 ≤ 2 * (p : ℕ) := by
    have hp1 : 1 ≤ (p : ℕ) := Nat.succ_le_of_lt p.pos
    omega
  have hpowerTrace_smul :
      π[2 * (p : ℕ)] (t • H) = (t ^ (2 * (p : ℕ))) * π[2 * (p : ℕ)] H := by
    -- Pull the scalar through the even matrix power and then through the trace.
    rw [RealSymmetricMatrixSpace.powerTrace_def, RealSymmetricMatrixSpace.powerTrace_def]
    change Matrix.trace ((t • (H : Mat)) ^ (2 * (p : ℕ))) =
      (t ^ (2 * (p : ℕ))) * Matrix.trace ((H : Mat) ^ (2 * (p : ℕ)))
    rw [smul_pow]
    simp [Matrix.trace_smul]
  have htrace_ne : π[2 * (p : ℕ)] (t • H) ≠ 0 := by
    rw [hpowerTrace_smul]
    exact mul_ne_zero (pow_ne_zero _ ht) hH
  have hpowerDiff :
      DifferentiableAt ℝ (π[2 * (p : ℕ)] : SymmMat → ℝ) (t • H) := by
    exact (powerTraceContDiffAtLocal (2 * (p : ℕ)) (t • H)).differentiableAt
      (x := t • H) (by norm_num)
  have hrpowDiff := hpowerDiff.rpow_const (p := 1 / (p : ℝ)) (Or.inl htrace_ne)
  have hdiff : DifferentiableAt ℝ (squaredLpMatrixNormSmoothing p) (t • H) := by
    -- Away from the zero trace-power base, the smoothing owner is the composition of the smooth
    -- trace-power polynomial with the scalar `rpow` map.
    change
      DifferentiableAt ℝ
        (fun Y : SymmMat ↦
          (1 / 2 : ℝ) * Real.rpow (π[2 * (p : ℕ)] Y) (1 / (p : ℝ)))
        (t • H)
    simpa using hrpowDiff.const_mul (1 / 2 : ℝ)
  have hsq :
      HasDerivAt (fun s : ℝ ↦ (t + s) ^ (2 : ℕ)) (2 * t) 0 := by
    -- Differentiate the shifted scalar square on the ray parameter.
    have hshift : HasDerivAt (fun s : ℝ ↦ t + s) 1 0 := by
      simpa using (hasDerivAt_id (x := (0 : ℝ))).const_add t
    simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc] using hshift.mul hshift
  have hscalar :
      HasDerivAt (fun s : ℝ ↦ ((1 / 2 : ℝ) * (t + s) ^ (2 : ℕ)) * c) (t * c) 0 := by
    -- The explicit ray formula is quadratic in the scalar parameter, so its derivative is linear.
    have hmul :
        HasDerivAt
          (fun s : ℝ ↦ (t + s) ^ (2 : ℕ) * ((1 / 2 : ℝ) * c))
          ((2 * t) * ((1 / 2 : ℝ) * c))
          0 := hsq.mul_const ((1 / 2 : ℝ) * c)
    simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc, mul_add, add_mul,
      mul_comm, mul_left_comm, mul_assoc] using hmul
  have hline :
      lineDeriv ℝ (squaredLpMatrixNormSmoothing p) (t • H) H = t * c := by
    have hlineDeriv :
        HasLineDerivAt ℝ (squaredLpMatrixNormSmoothing p) (t * c) (t • H) H := by
      -- Rewrite the translated line `s ↦ t • H + s • H` as the scalar ray `(t + s) • H`.
      change
        HasDerivAt
          (fun s : ℝ ↦ squaredLpMatrixNormSmoothing p (t • H + s • H))
          (t * c)
          0
      convert hscalar using 1
      ext s
      rw [show t • H + s • H = (t + s) • H by simp [add_smul]]
      simpa [c] using squaredLpMatrixNormSmoothing_smul p (t + s) H
    exact hlineDeriv.lineDeriv
  -- Identify the scalar line derivative with the Fréchet derivative at the nonzero ray point.
  calc
    fderiv ℝ (squaredLpMatrixNormSmoothing p) (t • H) H
        = lineDeriv ℝ (squaredLpMatrixNormSmoothing p) (t • H) H := by
          rw [hdiff.lineDeriv_eq_fderiv]
    _ = t * c := hline
    _ = t * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
          rfl

/-- Helper for Proposition 6.34: the trace power of a diagonal symmetric matrix is the sum of the
corresponding diagonal even powers. -/
private theorem powerTrace_eq_sum_evenPow_of_diagonal
    (p : ℕ+) {D : SymmMat} {d : Fin n → ℝ}
    (hD : ((D : SymmMat) : Mat) = Matrix.diagonal d) :
    π[2 * (p : ℕ)] D = ∑ i : Fin n, d i ^ (2 * (p : ℕ)) := by
  -- Rewrite the trace of the matrix power on the stable diagonal normal form.
  rw [RealSymmetricMatrixSpace.powerTrace_def, hD, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp [Pi.pow_apply]

/-- Helper for Proposition 6.34: the diagonal single-entry projector belongs to the symmetric
matrix space `𝕊^n`. -/
private theorem coordinateProjectorDiagonal_mem
    (i : Fin n) :
    Matrix.diagonal (Pi.single i (1 : ℝ)) ∈ 𝕊^n := by
  -- A diagonal matrix is symmetric, so it belongs to the intrinsic symmetric carrier.
  rw [RealSymmetricMatrixSpace.mem_iff_isSymm, Matrix.IsSymm]
  ext j k
  by_cases hjk : j = k
  · subst hjk
    simp
  · simp [hjk, eq_comm]

/-- Helper for Proposition 6.34: the `i`-th diagonal rank-one projector, viewed in `𝕊^n`. -/
private def coordinateProjector
    (i : Fin n) : SymmMat :=
  ⟨Matrix.diagonal (Pi.single i (1 : ℝ)), coordinateProjectorDiagonal_mem (n := n) i⟩

/-- Helper for Proposition 6.34: the ambient matrix of the coordinate projector is the expected
single-entry diagonal matrix. -/
private theorem coordinateProjector_coe
    (i : Fin n) :
    ((coordinateProjector (n := n) i : SymmMat) : Mat) = Matrix.diagonal (Pi.single i (1 : ℝ)) := by
  -- The projector is definitionally the diagonal matrix with a single `1`.
  rfl

/-- Helper for Proposition 6.34: the even trace power of a coordinate projector is `1`. -/
private theorem powerTrace_coordinateProjector
    (p : ℕ+) (i : Fin n) :
    π[2 * (p : ℕ)] (coordinateProjector (n := n) i) = 1 := by
  -- Normalize the coordinate projector to a diagonal matrix and collapse its single nonzero entry.
  simpa [Pi.single_apply] using
    powerTrace_eq_sum_evenPow_of_diagonal
      (p := p)
      (D := coordinateProjector (n := n) i)
      (d := Pi.single i (1 : ℝ))
      (coordinateProjector_coe (n := n) i)

/-- Helper for Proposition 6.34: the even trace power of the sum of two distinct coordinate
projectors is `2`. -/
private theorem powerTrace_coordinateProjector_add
    (p : ℕ+) {i j : Fin n} (hij : i ≠ j) :
    π[2 * (p : ℕ)] ((coordinateProjector (n := n) i) + coordinateProjector (n := n) j) = 2 := by
  let d : Fin n → ℝ := fun a ↦ if a = i then 1 else if a = j then 1 else 0
  have hdiag :
      (((coordinateProjector (n := n) i) + coordinateProjector (n := n) j : SymmMat) : Mat) =
        Matrix.diagonal d := by
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · by_cases haj : a = j
        · exact (hij (hai.symm.trans haj)).elim
        · have hij' : i ≠ j := by
            simpa [hai] using haj
          simp [coordinateProjector_coe, d, hai, hij']
      · by_cases haj : a = j
        · have hij' : i ≠ j := by
            intro hij_eq
            apply hai
            simpa [haj] using hij_eq.symm
          simp [coordinateProjector_coe, d, haj, hij']
        · simp [coordinateProjector_coe, d, hai, haj]
    · simp [coordinateProjector_coe, d, hab]
  -- The sum has exactly two diagonal entries equal to `1`, at `i` and `j`.
  calc
    π[2 * (p : ℕ)] ((coordinateProjector (n := n) i) + coordinateProjector (n := n) j)
        = ∑ a : Fin n, d a ^ (2 * (p : ℕ)) := by
            exact
              powerTrace_eq_sum_evenPow_of_diagonal
                (p := p)
                (D := (coordinateProjector (n := n) i) + coordinateProjector (n := n) j)
                (d := d)
                hdiag
    _ = 2 := by
          have hsplit :
              ∑ a : Fin n, d a ^ (2 * (p : ℕ)) =
                ∑ a : Fin n, ((if a = i then (1 : ℝ) else 0) + if a = j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            by_cases hai : a = i
            · have hij' : i ≠ j := hij
              simp [d, hai, hij']
            · by_cases haj : a = j
              · have hji : j ≠ i := fun hji ↦ hij hji.symm
                simp [d, haj, hji]
              · simp [d, hai, haj]
          rw [hsplit, Finset.sum_add_distrib]
          norm_num

/-- Helper for Proposition 6.34: the even trace power of the difference of two distinct coordinate
projectors is `2`. -/
private theorem powerTrace_coordinateProjector_sub
    (p : ℕ+) {i j : Fin n} (hij : i ≠ j) :
    π[2 * (p : ℕ)] ((coordinateProjector (n := n) i) - coordinateProjector (n := n) j) = 2 := by
  let d : Fin n → ℝ := fun a ↦ if a = i then 1 else if a = j then -1 else 0
  have hdiag :
      (((coordinateProjector (n := n) i) - coordinateProjector (n := n) j : SymmMat) : Mat) =
        Matrix.diagonal d := by
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hai : a = i
      · by_cases haj : a = j
        · exact (hij (hai.symm.trans haj)).elim
        · have hij' : i ≠ j := by
            simpa [hai] using haj
          simp [coordinateProjector_coe, d, hai, hij']
      · by_cases haj : a = j
        · have hij' : i ≠ j := by
            intro hij_eq
            apply hai
            simpa [haj] using hij_eq.symm
          have hji : j ≠ i := fun hji ↦ hij hji.symm
          simp [coordinateProjector_coe, d, haj, hji]
        · simp [coordinateProjector_coe, d, hai, haj]
    · simp [coordinateProjector_coe, d, hab]
  -- The two nonzero diagonal entries are `1` and `-1`, whose even powers both equal `1`.
  calc
    π[2 * (p : ℕ)] ((coordinateProjector (n := n) i) - coordinateProjector (n := n) j)
        = ∑ a : Fin n, d a ^ (2 * (p : ℕ)) := by
            exact
              powerTrace_eq_sum_evenPow_of_diagonal
                (p := p)
                (D := (coordinateProjector (n := n) i) - coordinateProjector (n := n) j)
                (d := d)
                hdiag
    _ = ∑ a : Fin n, if a = i then (1 : ℝ) else if a = j then 1 else 0 := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          by_cases hai : a = i
          · simp [d, hai]
          · by_cases haj : a = j
            · have hji : j ≠ i := fun hji ↦ hij hji.symm
              simp [d, haj, hji]
            · simp [d, hai, haj]
    _ = ∑ a : Fin n, ((if a = i then (1 : ℝ) else 0) + if a = j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            by_cases hai : a = i
            · have hij' : i ≠ j := hij
              simp [hai, hij']
            · by_cases haj : a = j
              · have hji : j ≠ i := fun hji ↦ hij hji.symm
                simp [haj, hji]
              · simp [hai, haj]
    _ = (∑ a : Fin n, if a = i then (1 : ℝ) else 0) +
          ∑ a : Fin n, if a = j then (1 : ℝ) else 0 := by
            rw [Finset.sum_add_distrib]
    _ = 2 := by
          norm_num

/-- Helper for Proposition 6.34: if the Fréchet-derivative field is differentiable at the
origin, then the totalized second Fréchet derivative agrees with the exact nonzero-ray slope. -/
private lemma iteratedFDerivTwoAtZero_eq_rpowPowerTrace_of_fderivDifferentiableAt
    (p : ℕ+) {H : SymmMat} (hH : π[2 * (p : ℕ)] H ≠ 0)
    (hfdiff : DifferentiableAt ℝ (fderiv ℝ (squaredLpMatrixNormSmoothing p)) (0 : SymmMat)) :
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![H, H] =
      Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
  -- Route correction: identify the origin second derivative by differentiating the scalar field
  -- `Y ↦ fderiv ℝ f Y H` along the line `t ↦ t • H`.
  let f : SymmMat → ℝ := squaredLpMatrixNormSmoothing p
  let c : ℝ := Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ))
  let φ : ℝ → ℝ := fun t ↦ fderiv ℝ f (t • H) H
  have hzeroDeriv : HasFDerivAt f (0 : SymmMat →L[ℝ] ℝ) (0 : SymmMat) := by
    simpa [f] using squaredLpMatrixNormSmoothing_hasFDerivAt_zero p
  have hfderiv0 : fderiv ℝ f (0 : SymmMat) = (0 : SymmMat →L[ℝ] ℝ) := by
    exact hzeroDeriv.fderiv
  have hgdiff :
      DifferentiableAt ℝ (fun Y : SymmMat ↦ fderiv ℝ f Y H) (0 : SymmMat) := by
    exact hfdiff.clm_apply (differentiableAt_const H)
  have happly :
      fderiv ℝ (fun Y : SymmMat ↦ fderiv ℝ f Y H) (0 : SymmMat) =
        (fderiv ℝ (fderiv ℝ f) (0 : SymmMat)).flip H := by
    -- Freeze the outer direction `H` using the canonical `clm_apply` derivative rule.
    simpa using
      (fderiv_clm_apply (𝕜 := ℝ) (x := (0 : SymmMat))
        (c := fderiv ℝ f) (u := fun _ : SymmMat ↦ H)
        hfdiff (differentiableAt_const H))
  have hφ_deriv :
      HasDerivAt φ (iteratedFDeriv ℝ 2 f (0 : SymmMat) ![H, H]) 0 := by
    have hline :
        HasLineDerivAt ℝ (fun Y : SymmMat ↦ fderiv ℝ f Y H)
          ((fderiv ℝ (fun Y : SymmMat ↦ fderiv ℝ f Y H) (0 : SymmMat)) H)
          (0 : SymmMat) H := by
      exact hgdiff.hasFDerivAt.hasLineDerivAt H
    have hvalue :
        (fderiv ℝ (fun Y : SymmMat ↦ fderiv ℝ f Y H) (0 : SymmMat)) H =
          iteratedFDeriv ℝ 2 f (0 : SymmMat) ![H, H] := by
      calc
        (fderiv ℝ (fun Y : SymmMat ↦ fderiv ℝ f Y H) (0 : SymmMat)) H
            = ((fderiv ℝ (fderiv ℝ f) (0 : SymmMat)).flip H) H := by
                rw [happly]
        _ = fderiv ℝ (fderiv ℝ f) (0 : SymmMat) H H := by
              rfl
        _ = iteratedFDeriv ℝ 2 f (0 : SymmMat) ![H, H] := by
              symm
              simpa [iteratedFDeriv_two_apply]
    have hφ_line :
        HasDerivAt φ
          ((fderiv ℝ (fun Y : SymmMat ↦ fderiv ℝ f Y H) (0 : SymmMat)) H) 0 := by
      simpa [HasLineDerivAt, φ] using hline
    exact hφ_line.congr_deriv hvalue
  have hφ_eq :
      φ = fun t : ℝ ↦ t * c := by
    funext t
    by_cases ht : t = 0
    · -- The origin value is forced to be zero by the vanishing derivative there.
      subst ht
      simp [φ, c, hfderiv0]
    · -- Away from the origin, the explicit Fréchet-derivative ray formula applies verbatim.
      simpa [φ, c, f] using fderivAlongRay_apply_eq_mul_rpowPowerTrace p hH ht
  have hφ_model := hφ_deriv
  rw [hφ_eq] at hφ_model
  -- Uniqueness of the scalar derivative identifies the origin second derivative with the ray slope.
  have hlinear : HasDerivAt (fun t : ℝ ↦ t * c) c 0 := by
    simpa [one_mul] using (hasDerivAt_id (x := (0 : ℝ))).mul_const c
  exact hφ_model.unique hlinear

/-- Helper for Proposition 6.34: every bilinear second derivative satisfies the parallelogram
identity on diagonal evaluations. -/
private lemma iteratedFDerivTwoParallelogram
    {f : SymmMat → ℝ} {x U V : SymmMat} :
    iteratedFDeriv ℝ 2 f x ![U + V, U + V] + iteratedFDeriv ℝ 2 f x ![U - V, U - V] =
      2 * iteratedFDeriv ℝ 2 f x ![U, U] + 2 * iteratedFDeriv ℝ 2 f x ![V, V] := by
  -- Expand the actual bilinear second derivative and cancel the mixed terms pairwise.
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply,
    iteratedFDeriv_two_apply]
  simp [map_add, map_sub, sub_eq_add_neg]
  ring

/-- Helper for Proposition 6.34: in dimension at least two and away from the quadratic branch
`p = 1`, the Fréchet-derivative field cannot be differentiable at the origin. -/
private lemma notDifferentiableAtFDeriv_zero_of_notSmallDimension_of_p_ne_one
    (p : ℕ+) (hn : ¬ n ≤ 1) (hp1 : p ≠ 1) :
    ¬ DifferentiableAt ℝ (fderiv ℝ (squaredLpMatrixNormSmoothing p)) (0 : SymmMat) := by
  -- Route correction: use the totalized second Fréchet derivative directly instead of rebuilding
  -- a quadratic form through `hessian`.
  intro hfdiff
  have hn0 : 0 < n := by
    omega
  have hn1 : 1 < n := by
    omega
  let i : Fin n := ⟨0, hn0⟩
  let j : Fin n := ⟨1, hn1⟩
  have hij : i ≠ j := by
    -- The first two coordinate directions are distinct when `n > 1`.
    simp [i, j]
  let Pi : SymmMat := coordinateProjector (n := n) i
  let Pj : SymmMat := coordinateProjector (n := n) j
  have hPi_ne : π[2 * (p : ℕ)] Pi ≠ 0 := by
    rw [show Pi = coordinateProjector (n := n) i by rfl, powerTrace_coordinateProjector]
    norm_num
  have hPj_ne : π[2 * (p : ℕ)] Pj ≠ 0 := by
    rw [show Pj = coordinateProjector (n := n) j by rfl, powerTrace_coordinateProjector]
    norm_num
  have hAdd_ne : π[2 * (p : ℕ)] (Pi + Pj) ≠ 0 := by
    rw [show Pi + Pj =
      coordinateProjector (n := n) i + coordinateProjector (n := n) j by rfl,
      powerTrace_coordinateProjector_add p hij]
    norm_num
  have hSub_ne : π[2 * (p : ℕ)] (Pi - Pj) ≠ 0 := by
    rw [show Pi - Pj =
      coordinateProjector (n := n) i - coordinateProjector (n := n) j by rfl,
      powerTrace_coordinateProjector_sub p hij]
    norm_num
  have hPi_quad :
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pi, Pi] = 1 := by
    -- Each coordinate projector has unit `2p`-power trace, so the ray slope is exactly `1`.
    calc
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pi, Pi]
          = Real.rpow (π[2 * (p : ℕ)] Pi) (1 / (p : ℝ)) := by
              exact
                iteratedFDerivTwoAtZero_eq_rpowPowerTrace_of_fderivDifferentiableAt
                  p hPi_ne hfdiff
      _ = 1 := by
            rw [show π[2 * (p : ℕ)] Pi = 1 by
              simpa [Pi] using powerTrace_coordinateProjector (p := p) i]
            simp
  have hPj_quad :
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pj, Pj] = 1 := by
    -- The same unit slope holds for the second coordinate projector.
    calc
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pj, Pj]
          = Real.rpow (π[2 * (p : ℕ)] Pj) (1 / (p : ℝ)) := by
              exact
                iteratedFDerivTwoAtZero_eq_rpowPowerTrace_of_fderivDifferentiableAt
                  p hPj_ne hfdiff
      _ = 1 := by
            rw [show π[2 * (p : ℕ)] Pj = 1 by
              simpa [Pj] using powerTrace_coordinateProjector (p := p) j]
            simp
  have hAdd_quad :
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pi + Pj, Pi + Pj] =
        Real.rpow 2 (1 / (p : ℝ)) := by
    -- The sum projector has `2p`-power trace equal to `2`.
    calc
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pi + Pj, Pi + Pj]
          = Real.rpow (π[2 * (p : ℕ)] (Pi + Pj)) (1 / (p : ℝ)) := by
              exact
                iteratedFDerivTwoAtZero_eq_rpowPowerTrace_of_fderivDifferentiableAt
                  p hAdd_ne hfdiff
      _ = Real.rpow 2 (1 / (p : ℝ)) := by
            rw [show π[2 * (p : ℕ)] (Pi + Pj) = 2 by
              simpa [Pi, Pj] using powerTrace_coordinateProjector_add (p := p) hij]
  have hSub_quad :
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pi - Pj, Pi - Pj] =
        Real.rpow 2 (1 / (p : ℝ)) := by
    -- The difference projector has the same even trace-power value `2`.
    calc
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pi - Pj, Pi - Pj]
          = Real.rpow (π[2 * (p : ℕ)] (Pi - Pj)) (1 / (p : ℝ)) := by
              exact
                iteratedFDerivTwoAtZero_eq_rpowPowerTrace_of_fderivDifferentiableAt
                  p hSub_ne hfdiff
      _ = Real.rpow 2 (1 / (p : ℝ)) := by
            rw [show π[2 * (p : ℕ)] (Pi - Pj) = 2 by
              simpa [Pi, Pj] using powerTrace_coordinateProjector_sub (p := p) hij]
  have hpar_eq : 2 * Real.rpow 2 (1 / (p : ℝ)) = 4 := by
    -- The exact ray slopes conflict with the universal parallelogram identity of bilinear forms.
    calc
      2 * Real.rpow 2 (1 / (p : ℝ))
          =
            iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pi + Pj, Pi + Pj] +
              iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pi - Pj, Pi - Pj] := by
              nlinarith [hAdd_quad, hSub_quad]
      _ =
          2 * iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pi, Pi] +
            2 * iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![Pj, Pj] := by
              exact
                iteratedFDerivTwoParallelogram
                  (f := squaredLpMatrixNormSmoothing p) (x := (0 : SymmMat))
                  (U := Pi) (V := Pj)
      _ = 4 := by
            nlinarith [hPi_quad, hPj_quad]
  have hp_ne_one_nat : (p : ℕ) ≠ 1 := by
    intro hp_eq
    apply hp1
    exact_mod_cast hp_eq
  have hp_gt_nat : 1 < (p : ℕ) := by
    have hp_one_le : 1 ≤ (p : ℕ) := Nat.succ_le_of_lt p.pos
    exact lt_of_le_of_ne hp_one_le hp_ne_one_nat.symm
  have hfrac_lt_one : 1 / (p : ℝ) < 1 := by
    have hp_real_ne : (p : ℝ) ≠ 0 := by
      exact_mod_cast p.ne_zero
    field_simp [hp_real_ne]
    have hp_gt_real : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast hp_gt_nat
    linarith
  have hstrict : Real.rpow 2 (1 / (p : ℝ)) < 2 := by
    -- Since `p > 1`, the exponent `1 / p` lies strictly below `1`, so the base-`2` power is
    -- strictly below `2`.
    have hlt : Real.rpow 2 (1 / (p : ℝ)) < Real.rpow 2 (1 : ℝ) := by
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hfrac_lt_one
    simpa using hlt
  have hneq : Real.rpow 2 (1 / (p : ℝ)) ≠ 2 := by
    exact ne_of_lt hstrict
  exact hneq (by nlinarith [hpar_eq])

/-- Helper for Proposition 6.34: if the Fréchet-derivative field is not differentiable at a
point, then the repeated second Fréchet derivative vanishes there by totalization. -/
private lemma iteratedFDerivTwo_eq_zero_of_not_differentiableAt_fderiv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x : E}
    (hfdiff : ¬ DifferentiableAt ℝ (fderiv ℝ f) x) :
    iteratedFDeriv ℝ 2 f x = 0 := by
  ext m
  simp [iteratedFDeriv_two_apply, fderiv_zero_of_not_differentiableAt hfdiff]

/-- Helper for Proposition 6.34: the ambient absolute-value eigenvalues agree with the
eigenvalues of `|X| : 𝕊^n`. -/
private lemma absEigenvaluesEqAmbientAbsEigenvalues
    (X : SymmMat) :
    eigenvalues (|X| : SymmMat) =
      (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues := by
  have habsHerm : (CFC.abs (X : Mat)).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian
  -- Both eigenvalue lists come from the same ambient Hermitian matrix `CFC.abs X`.
  exact
    ((habsHerm.eigenvalues_eq_eigenvalues_iff (isHermitian (|X| : SymmMat))).2 <| by
      simp [RealSymmetricMatrixSpace.coe_abs]).symm

/-- Helper for Proposition 6.34: the even power sum of the ambient absolute-value eigenvalues of
`X` is the Chapter 6 trace-power owner `π[2p] X`. -/
private lemma ambientAbsEigenvalue_evenPowerSum_eq_powerTrace
    (p : ℕ+) (X : SymmMat) :
    ∑ i : Fin n,
      (((Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues i) ^
        (2 * (p : ℕ))) =
      π[2 * (p : ℕ)] X := by
  have habs_nonneg : ∀ i : Fin n, 0 ≤ eigenvalues (|X| : SymmMat) i := by
    intro i
    exact
      (Matrix.nonneg_iff_posSemidef.mp
        (RealSymmetricMatrixSpace.abs_nonneg X)).eigenvalues_nonneg i
  have hself : IsSelfAdjoint (X : Mat) := by
    simpa using (isHermitian X)
  calc
    ∑ i : Fin n,
        (((Matrix.nonneg_iff_posSemidef.mp
            (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues i) ^
          (2 * (p : ℕ)))
        = ∑ i : Fin n, (eigenvalues (|X| : SymmMat) i) ^ (2 * (p : ℕ)) := by
            simp [absEigenvaluesEqAmbientAbsEigenvalues]
    _ = Matrix.trace
          ((isHermitian (|X| : SymmMat)).cfc (fun x : ℝ ↦ x ^ (2 * (p : ℕ)))) := by
            symm
            exact
              trace_cfc_eq_sum_map_eigenvalues
                (|X| : SymmMat) (fun x : ℝ ↦ x ^ (2 * (p : ℕ)))
    _ = Matrix.trace (cfc (fun x : ℝ ↦ x ^ (2 * (p : ℕ))) (((|X| : SymmMat) : Mat))) := by
          rw [(isHermitian (|X| : SymmMat)).cfc_eq]
    _ = Matrix.trace (cfc (fun x : ℝ ↦ |x| ^ (2 * (p : ℕ))) (X : Mat)) := by
          calc
            Matrix.trace (cfc (fun x : ℝ ↦ x ^ (2 * (p : ℕ))) (((|X| : SymmMat) : Mat)))
                = Matrix.trace (cfc (fun x : ℝ ↦ x ^ (2 * (p : ℕ))) (CFC.abs (X : Mat))) := by
                    simp [RealSymmetricMatrixSpace.coe_abs]
            _ = Matrix.trace (cfc (fun x : ℝ ↦ |x| ^ (2 * (p : ℕ))) (X : Mat)) := by
                  simpa using
                    congrArg Matrix.trace
                      ((cfc_comp_norm (fun x : ℝ ↦ x ^ (2 * (p : ℕ))) (X : Mat) hself).symm)
    _ = Matrix.trace ((isHermitian X).cfc (fun x : ℝ ↦ |x| ^ (2 * (p : ℕ)))) := by
          rw [(isHermitian X).cfc_eq]
    _ = ∑ i : Fin n, absEig X i ^ (2 * (p : ℕ)) := by
          simpa [absEig] using
            trace_cfc_eq_sum_map_eigenvalues X (fun x : ℝ ↦ |x| ^ (2 * (p : ℕ)))
    _ = π[2 * (p : ℕ)] X := absEig_evenPowerSum_eq_powerTrace p X

/-- Helper for Proposition 6.34: in the exact quadratic branch `p = 1`, the Hessian quadratic
form of the smoothing owner is exactly the Frobenius norm square of the direction. -/
private lemma halfPowerTraceIteratedFDerivTwoLe_of_one
    (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing 1) X ![H, H] ≤
      Real.rpow (π[2] H) (1 : ℝ) := by
  have hpowerCont : ContDiffAt ℝ 2 (π[2] : SymmMat → ℝ) X :=
    powerTraceContDiffAtLocal 2 X
  have hiter :
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing 1) X ![H, H] =
        (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 (π[2] : SymmMat → ℝ) X ![H, H] := by
    -- Rewrite the smoothing owner to `½ · π[2]` and pull the scalar through `iteratedFDeriv`.
    have howner :
        squaredLpMatrixNormSmoothing 1 =
          fun Y : SymmMat ↦ (1 / 2 : ℝ) • π[2] Y := by
      funext Y
      simpa [smul_eq_mul] using squaredLpMatrixNormSmoothing_eq_half_powerTraceTwo_of_one Y
    have hfunc :
        iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing 1) X =
          iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ (1 / 2 : ℝ) • π[2] Y) X := by
      simpa using
        congrArg (fun f : SymmMat → ℝ ↦ iteratedFDeriv ℝ 2 f X)
          howner
    have hsmul :
        iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ (1 / 2 : ℝ) • π[2] Y) X =
          (1 / 2 : ℝ) • iteratedFDeriv ℝ 2 (π[2] : SymmMat → ℝ) X :=
      iteratedFDeriv_const_smul_apply' hpowerCont
    calc
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing 1) X ![H, H]
          = iteratedFDeriv ℝ 2 (fun Y : SymmMat ↦ (1 / 2 : ℝ) • π[2] Y) X ![H, H] := by
              simpa using congrArg (fun T ↦ T ![H, H]) hfunc
      _ = (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 (π[2] : SymmMat → ℝ) X ![H, H] := by
            simpa [Pi.smul_apply, smul_eq_mul] using congrArg (fun T ↦ T ![H, H]) hsmul
  have hbase :
      iteratedFDeriv ℝ 2 (π[2] : SymmMat → ℝ) X ![H, H] ≤ 2 * π[2] H := by
    -- Theorem 6.9 at `k = 2` collapses to the square-power trace of `H`.
    have hsquare :
        ∑ i : Fin n,
            (((Matrix.nonneg_iff_posSemidef.mp
                (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
              (2 : ℕ)) = π[2] H := by
        simpa using ambientAbsEigenvalue_evenPowerSum_eq_powerTrace (p := (1 : ℕ+)) H
    have hpair_eq :
        ∑ i : Fin n,
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
            (2 - 2)) *
          (((Matrix.nonneg_iff_posSemidef.mp
              (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
            (2 : ℕ)) = π[2] H := by
      simpa [hsquare]
    calc
      iteratedFDeriv ℝ 2 (π[2] : SymmMat → ℝ) X ![H, H]
          ≤ (((2 * (2 - 1) : ℕ) : ℝ) *
              ∑ i : Fin n,
                (((Matrix.nonneg_iff_posSemidef.mp
                    (CFC.abs_nonneg ((X : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
                  (2 - 2)) *
                (((Matrix.nonneg_iff_posSemidef.mp
                    (CFC.abs_nonneg ((H : Matrix (Fin n) (Fin n) ℝ)))).isHermitian.eigenvalues i) ^
                  (2 : ℕ))) := by
              simpa using powerTraceIteratedFDerivTwoLeAbsEigenvaluePairingLocal 2 X H
      _ = 2 * π[2] H := by
            rw [hpair_eq]
            norm_num
  calc
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing 1) X ![H, H]
        = (1 / 2 : ℝ) * iteratedFDeriv ℝ 2 (π[2] : SymmMat → ℝ) X ![H, H] := hiter
    _ ≤ (1 / 2 : ℝ) * (2 * π[2] H) := by
          exact mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = π[2] H := by ring
    _ ≤ Real.rpow (π[2] H) (1 : ℝ) := by
          simp

/-- Helper for Proposition 6.34: in dimension `n ≤ 1`, the smoothing owner agrees with the
`p = 1` quadratic branch, so only the factor `(2p - 1) ≥ 1` remains. -/
private lemma halfPowerTraceIteratedFDerivTwoLe_of_smallDimension
    (p : ℕ+) (hn : n ≤ 1) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) X ![H, H] ≤
      (2 * (p : ℕ) - 1 : ℝ) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
  have hfactor_ge_one : (1 : ℝ) ≤ (2 * (p : ℕ) - 1 : ℝ) := by
    have hp_one_real : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt p.pos)
    nlinarith
  have hrpow_nonneg : 0 ≤ Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
    exact Real.rpow_nonneg (evenPowerTraceNonneg p H) _
  have hsmallDim_eq :
      Real.rpow (π[2] H) (1 : ℝ) =
        Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
    rw [powerTrace_two_eq_norm_sq, rpow_powerTrace_eq_normSq_of_smallDimension p hn H]
    simp
  have honeBranch :
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing 1) X ![H, H] ≤
        Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
    calc
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing 1) X ![H, H]
          ≤ Real.rpow (π[2] H) (1 : ℝ) := halfPowerTraceIteratedFDerivTwoLe_of_one X H
      _ = Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := hsmallDim_eq
  have hfactor :
      Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) ≤
        (2 * (p : ℕ) - 1 : ℝ) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
    simpa [one_mul] using mul_le_mul_of_nonneg_right hfactor_ge_one hrpow_nonneg
  calc
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) X ![H, H]
        = iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing 1) X ![H, H] := by
            rw [squaredLpMatrixNormSmoothing_eq_halfNormSq_of_smallDimension p hn,
              squaredLpMatrixNormSmoothing_eq_halfNormSq_of_one]
    _ ≤ Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := honeBranch
    _ ≤ (2 * (p : ℕ) - 1 : ℝ) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := hfactor

/-- Helper for Proposition 6.34: away from the already solved branches `n ≤ 1` and `p = 1`, the
totalized second Fréchet derivative at the origin vanishes because the Fréchet-derivative field
is not differentiable there. -/
private lemma iteratedFDerivTwo_zero_at_origin_of_notSmallDimension_of_p_ne_one
    (p : ℕ+) (hn : ¬ n ≤ 1) (hp1 : p ≠ 1) :
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) = 0 := by
  have hfdiff :
      ¬ DifferentiableAt ℝ (fderiv ℝ (squaredLpMatrixNormSmoothing p)) (0 : SymmMat) := by
    -- First isolate the origin obstruction directly at the Fréchet-derivative level.
    exact notDifferentiableAtFDeriv_zero_of_notSmallDimension_of_p_ne_one p hn hp1
  -- Then totalize the second Fréchet derivative through the nondifferentiable derivative field.
  exact iteratedFDerivTwo_eq_zero_of_not_differentiableAt_fderiv hfdiff


/-- Helper for Proposition 6.34: the zero-trace branch of the smoothing Hessian estimate. -/
private lemma halfPowerTraceIteratedFDerivTwoLe_of_powerTrace_eq_zero
    (p : ℕ+) (X H : SymmMat) (hX : π[2 * (p : ℕ)] X = 0) :
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) X ![H, H] ≤
      (2 * (p : ℕ) - 1 : ℝ) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
  -- Route correction: the raw `rpow` chain rule fails at the zero base, so this branch has to be
  -- proved by first identifying `X = 0` and then using the exact quadratic ray behavior.
  have hX0 : X = 0 := (evenPowerTrace_eq_zero_iff p X).mp hX
  subst hX0
  have hray :
      ∀ t : ℝ,
        squaredLpMatrixNormSmoothing p (t • H) =
          ((1 / 2 : ℝ) * (t ^ (2 : ℕ))) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
    -- The source owner is exactly quadratic along every ray through the origin.
    intro t
    simpa using squaredLpMatrixNormSmoothing_smul p t H
  by_cases hn : n ≤ 1
  · -- In the low-dimensional branch the smoothing owner is already quadratic, so the earlier exact
    -- quadratic proof closes the origin case directly.
    simpa using halfPowerTraceIteratedFDerivTwoLe_of_smallDimension p hn (0 : SymmMat) H
  by_cases hp1 : p = 1
  · -- The exact quadratic branch `p = 1` was already stabilized above.
    subst hp1
    calc
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing 1) (0 : SymmMat) ![H, H]
          ≤ Real.rpow (π[2] H) (1 : ℝ) := halfPowerTraceIteratedFDerivTwoLe_of_one (0 : SymmMat) H
      _ = (2 * ((1 : ℕ+) : ℕ) - 1 : ℝ) *
            Real.rpow (π[2 * ((1 : ℕ+) : ℕ)] H) (1 / ((1 : ℕ+) : ℝ)) := by
            norm_num
  have hiter_zero :
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) = 0 :=
    iteratedFDerivTwo_zero_at_origin_of_notSmallDimension_of_p_ne_one p hn hp1
  have hrhs_nonneg :
      0 ≤ (2 * (p : ℕ) - 1 : ℝ) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
    have hfactor_nonneg : 0 ≤ (2 * (p : ℕ) - 1 : ℝ) := by
      have hp_one_real : (1 : ℝ) ≤ ((p : ℕ) : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt p.pos)
      nlinarith
    exact mul_nonneg hfactor_nonneg (Real.rpow_nonneg (evenPowerTraceNonneg p H) _)
  -- Once the origin gradient is nondifferentiable, the totalized second derivative is zero.
  calc
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) (0 : SymmMat) ![H, H]
        = 0 := by
            rw [hiter_zero]
            simp
    _ ≤ (2 * (p : ℕ) - 1 : ℝ) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := hrhs_nonneg

/-- Helper for Proposition 6.34: the ambient eigenvalue pairing in Theorem 6.9 is bounded by the
weighted geometric mean of the `2p`-power traces of `X` and `H`. -/
private lemma absEigenvaluePairing_le_powerTraceBlend
    (p : ℕ+) (X H : SymmMat) :
    ∑ i : Fin n,
      (((Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues i) ^
        (2 * (p : ℕ) - 2)) *
      (((Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((H : Mat)))).isHermitian.eigenvalues i) ^
        (2 : ℕ))
      ≤
        Real.rpow (π[2 * (p : ℕ)] X) (((p : ℝ) - 1) / (p : ℝ)) *
          Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
  let xEig : Fin n → ℝ := fun i ↦
    ((Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues i)
  let hEig : Fin n → ℝ := fun i ↦
    ((Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((H : Mat)))).isHermitian.eigenvalues i)
  have hx_nonneg : ∀ i : Fin n, 0 ≤ xEig i := by
    intro i
    dsimp [xEig]
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).eigenvalues_nonneg i
  have hh_nonneg : ∀ i : Fin n, 0 ≤ hEig i := by
    intro i
    dsimp [hEig]
    exact (Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((H : Mat)))).eigenvalues_nonneg i
  by_cases hp1 : p = 1
  · subst hp1
    -- In the exact quadratic branch, the pairing is already the `2`-power trace of `H`.
    calc
      ∑ i : Fin n, xEig i ^ (2 * (((1 : ℕ+) : ℕ)) - 2) * hEig i ^ (2 : ℕ)
          = ∑ i : Fin n, hEig i ^ (2 : ℕ) := by
              simp [xEig]
      _ = π[2] H := by
            simpa [hEig] using ambientAbsEigenvalue_evenPowerSum_eq_powerTrace (p := (1 : ℕ+)) H
      _ ≤ Real.rpow (π[2] X) ((((1 : ℕ+) : ℝ) - 1) / ((1 : ℕ+) : ℝ)) *
            Real.rpow (π[2] H) (1 / ((1 : ℕ+) : ℝ)) := by
              simp
  let a : ℝ := (((p : ℕ) : ℝ) - 1) / (p : ℝ)
  let b : ℝ := 1 / (p : ℝ)
  have hp_real_pos : 0 < (p : ℝ) := by
    exact_mod_cast p.pos
  have hp_real_ne : (p : ℝ) ≠ 0 := hp_real_pos.ne'
  have hp_gt_nat : 1 < (p : ℕ) := by
    have hp_le : 1 ≤ (p : ℕ) := Nat.succ_le_of_lt p.pos
    exact lt_of_le_of_ne hp_le (by
      intro hp_eq
      apply hp1
      exact_mod_cast hp_eq.symm)
  have hp_gt_real : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast hp_gt_nat
  have ha_pos : 0 < a := by
    dsimp [a]
    have hnum : 0 < (p : ℝ) - 1 := by
      linarith
    exact div_pos hnum hp_real_pos
  have hb_pos : 0 < b := by
    dsimp [b]
    exact one_div_pos.mpr hp_real_pos
  have hab : a + b = 1 := by
    dsimp [a, b]
    field_simp [hp_real_ne]
    ring
  have htermX :
      ∀ i : Fin n, (xEig i ^ (2 * (p : ℕ)) : ℝ) ^ a = xEig i ^ (2 * (p : ℕ) - 2) := by
    intro i
    have hxa :
        (((2 * (p : ℕ)) : ℝ) * a) = ((2 * (p : ℕ) - 2 : ℕ) : ℝ) := by
      have htwo_le : 2 ≤ 2 * (p : ℕ) := by
        omega
      have hcast : ((2 * (p : ℕ) - 2 : ℕ) : ℝ) = 2 * (p : ℝ) - 2 := by
        norm_num [Nat.cast_mul, Nat.cast_sub htwo_le]
      dsimp [a]
      rw [hcast]
      field_simp [hp_real_ne]
    -- Push the outer real power through the even natural power before simplifying the exponent.
    calc
      (xEig i ^ (2 * (p : ℕ)) : ℝ) ^ a
          = Real.rpow (xEig i) (((2 * (p : ℕ)) : ℝ) * a) := by
              simpa [mul_comm] using
                (Real.rpow_natCast_mul (hx_nonneg i) (2 * (p : ℕ)) a).symm
      _ = Real.rpow (xEig i) ((2 * (p : ℕ) - 2 : ℕ) : ℝ) := by
            rw [hxa]
      _ = xEig i ^ (2 * (p : ℕ) - 2) := by
            exact Real.rpow_natCast (xEig i) (2 * (p : ℕ) - 2)
  have htermH :
      ∀ i : Fin n, (hEig i ^ (2 * (p : ℕ)) : ℝ) ^ b = hEig i ^ (2 : ℕ) := by
    intro i
    have hhb :
        (((2 * (p : ℕ)) : ℝ) * b) = ((2 : ℕ) : ℝ) := by
      dsimp [b]
      field_simp [hp_real_ne]
    -- The `1 / p` exponent reduces the `2p`-power back to a square on each eigenvalue.
    calc
      (hEig i ^ (2 * (p : ℕ)) : ℝ) ^ b
          = Real.rpow (hEig i) (((2 * (p : ℕ)) : ℝ) * b) := by
              simpa [mul_comm] using
                (Real.rpow_natCast_mul (hh_nonneg i) (2 * (p : ℕ)) b).symm
      _ = Real.rpow (hEig i) ((2 : ℕ) : ℝ) := by
            rw [hhb]
      _ = hEig i ^ (2 : ℕ) := by
            exact Real.rpow_natCast (hEig i) 2
  have hweighted :
      ∑ i : Fin n, xEig i ^ (2 * (p : ℕ) - 2) * hEig i ^ (2 : ℕ) ≤
        (∑ i : Fin n, xEig i ^ (2 * (p : ℕ))) ^ a *
          (∑ i : Fin n, hEig i ^ (2 * (p : ℕ))) ^ b := by
    -- Apply finite Hölder to the `2p`-power vectors and rewrite each summand explicitly.
    simpa [htermX, htermH] using
      (weightedGeometricMeanSum_le
        (n := n)
        Finset.univ
        ha_pos
        hb_pos
        hab
        (fun i ↦ xEig i ^ (2 * (p : ℕ)))
        (fun i ↦ hEig i ^ (2 * (p : ℕ)))
        (by
          intro i hi
          exact pow_nonneg (hx_nonneg i) _)
        (by
          intro i hi
          exact pow_nonneg (hh_nonneg i) _))
  -- Rewrite both `2p`-power sums by the ambient absolute-value bridge.
  calc
    ∑ i : Fin n, xEig i ^ (2 * (p : ℕ) - 2) * hEig i ^ (2 : ℕ)
        ≤ (∑ i : Fin n, xEig i ^ (2 * (p : ℕ))) ^ a *
            (∑ i : Fin n, hEig i ^ (2 * (p : ℕ))) ^ b := hweighted
    _ = Real.rpow (π[2 * (p : ℕ)] X) (((p : ℝ) - 1) / (p : ℝ)) *
          Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
          rw [ambientAbsEigenvalue_evenPowerSum_eq_powerTrace (p := p) X,
            ambientAbsEigenvalue_evenPowerSum_eq_powerTrace (p := p) H]
          rfl

/-- Helper for Proposition 6.34: away from the zero trace-power base, the smoothing owner is
`C²` because it is the positive-base `rpow` of the polynomial trace-power owner. -/
private lemma squaredLpMatrixNormSmoothing_contDiffAt_of_powerTrace_ne_zero
    (p : ℕ+) (X : SymmMat) (hX : π[2 * (p : ℕ)] X ≠ 0) :
    ContDiffAt ℝ 2 (squaredLpMatrixNormSmoothing p) X := by
  have hk : 1 ≤ 2 * (p : ℕ) := by
    have hp1 : 1 ≤ (p : ℕ) := Nat.succ_le_of_lt p.pos
    omega
  have hpower : ContDiffAt ℝ 2 (π[2 * (p : ℕ)] : SymmMat → ℝ) X := by
    exact powerTraceContDiffAtLocal (2 * (p : ℕ)) X
  -- Rewrite the owner once and compose the positive-base `rpow` regularity with the polynomial
  -- trace-power regularity.
  have hconst : ContDiffAt ℝ 2 (fun _ : SymmMat ↦ (1 / 2 : ℝ)) X := by
    exact (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : SymmMat ↦ (1 / 2 : ℝ)) X)
  change
    ContDiffAt ℝ 2
      (fun Y : SymmMat ↦
        (1 / 2 : ℝ) * Real.rpow (π[2 * (p : ℕ)] Y) (1 / (p : ℝ)))
      X
  simpa using
    (hconst.mul (hpower.rpow_const_of_ne (p := 1 / (p : ℝ)) hX))

/-- Helper for Proposition 6.34: on a positive scalar base, the concave outer map
`u ↦ (1 / 2) * u^(1 / p)` contributes a nonpositive pure-chain-rule term to the second derivative,
so only the `ψ''(0)` term remains in the upper bound. -/
private lemma scalarSecondDeriv_halfRpow_comp_le
    (p : ℕ+) (hp : 1 < (p : ℕ)) {ψ : ℝ → ℝ}
    (hψ : ContDiffAt ℝ 2 ψ 0) (hψ0 : 0 < ψ 0) :
    iteratedDeriv 2 (fun t ↦ (1 / 2 : ℝ) * Real.rpow (ψ t) (1 / (p : ℝ))) 0 ≤
      ((1 / (2 * (p : ℝ))) * Real.rpow (ψ 0) (1 / (p : ℝ) - 1)) * iteratedDeriv 2 ψ 0 := by
  let q : ℝ := 1 / (p : ℝ)
  have hp_real_pos : 0 < (p : ℝ) := by
    exact_mod_cast p.pos
  have hp_real_ne : (p : ℝ) ≠ 0 := hp_real_pos.ne'
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    exact one_div_nonneg.mpr hp_real_pos.le
  have hq_lt_one : q < 1 := by
    dsimp [q]
    have hp_real_gt_one : (1 : ℝ) < (p : ℝ) := by
      exact_mod_cast hp
    simpa [one_div] using inv_lt_one_of_one_lt₀ hp_real_gt_one
  have hq_sub_nonpos : q - 1 ≤ 0 := sub_nonpos.mpr (le_of_lt hq_lt_one)
  have hcomp :
      iteratedDeriv 2 (fun t : ℝ ↦ (ψ t) ^ q) 0 =
        iteratedDeriv 2 (fun x : ℝ ↦ x ^ q) (ψ 0) * deriv ψ 0 ^ (2 : ℕ) +
          deriv (fun x : ℝ ↦ x ^ q) (ψ 0) * iteratedDeriv 2 ψ 0 := by
    -- Use the scalar `C²` composition formula once, keeping the outer map on the stable
    -- positive-base `rpow` surface.
    simpa [Function.comp] using
      (iteratedDeriv_comp_two
        (hg := Real.contDiffAt_rpow_const (x := ψ 0) (p := q) (n := 2)
          (Or.inl hψ0.ne'))
        (hf := hψ) : _)
  have houter_second :
      iteratedDeriv 2 (fun x : ℝ ↦ x ^ q) (ψ 0) ≤ 0 := by
    -- The pure outer second derivative has the sign of `q (q - 1)`, which is nonpositive for
    -- `q = 1 / p < 1`.
    have hiter :
        iteratedDeriv 2 (fun x : ℝ ↦ x ^ q) (ψ 0) =
          (descPochhammer ℝ 2).eval q * (ψ 0) ^ (q - 2) := by
      rw [iteratedDeriv_eq_iterate]
      simpa using Real.iter_deriv_rpow_const q (ψ 0) 2
    rw [hiter]
    have hcoeff_nonpos : (q * (q - 1)) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hq_nonneg hq_sub_nonpos
    have hpow_nonneg : 0 ≤ (ψ 0) ^ (q - 2) := by
      exact Real.rpow_nonneg hψ0.le _
    simpa [descPochhammer] using mul_nonpos_of_nonpos_of_nonneg hcoeff_nonpos hpow_nonneg
  have hderiv :
      deriv (fun x : ℝ ↦ x ^ q) (ψ 0) = q * (ψ 0) ^ (q - 1) := by
    simpa using Real.deriv_rpow_const (ψ 0) q
  have hfirst_nonpos :
      (1 / 2 : ℝ) *
          (iteratedDeriv 2 (fun x : ℝ ↦ x ^ q) (ψ 0) * deriv ψ 0 ^ (2 : ℕ)) ≤
        0 := by
    have hsquare_nonneg : 0 ≤ deriv ψ 0 ^ (2 : ℕ) := by
      positivity
    have hmul_nonpos :
        iteratedDeriv 2 (fun x : ℝ ↦ x ^ q) (ψ 0) * deriv ψ 0 ^ (2 : ℕ) ≤ 0 := by
      exact mul_nonpos_of_nonpos_of_nonneg houter_second hsquare_nonneg
    nlinarith
  -- Split the second derivative into the nonpositive pure-chain-rule term and the transport term.
  rw [iteratedDeriv_const_mul_field]
  rw [show iteratedDeriv 2 (fun t : ℝ ↦ Real.rpow (ψ t) (1 / (p : ℝ))) 0 =
      iteratedDeriv 2 (fun t : ℝ ↦ (ψ t) ^ q) 0 by rfl]
  rw [hcomp]
  have hsplit :
      (1 / 2 : ℝ) *
          (iteratedDeriv 2 (fun x : ℝ ↦ x ^ q) (ψ 0) * deriv ψ 0 ^ (2 : ℕ) +
            deriv (fun x : ℝ ↦ x ^ q) (ψ 0) * iteratedDeriv 2 ψ 0)
        =
          (1 / 2 : ℝ) *
              (iteratedDeriv 2 (fun x : ℝ ↦ x ^ q) (ψ 0) * deriv ψ 0 ^ (2 : ℕ)) +
            ((1 / (2 * (p : ℝ))) * (ψ 0) ^ (q - 1)) * iteratedDeriv 2 ψ 0 := by
    rw [hderiv]
    have hq_eq : (1 / 2 : ℝ) * q = 1 / (2 * (p : ℝ)) := by
      dsimp [q]
      field_simp [hp_real_ne]
    calc
      (1 / 2 : ℝ) *
          (iteratedDeriv 2 (fun x : ℝ ↦ x ^ q) (ψ 0) * deriv ψ 0 ^ (2 : ℕ) +
            (q * (ψ 0) ^ (q - 1)) * iteratedDeriv 2 ψ 0)
          =
            (1 / 2 : ℝ) *
                (iteratedDeriv 2 (fun x : ℝ ↦ x ^ q) (ψ 0) * deriv ψ 0 ^ (2 : ℕ)) +
              ((1 / 2 : ℝ) * q) * ((ψ 0) ^ (q - 1) * iteratedDeriv 2 ψ 0) := by
                ring
      _ =
            (1 / 2 : ℝ) *
                (iteratedDeriv 2 (fun x : ℝ ↦ x ^ q) (ψ 0) * deriv ψ 0 ^ (2 : ℕ)) +
              ((1 / (2 * (p : ℝ))) * (ψ 0) ^ (q - 1)) * iteratedDeriv 2 ψ 0 := by
                rw [hq_eq]
                ring
  have htransport :
      ((1 / (2 * (p : ℝ))) * (ψ 0) ^ (q - 1)) * iteratedDeriv 2 ψ 0 =
        ((1 / (2 * (p : ℝ))) * Real.rpow (ψ 0) (1 / (p : ℝ) - 1)) * iteratedDeriv 2 ψ 0 := by
    simp [q]
  rw [hsplit]
  rw [htransport]
  simpa [add_comm, add_left_comm, add_assoc] using
    add_le_add_right hfirst_nonpos
      (((1 / (2 * (p : ℝ))) * Real.rpow (ψ 0) (1 / (p : ℝ) - 1)) * iteratedDeriv 2 ψ 0)

/-- Helper for Proposition 6.34: on the positive-trace branch, the smoothing Hessian is bounded by
the trace-power Hessian with the scalar prefactor coming from the outer `rpow` chain rule. -/
-- TODO: the mathematical route here is already correct, but the transport back from scalar slices
-- to `iteratedFDeriv` still times out through the current `ContDiffAt`/`secondDirectionalDerivative`
-- bridge on `SymmMat`. Replan this branch by refactoring that bridge to a cheaper normal form.
private lemma smoothingSecondDirectionalDerivative_le_powerTraceSecondDerivative
    (p : ℕ+) (hp : 1 < (p : ℕ)) (X H : SymmMat) (hX : π[2 * (p : ℕ)] X ≠ 0) :
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) X ![H, H] ≤
      ((1 / (2 * (p : ℝ))) * Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ) - 1)) *
        iteratedFDeriv ℝ 2 (π[2 * (p : ℕ)] : SymmMat → ℝ) X ![H, H] := by
  let ψ : ℝ → ℝ := fun t ↦ π[2 * (p : ℕ)] (X + t • H)
  have hcont_smoothing :
      ContDiffAt ℝ 2 (squaredLpMatrixNormSmoothing p) X :=
    squaredLpMatrixNormSmoothing_contDiffAt_of_powerTrace_ne_zero p X hX
  have hcont_power :
      ContDiffAt ℝ 2 (π[2 * (p : ℕ)] : SymmMat → ℝ) X :=
    powerTraceContDiffAtLocal (2 * (p : ℕ)) X
  have hcont_ψ : ContDiffAt ℝ 2 ψ 0 := by
    -- Compose the polynomial trace-power owner with the affine line through `X` in direction `H`.
    have hline : ContDiffAt ℝ 2 (fun t : ℝ ↦ X + t • H) 0 := by
      fun_prop
    have hcont_power_line :
        ContDiffAt ℝ 2 (π[2 * (p : ℕ)] : SymmMat → ℝ) ((fun t : ℝ ↦ X + t • H) 0) := by
      simpa using hcont_power
    simpa [ψ] using
      ContDiffAt.comp (x := 0) hcont_power_line hline
  have hπX_nonneg : 0 ≤ π[2 * (p : ℕ)] X := evenPowerTraceNonneg p X
  have hπX_pos : 0 < π[2 * (p : ℕ)] X := lt_of_le_of_ne hπX_nonneg (Ne.symm hX)
  have hψ0 : 0 < ψ 0 := by
    simpa [ψ] using hπX_pos
  have hslice :
      iteratedDeriv 2 (fun t : ℝ ↦ squaredLpMatrixNormSmoothing p (X + t • H)) 0 ≤
        ((1 / (2 * (p : ℝ))) * Real.rpow (ψ 0) (1 / (p : ℝ) - 1)) * iteratedDeriv 2 ψ 0 := by
    -- Apply the scalar positive-base chain-rule estimate to the affine slice.
    simpa [ψ, squaredLpMatrixNormSmoothing_eq_half_rpow_powerTrace] using
      scalarSecondDeriv_halfRpow_comp_le p hp hcont_ψ hψ0
  calc
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) X ![H, H]
        = iteratedDeriv 2 (fun t : ℝ ↦ squaredLpMatrixNormSmoothing p (X + t • H)) 0 := by
            symm
            exact
              AnalyticSymmetricSpectralFunction.slice_secondDeriv_eq_iteratedFDeriv_two
                hcont_smoothing
    _ ≤ ((1 / (2 * (p : ℝ))) * Real.rpow (ψ 0) (1 / (p : ℝ) - 1)) * iteratedDeriv 2 ψ 0 := hslice
    _ = ((1 / (2 * (p : ℝ))) * Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ) - 1)) *
          iteratedFDeriv ℝ 2 (π[2 * (p : ℕ)] : SymmMat → ℝ) X ![H, H] := by
            rw [show ψ 0 = π[2 * (p : ℕ)] X by simp [ψ]]
            rw [show iteratedDeriv 2 ψ 0 =
                iteratedFDeriv ℝ 2 (π[2 * (p : ℕ)] : SymmMat → ℝ) X ![H, H] by
              simpa [ψ] using
                AnalyticSymmetricSpectralFunction.slice_secondDeriv_eq_iteratedFDeriv_two
                  hcont_power]

/-- Helper for Proposition 6.34: the positive-trace branch of the smoothing Hessian estimate. -/
private lemma halfPowerTraceIteratedFDerivTwoLe_of_powerTrace_ne_zero
    (p : ℕ+) (X H : SymmMat) (hX : π[2 * (p : ℕ)] X ≠ 0) :
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) X ![H, H] ≤
      (2 * (p : ℕ) - 1 : ℝ) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
  by_cases hp1 : p = 1
  · -- The exact quadratic branch was already stabilized separately.
    subst hp1
    calc
      iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing 1) X ![H, H]
          ≤ Real.rpow (π[2] H) (1 : ℝ) := halfPowerTraceIteratedFDerivTwoLe_of_one X H
      _ = (2 * ((1 : ℕ+) : ℕ) - 1 : ℝ) *
            Real.rpow (π[2 * ((1 : ℕ+) : ℕ)] H) (1 / ((1 : ℕ+) : ℝ)) := by
            norm_num
  have hp : 1 < (p : ℕ) := by
    have hp_le : 1 ≤ (p : ℕ) := Nat.succ_le_of_lt p.pos
    exact lt_of_le_of_ne hp_le (by
      intro hp_eq
      apply hp1
      exact_mod_cast hp_eq.symm)
  have hπX_nonneg : 0 ≤ π[2 * (p : ℕ)] X := evenPowerTraceNonneg p X
  have hπX_pos : 0 < π[2 * (p : ℕ)] X := lt_of_le_of_ne hπX_nonneg (Ne.symm hX)
  have hp_real_pos : 0 < (p : ℝ) := by
    exact_mod_cast p.pos
  have hp_real_ne : (p : ℝ) ≠ 0 := hp_real_pos.ne'
  let pairing : ℝ :=
    ∑ i : Fin n,
      (((Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((X : Mat)))).isHermitian.eigenvalues i) ^
        (2 * (p : ℕ) - 2)) *
      (((Matrix.nonneg_iff_posSemidef.mp (CFC.abs_nonneg ((H : Mat)))).isHermitian.eigenvalues i) ^
        (2 : ℕ))
  let bound : ℝ :=
    Real.rpow (π[2 * (p : ℕ)] X) (((p : ℝ) - 1) / (p : ℝ)) *
      Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ))
  let c : ℝ :=
    (1 / (2 * (p : ℝ))) * Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ) - 1)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg hπX_nonneg _)
  have htrace :
      iteratedFDeriv ℝ 2 (π[2 * (p : ℕ)] : SymmMat → ℝ) X ![H, H] ≤
        (((2 * (p : ℕ) * (2 * (p : ℕ) - 1) : ℕ) : ℝ) * pairing) := by
    simpa [pairing] using
      powerTraceIteratedFDerivTwoLeAbsEigenvaluePairingLocal (2 * (p : ℕ)) X H
  have hpair :
      pairing ≤ bound := by
    simpa [pairing, bound] using absEigenvaluePairing_le_powerTraceBlend p X H
  have hpair_scaled :
      (((2 * (p : ℕ) * (2 * (p : ℕ) - 1) : ℕ) : ℝ) * pairing) ≤
        (((2 * (p : ℕ) * (2 * (p : ℕ) - 1) : ℕ) : ℝ) * bound) := by
    exact mul_le_mul_of_nonneg_left hpair (by positivity)
  have hcancel :
      c * ((((2 * (p : ℕ) * (2 * (p : ℕ) - 1) : ℕ) : ℝ) * bound)) =
        (2 * (p : ℕ) - 1 : ℝ) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
    have hcoeff :
        (1 / (2 * (p : ℝ))) *
            (((2 * (p : ℕ) * (2 * (p : ℕ) - 1) : ℕ) : ℝ) : ℝ) =
          (2 * (p : ℕ) - 1 : ℝ) := by
      have htwo_le : 2 ≤ 2 * (p : ℕ) := by
        omega
      field_simp [hp_real_ne]
      norm_num [Nat.cast_mul, Nat.cast_sub htwo_le]
    have hexp :
        (1 / (p : ℝ) - 1) + (((p : ℝ) - 1) / (p : ℝ)) = 0 := by
      field_simp [hp_real_ne]
      ring
    have hpow_cancel :
        Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ) - 1) *
            Real.rpow (π[2 * (p : ℕ)] X) (((p : ℝ) - 1) / (p : ℝ)) =
          1 := by
      calc
        Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ) - 1) *
            Real.rpow (π[2 * (p : ℕ)] X) (((p : ℝ) - 1) / (p : ℝ))
            =
              Real.rpow (π[2 * (p : ℕ)] X)
                ((1 / (p : ℝ) - 1) + (((p : ℝ) - 1) / (p : ℝ))) := by
                  symm
                  exact Real.rpow_add hπX_pos _ _
        _ = 1 := by
              rw [hexp]
              exact Real.rpow_zero (π[2 * (p : ℕ)] X)
    -- Cache the scalar coefficient simplification before the final closing `calc`.
    dsimp [c, bound]
    calc
      ((1 / (2 * (p : ℝ))) * Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ) - 1)) *
          ((((2 * (p : ℕ) * (2 * (p : ℕ) - 1) : ℕ) : ℝ) : ℝ) *
            (Real.rpow (π[2 * (p : ℕ)] X) (((p : ℝ) - 1) / (p : ℝ)) *
              Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ))))
          =
            ((1 / (2 * (p : ℝ))) *
                ((((2 * (p : ℕ) * (2 * (p : ℕ) - 1) : ℕ) : ℝ) : ℝ)) *
              (Real.rpow (π[2 * (p : ℕ)] X) (1 / (p : ℝ) - 1) *
                Real.rpow (π[2 * (p : ℕ)] X) (((p : ℝ) - 1) / (p : ℝ)))) *
              Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
                ring
      _ = (((2 * (p : ℕ) - 1 : ℝ) * 1)) *
            Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
              rw [hcoeff, hpow_cancel]
      _ = (2 * (p : ℕ) - 1 : ℝ) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
            ring
  -- Route correction: keep the proof on the positive scalar base, then use Theorem 6.9 and the
  -- spectral weighted-geometric-mean bound only at the final assembly step.
  calc
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) X ![H, H]
        ≤ c * iteratedFDeriv ℝ 2 (π[2 * (p : ℕ)] : SymmMat → ℝ) X ![H, H] := by
            simpa [c] using
              smoothingSecondDirectionalDerivative_le_powerTraceSecondDerivative p hp X H hX
    _ ≤ c * ((((2 * (p : ℕ) * (2 * (p : ℕ) - 1) : ℕ) : ℝ) * pairing)) := by
          exact mul_le_mul_of_nonneg_left htrace hc_nonneg
    _ ≤ c * ((((2 * (p : ℕ) * (2 * (p : ℕ) - 1) : ℕ) : ℝ) * bound)) := by
          exact mul_le_mul_of_nonneg_left hpair_scaled hc_nonneg
    _ = (2 * (p : ℕ) - 1 : ℝ) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := hcancel

/-- Proposition 6.34 [Hessian bound for `F_p`]: for real symmetric matrices `X` and `H`, the
Hessian quadratic form of the source smoothing functional
`F_p(X) = (1 / 2) * (π[2 * (p : ℕ)] X)^(1 / p) = (1 / 2) * ‖λ(X)‖_(2p)^2`
is bounded above by `(2p - 1) ‖λ(H)‖_(2p)^2`, written here via the equivalent trace-power formula
`(2p - 1) * (π[2p] H)^(1 / p)`. -/
theorem half_powerTrace_iteratedFDeriv_two_le
    (p : ℕ+) (X H : SymmMat) :
    iteratedFDeriv ℝ 2 (squaredLpMatrixNormSmoothing p) X ![H, H] ≤
      (2 * (p : ℕ) - 1 : ℝ) * Real.rpow (π[2 * (p : ℕ)] H) (1 / (p : ℝ)) := by
  -- Split on the trace-power base so the origin-totalization and positive-base branches can use
  -- their dedicated local proofs.
  by_cases hX : π[2 * (p : ℕ)] X = 0
  · exact halfPowerTraceIteratedFDerivTwoLe_of_powerTrace_eq_zero p X H hX
  · exact halfPowerTraceIteratedFDerivTwoLe_of_powerTrace_ne_zero p X H hX
