/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_42
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Real.ConjExponents
import Mathlib.Data.Real.Sign

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open WithLp (linearEquiv ofLp toLp)

noncomputable section

section

variable {ι : Type*} [Fintype ι] {p q : ENNReal}

/-- The coordinate-pairing functional on `WithLp p (ι → ℝ)` associated to `y`. -/
def lpPairingDual (p : ENNReal) (y : ι → ℝ) : Module.Dual ℝ (WithLp p (ι → ℝ)) :=
  ((dotProductBilin ℝ ℝ).flip y).comp (linearEquiv p ℝ (ι → ℝ)).toLinearMap

/-- Evaluating `lpPairingDual p y` on `x` recovers the coordinate dot product. -/
@[simp] theorem lpPairingDual_apply (y : ι → ℝ) (x : WithLp p (ι → ℝ)) :
    lpPairingDual p y x = dotProduct (ofLp x) y :=
  rfl

/-- Helper for Proposition 1.9: multiplying a real number by its sign recovers its absolute
value. -/
private theorem real_sign_mul_eq_abs (t : ℝ) : Real.sign t * t = |t| := by
  -- Split by the sign of `t` and rewrite the absolute value in each branch.
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · simp [Real.sign_of_neg hneg, abs_of_neg hneg]
  · simp
  · simp [Real.sign_of_pos hpos, abs_of_pos hpos]

/-- Helper for Proposition 1.9: every real sign has absolute value at most `1`. -/
private theorem abs_sign_le_one (t : ℝ) : |Real.sign t| ≤ 1 := by
  -- The sign function only takes the values `-1`, `0`, and `1`.
  rcases lt_trichotomy t 0 with hneg | rfl | hpos
  · simp [Real.sign_of_neg hneg]
  · simp
  · simp [Real.sign_of_pos hpos]

/-- Helper for Proposition 1.9: a maximizing coordinate realizes the `ℓ∞` norm. -/
private theorem linf_norm_eq_abs_of_coordinate_maximizer
    (a : ι → ℝ) (i : ι) (hmax : ∀ j : ι, |a j| ≤ |a i|) :
    ‖toLp (⊤ : ENNReal) a‖ = |a i| := by
  -- Rewrite the `ℓ∞` norm as the finite supremum of coordinate norms and plug in the maximizer.
  rw [PiLp.norm_toLp, Pi.norm_def]
  have hsup : Finset.univ.sup (fun j : ι ↦ ‖a j‖₊) = ‖a i‖₊ := by
    refine le_antisymm ?_
      (@Finset.le_sup NNReal ι inferInstance inferInstance Finset.univ
        (fun j : ι ↦ ‖a j‖₊) i (Finset.mem_univ i))
    refine Finset.sup_le fun j hj ↦ ?_
    exact_mod_cast hmax j
  rw [hsup]
  simp [Real.norm_eq_abs]

-- Proof sketch: the main object is the canonical functional `lpPairingDual p y` on the `WithLp`
-- model of `ℝ^n` with its `l_p` norm. Hölder gives the upper bound
-- `|lpPairingDual p y x| ≤ ‖toLp q y‖ * ‖x‖`, while the standard finite-dimensional extremizers
-- show the bound is sharp, including the endpoint pairs `(1, ∞)` and `(∞, 1)`.
section

variable [Fact (1 ≤ p)]

/-- Helper for Proposition 1.9: transporting the owner closed ball through `ofLp` rewrites the
image of `lpPairingDual p y` as the textbook coordinate unit-ball image. -/
private theorem lpPairingDualClosedBallImage_eq_coordinateUnitImage (y : ι → ℝ) :
    (lpPairingDual p y) '' Metric.closedBall (0 : WithLp p (ι → ℝ)) 1 =
      (fun x : ι → ℝ ↦ dotProduct x y) '' {x | ‖toLp p x‖ ≤ 1} := by
  -- Move each witness back and forth across the `WithLp`/coordinate equivalence.
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨ofLp x, ?_, ?_⟩
    · simpa [mem_closedBall_zero_iff] using hx
    · simp [lpPairingDual_apply]
  · rintro ⟨x, hx, rfl⟩
    refine ⟨toLp p x, ?_, ?_⟩
    · simpa [mem_closedBall_zero_iff] using hx
    · simp [lpPairingDual_apply]

/-- Helper for Proposition 1.9: the dual norm on the owner space is the `sSup` of the textbook
coordinate pairing over the closed `l_p` unit ball. -/
private theorem unitLpPairingSsupEqDualNormAux (y : ι → ℝ) :
    sSup ((fun x : ι → ℝ ↦ dotProduct x y) '' {x | ‖toLp p x‖ ≤ 1}) =
      dualNorm (lpPairingDual p y) := by
  -- Rewrite to the closed-ball image already handled by the chapter dual-norm theorem.
  have hgreatest :
      IsGreatest ((fun x : ι → ℝ ↦ dotProduct x y) '' {x | ‖toLp p x‖ ≤ 1})
        (dualNorm (lpPairingDual p y)) := by
    rw [← lpPairingDualClosedBallImage_eq_coordinateUnitImage (p := p) (y := y)]
    simpa using dualNorm_isGreatest_on_closedBall (lpPairingDual p y)
  exact hgreatest.csSup_eq

/-- Helper for Proposition 1.9: in the `(1, ∞)` endpoint case, the coordinate pairing functional
has dual norm equal to the `ℓ∞` norm of its coefficient vector. -/
private theorem dualNorm_lpPairingDual_one_eq_linf (y : ι → ℝ) :
    dualNorm (lpPairingDual (1 : ENNReal) y) = ‖toLp (⊤ : ENNReal) y‖ := by
  classical
  let T := LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) y)
  have hupper : ‖T‖ ≤ ‖toLp (⊤ : ENNReal) y‖ := by
    -- Bound each coordinate by the `ℓ∞` norm of `y` and sum the `ℓ₁` coordinates of `x`.
    refine ContinuousLinearMap.opNorm_le_bound T (norm_nonneg _) ?_
    intro x
    calc
      ‖T x‖ = ‖dotProduct (ofLp x) y‖ := by
        simp [T, lpPairingDual_apply]
      _ ≤ ∑ i, ‖ofLp x i * y i‖ := by
        simpa [dotProduct] using norm_sum_le Finset.univ (fun i : ι ↦ ofLp x i * y i)
      _ = ∑ i, ‖ofLp x i‖ * ‖y i‖ := by
        simp [norm_mul]
      _ ≤ ∑ i, ‖ofLp x i‖ * ‖toLp (⊤ : ENNReal) y‖ := by
        refine Finset.sum_le_sum ?_
        intro i hi
        gcongr
        simpa using (PiLp.norm_apply_le (toLp (⊤ : ENNReal) y) i)
      _ = ∑ i, ‖toLp (⊤ : ENNReal) y‖ * ‖ofLp x i‖ := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        rw [mul_comm]
      _ = ‖toLp (⊤ : ENNReal) y‖ * ∑ i, ‖ofLp x i‖ := by
        rw [Finset.mul_sum]
      _ = ‖toLp (⊤ : ENNReal) y‖ * ‖x‖ := by
        rw [PiLp.norm_eq_of_L1]
  by_cases hι : Nonempty ι
  · letI := hι
    obtain ⟨i, hmax⟩ := Finite.exists_max (fun j : ι ↦ |y j|)
    have hunit :
        ‖toLp (1 : ENNReal) (Pi.single i (Real.sign (y i)) : ι → ℝ)‖ ≤ 1 := by
      -- The signed basis vector has `ℓ₁` norm at most one.
      calc
        ‖toLp (1 : ENNReal) (Pi.single i (Real.sign (y i)) : ι → ℝ)‖ =
            ‖Real.sign (y i)‖ := by
          simp
        _ ≤ 1 := by
          rcases lt_trichotomy (y i) 0 with hneg | hzero | hpos
          · simp [Real.sign_of_neg hneg]
          · simp [hzero]
          · simp [Real.sign_of_pos hpos]
    have hvalue :
        ‖T (toLp (1 : ENNReal) (Pi.single i (Real.sign (y i)) : ι → ℝ))‖ = |y i| := by
      -- Pairing against the signed basis vector isolates the maximizing coordinate.
      have hsignmul : |Real.sign (y i) * y i| = |y i| := by
        rcases lt_trichotomy (y i) 0 with hneg | hzero | hpos
        · simp [Real.sign_of_neg hneg, abs_of_neg hneg]
        · simp [hzero]
        · simp [Real.sign_of_pos hpos, abs_of_pos hpos]
      simpa [T, lpPairingDual_apply, single_dotProduct, Real.norm_eq_abs] using hsignmul
    have hcoord : ‖toLp (⊤ : ENNReal) y‖ = |y i| :=
      linf_norm_eq_abs_of_coordinate_maximizer y i hmax
    have hlower : ‖toLp (⊤ : ENNReal) y‖ ≤ ‖T‖ := by
      -- The maximizing coordinate witness attains the operator norm lower bound.
      calc
        ‖toLp (⊤ : ENNReal) y‖ =
            ‖T (toLp (1 : ENNReal) (Pi.single i (Real.sign (y i)) : ι → ℝ))‖ := by
          rw [hcoord, hvalue]
        _ ≤ ‖T‖ := by
          simpa [T] using
            T.unit_le_opNorm
              (toLp (1 : ENNReal) (Pi.single i (Real.sign (y i)) : ι → ℝ)) hunit
    rw [dualNorm_eq_toContinuousLinearMap_norm]
    exact le_antisymm hupper hlower
  · haveI : IsEmpty ι := not_nonempty_iff.mp hι
    have hy : y = 0 := Subsingleton.elim _ _
    -- In the empty-index case every vector and pairing functional is zero.
    rw [dualNorm_eq_toContinuousLinearMap_norm]
    simp [hy]

/-- Helper for Proposition 1.9: the coordinate sign vector has `ℓ∞` norm at most `1`. -/
private theorem coordinateSignVector_norm_le_one (y : ι → ℝ) :
    ‖toLp (⊤ : ENNReal) (fun i : ι ↦ Real.sign (y i))‖ ≤ 1 := by
  -- Each coordinate sign has norm at most one, so their supremum does too.
  have hnn : ‖toLp (⊤ : ENNReal) (fun i : ι ↦ Real.sign (y i))‖₊ ≤ (1 : NNReal) := by
    rw [PiLp.nnnorm_toLp, Pi.nnnorm_def]
    refine Finset.sup_le fun i hi ↦ ?_
    exact_mod_cast abs_sign_le_one (y i)
  exact_mod_cast hnn

/-- Helper for Proposition 1.9: in the `(∞, 1)` endpoint case, the coordinate pairing functional
has dual norm equal to the `ℓ₁` norm of its coefficient vector. -/
private theorem dualNorm_lpPairingDual_top_eq_l1 (y : ι → ℝ) :
    dualNorm (lpPairingDual (⊤ : ENNReal) y) = ‖toLp (1 : ENNReal) y‖ := by
  letI : Fact (1 ≤ (⊤ : ENNReal)) := ⟨by simp⟩
  let T := LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) y)
  have hupper : ‖T‖ ≤ ‖toLp (1 : ENNReal) y‖ := by
    -- Bound each coordinate of `x` by its `ℓ∞` norm and sum the absolute coefficients of `y`.
    refine ContinuousLinearMap.opNorm_le_bound T (norm_nonneg _) ?_
    intro x
    calc
      ‖T x‖ = ‖dotProduct (ofLp x) y‖ := by
        simp [T, lpPairingDual_apply]
      _ ≤ ∑ i, ‖ofLp x i * y i‖ := by
        simpa [dotProduct] using norm_sum_le Finset.univ (fun i : ι ↦ ofLp x i * y i)
      _ = ∑ i, |ofLp x i| * |y i| := by
        simp [Real.norm_eq_abs]
      _ ≤ ∑ i, ‖x‖ * |y i| := by
        refine Finset.sum_le_sum ?_
        intro i hi
        gcongr
        simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le x i)
      _ = ‖x‖ * ∑ i, |y i| := by
        rw [Finset.mul_sum]
      _ = ‖x‖ * ‖toLp (1 : ENNReal) y‖ := by
        rw [PiLp.norm_eq_of_L1]
        simp [Real.norm_eq_abs]
      _ = ‖toLp (1 : ENNReal) y‖ * ‖x‖ := by
        ring
  have hunit : ‖toLp (⊤ : ENNReal) (fun i : ι ↦ Real.sign (y i))‖ ≤ 1 :=
    coordinateSignVector_norm_le_one y
  have hvalue :
      ‖T (toLp (⊤ : ENNReal) (fun i : ι ↦ Real.sign (y i)))‖ =
        ‖toLp (1 : ENNReal) y‖ := by
    -- Pairing against the sign vector adds the absolute values of the coefficients.
    have hsum_nonneg : 0 ≤ ∑ i, |y i| := by
      exact Finset.sum_nonneg fun i hi ↦ abs_nonneg _
    calc
      ‖T (toLp (⊤ : ENNReal) (fun i : ι ↦ Real.sign (y i)))‖ =
          |dotProduct (fun i : ι ↦ Real.sign (y i)) y| := by
        simp [T, lpPairingDual_apply, Real.norm_eq_abs]
      _ = abs (∑ i, |y i|) := by
        congr 1
        rw [dotProduct]
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact real_sign_mul_eq_abs (y i)
      _ = ∑ i, |y i| := abs_of_nonneg hsum_nonneg
      _ = ‖toLp (1 : ENNReal) y‖ := by
        symm
        rw [PiLp.norm_eq_of_L1]
        simp [Real.norm_eq_abs]
  have hlower : ‖toLp (1 : ENNReal) y‖ ≤ ‖T‖ := by
    -- The sign vector witness attains the operator norm lower bound.
    calc
      ‖toLp (1 : ENNReal) y‖ =
          ‖T (toLp (⊤ : ENNReal) (fun i : ι ↦ Real.sign (y i)))‖ := by
        rw [hvalue]
      _ ≤ ‖T‖ := by
        simpa [T] using
          T.unit_le_opNorm (toLp (⊤ : ENNReal) (fun i : ι ↦ Real.sign (y i))) hunit
  rw [dualNorm_eq_toContinuousLinearMap_norm]
  exact le_antisymm hupper hlower

/-- Helper for Proposition 1.9: in the strict finite case `1 < p.toReal`, the coordinate pairing
functional has dual norm equal to the canonical conjugate-exponent norm. -/
private theorem dualNorm_lpPairingDual_eq_conjExponentLp_of_one_lt_toReal
    (hp : 1 < p.toReal) (y : ι → ℝ) :
    dualNorm (lpPairingDual p y) = ‖toLp (ENNReal.conjExponent p) y‖ := by
  letI : Fact (1 ≤ ENNReal.conjExponent p) :=
    ⟨ENNReal.HolderConjugate.one_le (ENNReal.conjExponent p) p⟩
  let T := LinearMap.toContinuousLinearMap (lpPairingDual p y)
  have hpqReal : p.toReal.HolderConjugate (ENNReal.conjExponent p).toReal :=
    ENNReal.HolderConjugate.toReal hp
  have hupper : ‖T‖ ≤ ‖toLp (ENNReal.conjExponent p) y‖ := by
    -- Hölder bounds the pairing by the product of the `ℓ_p` and `ℓ_q` norms.
    let M : ℝ := ‖toLp (ENNReal.conjExponent p) y‖
    have hMnonneg : 0 ≤ M := by
      unfold M
      exact norm_nonneg (toLp (ENNReal.conjExponent p) y)
    refine ContinuousLinearMap.opNorm_le_bound T hMnonneg ?_
    intro x
    have hpPos : 0 < p.toReal := lt_trans zero_lt_one hp
    have hqPos : 0 < (ENNReal.conjExponent p).toReal := hpqReal.symm.pos
    calc
      ‖T x‖ = ‖∑ i, ofLp x i * y i‖ := by
        simp [T, lpPairingDual_apply, dotProduct]
      _ ≤ ∑ i, ‖ofLp x i * y i‖ := by
        simpa using norm_sum_le Finset.univ (fun i : ι ↦ ofLp x i * y i)
      _ = ∑ i, |ofLp x i| * |y i| := by
        simp [Real.norm_eq_abs]
      _ ≤ (∑ i, |ofLp x i| ^ p.toReal) ^ (1 / p.toReal) *
            (∑ i, |y i| ^ (ENNReal.conjExponent p).toReal) ^
              (1 / (ENNReal.conjExponent p).toReal) := by
        simpa using
          (Real.inner_le_Lp_mul_Lq (s := Finset.univ) (f := fun i : ι ↦ |ofLp x i|)
            (g := fun i : ι ↦ |y i|) hpqReal)
      _ = ‖x‖ * ‖toLp (ENNReal.conjExponent p) y‖ := by
        rw [PiLp.norm_eq_sum hpPos x,
          PiLp.norm_eq_sum hqPos (toLp (ENNReal.conjExponent p) y)]
        simp [Real.norm_eq_abs]
      _ = M * ‖x‖ := by
        simp [M, mul_comm]
  have hlower : ‖toLp (ENNReal.conjExponent p) y‖ ≤ ‖T‖ := by
    -- Transport the `NNReal.isGreatest_Lp` extremizer to a signed real witness in the `ℓ_p` ball.
    let f : ι → NNReal := fun i ↦ ⟨|y i|, abs_nonneg _⟩
    have hgreatest := NNReal.isGreatest_Lp (s := Finset.univ) f hpqReal.symm
    rcases hgreatest.1 with ⟨g, hgball, hgvalue⟩
    let x : ι → ℝ := fun i ↦ Real.sign (y i) * (g i : ℝ)
    have hpPos : 0 < p.toReal := lt_trans zero_lt_one hp
    have hxnorm : ‖toLp p x‖ ≤ 1 := by
      have hpow_le : ∑ i, |x i| ^ p.toReal ≤ ∑ i, (g i : ℝ) ^ p.toReal := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hxle : |x i| ≤ (g i : ℝ) := by
          calc
            |x i| = |Real.sign (y i)| * (g i : ℝ) := by
              simp [x, abs_mul]
            _ ≤ 1 * (g i : ℝ) := by
              gcongr
              exact abs_sign_le_one (y i)
            _ = (g i : ℝ) := by
              ring
        exact Real.rpow_le_rpow (abs_nonneg _) hxle hpPos.le
      have hgballReal : ∑ i, (g i : ℝ) ^ p.toReal ≤ 1 := by
        exact_mod_cast hgball
      have hxsum_nonneg : 0 ≤ ∑ i, |x i| ^ p.toReal := by
        refine Finset.sum_nonneg fun i hi ↦ ?_
        exact Real.rpow_nonneg (abs_nonneg _) _
      have hsum_nonneg : 0 ≤ ∑ i, (g i : ℝ) ^ p.toReal := by
        refine Finset.sum_nonneg fun i hi ↦ ?_
        exact Real.rpow_nonneg (show 0 ≤ (g i : ℝ) by exact_mod_cast (g i).property) _
      calc
        ‖toLp p x‖ = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal) := by
          rw [PiLp.norm_eq_sum hpPos (toLp p x)]
          simp [x]
        _ ≤ (∑ i, (g i : ℝ) ^ p.toReal) ^ (1 / p.toReal) := by
          exact Real.rpow_le_rpow hxsum_nonneg hpow_le (by positivity)
        _ ≤ 1 := by
          exact Real.rpow_le_one hsum_nonneg hgballReal (by positivity)
    have hgvalueNN : ((∑ i, f i * g i) : NNReal) = ‖toLp (ENNReal.conjExponent p) y‖₊ := by
      have hqPos : 0 < (ENNReal.conjExponent p).toReal := hpqReal.symm.pos
      have hqTop : ENNReal.conjExponent p ≠ ⊤ := by
        intro hqTop
        simp [hqTop] at hqPos
      have hnormq : ‖toLp (ENNReal.conjExponent p) y‖₊ =
          (∑ i, f i ^ (ENNReal.conjExponent p).toReal) ^
            (1 / (ENNReal.conjExponent p).toReal) := by
        rw [PiLp.nnnorm_eq_sum hqTop (toLp (ENNReal.conjExponent p) y)]
        rfl
      exact hgvalue.trans hnormq.symm
    have hgvalueReal : ∑ i, (f i : ℝ) * (g i : ℝ) = ‖toLp (ENNReal.conjExponent p) y‖ := by
      calc
        ∑ i, (f i : ℝ) * (g i : ℝ) = ((∑ i, f i * g i) : ℝ) := by
          norm_num
        _ = (((‖toLp (ENNReal.conjExponent p) y‖₊ : NNReal)) : ℝ) := by
          exact_mod_cast hgvalueNN
        _ = ‖toLp (ENNReal.conjExponent p) y‖ := by
          rfl
    have hsum_eq : ∑ i, (g i : ℝ) * |y i| = ∑ i, (f i : ℝ) * (g i : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      calc
        (g i : ℝ) * |y i| = (g i : ℝ) * (f i : ℝ) := by
          rfl
        _ = (f i : ℝ) * (g i : ℝ) := by
          ring
    have hdot : dotProduct x y = ∑ i, (g i : ℝ) * |y i| := by
      rw [dotProduct]
      refine Finset.sum_congr rfl ?_
      intro i hi
      dsimp [x]
      calc
        Real.sign (y i) * (g i : ℝ) * y i = (g i : ℝ) * (Real.sign (y i) * y i) := by
          ring
        _ = (g i : ℝ) * |y i| := by
          rw [real_sign_mul_eq_abs]
    have hvalue : ‖T (toLp p x)‖ = ‖toLp (ENNReal.conjExponent p) y‖ := by
      have hsum_nonneg : 0 ≤ ∑ i, (g i : ℝ) * |y i| := by
        refine Finset.sum_nonneg fun i hi ↦ ?_
        exact mul_nonneg (show 0 ≤ (g i : ℝ) by exact_mod_cast (g i).property) (abs_nonneg _)
      calc
        ‖T (toLp p x)‖ = |dotProduct x y| := by
          simp [T, lpPairingDual_apply, Real.norm_eq_abs]
        _ = abs (∑ i, (g i : ℝ) * |y i|) := by
          rw [hdot]
        _ = ∑ i, (g i : ℝ) * |y i| := abs_of_nonneg hsum_nonneg
        _ = ‖toLp (ENNReal.conjExponent p) y‖ := by
          rw [hsum_eq, hgvalueReal]
    calc
      ‖toLp (ENNReal.conjExponent p) y‖ = ‖T (toLp p x)‖ := hvalue.symm
      _ ≤ ‖T‖ := by
        simpa [T] using T.unit_le_opNorm (toLp p x) hxnorm
  rw [dualNorm_eq_toContinuousLinearMap_norm]
  exact le_antisymm hupper hlower

/-- Helper for Proposition 1.9: the owner dual norm agrees with the canonical conjugate-exponent
norm after splitting off the endpoint exponents and the strict finite branch. -/
private theorem dualNormLpPairingDualEqConjExponentLpNormAux (y : ι → ℝ) :
    dualNorm (lpPairingDual p y) = ‖toLp (ENNReal.conjExponent p) y‖ := by
  -- Route correction: handle the endpoint exponents directly, and use the `NNReal` extremizer
  -- only in the strict finite branch where Hölder conjugacy lives in `ℝ`.
  by_cases hp1 : p = 1
  · subst p
    have hone : ENNReal.conjExponent (1 : ENNReal) = ⊤ := by
      simp [ENNReal.conjExponent]
    calc
      dualNorm (lpPairingDual (1 : ENNReal) y) = ‖toLp (⊤ : ENNReal) y‖ :=
        dualNorm_lpPairingDual_one_eq_linf y
      _ = ‖toLp (ENNReal.conjExponent (1 : ENNReal)) y‖ := by
        rw [hone]
  · by_cases hpTop : p = ⊤
    · subst p
      have htop : ENNReal.conjExponent (⊤ : ENNReal) = 1 := by
        simp [ENNReal.conjExponent]
      calc
        dualNorm (lpPairingDual (⊤ : ENNReal) y) = ‖toLp (1 : ENNReal) y‖ :=
          dualNorm_lpPairingDual_top_eq_l1 y
        _ = ‖toLp (ENNReal.conjExponent (⊤ : ENNReal)) y‖ := by
          rw [htop]
    · have hp1le : 1 ≤ p.toReal := by
        exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top hpTop).2 Fact.out
      have hpRealNe : p.toReal ≠ 1 := by
        intro hpRealEq
        apply hp1
        exact (ENNReal.toReal_eq_one_iff p).mp hpRealEq
      have hpReal : 1 < p.toReal := lt_of_le_of_ne hp1le hpRealNe.symm
      exact dualNorm_lpPairingDual_eq_conjExponentLp_of_one_lt_toReal hpReal y

/-- Proposition 1.9: on the canonical `l_p` owner, the source-facing `sSup` of the coordinate
pairing realizes the canonical conjugate-exponent norm. -/
private theorem unitLpPairingSsupEqConjExponentLpNormAux (y : ι → ℝ) :
    sSup ((fun x : ι → ℝ ↦ dotProduct x y) '' {x | ‖toLp p x‖ ≤ 1}) =
      ‖toLp (ENNReal.conjExponent p) y‖ := by
  -- Read the source-facing supremum through the owner dual norm, then use the branchwise owner
  -- computation proved above.
  rw [unitLpPairingSsupEqDualNormAux, dualNormLpPairingDualEqConjExponentLpNormAux]

/-- On the canonical `l_p` owner, the dual norm of the coordinate pairing is the `l_q` norm for
the canonical conjugate exponent `q = ENNReal.conjExponent p`. -/
theorem dualNorm_lpPairingDual_eq_conjExponent_lp_norm (y : ι → ℝ) :
    dualNorm (lpPairingDual p y) = ‖toLp (ENNReal.conjExponent p) y‖ := by
  -- The owner-level formula is exactly the branchwise computation established above.
  exact dualNormLpPairingDualEqConjExponentLpNormAux (p := p) y

/-- The source-facing supremum formula is the unit-ball realization of the dual norm of
`lpPairingDual p y`. -/
theorem unit_lp_pairing_sSup_eq_dualNorm (y : ι → ℝ) :
    sSup ((fun x : ι → ℝ ↦ dotProduct x y) '' {x | ‖toLp p x‖ ≤ 1}) =
      dualNorm (lpPairingDual p y) := by
  -- This is exactly the transport lemma from the owner closed ball to coordinates.
  exact unitLpPairingSsupEqDualNormAux (p := p) y

-- Proof sketch: combine the owner-level dual-norm computation with the unit-ball companion.
/-- On the canonical `l_p` owner, the supremum of the coordinate pairing over the closed unit
ball is the norm of the coefficient vector in the canonical conjugate exponent. -/
theorem unit_lp_pairing_sSup_eq_conjExponent_lp_norm (y : ι → ℝ) :
    sSup ((fun x : ι → ℝ ↦ dotProduct x y) '' {x | ‖toLp p x‖ ≤ 1}) =
      ‖toLp (ENNReal.conjExponent p) y‖ :=
  by
  -- Reuse the direct source-facing supremum computation.
  exact unitLpPairingSsupEqConjExponentLpNormAux (p := p) y

end

namespace ENNReal.HolderConjugate

/-- A Hölder-conjugate pair canonically supplies the lower bound `1 ≤ p`. -/
theorem oneLeLeft (hpq : ENNReal.HolderConjugate p q) : 1 ≤ p := by
  letI : ENNReal.HolderConjugate p q := hpq
  simpa using ENNReal.HolderConjugate.one_le p q

/-- A Hölder-conjugate pair canonically supplies `Fact (1 ≤ p)`. -/
abbrev factOneLeLeft (hpq : ENNReal.HolderConjugate p q) : Fact (1 ≤ p) :=
  ⟨oneLeLeft hpq⟩

/-- A Hölder-conjugate pair canonically supplies the lower bound `1 ≤ q`. -/
theorem oneLeRight (hpq : ENNReal.HolderConjugate p q) : 1 ≤ q := by
  letI : ENNReal.HolderConjugate q p := hpq.symm
  simpa using ENNReal.HolderConjugate.one_le q p

/-- A Hölder-conjugate pair canonically supplies `Fact (1 ≤ q)`. -/
abbrev factOneLeRight (hpq : ENNReal.HolderConjugate p q) : Fact (1 ≤ q) :=
  ⟨oneLeRight hpq⟩

end ENNReal.HolderConjugate

private theorem conjExponent_eq_of_holderConjugate
    (hpq : ENNReal.HolderConjugate p q) : ENNReal.conjExponent p = q := by
  letI : ENNReal.HolderConjugate p q := hpq
  exact ENNReal.HolderConjugate.conjExponent_eq

/-- Source-facing bridge for Proposition 1.9: the dual norm of the coordinate-pairing functional
on `WithLp p (ι → ℝ)` is the `l_q` norm of the coefficient vector whenever `p` and `q` are
Hölder-conjugate. -/
abbrev dualNorm_lpPairingDual_eq_conjugate_lp_norm
    (hpq : ENNReal.HolderConjugate p q) (y : ι → ℝ) := by
  letI : Fact (1 ≤ p) := ENNReal.HolderConjugate.factOneLeLeft hpq
  have hcanon : dualNorm (lpPairingDual p y) = ‖toLp (ENNReal.conjExponent p) y‖ :=
    dualNorm_lpPairingDual_eq_conjExponent_lp_norm y
  simpa [conjExponent_eq_of_holderConjugate hpq] using hcanon

/-- The supremum of the coordinate pairing over the closed `l_p` unit ball is the conjugate
`l_q` norm. -/
theorem unit_lp_pairing_sSup_eq_conjugate_lp_norm
    (hpq : ENNReal.HolderConjugate p q) (y : ι → ℝ) :
    sSup ((fun x : ι → ℝ ↦ dotProduct x y) '' {x | ‖toLp p x‖ ≤ 1}) =
      ‖toLp q y‖ := by
  letI : Fact (1 ≤ p) := ENNReal.HolderConjugate.factOneLeLeft hpq
  rw [← conjExponent_eq_of_holderConjugate hpq]
  exact unit_lp_pairing_sSup_eq_conjExponent_lp_norm y

end
