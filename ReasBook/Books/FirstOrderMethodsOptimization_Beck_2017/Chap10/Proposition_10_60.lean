/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap01.Proposition_1_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_24
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_61

local notation "Λ[" a "]" => primalCounterparts a

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp (toLp ofLp)
open InnerProductSpace (toDualMap)

section

variable {ι : Type*} [Fintype ι]

local notation "E" => WithLp 1 (ι → ℝ)
local notation "E₂" => EuclideanSpace ℝ ι
local notation "E*" => WithLp (⊤ : ENNReal) (ι → ℝ)
local notation "coordToL1" => (fun z : E₂ ↦ toLp (1 : ENNReal) (ofLp z))

/-- Helper for Proposition 10.60: the `(1, ∞)` pairing functional has operator norm equal to the
`ℓ∞` norm of its coefficient vector. -/
private lemma lpPairingDual_one_operatorNorm_eq_linf (a : E*) :
    ‖LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a))‖ = ‖ofLp a‖ := by
  -- Specialize the canonical conjugate-exponent dual-norm formula to `p = 1`.
  letI : Fact (1 ≤ (1 : ENNReal)) := ⟨le_rfl⟩
  have hone : ENNReal.conjExponent (1 : ENNReal) = ⊤ := by
    simp [ENNReal.conjExponent]
  have hconj : ‖toLp (ENNReal.conjExponent (1 : ENNReal)) (ofLp a)‖ = ‖ofLp a‖ := by
    rw [hone]
    exact PiLp.norm_toLp (β := fun _ : ι ↦ ℝ) (f := ofLp a)
  simpa [dualNorm] using
    (dualNorm_lpPairingDual_eq_conjExponent_lp_norm
      (p := (1 : ENNReal)) (y := ofLp a)).trans hconj

/-- Helper for Proposition 10.60: the `(∞, 1)` pairing functional has operator norm equal to the
`ℓ₁` norm of its coefficient vector. -/
lemma lpPairingDual_top_operatorNorm_eq_l1 (x : E) :
    ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp x))‖ = ‖x‖ := by
  -- Specialize the canonical conjugate-exponent dual-norm formula to `p = ∞`.
  letI : Fact (1 ≤ (⊤ : ENNReal)) := ⟨by simp⟩
  have htop : ENNReal.conjExponent (⊤ : ENNReal) = 1 := by
    simp [ENNReal.conjExponent]
  have hconj : ‖toLp (ENNReal.conjExponent (⊤ : ENNReal)) (ofLp x)‖ = ‖x‖ := by
    rw [htop]
  simpa [dualNorm] using
    (dualNorm_lpPairingDual_eq_conjExponent_lp_norm
      (p := (⊤ : ENNReal)) (y := ofLp x)).trans hconj

/-- Helper for Proposition 10.60: the Euclidean Riesz pairing on the coordinate model is the
coordinate dot product. -/
private lemma prop10_60_toDualMap_apply_eq_dotProduct (u v : E₂) :
    ((toDualMap ℝ E₂ v) u : ℝ) = dotProduct (ofLp u) (ofLp v) := by
  -- Convert the Euclidean inner product to the explicit coordinate formula.
  simpa [InnerProductSpace.toDualMap_apply_apply, dotProduct, mul_comm] using
    (EuclideanSpace.inner_toLp_toLp (ofLp v) (ofLp u))

/-- Helper for Proposition 10.60: pairing with the translated point `y - a` splits into the
coordinate dot product at `y` minus the dot product at `a`. -/
private lemma prop10_60_toDualMap_apply_sub_eq_dotProduct_sub (a : E*) (x : E) (y : E₂) :
    ((toDualMap ℝ E₂ (toLp 2 (ofLp x))) (y - toLp 2 (ofLp a)) : ℝ) =
      dotProduct (ofLp y) (ofLp x) - dotProduct (ofLp a) (ofLp x) := by
  -- Expand the Euclidean pairing and separate the translated contribution.
  rw [prop10_60_toDualMap_apply_eq_dotProduct]
  simp [sub_eq_add_neg, add_dotProduct, neg_dotProduct]

/-- Helper for Proposition 10.60: every `ℓ₁`-unit vector pairs with an `ℓ∞` vector by at most its
`ℓ∞` norm. -/
private lemma prop10_60_dotProduct_le_linf_of_l1_norm_le_one
    (x : E) (hx : ‖x‖ ≤ 1) (v : ι → ℝ) :
    dotProduct v (ofLp x) ≤ ‖v‖ := by
  -- Turn the `ℓ₁` bound into an operator-norm bound on the corresponding `ℓ∞` pairing map.
  have hop : ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp x))‖ ≤ 1 := by
    rw [lpPairingDual_top_operatorNorm_eq_l1]
    exact hx
  have hEval :=
    ContinuousLinearMap.le_opNorm
      (LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp x)))
      (toLp (⊤ : ENNReal) v)
  have habs :
      |dotProduct v (ofLp x)| ≤
        ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp x))‖ * ‖v‖ := by
    simpa [lpPairingDual_apply] using hEval
  have habs' : |dotProduct v (ofLp x)| ≤ ‖v‖ := by
    calc
      |dotProduct v (ofLp x)| ≤
          ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp x))‖ * ‖v‖ := habs
      _ ≤ 1 * ‖v‖ := by gcongr
      _ = ‖v‖ := by simp
  exact (le_abs_self _).trans habs'

/-- Helper for Proposition 10.60: if a coefficient vector pairs with every `ℓ∞` vector by at most
its `ℓ∞` norm, then its `ℓ₁` norm is at most `1`. -/
lemma norm_le_one_of_dotProduct_le_linf (x : E)
    (hx : ∀ v : ι → ℝ, dotProduct v (ofLp x) ≤ ‖v‖) :
    ‖x‖ ≤ 1 := by
  -- Upgrade the support bound to an operator-norm bound on the `ℓ∞` pairing functional.
  have habs : ∀ v : ι → ℝ, |dotProduct v (ofLp x)| ≤ ‖v‖ := by
    intro v
    have hv := hx v
    have hneg := hx (-v)
    have hlower : -‖v‖ ≤ dotProduct v (ofLp x) := by
      have : -(dotProduct v (ofLp x)) ≤ ‖v‖ := by
        simpa [neg_dotProduct] using hneg
      linarith
    exact abs_le.2 ⟨hlower, hv⟩
  have hop : ‖LinearMap.toContinuousLinearMap (lpPairingDual (⊤ : ENNReal) (ofLp x))‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
    intro z
    simpa [lpPairingDual_apply] using habs (ofLp z)
  -- Read the operator-norm bound back as an `ℓ₁` bound.
  rw [lpPairingDual_top_operatorNorm_eq_l1] at hop
  exact hop

/-- Helper for Proposition 10.60: membership in the `coordToL1` image is equivalent to membership
of the canonical Euclidean coordinate representative. -/
lemma coordToL1_mem_image_iff (S : Set E₂) {x : E} :
    x ∈ coordToL1 '' S ↔ toLp 2 (ofLp x) ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    refine ⟨toLp 2 (ofLp x), hx, ?_⟩
    rfl

/-- Helper for Proposition 10.60: transporting the signed active-face parameterization through
`coordToL1` only changes the target `WithLp` exponent from `2` to `1`. -/
lemma coordToL1_image_signed_map (a : E*) (S : Set (ι → ℝ)) :
    coordToL1 '' ((fun coeff : ι → ℝ ↦ toLp 2 (fun i ↦ coeff i * Real.sign (a i))) '' S) =
      (fun coeff : ι → ℝ ↦ toLp 1 (fun i ↦ coeff i * Real.sign (a i))) '' S := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨coeff, hcoeff, rfl⟩
    refine ⟨coeff, hcoeff, ?_⟩
    rfl
  · rintro ⟨coeff, hcoeff, rfl⟩
    refine ⟨toLp 2 (fun i ↦ coeff i * Real.sign (a i)), ?_, ?_⟩
    · exact ⟨coeff, hcoeff, rfl⟩
    · rfl

/-- Helper for Proposition 10.60: the Chapter 10 `Λ[lpPairingDual 1 a]` condition is equivalent
to the Euclidean `ℓ∞` subgradient condition at the same coordinate vector. -/
lemma mem_primalCounterparts_lpPairingDual_one_iff_mem_euclideanSubdifferentialAt_linf
    (a : E*) {x : E} :
    x ∈ Λ[LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a))] ↔
      toLp 2 (ofLp x) ∈
        euclideanSubdifferentialAt (fun y : E₂ ↦ ‖ofLp y‖) (toLp 2 (ofLp a)) := by
  constructor
  · intro hx
    rw [mem_euclideanSubdifferentialAt_iff, mem_strongDualSubdifferential, mem_subdifferential,
      is_subgradient_at_coe_iff]
    -- Extract the norming-vector data from the Chapter 10 owner condition.
    have hx' :
        ‖x‖ ≤ 1 ∧
          LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a)) x =
            ‖LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a))‖ := by
      simpa using hx
    have hxnorm : ‖x‖ ≤ 1 := hx'.1
    have hxa :
        dotProduct (ofLp x) (ofLp a) = ‖ofLp a‖ := by
      calc
        dotProduct (ofLp x) (ofLp a) =
            ‖LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a))‖ := by
          simpa [lpPairingDual_apply] using hx'.2
        _ = ‖ofLp a‖ := lpPairingDual_one_operatorNorm_eq_linf a
    have hxa_symm : dotProduct (ofLp a) (ofLp x) = ‖ofLp a‖ := by
      -- Commute the dot product so the later translated-pairing identities match the source term.
      simpa [dotProduct_comm] using hxa
    -- Rewrite the Euclidean subgradient inequality as the support inequality `v · x ≤ ‖v‖∞`.
    intro y
    have hy :
        dotProduct (ofLp y) (ofLp x) ≤ ‖ofLp y‖ :=
      prop10_60_dotProduct_le_linf_of_l1_norm_le_one x hxnorm (ofLp y)
    have hpair :
        ((toDualMap ℝ E₂ (toLp 2 (ofLp x))) (y - toLp 2 (ofLp a)) : ℝ) =
          dotProduct (ofLp y) (ofLp x) - ‖ofLp a‖ := by
      calc
        ((toDualMap ℝ E₂ (toLp 2 (ofLp x))) (y - toLp 2 (ofLp a)) : ℝ) =
            dotProduct (ofLp y) (ofLp x) - dotProduct (ofLp a) (ofLp x) :=
          prop10_60_toDualMap_apply_sub_eq_dotProduct_sub a x y
        _ = dotProduct (ofLp y) (ofLp x) - ‖ofLp a‖ := by
          rw [hxa_symm]
    -- Normalize the translated affine inequality back to the support estimate `y · x ≤ ‖y‖∞`.
    calc
      ‖ofLp y‖ ≥ dotProduct (ofLp y) (ofLp x) := hy
      _ = ‖ofLp a‖ + ((toDualMap ℝ E₂ (toLp 2 (ofLp x))) (y - toLp 2 (ofLp a)) : ℝ) := by
        rw [hpair]
        ring
  · intro hx
    rw [mem_euclideanSubdifferentialAt_iff, mem_strongDualSubdifferential, mem_subdifferential,
      is_subgradient_at_coe_iff] at hx
    -- First recover the supporting equality `x · a = ‖a‖∞` from the Euclidean subgradient rule.
    have hzero := hx 0
    have hge :
        ‖ofLp a‖ ≤ dotProduct (ofLp x) (ofLp a) := by
      have hpair0 :
          ((toDualMap ℝ E₂ (toLp 2 (ofLp x))) (0 - toLp 2 (ofLp a)) : ℝ) =
            -dotProduct (ofLp a) (ofLp x) := by
        calc
          ((toDualMap ℝ E₂ (toLp 2 (ofLp x))) (0 - toLp 2 (ofLp a)) : ℝ) =
              dotProduct (ofLp (0 : E₂)) (ofLp x) - dotProduct (ofLp a) (ofLp x) :=
            prop10_60_toDualMap_apply_sub_eq_dotProduct_sub a x 0
          _ = -dotProduct (ofLp a) (ofLp x) := by simp
      have hzero' : 0 ≥ ‖ofLp a‖ - dotProduct (ofLp a) (ofLp x) := by
        -- Specializing the subgradient inequality at `0` gives the lower supporting bound.
        simpa [hpair0] using hzero
      have hge' : ‖ofLp a‖ ≤ dotProduct (ofLp a) (ofLp x) := by
        linarith
      simpa [dotProduct_comm] using hge'
    have htwo := hx (toLp 2 ((2 : ℝ) • ofLp a))
    have hle :
        dotProduct (ofLp x) (ofLp a) ≤ ‖ofLp a‖ := by
      have hpair2 :
          ((toDualMap ℝ E₂ (toLp 2 (ofLp x)))
              (toLp 2 ((2 : ℝ) • ofLp a) - toLp 2 (ofLp a)) : ℝ) =
            dotProduct (ofLp a) (ofLp x) := by
        calc
          ((toDualMap ℝ E₂ (toLp 2 (ofLp x)))
              (toLp 2 ((2 : ℝ) • ofLp a) - toLp 2 (ofLp a)) : ℝ) =
            dotProduct ((2 : ℝ) • ofLp a) (ofLp x) - dotProduct (ofLp a) (ofLp x) :=
            prop10_60_toDualMap_apply_sub_eq_dotProduct_sub a x (toLp 2 ((2 : ℝ) • ofLp a))
          _ = (2 : ℝ) * dotProduct (ofLp a) (ofLp x) - dotProduct (ofLp a) (ofLp x) := by
            simp [smul_dotProduct]
          _ = dotProduct (ofLp a) (ofLp x) := by
            ring
      have hle' : dotProduct (ofLp a) (ofLp x) ≤ ‖ofLp a‖ := by
        have hnorm2 : ‖(toLp 2 ((2 : ℝ) • ofLp a)).ofLp‖ = 2 * ‖ofLp a‖ := by
          simpa using norm_smul (2 : ℝ) (ofLp a)
        have htwo' : ‖(toLp 2 ((2 : ℝ) • ofLp a)).ofLp‖ ≥
            ‖ofLp a‖ + dotProduct (ofLp a) (ofLp x) := by
          calc
            ‖(toLp 2 ((2 : ℝ) • ofLp a)).ofLp‖ ≥
                ‖ofLp a‖ +
                  ((toDualMap ℝ E₂ (toLp 2 (ofLp x)))
                    (toLp 2 ((2 : ℝ) • ofLp a) - toLp 2 (ofLp a)) : ℝ) := by
              simpa using htwo
            _ = ‖ofLp a‖ + dotProduct (ofLp a) (ofLp x) := by
              rw [hpair2]
        have htwo'' : 2 * ‖ofLp a‖ ≥ ‖ofLp a‖ + dotProduct (ofLp a) (ofLp x) := by
          simpa [hnorm2] using htwo'
        linarith
      simpa [dotProduct_comm] using hle'
    have hxa : dotProduct (ofLp x) (ofLp a) = ‖ofLp a‖ := le_antisymm hle hge
    have hxa_symm : dotProduct (ofLp a) (ofLp x) = ‖ofLp a‖ := by
      -- The symmetric form is the one that appears in the translated-pairing computations.
      simpa [dotProduct_comm] using hxa
    -- Then every coordinate vector satisfies the dual support inequality `v · x ≤ ‖v‖∞`.
    have hsupport : ∀ v : ι → ℝ, dotProduct v (ofLp x) ≤ ‖v‖ := by
      intro v
      have hv := hx (toLp 2 v)
      have hpairv :
          ((toDualMap ℝ E₂ (toLp 2 (ofLp x))) (toLp 2 v - toLp 2 (ofLp a)) : ℝ) =
            dotProduct v (ofLp x) - ‖ofLp a‖ := by
        calc
          ((toDualMap ℝ E₂ (toLp 2 (ofLp x))) (toLp 2 v - toLp 2 (ofLp a)) : ℝ) =
              dotProduct v (ofLp x) - dotProduct (ofLp a) (ofLp x) :=
            prop10_60_toDualMap_apply_sub_eq_dotProduct_sub a x (toLp 2 v)
          _ = dotProduct v (ofLp x) - ‖ofLp a‖ := by
            rw [hxa_symm]
      have hv' :
          ‖ofLp a‖ + ((toDualMap ℝ E₂ (toLp 2 (ofLp x))) (toLp 2 v - toLp 2 (ofLp a)) : ℝ) ≤ ‖v‖ := by
        simpa using hv
      -- Normalize the translated affine inequality back to the support estimate `v · x ≤ ‖v‖∞`.
      calc
        dotProduct v (ofLp x) =
            ‖ofLp a‖ + ((toDualMap ℝ E₂ (toLp 2 (ofLp x))) (toLp 2 v - toLp 2 (ofLp a)) : ℝ) := by
          rw [hpairv]
          ring
        _ ≤ ‖v‖ := hv'
    have hxnorm : ‖x‖ ≤ 1 := norm_le_one_of_dotProduct_le_linf x hsupport
    -- Reassemble the Chapter 10 owner condition from the norm bound and the equality case.
    have hpair :
        LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a)) x =
          ‖LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a))‖ := by
      calc
        LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a)) x =
            dotProduct (ofLp x) (ofLp a) := by
          simp [lpPairingDual_apply]
        _ = ‖ofLp a‖ := hxa
        _ = ‖LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a))‖ := by
          rw [lpPairingDual_one_operatorNorm_eq_linf]
    simpa using And.intro hxnorm hpair

/- Proposition 10.60 has two layers:
- `source-facing`: the Chapter 10 owner `Λ[·]` on the primal `ℓ₁` space, with the dual
  coefficient vector living in the chapter's canonical `ℓ∞` model `E*`;
- `core/canonical`: the explicit owner condition `‖x‖ ≤ 1 ∧ a x = ‖a‖`, used directly here to
  identify `Λ[·]` with the canonical norm-subdifferential owner in the coordinate proof;
- `bridge/view`: the Euclidean `ℓ∞` subdifferential computation from Proposition 3.24, used only
  through the canonical coordinate transport `coordToL1 : E₂ → E`.

The primitive data are only the `ℓ∞` coefficient vector `a : E*`. The Euclidean coordinate point
`toLp 2 (ofLp a)` and the transport `coordToL1` are derived bridge data, so the public API keeps
`Λ[LinearMap.toContinuousLinearMap (lpPairingDual 1 (ofLp a))]` as the owner surface instead of
presenting `a` primarily as a Euclidean vector or introducing a second owner for the signed
active-coordinate image. -/

-- Proof sketch: identify the coefficient vector `a : E*` with the functional
-- `LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a))` on the primal `ℓ₁`
-- space. Then rewrite the owner condition `x ∈ Λ[·]` directly into the norming equations used in
-- the Euclidean subgradient inequality, and combine that with the `ℓ∞` subdifferential
-- computation from Proposition 3.24 via the canonical coordinate transport `coordToL1`.
/-- Bridge/view form of Proposition 10.60: transporting the Euclidean subdifferential of the `ℓ∞`
norm from the coordinate model `E₂` to the primal `ℓ₁` space identifies it with the
norming-functional set
`Λ[LinearMap.toContinuousLinearMap (lpPairingDual 1 (ofLp a))]`. -/
theorem primalCounterparts_lpPairingDual_one_eq_image_euclideanSubdifferentialAt_linf
    (a : E*) :
    Λ[LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a))] =
      coordToL1 '' euclideanSubdifferentialAt (fun y : E₂ ↦ ‖ofLp y‖) (toLp 2 (ofLp a)) := by
  ext x
  -- Rewrite the image membership through the canonical Euclidean coordinate representative.
  rw [coordToL1_mem_image_iff]
  -- The remaining step is exactly the Chapter 10/Chapter 3 membership bridge.
  exact mem_primalCounterparts_lpPairingDual_one_iff_mem_euclideanSubdifferentialAt_linf a

-- Proof sketch: combine the bridge theorem
-- `primalCounterparts_lpPairingDual_one_eq_image_euclideanSubdifferentialAt_linf` with
-- Chapter 3's nonzero `ℓ∞`-subdifferential formula
-- `euclidean_subdifferentialAt_linf_eq_piecewise`. Under `a ≠ 0`, the `if`-expression in that
-- theorem reduces to the upstream owner `activeCoordinateFace (fun i ↦ |a i|)`, and
-- transporting that branch along `coordToL1` yields the signed active-coordinate convex
-- combinations without introducing a second local wrapper for that image.
/-- Proposition 10.60: for a nonzero `ℓ∞` coefficient vector `a`, the norming-functional set
`Λ[LinearMap.toContinuousLinearMap (lpPairingDual 1 (ofLp a))]` is exactly the set of signed
active-coordinate convex combinations `∑_{i ∈ I(a)} λ_i sign(a_i) e_i`, expressed here as the image
of
`activeCoordinateFace (fun i ↦ |a i|)`. -/
theorem primalCounterparts_lpPairingDual_one_eq_signed_activeCoordinateFace
    (a : E*) (ha : a ≠ 0) :
    Λ[LinearMap.toContinuousLinearMap (lpPairingDual (1 : ENNReal) (ofLp a))] =
      (fun coeff : ι → ℝ ↦ toLp 1 (fun i ↦ coeff i * Real.sign (a i))) ''
        activeCoordinateFace (fun i ↦ |a i|) := by
  -- Route correction: rather than unfolding `Λ[·]` again, reuse the proved bridge to the
  -- Euclidean `ℓ∞` subdifferential and then specialize the Chapter 3 nonzero formula.
  rw [primalCounterparts_lpPairingDual_one_eq_image_euclideanSubdifferentialAt_linf]
  have ha' : toLp 2 (ofLp a) ≠ (0 : E₂) := by
    simpa using ha
  rw [euclidean_subdifferentialAt_linf_eq_signed_activeCoordinateFace (toLp 2 (ofLp a)) ha']
  -- The only remaining bookkeeping is collapsing the outer `coordToL1` transport.
  rw [coordToL1_image_signed_map]

end
