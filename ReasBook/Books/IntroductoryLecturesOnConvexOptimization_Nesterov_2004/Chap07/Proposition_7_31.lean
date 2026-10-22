/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_56

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open SetConstrainedMinimizationProblem

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)

/- Proposition 7.31 lies in Chapter 7's fractional-covering / nonnegative-orthant normalization
domain.

Sampled owner-style declarations:
- `EuclideanSpace.nonnegativeOrthant` in `Chap01/Definition_1_10_2`, the project owner for the
  orthant constraints `y ≥ 0`;
- `IsPositivelyHomogeneousOn` in `Chap03/Definition_3_1_7`, the chapter owner for positive
  homogeneity on cones;
- `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  `EReal` owner for infima over explicit feasible sets;
- `maximalValueOn` in `Chap07/Definition_7_56`, the Chapter 7 maximization-side owner for
  suprema over explicit feasible sets;
- `FractionalCoveringProblem.optimalValue` in `Chap07/Definition_7_67`, the nearby chapter owner
  showing the same fractional-covering domain should route source values through those `EReal`
  optimization owners.

Best owner abstraction:
- source-facing: the Proposition 7.31 values `φ⋆`, the reciprocal-ratio supremum, and the
  normalized-slice supremum;
- core/canonical: `nonnegativeOrthant`, `IsPositivelyHomogeneousOn`,
  `SetConstrainedMinimizationProblem.optimalValue`, and `maximalValueOn`;
- bridge/view: the comparison theorems relating those three values.

Primitive data:
- `b : E` and `ψ : E → ℝ`;
- the three feasible subsets of `nonnegativeOrthant m` cut out by the side conditions
  `y ≠ 0`, `0 < ⟪b, y⟫`, and `⟪b, y⟫ = 1`.

Derived API:
- the source-facing value names below, implemented through the canonical `EReal` optimization
  owners;
- the reciprocal and normalization identities proved below.

Source/core/bridge triage:
- source-facing: `fractionalCoveringPhiStar`, `fractionalCoveringReciprocalPsiSup`, and
  `fractionalCoveringNormalizedPsiSup`;
- core/canonical: `nonnegativeOrthant`, `IsPositivelyHomogeneousOn`, `optimalValue`, and
  `maximalValueOn`;
- bridge/view: `fractionalCoveringPhiStar_eq_inv_reciprocalPsiSup`,
  `fractionalCoveringReciprocalPsiSup_eq_normalizedPsiSup`, and
  `fractionalCoveringPhiStar_eq_inv_normalizedPsiSup`.

This refinement removes the duplicate raw-`ℝ` extremum wheel and the duplicate raw positive-
homogeneity binder. The three Proposition 7.31 values remain the public source-facing names, but
they are thin bridges to the project's canonical `EReal` optimization owners, and the
homogeneity input is stated through the chapter owner `IsPositivelyHomogeneousOn`. The owner
`fractionalCoveringPhiStar` keeps the source-facing feasible set `y ≥ 0, y ≠ 0`, while the bridge
theorems carry only the positivity hypotheses on `b` and `ψ` that are needed to justify the ratio
reformulation and the nonempty-domain reading of the source min/max notation.
-/

/-- The infimum `φ⋆ = inf_{y ≥ 0, y ≠ 0} ⟪b, y⟫ / ψ(y)` attached to a positively homogeneous
function on the nonnegative orthant. Positivity of `ψ` on this feasible set is a separate
hypothesis of the bridge theorems below, not part of the owner definition. -/
def fractionalCoveringPhiStar
    (b : E) (ψ : E → ℝ) : EReal :=
  (.mk (nonnegativeOrthant m ∩ {y | y ≠ 0}) (fun y : E ↦ inner ℝ b y / ψ y) :
    SetConstrainedMinimizationProblem E).optimalValue

/-- The supremum of the reciprocal ratio `ψ(y) / ⟪b, y⟫` over the nonnegative orthant where the
pairing with `b` is strictly positive. -/
def fractionalCoveringReciprocalPsiSup
    (b : E) (ψ : E → ℝ) : EReal :=
  maximalValueOn (nonnegativeOrthant m ∩ {y | 0 < inner ℝ b y})
    (fun y : E ↦ ψ y / inner ℝ b y)

/-- The supremum of `ψ` over the normalized nonnegative slice `⟪b, y⟫ = 1`. -/
def fractionalCoveringNormalizedPsiSup
    (b : E) (ψ : E → ℝ) : EReal :=
  maximalValueOn (nonnegativeOrthant m ∩ {y | inner ℝ b y = 1}) ψ

/-- Helper for Proposition 7.31: the nonzero nonnegative orthant is nonempty as soon as `Fin m`
is. -/
private theorem nonnegativeOrthant_nonzero_nonempty [Nonempty (Fin m)] :
    (nonnegativeOrthant m ∩ {y : E | y ≠ 0}).Nonempty := by
  classical
  let i : Fin m := Classical.choice ‹Nonempty (Fin m)›
  let y : E := EuclideanSpace.single i (1 : ℝ)
  refine ⟨y, ?_⟩
  constructor
  · intro j
    by_cases hji : j = i
    · subst hji
      simp [y, EuclideanSpace.single]
    · simp [y, EuclideanSpace.single, hji]
  · intro hy0
    have hi1 : y i = 1 := by
      simp [y, EuclideanSpace.single]
    have hi0 : y i = 0 := by
      simp [hy0]
    linarith

/-- Helper for Proposition 7.31: a nonempty nonnegative feasible image can be read through the
owner `optimalValue` as a finite `ℝ≥0∞` infimum. -/
private theorem optimalValue_eq_coe_sInf_of_nonempty_nonneg
    {X : Type*} (Q : Set X) (g : X → ℝ) (hQ : Q.Nonempty)
    (hnonneg : ∀ x ∈ Q, 0 ≤ g x) :
    (.mk Q g : SetConstrainedMinimizationProblem X).optimalValue =
      (((sInf ((fun x ↦ ENNReal.ofReal (g x)) '' Q) : ENNReal)) : EReal) := by
  rw [SetConstrainedMinimizationProblem.optimalValue_eq_sInf_image]
  let S : Set ENNReal := (fun x ↦ ENNReal.ofReal (g x)) '' Q
  have hs :
      IsGLB ((fun x ↦ (g x : EReal)) '' Q) (((sInf S : ENNReal) : EReal)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxS : ENNReal.ofReal (g x) ∈ S := Set.mem_image_of_mem (fun x ↦ ENNReal.ofReal (g x)) hx
      have hle : sInf S ≤ ENNReal.ofReal (g x) := sInf_le hxS
      have hcast :
          (((sInf S : ENNReal) : EReal)) ≤ ((ENNReal.ofReal (g x) : ENNReal) : EReal) :=
        EReal.coe_ennreal_le_coe_ennreal_iff.2 hle
      have hright :
          ((ENNReal.ofReal (g x) : ENNReal) : EReal) = ((g x : ℝ) : EReal) := by
        rw [EReal.coe_ennreal_ofReal, max_eq_left (hnonneg x hx)]
      exact hcast.trans_eq hright
    · intro z hz
      by_cases hz_nonneg : 0 ≤ z
      · lift z to ENNReal using hz_nonneg with z'
        exact EReal.coe_ennreal_le_coe_ennreal_iff.2 <| le_sInf <| by
          rintro _ ⟨x, hx, rfl⟩
          have hxle : (z' : EReal) ≤ ((g x : ℝ) : EReal) := by
            exact hz (Set.mem_image_of_mem (fun x ↦ (g x : EReal)) hx)
          have hright :
              ((ENNReal.ofReal (g x) : ENNReal) : EReal) = ((g x : ℝ) : EReal) := by
            rw [EReal.coe_ennreal_ofReal, max_eq_left (hnonneg x hx)]
          have hxle' :
              (z' : EReal) ≤ ((ENNReal.ofReal (g x) : ENNReal) : EReal) := by
            simpa [hright] using hxle
          exact EReal.coe_ennreal_le_coe_ennreal_iff.mp hxle'
      · exact le_trans (le_of_lt (lt_of_not_ge hz_nonneg)) (EReal.coe_ennreal_nonneg _)
  have hs' : ((fun x ↦ (g x : EReal)) '' Q).Nonempty := hQ.image fun x ↦ (g x : EReal)
  simpa [S] using hs.csInf_eq hs'

/-- Helper for Proposition 7.31: a nonempty nonnegative feasible image can be read through
`maximalValueOn` as a finite `ℝ≥0∞` supremum. -/
private theorem maximalValueOn_eq_coe_sSup_of_nonempty_nonneg
    {X : Type*} (Q : Set X) (g : X → ℝ) (hQ : Q.Nonempty)
    (hnonneg : ∀ x ∈ Q, 0 ≤ g x) :
    maximalValueOn Q g =
      (((sSup ((fun x ↦ ENNReal.ofReal (g x)) '' Q) : ENNReal)) : EReal) := by
  rw [maximalValueOn_eq_sSup_image]
  let S : Set ENNReal := (fun x ↦ ENNReal.ofReal (g x)) '' Q
  have hs :
      IsLUB ((fun x ↦ (g x : EReal)) '' Q) (((sSup S : ENNReal) : EReal)) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hxS : ENNReal.ofReal (g x) ∈ S := Set.mem_image_of_mem (fun x ↦ ENNReal.ofReal (g x)) hx
      have hle : ENNReal.ofReal (g x) ≤ sSup S := le_sSup hxS
      have hcast :
          ((ENNReal.ofReal (g x) : ENNReal) : EReal) ≤ (((sSup S : ENNReal) : EReal)) :=
        EReal.coe_ennreal_le_coe_ennreal_iff.2 hle
      have hleft :
          ((g x : ℝ) : EReal) = ((ENNReal.ofReal (g x) : ENNReal) : EReal) := by
        rw [EReal.coe_ennreal_ofReal, max_eq_left (hnonneg x hx)]
      exact hleft.trans_le hcast
    · intro z hz
      have hz_nonneg : 0 ≤ z := by
        rcases hQ with ⟨x, hx⟩
        have hx_nonneg : (0 : EReal) ≤ ((g x : ℝ) : EReal) := by
          exact_mod_cast hnonneg x hx
        exact hx_nonneg.trans (hz (Set.mem_image_of_mem (fun x ↦ (g x : EReal)) hx))
      lift z to ENNReal using hz_nonneg with z'
      exact EReal.coe_ennreal_le_coe_ennreal_iff.2 <| sSup_le <| by
        rintro _ ⟨x, hx, rfl⟩
        have hxle : ((g x : ℝ) : EReal) ≤ (z' : EReal) := by
          exact hz (Set.mem_image_of_mem (fun x ↦ (g x : EReal)) hx)
        have hleft :
            ((g x : ℝ) : EReal) = ((ENNReal.ofReal (g x) : ENNReal) : EReal) := by
          rw [EReal.coe_ennreal_ofReal, max_eq_left (hnonneg x hx)]
        have hxle' :
            ((ENNReal.ofReal (g x) : ENNReal) : EReal) ≤ (z' : EReal) := by
          simpa [hleft] using hxle
        exact EReal.coe_ennreal_le_coe_ennreal_iff.mp hxle'
  have hs' : ((fun x ↦ (g x : EReal)) '' Q).Nonempty := hQ.image fun x ↦ (g x : EReal)
  simpa [S] using hs.csSup_eq hs'

/-- Helper for Proposition 7.31: on the positive reciprocal domain, the ratio and reciprocal
ratio are mutual inverses in `ℝ≥0∞`. -/
private theorem ofReal_phiRatio_eq_inv_reciprocalRatio
    {b : E} {ψ : E → ℝ} {y : E}
    (hy_inner : 0 < inner ℝ b y) (hy_psi : 0 < ψ y) :
    ENNReal.ofReal (inner ℝ b y / ψ y) =
      (ENNReal.ofReal (ψ y / inner ℝ b y))⁻¹ := by
  rw [← ENNReal.ofReal_inv_of_pos (div_pos hy_psi hy_inner)]
  congr 1
  field_simp [hy_inner.ne', hy_psi.ne']

/-- Helper for Proposition 7.31: normalizing by the positive pairing with `b` lands on the slice
`⟪b, y⟫ = 1` and preserves the reciprocal-ratio value. -/
private theorem normalizedSliceValue_eq_reciprocalRatio
    (b : E) (ψ : E → ℝ)
    (hψ_hom : IsPositivelyHomogeneousOn 1 (nonnegativeOrthant m) ψ)
    {y : E} (hy_nonneg : y ∈ nonnegativeOrthant m) (hy_inner : 0 < inner ℝ b y) :
    let τ : NNReal := ⟨(inner ℝ b y)⁻¹, inv_nonneg.2 hy_inner.le⟩
    let y' : E := τ • y
    y' ∈ nonnegativeOrthant m ∩ {z | inner ℝ b z = 1} ∧ ψ y' = ψ y / inner ℝ b y := by
  dsimp
  constructor
  · -- The positive rescaling stays in the orthant and enforces the slice equation.
    constructor
    · simpa using
        hψ_hom.smul_mem hy_nonneg ⟨(inner ℝ b y)⁻¹, inv_nonneg.2 hy_inner.le⟩
    · change
        inner ℝ b
            ((((⟨(inner ℝ b y)⁻¹, inv_nonneg.2 hy_inner.le⟩ : NNReal) : ℝ)) • y) = 1
      rw [inner_smul_right]
      exact inv_mul_cancel₀ hy_inner.ne'
  · -- Positive homogeneity of degree `1` turns the normalized value into the reciprocal ratio.
    have hmap :=
      hψ_hom.map_smul hy_nonneg ⟨(inner ℝ b y)⁻¹, inv_nonneg.2 hy_inner.le⟩
    simpa [Real.rpow_one, NNReal.smul_def, smul_eq_mul, div_eq_mul_inv,
      mul_comm, mul_left_comm, mul_assoc] using hmap

/-- Helper for Proposition 7.31: for a nonzero `ENNReal`, coercing the inverse to `EReal`
agrees with inverting after coercion. -/
private theorem coe_ennreal_inv_ereal {x : ENNReal} (hx : x ≠ 0) :
    ((x : EReal)⁻¹) = (((x⁻¹ : ENNReal)) : EReal) := by
  cases x using ENNReal.recTopCoe with
  | top =>
      -- The infinite branch maps to `⊤`, whose inverse is `0` in both codomains.
      simp [EReal.coe_ennreal_top]
  | coe r =>
      -- The finite branch is reduced to the matching `NNReal` inverse-coercion identities.
      have hr : r ≠ 0 := by
        intro hr
        apply hx
        simp [hr]
      rw [EReal.coe_nnreal_eq_coe_real, ← EReal.coe_inv (x := (r : ℝ))]
      rw [(ENNReal.coe_inv hr).symm, EReal.coe_nnreal_eq_coe_real, NNReal.coe_inv]

-- Proof sketch: for every nonzero nonnegative `y`, the hypotheses give `0 < ⟪b, y⟫` and
-- `0 < ψ(y)`, so `⟪b, y⟫ / ψ(y) = (ψ(y) / ⟪b, y⟫)⁻¹`; then take the infimum and supremum over
-- the corresponding feasible-set images.
/-- Proposition 7.31: [Equivalent formulations of `φ⋆` via `ψ`]

For `b ∈ ℝ^m` and a positively homogeneous `ψ` that is strictly positive on the
nonzero nonnegative orthant, the value
`φ⋆ = inf_{y ≥ 0, y ≠ 0} ⟪b, y⟫ / ψ(y)` is the reciprocal of the supremum of the reciprocal
ratio `ψ(y) / ⟪b, y⟫`, provided `⟪b, y⟫ > 0` on the nonzero nonnegative orthant. The ambient
nonzero-domain assumption is carried by `[Nonempty (Fin m)]`, matching the source's implicit
use of min/max over `ℝ^m_+ \ {0}`. -/
theorem fractionalCoveringPhiStar_eq_inv_reciprocalPsiSup
    [Nonempty (Fin m)]
    (b : E) (ψ : E → ℝ)
    (hinner_pos :
      ∀ y : E, y ∈ nonnegativeOrthant m → y ≠ 0 → 0 < inner ℝ b y)
    (hψ_pos :
      ∀ y : E, y ∈ nonnegativeOrthant m → y ≠ 0 → 0 < ψ y) :
    fractionalCoveringPhiStar b ψ = (fractionalCoveringReciprocalPsiSup b ψ)⁻¹ := by
  let Q : Set E := nonnegativeOrthant m ∩ {y | y ≠ 0}
  let R : Set E := nonnegativeOrthant m ∩ {y | 0 < inner ℝ b y}
  let S : Set ENNReal := (fun y : E ↦ ENNReal.ofReal (inner ℝ b y / ψ y)) '' Q
  let T : Set ENNReal := (fun y : E ↦ ENNReal.ofReal (ψ y / inner ℝ b y)) '' Q
  have hQ_nonempty : Q.Nonempty := by
    -- The source domain is nonempty because `Fin m` contains at least one coordinate.
    simpa [Q] using (nonnegativeOrthant_nonzero_nonempty (m := m))
  have hR_eq_Q : R = Q := by
    -- The positivity hypothesis upgrades `y ≠ 0` to `0 < ⟪b, y⟫`, and that positivity forces
    -- `y` to be nonzero in the reverse direction.
    ext y
    constructor
    · intro hy
      refine ⟨hy.1, ?_⟩
      intro hy_zero
      have : inner ℝ b y = 0 := by simp [hy_zero]
      exact hy.2.ne' this
    · intro hy
      exact ⟨hy.1, hinner_pos y hy.1 hy.2⟩
  have hQ_nonneg : ∀ y ∈ Q, 0 ≤ inner ℝ b y / ψ y := by
    -- Positivity of both factors makes the source ratio nonnegative on the feasible set.
    intro y hy
    have hy_inner : 0 < inner ℝ b y := hinner_pos y hy.1 hy.2
    have hy_psi : 0 < ψ y := hψ_pos y hy.1 hy.2
    exact div_nonneg hy_inner.le hy_psi.le
  have hR_nonempty : R.Nonempty := by
    -- The reciprocal domain is the same feasible set after replacing `y ≠ 0` by `0 < ⟪b, y⟫`.
    simpa [hR_eq_Q] using hQ_nonempty
  have hR_nonneg : ∀ y ∈ R, 0 ≤ ψ y / inner ℝ b y := by
    -- The reciprocal ratio is nonnegative because both numerator and denominator are positive.
    intro y hy
    have hy_ne : y ≠ 0 := by
      intro hy_zero
      have : inner ℝ b y = 0 := by simp [hy_zero]
      exact hy.2.ne' this
    have hy_psi : 0 < ψ y := hψ_pos y hy.1 hy_ne
    exact div_nonneg hy_psi.le hy.2.le
  have hImage :
      S = (fun a : ENNReal ↦ a⁻¹) '' T := by
    -- The two `ENNReal` images differ only by pointwise inversion of the positive ratios.
    ext a
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨ENNReal.ofReal (ψ y / inner ℝ b y), ?_, ?_⟩
      · exact Set.mem_image_of_mem (fun y : E ↦ ENNReal.ofReal (ψ y / inner ℝ b y)) hy
      · have hy_inner : 0 < inner ℝ b y := hinner_pos y hy.1 hy.2
        have hy_psi : 0 < ψ y := hψ_pos y hy.1 hy.2
        simp [ofReal_phiRatio_eq_inv_reciprocalRatio hy_inner hy_psi]
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      have hy_inner : 0 < inner ℝ b y := hinner_pos y hy.1 hy.2
      have hy_psi : 0 < ψ y := hψ_pos y hy.1 hy.2
      simp [ofReal_phiRatio_eq_inv_reciprocalRatio hy_inner hy_psi]
  have hsInf : sInf S = (sSup T)⁻¹ := by
    -- The infimum over the source ratios is the inverse of the supremum over reciprocal ratios.
    rw [hImage, sInf_image, ← ENNReal.inv_sSup T]
  have hsSup_ne_zero : sSup T ≠ 0 := by
    -- The reciprocal image contains a strictly positive value, so its supremum cannot be `0`.
    rcases hQ_nonempty with ⟨y, hy⟩
    have hy_inner : 0 < inner ℝ b y := hinner_pos y hy.1 hy.2
    have hy_psi : 0 < ψ y := hψ_pos y hy.1 hy.2
    have hy_mem : ENNReal.ofReal (ψ y / inner ℝ b y) ∈ T := by
      exact Set.mem_image_of_mem (fun y : E ↦ ENNReal.ofReal (ψ y / inner ℝ b y)) hy
    have hy_pos : 0 < ENNReal.ofReal (ψ y / inner ℝ b y) := by
      exact ENNReal.ofReal_pos.2 (div_pos hy_psi hy_inner)
    intro hs_zero
    have hs_le : ENNReal.ofReal (ψ y / inner ℝ b y) ≤ sSup T := le_sSup hy_mem
    rw [hs_zero] at hs_le
    exact (not_le_of_gt hy_pos) hs_le
  have hphi :
      fractionalCoveringPhiStar b ψ = (((sInf S : ENNReal)) : EReal) := by
    -- Rewrite the fractional-covering owner as an `ENNReal` infimum over the feasible image.
    simpa [fractionalCoveringPhiStar, Q, S] using
      (optimalValue_eq_coe_sInf_of_nonempty_nonneg Q
        (fun y : E ↦ inner ℝ b y / ψ y) hQ_nonempty hQ_nonneg)
  have hrecip :
      fractionalCoveringReciprocalPsiSup b ψ = (((sSup T : ENNReal)) : EReal) := by
    -- Rewrite the reciprocal owner as the matching `ENNReal` supremum over the same domain.
    simpa [fractionalCoveringReciprocalPsiSup, R, Q, T, hR_eq_Q] using
      (maximalValueOn_eq_coe_sSup_of_nonempty_nonneg R
        (fun y : E ↦ ψ y / inner ℝ b y) hR_nonempty hR_nonneg)
  -- Route correction: keep the `ENNReal` infimum/supremum skeleton and use a dedicated
  -- `ENNReal`→`EReal` inversion bridge only at the final coercion boundary.
  rw [hphi, hrecip, coe_ennreal_inv_ereal hsSup_ne_zero, hsInf]

-- Proof sketch: for `y ≥ 0` with `0 < ⟪b, y⟫`, normalize to `y / ⟪b, y⟫`; positive homogeneity
-- gives `ψ(y) / ⟪b, y⟫ = ψ(y / ⟪b, y⟫)`. Conversely, any point on the slice `⟪b, y⟫ = 1`
-- contributes the same value to both suprema.
/-- The reciprocal-ratio supremum equals the supremum of `ψ` on the normalized slice
`⟪b, y⟫ = 1`. -/
theorem fractionalCoveringReciprocalPsiSup_eq_normalizedPsiSup
    (b : E) (ψ : E → ℝ)
    (hψ_hom : IsPositivelyHomogeneousOn 1 (nonnegativeOrthant m) ψ) :
    fractionalCoveringReciprocalPsiSup b ψ = fractionalCoveringNormalizedPsiSup b ψ := by
  let R : Set E := nonnegativeOrthant m ∩ {y | 0 < inner ℝ b y}
  let N : Set E := nonnegativeOrthant m ∩ {y | inner ℝ b y = 1}
  let A : Set EReal := (fun y : E ↦ ((ψ y / inner ℝ b y : ℝ) : EReal)) '' R
  let B : Set EReal := (fun y : E ↦ (ψ y : EReal)) '' N
  -- Rewrite both maxima as `sSup` and identify the two feasible-value images by normalization.
  rw [fractionalCoveringReciprocalPsiSup, fractionalCoveringNormalizedPsiSup,
    maximalValueOn_eq_sSup_image, maximalValueOn_eq_sSup_image]
  suffices hAB : A = B by simpa [A, B] using congrArg sSup hAB
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hnorm := normalizedSliceValue_eq_reciprocalRatio b ψ hψ_hom hy.1 hy.2
    dsimp at hnorm
    rcases hnorm with ⟨hy', hvalue⟩
    refine ⟨(⟨(inner ℝ b y)⁻¹, inv_nonneg.2 hy.2.le⟩ : NNReal) • y, hy', ?_⟩
    simpa [hvalue]
  · rintro ⟨y, hy, rfl⟩
    have hy_inner_pos : 0 < inner ℝ b y := by
      rw [hy.2]
      norm_num
    refine ⟨y, ⟨hy.1, hy_inner_pos⟩, ?_⟩
    change ((ψ y / inner ℝ b y : ℝ) : EReal) = (ψ y : EReal)
    rw [hy.2, div_one]

-- Proof sketch: combine `fractionalCoveringPhiStar_eq_inv_reciprocalPsiSup` with
-- `fractionalCoveringReciprocalPsiSup_eq_normalizedPsiSup`.
/-- Final normalized-slice form of Proposition 7.31, obtained by combining the reciprocal
reformulation with the normalized-slice supremum identity. -/
theorem fractionalCoveringPhiStar_eq_inv_normalizedPsiSup
    [Nonempty (Fin m)]
    (b : E) (ψ : E → ℝ)
    (hinner_pos :
      ∀ y : E, y ∈ nonnegativeOrthant m → y ≠ 0 → 0 < inner ℝ b y)
    (hψ_pos :
      ∀ y : E, y ∈ nonnegativeOrthant m → y ≠ 0 → 0 < ψ y)
    (hψ_hom : IsPositivelyHomogeneousOn 1 (nonnegativeOrthant m) ψ) :
    fractionalCoveringPhiStar b ψ = (fractionalCoveringNormalizedPsiSup b ψ)⁻¹ := by
  -- Chain the reciprocal reformulation with the normalization identity.
  rw [fractionalCoveringPhiStar_eq_inv_reciprocalPsiSup b ψ hinner_pos hψ_pos,
    fractionalCoveringReciprocalPsiSup_eq_normalizedPsiSup b ψ hψ_hom]

end
