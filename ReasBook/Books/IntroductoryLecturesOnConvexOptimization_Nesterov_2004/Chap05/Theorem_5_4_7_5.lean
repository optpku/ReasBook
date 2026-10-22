/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_7_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped EuclideanSpaceLp
open scoped PowerCone

noncomputable section

/- Theorem 5.4.7.5 lies in the Chapter 5 finite-dimensional `ℓ_p` epigraph / lifted-cone domain.

Sampled owner declarations:
* `EuclideanSpace.LpExponent` from `Definition_3_7`, the project owner for admissible
  finite-dimensional `ℓ_p` exponents `1 ≤ p < ∞`;
* `EuclideanSpace.lpSeminorm` and `EuclideanSpace.lpNorm_eq_sum` from `Definition_3_7`, the
  intrinsic finite-dimensional `ℓ_p` owner and its textbook notation surface `‖z‖_[p]`;
* `lpNormEpigraphCone` and `mem_lpNormEpigraphCone_iff` from `Definition_5_4_7_6`, the
  coordinate-model epigraph bridge sitting underneath the intrinsic norm inequality;
* `lpEpigraphConeLiftDomain` and `mem_lpEpigraphConeLiftDomain_iff` from
  `Definition_5_4_7_7`, the chapter owner for the lifted-domain witness data;
* `WithLp.toLp`, the canonical coordinate norm owner used internally by
  `lpNormEpigraphCone`.

Source/core/bridge triage:
* source-facing: membership of `(τ, z)` in the epigraph owner `lpNormEpigraphCone n p`;
* core/canonical: the owner seminorm `EuclideanSpace.lpSeminorm n p`;
* bridge/view: the coordinate epigraph owner `lpNormEpigraphCone n (p : ENNReal)` and the
  lifted witness
  domain `lpEpigraphConeLiftDomain n (1 / p.toReal)`.

Primitive data:
* the admissible exponent `p : EuclideanSpace.LpExponent`;
* the epigraph point `(τ, z) : ℝ × EuclideanSpace ℝ (Fin n)`.

Derived API:
* the source-facing epigraph membership `(τ, z) ∈ lpNormEpigraphCone n p`;
* the intrinsic inequality bridge `mem_lpNormEpigraphCone_iff`;
* the lifted witness domain `lpEpigraphConeLiftDomain n (1 / p.toReal)`;
* the coordinatewise witness inequalities, recovered from
  `mem_lpEpigraphConeLiftDomain_iff` when needed.

This theorem therefore lives on the Chapter 5 epigraph owner surface `lpNormEpigraphCone`, while
the intrinsic inequality `‖z‖_[p] ≤ τ` is kept only as the upstream bridge
`mem_lpNormEpigraphCone_iff`. The lifted witness set remains a genuine bridge layer rather than a
competing public owner. -/

-- Proof sketch: the main theorem is stated directly on the epigraph owner
-- `lpNormEpigraphCone n p`. For the forward direction, construct a lift `(τ, x, z)` in
-- `lpEpigraphConeLiftDomain n (1 / p.toReal)` by choosing the standard coordinate witness `x`
-- from the finite-dimensional `ℓ_p` norm formula. For the reverse direction, unpack the lift with
-- `mem_lpEpigraphConeLiftDomain_iff`, raise the coordinate inequalities to the power
-- `p.toReal`, sum over `i`, use `∑ i, x i = τ`, and finally read the result back through
-- `mem_lpNormEpigraphCone_iff` when needed.
/-- Helper for Theorem 5.4.7.5: the ambient coordinate triple used in the local lifted-domain
bridge to the power cone `K_[α]`. -/
private abbrev liftedPowerConeCoord
    {n : ℕ} (τ : ℝ) (x z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    ((ℝ × ℝ) × ℝ) :=
  ((x i, τ), z i)

/-- Helper for Theorem 5.4.7.5: package a coordinate function `Fin n → ℝ` as the canonical point
of `EuclideanSpace ℝ (Fin n)`. -/
private def ofCoords {n : ℕ} (f : Fin n → ℝ) : EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm f

/-- Helper for Theorem 5.4.7.5: the packaged coordinate point `ofCoords f` evaluates back to the
original coordinate function `f`. -/
private theorem ofCoords_apply
    {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    ofCoords f i = f i :=
  rfl

/-- Helper for Theorem 5.4.7.5: the lifted witness domain for the finite-dimensional `ℓ_p`
epigraph, written only with the earlier power-cone owner `K_[α]`. -/
private def lpEpigraphConeLiftDomainLocal
    (n : ℕ) (α : ℝ) : Set (ℝ × EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
  {p |
    (∀ i : Fin n, liftedPowerConeCoord p.1 p.2.1 p.2.2 i ∈ K_[α]) ∧
      ∑ i : Fin n, p.2.1 i = p.1}

local notation "lpEpigraphConeLiftDomain" => lpEpigraphConeLiftDomainLocal

/-- Helper for Theorem 5.4.7.5: membership in the local lifted witness domain is equivalent to
the coordinatewise inequalities and the normalization equation. -/
private theorem mem_lpEpigraphConeLiftDomain_iff_local
    {n : ℕ} (α τ : ℝ)
    (x z : EuclideanSpace ℝ (Fin n)) :
    (τ, x, z) ∈ lpEpigraphConeLiftDomain n α ↔
      (∀ i : Fin n, 0 ≤ x i) ∧
        (∀ i : Fin n, Real.rpow (x i) α * Real.rpow τ (1 - α) ≥ |z i|) ∧
          ∑ i : Fin n, x i = τ := by
  constructor
  · rintro ⟨hp, hsum⟩
    refine ⟨?_, ?_, hsum⟩
    · intro i
      rcases (mem_powerCone_iff α (x i) τ (z i)).1 (hp i) with ⟨hxi, -, -⟩
      exact hxi
    · intro i
      rcases (mem_powerCone_iff α (x i) τ (z i)).1 (hp i) with ⟨-, -, hzi⟩
      exact hzi
  · rintro ⟨hx, hz, hsum⟩
    refine ⟨?_, hsum⟩
    have hτ : 0 ≤ τ := by
      have hsum_nonneg : 0 ≤ ∑ i : Fin n, x i :=
        Finset.sum_nonneg fun i _ ↦ hx i
      simpa [hsum] using hsum_nonneg
    intro i
    exact (mem_powerCone_iff α (x i) τ (z i)).2 ⟨hx i, hτ, hz i⟩

/-- Helper for Theorem 5.4.7.5: raising the canonical `ℓ_p` norm formula to the power `p.toReal`
recovers the coordinate sum `∑ i, |z i| ^ p.toReal`. -/
lemma lpNormRpow_eq_sum_absRpow
    {n : ℕ} (p : EuclideanSpace.LpExponent) (z : EuclideanSpace ℝ (Fin n)) :
    ‖z‖_[p] ^ p.toReal = ∑ i : Fin n, |z i| ^ p.toReal := by
  have hsum_nonneg : 0 ≤ ∑ i : Fin n, |z i| ^ p.toReal :=
    Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg _) _
  have hp_ne : p.toReal ≠ 0 := ne_of_gt (EuclideanSpace.LpExponent.toReal_pos p)
  -- Raise the owner norm formula to the exponent `p.toReal`.
  calc
    ‖z‖_[p] ^ p.toReal
        = (((∑ i : Fin n, |z i| ^ p.toReal) ^ (1 / p.toReal : ℝ)) ^ p.toReal) := by
            rw [EuclideanSpace.lpNorm_eq_sum]
    _ = ∑ i : Fin n, |z i| ^ p.toReal := by
          simpa [one_div] using Real.rpow_inv_rpow hsum_nonneg hp_ne

/-- Helper for Theorem 5.4.7.5: the coordinates of a single-supported vector sum to its unique
nonzero entry. -/
lemma finSum_single_eq
    {n : ℕ} (i0 : Fin n) (s : ℝ) :
    ∑ i : Fin n, ((Pi.single i0 s : Fin n → ℝ) i) = s := by
  simp

/-- Helper for Theorem 5.4.7.5: if `‖z‖_[p] = 0`, then putting all mass at one coordinate gives a
lift in `lpEpigraphConeLiftDomain n (1 / p.toReal)`. -/
lemma zeroNorm_hasSingleCoordinateLift
    {n : ℕ} (hn : 0 < n) (p : EuclideanSpace.LpExponent)
    {τ : ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hzNorm : ‖z‖_[p] = 0) (hτ : 0 ≤ τ) :
    ∃ x : EuclideanSpace ℝ (Fin n), (τ, x, z) ∈ lpEpigraphConeLiftDomain n (1 / p.toReal) := by
  let i0 : Fin n := ⟨0, hn⟩
  let xCoords : Fin n → ℝ := Pi.single i0 τ
  let x : EuclideanSpace ℝ (Fin n) := ofCoords xCoords
  have hx_apply (i : Fin n) : x i = xCoords i := by
    simp [x, xCoords, ofCoords_apply]
  have hz_zero : z = 0 := by
    simpa using
      (EuclideanSpace.lpSeminorm_isNorm (n := n) p).eq_zero_of_map_eq_zero (x := z) hzNorm
  refine ⟨x, ?_⟩
  rw [mem_lpEpigraphConeLiftDomain_iff_local]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    -- The single-supported witness is coordinatewise nonnegative.
    by_cases hi : i = i0
    · subst hi
      simp [hx_apply, xCoords, hτ]
    · simp [hx_apply, xCoords, hi]
  · intro i
    -- Once `z = 0`, every coordinate inequality reduces to nonnegativity of the left-hand side.
    have hx_nonneg : 0 ≤ x i := by
      by_cases hi : i = i0
      · subst hi
        simp [hx_apply, xCoords, hτ]
      · simp [hx_apply, xCoords, hi]
    have hleft_nonneg :
        0 ≤ Real.rpow (x i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal) := by
      exact mul_nonneg (Real.rpow_nonneg hx_nonneg _) (Real.rpow_nonneg hτ _)
    simpa [hx_apply, xCoords, hz_zero] using hleft_nonneg
  · -- The sum of a single-supported vector is its distinguished coordinate.
    calc
      ∑ i : Fin n, x i = ∑ i : Fin n, xCoords i := by simp [hx_apply]
      _ = τ := finSum_single_eq i0 τ

/-- Helper for Theorem 5.4.7.5: if `‖z‖_[p] ≤ τ` and `‖z‖_[p] > 0`, then a powered witness plus
one-coordinate slack produces a lift in `lpEpigraphConeLiftDomain n (1 / p.toReal)`. -/
lemma positiveNorm_hasPoweredLift
    {n : ℕ} (hn : 0 < n) (p : EuclideanSpace.LpExponent)
    {τ : ℝ} {z : EuclideanSpace ℝ (Fin n)}
    (hzNormPos : 0 < ‖z‖_[p]) (hzNormLe : ‖z‖_[p] ≤ τ) :
    ∃ x : EuclideanSpace ℝ (Fin n), (τ, x, z) ∈ lpEpigraphConeLiftDomain n (1 / p.toReal) := by
  let i0 : Fin n := ⟨0, hn⟩
  have hp0 : 0 < p.toReal := EuclideanSpace.LpExponent.toReal_pos p
  have hp_ne : p.toReal ≠ 0 := hp0.ne'
  have hp_one_le : 1 ≤ p.toReal := by
    simpa [ENNReal.toReal_one] using ENNReal.toReal_mono p.2.2 p.2.1
  have hp_sub_nonneg : 0 ≤ p.toReal - 1 := by
    linarith
  have hτ_pos : 0 < τ := lt_of_lt_of_le hzNormPos hzNormLe
  have hτ_nonneg : 0 ≤ τ := hτ_pos.le
  let baseCoords : Fin n → ℝ := fun i ↦ τ ^ (1 - p.toReal) * |z i| ^ p.toReal
  let base : EuclideanSpace ℝ (Fin n) := ofCoords baseCoords
  have hbase_apply (i : Fin n) : base i = baseCoords i := by
    simp [base, baseCoords, ofCoords_apply]
  have hbase_nonneg : ∀ i : Fin n, 0 ≤ base i := by
    intro i
    rw [hbase_apply]
    exact mul_nonneg (Real.rpow_nonneg hτ_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _)
  have hpow_le : ‖z‖_[p] ^ p.toReal ≤ τ ^ p.toReal := by
    exact (Real.rpow_le_rpow_iff (by positivity) hτ_nonneg hp0).2 hzNormLe
  have hbase_sum_le : ∑ i : Fin n, base i ≤ τ := by
    -- Rewrite the powered witness mass using the canonical norm identity and compare with `τ`.
    calc
      ∑ i : Fin n, base i
          = ∑ i : Fin n, baseCoords i := by
              simp [hbase_apply]
      _ = ∑ i : Fin n, τ ^ (1 - p.toReal) * |z i| ^ p.toReal := by
            rfl
      _ = τ ^ (1 - p.toReal) * ∑ i : Fin n, |z i| ^ p.toReal := by
            simpa using
              (Finset.mul_sum
                (s := Finset.univ)
                (a := τ ^ (1 - p.toReal))
                (f := fun i : Fin n ↦ |z i| ^ p.toReal)).symm
      _ = τ ^ (1 - p.toReal) * ‖z‖_[p] ^ p.toReal := by
            rw [← lpNormRpow_eq_sum_absRpow p z]
      _ ≤ τ ^ (1 - p.toReal) * τ ^ p.toReal := by
            exact mul_le_mul_of_nonneg_left hpow_le (Real.rpow_nonneg hτ_nonneg _)
      _ = τ ^ ((1 - p.toReal) + p.toReal) := by
            symm
            exact Real.rpow_add hτ_pos _ _
      _ = τ := by
            have hexp : (1 - p.toReal) + p.toReal = (1 : ℝ) := by ring
            rw [hexp, Real.rpow_one]
  let slack : ℝ := τ - ∑ i : Fin n, base i
  have hslack_nonneg : 0 ≤ slack := by
    exact sub_nonneg.mpr hbase_sum_le
  let xCoords : Fin n → ℝ := fun i ↦ base i + if i = i0 then slack else 0
  let x : EuclideanSpace ℝ (Fin n) := ofCoords xCoords
  have hx_apply (i : Fin n) : x i = xCoords i := by
    simp [x, xCoords, ofCoords_apply]
  have hbase_le_x : ∀ i : Fin n, base i ≤ x i := by
    intro i
    rw [hx_apply]
    by_cases hi : i = i0
    · simp [xCoords, hi, hslack_nonneg]
    · simp [xCoords, hi]
  have hx_nonneg : ∀ i : Fin n, 0 ≤ x i := by
    intro i
    rw [hx_apply]
    by_cases hi : i = i0
    · subst hi
      exact add_nonneg (hbase_nonneg i0) hslack_nonneg
    · simp [xCoords, hi, hbase_nonneg i]
  have hbase_eq_abs (i : Fin n) :
      Real.rpow (base i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal) = |z i| := by
    -- The powered base witness saturates the coordinate inequality exactly.
    have hbase_rpow :
        Real.rpow (base i) (1 / p.toReal) =
          (τ ^ (1 - p.toReal)) ^ (1 / p.toReal) * (|z i| ^ p.toReal) ^ (1 / p.toReal) := by
      rw [hbase_apply]
      simpa using
        (Real.mul_rpow
          (Real.rpow_nonneg hτ_nonneg _)
          (Real.rpow_nonneg (abs_nonneg (z i)) _))
    have hτ_part :
        (τ ^ (1 - p.toReal)) ^ (1 / p.toReal) = τ ^ ((1 - p.toReal) * (1 / p.toReal)) := by
      simpa [one_div] using (Real.rpow_mul hτ_nonneg (1 - p.toReal) (1 / p.toReal)).symm
    have hz_part :
        (|z i| ^ p.toReal) ^ (1 / p.toReal) = |z i| := by
      simpa [one_div] using (Real.rpow_rpow_inv (abs_nonneg (z i)) hp_ne)
    calc
      Real.rpow (base i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal)
          = ((τ ^ (1 - p.toReal)) ^ (1 / p.toReal) *
                (|z i| ^ p.toReal) ^ (1 / p.toReal)) *
              Real.rpow τ (1 - 1 / p.toReal) := by
                rw [hbase_rpow]
      _ = (τ ^ ((1 - p.toReal) * (1 / p.toReal)) * |z i|) *
            Real.rpow τ (1 - 1 / p.toReal) := by
              rw [hτ_part, hz_part]
      _ = |z i| *
            (τ ^ ((1 - p.toReal) * (1 / p.toReal)) * Real.rpow τ (1 - 1 / p.toReal)) := by
              ring
      _ = |z i| * 1 := by
            congr 1
            calc
              τ ^ ((1 - p.toReal) * (1 / p.toReal)) * Real.rpow τ (1 - 1 / p.toReal)
                  = τ ^ (((1 - p.toReal) * (1 / p.toReal)) + (1 - 1 / p.toReal)) := by
                      symm
                      exact Real.rpow_add hτ_pos _ _
              _ = τ ^ (0 : ℝ) := by
                    have hexp :
                        ((1 - p.toReal) * (1 / p.toReal)) + (1 - 1 / p.toReal) = (0 : ℝ) := by
                      field_simp [hp_ne]
                      ring
                    rw [hexp]
              _ = 1 := by simp
      _ = |z i| := by ring
  have hsum_x : ∑ i : Fin n, x i = τ := by
    -- Add the slack back at the distinguished coordinate to recover the exact normalization.
    calc
      ∑ i : Fin n, x i = ∑ i : Fin n, xCoords i := by
            simp [hx_apply]
      _ = ∑ i : Fin n, (base i + if i = i0 then slack else 0) := by
            simp [xCoords]
      _ = ∑ i : Fin n, base i + ∑ i : Fin n, if i = i0 then slack else 0 := by
            rw [Finset.sum_add_distrib]
      _ = ∑ i : Fin n, base i + slack := by simp
      _ = τ := by
            simp [slack]
  refine ⟨x, ?_⟩
  rw [mem_lpEpigraphConeLiftDomain_iff_local]
  refine ⟨hx_nonneg, ?_, hsum_x⟩
  intro i
  -- Enlarging the saturated base witness by nonnegative slack preserves the coordinate inequality.
  have hrpow_le :
      Real.rpow (base i) (1 / p.toReal) ≤ Real.rpow (x i) (1 / p.toReal) := by
    exact Real.rpow_le_rpow (hbase_nonneg i) (hbase_le_x i) (by positivity)
  have hτ_factor_nonneg : 0 ≤ Real.rpow τ (1 - 1 / p.toReal) := Real.rpow_nonneg hτ_nonneg _
  have hmul_le :
      Real.rpow (base i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal) ≤
        Real.rpow (x i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal) := by
    exact mul_le_mul_of_nonneg_right hrpow_le hτ_factor_nonneg
  have habs_le :
      |z i| ≤ Real.rpow (x i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal) := by
    calc
      |z i|
          = Real.rpow (base i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal) :=
              (hbase_eq_abs i).symm
      _ ≤ Real.rpow (x i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal) := hmul_le
  simpa [ge_iff_le] using habs_le

/-- Helper for Theorem 5.4.7.5: summing the powered coordinate inequalities in a lift recovers
the intrinsic norm bound `‖z‖_[p] ≤ τ`. -/
lemma lpNorm_le_of_memLift
    {n : ℕ} (p : EuclideanSpace.LpExponent)
    {τ : ℝ} {x z : EuclideanSpace ℝ (Fin n)}
    (hLift : (τ, x, z) ∈ lpEpigraphConeLiftDomain n (1 / p.toReal)) :
    ‖z‖_[p] ≤ τ := by
  have hp0 : 0 < p.toReal := EuclideanSpace.LpExponent.toReal_pos p
  have hp_ne : p.toReal ≠ 0 := hp0.ne'
  have hp_one_le : 1 ≤ p.toReal := by
    simpa [ENNReal.toReal_one] using ENNReal.toReal_mono p.2.2 p.2.1
  have hp_sub_nonneg : 0 ≤ p.toReal - 1 := by
    linarith
  rw [mem_lpEpigraphConeLiftDomain_iff_local] at hLift
  rcases hLift with ⟨hx, hz, hsum⟩
  have hτ_nonneg : 0 ≤ τ := by
    have hsum_nonneg : 0 ≤ ∑ i : Fin n, x i := Finset.sum_nonneg fun i _ ↦ hx i
    simpa [hsum] using hsum_nonneg
  have hcoord_pow (i : Fin n) : |z i| ^ p.toReal ≤ x i * τ ^ (p.toReal - 1) := by
    have hleft_nonneg :
        0 ≤ Real.rpow (x i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal) := by
      exact mul_nonneg (Real.rpow_nonneg (hx i) _) (Real.rpow_nonneg hτ_nonneg _)
    have hzpow :
        |z i| ^ p.toReal ≤
          (Real.rpow (x i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal)) ^ p.toReal := by
      exact (Real.rpow_le_rpow_iff (abs_nonneg _) hleft_nonneg hp0).2 (hz i)
    have hmul_rpow :
        (Real.rpow (x i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal)) ^ p.toReal =
          (Real.rpow (x i) (1 / p.toReal)) ^ p.toReal *
            (Real.rpow τ (1 - 1 / p.toReal)) ^ p.toReal := by
      simpa using
        (Real.mul_rpow
          (Real.rpow_nonneg (hx i) _)
          (Real.rpow_nonneg hτ_nonneg _))
    have hx_rpow :
        (Real.rpow (x i) (1 / p.toReal)) ^ p.toReal = x i := by
      simpa [one_div] using (Real.rpow_inv_rpow (hx i) hp_ne)
    have hτ_rpow :
        (Real.rpow τ (1 - 1 / p.toReal)) ^ p.toReal = τ ^ (p.toReal - 1) := by
      calc
        (Real.rpow τ (1 - 1 / p.toReal)) ^ p.toReal
            = τ ^ ((1 - 1 / p.toReal) * p.toReal) := by
                simpa [one_div] using (Real.rpow_mul hτ_nonneg (1 - 1 / p.toReal) p.toReal).symm
        _ = τ ^ (p.toReal - 1) := by
              congr 1
              field_simp [hp_ne]
    calc
      |z i| ^ p.toReal
          ≤ (Real.rpow (x i) (1 / p.toReal) * Real.rpow τ (1 - 1 / p.toReal)) ^ p.toReal := hzpow
      _ = (Real.rpow (x i) (1 / p.toReal)) ^ p.toReal *
            (Real.rpow τ (1 - 1 / p.toReal)) ^ p.toReal := by
              rw [hmul_rpow]
      _ = x i * (Real.rpow τ (1 - 1 / p.toReal)) ^ p.toReal := by
            rw [hx_rpow]
      _ = x i * τ ^ (p.toReal - 1) := by
            rw [hτ_rpow]
  have hsum_pow :
      ∑ i : Fin n, |z i| ^ p.toReal ≤ ∑ i : Fin n, x i * τ ^ (p.toReal - 1) := by
    exact Finset.sum_le_sum fun i _ ↦ hcoord_pow i
  have hright_eq : ∑ i : Fin n, x i * τ ^ (p.toReal - 1) = τ ^ p.toReal := by
    calc
      ∑ i : Fin n, x i * τ ^ (p.toReal - 1)
          = (∑ i : Fin n, x i) * τ ^ (p.toReal - 1) := by
              rw [Finset.sum_mul]
      _ = τ * τ ^ (p.toReal - 1) := by rw [hsum]
      _ = τ ^ (1 : ℝ) * τ ^ (p.toReal - 1) := by rw [Real.rpow_one]
      _ = τ ^ ((1 : ℝ) + (p.toReal - 1)) := by
            symm
            exact Real.rpow_add_of_nonneg hτ_nonneg (by norm_num) hp_sub_nonneg
      _ = τ ^ p.toReal := by
            have hexp : (1 : ℝ) + (p.toReal - 1) = p.toReal := by ring
            rw [hexp]
  have hpow_le : ‖z‖_[p] ^ p.toReal ≤ τ ^ p.toReal := by
    calc
      ‖z‖_[p] ^ p.toReal = ∑ i : Fin n, |z i| ^ p.toReal := lpNormRpow_eq_sum_absRpow p z
      _ ≤ ∑ i : Fin n, x i * τ ^ (p.toReal - 1) := hsum_pow
      _ = τ ^ p.toReal := hright_eq
  exact (Real.rpow_le_rpow_iff (by positivity) hτ_nonneg hp0).1 hpow_le

/-- Theorem 5.4.7.5: for `n > 0`, a point `(τ, z)` lies in the finite-dimensional `ℓ_p` epigraph
cone exactly when it admits a lift to the chapter’s lifted domain with exponent `1 / p.toReal`.
-/
theorem mem_lpNormEpigraphCone_iff_exists_lift
    {n : ℕ} (hn : 0 < n) (p : EuclideanSpace.LpExponent)
    {τ : ℝ} {z : EuclideanSpace ℝ (Fin n)} :
    (τ, z) ∈ lpNormEpigraphCone n p ↔
      ∃ x : EuclideanSpace ℝ (Fin n), (τ, x, z) ∈ lpEpigraphConeLiftDomain n (1 / p.toReal) :=
  by
    rw [mem_lpNormEpigraphCone_iff]
    constructor
    · intro hzNormLe
      by_cases hzNorm : ‖z‖_[p] = 0
      · -- In the degenerate branch, `z = 0`, so a single-coordinate witness carries all of `τ`.
        exact zeroNorm_hasSingleCoordinateLift hn p hzNorm (le_trans (by positivity) hzNormLe)
      · -- In the positive branch, use the powered witness and put the
        -- residual slack at one coordinate.
        have hzNormPos : 0 < ‖z‖_[p] := lt_of_le_of_ne (by positivity) (Ne.symm hzNorm)
        exact positiveNorm_hasPoweredLift hn p hzNormPos hzNormLe
    · rintro ⟨x, hx⟩
      -- Summing the powered coordinate inequalities brings the lifted
      -- witness back to the norm bound.
      exact lpNorm_le_of_memLift p hx

/-- The intrinsic inequality form of Theorem 5.4.7.5, read through the epigraph-owner bridge
`mem_lpNormEpigraphCone_iff`. -/
theorem lpSeminorm_le_iff_exists_lift
    {n : ℕ} (hn : 0 < n) (p : EuclideanSpace.LpExponent)
    {τ : ℝ} {z : EuclideanSpace ℝ (Fin n)} :
    ‖z‖_[p] ≤ τ ↔
      ∃ x : EuclideanSpace ℝ (Fin n), (τ, x, z) ∈ lpEpigraphConeLiftDomain n (1 / p.toReal) := by
  rw [← mem_lpNormEpigraphCone_iff]
  exact mem_lpNormEpigraphCone_iff_exists_lift hn p
