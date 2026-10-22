/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_33

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
variable {D : Set H}

/-- The explicit affine companion used in Proposition 4.38. -/
private noncomputable def lipschitz_lt_one_companion (ρ : ℝ) (T : D → H) : D → H :=
  fun x ↦ ((ρ - 1) / (ρ + 1)) • (x : H) + (2 / (ρ + 1)) • T x

private lemma companion_coefficient_simplifications {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) :
    |(ρ - 1) / (ρ + 1)| = (1 - ρ) / (ρ + 1) ∧
      |(2 : ℝ) / (ρ + 1)| = 2 / (ρ + 1) ∧
        ((1 - ρ) / (ρ + 1) + (2 * ρ) / (ρ + 1) = 1) := by
  have hden : 0 < ρ + 1 := by
    linarith [hρ.1]
  have hnum_nonpos : ρ - 1 ≤ 0 := by
    linarith [hρ.2]
  have hfrac_nonpos : (ρ - 1) / (ρ + 1) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden.le
  have htwo_nonneg : 0 ≤ (2 : ℝ) / (ρ + 1) := by
    exact div_nonneg (by norm_num) hden.le
  refine ⟨?_, ?_, ?_⟩
  · calc
      |(ρ - 1) / (ρ + 1)| = -((ρ - 1) / (ρ + 1)) := abs_of_nonpos hfrac_nonpos
      _ = (1 - ρ) / (ρ + 1) := by
        field_simp [hden.ne']
        ring
  · exact abs_of_nonneg htwo_nonneg
  · field_simp [hden.ne']
    ring

private lemma companion_difference_eq {ρ : ℝ} {T : D → H} (x y : D) :
    lipschitz_lt_one_companion ρ T x - lipschitz_lt_one_companion ρ T y =
      ((ρ - 1) / (ρ + 1)) • ((x : H) - y) + (2 / (ρ + 1)) • (T x - T y) := by
  simp [lipschitz_lt_one_companion, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

private lemma companion_pairwise_nonexpansive {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) {T : D → H}
    (hT : LipschitzWith (Real.toNNReal ρ) T) :
    ∀ x y : D,
      ‖lipschitz_lt_one_companion ρ T x - lipschitz_lt_one_companion ρ T y‖ ≤ ‖(x : H) - y‖ := by
  intro x y
  rcases companion_coefficient_simplifications hρ with ⟨habs₁, habs₂, hsum⟩
  have hden : 0 < ρ + 1 := by
    linarith [hρ.1]
  have htwo_nonneg : 0 ≤ (2 : ℝ) / (ρ + 1) := by
    exact div_nonneg (by norm_num) hden.le
  have hTxy : ‖T x - T y‖ ≤ ρ * ‖(x : H) - y‖ := by
    simpa [Subtype.dist_eq, dist_eq_norm, Real.toNNReal_of_nonneg hρ.1.le] using hT.dist_le_mul x y
  rw [companion_difference_eq]
  calc
    ‖((ρ - 1) / (ρ + 1)) • ((x : H) - y) + (2 / (ρ + 1)) • (T x - T y)‖
      ≤ ‖((ρ - 1) / (ρ + 1)) • ((x : H) - y)‖ + ‖(2 / (ρ + 1)) • (T x - T y)‖ :=
        norm_add_le _ _
    _ = ‖(ρ - 1) / (ρ + 1)‖ * ‖(x : H) - y‖ + ‖(2 : ℝ) / (ρ + 1)‖ * ‖T x - T y‖ := by
      rw [norm_smul, norm_smul]
    _ = |(ρ - 1) / (ρ + 1)| * ‖(x : H) - y‖ + |(2 : ℝ) / (ρ + 1)| * ‖T x - T y‖ := by
      rw [abs_div, abs_div]
      simp [Real.norm_eq_abs]
    _ = ((1 - ρ) / (ρ + 1)) * ‖(x : H) - y‖ + (2 / (ρ + 1)) * ‖T x - T y‖ := by
      rw [habs₁, habs₂]
    _ ≤ ((1 - ρ) / (ρ + 1)) * ‖(x : H) - y‖ + (2 / (ρ + 1)) * (ρ * ‖(x : H) - y‖) := by
      have hscaled :
          (2 / (ρ + 1)) * ‖T x - T y‖ ≤ (2 / (ρ + 1)) * (ρ * ‖(x : H) - y‖) := by
        exact mul_le_mul_of_nonneg_left hTxy htwo_nonneg
      nlinarith [hscaled]
    _ = (((1 - ρ) / (ρ + 1)) + (2 * ρ) / (ρ + 1)) * ‖(x : H) - y‖ := by
      ring
    _ = ‖(x : H) - y‖ := by
      rw [hsum, one_mul]

private theorem companion_lipschitzWith_one {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) {T : D → H}
    (hT : LipschitzWith (Real.toNNReal ρ) T) :
    LipschitzWith 1 (lipschitz_lt_one_companion ρ T) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simpa [Subtype.dist_eq, dist_eq_norm] using companion_pairwise_nonexpansive hρ hT x y

private lemma companion_affine_reconstruction {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) {T : D → H} :
    T = fun x : D ↦
      (1 - ((ρ + 1) / 2 : ℝ)) • (x : H) +
        (((ρ + 1) / 2 : ℝ)) • lipschitz_lt_one_companion ρ T x := by
  ext x
  have hden : ρ + 1 ≠ 0 := by
    linarith [hρ.1]
  have hx :
      1 - ((ρ + 1) / 2 : ℝ) + ((ρ + 1) / 2 : ℝ) * ((ρ - 1) / (ρ + 1)) = 0 := by
    field_simp [hden]
    ring
  have hTx : ((ρ + 1) / 2 : ℝ) * (2 / (ρ + 1)) = 1 := by
    field_simp [hden]
  have hexpand :
      (1 - ((ρ + 1) / 2 : ℝ)) • (x : H) +
          (((ρ + 1) / 2 : ℝ)) • lipschitz_lt_one_companion ρ T x =
        (1 - ((ρ + 1) / 2 : ℝ) + ((ρ + 1) / 2 : ℝ) * ((ρ - 1) / (ρ + 1))) • (x : H) +
          (((ρ + 1) / 2 : ℝ) * (2 / (ρ + 1))) • T x := by
    simp [lipschitz_lt_one_companion, smul_add, mul_smul, add_smul, add_assoc, add_left_comm,
      add_comm]
  calc
    T x = 0 • (x : H) + 1 • T x := by
      simp
    _ = (1 - ((ρ + 1) / 2 : ℝ) + ((ρ + 1) / 2 : ℝ) * ((ρ - 1) / (ρ + 1))) • (x : H) +
          (((ρ + 1) / 2 : ℝ) * (2 / (ρ + 1))) • T x := by
      simp [hx, hTx]
    _ = (1 - ((ρ + 1) / 2 : ℝ)) • (x : H) +
          (((ρ + 1) / 2 : ℝ)) • lipschitz_lt_one_companion ρ T x := by
      rw [hexpand]

private lemma averaged_parameter_mem_Ioo {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) :
    (ρ + 1) / 2 ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor <;> nlinarith [hρ.1, hρ.2]

-- Proof sketch: define the affine companion
-- `R x = ((ρ - 1) / (ρ + 1)) • x + (2 / (ρ + 1)) • T x`, show it is nonexpansive by the
-- `ρ`-Lipschitz estimate, and then rewrite `T` as
-- `(1 - (ρ + 1) / 2) Id + ((ρ + 1) / 2) R`.
/-- Proposition 4.38: if `T : D → H` is `ρ`-Lipschitz with `0 < ρ < 1`, then `T` is
`((ρ + 1) / 2)`-averaged. -/
theorem averagedWith_of_lipschitz_lt_one {ρ : ℝ} (hρ : ρ ∈ Set.Ioo (0 : ℝ) 1) {T : D → H}
    (hT : LipschitzWith (Real.toNNReal ρ) T) :
    AveragedWith ((ρ + 1) / 2 : ℝ) T := by
  refine averagedWith_iff.mpr ?_
  refine ⟨averaged_parameter_mem_Ioo hρ, lipschitz_lt_one_companion ρ T, ?_, ?_⟩
  · exact companion_lipschitzWith_one hρ hT
  · exact companion_affine_reconstruction hρ

end
