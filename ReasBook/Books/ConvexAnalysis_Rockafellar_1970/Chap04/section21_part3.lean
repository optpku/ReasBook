/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part2

section Chap04
section Section21

set_option linter.unnecessarySimpa false

/-- Helper for Theorem 21.2: apply Theorem 21.1 to the augmented family
`Fin.append fStrict (fun x => (gSupport x : EReal))` extracted from support data. -/
lemma helperForTheorem_21_2_augmented_dual_from_supportData
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (hfStrict : ∀ i : Fin k,
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStrict i))
    (hdomStrict :
      ∀ i : Fin k,
        euclideanRelativeInterior_fin n C ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fStrict i))
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hAffine : ∀ j : Fin l, ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, fAffine j = g)
    (lamAffineSupport : Fin l → ℝ)
    (hSupportOnStrictFeasible :
      ∀ x, x ∈ C → (∀ i : Fin k, fStrict i x < (0 : EReal)) →
        0 ≤ ∑ j : Fin l, lamAffineSupport j * fAffine j x) :
    ∃ gSupport : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
      (∀ x : Fin n → ℝ, gSupport x = ∑ j : Fin l, lamAffineSupport j * fAffine j x) ∧
        ∃ muStrict : Fin k → ℝ, ∃ mu0 : ℝ,
          (∀ i : Fin k, 0 ≤ muStrict i) ∧
            0 ≤ mu0 ∧
              ((∃ i : Fin k, muStrict i ≠ 0) ∨ mu0 ≠ 0) ∧
                (∀ x, x ∈ C →
                  (0 : EReal) ≤
                    (∑ i : Fin k, ((muStrict i : ℝ) : EReal) * fStrict i x) +
                      ((mu0 : ℝ) : EReal) * ((gSupport x : ℝ) : EReal)) := by
  rcases helperForTheorem_21_2_supportWeightedAffine_properConvex_and_dom
      C fAffine hAffine lamAffineSupport with
    ⟨gSupport, hgSupport, hproperSupport, hdomSupport⟩
  let fAug : Fin (k + 1) → (Fin n → ℝ) → EReal :=
    Fin.append fStrict (fun _ x => ((gSupport x : ℝ) : EReal))
  have hfAug :
      ∀ q : Fin (k + 1),
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fAug q) := by
    intro q
    refine Fin.addCases ?_ ?_ q
    · intro i
      simpa [fAug] using hfStrict i
    · intro j
      have hj0 : j = (0 : Fin 1) := Subsingleton.elim j 0
      subst hj0
      simpa [fAug] using hproperSupport
  have hdomAug :
      ∀ q : Fin (k + 1),
        euclideanRelativeInterior_fin n C ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fAug q) := by
    intro q
    refine Fin.addCases ?_ ?_ q
    · intro i
      simpa [fAug] using hdomStrict i
    · intro j
      have hj0 : j = (0 : Fin 1) := Subsingleton.elim j 0
      subst hj0
      simpa [fAug] using hdomSupport
  have hNoAugPrimal :
      ¬ (∃ x, x ∈ C ∧ (∀ q : Fin (k + 1), fAug q x < (0 : EReal))) := by
    intro hAugPrimal
    rcases hAugPrimal with ⟨x, hxC, hxAugAll⟩
    have hxStrict : ∀ i : Fin k, fStrict i x < (0 : EReal) := by
      intro i
      simpa [fAug] using hxAugAll (Fin.castAdd 1 i)
    have hSupportNonneg : 0 ≤ ∑ j : Fin l, lamAffineSupport j * fAffine j x :=
      hSupportOnStrictFeasible x hxC hxStrict
    have hxAugLast : ((gSupport x : ℝ) : EReal) < (0 : EReal) := by
      simpa [fAug] using hxAugAll (Fin.natAdd k (0 : Fin 1))
    have hxSupportNeg : gSupport x < 0 := (EReal.coe_lt_coe_iff).1 hxAugLast
    have hxSupportNonnegReal : 0 ≤ gSupport x := by
      simpa [hgSupport x] using hSupportNonneg
    exact (not_lt_of_ge hxSupportNonnegReal) hxSupportNeg
  have hAlt :=
    theorem21_convex_inequality_alternative C hC (Nat.succ_pos k) fAug hfAug hdomAug
  rw [xor_def] at hAlt
  rcases hAlt with hAugPrimalOrNoDual | hAugDualOrNoPrimal
  · rcases hAugPrimalOrNoDual with ⟨hAugPrimal, _hNoDual⟩
    exact False.elim (hNoAugPrimal hAugPrimal)
  · rcases hAugDualOrNoPrimal with ⟨hAugDual, _hNoPrimal⟩
    rcases hAugDual with ⟨w, hw_nonneg, hw_nontriv, hglobal⟩
    have hw_split_nontriv :
        (∃ i : Fin k, w (Fin.castAdd 1 i) ≠ 0) ∨ w (Fin.natAdd k (0 : Fin 1)) ≠ 0 := by
      rcases hw_nontriv with ⟨q, hq⟩
      by_cases hqk : (q : ℕ) < k
      · let i : Fin k := ⟨(q : ℕ), hqk⟩
        have hqeq : q = Fin.castAdd 1 i := by
          apply Fin.ext
          rfl
        exact Or.inl ⟨i, by simpa [hqeq] using hq⟩
      · have hqge : k ≤ (q : ℕ) := Nat.le_of_not_lt hqk
        have hqle : (q : ℕ) ≤ k := Nat.le_of_lt_succ q.is_lt
        have hqeqNat : (q : ℕ) = k := le_antisymm hqle hqge
        have hqeq : q = Fin.natAdd k (0 : Fin 1) := by
          apply Fin.ext
          simp [hqeqNat]
        exact Or.inr (by simpa [hqeq] using hq)
    refine ⟨gSupport, hgSupport, ?_⟩
    refine ⟨(fun i => w (Fin.castAdd 1 i)), w (Fin.natAdd k (0 : Fin 1)), ?_, ?_, ?_, ?_⟩
    · intro i
      exact hw_nonneg (Fin.castAdd 1 i)
    · exact hw_nonneg (Fin.natAdd k (0 : Fin 1))
    · rcases hw_split_nontriv with hstrict | hlast
      · exact Or.inl hstrict
      · exact Or.inr hlast
    · intro x hxC
      -- Expand the appended sum into strict and support-weighted components.
      simpa [fAug, Fin.sum_univ_add] using hglobal x hxC

/-- Helper for Theorem 21.2: when the strict multiplier block is zero, augmented
nontriviality forces the scalar multiplier to be nonzero. -/
lemma helperForTheorem_21_2_muStrictZero_forces_mu0_nonzero
    {k : ℕ}
    (muStrict : Fin k → ℝ)
    (mu0 : ℝ)
    (hmu_nontriv : ((∃ i : Fin k, muStrict i ≠ 0) ∨ mu0 ≠ 0))
    (hmuStrict_zero : muStrict = 0) :
    mu0 ≠ 0 := by
  -- Eliminate the strict-block disjunct by rewriting `muStrict` pointwise with `0`.
  rcases hmu_nontriv with hstrict | hmu0
  · rcases hstrict with ⟨i, hi⟩
    have hzero_i : muStrict i = 0 := by
      simp [hmuStrict_zero]
    exact False.elim (hi hzero_i)
  · exact hmu0

/-- Helper for Theorem 21.2: if the strict multiplier block vanishes, the augmented
global inequality forces the support functional to be nonnegative on `C`. -/
lemma helperForTheorem_21_2_muStrictZero_implies_gSupport_nonneg_on_C
    {n k : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (gSupport : (Fin n → ℝ) →ᵃ[ℝ] ℝ)
    (muStrict : Fin k → ℝ)
    (mu0 : ℝ)
    (hmu0_nonneg : 0 ≤ mu0)
    (hmu_global :
      ∀ x, x ∈ C →
        (0 : EReal) ≤
          (∑ i : Fin k, ((muStrict i : ℝ) : EReal) * fStrict i x) +
            ((mu0 : ℝ) : EReal) * ((gSupport x : ℝ) : EReal))
    (hmu_nontriv : ((∃ i : Fin k, muStrict i ≠ 0) ∨ mu0 ≠ 0))
    (hmuStrict_zero : muStrict = 0) :
    ∀ x, x ∈ C → 0 ≤ gSupport x := by
  have hmu0_nonzero : mu0 ≠ 0 :=
    helperForTheorem_21_2_muStrictZero_forces_mu0_nonzero
      muStrict mu0 hmu_nontriv hmuStrict_zero
  have hmu0_pos : 0 < mu0 := lt_of_le_of_ne hmu0_nonneg (Ne.symm hmu0_nonzero)
  intro x hxC
  -- With `muStrict = 0`, the strict block contributes no mass to the augmented inequality.
  have hstrict_sum_zero :
      (∑ i : Fin k, ((muStrict i : ℝ) : EReal) * fStrict i x) = (0 : EReal) := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    simp [hmuStrict_zero]
  have hmuScaled_nonneg :
      (0 : EReal) ≤ ((mu0 : ℝ) : EReal) * ((gSupport x : ℝ) : EReal) := by
    simpa [hstrict_sum_zero] using hmu_global x hxC
  -- Convert back to `ℝ` and use `mu0 > 0` to divide out the positive scalar.
  have hmul_nonneg_real : 0 ≤ mu0 * gSupport x := by
    have hmul_nonneg_ereal :
        (((0 : ℝ) : EReal) ≤ (((mu0 * gSupport x : ℝ) : EReal))) := by
      simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc] using hmuScaled_nonneg
    exact (EReal.coe_le_coe_iff).1 hmul_nonneg_ereal
  exact nonneg_of_mul_nonneg_right hmul_nonneg_real hmu0_pos

/-- Helper for Theorem 21.2: rewrite support nonnegativity on `C` into nonnegativity of
the weighted affine sum on strict-feasible points using `gSupport`'s affine-expansion
identity. -/
lemma helperForTheorem_21_2_support_nonneg_on_C_to_weightedAffine_nonneg_on_strictFeasible
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (lamAffineSupport : Fin l → ℝ)
    (gSupport : (Fin n → ℝ) →ᵃ[ℝ] ℝ)
    (hgSupport : ∀ x : Fin n → ℝ, gSupport x = ∑ j : Fin l, lamAffineSupport j * fAffine j x)
    (hSupport_nonneg_on_C : ∀ x, x ∈ C → 0 ≤ gSupport x) :
    ∀ x, x ∈ C → (∀ i : Fin k, fStrict i x < (0 : EReal)) →
      0 ≤ ∑ j : Fin l, lamAffineSupport j * fAffine j x := by
  intro x hxC _hxStrict
  -- The strict-feasibility premise is carried for interface compatibility with `U`-witnesses;
  -- numerically, this step is just the affine expansion rewrite.
  simpa [hgSupport x] using hSupport_nonneg_on_C x hxC

/-- Helper for Theorem 21.2: transport support nonnegativity from `C` to the
strict-feasible affine upper hull `U` using the `U` witness representation and
coordinatewise monotonicity from nonnegative affine multipliers. -/
lemma helperForTheorem_21_2_support_nonneg_on_C_lifts_to_U_support_nonneg_of_lam_nonneg
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (U : Set (Fin l → ℝ))
    (hU_def :
      U = {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)})
    (lamAffineSupport : Fin l → ℝ)
    (hlamAffineSupport_nonneg : ∀ j : Fin l, 0 ≤ lamAffineSupport j)
    (gSupport : (Fin n → ℝ) →ᵃ[ℝ] ℝ)
    (hgSupport : ∀ x : Fin n → ℝ, gSupport x = ∑ j : Fin l, lamAffineSupport j * fAffine j x)
    (hSupport_nonneg_on_C : ∀ x, x ∈ C → 0 ≤ gSupport x) :
    ∀ u, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j := by
  intro u huU
  rcases (by simpa [hU_def] using huU) with ⟨x, hxC, hxStrict, hxLeU⟩
  -- First pull nonnegativity to the strict-feasible witness point `x`.
  have hbase :
      0 ≤ ∑ j : Fin l, lamAffineSupport j * fAffine j x :=
    helperForTheorem_21_2_support_nonneg_on_C_to_weightedAffine_nonneg_on_strictFeasible
      C fStrict fAffine lamAffineSupport gSupport hgSupport hSupport_nonneg_on_C x hxC hxStrict
  -- Then use coordinatewise monotonicity of the weighted sum under `fAffine x ≤ u`.
  have hsum_le :
      (∑ j : Fin l, lamAffineSupport j * fAffine j x) ≤
        (∑ j : Fin l, lamAffineSupport j * u j) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact mul_le_mul_of_nonneg_left (hxLeU j) (hlamAffineSupport_nonneg j)
  exact le_trans hbase hsum_le

/-- Helper for Theorem 21.2: in boundary-data form, transport support nonnegativity
from `C` to all points of the strict-feasible affine upper hull `U`. -/
lemma helperForTheorem_21_2_boundaryData_support_nonneg_on_U
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (U : Set (Fin l → ℝ))
    (hU_def :
      U = {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)})
    (lamAffineSupport : Fin l → ℝ)
    (hlamAffineSupport_nonneg : ∀ j : Fin l, 0 ≤ lamAffineSupport j)
    (gSupport : (Fin n → ℝ) →ᵃ[ℝ] ℝ)
    (hgSupport : ∀ x : Fin n → ℝ, gSupport x = ∑ j : Fin l, lamAffineSupport j * fAffine j x)
    (hSupport_nonneg_on_C : ∀ x, x ∈ C → 0 ≤ gSupport x) :
    ∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j := by
  -- Route correction: make the `C → U` transport explicit so the unresolved work is
  -- only the external separator bridge from support-nonnegativity to `0 ∈ U`.
  exact helperForTheorem_21_2_support_nonneg_on_C_lifts_to_U_support_nonneg_of_lam_nonneg
    C fStrict fAffine U hU_def lamAffineSupport hlamAffineSupport_nonneg
    gSupport hgSupport hSupport_nonneg_on_C

/-- Helper for Theorem 21.2: in the all-shifted-primal context, the affine-only
augmented branch (`muStrict = 0`) should force `0 ∈ U` via the Theorem 20.2 /
Corollary 7.3.3 closure-support bridge. -/
lemma helperForTheorem_21_2_muStrictZero_forces_zeroMemU_via_theorem20_2
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (U : Set (Fin l → ℝ))
    (_hU_def :
      U = {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)})
    (_hzeroMemClosureU : (fun _ : Fin l => (0 : ℝ)) ∈ closure U)
    (_hUconv : Convex ℝ U)
    (_hUupper : ∀ {u v : Fin l → ℝ}, u ∈ U → (∀ j : Fin l, u j ≤ v j) → v ∈ U)
    (gSupport : (Fin n → ℝ) →ᵃ[ℝ] ℝ)
    (muStrict : Fin k → ℝ)
    (mu0 : ℝ)
    (_hmuStrict_nonneg : ∀ i : Fin k, 0 ≤ muStrict i)
    (hmu0_nonneg : 0 ≤ mu0)
    (hmu_global :
      ∀ x, x ∈ C →
        (0 : EReal) ≤
          (∑ i : Fin k, ((muStrict i : ℝ) : EReal) * fStrict i x) +
            ((mu0 : ℝ) : EReal) * ((gSupport x : ℝ) : EReal))
    (hmu_nontriv : ((∃ i : Fin k, muStrict i ≠ 0) ∨ mu0 ≠ 0))
    (hmuStrict_zero : muStrict = 0)
    (hBridge :
      (∀ x, x ∈ C → 0 ≤ gSupport x) →
        (fun _ : Fin l => (0 : ℝ)) ∈ U) :
    (fun _ : Fin l => (0 : ℝ)) ∈ U := by
  -- Normalize the affine-only branch into a real-valued support nonnegativity statement.
  have hgSupport_nonneg_on_C : ∀ x, x ∈ C → 0 ≤ gSupport x :=
    helperForTheorem_21_2_muStrictZero_implies_gSupport_nonneg_on_C
      C fStrict gSupport muStrict mu0 hmu0_nonneg hmu_global hmu_nontriv hmuStrict_zero
  -- Route correction: consume the hard geometric bridge through an explicit callback.
  exact hBridge hgSupport_nonneg_on_C

/-- Helper for Theorem 21.2: in the all-shifted-primal closure/support context, the
affine-only augmented branch (`muStrict = 0`) contradicts `0 ∉ U` once the
Theorem 20.2 + Corollary 7.3.3 bridge provides `0 ∈ U`. -/
lemma helperForTheorem_21_2_affineOnly_augmentedDual_contradiction_via_closure_support
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (_hNotPrimal :
      ¬ (∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ 0)))
    (U : Set (Fin l → ℝ))
    (_hU_def :
      U = {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)})
    (hzeroNotMemU : (fun _ : Fin l => (0 : ℝ)) ∉ U)
    (lamAffineSupport : Fin l → ℝ)
    (gSupport : (Fin n → ℝ) →ᵃ[ℝ] ℝ)
    (_hgSupport : ∀ x : Fin n → ℝ, gSupport x = ∑ j : Fin l, lamAffineSupport j * fAffine j x)
    (muStrict : Fin k → ℝ)
    (mu0 : ℝ)
    (_hmuStrict_nonneg : ∀ i : Fin k, 0 ≤ muStrict i)
    (_hmu0_nonneg : 0 ≤ mu0)
    (_hmu_global :
      ∀ x, x ∈ C →
        (0 : EReal) ≤
          (∑ i : Fin k, ((muStrict i : ℝ) : EReal) * fStrict i x) +
            ((mu0 : ℝ) : EReal) * ((gSupport x : ℝ) : EReal))
    (hmu_nontriv : ((∃ i : Fin k, muStrict i ≠ 0) ∨ mu0 ≠ 0))
    (hmuStrictZero_forces_zeroMemU :
      muStrict = 0 → (fun _ : Fin l => (0 : ℝ)) ∈ U)
    (hmuStrict_zero : muStrict = 0) :
    False := by
  -- Route correction: move the hard affine-only contradiction to the context where
  -- `U`-boundary geometry is already available, instead of forcing it from underconstrained data.
  have _hmu0_nonzero : mu0 ≠ 0 :=
    helperForTheorem_21_2_muStrictZero_forces_mu0_nonzero
      muStrict mu0 hmu_nontriv hmuStrict_zero
  have hzeroMemU : (fun _ : Fin l => (0 : ℝ)) ∈ U :=
    hmuStrictZero_forces_zeroMemU hmuStrict_zero
  exact hzeroNotMemU hzeroMemU

/-- Helper for Theorem 21.2: exclude the affine-only augmented dual branch (`muStrict = 0`)
once that branch has been converted into an explicit contradiction hypothesis. -/
lemma helperForTheorem_21_2_exclude_affineOnly_augmentedDual_via_theorem20_2_bridge
    {k : ℕ}
    (muStrict : Fin k → ℝ)
    (mu0 : ℝ)
    (_hmu_nontriv : ((∃ i : Fin k, muStrict i ≠ 0) ∨ mu0 ≠ 0))
    (hAffineOnlyContradiction : muStrict = 0 → False) :
    ∃ i : Fin k, muStrict i ≠ 0 := by
  -- Route correction: this helper is now a thin extraction wrapper; the geometric
  -- contradiction is provided explicitly from the all-shifted-primal branch.
  by_cases hExists : ∃ i : Fin k, muStrict i ≠ 0
  · exact hExists
  · have hMuStrictZero : muStrict = 0 := by
      -- If no strict coordinate is nonzero, the strict block vanishes pointwise.
      funext i
      by_contra hi
      exact hExists ⟨i, hi⟩
    exact False.elim (hAffineOnlyContradiction hMuStrictZero)

/-- Helper for Theorem 21.2: convert support data into a target dual certificate and enforce
strict-block nontriviality via the augmented alternative route. -/
lemma helperForTheorem_21_2_supportData_to_targetDual_strictNonzero
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (hfStrict : ∀ i : Fin k,
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStrict i))
    (hdomStrict :
      ∀ i : Fin k,
        euclideanRelativeInterior_fin n C ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fStrict i))
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hAffine : ∀ j : Fin l, ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, fAffine j = g)
    (lamAffineSupport : Fin l → ℝ)
    (hlamAffineSupport_nonneg : ∀ j : Fin l, 0 ≤ lamAffineSupport j)
    (hSupportOnStrictFeasible :
      ∀ x, x ∈ C → (∀ i : Fin k, fStrict i x < (0 : EReal)) →
        0 ≤ ∑ j : Fin l, lamAffineSupport j * fAffine j x)
    (hAffineOnlyContradiction :
      ∀ (gSupport : (Fin n → ℝ) →ᵃ[ℝ] ℝ)
        (_hgSupport : ∀ x : Fin n → ℝ,
          gSupport x = ∑ j : Fin l, lamAffineSupport j * fAffine j x)
        (muStrict : Fin k → ℝ)
        (mu0 : ℝ)
        (_hmuStrict_nonneg : ∀ i : Fin k, 0 ≤ muStrict i)
        (_hmu0_nonneg : 0 ≤ mu0)
        (_hmu_global :
          ∀ x, x ∈ C →
            (0 : EReal) ≤
              (∑ i : Fin k, ((muStrict i : ℝ) : EReal) * fStrict i x) +
                ((mu0 : ℝ) : EReal) * ((gSupport x : ℝ) : EReal))
        (_hmu_nontriv : ((∃ i : Fin k, muStrict i ≠ 0) ∨ mu0 ≠ 0)),
        muStrict = 0 → False) :
    ∃ lamStrict : Fin k → ℝ, ∃ lamAffine : Fin l → ℝ,
      (∀ i : Fin k, 0 ≤ lamStrict i) ∧
        (∀ j : Fin l, 0 ≤ lamAffine j) ∧
          (∃ i : Fin k, lamStrict i ≠ 0) ∧
            (∀ x, x ∈ C →
              (0 : EReal) ≤
                (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
                  ∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) := by
  -- Route correction: keep this lemma as a stable conversion layer, and import
  -- strict-block nontriviality from an explicit affine-only contradiction callback.
  rcases helperForTheorem_21_2_augmented_dual_from_supportData
      C hC fStrict hfStrict hdomStrict fAffine hAffine lamAffineSupport
      hSupportOnStrictFeasible with
    ⟨gSupport, hgSupport, muStrict, mu0, hmuStrict_nonneg, hmu0_nonneg, hmu_nontriv, hmu_global⟩
  have hmuStrict_nonzero : ∃ i : Fin k, muStrict i ≠ 0 :=
    helperForTheorem_21_2_exclude_affineOnly_augmentedDual_via_theorem20_2_bridge
      muStrict mu0 hmu_nontriv
      (hAffineOnlyContradiction gSupport hgSupport muStrict mu0
        hmuStrict_nonneg hmu0_nonneg hmu_global hmu_nontriv)
  refine ⟨muStrict, (fun j : Fin l => mu0 * lamAffineSupport j), hmuStrict_nonneg, ?_, hmuStrict_nonzero, ?_⟩
  · intro j
    exact mul_nonneg hmu0_nonneg (hlamAffineSupport_nonneg j)
  · intro x hxC
    -- Rewrite the support term so the augmented inequality matches target dual form.
    have haug := hmu_global x hxC
    have hsum_real :
        mu0 * gSupport x = ∑ j : Fin l, (mu0 * lamAffineSupport j) * fAffine j x := by
      calc
        mu0 * gSupport x = mu0 * (∑ j : Fin l, lamAffineSupport j * fAffine j x) := by
          rw [hgSupport x]
        _ = ∑ j : Fin l, mu0 * (lamAffineSupport j * fAffine j x) := by
          simpa using
            (Finset.mul_sum (s := (Finset.univ : Finset (Fin l)))
              (f := fun j : Fin l => lamAffineSupport j * fAffine j x) (a := mu0))
        _ = ∑ j : Fin l, (mu0 * lamAffineSupport j) * fAffine j x := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    have hscaledSupport :
        ((mu0 : ℝ) : EReal) * ((gSupport x : ℝ) : EReal) =
          ∑ j : Fin l, (((mu0 * lamAffineSupport j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) := by
      calc
        ((mu0 : ℝ) : EReal) * ((gSupport x : ℝ) : EReal)
            = (((mu0 * gSupport x : ℝ) : EReal)) := by simp [EReal.coe_mul]
        _ = (((∑ j : Fin l, (mu0 * lamAffineSupport j) * fAffine j x : ℝ) : ℝ) : EReal) := by
              rw [hsum_real]
        _ = ∑ j : Fin l, (((mu0 * lamAffineSupport j) * fAffine j x : ℝ) : EReal) := by
              simpa using helperForTheorem_21_1_coe_finset_sum_real
                (s := (Finset.univ : Finset (Fin l)))
                (g := fun j : Fin l => (mu0 * lamAffineSupport j) * fAffine j x)
        _ = ∑ j : Fin l, (((mu0 * lamAffineSupport j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [EReal.coe_mul, mul_assoc]
    have htarget :
        (0 : EReal) ≤
          (∑ i : Fin k, ((muStrict i : ℝ) : EReal) * fStrict i x) +
            ∑ j : Fin l, (((mu0 * lamAffineSupport j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) := by
      calc
        (0 : EReal) ≤
            (∑ i : Fin k, ((muStrict i : ℝ) : EReal) * fStrict i x) +
              ((mu0 : ℝ) : EReal) * ((gSupport x : ℝ) : EReal) := haug
        _ =
            (∑ i : Fin k, ((muStrict i : ℝ) : EReal) * fStrict i x) +
              ∑ j : Fin l, (((mu0 * lamAffineSupport j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) := by
              rw [hscaledSupport]
    simpa using htarget

/-- Helper for Theorem 21.2: support nonnegativity on `U` extends from `U` to `closure U`
for the fixed weighted-sum functional `u ↦ ∑ j, lamAffineSupport j * u j`. -/
lemma helperForTheorem_21_2_support_nonneg_on_closure_of_support_nonneg_on_U
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hSupport_nonneg_on_U :
      ∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) :
    ∀ u : Fin l → ℝ, u ∈ closure U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j := by
  -- Package the weighted sum as a continuous real map.
  let weightedSum : (Fin l → ℝ) → ℝ := fun u => ∑ j : Fin l, lamAffineSupport j * u j
  have hWeightedSum_cont : Continuous weightedSum := by
    continuity
  -- The nonnegativity region of `weightedSum` is closed, so closure preserves membership.
  have hU_subset_nonneg : U ⊆ {u : Fin l → ℝ | 0 ≤ weightedSum u} := by
    intro u huU
    simpa [weightedSum] using hSupport_nonneg_on_U u huU
  have hNonneg_closed : IsClosed {u : Fin l → ℝ | 0 ≤ weightedSum u} := by
    exact isClosed_le continuous_const hWeightedSum_cont
  have hClosure_subset_nonneg : closure U ⊆ {u : Fin l → ℝ | 0 ≤ weightedSum u} :=
    closure_minimal hU_subset_nonneg hNonneg_closed
  intro u huClosure
  exact hClosure_subset_nonneg huClosure

/-- Helper for Theorem 21.2: support nonnegativity on `U` implies nonnegativity of the
weighted sum at the origin whenever `(fun _ => 0) ∈ closure U`. -/
lemma helperForTheorem_21_2_support_nonneg_at_zero_of_zeroMemClosure
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hzeroMemClosureU : (fun _ : Fin l => (0 : ℝ)) ∈ closure U)
    (hSupport_nonneg_on_U :
      ∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) :
    0 ≤ ∑ j : Fin l, lamAffineSupport j * (fun _ : Fin l => (0 : ℝ)) j := by
  -- Extend support nonnegativity from `U` to its closure.
  have hSupport_nonneg_on_closureU :
      ∀ u : Fin l → ℝ, u ∈ closure U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j :=
    helperForTheorem_21_2_support_nonneg_on_closure_of_support_nonneg_on_U
      U lamAffineSupport hSupport_nonneg_on_U
  -- Evaluate the closure inequality at the closure point `0`.
  exact hSupport_nonneg_on_closureU (fun _ : Fin l => (0 : ℝ)) hzeroMemClosureU

/-- Helper for Theorem 21.2: to prove `(fun _ => 0) ∈ U` from support data, it suffices
to derive a contradiction from the temporary assumption `(fun _ => 0) ∉ U`. -/
lemma helperForTheorem_21_2_zeroMemU_of_zeroNotMemU_contradiction
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (hzeroNotMemU_contradiction :
      ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False) :
    (fun _ : Fin l => (0 : ℝ)) ∈ U := by
  -- Turn a contradiction-under-negation proof into direct membership.
  by_contra hzeroNotMemU
  exact hzeroNotMemU_contradiction hzeroNotMemU

/-- Helper for Theorem 21.2: a contradiction-form bridge under temporary
`(fun _ => 0) ∉ U` curries to the callback shape
`support_nonneg_on_U → (fun _ => 0) ∈ U`. -/
lemma helperForTheorem_21_2_supportNonneg_to_zeroMemU_of_zeroNotMemU_contradictionBridge
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hSupportNonneg_zeroNotMemU_contradiction :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False) :
    (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
      (fun _ : Fin l => (0 : ℝ)) ∈ U := by
  intro hSupport_nonneg_on_U
  -- Route correction: first specialize the contradiction bridge at the current support data.
  have hzeroNotMemU_contradiction :
      ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False :=
    hSupportNonneg_zeroNotMemU_contradiction hSupport_nonneg_on_U
  -- Then convert contradiction-under-negation to direct membership.
  exact helperForTheorem_21_2_zeroMemU_of_zeroNotMemU_contradiction
    U hzeroNotMemU_contradiction

/-- Helper for Theorem 21.2: specialize an external contradiction bridge of the form
`support_nonneg_on_U → (0 ∉ U → False)` at the current support and boundary data. -/
lemma helperForTheorem_21_2_false_of_support_nonneg_and_externalZeroNotMemU_bridge
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hExternalBridge :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False)
    (hSupport_nonneg_on_U :
      ∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j)
    (hzeroNotMemU : (fun _ : Fin l => (0 : ℝ)) ∉ U) :
    False := by
  -- Specialize the external bridge at the current support and non-membership hypotheses.
  exact hExternalBridge hSupport_nonneg_on_U hzeroNotMemU

/-- Helper for Theorem 21.2: once the dependency-level Section 20 / Corollary 7.3.3
bridge is provided in the current all-shifted context, specialize it to the present
support and boundary hypotheses to obtain the required contradiction. -/
lemma helperForTheorem_21_2_external_supportNonneg_zeroNotMemU_contradiction_of_dependencyBridge
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hDependencyBridge :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False)
    (hSupport_nonneg_on_U :
      ∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j)
    (hzeroNotMemU : (fun _ : Fin l => (0 : ℝ)) ∉ U) :
    False := by
  -- Route correction: keep this as a pure specialization adapter, so the only remaining
  -- blocker is proving the dependency-level bridge itself.
  exact hDependencyBridge hSupport_nonneg_on_U hzeroNotMemU

/-- Helper for Theorem 21.2: external dependency-level bridge in the all-shifted-primal
boundary-data context; from support nonnegativity on `U` and temporary `0 ∉ U`, derive
the contradiction needed to conclude `0 ∈ U`. -/
lemma helperForTheorem_21_2_external_supportNonneg_zeroNotMemU_contradiction_in_allShifted_context
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (U : Set (Fin l → ℝ))
    (_hU_def :
      U = {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)})
    (_hFeasRi : ∃ x, x ∈ euclideanRelativeInterior_fin n C ∧ ∀ j : Fin l, fAffine j x ≤ 0)
    (_hAllShiftedPrimal :
      ∀ ε : ℝ, 0 < ε →
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x < ε))
    (_hNotPrimal :
      ¬ (∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ 0)))
    (_hzeroMemClosureU : (fun _ : Fin l => (0 : ℝ)) ∈ closure U)
    (_hUconv : Convex ℝ U)
    (_hUupper : ∀ {u v : Fin l → ℝ}, u ∈ U → (∀ j : Fin l, u j ≤ v j) → v ∈ U)
    (lamAffineSupport : Fin l → ℝ)
    (_hlamAffineSupport_nonneg : ∀ j : Fin l, 0 ≤ lamAffineSupport j)
    (hDependencyBridge :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False)
    (hSupport_nonneg_on_U :
      ∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j)
    (hzeroNotMemU : (fun _ : Fin l => (0 : ℝ)) ∉ U) :
    False := by
  -- Route correction: keep this declaration as a thin adapter once the dependency-level
  -- bridge is supplied explicitly by the caller.
  exact
    helperForTheorem_21_2_external_supportNonneg_zeroNotMemU_contradiction_of_dependencyBridge
      U lamAffineSupport hDependencyBridge hSupport_nonneg_on_U hzeroNotMemU

/-- Helper for Theorem 21.2: dependency-level Section 20 / Corollary 7.3.3 bridge
specialized to the all-shifted strict-feasible affine upper-hull context, used as
an adapter once the external bridge is supplied explicitly. -/
lemma helperForTheorem_21_2_dependencyBridge_supportNonneg_zeroNotMemU_in_allShifted_context
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (U : Set (Fin l → ℝ))
    (_hU_def :
      U = {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)})
    (_hFeasRi : ∃ x, x ∈ euclideanRelativeInterior_fin n C ∧ ∀ j : Fin l, fAffine j x ≤ 0)
    (_hAllShiftedPrimal :
      ∀ ε : ℝ, 0 < ε →
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x < ε))
    (_hNotPrimal :
      ¬ (∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ 0)))
    (_hzeroMemClosureU : (fun _ : Fin l => (0 : ℝ)) ∈ closure U)
    (_hUconv : Convex ℝ U)
    (_hUupper : ∀ {u v : Fin l → ℝ}, u ∈ U → (∀ j : Fin l, u j ≤ v j) → v ∈ U)
    (lamAffineSupport : Fin l → ℝ)
    (_hlamAffineSupport_nonneg : ∀ j : Fin l, 0 ≤ lamAffineSupport j)
    (hExternalDependencyBridge :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False) :
    (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
      ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False := by
  -- Route correction: this helper no longer tries to derive the bridge from
  -- underconstrained local assumptions; it only specializes an explicit dependency-level
  -- Section 20 / Corollary 7.3.3 bridge provided by the caller.
  exact hExternalDependencyBridge

/-- Helper for Theorem 21.2: once the all-shifted dependency bridge is available,
specialize it to the current support and temporary non-membership assumptions. -/
lemma helperForTheorem_21_2_supportNonneg_zeroNotMemU_contradiction_of_dependencyBridge_in_allShifted_context
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (U : Set (Fin l → ℝ))
    (hU_def :
      U = {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)})
    (hFeasRi : ∃ x, x ∈ euclideanRelativeInterior_fin n C ∧ ∀ j : Fin l, fAffine j x ≤ 0)
    (hAllShiftedPrimal :
      ∀ ε : ℝ, 0 < ε →
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x < ε))
    (hNotPrimal :
      ¬ (∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ 0)))
    (hzeroMemClosureU : (fun _ : Fin l => (0 : ℝ)) ∈ closure U)
    (hUconv : Convex ℝ U)
    (hUupper : ∀ {u v : Fin l → ℝ}, u ∈ U → (∀ j : Fin l, u j ≤ v j) → v ∈ U)
    (lamAffineSupport : Fin l → ℝ)
    (hlamAffineSupport_nonneg : ∀ j : Fin l, 0 ≤ lamAffineSupport j)
    (hDependencyBridge :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False)
    (hSupport_nonneg_on_U :
      ∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j)
    (hzeroNotMemU : (fun _ : Fin l => (0 : ℝ)) ∉ U) :
    False := by
  -- Route correction: use the existing all-shifted adapter and avoid nested bridge stubs.
  exact
    helperForTheorem_21_2_external_supportNonneg_zeroNotMemU_contradiction_in_allShifted_context
      C fStrict fAffine U hU_def hFeasRi hAllShiftedPrimal hNotPrimal
      hzeroMemClosureU hUconv hUupper
      lamAffineSupport hlamAffineSupport_nonneg hDependencyBridge
      hSupport_nonneg_on_U hzeroNotMemU

/-- Helper for Theorem 21.2: in the all-shifted branch, convert an external
dependency-level contradiction bridge into the local dependency-bridge callback
used by the affine-only contradiction step. -/
lemma helperForTheorem_21_2_affineOnly_localDependencyBridge_of_external_in_allShifted_context
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (U : Set (Fin l → ℝ))
    (hU_def :
      U = {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)})
    (hFeasRi : ∃ x, x ∈ euclideanRelativeInterior_fin n C ∧ ∀ j : Fin l, fAffine j x ≤ 0)
    (hAllShiftedPrimal :
      ∀ ε : ℝ, 0 < ε →
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x < ε))
    (hNotPrimal :
      ¬ (∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ 0)))
    (hzeroMemClosureU : (fun _ : Fin l => (0 : ℝ)) ∈ closure U)
    (hUconv : Convex ℝ U)
    (hUupper : ∀ {u v : Fin l → ℝ}, u ∈ U → (∀ j : Fin l, u j ≤ v j) → v ∈ U)
    (lamAffineSupport : Fin l → ℝ)
    (hlamAffineSupport_nonneg : ∀ j : Fin l, 0 ≤ lamAffineSupport j)
    (hExternalDependencyBridge :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False) :
    (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
      ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False := by
  -- Route correction: isolate the dependency bridge conversion at one named call site.
  exact
    helperForTheorem_21_2_dependencyBridge_supportNonneg_zeroNotMemU_in_allShifted_context
      C fStrict fAffine U hU_def hFeasRi hAllShiftedPrimal hNotPrimal
      hzeroMemClosureU hUconv hUupper
      lamAffineSupport hlamAffineSupport_nonneg hExternalDependencyBridge

/-- Helper for Theorem 21.2: reformulate the contradiction-callback bridge
`support_nonneg_on_U → (0 ∉ U → False)` as the equivalent membership-callback
`support_nonneg_on_U → (0 ∈ U)`. -/
lemma helperForTheorem_21_2_supportNonneg_zeroNotMemU_bridge_iff_supportNonneg_to_zeroMemU
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ) :
    ((∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
      ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False) ↔
      ((∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        (fun _ : Fin l => (0 : ℝ)) ∈ U) := by
  constructor
  · intro hContradictionCallback hSupport_nonneg_on_U
    -- Convert contradiction-under-negation at fixed support data into direct membership.
    exact
      helperForTheorem_21_2_zeroMemU_of_zeroNotMemU_contradiction
        U (hContradictionCallback hSupport_nonneg_on_U)
  · intro hMembershipCallback hSupport_nonneg_on_U hzeroNotMemU
    -- Membership at the same support data contradicts the temporary non-membership premise.
    exact hzeroNotMemU (hMembershipCallback hSupport_nonneg_on_U)

/-- Helper for Theorem 21.2: convert a membership callback
`support_nonneg_on_U → (0 ∈ U)` into the contradiction callback
`support_nonneg_on_U → (0 ∉ U → False)`. -/
lemma helperForTheorem_21_2_supportNonneg_zeroNotMemU_contradictionCallback_of_zeroMemU_callback
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hSupportNonneg_to_zeroMemU :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        (fun _ : Fin l => (0 : ℝ)) ∈ U) :
    (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
      ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False := by
  intro hSupport_nonneg_on_U hzeroNotMemU
  -- Evaluate the membership callback at the current support data.
  have hzeroMemU : (fun _ : Fin l => (0 : ℝ)) ∈ U :=
    hSupportNonneg_to_zeroMemU hSupport_nonneg_on_U
  -- Contradict the temporary non-membership assumption.
  exact hzeroNotMemU hzeroMemU

/-- Helper for Theorem 21.2: if support nonnegativity holds on `U`, then any witness
`u ∈ U` with strictly negative support sum is impossible. -/
lemma helperForTheorem_21_2_supportNonneg_on_U_contradicts_exists_negative_support_witness
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hSupport_nonneg_on_U :
      ∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j)
    (hExistsNegativeSupportWitness :
      ∃ u : Fin l → ℝ, u ∈ U ∧ (∑ j : Fin l, lamAffineSupport j * u j) < 0) :
    False := by
  rcases hExistsNegativeSupportWitness with ⟨u, huU, huNeg⟩
  -- Evaluate support nonnegativity at the witness point.
  have huNonneg : 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j :=
    hSupport_nonneg_on_U u huU
  -- A strict negative witness contradicts the nonnegativity certificate.
  exact (not_lt_of_ge huNonneg) huNeg

/-- Helper for Theorem 21.2: if no point of `U` has strictly negative support sum,
then the support sum is nonnegative at every point of `U`. -/
lemma helperForTheorem_21_2_supportNonneg_on_U_of_not_exists_negative_support_witness
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hNoNegativeSupportWitness :
      ¬ ∃ u : Fin l → ℝ, u ∈ U ∧ (∑ j : Fin l, lamAffineSupport j * u j) < 0) :
    ∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j := by
  intro u huU
  -- Route correction: prove support nonnegativity by contradiction at each fixed `u`.
  by_contra huNonneg
  have huNeg : (∑ j : Fin l, lamAffineSupport j * u j) < 0 := lt_of_not_ge huNonneg
  exact hNoNegativeSupportWitness ⟨u, huU, huNeg⟩

/-- Helper for Theorem 21.2: an external contradiction callback of the form
`support_nonneg_on_U → (0 ∉ U → False)` turns temporary `0 ∉ U` into a strictly
negative support witness in `U`. -/
lemma helperForTheorem_21_2_exists_negative_support_witness_of_zeroNotMemU_and_supportNonneg_contradictionCallback
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hSupportNonneg_zeroNotMemU_contradiction :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False)
    (hzeroNotMemU : (fun _ : Fin l => (0 : ℝ)) ∉ U) :
    ∃ u : Fin l → ℝ, u ∈ U ∧ (∑ j : Fin l, lamAffineSupport j * u j) < 0 := by
  -- Route correction: isolate the pure logical conversion from contradiction callback
  -- to existence of a strictly negative witness.
  by_contra hNoNegativeSupportWitness
  have hSupport_nonneg_on_U :
      ∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j :=
    helperForTheorem_21_2_supportNonneg_on_U_of_not_exists_negative_support_witness
      U lamAffineSupport hNoNegativeSupportWitness
  -- Apply the external callback at the derived nonnegativity certificate.
  exact hSupportNonneg_zeroNotMemU_contradiction hSupport_nonneg_on_U hzeroNotMemU

/-- Helper for Theorem 21.2: a callback of the form
`support_nonneg_on_U → (fun _ => 0) ∈ U` can be turned into the witness bridge
`(fun _ => 0) ∉ U → ∃ u ∈ U, Σ_j lam_j u_j < 0`. -/
lemma helperForTheorem_21_2_exists_negative_support_witness_of_zeroNotMemU_and_zeroMemU_callback
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hSupportNonneg_to_zeroMemU :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        (fun _ : Fin l => (0 : ℝ)) ∈ U)
    (hzeroNotMemU : (fun _ : Fin l => (0 : ℝ)) ∉ U) :
    ∃ u : Fin l → ℝ, u ∈ U ∧ (∑ j : Fin l, lamAffineSupport j * u j) < 0 := by
  -- Route correction: first convert the membership callback into a contradiction callback.
  have hSupportNonneg_zeroNotMemU_contradiction :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False :=
    helperForTheorem_21_2_supportNonneg_zeroNotMemU_contradictionCallback_of_zeroMemU_callback
      U lamAffineSupport hSupportNonneg_to_zeroMemU
  -- Then reuse the generic logical extractor from contradiction callback to witness.
  exact
    helperForTheorem_21_2_exists_negative_support_witness_of_zeroNotMemU_and_supportNonneg_contradictionCallback
      U lamAffineSupport hSupportNonneg_zeroNotMemU_contradiction hzeroNotMemU

/-- Helper for Theorem 21.2: in the all-shifted boundary-data context, an external
contradiction callback of the form `support_nonneg_on_U → (0 ∉ U → False)` yields
a strictly negative support witness in `U`. -/
lemma helperForTheorem_21_2_allShifted_exists_negative_support_witness_of_external_contradictionCallback
    {n k l : ℕ}
    (_C : Set (Fin n → ℝ))
    (_fStrict : Fin k → (Fin n → ℝ) → EReal)
    (_fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (U : Set (Fin l → ℝ))
    (_hU_def :
      U = {u : Fin l → ℝ |
        ∃ x, x ∈ _C ∧ (∀ i : Fin k, _fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, _fAffine j x ≤ u j)})
    (_hFeasRi : ∃ x, x ∈ euclideanRelativeInterior_fin n _C ∧ ∀ j : Fin l, _fAffine j x ≤ 0)
    (_hAllShiftedPrimal :
      ∀ ε : ℝ, 0 < ε →
        ∃ x, x ∈ _C ∧ (∀ i : Fin k, _fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, _fAffine j x < ε))
    (_hNotPrimal :
      ¬ (∃ x, x ∈ _C ∧ (∀ i : Fin k, _fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, _fAffine j x ≤ 0)))
    (_hzeroMemClosureU : (fun _ : Fin l => (0 : ℝ)) ∈ closure U)
    (_hUconv : Convex ℝ U)
    (_hUupper : ∀ {u v : Fin l → ℝ}, u ∈ U → (∀ j : Fin l, u j ≤ v j) → v ∈ U)
    (lamAffineSupport : Fin l → ℝ)
    (_hlamAffineSupport_nonneg : ∀ j : Fin l, 0 ≤ lamAffineSupport j)
    (hSupportNonneg_zeroNotMemU_contradiction :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False)
    (hzeroNotMemU : (fun _ : Fin l => (0 : ℝ)) ∉ U) :
    ∃ u : Fin l → ℝ, u ∈ U ∧ (∑ j : Fin l, lamAffineSupport j * u j) < 0 := by
  -- Route correction: keep all geometric assumptions explicit, but delegate the
  -- logical witness extraction to the generic contradiction-callback helper.
  exact
    helperForTheorem_21_2_exists_negative_support_witness_of_zeroNotMemU_and_supportNonneg_contradictionCallback
      U lamAffineSupport hSupportNonneg_zeroNotMemU_contradiction hzeroNotMemU

/-- Helper for Theorem 21.2: dependency-level Section 20 / Corollary 7.3.3 bridge,
in all-shifted boundary-data form, turning `0 ∉ U` into a strictly negative support
witness in `U`. -/
lemma helperForTheorem_21_2_allShifted_zeroNotMemU_implies_exists_negative_support_witness_dependencyBridge
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (U : Set (Fin l → ℝ))
    (_hU_def :
      U = {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)})
    (_hFeasRi : ∃ x, x ∈ euclideanRelativeInterior_fin n C ∧ ∀ j : Fin l, fAffine j x ≤ 0)
    (_hAllShiftedPrimal :
      ∀ ε : ℝ, 0 < ε →
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x < ε))
    (_hNotPrimal :
      ¬ (∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ 0)))
    (_hzeroMemClosureU : (fun _ : Fin l => (0 : ℝ)) ∈ closure U)
    (_hUconv : Convex ℝ U)
    (_hUupper : ∀ {u v : Fin l → ℝ}, u ∈ U → (∀ j : Fin l, u j ≤ v j) → v ∈ U)
    (lamAffineSupport : Fin l → ℝ)
    (_hlamAffineSupport_nonneg : ∀ j : Fin l, 0 ≤ lamAffineSupport j)
    (hSupportNonneg_zeroNotMemU_contradiction :
      (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
        ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False)
    (hzeroNotMemU : (fun _ : Fin l => (0 : ℝ)) ∉ U) :
    ∃ u : Fin l → ℝ, u ∈ U ∧ (∑ j : Fin l, lamAffineSupport j * u j) < 0 := by
  -- Route correction: the previous route tried to derive this bridge from underconstrained
  -- local hypotheses; the corrected route requires the explicit contradiction callback.
  exact
    helperForTheorem_21_2_allShifted_exists_negative_support_witness_of_external_contradictionCallback
      C fStrict fAffine U _hU_def _hFeasRi _hAllShiftedPrimal _hNotPrimal
      _hzeroMemClosureU _hUconv _hUupper
      lamAffineSupport _hlamAffineSupport_nonneg
      hSupportNonneg_zeroNotMemU_contradiction hzeroNotMemU

/-- Helper for Theorem 21.2: convert a bridge of the form
`(fun _ => 0) ∉ U → ∃ u ∈ U, Σ_j lam_j u_j < 0` into the contradiction callback
`support_nonneg_on_U → ((fun _ => 0) ∉ U → False)`. -/
lemma helperForTheorem_21_2_supportNonneg_zeroNotMemU_contradiction_of_negative_support_witness_bridge
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hzeroNotMemU_to_existsNegativeSupportWitness :
      ((fun _ : Fin l => (0 : ℝ)) ∉ U) →
        ∃ u : Fin l → ℝ, u ∈ U ∧ (∑ j : Fin l, lamAffineSupport j * u j) < 0) :
    (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
      ((fun _ : Fin l => (0 : ℝ)) ∉ U) → False := by
  intro hSupport_nonneg_on_U hzeroNotMemU
  -- First extract a strict negative witness from the bridge under temporary `0 ∉ U`.
  have hExistsNegativeSupportWitness :
      ∃ u : Fin l → ℝ, u ∈ U ∧ (∑ j : Fin l, lamAffineSupport j * u j) < 0 :=
    hzeroNotMemU_to_existsNegativeSupportWitness hzeroNotMemU
  -- Then contradict support nonnegativity at that witness.
  exact
    helperForTheorem_21_2_supportNonneg_on_U_contradicts_exists_negative_support_witness
      U lamAffineSupport hSupport_nonneg_on_U hExistsNegativeSupportWitness

/-- Helper for Theorem 21.2: a bridge of the form
`(fun _ => 0) ∉ U → ∃ u ∈ U, Σ_j lam_j u_j < 0` upgrades support nonnegativity on `U`
to `(fun _ => 0) ∈ U` by contradiction. -/
lemma helperForTheorem_21_2_zeroMemU_of_supportNonneg_and_zeroNotMemU_to_exists_negative_support_witness
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (lamAffineSupport : Fin l → ℝ)
    (hzeroNotMemU_to_existsNegativeSupportWitness :
      ((fun _ : Fin l => (0 : ℝ)) ∉ U) →
        ∃ u : Fin l → ℝ, u ∈ U ∧ (∑ j : Fin l, lamAffineSupport j * u j) < 0) :
    (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
      (fun _ : Fin l => (0 : ℝ)) ∈ U := by
  intro hSupport_nonneg_on_U
  -- Route correction: avoid proving `0 ∈ U` directly; contradiction through an external
  -- `0 ∉ U → ∃ negative-support witness` bridge closes the implication deterministically.
  by_contra hzeroNotMemU
  have hExistsNegativeSupportWitness :
      ∃ u : Fin l → ℝ, u ∈ U ∧ (∑ j : Fin l, lamAffineSupport j * u j) < 0 :=
    hzeroNotMemU_to_existsNegativeSupportWitness hzeroNotMemU
  exact
    helperForTheorem_21_2_supportNonneg_on_U_contradicts_exists_negative_support_witness
      U lamAffineSupport hSupport_nonneg_on_U hExistsNegativeSupportWitness

/-- Helper for Theorem 21.2: in the all-shifted boundary-data setup, once an external
negative-witness bridge `(fun _ => 0) ∉ U → ∃ u ∈ U, Σ_j λ_j u_j < 0` is available,
support nonnegativity on `U` upgrades to `(fun _ => 0) ∈ U`. -/
lemma helperForTheorem_21_2_section20Specialization_supportNonneg_to_zeroMemU_of_negativeWitnessBridge_in_allShifted_context
    {n k l : ℕ}
    (_C : Set (Fin n → ℝ))
    (_fStrict : Fin k → (Fin n → ℝ) → EReal)
    (_fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (U : Set (Fin l → ℝ))
    (_hU_def :
      U = {u : Fin l → ℝ |
        ∃ x, x ∈ _C ∧ (∀ i : Fin k, _fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, _fAffine j x ≤ u j)})
    (_hFeasRi : ∃ x, x ∈ euclideanRelativeInterior_fin n _C ∧ ∀ j : Fin l, _fAffine j x ≤ 0)
    (_hAllShiftedPrimal :
      ∀ ε : ℝ, 0 < ε →
        ∃ x, x ∈ _C ∧ (∀ i : Fin k, _fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, _fAffine j x < ε))
    (_hNotPrimal :
      ¬ (∃ x, x ∈ _C ∧ (∀ i : Fin k, _fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, _fAffine j x ≤ 0)))
    (_hzeroMemClosureU : (fun _ : Fin l => (0 : ℝ)) ∈ closure U)
    (_hUconv : Convex ℝ U)
    (_hUupper : ∀ {u v : Fin l → ℝ}, u ∈ U → (∀ j : Fin l, u j ≤ v j) → v ∈ U)
    (lamAffineSupport : Fin l → ℝ)
    (_hlamAffineSupport_nonneg : ∀ j : Fin l, 0 ≤ lamAffineSupport j)
    (hzeroNotMemU_to_existsNegativeSupportWitness :
      ((fun _ : Fin l => (0 : ℝ)) ∉ U) →
        ∃ u : Fin l → ℝ, u ∈ U ∧ (∑ j : Fin l, lamAffineSupport j * u j) < 0) :
    (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffineSupport j * u j) →
      (fun _ : Fin l => (0 : ℝ)) ∈ U := by
  intro hSupport_nonneg_on_U
  -- Route correction: isolate the purely logical final step from witness-bridge to
  -- membership callback so only the dependency-level witness source remains external.
  exact
    helperForTheorem_21_2_zeroMemU_of_supportNonneg_and_zeroNotMemU_to_exists_negative_support_witness
      U lamAffineSupport hzeroNotMemU_to_existsNegativeSupportWitness hSupport_nonneg_on_U


end Section21
end Chap04
