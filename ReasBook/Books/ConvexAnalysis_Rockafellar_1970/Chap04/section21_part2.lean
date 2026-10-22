/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part1

section Chap04
section Section21

set_option linter.unnecessarySimpa false

/-- The first function in the Text 21.1.1 counterexample:
`f₁(x) = -sqrt(x)` for `x ≥ 0` and `f₁(x) = +∞` for `x < 0`. -/
noncomputable def text21_1_1_f1 (x : ℝ) : EReal :=
  if 0 ≤ x then ((-Real.sqrt x : ℝ) : EReal) else (⊤ : EReal)

/-- The second function in the Text 21.1.1 counterexample: `f₂(x) = x`. -/
def text21_1_1_f2 (x : ℝ) : EReal :=
  (x : EReal)

/-- Helper for Text 21.1.1: the epigraph of `x ↦ text21_1_1_f1 x` is convex. -/
lemma helperForText_21_1_1_f1_isERealConvexFunction :
    IsERealConvexFunction 1 (fun p : Fin 1 → ℝ => text21_1_1_f1 (p 0)) := by
  -- Reduce the `EReal` epigraph constraint to a real inequality on `-sqrt` over `Ici 0`.
  change Convex ℝ {p : (Fin 1 → ℝ) × ℝ | text21_1_1_f1 (p.1 0) ≤ (p.2 : EReal)}
  have hconvSqrt : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => -Real.sqrt x) := by
    exact Real.strictConcaveOn_sqrt.concaveOn.neg
  intro x hx y hy a b ha hb hab
  have hx0 : 0 ≤ x.1 0 := by
    by_contra hx0neg
    have hxlt : x.1 0 < 0 := lt_of_not_ge hx0neg
    have : False := by
      simpa [text21_1_1_f1, hxlt.not_ge] using hx
    exact this
  have hy0 : 0 ≤ y.1 0 := by
    by_contra hy0neg
    have hylt : y.1 0 < 0 := lt_of_not_ge hy0neg
    have : False := by
      simpa [text21_1_1_f1, hylt.not_ge] using hy
    exact this
  have hxt : -Real.sqrt (x.1 0) ≤ x.2 := by
    have hxE : (((-Real.sqrt (x.1 0) : ℝ) : EReal) ≤ (x.2 : EReal)) := by
      simpa [text21_1_1_f1, hx0] using hx
    exact (EReal.coe_le_coe_iff).1 hxE
  have hyt : -Real.sqrt (y.1 0) ≤ y.2 := by
    have hyE : (((-Real.sqrt (y.1 0) : ℝ) : EReal) ≤ (y.2 : EReal)) := by
      simpa [text21_1_1_f1, hy0] using hy
    exact (EReal.coe_le_coe_iff).1 hyE
  have hcoord0 : ((a • x + b • y).1 0) = a * x.1 0 + b * y.1 0 := by
    simp [smul_eq_mul]
  have hz0' : 0 ≤ a * x.1 0 + b * y.1 0 := by
    nlinarith
  -- Apply Jensen's inequality for the convex function `-sqrt` on nonnegative inputs.
  have hsqrt0 :
      -Real.sqrt (a * x.1 0 + b * y.1 0)
        ≤ a * (-Real.sqrt (x.1 0)) + b * (-Real.sqrt (y.1 0)) := by
    have hsqrt' := hconvSqrt.2 hx0 hy0 ha hb hab
    simpa [smul_eq_mul] using hsqrt'
  have hweighted :
      a * (-Real.sqrt (x.1 0)) + b * (-Real.sqrt (y.1 0)) ≤ a * x.2 + b * y.2 := by
    have hax : a * (-Real.sqrt (x.1 0)) ≤ a * x.2 := by
      exact mul_le_mul_of_nonneg_left hxt ha
    have hby : b * (-Real.sqrt (y.1 0)) ≤ b * y.2 := by
      exact mul_le_mul_of_nonneg_left hyt hb
    linarith
  have hzE :
      (((-Real.sqrt (a * x.1 0 + b * y.1 0) : ℝ) : EReal) ≤ ((a * x.2 + b * y.2 : ℝ) : EReal)) :=
    (EReal.coe_le_coe_iff).2 (le_trans hsqrt0 hweighted)
  simpa [text21_1_1_f1, hcoord0, hz0', smul_eq_mul] using hzE

/-- Helper for Text 21.1.1: the epigraph of `x ↦ text21_1_1_f2 x = x` is convex. -/
lemma helperForText_21_1_1_f2_isERealConvexFunction :
    IsERealConvexFunction 1 (fun p : Fin 1 → ℝ => text21_1_1_f2 (p 0)) := by
  -- The defining inequality is linear in the `ℝ × ℝ` coordinates.
  change Convex ℝ {p : (Fin 1 → ℝ) × ℝ | ((p.1 0 : ℝ) : EReal) ≤ (p.2 : EReal)}
  intro x hx y hy a b ha hb hab
  have hxR : x.1 0 ≤ x.2 := (EReal.coe_le_coe_iff).1 hx
  have hyR : y.1 0 ≤ y.2 := (EReal.coe_le_coe_iff).1 hy
  have hax : a * x.1 0 ≤ a * x.2 := mul_le_mul_of_nonneg_left hxR ha
  have hby : b * y.1 0 ≤ b * y.2 := mul_le_mul_of_nonneg_left hyR hb
  have hsum : a * x.1 0 + b * y.1 0 ≤ a * x.2 + b * y.2 := by
    linarith
  simpa [text21_1_1_f2, smul_eq_mul] using hsum

/-- Helper for Text 21.1.1: a global nonnegativity inequality with nonnegative multipliers
forces `lam1 = 0`. -/
lemma helperForText_21_1_1_globalIneq_forces_lam1_zero
    (lam1 lam2 : ℝ)
    (hlam1 : 0 ≤ lam1) (hlam2 : 0 ≤ lam2)
    (hglobal : ∀ x : ℝ,
      (0 : EReal) ≤ ((lam1 : EReal) * text21_1_1_f1 x + (lam2 : EReal) * text21_1_1_f2 x)) :
    lam1 = 0 := by
  -- Evaluate the global inequality at a test point tuned to `lam1` and `lam2`.
  by_contra hlam1ne
  have hlam1pos : 0 < lam1 := lt_of_le_of_ne hlam1 (Ne.symm hlam1ne)
  let r : ℝ := lam1 / (lam2 + 1)
  let x0 : ℝ := r ^ 2
  have hx0 : 0 ≤ x0 := by
    dsimp [x0]
    positivity
  have hlam2Plus1_pos : 0 < lam2 + 1 := by
    linarith
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact div_nonneg hlam1 (le_of_lt hlam2Plus1_pos)
  have hsqrt_x0 : Real.sqrt x0 = r := by
    calc
      Real.sqrt x0 = Real.sqrt (r ^ 2) := by rfl
      _ = |r| := Real.sqrt_sq_eq_abs r
      _ = r := abs_of_nonneg hr_nonneg
  have hAtx0 := hglobal x0
  have hAtx0Real : 0 ≤ lam1 * (-Real.sqrt x0) + lam2 * x0 := by
    have hAtx0EReal :
        ((0 : ℝ) : EReal) ≤
          ((lam1 * (-Real.sqrt x0) + lam2 * x0 : ℝ) : EReal) := by
      simpa [text21_1_1_f1, text21_1_1_f2, hx0, EReal.coe_mul, EReal.coe_add,
        mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using hAtx0
    exact (EReal.coe_le_coe_iff).1 hAtx0EReal
  -- Compute the test-point expression explicitly; it is strictly negative if `lam1 > 0`.
  have hExpr : lam1 * (-Real.sqrt x0) + lam2 * x0 = -(lam1 ^ 2 / (lam2 + 1) ^ 2) := by
    rw [hsqrt_x0]
    dsimp [x0, r]
    have hden_ne : lam2 + 1 ≠ 0 := by
      linarith
    field_simp [hden_ne]
    ring
  have hNeg : lam1 * (-Real.sqrt x0) + lam2 * x0 < 0 := by
    rw [hExpr]
    have hNumPos : 0 < lam1 ^ 2 := by
      nlinarith
    have hDenPos : 0 < (lam2 + 1) ^ 2 := by
      nlinarith [hlam2Plus1_pos]
    have hFracPos : 0 < lam1 ^ 2 / (lam2 + 1) ^ 2 := div_pos hNumPos hDenPos
    nlinarith
  exact (not_lt_of_ge hAtx0Real) hNeg

/-- Helper for Text 21.1.1: when `lam1 = 0`, global nonnegativity forces `lam2 = 0`. -/
lemma helperForText_21_1_1_globalIneq_lam1_zero_forces_lam2_zero
    (lam2 : ℝ)
    (hlam2 : 0 ≤ lam2)
    (hglobal : ∀ x : ℝ,
      (0 : EReal) ≤ ((0 : EReal) * text21_1_1_f1 x + (lam2 : EReal) * text21_1_1_f2 x)) :
    lam2 = 0 := by
  -- Evaluate at a negative point to force `0 ≤ -lam2`.
  have hAtNegOne := hglobal (-1)
  have hReal : 0 ≤ -lam2 := by
    have hE : ((0 : ℝ) : EReal) ≤ ((-lam2 : ℝ) : EReal) := by
      simpa [text21_1_1_f1, text21_1_1_f2, EReal.coe_mul, EReal.coe_add] using hAtNegOne
    exact (EReal.coe_le_coe_iff).1 hE
  linarith

/-- Helper for Text 21.1.1: zero multipliers satisfy the global inequality trivially. -/
lemma helperForText_21_1_1_zeroMultipliers_give_globalIneq :
    ∀ x : ℝ, (0 : EReal) ≤ ((0 : EReal) * text21_1_1_f1 x + (0 : EReal) * text21_1_1_f2 x) := by
  -- Every term vanishes when both multipliers are zero.
  intro x
  simp [text21_1_1_f2]

/-- Helper for Text 21.1.1: there is no point where both inequalities are strict. -/
lemma helperForText_21_1_1_no_strict_common_point :
    ¬ ∃ x : ℝ, text21_1_1_f1 x < (0 : EReal) ∧ text21_1_1_f2 x < (0 : EReal) := by
  rintro ⟨x, hx1, hx2⟩
  -- Convert `f₂(x) < 0` into the real inequality `x < 0`.
  have hxlt : x < 0 := by
    have hx2' : ((x : ℝ) : EReal) < ((0 : ℝ) : EReal) := by
      simpa [text21_1_1_f2] using hx2
    exact (EReal.coe_lt_coe_iff).1 hx2'
  -- On negative inputs, `f₁` is by definition `⊤`, contradicting `f₁(x) < 0`.
  have hxTop : text21_1_1_f1 x = (⊤ : EReal) := by
    have hx_not_ge : ¬ 0 ≤ x := not_le.mpr hxlt
    simp [text21_1_1_f1, hx_not_ge]
  have hTopLt : (⊤ : EReal) < (0 : EReal) := by
    simpa [hxTop] using hx1
  exact (not_top_lt hTopLt)

/-- Helper for Text 21.1.1: under nonnegative multipliers, the global inequality
holds for all `x` iff both multipliers vanish. -/
lemma helperForText_21_1_1_globalIneq_iff_zeroMultipliers
    (lam1 lam2 : ℝ)
    (hlam1 : 0 ≤ lam1) (hlam2 : 0 ≤ lam2) :
    ((∀ x : ℝ,
        (0 : EReal) ≤
          ((lam1 : EReal) * text21_1_1_f1 x + (lam2 : EReal) * text21_1_1_f2 x)) ↔
      (lam1 = 0 ∧ lam2 = 0)) := by
  constructor
  · intro hglobal
    -- First force `lam1 = 0` from the global inequality.
    have hlam1zero :
        lam1 = 0 :=
      helperForText_21_1_1_globalIneq_forces_lam1_zero lam1 lam2 hlam1 hlam2 hglobal
    -- Then specialize to the `lam1 = 0` case and force `lam2 = 0`.
    have hglobal0 : ∀ x : ℝ,
        (0 : EReal) ≤ ((0 : EReal) * text21_1_1_f1 x + (lam2 : EReal) * text21_1_1_f2 x) := by
      intro x
      simpa [hlam1zero] using hglobal x
    have hlam2zero :
        lam2 = 0 :=
      helperForText_21_1_1_globalIneq_lam1_zero_forces_lam2_zero lam2 hlam2 hglobal0
    exact ⟨hlam1zero, hlam2zero⟩
  · rintro ⟨hlam1zero, hlam2zero⟩
    -- Conversely, zero multipliers reduce to the trivial nonnegativity identity.
    intro x
    simpa [hlam1zero, hlam2zero] using
      helperForText_21_1_1_zeroMultipliers_give_globalIneq x

/-- Helper for Text 21.1.1: the condition `ri C ⊆ dom f₁` fails when `C = ℝ`. -/
lemma helperForText_21_1_1_ri_univ_not_subset_dom_f1 :
    ¬ ((Set.univ : Set ℝ) ⊆ {x : ℝ | text21_1_1_f1 x < (⊤ : EReal)}) := by
  intro hsubset
  -- Use the negative witness `x = -1`, which lies in `ri C = univ`.
  have hNegOneMemUniv : (-1 : ℝ) ∈ (Set.univ : Set ℝ) := by
    simp
  have hAtNegOne : text21_1_1_f1 (-1 : ℝ) < (⊤ : EReal) := by
    exact hsubset hNegOneMemUniv
  -- But for negative inputs, `f₁` is exactly `⊤`.
  have hNegOneTop : text21_1_1_f1 (-1 : ℝ) = (⊤ : EReal) := by
    have hnot : ¬ 0 ≤ (-1 : ℝ) := by norm_num
    simp [text21_1_1_f1, hnot]
  have hlt : (⊤ : EReal) < (⊤ : EReal) := by
    simpa [hNegOneTop] using hAtNegOne
  exact (lt_irrefl (⊤ : EReal)) hlt

-- Proof sketch: (1) `f₂(x) < 0` forces `x < 0`, while `f₁(x) < 0` forces `x ≥ 0`,
-- so no `x` can satisfy both inequalities; (2) the global inequality for all `x`
-- implies `lam1 = lam2 = 0` by testing suitable positive/negative values; and
-- (3) `ri ℝ = ℝ`, but negative points are excluded from `dom f₁`, so the `ri`-domain
-- condition fails.
/-- Text 21.1.1: With `C = ℝ`, define
`f₁(x) = -sqrt(x)` for `x ≥ 0` and `f₁(x) = +∞` for `x < 0`, and `f₂(x) = x`.
Then there is no `x ∈ C` such that `f₁(x) < 0` and `f₂(x) < 0`; the only
nonnegative multipliers `lam1, lam2` satisfying
`lam1 * f₁(x) + lam2 * f₂(x) ≥ 0` for all `x ∈ C` are `lam1 = lam2 = 0`;
moreover, `ri C ⊆ dom f₁` fails. -/
theorem Text_21_1_1_multiplier_counterexample :
    IsERealConvexFunction 1 (fun p : Fin 1 → ℝ => text21_1_1_f1 (p 0)) ∧
      IsERealConvexFunction 1 (fun p : Fin 1 → ℝ => text21_1_1_f2 (p 0)) ∧
      (¬ ∃ x : ℝ, text21_1_1_f1 x < (0 : EReal) ∧ text21_1_1_f2 x < (0 : EReal)) ∧
      (∀ lam1 lam2 : ℝ,
        0 ≤ lam1 →
          0 ≤ lam2 →
            ((∀ x : ℝ,
                (0 : EReal) ≤
                  ((lam1 : EReal) * text21_1_1_f1 x + (lam2 : EReal) * text21_1_1_f2 x)) ↔
              (lam1 = 0 ∧ lam2 = 0))) ∧
      ¬ ((Set.univ : Set ℝ) ⊆ {x : ℝ | text21_1_1_f1 x < (⊤ : EReal)}) := by
  constructor
  · -- First conjunct: convexity of `f₁`.
    exact helperForText_21_1_1_f1_isERealConvexFunction
  constructor
  · -- Second conjunct: convexity of `f₂`.
    exact helperForText_21_1_1_f2_isERealConvexFunction
  constructor
  · -- Third conjunct: strict inequalities cannot hold simultaneously.
    exact helperForText_21_1_1_no_strict_common_point
  constructor
  · -- Fourth conjunct: package existing multiplier lemmas as an iff.
    intro lam1 lam2 hlam1 hlam2
    exact helperForText_21_1_1_globalIneq_iff_zeroMultipliers lam1 lam2 hlam1 hlam2
  · -- Final conjunct: `ri C ⊆ dom f₁` fails via the witness `x = -1`.
    exact helperForText_21_1_1_ri_univ_not_subset_dom_f1

-- Proof sketch: encode the weak affine constraints as part of the feasible region in
-- `ri C`, then apply the convex-alternative/separation argument from Theorem 21.1 to the
-- strict block together with these affine inequalities and read off the exclusive cases.
/-- Helper for Theorem 21.2: when `k + l = 0`, the `ri`-feasible affine witness
already gives the primal alternative on `C`. -/
lemma helperForTheorem_21_2_primal_of_no_indices {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hFeasRi : ∃ x, x ∈ euclideanRelativeInterior_fin n C ∧ ∀ j : Fin l, fAffine j x ≤ 0)
    (hkl : k + l = 0) :
    ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ 0) := by
  -- Reduce to the `k = 0`, `l = 0` branch and unpack the `ri` feasible point.
  rcases Nat.add_eq_zero_iff.mp hkl with ⟨hk0, hl0⟩
  subst k
  subst l
  rcases hFeasRi with ⟨x, hxri, hxaff⟩
  refine ⟨x, helperForTheorem_21_1_riFin_subset_C C hxri, ?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · exact hxaff

/-- Helper for Theorem 21.2: primal and dual alternatives cannot hold simultaneously. -/
lemma helperForTheorem_21_2_primal_dual_mutual_exclusion {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hPrimal :
      ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ 0))
    (hDual :
      ∃ lamStrict : Fin k → ℝ, ∃ lamAffine : Fin l → ℝ,
        (∀ i : Fin k, 0 ≤ lamStrict i) ∧
          (∀ j : Fin l, 0 ≤ lamAffine j) ∧
            (∃ i : Fin k, lamStrict i ≠ 0) ∧
              (∀ x, x ∈ C →
                (0 : EReal) ≤
                  (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
                    ∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal))) :
    False := by
  rcases hPrimal with ⟨x, hxC, hxStrict, hxAffine⟩
  rcases hDual with
    ⟨lamStrict, lamAffine, hlamStrict_nonneg, hlamAffine_nonneg, hstrict_nonzero, hglobal⟩
  rcases hstrict_nonzero with ⟨i0, hi0ne⟩
  have hi0pos : 0 < lamStrict i0 :=
    lt_of_le_of_ne (hlamStrict_nonneg i0) (by simpa [eq_comm] using hi0ne)
  -- Show one strict-block summand is strictly negative.
  have hterm_i0_lt :
      ((lamStrict i0 : ℝ) : EReal) * fStrict i0 x < (0 : EReal) := by
    have hfi0neg : fStrict i0 x < (0 : EReal) := hxStrict i0
    rcases (EReal.exists (p := fun z : EReal => z = fStrict i0 x)).1 (by
      exact ⟨fStrict i0 x, rfl⟩) with hbot | htop | hcoe
    · have hfi0bot : fStrict i0 x = (⊥ : EReal) := by simpa [eq_comm] using hbot
      have hmulBot : ((lamStrict i0 : ℝ) : EReal) * (⊥ : EReal) = (⊥ : EReal) := by
        simpa using (EReal.coe_mul_bot_of_pos hi0pos)
      have hmul : ((lamStrict i0 : ℝ) : EReal) * fStrict i0 x = (⊥ : EReal) := by
        simpa [hfi0bot] using hmulBot
      simp [hmul]
    · exfalso
      have hfi0top : fStrict i0 x = (⊤ : EReal) := by simpa [eq_comm] using htop
      have : ¬ ((⊤ : EReal) < (0 : EReal)) := by simp
      exact this (by simpa [hfi0top] using hfi0neg)
    · rcases hcoe with ⟨r, hr⟩
      have hrneg : r < 0 := by
        have : ((r : ℝ) : EReal) < (0 : EReal) := by simpa [hr] using hfi0neg
        exact (EReal.coe_lt_coe_iff).1 this
      have hmulR : lamStrict i0 * r < 0 := mul_neg_of_pos_of_neg hi0pos hrneg
      have hmulE : (((lamStrict i0 * r : ℝ) : EReal) < (0 : EReal)) := by
        exact_mod_cast hmulR
      simpa [hr, EReal.coe_mul] using hmulE
  let termStrict : Fin k → EReal := fun i => ((lamStrict i : ℝ) : EReal) * fStrict i x
  let termAffine : Fin l → EReal := fun j => ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)
  -- Every strict-block summand is nonpositive at the primal point.
  have htermStrict_nonpos : ∀ i : Fin k, termStrict i ≤ 0 := by
    intro i
    exact mul_nonpos_of_nonneg_of_nonpos
      (by exact_mod_cast hlamStrict_nonneg i) (hxStrict i).le
  have hstrict_erase_nonpos : Finset.sum (Finset.univ.erase i0) termStrict ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro i hi
    exact htermStrict_nonpos i
  have hstrict_sum_le_i0 : Finset.sum Finset.univ termStrict ≤ termStrict i0 := by
    have hsplit :
        termStrict i0 + Finset.sum (Finset.univ.erase i0) termStrict =
          Finset.sum Finset.univ termStrict := by
      simpa [termStrict, add_comm, add_left_comm, add_assoc] using
        (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin k))) (a := i0) (f := termStrict)
          (by simp))
    have haux :
        termStrict i0 + Finset.sum (Finset.univ.erase i0) termStrict ≤ termStrict i0 + 0 :=
      add_le_add_right hstrict_erase_nonpos (termStrict i0)
    calc
      Finset.sum Finset.univ termStrict =
          termStrict i0 + Finset.sum (Finset.univ.erase i0) termStrict := by
          exact hsplit.symm
      _ ≤ termStrict i0 + 0 := haux
      _ = termStrict i0 := by simp
  have hstrict_sum_lt_zero : Finset.sum Finset.univ termStrict < (0 : EReal) :=
    lt_of_le_of_lt hstrict_sum_le_i0 (by simpa [termStrict] using hterm_i0_lt)
  -- Every affine-block summand is nonpositive at the primal point.
  have htermAffine_nonpos : ∀ j : Fin l, termAffine j ≤ 0 := by
    intro j
    have hAffine_nonpos : ((fAffine j x : ℝ) : EReal) ≤ (0 : EReal) := by
      exact_mod_cast (hxAffine j)
    exact mul_nonpos_of_nonneg_of_nonpos
      (by exact_mod_cast hlamAffine_nonneg j) hAffine_nonpos
  have haffine_sum_nonpos : Finset.sum Finset.univ termAffine ≤ (0 : EReal) := by
    refine Finset.sum_nonpos ?_
    intro j hj
    exact htermAffine_nonpos j
  have htotal_lt_zero :
      (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
          ∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal) < (0 : EReal) := by
    have hsum_lt :
        Finset.sum Finset.univ termStrict + Finset.sum Finset.univ termAffine < (0 : EReal) := by
      let strictSum : EReal := Finset.sum Finset.univ termStrict
      let affineSum : EReal := Finset.sum Finset.univ termAffine
      have hsum_le_strict :
          strictSum + affineSum ≤ strictSum := by
        have haux : strictSum + affineSum ≤ strictSum + (0 : EReal) := by
          exact add_le_add_right haffine_sum_nonpos strictSum
        simpa using haux
      have hstrict_sum_lt_zero' : strictSum < (0 : EReal) := by
        simpa [strictSum] using hstrict_sum_lt_zero
      have hsum_lt' : strictSum + affineSum < (0 : EReal) :=
        lt_of_le_of_lt hsum_le_strict hstrict_sum_lt_zero'
      simpa [strictSum, affineSum] using hsum_lt'
    simpa [termStrict, termAffine] using hsum_lt
  -- Contradict the dual global nonnegativity inequality at the primal witness.
  exact (not_lt_of_ge (hglobal x hxC)) htotal_lt_zero

/-- Helper for Theorem 21.2: every shifted affine inequality
`x ↦ fAffine x - ε` (coerced to `EReal`) is proper convex on `Set.univ`. -/
lemma helperForTheorem_21_2_shifted_affine_properConvex {n : ℕ}
    (g : (Fin n → ℝ) →ᵃ[ℝ] ℝ) (ε : ℝ) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => ((g x - ε : ℝ) : EReal)) := by
  -- Reduce `EReal` convexity to real convexity of the affine map minus a constant.
  have hconvOnReal : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) (fun x => g x - ε) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    have hdecomp := AffineMap.decomp g
    have hgx : g x = g.linear x + g 0 := by
      simpa [Pi.add_apply] using congrArg (fun h => h x) hdecomp
    have hgy : g y = g.linear y + g 0 := by
      simpa [Pi.add_apply] using congrArg (fun h => h y) hdecomp
    have hgxy : g (a • x + b • y) = g.linear (a • x + b • y) + g 0 := by
      simpa [Pi.add_apply] using congrArg (fun h => h (a • x + b • y)) hdecomp
    have hlin :
        g (a • x + b • y) - ε = a * (g x - ε) + b * (g y - ε) := by
      rw [hgxy, g.linear.map_add, g.linear.map_smul, g.linear.map_smul, hgx, hgy]
      have hab' : b = 1 - a := by linarith
      rw [hab']
      simp [smul_eq_mul]
      ring_nf
    exact le_of_eq hlin
  have hconvEon :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ((g x - ε : ℝ) : EReal)) :=
    convexFunctionOn_of_convexOn_real (S := Set.univ) (g := fun x => g x - ε) hconvOnReal
  refine ⟨hconvEon, ?_, ?_⟩
  · refine ⟨((0 : Fin n → ℝ), g 0 - ε), ?_⟩
    have hxUniv : (0 : Fin n → ℝ) ∈ (Set.univ : Set (Fin n → ℝ)) := trivial
    have hvalue : (((g 0 - ε : ℝ) : EReal) ≤ ((g 0 - ε : ℝ) : EReal)) := le_rfl
    exact ⟨hxUniv, hvalue⟩
  · intro x hx
    exact EReal.coe_ne_bot (g x - ε)

/-- Helper for Theorem 21.2: for each `ε`, apply Theorem 21.1 to the appended shifted family
`Fin.append fStrict (fun j x => ((fAffine j x - ε : ℝ) : EReal))` and split the result into the
shifted-primal / shifted-dual alternatives. -/
lemma helperForTheorem_21_2_shifted_appended_alternative {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (hklPos : 0 < k + l)
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (hfStrict : ∀ i : Fin k,
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStrict i))
    (hdomStrict :
      ∀ i : Fin k,
        euclideanRelativeInterior_fin n C ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fStrict i))
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hAffine : ∀ j : Fin l, ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, fAffine j = g)
    (ε : ℝ) :
    Xor'
      (∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x < ε))
      (∃ lamStrict : Fin k → ℝ, ∃ lamAffine : Fin l → ℝ,
        (∀ i : Fin k, 0 ≤ lamStrict i) ∧
          (∀ j : Fin l, 0 ≤ lamAffine j) ∧
            ((∃ i : Fin k, lamStrict i ≠ 0) ∨ (∃ j : Fin l, lamAffine j ≠ 0)) ∧
              (∀ x, x ∈ C →
                (0 : EReal) ≤
                  (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
                    ∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * (((fAffine j x - ε : ℝ) : EReal)))) := by
  let fShift : Fin (k + l) → (Fin n → ℝ) → EReal :=
    Fin.append fStrict (fun j x => ((fAffine j x - ε : ℝ) : EReal))
  -- Build proper convexity for each appended component.
  have hfShift :
      ∀ q : Fin (k + l),
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fShift q) := by
    intro q
    refine Fin.addCases ?_ ?_ q
    · intro i
      simpa [fShift] using hfStrict i
    · intro j
      rcases hAffine j with ⟨g, hg⟩
      simpa [fShift, hg] using helperForTheorem_21_2_shifted_affine_properConvex (n := n) g ε
  -- Build `ri C ⊆ dom` for each appended component.
  have hdomShift :
      ∀ q : Fin (k + l),
        euclideanRelativeInterior_fin n C ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fShift q) := by
    intro q
    refine Fin.addCases ?_ ?_ q
    · intro i
      simpa [fShift] using hdomStrict i
    · intro j x hxri
      refine ⟨fAffine j x - ε, ?_⟩
      have hxUniv : x ∈ (Set.univ : Set (Fin n → ℝ)) := trivial
      have hle : fShift (Fin.natAdd k j) x ≤ ((fAffine j x - ε : ℝ) : EReal) := by
        simp [fShift]
      exact ⟨hxUniv, hle⟩
  have hAlt :=
    theorem21_convex_inequality_alternative C hC hklPos fShift hfShift hdomShift
  -- Rewrite `Xor'` and translate both branches to strict/affine coordinates.
  rw [xor_def] at hAlt ⊢
  rcases hAlt with hAlt | hAlt
  · left
    rcases hAlt with ⟨hxShift, hxNoDual⟩
    refine ⟨?_, ?_⟩
    · rcases hxShift with ⟨x, hxC, hxShiftAll⟩
      refine ⟨x, hxC, ?_, ?_⟩
      · intro i
        simpa [fShift] using hxShiftAll (Fin.castAdd l i)
      · intro j
        have hshift : ((fAffine j x - ε : ℝ) : EReal) < (0 : EReal) := by
          simpa [fShift] using hxShiftAll (Fin.natAdd k j)
        have hreal : fAffine j x - ε < 0 := (EReal.coe_lt_coe_iff).1 hshift
        linarith
    · intro hDual
      apply hxNoDual
      rcases hDual with ⟨lamStrict, lamAffine, hlamStrict, hlamAffine, hnontriv, hglobal⟩
      refine ⟨Fin.append lamStrict lamAffine, ?_, ?_, ?_⟩
      · intro q
        refine Fin.addCases ?_ ?_ q
        · intro i
          simpa using hlamStrict i
        · intro j
          simpa using hlamAffine j
      · by_contra hzero
        have hstrictZero : ∀ i : Fin k, lamStrict i = 0 := by
          intro i
          by_contra hi
          have hcastNe : Fin.append lamStrict lamAffine (Fin.castAdd l i) ≠ 0 := by
            simpa using hi
          have hcastEx : ∃ q : Fin (k + l), Fin.append lamStrict lamAffine q ≠ 0 :=
            ⟨Fin.castAdd l i, hcastNe⟩
          exact hzero hcastEx
        have haffineZero : ∀ j : Fin l, lamAffine j = 0 := by
          intro j
          by_contra hj
          have hnatNe : Fin.append lamStrict lamAffine (Fin.natAdd k j) ≠ 0 := by
            simpa using hj
          have hnatEx : ∃ q : Fin (k + l), Fin.append lamStrict lamAffine q ≠ 0 :=
            ⟨Fin.natAdd k j, hnatNe⟩
          exact hzero hnatEx
        rcases hnontriv with hstrictNonzero | haffineNonzero
        · rcases hstrictNonzero with ⟨i, hi⟩
          exact hi (hstrictZero i)
        · rcases haffineNonzero with ⟨j, hj⟩
          exact hj (haffineZero j)
      · intro x hxC
        simpa [fShift, Fin.sum_univ_add] using hglobal x hxC
  · right
    rcases hAlt with ⟨hDualShift, hNoShift⟩
    refine ⟨?_, ?_⟩
    · rcases hDualShift with ⟨w, hw_nonneg, hw_nontriv, hglobal⟩
      refine ⟨(fun i => w (Fin.castAdd l i)), (fun j => w (Fin.natAdd k j)), ?_, ?_, ?_, ?_⟩
      · intro i
        exact hw_nonneg (Fin.castAdd l i)
      · intro j
        exact hw_nonneg (Fin.natAdd k j)
      · by_contra hnone
        have hstrictZero : ∀ i : Fin k, w (Fin.castAdd l i) = 0 := by
          intro i
          by_contra hi
          exact hnone (Or.inl ⟨i, hi⟩)
        have haffineZero : ∀ j : Fin l, w (Fin.natAdd k j) = 0 := by
          intro j
          by_contra hj
          exact hnone (Or.inr ⟨j, hj⟩)
        have hallZero : ∀ q : Fin (k + l), w q = 0 :=
          (Fin.forall_fin_add (P := fun q : Fin (k + l) => w q = 0)).2
            ⟨hstrictZero, haffineZero⟩
        rcases hw_nontriv with ⟨q, hq⟩
        exact hq (hallZero q)
      · intro x hxC
        simpa [Fin.sum_univ_add, fShift] using hglobal x hxC
    · intro hx
      apply hNoShift
      rcases hx with ⟨x, hxC, hxStrict, hxAffine⟩
      refine ⟨x, hxC, ?_⟩
      intro q
      refine Fin.addCases ?_ ?_ q
      · intro i
        simpa [fShift] using hxStrict i
      · intro j
        have hreal : fAffine j x < ε := hxAffine j
        have hE : (((fAffine j x - ε : ℝ) : EReal) < (0 : EReal)) := by
          exact_mod_cast (sub_lt_zero.mpr hreal)
        simpa [fShift] using hE

/-- Helper for Theorem 21.2: a shifted dual certificate at some `ε > 0` yields a target dual
certificate, and the strict block must be nontrivial by testing at the `ri` affine-feasible point. -/
lemma helperForTheorem_21_2_shifted_dual_to_target_dual_with_strict_nonzero {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hFeasRi : ∃ x, x ∈ euclideanRelativeInterior_fin n C ∧ ∀ j : Fin l, fAffine j x ≤ 0)
    (ε : ℝ) (hε : 0 < ε)
    (hShiftedDual :
      ∃ lamStrict : Fin k → ℝ, ∃ lamAffine : Fin l → ℝ,
        (∀ i : Fin k, 0 ≤ lamStrict i) ∧
          (∀ j : Fin l, 0 ≤ lamAffine j) ∧
            ((∃ i : Fin k, lamStrict i ≠ 0) ∨ (∃ j : Fin l, lamAffine j ≠ 0)) ∧
              (∀ x, x ∈ C →
                (0 : EReal) ≤
                  (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
                    ∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * (((fAffine j x - ε : ℝ) : EReal)))) :
    ∃ lamStrict : Fin k → ℝ, ∃ lamAffine : Fin l → ℝ,
      (∀ i : Fin k, 0 ≤ lamStrict i) ∧
        (∀ j : Fin l, 0 ≤ lamAffine j) ∧
          (∃ i : Fin k, lamStrict i ≠ 0) ∧
            (∀ x, x ∈ C →
              (0 : EReal) ≤
                (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x) +
                  ∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) := by
  rcases hShiftedDual with
    ⟨lamStrict, lamAffine, hlamStrict_nonneg, hlamAffine_nonneg, hnontriv, hglobalShifted⟩
  -- Exclude the degenerate case `lamStrict = 0` by evaluating the shifted inequality at
  -- the affine-feasible point from `ri C`.
  have hstrict_nonzero : ∃ i : Fin k, lamStrict i ≠ 0 := by
    by_contra hno
    have hstrictZero : ∀ i : Fin k, lamStrict i = 0 := by
      intro i
      by_contra hi
      exact hno ⟨i, hi⟩
    have haffine_nonzero : ∃ j : Fin l, lamAffine j ≠ 0 := by
      rcases hnontriv with hstrict | haffine
      · exact False.elim (hno hstrict)
      · exact haffine
    rcases hFeasRi with ⟨x0, hx0ri, hx0Affine⟩
    have hx0C : x0 ∈ C := helperForTheorem_21_1_riFin_subset_C C hx0ri
    rcases haffine_nonzero with ⟨j0, hj0ne⟩
    have hj0ne' : 0 ≠ lamAffine j0 := by
      simpa [eq_comm] using hj0ne
    have hj0pos : 0 < lamAffine j0 :=
      lt_of_le_of_ne (hlamAffine_nonneg j0) hj0ne'
    have hshift_j0_neg : fAffine j0 x0 - ε < 0 := by
      linarith [hx0Affine j0, hε]
    let termAffine : Fin l → EReal :=
      fun j => ((lamAffine j : ℝ) : EReal) * (((fAffine j x0 - ε : ℝ) : EReal))
    have hterm_j0_lt : termAffine j0 < (0 : EReal) := by
      have hmulR : lamAffine j0 * (fAffine j0 x0 - ε) < 0 :=
        mul_neg_of_pos_of_neg hj0pos hshift_j0_neg
      have hmulE : (((lamAffine j0 * (fAffine j0 x0 - ε) : ℝ) : EReal) < (0 : EReal)) := by
        exact_mod_cast hmulR
      simpa [termAffine, EReal.coe_mul] using hmulE
    have htermAffine_nonpos : ∀ j : Fin l, termAffine j ≤ 0 := by
      intro j
      have hshift_nonpos : fAffine j x0 - ε ≤ 0 := by
        linarith [hx0Affine j, hε]
      have hshift_nonposE : (((fAffine j x0 - ε : ℝ) : EReal) ≤ (0 : EReal)) := by
        exact_mod_cast hshift_nonpos
      have hlamE : (0 : EReal) ≤ ((lamAffine j : ℝ) : EReal) := by
        exact_mod_cast (hlamAffine_nonneg j)
      exact mul_nonpos_of_nonneg_of_nonpos hlamE hshift_nonposE
    have hsum_erase_nonpos : Finset.sum (Finset.univ.erase j0) termAffine ≤ 0 := by
      refine Finset.sum_nonpos ?_
      intro j hj
      exact htermAffine_nonpos j
    have hsum_le_j0 : Finset.sum Finset.univ termAffine ≤ termAffine j0 := by
      have hsplit : termAffine j0 + Finset.sum (Finset.univ.erase j0) termAffine =
          Finset.sum Finset.univ termAffine := by
        simpa [termAffine, add_comm, add_left_comm, add_assoc] using
          (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin l))) (a := j0) (f := termAffine)
            (by simp))
      have haux :
          termAffine j0 + Finset.sum (Finset.univ.erase j0) termAffine ≤ termAffine j0 + 0 :=
        add_le_add_right hsum_erase_nonpos (termAffine j0)
      calc
        Finset.sum Finset.univ termAffine =
            termAffine j0 + Finset.sum (Finset.univ.erase j0) termAffine := by
              exact hsplit.symm
        _ ≤ termAffine j0 + 0 := haux
        _ = termAffine j0 := by simp
    have haffine_sum_lt_zero : Finset.sum Finset.univ termAffine < (0 : EReal) :=
      lt_of_le_of_lt hsum_le_j0 hterm_j0_lt
    have hstrict_sum_zero :
        (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x0) = (0 : EReal) := by
      refine Finset.sum_eq_zero ?_
      intro i hi
      simp [hstrictZero i]
    have htotal_lt_zero :
        (∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x0) +
            ∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * (((fAffine j x0 - ε : ℝ) : EReal))
              < (0 : EReal) := by
      simpa [hstrict_sum_zero, termAffine] using haffine_sum_lt_zero
    exact (not_lt_of_ge (hglobalShifted x0 hx0C)) htotal_lt_zero
  -- Drop the negative shift `-ε` term to obtain the target inequality on all `x ∈ C`.
  refine ⟨lamStrict, lamAffine, hlamStrict_nonneg, hlamAffine_nonneg, hstrict_nonzero, ?_⟩
  intro x hxC
  have hshifted := hglobalShifted x hxC
  let strictSum : EReal := ∑ i : Fin k, ((lamStrict i : ℝ) : EReal) * fStrict i x
  have hsum_shifted_le_target :
      (∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * (((fAffine j x - ε : ℝ) : EReal))) ≤
        (∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) := by
    refine Finset.sum_le_sum ?_
    intro j hj
    have hbase : (((fAffine j x - ε : ℝ) : EReal) ≤ ((fAffine j x : ℝ) : EReal)) := by
      exact_mod_cast (sub_le_self (fAffine j x) (le_of_lt hε))
    have hlamE : (0 : EReal) ≤ ((lamAffine j : ℝ) : EReal) := by
      exact_mod_cast (hlamAffine_nonneg j)
    exact mul_le_mul_of_nonneg_left hbase hlamE
  have hsum_shifted_le_target_full :
      strictSum + (∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * (((fAffine j x - ε : ℝ) : EReal)))
        ≤ strictSum + (∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hsum_shifted_le_target strictSum
  have hshifted' :
      (0 : EReal) ≤
        strictSum + (∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * (((fAffine j x - ε : ℝ) : EReal))) := by
    simpa [strictSum] using hshifted
  have htarget' :
      (0 : EReal) ≤
        strictSum + (∑ j : Fin l, ((lamAffine j : ℝ) : EReal) * ((fAffine j x : ℝ) : EReal)) :=
    le_trans hshifted' hsum_shifted_le_target_full
  simpa [strictSum] using htarget'

/-- Helper for Theorem 21.2: each positive shift yields a constant-vector point in the
strict-feasible affine upper hull. -/
lemma helperForTheorem_21_2_constant_vector_mem_strictFeasibleAffineUpperHull
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hAllShiftedPrimal :
      ∀ ε : ℝ, 0 < ε →
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x < ε)) :
    ∀ ε : ℝ, 0 < ε →
      (fun _ : Fin l => ε) ∈
        {u : Fin l → ℝ |
          ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)} := by
  intro ε hε
  -- Use the shifted-primal witness and weaken `< ε` to `≤ ε` coordinatewise.
  rcases hAllShiftedPrimal ε hε with ⟨x, hxC, hxStrict, hxAffineLt⟩
  refine ⟨x, hxC, hxStrict, ?_⟩
  intro j
  exact (hxAffineLt j).le

/-- Helper for Theorem 21.2: the origin belongs to the closure of the strict-feasible affine
upper hull generated by the positive-shift witnesses. -/
lemma helperForTheorem_21_2_zero_mem_closure_strictFeasibleAffineUpperHull
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hAllShiftedPrimal :
      ∀ ε : ℝ, 0 < ε →
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x < ε)) :
    (fun _ : Fin l => (0 : ℝ)) ∈
      closure
        {u : Fin l → ℝ |
          ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)} := by
  let U : Set (Fin l → ℝ) :=
    {u : Fin l → ℝ |
      ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)}
  let constVec : ℝ → Fin l → ℝ := fun ε _ => ε
  have hconst_mem : ∀ ε : ℝ, 0 < ε → constVec ε ∈ U := by
    intro ε hε
    -- Each shifted witness gives a constant-vector point in `U`.
    simpa [U, constVec] using
      helperForTheorem_21_2_constant_vector_mem_strictFeasibleAffineUpperHull
        C fStrict fAffine hAllShiftedPrimal ε hε
  have himage_subset : constVec '' Set.Ioi (0 : ℝ) ⊆ U := by
    intro u hu
    rcases hu with ⟨ε, hε, rfl⟩
    exact hconst_mem ε hε
  have hcontConst : Continuous constVec := by
    -- Coordinatewise continuity reduces to continuity of the identity map on `ℝ`.
    refine continuous_pi ?_
    intro i
    simpa [constVec] using (continuous_id : Continuous (fun ε : ℝ => ε))
  have hzeroClosureIoi : (0 : ℝ) ∈ closure (Set.Ioi (0 : ℝ)) := by
    simpa [closure_Ioi]
  have hzeroMemImageClosure : constVec 0 ∈ closure (constVec '' Set.Ioi (0 : ℝ)) := by
    have himageClosure :
        constVec '' closure (Set.Ioi (0 : ℝ)) ⊆ closure (constVec '' Set.Ioi (0 : ℝ)) :=
      image_closure_subset_closure_image (f := constVec) (s := Set.Ioi (0 : ℝ)) hcontConst
    exact himageClosure ⟨0, hzeroClosureIoi, rfl⟩
  have hclosureSubset : closure (constVec '' Set.Ioi (0 : ℝ)) ⊆ closure U :=
    closure_mono himage_subset
  have hzeroInClosureU : constVec 0 ∈ closure U := hclosureSubset hzeroMemImageClosure
  simpa [U, constVec] using hzeroInClosureU

/-- Helper for Theorem 21.2: the origin is not in the strict-feasible affine upper hull,
because that would realize the forbidden target-primal point. -/
lemma helperForTheorem_21_2_zero_not_mem_strictFeasibleAffineUpperHull
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hNotPrimal :
      ¬ (∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ 0))) :
    (fun _ : Fin l => (0 : ℝ)) ∉
      {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧ (∀ j : Fin l, fAffine j x ≤ u j)} := by
  intro hzeroMem
  rcases hzeroMem with ⟨x, hxC, hxStrict, hxAffineLe⟩
  -- At `u = 0`, upper-hull membership gives exactly the target primal inequalities.
  have hxAffineNonpos : ∀ j : Fin l, fAffine j x ≤ 0 := by
    intro j
    simpa using hxAffineLe j
  exact hNotPrimal ⟨x, hxC, hxStrict, hxAffineNonpos⟩

/-- Helper for Theorem 21.2: the strict-feasible affine upper hull is convex. -/
lemma helperForTheorem_21_2_convexity_of_strictFeasibleAffineUpperHull
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (hfStrict : ∀ i : Fin k,
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStrict i))
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hAffine : ∀ j : Fin l, ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, fAffine j = g) :
    Convex ℝ
      {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧
          (∀ j : Fin l, fAffine j x ≤ u j)} := by
  intro u hu v hv a b ha hb hab
  rcases hu with ⟨x, hxC, hxStrict, hxAffineLe⟩
  rcases hv with ⟨y, hyC, hyStrict, hyAffineLe⟩
  -- Push witnesses through convex combination in `C`.
  refine ⟨a • x + b • y, hC hxC hyC ha hb hab, ?_, ?_⟩
  · intro i
    -- Strict negativity is preserved by convexity of each strict block function.
    have hConvStrict : ConvexFunction (fStrict i) := by
      simpa [ConvexFunction] using (hfStrict i).1
    have hStrictSublevelConvex : Convex ℝ {z : Fin n → ℝ | fStrict i z < (0 : EReal)} :=
      (convexFunction_level_sets_convex (f := fStrict i) hConvStrict (0 : EReal)).1
    exact hStrictSublevelConvex (hxStrict i) (hyStrict i) ha hb hab
  · intro j
    -- Affine components satisfy the expected convex-combination identity.
    rcases hAffine j with ⟨g, hg⟩
    have hzEq : fAffine j (a • x + b • y) = a * fAffine j x + b * fAffine j y := by
      have hdecomp := AffineMap.decomp g
      have hgx : g x = g.linear x + g 0 := by
        simpa [Pi.add_apply] using congrArg (fun h => h x) hdecomp
      have hgy : g y = g.linear y + g 0 := by
        simpa [Pi.add_apply] using congrArg (fun h => h y) hdecomp
      have hgxy : g (a • x + b • y) = g.linear (a • x + b • y) + g 0 := by
        simpa [Pi.add_apply] using congrArg (fun h => h (a • x + b • y)) hdecomp
      calc
        fAffine j (a • x + b • y) = g (a • x + b • y) := by simp [hg]
        _ = a * g x + b * g y := by
          rw [hgxy, g.linear.map_add, g.linear.map_smul, g.linear.map_smul, hgx, hgy]
          have hab' : b = 1 - a := by linarith
          rw [hab']
          simp [smul_eq_mul]
          ring_nf
        _ = a * fAffine j x + b * fAffine j y := by simp [hg]
    have hax : a * fAffine j x ≤ a * u j := mul_le_mul_of_nonneg_left (hxAffineLe j) ha
    have hby : b * fAffine j y ≤ b * v j := mul_le_mul_of_nonneg_left (hyAffineLe j) hb
    have hsum : a * fAffine j x + b * fAffine j y ≤ a * u j + b * v j := add_le_add hax hby
    have htarget : fAffine j (a • x + b • y) ≤ a * u j + b * v j := hzEq.trans_le hsum
    simpa [Pi.add_apply, smul_eq_mul] using htarget

/-- Helper for Theorem 21.2: the strict-feasible affine upper hull is upward-closed
under coordinatewise order. -/
lemma helperForTheorem_21_2_upperClosed_strictFeasibleAffineUpperHull
    {n k l : ℕ}
    (C : Set (Fin n → ℝ))
    (fStrict : Fin k → (Fin n → ℝ) → EReal)
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    {u v : Fin l → ℝ}
    (hu :
      u ∈ {u : Fin l → ℝ |
        ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧
          (∀ j : Fin l, fAffine j x ≤ u j)})
    (huv : ∀ j : Fin l, u j ≤ v j) :
    v ∈ {u : Fin l → ℝ |
      ∃ x, x ∈ C ∧ (∀ i : Fin k, fStrict i x < (0 : EReal)) ∧
        (∀ j : Fin l, fAffine j x ≤ u j)} := by
  rcases hu with ⟨x, hxC, hxStrict, hxLeU⟩
  -- Keep the same `x` witness and weaken bounds with `u ≤ v`.
  refine ⟨x, hxC, hxStrict, ?_⟩
  intro j
  exact le_trans (hxLeU j) (huv j)

/-- Helper for Theorem 21.2: from boundary geometry of an upward-closed convex set
`U`, extract a nonnegative nontrivial support normal giving `0 ≤ ⟪lamAffine, u⟫` on `U`. -/
lemma helperForTheorem_21_2_boundary_support_normal_on_strictFeasibleAffineUpperHull
    {l : ℕ}
    (U : Set (Fin l → ℝ))
    (hUconv : Convex ℝ U)
    (hUupper : ∀ {u v : Fin l → ℝ}, u ∈ U → (∀ j : Fin l, u j ≤ v j) → v ∈ U)
    (hUne : U.Nonempty)
    (hzeroMemClosureU : (fun _ : Fin l => (0 : ℝ)) ∈ closure U)
    (hzeroNotMemU : (fun _ : Fin l => (0 : ℝ)) ∉ U) :
    ∃ lamAffine : Fin l → ℝ,
      (∀ j : Fin l, 0 ≤ lamAffine j) ∧
        lamAffine ≠ 0 ∧
          (∀ u : Fin l → ℝ, u ∈ U → 0 ≤ ∑ j : Fin l, lamAffine j * u j) := by
  -- Route correction: separate `U` from the negative orthant, then orient the separator.
  have _hBoundary : (fun _ : Fin l => (0 : ℝ)) ∈ closure U \ U := ⟨hzeroMemClosureU, hzeroNotMemU⟩
  let O : Set (Fin l → ℝ) := {o : Fin l → ℝ | ∀ j : Fin l, o j < 0}
  have hO_nonempty_convex : O.Nonempty ∧ Convex ℝ O := by
    simpa [O] using helperForTheorem_21_1_negativeOrthant_nonempty_convex l
  have hUO_disjoint : Disjoint U O := by
    refine Set.disjoint_left.2 ?_
    intro u huU huO
    -- If `u ∈ U` lies in the negative orthant, upward-closedness forces `0 ∈ U`, contradiction.
    have huLeZero : ∀ j : Fin l, u j ≤ 0 := by
      intro j
      exact (huO j).le
    have hzeroMemU : (fun _ : Fin l => (0 : ℝ)) ∈ U := hUupper huU huLeZero
    exact hzeroNotMemU hzeroMemU
  have hUO_disjoint_intrinsic :
      Disjoint (intrinsicInterior ℝ U) (intrinsicInterior ℝ O) := by
    exact hUO_disjoint.mono intrinsicInterior_subset intrinsicInterior_subset
  have hsepExists : ∃ H : Set (Fin l → ℝ), HyperplaneSeparatesProperly l H U O := by
    exact (exists_hyperplaneSeparatesProperly_iff_disjoint_intrinsicInterior
      (n := l) (C₁ := U) (C₂ := O)
      hUne hO_nonempty_convex.1 hUconv hO_nonempty_convex.2).2 hUO_disjoint_intrinsic
  rcases hsepExists with ⟨H, hHsep⟩
  rcases hyperplaneSeparatesProperly_oriented l H U O hHsep with
    ⟨b, β, hb_ne_zero, _hHdef, hU_lower, hO_upper, _hNotBothInH⟩
  -- Reuse Theorem 21.1 separator lemmas to get coordinatewise nonnegativity and `β ≥ 0`.
  have hb_nonneg : ∀ j : Fin l, 0 ≤ b j :=
    helperForTheorem_21_1_separatorNormal_nonneg_on_negativeOrthant O rfl b β hO_upper
  have hβ_nonneg : 0 ≤ β :=
    helperForTheorem_21_1_separatorBeta_nonneg_on_negativeOrthant O rfl b β hO_upper hb_ne_zero
      hb_nonneg
  refine ⟨b, hb_nonneg, hb_ne_zero, ?_⟩
  intro u huU
  have hβ_le : β ≤ u ⬝ᵥ b := hU_lower u huU
  have hdot_nonneg : 0 ≤ u ⬝ᵥ b := le_trans hβ_nonneg hβ_le
  simpa [dotProduct, mul_comm, mul_left_comm, mul_assoc] using hdot_nonneg

/-- Helper for Theorem 21.2: build the support-weighted affine combination and package it
as a proper convex `EReal` function with `ri C` in its effective domain. -/
lemma helperForTheorem_21_2_supportWeightedAffine_properConvex_and_dom
    {n l : ℕ}
    (C : Set (Fin n → ℝ))
    (fAffine : Fin l → (Fin n → ℝ) → ℝ)
    (hAffine : ∀ j : Fin l, ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, fAffine j = g)
    (lamAffineSupport : Fin l → ℝ) :
    ∃ gSupport : (Fin n → ℝ) →ᵃ[ℝ] ℝ,
      (∀ x : Fin n → ℝ, gSupport x = ∑ j : Fin l, lamAffineSupport j * fAffine j x) ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
          (fun x => ((gSupport x : ℝ) : EReal)) ∧
          (euclideanRelativeInterior_fin n C ⊆
            effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fun x => ((gSupport x : ℝ) : EReal))) := by
  let gAffine : Fin l → (Fin n → ℝ) →ᵃ[ℝ] ℝ := fun j => Classical.choose (hAffine j)
  let gSupport : (Fin n → ℝ) →ᵃ[ℝ] ℝ := ∑ j : Fin l, lamAffineSupport j • gAffine j
  have hgAffine : ∀ j : Fin l, fAffine j = gAffine j := by
    intro j
    exact Classical.choose_spec (hAffine j)
  have hgSupport_eval :
      ∀ x : Fin n → ℝ, gSupport x = ∑ j : Fin l, lamAffineSupport j * fAffine j x := by
    intro x
    -- Expand the affine sum pointwise and rewrite each component through `hAffine`.
    have hgAffine' : ∀ j : Fin l, gAffine j = fAffine j := by
      intro j
      simpa [eq_comm] using hgAffine j
    have hsum_apply :
        ∀ s : Finset (Fin l),
          (Finset.sum s (fun j : Fin l => lamAffineSupport j • gAffine j)) x =
            Finset.sum s (fun j : Fin l => lamAffineSupport j * gAffine j x) := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · simp
      · intro a s ha hs
        simp [ha, hs, smul_eq_mul, add_comm]
    have hgSupport_eval_gAffine :
        gSupport x = ∑ j : Fin l, lamAffineSupport j * gAffine j x := by
      simpa [gSupport] using hsum_apply (Finset.univ : Finset (Fin l))
    calc
      gSupport x = ∑ j : Fin l, lamAffineSupport j * gAffine j x := hgSupport_eval_gAffine
      _ = ∑ j : Fin l, lamAffineSupport j * fAffine j x := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        rw [hgAffine' j]
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => ((gSupport x : ℝ) : EReal)) := by
    -- Reuse the shifted-affine convexity helper at shift `ε = 0`.
    simpa using helperForTheorem_21_2_shifted_affine_properConvex (n := n) gSupport 0
  have hdom :
      euclideanRelativeInterior_fin n C ⊆
        effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fun x => ((gSupport x : ℝ) : EReal)) := by
    intro x hxri
    -- The weighted affine function is finite at every point in `Set.univ`.
    refine ⟨gSupport x, ?_⟩
    refine ⟨trivial, ?_⟩
    simp
  exact ⟨gSupport, hgSupport_eval, hproper, hdom⟩


end Section21
end Chap04
