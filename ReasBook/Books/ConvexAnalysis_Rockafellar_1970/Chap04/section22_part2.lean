/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section22_part1

section Chap04
section Section22

/-- Helper for Theorem 22.2: extend a sum over the first `k` indices to a full `Fin m` sum
by inserting zeros outside the first block. -/
lemma helperForTheorem_22_2_sum_firstBlock_extension
    {m k : ℕ} {γ : Type*} [AddCommMonoid γ]
    (hk_upper : k ≤ m) (w : Fin k → γ) :
    (∑ i : Fin k, w i) =
      ∑ j : Fin m, if hj : j.1 < k then w ⟨j.1, hj⟩ else 0 := by
  let g : ℕ → γ := fun j => if hj : j < k then w ⟨j, hj⟩ else 0
  have hleft : (∑ i : Fin k, w i) = (Finset.range k).sum g := by
    simpa [g] using (Fin.sum_univ_eq_sum_range g k)
  have hright :
      (∑ j : Fin m, if hj : j.1 < k then w ⟨j.1, hj⟩ else 0) = (Finset.range m).sum g := by
    simpa [g] using (Fin.sum_univ_eq_sum_range g m)
  rw [hleft, hright]
  rw [← Finset.sum_range_add_sum_Ico g hk_upper]
  have hIcoZero : (Finset.Ico k m).sum g = 0 := by
    -- Every term beyond the first block is forced to be zero by the cutoff `j < k`.
    refine Finset.sum_eq_zero ?_
    intro x hx
    have hxk : k ≤ x := (Finset.mem_Ico.mp hx).1
    simp [Nat.not_lt_of_ge hxk]
  simp [hIcoZero]

/-- Helper for Theorem 22.2: a mixed dual inequality from Theorem 21.2 yields the classical
nonnegative multiplier certificate with a nonzero coefficient in the first block. -/
lemma helperForTheorem_22_2_dualMargin_to_linearCertificate
    {m n k : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    (hk_upper : k ≤ m)
    (lamStrict : Fin k → ℝ) (lamAffine : Fin m → ℝ)
    (hlamStrictNonneg : ∀ i : Fin k, 0 ≤ lamStrict i)
    (hlamAffineNonneg : ∀ j : Fin m, 0 ≤ lamAffine j)
    (hStrictNonzero : ∃ i : Fin k, lamStrict i ≠ 0)
    (hmargin : ∀ x : Fin n → ℝ,
      (0 : EReal) ≤
        (∑ i : Fin k,
            ((lamStrict i : ℝ) : EReal) *
              ((((dotProduct (a (Fin.castLE hk_upper i)) x - α (Fin.castLE hk_upper i) : ℝ)) :
                EReal))) +
          ∑ j : Fin m,
            ((lamAffine j : ℝ) : EReal) *
              ((((if j.1 < k then 0 else dotProduct (a j) x - α j : ℝ)) : EReal))) :
    ∃ l : Fin m → ℝ,
      (∀ i : Fin m, 0 ≤ l i) ∧
        (∃ i : Fin m, i.1 < k ∧ l i ≠ 0) ∧
          (∑ i, l i • a i) = 0 ∧
            (∑ i, l i * α i) ≤ 0 := by
  let l : Fin m → ℝ := fun i => if hi : i.1 < k then lamStrict ⟨i.1, hi⟩ else lamAffine i
  -- First convert the `EReal` margin inequality to an ordinary real inequality.
  have hrealMargin :
      ∀ x : Fin n → ℝ, 0 ≤ ∑ i : Fin m, l i * (dotProduct (a i) x - α i) := by
    intro x
    have hx := hmargin x
    have hstrictE :
        (∑ i : Fin k,
            ((lamStrict i : ℝ) : EReal) *
              ((((dotProduct (a (Fin.castLE hk_upper i)) x - α (Fin.castLE hk_upper i) : ℝ)) :
                EReal))) =
          (((∑ i : Fin k,
              lamStrict i * (dotProduct (a (Fin.castLE hk_upper i)) x -
                α (Fin.castLE hk_upper i)) : ℝ)) : EReal) := by
      rw [helperForTheorem_21_1_coe_finset_sum_real]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [EReal.coe_mul]
    have hAffineE :
        (∑ j : Fin m,
            ((lamAffine j : ℝ) : EReal) *
              ((((if j.1 < k then 0 else dotProduct (a j) x - α j : ℝ)) : EReal))) =
          (((∑ j : Fin m, lamAffine j * (if j.1 < k then 0 else dotProduct (a j) x - α j) :
              ℝ)) : EReal) := by
      rw [helperForTheorem_21_1_coe_finset_sum_real]
      refine Finset.sum_congr rfl ?_
      intro j hj
      by_cases hki : j.1 < k
      · simp [hki]
      · simp [hki]
    have hsumE :
        (∑ i : Fin k,
            ((lamStrict i : ℝ) : EReal) *
              ((((dotProduct (a (Fin.castLE hk_upper i)) x - α (Fin.castLE hk_upper i) : ℝ)) :
                EReal))) +
            ∑ j : Fin m,
              ((lamAffine j : ℝ) : EReal) *
                ((((if j.1 < k then 0 else dotProduct (a j) x - α j : ℝ)) : EReal)) =
          (((∑ i : Fin k, lamStrict i * (dotProduct (a (Fin.castLE hk_upper i)) x -
              α (Fin.castLE hk_upper i))) +
            ∑ j : Fin m, lamAffine j * (if j.1 < k then 0 else dotProduct (a j) x - α j) :
              ℝ) : EReal) := by
      rw [hstrictE, hAffineE]
      norm_num
    rw [hsumE] at hx
    have hxReal :
        0 ≤ (∑ i : Fin k, lamStrict i * (dotProduct (a (Fin.castLE hk_upper i)) x -
            α (Fin.castLE hk_upper i))) +
          ∑ j : Fin m, lamAffine j * (if j.1 < k then 0 else dotProduct (a j) x - α j) := by
      exact_mod_cast hx
    have hstrictRewrite :
        (∑ i : Fin k, lamStrict i * (dotProduct (a (Fin.castLE hk_upper i)) x -
            α (Fin.castLE hk_upper i))) =
          ∑ j : Fin m,
            if hj : j.1 < k then lamStrict ⟨j.1, hj⟩ * (dotProduct (a j) x - α j) else 0 := by
      simpa using
        helperForTheorem_22_2_sum_firstBlock_extension hk_upper
          (w := fun i : Fin k =>
            lamStrict i * (dotProduct (a (Fin.castLE hk_upper i)) x - α (Fin.castLE hk_upper i)))
    have hsumRewrite :
        (∑ i : Fin k, lamStrict i * (dotProduct (a (Fin.castLE hk_upper i)) x -
            α (Fin.castLE hk_upper i))) +
            ∑ j : Fin m, lamAffine j * (if j.1 < k then 0 else dotProduct (a j) x - α j) =
          ∑ i : Fin m, l i * (dotProduct (a i) x - α i) := by
      rw [hstrictRewrite, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hki : i.1 < k
      · simp [l, hki]
      · simp [l, hki]
    rw [hsumRewrite] at hxReal
    exact hxReal
  let s : Fin n → ℝ := ∑ i : Fin m, l i • a i
  let c : ℝ := ∑ i : Fin m, l i * α i
  -- Package the weighted normals and scalar terms into the affine form `x ↦ ⟪s,x⟫ - c`.
  have hsum_dot :
      ∀ x : Fin n → ℝ, ∑ i : Fin m, l i * dotProduct (a i) x = dotProduct s x := by
    intro x
    calc
      ∑ i : Fin m, l i * dotProduct (a i) x
          = ∑ i : Fin m, dotProduct (l i • a i) x := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [smul_eq_mul]
      _ = dotProduct (∑ i : Fin m, l i • a i) x := by
            symm
            simpa using
              (sum_dotProduct (s := (Finset.univ : Finset (Fin m)))
                (u := fun i => l i • a i) (v := x))
      _ = dotProduct s x := by
            rfl
  have hsum_margin :
      ∀ x : Fin n → ℝ,
        ∑ i : Fin m, l i * (dotProduct (a i) x - α i) = dotProduct s x - c := by
    intro x
    calc
      ∑ i : Fin m, l i * (dotProduct (a i) x - α i)
          = ∑ i : Fin m, ((l i * dotProduct (a i) x) - (l i * α i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = (∑ i : Fin m, l i * dotProduct (a i) x) - (∑ i : Fin m, l i * α i) := by
            rw [Finset.sum_sub_distrib]
      _ = dotProduct s x - c := by
            simp [hsum_dot, c]
  -- Evaluating the global inequality at `x = 0` forces the scalar term to be nonpositive.
  have hc_nonpos : c ≤ 0 := by
    have h0 := hrealMargin 0
    rw [hsum_margin 0] at h0
    simp [c] at h0
    linarith
  -- A nonzero summed normal would violate the margin inequality along its own direction.
  have hs_zero : s = 0 := by
    by_contra hs_ne
    have hss_ne : dotProduct s s ≠ 0 := by
      intro hss_zero
      exact hs_ne ((dotProduct_self_eq_zero (v := s)).1 hss_zero)
    let t : ℝ := (c - 1) / dotProduct s s
    have ht := hrealMargin (t • s)
    rw [hsum_margin (t • s)] at ht
    have hdot_t : dotProduct s (t • s) - c = -1 := by
      calc
        dotProduct s (t • s) - c = t * dotProduct s s - c := by
          simp
        _ = -1 := by
              dsimp [t]
              field_simp [hss_ne]
              ring
    rw [hdot_t] at ht
    linarith
  refine ⟨l, ?_, ?_, ?_, ?_⟩
  · intro i
    -- The merged coefficient family is nonnegative on each block separately.
    by_cases hi : i.1 < k
    · simp [l, hi, hlamStrictNonneg]
    · simp [l, hi, hlamAffineNonneg]
  · rcases hStrictNonzero with ⟨i0, hi0⟩
    refine ⟨Fin.castLE hk_upper i0, ?_, ?_⟩
    · simpa using i0.2
    · simpa [l] using hi0
  · simpa [s] using hs_zero
  · simpa [c] using hc_nonpos

/-- Helper for Theorem 22.2: a strict/weak feasible point and a mixed Farkas certificate
cannot coexist. -/
lemma helperForTheorem_22_2_certificate_excludes_feasible
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ) (k : ℕ)
    {x : Fin n → ℝ}
    (hxStrict : ∀ i : Fin m, i.1 < k → dotProduct (a i) x < α i)
    (hxWeak : ∀ i : Fin m, k ≤ i.1 → dotProduct (a i) x ≤ α i)
    {l : Fin m → ℝ}
    (hl_nonneg : ∀ i : Fin m, 0 ≤ l i)
    (hFirstNonzero : ∃ i : Fin m, i.1 < k ∧ l i ≠ 0)
    (hsum_zero : (∑ i, l i • a i) = 0)
    (hscalar_nonpos : (∑ i, l i * α i) ≤ 0) : False := by
  -- Multiply each inequality by the matching nonnegative coefficient and sum the results.
  have hweighted_lt :
      ∑ i : Fin m, l i * dotProduct (a i) x < ∑ i : Fin m, l i * α i := by
    refine Finset.sum_lt_sum ?_ ?_
    · intro i hi
      by_cases hki : i.1 < k
      · exact mul_le_mul_of_nonneg_left (le_of_lt (hxStrict i hki)) (hl_nonneg i)
      · exact mul_le_mul_of_nonneg_left (hxWeak i (Nat.le_of_not_lt hki)) (hl_nonneg i)
    · rcases hFirstNonzero with ⟨i0, hi0lt, hi0ne⟩
      refine ⟨i0, by simp, ?_⟩
      have hi0pos : 0 < l i0 := lt_of_le_of_ne (hl_nonneg i0) (Ne.symm hi0ne)
      exact mul_lt_mul_of_pos_left (hxStrict i0 hi0lt) hi0pos
  -- The vanishing normal sum turns the weighted left side into `0`, forcing positivity of
  -- the scalar combination and contradicting the certificate hypothesis `≤ 0`.
  have hdot_sum :
      ∑ i : Fin m, l i * dotProduct (a i) x = dotProduct (∑ i : Fin m, l i • a i) x := by
    calc
      ∑ i : Fin m, l i * dotProduct (a i) x
          = ∑ i : Fin m, dotProduct (l i • a i) x := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [smul_eq_mul]
      _ = dotProduct (∑ i : Fin m, l i • a i) x := by
            symm
            simpa using
              (sum_dotProduct (s := (Finset.univ : Finset (Fin m)))
                (u := fun i => l i • a i) (v := x))
  have hleft_zero : ∑ i : Fin m, l i * dotProduct (a i) x = 0 := by
    rw [hdot_sum, hsum_zero]
    simp
  have hscalar_pos : 0 < ∑ i : Fin m, l i * α i := by
    linarith
  linarith

-- Proof sketch: this is the mixed strict/weak form of Farkas' lemma. A feasible `x` for the
-- strict first `k` inequalities and weak remaining inequalities is incompatible with a
-- nonnegative multiplier vector whose first `k` coordinates are not all zero and which satisfies
-- the vanishing linear combination and nonpositive scalar combination. Existence of one of the
-- two alternatives follows by reducing to the convex separation theorem of the previous section.
/-- Theorem 22.2: Let `a_i ∈ ℝ^n` and `α_i ∈ ℝ` for `i = 1, ..., m`, and let `k` satisfy
`1 ≤ k ≤ m`. Assume the weak subsystem `⟪a_i, x⟫ ≤ α_i` for `i = k + 1, ..., m` is consistent.
Then exactly one of the following holds: (a) there exists `x` such that `⟪a_i, x⟫ < α_i` for
`i = 1, ..., k` and `⟪a_i, x⟫ ≤ α_i` for `i = k + 1, ..., m`; (b) there exist nonnegative
reals `λ_1, ..., λ_m`, with at least one of `λ_1, ..., λ_k` nonzero, such that
`∑ i, λ_i a_i = 0` and `∑ i, λ_i α_i ≤ 0`. -/
theorem farkasAlternative_mixed_strictWeak_linearInequalities
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ) (k : ℕ)
    (hk_lower : 1 ≤ k) (hk_upper : k ≤ m)
    (hconsistent :
      ∃ x : Fin n → ℝ, ∀ i : Fin m, k ≤ i.1 → dotProduct (a i) x ≤ α i) :
    ((∃ x : Fin n → ℝ,
        (∀ i : Fin m, i.1 < k → dotProduct (a i) x < α i) ∧
          ∀ i : Fin m, k ≤ i.1 → dotProduct (a i) x ≤ α i) ∨
        ∃ l : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ l i) ∧
            (∃ i : Fin m, i.1 < k ∧ l i ≠ 0) ∧
              (∑ i, l i • a i) = 0 ∧ (∑ i, l i * α i) ≤ 0) ∧
      ¬((∃ x : Fin n → ℝ,
          (∀ i : Fin m, i.1 < k → dotProduct (a i) x < α i) ∧
            ∀ i : Fin m, k ≤ i.1 → dotProduct (a i) x ≤ α i) ∧
        ∃ l : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ l i) ∧
            (∃ i : Fin m, i.1 < k ∧ l i ≠ 0) ∧
              (∑ i, l i • a i) = 0 ∧ (∑ i, l i * α i) ≤ 0) := by
  let fStrict : Fin k → (Fin n → ℝ) → EReal :=
    fun i x => (((dotProduct x (a (Fin.castLE hk_upper i)) - α (Fin.castLE hk_upper i) : ℝ)) : EReal)
  let fAffine : Fin m → (Fin n → ℝ) → ℝ :=
    fun i x => if i.1 < k then 0 else dotProduct x (a i) - α i
  -- Route correction: specialize Theorem 21.2 on `Set.univ`, using the first `k`
  -- inequalities as the strict block and a dummy zero affine block on indices `< k`.
  have hfStrict :
      ∀ i : Fin k, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fStrict i) := by
    intro i
    let g : AffineMap ℝ (Fin n → ℝ) ℝ :=
      (dotProductLinear n (a (Fin.castLE hk_upper i))).toAffineMap -
        AffineMap.const ℝ (Fin n → ℝ) (α (Fin.castLE hk_upper i))
    -- Each strict-block function is an affine real map coerced to `EReal`.
    simpa [fStrict, g, dotProductLinear] using
      helperForTheorem_21_2_shifted_affine_properConvex (n := n) g 0
  have hdomStrict :
      ∀ i : Fin k,
        euclideanRelativeInterior_fin n (Set.univ : Set (Fin n → ℝ)) ⊆
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fStrict i) := by
    intro i x hx
    -- The affine `EReal` functions are finite everywhere on `ℝⁿ`.
    change ∃ μ,
      (x, μ) ∈ epigraph (S := (Set.univ : Set (Fin n → ℝ)))
        (fun y => (((dotProduct y (a (Fin.castLE hk_upper i)) - α (Fin.castLE hk_upper i) : ℝ)) :
          EReal))
    refine ⟨dotProduct x (a (Fin.castLE hk_upper i)) - α (Fin.castLE hk_upper i), ?_⟩
    exact ⟨by trivial, le_rfl⟩
  have hAffine :
      ∀ j : Fin m, ∃ g : (Fin n → ℝ) →ᵃ[ℝ] ℝ, fAffine j = g := by
    intro j
    by_cases hj : j.1 < k
    · refine ⟨AffineMap.const ℝ (Fin n → ℝ) 0, ?_⟩
      -- The first affine block is the dummy zero constraint.
      ext x
      simp [fAffine, hj]
    · let g : AffineMap ℝ (Fin n → ℝ) ℝ :=
        (dotProductLinear n (a j)).toAffineMap - AffineMap.const ℝ (Fin n → ℝ) (α j)
      refine ⟨g, ?_⟩
      -- Outside the first block, recover the original weak linear inequality.
      ext x
      simp [fAffine, g, hj, dotProductLinear]
  have hFeasRi :
      ∃ x, x ∈ euclideanRelativeInterior_fin n (Set.univ : Set (Fin n → ℝ)) ∧
        ∀ j : Fin m, fAffine j x ≤ 0 := by
    rcases hconsistent with ⟨x, hx⟩
    refine ⟨x, ?_, ?_⟩
    · refine (mem_euclideanRelativeInterior_fin_iff
        (n := n) (C := (Set.univ : Set (Fin n → ℝ))) (x := x)).2 ?_
      have himgUniv :
          ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm ''
            (Set.univ : Set (Fin n → ℝ))) =
            (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
        ext y
        constructor
        · intro hy
          trivial
        · intro hy
          refine ⟨(EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)) y, by simp, ?_⟩
          simp
      rw [himgUniv]
      unfold euclideanRelativeInterior
      refine ⟨by simp, 1, by norm_num, ?_⟩
      intro y hy
      trivial
    · intro j
      by_cases hj : j.1 < k
      · simp [fAffine, hj]
      · simpa [fAffine, hj, dotProduct_comm] using hx j (Nat.le_of_not_lt hj)
  have hAlt :=
    theorem21_mixed_convex_affine_alternative
      (Set.univ : Set (Fin n → ℝ)) convex_univ
      fStrict hfStrict hdomStrict fAffine hAffine hFeasRi
  rw [xor_def] at hAlt
  refine ⟨?_, ?_⟩
  · rcases hAlt with hPrimal | hDual
    · left
      rcases hPrimal with ⟨⟨x, hxC, hxStrict, hxAffine⟩, _⟩
      refine ⟨x, ?_, ?_⟩
      · intro i hi
        have hxi :
            fStrict ⟨i.1, hi⟩ x < (0 : EReal) := hxStrict ⟨i.1, hi⟩
        have hxiReal : dotProduct x (a i) - α i < 0 := by
          exact_mod_cast (by simpa [fStrict] using hxi :
            (((dotProduct x (a i) - α i : ℝ)) : EReal) < (0 : EReal))
        have hcomm : dotProduct x (a i) = dotProduct (a i) x := by
          simp [dotProduct_comm]
        linarith
      · intro i hki
        have hxi : fAffine i x ≤ 0 := hxAffine i
        have hxi' : dotProduct x (a i) - α i ≤ 0 := by
          simpa [fAffine, Nat.not_lt_of_ge hki] using hxi
        have hcomm : dotProduct x (a i) = dotProduct (a i) x := by
          simp [dotProduct_comm]
        linarith
    · right
      rcases hDual with ⟨hDual, _⟩
      rcases hDual with
        ⟨lamStrict, lamAffine, hlamStrictNonneg, hlamAffineNonneg, hStrictNonzero, hmargin⟩
      have hmargin' :
          ∀ x : Fin n → ℝ,
            (0 : EReal) ≤
              (∑ i : Fin k,
                  ((lamStrict i : ℝ) : EReal) *
                    ((((dotProduct (a (Fin.castLE hk_upper i)) x - α (Fin.castLE hk_upper i) :
                        ℝ)) : EReal))) +
                ∑ j : Fin m,
                  ((lamAffine j : ℝ) : EReal) *
                    ((((if j.1 < k then 0 else dotProduct (a j) x - α j : ℝ)) : EReal)) := by
        intro x
        simpa [fStrict, fAffine, dotProduct_comm] using hmargin x (by simp)
      exact
        helperForTheorem_22_2_dualMargin_to_linearCertificate
          a α hk_upper lamStrict lamAffine
          hlamStrictNonneg hlamAffineNonneg hStrictNonzero hmargin'
  · intro hBoth
    rcases hBoth with ⟨⟨x, hxStrict, hxWeak⟩, l, hl_nonneg, hFirstNonzero, hsum_zero, hscalar_nonpos⟩
    -- The weighted strict/weak inequalities contradict the sign pattern forced by the certificate.
    exact
      helperForTheorem_22_2_certificate_excludes_feasible
        a α k hxStrict hxWeak hl_nonneg hFirstNonzero hsum_zero hscalar_nonpos

-- Proof sketch: apply the weak-inequality form of Farkas' lemma to the subsystem indexed by
-- `i = k + 1, ..., m`, encoded in `Fin m` as the coordinates satisfying `k ≤ i.1`. A feasible
-- point and a nonnegative multiplier vector supported on this tail block cannot coexist, since
-- taking the weighted sum of the inequalities would force `0 ≤ ∑ i, λ i * α i`, contradicting
-- strict negativity. The stated infeasibility criterion is then the corresponding reformulation
-- of the exact-one-of-two-alternatives conclusion.
/-- Helper for Text 22.2.1: the dummy-head system with zero inequalities on `i.1 < k`
has the same feasible points as the original tail subsystem. -/
lemma helperForText_22_2_1_dummyHead_primal_iff_feasibleTail
    {m n k : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ) :
    (∃ x : Fin n → ℝ,
      ∀ i : Fin m, dotProduct (if i.1 < k then 0 else a i) x ≤ if i.1 < k then 0 else α i) ↔
      ∃ x : Fin n → ℝ, ∀ i : Fin m, k ≤ i.1 → dotProduct (a i) x ≤ α i := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    -- On the tail block, the dummy family agrees with the original data.
    intro i hki
    simpa [Nat.not_lt_of_ge hki] using hx i
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro i
    -- On the head block the dummy inequality is `0 ≤ 0`; on the tail block it is the
    -- original weak inequality.
    by_cases hki : i.1 < k
    · simp [hki]
    · simpa [hki] using hx i (Nat.le_of_not_lt hki)

/-- Helper for Text 22.2.1: a dual certificate for the dummy-head system can be truncated to
an equivalent certificate supported on the tail block. -/
lemma helperForText_22_2_1_dummyHead_dual_to_tailCertificate
    {m n k : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    {l : Fin m → ℝ}
    (hl_nonneg : ∀ i : Fin m, 0 ≤ l i)
    (hsum_zero : (∑ i : Fin m, l i • (if i.1 < k then 0 else a i)) = 0)
    (hscalar_neg : (∑ i : Fin m, l i * (if i.1 < k then 0 else α i)) < 0) :
    ∃ lTail : Fin m → ℝ,
      (∀ i : Fin m, 0 ≤ lTail i) ∧
        (∀ i : Fin m, i.1 < k → lTail i = 0) ∧
          (∑ i, lTail i • a i) = 0 ∧ (∑ i, lTail i * α i) < 0 := by
  let lTail : Fin m → ℝ := fun i => if i.1 < k then 0 else l i
  refine ⟨lTail, ?_, ?_, ?_, ?_⟩
  · intro i
    -- Zeroing the head block preserves nonnegativity.
    by_cases hki : i.1 < k
    · simp [lTail, hki]
    · simp [lTail, hki, hl_nonneg]
  · intro i hki
    -- The truncated family is identically zero on the head block.
    simp [lTail, hki]
  · -- The vector sum is unchanged because both the coefficient and the dummy vector vanish
    -- on the head block.
    calc
      ∑ i : Fin m, lTail i • a i
          = ∑ i : Fin m, l i • (if i.1 < k then 0 else a i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hki : i.1 < k
              · simp [lTail, hki]
              · simp [lTail, hki]
      _ = 0 := hsum_zero
  · -- The scalar sum is likewise unchanged after removing the dummy head coordinates.
    calc
      ∑ i : Fin m, lTail i * α i
          = ∑ i : Fin m, l i * (if i.1 < k then 0 else α i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hki : i.1 < k
              · simp [lTail, hki]
              · simp [lTail, hki]
      _ < 0 := hscalar_neg

/-- Helper for Text 22.2.1: a feasible tail point and a tail-supported negative certificate
cannot coexist. -/
lemma helperForText_22_2_1_tailCertificate_excludes_feasibleTail
    {m n k : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    {x : Fin n → ℝ}
    (hx : ∀ i : Fin m, k ≤ i.1 → dotProduct (a i) x ≤ α i)
    {l : Fin m → ℝ}
    (hl_nonneg : ∀ i : Fin m, 0 ≤ l i)
    (hhead_zero : ∀ i : Fin m, i.1 < k → l i = 0)
    (hsum_zero : (∑ i, l i • a i) = 0)
    (hscalar_neg : (∑ i, l i * α i) < 0) : False := by
  have hxDummy :
      ∀ i : Fin m, dotProduct (if i.1 < k then 0 else a i) x ≤ if i.1 < k then 0 else α i := by
    intro i
    -- The dummy head inequalities are automatic; the tail inequalities are the assumed ones.
    by_cases hki : i.1 < k
    · simp [hki]
    · simpa [hki] using hx i (Nat.le_of_not_lt hki)
  have hl_nonneg' : 0 ≤ l := by
    intro i
    exact hl_nonneg i
  have hsumDummy_zero :
      (∑ i : Fin m, l i • (if i.1 < k then 0 else a i)) = 0 := by
    -- Head terms vanish because the certificate is supported on the tail block.
    calc
      ∑ i : Fin m, l i • (if i.1 < k then 0 else a i)
          = ∑ i : Fin m, l i • a i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hki : i.1 < k
              · simp [hki, hhead_zero i hki]
              · simp [hki]
      _ = 0 := hsum_zero
  have hscalarDummy_neg :
      (∑ i : Fin m, l i * (if i.1 < k then 0 else α i)) < 0 := by
    -- The same support argument removes the head block from the scalar combination.
    calc
      ∑ i : Fin m, l i * (if i.1 < k then 0 else α i)
          = ∑ i : Fin m, l i * α i := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hki : i.1 < k
              · simp [hki, hhead_zero i hki]
              · simp [hki]
      _ < 0 := hscalar_neg
  -- Apply the already-proved weak Farkas incompatibility to the dummy-head family.
  exact
    helperForTheorem_22_1_certificate_excludes_feasible
      (a := fun i : Fin m => if i.1 < k then 0 else a i)
      (α := fun i : Fin m => if i.1 < k then 0 else α i)
      hxDummy hl_nonneg' hsumDummy_zero hscalarDummy_neg

/-- Text 22.2.1: Let `a_i ∈ ℝ^n` and `α_i ∈ ℝ` for `i = 1, ..., m`, and let `k` be an integer
with `1 ≤ k ≤ m`. For the weak subsystem `⟪a_i, x⟫ ≤ α_i` with `i = k + 1, ..., m`, encoded
with `Fin m` as the indices satisfying `k ≤ i.1`, exactly one of the following holds: (a) there
exists `x ∈ ℝ^n` satisfying all these inequalities; (b) there exist nonnegative multipliers
`λ_{k+1}, ..., λ_m` such that `∑_{i=k+1}^m λ_i a_i = 0` and `∑_{i=k+1}^m λ_i α_i < 0`.
Equivalently, the subsystem is infeasible if and only if such a nonnegative certificate exists. -/
theorem farkasAlternative_weakTail_linearInequalities
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ) (k : ℕ)
    (hk_lower : 1 ≤ k) (hk_upper : k ≤ m) :
    let feasibleTail :=
      ∃ x : Fin n → ℝ, ∀ i : Fin m, k ≤ i.1 → dotProduct (a i) x ≤ α i
    let certificateTail :=
      ∃ l : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ l i) ∧
          (∀ i : Fin m, i.1 < k → l i = 0) ∧
            (∑ i, l i • a i) = 0 ∧ (∑ i, l i * α i) < 0
    (((feasibleTail ∨ certificateTail) ∧ ¬(feasibleTail ∧ certificateTail)) ∧
      ((¬feasibleTail) ↔ certificateTail)) := by
  dsimp
  let aDummy : Fin m → (Fin n → ℝ) := fun i => if i.1 < k then 0 else a i
  let αDummy : Fin m → ℝ := fun i => if i.1 < k then 0 else α i
  have hAlt := farkasAlternative_linearInequalities aDummy αDummy
  have hPrimalIff :
      (∃ x : Fin n → ℝ, ∀ i : Fin m, dotProduct (aDummy i) x ≤ αDummy i) ↔
        ∃ x : Fin n → ℝ, ∀ i : Fin m, k ≤ i.1 → dotProduct (a i) x ≤ α i := by
    -- The dummy-head primal system is exactly the tail subsystem.
    simpa [aDummy, αDummy] using
      helperForText_22_2_1_dummyHead_primal_iff_feasibleTail a α (k := k)
  have hOr :
      (∃ x : Fin n → ℝ, ∀ i : Fin m, k ≤ i.1 → dotProduct (a i) x ≤ α i) ∨
        ∃ l : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ l i) ∧
            (∀ i : Fin m, i.1 < k → l i = 0) ∧
              (∑ i, l i • a i) = 0 ∧ (∑ i, l i * α i) < 0 := by
    rcases hAlt.1 with hPrimalDummy | hDualDummy
    · -- Transport the dummy-head feasible point back to the tail subsystem.
      left
      exact hPrimalIff.mp hPrimalDummy
    · -- Truncate the dummy-head certificate to the exact tail-supported certificate.
      right
      rcases hDualDummy with ⟨l, hl_nonneg, hsum_zero, hscalar_neg⟩
      exact
        helperForText_22_2_1_dummyHead_dual_to_tailCertificate
          a α (k := k) (l := l) (fun i => hl_nonneg i) hsum_zero hscalar_neg
  have hNotBoth :
      ¬((∃ x : Fin n → ℝ, ∀ i : Fin m, k ≤ i.1 → dotProduct (a i) x ≤ α i) ∧
        ∃ l : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ l i) ∧
            (∀ i : Fin m, i.1 < k → l i = 0) ∧
              (∑ i, l i • a i) = 0 ∧ (∑ i, l i * α i) < 0) := by
    intro hBoth
    rcases hBoth with ⟨⟨x, hx⟩, l, hl_nonneg, hhead_zero, hsum_zero, hscalar_neg⟩
    -- The weighted-sum contradiction now runs on the original tail-supported certificate.
    exact
      helperForText_22_2_1_tailCertificate_excludes_feasibleTail
        a α (k := k) hx hl_nonneg hhead_zero hsum_zero hscalar_neg
  have hIff :
      (¬∃ x : Fin n → ℝ, ∀ i : Fin m, k ≤ i.1 → dotProduct (a i) x ≤ α i) ↔
        ∃ l : Fin m → ℝ,
          (∀ i : Fin m, 0 ≤ l i) ∧
            (∀ i : Fin m, i.1 < k → l i = 0) ∧
              (∑ i, l i • a i) = 0 ∧ (∑ i, l i * α i) < 0 := by
    constructor
    · intro hNotFeasible
      -- The disjunction forces the certificate branch once feasibility is ruled out.
      rcases hOr with hFeasible | hCertificate
      · exact False.elim (hNotFeasible hFeasible)
      · exact hCertificate
    · intro hCertificate hFeasible
      exact hNotBoth ⟨hFeasible, hCertificate⟩
  exact ⟨⟨hOr, hNotBoth⟩, hIff⟩

/-- Text 22.2.2: A linear inequality `⟪a₀, x⟫ ≤ α₀` is a consequence of the system
`⟪aᵢ, x⟫ ≤ αᵢ` for `i = 1, ..., m` if every `x` satisfying the whole system also satisfies
`⟪a₀, x⟫ ≤ α₀`. -/
def IsConsequenceOfLinearInequalitySystem
    {m n : ℕ} (a₀ : Fin n → ℝ) (α₀ : ℝ) (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ) : Prop :=
  ∀ ⦃x : Fin n → ℝ⦄, (∀ i : Fin m, dotProduct (a i) x ≤ α i) → dotProduct a₀ x ≤ α₀

-- Proof sketch: rewrite the hypotheses `ξ₁ ≥ 0` and `ξ₂ ≥ 0` as the inequalities
-- `-ξ₁ ≤ 0` and `-ξ₂ ≤ 0`. Adding these two inequalities gives `-(ξ₁ + ξ₂) ≤ 0`,
-- which is equivalent to `ξ₁ + ξ₂ ≥ 0`.
/-- Text 22.2.3: The inequality `ξ₁ + ξ₂ ≥ 0`, encoded as `⟪(-1, -1), x⟫ ≤ 0`, is a
consequence of the system `ξ_i ≥ 0` for `i = 1, 2`, encoded as
`⟪(-1, 0), x⟫ ≤ 0` and `⟪(0, -1), x⟫ ≤ 0`. -/
theorem sum_nonnegative_isConsequence_of_coordinatewiseNonnegative :
    IsConsequenceOfLinearInequalitySystem
      (a₀ := ![-(1 : ℝ), -1])
      (α₀ := 0)
      (a := ![(![-(1 : ℝ), 0] : Fin 2 → ℝ), ![0, (-(1 : ℝ))]])
      (α := ![(0 : ℝ), 0]) := by
  intro x hx
  -- Specialize the system hypotheses to the two coordinate rows.
  have h₁ : dotProduct (![-(1 : ℝ), 0] : Fin 2 → ℝ) x ≤ 0 := hx 0
  have h₂ : dotProduct (![0, (-(1 : ℝ))] : Fin 2 → ℝ) x ≤ 0 := hx 1
  -- Add the two inequalities, then normalize the dot products to the target row.
  have hsum :
      dotProduct (![-(1 : ℝ), 0] : Fin 2 → ℝ) x +
          dotProduct (![0, (-(1 : ℝ))] : Fin 2 → ℝ) x ≤
        0 := by
    linarith
  simpa [dotProduct, add_comm, add_left_comm, add_assoc] using hsum

-- Proof sketch: one direction is immediate by multiplying the given inequalities by the
-- nonnegative coefficients `λ i` and summing, using the relations `∑ i, λ i • a i = a₀`
-- and `∑ i, λ i * α i ≤ α₀`. For the converse, apply the strict/weak Farkas alternative of
-- Theorem 22.2 to the system obtained by adjoining the negation of `⟪a₀, x⟫ ≤ α₀`.
/-- Helper for Theorem 22.3: a nonnegative linear combination reproducing the target normal and
bounding the target scalar yields the desired consequence relation. -/
lemma helperForTheorem_22_3_nonnegativeCombination_givesConsequence
    {m n : ℕ} (a₀ : Fin n → ℝ) (α₀ : ℝ) (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    {l : Fin m → ℝ}
    (hl_nonneg : 0 ≤ l)
    (hsum : (∑ i, l i • a i) = a₀)
    (hscalar : (∑ i, l i * α i) ≤ α₀) :
    IsConsequenceOfLinearInequalitySystem a₀ α₀ a α := by
  intro x hx
  have hl_nonneg' : ∀ i : Fin m, 0 ≤ l i := hl_nonneg
  -- Sum the original system after multiplying by the nonnegative coefficients `l i`.
  have hweighted :
      ∑ i : Fin m, l i * dotProduct (a i) x ≤ ∑ i : Fin m, l i * α i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    exact mul_le_mul_of_nonneg_left (hx i) (hl_nonneg' i)
  -- Rewrite the weighted left-hand side as the dot product of the combined normal with `x`.
  have hdot :
      ∑ i : Fin m, l i * dotProduct (a i) x = dotProduct (∑ i : Fin m, l i • a i) x := by
    calc
      ∑ i : Fin m, l i * dotProduct (a i) x
          = ∑ i : Fin m, dotProduct (l i • a i) x := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [smul_eq_mul]
      _ = dotProduct (∑ i : Fin m, l i • a i) x := by
            symm
            simpa using
              (sum_dotProduct (s := (Finset.univ : Finset (Fin m)))
                (u := fun i => l i • a i) (v := x))
  -- The coefficient identities now collapse the weighted inequality to the target inequality.
  calc
    dotProduct a₀ x = ∑ i : Fin m, l i * dotProduct (a i) x := by
      rw [← hsum, ← hdot]
    _ ≤ ∑ i : Fin m, l i * α i := hweighted
    _ ≤ α₀ := hscalar

/-- Helper for Theorem 22.3: feasibility of the original system gives feasibility of the tail
block in the augmented system whose head row is the negated target inequality. -/
lemma helperForTheorem_22_3_augmentedTailConsistent
    {m n : ℕ} (a₀ : Fin n → ℝ) (α₀ : ℝ) (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    (hconsistent : ∃ x : Fin n → ℝ, ∀ i : Fin m, dotProduct (a i) x ≤ α i) :
    ∃ x : Fin n → ℝ,
      ∀ j : Fin (m + 1),
        1 ≤ j.1 →
          dotProduct (Fin.cases (-a₀) (fun i => a i) j) x ≤
            Fin.cases (-α₀) (fun i => α i) j := by
  rcases hconsistent with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  intro j hj
  -- Indices with `1 ≤ j.1` lie in the tail, where the augmented system agrees with the
  -- original one.
  cases j using Fin.cases with
  | zero => cases hj
  | succ i =>
      simpa using hx i

/-- Helper for Theorem 22.3: a feasible point for the original system cannot also violate the
target inequality when that target is already known to be a consequence. -/
lemma helperForTheorem_22_3_augmentedPrimalContradictsConsequence
    {m n : ℕ} (a₀ : Fin n → ℝ) (α₀ : ℝ) (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    (hconsequence : IsConsequenceOfLinearInequalitySystem a₀ α₀ a α)
    {x : Fin n → ℝ}
    (hhead : dotProduct (-a₀) x < -α₀)
    (htail : ∀ i : Fin m, dotProduct (a i) x ≤ α i) : False := by
  -- Consequence gives the target inequality at every feasible point of the original system.
  have htarget : dotProduct a₀ x ≤ α₀ := hconsequence htail
  -- The augmented head inequality is exactly the strict negation of the target inequality.
  have htarget_lt : α₀ < dotProduct a₀ x := by
    simpa using hhead
  linarith

/-- Helper for Theorem 22.3: normalize the augmented Farkas certificate by dividing through by
its positive head coefficient to recover the textbook multipliers. -/
lemma helperForTheorem_22_3_augmentedCertificateToCombination
    {m n : ℕ} (a₀ : Fin n → ℝ) (α₀ : ℝ) (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    {lAug : Fin (m + 1) → ℝ}
    (hl_nonneg : ∀ j : Fin (m + 1), 0 ≤ lAug j)
    (hhead_ne : lAug 0 ≠ 0)
    (hvector :
      (-lAug 0) • a₀ + ∑ i : Fin m, lAug i.succ • a i = 0)
    (hscalar :
      (-lAug 0) * α₀ + ∑ i : Fin m, lAug i.succ * α i ≤ 0) :
    ∃ l : Fin m → ℝ, 0 ≤ l ∧ (∑ i, l i • a i) = a₀ ∧ (∑ i, l i * α i) ≤ α₀ := by
  have hhead_pos : 0 < lAug 0 := lt_of_le_of_ne (hl_nonneg 0) hhead_ne.symm
  let l : Fin m → ℝ := fun i => lAug i.succ / lAug 0
  -- First isolate the head contribution in the augmented vector equality.
  have hvector_scaled :
      (∑ i : Fin m, lAug i.succ • a i) = lAug 0 • a₀ := by
    have hneg :
        -(lAug 0 • a₀) + ∑ i : Fin m, lAug i.succ • a i = 0 := by
      simpa [neg_smul] using hvector
    exact (neg_add_eq_zero.mp hneg).symm
  -- The scalar inequality similarly bounds the tail scalar sum by the head coefficient.
  have hscalar_scaled :
      (∑ i : Fin m, lAug i.succ * α i) ≤ lAug 0 * α₀ := by
    have hneg :
        -(lAug 0 * α₀) + ∑ i : Fin m, lAug i.succ * α i ≤ 0 := by
      simpa using hscalar
    linarith
  refine ⟨l, ?_, ?_, ?_⟩
  · intro i
    -- Dividing by the positive head coefficient preserves nonnegativity.
    exact div_nonneg (hl_nonneg i.succ) (le_of_lt hhead_pos)
  · -- Scale the vector identity by the inverse head coefficient.
    calc
      ∑ i : Fin m, l i • a i
          = ∑ i : Fin m, (lAug 0)⁻¹ • (lAug i.succ • a i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [l, div_eq_mul_inv, smul_smul, mul_comm]
      _ = (lAug 0)⁻¹ • ∑ i : Fin m, lAug i.succ • a i := by
            symm
            exact Finset.smul_sum
      _ = (lAug 0)⁻¹ • (lAug 0 • a₀) := by rw [hvector_scaled]
      _ = a₀ := by simp [smul_smul, hhead_ne]
  · -- Multiply the scalar inequality by the inverse head coefficient and simplify.
    have hmul :
        (lAug 0)⁻¹ * (∑ i : Fin m, lAug i.succ * α i) ≤
          (lAug 0)⁻¹ * (lAug 0 * α₀) := by
      exact mul_le_mul_of_nonneg_left hscalar_scaled (le_of_lt (inv_pos.mpr hhead_pos))
    calc
      ∑ i : Fin m, l i * α i
          = ∑ i : Fin m, (lAug 0)⁻¹ * (lAug i.succ * α i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              simp [l, div_eq_mul_inv, mul_assoc, mul_comm]
      _ = (lAug 0)⁻¹ * (∑ i : Fin m, lAug i.succ * α i) := by
            symm
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Fin m)))
                (f := fun i => lAug i.succ * α i) (a := (lAug 0)⁻¹))
      _ ≤ (lAug 0)⁻¹ * (lAug 0 * α₀) := hmul
      _ = α₀ := by field_simp [hhead_ne]

/-- Theorem 22.3: Assuming the system `⟪aᵢ, x⟫ ≤ αᵢ` for `i = 1, ..., m` is consistent, the
inequality `⟪a₀, x⟫ ≤ α₀` is a consequence of this system if and only if there exist
nonnegative real numbers `λ₁, ..., λₘ` such that `∑ i, λᵢ aᵢ = a₀` and
`∑ i, λᵢ αᵢ ≤ α₀`. -/
theorem linearInequality_isConsequence_iff_nonnegative_combination
    {m n : ℕ} (a₀ : Fin n → ℝ) (α₀ : ℝ) (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    (hconsistent : ∃ x : Fin n → ℝ, ∀ i : Fin m, dotProduct (a i) x ≤ α i) :
    IsConsequenceOfLinearInequalitySystem a₀ α₀ a α ↔
      ∃ l : Fin m → ℝ, 0 ≤ l ∧ (∑ i, l i • a i) = a₀ ∧ (∑ i, l i * α i) ≤ α₀ := by
  constructor
  · intro hconsequence
    let aAug : Fin (m + 1) → (Fin n → ℝ) := Fin.cases (-a₀) (fun i => a i)
    let αAug : Fin (m + 1) → ℝ := Fin.cases (-α₀) (fun i => α i)
    have htailConsistent :=
      helperForTheorem_22_3_augmentedTailConsistent a₀ α₀ a α hconsistent
    -- Apply Theorem 22.2 to the augmented system with one strict head inequality.
    have hAlt :=
      farkasAlternative_mixed_strictWeak_linearInequalities
        aAug αAug 1 (by norm_num) (by simpa using Nat.succ_le_succ (Nat.zero_le m))
        htailConsistent
    rcases hAlt with ⟨hOr, hNotBoth⟩
    rcases hOr with hPrimal | hDual
    · rcases hPrimal with ⟨x, hxStrict, hxWeak⟩
      -- The primal branch would give a feasible point for the old system violating the
      -- target inequality, contradicting consequence.
      have hhead : dotProduct (-a₀) x < -α₀ := by
        simpa [aAug, αAug] using hxStrict 0 (by norm_num)
      have htail : ∀ i : Fin m, dotProduct (a i) x ≤ α i := by
        intro i
        simpa [aAug, αAug] using hxWeak i.succ (by exact Nat.succ_le_succ (Nat.zero_le i.1))
      exact False.elim
        (helperForTheorem_22_3_augmentedPrimalContradictsConsequence
          a₀ α₀ a α hconsequence hhead htail)
    · rcases hDual with ⟨lAug, hl_nonneg, hFirstNonzero, hsum_zero, hscalar_nonpos⟩
      -- The nonzero coefficient in the strict block must be the head coefficient `lAug 0`.
      have hhead_ne : lAug 0 ≠ 0 := by
        rcases hFirstNonzero with ⟨j, hjlt, hjne⟩
        have hjzero : j = 0 := by
          apply Fin.ext
          exact Nat.lt_one_iff.mp hjlt
        simpa [hjzero] using hjne
      -- Split the augmented equalities into head and tail parts and normalize them.
      have hvector :
          (-lAug 0) • a₀ + ∑ i : Fin m, lAug i.succ • a i = 0 := by
        simpa [aAug, Fin.sum_univ_succ, neg_smul] using hsum_zero
      have hscalar :
          (-lAug 0) * α₀ + ∑ i : Fin m, lAug i.succ * α i ≤ 0 := by
        simpa [αAug, Fin.sum_univ_succ] using hscalar_nonpos
      exact
        helperForTheorem_22_3_augmentedCertificateToCombination
          a₀ α₀ a α hl_nonneg hhead_ne hvector hscalar
  · rintro ⟨l, hl_nonneg, hsum, hscalar⟩
    -- The reverse implication is the direct weighted-sum argument.
    exact
      helperForTheorem_22_3_nonnegativeCombination_givesConsequence
        a₀ α₀ a α hl_nonneg hsum hscalar

-- Proof sketch: specialize Theorem 22.3 to the homogeneous system with all right-hand sides
-- equal to `0`. The system is consistent because `x = 0` satisfies every inequality, and the
-- scalar inequality `∑ i, λ i * 0 ≤ 0` is automatic, leaving exactly the stated certificate.
/-- Corollary 22.3.1 (Farkas' Lemma): The inequality `⟪a₀, x⟫ ≤ 0` is a consequence of the
homogeneous system `⟪aᵢ, x⟫ ≤ 0` for `i = 1, ..., m` if and only if there exist nonnegative
real numbers `λ₁, ..., λₘ` such that `∑ i, λᵢ aᵢ = a₀`. -/
theorem homogeneousLinearInequality_isConsequence_iff_nonnegative_combination
    {m n : ℕ} (a₀ : Fin n → ℝ) (a : Fin m → (Fin n → ℝ)) :
    IsConsequenceOfLinearInequalitySystem a₀ 0 a (fun _ : Fin m => (0 : ℝ)) ↔
      ∃ l : Fin m → ℝ, 0 ≤ l ∧ (∑ i, l i • a i) = a₀ := by
  -- The homogeneous system is consistent because the zero vector satisfies every inequality.
  have hconsistent : ∃ x : Fin n → ℝ, ∀ i : Fin m, dotProduct (a i) x ≤ 0 := by
    refine ⟨0, ?_⟩
    intro i
    simp
  -- Specialize Theorem 22.3 to zero right-hand sides, then simplify the scalar side-condition.
  simpa using
    (linearInequality_isConsequence_iff_nonnegative_combination
      a₀ 0 a (fun _ : Fin m => (0 : ℝ)) hconsistent)

/-- The cone generated by finitely many vectors `a₁, ..., aₘ` using nonnegative coefficients. -/
def generatedConeOfFamily
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {y | ∃ l : Fin m → ℝ, (∀ i : Fin m, 0 ≤ l i) ∧ y = ∑ i, l i • a i}

/-- The polar cone of a set `K ⊆ ℝⁿ`, encoded using the standard dot product on `Fin n → ℝ`. -/
def polarConeOfSet
    {n : ℕ} (K : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  {x | ∀ ⦃y : Fin n → ℝ⦄, y ∈ K → dotProduct x y ≤ 0}

/-- Helper for Text 22.3.2: each generator `a i` lies in the finitely generated cone spanned by
the family `a`. -/
lemma helperForText_22_3_2_generator_mem_generatedConeOfFamily
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (i : Fin m) :
    a i ∈ generatedConeOfFamily a := by
  -- Use the Kronecker-delta coefficient family that is `1` at `i` and `0` elsewhere.
  refine ⟨fun j => if j = i then 1 else 0, ?_, ?_⟩
  · intro j
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  · -- Summing the resulting combination leaves exactly the `i`-th generator.
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))

/-- Helper for Text 22.3.2: membership in the polar of a finitely generated cone is equivalent to
testing the inequality only on the generators. -/
lemma helperForText_22_3_2_mem_polar_generatedCone_iff_generator_inequalities
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (x : Fin n → ℝ) :
    x ∈ polarConeOfSet (generatedConeOfFamily a) ↔ ∀ i : Fin m, dotProduct (a i) x ≤ 0 := by
  constructor
  · intro hx i
    -- Apply the polar inequality to the single generator `a i`.
    have hgenerator : a i ∈ generatedConeOfFamily a :=
      helperForText_22_3_2_generator_mem_generatedConeOfFamily a i
    have htest : dotProduct x (a i) ≤ 0 := hx hgenerator
    simpa [dotProduct_comm] using htest
  · intro hx y hy
    rcases hy with ⟨l, hl_nonneg, rfl⟩
    -- Multiply each generator inequality by its nonnegative coefficient and sum.
    have hweighted :
        ∑ i : Fin m, l i * dotProduct (a i) x ≤ 0 := by
      have hsum_le :
          ∑ i : Fin m, l i * dotProduct (a i) x ≤ ∑ i : Fin m, 0 := by
        refine Finset.sum_le_sum ?_
        intro i hi
        simpa using mul_le_mul_of_nonneg_left (hx i) (hl_nonneg i)
      simpa using hsum_le
    -- Rewrite the weighted sum as the dot product against the conic combination.
    have hdot :
        ∑ i : Fin m, l i * dotProduct (a i) x =
          dotProduct (∑ i : Fin m, l i • a i) x := by
      calc
        ∑ i : Fin m, l i * dotProduct (a i) x
            = ∑ i : Fin m, dotProduct (l i • a i) x := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simp [smul_eq_mul]
        _ = dotProduct (∑ i : Fin m, l i • a i) x := by
              symm
              simpa using
                (sum_dotProduct (s := (Finset.univ : Finset (Fin m)))
                  (u := fun i => l i • a i) (v := x))
    have hcombination : dotProduct (∑ i : Fin m, l i • a i) x ≤ 0 := by
      rw [← hdot]
      exact hweighted
    simpa [dotProduct_comm] using hcombination

/-- Helper for Text 22.3.2: a homogeneous inequality is a consequence of the generator system
exactly when its normal lies in the double polar cone. -/
lemma helperForText_22_3_2_homogeneousConsequence_iff_mem_doublePolar
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (a₀ : Fin n → ℝ) :
    IsConsequenceOfLinearInequalitySystem a₀ 0 a (fun _ : Fin m => (0 : ℝ)) ↔
      a₀ ∈ polarConeOfSet (polarConeOfSet (generatedConeOfFamily a)) := by
  -- Unfold double-polar membership so both sides quantify over the same test vectors.
  change
    IsConsequenceOfLinearInequalitySystem a₀ 0 a (fun _ : Fin m => (0 : ℝ)) ↔
      ∀ ⦃x : Fin n → ℝ⦄, x ∈ polarConeOfSet (generatedConeOfFamily a) → dotProduct a₀ x ≤ 0
  constructor
  · intro h x hx
    exact h ((helperForText_22_3_2_mem_polar_generatedCone_iff_generator_inequalities a x).1 hx)
  · intro h x hx
    exact h ((helperForText_22_3_2_mem_polar_generatedCone_iff_generator_inequalities a x).2 hx)

/-- Helper for Text 22.3.2: the double polar of a finitely generated cone coincides with the
cone itself. -/
lemma helperForText_22_3_2_doublePolar_eq_generatedConeOfFamily
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) :
    polarConeOfSet (polarConeOfSet (generatedConeOfFamily a)) = generatedConeOfFamily a := by
  ext a₀
  constructor
  · intro ha₀
    -- Convert double-polar membership into a Farkas consequence, then into a conic combination.
    have hconsequence :
        IsConsequenceOfLinearInequalitySystem a₀ 0 a (fun _ : Fin m => (0 : ℝ)) :=
      (helperForText_22_3_2_homogeneousConsequence_iff_mem_doublePolar a a₀).2 ha₀
    rcases
        (homogeneousLinearInequality_isConsequence_iff_nonnegative_combination a₀ a).1
          hconsequence with
      ⟨l, hl_nonneg, hsum⟩
    exact ⟨l, fun i => hl_nonneg i, hsum.symm⟩
  · intro ha₀
    rcases ha₀ with ⟨l, hl_nonneg, hsum⟩
    -- A conic combination gives the homogeneous consequence, hence double-polar membership.
    have hl_nonneg' : 0 ≤ l := by
      intro i
      exact hl_nonneg i
    have hconsequence :
        IsConsequenceOfLinearInequalitySystem a₀ 0 a (fun _ : Fin m => (0 : ℝ)) :=
      (homogeneousLinearInequality_isConsequence_iff_nonnegative_combination a₀ a).2
        ⟨l, hl_nonneg', hsum.symm⟩
    exact (helperForText_22_3_2_homogeneousConsequence_iff_mem_doublePolar a a₀).1 hconsequence

-- Proof sketch: for (i), expand membership in the generated cone and check that it is enough to
-- test nonpositivity on the generators `a i`, since nonnegative linear combinations preserve the
-- inequality. Part (ii) is then exactly the reformulation of consequence for the homogeneous
-- system in terms of the polar of `Kᵒ`. Part (iii) is the bipolar theorem for finitely generated
-- convex cones, equivalently the homogeneous form of Farkas' lemma.
/-- Text 22.3.2: If `K = {∑ i, λᵢ aᵢ | λᵢ ≥ 0}` is the finitely generated convex cone spanned by
`a₁, ..., aₘ ∈ ℝⁿ`, then (i) `Kᵒ = {x : ⟪aᵢ, x⟫ ≤ 0 for i = 1, ..., m}`; (ii) for every
`a₀ ∈ ℝⁿ`, the inequality `⟪a₀, x⟫ ≤ 0` is a consequence of the system `⟪aᵢ, x⟫ ≤ 0`
`(i = 1, ..., m)` if and only if `a₀ ∈ Kᵒᵒ`; and (iii) `Kᵒᵒ = K`. -/
theorem generatedCone_polar_characterization_and_bipolar
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) :
    let K := generatedConeOfFamily a
    let Kpolar := polarConeOfSet K
    (Kpolar = {x | ∀ i : Fin m, dotProduct (a i) x ≤ 0}) ∧
      (∀ a₀ : Fin n → ℝ,
        IsConsequenceOfLinearInequalitySystem a₀ 0 a (fun _ : Fin m => (0 : ℝ)) ↔
          a₀ ∈ polarConeOfSet Kpolar) ∧
      polarConeOfSet Kpolar = K := by
  dsimp
  refine ⟨?_, ?_, helperForText_22_3_2_doublePolar_eq_generatedConeOfFamily a⟩
  · -- Part (i): the polar is determined by the generator inequalities.
    ext x
    exact helperForText_22_3_2_mem_polar_generatedCone_iff_generator_inequalities a x
  · intro a₀
    -- Part (ii): homogeneous consequence is exactly double-polar membership.
    exact helperForText_22_3_2_homogeneousConsequence_iff_mem_doublePolar a a₀

end Section22
end Chap04
