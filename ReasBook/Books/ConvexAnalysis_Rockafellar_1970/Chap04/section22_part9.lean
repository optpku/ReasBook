/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section22_part8

section Chap04
section Section22

/-- Theorem 22.6: Let `L` be a subspace of `ℝ^N`, and let `I₁, ..., I_N` be nonempty real
intervals. Then exactly one of the following holds: (a) there exists `z ∈ L` with `z_j ∈ I_j`
for every `j`; (b) there exists `z⋆ ∈ Lᗮ` such that `ζ₁⋆ I₁ + ··· + ζ_N⋆ I_N > 0`, encoded here
as strict positivity of `dotProduct z⋆ z` for every choice `z_j ∈ I_j`. If (b) holds, `z⋆` may
be chosen to be an elementary vector of `Lᗮ`. -/
theorem subspace_interval_alternative_with_elementary_orthogonal_separator
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) (I : Fin N → Set ℝ)
    (hI_interval : ∀ j, Set.OrdConnected (I j))
    (hI_nonempty : ∀ j, (I j).Nonempty) :
    (((∃ z : Fin N → ℝ, z ∈ L ∧ ∀ j, z j ∈ I j) ∨
        ∃ zStar : Fin N → ℝ,
          zStar ∈ dotProductOrthogonalComplement L ∧ PositivelySeparatesIntervalFamily I zStar) ∧
      ¬((∃ z : Fin N → ℝ, z ∈ L ∧ ∀ j, z j ∈ I j) ∧
        ∃ zStar : Fin N → ℝ,
          zStar ∈ dotProductOrthogonalComplement L ∧ PositivelySeparatesIntervalFamily I zStar) ∧
      ((∃ zStar : Fin N → ℝ,
          zStar ∈ dotProductOrthogonalComplement L ∧ PositivelySeparatesIntervalFamily I zStar) →
        ∃ zStar : Fin N → ℝ,
          zStar ∈ dotProductOrthogonalComplement L ∧
            IsElementaryVector (dotProductOrthogonalComplement L) zStar ∧
            PositivelySeparatesIntervalFamily I zStar)) := by
  -- Route correction: package the box geometry and support minimization separately, so the main
  -- theorem only glues together the infeasibility separator and the elementary upgrade.
  refine ⟨?_, ?_, ?_⟩
  · -- Split on primal feasibility; the infeasible branch is delegated to the direct separator
    -- helper for the interval box.
    by_cases hPrimal : ∃ z : Fin N → ℝ, z ∈ L ∧ ∀ j, z j ∈ I j
    · exact Or.inl hPrimal
    · right
      exact helperForTheorem_22_6_infeasible_interval_box_yields_orthogonal_separator
        (L := L) (I := I) hI_interval hI_nonempty hPrimal
  · rintro ⟨⟨z, hzL, hzI⟩, zStar, hzStarOrth, hSep⟩
    -- The dedicated helper converts orthogonality and positive separation into a contradiction.
    exact helperForTheorem_22_6_orthogonal_separator_excludes_primal
      (L := L) (I := I) hzL hzStarOrth hzI hSep
  · intro hSepExists
    by_contra hNoElemExists
    have hNoElemSep :
        ∀ zStar : Fin N → ℝ,
          zStar ∈ dotProductOrthogonalComplement L →
          IsElementaryVector (dotProductOrthogonalComplement L) zStar →
          ¬ PositivelySeparatesIntervalFamily I zStar := by
      intro zStar hzStarOrth hzStarElem hSep
      exact hNoElemExists ⟨zStar, hzStarOrth, hzStarElem, hSep⟩
    rcases helperForTheorem_22_6_primal_of_no_elementary_separator
        (L := L) (I := I) hI_interval hI_nonempty hNoElemSep with
      ⟨z, hzL, hzI⟩
    rcases hSepExists with ⟨zStar, hzStarOrth, hSep⟩
    exact
      helperForTheorem_22_6_orthogonal_separator_excludes_primal
        (L := L) (I := I) hzL hzStarOrth hzI hSep

/-- Two vectors in `ℝ^N` form a Tucker complementarity pair if they are both nonnegative and,
for each coordinate, exactly one of them is strictly positive while the other is zero. -/
def IsTuckerComplementarityPair {N : ℕ} (z zStar : Fin N → ℝ) : Prop :=
  0 ≤ z ∧ 0 ≤ zStar ∧
    ∀ i, (0 < z i ∧ zStar i = 0) ∨ (z i = 0 ∧ 0 < zStar i)

/-- Helper for Theorem 22.7: every nonnegative vector in `L` has support cardinality at most
`N`, so one can choose a nonnegative vector of `L` with maximal support size. -/
lemma helperForTheorem_22_7_exists_support_card_maximal_nonnegative_vector
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) :
    ∃ z : Fin N → ℝ, z ∈ L ∧ 0 ≤ z ∧
      ∀ w : Fin N → ℝ, w ∈ L → 0 ≤ w →
        (vectorSupport w).ncard ≤ (vectorSupport z).ncard := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ z : Fin N → ℝ, z ∈ L ∧ 0 ≤ z ∧ (vectorSupport z).ncard = n
  have hP0 : P 0 := by
    -- The zero vector provides a nonnegative witness, so the maximizing predicate is nonempty.
    refine ⟨0, L.zero_mem, ?_, ?_⟩
    · intro i
      simp
    · simp [P, vectorSupport]
  let m : ℕ := Nat.findGreatest P N
  have hmP : P m := by
    -- `findGreatest` returns an actually realized support size because `0` is realized.
    exact Nat.findGreatest_spec (show 0 ≤ N by exact Nat.zero_le _) hP0
  rcases hmP with ⟨z, hzL, hzNonneg, hzCard⟩
  refine ⟨z, hzL, hzNonneg, ?_⟩
  intro w hwL hwNonneg
  have hwLeN : (vectorSupport w).ncard ≤ N := by
    -- The support sits inside `Fin N`, so its finite cardinality is bounded by `N`.
    have hsubset : vectorSupport w ⊆ (Set.univ : Set (Fin N)) := by
      intro i hi
      simp
    simpa using Set.ncard_le_ncard hsubset
  have hwP : P (vectorSupport w).ncard := by
    exact ⟨w, hwL, hwNonneg, rfl⟩
  have hwLeM : (vectorSupport w).ncard ≤ m := Nat.le_findGreatest hwLeN hwP
  simpa [m, hzCard] using hwLeM

/-- Helper for Theorem 22.7: a positive separator for the support-pinned interval family is
coordinatewise nonnegative off the pinned support and strictly positive somewhere there. -/
lemma helperForTheorem_22_7_pinned_interval_separator_sign
    {N : ℕ} {S : Set (Fin N)} [DecidablePred fun i => i ∈ S] {y : Fin N → ℝ}
    (hSep :
      PositivelySeparatesIntervalFamily
        (fun i => if i ∈ S then ({0} : Set ℝ) else Set.Ioi (0 : ℝ)) y) :
    (∀ i, i ∉ S → 0 ≤ y i) ∧ ∃ j, j ∉ S ∧ 0 < y j := by
  classical
  have hOffNonneg : ∀ i, i ∉ S → 0 ≤ y i := by
    intro i hiS
    by_contra hyiNeg
    let c : ℝ :=
      Finset.sum (Finset.univ.erase i) (fun k : Fin N => y k * (if k ∈ S then 0 else 1))
    let t : ℝ := (|c| + 1) / (-y i)
    let w : Fin N → ℝ := fun k => if k ∈ S then 0 else if k = i then t else 1
    have hyiNeg' : y i < 0 := lt_of_not_ge hyiNeg
    have hyiPos : 0 < -y i := by linarith
    have htiPos : 0 < t := by
      -- The chosen scale is positive because the denominator is `-y i > 0`.
      have hnumPos : 0 < |c| + 1 := by nlinarith [abs_nonneg c]
      exact div_pos hnumPos hyiPos
    have hwMem :
        ∀ k, w k ∈ (if k ∈ S then ({0} : Set ℝ) else Set.Ioi (0 : ℝ)) := by
      intro k
      by_cases hkS : k ∈ S
      · simp [w, hkS]
      · by_cases hk : k = i
        · subst hk
          simp [w, hiS, htiPos]
        · simp [w, hkS, hk]
    have hDotEq : dotProduct y w = c + y i * t := by
      -- Split off the distinguished `i`-coordinate and rewrite the remaining coordinates using
      -- that `w` matches the simple off-support `0/1` pattern there.
      calc
        dotProduct y w = Finset.sum Finset.univ (fun k : Fin N => y k * w k) := by rfl
        _ = Finset.sum (Finset.univ.erase i) (fun k : Fin N => y k * w k) + y i * w i := by
              symm
              exact Finset.sum_erase_add (s := Finset.univ) (a := i)
                (f := fun k : Fin N => y k * w k) (by simp)
        _ = c + y i * t := by
              congr 1
              · unfold c
                refine Finset.sum_congr rfl ?_
                intro k hk
                have hki : k ≠ i := (Finset.mem_erase.mp hk).1
                by_cases hkS : k ∈ S
                · simp [w, hkS]
                · simp [w, hkS, hki]
              · simp [w, hiS, t]
    have hyiMul : y i * t = -(|c| + 1) := by
      have hyiNe : y i ≠ 0 := by linarith
      unfold t
      calc
        y i * ((|c| + 1) / (-y i))
            = y i * ((|c| + 1) * (-y i)⁻¹) := by rw [div_eq_mul_inv]
        _ = -((|c| + 1) * (y i * (y i)⁻¹)) := by ring
        _ = -((|c| + 1) * 1) := by rw [mul_inv_cancel₀ hyiNe]
        _ = -(|c| + 1) := by ring
    have hDotNeg : dotProduct y w < 0 := by
      rw [hDotEq, hyiMul]
      have hcle : c ≤ |c| := le_abs_self c
      linarith
    have hDotPos : 0 < dotProduct y w := hSep w hwMem
    linarith
  refine ⟨hOffNonneg, ?_⟩
  by_contra hNoPos
  push_neg at hNoPos
  let w : Fin N → ℝ := fun k => if k ∈ S then 0 else 1
  have hwMem :
      ∀ k, w k ∈ (if k ∈ S then ({0} : Set ℝ) else Set.Ioi (0 : ℝ)) := by
    intro k
    by_cases hkS : k ∈ S
    · simp [w, hkS]
    · simp [w, hkS]
  have hyOffZero : ∀ k, k ∉ S → y k = 0 := by
    intro k hkS
    have hnonneg : 0 ≤ y k := hOffNonneg k hkS
    have hnonpos : y k ≤ 0 := hNoPos k hkS
    linarith
  have hDotZero : dotProduct y w = 0 := by
    rw [dotProduct]
    refine Finset.sum_eq_zero ?_
    intro k hk
    by_cases hkS : k ∈ S
    · simp [w, hkS]
    · have hyk : y k = 0 := hyOffZero k hkS
      simp [w, hkS, hyk]
  have hDotPos : 0 < dotProduct y w := hSep w hwMem
  exact (hDotPos.ne' hDotZero).elim

/-- Helper for Theorem 22.7: one can choose a small positive perturbation size so that every old
support coordinate stays strictly positive after perturbing by `u`. -/
lemma helperForTheorem_22_7_support_coordinates_stay_positive_under_small_perturbation
    {N : ℕ} {z u : Fin N → ℝ}
    (hzNonneg : 0 ≤ z) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i, i ∈ vectorSupport z → 0 < z i + ε * u i := by
  classical
  let bad : Finset (Fin N) := Finset.univ.filter fun i => i ∈ vectorSupport z ∧ u i < 0
  by_cases hbad : bad.Nonempty
  · let ratio : Fin N → ℝ := fun i => z i / (-u i)
    let ratios : Finset ℝ := bad.image ratio
    have hRatiosNonempty : ratios.Nonempty := hbad.image ratio
    let ε : ℝ := ratios.min' hRatiosNonempty / 2
    have hεpos : 0 < ε := by
      -- The minimum ratio is positive because every bad support coordinate has `z i > 0` and
      -- `-u i > 0`.
      have hmem : ratios.min' hRatiosNonempty ∈ ratios := by
        simpa [ratios] using Finset.min'_mem ratios hRatiosNonempty
      rcases Finset.mem_image.1 hmem with ⟨i, hiBad, hiEq⟩
      have hiSupport : i ∈ vectorSupport z := (Finset.mem_filter.mp hiBad).2.1
      have huiNeg : u i < 0 := (Finset.mem_filter.mp hiBad).2.2
      have hziNe : z i ≠ 0 := by simpa [vectorSupport] using hiSupport
      have hziPos : 0 < z i := lt_of_le_of_ne (hzNonneg i) (Ne.symm hziNe)
      have hdenPos : 0 < -u i := by linarith
      have hratioPos : 0 < ratio i := by
        exact div_pos hziPos hdenPos
      simpa [ε, hiEq] using half_pos hratioPos
    refine ⟨ε, hεpos, ?_⟩
    intro i hiSupport
    have hziNe : z i ≠ 0 := by simpa [vectorSupport] using hiSupport
    have hziPos : 0 < z i := lt_of_le_of_ne (hzNonneg i) (Ne.symm hziNe)
    by_cases huiNeg : u i < 0
    · have hiBad : i ∈ bad := by
        exact Finset.mem_filter.mpr ⟨by simp, hiSupport, huiNeg⟩
      have hiMem : ratio i ∈ ratios := Finset.mem_image.mpr ⟨i, hiBad, rfl⟩
      have hminLe : ratios.min' hRatiosNonempty ≤ ratio i := by
        have h :=
          Finset.min'_le (s := ratios) (x := ratio i) hiMem
        have hproof :
            (⟨ratio i, hiMem⟩ : ratios.Nonempty) = hRatiosNonempty :=
          Subsingleton.elim _ _
        simpa [hproof] using h
      have hminPos : 0 < ratios.min' hRatiosNonempty := by
        have hmemMin : ratios.min' hRatiosNonempty ∈ ratios := by
          simpa [ratios] using Finset.min'_mem ratios hRatiosNonempty
        rcases Finset.mem_image.1 hmemMin with ⟨k, hkBad, hkEq⟩
        have hkSupport : k ∈ vectorSupport z := (Finset.mem_filter.mp hkBad).2.1
        have hukNeg : u k < 0 := (Finset.mem_filter.mp hkBad).2.2
        have hzkNe : z k ≠ 0 := by simpa [vectorSupport] using hkSupport
        have hzkPos : 0 < z k := lt_of_le_of_ne (hzNonneg k) (Ne.symm hzkNe)
        have hkDenPos : 0 < -u k := by linarith
        have hkRatioPos : 0 < ratio k := by
          exact div_pos hzkPos hkDenPos
        simpa [hkEq] using hkRatioPos
      have hεlt : ε < ratio i := by
        have hhalfLt : ratios.min' hRatiosNonempty / 2 < ratios.min' hRatiosNonempty := by
          nlinarith
        exact lt_of_lt_of_le (by simpa [ε] using hhalfLt) hminLe
      have hdenPos : 0 < -u i := by linarith
      have hbound : ε * (-u i) < z i := by
        exact (lt_div_iff₀ hdenPos).mp hεlt
      have hRewrite : z i + ε * u i = z i - ε * (-u i) := by ring
      rw [hRewrite]
      linarith
    · have huiNonneg : 0 ≤ u i := le_of_not_gt huiNeg
      nlinarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro i hiSupport
    have hziNe : z i ≠ 0 := by simpa [vectorSupport] using hiSupport
    have hziPos : 0 < z i := lt_of_le_of_ne (hzNonneg i) (Ne.symm hziNe)
    have huiNonneg : 0 ≤ u i := by
      by_contra huiNeg
      have hiBad : i ∈ bad := by
        exact Finset.mem_filter.mpr ⟨by simp, hiSupport, lt_of_not_ge huiNeg⟩
      exact hbad ⟨i, hiBad⟩
    nlinarith

/-- Helper for Theorem 22.7: a sufficiently small positive perturbation preserves nonnegativity on
the old support and turns one new off-support positive coordinate on. -/
lemma helperForTheorem_22_7_small_positive_perturbation_increases_support
    {N : ℕ} {z u : Fin N → ℝ}
    (hzNonneg : 0 ≤ z)
    (huOffNonneg : ∀ i, i ∉ vectorSupport z → 0 ≤ u i)
    (huOffPos : ∃ j, j ∉ vectorSupport z ∧ 0 < u j) :
    ∃ ε : ℝ, 0 < ε ∧ 0 ≤ z + ε • u ∧
      (vectorSupport z).ncard < (vectorSupport (z + ε • u)).ncard := by
  rcases huOffPos with ⟨j, hjOff, hujPos⟩
  rcases helperForTheorem_22_7_support_coordinates_stay_positive_under_small_perturbation
      (z := z) (u := u) hzNonneg with
    ⟨ε, hεpos, hOldPos⟩
  have hNewNonneg : 0 ≤ z + ε • u := by
    intro i
    by_cases hiSupport : i ∈ vectorSupport z
    · exact le_of_lt (hOldPos i hiSupport)
    · have hziZero : z i = 0 := by simpa [vectorSupport] using hiSupport
      have huiNonneg : 0 ≤ u i := huOffNonneg i hiSupport
      simpa [Pi.smul_apply, hziZero] using mul_nonneg (le_of_lt hεpos) huiNonneg
  refine ⟨ε, hεpos, hNewNonneg, ?_⟩
  have hSupportSubset : vectorSupport z ⊆ vectorSupport (z + ε • u) := by
    intro i hiSupport
    have hpos : 0 < (z + ε • u) i := by
      simpa [Pi.smul_apply] using hOldPos i hiSupport
    simpa [vectorSupport] using (ne_of_gt hpos)
  have hjNew : j ∈ vectorSupport (z + ε • u) := by
    have hzjZero : z j = 0 := by simpa [vectorSupport] using hjOff
    have hpos : 0 < (z + ε • u) j := by
      simpa [Pi.smul_apply, hzjZero, smul_eq_mul] using mul_pos hεpos hujPos
    simpa [vectorSupport] using (ne_of_gt hpos)
  have hStrictSubset : vectorSupport z ⊂ vectorSupport (z + ε • u) := by
    refine ⟨hSupportSubset, ?_⟩
    intro hReverse
    exact hjOff (hReverse hjNew)
  exact Set.ncard_lt_ncard hStrictSubset

/-- Helper for Theorem 22.7: a support-maximal nonnegative vector in `L` admits a complementary
nonnegative partner in `Lᗮ`. -/
lemma helperForTheorem_22_7_support_card_maximal_vector_has_dual_partner
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) {z : Fin N → ℝ}
    (hzL : z ∈ L) (hzNonneg : 0 ≤ z)
    (hzMax :
      ∀ w : Fin N → ℝ, w ∈ L → 0 ≤ w →
        (vectorSupport w).ncard ≤ (vectorSupport z).ncard) :
    ∃ zStar : Fin N → ℝ,
      zStar ∈ dotProductOrthogonalComplement L ∧
        IsTuckerComplementarityPair z zStar := by
  classical
  -- Route correction: the separator branch must be turned into a larger-support nonnegative
  -- vector in `L`, so we work over the pinned family for `(L ⊔ U)ᗮ`.
  let S : Set (Fin N) := vectorSupport z
  let U : Submodule ℝ (Fin N → ℝ) :=
    { carrier := {u : Fin N → ℝ | ∀ i, i ∉ S → u i = 0}
      zero_mem' := by
        intro i hiS
        simp
      add_mem' := by
        intro u v hu hv i hiS
        simp [hu i hiS, hv i hiS]
      smul_mem' := by
        intro c u hu i hiS
        simp [hu i hiS] }
  let M : Submodule ℝ (Fin N → ℝ) := dotProductOrthogonalComplement (L ⊔ U)
  let I : Fin N → Set ℝ := fun i => if i ∈ S then ({0} : Set ℝ) else Set.Ioi (0 : ℝ)
  have hI_interval : ∀ i, Set.OrdConnected (I i) := by
    intro i
    by_cases hiS : i ∈ S
    · simpa [I, hiS] using (Set.ordConnected_singleton : Set.OrdConnected ({0} : Set ℝ))
    · simpa [I, hiS] using (Set.ordConnected_Ioi (a := (0 : ℝ)))
  have hI_nonempty : ∀ i, (I i).Nonempty := by
    intro i
    by_cases hiS : i ∈ S
    · exact ⟨0, by simp [I, hiS]⟩
    · exact ⟨1, by simp [I, hiS]⟩
  have hAlt :
      (∃ zStar : Fin N → ℝ, zStar ∈ M ∧ ∀ i, zStar i ∈ I i) ∨
        ∃ y : Fin N → ℝ,
          y ∈ dotProductOrthogonalComplement M ∧
            PositivelySeparatesIntervalFamily I y :=
    (subspace_interval_alternative_with_elementary_orthogonal_separator
      M I hI_interval hI_nonempty).1
  rcases hAlt with hPrimal | hSepExists
  · rcases hPrimal with ⟨zStar, hzStarM, hzStarI⟩
    have hzStarOrth : zStar ∈ dotProductOrthogonalComplement L := by
      -- Membership in `(L ⊔ U)ᗮ` implies orthogonality to `L` by restricting the test vectors.
      change zStar ∈ dotProductOrthogonalComplement (L ⊔ U) at hzStarM
      rw [dotProductOrthogonalComplement, Submodule.mem_iInf] at hzStarM ⊢
      intro x
      have hxSup : (x : Fin N → ℝ) ∈ L ⊔ U := by
        exact Submodule.mem_sup.mpr ⟨(x : Fin N → ℝ), x.2, 0, U.zero_mem, by simp⟩
      simpa [LinearMap.mem_ker] using hzStarM ⟨(x : Fin N → ℝ), hxSup⟩
    have hzStarNonneg : 0 ≤ zStar := by
      intro i
      by_cases hiS : i ∈ S
      · have hzStarZero : zStar i = 0 := by
          simpa [I, hiS] using hzStarI i
        simp [hzStarZero]
      · have hzStarPos : 0 < zStar i := by
          simpa [I, hiS] using hzStarI i
        exact le_of_lt hzStarPos
    refine ⟨zStar, hzStarOrth, hzNonneg, hzStarNonneg, ?_⟩
    intro i
    by_cases hiS : i ∈ S
    · have hziNe : z i ≠ 0 := by simpa [S, vectorSupport] using hiS
      have hziPos : 0 < z i := lt_of_le_of_ne (hzNonneg i) (Ne.symm hziNe)
      have hzStarZero : zStar i = 0 := by simpa [I, hiS] using hzStarI i
      exact Or.inl ⟨hziPos, hzStarZero⟩
    · have hziZero : z i = 0 := by simpa [S, vectorSupport] using hiS
      have hzStarPos : 0 < zStar i := by simpa [I, hiS] using hzStarI i
      exact Or.inr ⟨hziZero, hzStarPos⟩
  · rcases hSepExists with ⟨y, hyOrthM, hSep⟩
    have hDouble :
        dotProductOrthogonalComplement (dotProductOrthogonalComplement (L ⊔ U)) = L ⊔ U := by
      rw [helperForTheorem_22_6_dotProductOrthogonalComplement_eq_bilinOrthogonal,
        helperForTheorem_22_6_dotProductOrthogonalComplement_eq_bilinOrthogonal]
      simpa using
        LinearMap.BilinForm.orthogonal_orthogonal
          (V := Fin N → ℝ) (K := ℝ)
          (B := dotProductBilin (R := ℝ) (S := ℝ) (A := ℝ) (m := Fin N))
          (helperForTheorem_22_6_dotProductBilin_nondegenerate (N := N))
          (helperForTheorem_22_6_dotProductBilin_isRefl (N := N))
          (L ⊔ U)
    have hySup : y ∈ L ⊔ U := by
      change y ∈ dotProductOrthogonalComplement (dotProductOrthogonalComplement (L ⊔ U)) at hyOrthM
      simpa [hDouble] using hyOrthM
    rcases Submodule.mem_sup.mp hySup with ⟨uL, huLL, uU, huUU, hyEq⟩
    rcases helperForTheorem_22_7_pinned_interval_separator_sign hSep with
      ⟨hyOffNonneg, ⟨j, hjOff, hyjPos⟩⟩
    have huLOffNonneg : ∀ i, i ∉ vectorSupport z → 0 ≤ uL i := by
      intro i hiOff
      have huUiZero : uU i = 0 := huUU i (by simpa [S] using hiOff)
      have hyiEq : y i = uL i := by
        have hCoord : y i = uL i + uU i := by
          simpa using (congrArg (fun w => w i) hyEq).symm
        simpa [huUiZero] using hCoord
      have hyiNonneg : 0 ≤ y i := hyOffNonneg i (by simpa [S] using hiOff)
      simpa [hyiEq] using hyiNonneg
    have huLOffPos : ∃ j, j ∉ vectorSupport z ∧ 0 < uL j := by
      refine ⟨j, by simpa [S] using hjOff, ?_⟩
      have huUjZero : uU j = 0 := huUU j hjOff
      have hyjEq : y j = uL j := by
        have hCoord : y j = uL j + uU j := by
          simpa using (congrArg (fun w => w j) hyEq).symm
        simpa [huUjZero] using hCoord
      simpa [hyjEq] using hyjPos
    rcases helperForTheorem_22_7_small_positive_perturbation_increases_support
        (z := z) (u := uL) hzNonneg huLOffNonneg huLOffPos with
      ⟨ε, hεpos, hPertNonneg, hCardLt⟩
    have hPertMem : z + ε • uL ∈ L := by
      exact L.add_mem hzL (L.smul_mem ε huLL)
    have hCardLe :
        (vectorSupport (z + ε • uL)).ncard ≤ (vectorSupport z).ncard :=
      hzMax (z + ε • uL) hPertMem hPertNonneg
    exfalso
    exact (lt_irrefl (vectorSupport z).ncard) (lt_of_lt_of_le hCardLt hCardLe)

/-- Helper for Theorem 22.7: in a zero dot product of coordinatewise nonnegative vectors, any
strictly positive coordinate on one side forces the corresponding coordinate on the other side
to vanish. -/
lemma helperForTheorem_22_7_zero_coordinate_of_positive_partner
    {N : ℕ} {x y : Fin N → ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hdot : dotProduct y x = 0)
    {i : Fin N} (hyi : 0 < y i) :
    x i = 0 := by
  have hTermsNonneg : ∀ j ∈ Finset.univ, 0 ≤ y j * x j := by
    intro j hj
    exact mul_nonneg (hy j) (hx j)
  have hZeroSum : ∑ j, y j * x j = 0 := by
    simpa [dotProduct] using hdot
  have hTermZero :
      y i * x i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hTermsNonneg).1 hZeroSum i (by simp)
  exact (mul_eq_zero.mp hTermZero).resolve_left hyi.ne'

/-- Helper for Theorem 22.7: in a Tucker pair, the support of the dual vector is exactly the
complement of the primal support. -/
lemma helperForTheorem_22_7_dual_support_eq_compl
    {N : ℕ} {z zStar : Fin N → ℝ}
    (hPair : IsTuckerComplementarityPair z zStar) :
    vectorSupport zStar = (vectorSupport z)ᶜ := by
  ext i
  constructor
  · intro hi
    have hzStarNe : zStar i ≠ 0 := by
      simpa [vectorSupport] using hi
    rcases hPair.2.2 i with h | h
    · exact False.elim (hzStarNe h.2)
    · simpa [vectorSupport, h.1]
  · intro hi
    have hzi0 : z i = 0 := by
      simpa [vectorSupport] using hi
    rcases hPair.2.2 i with h | h
    · exact False.elim (h.1.ne' hzi0)
    · simpa [vectorSupport] using h.2.ne'

/-- Helper for Theorem 22.7: any two Tucker pairs for the same subspace have the same primal and
dual supports. -/
lemma helperForTheorem_22_7_unique_supports_of_tucker_pairs
    {N : ℕ} {L : Submodule ℝ (Fin N → ℝ)}
    {z zStar z' zStar' : Fin N → ℝ}
    (hzL : z ∈ L) (hzStarOrth : zStar ∈ dotProductOrthogonalComplement L)
    (hPair : IsTuckerComplementarityPair z zStar)
    (hzL' : z' ∈ L) (hzStarOrth' : zStar' ∈ dotProductOrthogonalComplement L)
    (hPair' : IsTuckerComplementarityPair z' zStar') :
    vectorSupport z' = vectorSupport z ∧
      vectorSupport zStar' = vectorSupport zStar := by
  have hzNonneg : 0 ≤ z := hPair.1
  have hzStarNonneg : 0 ≤ zStar := hPair.2.1
  have hzNonneg' : 0 ≤ z' := hPair'.1
  have hzStarNonneg' : 0 ≤ zStar' := hPair'.2.1
  have hdotLeft : dotProduct zStar' z = 0 := by
    have hdot : dotProduct z zStar' = 0 := by
      rw [dotProductOrthogonalComplement, Submodule.mem_iInf] at hzStarOrth'
      simpa [LinearMap.mem_ker] using hzStarOrth' ⟨z, hzL⟩
    simpa [dotProduct_comm] using hdot
  have hdotRight : dotProduct zStar z' = 0 := by
    have hdot : dotProduct z' zStar = 0 := by
      rw [dotProductOrthogonalComplement, Submodule.mem_iInf] at hzStarOrth
      simpa [LinearMap.mem_ker] using hzStarOrth ⟨z', hzL'⟩
    simpa [dotProduct_comm] using hdot
  have hSubset : vectorSupport z ⊆ vectorSupport z' := by
    intro i hi
    have hziNe : z i ≠ 0 := by
      simpa [vectorSupport] using hi
    by_contra hi'
    have hz'i0 : z' i = 0 := by
      simpa [vectorSupport] using hi'
    have hzStar'iPos : 0 < zStar' i := by
      rcases hPair'.2.2 i with h | h
      · exact False.elim (h.1.ne' hz'i0)
      · exact h.2
    have hzi0 :
        z i = 0 :=
      helperForTheorem_22_7_zero_coordinate_of_positive_partner
        hzNonneg hzStarNonneg' hdotLeft hzStar'iPos
    exact hziNe hzi0
  have hSubset' : vectorSupport z' ⊆ vectorSupport z := by
    intro i hi
    have hz'iNe : z' i ≠ 0 := by
      simpa [vectorSupport] using hi
    by_contra hi'
    have hzi0 : z i = 0 := by
      simpa [vectorSupport] using hi'
    have hzStariPos : 0 < zStar i := by
      rcases hPair.2.2 i with h | h
      · exact False.elim (h.1.ne' hzi0)
      · exact h.2
    have hz'i0 :
        z' i = 0 :=
      helperForTheorem_22_7_zero_coordinate_of_positive_partner
        hzNonneg' hzStarNonneg hdotRight hzStariPos
    exact hz'iNe hz'i0
  have hSupportEq : vectorSupport z' = vectorSupport z :=
    Set.Subset.antisymm hSubset' hSubset
  refine ⟨hSupportEq, ?_⟩
  calc
    vectorSupport zStar' = (vectorSupport z')ᶜ := helperForTheorem_22_7_dual_support_eq_compl hPair'
    _ = (vectorSupport z)ᶜ := by rw [hSupportEq]
    _ = vectorSupport zStar := (helperForTheorem_22_7_dual_support_eq_compl hPair).symm

-- Proof sketch: apply the interval alternative of Theorem 22.6 to the nonnegative orthant.
-- The separating elementary vector in `Lᗮ` yields one side of the complementary pair, while
-- orthogonality and the elementary-vector support theory force the associated supports to be
-- complementary and independent of the particular realizing vectors.
/-- Theorem 22.7: Tucker's Complementarity Theorem. For any subspace `L ⊆ ℝ^N`, there exist
nonnegative vectors `z ∈ L` and `z⋆ ∈ Lᗮ` such that for each index `i`, either `z i > 0` and
`z⋆ i = 0`, or `z i = 0` and `z⋆ i > 0`. Moreover, the supports of `z` and `z⋆` are uniquely
determined by `L`, even though the vectors themselves need not be unique. -/
theorem tuckerComplementarity_exists_pair_with_unique_supports
    {N : ℕ} (L : Submodule ℝ (Fin N → ℝ)) :
    ∃ z zStar : Fin N → ℝ,
      z ∈ L ∧
      zStar ∈ dotProductOrthogonalComplement L ∧
      IsTuckerComplementarityPair z zStar ∧
      ∀ z' zStar' : Fin N → ℝ,
        z' ∈ L →
        zStar' ∈ dotProductOrthogonalComplement L →
        IsTuckerComplementarityPair z' zStar' →
        vectorSupport z' = vectorSupport z ∧
          vectorSupport zStar' = vectorSupport zStar := by
  classical
  -- Route correction: work with a nonnegative vector of maximal support, then apply Theorem 22.6
  -- to the support-pinned orthogonal complement to produce the dual partner.
  rcases helperForTheorem_22_7_exists_support_card_maximal_nonnegative_vector L with
    ⟨z, hzL, hzNonneg, hzMax⟩
  rcases helperForTheorem_22_7_support_card_maximal_vector_has_dual_partner
      (L := L) hzL hzNonneg hzMax with
    ⟨zStar, hzStarOrth, hPair⟩
  refine ⟨z, zStar, hzL, hzStarOrth, hPair, ?_⟩
  intro z' zStar' hzL' hzStarOrth' hPair'
  -- The dedicated uniqueness lemma packages the zero-dot-product support comparison.
  exact helperForTheorem_22_7_unique_supports_of_tucker_pairs
    hzL hzStarOrth hPair hzL' hzStarOrth' hPair'


end Section22
end Chap04
