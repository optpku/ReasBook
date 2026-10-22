/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section22_part2

open scoped BigOperators Pointwise

section Chap04
section Section22

/-- Helper for Text 22.3.5: the forward inequality together with the negated reverse
inequality forces equality. -/
lemma helperForText_22_3_5_eq_from_two_augmented_inequalities
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ)
    {i : Fin m} {x : Fin n → ℝ}
    (hle : dotProduct (a i) x ≤ α i)
    (hneg : dotProduct (-a i) x ≤ -α i) :
    dotProduct (a i) x = α i := by
  -- Combine the original inequality with the negated reverse inequality.
  refine (helperForText_21_0_4_eq_iff_le_and_neg_le_neg (dotProduct (a i) x) (α i)).2 ?_
  constructor
  · exact hle
  · simpa [dotProduct] using hneg

/-- Helper for Text 22.3.5: the augmented weak system obtained by duplicating equality
constraints as `a_i ≤ α_i` and `-a_i ≤ -α_i` is feasible exactly when the original mixed
system is feasible. -/
lemma helperForText_22_3_5_augmentedPrimal_iff_feasible
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ) (E : Set (Fin m))
    [DecidablePred fun i : Fin m => i ∈ E] :
    let aAug : Fin (m + m) → (Fin n → ℝ) :=
      Fin.append a (fun i => if i ∈ E then -a i else 0)
    let αAug : Fin (m + m) → ℝ :=
      Fin.append α (fun i => if i ∈ E then -α i else 0)
    (∃ x : Fin n → ℝ, ∀ j : Fin (m + m), dotProduct (aAug j) x ≤ αAug j) ↔
      ∃ x : Fin n → ℝ,
        (∀ i : Fin m, i ∉ E → dotProduct (a i) x ≤ α i) ∧
          ∀ i : Fin m, i ∈ E → dotProduct (a i) x = α i := by
  dsimp
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_, ?_⟩
    · intro i hi
      -- The first augmented block is exactly the original weak system.
      simpa using hx (Fin.castAdd m i)
    · intro i hi
      -- On equality indices, the second augmented block supplies the reverse inequality.
      have hle : dotProduct (a i) x ≤ α i := by
        simpa using hx (Fin.castAdd m i)
      have hrev : α i ≤ dotProduct (a i) x := by
        have hsecond := hx (Fin.natAdd m i)
        rw [Fin.append_right, Fin.append_right] at hsecond
        have hsecond' : dotProduct (-a i) x ≤ -α i := by
          simpa [hi] using hsecond
        have hneg' : -dotProduct (a i) x ≤ -α i := by
          simpa [dotProduct] using hsecond'
        linarith
      have hneg : dotProduct (-a i) x ≤ -α i := by
        have hneg' : -dotProduct (a i) x ≤ -α i := by
          linarith
        simpa [dotProduct] using hneg'
      exact
        helperForText_22_3_5_eq_from_two_augmented_inequalities
          a α hle hneg
  · rintro ⟨x, hxI, hxE⟩
    refine ⟨x, ?_⟩
    intro j
    refine Fin.addCases ?_ ?_ j
    · intro i
      -- The original inequalities come either from the inequality side or from equality.
      by_cases hi : i ∈ E
      · rw [Fin.append_left, Fin.append_left]
        exact le_of_eq (hxE i hi)
      · rw [Fin.append_left, Fin.append_left]
        exact hxI i hi
    · intro i
      -- The duplicated equality block is either the negated equality or a dummy zero row.
      by_cases hi : i ∈ E
      · have hEq : dotProduct (-a i) x = -α i := by
          simpa [dotProduct] using congrArg Neg.neg (hxE i hi)
        rw [Fin.append_right, Fin.append_right]
        simpa [hi] using le_of_eq hEq
      · have hzero : dotProduct (0 : Fin n → ℝ) x ≤ (0 : ℝ) := by
          simp
        rw [Fin.append_right, Fin.append_right]
        simpa [hi] using hzero

/-- Helper for Text 22.3.5: a nonnegative certificate for the augmented pure-inequality
system induces the mixed-sign certificate for the original equality/inequality system. -/
lemma helperForText_22_3_5_augmentedCertificate_to_mixedCertificate
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ) (E : Set (Fin m))
    [DecidablePred fun i : Fin m => i ∈ E] :
    let aAug : Fin (m + m) → (Fin n → ℝ) :=
      Fin.append a (fun i => if i ∈ E then -a i else 0)
    let αAug : Fin (m + m) → ℝ :=
      Fin.append α (fun i => if i ∈ E then -α i else 0)
    ∀ μ : Fin (m + m) → ℝ,
      0 ≤ μ →
      (∑ j : Fin (m + m), μ j • aAug j) = 0 →
      (∑ j : Fin (m + m), μ j * αAug j) < 0 →
      ∃ l : Fin m → ℝ,
        (∀ i : Fin m, i ∉ E → 0 ≤ l i) ∧
          (∑ i, l i • a i) = 0 ∧
            (∑ i, l i * α i) < 0 := by
  dsimp
  intro μ hμ_nonneg hsum_zero hscalar_neg
  let l : Fin m → ℝ := fun i =>
    if i ∈ E then μ (Fin.castAdd m i) - μ (Fin.natAdd m i) else μ (Fin.castAdd m i)
  refine ⟨l, ?_, ?_, ?_⟩
  · intro i hi
    -- Away from the equality set, the mixed certificate keeps the original nonnegative
    -- coefficient from the first augmented block.
    simpa [l, hi] using hμ_nonneg (Fin.castAdd m i)
  · -- Compare the summed normals coordinatewise after splitting the augmented sum into blocks.
    ext j0
    have hcoord :
        ∑ j : Fin (m + m), μ j * Fin.append a (fun i => if i ∈ E then -a i else 0) j j0 = 0 := by
      have hcoord' := congrArg (fun v : Fin n → ℝ => v j0) hsum_zero
      simpa [smul_eq_mul] using hcoord'
    have hright :
        ∑ i : Fin m,
            μ (Fin.natAdd m i) *
              Fin.append a (fun i => if i ∈ E then -a i else 0) (Fin.natAdd m i) j0 =
          ∑ i : Fin m, if i ∈ E then -(μ (Fin.natAdd m i) * a i j0) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hEi : i ∈ E
      · rw [Fin.append_right]
        have hterm :
            μ (Fin.natAdd m i) * (-a i j0) =
              (if i ∈ E then -(μ (Fin.natAdd m i) * a i j0) else 0) := by
          simp [hEi]
        simpa [hEi] using hterm
      · rw [Fin.append_right]
        simp [hEi]
    have hcoord' :
        (∑ i : Fin m, μ (Fin.castAdd m i) * a i j0) +
            (∑ i : Fin m, if i ∈ E then -(μ (Fin.natAdd m i) * a i j0) else 0) = 0 := by
      rw [Fin.sum_univ_add] at hcoord
      rw [hright] at hcoord
      simpa [Fin.append] using hcoord
    have hlrewrite :
        ∑ i : Fin m, l i * a i j0 =
          (∑ i : Fin m, μ (Fin.castAdd m i) * a i j0) +
            (∑ i : Fin m, if i ∈ E then -(μ (Fin.natAdd m i) * a i j0) else 0) := by
      calc
        ∑ i : Fin m, l i * a i j0
            = ∑ i : Fin m,
                (μ (Fin.castAdd m i) * a i j0 +
                  if i ∈ E then -(μ (Fin.natAdd m i) * a i j0) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                by_cases hEi : i ∈ E
                · simp [l, hEi]
                  ring_nf
                · simp [l, hEi]
        _ = (∑ i : Fin m, μ (Fin.castAdd m i) * a i j0) +
              (∑ i : Fin m, if i ∈ E then -(μ (Fin.natAdd m i) * a i j0) else 0) := by
              rw [Finset.sum_add_distrib]
    have htarget : ∑ i : Fin m, l i * a i j0 = 0 := by
      rw [hlrewrite]
      exact hcoord'
    simpa [smul_eq_mul] using htarget
  · -- The same block decomposition turns the augmented scalar inequality into the mixed one.
    have hright :
        ∑ i : Fin m, μ (Fin.natAdd m i) * Fin.append α (fun i => if i ∈ E then -α i else 0) (Fin.natAdd m i) =
          ∑ i : Fin m, if i ∈ E then -(μ (Fin.natAdd m i) * α i) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hEi : i ∈ E
      · rw [Fin.append_right]
        have hterm :
            μ (Fin.natAdd m i) * (-α i) =
              (if i ∈ E then -(μ (Fin.natAdd m i) * α i) else 0) := by
          simp [hEi]
        simpa [hEi] using hterm
      · rw [Fin.append_right]
        simp [hEi]
    have hscalar_split :
        ∑ j : Fin (m + m), μ j * Fin.append α (fun i => if i ∈ E then -α i else 0) j =
          (∑ i : Fin m, μ (Fin.castAdd m i) * α i) +
            (∑ i : Fin m, if i ∈ E then -(μ (Fin.natAdd m i) * α i) else 0) := by
      rw [Fin.sum_univ_add]
      rw [hright]
      simp [Fin.append]
    have hlrewrite :
        ∑ i : Fin m, l i * α i =
          (∑ i : Fin m, μ (Fin.castAdd m i) * α i) +
            (∑ i : Fin m, if i ∈ E then -(μ (Fin.natAdd m i) * α i) else 0) := by
      calc
        ∑ i : Fin m, l i * α i
            = ∑ i : Fin m,
                (μ (Fin.castAdd m i) * α i +
                  if i ∈ E then -(μ (Fin.natAdd m i) * α i) else 0) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                by_cases hEi : i ∈ E
                · simp [l, hEi]
                  ring_nf
                · simp [l, hEi]
        _ = (∑ i : Fin m, μ (Fin.castAdd m i) * α i) +
              (∑ i : Fin m, if i ∈ E then -(μ (Fin.natAdd m i) * α i) else 0) := by
              rw [Finset.sum_add_distrib]
    rw [hlrewrite]
    rw [← hscalar_split]
    exact hscalar_neg

/-- Helper for Text 22.3.5: a feasible point for the mixed system and a mixed-sign
certificate cannot coexist. -/
lemma helperForText_22_3_5_certificate_excludes_feasible
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ) (E : Set (Fin m))
    {x : Fin n → ℝ}
    (hxI : ∀ i : Fin m, i ∉ E → dotProduct (a i) x ≤ α i)
    (hxE : ∀ i : Fin m, i ∈ E → dotProduct (a i) x = α i)
    {l : Fin m → ℝ}
    (hl_nonneg : ∀ i : Fin m, i ∉ E → 0 ≤ l i)
    (hsum_zero : (∑ i, l i • a i) = 0)
    (hscalar_neg : (∑ i, l i * α i) < 0) : False := by
  classical
  -- Multiply each constraint by its coefficient and sum, using equality on `E`.
  have hweighted :
      ∑ i : Fin m, l i * dotProduct (a i) x ≤ ∑ i : Fin m, l i * α i := by
    refine Finset.sum_le_sum ?_
    intro i hi
    by_cases hEi : i ∈ E
    · simpa [hxE i hEi]
    · exact mul_le_mul_of_nonneg_left (hxI i hEi) (hl_nonneg i hEi)
  have hdot_sum :
      ∑ i : Fin m, l i * dotProduct (a i) x = dotProduct (∑ i : Fin m, l i • a i) x := by
    -- The weighted left-hand side is the dot product against the summed normal vector.
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
  have hscalar_nonneg : 0 ≤ ∑ i : Fin m, l i * α i := by
    -- The vanishing normal sum makes the weighted left-hand side equal to zero.
    have hleft_nonneg : 0 ≤ ∑ i : Fin m, l i * dotProduct (a i) x := by
      rw [hdot_sum, hsum_zero]
      simp
    exact le_trans hleft_nonneg hweighted
  linarith

/-- Text 22.3.5: Let `a_i ∈ ℝ^n` and `α_i ∈ ℝ` for `i = 1, ..., m`, and let `E ⊆ {1, ..., m}`
be the subset of indices imposed as equalities. Then exactly one of the following holds:
(a) there exists `x ∈ ℝ^n` such that `⟪a_i, x⟫ ≤ α_i` for every `i ∉ E` and
`⟪a_i, x⟫ = α_i` for every `i ∈ E`; (b) there exist real multipliers `λ_1, ..., λ_m` such
that `λ_i ≥ 0` for every `i ∉ E`, with no sign restriction on `i ∈ E`, and
`∑ i, λ_i a_i = 0` together with `∑ i, λ_i α_i < 0`. -/
theorem farkasAlternative_linearInequalities_withEqualityConstraints
    {m n : ℕ} (a : Fin m → (Fin n → ℝ)) (α : Fin m → ℝ) (E : Set (Fin m)) :
    let feasible :=
      ∃ x : Fin n → ℝ,
        (∀ i : Fin m, i ∉ E → dotProduct (a i) x ≤ α i) ∧
          ∀ i : Fin m, i ∈ E → dotProduct (a i) x = α i
    let certificate :=
      ∃ l : Fin m → ℝ,
        (∀ i : Fin m, i ∉ E → 0 ≤ l i) ∧
          (∑ i, l i • a i) = 0 ∧
            (∑ i, l i * α i) < 0
    (feasible ∨ certificate) ∧ ¬(feasible ∧ certificate) := by
  classical
  dsimp
  let aAug : Fin (m + m) → (Fin n → ℝ) :=
    Fin.append a (fun i => if i ∈ E then -a i else 0)
  let αAug : Fin (m + m) → ℝ :=
    Fin.append α (fun i => if i ∈ E then -α i else 0)
  have hAug :=
    farkasAlternative_linearInequalities aAug αAug
  have hPrimalTransport :
      (∃ x : Fin n → ℝ, ∀ j : Fin (m + m), dotProduct (aAug j) x ≤ αAug j) ↔
        ∃ x : Fin n → ℝ,
          (∀ i : Fin m, i ∉ E → dotProduct (a i) x ≤ α i) ∧
            ∀ i : Fin m, i ∈ E → dotProduct (a i) x = α i := by
    -- Transport the augmented primal feasibility statement back to the mixed one.
    simpa [aAug, αAug] using
      (helperForText_22_3_5_augmentedPrimal_iff_feasible (a := a) (α := α) (E := E))
  have hDualTransport :
      ∀ μ : Fin (m + m) → ℝ,
        0 ≤ μ →
        (∑ j : Fin (m + m), μ j • aAug j) = 0 →
        (∑ j : Fin (m + m), μ j * αAug j) < 0 →
        ∃ l : Fin m → ℝ,
          (∀ i : Fin m, i ∉ E → 0 ≤ l i) ∧
            (∑ i, l i • a i) = 0 ∧
              (∑ i, l i * α i) < 0 := by
    intro μ hμ_nonneg hsum_zero hscalar_neg
    -- Transport the augmented nonnegative certificate by subtracting the equality block.
    simpa [aAug, αAug] using
      (helperForText_22_3_5_augmentedCertificate_to_mixedCertificate
        (a := a) (α := α) (E := E) μ hμ_nonneg hsum_zero hscalar_neg)
  refine ⟨?_, ?_⟩
  · rcases hAug.1 with hPrimal | hDual
    · left
      exact hPrimalTransport.1 hPrimal
    · right
      rcases hDual with ⟨μ, hμ_nonneg, hsum_zero, hscalar_neg⟩
      exact hDualTransport μ hμ_nonneg hsum_zero hscalar_neg
  · intro hBoth
    rcases hBoth with ⟨⟨x, hxI, hxE⟩, ⟨l, hl_nonneg, hsum_zero, hscalar_neg⟩⟩
    -- The weighted-sum contradiction proves that the two alternatives are exclusive.
    exact
      helperForText_22_3_5_certificate_excludes_feasible
        a α E hxI hxE hl_nonneg hsum_zero hscalar_neg

end Section22
end Chap04
