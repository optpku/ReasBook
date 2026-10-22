/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part7

section Chap05
section Section26

attribute [local instance] Classical.propDecidable
open scoped ConvexAnalysis Pointwise

/-- Corollary 26.3.2: if `f₁` and `f₂` are closed proper convex functions on `ℝ^n`, `f₁` is
essentially smooth, and `ri (dom f₁*) ∩ ri (dom f₂*)` is nonempty, then the infimal convolution
`f₁ □ f₂` is essentially smooth. -/
theorem essentiallySmooth_infimalConvolution_of_essentiallySmooth_left_and_commonRelativeInterior_conjugateEffectiveDomain
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hf₁ : ProperConvexERealFunction (F := (Fin n → ℝ)) f₁)
    (hf₁_closed : LowerSemicontinuous f₁)
    (hf₂ : ProperConvexERealFunction (F := (Fin n → ℝ)) f₂)
    (hf₂_closed : LowerSemicontinuous f₂)
    (hf₁_smooth : IsEssentiallySmooth f₁)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₁)) ∩
          euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₂)))) :
    IsEssentiallySmooth (infimalConvolution f₁ f₂) := by
  let gTwo : Fin 2 → (Fin n → ℝ) → EReal :=
    fun i => Fin.cases (fenchelConjugate n f₁) (fun _ => fenchelConjugate n f₂) i
  let g : (Fin n → ℝ) → EReal := fun x => fenchelConjugate n f₁ x + fenchelConjugate n f₂ x
  have hf₁_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₁ :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f₁) hf₁
  have hf₂_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f₂ :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f₂) hf₂
  have hg_essStrict :
      IsEssentiallyStrictlyConvex g :=
    helperForCorollary_26_3_2_essentiallyStrictlyConvex_conjugateSum
      (f₁ := f₁) (f₂ := f₂) hf₁ hf₁_closed hf₂ hf₁_smooth hri
  have hg_proper : ProperConvexERealFunction (F := (Fin n → ℝ)) g :=
    helperForLemma_26_2_properConvexERealFunction hg_essStrict.1
  have hgTwo_closed :
      ∀ i : Fin 2, ClosedConvexFunction (gTwo i) := by
    intro i
    fin_cases i
    · simpa [gTwo] using
        (show ClosedConvexFunction (fenchelConjugate n f₁) from
          ⟨(fenchelConjugate_closedConvex (n := n) (f := f₁)).2,
            (fenchelConjugate_closedConvex (n := n) (f := f₁)).1⟩)
    · simpa [gTwo] using
        (show ClosedConvexFunction (fenchelConjugate n f₂) from
          ⟨(fenchelConjugate_closedConvex (n := n) (f := f₂)).2,
            (fenchelConjugate_closedConvex (n := n) (f := f₂)).1⟩)
  have hg_closed : LowerSemicontinuous g := by
    -- Closedness of the two summands passes to their finite sum.
    simpa [g, gTwo, Fin.sum_univ_two] using
      (closedConvexFunction_sum_of_closed
        (f := gTwo) hgTwo_closed
        (hproper := by
          intro i
          fin_cases i
          · simpa [gTwo] using (proper_fenchelConjugate_of_proper (n := n) (f := f₁) hf₁_proper)
          · simpa [gTwo] using (proper_fenchelConjugate_of_proper (n := n) (f := f₂) hf₂_proper))).2
  have hsmoothConj :
      IsEssentiallySmooth (fenchelConjugate n g) :=
    (essentiallyStrictlyConvex_iff_conjugate_essentiallySmooth
      (f := g) hg_proper hg_closed).1 hg_essStrict
  have hriWitness :
      Set.Nonempty
        (⋂ i : Fin 2,
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (gTwo i))) := by
    rcases
        helperForCorollary_26_3_2_commonRelativeInterior_twoConjugates
          (f₁ := f₁) (f₂ := f₂) hri with
      ⟨z, hz⟩
    refine ⟨(EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm z, Set.mem_iInter.2 ?_⟩
    intro i
    -- Convert the `Fin n → ℝ` relative-interior witness to the Euclidean-space formulation.
    have hz' :
        (EuclideanSpace.equiv (Fin n) ℝ).symm z ∈
          euclideanRelativeInterior n
            ((EuclideanSpace.equiv (Fin n) ℝ).symm ''
              effectiveDomain Set.univ (gTwo i)) :=
      (mem_euclideanRelativeInterior_fin_iff
        (n := n)
        (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) (gTwo i))
        (x := z)).1 (hz i)
    simpa [helperForTheorem_23_4_preimage_eq_symmImage
      (C := effectiveDomain Set.univ (gTwo i)), gTwo] using hz'
  have hconjEq :
      fenchelConjugate n g = infimalConvolution f₁ f₂ := by
    have hbiconj :
        ∀ i : Fin 2,
          fenchelConjugate n (gTwo i) =
            Fin.cases f₁ (fun _ => f₂) i := by
      intro i
      fin_cases i
      · simpa [gTwo] using
          (fenchelConjugate_biconjugate_eq_of_closedConvex (n := n) (f := f₁)
            (hf_closed := hf₁_closed)
            (hf_convex := hf₁_proper.1)
            (hf_ne_bot := fun x => hf₁.1.1 x))
      · simpa [gTwo] using
          (fenchelConjugate_biconjugate_eq_of_closedConvex (n := n) (f := f₂)
            (hf_closed := hf₂_closed)
            (hf_convex := hf₂_proper.1)
            (hf_ne_bot := fun x => hf₂.1.1 x))
    have hgSum :
        g = fun x => ∑ i : Fin 2, gTwo i x := by
      funext x
      rw [Fin.sum_univ_two]
      change fenchelConjugate n f₁ x + fenchelConjugate n f₂ x =
        gTwo ⟨0, by decide⟩ x + gTwo ⟨1, by decide⟩ x
      rfl
    calc
      fenchelConjugate n g = fenchelConjugate n (fun x => ∑ i : Fin 2, gTwo i x) := by
        rw [hgSum]
      _ =
          infimalConvolutionFamily (fun i : Fin 2 => fenchelConjugate n (gTwo i)) := by
            simpa using
              (section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
                (f := gTwo)
                (hf := by
                  intro i
                  fin_cases i
                  · simpa [gTwo] using
                      (proper_fenchelConjugate_of_proper (n := n) (f := f₁) hf₁_proper)
                  · simpa [gTwo] using
                      (proper_fenchelConjugate_of_proper (n := n) (f := f₂) hf₂_proper))
                hriWitness).1
      _ = infimalConvolutionFamily (fun i : Fin 2 => Fin.cases f₁ (fun _ => f₂) i) := by
            simp [hbiconj]
      _ = infimalConvolution f₁ f₂ := by
            simpa using
              (infimalConvolution_eq_infimalConvolutionFamily_two (f := f₁) (g := f₂)).symm
  -- The dual theorem yields smoothness of `(f₁* + f₂*)*`, which Theorem 16.4 rewrites as `f₁ □ f₂`.
  simpa [hconjEq] using hsmoothConj

end Section26
end Chap05
