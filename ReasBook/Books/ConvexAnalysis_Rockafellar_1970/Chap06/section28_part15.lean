/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part14

open scoped BigOperators Pointwise

section Chap06
section Section28

/-- Helper for Corollary 6.28.8: if each factor admits one finite witness, then the infimum of a
two-variable separable sum splits as the sum of the one-variable infima. -/
lemma helperForCorollary_6_28_8_twoFactor_iInf_eq_iInf_add_iInf
    {α β : Type*} [Nonempty α] [Nonempty β] (F : α → EReal) (G : β → EReal)
    (hF : ∃ a0, F a0 < ⊤) (hG : ∃ b0, G b0 < ⊤) :
    (⨅ p : α × β, F p.1 + G p.2) = (⨅ a, F a) + (⨅ b, G b) := by
  refine le_antisymm ?_ ?_
  · -- For the reverse inequality, approximate each one-variable infimum from above.
    refine EReal.le_add_of_forall_gt ?_ ?_ ?_
    · rcases hG with ⟨b0, hb0⟩
      exact Or.inr (ne_of_lt <| lt_of_le_of_lt (iInf_le G b0) hb0)
    · rcases hF with ⟨a0, ha0⟩
      exact Or.inl (ne_of_lt <| lt_of_le_of_lt (iInf_le F a0) ha0)
    · intro a' ha' b' hb'
      rcases (iInf_lt_iff.mp ha') with ⟨a, ha⟩
      rcases (iInf_lt_iff.mp hb') with ⟨b, hb⟩
      exact le_trans
        (iInf_le (fun p : α × β => F p.1 + G p.2) (a, b))
        (add_le_add ha.le hb.le)
  · -- The forward inequality is the pointwise lower-bound argument.
    refine le_iInf ?_
    intro p
    exact add_le_add (iInf_le F p.1) (iInf_le G p.2)

/-- Helper for Corollary 6.28.8: the zero tuple gives a finite witness for the finite sum of the
tilted coordinate integrands. -/
lemma helperForCorollary_6_28_8_sum_zero_lt_top
    {n : ℕ} (h : Fin n → ℝ → EReal) (hTop : ∀ k, h k 0 < ⊤) :
    (∑ k : Fin n, h k 0) < ⊤ := by
  -- Finite sums preserve non-`⊤` once every summand is non-`⊤`.
  refine lt_of_le_of_ne le_top ?_
  exact finset_sum_ne_top_of_forall (s := Finset.univ) (f := fun k : Fin n => h k 0)
    (fun k hk => ne_of_lt (hTop k))

/-- Helper for Corollary 6.28.8: the infimum of the separable tilted sum over `Fin n → ℝ`
splits into the finite sum of the coordinatewise infima. -/
lemma helperForCorollary_6_28_8_tiltedCoordinate_iInf_eq_sum_iInf
    {n : ℕ}
    (q :
      {q : Fin n → (Fin 1 → ℝ) → EReal //
        IsProperConvexFunctionFamilyOnUnitInterval n q})
    (vStar : ℝ) :
    (⨅ x : Fin n → ℝ,
      ∑ k : Fin n,
        (unitSimplexCoordinateObjective q k (fun _ : Fin 1 => x k) +
          ((vStar * x k : ℝ) : EReal))) =
      ∑ k : Fin n,
        ⨅ ξ : ℝ,
          (unitSimplexCoordinateObjective q k (fun _ : Fin 1 => ξ) +
            ((vStar * ξ : ℝ) : EReal)) := by
  -- Induct on the number of coordinates and peel off the last coordinate with `Fin.snoc`.
  induction n with
  | zero =>
      simp
  | succ m ih =>
      rw [helperForCorollary_6_28_8_iInf_snoc]
      have hRewrite :
          (⨅ y : Fin m → ℝ, ⨅ ξ : ℝ,
            ∑ k : Fin (m + 1),
              (unitSimplexCoordinateObjective q k
                  (fun _ : Fin 1 => ((@Fin.snoc _ (fun _ => ℝ) y ξ) k)) +
                ((vStar * ((@Fin.snoc _ (fun _ => ℝ) y ξ) k) : ℝ) : EReal))) =
            (⨅ y : Fin m → ℝ, ⨅ ξ : ℝ,
              (∑ k : Fin m,
                (unitSimplexCoordinateObjective q (Fin.castSucc k) (fun _ : Fin 1 => y k) +
                  ((vStar * y k : ℝ) : EReal))) +
                (unitSimplexCoordinateObjective q (Fin.last m) (fun _ : Fin 1 => ξ) +
                  ((vStar * ξ : ℝ) : EReal))) := by
        -- Rewrite the sum over `Fin (m + 1)` as the tail sum plus the last coordinate.
        apply iInf_congr
        intro y
        apply iInf_congr
        intro ξ
        rw [Fin.sum_univ_castSucc]
        simp
      rw [hRewrite]
      have hProd :
          (⨅ y : Fin m → ℝ, ⨅ ξ : ℝ,
              (∑ k : Fin m,
                (unitSimplexCoordinateObjective q (Fin.castSucc k) (fun _ : Fin 1 => y k) +
                  ((vStar * y k : ℝ) : EReal))) +
                (unitSimplexCoordinateObjective q (Fin.last m) (fun _ : Fin 1 => ξ) +
                  ((vStar * ξ : ℝ) : EReal))) =
            (⨅ p : (Fin m → ℝ) × ℝ,
              (∑ k : Fin m,
                (unitSimplexCoordinateObjective q (Fin.castSucc k) (fun _ : Fin 1 => p.1 k) +
                  ((vStar * p.1 k : ℝ) : EReal))) +
                (unitSimplexCoordinateObjective q (Fin.last m) (fun _ : Fin 1 => p.2) +
                  ((vStar * p.2 : ℝ) : EReal))) := by
        -- Repackage the iterated infimum as an infimum over the product space.
        simpa using
          (iInf_prod
            (f := fun p : (Fin m → ℝ) × ℝ =>
              (∑ k : Fin m,
                (unitSimplexCoordinateObjective q (Fin.castSucc k) (fun _ : Fin 1 => p.1 k) +
                  ((vStar * p.1 k : ℝ) : EReal))) +
                (unitSimplexCoordinateObjective q (Fin.last m) (fun _ : Fin 1 => p.2) +
                  ((vStar * p.2 : ℝ) : EReal)))).symm
      rw [hProd]
      have hTailWitness :
          ∃ y : Fin m → ℝ,
            (∑ k : Fin m,
              (unitSimplexCoordinateObjective q (Fin.castSucc k) (fun _ : Fin 1 => y k) +
                ((vStar * y k : ℝ) : EReal))) < ⊤ := by
        -- The zero tuple witnesses finiteness of the tail sum.
        refine ⟨fun _ => 0, ?_⟩
        simpa using
          helperForCorollary_6_28_8_sum_zero_lt_top
            (h := fun k ξ =>
              unitSimplexCoordinateObjective q (Fin.castSucc k) (fun _ : Fin 1 => ξ) +
                ((vStar * ξ : ℝ) : EReal))
            (hTop := fun k =>
              helperForCorollary_6_28_8_tiltedCoordinate_zero_lt_top q (Fin.castSucc k) vStar)
      have hLastWitness :
          ∃ ξ : ℝ,
            unitSimplexCoordinateObjective q (Fin.last m) (fun _ : Fin 1 => ξ) +
              ((vStar * ξ : ℝ) : EReal) < ⊤ := by
        exact ⟨0, helperForCorollary_6_28_8_tiltedCoordinate_zero_lt_top q (Fin.last m) vStar⟩
      rw [helperForCorollary_6_28_8_twoFactor_iInf_eq_iInf_add_iInf
        (F := fun y : Fin m → ℝ =>
          ∑ k : Fin m,
            (unitSimplexCoordinateObjective q (Fin.castSucc k) (fun _ : Fin 1 => y k) +
              ((vStar * y k : ℝ) : EReal)))
        (G := fun ξ : ℝ =>
          unitSimplexCoordinateObjective q (Fin.last m) (fun _ : Fin 1 => ξ) +
            ((vStar * ξ : ℝ) : EReal))
        hTailWitness hLastWitness]
      -- Apply the induction hypothesis to the tail block and rebuild the full finite sum.
      let qTail :
          {q : Fin m → (Fin 1 → ℝ) → EReal //
            IsProperConvexFunctionFamilyOnUnitInterval m q} :=
        ⟨fun k => q.1 (Fin.castSucc k), fun k => q.2 (Fin.castSucc k)⟩
      rw [show
          (⨅ a : Fin m → ℝ,
            ∑ k : Fin m,
              (unitSimplexCoordinateObjective q (Fin.castSucc k) (fun _ : Fin 1 => a k) +
                ((vStar * a k : ℝ) : EReal))) =
            ∑ k : Fin m,
              ⨅ ξ : ℝ,
                (unitSimplexCoordinateObjective q (Fin.castSucc k) (fun _ : Fin 1 => ξ) +
                  ((vStar * ξ : ℝ) : EReal)) by
            simpa [qTail] using ih qTail]
      simp [Fin.sum_univ_castSucc]

end Section28
end Chap06
