/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part11

section Chap04
section Section21

/-- Helper for Theorem 21.4: under the weaker recession hypothesis on `C = ℝⁿ`, failure of
the primal alternative still yields a sparse `Finsupp` dual-margin certificate. This is the
textbook `I = I₀ ⊔ I₁`, `k = conv {k₀, k₁}` route from `section21.json`, not the older
outside-subtype reduction (which is false in general). -/
lemma helperForTheorem_21_4_originalRoute_univ_convexHullConjugate_zero_neg_of_nonempty_affineBlock
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (hConstOutside :
      ∀ d : Fin n → ℝ,
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) →
          ∀ i : I, i ∉ I0 →
            ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x)
    (hInonempty : ¬ IsEmpty I)
    (hNotPrimal :
      ¬ ∃ x : Fin n → ℝ, ∀ i : I, f i x ≤ (0 : EReal))
    (hA :
      ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} : Set (Fin n → ℝ)).Nonempty) :
    convexHullFunctionFamily (fun i : I => fenchelConjugate n (f i)) 0 < (0 : EReal) := by
  by_cases hJempty : IsEmpty {i : I // i ∉ I0}
  · rcases hA with ⟨x, hxA⟩
    exfalso
    apply hNotPrimal
    refine ⟨x, ?_⟩
    intro i
    by_cases hi : i ∈ I0
    · exact hxA i hi
    · let _ : IsEmpty {i : I // i ∉ I0} := hJempty
      exact (isEmptyElim (α := {i : I // i ∉ I0}) ⟨i, hi⟩ : f i x ≤ (0 : EReal))
  have hJnonempty : ¬ IsEmpty {i : I // i ∉ I0} := hJempty
  have hNotPrimalOnOutsideSubtype :
      ¬ ∃ x : Fin n → ℝ,
          x ∈ {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} ∧
            ∀ j : {i : I // i ∉ I0}, f j.1 x ≤ (0 : EReal) := by
    exact
      helperForTheorem_21_4_notPrimal_on_affineFeasibleSet_outsideSubtype
        f I0 (helperForTheorem_21_4_notPrimal_on_affineFeasibleSet f I0 hNotPrimal)
  exact
    helperForTheorem_21_4_originalRoute_univ_convexHullConjugate_zero_neg_of_nonempty_twoBlock
      f I0 hfProper hfClosed hAffine hConstOutside hInonempty hNotPrimal hA
      hJnonempty hNotPrimalOnOutsideSubtype

/-- Helper for Theorem 21.4: under the weaker recession hypothesis on `C = ℝⁿ`, failure of
the primal alternative still yields a sparse `Finsupp` dual-margin certificate. This is the
textbook `I = I₀ ⊔ I₁`, `k = conv {k₀, k₁}` route from `section21.json`, not the older
outside-subtype reduction (which is false in general). -/
lemma helperForTheorem_21_4_originalRoute_univ_notPrimal_to_supportBoundedFinsupp_margin_of_nonempty_affineBlock
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (hConstOutside :
      ∀ d : Fin n → ℝ,
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) →
          ∀ i : I, i ∉ I0 →
            ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x)
    (hInonempty : ¬ IsEmpty I)
    (hNotPrimal :
      ¬ ∃ x : Fin n → ℝ, ∀ i : I, f i x ≤ (0 : EReal))
    (hA :
      ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} : Set (Fin n → ℝ)).Nonempty) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        lam.support.card ≤ n + 1 ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ,
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  have hHullZeroNeg :
      convexHullFunctionFamily (fun i : I => fenchelConjugate n (f i)) 0 < (0 : EReal) :=
    helperForTheorem_21_4_originalRoute_univ_convexHullConjugate_zero_neg_of_nonempty_affineBlock
      f I0 hfProper hfClosed hAffine hConstOutside hInonempty hNotPrimal hA
  rcases
      helperForTheorem_21_3_sparse_dual_margin_on_univ_of_convexHullConjugate_zero_neg
        f hfProper hHullZeroNeg with
    ⟨m, hm, idx, w, hwNonneg, ε, hε, hmargin⟩
  exact
    helperForTheorem_21_3_noninjectiveSparseDual_margin_on_univ_to_supportBoundedFinsupp_margin
      (f := f) ⟨m, hm, idx, w, hwNonneg, ε, hε, hmargin⟩

/-- Helper for Theorem 21.4: if the affine block `C₀ = {x | fᵢ(x) ≤ 0, i ∈ I₀}` is empty,
the theorem reduces to the already-settled finite affine-only separation on `I₀`. -/
lemma helperForTheorem_21_4_originalRoute_univ_notPrimal_to_supportBoundedFinsupp_margin_of_empty_affineBlock
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (I0 : Finset I)
    (hAffine :
      ∀ i : I, i ∈ I0 →
        ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal))
    (hAempty :
      ({x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)} : Set (Fin n → ℝ)) = ∅) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        lam.support.card ≤ n + 1 ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ,
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  have hfiniteAffine :
      ∃ m : ℕ, m ≤ n + 1 ∧
        ∃ idx : Fin m → {i : I // i ∈ I0}, ∃ w : Fin m → ℝ,
          (∀ j : Fin m, 0 ≤ w j) ∧
            ∃ ε : ℝ, 0 < ε ∧
              ∀ x : Fin n → ℝ,
                ((ε : ℝ) : EReal) ≤
                  ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j).1 x := by
    exact
      helperForTheorem_21_4_affineBlock_gap_of_empty_affineFeasibleSet_to_affineBlockSubtype_sparseFiniteDual_margin
        f I0 hAffine hAempty
  exact
    helperForTheorem_21_4_affineBlockSubtype_sparseDual_margin_to_supportBoundedFinsupp_margin
      f I0 hfiniteAffine

/-- Helper for Theorem 21.4: under the weaker recession hypothesis on `C = ℝⁿ`, failure of
the primal alternative still yields a sparse `Finsupp` dual-margin certificate. This is the
textbook `I = I₀ ⊔ I₁`, `k = conv {k₀, k₁}` route from `section21.json`, not the older
outside-subtype reduction (which is false in general). -/
lemma helperForTheorem_21_4_originalRoute_univ_notPrimal_to_supportBoundedFinsupp_margin
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hWeakerRecession :
      ∃ I0 : Finset I,
        (∀ i : I, i ∈ I0 →
          ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal)) ∧
        (∀ d : Fin n → ℝ,
          (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) →
            ∀ i : I, i ∉ I0 →
              ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x))
    (hInonempty : ¬ IsEmpty I)
    (hNotPrimal :
      ¬ ∃ x : Fin n → ℝ, ∀ i : I, f i x ≤ (0 : EReal)) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        lam.support.card ≤ n + 1 ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ,
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  rcases hWeakerRecession with ⟨I0, hAffine, hConstOutside⟩
  let A : Set (Fin n → ℝ) := {x : Fin n → ℝ | ∀ i : I, i ∈ I0 → f i x ≤ (0 : EReal)}
  by_cases hA : A.Nonempty
  · exact
      helperForTheorem_21_4_originalRoute_univ_notPrimal_to_supportBoundedFinsupp_margin_of_nonempty_affineBlock
        f I0 hfProper hfClosed hAffine hConstOutside hInonempty hNotPrimal hA
  · have hAempty : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    exact
      helperForTheorem_21_4_originalRoute_univ_notPrimal_to_supportBoundedFinsupp_margin_of_empty_affineBlock
        f I0 hAffine hAempty

/-- Helper for Theorem 21.4: under the weaker recession hypothesis on `C = ℝⁿ`, failure of
the primal alternative still yields a sparse `Finsupp` dual-margin certificate. -/
lemma helperForTheorem_21_4_univ_notPrimal_to_supportBoundedFinsupp_margin
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hWeakerRecession :
      ∃ I0 : Finset I,
        (∀ i : I, i ∈ I0 →
          ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal)) ∧
        (∀ d : Fin n → ℝ,
          (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) →
            ∀ i : I, i ∉ I0 →
              ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x))
    (hInonempty : ¬ IsEmpty I)
    (hNotPrimal :
      ¬ ∃ x : Fin n → ℝ, ∀ i : I, f i x ≤ (0 : EReal)) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        lam.support.card ≤ n + 1 ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ,
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  exact
    helperForTheorem_21_4_originalRoute_univ_notPrimal_to_supportBoundedFinsupp_margin
      f hfProper hfClosed hWeakerRecession hInonempty hNotPrimal

/-- Helper for Theorem 21.4: package the weaker-hypothesis bridge in exactly the sparse dual
format used by the main theorem and by the Corollary 21.3.1 contradiction step. -/
lemma helperForTheorem_21_4_sparseDual_of_notPrimal
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hWeakerRecession :
      ∃ I0 : Finset I,
        (∀ i : I, i ∈ I0 →
          ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal)) ∧
        (∀ d : Fin n → ℝ,
          (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) →
            ∀ i : I, i ∉ I0 →
              ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x))
    (hInonempty : ¬ IsEmpty I)
    (hNotPrimal :
      ¬ ∃ x : Fin n → ℝ, ∀ i : I, f i x ≤ (0 : EReal)) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        lam.support.card ≤ n + 1 ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ,
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  -- Route correction: once the weaker-hypothesis bridge reaches the sparse `Finsupp` shape,
  -- the remaining packaging is identical to the already-settled Theorem 21.3 endpoint.
  exact helperForTheorem_21_4_univ_notPrimal_to_supportBoundedFinsupp_margin
    f hfProper hfClosed hWeakerRecession hInonempty hNotPrimal

/-- Theorem 21.4: when `C = ℝⁿ`, the recession-direction hypothesis in Theorem 21.3 and
Corollary 21.3.1 may be replaced by the weaker assumption that there exists a finite subset
`I₀ ⊆ I` such that each `fᵢ` is affine for `i ∈ I₀`, and every common recession direction of
the family is a direction along which each `fᵢ` is constant for `i ∉ I₀`. Under this weaker
hypothesis, the `C = ℝⁿ` forms of Theorem 21.3 and Corollary 21.3.1 still hold. -/
theorem theorem21_4_univ_weaker_recession_hypothesis
    {n : ℕ} {I : Type*}
    (f : I → (Fin n → ℝ) → EReal)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hWeakerRecession :
      ∃ I0 : Finset I,
        (∀ i : I, i ∈ I0 →
          ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f i x = (a x : EReal)) ∧
        (∀ d : Fin n → ℝ,
          (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x) →
            ∀ i : I, i ∉ I0 →
              ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) = f i x)) :
    let primalAlt : Prop :=
      ∃ x : Fin n → ℝ, ∀ i : I, f i x ≤ (0 : EReal)
    let dualAlt : Prop :=
      ∃ lam : I →₀ ℝ,
        (∀ i : I, 0 ≤ lam i) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ,
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x)
    (Xor' primalAlt dualAlt ∧
      (dualAlt →
        ∃ lam : I →₀ ℝ,
          (∀ i : I, 0 ≤ lam i) ∧
            lam.support.card ≤ n + 1 ∧
              ∃ ε : ℝ, 0 < ε ∧
                ∀ x : Fin n → ℝ,
                  ((ε : ℝ) : EReal) ≤
                    Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x))) ∧
      ((∀ ε : ℝ, 0 < ε →
          ∀ s : Finset I, s.card ≤ n + 1 →
            ∃ x : Fin n → ℝ, ∀ i ∈ s, f i x < (ε : EReal)) →
        primalAlt) := by
  -- Route correction: do not try to reuse the stronger no-common-recession theorem directly;
  -- instead, isolate the new weaker-hypothesis bridge and keep the rest of the assembly exact.
  dsimp
  by_cases hI : IsEmpty I
  · have hPrimal :
        ∃ x : Fin n → ℝ, ∀ i : I, f i x ≤ (0 : EReal) := by
      -- In the empty-index case, the inequalities are vacuous.
      simpa using
        (helperForTheorem_21_3_primal_of_isEmpty
          (C := (Set.univ : Set (Fin n → ℝ)))
          (hCnonempty := (Set.univ_nonempty : (Set.univ : Set (Fin n → ℝ)).Nonempty))
          (f := f) hI)
    have hDualImpossible :
        ¬ ∃ lam : I →₀ ℝ,
          (∀ i : I, 0 ≤ lam i) ∧
            ∃ ε : ℝ, 0 < ε ∧
              ∀ x : Fin n → ℝ,
                ((ε : ℝ) : EReal) ≤
                  Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
      -- The empty support cannot dominate a positive margin on all of `ℝⁿ`.
      simpa using
        (helperForTheorem_21_3_dual_impossible_of_isEmpty
          (C := (Set.univ : Set (Fin n → ℝ)))
          (hCnonempty := (Set.univ_nonempty : (Set.univ : Set (Fin n → ℝ)).Nonempty))
          (f := f) hI)
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [xor_def]
        exact Or.inl ⟨hPrimal, hDualImpossible⟩
      · -- The sparse-upgrade implication is vacuous because dual is impossible.
        intro hDual
        exact False.elim (hDualImpossible hDual)
    · -- The finite-subsystem premise is irrelevant once the primal witness is already known.
      intro _
      exact hPrimal
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [xor_def]
        by_cases hPrimal :
            ∃ x : Fin n → ℝ, ∀ i : I, f i x ≤ (0 : EReal)
        · refine Or.inl ⟨hPrimal, ?_⟩
          intro hDual
          -- A primal witness on `Set.univ` rules out every dual margin certificate.
          have hPrimalUniv :
              ∃ x : Fin n → ℝ, x ∈ (Set.univ : Set (Fin n → ℝ)) ∧
                ∀ i : I, f i x ≤ (0 : EReal) := by
            rcases hPrimal with ⟨x, hx⟩
            exact ⟨x, by simp, hx⟩
          have hDualUniv :
              ∃ lam : I →₀ ℝ,
                (∀ i : I, 0 ≤ lam i) ∧
                  ∃ ε : ℝ, 0 < ε ∧
                    ∀ x : Fin n → ℝ, x ∈ (Set.univ : Set (Fin n → ℝ)) →
                      ((ε : ℝ) : EReal) ≤
                        Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
            rcases hDual with ⟨lam, hlamNonneg, ε, hε, hmargin⟩
            exact ⟨lam, hlamNonneg, ε, hε, by
              intro x hx
              exact hmargin x⟩
          exact helperForTheorem_21_3_primal_excludes_dual
            (C := (Set.univ : Set (Fin n → ℝ))) (f := f) hPrimalUniv hDualUniv
        · refine Or.inr ⟨?_, hPrimal⟩
          -- The new weaker-hypothesis bridge supplies the dual branch under `¬ primal`.
          have hSparse :
              ∃ lam : I →₀ ℝ,
                (∀ i : I, 0 ≤ lam i) ∧
                  lam.support.card ≤ n + 1 ∧
                    ∃ ε : ℝ, 0 < ε ∧
                      ∀ x : Fin n → ℝ,
                        ((ε : ℝ) : EReal) ≤
                          Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) :=
            helperForTheorem_21_4_sparseDual_of_notPrimal
              f hfProper hfClosed hWeakerRecession hI hPrimal
          have hSparseUniv :
              ∃ lam : I →₀ ℝ,
                (∀ i : I, 0 ≤ lam i) ∧
                  lam.support.card ≤ n + 1 ∧
                    ∃ ε : ℝ, 0 < ε ∧
                      ∀ x : Fin n → ℝ, x ∈ (Set.univ : Set (Fin n → ℝ)) →
                        ((ε : ℝ) : EReal) ≤
                          Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
            rcases hSparse with ⟨lam, hlamNonneg, hcard, ε, hε, hmargin⟩
            exact ⟨lam, hlamNonneg, hcard, ε, hε, by
              intro x hx
              exact hmargin x⟩
          simpa using
            (helperForTheorem_21_3_supportBoundedFinsupp_margin_forget_bound
              (C := (Set.univ : Set (Fin n → ℝ))) (f := f) hSparseUniv)
      · intro hDual
        by_cases hPrimal :
            ∃ x : Fin n → ℝ, ∀ i : I, f i x ≤ (0 : EReal)
        · -- If primal already holds, the given dual witness is impossible.
          have hPrimalUniv :
              ∃ x : Fin n → ℝ, x ∈ (Set.univ : Set (Fin n → ℝ)) ∧
                ∀ i : I, f i x ≤ (0 : EReal) := by
            rcases hPrimal with ⟨x, hx⟩
            exact ⟨x, by simp, hx⟩
          have hDualUniv :
              ∃ lam : I →₀ ℝ,
                (∀ i : I, 0 ≤ lam i) ∧
                  ∃ ε : ℝ, 0 < ε ∧
                    ∀ x : Fin n → ℝ, x ∈ (Set.univ : Set (Fin n → ℝ)) →
                      ((ε : ℝ) : EReal) ≤
                        Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
            rcases hDual with ⟨lam, hlamNonneg, ε, hε, hmargin⟩
            exact ⟨lam, hlamNonneg, ε, hε, by
              intro x hx
              exact hmargin x⟩
          exact False.elim <|
            helperForTheorem_21_3_primal_excludes_dual
              (C := (Set.univ : Set (Fin n → ℝ))) (f := f) hPrimalUniv hDualUniv
        · -- Otherwise we may invoke the same `¬ primal` sparse extraction again.
          exact helperForTheorem_21_4_sparseDual_of_notPrimal
            f hfProper hfClosed hWeakerRecession hI hPrimal
    · intro hFiniteSubsystemStrictFeasible
      -- The corollary argument is unchanged once the weaker-hypothesis bridge gives a
      -- sparse dual witness under `¬ primal`.
      by_contra hNotPrimal
      rcases helperForTheorem_21_4_sparseDual_of_notPrimal
          f hfProper hfClosed hWeakerRecession hI hNotPrimal with
        ⟨lam, hlamNonneg, hcard, ε, hε, hmargin⟩
      have hFiniteSubsystemStrictFeasibleUniv :
          ∀ ε : ℝ, 0 < ε →
            ∀ s : Finset I, s.card ≤ n + 1 →
              ∃ x : Fin n → ℝ, x ∈ (Set.univ : Set (Fin n → ℝ)) ∧
                ∀ i ∈ s, f i x < (ε : EReal) := by
        intro ε hεpos s hs
        rcases hFiniteSubsystemStrictFeasible ε hεpos s hs with ⟨x, hx⟩
        exact ⟨x, by simp, hx⟩
      exact helperForCorollary_21_3_1_sparseDual_contradicts_finiteSubsystemHyp
        (C := (Set.univ : Set (Fin n → ℝ))) (f := f)
        hFiniteSubsystemStrictFeasibleUniv lam hlamNonneg hcard ε hε
        (by
          intro x hx
          exact hmargin x)

/-- A family of convex sets in `ℝⁿ` satisfies the weaker Helly recession hypothesis when some
finite subfamily is polyhedral and every common recession direction is a lineality direction of
each member outside that finite block. -/
def HasHellyWeakRecessionHypothesis
    {n : ℕ} {I : Type*} (C : I → Set (Fin n → ℝ)) : Prop :=
  ∃ I0 : Finset I,
    (∀ i : I, i ∈ I0 → IsPolyhedralConvexSet n (C i)) ∧
      ∀ d : Fin n → ℝ,
        (∀ i : I, d ∈ Set.recessionCone (C i)) →
          ∀ i : I, i ∉ I0 → d ∈ (-Set.recessionCone (C i)) ∩ Set.recessionCone (C i)

-- Proof sketch: encode each set by its indicator function and translate the weaker set-level
-- hypothesis into the weaker functional recession hypothesis of `theorem21_4_univ_weaker_recession_hypothesis`.
-- Then apply the `C = ℝⁿ` Helly conclusion there and translate the resulting global nonpositive
-- point back into a common point of the original family.
/-- Helper for Theorem 21.5: each polyhedral member of the distinguished finite block admits a
finite closed-halfspace description. -/
lemma helperForTheorem_21_5_polyhedralMember_hasFiniteHalfspaceRepresentation
    {n : ℕ} {I : Type*} {I0 : Finset I}
    (C : I → Set (Fin n → ℝ))
    (i : {i : I // i ∈ I0})
    (hPoly : IsPolyhedralConvexSet n (C i.1)) :
    ∃ m : ℕ, ∃ b : Fin m → Fin n → ℝ, ∃ β : Fin m → ℝ,
      C i.1 = ⋂ j : Fin m, closedHalfSpaceLE n (b j) (β j) := by
  -- Unpack the standard finite-halfspace characterization of polyhedral convex sets.
  exact (isPolyhedralConvexSet_iff_exists_finite_halfspaces n (C i.1)).1 hPoly

/-- Helper for Theorem 21.5: nonpositive values on all half-space inequalities recover
membership in the represented polyhedral set. -/
lemma helperForTheorem_21_5_nonpositiveHalfspaceBlock_implies_memPolyhedral
    {n m : ℕ}
    {S : Set (Fin n → ℝ)}
    (b : Fin m → Fin n → ℝ)
    (β : Fin m → ℝ)
    (hS : S = ⋂ j : Fin m, closedHalfSpaceLE n (b j) (β j))
    {x : Fin n → ℝ}
    (hx : ∀ j : Fin m, (((x ⬝ᵥ b j) - β j : ℝ) : EReal) ≤ (0 : EReal)) :
    x ∈ S := by
  -- Convert the `EReal` inequalities back to the defining real half-space inequalities.
  have hxHalfspace : ∀ j : Fin m, x ∈ closedHalfSpaceLE n (b j) (β j) := by
    intro j
    have hxReal : (x ⬝ᵥ b j) - β j ≤ 0 := by
      exact_mod_cast hx j
    have hxLe : x ⬝ᵥ b j ≤ β j := by
      linarith
    simpa [closedHalfSpaceLE] using hxLe
  -- Reassemble the pointwise half-space bounds into membership in the intersection.
  rw [hS]
  exact Set.mem_iInter.mpr hxHalfspace

/-- Helper for Theorem 21.5: a lineality direction preserves the indicator of a convex set
along every nonnegative ray. -/
lemma helperForTheorem_21_5_indicator_eq_along_lineality
    {n : ℕ} {S : Set (Fin n → ℝ)}
    (_hSconv : Convex ℝ S)
    {d : Fin n → ℝ}
    (hd : d ∈ (-Set.recessionCone S) ∩ Set.recessionCone S) :
    ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
      indicatorFunction S (x + t • d) = indicatorFunction S x := by
  intro x t ht
  have hdPos : d ∈ Set.recessionCone S := hd.2
  have hdNeg : -d ∈ Set.recessionCone S := by
    simpa [Set.mem_neg] using hd.1
  have hdPos' : ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → x + t • d ∈ S := by
    intro x hx t ht
    exact hdPos hx (t := t) ht
  have hdNeg' : ∀ x ∈ S, ∀ t : ℝ, 0 ≤ t → x + t • (-d) ∈ S := by
    intro x hx t ht
    exact hdNeg hx (t := t) ht
  have hMemIff : x + t • d ∈ S ↔ x ∈ S := by
    constructor
    · intro hxt
      have hxBack : (x + t • d) + t • (-d) ∈ S := hdNeg' (x + t • d) hxt t ht
      simpa [smul_neg, add_assoc] using hxBack
    · intro hx
      exact hdPos' x hx t ht
  -- Compare the two indicator values by reducing both to the same membership test.
  by_cases hx : x ∈ S
  · have hxt : x + t • d ∈ S := hMemIff.mpr hx
    simp [indicatorFunction, hx, hxt]
  · have hxt : x + t • d ∉ S := by
      intro hxtMem
      exact hx (hMemIff.mp hxtMem)
    simp [indicatorFunction, hx, hxt]

/-- Helper for Theorem 21.5: projecting an expanded finite subsystem back to its original
indices cannot increase cardinality. -/
lemma helperForTheorem_21_5_projectExpandedSubfamily_cardBound
    {J I : Type*} [DecidableEq I]
    (s : Finset J) (proj : J → I) :
    (s.image proj).card ≤ s.card := by
  -- Finset image cardinality is monotone under projection.
  exact Finset.card_image_le

/-- Helper for Theorem 21.5: monotonicity of every left-block affine inequality along `d`
forces `d` to lie in the recession cone of the corresponding polyhedral member. -/
lemma helperForTheorem_21_5_leftBlock_monotone_implies_recessionMembership
    {n : ℕ} {I : Type*} {I0 : Finset I}
    (C : I → Set (Fin n → ℝ))
    (mOf : {i : I // i ∈ I0} → ℕ)
    (bOf : ∀ i : {i : I // i ∈ I0}, Fin (mOf i) → Fin n → ℝ)
    (βOf : ∀ i : {i : I // i ∈ I0}, Fin (mOf i) → ℝ)
    (hRepEq :
      ∀ i : {i : I // i ∈ I0},
        C i.1 = ⋂ j : Fin (mOf i), closedHalfSpaceLE n (bOf i j) (βOf i j))
    (i : {i : I // i ∈ I0})
    {d : Fin n → ℝ}
    (hmono :
      ∀ j : Fin (mOf i), ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
        ((((x + t • d) ⬝ᵥ bOf i j) - βOf i j : ℝ) : EReal) ≤
          ((((x ⬝ᵥ bOf i j) - βOf i j : ℝ) : EReal)) ) :
    d ∈ Set.recessionCone (C i.1) := by
  intro x hx t ht
  -- Rewrite membership in `C i.1` into the chosen finite half-space system.
  rw [hRepEq i] at hx ⊢
  refine Set.mem_iInter.mpr ?_
  intro j
  -- Read off the directional inequality from the special case `x = 0`, `t = 1`.
  have hSlopeEReal := hmono j 0 1 (by norm_num)
  have hSlopeReal :
      (((0 : Fin n → ℝ) + (1 : ℝ) • d) ⬝ᵥ bOf i j) - βOf i j ≤
        (((0 : Fin n → ℝ) ⬝ᵥ bOf i j) - βOf i j) :=
    EReal.coe_le_coe_iff.mp (by simpa using hSlopeEReal)
  have hDirLe : d ⬝ᵥ bOf i j ≤ 0 := by
    have hDirLe' : (d ⬝ᵥ bOf i j) - βOf i j ≤ 0 - βOf i j := by
      simpa using hSlopeReal
    linarith
  -- Combine the original half-space inequality with the nonpositive directional slope.
  have hxj : x ∈ closedHalfSpaceLE n (bOf i j) (βOf i j) := Set.mem_iInter.mp hx j
  have hxLe : x ⬝ᵥ bOf i j ≤ βOf i j := by
    simpa [closedHalfSpaceLE] using hxj
  have hTranslated : (x + t • d) ⬝ᵥ bOf i j ≤ βOf i j := by
    rw [add_dotProduct, smul_dotProduct]
    simp [smul_eq_mul]
    nlinarith [hxLe, hDirLe, ht]
  simpa [closedHalfSpaceLE] using hTranslated

/-- Theorem 21.5: in Helly's theorem, the no-common-recession-direction hypothesis may be
replaced by the weaker assumption that there is a finite subset `I₀` such that `C i` is
polyhedral for `i ∈ I₀`, and every direction common to all recession cones `recessionCone (C i)`
is a lineality direction of each `C i` with `i ∉ I₀`. Under this weaker hypothesis, if every
subfamily of cardinality at most `n + 1` has nonempty intersection, then the whole family has
nonempty intersection. -/
theorem theorem21_5_helly_theorem_under_weaker_recession_hypothesis
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    (hCnonempty : ∀ i : I, (C i).Nonempty)
    (hCclosed : ∀ i : I, IsClosed (C i))
    (hCconvex : ∀ i : I, Convex ℝ (C i))
    (hWeakerRecession : HasHellyWeakRecessionHypothesis (n := n) C)
    (hFiniteIntersectionNonempty :
      ∀ s : Finset I, s.card ≤ n + 1 → ∃ x : Fin n → ℝ, ∀ i ∈ s, x ∈ C i) :
    ∃ x : Fin n → ℝ, ∀ i : I, x ∈ C i := by
  classical
  rcases hWeakerRecession with ⟨I0, hI0poly, hLinealityOutside⟩
  have hHalfspaceRep :
      ∀ i : {i : I // i ∈ I0},
        ∃ m : ℕ, ∃ b : Fin m → Fin n → ℝ, ∃ β : Fin m → ℝ,
          C i.1 = ⋂ j : Fin m, closedHalfSpaceLE n (b j) (β j) := by
    intro i
    -- Expand each polyhedral member of the finite distinguished block into finitely many
    -- affine half-space inequalities.
    exact helperForTheorem_21_5_polyhedralMember_hasFiniteHalfspaceRepresentation
      C i (hI0poly i.1 i.2)
  let mOf : {i : I // i ∈ I0} → ℕ :=
    fun i => Classical.choose (hHalfspaceRep i)
  let bOf : ∀ i : {i : I // i ∈ I0}, Fin (mOf i) → Fin n → ℝ :=
    fun i => Classical.choose (Classical.choose_spec (hHalfspaceRep i))
  let βOf : ∀ i : {i : I // i ∈ I0}, Fin (mOf i) → ℝ :=
    fun i => Classical.choose (Classical.choose_spec (Classical.choose_spec (hHalfspaceRep i)))
  have hRepEq :
      ∀ i : {i : I // i ∈ I0},
        C i.1 = ⋂ j : Fin (mOf i), closedHalfSpaceLE n (bOf i j) (βOf i j) := by
    intro i
    -- Record the chosen half-space descriptions for later reconstruction.
    exact Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hHalfspaceRep i)))
  let JL : Type _ := Sigma fun i : {i : I // i ∈ I0} => Fin (mOf i)
  let JR : Type _ := {i : I // i ∉ I0}
  let J : Type _ := Sum JL JR
  let f : J → (Fin n → ℝ) → EReal :=
    fun j x =>
      match j with
      | Sum.inl ij => (((x ⬝ᵥ bOf ij.1 ij.2) - βOf ij.1 ij.2 : ℝ) : EReal)
      | Sum.inr i => indicatorFunction (C i.1) x
  have hfProper : ∀ j : J, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f j) := by
    intro j
    cases j with
    | inl ij =>
        -- Left-block functions are affine inequalities, hence proper convex.
        let a : AffineMap ℝ (Fin n → ℝ) ℝ :=
          (dotProductLinear n (bOf ij.1 ij.2)).toAffineMap -
            AffineMap.const ℝ (Fin n → ℝ) (βOf ij.1 ij.2)
        simpa [f, a, JL, J, dotProductLinear] using
          helperForTheorem_21_2_shifted_affine_properConvex (n := n) a 0
    | inr i =>
        -- Right-block functions stay as indicators of the original convex nonempty sets.
        exact properConvexFunctionOn_indicator_of_convex_of_nonempty
          (C := C i.1) (hCconvex i.1) (hCnonempty i.1)
  have hfClosed :
      ∀ j : J, IsClosed {p : (Fin n → ℝ) × ℝ | f j p.1 ≤ (p.2 : EReal)} := by
    intro j
    cases j with
    | inl ij =>
        -- The epigraph of an affine real-valued map is closed.
        let a : AffineMap ℝ (Fin n → ℝ) ℝ :=
          (dotProductLinear n (bOf ij.1 ij.2)).toAffineMap -
            AffineMap.const ℝ (Fin n → ℝ) (βOf ij.1 ij.2)
        simpa [f, a, JL, J, dotProductLinear] using
          helperForTheorem_21_4_affine_ereal_epigraph_closed (n := n) a
    | inr i =>
        -- Indicator epigraph closedness is exactly the closedness of the underlying set.
        exact (helperForCorollary_21_3_2_indicatorEpigraphClosed
          (C := fun i : JR => C i.1) (hCclosed := fun i => hCclosed i.1)) i
  have hExpandedWeaker :
      ∃ J0 : Finset J,
        (∀ j : J, j ∈ J0 →
          ∃ a : AffineMap ℝ (Fin n → ℝ) ℝ, ∀ x : Fin n → ℝ, f j x = (a x : EReal)) ∧
        (∀ d : Fin n → ℝ,
          (∀ j : J, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f j (x + t • d) ≤ f j x) →
            ∀ j : J, j ∉ J0 →
              ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f j (x + t • d) = f j x) := by
    -- Route correction: make the left/right bridge explicit by choosing the finite left block
    -- as `J0`, proving recession membership from left-block monotonicity, and then upgrading
    -- the right block from monotonicity to constancy via the weaker recession hypothesis.
    refine ⟨(Finset.univ : Finset JL).image Sum.inl, ?_⟩
    constructor
    · intro j hj
      rcases Finset.mem_image.mp hj with ⟨ij, hij, rfl⟩
      let a : AffineMap ℝ (Fin n → ℝ) ℝ :=
        (dotProductLinear n (bOf ij.1 ij.2)).toAffineMap -
          AffineMap.const ℝ (Fin n → ℝ) (βOf ij.1 ij.2)
      -- Every left-block function is exactly the corresponding affine inequality.
      refine ⟨a, ?_⟩
      intro x
      simpa [f, a, JL, J, dotProductLinear] using rfl
    · intro d hmono j hjNot x t ht
      cases j with
      | inl ij =>
          exfalso
          have hijUniv : ij ∈ (Finset.univ : Finset JL) := by
            simp
          exact hjNot (Finset.mem_image.mpr ⟨ij, hijUniv, rfl⟩)
      | inr i =>
          have hdAll : ∀ i' : I, d ∈ Set.recessionCone (C i') := by
            intro i'
            by_cases hi' : i' ∈ I0
            · let ii : {i : I // i ∈ I0} := ⟨i', hi'⟩
              -- The left block records every defining half-space for `C i'`, so monotonicity
              -- of those affine inequalities already forces `d ∈ recessionCone (C i')`.
              apply helperForTheorem_21_5_leftBlock_monotone_implies_recessionMembership
                (C := C) (mOf := mOf) (bOf := bOf) (βOf := βOf) hRepEq ii
              intro j' y s hs
              simpa [f] using hmono (Sum.inl ⟨ii, j'⟩) y s hs
            · have hmonoRight :
                  ∀ k : JR, ∀ y : Fin n → ℝ, ∀ s : ℝ, 0 ≤ s →
                    indicatorFunction (C k.1) (y + s • d) ≤ indicatorFunction (C k.1) y := by
                intro k y s hs
                simpa [f] using hmono (Sum.inr k) y s hs
              have hdRight : ∀ k : JR, d ∈ Set.recessionCone (C k.1) :=
                helperForCorollary_21_3_2_indicatorMonotoneAlong_d_implies_recessionMembership
                  (C := fun k : JR => C k.1) hmonoRight
              exact hdRight ⟨i', hi'⟩
          have hLineality : d ∈ (-Set.recessionCone (C i.1)) ∩ Set.recessionCone (C i.1) :=
            hLinealityOutside d hdAll i.1 i.2
          -- Outside the finite block, common recession directions become lineality directions,
          -- so the corresponding indicator functions are constant along the ray.
          simpa [f] using
            helperForTheorem_21_5_indicator_eq_along_lineality
              (S := C i.1) (hCconvex i.1) hLineality x t ht
  have hExpandedStrictFeasible :
      ∀ ε : ℝ, 0 < ε →
        ∀ s : Finset J, s.card ≤ n + 1 →
          ∃ x : Fin n → ℝ, ∀ j ∈ s, f j x < (ε : EReal) := by
    intro ε hε s hs
    let proj : J → I := fun j =>
      match j with
      | Sum.inl ij => ij.1.1
      | Sum.inr i => i.1
    have hProjCard : (s.image proj).card ≤ n + 1 := by
      exact le_trans (helperForTheorem_21_5_projectExpandedSubfamily_cardBound s proj) hs
    have hEpsEReal : ((0 : ℝ) : EReal) < (ε : EReal) := by
      exact (EReal.coe_lt_coe_iff).2 hε
    rcases hFiniteIntersectionNonempty (s.image proj) hProjCard with ⟨x, hxAll⟩
    refine ⟨x, ?_⟩
    intro j hj
    have hProjMem : proj j ∈ s.image proj := by
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
    have hxProj : x ∈ C (proj j) := hxAll (proj j) hProjMem
    cases j with
    | inl ij =>
        -- A common point of the projected original subsystem satisfies every selected
        -- half-space inequality coming from the left block.
        have hxC : x ∈ C ij.1.1 := by
          simpa [proj] using hxProj
        have hxInter : x ∈ ⋂ j' : Fin (mOf ij.1), closedHalfSpaceLE n (bOf ij.1 j') (βOf ij.1 j') := by
          rw [← hRepEq ij.1]
          exact hxC
        have hxHalf : x ∈ closedHalfSpaceLE n (bOf ij.1 ij.2) (βOf ij.1 ij.2) :=
          Set.mem_iInter.mp hxInter ij.2
        have hxLe : x ⬝ᵥ bOf ij.1 ij.2 ≤ βOf ij.1 ij.2 := by
          simpa [closedHalfSpaceLE] using hxHalf
        have hValLeZero :
            ((((x ⬝ᵥ bOf ij.1 ij.2) - βOf ij.1 ij.2 : ℝ) : EReal) ≤ (0 : EReal)) := by
          have hReal : (x ⬝ᵥ bOf ij.1 ij.2) - βOf ij.1 ij.2 ≤ 0 := by
            linarith
          exact_mod_cast hReal
        exact lt_of_le_of_lt (by simpa [f] using hValLeZero) hEpsEReal
    | inr i =>
        -- On the right block, the same projected point lies in the underlying original set,
        -- so the indicator value is exactly `0 < ε`.
        have hxC : x ∈ C i.1 := by
          simpa [proj] using hxProj
        simpa [f, indicatorFunction, hxC] using hEpsEReal
  have hExpandedWitnessMem :
      ∀ {x : Fin n → ℝ}, (∀ j : J, f j x ≤ (0 : EReal)) → ∀ i : I, x ∈ C i := by
    intro x hx j
    by_cases hj : j ∈ I0
    · let jj : {i : I // i ∈ I0} := ⟨j, hj⟩
      -- In the distinguished finite block, the stored half-space representation lets us
      -- reconstruct membership from the nonpositive affine inequalities.
      have hxLeft :
          ∀ k : Fin (mOf jj),
            ((((x ⬝ᵥ bOf jj k) - βOf jj k : ℝ) : EReal) ≤ (0 : EReal)) := by
        intro k
        simpa [f] using hx (Sum.inl ⟨jj, k⟩)
      exact
        helperForTheorem_21_5_nonpositiveHalfspaceBlock_implies_memPolyhedral
          (b := bOf jj) (β := βOf jj) (hS := hRepEq jj) hxLeft
    · -- Outside the finite block, a nonpositive indicator value means the point is already
      -- inside the original set.
      have hIndicatorNonpos :
          ∀ i : JR, indicatorFunction (C i.1) x ≤ (0 : EReal) := by
        intro i
        simpa [f] using hx (Sum.inr i)
      have hMemRight : ∀ i : JR, x ∈ C i.1 :=
        helperForCorollary_21_3_2_indicatorNonpositive_implies_memAll
          (C := fun i : JR => C i.1) hIndicatorNonpos
      exact hMemRight ⟨j, hj⟩
  have hExpandedPrimal : ∃ x : Fin n → ℝ, ∀ j : J, f j x ≤ (0 : EReal) := by
    -- Apply Theorem 21.4 to the expanded family and keep only its Helly conclusion.
    have hTheorem21_4 :=
      theorem21_4_univ_weaker_recession_hypothesis
        (n := n) (I := J) f hfProper hfClosed hExpandedWeaker
    dsimp at hTheorem21_4
    exact hTheorem21_4.2 hExpandedStrictFeasible
  rcases hExpandedPrimal with ⟨x, hx⟩
  -- Translate the nonpositive expanded witness back to a common point of the original family.
  exact ⟨x, hExpandedWitnessMem hx⟩


end Section21
end Chap04
