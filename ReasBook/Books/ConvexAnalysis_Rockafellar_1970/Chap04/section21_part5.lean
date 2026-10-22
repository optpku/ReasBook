/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section21_part4

section Chap04
section Section21

set_option linter.unnecessarySimpa false

/-- Helper for Theorem 21.3: package a sparse finite-index margin certificate into a
`Finsupp` certificate and preserve the support-card bound `≤ n + 1`. -/
lemma helperForTheorem_21_3_sparseFiniteDual_margin_to_finsuppDual_margin {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (f : I → (Fin n → ℝ) → EReal)
    (hfinite :
      ∃ m : ℕ, m ≤ n + 1 ∧
        ∃ idx : Fin m → I, Function.Injective idx ∧ ∃ w : Fin m → ℝ,
          (∀ j : Fin m, 0 ≤ w j) ∧
            ∃ ε : ℝ, 0 < ε ∧
              ∀ x : Fin n → ℝ, x ∈ C →
                ((ε : ℝ) : EReal) ≤
                  ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j) x) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        lam.support.card ≤ n + 1 ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  classical
  rcases hfinite with ⟨m, hm_le, idx, hidx, w, hw_nonneg, ε, hε, hmargin⟩
  let wF : Fin m →₀ ℝ := Finsupp.equivFunOnFinite.symm w
  let lam : I →₀ ℝ := Finsupp.embDomain ⟨idx, hidx⟩ wF
  refine ⟨lam, ?_, ?_, ε, hε, ?_⟩
  · -- Coefficients remain nonnegative after `embDomain` packaging.
    intro i
    by_cases hi : i ∈ Set.range idx
    · rcases hi with ⟨j, rfl⟩
      have hwF_nonneg : 0 ≤ wF j := by
        simpa [wF] using hw_nonneg j
      have hlam_apply : lam (idx j) = wF j := by
        simpa [lam] using Finsupp.embDomain_apply_self ⟨idx, hidx⟩ wF j
      simpa [hlam_apply] using hwF_nonneg
    · have hlam_zero : lam i = 0 := by
        simpa [lam] using Finsupp.embDomain_notin_range ⟨idx, hidx⟩ wF i hi
      simpa [hlam_zero]
  · -- The support of `embDomain` has cardinal at most `m`, hence at most `n + 1`.
    have hsupport :
        lam.support = Finset.map ⟨idx, hidx⟩ wF.support := by
      simpa [lam] using Finsupp.support_embDomain (f := ⟨idx, hidx⟩) (v := wF)
    have hcard_le_m : lam.support.card ≤ m := by
      calc
        lam.support.card = (Finset.map ⟨idx, hidx⟩ wF.support).card := by simpa [hsupport]
        _ = wF.support.card := by
          simpa using (Finset.card_map (f := ⟨idx, hidx⟩) (s := wF.support))
        _ ≤ Fintype.card (Fin m) := Finset.card_le_univ wF.support
        _ = m := by simp
    exact le_trans hcard_le_m hm_le
  · intro x hxC
    -- Transport the weighted sum through `embDomain`, then expand to `Fin m`.
    have hsumEq :
        Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) =
          ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j) x := by
      calc
        Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x)
            = lam.sum (fun i a => ((a : ℝ) : EReal) * f i x) := by
              rfl
        _ = wF.sum (fun j a => ((a : ℝ) : EReal) * f (idx j) x) := by
              simpa [lam] using
                (Finsupp.sum_embDomain
                  (v := wF) (f := ⟨idx, hidx⟩)
                  (g := fun i a => ((a : ℝ) : EReal) * f i x))
        _ = ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j) x := by
              calc
                wF.sum (fun j a => ((a : ℝ) : EReal) * f (idx j) x) =
                    ∑ j : Fin m, ((wF j : ℝ) : EReal) * f (idx j) x := by
                      simpa using
                        (Finsupp.sum_fintype
                          wF
                          (fun j a => ((a : ℝ) : EReal) * f (idx j) x)
                          (by intro j; simp))
                _ = ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j) x := by
                      simp [wF]
    simpa [hsumEq] using hmargin x hxC

/-- Helper for Theorem 21.3: forget the cardinal bound from a sparse finite-index margin
certificate, yielding the plain finite-index certificate shape. -/
lemma helperForTheorem_21_3_sparseFiniteDual_margin_forget_bound {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (f : I → (Fin n → ℝ) → EReal)
    (hfiniteSparse :
      ∃ m : ℕ, m ≤ n + 1 ∧
        ∃ idx : Fin m → I, Function.Injective idx ∧ ∃ w : Fin m → ℝ,
          (∀ j : Fin m, 0 ≤ w j) ∧
            ∃ ε : ℝ, 0 < ε ∧
              ∀ x : Fin n → ℝ, x ∈ C →
                ((ε : ℝ) : EReal) ≤
                  ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j) x) :
    ∃ m : ℕ, ∃ idx : Fin m → I, Function.Injective idx ∧ ∃ w : Fin m → ℝ,
      (∀ j : Fin m, 0 ≤ w j) ∧
        ∃ ε : ℝ, 0 < ε ∧
          ∀ x : Fin n → ℝ, x ∈ C →
            ((ε : ℝ) : EReal) ≤
              ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j) x := by
  -- Route correction: make the sparse-to-plain conversion explicit so downstream code can
  -- use the generic finite-packaging lemma without redoing existential unpacking.
  rcases hfiniteSparse with ⟨m, -, idx, hidx, w, hw_nonneg, ε, hε, hmargin⟩
  exact ⟨m, idx, hidx, w, hw_nonneg, ε, hε, hmargin⟩

/-- Helper for Theorem 21.3: package a sparse finite-index margin certificate into a
`Finsupp` dual certificate by first forgetting the cardinal bound, then using the generic
finite packaging helper. -/
lemma helperForTheorem_21_3_sparseFiniteDual_margin_to_finsuppDual_margin_via_finitePackaging
    {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (f : I → (Fin n → ℝ) → EReal)
    (hfiniteSparse :
      ∃ m : ℕ, m ≤ n + 1 ∧
        ∃ idx : Fin m → I, Function.Injective idx ∧ ∃ w : Fin m → ℝ,
          (∀ j : Fin m, 0 ≤ w j) ∧
            ∃ ε : ℝ, 0 < ε ∧
              ∀ x : Fin n → ℝ, x ∈ C →
                ((ε : ℝ) : EReal) ≤
                  ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j) x) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        ∃ ε : ℝ, 0 < ε ∧
          ∀ x : Fin n → ℝ, x ∈ C →
            ((ε : ℝ) : EReal) ≤
              Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  -- Convert sparse finite data to the plain finite format consumed by the generic packager.
  have hfinite :
      ∃ m : ℕ, ∃ idx : Fin m → I, Function.Injective idx ∧ ∃ w : Fin m → ℝ,
        (∀ j : Fin m, 0 ≤ w j) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j) x :=
    helperForTheorem_21_3_sparseFiniteDual_margin_forget_bound C f hfiniteSparse
  -- Then reuse the already-proved finite-index packaging lemma.
  exact helperForTheorem_21_3_finiteDual_margin_to_finsuppDual_margin C f hfinite

/-- Helper for Theorem 21.3: convert a support-bounded `Finsupp` margin certificate into a
finite-index certificate with injective indexing and the same `m ≤ n + 1` bound. -/
lemma helperForTheorem_21_3_finsuppDual_margin_with_supportBound_to_finiteDual_margin
    {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (f : I → (Fin n → ℝ) → EReal)
    (hDualSparse :
      ∃ lam : I →₀ ℝ,
        (∀ i : I, 0 ≤ lam i) ∧
          lam.support.card ≤ n + 1 ∧
            ∃ ε : ℝ, 0 < ε ∧
              ∀ x : Fin n → ℝ, x ∈ C →
                ((ε : ℝ) : EReal) ≤
                  Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x)) :
    ∃ m : ℕ, m ≤ n + 1 ∧
      ∃ idx : Fin m → I, Function.Injective idx ∧ ∃ w : Fin m → ℝ,
        (∀ j : Fin m, 0 ≤ w j) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j) x := by
  -- Route correction: reuse the earlier core conversion helper so all downstream
  -- Theorem 21.3 paths share one finite/injective transport argument.
  exact helperForTheorem_21_3_supportBoundedFinsupp_to_finiteDual_margin C f hDualSparse

/-- Helper for Theorem 21.3: combine finite extraction and coefficient packaging to obtain
the exact `Finsupp` dual-certificate shape. -/
lemma helperForTheorem_21_3_notPrimal_to_finsuppDual_margin {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (hCnonempty : C.Nonempty)
    (hCclosed : IsClosed C)
    (hCconvex : Convex ℝ C)
    (f : I → (Fin n → ℝ) → EReal)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hNoCommonRecession :
      ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧ d ∈ Set.recessionCone C ∧
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x))
    (hInonempty : ¬ IsEmpty I)
    (hNotPrimal :
      ¬ ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : I, f i x ≤ (0 : EReal)) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        ∃ ε : ℝ, 0 < ε ∧
          ∀ x : Fin n → ℝ, x ∈ C →
            ((ε : ℝ) : EReal) ≤
              Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  -- Route correction: target the sparse `Finsupp` endpoint directly from the dedicated
  -- bridge, rather than routing through finite/injective reindexing first.
  have hDualSparse :
      ∃ lam : I →₀ ℝ,
        (∀ i : I, 0 ≤ lam i) ∧
          lam.support.card ≤ n + 1 ∧
            ∃ ε : ℝ, 0 < ε ∧
              ∀ x : Fin n → ℝ, x ∈ C →
                ((ε : ℝ) : EReal) ≤
                  Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
    -- The only unresolved step is this analytic bridge endpoint.
    exact helperForTheorem_21_3_notPrimal_to_finsuppDual_margin_with_supportBound_bridge
      C hCnonempty hCclosed hCconvex f hfProper hfClosed hNoCommonRecession hInonempty hNotPrimal
  -- Route correction: project the same sparse witness through the shared bundle and keep
  -- this lemma focused on the plain `Finsupp` dual endpoint.
  exact (helperForTheorem_21_3_supportBoundedFinsupp_margin_to_finiteAndPlainDual
    C f hDualSparse).2

/-- Helper for Theorem 21.3: sparsify a `Finsupp` dual certificate to support size at most
`n + 1` while preserving positive margin. -/
lemma helperForTheorem_21_3_dual_sparsify_support_le_n_plus_one {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (hCclosed : IsClosed C)
    (hCconvex : Convex ℝ C)
    (f : I → (Fin n → ℝ) → EReal)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hNoCommonRecession :
      ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧ d ∈ Set.recessionCone C ∧
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x))
    (hInonempty : ¬ IsEmpty I)
    (hDual :
      ∃ lam : I →₀ ℝ,
        (∀ i : I, 0 ≤ lam i) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x)) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        lam.support.card ≤ n + 1 ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  -- Route correction: do not sparsify the given certificate directly; derive `¬primal`,
  -- then rebuild a fresh sparse certificate from the not-primal extraction pipeline.
  by_cases hCnonempty : C.Nonempty
  · have hNotPrimal :
        ¬ ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : I, f i x ≤ (0 : EReal) := by
      intro hPrimal
      exact helperForTheorem_21_3_primal_excludes_dual C f hPrimal hDual
    have hfiniteSparse :
        ∃ m : ℕ, m ≤ n + 1 ∧
          ∃ idx : Fin m → I, Function.Injective idx ∧ ∃ w : Fin m → ℝ,
            (∀ j : Fin m, 0 ≤ w j) ∧
              ∃ ε : ℝ, 0 < ε ∧
                ∀ x : Fin n → ℝ, x ∈ C →
                  ((ε : ℝ) : EReal) ≤
                    ∑ j : Fin m, ((w j : ℝ) : EReal) * f (idx j) x :=
      helperForTheorem_21_3_notPrimal_to_finiteDual_margin
        C hCnonempty hCclosed hCconvex f hfProper hfClosed
        hNoCommonRecession hInonempty hNotPrimal
    exact helperForTheorem_21_3_sparseFiniteDual_margin_to_finsuppDual_margin C f hfiniteSparse
  · have hCempty : C = ∅ := Set.not_nonempty_iff_eq_empty.mp hCnonempty
    refine ⟨0, ?_, ?_, 1, by norm_num, ?_⟩
    · intro i
      simp
    · simp
    · intro x hxC
      exfalso
      simpa [hCempty] using hxC

/-- Helper for Theorem 21.3: from failure of the primal branch, construct a dual
certificate with finite support and positive margin. -/
lemma helperForTheorem_21_3_dual_exists_of_not_primal {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (hCnonempty : C.Nonempty)
    (hCclosed : IsClosed C)
    (hCconvex : Convex ℝ C)
    (f : I → (Fin n → ℝ) → EReal)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hNoCommonRecession :
      ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧ d ∈ Set.recessionCone C ∧
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x))
    (hInonempty : ¬ IsEmpty I)
    (hNotPrimal :
      ¬ ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : I, f i x ≤ (0 : EReal)) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        ∃ ε : ℝ, 0 < ε ∧
          ∀ x : Fin n → ℝ, x ∈ C →
            ((ε : ℝ) : EReal) ≤
              Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  -- Route correction: use the dedicated finite-extraction + packaging pipeline.
  exact helperForTheorem_21_3_notPrimal_to_finsuppDual_margin
    C hCnonempty hCclosed hCconvex f hfProper hfClosed
    hNoCommonRecession hInonempty hNotPrimal

/-- Helper for Theorem 21.3: sparsify any dual certificate to support size at most `n + 1`. -/
lemma helperForTheorem_21_3_sparse_of_dual {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (hCclosed : IsClosed C)
    (hCconvex : Convex ℝ C)
    (f : I → (Fin n → ℝ) → EReal)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hNoCommonRecession :
      ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧ d ∈ Set.recessionCone C ∧
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x))
    (hInonempty : ¬ IsEmpty I)
    (hDual :
      ∃ lam : I →₀ ℝ,
        (∀ i : I, 0 ≤ lam i) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x)) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        lam.support.card ≤ n + 1 ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  -- Route correction: delegate sparsification to the dedicated support-reduction helper.
  exact helperForTheorem_21_3_dual_sparsify_support_le_n_plus_one
    C hCclosed hCconvex f hfProper hfClosed hNoCommonRecession hInonempty hDual

-- Proof sketch: prove primal and dual are mutually exclusive, derive dual existence from
-- failure of primal via the separation pipeline, then sparsify the dual certificate to
-- support size at most `n + 1`.
/-- Theorem 21.3: Let `fᵢ` (`i ∈ I`) be closed proper convex functions on `ℝⁿ`, and let
`C ⊆ ℝⁿ` be nonempty, closed, and convex. Assume there is no nonzero vector that is
simultaneously a recession direction of `C` and of every `fᵢ`. Then exactly one of:
(a) there exists `x ∈ C` such that `fᵢ(x) ≤ 0` for all `i ∈ I`;
(b) there exist nonnegative multipliers with finite support and some `ε > 0` such that
`∑ λᵢ fᵢ(x) ≥ ε` for all `x ∈ C`.
Moreover, whenever (b) holds, the multipliers can be chosen with at most `n + 1`
nonzero entries. -/
theorem theorem21_infinite_convex_alternative_with_sparse_certificate {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (hCnonempty : C.Nonempty)
    (hCclosed : IsClosed C)
    (hCconvex : Convex ℝ C)
    (f : I → (Fin n → ℝ) → EReal)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hNoCommonRecession :
      ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧ d ∈ Set.recessionCone C ∧
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x)) :
    let primalAlt : Prop :=
      ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : I, f i x ≤ (0 : EReal)
    let dualAlt : Prop :=
      ∃ lam : I →₀ ℝ,
        (∀ i : I, 0 ≤ lam i) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x)
    Xor' primalAlt dualAlt ∧
      (dualAlt →
        ∃ lam : I →₀ ℝ,
          (∀ i : I, 0 ≤ lam i) ∧
            lam.support.card ≤ n + 1 ∧
              ∃ ε : ℝ, 0 < ε ∧
                ∀ x : Fin n → ℝ, x ∈ C →
                  ((ε : ℝ) : EReal) ≤
                    Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x)) := by
  -- Unfold the named alternatives so the goal matches the helper-lemma endpoints.
  dsimp
  by_cases hI : IsEmpty I
  · -- In the empty-index case, primal holds vacuously and dual is impossible.
    have hPrimal :
        ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : I, f i x ≤ (0 : EReal) :=
      helperForTheorem_21_3_primal_of_isEmpty C hCnonempty f hI
    have hDualImpossible :
        ¬ ∃ lam : I →₀ ℝ,
          (∀ i : I, 0 ≤ lam i) ∧
            ∃ ε : ℝ, 0 < ε ∧
              ∀ x : Fin n → ℝ, x ∈ C →
                ((ε : ℝ) : EReal) ≤
                  Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) :=
      helperForTheorem_21_3_dual_impossible_of_isEmpty C hCnonempty f hI
    refine ⟨?_, ?_⟩
    · -- Assemble `Xor'` as `(primal ∧ ¬ dual)` in this branch.
      rw [xor_def]
      exact Or.inl ⟨hPrimal, hDualImpossible⟩
    · -- Sparse-upgrade implication is vacuous because dual cannot occur.
      intro hDual
      exact False.elim (hDualImpossible hDual)
  · -- In the nonempty-index case, use primal/dual exclusion and dual-existence helpers.
    refine ⟨?_, ?_⟩
    · rw [xor_def]
      by_cases hPrimal :
          ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : I, f i x ≤ (0 : EReal)
      · -- If primal holds, dual is excluded.
        refine Or.inl ⟨hPrimal, ?_⟩
        intro hDual
        exact helperForTheorem_21_3_primal_excludes_dual C f hPrimal hDual
      · -- If primal fails, obtain dual by the not-primal extraction pipeline.
        refine Or.inr ⟨?_, hPrimal⟩
        exact helperForTheorem_21_3_dual_exists_of_not_primal
          C hCnonempty hCclosed hCconvex f hfProper hfClosed hNoCommonRecession hI hPrimal
    · -- Any dual witness can be sparsified to support size at most `n + 1`.
      intro hDual
      exact helperForTheorem_21_3_sparse_of_dual
        C hCclosed hCconvex f hfProper hfClosed hNoCommonRecession hI hDual

-- Proof sketch: apply Theorem 21.3. If the primal conclusion failed, Theorem 21.3 would
-- produce a sparse dual certificate supported on at most `n + 1` indices with a uniform
-- positive lower bound `ε`; evaluating this certificate at the point given by the finite
-- subsystem strict-feasibility hypothesis yields a contradiction.
/-- Helper for Corollary 21.3.1: from `¬ primal`, extract the sparse dual margin witness
given by Theorem 21.3. -/
lemma helperForCorollary_21_3_1_sparseDual_of_notPrimal
    {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (hCnonempty : C.Nonempty)
    (hCclosed : IsClosed C)
    (hCconvex : Convex ℝ C)
    (f : I → (Fin n → ℝ) → EReal)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hNoCommonRecession :
      ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧ d ∈ Set.recessionCone C ∧
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x))
    (hNotPrimal :
      ¬ ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : I, f i x ≤ (0 : EReal)) :
    ∃ lam : I →₀ ℝ,
      (∀ i : I, 0 ≤ lam i) ∧
        lam.support.card ≤ n + 1 ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
  -- Expand Theorem 21.3 alternatives and keep only the dual branch via `¬ primal`.
  have hAlt := theorem21_infinite_convex_alternative_with_sparse_certificate
    C hCnonempty hCclosed hCconvex f hfProper hfClosed hNoCommonRecession
  dsimp at hAlt
  have hXor : Xor'
      (∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : I, f i x ≤ (0 : EReal))
      (∃ lam : I →₀ ℝ,
        (∀ i : I, 0 ≤ lam i) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x)) := hAlt.1
  have hSparseUpgrade :
      (∃ lam : I →₀ ℝ,
        (∀ i : I, 0 ≤ lam i) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x)) →
        ∃ lam : I →₀ ℝ,
          (∀ i : I, 0 ≤ lam i) ∧
            lam.support.card ≤ n + 1 ∧
              ∃ ε : ℝ, 0 < ε ∧
                ∀ x : Fin n → ℝ, x ∈ C →
                  ((ε : ℝ) : EReal) ≤
                    Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := hAlt.2
  rw [xor_def] at hXor
  have hDual :
      ∃ lam : I →₀ ℝ,
        (∀ i : I, 0 ≤ lam i) ∧
          ∃ ε : ℝ, 0 < ε ∧
            ∀ x : Fin n → ℝ, x ∈ C →
              ((ε : ℝ) : EReal) ≤
                Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x) := by
    rcases hXor with hPrimalBranch | hDualBranch
    · exact False.elim (hNotPrimal hPrimalBranch.1)
    · exact hDualBranch.1
  -- Apply the sparse-upgrade endpoint from Theorem 21.3.
  exact hSparseUpgrade hDual

/-- Helper for Corollary 21.3.1: the scaled parameter `ε / (σ + 1)` is positive and gives
`(ε / (σ + 1)) * σ < ε` when `ε > 0` and `σ ≥ 0`. -/
lemma helperForCorollary_21_3_1_scaledEpsilon_lt_original
    (ε σ : ℝ) (hε : 0 < ε) (hσ : 0 ≤ σ) :
    0 < ε / (σ + 1) ∧ (ε / (σ + 1)) * σ < ε := by
  -- Positivity comes from dividing by a strictly positive denominator.
  have hσPlusOnePos : 0 < σ + 1 := by
    linarith
  have hScaledPos : 0 < ε / (σ + 1) := div_pos hε hσPlusOnePos
  -- Show `σ / (σ + 1) < 1`, then multiply by `ε > 0`.
  have hRatioLtOne : σ / (σ + 1) < 1 := by
    have hRatioEq : σ / (σ + 1) = 1 - 1 / (σ + 1) := by
      field_simp [hσPlusOnePos.ne']
      ring
    have hInvPos : 0 < 1 / (σ + 1) := one_div_pos.mpr hσPlusOnePos
    rw [hRatioEq]
    linarith
  have hσPlusOneNe : σ + 1 ≠ 0 := by
    linarith
  have hRearrange : (ε / (σ + 1)) * σ = ε * (σ / (σ + 1)) := by
    field_simp [hσPlusOneNe]
  have hMulOne : ε * 1 = ε := by
    ring
  have hScaledMulLt : (ε / (σ + 1)) * σ < ε := by
    calc
      (ε / (σ + 1)) * σ = ε * (σ / (σ + 1)) := hRearrange
      _ < ε * 1 := mul_lt_mul_of_pos_left hRatioLtOne hε
      _ = ε := hMulOne
  exact ⟨hScaledPos, hScaledMulLt⟩

/-- Helper for Corollary 21.3.1: bound a nonnegative weighted `EReal` sum using a uniform
pointwise upper bound `δ` on the summands. -/
lemma helperForCorollary_21_3_1_weightedSum_le_scaled_bound
    {I : Type*}
    (s : Finset I)
    (w : I → ℝ)
    (g : I → EReal)
    (δ : ℝ)
    (hw : ∀ i : I, 0 ≤ w i)
    (hg : ∀ i : I, i ∈ s → g i ≤ (δ : EReal)) :
    Finset.sum s (fun i => ((w i : ℝ) : EReal) * g i) ≤
      ((Finset.sum s (fun i => w i * δ)) : EReal) := by
  classical
  -- Apply coordinatewise monotonicity under nonnegative multipliers.
  have hsumLe :
      Finset.sum s (fun i => ((w i : ℝ) : EReal) * g i) ≤
        Finset.sum s (fun i => ((w i : ℝ) : EReal) * ((δ : ℝ) : EReal)) := by
    refine Finset.sum_le_sum ?_
    intro i hi
    have hwiNonneg : (0 : EReal) ≤ ((w i : ℝ) : EReal) := by
      exact_mod_cast hw i
    exact mul_le_mul_of_nonneg_left (hg i hi) hwiNonneg
  -- Rewrite the right sum as a real weighted sum, coerced to `EReal`.
  have hsumConst :
      Finset.sum s (fun i => ((w i : ℝ) : EReal) * ((δ : ℝ) : EReal)) =
        ((Finset.sum s (fun i => w i * δ)) : EReal) := by
    induction s using Finset.induction_on with
    | empty =>
        simp
    | @insert a s ha hs =>
        simp [ha]
  calc
    Finset.sum s (fun i => ((w i : ℝ) : EReal) * g i) ≤
        Finset.sum s (fun i => ((w i : ℝ) : EReal) * ((δ : ℝ) : EReal)) :=
      hsumLe
    _ = ((Finset.sum s (fun i => w i * δ)) : EReal) := hsumConst

/-- Helper for Corollary 21.3.1: any sparse dual margin certificate contradicts the
finite-subsystem strict-feasibility hypothesis. -/
lemma helperForCorollary_21_3_1_sparseDual_contradicts_finiteSubsystemHyp
    {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (f : I → (Fin n → ℝ) → EReal)
    (hFiniteSubsystemStrictFeasible :
      ∀ ε : ℝ, 0 < ε →
        ∀ s : Finset I, s.card ≤ n + 1 →
          ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i ∈ s, f i x < (ε : EReal))
    (lam : I →₀ ℝ)
    (hlamNonneg : ∀ i : I, 0 ≤ lam i)
    (hcard : lam.support.card ≤ n + 1)
    (ε : ℝ)
    (hε : 0 < ε)
    (hmargin :
      ∀ x : Fin n → ℝ, x ∈ C →
        ((ε : ℝ) : EReal) ≤
          Finset.sum lam.support (fun i => ((lam i : ℝ) : EReal) * f i x)) :
    False := by
  classical
  let s : Finset I := lam.support
  let σ : ℝ := Finset.sum s (fun i => lam i)
  let δ : ℝ := ε / (σ + 1)
  -- The support-sum `σ` is nonnegative because all coefficients are nonnegative.
  have hσNonneg : 0 ≤ σ := by
    dsimp [σ]
    refine Finset.sum_nonneg ?_
    intro i hi
    exact hlamNonneg i
  -- Use the scaled parameter `δ` so the weighted upper bound falls strictly below `ε`.
  have hScaled :=
    helperForCorollary_21_3_1_scaledEpsilon_lt_original ε σ hε hσNonneg
  have hδPos : 0 < δ := by
    simpa [δ] using hScaled.1
  have hδσLt : δ * σ < ε := by
    simpa [δ] using hScaled.2
  have hsCard : s.card ≤ n + 1 := by
    simpa [s] using hcard
  -- Apply strict feasibility to the support set `s`.
  rcases hFiniteSubsystemStrictFeasible δ hδPos s hsCard with ⟨x, hxC, hxStrict⟩
  have hPointwiseLe : ∀ i : I, i ∈ s → f i x ≤ (δ : EReal) := by
    intro i hi
    exact le_of_lt (hxStrict i hi)
  -- Upper-bound the weighted sum at this witness point by `∑ (lam i * δ)`.
  have hWeightedLe :
      Finset.sum s (fun i => ((lam i : ℝ) : EReal) * f i x) ≤
        ((Finset.sum s (fun i => lam i * δ)) : EReal) :=
    helperForCorollary_21_3_1_weightedSum_le_scaled_bound s lam (fun i => f i x) δ
      hlamNonneg hPointwiseLe
  have hSumMulEq : Finset.sum s (fun i => lam i * δ) = σ * δ := by
    dsimp [σ]
    simp [Finset.sum_mul]
  have hσδLt : σ * δ < ε := by
    simpa [mul_comm] using hδσLt
  have hSumLt : Finset.sum s (fun i => lam i * δ) < ε := by
    simpa [hSumMulEq] using hσδLt
  have hSumLtEReal :
      Finset.sum s (fun i => ((lam i : ℝ) : EReal) * ((δ : ℝ) : EReal)) <
        ((ε : ℝ) : EReal) := by
    have hSumLtCoe :
        (((Finset.sum s (fun i => lam i * δ) : ℝ) : EReal) < ((ε : ℝ) : EReal)) := by
      exact (EReal.coe_lt_coe_iff).2 hSumLt
    have hSumLtCastProd :
        Finset.sum s (fun i => (((lam i * δ : ℝ)) : EReal)) < ((ε : ℝ) : EReal) := by
      have hSumEq :
          (((Finset.sum s (fun i => lam i * δ) : ℝ) : EReal)) =
            Finset.sum s (fun i => (((lam i * δ : ℝ)) : EReal)) := by
        simpa using
          (helperForTheorem_21_1_coe_finset_sum_real
            (s := s) (g := fun i => lam i * δ))
      simpa [hSumEq] using hSumLtCoe
    have hCastProdEq :
        Finset.sum s (fun i => (((lam i * δ : ℝ)) : EReal)) =
          Finset.sum s (fun i => ((lam i : ℝ) : EReal) * ((δ : ℝ) : EReal)) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp [EReal.coe_mul]
    simpa [hCastProdEq] using hSumLtCastProd
  have hWeightedLt :
      Finset.sum s (fun i => ((lam i : ℝ) : EReal) * f i x) < ((ε : ℝ) : EReal) :=
    lt_of_le_of_lt hWeightedLe hSumLtEReal
  -- This contradicts the dual margin lower bound evaluated at the same witness.
  have hMarginAtX :
      ((ε : ℝ) : EReal) ≤
        Finset.sum s (fun i => ((lam i : ℝ) : EReal) * f i x) := by
    simpa [s] using hmargin x hxC
  exact (not_lt_of_ge hMarginAtX) hWeightedLt

-- Proof sketch: argue by contradiction; use Theorem 21.3 to extract a sparse dual margin
-- witness from `¬ ∃ x ∈ C, ∀ i, f i x ≤ 0`, then contradict it using the finite-subsystem
-- strict-feasibility hypothesis at the same support.
/-- Corollary 21.3.1: Let `fᵢ` (`i ∈ I`) be closed proper convex functions on `ℝⁿ`, and let
`C ⊆ ℝⁿ` be nonempty, closed, and convex. Assume there is no nonzero vector that is
simultaneously a recession direction of `C` and of every `fᵢ`. If for every `ε > 0` and
every finite index set `s` with `s.card ≤ n + 1` there exists `x ∈ C` such that
`fᵢ(x) < ε` for all `i ∈ s`, then there exists `x ∈ C` such that `fᵢ(x) ≤ 0` for all
`i ∈ I`. -/
theorem corollary21_3_1_finite_subsystems_strictly_feasible_implies_global_nonpositive_point
    {n : ℕ} {I : Type*}
    (C : Set (Fin n → ℝ))
    (hCnonempty : C.Nonempty)
    (hCclosed : IsClosed C)
    (hCconvex : Convex ℝ C)
    (f : I → (Fin n → ℝ) → EReal)
    (hfProper : ∀ i : I, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hfClosed : ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | f i p.1 ≤ (p.2 : EReal)})
    (hNoCommonRecession :
      ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧ d ∈ Set.recessionCone C ∧
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t → f i (x + t • d) ≤ f i x))
    (hFiniteSubsystemStrictFeasible :
      ∀ ε : ℝ, 0 < ε →
        ∀ s : Finset I, s.card ≤ n + 1 →
          ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i ∈ s, f i x < (ε : EReal)) :
    ∃ x : Fin n → ℝ, x ∈ C ∧ ∀ i : I, f i x ≤ (0 : EReal) := by
  -- Argue by contradiction against the primal feasibility conclusion.
  by_contra hNotPrimal
  -- Extract a sparse dual margin witness from Theorem 21.3 under `¬ primal`.
  rcases helperForCorollary_21_3_1_sparseDual_of_notPrimal
      C hCnonempty hCclosed hCconvex f hfProper hfClosed hNoCommonRecession hNotPrimal with
    ⟨lam, hlamNonneg, hcard, ε, hε, hmargin⟩
  -- The finite-subsystem strict-feasibility hypothesis contradicts that sparse dual witness.
  exact helperForCorollary_21_3_1_sparseDual_contradicts_finiteSubsystemHyp
    C f hFiniteSubsystemStrictFeasible lam hlamNonneg hcard ε hε hmargin

/-- Helper for Corollary 21.3.2 (Helly's Theorem): the indicator epigraph inequality set is closed
when the underlying set is closed. -/
lemma helperForCorollary_21_3_2_indicatorEpigraphClosed
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    (hCclosed : ∀ i : I, IsClosed (C i)) :
    ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | indicatorFunction (C i) p.1 ≤ (p.2 : EReal)} := by
  intro i
  -- Rewrite the indicator-epigraph condition as an intersection of two closed preimages.
  have hEq :
      {p : (Fin n → ℝ) × ℝ | indicatorFunction (C i) p.1 ≤ (p.2 : EReal)} =
        ((fun p : (Fin n → ℝ) × ℝ => p.1) ⁻¹' C i) ∩
          ((fun p : (Fin n → ℝ) × ℝ => p.2) ⁻¹' Set.Ici (0 : ℝ)) := by
    ext p
    by_cases hx : p.1 ∈ C i
    · simp [indicatorFunction, hx]
    · simp [indicatorFunction, hx]
  -- Each side of the intersection is closed by continuity of coordinate projections.
  have hClosedMem : IsClosed (((fun p : (Fin n → ℝ) × ℝ => p.1) ⁻¹' C i)) := by
    exact (hCclosed i).preimage continuous_fst
  have hClosedLower : IsClosed (((fun p : (Fin n → ℝ) × ℝ => p.2) ⁻¹' Set.Ici (0 : ℝ))) := by
    exact (isClosed_Ici).preimage continuous_snd
  rw [hEq]
  exact hClosedMem.inter hClosedLower

/-- Helper for Corollary 21.3.2 (Helly's Theorem): indicator monotonicity along `d` forces `d`
to lie in each recession cone. -/
lemma helperForCorollary_21_3_2_indicatorMonotoneAlong_d_implies_recessionMembership
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    {d : Fin n → ℝ}
    (hmono :
      ∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
        indicatorFunction (C i) (x + t • d) ≤ indicatorFunction (C i) x) :
    ∀ i : I, d ∈ Set.recessionCone (C i) := by
  intro i
  -- To prove recession membership, start from an arbitrary feasible point and nonnegative scale.
  intro x hx t ht
  have hStep : indicatorFunction (C i) (x + t • d) ≤ indicatorFunction (C i) x :=
    hmono i x t ht
  have hxValue : indicatorFunction (C i) x = (0 : EReal) := by
    simp [indicatorFunction, hx]
  have hLeZero : indicatorFunction (C i) (x + t • d) ≤ (0 : EReal) := by
    simpa [hxValue] using hStep
  -- If the translated point were outside `C i`, the indicator would be `⊤`, contradicting `≤ 0`.
  by_cases hxt : x + t • d ∈ C i
  · exact hxt
  · have hImpossible : (⊤ : EReal) ≤ (0 : EReal) := by
      simpa [indicatorFunction, hxt] using hLeZero
    exact False.elim ((not_top_le_coe 0) hImpossible)

/-- Helper for Corollary 21.3.2 (Helly's Theorem): the original no-common-recession hypothesis
implies the no-common-recession hypothesis required by Corollary 21.3.1 for `C = univ`. -/
lemma helperForCorollary_21_3_2_noCommonRecession_for_univIndicator
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    (hNoCommonRecession :
      ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧ ∀ i : I, d ∈ Set.recessionCone (C i)) :
    ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧ d ∈ Set.recessionCone (Set.univ : Set (Fin n → ℝ)) ∧
      (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
        indicatorFunction (C i) (x + t • d) ≤ indicatorFunction (C i) x) := by
  intro hBad
  rcases hBad with ⟨d, hdne, -, hmono⟩
  -- Convert indicator monotonicity to recession-cone membership in every `C i`.
  have hdAll : ∀ i : I, d ∈ Set.recessionCone (C i) :=
    helperForCorollary_21_3_2_indicatorMonotoneAlong_d_implies_recessionMembership
      C hmono
  exact hNoCommonRecession ⟨d, hdne, hdAll⟩

/-- Helper for Corollary 21.3.2 (Helly's Theorem): finite-intersection nonemptiness yields the
strict feasibility hypothesis for indicator functions. -/
lemma helperForCorollary_21_3_2_finiteIntersection_to_indicatorStrictFeasibility
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    (hFiniteIntersectionNonempty :
      ∀ s : Finset I, s.card ≤ n + 1 → ∃ x : Fin n → ℝ, ∀ i ∈ s, x ∈ C i) :
    ∀ ε : ℝ, 0 < ε →
      ∀ s : Finset I, s.card ≤ n + 1 →
        ∃ x : Fin n → ℝ, x ∈ (Set.univ : Set (Fin n → ℝ)) ∧
          ∀ i ∈ s, indicatorFunction (C i) x < (ε : EReal) := by
  intro ε hε s hs
  rcases hFiniteIntersectionNonempty s hs with ⟨x, hxAll⟩
  -- Use the common intersection point; every active indicator value is `0 < ε`.
  refine ⟨x, ?_, ?_⟩
  · simp
  · intro i hi
    have hxMem : x ∈ C i := hxAll i hi
    have hEpsEReal : ((0 : ℝ) : EReal) < (ε : EReal) := by
      exact (EReal.coe_lt_coe_iff).2 hε
    simpa [indicatorFunction, hxMem] using hEpsEReal

/-- Helper for Corollary 21.3.2 (Helly's Theorem): an indicator upper bound by `0` forces set
membership. -/
lemma helperForCorollary_21_3_2_indicatorNonpositive_implies_memAll
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    {x : Fin n → ℝ}
    (hIndicatorNonpos : ∀ i : I, indicatorFunction (C i) x ≤ (0 : EReal)) :
    ∀ i : I, x ∈ C i := by
  intro i
  by_cases hx : x ∈ C i
  · exact hx
  · -- Outside `C i`, the indicator is `⊤`, contradicting the assumed nonpositivity.
    have hImpossible : (⊤ : EReal) ≤ (0 : EReal) := by
      simpa [indicatorFunction, hx] using hIndicatorNonpos i
    exact False.elim ((not_top_le_coe 0) hImpossible)

-- Proof sketch: encode each set `C i` by its indicator function and apply
-- Corollary 21.3.1 on `univ`; finite-subfamily intersection nonemptiness gives strict
-- feasibility for the indicator system, and `indicatorFunction (C i) x ≤ 0` yields `x ∈ C i`.
/-- Corollary 21.3.2 (Helly's Theorem): let `(C i) (i ∈ I)` be nonempty closed convex
subsets of `ℝⁿ` with no common nonzero recession direction. If every subcollection of
cardinality at most `n + 1` has nonempty intersection, then the whole family has
nonempty intersection. -/
theorem corollary21_3_2_helly_theorem
    {n : ℕ} {I : Type*}
    (C : I → Set (Fin n → ℝ))
    (hCnonempty : ∀ i : I, (C i).Nonempty)
    (hCclosed : ∀ i : I, IsClosed (C i))
    (hCconvex : ∀ i : I, Convex ℝ (C i))
    (hNoCommonRecession :
      ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧ ∀ i : I, d ∈ Set.recessionCone (C i))
    (hFiniteIntersectionNonempty :
      ∀ s : Finset I, s.card ≤ n + 1 → ∃ x : Fin n → ℝ, ∀ i ∈ s, x ∈ C i) :
    ∃ x : Fin n → ℝ, ∀ i : I, x ∈ C i := by
  -- Route correction: prove Helly directly by applying Corollary 21.3.1 to indicator functions.
  have hfProper :
      ∀ i : I,
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (indicatorFunction (C i)) := by
    intro i
    -- Each indicator is proper convex because `C i` is convex and nonempty.
    exact properConvexFunctionOn_indicator_of_convex_of_nonempty
      (C := C i) (hCconvex i) (hCnonempty i)
  -- The indicator epigraphs are closed by closedness of each `C i`.
  have hfClosed :
      ∀ i : I, IsClosed {p : (Fin n → ℝ) × ℝ | indicatorFunction (C i) p.1 ≤ (p.2 : EReal)} :=
    helperForCorollary_21_3_2_indicatorEpigraphClosed C hCclosed
  -- Translate the no-common-recession hypothesis to the indicator-system form.
  have hNoCommonRecessionIndicator :
      ¬ ∃ d : Fin n → ℝ, d ≠ 0 ∧ d ∈ Set.recessionCone (Set.univ : Set (Fin n → ℝ)) ∧
        (∀ i : I, ∀ x : Fin n → ℝ, ∀ t : ℝ, 0 ≤ t →
          indicatorFunction (C i) (x + t • d) ≤ indicatorFunction (C i) x) :=
    helperForCorollary_21_3_2_noCommonRecession_for_univIndicator C hNoCommonRecession
  -- Finite-intersection nonemptiness yields strict feasibility for finite indicator subsystems.
  have hFiniteStrictFeasible :
      ∀ ε : ℝ, 0 < ε →
        ∀ s : Finset I, s.card ≤ n + 1 →
          ∃ x : Fin n → ℝ, x ∈ (Set.univ : Set (Fin n → ℝ)) ∧
            ∀ i ∈ s, indicatorFunction (C i) x < (ε : EReal) :=
    helperForCorollary_21_3_2_finiteIntersection_to_indicatorStrictFeasibility C
      hFiniteIntersectionNonempty
  -- Register nonemptiness of `univ` for the corollary instantiation.
  have hUnivNonempty : (Set.univ : Set (Fin n → ℝ)).Nonempty := by
    refine ⟨0, ?_⟩
    simp
  -- Apply Corollary 21.3.1 with `C = univ` and `f i = indicatorFunction (C i)`.
  rcases corollary21_3_1_finite_subsystems_strictly_feasible_implies_global_nonpositive_point
      (C := (Set.univ : Set (Fin n → ℝ)))
      (hCnonempty := hUnivNonempty)
      (hCclosed := isClosed_univ)
      (hCconvex := convex_univ)
      (f := fun i : I => indicatorFunction (C i))
      (hfProper := hfProper)
      (hfClosed := hfClosed)
      (hNoCommonRecession := hNoCommonRecessionIndicator)
      (hFiniteSubsystemStrictFeasible := hFiniteStrictFeasible) with
    ⟨x, _, hIndicatorNonpos⟩
  -- Convert nonpositivity of all indicators back to set-membership in every `C i`.
  refine ⟨x, ?_⟩
  exact helperForCorollary_21_3_2_indicatorNonpositive_implies_memAll C hIndicatorNonpos

end Section21
end Chap04
