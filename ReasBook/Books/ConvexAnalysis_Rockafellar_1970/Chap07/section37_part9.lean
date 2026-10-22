/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section09_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part20
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part21
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section37_part8

section Chap07
section Section37

attribute [local instance] Classical.propDecidable

variable {m n : ℕ}

/-- Helper for Corollary 37.6.1: a bounded closed convex set in finite-dimensional Euclidean
space has no nonzero recession direction. -/
lemma helperForCorollary_37_6_1_nonzero_not_mem_recessionCone_of_bounded_closed_convex
    {k : ℕ} {C : Set (EuclideanSpace ℝ (Fin k))}
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hCbdd : Bornology.IsBounded C) {w : EuclideanSpace ℝ (Fin k)} (hw : w ≠ 0) :
    w ∉ Set.recessionCone C := by
  -- Route correction: the assigned part file has no `Corollary 37.6.1` skeleton, so we package
  -- the boundedness-to-trivial-recession step here for the later 37.6 proof route.
  have hRecession :
      Set.recessionCone C = ({0} : Set (EuclideanSpace ℝ (Fin k))) :=
    recessionCone_eq_singleton_zero_of_bounded
      (n := k) (C := C) hCne hCclosed hCconv hCbdd
  -- Rewriting through the singleton characterization reduces the claim to `w ≠ 0`.
  rw [hRecession]
  simpa [Set.mem_singleton_iff] using hw

/-- Helper for Corollary 37.6.1: the same bounded-recession obstruction holds on the coordinate
space `Fin k → ℝ`, which is the form used by effective domains in Section 37. -/
lemma helperForCorollary_37_6_1_nonzero_not_mem_recessionCone_of_bounded_closed_convex_fin
    {k : ℕ} {C : Set (Fin k → ℝ)}
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hCbdd : Bornology.IsBounded C) {w : Fin k → ℝ} (hw : w ≠ 0) :
    w ∉ Set.recessionCone C := by
  let e : EuclideanSpace ℝ (Fin k) ≃L[ℝ] (Fin k → ℝ) :=
    EuclideanSpace.equiv (ι := Fin k) (𝕜 := ℝ)
  let C' : Set (EuclideanSpace ℝ (Fin k)) := e ⁻¹' C
  have hCimage : e '' C' = C := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [C', Set.preimage] using hy
    · intro hx
      refine ⟨e.symm x, ?_, by simp⟩
      simpa [C', Set.preimage] using hx
  have hCne' : C'.Nonempty := by
    rcases hCne with ⟨x, hx⟩
    refine ⟨e.symm x, ?_⟩
    simpa [C', Set.preimage] using hx
  have hCclosed' : IsClosed C' := by
    -- Transport closedness from coordinates back to the Euclidean model.
    simpa [C', Set.preimage] using hCclosed.preimage e.continuous
  have hCconv' : Convex ℝ C' := by
    -- Linear preimages of convex sets stay convex under the coordinate equivalence.
    simpa [C'] using (Convex.linear_preimage (s := C) hCconv e.toLinearMap)
  have hCbdd' : Bornology.IsBounded C' := by
    -- The inverse coordinate map is Lipschitz, so boundedness is preserved.
    simpa [C', ContinuousLinearEquiv.image_symm_eq_preimage] using
      e.symm.lipschitz.isBounded_image hCbdd
  intro hwRec
  have hw' : e.symm w ≠ 0 := by
    intro hw0
    apply hw
    simpa using congrArg e hw0
  have hRecEq :
      Set.recessionCone C = e '' Set.recessionCone C' := by
    simpa [hCimage] using recessionCone_image_linearEquiv (e := e.toLinearEquiv) (C := C')
  have hwRecImage : w ∈ e '' Set.recessionCone C' := by
    simpa [hRecEq] using hwRec
  rcases hwRecImage with ⟨y, hy, hyw⟩
  have hyEq : y = e.symm w := by
    simpa using congrArg e.symm hyw
  have hwRec' : e.symm w ∈ Set.recessionCone C' := by
    simpa [hyEq] using hy
  -- Apply the Euclidean-space version to the transported set and transported direction.
  exact
    (helperForCorollary_37_6_1_nonzero_not_mem_recessionCone_of_bounded_closed_convex
      (C := C') hCne' hCclosed' hCconv' hCbdd' (w := e.symm w) hw') hwRec'

/-- Helper for Corollary 37.6.1: bounded closed convex coordinate domains have only the trivial
recession direction in each coordinate block. -/
lemma helperForCorollary_37_6_1_nonzero_not_mem_recessionCones_of_bounded_closed_convex_domains
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hCbdd : Bornology.IsBounded C)
    (hDne : D.Nonempty) (hDclosed : IsClosed D) (hDconv : Convex ℝ D)
    (hDbdd : Bornology.IsBounded D) :
    (∀ z : Fin m → ℝ, z ≠ 0 → z ∉ Set.recessionCone C) ∧
      (∀ w : Fin n → ℝ, w ≠ 0 → w ∉ Set.recessionCone D) := by
  constructor
  · intro z hz
    -- Apply the coordinate-space boundedness lemma to the first effective domain.
    exact
      helperForCorollary_37_6_1_nonzero_not_mem_recessionCone_of_bounded_closed_convex_fin
        (C := C) hCne hCclosed hCconv hCbdd (w := z) hz
  · intro w hw
    -- The same boundedness argument applies to the second effective domain.
    exact
      helperForCorollary_37_6_1_nonzero_not_mem_recessionCone_of_bounded_closed_convex_fin
        (C := D) hDne hDclosed hDconv hDbdd (w := w) hw

/-- Helper for Corollary 37.6.1: closed proper saddle-functions admit subtype witnesses in the
intrinsic interiors of both effective coordinate domains, matching the witness types used later
by Theorems 37.3 and 37.6. -/
lemma helperForCorollary_37_6_1_intrinsicInteriorSubtype_nonempty
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K) :
    Nonempty {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)} ∧
      Nonempty {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)} := by
  rcases
      helperForTheorem_37_2_intrinsicInterior_nonempty
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) with
    ⟨hFirst, hSecond⟩
  constructor
  · rcases hFirst with ⟨u, hu⟩
    -- Repackage the first-domain set witness into the subtype format used by later existence statements.
    exact ⟨⟨u, hu⟩⟩
  · rcases hSecond with ⟨v, hv⟩
    -- The second-domain witness is packaged in the same subtype form.
    exact ⟨⟨v, hv⟩⟩

/-- Helper for Corollary 37.6.1: a bounded closed proper convex function has no nonzero
recession directions, because any nonzero recession direction would already be a recession
direction of a nonempty bounded real sublevel set. -/
lemma helperForCorollary_37_6_1_nonzero_not_isRecessionDirection_of_bounded_closedProperConvex
    {k : ℕ} {g : (Fin k → ℝ) → EReal} {D : Set (Fin k → ℝ)}
    (hg : IsProperClosedConvexFunctionWithDomain g D)
    (hDne : D.Nonempty) (hDbdd : Bornology.IsBounded D) {w : Fin k → ℝ} (hw : w ≠ 0) :
    ¬ IsRecessionDirection g w := by
  have hConvFun : ConvexFunction g := by
    -- The Jensen inequality on `univ` is exactly the ordinary convex-function structure.
    simpa [ConvexFunction] using
      (helperForTheorem_37_2_convexFunctionOn_univ_of_IsERealConvexOn (f := g) hg.1)
  have hLsc : LowerSemicontinuous g := by
    -- Closedness means that `g` is already fixed by the convex-closure operator, whose output is
    -- lower semicontinuous by construction.
    rw [hg.2.1]
    exact helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := g)
  have hClosed : ClosedConvexFunction g := ⟨hConvFun, hLsc⟩
  have hProper : ProperConvexFunctionOn (Set.univ : Set (Fin k → ℝ)) g := by
    have hEpigraphNonempty : Set.Nonempty (epigraph (Set.univ : Set (Fin k → ℝ)) g) := by
      refine
        (nonempty_epigraph_iff_nonempty_effectiveDomain (S := (Set.univ : Set (Fin k → ℝ)))
          (f := g)).2 ?_
      rcases hDne with ⟨x0, hx0D⟩
      have hx0Dom : x0 ∈ convexFunctionEffectiveDomain g := by
        rwa [← hg.2.2.2] at hx0D
      refine ⟨x0, ?_⟩
      simpa [convexFunctionEffectiveDomain, effectiveDomain_eq] using hx0Dom
    have hNoBotOnUniv : ∀ x ∈ Set.univ, g x ≠ (⊥ : EReal) := by
      intro x _hx
      exact hg.2.2.1 x
    exact
      ⟨helperForTheorem_37_2_convexFunctionOn_univ_of_IsERealConvexOn (f := g) hg.1,
        hEpigraphNonempty, hNoBotOnUniv⟩
  intro hRec
  rcases hDne with ⟨x0, hx0⟩
  have hx0Dom : x0 ∈ convexFunctionEffectiveDomain g := by
    rwa [← hg.2.2.2] at hx0
  have hx0Top : g x0 ≠ (⊤ : EReal) := by
    simpa [convexFunctionEffectiveDomain, lt_top_iff_ne_top] using hx0Dom
  have hx0Sublevel : x0 ∈ sublevelSetEReal g (g x0).toReal := by
    -- The chosen domain point gives a concrete real sublevel containing that point.
    change g x0 ≤ (((g x0).toReal : ℝ) : EReal)
    rw [EReal.coe_toReal (x := g x0) hx0Top (hg.2.2.1 x0)]
  have hSublevelNonempty : (sublevelSetEReal g (g x0).toReal).Nonempty := ⟨x0, hx0Sublevel⟩
  have hSublevelClosed : IsClosed (sublevelSetEReal g (g x0).toReal) := by
    -- Lower semicontinuity makes every real sublevel closed.
    exact (lowerSemicontinuous_iff_closed_sublevel (f := g)).1 hClosed.2 (g x0).toReal
  have hSublevelConvex : Convex ℝ (sublevelSetEReal g (g x0).toReal) := by
    -- Convexity of `g` gives convexity of each real sublevel.
    simpa [sublevelSetEReal] using
      (convexFunction_level_sets_convex
        (f := g) hClosed.1 (α := (((g x0).toReal : ℝ) : EReal))).2
  have hSublevelSubset : sublevelSetEReal g (g x0).toReal ⊆ D := by
    intro x hx
    rw [← hg.2.2.2]
    -- Any point below a finite real level automatically lies in the effective domain.
    change g x < (⊤ : EReal)
    exact lt_of_le_of_lt hx (EReal.coe_lt_top (g x0).toReal)
  have hSublevelBounded : Bornology.IsBounded (sublevelSetEReal g (g x0).toReal) :=
    hDbdd.subset hSublevelSubset
  have hRecSublevel : w ∈ Set.recessionCone (sublevelSetEReal g (g x0).toReal) := by
    -- Read the function-level recession statement back as a sublevel-set recession statement.
    exact
      (helperForCorollary_6_27_5_sublevel_recession_iff_functionRecession
        (g := g) hClosed hProper hSublevelNonempty).2 hRec
  exact
    (helperForCorollary_37_6_1_nonzero_not_mem_recessionCone_of_bounded_closed_convex_fin
      (C := sublevelSetEReal g (g x0).toReal) hSublevelNonempty hSublevelClosed
      hSublevelConvex hSublevelBounded (w := w) hw) hRecSublevel

/-- Helper for Corollary 37.6.1: if the second effective domain is bounded, then no nonzero
vector can be a recession direction of any relative-interior second slice `K(u, ·)`. -/
lemma helperForCorollary_37_6_1_nonzero_not_isRecessionDirection_secondSlice_of_bounded_domain
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (hDbdd : Bornology.IsBounded (effectiveDomain₂ K))
    (u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)})
    {w : Fin n → ℝ} (hw : w ≠ 0) :
    ¬ IsRecessionDirection (K u.1) w := by
  have hSlice : IsProperClosedConvexFunctionWithDomain (K u.1) (effectiveDomain₂ K) :=
    helperForTheorem_37_2_convexSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal u.2
  have hDne : (effectiveDomain₂ K).Nonempty :=
    helperForTheorem_37_2_secondDomain_nonempty (K := K) hKproper
  -- Apply the bounded-domain obstruction to the concrete second slice through `u`.
  exact
    helperForCorollary_37_6_1_nonzero_not_isRecessionDirection_of_bounded_closedProperConvex
      (g := K u.1) (D := effectiveDomain₂ K) hSlice hDne hDbdd hw

/-- Helper for Corollary 37.6.1: if the first effective domain is bounded, then no nonzero
vector can be a recession direction of any relative-interior negated first slice `u ↦ -K(u, v)`. -/
lemma helperForCorollary_37_6_1_nonzero_not_isRecessionDirection_negatedFirstSlice_of_bounded_domain
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (hCbdd : Bornology.IsBounded (effectiveDomain₁ K))
    (v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)})
    {z : Fin m → ℝ} (hz : z ≠ 0) :
    ¬ IsRecessionDirection (fun u => -K u v.1) z := by
  have hSlice :
      IsProperClosedConvexFunctionWithDomain (fun u => -K u v.1) (effectiveDomain₁ K) :=
    helperForTheorem_37_2_negatedFirstSlice_on_intrinsicInterior
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal v.2
  have hCne : (effectiveDomain₁ K).Nonempty :=
    helperForTheorem_37_2_firstDomain_nonempty (K := K) hKproper
  -- The same bounded-domain argument applies to the sign-twisted first slices.
  exact
    helperForCorollary_37_6_1_nonzero_not_isRecessionDirection_of_bounded_closedProperConvex
      (g := fun u => -K u v.1) (D := effectiveDomain₁ K) hSlice hCne hCbdd hz

/-- Helper for Corollary 37.6.1: bounded effective coordinate domains provide exactly the two
no-common-recession hypotheses required later by Theorems 37.3 and 37.6. -/
lemma helperForCorollary_37_6_1_bounded_effectiveDomains_yield_bothNoCommonRecessionConditions
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hGlobal : Section34Theorem34_2GlobalQualification m n)
    (hCbdd : Bornology.IsBounded (effectiveDomain₁ K))
    (hDbdd : Bornology.IsBounded (effectiveDomain₂ K)) :
    (∀ w : Fin n → ℝ, w ≠ 0 →
      ∃ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
        ¬ IsRecessionDirection (K u.1) w) ∧
      (∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) := by
  rcases helperForCorollary_37_6_1_intrinsicInteriorSubtype_nonempty
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) with ⟨hUne, hVne⟩
  constructor
  · intro w hw
    rcases hUne with ⟨u⟩
    -- Any intrinsic-interior first-domain witness suffices once boundedness rules out
    -- nonzero recession directions for every second slice.
    refine ⟨u, ?_⟩
    exact
      helperForCorollary_37_6_1_nonzero_not_isRecessionDirection_secondSlice_of_bounded_domain
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hDbdd u hw
  · intro z hz
    rcases hVne with ⟨v⟩
    -- The same fixed witness works for the negated first-slice family.
    refine ⟨v, ?_⟩
    exact
      helperForCorollary_37_6_1_nonzero_not_isRecessionDirection_negatedFirstSlice_of_bounded_domain
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hGlobal hCbdd v hz

/-- Helper for Corollary 37.6.1: bounded effective coordinate domains already imply the finite
common saddle-value conclusion from the earlier Section 37.3 minimax theorem. -/
lemma helperForCorollary_37_6_1_finiteSaddleValue_of_bounded_effectiveDomains
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hCbdd : Bornology.IsBounded (effectiveDomain₁ K))
    (hDbdd : Bornology.IsBounded (effectiveDomain₂ K)) :
    minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
        maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ∧
      minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊤ : EReal) ∧
        minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K ≠ (⊥ : EReal) := by
  rcases
      helperForCorollary_37_6_1_bounded_effectiveDomains_yield_bothNoCommonRecessionConditions
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ.primalGlobal hCbdd hDbdd with
    ⟨hNoCommonSecond, hNoCommonFirst⟩
  have h373 :=
    section37_theorem37_3 (K := K) (hKclosed := hKclosed) (hKproper := hKproper)
      hQ (Or.inl hNoCommonSecond)
  -- Section 37.3 gives the minimax equality once one recession obstruction holds.
  refine ⟨h373.1, ?_⟩
  -- Boundedness supplies both obstructions, so the same theorem gives finiteness.
  exact h373.2 ⟨hNoCommonSecond, hNoCommonFirst⟩

/-- Helper for Corollary 37.6.1: once bounded effective domains force a finite common
extended-real saddle value, both minimax and maximin are recovered by coercing the minimax
value's real part back into `EReal`. -/
lemma helperForCorollary_37_6_1_commonSaddleValue_eq_minimax_toReal_of_bounded_effectiveDomains
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hCbdd : Bornology.IsBounded (effectiveDomain₁ K))
    (hDbdd : Bornology.IsBounded (effectiveDomain₂ K)) :
    minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
        ((((minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K).toReal : ℝ)) : EReal) ∧
      maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
        ((((minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K).toReal : ℝ)) : EReal) := by
  rcases
      helperForCorollary_37_6_1_finiteSaddleValue_of_bounded_effectiveDomains
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hCbdd hDbdd with
    ⟨hMinimaxEq, hMinimaxNeTop, hMinimaxNeBot⟩
  constructor
  · -- The finite minimax value is exactly the coercion of its ordinary real part.
    exact
      (EReal.coe_toReal
        (x := minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K)
        hMinimaxNeTop hMinimaxNeBot).symm
  · -- The maximin value shares the same coercion because Section 37.3 already identified them.
    calc
      maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K =
          minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K := hMinimaxEq.symm
      _ =
          ((((minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K).toReal : ℝ)) : EReal) :=
        (EReal.coe_toReal
          (x := minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K)
          hMinimaxNeTop hMinimaxNeBot).symm

/-- Helper for Corollary 37.6.1: bounded effective coordinate domains therefore yield a genuine
real number representing the common minimax-maximin value. -/
lemma helperForCorollary_37_6_1_exists_real_commonSaddleValue_of_bounded_effectiveDomains
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hCbdd : Bornology.IsBounded (effectiveDomain₁ K))
    (hDbdd : Bornology.IsBounded (effectiveDomain₂ K)) :
    ∃ α : ℝ,
      minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K = (α : EReal) ∧
        maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K = (α : EReal) := by
  refine ⟨(minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K).toReal, ?_⟩
  -- The new conversion helper packages both equalities with the same real witness.
  exact
    helperForCorollary_37_6_1_commonSaddleValue_eq_minimax_toReal_of_bounded_effectiveDomains
      (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hCbdd hDbdd

/-- Helper for Corollary 37.6.1: this part file already packages the bounded-domain recession
obstructions together with the finite real common saddle-value conclusion, leaving only the later
Section 37.6 saddle-point existence bridge to be supplied elsewhere. -/
lemma helperForCorollary_37_6_1_bounded_effectiveDomains_package_part9_consequences
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hCbdd : Bornology.IsBounded (effectiveDomain₁ K))
    (hDbdd : Bornology.IsBounded (effectiveDomain₂ K)) :
    (∀ w : Fin n → ℝ, w ≠ 0 →
      ∃ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
        ¬ IsRecessionDirection (K u.1) w) ∧
      (∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) ∧
      ∃ α : ℝ,
        minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K = (α : EReal) ∧
          maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K = (α : EReal) := by
  -- First collect the two recession obstructions already derived from bounded effective domains.
  rcases
      helperForCorollary_37_6_1_bounded_effectiveDomains_yield_bothNoCommonRecessionConditions
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ.primalGlobal hCbdd hDbdd with
    ⟨hNoCommonSecond, hNoCommonFirst⟩
  -- Then pair them with the finite real minimax-maximin value supplied by Section 37.3.
  rcases
      helperForCorollary_37_6_1_exists_real_commonSaddleValue_of_bounded_effectiveDomains
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hCbdd hDbdd with
    ⟨α, hMinimax, hMaximin⟩
  exact ⟨hNoCommonSecond, hNoCommonFirst, α, hMinimax, hMaximin⟩

/-- Helper for Corollary 37.6.2: bounded effective coordinate domains already provide the exact
two recession hypotheses required by the later Section 37.6 saddle-point existence theorem. -/
lemma helperForCorollary_37_6_2_bounded_effectiveDomains_yield_theorem37_6_hypotheses
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hCbdd : Bornology.IsBounded (effectiveDomain₁ K))
    (hDbdd : Bornology.IsBounded (effectiveDomain₂ K)) :
    (∀ w : Fin n → ℝ, w ≠ 0 →
      ∃ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
        ¬ IsRecessionDirection (K u.1) w) ∧
      (∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) := by
  -- Route correction: the main `Corollary 37.6.2` declaration is absent from this part file, so
  -- we isolate here the exact theorem-37.6 recession inputs that bounded effective domains supply.
  rcases
      helperForCorollary_37_6_1_bounded_effectiveDomains_package_part9_consequences
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hCbdd hDbdd with
    ⟨hNoCommonSecond, hNoCommonFirst, α, hMinimax, hMaximin⟩
  -- Only the two recession clauses are needed for the later existence bridge.
  exact ⟨hNoCommonSecond, hNoCommonFirst⟩

/-- Helper for Corollary 37.6.2: bounded effective coordinate domains also provide a real common
minimax-maximin value, so the eventual corollary proof only needs the later existence bridge. -/
lemma helperForCorollary_37_6_2_exists_real_commonSaddleValue_of_bounded_effectiveDomains
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hCbdd : Bornology.IsBounded (effectiveDomain₁ K))
    (hDbdd : Bornology.IsBounded (effectiveDomain₂ K)) :
    ∃ α : ℝ,
      minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K = (α : EReal) ∧
        maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K = (α : EReal) := by
  -- Read off the common real saddle value from the existing part-9 bounded-domain package.
  rcases
      helperForCorollary_37_6_1_bounded_effectiveDomains_package_part9_consequences
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hCbdd hDbdd with
    ⟨hNoCommonSecond, hNoCommonFirst, α, hMinimax, hMaximin⟩
  -- The packaged witness can be returned directly.
  exact ⟨α, hMinimax, hMaximin⟩

/-- Helper for Corollary 37.6.2: this part file already packages every bounded-domain consequence
needed before the later Section 37.6 saddle-point existence bridge can be invoked. -/
lemma helperForCorollary_37_6_2_bounded_effectiveDomains_package_part9_consequences
    (K : SaddleFunction m n)
    (hKclosed : IsClosedSaddleFunction K)
    (hKproper : IsProperSaddleFunction K)
    (hQ : Section37Theorem37_2Qualification K)
    (hCbdd : Bornology.IsBounded (effectiveDomain₁ K))
    (hDbdd : Bornology.IsBounded (effectiveDomain₂ K)) :
    (∀ w : Fin n → ℝ, w ≠ 0 →
      ∃ u : {u // u ∈ intrinsicInterior ℝ (effectiveDomain₁ K)},
        ¬ IsRecessionDirection (K u.1) w) ∧
      (∀ z : Fin m → ℝ, z ≠ 0 →
        ∃ v : {v // v ∈ intrinsicInterior ℝ (effectiveDomain₂ K)},
          ¬ IsRecessionDirection (fun u => -K u v.1) z) ∧
      ∃ α : ℝ,
        minimaxValue (C := Fin m → ℝ) (D := Fin n → ℝ) K = (α : EReal) ∧
          maximinValue (C := Fin m → ℝ) (D := Fin n → ℝ) K = (α : EReal) := by
  -- First extract the exact no-common-recession hypotheses that bounded effective domains give.
  rcases
      helperForCorollary_37_6_2_bounded_effectiveDomains_yield_theorem37_6_hypotheses
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hCbdd hDbdd with
    ⟨hNoCommonSecond, hNoCommonFirst⟩
  -- Then pair them with the already packaged real common saddle value.
  rcases
      helperForCorollary_37_6_2_exists_real_commonSaddleValue_of_bounded_effectiveDomains
        (K := K) (hKclosed := hKclosed) (hKproper := hKproper) hQ hCbdd hDbdd with
    ⟨α, hMinimax, hMaximin⟩
  exact ⟨hNoCommonSecond, hNoCommonFirst, α, hMinimax, hMaximin⟩

/-- Helper for Corollary 37.5.1: the packed ordinary subgradient condition is equivalent to the
explicit tilted-fiber lower bound on `F u' x' - ⟪x', v⟫ + ⟪u', uStar⟫`. -/
lemma helperForCorollary_37_5_1_packedSubgradientMem_iff_tiltedFiberLowerBound
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) (uStar : Fin m → ℝ) (vStar : Fin n → ℝ) :
    dotProductEquiv ℝ (Fin (m + n)) (Fin.append (-uStar) v) ∈
        subdifferentialAt (graphFunctionOfBifunction F) (Fin.append u vStar) ↔
      ∀ u' x',
        F u' x' - ((dotProduct x' v : ℝ) : EReal) + ((dotProduct u' uStar : ℝ) : EReal) ≥
          F u vStar - ((dotProduct vStar v : ℝ) : EReal) + ((dotProduct u uStar : ℝ) : EReal) := by
  rw [mem_subdifferentialAt_iff]
  constructor
  · intro hSub u' x'
    let leftAffine : EReal :=
      ((dotProduct u uStar : ℝ) : EReal) - ((dotProduct vStar v : ℝ) : EReal)
    let rightAffine : EReal :=
      ((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct x' v : ℝ) : EReal)
    have hAffineReal :
        (((dotProduct x' v : ℝ) - dotProduct vStar v) - (dotProduct u' uStar - dotProduct u uStar) : ℝ) =
          ((dotProduct u uStar - dotProduct vStar v) - (dotProduct u' uStar - dotProduct x' v) : ℝ) := by
      ring
    have hAffineEReal :
        ((((dotProduct x' v : ℝ) : EReal) - ((dotProduct vStar v : ℝ) : EReal)) -
            (((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct u uStar : ℝ) : EReal))) =
          leftAffine - rightAffine := by
      have hLeft :
          ((((dotProduct x' v : ℝ) : EReal) - ((dotProduct vStar v : ℝ) : EReal)) -
              (((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct u uStar : ℝ) : EReal))) =
            (((((dotProduct x' v : ℝ) - dotProduct vStar v) -
                (dotProduct u' uStar - dotProduct u uStar) : ℝ)) : EReal) := by
        repeat rw [← EReal.coe_sub]
      have hRight :
          leftAffine - rightAffine =
            (((((dotProduct u uStar - dotProduct vStar v) -
                (dotProduct u' uStar - dotProduct x' v) : ℝ)) : EReal)) := by
        simp [leftAffine, rightAffine]
        repeat rw [← EReal.coe_sub]
      have hCast :
          (((((dotProduct x' v : ℝ) - dotProduct vStar v) - (dotProduct u' uStar - dotProduct u uStar) : ℝ)) :
              EReal) =
            (((((dotProduct u uStar - dotProduct vStar v) - (dotProduct u' uStar - dotProduct x' v) : ℝ)) :
              EReal)) := by
        exact_mod_cast hAffineReal
      exact hLeft.trans (hCast.trans hRight.symm)
    have hPacked :
        F u' x' ≥
          F u vStar +
            (((dotProductEquiv ℝ (Fin (m + n)) (Fin.append (-uStar) v)
                (Fin.append u' x' - Fin.append u vStar) : ℝ)) : EReal) := by
      simpa [graphFunctionOfBifunction] using hSub (Fin.append u' x')
    have hAtPacked :
        F u vStar + (leftAffine - rightAffine) ≤ F u' x' := by
      rw [helperForCorollary_37_5_1_packedDotIncrement_eq_splitAffineTerm
        (u := u) (v := v) (uStar := uStar) (vStar := vStar) (u' := u') (x' := x')] at hPacked
      rw [hAffineEReal] at hPacked
      exact hPacked
    have hSubForm :
        F u vStar + leftAffine - (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) ≤
          F u' x' := by
      simpa [leftAffine, rightAffine, EReal.coe_sub, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using hAtPacked
    have hRearranged :
        F u vStar + leftAffine ≤ F u' x' + (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) := by
      -- Add back the right-hand affine term to recover the textbook lower-bound shape.
      have hAdded :
          (F u vStar + leftAffine - (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) +
              (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) ≤
            F u' x' + (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) :=
        (EReal.addLECancellable_coe (dotProduct u' uStar - dotProduct x' v : ℝ)).add_le_add_iff_right.2
          hSubForm
      have hCancelR :
          -((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) +
              ((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) = 0 := by
        have hneg :
            -((((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct x' v : ℝ) : EReal))) =
              (((dotProduct x' v : ℝ) : EReal) - ((dotProduct u' uStar : ℝ) : EReal)) := by
          change -((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) =
            ((((dotProduct x' v - dotProduct u' uStar : ℝ)) : EReal))
          have hreal : (-(dotProduct u' uStar - dotProduct x' v) : ℝ) =
              dotProduct x' v - dotProduct u' uStar := by
            ring
          exact_mod_cast hreal
        rw [show ((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) =
            (((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct x' v : ℝ) : EReal)) by
              rw [EReal.coe_sub]]
        rw [hneg]
        change (((dotProduct x' v - dotProduct u' uStar : ℝ)) : EReal) +
            (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) = 0
        rw [← EReal.coe_add]
        norm_num
      have hCancel :
          (F u vStar + leftAffine - (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) +
              (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) =
            F u vStar + leftAffine := by
        rw [sub_eq_add_neg]
        calc
          F u vStar + leftAffine + -((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) +
              ((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) =
              F u vStar + leftAffine +
                (-((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) +
                  ((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal))) := by
                    ac_rfl
          _ = F u vStar + leftAffine + 0 := by rw [hCancelR]
          _ = F u vStar + leftAffine := by simp
      rw [hCancel] at hAdded
      exact hAdded
    simpa [leftAffine, rightAffine, EReal.coe_sub, sub_eq_add_neg, add_assoc, add_left_comm,
      add_comm] using hRearranged
  · intro hLower z
    let u' : Fin m → ℝ := fun i => z (Fin.castAdd n i)
    let x' : Fin n → ℝ := fun j => z (Fin.natAdd m j)
    let leftAffine : EReal :=
      ((dotProduct u uStar : ℝ) : EReal) - ((dotProduct vStar v : ℝ) : EReal)
    let rightAffine : EReal :=
      ((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct x' v : ℝ) : EReal)
    have hAffineReal :
        (((dotProduct x' v : ℝ) - dotProduct vStar v) - (dotProduct u' uStar - dotProduct u uStar) : ℝ) =
          ((dotProduct u uStar - dotProduct vStar v) - (dotProduct u' uStar - dotProduct x' v) : ℝ) := by
      ring
    have hAffineEReal :
        ((((dotProduct x' v : ℝ) : EReal) - ((dotProduct vStar v : ℝ) : EReal)) -
            (((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct u uStar : ℝ) : EReal))) =
          leftAffine - rightAffine := by
      have hLeft :
          ((((dotProduct x' v : ℝ) : EReal) - ((dotProduct vStar v : ℝ) : EReal)) -
              (((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct u uStar : ℝ) : EReal))) =
            (((((dotProduct x' v : ℝ) - dotProduct vStar v) -
                (dotProduct u' uStar - dotProduct u uStar) : ℝ)) : EReal) := by
        repeat rw [← EReal.coe_sub]
      have hRight :
          leftAffine - rightAffine =
            (((((dotProduct u uStar - dotProduct vStar v) -
                (dotProduct u' uStar - dotProduct x' v) : ℝ)) : EReal)) := by
        simp [leftAffine, rightAffine]
        repeat rw [← EReal.coe_sub]
      have hCast :
          (((((dotProduct x' v : ℝ) - dotProduct vStar v) - (dotProduct u' uStar - dotProduct u uStar) : ℝ)) :
              EReal) =
            (((((dotProduct u uStar - dotProduct vStar v) - (dotProduct u' uStar - dotProduct x' v) : ℝ)) :
              EReal)) := by
        exact_mod_cast hAffineReal
      exact hLeft.trans (hCast.trans hRight.symm)
    have hAtSplit :
        F u vStar + leftAffine ≤ F u' x' + (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) := by
      simpa [leftAffine, rightAffine, EReal.coe_sub, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using hLower u' x'
    have hSubForm :
        F u vStar + leftAffine - (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) ≤
          F u' x' := by
      have hExpanded :
          (F u vStar + leftAffine - (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) +
              (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) ≤
            F u' x' + (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) := by
        have hExpandEq :
            (F u vStar + leftAffine - (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) +
                (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) =
              F u vStar + leftAffine := by
          rw [sub_eq_add_neg]
          have hCancelR :
              -((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) +
                  ((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) = 0 := by
            have hneg :
                -((((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct x' v : ℝ) : EReal))) =
                  (((dotProduct x' v : ℝ) : EReal) - ((dotProduct u' uStar : ℝ) : EReal)) := by
              change -((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) =
                ((((dotProduct x' v - dotProduct u' uStar : ℝ)) : EReal))
              have hreal : (-(dotProduct u' uStar - dotProduct x' v) : ℝ) =
                  dotProduct x' v - dotProduct u' uStar := by
                ring
              exact_mod_cast hreal
            rw [show ((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) =
                (((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct x' v : ℝ) : EReal)) by
                  rw [EReal.coe_sub]]
            rw [hneg]
            change (((dotProduct x' v - dotProduct u' uStar : ℝ)) : EReal) +
                (((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal) = 0
            rw [← EReal.coe_add]
            norm_num
          calc
            F u vStar + leftAffine + -((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) +
                ((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) =
                F u vStar + leftAffine +
                  (-((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal)) +
                    ((((dotProduct u' uStar - dotProduct x' v : ℝ)) : EReal))) := by
                      ac_rfl
            _ = F u vStar + leftAffine + 0 := by rw [hCancelR]
            _ = F u vStar + leftAffine := by simp
        rw [hExpandEq]
        exact hAtSplit
      exact
        (EReal.addLECancellable_coe (dotProduct u' uStar - dotProduct x' v : ℝ)).add_le_add_iff_right.1
          hExpanded
    have hAtPacked :
        F u vStar + (leftAffine - rightAffine) ≤ F u' x' := by
      simpa [leftAffine, rightAffine, EReal.coe_sub, sub_eq_add_neg, add_assoc, add_left_comm,
        add_comm] using hSubForm
    have hPackedSplit :
        F u vStar +
            (((dotProductEquiv ℝ (Fin (m + n)) (Fin.append (-uStar) v)
                (Fin.append u' x' - Fin.append u vStar) : ℝ)) : EReal) ≤
          F u' x' := by
      have hPackedAffine :
          F u vStar +
              ((((dotProduct x' v : ℝ) : EReal) - ((dotProduct vStar v : ℝ) : EReal)) -
                (((dotProduct u' uStar : ℝ) : EReal) - ((dotProduct u uStar : ℝ) : EReal))) ≤
            F u' x' := by
        rw [hAffineEReal]
        exact hAtPacked
      rw [helperForCorollary_37_5_1_packedDotIncrement_eq_splitAffineTerm
        (u := u) (v := v) (uStar := uStar) (vStar := vStar) (u' := u') (x' := x')]
      exact hPackedAffine
    -- Rewrite an arbitrary packed point as its first and second coordinate blocks.
    simpa [u', x', graphFunctionOfBifunction, helperForLemma33_0_14_append_split_eq] using hPackedSplit

/-- Helper for Corollary 37.5.1: second-partial membership for the canonical pairing is exactly
attainment of the Fenchel kernel at the dual point `vStar`. -/
lemma helperForCorollary_37_5_1_secondPartialMem_iff_pairingAttainment
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (u : Fin m → ℝ) (v : Fin n → ℝ) (vStar : Fin n → ℝ) :
    vStar ∈ partialSubdifferentialInSecondVariable (convexBifunctionPairing F) u v ↔
      convexBifunctionPairing F u v =
        (((dotProduct vStar v : ℝ) : EReal) - F u vStar) := by
  rcases hF with ⟨hRock, hNoBot, hClosedSections⟩
  by_cases hAllTop : ∀ x : Fin n → ℝ, F u x = ⊤
  · have hPairBot : convexBifunctionPairing F u = fun _ : Fin n → ℝ => (⊥ : EReal) := by
      -- If the whole primal section is `⊤`, its pairing conjugate collapses to the constant `⊥`.
      funext y
      rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
      apply le_antisymm
      · refine iSup_le ?_
        intro x
        simp [hAllTop]
      · exact bot_le
    constructor
    · intro _
      -- In the degenerate all-`⊤` case, the displayed equality is exactly `⊥ = ⊥`.
      have hPairBotAt : convexBifunctionPairing F u v = (⊥ : EReal) := by
        simpa using congrArg (fun g => g v) hPairBot
      simpa [hPairBotAt, hAllTop]
    · intro _
      -- The same degenerate case makes every second-partial inequality tautological.
      intro v'
      have hPairBotAt : convexBifunctionPairing F u v = (⊥ : EReal) := by
        simpa using congrArg (fun g => g v) hPairBot
      have hPairBotAt' : convexBifunctionPairing F u v' = (⊥ : EReal) := by
        simpa using congrArg (fun g => g v') hPairBot
      calc
        convexBifunctionPairing F u v +
            ∑ i, ↑(vStar i) * (↑(v' i) - ↑(v i)) =
              (⊥ : EReal) + ∑ i, ↑(vStar i) * (↑(v' i) - ↑(v i)) := by
              rw [hPairBotAt]
        _ = (⊥ : EReal) := by
              simp
        _ ≤ convexBifunctionPairing F u v' := by
              simpa [hPairBotAt'] using (bot_le : (⊥ : EReal) ≤ ⊥)
  · rcases not_forall.mp hAllTop with ⟨x0, hx0⟩
    have hx0_ne_top : F u x0 ≠ (⊤ : EReal) := by
      simpa using hx0
    have hConvFun : ConvexFunction (F u) :=
      helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction (hRock.1 u)
    have hConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (F u) := by
      -- The fixed section `F u` is convex on all of `ℝ^n`.
      simpa [ConvexFunction] using hConvFun
    have hx0dom : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u) := by
      -- A single non-`⊤` point already gives the effective-domain witness needed for properness.
      refine ⟨(F u x0).toReal, ?_⟩
      exact epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ))) (x := x0)
        (μ := (F u x0).toReal) (by simp)
        (by rw [EReal.coe_toReal (x := F u x0) hx0_ne_top (hNoBot u x0)])
    have hSectionProper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (F u) := by
      -- Closed convexity plus one finite point makes the primal section proper.
      refine (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
        (S := (Set.univ : Set (Fin n → ℝ))) (f := F u)).2 ?_
      refine ⟨hConvOn, ⟨x0, hx0dom⟩, ?_⟩
      intro x hx
      constructor
      · exact hNoBot u x
      · exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := F u) hx
    have hPairProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexBifunctionPairing F u) := by
      -- The pairing slice is the Fenchel conjugate of the now-proper primal section.
      simpa [convexBifunctionPairing, helperForTheorem33_1_convexConjugate_eq_fenchelConjugate] using
        (proper_fenchelConjugate_of_proper (n := n) (f := F u) hSectionProper)
    have hClosurePoint : convexConjugate (convexBifunctionPairing F u) vStar = F u vStar := by
      -- Section 33 identifies the conjugate of the pairing slice with the closed primal section.
      have hCorr := (convexBifunction_pairing_correspondence (m := m) (n := n)).1 F hRock hNoBot
      have hPairEq :
          functionConvexClosure (F u) vStar =
            convexConjugate (convexBifunctionPairing F u) vStar :=
        hCorr.2.2 u vStar
      have hSectionPoint : functionConvexClosure (F u) vStar = F u vStar := by
        exact congrArg (fun g => g vStar) (hClosedSections u).symm
      exact hPairEq ▸ hSectionPoint
    constructor
    · intro hvStar
      have hEuclid : IsEuclideanSubgradientAt (convexBifunctionPairing F u) v vStar := by
        -- Rewrite the textbook second partial as ordinary Euclidean subgradient membership.
        have hSlice :
            dotProductEquiv ℝ (Fin n) vStar ∈
              subdifferentialAt (convexBifunctionPairing F u) v := by
          simpa using
            (helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
              (K := convexBifunctionPairing F) (u := u) (v := v) (vStar := vStar)).2 hvStar
        simpa [IsEuclideanSubgradientAt] using hSlice
      have hFY := fenchelYoung_inequality_and_eq_iff_mem_subdifferential
        (g := convexBifunctionPairing F u) hPairProper v vStar
      have hEqFY :
          convexBifunctionPairing F u v +
              fenchelConjugate n (convexBifunctionPairing F u) vStar =
            (((dotProduct v vStar : ℝ) : EReal)) :=
        (hFY.2).2 hEuclid
      have hEqAdd :
          convexBifunctionPairing F u v + F u vStar =
            (((dotProduct v vStar : ℝ) : EReal)) := by
        -- Replace the conjugate of the pairing slice by the original closed section value.
        simpa [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate, hClosurePoint] using hEqFY
      have hPairNotBot : convexBifunctionPairing F u v ≠ (⊥ : EReal) :=
        hPairProper.2.2 v (by simp)
      have hFvTop : F u vStar ≠ (⊤ : EReal) := by
        intro hTop
        have hRealTop : (((dotProduct v vStar : ℝ) : EReal)) = (⊤ : EReal) := by
          simpa [hTop, hPairNotBot] using hEqAdd
        exact EReal.coe_ne_top _ hRealTop
      have hMainLe :
          convexBifunctionPairing F u v ≤
            (((dotProduct v vStar : ℝ) : EReal) - F u vStar) := by
        exact
          (EReal.le_sub_iff_add_le (Or.inl (hNoBot u vStar)) (Or.inl hFvTop)).2
            (le_of_eq hEqAdd)
      have hMainGe :
          (((dotProduct v vStar : ℝ) : EReal) - F u vStar) ≤
            convexBifunctionPairing F u v := by
        exact
          (EReal.sub_le_iff_le_add (Or.inl (hNoBot u vStar)) (Or.inl hFvTop)).2
            (le_of_eq hEqAdd.symm)
      -- The Fenchel-Young equality is precisely the desired attainment identity.
      simpa [dotProduct_comm] using le_antisymm hMainLe hMainGe
    · intro hEq
      have hPairNotBot : convexBifunctionPairing F u v ≠ (⊥ : EReal) := by
        exact hPairProper.2.2 v (by simp)
      have hFvTop : F u vStar ≠ (⊤ : EReal) := by
        intro hTop
        have : convexBifunctionPairing F u v = (⊥ : EReal) := by
          simpa [hTop] using hEq
        exact hPairNotBot this
      have hEq' :
          convexBifunctionPairing F u v =
            (((dotProduct v vStar : ℝ) : EReal) - F u vStar) := by
        simpa [dotProduct_comm] using hEq
      have hEqAdd :
          convexBifunctionPairing F u v +
              fenchelConjugate n (convexBifunctionPairing F u) vStar =
            (((dotProduct v vStar : ℝ) : EReal)) := by
        have hMainLe :
            convexBifunctionPairing F u v + F u vStar ≤
              (((dotProduct v vStar : ℝ) : EReal)) := by
          exact
            (EReal.le_sub_iff_add_le (Or.inl (hNoBot u vStar)) (Or.inl hFvTop)).1
              (le_of_eq hEq')
        have hMainGe :
            (((dotProduct v vStar : ℝ) : EReal)) ≤
              convexBifunctionPairing F u v + F u vStar := by
          exact
            (EReal.sub_le_iff_le_add (Or.inl (hNoBot u vStar)) (Or.inl hFvTop)).1
              (le_of_eq hEq'.symm)
        have hEqAdd' :
            convexBifunctionPairing F u v + F u vStar =
              (((dotProduct v vStar : ℝ) : EReal)) :=
          le_antisymm hMainLe hMainGe
        simpa [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate, hClosurePoint] using hEqAdd'
      have hEuclid : IsEuclideanSubgradientAt (convexBifunctionPairing F u) v vStar :=
        (fenchelYoung_inequality_and_eq_iff_mem_subdifferential
          (g := convexBifunctionPairing F u) hPairProper v vStar).2.1 hEqAdd
      have hSlice :
          dotProductEquiv ℝ (Fin n) vStar ∈
            subdifferentialAt (convexBifunctionPairing F u) v := by
        -- Convert the Euclidean subgradient back to the ordinary subdifferential fiber.
        simpa [IsEuclideanSubgradientAt] using hEuclid
      exact
        (helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
          (K := convexBifunctionPairing F) (u := u) (v := v) (vStar := vStar)).1 hSlice

/-- Helper for Corollary 37.5.1: re-adding the canceled affine term `⟪u',uStar⟫` collapses the
intermediate correction `⟪u,uStar⟫ - ⟪u',uStar⟫` back to the baseline affine anchor. -/
lemma helperForCorollary_37_5_1_readding_uStar_cancels_affineCorrection
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) (uStar : Fin m → ℝ) (vStar : Fin n → ℝ)
    (u' : Fin m → ℝ) :
    (F u vStar - ((dotProduct vStar v : ℝ) : EReal) +
        (((dotProduct u uStar - dotProduct u' uStar : ℝ)) : EReal)) +
        ((dotProduct u' uStar : ℝ) : EReal) =
      F u vStar - ((dotProduct vStar v : ℝ) : EReal) + ((dotProduct u uStar : ℝ) : EReal) := by
  have hCancel :
      (((dotProduct u' uStar : ℝ) : EReal) + -(((dotProduct u' uStar : ℝ) : EReal))) = 0 := by
    -- The re-added finite affine term cancels its negative exactly.
    change ((((dotProduct u' uStar : ℝ) + -(dotProduct u' uStar)) : ℝ) : EReal) = 0
    norm_num
  -- Expand the affine correction, then contract the canceled pair back to zero.
  calc
    (F u vStar - ((dotProduct vStar v : ℝ) : EReal) +
        (((dotProduct u uStar - dotProduct u' uStar : ℝ)) : EReal)) +
        ((dotProduct u' uStar : ℝ) : EReal) =
        F u vStar +
          ((((dotProduct u uStar : ℝ) : EReal) +
            ((((dotProduct u' uStar : ℝ) : EReal) + -(((dotProduct u' uStar : ℝ) : EReal))) +
              -(((dotProduct vStar v : ℝ) : EReal))))) := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, EReal.coe_sub]
    _ = F u vStar +
        ((((dotProduct u uStar : ℝ) : EReal) + (0 + -(((dotProduct vStar v : ℝ) : EReal))))) := by
          rw [hCancel]
    _ = F u vStar - ((dotProduct vStar v : ℝ) : EReal) + ((dotProduct u uStar : ℝ) : EReal) := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Corollary 37.5.1: negating a single endpoint kernel swaps the primal and dual
terms into the tilted-fiber order. -/
lemma helperForCorollary_37_5_1_negatedEndpointKernel_eq_tiltedEndpoint
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u' : Fin m → ℝ) (x' : Fin n → ℝ) (v : Fin n → ℝ) :
    -((((dotProduct x' v : ℝ) : EReal) - F u' x')) =
      F u' x' - ((dotProduct x' v : ℝ) : EReal) := by
  let y : EReal := (((dotProduct x' v : ℝ) : EReal))
  have hyTop : y ≠ (⊤ : EReal) := by
    simpa [y] using EReal.coe_ne_top (dotProduct x' v : ℝ)
  have hyBot : y ≠ (⊥ : EReal) := by
    simpa [y] using EReal.coe_ne_bot (dotProduct x' v : ℝ)
  -- Rewrite the kernel as `y + (-F u' x')` so that `EReal.neg_add` can reverse the sign cleanly.
  rw [show ((((dotProduct x' v : ℝ) : EReal) - F u' x')) = y + -(F u' x') by
        simp [y, sub_eq_add_neg]]
  rw [show F u' x' - ((dotProduct x' v : ℝ) : EReal) = F u' x' - y by simp [y]]
  calc
    -(y + -(F u' x')) = -y - -(F u' x') := by
      exact EReal.neg_add (x := y) (y := -(F u' x')) (Or.inl hyBot) (Or.inl hyTop)
    _ = F u' x' - y := by
      simp [sub_eq_add_neg, add_comm]

/-- Helper for Corollary 37.5.1: this exact one-point `EReal` normalization rewrites the tilted
fiber lower bound into the affine kernel bound used by the pairing supremum, and conversely. -/
lemma helperForCorollary_37_5_1_exactERealKernelTiltNormalization
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) (uStar : Fin m → ℝ) (vStar : Fin n → ℝ)
    (u' : Fin m → ℝ) (x' : Fin n → ℝ) :
    ((((dotProduct x' v : ℝ) : EReal) - F u' x') ≤
        (((dotProduct vStar v : ℝ) : EReal) - F u vStar) +
          (((dotProduct u' uStar - dotProduct u uStar : ℝ)) : EReal)) ↔
      F u' x' - ((dotProduct x' v : ℝ) : EReal) + ((dotProduct u' uStar : ℝ) : EReal) ≥
        F u vStar - ((dotProduct vStar v : ℝ) : EReal) + ((dotProduct u uStar : ℝ) : EReal) := by
  let γ : EReal := ((dotProduct u' uStar : ℝ) : EReal)
  let δ : EReal := ((dotProduct u uStar : ℝ) : EReal)
  have hγTop : γ ≠ (⊤ : EReal) := by
    simpa [γ] using EReal.coe_ne_top (dotProduct u' uStar : ℝ)
  have hγBot : γ ≠ (⊥ : EReal) := by
    simpa [γ] using EReal.coe_ne_bot (dotProduct u' uStar : ℝ)
  have hShift :
      ((((dotProduct x' v : ℝ) : EReal) - F u' x') ≤
          (((dotProduct vStar v : ℝ) : EReal) - F u vStar) + (γ - δ)) ↔
        (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ ≤
          -((((dotProduct x' v : ℝ) : EReal) - F u' x')) + γ) := by
    constructor
    · intro h
      have hneg :
          -(((((dotProduct vStar v : ℝ) : EReal) - F u vStar) + (γ - δ))) ≤
            -((((dotProduct x' v : ℝ) : EReal) - F u' x')) := by
        -- Negating the kernel inequality reverses the order and exposes the affine correction.
        exact (EReal.neg_le_neg_iff).2 h
      have hsub :
          (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ) - γ ≤
            -((((dotProduct x' v : ℝ) : EReal) - F u' x')) := by
        have hRewrite :
            -(((((dotProduct vStar v : ℝ) : EReal) - F u vStar) + (γ - δ))) =
              (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ) - γ := by
          -- Rewrite the negated affine shift into the form handled by `sub_le_iff_le_add`.
          calc
            -(((((dotProduct vStar v : ℝ) : EReal) - F u vStar) + (γ - δ))) =
                -((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) - (γ - δ) := by
                  exact EReal.neg_add (x := (((dotProduct vStar v : ℝ) : EReal) - F u vStar))
                    (y := γ - δ)
                    (Or.inr (by
                      simpa [γ, δ, EReal.coe_sub] using
                        EReal.coe_ne_top
                          ((dotProduct u' uStar - dotProduct u uStar : ℝ))))
                    (Or.inr (by
                      simpa [γ, δ, EReal.coe_sub] using
                        EReal.coe_ne_bot
                          ((dotProduct u' uStar - dotProduct u uStar : ℝ))))
            _ = -((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + (-(γ - δ)) := by
                  simp [sub_eq_add_neg]
            _ = -((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + (-γ + δ) := by
                  rw [EReal.neg_sub (x := γ) (y := δ) (Or.inl hγBot) (Or.inl hγTop)]
            _ = (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ) - γ := by
                  rw [sub_eq_add_neg]
                  calc
                    -((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + (-γ + δ) =
                        (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + -γ) + δ := by
                          rw [← add_assoc]
                    _ = (-γ + -((((dotProduct vStar v : ℝ) : EReal) - F u vStar))) + δ := by
                          rw [add_comm (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar))) (-γ)]
                    _ = -γ + (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ) := by
                          rw [add_assoc]
                    _ = (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ) + -γ := by
                          rw [add_comm (-γ) (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ)]
        rw [hRewrite] at hneg
        exact hneg
      -- Move the finite `⟪u',uStar⟫` term back to the right-hand side.
      exact (EReal.sub_le_iff_le_add (h₁ := Or.inl hγBot) (h₂ := Or.inl hγTop)).1 hsub
    · intro h
      have hsub :
          (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ) - γ ≤
            -((((dotProduct x' v : ℝ) : EReal) - F u' x')) := by
        -- First recast the tilted inequality as a subtract-one-finite-term inequality.
        exact (EReal.sub_le_iff_le_add (h₁ := Or.inl hγBot) (h₂ := Or.inl hγTop)).2 h
      have hneg :
          -(((((dotProduct vStar v : ℝ) : EReal) - F u vStar) + (γ - δ))) ≤
            -((((dotProduct x' v : ℝ) : EReal) - F u' x')) := by
        calc
          -(((((dotProduct vStar v : ℝ) : EReal) - F u vStar) + (γ - δ))) =
              (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ) - γ := by
                -- This is the same affine normalization in the reverse direction.
                calc
                  -(((((dotProduct vStar v : ℝ) : EReal) - F u vStar) + (γ - δ))) =
                      -((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) - (γ - δ) := by
                        exact EReal.neg_add (x := (((dotProduct vStar v : ℝ) : EReal) - F u vStar))
                          (y := γ - δ)
                          (Or.inr (by
                            simpa [γ, δ, EReal.coe_sub] using
                              EReal.coe_ne_top
                                ((dotProduct u' uStar - dotProduct u uStar : ℝ))))
                          (Or.inr (by
                            simpa [γ, δ, EReal.coe_sub] using
                              EReal.coe_ne_bot
                                ((dotProduct u' uStar - dotProduct u uStar : ℝ))))
                  _ = -((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + (-(γ - δ)) := by
                        simp [sub_eq_add_neg]
                  _ = -((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + (-γ + δ) := by
                        rw [EReal.neg_sub (x := γ) (y := δ) (Or.inl hγBot) (Or.inl hγTop)]
                  _ = (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ) - γ := by
                        rw [sub_eq_add_neg]
                        calc
                          -((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + (-γ + δ) =
                              (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + -γ) + δ := by
                                rw [← add_assoc]
                          _ = (-γ + -((((dotProduct vStar v : ℝ) : EReal) - F u vStar))) + δ := by
                                rw [add_comm (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar))) (-γ)]
                          _ = -γ + (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ) := by
                                rw [add_assoc]
                          _ = (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ) + -γ := by
                                rw [add_comm (-γ) (-((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ)]
          _ ≤ -((((dotProduct x' v : ℝ) : EReal) - F u' x')) := hsub
      -- Negating once more returns to the original kernel inequality.
      exact (EReal.neg_le_neg_iff).1 hneg
  have hLeftEndpoint :
      -((((dotProduct x' v : ℝ) : EReal) - F u' x')) + γ =
        F u' x' - ((dotProduct x' v : ℝ) : EReal) + ((dotProduct u' uStar : ℝ) : EReal) := by
    -- The left endpoint is exactly the tilted-fiber expression at `(u',x')`.
    rw [helperForCorollary_37_5_1_negatedEndpointKernel_eq_tiltedEndpoint
      (u' := u') (x' := x') (v := v)]
  have hRightEndpoint :
      -((((dotProduct vStar v : ℝ) : EReal) - F u vStar)) + δ =
        F u vStar - ((dotProduct vStar v : ℝ) : EReal) + ((dotProduct u uStar : ℝ) : EReal) := by
    -- The right endpoint is the fixed center value of the tilted fiber.
    rw [helperForCorollary_37_5_1_negatedEndpointKernel_eq_tiltedEndpoint
      (u' := u) (x' := vStar) (v := v)]
  -- Replace the generic shifted inequality by the concrete textbook affine bounds.
  simpa [γ, δ, hLeftEndpoint, hRightEndpoint] using hShift

/-- Helper for Corollary 37.5.1: once the packed tilted-fiber lower bound has fixed the center
value of the pairing, taking the supremum over each fiber recovers the first partial
subdifferential. -/
lemma helperForCorollary_37_5_1_tiltedFiberLowerBound_implies_pairingFirstPartial
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) (uStar : Fin m → ℝ) (vStar : Fin n → ℝ)
    (hCenter :
      convexBifunctionPairing F u v =
        (((dotProduct vStar v : ℝ) : EReal) - F u vStar))
    (hLower :
      ∀ u' x',
        F u' x' - ((dotProduct x' v : ℝ) : EReal) + ((dotProduct u' uStar : ℝ) : EReal) ≥
          F u vStar - ((dotProduct vStar v : ℝ) : EReal) + ((dotProduct u uStar : ℝ) : EReal)) :
    uStar ∈ partialSubdifferentialInFirstVariable (convexBifunctionPairing F) u v := by
  intro u'
  have hTarget :
      convexBifunctionPairing F u' v ≤
        convexBifunctionPairing F u v + (((dotProduct u' uStar - dotProduct u uStar : ℝ)) : EReal) := by
    -- Convert each fiber inequality into the corresponding kernel bound and then take the
    -- supremum over the primal endpoint.
    rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
    refine iSup_le ?_
    intro x'
    have hKernel :
        (((dotProduct x' v : ℝ) : EReal) - F u' x') ≤
          (((dotProduct vStar v : ℝ) : EReal) - F u vStar) +
            (((dotProduct u' uStar - dotProduct u uStar : ℝ)) : EReal) := by
      exact
        (helperForCorollary_37_5_1_exactERealKernelTiltNormalization
          (u := u) (v := v) (uStar := uStar) (vStar := vStar) (u' := u') (x' := x')).2
          (hLower u' x')
    -- The center equality turns the bound into the required first-partial inequality.
    simpa [hCenter] using hKernel
  simpa [helperForTheorem_37_4_sumERealProducts_subtractedCoordinates_eq_coe_sum,
    helperForTheorem_37_4_coe_firstPartialIncrement_eq_finDot_sub] using hTarget

end Section37
end Chap07
