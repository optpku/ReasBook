/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part8

open scoped Topology Pointwise

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 31.1: book-polyhedral convexity transports through Fenchel conjugation under
properness. -/
lemma helperForTheorem_31_1_bookPolyhedralConvex_transport_conjugate {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hfPoly : IsBookPolyhedralConvexFunction n f) :
    IsBookPolyhedralConvexFunction n (fenchelConjugate n f) := by
  rcases hfPoly with ⟨hfPolyConv, _hf_ne_bot⟩
  refine ⟨polyhedralConvexFunction_fenchelConjugate n f hfPolyConv, ?_⟩
  intro x
  have hx_univ : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
    simp
  exact (proper_fenchelConjugate_of_proper (n := n) (f := f) hf).2.2 x hx_univ

/-- Helper for Theorem 31.1: book-polyhedral concavity transports through concave Fenchel
conjugation under properness. -/
lemma helperForTheorem_31_1_bookPolyhedralConcave_transport_conjugate {n : ℕ}
    (g : (Fin n → ℝ) → EReal)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hgPoly : IsBookPolyhedralConcaveFunction n g) :
    IsBookPolyhedralConcaveFunction n (concaveFenchelConjugate g) := by
  let hNeg : (Fin n → ℝ) → EReal := fun x => -(g x)
  rcases hgPoly with ⟨hNegPoly, _hNeg_ne_bot⟩
  have hConjPoly :
      IsPolyhedralConvexFunction n (fenchelConjugate n hNeg) :=
    polyhedralConvexFunction_fenchelConjugate n hNeg hNegPoly
  let negMap : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := -LinearMap.id
  have hPrecompPoly :
      IsPolyhedralConvexFunction n
        (inverseImageUnderLinearMap negMap (fenchelConjugate n hNeg)) := by
    exact (polyhedralConvexFunction_image_preimage_linear n n negMap).2
      (fenchelConjugate n hNeg) hConjPoly
  have hPrecompEq :
      inverseImageUnderLinearMap negMap (fenchelConjugate n hNeg) =
        (fun y : Fin n → ℝ => -(concaveFenchelConjugate g y)) := by
    funext y
    simp [inverseImageUnderLinearMap, hNeg, negMap, concaveFenchelConjugate]
  have hConjProper :
      ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) (concaveFenchelConjugate g) :=
    helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
      (n := n) (g := g) hg
  refine ⟨?_, ?_⟩
  · simpa [IsBookPolyhedralConcaveFunction, hPrecompEq] using hPrecompPoly
  · intro x
    have hx_univ : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    exact hConjProper.2.2 x hx_univ

-- Proof sketch: rewrite the concave part in terms of the convex function `-g`, apply the
-- lower-bound, separation, and closedness statements for the convex pair `(f, -g)`, and then
-- translate the resulting conjugates and domain conditions back to the book's `g`, `g⋆`, `dom g`,
-- and `dom g⋆` conventions.
/-- Theorem 31.1 (Fenchel's Duality Theorem): for a proper convex `EReal`-valued function `f` and
a proper concave `EReal`-valued function `g`, the primal infimum and dual supremum coincide under
either qualification condition `(a)` or `(b)`. Condition `(a)` yields attainment of the dual
supremum, condition `(b)` yields attainment of the primal infimum, and if both hold then both
optimal values are finite. If `f` or `g` is polyhedral in the book's sense, the corresponding
relative-interior condition may be replaced by an effective-domain condition as in the book. In
this formalization, the primal value is `fenchelPrimalInfimum f g`, which agrees with
`inf_x (f x - g x)` on the common book-effective domain of `f` and `g`, and the dual value uses
the concave conjugate `concaveFenchelConjugate g`. -/
theorem fenchel_duality_theorem {n : ℕ}
    (f g : (Fin n → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g) :
    let primal := fenchelPrimalInfimum f g
    let primalObj := commonBookEffectiveDomainDifference f g
    let dual := fenchelDualSupremum (n := n) f g
    let dualObj := fenchelDualObjective (n := n) f g
    (FenchelConditionA (n := n) f g →
      primal = dual ∧ ∃ xStar : Fin n → ℝ, dual = dualObj xStar) ∧
    (FenchelConditionB (n := n) f g →
      primal = dual ∧ ∃ x : Fin n → ℝ, primal = primalObj x) ∧
    (FenchelConditionA (n := n) f g ∧ FenchelConditionB (n := n) f g →
      IsFiniteEReal primal ∧ IsFiniteEReal dual) ∧
    (IsBookPolyhedralConcaveFunction n g →
      (FenchelConditionAWithPolyhedralG (n := n) f g →
        primal = dual ∧ ∃ xStar : Fin n → ℝ, dual = dualObj xStar) ∧
      (FenchelConditionBWithPolyhedralG (n := n) f g →
        primal = dual ∧ ∃ x : Fin n → ℝ, primal = primalObj x)) ∧
    (IsBookPolyhedralConvexFunction n f →
      (FenchelConditionAWithPolyhedralF (n := n) f g →
        primal = dual ∧ ∃ xStar : Fin n → ℝ, dual = dualObj xStar) ∧
      (FenchelConditionBWithPolyhedralF (n := n) f g →
        primal = dual ∧ ∃ x : Fin n → ℝ, primal = primalObj x)) ∧
    (IsBookPolyhedralConvexFunction n f ∧ IsBookPolyhedralConcaveFunction n g →
      (FenchelConditionAForPolyhedralPair (n := n) f g →
        primal = dual ∧ ∃ xStar : Fin n → ℝ, dual = dualObj xStar) ∧
      (FenchelConditionBForPolyhedralPair (n := n) f g →
        primal = dual ∧ ∃ x : Fin n → ℝ, primal = primalObj x) ∧
      (FenchelConditionAForPolyhedralPair (n := n) f g ∧
          FenchelConditionBForPolyhedralPair (n := n) f g →
        IsFiniteEReal primal ∧ IsFiniteEReal dual)) := by
  classical
  -- Unfold the `let`-binders so the proof can refer directly to the defined primal/dual values.
  dsimp
  -- We will use the always-valid Fenchel-inequality lower bound `primal ≥ dual`.
  have hLower :
      fenchelPrimalInfimum f g ≥ fenchelDualSupremum (n := n) f g :=
    helperForTheorem_31_1_primal_ge_dual (n := n) f g hf hg
  -- The attainment/equality clauses for (a), (b), and the polyhedral replacements are blocked
  -- upstream by missing concave-side bridge lemmas (see feedback block below).
  refine And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ (And.intro ?_ ?_))))
  · intro hA
    -- Use the Chapter 20 bridge for the convex pair `(f, -g)` to obtain equality and attainment.
    exact helperForTheorem_31_1_conditionA_concaveDuality_core (n := n) f g hf hg hA
  · intro hB
    -- Reduce to condition (a) for the conjugate pair `(f⋆, g⋆)` and translate back by biconjugacy.
    exact helperForTheorem_31_1_conditionB_concaveDuality_core (n := n) f g hf hg hB
  · intro hAB
    rcases hAB with ⟨hA, hB⟩
    -- Condition (a) rules out `primal = ⊤`, and condition (b) rules out `dual = ⊥`; together
    -- with the universal inequality `primal ≥ dual` this forces finiteness on both sides.
    have hPrimal_ne_top : fenchelPrimalInfimum f g ≠ (⊤ : EReal) :=
      helperForTheorem_31_1_primal_ne_top_of_conditionA (n := n) f g hf hg hA
    have hDual_ne_bot : fenchelDualSupremum (n := n) f g ≠ (⊥ : EReal) :=
      helperForTheorem_31_1_dual_ne_bot_of_conditionB (n := n) f g hf hg hB
    have hDual_ne_top : fenchelDualSupremum (n := n) f g ≠ (⊤ : EReal) := by
      intro hDualTop
      have hTopLePrimal : (⊤ : EReal) ≤ fenchelPrimalInfimum f g := by
        -- Rewrite `primal ≥ dual` with `dual = ⊤`.
        simpa [hDualTop] using hLower
      exact hPrimal_ne_top ((top_le_iff).1 hTopLePrimal)
    have hPrimal_ne_bot : fenchelPrimalInfimum f g ≠ (⊥ : EReal) := by
      intro hPrimalBot
      have hDualLeBot : fenchelDualSupremum (n := n) f g ≤ (⊥ : EReal) := by
        -- From `primal = ⊥` and `primal ≥ dual`.
        simpa [hPrimalBot] using hLower
      have hDualEqBot : fenchelDualSupremum (n := n) f g = (⊥ : EReal) :=
        (le_bot_iff).1 hDualLeBot
      exact hDual_ne_bot hDualEqBot
    refine And.intro ?_ ?_
    · exact And.intro hPrimal_ne_top hPrimal_ne_bot
    · exact And.intro hDual_ne_top hDual_ne_bot
  · intro hg_poly
    -- Polyhedrality allows replacing `ri` by `dom` in the corresponding qualification hypotheses.
    refine And.intro ?_ ?_
    · intro hA_polyG
      exact
        (helperForTheorem_31_1_conditionA_polyhedralVariants_concaveDuality_core
          (n := n) f g hf hg).1 ⟨hg_poly, hA_polyG⟩
    · intro hB_polyG
      let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
      let gStar : (Fin n → ℝ) → EReal := concaveFenchelConjugate g
      have hfStar :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar := by
        simpa [fStar] using proper_fenchelConjugate_of_proper (n := n) (f := f) hf
      have hgStar :
          ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
        simpa [gStar] using
          helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
            (n := n) (g := g) hg
      have hgStarPoly :
          IsBookPolyhedralConcaveFunction n gStar := by
        simpa [gStar] using
          helperForTheorem_31_1_bookPolyhedralConcave_transport_conjugate
            (n := n) g hg hg_poly
      rcases hB_polyG with ⟨hfClosed, hWitness⟩
      have hAStarPolyG : FenchelConditionAWithPolyhedralG (n := n) fStar gStar := by
        rcases hWitness with ⟨xStar, hxDomGStar, hxRiFStar⟩
        refine ⟨xStar, ?_, ?_⟩
        · simpa [fStar] using hxRiFStar
        · simpa [gStar, concaveEffectiveDomain, concaveConjugateEffectiveDomain] using hxDomGStar
      have hPairCore :
          fenchelPrimalInfimum fStar gStar = fenchelDualSupremum (n := n) fStar gStar ∧
            ∃ x : Fin n → ℝ,
              fenchelDualSupremum (n := n) fStar gStar = fenchelDualObjective (n := n) fStar gStar x :=
        (helperForTheorem_31_1_conditionA_polyhedralVariants_concaveDuality_core
          (n := n) fStar gStar hfStar hgStar).1 ⟨hgStarPoly, hAStarPolyG⟩
      have hgClosed : ClosedConcaveFunction g := by
        have hNegClosed : ClosedConvexFunction (fun x => -(g x)) :=
          helperForLemma_31_0_3_closedConvexFunction_of_polyhedralProper
            (n := n) (g := fun x => -(g x)) hg_poly.1 hg
        simpa [ClosedConcaveFunction] using hNegClosed
      exact
        helperForTheorem_31_1_translate_conjugatePair_duality_to_original
          (n := n) f g hf hg hfClosed hgClosed hPairCore.1 hPairCore.2
  · intro hf_poly
    refine And.intro ?_ ?_
    · intro hA_polyF
      exact
        (helperForTheorem_31_1_conditionA_polyhedralVariants_concaveDuality_core
          (n := n) f g hf hg).2.1 ⟨hf_poly, hA_polyF⟩
    · intro hB_polyF
      let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
      let gStar : (Fin n → ℝ) → EReal := concaveFenchelConjugate g
      have hfStar :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar := by
        simpa [fStar] using proper_fenchelConjugate_of_proper (n := n) (f := f) hf
      have hgStar :
          ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
        simpa [gStar] using
          helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
            (n := n) (g := g) hg
      have hfStarPoly :
          IsBookPolyhedralConvexFunction n fStar := by
        simpa [fStar] using
          helperForTheorem_31_1_bookPolyhedralConvex_transport_conjugate
            (n := n) f hf hf_poly
      rcases hB_polyF with ⟨hgClosed, hWitness⟩
      have hAStarPolyF : FenchelConditionAWithPolyhedralF (n := n) fStar gStar := by
        rcases hWitness with ⟨xStar, hxRiGStar, hxDomFStar⟩
        refine ⟨xStar, ?_, ?_⟩
        · simpa [fStar] using hxDomFStar
        · simpa [gStar, concaveEffectiveDomain, concaveConjugateEffectiveDomain] using hxRiGStar
      have hPairCore :
          fenchelPrimalInfimum fStar gStar = fenchelDualSupremum (n := n) fStar gStar ∧
            ∃ x : Fin n → ℝ,
              fenchelDualSupremum (n := n) fStar gStar = fenchelDualObjective (n := n) fStar gStar x :=
        (helperForTheorem_31_1_conditionA_polyhedralVariants_concaveDuality_core
          (n := n) fStar gStar hfStar hgStar).2.1 ⟨hfStarPoly, hAStarPolyF⟩
      have hfClosed : ClosedConvexFunction f :=
        helperForLemma_31_0_3_closedConvexFunction_of_polyhedralProper
          (n := n) (g := f) hf_poly.1 hf
      exact
        helperForTheorem_31_1_translate_conjugatePair_duality_to_original
          (n := n) f g hf hg hfClosed hgClosed hPairCore.1 hPairCore.2
  · rintro ⟨_hf_poly, _hg_poly⟩
    have hPairCore :
        (FenchelConditionAForPolyhedralPair (n := n) f g →
          fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
            ∃ xStar : Fin n → ℝ,
              fenchelDualSupremum (n := n) f g = fenchelDualObjective (n := n) f g xStar) ∧
        (FenchelConditionBForPolyhedralPair (n := n) f g →
          fenchelPrimalInfimum f g = fenchelDualSupremum (n := n) f g ∧
            ∃ x : Fin n → ℝ,
              fenchelPrimalInfimum f g = commonBookEffectiveDomainDifference f g x) := by
      refine And.intro ?_ ?_
      · intro hA_pair
        exact
          (helperForTheorem_31_1_conditionA_polyhedralVariants_concaveDuality_core
            (n := n) f g hf hg).2.2 ⟨_hf_poly, _hg_poly, hA_pair⟩
      · intro hB_pair
        let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
        let gStar : (Fin n → ℝ) → EReal := concaveFenchelConjugate g
        have hfStar :
            ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar := by
          simpa [fStar] using proper_fenchelConjugate_of_proper (n := n) (f := f) hf
        have hgStar :
            ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) gStar := by
          simpa [gStar] using
            helperForTheorem_31_1_properConcave_concaveFenchelConjugate_of_properConcave
              (n := n) (g := g) hg
        have hfStarPoly :
            IsBookPolyhedralConvexFunction n fStar := by
          simpa [fStar] using
            helperForTheorem_31_1_bookPolyhedralConvex_transport_conjugate
              (n := n) f hf _hf_poly
        have hgStarPoly :
            IsBookPolyhedralConcaveFunction n gStar := by
          simpa [gStar] using
            helperForTheorem_31_1_bookPolyhedralConcave_transport_conjugate
              (n := n) g hg _hg_poly
        have hAStarPair : FenchelConditionAForPolyhedralPair (n := n) fStar gStar := by
          rcases hB_pair with ⟨xStar, hxDomGStar, hxDomFStar⟩
          refine ⟨xStar, ?_, ?_⟩
          · simpa [fStar] using hxDomFStar
          · simpa [gStar, concaveEffectiveDomain, concaveConjugateEffectiveDomain] using hxDomGStar
        have hPairDualCore :
            fenchelPrimalInfimum fStar gStar = fenchelDualSupremum (n := n) fStar gStar ∧
              ∃ x : Fin n → ℝ,
                fenchelDualSupremum (n := n) fStar gStar = fenchelDualObjective (n := n) fStar gStar x :=
          (helperForTheorem_31_1_conditionA_polyhedralVariants_concaveDuality_core
            (n := n) fStar gStar hfStar hgStar).2.2 ⟨hfStarPoly, hgStarPoly, hAStarPair⟩
        have hfClosed : ClosedConvexFunction f :=
          helperForLemma_31_0_3_closedConvexFunction_of_polyhedralProper
            (n := n) (g := f) _hf_poly.1 hf
        have hgClosed : ClosedConcaveFunction g := by
          have hNegClosed : ClosedConvexFunction (fun x => -(g x)) :=
            helperForLemma_31_0_3_closedConvexFunction_of_polyhedralProper
              (n := n) (g := fun x => -(g x)) _hg_poly.1 hg
          simpa [ClosedConcaveFunction] using hNegClosed
        exact
          helperForTheorem_31_1_translate_conjugatePair_duality_to_original
            (n := n) f g hf hg hfClosed hgClosed hPairDualCore.1 hPairDualCore.2
    refine And.intro hPairCore.1 ?_
    refine And.intro hPairCore.2 ?_
    intro hAB_pair
    rcases hAB_pair with ⟨hA_pair, hB_pair⟩
    -- The pair-level domain witnesses already force both values away from `±∞`.
    have hPrimal_ne_top : fenchelPrimalInfimum f g ≠ (⊤ : EReal) :=
      helperForTheorem_31_1_primal_ne_top_of_polyhedral_pair_conditionA
        (n := n) f g hf hg hA_pair
    have hDual_ne_bot : fenchelDualSupremum (n := n) f g ≠ (⊥ : EReal) :=
      helperForTheorem_31_1_dual_ne_bot_of_polyhedral_pair_conditionB
        (n := n) f g hB_pair
    have hDual_ne_top : fenchelDualSupremum (n := n) f g ≠ (⊤ : EReal) := by
      intro hDualTop
      have hTopLePrimal : (⊤ : EReal) ≤ fenchelPrimalInfimum f g := by
        simpa [hDualTop] using hLower
      exact hPrimal_ne_top ((top_le_iff).1 hTopLePrimal)
    have hPrimal_ne_bot : fenchelPrimalInfimum f g ≠ (⊥ : EReal) := by
      intro hPrimalBot
      have hDualLeBot : fenchelDualSupremum (n := n) f g ≤ (⊥ : EReal) := by
        simpa [hPrimalBot] using hLower
      have hDualEqBot : fenchelDualSupremum (n := n) f g = (⊥ : EReal) :=
        (le_bot_iff).1 hDualLeBot
      exact hDual_ne_bot hDualEqBot
    refine And.intro ?_ ?_
    · exact And.intro hPrimal_ne_top hPrimal_ne_bot
    · exact And.intro hDual_ne_top hDual_ne_bot

/-- The perturbation function `F(u, x) = f x - g (A x + u)` used for Fenchel duality with a
linear map `A : ℝ^n → ℝ^m`. -/
def fenchelPerturbationFunction {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) :
    ((Fin m → ℝ) × (Fin n → ℝ)) → EReal :=
  fun p => f p.2 - g (A p.2 + p.1)

/-- A generic closedness condition for an `EReal`-valued function on a topological space, matching
the textbook's use of lower semicontinuity for closed convex functions. -/
def ClosedERealFunction {α : Type*} [TopologicalSpace α] (F : α → EReal) : Prop :=
  LowerSemicontinuous F

/-!
Helpers for Lemma 31.0.6.

We treat the perturbation as the sum `f x + (-(g (A x + u)))` so we can reuse basic lemmas about
`EReal` addition and lower semicontinuity. -/

/-- Helper for Lemma 31.0.6: the Fenchel perturbation `F(u, x) = f x - g(Ax + u)` never takes the
value `⊥`. -/
lemma helperForLemma_31_0_6_ne_bot {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    ∀ p, fenchelPerturbationFunction A f g p ≠ (⊥ : EReal) := by
  intro p
  -- Expand the subtraction into an `EReal` sum so `add_ne_bot_of_notbot` applies.
  have hx_univ : p.2 ∈ (Set.univ : Set (Fin n → ℝ)) := by simp
  have hf_ne_bot : f p.2 ≠ (⊥ : EReal) := hf.2.2 p.2 hx_univ
  have hneg_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun y => -(g y)) := by
    simpa [ProperConcaveFunctionOn] using hg
  have hy_univ : (A p.2 + p.1) ∈ (Set.univ : Set (Fin m → ℝ)) := by simp
  have hneg_ne_bot : -(g (A p.2 + p.1)) ≠ (⊥ : EReal) :=
    hneg_proper.2.2 (A p.2 + p.1) hy_univ
  -- The sum of two non-`⊥` `EReal`s is again non-`⊥`.
  simpa [fenchelPerturbationFunction, sub_eq_add_neg] using
    add_ne_bot_of_notbot hf_ne_bot hneg_ne_bot

/-- Helper for Lemma 31.0.6: the Fenchel perturbation is finite at some point, hence it is not
identically `⊤`. -/
lemma helperForLemma_31_0_6_exists_ne_top {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    ∃ p, fenchelPerturbationFunction A f g p ≠ (⊤ : EReal) := by
  classical
  -- Work with the proper convex function `-g` provided by proper concavity of `g`.
  have hneg_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun y => -(g y)) := by
    simpa [ProperConcaveFunctionOn] using hg
  -- Choose an epigraph witness for `f`.
  rcases hf.2.1 with ⟨pF, hpF⟩
  set x0 : Fin n → ℝ := pF.1
  set μ0 : ℝ := pF.2
  have hle_f : f x0 ≤ (μ0 : EReal) := by
    -- Membership in the epigraph over `univ` is exactly the inequality `f x ≤ μ`.
    simpa [x0, μ0] using (mem_epigraph_univ_iff (f := f)).1 hpF
  -- Choose an epigraph witness for `-g`.
  rcases hneg_proper.2.1 with ⟨pG, hpG⟩
  set y0 : Fin m → ℝ := pG.1
  set ν0 : ℝ := pG.2
  have hle_neg_g : -(g y0) ≤ (ν0 : EReal) := by
    simpa [y0, ν0] using (mem_epigraph_univ_iff (f := fun y => -(g y))).1 hpG
  -- Set `u0 = y0 - A x0` so that `A x0 + u0 = y0`.
  set u0 : Fin m → ℝ := y0 - A x0
  have hAx0_add_u0 : A x0 + u0 = y0 := by
    -- Rearrange to `A x0 + y0 - A x0 = y0` and apply `add_sub_cancel`.
    calc
      A x0 + u0 = A x0 + y0 - A x0 := by
        simp [u0, sub_eq_add_neg, add_assoc]
      _ = y0 := add_sub_cancel_left (A x0) y0
  refine ⟨(u0, x0), ?_⟩
  intro hTop
  -- Bound `F(u0, x0)` above by a real number using the epigraph inequalities.
  have hle_F :
      fenchelPerturbationFunction A f g (u0, x0) ≤ (μ0 : EReal) + (ν0 : EReal) := by
    -- Rewrite `F` as a sum and use monotonicity of addition.
    have : f x0 + (-(g y0)) ≤ (μ0 : EReal) + (ν0 : EReal) :=
      add_le_add hle_f hle_neg_g
    -- Substitute `A x0 + u0 = y0` into the perturbation term.
    simpa [fenchelPerturbationFunction, sub_eq_add_neg, u0, x0, y0, μ0, ν0, hAx0_add_u0] using this
  have hTop_le :
      (⊤ : EReal) ≤ (μ0 : EReal) + (ν0 : EReal) := by
    simpa [hTop] using hle_F
  have hSum_coe : (μ0 : EReal) + (ν0 : EReal) = ((μ0 + ν0 : ℝ) : EReal) := by
    simp
  have hTop_le' : (⊤ : EReal) ≤ ((μ0 + ν0 : ℝ) : EReal) := by
    -- Avoid `simp` here: coercion lemmas for `EReal` addition can cause simp recursion.
    rw [← hSum_coe]
    exact hTop_le
  exact (not_top_le_coe (μ0 + ν0)) hTop_le'

/-- Helper for Lemma 31.0.6: if `f` is closed convex and `g` is closed concave, then the Fenchel
perturbation is lower semicontinuous. -/
lemma helperForLemma_31_0_6_lowerSemicontinuous {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g)
    (hClosed : ClosedConvexFunction f ∧ ClosedConcaveFunction g) :
    LowerSemicontinuous (fenchelPerturbationFunction A f g) := by
  classical
  -- We show lower semicontinuity by writing `F = (f ∘ snd) + ((-g) ∘ (Ax + u))`.
  have hcont_snd :
      Continuous (fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.2) :=
    continuous_snd
  have hcont_fst :
      Continuous (fun p : (Fin m → ℝ) × (Fin n → ℝ) => p.1) :=
    continuous_fst
  have hcont_A : Continuous (fun x : Fin n → ℝ => A x) := by
    simpa using (LinearMap.continuous_of_finiteDimensional A)
  have hcont_A_snd :
      Continuous (fun p : (Fin m → ℝ) × (Fin n → ℝ) => A p.2) :=
    hcont_A.comp hcont_snd
  have hcont_affine :
      Continuous (fun p : (Fin m → ℝ) × (Fin n → ℝ) => A p.2 + p.1) :=
    hcont_A_snd.add hcont_fst
  -- Lower semicontinuity of the two summands.
  have hf_lsc : LowerSemicontinuous f := hClosed.1.2
  have hneg_lsc : LowerSemicontinuous (fun y : Fin m → ℝ => -(g y)) := (hClosed.2).2
  have hF1_lsc : LowerSemicontinuous (fun p : (Fin m → ℝ) × (Fin n → ℝ) => f p.2) :=
    hf_lsc.comp hcont_snd
  have hF2_lsc :
      LowerSemicontinuous
        (fun p : (Fin m → ℝ) × (Fin n → ℝ) => -(g (A p.2 + p.1))) :=
    hneg_lsc.comp hcont_affine
  -- Addition is continuous at `(a,b)` as soon as both `a` and `b` are not `⊥`; properness provides
  -- those pointwise hypotheses for `f` and `-g`.
  have hneg_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun y => -(g y)) := by
    simpa [ProperConcaveFunctionOn] using hg
  have hcont_add :
      ∀ p : (Fin m → ℝ) × (Fin n → ℝ),
        ContinuousAt (fun q : EReal × EReal => q.1 + q.2) (f p.2, -(g (A p.2 + p.1))) := by
    intro p
    have hx_univ : p.2 ∈ (Set.univ : Set (Fin n → ℝ)) := by simp
    have hf_ne_bot : f p.2 ≠ (⊥ : EReal) := hf.2.2 p.2 hx_univ
    have hy_univ : (A p.2 + p.1) ∈ (Set.univ : Set (Fin m → ℝ)) := by simp
    have hneg_ne_bot : -(g (A p.2 + p.1)) ≠ (⊥ : EReal) :=
      hneg_proper.2.2 (A p.2 + p.1) hy_univ
    exact EReal.continuousAt_add (h := Or.inr hneg_ne_bot) (h' := Or.inl hf_ne_bot)
  have hsum_lsc :
      LowerSemicontinuous
        (fun p : (Fin m → ℝ) × (Fin n → ℝ) => f p.2 + (-(g (A p.2 + p.1)))) :=
    LowerSemicontinuous.add' hF1_lsc hF2_lsc hcont_add
  -- Rewrite the sum back into the perturbation `f x - g(Ax + u)`.
  simpa [fenchelPerturbationFunction, sub_eq_add_neg] using hsum_lsc

-- Proof sketch: use properness of `f` and `g` to choose `x₀` and `y₀` with finite values, then
-- set `u₀ = y₀ - A x₀` so `fenchelPerturbationFunction A f g` is finite at `(u₀, x₀)` and never
-- takes the value `⊥`. For closedness, rewrite the perturbation as the sum of the closed convex
-- function `x ↦ f x` and the pullback of the closed convex function `-g` along the continuous
-- affine map `(u, x) ↦ A x + u`.
/-- Lemma 31.0.6 (Basic Properties of `F`): if `f : ℝ^n → ℝ ∪ {+∞}` is proper convex,
`g : ℝ^m → ℝ ∪ {-∞}` is proper concave, and `A : ℝ^n → ℝ^m` is linear, then the perturbation
function `F(u, x) = f x - g (A x + u)` is a proper bivariate `EReal`-valued function on
`ℝ^m × ℝ^n`. If `f` is closed convex and `g` is closed concave, then the specific perturbation
function `fenchelPerturbationFunction A f g` is closed, i.e. lower semicontinuous on
`ℝ^m × ℝ^n`. -/
lemma fenchelPerturbationFunction_basicProperties {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    ProperERealFunction (fenchelPerturbationFunction A f g) ∧
      (ClosedConvexFunction f ∧ ClosedConcaveFunction g →
        ClosedERealFunction (fenchelPerturbationFunction A f g)) := by
  classical
  -- Properness is the conjunction of two facts:
  -- (1) the perturbation never takes the value `⊥`;
  -- (2) it is finite at a specific point constructed from epigraph witnesses of `f` and `-g`.
  refine And.intro ?_ ?_
  · refine And.intro ?_ ?_
    · intro p
      exact helperForLemma_31_0_6_ne_bot (A := A) (f := f) (g := g) hf hg p
    · exact helperForLemma_31_0_6_exists_ne_top (A := A) (f := f) (g := g) hf hg
  · intro hClosed
    -- Closedness is defined as lower semicontinuity (`ClosedERealFunction`).
    have hLsc :
        LowerSemicontinuous (fenchelPerturbationFunction A f g) :=
      helperForLemma_31_0_6_lowerSemicontinuous (A := A) (f := f) (g := g) hf hg hClosed
    simpa [ClosedERealFunction] using hLsc

/-- The value function `u ↦ inf_x F(u, x)` associated with the Fenchel perturbation
`F(u, x) = f x - g (A x + u)`. -/
noncomputable def fenchelPerturbationValueFunction {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) :
    (Fin m → ℝ) → EReal :=
  fun u => functionInfimumEReal (fun x => fenchelPerturbationFunction A f g (u, x))

/-- The convex program `(P)` is strongly consistent when the origin lies in the relative interior
of the effective domain of its perturbation value function. -/
def FenchelProgramStronglyConsistent {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal) : Prop :=
  (0 : Fin m → ℝ) ∈
    euclideanRelativeInterior_fin m
      (effectiveDomain (Set.univ : Set (Fin m → ℝ))
        (fenchelPerturbationValueFunction A f g))

/-!
Helpers for Lemma 31.0.7.

The main work is (1) to identify the effective domain of the perturbation value function, and
(2) to translate the strong-consistency condition `0 ∈ ri(dom p)` into a concrete relative-interior
intersection witness.
-/

-- We will repeatedly use that proper concavity of `g` is encoded through proper convexity of `-g`.
/-- Helper for Lemma 31.0.7: the effective domain of the perturbation value function is the
Minkowski difference `dom g - A(dom f)`. -/
lemma helperForLemma_31_0_7_effectiveDomain_valueFunction {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fenchelPerturbationValueFunction A f g) =
      concaveEffectiveDomain g -
        (A '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
  classical
  -- Abbreviate the domains so elementwise arguments remain readable.
  let domF : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  let domG : Set (Fin m → ℝ) := concaveEffectiveDomain g
  ext u
  constructor
  · intro hu
    -- Unfold membership in the effective domain as `p u < ⊤`.
    have hu_lt_top : fenchelPerturbationValueFunction A f g u < (⊤ : EReal) := by
      have :
          u ∈ (Set.univ : Set (Fin m → ℝ)) ∧
            fenchelPerturbationValueFunction A f g u < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using hu
      exact this.2
    have hu_ne_top : fenchelPerturbationValueFunction A f g u ≠ (⊤ : EReal) :=
      (lt_top_iff_ne_top).1 hu_lt_top
    -- If the infimum is finite, then not all perturbation values can be `⊤`.
    have hx_exists :
        ∃ x : Fin n → ℝ, fenchelPerturbationFunction A f g (u, x) ≠ (⊤ : EReal) := by
      by_contra hNo
      have hAll :
          ∀ x : Fin n → ℝ, fenchelPerturbationFunction A f g (u, x) = (⊤ : EReal) := by
        intro x
        by_contra hx
        exact hNo ⟨x, hx⟩
      have hVal_top : fenchelPerturbationValueFunction A f g u = (⊤ : EReal) := by
        -- The value function is `⨅ x, F(u,x)`.
        simp [fenchelPerturbationValueFunction, functionInfimumEReal, hAll]
      exact hu_ne_top hVal_top
    rcases hx_exists with ⟨x, hx_ne_top⟩
    -- Proper concavity gives `g y ≠ ⊤` for all `y` (equivalently, `-g y ≠ ⊥` for all `y`).
    have hneg_proper :
        ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun y => -(g y)) := by
      simpa [ProperConcaveFunctionOn] using hg
    have hg_ne_top : ∀ y : Fin m → ℝ, g y ≠ (⊤ : EReal) := by
      intro y hyTop
      have hneg_eq : -(g y) = (⊥ : EReal) := by
        simpa [hyTop]
      have hy_univ : y ∈ (Set.univ : Set (Fin m → ℝ)) := by
        simp
      exact (hneg_proper.2.2 y hy_univ) hneg_eq
    -- Use `F(u,x) ≠ ⊤` to deduce `f x < ⊤` and `g(Ax+u) ≠ ⊥`.
    have hx_univ : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hf_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x hx_univ
    have hfx_ne_top : f x ≠ (⊤ : EReal) := by
      intro hTop
      have hterm_top : fenchelPerturbationFunction A f g (u, x) = (⊤ : EReal) := by
        have hgAxu_ne_top : g (A x + u) ≠ (⊤ : EReal) := hg_ne_top (A x + u)
        -- If `f x = ⊤`, then `F(u,x) = ⊤ - g(Ax+u) = ⊤`.
        simpa [fenchelPerturbationFunction, hTop, EReal.top_sub hgAxu_ne_top]
      exact hx_ne_top hterm_top
    have hx_domF : x ∈ domF := by
      have hx' : x ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f x < (⊤ : EReal) := by
        have hx_univ' : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
          simp
        refine ⟨hx_univ', (lt_top_iff_ne_top).2 hfx_ne_top⟩
      simpa [domF, effectiveDomain_eq] using hx'
    have hgAxu_ne_bot : g (A x + u) ≠ (⊥ : EReal) := by
      intro hBot
      have hterm_top : fenchelPerturbationFunction A f g (u, x) = (⊤ : EReal) := by
        -- If `g(Ax+u) = ⊥`, then `F(u,x) = f x - ⊥ = ⊤` (properness rules out `f x = ⊥`).
        have : f x - (⊥ : EReal) = (⊤ : EReal) := by
          simpa using (EReal.sub_bot hf_ne_bot)
        simpa [fenchelPerturbationFunction, hBot, this]
      exact hx_ne_top hterm_top
    have hAxu_domG : (A x + u) ∈ domG := by
      -- `A x + u ∈ domG` means `-(g (A x + u)) < ⊤`.
      have hneg_lt_top : -(g (A x + u)) < (⊤ : EReal) := by
        cases hgy : g (A x + u) with
        | bot =>
            exact (hgAxu_ne_bot hgy).elim
        | top =>
            exact (hg_ne_top (A x + u) hgy).elim
        | coe r =>
            simpa [hgy] using (EReal.coe_lt_top (-r))
      have hdom' :
          (A x + u) ∈ (Set.univ : Set (Fin m → ℝ)) ∧
            (-(g (A x + u))) < (⊤ : EReal) := by
        have hAxu_univ : (A x + u) ∈ (Set.univ : Set (Fin m → ℝ)) := by
          simp
        exact ⟨hAxu_univ, hneg_lt_top⟩
      simpa [domG, concaveEffectiveDomain, effectiveDomain_eq] using hdom'
    -- Convert `A x + u ∈ domG` and `A x ∈ A(domF)` into membership of the Minkowski difference.
    change u ∈ domG - (A '' domF)
    -- Witness `u = (A x + u) - A x`.
    refine ⟨A x + u, hAxu_domG, A x, ?_, ?_⟩
    · refine ⟨x, hx_domF, rfl⟩
    · simpa using (add_sub_cancel_left (A x) u).symm
  · intro hu
    -- Start from a domain witness `u = y - A x` with `y ∈ domG` and `x ∈ domF`.
    change u ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fenchelPerturbationValueFunction A f g)
    rcases hu with ⟨y, hy_domG, z, hz_mem, huz⟩
    rcases hz_mem with ⟨x, hx_domF, rfl⟩
    -- Rewrite `A x + u = y` using `u = y - A x`.
    have hAxu_eq : A x + u = y := by
      calc
        A x + u = A x + (y - A x) := by simpa [huz]
        _ = y := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    -- Use `x ∈ domF` and `y ∈ domG` to show `F(u,x) < ⊤`, hence `p u < ⊤`.
    have hx_lt_top : f x < (⊤ : EReal) := by
      have hx' : x ∈ (Set.univ : Set (Fin n → ℝ)) ∧ f x < (⊤ : EReal) := by
        simpa [effectiveDomain_eq] using hx_domF
      exact hx'.2
    have hneg_proper :
        ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun y => -(g y)) := by
      simpa [ProperConcaveFunctionOn] using hg
    have hx_univ : x ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hf_ne_bot : f x ≠ (⊥ : EReal) := hf.2.2 x hx_univ
    have hg_y_ne_top : g y ≠ (⊤ : EReal) := by
      intro hyTop
      have hneg_eq : -(g y) = (⊥ : EReal) := by simpa [hyTop]
      have hy_univ : y ∈ (Set.univ : Set (Fin m → ℝ)) := by
        simp
      exact (hneg_proper.2.2 y hy_univ) hneg_eq
    have hy_lt_top : -(g y) < (⊤ : EReal) := by
      have hy' :
          y ∈ (Set.univ : Set (Fin m → ℝ)) ∧ (-(g y)) < (⊤ : EReal) := by
        simpa [concaveEffectiveDomain, effectiveDomain_eq] using hy_domG
      exact hy'.2
    have hg_y_ne_bot : g y ≠ (⊥ : EReal) := by
      -- If `g y = ⊥`, then `-g y = ⊤`, contradicting `-g y < ⊤`.
      intro hyBot
      have hneg_eq_top : (-(g y)) = (⊤ : EReal) := by
        simpa [hyBot]
      have hneg_ne_top : (-(g y)) ≠ (⊤ : EReal) :=
        (lt_top_iff_ne_top).1 hy_lt_top
      exact hneg_ne_top hneg_eq_top
    -- With `f x` finite above and `g y` finite below, the objective value is a real number.
    have hFx_lt_top : fenchelPerturbationFunction A f g (u, x) < (⊤ : EReal) := by
      cases hfx : f x with
      | top =>
          have : (⊤ : EReal) < (⊤ : EReal) := by
            simpa [hfx] using hx_lt_top
          exact (lt_irrefl (⊤ : EReal) this).elim
      | bot =>
          exact (hf_ne_bot hfx).elim
      | coe r =>
          cases hgy : g y with
          | bot =>
              exact (hg_y_ne_bot hgy).elim
          | top =>
              exact (hg_y_ne_top hgy).elim
          | coe s =>
              -- Everything is real, so the subtraction is real and hence `< ⊤`.
              simpa [fenchelPerturbationFunction, hAxu_eq, hfx, hgy, EReal.coe_sub] using
                (EReal.coe_lt_top (r - s))
    have hVal_le :
        fenchelPerturbationValueFunction A f g u ≤ fenchelPerturbationFunction A f g (u, x) := by
      -- `p u` is an `iInf`, so it is below every sampled value.
      simpa [fenchelPerturbationValueFunction, functionInfimumEReal] using
        (iInf_le (fun z : Fin n → ℝ => fenchelPerturbationFunction A f g (u, z)) x)
    have hVal_lt_top : fenchelPerturbationValueFunction A f g u < (⊤ : EReal) :=
      lt_of_le_of_lt hVal_le hFx_lt_top
    have hu' :
        u ∈ (Set.univ : Set (Fin m → ℝ)) ∧
          fenchelPerturbationValueFunction A f g u < (⊤ : EReal) := by
      have hu_univ : u ∈ (Set.univ : Set (Fin m → ℝ)) := by
        simp
      exact ⟨hu_univ, hVal_lt_top⟩
    simpa [effectiveDomain_eq] using hu'

/-- Helper for Lemma 31.0.7: relative interior commutes with the linear image of a convex set. -/
lemma helperForLemma_31_0_7_relativeInterior_fin_image_linearMap {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (C : Set (Fin n → ℝ)) (hC : Convex ℝ C) :
    euclideanRelativeInterior_fin m (A '' C) = A '' euclideanRelativeInterior_fin n C := by
  classical
  -- Unfold `euclideanRelativeInterior_fin` and apply the Euclidean-space linear-image lemma
  -- to the conjugated map `A' = eM.symm ∘ A ∘ eN`.
  let eN : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)
  let eM : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  let CE : Set (EuclideanSpace ℝ (Fin n)) := eN.symm '' C
  let A' : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
    (eM.symm.toLinearMap).comp (A.comp eN.toLinearMap)
  have hCE_conv : Convex ℝ CE := by
    -- Convexity is preserved under linear images.
    simpa [CE] using hC.linear_image eN.symm.toLinearMap
  have hPreimage :
      eM.symm '' (A '' C) = A' '' CE := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨x, hxC, rfl⟩
      refine ⟨eN.symm x, ?_, ?_⟩
      · exact ⟨x, hxC, rfl⟩
      · -- `A' (eN.symm x)` is exactly `eM.symm (A x)`.
        simp [A', eN, eM]
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨x, hxC, rfl⟩
      -- With `z = eN.symm x`, the image point is `A' z = eM.symm (A x)`.
      refine ⟨A x, ?_, ?_⟩
      · exact ⟨x, hxC, rfl⟩
      · simp [A', eN, eM]
  have hImage_comp (S : Set (EuclideanSpace ℝ (Fin n))) :
      eM '' (A' '' S) = A '' (eN '' S) := by
    ext y
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨eN w, ?_, ?_⟩
      · exact ⟨w, hw, rfl⟩
      · simp [A', eN, eM]
    · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨A' w, ?_, ?_⟩
      · exact ⟨w, hw, rfl⟩
      · simp [A', eN, eM]
  -- Now compute both sides by unfolding the transported definition.
  -- Left-hand side: transport via `eM` from Euclidean relative interior.
  -- Right-hand side: apply `A` to the transported relative interior via `eN`.
  calc
    euclideanRelativeInterior_fin m (A '' C)
        = eM '' euclideanRelativeInterior m (eM.symm '' (A '' C)) := by
            simp [euclideanRelativeInterior_fin, eM]
    _ = eM '' euclideanRelativeInterior m (A' '' CE) := by
          simpa [hPreimage]
    _ = eM '' (A' '' euclideanRelativeInterior n CE) := by
          -- Euclidean relative interior commutes with linear images of convex sets.
          have hri :
              euclideanRelativeInterior m (A' '' CE) =
                A' '' euclideanRelativeInterior n CE :=
            (euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset
              (n := n) (m := m) (C := CE) hCE_conv (A := A')).1
          simpa [hri]
    _ = A '' (eN '' euclideanRelativeInterior n CE) := by
          simpa using (hImage_comp (S := euclideanRelativeInterior n CE))
    _ = A '' euclideanRelativeInterior_fin n C := by
          simp [euclideanRelativeInterior_fin, eN, CE]

/-- Helper for Lemma 31.0.7: the two domain components in the strong-consistency criterion are
convex, so Chapter 11 subtraction lemmas apply. -/
lemma helperForLemma_31_0_7_convexity_domain_components {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    Convex ℝ (concaveEffectiveDomain g) ∧
      Convex ℝ (A '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
  -- `dom g` is the effective domain of the proper convex function `-g`.
  have hneg_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) (fun y => -(g y)) := by
    simpa [ProperConcaveFunctionOn] using hg
  have hdomF_conv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
    effectiveDomain_convex (S := Set.univ) (f := f) hf.1
  have hdomG_conv :
      Convex ℝ (concaveEffectiveDomain g) := by
    simpa [concaveEffectiveDomain] using
      (effectiveDomain_convex (S := Set.univ) (f := fun y => -(g y)) hneg_proper.1)
  refine And.intro hdomG_conv ?_
  -- Linear images of convex sets are convex.
  simpa using hdomF_conv.linear_image A

-- Proof sketch: unfold the perturbation value function at `u = 0` to identify `inf F₀` with the
-- primal infimum `inf_x (f x - g (A x))`. For strong consistency, identify the effective domain
-- of the value function with the perturbation set determined by `dom f` and `dom g`, and then use
-- the relative-interior criterion that `0` lies in that domain exactly when some
-- `x ∈ ri (dom f)` satisfies `A x ∈ ri (dom g)`.
/-- Lemma 31.0.7 (Optimal Value and Strong Consistency of Convex Program `(P)`): let
`f : ℝ^n → ℝ ∪ {+∞}` be proper convex, let `g : ℝ^m → ℝ ∪ {-∞}` be proper concave, and let
`A : ℝ^n → ℝ^m` be linear. For the perturbation family
`F(u, x) = f x - g (A x + u)`, the optimal value of `(P)` is `inf F₀`, and `(P)` is strongly
consistent iff there exists `x ∈ ri (dom f)` such that `A x ∈ ri (dom g)`. In this
formalization, `dom g` is `concaveEffectiveDomain g` and strong consistency means
`0 ∈ ri (dom (fenchelPerturbationValueFunction A f g))`. -/
lemma fenchel_program_optimalValue_and_strongConsistency {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (f : (Fin n → ℝ) → EReal) (g : (Fin m → ℝ) → EReal)
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hg : ProperConcaveFunctionOn (Set.univ : Set (Fin m → ℝ)) g) :
    functionInfimumEReal (fun x => f x - g (A x)) =
        fenchelPerturbationValueFunction A f g (0 : Fin m → ℝ) ∧
      (FenchelProgramStronglyConsistent A f g ↔
        ∃ x : Fin n → ℝ,
          x ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
            A x ∈ euclideanRelativeInterior_fin m (concaveEffectiveDomain g)) := by
  classical
  -- Split the statement into the optimal-value identity and the strong-consistency criterion.
  refine And.intro ?_ ?_
  · -- Optimal value: this is definitional unfolding at `u = 0`.
    -- Expand `p(0) = inf_x F(0,x)` and simplify `A x + 0 = A x`.
    simp [fenchelPerturbationValueFunction, fenchelPerturbationFunction, functionInfimumEReal]
  · -- Strong consistency: rewrite the value-function domain and translate `0 ∈ ri(dom p)`.
    let domF : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
    let domG : Set (Fin m → ℝ) := concaveEffectiveDomain g
    let domA : Set (Fin m → ℝ) := A '' domF
    have hDom :
        effectiveDomain (Set.univ : Set (Fin m → ℝ)) (fenchelPerturbationValueFunction A f g) =
          domG - domA := by
      -- This is the effective-domain identity proved above.
      simpa [domF, domG, domA] using
        helperForLemma_31_0_7_effectiveDomain_valueFunction (A := A) (f := f) (g := g) hf hg
    have hConv : Convex ℝ domG ∧ Convex ℝ domA := by
      -- Convexity of `domG` and `A(domF)` follows from properness and linearity.
      simpa [domF, domG, domA] using
        helperForLemma_31_0_7_convexity_domain_components (A := A) (f := f) (g := g) hf hg
    have hRiImage :
        euclideanRelativeInterior_fin m domA = A '' euclideanRelativeInterior_fin n domF := by
      -- Relative interior commutes with linear images of convex sets.
      have hdomF_conv : Convex ℝ domF :=
        effectiveDomain_convex (S := Set.univ) (f := f) hf.1
      simpa [domA, domF] using
        helperForLemma_31_0_7_relativeInterior_fin_image_linearMap (A := A) (C := domF) hdomF_conv
    constructor
    · intro hStrong
      -- Rewrite strong consistency as `0 ∈ ri(domG - domA)`.
      have h0_ri : (0 : Fin m → ℝ) ∈ euclideanRelativeInterior_fin m (domG - domA) := by
        simpa [FenchelProgramStronglyConsistent, hDom, domG, domA] using hStrong
      -- Move to intrinsic interior so Chapter 11 disjointness lemmas apply.
      have h0_intr :
          (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ (domG - domA) := by
        -- `euclideanRelativeInterior_fin = intrinsicInterior` on `Fin m → ℝ`.
        have h0' : (0 : Fin m → ℝ) ∈ euclideanRelativeInterior_fin m (domG - domA) := h0_ri
        rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
          (n := m) (C := domG - domA)] at h0'
        exact h0'
      -- If `0` lies in the intrinsic interior of the difference, then the intrinsic interiors
      -- of `domG` and `domA` cannot be disjoint, so they share a point.
      have hNotDisj :
          ¬ Disjoint (intrinsicInterior ℝ domG) (intrinsicInterior ℝ domA) := by
        intro hDisj
        have h0_not :
            (0 : Fin m → ℝ) ∉ intrinsicInterior ℝ (domG - domA) :=
          (disjoint_intrinsicInterior_iff_zero_not_mem_intrinsicInterior_sub m domG domA
            hConv.1 hConv.2).1 hDisj
        exact h0_not h0_intr
      rcases (Set.not_disjoint_iff.1 hNotDisj) with ⟨y, hyG_intr, hyA_intr⟩
      -- Convert the intrinsic-interior facts back to `euclideanRelativeInterior_fin`.
      have hyG_ri : y ∈ euclideanRelativeInterior_fin m domG := by
        -- Rewrite the goal using `euclideanRelativeInterior_fin = intrinsicInterior`.
        rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
          (n := m) (C := domG)]
        exact hyG_intr
      have hyA_ri : y ∈ euclideanRelativeInterior_fin m domA := by
        rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
          (n := m) (C := domA)]
        exact hyA_intr
      -- Use the linear-image relative-interior identity to pull the `domA` witness back to
      -- a relative-interior point of `domF`.
      have hyImage : y ∈ A '' euclideanRelativeInterior_fin n domF := by
        -- Rewrite `hyA_ri` using `ri(domA) = A '' ri(domF)`.
        have hyA_ri' : y ∈ euclideanRelativeInterior_fin m domA := hyA_ri
        -- Change the goal by rewriting the set.
        simpa [hRiImage] using hyA_ri'
      rcases hyImage with ⟨x, hx_ri, rfl⟩
      -- The common point is `A x`, with `x ∈ ri(dom f)` and `A x ∈ ri(dom g)`.
      refine ⟨x, ?_, ?_⟩
      · simpa [domF] using hx_ri
      · simpa [domG] using hyG_ri
    · rintro ⟨x, hx_riF, hx_riG⟩
      -- Starting from `x ∈ ri(dom f)` and `A x ∈ ri(dom g)`, build the witness `0 = y - y`
      -- with `y = A x` in the relative-interior difference.
      have hxG_intr : A x ∈ intrinsicInterior ℝ domG := by
        have hxG_ri : A x ∈ euclideanRelativeInterior_fin m domG := by
          simpa [domG] using hx_riG
        -- Rewrite the hypothesis into intrinsic interior.
        rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
          (n := m) (C := domG)] at hxG_ri
        exact hxG_ri
      -- Place `A x` in `ri(domA)` using `ri(A(domF)) = A(ri(domF))`.
      have hxA_ri : A x ∈ euclideanRelativeInterior_fin m domA := by
        have hxImage : A x ∈ A '' euclideanRelativeInterior_fin n domF := by
          refine ⟨x, ?_, rfl⟩
          simpa [domF] using hx_riF
        -- Rewrite the target relative-interior set using `hRiImage`.
        -- This avoids embedding a proof inside a term.
        have : A x ∈ euclideanRelativeInterior_fin m domA := by
          -- After rewriting, the goal is exactly `hxImage`.
          -- (The rewrite is on sets, so the goal becomes membership in `A '' ...`.)
          simpa [hRiImage] using hxImage
        exact this
      have hxA_intr : A x ∈ intrinsicInterior ℝ domA := by
        have hxA_ri' : A x ∈ euclideanRelativeInterior_fin m domA := hxA_ri
        rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
          (n := m) (C := domA)] at hxA_ri'
        exact hxA_ri'
      -- Show `0 ∈ intrinsicInterior(domG - domA)` by rewriting to the difference of intrinsic
      -- interiors and using the witness `0 = (A x) - (A x)`.
      have h0_mem_intrSub :
          (0 : Fin m → ℝ) ∈ intrinsicInterior ℝ (domG - domA) := by
        have hsubEq :
            intrinsicInterior ℝ (domG - domA) =
              intrinsicInterior ℝ domG - intrinsicInterior ℝ domA :=
          intrinsicInterior_sub_eq (n := m) (C₁ := domG) (C₂ := domA) hConv.1 hConv.2
        -- Reduce to membership in the set difference of intrinsic interiors.
        rw [hsubEq]
        change (0 : Fin m → ℝ) ∈
          Set.image2 (fun a b : Fin m → ℝ => a - b) (intrinsicInterior ℝ domG)
            (intrinsicInterior ℝ domA)
        exact ⟨A x, hxG_intr, A x, hxA_intr, sub_self (A x)⟩
      have h0_mem_ri :
          (0 : Fin m → ℝ) ∈ euclideanRelativeInterior_fin m (domG - domA) := by
        -- Rewrite the goal into intrinsic interior.
        rw [helperForTheorem_6_27_1_euclideanRelativeInterior_fin_eq_intrinsicInterior
          (n := m) (C := domG - domA)]
        exact h0_mem_intrSub
      -- Translate back to the strong-consistency definition.
      have hStrong :
          FenchelProgramStronglyConsistent A f g := by
        simpa [FenchelProgramStronglyConsistent, hDom, domG, domA] using h0_mem_ri
      exact hStrong

end Section31
end Chap06
