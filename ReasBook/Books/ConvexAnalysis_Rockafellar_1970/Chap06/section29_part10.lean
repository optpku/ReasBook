/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part9

open scoped Pointwise

section Chap06
section Section29

local notation "ConvexBifunction" => BundledConvexBifunction

/-- Helper for Corollary 6.29.5: strict consistency and finite optimal value force the
perturbation function to be proper. -/
lemma helperForCorollary_6_29_5_perturbationFunctionProper_of_strictConsistency
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F))
    (hstrict : generalizedConvexProgramStrictlyConsistent F) :
    ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ))
      (generalizedConvexProgramPerturbationFunction F) := by
  let p : (Fin m → ℝ) → EReal := helperForCorollary_6_29_4_perturbationFunction F
  have hpConv : ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  have hri :
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) :=
    -- Strict consistency is the relative-interior input used in Corollary 6.29.4.
    helperForCorollary_6_29_4_zero_mem_relativeInterior_effectiveDomain F (Or.inr hstrict)
  have hsub :
      Set.Nonempty (subdifferentialAt p 0) :=
    -- Corollary 6.29.4 already converts that relative-interior condition into a subgradient.
    helperForCorollary_6_29_4_subdifferentialNonemptyAtOrigin F hfinite hri
  -- A subgradient at the origin upgrades the convex perturbation function to a proper one.
  simpa [p] using
    (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
      p hpConv 0 hpFinite).1 hsub

/-- Helper for Corollary 6.29.5: strict consistency chooses the open convex neighborhood
`interior (dom F)` containing the origin. -/
lemma helperForCorollary_6_29_5_interior_bifunctionEffectiveDomain_open_convex_mem_zero
    {m n : ℕ} (F : ConvexBifunction m n)
    (hstrict : generalizedConvexProgramStrictlyConsistent F) :
    IsOpen (interior (bifunctionEffectiveDomain F.1)) ∧
      Convex ℝ (interior (bifunctionEffectiveDomain F.1)) ∧
      (0 : Fin m → ℝ) ∈ interior (bifunctionEffectiveDomain F.1) := by
  refine ⟨isOpen_interior, ?_, hstrict⟩
  -- Proposition 6.29.2 makes `dom F` convex, so its interior is convex as well.
  exact ((proposition_29_2 (F := F.1) F.2).2.2).interior

/-- Helper for Corollary 6.29.5: on the interior of `dom F`, the perturbation function avoids
both `+∞` and `-∞`. -/
lemma helperForCorollary_6_29_5_finiteOn_interior_bifunctionEffectiveDomain
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F))
    (hstrict : generalizedConvexProgramStrictlyConsistent F) :
    ∀ u ∈ interior (bifunctionEffectiveDomain F.1),
      generalizedConvexProgramPerturbationFunction F u ≠ (⊤ : EReal) ∧
        generalizedConvexProgramPerturbationFunction F u ≠ (⊥ : EReal) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p :=
    helperForCorollary_6_29_5_perturbationFunctionProper_of_strictConsistency F hfinite hstrict
  have hdom :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = bifunctionEffectiveDomain F.1 := by
    -- Theorem 6.29.1 identifies the perturbation effective domain with `dom F`.
    calc
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = erealDom p := by
        ext u
        simp [p, effectiveDomain_eq, erealDom]
      _ = bifunctionEffectiveDomain F.1 :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.1
  intro u huInt
  have huDom :
      u ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ)) p := by
    -- Interior points of `dom F` stay in the effective domain after rewriting Theorem 6.29.1.
    simpa [hdom] using (interior_subset huInt)
  refine ⟨?_, ?_⟩
  · -- Effective-domain membership excludes the value `+∞`.
    exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin m → ℝ))) (f := p) huDom
  · -- Properness excludes the value `-∞` everywhere on the ambient space.
    simpa [p] using hproper.2.2 u (by simp)

/-- Helper for Corollary 6.29.5: properness makes the perturbation function continuous on the
interior of `dom F`. -/
lemma helperForCorollary_6_29_5_continuousOn_interior_bifunctionEffectiveDomain
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F))
    (hstrict : generalizedConvexProgramStrictlyConsistent F) :
    ContinuousOn (generalizedConvexProgramPerturbationFunction F)
      (interior (bifunctionEffectiveDomain F.1)) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  let domp : Set (Fin m → ℝ) := effectiveDomain (Set.univ : Set (Fin m → ℝ)) p
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p :=
    helperForCorollary_6_29_5_perturbationFunctionProper_of_strictConsistency F hfinite hstrict
  have hdom :
      domp = bifunctionEffectiveDomain F.1 := by
    -- Theorem 6.29.1 rewrites the perturbation effective domain as `dom F`.
    calc
      domp = erealDom p := by
        ext u
        simp [domp, p, effectiveDomain_eq, erealDom]
      _ = bifunctionEffectiveDomain F.1 :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.1
  have hpreim :
      ((fun x : EuclideanSpace ℝ (Fin m) => x.ofLp) ⁻¹' domp) = e.symm '' domp := by
    ext y
    constructor
    · intro hy
      exact ⟨y.ofLp, hy, by simp [e]⟩
    · rintro ⟨x, hx, rfl⟩
      simpa [e] using hx
  have hcontRi :=
    (hpreim ▸ convexFunction_continuousOn_ri_effectiveDomain_of_proper (f := p) hproper)
  have hcontFin :
      ContinuousOn p (euclideanRelativeInterior_fin m domp) := by
    -- Transport continuity back from `EuclideanSpace` to `Fin m → ℝ`.
    simpa [p] using
      hcontRi.comp (s := euclideanRelativeInterior_fin m domp)
        (show ContinuousOn (fun x : Fin m → ℝ => e.symm x) (euclideanRelativeInterior_fin m domp)
          from e.symm.continuous.continuousOn)
        (by
          intro x hx
          simpa [e, domp] using
            (mem_euclideanRelativeInterior_fin_iff (n := m) (C := domp) (x := x)).1 hx)
  have hintSubset :
      interior (bifunctionEffectiveDomain F.1) ⊆ euclideanRelativeInterior_fin m domp := by
    intro x hx
    have hxri :
        x ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1) :=
      helperForTheorem_23_4_mem_relativeInterior_of_mem_interior (n := m)
        (C := bifunctionEffectiveDomain F.1) hx
    simpa [hdom] using hxri
  -- Restrict the relative-interior continuity statement to the interior neighborhood.
  simpa [p] using hcontFin.mono hintSubset

/-- Helper for Corollary 6.29.5: the Kuhn--Tucker set is the negated image of the Euclideanized
perturbation subdifferential at the origin. -/
lemma helperForCorollary_6_29_5_kuhnTuckerSet_eq_negImage_subdifferentialPreimage
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} =
      (fun v : Fin m → ℝ => -v) ''
        (((dotProductEquiv ℝ (Fin m)) ⁻¹'
          subdifferentialAt (generalizedConvexProgramPerturbationFunction F) 0)) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  ext uStar
  constructor
  · intro huStar
    have hnegMem :
        -uStar ∈ ((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt p 0) := by
      -- Corollary 6.29.4 already identifies the preimage fiber with the negated Kuhn--Tucker set.
      rw [helperForCorollary_6_29_4_subdifferentialPreimage_eq_negImage_kuhnTuckerSet F hfinite]
      exact ⟨uStar, huStar, by simp⟩
    -- Reinsert that preimage witness through one more negation to recover `uStar`.
    exact ⟨-uStar, hnegMem, by simp⟩
  · rintro ⟨v, hv, rfl⟩
    -- Rewrite preimage membership back into the Corollary 6.29.4 Kuhn--Tucker description.
    rw [helperForCorollary_6_29_4_subdifferentialPreimage_eq_negImage_kuhnTuckerSet F hfinite] at hv
    rcases hv with ⟨uStar, huStar, hvEq⟩
    have : uStar = -v := by
      simpa using congrArg Neg.neg hvEq
    simpa [this] using huStar

/-- Helper for Corollary 6.29.5: at the origin, the Euclideanized perturbation subdifferential is
nonempty, closed, bounded, and convex. -/
lemma helperForCorollary_6_29_5_subdifferentialPreimage_nonempty_closed_bounded_convex_at_origin
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F))
    (hstrict : generalizedConvexProgramStrictlyConsistent F) :
    let p := generalizedConvexProgramPerturbationFunction F
    let C := ((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt p 0)
    C.Nonempty ∧ IsClosed C ∧ Bornology.IsBounded C ∧ Convex ℝ C := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  let C : Set (Fin m → ℝ) := ((dotProductEquiv ℝ (Fin m)) ⁻¹' subdifferentialAt p 0)
  have hproper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p :=
    helperForCorollary_6_29_5_perturbationFunctionProper_of_strictConsistency F hfinite hstrict
  have hpConv : ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  have hclosed :
      IsClosed C := by
    -- Theorem 23.2 gives closedness of the vectorized subdifferential at every finite point.
    simpa [C, p] using
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        p hpConv 0 hpFinite (0 : Module.Dual ℝ (Fin m → ℝ))).2.1
  have hconv :
      Convex ℝ C := by
    -- The same theorem also gives convexity of that vectorized subdifferential.
    simpa [C, p] using
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        p hpConv 0 hpFinite (0 : Module.Dual ℝ (Fin m → ℝ))).2.2.1
  have hdom :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = bifunctionEffectiveDomain F.1 := by
    -- Theorem 6.29.1 identifies `dom p` with `dom F`.
    calc
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = erealDom p := by
        ext u
        simp [p, effectiveDomain_eq, erealDom]
      _ = bifunctionEffectiveDomain F.1 :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.1
  have hsubAndBdd :
      Set.Nonempty (subdifferentialAt p 0) ∧ Bornology.IsBounded C := by
    -- Theorem 23.4 turns strict consistency into nonemptiness and boundedness at the origin.
    have h0Int :
        (0 : Fin m → ℝ) ∈ interior (effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) := by
      simpa [hdom] using hstrict
    exact
      ((subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        p hproper 0).2.2.1).2 h0Int
  have hnonempty : C.Nonempty := by
    rcases hsubAndBdd.1 with ⟨g, hg⟩
    -- Convert a dual subgradient into its Euclidean representative.
    exact ⟨(dotProductEquiv ℝ (Fin m)).symm g, by simpa [C] using hg⟩
  exact ⟨hnonempty, hclosed, hsubAndBdd.2, hconv⟩

/-- Helper for Corollary 6.29.5: the Kuhn--Tucker vectors form a nonempty closed bounded convex
set. -/
lemma helperForCorollary_6_29_5_kuhnTuckerSet_nonempty_closed_bounded_convex
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F))
    (hstrict : generalizedConvexProgramStrictlyConsistent F) :
    {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar}.Nonempty ∧
      IsClosed {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} ∧
      Bornology.IsBounded {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} ∧
      Convex ℝ {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} := by
  let C : Set (Fin m → ℝ) :=
    ((dotProductEquiv ℝ (Fin m)) ⁻¹'
      subdifferentialAt (generalizedConvexProgramPerturbationFunction F) 0)
  let K : Set (Fin m → ℝ) := {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar}
  let negEquiv : (Fin m → ℝ) ≃L[ℝ] (Fin m → ℝ) := ContinuousLinearEquiv.neg ℝ
  rcases
      helperForCorollary_6_29_5_subdifferentialPreimage_nonempty_closed_bounded_convex_at_origin
        F hfinite hstrict with
    ⟨hCne, hCclosed, hCbounded, hCconv⟩
  have hEq : K = (fun v : Fin m → ℝ => -v) '' C :=
    helperForCorollary_6_29_5_kuhnTuckerSet_eq_negImage_subdifferentialPreimage F hfinite
  have hnegEq : (negEquiv '' C : Set (Fin m → ℝ)) = -C := by
    ext x
    simp [negEquiv]
  have hKne : K.Nonempty := by
    rcases hCne with ⟨v, hv⟩
    -- Negating a point of the subdifferential preimage gives a Kuhn--Tucker vector.
    exact ⟨-v, by rw [hEq]; exact ⟨v, hv, rfl⟩⟩
  have hKclosedImage : IsClosed (-C) := by
    -- Negation is a homeomorphism, so it preserves closed subsets.
    convert (negEquiv.toHomeomorph.isClosed_image (s := C)).2 hCclosed using 1
    exact hnegEq.symm
  have hKboundedImage : Bornology.IsBounded (-C) := by
    -- The negation map is Lipschitz, hence it preserves boundedness.
    convert negEquiv.lipschitz.isBounded_image hCbounded using 1
    exact hnegEq.symm
  have hKconvImage : Convex ℝ (-C) := by
    -- Convexity also transports through the linear negation map.
    convert hCconv.linear_image negEquiv.toLinearMap using 1
    exact hnegEq.symm
  have hKclosed : IsClosed K := by
    simpa [hEq] using hKclosedImage
  have hKbounded : Bornology.IsBounded K := by
    simpa [hEq] using hKboundedImage
  have hKconv : Convex ℝ K := by
    simpa [hEq] using hKconvImage
  exact ⟨hKne, hKclosed, hKbounded, hKconv⟩

-- Route correction: the previous attempt failed because this part file had no main corollary
-- declaration. We now insert the statement here and assemble it from the local 6.29.5 helpers.
/-- Corollary 6.29.5: Let `F` be a convex bifunction from `ℝ^m` to `ℝ^n`. Suppose that the
optimal value in the associated generalized convex program `(P)` is finite and that `(P)` is
strictly consistent. Then there is an open convex neighborhood of `0` in `ℝ^m` on which `inf F`
is finite and continuous. Moreover, the Kuhn--Tucker vectors for `(P)` form a nonempty closed
bounded convex subset of `ℝ^m`. -/
theorem generalizedConvexProgram_exists_openConvexNeighborhood_zero_finite_continuousOn_and_kuhnTuckerSet_nonempty_closed_bounded_convex
    {m n : ℕ} (F : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F))
    (hstrict : generalizedConvexProgramStrictlyConsistent F) :
    ∃ U : Set (Fin m → ℝ),
      IsOpen U ∧
        Convex ℝ U ∧
          (0 : Fin m → ℝ) ∈ U ∧
            (∀ u ∈ U,
              generalizedConvexProgramPerturbationFunction F u ≠ (⊤ : EReal) ∧
                generalizedConvexProgramPerturbationFunction F u ≠ (⊥ : EReal)) ∧
              ContinuousOn (generalizedConvexProgramPerturbationFunction F) U ∧
                {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar}.Nonempty ∧
                  IsClosed {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} ∧
                    Bornology.IsBounded {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} ∧
                      Convex ℝ {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} := by
  let U : Set (Fin m → ℝ) := interior (bifunctionEffectiveDomain F.1)
  rcases
      helperForCorollary_6_29_5_interior_bifunctionEffectiveDomain_open_convex_mem_zero
        F hstrict with
    ⟨hUopen, hUconv, hUzero⟩
  have hUfinite :
      ∀ u ∈ U,
        generalizedConvexProgramPerturbationFunction F u ≠ (⊤ : EReal) ∧
          generalizedConvexProgramPerturbationFunction F u ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_5_finiteOn_interior_bifunctionEffectiveDomain F hfinite hstrict
  have hUcont :
      ContinuousOn (generalizedConvexProgramPerturbationFunction F) U :=
    helperForCorollary_6_29_5_continuousOn_interior_bifunctionEffectiveDomain F hfinite hstrict
  rcases
      helperForCorollary_6_29_5_kuhnTuckerSet_nonempty_closed_bounded_convex
        F hfinite hstrict with
    ⟨hKnonempty, hKclosed, hKbounded, hKconv⟩
  -- Assemble the chosen neighborhood `U = interior (dom F)` and the transported Kuhn--Tucker
  -- geometry into the textbook conclusion.
  refine ⟨U, hUopen, hUconv, hUzero, ?_, hUcont, hKnonempty, hKclosed, hKbounded, hKconv⟩
  intro u hu
  exact hUfinite u hu

/-- Helper for Corollary 6.29.6: a `-∞` value forces the perturbation function to be improper. -/
lemma helperForCorollary_6_29_6_perturbationFunction_improper_of_exists_bot
    {m n : ℕ} (F : ConvexBifunction m n)
    (hbot :
      ∃ u0 : Fin m → ℝ,
        generalizedConvexProgramPerturbationFunction F u0 = (⊥ : EReal)) :
    ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ))
      (generalizedConvexProgramPerturbationFunction F) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hpConv : ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  refine ⟨?_, ?_⟩
  · -- Theorem 6.29.1 supplies convexity of the perturbation function on the whole space.
    simpa [p, ConvexFunction] using hpConv
  · intro hproper
    rcases hproper with ⟨_, _, hneBot⟩
    rcases hbot with ⟨u0, hu0⟩
    -- Proper convex functions never attain `-∞`, so the given witness contradicts properness.
    exact hneBot u0 (by simp) (by simpa [p] using hu0)

/-- Helper for Corollary 6.29.6: once the perturbation function hits `-∞`, it equals `-∞` on
the relative interior of `dom F`. -/
lemma helperForCorollary_6_29_6_eq_bot_on_relativeInterior_bifunctionEffectiveDomain
    {m n : ℕ} (F : ConvexBifunction m n)
    (hbot :
      ∃ u0 : Fin m → ℝ,
        generalizedConvexProgramPerturbationFunction F u0 = (⊥ : EReal)) :
    ∀ u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1),
      generalizedConvexProgramPerturbationFunction F u = (⊥ : EReal) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have himproper :
      ImproperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p :=
    helperForCorollary_6_29_6_perturbationFunction_improper_of_exists_bot F hbot
  have hdom :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = bifunctionEffectiveDomain F.1 := by
    -- Theorem 6.29.1 identifies the effective domain of the perturbation function with `dom F`.
    calc
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = erealDom p := by
        ext u
        simp [p, effectiveDomain_eq, erealDom]
      _ = bifunctionEffectiveDomain F.1 :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.1
  intro u hu
  have hu' :
      (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).symm u ∈
        euclideanRelativeInterior m
          ((EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).symm ''
            effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) := by
    -- Convert the finite-coordinate relative interior statement into the Euclidean version used
    -- by Theorem 7.2, then rewrite the domain via Theorem 6.29.1.
    have huEuclid :
        (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).symm u ∈
          euclideanRelativeInterior m
            ((EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).symm ''
              bifunctionEffectiveDomain F.1) :=
      (mem_euclideanRelativeInterior_fin_iff (n := m) (C := bifunctionEffectiveDomain F.1)
        (x := u)).1 hu
    simpa [hdom] using huEuclid
  have hpreim :
      ((fun x : EuclideanSpace ℝ (Fin m) => (x : Fin m → ℝ)) ⁻¹'
        effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) =
        (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).symm ''
          effectiveDomain (Set.univ : Set (Fin m → ℝ)) p := by
    ext x
    constructor
    · intro hx
      exact ⟨x.ofLp, hx, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  have hu'' :
      (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).symm u ∈
        euclideanRelativeInterior m
          ((fun x : EuclideanSpace ℝ (Fin m) => (x : Fin m → ℝ)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) := by
    -- The Euclidean equivalence image agrees with the coercion preimage used in Chapter 2.
    simpa [hpreim] using hu'
  -- The Chapter 2 improper-function theorem propagates the `-∞` value across `ri (dom p)`.
  simpa [p] using
    improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain (f := p) himproper
      (x := (EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)).symm u) hu''

/-- Helper for Corollary 6.29.6: outside `dom F`, the perturbation function equals `+∞`. -/
lemma helperForCorollary_6_29_6_eq_top_of_not_mem_bifunctionEffectiveDomain
    {m n : ℕ} (F : ConvexBifunction m n) :
    ∀ u : Fin m → ℝ,
      u ∉ bifunctionEffectiveDomain F.1 →
        generalizedConvexProgramPerturbationFunction F u = (⊤ : EReal) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hdom :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = bifunctionEffectiveDomain F.1 := by
    -- Theorem 6.29.1 again rewrites the perturbation effective domain as `dom F`.
    calc
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = erealDom p := by
        ext u
        simp [p, effectiveDomain_eq, erealDom]
      _ = bifunctionEffectiveDomain F.1 :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.1
  intro u hu
  have huNotDom :
      u ∉ effectiveDomain (Set.univ : Set (Fin m → ℝ)) p := by
    simpa [hdom] using hu
  by_contra huTop
  have huDom :
      u ∈ effectiveDomain (Set.univ : Set (Fin m → ℝ)) p := by
    -- If the value were not `+∞`, the point would lie in the effective domain by definition.
    rw [effectiveDomain_eq]
    simp [lt_top_iff_ne_top, p, huTop]
  exact huNotDom huDom

-- Proof sketch: package the `-∞` witness into improperness of the perturbation function, apply
-- the Chapter 2 theorem on `ri (dom p)`, and use the domain characterization from Theorem 6.29.1
-- for the off-domain `+∞` branch.
/-- Corollary 6.29.6: Let `F` be any convex bifunction from `ℝ^m` to `ℝ^n`. If there exists
`u ∈ ℝ^m` such that `inf F u = -∞`, then `inf F u = -∞` for every
`u ∈ ri (dom F)`, whereas `inf F u = +∞` for every `u ∉ dom F`. -/
theorem generalizedConvexProgram_perturbationFunction_eq_bot_on_relativeInterior_bifunctionEffectiveDomain_of_exists_bot
    {m n : ℕ} (F : ConvexBifunction m n)
    (hbot :
      ∃ u0 : Fin m → ℝ,
        generalizedConvexProgramPerturbationFunction F u0 = (⊥ : EReal)) :
    (∀ u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1),
      generalizedConvexProgramPerturbationFunction F u = (⊥ : EReal)) ∧
      (∀ u ∉ bifunctionEffectiveDomain F.1,
        generalizedConvexProgramPerturbationFunction F u = (⊤ : EReal)) := by
  constructor
  · -- The relative-interior branch is exactly the propagated `-∞` statement.
    exact helperForCorollary_6_29_6_eq_bot_on_relativeInterior_bifunctionEffectiveDomain F hbot
  · -- Off the effective domain, the perturbation function is forced to be `+∞`.
    exact helperForCorollary_6_29_6_eq_top_of_not_mem_bifunctionEffectiveDomain F

/-- Helper for Corollary 6.29.7: the graph function of `F` written in the standard
`Fin (m + n) → ℝ` coordinates. -/
noncomputable abbrev helperForCorollary_6_29_7_coordinateGraphFunction {m n : ℕ}
    (F : ConvexBifunction m n) : (Fin (m + n) → ℝ) → EReal :=
  fun z => F.1 (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))

/-- Helper for Corollary 6.29.7: the coordinate-space linear projection recovering the
perturbation variable from a graph point in `ℝ^(m+n)`. -/
noncomputable abbrev helperForCorollary_6_29_7_coordinateProjection {m n : ℕ} :
    (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
  LinearMap.pi (fun i : Fin m =>
    (LinearMap.proj (i := Fin.castAdd n i) : (Fin (m + n) → ℝ) →ₗ[ℝ] ℝ))

/-- Helper for Corollary 6.29.7: any optimal solution already forces the optimal value of the
generalized convex program to be finite. -/
lemma helperForCorollary_6_29_7_optimalValue_finite_of_optimalSolution
    {m n : ℕ} (F : ConvexBifunction m n) {x : Fin n → ℝ}
    (hx : x ∈ generalizedConvexProgramOptimalSolutionSet F) :
    IsFiniteEReal (generalizedConvexProgramOptimalValue F) := by
  rcases hx with ⟨hxFeasible, hxValue, hxNeBot⟩
  have hopt_ne_top : generalizedConvexProgramOptimalValue F ≠ (⊤ : EReal) := by
    -- Feasibility means the displayed objective value is finite above, hence so is the optimum.
    have hltTop : generalizedConvexProgramOptimalValue F < (⊤ : EReal) := by
      simpa [generalizedConvexProgramFeasibleSet, erealDom, hxValue] using hxFeasible
    exact ne_of_lt hltTop
  have hopt_ne_bot : generalizedConvexProgramOptimalValue F ≠ (⊥ : EReal) := by
    -- The optimality equality transports the non-`⊥` objective value to the optimum.
    simpa [hxValue] using hxNeBot
  exact ⟨hopt_ne_top, hopt_ne_bot⟩

/-- Helper for Corollary 6.29.7: the perturbation function is the image-under-linear-map infimum
of the coordinate graph function under first-coordinate projection. -/
lemma helperForCorollary_6_29_7_perturbationFunction_eq_imageUnderLinearMap_graphProjection
    {m n : ℕ} (F : ConvexBifunction m n) :
    generalizedConvexProgramPerturbationFunction F =
      imageUnderLinearMap
        (helperForCorollary_6_29_7_coordinateProjection (m := m) (n := n))
        (helperForCorollary_6_29_7_coordinateGraphFunction F) := by
  funext u
  let A : (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    helperForCorollary_6_29_7_coordinateProjection (m := m) (n := n)
  let h : (Fin (m + n) → ℝ) → EReal :=
    helperForCorollary_6_29_7_coordinateGraphFunction F
  have hSet :
      {z : EReal | ∃ y : Fin (m + n) → ℝ, A y = u ∧ z = h y} =
        {z : EReal | ∃ p : (Fin m → ℝ) × (Fin n → ℝ),
          LinearMap.fst ℝ (Fin m → ℝ) (Fin n → ℝ) p = u ∧ z = graphFunction F.1 p} := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      -- Convert the coordinate witness back to the product-space witness used in Theorem 6.29.1.
      refine ⟨((fun i => y (Fin.castAdd n i)), fun j => y (Fin.natAdd m j)), ?_, ?_⟩
      · simpa [A] using hy
      · simp [h, graphFunction]
    · rintro ⟨p, hp, rfl⟩
      -- Repackage the product-space witness into appended coordinates.
      refine ⟨Fin.append p.1 p.2, ?_, ?_⟩
      · ext i
        simpa [A] using congrArg (fun f : Fin m → ℝ => f i) hp
      · simp [h, helperForCorollary_6_29_7_coordinateGraphFunction, graphFunction]
  -- Replace the image-under-linear-map fiber with the Section 29.1 fiber-infimum formula.
  rw [imageUnderLinearMap, hSet]
  exact helperForTheorem_6_29_1_perturbation_eq_fiberInf_graphFunction F u

/-- Helper for Corollary 6.29.7: polyhedrality of the coordinate graph function descends to the
perturbation function by first-coordinate projection. -/
lemma helperForCorollary_6_29_7_perturbationFunction_polyhedral_of_polyhedralGraph
    {m n : ℕ} (F : ConvexBifunction m n)
    (hgraphPoly :
      IsPolyhedralConvexFunction (m + n)
        (helperForCorollary_6_29_7_coordinateGraphFunction F)) :
    IsPolyhedralConvexFunction m (generalizedConvexProgramPerturbationFunction F) := by
  let A : (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    helperForCorollary_6_29_7_coordinateProjection (m := m) (n := n)
  have hImagePoly :
      IsPolyhedralConvexFunction m
        (imageUnderLinearMap A (helperForCorollary_6_29_7_coordinateGraphFunction F)) :=
    helperForCorollary_19_3_1_polyhedral_imageUnderLinearMap
      (A := A) (hfpoly := hgraphPoly)
  -- The projection formula identifies that image function with the perturbation function.
  simpa [A,
    helperForCorollary_6_29_7_perturbationFunction_eq_imageUnderLinearMap_graphProjection F]
    using hImagePoly

/-- Helper for Corollary 6.29.7: a polyhedral graph function and finite optimal value produce a
Kuhn--Tucker vector by subdifferentiability of the perturbation function at the origin. -/
lemma helperForCorollary_6_29_7_exists_kuhnTuckerVector_of_polyhedralGraph_and_finiteOptimalValue
    {m n : ℕ} (F : ConvexBifunction m n)
    (hgraphPoly :
      IsPolyhedralConvexFunction (m + n)
        (helperForCorollary_6_29_7_coordinateGraphFunction F))
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    ∃ uStar : Fin m → ℝ, IsKuhnTuckerVector F uStar := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  have hpPoly : IsPolyhedralConvexFunction m p :=
    helperForCorollary_6_29_7_perturbationFunction_polyhedral_of_polyhedralGraph
      F hgraphPoly
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite F hfinite
  rcases polyhedralConvex_subdifferentiable_and_subdifferential_polyhedral p hpPoly hpFinite with
    ⟨hsubNonempty, _hsubPoly, _hdirProper, _hdirPoly, _hdirEq⟩
  rcases hsubNonempty with ⟨g, hg⟩
  have hgEuclidean :
      ((dotProductEquiv ℝ (Fin m)).symm g) ∈ euclideanSubdifferentialAt p 0 := by
    -- Switch from the ordinary subdifferential witness to its Euclidean vector representative.
    simpa [p, euclideanSubdifferentialAt] using hg
  let uStar : Fin m → ℝ := -((dotProductEquiv ℝ (Fin m)).symm g)
  have huEuclidean : -uStar ∈ euclideanSubdifferentialAt p 0 := by
    -- The Kuhn--Tucker sign convention uses the negative Euclidean subgradient.
    simpa [uStar] using hgEuclidean
  have hKT :
      IsKuhnTuckerVector F uStar := by
    exact ((generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.2
      hfinite uStar).2 huEuclidean
  exact ⟨uStar, hKT⟩

-- Route correction: the missing corollary needs one new polyhedral branch, but the strong/strict
-- route should still follow Corollaries 6.29.4 and 6.29.3 exactly.
/-- Corollary 6.29.7: Let `F` be a closed proper convex bifunction from `ℝ^m` to `ℝ^n`.
Suppose that the associated generalized convex program `(P)` is strongly consistent, or strictly
consistent, or that its graph function is polyhedral convex and `(P)` is consistent. Then a given
vector `x ∈ ℝ^n` is an optimal solution to `(P)` if and only if there exists a multiplier
`uStar ∈ ℝ^m` such that `(uStar, x)` is a saddle point of the generalized-program Lagrangian. -/
theorem generalizedConvexProgram_optimalSolution_iff_exists_saddlePointOfGeneralizedConvexProgramLagrangian_under_qualification
    {m n : ℕ} (F : ConvexBifunction m n) (hclosed : IsClosedBifunction F.1)
    (hproper : IsProperBifunction F.1) (x : Fin n → ℝ)
    (hqualification :
      generalizedConvexProgramStronglyConsistent F ∨
        generalizedConvexProgramStrictlyConsistent F ∨
          (IsPolyhedralConvexFunction (m + n)
              (helperForCorollary_6_29_7_coordinateGraphFunction F) ∧
            generalizedConvexProgramConsistent F)) :
    x ∈ generalizedConvexProgramOptimalSolutionSet F ↔
      ∃ uStar : Fin m → ℝ,
        helperForTheorem_6_29_3_isSaddlePointOfGeneralizedConvexProgramLagrangian F uStar x := by
  constructor
  · intro hx
    have hfinite :
        IsFiniteEReal (generalizedConvexProgramOptimalValue F) :=
      helperForCorollary_6_29_7_optimalValue_finite_of_optimalSolution F hx
    rcases hqualification with hstrong | hrest
    · -- Strong consistency is exactly the Corollary 6.29.4 qualification route.
      rcases
          (generalizedConvexProgram_exists_kuhnTuckerVector_and_originDirectionalDerivative_eq_neg_sInf
            F hfinite (Or.inl hstrong)).1 with
        ⟨uStar, huKT⟩
      refine ⟨uStar, ?_⟩
      -- Theorem 6.29.3 turns Kuhn--Tucker optimality into the desired saddle point.
      exact
        (kuhnTuckerVector_and_optimalSolution_iff_saddlePointOfGeneralizedConvexProgramLagrangian
          F hclosed hproper uStar x).1 ⟨huKT, hx⟩
    · rcases hrest with hstrict | hpoly
      · -- Strict consistency follows the same Corollary 6.29.4 route.
        rcases
            (generalizedConvexProgram_exists_kuhnTuckerVector_and_originDirectionalDerivative_eq_neg_sInf
              F hfinite (Or.inr hstrict)).1 with
          ⟨uStar, huKT⟩
        refine ⟨uStar, ?_⟩
        -- The same saddle-point equivalence finishes the strict-consistency branch.
        exact
          (kuhnTuckerVector_and_optimalSolution_iff_saddlePointOfGeneralizedConvexProgramLagrangian
            F hclosed hproper uStar x).1 ⟨huKT, hx⟩
      · rcases hpoly with ⟨hgraphPoly, _hconsistent⟩
        rcases
            helperForCorollary_6_29_7_exists_kuhnTuckerVector_of_polyhedralGraph_and_finiteOptimalValue
              F hgraphPoly hfinite with
          ⟨uStar, huKT⟩
        refine ⟨uStar, ?_⟩
        -- In the polyhedral branch, the subgradient witness again feeds into Theorem 6.29.3.
        exact
          (kuhnTuckerVector_and_optimalSolution_iff_saddlePointOfGeneralizedConvexProgramLagrangian
            F hclosed hproper uStar x).1 ⟨huKT, hx⟩
  · rintro ⟨uStar, hsaddle⟩
    -- The reverse implication is the easy half of Theorem 6.29.3.
    exact
      (kuhnTuckerVector_and_optimalSolution_iff_saddlePointOfGeneralizedConvexProgramLagrangian
        F hclosed hproper uStar x).2 hsaddle |>.2


end Section29
end Chap06
