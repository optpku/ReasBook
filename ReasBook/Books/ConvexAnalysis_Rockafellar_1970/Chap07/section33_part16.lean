/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part15

section Chap07
section Section33

attribute [local instance] Classical.propDecidable

/-- The parameter domain of a convex bifunction, viewed as the set of `u` for which the
image section `F u` is not identically `⊤`. -/
def convexBifunctionParameterDomain {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Set (Fin m → ℝ) :=
  {u | ∃ x : Fin n → ℝ, F u x ≠ ⊤}

/-- The adjoint domain of a convex bifunction, viewed as the set of `x^*` for which the
adjoint section `F^* x^*` is not identically `⊥`. -/
def convexBifunctionAdjointDomain {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {xStar | ∃ u : Fin m → ℝ, convexBifunctionAdjointPairing F xStar u ≠ ⊥}

/-- A proper polyhedral convex bifunction is a polyhedral convex bifunction whose graph
function is proper convex on the whole space. -/
def IsProperPolyhedralConvexBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsRockafellarPolyhedralConvexBifunction F ∧
    ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F)

/-- The effective parameter domain of a concave bifunction, viewed as the set of `u` for
which the image section `F u` is not identically `-∞`. -/
def concaveBifunctionParameterDomain {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Set (Fin m → ℝ) :=
  {u | ∃ x : Fin n → ℝ, F u x ≠ ⊥}

/-- The effective domain of the genuine convex adjoint of a concave bifunction, viewed as
the set of `x^*` for which `F^* x^*` is not identically `+∞`. -/
def concaveBifunctionAdjointDomain {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {xStar | ∃ u : Fin m → ℝ, concaveBifunctionAdjointPairing F xStar u ≠ ⊤}

/-- A proper polyhedral concave bifunction is a polyhedral concave bifunction in the sense
that its negated graph function is proper polyhedral convex on the whole space. -/
def IsProperPolyhedralConcaveBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsRockafellarConcaveBifunction F ∧
    IsPolyhedralConvexFunction (m + n) (fun z => -graphFunctionOfBifunction F z) ∧
    ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
      (fun z => -graphFunctionOfBifunction F z)

lemma helperForCorollary33_2_2_concaveAdjointDomain_eq_negated_convexAdjointTopDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    concaveBifunctionAdjointDomain F =
      {xStar | ∃ u : Fin m → ℝ,
        convexBifunctionAdjointPairing (fun u' x => -F u' x) (-xStar) u ≠ ⊥} := by
  ext xStar
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    intro hBot
    apply hu
    rw [helperForCorollary33_2_1_concaveAdjoint_eq_neg_convexAdjoint_of_neg
      (F := F) xStar u]
    simpa [hBot]
  · rintro ⟨u, hu⟩
    refine ⟨-u, ?_⟩
    intro hTop
    apply hu
    have hNegTop :
        -convexBifunctionAdjointPairing (fun u' x => -F u' x) (-xStar) u = (⊤ : EReal) := by
      simpa [helperForCorollary33_2_1_concaveAdjoint_eq_neg_convexAdjoint_of_neg
        (F := F) xStar (-u)] using hTop
    simpa using congrArg Neg.neg hNegTop

/-- Helper for Corollary33.2.2: every polyhedral convex function is already closed in the
lower-semicontinuity sense used by `ClosedConvexFunction`. -/
lemma helperForCorollary33_2_2_polyhedralConvexFunction_isClosed
    {k : ℕ}
    {f : (Fin k → ℝ) → EReal}
    (hfpoly : IsPolyhedralConvexFunction k f) :
    ClosedConvexFunction f := by
  -- Step 1: polyhedrality makes the packed epigraph a closed polyhedral set.
  have hclosed_transformedEpigraph :
      IsClosed
        ((fun p => (prodLinearEquiv_append_coord (n := k)) p) ''
          epigraph (Set.univ : Set (Fin k → ℝ)) f) := by
    exact
      (helperForTheorem_19_1_polyhedral_imp_closed_finiteFaces
        (n := k + 1)
        (C := ((fun p => (prodLinearEquiv_append_coord (n := k)) p) ''
          epigraph (Set.univ : Set (Fin k → ℝ)) f))
        (by simpa [prodLinearEquiv_append_coord] using hfpoly.2)).1
  let hhome :=
    ((prodLinearEquiv_append_coord (n := k)).toAffineEquiv).toHomeomorphOfFiniteDimensional
  have hclosed_epigraph :
      IsClosed (epigraph (Set.univ : Set (Fin k → ℝ)) f) := by
    have hclosed_image_homeomorph :
        IsClosed
          ((hhome : ((Fin k → ℝ) × ℝ) → (Fin (k + 1) → ℝ)) ''
            epigraph (Set.univ : Set (Fin k → ℝ)) f) := by
      simpa [hhome, AffineEquiv.coe_toHomeomorphOfFiniteDimensional] using
        hclosed_transformedEpigraph
    exact
      (hhome.isClosed_image (s := epigraph (Set.univ : Set (Fin k → ℝ)) f)).1
        hclosed_image_homeomorph
  -- Step 2: closedness of the epigraph is equivalent to lower semicontinuity.
  have hclosed_sublevel :
      ∀ α : ℝ, IsClosed {x : Fin k → ℝ | f x ≤ (α : EReal)} :=
    (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph
      (f := f)).2.mpr hclosed_epigraph
  have hlsc : LowerSemicontinuous f :=
    (lowerSemicontinuous_iff_closed_sublevel_iff_closed_epigraph
      (f := f)).1.mpr hclosed_sublevel
  exact ⟨hfpoly.1, hlsc⟩

/-- Helper for Corollary33.2.2: a proper polyhedral convex bifunction already has the graph
closedness and no-`⊥` package needed by Theorem33.2. -/
lemma helperForCorollary33_2_2_convex_graphClosed_and_noBot
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConvexBifunction F) :
    IsGraphConvexBifunction F ∧
      IsFunctionConvexClosed (graphFunctionOfBifunction F) ∧
      HasNoBotValuesBifunction F := by
  rcases hF with ⟨hF_poly, hGraphProper⟩
  have hPoly : IsRockafellarPolyhedralConvexBifunction F := hF_poly
  rcases hF_poly with ⟨hRock, hGraphPoly⟩
  -- Step 1: properness of the graph function supplies the no-`⊥` convention for `F`.
  have hNoBot : HasNoBotValuesBifunction F := by
    intro u x
    simpa [graphFunctionOfBifunction, Fin.append] using
      hGraphProper.2.2 (Fin.append u x) (by simp)
  -- Step 2: each primal section is polyhedral convex, hence fixed by its one-variable closure.
  have hSectionClosureExact :
      ∀ u x, convexFunctionClosure (F u) x = F u x := by
    intro u x
    have hSectionPoly :
        IsPolyhedralConvexFunction n (F u) :=
      helperForCorollary33_1_3_section_isPolyhedralConvexFunction
        (F := F) hPoly u
    have hSectionClosed :
        ClosedConvexFunction (F u) :=
      helperForCorollary33_2_2_polyhedralConvexFunction_isClosed
        (f := F u) hSectionPoly
    have hClosureEq :
        F u = functionConvexClosure (F u) :=
      helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
        (f := F u) hSectionClosed.2
    calc
      convexFunctionClosure (F u) x = functionConvexClosure (F u) x := by
        rw [← helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
          (hNoBot := hNoBot u)]
      _ = F u x := (congrArg (fun g => g x) hClosureEq).symm
  -- Step 3: exact sectionwise closure upgrades Rockafellar convexity to graph convexity.
  have hGraphConvex :
      IsGraphConvexBifunction F :=
    helperForLemma33_0_14_graphConvex_of_rockafellar_with_exactSectionwiseClosure
      (F := F) hRock hSectionClosureExact hNoBot
  -- Step 4: the graph function itself is polyhedral proper, hence closed under the raw
  -- Section 33 convex closure operator.
  have hGraphClosedConv :
      ClosedConvexFunction (graphFunctionOfBifunction F) :=
    helperForCorollary_19_1_2_closed_of_polyhedral_proper hGraphPoly hGraphProper
  have hGraphClosed :
      IsFunctionConvexClosed (graphFunctionOfBifunction F) :=
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
      (f := graphFunctionOfBifunction F) hGraphClosedConv.2
  exact ⟨hGraphConvex, hGraphClosed, hNoBot⟩

/-!
The following block records the pre-canonical-closure attempt at Corollary 33.2.2.  It is
kept as migration history only: it incorrectly forced the adjoint domain to be universal and
therefore erased the exceptional off-both-domains case from the book.

/-- Helper for Corollary33.2.2: with the current Section 33 object
`convexBifunctionCanonicalAdjointPairing`, the convex branch already satisfies the pairing identity
everywhere for proper polyhedral bifunctions. -/
lemma helperForCorollary33_2_2_convex_pairing_eq_everywhere
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConvexBifunction F) :
    ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      convexBifunctionPairing F u xStar =
        convexBifunctionCanonicalAdjointPairing F xStar u := by
  rcases helperForCorollary33_2_2_convex_graphClosed_and_noBot
      (F := F) hF with ⟨hGraphConvex, _hGraphClosed, hNoBot⟩
  intro u xStar
  let q : (Fin m → ℝ) → EReal := fun u' => -convexBifunctionPairing F u' xStar
  -- Step 1: the fixed-`xStar` negated pairing section is polyhedral convex, hence closed.
  have hqPoly :
      IsPolyhedralConvexFunction m q := by
    simpa [q] using
      (polyhedralConvexBifunction_pairing_sections_and_reconstruction
        (m := m) (n := n) (F := F) hF.1).2.1 xStar
  have hqClosed : ClosedConvexFunction q :=
    helperForCorollary33_2_2_polyhedralConvexFunction_isClosed
      (f := q) hqPoly
  have hqFixEq :
      q = functionConvexClosure q :=
    helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
      (f := q) hqClosed.2
  have hqFix : functionConvexClosure q u = q u := by
    exact (congrArg (fun g => g u) hqFixEq).symm
  -- Step 2: use the Section 33 sign-flip identity to convert the convex closure of `q`
  -- into the concave closure of the original pairing section.
  have hClosureEq :
      concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u =
        convexBifunctionPairing F u xStar := by
    have hSign :
        concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u =
          -convexFunctionClosure q u := by
      rfl
    calc
      concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u =
          -convexFunctionClosure q u := hSign
      _ = -q u := by
        rw [← helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot]
        exact congrArg Neg.neg hqFix
      _ = convexBifunctionPairing F u xStar := by simp [q]
  -- Step 3: Theorem33.2 now collapses to the displayed global equality.
  rcases
      (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).1 F
        ⟨hGraphConvex, hNoBot⟩ with
    ⟨hFirst, _hSecond⟩
  calc
    convexBifunctionPairing F u xStar =
        concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u := by
      symm
      exact hClosureEq
    _ = convexBifunctionCanonicalAdjointPairing F xStar u := by
      symm
      exact hFirst xStar u

/-- Helper bridge for Sections 34 and 35: in the proper polyhedral convex branch, the Section 33
pairing and adjoint-pairing objects already agree globally. This packages the local Corollary
33.2.2 argument into a single reusable theorem so downstream chapters can appeal to an exact
recovery statement without replaying the closure-side proof. -/
lemma helperForSection34_35_section33_convex_pairing_exactRecovery
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConvexBifunction F) :
    ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      convexBifunctionPairing F u xStar =
        convexBifunctionCanonicalAdjointPairing F xStar u :=
  helperForCorollary33_2_2_convex_pairing_eq_everywhere (F := F) hF

/-- Helper for Corollary33.2.2: in the present convex Section 33 interface,
properness of the graph function already provides one primal section with a finite value, and
that single witness forces the displayed adjoint domain to be all of `ℝ^n`. -/
lemma helperForCorollary33_2_2_convex_adjointDomain_eq_univ
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConvexBifunction F) :
    convexBifunctionAdjointDomain F = Set.univ := by
  ext xStar
  constructor
  · intro _hxStar
    simp
  · intro _hxStar
    rcases hF with ⟨_hPoly, hGraphProper⟩
    rcases hGraphProper.2.1 with ⟨p, hp⟩
    rcases p with ⟨z, μ⟩
    -- Step 1: properness gives a graph point where the section value is not `⊤`.
    have hzLe : graphFunctionOfBifunction F z ≤ (μ : EReal) :=
      (mem_epigraph_univ_iff (f := graphFunctionOfBifunction F)).1 hp
    have hzNeTop : graphFunctionOfBifunction F z ≠ (⊤ : EReal) := by
      intro hzTop
      rw [hzTop] at hzLe
      exact not_top_le_coe μ hzLe
    let u₀ : Fin m → ℝ := fun i => z (Fin.castAdd n i)
    let x₀ : Fin n → ℝ := fun j => z (Fin.natAdd m j)
    have hx₀NeTop : F u₀ x₀ ≠ (⊤ : EReal) := by
      simpa [u₀, x₀, graphFunctionOfBifunction, Fin.append] using hzNeTop
    -- Step 2: that one finite section value keeps the convex pairing away from `⊥`
    -- for every dual vector `xStar`.
    refine ⟨u₀, ?_⟩
    have hPairNeBot :
        convexBifunctionPairing F u₀ xStar ≠ (⊥ : EReal) := by
      simpa [convexBifunctionPairing, bifunctionPairingNotation, convexConjugate] using
        helperForTheorem33_1_convexConjugate_ne_bot_of_point
          (f := F u₀) (x₀ := x₀) hx₀NeTop xStar
    simpa [convexBifunctionAdjointPairing] using hPairNeBot

/-- Helper for Corollary33.2.2: on the convex side of the current Section 33 interface,
the displayed exceptional case can never occur because the adjoint domain is already all of
`ℝ^n`. -/
lemma helperForCorollary33_2_2_convex_off_both_domains_impossible
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConvexBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ} :
    ¬ (u ∉ convexBifunctionParameterDomain F ∧
        xStar ∉ convexBifunctionAdjointDomain F) := by
  intro hOutside
  -- Step 1: the new domain computation puts every `xStar` into the displayed adjoint domain.
  have hxStarMem : xStar ∈ convexBifunctionAdjointDomain F := by
    rw [helperForCorollary33_2_2_convex_adjointDomain_eq_univ (F := F) hF]
    simp
  -- Step 2: this contradicts the advertised off-both-domains hypothesis.
  exact hOutside.2 hxStarMem

/-- Helper for Corollary33.2.2: for the current Section 33 closure-side adjoint pairing,
the textbook opposite-infinities disjunction is incompatible with the already-proved global
pairing identity. -/
lemma helperForCorollary33_2_2_convex_exceptional_disjunction_impossible
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConvexBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ}
    (hExceptional :
      (convexBifunctionPairing F u xStar = ⊤ ∧
          convexBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
        (convexBifunctionPairing F u xStar = ⊥ ∧
          convexBifunctionCanonicalAdjointPairing F xStar u = ⊤)) :
    False := by
  -- Step 1: the earlier helper already identifies the two closure-side pairings everywhere.
  have hEq :
      convexBifunctionPairing F u xStar =
        convexBifunctionCanonicalAdjointPairing F xStar u :=
    helperForCorollary33_2_2_convex_pairing_eq_everywhere
      (F := F) hF u xStar
  -- Step 2: each exceptional alternative would force `⊤ = ⊥`.
  rcases hExceptional with hTopBot | hBotTop
  · rcases hTopBot with ⟨hLeft, hRight⟩
    have hAbsurd : (⊤ : EReal) = ⊥ := by
      rw [← hLeft, ← hRight]
      exact hEq
    exact top_ne_bot hAbsurd
  · rcases hBotTop with ⟨hLeft, hRight⟩
    have hAbsurd : (⊥ : EReal) = ⊤ := by
      rw [← hLeft, ← hRight]
      exact hEq
    exact top_ne_bot hAbsurd.symm

/-- Helper for Corollary33.2.2: the convex exceptional conclusion appearing in the current
header is false at every point, because the two displayed closure-side pairing objects are
already equal everywhere. -/
lemma helperForCorollary33_2_2_convex_exceptional_conclusion_false
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConvexBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ} :
    ¬ ((convexBifunctionPairing F u xStar = ⊤ ∧
            convexBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
          (convexBifunctionPairing F u xStar = ⊥ ∧
            convexBifunctionCanonicalAdjointPairing F xStar u = ⊤)) := by
  -- Step 1: convert the advertised exceptional conclusion into the already-normalized
  -- contradiction helper.
  intro hExceptional
  exact
    helperForCorollary33_2_2_convex_exceptional_disjunction_impossible
      (F := F) hF hExceptional

/-- Helper for Corollary33.2.2: at a point lying outside both displayed convex domains, the
current closure-side exceptional implication is itself impossible because its conclusion would
contradict the already-proved global pairing identity. -/
lemma helperForCorollary33_2_2_convex_exceptional_implication_false_at_off_both_domains
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConvexBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ}
    (hOutside :
      u ∉ convexBifunctionParameterDomain F ∧
        xStar ∉ convexBifunctionAdjointDomain F) :
    ¬ ((u ∉ convexBifunctionParameterDomain F ∧
          xStar ∉ convexBifunctionAdjointDomain F) →
        (convexBifunctionPairing F u xStar = ⊤ ∧
            convexBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
          (convexBifunctionPairing F u xStar = ⊥ ∧
            convexBifunctionCanonicalAdjointPairing F xStar u = ⊤)) := by
  -- Step 1: assume the displayed exceptional implication at the current off-domain point.
  intro hClause
  -- Step 2: specialize it and invoke the contradiction helper for the closure-side pairing.
  exact
    helperForCorollary33_2_2_convex_exceptional_disjunction_impossible
      (F := F) hF (u := u) (xStar := xStar) (hClause hOutside)

/-- Helper for Corollary33.2.2: properness of the negated graph function forbids `⊤`-values
for a proper polyhedral concave bifunction. -/
lemma helperForCorollary33_2_2_concave_hasNoTopValues
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConcaveBifunction F) :
    HasNoTopValuesBifunction F := by
  rcases hF with ⟨_hRock, _hPoly, hProper⟩
  intro u x
  -- Step 1: properness of the negated graph function excludes `⊥` on every graph point.
  have hNotBot :
      (fun z => -graphFunctionOfBifunction F z) (Fin.append u x) ≠ (⊥ : EReal) := by
    exact hProper.2.2 (Fin.append u x) (by simp)
  -- Step 2: rewrite the graph point back to `F u x` and undo the outer negation.
  simpa [graphFunctionOfBifunction, Fin.append, EReal.neg_eq_bot_iff] using hNotBot

/-- Helper for Corollary33.2.2: the present Section 33 concave adjoint pairing is already
equal to the primal concave pairing everywhere for a proper polyhedral concave bifunction. -/
lemma helperForCorollary33_2_2_concave_pairing_eq_everywhere
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConcaveBifunction F) :
    ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
      concaveBifunctionPairing F u xStar =
        concaveBifunctionCanonicalAdjointPairing F xStar u := by
  rcases hF with ⟨hRock, hPolyNegGraph, hProperNegGraph⟩
  have hF' : IsProperPolyhedralConcaveBifunction F := ⟨hRock, hPolyNegGraph, hProperNegGraph⟩
  have hNoTop : HasNoTopValuesBifunction F :=
    helperForCorollary33_2_2_concave_hasNoTopValues (F := F) hF'
  let G : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u' x => -F u' x
  -- Step 1: the negated graph function is already a proper polyhedral convex graph function.
  have hGraphConvexG : IsGraphConvexBifunction G := by
    have hConvOnG :
        ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction G) := by
      simpa [G, graphFunctionOfBifunction] using hPolyNegGraph.1
    have hNoBotGraphG :
        ∀ z : Fin (m + n) → ℝ, graphFunctionOfBifunction G z ≠ (⊥ : EReal) := by
      intro z
      simpa [G, graphFunctionOfBifunction] using hProperNegGraph.2.2 z (by simp)
    have hJensenG :=
      (convexFunctionOn_univ_iff_jensen_inequality
        (f := graphFunctionOfBifunction G) hNoBotGraphG).1 hConvOnG
    intro z₁ z₂ _hz₁ _hz₂ a b ha hb hab _hz
    let w : Fin 2 → ℝ := fun i => if i = 0 then a else b
    let x : Fin 2 → (Fin (m + n) → ℝ) := fun i => if i = 0 then z₁ else z₂
    have hw : ∀ i, 0 ≤ w i := by
      intro i
      fin_cases i <;> simp [w, ha, hb]
    have hsum : Finset.univ.sum (fun i => w i) = 1 := by
      simp [w, Fin.sum_univ_two, hab]
    simpa [w, x, Fin.sum_univ_two] using hJensenG 2 w x hw hsum
  have hRockG : IsRockafellarConvexBifunction G :=
    helperForLemma33_0_22_graphConvex_gives_rockafellarConvex
      (F := G) hGraphConvexG
  have hPolyG : IsPolyhedralConvexFunction (m + n) (graphFunctionOfBifunction G) := by
    simpa [G, graphFunctionOfBifunction] using hPolyNegGraph
  have hRockPolyG : IsRockafellarPolyhedralConvexBifunction G := ⟨hRockG, hPolyG⟩
  intro u xStar
  have hSectionEq :
      (fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar) =
        fun u' : Fin m → ℝ => -convexBifunctionPairing G u' (-xStar) := by
    -- Step 2: rewrite the concave pairing section through the negated convex bifunction.
    funext u'
    simpa [G] using
      helperForCorollary33_2_1_concavePairing_eq_neg_convexPairing_of_neg
        (F := F) u' xStar
  have hSectionPoly :
      IsPolyhedralConvexFunction m
        (fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar) := by
    -- Step 3: the negated convex pairing section of `G` is polyhedral convex, hence so is
    -- the present concave pairing section after rewriting by `hSectionEq`.
    have hPoly :
        IsPolyhedralConvexFunction m
          (fun u' : Fin m → ℝ => -convexBifunctionPairing G u' (-xStar)) := by
      simpa [G] using
        (polyhedralConvexBifunction_pairing_sections_and_reconstruction
          (m := m) (n := n) (F := G) hRockPolyG).2.1 (-xStar)
    simpa [hSectionEq] using hPoly
  have hSectionClosed :
      ClosedConvexFunction (fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar) :=
    helperForCorollary33_2_2_polyhedralConvexFunction_isClosed
      (f := fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar) hSectionPoly
  have hSectionFixEq :
      (fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar) =
        functionConvexClosure (fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar) := by
    -- Step 4: closed polyhedral convexity fixes the raw Section 33 convex closure.
    exact
      helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
        (f := fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar) hSectionClosed.2
  have hSectionFix :
      functionConvexClosure (fun u' : Fin m → ℝ => concaveBifunctionPairing F u' xStar) u =
        concaveBifunctionPairing F u xStar := by
    exact (congrArg (fun g => g u) hSectionFixEq).symm
  -- Step 5: substitute the fixed-point identity into Theorem33.2's concave closure formula.
  rcases
      (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).2 F
        ⟨hRock, hNoTop⟩ with
    ⟨hFirst, _hSecond⟩
  calc
    concaveBifunctionPairing F u xStar =
        functionConvexClosure (fun u' => concaveBifunctionPairing F u' xStar) u := by
      symm
      exact hSectionFix
    _ = concaveBifunctionCanonicalAdjointPairing F xStar u := by
      exact (hFirst xStar u).symm

/-- Helper for Corollary33.2.2: after negating the bifunction, the concave parameter-domain
obstruction is exactly the convex parameter-domain obstruction for `-F`. -/
lemma helperForCorollary33_2_2_concave_off_parameterDomain_iff_negated_convex_off_parameterDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} :
    u ∉ concaveBifunctionParameterDomain F ↔
      u ∉ convexBifunctionParameterDomain (fun u' x => -F u' x) := by
  constructor
  · intro hConcave hConvex
    rcases hConvex with ⟨x, hx⟩
    -- Step 1: a convex witness for `-F` produces the corresponding concave witness for `F`.
    have hWitness : F u x ≠ (⊥ : EReal) := by
      intro hBot
      apply hx
      simp [hBot]
    exact hConcave ⟨x, hWitness⟩
  · intro hConvex hConcave
    rcases hConcave with ⟨x, hx⟩
    -- Step 2: conversely, a concave witness for `F` produces a convex witness for `-F`.
    have hWitness : (fun u' x => -F u' x) u x ≠ (⊤ : EReal) := by
      intro hTop
      apply hx
      simpa using hTop
    exact hConvex ⟨x, hWitness⟩

/-- Helper for Corollary33.2.2: failing the current concave adjoint-domain predicate is
equivalent to saying that every corresponding convex pairing of `-F` takes the value `⊤`. -/
lemma helperForCorollary33_2_2_concave_off_adjointDomain_iff_negated_convex_pairing_top_everywhere
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {xStar : Fin n → ℝ} :
    xStar ∉ concaveBifunctionAdjointDomain F ↔
      ∀ u : Fin m → ℝ,
        convexBifunctionPairing (fun u' x => -F u' x) u (-xStar) = ⊤ := by
  constructor
  · intro hOutside u
    have hPairBot : concaveBifunctionPairing F u xStar = ⊥ := by
      by_contra hPairNeBot
      apply hOutside
      -- Step 1: any non-`⊥` pairing value is already a witness for the displayed adjoint
      -- domain predicate.
      refine ⟨u, ?_⟩
      simpa [concaveBifunctionAdjointPairing] using hPairNeBot
    -- Step 2: rewrite through the sign-change identity and cancel the outer negation.
    rw [helperForCorollary33_2_1_concavePairing_eq_neg_convexPairing_of_neg
      (F := F) u xStar] at hPairBot
    simpa using hPairBot
  · intro hTop hMem
    rcases hMem with ⟨u, hu⟩
    have hPairBot : concaveBifunctionPairing F u xStar = ⊥ := by
      -- Step 1: the assumed negated-convex obstruction forces the present concave pairing
      -- value to be `⊥`.
      rw [helperForCorollary33_2_1_concavePairing_eq_neg_convexPairing_of_neg
        (F := F) u xStar, hTop u]
      simp
    -- Step 2: this contradicts the witness showing `xStar` lies in the adjoint domain.
    exact hu (by simpa [concaveBifunctionAdjointPairing] using hPairBot)

/-- Helper for Corollary33.2.2: the remaining concave off-both-domains obstruction rewrites,
after negating `F`, to a convex off-parameter-domain point together with a dual vector whose
entire negated-convex pairing section is `⊤`. -/
lemma helperForCorollary33_2_2_concave_off_both_domains_iff_negated_convex_obstruction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {xStar : Fin n → ℝ} :
    (u ∉ concaveBifunctionParameterDomain F ∧
        xStar ∉ concaveBifunctionAdjointDomain F) ↔
      (u ∉ convexBifunctionParameterDomain (fun u' x => -F u' x) ∧
        ∀ u' : Fin m → ℝ,
          convexBifunctionPairing (fun u'' x => -F u'' x) u' (-xStar) = ⊤) := by
  constructor
  · intro hOutside
    -- Step 1: rewrite each half of the concave obstruction after negating `F`.
    exact
      ⟨(helperForCorollary33_2_2_concave_off_parameterDomain_iff_negated_convex_off_parameterDomain
          (F := F) (u := u)).mp hOutside.1,
        (helperForCorollary33_2_2_concave_off_adjointDomain_iff_negated_convex_pairing_top_everywhere
          (F := F) (xStar := xStar)).mp hOutside.2⟩
  · intro hObstruction
    -- Step 2: transport the normalized negated-convex obstruction back to the original
    -- concave domains.
    exact
      ⟨(helperForCorollary33_2_2_concave_off_parameterDomain_iff_negated_convex_off_parameterDomain
          (F := F) (u := u)).mpr hObstruction.1,
        (helperForCorollary33_2_2_concave_off_adjointDomain_iff_negated_convex_pairing_top_everywhere
          (F := F) (xStar := xStar)).mpr hObstruction.2⟩

/-- Helper for Corollary33.2.2: outside the convex parameter domain, the whole primal section
must already be constantly `⊤`. -/
lemma helperForCorollary33_2_2_allTop_of_off_convexParameterDomain
    {m n : ℕ}
    {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ}
    (hOutside : u ∉ convexBifunctionParameterDomain G) :
    ∀ x : Fin n → ℝ, G u x = ⊤ := by
  intro x
  -- Step 1: if one value were not `⊤`, it would witness membership in the parameter domain.
  by_contra hNotTop
  exact hOutside ⟨x, hNotTop⟩

/-- Helper for Corollary33.2.2: once a convex primal section is constantly `⊤`, its pairing
section is constantly `⊥`. -/
lemma helperForCorollary33_2_2_convex_pairing_eq_bot_of_off_parameterDomain
    {m n : ℕ}
    {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ}
    (hOutside : u ∉ convexBifunctionParameterDomain G) :
    ∀ xStar : Fin n → ℝ, convexBifunctionPairing G u xStar = ⊥ := by
  have hAllTop :
      ∀ x : Fin n → ℝ, G u x = ⊤ :=
    helperForCorollary33_2_2_allTop_of_off_convexParameterDomain
      (G := G) hOutside
  intro xStar
  -- Step 1: unfold the convex pairing and collapse the defining supremum of the constant-`⊤`
  -- section to `⊥`.
  rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
  apply le_antisymm
  · refine iSup_le ?_
    intro x
    simp [hAllTop x]
  · exact bot_le

/-- Helper for Corollary33.2.2: under the current Section 33 concave domain predicates, the
displayed off-both-domains configuration is internally inconsistent after negating `F`. -/
lemma helperForCorollary33_2_2_concave_off_both_domains_impossible
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {xStar : Fin n → ℝ} :
    ¬ (u ∉ concaveBifunctionParameterDomain F ∧
        xStar ∉ concaveBifunctionAdjointDomain F) := by
  intro hOutside
  have hObstruction :
      u ∉ convexBifunctionParameterDomain (fun u' x => -F u' x) ∧
        ∀ u' : Fin m → ℝ,
          convexBifunctionPairing (fun u'' x => -F u'' x) u' (-xStar) = ⊤ :=
    (helperForCorollary33_2_2_concave_off_both_domains_iff_negated_convex_obstruction
      (F := F) (u := u) (xStar := xStar)).mp hOutside
  have hPairBot :
      convexBifunctionPairing (fun u' x => -F u' x) u (-xStar) = ⊥ :=
    helperForCorollary33_2_2_convex_pairing_eq_bot_of_off_parameterDomain
      (G := fun u' x => -F u' x) (u := u) hObstruction.1 (-xStar)
  have hPairTop :
      convexBifunctionPairing (fun u' x => -F u' x) u (-xStar) = ⊤ :=
    hObstruction.2 u
  -- Step 1: specializing the universal-`⊤` clause at the same off-domain parameter contradicts
  -- the constant-`⊥` pairing value forced above.
  have hAbsurd : (⊤ : EReal) = ⊥ := by
    rw [← hPairTop, hPairBot]
  exact top_ne_bot hAbsurd

/-- Helper for Corollary33.2.2: for the current Section 33 concave adjoint pairing, the
textbook opposite-infinities disjunction is incompatible with the already-proved global
pairing identity. -/
lemma helperForCorollary33_2_2_concave_exceptional_disjunction_impossible
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConcaveBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ}
    (hExceptional :
      (concaveBifunctionPairing F u xStar = ⊤ ∧
          concaveBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
        (concaveBifunctionPairing F u xStar = ⊥ ∧
          concaveBifunctionCanonicalAdjointPairing F xStar u = ⊤)) :
    False := by
  -- Step 1: the new concave helper identifies the two present pairing objects everywhere.
  have hEq :
      concaveBifunctionPairing F u xStar =
        concaveBifunctionCanonicalAdjointPairing F xStar u :=
    helperForCorollary33_2_2_concave_pairing_eq_everywhere
      (F := F) hF u xStar
  -- Step 2: each exceptional alternative would again force `⊤ = ⊥`.
  rcases hExceptional with hTopBot | hBotTop
  · rcases hTopBot with ⟨hLeft, hRight⟩
    have hAbsurd : (⊤ : EReal) = ⊥ := by
      rw [← hLeft, ← hRight]
      exact hEq
    exact top_ne_bot hAbsurd
  · rcases hBotTop with ⟨hLeft, hRight⟩
    have hAbsurd : (⊥ : EReal) = ⊤ := by
      rw [← hLeft, ← hRight]
      exact hEq
    exact top_ne_bot hAbsurd.symm

/-- Helper for Corollary33.2.2: the concave exceptional conclusion appearing in the current
header is false at every point, because the two displayed closure-side pairing objects are
already equal everywhere. -/
lemma helperForCorollary33_2_2_concave_exceptional_conclusion_false
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConcaveBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ} :
    ¬ ((concaveBifunctionPairing F u xStar = ⊤ ∧
            concaveBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
          (concaveBifunctionPairing F u xStar = ⊥ ∧
            concaveBifunctionCanonicalAdjointPairing F xStar u = ⊤)) := by
  -- Step 1: reduce the displayed exceptional conclusion to the contradiction helper above.
  intro hExceptional
  exact
    helperForCorollary33_2_2_concave_exceptional_disjunction_impossible
      (F := F) hF hExceptional

/-- Helper for Corollary33.2.2: at a point lying outside both displayed concave domains, the
current exceptional implication is impossible because its conclusion contradicts the
already-proved global pairing identity. -/
lemma helperForCorollary33_2_2_concave_exceptional_implication_false_at_off_both_domains
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConcaveBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ}
    (hOutside :
      u ∉ concaveBifunctionParameterDomain F ∧
        xStar ∉ concaveBifunctionAdjointDomain F) :
    ¬ ((u ∉ concaveBifunctionParameterDomain F ∧
          xStar ∉ concaveBifunctionAdjointDomain F) →
        (concaveBifunctionPairing F u xStar = ⊤ ∧
            concaveBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
          (concaveBifunctionPairing F u xStar = ⊥ ∧
            concaveBifunctionCanonicalAdjointPairing F xStar u = ⊤)) := by
  -- Step 1: assume the displayed exceptional implication at the current off-domain point.
  intro hClause
  -- Step 2: specialize it and invoke the contradiction helper for the present concave pairing.
  exact
    helperForCorollary33_2_2_concave_exceptional_disjunction_impossible
      (F := F) hF (u := u) (xStar := xStar) (hClause hOutside)

/-- Helper for Corollary33.2.2: at an off-both-domains convex point, the full local
conclusion of the current theorem branch is inconsistent because its exceptional implication
is already false for the closure-side adjoint pairing used in this file. -/
lemma helperForCorollary33_2_2_convex_target_branch_false_at_off_both_domains
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConvexBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ}
    (hOutside :
      u ∉ convexBifunctionParameterDomain F ∧
        xStar ∉ convexBifunctionAdjointDomain F) :
    ¬ ((¬ (u ∉ convexBifunctionParameterDomain F ∧
              xStar ∉ convexBifunctionAdjointDomain F) →
            convexBifunctionPairing F u xStar =
              convexBifunctionCanonicalAdjointPairing F xStar u) ∧
          ((u ∉ convexBifunctionParameterDomain F ∧
                xStar ∉ convexBifunctionAdjointDomain F) →
            (convexBifunctionPairing F u xStar = ⊤ ∧
                convexBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
              (convexBifunctionPairing F u xStar = ⊥ ∧
                convexBifunctionCanonicalAdjointPairing F xStar u = ⊤))) := by
  intro hTarget
  -- Step 1: only the exceptional implication matters at the current off-domain point.
  exact
    helperForCorollary33_2_2_convex_exceptional_implication_false_at_off_both_domains
      (F := F) hF hOutside hTarget.2

/-- Helper for Corollary33.2.2: at an off-both-domains concave point, the full local
conclusion of the current theorem branch is inconsistent because its exceptional implication
is already false for the closure-side adjoint pairing used in this file. -/
lemma helperForCorollary33_2_2_concave_target_branch_false_at_off_both_domains
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConcaveBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ}
    (hOutside :
      u ∉ concaveBifunctionParameterDomain F ∧
        xStar ∉ concaveBifunctionAdjointDomain F) :
    ¬ ((¬ (u ∉ concaveBifunctionParameterDomain F ∧
              xStar ∉ concaveBifunctionAdjointDomain F) →
            concaveBifunctionPairing F u xStar =
              concaveBifunctionCanonicalAdjointPairing F xStar u) ∧
          ((u ∉ concaveBifunctionParameterDomain F ∧
                xStar ∉ concaveBifunctionAdjointDomain F) →
            (concaveBifunctionPairing F u xStar = ⊤ ∧
                concaveBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
              (concaveBifunctionPairing F u xStar = ⊥ ∧
                concaveBifunctionCanonicalAdjointPairing F xStar u = ⊤))) := by
  intro hTarget
  -- Step 1: again, the exceptional implication already contradicts the global pairing
  -- identity at this off-domain point.
  exact
    helperForCorollary33_2_2_concave_exceptional_implication_false_at_off_both_domains
      (F := F) hF hOutside hTarget.2

/-- Helper for Corollary33.2.2: if the current convex target branch were valid at a point,
that point could not lie outside both displayed convex domains, because the off-both-domains
case already contradicts the closure-side pairing objects frozen into the theorem header. -/
lemma helperForCorollary33_2_2_convex_target_branch_forces_not_off_both_domains
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConvexBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ}
    (hTarget :
      (¬ (u ∉ convexBifunctionParameterDomain F ∧
            xStar ∉ convexBifunctionAdjointDomain F) →
          convexBifunctionPairing F u xStar =
            convexBifunctionCanonicalAdjointPairing F xStar u) ∧
        ((u ∉ convexBifunctionParameterDomain F ∧
              xStar ∉ convexBifunctionAdjointDomain F) →
          (convexBifunctionPairing F u xStar = ⊤ ∧
              convexBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
            (convexBifunctionPairing F u xStar = ⊥ ∧
              convexBifunctionCanonicalAdjointPairing F xStar u = ⊤))) :
    ¬ (u ∉ convexBifunctionParameterDomain F ∧
        xStar ∉ convexBifunctionAdjointDomain F) := by
  -- Step 1: an off-both-domains point would trigger the already-proved branch contradiction.
  intro hOutside
  exact
    helperForCorollary33_2_2_convex_target_branch_false_at_off_both_domains
      (F := F) hF hOutside hTarget

/-- Helper for Corollary33.2.2: if the current concave target branch were valid at a point,
that point could not lie outside both displayed concave domains, because the off-both-domains
case already contradicts the closure-side pairing objects frozen into the theorem header. -/
lemma helperForCorollary33_2_2_concave_target_branch_forces_not_off_both_domains
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConcaveBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ}
    (hTarget :
      (¬ (u ∉ concaveBifunctionParameterDomain F ∧
            xStar ∉ concaveBifunctionAdjointDomain F) →
          concaveBifunctionPairing F u xStar =
            concaveBifunctionCanonicalAdjointPairing F xStar u) ∧
        ((u ∉ concaveBifunctionParameterDomain F ∧
              xStar ∉ concaveBifunctionAdjointDomain F) →
          (concaveBifunctionPairing F u xStar = ⊤ ∧
              concaveBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
            (concaveBifunctionPairing F u xStar = ⊥ ∧
              concaveBifunctionCanonicalAdjointPairing F xStar u = ⊤))) :
    ¬ (u ∉ concaveBifunctionParameterDomain F ∧
        xStar ∉ concaveBifunctionAdjointDomain F) := by
  -- Step 1: the concave branch has the same off-both-domains contradiction mechanism.
  intro hOutside
  exact
    helperForCorollary33_2_2_concave_target_branch_false_at_off_both_domains
      (F := F) hF hOutside hTarget

/-- Helper for Corollary33.2.2: in the current concave Section 33 interface, the full local
target branch is equivalent to ruling out off-both-domains points. The forward direction is
the contradiction helper above, while the reverse direction is immediate because the pairing
identity already holds globally and the exceptional implication is then vacuous. -/
lemma helperForCorollary33_2_2_concave_target_branch_iff_not_off_both_domains
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConcaveBifunction F)
    {u : Fin m → ℝ} {xStar : Fin n → ℝ} :
    ((¬ (u ∉ concaveBifunctionParameterDomain F ∧
            xStar ∉ concaveBifunctionAdjointDomain F) →
          concaveBifunctionPairing F u xStar =
            concaveBifunctionCanonicalAdjointPairing F xStar u) ∧
        ((u ∉ concaveBifunctionParameterDomain F ∧
              xStar ∉ concaveBifunctionAdjointDomain F) →
          (concaveBifunctionPairing F u xStar = ⊤ ∧
              concaveBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
            (concaveBifunctionPairing F u xStar = ⊥ ∧
              concaveBifunctionCanonicalAdjointPairing F xStar u = ⊤))) ↔
      ¬ (u ∉ concaveBifunctionParameterDomain F ∧
          xStar ∉ concaveBifunctionAdjointDomain F) := by
  constructor
  · intro hTarget
    -- Step 1: any proof of the current local target branch already excludes the off-domain
    -- configuration, because that configuration contradicts the frozen closure-side objects.
    exact
      helperForCorollary33_2_2_concave_target_branch_forces_not_off_both_domains
        (F := F) hF hTarget
  · intro hNotOutside
    refine ⟨?_, ?_⟩
    · intro _hNonExceptional
      -- Step 2: the displayed pairing equality is already global in the present concave
      -- closure-side interface, so the nonexceptional hypothesis is unused.
      exact
        helperForCorollary33_2_2_concave_pairing_eq_everywhere
          (F := F) hF u xStar
    · intro hOutside
      -- Step 3: once the off-both-domains case is excluded, the exceptional implication is
      -- vacuous.
      exact False.elim (hNotOutside hOutside)

-- Proof sketch: combine Theorem33.2 and Corollary33.2.1 with the fact that for proper
-- polyhedral convex or concave functions the relative interior of the effective domain
-- coincides with the effective domain itself. This upgrades the relative-interior pairing
-- identity to all points except the case where both variables lie outside their respective
-- domains; in that exceptional case, proper conjugacy forces one pairing to be `⊤` and the
-- other to be `⊥`.
/-- Corollary33.2.2: Let `F` be a proper polyhedral convex or concave bifunction. Then
`⟪F u, x^*⟫ = ⟪u, F^* x^*⟫` holds except when both `u ∉ dom F` and `x^* ∉ dom F^*`.
On the convex side, `dom F` is modeled by `convexBifunctionParameterDomain F` and
`dom F^*` by `convexBifunctionAdjointDomain F`; on the concave side, these are modeled by
`concaveBifunctionParameterDomain F` and `concaveBifunctionAdjointDomain F`. In the
exceptional case, one of the two pairings is `⊤` and the other is `⊥`. -/
theorem properPolyhedralBifunction_pairing_eq_except_off_both_domains
    {m n : ℕ} :
    (∀ {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
      IsProperPolyhedralConvexBifunction F →
        ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
          (¬ (u ∉ convexBifunctionParameterDomain F ∧
                xStar ∉ convexBifunctionAdjointDomain F) →
            convexBifunctionPairing F u xStar =
              convexBifunctionCanonicalAdjointPairing F xStar u) ∧
          ((u ∉ convexBifunctionParameterDomain F ∧
                xStar ∉ convexBifunctionAdjointDomain F) →
            (convexBifunctionPairing F u xStar = ⊤ ∧
                convexBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
              (convexBifunctionPairing F u xStar = ⊥ ∧
                convexBifunctionCanonicalAdjointPairing F xStar u = ⊤))) ∧
      (∀ {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsProperPolyhedralConcaveBifunction F →
          ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
            (¬ (u ∉ concaveBifunctionParameterDomain F ∧
                  xStar ∉ concaveBifunctionAdjointDomain F) →
              concaveBifunctionPairing F u xStar =
                concaveBifunctionCanonicalAdjointPairing F xStar u) ∧
            ((u ∉ concaveBifunctionParameterDomain F ∧
                  xStar ∉ concaveBifunctionAdjointDomain F) →
              (concaveBifunctionPairing F u xStar = ⊤ ∧
                  concaveBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
              (concaveBifunctionPairing F u xStar = ⊥ ∧
                  concaveBifunctionCanonicalAdjointPairing F xStar u = ⊤))) := by
  -- Route correction: after the Section 33 refactor, `convexBifunctionCanonicalAdjointPairing` is the
  -- closure-side pairing object, not the genuine adjoint-side pairing used by the textbook's
  -- opposite-infinities exceptional case. The helper above already forces global equality on
  -- the convex branch, so the current displayed exceptional clause is incompatible with that
  -- refactored object and needs a statement-level repair.
  constructor
  · intro F hF u xStar
    refine ⟨?_, ?_⟩
    · intro _hNonExceptional
      -- Step 1: the proper polyhedral convex helper already upgrades Theorem33.2 to a
      -- global equality for the closure-side pairing object appearing in this statement.
      exact
        helperForCorollary33_2_2_convex_pairing_eq_everywhere
          (F := F) hF u xStar
    · intro hExceptional
      -- Step 2: the current convex exceptional hypothesis is itself impossible, because the
      -- present adjoint domain is already all of `ℝ^n`.
      exact False.elim <|
        helperForCorollary33_2_2_convex_off_both_domains_impossible
          (F := F) hF hExceptional
  · intro F hF u xStar
    -- Step 1: under the frozen closure-side interface, the entire local concave branch is
    -- equivalent to ruling out off-both-domains points.
    have hTargetIff :
        ((¬ (u ∉ concaveBifunctionParameterDomain F ∧
                xStar ∉ concaveBifunctionAdjointDomain F) →
              concaveBifunctionPairing F u xStar =
                concaveBifunctionCanonicalAdjointPairing F xStar u) ∧
            ((u ∉ concaveBifunctionParameterDomain F ∧
                  xStar ∉ concaveBifunctionAdjointDomain F) →
              (concaveBifunctionPairing F u xStar = ⊤ ∧
                  concaveBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
                (concaveBifunctionPairing F u xStar = ⊥ ∧
                  concaveBifunctionCanonicalAdjointPairing F xStar u = ⊤))) ↔
          ¬ (u ∉ concaveBifunctionParameterDomain F ∧
              xStar ∉ concaveBifunctionAdjointDomain F) :=
      helperForCorollary33_2_2_concave_target_branch_iff_not_off_both_domains
        (F := F) hF
    have hNotOutside :
        ¬ (u ∉ concaveBifunctionParameterDomain F ∧
            xStar ∉ concaveBifunctionAdjointDomain F) :=
      helperForCorollary33_2_2_concave_off_both_domains_impossible
        (F := F) (u := u) (xStar := xStar)
    -- Step 3: rebuild the whole local branch from the isolated nonexceptionality statement.
    exact hTargetIff.mpr hNotOutside
-/

/-- A polyhedral convex function agrees with its canonical closure at every point of its
effective domain.  In the improper case lower semicontinuity forces each non-`⊤` value to be
`⊥`, exactly matching the canonical improper closure. -/
lemma helperForCorollary33_2_2_convexClosure_eq_self_at_effectivePoint
    {k : ℕ} {f : (Fin k → ℝ) → EReal}
    (hpoly : IsPolyhedralConvexFunction k f)
    {x : Fin k → ℝ} (hx : f x < ⊤) :
    convexFunctionClosure f x = f x := by
  have hclosed : ClosedConvexFunction f :=
    helperForCorollary33_2_2_polyhedralConvexFunction_isClosed hpoly
  by_cases hproper : ProperConvexFunctionOn (Set.univ : Set (Fin k → ℝ)) f
  · have hNoBot : ∀ y, f y ≠ (⊥ : EReal) := by
      intro y
      exact hproper.2.2 y (by simp)
    exact congrFun (convexFunctionClosure_eq_of_closedConvexFunction hclosed hNoBot) x
  · have himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin k → ℝ)) f :=
      ⟨hpoly.1, hproper⟩
    have htopOrBot :=
      lowerSemicontinuous_improperConvexFunction_no_finite_values himproper hclosed.2 x
    have hbot : f x = (⊥ : EReal) :=
      htopOrBot.resolve_left (lt_top_iff_ne_top.1 hx)
    have hclbot : convexFunctionClosure f = fun _ => (⊥ : EReal) :=
      convexFunctionClosure_eq_bot_of_exists_bot ⟨x, hbot⟩
    rw [congrFun hclbot x, hbot]

/-- Proper polyhedral concave bifunctions have no `⊤` values. -/
lemma helperForCorollary33_2_2_concave_hasNoTopValues
    {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConcaveBifunction F) :
    HasNoTopValuesBifunction F := by
  rcases hF with ⟨_hRock, _hPoly, hProper⟩
  intro u x
  have hNotBot :
      (fun z => -graphFunctionOfBifunction F z) (Fin.append u x) ≠ (⊥ : EReal) :=
    hProper.2.2 (Fin.append u x) (by simp)
  simpa [graphFunctionOfBifunction, Fin.append, EReal.neg_eq_bot_iff] using hNotBot

/-- Outside the convex parameter domain the entire primal section is `⊤`. -/
lemma helperForCorollary33_2_2_allTop_of_off_convexParameterDomain
    {m n : ℕ} {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} (hOutside : u ∉ convexBifunctionParameterDomain G) :
    ∀ x : Fin n → ℝ, G u x = ⊤ := by
  intro x
  by_contra hNotTop
  exact hOutside ⟨x, hNotTop⟩

/-- A constantly-`⊤` primal section has constantly-`⊥` convex pairing. -/
lemma helperForCorollary33_2_2_convex_pairing_eq_bot_of_off_parameterDomain
    {m n : ℕ} {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} (hOutside : u ∉ convexBifunctionParameterDomain G) :
    ∀ xStar : Fin n → ℝ, convexBifunctionPairing G u xStar = ⊥ := by
  have hAllTop := helperForCorollary33_2_2_allTop_of_off_convexParameterDomain
    (G := G) hOutside
  intro xStar
  rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
  simp [hAllTop]

/-- The negative convex-pairing section of a proper polyhedral convex bifunction is
polyhedral convex. -/
lemma helperForCorollary33_2_2_negConvexPairingSection_polyhedral
    {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConvexBifunction F) (xStar : Fin n → ℝ) :
    IsPolyhedralConvexFunction m
      (fun u => -convexBifunctionPairing F u xStar) := by
  exact (polyhedralConvexBifunction_pairing_sections_and_reconstruction
    (m := m) (n := n) (F := F) hF.1).2.1 xStar

/-- The concave-pairing section of a proper polyhedral concave bifunction is polyhedral
convex. -/
lemma helperForCorollary33_2_2_concavePairingSection_polyhedral
    {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsProperPolyhedralConcaveBifunction F) (xStar : Fin n → ℝ) :
    IsPolyhedralConvexFunction m
      (fun u => concaveBifunctionPairing F u xStar) := by
  rcases hF with ⟨hRock, hPolyNegGraph, hProperNegGraph⟩
  let G : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => -F u x
  have hGraphG : IsGraphConvexBifunction G := by
    have hConvOn : ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
        (graphFunctionOfBifunction G) := by
      simpa [G, graphFunctionOfBifunction] using hPolyNegGraph.1
    have hNoBot : ∀ z, graphFunctionOfBifunction G z ≠ (⊥ : EReal) := by
      intro z
      simpa [G, graphFunctionOfBifunction] using hProperNegGraph.2.2 z (by simp)
    have hJensen := (convexFunctionOn_univ_iff_jensen_inequality
      (f := graphFunctionOfBifunction G) hNoBot).1 hConvOn
    intro z₁ z₂ _ _ a b ha hb hab _
    let w : Fin 2 → ℝ := fun i => if i = 0 then a else b
    let z : Fin 2 → (Fin (m + n) → ℝ) := fun i => if i = 0 then z₁ else z₂
    have hw : ∀ i, 0 ≤ w i := by intro i; fin_cases i <;> simp [w, ha, hb]
    have hsum : Finset.univ.sum (fun i => w i) = 1 := by
      simp [w, Fin.sum_univ_two, hab]
    simpa [w, z, Fin.sum_univ_two] using hJensen 2 w z hw hsum
  have hRockG := helperForLemma33_0_22_graphConvex_gives_rockafellarConvex
    (F := G) hGraphG
  have hPolyG : IsPolyhedralConvexFunction (m + n) (graphFunctionOfBifunction G) := by
    simpa [G, graphFunctionOfBifunction] using hPolyNegGraph
  have hSection := (polyhedralConvexBifunction_pairing_sections_and_reconstruction
    (m := m) (n := n) (F := G) ⟨hRockG, hPolyG⟩).2.1 (-xStar)
  have hEq : (fun u => concaveBifunctionPairing F u xStar) =
      fun u => -convexBifunctionPairing G u (-xStar) := by
    funext u
    simpa [G] using helperForCorollary33_2_1_concavePairing_eq_neg_convexPairing_of_neg
      (F := F) u xStar
  simpa [hEq] using hSection

-- Proof sketch: use the first identity of Theorem 33.2.  Polyhedrality makes the relevant
-- one-variable section lower semicontinuous.  At a parameter-domain point its canonical
-- closure agrees pointwise; at an adjoint-domain point the section is proper, so it agrees
-- everywhere.  If both points are outside their domains, the defining conjugates collapse to
-- opposite infinities.
/-- Corollary33.2.2: Let `F` be a proper polyhedral convex or concave bifunction. Then
`\u27e6F u, x^*\u27e7 = \u27e6u, F^* x^*\u27e7` unless both variables lie outside their respective
domains; at such a point the two pairings take opposite infinite values. -/
theorem properPolyhedralBifunction_pairing_eq_except_off_both_domains
    {m n : ℕ} :
    (∀ {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
      IsProperPolyhedralConvexBifunction F →
        ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
          (¬ (u ∉ convexBifunctionParameterDomain F ∧
                xStar ∉ convexBifunctionAdjointDomain F) →
            convexBifunctionPairing F u xStar =
              convexBifunctionCanonicalAdjointPairing F xStar u) ∧
          ((u ∉ convexBifunctionParameterDomain F ∧
                xStar ∉ convexBifunctionAdjointDomain F) →
            (convexBifunctionPairing F u xStar = ⊤ ∧
                convexBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
              (convexBifunctionPairing F u xStar = ⊥ ∧
                convexBifunctionCanonicalAdjointPairing F xStar u = ⊤))) ∧
      (∀ {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsProperPolyhedralConcaveBifunction F →
          ∀ u : Fin m → ℝ, ∀ xStar : Fin n → ℝ,
            (¬ (u ∉ concaveBifunctionParameterDomain F ∧
                  xStar ∉ concaveBifunctionAdjointDomain F) →
              concaveBifunctionPairing F u xStar =
                concaveBifunctionCanonicalAdjointPairing F xStar u) ∧
            ((u ∉ concaveBifunctionParameterDomain F ∧
                  xStar ∉ concaveBifunctionAdjointDomain F) →
              (concaveBifunctionPairing F u xStar = ⊤ ∧
                  concaveBifunctionCanonicalAdjointPairing F xStar u = ⊥) ∨
                (concaveBifunctionPairing F u xStar = ⊥ ∧
                  concaveBifunctionCanonicalAdjointPairing F xStar u = ⊤))) := by
  classical
  constructor
  · intro F hF u xStar
    rcases helperForCorollary33_2_2_convex_graphClosed_and_noBot
        (F := F) hF with ⟨hGraph, _hGraphClosed, hNoBot⟩
    let q : (Fin m → ℝ) → EReal :=
      fun v => -convexBifunctionPairing F v xStar
    have hqPoly : IsPolyhedralConvexFunction m q := by
      simpa [q] using
        helperForCorollary33_2_2_negConvexPairingSection_polyhedral
          (F := F) hF xStar
    have hFirst :=
      (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).1 F
        ⟨hGraph, hNoBot⟩ |>.1
    refine ⟨?_, ?_⟩
    · intro hNotBoth
      have hClosureAt : convexFunctionClosure q u = q u := by
        by_cases hu : u ∈ convexBifunctionParameterDomain F
        · rcases hu with ⟨x, hx⟩
          have hPairNeBot : convexBifunctionPairing F u xStar ≠ (⊥ : EReal) := by
            simpa [convexBifunctionPairing, bifunctionPairingNotation, convexConjugate] using
              helperForTheorem33_1_convexConjugate_ne_bot_of_point
                (f := F u) (x₀ := x) hx xStar
          apply helperForCorollary33_2_2_convexClosure_eq_self_at_effectivePoint hqPoly
          exact lt_top_iff_ne_top.2 (by simpa [q] using hPairNeBot)
        · have hxDom : xStar ∈ convexBifunctionAdjointDomain F := by
            by_contra hx
            exact hNotBoth ⟨hu, hx⟩
          have hqNoBot : ∀ v, q v ≠ (⊥ : EReal) := by
            intro v hv
            rcases hxDom with ⟨uStar, huStar⟩
            apply huStar
            have hConjTop : convexConjugate q (-uStar) = (⊤ : EReal) := by
              rw [convexConjugate, fenchelConjugate_eq_iSup]
              apply top_unique
              have hle := le_iSup (fun w : Fin m → ℝ =>
                (((w ⬝ᵥ (-uStar) : ℝ) : EReal)) - q w) v
              simpa [hv] using hle
            calc
              convexBifunctionAdjointPairing F xStar uStar =
                  -convexConjugate q (-uStar) := by
                    simpa [q, convexBifunctionAdjointPairing,
                      convexBifunctionAdjoint, convexConjugate] using
                      helperForTheorem_6_30_3_concaveConjugate_eq_neg_fenchelConjugate_neg_unrestricted
                        (g := fun w => convexBifunctionPairing F w xStar) uStar
              _ = ⊥ := by simp [hConjTop]
          exact congrFun
            (convexFunctionClosure_eq_of_closedConvexFunction
              (helperForCorollary33_2_2_polyhedralConvexFunction_isClosed hqPoly) hqNoBot) u
      calc
        convexBifunctionPairing F u xStar = -q u := by simp [q]
        _ = -convexFunctionClosure q u := by rw [hClosureAt]
        _ = concaveClosure (fun v => convexBifunctionPairing F v xStar) u := by rfl
        _ = convexBifunctionCanonicalAdjointPairing F xStar u := (hFirst xStar u).symm
    · rintro ⟨hu, hx⟩
      have hPairBot := helperForCorollary33_2_2_convex_pairing_eq_bot_of_off_parameterDomain
        (G := F) hu xStar
      have hAllBot : ∀ uStar, convexBifunctionAdjointPairing F xStar uStar = (⊥ : EReal) := by
        intro uStar
        by_contra hne
        exact hx ⟨uStar, hne⟩
      right
      refine ⟨hPairBot, ?_⟩
      rw [convexBifunctionCanonicalAdjointPairing,
        helperForTheorem_6_30_4_concaveConjugate_eq_iInf]
      simp [hAllBot]
  · intro F hF u xStar
    have hNoTop := helperForCorollary33_2_2_concave_hasNoTopValues (F := F) hF
    let r : (Fin m → ℝ) → EReal :=
      fun v => concaveBifunctionPairing F v xStar
    have hrPoly : IsPolyhedralConvexFunction m r := by
      simpa [r] using
        helperForCorollary33_2_2_concavePairingSection_polyhedral
          (F := F) hF xStar
    let G : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun v x => -F v x
    have hGraphG : IsGraphConvexBifunction G := by
      have hConvOn : ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
          (graphFunctionOfBifunction G) := by
        simpa [G, graphFunctionOfBifunction] using hF.2.1.1
      have hNoBotG : ∀ z, graphFunctionOfBifunction G z ≠ (⊥ : EReal) := by
        intro z
        simpa [G, graphFunctionOfBifunction] using hF.2.2.2.2 z (by simp)
      have hJensen := (convexFunctionOn_univ_iff_jensen_inequality
        (f := graphFunctionOfBifunction G) hNoBotG).1 hConvOn
      intro z₁ z₂ _ _ a b ha hb hab _
      let w : Fin 2 → ℝ := fun i => if i = 0 then a else b
      let z : Fin 2 → (Fin (m + n) → ℝ) := fun i => if i = 0 then z₁ else z₂
      have hw : ∀ i, 0 ≤ w i := by intro i; fin_cases i <;> simp [w, ha, hb]
      have hsum : Finset.univ.sum (fun i => w i) = 1 := by simp [w, Fin.sum_univ_two, hab]
      simpa [w, z, Fin.sum_univ_two] using hJensen 2 w z hw hsum
    have hGraph : IsGraphConcaveBifunction F := by
      have hNeg := helperForLemma33_0_5_convexNegation_isConcave hGraphG
      simpa [IsGraphConcaveBifunction, G, graphFunctionOfBifunction] using hNeg
    have hFirst :=
      (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).2 F
        ⟨hGraph, hNoTop⟩ |>.1
    refine ⟨?_, ?_⟩
    · intro hNotBoth
      have hClosureAt : convexFunctionClosure r u = r u := by
        by_cases hu : u ∈ concaveBifunctionParameterDomain F
        · rcases hu with ⟨x, hx⟩
          have hConvNeBot :
              convexBifunctionPairing G u (-xStar) ≠ (⊥ : EReal) := by
            simpa [convexBifunctionPairing, bifunctionPairingNotation, convexConjugate, G] using
              helperForTheorem33_1_convexConjugate_ne_bot_of_point
                (f := G u) (x₀ := x) (by simpa [G] using hx) (-xStar)
          have hrNeTop : r u ≠ (⊤ : EReal) := by
            intro hrTop
            apply hConvNeBot
            have hPoint :=
              helperForCorollary33_2_1_concavePairing_eq_neg_convexPairing_of_neg
                (F := F) u xStar
            have hNegTop :
                -convexBifunctionPairing G u (-xStar) = (⊤ : EReal) := by
              simpa [r, G] using hPoint.symm.trans hrTop
            have := congrArg Neg.neg hNegTop
            simpa using this
          exact helperForCorollary33_2_2_convexClosure_eq_self_at_effectivePoint
            hrPoly (lt_top_iff_ne_top.2 hrNeTop)
        · have hxDom : xStar ∈ concaveBifunctionAdjointDomain F := by
            by_contra hx
            exact hNotBoth ⟨hu, hx⟩
          have hrNoBot : ∀ v, r v ≠ (⊥ : EReal) := by
            intro v hv
            rcases hxDom with ⟨uStar, huStar⟩
            apply huStar
            rw [concaveBifunctionAdjointPairing, convexConjugate, fenchelConjugate_eq_iSup]
            apply top_unique
            have hle := le_iSup (fun w : Fin m → ℝ =>
              (((w ⬝ᵥ uStar : ℝ) : EReal)) - r w) v
            simpa [r, hv] using hle
          exact congrFun
            (convexFunctionClosure_eq_of_closedConvexFunction
              (helperForCorollary33_2_2_polyhedralConvexFunction_isClosed hrPoly) hrNoBot) u
      calc
        concaveBifunctionPairing F u xStar = r u := rfl
        _ = convexFunctionClosure r u := hClosureAt.symm
        _ = concaveBifunctionCanonicalAdjointPairing F xStar u := (hFirst xStar u).symm
    · rintro ⟨hu, hx⟩
      have hAllBot : ∀ x, F u x = (⊥ : EReal) := by
        intro x
        by_contra hne
        exact hu ⟨x, hne⟩
      have hPairTop : concaveBifunctionPairing F u xStar = (⊤ : EReal) := by
        simp [concaveBifunctionPairing, bifunctionPairingNotation,
          conjugatePairingNotation, hAllBot]
      have hAllTop : ∀ uStar, concaveBifunctionAdjointPairing F xStar uStar = (⊤ : EReal) := by
        intro uStar
        by_contra hne
        exact hx ⟨uStar, hne⟩
      left
      refine ⟨hPairTop, ?_⟩
      rw [concaveBifunctionCanonicalAdjointPairing, convexConjugate, fenchelConjugate_eq_iSup]
      simp [hAllTop]

-- Theorems 33.24 and beyond are blocked on Theorem 30.1 and are intentionally deferred.
end Section33
end Chap07
