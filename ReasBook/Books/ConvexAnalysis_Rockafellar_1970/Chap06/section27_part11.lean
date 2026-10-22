/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section27_part10

section Chap06
section Section27

/-- Helper for Corollary 6.27.3: the remaining one-dimensional bridge for the unbounded scalar
slice cases `Ici`, `Iic`, and `univ`. This is the only unresolved step after handling the trivial
and bounded slice cases. -/
lemma helperForCorollary_6_27_3_unboundedScalarSlice_attainment
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (haffine : EveryRecessionDirectionIsAffineAlongRay h)
    (C : Set (Fin n → ℝ)) (hbounded : HasRealLowerBoundOn h C)
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (hgClosed : ClosedConvexFunction g)
    (x y : Fin n → ℝ) (hy : y ≠ 0)
    (hFinite : ∃ s : ℝ, x + s • y ∈ C ∧ h (x + s • y) < (⊤ : EReal))
    (hSlice :
      let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
      T = Set.Ici (sInf T) ∨ T = Set.Iic (sSup T) ∨ T = Set.univ) :
    ∃ t : ℝ, g (x + t • y) = ⨅ s : ℝ, g (x + s • y) := by
  rcases hFinite with ⟨s0, hs0C, hs0Top⟩
  rcases hSlice with hIci | hIic | hUniv
  · by_cases hyRec : IsRecessionDirection h y
    · -- When `y` is already a recession direction of `h`, the affine-on-rays hypothesis forces a
      -- zero slope, so the chosen feasible finite point minimizes the whole forward slice.
      have hForwardC : ∀ t : ℝ, 0 ≤ t → x + (s0 + t) • y ∈ C := by
        intro t ht
        let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
        have hIciT : T = Set.Ici (sInf T) := by
          simpa [T] using hIci
        have hs0T : s0 ∈ T := by
          simpa [T] using hs0C
        have hs0ge : sInf T ≤ s0 := by
          rw [hIciT] at hs0T
          exact hs0T
        have hsT : s0 + t ∈ T := by
          rw [hIciT]
          change sInf T ≤ s0 + t
          linarith
        simpa [T] using hsT
      exact
        helperForCorollary_6_27_3_lineMinimizer_of_forwardRecessionDirection
          (h := h) hproper haffine C hbounded hg x y hyRec hs0C hs0Top hForwardC
    · -- Route correction: the ambient non-recession branch is now isolated as its own 1D bridge.
      exact
        helperForCorollary_6_27_3_rightRayScalarSlice_attainment_of_not_recessionDirection
          (h := h) hclosed hproper haffine C hbounded hg hgClosed x y hy
          ⟨s0, hs0C, hs0Top⟩ hyRec hIci
  · by_cases hyRec : IsRecessionDirection h (-y)
    · -- The left-ray branch is symmetric after flipping the direction to `-y`.
      have hBackwardC : ∀ t : ℝ, 0 ≤ t → x + (s0 - t) • y ∈ C := by
        intro t ht
        let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
        have hIicT : T = Set.Iic (sSup T) := by
          simpa [T] using hIic
        have hs0T : s0 ∈ T := by
          simpa [T] using hs0C
        have hs0le : s0 ≤ sSup T := by
          rw [hIicT] at hs0T
          exact hs0T
        have hsT : s0 - t ∈ T := by
          rw [hIicT]
          change s0 - t ≤ sSup T
          linarith
        simpa [T] using hsT
      exact
        helperForCorollary_6_27_3_lineMinimizer_of_backwardRecessionDirection
          (h := h) hproper haffine C hbounded hg x y hyRec hs0C hs0Top hBackwardC
    · -- The ambient non-recession left-ray case is the second remaining 1D bridge.
      exact
        helperForCorollary_6_27_3_leftRayScalarSlice_attainment_of_not_recessionDirection
          (h := h) hclosed hproper haffine C hbounded hg hgClosed x y hy
          ⟨s0, hs0C, hs0Top⟩ hyRec hIic
  · by_cases hyRec : IsRecessionDirection h y
    · -- On the full line, a forward recession direction again forces a zero affine slope.
      have hForwardC : ∀ t : ℝ, 0 ≤ t → x + (s0 + t) • y ∈ C := by
        intro t _ht
        let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
        have hUnivT : T = Set.univ := by
          simpa [T] using hUniv
        have hsT : s0 + t ∈ T := by
          rw [hUnivT]
          simp
        simpa [T] using hsT
      exact
        helperForCorollary_6_27_3_lineMinimizer_of_forwardRecessionDirection
          (h := h) hproper haffine C hbounded hg x y hyRec hs0C hs0Top hForwardC
    · by_cases hyNegRec : IsRecessionDirection h (-y)
      · -- The symmetric full-line branch uses the backward ray from the same finite point.
        have hBackwardC : ∀ t : ℝ, 0 ≤ t → x + (s0 - t) • y ∈ C := by
          intro t _ht
          let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
          have hUnivT : T = Set.univ := by
            simpa [T] using hUniv
          have hsT : s0 - t ∈ T := by
            rw [hUnivT]
            simp
          simpa [T] using hsT
        exact
          helperForCorollary_6_27_3_lineMinimizer_of_backwardRecessionDirection
            (h := h) hproper haffine C hbounded hg x y hyNegRec hs0C hs0Top hBackwardC
      · -- What remains is the genuinely scalar full-line case with no ambient recession data.
        exact
          helperForCorollary_6_27_3_fullLineScalarSlice_attainment_of_no_recessionDirection
            (h := h) hclosed hproper haffine C hbounded hg hgClosed x y hy
            ⟨s0, hs0C, hs0Top⟩ hyRec hyNegRec hUniv

/-- Helper for Corollary 6.27.3: the indicator extension `g = h + δ_C` has linewise infimum
attainment once the trivial slice branch, the bounded interval branch, and the remaining
unbounded one-dimensional bridge are assembled. -/
lemma helperForCorollary_6_27_3_linewiseAttainment_indicatorExtension
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (haffine : EveryRecessionDirectionIsAffineAlongRay h)
    (C : Set (Fin n → ℝ))
    (hCpoly : IsPolyhedralConvexSet n C)
    (hbounded : HasRealLowerBoundOn h C)
    {g : (Fin n → ℝ) → EReal} (hg : g = fun z => h z + indicatorFunction C z)
    (hgClosed : ClosedConvexFunction g) :
    HasLinewiseInfimumAttainment g := by
  intro x y hy
  by_cases hFinite : ∃ s : ℝ, x + s • y ∈ C ∧ h (x + s • y) < (⊤ : EReal)
  · let T : Set ℝ := {s : ℝ | x + s • y ∈ C}
    have hTcases :
        IsClosed T ∧ Convex ℝ T ∧
          (T = ∅ ∨ T = Set.Icc (sInf T) (sSup T) ∨ T = Set.Ici (sInf T) ∨
            T = Set.Iic (sSup T) ∨ T = Set.univ) := by
      simpa [T] using
        helperForCorollary_6_27_3_scalarFeasibleSet_intervalCases (C := C) hCpoly x y
    rcases hTcases with ⟨_hTclosed, _hTconv, hTcases'⟩
    rcases hTcases' with hEmpty | hIcc | hIci | hIic | hUniv
    · -- A finite feasible point rules out the empty slice.
      exfalso
      rcases hFinite with ⟨s, hsC, _hsTop⟩
      have hsT : s ∈ T := by simpa [T] using hsC
      simpa [hEmpty] using hsT
    · -- The bounded slice is handled by compact minimization on the interval.
      exact
        helperForCorollary_6_27_3_boundedScalarSlice_attainment
          (h := h) hproper C hg hgClosed x y hIcc hFinite
    · -- The right-ray case is delegated to the dedicated one-dimensional bridge.
      exact
        helperForCorollary_6_27_3_unboundedScalarSlice_attainment
          (h := h) hclosed hproper haffine C hbounded hg hgClosed x y hy hFinite
          (by simpa [T] using (Or.inl hIci))
    · -- The left-ray case is the symmetric unbounded slice branch.
      exact
        helperForCorollary_6_27_3_unboundedScalarSlice_attainment
          (h := h) hclosed hproper haffine C hbounded hg hgClosed x y hy hFinite
          (by simpa [T] using (Or.inr (Or.inl hIic)))
    · -- The full-line case is the final unbounded branch.
      exact
        helperForCorollary_6_27_3_unboundedScalarSlice_attainment
          (h := h) hclosed hproper haffine C hbounded hg hgClosed x y hy hFinite
          (by simpa [T] using (Or.inr (Or.inr hUniv)))
  · -- If the line contains no feasible finite point, the line infimum is attained trivially.
    exact
      helperForCorollary_6_27_3_scalarSlice_allTop_attainment
        (h := h) hproper C hg x y hFinite

/- A direction is affine in Rockafellar's two-sided sense when every full line parallel to it
has one fixed slope.  The earlier forward-ray predicate is insufficient here: the book uses the
value at `-y` as well as the value at `y`. -/
def EveryRecessionDirectionIsAffine {n : ℕ} (h : (Fin n → ℝ) → EReal) : Prop :=
  ∀ y : Fin n → ℝ, IsRecessionDirection h y →
    ∃ a : ℝ, ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h, ∀ t : ℝ,
      h (x + t • y) = h x + ((t * a : ℝ) : EReal)

-- Proof sketch: for a common recession direction `y` of `h` and the polyhedral set `C`,
-- the affine-on-rays hypothesis gives a fixed slope along feasible rays in direction `y`.
-- Since `h` is bounded below on `C`, that slope cannot be negative; because `y` is also a
-- recession direction of `h`, it cannot be positive either, hence it is zero and `y` is a
-- direction of constancy. The polyhedral case of Theorem 6.27.4 then yields attainment.
/-- Corollary 6.27.3: let `h` be a closed proper convex function such that every direction of
recession of `h` is a direction in which `h` is affine. Then `h` attains its infimum relative to
any polyhedral convex set `C` on which it is bounded below. -/
theorem attainsInfimumOn_polyhedralConvexSet_of_recessionDirections_affine
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hclosed : ClosedConvexFunction h)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) h)
    (haffine : EveryRecessionDirectionIsAffine h)
    (C : Set (Fin n → ℝ)) (hCne : Set.Nonempty C)
    (hCpoly : IsPolyhedralConvexSet n C) (hbounded : HasRealLowerBoundOn h C) :
    AttainsInfimumOn h C := by
  classical
  by_cases hallTop : ∀ x : Fin n → ℝ, x ∈ C → h x = (⊤ : EReal)
  · -- If every feasible value is `⊤`, the restricted infimum is attained trivially.
    exact
      helperForTheorem_6_27_4_trivial_attainment_of_all_top_on_C
        (h := h) (C := C) hCne hallTop
  · -- A finite feasible anchor lets boundedness force every common affine slope to vanish.
    have hfinitePoint : ∃ x0 : Fin n → ℝ, x0 ∈ C ∧ h x0 < (⊤ : EReal) := by
      by_contra hNoFinite
      push_neg at hNoFinite
      apply hallTop
      intro x hxC
      by_contra hxneTop
      exact
        (not_le_of_gt (lt_top_iff_ne_top.mpr hxneTop))
          (hNoFinite x hxC)
    rcases hfinitePoint with ⟨x0, hx0C, hx0Top⟩
    have hcommon : CommonRecessionDirectionsAreDirectionsOfConstancy h C := by
      intro y hyRec hyC
      rcases haffine y hyRec with ⟨a, ha⟩
      have haForward :
          ∀ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h, ∀ t : ℝ, 0 ≤ t →
            h (x + t • y) = h x + ((t * a : ℝ) : EReal) := by
        intro x hx t _ht
        exact ha x hx t
      have haNonpos : a ≤ 0 :=
        helperForCorollary_6_27_3_affineSlope_nonpositive_of_recessionDirection
          (h := h) hproper hyRec hx0Top haForward
      have hRay : ∀ t : ℝ, 0 ≤ t → x0 + t • y ∈ C := by
        intro t ht
        exact hyC hx0C ht
      have haNonneg : 0 ≤ a :=
        helperForCorollary_6_27_3_affineSlope_nonnegative_on_pointedFeasibleRay
          (h := h) hproper C hRay hx0Top haForward hbounded
      have haZero : a = 0 := le_antisymm haNonpos haNonneg
      have hx0Dom : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h := by
        simpa [effectiveDomain_eq] using hx0Top
      have hrecZero (v : Fin n → ℝ) (hv : ∃ t : ℝ, v = t • y) :
          recessionFunction h v = 0 := by
        rcases hv with ⟨t, rfl⟩
        apply le_antisymm
        · unfold recessionFunction
          refine sSup_le ?_
          intro r hr
          rcases hr with ⟨x, hx, rfl⟩
          rw [ha x hx t, haZero]
          have hxTop : h x ≠ (⊤ : EReal) := by
            exact lt_top_iff_ne_top.mp (by simpa [effectiveDomain_eq] using hx)
          have hxBot : h x ≠ (⊥ : EReal) := hproper.2.2 x (by simp)
          simp [hxTop, hxBot]
        · unfold recessionFunction
          have hmember :
              (0 : EReal) ∈
                {r : EReal | ∃ x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) h,
                  r = h (x + t • y) - h x} := by
            refine ⟨x0, hx0Dom, ?_⟩
            rw [ha x0 hx0Dom t, haZero]
            have hx0Top' : h x0 ≠ (⊤ : EReal) := lt_top_iff_ne_top.mp hx0Top
            have hx0Bot : h x0 ≠ (⊥ : EReal) := hproper.2.2 x0 (by simp)
            simp [hx0Top', hx0Bot]
          exact le_sSup hmember
      refine ⟨hrecZero y ⟨1, by simp⟩, ?_⟩
      exact hrecZero (-y) ⟨-1, by simp⟩
    exact
      (attainsInfimumOn_closedConvexSet_of_commonRecessionHypotheses
        (h := h) (C := C) hclosed hproper hCne
        (helperForTheorem_19_1_polyhedral_isClosed (n := n) (C := C) hCpoly)
        (helperForTheorem_19_1_polyhedral_isConvex (n := n) (C := C) hCpoly)).2
        hCpoly hcommon

-- Proof sketch: polyhedral and finitely generated convex functions are equivalent notions in the
-- earlier development. Their recession behavior reduces to the affine-on-rays situation covered by
-- Corollary 6.27.3. Since `AttainsInfimumOn h C` is existential over points of `C`, the formal
-- conclusion is expressed as `Set.Nonempty C → AttainsInfimumOn h C`.
/-- Corollary 6.27.4: a polyhedral, equivalently finitely generated, convex function `h`
attains its infimum relative to any polyhedral convex set `C` on which it is bounded below.
In this formalization, the conclusion is stated as `Set.Nonempty C → AttainsInfimumOn h C`
because attainment is existential in `C`. -/
theorem attainsInfimumOn_polyhedralConvexSet_of_polyhedralOrFinitelyGeneratedConvexFunction
    {n : ℕ} (h : (Fin n → ℝ) → EReal)
    (hpoly_or_fg : IsPolyhedralConvexFunction n h ∨ IsFinitelyGeneratedConvexFunction n h)
    (C : Set (Fin n → ℝ))
    (hCpoly : IsPolyhedralConvexSet n C) (hbounded : HasRealLowerBoundOn h C) :
    Set.Nonempty C → AttainsInfimumOn h C := by
  classical
  intro hCne
  rcases hbounded with ⟨mLower, hmLower⟩
  have hpoly : IsPolyhedralConvexFunction n h := by
    rcases hpoly_or_fg with hpoly | hfg
    · exact hpoly
    · exact helperForCorollary_19_1_2_finitelyGenerated_imp_polyhedral hfg
  have hnotbotOnC : ∀ x : Fin n → ℝ, x ∈ C → h x ≠ (⊥ : EReal) := by
    intro x hxC
    intro hbot
    have hle : (mLower : EReal) ≤ h x := hmLower x hxC
    simpa [hbot] using hle
  by_cases hallTop : ∀ x : Fin n → ℝ, x ∈ C → h x = (⊤ : EReal)
  · -- If every feasible value is `⊤`, the constrained infimum is attained trivially.
    exact
      helperForTheorem_6_27_4_trivial_attainment_of_all_top_on_C
        (h := h) (C := C) hCne hallTop
  · -- Route correction: the direct recession-affine route on `h` is false in general for
    -- polyhedral convex functions, so we minimize the last coordinate on a lifted epigraph slice.
    have hfinitePoint : ∃ x0 : Fin n → ℝ, x0 ∈ C ∧ h x0 < (⊤ : EReal) := by
      by_contra hNoFinite
      push_neg at hNoFinite
      apply hallTop
      intro x hxC
      by_contra hxneTop
      exact
        (not_le_of_gt (lt_top_iff_ne_top.mpr hxneTop))
          (hNoFinite x hxC)
    rcases hfinitePoint with ⟨x0, hx0C, hx0Top⟩
    have hx0Bot : h x0 ≠ (⊥ : EReal) := hnotbotOnC x0 hx0C
    let proj : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      (LinearMap.fst ℝ (Fin n → ℝ) ℝ).comp
        ((prodLinearEquiv_append_coord (n := n)).symm.toLinearMap)
    let P : Set (Fin (n + 1) → ℝ) :=
      ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) h) ∩
        proj ⁻¹' C
    let ell : (Fin (n + 1) → ℝ) → EReal := fun z => (z (Fin.last n) : EReal)
    -- The lifted feasible points are exactly the feasible epigraph points with first coordinate
    -- in `C`, written in `Fin (n + 1)` coordinates.
    have hmemP_of_memC_of_le :
        ∀ {x : Fin n → ℝ} {μ : ℝ}, x ∈ C → h x ≤ (μ : EReal) →
          prodLinearEquiv_append_coord (n := n) (x, μ) ∈ P := by
      intro x μ hxC hxμ
      refine ⟨?_, ?_⟩
      · exact ⟨(x, μ), (mem_epigraph_univ_iff (f := h)).2 hxμ, rfl⟩
      · simpa [proj] using hxC
    -- Decoding a point of `P` back through `prodLinearEquiv_append_coord` recovers its epigraph
    -- and feasibility information.
    have hsymm_mem_epigraph_of_memP :
        ∀ {z : Fin (n + 1) → ℝ}, z ∈ P →
          (prodLinearEquiv_append_coord (n := n)).symm z ∈
            epigraph (Set.univ : Set (Fin n → ℝ)) h := by
      intro z hzP
      rcases hzP.1 with ⟨p, hp, rfl⟩
      simpa
    have hfst_memC_of_memP :
        ∀ {z : Fin (n + 1) → ℝ}, z ∈ P →
          ((prodLinearEquiv_append_coord (n := n)).symm z).1 ∈ C := by
      intro z hzP
      simpa [proj] using hzP.2
    have hTransformedEpigraphPoly :
        IsPolyhedralConvexSet (n + 1)
          ((fun p => prodLinearEquiv_append_coord (n := n) p) ''
            epigraph (Set.univ : Set (Fin n → ℝ)) h) := by
      simpa [prodLinearEquiv_append_coord] using hpoly.2
    have hProjPreimagePoly : IsPolyhedralConvexSet (n + 1) (proj ⁻¹' C) := by
      exact (polyhedralConvexSet_image_preimage_linear (n + 1) n proj).2 C hCpoly
    have hPpoly : IsPolyhedralConvexSet (n + 1) P := by
      exact helperForTheorem_19_1_polyhedral_inter hTransformedEpigraphPoly hProjPreimagePoly
    let μ0 : ℝ := (h x0).toReal
    have hμ0 : ((μ0 : ℝ) : EReal) = h x0 := by
      simpa [μ0] using EReal.coe_toReal (x := h x0) (lt_top_iff_ne_top.mp hx0Top) hx0Bot
    have hx0leμ0 : h x0 ≤ (μ0 : EReal) := by
      rw [hμ0]
    have hPne : Set.Nonempty P := by
      refine ⟨prodLinearEquiv_append_coord (n := n) (x0, μ0), ?_⟩
      exact hmemP_of_memC_of_le hx0C hx0leμ0
    let b : Fin 1 → Fin (n + 1) → ℝ :=
      fun _ j => if j = Fin.last n then 1 else 0
    let β : Fin 1 → ℝ := fun _ => 0
    -- The last-coordinate objective is a single affine functional, hence polyhedral.
    have hell_repr :
        ell =
          fun z =>
            ((sSup {r : ℝ |
                ∃ i : Fin 1, (i : ℕ) < 1 ∧ r = (∑ j, z j * b i j) - β i} : ℝ) : EReal) +
              indicatorFunction
                (C := {y | ∀ i : Fin 1, 1 ≤ (i : ℕ) →
                  (∑ j, y j * b i j) ≤ β i})
                z := by
      funext z
      simp [ell, b, β, indicatorFunction]
    have hEllPoly_nonbot :
        IsPolyhedralConvexFunction (n + 1) ell ∧
          (∀ z : Fin (n + 1) → ℝ, ell z ≠ (⊥ : EReal)) := by
      exact
        (polyhedral_convex_function_iff_max_affine_plus_indicator
          (n := n + 1) (f := ell)).2 ⟨1, 1, b, β, by norm_num, hell_repr⟩
    have hEllPoly : IsPolyhedralConvexFunction (n + 1) ell := hEllPoly_nonbot.1
    have hEllProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin (n + 1) → ℝ)) ell := by
      refine ⟨hEllPoly.1, ?_, ?_⟩
      · refine ⟨((0 : Fin (n + 1) → ℝ), (0 : ℝ)), ?_⟩
        exact (mem_epigraph_univ_iff (f := ell)).2 (by simp [ell])
      · intro z _hz
        exact hEllPoly_nonbot.2 z
    have hEllClosed : ClosedConvexFunction ell := by
      exact helperForCorollary_19_1_2_closed_of_polyhedral_proper hEllPoly hEllProper
    -- Along any ray, the last-coordinate objective changes with the fixed slope `y_last`.
    have hEllAffine : EveryRecessionDirectionIsAffine ell := by
      intro y _hyRec
      refine ⟨y (Fin.last n), ?_⟩
      intro x hx t
      simp [ell, smul_eq_mul, add_comm]
    -- The real lower bound on `h` over `C` transfers to the last-coordinate objective on `P`.
    have hEllLower : HasRealLowerBoundOn ell P := by
      refine ⟨mLower, ?_⟩
      intro z hzP
      let p : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm z
      have hp_epi :
          p ∈ epigraph (Set.univ : Set (Fin n → ℝ)) h := by
        simpa [p] using hsymm_mem_epigraph_of_memP (z := z) hzP
      have hpC : p.1 ∈ C := by
        simpa [p] using hfst_memC_of_memP (z := z) hzP
      have hh_le : h p.1 ≤ (p.2 : EReal) := (mem_epigraph_univ_iff (f := h)).1 hp_epi
      have hm_le_h : (mLower : EReal) ≤ h p.1 := hmLower p.1 hpC
      have hm_le_p2 : (mLower : EReal) ≤ (p.2 : EReal) := le_trans hm_le_h hh_le
      have hlast :
          p.2 = (prodLinearEquiv_append_coord (n := n) p) (Fin.last n) := by
        simpa using
          helperForTheorem_19_4_last_coord_prodLinearEquiv_append_coord
            (n := n) p.1 p.2
      calc
        (mLower : EReal) ≤ (p.2 : EReal) := hm_le_p2
        _ = ell z := by simpa [ell, p] using congrArg (fun r : ℝ => (r : EReal)) hlast
    have hLiftedAttains : AttainsInfimumOn ell P := by
      exact
        attainsInfimumOn_polyhedralConvexSet_of_recessionDirections_affine
          (h := ell) hEllClosed hEllProper hEllAffine P hPne hPpoly hEllLower
    obtain ⟨zBar, hzBarMin⟩ := hLiftedAttains
    let pBar : (Fin n → ℝ) × ℝ := (prodLinearEquiv_append_coord (n := n)).symm zBar.1
    let xBar : Fin n → ℝ := pBar.1
    let μBar : ℝ := pBar.2
    have hpBar_epi :
        pBar ∈ epigraph (Set.univ : Set (Fin n → ℝ)) h := by
      simpa [pBar] using hsymm_mem_epigraph_of_memP (z := zBar.1) zBar.property
    have hxBarC : xBar ∈ C := by
      simpa [xBar, pBar] using hfst_memC_of_memP (z := zBar.1) zBar.property
    have hxBar_le_muBar : h xBar ≤ (μBar : EReal) := by
      simpa [xBar, μBar, pBar] using (mem_epigraph_univ_iff (f := h)).1 hpBar_epi
    have hxBarBot : h xBar ≠ (⊥ : EReal) := hnotbotOnC xBar hxBarC
    have hxBarTop : h xBar ≠ (⊤ : EReal) := by
      exact lt_top_iff_ne_top.mp (lt_of_le_of_lt hxBar_le_muBar (by simp))
    let μBarExact : ℝ := (h xBar).toReal
    have hμBarExact : ((μBarExact : ℝ) : EReal) = h xBar := by
      simpa [μBarExact] using
        EReal.coe_toReal (x := h xBar) hxBarTop hxBarBot
    have hzEqP :
        prodLinearEquiv_append_coord (n := n) (xBar, μBarExact) ∈ P := by
      have hxBar_le_muBarExact : h xBar ≤ (μBarExact : EReal) := by
        rw [hμBarExact]
      exact hmemP_of_memC_of_le hxBarC hxBar_le_muBarExact
    let zEq : P := ⟨prodLinearEquiv_append_coord (n := n) (xBar, μBarExact), hzEqP⟩
    have hell_prod :
        ∀ x : Fin n → ℝ, ∀ μ : ℝ,
          ell (prodLinearEquiv_append_coord (n := n) (x, μ)) = (μ : EReal) := by
      intro x μ
      simpa [ell] using
        congrArg (fun r : ℝ => (r : EReal))
          (helperForTheorem_19_4_last_coord_prodLinearEquiv_append_coord
            (n := n) x μ).symm
    have hell_zBar : ell zBar = (μBar : EReal) := by
      simpa [pBar, μBar] using hell_prod pBar.1 pBar.2
    have hzBar_le_zEq : ell zBar ≤ ell zEq := by
      rw [hzBarMin]
      exact iInf_le (fun z : P => ell z) zEq
    have hμBar_le_exact : (μBar : EReal) ≤ (μBarExact : EReal) := by
      calc
        (μBar : EReal) = ell zBar := hell_zBar.symm
        _ ≤ ell zEq := hzBar_le_zEq
        _ = (μBarExact : EReal) := by simpa [zEq] using hell_prod xBar μBarExact
    have hμEq : (μBar : EReal) = h xBar := by
      apply le_antisymm
      · calc
          (μBar : EReal) ≤ (μBarExact : EReal) := hμBar_le_exact
          _ = h xBar := hμBarExact
      · exact hxBar_le_muBar
    refine ⟨⟨xBar, hxBarC⟩, le_antisymm ?_ ?_⟩
    · -- Comparing the lifted minimizer with the lifted witness over any feasible `y` gives a
      -- pointwise lower bound against all values `h y`.
      refine le_iInf ?_
      intro y
      by_cases hyTop : h y = (⊤ : EReal)
      · rw [← hμEq]
        simpa [hyTop] using (show (μBar : EReal) ≤ (⊤ : EReal) from le_top)
      · have hyBot : h y ≠ (⊥ : EReal) := hnotbotOnC y y.property
        let μy : ℝ := (h y).toReal
        have hμy : ((μy : ℝ) : EReal) = h y := by
          simpa [μy] using EReal.coe_toReal (x := h y) hyTop hyBot
        have hyLeμy : h y ≤ (μy : EReal) := by
          rw [hμy]
        have hzYP :
            prodLinearEquiv_append_coord (n := n) (y, μy) ∈ P := by
          exact hmemP_of_memC_of_le y.property hyLeμy
        let zY : P := ⟨prodLinearEquiv_append_coord (n := n) (y, μy), hzYP⟩
        have hzBar_le_y : ell zBar ≤ ell zY := by
          rw [hzBarMin]
          exact iInf_le (fun z : P => ell z) zY
        have hμBar_le_hy : (μBar : EReal) ≤ h y := by
          calc
            (μBar : EReal) = ell zBar := hell_zBar.symm
            _ ≤ ell zY := hzBar_le_y
            _ = (μy : EReal) := by simpa [zY] using hell_prod y μy
            _ = h y := hμy
        rw [← hμEq]
        exact hμBar_le_hy
    · exact iInf_le (fun y : C => h y) ⟨xBar, hxBarC⟩

end Section27
end Chap06
