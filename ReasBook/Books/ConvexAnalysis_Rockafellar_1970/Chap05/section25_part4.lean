/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part3

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

/-- Helper for Corollary 25.1.2: a differentiability point of `f` exposes the corresponding graph
point of `f*`. -/
lemma helperForCorollary_25_1_2_exposedPoint_of_differentiablePoint
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (x : Fin n → Real) (hdiff : ERealDifferentiableAt f x) :
    IsExposedPoint
      (epigraph (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f))
      (erealGradientAt hdiff, (fenchelConjugate n f (erealGradientAt hdiff)).toReal) := by
  let g : Fin n → Real := erealGradientAt hdiff
  let C : Set ((Fin n → Real) × Real) :=
    epigraph (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  let target : (Fin n → Real) × Real := (g, (fenchelConjugate n f g).toReal)
  let l : ((Fin n → Real) × Real) →ₗ[Real] Real :=
    (dotProductEquiv Real (Fin n) x).comp (LinearMap.fst Real (Fin n → Real) Real) -
      LinearMap.snd Real (Fin n → Real) Real
  have hproperConj :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hcore :=
    helperForTheorem_25_1_gradient_gives_subgradient_and_directionalDerivative
      (hf := hproper.1) (hdiff := hdiff)
  have hsub : IsSubgradientAt f x (dotProductEquiv Real (Fin n) g) := by
    simpa [g] using hcore.2
  have hsubE : IsEuclideanSubgradientAt f x g := by
    simpa [IsEuclideanSubgradientAt, g] using hsub
  have hclx : convexFunctionClosure f x = f x :=
    helperForCorollary_23_5_2_closure_eq_at_point_of_euclideanSubgradient
      f hproper x g hsubE
  have hdual : DualFenchelSupremumAttainedAt f x g := by
    exact (((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
      f hproper x g).2 hclx).out 0 5).1 hsubE
  have hatt : PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) g x :=
    (helperForTheorem_23_5_primalSupremumAttainedAt_conjugate_iff_dualSupremumAttainedAt
      f x g).2 hdual
  have hgFinite : fenchelConjugate n f g ≠ (⊤ : EReal) ∧
      fenchelConjugate n f g ≠ (⊥ : EReal) := by
    -- The maximizing conjugate graph point is finite by the Fenchel-Young inequality.
    have hfy : FenchelYoungInequalityAt (fenchelConjugate n f) g x :=
      (helperForTheorem_23_5_primalSupremumAttainedAt_iff_fenchelYoungInequality
        (fenchelConjugate n f) g x).1 hatt
    exact helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality
      (fenchelConjugate n f) hproperConj g x hfy
  have htarget_mem : target ∈ C := by
    -- The target graph point lies in `epi f*` at the canonical real height.
    exact (mem_epigraph_univ_iff (f := fenchelConjugate n f)).2
      (by simpa [target, g] using EReal.le_coe_toReal hgFinite.1)
  have hconvC : Convex ℝ C := by
    simpa [C] using convex_epigraph_of_convexFunctionOn hproperConj.1
  have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) :=
    ERealDifferentiableAt.finiteAt hdiff
  have huniqGrad :
      ∀ y : Fin n → Real,
        IsSubgradientAt f x (dotProductEquiv Real (Fin n) y) → y = g := by
    -- Differentiability makes the gradient the unique Euclidean subgradient at `x`.
    intro y hy
    exact
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hproper.1 x hxFinite).1 hdiff |>.2.2 y hy
  dsimp [IsExposedPoint, IsExposedFace]
  refine ⟨hconvC, ?_, ⟨l, ?_⟩⟩
  · intro q hq
    rcases Set.mem_singleton_iff.1 hq with rfl
    exact htarget_mem
  · ext q
    constructor
    · intro hq
      rcases hq with rfl
      -- The gradient graph point maximizes `(y, μ) ↦ ⟪x,y⟫ - μ` on the conjugate epigraph.
      refine (mem_maximizers_iff (C := C) (h := l) (x := target)).2 ?_
      refine ⟨htarget_mem, ?_⟩
      intro q hqC
      have hqLe : fenchelConjugate n f q.1 ≤ (q.2 : EReal) :=
        (mem_epigraph_univ_iff (f := fenchelConjugate n f)).1 hqC
      have hqTop : fenchelConjugate n f q.1 ≠ (⊤ : EReal) := by
        intro htop
        rw [htop] at hqLe
        exact (not_top_le_coe q.2 hqLe).elim
      have hqBot : fenchelConjugate n f q.1 ≠ (⊥ : EReal) :=
        hproperConj.2.2 q.1 (by simp)
      have hqToRealLe : (fenchelConjugate n f q.1).toReal ≤ q.2 := by
        exact_mod_cast
          (show (((fenchelConjugate n f q.1).toReal : Real) : EReal) ≤ (q.2 : EReal) by
            rw [EReal.coe_toReal hqTop hqBot]
            exact hqLe)
      have hAttq :
          ((dotProduct x q.1 : Real) : EReal) - fenchelConjugate n f q.1 ≤
            ((dotProduct x g : Real) : EReal) - fenchelConjugate n f g := by
        simpa [dotProduct_comm, g] using hatt q.1
      have hGraphLeTargetE :
          (((dotProduct x q.1 - (fenchelConjugate n f q.1).toReal : Real) : Real) : EReal) ≤
            (((dotProduct x g - (fenchelConjugate n f g).toReal : Real) : Real) : EReal) := by
        simpa [EReal.coe_sub, EReal.coe_toReal hqTop hqBot,
          EReal.coe_toReal hgFinite.1 hgFinite.2] using hAttq
      have hGraphLeTarget :
          dotProduct x q.1 - (fenchelConjugate n f q.1).toReal ≤
            dotProduct x g - (fenchelConjugate n f g).toReal := by
        exact_mod_cast hGraphLeTargetE
      have hValueLeGraph :
          dotProduct x q.1 - q.2 ≤
            dotProduct x q.1 - (fenchelConjugate n f q.1).toReal := by
        linarith
      simpa [l, target, g] using le_trans hValueLeGraph hGraphLeTarget
    · intro hqmax
      -- Equality in the maximizer set forces another epigraph point back onto the same graph
      -- point, and then unique subgradient data identifies its horizontal coordinate with `g`.
      rcases (mem_maximizers_iff (C := C) (h := l) (x := q)).1 hqmax with ⟨hqC, hqmax_le⟩
      have htarget_le : l target ≤ l q := hqmax_le target htarget_mem
      have hqLe : fenchelConjugate n f q.1 ≤ (q.2 : EReal) :=
        (mem_epigraph_univ_iff (f := fenchelConjugate n f)).1 hqC
      have hqTop : fenchelConjugate n f q.1 ≠ (⊤ : EReal) := by
        intro htop
        rw [htop] at hqLe
        exact (not_top_le_coe q.2 hqLe).elim
      have hqBot : fenchelConjugate n f q.1 ≠ (⊥ : EReal) :=
        hproperConj.2.2 q.1 (by simp)
      have hqToRealLe : (fenchelConjugate n f q.1).toReal ≤ q.2 := by
        exact_mod_cast
          (show (((fenchelConjugate n f q.1).toReal : Real) : EReal) ≤ (q.2 : EReal) by
            rw [EReal.coe_toReal hqTop hqBot]
            exact hqLe)
      have hAttq :
          ((dotProduct x q.1 : Real) : EReal) - fenchelConjugate n f q.1 ≤
            ((dotProduct x g : Real) : EReal) - fenchelConjugate n f g := by
        simpa [dotProduct_comm, g] using hatt q.1
      have hGraphLeTargetE :
          (((dotProduct x q.1 - (fenchelConjugate n f q.1).toReal : Real) : Real) : EReal) ≤
            (((dotProduct x g - (fenchelConjugate n f g).toReal : Real) : Real) : EReal) := by
        simpa [EReal.coe_sub, EReal.coe_toReal hqTop hqBot,
          EReal.coe_toReal hgFinite.1 hgFinite.2] using hAttq
      have hGraphLeTarget :
          dotProduct x q.1 - (fenchelConjugate n f q.1).toReal ≤
            dotProduct x g - (fenchelConjugate n f g).toReal := by
        exact_mod_cast hGraphLeTargetE
      have hValueLeGraph :
          dotProduct x q.1 - q.2 ≤
            dotProduct x q.1 - (fenchelConjugate n f q.1).toReal := by
        linarith
      have hq_le : l q ≤ l target := by
        simpa [l, target, g] using le_trans hValueLeGraph hGraphLeTarget
      have hEqVal : l q = l target := le_antisymm hq_le htarget_le
      have hEqVal' :
          dotProduct x q.1 - q.2 =
            dotProduct x g - (fenchelConjugate n f g).toReal := by
        simpa [l, target, g] using hEqVal
      have hqHeight : q.2 = (fenchelConjugate n f q.1).toReal :=
        helperForCorollary_25_1_2_epigraphEquality_forces_graphHeight
          (f := f) hproper hatt hqC hEqVal'
      have hEqGraph :
          dotProduct x q.1 - (fenchelConjugate n f q.1).toReal =
            dotProduct x g - (fenchelConjugate n f g).toReal := by
        simpa [hqHeight] using hEqVal'
      have hqAtt : PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) q.1 x := by
        -- Replacing the target graph height by the new equality witness makes `q.1` another
        -- conjugate maximizer for the same primal point.
        intro z
        have hzTarget :
            ((dotProduct x z : Real) : EReal) - fenchelConjugate n f z ≤
              (((dotProduct x g - (fenchelConjugate n f g).toReal : Real) : Real) : EReal) := by
          simpa [dotProduct_comm, EReal.coe_sub, EReal.coe_toReal hgFinite.1 hgFinite.2] using
            hatt z
        have hzTarget' :
            ((dotProduct x z : Real) : EReal) - fenchelConjugate n f z ≤
              (((dotProduct x q.1 - (fenchelConjugate n f q.1).toReal : Real) : Real) : EReal) := by
          rw [hEqGraph]
          exact hzTarget
        simpa [dotProduct_comm, EReal.coe_sub, EReal.coe_toReal hqTop hqBot] using hzTarget'
      have hqDual : DualFenchelSupremumAttainedAt f x q.1 :=
        (helperForTheorem_23_5_primalSupremumAttainedAt_conjugate_iff_dualSupremumAttainedAt
          f x q.1).1 hqAtt
      have hqSubE : IsEuclideanSubgradientAt f x q.1 := by
        exact (((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
          f hproper x q.1).2 hclx).out 5 0).1 hqDual
      have hqSub : IsSubgradientAt f x (dotProductEquiv Real (Fin n) q.1) := by
        simpa [IsEuclideanSubgradientAt] using hqSubE
      have hqGrad : q.1 = g := huniqGrad q.1 hqSub
      apply Set.mem_singleton_iff.2
      apply Prod.ext
      · exact hqGrad
      · simpa [target, g, hqGrad] using hqHeight

/-- Corollary 25.1.2: for a proper convex function `f` on `ℝ^n`, a point of `epi f*` is an
exposed point exactly when it is the graph point `(xStar, f*(xStar))` above a vector `xStar`
that occurs as the gradient of `f` at some differentiability point `x`. -/
theorem isExposedPoint_epigraph_fenchelConjugate_iff_exists_differentiable_point
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (p : (Fin n → Real) × Real) :
    IsExposedPoint (epigraph (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) p ↔
      ∃ (x : Fin n → Real) (hdiff : ERealDifferentiableAt f x),
        p = (erealGradientAt hdiff,
          (fenchelConjugate n f (erealGradientAt hdiff)).toReal) := by
  constructor
  · intro hp
    -- Extract the unique conjugate maximizer encoded by the exposing functional of the epigraph.
    rcases helperForCorollary_25_1_2_exposedPoint_yields_unique_primalAttainment
        (f := f) hproper p hp with
      ⟨x, hpGraph, hpAtt, hpUniq⟩
    -- Convert that unique attainment into differentiability of `f` and identify the gradient.
    rcases helperForCorollary_25_1_2_differentiablePoint_of_unique_conjugateAttainment
        (f := f) hproper hpAtt hpUniq with
      ⟨hdiff, hgrad⟩
    refine ⟨x, hdiff, ?_⟩
    -- The exposed point is precisely the graph point over the recovered gradient.
    ext
    · simp [hgrad]
    · simp [hpGraph, hgrad]
  · rintro ⟨x, hdiff, rfl⟩
    -- The gradient graph point exposes `epi f*` via the affine functional `(y, μ) ↦ ⟪x, y⟫ - μ`.
    exact helperForCorollary_25_1_2_exposedPoint_of_differentiablePoint
      (f := f) hproper x hdiff

-- Proof sketch: use Corollary 13.2.1 to replace `cl g` by the support function of the closed
-- convex set `C`, apply Corollary 25.1.2 to that support function to characterize exposed points
-- by gradients of differentiability points, and then use the closure invariance of differentiability
-- and gradients from Corollary 25.1.1.1 to transfer the conclusion back from `cl g` to `g`.
/-- Helper for Corollary 25.1.3: the convex closure of `g` is the support function of the set cut
out by its linear minorants. -/
lemma helperForCorollary_25_1_3_closure_eq_supportFunction
    {n : Nat} (C : Set (Fin n → Real)) (g : (Fin n → Real) → EReal)
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g)
    (hgpos : PositivelyHomogeneous g)
    (hCeq :
      C =
        {z : Fin n → Real |
          ∀ y : Fin n → Real, ((dotProduct y z : Real) : EReal) ≤ g y}) :
    convexFunctionClosure g = supportFunctionEReal C := by
  have hgconv : ConvexFunction g := by
    simpa [ConvexFunction] using hgproper.1
  have hdomne :
      Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → Real)) g) :=
    section13_effectiveDomain_nonempty_of_proper hgproper
  rcases hdomne with ⟨x, hxdom⟩
  have hnotTop : ¬ ∀ y : Fin n → Real, g y = (⊤ : EReal) := by
    intro hall
    exact (mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := g) hxdom)
      (hall x)
  rcases
      clConv_eq_supportFunctionEReal_setOf_forall_dotProduct_le
        (n := n) (f := g) hgpos hgconv hnotTop with
    ⟨C0, _hC0closed, _hC0conv, hclConv, hC0eq⟩
  have hclEqClosure : clConv n g = convexFunctionClosure g := by
    -- Identify `clConv` with the convex-function closure through Fenchel biconjugation.
    calc
      clConv n g = fenchelConjugate n (fenchelConjugate n g) := by
        symm
        simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := g))
      _ = convexFunctionClosure g := by
        simpa using
          (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
            (n := n) (f := g) hgconv)
  have hC0eqC : C0 = C := by
    calc
      C0 = {z : Fin n → Real | ∀ y : Fin n → Real, ((dotProduct y z : Real) : EReal) ≤ g y} :=
        hC0eq
      _ = C := hCeq.symm
  -- Replace the abstract support set from Corollary 13.2.1 by the given set `C`.
  calc
    convexFunctionClosure g = clConv n g := hclEqClosure.symm
    _ = supportFunctionEReal C0 := hclConv
    _ = supportFunctionEReal C := by rw [hC0eqC]

/-- Helper for Corollary 25.1.3: after representing a linear functional by a dot product, its
maximizers on `C` are exactly the Euclidean support-function subgradients at the representing
vector. -/
lemma helperForCorollary_25_1_3_mem_maximizers_iff_supportFunctionSubgradient
    {n : Nat} (C : Set (Fin n → Real))
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    {l : (Fin n → Real) →ₗ[ℝ] Real} {y x : Fin n → Real}
    (hy : ∀ w : Fin n → Real, l w = w ⬝ᵥ y) :
    x ∈ maximizers C l ↔ IsEuclideanSubgradientAt (supportFunctionEReal C) y x := by
  constructor
  · intro hx
    have hxDot : x ∈ C ∧ ∀ w ∈ C, dotProduct w y ≤ dotProduct x y := by
      -- Re-express the exposed maximizer condition using the representing vector `y`.
      rcases (mem_maximizers_iff (C := C) (h := l) (x := x)).1 hx with ⟨hxC, hxmax⟩
      refine ⟨hxC, ?_⟩
      intro w hwC
      simpa [hy w, hy x] using hxmax w hwC
    -- The Chapter 13 support-function theorem turns those maximizers into Euclidean subgradients.
    exact
      (euclidean_subgradient_supportFunctionEReal_iff_mem_and_maximizes_on_closed_convex_set
        C hCne hCclosed hCconv y x).2 hxDot
  · intro hxSub
    have hxDot :
        x ∈ C ∧ ∀ w ∈ C, dotProduct w y ≤ dotProduct x y :=
      (euclidean_subgradient_supportFunctionEReal_iff_mem_and_maximizes_on_closed_convex_set
        C hCne hCclosed hCconv y x).1 hxSub
    -- Convert the dot-product maximizer statement back to the original linear functional `l`.
    refine (mem_maximizers_iff (C := C) (h := l) (x := x)).2 ?_
    refine ⟨hxDot.1, ?_⟩
    intro w hwC
    simpa [hy w, hy x] using hxDot.2 w hwC

/-- Helper for Corollary 25.1.3: exposed points of a closed convex set are exactly gradients of
differentiability points of its support function. -/
lemma helperForCorollary_25_1_3_isExposedPoint_iff_exists_gradient_supportFunction
    {n : Nat} (C : Set (Fin n → Real)) (z : Fin n → Real)
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex ℝ C) :
    IsExposedPoint C z ↔
      ∃ y : Fin n → Real,
        ∃ hdiff : ERealDifferentiableAt (supportFunctionEReal C) y,
          erealGradientAt hdiff = z := by
  have hsupport :=
    section13_supportFunctionEReal_closedProperConvex_posHom (n := n) (C := C) hCne hCconv
  constructor
  · intro hzExposed
    -- Route correction: rather than rebuilding the epigraph-exposed equivalence, use the
    -- support-function subgradient characterization plus Theorem 25.1.
    dsimp [IsExposedPoint, IsExposedFace] at hzExposed
    rcases hzExposed with ⟨_hconvC, hzSubset, ⟨l, hzEq⟩⟩
    rcases linearMap_exists_dotProduct_representation (φ := l) with ⟨y, hy⟩
    have hzMax : z ∈ maximizers C l := by
      simpa [hzEq] using (show z ∈ ({z} : Set (Fin n → Real)) by simp)
    have hzSubE : IsEuclideanSubgradientAt (supportFunctionEReal C) y z := by
      -- The exposing functional becomes the maximizing dot-product direction.
      exact
        (helperForCorollary_25_1_3_mem_maximizers_iff_supportFunctionSubgradient
          (C := C) hCne hCclosed hCconv hy).1 hzMax
    have hzSub : IsSubgradientAt (supportFunctionEReal C) y (dotProductEquiv Real (Fin n) z) := by
      simpa [IsEuclideanSubgradientAt] using hzSubE
    have hyFinite :
        supportFunctionEReal C y ≠ (⊤ : EReal) ∧ supportFunctionEReal C y ≠ (⊥ : EReal) :=
      helperForTheorem_23_5_finiteAt_of_euclideanSubgradient
        (supportFunctionEReal C) hsupport.2.1 y z hzSubE
    have huniq :
        ∃! g' : Fin n → Real,
          IsSubgradientAt (supportFunctionEReal C) y (dotProductEquiv Real (Fin n) g') := by
      refine ⟨z, hzSub, ?_⟩
      intro g' hg'
      have hg'SubE : IsEuclideanSubgradientAt (supportFunctionEReal C) y g' := by
        simpa [IsEuclideanSubgradientAt] using hg'
      have hg'MaxL : g' ∈ maximizers C l := by
        -- Any competing subgradient maximizes the same exposing functional on `C`.
        exact
          (helperForCorollary_25_1_3_mem_maximizers_iff_supportFunctionSubgradient
            (C := C) hCne hCclosed hCconv hy).2 hg'SubE
      have hg'Singleton : g' ∈ ({z} : Set (Fin n → Real)) := by
        simpa [hzEq] using hg'MaxL
      exact Set.mem_singleton_iff.1 hg'Singleton
    have hdiff :
        ERealDifferentiableAt (supportFunctionEReal C) y :=
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        (supportFunctionEReal C) hsupport.1.1 y hyFinite).2 huniq
    have hgradSub :
        IsSubgradientAt (supportFunctionEReal C) y
          (dotProductEquiv Real (Fin n) (erealGradientAt hdiff)) :=
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        (supportFunctionEReal C) hsupport.1.1 y hyFinite).1 hdiff |>.1
    have hgradEq : erealGradientAt hdiff = z := by
      have hcoreDiff :=
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (supportFunctionEReal C) hsupport.1.1 y hyFinite).1 hdiff
      exact (hcoreDiff.2.2 z hzSub).symm
    exact ⟨y, hdiff, hgradEq⟩
  · rintro ⟨y, hdiff, hgrad⟩
    have hyDot :
        ∀ w : Fin n → Real,
          (dotProductEquiv Real (Fin n) y) w = w ⬝ᵥ y := by
      -- Use the canonical dot-product linear functional as the exposing functional.
      intro w
      simp [dotProduct_comm]
    have hyFinite :
        supportFunctionEReal C y ≠ (⊤ : EReal) ∧ supportFunctionEReal C y ≠ (⊥ : EReal) :=
      ERealDifferentiableAt.finiteAt hdiff
    have hcore :=
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        (supportFunctionEReal C) hsupport.1.1 y hyFinite).1 hdiff
    have hzSubE :
        IsEuclideanSubgradientAt (supportFunctionEReal C) y (erealGradientAt hdiff) := by
      simpa [IsEuclideanSubgradientAt] using hcore.1
    have hzMax :
        erealGradientAt hdiff ∈ C ∧
          ∀ w ∈ C, dotProduct w y ≤ dotProduct (erealGradientAt hdiff) y :=
      (euclidean_subgradient_supportFunctionEReal_iff_mem_and_maximizes_on_closed_convex_set
        C hCne hCclosed hCconv y (erealGradientAt hdiff)).1 hzSubE
    -- The gradient gives the exposing functional and differentiability makes its maximizer unique.
    refine ⟨hCconv, ?_, ?_⟩
    · intro w hw
      rcases Set.mem_singleton_iff.1 hw with rfl
      simpa [hgrad] using hzMax.1
    · refine ⟨dotProductEquiv Real (Fin n) y, ?_⟩
      ext w
      constructor
      · intro hw
        rcases Set.mem_singleton_iff.1 hw with rfl
        have hgradMax :
            erealGradientAt hdiff ∈ maximizers C (dotProductEquiv Real (Fin n) y) := by
          -- The gradient maximizes the exposing dot-product functional on `C`.
          exact
            (helperForCorollary_25_1_3_mem_maximizers_iff_supportFunctionSubgradient
              (C := C) hCne hCclosed hCconv hyDot).2 hzSubE
        simpa [hgrad] using hgradMax
      · intro hwMax
        have hwSubE : IsEuclideanSubgradientAt (supportFunctionEReal C) y w := by
          -- Every other maximizer gives another support-function subgradient at the same `y`.
          exact
            (helperForCorollary_25_1_3_mem_maximizers_iff_supportFunctionSubgradient
              (C := C) hCne hCclosed hCconv hyDot).1 hwMax
        have hwSub :
            IsSubgradientAt (supportFunctionEReal C) y (dotProductEquiv Real (Fin n) w) := by
          simpa [IsEuclideanSubgradientAt] using hwSubE
        have hwEqGrad : w = erealGradientAt hdiff := hcore.2.2 w hwSub
        apply Set.mem_singleton_iff.2
        simpa [hgrad] using hwEqGrad

/-- Helper for Corollary 25.1.3: differentiability points of `convexFunctionClosure g` are exactly
the differentiability points of `g`, with the same gradient. -/
lemma helperForCorollary_25_1_3_exists_gradient_closure_iff_exists_gradient_original
    {n : Nat} (g : (Fin n → Real) → EReal) (z : Fin n → Real)
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g) :
    (∃ y : Fin n → Real,
        ∃ hdiff : ERealDifferentiableAt (convexFunctionClosure g) y,
          erealGradientAt hdiff = z) ↔
      (∃ y : Fin n → Real, ∃ hdiff : ERealDifferentiableAt g y, erealGradientAt hdiff = z) := by
  have hclosureProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (convexFunctionClosure g) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := g) hgproper).1.2
  constructor
  · rintro ⟨y, hcldiff, hgrad⟩
    have hyIntClosure :
        y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure g)) :=
      (convexFunction_proper_and_mem_interior_of_differentiableAt
        (convexFunctionClosure g) hclosureProper.1 y hcldiff).2
    have hyInt :
        y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) g) :=
      helperForCorollary_25_1_2_mem_interior_effectiveDomain_of_closure_mem_interior
        hgproper hyIntClosure
    have htransfer :=
      convexFunction_differentiableAt_iff_convexFunctionClosure_differentiableAt_and_gradient_eq
        g hgproper.1 y hyInt
    have hdiff : ERealDifferentiableAt g y := htransfer.1.2 hcldiff
    refine ⟨y, hdiff, ?_⟩
    calc
      erealGradientAt hdiff = erealGradientAt hcldiff := by
        symm
        exact htransfer.2 hdiff hcldiff
      _ = z := hgrad
  · rintro ⟨y, hdiff, hgrad⟩
    have hyInt :
        y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) g) :=
      (convexFunction_proper_and_mem_interior_of_differentiableAt g hgproper.1 y hdiff).2
    have htransfer :=
      convexFunction_differentiableAt_iff_convexFunctionClosure_differentiableAt_and_gradient_eq
        g hgproper.1 y hyInt
    have hcldiff : ERealDifferentiableAt (convexFunctionClosure g) y := htransfer.1.1 hdiff
    refine ⟨y, hcldiff, ?_⟩
    calc
      erealGradientAt hcldiff = erealGradientAt hdiff := htransfer.2 hdiff hcldiff
      _ = z := hgrad

/-- Corollary 25.1.3: let `C` be a nonempty closed convex set, and let `g` be a positively
homogeneous proper convex function such that
`C = {z | ∀ y, ⟨y, z⟩ ≤ g(y)}`. Then `z` is an exposed point of `C` if and only if there exists
`y` such that `g` is differentiable at `y` and `∇ g(y) = z`. In particular, `g` may be taken to be
the support function of `C`. -/
theorem isExposedPoint_iff_exists_gradient_of_differentiable_positivelyHomogeneous_properConvex
    {n : Nat} (C : Set (Fin n → Real)) (g : (Fin n → Real) → EReal) (z : Fin n → Real)
    (hCne : C.Nonempty) (hCclosed : IsClosed C) (hCconv : Convex ℝ C)
    (hgproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) g)
    (hgpos : PositivelyHomogeneous g)
    (hCeq :
      C =
        {z : Fin n → Real |
          ∀ y : Fin n → Real, ((dotProduct y z : Real) : EReal) ≤ g y}) :
    IsExposedPoint C z ↔
      ∃ y : Fin n → Real, ∃ hdiff : ERealDifferentiableAt g y, erealGradientAt hdiff = z := by
  have hclosureEq :
      convexFunctionClosure g = supportFunctionEReal C :=
    helperForCorollary_25_1_3_closure_eq_supportFunction
      (C := C) (g := g) hgproper hgpos hCeq
  -- Route correction: use the equivalent unique-subgradient characterization of exposed points
  -- for the support function, then transport differentiability back from `cl g` to `g`.
  calc
    IsExposedPoint C z ↔
        ∃ y : Fin n → Real,
          ∃ hdiff : ERealDifferentiableAt (supportFunctionEReal C) y,
            erealGradientAt hdiff = z :=
      helperForCorollary_25_1_3_isExposedPoint_iff_exists_gradient_supportFunction
        (C := C) (z := z) hCne hCclosed hCconv
    _ ↔
        ∃ y : Fin n → Real,
          ∃ hdiff : ERealDifferentiableAt (convexFunctionClosure g) y,
            erealGradientAt hdiff = z := by
          rw [← hclosureEq]
    _ ↔
        ∃ y : Fin n → Real, ∃ hdiff : ERealDifferentiableAt g y, erealGradientAt hdiff = z :=
      helperForCorollary_25_1_3_exists_gradient_closure_iff_exists_gradient_original
        (g := g) (z := z) hgproper

-- Proof sketch: use Theorem 25.1 to identify differentiability at `x` with uniqueness of the
-- subgradient, and combine this with the Chapter 23 description of the directional derivative as
-- the support function of the subdifferential. A singleton subdifferential makes the directional
-- derivative equal to a dot product, while conversely linearity forces the support set to collapse
-- to one vector subgradient. If the two-sided coordinate partials exist and are finite, then the
-- directional derivative is linear on the standard basis and hence on all of `ℝⁿ`.
/-- Helper for Theorem 25.2: coercing a finite real sum into `EReal` equals summing the coerced
terms. -/
lemma helperForTheorem_25_2_coe_finset_sum_real_toEReal {ι : Type} (s : Finset ι)
    (f : ι → Real) :
    (((Finset.sum s f : Real)) : EReal) =
      Finset.sum s (fun i => ((f i : Real) : EReal)) := by
  classical
  -- Expand the finite sum one term at a time and use additivity of the real-to-`EReal` coercion.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    simp [Finset.sum_insert, ha, hs]

/-- Helper for Theorem 25.2: a linear directional-derivative formula forces a unique vector
subgradient at the base point. -/
lemma helperForTheorem_25_2_uniqueSubgradient_of_linearDirectionalDerivative
    {n : Nat} {f : (Fin n → Real) → EReal} (hf : ConvexFunction f) {x : Fin n → Real}
    (hx : f x ≠ ⊤ ∧ f x ≠ ⊥) {g : Fin n → Real}
    (hdir :
      ∀ y : Fin n → Real,
        upperDirectionalDerivativeAt f x y = (((g ⬝ᵥ y : Real) : Real) : EReal)) :
    ∃! v : Fin n → Real, IsSubgradientAt f x (dotProductEquiv Real (Fin n) v) := by
  have hsubg : IsSubgradientAt f x (dotProductEquiv Real (Fin n) g) := by
    -- The Chapter 23 characterization turns the pointwise lower bound `⟨g,y⟩ ≤ f'(x;y)` into a
    -- genuine subgradient statement.
    have hiff :=
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        f hf x hx (dotProductEquiv Real (Fin n) g)).1
    apply hiff.mpr
    intro y
    calc
      ((((dotProductEquiv Real (Fin n) g) y : Real) : Real) : EReal) =
          (((g ⬝ᵥ y : Real) : Real) : EReal) := by
            simp
      _ ≤ upperDirectionalDerivativeAt f x y := by
            exact le_of_eq (hdir y).symm
  refine ⟨g, hsubg, ?_⟩
  intro v hv
  have hiffv :=
    (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
      f hf x hx (dotProductEquiv Real (Fin n) v)).1
  have hvminor := hiffv.mp hv
  have hdotEq : ∀ y : Fin n → Real, v ⬝ᵥ y = g ⬝ᵥ y := by
    intro y
    -- Compare the two candidate subgradients on `y` and then on `-y` to get equality.
    have hle :
        (((v ⬝ᵥ y : Real) : Real) : EReal) ≤ (((g ⬝ᵥ y : Real) : Real) : EReal) := by
      calc
        (((v ⬝ᵥ y : Real) : Real) : EReal) =
            ((((dotProductEquiv Real (Fin n) v) y : Real) : Real) : EReal) := by
              simp
        _ ≤ upperDirectionalDerivativeAt f x y := hvminor y
        _ = (((g ⬝ᵥ y : Real) : Real) : EReal) := hdir y
    have hneg :
        (((g ⬝ᵥ y : Real) : Real) : EReal) ≤ (((v ⬝ᵥ y : Real) : Real) : EReal) := by
      have hneg' :
          (((v ⬝ᵥ (-y) : Real) : Real) : EReal) ≤ (((g ⬝ᵥ (-y) : Real) : Real) : EReal) := by
        calc
          (((v ⬝ᵥ (-y) : Real) : Real) : EReal) =
              ((((dotProductEquiv Real (Fin n) v) (-y) : Real) : Real) : EReal) := by
                simp
          _ ≤ upperDirectionalDerivativeAt f x (-y) := hvminor (-y)
          _ = (((g ⬝ᵥ (-y) : Real) : Real) : EReal) := hdir (-y)
      have hnegReal : -(v ⬝ᵥ y) ≤ -(g ⬝ᵥ y) := by
        simpa [dotProduct_comm] using hneg'
      have hposReal : g ⬝ᵥ y ≤ v ⬝ᵥ y := by
        linarith
      exact_mod_cast hposReal
    exact (EReal.coe_eq_coe_iff).1 (le_antisymm hle hneg)
  -- Equality of all dot products identifies the representing vectors.
  exact helperForTheorem_25_1_eq_of_dotProduct_eq hdotEq

/-- Helper for Theorem 25.2: a bilateral coordinate partial derivative pins down the upper
directional derivative on the corresponding signed basis directions. -/
lemma helperForTheorem_25_2_basisValues_of_coordinatePartials
    {n : Nat} {f : (Fin n → Real) → EReal} {x : Fin n → Real}
    (hf : ConvexFunction f) (hx : f x ≠ ⊤ ∧ f x ≠ ⊥)
    (j : Fin n) (L : Real)
    (hpartial : HasCoordinatePartialDerivativeAt f x j (L : EReal)) :
    let e : Fin n → Real := Pi.single j (1 : Real)
    upperDirectionalDerivativeAt f x e = (L : EReal) ∧
      upperDirectionalDerivativeAt f x (-e) = ((-L : Real) : EReal) := by
  let e : Fin n → Real := Pi.single j (1 : Real)
  have hright :
      Filter.Tendsto (directionalDifferenceQuotientAt f x e)
        (𝓝[>] (0 : Real))
        (𝓝 (upperDirectionalDerivativeAt f x e)) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx).1 e |>.2.1
  have heq : upperDirectionalDerivativeAt f x e = (L : EReal) :=
    -- The right-hand quotient limit already computes `f'(x; e_j)`.
    tendsto_nhds_unique hright (by simpa [e] using hpartial.1)
  have hbilat : HasBilateralDirectionalDerivativeAt f x e := ⟨(L : EReal), hpartial.1, hpartial.2⟩
  rcases
      ((bilateralDirectionalDerivative_iff_exists_neg_direction (f := f) (x := x) (y := e) hx).2).1
        hbilat with
    ⟨M, hMeq, hnegRight⟩
  have hML : M = (L : EReal) :=
    -- The bilateral witness must agree with the already known right-hand limit along `e_j`.
    tendsto_nhds_unique hMeq (by simpa [e] using hpartial.1)
  have hrightNeg :
      Filter.Tendsto (directionalDifferenceQuotientAt f x (-e))
        (𝓝[>] (0 : Real))
        (𝓝 (upperDirectionalDerivativeAt f x (-e))) :=
    (convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx).1 (-e) |>.2.1
  have hnegEq : upperDirectionalDerivativeAt f x (-e) = ((-L : Real) : EReal) := by
    -- The right-hand quotient along `-e_j` is the negated left-hand quotient along `e_j`.
    refine tendsto_nhds_unique hrightNeg ?_
    simpa [hML] using hnegRight
  exact ⟨heq, hnegEq⟩

/-- Helper for Theorem 25.2: convexity plus positive homogeneity propagates real upper bounds
through vector addition. -/
lemma helperForTheorem_25_2_add_upper_bound_of_convex_posHom
    {n : Nat} {D : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous D) (hconv : ConvexFunction D)
    {u v : Fin n → Real} {μ ν : Real}
    (hu : D u ≤ (μ : EReal)) (hv : D v ≤ (ν : EReal)) :
    D (u + v) ≤ ((μ + ν : Real) : EReal) := by
  have hconvEp : Convex ℝ (epigraph (Set.univ : Set (Fin n → Real)) D) := by
    simpa [ConvexFunction] using hconv
  have hu' : D ((2 : Real) • u) ≤ (((2 : Real) * μ : Real) : EReal) := by
    -- Scale the first upper bound so it becomes a real epigraph point at height `2μ`.
    calc
      D ((2 : Real) • u) = ((2 : Real) : EReal) * D u := by
        simpa using hpos u 2 (by norm_num)
      _ ≤ ((2 : Real) : EReal) * (μ : EReal) := by
        gcongr
      _ = ((((2 : Real) * μ : Real) : Real) : EReal) := by
        norm_num
  have hv' : D ((2 : Real) • v) ≤ (((2 : Real) * ν : Real) : EReal) := by
    -- The same scaling turns the second upper bound into a matching epigraph point.
    calc
      D ((2 : Real) • v) = ((2 : Real) : EReal) * D v := by
        simpa using hpos v 2 (by norm_num)
      _ ≤ ((2 : Real) : EReal) * (ν : EReal) := by
        gcongr
      _ = ((((2 : Real) * ν : Real) : Real) : EReal) := by
        norm_num
  have hmemu : (((2 : Real) • u), 2 * μ) ∈ epigraph (Set.univ : Set (Fin n → Real)) D := by
    exact epigraph_mem_of_le_aux
      (S := (Set.univ : Set (Fin n → Real))) (x := (2 : Real) • u) (μ := 2 * μ) (by simp) hu'
  have hmemv : (((2 : Real) • v), 2 * ν) ∈ epigraph (Set.univ : Set (Fin n → Real)) D := by
    exact epigraph_mem_of_le_aux
      (S := (Set.univ : Set (Fin n → Real))) (x := (2 : Real) • v) (μ := 2 * ν) (by simp) hv'
  have hmem :=
    hconvEp hmemu hmemv (show 0 ≤ (1 / 2 : Real) by norm_num)
      (show 0 ≤ (1 / 2 : Real) by norm_num) (by norm_num)
  have hineq :
      D ((1 / 2 : Real) • ((2 : Real) • u) + (1 / 2 : Real) • ((2 : Real) • v)) ≤
        ((((1 / 2 : Real) * (2 * μ) + (1 / 2 : Real) * (2 * ν) : Real)) : EReal) := by
    simpa [epigraph] using hmem.2
  have hvec :
      (1 / 2 : Real) • ((2 : Real) • u) + (1 / 2 : Real) • ((2 : Real) • v) = u + v := by
    -- The midpoint of the doubled vectors is exactly `u + v`.
    ext i
    ring_nf
    simp
  have hscalar :
      ((1 / 2 : Real) * (2 * μ) + (1 / 2 : Real) * (2 * ν) : Real) = μ + ν := by
    ring
  simpa [hvec, hscalar] using hineq

/-- Helper for Theorem 25.2: once the signed basis values are known, positive homogeneity fixes
the directional derivative on every coordinate ray. -/
lemma helperForTheorem_25_2_scaled_basis_value_of_signed_basis_values
    {n : Nat} {D : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous D) (hzero : D 0 = 0)
    {e : Fin n → Real} {L a : Real}
    (he : D e = (L : EReal))
    (hneg : D (-e) = ((-L : Real) : EReal)) :
    D (a • e) = ((a * L : Real) : EReal) := by
  by_cases ha0 : a = 0
  · -- The zero coordinate contributes nothing.
    subst ha0
    simp [hzero]
  · by_cases ha : 0 < a
    · -- Positive homogeneity handles the positive-ray case directly.
      calc
        D (a • e) = ((a : Real) : EReal) * D e := by
          simpa using hpos e a ha
        _ = ((a : Real) : EReal) * (L : EReal) := by
          rw [he]
        _ = ((a * L : Real) : EReal) := by
          simp [EReal.coe_mul]
    · have hnonpos : a ≤ 0 := le_of_not_gt ha
      have hlt : a < 0 := lt_of_le_of_ne hnonpos (by simpa using ha0)
      have hnegpos : 0 < -a := by
        linarith
      have hmul :
          (((-a : Real) : EReal) * (((-L : Real) : Real) : EReal)) =
            ((a * L : Real) : EReal) := by
        exact_mod_cast (show (-a) * (-L) = a * L by ring)
      -- A negative coefficient is a positive multiple of the opposite basis vector.
      calc
        D (a • e) = D ((-a) • (-e)) := by
          simp
        _ = (((-a : Real) : EReal) * D (-e)) := by
          simpa using hpos (-e) (-a) hnegpos
        _ = (((-a : Real) : EReal) * (((-L : Real) : Real) : EReal)) := by
          rw [hneg]
        _ = ((a * L : Real) : EReal) := hmul

/-- Helper for Theorem 25.2: the signed-basis values determine a global upper bound for the
directional derivative. -/
lemma helperForTheorem_25_2_upper_bound_from_signed_basis_values
    {n : Nat} {D : (Fin n → Real) → EReal}
    (hpos : PositivelyHomogeneous D) (hconv : ConvexFunction D) (hzero : D 0 = 0)
    (g : Fin n → Real)
    (hbasis : ∀ j : Fin n,
      D (Pi.single j (1 : Real)) = (g j : EReal) ∧
        D (-(Pi.single j (1 : Real) : Fin n → Real)) = ((-g j : Real) : EReal)) :
    ∀ y : Fin n → Real, D y ≤ (((g ⬝ᵥ y : Real) : Real) : EReal) := by
  intro y
  let term : Fin n → Fin n → Real := fun j => (y j) • (Pi.single j (1 : Real) : Fin n → Real)
  have hsum :
      ∀ s : Finset (Fin n),
        D (Finset.sum s term) ≤ Finset.sum s (fun j => ((g j * y j : Real) : EReal)) := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · -- The empty sum reduces to the zero-direction value.
      simp [hzero, term]
    · intro j s hj hs
      have hterm : D (term j) ≤ ((g j * y j : Real) : EReal) := by
        rcases hbasis j with ⟨hposBasis, hnegBasis⟩
        -- Each coordinate ray already has the correct linear value.
        simpa [term, mul_comm] using
          le_of_eq
            (helperForTheorem_25_2_scaled_basis_value_of_signed_basis_values
              hpos hzero hposBasis hnegBasis (a := y j))
      have hadd :=
        helperForTheorem_25_2_add_upper_bound_of_convex_posHom hpos hconv
          (u := Finset.sum s term) (v := term j)
          (μ := Finset.sum s fun k => (g k * y k : Real)) (ν := g j * y j)
          (hu := by simpa [helperForTheorem_25_2_coe_finset_sum_real_toEReal] using hs)
          (hv := hterm)
      -- Add the new coordinate contribution to the inductive upper bound.
      simpa [helperForTheorem_25_2_coe_finset_sum_real_toEReal, Finset.sum_insert, hj, term,
        add_comm, add_left_comm, add_assoc] using hadd
  have hdecomp : Finset.sum Finset.univ term = y := by
    -- Every vector is the sum of its coordinate multiples of the standard basis.
    ext i
    simp [term, Pi.single_apply]
  have hsum' : D y ≤ Finset.sum Finset.univ (fun j => ((g j * y j : Real) : EReal)) := by
    simpa [hdecomp, term] using hsum Finset.univ
  have hdot : (g ⬝ᵥ y : Real) = Finset.sum Finset.univ (fun j => g j * y j) := by
    simp [dotProduct]
  simpa [hdot, helperForTheorem_25_2_coe_finset_sum_real_toEReal] using hsum'

/-- Helper for Theorem 25.2: finite bilateral coordinate partials force the full directional
derivative map to be linear. -/
lemma helperForTheorem_25_2_coordinatePartials_imply_linearDirectionalDerivative
    {n : Nat} {f : (Fin n → Real) → EReal} (hf : ConvexFunction f) (x : Fin n → Real)
    (hx : f x ≠ ⊤ ∧ f x ≠ ⊥)
    (hpartials : ∀ j : Fin n, ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal)) :
    ∃ g : Fin n → Real,
      ∀ y : Fin n → Real,
        upperDirectionalDerivativeAt f x y = (((g ⬝ᵥ y : Real) : Real) : EReal) := by
  classical
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
    ⟨_hmono, hpos, hconv, hzero, hsymm⟩
  let D : (Fin n → Real) → EReal := upperDirectionalDerivativeAt f x
  let g : Fin n → Real := fun j => Classical.choose (hpartials j)
  have hgBasis : ∀ j : Fin n,
      D (Pi.single j (1 : Real)) = (g j : EReal) ∧
        D (-(Pi.single j (1 : Real) : Fin n → Real)) = ((-g j : Real) : EReal) := by
    intro j
    -- The chosen coordinate partial realizes the directional derivative on `±e_j`.
    simpa [D, g] using
      helperForTheorem_25_2_basisValues_of_coordinatePartials hf hx j (g j)
        (Classical.choose_spec (hpartials j))
  refine ⟨g, ?_⟩
  intro y
  have hupper :
      D y ≤ (((g ⬝ᵥ y : Real) : Real) : EReal) :=
    helperForTheorem_25_2_upper_bound_from_signed_basis_values hpos hconv hzero g hgBasis y
  have hupperNeg :
      D (-y) ≤ (((g ⬝ᵥ (-y) : Real) : Real) : EReal) :=
    helperForTheorem_25_2_upper_bound_from_signed_basis_values hpos hconv hzero g hgBasis (-y)
  have hdotNeg : g ⬝ᵥ (-y) = -(g ⬝ᵥ y) := by
    exact dotProduct_neg g y
  have hlower :
      (((g ⬝ᵥ y : Real) : Real) : EReal) ≤ D y := by
    -- Apply the upper bound to `-y` and then use the general inequality `-D(-y) ≤ D(y)`.
    calc
      (((g ⬝ᵥ y : Real) : Real) : EReal) =
          -((((g ⬝ᵥ (-y) : Real) : Real) : EReal)) := by
            rw [hdotNeg]
            simp
      _ ≤ -(D (-y)) := by
            exact (EReal.neg_le).2 (by simpa using hupperNeg)
      _ ≤ D y := hsymm y
  exact le_antisymm hupper hlower

/-- Theorem 25.2: let `f` be convex on `ℝ^n`, and let `x` be a point where `f` is finite. Then
`f` is differentiable at `x` if and only if there exists a vector `g` such that for every
direction `y`, the directional derivative `f'(x; y)` equals `⟨g, y⟩`. Moreover, if the `n`
two-sided coordinate partial derivatives of `f` at `x` all exist and are finite, then this
linearity condition holds. -/
theorem convexFunction_differentiableAt_iff_directionalDerivativeHasGradient_and_coordinatePartials_imply_linearity
    {n : Nat}
    (f : (Fin n → Real) → EReal) (hf : ConvexFunction f) (x : Fin n → Real)
    (hx : f x ≠ ⊤ ∧ f x ≠ ⊥) :
    (ERealDifferentiableAt f x ↔
      ∃ g : Fin n → Real,
        ∀ y : Fin n → Real,
          upperDirectionalDerivativeAt f x y = (((g ⬝ᵥ y : Real) : Real) : EReal)) ∧
      ((∀ j : Fin n, ∃ L : Real, HasCoordinatePartialDerivativeAt f x j (L : EReal)) →
        ∃ g : Fin n → Real,
          ∀ y : Fin n → Real,
            upperDirectionalDerivativeAt f x y = (((g ⬝ᵥ y : Real) : Real) : EReal)) := by
  constructor
  · constructor
    · intro hdiff
      -- Differentiability already identifies the directional derivative with the gradient pairing.
      refine ⟨erealGradientAt hdiff, ?_⟩
      exact
        (helperForTheorem_25_1_gradient_gives_subgradient_and_directionalDerivative
          (hf := hf) (hdiff := hdiff)).1
    · rintro ⟨g, hdir⟩
      have huniq :
          ∃! v : Fin n → Real, IsSubgradientAt f x (dotProductEquiv Real (Fin n) v) :=
        helperForTheorem_25_2_uniqueSubgradient_of_linearDirectionalDerivative hf hx hdir
      -- Theorem 25.1 upgrades the unique vector subgradient back to differentiability.
      exact
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient f hf x hx).2 huniq
  · intro hpartials
    -- The coordinate partial data determines the signed basis values and hence the whole map
    -- `y ↦ f'(x; y)`.
    exact helperForTheorem_25_2_coordinatePartials_imply_linearDirectionalDerivative hf x hx
      hpartials

-- Proof sketch: use the one-dimensional convex derivative theory from Section 24 on each compact
-- subinterval of the open interval `I`. The left and right derivatives are monotone, hence they
-- can disagree only at countably many points; at the remaining points `f` is differentiable. On
-- this differentiability set, the derivative is the common value of the one-sided derivatives, so
-- the one-sided continuity statements imply relative continuity, and monotonicity follows from the
-- ordering between left and right derivatives.
/-- Helper for Theorem 25.3: at an interior point of the open interval, ordinary differentiability
is equivalent to equality of the left and right one-sided derivatives. -/
lemma helperForTheorem_25_3_hasDerivAt_iff_eq_left_right_derivWithin
    {I : Set ℝ} (hIopen : IsOpen I) {f : ℝ → ℝ} (hf : ConvexOn ℝ I f) {x : ℝ} (hx : x ∈ I) :
    HasDerivAt f (deriv f x) x ↔
      derivWithin f (Set.Iio x) x = derivWithin f (Set.Ioi x) x := by
  have hxInt : x ∈ interior I := by
    simpa [hIopen.interior_eq] using hx
  constructor
  · intro hderiv
    -- Differentiate within each one-sided ray and identify both values with the ordinary derivative.
    calc
      derivWithin f (Set.Iio x) x = deriv f x := by
        exact hderiv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)
      _ = derivWithin f (Set.Ioi x) x := by
        symm
        exact hderiv.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)
  · intro hEq
    -- Matching left and right slope limits recombine into an ordinary derivative at `x`.
    have hleft :
        Filter.Tendsto (slope f x) (𝓝[<] x) (𝓝 (derivWithin f (Set.Iio x) x)) := by
      exact
        (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1
          (hf.hasDerivWithinAt_leftDeriv_of_mem_interior hxInt)
    have hright :
        Filter.Tendsto (slope f x) (𝓝[>] x) (𝓝 (derivWithin f (Set.Ioi x) x)) := by
      exact
        (hasDerivWithinAt_iff_tendsto_slope' (by simp)).1
          (hf.hasDerivWithinAt_rightDeriv_of_mem_interior hxInt)
    have hderiv :
        HasDerivAt f (derivWithin f (Set.Ioi x) x) x := by
      refine (hasDerivAt_iff_tendsto_slope_left_right).2 ?_
      refine ⟨?_, hright⟩
      simpa [hEq] using hleft
    simpa [hderiv.deriv] using hderiv

/-- Helper for Theorem 25.3: a right derivative taken at a point to the left of `y` is bounded
above by the left derivative at `y`. -/
lemma helperForTheorem_25_3_rightDeriv_le_leftDeriv_of_lt
    {I : Set ℝ} (hIopen : IsOpen I) {f : ℝ → ℝ} (hf : ConvexOn ℝ I f)
    {x y : ℝ} (hx : x ∈ I) (hy : y ∈ I) (hxy : x < y) :
    derivWithin f (Set.Ioi x) x ≤ derivWithin f (Set.Iio y) y := by
  have hxInt : x ∈ interior I := by
    simpa [hIopen.interior_eq] using hx
  have hyInt : y ∈ interior I := by
    simpa [hIopen.interior_eq] using hy
  -- Compare both one-sided derivatives through the secant slope joining `x` to `y`.
  exact
    (hf.rightDeriv_le_slope_of_mem_interior hxInt hy hxy).trans
      (hf.slope_le_leftDeriv_of_mem_interior hx hyInt hxy)

/-- Helper for Theorem 25.3: on the differentiability set `D`, the ordinary derivative agrees with
either one-sided derivative selector. -/
lemma helperForTheorem_25_3_deriv_eq_oneSidedDerivWithin_on_D
    {I : Set ℝ} {f : ℝ → ℝ} :
    let D : Set ℝ := {x | x ∈ I ∧ HasDerivAt f (deriv f x) x}
    Set.EqOn (deriv f) (fun x => derivWithin f (Set.Ioi x) x) D ∧
      Set.EqOn (deriv f) (fun x => derivWithin f (Set.Iio x) x) D := by
  intro D
  constructor
  · intro x hxD
    -- At a differentiability point, the ordinary derivative specializes to the right derivative.
    exact
      (hxD.2.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ioi x)).symm
  · intro x hxD
    -- The same specialization identifies the left derivative with `deriv f x`.
    exact
      (hxD.2.hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Iio x)).symm

/-- Helper for Theorem 25.3: every nondifferentiability point in `I` is a discontinuity point of
the right-derivative selector restricted to `I`. -/
lemma helperForTheorem_25_3_nondiff_subset_rightDeriv_discontinuitySet
    {I : Set ℝ} (hIopen : IsOpen I) {f : ℝ → ℝ} (hf : ConvexOn ℝ I f) :
    let D : Set ℝ := {x | x ∈ I ∧ HasDerivAt f (deriv f x) x}
    I \ D ⊆ {x ∈ I | ¬ ContinuousWithinAt (fun x => derivWithin f (Set.Ioi x) x) I x} := by
  intro D x hx
  rcases hx with ⟨hxI, hxNotD⟩
  have hxInt : x ∈ interior I := by
    simpa [hIopen.interior_eq] using hxI
  let g : ℝ → ℝ := fun t => derivWithin f (Set.Ioi t) t
  let l : ℝ → ℝ := fun t => derivWithin f (Set.Iio t) t
  have hmonoI : MonotoneOn g I := by
    simpa [g, hIopen.interior_eq] using hf.monotoneOn_rightDeriv
  have hneq : l x ≠ g x := by
    intro hEq
    have hderiv :
        HasDerivAt f (deriv f x) x :=
      (helperForTheorem_25_3_hasDerivAt_iff_eq_left_right_derivWithin
        hIopen hf hxI).2 hEq
    exact hxNotD ⟨hxI, hderiv⟩
  have hlt : l x < g x := by
    exact lt_of_le_of_ne (hf.leftDeriv_le_rightDeriv_of_mem_interior hxInt) hneq
  rcases (mem_nhds_iff_exists_Ioo_subset.mp <| mem_interior_iff_mem_nhds.mp hxInt) with
    ⟨a, b, hxab, habI⟩
  have hxIooab : x ∈ Set.Ioo a b := ⟨hxab.1, hxab.2⟩
  have hmonoLocal : MonotoneOn g (Set.Ioo a x) := by
    intro u hu v hv huv
    exact
      hmonoI
        (habI ⟨hu.1, hu.2.trans hxab.2⟩)
        (habI ⟨hv.1, hv.2.trans hxab.2⟩)
        huv
  have hleftLimit :
      Filter.Tendsto g (𝓝[<] x) (𝓝 (sSup (g '' Set.Ioo a x))) := by
    -- On the small left interval, monotonicity gives a canonical left-hand limit.
    simpa [nhdsWithin_Ioo_eq_nhdsLT hxab.1] using
      (MonotoneOn.tendsto_nhdsWithin_Ioo_left
        (Set.nonempty_Ioo.2 hxab.1) hmonoLocal
        (by
          refine ⟨l x, ?_⟩
          rintro _ ⟨z, hz, rfl⟩
          exact
            helperForTheorem_25_3_rightDeriv_le_leftDeriv_of_lt
              hIopen hf
              (habI ⟨hz.1, hz.2.trans hxab.2⟩)
              hxI hz.2))
  have hsSup_le : sSup (g '' Set.Ioo a x) ≤ l x := by
    -- Every left-nearby right derivative is bounded above by the left derivative at `x`.
    refine csSup_le ?_ ?_
    · rw [Set.image_nonempty]
      exact Set.nonempty_Ioo.2 hxab.1
    · rintro _ ⟨z, hz, rfl⟩
      exact
        helperForTheorem_25_3_rightDeriv_le_leftDeriv_of_lt
          hIopen hf
          (habI ⟨hz.1, hz.2.trans hxab.2⟩)
          hxI hz.2
  refine ⟨hxI, ?_⟩
  intro hgcont
  have hgleftI : ContinuousWithinAt g (I ∩ Set.Iio x) x :=
    (continuousWithinAt_iff_continuous_left'_right'.1 hgcont).1
  have hfilterEq : 𝓝[I ∩ Set.Iio x] x = 𝓝[<] x := by
    calc
      𝓝[I ∩ Set.Iio x] x = 𝓝[Set.Iio x] x := by
        apply nhdsWithin_eq_nhdsWithin hxIooab isOpen_Ioo
        ext z
        constructor
        · intro hz
          exact ⟨hz.1.2, hz.2⟩
        · intro hz
          exact ⟨⟨habI hz.2, hz.1⟩, hz.2⟩
      _ = 𝓝[<] x := rfl
  have hgleft : Filter.Tendsto g (𝓝[<] x) (𝓝 (g x)) := by
    simpa [ContinuousWithinAt, hfilterEq] using hgleftI
  have hlimitEq : sSup (g '' Set.Ioo a x) = g x :=
    tendsto_nhds_unique hleftLimit hgleft
  have hle : g x ≤ l x := by
    simpa [g, hlimitEq] using hsSup_le
  exact (not_le_of_gt hlt) hle

end Section25
end Chap05
