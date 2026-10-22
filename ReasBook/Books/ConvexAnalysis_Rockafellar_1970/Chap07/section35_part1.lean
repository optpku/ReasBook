/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section04_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section10_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section14_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

/-- A convex set that is open in the topology induced on its affine span. -/
abbrev IsRelativelyOpenConvex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Set E) : Prop :=
  Convex ℝ s ∧ IsOpen ((fun x : affineSpan ℝ s => (x : E)) ⁻¹' s)

/-- A real-valued function on `C × D` that is concave in the first variable on `C`
and convex in the second variable on `D`. -/
abbrev IsRealConcaveConvexOn {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (C : Set E) (D : Set F)
    (K : E → F → ℝ) : Prop :=
  (∀ y ∈ D, ConcaveOn ℝ C (fun x => K x y)) ∧ ∀ x ∈ C, ConvexOn ℝ D (K x)

/-- A finite real-valued concave-convex bifunction induces the canonical `EReal`-valued
Section 33 saddle predicate after coercion. -/
theorem IsRealConcaveConvexOn.toEReal
    {m n : ℕ}
    {C : Set (Fin m → ℝ)} {D : Set (Fin n → ℝ)}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → ℝ}
    (hK : IsRealConcaveConvexOn C D K) :
    IsConcaveConvexOn C D (fun u v => ((K u v : ℝ) : EReal)) := by
  constructor
  · intro v hv x y hx hy a b ha hb hab hxy
    have hReal :
        a * K x v + b * K y v ≤ K (a • x + b • y) v :=
      (hK.1 v hv).2 hx hy ha hb hab
    simpa only [← EReal.coe_mul, ← EReal.coe_add] using
      EReal.coe_le_coe_iff.mpr hReal
  · intro u hu x y hx hy a b ha hb hab hxy
    have hReal :
        K u (a • x + b • y) ≤ a * K u x + b * K u y :=
      (hK.2 u hu).2 hx hy ha hb hab
    simpa only [← EReal.coe_mul, ← EReal.coe_add] using
      EReal.coe_le_coe_iff.mpr hReal

-- Proof sketch: apply the finite-dimensional facts that convex and concave real-valued
-- functions are locally Lipschitz on relatively open convex domains, separately in each
-- variable, and combine the resulting local estimates on closed bounded subsets.
/-- Helper for Theorem 35.1: a relatively open convex set equals its Euclidean relative
interior. -/
lemma helperForTheorem_35_1_relativelyOpenConvex_eq_ri
    {k : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin k))}
    (hs : IsRelativelyOpenConvex s) :
    euclideanRelativeInterior k s = s := by
  -- Rewrite relative openness in the affine-span topology as equality with `intrinsicInterior`.
  have hIntrinsic : intrinsicInterior ℝ s = s := by
    ext x
    constructor
    · intro hx
      exact intrinsicInterior_subset (𝕜 := ℝ) (s := s) hx
    · intro hx
      refine (mem_intrinsicInterior).2 ?_
      let xA : affineSpan ℝ s := ⟨x, subset_affineSpan (k := ℝ) (s := s) hx⟩
      have hxA :
          xA ∈ ((fun y : affineSpan ℝ s => (y : EuclideanSpace ℝ (Fin k))) ⁻¹' s) := by
        simpa [xA] using hx
      have hxInterior :
          xA ∈ interior ((fun y : affineSpan ℝ s => (y : EuclideanSpace ℝ (Fin k))) ⁻¹' s) := by
        exact mem_interior_iff_mem_nhds.2 (hs.2.mem_nhds hxA)
      exact ⟨xA, hxInterior, rfl⟩
  -- Then convert the Euclidean relative interior to `intrinsicInterior`.
  calc
    euclideanRelativeInterior k s = intrinsicInterior ℝ s := by
      symm
      exact intrinsicInterior_eq_euclideanRelativeInterior (n := k) (C := s)
    _ = s := hIntrinsic

/-- Helper for Theorem 35.1: a convex real-valued function on a relatively open convex set is
continuous on that set. -/
lemma helperForTheorem_35_1_sliceContinuousOn_relativelyOpenConvex
    {k : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → ℝ}
    (hs : IsRelativelyOpenConvex s)
    (hf : ConvexOn ℝ s f) :
    ContinuousOn f s := by
  -- The Chapter 2 continuity theorem applies on relative interior, and the bridge lemma
  -- identifies that relative interior with the given relatively open convex set.
  rw [← helperForTheorem_35_1_relativelyOpenConvex_eq_ri (hs := hs)]
  exact convexOn_continuousOn_ri_via_coordinateSubspace (C := s) (g := f) hf

/-- Helper for Theorem 35.1: every affine coordinate model map between finite-dimensional
Euclidean spaces is globally Lipschitz. -/
lemma helperForTheorem_35_1_affineModelMap_lipschitz
    {k m : ℕ}
    (A : EuclideanSpace ℝ (Fin k) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m)) :
    ∃ L : NNReal, LipschitzWith L A := by
  let Alinear : EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
    A.linear.toContinuousLinearMap
  -- Control the affine map by its linear part, since translations cancel in pairwise differences.
  refine ⟨‖Alinear‖₊, LipschitzWith.of_dist_le_mul ?_⟩
  intro x y
  have hLinear :
      ‖Alinear x - Alinear y‖ ≤ (‖Alinear‖₊ : ℝ) * dist x y := by
    simpa [dist_eq_norm] using Alinear.lipschitz.norm_sub_le x y
  have hAffine :
      A x - A y = Alinear (x - y) := by
    simpa [Alinear, sub_eq_add_neg] using (AffineMap.linearMap_vsub A x y).symm
  simpa [dist_eq_norm, hAffine] using hLinear

/-- Helper for Theorem 35.1: an equi-Lipschitz estimate on the coordinate model pulls back along
one Lipschitz parameterization of the original set. -/
lemma helperForTheorem_35_1_coordinateModel_pullback_equiLipschitz
    {α β I : Type*} [PseudoMetricSpace α] [PseudoMetricSpace β]
    {S : Set α} {Smodel : Set β}
    {ψ : α → β} {f : I → α → ℝ} {g : I → β → ℝ}
    {L Kψ : NNReal}
    (hSmodel : Smodel = ψ '' S)
    (hψ : LipschitzWith Kψ ψ)
    (hg : ∀ i, LipschitzOnWith L (g i) Smodel)
    (hEq : ∀ i, Set.EqOn (fun x => g i (ψ x)) (f i) S) :
    ∀ i, LipschitzOnWith (L * Kψ) (f i) S := by
  intro i
  have hmaps : Set.MapsTo ψ S Smodel := by
    intro x hx
    rw [hSmodel]
    exact ⟨x, hx, rfl⟩
  have hcomp : LipschitzOnWith (L * Kψ) (g i ∘ ψ) S :=
    (hg i).comp hψ.lipschitzOnWith hmaps
  -- Replace the pulled-back model family with the original family on `S`.
  intro x hx y hy
  simpa [Function.comp, hEq i hx, hEq i hy] using hcomp hx hy

/-- Helper for Theorem 35.1: the relative-open form of Theorem 10.6 gives a uniform Lipschitz
constant on a closed bounded subset. -/
lemma helperForTheorem_35_1_familyEquiLipschitz_relativelyOpenConvex
    {k : ℕ} {I : Type*}
    {s : Set (EuclideanSpace ℝ (Fin k))}
    {f : I → EuclideanSpace ℝ (Fin k) → ℝ}
    (hs : IsRelativelyOpenConvex s)
    (hf : ∀ i, ConvexOn ℝ s (f i))
    (hpt : Function.PointwiseBoundedOn f s)
    {S : Set (EuclideanSpace ℝ (Fin k))}
    (hSclosed : IsClosed S) (hSbdd : Bornology.IsBounded S) (hSsub : S ⊆ s) :
    ∃ L : NNReal, ∀ i, LipschitzOnWith L (f i) S := by
  classical
  by_cases hsEmpty : s = ∅
  · have hSEmpty : S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      have hxEmpty : x ∈ (∅ : Set (EuclideanSpace ℝ (Fin k))) := by
        simpa [hsEmpty] using hSsub hx
      exact hxEmpty.elim
    subst hSEmpty
    -- The empty subset is Lipschitz for every family with constant `0`.
    refine ⟨0, ?_⟩
    intro i
    simp
  · have hsNonempty : s.Nonempty := Set.nonempty_iff_ne_empty.2 hsEmpty
    let m := Module.finrank ℝ (affineSpan ℝ s).direction
    obtain ⟨T, hT⟩ :=
      exists_affineEquiv_affineSpan_eq_coordinateSubspace k m s hsNonempty (by simp [m])
    have hspanT :
        (affineSpan ℝ (T '' s) : Set (EuclideanSpace ℝ (Fin k))) =
          coordinateSubspace k m := by
      have hspan' := affineSpan_image_affineEquiv (n := k) (C := s) (e := T)
      simpa [hspan'] using hT
    have hmn : m ≤ k := by
      have hle :
          Module.finrank ℝ (affineSpan ℝ s).direction ≤
            Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) :=
        Submodule.finrank_le (affineSpan ℝ s).direction
      simpa [m, finrank_euclideanSpace_fin] using hle
    let e := coordinateSubspace_affineEquiv (n := k) (m := m) hmn
    let C' : Set (EuclideanSpace ℝ (Fin k)) := T '' s
    let A : EuclideanSpace ℝ (Fin m) →ᵃ[ℝ] EuclideanSpace ℝ (Fin k) :=
      ((coordinateSubmodule k m).subtype.toAffineMap).comp e.toAffineMap
    let D : Set (EuclideanSpace ℝ (Fin m)) :=
      e.symm '' (Subtype.val ⁻¹' C')
    let g : I → EuclideanSpace ℝ (Fin m) → ℝ := fun i z => f i (T.symm (A z))
    have hpre : T.symm ⁻¹' s = C' := by
      ext x
      constructor
      · intro hx
        exact ⟨T.symm x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    have hconvC' : Convex ℝ C' := by
      -- Affine equivalences preserve convexity.
      simpa [C'] using hs.1.affine_image T.toAffineMap
    have hconvT : ∀ i, ConvexOn ℝ C' (fun x => f i (T.symm x)) := by
      intro i
      -- Rewrite the transformed domain as a pullback of `s`.
      simpa [hpre, C', Function.comp] using
        (ConvexOn.comp_affineMap (g := T.symm.toAffineMap) (s := s) (hf i))
    have hD : D = A ⁻¹' C' := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [A, C', AffineMap.comp_apply] using hy
      · intro hx
        refine ⟨e x, ?_, by simp⟩
        simpa [A, C', AffineMap.comp_apply] using hx
    have hconvDset : Convex ℝ D := by
      -- The coordinate model domain is an affine preimage of the convex image of `s`.
      simpa [D, hD] using hconvC'.affine_preimage A
    have hgconv : ∀ i, ConvexOn ℝ D (g i) := by
      intro i
      -- Compose the transported family with the coordinate-subspace embedding.
      simpa [g, D, hD, Function.comp, A] using
        (ConvexOn.comp_affineMap (g := A) (s := C') (hconvT i))
    have hspanD :
        (affineSpan ℝ D : Set (EuclideanSpace ℝ (Fin m))) = Set.univ := by
      simpa [D, C'] using
        (affineSpan_preimage_eq_univ (n := k) (m := m) hmn
          (C := C') hspanT)
    have hC'sub : C' ⊆ coordinateSubspace k m := by
      intro x hx
      have hx' :
          x ∈ (affineSpan ℝ C' : Set (EuclideanSpace ℝ (Fin k))) :=
        subset_affineSpan (k := ℝ) (s := C') hx
      simpa [C', hspanT] using hx'
    have hA_image : A '' D = C' := by
      have hA_image' :
          A '' (A ⁻¹' C') = C' :=
        A_image_eq_C' (e := e) (A := A) rfl hC'sub
      simpa [hD] using hA_image'
    have hri_s :
        euclideanRelativeInterior k s = s :=
      helperForTheorem_35_1_relativelyOpenConvex_eq_ri (hs := hs)
    have hri_C' :
        euclideanRelativeInterior k C' = C' := by
      calc
        euclideanRelativeInterior k C' = T '' euclideanRelativeInterior k s := by
          simpa [C'] using
            (euclideanRelativeInterior_image_affineEquiv (n := k) (C := s) (e := T))
        _ = T '' s := by rw [hri_s]
        _ = C' := rfl
    let e_m' : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
      EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m)
    let e_k' : EuclideanSpace ℝ (Fin k) ≃L[ℝ] (Fin k → ℝ) :=
      EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin k)
    let A0' : (Fin m → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
      Function.ExtendByZero.linearMap ℝ (Fin.castLE hmn)
    let A0 : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
      e_k'.symm.toLinearMap.comp (A0'.comp e_m'.toLinearMap)
    have hAeq : ∀ x, A x = A0 x := by
      intro x
      simp [A, A0, A0', AffineMap.comp_apply, e, coordinateSubspace_affineEquiv, e_m', e_k']
    have hA0 : A 0 = 0 := by
      simp [hAeq 0]
    let p' : (Fin k → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
      LinearMap.funLeft ℝ ℝ (Fin.castLE hmn)
    let p : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
      e_m'.symm.toLinearMap.comp (p'.comp e_k'.toLinearMap)
    have hleft0' : Function.LeftInverse p' A0' := by
      intro x
      ext i
      have hcomp :=
        Function.extend_comp (f := Fin.castLE hmn) (g := x) (e' := fun _ => (0 : ℝ))
          (hf := Fin.castLE_injective hmn)
      have hcomp' := congrArg (fun h => h i) hcomp
      simpa [A0', p', LinearMap.funLeft_apply] using hcomp'
    have hleft0 : Function.LeftInverse p A0 := by
      intro x
      apply e_m'.injective
      have hcomp : e_m' (p (A0 x)) = p' (A0' (e_m' x)) := by
        have h1 : e_m' (p (A0 x)) = p' (e_k' (A0 x)) := by
          simp [p, LinearMap.comp_apply]
        have h2 : e_k' (A0 x) = A0' (e_m' x) := by
          simp [A0, LinearMap.comp_apply]
        simpa [h2] using h1
      simpa [hcomp] using (hleft0' (e_m' x))
    have hleft : Function.LeftInverse p A := by
      intro x
      simpa [hAeq x] using hleft0 x
    have hA_right_on_C' : ∀ y ∈ C', A (p y) = y := by
      intro y hy
      have hyim : y ∈ A '' D := by
        simpa [hA_image] using hy
      rcases hyim with ⟨z, hz, rfl⟩
      rw [hleft z]
    have hri_eq :
        euclideanRelativeInterior k C' = A '' euclideanRelativeInterior m D := by
      have hri := ri_image_linearMap_eq (n := k) (m := m) (D := D) hconvDset A hA0
      simpa [hA_image] using hri
    have hri_D :
        euclideanRelativeInterior m D = D := by
      ext z
      constructor
      · intro hzri
        exact (euclideanRelativeInterior_subset_closure m D).1 hzri
      · intro hz
        have hAzC' : A z ∈ C' := by
          simpa [hD] using hz
        have hAzri : A z ∈ euclideanRelativeInterior k C' := by
          rw [hri_C']
          exact hAzC'
        rw [hri_eq] at hAzri
        rcases hAzri with ⟨w, hwri, hwA⟩
        have hwz : w = z := by
          calc
            w = p (A w) := by symm; exact hleft w
            _ = p (A z) := by rw [hwA]
            _ = z := hleft z
        simpa [hwz] using hwri
    have hDopen : IsOpen D := by
      rw [← hri_D, euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ m D hspanD]
      exact isOpen_interior
    have hgpt : Function.PointwiseBoundedOn g D := by
      intro z hz
      have hAzC' : A z ∈ C' := by
        simpa [hD] using hz
      have hzs : T.symm (A z) ∈ s := by
        have hzpre : A z ∈ T.symm ⁻¹' s := by
          simpa [hpre] using hAzC'
        exact hzpre
      -- Evaluate the original pointwise-bounded family at the corresponding point of `s`.
      simpa [g] using hpt (T.symm (A z)) hzs
    let ψAff : EuclideanSpace ℝ (Fin k) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m) :=
      p.toAffineMap.comp T.toAffineMap
    let ψ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) := ψAff
    have hψLip : ∃ Kψ : NNReal, LipschitzWith Kψ ψ := by
      simpa [ψ, ψAff] using helperForTheorem_35_1_affineModelMap_lipschitz ψAff
    rcases hψLip with ⟨Kψ, hψLip⟩
    let Smodel : Set (EuclideanSpace ℝ (Fin m)) := ψ '' S
    have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
    have hSmodelComp : IsCompact Smodel := by
      simpa [Smodel] using hScomp.image hψLip.continuous
    have hSmodelClosed : IsClosed Smodel := hSmodelComp.isClosed
    have hSmodelBdd : Bornology.IsBounded Smodel := hSmodelComp.isBounded
    have hSmodelSub : Smodel ⊆ D := by
      intro z hz
      rcases hz with ⟨x, hxS, rfl⟩
      have hxs : x ∈ s := hSsub hxS
      have hTxC' : T x ∈ C' := ⟨x, hxs, rfl⟩
      have hAψ : A (ψ x) = T x := by
        simpa [ψ, ψAff] using hA_right_on_C' (T x) hTxC'
      rw [hD]
      simpa [hAψ] using hTxC'
    have hModelEqui :
        Function.EquiLipschitzRelativeTo g Smodel := by
      exact
        (convexOn_family_uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_pointwiseBoundedOn
          (n := m) (I := I) (C := D) hDopen hconvDset g hgconv hgpt
          (S := Smodel) hSmodelClosed hSmodelBdd hSmodelSub).2
    rcases hModelEqui with ⟨L, hL⟩
    have hEq : ∀ i, Set.EqOn (fun x => g i (ψ x)) (f i) S := by
      intro i x hx
      have hxs : x ∈ s := hSsub hx
      have hTxC' : T x ∈ C' := ⟨x, hxs, rfl⟩
      have hAψ : A (ψ x) = T x := by
        simpa [ψ, ψAff] using hA_right_on_C' (T x) hTxC'
      -- Route correction: instead of transporting a two-sided metric equivalence, we only rewrite
      -- the modeled evaluation back to `x` using the right-inverse identity on `C'`.
      calc
        g i (ψ x) = f i (T.symm (T x)) := by
          simp [g, hAψ]
        _ = f i x := by rw [T.symm_apply_apply]
    refine ⟨L * Kψ, ?_⟩
    -- Pull the model-side Lipschitz constant back to the original closed bounded set.
    exact
      helperForTheorem_35_1_coordinateModel_pullback_equiLipschitz
        (Smodel := Smodel) (hSmodel := rfl) hψLip hL hEq

/-- Helper for Theorem 35.1: every point of a relatively open convex set admits a closed bounded
neighborhood contained in the set. -/
lemma helperForTheorem_35_1_existsClosedBoundedNeighborhood_subset_relativelyOpenConvex
    {k : ℕ}
    {s : Set (EuclideanSpace ℝ (Fin k))}
    (hs : IsRelativelyOpenConvex s)
    {x : EuclideanSpace ℝ (Fin k)}
    (hx : x ∈ s) :
    ∃ T : Set (EuclideanSpace ℝ (Fin k)),
      x ∈ T ∧ T ⊆ s ∧ IsClosed T ∧ Bornology.IsBounded T ∧ T ∈ nhdsWithin x s := by
  -- Move `x` into relative interior so the Chapter 2 ball lemma applies.
  have hxri : x ∈ euclideanRelativeInterior k s := by
    rw [helperForTheorem_35_1_relativelyOpenConvex_eq_ri (hs := hs)]
    exact hx
  rcases euclideanRelativeInterior_ball_subset k s hxri with ⟨ε, hεpos, hεsub⟩
  refine
    ⟨Metric.closedBall x (ε / 2) ∩ (affineSpan ℝ s : Set (EuclideanSpace ℝ (Fin k))), ?_, ?_,
      ?_, ?_, ?_⟩
  · -- The center lies in the closed ball and in the affine span.
    constructor
    · simpa [Metric.mem_closedBall, dist_self] using (show (0 : ℝ) ≤ ε / 2 by linarith)
    · exact subset_affineSpan (k := ℝ) (s := s) hx
  · -- The chosen closed ball still stays inside `s` after intersecting the affine span.
    intro y hy
    have hy_ball : y ∈ Metric.closedBall x ε :=
      Metric.closedBall_subset_closedBall (by linarith) hy.1
    have hy_image : y ∈ (fun z => x + z) '' (ε • euclideanUnitBall k) := by
      rw [translate_smul_unitBall_eq_closedBall k x ε hεpos]
      exact hy_ball
    have hy_ri : y ∈ euclideanRelativeInterior k s := hεsub ⟨hy_image, hy.2⟩
    rw [helperForTheorem_35_1_relativelyOpenConvex_eq_ri (hs := hs)] at hy_ri
    exact hy_ri
  · -- Closedness comes from the closed ball and the affine span.
    exact
      Metric.isClosed_closedBall.inter
        (AffineSubspace.closed_of_finiteDimensional (affineSpan ℝ s))
  · -- Boundedness follows because the neighborhood sits inside a closed ball.
    exact
      Bornology.IsBounded.subset (t := Metric.closedBall x (ε / 2)) Metric.isBounded_closedBall
        (by
          intro y hy
          exact hy.1)
  · -- A small ambient ball still lands in the closed ball, and points of `s` already lie in the affine span.
    rw [Metric.mem_nhdsWithin_iff]
    refine ⟨ε / 2, by linarith, ?_⟩
    intro y hy
    constructor
    · have hy_dist : dist y x < ε / 2 := by
        simpa [Metric.mem_ball, dist_comm] using hy.1
      simpa [Metric.mem_closedBall, dist_comm] using le_of_lt hy_dist
    · exact subset_affineSpan (k := ℝ) (s := s) hy.2

/-- Helper for Theorem 35.1: a continuous real-valued function has bounded range on a compact
set, written over the corresponding subtype. -/
lemma helperForTheorem_35_1_boundedRange_of_continuousOn_compact
    {α : Type*} [TopologicalSpace α]
    {s : Set α} (hs : IsCompact s) {g : α → ℝ} (hg : ContinuousOn g s) :
    Bornology.IsBounded (Set.range fun x : s => g x.1) := by
  -- Rewrite the subtype range as an ordinary image of `s`.
  have hEq : (Set.range fun x : s => g x.1) = g '' s := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x.1, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  -- Compact images in `ℝ` are bounded.
  simpa [hEq] using (hs.image_of_continuousOn hg).isBounded

/-- Helper for Theorem 35.1: continuity of the slice families over compact projections yields the
pointwise boundedness needed for the one-variable equi-Lipschitz estimates. -/
lemma helperForTheorem_35_1_projectionFamilies_pointwiseBounded
    {m n : ℕ}
    {X : Set (EuclideanSpace ℝ (Fin m))} {Y : Set (EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hXcomp : IsCompact X) (hYcomp : IsCompact Y)
    (hcontX : ∀ y ∈ Y, ContinuousOn (fun x => K x y) X)
    (hcontY : ∀ x ∈ X, ContinuousOn (K x) Y) :
    (∀ y ∈ Y, Bornology.IsBounded (Set.range fun x : X => K x.1 y)) ∧
      (∀ x ∈ X, Bornology.IsBounded (Set.range fun y : Y => K x y.1)) := by
  constructor
  · intro y hy
    -- Fixing `y`, compactness of `X` bounds the corresponding first-variable slice.
    exact
      helperForTheorem_35_1_boundedRange_of_continuousOn_compact
        (hs := hXcomp) (hg := hcontX y hy)
  · intro x hx
    -- Fixing `x`, compactness of `Y` bounds the corresponding second-variable slice.
    exact
      helperForTheorem_35_1_boundedRange_of_continuousOn_compact
        (hs := hYcomp) (hg := hcontY x hx)

/-- Helper for Theorem 35.1: coordinatewise Lipschitz estimates assemble into a product
Lipschitz estimate on `X × Y`. -/
lemma helperForTheorem_35_1_productLipschitz_of_coordinatewiseBounds
    {m n : ℕ}
    {X : Set (EuclideanSpace ℝ (Fin m))} {Y : Set (EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    {Lx Ly : NNReal}
    (hX : ∀ y ∈ Y, LipschitzOnWith Lx (fun x => K x y) X)
    (hY : ∀ x ∈ X, LipschitzOnWith Ly (K x) Y) :
    LipschitzOnWith (Lx + Ly) (Function.uncurry K) (X ×ˢ Y) := by
  -- Compare `(x,y)` to `(x',y')` by changing one coordinate at a time.
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro p hp q hq
  rcases hp with ⟨hpX, hpY⟩
  rcases hq with ⟨hqX, hqY⟩
  have hx :
      dist (K p.1 p.2) (K q.1 p.2) ≤ (Lx : ℝ) * dist p.1 q.1 :=
    (hX p.2 hpY).dist_le_mul p.1 hpX q.1 hqX
  have hy :
      dist (K q.1 p.2) (K q.1 q.2) ≤ (Ly : ℝ) * dist p.2 q.2 :=
    (hY q.1 hqX).dist_le_mul p.2 hpY q.2 hqY
  have hx' : (Lx : ℝ) * dist p.1 q.1 ≤ (Lx : ℝ) * dist p q := by
    gcongr
    simpa [Prod.dist_eq] using (le_max_left (dist p.1 q.1) (dist p.2 q.2))
  have hy' : (Ly : ℝ) * dist p.2 q.2 ≤ (Ly : ℝ) * dist p q := by
    gcongr
    simpa [Prod.dist_eq] using (le_max_right (dist p.1 q.1) (dist p.2 q.2))
  calc
    dist (Function.uncurry K p) (Function.uncurry K q)
        ≤ dist (K p.1 p.2) (K q.1 p.2) + dist (K q.1 p.2) (K q.1 q.2) := by
          simpa [Function.uncurry] using dist_triangle (K p.1 p.2) (K q.1 p.2) (K q.1 q.2)
    _ ≤ (Lx : ℝ) * dist p.1 q.1 + (Ly : ℝ) * dist p.2 q.2 := add_le_add hx hy
    _ ≤ (Lx : ℝ) * dist p q + (Ly : ℝ) * dist p q := add_le_add hx' hy'
    _ = ((Lx + Ly : NNReal) : ℝ) * dist p q := by
      rw [← add_mul]
      norm_num

/-- Theorem 35.1: if `C ⊆ ℝ^m` and `D ⊆ ℝ^n` are relatively open convex sets and
`K` is a finite concave-convex function on `C × D`, then `K` is continuous relative to
`C × D`; in fact, on every closed bounded subset of `C × D`, `K` is Lipschitzian. -/
theorem section35_theorem35_1
    {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hC : IsRelativelyOpenConvex C) (hD : IsRelativelyOpenConvex D)
    (hK : IsRealConcaveConvexOn C D K) :
    ContinuousOn (Function.uncurry K) (C ×ˢ D) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
        S ⊆ C ×ˢ D → IsClosed S → Bornology.IsBounded S →
          ∃ L : NNReal, LipschitzOnWith L (Function.uncurry K) S := by
  classical
  -- First establish the closed-bounded Lipschitz estimate, since the continuity argument will
  -- use it on product neighborhoods.
  have hLipClosedBounded :
      ∀ S : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
        S ⊆ C ×ˢ D → IsClosed S → Bornology.IsBounded S →
          ∃ L : NNReal, LipschitzOnWith L (Function.uncurry K) S := by
    intro S hSsub hSclosed hSbdd
    set X : Set (EuclideanSpace ℝ (Fin m)) := Prod.fst '' S
    set Y : Set (EuclideanSpace ℝ (Fin n)) := Prod.snd '' S
    -- Closed bounded subsets of the product are compact, so their projections are compact too.
    have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
    have hXcomp : IsCompact X := by
      simpa [X] using hScomp.image continuous_fst
    have hYcomp : IsCompact Y := by
      simpa [Y] using hScomp.image continuous_snd
    have hXsub : X ⊆ C := by
      intro x hx
      rcases hx with ⟨p, hpS, rfl⟩
      exact (hSsub hpS).1
    have hYsub : Y ⊆ D := by
      intro y hy
      rcases hy with ⟨p, hpS, rfl⟩
      exact (hSsub hpS).2
    have hXclosed : IsClosed X := hXcomp.isClosed
    have hYclosed : IsClosed Y := hYcomp.isClosed
    have hXbdd : Bornology.IsBounded X := hXcomp.isBounded
    have hYbdd : Bornology.IsBounded Y := hYcomp.isBounded
    -- Route correction: the first-variable slices are concave, so we pass to their negatives to
    -- match the convex family theorem and then convert the Lipschitz estimate back.
    let firstFamily : Y → EuclideanSpace ℝ (Fin m) → ℝ := fun y x => -K x y.1
    let secondFamily : X → EuclideanSpace ℝ (Fin n) → ℝ := fun x y => K x.1 y
    have hFirstConv : ∀ y, ConvexOn ℝ C (firstFamily y) := by
      intro y
      exact neg_convexOn_iff.mpr (hK.1 y.1 (hYsub y.2))
    have hSecondConv : ∀ x, ConvexOn ℝ D (secondFamily x) := by
      intro x
      simpa [secondFamily] using hK.2 x.1 (hXsub x.2)
    have hFirstPointwise : Function.PointwiseBoundedOn firstFamily C := by
      intro x hxC
      have hcontSlice :
          ContinuousOn (fun y => K x y) D :=
        helperForTheorem_35_1_sliceContinuousOn_relativelyOpenConvex
          (hs := hD) (hf := hK.2 x hxC)
      have hcontY : ContinuousOn (fun y => K x y) Y := hcontSlice.mono hYsub
      have hbdd :
          Bornology.IsBounded (Set.range fun y : Y => K x y.1) :=
        helperForTheorem_35_1_boundedRange_of_continuousOn_compact
          (hs := hYcomp) (hg := hcontY)
      have hEq :
          (Set.range fun y : Y => -K x y.1) =
            Neg.neg '' (Set.range fun y : Y => K x y.1) := by
        ext z
        constructor
        · rintro ⟨y, rfl⟩
          exact ⟨K x y.1, ⟨y, rfl⟩, rfl⟩
        · rintro ⟨z, ⟨y, rfl⟩, rfl⟩
          exact ⟨y, rfl⟩
      simpa [firstFamily, hEq] using hbdd.neg
    have hSecondPointwise : Function.PointwiseBoundedOn secondFamily D := by
      intro y hyD
      have hconcSlice : ConcaveOn ℝ C (fun x => K x y) := hK.1 y hyD
      have hconvNeg : ConvexOn ℝ C (fun x => -K x y) := neg_convexOn_iff.mpr hconcSlice
      have hcontNeg :
          ContinuousOn (fun x => -K x y) C :=
        helperForTheorem_35_1_sliceContinuousOn_relativelyOpenConvex
          (hs := hC) (hf := hconvNeg)
      have hcontX : ContinuousOn (fun x => K x y) X := by
        simpa using hcontNeg.neg.mono hXsub
      exact
        helperForTheorem_35_1_boundedRange_of_continuousOn_compact
          (hs := hXcomp) (hg := hcontX)
    have hFirstLip :
        ∃ L : NNReal, ∀ y, LipschitzOnWith L (firstFamily y) X :=
      helperForTheorem_35_1_familyEquiLipschitz_relativelyOpenConvex
        (hs := hC) (hf := hFirstConv) (hpt := hFirstPointwise)
        (hSclosed := hXclosed) (hSbdd := hXbdd) (hSsub := hXsub)
    have hSecondLip :
        ∃ L : NNReal, ∀ x, LipschitzOnWith L (secondFamily x) Y :=
      helperForTheorem_35_1_familyEquiLipschitz_relativelyOpenConvex
        (hs := hD) (hf := hSecondConv) (hpt := hSecondPointwise)
        (hSclosed := hYclosed) (hSbdd := hYbdd) (hSsub := hYsub)
    rcases hFirstLip with ⟨Lx, hLx⟩
    rcases hSecondLip with ⟨Ly, hLy⟩
    have hFirstLipOriginal :
        ∀ y ∈ Y, LipschitzOnWith Lx (fun x => K x y) X := by
      intro y hy
      refine LipschitzOnWith.of_dist_le_mul ?_
      intro x hx x' hx'
      simpa [firstFamily] using (hLx ⟨y, hy⟩).dist_le_mul x hx x' hx'
    have hSecondLipOriginal :
        ∀ x ∈ X, LipschitzOnWith Ly (fun y => K x y) Y := by
      intro x hx
      simpa [secondFamily] using hLy ⟨x, hx⟩
    have hProdLip :
        LipschitzOnWith (Lx + Ly) (Function.uncurry K) (X ×ˢ Y) :=
      helperForTheorem_35_1_productLipschitz_of_coordinatewiseBounds
        (hX := hFirstLipOriginal) (hY := hSecondLipOriginal)
    have hSXY : S ⊆ X ×ˢ Y := by
      intro p hpS
      refine ⟨?_, ?_⟩
      · exact ⟨p, hpS, rfl⟩
      · exact ⟨p, hpS, rfl⟩
    exact ⟨Lx + Ly, hProdLip.mono hSXY⟩
  refine ⟨?_, hLipClosedBounded⟩
  intro p hp
  rcases p with ⟨x, y⟩
  -- Build closed bounded neighborhoods in each factor and apply the Lipschitz estimate there.
  rcases
      helperForTheorem_35_1_existsClosedBoundedNeighborhood_subset_relativelyOpenConvex
        (hs := hC) hp.1 with
    ⟨TC, hxTC, hTCsub, hTCclosed, hTCbdd, hTCnhds⟩
  rcases
      helperForTheorem_35_1_existsClosedBoundedNeighborhood_subset_relativelyOpenConvex
        (hs := hD) hp.2 with
    ⟨TD, hyTD, hTDsub, hTDclosed, hTDbdd, hTDnhds⟩
  have hProdSub : TC ×ˢ TD ⊆ C ×ˢ D := by
    intro q hq
    exact ⟨hTCsub hq.1, hTDsub hq.2⟩
  have hProdClosed : IsClosed (TC ×ˢ TD) := hTCclosed.prod hTDclosed
  have hProdBdd : Bornology.IsBounded (TC ×ˢ TD) := hTCbdd.prod hTDbdd
  rcases hLipClosedBounded (TC ×ˢ TD) hProdSub hProdClosed hProdBdd with ⟨L, hL⟩
  have hContProd : ContinuousOn (Function.uncurry K) (TC ×ˢ TD) := hL.continuousOn
  have hpProd : (x, y) ∈ TC ×ˢ TD := ⟨hxTC, hyTD⟩
  have hProdNhds : TC ×ˢ TD ∈ nhdsWithin (x, y) (C ×ˢ D) := by
    simpa [nhdsWithin_prod_eq] using Filter.prod_mem_prod hTCnhds hTDnhds
  -- Continuity on a neighborhood within `C × D` upgrades to continuity relative to `C × D`.
  exact (hContProd (x, y) hpProd).mono_left (nhdsWithin_le_of_mem hProdNhds)

-- Proof sketch: repeat the coordinate-model reduction from the Theorem 35.1 helper, but now
-- transport the subset witness through the affine chart and apply the subset-witness form of
-- Theorem 10.6 on the open model domain.
/-- Helper for Theorem 35.2: the subset-witness form of Theorem 10.6 extends from open convex
domains to relatively open convex domains. -/
lemma helperForTheorem_35_2_relativelyOpenConvex_existsSubset_uniformlyBounded_and_equiLipschitz
    {k : ℕ} {I : Type*}
    {s : Set (EuclideanSpace ℝ (Fin k))}
    {f : I → EuclideanSpace ℝ (Fin k) → ℝ}
    (hs : IsRelativelyOpenConvex s)
    (hf : ∀ i, ConvexOn ℝ s (f i))
    {s' : Set (EuclideanSpace ℝ (Fin k))} (hs'sub : s' ⊆ s)
    (hs'hull : s ⊆ convexHull ℝ (closure s'))
    (hs'bdAbove : ∀ x ∈ s', BddAbove (Set.range fun i : I => f i x))
    (hexists_bddBelow : ∃ x ∈ s, BddBelow (Set.range fun i : I => f i x))
    {S : Set (EuclideanSpace ℝ (Fin k))}
    (hSclosed : IsClosed S) (hSbdd : Bornology.IsBounded S) (hSsub : S ⊆ s) :
    Function.UniformlyBoundedOn f S ∧ Function.EquiLipschitzRelativeTo f S := by
  classical
  by_cases hsEmpty : s = ∅
  · have hSEmpty : S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.2
      intro x hx
      have hxEmpty : x ∈ (∅ : Set (EuclideanSpace ℝ (Fin k))) := by
        simpa [hsEmpty] using hSsub hx
      exact hxEmpty.elim
    subst hSEmpty
    -- On the empty set, both conclusions are immediate with the zero bound and zero Lipschitz constant.
    refine ⟨?_, ?_⟩
    · refine ⟨0, 0, ?_⟩
      intro i x hx
      exact (False.elim (by simpa using hx))
    · refine ⟨0, ?_⟩
      intro i
      simp
  · have hsNonempty : s.Nonempty := Set.nonempty_iff_ne_empty.2 hsEmpty
    let m := Module.finrank ℝ (affineSpan ℝ s).direction
    obtain ⟨T, hT⟩ :=
      exists_affineEquiv_affineSpan_eq_coordinateSubspace k m s hsNonempty (by simp [m])
    have hspanT :
        (affineSpan ℝ (T '' s) : Set (EuclideanSpace ℝ (Fin k))) =
          coordinateSubspace k m := by
      have hspan' := affineSpan_image_affineEquiv (n := k) (C := s) (e := T)
      simpa [hspan'] using hT
    have hmn : m ≤ k := by
      have hle :
          Module.finrank ℝ (affineSpan ℝ s).direction ≤
            Module.finrank ℝ (EuclideanSpace ℝ (Fin k)) :=
        Submodule.finrank_le (affineSpan ℝ s).direction
      simpa [m, finrank_euclideanSpace_fin] using hle
    let e := coordinateSubspace_affineEquiv (n := k) (m := m) hmn
    let C0 : Set (EuclideanSpace ℝ (Fin k)) := T '' s
    let A : EuclideanSpace ℝ (Fin m) →ᵃ[ℝ] EuclideanSpace ℝ (Fin k) :=
      ((coordinateSubmodule k m).subtype.toAffineMap).comp e.toAffineMap
    let D0 : Set (EuclideanSpace ℝ (Fin m)) :=
      e.symm '' (Subtype.val ⁻¹' C0)
    let g : I → EuclideanSpace ℝ (Fin m) → ℝ := fun i z => f i (T.symm (A z))
    have hpre : T.symm ⁻¹' s = C0 := by
      ext x
      constructor
      · intro hx
        exact ⟨T.symm x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        simpa using hy
    have hconvC0 : Convex ℝ C0 := by
      -- Affine equivalences preserve convexity.
      simpa [C0] using hs.1.affine_image T.toAffineMap
    have hconvT : ∀ i, ConvexOn ℝ C0 (fun x => f i (T.symm x)) := by
      intro i
      -- Rewrite the transported domain as a pullback of `s`.
      simpa [hpre, C0, Function.comp] using
        (ConvexOn.comp_affineMap (g := T.symm.toAffineMap) (s := s) (hf i))
    have hD0 : D0 = A ⁻¹' C0 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [A, C0, AffineMap.comp_apply] using hy
      · intro hx
        refine ⟨e x, ?_, by simp⟩
        simpa [A, C0, AffineMap.comp_apply] using hx
    have hconvD0 : Convex ℝ D0 := by
      -- The coordinate model domain is an affine preimage of the convex image of `s`.
      simpa [D0, hD0] using hconvC0.affine_preimage A
    have hgconv : ∀ i, ConvexOn ℝ D0 (g i) := by
      intro i
      -- Compose the transported family with the coordinate-subspace embedding.
      simpa [g, D0, hD0, Function.comp, A] using
        (ConvexOn.comp_affineMap (g := A) (s := C0) (hconvT i))
    have hspanD0 :
        (affineSpan ℝ D0 : Set (EuclideanSpace ℝ (Fin m))) = Set.univ := by
      simpa [D0, C0] using
        (affineSpan_preimage_eq_univ (n := k) (m := m) hmn
          (C := C0) hspanT)
    have hC0sub : C0 ⊆ coordinateSubspace k m := by
      intro x hx
      have hx' :
          x ∈ (affineSpan ℝ C0 : Set (EuclideanSpace ℝ (Fin k))) :=
        subset_affineSpan (k := ℝ) (s := C0) hx
      simpa [C0, hspanT] using hx'
    have hA_image : A '' D0 = C0 := by
      have hA_image' :
          A '' (A ⁻¹' C0) = C0 :=
        A_image_eq_C' (e := e) (A := A) rfl hC0sub
      simpa [hD0] using hA_image'
    have hri_s :
        euclideanRelativeInterior k s = s :=
      helperForTheorem_35_1_relativelyOpenConvex_eq_ri (hs := hs)
    have hri_C0 :
        euclideanRelativeInterior k C0 = C0 := by
      calc
        euclideanRelativeInterior k C0 = T '' euclideanRelativeInterior k s := by
          simpa [C0] using
            (euclideanRelativeInterior_image_affineEquiv (n := k) (C := s) (e := T))
        _ = T '' s := by rw [hri_s]
        _ = C0 := rfl
    let e_m' : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
      EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin m)
    let e_k' : EuclideanSpace ℝ (Fin k) ≃L[ℝ] (Fin k → ℝ) :=
      EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin k)
    let A0' : (Fin m → ℝ) →ₗ[ℝ] (Fin k → ℝ) :=
      Function.ExtendByZero.linearMap ℝ (Fin.castLE hmn)
    let A0 : EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin k) :=
      e_k'.symm.toLinearMap.comp (A0'.comp e_m'.toLinearMap)
    have hAeq : ∀ x, A x = A0 x := by
      intro x
      simp [A, A0, A0', AffineMap.comp_apply, e, coordinateSubspace_affineEquiv, e_m', e_k']
    have hA0 : A 0 = 0 := by
      simp [hAeq 0]
    let p' : (Fin k → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
      LinearMap.funLeft ℝ ℝ (Fin.castLE hmn)
    let p : EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
      e_m'.symm.toLinearMap.comp (p'.comp e_k'.toLinearMap)
    have hleft0' : Function.LeftInverse p' A0' := by
      intro x
      ext i
      have hcomp :=
        Function.extend_comp (f := Fin.castLE hmn) (g := x) (e' := fun _ => (0 : ℝ))
          (hf := Fin.castLE_injective hmn)
      have hcomp' := congrArg (fun h => h i) hcomp
      simpa [A0', p', LinearMap.funLeft_apply] using hcomp'
    have hleft0 : Function.LeftInverse p A0 := by
      intro x
      apply e_m'.injective
      have hcomp : e_m' (p (A0 x)) = p' (A0' (e_m' x)) := by
        have h1 : e_m' (p (A0 x)) = p' (e_k' (A0 x)) := by
          simp [p, LinearMap.comp_apply]
        have h2 : e_k' (A0 x) = A0' (e_m' x) := by
          simp [A0, LinearMap.comp_apply]
        simpa [h2] using h1
      simpa [hcomp] using (hleft0' (e_m' x))
    have hleft : Function.LeftInverse p A := by
      intro x
      simpa [hAeq x] using hleft0 x
    have hA_right_on_C0 : ∀ y ∈ C0, A (p y) = y := by
      intro y hy
      have hyim : y ∈ A '' D0 := by
        simpa [hA_image] using hy
      rcases hyim with ⟨z, hz, rfl⟩
      rw [hleft z]
    have hri_eq :
        euclideanRelativeInterior k C0 = A '' euclideanRelativeInterior m D0 := by
      have hri := ri_image_linearMap_eq (n := k) (m := m) (D := D0) hconvD0 A hA0
      simpa [hA_image] using hri
    have hri_D0 :
        euclideanRelativeInterior m D0 = D0 := by
      ext z
      constructor
      · intro hzri
        exact (euclideanRelativeInterior_subset_closure m D0).1 hzri
      · intro hz
        have hAzC0 : A z ∈ C0 := by
          simpa [hD0] using hz
        have hAzri : A z ∈ euclideanRelativeInterior k C0 := by
          rw [hri_C0]
          exact hAzC0
        rw [hri_eq] at hAzri
        rcases hAzri with ⟨w, hwri, hwA⟩
        have hwz : w = z := by
          calc
            w = p (A w) := by symm; exact hleft w
            _ = p (A z) := by rw [hwA]
            _ = z := hleft z
        simpa [hwz] using hwri
    have hD0open : IsOpen D0 := by
      rw [← hri_D0, euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ m D0 hspanD0]
      exact isOpen_interior
    let ψAff : EuclideanSpace ℝ (Fin k) →ᵃ[ℝ] EuclideanSpace ℝ (Fin m) :=
      p.toAffineMap.comp T.toAffineMap
    let ψ : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m) := ψAff
    have hψLip : ∃ Kψ : NNReal, LipschitzWith Kψ ψ := by
      simpa [ψ, ψAff] using helperForTheorem_35_1_affineModelMap_lipschitz ψAff
    rcases hψLip with ⟨Kψ, hψLip⟩
    have hψ_image : ψ '' s = D0 := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hTxC0 : T x ∈ C0 := ⟨x, hx, rfl⟩
        have hAψ : A (ψ x) = T x := by
          simpa [ψ, ψAff] using hA_right_on_C0 (T x) hTxC0
        rw [hD0]
        simpa [hAψ] using hTxC0
      · intro hz
        have hAzC0 : A z ∈ C0 := by
          simpa [hD0] using hz
        rcases hAzC0 with ⟨x, hx, hTx⟩
        refine ⟨x, hx, ?_⟩
        calc
          ψ x = p (T x) := by rfl
          _ = p (A z) := by rw [hTx]
          _ = z := hleft z
    let sModel : Set (EuclideanSpace ℝ (Fin m)) := ψ '' s'
    have hsModelSub : sModel ⊆ D0 := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have hxs : x ∈ s := hs'sub hx
      rw [← hψ_image]
      exact ⟨x, hxs, rfl⟩
    have hC0_witnessHull : C0 ⊆ convexHull ℝ (closure (T '' s')) := by
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hxHull : x ∈ convexHull ℝ (closure s') := hs'hull hx
      have hyImage : T x ∈ T '' convexHull ℝ (closure s') := ⟨x, hxHull, rfl⟩
      have hTconv :
          T '' convexHull ℝ (closure s') = convexHull ℝ (T '' closure s') := by
        simpa using (AffineMap.image_convexHull (f := T.toAffineMap) (s := closure s'))
      have hyHull : T x ∈ convexHull ℝ (T '' closure s') := by
        simpa [hTconv] using hyImage
      have hTclosure : T '' closure s' ⊆ closure (T '' s') := by
        exact image_closure_subset_closure_image T.toAffineMap.continuous_of_finiteDimensional
      exact
        (convexHull_min
          (hTclosure.trans (subset_convexHull ℝ (closure (T '' s'))))
          (convex_convexHull ℝ (closure (T '' s')))) hyHull
    have hD0Hull : D0 ⊆ convexHull ℝ (closure sModel) := by
      intro z hz
      have hAzC0 : A z ∈ C0 := by
        simpa [hD0] using hz
      have hAzHull : A z ∈ convexHull ℝ (closure (T '' s')) := hC0_witnessHull hAzC0
      have hzImage : z ∈ p '' convexHull ℝ (closure (T '' s')) := by
        exact ⟨A z, hAzHull, hleft z⟩
      have hpconv :
          p '' convexHull ℝ (closure (T '' s')) =
            convexHull ℝ (p '' closure (T '' s')) := by
        simpa using (LinearMap.image_convexHull (f := p) (s := closure (T '' s')))
      have hzHull : z ∈ convexHull ℝ (p '' closure (T '' s')) := by
        simpa [hpconv] using hzImage
      have hpclosure : p '' closure (T '' s') ⊆ closure (p '' (T '' s')) := by
        exact image_closure_subset_closure_image p.continuous_of_finiteDimensional
      have hpimage : p '' (T '' s') = sModel := by
        ext w
        constructor
        · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
          exact ⟨x, hx, rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨T x, ⟨x, hx, rfl⟩, rfl⟩
      exact
        (convexHull_min
          (by
            have hsub :
                p '' closure (T '' s') ⊆ convexHull ℝ (closure (p '' (T '' s'))) :=
              hpclosure.trans (subset_convexHull ℝ (closure (p '' (T '' s'))))
            simpa [hpimage] using hsub)
          (convex_convexHull ℝ (closure sModel))) hzHull
    have hsModelBdAbove : ∀ z ∈ sModel, BddAbove (Set.range fun i : I => g i z) := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have hTxC0 : T x ∈ C0 := ⟨x, hs'sub hx, rfl⟩
      have hAψ : A (ψ x) = T x := by
        simpa [ψ, ψAff] using hA_right_on_C0 (T x) hTxC0
      simpa [sModel, g, hAψ] using hs'bdAbove x hx
    have hexists_model_bddBelow : ∃ z ∈ D0, BddBelow (Set.range fun i : I => g i z) := by
      rcases hexists_bddBelow with ⟨x, hx, hbdd⟩
      refine ⟨ψ x, ?_, ?_⟩
      · rw [← hψ_image]
        exact ⟨x, hx, rfl⟩
      · have hTxC0 : T x ∈ C0 := ⟨x, hx, rfl⟩
        have hAψ : A (ψ x) = T x := by
          simpa [ψ, ψAff] using hA_right_on_C0 (T x) hTxC0
        simpa [g, hAψ] using hbdd
    let Smodel : Set (EuclideanSpace ℝ (Fin m)) := ψ '' S
    have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
    have hSmodelComp : IsCompact Smodel := by
      simpa [Smodel] using hScomp.image hψLip.continuous
    have hSmodelClosed : IsClosed Smodel := hSmodelComp.isClosed
    have hSmodelBdd : Bornology.IsBounded Smodel := hSmodelComp.isBounded
    have hSmodelSub : Smodel ⊆ D0 := by
      intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      have hxs : x ∈ s := hSsub hx
      rw [← hψ_image]
      exact ⟨x, hxs, rfl⟩
    have hModel :
        Function.UniformlyBoundedOn g Smodel ∧ Function.EquiLipschitzRelativeTo g Smodel := by
      exact
        convexOn_family_uniformlyBoundedOn_and_equiLipschitzRelativeTo_of_exists_subset
          (n := m) (I := I) (C := D0) hD0open hconvD0 g hgconv (C' := sModel) hsModelSub
          hD0Hull hsModelBdAbove hexists_model_bddBelow hSmodelClosed hSmodelBdd hSmodelSub
    rcases hModel with ⟨hModelUbdd, hModelEqui⟩
    have hEq : ∀ i, Set.EqOn (fun x => g i (ψ x)) (f i) S := by
      intro i x hx
      have hxs : x ∈ s := hSsub hx
      have hTxC0 : T x ∈ C0 := ⟨x, hxs, rfl⟩
      have hAψ : A (ψ x) = T x := by
        simpa [ψ, ψAff] using hA_right_on_C0 (T x) hTxC0
      -- Route correction: as in Theorem 35.1, rewrite through the affine chart rather than
      -- trying to compare the original and modeled metrics directly.
      calc
        g i (ψ x) = f i (T.symm (T x)) := by
          simp [g, hAψ]
        _ = f i x := by rw [T.symm_apply_apply]
    have hOrigUbdd : Function.UniformlyBoundedOn f S := by
      rcases hModelUbdd with ⟨α₁, α₂, hα⟩
      refine ⟨α₁, α₂, ?_⟩
      intro i x hx
      have hxModel : ψ x ∈ Smodel := ⟨x, hx, rfl⟩
      have hxs : x ∈ s := hSsub hx
      have hTxC0 : T x ∈ C0 := ⟨x, hxs, rfl⟩
      have hAψ : A (ψ x) = T x := by
        simpa [ψ, ψAff] using hA_right_on_C0 (T x) hTxC0
      simpa [g, hAψ] using hα i (ψ x) hxModel
    have hOrigEqui :
        Function.EquiLipschitzRelativeTo f S := by
      rcases hModelEqui with ⟨L, hL⟩
      refine ⟨L * Kψ, ?_⟩
      exact
        helperForTheorem_35_1_coordinateModel_pullback_equiLipschitz
          (Smodel := Smodel) (hSmodel := rfl) hψLip hL hEq
    exact ⟨hOrigUbdd, hOrigEqui⟩
end Section35
end Chap07
