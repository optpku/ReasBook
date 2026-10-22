/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section10_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part1

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

-- Proof sketch: project the product witness through the coordinate projections and use
-- nonemptiness of the opposite factor to realize each point as a projected point of the product.
/-- Helper for Theorem 35.2: a convex-hull witness on `C' × D'` projects to convex-hull witnesses
on each factor once `C` and `D` are nonempty. -/
lemma helperForTheorem_35_2_projectedHull_of_productHull
    {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {C' : Set (EuclideanSpace ℝ (Fin m))} {D' : Set (EuclideanSpace ℝ (Fin n))}
    (hHull : C ×ˢ D ⊆ convexHull ℝ (closure (C' ×ˢ D')))
    (hCne : C.Nonempty) (hDne : D.Nonempty) :
    C ⊆ convexHull ℝ (closure C') ∧ D ⊆ convexHull ℝ (closure D') := by
  let fst : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin m) :=
    LinearMap.fst ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
  let snd : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) →ₗ[ℝ]
      EuclideanSpace ℝ (Fin n) :=
    LinearMap.snd ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n))
  have hfstImage :
      fst '' convexHull ℝ (closure (C' ×ˢ D')) =
        convexHull ℝ (fst '' closure (C' ×ˢ D')) := by
    simpa [fst] using
      (LinearMap.image_convexHull (f := fst) (s := closure (C' ×ˢ D')))
  have hsndImage :
      snd '' convexHull ℝ (closure (C' ×ˢ D')) =
        convexHull ℝ (snd '' closure (C' ×ˢ D')) := by
    simpa [snd] using
      (LinearMap.image_convexHull (f := snd) (s := closure (C' ×ˢ D')))
  have hfstClosure :
      fst '' closure (C' ×ˢ D') ⊆ closure (fst '' (C' ×ˢ D')) := by
    exact image_closure_subset_closure_image fst.continuous_of_finiteDimensional
  have hsndClosure :
      snd '' closure (C' ×ˢ D') ⊆ closure (snd '' (C' ×ˢ D')) := by
    exact image_closure_subset_closure_image snd.continuous_of_finiteDimensional
  have hC'ne : C'.Nonempty := by
    rcases hCne with ⟨x0, hx0⟩
    rcases hDne with ⟨y0, hy0⟩
    have hmem : (x0, y0) ∈ convexHull ℝ (closure (C' ×ˢ D')) := hHull ⟨hx0, hy0⟩
    by_contra hEmpty
    have : (x0, y0) ∈ (∅ : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) := by
      simpa [Set.not_nonempty_iff_eq_empty.mp hEmpty] using hmem
    exact this.elim
  have hD'ne : D'.Nonempty := by
    rcases hCne with ⟨x0, hx0⟩
    rcases hDne with ⟨y0, hy0⟩
    have hmem : (x0, y0) ∈ convexHull ℝ (closure (C' ×ˢ D')) := hHull ⟨hx0, hy0⟩
    by_contra hEmpty
    have : (x0, y0) ∈ (∅ : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) := by
      simpa [Set.not_nonempty_iff_eq_empty.mp hEmpty] using hmem
    exact this.elim
  constructor
  · intro x hx
    rcases hDne with ⟨y0, hy0⟩
    have hxy : (x, y0) ∈ convexHull ℝ (closure (C' ×ˢ D')) := hHull ⟨hx, hy0⟩
    have hxImage : x ∈ fst '' convexHull ℝ (closure (C' ×ˢ D')) := ⟨(x, y0), hxy, rfl⟩
    have hxHull : x ∈ convexHull ℝ (fst '' closure (C' ×ˢ D')) := by
      simpa [hfstImage] using hxImage
    have hfstProd : fst '' (C' ×ˢ D') = C' := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact hp.1
      · intro hz
        rcases hD'ne with ⟨y', hy'⟩
        exact ⟨(z, y'), ⟨hz, hy'⟩, rfl⟩
    exact
      (convexHull_min
        (by
          have hsub :
              fst '' closure (C' ×ˢ D') ⊆ convexHull ℝ (closure (fst '' (C' ×ˢ D'))) :=
            hfstClosure.trans (subset_convexHull ℝ (closure (fst '' (C' ×ˢ D'))))
          simpa [hfstProd] using hsub)
        (convex_convexHull ℝ (closure C'))) hxHull
  · intro y hy
    rcases hCne with ⟨x0, hx0⟩
    have hxy : (x0, y) ∈ convexHull ℝ (closure (C' ×ˢ D')) := hHull ⟨hx0, hy⟩
    have hyImage : y ∈ snd '' convexHull ℝ (closure (C' ×ˢ D')) := ⟨(x0, y), hxy, rfl⟩
    have hyHull : y ∈ convexHull ℝ (snd '' closure (C' ×ˢ D')) := by
      simpa [hsndImage] using hyImage
    have hsndProd : snd '' (C' ×ˢ D') = D' := by
      ext z
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact hp.2
      · intro hz
        rcases hC'ne with ⟨x', hx'⟩
        exact ⟨(x', z), ⟨hx', hz⟩, rfl⟩
    exact
      (convexHull_min
        (by
          have hsub :
              snd '' closure (C' ×ˢ D') ⊆ convexHull ℝ (closure (snd '' (C' ×ˢ D'))) :=
            hsndClosure.trans (subset_convexHull ℝ (closure (snd '' (C' ×ˢ D'))))
          simpa [hsndProd] using hsub)
        (convex_convexHull ℝ (closure D'))) hyHull

/-- A family of real-valued functions is pointwise bounded on `s` if the image set
`{f i x | i ∈ I}` is bounded for every `x ∈ s`. -/
def Function.PointwiseBoundedFamilyOn {α I : Type*} (f : I → α → ℝ) (s : Set α) : Prop :=
  ∀ x ∈ s, Bornology.IsBounded (Set.range fun i : I => f i x)

/-- A family of real-valued functions is uniformly bounded on `s` if all values lie between a
common lower and upper bound on `s`. -/
def Function.UniformlyBoundedFamilyOn {α I : Type*} (f : I → α → ℝ) (s : Set α) : Prop :=
  ∃ α₁ α₂ : ℝ, ∀ i x, x ∈ s → α₁ ≤ f i x ∧ f i x ≤ α₂

/-- A family of real-valued functions is equi-Lipschitzian on `s` if one Lipschitz constant works
simultaneously for all members of the family on `s`. -/
def Function.EquiLipschitzFamilyOn {α I : Type*} [PseudoMetricSpace α]
    (f : I → α → ℝ) (s : Set α) : Prop :=
  ∃ L : NNReal, ∀ i : I, LipschitzOnWith L (f i) s

-- Proof sketch: a bounded subset of `ℝ` lies in a closed ball, so the ball radius gives a
-- uniform upper bound on every element of the set.
/-- Helper for Theorem 35.2: a bounded set of real numbers is bounded above. -/
lemma helperForTheorem_35_2_bddAbove_of_isBounded
    {A : Set ℝ} (hA : Bornology.IsBounded A) :
    BddAbove A := by
  rcases hA.subset_closedBall (0 : ℝ) with ⟨R, hR⟩
  refine ⟨R, ?_⟩
  intro y hy
  have hy' : y ∈ Metric.closedBall (0 : ℝ) R := hR hy
  have hyR : |y| ≤ R := by
    simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hy'
  exact (abs_le.mp hyR).2

-- Proof sketch: the same closed-ball control also yields a lower bound by taking the negative
-- radius as a common lower endpoint.
/-- Helper for Theorem 35.2: a bounded set of real numbers is bounded below. -/
lemma helperForTheorem_35_2_bddBelow_of_isBounded
    {A : Set ℝ} (hA : Bornology.IsBounded A) :
    BddBelow A := by
  rcases hA.subset_closedBall (0 : ℝ) with ⟨R, hR⟩
  refine ⟨-R, ?_⟩
  intro y hy
  have hy' : y ∈ Metric.closedBall (0 : ℝ) R := hR hy
  have hyR : |y| ≤ R := by
    simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hy'
  exact (abs_le.mp hyR).1

-- Proof sketch: fix `x ∈ C'`, apply the relative-open subset-witness theorem on `D` to the
-- convex family `y ↦ K_i(x,y)`, and use the witness pointwise bounds on `C' × D'`.
/-- Helper for Theorem 35.2: for each witness point `x ∈ C'`, the `y`-slice family is uniformly
bounded on every closed bounded `Y ⊆ D`. -/
lemma helperForTheorem_35_2_uniformlyBounded_ySlices_of_mem_Cprime
    {I : Type*} {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {C' : Set (EuclideanSpace ℝ (Fin m))} {D' : Set (EuclideanSpace ℝ (Fin n))}
    {K : I → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hD : IsRelativelyOpenConvex D)
    (hK : ∀ i, IsRealConcaveConvexOn C D (K i))
    (hC'sub : C' ⊆ C) (hD'sub : D' ⊆ D)
    (hDhull : D ⊆ convexHull ℝ (closure D'))
    (hPointwise :
      ∀ x ∈ C', ∀ y ∈ D', Bornology.IsBounded (Set.range fun i : I => K i x y))
    (hD'ne : D'.Nonempty)
    {Y : Set (EuclideanSpace ℝ (Fin n))}
    (hYclosed : IsClosed Y) (hYbdd : Bornology.IsBounded Y) (hYsub : Y ⊆ D)
    {x : EuclideanSpace ℝ (Fin m)} (hx : x ∈ C') :
    Function.UniformlyBoundedOn (fun i y => K i x y) Y := by
  rcases hD'ne with ⟨y0, hy0⟩
  have hSliceConv : ∀ i, ConvexOn ℝ D (fun y => K i x y) := by
    intro i
    simpa using (hK i).2 x (hC'sub hx)
  have hSliceBdAbove : ∀ y ∈ D', BddAbove (Set.range fun i : I => K i x y) := by
    intro y hy
    exact
      helperForTheorem_35_2_bddAbove_of_isBounded
        (hPointwise x hx y hy)
  have hExistsBddBelow : ∃ y ∈ D, BddBelow (Set.range fun i : I => K i x y) := by
    refine ⟨y0, hD'sub hy0, ?_⟩
    exact
      helperForTheorem_35_2_bddBelow_of_isBounded
        (hPointwise x hx y0 hy0)
  -- The subset-witness theorem on `D` supplies the desired uniform two-sided bound on `Y`.
  exact
    (helperForTheorem_35_2_relativelyOpenConvex_existsSubset_uniformlyBounded_and_equiLipschitz
      (hs := hD) (hf := hSliceConv) (hs'sub := hD'sub) (hs'hull := hDhull)
      (hs'bdAbove := hSliceBdAbove) (hexists_bddBelow := hExistsBddBelow)
      (S := Y) hYclosed hYbdd hYsub).1

-- Proof sketch: fix `y ∈ D'`, apply the relative-open subset-witness theorem on `C` to the
-- convex family `x ↦ -K_i(x,y)`, and then flip the resulting uniform bounds back to `K_i(x,y)`.
/-- Helper for Theorem 35.2: for each witness point `y ∈ D'`, the `x`-slice family is uniformly
bounded on every closed bounded `X ⊆ C`. -/
lemma helperForTheorem_35_2_uniformlyBounded_xSlices_of_mem_Dprime
    {I : Type*} {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {C' : Set (EuclideanSpace ℝ (Fin m))} {D' : Set (EuclideanSpace ℝ (Fin n))}
    {K : I → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hC : IsRelativelyOpenConvex C)
    (hK : ∀ i, IsRealConcaveConvexOn C D (K i))
    (hC'sub : C' ⊆ C) (hD'sub : D' ⊆ D)
    (hChull : C ⊆ convexHull ℝ (closure C'))
    (hPointwise :
      ∀ x ∈ C', ∀ y ∈ D', Bornology.IsBounded (Set.range fun i : I => K i x y))
    (hC'ne : C'.Nonempty)
    {X : Set (EuclideanSpace ℝ (Fin m))}
    (hXclosed : IsClosed X) (hXbdd : Bornology.IsBounded X) (hXsub : X ⊆ C)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ D') :
    Function.UniformlyBoundedOn (fun i x => K i x y) X := by
  rcases hC'ne with ⟨x0, hx0⟩
  let negSlice : I → EuclideanSpace ℝ (Fin m) → ℝ := fun i x => -K i x y
  have hNegConv : ∀ i, ConvexOn ℝ C (negSlice i) := by
    intro i
    exact neg_convexOn_iff.mpr ((hK i).1 y (hD'sub hy))
  have hNegBdAbove : ∀ x ∈ C', BddAbove (Set.range fun i : I => negSlice i x) := by
    intro x hx
    have hbdd : Bornology.IsBounded (Set.range fun i : I => K i x y) := hPointwise x hx y hy
    have hEq :
        (Set.range fun i : I => negSlice i x) =
          Neg.neg '' (Set.range fun i : I => K i x y) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨K i x y, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    exact
      helperForTheorem_35_2_bddAbove_of_isBounded
        (by simpa [negSlice, hEq] using hbdd.neg)
  have hNegExistsBddBelow : ∃ x ∈ C, BddBelow (Set.range fun i : I => negSlice i x) := by
    have hbdd : Bornology.IsBounded (Set.range fun i : I => K i x0 y) := hPointwise x0 hx0 y hy
    have hEq :
        (Set.range fun i : I => negSlice i x0) =
          Neg.neg '' (Set.range fun i : I => K i x0 y) := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨K i x0 y, ⟨i, rfl⟩, rfl⟩
      · rintro ⟨z, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
    refine ⟨x0, hC'sub hx0, ?_⟩
    exact
      helperForTheorem_35_2_bddBelow_of_isBounded
        (by simpa [negSlice, hEq] using hbdd.neg)
  rcases
      (helperForTheorem_35_2_relativelyOpenConvex_existsSubset_uniformlyBounded_and_equiLipschitz
        (hs := hC) (hf := hNegConv) (hs'sub := hC'sub) (hs'hull := hChull)
        (hs'bdAbove := hNegBdAbove) (hexists_bddBelow := hNegExistsBddBelow)
        (S := X) hXclosed hXbdd hXsub).1 with
    ⟨α₁, α₂, hα⟩
  -- Flip the uniform bounds from `-K` back to `K`.
  refine ⟨-α₂, -α₁, ?_⟩
  intro i x hxX
  have hBounds := hα i x hxX
  constructor
  · linarith [hBounds.2]
  · linarith [hBounds.1]

-- Proof sketch: apply the already-proved coordinatewise product lemma separately for each index.
/-- Helper for Theorem 35.2: uniform coordinatewise Lipschitz bounds yield a uniform product
Lipschitz bound for each kernel in the family. -/
lemma helperForTheorem_35_2_familyProductLipschitz_of_coordinatewiseBounds
    {I : Type*} {m n : ℕ}
    {X : Set (EuclideanSpace ℝ (Fin m))} {Y : Set (EuclideanSpace ℝ (Fin n))}
    {K : I → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    {Lx Ly : NNReal}
    (hX :
      ∀ (i : I) (y : EuclideanSpace ℝ (Fin n)), y ∈ Y →
        LipschitzOnWith Lx (fun x => K i x y) X)
    (hY :
      ∀ (i : I) (x : EuclideanSpace ℝ (Fin m)), x ∈ X →
        LipschitzOnWith Ly (fun y => K i x y) Y) :
    ∀ i, LipschitzOnWith (Lx + Ly) (Function.uncurry (K i)) (X ×ˢ Y) := by
  intro i
  -- Use the single-function product estimate already established for Theorem 35.1.
  exact
    helperForTheorem_35_1_productLipschitz_of_coordinatewiseBounds
      (hX := fun y hy => hX i y hy) (hY := fun x hx => hY i x hx)

-- Proof sketch: use the convex-hull hypothesis and the pointwise boundedness on `C' × D'` to
-- derive uniform upper and lower bounds on closed bounded subsets of `C × D`, then combine the
-- one-variable Lipschitz estimates from the concave and convex slices to obtain a common constant.
/-- Theorem 35.2: let `C ⊆ ℝ^m` and `D ⊆ ℝ^n` be relatively open convex sets, and let
`{K i | i ∈ I}` be a collection of finite concave-convex functions on `C × D`. If there exist
subsets `C' ⊆ C` and `D' ⊆ D` such that `C × D ⊆ convexHull ℝ (closure (C' ×ˢ D'))` and the
family is pointwise bounded on `C' × D'`, then on every closed bounded subset of `C × D` the
family is uniformly bounded and equi-Lipschitzian. -/
theorem section35_theorem35_2
    {I : Type*} {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {K : I → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hC : IsRelativelyOpenConvex C) (hD : IsRelativelyOpenConvex D)
    (hK : ∀ i, IsRealConcaveConvexOn C D (K i))
    (hWitness :
      ∃ C' : Set (EuclideanSpace ℝ (Fin m)),
        ∃ D' : Set (EuclideanSpace ℝ (Fin n)),
          C' ⊆ C ∧
          D' ⊆ D ∧
          C ×ˢ D ⊆ convexHull ℝ (closure (C' ×ˢ D')) ∧
          Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (K i)) (C' ×ˢ D')) :
    ∀ S : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
      S ⊆ C ×ˢ D → IsClosed S → Bornology.IsBounded S →
        Function.UniformlyBoundedFamilyOn (fun i => Function.uncurry (K i)) S ∧
          Function.EquiLipschitzFamilyOn (fun i => Function.uncurry (K i)) S := by
  classical
  rcases hWitness with ⟨C', D', hC'sub, hD'sub, hHull, hWitnessBound⟩
  intro S hSsub hSclosed hSbdd
  by_cases hSEmpty : S = ∅
  · subst hSEmpty
    -- On the empty set, both the uniform bound and the Lipschitz condition are trivial.
    refine ⟨?_, ?_⟩
    · refine ⟨0, 0, ?_⟩
      intro i x hx
      exact (False.elim (by simpa using hx))
    · refine ⟨0, ?_⟩
      intro i
      simp
  · let X : Set (EuclideanSpace ℝ (Fin m)) := Prod.fst '' S
    let Y : Set (EuclideanSpace ℝ (Fin n)) := Prod.snd '' S
    have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
    have hXcomp : IsCompact X := by
      simpa [X] using hScomp.image continuous_fst
    have hYcomp : IsCompact Y := by
      simpa [Y] using hScomp.image continuous_snd
    have hXclosed : IsClosed X := hXcomp.isClosed
    have hYclosed : IsClosed Y := hYcomp.isClosed
    have hXbdd : Bornology.IsBounded X := hXcomp.isBounded
    have hYbdd : Bornology.IsBounded Y := hYcomp.isBounded
    have hXsub : X ⊆ C := by
      intro x hx
      rcases hx with ⟨p, hpS, rfl⟩
      exact (hSsub hpS).1
    have hYsub : Y ⊆ D := by
      intro y hy
      rcases hy with ⟨p, hpS, rfl⟩
      exact (hSsub hpS).2
    have hSnonempty : S.Nonempty := Set.nonempty_iff_ne_empty.2 hSEmpty
    rcases hSnonempty with ⟨p0, hp0S⟩
    have hp0CD : p0 ∈ C ×ˢ D := hSsub hp0S
    have hCne : C.Nonempty := ⟨p0.1, hp0CD.1⟩
    have hDne : D.Nonempty := ⟨p0.2, hp0CD.2⟩
    have hProjected :=
      helperForTheorem_35_2_projectedHull_of_productHull
        (hHull := hHull) hCne hDne
    have hChull : C ⊆ convexHull ℝ (closure C') := hProjected.1
    have hDhull : D ⊆ convexHull ℝ (closure D') := hProjected.2
    have hC'ne : C'.Nonempty := by
      have hmem : p0 ∈ convexHull ℝ (closure (C' ×ˢ D')) := hHull hp0CD
      by_contra hEmpty
      have : p0 ∈ (∅ : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) := by
        simpa [Set.not_nonempty_iff_eq_empty.mp hEmpty] using hmem
      exact this.elim
    have hD'ne : D'.Nonempty := by
      have hmem : p0 ∈ convexHull ℝ (closure (C' ×ˢ D')) := hHull hp0CD
      by_contra hEmpty
      have : p0 ∈ (∅ : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) := by
        simpa [Set.not_nonempty_iff_eq_empty.mp hEmpty] using hmem
      exact this.elim
    have hPointwise :
        ∀ x ∈ C', ∀ y ∈ D', Bornology.IsBounded (Set.range fun i : I => K i x y) := by
      intro x hx y hy
      simpa [Function.uncurry] using hWitnessBound (x, y) ⟨hx, hy⟩
    let Yhat : Type _ := {y : EuclideanSpace ℝ (Fin n) // y ∈ Y}
    let Xhat : Type _ := {x : EuclideanSpace ℝ (Fin m) // x ∈ X}
    let firstFamily : I × Yhat → EuclideanSpace ℝ (Fin m) → ℝ :=
      fun p x => -K p.1 x p.2.1
    let secondFamily : I × Xhat → EuclideanSpace ℝ (Fin n) → ℝ :=
      fun p y => K p.1 p.2.1 y
    have hYSlicesUbdd :
        ∀ x ∈ C', Function.UniformlyBoundedOn (fun i y => K i x y) Y := by
      intro x hx
      exact
        helperForTheorem_35_2_uniformlyBounded_ySlices_of_mem_Cprime
          (hD := hD) (hK := hK) (hC'sub := hC'sub) (hD'sub := hD'sub)
          (hDhull := hDhull) (hPointwise := hPointwise) (hD'ne := hD'ne)
          hYclosed hYbdd hYsub hx
    have hFirstConv : ∀ p, ConvexOn ℝ C (firstFamily p) := by
      intro p
      exact neg_convexOn_iff.mpr ((hK p.1).1 p.2.1 (hYsub p.2.2))
    have hFirstBdAbove : ∀ x ∈ C', BddAbove (Set.range fun p : I × Yhat => firstFamily p x) := by
      intro x hx
      rcases hYSlicesUbdd x hx with ⟨α₁, α₂, hα⟩
      refine ⟨-α₁, ?_⟩
      rintro z ⟨⟨i, y⟩, rfl⟩
      have hBounds := hα i y.1 y.2
      linarith [hBounds.1]
    have hFirstExistsBddBelow :
        ∃ x ∈ C, BddBelow (Set.range fun p : I × Yhat => firstFamily p x) := by
      rcases hC'ne with ⟨x0, hx0⟩
      rcases hYSlicesUbdd x0 hx0 with ⟨α₁, α₂, hα⟩
      refine ⟨x0, hC'sub hx0, ⟨-α₂, ?_⟩⟩
      rintro z ⟨⟨i, y⟩, rfl⟩
      have hBounds := hα i y.1 y.2
      linarith [hBounds.2]
    have hFirst :
        Function.UniformlyBoundedOn firstFamily X ∧
          Function.EquiLipschitzRelativeTo firstFamily X := by
      exact
        helperForTheorem_35_2_relativelyOpenConvex_existsSubset_uniformlyBounded_and_equiLipschitz
          (hs := hC) (hf := hFirstConv) (hs'sub := hC'sub) (hs'hull := hChull)
          (hs'bdAbove := hFirstBdAbove) (hexists_bddBelow := hFirstExistsBddBelow)
          (S := X) hXclosed hXbdd hXsub
    have hXSlicesUbdd :
        ∀ y ∈ D', Function.UniformlyBoundedOn (fun i x => K i x y) X := by
      intro y hy
      exact
        helperForTheorem_35_2_uniformlyBounded_xSlices_of_mem_Dprime
          (hC := hC) (hK := hK) (hC'sub := hC'sub) (hD'sub := hD'sub)
          (hChull := hChull) (hPointwise := hPointwise) (hC'ne := hC'ne)
          hXclosed hXbdd hXsub hy
    have hSecondConv : ∀ p, ConvexOn ℝ D (secondFamily p) := by
      intro p
      simpa [secondFamily] using (hK p.1).2 p.2.1 (hXsub p.2.2)
    have hSecondBdAbove :
        ∀ y ∈ D', BddAbove (Set.range fun p : I × Xhat => secondFamily p y) := by
      intro y hy
      rcases hXSlicesUbdd y hy with ⟨α₁, α₂, hα⟩
      refine ⟨α₂, ?_⟩
      rintro z ⟨⟨i, x⟩, rfl⟩
      exact (hα i x.1 x.2).2
    have hSecondExistsBddBelow :
        ∃ y ∈ D, BddBelow (Set.range fun p : I × Xhat => secondFamily p y) := by
      rcases hD'ne with ⟨y0, hy0⟩
      rcases hXSlicesUbdd y0 hy0 with ⟨α₁, α₂, hα⟩
      refine ⟨y0, hD'sub hy0, ⟨α₁, ?_⟩⟩
      rintro z ⟨⟨i, x⟩, rfl⟩
      exact (hα i x.1 x.2).1
    have hSecond :
        Function.UniformlyBoundedOn secondFamily Y ∧
          Function.EquiLipschitzRelativeTo secondFamily Y := by
      exact
        helperForTheorem_35_2_relativelyOpenConvex_existsSubset_uniformlyBounded_and_equiLipschitz
          (hs := hD) (hf := hSecondConv) (hs'sub := hD'sub) (hs'hull := hDhull)
          (hs'bdAbove := hSecondBdAbove) (hexists_bddBelow := hSecondExistsBddBelow)
          (S := Y) hYclosed hYbdd hYsub
    have hSXY : S ⊆ X ×ˢ Y := by
      intro p hpS
      refine ⟨?_, ?_⟩
      · exact ⟨p, hpS, rfl⟩
      · exact ⟨p, hpS, rfl⟩
    have hUniformBound :
        Function.UniformlyBoundedFamilyOn (fun i => Function.uncurry (K i)) S := by
      rcases hFirst.1 with ⟨β₁, β₂, hβ⟩
      refine ⟨-β₂, -β₁, ?_⟩
      intro i p hpS
      have hpXY : p ∈ X ×ˢ Y := hSXY hpS
      have hBounds := hβ (i, ⟨p.2, hpXY.2⟩) p.1 hpXY.1
      have hLower' : -K i p.1 p.2 ≤ β₂ := by
        simpa [firstFamily] using hBounds.2
      have hUpper' : β₁ ≤ -K i p.1 p.2 := by
        simpa [firstFamily] using hBounds.1
      have hLower : -β₂ ≤ K i p.1 p.2 := by
        linarith
      have hUpper : K i p.1 p.2 ≤ -β₁ := by
        linarith
      constructor
      · simpa [Function.uncurry] using hLower
      · simpa [Function.uncurry] using hUpper
    rcases hFirst.2 with ⟨Lx, hLx⟩
    rcases hSecond.2 with ⟨Ly, hLy⟩
    have hFirstLipOriginal :
        ∀ (i : I) (y : EuclideanSpace ℝ (Fin n)), y ∈ Y →
          LipschitzOnWith Lx (fun x => K i x y) X := by
      intro i y hy
      refine LipschitzOnWith.of_dist_le_mul ?_
      intro x hx x' hx'
      simpa [firstFamily] using (hLx (i, ⟨y, hy⟩)).dist_le_mul x hx x' hx'
    have hSecondLipOriginal :
        ∀ (i : I) (x : EuclideanSpace ℝ (Fin m)), x ∈ X →
          LipschitzOnWith Ly (fun y => K i x y) Y := by
      intro i x hx
      simpa [secondFamily] using hLy (i, ⟨x, hx⟩)
    have hProdLip :
        ∀ i, LipschitzOnWith (Lx + Ly) (Function.uncurry (K i)) (X ×ˢ Y) := by
      intro i
      exact
        helperForTheorem_35_2_familyProductLipschitz_of_coordinatewiseBounds
          (K := K) (Lx := Lx) (Ly := Ly)
          (hX := hFirstLipOriginal) (hY := hSecondLipOriginal) i
    have hEquiLip :
        Function.EquiLipschitzFamilyOn (fun i => Function.uncurry (K i)) S := by
      refine ⟨Lx + Ly, ?_⟩
      intro i
      exact (hProdLip i).mono hSXY
    exact ⟨hUniformBound, hEquiLip⟩

-- Proof sketch: use Theorem 35.2 on each closed bounded subset of `C × D` to obtain a common
-- Lipschitz bound for the sequence from its pointwise convergence on the dense witness set
-- `C' × D'`; then apply the finite-dimensional extension principle for equi-Lipschitz families to
-- construct the pointwise limit on all of `C × D`, prove that the limit remains concave-convex,
-- and upgrade the convergence to uniform convergence on each closed bounded subset.
/-- Helper for Theorem 35.4: pointwise convergence on the dense witness product gives the
pointwise boundedness package required by Theorem 35.2. -/
lemma helperForTheorem_35_4_pointwiseBounded_denseProduct_of_tendsto
    {m n : ℕ}
    {C' : Set (EuclideanSpace ℝ (Fin m))} {D' : Set (EuclideanSpace ℝ (Fin n))}
    {KSeq : ℕ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hTendsto :
      ∀ u ∈ C', ∀ v ∈ D', ∃ l : ℝ,
        Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds l)) :
    Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (KSeq i)) (C' ×ˢ D') := by
  -- A convergent real sequence has bounded range, so each witness orbit is bounded in `ℝ`.
  intro p hp
  rcases hTendsto p.1 hp.1 p.2 hp.2 with ⟨l, hl⟩
  simpa [Function.uncurry] using
    Metric.isBounded_range_of_tendsto (u := fun i : ℕ => KSeq i p.1 p.2) hl

/-- Helper for Theorem 35.4: density in each factor gives the product convex-hull witness needed
for Theorem 35.2. -/
lemma helperForTheorem_35_4_productHull_of_factorClosures
    {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {C' : Set (EuclideanSpace ℝ (Fin m))} {D' : Set (EuclideanSpace ℝ (Fin n))}
    (hCclosure : C ⊆ closure C') (hDclosure : D ⊆ closure D') :
    C ×ˢ D ⊆ convexHull ℝ (closure (C' ×ˢ D')) := by
  -- Each point of `C × D` already lies in the closure of the dense witness product.
  intro p hp
  have hpClosure : p ∈ closure (C' ×ˢ D') := by
    rw [closure_prod_eq]
    exact ⟨hCclosure hp.1, hDclosure hp.2⟩
  exact subset_convexHull ℝ (closure (C' ×ˢ D')) hpClosure

/-- Helper for Theorem 35.4: pointwise limits of finite concave-convex kernels remain
concave-convex. -/
lemma helperForTheorem_35_4_concaveConvex_limit_of_pointwiseTendsto
    {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {KSeq : ℕ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    {K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hCconv : Convex ℝ C) (hDconv : Convex ℝ D)
    (hKSeq : ∀ i, IsRealConcaveConvexOn C D (KSeq i))
    (hTendsto :
      ∀ u ∈ C, ∀ v ∈ D,
        Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v))) :
    IsRealConcaveConvexOn C D K := by
  constructor
  · intro v hv
    -- Pass to the negatives to reduce the concave first-variable slices to the convex theorem.
    have hNegTendsto :
        ∀ u ∈ C,
          Filter.Tendsto (fun i : ℕ => -KSeq i u v) Filter.atTop (nhds (-K u v)) := by
      intro u hu
      simpa using (hTendsto u hu v hv).neg
    have hNegConv : ∀ i, ConvexOn ℝ C (fun u => -KSeq i u v) := by
      intro i
      exact neg_convexOn_iff.mpr ((hKSeq i).1 v hv)
    exact
      neg_convexOn_iff.mp
        (Section10.convexOn_lim_of_pointwise_tendsto
          (n := m) (C := C) hCconv (f := fun i u => -KSeq i u v) (g := fun u => -K u v)
          hNegTendsto hNegConv)
  · intro u hu
    -- The second-variable slices are already convex, so Chapter 10 applies directly.
    exact
      Section10.convexOn_lim_of_pointwise_tendsto
        (n := n) (C := D) hDconv (f := fun i v => KSeq i u v) (g := fun v => K u v)
        (fun v hv => hTendsto u hu v hv) (fun i => (hKSeq i).2 u hu)

/-- Helper for Theorem 35.4: dense-product convergence extends from `C' × D'` to any point of
`C × D` by combining one local equi-Lipschitz estimate with Cauchy convergence at a nearby
witness point. -/
lemma helperForTheorem_35_4_pointwiseTendsto_of_denseWitness
    {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {C' : Set (EuclideanSpace ℝ (Fin m))} {D' : Set (EuclideanSpace ℝ (Fin n))}
    {KSeq : ℕ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hC : IsRelativelyOpenConvex C) (hD : IsRelativelyOpenConvex D)
    (hKSeq : ∀ i, IsRealConcaveConvexOn C D (KSeq i))
    (hC'sub : C' ⊆ C) (hD'sub : D' ⊆ D)
    (hCclosure : C ⊆ closure C') (hDclosure : D ⊆ closure D')
    (hDenseTendsto :
      ∀ u ∈ C', ∀ v ∈ D', ∃ l : ℝ,
        Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds l))
    {u0 : EuclideanSpace ℝ (Fin m)} (hu0 : u0 ∈ C)
    {v0 : EuclideanSpace ℝ (Fin n)} (hv0 : v0 ∈ D) :
    ∃ l : ℝ, Filter.Tendsto (fun i : ℕ => KSeq i u0 v0) Filter.atTop (nhds l) := by
  -- Build the witness package for Theorem 35.2 from the dense convergence hypothesis.
  have hHull :=
    helperForTheorem_35_4_productHull_of_factorClosures
      (C := C) (D := D) (C' := C') (D' := D') hCclosure hDclosure
  have hPointwiseBounded :
      Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (KSeq i)) (C' ×ˢ D') :=
    helperForTheorem_35_4_pointwiseBounded_denseProduct_of_tendsto
      (KSeq := KSeq) hDenseTendsto
  -- Localize around `(u0, v0)` so that one Lipschitz constant controls every `KSeq i`.
  rcases
      helperForTheorem_35_1_existsClosedBoundedNeighborhood_subset_relativelyOpenConvex
        (hs := hC) hu0 with
    ⟨TC, hu0TC, hTCsub, hTCclosed, hTCbdd, hTCnhds⟩
  rcases
      helperForTheorem_35_1_existsClosedBoundedNeighborhood_subset_relativelyOpenConvex
        (hs := hD) hv0 with
    ⟨TD, hv0TD, hTDsub, hTDclosed, hTDbdd, hTDnhds⟩
  let S : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) := TC ×ˢ TD
  have hSsub : S ⊆ C ×ˢ D := by
    intro p hp
    exact ⟨hTCsub hp.1, hTDsub hp.2⟩
  have hSclosed : IsClosed S := hTCclosed.prod hTDclosed
  have hSbdd : Bornology.IsBounded S := hTCbdd.prod hTDbdd
  have hFamily :=
    section35_theorem35_2
      (I := ℕ) (C := C) (D := D) (K := KSeq)
      hC hD hKSeq
      ⟨C', D', hC'sub, hD'sub, hHull, hPointwiseBounded⟩
      S hSsub hSclosed hSbdd
  rcases hFamily.2 with ⟨L, hL⟩
  have hL1pos : 0 < ((L : ℝ) + 1) := by
    have hLnonneg : 0 ≤ (L : ℝ) := by exact_mod_cast L.2
    linarith
  have hL1ne : ((L : ℝ) + 1) ≠ 0 := ne_of_gt hL1pos
  rcases Metric.mem_nhdsWithin_iff.mp hTCnhds with ⟨rC, hrCpos, hrCsub⟩
  rcases Metric.mem_nhdsWithin_iff.mp hTDnhds with ⟨rD, hrDpos, hrDsub⟩
  have hu0Cl : u0 ∈ closure C' := hCclosure hu0
  have hv0Cl : v0 ∈ closure D' := hDclosure hv0
  -- Show the scalar sequence at `(u0, v0)` is Cauchy by comparing it to a nearby witness point.
  have hCauchy : CauchySeq (fun i : ℕ => KSeq i u0 v0) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hεthird : 0 < ε / 3 := by linarith
    let δ : ℝ := (ε / 3) / ((L : ℝ) + 1)
    have hδpos : 0 < δ := div_pos hεthird hL1pos
    let δ1 : ℝ := min rC (min rD δ)
    have hδ1pos : 0 < δ1 := by
      refine lt_min hrCpos ?_
      exact lt_min hrDpos hδpos
    rcases (Metric.mem_closure_iff.1 hu0Cl) δ1 hδ1pos with ⟨u1, hu1C', hu1dist⟩
    rcases (Metric.mem_closure_iff.1 hv0Cl) δ1 hδ1pos with ⟨v1, hv1D', hv1dist⟩
    have hu1C : u1 ∈ C := hC'sub hu1C'
    have hv1D : v1 ∈ D := hD'sub hv1D'
    have hu1dist' : dist u1 u0 < δ1 := by simpa [dist_comm] using hu1dist
    have hv1dist' : dist v1 v0 < δ1 := by simpa [dist_comm] using hv1dist
    have hu1TC : u1 ∈ TC := by
      apply hrCsub
      refine ⟨?_, hu1C⟩
      have : dist u1 u0 < rC := lt_of_lt_of_le hu1dist' (min_le_left _ _)
      simpa [Metric.mem_ball, dist_comm] using this
    have hv1TD : v1 ∈ TD := by
      apply hrDsub
      refine ⟨?_, hv1D⟩
      have : dist v1 v0 < rD := lt_of_lt_of_le hv1dist' (le_trans (min_le_right _ _) (min_le_left _ _))
      simpa [Metric.mem_ball, dist_comm] using this
    have hq0S : (u0, v0) ∈ S := ⟨hu0TC, hv0TD⟩
    have hq1S : (u1, v1) ∈ S := ⟨hu1TC, hv1TD⟩
    have hq01 : dist (u0, v0) (u1, v1) < δ1 := by
      rw [Prod.dist_eq]
      exact
        max_lt_iff.mpr
          ⟨by simpa [dist_comm] using hu1dist', by simpa [dist_comm] using hv1dist'⟩
    rcases hDenseTendsto u1 hu1C' v1 hv1D' with ⟨l, hl⟩
    have hWitnessCauchy : CauchySeq (fun i : ℕ => KSeq i u1 v1) := hl.cauchySeq
    rcases (Metric.cauchySeq_iff.1 hWitnessCauchy) (ε / 3) hεthird with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro i hi j hj
    have hdist_i :
        dist (KSeq i u0 v0) (KSeq i u1 v1) ≤ (L : ℝ) * dist (u0, v0) (u1, v1) := by
      simpa [S, Function.uncurry] using (hL i).dist_le_mul (u0, v0) hq0S (u1, v1) hq1S
    have hdist_j :
        dist (KSeq j u1 v1) (KSeq j u0 v0) ≤ (L : ℝ) * dist (u0, v0) (u1, v1) := by
      have :
          dist (KSeq j u0 v0) (KSeq j u1 v1) ≤ (L : ℝ) * dist (u0, v0) (u1, v1) := by
        simpa [S, Function.uncurry] using (hL j).dist_le_mul (u0, v0) hq0S (u1, v1) hq1S
      simpa [dist_comm] using this
    have hδ1le : δ1 ≤ δ := le_trans (min_le_right _ _) (min_le_right _ _)
    have hmul_lt :
        ((L : ℝ) + 1) * dist (u0, v0) (u1, v1) < ε / 3 := by
      have hq01' : dist (u0, v0) (u1, v1) < δ :=
        lt_of_lt_of_le hq01 hδ1le
      have :
          ((L : ℝ) + 1) * dist (u0, v0) (u1, v1) < ((L : ℝ) + 1) * δ :=
        mul_lt_mul_of_pos_left hq01' hL1pos
      have hmul : ((L : ℝ) + 1) * δ = ε / 3 := by
        simpa [δ] using (mul_div_cancel₀ (a := ε / 3) (b := (L : ℝ) + 1) hL1ne)
      simpa [hmul] using this
    have hle_mul :
        (L : ℝ) * dist (u0, v0) (u1, v1) ≤ ((L : ℝ) + 1) * dist (u0, v0) (u1, v1) := by
      have hLle : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
      exact mul_le_mul_of_nonneg_right hLle dist_nonneg
    have houter_i : dist (KSeq i u0 v0) (KSeq i u1 v1) < ε / 3 :=
      lt_of_le_of_lt hdist_i (lt_of_le_of_lt hle_mul hmul_lt)
    have houter_j : dist (KSeq j u1 v1) (KSeq j u0 v0) < ε / 3 :=
      lt_of_le_of_lt hdist_j (lt_of_le_of_lt hle_mul hmul_lt)
    have hmid : dist (KSeq i u1 v1) (KSeq j u1 v1) < ε / 3 := by
      have : ‖KSeq i u1 v1 - KSeq j u1 v1‖ < ε / 3 := hN i hi j hj
      simpa [dist_eq_norm] using this
    have htri :
        dist (KSeq i u0 v0) (KSeq j u0 v0) ≤
          dist (KSeq i u0 v0) (KSeq i u1 v1) +
            dist (KSeq i u1 v1) (KSeq j u1 v1) +
              dist (KSeq j u1 v1) (KSeq j u0 v0) :=
      dist_triangle4 _ _ _ _
    have hlt :
        dist (KSeq i u0 v0) (KSeq j u0 v0) < ε / 3 + ε / 3 + ε / 3 :=
      lt_of_le_of_lt htri (add_lt_add (add_lt_add houter_i hmid) houter_j)
    have hsum : ε / 3 + ε / 3 + ε / 3 = ε := by nlinarith
    simpa [dist_eq_norm, hsum] using hlt
  exact cauchySeq_tendsto_of_complete hCauchy

/-- Helper for Theorem 35.4: on a closed bounded set, pointwise convergence plus a common
Lipschitz constant upgrades to uniform convergence. -/
lemma helperForTheorem_35_4_tendstoUniformlyOn_of_pointwiseTendsto_and_equiLipschitz
    {m n : ℕ}
    {S : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
    {f : ℕ → (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) → ℝ}
    {g : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) → ℝ}
    (hSclosed : IsClosed S) (hSbdd : Bornology.IsBounded S)
    (hPoint :
      ∀ p ∈ S, Filter.Tendsto (fun i : ℕ => f i p) Filter.atTop (nhds (g p)))
    (hEqui : Function.EquiLipschitzFamilyOn f S) :
    TendstoUniformlyOn f g Filter.atTop S := by
  classical
  rcases hEqui with ⟨L, hL⟩
  have hLipG : LipschitzOnWith L g S := by
    -- Pass the pointwise Lipschitz inequality to the limit to show the same constant works for `g`.
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    have hdistT :
        Filter.Tendsto (fun i : ℕ => dist (f i x) (f i y)) Filter.atTop
          (nhds (dist (g x) (g y))) := (hPoint x hx).dist (hPoint y hy)
    have hEv :
        ∀ᶠ i : ℕ in Filter.atTop, dist (f i x) (f i y) ≤ (L : ℝ) * dist x y := by
      refine Filter.eventually_atTop.2 ⟨0, ?_⟩
      intro i hi
      exact (hL i).dist_le_mul x hx y hy
    exact tendsto_le_of_eventuallyLE hdistT tendsto_const_nhds hEv
  have hScomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed hSbdd
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hεthird : 0 < ε / 3 := by linarith
  let δ : ℝ := (ε / 3) / ((L : ℝ) + 1)
  have hL1pos : 0 < ((L : ℝ) + 1) := by
    have hLnonneg : 0 ≤ (L : ℝ) := by exact_mod_cast L.2
    linarith
  have hL1ne : ((L : ℝ) + 1) ≠ 0 := ne_of_gt hL1pos
  have hδpos : 0 < δ := div_pos hεthird hL1pos
  rcases hScomp.elim_nhds_subcover (U := fun x => Metric.ball x δ) (by
      intro x hx
      exact Metric.ball_mem_nhds x hδpos) with ⟨t, htS, hcover⟩
  have hPointNet :
      ∀ᶠ i : ℕ in Filter.atTop, ∀ z ∈ t, dist (f i z) (g z) < ε / 3 := by
    exact t.eventually_all.2 (fun z hz =>
      (Metric.tendsto_nhds.1 (hPoint z (htS z hz))) (ε / 3) hεthird)
  rcases Filter.eventually_atTop.1 hPointNet with ⟨N, hN⟩
  refine Filter.eventually_atTop.2 ⟨N, ?_⟩
  intro i hi x hxS
  have hxcover : x ∈ ⋃ z ∈ t, Metric.ball z δ := hcover hxS
  rcases Set.mem_iUnion.mp hxcover with ⟨z, hxcover'⟩
  rcases Set.mem_iUnion.mp hxcover' with ⟨hzT, hxz⟩
  have hzS : z ∈ S := htS z hzT
  have hxzlt : dist x z < δ := by simpa [Metric.mem_ball, dist_comm] using hxz
  have hmul_lt : ((L : ℝ) + 1) * dist x z < ε / 3 := by
    have :
        ((L : ℝ) + 1) * dist x z < ((L : ℝ) + 1) * δ :=
      mul_lt_mul_of_pos_left hxzlt hL1pos
    have hmul : ((L : ℝ) + 1) * δ = ε / 3 := by
      simpa [δ] using (mul_div_cancel₀ (a := ε / 3) (b := (L : ℝ) + 1) hL1ne)
    simpa [hmul] using this
  have hle_mul :
      (L : ℝ) * dist x z ≤ ((L : ℝ) + 1) * dist x z := by
    have hLle : (L : ℝ) ≤ (L : ℝ) + 1 := by linarith
    exact mul_le_mul_of_nonneg_right hLle dist_nonneg
  have hixz : dist (f i x) (f i z) < ε / 3 :=
    lt_of_le_of_lt ((hL i).dist_le_mul x hxS z hzS) (lt_of_le_of_lt hle_mul hmul_lt)
  have hgzx : dist (g z) (g x) < ε / 3 := by
    have hdist : dist (g x) (g z) ≤ (L : ℝ) * dist x z := hLipG.dist_le_mul x hxS z hzS
    have : dist (g x) (g z) < ε / 3 :=
      lt_of_le_of_lt hdist (lt_of_le_of_lt hle_mul hmul_lt)
    simpa [dist_comm] using this
  have hiz : dist (f i z) (g z) < ε / 3 := hN i hi z hzT
  have htri :
      dist (f i x) (g x) ≤
        dist (f i x) (f i z) + dist (f i z) (g z) + dist (g z) (g x) :=
    dist_triangle4 _ _ _ _
  have hlt :
      dist (f i x) (g x) < ε / 3 + ε / 3 + ε / 3 :=
    lt_of_le_of_lt htri (add_lt_add (add_lt_add hixz hiz) hgzx)
  have hsum : ε / 3 + ε / 3 + ε / 3 = ε := by nlinarith
  simpa [dist_comm, hsum] using hlt

/-- Theorem 35.4: if `C ⊆ ℝ^m` and `D ⊆ ℝ^n` are relatively open convex sets and
`K₁, K₂, ...` is a sequence of finite concave-convex functions on `C × D` whose pointwise limit
exists on a dense product subset `C' × D'`, then there is a finite concave-convex limit function
`K` on `C × D` such that `K i` converges pointwise to `K` on `C × D` and uniformly on every
closed bounded subset of `C × D`. -/
theorem section35_theorem35_4
    {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {KSeq : ℕ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ}
    (hC : IsRelativelyOpenConvex C) (hD : IsRelativelyOpenConvex D)
    (hKSeq : ∀ i, IsRealConcaveConvexOn C D (KSeq i))
    (hDense :
      ∃ C' : Set (EuclideanSpace ℝ (Fin m)),
        ∃ D' : Set (EuclideanSpace ℝ (Fin n)),
          C' ⊆ C ∧
          D' ⊆ D ∧
          C ⊆ closure C' ∧
          D ⊆ closure D' ∧
          ∀ u ∈ C', ∀ v ∈ D', ∃ l : ℝ,
            Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds l)) :
    ∃ K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ,
      IsRealConcaveConvexOn C D K ∧
      (∀ u ∈ C, ∀ v ∈ D,
        Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v))) ∧
      ∀ S : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)),
        S ⊆ C ×ˢ D → IsClosed S → Bornology.IsBounded S →
          TendstoUniformlyOn (fun i p => Function.uncurry (KSeq i) p) (Function.uncurry K)
            Filter.atTop S := by
  classical
  rcases hDense with ⟨C', D', hC'sub, hD'sub, hCclosure, hDclosure, hDenseTendsto⟩
  -- Convert dense witness convergence into the boundedness package required by Theorem 35.2.
  have hHull :=
    helperForTheorem_35_4_productHull_of_factorClosures
      (C := C) (D := D) (C' := C') (D' := D') hCclosure hDclosure
  have hPointwiseBounded :
      Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (KSeq i)) (C' ×ˢ D') :=
    helperForTheorem_35_4_pointwiseBounded_denseProduct_of_tendsto
      (KSeq := KSeq) hDenseTendsto
  have hWitness :
      ∃ Cw : Set (EuclideanSpace ℝ (Fin m)),
        ∃ Dw : Set (EuclideanSpace ℝ (Fin n)),
          Cw ⊆ C ∧
          Dw ⊆ D ∧
          C ×ˢ D ⊆ convexHull ℝ (closure (Cw ×ˢ Dw)) ∧
          Function.PointwiseBoundedFamilyOn (fun i => Function.uncurry (KSeq i)) (Cw ×ˢ Dw) :=
    ⟨C', D', hC'sub, hD'sub, hHull, hPointwiseBounded⟩
  -- First extend the pointwise convergence from `C' × D'` to all of `C × D`.
  have hLimitExists :
      ∀ u ∈ C, ∀ v ∈ D, ∃ l : ℝ,
        Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds l) := by
    intro u hu v hv
    exact
      helperForTheorem_35_4_pointwiseTendsto_of_denseWitness
        (C := C) (D := D) (C' := C') (D' := D') (KSeq := KSeq)
        hC hD hKSeq hC'sub hD'sub hCclosure hDclosure hDenseTendsto hu hv
  -- Choose the pointwise limit on `C × D`, using `0` only outside the domain where it is irrelevant.
  let K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun u v =>
      if hu : u ∈ C then
        if hv : v ∈ D then
          Classical.choose (hLimitExists u hu v hv)
        else 0
      else 0
  have hKtendsto :
      ∀ u ∈ C, ∀ v ∈ D,
        Filter.Tendsto (fun i : ℕ => KSeq i u v) Filter.atTop (nhds (K u v)) := by
    intro u hu v hv
    simpa [K, hu, hv] using Classical.choose_spec (hLimitExists u hu v hv)
  -- The slice-wise Chapter 10 limit theorem preserves the concave-convex structure.
  have hKconcaveConvex : IsRealConcaveConvexOn C D K :=
    helperForTheorem_35_4_concaveConvex_limit_of_pointwiseTendsto
      (C := C) (D := D) (KSeq := KSeq) (K := K) hC.1 hD.1 hKSeq hKtendsto
  refine ⟨K, hKconcaveConvex, hKtendsto, ?_⟩
  intro S hSsub hSclosed hSbdd
  -- On each closed bounded set, Theorem 35.2 gives one Lipschitz constant for the whole sequence.
  have hFamily :=
    section35_theorem35_2
      (I := ℕ) (C := C) (D := D) (K := KSeq)
      hC hD hKSeq hWitness S hSsub hSclosed hSbdd
  -- Pointwise convergence on the compact set and the common Lipschitz constant upgrade to uniform convergence.
  exact
    helperForTheorem_35_4_tendstoUniformlyOn_of_pointwiseTendsto_and_equiLipschitz
      (S := S) (f := fun i p => Function.uncurry (KSeq i) p) (g := Function.uncurry K)
      hSclosed hSbdd
      (by
        intro p hp
        exact hKtendsto p.1 (hSsub hp).1 p.2 (hSsub hp).2)
      hFamily.2

-- Proof sketch: apply Theorem 35.2 to the family of saddle functions `K(·, ·, t)` indexed by
-- `t ∈ T` on compact neighborhoods in the locally compact space `T`; pointwise continuity in `t`
-- gives the needed pointwise boundedness, and the dense-subset variant follows from the same
-- argument using the weaker continuity hypothesis on a dense witness set.
/-- Helper for Theorem 35.3: density in each factor yields the product convex-hull witness needed
for Theorem 35.2. -/
lemma helperForTheorem_35_3_productHull_of_factorClosures
    {m n : ℕ}
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {C' : Set (EuclideanSpace ℝ (Fin m))} {D' : Set (EuclideanSpace ℝ (Fin n))}
    (hCclosure : C ⊆ closure C') (hDclosure : D ⊆ closure D') :
    C ×ˢ D ⊆ convexHull ℝ (closure (C' ×ˢ D')) := by
  -- Each point of `C × D` already lies in the closure of the witness product.
  intro p hp
  have hpClosure : p ∈ closure (C' ×ˢ D') := by
    rw [closure_prod_eq]
    exact ⟨hCclosure hp.1, hDclosure hp.2⟩
  -- The convex hull contains the set whose hull it is built from.
  exact subset_convexHull ℝ (closure (C' ×ˢ D')) hpClosure

/-- Helper for Theorem 35.3: on a compact set of parameters `t`, continuity in `t` on a witness
product gives a uniformly bounded and equi-Lipschitz family on each closed bounded subset of
`C × D`. -/
lemma helperForTheorem_35_3_compactIndexed_family_uniformlyBoundedAndEquiLipschitz
    {m n : ℕ} {T : Type*} [TopologicalSpace T]
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {Cw : Set (EuclideanSpace ℝ (Fin m))} {Dw : Set (EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → T → ℝ}
    (hC : IsRelativelyOpenConvex C) (hD : IsRelativelyOpenConvex D)
    (hK : ∀ t, IsRealConcaveConvexOn C D (fun u v => K u v t))
    {K0 : Set T} (hK0comp : IsCompact K0)
    (hCwsub : Cw ⊆ C) (hDwsub : Dw ⊆ D)
    (hHull : C ×ˢ D ⊆ convexHull ℝ (closure (Cw ×ˢ Dw)))
    (hCont : ∀ u ∈ Cw, ∀ v ∈ Dw, Continuous fun t => K u v t)
    {S : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))}
    (hSsub : S ⊆ C ×ˢ D) (hSclosed : IsClosed S) (hSbdd : Bornology.IsBounded S) :
    Function.UniformlyBoundedFamilyOn
        (fun τ : {t : T // t ∈ K0} => Function.uncurry (fun u v => K u v τ.1)) S ∧
      Function.EquiLipschitzFamilyOn
        (fun τ : {t : T // t ∈ K0} => Function.uncurry (fun u v => K u v τ.1)) S := by
  -- Continuity on the compact parameter set bounds each witness orbit in `ℝ`.
  have hPointwise :
      Function.PointwiseBoundedFamilyOn
        (fun τ : {t : T // t ∈ K0} => Function.uncurry (fun u v => K u v τ.1)) (Cw ×ˢ Dw) := by
    intro p hp
    have hContinuous :
        ContinuousOn (fun t => K p.1 p.2 t) K0 := (hCont p.1 hp.1 p.2 hp.2).continuousOn
    simpa [Function.uncurry] using
      helperForTheorem_35_1_boundedRange_of_continuousOn_compact
        (hs := hK0comp) (g := fun t => K p.1 p.2 t) (hg := hContinuous)
  -- Apply Theorem 35.2 to the compactly indexed family `t ↦ K(·, ·, t)`.
  exact
    section35_theorem35_2
      (I := {t : T // t ∈ K0}) (C := C) (D := D)
      (K := fun τ u v => K u v τ.1)
      hC hD (fun τ => hK τ.1)
      ⟨Cw, Dw, hCwsub, hDwsub, hHull, hPointwise⟩ S hSsub hSclosed hSbdd

/-- Helper for Theorem 35.3: continuity on the left-associated product `((u,v), t)` transfers to
the textbook right-associated product `u, (v, t)`. -/
lemma helperForTheorem_35_3_rightAssociatedContinuousOn
    {m n : ℕ} {T : Type*} [TopologicalSpace T]
    {C : Set (EuclideanSpace ℝ (Fin m))} {D : Set (EuclideanSpace ℝ (Fin n))}
    {K : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin n) → T → ℝ}
    (hCont :
      ContinuousOn
        (fun p : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) × T =>
          K p.1.1 p.1.2 p.2)
        ((C ×ˢ D) ×ˢ (Set.univ : Set T))) :
    ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) × T =>
        K p.1 p.2.1 p.2.2)
      (C ×ˢ (D ×ˢ (Set.univ : Set T))) := by
  -- The inverse associativity homeomorphism sends `u, (v, t)` back to `((u, v), t)`.
  have hMaps :
      Set.MapsTo
        (Homeomorph.prodAssoc
          (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)) T).symm
        (C ×ˢ (D ×ˢ (Set.univ : Set T)))
        ((C ×ˢ D) ×ˢ (Set.univ : Set T)) := by
    intro p hp
    exact ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩
  -- Compose the continuity statement with the homeomorphism.
  simpa using
    hCont.comp
      (Homeomorph.prodAssoc
        (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin n)) T).symm.continuous.continuousOn
      hMaps

end Section35
end Chap07
