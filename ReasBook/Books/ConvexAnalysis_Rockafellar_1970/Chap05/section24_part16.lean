/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part15

section Chap05
section Section24

open scoped ConvexAnalysis
open scoped Topology
open scoped Pointwise

attribute [local instance] Classical.propDecidable

-- Proof sketch: the forward implication is Proposition 5.24.3, which shows that every proper
-- convex potential has cyclically monotone Euclideanized subdifferential. For the converse, apply
-- Rockafellar's construction of a convex potential from the path-supremum associated to a
-- cyclically monotone mapping, then close the resulting proper convex function and verify that the
-- original mapping is pointwise contained in its Euclideanized subdifferential.
/-- Theorem 5.24.11: a multivalued mapping `ρ : ℝ^n ⇉ ℝ^n` is cyclically monotone if and only if
there exists a closed proper convex function `f` on `ℝ^n` whose Euclideanized subdifferential
contains `ρ` pointwise; in Lean this containment is
`ρ x ⊆ (dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x` for every `x`. -/
theorem exists_closedProperConvex_subdifferential_superset_iff_isCyclicallyMonotone {n : ℕ}
    (ρ : (Fin n → ℝ) → Set (Fin n → ℝ)) :
    (∃ f : (Fin n → ℝ) → EReal,
      ClosedConvexFunction f ∧
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
        ∀ x : Fin n → ℝ,
          ρ x ⊆ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)) ↔
      IsCyclicallyMonotone ρ := by
  constructor
  · intro hWitness
    rcases hWitness with ⟨f, _hclosed, hproper, hsubset⟩
    have hsubdiff :
        IsCyclicallyMonotone
          (fun x => ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x)) :=
      properConvexFunctionOn_isCyclicallyMonotone_subdifferential f hproper
    -- First prove cyclic monotonicity for the ambient subdifferential mapping, then descend
    -- along the given pointwise inclusion `ρ x ⊆ ∂f(x)`.
    exact
      helperForTheorem_5_24_11_pointwiseSubset_preserves_isCyclicallyMonotone
        hsubdiff hsubset
  · intro hρ
    by_cases hempty : ∀ x : Fin n → ℝ, ρ x = ∅
    · -- The empty graph branch is realized by the constant-zero potential.
      exact
        helperForTheorem_5_24_11_emptyGraph_exists_closedProperConvex_subdifferential_superset
          hempty
    · -- Route correction: the substantive Rockafellar construction is only needed once the graph
      -- is known to be nonempty; the easy empty-graph case has already been discharged above.
      exact
        helperForTheorem_5_24_11_nonemptyGraph_exists_closedProperConvex_subdifferential_superset
          hρ hempty

-- Proof sketch: if `ρ` is the Euclideanized subdifferential of a closed proper convex function,
-- Proposition 5.24.3 gives cyclic monotonicity, and maximality follows from Theorem 5.24.11 by
-- applying the cyclically monotone-superset realization to any larger cyclically monotone graph.
-- Conversely, Theorem 5.24.11 yields a closed proper convex potential whose Euclideanized
-- subdifferential contains `ρ`; maximality upgrades that containment to equality. For uniqueness,
-- compare two closed proper convex functions with the same Euclideanized subdifferential mapping
-- and apply the same potential-reconstruction argument to conclude that they differ by a real
-- additive constant.
/-- Helper for Theorem 5.24.12: a common Euclideanized subgradient point already determines the
additive gap between two proper convex functions. -/
lemma helperForTheorem_5_24_12_additive_constant_exists_at_common_graph_point
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    {x xStar : Fin n → ℝ}
    (hxStarF : xStar ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x))
    (hxStarG : xStar ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x)) :
    ∃ α : ℝ, g x = f x + ((α : ℝ) : EReal) := by
  have hSubF : IsEuclideanSubgradientAt f x xStar := by
    -- Read Euclideanized fiber membership as the subgradient condition in primal coordinates.
    simpa [IsEuclideanSubgradientAt] using hxStarF
  have hSubG : IsEuclideanSubgradientAt g x xStar := by
    -- The same identification applies on the `g` side.
    simpa [IsEuclideanSubgradientAt] using hxStarG
  have hFYF : FenchelYoungEqualityAt f x xStar := by
    -- A Euclidean subgradient realizes Fenchel-Young equality for `f`.
    exact
      ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        f hproperF x xStar).1.out 0 3).1 hSubF
  have hFYG : FenchelYoungEqualityAt g x xStar := by
    -- The same equality holds for `g`.
    exact
      ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        g hproperG x xStar).1.out 0 3).1 hSubG
  have hFiniteF :=
    helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality
      f hproperF x xStar (le_of_eq hFYF)
  have hFiniteG :=
    helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality
      g hproperG x xStar (le_of_eq hFYG)
  have hProperStarF :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproperF
  have hProperStarG :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g) :=
    proper_fenchelConjugate_of_proper (n := n) (f := g) hproperG
  have hStarF_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) :=
    hProperStarF.2.2 xStar (by simp)
  have hStarG_ne_bot : fenchelConjugate n g xStar ≠ (⊥ : EReal) :=
    hProperStarG.2.2 xStar (by simp)
  have hStarF_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) := by
    -- The finite Fenchel-Young equality excludes `⊤` on the conjugate side.
    intro htop
    rw [FenchelYoungEqualityAt] at hFYF
    have hLeftTop : f x + fenchelConjugate n f xStar = (⊤ : EReal) := by
      simpa [htop] using (EReal.add_top_of_ne_bot hFiniteF.2)
    exact EReal.coe_ne_top (dotProduct x xStar) (hFYF.symm.trans hLeftTop)
  have hStarG_ne_top : fenchelConjugate n g xStar ≠ (⊤ : EReal) := by
    -- The same finiteness argument excludes `⊤` for the conjugate of `g`.
    intro htop
    rw [FenchelYoungEqualityAt] at hFYG
    have hLeftTop : g x + fenchelConjugate n g xStar = (⊤ : EReal) := by
      simpa [htop] using (EReal.add_top_of_ne_bot hFiniteG.2)
    exact EReal.coe_ne_top (dotProduct x xStar) (hFYG.symm.trans hLeftTop)
  rw [FenchelYoungEqualityAt] at hFYF hFYG
  have hfx : f x = (((f x).toReal : ℝ) : EReal) := by
    rw [EReal.coe_toReal hFiniteF.1 hFiniteF.2]
  have hgx : g x = (((g x).toReal : ℝ) : EReal) := by
    rw [EReal.coe_toReal hFiniteG.1 hFiniteG.2]
  have hstarf : fenchelConjugate n f xStar =
      (((fenchelConjugate n f xStar).toReal : ℝ) : EReal) := by
    rw [EReal.coe_toReal hStarF_ne_top hStarF_ne_bot]
  have hstarg : fenchelConjugate n g xStar =
      (((fenchelConjugate n g xStar).toReal : ℝ) : EReal) := by
    rw [EReal.coe_toReal hStarG_ne_top hStarG_ne_bot]
  have hFYF' := hFYF
  rw [hfx, hstarf] at hFYF'
  have hFYG' := hFYG
  rw [hgx, hstarg] at hFYG'
  have hEqRealF :
      (f x).toReal + (fenchelConjugate n f xStar).toReal = dotProduct x xStar := by
    exact_mod_cast hFYF'
  have hEqRealG :
      (g x).toReal + (fenchelConjugate n g xStar).toReal = dotProduct x xStar := by
    exact_mod_cast hFYG'
  have hGapReal :
      (g x).toReal - (f x).toReal =
        (fenchelConjugate n f xStar).toReal - (fenchelConjugate n g xStar).toReal := by
    -- After coercing every finite value to `ℝ`, the two Fenchel-Young equalities differ by a
    -- purely real affine relation.
    linarith
  let α : ℝ := (fenchelConjugate n f xStar).toReal - (fenchelConjugate n g xStar).toReal
  have hReal : (g x).toReal = (f x).toReal + α := by
    dsimp [α]
    linarith
  refine ⟨α, ?_⟩
  calc
    g x = (((g x).toReal : ℝ) : EReal) := hgx
    _ = ((((f x).toReal + α : ℝ)) : EReal) := by
      exact congrArg (fun r : ℝ => (r : EReal)) hReal
    _ = (((f x).toReal : ℝ) : EReal) + ((α : ℝ) : EReal) := by
      rw [EReal.coe_add]
    _ = f x + ((α : ℝ) : EReal) := by
      rw [← hfx]

/-- Helper for Theorem 5.24.12: primal Euclideanized fiber inclusion transports to the Fenchel
conjugates by swapping the two Euclidean subgradient coordinates. -/
lemma helperForTheorem_5_24_12_conjugateFiberSubset_of_primalFiberSubset
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction f)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hclosedG : ClosedConvexFunction g)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hsubset : ∀ x : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ⊆
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x)) :
    ∀ xStar : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (fenchelConjugate n f) xStar) ⊆
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (fenchelConjugate n g) xStar) := by
  intro xStar v hv
  change dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt (fenchelConjugate n f) xStar at hv
  change dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt (fenchelConjugate n g) xStar
  have hvConjF : IsEuclideanSubgradientAt (fenchelConjugate n f) xStar v := by
    -- Read conjugate-fiber membership as a Euclidean subgradient statement.
    simpa [IsEuclideanSubgradientAt] using hv
  have hvPrimalF : IsEuclideanSubgradientAt f v xStar :=
    (euclidean_subgradient_fenchelConjugate_iff
      (f := f) hclosedF hproperF v xStar).1 hvConjF
  have hvMemPrimalF : xStar ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f v) := by
    -- Swap back to the primal coordinates before applying the assumed fiber inclusion.
    simpa [IsEuclideanSubgradientAt, dotProduct_comm] using hvPrimalF
  have hvMemPrimalG : xStar ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g v) :=
    hsubset v hvMemPrimalF
  have hvPrimalG : IsEuclideanSubgradientAt g v xStar := by
    -- Convert the included primal fiber point back into a Euclidean subgradient witness.
    simpa [IsEuclideanSubgradientAt, dotProduct_comm] using hvMemPrimalG
  have hvConjG : IsEuclideanSubgradientAt (fenchelConjugate n g) xStar v :=
    (euclidean_subgradient_fenchelConjugate_iff
      (f := g) hclosedG hproperG v xStar).2 hvPrimalG
  -- Swap once more to recover the conjugate-fiber inclusion.
  simpa [IsEuclideanSubgradientAt] using hvConjG

/-- Helper for Theorem 5.24.12: adding a finite real constant does not change Euclideanized
subdifferential fibers. -/
lemma helperForTheorem_5_24_12_subdifferential_eq_of_eq_add_constant
    {n : ℕ} {f g : (Fin n → ℝ) → EReal} {α : ℝ}
    (hEq : ∀ x : Fin n → ℝ, g x = f x + ((α : ℝ) : EReal)) :
    ∀ x : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) =
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x) := by
  intro x
  ext v
  constructor
  · intro hv
    change dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f x at hv
    change dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt g x
    rw [mem_subdifferentialAt_iff] at hv ⊢
    intro z
    -- Push the subgradient inequality for `f` through the common finite shift `α`.
    calc
      g z = f z + ((α : ℝ) : EReal) := hEq z
      _ ≥
          (f x + ((((dotProductEquiv ℝ (Fin n)) v) (z - x) : ℝ) : EReal)) +
            ((α : ℝ) : EReal) := by
        gcongr
        exact hv z
      _ = g x + ((((dotProductEquiv ℝ (Fin n)) v) (z - x) : ℝ) : EReal) := by
        rw [hEq x]
        simp [add_assoc, add_left_comm, add_comm]
  · intro hv
    change dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt g x at hv
    change dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f x
    rw [mem_subdifferentialAt_iff] at hv ⊢
    have hEqSymm : ∀ z : Fin n → ℝ, f z = g z + (((-α : ℝ)) : EReal) := by
      intro z
      have hcancel : ((α : ℝ) : EReal) + (((-α : ℝ)) : EReal) = 0 := by
        rw [← EReal.coe_add]
        norm_num
      have htmp :
          g z + (((-α : ℝ)) : EReal) = f z := by
        have htmp0 := congrArg (fun t : EReal => t + (((-α : ℝ)) : EReal)) (hEq z)
        calc
          g z + (((-α : ℝ)) : EReal) = (f z + ((α : ℝ) : EReal)) + (((-α : ℝ)) : EReal) :=
            htmp0
          _ = f z + (((α : ℝ) : EReal) + (((-α : ℝ)) : EReal)) := by
            simp [add_assoc]
          _ = f z + 0 := by rw [hcancel]
          _ = f z := by simp
      exact htmp.symm
    intro z
    -- Apply the same argument in reverse after rewriting `f` as `g` shifted by `-α`.
    calc
      f z = g z + (((-α : ℝ)) : EReal) := hEqSymm z
      _ ≥
          (g x + ((((dotProductEquiv ℝ (Fin n)) v) (z - x) : ℝ) : EReal)) +
            (((-α : ℝ)) : EReal) := by
        gcongr
        exact hv z
      _ = f x + ((((dotProductEquiv ℝ (Fin n)) v) (z - x) : ℝ) : EReal) := by
        rw [hEqSymm x]
        simp [add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 5.24.12: primal Euclideanized fiber inclusion persists after passing to a
fixed-step secant quotient based at a finite anchor point. -/
lemma helperForTheorem_5_24_12_secantQuotientFiberSubset_of_primalFiberSubset
    {n : ℕ} (f g : (Fin n → ℝ) → EReal)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g)
    (hsubset : ∀ x : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ⊆
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x))
    {x u : Fin n → ℝ} {t : ℝ}
    (hxFiniteF : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hxFiniteG : g x ≠ (⊤ : EReal) ∧ g x ≠ (⊥ : EReal))
    (huFiniteF : f (x + t • u) ≠ (⊤ : EReal) ∧ f (x + t • u) ≠ (⊥ : EReal))
    (huFiniteG : g (x + t • u) ≠ (⊤ : EReal) ∧ g (x + t • u) ≠ (⊥ : EReal))
    (ht : 0 < t) :
    ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt
        (fun v => directionalDifferenceQuotientAt f x v t) u) ⊆
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt
        (fun v => directionalDifferenceQuotientAt g x v t) u) := by
  intro v hv
  have hf : ConvexFunction f := by
    -- The secant-quotient transport theorem expects the ambient convexity of `f`.
    simpa [ConvexFunction] using hproperF.1
  have hg : ConvexFunction g := by
    -- The same convexity package is needed on the `g` side.
    simpa [ConvexFunction] using hproperG.1
  have hvPrimal :
      v ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f (x + t • u)) := by
    -- Move the secant-quotient fiber back to the translated primal fiber of `f`.
    simpa [helperForTheorem_5_24_9_secantQuotient_subdifferential_transport
      (f := f) hproperF hf (x := x) (u := u) (t := t) hxFiniteF huFiniteF ht] using hv
  have hvPrimalG :
      v ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g (x + t • u)) :=
    hsubset (x + t • u) hvPrimal
  -- Transport the included primal witness back to the secant quotient of `g`.
  simpa [helperForTheorem_5_24_9_secantQuotient_subdifferential_transport
    (f := g) hproperG hg (x := x) (u := u) (t := t) hxFiniteG huFiniteG ht] using hvPrimalG

/-- Helper for Theorem 5.24.12: once two nonempty scalar interval fibers are written with finite
endpoints, equality of the interval sets forces equality of the two endpoint pairs. -/
lemma helperForTheorem_5_24_12_intervalSetEq_implies_derivativeEndpointsEq
    {a1 b1 a2 b2 : EReal}
    (ha1_top : a1 ≠ (⊤ : EReal)) (ha1_bot : a1 ≠ (⊥ : EReal))
    (hb1_top : b1 ≠ (⊤ : EReal)) (hb1_bot : b1 ≠ (⊥ : EReal))
    (ha2_top : a2 ≠ (⊤ : EReal)) (ha2_bot : a2 ≠ (⊥ : EReal))
    (hb2_top : b2 ≠ (⊤ : EReal)) (hb2_bot : b2 ≠ (⊥ : EReal))
    (hNonempty :
      Set.Nonempty {x : ℝ | a1 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b1)})
    (hEq :
      {x : ℝ | a1 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b1)} =
        {x : ℝ | a2 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b2)}) :
    a1 = a2 ∧ b1 = b2 := by
  let ra1 : ℝ := a1.toReal
  let rb1 : ℝ := b1.toReal
  let ra2 : ℝ := a2.toReal
  let rb2 : ℝ := b2.toReal
  have ha1_coe : a1 = ((ra1 : ℝ) : EReal) := by
    -- Finite endpoints can be rewritten as coerced real numbers.
    simp [ra1, EReal.coe_toReal ha1_top ha1_bot]
  have hb1_coe : b1 = ((rb1 : ℝ) : EReal) := by
    -- The same finite-endpoint reduction applies on the upper side.
    simp [rb1, EReal.coe_toReal hb1_top hb1_bot]
  have ha2_coe : a2 = ((ra2 : ℝ) : EReal) := by
    -- Rewrite the second lower endpoint as a real coercion.
    simp [ra2, EReal.coe_toReal ha2_top ha2_bot]
  have hb2_coe : b2 = ((rb2 : ℝ) : EReal) := by
    -- Rewrite the second upper endpoint as a real coercion.
    simp [rb2, EReal.coe_toReal hb2_top hb2_bot]
  have hSet1 :
      {x : ℝ | a1 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b1)} = Set.Icc ra1 rb1 := by
    -- After coercing the finite endpoints to `ℝ`, the scalar fiber is an ordinary closed interval.
    ext x
    constructor
    · intro hx
      constructor
      · have hxLeft : a1 ≤ ((x : ℝ) : EReal) := hx.1
        rw [ha1_coe] at hxLeft
        exact_mod_cast hxLeft
      · have hxRight : ((x : ℝ) : EReal) ≤ b1 := hx.2
        rw [hb1_coe] at hxRight
        exact_mod_cast hxRight
    · intro hx
      constructor
      · rw [ha1_coe]
        exact_mod_cast hx.1
      · rw [hb1_coe]
        exact_mod_cast hx.2
  have hSet2 :
      {x : ℝ | a2 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b2)} = Set.Icc ra2 rb2 := by
    -- The second scalar fiber has the same interval form.
    ext x
    constructor
    · intro hx
      constructor
      · have hxLeft : a2 ≤ ((x : ℝ) : EReal) := hx.1
        rw [ha2_coe] at hxLeft
        exact_mod_cast hxLeft
      · have hxRight : ((x : ℝ) : EReal) ≤ b2 := hx.2
        rw [hb2_coe] at hxRight
        exact_mod_cast hxRight
    · intro hx
      constructor
      · rw [ha2_coe]
        exact_mod_cast hx.1
      · rw [hb2_coe]
        exact_mod_cast hx.2
  rcases hNonempty with ⟨x0, hx0⟩
  have hx0Icc : x0 ∈ Set.Icc ra1 rb1 := by
    -- Convert the chosen point of the first interval set into ordinary interval membership.
    rw [hSet1] at hx0
    exact hx0
  have hra1_rb1 : ra1 ≤ rb1 := by
    -- Nonemptiness of the first interval provides the order hypothesis for `Set.Icc_eq_Icc_iff`.
    exact le_trans hx0Icc.1 hx0Icc.2
  have hEqIcc : Set.Icc ra1 rb1 = Set.Icc ra2 rb2 := by
    -- Replace both scalar-fiber descriptions by the corresponding real intervals.
    calc
      Set.Icc ra1 rb1 =
          {x : ℝ | a1 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b1)} := hSet1.symm
      _ = {x : ℝ | a2 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b2)} := hEq
      _ = Set.Icc ra2 rb2 := hSet2
  have hEndpoints : ra1 = ra2 ∧ rb1 = rb2 :=
    (Set.Icc_eq_Icc_iff hra1_rb1).1 hEqIcc
  constructor
  · -- Equality of the lower real endpoints lifts back to equality in `EReal`.
    calc
      a1 = ((ra1 : ℝ) : EReal) := ha1_coe
      _ = ((ra2 : ℝ) : EReal) := by
        exact congrArg (fun r : ℝ => ((r : ℝ) : EReal)) hEndpoints.1
      _ = a2 := ha2_coe.symm
  · -- The upper endpoints are handled in the same way.
    calc
      b1 = ((rb1 : ℝ) : EReal) := hb1_coe
      _ = ((rb2 : ℝ) : EReal) := by
        exact congrArg (fun r : ℝ => ((r : ℝ) : EReal)) hEndpoints.2
      _ = b2 := hb2_coe.symm

/-- Helper for Theorem 5.24.12: inclusion of two finite nonempty scalar interval fibers already
forces the corresponding derivative-band bounds in the only direction available from the
inclusion. -/
lemma helperForTheorem_5_24_12_intervalSubset_implies_derivativeBandBounds
    {a1 b1 a2 b2 : EReal}
    (ha1_top : a1 ≠ (⊤ : EReal)) (ha1_bot : a1 ≠ (⊥ : EReal))
    (hb1_top : b1 ≠ (⊤ : EReal)) (hb1_bot : b1 ≠ (⊥ : EReal))
    (_ha2_top : a2 ≠ (⊤ : EReal)) (_ha2_bot : a2 ≠ (⊥ : EReal))
    (_hb2_top : b2 ≠ (⊤ : EReal)) (_hb2_bot : b2 ≠ (⊥ : EReal))
    (hNonempty :
      Set.Nonempty {x : ℝ | a1 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b1)})
    (hSubset :
      {x : ℝ | a1 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b1)} ⊆
        {x : ℝ | a2 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b2)}) :
    a2 ≤ a1 ∧ b1 ≤ b2 := by
  let ra1 : ℝ := a1.toReal
  let rb1 : ℝ := b1.toReal
  have ha1_coe : a1 = ((ra1 : ℝ) : EReal) := by
    -- Finite endpoints can be rewritten as coerced real numbers.
    simp [ra1, EReal.coe_toReal ha1_top ha1_bot]
  have hb1_coe : b1 = ((rb1 : ℝ) : EReal) := by
    -- The same reduction holds for the upper endpoint.
    simp [rb1, EReal.coe_toReal hb1_top hb1_bot]
  rcases hNonempty with ⟨x0, hx0⟩
  have hLowerLeUpper : ra1 ≤ rb1 := by
    -- Any point of the first scalar fiber witnesses that its lower endpoint lies below its upper
    -- endpoint once both are viewed in `ℝ`.
    have hx0Left : a1 ≤ ((x0 : ℝ) : EReal) := hx0.1
    have hx0Right : ((x0 : ℝ) : EReal) ≤ b1 := hx0.2
    rw [ha1_coe] at hx0Left
    rw [hb1_coe] at hx0Right
    exact le_trans (by exact_mod_cast hx0Left) (by exact_mod_cast hx0Right)
  have hra1_mem :
      ra1 ∈ {x : ℝ | a1 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b1)} := by
    -- The lower endpoint belongs to the first interval because it lies below the upper endpoint.
    constructor
    · rw [ha1_coe]
    · rw [hb1_coe]
      exact_mod_cast hLowerLeUpper
  have hrb1_mem :
      rb1 ∈ {x : ℝ | a1 ≤ ((x : ℝ) : EReal) ∧ (((x : ℝ) : EReal) ≤ b1)} := by
    -- The upper endpoint belongs to the first interval for the same reason.
    constructor
    · rw [ha1_coe]
      exact_mod_cast hLowerLeUpper
    · rw [hb1_coe]
  have hra1_mem' := hSubset hra1_mem
  have hrb1_mem' := hSubset hrb1_mem
  constructor
  · -- Evaluating the inclusion at the first lower endpoint gives the lower-band inequality.
    calc
      a2 ≤ ((ra1 : ℝ) : EReal) := hra1_mem'.1
      _ = a1 := ha1_coe.symm
  · -- Evaluating the inclusion at the first upper endpoint gives the upper-band inequality.
    calc
      b1 = ((rb1 : ℝ) : EReal) := hb1_coe
      _ ≤ b2 := hrb1_mem'.2

/-- Helper for Theorem 5.24.12: once scalar fiber inclusion is rewritten through Theorem 5.24.2,
the only remaining information is the corresponding one-sided derivative-band bounds. -/
lemma helperForTheorem_5_24_12_scalarRestrictionDerivativeBandBounds_of_primalFiberSubset
    (F G : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hclosedG : ClosedConvexFunction G)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    {t : ℝ}
    (htF : t ∈ interior (scalarEffectiveDomain F))
    (htG : t ∈ interior (scalarEffectiveDomain G))
    (hFiberSubset :
      {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ F (scalarPoint t)} ⊆
        {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ G (scalarPoint t)}) :
    leftDerivativeExtension G t ≤ leftDerivativeExtension F t ∧
      rightDerivativeExtension F t ≤ rightDerivativeExtension G t := by
  have hBandsF :
      {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ F (scalarPoint t)} =
        {xStar : ℝ |
          leftDerivativeExtension F t ≤ ((xStar : ℝ) : EReal) ∧
            (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension F t)} := by
    -- Rewrite the scalar subdifferential fiber of `F` as its derivative interval.
    simpa using
      oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
        F hclosedF hproperF t
  have hBandsG :
      {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ G (scalarPoint t)} =
        {xStar : ℝ |
          leftDerivativeExtension G t ≤ ((xStar : ℝ) : EReal) ∧
            (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension G t)} := by
    -- The same interval description applies to `G`.
    simpa using
      oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
        G hclosedG hproperG t
  have hFiniteF :=
    helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives F hproperF htF
  have hFiniteG :=
    helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives G hproperG htG
  have hMidpointLeF :
      (leftDerivativeExtension F t).toReal ≤
        ((leftDerivativeExtension F t).toReal + (rightDerivativeExtension F t).toReal) / 2 := by
    have hLe :
        ((leftDerivativeExtension F t).toReal : EReal) ≤
          (((rightDerivativeExtension F t).toReal : ℝ) : EReal) := by
      -- Finiteness lets us compare the interval endpoints inside `ℝ`.
      calc
        (((leftDerivativeExtension F t).toReal : ℝ) : EReal) = leftDerivativeExtension F t := by
          rw [EReal.coe_toReal hFiniteF.2.2.1 hFiniteF.2.2.2]
        _ ≤ rightDerivativeExtension F t :=
          helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
            F hproperF t
        _ = (((rightDerivativeExtension F t).toReal : ℝ) : EReal) := by
          rw [EReal.coe_toReal hFiniteF.1 hFiniteF.2.1]
    have hLeReal :
        (leftDerivativeExtension F t).toReal ≤ (rightDerivativeExtension F t).toReal := by
      exact_mod_cast hLe
    linarith
  have hMidpointGeF :
      ((leftDerivativeExtension F t).toReal + (rightDerivativeExtension F t).toReal) / 2 ≤
        (rightDerivativeExtension F t).toReal := by
    have hLe :
        ((leftDerivativeExtension F t).toReal : EReal) ≤
          (((rightDerivativeExtension F t).toReal : ℝ) : EReal) := by
      -- The same order relation places the midpoint below the upper endpoint.
      calc
        (((leftDerivativeExtension F t).toReal : ℝ) : EReal) = leftDerivativeExtension F t := by
          rw [EReal.coe_toReal hFiniteF.2.2.1 hFiniteF.2.2.2]
        _ ≤ rightDerivativeExtension F t :=
          helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
            F hproperF t
        _ = (((rightDerivativeExtension F t).toReal : ℝ) : EReal) := by
          rw [EReal.coe_toReal hFiniteF.1 hFiniteF.2.1]
    have hLeReal :
        (leftDerivativeExtension F t).toReal ≤ (rightDerivativeExtension F t).toReal := by
      exact_mod_cast hLe
    linarith
  have hNonemptyF :
      Set.Nonempty
        {xStar : ℝ |
          leftDerivativeExtension F t ≤ ((xStar : ℝ) : EReal) ∧
            (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension F t)} := by
    let xMid : ℝ :=
      ((leftDerivativeExtension F t).toReal + (rightDerivativeExtension F t).toReal) / 2
    have hLeft :
        leftDerivativeExtension F t ≤ ((xMid : ℝ) : EReal) := by
      -- Choose the midpoint of the finite interval as a concrete point in the fiber.
      calc
        leftDerivativeExtension F t = (((leftDerivativeExtension F t).toReal : ℝ) : EReal) := by
          rw [EReal.coe_toReal hFiniteF.2.2.1 hFiniteF.2.2.2]
        _ ≤ ((xMid : ℝ) : EReal) := by
          exact_mod_cast hMidpointLeF
    have hRight :
        ((xMid : ℝ) : EReal) ≤ rightDerivativeExtension F t := by
      -- The midpoint also stays below the upper endpoint.
      calc
        ((xMid : ℝ) : EReal) ≤ (((rightDerivativeExtension F t).toReal : ℝ) : EReal) := by
          exact_mod_cast hMidpointGeF
        _ = rightDerivativeExtension F t := by
          rw [EReal.coe_toReal hFiniteF.1 hFiniteF.2.1]
    exact ⟨xMid, And.intro hLeft hRight⟩
  have hIntervalSubset :
      {xStar : ℝ |
        leftDerivativeExtension F t ≤ ((xStar : ℝ) : EReal) ∧
          (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension F t)} ⊆
        {xStar : ℝ |
          leftDerivativeExtension G t ≤ ((xStar : ℝ) : EReal) ∧
            (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension G t)} := by
    -- Rewrite the fiber inclusion through the interval descriptions on both sides.
    intro xStar hxStar
    have hxFiber :
        xStar ∈ {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ F (scalarPoint t)} := by
      rw [← hBandsF] at hxStar
      exact hxStar
    have hxFiber' :
        xStar ∈ {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ G (scalarPoint t)} :=
      hFiberSubset hxFiber
    rw [← hBandsG]
    exact hxFiber'
  exact
    helperForTheorem_5_24_12_intervalSubset_implies_derivativeBandBounds
      hFiniteF.2.2.1 hFiniteF.2.2.2 hFiniteF.1 hFiniteF.2.1
      hFiniteG.2.2.1 hFiniteG.2.2.2 hFiniteG.1 hFiniteG.2.1
      hNonemptyF hIntervalSubset

/-- Helper for Theorem 5.24.12: once the scalar derivative-band inequalities hold on every point
of an open interval, the one-sided continuity of the derivative extensions upgrades them to
pointwise equality of the left and right derivative extensions on that interval. -/
lemma helperForTheorem_5_24_12_derivativeBandBounds_on_Ioo_imply_scalarDerivativeExtensionsEq
    (F G : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hclosedG : ClosedConvexFunction G)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    {a b : ℝ} (_hab : a < b)
    (hband : ∀ t ∈ Set.Ioo a b,
      leftDerivativeExtension G t ≤ leftDerivativeExtension F t ∧
        rightDerivativeExtension F t ≤ rightDerivativeExtension G t) :
    ∀ x ∈ Set.Ioo a b,
      leftDerivativeExtension G x = leftDerivativeExtension F x ∧
        rightDerivativeExtension F x = rightDerivativeExtension G x := by
  rcases
      oneDimensional_derivativeExtensions_monotone_ordered_and_oneSidedContinuous
        F hclosedF hproperF with
    ⟨_hmonoRightF, _hmonoLeftF, _hfiniteF, _horderedF,
      _hRightRightF, hRightLeftF, hLeftRightF, _hLeftLeftF⟩
  rcases
      oneDimensional_derivativeExtensions_monotone_ordered_and_oneSidedContinuous
        G hclosedG hproperG with
    ⟨_hmonoRightG, _hmonoLeftG, _hfiniteG, _horderedG,
      _hRightRightG, hRightLeftG, hLeftRightG, _hLeftLeftG⟩
  intro x hx
  have hLeftLe : leftDerivativeExtension G x ≤ leftDerivativeExtension F x :=
    (hband x hx).1
  have hRightLe : rightDerivativeExtension F x ≤ rightDerivativeExtension G x :=
    (hband x hx).2
  have hLeftGe : leftDerivativeExtension F x ≤ leftDerivativeExtension G x := by
    have hneLeft : (nhdsWithin x (Set.Iio x)).NeBot := by
      refine nhdsWithin_Iio_self_neBot' ?_
      exact ⟨x - 1, by simp⟩
    have hTailLe :
        (nhdsWithin x (Set.Iio x)).EventuallyLE
          (fun z : ℝ => rightDerivativeExtension F z)
          (fun z : ℝ => rightDerivativeExtension G z) := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hx.1]
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hband z ⟨hz.1, lt_trans hz.2 hx.2⟩).2
    -- Compare the left limits by transporting the right-derivative inequality from the strict
    -- left tail to the endpoint `x`.
    exact
      le_of_tendsto_of_tendsto
        (by simpa using hRightLeftF x)
        (by simpa using hRightLeftG x)
        hTailLe
  have hRightGe : rightDerivativeExtension G x ≤ rightDerivativeExtension F x := by
    have hneRight : (nhdsWithin x (Set.Ioi x)).NeBot := by
      exact nhdsWithin_Ioi_neBot (show x ≤ x by rfl)
    have hTailLe :
        (nhdsWithin x (Set.Ioi x)).EventuallyLE
          (fun z : ℝ => leftDerivativeExtension G z)
          (fun z : ℝ => leftDerivativeExtension F z) := by
      rw [← nhdsWithin_Ioo_eq_nhdsGT hx.2]
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (hband z ⟨lt_trans hx.1 hz.1, hz.2⟩).1
    -- Apply the same limit comparison on the strict right tail, now using the left derivatives
    -- which converge to the right derivative at `x`.
    exact
      le_of_tendsto_of_tendsto
        (by simpa using hLeftRightG x)
        (by simpa using hLeftRightF x)
        hTailLe
  exact ⟨le_antisymm hLeftLe hLeftGe, le_antisymm hRightLe hRightGe⟩

/-- Helper for Theorem 5.24.12: if two one-dimensional scalar restrictions have the same scalar
subdifferential fiber at an interior point, then their left and right derivative bands agree at
that point. -/
lemma helperForTheorem_5_24_12_scalarRestrictionDerivativeBands_eq_of_commonScalarFibers
    (F G : (Fin 1 → ℝ) → EReal)
    (hclosedF : ClosedConvexFunction F)
    (hproperF : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) F)
    (hclosedG : ClosedConvexFunction G)
    (hproperG : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) G)
    {t : ℝ}
    (htF : t ∈ interior (scalarEffectiveDomain F))
    (htG : t ∈ interior (scalarEffectiveDomain G))
    (hFiberEq :
      {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ F (scalarPoint t)} =
        {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ G (scalarPoint t)}) :
    leftDerivativeExtension F t = leftDerivativeExtension G t ∧
      rightDerivativeExtension F t = rightDerivativeExtension G t := by
  have hBandsF :
      {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ F (scalarPoint t)} =
        {xStar : ℝ |
          leftDerivativeExtension F t ≤ ((xStar : ℝ) : EReal) ∧
            (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension F t)} := by
    -- Theorem 5.24.2 rewrites the scalar subdifferential fiber as the derivative interval.
    simpa using
      oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
        F hclosedF hproperF t
  have hBandsG :
      {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ G (scalarPoint t)} =
        {xStar : ℝ |
          leftDerivativeExtension G t ≤ ((xStar : ℝ) : EReal) ∧
            (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension G t)} := by
    -- The same scalar interval description holds for `G`.
    simpa using
      oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
        G hclosedG hproperG t
  have hFiniteF :=
    helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives F hproperF htF
  have hFiniteG :=
    helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives G hproperG htG
  have hMidpointLeF :
      (leftDerivativeExtension F t).toReal ≤
        ((leftDerivativeExtension F t).toReal + (rightDerivativeExtension F t).toReal) / 2 := by
    have hLe :
        ((leftDerivativeExtension F t).toReal : EReal) ≤
          (((rightDerivativeExtension F t).toReal : ℝ) : EReal) := by
      -- Finiteness lets us rewrite both derivative endpoints as real coercions.
      calc
        (((leftDerivativeExtension F t).toReal : ℝ) : EReal) = leftDerivativeExtension F t := by
          rw [EReal.coe_toReal hFiniteF.2.2.1 hFiniteF.2.2.2]
        _ ≤ rightDerivativeExtension F t :=
          helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
            F hproperF t
        _ = (((rightDerivativeExtension F t).toReal : ℝ) : EReal) := by
          rw [EReal.coe_toReal hFiniteF.1 hFiniteF.2.1]
    have hLeReal :
        (leftDerivativeExtension F t).toReal ≤ (rightDerivativeExtension F t).toReal := by
      exact_mod_cast hLe
    linarith
  have hMidpointGeF :
      ((leftDerivativeExtension F t).toReal + (rightDerivativeExtension F t).toReal) / 2 ≤
        (rightDerivativeExtension F t).toReal := by
    have hLe :
        ((leftDerivativeExtension F t).toReal : EReal) ≤
          (((rightDerivativeExtension F t).toReal : ℝ) : EReal) := by
      -- The same order relation bounds the midpoint from above by the right endpoint.
      calc
        (((leftDerivativeExtension F t).toReal : ℝ) : EReal) = leftDerivativeExtension F t := by
          rw [EReal.coe_toReal hFiniteF.2.2.1 hFiniteF.2.2.2]
        _ ≤ rightDerivativeExtension F t :=
          helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
            F hproperF t
        _ = (((rightDerivativeExtension F t).toReal : ℝ) : EReal) := by
          rw [EReal.coe_toReal hFiniteF.1 hFiniteF.2.1]
    have hLeReal :
        (leftDerivativeExtension F t).toReal ≤ (rightDerivativeExtension F t).toReal := by
      exact_mod_cast hLe
    linarith
  have hNonemptyF :
      Set.Nonempty
        {xStar : ℝ |
          leftDerivativeExtension F t ≤ ((xStar : ℝ) : EReal) ∧
            (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension F t)} := by
    let xMid : ℝ :=
      ((leftDerivativeExtension F t).toReal + (rightDerivativeExtension F t).toReal) / 2
    have hLeft :
        leftDerivativeExtension F t ≤ ((xMid : ℝ) : EReal) := by
      -- Choose the midpoint of the finite interval as an explicit point of the scalar fiber.
      calc
        leftDerivativeExtension F t = (((leftDerivativeExtension F t).toReal : ℝ) : EReal) := by
          rw [EReal.coe_toReal hFiniteF.2.2.1 hFiniteF.2.2.2]
        _ ≤ ((xMid : ℝ) : EReal) := by
          exact_mod_cast hMidpointLeF
    have hRight :
        ((xMid : ℝ) : EReal) ≤ rightDerivativeExtension F t := by
      -- The midpoint also lies below the right endpoint.
      calc
        ((xMid : ℝ) : EReal) ≤ (((rightDerivativeExtension F t).toReal : ℝ) : EReal) := by
          exact_mod_cast hMidpointGeF
        _ = rightDerivativeExtension F t := by
          rw [EReal.coe_toReal hFiniteF.1 hFiniteF.2.1]
    exact ⟨xMid, And.intro hLeft hRight⟩
  have hIntervalEq :
      {xStar : ℝ |
        leftDerivativeExtension F t ≤ ((xStar : ℝ) : EReal) ∧
          (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension F t)} =
        {xStar : ℝ |
          leftDerivativeExtension G t ≤ ((xStar : ℝ) : EReal) ∧
            (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension G t)} := by
    -- Rewrite the common scalar fiber equality through the interval description on both sides.
    calc
      {xStar : ℝ |
          leftDerivativeExtension F t ≤ ((xStar : ℝ) : EReal) ∧
            (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension F t)} =
          {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ F (scalarPoint t)} := by
            exact hBandsF.symm
      _ = {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ G (scalarPoint t)} :=
            hFiberEq
      _ = {xStar : ℝ |
            leftDerivativeExtension G t ≤ ((xStar : ℝ) : EReal) ∧
              (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension G t)} := hBandsG
  have hEndpoints :=
    helperForTheorem_5_24_12_intervalSetEq_implies_derivativeEndpointsEq
      hFiniteF.2.2.1 hFiniteF.2.2.2 hFiniteF.1 hFiniteF.2.1
      hFiniteG.2.2.1 hFiniteG.2.2.2 hFiniteG.1 hFiniteG.2.1
      hNonemptyF hIntervalEq
  exact ⟨hEndpoints.1, hEndpoints.2⟩

/-- Helper for Theorem 5.24.12: translating by a fixed primal base point rewrites the
Euclideanized subdifferential fiber of the translated-difference function as the original fiber
at the shifted point. -/
lemma helperForTheorem_5_24_12_translatedDifference_subdifferential_eq_shifted
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x z : Fin n → ℝ)
    (hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (translatedDifferenceFunctionAt f x) z) =
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f (x + z)) := by
  let β : ℝ := (f x).toReal
  have hβ : f x = ((β : ℝ) : EReal) := by
    simp [β, EReal.coe_toReal, hxFinite.1, hxFinite.2]
  ext v
  constructor
  · intro hv
    change dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt (translatedDifferenceFunctionAt f x) z
      at hv
    change dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f (x + z)
    rw [mem_subdifferentialAt_iff] at hv ⊢
    intro w
    -- Evaluate the translated subgradient inequality at `w - x` so that the translated endpoint
    -- collapses back to the original primal point `w`.
    have hv' :
        (f (x + z) - ((β : ℝ) : EReal)) +
            ((((dotProductEquiv ℝ (Fin n)) v) (w - (x + z)) : ℝ) : EReal) ≤
          f w - ((β : ℝ) : EReal) := by
      simpa [translatedDifferenceFunctionAt, hβ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using hv (w - x)
    have hv'' :
        ((f (x + z) - ((β : ℝ) : EReal)) +
            ((((dotProductEquiv ℝ (Fin n)) v) (w - (x + z)) : ℝ) : EReal)) +
          ((β : ℝ) : EReal) ≤
        f w := by
      exact
        (EReal.le_sub_iff_add_le
          (a := (f (x + z) - ((β : ℝ) : EReal)) +
            ((((dotProductEquiv ℝ (Fin n)) v) (w - (x + z)) : ℝ) : EReal))
          (b := ((β : ℝ) : EReal))
          (c := f w)
          (Or.inl (by simp))
          (Or.inl (by simp))).1 hv'
    have hcancel :
        (f (x + z) - ((β : ℝ) : EReal)) + ((β : ℝ) : EReal) = f (x + z) := by
      simpa using (EReal.sub_add_cancel (a := f (x + z)) (b := β))
    have hcancel' :
        ((β : ℝ) : EReal) + (f (x + z) - ((β : ℝ) : EReal)) = f (x + z) := by
      calc
        ((β : ℝ) : EReal) + (f (x + z) - ((β : ℝ) : EReal)) =
            (f (x + z) - ((β : ℝ) : EReal)) + ((β : ℝ) : EReal) := by
              simp [add_comm]
        _ = f (x + z) := hcancel
    simpa [hcancel, hcancel', add_assoc, add_left_comm, add_comm] using hv''
  · intro hv
    change dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f (x + z) at hv
    change dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt (translatedDifferenceFunctionAt f x) z
    rw [mem_subdifferentialAt_iff] at hv ⊢
    intro w
    -- Conversely, evaluate the original subgradient inequality at the shifted point `x + w`.
    have hv' :
        f (x + z) +
            ((((dotProductEquiv ℝ (Fin n)) v) ((x + w) - (x + z)) : ℝ) : EReal) ≤
          f (x + w) := hv (x + w)
    have hshiftSub : (x + w) - (x + z) = w - z := by
      ext i
      simp [Pi.add_apply, Pi.sub_apply, sub_eq_add_neg]
      ring
    have hcancel :
        (f (x + z) - ((β : ℝ) : EReal)) + ((β : ℝ) : EReal) = f (x + z) := by
      simpa using (EReal.sub_add_cancel (a := f (x + z)) (b := β))
    have hv'' :
        (f (x + z) - ((β : ℝ) : EReal)) +
            ((((dotProductEquiv ℝ (Fin n)) v) (w - z) : ℝ) : EReal) ≤
          f (x + w) - ((β : ℝ) : EReal) := by
      apply
        (EReal.le_sub_iff_add_le
          (a := (f (x + z) - ((β : ℝ) : EReal)) +
            ((((dotProductEquiv ℝ (Fin n)) v) (w - z) : ℝ) : EReal))
          (b := ((β : ℝ) : EReal))
          (c := f (x + w))
          (Or.inl (by simp))
          (Or.inl (by simp))).2
      have hbetaCancel :
          ((β : ℝ) : EReal) + (-((β : ℝ) : EReal) + f (x + z)) = f (x + z) := by
        have hbetaZero : ((β : ℝ) : EReal) + (-((β : ℝ) : EReal)) = 0 := by
          rw [← EReal.coe_neg, ← EReal.coe_add]
          norm_num
        calc
          ((β : ℝ) : EReal) + (-((β : ℝ) : EReal) + f (x + z)) =
              ((((β : ℝ) : EReal) + (-((β : ℝ) : EReal))) + f (x + z)) := by
                rw [add_assoc]
          _ = f (x + z) := by
                rw [hbetaZero]
                simp
      simpa [hshiftSub, hbetaCancel, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        using hv'
    simpa [translatedDifferenceFunctionAt, hβ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      using hv''

/-- Helper for Theorem 5.24.12: pointwise Euclideanized primal-fiber inclusion is preserved after
translating both functions by the same base point and subtracting the corresponding base value. -/
lemma helperForTheorem_5_24_12_translatedDifferenceFiberSubset_of_primalFiberSubset
    {n : ℕ} (f g : (Fin n → ℝ) → EReal) (x0 : Fin n → ℝ)
    (hx0FiniteF : f x0 ≠ (⊤ : EReal) ∧ f x0 ≠ (⊥ : EReal))
    (hx0FiniteG : g x0 ≠ (⊤ : EReal) ∧ g x0 ≠ (⊥ : EReal))
    (hsubset : ∀ x : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ⊆
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x)) :
    ∀ z : Fin n → ℝ,
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (translatedDifferenceFunctionAt f x0) z) ⊆
        ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (translatedDifferenceFunctionAt g x0) z) := by
  intro z v hv
  have hvShift :
      v ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f (x0 + z)) := by
    -- Rewrite the translated fiber back to the shifted primal point before applying `hsubset`.
    simpa [helperForTheorem_5_24_12_translatedDifference_subdifferential_eq_shifted,
      hx0FiniteF]
      using hv
  have hvShift' :
      v ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g (x0 + z)) :=
    hsubset (x0 + z) hvShift
  -- Translate the included primal witness back to the translated-difference fiber of `g`.
  simpa [helperForTheorem_5_24_12_translatedDifference_subdifferential_eq_shifted,
    hx0FiniteG]
    using hvShift'

/-- Helper for Theorem 5.24.12: the translated-difference function vanishes at the origin when the
base value is finite. -/
lemma helperForTheorem_5_24_12_translatedDifference_zero
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    translatedDifferenceFunctionAt f x 0 = 0 := by
  -- Evaluate the translated difference at the zero direction and cancel the finite base value.
  simp [translatedDifferenceFunctionAt, EReal.sub_self hx.1 hx.2]

/-- Helper for Theorem 5.24.12: translated differences inherit proper convexity from the original
proper convex function. -/
lemma helperForTheorem_5_24_12_translatedDifference_properConvex
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (translatedDifferenceFunctionAt f x) := by
  let β : ℝ := (f x).toReal
  have hβ : ((β : ℝ) : EReal) = f x := by
    -- Finiteness at the anchor lets us rewrite the subtracted value as a real constant.
    simp [β, EReal.coe_toReal, hx.1, hx.2]
  have htranslate :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun z => f (z - (-x))) :=
    properConvexFunctionOn_translate (n := n) (a := -x) hproper
  have hconst :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun _ : Fin n → ℝ => (((-β : ℝ)) : EReal)) :=
    properConvexFunctionOn_const (n := n) (-β)
  have hrepr :
      translatedDifferenceFunctionAt f x =
        fun z => f (z - (-x)) + (((-β : ℝ)) : EReal) := by
    -- Rewrite the translated difference as a translate plus a finite constant shift.
    funext z
    simp [translatedDifferenceFunctionAt, hβ, sub_eq_add_neg, add_comm]
  refine ⟨?_, ?_, ?_⟩
  · -- Convexity is stable under adding a finite constant after translation.
    rw [hrepr]
    exact convexFunctionOn_add_of_proper (n := n) htranslate hconst
  · -- The origin remains a finite epigraph point after the normalization.
    refine ⟨(0, 0), ?_⟩
    constructor
    · exact Set.mem_univ 0
    · simp [helperForTheorem_5_24_12_translatedDifference_zero (f := f) x hx]
  · -- Properness still excludes `⊥` everywhere after subtracting the finite anchor value.
    intro z _
    have hxz : f (x + z) ≠ (⊥ : EReal) := hproper.2.2 (x + z) (by simp)
    simp [translatedDifferenceFunctionAt, sub_eq_add_neg, hxz, hx.1]

/-- Helper for Theorem 5.24.12: translated differences of closed proper convex functions remain
closed. -/
lemma helperForTheorem_5_24_12_translatedDifference_closed
    {n : ℕ} (f : (Fin n → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (x : Fin n → ℝ) (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    ClosedConvexFunction (translatedDifferenceFunctionAt f x) := by
  let g : (Fin n → ℝ) → EReal := translatedDifferenceFunctionAt f x
  let β : ℝ := (f x).toReal
  have hβ : ((β : ℝ) : EReal) = f x := by
    -- The translated-difference normalization subtracts a genuine finite real constant.
    simp [β, EReal.coe_toReal, hx.1, hx.2]
  have hg_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g :=
    helperForTheorem_5_24_12_translatedDifference_properConvex (f := f) hproper x hx
  have hg_lsc : LowerSemicontinuous g := by
    -- Closed sublevel sets are preserved under translation and subtraction of the finite anchor
    -- value.
    rw [lowerSemicontinuous_iff_closed_sublevel]
    intro α
    have hsub :
        {z : Fin n → ℝ | g z ≤ (α : EReal)} =
          (fun z : Fin n → ℝ => z + x) ⁻¹'
            {z : Fin n → ℝ | f z ≤ (((α + β : ℝ)) : EReal)} := by
      ext z
      constructor
      · intro hz
        have hz' :
            f (z + x) - ((β : ℝ) : EReal) ≤ (α : EReal) := by
          simpa [g, translatedDifferenceFunctionAt, hβ, add_comm, add_left_comm, add_assoc] using hz
        have hz'' :
            f (z + x) ≤ (α : EReal) + ((β : ℝ) : EReal) :=
          (EReal.sub_le_iff_le_add (Or.inl (by simp)) (Or.inl (by simp))).1 hz'
        simpa [Set.mem_preimage, add_comm, add_left_comm, add_assoc] using hz''
      · intro hz
        have hz' :
            f (z + x) ≤ (α : EReal) + ((β : ℝ) : EReal) := by
          simpa [Set.mem_preimage, add_comm, add_left_comm, add_assoc] using hz
        have hz'' :
            f (z + x) - ((β : ℝ) : EReal) ≤ (α : EReal) :=
          (EReal.sub_le_iff_le_add (Or.inl (by simp)) (Or.inl (by simp))).2 hz'
        simpa [g, translatedDifferenceFunctionAt, hβ, add_comm, add_left_comm, add_assoc] using hz''
    rw [hsub]
    exact
      IsClosed.preimage (show Continuous fun z : Fin n → ℝ => z + x by fun_prop)
        ((lowerSemicontinuous_iff_closed_sublevel (f := f)).1 hclosed.2 (α + β))
  exact ⟨hg_proper.1, hg_lsc⟩


end Section24
end Chap05
