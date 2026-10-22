/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section25_part2

open scoped Topology
open scoped Pointwise

section Chap05
section Section25

-- Proof sketch: combine Theorem 25.1.2 with the identity
-- `⟨g, Pi.single j 1⟩ = g j` to identify the coordinates of the chosen gradient with the
-- coordinate partial derivatives, then substitute these coordinates into Theorem 25.1.1 and
-- rewrite the dot product as the finite sum `∑ j, (∂f/∂ξ_j)(x) * η_j`.
/-- Theorem 25.1.3: if `f` is differentiable at `x`, then the `j`th coordinate of `∇ f(x)` is the
`j`th partial derivative of `f` at `x`; consequently, for every nonzero direction
`y = (η_1, …, η_n)`, the directional derivative is
`∑ j, (∂f / ∂ξ_j)(x) * η_j`. -/
theorem ERealDifferentiableAt.coordinatePartials_and_directionalDerivative_formula {n : Nat}
    {f : (Fin n → Real) → EReal} {x : Fin n → Real}
    (hf : ERealDifferentiableAt f x) :
    (∀ j : Fin n,
      HasCoordinatePartialDerivativeAt f x j
        ((((erealGradientAt hf) j : Real) : EReal))) ∧
      ∀ y : Fin n → Real, y ≠ 0 →
        Filter.Tendsto (directionalDifferenceQuotientAt f x y)
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds (((∑ j : Fin n, (erealGradientAt hf) j * y j : Real) : EReal))) := by
  constructor
  · intro j
    have hcoordinate :
        HasCoordinatePartialDerivativeAt f x j
          (((((erealGradientAt hf) ⬝ᵥ Pi.single j (1 : Real)) : Real) : EReal)) :=
      ERealDifferentiableAt.hasCoordinatePartialDerivativeAt (hf := hf) (j := j)
    have hdotReal :
        (erealGradientAt hf) ⬝ᵥ Pi.single j (1 : Real) = (erealGradientAt hf) j :=
      dotProduct_single_one (v := erealGradientAt hf) (i := j)
    have hdot :
        (((((erealGradientAt hf) ⬝ᵥ Pi.single j (1 : Real)) : Real) : EReal)) =
          ((((erealGradientAt hf) j : Real) : EReal)) := by
      exact congrArg (fun r : Real => (r : EReal)) hdotReal
    -- The `j`th basis vector extracts the `j`th coordinate of the chosen gradient.
    simpa [hdot] using hcoordinate
  · intro y hy
    have hdirectional :
        Filter.Tendsto (directionalDifferenceQuotientAt f x y)
          (nhdsWithin (0 : Real) (Set.Ioi 0))
          (nhds ((((erealGradientAt hf) ⬝ᵥ y : Real) : EReal))) :=
      ERealDifferentiableAt.tendsto_directionalDifferenceQuotient (hf := hf) (y := y) hy
    have hdot :
        (((((erealGradientAt hf) ⬝ᵥ y) : Real) : EReal)) =
          (((∑ j : Fin n, (erealGradientAt hf) j * y j : Real) : EReal)) := by
      simp [dotProduct]
    -- Rewrite the gradient-direction pairing as the coordinate sum from the textbook statement.
    simpa [hdot] using hdirectional

-- Proof sketch: on `interior (dom f)`, the closure `cl f` agrees locally with `f`, so the same
-- first-order expansion witnesses differentiability for either function. Uniqueness of the
-- gradient witness then identifies the gradients whenever both differentiability statements hold.
/-- Helper for Corollary 25.1.1.1: an interior effective-domain point lies in the relative
interior of the Euclidean preimage of that domain. -/
lemma helperForCorollary_25_1_1_1_mem_preimageRi_of_mem_interior_effectiveDomain
    {n : Nat} {f : (Fin n → Real) → EReal} {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    (EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)).symm x ∈
      euclideanRelativeInterior n
        ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
  let e : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)
  let C : Set (EuclideanSpace Real (Fin n)) :=
    ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f)
  let Cint : Set (EuclideanSpace Real (Fin n)) :=
    ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
      interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
  have hxCint : e.symm x ∈ Cint := by
    simpa [e, Cint] using hx
  have hCintOpen : IsOpen Cint := by
    exact isOpen_interior.preimage (by fun_prop)
  have hCintSub : Cint ⊆ C := by
    intro z hz
    have hz' : (z : Fin n → Real) ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
      simpa [Cint] using hz
    have hz'' : (z : Fin n → Real) ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
      interior_subset hz'
    simpa [C] using hz''
  have hxC : e.symm x ∈ interior C := by
    -- The interior point already belongs to an open subset of the preimage domain.
    refine mem_interior_iff_mem_nhds.2 ?_
    exact Filter.mem_of_superset (hCintOpen.mem_nhds hxCint) hCintSub
  have hCintne : Cint.Nonempty := ⟨e.symm x, hxCint⟩
  have hAffTopCint : affineSpan ℝ Cint = ⊤ := hCintOpen.affineSpan_eq_top hCintne
  have hAffTop : affineSpan ℝ C = ⊤ :=
    top_unique <| by
      simpa [hAffTopCint] using
        (affineSpan_mono Real hCintSub : affineSpan ℝ Cint ≤ affineSpan ℝ C)
  have hAff : (affineSpan Real C : Set (EuclideanSpace Real (Fin n))) = Set.univ := by
    simp [hAffTop]
  have hri : euclideanRelativeInterior n C = interior C :=
    euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ n C hAff
  -- Full dimensionality turns the relative interior condition into ordinary interior membership.
  simpa [C, hri] using hxC

/-- Helper for Corollary 25.1.1.1: an interior effective-domain point with finite value forces
properness. -/
lemma helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
    {n : Nat} {f : (Fin n → Real) → EReal} (hf : ConvexFunction f) {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
    (hxbot : f x ≠ (⊥ : EReal)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
  -- Route correction: `effectiveDomain` only excludes `⊤`, so we also use `f x ≠ ⊥`
  -- to rule out the improper case.
  by_contra hproper
  have himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f := by
    refine ⟨?_, hproper⟩
    simpa [ConvexFunction] using hf
  have hxri :
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)).symm x ∈
        euclideanRelativeInterior n
          ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    helperForCorollary_25_1_1_1_mem_preimageRi_of_mem_interior_effectiveDomain hx
  have hxbotEq : f x = (⊥ : EReal) := by
    simpa using
      improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain
        (f := f) himproper ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)).symm x) hxri
  exact hxbot hxbotEq

/-- Helper for Corollary 25.1.1.1: the convex closure agrees with the original function at every
interior effective-domain point of a proper convex function. -/
lemma helperForCorollary_25_1_1_1_closure_eq_at_interior_point
    {n : Nat} {f : (Fin n → Real) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    convexFunctionClosure f x = f x := by
  have hxri :
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)).symm x ∈
        euclideanRelativeInterior n
          ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
            effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    helperForCorollary_25_1_1_1_mem_preimageRi_of_mem_interior_effectiveDomain hx
  -- The Chapter 7 closure theorem identifies `cl f` and `f` on the relative interior of `dom f`.
  simpa using
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
      (f := f) hproper).2 ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)).symm x) hxri

/-- Helper for Corollary 25.1.1.1: pointwise closure agreement transports vector subgradients
between `f` and `cl f`. -/
lemma helperForCorollary_25_1_1_1_subgradient_iff_closure_subgradient_at_interior_point
    {n : Nat} {f : (Fin n → Real) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x g : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    IsSubgradientAt (convexFunctionClosure f) x (dotProductEquiv Real (Fin n) g) ↔
      IsSubgradientAt f x (dotProductEquiv Real (Fin n) g) := by
  have hclx :
      convexFunctionClosure f x = f x :=
    helperForCorollary_25_1_1_1_closure_eq_at_interior_point hproper hx
  -- Reinterpret the Euclidean subgradient transport from Section 23 in dual-vector form.
  simpa [IsEuclideanSubgradientAt] using
    helperForCorollary_23_5_2_euclideanSubgradient_closure_iff_original
      f hproper x g hclx

/-- Helper for Corollary 25.1.1.1: uniqueness of the vector subgradient is unchanged by passing
to the convex closure at an interior point. -/
lemma helperForCorollary_25_1_1_1_uniqueSubgradient_iff_closure_uniqueSubgradient
    {n : Nat} {f : (Fin n → Real) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x : Fin n → Real}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    (∃! g : Fin n → Real, IsSubgradientAt f x (dotProductEquiv Real (Fin n) g)) ↔
      (∃! g : Fin n → Real,
        IsSubgradientAt (convexFunctionClosure f) x (dotProductEquiv Real (Fin n) g)) := by
  constructor
  · rintro ⟨g, hg, huniq⟩
    refine ⟨g, ?_, ?_⟩
    · -- Transport the distinguished subgradient from `f` to `cl f`.
      exact
        (helperForCorollary_25_1_1_1_subgradient_iff_closure_subgradient_at_interior_point
          hproper hx).2 hg
    · intro g' hg'
      -- Any closure-side subgradient pulls back to the unique original one.
      exact huniq g'
        ((helperForCorollary_25_1_1_1_subgradient_iff_closure_subgradient_at_interior_point
          hproper hx).1 hg')
  · rintro ⟨g, hg, huniq⟩
    refine ⟨g, ?_, ?_⟩
    · -- Transport the distinguished closure subgradient back to `f`.
      exact
        (helperForCorollary_25_1_1_1_subgradient_iff_closure_subgradient_at_interior_point
          hproper hx).1 hg
    · intro g' hg'
      -- Then uniqueness on the closure side identifies every original subgradient as well.
      exact huniq g'
        ((helperForCorollary_25_1_1_1_subgradient_iff_closure_subgradient_at_interior_point
          hproper hx).2 hg')

/-- Corollary 25.1.1.1: if `f` is convex and `x ∈ interior (dom f)`, then (1) `f` is
differentiable at `x` if and only if (2) `cl f` is differentiable at `x`. In this case
`∇ (cl f) (x) = ∇ f (x)`. -/
theorem convexFunction_differentiableAt_iff_convexFunctionClosure_differentiableAt_and_gradient_eq
    {n : Nat} (f : (Fin n → Real) → EReal) (hf : ConvexFunction f) (x : Fin n → Real)
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) :
    (ERealDifferentiableAt f x ↔ ERealDifferentiableAt (convexFunctionClosure f) x) ∧
      ∀ (hdiff : ERealDifferentiableAt f x)
        (hcldiff : ERealDifferentiableAt (convexFunctionClosure f) x),
        erealGradientAt hcldiff = erealGradientAt hdiff := by
  have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → Real)) f :=
    interior_subset hx
  have hxtop : f x ≠ (⊤ : EReal) :=
    mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → Real))) (f := f) hxDom
  constructor
  · constructor
    · intro hdiff
      have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) :=
        ERealDifferentiableAt.finiteAt hdiff
      have hproper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
        helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
          hf hx hxFinite.2
      have hclx :
          convexFunctionClosure f x = f x :=
        helperForCorollary_25_1_1_1_closure_eq_at_interior_point hproper hx
      have hclosureClosed :
          ClosedConvexFunction (convexFunctionClosure f) :=
        (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
          (f := f) hproper).1.1
      have hclFinite :
          convexFunctionClosure f x ≠ (⊤ : EReal) ∧ convexFunctionClosure f x ≠ (⊥ : EReal) := by
        constructor
        · simpa [hclx] using hxFinite.1
        · simpa [hclx] using hxFinite.2
      have huniq_f :
          ∃! g : Fin n → Real, IsSubgradientAt f x (dotProductEquiv Real (Fin n) g) := by
        rcases
            (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
              f hf x hxFinite).1 hdiff with
          ⟨hsub, _hminorant, huniq⟩
        -- Theorem 25.1 packages differentiability as uniqueness of the gradient subgradient.
        exact ⟨erealGradientAt hdiff, hsub, huniq⟩
      have huniq_cl :
          ∃! g : Fin n → Real,
            IsSubgradientAt (convexFunctionClosure f) x (dotProductEquiv Real (Fin n) g) :=
        (helperForCorollary_25_1_1_1_uniqueSubgradient_iff_closure_uniqueSubgradient
          hproper hx).1 huniq_f
      -- Use the transported unique subgradient to recover differentiability of `cl f`.
      exact
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (convexFunctionClosure f) hclosureClosed.1 x hclFinite).2 huniq_cl
    · intro hcldiff
      have hclFinite :
          convexFunctionClosure f x ≠ (⊤ : EReal) ∧ convexFunctionClosure f x ≠ (⊥ : EReal) :=
        ERealDifferentiableAt.finiteAt hcldiff
      have hxbot : f x ≠ (⊥ : EReal) := by
        intro hfxbot
        have hclbot : convexFunctionClosure f x = (⊥ : EReal) := by
          refine le_antisymm ?_ bot_le
          simpa [hfxbot] using (convexFunctionClosure_le_self (f := f) x)
        exact hclFinite.2 hclbot
      have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) := ⟨hxtop, hxbot⟩
      have hproper :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
        helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
          hf hx hxbot
      have hclosureClosed :
          ClosedConvexFunction (convexFunctionClosure f) :=
        (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
          (f := f) hproper).1.1
      have huniq_cl :
          ∃! g : Fin n → Real,
            IsSubgradientAt (convexFunctionClosure f) x (dotProductEquiv Real (Fin n) g) := by
        rcases
            (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
              (convexFunctionClosure f) hclosureClosed.1 x hclFinite).1 hcldiff with
          ⟨hsub, _hminorant, huniq⟩
        -- Apply Theorem 25.1 on the closure, then pull uniqueness back to `f`.
        exact ⟨erealGradientAt hcldiff, hsub, huniq⟩
      have huniq_f :
          ∃! g : Fin n → Real, IsSubgradientAt f x (dotProductEquiv Real (Fin n) g) :=
        (helperForCorollary_25_1_1_1_uniqueSubgradient_iff_closure_uniqueSubgradient
          hproper hx).2 huniq_cl
      -- The converse half of Theorem 25.1 turns the transported uniqueness back into differentiability.
      exact
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          f hf x hxFinite).2 huniq_f
  · intro hdiff hcldiff
    have hxFinite : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal) :=
      ERealDifferentiableAt.finiteAt hdiff
    have hproper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f :=
      helperForCorollary_25_1_1_1_proper_of_mem_interior_effectiveDomain_and_ne_bot
        hf hx hxFinite.2
    have hclosureClosed :
        ClosedConvexFunction (convexFunctionClosure f) :=
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
        (f := f) hproper).1.1
    have hclx :
        convexFunctionClosure f x = f x :=
      helperForCorollary_25_1_1_1_closure_eq_at_interior_point hproper hx
    have hclFinite :
        convexFunctionClosure f x ≠ (⊤ : EReal) ∧ convexFunctionClosure f x ≠ (⊥ : EReal) := by
      constructor
      · simpa [hclx] using hxFinite.1
      · simpa [hclx] using hxFinite.2
    rcases
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          f hf x hxFinite).1 hdiff with
      ⟨_hsub_f, _hminorant_f, huniq_f⟩
    rcases
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (convexFunctionClosure f) hclosureClosed.1 x hclFinite).1 hcldiff with
      ⟨hsub_cl, _hminorant_cl, _huniq_cl⟩
    have hsub_f_of_cl :
        IsSubgradientAt f x
          (dotProductEquiv Real (Fin n) (erealGradientAt hcldiff)) :=
      (helperForCorollary_25_1_1_1_subgradient_iff_closure_subgradient_at_interior_point
        hproper hx).1 hsub_cl
    -- Uniqueness on the original function forces the two gradient vectors to coincide.
    exact huniq_f (erealGradientAt hcldiff) hsub_f_of_cl

-- Proof sketch: use the Fenchel-Young exposed-face characterization of supporting hyperplanes of
-- `epi f*` from Section 23 together with Corollary 25.1.1, which identifies the unique
-- subgradient at a differentiability point with the Euclidean gradient. This turns exposed graph
-- points of `f*` into gradient images of differentiability points, and conversely such gradient
-- images define exposed supporting hyperplanes to `epi f*`.
/-- Helper for Corollary 25.1.2: a linear functional on `ℝⁿ × ℝ` splits into its horizontal and
vertical parts. -/
lemma helperForCorollary_25_1_2_linearMap_apply_prod {n : Nat}
    (l : ((Fin n → Real) × Real) →ₗ[Real] Real) (x : Fin n → Real) (μ : Real) :
    l (x, μ) = l (x, (0 : Real)) + μ * l ((0 : Fin n → Real), (1 : Real)) := by
  -- Decompose `(x, μ)` into its horizontal and vertical components, then use linearity.
  have hdecomp : (x, μ) = (x, (0 : Real)) + ((0 : Fin n → Real), μ) := by
    ext <;> simp
  have hsmul : ((0 : Fin n → Real), μ) = μ • ((0 : Fin n → Real), (1 : Real)) := by
    ext <;> simp
  have hl0 : l ((0 : Fin n → Real), μ) = μ * l ((0 : Fin n → Real), (1 : Real)) := by
    calc
      l ((0 : Fin n → Real), μ) = l (μ • ((0 : Fin n → Real), (1 : Real))) := congrArg l hsmul
      _ = μ • l ((0 : Fin n → Real), (1 : Real)) := l.map_smul μ ((0 : Fin n → Real), (1 : Real))
      _ = μ * l ((0 : Fin n → Real), (1 : Real)) := by simp [smul_eq_mul]
  calc
    l (x, μ) = l ((x, (0 : Real)) + ((0 : Fin n → Real), μ)) := congrArg l hdecomp
    _ = l (x, (0 : Real)) + l ((0 : Fin n → Real), μ) := l.map_add (x, (0 : Real))
        ((0 : Fin n → Real), μ)
    _ = l (x, (0 : Real)) + μ * l ((0 : Fin n → Real), (1 : Real)) := by simp [hl0]

/-- Helper for Corollary 25.1.2: an exposed point of `epi f*` determines a point of unique
primal Fenchel attainment for `f*`. -/
lemma helperForCorollary_25_1_2_exposedPoint_yields_unique_primalAttainment
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    (p : (Fin n → Real) × Real)
    (hp : IsExposedPoint (epigraph (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)) p) :
    ∃ x : Fin n → Real,
      p.2 = (fenchelConjugate n f p.1).toReal ∧
        PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) p.1 x ∧
        (∀ y : Fin n → Real,
          PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) y x → y = p.1) := by
  let C : Set ((Fin n → Real) × Real) :=
    epigraph (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f)
  have hproperConj :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  -- Route correction: the singleton-maximizer presentation in `IsExposedPoint` already gives the
  -- strict vertical-sign contradiction, so we normalize the exposing functional directly.
  dsimp [IsExposedPoint, IsExposedFace] at hp
  rcases hp with ⟨hconvC, hpSubset, ⟨l0, hpEq⟩⟩
  have hpC : p ∈ C := by
    exact hpSubset (by simp)
  have hpmax : p ∈ maximizers C l0 := by
    simpa [hpEq] using (show p ∈ ({p} : Set ((Fin n → Real) × Real)) by simp)
  have hpmax_le : ∀ q ∈ C, l0 q ≤ l0 p :=
    (mem_maximizers_iff (C := C) (h := l0) (x := p)).1 hpmax |>.2
  let q1 : (Fin n → Real) × Real := (p.1, p.2 + 1)
  have hq1C : q1 ∈ C := by
    apply (mem_epigraph_univ_iff (f := fenchelConjugate n f)).2
    have hpLe : fenchelConjugate n f p.1 ≤ (p.2 : EReal) :=
      (mem_epigraph_univ_iff (f := fenchelConjugate n f)).1 hpC
    exact le_trans hpLe <| by
      exact_mod_cast (show p.2 ≤ p.2 + 1 by linarith)
  let c : Real := l0 ((0 : Fin n → Real), (1 : Real))
  let φ : (Fin n → Real) →ₗ[Real] Real := l0.comp (LinearMap.inl Real (Fin n → Real) Real)
  rcases linearMap_exists_dotProduct_representation (φ := φ) with ⟨b, hb⟩
  have hl0_form : ∀ y : Fin n → Real, ∀ μ : Real, l0 (y, μ) = dotProduct y b + μ * c := by
    intro y μ
    rw [helperForCorollary_25_1_2_linearMap_apply_prod (l := l0) (x := y) (μ := μ)]
    have hhorizontal : l0 (y, (0 : Real)) = dotProduct y b := by
      simpa [φ, LinearMap.inl] using hb y
    simpa [c] using congrArg (fun t : Real => t + μ * c) hhorizontal
  have hc_nonpos : c ≤ 0 := by
    have hq1le : l0 q1 ≤ l0 p := hpmax_le q1 hq1C
    rw [show q1 = (p.1, p.2 + 1) by rfl] at hq1le
    rw [hl0_form p.1 (p.2 + 1), hl0_form p.1 p.2] at hq1le
    linarith
  have hc_ne_zero : c ≠ 0 := by
    intro hc0
    have hq1eq : l0 q1 = l0 p := by
      rw [show q1 = (p.1, p.2 + 1) by rfl]
      rw [hl0_form p.1 (p.2 + 1), hl0_form p.1 p.2]
      simp [hc0]
    have hq1max : q1 ∈ maximizers C l0 :=
      mem_maximizers_of_mem_of_eq_value
        (C := C) (h := l0) (x := p) (x' := q1) hpmax hq1C hq1eq
    have hq1eqp : q1 = p := by
      have : q1 ∈ ({p} : Set ((Fin n → Real) × Real)) := by
        simpa [hpEq] using hq1max
      simpa using this
    have hsecond : p.2 + 1 = p.2 := by
      simpa [q1] using congrArg Prod.snd hq1eqp
    linarith
  have hc_neg : c < 0 :=
    lt_of_le_of_ne hc_nonpos hc_ne_zero
  let α : Real := -(1 / c)
  have hα_pos : 0 < α := by
    dsimp [α]
    exact neg_pos.mpr (one_div_neg.2 hc_neg)
  have hα_ne_zero : α ≠ 0 := ne_of_gt hα_pos
  have hαc : α * c = -1 := by
    dsimp [α]
    field_simp [hc_ne_zero]
  let x : Fin n → Real := α • b
  let l : ((Fin n → Real) × Real) →ₗ[Real] Real :=
    (dotProductEquiv Real (Fin n) x).comp (LinearMap.fst Real (Fin n → Real) Real) -
      LinearMap.snd Real (Fin n → Real) Real
  have hl_eval : ∀ q : (Fin n → Real) × Real, l q = α * l0 q := by
    intro q
    rcases q with ⟨y, μ⟩
    have hdot : dotProduct x y = α * dotProduct y b := by
      calc
        dotProduct x y = dotProduct (α • b) y := by rfl
        _ = α * dotProduct b y := dotProduct_smul_left_real (a := α) (y := b) (xStar := y)
        _ = α * dotProduct y b := by rw [dotProduct_comm]
    calc
      l (y, μ) = dotProduct x y - μ := by
        simp [l]
      _ = α * dotProduct y b - μ := by
        rw [hdot]
      _ = α * (dotProduct y b + μ * c) := by
        have hmul : α * (μ * c) = -μ := by
          calc
            α * (μ * c) = μ * (α * c) := by ring
            _ = μ * (-1) := by rw [hαc]
            _ = -μ := by ring
        linarith
      _ = α * l0 (y, μ) := by
        rw [hl0_form y μ]
  have hcanonical_le : ∀ q ∈ C, l q ≤ l p := by
    intro q hqC
    have hqle : l0 q ≤ l0 p := hpmax_le q hqC
    have hscaled : α * l0 q ≤ α * l0 p :=
      mul_le_mul_of_nonneg_left hqle hα_pos.le
    simpa [hl_eval q, hl_eval p] using hscaled
  have hpmaxCanon : p ∈ maximizers C l := by
    refine (mem_maximizers_iff (C := C) (h := l) (x := p)).2 ?_
    refine ⟨hpC, ?_⟩
    intro q hqC
    exact hcanonical_le q hqC
  have hcanonical_eq_implies_eq :
      ∀ q : (Fin n → Real) × Real,
        q ∈ C → l q = l p → q = p := by
    intro q hqC hEq
    have hl0eq : l0 q = l0 p := by
      apply mul_left_cancel₀ hα_ne_zero
      simpa [hl_eval q, hl_eval p] using hEq
    have hqmax : q ∈ maximizers C l0 :=
      mem_maximizers_of_mem_of_eq_value
        (C := C) (h := l0) (x := p) (x' := q) hpmax hqC hl0eq
    have : q ∈ ({p} : Set ((Fin n → Real) × Real)) := by
      simpa [hpEq] using hqmax
    simpa using this
  have hsingletonCanon : maximizers C l = ({p} : Set ((Fin n → Real) × Real)) := by
    ext q
    constructor
    · intro hqmax
      have hqC : q ∈ C := (mem_maximizers_iff (C := C) (h := l) (x := q)).1 hqmax |>.1
      have hEqVal : l q = l p := h_eq_of_mem_maximizers (x := q) (y := p) hqmax hpmaxCanon
      exact Set.mem_singleton_iff.2 (hcanonical_eq_implies_eq q hqC hEqVal)
    · intro hq
      rcases Set.mem_singleton_iff.1 hq with rfl
      exact hpmaxCanon
  have hpTop : fenchelConjugate n f p.1 ≠ (⊤ : EReal) := by
    intro htop
    have hpLe : fenchelConjugate n f p.1 ≤ (p.2 : EReal) :=
      (mem_epigraph_univ_iff (f := fenchelConjugate n f)).1 hpC
    rw [htop] at hpLe
    exact (not_top_le_coe p.2 hpLe).elim
  have hpBot : fenchelConjugate n f p.1 ≠ (⊥ : EReal) :=
    hproperConj.2.2 p.1 (by simp)
  let q0 : (Fin n → Real) × Real := (p.1, (fenchelConjugate n f p.1).toReal)
  have hq0C : q0 ∈ C := by
    apply (mem_epigraph_univ_iff (f := fenchelConjugate n f)).2
    simpa [q0] using EReal.le_coe_toReal hpTop
  have hq0_ge : l p ≤ l q0 := by
    have hq0Height : (fenchelConjugate n f p.1).toReal ≤ p.2 := by
      exact_mod_cast
        (show (((fenchelConjugate n f p.1).toReal : Real) : EReal) ≤ (p.2 : EReal) by
          rw [EReal.coe_toReal hpTop hpBot]
          exact (mem_epigraph_univ_iff (f := fenchelConjugate n f)).1 hpC)
    have : dotProduct x p.1 - p.2 ≤ dotProduct x p.1 - (fenchelConjugate n f p.1).toReal := by
      linarith
    simpa [l, q0] using this
  have hq0_le : l q0 ≤ l p :=
    (mem_maximizers_iff (C := C) (h := l) (x := p)).1 hpmaxCanon |>.2 q0 hq0C
  have hq0eq : q0 = p := by
    have hq0Val : l q0 = l p := le_antisymm hq0_le hq0_ge
    have hq0max : q0 ∈ maximizers C l :=
      mem_maximizers_of_mem_of_eq_value
        (C := C) (h := l) (x := p) (x' := q0) hpmaxCanon hq0C hq0Val
    have : q0 ∈ ({p} : Set ((Fin n → Real) × Real)) := by
      simpa [hsingletonCanon] using hq0max
    simpa using this
  have hpGraph : p.2 = (fenchelConjugate n f p.1).toReal := by
    simpa [q0] using congrArg Prod.snd hq0eq.symm
  have hpAtt : PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) p.1 x := by
    intro y
    by_cases hyTop : fenchelConjugate n f y = (⊤ : EReal)
    · rw [hyTop]
      simp
    · have hyBot : fenchelConjugate n f y ≠ (⊥ : EReal) :=
        hproperConj.2.2 y (by simp)
      let q : (Fin n → Real) × Real := (y, (fenchelConjugate n f y).toReal)
      have hqC : q ∈ C := by
        apply (mem_epigraph_univ_iff (f := fenchelConjugate n f)).2
        simpa [q] using EReal.le_coe_toReal hyTop
      have hqle : l q ≤ l p :=
        (mem_maximizers_iff (C := C) (h := l) (x := p)).1 hpmaxCanon |>.2 q hqC
      have hqGraphLe :
          dotProduct x y - (fenchelConjugate n f y).toReal ≤
            dotProduct x p.1 - p.2 := by
        have hqle' := hqle
        simp [q, l, sub_eq_add_neg, add_comm] at hqle'
        linarith
      have hqleE :
          ((((dotProduct x y - (fenchelConjugate n f y).toReal : Real) : Real) : EReal)) ≤
            ((((dotProduct x p.1 - (fenchelConjugate n f p.1).toReal : Real) : Real) : EReal)) := by
        have hqleGraph' :
            dotProduct x y - (fenchelConjugate n f y).toReal ≤
              dotProduct x p.1 - (fenchelConjugate n f p.1).toReal := by
          simpa [hpGraph] using hqGraphLe
        exact_mod_cast hqleGraph'
      simpa [q, l, hpGraph, dotProduct_comm, EReal.coe_sub,
        EReal.coe_toReal hyTop hyBot, EReal.coe_toReal hpTop hpBot] using hqleE
  have hpUniq :
      ∀ y : Fin n → Real,
        PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) y x → y = p.1 := by
    intro y hyAtt
    have hyFY : FenchelYoungInequalityAt (fenchelConjugate n f) y x :=
      (helperForTheorem_23_5_primalSupremumAttainedAt_iff_fenchelYoungInequality
        (fenchelConjugate n f) y x).1 hyAtt
    have hyFinite :
        fenchelConjugate n f y ≠ (⊤ : EReal) ∧ fenchelConjugate n f y ≠ (⊥ : EReal) :=
      helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality
        (fenchelConjugate n f) hproperConj y x hyFY
    let q : (Fin n → Real) × Real := (y, (fenchelConjugate n f y).toReal)
    have hqC : q ∈ C := by
      apply (mem_epigraph_univ_iff (f := fenchelConjugate n f)).2
      simpa [q] using EReal.le_coe_toReal hyFinite.1
    have hp_le_y : ((dotProduct p.1 x : Real) : EReal) - fenchelConjugate n f p.1 ≤
        ((dotProduct y x : Real) : EReal) - fenchelConjugate n f y := by
      simpa [dotProduct_comm] using hyAtt p.1
    have hy_le_p : ((dotProduct y x : Real) : EReal) - fenchelConjugate n f y ≤
        ((dotProduct p.1 x : Real) : EReal) - fenchelConjugate n f p.1 := by
      simpa [dotProduct_comm] using hpAtt y
    have hEqAtt :
        ((dotProduct y x : Real) : EReal) - fenchelConjugate n f y =
          ((dotProduct p.1 x : Real) : EReal) - fenchelConjugate n f p.1 :=
      le_antisymm hy_le_p hp_le_y
    have hEqValE :
        ((((dotProduct x y - (fenchelConjugate n f y).toReal : Real) : Real) : EReal)) =
          ((((dotProduct x p.1 - (fenchelConjugate n f p.1).toReal : Real) : Real) : EReal)) := by
      simpa [dotProduct_comm, EReal.coe_sub, EReal.coe_toReal hyFinite.1 hyFinite.2,
        EReal.coe_toReal hpTop hpBot] using hEqAtt
    have hEqVal :
        dotProduct x y - (fenchelConjugate n f y).toReal =
          dotProduct x p.1 - (fenchelConjugate n f p.1).toReal := by
      exact_mod_cast hEqValE
    have hqVal : l q = l p := by
      simpa [q, l, hpGraph] using hEqVal
    have hqmax : q ∈ maximizers C l :=
      mem_maximizers_of_mem_of_eq_value
        (C := C) (h := l) (x := p) (x' := q) hpmaxCanon hqC hqVal
    have hqeqp : q = p := by
      have : q ∈ ({p} : Set ((Fin n → Real) × Real)) := by
        simpa [hsingletonCanon] using hqmax
      simpa using this
    simpa [q] using congrArg Prod.fst hqeqp
  exact ⟨x, hpGraph, hpAtt, hpUniq⟩

/-- Helper for Corollary 25.1.2: a convex set in `ℝ^n` has the same interior as its closure. -/
lemma helperForCorollary_25_1_2_interior_closure_eq_interior_of_convex
    {n : Nat} (S : Set (EuclideanSpace Real (Fin n))) (hS : Convex Real S) :
    interior (closure S) = interior S := by
  apply le_antisymm
  · intro x hx
    by_cases hne : (interior (closure S)).Nonempty
    · have hspanInt : affineSpan ℝ (interior (closure S)) = ⊤ :=
        isOpen_interior.affineSpan_eq_top hne
      have hspanClosure : affineSpan ℝ (closure S) = ⊤ := by
        apply top_unique
        have :
            (affineSpan ℝ (interior (closure S)) :
              AffineSubspace ℝ (EuclideanSpace Real (Fin n))) ≤
              affineSpan ℝ (closure S) :=
          affineSpan_mono ℝ interior_subset
        simpa [hspanInt] using this
      have hspan : affineSpan ℝ S = ⊤ := by
        -- Closure preserves affine span, so nonempty interior forces full dimension for `S`.
        simpa [affineSpan_closure_eq (n := n) (C := S)] using hspanClosure
      have hriClosure :
          euclideanRelativeInterior n (closure S) = interior (closure S) := by
        apply euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ (n := n) (C := closure S)
        simp [hspanClosure]
      have hri :
          euclideanRelativeInterior n S = interior S := by
        apply euclideanRelativeInterior_eq_interior_of_affineSpan_eq_univ (n := n) (C := S)
        simp [hspan]
      have hriEq :=
        (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq
          (n := n) (C := S) hS).2
      -- Rewrite both interiors through relative interior and conclude.
      have hEq : interior (closure S) = interior S := by
        calc
          interior (closure S) = euclideanRelativeInterior n (closure S) := by
            simp [hriClosure]
          _ = euclideanRelativeInterior n S := by
            simpa using hriEq
          _ = interior S := by
            simp [hri]
      simpa [hEq] using hx
    · exact (hne ⟨x, hx⟩).elim
  · exact interior_mono subset_closure

/-- Helper for Corollary 25.1.2: unique attainment for `f*` gives the unique Euclidean
subgradient of `cl f` at the primal point. -/
lemma helperForCorollary_25_1_2_uniqueClosureSubgradient_of_uniqueConjugateAttainment
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {xStar x : Fin n → Real}
    (hatt : PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) xStar x)
    (huniq : ∀ y : Fin n → Real,
      PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) y x → y = xStar) :
    IsSubgradientAt (convexFunctionClosure f) x (dotProductEquiv Real (Fin n) xStar) ∧
      ∀ g : Fin n → Real,
        IsSubgradientAt (convexFunctionClosure f) x (dotProductEquiv Real (Fin n) g) →
          g = xStar := by
  have hproperConj :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hclosureProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := f) hproper).1.2
  have hclosureClosed :
      ClosedConvexFunction (convexFunctionClosure f) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := f) hproper).1.1
  have hsubConj :
      IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x := by
    -- The four-way Fenchel equivalence turns conjugate attainment into a conjugate subgradient.
    exact
      (((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        (fenchelConjugate n f) hproperConj xStar x).1.out 1 0).1 hatt)
  have hsubClosure : IsSubgradientAt (convexFunctionClosure f) x
      (dotProductEquiv Real (Fin n) xStar) := by
    have hsubConjClosure :
        IsEuclideanSubgradientAt (fenchelConjugate n (convexFunctionClosure f)) xStar x := by
      -- The conjugates of `f` and `cl f` agree, so the same conjugate subgradient applies.
      simpa [fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := f)] using hsubConj
    have hsubClosureE :
        IsEuclideanSubgradientAt (convexFunctionClosure f) x xStar :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := convexFunctionClosure f) hclosureClosed hclosureProper x xStar).1 hsubConjClosure
    simpa [IsEuclideanSubgradientAt] using hsubClosureE
  refine ⟨hsubClosure, ?_⟩
  intro g hg
  have hgClosureE : IsEuclideanSubgradientAt (convexFunctionClosure f) x g := by
    -- Rewrite the closure-side subgradient into Euclidean coordinates.
    simpa [IsEuclideanSubgradientAt] using hg
  have hgConjClosure :
      IsEuclideanSubgradientAt (fenchelConjugate n (convexFunctionClosure f)) g x :=
    (euclidean_subgradient_fenchelConjugate_iff
      (f := convexFunctionClosure f) hclosureClosed hclosureProper x g).2 hgClosureE
  have hgConj : IsEuclideanSubgradientAt (fenchelConjugate n f) g x := by
    -- Move back from `(cl f)*` to `f*`.
    simpa [fenchelConjugate_eq_of_convexFunctionClosure (n := n) (f := f)] using hgConjClosure
  have hgAtt : PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) g x := by
    -- Another use of the four-way equivalence recovers primal attainment for the conjugate.
    exact
      (((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        (fenchelConjugate n f) hproperConj g x).1.out 0 1).1 hgConj)
  exact huniq g hgAtt

/-- Helper for Corollary 25.1.2: interior points of `dom (cl f)` are already interior points of
`dom f`. -/
lemma helperForCorollary_25_1_2_mem_interior_effectiveDomain_of_closure_mem_interior
    {n : Nat} {f : (Fin n → Real) → EReal}
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x : Fin n → Real}
    (hxcl :
      x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f))) :
    x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) := by
  let e : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → Real) :=
    EuclideanSpace.equiv (ι := Fin n) (𝕜 := Real)
  let domf : Set (EuclideanSpace Real (Fin n)) :=
    ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) f)
  let domcl : Set (EuclideanSpace Real (Fin n)) :=
    ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f))
  have hpreimageDomcl :
      ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
        interior (effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f))) =
        interior domcl := by
    simpa [e, domcl] using
      (e.toHomeomorph.preimage_interior
        (effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f)))
  have hxclDom : e.symm x ∈ interior domcl := by
    -- Convert interior membership across the Euclidean-coordinate homeomorphism.
    have hxclPre :
        e.symm x ∈ ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
          interior (effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f))) := by
      simpa [e] using hxcl
    simpa [hpreimageDomcl] using hxclPre
  have hclosureDom :
      closure domcl = closure domf := by
    -- Chapter 7 gives equality of the closures of the effective domains of `f` and `cl f`.
    simpa [domf, domcl] using
      (convexFunctionClosure_effectiveDomain_subset_relativeBoundary_and_same_closure_ri_dim
        (hf := hproper)).2.2.1
  have hconvDomf : Convex Real domf := by
    have hconvEff :
        Convex Real (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → Real))) (f := f) hproper.1
    simpa [domf, e] using
      (Convex.linear_preimage
        (s := effectiveDomain (Set.univ : Set (Fin n → Real)) f) hconvEff e.toLinearMap)
  have hxClosure : e.symm x ∈ interior (closure domf) := by
    have hxClosureCl : e.symm x ∈ interior (closure domcl) :=
      interior_mono subset_closure hxclDom
    simpa [hclosureDom] using hxClosureCl
  have hInteriorEq : interior (closure domf) = interior domf :=
    helperForCorollary_25_1_2_interior_closure_eq_interior_of_convex domf hconvDomf
  -- Replace the Euclidean-domain statement by the original `Fin n → Real` statement.
  have hxDomf : e.symm x ∈ interior domf := by
    simpa [hInteriorEq] using hxClosure
  have hpreimageDomf :
      ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
        interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) =
        interior domf := by
    simpa [e, domf] using
      (e.toHomeomorph.preimage_interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f))
  have hxPreimage :
      e.symm x ∈ ((fun z : EuclideanSpace Real (Fin n) => (z : Fin n → Real)) ⁻¹'
        interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f)) := by
    simpa [hpreimageDomf] using hxDomf
  simpa [e] using hxPreimage

/-- Helper for Corollary 25.1.2: unique primal attainment for `f*` forces differentiability of
`f` at the corresponding primal point and identifies the gradient. -/
lemma helperForCorollary_25_1_2_differentiablePoint_of_unique_conjugateAttainment
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {xStar x : Fin n → Real}
    (hatt : PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) xStar x)
    (huniq : ∀ y : Fin n → Real,
      PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) y x → y = xStar) :
    ∃ hdiff : ERealDifferentiableAt f x, erealGradientAt hdiff = xStar := by
  have hclosureProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f) :=
    (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri (f := f) hproper).1.2
  have hclosureSubgrad :
      IsSubgradientAt (convexFunctionClosure f) x (dotProductEquiv Real (Fin n) xStar) ∧
        ∀ g : Fin n → Real,
          IsSubgradientAt (convexFunctionClosure f) x (dotProductEquiv Real (Fin n) g) →
            g = xStar :=
    helperForCorollary_25_1_2_uniqueClosureSubgradient_of_uniqueConjugateAttainment
      (f := f) hproper hatt huniq
  have hsubClosure :
      IsSubgradientAt (convexFunctionClosure f) x (dotProductEquiv Real (Fin n) xStar) :=
    hclosureSubgrad.1
  have huniqueClosure :
      ∃! g : Fin n → Real,
        IsSubgradientAt (convexFunctionClosure f) x (dotProductEquiv Real (Fin n) g) := by
    refine ⟨xStar, hsubClosure, ?_⟩
    intro g hg
    exact hclosureSubgrad.2 g hg
  have hsubClosureE :
      IsEuclideanSubgradientAt (convexFunctionClosure f) x xStar := by
    -- Repackage the distinguished closure subgradient in Euclidean coordinates.
    simpa [IsEuclideanSubgradientAt] using hsubClosure
  have hxClosureFinite :
      convexFunctionClosure f x ≠ (⊤ : EReal) ∧ convexFunctionClosure f x ≠ (⊥ : EReal) :=
    helperForTheorem_23_5_finiteAt_of_euclideanSubgradient
      (convexFunctionClosure f) hclosureProper x xStar hsubClosureE
  have hclDiff : ERealDifferentiableAt (convexFunctionClosure f) x :=
    -- The unique closure subgradient is the converse half of Theorem 25.1 for `cl f`.
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
      (convexFunctionClosure f) hclosureProper.1 x hxClosureFinite).2 huniqueClosure
  have hgradClosure : erealGradientAt hclDiff = xStar := by
    rcases
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (convexFunctionClosure f) hclosureProper.1 x hxClosureFinite).1 hclDiff with
      ⟨_hsubGrad, _hminorant, huniqGrad⟩
    -- The closure gradient is exactly the unique closure subgradient recovered above.
    exact (huniqGrad xStar hsubClosure).symm
  have hxIntClosure :
      x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) (convexFunctionClosure f)) :=
    (convexFunction_proper_and_mem_interior_of_differentiableAt
      (convexFunctionClosure f) hclosureProper.1 x hclDiff).2
  have hxInt :
      x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → Real)) f) :=
    helperForCorollary_25_1_2_mem_interior_effectiveDomain_of_closure_mem_interior
      hproper hxIntClosure
  have htransfer :=
    convexFunction_differentiableAt_iff_convexFunctionClosure_differentiableAt_and_gradient_eq
      f hproper.1 x hxInt
  have hdiff : ERealDifferentiableAt f x := htransfer.1.2 hclDiff
  refine ⟨hdiff, ?_⟩
  -- The gradient comparison theorem from Corollary 25.1.1.1 identifies the original gradient.
  calc
    erealGradientAt hdiff = erealGradientAt hclDiff := by
      symm
      exact htransfer.2 hdiff hclDiff
    _ = xStar := hgradClosure

/-- Helper for Corollary 25.1.2: equality of the canonical exposing functional on `epi f*`
forces the epigraph point to lie on the graph of `f*`. -/
lemma helperForCorollary_25_1_2_epigraphEquality_forces_graphHeight
    {n : Nat} (f : (Fin n → Real) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) f)
    {x g : Fin n → Real}
    (hatt : PrimalFenchelSupremumAttainedAt (fenchelConjugate n f) g x)
    {q : (Fin n → Real) × Real}
    (hq : q ∈ epigraph (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f))
    (hEq : dotProduct x q.1 - q.2 =
      dotProduct x g - (fenchelConjugate n f g).toReal) :
    q.2 = (fenchelConjugate n f q.1).toReal := by
  have hproperConj :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → Real)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hqLe : fenchelConjugate n f q.1 ≤ (q.2 : EReal) :=
    (mem_epigraph_univ_iff (f := fenchelConjugate n f)).1 hq
  have hqTop : fenchelConjugate n f q.1 ≠ (⊤ : EReal) := by
    -- Epigraph membership against a real height rules out `f*(q.1) = ⊤`.
    intro htop
    rw [htop] at hqLe
    exact (not_top_le_coe q.2 hqLe).elim
  have hqBot : fenchelConjugate n f q.1 ≠ (⊥ : EReal) :=
    hproperConj.2.2 q.1 (by simp)
  have hgFinite : fenchelConjugate n f g ≠ (⊤ : EReal) ∧
      fenchelConjugate n f g ≠ (⊥ : EReal) := by
    -- The distinguished conjugate attainment point has finite conjugate value by Fenchel-Young.
    have hfy : FenchelYoungInequalityAt (fenchelConjugate n f) g x :=
      (helperForTheorem_23_5_primalSupremumAttainedAt_iff_fenchelYoungInequality
        (fenchelConjugate n f) g x).1 hatt
    exact helperForTheorem_23_5_finiteAt_of_fenchelYoungInequality
      (fenchelConjugate n f) hproperConj g x hfy
  have hqToRealLe : (fenchelConjugate n f q.1).toReal ≤ q.2 := by
    -- Replace `f*(q.1)` by its real height now that finiteness is known.
    exact_mod_cast
      (show (((fenchelConjugate n f q.1).toReal : Real) : EReal) ≤ (q.2 : EReal) by
        rw [EReal.coe_toReal hqTop hqBot]
        exact hqLe)
  have hAttq :
      ((dotProduct x q.1 : Real) : EReal) - fenchelConjugate n f q.1 ≤
        ((dotProduct x g : Real) : EReal) - fenchelConjugate n f g := by
    simpa [dotProduct_comm] using hatt q.1
  have hGraphLeTargetE :
      (((dotProduct x q.1 - (fenchelConjugate n f q.1).toReal : Real) : Real) : EReal) ≤
        (((dotProduct x g - (fenchelConjugate n f g).toReal : Real) : Real) : EReal) := by
    -- Convert the Fenchel bound to real graph heights on both sides.
    simpa [EReal.coe_sub, EReal.coe_toReal hqTop hqBot,
      EReal.coe_toReal hgFinite.1 hgFinite.2] using hAttq
  have hGraphLeTarget :
      dotProduct x q.1 - (fenchelConjugate n f q.1).toReal ≤
        dotProduct x g - (fenchelConjugate n f g).toReal := by
    exact_mod_cast hGraphLeTargetE
  have hValueLeGraph :
      dotProduct x q.1 - q.2 ≤
        dotProduct x q.1 - (fenchelConjugate n f q.1).toReal := by
    -- Real epigraph heights can only lower the exposing value.
    linarith
  have hGraphLeValue :
      dotProduct x q.1 - (fenchelConjugate n f q.1).toReal ≤
        dotProduct x q.1 - q.2 := by
    -- Equality with the target exposing value forces the graph-value branch to agree as well.
    rw [hEq]
    exact hGraphLeTarget
  have hSameHeight :
      dotProduct x q.1 - q.2 =
        dotProduct x q.1 - (fenchelConjugate n f q.1).toReal :=
    le_antisymm hValueLeGraph hGraphLeValue
  linarith

end Section25
end Chap05
