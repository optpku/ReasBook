/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section28_part9

open scoped BigOperators Pointwise

section Chap06
section Section28

/-!
Helpers for Proposition 6.28.1.

The proof follows the Chapter 23 finite-sum subdifferential rule under a common
`intrinsicInterior` effective-domain qualification, and then transports the resulting
dual-space equality through the dot-product identification to the Euclideanized
subdifferentials used in Chapter 6.
-/

/-- Helper for Proposition 6.28.1: rewrite the indicator reformulation objective as a single
finite sum indexed by `Fin (m+1)`, matching the input form of the Chapter 23 sum rule. -/
lemma helperForProposition_6_28_1_indicatorReformulationObjective_eq_finSum
    {n m : ℕ} (f₀ : (Fin n → ℝ) → ℝ) (constraints : Fin m → (Fin n → ℝ) → ℝ) :
    (fun y : Fin n → ℝ =>
        ∑ j : Fin (m + 1),
          (Fin.cases (motive := fun _ => (Fin n → ℝ) → EReal)
              (fun x : Fin n → ℝ => ((f₀ x : ℝ) : EReal))
              (fun i : Fin m =>
                indicatorFunction {z : Fin n → ℝ | constraints i z ≤ 0}) j) y) =
      indicatorReformulationObjective f₀ constraints := by
  -- Split the `Fin (m+1)` sum into the `0`-summand plus the `Fin m` tail.
  funext y
  simp [indicatorReformulationObjective, Fin.sum_univ_succ]

/-- Helper for Proposition 6.28.1: a real-valued convex function on `ℝⁿ` (coerced to `EReal`)
is a proper convex function on `Set.univ`. -/
lemma helperForProposition_6_28_1_properConvexFunctionOn_univ_coe_of_convexOn
    {n : ℕ} {g : (Fin n → ℝ) → ℝ} (hg : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) g) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun x => ((g x : ℝ) : EReal)) := by
  -- Properness is immediate: the epigraph contains `(0, g 0)` and coercions never equal `⊥`.
  have hconv :
      ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun x => ((g x : ℝ) : EReal)) :=
    convexFunctionOn_of_convexOn_real (S := (Set.univ : Set (Fin n → ℝ))) hg
  have hne :
      Set.Nonempty
        (epigraph (Set.univ : Set (Fin n → ℝ)) (fun x => ((g x : ℝ) : EReal))) := by
    -- `(0, g 0)` lies in the epigraph by reflexivity of `≤`.
    refine ⟨((0 : Fin n → ℝ), g 0), ?_⟩
    refine And.intro ?_ ?_
    · -- `Set.univ` holds for every point.
      change (0 : Fin n → ℝ) ∈ (Set.univ : Set (Fin n → ℝ))
      simp
    · exact le_rfl
  have hnotbot :
      ∀ x ∈ (Set.univ : Set (Fin n → ℝ)), ((g x : ℝ) : EReal) ≠ (⊥ : EReal) := by
    intro x hx
    exact EReal.coe_ne_bot (g x)
  exact ⟨hconv, hne, hnotbot⟩

/-- Helper for Proposition 6.28.1: the indicator functions of the convex constraint sets are
proper convex functions, using the common intrinsic-interior witness to obtain nonemptiness. -/
lemma helperForProposition_6_28_1_properConvexFunctionOn_indicator_summands
    {n m : ℕ} (constraints : Fin m → (Fin n → ℝ) → ℝ)
    (hconstraints : ∀ i : Fin m, Convex ℝ {y : Fin n → ℝ | constraints i y ≤ 0})
    (hri :
      ∃ z : Fin n → ℝ,
        ∀ i : Fin m, z ∈ intrinsicInterior ℝ {y : Fin n → ℝ | constraints i y ≤ 0}) :
    ∀ i : Fin m,
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) := by
  classical
  rcases hri with ⟨z, hz⟩
  intro i
  -- The intrinsic-interior point lies in the set itself, hence the set is nonempty.
  have hzC :
      z ∈ {y : Fin n → ℝ | constraints i y ≤ 0} :=
    (intrinsicInterior_subset : intrinsicInterior ℝ {y : Fin n → ℝ | constraints i y ≤ 0} ⊆
        {y : Fin n → ℝ | constraints i y ≤ 0}) (hz i)
  have hne : ({y : Fin n → ℝ | constraints i y ≤ 0} : Set (Fin n → ℝ)).Nonempty := ⟨z, hzC⟩
  exact properConvexFunctionOn_indicator_of_convex_of_nonempty (hconstraints i) hne

/-- Helper for Proposition 6.28.1: a real-valued function coerced to `EReal` is finite
everywhere, so its effective domain on `Set.univ` is all of `ℝⁿ`. -/
lemma helperForProposition_6_28_1_effectiveDomain_univ_coe_eq_univ
    {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => ((g x : ℝ) : EReal)) = Set.univ := by
  -- Use the characterization `dom f = {x | x ∈ S ∧ f x < ⊤}`.
  ext x
  constructor
  · intro hx
    simp
  · intro hx
    -- Membership is automatic since `((g x : ℝ) : EReal) < ⊤`.
    have hx' :
        x ∈ {y : Fin n → ℝ |
              y ∈ (Set.univ : Set (Fin n → ℝ)) ∧ ((g y : ℝ) : EReal) < (⊤ : EReal)} := by
      refine And.intro ?_ ?_
      · simp
      · simpa using (EReal.coe_lt_top (g x))
    simpa [effectiveDomain_eq] using hx'

/-- Helper for Proposition 6.28.1: build the common intrinsic-interior qualification for the
`Fin (m+1)` summand family used in the sum-rule proof. -/
lemma helperForProposition_6_28_1_sumRule_qualification_for_fFam
    {n m : ℕ} (f₀ : (Fin n → ℝ) → ℝ) (constraints : Fin m → (Fin n → ℝ) → ℝ)
    (hri :
      ∃ z : Fin n → ℝ,
        ∀ i : Fin m, z ∈ intrinsicInterior ℝ {y : Fin n → ℝ | constraints i y ≤ 0}) :
    ∃ z : Fin n → ℝ,
      ∀ j : Fin (m + 1),
        z ∈ intrinsicInterior ℝ
          (effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (Fin.cases (motive := fun _ => (Fin n → ℝ) → EReal)
              (fun x : Fin n → ℝ => ((f₀ x : ℝ) : EReal))
              (fun i : Fin m =>
                indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) j)) := by
  classical
  rcases hri with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  intro j
  refine Fin.cases ?_ ?_ j
  · -- The `0`-summand is finite everywhere, hence has effective domain `univ`.
    -- We therefore only need `z ∈ intrinsicInterior ℝ Set.univ`, which follows from
    -- `interior univ = univ` and `interior ⊆ intrinsicInterior`.
    have hdom :
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => ((f₀ x : ℝ) : EReal)) = Set.univ :=
      helperForProposition_6_28_1_effectiveDomain_univ_coe_eq_univ (g := f₀)
    have hzUniv : z ∈ (Set.univ : Set (Fin n → ℝ)) := by
      simp
    have hzInterior : z ∈ interior (Set.univ : Set (Fin n → ℝ)) := by
      -- `z` is in the interior of `univ` because `interior univ = univ`.
      simpa [interior_univ] using hzUniv
    have hzII : z ∈ intrinsicInterior ℝ (Set.univ : Set (Fin n → ℝ)) :=
      (interior_subset_intrinsicInterior (s := (Set.univ : Set (Fin n → ℝ)))) hzInterior
    simpa [hdom] using hzII
  · intro i
    -- For indicator summands, `dom (indicatorFunction C) = C`.
    -- Avoid `simp` unfolding `intrinsicInterior`; just rewrite the effective domain.
    -- This keeps typeclass inference stable.
    change
      z ∈ intrinsicInterior ℝ
        (effectiveDomain Set.univ (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}))
    rw [effectiveDomain_indicatorFunction_eq (C := {y : Fin n → ℝ | constraints i y ≤ 0})]
    exact hz i

/-- Helper for Proposition 6.28.1: transport a dual-space finite-sum subdifferential identity
through the dot-product equivalence to obtain the Euclideanized identity. -/
lemma helperForProposition_6_28_1_euclideanSubdifferentialAt_sum_eq_sum
    {n k : ℕ} (f : Fin k → (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (hdual :
      subdifferentialAt (fun y : Fin n → ℝ => ∑ i : Fin k, f i y) x =
        ∑ i : Fin k, (subdifferentialAt (f i) x : Set (Module.Dual ℝ (Fin n → ℝ)))) :
    euclideanSubdifferentialAt (fun y : Fin n → ℝ => ∑ i : Fin k, f i y) x =
      ∑ i : Fin k, (euclideanSubdifferentialAt (f i) x : Set (Fin n → ℝ)) := by
  classical
  -- We prove set equality by membership, unfolding `euclideanSubdifferentialAt` and using
  -- `Set.mem_fintype_sum` to translate Minkowski-sum membership into decomposition data.
  let e : (Fin n → ℝ) ≃ₗ[ℝ] Module.Dual ℝ (Fin n → ℝ) := dotProductEquiv ℝ (Fin n)
  ext g
  constructor
  · intro hg
    -- Move from the Euclideanized subdifferential to the dual subdifferential.
    have hgdual : e g ∈ subdifferentialAt (fun y : Fin n → ℝ => ∑ i : Fin k, f i y) x := by
      simpa [euclideanSubdifferentialAt, e] using hg
    -- Use the dual identity to obtain a dual decomposition.
    have hgdual' :
        e g ∈ ∑ i : Fin k, (subdifferentialAt (f i) x : Set (Module.Dual ℝ (Fin n → ℝ))) := by
      simpa [hdual] using hgdual
    rcases
        (Set.mem_fintype_sum
          (f := fun i : Fin k =>
            (subdifferentialAt (f i) x : Set (Module.Dual ℝ (Fin n → ℝ))))
          (a := e g)).1 hgdual' with
      ⟨parts, hparts, hsum⟩
    -- Pull the dual decomposition back to a Euclidean one using `e.symm`.
    let partsE : Fin k → (Fin n → ℝ) := fun i => e.symm (parts i)
    have hpartsE :
        ∀ i : Fin k, partsE i ∈ euclideanSubdifferentialAt (f i) x := by
      intro i
      have : e (partsE i) ∈ subdifferentialAt (f i) x := by
        -- `e (e.symm (parts i)) = parts i`.
        simpa [partsE, e] using hparts i
      simpa [euclideanSubdifferentialAt, partsE, e] using this
    have hsumE : (∑ i : Fin k, partsE i) = g := by
      -- Apply `e.symm` to the dual sum identity and use additivity to move across the sum.
      have hsum' : e.symm (∑ i : Fin k, parts i) = e.symm (e g) := congrArg e.symm hsum
      have hmap :
          e.symm (∑ i : Fin k, parts i) = ∑ i : Fin k, e.symm (parts i) := by
        -- `map_sum` for the additive hom underlying the linear equivalence `e.symm`.
        simpa [e] using
          (map_sum (g := (e.symm.toLinearMap.toAddMonoidHom)) (f := parts)
            (s := (Finset.univ : Finset (Fin k))))
      -- Finish by rewriting the left-hand side using `hmap` and simplifying `e.symm (e g) = g`.
      have hsum'' : (∑ i : Fin k, e.symm (parts i)) = g := by
        have hsum1 : (∑ i : Fin k, e.symm (parts i)) = e.symm (e g) := by
          simpa [hmap] using hsum'
        simpa [e] using hsum1
      simpa [partsE] using hsum''
    refine
      (Set.mem_fintype_sum
        (f := fun i : Fin k => (euclideanSubdifferentialAt (f i) x : Set (Fin n → ℝ)))
        (a := g)).2 ?_
    exact ⟨partsE, hpartsE, hsumE⟩
  · intro hg
    -- Start with a Euclidean decomposition for Minkowski-sum membership.
    rcases
        (Set.mem_fintype_sum
          (f := fun i : Fin k => (euclideanSubdifferentialAt (f i) x : Set (Fin n → ℝ)))
          (a := g)).1 hg with
      ⟨partsE, hpartsE, hsumE⟩
    let parts : Fin k → Module.Dual ℝ (Fin n → ℝ) := fun i => e (partsE i)
    have hparts :
        ∀ i : Fin k, parts i ∈ subdifferentialAt (f i) x := by
      intro i
      have : partsE i ∈ euclideanSubdifferentialAt (f i) x := hpartsE i
      -- Unfold `euclideanSubdifferentialAt` to get the dual membership.
      simpa [euclideanSubdifferentialAt, parts, e] using this
    have hsum : (∑ i : Fin k, parts i) = e g := by
      -- Map the Euclidean sum identity through `e`.
      have hmap :
          e (∑ i : Fin k, partsE i) = ∑ i : Fin k, e (partsE i) := by
        simpa [e] using
          (map_sum (g := (e.toLinearMap.toAddMonoidHom)) (f := partsE)
            (s := (Finset.univ : Finset (Fin k))))
      simpa [parts, e, hmap] using congrArg e hsumE
    have hgdual :
        e g ∈ ∑ i : Fin k, (subdifferentialAt (f i) x : Set (Module.Dual ℝ (Fin n → ℝ))) := by
      refine
        (Set.mem_fintype_sum
          (f := fun i : Fin k =>
            (subdifferentialAt (f i) x : Set (Module.Dual ℝ (Fin n → ℝ))))
          (a := e g)).2 ?_
      exact ⟨parts, hparts, hsum⟩
    have hgdual' : e g ∈ subdifferentialAt (fun y : Fin n → ℝ => ∑ i : Fin k, f i y) x := by
      -- Use the dual identity backwards.
      simpa [hdual] using hgdual
    -- Return to the Euclideanized subdifferential by unfolding the preimage.
    simpa [euclideanSubdifferentialAt, e] using hgdual'

/-- Helper for Proposition 6.28.1: rewrite a `Fin (m+1)` Minkowski sum as the `0`-summand plus
the `Fin m` tail. -/
lemma helperForProposition_6_28_1_finSucc_setSum_rewrite
    {n m : ℕ} (S : Fin (m + 1) → Set (Fin n → ℝ)) :
    (∑ j : Fin (m + 1), S j) = S 0 + ∑ i : Fin m, S i.succ := by
  -- This is the standard `Fin` sum split lemma, specialized to Minkowski sums of sets.
  simpa using (Fin.sum_univ_succ (f := S))

-- Proof sketch: view `indicatorReformulationObjective f₀ constraints` as the finite sum of the
-- extended-real objective `fun y ↦ (f₀ y : EReal)` and the indicator functions of the convex sets
-- `Cᵢ = {y | constraints i y ≤ 0}`. Because `f₀` is finite everywhere, its effective domain is
-- all of `ℝⁿ`; the common intrinsic-interior point of the `Cᵢ` therefore gives the qualification
-- needed for the finite subdifferential sum rule. Translating that Chapter 23 result into the
-- Euclideanized subdifferential notation yields the stated Minkowski-sum identity.
/-- Proposition 6.28.1: Assume `f₀` is convex on `ℝ^n`, each constraint set
`Cᵢ = {y | constraints i y ≤ 0}` is convex, and the sets `C₁, …, C_m` have a common point in
their intrinsic interiors. Then for every `x ∈ ℝ^n`,
`∂ (indicatorReformulationObjective f₀ constraints) (x)` equals the Minkowski sum of
`∂ (fun y ↦ (f₀ y : EReal)) (x)` and the subdifferentials of the indicator functions
`δ(· | Cᵢ)`. -/
theorem subdifferential_indicatorReformulationObjective_eq_sum
    {n m : ℕ} (f₀ : (Fin n → ℝ) → ℝ) (constraints : Fin m → (Fin n → ℝ) → ℝ)
    (hf₀ : ConvexOn ℝ Set.univ f₀)
    (hconstraints : ∀ i : Fin m, Convex ℝ {y : Fin n → ℝ | constraints i y ≤ 0})
    (hri :
      ∃ z : Fin n → ℝ,
        ∀ i : Fin m, z ∈ intrinsicInterior ℝ {y : Fin n → ℝ | constraints i y ≤ 0})
    (x : Fin n → ℝ) :
    euclideanSubdifferentialAt (indicatorReformulationObjective f₀ constraints) x =
      euclideanSubdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x +
        ∑ i : Fin m,
          (euclideanSubdifferentialAt
            (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
            Set (Fin n → ℝ)) := by
  classical
  -- Step 1: package the objective as a `Fin (m+1)` finite sum.
  let fFam : Fin (m + 1) → (Fin n → ℝ) → EReal :=
    fun j =>
      Fin.cases (motive := fun _ => (Fin n → ℝ) → EReal)
        (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal))
        (fun i : Fin m => indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) j
  have hObj :
      (fun y : Fin n → ℝ => ∑ j : Fin (m + 1), fFam j y) =
        indicatorReformulationObjective f₀ constraints := by
    -- This is a direct computation using `Fin.sum_univ_succ`.
    simpa [fFam] using
      (helperForProposition_6_28_1_indicatorReformulationObjective_eq_finSum
        (f₀ := f₀) (constraints := constraints))
  -- Step 2: show each summand is proper convex on `Set.univ`.
  have hproper : ∀ j : Fin (m + 1), ProperConvexFunctionOn Set.univ (fFam j) := by
    intro j
    refine Fin.cases ?_ ?_ j
    · -- The `0`-summand comes from the convex real objective.
      simpa [fFam] using
        (helperForProposition_6_28_1_properConvexFunctionOn_univ_coe_of_convexOn
          (g := f₀) hf₀)
    · intro i
      -- Each indicator summand is proper convex by convexity + nonemptiness.
      have hind :
          ∀ i : Fin m,
            ProperConvexFunctionOn Set.univ
              (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) :=
        helperForProposition_6_28_1_properConvexFunctionOn_indicator_summands
          (constraints := constraints) hconstraints hri
      simpa [fFam] using hind i
  -- Step 3: build the common intrinsic-interior point for the effective domains.
  have hii :
      ∃ z : Fin n → ℝ,
        ∀ j : Fin (m + 1),
          z ∈ intrinsicInterior ℝ (effectiveDomain Set.univ (fFam j)) := by
    -- Reuse the intrinsic-interior witness for the constraint sets, and note that the `0`-summand
    -- has effective domain `univ` because it is finite everywhere.
    rcases hri with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    intro j
    refine Fin.cases ?_ ?_ j
    · -- `fFam 0` is the real objective coerced to `EReal`, hence has effective domain `univ`.
      have hdom0 :
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fun x => ((f₀ x : ℝ) : EReal)) = Set.univ :=
        helperForProposition_6_28_1_effectiveDomain_univ_coe_eq_univ (g := f₀)
      have hdom : effectiveDomain Set.univ (fFam 0) = Set.univ := by
        simpa [fFam] using hdom0
      have hzInterior : z ∈ interior (Set.univ : Set (Fin n → ℝ)) := by
        have hzUniv : z ∈ (Set.univ : Set (Fin n → ℝ)) := by
          simp
        simpa [interior_univ] using hzUniv
      have hzII : z ∈ intrinsicInterior ℝ (Set.univ : Set (Fin n → ℝ)) :=
        (interior_subset_intrinsicInterior (s := (Set.univ : Set (Fin n → ℝ)))) hzInterior
      simpa [hdom] using hzII
    · intro i
      -- For indicator summands, rewrite the effective domain back to the underlying set.
      change
        z ∈ intrinsicInterior ℝ
          (effectiveDomain Set.univ (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}))
      rw [effectiveDomain_indicatorFunction_eq (C := {y : Fin n → ℝ | constraints i y ≤ 0})]
      exact hz i
  -- Step 4: apply the Chapter 23 finite-sum rule in the dual space.
  have hdual :
      subdifferentialAt (fun y : Fin n → ℝ => ∑ j : Fin (m + 1), fFam j y) x =
        ∑ j : Fin (m + 1),
          (subdifferentialAt (fFam j) x : Set (Module.Dual ℝ (Fin n → ℝ))) := by
    -- This is Theorem 23.8(2), intrinsic-interior effective-domain form.
    simpa using
      (subdifferential_sum_eq_sum_of_commonIntrinsicInteriorEffectiveDomain
        (f := fFam) hproper hii x)
  -- Step 5: transport the identity to Euclideanized subdifferentials and rewrite the sum index.
  have heuc :
      euclideanSubdifferentialAt (fun y : Fin n → ℝ => ∑ j : Fin (m + 1), fFam j y) x =
        ∑ j : Fin (m + 1), (euclideanSubdifferentialAt (fFam j) x : Set (Fin n → ℝ)) :=
    helperForProposition_6_28_1_euclideanSubdifferentialAt_sum_eq_sum (f := fFam) (x := x) hdual
  -- Rewrite the objective and split the `Fin (m+1)` Minkowski sum into `0` plus the tail.
  have heucObj :
      euclideanSubdifferentialAt (indicatorReformulationObjective f₀ constraints) x =
        ∑ j : Fin (m + 1), (euclideanSubdifferentialAt (fFam j) x : Set (Fin n → ℝ)) := by
    -- Replace the sum function by the indicator reformulation objective using `hObj`.
    simpa [hObj] using heuc
  -- Now rewrite the `Fin (m+1)` sum to match the statement's `A + ∑ i, ...` shape.
  calc
    euclideanSubdifferentialAt (indicatorReformulationObjective f₀ constraints) x
        = ∑ j : Fin (m + 1), (euclideanSubdifferentialAt (fFam j) x : Set (Fin n → ℝ)) := heucObj
    _ = (euclideanSubdifferentialAt (fFam 0) x : Set (Fin n → ℝ)) +
          ∑ i : Fin m, (euclideanSubdifferentialAt (fFam i.succ) x : Set (Fin n → ℝ)) := by
          simpa using
            (helperForProposition_6_28_1_finSucc_setSum_rewrite
              (S := fun j : Fin (m + 1) => (euclideanSubdifferentialAt (fFam j) x : Set (Fin n → ℝ))))
    _ = euclideanSubdifferentialAt (fun y : Fin n → ℝ => ((f₀ y : ℝ) : EReal)) x +
          ∑ i : Fin m,
            (euclideanSubdifferentialAt
              (indicatorFunction {y : Fin n → ℝ | constraints i y ≤ 0}) x :
              Set (Fin n → ℝ)) := by
          -- Unfold the family at `0` and at `succ i`.
          simp [fFam]

-- Proof sketch: identify the indicator subdifferential with the normal cone of the sublevel set
-- `C = {y | constraint y ≤ 0}` by the Chapter 23 indicator-function theorem. Then analyze the
-- three regimes of the point `x`: on the boundary `constraint x = 0`, the normal cone to a convex
-- sublevel set is the cone generated by the subdifferential of the active constraint; in the
-- interior `constraint x < 0`, the normal cone collapses to `{0}`; and outside the set
-- `constraint x > 0`, the indicator subdifferential is empty.
/-- Helper for Proposition 6.28.2: the sublevel set `{y | (y 0)^2 ≤ 0}` in dimension `1` is the
singleton `{0}`. -/
lemma helperForProposition_6_28_2_sublevelSet_evalSq_eq_singleton_zero :
    {y : Fin 1 → ℝ | (y 0) ^ (2 : ℕ) ≤ 0} = ({0} : Set (Fin 1 → ℝ)) := by
  ext y
  constructor
  · intro hy
    -- Since squares are nonnegative, `y 0 ^ 2 ≤ 0` forces `y 0 = 0`; in `Fin 1` this means `y=0`.
    have hy0sq : (y 0) ^ (2 : ℕ) = 0 := by
      refine le_antisymm hy ?_
      -- `0 ≤ (y 0)^2` is `sq_nonneg (y 0)`, rewritten to `^ 2`.
      simpa [pow_two] using (sq_nonneg (y 0))
    have hy0pow : (y 0) ^ (2 : ℕ) = 0 := hy0sq
    have hy0pow' : (y 0) ^ 2 = 0 := by
      simpa using hy0pow
    have hy0 : y 0 = 0 := by
      -- Turn `y 0 ^ 2 = 0` into `y 0 = 0`.
      exact sq_eq_zero_iff.mp hy0pow'
    have hyfun : y = 0 := by
      funext i
      have hi : i = 0 := Fin.eq_zero i
      -- There is only one coordinate, so `y i = y 0 = 0`.
      simpa [hi, hy0]
    simpa [Set.mem_singleton_iff, hyfun]
  · intro hy
    -- For `y = 0`, the square is `0`, hence `≤ 0`.
    have hy' : y = 0 := by simpa [Set.mem_singleton_iff] using hy
    subst hy'
    simp

/-- Helper for Proposition 6.28.2: the normal cone (as defined in Chapter 23) of `{0}` at `0` is
all dual vectors, because the only inequality to check is on `z=0`. -/
lemma helperForProposition_6_28_2_normalConeAt_singleton_zero_eq_univ :
    normalConeAt ({0} : Set (Fin 1 → ℝ)) (0 : Fin 1 → ℝ) = Set.univ := by
  ext xStar
  constructor
  · intro hxStar
    -- Membership in `Set.univ` is trivial.
    trivial
  · intro hxStar
    -- Unpack the definition: `0 ∈ {0}` and `xStar (0 - 0) ≤ 0`.
    refine And.intro ?_ ?_
    · simp
    · intro z hz
      have hz0 : z = (0 : Fin 1 → ℝ) := by simpa [Set.mem_singleton_iff] using hz
      subst hz0
      -- Linear maps send `0` to `0`.
      simpa using (le_rfl : (0 : ℝ) ≤ 0)

/-- Helper for Proposition 6.28.2: the subdifferential of `y ↦ (y 0)^2` (coerced to `EReal`) at
`0` in dimension `1` is the singleton `{0}`. -/
lemma helperForProposition_6_28_2_subdifferentialAt_evalSq_coeEReal_zero_eq_singleton :
    subdifferentialAt (fun y : Fin 1 → ℝ => (((y 0) ^ (2 : ℕ) : ℝ) : EReal)) (0 : Fin 1 → ℝ) =
      ({0} : Set (Module.Dual ℝ (Fin 1 → ℝ))) := by
  classical
  -- Prove set equality by membership, unfolding `subdifferentialAt` into the subgradient inequality.
  ext xStar
  constructor
  · intro hxStar
    -- Show any subgradient must vanish on the `1`-dimensional basis vector `1`.
    have hxStarIneq :
        IsSubgradientAt (fun y : Fin 1 → ℝ => (((y 0) ^ (2 : ℕ) : ℝ) : EReal))
          (0 : Fin 1 → ℝ) xStar := hxStar
    let oneFun : Fin 1 → ℝ := fun _ => (1 : ℝ)
    let c : ℝ := xStar oneFun
    have hc : c = 0 := by
      -- Route correction: use a direct algebraic contradiction at `z = (c/2) * 1`.
      by_contra hc0
      let z : Fin 1 → ℝ := (c / 2) • oneFun
      have hzIneq := hxStarIneq z
      -- Convert the `EReal` subgradient inequality into a real inequality `xStar z ≤ (z 0)^2`.
      have hzIneq' :
          (0 : EReal) + ((xStar (z - (0 : Fin 1 → ℝ)) : ℝ) : EReal) ≤
            (((z 0) ^ (2 : ℕ) : ℝ) : EReal) := by
        simpa [IsSubgradientAt, ge_iff_le] using hzIneq
      have hzIneq'' :
          ((xStar z : ℝ) : EReal) ≤ (((z 0) ^ (2 : ℕ) : ℝ) : EReal) := by
        -- `z - 0 = z` and `0 + a = a`.
        simpa [z, zero_add, sub_zero] using hzIneq'
      have hzle : xStar z ≤ (z 0) ^ (2 : ℕ) := by
        -- Both sides are real-valued coercions, so `EReal.coe_le_coe_iff` applies.
        have hzIneqCo :
            ((xStar z : ℝ) : EReal) ≤ (((z 0) ^ (2 : ℕ) : ℝ) : EReal) := hzIneq''
        exact (EReal.coe_le_coe_iff).1 hzIneqCo
      -- Rewrite `z` and `xStar z` using linearity; this gives an impossible inequality unless `c=0`.
      have hzCoord : z 0 = c / 2 := by
        -- Pointwise scalar multiplication makes `z` constant.
        simp [z, oneFun, smul_eq_mul]
      have hxStarz : xStar z = (c / 2) * c := by
        -- `z = (c/2) • oneFun` and `xStar (t • v) = t • xStar v`.
        calc
          xStar z = (c / 2) • xStar oneFun := by
            simpa [z] using (xStar.map_smul (c / 2) oneFun)
          _ = (c / 2) * c := by
            simp [c, smul_eq_mul]
      have hineq : (c / 2) * c ≤ (c / 2) ^ (2 : ℕ) := by
        -- Substitute the coordinate computation `z 0 = c/2` into `hzle`.
        simpa [hxStarz, hzCoord] using hzle
      -- `hineq` simplifies to `c^2/2 ≤ c^2/4`, forcing `c = 0`, contradicting `hc0`.
      have hineq' : (c / 2) * c ≤ (c / 2) * (c / 2) := by
        simpa [pow_two] using hineq
      have hcEq : c = 0 := by
        nlinarith [hineq']
      exact hc0 hcEq
    -- Once `c=0`, the functional vanishes on all of `Fin 1 → ℝ`, hence is the zero map.
    have hxStar0 : xStar = 0 := by
      -- Use `LinearMap.ext` explicitly to keep the argument type as `Fin 1 → ℝ`.
      refine LinearMap.ext ?_
      intro y
      have hy : y = (y 0) • (fun _ : Fin 1 => (1 : ℝ)) := by
        funext i
        have hi : i = 0 := Fin.eq_zero i
        simp [hi, smul_eq_mul]
      -- Rewrite `y` as a scalar multiple of `oneFun` and use linearity plus `c=0`.
      have hxStar_oneFun : xStar (fun _ : Fin 1 => (1 : ℝ)) = 0 := by
        -- `hc : c = 0` with `c = xStar oneFun`.
        simpa [c, oneFun] using hc
      have hxStar_y : xStar y = (y 0) • xStar (fun _ : Fin 1 => (1 : ℝ)) := by
        -- Apply `xStar` to the representation `hy`, then use `map_smul`.
        have h1 : xStar y = xStar ((y 0) • (fun _ : Fin 1 => (1 : ℝ))) := congrArg xStar hy
        have h2 :
            xStar ((y 0) • (fun _ : Fin 1 => (1 : ℝ))) =
              (y 0) • xStar (fun _ : Fin 1 => (1 : ℝ)) :=
          xStar.map_smul (y 0) (fun _ : Fin 1 => (1 : ℝ))
        exact h1.trans h2
      -- The scalar multiple is `0` because `xStar oneFun = 0`.
      simpa [hxStar_oneFun, smul_eq_mul] using hxStar_y
    -- Finish: membership in `{0}` means equality to `0`.
    simpa [Set.mem_singleton_iff, hxStar0]
  · intro hxStar
    -- The zero dual vector is always a subgradient of a nonnegative function at `0`.
    have hxStar0 : xStar = 0 := by simpa [Set.mem_singleton_iff] using hxStar
    subst hxStar0
    intro z
    -- Turn the goal into `0 ≤ (z 0)^2` in `EReal`.
    have hzNonneg : (0 : ℝ) ≤ (z 0) ^ (2 : ℕ) := by
      simpa [pow_two] using (sq_nonneg (z 0))
    have hzNonnegE :
        ((0 : ℝ) : EReal) ≤ (((z 0) ^ (2 : ℕ) : ℝ) : EReal) :=
      (EReal.coe_le_coe_iff).2 hzNonneg
    -- Unfold the definitions and simplify `f 0 = 0` and `0 (z - 0) = 0`.
    simpa [IsSubgradientAt, ge_iff_le, sub_eq_add_neg] using hzNonnegE

/-- Helper for Proposition 6.28.2: `indicatorFunction ∅` is the constant `⊤` function, hence its
subdifferential is `Set.univ` at every point under Definition 23.0.6. -/
lemma helperForProposition_6_28_2_subdifferentialAt_indicator_empty_eq_univ
    {n : ℕ} (x : Fin n → ℝ) :
    subdifferentialAt (indicatorFunction (∅ : Set (Fin n → ℝ))) x = Set.univ := by
  classical
  ext xStar
  constructor
  · intro hxStar
    trivial
  · intro hxStar
    -- Every `xStar` satisfies the subgradient inequality because both sides are `⊤`.
    intro z
    -- `indicatorFunction ∅ _ = ⊤` and `⊤ + (real) = ⊤`.
    simp [IsSubgradientAt, indicatorFunction, EReal.top_add_coe]

/-- Helper for Proposition 6.28.2: the sublevel set `C = {y | constraint y ≤ 0}` is empty if and
only if there is no point satisfying the feasibility inequality `constraint y ≤ 0`. -/
lemma helperForProposition_6_28_2_sublevelSet_eq_empty_iff_not_exists_le_zero
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) :
    (({y : Fin n → ℝ | constraint y ≤ 0} : Set (Fin n → ℝ)) = ∅) ↔
      ¬ ∃ y : Fin n → ℝ, constraint y ≤ 0 := by
  classical
  constructor
  · intro hEmpty hExists
    -- A feasible witness gives an element of the sublevel set, contradicting emptiness.
    rcases hExists with ⟨y, hy⟩
    have : y ∈ ({y : Fin n → ℝ | constraint y ≤ 0} : Set (Fin n → ℝ)) := hy
    simpa [hEmpty] using this
  · intro hNoExists
    -- Prove set equality by extensionality; membership is exactly the feasibility inequality.
    ext y
    constructor
    · intro hy
      exfalso
      exact hNoExists ⟨y, hy⟩
    · intro hy
      cases hy

/-- Helper for Proposition 6.28.2: if there is no feasible point `y` with `constraint y ≤ 0`, then
the indicator `δ(· | {y | constraint y ≤ 0})` is identically `⊤`, hence its subdifferential is
`Set.univ` at every point (under Definition 23.0.6). -/
lemma helperForProposition_6_28_2_subdifferentialAt_indicator_sublevelSet_eq_univ_of_not_exists_le_zero
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hne : ¬ ∃ y : Fin n → ℝ, constraint y ≤ 0) :
    subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
      (Set.univ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
  classical
  -- First convert the nonexistence of feasible points into an empty-set identity.
  have hEmpty :
      ({y : Fin n → ℝ | constraint y ≤ 0} : Set (Fin n → ℝ)) = ∅ :=
    (helperForProposition_6_28_2_sublevelSet_eq_empty_iff_not_exists_le_zero
      (constraint := constraint)).2 hne
  -- Then rewrite to the lemma for the empty indicator.
  simpa [hEmpty] using
    (helperForProposition_6_28_2_subdifferentialAt_indicator_empty_eq_univ (n := n) (x := x))

/-- Helper for Proposition 6.28.2: the normal cone of the empty set is empty, since membership
requires `x ∈ C`. -/
lemma helperForProposition_6_28_2_normalConeAt_empty_eq_empty
    {n : ℕ} (x : Fin n → ℝ) :
    normalConeAt (∅ : Set (Fin n → ℝ)) x =
      (∅ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
  classical
  ext xStar
  constructor
  · intro hxStar
    -- Unpack membership: it implies `x ∈ (∅ : Set _)`, which is impossible.
    have hx : x ∈ (∅ : Set (Fin n → ℝ)) := (mem_normalConeAt_iff.1 hxStar).1
    simpa using hx
  · intro hxStar
    cases hxStar

/-- Helper for Proposition 6.28.2: if the feasible sublevel set `{y | constraint y ≤ 0}` is empty,
then its normal cone is empty at every point. -/
lemma helperForProposition_6_28_2_normalConeAt_sublevelSet_eq_empty_of_not_exists_le_zero
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ)
    (hne : ¬ ∃ y : Fin n → ℝ, constraint y ≤ 0) :
    normalConeAt {y : Fin n → ℝ | constraint y ≤ 0} x =
      (∅ : Set (Module.Dual ℝ (Fin n → ℝ))) := by
  classical
  -- Turn `hne` into an explicit emptiness statement for the sublevel set, then rewrite.
  have hEmpty :
      ({y : Fin n → ℝ | constraint y ≤ 0} : Set (Fin n → ℝ)) = ∅ :=
    (helperForProposition_6_28_2_sublevelSet_eq_empty_iff_not_exists_le_zero
      (constraint := constraint)).2 hne
  simpa [hEmpty] using
    (helperForProposition_6_28_2_normalConeAt_empty_eq_empty (n := n) (x := x))

/-- Helper for Proposition 6.28.2: any feasible witness `y` with `constraint y ≤ 0` gives
nonemptiness of the sublevel set `{y | constraint y ≤ 0}`. -/
lemma helperForProposition_6_28_2_sublevelSet_nonempty_of_exists_feasible
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) (hne : ∃ y : Fin n → ℝ, constraint y ≤ 0) :
    ({y : Fin n → ℝ | constraint y ≤ 0} : Set (Fin n → ℝ)).Nonempty := by
  -- Unpack the feasible point and use it directly as the nonempty witness for the sublevel set.
  rcases hne with ⟨y, hy⟩
  exact ⟨y, hy⟩

/-- Helper for Proposition 6.28.2: if the sublevel set `C = {y | constraint y ≤ 0}` is nonempty,
then the subdifferential of its indicator agrees with the normal cone everywhere. -/
lemma helperForProposition_6_28_2_subdifferential_indicator_sublevelSet_eq_normalCone_of_exists_feasible
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) (hne : ∃ y : Fin n → ℝ, constraint y ≤ 0)
    (x : Fin n → ℝ) :
    subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
      normalConeAt {y : Fin n → ℝ | constraint y ≤ 0} x := by
  -- Convert the existential witness into `Set.Nonempty`, then invoke the Chapter 23 indicator theorem.
  have hCne : ({y : Fin n → ℝ | constraint y ≤ 0} : Set (Fin n → ℝ)).Nonempty :=
    helperForProposition_6_28_2_sublevelSet_nonempty_of_exists_feasible
      (constraint := constraint) hne
  simpa using
    (helperForCorollary_23_8_1_subdifferential_indicator_eq_normalCone_of_nonempty
      (C := ({y : Fin n → ℝ | constraint y ≤ 0} : Set (Fin n → ℝ))) hCne x)

/-- Helper for Proposition 6.28.2: if the sublevel set `C = {y | constraint y ≤ 0}` is nonempty,
then outside `C` (in particular when `0 < constraint x`) the indicator subdifferential is empty. -/
lemma helperForProposition_6_28_2_subdifferential_indicator_sublevelSet_eq_empty_of_exists_feasible_of_pos
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) (hne : ∃ y : Fin n → ℝ, constraint y ≤ 0)
    {x : Fin n → ℝ} (hx : 0 < constraint x) :
    subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x = ∅ := by
  classical
  -- Use the witness to show the set is nonempty, and `hx` to show `x ∉ C`.
  have hCne : ({y : Fin n → ℝ | constraint y ≤ 0} : Set (Fin n → ℝ)).Nonempty :=
    helperForProposition_6_28_2_sublevelSet_nonempty_of_exists_feasible
      (constraint := constraint) hne
  have hxC : x ∉ {y : Fin n → ℝ | constraint y ≤ 0} := by
    intro hxC
    have hxle : constraint x ≤ 0 := hxC
    exact (not_le_of_gt hx) hxle
  -- Chapter 23 gives `∂δ_C(x) = ∅` for nonempty `C` and `x ∉ C`.
  simpa using
    (subdifferential_indicatorFunction_eq_empty_of_not_mem
      (C := ({y : Fin n → ℝ | constraint y ≤ 0} : Set (Fin n → ℝ))) hCne hxC)

/-- Helper for Proposition 6.28.2: under strict feasibility (`∃ z, constraint z < 0`) at a boundary
point (`constraint x = 0`), the normal cone to the sublevel set is the cone generated by the
constraint subdifferential. -/
lemma helperForProposition_6_28_2_normalConeAt_sublevelSet_eq_iUnion_nonneg_smul_subdifferential_of_exists_strict
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) (hconstraint : ConvexOn ℝ Set.univ constraint)
    (x : Fin n → ℝ) (hx0 : constraint x = 0) (hstrict : ∃ z : Fin n → ℝ, constraint z < 0) :
    normalConeAt {y : Fin n → ℝ | constraint y ≤ 0} x =
      Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
        a.1 • subdifferentialAt (fun y : Fin n → ℝ => ((constraint y : ℝ) : EReal)) x := by
  classical
  -- Reduce to Corollary 23.7.1 applied to `f := constraint` coerced to `EReal`.
  let f : (Fin n → ℝ) → EReal := fun y => ((constraint y : ℝ) : EReal)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForProposition_6_28_1_properConvexFunctionOn_univ_coe_of_convexOn (g := constraint)
      hconstraint
  have hdom : effectiveDomain (Set.univ : Set (Fin n → ℝ)) f = Set.univ :=
    helperForProposition_6_28_1_effectiveDomain_univ_coe_eq_univ (g := constraint)
  have hxDom : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    -- `dom f = univ`, so `x` is automatically an interior point.
    simpa [hdom]
  have hnotmin : ∃ z : Fin n → ℝ, f z < f x := by
    -- Strict feasibility gives a point with strictly smaller value than the boundary value `0`.
    rcases hstrict with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    -- First rewrite the strict feasibility inequality as `constraint z < constraint x`.
    have hzx : constraint z < constraint x := by
      simpa [hx0] using hz
    -- Lift the real inequality to `EReal` after unfolding `f`.
    dsimp [f]
    exact (EReal.coe_lt_coe_iff.2 hzx)
  -- Identify the boundary sublevel set `{y | constraint y ≤ 0}` with `{y | f y ≤ f x}`.
  have hsublevel :
      {y : Fin n → ℝ | f y ≤ f x} = {y : Fin n → ℝ | constraint y ≤ 0} := by
    ext y
    -- Use `hx0` to rewrite `f x` and then drop coercions.
    have hx0' : (f x) = ((0 : ℝ) : EReal) := by
      dsimp [f]
      simpa [hx0]
    constructor
    · intro hy
      -- `((constraint y) : EReal) ≤ 0` implies `constraint y ≤ 0`.
      have hy' : (f y) ≤ ((0 : ℝ) : EReal) := by simpa [hx0'] using hy
      exact (EReal.coe_le_coe_iff.1 hy')
    · intro hy
      -- `constraint y ≤ 0` implies `((constraint y) : EReal) ≤ 0 = f x`.
      have hy' : (f y) ≤ ((0 : ℝ) : EReal) := (EReal.coe_le_coe_iff.2 hy)
      simpa [hx0'] using hy'
  -- Translate the `mem_euclideanNormalCone...` characterization back to the dual-space normal cone.
  let φ : (Fin n → ℝ) ≃ₗ[ℝ] Module.Dual ℝ (Fin n → ℝ) := dotProductEquiv ℝ (Fin n)
  ext xStar
  constructor
  · intro hxStar
    -- Move to Euclidean coordinates `v = φ.symm xStar` so we can apply Corollary 23.7.1.
    have hxStar' : xStar ∈ normalConeAt {y : Fin n → ℝ | f y ≤ f x} x := by
      -- Rewrite the set `{y | f y ≤ f x}` as the boundary sublevel set `constraint y ≤ 0`.
      simpa [hsublevel] using hxStar
    have hv :
        (φ.symm xStar) ∈ (φ ⁻¹' normalConeAt {y : Fin n → ℝ | f y ≤ f x} x) := by
      -- This is just rewriting `Set.mem_preimage` and `φ (φ.symm xStar) = xStar`.
      change φ (φ.symm xStar) ∈ normalConeAt {y : Fin n → ℝ | f y ≤ f x} x
      simpa [φ] using hxStar'
    have hv' :=
      (mem_euclideanNormalCone_sublevelSet_iff_exists_nonneg_smul_mem_subdifferential
        (n := n) f hproper x (φ.symm xStar) hxDom hnotmin).1 hv
    rcases hv' with ⟨a, ha, y, hy, hvEq⟩
    -- Convert the vector `y` back to a dual subgradient `g = φ y`.
    have hg : (φ y) ∈ subdifferentialAt f x := by
      -- Unfold `Set.preimage`: `y ∈ φ ⁻¹' ∂f(x)` means `φ y ∈ ∂f(x)`.
      change φ y ∈ subdifferentialAt f x
      simpa [Set.preimage, φ] using hy
    -- Apply `φ` to `hvEq` to get the dual equality `xStar = a • (φ y)`.
    have hxStarEq : xStar = a • (φ y) := by
      -- `φ (φ.symm xStar) = xStar` and `φ (a • y) = a • φ y`.
      have := congrArg φ hvEq
      simpa [φ, LinearEquiv.apply_symm_apply, LinearEquiv.map_smul] using this
    -- Package the result as membership in the union of nonnegative dilates.
    refine Set.mem_iUnion.2 ?_
    refine ⟨⟨a, ha⟩, ?_⟩
    -- Unfold the set scalar multiple and witness the image element `g = φ y`.
    change xStar ∈ (fun g : Module.Dual ℝ (Fin n → ℝ) => a • g) '' subdifferentialAt f x
    refine ⟨φ y, hg, ?_⟩
    exact hxStarEq.symm
  · intro hxStar
    -- Unpack the union into an explicit scalar and subgradient.
    rcases (Set.mem_iUnion.1 hxStar) with ⟨a, hxStar⟩
    rcases hxStar with ⟨g, hg, rfl⟩
    -- Apply Corollary 23.7.1 with `y = φ.symm g` in Euclidean coordinates.
    have hy :
        (φ.symm g) ∈ (φ ⁻¹' subdifferentialAt f x) := by
      simpa [Set.mem_preimage, φ] using hg
    have hv :
        (φ.symm (a.1 • g)) ∈ (φ ⁻¹' normalConeAt {y : Fin n → ℝ | f y ≤ f x} x) := by
      -- Use the reverse direction of Corollary 23.7.1, then rewrite by linearity of `φ.symm`.
      have hv' :
          ∃ b : ℝ, 0 ≤ b ∧
            ∃ y ∈ (φ ⁻¹' subdifferentialAt f x), (φ.symm (a.1 • g)) = b • y := by
        refine ⟨a.1, a.2, ?_⟩
        refine Exists.intro (φ.symm g) ?_
        refine And.intro hy ?_
        -- `φ.symm (a • g) = a • φ.symm g`.
        simpa [φ, LinearEquiv.map_smul]
      exact
        (mem_euclideanNormalCone_sublevelSet_iff_exists_nonneg_smul_mem_subdifferential
          (n := n) f hproper x (φ.symm (a.1 • g)) hxDom hnotmin).2 hv'
    -- Finally, translate back from Euclidean coordinates to the dual-space normal cone.
    have : (a.1 • g) ∈ normalConeAt {y : Fin n → ℝ | f y ≤ f x} x := by
      simpa [Set.mem_preimage, φ, LinearEquiv.apply_symm_apply] using hv
    simpa [hsublevel] using this

/-- Helper for Proposition 6.28.2: if a real-valued convex constraint satisfies `constraint x < 0`,
then `x` lies in the interior of the feasible sublevel set `{y | constraint y ≤ 0}`. -/
lemma helperForProposition_6_28_2_mem_interior_sublevelSet_of_lt_zero
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) (hconstraint : ConvexOn ℝ Set.univ constraint)
    {x : Fin n → ℝ} (hx : constraint x < 0) :
    x ∈ interior {y : Fin n → ℝ | constraint y ≤ 0} := by
  -- Use continuity of real-valued convex functions on the open set `Set.univ` to see that the
  -- strict sublevel set `{y | constraint y < 0}` is open.
  have hcontOn : ContinuousOn constraint (Set.univ : Set (Fin n → ℝ)) :=
    ConvexOn.continuousOn (E := Fin n → ℝ) (C := (Set.univ : Set (Fin n → ℝ)))
      (hC := isOpen_univ) hconstraint
  have hcont : Continuous constraint := by
    simpa [continuousOn_univ] using hcontOn
  have hopen : IsOpen {y : Fin n → ℝ | constraint y < 0} := by
    -- This is the standard “continuous < constant” open set.
    simpa using (isOpen_lt hcont continuous_const)
  have hsubset : {y : Fin n → ℝ | constraint y < 0} ⊆ {y : Fin n → ℝ | constraint y ≤ 0} := by
    intro y hy
    have : constraint y < 0 := by simpa using hy
    exact le_of_lt this
  have hxmem : x ∈ {y : Fin n → ℝ | constraint y < 0} := by simpa using hx
  -- Turn the open inclusion into a neighborhood inclusion, then use `x ∈ interior C ↔ C ∈ nhds x`.
  have hU_nhds : {y : Fin n → ℝ | constraint y < 0} ∈ nhds x := hopen.mem_nhds hxmem
  have hC_nhds : {y : Fin n → ℝ | constraint y ≤ 0} ∈ nhds x :=
    Filter.mem_of_superset hU_nhds hsubset
  exact (mem_interior_iff_mem_nhds).2 hC_nhds

/-- Helper for Proposition 6.28.2: at an interior point of a set `C`, the supporting-inequality
definition forces the normal cone `normalConeAt C x` to be exactly `{0}`. -/
lemma helperForProposition_6_28_2_normalConeAt_eq_singleton_zero_of_mem_interior
    {n : ℕ} {C : Set (Fin n → ℝ)} {x : Fin n → ℝ} (hx : x ∈ interior C) :
    normalConeAt C x = ({0} : Set (Module.Dual ℝ (Fin n → ℝ))) := by
  classical
  ext xStar
  constructor
  · intro hxStar
    -- Work with the metric characterization of interior points to get a ball around `x`
    -- contained in `C`, so we can test the normal-cone inequality in both directions.
    have hnhds : C ∈ nhds x := (mem_interior_iff_mem_nhds).1 hx
    rcases (Metric.mem_nhds_iff.1 hnhds) with ⟨ε, hε, hball⟩
    have hxStarIneq : ∀ z ∈ C, xStar (z - x) ≤ 0 :=
      (mem_normalConeAt_iff.1 hxStar).2
    have hxStar0 : xStar = 0 := by
      -- Show `xStar v = 0` for every direction `v` by applying the supporting inequality at
      -- points `x ± t v` inside the interior ball.
      apply LinearMap.ext
      intro v
      by_cases hv : v = 0
      · simp [hv]
      · have hvnorm : 0 < ‖v‖ := by
          simpa [norm_pos_iff] using hv
        have hvne : ‖v‖ ≠ 0 := ne_of_gt hvnorm
        let t : ℝ := ε / (2 * ‖v‖)
        have htpos : 0 < t := by
          have : 0 < 2 * ‖v‖ := by nlinarith [hvnorm]
          exact div_pos hε this
        -- First show `x + t v` is in the interior ball, hence in `C`.
        have hnorm_lt : ‖t • v‖ < ε := by
          calc
            ‖t • v‖ = |t| * ‖v‖ := by
              simpa [Real.norm_eq_abs] using (norm_smul t v)
            _ = t * ‖v‖ := by simp [abs_of_pos htpos]
            _ = ε / 2 := by
              -- Cancel `‖v‖` (nonzero) from `(ε / (2‖v‖)) * ‖v‖`.
              have :
                  (ε / (2 * ‖v‖)) * ‖v‖ = ε / 2 := by
                calc
                  (ε / (2 * ‖v‖)) * ‖v‖ = ε * ‖v‖ / (2 * ‖v‖) := by
                    simpa [div_mul_eq_mul_div]
                  _ = ε / 2 := by
                    simpa [mul_assoc, mul_left_comm, mul_comm] using
                      (mul_div_mul_right ε (2 : ℝ) hvne)
              simpa [t] using this
            _ < ε := by linarith [hε]
        have hz1ball : x + t • v ∈ Metric.ball x ε := by
          have : dist (x + t • v) x < ε := by
            simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hnorm_lt
          simpa [Metric.mem_ball] using this
        have hz1 : x + t • v ∈ C := hball hz1ball
        -- Likewise, `x - t v` is also in the interior ball.
        have hnorm_eq_neg : ‖(-t) • v‖ = ‖t • v‖ := by
          simpa [neg_smul] using (norm_neg (t • v))
        have hnorm_lt_neg : ‖(-t) • v‖ < ε := by
          exact lt_of_eq_of_lt hnorm_eq_neg hnorm_lt
        have hz2ball : x - t • v ∈ Metric.ball x ε := by
          have : dist (x - t • v) x < ε := by
            -- Rewrite `x - t v` as `x + (-t) v` so the distance computation matches the
            -- previous one.
            simpa [sub_eq_add_neg, dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
              using hnorm_lt_neg
          simpa [Metric.mem_ball] using this
        have hz2 : x - t • v ∈ C := hball hz2ball
        -- Apply the supporting inequality at the two symmetric points.
        have h1' : xStar ((x + t • v) - x) ≤ 0 := hxStarIneq (x + t • v) hz1
        have h2' : xStar ((x - t • v) - x) ≤ 0 := hxStarIneq (x - t • v) hz2
        have h1 : t * xStar v ≤ 0 := by
          have : t • xStar v ≤ 0 := by
            -- Simplify `(x + t v) - x = t v` and then use linearity of `xStar`.
            have h1'' : xStar (t • v) ≤ 0 := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h1'
            have hxStar_smul : xStar (t • v) = t • xStar v := xStar.map_smul t v
            simpa [hxStar_smul] using h1''
          simpa [smul_eq_mul] using this
        have h2 : (-t) * xStar v ≤ 0 := by
          have : (-t) • xStar v ≤ 0 := by
            -- Simplify `(x - t v) - x = (-t) v` and then use linearity of `xStar`.
            have h2'' : xStar ((-t) • v) ≤ 0 := by
              simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using h2'
            have hxStar_smul : xStar ((-t) • v) = (-t) • xStar v := xStar.map_smul (-t) v
            simpa [hxStar_smul] using h2''
          simpa [smul_eq_mul] using this
        -- Convert the second inequality into `0 ≤ t * xStar v`, then squeeze to get equality.
        have hge : 0 ≤ t * xStar v := by
          have : -(t * xStar v) ≤ 0 := by
            simpa [neg_mul] using h2
          exact (neg_nonpos).1 this
        have hmul : t * xStar v = 0 := le_antisymm h1 hge
        have htne : t ≠ 0 := ne_of_gt htpos
        have hv0 : xStar v = 0 := by
          rcases mul_eq_zero.mp hmul with ht0 | hv0
          · exact (False.elim (htne ht0))
          · exact hv0
        simpa using hv0
    -- Membership in the singleton `{0}` is just `xStar = 0`.
    simpa [Set.mem_singleton_iff, hxStar0]
  · intro hxStar
    -- Conversely, `0` always satisfies the normal-cone inequalities at points of `C`.
    have hxC : x ∈ C := interior_subset hx
    have hxStar0 : xStar = 0 := by simpa [Set.mem_singleton_iff] using hxStar
    subst hxStar0
    refine (mem_normalConeAt_iff).2 ?_
    refine And.intro hxC ?_
    intro z hz
    simp

/-- Helper for Proposition 6.28.2: a “repaired” version of the proposition which adds the
feasibility and strict-feasibility hypotheses needed for the outside and boundary formulas. -/
theorem helperForProposition_6_28_2_repaired
    {n : ℕ} (constraint : (Fin n → ℝ) → ℝ) (hconstraint : ConvexOn ℝ Set.univ constraint)
    (hne : ∃ y : Fin n → ℝ, constraint y ≤ 0) (x : Fin n → ℝ) :
    subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
        normalConeAt {y : Fin n → ℝ | constraint y ≤ 0} x ∧
      (constraint x = 0 → (∃ z : Fin n → ℝ, constraint z < 0) →
        subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
          Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
            a.1 • subdifferentialAt
              (fun y : Fin n → ℝ => ((constraint y : ℝ) : EReal)) x) ∧
      (constraint x < 0 →
        subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
          ({0} : Set (Module.Dual ℝ (Fin n → ℝ)))) ∧
      (0 < constraint x →
        subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x = ∅) := by
  classical
  -- Assemble the conclusion using the previously proved feasibility and strict-feasibility lemmas.
  constructor
  · -- Main equality: indicator subdifferential equals the normal cone under feasibility.
    exact
      helperForProposition_6_28_2_subdifferential_indicator_sublevelSet_eq_normalCone_of_exists_feasible
        (constraint := constraint) hne x
  constructor
  · intro hx0 hstrict
    -- Boundary case: rewrite `∂ δ_C(x)` as the normal cone, then apply the strict-feasibility
    -- normal-cone formula.
    have hSubEqNormal :
        subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
          normalConeAt {y : Fin n → ℝ | constraint y ≤ 0} x :=
      helperForProposition_6_28_2_subdifferential_indicator_sublevelSet_eq_normalCone_of_exists_feasible
        (constraint := constraint) hne x
    have hNormalEqCone :
        normalConeAt {y : Fin n → ℝ | constraint y ≤ 0} x =
          Set.iUnion fun a : {t : ℝ // 0 ≤ t} =>
            a.1 •
              subdifferentialAt (fun y : Fin n → ℝ => ((constraint y : ℝ) : EReal)) x :=
      helperForProposition_6_28_2_normalConeAt_sublevelSet_eq_iUnion_nonneg_smul_subdifferential_of_exists_strict
        (constraint := constraint) (hconstraint := hconstraint) x hx0 hstrict
    exact hSubEqNormal.trans hNormalEqCone
  constructor
  · intro hxlt
    -- Interior case: strict inequality puts `x` in the interior of `C`, so the normal cone is `{0}`.
    have hxint :
        x ∈ interior {y : Fin n → ℝ | constraint y ≤ 0} :=
      helperForProposition_6_28_2_mem_interior_sublevelSet_of_lt_zero
        (constraint := constraint) (hconstraint := hconstraint) hxlt
    have hNormalZero :
        normalConeAt {y : Fin n → ℝ | constraint y ≤ 0} x =
          ({0} : Set (Module.Dual ℝ (Fin n → ℝ))) :=
      helperForProposition_6_28_2_normalConeAt_eq_singleton_zero_of_mem_interior
        (C := {y : Fin n → ℝ | constraint y ≤ 0}) (x := x) hxint
    have hSubEqNormal :
        subdifferentialAt (indicatorFunction {y : Fin n → ℝ | constraint y ≤ 0}) x =
          normalConeAt {y : Fin n → ℝ | constraint y ≤ 0} x :=
      helperForProposition_6_28_2_subdifferential_indicator_sublevelSet_eq_normalCone_of_exists_feasible
        (constraint := constraint) hne x
    exact hSubEqNormal.trans hNormalZero
  · intro hxpos
    -- Outside case: with feasibility, Chapter 23 gives an empty subdifferential outside `C`.
    exact
      helperForProposition_6_28_2_subdifferential_indicator_sublevelSet_eq_empty_of_exists_feasible_of_pos
        (constraint := constraint) hne (x := x) hxpos

end Section28
end Chap06
