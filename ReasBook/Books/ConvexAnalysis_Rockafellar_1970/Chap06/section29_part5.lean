/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section06_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section09_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section10_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part4

section Chap06
section Section29

local notation "ConvexBifunction" => BundledConvexBifunction

/-- Definition 6.29.21: The generalized convex program `(P)` associated with a convex
bifunction `F` is strongly consistent when the zero perturbation belongs to the relative
interior of `dom F`. -/
def generalizedConvexProgramStronglyConsistent {m n : ℕ} (F : ConvexBifunction m n) : Prop :=
  (0 : Fin m → ℝ) ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1)

/-- Definition 6.29.22: The generalized convex program `(P)` associated with a convex
bifunction `F` is strictly consistent when the zero perturbation belongs to the interior
of `dom F`. -/
def generalizedConvexProgramStrictlyConsistent {m n : ℕ} (F : ConvexBifunction m n) : Prop :=
  (0 : Fin m → ℝ) ∈ interior (bifunctionEffectiveDomain F.1)

-- Proof sketch: this is the convexity half of Lemma 6.29.1 packaged as a standalone
-- statement so the associated ordinary program can be viewed as a generalized convex
-- program in the sense of Definition 6.29.21.
/-- The bifunction associated with an ordinary convex program is convex. -/
theorem ordinaryConvexProgramAssociatedBifunction_isConvex {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) :
    IsConvexBifunction (ordinaryConvexProgramAssociatedBifunction P) := by
  -- The convexity component is exactly the first half of Lemma 6.29.1.
  exact (ordinaryConvexProgramAssociatedBifunction_graphFunction_convex P).1

/-- The convex bifunction canonically associated with an ordinary convex program. -/
noncomputable def ordinaryConvexProgramAssociatedConvexBifunction {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) : ConvexBifunction m n :=
  ⟨ordinaryConvexProgramAssociatedBifunction P,
    ordinaryConvexProgramAssociatedBifunction_isConvex P⟩

/-- An ordinary convex program is strongly consistent when its associated generalized convex
program is strongly consistent. -/
def ordinaryConvexProgramStronglyConsistent {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) : Prop :=
  generalizedConvexProgramStronglyConsistent
    (ordinaryConvexProgramAssociatedConvexBifunction P)

/-- An ordinary convex program is strictly consistent when its associated generalized convex
program is strictly consistent. -/
def ordinaryConvexProgramStrictlyConsistent {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) : Prop :=
  generalizedConvexProgramStrictlyConsistent
    (ordinaryConvexProgramAssociatedConvexBifunction P)

-- Proof sketch: unfold strong consistency via Definition 6.29.21 and rewrite `dom F` for the
-- associated bifunction using Lemma 6.29.2. Then identify `0 ∈ ri (dom F)` with the existence
-- of a point in `ri C`, where `C = dom f₀`, satisfying strict negativity on the inequality
-- constraints and equality on the equality constraints.
/-- Helper for Lemma 6.29.9: the explicit perturbation domain obtained by rewriting the effective
domain of the associated bifunction via Lemma 6.29.2. -/
def helperForLemma_6_29_9_rewrittenPerturbationDomain {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) : Set (Fin m → ℝ) :=
  {u : Fin m → ℝ | ∃ x : Fin n → ℝ,
      x ∈ ordinaryConvexProgramObjectiveDomain P ∧
        ∀ i : Fin m,
          if (i : ℕ) < P.inequalityCount then
            P.constraint i x ≤ u i
          else
            P.constraint i x = u i}

/-- Helper for Lemma 6.29.9: strong consistency is exactly origin-membership in the relative
interior of the explicit perturbation domain. -/
lemma helperForLemma_6_29_9_strongConsistency_iff_zero_mem_rewrittenPerturbationDomain
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    ordinaryConvexProgramStronglyConsistent P ↔
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (helperForLemma_6_29_9_rewrittenPerturbationDomain P) := by
  -- Unfold strong consistency until only the effective-domain description remains.
  unfold ordinaryConvexProgramStronglyConsistent generalizedConvexProgramStronglyConsistent
  simp [ordinaryConvexProgramAssociatedConvexBifunction]
  -- Rewrite `dom F` using Lemma 6.29.2 and unpack the intersection witness.
  rw [ordinaryConvexProgramAssociatedBifunction_dom_eq_nonempty_inter_dom_objective]
  have hset :
      {u : Fin m → ℝ |
          Set.Nonempty
            (ordinaryConvexProgramConstraintSet P u ∩ ordinaryConvexProgramObjectiveDomain P)} =
        helperForLemma_6_29_9_rewrittenPerturbationDomain P := by
    ext u
    change
      Set.Nonempty
          (ordinaryConvexProgramConstraintSet P u ∩ ordinaryConvexProgramObjectiveDomain P) ↔
        ∃ x : Fin n → ℝ,
          x ∈ ordinaryConvexProgramObjectiveDomain P ∧
            ∀ i : Fin m,
              if (i : ℕ) < P.inequalityCount then
                P.constraint i x ≤ u i
              else
                P.constraint i x = u i
    constructor
    · rintro ⟨x, hx⟩
      -- A point in the intersection yields exactly the rewritten perturbation witness.
      refine ⟨x, hx.2, ?_⟩
      simpa [ordinaryConvexProgramConstraintSet] using hx.1
    · rintro ⟨x, hxObjective, hxConstraint⟩
      -- Conversely, the rewritten witness certifies nonempty intersection with `dom f₀`.
      refine ⟨x, ?_⟩
      constructor
      · simpa [ordinaryConvexProgramConstraintSet] using hxConstraint
      · exact hxObjective
  simp [hset]

/-- Helper for Lemma 6.29.9: the convex set of feasible `(u, x)` pairs lying over the rewritten
perturbation domain. -/
def helperForLemma_6_29_9_feasiblePairSet {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {ux | ux.2 ∈ ordinaryConvexProgramObjectiveDomain P ∧
      ux.2 ∈ ordinaryConvexProgramConstraintSet P ux.1}

/-- Helper for Lemma 6.29.9: a perturbation belongs to the rewritten perturbation domain exactly
when it appears as the `u`-component of a feasible pair. -/
lemma helperForLemma_6_29_9_mem_rewrittenPerturbationDomain_iff_exists_feasiblePair
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) {u : Fin m → ℝ} :
    u ∈ helperForLemma_6_29_9_rewrittenPerturbationDomain P ↔
      ∃ x : Fin n → ℝ, (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P := by
  -- Unfold both sets and note that they package the same witness data in different formats.
  constructor
  · rintro ⟨x, hxObjective, hxConstraint⟩
    refine ⟨x, ?_⟩
    constructor
    · exact hxObjective
    · simpa [ordinaryConvexProgramConstraintSet] using hxConstraint
  · rintro ⟨x, hx⟩
    refine ⟨x, hx.1, ?_⟩
    simpa [helperForLemma_6_29_9_feasiblePairSet, ordinaryConvexProgramConstraintSet] using hx.2

/-- Helper for Lemma 6.29.9: every point of the objective domain occurs as the `x`-component of
a feasible pair, using its own constraint values as the perturbation vector. -/
lemma helperForLemma_6_29_9_mem_objectiveDomain_iff_exists_feasiblePerturbation
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) {x : Fin n → ℝ} :
    x ∈ ordinaryConvexProgramObjectiveDomain P ↔
      ∃ u : Fin m → ℝ, (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P := by
  constructor
  · intro hx
    -- Use the actual constraint values of `x` as a canonical perturbation witness.
    refine ⟨fun i => P.constraint i x, ?_⟩
    constructor
    · exact hx
    · exact helperForLemma_6_29_3_constraintVector_mem_constraintSet_self P
  · rintro ⟨u, hu⟩
    -- Any feasible pair already records that `x` lies in the objective domain.
    exact hu.1

/-- Helper for Lemma 6.29.9: the origin fiber of the feasible-pair set is the weak-feasibility
section `S₀ ∩ C`. -/
lemma helperForLemma_6_29_9_zeroPerturbation_mem_feasiblePairSet_iff_weakWitness
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) {x : Fin n → ℝ} :
    ((0 : Fin m → ℝ), x) ∈ helperForLemma_6_29_9_feasiblePairSet P ↔
      x ∈ ordinaryConvexProgramObjectiveDomain P ∧
        ∀ i : Fin m,
          if (i : ℕ) < P.inequalityCount then
            P.constraint i x ≤ 0
          else
            P.constraint i x = 0 := by
  -- Evaluating the fiber at `u = 0` turns each right-hand side into the scalar `0`.
  simp [helperForLemma_6_29_9_feasiblePairSet, ordinaryConvexProgramConstraintSet]

/-- Helper for Lemma 6.29.9: the feasible-pair set is convex, so Chapter 2 section/projection
formulas can be applied to it. -/
lemma helperForLemma_6_29_9_feasiblePairSet_convex
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    Convex ℝ (helperForLemma_6_29_9_feasiblePairSet P) := by
  have hObjectiveConvex : Convex ℝ (ordinaryConvexProgramObjectiveDomain P) := by
    -- The objective domain is the effective domain of a convex function.
    simpa [ordinaryConvexProgramObjectiveDomain, erealDom, effectiveDomain_eq] using
      (effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) P.objective_convex)
  intro p hp q hq a b ha hb hab
  refine ⟨?_, ?_⟩
  · -- The objective-domain coordinate is preserved by convexity of `dom f₀`.
    exact hObjectiveConvex hp.1 hq.1 ha hb hab
  · -- Feasibility of the graph constraints is preserved under convex combinations.
    simpa [helperForLemma_6_29_9_feasiblePairSet] using
      (helperForLemma_6_29_1_mem_constraintSet_of_convexCombo P hp.2 hq.2 ha hb hab)

/-- Helper for Lemma 6.29.9: for fixed `x`, the perturbation fiber is exactly the coordinatewise
mixed inequality/equality set determined by the constraint values at `x`. -/
lemma helperForLemma_6_29_9_fixedFiber_eq_coordinateConditions
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) (x : Fin n → ℝ) :
    {u : Fin m → ℝ | (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P} =
      {u : Fin m → ℝ |
        x ∈ ordinaryConvexProgramObjectiveDomain P ∧
          ∀ i : Fin m,
            if (i : ℕ) < P.inequalityCount then
              P.constraint i x ≤ u i
            else
              P.constraint i x = u i} := by
  -- Unfolding the feasible-pair set at fixed `x` leaves exactly the textbook coordinate conditions.
  ext u
  simp [helperForLemma_6_29_9_feasiblePairSet, ordinaryConvexProgramConstraintSet]

/-- Helper for Lemma 6.29.9: the mixed core with nonnegative inequality coordinates and zero
equality coordinates. -/
def helperForLemma_6_29_9_mixedCoordinateCore {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) : Set (Fin m → ℝ) :=
  {v : Fin m → ℝ |
    ∀ i : Fin m,
      if (i : ℕ) < P.inequalityCount then
        0 ≤ v i
      else
        v i = 0}

/-- Helper for Lemma 6.29.9: after fixing `x`, the coordinate-condition fiber is either empty
outside `dom f₀` or a translation of the mixed coordinate core by the constraint vector at `x`. -/
lemma helperForLemma_6_29_9_coordinateConditionFiber_eq_guardedTranslateOfMixedCore
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) (x : Fin n → ℝ) :
    {u : Fin m → ℝ |
      x ∈ ordinaryConvexProgramObjectiveDomain P ∧
        ∀ i : Fin m,
          if (i : ℕ) < P.inequalityCount then
            P.constraint i x ≤ u i
          else
            P.constraint i x = u i} =
      {u : Fin m → ℝ |
        x ∈ ordinaryConvexProgramObjectiveDomain P ∧
          u ∈ Set.image
            (fun v : Fin m → ℝ => v + fun i => P.constraint i x)
            (helperForLemma_6_29_9_mixedCoordinateCore P)} := by
  -- Replace the guarded fiber by a translated mixed core together with the explicit domain guard.
  ext u
  constructor
  · rintro ⟨hx, hu⟩
    refine ⟨hx, ?_⟩
    refine ⟨fun i => u i - P.constraint i x, ?_, ?_⟩
    · intro i
      by_cases hi : (i : ℕ) < P.inequalityCount
      · have hle : P.constraint i x ≤ u i := by simpa [hi] using hu i
        simp [hi, sub_nonneg.mpr hle]
      · have heq : P.constraint i x = u i := by simpa [hi] using hu i
        have hu0 : u i - P.constraint i x = 0 := by linarith
        simp [hi, hu0]
    · funext i
      simp
  · rintro ⟨hx, hvImage⟩
    rcases hvImage with ⟨v, hv, rfl⟩
    refine ⟨hx, ?_⟩
    intro i
    by_cases hi : (i : ℕ) < P.inequalityCount
    · have hnonneg : 0 ≤ v i := by
        simpa [helperForLemma_6_29_9_mixedCoordinateCore, hi] using hv i
      have hle : P.constraint i x ≤ v i + P.constraint i x := by
        linarith
      simpa [hi] using hle
    · have hv0 : v i = 0 := by
        simpa [helperForLemma_6_29_9_mixedCoordinateCore, hi] using hv i
      simp [hi, hv0]

/-- Helper for Lemma 6.29.9: the feasible pairs written in `(x, u)` order and transported to
Euclidean product coordinates. -/
def helperForLemma_6_29_9_feasiblePairSet_xuEuclideanProduct {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) :
    Set ((EuclideanSpace Real (Fin n)) × (EuclideanSpace Real (Fin m))) :=
  {xu : (EuclideanSpace Real (Fin n)) × (EuclideanSpace Real (Fin m)) |
    (((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) xu.2),
      ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) xu.1))
      ∈ helperForLemma_6_29_9_feasiblePairSet P}

/-- Helper for Lemma 6.29.9: the same `(x, u)` feasible-pair set embedded into `ℝ^(n+m)` via
the standard append affine equivalence. -/
def helperForLemma_6_29_9_feasiblePairSet_xuEuclidean {m n : ℕ}
    (P : IndexedOrdinaryConvexProgram m n) :
    Set (EuclideanSpace Real (Fin (n + m))) :=
  (appendAffineEquiv n m) '' helperForLemma_6_29_9_feasiblePairSet_xuEuclideanProduct P

/-- Helper for Lemma 6.29.9: the transported `(x, u)` feasible-pair set remains convex in product
Euclidean coordinates. -/
lemma helperForLemma_6_29_9_feasiblePairSet_xuEuclideanProduct_convex
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    Convex ℝ (helperForLemma_6_29_9_feasiblePairSet_xuEuclideanProduct P) := by
  have hPairConv :
      Convex ℝ (helperForLemma_6_29_9_feasiblePairSet P) :=
    helperForLemma_6_29_9_feasiblePairSet_convex P
  intro xu hxu yu hyu a b ha hb hab
  -- Apply convexity in the original `(u, x)` coordinates, then transport back through the
  -- Euclidean coordinate equivalences.
  have hxu' :
      (((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) xu.2),
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) xu.1))
        ∈ helperForLemma_6_29_9_feasiblePairSet P := hxu
  have hyu' :
      (((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) yu.2),
        ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) yu.1))
        ∈ helperForLemma_6_29_9_feasiblePairSet P := hyu
  have hcombo :
      a •
          (((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) xu.2),
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) xu.1)) +
        b •
          (((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)) yu.2),
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)) yu.1))
        ∈ helperForLemma_6_29_9_feasiblePairSet P :=
    hPairConv hxu' hyu' ha hb hab
  simpa [helperForLemma_6_29_9_feasiblePairSet_xuEuclideanProduct,
    smul_add, add_comm, add_left_comm, add_assoc] using hcombo

/-- Helper for Lemma 6.29.9: appending the Euclidean `(x, u)` coordinates into `ℝ^(n+m)` preserves
convexity of the feasible-pair set. -/
lemma helperForLemma_6_29_9_feasiblePairSet_xuEuclidean_convex
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    Convex ℝ (helperForLemma_6_29_9_feasiblePairSet_xuEuclidean P) := by
  -- The append map is an affine equivalence, so convexity transports directly.
  simpa [helperForLemma_6_29_9_feasiblePairSet_xuEuclidean] using
    (Convex.affine_image
      (f := (appendAffineEquiv n m).toAffineMap)
      (helperForLemma_6_29_9_feasiblePairSet_xuEuclideanProduct_convex P))

/-- Helper for Lemma 6.29.9: translating a fin-dimensional set by `a` carries its relative
interior along with it, so the origin lies in the translated relative interior exactly when
`-a` lies in the original one. -/
lemma helperForLemma_6_29_9_zero_mem_ri_translate_iff_neg_mem_ri
    {m : ℕ} (a : Fin m → ℝ) (C : Set (Fin m → ℝ)) :
    (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m (Set.image (fun v : Fin m → ℝ => v + a) C) ↔
      (-a) ∈ euclideanRelativeInterior_fin m C := by
  let e : EuclideanSpace Real (Fin m) ≃L[Real] (Fin m → ℝ) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)
  let CE : Set (EuclideanSpace Real (Fin m)) :=
    e.symm '' C
  let T : EuclideanSpace Real (Fin m) ≃ᵃ[Real] EuclideanSpace Real (Fin m) :=
    AffineEquiv.ofLinearEquiv (LinearEquiv.refl ℝ (EuclideanSpace Real (Fin m))) 0 (e.symm a)
  have hT_apply : ∀ z : EuclideanSpace Real (Fin m), T z = z + e.symm a := by
    intro z
    simp [T, AffineEquiv.ofLinearEquiv_apply]
  have hT_zero : T (e.symm (-a)) = 0 := by
    simp [T, e]
  have hT_image :
      e.symm '' Set.image (fun v : Fin m → ℝ => v + a) C = T '' CE := by
    ext z
    constructor
    · rintro ⟨w, hw, hz⟩
      rcases hw with ⟨v, hv, rfl⟩
      refine ⟨e.symm v, ?_, ?_⟩
      · exact ⟨v, hv, rfl⟩
      · simpa [hT_apply] using hz
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨v, hv, rfl⟩
      refine ⟨v + a, ⟨v, hv, rfl⟩, ?_⟩
      apply e.injective
      simp [hT_apply]
  constructor
  · intro hzero
    have hzeroE :
        (0 : EuclideanSpace Real (Fin m)) ∈ euclideanRelativeInterior m (T '' CE) := by
      have hzero' :
          e.symm (0 : Fin m → ℝ) ∈
            euclideanRelativeInterior m (e.symm '' Set.image (fun v : Fin m → ℝ => v + a) C) :=
        (mem_euclideanRelativeInterior_fin_iff
          (n := m) (C := Set.image (fun v : Fin m → ℝ => v + a) C) (x := 0)).1 hzero
      simpa [hT_image] using hzero'
    have hzeroImage :
        (0 : EuclideanSpace Real (Fin m)) ∈ T '' euclideanRelativeInterior m CE := by
      simpa [euclideanRelativeInterior_image_affineEquiv (n := m) (C := CE) (e := T)] using hzeroE
    rcases hzeroImage with ⟨y, hy, hy0⟩
    have hyEq : y = e.symm (-a) := by
      apply T.injective
      rw [hy0, hT_zero]
    refine (mem_euclideanRelativeInterior_fin_iff (n := m) (C := C) (x := -a)).2 ?_
    simpa [CE, hyEq]
      using hy
  · intro hneg
    have hnegE :
        e.symm (-a) ∈ euclideanRelativeInterior m CE := by
      simpa [CE] using
        (mem_euclideanRelativeInterior_fin_iff (n := m) (C := C) (x := -a)).1 hneg
    have hzeroImage :
        (0 : EuclideanSpace Real (Fin m)) ∈ T '' euclideanRelativeInterior m CE := by
      refine ⟨e.symm (-a), hnegE, ?_⟩
      simpa [hT_zero]
    have hzeroE :
        (0 : EuclideanSpace Real (Fin m)) ∈ euclideanRelativeInterior m (T '' CE) := by
      simpa [euclideanRelativeInterior_image_affineEquiv (n := m) (C := CE) (e := T)] using
        hzeroImage
    have hzeroE' :
        (0 : EuclideanSpace Real (Fin m)) ∈
          euclideanRelativeInterior m (e.symm '' Set.image (fun v : Fin m → ℝ => v + a) C) := by
      simpa [hT_image] using hzeroE
    refine (mem_euclideanRelativeInterior_fin_iff
      (n := m) (C := Set.image (fun v : Fin m → ℝ => v + a) C) (x := 0)).2 ?_
    exact hzeroE'

/-- Helper for Lemma 6.29.9: origin-membership in the `u`-projection relative interior is the
remaining projection/section bridge needed to turn the feasible-pair geometry into a fixed-fiber
relative-interior witness. -/
lemma helperForLemma_6_29_9_zero_mem_ri_projectionOfFeasiblePairSet_iff_exists_riFiberWitness
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          {u : Fin m → ℝ | ∃ x : Fin n → ℝ, (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P} ↔
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n (ordinaryConvexProgramObjectiveDomain P) ∧
          (0 : Fin m → ℝ) ∈
            euclideanRelativeInterior_fin m
              {u : Fin m → ℝ | (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P} := by
  classical
  let C : Set (EuclideanSpace Real (Fin (n + m))) :=
    helperForLemma_6_29_9_feasiblePairSet_xuEuclidean P
  let eN : EuclideanSpace Real (Fin n) ≃L[Real] (Fin n → ℝ) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)
  let eM : EuclideanSpace Real (Fin m) ≃L[Real] (Fin m → ℝ) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)
  let A : EuclideanSpace Real (Fin (n + m)) →ₗ[Real] EuclideanSpace Real (Fin m) :=
    (LinearMap.snd (R := Real) (M := EuclideanSpace Real (Fin n))
      (M₂ := EuclideanSpace Real (Fin m))).comp (appendAffineEquiv n m).symm.linear.toLinearMap
  let Cy : EuclideanSpace Real (Fin n) → Set (EuclideanSpace Real (Fin m)) :=
    fun xE => {uE | appendAffineEquiv n m (xE, uE) ∈ C}
  let D : Set (EuclideanSpace Real (Fin n)) := {xE | (Cy xE).Nonempty}
  have hconvC : Convex ℝ C := by
    simpa [C] using helperForLemma_6_29_9_feasiblePairSet_xuEuclidean_convex P
  have hA_append :
      ∀ xE : EuclideanSpace Real (Fin n), ∀ uE : EuclideanSpace Real (Fin m),
        A (appendAffineEquiv n m (xE, uE)) = uE := by
    intro xE uE
    have happ :
        appendAffineEquiv n m (xE, uE) = (appendAffineEquiv n m).linear (xE, uE) := by
      simpa using
        congrArg (fun f => f (xE, uE)) (appendAffineEquiv_eq_linear_toAffineEquiv n m)
    have hback :
        (appendAffineEquiv n m).symm.linear (appendAffineEquiv n m (xE, uE)) = (xE, uE) := by
      rw [happ]
      simp
    simpa [A] using congrArg Prod.snd hback
  have hCyEq :
      ∀ xE : EuclideanSpace Real (Fin n),
        Cy xE =
          eM.symm '' {u : Fin m → ℝ | (u, eN xE) ∈ helperForLemma_6_29_9_feasiblePairSet P} := by
    intro xE
    ext uE
    constructor
    · intro huE
      change appendAffineEquiv n m (xE, uE) ∈ C at huE
      rw [show C = helperForLemma_6_29_9_feasiblePairSet_xuEuclidean P by rfl] at huE
      rw [helperForLemma_6_29_9_feasiblePairSet_xuEuclidean] at huE
      rcases huE with ⟨⟨xE', uE'⟩, hxu, hEq⟩
      have hpair : (xE', uE') = (xE, uE) := (appendAffineEquiv n m).injective hEq
      have hx : xE' = xE := by simpa using congrArg Prod.fst hpair
      have hu : uE' = uE := by simpa using congrArg Prod.snd hpair
      subst xE'
      subst uE'
      refine ⟨eM uE, ?_, by simp [eM]⟩
      simpa [helperForLemma_6_29_9_feasiblePairSet_xuEuclideanProduct, eN, eM] using hxu
    · rintro ⟨u, hu, rfl⟩
      change appendAffineEquiv n m (xE, eM.symm u) ∈ C
      rw [show C = helperForLemma_6_29_9_feasiblePairSet_xuEuclidean P by rfl]
      rw [helperForLemma_6_29_9_feasiblePairSet_xuEuclidean]
      refine ⟨(xE, eM.symm u), ?_, rfl⟩
      simpa [helperForLemma_6_29_9_feasiblePairSet_xuEuclideanProduct, eN, eM] using hu
  have hDEq :
      D = eN.symm '' ordinaryConvexProgramObjectiveDomain P := by
    ext xE
    constructor
    · rintro ⟨uE, huE⟩
      have huE' :
          uE ∈ eM.symm '' {u : Fin m → ℝ | (u, eN xE) ∈ helperForLemma_6_29_9_feasiblePairSet P} := by
        simpa [hCyEq xE] using huE
      rcases huE' with ⟨u, hu, rfl⟩
      refine ⟨eN xE, ?_, by simp [eN]⟩
      exact
        (helperForLemma_6_29_9_mem_objectiveDomain_iff_exists_feasiblePerturbation
          P (x := eN xE)).2 ⟨u, hu⟩
    · rintro ⟨x, hx, rfl⟩
      rcases
          (helperForLemma_6_29_9_mem_objectiveDomain_iff_exists_feasiblePerturbation
            P (x := x)).1 hx with
        ⟨u, hu⟩
      refine ⟨eM.symm u, ?_⟩
      simpa [hCyEq, eM]
  have hprojEq :
      eM.symm ''
          {u : Fin m → ℝ | ∃ x : Fin n → ℝ, (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P} =
        A '' C := by
    ext vE
    constructor
    · rintro ⟨u, hu, rfl⟩
      rcases hu with ⟨x, hx⟩
      refine ⟨appendAffineEquiv n m (eN.symm x, eM.symm u), ?_, ?_⟩
      · rw [show C = helperForLemma_6_29_9_feasiblePairSet_xuEuclidean P by rfl]
        rw [helperForLemma_6_29_9_feasiblePairSet_xuEuclidean]
        refine ⟨(eN.symm x, eM.symm u), ?_, rfl⟩
        simpa [helperForLemma_6_29_9_feasiblePairSet_xuEuclideanProduct, eN, eM] using hx
      · simpa [hA_append, eM]
    · rintro ⟨w, hw, hwA⟩
      rw [show C = helperForLemma_6_29_9_feasiblePairSet_xuEuclidean P by rfl] at hw
      rw [helperForLemma_6_29_9_feasiblePairSet_xuEuclidean] at hw
      rcases hw with ⟨⟨xE, uE⟩, hxu, rfl⟩
      have hu : uE = vE := by
        rwa [hA_append xE uE] at hwA
      refine ⟨eM uE, ?_, by simpa [hu, eM]⟩
      refine ⟨eN xE, ?_⟩
      simpa [helperForLemma_6_29_9_feasiblePairSet_xuEuclideanProduct, eN, eM] using hxu
  have hprojEq' :
      ((fun u : Fin m → ℝ => eM.symm u) ''
          {u : Fin m → ℝ | ∃ x : Fin n → ℝ,
            (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P}) =
        A '' C := by
    simpa using hprojEq
  have hsection :
      ∀ xE : EuclideanSpace Real (Fin n),
        appendAffineEquiv n m (xE, (0 : EuclideanSpace Real (Fin m))) ∈
            euclideanRelativeInterior (n + m) C ↔
          xE ∈ euclideanRelativeInterior n D ∧
            (0 : EuclideanSpace Real (Fin m)) ∈ euclideanRelativeInterior m (Cy xE) := by
    intro xE
    simpa [C, Cy, D, appendAffineEquiv_apply] using
      (euclideanRelativeInterior_mem_iff_relativeInterior_section
        (m := n) (p := m) (C := C) hconvC xE (0 : EuclideanSpace Real (Fin m)))
  have hriImage :
      euclideanRelativeInterior m (A '' C) = A '' euclideanRelativeInterior (n + m) C := by
    exact
      (euclideanRelativeInterior_image_linearMap_eq_and_image_closure_subset
        (n := n + m) (m := m) (C := C) hconvC A).1
  constructor
  · intro hzero
    -- Convert origin-membership in the `u`-projection into a point of `ri C` with zero `u`-part.
    have hzeroE :
        (0 : EuclideanSpace Real (Fin m)) ∈ euclideanRelativeInterior m (A '' C) := by
      have hzero' :
          eM.symm (0 : Fin m → ℝ) ∈
            euclideanRelativeInterior m
              (eM.symm ''
                {u : Fin m → ℝ | ∃ x : Fin n → ℝ,
                  (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P}) :=
        (mem_euclideanRelativeInterior_fin_iff
          (n := m)
          (C := {u : Fin m → ℝ | ∃ x : Fin n → ℝ,
            (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P})
          (x := 0)).1 hzero
      rw [hprojEq'] at hzero'
      simpa [eM] using hzero'
    have hzeroImage :
        (0 : EuclideanSpace Real (Fin m)) ∈ A '' euclideanRelativeInterior (n + m) C := by
      simpa [hriImage] using hzeroE
    rcases hzeroImage with ⟨w, hwri, hw0⟩
    rcases (appendAffineEquiv n m).surjective w with ⟨⟨xE, uE⟩, rfl⟩
    have hu0 : uE = 0 := by
      rwa [hA_append xE uE] at hw0
    subst hu0
    have hsplit :
        xE ∈ euclideanRelativeInterior n D ∧
          (0 : EuclideanSpace Real (Fin m)) ∈ euclideanRelativeInterior m (Cy xE) :=
      (hsection xE).1 hwri
    refine ⟨eN xE, ?_, ?_⟩
    · -- The base section of the feasible-pair set is exactly the objective domain.
      refine (mem_euclideanRelativeInterior_fin_iff
        (n := n) (C := ordinaryConvexProgramObjectiveDomain P) (x := eN xE)).2 ?_
      simpa [hDEq, eN] using hsplit.1
    · -- The vertical section at `x` is exactly the fixed-`x` perturbation fiber.
      refine (mem_euclideanRelativeInterior_fin_iff
        (n := m)
        (C := {u : Fin m → ℝ | (u, eN xE) ∈ helperForLemma_6_29_9_feasiblePairSet P})
        (x := 0)).2 ?_
      simpa [hCyEq xE, eM] using hsplit.2
  · rintro ⟨x, hxri, hfiber⟩
    let xE : EuclideanSpace Real (Fin n) := eN.symm x
    have hxEri : xE ∈ euclideanRelativeInterior n D := by
      have hxri' :
          eN.symm x ∈ euclideanRelativeInterior n (eN.symm '' ordinaryConvexProgramObjectiveDomain P) :=
        (mem_euclideanRelativeInterior_fin_iff
          (n := n) (C := ordinaryConvexProgramObjectiveDomain P) (x := x)).1 hxri
      simpa [xE, hDEq] using hxri'
    have hfiberE :
        (0 : EuclideanSpace Real (Fin m)) ∈ euclideanRelativeInterior m (Cy xE) := by
      have hfiber' :
          eM.symm (0 : Fin m → ℝ) ∈
            euclideanRelativeInterior m
              (eM.symm '' {u : Fin m → ℝ | (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P}) :=
        (mem_euclideanRelativeInterior_fin_iff
          (n := m)
          (C := {u : Fin m → ℝ | (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P})
          (x := 0)).1 hfiber
      simpa [xE, hCyEq xE, eM] using hfiber'
    have hwri :
        appendAffineEquiv n m (xE, (0 : EuclideanSpace Real (Fin m))) ∈
          euclideanRelativeInterior (n + m) C :=
      (hsection xE).2 ⟨hxEri, hfiberE⟩
    have hzeroImage :
        (0 : EuclideanSpace Real (Fin m)) ∈ A '' euclideanRelativeInterior (n + m) C := by
      refine ⟨appendAffineEquiv n m (xE, (0 : EuclideanSpace Real (Fin m))), hwri, ?_⟩
      simpa [hA_append]
    have hzeroE :
        (0 : EuclideanSpace Real (Fin m)) ∈ euclideanRelativeInterior m (A '' C) := by
      simpa [hriImage] using hzeroImage
    refine (mem_euclideanRelativeInterior_fin_iff
      (n := m)
      (C := {u : Fin m → ℝ | ∃ x : Fin n → ℝ,
        (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P})
      (x := 0)).2 ?_
    have hzeroE' := hzeroE
    rw [← hprojEq'] at hzeroE'
    simpa [eM] using hzeroE'

/-- Helper for Lemma 6.29.9: the relative interior of the mixed coordinate core is obtained by
making the inequality coordinates strictly positive while keeping the equality coordinates fixed
at zero. -/
lemma helperForLemma_6_29_9_euclideanRelativeInterior_mixedCoordinateCore
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    euclideanRelativeInterior_fin m (helperForLemma_6_29_9_mixedCoordinateCore P) =
      {v : Fin m → ℝ |
        ∀ i : Fin m,
          if (i : ℕ) < P.inequalityCount then
            0 < v i
          else
            v i = 0} := by
  classical
  let r := P.inequalityCount
  let hr : r ≤ m := P.inequalityCount_le
  let e : EuclideanSpace Real (Fin m) ≃L[Real] (Fin m → ℝ) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)
  let eHead : EuclideanSpace Real (Fin r) ≃L[Real] (Fin r → ℝ) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin r)
  let C : Set (EuclideanSpace Real (Fin m)) :=
    e.symm '' helperForLemma_6_29_9_mixedCoordinateCore P
  let Chead : Set (EuclideanSpace Real (Fin r)) :=
    {y : EuclideanSpace Real (Fin r) | ∀ i : Fin r, 0 ≤ (y : Fin r → ℝ) i}
  let A : EuclideanSpace Real (Fin m) →ₗ[Real] EuclideanSpace Real (Fin r) :=
    eHead.symm.toLinearMap.comp ((LinearMap.funLeft Real Real (Fin.castLE hr)).comp e.toLinearMap)
  let M : AffineSubspace Real (EuclideanSpace Real (Fin m)) :=
    (coordinateSubmodule m r).toAffineSubspace
  let z0 : EuclideanSpace Real (Fin m) := e.symm (fun i => if (i : ℕ) < r then 1 else 0)
  have hA_apply :
      ∀ z : EuclideanSpace Real (Fin m), ∀ i : Fin r,
        ((A z : EuclideanSpace Real (Fin r)) : Fin r → ℝ) i =
          (z : Fin m → ℝ) (Fin.castLE hr i) := by
    intro z i
    change
      (eHead.symm ((LinearMap.funLeft Real Real (Fin.castLE hr)) (e z))).ofLp i =
        e z (Fin.castLE hr i)
    rfl
  have hC_eq :
      C = (A ⁻¹' Chead) ∩ (M : Set (EuclideanSpace Real (Fin m))) := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨?_, ?_⟩
      · intro i
        have hvi := hv (Fin.castLE hr i)
        have hi : ((Fin.castLE hr i : Fin m) : ℕ) < r := by
          simpa using i.is_lt
        simpa [Chead, helperForLemma_6_29_9_mixedCoordinateCore, hA_apply, r, hi]
          using hvi
      · intro i hi
        have hvi := hv i
        have hnot : ¬ (i : ℕ) < r := not_lt_of_ge hi
        simpa [M, coordinateSubmodule, coordinateSubspace,
          helperForLemma_6_29_9_mixedCoordinateCore, r, hnot] using hvi
    · rintro ⟨hzHead, hzTail⟩
      refine ⟨e z, ?_, by simp [e]⟩
      intro i
      by_cases hi : (i : ℕ) < r
      · have hzHead' : 0 ≤ ((A z : EuclideanSpace Real (Fin r)) : Fin r → ℝ) ⟨i, hi⟩ :=
          hzHead ⟨i, hi⟩
        simpa [helperForLemma_6_29_9_mixedCoordinateCore, r, hi, hA_apply] using hzHead'
      · have hi' : r ≤ (i : ℕ) := le_of_not_gt hi
        have hzTail' : ((z : EuclideanSpace Real (Fin m)) : Fin m → ℝ) i = 0 := hzTail i hi'
        simpa [helperForLemma_6_29_9_mixedCoordinateCore, r, hi] using hzTail'
  have hconvChead : Convex ℝ Chead := by
    intro x hx y hy a b ha hb hab
    intro i
    have hx' : 0 ≤ (x : Fin r → ℝ) i := hx i
    have hy' : 0 ≤ (y : Fin r → ℝ) i := hy i
    have hnonneg : 0 ≤ a * (x : Fin r → ℝ) i + b * (y : Fin r → ℝ) i := by
      exact add_nonneg (mul_nonneg ha hx') (mul_nonneg hb hy')
    simpa [Pi.add_apply, Pi.smul_apply, mul_comm, mul_left_comm, mul_assoc] using hnonneg
  have hri_Chead :
      euclideanRelativeInterior r Chead =
        {y : EuclideanSpace Real (Fin r) | ∀ i : Fin r, 0 < (y : Fin r → ℝ) i} := by
    simpa [Chead] using (Section10.euclideanRelativeInterior_preimage_nonnegOrthant (n := r))
  have hz0_mem_head :
      z0 ∈ A ⁻¹' euclideanRelativeInterior r Chead := by
    -- The witness `z0` has strictly positive inequality coordinates, so it lies in the pulled-back
    -- relative interior of the nonnegative orthant.
    rw [hri_Chead]
    intro i
    rw [hA_apply]
    simp [z0, e, r, i.is_lt]
  have hri_preimage :
      euclideanRelativeInterior m (A ⁻¹' Chead) =
        {z : EuclideanSpace Real (Fin m) | ∀ i : Fin m, (i : ℕ) < r → 0 < (z : Fin m → ℝ) i} := by
    -- First compute the relative interior through the linear preimage theorem, then rewrite the
    -- projected head coordinates back in the original `Fin m` indexing.
    have hpre :=
      euclideanRelativeInterior_preimage_linearMap_eq_and_closure_preimage
        (n := m) (m := r) A Chead hconvChead ⟨z0, hz0_mem_head⟩
    calc
      euclideanRelativeInterior m (A ⁻¹' Chead) = A ⁻¹' euclideanRelativeInterior r Chead := hpre.1
      _ = {z : EuclideanSpace Real (Fin m) | ∀ i : Fin m, (i : ℕ) < r → 0 < (z : Fin m → ℝ) i} := by
          ext z
          constructor
          · intro hz i hi
            have hzA : A z ∈ euclideanRelativeInterior r Chead := hz
            rw [hri_Chead] at hzA
            have hz' : 0 < ((A z : EuclideanSpace Real (Fin r)) : Fin r → ℝ) ⟨i, hi⟩ := by
              exact hzA ⟨i, hi⟩
            simpa [hA_apply] using hz'
          · intro hz
            rw [hri_Chead]
            intro i
            have hz' : 0 < (z : Fin m → ℝ) (Fin.castLE hr i) :=
              hz (Fin.castLE hr i) (by simpa using i.is_lt)
            simpa [hA_apply] using hz'
  have hz0_mem_M : z0 ∈ (M : Set (EuclideanSpace Real (Fin m))) := by
    intro i hi
    have hnot : ¬ (i : ℕ) < r := not_lt_of_ge hi
    simp [M, z0, e, hnot]
  have hz0_mem_ri_preimage : z0 ∈ euclideanRelativeInterior m (A ⁻¹' Chead) := by
    rw [hri_preimage]
    intro i hi
    simp [z0, e, hi]
  have hM_nonempty :
      ((M : Set (EuclideanSpace Real (Fin m))) ∩
        euclideanRelativeInterior m (A ⁻¹' Chead)).Nonempty := by
    exact ⟨z0, hz0_mem_M, hz0_mem_ri_preimage⟩
  have hri_C :
      euclideanRelativeInterior m C =
        {z : EuclideanSpace Real (Fin m) |
          ∀ i : Fin m,
            if (i : ℕ) < r then
              0 < (z : Fin m → ℝ) i
            else
              (z : Fin m → ℝ) i = 0} := by
    -- Intersect the head-orthant relative interior with the coordinate subspace enforcing the
    -- equality coordinates to vanish.
    have hinter :=
      euclideanRelativeInterior_inter_affineSubspace_eq_and_closure_eq
        (n := m) (C := A ⁻¹' Chead) (hconvChead.linear_preimage A) M hM_nonempty
    calc
      euclideanRelativeInterior m C =
          euclideanRelativeInterior m ((M : Set (EuclideanSpace Real (Fin m))) ∩ (A ⁻¹' Chead)) := by
            rw [hC_eq]
            simp [Set.inter_comm]
      _ = (M : Set (EuclideanSpace Real (Fin m))) ∩ euclideanRelativeInterior m (A ⁻¹' Chead) := by
            simpa [Set.inter_comm] using hinter.1
      _ = {z : EuclideanSpace Real (Fin m) |
            ∀ i : Fin m,
              if (i : ℕ) < r then
                0 < (z : Fin m → ℝ) i
              else
                (z : Fin m → ℝ) i = 0} := by
            ext z
            constructor
            · rintro ⟨hzM, hzri⟩
              rw [hri_preimage] at hzri
              intro i
              by_cases hi : (i : ℕ) < r
              · have hpos : 0 < (z : Fin m → ℝ) i := hzri i hi
                simpa [hi] using hpos
              · have hi' : r ≤ (i : ℕ) := le_of_not_gt hi
                have hzero : (z : Fin m → ℝ) i = 0 := hzM i hi'
                simpa [hi] using hzero
            · intro hz
              refine ⟨?_, ?_⟩
              · intro i hi
                have hzero := hz i
                have hnot : ¬ (i : ℕ) < r := not_lt_of_ge hi
                simpa [hnot] using hzero
              · rw [hri_preimage]
                intro i hi
                have hpos := hz i
                simpa [hi] using hpos
  -- Rewrite the Euclidean relative-interior computation back to `Fin m → ℝ` coordinates.
  ext v
  rw [mem_euclideanRelativeInterior_fin_iff]
  rw [hri_C]
  constructor
  · intro hv
    intro i
    have hvi := hv i
    by_cases hi : (i : ℕ) < r
    · simpa [r, hi, e] using hvi
    · simpa [r, hi, e] using hvi
  · intro hv
    intro i
    have hvi := hv i
    by_cases hi : (i : ℕ) < r
    · simpa [r, hi, e] using hvi
    · simpa [r, hi, e] using hvi

/-- Helper for Lemma 6.29.9: once the mixed-core relative interior is known, origin-membership in
the fixed-`x` perturbation fiber is equivalent to the textbook strict/equality constraint witness
at that same `x`. -/
lemma helperForLemma_6_29_9_zero_mem_ri_fixedFiberCoordinateConditions_iff_strictWitness
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) (x : Fin n → ℝ) :
    (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          {u : Fin m → ℝ |
            x ∈ ordinaryConvexProgramObjectiveDomain P ∧
              ∀ i : Fin m,
                if (i : ℕ) < P.inequalityCount then
                  P.constraint i x ≤ u i
                else
                  P.constraint i x = u i} ↔
      x ∈ ordinaryConvexProgramObjectiveDomain P ∧
        ∀ i : Fin m,
          if (i : ℕ) < P.inequalityCount then
            P.constraint i x < 0
          else
            P.constraint i x = 0 := by
  -- Rewrite the guarded fiber as a translation of the mixed core, and evaluate the origin inside
  -- that translated relative interior.
  rw [helperForLemma_6_29_9_coordinateConditionFiber_eq_guardedTranslateOfMixedCore]
  by_cases hx : x ∈ ordinaryConvexProgramObjectiveDomain P
  · have hset :
        {u : Fin m → ℝ |
          x ∈ ordinaryConvexProgramObjectiveDomain P ∧
            u ∈ Set.image
              (fun v : Fin m → ℝ => v + fun i => P.constraint i x)
              (helperForLemma_6_29_9_mixedCoordinateCore P)} =
          Set.image
            (fun v : Fin m → ℝ => v + fun i => P.constraint i x)
            (helperForLemma_6_29_9_mixedCoordinateCore P) := by
      ext u
      simp [hx]
    rw [hset]
    rw [helperForLemma_6_29_9_zero_mem_ri_translate_iff_neg_mem_ri]
    rw [helperForLemma_6_29_9_euclideanRelativeInterior_mixedCoordinateCore]
    constructor
    · intro hneg
      refine ⟨hx, ?_⟩
      intro i
      by_cases hi : (i : ℕ) < P.inequalityCount
      · have hi' : 0 < -(P.constraint i x) := by
          simpa [hi] using hneg i
        have hlt : P.constraint i x < 0 := by
          linarith
        simpa [hi] using hlt
      · have hi' : -(P.constraint i x) = 0 := by
          simpa [hi] using hneg i
        have heq : P.constraint i x = 0 := by
          linarith
        simpa [hi] using heq
    · rintro ⟨_, hw⟩
      intro i
      by_cases hi : (i : ℕ) < P.inequalityCount
      · have hlt : P.constraint i x < 0 := by
          simpa [hi] using hw i
        have hi' : 0 < -(P.constraint i x) := by
          linarith
        simpa [hi] using hi'
      · have heq : P.constraint i x = 0 := by
          simpa [hi] using hw i
        simpa [hi, heq]
  · have hset :
      {u : Fin m → ℝ |
        x ∈ ordinaryConvexProgramObjectiveDomain P ∧
          u ∈ Set.image
            (fun v : Fin m → ℝ => v + fun i => P.constraint i x)
            (helperForLemma_6_29_9_mixedCoordinateCore P)} = ∅ := by
        ext u
        simp [hx]
    rw [hset]
    constructor
    · intro hzero
      have hzero' :
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm (0 : Fin m → ℝ) ∈
            euclideanRelativeInterior m
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm '' (∅ : Set (Fin m → ℝ))) :=
        (mem_euclideanRelativeInterior_fin_iff (n := m) (C := (∅ : Set (Fin m → ℝ))) (x := 0)).1
          hzero
      have : False := by
        have hmem :
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm (0 : Fin m → ℝ) ∈
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm '' (∅ : Set (Fin m → ℝ))) :=
          (euclideanRelativeInterior_subset_closure m
            ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin m)).symm '' (∅ : Set (Fin m → ℝ)))).1
            hzero'
        simpa using hmem
      exact False.elim this
    · rintro ⟨hx', _⟩
      exact (hx hx').elim

/-- Helper for Lemma 6.29.9: the geometric core identifies origin-membership in the rewritten
perturbation domain with a strict/equality witness in `ri C`. -/
lemma helperForLemma_6_29_9_zero_mem_ri_rewrittenPerturbationDomain_iff_strictWitness
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (helperForLemma_6_29_9_rewrittenPerturbationDomain P) ↔
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n (ordinaryConvexProgramObjectiveDomain P) ∧
          ∀ i : Fin m,
            if (i : ℕ) < P.inequalityCount then
              P.constraint i x < 0
            else
              P.constraint i x = 0 := by
  -- Route correction: package the feasible `(u, x)` pairs first, then separate the remaining
  -- work into a projection/section bridge and a fixed-fiber mixed-core computation.
  have hDomainRewrite :
      (0 : Fin m → ℝ) ∈ euclideanRelativeInterior_fin m
          (helperForLemma_6_29_9_rewrittenPerturbationDomain P) ↔
        (0 : Fin m → ℝ) ∈ euclideanRelativeInterior_fin m
          {u : Fin m → ℝ | ∃ x : Fin n → ℝ, (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P} := by
    -- The rewritten perturbation domain is precisely the `u`-projection of the feasible-pair set.
    have hProjectionSet :
        helperForLemma_6_29_9_rewrittenPerturbationDomain P =
          {u : Fin m → ℝ | ∃ x : Fin n → ℝ, (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P} := by
      ext u
      simpa [Set.mem_setOf_eq] using
        (helperForLemma_6_29_9_mem_rewrittenPerturbationDomain_iff_exists_feasiblePair P
          (u := u))
    simp [hProjectionSet]
  -- First convert origin-membership in the projection into an `x ∈ ri C` witness together with a
  -- relative-interior statement on the fixed perturbation fiber.
  rw [hDomainRewrite,
    helperForLemma_6_29_9_zero_mem_ri_projectionOfFeasiblePairSet_iff_exists_riFiberWitness]
  constructor
  · rintro ⟨x, hxri, hfiber⟩
    have hfiber' :
        (0 : Fin m → ℝ) ∈
          euclideanRelativeInterior_fin m
            {u : Fin m → ℝ |
              x ∈ ordinaryConvexProgramObjectiveDomain P ∧
                ∀ i : Fin m,
                  if (i : ℕ) < P.inequalityCount then
                    P.constraint i x ≤ u i
                  else
                    P.constraint i x = u i} := by
      simpa [helperForLemma_6_29_9_fixedFiber_eq_coordinateConditions] using hfiber
    have hwitness :=
      (helperForLemma_6_29_9_zero_mem_ri_fixedFiberCoordinateConditions_iff_strictWitness P x).1
        hfiber'
    exact ⟨x, hxri, hwitness.2⟩
  · rintro ⟨x, hxri, hwitness⟩
    have hxObjective : x ∈ ordinaryConvexProgramObjectiveDomain P := by
      have hxri' :
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x ∈
            euclideanRelativeInterior n
              ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm ''
                ordinaryConvexProgramObjectiveDomain P) :=
        (mem_euclideanRelativeInterior_fin_iff
          (n := n) (C := ordinaryConvexProgramObjectiveDomain P) (x := x)).1 hxri
      have hxObjective' :
          (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm x ∈
            (EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm ''
              ordinaryConvexProgramObjectiveDomain P :=
        (euclideanRelativeInterior_subset_closure n
          ((EuclideanSpace.equiv (𝕜 := Real) (ι := Fin n)).symm ''
            ordinaryConvexProgramObjectiveDomain P)).1 hxri'
      simpa using hxObjective'
    have hfiber' :
        (0 : Fin m → ℝ) ∈
          euclideanRelativeInterior_fin m
            {u : Fin m → ℝ |
              x ∈ ordinaryConvexProgramObjectiveDomain P ∧
                ∀ i : Fin m,
                  if (i : ℕ) < P.inequalityCount then
                    P.constraint i x ≤ u i
                  else
                    P.constraint i x = u i} := by
      exact
        (helperForLemma_6_29_9_zero_mem_ri_fixedFiberCoordinateConditions_iff_strictWitness P x).2
          ⟨hxObjective, hwitness⟩
    have hfiber :
        (0 : Fin m → ℝ) ∈
          euclideanRelativeInterior_fin m
            {u : Fin m → ℝ | (u, x) ∈ helperForLemma_6_29_9_feasiblePairSet P} := by
      simpa [helperForLemma_6_29_9_fixedFiber_eq_coordinateConditions] using hfiber'
    exact ⟨x, hxri, hfiber⟩

/-- Lemma 6.29.9: For an ordinary convex program `(P)`, strong consistency is equivalent to the
existence of a point `x ∈ ri C`, where `C = dom f₀`, such that each inequality constraint is
strictly negative and each equality constraint is zero. -/
theorem ordinaryConvexProgram_stronglyConsistent_iff_exists_point_in_riObjectiveDomain
    {m n : ℕ} (P : IndexedOrdinaryConvexProgram m n) :
    ordinaryConvexProgramStronglyConsistent P ↔
      ∃ x : Fin n → ℝ,
        x ∈ euclideanRelativeInterior_fin n (ordinaryConvexProgramObjectiveDomain P) ∧
          ∀ i : Fin m,
            if (i : ℕ) < P.inequalityCount then
              P.constraint i x < 0
            else
              P.constraint i x = 0 := by
  -- First rewrite strong consistency as origin-membership in the explicit perturbation domain.
  rw [helperForLemma_6_29_9_strongConsistency_iff_zero_mem_rewrittenPerturbationDomain]
  -- The remaining content is the Chapter 4 mixed strict/equality geometry for that domain.
  exact helperForLemma_6_29_9_zero_mem_ri_rewrittenPerturbationDomain_iff_strictWitness P

end Section29
end Chap06
