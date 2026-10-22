/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_22
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_extra_1

open scoped BigOperators

noncomputable section

section Chapter08Lemma826

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {ι : Type*} [Finite ι]

/- Domain sampling:
* primary domain: first-order descent systems and multiplier alternatives in real inner-product
  spaces
* inspected owners:
  `descentDirections` / `IsDescentDirectionAt`
  `HasGradientAt.gradient`
  `farkasSystem1` / `farkasSystem2`

Source/core/bridge triage:
* `source-facing`: the linear system on the objective gradient and the constraint gradients
* `core/canonical`: the Chapter 1 owner `descentDirections` on the objective side
* `bridge/view`: `HasGradientAt`, which identifies the primitive objective gradient vector with
  the canonical calculus owner when needed

The primitive data of Lemma 8.2.6 are the actual vectors `gradF` and `gradC i`. The function
`f` enters only through the existing owner `descentDirections f xStar`; using totalized
`gradient (c i) xStar` directly on the constraint side would change the source semantics at
nondifferentiable constraints. The source system also omits feasible-set and active-set data, so
it does not coincide with the constrained-problem owner exactly. -/

attribute [local instance] Fintype.ofFinite

/-- Helper for Chapter08 Lemma 8.2.6: the equality rows are duplicated so that the source mixed
system can be rewritten as a pure inequality system. -/
abbrev AugmentedConstraintIndex (E I : Set ι) := E ⊕ E ⊕ I

/-- Helper for Chapter08 Lemma 8.2.6: the augmented normal family consisting of the equality rows,
their negatives, and the inequality rows. -/
def augmentedConstraintGradient (E I : Set ι) (gradC : ι → X) :
    AugmentedConstraintIndex E I → X
  | Sum.inl i => gradC i
  | Sum.inr (Sum.inl i) => -gradC i
  | Sum.inr (Sum.inr i) => gradC i

/-- Helper for Chapter08 Lemma 8.2.6: the pure-inequality primal system used for the Farkas
reduction. -/
def augmentedPrimalSystem {κ : Type*} (gradF : X) (a : κ → X) (x : X) : Prop :=
  (∀ j : κ, inner ℝ x (a j) ≤ 0) ∧ 0 < inner ℝ x gradF

/-- Helper for Chapter08 Lemma 8.2.6: negating the direction rewrites the source
equality-and-inequality system as a pure inequality system on the augmented family. -/
lemma constraint_gradient_system_iff_augmented_inequality_system
    (E I : Set ι) (f : X → ℝ) (xStar gradF : X) (gradC : ι → X)
    (hf : HasGradientAt f gradF xStar) :
    (∃ d : X,
      d ∈ descentDirections f xStar ∩
        {d | (∀ i ∈ E, inner ℝ d (gradC i) = 0) ∧
          ∀ i ∈ I, 0 ≤ inner ℝ d (gradC i)}) ↔
      ∃ x : X,
        augmentedPrimalSystem gradF
          (augmentedConstraintGradient (X := X) E I gradC) x := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨-d, ?_⟩
    constructor
    · -- The augmented rows encode the equality constraints twice and the inequality rows once.
      intro j
      cases j with
      | inl i =>
          simpa [augmentedConstraintGradient, inner_neg_left] using (hd.2.1 i i.2).ge
      | inr j =>
          cases j with
          | inl i =>
              simpa [augmentedConstraintGradient, inner_neg_left, inner_neg_right] using
                (hd.2.1 i i.2).le
          | inr i =>
              simpa [augmentedConstraintGradient, inner_neg_left] using
                neg_nonpos.mpr (hd.2.2 i i.2)
    · -- Strict descent becomes strict positivity after the sign change.
      have hdesc : inner ℝ d gradF < 0 := by
        simpa [hf.gradient] using (mem_descentDirections_iff f xStar d).1 hd.1
      have hpos : 0 < -inner ℝ d gradF := by
        linarith
      simpa [augmentedPrimalSystem, inner_neg_left] using hpos
  · rintro ⟨x, hx⟩
    refine ⟨-x, ?_⟩
    constructor
    · -- Route correction: the source system is recovered by reading the two equality inequalities
      -- as an upper and lower bound, then undoing the initial sign change.
      have hneg : inner ℝ (-x) gradF < 0 := by
        simpa [inner_neg_left] using (neg_neg_of_pos hx.2)
      have hneg_grad : inner ℝ (-x) (gradient f xStar) < 0 := by
        simpa [hf.gradient] using hneg
      exact (mem_descentDirections_iff f xStar (-x)).2 hneg_grad
    · constructor
      · intro i hiE
        have hleft := hx.1 (Sum.inl ⟨i, hiE⟩)
        have hright := hx.1 (Sum.inr (Sum.inl ⟨i, hiE⟩))
        have hupper : inner ℝ x (gradC i) ≤ 0 := by
          simpa [augmentedConstraintGradient] using hleft
        have hlower : 0 ≤ inner ℝ x (gradC i) := by
          simpa [augmentedConstraintGradient, inner_neg_right] using hright
        simpa [inner_neg_left] using le_antisymm hupper hlower
      · intro i hiI
        have hrow := hx.1 (Sum.inr (Sum.inr ⟨i, hiI⟩))
        simpa [augmentedConstraintGradient, inner_neg_left] using neg_nonneg.mpr hrow

/-- Helper for Chapter08 Lemma 8.2.6: only the finite-dimensional span of the augmented normals
and `gradF` matters for the primal witness problem. -/
lemma augmented_inequality_system_exists_iff_exists_in_span
    {κ : Type*} [Finite κ] (gradF : X) (a : κ → X) :
    (∃ x : X, augmentedPrimalSystem gradF a x) ↔
      ∃ v : Submodule.span ℝ (Set.range a ∪ {gradF}),
        augmentedPrimalSystem gradF a (v : X) := by
  let V : Submodule ℝ X := Submodule.span ℝ (Set.range a ∪ {gradF})
  have hfinite : (Set.range a ∪ {gradF} : Set X).Finite :=
    (Set.finite_range a).union (Set.finite_singleton gradF)
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ hfinite
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨V.orthogonalProjectionOnto x, ?_⟩
    constructor
    · -- Projection preserves the inner products against vectors already lying in the span.
      intro j
      have haj : a j ∈ V := Submodule.subset_span (by
        exact Or.inl ⟨j, rfl⟩)
      let aj : V := ⟨a j, haj⟩
      have hproj : inner ℝ ((V.orthogonalProjectionOnto x : V) : X) (a j) = inner ℝ x (a j) := by
        change inner ℝ (V.orthogonalProjectionOnto x) aj = inner ℝ x aj
        exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right aj x
      rw [hproj]
      exact hx.1 j
    · -- The objective pairing is preserved for the same reason.
      have hgrad_mem : gradF ∈ V := Submodule.subset_span (by
        exact Or.inr (by simp))
      let g : V := ⟨gradF, hgrad_mem⟩
      have hproj : inner ℝ ((V.orthogonalProjectionOnto x : V) : X) gradF = inner ℝ x gradF := by
        change inner ℝ (V.orthogonalProjectionOnto x) g = inner ℝ x g
        exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right g x
      rw [hproj]
      exact hx.2
  · rintro ⟨v, hv⟩
    exact ⟨v, hv⟩

/-- Helper for Chapter08 Lemma 8.2.6: once the augmented primal system has been reduced to the
finite-dimensional span generated by the relevant normals and `gradF`, Farkas' lemma should
produce a nonnegative dual combination representing `gradF`. -/
lemma augmented_system_empty_implies_nonnegative_combination
    (E I : Set ι) (gradF : X) (gradC : ι → X)
    (hNo :
      ¬ ∃ v :
          Submodule.span ℝ
            (Set.range (augmentedConstraintGradient (X := X) E I gradC) ∪ {gradF}),
        augmentedPrimalSystem gradF
          (augmentedConstraintGradient (X := X) E I gradC) (v : X)) :
    ∃ μ : AugmentedConstraintIndex E I → ℝ,
      (∀ j, 0 ≤ μ j) ∧
        gradF =
          (∑ i : E,
            μ (Sum.inl i) • augmentedConstraintGradient (X := X) E I gradC (Sum.inl i)) +
            ((∑ i : E,
              μ (Sum.inr (Sum.inl i)) •
                augmentedConstraintGradient (X := X) E I gradC (Sum.inr (Sum.inl i))) +
              ∑ i : I,
                μ (Sum.inr (Sum.inr i)) •
                  augmentedConstraintGradient (X := X) E I gradC (Sum.inr (Sum.inr i))) := by
  let κ := AugmentedConstraintIndex E I
  let a : κ → X := augmentedConstraintGradient (X := X) E I gradC
  let V : Submodule ℝ X := Submodule.span ℝ (Set.range a ∪ {gradF})
  have hfinite : (Set.range a ∪ {gradF} : Set X).Finite :=
    (Set.finite_range a).union (Set.finite_singleton gradF)
  letI : FiniteDimensional ℝ V := FiniteDimensional.span_of_finite ℝ hfinite
  let b := stdOrthonormalBasis ℝ V
  let eκ : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  have hgrad_mem : gradF ∈ V := Submodule.subset_span (by
    exact Or.inr (by simp))
  let g : V := ⟨gradF, hgrad_mem⟩
  have ha_mem : ∀ j : κ, a j ∈ V := fun j =>
    Submodule.subset_span (by exact Or.inl ⟨j, rfl⟩)
  let aV : κ → V := fun j ↦ ⟨a j, ha_mem j⟩
  let A : Matrix (Fin (Fintype.card κ)) (Fin (Module.finrank ℝ V)) ℝ :=
    fun r k ↦ (b.repr (aV (eκ.symm r))).ofLp k
  let c : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := b.repr g
  have hrow :
      ∀ r : Fin (Fintype.card κ), matrixRowFamily A r = b.repr (aV (eκ.symm r)) := by
    intro r
    ext k
    have hrowCoord :
        inner ℝ (EuclideanSpace.basisFun (Fin (Module.finrank ℝ V)) ℝ k) (matrixRowFamily A r) =
          A r k := by
      simpa [Matrix.toEuclideanLin_apply] using
        (inner_matrixRowFamily_eq_apply A
          (EuclideanSpace.basisFun (Fin (Module.finrank ℝ V)) ℝ k) r)
    calc
      (matrixRowFamily A r).ofLp k
          = inner ℝ (EuclideanSpace.basisFun (Fin (Module.finrank ℝ V)) ℝ k)
              (matrixRowFamily A r) := by
              exact (EuclideanSpace.basisFun_inner
                (Fin (Module.finrank ℝ V)) ℝ (matrixRowFamily A r) k).symm
      _ = A r k := hrowCoord
      _ = (b.repr (aV (eκ.symm r))).ofLp k := by simp [A]
  have hprimal_model :
      (∃ v : V, augmentedPrimalSystem gradF a (v : X)) ↔ farkasSystem1 A c := by
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨b.repr v, ?_, ?_⟩
      · -- The coordinate matrix rows reproduce the augmented inequalities exactly.
        intro r
        calc
          A.toEuclideanLin (b.repr v) r
              = inner ℝ (b.repr v) (matrixRowFamily A r) := by
                  symm
                  exact inner_matrixRowFamily_eq_apply A (b.repr v) r
          _ = inner ℝ (b.repr v) (b.repr (aV (eκ.symm r))) := by rw [hrow r]
          _ = inner ℝ v (aV (eκ.symm r)) := by
                simpa using b.repr.inner_map_map v (aV (eκ.symm r))
          _ ≤ 0 := by
                simpa [aV] using hv.1 (eκ.symm r)
      · -- The objective row is preserved by the orthonormal coordinate map.
        have hposV : 0 < inner ℝ g v := by
          simpa [g, real_inner_comm] using hv.2
        have hcoord :
            inner ℝ c (b.repr v) = inner ℝ g v := by
          simpa [c] using b.repr.inner_map_map g v
        rw [hcoord]
        exact hposV
    · rintro ⟨x, hxA, hxc⟩
      refine ⟨b.repr.symm x, ?_⟩
      constructor
      · -- Reading the matrix inequalities back through `b.repr.symm` recovers the span witness.
        intro j
        have hrowj : matrixRowFamily A (eκ j) = b.repr (aV j) := by
          simpa using hrow (eκ j)
        have hcoord :
            inner ℝ (b.repr.symm x) (aV j) ≤ 0 := by
          calc
            inner ℝ (b.repr.symm x) (aV j)
                = inner ℝ x (b.repr (aV j)) := by
                    symm
                    simpa using b.repr.inner_map_map (b.repr.symm x) (aV j)
            _ = inner ℝ x (matrixRowFamily A (eκ j)) := by rw [← hrowj]
            _ = A.toEuclideanLin x (eκ j) := by
                  exact inner_matrixRowFamily_eq_apply A x (eκ j)
            _ ≤ 0 := hxA (eκ j)
        simpa [aV] using hcoord
      · have hcoord :
            inner ℝ c x = inner ℝ g (b.repr.symm x) := by
          simpa [c] using b.repr.inner_map_map g (b.repr.symm x)
        have hposV : 0 < inner ℝ g (b.repr.symm x) := by
          rw [← hcoord]
          exact hxc
        simpa [g, real_inner_comm] using hposV
  have hNoMatrix : ¬ farkasSystem1 A c := by
    intro hMatrix
    exact hNo ((hprimal_model).2 hMatrix)
  have hdual : farkasSystem2 A c := by
    rcases farkasLemmaOneHasSolution A c with hprimal | hcert
    · exact False.elim (hNoMatrix hprimal)
    · exact hcert
  rcases hdual with ⟨y, hyEq, hyNonneg⟩
  let μ : κ → ℝ := fun j ↦ y (eκ j)
  have hreprV : g = ∑ j : κ, μ j • aV j := by
    apply b.repr.injective
    ext k
    have hk :
        c.ofLp k = ∑ r : Fin (Fintype.card κ), A r k * y r := by
      calc
        c.ofLp k = (matrixTransposeCoordMap A y).ofLp k := by
          simpa using congrArg (fun z => z.ofLp k) hyEq.symm
        _ = ∑ r : Fin (Fintype.card κ), A r k * y r := by
          simp [matrixTransposeCoordMap, Matrix.mulVec, dotProduct]
    calc
      (b.repr g).ofLp k = c.ofLp k := by rfl
      _ = ∑ r : Fin (Fintype.card κ), A r k * y r := hk
      _ = ∑ j : κ, μ j * (b.repr (aV j)).ofLp k := by
            rw [show (∑ r : Fin (Fintype.card κ), A r k * y r) =
                ∑ r : Fin (Fintype.card κ), y r * A r k by
                  simp_rw [mul_comm]]
            simpa [μ, A] using
              (Equiv.sum_comp eκ
                (fun r : Fin (Fintype.card κ) ↦ y r * A r k)).symm
      _ = (b.repr (∑ j : κ, μ j • aV j)).ofLp k := by
            simp
  have hrepr :
      gradF = ∑ j : κ, μ j • a j := by
    have hreprX := congrArg (fun z : V ↦ (z : X)) hreprV
    simpa [g, aV] using hreprX
  refine ⟨μ, ?_, ?_⟩
  · -- The dual certificate stays nonnegative after reindexing the rows back to `κ`.
    intro j
    simpa [μ] using hyNonneg (eκ j)
  · -- Splitting the augmented sum by its three row blocks gives the textbook certificate shape.
    simpa [κ, a, augmentedConstraintGradient, Fintype.sum_sum_type, add_assoc] using hrepr

/-- Helper for Chapter08 Lemma 8.2.6: a nonnegative coefficient family on the augmented system
compresses to the textbook multiplier family, with the equality multipliers obtained by subtracting
the two equality-row coefficients. -/
lemma augmented_dual_combination_yields_multiplier_family
    (E I : Set ι) (h_disj : Disjoint E I) (gradF : X) (gradC : ι → X)
    (μ : AugmentedConstraintIndex E I → ℝ)
    (hμ_nonneg : ∀ j, 0 ≤ μ j)
    (hμ_repr :
      gradF =
        (∑ i : E,
          μ (Sum.inl i) • augmentedConstraintGradient (X := X) E I gradC (Sum.inl i)) +
          ((∑ i : E,
            μ (Sum.inr (Sum.inl i)) •
              augmentedConstraintGradient (X := X) E I gradC (Sum.inr (Sum.inl i))) +
            ∑ i : I,
              μ (Sum.inr (Sum.inr i)) •
                augmentedConstraintGradient (X := X) E I gradC (Sum.inr (Sum.inr i)))) :
    ∃ lam : ι → ℝ,
      (∀ i ∈ I, 0 ≤ lam i) ∧
        gradF = (∑ i : E, lam i • gradC i) + (∑ i : I, lam i • gradC i) := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  letI : Fintype I := Fintype.ofFinite I
  let lam : ι → ℝ := fun i ↦
    if hiE : i ∈ E then
      μ (Sum.inl ⟨i, hiE⟩) - μ (Sum.inr (Sum.inl ⟨i, hiE⟩))
    else if hiI : i ∈ I then
      μ (Sum.inr (Sum.inr ⟨i, hiI⟩))
    else
      0
  refine ⟨lam, ?_, ?_⟩
  · intro i hiI
    -- Disjointness forces the `I`-branch of `lam`, so its value is the nonnegative third-block
    -- coefficient.
    have hnotE : i ∉ E := by
      intro hiE
      exact Set.disjoint_left.mp h_disj hiE hiI
    simpa [lam, hnotE, hiI] using hμ_nonneg (Sum.inr (Sum.inr ⟨i, hiI⟩))
  · -- Route correction: the certificate is already split into the three augmented blocks, so the
    -- remaining work is only algebraic compression of the duplicated equality rows.
    have hrepr' :=
      (show
        gradF =
          (∑ i : E, μ (Sum.inl i) • gradC i) +
            ((-(∑ i : E, μ (Sum.inr (Sum.inl i)) • gradC i)) +
              ∑ i : I, μ (Sum.inr (Sum.inr i)) • gradC i) from by
          simpa [augmentedConstraintGradient, smul_neg, add_assoc] using hμ_repr)
    have hEqCompress :
        (∑ i : E, μ (Sum.inl i) • gradC i) +
            (-(∑ i : E, μ (Sum.inr (Sum.inl i)) • gradC i)) =
          ∑ i : E, lam i • gradC i := by
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl ?_
      intro i hi
      calc
        μ (Sum.inl i) • gradC ↑i + -(μ (Sum.inr (Sum.inl i)) • gradC ↑i)
            = μ (Sum.inl i) • gradC ↑i + (-μ (Sum.inr (Sum.inl i))) • gradC ↑i := by
                simp
        _ = (μ (Sum.inl i) + -μ (Sum.inr (Sum.inl i))) • gradC ↑i := by
              rw [add_smul]
        _ = lam i • gradC ↑i := by
              simp [lam, i.2, sub_eq_add_neg]
    have hIRewrite :
        (∑ i : I, μ (Sum.inr (Sum.inr i)) • gradC i) =
          ∑ i : I, lam i • gradC i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hnotE : (i : ι) ∉ E := by
        intro hiE
        exact Set.disjoint_left.mp h_disj hiE i.2
      simp [lam, hnotE, i.2]
    calc
      gradF =
          (∑ i : E, μ (Sum.inl i) • gradC i) +
            ((-(∑ i : E, μ (Sum.inr (Sum.inl i)) • gradC i)) +
              ∑ i : I, μ (Sum.inr (Sum.inr i)) • gradC i) := hrepr'
      _ =
          ((∑ i : E, μ (Sum.inl i) • gradC i) +
            (-(∑ i : E, μ (Sum.inr (Sum.inl i)) • gradC i))) +
              ∑ i : I, μ (Sum.inr (Sum.inr i)) • gradC i := by
                rw [add_assoc]
      _ = (∑ i : E, lam i • gradC i) +
            ∑ i : I, μ (Sum.inr (Sum.inr i)) • gradC i := by
              rw [hEqCompress]
      _ = (∑ i : E, lam i • gradC i) + ∑ i : I, lam i • gradC i := by
            rw [hIRewrite]

/-- Helper for Chapter08 Lemma 8.2.6: once the textbook multiplier identity holds, no direction can
satisfy the source strict-descent/equality/inequality system. -/
lemma multiplier_family_forces_constraint_system_empty
    (E I : Set ι) (f : X → ℝ) (xStar gradF : X) (gradC : ι → X)
    (hf : HasGradientAt f gradF xStar)
    (hLam :
      ∃ lam : ι → ℝ,
        (∀ i ∈ I, 0 ≤ lam i) ∧
          gradF = (∑ i : E, lam i • gradC i) + (∑ i : I, lam i • gradC i)) :
    descentDirections f xStar ∩
        {d | (∀ i ∈ E, inner ℝ d (gradC i) = 0) ∧
          ∀ i ∈ I, 0 ≤ inner ℝ d (gradC i)} = (∅ : Set X) := by
  rcases hLam with ⟨lam, hlam_nonneg, hlam_repr⟩
  rw [Set.eq_empty_iff_forall_notMem]
  intro d hd
  have hdesc : inner ℝ d gradF < 0 := by
    simpa [hf.gradient] using (mem_descentDirections_iff f xStar d).1 hd.1
  have hnonneg_grad : 0 ≤ inner ℝ d gradF := by
    -- Pair the multiplier identity with `d`; the equality rows vanish and the inequality rows are
    -- nonnegative term by term.
    rw [hlam_repr, inner_add_right, inner_sum, inner_sum]
    refine add_nonneg ?_ ?_
    · have hzero :
          ∀ i : E, inner ℝ d (lam i • gradC i) = 0 := by
            intro i
            simpa [inner_smul_right, hd.2.1 i i.2] using
              (show lam i * inner ℝ d (gradC i) = 0 by simp [hd.2.1 i i.2])
      simp [hzero]
    · refine Finset.sum_nonneg ?_
      intro i hi
      simpa [inner_smul_right, mul_comm] using
        mul_nonneg (hlam_nonneg i i.2) (hd.2.2 i i.2)
  exact not_lt_of_ge hnonneg_grad hdesc

/-- Chapter08 Lemma 8.2.6: assuming `E` and `I` are disjoint, the source descent system
`(8.2.16)` has no solution exactly when there exists a multiplier family `lam`, nonnegative on
`I`, such that
`gradF = (∑ i : E, lam i • gradC i) + (∑ i : I, lam i • gradC i)`. Here `hf` identifies
`gradF` as the gradient of `f` at `xStar`, while the constraint gradients stay as primitive
source data. -/
theorem descentDirections_inter_constraintGradientSystem_eq_empty_iff_exists_multiplier
    (E I : Set ι) (h_disj : Disjoint E I) (f : X → ℝ) (xStar gradF : X) (gradC : ι → X)
    (hf : HasGradientAt f gradF xStar) :
    descentDirections f xStar ∩
        {d | (∀ i ∈ E, inner ℝ d (gradC i) = 0) ∧
          ∀ i ∈ I, 0 ≤ inner ℝ d (gradC i)} = (∅ : Set X) ↔
      ∃ lam : ι → ℝ,
        (∀ i ∈ I, 0 ≤ lam i) ∧
          gradF = (∑ i : E, lam i • gradC i) + (∑ i : I, lam i • gradC i) := by
  constructor
  · intro hEmpty
    let a := augmentedConstraintGradient (X := X) E I gradC
    have hNoOriginal :
        ¬ ∃ d : X,
          d ∈ descentDirections f xStar ∩
            {d | (∀ i ∈ E, inner ℝ d (gradC i) = 0) ∧
              ∀ i ∈ I, 0 ≤ inner ℝ d (gradC i)} := by
      rintro ⟨d, hd⟩
      have : d ∈ (∅ : Set X) := by
        rw [← hEmpty]
        exact hd
      simpa using this
    have hNoAugmented :
        ¬ ∃ x : X, augmentedPrimalSystem gradF a x := by
      intro hx
      exact hNoOriginal
        ((constraint_gradient_system_iff_augmented_inequality_system
          (X := X) E I f xStar gradF gradC hf).2 hx)
    have hNoSpan :
        ¬ ∃ v : Submodule.span ℝ (Set.range a ∪ {gradF}),
          augmentedPrimalSystem gradF a (v : X) := by
      intro hv
      exact hNoAugmented
        ((augmented_inequality_system_exists_iff_exists_in_span
          (X := X) gradF a).2 hv)
    obtain ⟨μ, hμ_nonneg, hμ_repr⟩ :=
      augmented_system_empty_implies_nonnegative_combination
        (X := X) E I gradF gradC (by simpa [a] using hNoSpan)
    exact augmented_dual_combination_yields_multiplier_family
      (X := X) E I h_disj gradF gradC μ hμ_nonneg hμ_repr
  · intro hLam
    exact multiplier_family_forces_constraint_system_empty
      (X := X) E I f xStar gradF gradC hf hLam

end Chapter08Lemma826
