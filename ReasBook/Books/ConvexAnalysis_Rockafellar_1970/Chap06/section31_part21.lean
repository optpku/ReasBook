/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section31_part20

open scoped Topology

section Chap06
section Section31

attribute [local instance] Classical.propDecidable

/-- The one-dimensional lift of a scalar `EReal`-valued function, viewed as a function on
`ℝ^1`. -/
noncomputable def scalarCoordinateLift (φ : ℝ → EReal) : (Fin 1 → ℝ) → EReal :=
  fun x => φ (x 0)

/-- The separable sum `x ↦ ∑ᵢ fᵢ(xᵢ)` attached to a family of scalar convex functions. -/
noncomputable def separableCoordinateFunctionSum {n : ℕ} (fFamily : Fin n → ℝ → EReal) :
    (Fin n → ℝ) → EReal :=
  fun x => ∑ i, fFamily i (x i)

/-- The sum of the one-dimensional Fenchel conjugates of the coordinate functions in a separable
family. -/
noncomputable def separableCoordinateConjugateSum {n : ℕ} (fFamily : Fin n → ℝ → EReal) :
    (Fin n → ℝ) → EReal :=
  fun xStar =>
    ∑ i, fenchelConjugate 1 (scalarCoordinateLift (fFamily i)) (fun _ : Fin 1 => xStar i)

/-- The orthogonal complement of a subspace, written as the set of vectors annihilating that
subspace under the Euclidean dot product. -/
def subspaceOrthogonalComplementSet {n : ℕ} (L : Submodule ℝ (Fin n → ℝ)) :
    Set (Fin n → ℝ) :=
  {xStar | ∀ x ∈ (L : Set (Fin n → ℝ)), dotProduct xStar x = 0}

/-- The graph of the subdifferential of a scalar convex function, encoded through its lift to
`ℝ^1`. -/
def scalarSubdifferentialGraph (φ : ℝ → EReal) : Set (ℝ × ℝ) :=
  {p |
    dotProductEquiv ℝ (Fin 1) (fun _ : Fin 1 => p.2) ∈
      subdifferentialAt (scalarCoordinateLift φ) (fun _ : Fin 1 => p.1)}

/-- The Fenchel conjugate of a finite separable sum is the sum of the one-dimensional
conjugates. Properness of the coordinate functions is used only to rule out `⊥` when
distributing negation across the finite sum. -/
lemma fenchelConjugate_separableCoordinateFunctionSum {n : ℕ}
    (fFamily : Fin n → ℝ → EReal)
    (hfFamily_proper :
      ∀ j : Fin n,
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (scalarCoordinateLift (fFamily j)))
    (xStar : Fin n → ℝ) :
    fenchelConjugate n (separableCoordinateFunctionSum fFamily) xStar =
      separableCoordinateConjugateSum fFamily xStar := by
  classical
  let e : (Fin n → ℝ) ≃ (∀ i : Fin n, Fin 1 → ℝ) :=
    { toFun := fun x i _ => x i
      invFun := fun x i => x i 0
      left_inv := by
        intro x
        rfl
      right_inv := by
        intro x
        funext i j
        fin_cases j
        rfl }
  have hpointwise (x : Fin n → ℝ) :
      (((dotProduct x xStar : ℝ) : EReal) - separableCoordinateFunctionSum fFamily x) =
        ∑ i : Fin n,
          ((((e x i) ⬝ᵥ (fun _ : Fin 1 => xStar i) : ℝ) : EReal) -
            scalarCoordinateLift (fFamily i) (e x i)) := by
    have hnotbot : ∀ i ∈ (Finset.univ : Finset (Fin n)), fFamily i (x i) ≠ (⊥ : EReal) := by
      intro i hi
      exact (hfFamily_proper i).2.2 (fun _ : Fin 1 => x i) (by simp)
    have hcoe :
        (((∑ i : Fin n, x i * xStar i : ℝ)) : EReal) =
          ∑ i : Fin n, (((x i * xStar i : ℝ) : EReal)) := by
      simpa using
        helperForTheorem_6_30_22_coe_finset_sum_eq_finset_sum_coe
          (s := (Finset.univ : Finset (Fin n))) (r := fun i => x i * xStar i)
    have hneg :
        -(∑ i : Fin n, fFamily i (x i)) = ∑ i : Fin n, -(fFamily i (x i)) :=
      section16_neg_sum_eq_sum_neg (s := (Finset.univ : Finset (Fin n)))
        (b := fun i => fFamily i (x i)) hnotbot
    rw [separableCoordinateFunctionSum, dotProduct, hcoe]
    simp only [sub_eq_add_neg, hneg, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp [e, scalarCoordinateLift, dotProduct]
  rw [fenchelConjugate_eq_iSup]
  change iSup (fun x : Fin n → ℝ =>
      (((dotProduct x xStar : ℝ) : EReal) - separableCoordinateFunctionSum fFamily x)) = _
  calc
    iSup (fun x : Fin n → ℝ =>
        (((dotProduct x xStar : ℝ) : EReal) - separableCoordinateFunctionSum fFamily x)) =
        iSup (fun x : ∀ i : Fin n, Fin 1 → ℝ =>
          ∑ i : Fin n,
            ((((x i) ⬝ᵥ (fun _ : Fin 1 => xStar i) : ℝ) : EReal) -
              scalarCoordinateLift (fFamily i) (x i))) := by
          refine Equiv.iSup_congr e ?_
          intro x
          exact (hpointwise x).symm
    _ = ∑ i : Fin n,
          iSup (fun xi : Fin 1 → ℝ =>
            (((xi ⬝ᵥ (fun _ : Fin 1 => xStar i) : ℝ) : EReal) -
              scalarCoordinateLift (fFamily i) xi)) := by
          exact helperForTheorem_6_30_14_dependentFamily_iSup_sum_eq_sum_iSup
            (n := fun _ : Fin n => 1)
            (g := fun i xi =>
              (((xi ⬝ᵥ (fun _ : Fin 1 => xStar i) : ℝ) : EReal) -
                scalarCoordinateLift (fFamily i) xi))
    _ = separableCoordinateConjugateSum fFamily xStar := by
          simp only [separableCoordinateConjugateSum, fenchelConjugate_eq_iSup]

/-- For a proper separable objective, the Euclidean subgradient condition is exactly the
coordinatewise scalar subgradient condition. -/
lemma euclideanSubgradient_separableCoordinateFunctionSum_iff {n : ℕ}
    (fFamily : Fin n → ℝ → EReal)
    (hfProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (separableCoordinateFunctionSum fFamily))
    (hfFamily_proper :
      ∀ j : Fin n,
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (scalarCoordinateLift (fFamily j)))
    (x xStar : Fin n → ℝ) :
    IsEuclideanSubgradientAt (separableCoordinateFunctionSum fFamily) x xStar ↔
      ∀ j : Fin n, (x j, xStar j) ∈ scalarSubdifferentialGraph (fFamily j) := by
  classical
  let fStar : Fin n → EReal := fun i =>
    fenchelConjugate 1 (scalarCoordinateLift (fFamily i)) (fun _ : Fin 1 => xStar i)
  have hconj :
      fenchelConjugate n (separableCoordinateFunctionSum fFamily) xStar = ∑ i, fStar i := by
    simpa [fStar, separableCoordinateConjugateSum] using
      fenchelConjugate_separableCoordinateFunctionSum fFamily hfFamily_proper xStar
  constructor
  · intro hsub
    have hfullFY :
        FenchelYoungEqualityAt (separableCoordinateFunctionSum fFamily) x xStar :=
      ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        (separableCoordinateFunctionSum fFamily) hfProper x xStar).1.out 0 3).1 hsub
    have hsumFinite :=
      helperForTheorem_23_5_finiteAt_of_euclideanSubgradient
        (separableCoordinateFunctionSum fFamily) hfProper x xStar hsub
    have hfi_ne_bot : ∀ i : Fin n, fFamily i (x i) ≠ (⊥ : EReal) := by
      intro i
      exact (hfFamily_proper i).2.2 (fun _ : Fin 1 => x i) (by simp)
    have hfi_ne_top : ∀ i : Fin n, fFamily i (x i) ≠ (⊤ : EReal) := by
      intro i htop
      exact hsumFinite.1
        (sum_eq_top_of_term_top
          (s := (Finset.univ : Finset (Fin n)))
          (f := fun j : Fin n => fFamily j (x j))
          (i := i) (by simp) htop
          (by intro j hj; exact hfi_ne_bot j))
    have hfStar_ne_bot : ∀ i : Fin n, fStar i ≠ (⊥ : EReal) := by
      intro i
      obtain ⟨z0, r0, hz0⟩ :=
        properConvexFunctionOn_exists_finite_point
          (n := 1) (f := scalarCoordinateLift (fFamily i)) (hfFamily_proper i)
      exact fenchelConjugate_ne_bot_of_exists_ne_top
        (n := 1) (f := scalarCoordinateLift (fFamily i))
        ⟨z0, by rw [hz0]; simp⟩ (fun _ : Fin 1 => xStar i)
    have hfullStar_ne_top :
        fenchelConjugate n (separableCoordinateFunctionSum fFamily) xStar ≠ (⊤ : EReal) := by
      intro htop
      rw [FenchelYoungEqualityAt] at hfullFY
      have hleftTop :
          separableCoordinateFunctionSum fFamily x +
              fenchelConjugate n (separableCoordinateFunctionSum fFamily) xStar = (⊤ : EReal) := by
        rw [htop]
        exact EReal.add_top_of_ne_bot hsumFinite.2
      exact EReal.coe_ne_top (dotProduct x xStar) (hfullFY.symm.trans hleftTop)
    have hsumStar_ne_top : (∑ i, fStar i) ≠ (⊤ : EReal) := by
      simpa [hconj] using hfullStar_ne_top
    have hfStar_ne_top : ∀ i : Fin n, fStar i ≠ (⊤ : EReal) := by
      intro i htop
      exact hsumStar_ne_top
        (sum_eq_top_of_term_top
          (s := (Finset.univ : Finset (Fin n))) (f := fStar)
          (i := i) (by simp) htop
          (by intro j hj; exact hfStar_ne_bot j))
    have hgap_nonneg : ∀ i : Fin n,
        0 ≤ (fFamily i (x i)).toReal + (fStar i).toReal - x i * xStar i := by
      intro i
      have hfenchel := fenchel_inequality 1 (scalarCoordinateLift (fFamily i))
        (hfFamily_proper i) (fun _ : Fin 1 => x i) (fun _ : Fin 1 => xStar i)
      have hreal_le :
          x i * xStar i ≤
            (fFamily i (x i) + fStar i).toReal := by
        simpa [scalarCoordinateLift, fStar, dotProduct] using
          EReal.toReal_le_toReal hfenchel (EReal.coe_ne_bot _)
            (EReal.add_ne_top (hfi_ne_top i) (hfStar_ne_top i))
      have hadd_toReal :
          (fFamily i (x i) + fStar i).toReal =
            (fFamily i (x i)).toReal + (fStar i).toReal :=
        EReal.toReal_add (hfi_ne_top i) (hfi_ne_bot i)
          (hfStar_ne_top i) (hfStar_ne_bot i)
      rw [hadd_toReal] at hreal_le
      linarith
    have hsum_fx_real :
        separableCoordinateFunctionSum fFamily x =
          ((((∑ i, (fFamily i (x i)).toReal) : ℝ)) : EReal) := by
      rw [separableCoordinateFunctionSum]
      calc
        (∑ i, fFamily i (x i)) =
            ∑ i, ((((fFamily i (x i)).toReal : ℝ)) : EReal) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
                (hTop := hfi_ne_top i) (hBot := hfi_ne_bot i)
        _ = ((((∑ i, (fFamily i (x i)).toReal) : ℝ)) : EReal) := by
              symm
              exact section16_coe_finset_sum (s := Finset.univ)
                (b := fun i : Fin n => (fFamily i (x i)).toReal)
    have hsum_star_real :
        (∑ i, fStar i) = ((((∑ i, (fStar i).toReal) : ℝ)) : EReal) := by
      calc
        (∑ i, fStar i) = ∑ i, ((((fStar i).toReal : ℝ)) : EReal) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
            (hTop := hfStar_ne_top i) (hBot := hfStar_ne_bot i)
        _ = ((((∑ i, (fStar i).toReal) : ℝ)) : EReal) := by
          symm
          exact section16_coe_finset_sum (s := Finset.univ)
            (b := fun i : Fin n => (fStar i).toReal)
    have hsum_eq_dot :
        (∑ i, (fFamily i (x i)).toReal) + (∑ i, (fStar i).toReal) =
          ∑ i, x i * xStar i := by
      have hEqEReal :
          (((∑ i, (fFamily i (x i)).toReal) + ∑ i, (fStar i).toReal : ℝ) : EReal) =
            (((∑ i, x i * xStar i : ℝ)) : EReal) := by
        calc
          (((∑ i, (fFamily i (x i)).toReal) + ∑ i, (fStar i).toReal : ℝ) : EReal) =
              separableCoordinateFunctionSum fFamily x + ∑ i, fStar i := by
                rw [hsum_fx_real, hsum_star_real]
                simp [EReal.coe_add]
          _ = separableCoordinateFunctionSum fFamily x +
                fenchelConjugate n (separableCoordinateFunctionSum fFamily) xStar := by
                rw [hconj]
          _ = ((dotProduct x xStar : ℝ) : EReal) := by
                simpa [FenchelYoungEqualityAt] using hfullFY
          _ = (((∑ i, x i * xStar i : ℝ)) : EReal) := by
                simp [dotProduct]
      exact_mod_cast hEqEReal
    have hgap_sum_zero :
        ∑ i, ((fFamily i (x i)).toReal + (fStar i).toReal - x i * xStar i) = 0 := by
      calc
        ∑ i, ((fFamily i (x i)).toReal + (fStar i).toReal - x i * xStar i) =
            (∑ i, (fFamily i (x i)).toReal) + (∑ i, (fStar i).toReal) -
              ∑ i, x i * xStar i := by
                simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                  sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = 0 := by linarith
    have hgap_zero : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        (fFamily i (x i)).toReal + (fStar i).toReal - x i * xStar i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (s := Finset.univ)
        (f := fun i : Fin n =>
          (fFamily i (x i)).toReal + (fStar i).toReal - x i * xStar i)
        (by intro i hi; exact hgap_nonneg i)).1 hgap_sum_zero
    intro i
    have hrealEq :
        (fFamily i (x i)).toReal + (fStar i).toReal = x i * xStar i := by
      linarith [hgap_zero i (by simp)]
    have hscalarFY :
        FenchelYoungEqualityAt (scalarCoordinateLift (fFamily i))
          (fun _ : Fin 1 => x i) (fun _ : Fin 1 => xStar i) := by
      rw [FenchelYoungEqualityAt]
      change fFamily i (x i) + fStar i = _
      calc
        fFamily i (x i) + fStar i =
            ((((fFamily i (x i)).toReal + (fStar i).toReal : ℝ)) : EReal) := by
              rw [helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
                    (hTop := hfi_ne_top i) (hBot := hfi_ne_bot i)]
              rw [helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot
                    (hTop := hfStar_ne_top i) (hBot := hfStar_ne_bot i)]
              simp [EReal.coe_add]
        _ = ((dotProduct (fun _ : Fin 1 => x i) (fun _ : Fin 1 => xStar i) : ℝ) : EReal) := by
              simp [dotProduct, hrealEq]
    have hscalarSub :
        IsEuclideanSubgradientAt (scalarCoordinateLift (fFamily i))
          (fun _ : Fin 1 => x i) (fun _ : Fin 1 => xStar i) :=
      ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        (scalarCoordinateLift (fFamily i)) (hfFamily_proper i)
        (fun _ : Fin 1 => x i) (fun _ : Fin 1 => xStar i)).1.out 3 0).1 hscalarFY
    simpa [scalarSubdifferentialGraph, IsEuclideanSubgradientAt] using hscalarSub
  · intro hcoord
    have hscalarFY : ∀ i : Fin n,
        FenchelYoungEqualityAt (scalarCoordinateLift (fFamily i))
          (fun _ : Fin 1 => x i) (fun _ : Fin 1 => xStar i) := by
      intro i
      have hscalarSub :
          IsEuclideanSubgradientAt (scalarCoordinateLift (fFamily i))
            (fun _ : Fin 1 => x i) (fun _ : Fin 1 => xStar i) := by
        simpa [scalarSubdifferentialGraph, IsEuclideanSubgradientAt] using hcoord i
      exact ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        (scalarCoordinateLift (fFamily i)) (hfFamily_proper i)
        (fun _ : Fin 1 => x i) (fun _ : Fin 1 => xStar i)).1.out 0 3).1 hscalarSub
    have hfullFY :
        FenchelYoungEqualityAt (separableCoordinateFunctionSum fFamily) x xStar := by
      rw [FenchelYoungEqualityAt, hconj]
      change (∑ i, fFamily i (x i)) + ∑ i, fStar i = _
      calc
        (∑ i, fFamily i (x i)) + ∑ i, fStar i =
            ∑ i, (fFamily i (x i) + fStar i) := by
              rw [Finset.sum_add_distrib]
        _ = ∑ i, (((x i * xStar i : ℝ) : EReal)) := by
              apply Finset.sum_congr rfl
              intro i hi
              simpa [FenchelYoungEqualityAt, scalarCoordinateLift, fStar, dotProduct] using
                hscalarFY i
        _ = ((dotProduct x xStar : ℝ) : EReal) := by
              rw [dotProduct]
              symm
              exact helperForTheorem_6_30_22_coe_finset_sum_eq_finset_sum_coe
                (s := (Finset.univ : Finset (Fin n))) (r := fun i => x i * xStar i)
    exact ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
      (separableCoordinateFunctionSum fFamily) hfProper x xStar).1.out 3 0).1 hfullFY

/-- The coordinatewise Kuhn-Tucker conditions for a separable convex objective over a subspace. -/
def SeparableSubspaceKuhnTuckerConditions {n : ℕ} (fFamily : Fin n → ℝ → EReal)
    (L : Submodule ℝ (Fin n → ℝ)) (x xStar : Fin n → ℝ) : Prop :=
  x ∈ (L : Set (Fin n → ℝ)) ∧
    xStar ∈ subspaceOrthogonalComplementSet L ∧
      ∀ j : Fin n, (x j, xStar j) ∈ scalarSubdifferentialGraph (fFamily j)

/-- The subspace duality statement of Corollary 31.4.2 specialized to a separable convex
objective `x ↦ ∑ᵢ fᵢ(xᵢ)`, with the dual objective written as the sum of the scalar conjugates and
the optimality condition written coordinatewise via the graphs of the scalar subdifferentials. -/
def SeparableSubspaceFenchelApplicationStatement {n : ℕ} (fFamily : Fin n → ℝ → EReal)
    (L : Submodule ℝ (Fin n → ℝ)) : Prop :=
  let f := separableCoordinateFunctionSum fFamily
  let orthogonal := subspaceOrthogonalComplementSet L
  let primal : EReal :=
    functionInfimumEReal (fun x => f x + indicatorFunction (L : Set (Fin n → ℝ)) x)
  let dual : EReal :=
    functionInfimumEReal
      (fun xStar => separableCoordinateConjugateSum fFamily xStar + indicatorFunction orthogonal xStar)
  ((((∃ x : Fin n → ℝ,
          x ∈ (L : Set (Fin n → ℝ)) ∧
            x ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) ∨
        ∃ xStar : Fin n → ℝ,
          xStar ∈ orthogonal ∧
            xStar ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ))
                (separableCoordinateConjugateSum fFamily))) →
      primal = -dual) ∧
    ((∃ x : Fin n → ℝ,
        x ∈ (L : Set (Fin n → ℝ)) ∧
          x ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) →
      ∃ xStar : Fin n → ℝ,
        xStar ∈ orthogonal ∧ dual = separableCoordinateConjugateSum fFamily xStar) ∧
    ((∃ xStar : Fin n → ℝ,
        xStar ∈ orthogonal ∧
          xStar ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (separableCoordinateConjugateSum fFamily))) →
      ∃ x : Fin n → ℝ, x ∈ (L : Set (Fin n → ℝ)) ∧ primal = f x) ∧
    (∀ x xStar : Fin n → ℝ,
      (x ∈ (L : Set (Fin n → ℝ)) ∧
        xStar ∈ orthogonal ∧
        f x = primal ∧
        primal = -dual ∧
        dual = separableCoordinateConjugateSum fFamily xStar) ↔
          SeparableSubspaceKuhnTuckerConditions fFamily L x xStar))

-- Proof sketch: write the separable objective as `x ↦ ∑ᵢ fᵢ(xᵢ)` and use the one-dimensional
-- conjugate formula coordinatewise to identify `f⋆` with the sum of the scalar conjugates.
-- Then specialize Corollary 31.4.2 to this `f`: the primal and dual subspace extremum problems
-- become the displayed separable minimization problems, and the single subgradient condition
-- `xStar ∈ ∂ f(x)` becomes the coordinatewise graph condition `(xⱼ, x⋆ⱼ) ∈ Γⱼ`.
/-- Lemma 31.4.5 (Separable Case of Corollary 31.4.2): let
`f : ℝ^n → ℝ ∪ {+∞}` be a separable closed proper convex function with
`f(x) = ∑ᵢ fᵢ(xᵢ)`, where each scalar coordinate function `fᵢ : ℝ → ℝ ∪ {+∞}` is closed proper
convex. Then `(1)` the conjugate `f⋆` is separable, namely
`f⋆(x⋆) = ∑ᵢ fᵢ⋆(x⋆ᵢ)`; `(2)` the primal-dual extremal problems in Corollary 31.4.2 reduce to
minimizing `∑ᵢ fᵢ(xᵢ)` on `L` and minimizing `∑ᵢ fᵢ⋆(x⋆ᵢ)` on `L⊥`; and `(3)` the
Kuhn-Tucker conditions reduce to membership of `x` in `L`, membership of `x⋆` in `L⊥`, and the
coordinatewise graph conditions `(xᵢ, x⋆ᵢ) ∈ Γᵢ`, where `Γᵢ` is the graph of `∂ fᵢ`. -/
lemma separable_case_of_subspace_fenchel_duality_corollary {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (fFamily : Fin n → ℝ → EReal)
    (hf_sep : f = separableCoordinateFunctionSum fFamily)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (hfFamily_closed : ∀ j : Fin n, ClosedConvexFunction (scalarCoordinateLift (fFamily j)))
    (hfFamily_proper :
      ∀ j : Fin n,
        ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) (scalarCoordinateLift (fFamily j)))
    (L : Submodule ℝ (Fin n → ℝ)) :
    SubspaceFenchelApplicationStatement f L ∧
      (∀ xStar : Fin n → ℝ,
        fenchelConjugate n f xStar = separableCoordinateConjugateSum fFamily xStar) ∧
      SeparableSubspaceFenchelApplicationStatement fFamily L := by
  subst f
  have hconj (xStar : Fin n → ℝ) :
      fenchelConjugate n (separableCoordinateFunctionSum fFamily) xStar =
        separableCoordinateConjugateSum fFamily xStar :=
    fenchelConjugate_separableCoordinateFunctionSum fFamily hfFamily_proper xStar
  have hsubspace :
      SubspaceFenchelApplicationStatement (separableCoordinateFunctionSum fFamily) L := by
    simpa [SubspaceFenchelApplicationStatement] using
      (fenchel_duality_subspace_corollary
        (separableCoordinateFunctionSum fFamily) hf_proper hf_closed L)
  refine ⟨hsubspace, hconj, ?_⟩
  have hsubgrad (x xStar : Fin n → ℝ) :
      dotProductEquiv ℝ (Fin n) xStar ∈
          subdifferentialAt (separableCoordinateFunctionSum fFamily) x ↔
        ∀ j : Fin n, (x j, xStar j) ∈ scalarSubdifferentialGraph (fFamily j) := by
    exact euclideanSubgradient_separableCoordinateFunctionSum_iff
      fFamily hf_proper hfFamily_proper x xStar
  have hconj_fun :
      fenchelConjugate n (separableCoordinateFunctionSum fFamily) =
        separableCoordinateConjugateSum fFamily := by
    funext xStar
    exact hconj xStar
  unfold SubspaceFenchelApplicationStatement at hsubspace
  unfold SeparableSubspaceFenchelApplicationStatement
  rcases hsubspace with ⟨hstrong, hprimal, hdual, hkt⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hconj_fun, subspaceOrthogonalComplementSet] using hstrong
  · simpa only [hconj_fun, subspaceOrthogonalComplementSet] using hprimal
  · simpa only [hconj_fun, subspaceOrthogonalComplementSet] using hdual
  · intro x xStar
    constructor
    · rintro ⟨hxL, hxOrth, hfx, hpd, hd⟩
      have hold :
          x ∈ (L : Set (Fin n → ℝ)) ∧
            (∀ y ∈ (L : Set (Fin n → ℝ)), dotProduct xStar y = 0) ∧
            separableCoordinateFunctionSum fFamily x =
              functionInfimumEReal (fun y =>
                separableCoordinateFunctionSum fFamily y +
                  indicatorFunction (L : Set (Fin n → ℝ)) y) ∧
            functionInfimumEReal (fun y =>
                separableCoordinateFunctionSum fFamily y +
                  indicatorFunction (L : Set (Fin n → ℝ)) y) =
              -functionInfimumEReal (fun yStar =>
                fenchelConjugate n (separableCoordinateFunctionSum fFamily) yStar +
                  indicatorFunction
                    {zStar | ∀ y ∈ (L : Set (Fin n → ℝ)), dotProduct zStar y = 0}
                    yStar) ∧
            functionInfimumEReal (fun yStar =>
                fenchelConjugate n (separableCoordinateFunctionSum fFamily) yStar +
                  indicatorFunction
                    {zStar | ∀ y ∈ (L : Set (Fin n → ℝ)), dotProduct zStar y = 0}
                    yStar) =
              fenchelConjugate n (separableCoordinateFunctionSum fFamily) xStar := by
        simpa only [hconj_fun, subspaceOrthogonalComplementSet] using
          (⟨hxL, hxOrth, hfx, hpd, hd⟩)
      rcases (hkt x xStar).1 hold with ⟨hsg, hxL', hxOrth'⟩
      exact ⟨hxL', hxOrth', (hsubgrad x xStar).1 hsg⟩
    · rintro ⟨hxL, hxOrth, hcoord⟩
      have hold := (hkt x xStar).2
        ⟨(hsubgrad x xStar).2 hcoord, hxL, hxOrth⟩
      simpa only [hconj_fun, subspaceOrthogonalComplementSet] using hold

/-- The quadratic kernel `w(z) = |z|^2 / 2` used in Moreau's theorem. -/
noncomputable def moreauQuadraticKernel {n : ℕ} : (Fin n → ℝ) → EReal :=
  fun z => (((dotProduct z z) / 2 : ℝ) : EReal)

/-- The Moreau envelope `f □ w` obtained by infimal convolution with the quadratic kernel
`w(z) = |z|^2 / 2`. -/
noncomputable def quadraticMoreauEnvelope {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun z => functionInfimumEReal (fun x => f x + moreauQuadraticKernel (z - x))

/-- A vector `x` attains the infimum defining the quadratic Moreau envelope of `f` at `z`. -/
def AttainsQuadraticMoreauEnvelopeAt {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (z x : Fin n → ℝ) : Prop :=
  quadraticMoreauEnvelope (n := n) f z = f x + moreauQuadraticKernel (z - x)

/-- Helper for Theorem 31.5: the book's quadratic kernel is exactly the standard quadratic
Fenchel-self-conjugate function `quadraticHalfInner`. -/
lemma helperForTheorem_31_5_moreauQuadraticKernel_eq_quadraticHalfInner {n : ℕ} :
    moreauQuadraticKernel (n := n) = quadraticHalfInner n := by
  -- This is only an algebraic rewrite of `/ 2` into multiplication by `1 / 2`.
  funext z
  simp [moreauQuadraticKernel, quadraticHalfInner, div_eq_mul_inv, mul_comm]

/-- Helper for Theorem 31.5: the quadratic kernel is a proper convex function on all of `ℝ^n`. -/
lemma helperForTheorem_31_5_properConvex_moreauQuadraticKernel {n : ℕ} :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (moreauQuadraticKernel (n := n)) := by
  -- Realize the kernel as the diagonal quadratic with all weights equal to `1`.
  rw [helperForTheorem_31_5_moreauQuadraticKernel_eq_quadraticHalfInner]
  convert
      (properConvexFunctionOn_diagonalQuadratic (n := n) (d := fun _ : Fin n => (1 : ℝ))
        (hd := by
          intro i
          norm_num)) using 1
  -- The diagonal quadratic with unit weights is exactly `quadraticHalfInner`.
  funext x
  simp [quadraticHalfInner, dotProduct]
  ring_nf

/-- Helper for Theorem 31.5: every vector lies in the relative interior of the whole space. -/
lemma helperForTheorem_31_5_mem_euclideanRelativeInterior_univ {n : ℕ} (x : Fin n → ℝ) :
    x ∈ euclideanRelativeInterior_fin n (Set.univ : Set (Fin n → ℝ)) := by
  -- The relative interior of the ambient space is the ambient space itself.
  refine
    (mem_euclideanRelativeInterior_fin_iff
      (n := n) (C := (Set.univ : Set (Fin n → ℝ))) (x := x)).2 ?_
  have hImageUniv :
      ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm '' (Set.univ : Set (Fin n → ℝ))) =
        (Set.univ : Set (EuclideanSpace ℝ (Fin n))) := by
    ext y
    constructor
    · intro hy
      trivial
    · intro hy
      refine ⟨(EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)) y, by simp, ?_⟩
      simp
  rw [hImageUniv]
  unfold euclideanRelativeInterior
  refine ⟨by simp, 1, by norm_num, ?_⟩
  intro y hy
  trivial

/-- Helper for Theorem 31.5: the translated quadratic is finite everywhere, so its effective
domain is all of `ℝ^n`. -/
lemma helperForTheorem_31_5_effectiveDomain_translatedQuadratic_eq_univ {n : ℕ}
    (z : Fin n → ℝ) :
    effectiveDomain (Set.univ : Set (Fin n → ℝ))
      (fun x => moreauQuadraticKernel (n := n) (z - x)) = Set.univ := by
  -- The translated kernel is real-valued at every point, hence never equals `⊤`.
  ext x
  simp [effectiveDomain_eq, moreauQuadraticKernel]

/-- Helper for Theorem 31.5: negating the translated quadratic produces a proper concave
function, which is the concave datum used in Fenchel duality. -/
lemma helperForTheorem_31_5_properConcave_negTranslatedQuadratic {n : ℕ}
    (z : Fin n → ℝ) :
    ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => -moreauQuadraticKernel (n := n) (z - x)) := by
  -- Rewrite `z - x` as `(-x) - (-z)` so the translated-kernel lemma applies in the correct direction.
  have hPre :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => moreauQuadraticKernel (n := n) (-x)) := by
    simpa [moreauQuadraticKernel, quadraticHalfInner, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, dotProduct, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc] using
      (helperForTheorem_31_5_properConvex_moreauQuadraticKernel (n := n))
  -- Negating a translated proper convex function gives the required proper concave function.
  simpa [ProperConcaveFunctionOn, moreauQuadraticKernel, quadraticHalfInner, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc] using
    (properConvexFunctionOn_translate (n := n) (a := z)
      (f := fun x => moreauQuadraticKernel (n := n) (-x)) hPre)

/-- Helper for Theorem 31.5: the quadratic difference `w z - w (z - x⋆)` is the affine term
`⟪z, x⋆⟫ - w x⋆` obtained after conjugating the translated quadratic. -/
lemma helperForTheorem_31_5_quadraticDifference_eq_dotSub {n : ℕ}
    (z xStar : Fin n → ℝ) :
    ((dotProduct z xStar : ℝ) : EReal) - moreauQuadraticKernel (n := n) xStar =
      moreauQuadraticKernel (n := n) z - moreauQuadraticKernel (n := n) (z - xStar) := by
  -- Expand the translated square and compare the real quadratic coefficients.
  unfold moreauQuadraticKernel
  have hsq :
      dotProduct (z - xStar) (z - xStar) =
        dotProduct z z - dotProduct z xStar - dotProduct xStar z + dotProduct xStar xStar := by
    simp [dotProduct, sub_eq_add_neg, Finset.sum_add_distrib, mul_add, add_mul]
    ring_nf
  have hreal :
      (dotProduct z xStar : ℝ) - (dotProduct xStar xStar) / 2 =
        (dotProduct z z) / 2 - (dotProduct (z - xStar) (z - xStar)) / 2 := by
    rw [hsq, dotProduct_comm xStar z]
    ring
  exact_mod_cast hreal

/-- Helper for Theorem 31.5: the concave Fenchel conjugate of the negated translated quadratic is
the quadratic difference appearing in Moreau's identity. -/
lemma helperForTheorem_31_5_concaveConjugate_negTranslatedQuadratic {n : ℕ}
    (z xStar : Fin n → ℝ) :
    concaveFenchelConjugate (fun x => -moreauQuadraticKernel (n := n) (z - x)) xStar =
      moreauQuadraticKernel (n := n) z - moreauQuadraticKernel (n := n) (z - xStar) := by
  -- First rewrite `w (z - x)` as the translated form `w (x - z)` required by Chapter 16.
  have hsymm :
      ∀ x : Fin n → ℝ,
        moreauQuadraticKernel (n := n) (z - x) = moreauQuadraticKernel (n := n) (x - z) := by
    intro x
    unfold moreauQuadraticKernel
    congr 1
    simp [dotProduct, sub_eq_add_neg, Finset.sum_add_distrib, mul_add, add_mul]
    ring_nf
  have htranslateArg :
      (fun x : Fin n → ℝ => moreauQuadraticKernel (n := n) (z - x)) =
        (fun x : Fin n → ℝ => moreauQuadraticKernel (n := n) (x - z)) := by
    funext x
    exact hsymm x
  have hkernelNeg :
      moreauQuadraticKernel (n := n) (-xStar) = moreauQuadraticKernel (n := n) xStar := by
    -- The quadratic kernel is even, so evaluating at `-x⋆` changes nothing.
    unfold moreauQuadraticKernel
    congr 1
    simp [dotProduct]
  calc
    concaveFenchelConjugate (fun x => -moreauQuadraticKernel (n := n) (z - x)) xStar
        = -fenchelConjugate n (fun x => moreauQuadraticKernel (n := n) (z - x)) (-xStar) := by
            simp [concaveFenchelConjugate]
    _ = -fenchelConjugate n (fun x => moreauQuadraticKernel (n := n) (x - z)) (-xStar) := by
          rw [htranslateArg]
    _ =
        -(fenchelConjugate n (moreauQuadraticKernel (n := n)) (-xStar) +
            ((dotProduct z (-xStar) : ℝ) : EReal)) := by
          -- Apply the translation rule to the convex quadratic.
          rw [section16_fenchelConjugate_translate (h := moreauQuadraticKernel (n := n)) (a := z)]
    _ = -(fenchelConjugate n (quadraticHalfInner n) (-xStar) + ((dotProduct z (-xStar) : ℝ) : EReal)) := by
          rw [helperForTheorem_31_5_moreauQuadraticKernel_eq_quadraticHalfInner]
    _ = -(quadraticHalfInner n (-xStar) + ((dotProduct z (-xStar) : ℝ) : EReal)) := by
          -- The quadratic is Fenchel self-conjugate.
          rw [fenchelConjugate_quadraticHalfInner n]
    _ = -(moreauQuadraticKernel (n := n) xStar + ((dotProduct z (-xStar) : ℝ) : EReal)) := by
          -- Return from `quadraticHalfInner` to the Moreau kernel and use evenness.
          rw [← helperForTheorem_31_5_moreauQuadraticKernel_eq_quadraticHalfInner]
          simp [hkernelNeg]
    _ = ((dotProduct z xStar : ℝ) : EReal) - moreauQuadraticKernel (n := n) xStar := by
          -- Simplify the sign on the affine term, then rewrite the outer negation as subtraction.
          have hdot : ((dotProduct z (-xStar) : ℝ) : EReal) = -((dotProduct z xStar : ℝ) : EReal) := by
            norm_num [dotProduct]
          have hkernel_ne_bot : moreauQuadraticKernel (n := n) xStar ≠ (⊥ : EReal) := by
            simp [moreauQuadraticKernel]
          have hkernel_ne_top : moreauQuadraticKernel (n := n) xStar ≠ (⊤ : EReal) := by
            simp [moreauQuadraticKernel]
          rw [hdot]
          calc
            -(moreauQuadraticKernel (n := n) xStar + -((dotProduct z xStar : ℝ) : EReal)) =
                -moreauQuadraticKernel (n := n) xStar - (-((dotProduct z xStar : ℝ) : EReal)) := by
                  exact
                    EReal.neg_add
                      (x := moreauQuadraticKernel (n := n) xStar)
                      (y := -((dotProduct z xStar : ℝ) : EReal))
                      (Or.inl hkernel_ne_bot)
                      (Or.inl hkernel_ne_top)
            _ = ((dotProduct z xStar : ℝ) : EReal) - moreauQuadraticKernel (n := n) xStar := by
                  simp [sub_eq_add_neg, add_comm]
    _ = moreauQuadraticKernel (n := n) z - moreauQuadraticKernel (n := n) (z - xStar) := by
          -- Finish with the explicit quadratic identity.
          exact helperForTheorem_31_5_quadraticDifference_eq_dotSub (n := n) z xStar

/-- Helper for Theorem 31.5: properness gives relative-interior witnesses for both `dom f` and
`dom f⋆`, which are the qualification data used later for Fenchel duality and infimal
convolution. -/
lemma helperForTheorem_31_5_relativeInteriorWitnesses {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) :
    (∃ x0, x0 ∈ euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) ∧
      (∃ xStar0, xStar0 ∈ euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) := by
  have hconv : ConvexFunction f := by
    -- Properness packages convexity on all of `ℝ^n`.
    simpa [ConvexFunction] using hf_proper.1
  rcases hf_proper.2.1 with ⟨⟨x0, μ0⟩, hx0μ0⟩
  have hxlt : ∃ x : Fin n → ℝ, f x < ((μ0 + 1 : ℝ) : EReal) := by
    -- A finite epigraph point lets us choose a real level strictly above the sampled value.
    refine ⟨x0, ?_⟩
    exact lt_of_le_of_lt hx0μ0.2
      (by exact_mod_cast (show μ0 < μ0 + 1 by linarith))
  rcases exists_lt_on_ri_effectiveDomain_of_convexFunction
      (n := n) (f := f) hconv (α := μ0 + 1) hxlt with ⟨x, hxri, hxlt'⟩
  have hfStar_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper
  have hconvStar : ConvexFunction (fenchelConjugate n f) := by
    -- The conjugate of a proper convex function is again proper convex, hence convex.
    simpa [ConvexFunction] using hfStar_proper.1
  rcases hfStar_proper.2.1 with ⟨⟨xStar0, μStar0⟩, hxStar0μ0⟩
  have hxStarlt :
      ∃ xStar : Fin n → ℝ, fenchelConjugate n f xStar < ((μStar0 + 1 : ℝ) : EReal) := by
    -- Apply the same relative-interior argument to the conjugate.
    refine ⟨xStar0, ?_⟩
    exact lt_of_le_of_lt hxStar0μ0.2
      (by exact_mod_cast (show μStar0 < μStar0 + 1 by linarith))
  rcases exists_lt_on_ri_effectiveDomain_of_convexFunction
      (n := n) (f := fenchelConjugate n f) hconvStar (α := μStar0 + 1) hxStarlt with
    ⟨xStar, hxStarri, hxStarlt'⟩
  have hpreimageDomF :
      ((fun y : EuclideanSpace ℝ (Fin n) => (y : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) =
        ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm ''
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    ext y
    constructor
    · intro hy
      exact ⟨(y : Fin n → ℝ), hy, by simp⟩
    · rintro ⟨u, hu, rfl⟩
      simpa [Set.mem_preimage]
  have hpreimageDomFStar :
      ((fun y : EuclideanSpace ℝ (Fin n) => (y : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) =
        ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm ''
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f)) := by
    ext y
    constructor
    · intro hy
      exact ⟨(y : Fin n → ℝ), hy, by simp⟩
    · rintro ⟨u, hu, rfl⟩
      simpa [Set.mem_preimage]
  refine ⟨?_, ?_⟩
  · -- Convert the Euclidean-space relative-interior statement back to `Fin n → ℝ`.
    refine ⟨(x : Fin n → ℝ), ?_⟩
    exact
      (mem_euclideanRelativeInterior_fin_iff
        (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
        (x := (x : Fin n → ℝ))).2
        (by simpa [hpreimageDomF] using hxri)
  · -- The same coordinate conversion works for the conjugate domain.
    refine ⟨(xStar : Fin n → ℝ), ?_⟩
    exact
      (mem_euclideanRelativeInterior_fin_iff
        (n := n)
        (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))
        (x := (xStar : Fin n → ℝ))).2
        (by simpa [hpreimageDomFStar] using hxStarri)

/-- Helper for Theorem 31.5: the explicit formula for the concave conjugate of the negated
translated quadratic implies that its effective domain is all of `ℝ^n`. -/
lemma helperForTheorem_31_5_concaveConjugateEffectiveDomain_negTranslatedQuadratic_eq_univ
    {n : ℕ} (z : Fin n → ℝ) :
    concaveConjugateEffectiveDomain
      (fun x => -moreauQuadraticKernel (n := n) (z - x)) = Set.univ := by
  -- Rewrite the negated concave conjugate as a difference of two finite quadratic values.
  ext xStar
  have hKernelZ_ne_top : moreauQuadraticKernel (n := n) z ≠ (⊤ : EReal) := by
    simp [moreauQuadraticKernel]
  have hKernelZ_ne_bot : moreauQuadraticKernel (n := n) z ≠ (⊥ : EReal) := by
    simp [moreauQuadraticKernel]
  have hKernelSub_ne_top : moreauQuadraticKernel (n := n) (z - xStar) ≠ (⊤ : EReal) := by
    simp [moreauQuadraticKernel]
  have hKernelSub_ne_bot : moreauQuadraticKernel (n := n) (z - xStar) ≠ (⊥ : EReal) := by
    simp [moreauQuadraticKernel]
  have hNegKernelSub_ne_top : -moreauQuadraticKernel (n := n) (z - xStar) ≠ (⊤ : EReal) := by
    simpa using hKernelSub_ne_bot
  have hNegKernelSub_ne_bot : -moreauQuadraticKernel (n := n) (z - xStar) ≠ (⊥ : EReal) := by
    simpa using hKernelSub_ne_top
  have hvalue :
      -(concaveFenchelConjugate (fun x => -moreauQuadraticKernel (n := n) (z - x)) xStar) =
        moreauQuadraticKernel (n := n) (z - xStar) - moreauQuadraticKernel (n := n) z := by
    rw [helperForTheorem_31_5_concaveConjugate_negTranslatedQuadratic (n := n) z xStar]
    calc
      -(moreauQuadraticKernel (n := n) z - moreauQuadraticKernel (n := n) (z - xStar)) =
          -(moreauQuadraticKernel (n := n) z + -moreauQuadraticKernel (n := n) (z - xStar)) := by
            rfl
      _ = -moreauQuadraticKernel (n := n) z - (-moreauQuadraticKernel (n := n) (z - xStar)) := by
            exact
              EReal.neg_add
                (x := moreauQuadraticKernel (n := n) z)
                (y := -moreauQuadraticKernel (n := n) (z - xStar))
                (Or.inl hKernelZ_ne_bot) (Or.inl hKernelZ_ne_top)
      _ = moreauQuadraticKernel (n := n) (z - xStar) - moreauQuadraticKernel (n := n) z := by
            simp [sub_eq_add_neg, add_comm]
  -- That difference is always real-valued, so every `xStar` belongs to the effective domain.
  constructor
  · intro _
    simp
  · intro _
    simp [concaveConjugateEffectiveDomain, effectiveDomain_eq]
    change -concaveFenchelConjugate (fun x => -moreauQuadraticKernel (n := n) (z - x)) xStar < ⊤
    rw [hvalue]
    let t : ℝ :=
      (dotProduct (z - xStar) (z - xStar)) / 2 - (dotProduct z z) / 2
    have ht :
        ((t : ℝ) : EReal) =
          moreauQuadraticKernel (n := n) (z - xStar) - moreauQuadraticKernel (n := n) z := by
      simp [t, moreauQuadraticKernel, EReal.coe_sub]
    exact lt_top_iff_ne_top.2 (by
      intro htop
      have hEq : ((t : ℝ) : EReal) = (⊤ : EReal) := by simpa [ht] using htop
      exact EReal.coe_ne_top t hEq)

/-- Helper for Theorem 31.5: the Fenchel dual objective for the negated translated quadratic is
the displayed Moreau complement term. -/
lemma helperForTheorem_31_5_dualObjective_negTranslatedQuadratic {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (z xStar : Fin n → ℝ) :
    fenchelDualObjective (n := n) f
        (fun x => -moreauQuadraticKernel (n := n) (z - x)) xStar =
      moreauQuadraticKernel (n := n) z -
        (fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)) := by
  -- Substitute the explicit quadratic conjugate formula, then reassociate the `EReal` terms.
  rw [fenchelDualObjective, helperForTheorem_31_5_concaveConjugate_negTranslatedQuadratic,
    sub_eq_add_neg, sub_eq_add_neg]
  have hKernel_ne_top :
      moreauQuadraticKernel (n := n) (z - xStar) ≠ (⊤ : EReal) := by
    simp [moreauQuadraticKernel]
  have hKernel_ne_bot :
      moreauQuadraticKernel (n := n) (z - xStar) ≠ (⊥ : EReal) := by
    simp [moreauQuadraticKernel]
  have hneg :
      -(fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)) =
        -fenchelConjugate n f xStar - moreauQuadraticKernel (n := n) (z - xStar) := by
    exact
      EReal.neg_add (x := fenchelConjugate n f xStar)
        (y := moreauQuadraticKernel (n := n) (z - xStar))
        (Or.inr hKernel_ne_top) (Or.inr hKernel_ne_bot)
  calc
    moreauQuadraticKernel (n := n) z + -moreauQuadraticKernel (n := n) (z - xStar) +
        -fenchelConjugate n f xStar =
      moreauQuadraticKernel (n := n) z +
        (-fenchelConjugate n f xStar - moreauQuadraticKernel (n := n) (z - xStar)) := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = moreauQuadraticKernel (n := n) z +
          -(fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)) := by
          rw [hneg]
    _ = moreauQuadraticKernel (n := n) z -
          (fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)) := by
          simp [sub_eq_add_neg]

/-- Helper for Theorem 31.5: the negated translated quadratic satisfies Fenchel's condition
`(b)` against every closed proper convex function `f`. -/
lemma helperForTheorem_31_5_conditionB_negTranslatedQuadratic {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_closed : ClosedConvexFunction f)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (z : Fin n → ℝ) :
    FenchelConditionB (n := n) f
      (fun x => -moreauQuadraticKernel (n := n) (z - x)) := by
  let g : (Fin n → ℝ) → EReal := fun x => -moreauQuadraticKernel (n := n) (z - x)
  have hg_proper :
      ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    -- The translated quadratic was already packaged as a proper concave datum.
    simpa [g] using
      helperForTheorem_31_5_properConcave_negTranslatedQuadratic (n := n) z
  have htranslated_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
        (fun x => moreauQuadraticKernel (n := n) (z - x)) := by
    -- Unfolding `ProperConcaveFunctionOn` removes the outer negation.
    simpa [g, ProperConcaveFunctionOn] using hg_proper
  have htranslated_convex :
      ConvexFunction (fun x => moreauQuadraticKernel (n := n) (z - x)) := by
    -- Properness on the whole space includes global convexity.
    simpa [ConvexFunction] using htranslated_proper.1
  have htranslated_finite :
      ∀ x : Fin n → ℝ,
        moreauQuadraticKernel (n := n) (z - x) ≠ (⊤ : EReal) ∧
          moreauQuadraticKernel (n := n) (z - x) ≠ (⊥ : EReal) := by
    -- The quadratic kernel is always a real value.
    intro x
    simp [moreauQuadraticKernel]
  have hg_closed : ClosedConcaveFunction g := by
    -- Closedness of the convex translated quadratic yields closedness of its negative.
    simpa [g, ClosedConcaveFunction] using
      (section13_closedProper_of_convex_finite
        (f := fun x => moreauQuadraticKernel (n := n) (z - x))
        (hf := htranslated_convex) htranslated_finite).1
  have hConjDom :
      concaveConjugateEffectiveDomain g = Set.univ := by
    -- Use the isolated domain computation for the translated quadratic conjugate.
    simpa [g] using
      helperForTheorem_31_5_concaveConjugateEffectiveDomain_negTranslatedQuadratic_eq_univ
        (n := n) z
  rcases helperForTheorem_31_5_relativeInteriorWitnesses (n := n) f hf_proper with
    ⟨_hx0, ⟨xStar0, hxStar0⟩⟩
  refine ⟨hf_closed, hg_closed, ?_⟩
  -- Any relative-interior point of `dom f⋆` also lies in `ri (dom g⋆)` because `dom g⋆ = ℝ^n`.
  refine ⟨xStar0, ?_, hxStar0⟩
  rw [hConjDom]
  exact helperForTheorem_31_5_mem_euclideanRelativeInterior_univ (n := n) xStar0

/-- Helper for Theorem 31.5: the Fenchel objects for the negated translated quadratic rewrite
exactly as the textbook Moreau-envelope quantities. -/
lemma helperForTheorem_31_5_fenchelObjects_rewrite_as_moreau {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (z : Fin n → ℝ) :
    let g : (Fin n → ℝ) → EReal := fun x => -moreauQuadraticKernel (n := n) (z - x)
    commonBookEffectiveDomainDifference f g =
        (fun x => f x + moreauQuadraticKernel (n := n) (z - x)) ∧
      fenchelPrimalInfimum f g = quadraticMoreauEnvelope (n := n) f z ∧
      (∀ xStar : Fin n → ℝ,
        fenchelDualObjective (n := n) f g xStar =
          moreauQuadraticKernel (n := n) z -
            (fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar))) ∧
      fenchelDualSupremum (n := n) f g =
        moreauQuadraticKernel (n := n) z -
          quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z := by
  let g : (Fin n → ℝ) → EReal := fun x => -moreauQuadraticKernel (n := n) (z - x)
  have hg_proper :
      ProperConcaveFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    -- Reuse the quadratic proper-concavity package to enter Theorem 31.1's syntax.
    simpa [g] using
      helperForTheorem_31_5_properConcave_negTranslatedQuadratic (n := n) z
  have hCommon :
      commonBookEffectiveDomainDifference f g =
        fun x => f x + moreauQuadraticKernel (n := n) (z - x) := by
    -- On the common effective domain the book's guarded objective is simply `f + w(z - ·)`.
    simpa [g, sub_eq_add_neg] using
      (helperForTheorem_31_1_commonBookEffectiveDomainDifference_eq_pointwise_sub_of_proper
        (n := n) f g hf_proper hg_proper)
  have hPrimal :
      fenchelPrimalInfimum f g = quadraticMoreauEnvelope (n := n) f z := by
    -- After the pointwise rewrite, the primal infimum is exactly the Moreau envelope.
    simp [fenchelPrimalInfimum, quadraticMoreauEnvelope, hCommon]
  have hDualObj :
      ∀ xStar : Fin n → ℝ,
        fenchelDualObjective (n := n) f g xStar =
          moreauQuadraticKernel (n := n) z -
            (fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)) := by
    intro xStar
    -- Use the isolated pointwise normalization of the dual objective.
    simpa [g] using
      helperForTheorem_31_5_dualObjective_negTranslatedQuadratic (n := n) f z xStar
  have hDualSup :
      fenchelDualSupremum (n := n) f g =
        moreauQuadraticKernel (n := n) z -
          quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z := by
    let c : ℝ := (dotProduct z z) / 2
    let candidate : (Fin n → ℝ) → EReal :=
      fun xStar =>
        fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)
    have hc : ((c : EReal)) = moreauQuadraticKernel (n := n) z := by
      simp [c, moreauQuadraticKernel]
    calc
      fenchelDualSupremum (n := n) f g
          = iSup (fun xStar => ((c : EReal) + -(candidate xStar))) := by
              unfold fenchelDualSupremum
              refine iSup_congr ?_
              intro xStar
              rw [hDualObj xStar, hc]
              simp [candidate, sub_eq_add_neg]
      _ = ((c : EReal) + iSup (fun xStar => -(candidate xStar))) := by
            symm
            exact
              helperForTheorem_6_30_15_real_add_iSup (c := c)
                (f := fun xStar => -(candidate xStar))
      _ = ((c : EReal) + -(iInf candidate)) := by
            rw [ereal_iSup_neg_eq_neg_iInf]
      _ = ((c : EReal) - functionInfimumEReal candidate) := by
            simp [functionInfimumEReal, sub_eq_add_neg]
      _ = moreauQuadraticKernel (n := n) z -
            quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z := by
            simp [candidate, hc, quadraticMoreauEnvelope]
  exact ⟨hCommon, hPrimal, hDualObj, hDualSup⟩

/-- Helper for Theorem 31.5: subtracting the same finite Moreau-kernel value from two `EReal`
expressions is cancellable. -/
lemma helperForTheorem_31_5_cancel_sub_eq_of_moreauKernel {n : ℕ} {z : Fin n → ℝ}
    {a b : EReal}
    (h :
      moreauQuadraticKernel (n := n) z - a =
        moreauQuadraticKernel (n := n) z - b) :
    a = b := by
  -- Split on whether `a` or `b` is infinite. The finite quadratic kernel cannot hide the
  -- difference between `⊤`, `⊥`, and a real value.
  by_cases hTopA : a = (⊤ : EReal)
  · have hrhs : moreauQuadraticKernel (n := n) z - b = (⊥ : EReal) := by
      simpa [hTopA] using h.symm
    by_cases hTopB : b = (⊤ : EReal)
    · simpa [hTopA, hTopB]
    · by_cases hBotB : b = (⊥ : EReal)
      · simp [hBotB, moreauQuadraticKernel] at hrhs
      · rcases
          section14_eq_coe_of_lt_top (z := b) (lt_top_iff_ne_top.2 hTopB) hBotB with
          ⟨r, rfl⟩
        exfalso
        have hEq : ((((dotProduct z z) / 2 - r : ℝ) : EReal) = (⊥ : EReal)) := by
          simpa [moreauQuadraticKernel, EReal.coe_sub] using hrhs
        exact EReal.coe_ne_bot _ hEq
  · by_cases hBotA : a = (⊥ : EReal)
    · have hrhs : moreauQuadraticKernel (n := n) z - b = (⊤ : EReal) := by
        simpa [hBotA] using h.symm
      by_cases hBotB : b = (⊥ : EReal)
      · simpa [hBotA, hBotB]
      · by_cases hTopB : b = (⊤ : EReal)
        · simp [hTopB, moreauQuadraticKernel] at hrhs
        · rcases
            section14_eq_coe_of_lt_top (z := b) (lt_top_iff_ne_top.2 hTopB) hBotB with
            ⟨r, rfl⟩
          exfalso
          have hEq : ((((dotProduct z z) / 2 - r : ℝ) : EReal) = (⊤ : EReal)) := by
            simpa [moreauQuadraticKernel, EReal.coe_sub] using hrhs
          exact EReal.coe_ne_top _ hEq
    · by_cases hTopB : b = (⊤ : EReal)
      · have hlhs : moreauQuadraticKernel (n := n) z - a = (⊥ : EReal) := by
          simpa [hTopB] using h
        rcases section14_eq_coe_of_lt_top (z := a) (lt_top_iff_ne_top.2 hTopA) hBotA with
          ⟨r, rfl⟩
        exfalso
        have hEq : ((((dotProduct z z) / 2 - r : ℝ) : EReal) = (⊥ : EReal)) := by
          simpa [moreauQuadraticKernel, EReal.coe_sub] using hlhs
        exact EReal.coe_ne_bot _ hEq
      · by_cases hBotB : b = (⊥ : EReal)
        · have hlhs : moreauQuadraticKernel (n := n) z - a = (⊤ : EReal) := by
            simpa [hBotB] using h
          rcases section14_eq_coe_of_lt_top (z := a) (lt_top_iff_ne_top.2 hTopA) hBotA with
            ⟨r, rfl⟩
          exfalso
          have hEq : ((((dotProduct z z) / 2 - r : ℝ) : EReal) = (⊤ : EReal)) := by
            simpa [moreauQuadraticKernel, EReal.coe_sub] using hlhs
          exact EReal.coe_ne_top _ hEq
        · rcases section14_eq_coe_of_lt_top (z := a) (lt_top_iff_ne_top.2 hTopA) hBotA with
            ⟨ra, rfl⟩
          rcases section14_eq_coe_of_lt_top (z := b) (lt_top_iff_ne_top.2 hTopB) hBotB with
            ⟨rb, rfl⟩
          -- In the finite-finite case the equality is just equality of real differences.
          have hrealE :
              ((((dotProduct z z) / 2 : ℝ) - ra : ℝ) : EReal) =
                ((((dotProduct z z) / 2 : ℝ) - rb : ℝ) : EReal) := by
            simpa [moreauQuadraticKernel] using h
          have hreal :
              ((dotProduct z z) / 2 : ℝ) - ra = ((dotProduct z z) / 2 : ℝ) - rb :=
            EReal.coe_eq_coe_iff.mp hrealE
          have hrab : ra = rb := by
            linarith [hreal]
          simpa [hrab]

/-- Helper for Theorem 31.5: the quadratic kernel expands additively with the Euclidean cross
term. -/
lemma helperForTheorem_31_5_moreauQuadraticKernel_add {n : ℕ}
    (u v : Fin n → ℝ) :
    moreauQuadraticKernel (n := n) (u + v) =
      moreauQuadraticKernel (n := n) u + ((dotProduct u v : ℝ) : EReal) +
        moreauQuadraticKernel (n := n) v := by
  -- Expand the square `|u + v|²` and collect the mixed term `⟪u, v⟫`.
  unfold moreauQuadraticKernel
  have hreal :
      dotProduct (u + v) (u + v) / 2 =
        dotProduct u u / 2 + dotProduct u v + dotProduct v v / 2 := by
    simp [dotProduct, Finset.sum_add_distrib, mul_add, add_mul]
    have hcross : (∑ x, v x * u x) = ∑ x, u x * v x := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    rw [hcross]
    ring_nf
  exact_mod_cast hreal

/-- Helper for Theorem 31.5: the quadratic completion identity isolates the nonnegative remainder
measuring the failure of `z = x + x⋆`. -/
lemma helperForTheorem_31_5_quadratic_sum_eq_kernel_plus_remainder {n : ℕ}
    (z x xStar : Fin n → ℝ) :
    ((dotProduct x xStar : ℝ) : EReal) +
        moreauQuadraticKernel (n := n) (z - x) +
        moreauQuadraticKernel (n := n) (z - xStar) =
      moreauQuadraticKernel (n := n) z +
        moreauQuadraticKernel (n := n) (z - x - xStar) := by
  -- Expand both quadratic terms and simplify the remaining bilinear expression.
  unfold moreauQuadraticKernel
  have hreal :
      dotProduct x xStar + dotProduct (z - x) (z - x) / 2 +
          dotProduct (z - xStar) (z - xStar) / 2 =
        dotProduct z z / 2 + dotProduct (z - x - xStar) (z - x - xStar) / 2 := by
    simp [dotProduct, sub_eq_add_neg, Finset.sum_add_distrib, mul_add, add_mul]
    have hcross : (∑ i, xStar i * x i) = ∑ i, x i * xStar i := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    rw [hcross]
    ring_nf
  exact_mod_cast hreal

/-- Helper for Theorem 31.5: the quadratic kernel is everywhere nonnegative. -/
lemma helperForTheorem_31_5_moreauQuadraticKernel_nonneg {n : ℕ}
    (u : Fin n → ℝ) :
    (0 : EReal) ≤ moreauQuadraticKernel (n := n) u := by
  -- The kernel is one-half of the nonnegative square norm.
  simpa [moreauQuadraticKernel] using
    (show (0 : ℝ) ≤ dotProduct u u / 2 by
      have hself : 0 ≤ dotProduct u u := dotProduct_self_nonneg (v := u)
      linarith)

/-- Helper for Theorem 31.5: the Moreau envelope is exactly the infimal convolution `f □ w`. -/
lemma helperForTheorem_31_5_quadraticMoreauEnvelope_eq_infimalConvolution {n : ℕ}
    (f : (Fin n → ℝ) → EReal) :
    quadraticMoreauEnvelope (n := n) f =
      infimalConvolution f (moreauQuadraticKernel (n := n)) := by
  -- Rewrite the `iInf` over `x` as the `sInf` over the corresponding infimal-convolution range.
  funext z
  rw [quadraticMoreauEnvelope, functionInfimumEReal]
  rw [show (⨅ x : Fin n → ℝ, f x + moreauQuadraticKernel (n := n) (z - x)) =
      sInf (Set.range (fun x : Fin n → ℝ => f x + moreauQuadraticKernel (n := n) (z - x))) by
      simpa using
        (sInf_range
          (f := fun x : Fin n → ℝ => f x + moreauQuadraticKernel (n := n) (z - x))).symm]
  unfold infimalConvolution
  congr 1
  ext a
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, z - x, by simp, rfl⟩
  · rintro ⟨x1, x2, hsum, rfl⟩
    refine ⟨x1, ?_⟩
    have hsub : z - x1 = x2 := by
      have h := congrArg (fun t : Fin n → ℝ => t - x1) hsum
      simpa using h.symm
    simpa [hsub]

/-- Helper for Theorem 31.5: for the negated translated quadratic, the concave Fenchel-Young
equality is exactly the decomposition equation `z = x + x⋆`. -/
lemma helperForTheorem_31_5_concaveFenchelYoung_negTranslatedQuadratic_iff_sum {n : ℕ}
    (z x xStar : Fin n → ℝ) :
    ConcaveFenchelYoungEqualityAt
      (fun y : Fin n → ℝ => -moreauQuadraticKernel (n := n) (z - y)) x xStar ↔
      z = x + xStar := by
  rw [ConcaveFenchelYoungEqualityAt]
  rw [helperForTheorem_31_5_concaveConjugate_negTranslatedQuadratic (n := n) z xStar]
  constructor
  · intro hEq
    -- Move the translated quadratic terms to the right so the completion identity can be applied.
    have hEq' :
        ((dotProduct x xStar : ℝ) : EReal) + moreauQuadraticKernel (n := n) (z - x) +
            moreauQuadraticKernel (n := n) (z - xStar) =
          moreauQuadraticKernel (n := n) z := by
      have hEqReal :
          -((dotProduct (z - x) (z - x)) / 2 : ℝ) +
              ((dotProduct z z) / 2 - (dotProduct (z - xStar) (z - xStar)) / 2) =
            dotProduct x xStar := by
        have hEqE :
            (((-((dotProduct (z - x) (z - x)) / 2 : ℝ) +
                ((dotProduct z z) / 2 - (dotProduct (z - xStar) (z - xStar)) / 2) : ℝ) :
                EReal)) =
              ((dotProduct x xStar : ℝ) : EReal) := by
          simpa [moreauQuadraticKernel, sub_eq_add_neg] using hEq
        exact EReal.coe_eq_coe_iff.mp hEqE
      have hEqReal' :
          dotProduct x xStar + dotProduct (z - x) (z - x) / 2 +
              dotProduct (z - xStar) (z - xStar) / 2 =
            dotProduct z z / 2 := by
        linarith
      change
        (((dotProduct x xStar + dotProduct (z - x) (z - x) / 2 +
            dotProduct (z - xStar) (z - xStar) / 2 : ℝ) : EReal) =
          (((dotProduct z z / 2 : ℝ)) : EReal))
      exact_mod_cast hEqReal'
    have hQuad :=
      helperForTheorem_31_5_quadratic_sum_eq_kernel_plus_remainder (n := n) z x xStar
    rw [hEq'] at hQuad
    have hZero : moreauQuadraticKernel (n := n) (z - x - xStar) = 0 := by
      have hQuadReal :
          (dotProduct z z) / 2 =
            (dotProduct z z) / 2 +
              (dotProduct (z - x - xStar) (z - x - xStar)) / 2 := by
        have hQuadE :
            ((((dotProduct z z) / 2 : ℝ) : EReal)) =
              (((dotProduct z z / 2 +
                  dotProduct (z - x - xStar) (z - x - xStar) / 2 : ℝ) : EReal)) := by
          simpa [moreauQuadraticKernel] using hQuad
        exact EReal.coe_eq_coe_iff.mp hQuadE
      have hzeroReal :
          (dotProduct (z - x - xStar) (z - x - xStar)) / 2 = (0 : ℝ) := by
        linarith [hQuadReal]
      change ((((dotProduct (z - x - xStar) (z - x - xStar)) / 2 : ℝ) : EReal)) = 0
      exact_mod_cast hzeroReal
    -- Vanishing of the nonnegative quadratic remainder forces the decomposition equation.
    have hZeroReal : z - x - xStar = 0 := by
      have hrealE :
          ((((dotProduct (z - x - xStar) (z - x - xStar)) / 2 : ℝ) : EReal)) = (0 : EReal) := by
        simpa [moreauQuadraticKernel] using hZero
      have hreal :
          (dotProduct (z - x - xStar) (z - x - xStar)) / 2 = (0 : ℝ) :=
        EReal.coe_eq_coe_iff.mp hrealE
      have hself : dotProduct (z - x - xStar) (z - x - xStar) = 0 := by
        linarith
      exact dotProduct_self_eq_zero.mp hself
    have hsum : z = x + xStar := by
      have := congrArg (fun t : Fin n → ℝ => t + x + xStar) hZeroReal
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using this
    exact hsum
  · intro hSum
    subst hSum
    -- After substituting `z = x + x⋆`, the translated quadratic terms collapse to `w x⋆` and `w x`.
    have hxsub : x + xStar - x = xStar := by
      ext i
      simp
    have hxs : x + xStar - xStar = x := by
      ext i
      simp
    rw [hxsub, hxs]
    have hQuad := helperForTheorem_31_5_moreauQuadraticKernel_add (n := n) x xStar
    rw [hQuad]
    have hreal :
        -((dotProduct xStar xStar) / 2 : ℝ) +
            ((dotProduct x x / 2 + dotProduct x xStar + dotProduct xStar xStar / 2) -
              dotProduct x x / 2) =
          dotProduct x xStar := by
      ring
    have hE :
        (((-((dotProduct xStar xStar) / 2 : ℝ) +
            ((dotProduct x x / 2 + dotProduct x xStar + dotProduct xStar xStar / 2) -
              dotProduct x x / 2) : ℝ) : EReal)) =
          ((dotProduct x xStar : ℝ) : EReal) := by
      exact_mod_cast hreal
    simpa [moreauQuadraticKernel, sub_eq_add_neg] using hE

/-- Helper for Theorem 31.5: simultaneous primal and dual Moreau attainers force the textbook
graph decomposition `z = x + x⋆` together with `x⋆ ∈ ∂f(x)`. -/
lemma helperForTheorem_31_5_attainers_imply_graphDecomposition {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf_proper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f)
    (z x xStar : Fin n → ℝ)
    (hMoreauIdentity :
      quadraticMoreauEnvelope (n := n) f z +
          quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z =
        moreauQuadraticKernel (n := n) z)
    (hPrimalAttain : AttainsQuadraticMoreauEnvelopeAt (n := n) f z x)
    (hDualAttain :
      AttainsQuadraticMoreauEnvelopeAt (n := n) (fenchelConjugate n f) z xStar) :
    z = x + xStar ∧
      dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x := by
  let w1 : ℝ := dotProduct (z - x) (z - x) / 2
  let w2 : ℝ := dotProduct (z - xStar) (z - xStar) / 2
  let wz : ℝ := dotProduct z z / 2
  let wRem : ℝ := dotProduct (z - x - xStar) (z - x - xStar) / 2
  -- First rewrite the simultaneous attainment equations into a single equality of finite values.
  have hValueEq :
      f x + fenchelConjugate n f xStar +
          (moreauQuadraticKernel (n := n) (z - x) +
            moreauQuadraticKernel (n := n) (z - xStar)) =
        moreauQuadraticKernel (n := n) z := by
    calc
      f x + fenchelConjugate n f xStar +
          (moreauQuadraticKernel (n := n) (z - x) +
            moreauQuadraticKernel (n := n) (z - xStar)) =
        (f x + moreauQuadraticKernel (n := n) (z - x)) +
          (fenchelConjugate n f xStar + moreauQuadraticKernel (n := n) (z - xStar)) := by
            simp [add_assoc, add_left_comm, add_comm]
      _ =
          quadraticMoreauEnvelope (n := n) f z +
            quadraticMoreauEnvelope (n := n) (fenchelConjugate n f) z := by
              rw [hPrimalAttain, hDualAttain]
      _ = moreauQuadraticKernel (n := n) z := hMoreauIdentity
  have hfx_ne_bot : f x ≠ (⊥ : EReal) :=
    hf_proper.2.2 x (by simp)
  have hfStar_proper :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hf_proper
  have hfxStar_ne_bot : fenchelConjugate n f xStar ≠ (⊥ : EReal) :=
    hfStar_proper.2.2 xStar (by simp)
  have hfx_ne_top : f x ≠ (⊤ : EReal) := by
    intro hTop
    have hLeftTop :
        f x + fenchelConjugate n f xStar +
            (moreauQuadraticKernel (n := n) (z - x) +
              moreauQuadraticKernel (n := n) (z - xStar)) =
          (⊤ : EReal) := by
      calc
        f x + fenchelConjugate n f xStar +
            (moreauQuadraticKernel (n := n) (z - x) +
              moreauQuadraticKernel (n := n) (z - xStar)) =
          (⊤ : EReal) + fenchelConjugate n f xStar +
            (moreauQuadraticKernel (n := n) (z - x) +
              moreauQuadraticKernel (n := n) (z - xStar)) := by
                rw [hTop]
        _ = (⊤ : EReal) +
              (moreauQuadraticKernel (n := n) (z - x) +
                moreauQuadraticKernel (n := n) (z - xStar)) := by
              rw [EReal.top_add_of_ne_bot hfxStar_ne_bot]
        _ = (⊤ : EReal) := by
              have hsum_ne_bot :
                  moreauQuadraticKernel (n := n) (z - x) +
                      moreauQuadraticKernel (n := n) (z - xStar) ≠ (⊥ : EReal) := by
                simp [moreauQuadraticKernel]
              rw [EReal.top_add_of_ne_bot hsum_ne_bot]
    have hTopEq : moreauQuadraticKernel (n := n) z = (⊤ : EReal) := by
      exact hValueEq.symm.trans hLeftTop
    simp [moreauQuadraticKernel] at hTopEq
  have hfxStar_ne_top : fenchelConjugate n f xStar ≠ (⊤ : EReal) := by
    intro hTop
    have hLeftTop :
        f x + fenchelConjugate n f xStar +
            (moreauQuadraticKernel (n := n) (z - x) +
              moreauQuadraticKernel (n := n) (z - xStar)) =
          (⊤ : EReal) := by
      calc
        f x + fenchelConjugate n f xStar +
            (moreauQuadraticKernel (n := n) (z - x) +
              moreauQuadraticKernel (n := n) (z - xStar)) =
          f x + (⊤ : EReal) +
            (moreauQuadraticKernel (n := n) (z - x) +
              moreauQuadraticKernel (n := n) (z - xStar)) := by
                rw [hTop]
        _ = (⊤ : EReal) +
              (moreauQuadraticKernel (n := n) (z - x) +
                moreauQuadraticKernel (n := n) (z - xStar)) := by
              rw [EReal.add_top_of_ne_bot hfx_ne_bot]
        _ = (⊤ : EReal) := by
              have hsum_ne_bot :
                  moreauQuadraticKernel (n := n) (z - x) +
                      moreauQuadraticKernel (n := n) (z - xStar) ≠ (⊥ : EReal) := by
                simp [moreauQuadraticKernel]
              rw [EReal.top_add_of_ne_bot hsum_ne_bot]
    have hTopEq : moreauQuadraticKernel (n := n) z = (⊤ : EReal) := by
      exact hValueEq.symm.trans hLeftTop
    simp [moreauQuadraticKernel] at hTopEq
  rcases section14_eq_coe_of_lt_top (z := f x) (lt_top_iff_ne_top.2 hfx_ne_top) hfx_ne_bot with
    ⟨fx, hfx⟩
  rcases
      section14_eq_coe_of_lt_top (z := fenchelConjugate n f xStar)
        (lt_top_iff_ne_top.2 hfxStar_ne_top) hfxStar_ne_bot with
    ⟨fxStar, hfxStar⟩
  -- Convert the Moreau equality and the quadratic completion identity to real equalities.
  have hValueEqReal :
      fx + fxStar + w1 + w2 = wz := by
    have hValueEqE :
        ((((fx + fxStar + w1 + w2 : ℝ) : EReal))) =
          (((wz : ℝ) : EReal)) := by
      simpa [hfx, hfxStar, moreauQuadraticKernel, w1, w2, wz, add_assoc, add_left_comm, add_comm]
        using hValueEq
    exact EReal.coe_eq_coe_iff.mp hValueEqE
  have hQuadReal :
      dotProduct x xStar + w1 + w2 = wz + wRem := by
    have hQuad :=
      helperForTheorem_31_5_quadratic_sum_eq_kernel_plus_remainder (n := n) z x xStar
    have hQuadE :
        ((((dotProduct x xStar + w1 + w2 : ℝ) : EReal))) =
          (((wz + wRem : ℝ) : EReal)) := by
      simpa [moreauQuadraticKernel, w1, w2, wz, wRem] using hQuad
    exact EReal.coe_eq_coe_iff.mp hQuadE
  have hFenchelLeE :
      (((dotProduct x xStar : ℝ) : EReal)) ≤ f x + fenchelConjugate n f xStar :=
    fenchel_inequality n f hf_proper x xStar
  have hFenchelLe :
      dotProduct x xStar ≤ fx + fxStar := by
    have hFenchelLeE' :
        (((dotProduct x xStar : ℝ) : EReal)) ≤ (((fx + fxStar : ℝ) : EReal)) := by
      simpa [hfx, hfxStar] using hFenchelLeE
    exact EReal.coe_le_coe_iff.mp hFenchelLeE'
  have hRemNonneg : 0 ≤ wRem := by
    dsimp [wRem]
    have hself : 0 ≤ dotProduct (z - x - xStar) (z - x - xStar) := dotProduct_self_nonneg _
    linarith
  have hDotEqPlusRem : dotProduct x xStar = fx + fxStar + wRem := by
    linarith [hValueEqReal, hQuadReal]
  have hRemZero : wRem = 0 := by
    linarith [hFenchelLe, hRemNonneg, hDotEqPlusRem]
  have hFenchelEqReal : fx + fxStar = dotProduct x xStar := by
    linarith [hDotEqPlusRem, hRemZero]
  have hFenchelEq :
      FenchelYoungEqualityAt f x xStar := by
    rw [FenchelYoungEqualityAt, hfx, hfxStar]
    exact_mod_cast hFenchelEqReal
  -- The quadratic completion identity now becomes the concave Fenchel-Young equality for `-w(z-·)`.
  have hConcaveEq :
      ConcaveFenchelYoungEqualityAt
        (fun y : Fin n → ℝ => -moreauQuadraticKernel (n := n) (z - y)) x xStar := by
    rw [ConcaveFenchelYoungEqualityAt]
    rw [helperForTheorem_31_5_concaveConjugate_negTranslatedQuadratic (n := n) z xStar]
    have hConcaveReal : -w1 + (wz - w2) = dotProduct x xStar := by
      linarith [hValueEqReal, hFenchelEqReal]
    have hConcaveE :
        (((-w1 + (wz - w2) : ℝ) : EReal)) = ((dotProduct x xStar : ℝ) : EReal) := by
      exact_mod_cast hConcaveReal
    simpa [moreauQuadraticKernel, w1, w2, wz] using hConcaveE
  have hSum : z = x + xStar :=
    (helperForTheorem_31_5_concaveFenchelYoung_negTranslatedQuadratic_iff_sum
      (n := n) z x xStar).1 hConcaveEq
  have hSub :
      IsEuclideanSubgradientAt f x xStar :=
    (fenchelYoung_inequality_and_eq_iff_mem_subdifferential
      (g := f) hf_proper x xStar).2.1 (by simpa [FenchelYoungEqualityAt] using hFenchelEq)
  exact ⟨hSum, by simpa [IsEuclideanSubgradientAt] using hSub⟩

end Section31
end Chap06
