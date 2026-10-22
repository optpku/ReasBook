/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section35_part9

section Chap07
section Section35

attribute [local instance] Classical.propDecidable
open scoped Pointwise

/-- The second-variable directional derivative function attached to a saddle kernel at `(u, v)`,
defined by `v' ↦ K'(u, v; 0, v')` using the infimum of all admissible directional-derivative
values. -/
noncomputable def secondVariableDirectionalDerivativeFunction {m n : ℕ}
    (K : (Fin m → ℝ) → (Fin n → ℝ) → EReal) (u : Fin m → ℝ) (v : Fin n → ℝ) :
    (Fin n → ℝ) → EReal :=
  fun v' => sInf {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L}

/-- Helper for Text 35.6.7: the textbook second-variable directional-derivative function is
exactly the ordinary upper directional derivative of the convex slice `v' ↦ K u v'` at `v`. -/
lemma helperForText_35_6_7_secondVariableDirectionalDerivative_eq_upperDirectionalDerivative
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) :
    secondVariableDirectionalDerivativeFunction K u v =
      upperDirectionalDerivativeAt (K u) v := by
  funext v'
  let g : (Fin n → ℝ) → EReal := K u
  let S : Set EReal := {L : EReal | IsSaddleDirectionalDerivativeAt K u v 0 v' L}
  have hg : ConvexFunction g := by
    -- Fixing the first variable leaves the second slice convex by the saddle hypothesis.
    simpa [g] using hSaddle.2 u
  have hright :
      Filter.Tendsto
        (directionalDifferenceQuotientAt g v v')
        (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
        (nhds (upperDirectionalDerivativeAt g v v')) :=
    -- The Chapter 23 directional derivative of the slice exists at the finite base point `v`.
    (convex_directionalDerivative_monotone_exists_and_sublinear g hg v hFinite).1 v' |>.2.1
  have hEventuallyEq :
      (fun t : ℝ => saddleDirectionalDifferenceQuotientAt K u v 0 v' t) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))]
        directionalDifferenceQuotientAt g v v' := by
    -- With zero first-direction component, the saddle quotient is exactly the slice quotient.
    filter_upwards with t
    simp [g, directionalDifferenceQuotientAt, saddleDirectionalDifferenceQuotientAt]
  have hmem : upperDirectionalDerivativeAt g v v' ∈ S := by
    -- The slice derivative supplies a concrete witness for the infimum defining `ψ(v')`.
    refine ⟨hFinite.1, hFinite.2, ?_⟩
    simpa [S] using Filter.Tendsto.congr' hEventuallyEq.symm hright
  have hunique : ∀ L ∈ S, L = upperDirectionalDerivativeAt g v v' := by
    intro L hL
    rcases hL with ⟨_, _, hLlim⟩
    -- Limits of the same quotient family are unique, so every admissible derivative value agrees.
    exact tendsto_nhds_unique hLlim (Filter.Tendsto.congr' hEventuallyEq.symm hright)
  have hS_nonempty : S.Nonempty := ⟨upperDirectionalDerivativeAt g v v', hmem⟩
  have hsInf_eq : sInf S = upperDirectionalDerivativeAt g v v' := by
    -- The defining set is a singleton up to equality, so its infimum is that unique value.
    refine le_antisymm ?_ ?_
    · exact sInf_le hmem
    · exact le_csInf hS_nonempty (by intro L hL; rw [hunique L hL])
  -- Rewrite the textbook `ψ(v')` to the slice directional derivative value.
  calc
    secondVariableDirectionalDerivativeFunction K u v v' = sInf S := by
      rfl
    _ = upperDirectionalDerivativeAt g v v' := hsInf_eq

/-- Helper for Text 35.6.7: membership in the Euclidean subdifferential of the convex second slice
`v' ↦ K u v'` is exactly membership in the textbook second partial subdifferential `∂₂ K(u, v)`. -/
lemma helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} {vStar : Fin n → ℝ} :
    dotProductEquiv ℝ (Fin n) vStar ∈ subdifferentialAt (K u) v ↔
      vStar ∈ partialSubdifferentialInSecondVariable K u v := by
  have hsumTransport : ∀ w : Fin n → ℝ,
      (((∑ i : Fin n, vStar i * (w i - v i) : ℝ)) : EReal) =
        ∑ i : Fin n, (((vStar i : ℝ) : EReal) * ((((w i - v i : ℝ)) : EReal))) := by
    intro w
    classical
    -- Expand the real sum term-by-term so it matches the `EReal` sum used in the file.
    refine Finset.induction_on Finset.univ ?_ ?_
    · simp
    · intro i s hi hs
      simp [hi, hs, EReal.coe_add, EReal.coe_mul]
  constructor
  · intro hv
    rw [mem_subdifferentialAt_iff] at hv
    intro v'
    -- The slice subgradient inequality is literally the textbook second-partial inequality.
    have hineq :
        K u v' ≥ K u v + ((dotProductEquiv ℝ (Fin n) vStar (v' - v) : ℝ) : EReal) := hv v'
    have hineq0 :
        K u v' ≥ K u v + (((∑ i : Fin n, vStar i * (v' i - v i) : ℝ)) : EReal) := by
      simpa [dotProductEquiv_apply_apply, dotProduct, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc, mul_comm, mul_left_comm, mul_assoc] using hineq
    have hineq' :
        K u v' ≥
          K u v + ∑ i : Fin n, (((vStar i : ℝ) : EReal) * ((((v' i - v i : ℝ)) : EReal))) := by
      simpa [hsumTransport (w := v')] using hineq0
    simpa [partialSubdifferentialInSecondVariable] using hineq'
  · intro hv
    rw [mem_subdifferentialAt_iff]
    intro v'
    -- Conversely, the textbook inequality is already the slice subgradient inequality.
    have hineq :
        K u v' ≥ K u v + (((∑ i : Fin n, vStar i * (v' i - v i) : ℝ)) : EReal) := by
      simpa [partialSubdifferentialInSecondVariable, hsumTransport (w := v')] using hv v'
    simpa [dotProductEquiv_apply_apply, dotProduct, sub_eq_add_neg, add_comm, add_left_comm,
      add_assoc, mul_comm, mul_left_comm, mul_assoc] using hineq

/-- Helper for Text 35.6.7: the Euclidean subdifferential of the slice `v' ↦ K u v'` at `v`
matches the textbook second partial subdifferential `∂₂ K(u, v)`. -/
lemma helperForText_35_6_7_partialSecond_eq_sliceSubdifferential
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} :
    ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (K u) v) =
      partialSubdifferentialInSecondVariable K u v := by
  ext vStar
  -- The set equality is just the pointwise equivalence between slice and textbook inequalities.
  exact helperForText_35_6_7_secondSliceSubgradient_iff_partialSecondMem
    (K := K) (u := u) (v := v) (vStar := vStar)

/-- Helper for Text 35.6.7: after identifying the slice subdifferential with `∂₂ K(u, v)`, the
Chapter 23 support value is exactly the textbook support function of the second partial
subdifferential. -/
lemma helperForText_35_6_7_sliceSupport_eq_secondPartialSupport
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} :
    subdifferentialSupportAt (K u) v =
      supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) := by
  funext v'
  -- Rewrite the Chapter 23 support through the Euclidean-coordinate representative of `∂₂ K(u,v)`.
  calc
    subdifferentialSupportAt (K u) v v' =
        supportFunctionEReal
          (((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (K u) v)) v' := by
      symm
      exact helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq (K u) v v'
    _ = supportFunctionEReal (partialSubdifferentialInSecondVariable K u v) v' := by
      rw [helperForText_35_6_7_partialSecond_eq_sliceSubdifferential
        (K := K) (u := u) (v := v)]
    _ = supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) v' := by
      rw [← helperForText_35_6_6_supportFunctionOfSet_eq_supportFunctionEReal]

/-- Helper for Text 35.6.7: nonemptiness of the textbook second partial subdifferential is
equivalent to nonemptiness of the Euclidean subdifferential of the convex second slice. -/
lemma helperForText_35_6_7_partialSecond_nonempty_iff_sliceSubdifferential_nonempty
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} :
    Set.Nonempty (partialSubdifferentialInSecondVariable K u v) ↔
      Set.Nonempty (subdifferentialAt (K u) v) := by
  constructor
  · rintro ⟨vStar, hvStar⟩
    refine ⟨dotProductEquiv ℝ (Fin n) vStar, ?_⟩
    -- Push the textbook witness through the dot-product equivalence into the slice subdifferential.
    have hpre :
        vStar ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (K u) v) := by
      simpa [helperForText_35_6_7_partialSecond_eq_sliceSubdifferential
        (K := K) (u := u) (v := v)] using hvStar
    simpa using hpre
  · rintro ⟨xStar, hxStar⟩
    refine ⟨(dotProductEquiv ℝ (Fin n)).symm xStar, ?_⟩
    -- Pull the Euclidean subgradient back to a vector witness for `∂₂ K(u, v)`.
    have hpre :
        (dotProductEquiv ℝ (Fin n)).symm xStar ∈
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (K u) v) := by
      simpa using hxStar
    simpa [helperForText_35_6_7_partialSecond_eq_sliceSubdifferential
      (K := K) (u := u) (v := v)] using hpre

/-- Helper for Text 35.6.7: emptiness of the textbook second partial subdifferential is
equivalent to emptiness of the Euclidean subdifferential of the convex second slice. -/
lemma helperForText_35_6_7_partialSecond_empty_iff_sliceSubdifferential_empty
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} :
    partialSubdifferentialInSecondVariable K u v = ∅ ↔
      subdifferentialAt (K u) v = ∅ := by
  constructor
  · intro hpartialEmpty
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro xStar hxStar
    have hsliceNonempty : Set.Nonempty (subdifferentialAt (K u) v) := ⟨xStar, hxStar⟩
    have hpartialNonempty :
        Set.Nonempty (partialSubdifferentialInSecondVariable K u v) :=
      (helperForText_35_6_7_partialSecond_nonempty_iff_sliceSubdifferential_nonempty
        (K := K) (u := u) (v := v)).2 hsliceNonempty
    rcases hpartialNonempty with ⟨vStar, hvStar⟩
    -- Any slice subgradient would transport back to a witness in `∂₂ K(u, v)`.
    simp [hpartialEmpty] at hvStar
  · intro hsliceEmpty
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro vStar hvStar
    have hpartialNonempty :
        Set.Nonempty (partialSubdifferentialInSecondVariable K u v) := ⟨vStar, hvStar⟩
    have hsliceNonempty :
        Set.Nonempty (subdifferentialAt (K u) v) :=
      (helperForText_35_6_7_partialSecond_nonempty_iff_sliceSubdifferential_nonempty
        (K := K) (u := u) (v := v)).1 hpartialNonempty
    rcases hsliceNonempty with ⟨xStar, hxStar⟩
    -- Conversely, any textbook second partial witness would produce a slice subgradient.
    simp [hsliceEmpty] at hxStar

/-- Helper for Text 35.6.7: if `∂₂ K(u, v)` is empty, then Theorem 23.3 produces a direction in
which the textbook directional derivative is `⊥`, while the opposite direction is `⊤`. -/
lemma helperForText_35_6_7_exists_bot_and_top_direction_of_empty_partialSecond
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInSecondVariable K u v = ∅) :
    ∃ w : Fin n → ℝ,
      secondVariableDirectionalDerivativeFunction K u v w = (⊥ : EReal) ∧
        secondVariableDirectionalDerivativeFunction K u v (-w) = (⊤ : EReal) := by
  let g : (Fin n → ℝ) → EReal := K u
  have hg : ConvexFunction g := by
    -- The saddle hypothesis makes the second slice convex.
    simpa [g] using hSaddle.2 u
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    -- The slice base point has exactly the finite value `K u v`.
    simpa [g] using hFinite
  have hsliceEmpty : subdifferentialAt g v = ∅ := by
    -- Empty textbook second partial subdifferential is the same as empty slice subdifferential.
    simpa [g] using
      (helperForText_35_6_7_partialSecond_empty_iff_sliceSubdifferential_empty
        (K := K) (u := u) (v := v)).1 hpartialEmpty
  have hsliceNotNonempty : ¬ Set.Nonempty (subdifferentialAt g v) := by
    exact Set.not_nonempty_iff_eq_empty.mpr hsliceEmpty
  rcases
      (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
        g hg v hgv).2 hsliceNotNonempty with
    ⟨⟨w, hwBot, hwTop⟩, _⟩
  have hpsiEq :
      secondVariableDirectionalDerivativeFunction K u v =
        upperDirectionalDerivativeAt g v := by
    -- Identify the textbook `ψ` with the ordinary slice directional derivative.
    simpa [g] using
      helperForText_35_6_7_secondVariableDirectionalDerivative_eq_upperDirectionalDerivative
        (K := K) hSaddle (u := u) (v := v) hFinite
  refine ⟨w, ?_, ?_⟩
  · -- Transport the `⊥` witness back to the textbook directional-derivative notation.
    simpa [hpsiEq] using hwBot
  · -- The same transport converts the opposite-direction `⊤` witness.
    simpa [hpsiEq] using hwTop

/-- Helper for Text 35.6.7: on the branch where `∂₂ K(u, v)` is nonempty, the textbook
lower-semicontinuous hull already matches the textbook support function. -/
lemma helperForText_35_6_7_saddleLowerHull_eq_secondPartialSupport_of_nonempty_partialSecond
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartial : Set.Nonempty (partialSubdifferentialInSecondVariable K u v)) :
    saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) =
      supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) := by
  let g : (Fin n → ℝ) → EReal := K u
  have hg : ConvexFunction g := by
    -- The saddle hypothesis gives convexity of the second slice directly.
    simpa [g] using hSaddle.2 u
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    -- The fixed slice still has the same finite base value `K u v`.
    simpa [g] using hFinite
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt g v
  have hpsiEq :
      secondVariableDirectionalDerivativeFunction K u v = D := by
    -- The textbook `ψ` is exactly the slice directional derivative.
    simpa [D, g] using
      helperForText_35_6_7_secondVariableDirectionalDerivative_eq_upperDirectionalDerivative
        (K := K) hSaddle (u := u) (v := v) hFinite
  have hsliceNonempty : Set.Nonempty (subdifferentialAt g v) :=
    (helperForText_35_6_7_partialSecond_nonempty_iff_sliceSubdifferential_nonempty
      (K := K) (u := u) (v := v)).1 hpartial
  calc
    saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) =
        epigraphClosureInf D := by
      rw [hpsiEq]
      rw [helperForText_35_6_6_saddleLowerHull_eq_epigraphClosureInf (φ := D)]
    _ = subdifferentialSupportAt g v := by
      -- On the honest branch, the Chapter 2 hull agrees with the Chapter 23 support formula.
      exact
        helperForText_35_6_6_epigraphClosureInf_eq_sliceSupport_of_nonempty_sliceSubdifferential
          (g := g) (x := v) hg hgv hsliceNonempty
    _ = supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) := by
      -- Translate the slice support back to the textbook second partial subdifferential.
      simpa [g] using
        helperForText_35_6_7_sliceSupport_eq_secondPartialSupport
          (K := K) (u := u) (v := v)

/-- Helper for Text 35.6.7: if `∂₂ K(u, v)` is empty, then its textbook support function is the
constant `⊥` function. -/
lemma helperForText_35_6_7_secondPartialSupport_eq_bot_of_empty_partialSecond
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hpartialEmpty : partialSubdifferentialInSecondVariable K u v = ∅) :
    supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) =
      fun _ => (⊥ : EReal) := by
  funext v'
  -- Once `∂₂ K(u, v)` is empty, the support supremum is over `∅`, hence equals `⊥`.
  simp [supportFunctionOfSet, hpartialEmpty]

/-- Helper for Text 35.6.7: Theorem 23.2 identifies the convex closure of the textbook
second-variable directional derivative with the support function of `∂₂ K(u, v)`. This is the
full dependency-closed Chapter 23 conclusion available before upgrading to the stronger
lower-semicontinuous hull. -/
lemma helperForText_35_6_7_convexFunctionClosure_eq_secondPartialSupport
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal)) :
    convexFunctionClosure (secondVariableDirectionalDerivativeFunction K u v) =
      supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) := by
  let g : (Fin n → ℝ) → EReal := K u
  have hg : ConvexFunction g := by
    -- The saddle hypothesis already makes the second slice convex.
    simpa [g] using hSaddle.2 u
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    -- The slice base point has the same finite value as `K u v`.
    simpa [g] using hFinite
  have hpsiEq :
      secondVariableDirectionalDerivativeFunction K u v =
        upperDirectionalDerivativeAt g v := by
    -- The textbook `ψ` is exactly the Chapter 23 directional derivative of the slice.
    simpa [g] using
      helperForText_35_6_7_secondVariableDirectionalDerivative_eq_upperDirectionalDerivative
        (K := K) hSaddle (u := u) (v := v) hFinite
  calc
    convexFunctionClosure (secondVariableDirectionalDerivativeFunction K u v) =
        convexFunctionClosure (upperDirectionalDerivativeAt g v) := by
      rw [hpsiEq]
    _ = subdifferentialSupportAt g v := by
      -- This is exactly the closure/support identity supplied by Theorem 23.2.
      simpa using
        (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
          g hg v hgv (0 : Module.Dual ℝ (Fin n → ℝ))).2.2.2
    _ = supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) := by
      -- Translate the slice support back to textbook second-partial coordinates.
      simpa [g] using
        helperForText_35_6_7_sliceSupport_eq_secondPartialSupport
          (K := K) (u := u) (v := v)

/-- Helper for Text 35.6.7: when `∂₂ K(u, v)` is empty, the correct dependency-closed Chapter 23
conclusion is that the convex closure of the textbook directional-derivative function is
constantly `⊥`. This still falls short of the stronger hull identity used in the blocked branch.
-/
lemma helperForText_35_6_7_convexFunctionClosure_eq_bot_of_empty_partialSecond
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInSecondVariable K u v = ∅) :
    convexFunctionClosure (secondVariableDirectionalDerivativeFunction K u v) =
      fun _ => (⊥ : EReal) := by
  rcases
      helperForText_35_6_7_exists_bot_and_top_direction_of_empty_partialSecond
        (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty with
    ⟨w, hwBot, _⟩
  -- A single `⊥` value forces the Chapter 2 convex closure to collapse to constant `⊥`.
  exact
    convexFunctionClosure_eq_bot_of_exists_bot
      (f := secondVariableDirectionalDerivativeFunction K u v) ⟨w, hwBot⟩

/-- Helper for Text 35.6.7: the saddle lower-semicontinuous hull of the textbook
directional-derivative slice `ψ` is exactly the ordinary lower semicontinuous hull. -/
lemma helperForText_35_6_7_saddleLowerHull_eq_lowerSemicontinuousHull
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u : Fin m → ℝ} {v : Fin n → ℝ} :
    saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) =
      lowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) := by
  -- First rewrite the saddle hull through the Chapter 2 epigraph-closure construction.
  calc
    saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) =
        epigraphClosureInf (secondVariableDirectionalDerivativeFunction K u v) := by
      rw [helperForText_35_6_6_saddleLowerHull_eq_epigraphClosureInf
        (φ := secondVariableDirectionalDerivativeFunction K u v)]
    _ = lowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) := by
      -- Then identify that epigraph hull with the standard lower semicontinuous hull.
      rw [helperForText_35_6_6_epigraphClosureInf_eq_lowerSemicontinuousHull
        (φ := secondVariableDirectionalDerivativeFunction K u v)]

/-- Helper for Text 35.6.7: on the empty `∂₂ K(u, v)` branch, the textbook target at a fixed
direction `v'` is equivalent to the missing upgrade from the saddle epigraph hull to the Chapter
23 convex closure. -/
lemma helperForText_35_6_7_emptyPartial_goal_iff_hull_eq_convexClosure
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInSecondVariable K u v = ∅)
    (v' : Fin n → ℝ) :
    saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
        supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) v' ↔
      saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
        convexFunctionClosure (secondVariableDirectionalDerivativeFunction K u v) v' := by
  -- The empty-partial branch collapses the textbook support side to `⊥`.
  rw [helperForText_35_6_7_secondPartialSupport_eq_bot_of_empty_partialSecond
    (K := K) (u := u) (v := v) hpartialEmpty]
  have hclosureBotAt :
      convexFunctionClosure (secondVariableDirectionalDerivativeFunction K u v) v' =
        (⊥ : EReal) := by
    -- Theorem 23.2 still forces the convex closure of `ψ` to be `⊥` on the empty branch.
    simpa using congrFun
      (helperForText_35_6_7_convexFunctionClosure_eq_bot_of_empty_partialSecond
        (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty) v'
  -- After both rewrites, the remaining equivalence is tautological.
  rw [hclosureBotAt]

/-- Helper for Text 35.6.7: after rewriting the saddle hull as the ordinary lower
semicontinuous hull, the empty-`∂₂ K(u, v)` branch of the textbook target at a fixed direction
`v'` is equivalent to the missing lower-hull/convex-closure upgrade. -/
lemma helperForText_35_6_7_emptyPartial_goal_iff_lowerHull_eq_convexClosure
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInSecondVariable K u v = ∅)
    (v' : Fin n → ℝ) :
    saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
        supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) v' ↔
      lowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
        convexFunctionClosure (secondVariableDirectionalDerivativeFunction K u v) v' := by
  have hreduce :
      saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
          supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) v' ↔
        saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
          convexFunctionClosure (secondVariableDirectionalDerivativeFunction K u v) v' :=
    helperForText_35_6_7_emptyPartial_goal_iff_hull_eq_convexClosure
      (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty v'
  have hhullEqAt :
      saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
        lowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' := by
    -- The Chapter 2 saddle hull is already the ordinary lower semicontinuous hull of `ψ`.
    simpa using congrFun
      (helperForText_35_6_7_saddleLowerHull_eq_lowerSemicontinuousHull
        (K := K) (u := u) (v := v)) v'
  constructor
  · intro htarget
    -- Reduce the textbook target to the saddle-hull/closure equality, then rewrite the hull.
    have hhullClosureAt :
        saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
          convexFunctionClosure (secondVariableDirectionalDerivativeFunction K u v) v' :=
      hreduce.mp htarget
    exact hhullEqAt.symm.trans hhullClosureAt
  · intro hlowerClosureAt
    -- Conversely, the lower-hull equality immediately gives the saddle-hull equality.
    have hhullClosureAt :
        saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
          convexFunctionClosure (secondVariableDirectionalDerivativeFunction K u v) v' :=
      hhullEqAt.trans hlowerClosureAt
    exact hreduce.mpr hhullClosureAt

/-- Helper for Text 35.6.7: the ordinary lower semicontinuous hull is exactly the Section 33 raw
local-closure operator `functionConvexClosure`. -/
lemma helperForText_35_6_7_lowerSemicontinuousHull_eq_functionConvexClosure
    {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    lowerSemicontinuousHull f = functionConvexClosure f := by
  have hHullSpec := Classical.choose_spec (exists_lowerSemicontinuousHull (n := n) f)
  have hHullLsc : LowerSemicontinuous (lowerSemicontinuousHull f) := hHullSpec.1
  have hHullLe : lowerSemicontinuousHull f ≤ f := hHullSpec.2.1
  have hHullMax := hHullSpec.2.2
  have hRawLsc : LowerSemicontinuous (functionConvexClosure f) := by
    -- The Section 33 raw closure is lower semicontinuous by construction.
    simpa [functionConvexClosure] using
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := f)
  have hRawLe : functionConvexClosure f ≤ f := by
    -- The raw closure remains a pointwise minorant of the original function.
    intro x
    exact helperForLemma33_0_5_functionConvexClosure_raw_le_self (f := f) x
  apply le_antisymm
  · -- Every lower semicontinuous minorant lies below the raw closure.
    exact
      helperForTheorem33_1_lowerSemicontinuous_le_functionConvexClosure
        (f := f) (h := lowerSemicontinuousHull f) hHullLsc hHullLe
  · -- The raw closure is itself a lower semicontinuous minorant, so maximality of the hull
    -- forces it below `lowerSemicontinuousHull f`.
    exact hHullMax (functionConvexClosure f) hRawLsc hRawLe

/-- Helper for Text 35.6.7: for positive weights, epigraph convexity already yields Jensen's
inequality whenever both endpoint values avoid `⊥`; the only unresolved branch is the genuine
mixed `(⊥, ⊤)` case. -/
lemma helperForText_35_6_7_convexFunction_jensen_of_positiveWeights_and_endpointNeBot
    {n : ℕ} {D : (Fin n → ℝ) → EReal}
    (hconvD : ConvexFunction D)
    {x y : Fin n → ℝ} {a b : ℝ}
    (hPosA : 0 < a) (hPosB : 0 < b) (hab : a + b = 1)
    (hxBot : D x ≠ (⊥ : EReal)) (hyBot : D y ≠ (⊥ : EReal)) :
    D (a • x + b • y) ≤ (a : EReal) * D x + (b : EReal) * D y := by
  by_cases hxTop : D x = (⊤ : EReal)
  · -- A positive `⊤` contribution on the left endpoint makes the Jensen bound trivial.
    have hMulNeBot : (b : EReal) * D y ≠ (⊥ : EReal) :=
      helperForLemma33_0_5_positiveReal_mul_ne_bot hPosB hyBot
    have hRhsTop : (a : EReal) * D x + (b : EReal) * D y = (⊤ : EReal) := by
      rw [hxTop, EReal.coe_mul_top_of_pos hPosA]
      exact EReal.top_add_of_ne_bot hMulNeBot
    rw [hRhsTop]
    exact le_top
  by_cases hyTop : D y = (⊤ : EReal)
  · -- The symmetric `⊤` branch is just as immediate.
    have hMulNeBot : (a : EReal) * D x ≠ (⊥ : EReal) :=
      helperForLemma33_0_5_positiveReal_mul_ne_bot hPosA hxBot
    have hRhsTop : (a : EReal) * D x + (b : EReal) * D y = (⊤ : EReal) := by
      rw [hyTop, EReal.coe_mul_top_of_pos hPosB]
      exact EReal.add_top_of_ne_bot hMulNeBot
    rw [hRhsTop]
    exact le_top
  have hxReal : D x = (((D x).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hxTop hxBot).symm
  have hyReal : D y = (((D y).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hyTop hyBot).symm
  unfold ConvexFunction ConvexFunctionOn epigraph at hconvD
  have hxMem :
      (x, (D x).toReal) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) D := by
    refine ⟨Set.mem_univ x, ?_⟩
    exact le_of_eq hxReal
  have hyMem :
      (y, (D y).toReal) ∈ epigraph (Set.univ : Set (Fin n → ℝ)) D := by
    refine ⟨Set.mem_univ y, ?_⟩
    exact le_of_eq hyReal
  have hComboMem :
      a • (x, (D x).toReal) + b • (y, (D y).toReal) ∈
        epigraph (Set.univ : Set (Fin n → ℝ)) D :=
    hconvD hxMem hyMem hPosA.le hPosB.le hab
  -- Rewrite the real epigraph height back to the weighted `EReal` endpoint values.
  have hHeight :
      D (a • x + b • y) ≤
        ((((a * (D x).toReal + b * (D y).toReal : ℝ)) : EReal)) := by
    simpa [smul_eq_mul, EReal.coe_add, EReal.coe_mul] using hComboMem.2
  calc
    D (a • x + b • y) ≤ ((((a * (D x).toReal + b * (D y).toReal : ℝ)) : EReal)) := hHeight
    _ = (a : EReal) * (((D x).toReal : ℝ) : EReal) +
          (b : EReal) * (((D y).toReal : ℝ) : EReal) := by
        exact_mod_cast (show
          a * (D x).toReal + b * (D y).toReal =
            a * (D x).toReal + b * (D y).toReal by rfl)
    _ = (a : EReal) * D x + (b : EReal) * D y := by
        conv_rhs => rw [hxReal, hyReal]

/-- Helper for Text 35.6.7: once the Section 33 raw closure is Jensen-convex and already attains
`⊥` at one point, the mixed `(⊥, ⊤)` collapse forbids any `⊤` value, so the raw closure is the
constant `⊥` function. -/
lemma helperForText_35_6_7_functionConvexClosure_eq_bot_of_rawClosureConvex_and_rawBotPoint
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {x0 : Fin n → ℝ}
    (hRawConv :
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (functionConvexClosure f))
    (hx0Bot : functionConvexClosure f x0 = (⊥ : EReal)) :
    functionConvexClosure f = fun _ => (⊥ : EReal) := by
  have hRawConvFun : ConvexFunction (functionConvexClosure f) :=
    helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hRawConv
  have hRawConv' :
      IsERealConvexOn (Set.univ : Set (Fin n → ℝ))
        (fun z =>
          ⨆ ε : {r : ℝ // 0 < r},
            ⨅ w : {w : Fin n → ℝ // ‖w - z‖ < ε.1}, f w.1) := by
    simpa [functionConvexClosure] using hRawConv
  have hRawLsc : LowerSemicontinuous (functionConvexClosure f) := by
    -- The raw closure is lower semicontinuous by construction.
    simpa [functionConvexClosure] using
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := f)
  have hTopOrBot :
      ∀ y, functionConvexClosure f y = (⊤ : EReal) ∨
        functionConvexClosure f y = (⊥ : EReal) :=
    helperForLemma33_0_5_closedImproperConvex_values_top_or_bot
      (g := functionConvexClosure f) hRawConvFun hRawLsc ⟨x0, hx0Bot⟩
  have hNoTop : ∀ y, functionConvexClosure f y ≠ (⊤ : EReal) := by
    intro y hyTop
    rcases
        helperForLemma33_0_5_functionConvexClosure_top_has_topNeighborhood
          (f := f) (y := y) hTopOrBot hyTop with
      ⟨δ, hδTop⟩
    let δ' : {r : ℝ // 0 < r} := ⟨min δ.1 1, lt_min_iff.mpr ⟨δ.2, by norm_num⟩⟩
    let a : ℝ := δ'.1 / (2 * (‖x0 - y‖ + 1))
    let b : ℝ := 1 - a
    let z : Fin n → ℝ := a • x0 + b • y
    have hPosA : 0 < a := by
      -- The chosen coefficient is a positive fraction of the positive radius `δ'`.
      dsimp [a]
      exact div_pos δ'.2 (by positivity)
    have hA_mul_plus_one : a * (‖x0 - y‖ + 1) = δ'.1 / 2 := by
      -- Clearing the denominator isolates the exact contraction factor.
      dsimp [a]
      field_simp [show (‖x0 - y‖ + 1 : ℝ) ≠ 0 by positivity]
    have hA_le_half : a ≤ (1 / 2 : ℝ) := by
      have hPlusOne_ge_one : 1 ≤ ‖x0 - y‖ + 1 := by
        nlinarith [norm_nonneg (x0 - y)]
      have hDeltaLeOne : δ'.1 ≤ 1 := by
        exact min_le_right _ _
      -- The denominator `‖x0 - y‖ + 1` is at least `1`, so the contraction is at most `1/2`.
      nlinarith [hA_mul_plus_one, hPlusOne_ge_one, hDeltaLeOne]
    have hPosB : 0 < b := by
      -- The complementary weight stays strictly positive because `a ≤ 1/2`.
      dsimp [b]
      nlinarith
    have hzRewrite : z - y = a • (x0 - y) := by
      -- Rewrite the perturbation from `y` as a contracted displacement toward the `⊥` point.
      ext i
      dsimp [z, b]
      ring
    have hA_mul_norm_le : a * ‖x0 - y‖ ≤ δ'.1 / 2 := by
      have hNorm_le : ‖x0 - y‖ ≤ ‖x0 - y‖ + 1 := by
        nlinarith [norm_nonneg (x0 - y)]
      have hMul_le :
          a * ‖x0 - y‖ ≤ a * (‖x0 - y‖ + 1) := by
        exact mul_le_mul_of_nonneg_left hNorm_le hPosA.le
      -- Comparing with `a * (‖x0 - y‖ + 1)` gives the desired half-radius bound.
      simpa [hA_mul_plus_one] using hMul_le
    have hzBall' : ‖z - y‖ < δ'.1 := by
      have hHalfLt : δ'.1 / 2 < δ'.1 := by
        nlinarith [δ'.2]
      -- The contracted point `z` lies strictly inside the smaller top neighborhood around `y`.
      calc
        ‖z - y‖ = ‖a • (x0 - y)‖ := by rw [hzRewrite]
        _ = |a| * ‖x0 - y‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = a * ‖x0 - y‖ := by simp [abs_of_nonneg hPosA.le]
        _ ≤ δ'.1 / 2 := hA_mul_norm_le
        _ < δ'.1 := hHalfLt
    have hzBall : ‖z - y‖ < δ.1 := by
      exact lt_of_lt_of_le hzBall' (min_le_left _ _)
    have hzTop : functionConvexClosure f z = (⊤ : EReal) := by
      -- Any point in the shrunken ball still lies in the original top neighborhood of `y`.
      exact hδTop ⟨z, hzBall⟩
    have hzBot : functionConvexClosure f z = (⊥ : EReal) := by
      -- The mixed `(⊥, ⊤)` collapse now forces the same strict convex combination to be `⊥`.
      have hCollapse :
          (⨆ ε : {r : ℝ // 0 < r},
            ⨅ w : {w : Fin n → ℝ // ‖w - (a • x0 + b • y)‖ < ε.1}, f w.1) = (⊥ : EReal) :=
        helperForLemma33_0_5_functionConvexClosure_mixedBotTop_collapse_from_rawClassification
          (f := f) (x := x0) (y := y) hRawConv' hPosA.le hPosB.le
          (by dsimp [b]; linarith) hPosA hPosB hx0Bot hyTop
      simpa [functionConvexClosure, z] using hCollapse
    rw [hzTop] at hzBot
    simp at hzBot
  funext y
  rcases hTopOrBot y with hyTop | hyBot
  · exact False.elim (hNoTop y hyTop)
  · exact hyBot

/- Formalization history: an earlier route tried to prove the empty-partial branch without the
dense-domain qualification by forcing a mixed `(⊥, ⊤)` directional-derivative collapse. That
unsupported legacy chain was unused by the corrected dense-domain theorem and has been removed. -/

/-- Helper for Text 35.6.7: if the effective domain of the convex second slice `v' ↦ K u v'` is
dense, then the empty-`∂₂ K(u, v)` branch forces the ordinary lower semicontinuous hull of `ψ` to
collapse to the constant `⊥` function. -/
lemma helperForText_35_6_7_lowerHull_eq_bot_of_empty_partialSecond_of_dense_secondSliceDomain
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInSecondVariable K u v = ∅)
    (hDense :
      closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u)) = Set.univ) :
    lowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) =
      fun _ => (⊥ : EReal) := by
  let g : (Fin n → ℝ) → EReal := K u
  have hg : ConvexFunction g := by
    -- Fixing the first variable leaves the second slice convex.
    simpa [g] using hSaddle.2 u
  have hgv : g v ≠ (⊤ : EReal) ∧ g v ≠ (⊥ : EReal) := by
    -- The base value of the slice is exactly the finite value `K u v`.
    simpa [g] using hFinite
  have hsliceEmpty : subdifferentialAt g v = ∅ := by
    -- Empty textbook second partial subdifferential is the same as empty slice subdifferential.
    simpa [g] using
      (helperForText_35_6_7_partialSecond_empty_iff_sliceSubdifferential_empty
        (K := K) (u := u) (v := v)).1 hpartialEmpty
  have hpsiEq :
      secondVariableDirectionalDerivativeFunction K u v =
        upperDirectionalDerivativeAt g v := by
    -- Identify the textbook `ψ` with the ordinary slice directional derivative.
    simpa [g] using
      helperForText_35_6_7_secondVariableDirectionalDerivative_eq_upperDirectionalDerivative
        (K := K) hSaddle (u := u) (v := v) hFinite
  calc
    lowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) =
        epigraphClosureInf (secondVariableDirectionalDerivativeFunction K u v) := by
      -- The standard lower semicontinuous hull is the same epigraph hull used throughout the
      -- Chapter 2 formalization.
      symm
      exact
        helperForText_35_6_6_epigraphClosureInf_eq_lowerSemicontinuousHull
          (φ := secondVariableDirectionalDerivativeFunction K u v)
    _ = epigraphClosureInf (upperDirectionalDerivativeAt g v) := by
      rw [hpsiEq]
    _ = fun _ => (⊥ : EReal) := by
      -- Once the second slice has dense effective domain, the imported empty-subdifferential
      -- collapse applies directly to the slice directional derivative.
      exact
        helperForText_35_6_6_epigraphClosureInf_eq_bot_of_empty_sliceSubdifferential_of_dense_reflectedSliceDomain
          (g := g) (x := v) hg hgv hsliceEmpty (by simpa [g] using hDense)

/-- Helper for Text 35.6.7: with dense effective domain for the second slice, the empty-`∂₂ K(u,
v)` branch upgrades all the way from the ordinary lower semicontinuous hull of `ψ` to its Chapter
23 convex closure. -/
lemma helperForText_35_6_7_lowerHull_eq_convexClosure_of_empty_partialSecond_of_dense_secondSliceDomain
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hpartialEmpty : partialSubdifferentialInSecondVariable K u v = ∅)
    (hDense :
      closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u)) = Set.univ)
    (v' : Fin n → ℝ) :
    lowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
      convexFunctionClosure (secondVariableDirectionalDerivativeFunction K u v) v' := by
  -- The dense-domain collapse identifies both sides with the constant `⊥` function.
  calc
    lowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
        (⊥ : EReal) := by
      simpa using congrFun
        (helperForText_35_6_7_lowerHull_eq_bot_of_empty_partialSecond_of_dense_secondSliceDomain
          (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty hDense) v'
    _ =
        convexFunctionClosure (secondVariableDirectionalDerivativeFunction K u v) v' := by
      symm
      simpa using congrFun
        (helperForText_35_6_7_convexFunctionClosure_eq_bot_of_empty_partialSecond
          (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty) v'

/-- Text 35.6.7: let `K` be a saddle function on `ℝ^m × ℝ^n`, and let `(u, v)` be a point with
finite value `K u v`. Assume that the effective domain of the second slice `v' ↦ K u v'` is
dense in `ℝ^n`. Define `ψ(v') = K'(u, v; 0, v')`. Then `ψ` is a convex function on `ℝ^n`,
and the lower semicontinuous hull of `ψ` coincides with the support function of the closed convex
set `∂₂ K(u, v)`. -/
theorem section35_text35_6_7
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSaddle : IsGloballyConcaveConvexERealKernel K)
    {u : Fin m → ℝ} {v : Fin n → ℝ}
    (hFinite : K u v ≠ (⊤ : EReal) ∧ K u v ≠ (⊥ : EReal))
    (hDense :
      closure (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (K u)) = Set.univ) :
    ConvexFunction (secondVariableDirectionalDerivativeFunction K u v) ∧
      ∀ v' : Fin n → ℝ,
        saddleLowerSemicontinuousHull (secondVariableDirectionalDerivativeFunction K u v) v' =
          supportFunctionOfSet (partialSubdifferentialInSecondVariable K u v) v' := by
  have hpsiEq :
      secondVariableDirectionalDerivativeFunction K u v =
        upperDirectionalDerivativeAt (K u) v :=
    helperForText_35_6_7_secondVariableDirectionalDerivative_eq_upperDirectionalDerivative
      (K := K) hSaddle (u := u) (v := v) hFinite
  constructor
  · rw [hpsiEq]
    exact
      (convex_directionalDerivative_monotone_exists_and_sublinear
        (K u) (hSaddle.2 u) v hFinite).2.2.1
  · intro v'
    by_cases hpartial : Set.Nonempty (partialSubdifferentialInSecondVariable K u v)
    · exact congrFun
        (helperForText_35_6_7_saddleLowerHull_eq_secondPartialSupport_of_nonempty_partialSecond
          (K := K) hSaddle (u := u) (v := v) hFinite hpartial) v'
    · have hpartialEmpty : partialSubdifferentialInSecondVariable K u v = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hpartial
      exact
        (helperForText_35_6_7_emptyPartial_goal_iff_lowerHull_eq_convexClosure
          (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty v').2
          (helperForText_35_6_7_lowerHull_eq_convexClosure_of_empty_partialSecond_of_dense_secondSliceDomain
            (K := K) hSaddle (u := u) (v := v) hFinite hpartialEmpty hDense v')

end Section35
end Chap07
