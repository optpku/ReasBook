/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part17

section Chap06
section Section30

/-- Helper for Theorem 6.30.21: in the negative-multiplier counterexample (`uStar ≡ -1`), the
witness condition (right-hand side of the third conjunct) holds with the zero witnesses, while
the weighted objective is unbounded below, so the infimum condition (left-hand side) fails. -/
lemma helperForTheorem_6_30_21_counterexample_negativeMultiplier_rhs_true_and_lhs_false :
    let f0 : (Fin 1 → ℝ) → EReal := fun _ => (0 : EReal)
    let f : Fin 1 → (Fin 1 → ℝ) → EReal := fun _ x => (((x 0) ^ 2 : ℝ) : EReal)
    let uStar : Fin 1 → ℝ := fun _ => (-1 : ℝ)
    (∃ y0 : Fin 1 → ℝ,
        y0 ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 f0) ∧
        ∃ y : Fin 1 → Fin 1 → ℝ,
          (∀ i : Fin 1,
            y i ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 (f i))) ∧
          y0 + ∑ i : Fin 1, (uStar i) • y i = 0) ∧
      ¬ ((⊥ : EReal) <
          sInf (Set.range fun x : Fin 1 → ℝ =>
            ordinaryConvexProgramWeightedObjective f0 f uStar x)) := by
  classical
  -- Unfold the concrete data so we can reuse the already-proved counterexample lemma.
  dsimp

  -- Step 1: establish the witness condition by specializing the zero-witness helper to `c = -1`.
  have hRhs :
      ∃ y0 : Fin 1 → ℝ,
        y0 ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal))) ∧
        ∃ y : Fin 1 → Fin 1 → ℝ,
          (∀ i : Fin 1,
            y i ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
              (fenchelConjugate 1 (fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal)))) ∧
          (y0 + ∑ i : Fin 1, ((fun _ : Fin 1 => (-1 : ℝ)) i) • y i = 0) := by
    simpa using
      (helperForTheorem_6_30_21_zeroWitness_rhs_for_scalarMultiplier (c := (-1 : ℝ)))

  -- Step 2: the already-proved counterexample lemma upgrades `RHS` into `¬ LHS`.
  have hContra :
      ¬ ((⊥ : EReal) <
            sInf (Set.range fun x : Fin 1 → ℝ =>
              ordinaryConvexProgramWeightedObjective
                (fun _ : Fin 1 → ℝ => (0 : EReal))
                (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
                (fun _ : Fin 1 => (-1 : ℝ)) x) ↔
          ∃ y0 : Fin 1 → ℝ,
            y0 ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
                  (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal))) ∧
              ∃ y : Fin 1 → Fin 1 → ℝ,
                (∀ i : Fin 1,
                  y i ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
                        (fenchelConjugate 1
                          (fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal)))) ∧
                  y0 + ∑ i : Fin 1, ((fun _ : Fin 1 => (-1 : ℝ)) i) • y i = 0) := by
    simpa using helperForTheorem_6_30_21_counterexample_negativeMultiplier
  refine ⟨hRhs, ?_⟩
  intro hLhs
  -- If `LHS` were true, then since `RHS` is true we would get `LHS ↔ RHS`, contradicting `hContra`.
  have hIff :
      ((⊥ : EReal) <
            sInf (Set.range fun x : Fin 1 → ℝ =>
              ordinaryConvexProgramWeightedObjective
                (fun _ : Fin 1 → ℝ => (0 : EReal))
                (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
                (fun _ : Fin 1 => (-1 : ℝ)) x) ↔
          ∃ y0 : Fin 1 → ℝ,
            y0 ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
                  (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal))) ∧
              ∃ y : Fin 1 → Fin 1 → ℝ,
                (∀ i : Fin 1,
                  y i ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
                        (fenchelConjugate 1
                          (fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal)))) ∧
                  y0 + ∑ i : Fin 1, ((fun _ : Fin 1 => (-1 : ℝ)) i) • y i = 0) := by
    constructor
    · intro _h
      exact hRhs
    · intro _h
      exact hLhs
  exact hContra hIff

/-- Helper for Theorem 6.30.21: the third conjunct in
`dualObjective_and_feasibleSet_of_ordinaryConvexProgram` cannot be true as stated, since it
quantifies the witness-style equivalence over all multipliers `uStar : Fin m → ℝ` without
restricting to the dual-feasible region `uStar ≥ 0`. The counterexample with `uStar ≡ -1`
exhibits `RHS` true and `LHS` false. -/
lemma helperForTheorem_6_30_21_thirdConjunct_isFalse_asQuantified :
    let f0 : (Fin 1 → ℝ) → EReal := fun _ => (0 : EReal)
    let f : Fin 1 → (Fin 1 → ℝ) → EReal := fun _ x => (((x 0) ^ 2 : ℝ) : EReal)
    ¬ (∀ uStar : Fin 1 → ℝ,
        (⊥ : EReal) <
            sInf (Set.range fun x : Fin 1 → ℝ =>
              ordinaryConvexProgramWeightedObjective f0 f uStar x) ↔
          ∃ y0 : Fin 1 → ℝ,
            y0 ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) (fenchelConjugate 1 f0) ∧
            ∃ y : Fin 1 → Fin 1 → ℝ,
              (∀ i : Fin 1,
                y i ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
                  (fenchelConjugate 1 (f i))) ∧
              y0 + ∑ i : Fin 1, (uStar i) • y i = 0) := by
  classical
  -- Unfold `f0` and `f` so we can apply the explicit counterexample at `uStar ≡ -1`.
  dsimp
  intro hall
  have hBad := hall (fun _ : Fin 1 => (-1 : ℝ))
  -- The explicit counterexample refutes the equivalence at the negative multiplier.
  have hContra :
      ¬ ((⊥ : EReal) <
            sInf (Set.range fun x : Fin 1 → ℝ =>
              ordinaryConvexProgramWeightedObjective
                (fun _ : Fin 1 → ℝ => (0 : EReal))
                (fun _ : Fin 1 => fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal))
                (fun _ : Fin 1 => (-1 : ℝ)) x) ↔
          ∃ y0 : Fin 1 → ℝ,
            y0 ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
                  (fenchelConjugate 1 (fun _ : Fin 1 → ℝ => (0 : EReal))) ∧
              ∃ y : Fin 1 → Fin 1 → ℝ,
                (∀ i : Fin 1,
                  y i ∈ effectiveDomain (Set.univ : Set (Fin 1 → ℝ))
                        (fenchelConjugate 1
                (fun x : Fin 1 → ℝ => (((x 0) ^ 2 : ℝ) : EReal)))) ∧
                  y0 + ∑ i : Fin 1, ((fun _ : Fin 1 => (-1 : ℝ)) i) • y i = 0) := by
    simpa using helperForTheorem_6_30_21_counterexample_negativeMultiplier
  exact hContra hBad

/-- Helper for Theorem 6.30.21: on the branch `uStar ≥ 0`, finiteness of the Fenchel conjugate of
the weighted objective at `0` yields the textbook witness form
`0 ∈ dom(f₀^*) + ∑ᵢ uᵢ* • dom(fᵢ^*)`. -/
lemma helperForTheorem_6_30_21_exists_witness_of_fenchelConjugate_zero_lt_top_of_nonneg
    {m n : ℕ} (C : Set (Fin n → ℝ))
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (hf0 : ProperConvexERealFunction (F := (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexERealFunction (F := (Fin n → ℝ)) (f i))
    (hdom_f0 : effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0 = C)
    (hdom_f : ∀ i : Fin m, C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
    (hri_f : ∀ i : Fin m,
      euclideanRelativeInterior_fin n C ⊆
        euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)))
    {uStar : Fin m → ℝ} (hnonneg : ∀ i : Fin m, 0 ≤ uStar i)
    (hfinite :
      fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) 0 < (⊤ : EReal)) :
    ∃ y0 : Fin n → ℝ,
      y0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f0) ∧
      ∃ y : Fin m → Fin n → ℝ,
        (∀ i : Fin m,
          y i ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))) ∧
        y0 + ∑ i : Fin m, (uStar i) • y i = 0 := by
  classical
  let fFam : Fin (m + 1) → (Fin n → ℝ) → EReal :=
    Fin.cases f0 (fun i => fun x => (((uStar i : ℝ) : EReal) * f i x))
  have hsumFam :
      (fun x => ∑ j : Fin (m + 1), fFam j x) =
        ordinaryConvexProgramWeightedObjective f0 f uStar := by
    -- Reindex the family as the head term `f₀` plus the scaled constraint terms.
    funext x
    simp [fFam, ordinaryConvexProgramWeightedObjective, Fin.sum_univ_succ,
      add_assoc, add_left_comm, add_comm]
  have hproperFam :
      ∀ j : Fin (m + 1),
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fFam j) := by
    intro j
    refine Fin.cases ?_ ?_ j
    · -- The head term is just `f₀`.
      simpa [fFam] using
        helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
          (f := f0) hf0
    · intro i
      -- Every tail term is a nonnegative scalar multiple of `f i`.
      simpa [fFam] using
        helperForTheorem_6_30_21_properConvexFunctionOn_univ_mul_of_nonneg
          (f := f i) (hf := hf i) (hlam := hnonneg i)
  have hproperF0 :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f0 :=
    helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
      (f := f0) hf0
  have hCconv : Convex ℝ C := by
    -- `C = dom f₀`, and effective domains of proper convex functions are convex.
    simpa [hdom_f0] using
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f0) hproperF0.1
  have hCne : C.Nonempty := by
    -- Properness of `f₀` provides one finite point, hence one point of `C`.
    rcases hf0.1.2 with ⟨x0, hx0_ne_top⟩
    have hx0_dom : x0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0 := by
      rw [effectiveDomain_eq]
      exact ⟨by simp, (lt_top_iff_ne_top).2 hx0_ne_top⟩
    exact ⟨x0, by simpa [hdom_f0] using hx0_dom⟩
  rcases helperForTheorem_21_1_riFin_nonempty_of_convex_nonempty C hCconv hCne with
    ⟨x0, hx0riC⟩
  have hriFam :
      Set.Nonempty
        (⋂ j : Fin (m + 1),
          euclideanRelativeInterior n
            ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFam j))) := by
    let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
    have hpreimage (A : Set (Fin n → ℝ)) :
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹' A) = e.symm '' A := by
      ext x
      constructor
      · intro hx
        refine ⟨e x, hx, ?_⟩
        simp [e]
      · rintro ⟨y, hy, rfl⟩
        simpa [e] using hy
    refine ⟨e.symm x0, Set.mem_iInter.2 ?_⟩
    intro j
    refine Fin.cases ?_ ?_ j
    · -- The head block uses the chosen point in `ri C = ri dom(f₀)`.
      have hx0ri0 :
          x0 ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0) := by
        simpa [hdom_f0] using hx0riC
      -- Rewrite the preimage domain into an `e.symm` image so `mem_euclideanRelativeInterior_fin_iff` applies.
      have hx0ri0E :
          e.symm x0 ∈
            euclideanRelativeInterior n
              (e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0) :=
        (mem_euclideanRelativeInterior_fin_iff
          (n := n) (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0) (x := x0)).1 hx0ri0
      simpa [hpreimage, fFam, e] using hx0ri0E
    · intro i
      by_cases hzero : uStar i = 0
      · -- Zero multipliers give the constant-zero function, whose effective domain is all of `ℝⁿ`.
        have hx0Interior :
            x0 ∈ interior (Set.univ : Set (Fin n → ℝ)) := by
          simp
        have hx0riUniv :
            x0 ∈ euclideanRelativeInterior_fin n (Set.univ : Set (Fin n → ℝ)) := by
          exact helperForTheorem_23_4_mem_relativeInterior_of_mem_interior hx0Interior
        have hx0riScaled :
            x0 ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFam (Fin.succ i))) := by
          simpa [fFam, hzero, effectiveDomain_eq] using hx0riUniv
        have hx0riScaledE :
            e.symm x0 ∈
              euclideanRelativeInterior n
                (e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFam (Fin.succ i))) :=
          (mem_euclideanRelativeInterior_fin_iff
            (n := n)
            (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFam (Fin.succ i)))
            (x := x0)).1 hx0riScaled
        simpa [hpreimage, e] using hx0riScaledE
      · -- Positive multipliers preserve the effective domain and therefore its relative interior.
        have hpos : 0 < uStar i := lt_of_le_of_ne (hnonneg i) (Ne.symm hzero)
        have hx0rii :
            x0 ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :=
          hri_f i hx0riC
        have hx0riScaled :
            x0 ∈ euclideanRelativeInterior_fin n
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFam (Fin.succ i))) := by
          simpa [fFam,
            helperForTheorem_6_30_21_effectiveDomain_mul_eq_of_pos (f := f i) hpos] using hx0rii
        have hx0riScaledE :
            e.symm x0 ∈
              euclideanRelativeInterior n
                (e.symm '' effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFam (Fin.succ i))) :=
          (mem_euclideanRelativeInterior_fin_iff
            (n := n)
            (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fFam (Fin.succ i)))
            (x := x0)).1 hx0riScaled
        simpa [hpreimage, e] using hx0riScaledE
  have hsec16 :=
    section16_fenchelConjugate_sum_eq_infimalConvolutionFamily_of_nonempty_iInter_ri_effectiveDomain
      (f := fFam) hproperFam hriFam
  have hInfConvLtTop :
      infimalConvolutionFamily (fun j : Fin (m + 1) => fenchelConjugate n (fFam j)) 0 < (⊤ : EReal) := by
    -- Rewrite the weighted-objective conjugate using the Section 16 sum theorem.
    have hEqAtZero :
        fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) 0 =
          infimalConvolutionFamily (fun j : Fin (m + 1) => fenchelConjugate n (fFam j)) 0 := by
      simpa [hsumFam] using
        congrArg (fun g : (Fin n → ℝ) → EReal => g (0 : Fin n → ℝ)) hsec16.1
    simpa [hEqAtZero] using hfinite
  rcases hsec16.2 (0 : Fin n → ℝ) with htop | ⟨z, hsumz, hzval⟩
  · -- The `= ⊤` branch contradicts the assumed finiteness at `0`.
    have : (⊤ : EReal) < (⊤ : EReal) := by
      simpa [htop] using hInfConvLtTop
    exact False.elim ((lt_irrefl (⊤ : EReal)) this)
  · let term : Fin (m + 1) → EReal := fun j => fenchelConjugate n (fFam j) (z j)
    have hterm_ne_bot : ∀ j : Fin (m + 1), term j ≠ (⊥ : EReal) := by
      intro j
      have hproperE :
          ProperERealFunction (fFam j) :=
        (helperForLemma_26_2_properConvexERealFunction (hproperFam j)).1
      exact
        helperForTheorem_6_30_21_fenchelConjugate_ne_bot_of_properERealFunction
          (hf := hproperE) (xStar := z j)
    have hsum_ne_top : (∑ j : Fin (m + 1), term j) ≠ (⊤ : EReal) := by
      have hsum_lt_top : (∑ j : Fin (m + 1), term j) < (⊤ : EReal) := by
        simpa [term, hzval] using hInfConvLtTop
      exact (lt_top_iff_ne_top).1 hsum_lt_top
    have hterm_dom :
        ∀ j : Fin (m + 1),
          z j ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (fFam j)) := by
      intro j
      have hterm_ne_top : term j ≠ (⊤ : EReal) := by
        intro htop_j
        have hrest_ne_bot :
            Finset.sum (Finset.univ.erase j) term ≠ (⊥ : EReal) := by
          refine finset_sum_ne_bot_of_forall (s := Finset.univ.erase j) (f := term) ?_
          intro k hk
          exact hterm_ne_bot k
        have hsum_eq_top : (∑ k : Fin (m + 1), term k) = (⊤ : EReal) := by
          calc
            (∑ k : Fin (m + 1), term k) = term j + Finset.sum (Finset.univ.erase j) term := by
              symm
              have hj : j ∈ (Finset.univ : Finset (Fin (m + 1))) := by
                simp
              exact Finset.add_sum_erase (s := Finset.univ) (f := term) (a := j) hj
            _ = (⊤ : EReal) + Finset.sum (Finset.univ.erase j) term := by
              simp [term, htop_j]
            _ = (⊤ : EReal) := EReal.top_add_of_ne_bot hrest_ne_bot
        exact hsum_ne_top hsum_eq_top
      rw [effectiveDomain_eq]
      exact ⟨by simp, by simpa [term] using (lt_top_iff_ne_top).2 hterm_ne_top⟩
    have hzeroDom :
        z 0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f0) := by
      simpa [fFam] using hterm_dom 0
    have hArbExists :
        ∀ i : Fin m,
          ∃ yi : Fin n → ℝ,
            yi ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i)) := by
      intro i
      have hproperFi :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i) :=
        helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
          (f := f i) (hf i)
      have hproperFiStar :
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i)) :=
        proper_fenchelConjugate_of_proper (n := n) (f := f i) hproperFi
      rcases properConvexFunctionOn_exists_finite_point (n := n)
          (f := fenchelConjugate n (f i)) hproperFiStar with ⟨yi, r, hyr⟩
      refine ⟨yi, ?_⟩
      rw [effectiveDomain_eq]
      refine ⟨by simp, ?_⟩
      rw [hyr]
      simp
    choose yArb hyArb using hArbExists
    let y : Fin m → Fin n → ℝ :=
      fun i => if hpos : 0 < uStar i then (uStar i)⁻¹ • z (Fin.succ i) else yArb i
    have hy :
        ∀ i : Fin m,
          y i ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i)) := by
      intro i
      by_cases hpos : 0 < uStar i
      · -- On positive coordinates, use the scaling formula to pull the domain witness back.
        have hzScaled :
            z (Fin.succ i) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fenchelConjugate n (fun x => (((uStar i : ℝ) : EReal) * f i x))) := by
          simpa [fFam] using hterm_dom (Fin.succ i)
        have hproperFi :
            ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i) :=
          helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
            (f := f i) (hf i)
        have hproperFiStar :
            ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i)) :=
          proper_fenchelConjugate_of_proper (n := n) (f := f i) hproperFi
        have hpoint :
            fenchelConjugate n (fun x => (((uStar i : ℝ) : EReal) * f i x)) (z (Fin.succ i)) =
              (((uStar i : ℝ) : EReal) *
                fenchelConjugate n (f i) ((uStar i)⁻¹ • z (Fin.succ i))) := by
          have hscale :=
            (section16_fenchelConjugate_scaling (n := n) (f := f i) (hf := hproperFi)
              (hlam := le_of_lt hpos)).1
          calc
            fenchelConjugate n (fun x => (((uStar i : ℝ) : EReal) * f i x)) (z (Fin.succ i))
                = rightScalarMultiple (fenchelConjugate n (f i)) (uStar i) (z (Fin.succ i)) := by
                    simpa using congrArg (fun g : (Fin n → ℝ) → EReal => g (z (Fin.succ i))) hscale
            _ =
                (((uStar i : ℝ) : EReal) *
                  fenchelConjugate n (f i) ((uStar i)⁻¹ • z (Fin.succ i))) := by
                    simpa using
                      rightScalarMultiple_pos (f := fenchelConjugate n (f i)) (lam := uStar i)
                        hproperFiStar.1 hpos (z (Fin.succ i))
        have hltTopScaled :
            fenchelConjugate n (fun x => (((uStar i : ℝ) : EReal) * f i x)) (z (Fin.succ i)) <
              (⊤ : EReal) := by
          rw [effectiveDomain_eq] at hzScaled
          exact hzScaled.2
        have hltTopOrig :
            fenchelConjugate n (f i) ((uStar i)⁻¹ • z (Fin.succ i)) < (⊤ : EReal) := by
          have hltTopScaled' :
              (((uStar i : ℝ) : EReal) *
                fenchelConjugate n (f i) ((uStar i)⁻¹ • z (Fin.succ i))) < (⊤ : EReal) := by
            simpa [hpoint] using hltTopScaled
          exact
            (helperForTheorem_6_30_21_mul_lt_top_iff_of_pos
              (lam := uStar i) hpos
              (fenchelConjugate n (f i) ((uStar i)⁻¹ • z (Fin.succ i)))).1 hltTopScaled'
        simpa [y, hpos, effectiveDomain_eq, hltTopOrig]
      · -- On zero coordinates, use the arbitrary conjugate-domain witness.
        simpa [y, hpos] using hyArb i
    have hyTail :
        ∀ i : Fin m, (uStar i) • y i = z (Fin.succ i) := by
      intro i
      by_cases hpos : 0 < uStar i
      · -- Positive coordinates undo the inverse scaling.
        have hne : uStar i ≠ 0 := ne_of_gt hpos
        calc
          (uStar i) • y i = (uStar i) • ((uStar i)⁻¹ • z (Fin.succ i)) := by
            simp [y, hpos]
          _ = ((uStar i * (uStar i)⁻¹ : ℝ)) • z (Fin.succ i) := by
            simp [smul_smul]
          _ = z (Fin.succ i) := by
            simp [hne]
      · -- Zero coordinates contribute `0`, and their attained split point is forced to be `0`.
        have hzero : uStar i = 0 := le_antisymm (le_of_not_gt hpos) (hnonneg i)
        have hzScaled :
            z (Fin.succ i) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fenchelConjugate n (fun x => (((uStar i : ℝ) : EReal) * f i x))) := by
          simpa [fFam] using hterm_dom (Fin.succ i)
        have hzZero :
            z (Fin.succ i) = 0 := by
          have hzScaledZero :
              z (Fin.succ i) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
                (fenchelConjugate n (fun _ : Fin n → ℝ => (0 : EReal))) := by
            simpa [hzero] using hzScaled
          have hconstConj :
              fenchelConjugate n (fun _ : Fin n → ℝ => (0 : EReal)) =
                indicatorFunction ({0} : Set (Fin n → ℝ)) := by
            simpa using (section16_fenchelConjugate_const_zero (n := n))
          have hzIndicator :
              z (Fin.succ i) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ))
                (indicatorFunction ({0} : Set (Fin n → ℝ))) := by
            simpa [hconstConj] using hzScaledZero
          rw [effectiveDomain_eq] at hzIndicator
          by_cases hz : z (Fin.succ i) = 0
          · exact hz
          · simp [indicatorFunction, hz] at hzIndicator
        simp [y, hpos, hzero, hzZero]
    have hsumZero : z 0 + ∑ i : Fin m, z (Fin.succ i) = 0 := by
      simpa [Fin.sum_univ_succ, add_assoc, add_left_comm, add_comm] using hsumz
    refine ⟨z 0, hzeroDom, y, hy, ?_⟩
    -- Replace each attained tail piece by its corresponding `uStar i • y i`.
    calc
      z 0 + ∑ i : Fin m, (uStar i) • y i = z 0 + ∑ i : Fin m, z (Fin.succ i) := by
        refine congrArg (fun t => z 0 + t) ?_
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact hyTail i
      _ = 0 := hsumZero

/-- Theorem 6.30.21: under the assumptions of Theorem 6.30.20, the objective function of the
dual concave program associated with the ordinary convex program is
`u* ↦ inf_x (f₀(x) + ∑ᵢ uᵢ* fᵢ(x))` for `u* ≥ 0`, and `-∞` otherwise. Hence the feasible
solutions of the dual program are exactly the nonnegative vectors `u*` for which this infimum is
strictly greater than `-∞`. Equivalently, the finiteness condition is the existence of vectors in
the domains of `f₀*` and the `fᵢ*` whose weighted sum is zero, i.e. Lean's witness form of
`0 ∈ dom(f₀*) + ∑ᵢ uᵢ* • dom(fᵢ*)`. -/
theorem dualObjective_and_feasibleSet_of_ordinaryConvexProgram
    {m n : ℕ} (C : Set (Fin n → ℝ))
    (f0 : (Fin n → ℝ) → EReal) (f : Fin m → (Fin n → ℝ) → EReal)
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F})
    (hF : F.1 = ordinaryConvexProgramBifunction f0 f)
    (hf0 : ProperConvexERealFunction (F := (Fin n → ℝ)) f0)
    (hf : ∀ i : Fin m, ProperConvexERealFunction (F := (Fin n → ℝ)) (f i))
    (hdom_f0 : effectiveDomain (Set.univ : Set (Fin n → ℝ)) f0 = C)
    (hdom_f : ∀ i : Fin m, C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
    (hri_f : ∀ i : Fin m,
      euclideanRelativeInterior_fin n C ⊆
        euclideanRelativeInterior_fin n (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))) :
    (∀ uStar : Fin m → ℝ,
      adjointOfConvexBifunction F 0 uStar =
        if ∀ i : Fin m, 0 ≤ uStar i then
          sInf (Set.range fun x : Fin n → ℝ =>
            ordinaryConvexProgramWeightedObjective f0 f uStar x)
        else
          (⊥ : EReal)) ∧
    ({uStar : Fin m → ℝ | (⊥ : EReal) < adjointOfConvexBifunction F 0 uStar} =
      {uStar : Fin m → ℝ | (∀ i : Fin m, 0 ≤ uStar i) ∧
        (⊥ : EReal) <
          sInf (Set.range fun x : Fin n → ℝ =>
            ordinaryConvexProgramWeightedObjective f0 f uStar x)}) ∧
    (∀ uStar : Fin m → ℝ, (∀ i : Fin m, 0 ≤ uStar i) →
      ((⊥ : EReal) <
          sInf (Set.range fun x : Fin n → ℝ =>
            ordinaryConvexProgramWeightedObjective f0 f uStar x) ↔
        ∃ y0 : Fin n → ℝ,
          y0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f0) ∧
          ∃ y : Fin m → Fin n → ℝ,
            (∀ i : Fin m,
              y i ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))) ∧
            y0 + ∑ i : Fin m, (uStar i) • y i = 0)) := by
  -- First, specialize Theorem 6.30.20 at `x* = 0` and rewrite `-f* (0)` as an infimum.
  have hObjectiveFormula :
      ∀ uStar : Fin m → ℝ,
        adjointOfConvexBifunction F 0 uStar =
          if ∀ i : Fin m, 0 ≤ uStar i then
            sInf (Set.range fun x : Fin n → ℝ =>
              ordinaryConvexProgramWeightedObjective f0 f uStar x)
          else
            (⊥ : EReal) := by
    intro uStar
    have hAdjointAtZero :
        adjointOfConvexBifunction F 0 uStar =
          if ∀ i : Fin m, 0 ≤ uStar i then
            -fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) 0
          else
            (⊥ : EReal) := by
      simpa using
        adjointOfOrdinaryConvexProgramBifunction_eq_neg_fenchelConjugate_weightedObjective
          (C := C) (f0 := f0) (f := f) (F := F) (hF := hF)
          (hf0 := hf0) (hf := hf) (hdom_f0 := hdom_f0) (hdom_f := hdom_f)
          (hri_f := hri_f) (uStar := uStar) (xStar := (0 : Fin n → ℝ))
    have hFenchelAtZero :
        -fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) 0 =
          sInf (Set.range fun x : Fin n → ℝ =>
            ordinaryConvexProgramWeightedObjective f0 f uStar x) := by
      -- At `x* = 0`, the subtractive dot-product term vanishes pointwise.
      simpa [sub_eq_add_neg, ordinaryConvexProgramWeightedObjective] using
        (helperForTheorem_6_30_20_sInf_range_weightedObjective_sub_dot_eq_neg_fenchelConjugate
          (f0 := f0) (f := f) (uStar := uStar) (xStar := (0 : Fin n → ℝ))).symm
    by_cases hnonneg : ∀ i : Fin m, 0 ≤ uStar i
    · -- Nonnegative branch: replace `-f* (0)` by the weighted-objective infimum.
      rw [if_pos hnonneg] at hAdjointAtZero ⊢
      exact hAdjointAtZero.trans hFenchelAtZero
    · -- Negative branch: the value is `⊥`.
      rw [if_neg hnonneg] at hAdjointAtZero ⊢
      exact hAdjointAtZero
  refine ⟨hObjectiveFormula, ?_⟩
  refine ⟨?_, ?_⟩
  · -- Characterize the dual-feasible slice by unfolding the objective formula pointwise.
    ext uStar
    constructor
    · intro huStar
      by_cases hnonneg : ∀ i : Fin m, 0 ≤ uStar i
      · refine ⟨hnonneg, ?_⟩
        have hEq :
            adjointOfConvexBifunction F 0 uStar =
              sInf (Set.range fun x : Fin n → ℝ =>
                ordinaryConvexProgramWeightedObjective f0 f uStar x) := by
          simpa [hnonneg] using hObjectiveFormula uStar
        simpa [hEq] using huStar
      · have hEqBot : adjointOfConvexBifunction F 0 uStar = (⊥ : EReal) := by
          simpa [hnonneg] using hObjectiveFormula uStar
        have hContr : (⊥ : EReal) < (⊥ : EReal) := by
          simpa [hEqBot] using huStar
        exact (False.elim ((lt_irrefl (⊥ : EReal)) hContr))
    · intro huStar
      rcases huStar with ⟨hnonneg, hFiniteInf⟩
      have hEq :
          adjointOfConvexBifunction F 0 uStar =
            sInf (Set.range fun x : Fin n → ℝ =>
              ordinaryConvexProgramWeightedObjective f0 f uStar x) := by
        simpa [hnonneg] using hObjectiveFormula uStar
      simpa [hEq] using hFiniteInf
  · -- The witness criterion belongs to the dual-feasible branch `uStar ≥ 0`.
    intro uStar
    intro hnonneg
    -- Translate the left-hand side into a finiteness statement about the Fenchel conjugate at `0`.
    have hInfAsConj :
        (⊥ : EReal) <
            sInf (Set.range fun x : Fin n → ℝ =>
              ordinaryConvexProgramWeightedObjective f0 f uStar x) ↔
          fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) 0 < (⊤ : EReal) := by
      simpa using
        (helperForTheorem_6_30_21_bot_lt_sInf_range_iff_fenchelConjugate_zero_lt_top
          (g := ordinaryConvexProgramWeightedObjective f0 f uStar))
    have hRhsToLhs :
        (∃ y0 : Fin n → ℝ,
          y0 ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f0) ∧
          ∃ y : Fin m → Fin n → ℝ,
            (∀ i : Fin m,
              y i ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n (f i))) ∧
            y0 + ∑ i : Fin m, (uStar i) • y i = 0) →
          (⊥ : EReal) <
            sInf (Set.range fun x : Fin n → ℝ =>
              ordinaryConvexProgramWeightedObjective f0 f uStar x) := by
      intro hwit
      exact
        helperForTheorem_6_30_21_bot_lt_sInf_range_weightedObjective_of_exists_witness_of_nonneg
          (f0 := f0) (f := f) (hf0 := hf0) (hf := hf) (uStar := uStar) hnonneg hwit
    constructor
    · intro hLhs
      -- Rewrite finite infimum as finiteness of the conjugate at `0`, then apply the attained
      -- Section 16 decomposition for the weighted sum family.
      have hfinite0 :
          fenchelConjugate n (ordinaryConvexProgramWeightedObjective f0 f uStar) 0 < (⊤ : EReal) :=
        hInfAsConj.mp hLhs
      exact
        helperForTheorem_6_30_21_exists_witness_of_fenchelConjugate_zero_lt_top_of_nonneg
          (C := C) (f0 := f0) (f := f) (hf0 := hf0) (hf := hf)
          (hdom_f0 := hdom_f0) (hdom_f := hdom_f) (hri_f := hri_f)
          (uStar := uStar) hnonneg hfinite0
    · exact hRhsToLhs

/-- A perturbation parameter for the enlarged-perturbation program, consisting of the scalar
constraint perturbation `u`, the translation `x₀`, and the translations `xᵢ` for the constraint
functions. -/
structure EnlargedPerturbationParameter (m n : ℕ) where
  u : Fin m → ℝ
  x0 : Fin n → ℝ
  xShift : Fin m → Fin n → ℝ

/-- A dual perturbation parameter for the enlarged-perturbation program, consisting of the dual
vector `u*` and the dual translations `x₀*`, `xᵢ*`. -/
structure EnlargedPerturbationDualParameter (m n : ℕ) where
  uStar : Fin m → ℝ
  x0Star : Fin n → ℝ
  xShiftStar : Fin m → Fin n → ℝ

end Section30
end Chap06
