/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section23_part2

open scoped Topology
open scoped Pointwise

section Chap05
section Section23

-- Proof sketch: combine the subgradient inequality with the monotone-limit description of the
-- directional derivative from Theorem 23.1 to obtain the equivalence
-- `x* ∈ ∂f(x) ↔ ∀ y, ⟪x*, y⟫ ≤ f'(x; y)`; then identify the lower semicontinuous closure of the
-- directional-derivative function with the support function of the subdifferential and record that
-- the subdifferential is closed and convex.
/-- Helper for Theorem 23.2: a subgradient gives a lower bound on every positive directional
difference quotient. -/
lemma helperForTheorem_23_2_differenceQuotient_lowerBound_of_subgradient {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (xStar : Module.Dual ℝ (Fin n → ℝ))
    (hg : IsSubgradientAt f x xStar)
    (y : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    ((xStar y : ℝ) : EReal) ≤ directionalDifferenceQuotientAt f x y t := by
  let z : Fin n → ℝ := x + t • y
  have hnumerator :
      ((xStar (t • y) : ℝ) : EReal) ≤ f z - f x := by
    -- Repackage the subgradient inequality as a bound on the finite-difference numerator.
    exact
      (EReal.le_sub_iff_add_le (a := ((xStar (t • y) : ℝ) : EReal)) (b := f x) (c := f z)
        (Or.inl hx.2) (Or.inl hx.1)).2
        (by
          simpa [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hg z)
  have ht_nonneg_ereal : (0 : EReal) ≤ (t : EReal) := by
    exact_mod_cast le_of_lt ht
  have ht_ne_zero_ereal : (t : EReal) ≠ 0 := by
    exact_mod_cast ht.ne'
  have hdiv :=
    (EReal.monotone_div_right_of_nonneg (b := (t : EReal)) ht_nonneg_ereal) hnumerator
  have hscale :
      (((xStar (t • y) : ℝ) : EReal) / (t : EReal)) = ((xStar y : ℝ) : EReal) := by
    have hdiv_eq :=
      (EReal.div_eq_iff (a := ((xStar y : ℝ) : EReal)) (b := (t : EReal))
        (c := ((xStar (t • y) : ℝ) : EReal)) (by simp) (by simp) ht_ne_zero_ereal)
    refine hdiv_eq.2 ?_
    simp [mul_comm]
  -- Divide by the positive step length to obtain the quotient bound.
  calc
    ((xStar y : ℝ) : EReal) =
        (((xStar (t • y) : ℝ) : EReal) / (t : EReal)) := hscale.symm
    _ ≤ directionalDifferenceQuotientAt f x y t := by
      simpa [directionalDifferenceQuotientAt, z] using hdiv

/-- Helper for Theorem 23.2: subgradients are exactly the dual linear minorants of the upper
directional derivative. -/
lemma helperForTheorem_23_2_subgradient_iff_dual_linear_minorant {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (xStar : Module.Dual ℝ (Fin n → ℝ)) :
    IsSubgradientAt f x xStar ↔
      ∀ y : Fin n → ℝ, ((xStar y : ℝ) : EReal) ≤ upperDirectionalDerivativeAt f x y := by
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
    ⟨hdir, _hpos, _hconv, _hzero, _hsymm⟩
  constructor
  · intro hg y
    rcases hdir y with ⟨_hmono, _htend, hsInfEq⟩
    rw [hsInfEq]
    have hone_pos : 0 < (1 : ℝ) := by norm_num
    have hquot_nonempty :
        ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t).Nonempty := by
      refine ⟨directionalDifferenceQuotientAt f x y 1, ?_⟩
      exact ⟨1, hone_pos, rfl⟩
    -- The quotient lower bounds pass to the infimum formula for `f'(x; y)`.
    refine le_csInf hquot_nonempty ?_
    intro q hq
    rcases hq with ⟨t, ht, rfl⟩
    exact
      helperForTheorem_23_2_differenceQuotient_lowerBound_of_subgradient
        f x hx xStar hg y ht
  · intro hminor z
    let y : Fin n → ℝ := z - x
    rcases hdir y with ⟨_hmono, _htend, hsInfEq⟩
    have hy_le :
        ((xStar y : ℝ) : EReal) ≤ upperDirectionalDerivativeAt f x y := hminor y
    have hquot_bdd :
        BddBelow ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t) := by
      refine ⟨⊥, ?_⟩
      intro q hq
      simp
    have hone_pos : 0 < (1 : ℝ) := by norm_num
    have hy_le_quot :
        ((xStar y : ℝ) : EReal) ≤ directionalDifferenceQuotientAt f x y 1 := by
      rw [hsInfEq] at hy_le
      have hsInf_le :
          sInf ((Set.Ioi (0 : ℝ)).image fun t : ℝ => directionalDifferenceQuotientAt f x y t) ≤
            directionalDifferenceQuotientAt f x y 1 := by
        exact csInf_le hquot_bdd ⟨1, hone_pos, rfl⟩
      exact le_trans hy_le hsInf_le
    have hstep :
        ((xStar (z - x) : ℝ) : EReal) ≤ f z - f x := by
      -- Evaluating the difference quotient at `t = 1` recovers the textbook subgradient inequality.
      simpa [directionalDifferenceQuotientAt, y, one_smul, sub_eq_add_neg, add_assoc,
        add_left_comm, add_comm] using hy_le_quot
    have hadd :
        ((xStar (z - x) : ℝ) : EReal) + f x ≤ f z :=
      (EReal.le_sub_iff_add_le (a := ((xStar (z - x) : ℝ) : EReal)) (b := f x) (c := f z)
        (Or.inl hx.2) (Or.inl hx.1)).1 hstep
    simpa [add_comm, add_left_comm, add_assoc] using hadd

/-- Helper for Theorem 23.2: under the Euclidean identification, vectors whose dot products lie
below the upper directional derivative are exactly the subgradients. -/
lemma helperForTheorem_23_2_subgradient_iff_vector_linear_minorant {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (v : Fin n → ℝ) :
    dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f x ↔
      ∀ y : Fin n → ℝ, ((dotProduct y v : ℝ) : EReal) ≤ upperDirectionalDerivativeAt f x y := by
  -- Translate the dual statement back to vectors using `dotProductEquiv`.
  simpa [dotProduct_comm] using
    (helperForTheorem_23_2_subgradient_iff_dual_linear_minorant
      f hf x hx (dotProductEquiv ℝ (Fin n) v))

/-- Helper for Theorem 23.2: the support function of the vectorized subdifferential agrees with
the support of the dual subdifferential. -/
lemma helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (x : Fin n → ℝ) (y : Fin n → ℝ) :
    supportFunctionEReal ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) y =
      subdifferentialSupportAt f x y := by
  classical
  have hset :
      {z : EReal |
          ∃ v : Fin n → ℝ,
            IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) v) ∧
              z = ((dotProduct v y : ℝ) : EReal)} =
        ((fun g : Module.Dual ℝ (Fin n → ℝ) => ((g y : ℝ) : EReal)) '' subdifferentialAt f x) := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : dotProductEquiv ℝ (Fin n) v ∈ subdifferentialAt f x := hv
      have hz :
          (((dotProductEquiv ℝ (Fin n) v) y : ℝ) : EReal) = ((dotProduct v y : ℝ) : EReal) := by
        simp [dotProduct_comm]
      exact ⟨dotProductEquiv ℝ (Fin n) v, hv', hz.symm⟩
    · rintro ⟨g, hg, hz⟩
      have hv :
          IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm g)) := by
        simpa using hg
      have hdot :
          dotProduct ((dotProductEquiv ℝ (Fin n)).symm g) y = g y := by
        calc
          dotProduct ((dotProductEquiv ℝ (Fin n)).symm g) y =
              (dotProductEquiv ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm g)) y := by
                symm
                exact dotProductEquiv_apply_apply ℝ (Fin n) ((dotProductEquiv ℝ (Fin n)).symm g) y
          _ = g y := by simp
      have hz' :
          z = ((dotProduct ((dotProductEquiv ℝ (Fin n)).symm g) y : ℝ) : EReal) := by
        simpa [hdot] using hz.symm
      exact ⟨(dotProductEquiv ℝ (Fin n)).symm g, hv, hz'⟩
  -- Both sides are the same `sSup` after identifying the underlying image sets.
  rw [supportFunctionEReal, subdifferentialSupportAt]
  change sSup {z : EReal | ∃ v : Fin n → ℝ,
      IsSubgradientAt f x (dotProductEquiv ℝ (Fin n) v) ∧ z = ((dotProduct v y : ℝ) : EReal)} =
    sSup ((fun g : Module.Dual ℝ (Fin n → ℝ) => ((g y : ℝ) : EReal)) '' subdifferentialAt f x)
  exact congrArg sSup hset

/-- Helper for Theorem 23.2: the closure of the upper directional derivative is the support
function of its linear-minorant set. -/
lemma helperForTheorem_23_2_closure_eq_support_of_minorant_set {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    convexFunctionClosure (upperDirectionalDerivativeAt f x) =
      supportFunctionEReal {v : Fin n → ℝ |
        ∀ y : Fin n → ℝ, ((dotProduct y v : ℝ) : EReal) ≤ upperDirectionalDerivativeAt f x y} := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
    ⟨_hdir, hpos, hconv, hzero, _hsymm⟩
  have hnotTop : ¬ ∀ y : Fin n → ℝ, D y = (⊤ : EReal) := by
    intro htop
    have hzero_top : D 0 = (⊤ : EReal) := htop 0
    simpa [D, hzero] using hzero_top
  -- Apply the support-function representation to the sublinear function `D`.
  rcases
      clConv_eq_supportFunctionEReal_setOf_forall_dotProduct_le
        (n := n) (f := D) hpos hconv hnotTop with
    ⟨C, _hCclosed, _hCconv, hclConv, hCeq⟩
  have hclEqClosure : clConv n D = convexFunctionClosure D := by
    -- Identify `clConv` with the convex-function closure through the Fenchel biconjugate.
    calc
      clConv n D = fenchelConjugate n (fenchelConjugate n D) := by
        symm
        simpa using (fenchelConjugate_biconjugate_eq_clConv (n := n) (f := D))
      _ = convexFunctionClosure D := by
        simpa using
          (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
            (n := n) (f := D) hconv)
  calc
    convexFunctionClosure D = clConv n D := hclEqClosure.symm
    _ = supportFunctionEReal C := hclConv
    _ = supportFunctionEReal {v : Fin n → ℝ |
          ∀ y : Fin n → ℝ, ((dotProduct y v : ℝ) : EReal) ≤ D y} := by
        rw [hCeq]

/-- Theorem 23.2: Let `f` be convex and finite-valued at `x`. Then a dual vector `xStar` is a
subgradient of `f` at `x` if and only if `f'(x; y) ≥ ⟪xStar, y⟫` for every direction `y`.
Moreover, under the Euclidean identification of vectors with dual vectors, the subdifferential
`∂f(x)` is represented by a closed convex set, and the closure of the directional derivative
`y ↦ f'(x; y)` is its support function. -/
theorem subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (xStar : Module.Dual ℝ (Fin n → ℝ)) :
    (IsSubgradientAt f x xStar ↔
      ∀ y : Fin n → ℝ, ((xStar y : ℝ) : EReal) ≤ upperDirectionalDerivativeAt f x y) ∧
    IsClosed ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ∧
    Convex ℝ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) ∧
    convexFunctionClosure (upperDirectionalDerivativeAt f x) = subdifferentialSupportAt f x := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  let C : Set (Fin n → ℝ) :=
    {v : Fin n → ℝ | ∀ y : Fin n → ℝ, ((dotProduct y v : ℝ) : EReal) ≤ D y}
  have hiff :
      IsSubgradientAt f x xStar ↔
        ∀ y : Fin n → ℝ, ((xStar y : ℝ) : EReal) ≤ D y :=
    helperForTheorem_23_2_subgradient_iff_dual_linear_minorant f hf x hx xStar
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
    ⟨_hdir, hpos, hconvD, hzero, _hsymm⟩
  have hnotTop : ¬ ∀ y : Fin n → ℝ, D y = (⊤ : EReal) := by
    intro htop
    have hzero_top : D 0 = (⊤ : EReal) := htop 0
    simpa [D, hzero] using hzero_top
  rcases
      clConv_eq_supportFunctionEReal_setOf_forall_dotProduct_le
        (n := n) (f := D) hpos hconvD hnotTop with
    ⟨C0, hC0_closed, hC0_convex, _hclConv, hC0_eq⟩
  have hC0_eq_C : C0 = C := by
    simpa [C, D] using hC0_eq
  have hpreimage_eq :
      ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) = C := by
    ext v
    constructor
    · intro hv
      simpa [C, D, dotProduct_comm] using
        (helperForTheorem_23_2_subgradient_iff_vector_linear_minorant f hf x hx v).1 hv
    · intro hv
      simpa [C, D, dotProduct_comm] using
        (helperForTheorem_23_2_subgradient_iff_vector_linear_minorant f hf x hx v).2 hv
  have hclosed :
      IsClosed ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) := by
    -- The representing minorant set is closed by Corollary 13.2.1.
    have hclosedC : IsClosed C := by
      rw [← hC0_eq_C]
      exact hC0_closed
    simpa [hpreimage_eq] using hclosedC
  have hconvex :
      Convex ℝ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) := by
    -- The same representation shows convexity of the vectorized subdifferential.
    have hconvexC : Convex ℝ C := by
      rw [← hC0_eq_C]
      exact hC0_convex
    simpa [hpreimage_eq] using hconvexC
  have hclosure_minorant :
      convexFunctionClosure D = supportFunctionEReal C := by
    simpa [C, D] using
      helperForTheorem_23_2_closure_eq_support_of_minorant_set f hf x hx
  have hsupport :
      supportFunctionEReal C = subdifferentialSupportAt f x := by
    funext y
    calc
      supportFunctionEReal C y =
          supportFunctionEReal ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt f x) y := by
            rw [hpreimage_eq.symm]
      _ = subdifferentialSupportAt f x y :=
          helperForTheorem_23_2_supportFunctionEReal_preimage_subdifferential_eq f x y
  refine ⟨?_, hclosed, hconvex, ?_⟩
  · simpa [D] using hiff
  · calc
      convexFunctionClosure (upperDirectionalDerivativeAt f x) = supportFunctionEReal C := by
        simpa [D] using hclosure_minorant
      _ = subdifferentialSupportAt f x := hsupport

/-- Helper for Theorem 23.3: any actual subgradient at a finite point rules out the value `⊥`
everywhere, so convexity plus the witness `x ∈ dom f` make `f` proper. -/
lemma helperForTheorem_23_3_proper_of_mem_subdifferential {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (g : Module.Dual ℝ (Fin n → ℝ)) (hg : g ∈ subdifferentialAt f x) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
  have hconvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
    simpa [ConvexFunction] using hf
  have hxdom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
    -- The hypothesis that `f x` is finite provides the nonempty-domain witness for properness.
    refine ⟨(f x).toReal, ?_⟩
    exact epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ))) (x := x) (μ := (f x).toReal)
      (by simp) (by rw [EReal.coe_toReal hx.1 hx.2])
  refine (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
    (S := (Set.univ : Set (Fin n → ℝ))) (f := f)).2 ?_
  refine ⟨hconvOn, ⟨x, hxdom⟩, ?_⟩
  intro z hz
  have hbotz : f z ≠ (⊥ : EReal) := by
    -- The subgradient inequality compares `f z` to a finite affine lower bound, so `f z` cannot
    -- collapse to `⊥`.
    intro hzbot
    have hineq : f z ≥ f x + ((g (z - x) : ℝ) : EReal) := hg z
    have hEqBot : f x + ((g (z - x) : ℝ) : EReal) = (⊥ : EReal) := by
      exact le_antisymm (by simpa [hzbot] using hineq) bot_le
    have hrealBot : (((g z - g x : ℝ)) : EReal) = (⊥ : EReal) := by
      simpa [hx.1, hx.2] using hEqBot
    exact EReal.coe_ne_bot _ hrealBot
  exact ⟨hbotz, mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hz⟩

/-- Helper for Theorem 23.3: if `f` has no subgradient at `x`, then the upper directional
derivative `y ↦ f'(x; y)` cannot be proper. -/
lemma helperForTheorem_23_3_directionalDerivative_improper_of_empty_subdifferential {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hEmpty : ¬ Set.Nonempty (subdifferentialAt f x)) :
    ImproperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (upperDirectionalDerivativeAt f x) := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
    ⟨_hdir, _hpos, hconvD, _hzero, _hsymm⟩
  have hsubEmpty : subdifferentialAt f x = ∅ := Set.not_nonempty_iff_eq_empty.mp hEmpty
  have hclosureEq :
      convexFunctionClosure D = subdifferentialSupportAt f x := by
    -- Theorem 23.2 identifies the closure of `D` with the support of the subdifferential.
    simpa [D] using
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        f hf x hx (0 : Module.Dual ℝ (Fin n → ℝ))).2.2.2
  have hclosureBot : convexFunctionClosure D = fun _ => (⊥ : EReal) := by
    -- With no subgradients available, the support is the supremum over the empty image.
    funext y
    have hy :
        convexFunctionClosure D y = (⊥ : EReal) := by
      rw [hclosureEq, subdifferentialSupportAt]
      simp [hsubEmpty]
    simpa using hy
  have hnotProper : ¬ ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) D := by
    intro hproperD
    have hproperClosure :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (convexFunctionClosure D) :=
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
        (f := D) hproperD).1.2
    -- A proper convex function cannot take the value `⊥` anywhere on its ambient set.
    have hneBot0 : convexFunctionClosure D 0 ≠ (⊥ : EReal) := hproperClosure.2.2 0 (by simp)
    exact hneBot0 (by simpa [hclosureBot])
  refine ⟨?_, hnotProper⟩
  simpa [ConvexFunction] using hconvD

/-- Helper for Theorem 23.3: if a convex directional-derivative function satisfies the symmetry
inequality and is `⊥` at `y`, then it is `⊤` at the opposite direction. -/
lemma helperForTheorem_23_3_opposite_upperDerivative_eq_top_of_eq_bot {n : ℕ}
    (D : (Fin n → ℝ) → EReal)
    (hsymm : ∀ y : Fin n → ℝ, -(D (-y)) ≤ D y)
    (y : Fin n → ℝ) (hybot : D y = (⊥ : EReal)) :
    D (-y) = (⊤ : EReal) := by
  by_cases htop : D (-y) = (⊤ : EReal)
  · exact htop
  by_cases hbot : D (-y) = (⊥ : EReal)
  · have : (⊤ : EReal) ≤ (⊥ : EReal) := by
      simpa [hybot, hbot] using hsymm y
    exact (bot_lt_top.not_ge this).elim
  have hfinite :
      - (D (-y)) = (((-(D (-y)).toReal : ℝ)) : EReal) := by
    rw [← EReal.coe_toReal htop hbot]
    simp
  have : (((-(D (-y)).toReal : ℝ)) : EReal) ≤ (⊥ : EReal) := by
    simpa [hybot, hfinite] using hsymm y
  exact (EReal.bot_lt_coe (-(D (-y)).toReal)).not_ge this |> False.elim

/-- Helper for Theorem 23.3: every direction from `x` to a point of `ri (dom f)` lies in
`ri (dom (y ↦ f'(x; y)))`. -/
lemma helperForTheorem_23_3_directionToRi_mem_ri_effectiveDomain_directionalDerivative {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x z : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal))
    (hzri : z ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    z - x ∈ euclideanRelativeInterior_fin n
      (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (upperDirectionalDerivativeAt f x)) := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  let domf : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f
  let domD : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) D
  let A : Set (Fin n → ℝ) := domf + ({-x} : Set (Fin n → ℝ))
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
    ⟨hdir, _hpos, _hconvD, _hzero, _hsymm⟩
  have hdomfConv : Convex ℝ domf :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hf
  have hAri :
      z - x ∈ euclideanRelativeInterior_fin n A := by
    -- Translate the relative interior point in `dom f` by the singleton `{-x}`.
    change z - x ∈ euclideanRelativeInterior_fin n (domf + ({-x} : Set (Fin n → ℝ)))
    rw [euclideanRelativeInterior_fin_add_eq_and_closure_add_superset hdomfConv
      (by simpa using convex_singleton (-x))]
    refine ⟨z, hzri, -x, ?_, ?_⟩
    · simpa [euclideanRelativeInterior_fin_singleton]
    · simp [sub_eq_add_neg]
  have hAsub : A ⊆ domD := by
    intro y hy
    rcases hy with ⟨u, hu, v, hv, rfl⟩
    have hvx : v = -x := by simpa using hv
    subst hvx
    have hy_lt_top : D (u - x) < (⊤ : EReal) := by
      -- Evaluating the difference quotient at `t = 1` shows every translated domain point lies in
      -- the effective domain of `D`.
      have hDu_le :
          D (u - x) ≤ directionalDifferenceQuotientAt f x (u - x) 1 := by
        rcases hdir (u - x) with ⟨_hmono, _htend, hsInfEq⟩
        have hQ_bdd :
            BddBelow ((Set.Ioi (0 : ℝ)).image fun t : ℝ =>
              directionalDifferenceQuotientAt f x (u - x) t) := by
          refine ⟨⊥, ?_⟩
          intro q hq
          simp
        have hle' :
            upperDirectionalDerivativeAt f x (u - x) ≤
              directionalDifferenceQuotientAt f x (u - x) 1 := by
          rw [hsInfEq]
          exact csInf_le hQ_bdd ⟨1, by simpa, rfl⟩
        simpa [D] using hle'
      have hquot_lt_top :
          directionalDifferenceQuotientAt f x (u - x) 1 < (⊤ : EReal) := by
        by_cases huBot : f u = (⊥ : EReal)
        · simpa [directionalDifferenceQuotientAt, huBot, one_smul, sub_eq_add_neg, add_assoc,
            add_left_comm, add_comm, hx.1, hx.2]
        · have huTop : f u ≠ (⊤ : EReal) :=
            mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hu
          have : directionalDifferenceQuotientAt f x (u - x) 1 =
              f u - f x := by
            simp [directionalDifferenceQuotientAt, one_smul, sub_eq_add_neg, add_assoc,
              add_left_comm, add_comm]
          rw [this]
          exact lt_of_le_of_ne le_top
            (by
              rw [sub_eq_add_neg]
              exact EReal.add_ne_top huTop (by simpa using hx.2))
      exact lt_of_le_of_lt hDu_le hquot_lt_top
    refine ⟨(D (u - x)).toReal, ?_⟩
    exact epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ))) (x := u - x)
      (μ := (D (u - x)).toReal) (by simp) (by
        by_cases hbot : D (u - x) = (⊥ : EReal)
        · simp [hbot]
        · have htop : D (u - x) ≠ (⊤ : EReal) := ne_of_lt hy_lt_top
          rw [EReal.coe_toReal htop hbot])
  have hzero_mem_A : (0 : Fin n → ℝ) ∈ A := by
    refine ⟨x, ?_, -x, by simp, ?_⟩
    · refine ⟨(f x).toReal, ?_⟩
      exact epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ))) (x := x)
        (μ := (f x).toReal) (by simp) (by rw [EReal.coe_toReal hx.1 hx.2])
    · simp
  have haff : affineSpan ℝ A = affineSpan ℝ domD := by
    apply le_antisymm
    · exact affineSpan_mono ℝ hAsub
    · refine affineSpan_le.2 ?_
      intro y hy
      have hy_lt : D y < (⊤ : EReal) := by
        simpa [domD, effectiveDomain_eq] using hy
      rcases hdir y with ⟨_hmono, _htend, hsInfEq⟩
      let Q : Set EReal := (Set.Ioi (0 : ℝ)).image fun t : ℝ =>
        directionalDifferenceQuotientAt f x y t
      have hQ_nonempty : Q.Nonempty := by
        refine ⟨directionalDifferenceQuotientAt f x y 1, ⟨1, by simpa, rfl⟩⟩
      have hsInf_lt_top : sInf Q < (⊤ : EReal) := by
        rw [← hsInfEq]
        exact hy_lt
      rcases exists_lt_of_csInf_lt hQ_nonempty hsInf_lt_top with ⟨q, hqQ, hq_lt_top⟩
      rcases hqQ with ⟨t, ht, rfl⟩
      have hxty_dom : x + t • y ∈ domf := by
        -- A finite difference quotient at some positive step forces the corresponding displaced
        -- point to lie in `dom f`.
        by_cases htop : f (x + t • y) = (⊤ : EReal)
        · have : directionalDifferenceQuotientAt f x y t = (⊤ : EReal) := by
            rw [directionalDifferenceQuotientAt, htop]
            simp [hx.1]
            exact EReal.top_div_of_pos_ne_top (by exact_mod_cast ht) (by simp)
          exact (this.not_lt hq_lt_top).elim
        · refine ⟨(f (x + t • y)).toReal, ?_⟩
          exact epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ))) (x := x + t • y)
            (μ := (f (x + t • y)).toReal) (by simp) (by
              by_cases hbot : f (x + t • y) = (⊥ : EReal)
              · simp [hbot]
              · rw [EReal.coe_toReal htop hbot])
      have hty_mem_A : t • y ∈ A := by
        refine ⟨x + t • y, hxty_dom, -x, by simp, ?_⟩
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      have hty_vec : t • y ∈ AffineSubspace.direction (affineSpan ℝ A) := by
        rw [direction_affineSpan]
        simpa using vsub_mem_vectorSpan ℝ hty_mem_A hzero_mem_A
      have hy_vec : y ∈ AffineSubspace.direction (affineSpan ℝ A) := by
        rw [direction_affineSpan] at hty_vec ⊢
        have ht0 : t ≠ 0 := by
          exact (show 0 < t by simpa using ht).ne'
        have : y = (t⁻¹ : ℝ) • (t • y) := by
          simp [smul_smul, ht0]
        rw [this]
        exact (vectorSpan ℝ A).smul_mem (t⁻¹) hty_vec
      have hzero_aff : (0 : Fin n → ℝ) ∈ affineSpan ℝ A := mem_affineSpan ℝ hzero_mem_A
      simpa using
        (AffineSubspace.vadd_mem_of_mem_direction hy_vec hzero_aff :
          y +ᵥ (0 : Fin n → ℝ) ∈ affineSpan ℝ A)
  have hAsub' : e.symm '' A ⊆ e.symm '' domD := by
    intro u hu
    rcases hu with ⟨v, hv, rfl⟩
    exact ⟨v, hAsub hv, rfl⟩
  have haff' : affineSpan ℝ (e.symm '' A) = affineSpan ℝ (e.symm '' domD) := by
    calc
      affineSpan ℝ (e.symm '' A) = (affineSpan ℝ A).map e.symm.toAffineMap := by
        symm
        simpa using (AffineSubspace.map_span (k := ℝ) (f := e.symm.toAffineMap) (s := A))
      _ = (affineSpan ℝ domD).map e.symm.toAffineMap := by rw [haff]
      _ = affineSpan ℝ (e.symm '' domD) := by
        simpa using (AffineSubspace.map_span (k := ℝ) (f := e.symm.toAffineMap) (s := domD))
  have hAri' :
      e.symm (z - x) ∈ euclideanRelativeInterior n (e.symm '' A) :=
    (mem_euclideanRelativeInterior_fin_iff (n := n) (C := A) (x := z - x)).1 hAri
  have hDomDri' :
      e.symm (z - x) ∈ euclideanRelativeInterior n (e.symm '' domD) :=
    (euclideanRelativeInterior_mono_of_subset_of_affineSpan_eq hAsub' haff') hAri'
  exact
    (mem_euclideanRelativeInterior_fin_iff (n := n) (C := domD) (x := z - x)).2 hDomDri'

-- Proof sketch: apply Theorem 23.2 to identify subdifferentiability with the existence of a
-- supporting affine functional at `x`; this yields properness. If no subgradient exists, then the
-- directional derivative cannot be bounded below by any linear functional, forcing a direction of
-- bilateral blow-up, and for any `z` in the relative interior of the effective domain the same
-- blow-up occurs along the direction `z - x`.
/-- Theorem 23.3: Let `f` be convex and finite-valued at `x`. If `f` is subdifferentiable at `x`,
then `f` is proper. If `f` is not subdifferentiable at `x`, then there exists a direction `y`
such that `f'(x; y) = -∞` and `f'(x; -y) = +∞`. Moreover, for every
`z ∈ ri (dom f)`, the same conclusion holds for `y = z - x`. -/
theorem proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (hf : ConvexFunction f) (x : Fin n → ℝ)
    (hx : f x ≠ (⊤ : EReal) ∧ f x ≠ (⊥ : EReal)) :
    (Set.Nonempty (subdifferentialAt f x) →
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f) ∧
    (¬ Set.Nonempty (subdifferentialAt f x) →
      (∃ y : Fin n → ℝ,
        upperDirectionalDerivativeAt f x y = (⊥ : EReal) ∧
          upperDirectionalDerivativeAt f x (-y) = (⊤ : EReal)) ∧
      ∀ z : Fin n → ℝ,
        z ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) →
          upperDirectionalDerivativeAt f x (z - x) = (⊥ : EReal) ∧
            upperDirectionalDerivativeAt f x (x - z) = (⊤ : EReal)) := by
  let D : (Fin n → ℝ) → EReal := upperDirectionalDerivativeAt f x
  rcases convex_directionalDerivative_monotone_exists_and_sublinear f hf x hx with
    ⟨_hdir, _hpos, _hconvD, _hzero, hsymmD⟩
  refine ⟨?_, ?_⟩
  · intro hsub
    -- A single subgradient is enough to upgrade the finite-point hypothesis to properness.
    rcases hsub with ⟨g, hg⟩
    exact helperForTheorem_23_3_proper_of_mem_subdifferential f hf x hx g hg
  · intro hEmpty
    have himproperD :
        ImproperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) D :=
      helperForTheorem_23_3_directionalDerivative_improper_of_empty_subdifferential f hf x hx hEmpty
    have hpreimage_domD :
        ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) =
          ((fun a : Fin n → ℝ => (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm a) ''
            effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) := by
      ext u
      constructor
      · intro hu
        exact ⟨(u : Fin n → ℝ), hu, by simp⟩
      · rintro ⟨v, hv, rfl⟩
        simpa using hv
    have hdomfConv :
        Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
      effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hf
    have hxdom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) f := by
      refine ⟨(f x).toReal, ?_⟩
      exact epigraph_mem_of_le_aux (S := (Set.univ : Set (Fin n → ℝ))) (x := x)
        (μ := (f x).toReal) (by simp) (by rw [EReal.coe_toReal hx.1 hx.2])
    rcases
        helperForText_19_0_7_exists_mem_euclideanRelativeInterior_fin_of_convex_nonempty
          hdomfConv ⟨x, hxdom⟩ with
      ⟨z0, hz0ri⟩
    have hz0riD :
        z0 - x ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) :=
      helperForTheorem_23_3_directionToRi_mem_ri_effectiveDomain_directionalDerivative
        f hf x z0 hx hz0ri
    have hz0bot :
        D (z0 - x) = (⊥ : EReal) := by
      -- Theorem 7.2 now applies to the improper convex function `D`.
      have hz0riD' :
          (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm (z0 - x) ∈
            euclideanRelativeInterior n
              ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) := by
        rw [hpreimage_domD]
        simpa using
          ((mem_euclideanRelativeInterior_fin_iff (n := n)
            (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) (x := z0 - x)).1 hz0riD)
      simpa [D] using
        improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain
          (f := D) himproperD ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm (z0 - x))
          hz0riD'
    have hz0top :
        D (-(z0 - x)) = (⊤ : EReal) :=
      helperForTheorem_23_3_opposite_upperDerivative_eq_top_of_eq_bot D hsymmD (z0 - x) hz0bot
    refine ⟨⟨z0 - x, hz0bot, ?_⟩, ?_⟩
    · simpa [D, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hz0top
    · intro z hzri
      have hzriD :
          z - x ∈ euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) :=
        helperForTheorem_23_3_directionToRi_mem_ri_effectiveDomain_directionalDerivative
          f hf x z hx hzri
      have hzbot :
          D (z - x) = (⊥ : EReal) := by
        -- The same relative-interior transfer works for every `z ∈ ri (dom f)`.
        have hzriD' :
            (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm (z - x) ∈
              euclideanRelativeInterior n
                ((fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) ⁻¹'
                  effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) := by
          rw [hpreimage_domD]
          simpa using
            ((mem_euclideanRelativeInterior_fin_iff (n := n)
              (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) D) (x := z - x)).1 hzriD)
        simpa [D] using
          improperConvexFunctionOn_eq_bot_on_ri_effectiveDomain
            (f := D) himproperD ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm (z - x))
            hzriD'
      have hztop :
          D (-(z - x)) = (⊤ : EReal) :=
        helperForTheorem_23_3_opposite_upperDerivative_eq_top_of_eq_bot D hsymmD (z - x) hzbot
      refine ⟨hzbot, ?_⟩
      simpa [D, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hztop

end Section23
end Chap05
