/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section29_part10

open scoped Pointwise

section Chap06
section Section29

local notation "ConvexBifunction" => BundledConvexBifunction

/-- Helper for Corollary 6.29.8: bundle the Section 29 closure back into a convex bifunction. -/
noncomputable def helperForCorollary_6_29_8_closureConvexBifunction {m n : ℕ}
    (F : ConvexBifunction m n) : ConvexBifunction m n := by
  refine ⟨helperForTheorem_6_29_4_define_section29_bifunctionClosure F, ?_⟩
  -- The packed graph-function closure is convex, so every `(u, x)` slice is again a convex
  -- bifunction in the original coordinates.
  let g : (Fin (m + n) → ℝ) → EReal := helperForTheorem_6_29_4_coordinateGraphFunction F
  have hclConv : ConvexERealFunction (convexFunctionClosure g) := by
    by_cases hgproper :
        ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) g
    · exact
        (helperForText_26_4_0_2_properConvexERealFunction_of_properConvexFunctionOn
          ((convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
            (f := g) hgproper).1.2)).2
    · have hgconv : ConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) g := by
        simpa [ConvexFunction] using helperForTheorem_6_29_4_coordinateGraphFunction_convex F
      have hgimproper : ImproperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) g := by
        exact ⟨hgconv, hgproper⟩
      rcases improperConvexFunctionOn_cases_epigraph_empty_or_bot hgimproper with hEmpty | hBot
      · have htop : ∀ z : Fin (m + n) → ℝ, g z = (⊤ : EReal) := by
          intro z
          exact epigraph_empty_imp_forall_top (S := (Set.univ : Set (Fin (m + n) → ℝ))) (f := g)
            hEmpty z (by simp)
        have htopEq : g = (fun _ => (⊤ : EReal)) := by
          funext z
          exact htop z
        have hclTop : convexFunctionClosure g = (fun _ => (⊤ : EReal)) := by
          simpa [htopEq] using (convexFunctionClosure_const_top (n := m + n))
        intro x y a b ha hb hab
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          simp [hclTop, ha0, hb1]
        · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have hmulTop : ((a : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
            exact EReal.mul_top_of_pos (by exact_mod_cast haPos)
          have hmulNeBot : ((b : ℝ) : EReal) * (⊤ : EReal) ≠ (⊥ : EReal) := by
            exact (EReal.mul_ne_bot ((b : ℝ) : EReal) (⊤ : EReal)).2
              ⟨Or.inl (by simp), Or.inr (by simp), Or.inl (by simp), Or.inl (by exact_mod_cast hb)⟩
          have hrhs :
              ((a : ℝ) : EReal) * (⊤ : EReal) + ((b : ℝ) : EReal) * (⊤ : EReal) = ⊤ := by
            calc
              ((a : ℝ) : EReal) * (⊤ : EReal) + ((b : ℝ) : EReal) * (⊤ : EReal)
                  = ⊤ + ((b : ℝ) : EReal) * (⊤ : EReal) := by rw [hmulTop]
              _ = ⊤ := EReal.top_add_of_ne_bot hmulNeBot
          simpa [hclTop, hrhs] using (le_rfl : (⊤ : EReal) ≤ ⊤)
      · rcases hBot with ⟨z, -, hzBot⟩
        have hclBot : convexFunctionClosure g = (fun _ => (⊥ : EReal)) :=
          convexFunctionClosure_eq_bot_of_exists_bot (f := g) ⟨z, hzBot⟩
        intro x y a b ha hb hab
        simp [hclBot]
  intro p q a b ha hb hab
  have happ :
      a • Fin.append p.1 p.2 + b • Fin.append q.1 q.2 =
        Fin.append (a • p.1 + b • q.1) (a • p.2 + b • q.2) := by
    ext i
    cases i using Fin.addCases with
    | left i =>
        simp [Fin.append_left, Pi.add_apply, Pi.smul_apply]
    | right i =>
        simp [Fin.append_right, Pi.add_apply, Pi.smul_apply]
  -- Repack the two product-space points and apply convexity of the closed graph function.
  simpa [graphFunction, helperForTheorem_6_29_4_define_section29_bifunctionClosure,
    happ] using
    hclConv (x := Fin.append p.1 p.2) (y := Fin.append q.1 q.2) ha hb hab

/-- Helper for Corollary 6.29.8: in the proper branch, the Section 29 closure has the same
relative interior of the perturbation domain, so strong consistency transfers. -/
lemma helperForCorollary_6_29_8_strongConsistency_of_closureProgram_of_proper
    {m n : ℕ} (F : ConvexBifunction m n) (hproper : IsProperBifunction F.1)
    (hstrong : generalizedConvexProgramStronglyConsistent F) :
    generalizedConvexProgramStronglyConsistent
      (helperForCorollary_6_29_8_closureConvexBifunction F) := by
  let clF := helperForCorollary_6_29_8_closureConvexBifunction F
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  let domF : Set (EuclideanSpace ℝ (Fin m)) := e.symm '' bifunctionEffectiveDomain F.1
  let domCl : Set (EuclideanSpace ℝ (Fin m)) := e.symm '' bifunctionEffectiveDomain clF.1
  have hdom_left :
      bifunctionEffectiveDomain F.1 ⊆ bifunctionEffectiveDomain clF.1 := by
    -- The closure graph always projects onto a superset of the original perturbation domain.
    simpa [clF, helperForCorollary_6_29_8_closureConvexBifunction] using
      helperForTheorem_6_29_4_projection_domain_inclusion_left F
  have hdom_right :
      bifunctionEffectiveDomain clF.1 ⊆ closure (bifunctionEffectiveDomain F.1) := by
    -- Properness is the hypothesis that upgrades Theorem 6.29.4 to a closure-domain sandwich.
    simpa [clF, helperForCorollary_6_29_8_closureConvexBifunction] using
      ((theorem_29_4_convex_bifunction_closure_section_and_domain F).2.2 hproper).2
  have hdomF_sub : domF ⊆ domCl := by
    intro z hz
    rcases hz with ⟨u, hu, rfl⟩
    exact ⟨u, hdom_left hu, rfl⟩
  have himageClosure :
      e.symm '' closure (bifunctionEffectiveDomain F.1) = closure domF := by
    -- Transport closure across the Euclidean coordinate equivalence.
    simpa [domF, e] using
      (Homeomorph.image_closure (h := e.symm.toHomeomorph) (s := bifunctionEffectiveDomain F.1))
  have hdomCl_sub : domCl ⊆ closure domF := by
    intro z hz
    rcases hz with ⟨u, hu, rfl⟩
    have huClosure :
        e.symm u ∈ e.symm '' closure (bifunctionEffectiveDomain F.1) := by
      exact ⟨u, hdom_right hu, rfl⟩
    simpa [himageClosure] using huClosure
  have hconv_domF : Convex ℝ domF := by
    -- Proposition 6.29.2 makes `dom F` convex, and linear equivalences preserve convexity.
    simpa [domF, e] using
      ((proposition_29_2 (F := F.1) F.2).2.2).linear_image e.symm.toLinearMap
  have hconv_domCl : Convex ℝ domCl := by
    -- The same convex-domain argument applies to the closure bifunction.
    simpa [domCl, e] using
      ((proposition_29_2 (F := clF.1) clF.2).2.2).linear_image e.symm.toLinearMap
  have hclosure : closure domCl = closure domF :=
    closure_domcl_eq_domf (domf := domF) (domcl := domCl) hdomF_sub hdomCl_sub
  have hri_eq :
      euclideanRelativeInterior m domCl = euclideanRelativeInterior m domF :=
    ri_domcl_eq_domf (domf := domF) (domcl := domCl) hconv_domF hconv_domCl hclosure
  have hstrongE :
      e.symm (0 : Fin m → ℝ) ∈ euclideanRelativeInterior m domF := by
    -- Rewrite the original strong-consistency statement in Euclidean coordinates.
    simpa [domF, e] using
      (mem_euclideanRelativeInterior_fin_iff
        (n := m) (C := bifunctionEffectiveDomain F.1) (x := (0 : Fin m → ℝ))).1 hstrong
  have hstrongClE :
      e.symm (0 : Fin m → ℝ) ∈ euclideanRelativeInterior m domCl := by
    -- The closure-domain sandwich identifies the two relative interiors.
    simpa [hri_eq] using hstrongE
  -- Translate the Euclidean relative-interior conclusion back to `Fin m → ℝ`.
  exact
    (mem_euclideanRelativeInterior_fin_iff
      (n := m) (C := bifunctionEffectiveDomain clF.1) (x := (0 : Fin m → ℝ))).2
      (by simpa [domCl, e] using hstrongClE)

/-- Helper for Corollary 6.29.8: strong consistency plus nonproperness forces the packed graph
closure to collapse to the constant `⊥` function. -/
lemma helperForCorollary_6_29_8_coordinateGraphClosure_eq_bot_of_nonproperStrongConsistency
    {m n : ℕ} (F : ConvexBifunction m n) (hnotproper : ¬ IsProperBifunction F.1)
    (hstrong : generalizedConvexProgramStronglyConsistent F) :
    convexFunctionClosure (helperForTheorem_6_29_4_coordinateGraphFunction F) =
      (fun _ => (⊥ : EReal)) := by
  rcases
      helperForTheorem_6_29_4_section_botWitness_of_nonproper_on_riProjection
        (F := F) hnotproper hstrong with
    ⟨x0, hx0bot⟩
  -- The origin section already contains a `⊥` value, so the whole packed closure collapses.
  exact
    convexFunctionClosure_eq_bot_of_exists_bot
      (f := helperForTheorem_6_29_4_coordinateGraphFunction F)
      ⟨Fin.append 0 x0, by
        simpa [helperForTheorem_6_29_4_coordinateGraphFunction] using hx0bot⟩

/-- Helper for Corollary 6.29.8: in the nonproper strongly consistent branch, the Section 29
closure bifunction is everywhere `⊥`. -/
lemma helperForCorollary_6_29_8_closureBifunction_eq_bot_of_nonproperStrongConsistency
    {m n : ℕ} (F : ConvexBifunction m n) (hnotproper : ¬ IsProperBifunction F.1)
    (hstrong : generalizedConvexProgramStronglyConsistent F) :
    ∀ u x,
      (helperForCorollary_6_29_8_closureConvexBifunction F).1 u x = (⊥ : EReal) := by
  have hgraphClosure :
      convexFunctionClosure (helperForTheorem_6_29_4_coordinateGraphFunction F) =
        (fun _ => (⊥ : EReal)) :=
    helperForCorollary_6_29_8_coordinateGraphClosure_eq_bot_of_nonproperStrongConsistency
      F hnotproper hstrong
  intro u x
  -- Evaluate the collapsed packed closure on the displayed `(u, x)` fiber point.
  simpa [helperForCorollary_6_29_8_closureConvexBifunction,
    helperForTheorem_6_29_4_define_section29_bifunctionClosure, hgraphClosure]

/-- Helper for Corollary 6.29.8: in the nonproper strongly consistent branch, the closure
program has full perturbation domain and is therefore strongly consistent. -/
lemma helperForCorollary_6_29_8_strongConsistency_of_closureProgram_of_nonproper
    {m n : ℕ} (F : ConvexBifunction m n) (hnotproper : ¬ IsProperBifunction F.1)
    (hstrong : generalizedConvexProgramStronglyConsistent F) :
    generalizedConvexProgramStronglyConsistent
      (helperForCorollary_6_29_8_closureConvexBifunction F) := by
  let clF := helperForCorollary_6_29_8_closureConvexBifunction F
  have hbotAll :
      ∀ u x, clF.1 u x = (⊥ : EReal) := by
    simpa [clF] using
      helperForCorollary_6_29_8_closureBifunction_eq_bot_of_nonproperStrongConsistency
        F hnotproper hstrong
  have hdomUniv : bifunctionEffectiveDomain clF.1 = Set.univ := by
    ext u
    constructor
    · intro _
      simp
    · intro _
      rw [helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue]
      refine ⟨0, ?_⟩
      -- Every section point already has value `⊥`, hence is certainly finite.
      simpa [hbotAll u 0]
  have hzeroInt : (0 : Fin m → ℝ) ∈ interior (Set.univ : Set (Fin m → ℝ)) := by
    simp
  have hzeroRi :
      (0 : Fin m → ℝ) ∈ euclideanRelativeInterior_fin m (Set.univ : Set (Fin m → ℝ)) :=
    helperForTheorem_23_4_mem_relativeInterior_of_mem_interior
      (n := m) (C := (Set.univ : Set (Fin m → ℝ))) hzeroInt
  -- Rewrite the full-domain conclusion back into the definition of strong consistency.
  simpa [generalizedConvexProgramStronglyConsistent, clF, hdomUniv] using hzeroRi

/-- Helper for Corollary 6.29.8: in the nonproper branch, the origin section already attains
`⊥`, so the optimal value collapses to `⊥`. -/
lemma helperForCorollary_6_29_8_optimalValue_eq_bot_of_nonproper
    {m n : ℕ} (F : ConvexBifunction m n) (hnotproper : ¬ IsProperBifunction F.1)
    (hstrong : generalizedConvexProgramStronglyConsistent F) :
    generalizedConvexProgramOptimalValue F = (⊥ : EReal) := by
  rcases
      helperForTheorem_6_29_4_section_botWitness_of_nonproper_on_riProjection
        (F := F) hnotproper hstrong with
    ⟨x0, hx0bot⟩
  have hp0bot :
      generalizedConvexProgramPerturbationFunction F 0 = (⊥ : EReal) := by
    -- The origin perturbation infimum sees the `⊥` witness from the origin section.
    refine le_antisymm ?_ bot_le
    calc
      generalizedConvexProgramPerturbationFunction F 0 ≤ F.1 0 x0 := by
        exact sInf_le ⟨x0, rfl⟩
      _ = (⊥ : EReal) := hx0bot
  -- Theorem 6.29.1 identifies the optimal value with the origin perturbation value.
  calc
    generalizedConvexProgramOptimalValue F =
        generalizedConvexProgramPerturbationFunction F 0 :=
      helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero F
    _ = (⊥ : EReal) := hp0bot

/-- Helper for Corollary 6.29.8: in the proper branch, nonfiniteness of the optimal value can
only mean `⊥`, because strong consistency rules out `⊤`. -/
lemma helperForCorollary_6_29_8_optimalValue_eq_bot_of_proper_not_finite
    {m n : ℕ} (F : ConvexBifunction m n) (_hproper : IsProperBifunction F.1)
    (hstrong : generalizedConvexProgramStronglyConsistent F)
    (hnotfinite : ¬ IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    generalizedConvexProgramOptimalValue F = (⊥ : EReal) := by
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  have h0riE :
      e.symm (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior m (e.symm '' bifunctionEffectiveDomain F.1) := by
    -- Translate strong consistency into the Euclidean-coordinate relative interior statement.
    exact
      (mem_euclideanRelativeInterior_fin_iff
        (n := m) (C := bifunctionEffectiveDomain F.1) (x := (0 : Fin m → ℝ))).1 hstrong
  have h0domE : e.symm (0 : Fin m → ℝ) ∈ e.symm '' bifunctionEffectiveDomain F.1 := by
    -- Relative-interior points lie in the underlying set itself.
    exact (euclideanRelativeInterior_subset_closure m (e.symm '' bifunctionEffectiveDomain F.1)).1
      h0riE
  have h0dom : (0 : Fin m → ℝ) ∈ bifunctionEffectiveDomain F.1 := by
    simpa [e] using h0domE
  have hconsistent : generalizedConvexProgramConsistent F := by
    rw [helperForLemma_6_29_6_consistent_iff_exists_finiteObjectiveValue]
    rcases
        (helperForProposition_6_29_2_mem_bifunctionEffectiveDomain_iff_exists_finiteSectionValue
          (F := F.1) (u := (0 : Fin m → ℝ))).1 h0dom with
      ⟨x0, hx0⟩
    -- The domain witness at `u = 0` is exactly a feasible point with finite objective value.
    exact ⟨x0, by simpa [generalizedConvexProgramObjective] using hx0⟩
  have hopt_ne_top : generalizedConvexProgramOptimalValue F ≠ (⊤ : EReal) := by
    exact lt_top_iff_ne_top.mp
      ((generalizedConvexProgramConsistent_iff_optimalValue_lt_top F).1 hconsistent)
  by_cases hbot : generalizedConvexProgramOptimalValue F = (⊥ : EReal)
  · exact hbot
  · have hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F) :=
      ⟨hopt_ne_top, hbot⟩
    exact False.elim (hnotfinite hfinite)

/-- Helper for Corollary 6.29.8: in the proper branch, the closure-program perturbation and the
original perturbation have the same convex closure. -/
lemma helperForCorollary_6_29_8_closurePerturbationClosure_eq_perturbationClosure_of_proper
    {m n : ℕ} (F : ConvexBifunction m n) (hproper : IsProperBifunction F.1) :
    let clF := helperForCorollary_6_29_8_closureConvexBifunction F
    convexFunctionClosure (generalizedConvexProgramPerturbationFunction clF) =
      convexFunctionClosure (generalizedConvexProgramPerturbationFunction F) := by
  let clF := helperForCorollary_6_29_8_closureConvexBifunction F
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  let pcl : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction clF
  let e : EuclideanSpace ℝ (Fin m) ≃L[ℝ] (Fin m → ℝ) :=
    EuclideanSpace.equiv (ι := Fin m) (𝕜 := ℝ)
  let domF : Set (EuclideanSpace ℝ (Fin m)) := e.symm '' bifunctionEffectiveDomain F.1
  let domCl : Set (EuclideanSpace ℝ (Fin m)) := e.symm '' bifunctionEffectiveDomain clF.1
  let domp : Set (EuclideanSpace ℝ (Fin m)) :=
    (fun x : EuclideanSpace ℝ (Fin m) => (x : Fin m → ℝ)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p
  let dompcl : Set (EuclideanSpace ℝ (Fin m)) :=
    (fun x : EuclideanSpace ℝ (Fin m) => (x : Fin m → ℝ)) ⁻¹'
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) pcl
  have hpConv : ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).1
  have hpclConv : ConvexFunction pcl :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker clF).1
  have hpDom :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = bifunctionEffectiveDomain F.1 := by
    -- Theorem 6.29.1 rewrites the perturbation effective domain as `dom F`.
    calc
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) p = erealDom p := by
        ext u
        simp [p, effectiveDomain_eq, erealDom]
      _ = bifunctionEffectiveDomain F.1 :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker F).2.1
  have hpclDom :
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) pcl = bifunctionEffectiveDomain clF.1 := by
    -- The same domain rewrite applies to the closure program.
    calc
      effectiveDomain (Set.univ : Set (Fin m → ℝ)) pcl = erealDom pcl := by
        ext u
        simp [pcl, effectiveDomain_eq, erealDom]
      _ = bifunctionEffectiveDomain clF.1 :=
        (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker clF).2.1
  have hdom_left :
      bifunctionEffectiveDomain F.1 ⊆ bifunctionEffectiveDomain clF.1 := by
    -- Properness puts the closure-program domain above the original perturbation domain.
    simpa [clF, helperForCorollary_6_29_8_closureConvexBifunction] using
      helperForTheorem_6_29_4_projection_domain_inclusion_left F
  have hdom_right :
      bifunctionEffectiveDomain clF.1 ⊆ closure (bifunctionEffectiveDomain F.1) := by
    -- Theorem 6.29.4 provides the upper closure-domain bound in the proper branch.
    simpa [clF, helperForCorollary_6_29_8_closureConvexBifunction] using
      ((theorem_29_4_convex_bifunction_closure_section_and_domain F).2.2 hproper).2
  have hdomF_sub : domF ⊆ domCl := by
    intro z hz
    rcases hz with ⟨u, hu, rfl⟩
    exact ⟨u, hdom_left hu, rfl⟩
  have himageClosure :
      e.symm '' closure (bifunctionEffectiveDomain F.1) = closure domF := by
    -- Transport closure through the Euclidean coordinate equivalence.
    simpa [domF, e] using
      (Homeomorph.image_closure (h := e.symm.toHomeomorph) (s := bifunctionEffectiveDomain F.1))
  have hdomCl_sub : domCl ⊆ closure domF := by
    intro z hz
    rcases hz with ⟨u, hu, rfl⟩
    have huClosure :
        e.symm u ∈ e.symm '' closure (bifunctionEffectiveDomain F.1) := by
      exact ⟨u, hdom_right hu, rfl⟩
    simpa [himageClosure] using huClosure
  have hconv_domF : Convex ℝ domF := by
    -- Convexity of `dom F` transports through the Euclidean equivalence.
    simpa [domF, e] using
      ((proposition_29_2 (F := F.1) F.2).2.2).linear_image e.symm.toLinearMap
  have hconv_domCl : Convex ℝ domCl := by
    -- The closure bifunction enjoys the same convex-domain property.
    simpa [domCl, e] using
      ((proposition_29_2 (F := clF.1) clF.2).2.2).linear_image e.symm.toLinearMap
  have hclosure : closure domCl = closure domF :=
    closure_domcl_eq_domf (domf := domF) (domcl := domCl) hdomF_sub hdomCl_sub
  have hri_eq :
      euclideanRelativeInterior m domCl = euclideanRelativeInterior m domF :=
    ri_domcl_eq_domf (domf := domF) (domcl := domCl) hconv_domF hconv_domCl hclosure
  have hdomp_eq : domp = domF := by
    -- Rewrite the theorem-side effective-domain preimage into the same Euclidean image set.
    ext x
    constructor
    · intro hx
      exact ⟨x.ofLp, by simpa [domp, hpDom] using hx, by simp [e]⟩
    · rintro ⟨u, hu, huEq⟩
      simpa [domp, hpDom, e] using huEq ▸ hu
  have hdompcl_eq : dompcl = domCl := by
    -- The closure-program perturbation has the analogous Euclideanized domain.
    ext x
    constructor
    · intro hx
      exact ⟨x.ofLp, by simpa [dompcl, hpclDom] using hx, by simp [e]⟩
    · rintro ⟨u, hu, huEq⟩
      simpa [dompcl, hpclDom, e] using huEq ▸ hu
  have hagree :
      ∀ x ∈ euclideanRelativeInterior m domp,
        p (x : Fin m → ℝ) = pcl (x : Fin m → ℝ) := by
    intro x hx
    have hxF :
        (x : Fin m → ℝ) ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1) := by
      refine
        (mem_euclideanRelativeInterior_fin_iff
          (n := m) (C := bifunctionEffectiveDomain F.1) (x := (x : Fin m → ℝ))).2 ?_
      have hx' : x ∈ euclideanRelativeInterior m domF := by
        simpa [hdomp_eq] using hx
      simpa [domF, e] using hx'
    -- Theorem 6.29.4 identifies the two perturbation functions on `ri (dom F)`.
    simpa [p, pcl, clF, helperForCorollary_6_29_8_closureConvexBifunction] using
      ((theorem_29_4_convex_bifunction_closure_section_and_domain F).2.1 (x : Fin m → ℝ) hxF).symm
  have hri :
      euclideanRelativeInterior m domp = euclideanRelativeInterior m dompcl := by
    -- The proper-domain sandwich shows the two perturbation domains have the same relative interior.
    calc
      euclideanRelativeInterior m domp = euclideanRelativeInterior m domF := by
        rw [hdomp_eq]
      _ = euclideanRelativeInterior m domCl := by
        simpa using hri_eq.symm
      _ = euclideanRelativeInterior m dompcl := by
        rw [hdompcl_eq]
  -- Corollary 7.3.4 now upgrades equality on the common relative interior to equality of
  -- closures.
  exact
    convexFunctionClosure_eq_of_agree_on_ri_effectiveDomain
      (n := m) (f := p) (g := pcl) hpConv hpclConv hri hagree |>.symm

/-- Helper for Corollary 6.29.8: strong consistency and finite optimal value make the
perturbation function proper. -/
lemma helperForCorollary_6_29_8_perturbationProper_of_strongConsistency_and_finiteOptimalValue
    {m n : ℕ} (G : ConvexBifunction m n)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue G))
    (hstrong : generalizedConvexProgramStronglyConsistent G) :
    ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ))
      (generalizedConvexProgramPerturbationFunction G) := by
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction G
  have hpConv : ConvexFunction p :=
    (generalizedConvexProgram_perturbationFunction_convex_dom_and_kuhnTucker G).1
  have hpFinite : p 0 ≠ (⊤ : EReal) ∧ p 0 ≠ (⊥ : EReal) :=
    helperForCorollary_6_29_1_perturbationAt_zero_finite G hfinite
  have hri :
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) :=
    -- Strong consistency provides the relative-interior input at the origin.
    helperForCorollary_6_29_4_zero_mem_relativeInterior_effectiveDomain G (Or.inl hstrong)
  have hsub :
      Set.Nonempty (subdifferentialAt p 0) :=
    -- Corollary 6.29.4 converts that relative-interior condition into a subgradient.
    helperForCorollary_6_29_4_subdifferentialNonemptyAtOrigin G hfinite hri
  -- A subgradient at the origin upgrades the convex perturbation function to a proper one.
  simpa [p] using
    (proper_of_subdifferentiableAt_or_infiniteDirectionalDerivative_to_relativeInterior
      p hpConv 0 hpFinite).1 hsub

/-- Helper for Corollary 6.29.8: in the proper finite branch, the perturbation subdifferentials
at the origin coincide for the original program and its Section 29 closure. -/
lemma helperForCorollary_6_29_8_subdifferential_eq_at_origin_of_proper_finite
    {m n : ℕ} (F : ConvexBifunction m n) (hproper : IsProperBifunction F.1)
    (hstrong : generalizedConvexProgramStronglyConsistent F)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    let clF := helperForCorollary_6_29_8_closureConvexBifunction F
    subdifferentialAt (generalizedConvexProgramPerturbationFunction clF) 0 =
      subdifferentialAt (generalizedConvexProgramPerturbationFunction F) 0 := by
  let clF := helperForCorollary_6_29_8_closureConvexBifunction F
  let p : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction F
  let pcl : (Fin m → ℝ) → EReal := generalizedConvexProgramPerturbationFunction clF
  have hclosureEq :
      convexFunctionClosure pcl = convexFunctionClosure p := by
    -- The proper-branch perturbations share the same closed hull.
    simpa [p, pcl, clF] using
      helperForCorollary_6_29_8_closurePerturbationClosure_eq_perturbationClosure_of_proper
        F hproper
  have hstrong_cl : generalizedConvexProgramStronglyConsistent clF := by
    -- Properness lets strong consistency transfer to the closure program.
    simpa [clF] using
      helperForCorollary_6_29_8_strongConsistency_of_closureProgram_of_proper
        F hproper hstrong
  have hpert0 :
      generalizedConvexProgramPerturbationFunction clF 0 =
        generalizedConvexProgramPerturbationFunction F 0 := by
    -- Theorem 6.29.4 identifies the two perturbation values at the origin.
    simpa [clF, helperForCorollary_6_29_8_closureConvexBifunction] using
      (theorem_29_4_convex_bifunction_closure_section_and_domain F).2.1 0 hstrong
  have hfinite_cl : IsFiniteEReal (generalizedConvexProgramOptimalValue clF) := by
    have hopt_cl :
        generalizedConvexProgramOptimalValue clF =
          generalizedConvexProgramOptimalValue F := by
      calc
        generalizedConvexProgramOptimalValue clF =
            generalizedConvexProgramPerturbationFunction clF 0 := by
              rw [helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero]
        _ = generalizedConvexProgramPerturbationFunction F 0 := hpert0
        _ = generalizedConvexProgramOptimalValue F := by
              rw [← helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero]
    simpa [hopt_cl] using hfinite
  have hpProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) p :=
    helperForCorollary_6_29_8_perturbationProper_of_strongConsistency_and_finiteOptimalValue
      F hfinite hstrong
  have hpclProper :
      ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) pcl :=
    helperForCorollary_6_29_8_perturbationProper_of_strongConsistency_and_finiteOptimalValue
      clF hfinite_cl hstrong_cl
  have hri_p :
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (effectiveDomain (Set.univ : Set (Fin m → ℝ)) p) :=
    helperForCorollary_6_29_4_zero_mem_relativeInterior_effectiveDomain F (Or.inl hstrong)
  have hri_pcl :
      (0 : Fin m → ℝ) ∈
        euclideanRelativeInterior_fin m
          (effectiveDomain (Set.univ : Set (Fin m → ℝ)) pcl) :=
    helperForCorollary_6_29_4_zero_mem_relativeInterior_effectiveDomain clF (Or.inl hstrong_cl)
  have hsub_p :
      Set.Nonempty (subdifferentialAt p 0) :=
    -- Both programs are finite at the origin and strongly consistent, so both admit subgradients.
    helperForCorollary_6_29_4_subdifferentialNonemptyAtOrigin F hfinite hri_p
  have hsub_pcl :
      Set.Nonempty (subdifferentialAt pcl 0) :=
    helperForCorollary_6_29_4_subdifferentialNonemptyAtOrigin clF hfinite_cl hri_pcl
  have hcl_p :
      subdifferentialAt (convexFunctionClosure p) 0 = subdifferentialAt p 0 :=
    (convexFunctionClosure_eq_at_subdifferentiable_point_and_subdifferential_eq
      p hpProper 0 hsub_p).2
  have hcl_pcl :
      subdifferentialAt (convexFunctionClosure pcl) 0 = subdifferentialAt pcl 0 :=
    (convexFunctionClosure_eq_at_subdifferentiable_point_and_subdifferential_eq
      pcl hpclProper 0 hsub_pcl).2
  -- Compare both raw subdifferentials through their common closure fiber at the origin.
  calc
    subdifferentialAt pcl 0 = subdifferentialAt (convexFunctionClosure pcl) 0 := by
      symm
      exact hcl_pcl
    _ = subdifferentialAt (convexFunctionClosure p) 0 := by
      simp [hclosureEq]
    _ = subdifferentialAt p 0 := hcl_p

/-- Helper for Corollary 6.29.8: in the proper finite branch, the Kuhn--Tucker sets should agree
because the perturbation subdifferentials at the origin coincide. -/
lemma helperForCorollary_6_29_8_kuhnTuckerSet_eq_of_proper_finite
    {m n : ℕ} (F : ConvexBifunction m n) (hproper : IsProperBifunction F.1)
    (hstrong : generalizedConvexProgramStronglyConsistent F)
    (hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)) :
    let clF := helperForCorollary_6_29_8_closureConvexBifunction F
    {uStar : Fin m → ℝ | IsKuhnTuckerVector clF uStar} =
      {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} := by
  let clF := helperForCorollary_6_29_8_closureConvexBifunction F
  have hpert0 :
      generalizedConvexProgramPerturbationFunction clF 0 =
        generalizedConvexProgramPerturbationFunction F 0 := by
    -- Theorem 6.29.4 identifies the two perturbation values at the origin.
    simpa [clF, helperForCorollary_6_29_8_closureConvexBifunction] using
      (theorem_29_4_convex_bifunction_closure_section_and_domain F).2.1 0 hstrong
  have hfinite_cl : IsFiniteEReal (generalizedConvexProgramOptimalValue clF) := by
    have hopt_cl :
        generalizedConvexProgramOptimalValue clF =
          generalizedConvexProgramOptimalValue F := by
      calc
        generalizedConvexProgramOptimalValue clF =
            generalizedConvexProgramPerturbationFunction clF 0 := by
              rw [helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero]
        _ = generalizedConvexProgramPerturbationFunction F 0 := hpert0
        _ = generalizedConvexProgramOptimalValue F := by
              rw [← helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero]
    simpa [hopt_cl] using hfinite
  have hsubEq :
      subdifferentialAt (generalizedConvexProgramPerturbationFunction clF) 0 =
        subdifferentialAt (generalizedConvexProgramPerturbationFunction F) 0 := by
    -- Route correction: the needed transport is equality of the two closure fibers at `0`,
    -- not a global pointwise identity of the perturbation functions themselves.
    simpa [clF] using
      helperForCorollary_6_29_8_subdifferential_eq_at_origin_of_proper_finite
        F hproper hstrong hfinite
  have hkt_cl :
      {uStar : Fin m → ℝ | IsKuhnTuckerVector clF uStar} =
        (fun v : Fin m → ℝ => -v) ''
          (((dotProductEquiv ℝ (Fin m)) ⁻¹'
            subdifferentialAt (generalizedConvexProgramPerturbationFunction clF) 0)) :=
    helperForCorollary_6_29_5_kuhnTuckerSet_eq_negImage_subdifferentialPreimage clF hfinite_cl
  have hkt :
      {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} =
        (fun v : Fin m → ℝ => -v) ''
          (((dotProductEquiv ℝ (Fin m)) ⁻¹'
            subdifferentialAt (generalizedConvexProgramPerturbationFunction F) 0)) :=
    helperForCorollary_6_29_5_kuhnTuckerSet_eq_negImage_subdifferentialPreimage F hfinite
  -- Rewrite both Kuhn--Tucker sets through the same negated subdifferential-preimage fiber.
  calc
    {uStar : Fin m → ℝ | IsKuhnTuckerVector clF uStar}
        = (fun v : Fin m → ℝ => -v) ''
            (((dotProductEquiv ℝ (Fin m)) ⁻¹'
              subdifferentialAt (generalizedConvexProgramPerturbationFunction clF) 0)) := hkt_cl
    _ = (fun v : Fin m → ℝ => -v) ''
          (((dotProductEquiv ℝ (Fin m)) ⁻¹'
            subdifferentialAt (generalizedConvexProgramPerturbationFunction F) 0)) := by
            rw [hsubEq]
    _ = {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} := hkt.symm

/-- Helper for Corollary 6.29.8: in the nonproper branch, both programs have optimal value
`⊥`, so both Kuhn--Tucker sets are empty. -/
lemma helperForCorollary_6_29_8_kuhnTuckerSet_eq_of_nonproper
    {m n : ℕ} (F : ConvexBifunction m n) (hnotproper : ¬ IsProperBifunction F.1)
    (hstrong : generalizedConvexProgramStronglyConsistent F) :
    let clF := helperForCorollary_6_29_8_closureConvexBifunction F
    {uStar : Fin m → ℝ | IsKuhnTuckerVector clF uStar} =
      {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} := by
  let clF := helperForCorollary_6_29_8_closureConvexBifunction F
  have h29_4 := theorem_29_4_convex_bifunction_closure_section_and_domain F
  have hoptFbot :
      generalizedConvexProgramOptimalValue F = (⊥ : EReal) :=
    helperForCorollary_6_29_8_optimalValue_eq_bot_of_nonproper F hnotproper hstrong
  have hoptClbot :
      generalizedConvexProgramOptimalValue clF = (⊥ : EReal) := by
    have hpert0 :
        helperForTheorem_6_29_4_closurePerturbationFunction F 0 =
          generalizedConvexProgramPerturbationFunction F 0 :=
      h29_4.2.1 0 hstrong
    -- Compare the two origin perturbation values and then rewrite through Theorem 6.29.1.
    calc
      generalizedConvexProgramOptimalValue clF
          = generalizedConvexProgramPerturbationFunction clF 0 := by
              rw [helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero]
      _ = helperForTheorem_6_29_4_closurePerturbationFunction F 0 := by
            rfl
      _ = generalizedConvexProgramPerturbationFunction F 0 := hpert0
      _ = generalizedConvexProgramOptimalValue F := by
            rw [← helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero]
      _ = (⊥ : EReal) := hoptFbot
  ext uStar
  -- A Kuhn--Tucker vector cannot exist once the optimal value is `⊥`.
  simp [IsKuhnTuckerVector, clF, hoptClbot, hoptFbot]

-- Proof sketch: apply Theorem 6.29.4 at the origin, which belongs to `ri (dom F)` by strong
-- consistency, to identify the closure objective and perturbation function near `0`. Then
-- transport optimal values, optimal solutions, and Kuhn--Tucker vectors through the local
-- perturbation equality and the objective-closure identity.
/-- Corollary 6.29.8: let `F` be a convex bifunction from `ℝ^m` to `ℝ^n`. Let `(P)` be the
generalized convex program associated with `F`, and let `(cl P)` be the generalized convex
program associated with the Section 29 closure `cl F`. If `(P)` is strongly consistent, then
`(cl P)` is strongly consistent. Its objective function is the closure of the objective function
for `(P)`, the two programs have the same optimal value, every optimal solution of `(P)` is an
optimal solution of `(cl P)`, and the Kuhn--Tucker vectors of the two programs coincide because
their perturbation functions agree on `ri (dom F)`. -/
theorem closureOfStronglyConsistentGeneralizedConvexProgram_preserves_optimalValue_optimalSolutions_and_kuhnTuckerVectors
    {m n : ℕ} (F : ConvexBifunction m n)
    (hstrong : generalizedConvexProgramStronglyConsistent F) :
    let clF := helperForCorollary_6_29_8_closureConvexBifunction F
    generalizedConvexProgramStronglyConsistent clF ∧
      generalizedConvexProgramObjective clF =
        convexFunctionClosure (generalizedConvexProgramObjective F) ∧
      generalizedConvexProgramOptimalValue clF =
        generalizedConvexProgramOptimalValue F ∧
      generalizedConvexProgramOptimalSolutionSet F ⊆
        generalizedConvexProgramOptimalSolutionSet clF ∧
      (∀ u,
          u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1) →
            generalizedConvexProgramPerturbationFunction clF u =
              generalizedConvexProgramPerturbationFunction F u) ∧
      {uStar : Fin m → ℝ | IsKuhnTuckerVector clF uStar} =
        {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} := by
  let clF := helperForCorollary_6_29_8_closureConvexBifunction F
  have h29_4 := theorem_29_4_convex_bifunction_closure_section_and_domain F
  have h0ri :
      (0 : Fin m → ℝ) ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1) :=
    hstrong
  have hsection0 :
      helperForTheorem_6_29_4_define_section29_bifunctionClosure F 0 =
        convexFunctionClosure (F.1 0) :=
    h29_4.1 0 h0ri
  have hpert0 :
      helperForTheorem_6_29_4_closurePerturbationFunction F 0 =
        generalizedConvexProgramPerturbationFunction F 0 :=
    h29_4.2.1 0 h0ri
  have hobj :
      generalizedConvexProgramObjective clF =
        convexFunctionClosure (generalizedConvexProgramObjective F) := by
    -- The objective is the `u = 0` slice of the closure bifunction.
    simpa [clF, helperForCorollary_6_29_8_closureConvexBifunction,
      generalizedConvexProgramObjective] using hsection0
  have hopt :
      generalizedConvexProgramOptimalValue clF =
        generalizedConvexProgramOptimalValue F := by
    -- Compare the two perturbation values at the origin.
    calc
      generalizedConvexProgramOptimalValue clF
          = generalizedConvexProgramPerturbationFunction clF 0 := by
              rw [helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero]
      _ = helperForTheorem_6_29_4_closurePerturbationFunction F 0 := by
            rfl
      _ = generalizedConvexProgramPerturbationFunction F 0 := hpert0
      _ = generalizedConvexProgramOptimalValue F := by
            rw [← helperForTheorem_6_29_1_optimalValue_eq_perturbationAt_zero]
  have hstrong_cl : generalizedConvexProgramStronglyConsistent clF := by
    by_cases hproper : IsProperBifunction F.1
    · -- In the proper branch, the closure-domain sandwich from Theorem 6.29.4 closes the
      -- relative-interior argument directly.
      exact
        helperForCorollary_6_29_8_strongConsistency_of_closureProgram_of_proper
          F hproper hstrong
    · -- In the nonproper branch, the Section 29 closure is pointwise `⊥`, so its domain is all
      -- of `ℝ^m` and strong consistency is immediate.
      exact
        helperForCorollary_6_29_8_strongConsistency_of_closureProgram_of_nonproper
          F hproper hstrong
  have hlocal :
      ∀ u,
        u ∈ euclideanRelativeInterior_fin m (bifunctionEffectiveDomain F.1) →
          generalizedConvexProgramPerturbationFunction clF u =
            generalizedConvexProgramPerturbationFunction F u := by
    intro u hu
    simpa [clF, helperForCorollary_6_29_8_closureConvexBifunction] using h29_4.2.1 u hu
  have hoptSol :
      generalizedConvexProgramOptimalSolutionSet F ⊆
        generalizedConvexProgramOptimalSolutionSet clF := by
    intro x hx
    rcases hx with ⟨hxFeas, hxVal, hxNeBot⟩
    unfold generalizedConvexProgramOptimalSolutionSet
    refine ⟨?_, ?_, ?_⟩
    · -- Finite objective values stay finite after passing to the section closure.
      simpa [generalizedConvexProgramFeasibleSet, generalizedConvexProgramObjective, clF, hobj] using
        lt_of_le_of_lt
          (convexFunctionClosure_le_self (f := generalizedConvexProgramObjective F) x)
          hxFeas
    · -- The closure objective lies between the common optimal value and the original objective.
      refine le_antisymm ?_ ?_
      · calc
          generalizedConvexProgramObjective clF x
              = convexFunctionClosure (generalizedConvexProgramObjective F) x := by
                  simp [hobj]
          _ ≤ generalizedConvexProgramObjective F x :=
            convexFunctionClosure_le_self (f := generalizedConvexProgramObjective F) x
          _ = generalizedConvexProgramOptimalValue F := hxVal
          _ = generalizedConvexProgramOptimalValue clF := hopt.symm
      · exact sInf_le ⟨x, rfl⟩
    · -- The closure objective is squeezed above by a value different from `⊥`.
      intro hxbot
      have hoptCl_le : generalizedConvexProgramOptimalValue clF ≤ generalizedConvexProgramObjective clF x :=
        sInf_le ⟨x, rfl⟩
      have hoptCl_bot : generalizedConvexProgramOptimalValue clF = (⊥ : EReal) := by
        refine le_antisymm ?_ bot_le
        simpa [hxbot] using hoptCl_le
      have hoptF_bot : generalizedConvexProgramOptimalValue F = (⊥ : EReal) := by
        simpa [hopt] using hoptCl_bot
      exact hxNeBot (hxVal.trans hoptF_bot)
  have hKT :
      {uStar : Fin m → ℝ | IsKuhnTuckerVector clF uStar} =
        {uStar : Fin m → ℝ | IsKuhnTuckerVector F uStar} := by
    by_cases hproper : IsProperBifunction F.1
    · by_cases hfinite : IsFiniteEReal (generalizedConvexProgramOptimalValue F)
      · -- In the finite proper branch, the remaining work is the Chapter 23 subdifferential
        -- comparison at the origin.
        exact helperForCorollary_6_29_8_kuhnTuckerSet_eq_of_proper_finite
          F hproper hstrong hfinite
      · have hoptFbot :
            generalizedConvexProgramOptimalValue F = (⊥ : EReal) :=
          helperForCorollary_6_29_8_optimalValue_eq_bot_of_proper_not_finite
            F hproper hstrong hfinite
        have hoptClbot :
            generalizedConvexProgramOptimalValue clF = (⊥ : EReal) := by
          simpa [hopt] using hoptFbot
        -- Once both optimal values are `⊥`, neither program admits a Kuhn--Tucker vector.
        simp [IsKuhnTuckerVector, hoptClbot, hoptFbot]
    · -- In the nonproper branch, both optimal values are `⊥`, so both Kuhn--Tucker sets vanish.
      exact helperForCorollary_6_29_8_kuhnTuckerSet_eq_of_nonproper F hproper hstrong
  exact ⟨hstrong_cl, hobj, hopt, hoptSol, hlocal, hKT⟩


end Section29
end Chap06
