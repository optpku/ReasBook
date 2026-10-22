/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.BondPercolationAPI

open MeasureTheory ProbabilityTheory
open scoped unitInterval
open unitInterval

universe u

variable {Ω : Type u} {d : ℕ}

/-- Helper for Theorem 2.46: a non-degenerate Bernoulli parameter gives positive weight to the
`open` outcome at a single lattice bond. -/
lemma unitInterval_toNNReal_pos (p : unitInterval) (hp0 : p ≠ 0) :
    0 < toNNReal p := by
  -- Convert the endpoint exclusion `p ≠ 0` into strict positivity on the real interval.
  have hp_real : 0 < (p : ℝ) := by
    refine lt_of_le_of_ne p.2.1 ?_
    intro hp_zero
    apply hp0
    ext
    simpa using hp_zero.symm
  exact_mod_cast hp_real

/-- Helper for Theorem 2.46: a non-degenerate Bernoulli parameter gives positive weight to the
`closed` outcome at a single lattice bond. -/
lemma unitInterval_sigma_toNNReal_pos (p : unitInterval) (hp1 : p ≠ 1) :
    0 < toNNReal (σ p) := by
  -- The complementary parameter `σ p = 1 - p` is positive precisely away from the endpoint `1`.
  have hsigma_real : 0 < ((σ p : unitInterval) : ℝ) := by
    refine lt_of_le_of_ne (σ p).2.1 ?_
    intro hsigma_zero
    have hsigma_eq_zero : σ p = 0 := by
      ext
      simpa using hsigma_zero.symm
    apply hp1
    simpa using congrArg σ hsigma_eq_zero
  exact_mod_cast hsigma_real

/-- Helper for Theorem 2.46: every finite cylinder pattern on lattice bonds has positive
probability under a non-degenerate Bernoulli law. -/
lemma finiteCylinderPatternPos
    [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω)
    (openEdges : Ω → Set (Sym2 (LatticePoint d)))
    (p : unitInterval)
    (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hber : IsSetBernoulli openEdges (latticeGraph d).edgeSet p (μ : Measure Ω))
    {F A : Set (Sym2 (LatticePoint d))}
    (hFfin : F.Finite) (hA : A ⊆ F) (hF : F ⊆ (latticeGraph d).edgeSet) :
    0 < (μ : Measure Ω) {ω | openEdges ω ∩ F = A} := by
  classical
  let sF : Finset (Sym2 (LatticePoint d)) := hFfin.toFinset
  let pattern : ∀ e : sF, Prop := fun e ↦ e.1 ∈ A
  let ν : Sym2 (LatticePoint d) → Measure Prop := fun e ↦
    toNNReal p • Measure.dirac (e ∈ (latticeGraph d).edgeSet) +
      toNNReal (σ p) • Measure.dirac False
  let field : Ω → Sym2 (LatticePoint d) → Prop := fun ω e ↦ e ∈ openEdges ω
  have hpreimage :
      ((fun q : Sym2 (LatticePoint d) → Prop ↦ {e | q e}) ⁻¹'
          {s : Set (Sym2 (LatticePoint d)) | s ∩ F = A}) =
        MeasureTheory.cylinder (α := fun _ : Sym2 (LatticePoint d) => Prop)
          sF ({pattern} : Set (∀ e : sF, Prop)) := by
    -- Restricting the indicator field to the finite set `F` records exactly the prescribed
    -- finite pattern `A`.
    ext q
    rw [Set.mem_preimage, MeasureTheory.mem_cylinder, Set.mem_singleton_iff]
    constructor
    · intro hq
      ext e
      have heF : e.1 ∈ F := by
        exact hFfin.mem_toFinset.mp e.2
      change q e.1 ↔ e.1 ∈ A
      have hmem :
          q e.1 ∧ e.1 ∈ F ↔ e.1 ∈ A := by
        have := congrArg (fun t : Set (Sym2 (LatticePoint d)) => e.1 ∈ t) hq
        simpa [Set.mem_setOf_eq, heF] using this
      constructor
      · intro hqe
        exact hmem.mp ⟨hqe, heF⟩
      · intro hAe
        exact (hmem.mpr hAe).1
    · intro hq
      ext e
      by_cases heF : e ∈ F
      · have hpattern :
          q e = (e ∈ A) := by
          have := congrFun hq ⟨e, by simpa [sF] using heF⟩
          simpa [pattern] using this
        simp [Set.mem_setOf_eq, heF, hpattern]
      · have heA : e ∉ A := fun heA ↦ heF (hA heA)
        simp [Set.mem_setOf_eq, heF, heA]
  have hfieldLaw :
      HasLaw field (MeasureTheory.Measure.infinitePi ν) (μ : Measure Ω) := by
    -- Transport the Bernoulli law from random subsets to their predicate-valued indicator field.
    have hmap_set :
        Measure.map (MeasurableEquiv.setOf (α := Sym2 (LatticePoint d)))
            (MeasureTheory.Measure.infinitePi ν) =
          ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p := by
      simp [ProbabilityTheory.setBernoulli_eq_map, ν]
    have hmap_field :
        Measure.map (MeasurableEquiv.setOf (α := Sym2 (LatticePoint d))).symm
            (ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p) =
          MeasureTheory.Measure.infinitePi ν := by
      exact
        (MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq
          (μ := MeasureTheory.Measure.infinitePi ν)
          (ν := ProbabilityTheory.setBernoulli (latticeGraph d).edgeSet p)
          (e := MeasurableEquiv.setOf (α := Sym2 (LatticePoint d)))).mp hmap_set |>.symm
    refine ⟨by fun_prop, ?_⟩
    calc
      Measure.map field (μ : Measure Ω)
          = Measure.map (MeasurableEquiv.setOf (α := Sym2 (LatticePoint d))).symm
              (Measure.map openEdges (μ : Measure Ω)) := by
            simpa [field, Function.comp] using
              (AEMeasurable.map_map_of_aemeasurable
                ((MeasurableEquiv.setOf (α := Sym2 (LatticePoint d))).symm.measurable.aemeasurable)
                hber.aemeasurable).symm
      _ = MeasureTheory.Measure.infinitePi ν := by
        rw [hber.map_eq, hmap_field]
  have hcylinderMeas :
      MeasurableSet
        (MeasureTheory.cylinder (α := fun _ : Sym2 (LatticePoint d) => Prop)
          sF ({pattern} : Set (∀ e : sF, Prop))) := by
    -- A finite cylinder is the preimage of a measurable singleton under the coordinate restriction.
    simpa [MeasureTheory.cylinder] using
      measurableSet_preimage (Finset.measurable_restrict sF) (MeasurableSet.singleton pattern)
  have hpatternEvent :
      {ω | openEdges ω ∩ F = A} =
        field ⁻¹' MeasureTheory.cylinder (α := fun _ : Sym2 (LatticePoint d) => Prop)
          sF ({pattern} : Set (∀ e : sF, Prop)) := by
    -- Evaluating the cylinder characterization at the indicator field of `openEdges` gives the
    -- configuration-space event.
    ext ω
    have := congrArg
      (fun T : Set (Sym2 (LatticePoint d) → Prop) => field ω ∈ T) hpreimage
    simpa [field] using this
  have hprod :
      0 < (∏ e : sF, ν e.1 ({pattern e} : Set Prop)) := by
    -- Each coordinate contributes either the strictly positive open weight `p` or the strictly
    -- positive closed weight `1 - p`.
    have hprod' :
        0 < Finset.prod (Finset.univ : Finset sF)
          (fun e : sF => ν e.1 ({pattern e} : Set Prop)) := by
      refine
        (CanonicallyOrderedAdd.prod_pos
          (s := (Finset.univ : Finset sF))
          (f := fun e : sF => ν e.1 ({pattern e} : Set Prop))).2 ?_
      intro e he
      have heF : e.1 ∈ F := by
        exact hFfin.mem_toFinset.mp e.2
      have hedge : e.1 ∈ (latticeGraph d).edgeSet := hF heF
      by_cases heA : e.1 ∈ A
      · have hp_pos_enn := ENNReal.coe_pos.2 (unitInterval_toNNReal_pos p hp0)
        simpa [ν, pattern, heA, hedge, ENNReal.smul_def] using hp_pos_enn
      · have hsigma_pos_enn := ENNReal.coe_pos.2 (unitInterval_sigma_toNNReal_pos p hp1)
        simpa [ν, pattern, heA, hedge, ENNReal.smul_def] using hsigma_pos_enn
    simpa using hprod'
  calc
    0 < (MeasureTheory.Measure.infinitePi ν)
        (MeasureTheory.cylinder (α := fun _ : Sym2 (LatticePoint d) => Prop)
          sF ({pattern} : Set (∀ e : sF, Prop))) := by
      rw [MeasureTheory.Measure.infinitePi_cylinder ν (MeasurableSet.singleton pattern)]
      rw [Measure.pi_singleton (μ := fun e : sF ↦ ν e.1) pattern]
      exact hprod
    _ = (Measure.map field (μ : Measure Ω))
        (MeasureTheory.cylinder (α := fun _ : Sym2 (LatticePoint d) => Prop)
          sF ({pattern} : Set (∀ e : sF, Prop))) := by
      rw [hfieldLaw.map_eq]
    _ = (μ : Measure Ω)
        (field ⁻¹' MeasureTheory.cylinder (α := fun _ : Sym2 (LatticePoint d) => Prop)
          sF ({pattern} : Set (∀ e : sF, Prop))) := by
      rw [Measure.map_apply_of_aemeasurable hfieldLaw.aemeasurable hcylinderMeas]
    _ = (μ : Measure Ω) {ω | openEdges ω ∩ F = A} := by
      rw [← hpatternEvent]

/-- Helper for Theorem 2.46: on any finite family of lattice bonds, the event that all bonds are
open has positive probability under a non-degenerate Bernoulli law. -/
lemma finiteCylinderAllOpenPos
    [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω)
    (openEdges : Ω → Set (Sym2 (LatticePoint d)))
    (p : unitInterval)
    (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hber : IsSetBernoulli openEdges (latticeGraph d).edgeSet p (μ : Measure Ω))
    {F : Set (Sym2 (LatticePoint d))}
    (hFfin : F.Finite) (hF : F ⊆ (latticeGraph d).edgeSet) :
    0 < (μ : Measure Ω) {ω | F ⊆ openEdges ω} := by
  have hEvent :
      {ω | openEdges ω ∩ F = F} = {ω | F ⊆ openEdges ω} := by
    ext ω
    constructor
    · intro hω e he
      have hmem := congrArg (fun s : Set (Sym2 (LatticePoint d)) => e ∈ s) hω
      simpa [he] using hmem
    · intro hω
      ext e
      constructor
      · intro he
        exact he.2
      · intro he
        exact ⟨hω he, he⟩
  -- Proof comment: the all-open event is the finite cylinder with prescribed pattern `A = F`.
  rw [← hEvent]
  exact
    finiteCylinderPatternPos μ openEdges p hp0 hp1 hber hFfin
      (show F ⊆ F by intro e he; exact he) hF

/-- Helper for Theorem 2.46: on any finite family of lattice bonds, the event that all bonds are
closed has positive probability under a non-degenerate Bernoulli law. -/
lemma finiteCylinderAllClosedPos
    [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω)
    (openEdges : Ω → Set (Sym2 (LatticePoint d)))
    (p : unitInterval)
    (hp0 : p ≠ 0) (hp1 : p ≠ 1)
    (hber : IsSetBernoulli openEdges (latticeGraph d).edgeSet p (μ : Measure Ω))
    {F : Set (Sym2 (LatticePoint d))}
    (hFfin : F.Finite) (hF : F ⊆ (latticeGraph d).edgeSet) :
    0 < (μ : Measure Ω) {ω | openEdges ω ∩ F = ∅} := by
  -- Proof comment: the all-closed event is the finite cylinder with prescribed pattern `A = ∅`.
  simpa using
    finiteCylinderPatternPos μ openEdges p hp0 hp1 hber hFfin (show (∅ : Set _) ⊆ F by simp) hF
