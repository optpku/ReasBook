/-
Authors: Zichen Wang, Wanli Ma, Min Cui, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import Analysis2_Tao_2022.Chap08.section01_part1

section Chap08
section Section01

/-- Pointwise sum of two non-negative simple functions on `Ω`. -/
noncomputable def NonnegSimpleFunction.add {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f g : NonnegSimpleFunction Ω) : NonnegSimpleFunction Ω :=
  ⟨(fun x : Ω => f.1 x + g.1 x),
    ⟨IsSimpleFunction.add f.2.1 g.2.1,
      fun x : Ω => add_nonneg (f.2.2 x) (g.2.2 x)⟩⟩

/-- Proposition 8.1.2: for non-negative simple functions `f, g : Ω → ℝ`, the integral is
additive: `∫_Ω (f + g) dm = ∫_Ω f dm + ∫_Ω g dm`. -/
theorem lebesgueIntegralNonnegSimple_add {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f g : NonnegSimpleFunction Ω) :
    lebesgueIntegralNonnegSimple (NonnegSimpleFunction.add f g) =
      lebesgueIntegralNonnegSimple f + lebesgueIntegralNonnegSimple g := by
  classical
  have hΩ : MeasurableSet Ω := f.2.1.1
  have hf_meas : Measurable f.1 := f.2.1.2.1
  have hg_meas : Measurable g.1 := g.2.1.2.1
  have hf_fin : (Set.range f.1).Finite := f.2.1.2.2
  have hg_fin : (Set.range g.1).Finite := g.2.1.2.2

  letI : Fintype (Set.range f.1) := hf_fin.fintype
  let Nf : ℕ := Fintype.card (Set.range f.1)
  let ef : Fin Nf ≃ Set.range f.1 := (Fintype.equivFin (Set.range f.1)).symm
  let cf : Fin Nf → ℝ := fun i : Fin Nf => (ef i).1
  let Ef : Fin Nf → Set (Fin n → ℝ) :=
    fun i : Fin Nf => (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {cf i}))

  letI : Fintype (Set.range g.1) := hg_fin.fintype
  let Ng : ℕ := Fintype.card (Set.range g.1)
  let eg : Fin Ng ≃ Set.range g.1 := (Fintype.equivFin (Set.range g.1)).symm
  let cg : Fin Ng → ℝ := fun j : Fin Ng => (eg j).1
  let Eg : Fin Ng → Set (Fin n → ℝ) :=
    fun j : Fin Ng => (((↑) : Ω → Fin n → ℝ) '' (g.1 ⁻¹' {cg j}))

  have hEf_meas : ∀ i : Fin Nf, MeasurableSet (Ef i) := by
    intro i
    have hpre : MeasurableSet (f.1 ⁻¹' {cf i}) := hf_meas (MeasurableSet.singleton (cf i))
    simpa [Ef] using MeasurableSet.subtype_image hΩ hpre
  have hEf_subset : ∀ i : Fin Nf, Ef i ⊆ Ω := by
    intro i x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property
  have hEg_meas : ∀ j : Fin Ng, MeasurableSet (Eg j) := by
    intro j
    have hpre : MeasurableSet (g.1 ⁻¹' {cg j}) := hg_meas (MeasurableSet.singleton (cg j))
    simpa [Eg] using MeasurableSet.subtype_image hΩ hpre
  have hEg_subset : ∀ j : Fin Ng, Eg j ⊆ Ω := by
    intro j x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property

  have hcf_inj : Function.Injective cf := by
    dsimp [cf]
    exact helperForLemma_8_2_coeffIndexing_injective (f := f.1) ef
  have hcg_inj : Function.Injective cg := by
    dsimp [cg]
    exact helperForLemma_8_2_coeffIndexing_injective (f := g.1) eg

  have hEf_disjoint :
      Pairwise (fun i j : Fin Nf => Disjoint (Ef i) (Ef j)) := by
    simpa [Ef] using helperForLemma_8_2_pairwiseDisjoint_fiberSets (f := f.1) cf hcf_inj
  have hEg_disjoint :
      Pairwise (fun i j : Fin Ng => Disjoint (Eg i) (Eg j)) := by
    simpa [Eg] using helperForLemma_8_2_pairwiseDisjoint_fiberSets (f := g.1) cg hcg_inj

  let P : ℕ := Fintype.card (Fin Nf × Fin Ng)
  let eProd : Fin P ≃ Fin Nf × Fin Ng := (Fintype.equivFin (Fin Nf × Fin Ng)).symm
  let H : Fin P → Set (Fin n → ℝ) := fun p : Fin P => Ef (eProd p).1 ∩ Eg (eProd p).2
  let cF : Fin P → ℝ := fun p : Fin P => cf (eProd p).1
  let cG : Fin P → ℝ := fun p : Fin P => cg (eProd p).2
  let cFG : Fin P → ℝ := fun p : Fin P => cF p + cG p

  have hH_meas : ∀ p : Fin P, MeasurableSet (H p) := by
    intro p
    exact (hEf_meas ((eProd p).1)).inter (hEg_meas ((eProd p).2))
  have hH_subset : ∀ p : Fin P, H p ⊆ Ω := by
    intro p x hx
    exact hEf_subset ((eProd p).1) hx.1
  have hH_disjoint : Pairwise (fun p q : Fin P => Disjoint (H p) (H q)) := by
    intro p q hpq
    by_cases hfst : (eProd p).1 = (eProd q).1
    · have hsnd : (eProd p).2 ≠ (eProd q).2 := by
        intro hsnd
        apply hpq
        apply eProd.injective
        exact Prod.ext hfst hsnd
      refine Set.disjoint_left.2 ?_
      intro x hxP hxQ
      exact (Set.disjoint_left.1 (hEg_disjoint (i := (eProd p).2) (j := (eProd q).2) hsnd))
        hxP.2 hxQ.2
    · have hfst_ne : (eProd p).1 ≠ (eProd q).1 := hfst
      refine Set.disjoint_left.2 ?_
      intro x hxP hxQ
      exact (Set.disjoint_left.1 (hEf_disjoint (i := (eProd p).1) (j := (eProd q).1) hfst_ne))
        hxP.1 hxQ.1

  have hcF_nonneg : ∀ p : Fin P, 0 ≤ cF p := by
    intro p
    rcases (ef ((eProd p).1)).2 with ⟨x, hx⟩
    have hx' : f.1 x = cF p := by
      simpa [cF, cf] using hx
    simpa [hx'] using f.2.2 x
  have hcG_nonneg : ∀ p : Fin P, 0 ≤ cG p := by
    intro p
    rcases (eg ((eProd p).2)).2 with ⟨x, hx⟩
    have hx' : g.1 x = cG p := by
      simpa [cG, cg] using hx
    simpa [hx'] using g.2.2 x
  have hcFG_nonneg : ∀ p : Fin P, 0 ≤ cFG p := by
    intro p
    exact add_nonneg (hcF_nonneg p) (hcG_nonneg p)

  have hf_repr_common :
      ∀ x : Fin n → ℝ, ∀ hx : x ∈ Ω,
        f.1 ⟨x, hx⟩ =
          (Finset.univ : Finset (Fin P)).sum
            (fun p : Fin P =>
              cF p * Set.indicator (H p) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
    intro x hx
    let i0 : Fin Nf := ef.symm ⟨f.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    let j0 : Fin Ng := eg.symm ⟨g.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    let p0 : Fin P := eProd.symm (i0, j0)
    have hi0_eq : ef i0 = ⟨f.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ := by
      simpa [i0] using ef.apply_symm_apply ⟨f.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    have hj0_eq : eg j0 = ⟨g.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ := by
      simpa [j0] using eg.apply_symm_apply ⟨g.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    have hi0_val : cF p0 = f.1 ⟨x, hx⟩ := by
      simpa [cF, cf, p0] using congrArg Subtype.val hi0_eq
    have hj0_val : cG p0 = g.1 ⟨x, hx⟩ := by
      simpa [cG, cg, p0] using congrArg Subtype.val hj0_eq
    have hi0_mem : x ∈ Ef i0 := by
      refine (helperForLemma_8_2_mem_fiberSet_iff (f := f.1) (c := cf) (hx := hx) (i := i0)).2 ?_
      simpa [cF, cf, p0] using hi0_val.symm
    have hj0_mem : x ∈ Eg j0 := by
      refine (helperForLemma_8_2_mem_fiberSet_iff (f := g.1) (c := cg) (hx := hx) (i := j0)).2 ?_
      simpa [cG, cg, p0] using hj0_val.symm
    have hxHp0 : x ∈ H p0 := by
      simpa [H, p0] using And.intro hi0_mem hj0_mem
    have hcollapse :
        (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P =>
            cF p * Set.indicator (H p) (fun _ : Fin n → ℝ => (1 : ℝ)) x) = cF p0 :=
      helperForLemma_8_4_sum_indicator_eq_coeff_of_mem (hE_disjoint := hH_disjoint) cF
        (hxi := hxHp0)
    calc
      f.1 ⟨x, hx⟩ = cF p0 := by simpa [hi0_val]
      _ = (Finset.univ : Finset (Fin P)).sum
            (fun p : Fin P =>
              cF p * Set.indicator (H p) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
            exact hcollapse.symm

  have hg_repr_common :
      ∀ x : Fin n → ℝ, ∀ hx : x ∈ Ω,
        g.1 ⟨x, hx⟩ =
          (Finset.univ : Finset (Fin P)).sum
            (fun p : Fin P =>
              cG p * Set.indicator (H p) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
    intro x hx
    let i0 : Fin Nf := ef.symm ⟨f.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    let j0 : Fin Ng := eg.symm ⟨g.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    let p0 : Fin P := eProd.symm (i0, j0)
    have hi0_eq : ef i0 = ⟨f.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ := by
      simpa [i0] using ef.apply_symm_apply ⟨f.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    have hj0_eq : eg j0 = ⟨g.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ := by
      simpa [j0] using eg.apply_symm_apply ⟨g.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    have hi0_mem : x ∈ Ef i0 := by
      have hi0_val : cf i0 = f.1 ⟨x, hx⟩ := by
        simpa [cf] using congrArg Subtype.val hi0_eq
      refine (helperForLemma_8_2_mem_fiberSet_iff (f := f.1) (c := cf) (hx := hx) (i := i0)).2 ?_
      simpa using hi0_val.symm
    have hj0_val : cG p0 = g.1 ⟨x, hx⟩ := by
      simpa [cG, cg, p0] using congrArg Subtype.val hj0_eq
    have hj0_mem : x ∈ Eg j0 := by
      refine (helperForLemma_8_2_mem_fiberSet_iff (f := g.1) (c := cg) (hx := hx) (i := j0)).2 ?_
      simpa [cG, p0] using hj0_val.symm
    have hxHp0 : x ∈ H p0 := by
      simpa [H, p0] using And.intro hi0_mem hj0_mem
    have hcollapse :
        (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P =>
            cG p * Set.indicator (H p) (fun _ : Fin n → ℝ => (1 : ℝ)) x) = cG p0 :=
      helperForLemma_8_4_sum_indicator_eq_coeff_of_mem (hE_disjoint := hH_disjoint) cG
        (hxi := hxHp0)
    calc
      g.1 ⟨x, hx⟩ = cG p0 := by simpa [hj0_val]
      _ = (Finset.univ : Finset (Fin P)).sum
            (fun p : Fin P =>
              cG p * Set.indicator (H p) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
            exact hcollapse.symm

  have hAdd_repr_common :
      ∀ x : Fin n → ℝ, ∀ hx : x ∈ Ω,
        (NonnegSimpleFunction.add f g).1 ⟨x, hx⟩ =
          (Finset.univ : Finset (Fin P)).sum
            (fun p : Fin P =>
              cFG p * Set.indicator (H p) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
    intro x hx
    let i0 : Fin Nf := ef.symm ⟨f.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    let j0 : Fin Ng := eg.symm ⟨g.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    let p0 : Fin P := eProd.symm (i0, j0)
    have hi0_eq : ef i0 = ⟨f.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ := by
      simpa [i0] using ef.apply_symm_apply ⟨f.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    have hj0_eq : eg j0 = ⟨g.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ := by
      simpa [j0] using eg.apply_symm_apply ⟨g.1 ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    have hi0_val : cF p0 = f.1 ⟨x, hx⟩ := by
      simpa [cF, cf, p0] using congrArg Subtype.val hi0_eq
    have hj0_val : cG p0 = g.1 ⟨x, hx⟩ := by
      simpa [cG, cg, p0] using congrArg Subtype.val hj0_eq
    have hi0_mem : x ∈ Ef i0 := by
      refine (helperForLemma_8_2_mem_fiberSet_iff (f := f.1) (c := cf) (hx := hx) (i := i0)).2 ?_
      simpa [cF, p0] using hi0_val.symm
    have hj0_mem : x ∈ Eg j0 := by
      refine (helperForLemma_8_2_mem_fiberSet_iff (f := g.1) (c := cg) (hx := hx) (i := j0)).2 ?_
      simpa [cG, p0] using hj0_val.symm
    have hxHp0 : x ∈ H p0 := by
      simpa [H, p0] using And.intro hi0_mem hj0_mem
    have hcollapse :
        (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P =>
            cFG p * Set.indicator (H p) (fun _ : Fin n → ℝ => (1 : ℝ)) x) = cFG p0 :=
      helperForLemma_8_4_sum_indicator_eq_coeff_of_mem (hE_disjoint := hH_disjoint) cFG
        (hxi := hxHp0)
    calc
      (NonnegSimpleFunction.add f g).1 ⟨x, hx⟩ = f.1 ⟨x, hx⟩ + g.1 ⟨x, hx⟩ := by
        simp [NonnegSimpleFunction.add]
      _ = cF p0 + cG p0 := by simpa [hi0_val, hj0_val]
      _ = cFG p0 := by simp [cFG]
      _ = (Finset.univ : Finset (Fin P)).sum
            (fun p : Fin P =>
              cFG p * Set.indicator (H p) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
            exact hcollapse.symm

  have hIntF :
      lebesgueIntegralNonnegSimple f =
        (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P => ENNReal.ofReal (cF p) * MeasureTheory.volume (H p)) := by
    exact lemma_8_4 (E := H) hH_meas hH_subset hH_disjoint cF hcF_nonneg f hf_repr_common
  have hIntG :
      lebesgueIntegralNonnegSimple g =
        (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P => ENNReal.ofReal (cG p) * MeasureTheory.volume (H p)) := by
    exact lemma_8_4 (E := H) hH_meas hH_subset hH_disjoint cG hcG_nonneg g hg_repr_common
  have hIntAdd :
      lebesgueIntegralNonnegSimple (NonnegSimpleFunction.add f g) =
        (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P => ENNReal.ofReal (cFG p) * MeasureTheory.volume (H p)) := by
    exact lemma_8_4 (E := H) hH_meas hH_subset hH_disjoint cFG hcFG_nonneg
      (NonnegSimpleFunction.add f g) hAdd_repr_common

  have hIntegralAlgebra :
      (Finset.univ : Finset (Fin P)).sum
        (fun p : Fin P => ENNReal.ofReal (cFG p) * MeasureTheory.volume (H p))
        =
      (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P => ENNReal.ofReal (cF p) * MeasureTheory.volume (H p))
        +
      (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P => ENNReal.ofReal (cG p) * MeasureTheory.volume (H p)) := by
    calc
      (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P => ENNReal.ofReal (cFG p) * MeasureTheory.volume (H p))
          =
        (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P =>
            (ENNReal.ofReal (cF p) + ENNReal.ofReal (cG p)) * MeasureTheory.volume (H p)) := by
            refine Finset.sum_congr rfl ?_
            intro p hp
            have hcfp : 0 ≤ cF p := hcF_nonneg p
            have hcgp : 0 ≤ cG p := hcG_nonneg p
            simp [cFG, ENNReal.ofReal_add, hcfp, hcgp]
      _ =
        (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P =>
            ENNReal.ofReal (cF p) * MeasureTheory.volume (H p) +
              ENNReal.ofReal (cG p) * MeasureTheory.volume (H p)) := by
              refine Finset.sum_congr rfl ?_
              intro p hp
              simpa [add_mul]
      _ =
        (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P => ENNReal.ofReal (cF p) * MeasureTheory.volume (H p))
        +
        (Finset.univ : Finset (Fin P)).sum
          (fun p : Fin P => ENNReal.ofReal (cG p) * MeasureTheory.volume (H p)) := by
            exact Finset.sum_add_distrib

  calc
    lebesgueIntegralNonnegSimple (NonnegSimpleFunction.add f g)
        =
      (Finset.univ : Finset (Fin P)).sum
        (fun p : Fin P => ENNReal.ofReal (cFG p) * MeasureTheory.volume (H p)) := hIntAdd
    _ =
      (Finset.univ : Finset (Fin P)).sum
        (fun p : Fin P => ENNReal.ofReal (cF p) * MeasureTheory.volume (H p))
      +
      (Finset.univ : Finset (Fin P)).sum
        (fun p : Fin P => ENNReal.ofReal (cG p) * MeasureTheory.volume (H p)) := hIntegralAlgebra
    _ = lebesgueIntegralNonnegSimple f + lebesgueIntegralNonnegSimple g := by
      rw [← hIntF, ← hIntG]

/-- Pointwise scalar multiplication of a non-negative simple function by a nonnegative real. -/
noncomputable def NonnegSimpleFunction.constMul {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (c : ℝ) (hc : 0 ≤ c) (f : NonnegSimpleFunction Ω) : NonnegSimpleFunction Ω :=
  ⟨(fun x : Ω => c * f.1 x),
    ⟨IsSimpleFunction.const_mul f.2.1 c, fun x : Ω => mul_nonneg hc (f.2.2 x)⟩⟩

/-- Proposition 8.1.3: if `f : Ω → ℝ` is a non-negative simple function and `c > 0`,
then the integral scales linearly: `∫_Ω (c f) dm = c ∫_Ω f dm`. -/
theorem lebesgueIntegralNonnegSimple_constMul {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f : NonnegSimpleFunction Ω) {c : ℝ} (hc : 0 < c) :
    lebesgueIntegralNonnegSimple (NonnegSimpleFunction.constMul c (le_of_lt hc) f) =
      ENNReal.ofReal c * lebesgueIntegralNonnegSimple f := by
  classical
  have hΩ : MeasurableSet Ω := f.2.1.1
  have hf_meas : Measurable f.1 := f.2.1.2.1
  have hf_fin : (Set.range f.1).Finite := f.2.1.2.2

  letI : Fintype (Set.range f.1) := hf_fin.fintype
  let N : ℕ := Fintype.card (Set.range f.1)
  let e : Fin N ≃ Set.range f.1 := (Fintype.equivFin (Set.range f.1)).symm
  let cf : Fin N → ℝ := fun i : Fin N => (e i).1
  let Ef : Fin N → Set (Fin n → ℝ) :=
    fun i : Fin N => (((↑) : Ω → Fin n → ℝ) '' (f.1 ⁻¹' {cf i}))

  have hEf_meas : ∀ i : Fin N, MeasurableSet (Ef i) := by
    have hE := helperForLemma_8_2_fiberSets_measurable_subset (f := f.1) hΩ hf_meas cf
    intro i
    simpa [Ef] using hE.1 i
  have hEf_subset : ∀ i : Fin N, Ef i ⊆ Ω := by
    have hE := helperForLemma_8_2_fiberSets_measurable_subset (f := f.1) hΩ hf_meas cf
    intro i
    simpa [Ef] using hE.2 i
  have hcf_inj : Function.Injective cf := by
    dsimp [cf]
    exact helperForLemma_8_2_coeffIndexing_injective (f := f.1) e
  have hEf_disjoint :
      Pairwise (fun i j : Fin N => Disjoint (Ef i) (Ef j)) := by
    simpa [Ef] using helperForLemma_8_2_pairwiseDisjoint_fiberSets (f := f.1) cf hcf_inj

  have hcf_nonneg : ∀ i : Fin N, 0 ≤ cf i := by
    intro i
    rcases (e i).2 with ⟨x, hx⟩
    have hx' : f.1 x = cf i := by
      simpa [cf] using hx
    simpa [hx'] using f.2.2 x
  have hscaledCoeff_nonneg : ∀ i : Fin N, 0 ≤ c * cf i := by
    intro i
    exact mul_nonneg (le_of_lt hc) (hcf_nonneg i)

  have hf_repr :
      ∀ x : Fin n → ℝ, ∀ hx : x ∈ Ω,
        f.1 ⟨x, hx⟩ =
          (Finset.univ : Finset (Fin N)).sum
            (fun i : Fin N =>
              cf i * Set.indicator (Ef i) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
    intro x hx
    have hpoint := helperForLemma_8_2_pointwise_sum_representation (f := f.1) e hx
    simpa [cf, Ef] using hpoint

  have hscaled_repr :
      ∀ x : Fin n → ℝ, ∀ hx : x ∈ Ω,
        (NonnegSimpleFunction.constMul c (le_of_lt hc) f).1 ⟨x, hx⟩ =
          (Finset.univ : Finset (Fin N)).sum
            (fun i : Fin N =>
              (c * cf i) * Set.indicator (Ef i) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
    intro x hx
    calc
      (NonnegSimpleFunction.constMul c (le_of_lt hc) f).1 ⟨x, hx⟩ = c * f.1 ⟨x, hx⟩ := by
        simp [NonnegSimpleFunction.constMul]
      _ = c *
          (Finset.univ : Finset (Fin N)).sum
            (fun i : Fin N =>
              cf i * Set.indicator (Ef i) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
            rw [hf_repr x hx]
      _ =
          (Finset.univ : Finset (Fin N)).sum
            (fun i : Fin N =>
              c * (cf i * Set.indicator (Ef i) (fun _ : Fin n → ℝ => (1 : ℝ)) x)) := by
            rw [Finset.mul_sum]
      _ =
          (Finset.univ : Finset (Fin N)).sum
            (fun i : Fin N =>
              (c * cf i) * Set.indicator (Ef i) (fun _ : Fin n → ℝ => (1 : ℝ)) x) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring

  have hIntF :
      lebesgueIntegralNonnegSimple f =
        (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N => ENNReal.ofReal (cf i) * MeasureTheory.volume (Ef i)) := by
    exact lemma_8_4 (E := Ef) hEf_meas hEf_subset hEf_disjoint cf hcf_nonneg f hf_repr
  have hIntScaled :
      lebesgueIntegralNonnegSimple (NonnegSimpleFunction.constMul c (le_of_lt hc) f) =
        (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N => ENNReal.ofReal (c * cf i) * MeasureTheory.volume (Ef i)) := by
    exact lemma_8_4 (E := Ef) hEf_meas hEf_subset hEf_disjoint (fun i : Fin N => c * cf i)
      hscaledCoeff_nonneg (NonnegSimpleFunction.constMul c (le_of_lt hc) f) hscaled_repr

  have hEnnrealScale :
      (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N => ENNReal.ofReal (c * cf i) * MeasureTheory.volume (Ef i))
        =
      ENNReal.ofReal c *
        (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N => ENNReal.ofReal (cf i) * MeasureTheory.volume (Ef i)) := by
    calc
      (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N => ENNReal.ofReal (c * cf i) * MeasureTheory.volume (Ef i))
          =
        (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N =>
            (ENNReal.ofReal c * ENNReal.ofReal (cf i)) * MeasureTheory.volume (Ef i)) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [ENNReal.ofReal_mul (le_of_lt hc)]
      _ =
        (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N =>
            ENNReal.ofReal c * (ENNReal.ofReal (cf i) * MeasureTheory.volume (Ef i))) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [mul_assoc]
      _ =
        ENNReal.ofReal c *
          (Finset.univ : Finset (Fin N)).sum
            (fun i : Fin N => ENNReal.ofReal (cf i) * MeasureTheory.volume (Ef i)) := by
            simpa using
              (Finset.mul_sum (s := (Finset.univ : Finset (Fin N)))
                (a := ENNReal.ofReal c)
                (f := fun i : Fin N => ENNReal.ofReal (cf i) * MeasureTheory.volume (Ef i))).symm

  calc
    lebesgueIntegralNonnegSimple (NonnegSimpleFunction.constMul c (le_of_lt hc) f)
        =
      (Finset.univ : Finset (Fin N)).sum
        (fun i : Fin N => ENNReal.ofReal (c * cf i) * MeasureTheory.volume (Ef i)) := hIntScaled
    _ =
      ENNReal.ofReal c *
        (Finset.univ : Finset (Fin N)).sum
          (fun i : Fin N => ENNReal.ofReal (cf i) * MeasureTheory.volume (Ef i)) := hEnnrealScale
    _ = ENNReal.ofReal c * lebesgueIntegralNonnegSimple f := by
      rw [hIntF]

/-- Helper for Proposition 8.1.4: the pointwise difference of two non-negative simple
functions is simple. -/
lemma helperForProposition_8_1_4_difference_isSimple {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f g : NonnegSimpleFunction Ω) :
    IsSimpleFunction Ω (fun x : Ω => g.1 x - f.1 x) := by
  have hneg : IsSimpleFunction Ω (fun x : Ω => -f.1 x) := by
    simpa using (IsSimpleFunction.const_mul (f := f.1) f.2.1 (-1 : ℝ))
  have hadd : IsSimpleFunction Ω (fun x : Ω => g.1 x + -f.1 x) :=
    IsSimpleFunction.add g.2.1 hneg
  simpa [sub_eq_add_neg] using hadd

/-- Helper for Proposition 8.1.4: if `f ≤ g` pointwise then `g - f` is pointwise nonnegative. -/
lemma helperForProposition_8_1_4_difference_nonneg {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f g : NonnegSimpleFunction Ω) (hfg : ∀ x : Ω, f.1 x ≤ g.1 x) :
    ∀ x : Ω, 0 ≤ g.1 x - f.1 x := by
  intro x
  exact sub_nonneg.mpr (hfg x)

/-- Helper for Proposition 8.1.4: the non-negative simple remainder `g - f`. -/
noncomputable def helperForProposition_8_1_4_difference {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f g : NonnegSimpleFunction Ω) (hfg : ∀ x : Ω, f.1 x ≤ g.1 x) :
    NonnegSimpleFunction Ω :=
  ⟨(fun x : Ω => g.1 x - f.1 x),
    ⟨helperForProposition_8_1_4_difference_isSimple f g,
      helperForProposition_8_1_4_difference_nonneg f g hfg⟩⟩

/-- Helper for Proposition 8.1.4: `f + (g - f) = g` as non-negative simple functions. -/
lemma helperForProposition_8_1_4_add_difference_eq {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f g : NonnegSimpleFunction Ω) (hfg : ∀ x : Ω, f.1 x ≤ g.1 x) :
    NonnegSimpleFunction.add f (helperForProposition_8_1_4_difference f g hfg) = g := by
  apply Subtype.ext
  funext x
  change f.1 x + (g.1 x - f.1 x) = g.1 x
  ring

/-- Proposition 8.1.4: if `f, g : Ω → ℝ` are non-negative simple functions and
`f(x) ≤ g(x)` for every `x ∈ Ω`, then `∫_Ω f dm ≤ ∫_Ω g dm`. -/
theorem lebesgueIntegralNonnegSimple_mono {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (f g : NonnegSimpleFunction Ω) (hfg : ∀ x : Ω, f.1 x ≤ g.1 x) :
    lebesgueIntegralNonnegSimple f ≤ lebesgueIntegralNonnegSimple g := by
  let h : NonnegSimpleFunction Ω := helperForProposition_8_1_4_difference f g hfg
  have hle :
      lebesgueIntegralNonnegSimple f
        ≤ lebesgueIntegralNonnegSimple f + lebesgueIntegralNonnegSimple h := by
    simpa [add_zero] using
      (add_le_add_left (a := lebesgueIntegralNonnegSimple f)
        (b := (0 : ENNReal)) (c := lebesgueIntegralNonnegSimple h) bot_le)
  calc
    lebesgueIntegralNonnegSimple f
        ≤ lebesgueIntegralNonnegSimple f + lebesgueIntegralNonnegSimple h := hle
    _ = lebesgueIntegralNonnegSimple (NonnegSimpleFunction.add f h) := by
      symm
      exact lebesgueIntegralNonnegSimple_add f h
    _ = lebesgueIntegralNonnegSimple g := by
      rw [show NonnegSimpleFunction.add f h = g by
        simpa [h] using helperForProposition_8_1_4_add_difference_eq f g hfg]

/-- Definition 8.4: A property `P` holds for almost every `x ∈ Ω` (with respect to `μ`)
if there is a measurable null set `N ⊆ Ω` such that `P x` holds for all `x ∈ Ω \ N`. -/
def HoldsForAlmostEverywhereOn {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (Ω : Set α) (P : α → Prop) : Prop :=
  ∃ N : Set α, N ⊆ Ω ∧ MeasurableSet N ∧ μ N = 0 ∧ ∀ ⦃x : α⦄, x ∈ Ω \ N → P x

/-- Helper for Proposition 8.2: almost-everywhere vanishing gives a null nonzero set. -/
lemma helperForProposition_8_2_nonzeroSetNull_of_aeEqZero {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f : α → ENNReal} (hAe : f =ᵐ[μ] 0) :
    μ {x | f x ≠ 0} = 0 := by
  have hAeProp : ∀ᵐ x ∂μ, f x = 0 := hAe
  have hNull : μ {x | ¬f x = 0} = 0 := (MeasureTheory.ae_iff).1 hAeProp
  simpa using hNull

/-- Helper for Proposition 8.2: convert `f = 0` almost everywhere to Definition 8.4 on `univ`. -/
lemma helperForProposition_8_2_holdsOnUniv_of_aeEqZero {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f : α → ENNReal} (hf : Measurable f) :
    (f =ᵐ[μ] 0) → HoldsForAlmostEverywhereOn μ Set.univ (fun x => f x = 0) := by
  intro hAe
  refine ⟨{x | f x ≠ 0}, ?_, ?_, ?_, ?_⟩
  · intro x hx
    simp
  · have hMeasEq : MeasurableSet {x | f x = 0} := hf (MeasurableSet.singleton 0)
    have hSetEq : {x | f x ≠ 0} = ({x | f x = 0})ᶜ := by
      ext x
      simp
    rw [hSetEq]
    exact hMeasEq.compl
  · exact helperForProposition_8_2_nonzeroSetNull_of_aeEqZero hAe
  · intro x hx
    have hxNot : x ∉ {x | f x ≠ 0} := hx.2
    by_contra hfx
    exact hxNot hfx

/-- Helper for Proposition 8.2: convert Definition 8.4 on `univ` to `f = 0` almost
everywhere. -/
lemma helperForProposition_8_2_aeEqZero_of_holdsOnUniv {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f : α → ENNReal} :
    HoldsForAlmostEverywhereOn μ Set.univ (fun x => f x = 0) → (f =ᵐ[μ] 0) := by
  intro hHolds
  rcases hHolds with ⟨N, hNsubset, hNmeas, hNnull, hOutside⟩
  have hSubset : {x | f x ≠ 0} ⊆ N := by
    intro x hxNe
    by_contra hxN
    have hxDiff : x ∈ Set.univ \ N := by
      exact ⟨trivial, hxN⟩
    have hxZero : f x = 0 := hOutside hxDiff
    exact hxNe hxZero
  have hNonzeroNull : μ {x | f x ≠ 0} = 0 := MeasureTheory.measure_mono_null hSubset hNnull
  have hAeProp : ∀ᵐ x ∂μ, f x = 0 := (MeasureTheory.ae_iff).2 (by simpa using hNonzeroNull)
  exact hAeProp

/-- Helper for Proposition 8.2: Definition 8.4 on `univ` is equivalent to `f = 0`
almost everywhere. -/
lemma helperForProposition_8_2_holdsOnUniv_iff_aeEqZero {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f : α → ENNReal} (hf : Measurable f) :
    HoldsForAlmostEverywhereOn μ Set.univ (fun x => f x = 0) ↔ (f =ᵐ[μ] 0) := by
  constructor
  · exact helperForProposition_8_2_aeEqZero_of_holdsOnUniv
  · exact helperForProposition_8_2_holdsOnUniv_of_aeEqZero hf

/-- Proposition 8.2: if `f : α → [0, ∞]` is measurable, then its integral is zero iff
`f x = 0` for `μ`-almost every `x`. -/
theorem proposition_8_2_lintegral_eq_zero_iff_holdsForAlmostEverywhereOn
    {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α) {f : α → ENNReal}
    (hf : Measurable f) :
    (∫⁻ x, f x ∂ μ) = 0 ↔ f =ᵐ[μ] 0 := by
  simpa using MeasureTheory.lintegral_eq_zero_iff hf

end Section01
end Chap08
