/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set MeasureTheory MeasurableSpace Real Encodable

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

-- Proof sketch: the forward implication is immediate because singleton sets are measurable in a
-- discrete measurable space. For the converse, use `measurable_to_countable'` on the countable
-- codomain, since every measurable set is a countable union of singleton fibers.
/-- Example 1.85 (1): Item (i). If the countable codomain `Ω'` carries the full powerset
`σ`-algebra, then `X : Ω → Ω'` is measurable if and only if every singleton fiber
`X ⁻¹' {ω'}` is measurable. -/
theorem measurable_iff_preimage_singleton_of_countable
    {Ω' : Type v} [MeasurableSpace Ω'] [Countable Ω'] [DiscreteMeasurableSpace Ω']
    {X : Ω → Ω'} :
    Measurable X ↔ ∀ ω' : Ω', MeasurableSet (X ⁻¹' ({ω'} : Set Ω')) := by
  constructor
  · intro hX ω'
    exact (measurableSet_singleton ω').preimage hX
  · intro hX
    exact measurable_to_countable' hX

private theorem borel_real_ne_top : borel ℝ ≠ ⊤ := by
  intro htop
  let s : Set (Set ℝ) := ⋃ q : ℚ, {Iic (q : ℝ)}
  have hs : Cardinal.mk s ≤ Cardinal.continuum := by
    calc
      Cardinal.mk s = Cardinal.mk (Set.range fun q : ℚ ↦ Iic (q : ℝ)) := by
        simp [s, iUnion_singleton_eq_range]
      _ ≤ Cardinal.mk ℚ := Cardinal.mk_range_le
      _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
      _ ≤ Cardinal.continuum := Cardinal.aleph0_le_continuum
  have hmeas : Cardinal.mk { t | @MeasurableSet ℝ (borel ℝ) t } ≤ Cardinal.continuum := by
    rw [Real.borel_eq_generateFrom_Iic_rat]
    exact MeasurableSpace.cardinal_measurableSet_le_continuum hs
  have hpow : Cardinal.continuum < Cardinal.mk { t | @MeasurableSet ℝ (borel ℝ) t } := by
    rw [htop]
    simpa using (show Cardinal.continuum < Cardinal.mk (Set ℝ) by
      rw [Cardinal.mk_set, Cardinal.mk_real]
      exact Cardinal.cantor Cardinal.continuum)
  exact not_lt_of_ge hmeas hpow

-- Proof sketch: if the identity map from `(ℝ, borel ℝ)` to `(ℝ, ⊤)` were measurable, then the
-- preimage of every subset of `ℝ` would be Borel. This contradicts the existence of non-Borel
-- subsets of `ℝ`.
/-- Example 1.85 (2): Item (i). For the uncountable codomain `ℝ` with the full powerset
`σ`-algebra, the identity map from `(ℝ, 𝓑(ℝ))` to `(ℝ, 2^ℝ)` is not measurable. -/
theorem not_measurable_id_real_to_powerset :
    ¬ @Measurable ℝ ℝ (borel ℝ) ⊤ id := by
  intro h
  have htop : borel ℝ = ⊤ := by
    apply top_unique
    intro s hs
    simpa using h hs
  exact borel_real_ne_top htop

/- Example 1.85 (3): Item (ii). The floor map `x ↦ ⌊x⌋` from `ℝ` to `ℤ` is measurable. -/
recall Int.measurable_floor

/- Example 1.85 (4): Item (ii). The ceiling map `x ↦ ⌈x⌉` from `ℝ` to `ℤ` is measurable. -/
recall Int.measurable_ceil

/- Example 1.85 (5): Item (ii). If `f : Ω → ℝ` is measurable, then the rounded-down map
`ω ↦ ⌊f ω⌋` is measurable. -/
recall Measurable.floor

/- Example 1.85 (6): Item (ii). If `f : Ω → ℝ` is measurable, then the rounded-up map
`ω ↦ ⌈f ω⌉` is measurable. -/
recall Measurable.ceil

private theorem isCountablySpanning_Iic_rat : IsCountablySpanning (⋃ q : ℚ, {Iic (q : ℝ)}) := by
  classical
  cases nonempty_encodable ℚ
  let e : ℕ → ℚ := fun n ↦ (@Encodable.decode ℚ _ n).getD 0
  refine ⟨fun n ↦ Iic (e n : ℝ), ?_, ?_⟩
  · intro n
    exact mem_iUnion.2 ⟨e n, by simp⟩
  · simpa [Real.iUnion_Iic_rat, e] using
      (Encodable.surjective_decode_getD ℚ 0).iUnion_comp fun q ↦ Iic (q : ℝ)

private theorem measurableSpace_pi_eq_generateFrom_Iic (d : ℕ) :
    MeasurableSpace.pi = generateFrom (range (Iic : (Fin d → ℝ) → Set (Fin d → ℝ))) := by
  let C : Set (Set ℝ) := ⋃ q : ℚ, {Iic (q : ℝ)}
  refine le_antisymm ?_ ?_
  · have hpi :
        generateFrom (pi univ '' pi univ (fun _ : Fin d ↦ C)) = MeasurableSpace.pi := by
      simpa [C] using
        (generateFrom_eq_pi (α := fun _ : Fin d ↦ ℝ) (C := fun _ : Fin d ↦ C)
          (fun _ ↦ Real.borel_eq_generateFrom_Iic_rat.symm)
          (fun _ ↦ isCountablySpanning_Iic_rat))
    rw [← hpi]
    exact generateFrom_mono <| by
      rintro _ ⟨s, hs, rfl⟩
      have hs' : ∀ i : Fin d, ∃ q : ℚ, Iic (q : ℝ) = s i := by
        intro i
        simpa [C] using hs i (mem_univ i)
      choose q hq using hs'
      refine mem_range.2 ⟨fun i ↦ (q i : ℝ), ?_⟩
      ext x
      constructor
      · intro hx
        show x ∈ pi univ s
        intro i _
        rw [← hq i]
        exact hx i
      · intro hx i
        have hxi : x i ∈ s i := hx i (mem_univ i)
        rw [← hq i] at hxi
        exact hxi
  · refine generateFrom_le ?_
    rintro _ ⟨b, rfl⟩
    rw [← pi_univ_Iic]
    exact MeasurableSet.univ_pi fun _ ↦ measurableSet_Iic

-- Proof sketch: for the forward implication, preimages of lower orthants are measurable because
-- these orthants are Borel. For the converse, Theorem 1.23 identifies the Borel `σ`-algebra on
-- `Fin d → ℝ` with the one generated by closed lower orthants.
/-- Example 1.85 (7): Item (iii). A map into `ℝ^d`, modeled as `Fin d → ℝ`, is measurable if and
only if the preimage of every closed lower orthant `(-∞, a] = Iic a` is measurable. -/
theorem measurable_iff_preimage_Iic
    {d : ℕ} {X : Ω → Fin d → ℝ} :
    Measurable X ↔ ∀ a : Fin d → ℝ, MeasurableSet (X ⁻¹' Iic a) := by
  constructor
  · intro hX a
    exact measurableSet_Iic.preimage hX
  · intro hX
    rw [measurable_iff_comap_le, measurableSpace_pi_eq_generateFrom_Iic d,
      MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_le ?_
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hX a
