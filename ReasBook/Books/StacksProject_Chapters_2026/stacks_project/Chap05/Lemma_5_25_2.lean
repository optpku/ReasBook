module

public import Mathlib.Topology.Compactification.StoneCech
import Mathlib.Topology.Compactification.OnePoint.Basic
import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open Set Topology OnePoint

universe u

section

variable {X : Type u} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

/- Domain-style sampling for the Stone-Cech unit over a locally compact Hausdorff space:
- owner abstraction: `Topology.IsOpenEmbedding (stoneCechUnit : X → StoneCech X)`
- same-domain declarations inspected:
  `OnePoint.isOpenEmbedding_coe`,
  `continuous_stoneCechExtend`,
  `isDenseEmbedding_stoneCechUnit`,
  `Function.LeftInverse.isClosed_range`

Layer triage:
- `source-facing`: the canonical map identifies `X` with an open subspace of `StoneCech X`
- `core/canonical`: `Topology.IsOpenEmbedding` for `stoneCechUnit`
- `bridge/view`: extend the one-point compactification embedding along `stoneCechUnit`

Primitive data is just the canonical Stone-Cech unit together with the locally compact Hausdorff
hypothesis. The auxiliary maps into the open preimage subset are derived bridge data used only to
prove openness of the range, so this file should reuse the canonical owner declarations above
instead of introducing any parallel public wrapper for the image of `stoneCechUnit`.
-/
/-- Lemma 5.25.2: if `X` is Hausdorff and locally quasi-compact, then the canonical map from `X`
to its Stone-Cech compactification identifies `X` with an open subspace of `StoneCech X`. -/
theorem stoneCechUnit_isOpenEmbedding_of_locallyCompact_t2 :
    IsOpenEmbedding (stoneCechUnit : X → StoneCech X) := by
  have hcoe : IsOpenEmbedding ((↑) : X → OnePoint X) := OnePoint.isOpenEmbedding_coe
  -- Pull back the Tychonoff structure from the one-point compactification so that Stone-Cech
  -- extension is available for the ordinary inclusion.
  let _ : T35Space X := hcoe.isEmbedding.t35Space
  -- Extend the ordinary inclusion `X → OnePoint X` across the Stone-Cech compactification.
  set φ : StoneCech X → OnePoint X :=
    stoneCechExtend (OnePoint.continuous_coe : Continuous ((↑) : X → OnePoint X)) with hφ
  set rangeCoe : Set (OnePoint X) := Set.range ((↑) : X → OnePoint X) with hRangeCoe
  set U : Set (StoneCech X) := φ ⁻¹' rangeCoe with hU
  set R : Set (StoneCech X) := Set.range (stoneCechUnit : X → StoneCech X) with hR
  -- The Stone-Cech image lands in the ordinary locus of `OnePoint X`.
  have hsub : R ⊆ U := by
    rintro _ ⟨x, rfl⟩
    rw [hU, hRangeCoe]
    rw [Set.mem_preimage, hφ, stoneCechExtend_stoneCechUnit]
    exact Set.mem_range_self x
  let i : R → U := Set.inclusion hsub
  have hrangeCoe_subset : rangeCoe ⊆ Set.range ((↑) : X → OnePoint X) := by
    simpa [hRangeCoe] using
      (subset_rfl : Set.range ((↑) : X → OnePoint X) ⊆ Set.range ((↑) : X → OnePoint X))
  -- Identify the ordinary locus in `OnePoint X` with `X` itself.
  let e : ((↑) : X → OnePoint X) ⁻¹' rangeCoe ≃ₜ rangeCoe :=
    hcoe.isEmbedding.homeomorphOfSubsetRange hrangeCoe_subset
  have hu_mem (u : U) : φ u.1 ∈ rangeCoe := by
    change u.1 ∈ φ ⁻¹' rangeCoe
    simpa [hU] using u.2
  let q : U → rangeCoe := fun u ↦ ⟨φ u.1, hu_mem u⟩
  let toX : U → X := fun u ↦ (e.symm (q u)).1
  -- Retract the preimage `U` back onto the Stone-Cech range `R`.
  let p : U → R := fun u ↦
    Set.rangeFactorization (stoneCechUnit : X → StoneCech X) (toX u)
  have hp_left : Function.LeftInverse p i := by
    intro r
    apply Subtype.ext
    rcases r with ⟨z, hz⟩
    rcases hz with ⟨x, rfl⟩
    have hx_mem_R : stoneCechUnit x ∈ R := by
      rw [hR]
      exact Set.mem_range_self x
    let rx : R := ⟨stoneCechUnit x, hx_mem_R⟩
    have hx_mem_preimage : x ∈ ((↑) : X → OnePoint X) ⁻¹' rangeCoe := by
      rw [hRangeCoe]
      exact Set.mem_range_self x
    let x_in_preimage : ((↑) : X → OnePoint X) ⁻¹' rangeCoe := ⟨x, hx_mem_preimage⟩
    change stoneCechUnit (toX (i rx)) = stoneCechUnit x
    have hqix : q (i rx) = e x_in_preimage := by
      apply Subtype.ext
      change φ (stoneCechUnit x) = ((x : X) : OnePoint X)
      simp [hφ]
    have hx : e.symm (e x_in_preimage) = x_in_preimage := e.symm_apply_apply x_in_preimage
    change stoneCechUnit ((e.symm (q (i rx))).1) = stoneCechUnit x
    rw [hqix]
    exact congrArg (fun y ↦ stoneCechUnit y.1) hx
  have hφ_cont : Continuous φ := by
    simpa [hφ] using
      (continuous_stoneCechExtend
        (OnePoint.continuous_coe : Continuous ((↑) : X → OnePoint X)))
  have hq_cont : Continuous q := by
    exact (hφ_cont.comp continuous_subtype_val).subtype_mk hu_mem
  have htoX_cont : Continuous toX := by
    exact continuous_subtype_val.comp (Continuous.comp e.symm.continuous hq_cont)
  have hp_cont : Continuous p := by
    exact continuous_stoneCechUnit.rangeFactorization.comp htoX_cont
  have hi_cont : Continuous i := by
    simpa [i] using continuous_inclusion hsub
  -- Inside `U`, the inclusion of the Stone-Cech range is both closed and dense.
  have hclosed : IsClosed (Set.range i) := hp_left.isClosed_range hp_cont hi_cont
  have hdense : DenseRange i := by
    have hi_def : i = Set.inclusion hsub := rfl
    rw [hi_def]
    rw [denseRange_inclusion_iff hsub]
    intro u hu
    have hclosure : closure R = Set.univ := by
      rw [hR]
      exact DenseRange.closure_range denseRange_stoneCechUnit
    rw [hclosure]
    simp
  have hrange : Set.range i = Set.univ := by
    rw [← hclosed.closure_eq, DenseRange.closure_range hdense]
  have hUR : U ⊆ R := by
    intro z hz
    have hz_range : (⟨z, hz⟩ : U) ∈ Set.range i := by
      rw [hrange]
      simp
    rcases hz_range with ⟨r, hr⟩
    have hEq : (r : StoneCech X) = z := congrArg Subtype.val hr
    exact hEq ▸ r.2
  have hUeqR : U = R := Set.Subset.antisymm hUR hsub
  -- Once `U = R`, openness of the Stone-Cech image follows from openness of the ordinary locus.
  have hUopen : IsOpen U := by
    rw [hU]
    simpa [hRangeCoe] using hcoe.isOpen_range.preimage hφ_cont
  have hRopen : IsOpen R := hUeqR.symm ▸ hUopen
  refine ⟨isEmbedding_stoneCechUnit, ?_⟩
  simpa [hR] using hRopen

end
