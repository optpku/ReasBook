/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_25
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory preVariation
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A finite measurable partition of `Ω`, organized around mathlib's canonical finite-partition
owner on measurable sets. -/
abbrev MeasurableFinpartition (Ω : Type u) [MeasurableSpace Ω] :=
  Finpartition (⊤ : Subtype (MeasurableSet : Set Ω → Prop))

namespace MeasurableFinpartition

instance (part : MeasurableFinpartition Ω) : MeasurableSpace part.parts := ⊤

instance (part : MeasurableFinpartition Ω) : MeasurableSingletonClass part.parts where
  measurableSet_singleton _ := by
    trivial

private theorem biUnion_parts_eq_univ (part : MeasurableFinpartition Ω) :
    (⋃ s ∈ part.parts, ((s : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) = Set.univ := by
  simpa [Finset.sup_measurableSetSubtype_eq_biUnion] using
    congrArg (fun s : Subtype (MeasurableSet : Set Ω → Prop) ↦ (s : Set Ω)) part.sup_parts

private noncomputable def indexed (part : MeasurableFinpartition Ω) :
    IndexedPartition fun s : part.parts ↦
      ((s.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) := by
  classical
  refine IndexedPartition.mk' _ ?_ ?_ ?_
  · intro s t hst
    have hdisj :
        Disjoint (s.1 : Subtype (MeasurableSet : Set Ω → Prop)) t.1 :=
      part.disjoint s.2 t.2 (by simpa using hst)
    exact (disjoint_subtype_iff (fun {_ _} hx hy ↦ hx.inter hy) MeasurableSet.empty).1 hdisj
  · intro s
    rw [Set.nonempty_iff_ne_empty]
    intro hs
    apply part.ne_bot s.2
    ext ω
    simp [hs]
  · intro ω
    have :
        ω ∈ ⋃ s ∈ part.parts, ((s : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) := by
      rw [biUnion_parts_eq_univ part]
      simp
    simpa [Set.mem_iUnion] using this

/-- The canonical finite-valued coding of a measurable finite partition by its atoms. This is a
thin bridge from the intrinsic partition owner to a finite-valued measurable map. -/
noncomputable def toSimpleFunc (part : MeasurableFinpartition Ω) :
    SimpleFunc Ω part.parts where
  toFun := (indexed part).index
  measurableSet_fiber' s := by
    rw [show (indexed part).index ⁻¹' {s} =
      ((s.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) by
      ext ω
      change (indexed part).index ω = s ↔
        ω ∈ ((s.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)
      rw [← (indexed part).mem_iff_index_eq]]
    exact s.1.2
  finite_range' := Set.toFinite _

/-- The measurable finite partition associated to a finite-valued measurable map, with atoms given
by its nonempty fibers. This is a bridge from a finite-valued coding to the intrinsic partition
owner. -/
noncomputable def ofSimpleFunc {α : Type*} (f : SimpleFunc Ω α) : MeasurableFinpartition Ω := by
  classical
  let parts : Finset (Set Ω) := f.range.image fun a ↦ f ⁻¹' ({a} : Set α)
  have hparts : Setoid.IsPartition (parts : Set (Set Ω)) := by
    refine Set.PairwiseDisjoint.isPartition_of_exists_of_ne_empty ?_ ?_ ?_
    · intro s hs t ht hst
      refine Set.disjoint_left.2 fun ω hωs hωt ↦ hst ?_
      change s ∈ f.range.image (fun a ↦ f ⁻¹' ({a} : Set α)) at hs
      change t ∈ f.range.image (fun a ↦ f ⁻¹' ({a} : Set α)) at ht
      rcases Finset.mem_image.mp hs with ⟨a, ha, rfl⟩
      rcases Finset.mem_image.mp ht with ⟨b, hb, rfl⟩
      have hfa : f ω = a := by
        simpa using hωs
      have hfb : f ω = b := by
        simpa using hωt
      subst a
      subst b
      rfl
    · intro ω
      refine ⟨f ⁻¹' ({f ω} : Set α), ?_, by simp⟩
      change f ⁻¹' ({f ω} : Set α) ∈ f.range.image (fun a ↦ f ⁻¹' ({a} : Set α))
      exact Finset.mem_image.mpr ⟨f ω, f.mem_range_self ω, rfl⟩
    · change ∅ ∉ f.range.image (fun a ↦ f ⁻¹' ({a} : Set α))
      intro hempty
      rcases Finset.mem_image.mp hempty with ⟨a, ha, haeq⟩
      rcases f.mem_range.mp ha with ⟨ω, rfl⟩
      have : ω ∈ f ⁻¹' ({f ω} : Set α) := by
        simp
      simp [haeq] at this
  let P₀ : Finpartition (Set.univ : Set Ω) := hparts.finpartition
  exact P₀.toSubtype
    (fun {_ _} hx hy ↦ hx.union hy)
    (fun {_ _} hx hy ↦ hx.inter hy)
    MeasurableSet.empty
    MeasurableSet.univ
    (fun p hp ↦ by
      change p ∈ f.range.image (fun a ↦ f ⁻¹' ({a} : Set α)) at hp
      rcases Finset.mem_image.mp hp with ⟨a, ha, rfl⟩
      exact f.measurableSet_fiber a)

/-- The probability mass function obtained by pushing `P` forward to the finite set of partition
atoms. -/
noncomputable def toPMF (part : MeasurableFinpartition Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] : PMF part.parts :=
  let μ : Measure part.parts := P.map (toSimpleFunc part)
  letI : IsProbabilityMeasure μ :=
    Measure.isProbabilityMeasure_map (toSimpleFunc part).aemeasurable
  μ.toPMF

private theorem measurable_blockCode (τ : Ω → Ω) (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) (n : ℕ+) :
    Measurable (fun ω : Ω ↦ fun i : Fin n ↦ (toSimpleFunc part) ((τ^[i]) ω)) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  exact (toSimpleFunc part).measurable.comp (Measurable.iterate hτ i)

private noncomputable def blockCode (τ : Ω → Ω) (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) (n : ℕ+) :
    SimpleFunc Ω (Fin n → part.parts) where
  toFun := fun ω : Ω ↦ fun i : Fin n ↦ (toSimpleFunc part) ((τ^[i]) ω)
  measurableSet_fiber' s := measurable_blockCode τ hτ part n (measurableSet_singleton s)
  finite_range' := Set.toFinite _

/-- The length-`n` joined partition obtained by recording the first `n` iterates of `τ`. -/
noncomputable def block (τ : Ω → Ω) (hτ : Measurable τ)
    (part : MeasurableFinpartition Ω) (n : ℕ+) : MeasurableFinpartition Ω :=
  ofSimpleFunc (blockCode τ hτ part n)

/-- The Shannon entropy of the pushforward law of a finite measurable partition. -/
noncomputable def partitionEntropy (part : MeasurableFinpartition Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] : EReal :=
  entropy (part.toPMF P)

-- Proof sketch: unfold `partitionEntropy`; it is the Shannon entropy of the pushforward PMF of the
-- partition atoms under `P`.
/-- The partition entropy is the Shannon entropy of the induced finite-valued random variable on
partition atoms. -/
theorem partitionEntropy_def (part : MeasurableFinpartition Ω) (P : Measure Ω)
    [IsProbabilityMeasure P] :
    part.partitionEntropy P = entropy (part.toPMF P) :=
  rfl

/-- The entropy rate `h(P, τ; 𝒫)` of a finite measurable partition. -/
noncomputable def dynamicalEntropy (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → Ω) (hτ : Measurable τ) (part : MeasurableFinpartition Ω) : EReal :=
  sInf (Set.range fun n : ℕ+ ↦
    (part.block τ hτ n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹))

scoped[ProbabilityTheory] notation "h(" P ", " τ ", " hτ "; " part ")" =>
  MeasurableFinpartition.dynamicalEntropy P τ hτ part

-- Proof sketch: unfold `dynamicalEntropy`; by definition it is the infimum of the normalized block
-- entropies of the joined partitions.
/-- The partition dynamical entropy is the infimum of the normalized entropies of the joined block
partitions. -/
theorem dynamicalEntropy_def (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → Ω) (hτ : Measurable τ) (part : MeasurableFinpartition Ω) :
    h(P, τ, hτ; part) =
      sInf (Set.range fun n : ℕ+ ↦
        (part.block τ hτ n).partitionEntropy P * (((n : ℕ) : EReal)⁻¹)) :=
  rfl

end MeasurableFinpartition

/-- Definition 20.34: for a measurable self-map `τ` of a probability space `(Ω, 𝓐, P)`, the
Kolmogorov--Sinai entropy is the supremum of the partition entropies `h(P, τ; 𝒫)` over all finite
measurable partitions `𝒫` of `Ω`. For a probability-preserving dynamical system, this is the
textbook Kolmogorov--Sinai entropy. -/
noncomputable def kolmogorov_sinai_entropy (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → Ω) (hτ : Measurable τ) : EReal :=
  sSup (Set.range fun part : MeasurableFinpartition Ω ↦
    part.dynamicalEntropy P τ hτ)

scoped[ProbabilityTheory] notation "h(" P ", " τ ", " hτ ")" =>
  kolmogorov_sinai_entropy P τ hτ

-- Proof sketch: unfold `kolmogorov_sinai_entropy`; the definition is exactly the supremum of the
-- entropy rates of all finite measurable partitions.
/-- The Kolmogorov--Sinai entropy is the supremum of the entropy rates of finite measurable
partitions. -/
theorem kolmogorov_sinai_entropy_def (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → Ω) (hτ : Measurable τ) :
    h(P, τ, hτ) =
      sSup (Set.range fun part : MeasurableFinpartition Ω ↦
        h(P, τ, hτ; part)) :=
  rfl
