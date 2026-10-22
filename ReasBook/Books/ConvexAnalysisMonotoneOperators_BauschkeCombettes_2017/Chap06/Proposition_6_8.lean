/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Set

open scoped BigOperators

section

variable {ι : Type v} {E : Type u}
variable [AddCommMonoid E] [Module ℝ E]

-- Proof sketch: apply `PointedCone.mem_hull_set` to the finite image `x '' ↑s`, then rewrite the
-- resulting finitely supported conical combination as a sum indexed by `s`.
/-- Membership in the pointed cone hull of the finite image `x '' ↑s` means admitting a finite
nonnegative linear combination representation using the generators `x i` with `i ∈ s`. -/
theorem mem_pointedConeHull_image_finset_iff {s : Finset ι} {x : ι → E} {y : E} :
    y ∈ (PointedCone.hull ℝ (x '' (s : Set ι)) : Set E) ↔
      ∃ a : ι → NNReal, ∑ i ∈ s, (a i : ℝ) • x i = y := by
  constructor
  · intro hy
    -- Reindex the finitely supported conical combination from the image set back to the source
    -- index set by choosing one generator index for each point in the finite support.
    have hy' :
        ∃ c : E →₀ ℝ, ↑c.support ⊆ x '' (s : Set ι) ∧ (∀ z, 0 ≤ c z) ∧
          c.sum (fun m r ↦ r • m) = y := by
      simpa using
        (PointedCone.mem_hull_set (R := ℝ) (s := x '' (s : Set ι)) (x := y)).mp hy
    rcases hy' with ⟨c, hc, hc_nonneg, rfl⟩
    classical
    let c' : {m // m ∈ c.support} →₀ ℝ := c.subtypeDomain (fun m ↦ m ∈ c.support)
    have hrep :
        ∀ m : {m // m ∈ c.support}, ∃ i, i ∈ s ∧ x i = m.1 := by
      intro m
      rcases hc m.2 with ⟨i, hi, hxi⟩
      exact ⟨i, hi, hxi⟩
    let rep : {m // m ∈ c.support} → ι := fun m ↦ Classical.choose (hrep m)
    have hrep_mem : ∀ m : {m // m ∈ c.support}, rep m ∈ s := by
      intro m
      simpa [rep] using (Classical.choose_spec (hrep m)).1
    have hrep_eq : ∀ m : {m // m ∈ c.support}, x (rep m) = m.1 := by
      intro m
      simpa [rep] using (Classical.choose_spec (hrep m)).2
    let e : {m // m ∈ c.support} ↪ ι := ⟨rep, by
        intro m₁ m₂ h
        apply Subtype.ext
        calc
          m₁.1 = x (rep m₁) := by rw [hrep_eq m₁]
          _ = x (rep m₂) := by rw [h]
          _ = m₂.1 := by rw [hrep_eq m₂]
      ⟩
    let d : ι →₀ ℝ := c'.embDomain e
    have hd_support : d.support ⊆ s := by
      intro i hi
      by_contra his
      have hnot_range : i ∉ Set.range e := by
        intro hi_range
        rcases hi_range with ⟨m, hm⟩
        have hmemb : e m ∈ s := by
          simpa [e] using hrep_mem m
        exact his (hm ▸ hmemb)
      rw [Finsupp.mem_support_iff] at hi
      exact hi (Finsupp.embDomain_notin_range e c' i hnot_range)
    have hd_nonneg : ∀ i, 0 ≤ d i := by
      intro i
      rw [Finsupp.embDomain_apply]
      split_ifs with hi
      · simpa [c'] using hc_nonneg hi.choose.1
      · simp
    refine ⟨fun i ↦ ⟨d i, hd_nonneg i⟩, ?_⟩
    calc
      (∑ i ∈ s, ((⟨d i, hd_nonneg i⟩ : NNReal) : ℝ) • x i) = (∑ i ∈ s, d i • x i) := by
        simp
      _ = Finset.sum d.support (fun i ↦ d i • x i) := by
        symm
        exact Finset.sum_subset hd_support fun i _ hi_not_mem ↦ by
          rw [Finsupp.notMem_support_iff.mp hi_not_mem, zero_smul]
      _ = d.sum (fun i r ↦ r • x i) := rfl
      _ = c'.sum (fun m r ↦ r • x (e m)) := by
        rw [Finsupp.sum_embDomain]
      _ = c'.sum (fun m r ↦ r • m.1) := by
        refine Finsupp.sum_congr ?_
        intro m hm
        simpa [e] using congrArg (fun z ↦ c' m • z) (hrep_eq m)
      _ = c.sum (fun m r ↦ r • m) := by
        have hemb :
            c'.embDomain (Function.Embedding.subtype fun m ↦ m ∈ c.support) = c := by
          calc
            c'.embDomain (Function.Embedding.subtype fun m ↦ m ∈ c.support) = c'.extendDomain := by
              symm
              rw [Finsupp.extendDomain_eq_embDomain_subtype]
            _ = c := by
              simpa [c'] using
                (Finsupp.extendDomain_subtypeDomain (f := c) (P := fun m ↦ m ∈ c.support)
                  (hf := fun m hm ↦ hm))
        calc
          c'.sum (fun m r ↦ r • m.1) =
              (c'.embDomain (Function.Embedding.subtype fun m ↦ m ∈ c.support)).sum
                (fun m r ↦ r • m) := by
                  symm
                  simpa using
                    (Finsupp.sum_embDomain
                      (f := Function.Embedding.subtype fun m ↦ m ∈ c.support)
                      (v := c') (g := fun m r ↦ r • m))
          _ = c.sum (fun m r ↦ r • m) := by rw [hemb]
  · rintro ⟨a, rfl⟩
    -- Each generator lies in the hull, so closure under nonnegative scaling and finite sums
    -- gives the required conical combination membership.
    exact Submodule.sum_mem _ fun i hi ↦
      (PointedCone.hull ℝ (x '' (s : Set ι))).smul_mem
        (show 0 ≤ (a i : ℝ) by exact_mod_cast (show 0 ≤ a i from (a i).2))
        (PointedCone.subset_hull ⟨i, hi, rfl⟩)

-- Proof sketch: `PointedCone.hull ℝ (x '' ↑s)` is the smallest pointed cone containing the image.
-- The convex cone hull of `x '' ↑s ∪ {0}` is pointed because it contains `0`, so the universal
-- properties of the two hull constructions identify them after coercing the pointed cone to a
-- convex cone.
/-- Proposition 6.8 at the cone-owner level: the pointed cone generated by the finite image
`x '' ↑s` is exactly the convex cone generated by the same image together with `0`. -/
theorem pointedConeHull_image_finset_eq_convexConeHull_image_union_zero
    (s : Finset ι) (x : ι → E) :
    (PointedCone.hull ℝ (x '' (s : Set ι)) : ConvexCone ℝ E) =
      ConvexCone.hull ℝ (x '' (s : Set ι) ∪ ({0} : Set E)) := by
  apply le_antisymm
  · intro y hy
    rcases (mem_pointedConeHull_image_finset_iff.mp hy) with ⟨a, rfl⟩
    -- The coefficient description turns hull membership into a finite sum of scaled generators.
    let K : PointedCone ℝ E :=
      (ConvexCone.hull ℝ (x '' (s : Set ι) ∪ ({0} : Set E))).toPointedCone
        (ConvexCone.subset_hull (Or.inr rfl))
    have hsum :
        ∑ i ∈ s, (a i : ℝ) • x i ∈ K := by
      exact Submodule.sum_mem _ fun i hi ↦ by
        have hx : x i ∈ K := by
          exact ConvexCone.subset_hull (Or.inl ⟨i, hi, rfl⟩)
        by_cases hai : a i = 0
        · simpa [hai] using (ConvexCone.subset_hull (Or.inr rfl) : (0 : E) ∈ K)
        · exact K.smul_mem
            (show 0 ≤ (a i : ℝ) by exact_mod_cast (show 0 ≤ a i from (a i).2))
            hx
    simpa [K] using hsum
  · -- The convex-cone hull of `x '' ↑s ∪ {0}` is contained in the pointed cone hull because the
    -- latter already contains every generator and the origin.
    exact ConvexCone.hull_min fun y hy ↦ by
      rcases hy with hy | rfl
      · exact PointedCone.subset_hull hy
      · exact (PointedCone.hull ℝ (x '' (s : Set ι))).zero_mem

end

section

variable {ι : Type v} {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [T2Space E] [ContinuousAdd E] [ContinuousConstSMul ℝ E] [ContinuousSMul ℝ E]

/-- Helper for Proposition 6.8: membership in the finite pointed cone hull can be rewritten using
coefficients indexed by the subtype `s`. -/
lemma mem_pointedConeHull_image_finset_iff_exists_nonneg_subtype_sum
    {s : Finset ι} {x : ι → E} {y : E} :
    y ∈ (PointedCone.hull ℝ (x '' (s : Set ι)) : Set E) ↔
      ∃ a : s → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i : s, a i • x i.1) = y := by
  classical
  rw [mem_pointedConeHull_image_finset_iff]
  constructor
  · rintro ⟨a, ha⟩
    -- Restrict the global nonnegative coefficients to the finite index subtype.
    refine ⟨fun i ↦ a i.1, fun i ↦ by exact_mod_cast (a i.1).2, ?_⟩
    calc
      ∑ i : s, (a i.1 : ℝ) • x i.1 = ∑ i ∈ s, (a i : ℝ) • x i := by
        simpa using (s.sum_attach (f := fun i ↦ (a i : ℝ) • x i))
      _ = y := ha
  · rintro ⟨a, ha_nonneg, ha_sum⟩
    -- Extend the subtype coefficients by zero outside `s`.
    let b : ι → NNReal := fun i ↦ if hi : i ∈ s then ⟨a ⟨i, hi⟩, ha_nonneg ⟨i, hi⟩⟩ else 0
    refine ⟨b, ?_⟩
    rw [← s.sum_attach (f := fun i ↦ (b i : ℝ) • x i)]
    simpa [b]

/-- Helper for Proposition 6.8: the coefficient linear map of a finite family sends a coefficient
function on `s` to the corresponding finite linear combination of the generators. -/
def coefficient_sum_linear_map
    (s : Finset ι) (x : ι → E) : (s → ℝ) →ₗ[ℝ] E :=
  Fintype.linearCombination ℝ (fun i : s ↦ x i.1)

/-- Helper for Proposition 6.8: the nonnegative orthant in the coefficient space `s → ℝ` is closed.
-/
lemma isClosed_nonnegative_subtype_coefficients
    (s : Finset ι) : IsClosed {a : s → ℝ | ∀ i, 0 ≤ a i} := by
  -- Each coordinate condition `0 ≤ a i` cuts out a closed halfspace, and the finite orthant is
  -- their intersection.
  simpa [Set.pi, Set.mem_Ici] using
    (isClosed_set_pi (i := (Set.univ : Set s)) (s := fun _ : s ↦ Set.Ici (0 : ℝ))
      (fun _ _ ↦ isClosed_Ici))

/-- Helper for Proposition 6.8: the simplicial cone generated by the finite family is exactly the
image of the nonnegative orthant under the coefficient map. -/
lemma image_nonnegative_subtype_coefficients_eq_pointedConeHull_image_finset
    (s : Finset ι) (x : ι → E) :
    coefficient_sum_linear_map s x '' {a : s → ℝ | ∀ i, 0 ≤ a i} =
      (PointedCone.hull ℝ (x '' (s : Set ι)) : Set E) := by
  ext y
  constructor
  · rintro ⟨a, ha_nonneg, rfl⟩
    -- The image description matches the subtype-coefficient membership criterion exactly.
    refine mem_pointedConeHull_image_finset_iff_exists_nonneg_subtype_sum.mpr ?_
    refine ⟨a, ha_nonneg, ?_⟩
    simp [coefficient_sum_linear_map, Fintype.linearCombination_apply]
  · intro hy
    -- Conversely, a cone point already comes with nonnegative subtype coefficients.
    rcases (mem_pointedConeHull_image_finset_iff_exists_nonneg_subtype_sum.mp hy) with
      ⟨a, ha_nonneg, ha_sum⟩
    refine ⟨a, ha_nonneg, ?_⟩
    simpa [coefficient_sum_linear_map, Fintype.linearCombination_apply] using ha_sum

/-- Helper for Proposition 6.8: a pointed cone generated by a finite linearly independent family is
closed. -/
lemma isClosed_pointedConeHull_image_finset_of_linearIndependent
    (s : Finset ι) (x : ι → E) (hlin : LinearIndependent ℝ (fun i : s ↦ x i.1)) :
    IsClosed (PointedCone.hull ℝ (x '' (s : Set ι)) : Set E) := by
  let coeffMap : (s → ℝ) →ₗ[ℝ] E := coefficient_sum_linear_map s x
  let P : Set (s → ℝ) := {a | ∀ i, 0 ≤ a i}
  have hcoeff_injective : Function.Injective coeffMap := by
    -- Linear independence makes the coefficient map injective on the finite coefficient space.
    simpa [coeffMap, coefficient_sum_linear_map] using hlin.fintypeLinearCombination_injective
  have hker : LinearMap.ker coeffMap = ⊥ := LinearMap.ker_eq_bot.mpr hcoeff_injective
  have hP : IsClosed P := isClosed_nonnegative_subtype_coefficients s
  letI : ContinuousNeg E := ContinuousNeg.of_continuousConstSMul ℝ E
  letI : IsTopologicalAddGroup E :=
    { toContinuousAdd := inferInstance
      toContinuousNeg := inferInstance }
  have hclosedEmbedding : Topology.IsClosedEmbedding coeffMap :=
    LinearMap.isClosedEmbedding_of_injective hker
  -- Route correction: work with the closed embedding of the coefficient map instead of the span.
  rw [← image_nonnegative_subtype_coefficients_eq_pointedConeHull_image_finset (s := s) (x := x)]
  simpa [coeffMap, P] using hclosedEmbedding.isClosedMap _ hP

/-- Helper for Proposition 6.8: if the finite generating family is linearly dependent, every point
of the cone belongs to a cone generated after erasing one generator. -/
lemma exists_mem_pointedConeHull_image_finset_erase_of_not_linearIndependent
    [DecidableEq ι]
    {s : Finset ι} {x : ι → E} {y : E}
    (hdep : ¬ LinearIndependent ℝ (fun i : s ↦ x i.1))
    (hy : y ∈ (PointedCone.hull ℝ (x '' (s : Set ι)) : Set E)) :
    ∃ j ∈ s,
      y ∈ (PointedCone.hull ℝ (x '' (((s.erase j) : Finset ι) : Set ι)) : Set E) := by
  classical
  rcases (mem_pointedConeHull_image_finset_iff.mp hy) with ⟨a, ha_sum⟩
  have hdepOn : ¬ LinearIndepOn ℝ x (s : Set ι) := by
    simpa [linearIndependent_restrict_iff] using hdep
  obtain ⟨β, hβsum, hβnz⟩ :=
    (not_linearIndepOn_finset_iff (R := ℝ) (v := x) (s := s)).mp hdepOn
  obtain ⟨β', hβ'sum, hβ'pos⟩ :
      ∃ β' : ι → ℝ, (∑ i ∈ s, β' i • x i = 0) ∧ ∃ i ∈ s, 0 < β' i := by
    by_cases hpos : ∃ i ∈ s, 0 < β i
    · exact ⟨β, hβsum, hpos⟩
    · refine ⟨fun i ↦ -β i, ?_, ?_⟩
      · simpa [neg_smul, Finset.sum_neg_distrib] using congrArg Neg.neg hβsum
      · rcases hβnz with ⟨i, hi, hβi_ne⟩
        have hβi_nonpos : β i ≤ 0 := le_of_not_gt (fun h ↦ hpos ⟨i, hi, h⟩)
        have hβi_neg : β i < 0 :=
          lt_of_le_of_ne hβi_nonpos (by simpa using hβi_ne)
        exact ⟨i, hi, by simpa using neg_pos.mpr hβi_neg⟩
  let positiveSupport : Finset ι := s.filter (fun i ↦ 0 < β' i)
  have hpositiveSupport_nonempty : positiveSupport.Nonempty := by
    rcases hβ'pos with ⟨i, hi, hβi_pos⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hβi_pos⟩⟩
  obtain ⟨j, hj_positiveSupport, hmin⟩ :=
    Finset.exists_min_image positiveSupport (fun i ↦ (a i : ℝ) / β' i)
      hpositiveSupport_nonempty
  have hj_mem : j ∈ s := (Finset.mem_filter.mp hj_positiveSupport).1
  have hj_pos : 0 < β' j := (Finset.mem_filter.mp hj_positiveSupport).2
  let γ : ℝ := (a j : ℝ) / β' j
  let δ : ι → ℝ := fun i ↦ (a i : ℝ) - γ * β' i
  have hγ_nonneg : 0 ≤ γ := by
    exact div_nonneg (by exact_mod_cast (a j).2) (le_of_lt hj_pos)
  have hδ_nonneg : ∀ i ∈ s, 0 ≤ δ i := by
    intro i hi
    by_cases hβi_pos : 0 < β' i
    · have hi_positiveSupport : i ∈ positiveSupport := Finset.mem_filter.mpr ⟨hi, hβi_pos⟩
      have hratio : γ ≤ (a i : ℝ) / β' i := hmin i hi_positiveSupport
      have hupper : γ * β' i ≤ (a i : ℝ) := (le_div_iff₀ hβi_pos).mp hratio
      exact sub_nonneg.mpr (by simpa [δ, mul_comm] using hupper)
    · have hβi_nonpos : β' i ≤ 0 := le_of_not_gt hβi_pos
      have hmul_nonpos : γ * β' i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hγ_nonneg hβi_nonpos
      have ha_nonneg : 0 ≤ (a i : ℝ) := by exact_mod_cast (a i).2
      exact sub_nonneg.mpr (le_trans hmul_nonpos ha_nonneg)
  have hδj : δ j = 0 := by
    have hj_ne : β' j ≠ 0 := ne_of_gt hj_pos
    have hmul : γ * β' j = (a j : ℝ) := by
      calc
        γ * β' j = ((a j : ℝ) / β' j) * β' j := rfl
        _ = (a j : ℝ) := by field_simp [hj_ne]
    calc
      δ j = (a j : ℝ) - γ * β' j := rfl
      _ = 0 := by simp [hmul]
  have hδ_sum : ∑ i ∈ s, δ i • x i = y := by
    calc
      ∑ i ∈ s, δ i • x i = ∑ i ∈ s, (((a i : ℝ) • x i) - ((γ * β' i) • x i)) := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        simp [δ, sub_smul, mul_smul]
      _ = (∑ i ∈ s, (a i : ℝ) • x i) - ∑ i ∈ s, (γ * β' i) • x i := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ i ∈ s, (a i : ℝ) • x i) - γ • ∑ i ∈ s, β' i • x i := by
        simp [Finset.smul_sum, mul_smul]
      _ = y := by
        rw [hβ'sum, smul_zero, sub_zero, ha_sum]
  let c : ι → NNReal := fun i ↦
    if hi : i ∈ s.erase j then ⟨δ i, hδ_nonneg i (Finset.mem_of_mem_erase hi)⟩ else 0
  have hc_sum : ∑ i ∈ s.erase j, (c i : ℝ) • x i = y := by
    calc
      ∑ i ∈ s.erase j, (c i : ℝ) • x i = ∑ i ∈ s.erase j, δ i • x i := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        have hij : i ≠ j := (Finset.mem_erase.mp hi).1
        have his : i ∈ s := (Finset.mem_erase.mp hi).2
        simp only [c, dif_pos hi]
        rfl
      _ = ∑ i ∈ s, δ i • x i := by
        have hsplitted :
            ∑ i ∈ s.erase j, δ i • x i + δ j • x j = ∑ i ∈ s, δ i • x i :=
          Finset.sum_erase_add s (fun i ↦ δ i • x i) hj_mem
        simpa [hδj] using hsplitted
      _ = y := hδ_sum
  exact ⟨j, hj_mem, (mem_pointedConeHull_image_finset_iff.mpr ⟨c, hc_sum⟩)⟩

/-- Helper for Proposition 6.8: a finitely generated dependent cone is a finite union of cones
obtained by erasing one generator. -/
lemma pointedConeHull_image_finset_eq_biUnion_erase_of_not_linearIndependent
    [DecidableEq ι]
    (s : Finset ι) (x : ι → E)
    (hdep : ¬ LinearIndependent ℝ (fun i : s ↦ x i.1)) :
    (PointedCone.hull ℝ (x '' (s : Set ι)) : Set E) =
      ⋃ j ∈ s, (PointedCone.hull ℝ (x '' (((s.erase j) : Finset ι) : Set ι)) : Set E) := by
  ext y
  constructor
  · intro hy
    -- The route correction is the textbook elimination step: kill one positive coefficient in a
    -- dependence relation to move `y` into a smaller finitely generated cone.
    rcases exists_mem_pointedConeHull_image_finset_erase_of_not_linearIndependent hdep hy with
      ⟨j, hj, hyj⟩
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, hyj⟩⟩
  · intro hy
    rcases Set.mem_iUnion.mp hy with ⟨j, hy⟩
    rcases Set.mem_iUnion.mp hy with ⟨hj, hyj⟩
    rcases (mem_pointedConeHull_image_finset_iff.mp hyj) with ⟨a, ha_sum⟩
    let b : ι → NNReal := fun i ↦ if hi : i ∈ s.erase j then a i else 0
    -- Extending the smaller-family coefficients by zero puts them back in the original cone.
    refine (mem_pointedConeHull_image_finset_iff.mpr ?_)
    refine ⟨b, ?_⟩
    calc
      ∑ i ∈ s, (b i : ℝ) • x i = ∑ i ∈ s.erase j, (b i : ℝ) • x i + (b j : ℝ) • x j := by
        exact (Finset.sum_erase_add s (fun i ↦ (b i : ℝ) • x i) hj).symm
      _ = ∑ i ∈ s.erase j, (a i : ℝ) • x i := by
        have hb_sum :
            ∑ i ∈ s.erase j, (b i : ℝ) • x i = ∑ i ∈ s.erase j, (a i : ℝ) • x i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hij : i ≠ j := (Finset.mem_erase.mp hi).1
          have his : i ∈ s := (Finset.mem_erase.mp hi).2
          simp [b, Finset.mem_erase, hij, his]
        have hbj : (b j : ℝ) • x j = 0 := by
          simp [b]
        rw [hbj, add_zero, hb_sum]
      _ = y := ha_sum

-- Proof sketch: realize the pointed cone hull of a finite family as the image of the positive
-- orthant in a finite-dimensional coefficient space under the linear map sending coefficients to
-- the corresponding conical combination. In the dependent case, use the textbook elimination of
-- one generator and induct on the number of generators.
/-- Proposition 6.8: the pointed cone generated by a finite family is already closed. -/
theorem isClosed_pointedConeHull_image_finset
    (s : Finset ι) (x : ι → E) :
    IsClosed (PointedCone.hull ℝ (x '' (s : Set ι)) : Set E) := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ t : Finset ι, t.card = n →
      IsClosed (PointedCone.hull ℝ (x '' (t : Set ι)) : Set E)
  have hP : ∀ n, (∀ m < n, P m) → P n := by
    intro n ih t ht
    by_cases hlin : LinearIndependent ℝ (fun i : t ↦ x i.1)
    · -- The simplicial branch is the closed-embedding argument on the coefficient map.
      exact isClosed_pointedConeHull_image_finset_of_linearIndependent t x hlin
    · -- Route correction: replace the unavailable global closed-image theorem with the source
      -- proof's finite-union decomposition into smaller cones.
      rw [pointedConeHull_image_finset_eq_biUnion_erase_of_not_linearIndependent t x hlin]
      refine isClosed_biUnion_finset ?_
      intro j hj
      have hcard : (t.erase j).card < n := by
        rw [← ht]
        exact Finset.card_erase_lt_of_mem hj
      exact ih (t.erase j).card hcard (t.erase j) rfl
  have hs_closed : P s.card := Nat.strong_induction_on (p := P) s.card hP
  exact hs_closed s rfl

-- Proof sketch: Proposition 6.2 identifies the closed conical hull of the convex hull of a set
-- with the closure of its canonical convex cone hull. For the finite generating set
-- `x '' ↑s ∪ {0}`, Proposition 6.8 shows that this closure is already unnecessary because the
-- pointed cone hull is closed.
/-- Proposition 6.8 in source-facing form: the cone
`PointedCone.hull ℝ (x '' ↑s)` is exactly the smallest closed convex cone containing the finite
family `x '' ↑s` together with `0`. -/
theorem pointedConeHull_image_finset_eq_closedConicalHull_convexHull_image_union_zero
    (s : Finset ι) (x : ι → E) :
    (PointedCone.hull ℝ (x '' (s : Set ι)) : Set E) =
      closedConicalHull (convexHull ℝ (x '' (s : Set ι) ∪ ({0} : Set E))) := by
  let S : Set E := x '' (s : Set ι) ∪ ({0} : Set E)
  have hclosed :
      closure ((PointedCone.hull ℝ (x '' (s : Set ι)) : Set E)) =
        closure ((ConvexCone.hull ℝ S : Set E)) := by
    simpa [S] using congrArg (fun C : ConvexCone ℝ E ↦ closure (C : Set E))
      (pointedConeHull_image_finset_eq_convexConeHull_image_union_zero s x)
  -- Once the finite cone is known to be closed, Proposition 6.2 rewrites it as the closed
  -- conical hull of the convex hull of the generators with `0`.
  calc
    (PointedCone.hull ℝ (x '' (s : Set ι)) : Set E) =
        closure ((PointedCone.hull ℝ (x '' (s : Set ι)) : Set E)) := by
          symm
          exact (isClosed_pointedConeHull_image_finset s x).closure_eq
    _ = closure ((ConvexCone.hull ℝ S : Set E)) := hclosed
    _ = ((ConvexCone.hull ℝ S).closure : Set E) := by
          rw [← ConvexCone.coe_closure]
    _ = closedConicalHull (convexHull ℝ S) := by
          symm
          exact closedConicalHull_convexHull_eq_closure_convexConeHull S

-- Proof sketch: combine the source-facing closed-conical-hull identity with Proposition 6.2 (8),
-- which identifies that closed conical hull with the closure of the canonical convex cone hull.
/-- Proposition 6.8 at the canonical owner level: for a finite family, the pointed cone hull is
already the closed convex cone generated by the image together with `0`. -/
theorem pointedConeHull_image_finset_eq_closure_convexConeHull_image_union_zero
    (s : Finset ι) (x : ι → E) :
    (PointedCone.hull ℝ (x '' (s : Set ι)) : Set E) =
      ((ConvexCone.hull ℝ (x '' (s : Set ι) ∪ ({0} : Set E))).closure : Set E) := by
  let S : Set E := x '' (s : Set ι) ∪ ({0} : Set E)
  -- This is the canonical-owner restatement of the preceding source-facing identity.
  calc
    (PointedCone.hull ℝ (x '' (s : Set ι)) : Set E) =
        closedConicalHull (convexHull ℝ S) :=
      pointedConeHull_image_finset_eq_closedConicalHull_convexHull_image_union_zero s x
    _ = ((ConvexCone.hull ℝ S).closure : Set E) :=
      closedConicalHull_convexHull_eq_closure_convexConeHull S

end

end Set
