/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Theorem_1_64
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_25
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Exercise_5_3_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Theorem_20_35
import Books.ProbabilityTheory_Klenke_2020.Items.Chap07.Exercise_7_4_1
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := by
  refine ⟨by
    rw [show (1 : ENNReal) = ENNReal.ofReal (1 : ℝ) by norm_num]
    exact AddCircle.measure_univ (1 : ℝ)
  ⟩

/-- Helper for Exercise 20.6.1: the atoms of a measurable finite partition cover the ambient
space. This local copy is needed because the owner `indexed` helper is private. -/
private theorem biUnion_parts_eq_univ {Ω : Type*} [MeasurableSpace Ω]
    (part : MeasurableFinpartition Ω) :
    (⋃ s ∈ part.parts, ((s : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) = Set.univ := by
  -- Proof comment: the partition atoms cover the whole ambient space.
  simpa [MeasureTheory.preVariation.Finset.sup_measurableSetSubtype_eq_biUnion] using
    congrArg (fun s : Subtype (MeasurableSet : Set Ω → Prop) ↦ (s : Set Ω)) part.sup_parts

/-- Helper for Exercise 20.6.1: a local indexed-partition model matching
`MeasurableFinpartition.toSimpleFunc`. This local copy is needed because the owner `indexed`
helper is private. -/
private noncomputable def indexedPart {Ω : Type*} [MeasurableSpace Ω]
    (part : MeasurableFinpartition Ω) :
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

/-- Helper for Exercise 20.6.1: a point belongs to the atom selected by the canonical
`toSimpleFunc` coding of a measurable finite partition. -/
private theorem mem_toSimpleFunc_atom {Ω : Type*} [MeasurableSpace Ω]
    (part : MeasurableFinpartition Ω) (ω : Ω) :
    ω ∈ (((part.toSimpleFunc ω).1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) := by
  -- Proof comment: unfold the local indexed-partition model so the selected atom contains `ω` by
  -- construction.
  change ω ∈ (((indexedPart part).index ω : part.parts).1 : Set Ω)
  exact (indexedPart part).mem_index ω

/-- Helper for Exercise 20.6.1: membership in a partition atom is equivalent to the canonical
`toSimpleFunc` code selecting that atom. -/
private theorem mem_atom_iff_toSimpleFunc_eq {Ω : Type*} [MeasurableSpace Ω]
    (part : MeasurableFinpartition Ω) {A : part.parts} {ω : Ω} :
    ω ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) ↔ part.toSimpleFunc ω = A := by
  -- Proof comment: after rewriting through the local indexed partition, membership is exactly the
  -- statement that the canonical index map chooses `A`.
  change ω ∈ ((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω) ↔
    (indexedPart part).index ω = A
  rw [← (indexedPart part).mem_iff_index_eq]

/-- Helper for Exercise 20.6.1: two points in the same atom of a measurable finite partition have
the same canonical partition code. -/
private theorem toSimpleFunc_eq_of_mem_atom {Ω : Type*} [MeasurableSpace Ω]
    (part : MeasurableFinpartition Ω) {A : part.parts} {ω ω' : Ω}
    (hω : ω ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)))
    (hω' : ω' ∈ (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω))) :
    part.toSimpleFunc ω = part.toSimpleFunc ω' := by
  -- Proof comment: both points are coded by the unique atom `A` containing them.
  rw [(mem_atom_iff_toSimpleFunc_eq part).mp hω, (mem_atom_iff_toSimpleFunc_eq part).mp hω']

/-- Helper for Exercise 20.6.1: every nonempty fiber of a simple function is one of the atoms of
the partition built from that simple function. -/
private theorem fiber_mem_parts_of_ofSimpleFunc {Ω : Type*} [MeasurableSpace Ω] {α : Type*}
    (f : SimpleFunc Ω α) {a : α} (ha : a ∈ f.range) :
    (⟨f ⁻¹' ({a} : Set α), f.measurableSet_fiber a⟩ :
      Subtype (MeasurableSet : Set Ω → Prop)) ∈
      (MeasurableFinpartition.ofSimpleFunc f).parts := by
  classical
  -- Proof comment: `ofSimpleFunc` stores exactly the nonempty singleton fibers of `f`.
  change (⟨f ⁻¹' ({a} : Set α), f.measurableSet_fiber a⟩ :
      Subtype (MeasurableSet : Set Ω → Prop)) ∈
      Finset.preimage (f.range.image (fun b ↦ f ⁻¹' ({b} : Set α)))
        Subtype.val Subtype.val_injective.injOn
  exact Finset.mem_preimage.mpr (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

/-- Helper for Exercise 20.6.1: an injective relabeling of a finite pmf preserves Shannon
entropy. -/
private theorem entropy_map_eq_of_injective {α β : Type*} [Finite α] [Finite β]
    (p : PMF α) (f : α → β) (hf : Function.Injective f) :
    entropy (PMF.map f p) = entropy p := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  let φ : β → ℝ := fun b ↦ ((PMF.map f p) b).toReal * Real.log (((PMF.map f p) b).toReal)
  have hmap : ∀ a : α, PMF.map f p (f a) = p a := by
    intro a
    -- Proof comment: injectivity collapses the mapped mass at `f a` to the single source point
    -- `a`.
    rw [PMF.map_apply]
    refine (tsum_eq_single a ?_).trans ?_
    · intro a' ha'
      have hneq : f a ≠ f a' := fun h => ha' ((hf h).symm)
      simp [hneq]
    · simp
  have hzero : ∀ b : β, b ∉ Set.range f → PMF.map f p b = 0 := by
    intro b hb
    -- Proof comment: outside the image of `f`, every term in the defining pushforward sum is
    -- zero.
    rw [PMF.map_apply, ENNReal.tsum_eq_zero]
    intro a
    by_cases hba : b = f a
    · exact (hb ⟨a, hba.symm⟩).elim
    · simp [hba]
  have himage :
      Finset.univ.filter (fun b : β ↦ b ∈ Set.range f) = (Finset.univ.image f) := by
    -- Proof comment: on a finite type, filtering by the range of `f` gives exactly the image of
    -- the whole source alphabet.
    ext b
    simp
  have hfilter_sum :
      Finset.univ.sum φ = (Finset.univ.filter (fun b : β ↦ b ∈ Set.range f)).sum φ := by
    -- Proof comment: the target points outside the image contribute zero to the entropy sum.
    have hsubset :
        Finset.univ.filter (fun b : β ↦ b ∈ Set.range f) ⊆ Finset.univ := by
      intro b hb
      simp
    have hvanish :
        ∀ b ∈ Finset.univ, b ∉ Finset.univ.filter (fun b : β ↦ b ∈ Set.range f) → φ b = 0 := by
      intro b hb hnot
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hnot
      have hb0 : PMF.map f p b = 0 := hzero b hnot
      dsimp [φ]
      rw [hb0]
      norm_num
    simpa using (Finset.sum_subset hsubset hvanish).symm
  have hreindex :
      (Finset.univ.image f).sum φ = Finset.univ.sum (fun a : α ↦ φ (f a)) := by
    -- Proof comment: reindex the image sum back along the injective relabeling.
    simpa using (Finset.sum_image (s := Finset.univ) (f := φ) hf.injOn)
  have hpointwise :
      Finset.univ.sum (fun a : α ↦ φ (f a)) =
        Finset.univ.sum (fun a : α ↦ (p a).toReal * Real.log ((p a).toReal)) := by
    -- Proof comment: on image points, the mapped pmf agrees with the original pmf.
    apply Finset.sum_congr rfl
    intro a ha
    dsimp [φ]
    rw [hmap a]
  rw [entropy_eq_sum, entropy_eq_sum]
  calc
    ((-(Finset.univ.sum φ) : ℝ) : EReal) =
        ((-((Finset.univ.filter (fun b : β ↦ b ∈ Set.range f)).sum φ) : ℝ) : EReal) := by
      simpa using congrArg (fun t : ℝ ↦ ((-t : ℝ) : EReal)) hfilter_sum
    _ = ((-((Finset.univ.image f).sum φ) : ℝ) : EReal) := by
      rw [himage]
    _ = ((-(Finset.univ.sum fun a : α ↦ φ (f a)) : ℝ) : EReal) := by
      simpa using congrArg (fun t : ℝ ↦ ((-t : ℝ) : EReal)) hreindex
    _ = ((-(Finset.univ.sum fun a : α ↦ (p a).toReal * Real.log ((p a).toReal)) : ℝ) : EReal) := by
      simpa using congrArg (fun t : ℝ ↦ ((-t : ℝ) : EReal)) hpointwise

/-- Helper for Exercise 20.6.1: every atom of `MeasurableFinpartition.ofSimpleFunc g` is the fiber
of `g` over some value in the range of `g`. -/
private theorem exists_fiber_eq_of_ofSimpleFunc_part {Ω : Type*} [MeasurableSpace Ω] {α : Type*}
    (g : SimpleFunc Ω α) (A : (MeasurableFinpartition.ofSimpleFunc g).parts) :
    ∃ a ∈ g.range, g ⁻¹' ({a} : Set α) =
      (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) := by
  classical
  have hA :
      (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) ∈
        g.range.image (fun a ↦ g ⁻¹' ({a} : Set α)) := by
    -- Proof comment: unpack the `ofSimpleFunc` atom back to the stored fiber presentation.
    have hA' :
        (A.1 : Subtype (MeasurableSet : Set Ω → Prop)) ∈
          Finset.preimage (g.range.image (fun a ↦ g ⁻¹' ({a} : Set α)))
            Subtype.val Subtype.val_injective.injOn := by
      simpa [MeasurableFinpartition.ofSimpleFunc] using A.2
    exact Finset.mem_preimage.mp hA'
  rcases Finset.mem_image.mp hA with ⟨a, ha, hAeq⟩
  exact ⟨a, ha, hAeq⟩

/-- Helper for Exercise 20.6.1: each atom of `MeasurableFinpartition.ofSimpleFunc g` remembers
the unique value whose fiber it is. -/
private noncomputable def ofSimpleFuncFiberValue {Ω : Type*} [MeasurableSpace Ω] {α : Type*}
    (g : SimpleFunc Ω α) (A : (MeasurableFinpartition.ofSimpleFunc g).parts) : α :=
  Classical.choose (exists_fiber_eq_of_ofSimpleFunc_part g A)

/-- Helper for Exercise 20.6.1: the underlying set of an `ofSimpleFunc` atom is exactly the fiber
over its remembered value. -/
private theorem ofSimpleFuncFiberValue_spec {Ω : Type*} [MeasurableSpace Ω] {α : Type*}
    (g : SimpleFunc Ω α) (A : (MeasurableFinpartition.ofSimpleFunc g).parts) :
    g ⁻¹' ({ofSimpleFuncFiberValue g A} : Set α) =
      (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) :=
  by
    -- Proof comment: unwrap the chosen representative value and read off the fiber equality from
    -- the existence witness used to define `ofSimpleFuncFiberValue`.
    exact (Classical.choose_spec (exists_fiber_eq_of_ofSimpleFunc_part g A)).2

/-- Helper for Exercise 20.6.1: the original simple function factors through the canonical atom
coding of the partition built from its fibers. -/
private theorem simpleFunc_eq_ofSimpleFuncFiberValue_comp_toSimpleFunc {Ω : Type*}
    [MeasurableSpace Ω] {α : Type*} (g : SimpleFunc Ω α) :
    g = fun ω ↦ ofSimpleFuncFiberValue g ((MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω) := by
  funext ω
  -- Proof comment: the point `ω` lies in its selected atom, and that atom is the fiber over the
  -- value of `g` at `ω`.
  have hmem := mem_toSimpleFunc_atom (MeasurableFinpartition.ofSimpleFunc g) ω
  have hspec := ofSimpleFuncFiberValue_spec g ((MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω)
  have : ω ∈ g ⁻¹' ({ofSimpleFuncFiberValue g ((MeasurableFinpartition.ofSimpleFunc g).toSimpleFunc ω)} : Set α) := by
    simpa [hspec] using hmem
  simpa using this

/-- Helper for Exercise 20.6.1: the remembered value labels `ofSimpleFunc` atoms injectively. -/
private theorem ofSimpleFuncFiberValue_injective {Ω : Type*} [MeasurableSpace Ω] {α : Type*}
    (g : SimpleFunc Ω α) :
    Function.Injective (ofSimpleFuncFiberValue g) := by
  intro A B hAB
  -- Proof comment: atoms with the same remembered value are the same singleton fiber, hence the
  -- same atom of `MeasurableFinpartition.ofSimpleFunc g`.
  apply Subtype.ext
  apply Subtype.ext
  calc
    (((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) =
        g ⁻¹' ({ofSimpleFuncFiberValue g A} : Set α) := by
          symm
          exact ofSimpleFuncFiberValue_spec g A
    _ = g ⁻¹' ({ofSimpleFuncFiberValue g B} : Set α) := by rw [hAB]
    _ = (((B.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) := by
          exact ofSimpleFuncFiberValue_spec g B

/-- Helper for Exercise 20.6.1: pushing a probability measure forward along a composition gives
the pmf pushforward of the intermediate law. -/
private theorem toPMF_eq_map_of_comp {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {α β : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α]
    [MeasurableSpace β] [MeasurableSingletonClass β] [Countable β]
    (f : Ω → α) (hf : Measurable f) (g : α → β) (hg : Measurable g)
    [IsProbabilityMeasure (Measure.map f P)]
    [IsProbabilityMeasure (Measure.map (fun ω ↦ g (f ω)) P)] :
    (Measure.map (fun ω ↦ g (f ω)) P).toPMF = PMF.map g ((Measure.map f P).toPMF) := by
  -- Proof comment: compare the two pmfs by converting both sides back to the corresponding
  -- pushforward probability measures.
  apply PMF.toMeasure_injective
  rw [Measure.toPMF_toMeasure, ← PMF.toMeasure_map]
  · rw [Measure.toPMF_toMeasure, Measure.map_map hg hf]
    rfl
  · exact hg

/-- Helper for Exercise 20.6.1: if one partition code factors through another, then the induced
pmf is the corresponding pushforward. -/
private theorem toPMF_eq_map_of_toSimpleFuncFactor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {q r : MeasurableFinpartition Ω} (Φ : r.parts → q.parts)
    (hΦ : (q.toSimpleFunc : Ω → q.parts) = fun ω ↦ Φ (r.toSimpleFunc ω)) :
    q.toPMF P = PMF.map Φ (r.toPMF P) := by
  let μq : Measure q.parts := P.map q.toSimpleFunc
  let μr : Measure r.parts := P.map r.toSimpleFunc
  letI : IsProbabilityMeasure μq :=
    Measure.isProbabilityMeasure_map q.toSimpleFunc.aemeasurable
  letI : IsProbabilityMeasure μr :=
    Measure.isProbabilityMeasure_map r.toSimpleFunc.aemeasurable
  -- Proof comment: compare both pmfs by rewriting them back to the pushforward measures that
  -- define them.
  change μq.toPMF = PMF.map Φ μr.toPMF
  apply PMF.toMeasure_injective
  rw [Measure.toPMF_toMeasure, ← PMF.toMeasure_map]
  · rw [Measure.toPMF_toMeasure]
    dsimp [μq, μr]
    rw [Measure.map_map (μ := P) (g := Φ) (f := r.toSimpleFunc)
      (Measurable.of_discrete (f := Φ)) r.toSimpleFunc.measurable]
    rw [hΦ]
    rfl
  · exact Measurable.of_discrete (f := Φ)

/-- Helper for Exercise 20.6.1: the Shannon contribution of a finite sum of nonnegative masses is
bounded by the sum of the individual Shannon contributions. -/
private theorem negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  by_cases hxy : x + y = 0
  · -- Proof comment: if the total mass is zero, both summands already vanish.
    have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  · -- Proof comment: normalize by the total mass and use the multiplicative `negMulLog` formula.
    set s : ℝ := x + y
    have hxy' : x + y ≠ 0 := by
      simpa [s] using hxy
    have hs : 0 < s := by
      dsimp [s]
      exact lt_of_le_of_ne (add_nonneg hx hy) (by simpa [ne_comm] using hxy')
    have hs_nonneg : 0 ≤ s := le_of_lt hs
    have hs_ne : s ≠ 0 := ne_of_gt hs
    have hxs : x = s * (x / s) := by
      field_simp [s, hs_ne]
    have hys : y = s * (y / s) := by
      field_simp [s, hs_ne]
    have hx_div_nonneg : 0 ≤ x / s := by positivity
    have hy_div_nonneg : 0 ≤ y / s := by positivity
    have hx_div_le_one : x / s ≤ 1 := by
      have hle : x ≤ s := by
        dsimp [s]
        linarith
      field_simp [hs_ne]
      linarith
    have hy_div_le_one : y / s ≤ 1 := by
      have hle : y ≤ s := by
        dsimp [s]
        linarith
      field_simp [hs_ne]
      linarith
    have hsum_div : x / s + y / s = 1 := by
      field_simp [s, hs_ne]
      ring
    have hx_term_nonneg : 0 ≤ s * Real.negMulLog (x / s) := by
      exact mul_nonneg hs_nonneg (Real.negMulLog_nonneg hx_div_nonneg hx_div_le_one)
    have hy_term_nonneg : 0 ≤ s * Real.negMulLog (y / s) := by
      exact mul_nonneg hs_nonneg (Real.negMulLog_nonneg hy_div_nonneg hy_div_le_one)
    have hsplit :
        Real.negMulLog s + (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) =
          ((x / s) * Real.negMulLog s + s * Real.negMulLog (x / s)) +
            ((y / s) * Real.negMulLog s + s * Real.negMulLog (y / s)) := by
      calc
        Real.negMulLog s + (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) =
            ((x / s + y / s) * Real.negMulLog s) +
              (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) := by
          rw [hsum_div]
          ring
        _ =
            ((x / s) * Real.negMulLog s + s * Real.negMulLog (x / s)) +
              ((y / s) * Real.negMulLog s + s * Real.negMulLog (y / s)) := by
          ring
    have hnegMulLog_x :
        Real.negMulLog x = (x / s) * Real.negMulLog s + s * Real.negMulLog (x / s) := by
      calc
        Real.negMulLog x = Real.negMulLog (s * (x / s)) := by
          exact congrArg Real.negMulLog hxs
        _ = (x / s) * Real.negMulLog s + s * Real.negMulLog (x / s) := by
          rw [Real.negMulLog_mul]
    have hnegMulLog_y :
        Real.negMulLog y = (y / s) * Real.negMulLog s + s * Real.negMulLog (y / s) := by
      calc
        Real.negMulLog y = Real.negMulLog (s * (y / s)) := by
          exact congrArg Real.negMulLog hys
        _ = (y / s) * Real.negMulLog s + s * Real.negMulLog (y / s) := by
          rw [Real.negMulLog_mul]
    calc
      Real.negMulLog (x + y) = Real.negMulLog s := by simp [s]
      _ ≤ Real.negMulLog s + (s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s)) := by
        have htail_nonneg :
            0 ≤ s * Real.negMulLog (x / s) + s * Real.negMulLog (y / s) := by
          linarith
        linarith
      _ =
          ((x / s) * Real.negMulLog s + s * Real.negMulLog (x / s)) +
            ((y / s) * Real.negMulLog s + s * Real.negMulLog (y / s)) := by
        exact hsplit
      _ = Real.negMulLog x + Real.negMulLog y := by
        rw [hnegMulLog_x, hnegMulLog_y]

/-- Helper for Exercise 20.6.1: the Shannon contribution of a finite sum of nonnegative masses is
bounded by the sum of the individual Shannon contributions. -/
private theorem negMulLog_sum_le_sum_negMulLog {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    Real.negMulLog (Finset.sum s w) ≤ Finset.sum s (fun i ↦ Real.negMulLog (w i)) := by
  induction s using Finset.cons_induction with
  | empty =>
      -- Proof comment: the empty sum has zero Shannon contribution.
      simp [Real.negMulLog_zero]
  | @cons a s ha ih =>
      -- Proof comment: split off one mass and apply the two-point superadditivity step.
      have hwa : 0 ≤ w a := hw a (by simp)
      have hws : ∀ i ∈ s, 0 ≤ w i := by
        intro i hi
        exact hw i (by simp [hi])
      have hsum_nonneg : 0 ≤ Finset.sum s w := Finset.sum_nonneg hws
      calc
        Real.negMulLog (Finset.sum (Finset.cons a s ha) w) =
            Real.negMulLog (w a + Finset.sum s w) := by
          rw [Finset.sum_cons]
        _ ≤ Real.negMulLog (w a) + Real.negMulLog (Finset.sum s w) :=
          negMulLog_add_le hwa hsum_nonneg
        _ ≤ Real.negMulLog (w a) + Finset.sum s (fun i ↦ Real.negMulLog (w i)) := by
          gcongr
          exact ih hws
        _ = Finset.sum (Finset.cons a s ha) (fun i ↦ Real.negMulLog (w i)) := by
          rw [Finset.sum_cons]

/-- Helper for Exercise 20.6.1: a deterministic relabeling of a finite pmf cannot increase
Shannon entropy. -/
private theorem entropy_map_le
    {α β : Type*} [Finite α] [Finite β] (p : PMF α) (Φ : α → β) :
    entropy (PMF.map Φ p) ≤ entropy p := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Fintype β := Fintype.ofFinite β
  have hmap_apply (b : β) :
      ((PMF.map Φ p) b).toReal =
        Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b)) (fun a ↦ (p a).toReal) := by
    -- Proof comment: rewrite the pushed-forward mass at `b` as the finite sum over the fiber
    -- `Φ ⁻¹' {b}`.
    calc
      ((PMF.map Φ p) b).toReal =
          (∑' a : α, if b = Φ a then p a else 0).toReal := by
        rw [PMF.map_apply]
      _ = (∑ a : α, if b = Φ a then p a else 0).toReal := by
        rw [tsum_fintype]
      _ = ∑ a : α, (if b = Φ a then p a else 0).toReal := by
        refine ENNReal.toReal_sum ?_
        intro a ha
        by_cases hab : b = Φ a
        · simp [hab, p.apply_ne_top a]
        · simp [hab]
      _ = Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b)) (fun a ↦ (p a).toReal) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro a ha
        by_cases hab : Φ a = b
        · simp [hab]
        · have hab' : b ≠ Φ a := by
            simpa [eq_comm] using hab
          simp [hab, hab']
  have hfiber :
      ∑ b : β, Real.negMulLog (((PMF.map Φ p) b).toReal) ≤
        (∑ b : β,
          Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b))
            fun a ↦ Real.negMulLog ((p a).toReal)) := by
    -- Proof comment: apply the finite superadditivity lemma on each fiber separately.
    refine Finset.sum_le_sum ?_
    intro b hb
    rw [hmap_apply b]
    refine negMulLog_sum_le_sum_negMulLog _ _ ?_
    intro a ha
    exact ENNReal.toReal_nonneg
  have hfiberwise :
      (∑ b : β,
        Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b))
          fun a ↦ Real.negMulLog ((p a).toReal)) =
        ∑ a : α, Real.negMulLog ((p a).toReal) := by
    -- Proof comment: reassemble the fiberwise sum to recover the original entropy sum.
    simpa using
      (Finset.sum_fiberwise (s := Finset.univ) (g := Φ)
        (f := fun a : α ↦ Real.negMulLog ((p a).toReal)))
  rw [entropy_eq_sum, entropy_eq_sum]
  apply EReal.coe_le_coe
  calc
    (-∑ b : β, ((PMF.map Φ p) b).toReal * Real.log (((PMF.map Φ p) b).toReal) : ℝ) =
        ∑ b : β, Real.negMulLog (((PMF.map Φ p) b).toReal) := by
      simp [Real.negMulLog_def]
    _ ≤ ∑ b : β,
          Finset.sum (Finset.univ.filter (fun a : α ↦ Φ a = b))
            fun a ↦ Real.negMulLog ((p a).toReal) := hfiber
    _ = ∑ a : α, Real.negMulLog ((p a).toReal) := hfiberwise
    _ = (-∑ a : α, (p a).toReal * Real.log ((p a).toReal) : ℝ) := by
      simp [Real.negMulLog_def]

/-- Helper for Exercise 20.6.1: a partition that factors through another finite measurable
partition cannot have larger one-step entropy. -/
private theorem partitionEntropy_le_of_toSimpleFuncFactor
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {q r : MeasurableFinpartition Ω} (Φ : r.parts → q.parts)
    (hΦ : (q.toSimpleFunc : Ω → q.parts) = fun ω ↦ Φ (r.toSimpleFunc ω)) :
    q.partitionEntropy P ≤ r.partitionEntropy P := by
  -- Proof comment: after identifying the pmf laws by pushforward, entropy monotonicity under a
  -- factor map gives the comparison.
  calc
    q.partitionEntropy P = entropy (PMF.map Φ (r.toPMF P)) := by
      rw [MeasurableFinpartition.partitionEntropy_def, toPMF_eq_map_of_toSimpleFuncFactor P Φ hΦ]
    _ ≤ entropy (r.toPMF P) := entropy_map_le (r.toPMF P) Φ
    _ = r.partitionEntropy P := by
      rw [MeasurableFinpartition.partitionEntropy_def]

/-- Helper for Exercise 20.6.1: the entropy of `MeasurableFinpartition.ofSimpleFunc g` is exactly
the entropy of the law of `g`. -/
private theorem partitionEntropy_ofSimpleFunc_eq_entropy_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {α : Type*}
    [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] [Finite α]
    (g : SimpleFunc Ω α) [IsProbabilityMeasure (Measure.map g P)] :
    (MeasurableFinpartition.ofSimpleFunc g).partitionEntropy P =
      entropy ((Measure.map g P).toPMF) := by
  let q : MeasurableFinpartition Ω := MeasurableFinpartition.ofSimpleFunc g
  let Φ : q.parts → α := ofSimpleFuncFiberValue g
  letI : IsProbabilityMeasure (Measure.map q.toSimpleFunc P) :=
    Measure.isProbabilityMeasure_map q.toSimpleFunc.aemeasurable
  have hfactor :
      g = fun ω ↦ Φ (q.toSimpleFunc ω) := by
    -- Proof comment: the `ofSimpleFunc` partition code records exactly the fiber that contains
    -- each point, and `Φ` remembers the fiber value.
    simpa [q, Φ] using simpleFunc_eq_ofSimpleFuncFiberValue_comp_toSimpleFunc g
  letI : IsProbabilityMeasure (Measure.map (fun ω ↦ Φ (q.toSimpleFunc ω)) P) := by
    simpa [hfactor] using (show IsProbabilityMeasure (Measure.map g P) from inferInstance)
  have hmap :
      (Measure.map g P).toPMF = PMF.map Φ (q.toPMF P) := by
    -- Proof comment: push forward first to partition atoms and then relabel each atom by its
    -- remembered `g`-value.
    simpa [MeasurableFinpartition.toPMF, q, Φ, hfactor] using
      (toPMF_eq_map_of_comp (P := P) (f := q.toSimpleFunc) (hf := q.toSimpleFunc.measurable)
        (g := Φ) (hg := Measurable.of_discrete (f := Φ)))
  rw [MeasurableFinpartition.partitionEntropy_def]
  calc
    entropy (q.toPMF P) = entropy (PMF.map Φ (q.toPMF P)) := by
      symm
      exact entropy_map_eq_of_injective (q.toPMF P) Φ (ofSimpleFuncFiberValue_injective g)
    _ = entropy ((Measure.map g P).toPMF) := by
      rw [← hmap]

/-- Helper for Exercise 20.6.1: each fiber of the transparent block code is measurable. -/
private theorem measurableSet_prefixBlockCode_fiber {Ω : Type*} [MeasurableSpace Ω]
    (τ : Ω → Ω) (hτ : Measurable τ) (part : MeasurableFinpartition Ω) (n : ℕ+)
    (s : Fin n → part.parts) :
    MeasurableSet ((fun ω : Ω ↦ fun i : Fin n ↦ part.toSimpleFunc ((τ^[i]) ω)) ⁻¹' {s}) := by
  have hmeas : Measurable (fun ω : Ω ↦ fun i : Fin n ↦ part.toSimpleFunc ((τ^[i]) ω)) := by
    -- Proof comment: each coordinate of the block code is measurable.
    refine measurable_pi_lambda _ fun i ↦ ?_
    exact (part.toSimpleFunc).measurable.comp (Measurable.iterate hτ i)
  exact hmeas (measurableSet_singleton s)

/-- Helper for Exercise 20.6.1: the transparent block code records the first `n` visited atoms of
`part`. -/
private noncomputable def prefixBlockCode {Ω : Type*} [MeasurableSpace Ω]
    (τ : Ω → Ω) (hτ : Measurable τ) (part : MeasurableFinpartition Ω) (n : ℕ+) :
    SimpleFunc Ω (Fin n → part.parts) where
  toFun := fun ω : Ω ↦ fun i : Fin n ↦ part.toSimpleFunc ((τ^[i]) ω)
  measurableSet_fiber' := measurableSet_prefixBlockCode_fiber τ hτ part n
  finite_range' := Set.toFinite _

/-- Helper for Exercise 20.6.1: the owner block partition is definitionally the partition built
from the transparent block code. -/
private theorem block_eq_ofSimpleFunc_prefixBlockCode {Ω : Type*} [MeasurableSpace Ω]
    {τ : Ω → Ω} (hτ : Measurable τ) (part : MeasurableFinpartition Ω) (n : ℕ+) :
    part.block τ hτ n = MeasurableFinpartition.ofSimpleFunc (prefixBlockCode τ hτ part n) := by
  -- Proof comment: both sides are the same owner `ofSimpleFunc` presentation of the block code.
  rfl

/-- The mod-one doubling map on the additive-circle model of `[0,1)`. -/
def modOneDoubling : UnitAddCircle → UnitAddCircle :=
  fun x ↦ (2 : ℤ) • x

-- Proof sketch: multiplication by `2` on `AddCircle 1` is a continuous surjective group
-- endomorphism preserving Haar measure; identify Haar measure on `AddCircle 1` with Lebesgue
-- measure on `[0,1)`.
/-- The mod-one doubling map preserves Lebesgue/Haar measure on the circle. -/
theorem modOneDoubling_measurePreserving :
    MeasurePreserving modOneDoubling volume volume := by
  simpa [modOneDoubling] using
    (Measure.measurePreserving_zsmul volume (by norm_num : (2 : ℤ) ≠ 0))

/-- Helper for Exercise 20.6.1: the right half of `UnitAddCircle`, viewed through the standard
`[0,1)` chart. -/
noncomputable def modOneDoublingRightHalf : Set UnitAddCircle :=
  (fun x : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 x : ℝ)) ⁻¹' Set.Ico (1 / 2 : ℝ) 1

/-- Helper for Exercise 20.6.1: the right-half atom is measurable. -/
private theorem measurableSet_modOneDoublingRightHalf :
    MeasurableSet modOneDoublingRightHalf := by
  -- Proof comment: pull the half-interval back through the measurable `[0,1)` chart.
  simpa [modOneDoublingRightHalf] using
    (MeasurableSet.preimage measurableSet_Ico
      (measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable))

/-- Helper for Exercise 20.6.1: the measurable right-half atom packaged for
`MeasurableFinpartition`. -/
private noncomputable def modOneDoublingRightHalfSet :
    Subtype (MeasurableSet : Set UnitAddCircle → Prop) :=
  ⟨modOneDoublingRightHalf, measurableSet_modOneDoublingRightHalf⟩

/-- Helper for Exercise 20.6.1: the measurable left-half atom packaged for
`MeasurableFinpartition`. -/
private noncomputable def modOneDoublingLeftHalfSet :
    Subtype (MeasurableSet : Set UnitAddCircle → Prop) :=
  ⟨modOneDoublingRightHalfᶜ, measurableSet_modOneDoublingRightHalf.compl⟩

/-- Helper for Exercise 20.6.1: the two half-circle atoms are pairwise disjoint. -/
private theorem modOneDoublingHalfPartition_pairwiseDisjoint :
    ({modOneDoublingRightHalfSet, modOneDoublingLeftHalfSet} :
        Finset (Subtype (MeasurableSet : Set UnitAddCircle → Prop))).SupIndep id := by
  -- Proof comment: the two atoms are complementary, so the only nontrivial overlap is empty.
  refine Finset.supIndep_iff_pairwiseDisjoint.mpr ?_
  intro a ha b hb hab
  simp at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (hab rfl).elim
  · intro s hs_right hs_left x hx
    exact (hs_left hx) (hs_right hx)
  · intro s hs_left hs_right x hx
    exact (hs_left hx) (hs_right hx)
  · exact (hab rfl).elim

/-- Helper for Exercise 20.6.1: the two half-circle atoms cover all of `UnitAddCircle`. -/
private theorem modOneDoublingHalfPartition_sup_eq_univ :
    (({modOneDoublingRightHalfSet, modOneDoublingLeftHalfSet} :
        Finset (Subtype (MeasurableSet : Set UnitAddCircle → Prop))).sup id) = ⊤ := by
  -- Proof comment: a set together with its complement has union `univ`.
  ext x
  simp [modOneDoublingRightHalfSet, modOneDoublingLeftHalfSet, Finset.sup_insert,
    Finset.sup_singleton]

/-- Helper for Exercise 20.6.1: the canonical partition of `UnitAddCircle` into the two halves
`[0,1/2)` and `[1/2,1)` in the `[0,1)` model. -/
noncomputable def modOneDoublingHalfPartition : MeasurableFinpartition UnitAddCircle :=
  Finpartition.ofErase {modOneDoublingRightHalfSet, modOneDoublingLeftHalfSet}
    modOneDoublingHalfPartition_pairwiseDisjoint
    modOneDoublingHalfPartition_sup_eq_univ

/-- Helper for Exercise 20.6.1: the `n`th iterate of `modOneDoubling` is multiplication by
`2 ^ n` on `UnitAddCircle`. -/
private theorem modOneDoubling_iterate_eq_zsmul_pow (n : ℕ) :
    modOneDoubling^[n] = fun x : UnitAddCircle ↦ ((2 : ℤ) ^ n) • x := by
  -- Proof comment: iterate the fixed doubling endomorphism and collect the repeated `zsmul`
  -- factors into the integer power `2 ^ n`.
  induction n with
  | zero =>
      funext x
      simp
  | succ n ih =>
      funext x
      simp [Function.iterate_succ_apply', modOneDoubling, ih, pow_succ, smul_smul, mul_comm]

/-- Helper for Exercise 20.6.1: on a chart point `x ∈ [0,1)`, the `[0,1)` coordinate of the
`n`th doubling iterate is the fractional part of `2 ^ n * x`. -/
private theorem equivIco_modOneDoubling_iterate_eq_fract_pow_mul
    (n : ℕ) (x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) :
    (AddCircle.equivIco (1 : ℝ) 0 ((modOneDoubling^[n]) ((x : ℝ) : UnitAddCircle)) : ℝ) =
      Int.fract ((((2 : ℤ) ^ n : ℤ) : ℝ) * (x : ℝ)) := by
  -- Proof comment: rewrite the iterate as integer multiplication on the circle, then evaluate the
  -- canonical `[0,1)` chart of the resulting quotient class by the standard `Int.fract` formula.
  rw [modOneDoubling_iterate_eq_zsmul_pow]
  change (AddCircle.equivIco (1 : ℝ) 0 (((((2 : ℤ) ^ n) • (x : ℝ)) : ℝ) : UnitAddCircle) : ℝ) =
    Int.fract ((((2 : ℤ) ^ n : ℤ) : ℝ) * (x : ℝ))
  simpa [zsmul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
    (AddCircle.coe_equivIco_mk_apply
      (p := (1 : ℝ)) (x := (((2 : ℤ) ^ n) • (x : ℝ))))

/-- Helper for Exercise 20.6.1: the parity of `⌊2 y⌋` records whether the fractional part of `y`
lies in the right half of `[0,1)`. -/
private theorem finTwoEquiv_floorTwoMul_eq_true_iff_fract_mem_rightHalf {y : ℝ} (hy : 0 ≤ y) :
    finTwoEquiv (Fin.ofNat 2 ⌊2 * y⌋₊) = true ↔ Int.fract y ∈ Set.Ico (1 / 2 : ℝ) 1 := by
  have hfin_mod (n : ℕ) : finTwoEquiv (Fin.ofNat 2 n) = true ↔ n % 2 = 1 := by
    have htrue : finTwoEquiv (1 : Fin 2) = true := by
      decide
    have hcast_iff : Fin.ofNat 2 n = (1 : Fin 2) ↔ n % 2 = 1 := by
      rw [Fin.ext_iff]
      simp [Fin.val_natCast]
    constructor
    · intro h
      have hcast : Fin.ofNat 2 n = (1 : Fin 2) := by
        apply finTwoEquiv.injective
        simpa [htrue] using h
      exact hcast_iff.mp hcast
    · intro h
      have hcast : Fin.ofNat 2 n = (1 : Fin 2) := hcast_iff.mpr h
      simpa [htrue] using congrArg finTwoEquiv hcast
  have hy_decomp : y = Int.fract y + (⌊y⌋₊ : ℝ) := by
    -- Proof comment: replace the integer floor term in `fract_add_floor` by the nonnegative
    -- natural floor, since `hy` keeps the floor of `y` nonnegative.
    calc
      y = Int.fract y + (⌊y⌋ : ℤ) := by
        simpa [add_comm] using (Int.fract_add_floor y).symm
      _ = Int.fract y + (⌊y⌋₊ : ℝ) := by
        congr 1
        exact_mod_cast (Int.natCast_floor_eq_floor hy).symm
  have hmul :
      2 * (Int.fract y + (⌊y⌋₊ : ℝ)) = 2 * Int.fract y + (2 * ⌊y⌋₊ : ℝ) := by
    ring
  have hfloor_split : ⌊2 * y⌋₊ = ⌊2 * Int.fract y⌋₊ + 2 * ⌊y⌋₊ := by
    -- Proof comment: after splitting `y` into fractional and integral parts, the natural floor
    -- only sees the fractional contribution plus an even natural offset.
    have hy_two :
        2 * y = 2 * Int.fract y + (2 * ⌊y⌋₊ : ℝ) := by
      calc
        2 * y = 2 * (Int.fract y + (⌊y⌋₊ : ℝ)) := by
          simpa using congrArg (fun t : ℝ ↦ 2 * t) hy_decomp
        _ = 2 * Int.fract y + (2 * ⌊y⌋₊ : ℝ) := hmul
    calc
      ⌊2 * y⌋₊ = ⌊2 * Int.fract y + (2 * ⌊y⌋₊ : ℝ)⌋₊ := by
        rw [hy_two]
      _ = ⌊2 * Int.fract y⌋₊ + 2 * ⌊y⌋₊ := by
        simpa using (Nat.floor_add_natCast (a := 2 * Int.fract y) (n := 2 * ⌊y⌋₊))
  have hfloor_fract_lt_two : ⌊2 * Int.fract y⌋₊ < 2 := by
    -- Proof comment: because `fract y < 1`, doubling it stays below `2`, so its natural floor is
    -- either `0` or `1`.
    rw [Nat.floor_lt (show 0 ≤ 2 * Int.fract y by
      exact mul_nonneg (by norm_num) (Int.fract_nonneg y))]
    have htwo : 2 * Int.fract y < (2 : ℝ) := by
      nlinarith [Int.fract_lt_one y]
    simpa using htwo
  have hmod :
      ⌊2 * y⌋₊ % 2 = ⌊2 * Int.fract y⌋₊ := by
    -- Proof comment: the extra term `2 * ⌊y⌋₊` is even, so it disappears modulo `2`.
    rw [hfloor_split]
    omega
  have hfloor_fract :
      ⌊2 * Int.fract y⌋₊ = 1 ↔ Int.fract y ∈ Set.Ico (1 / 2 : ℝ) 1 := by
    -- Proof comment: on the unit interval, doubling lands in `[1,2)` exactly on the right half
    -- `[1/2, 1)`.
    rw [Nat.floor_eq_iff (show 0 ≤ 2 * Int.fract y by
      exact mul_nonneg (by norm_num) (Int.fract_nonneg y))]
    constructor
    · intro h
      norm_num at h
      constructor
      · have hhalf : (1 : ℝ) ≤ 2 * Int.fract y := by exact_mod_cast h.1
        nlinarith
      · nlinarith [h.2]
    · intro h
      constructor
      · have hhalf : (1 / 2 : ℝ) ≤ Int.fract y := h.1
        have hone : (1 : ℝ) ≤ 2 * Int.fract y := by
          nlinarith
        simpa using hone
      · have hlt : Int.fract y < (1 : ℝ) := h.2
        have hadd_lt : Int.fract y + Int.fract y < (1 : ℝ) + 1 := add_lt_add hlt hlt
        simpa [two_mul] using hadd_lt
  calc
    finTwoEquiv (Fin.ofNat 2 ⌊2 * y⌋₊) = true ↔ ⌊2 * y⌋₊ % 2 = 1 := hfin_mod _
    _ ↔ ⌊2 * Int.fract y⌋₊ = 1 := by rw [hmod]
    _ ↔ Int.fract y ∈ Set.Ico (1 / 2 : ℝ) 1 := hfloor_fract

/-- Helper for Exercise 20.6.1: the `m`th binary digit of a chart point records whether the
`m`th doubling iterate falls into the right-half atom. -/
private theorem modOneDoublingDigit_eq_rightHalf_iff
    (x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) (m : ℕ) :
    finTwoEquiv (Real.digits (x : ℝ) 2 m) = true ↔
      ((modOneDoubling^[m]) ((x : ℝ) : UnitAddCircle)) ∈ modOneDoublingRightHalf := by
  let y : ℝ := ((((2 : ℤ) ^ m : ℤ) : ℝ) * (x : ℝ))
  have hy : 0 ≤ y := by
    dsimp [y]
    have hpow : (0 : ℝ) ≤ ((((2 : ℤ) ^ m : ℤ) : ℝ)) := by
      norm_num
    exact mul_nonneg hpow x.2.1
  -- Proof comment: rewrite the right-half membership through the chart formula for doubling
  -- iterates, then normalize the binary digit to the parity test from the previous lemma.
  rw [modOneDoublingRightHalf, Set.mem_preimage]
  rw [equivIco_modOneDoubling_iterate_eq_fract_pow_mul]
  have hdigit :
      Real.digits (x : ℝ) 2 m = Fin.ofNat 2 ⌊2 * y⌋₊ := by
    change Fin.ofNat 2 ⌊(x : ℝ) * 2 ^ (m + 1)⌋₊ = Fin.ofNat 2 ⌊2 * y⌋₊
    congr 1
    dsimp [y]
    norm_num [pow_succ, mul_assoc, mul_left_comm, mul_comm]
  rw [hdigit]
  exact finTwoEquiv_floorTwoMul_eq_true_iff_fract_mem_rightHalf hy

/-- Helper for Exercise 20.6.1: reconstructing a chart point from its binary digits recovers the
original point of `[0,1)`. -/
private theorem fromBinary_digits_eq_self (x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) :
    (((Real.fromBinary (fun n ↦ finTwoEquiv (Real.digits (x : ℝ) 2 n)) :
        unitInterval) : ℝ)) = (x : ℝ) := by
  -- Proof comment: unfold `Real.fromBinary`, identify its `Fin 2`-digit sequence with
  -- `Real.digits`, and then apply the canonical `Real.ofDigits_digits` reconstruction theorem on
  -- `[0,1)`.
  unfold Real.fromBinary
  change Real.ofDigits
      ((Homeomorph.piCongrRight fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
        (fun n ↦ finTwoEquiv (Real.digits (x : ℝ) 2 n))) = (x : ℝ)
  have hdigits :
      ((Homeomorph.piCongrRight fun _ ↦ finTwoEquiv.toHomeomorphOfDiscrete.symm)
        (fun n ↦ finTwoEquiv (Real.digits (x : ℝ) 2 n))) =
        fun n ↦ Real.digits (x : ℝ) 2 n := by
    funext n
    change finTwoEquiv.symm (finTwoEquiv (Real.digits (x : ℝ) 2 n)) = Real.digits (x : ℝ) 2 n
    simp
  rw [hdigits]
  let x' : Set.Ico (0 : ℝ) 1 := ⟨(x : ℝ), by simpa [zero_add] using x.2⟩
  simpa [x'] using Real.ofDigits_digits (b := 2) (by norm_num) x'.2

/-- Helper for Exercise 20.6.1: the right-half itinerary of a circle point is encoded as a binary
sequence. -/
private noncomputable def modOneDoublingBinaryCode (z : UnitAddCircle) : BernoulliSequence :=
  fun n ↦ if ((modOneDoubling^[n]) z) ∈ modOneDoublingRightHalf then true else false

/-- Helper for Exercise 20.6.1: in the `[0,1)` chart, the binary code of the orbit agrees with the
ordinary binary digits of the chart coordinate. -/
private theorem modOneDoublingBinaryCode_eq_chartDigits (z : UnitAddCircle) :
    modOneDoublingBinaryCode z =
      fun n ↦ finTwoEquiv (Real.digits ((AddCircle.equivIco (1 : ℝ) 0 z :
        Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ)
        2 n) := by
  let x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1) := AddCircle.equivIco (1 : ℝ) 0 z
  have hx :
      (((x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ) : UnitAddCircle) = z := by
    -- Proof comment: `equivIco` followed by the quotient map is the identity on the circle.
    exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply z
  funext n
  by_cases hmem : ((modOneDoubling^[n]) z) ∈ modOneDoublingRightHalf
  · have hdigit : finTwoEquiv (Real.digits (x : ℝ) 2 n) = true := by
      -- Proof comment: the digit/right-half characterization applies to the chart representative
      -- of `z`, and `hx` identifies that representative with `z` in the circle.
      exact (modOneDoublingDigit_eq_rightHalf_iff x n).2 (by simpa [hx] using hmem)
    simp [modOneDoublingBinaryCode, x, hmem, hdigit]
  · have hdigit : finTwoEquiv (Real.digits (x : ℝ) 2 n) = false := by
      -- Proof comment: if the digit were `true`, the right-half characterization would contradict
      -- the current branch assumption.
      cases hbool : finTwoEquiv (Real.digits (x : ℝ) 2 n) with
      | false =>
          simpa using hbool
      | true =>
          exfalso
          exact hmem (by
            simpa [hx] using
              (modOneDoublingDigit_eq_rightHalf_iff x n).1 (by simpa using hbool))
    simp [modOneDoublingBinaryCode, x, hmem, hdigit]

/-- Helper for Exercise 20.6.1: decoding the binary orbit code by `Real.fromBinary` recovers the
original circle point. -/
private theorem modOneDoublingBinaryCode_decode (z : UnitAddCircle) :
    (((Real.fromBinary (modOneDoublingBinaryCode z) : unitInterval) : ℝ) : UnitAddCircle) = z := by
  -- Proof comment: rewrite the orbit code as the canonical chart digits, decode those digits in
  -- `[0,1)`, and then return to the circle through the quotient map.
  rw [modOneDoublingBinaryCode_eq_chartDigits]
  let x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1) := ⟨(AddCircle.equivIco (1 : ℝ) 0 z : ℝ), by
    simpa using (AddCircle.equivIco (1 : ℝ) 0 z).2⟩
  have hdecode : (((Real.fromBinary (fun n ↦ finTwoEquiv (Real.digits (x : ℝ) 2 n)) :
      unitInterval) : ℝ)) = (x : ℝ) :=
    fromBinary_digits_eq_self x
  have hcast :=
    congrArg (fun t : ℝ ↦ (t : UnitAddCircle)) hdecode
  have hchart : (((x : ℝ) : UnitAddCircle)) = z := by
    -- Proof comment: the chart point represents exactly the original circle element.
    exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply z
  exact hcast.trans hchart

/-- Helper for Exercise 20.6.1: the right-half atom is nonempty, so it survives the `ofErase`
construction of the partition. -/
private theorem modOneDoublingRightHalf_nonempty :
    (modOneDoublingRightHalf : Set UnitAddCircle).Nonempty := by
  let x : Set.Ico (0 : ℝ) 1 := ⟨3 / 4, by constructor <;> norm_num⟩
  refine ⟨((x : ℝ) : UnitAddCircle), ?_⟩
  -- Proof comment: the chart coordinate of `3 / 4` lies in the right-half interval.
  rw [modOneDoublingRightHalf, Set.mem_preimage, AddCircle.coe_equivIco_mk_apply]
  rw [div_one, Int.fract_eq_self.mpr x.2, mul_one]
  simpa [x] using (show ((x : ℝ) : ℝ) ∈ Set.Ico (1 / 2 : ℝ) 1 by constructor <;> norm_num)

/-- Helper for Exercise 20.6.1: the right-half measurable atom is not bottom. -/
private theorem modOneDoublingRightHalfSet_ne_bot :
    modOneDoublingRightHalfSet ≠ (⊥ : Subtype (MeasurableSet : Set UnitAddCircle → Prop)) := by
  intro h
  rcases modOneDoublingRightHalf_nonempty with ⟨z, hz⟩
  have hset : modOneDoublingRightHalf = (∅ : Set UnitAddCircle) := by
    simpa [modOneDoublingRightHalfSet] using congrArg Subtype.val h
  simpa [hset] using hz

/-- Helper for Exercise 20.6.1: the right-half atom appears among the parts of the canonical
two-piece partition. -/
private theorem modOneDoublingRightHalf_mem_parts :
    modOneDoublingRightHalfSet ∈ modOneDoublingHalfPartition.parts := by
  -- Proof comment: `modOneDoublingHalfPartition` is built from the two atoms by `Finpartition.ofErase`,
  -- and the previous lemma shows the right-half atom is not erased as `⊥`.
  simp [modOneDoublingHalfPartition, modOneDoublingRightHalfSet_ne_bot]

/-- Helper for Exercise 20.6.1: the left half of the circle is nonempty, so it also survives the
`ofErase` construction of the partition. -/
private theorem modOneDoublingLeftHalf_nonempty :
    (modOneDoublingRightHalfᶜ : Set UnitAddCircle).Nonempty := by
  let x : Set.Ico (0 : ℝ) 1 := ⟨1 / 4, by constructor <;> norm_num⟩
  refine ⟨((x : ℝ) : UnitAddCircle), ?_⟩
  -- Proof comment: the chart coordinate of `1 / 4` stays in the left half, so it avoids the
  -- right-half atom.
  rw [Set.mem_compl_iff, modOneDoublingRightHalf, Set.mem_preimage, AddCircle.coe_equivIco_mk_apply]
  rw [div_one, Int.fract_eq_self.mpr x.2, mul_one]
  simpa [x] using (show ((x : ℝ) : ℝ) ∉ Set.Ico (1 / 2 : ℝ) 1 by
    intro hx
    linarith [hx.1, hx.2])

/-- Helper for Exercise 20.6.1: the left-half measurable atom is not bottom. -/
private theorem modOneDoublingLeftHalfSet_ne_bot :
    modOneDoublingLeftHalfSet ≠ (⊥ : Subtype (MeasurableSet : Set UnitAddCircle → Prop)) := by
  intro h
  rcases modOneDoublingLeftHalf_nonempty with ⟨z, hz⟩
  have hset : modOneDoublingRightHalfᶜ = (∅ : Set UnitAddCircle) := by
    simpa [modOneDoublingLeftHalfSet] using congrArg Subtype.val h
  simpa [hset] using hz

/-- Helper for Exercise 20.6.1: the left and right half atoms are distinct. -/
private theorem modOneDoublingLeftHalfSet_ne_rightHalfSet :
    modOneDoublingLeftHalfSet ≠ modOneDoublingRightHalfSet := by
  -- Proof comment: a nonempty set cannot agree with its complement.
  intro hEq
  have hcompl : modOneDoublingRightHalfᶜ = modOneDoublingRightHalf := by
    simpa [modOneDoublingLeftHalfSet, modOneDoublingRightHalfSet] using congrArg Subtype.val hEq
  rcases modOneDoublingRightHalf_nonempty with ⟨z, hz⟩
  have hzCompl : z ∈ modOneDoublingRightHalfᶜ := by simpa [hcompl] using hz
  exact hzCompl hz

/-- Helper for Exercise 20.6.1: the left-half atom also appears among the parts of the canonical
two-piece partition. -/
private theorem modOneDoublingLeftHalf_mem_parts :
    modOneDoublingLeftHalfSet ∈ modOneDoublingHalfPartition.parts := by
  -- Proof comment: the complementary atom is kept by the same `Finpartition.ofErase` construction
  -- once we know it is not `⊥`.
  simp [modOneDoublingHalfPartition, modOneDoublingLeftHalfSet_ne_bot]

/-- Helper for Exercise 20.6.1: every atom of the half partition is either the right-half atom or
the left-half atom. -/
private theorem eq_right_or_left_of_mem_modOneDoublingHalfPartition_parts
    {A : Subtype (MeasurableSet : Set UnitAddCircle → Prop)}
    (hA : A ∈ modOneDoublingHalfPartition.parts) :
    A = modOneDoublingRightHalfSet ∨ A = modOneDoublingLeftHalfSet := by
  -- Proof comment: `modOneDoublingHalfPartition` is exactly the two-point `ofErase` partition, so
  -- membership in its parts simplifies to the two surviving atoms.
  have hA' : A ≠ (⊥ : Subtype (MeasurableSet : Set UnitAddCircle → Prop)) ∧
      (A = modOneDoublingRightHalfSet ∨ A = modOneDoublingLeftHalfSet) := by
    simpa [modOneDoublingHalfPartition, modOneDoublingRightHalfSet_ne_bot,
      modOneDoublingLeftHalfSet_ne_bot] using hA
  exact hA'.2

/-- Helper for Exercise 20.6.1: label the two atoms of the half partition by `Bool`, with `true`
for the right-half atom and `false` for the left-half atom. -/
private noncomputable def halfPartitionAtomToBool
    (A : modOneDoublingHalfPartition.parts) : Bool :=
  if (A : Subtype (MeasurableSet : Set UnitAddCircle → Prop)) = modOneDoublingRightHalfSet
    then true
    else false

/-- Helper for Exercise 20.6.1: the Boolean label of the right-half atom is `true`. -/
private theorem halfPartitionAtomToBool_right :
    halfPartitionAtomToBool ⟨modOneDoublingRightHalfSet, modOneDoublingRightHalf_mem_parts⟩ = true := by
  -- Proof comment: the defining `if` takes the right-half branch on the right-half atom itself.
  simp [halfPartitionAtomToBool]

/-- Helper for Exercise 20.6.1: the Boolean label of the left-half atom is `false`. -/
private theorem halfPartitionAtomToBool_left :
    halfPartitionAtomToBool ⟨modOneDoublingLeftHalfSet, modOneDoublingLeftHalf_mem_parts⟩ = false := by
  -- Proof comment: the left-half atom is distinct from the right-half atom because the right half
  -- is nonempty and proper.
  simp [halfPartitionAtomToBool, modOneDoublingLeftHalfSet_ne_rightHalfSet]

/-- Helper for Exercise 20.6.1: the Boolean atom label is injective on the two-part partition. -/
private theorem halfPartitionAtomToBool_injective :
    Function.Injective halfPartitionAtomToBool := by
  intro A B hAB
  rcases eq_right_or_left_of_mem_modOneDoublingHalfPartition_parts A.2 with hA | hA
  · rcases eq_right_or_left_of_mem_modOneDoublingHalfPartition_parts B.2 with hB | hB
    · exact Subtype.ext (hA.trans hB.symm)
    · have : true = false := by
        simpa [hA, hB, halfPartitionAtomToBool, modOneDoublingLeftHalfSet_ne_rightHalfSet] using hAB
      cases this
  · rcases eq_right_or_left_of_mem_modOneDoublingHalfPartition_parts B.2 with hB | hB
    · have : false = true := by
        simpa [hA, hB, halfPartitionAtomToBool, modOneDoublingLeftHalfSet_ne_rightHalfSet] using hAB
      cases this
    · exact Subtype.ext (hA.trans hB.symm)

/-- Helper for Exercise 20.6.1: relabel a block word over half-partition atoms coordinatewise by
the corresponding Boolean word. -/
private def halfPartitionWordLabel (n : ℕ+) :
    (Fin n → modOneDoublingHalfPartition.parts) → (Fin n → Bool) :=
  fun w i ↦ halfPartitionAtomToBool (w i)

/-- Helper for Exercise 20.6.1: coordinatewise Boolean relabeling of half-partition words is
injective. -/
private theorem halfPartitionWordLabel_injective (n : ℕ+) :
    Function.Injective (halfPartitionWordLabel n) := by
  intro u v huv
  funext i
  exact halfPartitionAtomToBool_injective (congrFun huv i)

/-- Helper for Exercise 20.6.1: reinterpret the `[0,1)` chart as a point of the closed unit
interval. -/
private noncomputable def modOneDoublingChartToUnitInterval (z : UnitAddCircle) : unitInterval :=
  ⟨(AddCircle.equivIco (1 : ℝ) 0 z : ℝ),
    ⟨(AddCircle.equivIco (1 : ℝ) 0 z).2.1,
      le_of_lt (by simpa using (AddCircle.equivIco (1 : ℝ) 0 z).2.2)⟩⟩

/-- Helper for Exercise 20.6.1: the standard `(0,1]` chart on `UnitAddCircle` preserves the
ambient volume measure. -/
private theorem measurePreserving_iocToUnitInterval :
    MeasurePreserving (AddCircle.equivIoc (1 : ℝ) 0) volume
      (Measure.comap Subtype.val volume) := by
  simpa using (AddCircle.measurePreserving_equivIoc (T := (1 : ℝ)) (a := (0 : ℝ)))

/-- Helper for Exercise 20.6.1: the Haar/Lebesgue measure on `UnitAddCircle` has no atom at `0`.
-/
private theorem volume_singleton_zero_unitAddCircle :
    (volume : Measure UnitAddCircle) ({(0 : UnitAddCircle)} : Set UnitAddCircle) = 0 := by
  let y : Set.Ioc (0 : ℝ) ((0 : ℝ) + 1) := AddCircle.equivIoc (1 : ℝ) 0 (0 : UnitAddCircle)
  have hpre :
      (AddCircle.equivIoc (1 : ℝ) 0) ⁻¹' ({y} : Set (Set.Ioc (0 : ℝ) ((0 : ℝ) + 1))) =
        ({(0 : UnitAddCircle)} : Set UnitAddCircle) := by
    ext z
    simp [y]
  calc
    (volume : Measure UnitAddCircle) ({(0 : UnitAddCircle)} : Set UnitAddCircle) =
        (volume : Measure UnitAddCircle)
          ((AddCircle.equivIoc (1 : ℝ) 0) ⁻¹' ({y} : Set (Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)))) := by
      simpa [hpre]
    _ = (Measure.map (AddCircle.equivIoc (1 : ℝ) 0) (volume : Measure UnitAddCircle))
          ({y} : Set (Set.Ioc (0 : ℝ) ((0 : ℝ) + 1))) := by
      symm
      exact Measure.map_apply (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable
        (measurableSet_singleton y)
    _ = (Measure.comap Subtype.val (volume : Measure ℝ))
          ({y} : Set (Set.Ioc (0 : ℝ) ((0 : ℝ) + 1))) := by
      rw [measurePreserving_iocToUnitInterval.map_eq]
    _ = (volume : Measure ℝ) (Subtype.val '' ({y} : Set (Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)))) := by
      rw [Measure.comap_apply _ Subtype.val_injective (fun _ ↦ measurableSet_Ioc.subtype_image) _
        (measurableSet_singleton y)]
    _ = (volume : Measure ℝ) ({(y : ℝ)} : Set ℝ) := by
      simp [y]
    _ = 0 := measure_singleton (y : ℝ)

/-- Helper for Exercise 20.6.1: the `unitInterval`-valued chart is measurable. -/
private theorem measurable_modOneDoublingChartToUnitInterval :
    Measurable modOneDoublingChartToUnitInterval := by
  let g : UnitAddCircle → unitInterval := fun z ↦
    ⟨(AddCircle.equivIco (1 : ℝ) 0 z : ℝ),
      ⟨(AddCircle.equivIco (1 : ℝ) 0 z).2.1,
        le_of_lt (by simpa using (AddCircle.equivIco (1 : ℝ) 0 z).2.2)⟩⟩
  change Measurable g
  have hbase : Measurable fun z : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 z : ℝ) := by
    exact measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable
  -- Proof comment: package the measurable real-valued chart into `unitInterval` using the
  -- defining bounds of `equivIco`.
  exact hbase.subtype_mk

/-- Helper for Exercise 20.6.1: the circle chart to `unitInterval` preserves volume. -/
private theorem measurePreserving_modOneDoublingChartToUnitInterval :
    MeasurePreserving modOneDoublingChartToUnitInterval volume volume := by
  refine ⟨measurable_modOneDoublingChartToUnitInterval, ?_⟩
  have hchart_eq :
      (fun z : UnitAddCircle ↦ (AddCircle.equivIco (1 : ℝ) 0 z : ℝ)) =ᵐ[volume]
        fun z : UnitAddCircle ↦ (AddCircle.equivIoc (1 : ℝ) 0 z : ℝ) := by
    have hne_zero : ∀ᵐ z ∂(volume : Measure UnitAddCircle), z ≠ (0 : UnitAddCircle) := by
      rw [ae_iff]
      simpa using volume_singleton_zero_unitAddCircle
    filter_upwards [hne_zero] with z hz
    let x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1) := AddCircle.equivIco (1 : ℝ) 0 z
    have hx_ne : (x : ℝ) ≠ 0 := by
      intro hx_zero
      apply hz
      have hx_cast : ((x : ℝ) : UnitAddCircle) = z := by
        exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply z
      simpa [x, hx_zero] using hx_cast.symm
    have hx_ioc : (x : ℝ) ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1) := by
      constructor
      · exact lt_of_le_of_ne x.2.1 (Ne.symm hx_ne)
      · exact le_of_lt (by simpa [zero_add] using x.2.2)
    have hioc :
        (AddCircle.equivIoc (1 : ℝ) 0 z : ℝ) = (x : ℝ) := by
      have hz_eq : z = ((x : ℝ) : UnitAddCircle) := by
        exact ((AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply z).symm
      rw [hz_eq]
      simpa [x] using congrArg Subtype.val
        (AddCircle.equivIoc_coe_eq (p := (1 : ℝ)) (a := (0 : ℝ)) hx_ioc)
    simpa [x] using hioc.symm
  -- Proof comment: compare both `unitInterval` measures after pushing them to `ℝ` along the
  -- measurable embedding `Subtype.val`; on `ℝ` this becomes the standard `Ico` chart together with
  -- the null-singleton identification `Ico (0,1) =ᵐ Icc (0,1)`.
  apply (MeasurableEmbedding.map_injective unitInterval.measurableEmbedding_coe)
  calc
    Measure.map ((↑) : unitInterval → ℝ) (Measure.map modOneDoublingChartToUnitInterval volume) =
        Measure.map (fun z : UnitAddCircle ↦
          ((modOneDoublingChartToUnitInterval z : unitInterval) : ℝ)) volume := by
            simpa [Function.comp] using
              (Measure.map_map measurable_subtype_coe
                measurable_modOneDoublingChartToUnitInterval
                (μ := volume))
    _ = Measure.map (fun z : UnitAddCircle ↦
          (AddCircle.equivIco (1 : ℝ) 0 z : ℝ)) volume := by
            rfl
    _ = Measure.map (fun z : UnitAddCircle ↦
          (AddCircle.equivIoc (1 : ℝ) 0 z : ℝ)) volume := by
            exact Measure.map_congr hchart_eq
    _ = Measure.map ((↑) : Set.Ioc (0 : ℝ) ((0 : ℝ) + 1) → ℝ)
          (Measure.map (AddCircle.equivIoc (1 : ℝ) 0) volume) := by
            symm
            simpa [Function.comp] using
              (Measure.map_map measurable_subtype_coe
                (AddCircle.measurableEquivIoc (1 : ℝ) 0).measurable
                (μ := volume))
    _ = Measure.map ((↑) : Set.Ioc (0 : ℝ) ((0 : ℝ) + 1) → ℝ)
          (Measure.comap Subtype.val volume) := by
            rw [measurePreserving_iocToUnitInterval.map_eq]
    _ = (volume : Measure ℝ).restrict (Set.Ico (0 : ℝ) 1) := by
            rw [map_comap_subtype_coe measurableSet_Ioc]
            simpa [zero_add] using
              (Measure.restrict_congr_set
                (μ := (volume : Measure ℝ))
                (Ico_ae_eq_Ioc.symm : Set.Ioc (0 : ℝ) 1 =ᵐ[(volume : Measure ℝ)] Set.Ico (0 : ℝ) 1))
    _ = (volume : Measure ℝ).restrict unitInterval := by
            simpa [unitInterval] using
              (Measure.restrict_congr_set
                (μ := (volume : Measure ℝ))
                (Ico_ae_eq_Icc : Set.Ico (0 : ℝ) 1 =ᵐ[(volume : Measure ℝ)] Set.Icc (0 : ℝ) 1))
    _ = Measure.map ((↑) : unitInterval → ℝ) (volume : Measure unitInterval) := by
            symm
            exact unitInterval.measurePreserving_coe.map_eq

/-- Helper for Exercise 20.6.1: the canonical binary digit map on `[0,1]` is measurable. -/
private theorem measurable_canonicalBinaryDigitsLocal :
    Measurable (canonicalBinaryDigits : unitInterval → BernoulliSequence) := by
  have hcoord : ∀ n : ℕ, Measurable (fun x : unitInterval ↦ canonicalBinaryDigits x n) := by
    intro n
    have hs : MeasurableSet {x : unitInterval | (x : ℝ) = 1} := by
      exact (measurable_subtype_coe : Measurable (fun x : unitInterval ↦ (x : ℝ)))
        (measurableSet_singleton (1 : ℝ))
    have hfloor : Measurable (fun x : unitInterval ↦ ⌊(x : ℝ) * 2 ^ (n + 1)⌋₊) := by
      exact (measurable_subtype_coe.mul measurable_const).nat_floor
    have hdigitsFin : Measurable (fun x : unitInterval ↦ Real.digits (x : ℝ) 2 n) := by
      simpa [Real.digits] using (Measurable.of_discrete (f := Fin.ofNat 2)).comp hfloor
    have hdigitsBool :
        Measurable (fun x : unitInterval ↦ finTwoEquiv (Real.digits (x : ℝ) 2 n)) := by
      exact (Measurable.of_discrete (f := finTwoEquiv)).comp hdigitsFin
    have hrewrite :
        (fun x : unitInterval ↦ canonicalBinaryDigits x n) =
          fun x : unitInterval ↦
            if (x : ℝ) = 1 then true else finTwoEquiv (Real.digits (x : ℝ) 2 n) := by
      funext x
      by_cases hx : (x : ℝ) = 1 <;> simp [canonicalBinaryDigits, hx]
    rw [hrewrite]
    exact Measurable.ite hs measurable_const hdigitsBool
  -- Proof comment: sequence measurability reduces to measurability of each coordinate map.
  exact measurable_pi_lambda _ hcoord

/-- Helper for Exercise 20.6.1: the orbit code is measurable as a Bernoulli-sequence-valued map. -/
private theorem measurable_modOneDoublingBinaryCode :
    Measurable modOneDoublingBinaryCode := by
  refine measurable_pi_lambda _ ?_
  intro n
  let s : Set UnitAddCircle := (modOneDoubling^[n]) ⁻¹' modOneDoublingRightHalf
  have hs : MeasurableSet s := by
    exact measurableSet_modOneDoublingRightHalf.preimage
      (Measurable.iterate modOneDoubling_measurePreserving.measurable n)
  -- Proof comment: the `n`th digit is the indicator of the `n`th right-half iterate event.
  simpa [modOneDoublingBinaryCode, s] using
    (measurable_const.piecewise hs measurable_const :
      Measurable (s.piecewise (fun _ : UnitAddCircle ↦ true) fun _ ↦ false))

/-- Helper for Exercise 20.6.1: because the `[0,1)` chart never hits the endpoint `1`, the orbit
code agrees with the canonical binary digits of the chart point in `unitInterval`. -/
private theorem modOneDoublingBinaryCode_eq_canonicalBinaryDigits_chart
    (z : UnitAddCircle) :
    modOneDoublingBinaryCode z =
      canonicalBinaryDigits (modOneDoublingChartToUnitInterval z) := by
  -- Proof comment: the chart value lies in `[0,1)`, so the canonical digit map uses the ordinary
  -- `Real.digits` branch rather than the exceptional endpoint branch at `1`.
  rw [modOneDoublingBinaryCode_eq_chartDigits]
  have hne :
      ((AddCircle.equivIco (1 : ℝ) 0 z : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ) ≠ 1 := by
    exact ne_of_lt (by simpa using (AddCircle.equivIco (1 : ℝ) 0 z).2.2)
  funext n
  simpa [canonicalBinaryDigits, modOneDoublingChartToUnitInterval, hne]

/-- Helper for Exercise 20.6.1: the full doubling-itinerary law is the fair Bernoulli measure. -/
private theorem modOneDoublingBinaryCode_map_eq_fairBernoulliMeasure :
    Measure.map modOneDoublingBinaryCode volume = fairBernoulliMeasure := by
  -- Proof comment: rewrite the orbit code as the canonical binary digits of the measurable chart
  -- point, then push the ambient measure through the chart-to-`unitInterval` transport.
  calc
    Measure.map modOneDoublingBinaryCode volume =
        Measure.map (fun z : UnitAddCircle ↦
          canonicalBinaryDigits (modOneDoublingChartToUnitInterval z)) volume := by
            refine Measure.map_congr <| Filter.Eventually.of_forall ?_
            intro z
            exact modOneDoublingBinaryCode_eq_canonicalBinaryDigits_chart z
    _ = Measure.map canonicalBinaryDigits
          (Measure.map modOneDoublingChartToUnitInterval volume) := by
            symm
            simpa [Function.comp] using
              (Measure.map_map measurable_canonicalBinaryDigitsLocal
                measurable_modOneDoublingChartToUnitInterval
                (μ := volume))
    _ = Measure.map canonicalBinaryDigits (volume : Measure unitInterval) := by
            rw [measurePreserving_modOneDoublingChartToUnitInterval.map_eq]
    _ = fairBernoulliMeasure := by
            rfl

/-- Helper for Exercise 20.6.1: the finite-prefix orbit code is measurable because each
coordinate is a measurable coordinate of the full Bernoulli code. -/
private theorem measurable_modOneDoublingPrefixCodeAux (n : ℕ+) :
    Measurable (fun z : UnitAddCircle ↦ fun i : Fin n ↦ modOneDoublingBinaryCode z i) := by
  -- Proof comment: each finite coordinate is obtained by composing the measurable full code with
  -- the measurable coordinate evaluation map on `BernoulliSequence`.
  refine measurable_pi_lambda _ fun i ↦ ?_
  have hcoord :
      Measurable (fun ω : BernoulliSequence ↦ ω (i : ℕ)) := by
    simpa using (measurable_pi_apply (i : ℕ) :
      Measurable (fun ω : BernoulliSequence ↦ ω (i : ℕ)))
  exact hcoord.comp measurable_modOneDoublingBinaryCode

/-- Helper for Exercise 20.6.1: the first `n` digits of the orbit code, viewed as a finite binary
word. -/
private noncomputable abbrev modOneDoublingPrefixCode (n : ℕ+) (z : UnitAddCircle) : Fin n → Bool :=
  fun i ↦ modOneDoublingBinaryCode z i

/-- Helper for Exercise 20.6.1: package the finite prefix code as a simple function so its law can
be compared directly with partition entropies. -/
private noncomputable def modOneDoublingPrefixSimpleFunc (n : ℕ+) :
    SimpleFunc UnitAddCircle (Fin n → Bool) where
  toFun := modOneDoublingPrefixCode n
  measurableSet_fiber' := fun s ↦ measurable_modOneDoublingPrefixCodeAux n (measurableSet_singleton s)
  finite_range' := Set.toFinite _

/-- Helper for Exercise 20.6.1: the finite-prefix orbit code is measurable. -/
private theorem measurable_modOneDoublingPrefixCode (n : ℕ+) :
    Measurable (modOneDoublingPrefixCode n) := by
  -- Proof comment: each finite coordinate is a measurable coordinate of the full Bernoulli code.
  simpa using measurable_modOneDoublingPrefixCodeAux n

/-- Helper for Exercise 20.6.1: truncating a Bernoulli sequence to its first `n` coordinates is a
measurable finite-valued map. -/
private theorem measurable_bernoulliPrefixProjection (n : ℕ+) :
    Measurable (fun ω : BernoulliSequence ↦ fun i : Fin n ↦ ω i) := by
  -- Proof comment: the finite restriction map is measurable coordinatewise.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa using (measurable_pi_apply (i : ℕ) :
    Measurable (fun ω : BernoulliSequence ↦ ω (i : ℕ)))

/-- Helper for Exercise 20.6.1: one chart step for the doubling map, still viewed in `[0,1)`. -/
private noncomputable def modOneDoublingChartStep (x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) :
    Set.Ico (0 : ℝ) ((0 : ℝ) + 1) :=
  AddCircle.equivIco (1 : ℝ) 0 (modOneDoubling ((x : ℝ) : UnitAddCircle))

/-- Helper for Exercise 20.6.1: applying the `[0,1)` chart after one doubling step returns to the
same circle point. -/
private theorem modOneDoublingChartStep_coe
    (x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) :
    (((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ) : UnitAddCircle) =
      modOneDoubling ((x : ℝ) : UnitAddCircle) := by
  -- Proof comment: `equivIco` is the inverse of the quotient map on `UnitAddCircle`.
  change (((AddCircle.equivIco (1 : ℝ) 0
      (modOneDoubling ((x : ℝ) : UnitAddCircle)) : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ) :
        UnitAddCircle) = modOneDoubling ((x : ℝ) : UnitAddCircle)
  exact (AddCircle.equivIco (1 : ℝ) 0).symm_apply_apply
    (modOneDoubling ((x : ℝ) : UnitAddCircle))

/-- Helper for Exercise 20.6.1: the first binary digit of a chart point records membership in the
right half of `[0,1)`. -/
private theorem chartFirstDigit_eq_true_iff_rightHalf
    (x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) :
    finTwoEquiv (Real.digits (x : ℝ) 2 0) = true ↔ (x : ℝ) ∈ Set.Ico (1 / 2 : ℝ) 1 := by
  -- Proof comment: specialize the already-proved digit/right-half equivalence at time `0` and
  -- simplify the chart of the represented circle point.
  simpa [modOneDoublingRightHalf, Function.iterate_zero_apply, Set.mem_preimage,
    AddCircle.coe_equivIco_mk_apply, Int.fract_eq_self.2 (by simpa [zero_add] using x.2)] using
    (modOneDoublingDigit_eq_rightHalf_iff x 0)

/-- Helper for Exercise 20.6.1: on the left half of `[0,1)`, one doubling step doubles the chart
coordinate. -/
private theorem modOneDoublingChartStep_eq_two_mul_of_lt_half
    (x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) (hx : (x : ℝ) < 1 / 2) :
    ((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ) = 2 * (x : ℝ) := by
  have hmem : 2 * (x : ℝ) ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · nlinarith [x.2.1]
    · nlinarith [hx]
  -- Proof comment: on the left half, the fractional part formula for the charted doubling step
  -- stays inside `[0,1)`, so `Int.fract` is the identity.
  change (AddCircle.equivIco (1 : ℝ) 0
      ((modOneDoubling^[1]) ((x : ℝ) : UnitAddCircle)) : ℝ) = 2 * (x : ℝ)
  rw [equivIco_modOneDoubling_iterate_eq_fract_pow_mul 1 x]
  simpa using (Int.fract_eq_self.2 hmem)

/-- Helper for Exercise 20.6.1: on the right half of `[0,1)`, one doubling step subtracts `1`
after doubling the chart coordinate. -/
private theorem modOneDoublingChartStep_eq_two_mul_sub_one_of_half_le
    (x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) (hx : 1 / 2 ≤ (x : ℝ)) :
    ((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ) = 2 * (x : ℝ) - 1 := by
  have hmem : 2 * (x : ℝ) - 1 ∈ Set.Ico (0 : ℝ) 1 := by
    constructor
    · nlinarith [hx]
    · nlinarith [x.2.2]
  -- Proof comment: on the right half, the doubled chart value lies in `[1,2)`, so subtracting the
  -- integer part `1` gives the chart of the mod-one image.
  change (AddCircle.equivIco (1 : ℝ) 0
      ((modOneDoubling^[1]) ((x : ℝ) : UnitAddCircle)) : ℝ) = 2 * (x : ℝ) - 1
  rw [equivIco_modOneDoubling_iterate_eq_fract_pow_mul 1 x]
  calc
    Int.fract (2 * (x : ℝ)) = Int.fract (2 * (x : ℝ) - 1) := by
      simpa using (Int.fract_sub_natCast (2 * (x : ℝ)) 1).symm
    _ = 2 * (x : ℝ) - 1 := by
      simpa using (Int.fract_eq_self.2 hmem)

/-- Helper for Exercise 20.6.1: after one doubling step, the later chart digits shift left by one
place. -/
private theorem modOneDoublingChartStep_digit_shift
    (x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) (m : ℕ) :
    finTwoEquiv (Real.digits
        ((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ) 2 m) =
      finTwoEquiv (Real.digits (x : ℝ) 2 (m + 1)) := by
  -- Proof comment: both sides encode the same right-half event, namely the `m`th iterate of the
  -- orbit started one step later.
  apply Bool.eq_iff_iff.mpr
  calc
    finTwoEquiv (Real.digits
        ((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ) 2 m) = true ↔
        ((modOneDoubling^[m])
            ((((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ) :
              UnitAddCircle))) ∈
          modOneDoublingRightHalf := by
            exact modOneDoublingDigit_eq_rightHalf_iff (modOneDoublingChartStep x) m
    _ ↔ ((modOneDoubling^[m + 1]) ((x : ℝ) : UnitAddCircle)) ∈ modOneDoublingRightHalf := by
      rw [modOneDoublingChartStep_coe]
      simpa using
        congrArg (fun z : UnitAddCircle ↦ z ∈ modOneDoublingRightHalf)
          (Function.Commute.iterate_right (Function.Commute.self modOneDoubling) m
            ((x : ℝ) : UnitAddCircle))
    _ ↔ finTwoEquiv (Real.digits (x : ℝ) 2 (m + 1)) = true := by
      symm
      exact modOneDoublingDigit_eq_rightHalf_iff x (m + 1)

/-- Helper for Exercise 20.6.1: the left endpoint of the dyadic interval determined by a Boolean
prefix. -/
private def binaryPrefixLeftEndpoint : ∀ n : ℕ, (Fin n → Bool) → ℝ
  | 0, _ => 0
  | n + 1, w =>
      (if w 0 then (1 / 2 : ℝ) else 0) +
        binaryPrefixLeftEndpoint n (fun i : Fin n ↦ w i.succ) / 2

/-- Helper for Exercise 20.6.1: every dyadic prefix interval stays inside `[0, 1]`. -/
private theorem binaryPrefixLeftEndpoint_bounds :
    ∀ n : ℕ, ∀ w : Fin n → Bool,
      0 ≤ binaryPrefixLeftEndpoint n w ∧
        binaryPrefixLeftEndpoint n w + (1 / 2 : ℝ) ^ n ≤ 1
  | 0, _ => by
      -- Proof comment: the empty word corresponds to the whole unit interval.
      constructor
      · simp [binaryPrefixLeftEndpoint]
      · simp [binaryPrefixLeftEndpoint]
  | n + 1, w => by
      rcases binaryPrefixLeftEndpoint_bounds n (fun i : Fin n ↦ w i.succ) with ⟨ha, hb⟩
      by_cases h0 : w 0
      · -- Proof comment: the `true` branch prepends the right half `[1/2, 1)`.
        constructor
        · rw [binaryPrefixLeftEndpoint, if_pos h0]
          positivity
        · rw [binaryPrefixLeftEndpoint, if_pos h0, pow_succ]
          nlinarith
      · -- Proof comment: the `false` branch prepends the left half `[0, 1/2)`.
        constructor
        · rw [binaryPrefixLeftEndpoint, if_neg h0]
          positivity
        · rw [binaryPrefixLeftEndpoint, if_neg h0, pow_succ]
          nlinarith

/-- Helper for Exercise 20.6.1: the dyadic interval cut out by a Boolean prefix has measure
`(1 / 2)^n`. -/
private theorem volume_binaryPrefixInterval (n : ℕ) (w : Fin n → Bool) :
    volume {x : unitInterval |
      binaryPrefixLeftEndpoint n w ≤ (x : ℝ) ∧
        (x : ℝ) < binaryPrefixLeftEndpoint n w + (1 / 2 : ℝ) ^ n} =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  rcases binaryPrefixLeftEndpoint_bounds n w with ⟨ha, hb⟩
  rw [unitInterval.volume_apply]
  have himage :
      ((↑) : unitInterval → ℝ) '' {x : unitInterval |
        binaryPrefixLeftEndpoint n w ≤ (x : ℝ) ∧
          (x : ℝ) < binaryPrefixLeftEndpoint n w + (1 / 2 : ℝ) ^ n} =
        Set.Ico (binaryPrefixLeftEndpoint n w)
          (binaryPrefixLeftEndpoint n w + (1 / 2 : ℝ) ^ n) := by
    -- Proof comment: once the endpoint bounds are known, coercing from `unitInterval` to `ℝ`
    -- identifies the subtype interval with the usual real half-open interval.
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Ico]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨⟨y, ?_⟩, hy, rfl⟩
      constructor
      · linarith
      · linarith
  rw [himage, Real.volume_Ico]
  congr 1
  ring

/-- Helper for Exercise 20.6.1: for a point of `[0,1)`, the first `n` binary digits equal `w`
exactly on the dyadic interval cut out by `w`. -/
private theorem chartPrefix_eq_iff_mem_binaryPrefixInterval :
    ∀ n : ℕ, ∀ w : Fin n → Bool, ∀ x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1),
      (∀ i : Fin n, finTwoEquiv (Real.digits (x : ℝ) 2 i) = w i) ↔
        binaryPrefixLeftEndpoint n w ≤ (x : ℝ) ∧
          (x : ℝ) < binaryPrefixLeftEndpoint n w + (1 / 2 : ℝ) ^ n
  | 0, _, x => by
      simpa [binaryPrefixLeftEndpoint, zero_add] using x.2
  | n + 1, w, x => by
      let wTail : Fin n → Bool := fun i ↦ w i.succ
      rcases binaryPrefixLeftEndpoint_bounds n wTail with ⟨hTailLo, hTailHi⟩
      constructor
      · intro hx
        by_cases h0 : w 0
        · have hx0 : finTwoEquiv (Real.digits (x : ℝ) 2 0) = true := by
            simpa [h0] using hx 0
          have hxHalf : (1 / 2 : ℝ) ≤ (x : ℝ) :=
            (chartFirstDigit_eq_true_iff_rightHalf x).1 hx0 |>.1
          have hxTail :
              ∀ i : Fin n,
                finTwoEquiv
                    (Real.digits
                      ((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ) 2 i) =
                  wTail i := by
            intro i
            simpa [wTail] using (modOneDoublingChartStep_digit_shift x i).trans (hx i.succ)
          have hstep :=
            (chartPrefix_eq_iff_mem_binaryPrefixInterval n wTail (modOneDoublingChartStep x)).1 hxTail
          rw [modOneDoublingChartStep_eq_two_mul_sub_one_of_half_le x hxHalf] at hstep
          rw [binaryPrefixLeftEndpoint, if_pos h0, pow_succ]
          constructor <;> nlinarith
        · have hxHalf : (x : ℝ) < 1 / 2 := by
            have hxFalse : finTwoEquiv (Real.digits (x : ℝ) 2 0) = false := by
              simpa [h0] using hx 0
            have hxNotMem : ¬ (x : ℝ) ∈ Set.Ico (1 / 2 : ℝ) 1 := by
              exact (chartFirstDigit_eq_true_iff_rightHalf x).not.mp (by simpa using hxFalse)
            have hxlt1 : (x : ℝ) < 1 := by
              simpa [zero_add] using x.2.2
            by_contra hxGe
            exact hxNotMem ⟨le_of_not_gt hxGe, hxlt1⟩
          have hxTail :
              ∀ i : Fin n,
                finTwoEquiv
                    (Real.digits
                      ((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ) 2 i) =
                  wTail i := by
            intro i
            simpa [wTail] using (modOneDoublingChartStep_digit_shift x i).trans (hx i.succ)
          have hstep :=
            (chartPrefix_eq_iff_mem_binaryPrefixInterval n wTail (modOneDoublingChartStep x)).1 hxTail
          rw [modOneDoublingChartStep_eq_two_mul_of_lt_half x hxHalf] at hstep
          rw [binaryPrefixLeftEndpoint, if_neg h0, pow_succ]
          constructor <;> nlinarith
      · intro hx
        by_cases h0 : w 0
        · have hxHalf : (1 / 2 : ℝ) ≤ (x : ℝ) := by
            rw [binaryPrefixLeftEndpoint, if_pos h0, pow_succ] at hx
            nlinarith [hx.1, hTailLo]
          have hstep :
              binaryPrefixLeftEndpoint n wTail ≤
                  (((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ)) ∧
                (((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ)) <
                  binaryPrefixLeftEndpoint n wTail + (1 / 2 : ℝ) ^ n := by
            rw [modOneDoublingChartStep_eq_two_mul_sub_one_of_half_le x hxHalf]
            rw [binaryPrefixLeftEndpoint, if_pos h0, pow_succ] at hx
            constructor <;> nlinarith
          have hxTail :=
            (chartPrefix_eq_iff_mem_binaryPrefixInterval n wTail (modOneDoublingChartStep x)).2 hstep
          refine Fin.cases ?_ ?_
          · simpa [h0, zero_add] using
              (chartFirstDigit_eq_true_iff_rightHalf x).2 ⟨hxHalf, by simpa [zero_add] using x.2.2⟩
          · intro i
            simpa [wTail] using (modOneDoublingChartStep_digit_shift x i).symm.trans (hxTail i)
        · have hxHalf : (x : ℝ) < 1 / 2 := by
            rw [binaryPrefixLeftEndpoint, if_neg h0, pow_succ] at hx
            nlinarith [hx.2, hTailHi]
          have hstep :
              binaryPrefixLeftEndpoint n wTail ≤
                  (((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ)) ∧
                (((modOneDoublingChartStep x : Set.Ico (0 : ℝ) ((0 : ℝ) + 1)) : ℝ)) <
                  binaryPrefixLeftEndpoint n wTail + (1 / 2 : ℝ) ^ n := by
            rw [modOneDoublingChartStep_eq_two_mul_of_lt_half x hxHalf]
            rw [binaryPrefixLeftEndpoint, if_neg h0, pow_succ] at hx
            constructor <;> nlinarith
          have hxTail :=
            (chartPrefix_eq_iff_mem_binaryPrefixInterval n wTail (modOneDoublingChartStep x)).2 hstep
          refine Fin.cases ?_ ?_
          · have hxFalse : finTwoEquiv (Real.digits (x : ℝ) 2 0) = false := by
              by_cases hx0 : finTwoEquiv (Real.digits (x : ℝ) 2 0) = true
              · exfalso
                exact not_lt_of_ge ((chartFirstDigit_eq_true_iff_rightHalf x).1 hx0).1 hxHalf
              · cases hbool : finTwoEquiv (Real.digits (x : ℝ) 2 0) <;> simp_all
            simpa [h0] using hxFalse
          · intro i
            simpa [wTail] using (modOneDoublingChartStep_digit_shift x i).symm.trans (hxTail i)

/-- Helper for Exercise 20.6.1: away from the endpoint `1`, a canonical binary prefix cuts out
the corresponding dyadic interval. -/
private theorem canonicalPrefixFiber_ae_eq_binaryPrefixInterval (n : ℕ) (w : Fin n → Bool) :
    {x : unitInterval | ∀ i : Fin n, canonicalBinaryDigits x i = w i} =ᵐ[volume]
      {x : unitInterval |
        binaryPrefixLeftEndpoint n w ≤ (x : ℝ) ∧
          (x : ℝ) < binaryPrefixLeftEndpoint n w + (1 / 2 : ℝ) ^ n} := by
  have hne_one : ∀ᵐ x : unitInterval ∂volume, (x : ℝ) ≠ 1 := by
    rw [ae_iff]
    simpa using (measure_singleton (1 : unitInterval))
  filter_upwards [hne_one] with x hx1
  let xIco : Set.Ico (0 : ℝ) ((0 : ℝ) + 1) := ⟨(x : ℝ), by
    constructor
    · exact x.2.1
    · exact lt_of_le_of_ne (by simpa [zero_add] using x.2.2) (by simpa [zero_add] using hx1)⟩
  have hprefix :
      (∀ i : Fin n, canonicalBinaryDigits x i = w i) ↔
        (∀ i : Fin n, finTwoEquiv (Real.digits (xIco : ℝ) 2 i) = w i) := by
    constructor
    · intro hxPrefix i
      simpa [canonicalBinaryDigits, hx1, xIco] using hxPrefix i
    · intro hxPrefix i
      simpa [canonicalBinaryDigits, hx1, xIco] using hxPrefix i
  simpa [xIco] using
    hprefix.trans (chartPrefix_eq_iff_mem_binaryPrefixInterval n w xIco)

/-- Helper for Exercise 20.6.1: finite prefixes of the fair Bernoulli sequence are uniformly
distributed on Boolean words. -/
private theorem fairBernoulliPrefixLaw_eq_uniform (n : ℕ+) :
    Measure.map (fun ω : BernoulliSequence ↦ fun i : Fin n ↦ ω i) fairBernoulliMeasure =
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  rw [fairBernoulliMeasure]
  rw [Measure.map_map (measurable_bernoulliPrefixProjection n) measurable_canonicalBinaryDigitsLocal]
  have hprefixMeas :
      Measurable (fun x : unitInterval ↦ fun i : Fin n ↦ canonicalBinaryDigits x i) := by
    exact (measurable_bernoulliPrefixProjection n).comp measurable_canonicalBinaryDigitsLocal
  refine Measure.ext_of_singleton ?_
  intro w
  change (Measure.map
      (fun x : unitInterval ↦ fun i : Fin n ↦ canonicalBinaryDigits x i) volume)
      ({w} : Set (Fin n → Bool)) =
    (PMF.uniformOfFintype (Fin n → Bool)).toMeasure ({w} : Set (Fin n → Bool))
  rw [Measure.map_apply hprefixMeas (measurableSet_singleton w)]
  have hfiber :
      {x : unitInterval | ∀ i : Fin n, canonicalBinaryDigits x i = w i} =ᵐ[volume]
        {x : unitInterval |
          binaryPrefixLeftEndpoint n w ≤ (x : ℝ) ∧
            (x : ℝ) < binaryPrefixLeftEndpoint n w + (1 / 2 : ℝ) ^ (n : ℕ)} :=
    canonicalPrefixFiber_ae_eq_binaryPrefixInterval n w
  calc
    volume (((fun x : unitInterval ↦ fun i : Fin n ↦ canonicalBinaryDigits x i) ⁻¹'
        ({w} : Set (Fin n → Bool)))) =
        volume {x : unitInterval | ∀ i : Fin n, canonicalBinaryDigits x i = w i} := by
          congr 1
          ext x
          constructor
          · intro hx i
            exact congrFun hx i
          · intro hx
            funext i
            exact hx i
    _ = volume {x : unitInterval |
          binaryPrefixLeftEndpoint n w ≤ (x : ℝ) ∧
            (x : ℝ) < binaryPrefixLeftEndpoint n w + (1 / 2 : ℝ) ^ (n : ℕ)} := by
          exact measure_congr hfiber
    _ = ENNReal.ofReal ((1 / 2 : ℝ) ^ (n : ℕ)) := volume_binaryPrefixInterval (n : ℕ) w
    _ = (PMF.uniformOfFintype (Fin n → Bool)).toMeasure ({w} : Set (Fin n → Bool)) := by
          simp [PMF.uniformOfFintype_apply, ENNReal.inv_pow]

/-- Helper for Exercise 20.6.1: the first `n` bits of the doubling itinerary are uniformly
distributed. -/
private theorem modOneDoublingPrefixLaw_eq_uniform (n : ℕ+) :
    Measure.map (modOneDoublingPrefixCode n) volume =
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure := by
  -- Proof comment: truncate the full Bernoulli itinerary law to the first `n` coordinates and
  -- invoke the corresponding finite-prefix law of the fair Bernoulli measure.
  calc
    Measure.map (modOneDoublingPrefixCode n) volume =
        Measure.map (fun ω : BernoulliSequence ↦ fun i : Fin n ↦ ω i)
          (Measure.map modOneDoublingBinaryCode volume) := by
            symm
            simpa [Function.comp, modOneDoublingPrefixCode] using
              (Measure.map_map (measurable_bernoulliPrefixProjection n)
                measurable_modOneDoublingBinaryCode
                (μ := volume))
    _ = Measure.map (fun ω : BernoulliSequence ↦ fun i : Fin n ↦ ω i)
          fairBernoulliMeasure := by
            rw [modOneDoublingBinaryCode_map_eq_fairBernoulliMeasure]
    _ = (PMF.uniformOfFintype (Fin n → Bool)).toMeasure :=
          fairBernoulliPrefixLaw_eq_uniform n

/-- Helper for Exercise 20.6.1: the explicit Boolean prefix code is the coordinatewise relabeling
of the transparent block code of the two-half partition. -/
private theorem modOneDoublingPrefixSimpleFunc_eq_label_prefixBlockCode (n : ℕ+) :
    (modOneDoublingPrefixSimpleFunc n : UnitAddCircle → Fin n → Bool) =
      fun z ↦ halfPartitionWordLabel n
        (prefixBlockCode modOneDoubling modOneDoubling_measurePreserving.measurable
          modOneDoublingHalfPartition n z) := by
  funext z
  funext i
  let y : UnitAddCircle := (modOneDoubling^[i]) z
  by_cases hy : y ∈ modOneDoublingRightHalf
  · have hcode :
        modOneDoublingHalfPartition.toSimpleFunc y =
          ⟨modOneDoublingRightHalfSet, modOneDoublingRightHalf_mem_parts⟩ := by
      -- Proof comment: if the iterate lies in the right-half atom, the canonical partition code
      -- selects that atom.
      exact (mem_atom_iff_toSimpleFunc_eq modOneDoublingHalfPartition).1 (by
        simpa [y, modOneDoublingRightHalfSet] using hy)
    simp [modOneDoublingPrefixSimpleFunc, modOneDoublingPrefixCode, halfPartitionWordLabel,
      prefixBlockCode, modOneDoublingBinaryCode, y, hy, hcode, halfPartitionAtomToBool]
  · have hcode :
        modOneDoublingHalfPartition.toSimpleFunc y =
          ⟨modOneDoublingLeftHalfSet, modOneDoublingLeftHalf_mem_parts⟩ := by
      -- Proof comment: outside the right-half atom, the canonical two-atom partition must select
      -- the complementary left-half atom.
      exact (mem_atom_iff_toSimpleFunc_eq modOneDoublingHalfPartition).1 (by
        simpa [y, modOneDoublingLeftHalfSet] using hy)
    simp [modOneDoublingPrefixSimpleFunc, modOneDoublingPrefixCode, halfPartitionWordLabel,
      prefixBlockCode, modOneDoublingBinaryCode, y, hy, hcode, halfPartitionAtomToBool,
      modOneDoublingLeftHalfSet_ne_rightHalfSet]

/-- Helper for Exercise 20.6.1: the entropy of a uniform Boolean word of length `n` is `n * log 2`,
so the normalized value equals the entropy of the fair two-point law. -/
private theorem uniformBoolWordEntropyNormalized (n : ℕ+) :
    entropy (PMF.uniformOfFintype (Fin n → Bool)) * (((n : ℕ) : EReal)⁻¹) =
      entropy (PMF.uniformOfFintype (Fin 2)) := by
  have hwords :
      entropy (PMF.uniformOfFintype (Fin n → Bool)) =
        (Real.log (Fintype.card (Fin n → Bool)) : EReal) := by
    simpa using (entropy_uniformOfFintype_eq_log_card (E := Fin n → Bool))
  have htwo :
      entropy (PMF.uniformOfFintype (Fin 2)) =
        (Real.log (Fintype.card (Fin 2)) : EReal) := by
    simpa using (entropy_uniformOfFintype_eq_log_card (E := Fin 2))
  rw [hwords, htwo]
  norm_num [Fintype.card_fun]
  have hn_bot : (((n : ℕ) : EReal)) ≠ ⊥ := EReal.natCast_ne_bot (n : ℕ)
  have hn_top : (((n : ℕ) : EReal)) ≠ ⊤ := EReal.natCast_ne_top (n : ℕ)
  have hn_zero : (((n : ℕ) : EReal)) ≠ 0 := by
    exact_mod_cast n.ne_zero
  have hdiv : (((n : ℕ) : EReal) / ((n : ℕ) : EReal)) = 1 :=
    EReal.div_self hn_bot hn_top hn_zero
  calc
    (((n : ℕ) : EReal) * ((Real.log 2 : ℝ) : EReal)) * (((n : ℕ) : EReal)⁻¹) =
        (((n : ℕ) : EReal) / ((n : ℕ) : EReal)) * ((Real.log 2 : ℝ) : EReal) := by
      rw [EReal.div_eq_inv_mul]
      ac_rfl
    _ = ((Real.log 2 : ℝ) : EReal) := by
      rw [hdiv, one_mul]

/-- Helper for Exercise 20.6.1: the two-half partition is generating because the full right-half
itinerary reconstructs the circle point via `Real.fromBinary`. -/
private theorem modOneDoublingHalfPartition_isGenerator :
    is_generator modOneDoubling modOneDoublingHalfPartition := by
  -- Route correction: the intended proof is to work in the generated sigma algebra, prove each
  -- coordinate of `modOneDoublingBinaryCode` is measurable because `{true}` and `{false}` fibers
  -- are iterate-preimages of the two half atoms, then use `modOneDoublingBinaryCode_decode` to
  -- show the identity map is measurable back to the ambient space.
  let G : Set (Set UnitAddCircle) :=
    ⋃ n : ℕ,
      Set.range fun A : modOneDoublingHalfPartition.parts ↦
        (modOneDoubling^[n]) ⁻¹'
          ((A.1 : Subtype (MeasurableSet : Set UnitAddCircle → Prop)) : Set UnitAddCircle)
  let mAmbient : MeasurableSpace UnitAddCircle := inferInstance
  have hmGen_le : MeasurableSpace.generateFrom G ≤ mAmbient := by
    -- Proof comment: every generator is an iterate-preimage of a measurable partition atom, hence
    -- already measurable in the ambient circle σ-algebra.
    refine MeasurableSpace.generateFrom_le ?_
    intro s hs
    rcases Set.mem_iUnion.mp hs with ⟨n, hs⟩
    rcases Set.mem_range.mp hs with ⟨A, rfl⟩
    exact A.1.2.preimage (Measurable.iterate modOneDoubling_measurePreserving.measurable n)
  letI : MeasurableSpace UnitAddCircle := MeasurableSpace.generateFrom G
  have hcoord :
      ∀ n : ℕ, Measurable (fun z : UnitAddCircle ↦ modOneDoublingBinaryCode z n) := by
    intro n
    -- Proof comment: each itinerary coordinate is the indicator of one basic generator set.
    let s : Set UnitAddCircle := (modOneDoubling^[n]) ⁻¹' modOneDoublingRightHalf
    have hs_mem : s ∈ G := by
      refine Set.mem_iUnion.mpr ⟨n, ?_⟩
      refine Set.mem_range.mpr ?_
      refine ⟨⟨modOneDoublingRightHalfSet, modOneDoublingRightHalf_mem_parts⟩, ?_⟩
      ext z
      rfl
    have hs : MeasurableSet s := MeasurableSpace.measurableSet_generateFrom hs_mem
    simpa [modOneDoublingBinaryCode, s] using
      (measurable_const.piecewise hs measurable_const :
        Measurable (s.piecewise (fun _ : UnitAddCircle ↦ true) fun _ ↦ false))
  have hcode : Measurable modOneDoublingBinaryCode := by
    -- Proof comment: product measurability follows from the coordinate measurability proved
    -- above inside the generated σ-algebra.
    exact measurable_pi_lambda _ hcoord
  have hdecodeMeas :
      Measurable[MeasurableSpace.generateFrom G, mAmbient] fun z : UnitAddCircle ↦
        ((((Real.fromBinary (modOneDoublingBinaryCode z) : unitInterval) : ℝ) : UnitAddCircle)) := by
    -- Proof comment: decode the measurable itinerary inside the generated σ-algebra and then
    -- return to the circle through the measurable quotient map.
    exact (AddCircle.measurable_mk'.comp measurable_subtype_coe).comp
      (measurable_fromBinary.comp hcode)
  have hdecodeEq :
      (fun z : UnitAddCircle ↦
        ((((Real.fromBinary (modOneDoublingBinaryCode z) : unitInterval) : ℝ) : UnitAddCircle))) =
        fun z : UnitAddCircle ↦ z := by
    funext z
    simpa using modOneDoublingBinaryCode_decode z
  have hdecodeEqId :
      (fun z : UnitAddCircle ↦
        ((((Real.fromBinary (modOneDoublingBinaryCode z) : unitInterval) : ℝ) : UnitAddCircle))) =
        id := by
    simpa [id] using hdecodeEq
  have hambient_le : mAmbient ≤ MeasurableSpace.generateFrom G := by
    -- Proof comment: the decoded itinerary is literally the identity, so its measurability forces
    -- the full ambient σ-algebra to sit inside the generated one.
    have hcomap :
        MeasurableSpace.comap
            (fun z : UnitAddCircle ↦
              ((((Real.fromBinary (modOneDoublingBinaryCode z) : unitInterval) : ℝ) :
                UnitAddCircle)))
            mAmbient ≤
          MeasurableSpace.generateFrom G :=
      (hdecodeMeas.comap_le :
        MeasurableSpace.comap
            (fun z : UnitAddCircle ↦
              ((((Real.fromBinary (modOneDoublingBinaryCode z) : unitInterval) : ℝ) :
                UnitAddCircle)))
            mAmbient ≤
          MeasurableSpace.generateFrom G)
    have hidcomap : MeasurableSpace.comap id mAmbient ≤ MeasurableSpace.generateFrom G := by
      simpa [hdecodeEqId] using hcomap
    exact (MeasurableSpace.comap_id (m := mAmbient)) ▸ hidcomap
  exact le_antisymm hmGen_le hambient_le

/-- Helper for Exercise 20.6.1: every fixed partition dynamical entropy is bounded above by the
Kolmogorov--Sinai entropy. -/
private theorem dynamicalEntropy_le_kolmogorovSinai
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (τ : Ω → Ω) (hτ : Measurable τ) (part : MeasurableFinpartition Ω) :
    h(P, τ, hτ; part) ≤ h(P, τ, hτ) := by
  -- Proof comment: the Kolmogorov--Sinai entropy is the supremum over all finite measurable
  -- partitions, so the chosen partition contributes one admissible term.
  rw [kolmogorov_sinai_entropy_def]
  exact le_sSup (Set.mem_range.mpr ⟨part, rfl⟩)

-- Proof sketch: code the doubling map by binary expansions to obtain a measurable conjugacy with
-- the fair Bernoulli shift on two symbols, then apply the entropy computation for the fair binary
-- shift and evaluate the entropy of the uniform law on `Fin 2`.
/-- Helper for Exercise 20.6.1: each normalized block entropy of the two-half partition should
match the one-step entropy of the fair two-point law. -/
private theorem modOneDoublingHalfPartition_blockEntropyNormalized (n : ℕ+) :
    (modOneDoublingHalfPartition.block modOneDoubling
        modOneDoubling_measurePreserving.measurable n).partitionEntropy volume *
      (((n : ℕ) : EReal)⁻¹) =
        entropy (PMF.uniformOfFintype (Fin 2)) := by
  let g :
      SimpleFunc UnitAddCircle (Fin n → modOneDoublingHalfPartition.parts) :=
    prefixBlockCode modOneDoubling modOneDoubling_measurePreserving.measurable
      modOneDoublingHalfPartition n
  let Λ : (Fin n → modOneDoublingHalfPartition.parts) → (Fin n → Bool) :=
    halfPartitionWordLabel n
  let μg : Measure (Fin n → modOneDoublingHalfPartition.parts) := Measure.map g volume
  let μb : Measure (Fin n → Bool) := Measure.map (modOneDoublingPrefixSimpleFunc n) volume
  letI : IsProbabilityMeasure μg := Measure.isProbabilityMeasure_map g.aemeasurable
  letI : IsProbabilityMeasure μb :=
    Measure.isProbabilityMeasure_map (modOneDoublingPrefixSimpleFunc n).aemeasurable
  have hblock :
      (modOneDoublingHalfPartition.block modOneDoubling
          modOneDoubling_measurePreserving.measurable n).partitionEntropy volume =
        entropy μg.toPMF := by
    -- Proof comment: rewrite the block partition to the transparent prefix code and apply the
    -- `ofSimpleFunc` entropy bridge.
    simpa [g, μg, block_eq_ofSimpleFunc_prefixBlockCode
      modOneDoubling_measurePreserving.measurable modOneDoublingHalfPartition n] using
      (partitionEntropy_ofSimpleFunc_eq_entropy_law (P := volume) g)
  have hfactor :
      (modOneDoublingPrefixSimpleFunc n : UnitAddCircle → Fin n → Bool) =
        fun z ↦ Λ (g z) := by
    -- Proof comment: the explicit Boolean prefix code is the injective relabeling of the
    -- transparent block code by the two atom labels.
    simpa [g, Λ] using modOneDoublingPrefixSimpleFunc_eq_label_prefixBlockCode n
  letI : IsProbabilityMeasure (Measure.map (fun z : UnitAddCircle ↦ Λ (g z)) volume) := by
    -- Proof comment: the relabeled transparent block code is again a pushforward of the ambient
    -- probability measure.
    exact Measure.isProbabilityMeasure_map
      ((Measurable.of_discrete (f := Λ)).comp g.measurable).aemeasurable
  have hmap :
      μb.toPMF = PMF.map Λ μg.toPMF := by
    -- Proof comment: pushing forward first to block atoms and then relabeling them by `Bool`
    -- gives the same law as the explicit Boolean prefix code.
    simpa [μb, μg, g, Λ, hfactor] using
      (toPMF_eq_map_of_comp (P := volume) (f := g) (hf := g.measurable)
        (g := Λ) (hg := Measurable.of_discrete (f := Λ)))
  have hμb :
      μb.toPMF = PMF.uniformOfFintype (Fin n → Bool) := by
    -- Proof comment: the prefix-law lemma identifies the Boolean prefix code law with the
    -- uniform law on binary words of length `n`.
    apply PMF.toMeasure_injective
    rw [Measure.toPMF_toMeasure]
    change Measure.map (modOneDoublingPrefixSimpleFunc n) volume =
      (PMF.uniformOfFintype (Fin n → Bool)).toMeasure
    exact modOneDoublingPrefixLaw_eq_uniform n
  have hEntropy :
      entropy μg.toPMF = entropy (PMF.uniformOfFintype (Fin n → Bool)) := by
    -- Proof comment: the coordinatewise Boolean relabeling is injective, so it preserves the
    -- Shannon entropy of the block-name law.
    calc
      entropy μg.toPMF = entropy (PMF.map Λ μg.toPMF) := by
        symm
        exact entropy_map_eq_of_injective μg.toPMF Λ (halfPartitionWordLabel_injective n)
      _ = entropy μb.toPMF := by
        rw [hmap]
      _ = entropy (PMF.uniformOfFintype (Fin n → Bool)) := by
        rw [hμb]
  -- Proof comment: combine the transparent block-entropy identification with the normalized
  -- uniform-word entropy computation.
  calc
    (modOneDoublingHalfPartition.block modOneDoubling
        modOneDoubling_measurePreserving.measurable n).partitionEntropy volume *
      (((n : ℕ) : EReal)⁻¹) =
        entropy μg.toPMF * (((n : ℕ) : EReal)⁻¹) := by
          rw [hblock]
    _ = entropy (PMF.uniformOfFintype (Fin n → Bool)) * (((n : ℕ) : EReal)⁻¹) := by
          rw [hEntropy]
    _ = entropy (PMF.uniformOfFintype (Fin 2)) := uniformBoolWordEntropyNormalized n

/-- Helper for Exercise 20.6.1: the remaining missing comparison is the specialized upper bound
from the full Kolmogorov--Sinai entropy to the dynamical entropy of the half partition. -/
private theorem kolmogorovSinai_le_dynamicalEntropy_halfPartition :
    h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable) ≤
      h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable;
        modOneDoublingHalfPartition) := by
  -- Route correction: now that the canonical owner theorem is available, bridge the local
  -- generator predicate to the owner statement and close the comparison by equality.
  have hgen : is_generator modOneDoubling modOneDoublingHalfPartition :=
    modOneDoublingHalfPartition_isGenerator
  exact le_of_eq <|
    _root_.kolmogorov_sinai_of_generator (P := volume)
      (hτ := modOneDoubling_measurePreserving) (part := modOneDoublingHalfPartition) hgen

/-- Helper for Exercise 20.6.1: once the orbit code is identified with the Chapter 7 Bernoulli
digit model, the remaining entropy step is the finite-prefix law computation for the half
partition. -/
private theorem modOneDoublingHalfPartition_dynamicalEntropy_eq_entropy_uniformFinTwo :
    h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable;
      modOneDoublingHalfPartition) = entropy (PMF.uniformOfFintype (Fin 2)) := by
  -- Proof comment: once every normalized block entropy is the same constant, the defining infimum
  -- of dynamical entropy collapses to that singleton value.
  rw [MeasurableFinpartition.dynamicalEntropy_def]
  have hrange :
      Set.range
          (fun n : ℕ+ ↦
            (modOneDoublingHalfPartition.block modOneDoubling
                modOneDoubling_measurePreserving.measurable n).partitionEntropy volume *
              (((n : ℕ) : EReal)⁻¹)) =
        {entropy (PMF.uniformOfFintype (Fin 2))} := by
    -- Proof comment: the previous helper shows that every point of the range is the same entropy
    -- constant.
    ext x
    constructor
    · rintro ⟨n, rfl⟩
      simp [modOneDoublingHalfPartition_blockEntropyNormalized n]
    · intro hx
      simp at hx
      subst hx
      refine ⟨1, ?_⟩
      simpa using modOneDoublingHalfPartition_blockEntropyNormalized 1
  rw [hrange, sInf_singleton]

/-- The dyadic coding identifies the entropy of the doubling map with the entropy of the fair
binary Bernoulli shift. -/
theorem kolmogorov_sinai_entropy_modOneDoubling_eq_entropy_uniformFinTwo :
    h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable) =
      entropy (PMF.uniformOfFintype (Fin 2)) := by
  -- Route correction: close the theorem by `le_antisymm` around the explicit half partition,
  -- rather than by the unavailable generic generator equality wrapper.
  refine le_antisymm ?_ ?_
  · -- Proof comment: the new specialized upper bound reduces the full entropy to the explicit
    -- half-partition dynamical entropy, which was computed from uniform block laws above.
    calc
      h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable) ≤
          h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable;
            modOneDoublingHalfPartition) :=
        kolmogorovSinai_le_dynamicalEntropy_halfPartition
      _ = entropy (PMF.uniformOfFintype (Fin 2)) :=
        modOneDoublingHalfPartition_dynamicalEntropy_eq_entropy_uniformFinTwo
  · -- Proof comment: every dynamical entropy term is one competitor in the Kolmogorov--Sinai
    -- supremum, so the half-partition value gives the reverse inequality.
    calc
      entropy (PMF.uniformOfFintype (Fin 2)) =
          h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable;
            modOneDoublingHalfPartition) :=
        modOneDoublingHalfPartition_dynamicalEntropy_eq_entropy_uniformFinTwo.symm
      _ ≤ h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable) :=
        dynamicalEntropy_le_kolmogorovSinai volume modOneDoubling
          modOneDoubling_measurePreserving.measurable modOneDoublingHalfPartition

/-- Exercise 20.6.1: the Lebesgue-measure entropy of the doubling map `x ↦ 2x (mod 1)` on
`[0,1)` is `log 2`; equivalently, the corresponding system on `AddCircle 1` has entropy `log 2`. -/
theorem kolmogorov_sinai_entropy_modOneDoubling_eq_log_two :
    h(volume, modOneDoubling, modOneDoubling_measurePreserving.measurable) =
      ((Real.log 2 : ℝ) : EReal) := by
  rw [kolmogorov_sinai_entropy_modOneDoubling_eq_entropy_uniformFinTwo]
  rw [entropy_eq_sum]
  simp [PMF.uniformOfFintype_apply]
