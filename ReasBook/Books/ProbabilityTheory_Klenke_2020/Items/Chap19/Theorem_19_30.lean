/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_30
import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Theorem_17_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_19
import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Theorem_19_25
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v w

namespace ProbabilityTheory

attribute [local instance] Classical.propDecidable

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]
variable {Ω : Type v} [MeasurableSpace Ω]
variable {Ω' : Type w} [MeasurableSpace Ω']

/-- Helper for Theorem 19.30: the ambient target attached to `A : Set s` has complement equal to
the ambient copy of the subtype complement `Aᶜ`. -/
private theorem ambientTarget_compl_eq_image_subtypeCompl
    {s : Set E} (A : Set s) :
    ((((↑) '' A) ∪ sᶜ : Set E)ᶜ) = Subtype.val '' (Aᶜ : Set s) := by
  -- Proof comment: a point avoids both the ambient image of `A` and the ambient complement `sᶜ`
  -- exactly when it comes from some `z : s` that is not in `A`.
  ext x
  constructor
  · intro hx
    have hxs : x ∈ s := by
      by_contra hxs
      exact hx (Or.inr hxs)
    refine ⟨⟨x, hxs⟩, ?_, rfl⟩
    intro hxA
    exact hx <| Or.inl ⟨⟨x, hxs⟩, hxA, rfl⟩
  · rintro ⟨x, hxA, rfl⟩
    intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨y, hyA, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      exact hxA (hyx' ▸ hyA)
    · exact hx x.2

/-- Helper for Theorem 19.30: the ambient target attached to a cofinite `A : Set s` is again
cofinite after transporting from the subtype to the ambient state space. -/
private theorem ambientTarget_compl_finite
    {s : Set E} {A : Set s} (hAfinite : (Aᶜ : Set s).Finite) :
    ((((↑) '' A) ∪ sᶜ : Set E)ᶜ).Finite := by
  -- Proof comment: after identifying the complement with the ambient image of `Aᶜ`, finiteness
  -- is preserved by the subtype coercion map.
  rw [ambientTarget_compl_eq_image_subtypeCompl A]
  exact hAfinite.image Subtype.val

/-- Helper for Theorem 19.30: a subtype vertex outside `A` also lies outside the transported
ambient target `((↑) '' A) ∪ sᶜ`. -/
private theorem not_mem_ambientTarget_of_visibleSubtype
    {s : Set E} {A : Set s} (y : {z : s // z ∉ A}) :
    (y.1 : E) ∉ (((↑) '' A) ∪ sᶜ : Set E) := by
  -- Proof comment: the ambient target consists of the subtype points coming from `A` together
  -- with the points outside `s`, and `y` belongs to neither piece.
  intro hy
  rcases hy with hy | hy
  · rcases hy with ⟨z, hzA, hzy⟩
    have hzy' : z = y.1 := Subtype.ext hzy
    exact y.2 (hzy' ▸ hzA)
  · exact hy y.1.2

/-- Helper for Theorem 19.30: a point outside the transported ambient target must still lie in the
original subtype carrier `s`. -/
private theorem mem_subtype_of_not_mem_ambientTarget
    {s : Set E} {A : Set s}
    (y : {z : E // z ∉ (((↑) '' A) ∪ sᶜ : Set E)}) :
    y.1 ∈ s := by
  -- Proof comment: the ambient target already contains the whole complement `sᶜ`.
  by_contra hy
  exact y.2 (Or.inr hy)

/-- Helper for Theorem 19.30: a point outside the transported ambient target does not come from
the subtype target `A`. -/
private theorem not_mem_subtypeTarget_of_not_mem_ambientTarget
    {s : Set E} {A : Set s}
    (y : {z : E // z ∉ (((↑) '' A) ∪ sᶜ : Set E)}) :
    (⟨y.1, mem_subtype_of_not_mem_ambientTarget (A := A) y⟩ : s) ∉ A := by
  -- Proof comment: if the ambient point came from `A`, it would belong to the image part of the
  -- transported target.
  intro hyA
  exact y.2 <| Or.inl ⟨⟨y.1, mem_subtype_of_not_mem_ambientTarget (A := A) y⟩, hyA, rfl⟩

/-- Helper for Theorem 19.30: visible subtype vertices map canonically to the ambient complement
carrier of the transported target. -/
private abbrev ambientVisible
    {s : Set E} {A : Set s} (y : {z : s // z ∉ A}) :
    {z : E // z ∉ (((↑) '' A) ∪ sᶜ : Set E)} :=
  ⟨y.1, not_mem_ambientTarget_of_visibleSubtype y⟩

/-- Helper for Theorem 19.30: the transported ambient complement carrier maps back to the subtype
complement carrier by recovering membership in `s` and then in `Aᶜ`. -/
private abbrev subtypeVisible
    {s : Set E} {A : Set s}
    (y : {z : E // z ∉ (((↑) '' A) ∪ sᶜ : Set E)}) :
    {z : s // z ∉ A} :=
  ⟨⟨y.1, mem_subtype_of_not_mem_ambientTarget (A := A) y⟩,
    not_mem_subtypeTarget_of_not_mem_ambientTarget (A := A) y⟩

/-- Helper for Theorem 19.30: transporting a visible subtype vertex to the ambient complement and
back is the identity. -/
private theorem subtypeVisible_ambientVisible
    {s : Set E} {A : Set s} (y : {z : s // z ∉ A}) :
    subtypeVisible (A := A) (ambientVisible (A := A) y) = y := by
  -- Proof comment: both maps keep the same underlying ambient point; only the proof witnesses are
  -- reconstructed.
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-- Helper for Theorem 19.30: transporting an ambient complement vertex to the subtype carrier and
back is the identity. -/
private theorem ambientVisible_subtypeVisible
    {s : Set E} {A : Set s}
    (y : {z : E // z ∉ (((↑) '' A) ∪ sᶜ : Set E)}) :
    ambientVisible (A := A) (subtypeVisible (A := A) y) = y := by
  -- Proof comment: after recovering the subtype membership of `y`, the ambient point itself is
  -- unchanged.
  apply Subtype.ext
  rfl

/-- Helper for Theorem 19.30: the visible complement carrier of `A : Set s` is canonically
equivalent to the ambient complement carrier of the transported target `((↑) '' A) ∪ sᶜ`. -/
private abbrev ambientTargetSubtypeComplEquiv
    {s : Set E} {A : Set s} :
    {z : s // z ∉ A} ≃ {z : E // z ∉ (((↑) '' A) ∪ sᶜ : Set E)} :=
  { toFun := ambientVisible (A := A)
    invFun := subtypeVisible (A := A)
    left_inv := subtypeVisible_ambientVisible (A := A)
    right_inv := ambientVisible_subtypeVisible (A := A) }

/-- Helper for Theorem 19.30: the unit edge weights on an induced graph are exactly the ambient
unit edge weights evaluated on the underlying vertices. -/
private theorem simpleGraphWeights_induce_apply
    {s : Set E} (G : SimpleGraph E) (y z : s) :
    simpleGraphWeights (SimpleGraph.induce s G) y z = simpleGraphWeights G y.1 z.1 := by
  -- Proof comment: induced adjacency is definitionally the ambient adjacency restricted to the
  -- subtype carrier.
  simp [simpleGraphWeights, SimpleGraph.induce_adj]

/-- Helper for Theorem 19.30: rewriting the cofinite-target `sInf` as an indexed infimum over the
subtype of admissible cofinite targets makes the later monotonicity argument a pointwise `iInf`
comparison. -/
private theorem effectiveConductanceToInfinity_eq_iInf_cofiniteTargets
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) :
    effectiveConductanceToInfinity C P X x =
      conductance C x *
        ⨅ A : {A : Set E // Aᶜ.Finite ∧ x ∉ A},
          escapeToSetProbability P X x A.1 := by
  -- Proof comment: package each cofinite target avoiding `x` as a subtype element so that the
  -- source-facing existential infimum becomes a plain indexed `iInf`.
  rw [effectiveConductanceToInfinity_def]
  congr 1
  let f : {A : Set E // Aᶜ.Finite ∧ x ∉ A} → ℝ≥0∞ :=
    fun A ↦ escapeToSetProbability P X x A.1
  have himage :
      {r : ℝ≥0∞ |
          ∃ A : Set E, Aᶜ.Finite ∧ x ∉ A ∧ r = escapeToSetProbability P X x A} =
        f '' Set.univ := by
    ext r
    constructor
    · rintro ⟨A, hAfinite, hxA, rfl⟩
      exact ⟨⟨A, hAfinite, hxA⟩, by simp [f]⟩
    · rintro ⟨A, -, rfl⟩
      exact ⟨A.1, A.2.1, A.2.2, rfl⟩
  rw [himage, sInf_image]
  simp [f]

/-- Helper for Theorem 19.30: collapse a cofinite target `A` to one sink vertex while keeping the
finite complement `Aᶜ` as explicit states. -/
private def cofiniteTargetCollapse (C : E → E → ℝ≥0∞) (A : Set E) :
    ({y : E // y ∉ A} ⊕ Unit) → ({y : E // y ∉ A} ⊕ Unit) → ℝ≥0∞ :=
  fun u v ↦
    match u, v with
    | Sum.inl x, Sum.inl y => C x.1 y.1
    | Sum.inl x, Sum.inr _ => ∑' y : E, if y ∈ A then C x.1 y else 0
    | Sum.inr _, Sum.inl y => ∑' x : E, if x ∈ A then C x y.1 else 0
    | Sum.inr _, Sum.inr _ => 0

/-- Helper for Theorem 19.30: the collapsed cofinite-target conductance inherits symmetry from the
ambient weight family. -/
private theorem cofiniteTargetCollapse_symmetric
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    [IsRandomWalkWithWeights p C] (A : Set E) :
    ∀ u v : ({y : E // y ∉ A} ⊕ Unit),
      cofiniteTargetCollapse C A u v = cofiniteTargetCollapse C A v u := by
  -- Proof comment: the explicit complement-complement edge keeps ambient symmetry, and each
  -- complement-sink edge is defined by the same collapsed sum in either direction.
  intro u v
  rcases u with x | x <;> rcases v with y | y
  · simpa [cofiniteTargetCollapse] using
      ((inferInstance : IsRandomWalkWithWeights p C).symmetric x.1 y.1)
  · unfold cofiniteTargetCollapse
    refine tsum_congr fun z ↦ ?_
    by_cases hz : z ∈ A
    · simpa [hz] using ((inferInstance : IsRandomWalkWithWeights p C).symmetric x.1 z)
    · simp [hz]
  · unfold cofiniteTargetCollapse
    refine tsum_congr fun z ↦ ?_
    by_cases hz : z ∈ A
    · simpa [hz] using ((inferInstance : IsRandomWalkWithWeights p C).symmetric z y.1)
    · simp [hz]
  · simp [cofiniteTargetCollapse]

/-- Helper for Theorem 19.30: collapsing a cofinite target preserves pointwise edge-weight
monotonicity. -/
private theorem cofiniteTargetCollapse_mono
    {C C' : E → E → ℝ≥0∞} (A : Set E)
    (hCC' : ∀ x y : E, C' x y ≤ C x y) :
    ∀ u v : ({y : E // y ∉ A} ⊕ Unit),
      cofiniteTargetCollapse C' A u v ≤ cofiniteTargetCollapse C A u v := by
  -- Proof comment: every branch is either the original pointwise inequality on `C' ≤ C` or a
  -- `tsum` of such inequalities over the collapsed sink term.
  intro u v
  rcases u with x | x <;> rcases v with y | y
  · simpa [cofiniteTargetCollapse] using hCC' x.1 y.1
  · unfold cofiniteTargetCollapse
    exact ENNReal.tsum_le_tsum fun z ↦ by
      by_cases hz : z ∈ A
      · simpa [hz] using hCC' x.1 z
      · simp [hz]
  · unfold cofiniteTargetCollapse
    exact ENNReal.tsum_le_tsum fun z ↦ by
      by_cases hz : z ∈ A
      · simpa [hz] using hCC' z y.1
      · simp [hz]
  · simp [cofiniteTargetCollapse]

/-- Helper for Theorem 19.30: the collapsed edge from a complement vertex into the sink is bounded
by the ambient total conductance at that same vertex. -/
private theorem cofiniteTargetCollapse_left_sink_le_conductance
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    [IsRandomWalkWithWeights p C] (A : Set E) (x : {y : E // y ∉ A}) :
    cofiniteTargetCollapse C A (Sum.inl x) (Sum.inr ()) ≤ conductance C x.1 := by
  -- Proof comment: the sink edge is the sum of the ambient edges from `x` into `A`, so it is
  -- bounded by the full ambient row sum at `x`.
  unfold cofiniteTargetCollapse conductance
  refine ENNReal.tsum_le_tsum fun y ↦ ?_
  by_cases hy : y ∈ A
  · simpa [hy]
  · simp [hy]

/-- Helper for Theorem 19.30: every row of the sink-collapsed cofinite network is finite as soon
as the visible complement `Aᶜ` is finite. -/
private theorem cofiniteTargetCollapse_conductance_lt_top
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    [IsRandomWalkWithWeights p C] {A : Set E} (hAfinite : Aᶜ.Finite) :
    ∀ u : ({y : E // y ∉ A} ⊕ Unit), conductance (cofiniteTargetCollapse C A) u < ∞ := by
  classical
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  letI : Fintype {y : E // y ∉ A} := hAfinite.fintype
  intro u
  rcases u with x | u
  · -- Proof comment: the visible row is a finite sum of ambient edges together with one sink
    -- edge, and each summand is bounded by the ambient row sum at `x`.
    simp only [conductance, tsum_fintype, ENNReal.sum_lt_top, Finset.mem_univ, forall_true_left]
    intro a
    rcases a with y | y
    · exact
        lt_of_le_of_lt
          (by
            simpa [cofiniteTargetCollapse, conductance] using
              (ENNReal.le_tsum y.1 : C x.1 y.1 ≤ ∑' z : E, C x.1 z))
          (hWalk.conductance_lt_top x.1)
    · exact
        lt_of_le_of_lt
          (cofiniteTargetCollapse_left_sink_le_conductance
            (p := p) (C := C) A x)
          (hWalk.conductance_lt_top x.1)
  · -- Proof comment: every sink-to-visible edge is the symmetric copy of a visible-to-sink edge,
    -- and there is no sink loop.
    simp only [conductance, cofiniteTargetCollapse, tsum_fintype, ENNReal.sum_lt_top,
      Finset.mem_univ, forall_true_left]
    intro a
    rcases a with y | y
    · exact
        lt_of_le_of_lt
          (by
            calc
              cofiniteTargetCollapse C A (Sum.inr ()) (Sum.inl y)
                  = cofiniteTargetCollapse C A (Sum.inl y) (Sum.inr ()) := by
                      simpa using
                        (cofiniteTargetCollapse_symmetric (p := p) (C := C) A
                          (Sum.inr ()) (Sum.inl y))
              _ ≤ conductance C y.1 :=
                  cofiniteTargetCollapse_left_sink_le_conductance
                    (p := p) (C := C) A y)
          (hWalk.conductance_lt_top y.1)
    · simp [cofiniteTargetCollapse]

/-- Helper for Theorem 19.30: collapsing the cofinite target into one sink preserves the total
conductance of every visible row. -/
private theorem cofiniteTargetCollapse_visible_conductance
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    [IsRandomWalkWithWeights p C] {A : Set E} [Fintype {y : E // y ∉ A}]
    (y : {z : E // z ∉ A}) :
    conductance (cofiniteTargetCollapse C A) (Sum.inl y) = conductance C y.1 := by
  classical
  have hvisible :
      ∑ z : {z : E // z ∉ A}, C y.1 z.1 =
        ∑' z : E, Set.indicator {z : E | z ∉ A} (fun z ↦ C y.1 z) z := by
    calc
      ∑ z : {z : E // z ∉ A}, C y.1 z.1 = ∑' z : {z : E // z ∉ A}, C y.1 z.1 := by
            symm
            exact tsum_fintype (f := fun z : {z : E // z ∉ A} ↦ C y.1 z.1)
      _ = ∑' z : E, Set.indicator {z : E | z ∉ A} (fun z ↦ C y.1 z) z := by
            simpa using (tsum_subtype (s := {z : E | z ∉ A}) (f := fun z : E ↦ C y.1 z))
  -- Proof comment: the visible part contributes the row sum over `Aᶜ`, while the sink collects
  -- exactly the complementary row sum over `A`.
  calc
    conductance (cofiniteTargetCollapse C A) (Sum.inl y)
        = (∑ z : {z : E // z ∉ A}, C y.1 z.1) +
            ∑' z : E, if z ∈ A then C y.1 z else 0 := by
              rw [conductance, tsum_fintype, Fintype.sum_sum_type]
              simp [cofiniteTargetCollapse]
    _ =
        (∑' z : E, Set.indicator {z : E | z ∉ A} (fun z ↦ C y.1 z) z) +
          ∑' z : E, if z ∈ A then C y.1 z else 0 := by
            rw [hvisible]
    _ =
        ∑' z : E,
          (Set.indicator {z : E | z ∉ A} (fun z ↦ C y.1 z) z +
            if z ∈ A then C y.1 z else 0) := by
              rw [← ENNReal.tsum_add]
    _ = ∑' z : E, C y.1 z := by
          refine tsum_congr fun z ↦ ?_
          by_cases hz : z ∈ A
          · simp [Set.indicator, hz]
          · simp [Set.indicator, hz]
    _ = conductance C y.1 := by
          rfl

/-- Helper for Theorem 19.30: after transporting the subtype complement of `A : Set s` to the
ambient complement of `((↑) '' A) ∪ sᶜ`, the induced-graph sink edge is bounded by the ambient
sink edge. -/
private theorem cofiniteTargetCollapse_sinkEdge_induced_le_ambient
    {s : Set E} (G : SimpleGraph E) {A : Set s} (y : {z : s // z ∉ A}) :
    cofiniteTargetCollapse (simpleGraphWeights (SimpleGraph.induce s G)) A
        (Sum.inl y) (Sum.inr ()) ≤
      cofiniteTargetCollapse (simpleGraphWeights G) (((↑) '' A) ∪ sᶜ : Set E)
        (Sum.inl (ambientVisible (A := A) y)) (Sum.inr ()) := by
  let B : Set E := (((↑) '' A) ∪ sᶜ : Set E)
  let g : E → ℝ≥0∞ := fun z ↦ if z ∈ B then simpleGraphWeights G y.1 z else 0
  have hSubtypeSum :
      (∑' z : s, if z ∈ A then simpleGraphWeights G y.1 z.1 else 0) = ∑' z : s, g z := by
    -- Proof comment: on the subtype carrier `s`, membership in the transported ambient target `B`
    -- is equivalent to membership in `A`.
    refine tsum_congr fun z ↦ ?_
    by_cases hzA : z ∈ A
    · have hzB : (z : E) ∈ B := by
        exact Or.inl ⟨z, hzA, rfl⟩
      simp [g, B, hzA, hzB]
    · have hzImage : (z : E) ∉ ((↑) '' A : Set E) := by
        rintro ⟨w, hwA, hwz⟩
        have hwz' : w = z := Subtype.ext hwz
        exact hzA (hwz' ▸ hwA)
      have hzB : (z : E) ∉ B := by
        simp [B, hzImage, z.2]
      simp [g, B, hzA, hzB]
  calc
    cofiniteTargetCollapse (simpleGraphWeights (SimpleGraph.induce s G)) A
        (Sum.inl y) (Sum.inr ())
        = ∑' z : s, if z ∈ A then simpleGraphWeights G y.1 z.1 else 0 := by
            -- Proof comment: the sink edge of the induced collapse is the sum over the subtype
            -- target, and induced visible-visible weights are ambient visible-visible weights.
            simp [cofiniteTargetCollapse, simpleGraphWeights_induce_apply]
    _ = ∑' z : s, g z := hSubtypeSum
    _ = ∑' z : E, Set.indicator (s : Set E) g z := by
          simpa [g] using (tsum_subtype (s := s) (f := g))
    _ ≤ ∑' z : E, g z := by
          exact ENNReal.tsum_le_tsum fun z ↦ by
            by_cases hz : z ∈ s
            · simp [Set.indicator, hz]
            · simp [Set.indicator, hz]
    _ = cofiniteTargetCollapse (simpleGraphWeights G) B
          (Sum.inl (ambientVisible (A := A) y)) (Sum.inr ()) := by
            -- Proof comment: the ambient collapse sink edge is exactly the ambient target sum.
            simp [g, B, cofiniteTargetCollapse]

/-- Helper for Theorem 19.30: a weighted row identity for `u` at `x` forces the Ohm-law current
to have zero net flow there. -/
private theorem netFlowAt_electricalCurrent_eq_zero_of_weightedSum
    {F : Type*} [Fintype F] {C : F → F → ℝ≥0∞} {u : F → ℝ} {x : F}
    (hCfinite : conductance C x < ∞)
    (hweighted :
      (conductance C x).toReal * u x = ∑ y : F, (C x y).toReal * u y) :
    netFlowAt (electricalCurrent C u) x = 0 := by
  have hentry_ne_top : ∀ y : F, C x y ≠ ∞ := by
    intro y
    have hxy_le : C x y ≤ conductance C x := by
      simpa [conductance] using (ENNReal.le_tsum y : C x y ≤ ∑' z : F, C x z)
    exact ne_of_lt (lt_of_le_of_lt hxy_le hCfinite)
  have hconductance_sum :
      ∑ y : F, (C x y).toReal = (conductance C x).toReal := by
    -- Proof comment: finiteness of the row lets us move `ENNReal.toReal` through the finite sum.
    simpa [conductance] using
      (ENNReal.toReal_sum (s := Finset.univ) (f := fun y : F ↦ C x y)
        (fun y _ ↦ hentry_ne_top y)).symm
  -- Proof comment: expand the Ohm-law row at `x`, collect the `u x` terms, and substitute the
  -- weighted row identity.
  calc
    netFlowAt (electricalCurrent C u) x
        = ∑ y : F, (C x y).toReal * (u x - u y) := by
            simp [netFlowAt, electricalCurrent]
    _ = (∑ y : F, (C x y).toReal * u x) - ∑ y : F, (C x y).toReal * u y := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          ring
    _ = ((∑ y : F, (C x y).toReal) * u x) - ∑ y : F, (C x y).toReal * u y := by
          rw [Finset.sum_mul]
    _ = (conductance C x).toReal * u x - ∑ y : F, (C x y).toReal * u y := by
          rw [hconductance_sum]
    _ = 0 := by
          linarith

/-- Helper for Theorem 19.30: once the visible vertices satisfy the weighted row identities,
the collapsed voltage is an electrical potential outside the two-point boundary
`{x, sink}`. -/
private theorem cofiniteTargetCollapse_isElectricalPotential_of_weightedSum
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    [IsRandomWalkWithWeights p C]
    (x : E) {A : Set E} [Fintype {y : E // y ∉ A}]
    (hAfinite : Aᶜ.Finite) (hxA : x ∉ A)
    {u : ({y : E // y ∉ A} ⊕ Unit) → ℝ}
    (hweighted :
      ∀ y : {z : E // z ∉ A}, y.1 ≠ x →
        (conductance (cofiniteTargetCollapse C A) (Sum.inl y)).toReal * u (Sum.inl y) =
          ∑ z : ({z : E // z ∉ A} ⊕ Unit),
            (cofiniteTargetCollapse C A (Sum.inl y) z).toReal * u z) :
    IsElectricalPotential (cofiniteTargetCollapse C A)
      ({Sum.inl ⟨x, hxA⟩, Sum.inr ()} : Set ({y : E // y ∉ A} ⊕ Unit)) u := by
  refine ⟨?_, ?_⟩
  · intro a b
    -- Proof comment: symmetry of the collapsed conductance makes the induced Ohm-law current
    -- antisymmetric.
    rw [electricalCurrent_apply, electricalCurrent_apply,
      cofiniteTargetCollapse_symmetric (p := p) (C := C) A a b]
    ring
  · intro a ha
    rcases a with y | u0
    · have hyx : y.1 ≠ x := by
        intro hyx
        have hy_sub : y = ⟨x, hxA⟩ := by
          apply Subtype.ext
          simpa using hyx
        apply ha
        simpa [hy_sub]
      -- Proof comment: every visible interior row is closed by the weighted identity supplied in
      -- `hweighted`.
      exact
        netFlowAt_electricalCurrent_eq_zero_of_weightedSum
          (C := cofiniteTargetCollapse C A) (u := u) (x := Sum.inl y)
          (cofiniteTargetCollapse_conductance_lt_top
            (p := p) (C := C) (A := A) hAfinite (Sum.inl y))
          (hweighted y hyx)
    · cases u0
      exfalso
      exact ha (by simp)

/-- Helper for Theorem 19.30: the collapsed boundary-hit event records that the first hit of
`insert x A` lands in `A`, which is the sink side of the collapsed network. -/
private def collapsedBoundaryHitEvent
    (X : ℕ → Ω → E) (x : E) (A : Set E) : Set Ω :=
  {ω | hittingAfter X (insert x A) 0 ω < ⊤ ∧
      stoppedValue X (hittingAfter X (insert x A) 0) ω ∈ A}

/-- Helper for Theorem 19.30: the future path after `k` steps is the shifted trajectory
`n ↦ X (n + k)`. -/
private def shiftedFuturePath {Ω' : Type*} [MeasurableSpace Ω']
    (Y : ℕ → Ω' → E) (k : ℕ) : Ω' → ℕ → E :=
  fun ω n ↦ Y (n + k) ω

/-- Helper for Theorem 19.30: if each time coordinate of `Y` is measurable, then the shifted
future-path map `ω ↦ shiftedFuturePath Y k ω` is measurable. -/
private theorem measurable_shiftedFuturePath {Ω' : Type*} [MeasurableSpace Ω']
    (Y : ℕ → Ω' → E) (hY : ∀ n : ℕ, Measurable (Y n)) (k : ℕ) :
    Measurable (shiftedFuturePath Y k) := by
  refine measurable_pi_lambda _ fun n ↦ ?_
  simpa [shiftedFuturePath] using hY (n + k)

/-- Helper for Theorem 19.30: the past path up to time `k` records the coordinates
`0, 1, ..., k`. -/
private def pastPath {Ω' : Type*} [MeasurableSpace Ω']
    (Y : ℕ → Ω' → E) (k : ℕ) : Ω' → Fin (k + 1) → E :=
  fun ω i ↦ Y i ω

/-- Helper for Theorem 19.30: if each time coordinate of `Y` is measurable, then the finite
history map `pastPath Y k` is measurable. -/
private theorem measurable_pastPath {Ω' : Type*} [MeasurableSpace Ω']
    (Y : ℕ → Ω' → E) (hY : ∀ n : ℕ, Measurable (Y n)) (k : ℕ) :
    Measurable (pastPath Y k) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [pastPath] using hY i

/-- Helper for Theorem 19.30: every generated history filtration is a sub-σ-algebra of the
ambient measurable space. -/
private theorem generatedFiltrationSpace_le_ambient
    {Ω' : Type*} [MeasurableSpace Ω'] {F : Type*} [MeasurableSpace F]
    (Y : ℕ → Ω' → F) (hY : ∀ n : ℕ, Measurable (Y n)) (k : ℕ) :
    generatedFiltrationSpace Y k ≤ ‹MeasurableSpace Ω'› := by
  refine iSup_le fun r ↦ iSup_le fun hr ↦ ?_
  exact (hY r).comap_le

/-- Helper for Theorem 19.30: the time-`k` generated filtration is the pullback sigma-algebra of
the finite-history map `pastPath X k`. -/
private theorem generatedFiltrationSpace_eq_pastPath_comapLocal
    (X : ℕ → Ω → E) (k : ℕ) :
    generatedFiltrationSpace X k = MeasurableSpace.comap (pastPath X k) inferInstance := by
  have hleft :
      MeasurableSpace.comap (pastPath X k) inferInstance ≤ generatedFiltrationSpace X k := by
    have hPastMeas :
        Measurable[generatedFiltrationSpace X k] (fun ω ↦ fun i : Fin (k + 1) ↦ X i ω) := by
      rw [@measurable_pi_iff]
      intro i
      refine Measurable.of_comap_le ?_
      exact le_iSup_of_le i <| le_iSup_of_le (show (i : ℕ) ≤ k from Nat.le_of_lt_succ i.2) le_rfl
    exact hPastMeas.comap_le
  have hright :
      generatedFiltrationSpace X k ≤ MeasurableSpace.comap (pastPath X k) inferInstance := by
    rw [generatedFiltrationSpace]
    refine iSup₂_le fun t ht ↦ ?_
    let i : Fin (k + 1) := ⟨t, Nat.lt_succ_of_le ht⟩
    have hCoord :
        Measurable[MeasurableSpace.comap (pastPath X k) inferInstance]
          (fun ω ↦ pastPath X k ω i) := by
      exact (measurable_pi_apply i).comp (comap_measurable (pastPath X k))
    simpa [pastPath, i] using hCoord.comap_le
  exact le_antisymm hright hleft

/-- Helper for Theorem 19.30: the ordered future coordinates after time `k` are the tuple
`i ↦ X (t i + k)`. -/
private def shiftedFuturePathCoordinates {n : ℕ} {Ω' : Type*} [MeasurableSpace Ω']
    (Y : ℕ → Ω' → E) (k : ℕ) (t : Fin n → ℕ) :
    Ω' → Fin n → E :=
  fun ω i ↦ Y (t i + k) ω

/-- Helper for Theorem 19.30: finite ordered coordinates of the shifted future path are measurable
whenever each coordinate of `Y` is measurable. -/
private theorem measurable_shiftedFuturePathCoordinates {n : ℕ} {Ω' : Type*}
    [MeasurableSpace Ω'] (Y : ℕ → Ω' → E) (hY : ∀ n, Measurable (Y n))
    (k : ℕ) (t : Fin n → ℕ) :
    Measurable (shiftedFuturePathCoordinates Y k t) := by
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [shiftedFuturePathCoordinates, Nat.add_comm] using hY (t i + k)

/-- Helper for Theorem 19.30: every Nat-indexed path measure is the projective limit of its finite
restriction marginals. -/
private theorem natPathMeasure_isProjectiveLimit_restrictions
    (ν : Measure (ℕ → E)) :
    MeasureTheory.IsProjectiveLimit ν (fun J : Finset ℕ ↦ ν.map J.restrict) := by
  intro J
  rfl

/-- Helper for Theorem 19.30: reindexing the sorted tuple attached to `J.orderEmbOfFin` recovers
the ordinary finite restriction map. -/
private theorem piCongrLeft_orderEmbOfFin_eq_restrict
    (J : Finset ℕ) (y : ℕ → E) :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) (fun i ↦ y (t i)) = J.restrict y := by
  dsimp
  ext j
  have hindex :
      J.orderEmbOfFin rfl ((J.orderIsoOfFin rfl).symm j) = j.1 := by
    exact congrArg Subtype.val ((J.orderIsoOfFin rfl).apply_symm_apply j)
  change
    ((Equiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
        (fun i ↦ y (J.orderEmbOfFin rfl i)) j) =
      J.restrict y j
  rw [Equiv.piCongrLeft_apply]
  simp [hindex]

/-- Helper for Theorem 19.30: reindexing the ordered shifted future coordinates by
`J.orderEmbOfFin` matches the ordinary finite restriction event. -/
private theorem shiftedFuturePathIndicator_eq_restrictIndicator {Ω' : Type*}
    [MeasurableSpace Ω'] (Y : ℕ → Ω' → E) (k : ℕ) (J : Finset ℕ) {A : Set (J → E)} :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
    let A' : Set (Fin J.card → E) :=
      (fun z ↦ (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) z) ⁻¹' A
    (fun ω ↦ Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ))
        (shiftedFuturePathCoordinates Y k t ω)) =
      fun ω ↦ Set.indicator A (fun _ : J → E ↦ (1 : ℝ))
        (J.restrict (shiftedFuturePath Y k ω)) := by
  dsimp
  funext ω
  have hEq :
      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
          (shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω) =
        J.restrict (shiftedFuturePath Y k ω) := by
    calc
      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
          (shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω)
          =
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
              (fun i ↦ shiftedFuturePath Y k ω (J.orderEmbOfFin rfl i)) := by
                rfl
      _ = J.restrict (shiftedFuturePath Y k ω) := by
            simpa using
              piCongrLeft_orderEmbOfFin_eq_restrict (J := J) (y := shiftedFuturePath Y k ω)
  have hmem :
      shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω ∈
          ((fun z ↦
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A)
        ↔ J.restrict (shiftedFuturePath Y k ω) ∈ A := by
    simpa using show
      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
          (shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω) ∈ A ↔
        J.restrict (shiftedFuturePath Y k ω) ∈ A from by rw [hEq]
  by_cases hω : J.restrict (shiftedFuturePath Y k ω) ∈ A
  · have hω' :
        shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω ∈
          ((fun z ↦
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) :=
      hmem.mpr hω
    simp [hω, hω']
  · have hω' :
        shiftedFuturePathCoordinates Y k (J.orderEmbOfFin rfl) ω ∉
          ((fun z ↦
            (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) := by
        intro hω'
        exact hω (hmem.mp hω')
    simp [hω, hω']

/-- Helper for Theorem 19.30: evaluating a composed kernel on a restricted pushforward equals the
corresponding set integral of row masses. -/
private theorem kernelCompRestrictMapRealEqSetIntegral
    {F : Type*} [MeasurableSpace F]
    (κ : Kernel E F) [IsMarkovKernel κ]
    (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → E} (hY : Measurable Y)
    {B : Set Ω} (_hB : MeasurableSet B) {A : Set F} (hA : MeasurableSet A) :
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
  let ν : Measure E := (μ.restrict B).map Y
  have hkernel_int :
      Integrable (fun y : E ↦ (κ y).real A) ν := by
    simpa [ν] using
      (ProbabilityTheory.Kernel.IsMarkovKernel.integrable (μ := ν) (κ := κ) hA)
  have hkernel_nonneg :
      0 ≤ᵐ[ν] fun y : E ↦ (κ y).real A :=
    Filter.Eventually.of_forall fun _ ↦ MeasureTheory.measureReal_nonneg
  have hcomp_real :
      ((κ ∘ₘ ν).real A) = ∫ y, (κ y).real A ∂ν := by
    rw [MeasureTheory.measureReal_def, MeasureTheory.Measure.bind_apply hA
      (ProbabilityTheory.Kernel.aemeasurable _)]
    have hlintegral :
        ∫⁻ y, κ y A ∂ν = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
      calc
        ∫⁻ y, κ y A ∂ν = ∫⁻ y, ENNReal.ofReal ((κ y).real A) ∂ν := by
            refine lintegral_congr_ae ?_
            filter_upwards with y
            rw [MeasureTheory.measureReal_def, ENNReal.ofReal_toReal]
            exact measure_ne_top _ _
        _ = ENNReal.ofReal (∫ y, (κ y).real A ∂ν) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hkernel_int hkernel_nonneg
    rw [hlintegral, ENNReal.toReal_ofReal]
    exact integral_nonneg_of_ae hkernel_nonneg
  have hmap_real :
      ∫ y, (κ y).real A ∂ν = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
    change
      ∫ y, (κ y).real A ∂((μ.restrict B).map Y) =
        ∫ ω, (κ (Y ω)).real A ∂(μ.restrict B)
    rw [MeasureTheory.integral_map hY.aemeasurable hkernel_int.aestronglyMeasurable]
  calc
    ((κ ∘ₘ ((μ.restrict B).map Y)).real A) = ∫ y, (κ y).real A ∂ν := by
      simpa [ν] using hcomp_real
    _ = ∫ ω in B, (κ (Y ω)).real A ∂μ := by
      simpa [ν] using hmap_real

/-- Helper for Theorem 19.30: evaluating a Nat-indexed path measure on a finite restriction
preimage is the same as evaluating its pushforward along that restriction. -/
private theorem kernelReal_restrictPreimage_eq_mapRestrictReal
    (ν : Measure (ℕ → E)) (J : Finset ℕ) {A : Set (J → E)} (hA : MeasurableSet A) :
    ν.real (J.restrict ⁻¹' A) = ((ν.map J.restrict).real A) := by
  simpa using
    (MeasureTheory.map_measureReal_apply (μ := ν) (f := J.restrict)
      (Finset.measurable_restrict J) hA).symm

/-- Helper for Theorem 19.30: integrating the ordered-tuple indicator of a finite restriction
event against a Nat-indexed path measure recovers the corresponding restricted pushforward mass. -/
private theorem orderedTupleIndicatorIntegral_eq_mapRestrictReal
    (ν : Measure (ℕ → E)) (J : Finset ℕ) {A : Set (J → E)} (hA : MeasurableSet A) :
    let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
    let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
    let A' : Set (Fin J.card → E) :=
      (fun z ↦ (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) z) ⁻¹' A
    (∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i)) ∂ν) =
      ((ν.map J.restrict).real A) := by
  dsimp
  calc
    ∫ y, Set.indicator ((fun z ↦
          (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A)
          (fun _ : Fin J.card → E ↦ (1 : ℝ))
          (fun i ↦ y (J.orderEmbOfFin rfl i)) ∂ν
        =
          ∫ y, Set.indicator (J.restrict ⁻¹' A) (fun _ : ℕ → E ↦ (1 : ℝ)) y ∂ν := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
            have hEq := piCongrLeft_orderEmbOfFin_eq_restrict (J := J) (y := y)
            have hmem :
                (fun i ↦ y (J.orderEmbOfFin rfl i)) ∈
                    ((fun z ↦
                      (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E)
                        ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) ↔
                  y ∈ J.restrict ⁻¹' A := by
              simpa using show
                (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) ((J.orderIsoOfFin rfl).toEquiv))
                    (fun i ↦ y (J.orderEmbOfFin rfl i)) ∈ A ↔
                  J.restrict y ∈ A from by rw [hEq]
            by_cases hy : y ∈ J.restrict ⁻¹' A
            · have hy' :
                (fun i ↦ y (J.orderEmbOfFin rfl i)) ∈
                  ((fun z ↦
                    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E)
                      ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) := hmem.mpr hy
              simp [hy, hy']
            · have hy' :
                (fun i ↦ y (J.orderEmbOfFin rfl i)) ∉
                  ((fun z ↦
                    (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E)
                      ((J.orderIsoOfFin rfl).toEquiv)) z) ⁻¹' A) := by
                  intro hy'
                  exact hy (hmem.mp hy')
              simp [hy, hy']
    _ = ν.real (J.restrict ⁻¹' A) := by
          simpa using
            (MeasureTheory.integral_indicator_one (μ := ν)
              (s := J.restrict ⁻¹' A) ((Finset.measurable_restrict J) hA))
    _ = ((ν.map J.restrict).real A) := by
          simpa using kernelReal_restrictPreimage_eq_mapRestrictReal (ν := ν) (J := J) hA

/-- Helper for Theorem 19.30: transport the Chapter 17 ordered-coordinate conditional-expectation
formula from the natural-number submonoid of `NNReal` back to the discrete-time `ℕ` indexing used
here. -/
private theorem orderedFutureCoordinateCondExp_of_markovProcessNat
    {m : ℕ} (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x} : Set Ω) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (f : (Fin m → E) → ℝ)
    (hf_meas : Measurable f) (hf_bdd : Bornology.IsBounded (Set.range f))
    (t : Fin m → ℕ) (ht : Monotone t) :
    ((P x : Measure Ω)[fun ω ↦ f (shiftedFuturePathCoordinates X k t ω) |
        generatedFiltrationSpace X k]) =ᵐ[(P x : Measure Ω)]
      fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X k ω) := by
  let Iℕ : AddSubmonoid NNReal := {
    carrier := {r | ∃ n : ℕ, ((n : ℕ) : NNReal) = r}
    zero_mem' := ⟨0, by simp⟩
    add_mem' := by
      intro a b ha hb
      rcases ha with ⟨m, hm⟩
      rcases hb with ⟨n, hn⟩
      refine ⟨m + n, ?_⟩
      simpa [hm, hn] }
  let natTime : ℕ → Iℕ := fun n ↦ ⟨n, ⟨n, rfl⟩⟩
  let natIndex : Iℕ → ℕ := fun s ↦
    Classical.choose (show ∃ n : ℕ, ((n : ℕ) : NNReal) = s.1 from s.2)
  let Xnat : Iℕ → Ω → E := fun s ω ↦ X (natIndex s) ω
  let reindexPath : (ℕ → E) → Iℕ → E := fun y s ↦ y (natIndex s)
  let κnat : Kernel E (Iℕ → E) := κ.map reindexPath
  let tnat : Fin m → Iℕ := fun i ↦ natTime (t i)
  have hnatIndex_spec : ∀ s : Iℕ, ((natIndex s : ℕ) : NNReal) = s.1 := by
    intro s
    exact Classical.choose_spec (show ∃ n : ℕ, ((n : ℕ) : NNReal) = s.1 from s.2)
  have hnatIndex_natTime : ∀ n : ℕ, natIndex (natTime n) = n := by
    intro n
    have hcast : (((natIndex (natTime n) : ℕ) : ℕ) : NNReal) = n := by
      simpa [natTime] using hnatIndex_spec (natTime n)
    exact_mod_cast hcast
  have hnatTime_natIndex : ∀ s : Iℕ, natTime (natIndex s) = s := by
    intro s
    apply Subtype.ext
    exact hnatIndex_spec s
  have hnatIndex_add : ∀ s u : Iℕ, natIndex (s + u) = natIndex s + natIndex u := by
    intro s u
    have hcast :
        (((natIndex (s + u) : ℕ) : ℕ) : NNReal) =
          ((natIndex s + natIndex u : ℕ) : NNReal) := by
      calc
        (((natIndex (s + u) : ℕ) : ℕ) : NNReal) = (s + u).1 := hnatIndex_spec (s + u)
        _ = s.1 + u.1 := rfl
        _ = (((natIndex s : ℕ) : ℕ) : NNReal) + (((natIndex u : ℕ) : ℕ) : NNReal) := by
              rw [hnatIndex_spec s, hnatIndex_spec u]
        _ = ((natIndex s + natIndex u : ℕ) : NNReal) := by simp
    exact_mod_cast hcast
  have hnatTime_le_iff : ∀ {n l : ℕ}, natTime n ≤ natTime l ↔ n ≤ l := by
    intro n l
    change ((n : NNReal) ≤ (l : NNReal)) ↔ n ≤ l
    norm_num
  have hsub : ∀ ⦃s u : Iℕ⦄, s ≤ u → u.1 - s.1 ∈ Iℕ := by
    intro s u hsu
    change ∃ n : ℕ, ((n : ℕ) : NNReal) = u.1 - s.1
    refine ⟨natIndex u - natIndex s, ?_⟩
    have hle : natIndex s ≤ natIndex u := by
      have : natTime (natIndex s) ≤ natTime (natIndex u) := by
        simpa [hnatTime_natIndex] using hsu
      exact hnatTime_le_iff.mp this
    calc
      (((natIndex u - natIndex s : ℕ) : ℕ) : NNReal)
          = ((natIndex u : ℕ) : NNReal) - ((natIndex s : ℕ) : NNReal) := by
              simpa [Nat.cast_sub hle]
      _ = u.1 - s.1 := by rw [hnatIndex_spec u, hnatIndex_spec s]
  have hreindex_meas : Measurable reindexPath := by
    refine measurable_pi_lambda _ fun s ↦ ?_
    exact measurable_pi_apply (natIndex s)
  have hpathMap_meas : Measurable (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) := by
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa using hX_meas n
  have hgenerated :
      ∀ n : ℕ, generatedFiltrationSpace Xnat (natTime n) = generatedFiltrationSpace X n := by
    intro n
    rw [generatedFiltrationSpace, generatedFiltrationSpace]
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun s hs ↦ ?_
      have hs' : natIndex s ≤ n := by
        have : natTime (natIndex s) ≤ natTime n := by
          simpa [hnatTime_natIndex] using hs
        exact hnatTime_le_iff.mp this
      have hcomap :
          MeasurableSpace.comap (X (natIndex s)) inferInstance ≤ generatedFiltrationSpace X n := by
        exact le_iSup_of_le (natIndex s) <| le_iSup_of_le hs' le_rfl
      simpa [Xnat] using hcomap
    · refine iSup₂_le fun r hr ↦ ?_
      have hr' : natTime r ≤ natTime n := hnatTime_le_iff.mpr hr
      have hcomap :
          MeasurableSpace.comap (Xnat (natTime r)) inferInstance ≤
            generatedFiltrationSpace Xnat (natTime n) := by
        exact le_iSup_of_le (natTime r) <| le_iSup_of_le hr' le_rfl
      simpa [Xnat, hnatIndex_natTime] using hcomap
  have hgenerated' :
      ∀ s : Iℕ, generatedFiltrationSpace Xnat s = generatedFiltrationSpace X (natIndex s) := by
    intro s
    calc
      generatedFiltrationSpace Xnat s = generatedFiltrationSpace Xnat (natTime (natIndex s)) := by
        rw [hnatTime_natIndex s]
      _ = generatedFiltrationSpace X (natIndex s) := hgenerated (natIndex s)
  have htransition : ∀ s : Iℕ, transitionKernel κnat s = transitionKernel κ (natIndex s) := by
    intro s
    ext y A hA
    rw [transitionKernel_apply, transitionKernel_apply]
    have hrow : κnat y = (κ y).map reindexPath := by
      simpa [κnat] using Kernel.map_apply κ hreindex_meas y
    rw [hrow]
    rw [Measure.map_map (μ := κ y) (f := reindexPath) (g := fun z : Iℕ → E ↦ z s)
      (measurable_pi_apply s) hreindex_meas]
    rfl
  letI : IsTimeHomogeneousMarkovProcess Xnat P κnat := by
    refine
      { measurable_process := fun s ↦ by simpa [Xnat] using hX_meas (natIndex s)
        initial_state := ?_
        path_law := ?_
        markov_property := ?_ }
    · intro y
      have hzero : natIndex (0 : Iℕ) = 0 := by
        have : (0 : Iℕ) = natTime 0 := by
          apply Subtype.ext
          simp [natTime]
        simpa [this] using hnatIndex_natTime 0
      simpa [Xnat, hzero] using hX0 y
    · intro y
      calc
        κnat y = ((κ y).map reindexPath) := by
              simpa [κnat] using Kernel.map_apply κ hreindex_meas y
        _ = (((P y : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω)).map reindexPath) := by
              rw [hpath y]
        _ = (P y : Measure Ω).map (fun ω : Ω ↦ fun s : Iℕ ↦ Xnat s ω) := by
              rw [Measure.map_map hreindex_meas hpathMap_meas]
              rfl
    · intro y A hA s u
      have hsum : Xnat (u + s) ⁻¹' A = X (natIndex u + natIndex s) ⁻¹' A := by
        ext ω
        simp [Xnat, hnatIndex_add]
      have hright :
          (fun ω ↦ ((transitionKernel κnat u) (Xnat s ω)).real A) =
            fun ω ↦ ((transitionKernel κ (natIndex u)) (X (natIndex s) ω)).real A := by
        funext ω
        rw [htransition u]
      simpa [hsum, hgenerated' s, hright] using
        ((inferInstance : IsTimeHomogeneousMarkovProcess X P κ).markov_property
          y hA (natIndex s) (natIndex u))
  have hordered :
      HasOrderedFutureCoordinateConditionalExpectationFormula Xnat P κnat :=
    hasOrderedFutureCoordinateConditionalExpectationFormula_of_isTimeHomogeneousMarkovProcess
      Xnat P κnat hsub
  have htnat : Monotone tnat := by
    intro i j hij
    exact hnatTime_le_iff.mpr (ht hij)
  have horderedNat :
      (P x : Measure Ω)[fun ω ↦ f (futurePathCoordinates Xnat (natTime k) tnat ω) |
          generatedFiltrationSpace Xnat (natTime k)] =ᵐ[(P x : Measure Ω)]
        fun ω ↦ ∫ y, f (fun i ↦ y (tnat i)) ∂κnat (Xnat (natTime k) ω) := by
    have hk_nonneg : 0 ≤ natTime k := by
      show (0 : NNReal) ≤ ((natTime k : Iℕ) : NNReal)
      exact zero_le _
    simpa using hordered hf_meas hf_bdd (t := tnat) htnat (natTime k) x hk_nonneg
  have hleft :
      (fun ω ↦ f (futurePathCoordinates Xnat (natTime k) tnat ω)) =
        fun ω ↦ f (shiftedFuturePathCoordinates X k t ω) := by
    funext ω
    congr 1
    funext i
    simp [futurePathCoordinates, shiftedFuturePathCoordinates, Xnat, tnat, natTime,
      hnatIndex_add, hnatIndex_natTime, add_comm]
  have hright :
      (fun ω ↦ ∫ y, f (fun i ↦ y (tnat i)) ∂κnat (Xnat (natTime k) ω)) =
        fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X k ω) := by
    funext ω
    have htuple_meas :
        Measurable (fun y : Iℕ → E ↦ f (fun i ↦ y (tnat i))) := by
      refine hf_meas.comp ?_
      refine measurable_pi_lambda _ fun i ↦ ?_
      exact measurable_pi_apply (tnat i)
    have hrow : κnat (Xnat (natTime k) ω) = (κ (X k ω)).map reindexPath := by
      rw [show Xnat (natTime k) ω = X k ω by simp [Xnat, hnatIndex_natTime]]
      simpa [κnat] using Kernel.map_apply κ hreindex_meas (X k ω)
    rw [hrow]
    rw [MeasureTheory.integral_map hreindex_meas.aemeasurable htuple_meas.aestronglyMeasurable]
    congr 1 with y
    congr 1
    funext i
    simp [reindexPath, tnat, hnatIndex_natTime]
  calc
    (P x : Measure Ω)[fun ω ↦ f (shiftedFuturePathCoordinates X k t ω) |
        generatedFiltrationSpace X k] =ᵐ[(P x : Measure Ω)]
          (P x : Measure Ω)[fun ω ↦ f (futurePathCoordinates Xnat (natTime k) tnat ω) |
            generatedFiltrationSpace Xnat (natTime k)] := by
              rw [hgenerated k]
              exact MeasureTheory.condExp_congr_ae (Filter.EventuallyEq.of_eq hleft.symm)
    _ =ᵐ[(P x : Measure Ω)] fun ω ↦ ∫ y, f (fun i ↦ y (tnat i)) ∂κnat (Xnat (natTime k) ω) :=
      horderedNat
    _ =ᵐ[(P x : Measure Ω)] fun ω ↦ ∫ y, f (fun i ↦ y (t i)) ∂κ (X k ω) :=
      Filter.EventuallyEq.of_eq hright

/-- Helper for Theorem 19.30: Theorem 17.9 gives the conditional law of every finite shifted
future restriction on a history event. -/
private theorem futurePathRestrictionIndicator_condExp
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (J : Finset ℕ) {A : Set (J → E)} (hA : MeasurableSet A) :
    ((P x : Measure Ω)[fun ω ↦ Set.indicator A (fun _ ↦ (1 : ℝ))
        (J.restrict (shiftedFuturePath X k ω)) | generatedFiltrationSpace X k]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ (((κ (X k ω)).map J.restrict).real A) := by
  let e : Fin J.card ≃ J := (J.orderIsoOfFin rfl).toEquiv
  let t : Fin J.card → ℕ := J.orderEmbOfFin rfl
  let A' : Set (Fin J.card → E) :=
    (fun z ↦ (MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e) z) ⁻¹' A
  have hA'_meas : MeasurableSet A' := by
    exact hA.preimage ((MeasurableEquiv.piCongrLeft (fun _ : J ↦ E) e).measurable)
  have hIndicator_meas :
      Measurable (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ)) := by
    exact Measurable.indicator measurable_const hA'_meas
  have hIndicator_bdd :
      Bornology.IsBounded (Set.range (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ))) := by
    simpa [A'] using isBounded_range_indicator_one A'
  have hFiniteIndicator :
      (P x : Measure Ω)[fun ω ↦ Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ))
          (shiftedFuturePathCoordinates X k t ω) | generatedFiltrationSpace X k] =ᵐ[
            (P x : Measure Ω)] fun ω ↦
              ∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i))
                ∂κ (X k ω) := by
    exact
      orderedFutureCoordinateCondExp_of_markovProcessNat
        (X := X) (P := P) (κ := κ) (hX_meas := hX_meas) (hX0 := hX0) (hpath := hpath)
        x k (Set.indicator A' fun _ : Fin J.card → E ↦ (1 : ℝ))
        hIndicator_meas hIndicator_bdd t
        (by simpa [t] using (J.orderEmbOfFin rfl).monotone)
  have hleft_fun :
      (fun ω ↦ Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ))
          (shiftedFuturePathCoordinates X k t ω)) =
        fun ω ↦ Set.indicator A (fun _ : J → E ↦ (1 : ℝ))
          (J.restrict (shiftedFuturePath X k ω)) := by
    simpa [e, t, A'] using
      shiftedFuturePathIndicator_eq_restrictIndicator (Y := X) (k := k) (J := J) (A := A)
  have hFiniteIndicator' :
      (P x : Measure Ω)[fun ω ↦ Set.indicator A (fun _ : J → E ↦ (1 : ℝ))
          (J.restrict (shiftedFuturePath X k ω)) | generatedFiltrationSpace X k] =ᵐ[
            (P x : Measure Ω)] fun ω ↦
              ∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i))
                ∂κ (X k ω) := by
    simpa [hleft_fun] using hFiniteIndicator
  filter_upwards [hFiniteIndicator'] with ω hω
  have hright :
      (∫ y, Set.indicator A' (fun _ : Fin J.card → E ↦ (1 : ℝ)) (fun i ↦ y (t i)) ∂κ (X k ω)) =
        (((κ (X k ω)).map J.restrict).real A) := by
    simpa [e, t, A'] using
      orderedTupleIndicatorIntegral_eq_mapRestrictReal (ν := κ (X k ω)) (J := J) hA
  simpa [hright] using hω

/-- Helper for Theorem 19.30: on each history event, the restricted shifted-future law agrees with
the path kernel mixed against the present-state law. -/
private theorem restrictedShiftedFuturePathLaw_eq_mixedPathLaw_on_history
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' {x}) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (n : ℕ) {B : Set Ω} (hB : MeasurableSet[generatedFiltrationSpace X n] B) :
    let μ : Measure Ω := (P x : Measure Ω)
    let νB : Measure (ℕ → E) := (μ.restrict B).map (shiftedFuturePath X n)
    let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict B).map (X n))
    νB = ρB := by
  let μ : Measure Ω := (P x : Measure Ω)
  let νB : Measure (ℕ → E) := (μ.restrict B).map (shiftedFuturePath X n)
  let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict B).map (X n))
  have hgenerated_le : generatedFiltrationSpace X n ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comapLocal X n]
    exact (measurable_pastPath X hX_meas n).comap_le
  have hPathMap_meas : Measurable (fun ω ↦ fun m : ℕ ↦ X m ω) := by
    refine measurable_pi_lambda _ fun m ↦ ?_
    simpa using hX_meas m
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  have hB_ambient : MeasurableSet B := hgenerated_le B hB
  have hJ :
      ∀ J : Finset ℕ, νB.map J.restrict = ρB.map J.restrict := by
    intro J
    let κJ : Kernel E (J → E) := κ.map J.restrict
    letI : IsMarkovKernel κJ := by
      let hmeasRestrict : Measurable (J.restrict : (ℕ → E) → J → E) :=
        Finset.measurable_restrict J
      refine ⟨fun y : E ↦ ?_⟩
      have hrow : κJ y = (κ y).map J.restrict := by
        simpa [κJ] using Kernel.map_apply κ hmeasRestrict y
      rw [hrow]
      simpa using Measure.isProbabilityMeasure_map (μ := κ y) hmeasRestrict.aemeasurable
    refine Measure.ext fun A hA ↦ ?_
    let futureEvent : Set Ω := (fun ω ↦ J.restrict (shiftedFuturePath X n ω)) ⁻¹' A
    have hfuture_meas : MeasurableSet futureEvent := by
      simpa [futureEvent] using
        ((Finset.measurable_restrict J).comp (measurable_shiftedFuturePath X hX_meas n)) hA
    have hIndicatorInt :
        Integrable (Set.indicator futureEvent (fun _ ↦ (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hfuture_meas
    have hmarkov :
        μ⟦futureEvent | generatedFiltrationSpace X n⟧ =ᵐ[μ]
          fun ω ↦ (((κ (X n ω)).map J.restrict).real A) := by
      simpa [futureEvent] using
        futurePathRestrictionIndicator_condExp X P κ hX_meas hX0 hpath x n J hA
    have hleft_real :
        (((νB.map J.restrict).real A)) = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
      have hmass :
          μ.real (B ∩ futureEvent) =
            ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
        calc
          μ.real (B ∩ futureEvent)
              = ∫ ω in B, (μ⟦futureEvent | generatedFiltrationSpace X n⟧) ω ∂μ := by
                  rw [MeasureTheory.setIntegral_condExp hgenerated_le hIndicatorInt hB,
                    ← MeasureTheory.integral_indicator hB_ambient]
                  simpa [futureEvent, Set.indicator_indicator, Set.inter_assoc,
                    Set.inter_left_comm, Set.inter_comm, smul_eq_mul] using
                    (MeasureTheory.integral_indicator_const (μ := μ) (1 : ℝ)
                      (hB_ambient.inter hfuture_meas)).symm
          _ = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
                exact MeasureTheory.integral_congr_ae hmarkov.restrict
      have hmapJ :
          νB.map J.restrict = (μ.restrict B).map (fun ω ↦ J.restrict (shiftedFuturePath X n ω)) := by
        dsimp [νB]
        rw [AEMeasurable.map_map_of_aemeasurable (Finset.measurable_restrict J).aemeasurable]
        · rfl
        · exact (measurable_shiftedFuturePath X hX_meas n).aemeasurable
      calc
        (((νB.map J.restrict).real A))
            = ((((μ.restrict B).map (fun ω ↦ J.restrict (shiftedFuturePath X n ω))).real A)) := by
                rw [hmapJ]
        _ = (μ.restrict B).real futureEvent := by
              simpa [futureEvent] using
                (MeasureTheory.map_measureReal_apply
                  (μ := (μ.restrict B)) (f := fun ω ↦ J.restrict (shiftedFuturePath X n ω))
                  ((Finset.measurable_restrict J).comp (measurable_shiftedFuturePath X hX_meas n)) hA)
        _ = μ.real (futureEvent ∩ B) := by
              simpa [futureEvent] using
                (MeasureTheory.measureReal_restrict_apply (μ := μ) (s := B) (t := futureEvent)
                  hfuture_meas)
        _ = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
              simpa [Set.inter_comm] using hmass
    have hright_real :
        (((ρB.map J.restrict).real A)) = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
      let κJ : Kernel E (J → E) := κ.map J.restrict
      have hmap :
          ρB.map J.restrict = κJ ∘ₘ ((μ.restrict B).map (X n)) := by
        dsimp [ρB, κJ]
        simpa using Measure.map_comp (((μ.restrict B).map (X n))) κ (Finset.measurable_restrict J)
      haveI : IsMarkovKernel κJ := by
        let hmeasRestrict : Measurable (J.restrict : (ℕ → E) → J → E) :=
          Finset.measurable_restrict J
        refine ⟨fun y : E ↦ ?_⟩
        have hrow : κJ y = (κ y).map J.restrict := by
          simpa [κJ] using Kernel.map_apply κ hmeasRestrict y
        rw [hrow]
        simpa using Measure.isProbabilityMeasure_map (μ := κ y) hmeasRestrict.aemeasurable
      rw [hmap]
      calc
        ((κJ ∘ₘ ((μ.restrict B).map (X n))).real A)
            = ∫ ω in B, (κJ (X n ω)).real A ∂μ := by
                simpa [κJ] using
                  (kernelCompRestrictMapRealEqSetIntegral
                    (κ := κ.map J.restrict) (μ := μ) (Y := X n) (hY := hX_meas n)
                    (B := B) hB_ambient (A := A) hA)
        _ = ∫ ω in B, (((κ (X n ω)).map J.restrict).real A) ∂μ := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              have hrow : κJ (X n ω) = (κ (X n ω)).map J.restrict := by
                simpa [κJ] using Kernel.map_apply κ (Finset.measurable_restrict J) (X n ω)
              exact congrArg (fun ν : Measure (J → E) ↦ ν.real A) hrow
    have hleft_ne_top : (νB.map J.restrict) A ≠ ⊤ := by
      simpa using measure_lt_top (νB.map J.restrict) A
    have hright_ne_top : (ρB.map J.restrict) A ≠ ⊤ := by
      simpa using measure_lt_top (ρB.map J.restrict) A
    exact
      (MeasureTheory.measureReal_eq_measureReal_iff
        (μ := νB.map J.restrict) (ν := ρB.map J.restrict)
        (s := A) (t := A) hleft_ne_top hright_ne_top).mp
        (hleft_real.trans hright_real.symm)
  have hν :
      MeasureTheory.IsProjectiveLimit νB (fun J : Finset ℕ ↦ νB.map J.restrict) := by
    simpa [νB] using natPathMeasure_isProjectiveLimit_restrictions νB
  have hρ :
      MeasureTheory.IsProjectiveLimit ρB (fun J : Finset ℕ ↦ ρB.map J.restrict) := by
    simpa [ρB] using natPathMeasure_isProjectiveLimit_restrictions ρB
  have hρ' :
      MeasureTheory.IsProjectiveLimit ρB (fun J : Finset ℕ ↦ νB.map J.restrict) := by
    intro J
    exact (hJ J).symm
  haveI : ∀ J : Finset ℕ, IsFiniteMeasure (νB.map J.restrict) := fun _ ↦ inferInstance
  exact MeasureTheory.IsProjectiveLimit.unique hν hρ'


/-- Helper for Theorem 19.30: the canonical path-law kernel attached to the realization `(P, X)`.
Because the state space `E` is discrete, the kernel measurability is automatic. -/
private def realizationPathKernel
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E} :
    Kernel E (ℕ → E) where
  toFun := fun z ↦ (P z : Measure Ω).map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω)
  measurable' := Measurable.of_discrete

/-- Helper for Theorem 19.30: each row of the theorem-local path kernel is the pushforward of
`P z` along the full realized trajectory. -/
@[simp] private theorem realizationPathKernel_apply
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    (z : E) :
    realizationPathKernel (P := P) (X := X) z =
      (P z : Measure Ω).map (fun ω : Ω ↦ fun n : ℕ ↦ X n ω) :=
  rfl

/-- Helper for Theorem 19.30: the time-`n` marginal of the theorem-local path kernel is the
`n`-step transition row of the realized walk. -/
private theorem realizationPathKernel_transition
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) (n : ℕ) :
    transitionKernel (realizationPathKernel (P := P) (X := X)) n x =
      (discreteMatrixKernel p ^ n) x := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  -- Proof comment: expand the explicit path kernel and read off its time-`n` marginal from the
  -- stored realization transition law.
  rw [transitionKernel_apply]
  change
    Measure.map (fun ξ : ℕ → E ↦ ξ n)
      ((P x : Measure Ω).map (fun ω : Ω ↦ fun m : ℕ ↦ X m ω)) =
        (discreteMatrixKernel p ^ n) x
  rw [Measure.map_map]
  · simpa using hReal.transition_eq x n
  · exact measurable_pi_apply n
  · exact measurable_pi_lambda _ fun m ↦ hReal.measurable_process m


/-- Helper for Theorem 19.30: under `P x`, the time-`0` law of the realization is concentrated at
the start state `x`. -/
private theorem initialState_prob_eq_one_local
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    (hReal : IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X)
    (x : E) :
    (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1 := by
  -- Proof comment: this is the singleton evaluation of the realization field `initial_eq`.
  have hInit := congrArg (fun ν : Measure E ↦ ν ({x} : Set E)) (hReal.initial_eq x)
  simpa [Measure.map_apply (hReal.measurable_process 0) (measurableSet_singleton x)] using hInit

/-- Helper for Theorem 19.30: under `P x`, the realized chain starts from `x` almost surely. -/
private theorem initialState_ae_eq_start_local
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) :
    ∀ᵐ ω ∂(P x : Measure Ω), X 0 ω = x := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hprob : (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1 := by
    exact initialState_prob_eq_one_local (hReal := hReal) x
  have hmeas : MeasurableSet (X 0 ⁻¹' ({x} : Set E)) := by
    simpa using (hReal.measurable_process 0) (measurableSet_singleton x)
  exact (mem_ae_iff_prob_eq_one hmeas).2 hprob

/-- Helper for Theorem 19.30: the theorem-local path kernel is the actual path law of the given
realization, so it upgrades the realization to a discrete-time time-homogeneous Markov process on
path space. -/
private theorem realizationPathKernel_isTimeHomogeneousMarkovProcess
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X] :
    IsTimeHomogeneousMarkovProcess X P (realizationPathKernel (P := P) (X := X)) := by
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  refine
    { measurable_process := hReal.measurable_process
      initial_state := ?_
      path_law := ?_
      markov_property := ?_ }
  · intro z
    -- Proof comment: the `time = 0` marginal of the realization is already the Dirac mass at
    -- the starting state, so the path-kernel owner inherits the usual initial-state law.
    exact initialState_prob_eq_one_local (hReal := hReal) z
  · intro z
    -- Proof comment: by construction, each row of `realizationPathKernel` is the pushforward of
    -- `P z` along the full realized trajectory.
    exact realizationPathKernel_apply (P := P) (X := X) z
  · intro z B hB s t
    -- Proof comment: the source Markov property already gives the conditional law of `X (t + s)`;
    -- the only bridge needed here is that the induced time-`t` marginal of the path kernel is the
    -- same state kernel `(discreteMatrixKernel p ^ t)`.
    filter_upwards [hReal.markov_property z hB s t] with ω hω
    have htransition :
        ((discreteMatrixKernel p ^ t) (X s ω)).real B =
          ((transitionKernel (realizationPathKernel (P := P) (X := X)) t) (X s ω)).real B := by
      simpa using
        congrArg (fun ν : Measure E ↦ ν.real B)
          (realizationPathKernel_transition (p := p) (P := P) (X := X) (X s ω) t).symm
    exact hω.trans htransition

/-- Helper for Theorem 19.30: finite prefix avoidance of a boundary set is measurable on path
space. -/
private theorem avoidBeforePathEvent_measurable
    (B : Set E) :
    ∀ n : ℕ, MeasurableSet {ξ : ℕ → E | ∀ m < n, ξ m ∉ B}
  | 0 => by
      simp
  | n + 1 => by
      have hEq :
          {ξ : ℕ → E | ∀ m < n + 1, ξ m ∉ B} =
            {ξ : ℕ → E | ∀ m < n, ξ m ∉ B} ∩ {ξ : ℕ → E | ξ n ∉ B} := by
        ext ξ
        constructor
        · intro hξ
          refine ⟨?_, ?_⟩
          · intro m hm
            exact hξ m (Nat.lt_succ_of_lt hm)
          · exact hξ n (Nat.lt_succ_self n)
        · intro hξ m hm
          rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
          · exact hξ.1 m hm
          · exact hξ.2
      -- Proof comment: split the length-`n + 1` avoidance condition into the length-`n` prefix
      -- avoidance and the one-coordinate constraint at time `n`.
      rw [hEq]
      refine (avoidBeforePathEvent_measurable B n).inter ?_
      change MeasurableSet (((fun ξ : ℕ → E ↦ ξ n) ⁻¹' Bᶜ))
      exact
        (measurable_pi_apply n)
          (by simpa using (MeasurableSet.of_discrete : MeasurableSet B))

/-- Helper for Theorem 19.30: on path space, the sink-hit event is the explicit first-entrance
event "avoid `insert x A` before time `n` and hit `A` at time `n`". -/
private def collapsedBoundaryHitPathEvent
    (x : E) (A : Set E) : Set (ℕ → E) :=
  {ξ | ∃ n : ℕ, ξ n ∈ A ∧ ∀ m < n, ξ m ∉ insert x A}

/-- Helper for Theorem 19.30: the path-space first-entrance description of the collapsed sink-hit
event is measurable. -/
private theorem collapsedBoundaryHitPathEvent_measurable
    (x : E) (A : Set E) :
    MeasurableSet (collapsedBoundaryHitPathEvent x A) := by
  have hEq :
      collapsedBoundaryHitPathEvent x A =
        ⋃ n : ℕ, ({ξ : ℕ → E | ξ n ∈ A} ∩ {ξ : ℕ → E | ∀ m < n, ξ m ∉ insert x A}) := by
    ext ξ
    simp [collapsedBoundaryHitPathEvent, and_left_comm, and_assoc]
  rw [hEq]
  refine MeasurableSet.iUnion fun n ↦ ?_
  refine ((measurable_pi_apply n) ?_).inter ?_
  · simpa using (MeasurableSet.of_discrete : MeasurableSet A)
  · exact avoidBeforePathEvent_measurable (insert x A) n

/-- Helper for Theorem 19.30: hitting `insert x A` from time `0` and stopping in `A` is
equivalent to an explicit first-entrance witness into `A` while avoiding `insert x A` earlier. -/
private theorem collapsedBoundaryHitEvent_iff_exists
    {Ω' : Type*} [MeasurableSpace Ω'] (u : ℕ → Ω' → E)
    (x : E) (A : Set E) (ω : Ω') :
    (hittingAfter u (insert x A) 0 ω < ⊤ ∧
        stoppedValue u (hittingAfter u (insert x A) 0) ω ∈ A) ↔
      ∃ n : ℕ, u n ω ∈ A ∧ ∀ m < n, u m ω ∉ insert x A := by
  let s : Set E := insert x A
  constructor
  · rintro ⟨hfin, hstop⟩
    have hne_top : hittingAfter u s 0 ω ≠ ⊤ := ne_of_lt hfin
    lift hittingAfter u s 0 ω to ℕ using hne_top with n hn
    have hidx : (hittingAfter u s 0 ω).untopA = n := by
      rw [← hn, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have hnA : u n ω ∈ A := by
      -- Proof comment: after identifying the finite hitting time with `n`, the stopped-value
      -- condition is exactly the claim that the hit lands in `A`.
      change stoppedValue u (hittingAfter u s 0) ω ∈ A at hstop
      rw [stoppedValue, hidx] at hstop
      exact hstop
    refine ⟨n, hnA, ?_⟩
    intro m hm
    have hm_lt_hit : (m : ℕ∞) < hittingAfter u s 0 ω := by
      have hm_top : (m : ℕ∞) < (n : ℕ∞) := by
        simpa using hm
      rw [← hn]
      exact hm_top
    -- Proof comment: every time strictly before the first hit must stay outside `insert x A`.
    exact
      notMem_of_lt_hittingAfter (u := u) (s := s) (n := 0) (ω := ω) (k := m) hm_lt_hit
        (by simp)
  · rintro ⟨n, hnA, havoid⟩
    have hhit_le_n :
        hittingAfter u s 0 ω ≤ n :=
      hittingAfter_le_of_mem (u := u) (s := s) (n := 0) (i := n) (ω := ω) (by simp) <| by
        simp [s, hnA]
    have hne_top : hittingAfter u s 0 ω ≠ ⊤ := by
      intro htop
      simpa [htop] using hhit_le_n
    lift hittingAfter u s 0 ω to ℕ using hne_top with t ht
    have hidx : (hittingAfter u s 0 ω).untopA = t := by
      rw [← ht, WithTop.untopA_eq_untop (by simp)]
      exact (WithTop.untop_eq_iff (by simp)).2 rfl
    have htn : t ≤ n := by
      simpa using hhit_le_n
    have hne_top0 : hittingAfter u s 0 ω ≠ ⊤ := by
      intro htop
      have ht_top : (t : ℕ∞) = ⊤ := by
        exact ht.trans htop
      simpa using ht_top
    have ht_mem : u t ω ∈ s := by
      simpa [hidx] using
        hittingAfter_mem_set_of_ne_top (u := u) (s := s) (n := 0) (ω := ω) hne_top0
    have hnot_lt : ¬ t < n := by
      intro hlt
      exact (havoid t hlt) ht_mem
    have htn_eq : t = n := le_antisymm htn (not_lt.mp hnot_lt)
    have hltop : hittingAfter u s 0 ω < ⊤ := lt_top_iff_ne_top.mpr hne_top0
    refine ⟨hltop, ?_⟩
    -- Proof comment: the first hit cannot occur before the witness time `n`, so the stopped value
    -- is exactly `u n`, which already lies in `A`.
    change stoppedValue u (hittingAfter u s 0) ω ∈ A
    rw [stoppedValue, hidx, htn_eq]
    exact hnA

/-- Helper for Theorem 19.30: evaluating the coordinate path of `u` on the path-space hit event
recovers the original collapsed boundary-hit event. -/
private theorem path_mem_collapsedBoundaryHitPathEvent_iff
    {Ω' : Type*} [MeasurableSpace Ω'] (u : ℕ → Ω' → E)
    (x : E) (A : Set E) (ω : Ω') :
    (fun n : ℕ ↦ u n ω) ∈ collapsedBoundaryHitPathEvent x A ↔
      ω ∈ collapsedBoundaryHitEvent u x A := by
  simpa [collapsedBoundaryHitPathEvent, Set.mem_setOf_eq] using
    (collapsedBoundaryHitEvent_iff_exists u x A ω).symm

/-- Helper for Theorem 19.30: if the start state is already outside `insert x A`, then the
collapsed sink-hit event is exactly the shifted path-space hit event after one step. -/
private theorem shiftedFuturePath_mem_collapsedBoundaryHitPathEvent_iff
    {Ω' : Type*} [MeasurableSpace Ω'] (u : ℕ → Ω' → E)
    (x : E) (A : Set E) {ω : Ω'}
    (hstart : u 0 ω ∉ insert x A) :
    shiftedFuturePath u 1 ω ∈ collapsedBoundaryHitPathEvent x A ↔
      ω ∈ collapsedBoundaryHitEvent u x A := by
  rw [show ω ∈ collapsedBoundaryHitEvent u x A ↔
      ∃ n : ℕ, u n ω ∈ A ∧ ∀ m < n, u m ω ∉ insert x A from
        collapsedBoundaryHitEvent_iff_exists u x A ω]
  constructor
  · rintro ⟨n, hnA, havoid⟩
    refine ⟨n + 1, ?_, ?_⟩
    · simpa [shiftedFuturePath, Nat.add_comm] using hnA
    · intro m hm
      cases m with
      | zero =>
          simpa using hstart
      | succ m =>
          have hm_lt : m < n := by
            simpa using hm
          simpa [shiftedFuturePath, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using havoid m hm_lt
  · rintro ⟨n, hnA, havoid⟩
    have hn_ne_zero : n ≠ 0 := by
      intro hn0
      exact hstart <| by simpa [hn0] using Or.inr hnA
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn_ne_zero
    refine ⟨k, ?_, ?_⟩
    · simpa [shiftedFuturePath, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hnA
    · intro m hm
      have hm' : m + 1 < k + 1 := Nat.succ_lt_succ hm
      simpa [shiftedFuturePath, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using havoid (m + 1) hm'

/-- Helper for Theorem 19.30: if the shifted path hits the collapsed sink event, then the
original trajectory reaches `A` at a positive time before any positive-time return to `x`. -/
private theorem shiftedFuturePath_mem_collapsedBoundaryHitPathEvent_imp_escapeEvent
    {Ω' : Type*} [MeasurableSpace Ω'] (u : ℕ → Ω' → E)
    (x : E) (A : Set E) (hxA : x ∉ A) (ω : Ω') :
    shiftedFuturePath u 1 ω ∈ collapsedBoundaryHitPathEvent x A →
      ∃ n : ℕ, 0 < n ∧ u n ω ∈ A ∧
        ∀ m : ℕ, 0 < m → m ≤ n → u m ω ≠ x := by
  intro hω
  rcases hω with ⟨n, hnA, havoid⟩
  refine ⟨n + 1, Nat.succ_pos _, ?_, ?_⟩
  · simpa [shiftedFuturePath, Nat.add_comm] using hnA
  · intro m hm_pos hm_le
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm_pos)
    intro hmx
    by_cases hk : k = n
    · subst hk
      have hx_mem : x ∈ A := by
        simpa [shiftedFuturePath, Nat.add_comm, hmx] using hnA
      exact hxA hx_mem
    · have hk_lt : k < n := lt_of_le_of_ne (by simpa using hm_le) hk
      have hnot_mem := havoid k hk_lt
      exact hnot_mem <| by simp [shiftedFuturePath, hmx]

/-- Helper for Theorem 19.30: the voltage on the sink-collapsed carrier is the boundary-hit
probability of `A` before the first hit of `x`, with the sink normalized to `1`. -/
private def collapsedBoundaryVoltage
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    (x : E) (A : Set E) :
    ({y : E // y ∉ A} ⊕ Unit) → ℝ
  | Sum.inl y => ((P y.1 : Measure Ω).real (collapsedBoundaryHitEvent X x A))
  | Sum.inr _ => 1

/-- Helper for Theorem 19.30: extend the collapsed boundary voltage back to the ambient state
space by fixing value `0` at `x` and value `1` on the target `A`. -/
private def collapsedBoundaryVoltageAmbient
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    (x : E) (A : Set E) : E → ℝ :=
  fun y ↦
    if y = x then 0 else if y ∈ A then 1 else
      ((P y : Measure Ω).real (collapsedBoundaryHitEvent X x A))

/-- Helper for Theorem 19.30: the collapsed boundary-hit event is measurable because it is the
preimage of the measurable path-space event under the realized full-path map. -/
private theorem collapsedBoundaryHitEvent_measurable
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) (A : Set E) :
    MeasurableSet (collapsedBoundaryHitEvent X x A) := by
  let path : Ω → ℕ → E := fun ω n ↦ X n ω
  have hpath_meas : Measurable path := by
    -- Proof comment: the full realized path is measurable coordinatewise.
    refine measurable_pi_lambda _ fun n ↦ ?_
    exact
      (inferInstance : IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process n
  have hpre :
      path ⁻¹' collapsedBoundaryHitPathEvent x A = collapsedBoundaryHitEvent X x A := by
    ext ω
    simpa [path, Set.mem_setOf_eq] using
      (path_mem_collapsedBoundaryHitPathEvent_iff (u := X) x A ω)
  rw [← hpre]
  exact (collapsedBoundaryHitPathEvent_measurable x A).preimage hpath_meas

/-- Helper for Theorem 19.30: the collapsed sink carries unit voltage by definition. -/
@[simp] private theorem collapsedBoundaryVoltage_sink
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    (x : E) (A : Set E) :
    collapsedBoundaryVoltage (P := P) (X := X) x A (Sum.inr ()) = 1 := by
  -- Proof comment: the sink value is the normalization built into the owner definition.
  rfl

/-- Helper for Theorem 19.30: the visible start vertex has voltage `0` because the time-`0`
boundary hit of `insert x A` is already at `x`, never in `A`. -/
private theorem collapsedBoundaryVoltage_start
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) (A : Set E) (hxA : x ∉ A) :
    collapsedBoundaryVoltage (P := P) (X := X) x A (Sum.inl ⟨x, hxA⟩) = 0 := by
  -- Proof comment: starting at `x` makes the first hit of `insert x A` occur immediately at
  -- `x`, so the sink-side event is empty.
  let μ : Measure Ω := (P x : Measure Ω)
  have hstart_meas : MeasurableSet {ω | X 0 ω = x} := by
    simpa [Set.preimage] using
      ((inferInstance : IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process 0)
        (measurableSet_singleton x)
  have hstart_one : μ {ω | X 0 ω = x} = 1 := by
    have hmap : μ.map (X 0) = Measure.dirac x := by
      simpa [μ] using
        (inferInstance : IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).initial_eq x
    calc
      μ {ω | X 0 ω = x} = (μ.map (X 0)) ({x} : Set E) := by
        symm
        simpa [Set.preimage] using
          (Measure.map_apply
            ((inferInstance : IsMarkovProcessRealization
              (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process 0)
            (measurableSet_singleton x))
      _ = 1 := by simp [hmap]
  have hstart : ∀ᵐ ω ∂μ, X 0 ω = x :=
    (mem_ae_iff_prob_eq_one hstart_meas).2 hstart_one
  have hzero :
      μ (collapsedBoundaryHitEvent X x A) = 0 := by
    have hEventAE : collapsedBoundaryHitEvent X x A =ᵐ[μ] (∅ : Set Ω) := by
      filter_upwards [hstart] with ω hω
      apply propext
      constructor
      · intro hωEvent
        have hτ0 :
            hittingAfter X (insert x A) 0 ω = 0 := by
          refine le_antisymm ?_ (le_hittingAfter (u := X) (s := insert x A) (n := 0) ω)
          exact hittingAfter_le_of_mem (u := X) (s := insert x A) (n := 0) (ω := ω)
            (by simp) (by left; exact hω)
        have hstop : stoppedValue X (hittingAfter X (insert x A) 0) ω = x := by
          simpa [stoppedValue, hτ0] using hω
        have hx_mem_A : x ∈ A := by
          simpa [collapsedBoundaryHitEvent, hstop] using hωEvent.2
        exact (hxA hx_mem_A).elim
      · intro hωFalse
        exact False.elim hωFalse
    rw [measure_congr hEventAE]
    simp
  -- Proof comment: the visible start value is the real measure of that empty sink-hit event.
  simp [collapsedBoundaryVoltage, Measure.real_def, μ, hzero]

/-- Helper for Theorem 19.30: away from `insert x A`, the ambient voltage equals the shifted
path-space hit indicator integrated under the start law `P y`. -/
private theorem collapsedBoundaryVoltageAmbient_eq_shiftedIndicatorIntegral
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) (A : Set E) {y : E} (hy : y ∉ insert x A) :
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y =
      ∫ ω,
        Set.indicator (collapsedBoundaryHitPathEvent x A) (fun _ ↦ (1 : ℝ))
          (shiftedFuturePath X 1 ω) ∂(P y : Measure Ω) := by
  let μ : Measure Ω := (P y : Measure Ω)
  have hyx : y ≠ x := by
    intro hy'
    exact hy (Or.inl hy')
  have hyA : y ∉ A := by
    intro hy'
    exact hy (Or.inr hy')
  have hEventMeas : MeasurableSet (collapsedBoundaryHitEvent X x A) :=
    collapsedBoundaryHitEvent_measurable (p := p) (P := P) (X := X) x A
  have hstart_ae : ∀ᵐ ω ∂μ, X 0 ω ∉ insert x A := by
    filter_upwards [initialState_ae_eq_start_local (p := p) (P := P) (X := X) y] with ω hω
    simpa [hω] using hy
  have hIndicatorAE :
      (fun ω ↦
        Set.indicator (collapsedBoundaryHitPathEvent x A) (fun _ ↦ (1 : ℝ))
          (shiftedFuturePath X 1 ω)) =ᵐ[μ]
        fun ω ↦ Set.indicator (collapsedBoundaryHitEvent X x A) (fun _ ↦ (1 : ℝ)) ω := by
    filter_upwards [hstart_ae] with ω hω
    have hiff :
        shiftedFuturePath X 1 ω ∈ collapsedBoundaryHitPathEvent x A ↔
          ω ∈ collapsedBoundaryHitEvent X x A :=
      shiftedFuturePath_mem_collapsedBoundaryHitPathEvent_iff (u := X) x A hω
    by_cases hEvent : ω ∈ collapsedBoundaryHitEvent X x A
    · have hmem : shiftedFuturePath X 1 ω ∈ collapsedBoundaryHitPathEvent x A := hiff.mpr hEvent
      simp [Set.indicator, hEvent, hmem]
    · have hmem : shiftedFuturePath X 1 ω ∉ collapsedBoundaryHitPathEvent x A := by
        intro hmem
        exact hEvent (hiff.mp hmem)
      simp [Set.indicator, hEvent, hmem]
  calc
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y
        = μ.real (collapsedBoundaryHitEvent X x A) := by
            simp [collapsedBoundaryVoltageAmbient, hyx, hyA, μ]
    _ = ∫ ω,
          Set.indicator (collapsedBoundaryHitEvent X x A) (fun _ ↦ (1 : ℝ)) ω ∂μ := by
            symm
            exact MeasureTheory.integral_indicator_one (μ := μ) (s := collapsedBoundaryHitEvent X x A)
              hEventMeas
    _ = ∫ ω,
          Set.indicator (collapsedBoundaryHitPathEvent x A) (fun _ ↦ (1 : ℝ))
            (shiftedFuturePath X 1 ω) ∂μ := by
              symm
              exact MeasureTheory.integral_congr_ae hIndicatorAE

/-- Helper for Theorem 19.30: integrating the path-space boundary-hit indicator against the
realized path law started from `z` recovers the ambient boundary voltage at `z`. -/
private theorem collapsedBoundaryVoltageAmbient_eq_pathIntegral
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} (hxA : x ∉ A) (z : E) :
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z =
      ∫ ξ,
        Set.indicator (collapsedBoundaryHitPathEvent x A) (fun _ ↦ (1 : ℝ)) ξ
          ∂realizationPathKernel (P := P) (X := X) z := by
  let κ := realizationPathKernel (P := P) (X := X)
  let pathMap : Ω → ℕ → E := fun ω n ↦ X n ω
  have hPathMeas : Measurable pathMap := by
    -- Proof comment: the full realized trajectory is measurable coordinatewise.
    refine measurable_pi_lambda _ fun n ↦ ?_
    exact
      (inferInstance : IsMarkovProcessRealization
        (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process n
  have hEventMeas :
      MeasurableSet (collapsedBoundaryHitEvent X x A) :=
    collapsedBoundaryHitEvent_measurable (p := p) (P := P) (X := X) x A
  have hPathEventMeas :
      MeasurableSet (collapsedBoundaryHitPathEvent x A) :=
    collapsedBoundaryHitPathEvent_measurable x A
  have hPathReal :
      ((κ z).real (collapsedBoundaryHitPathEvent x A)) =
        ((P z : Measure Ω).real (collapsedBoundaryHitEvent X x A)) := by
    -- Proof comment: the theorem-local path kernel is exactly the pushforward of `P z` along the
    -- full realized trajectory, and the path event pulls back to the original boundary-hit event.
    rw [realizationPathKernel_apply]
    calc
      (((P z : Measure Ω).map pathMap).real (collapsedBoundaryHitPathEvent x A))
          = (P z : Measure Ω).real (pathMap ⁻¹' collapsedBoundaryHitPathEvent x A) := by
              exact
                MeasureTheory.map_measureReal_apply
                  (μ := (P z : Measure Ω)) (f := pathMap) hPathMeas hPathEventMeas
      _ = (P z : Measure Ω).real (collapsedBoundaryHitEvent X x A) := by
            congr 1
            ext ω
            simpa [pathMap, Set.mem_setOf_eq] using
              (path_mem_collapsedBoundaryHitPathEvent_iff (u := X) x A ω)
  have hIntegralReal :
      ∫ ξ,
          Set.indicator (collapsedBoundaryHitPathEvent x A) (fun _ ↦ (1 : ℝ)) ξ
            ∂κ z =
        ((κ z).real (collapsedBoundaryHitPathEvent x A)) := by
    -- Proof comment: the indicator integral of a measurable path event is its real-valued
    -- probability under the chosen path law.
    exact
      MeasureTheory.integral_indicator_one
        (μ := κ z) (s := collapsedBoundaryHitPathEvent x A) hPathEventMeas
  by_cases hzx : z = x
  · subst z
    -- Proof comment: starting from `x`, the boundary-hit event has probability `0`, matching the
    -- prescribed ambient boundary value at the start vertex.
    calc
      collapsedBoundaryVoltageAmbient (P := P) (X := X) x A x = 0 := by
        simp [collapsedBoundaryVoltageAmbient]
      _ = collapsedBoundaryVoltage (P := P) (X := X) x A (Sum.inl ⟨x, hxA⟩) := by
        symm
        simpa using collapsedBoundaryVoltage_start (p := p) (P := P) (X := X) x A hxA
      _ = ((P x : Measure Ω).real (collapsedBoundaryHitEvent X x A)) := by
        rfl
      _ = ((κ x).real (collapsedBoundaryHitPathEvent x A)) := by
        symm
        exact hPathReal
      _ = ∫ ξ,
            Set.indicator (collapsedBoundaryHitPathEvent x A) (fun _ ↦ (1 : ℝ)) ξ
              ∂κ x := by
                symm
                exact hIntegralReal
  · by_cases hzA : z ∈ A
    · have hEventAE : ∀ᵐ ω ∂(P z : Measure Ω), ω ∈ collapsedBoundaryHitEvent X x A := by
        filter_upwards [initialState_ae_eq_start_local (p := p) (P := P) (X := X) z] with ω hω
        exact
          (collapsedBoundaryHitEvent_iff_exists (u := X) x A ω).2 <|
            ⟨0, by simpa [hω] using hzA, by
              intro m hm
              exact (Nat.not_lt_zero _ hm).elim⟩
      have hEventProb :
          (P z : Measure Ω) (collapsedBoundaryHitEvent X x A) = 1 :=
        (mem_ae_iff_prob_eq_one hEventMeas).1 hEventAE
      -- Proof comment: if the realized trajectory already starts in `A`, then the path event
      -- occurs immediately at time `0`, so its probability is `1`.
      calc
        collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z = 1 := by
          simp [collapsedBoundaryVoltageAmbient, hzx, hzA]
        _ = ((P z : Measure Ω).real (collapsedBoundaryHitEvent X x A)) := by
            simp [Measure.real_def, hEventProb]
        _ = ((κ z).real (collapsedBoundaryHitPathEvent x A)) := by
            symm
            exact hPathReal
        _ = ∫ ξ,
              Set.indicator (collapsedBoundaryHitPathEvent x A) (fun _ ↦ (1 : ℝ)) ξ
                ∂κ z := by
                  symm
                  exact hIntegralReal
    · -- Proof comment: away from the boundary, the ambient extension is defined by the real mass
      -- of the original boundary-hit event, so only the path-law rewrite remains.
      calc
        collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z =
            ((P z : Measure Ω).real (collapsedBoundaryHitEvent X x A)) := by
              simp [collapsedBoundaryVoltageAmbient, hzx, hzA]
        _ = ((κ z).real (collapsedBoundaryHitPathEvent x A)) := by
            symm
            exact hPathReal
        _ = ∫ ξ,
              Set.indicator (collapsedBoundaryHitPathEvent x A) (fun _ ↦ (1 : ℝ)) ξ
                ∂κ z := by
                  symm
                  exact hIntegralReal

/-- Helper for Theorem 19.30: away from the boundary `insert x A`, the ambient voltage and the
visible collapsed voltage are the same quantity. -/
private theorem collapsedBoundaryVoltageAmbient_eq_visible
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    (x : E) {A : Set E} (y : {z : E // z ∉ A}) (hyx : y.1 ≠ x) :
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y.1 =
      collapsedBoundaryVoltage (P := P) (X := X) x A (Sum.inl y) := by
  -- Proof comment: on visible interior vertices, both owners are defined by the same boundary-hit
  -- probability; only the boundary cases `x` and `A` were separated in the ambient extension.
  simp [collapsedBoundaryVoltageAmbient, collapsedBoundaryVoltage, hyx, y.2]

/-- Helper for Theorem 19.30: the ambient boundary voltage is always bounded by `1` in absolute
value. -/
private theorem collapsedBoundaryVoltageAmbient_norm_le_one
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    (x : E) (A : Set E) (z : E) :
    ‖collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z‖ ≤ 1 := by
  -- Proof comment: the ambient extension only takes the boundary values `0` and `1`, or the real
  -- mass of a measurable event under a probability measure.
  by_cases hzx : z = x
  · simp [collapsedBoundaryVoltageAmbient, hzx]
  · by_cases hzA : z ∈ A
    · simp [collapsedBoundaryVoltageAmbient, hzx, hzA]
    · have hprob_le :
        ((P z : Measure Ω).real (collapsedBoundaryHitEvent X x A)) ≤ 1 := by
        exact
          MeasureTheory.measureReal_le_one
            (μ := (P z : Measure Ω)) (s := collapsedBoundaryHitEvent X x A)
      have hprob_nonneg :
          0 ≤ ((P z : Measure Ω).real (collapsedBoundaryHitEvent X x A)) :=
        ENNReal.toReal_nonneg
      rw [collapsedBoundaryVoltageAmbient, if_neg hzx, if_neg hzA,
        Real.norm_of_nonneg hprob_nonneg]
      exact hprob_le

/-- Helper for Theorem 19.30: every conductance row is nonzero for a random walk with weights. -/
private theorem conductance_ne_zero_of_randomWalk
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    [IsRandomWalkWithWeights p C] (x : E) :
    conductance C x ≠ 0 := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  intro hx0
  have hC0 : ∀ z : E, C x z = 0 := by
    intro z
    exact (ENNReal.tsum_eq_zero.mp hx0) z
  have hp0 : ∀ z : E, p x z = 0 := by
    intro z
    rw [hWalk.transition_eq, hC0 z]
    simp
  have hsum0 : ∑' z : E, p x z = 0 := by
    simp [hp0]
  have hstoch := hWalk.isStochastic x
  rw [hsum0] at hstoch
  simp at hstoch

/-- Helper for Theorem 19.30: integrating a real observable of `X n` under `P x` matches the
`n`-step kernel row of the realized chain. -/
private theorem localMarkovRealization_integral_comp_transition_eq
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    {g : E → ℝ} (x : E) (n : ℕ) :
    ∫ ω, g (X n ω) ∂(P x : Measure Ω) =
      ∫ z, g z ∂((discreteMatrixKernel p ^ n) x) := by
  let hReal :
      IsMarkovProcessRealization (fun m : ℕ ↦ discreteMatrixKernel p ^ m) P X := inferInstance
  have hXn : Measurable (X n) := hReal.measurable_process n
  -- Proof comment: rewrite the time-`n` marginal through the realization field `transition_eq`.
  rw [← hReal.transition_eq x n, integral_map]
  · exact hXn.aemeasurable
  · exact (Measurable.of_discrete : Measurable g).aestronglyMeasurable

/-- Helper for Theorem 19.30: in discrete time, bounded measurable shifted-future-path
functionals admit the standard Markov conditional-expectation formula along
`generatedFiltrationSpace X k`. -/
private theorem futurePathCondExp_of_markovProcessNat
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (g : (ℕ → E) → ℝ) (hg_meas : Measurable g)
    (hg_bdd : Bornology.IsBounded (Set.range g)) :
    ((P x : Measure Ω)[fun ω ↦ g (shiftedFuturePath X k ω) | generatedFiltrationSpace X k]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
  have hPathMap_meas : Measurable (fun ω ↦ fun m : ℕ ↦ X m ω) := by
    refine measurable_pi_lambda _ fun m ↦ ?_
    simpa using hX_meas m
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  let μ : Measure Ω := (P x : Measure Ω)
  have hgenerated_le : generatedFiltrationSpace X k ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comapLocal X k]
    exact (measurable_pastPath X hX_meas k).comap_le
  have hfuture_meas : Measurable (shiftedFuturePath X k) :=
    measurable_shiftedFuturePath X hX_meas k
  have hg_int :
      Integrable (fun ω ↦ g (shiftedFuturePath X k ω)) μ := by
    obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
    refine Integrable.of_bound (hg_meas.comp hfuture_meas).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC _ ⟨shiftedFuturePath X k ω, rfl⟩
  have hXk_generated : Measurable[generatedFiltrationSpace X k] (X k) := by
    rw [generatedFiltrationSpace_eq_pastPath_comapLocal X k]
    have hCoord :
        Measurable[MeasurableSpace.comap (pastPath X k) inferInstance]
          (fun ω ↦ pastPath X k ω (Fin.last k)) := by
      exact (measurable_pi_apply (Fin.last k)).comp (comap_measurable (pastPath X k))
    simpa [pastPath] using hCoord
  have hKernelIntegral_meas :
      Measurable fun z : E ↦ ∫ y, g y ∂κ z := by
    exact
      (hg_meas.stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun z : E ↦ ∫ y, g y ∂κ z).measurable
  have hKernelIntegral_meas_generated :
      Measurable[generatedFiltrationSpace X k] fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    exact hKernelIntegral_meas.comp hXk_generated
  have hKernelIntegral_meas_ambient :
      Measurable fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    exact hKernelIntegral_meas.comp (hX_meas k)
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
  have hCondExp :
      (fun ω ↦ ∫ y, g y ∂κ (X k ω)) =ᵐ[μ]
        μ[fun ω ↦ g (shiftedFuturePath X k ω) | generatedFiltrationSpace X k] := by
    exact MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hg_int
      (fun s hs hμs ↦ by
        refine IntegrableOn.of_bound hμs hKernelIntegral_meas_ambient.aestronglyMeasurable C ?_
        refine Filter.Eventually.of_forall fun ω ↦ ?_
        have hbound_row :
            ‖∫ y, g y ∂κ (X k ω)‖ ≤ C := by
          have hgC : ∀ᵐ y ∂κ (X k ω), ‖g y‖ ≤ C := by
            exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
          simpa using
            (MeasureTheory.norm_integral_le_of_norm_le_const (μ := κ (X k ω)) hgC)
        exact hbound_row)
      (fun s hs hμs ↦ by
        let νB : Measure (ℕ → E) := (μ.restrict s).map (shiftedFuturePath X k)
        let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict s).map (X k))
        have hs_history : MeasurableSet[generatedFiltrationSpace X k] s := hs
        have hlaw : νB = ρB := by
          simpa [μ, νB, ρB] using
            restrictedShiftedFuturePathLaw_eq_mixedPathLaw_on_history
              X P κ hX_meas hX0 hpath x k hs_history
        haveI : IsFiniteMeasure νB := by
          dsimp [νB]
          infer_instance
        have hg_νB_int : Integrable g νB := by
          refine Integrable.of_bound hg_meas.aestronglyMeasurable C ?_
          exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
        have hg_ρB_int : Integrable g ρB := by
          rw [← hlaw]
          exact hg_νB_int
        have hleft :
            ∫ ω in s, g (shiftedFuturePath X k ω) ∂μ = ∫ y, g y ∂νB := by
          change ∫ ω, g (shiftedFuturePath X k ω) ∂(μ.restrict s) = ∫ y, g y ∂νB
          rw [show νB = (μ.restrict s).map (shiftedFuturePath X k) by rfl]
          exact
            (MeasureTheory.integral_map hfuture_meas.aemeasurable
              hg_meas.aestronglyMeasurable).symm
        have hright :
            ∫ y, g y ∂ρB = ∫ ω in s, ∫ y, g y ∂κ (X k ω) ∂μ := by
          let κ₀ : Kernel Unit E := Kernel.const Unit ((μ.restrict s).map (X k))
          have hcomp :
              (κ ∘ₖ κ₀) () = ρB := by
            simp [κ₀, ρB]
          calc
            ∫ y, g y ∂ρB = ∫ y, g y ∂((κ ∘ₖ κ₀) ()) := by rw [← hcomp]
            _ = ∫ z, ∫ y, g y ∂κ z ∂κ₀ () := by
                  simpa using
                    (ProbabilityTheory.Kernel.integral_comp (η := κ) (κ := κ₀) (a := ())
                      hg_ρB_int)
            _ = ∫ z, ∫ y, g y ∂κ z ∂((μ.restrict s).map (X k)) := by
                  simp [κ₀]
            _ = ∫ ω in s, ∫ y, g y ∂κ (X k ω) ∂μ := by
                  simpa using
                    (MeasureTheory.integral_map (hX_meas k).aemeasurable
                      hKernelIntegral_meas.aestronglyMeasurable)
        exact (hleft.trans (hlaw ▸ hright)).symm)
      hKernelIntegral_meas_generated.aestronglyMeasurable
  exact hCondExp.symm

 -- The stale future-path averaging prototype below is kept commented because it still depends on
 -- a non-active conditional-expectation owner.
 /-

/-- Helper for Theorem 19.30: integrating the shifted collapsed-boundary hit indicator under the
start law `P y` equals the one-step average of the corresponding path-kernel row masses. -/
private theorem collapsedBoundaryHitFuturePath_real_eq_pathKernelAverage
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) (A : Set E) (y : E) :
    (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' collapsedBoundaryHitPathEvent x A) =
      ∫ z,
        (realizationPathKernel (P := P) (X := X) z).real (collapsedBoundaryHitPathEvent x A)
        ∂((discreteMatrixKernel p) y) := by
  let μ : Measure Ω := (P y : Measure Ω)
  let B : Set (ℕ → E) := collapsedBoundaryHitPathEvent x A
  let futureIndicator : Ω → ℝ := fun ω ↦
    Set.indicator B (fun _ ↦ (1 : ℝ)) (shiftedFuturePath X 1 ω)
  let rowMass : E → ℝ := fun z ↦
    (realizationPathKernel (P := P) (X := X) z).real B
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hB : MeasurableSet B := collapsedBoundaryHitPathEvent_measurable x A
  have hfuturePath_meas : Measurable (shiftedFuturePath X 1) :=
    measurable_shiftedFuturePath X hReal.measurable_process 1
  have hfuture_meas : Measurable futureIndicator := by
    -- Proof comment: compose the measurable path-event indicator with the measurable future-path
    -- map `ω ↦ (n ↦ X (n + 1) ω)`.
    exact (Measurable.indicator measurable_const hB).comp hfuturePath_meas
  have hfuture_int : Integrable futureIndicator μ := by
    -- Proof comment: the indicator takes values in `{0,1}`, so it is bounded and therefore
    -- integrable under the probability law `P y`.
    refine Integrable.of_bound hfuture_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : shiftedFuturePath X 1 ω ∈ B
      · simp [futureIndicator, hω]
      · simp [futureIndicator, hω]
  letI : IsTimeHomogeneousMarkovProcess X P
      (realizationPathKernel (P := P) (X := X)) :=
    realizationPathKernel_isTimeHomogeneousMarkovProcess
      (p := p) (P := P) (X := X)
  have hgenerated_le :
      generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ω› :=
    generatedFiltrationSpace_le_ambient (Y := X) (hY := hReal.measurable_process) 1
  have hcondAE :
      μ[fun ω ↦ futureIndicator ω | generatedFiltrationSpace X 1] =ᵐ[μ]
        fun ω ↦ rowMass (X 1 ω) := by
    let g : (ℕ → E) → ℝ := fun ξ ↦ Set.indicator B (fun _ ↦ (1 : ℝ)) ξ
    have hg_meas : Measurable g := by
      -- Proof comment: `g` is the measurable indicator of the path-space hit event.
      exact Measurable.indicator measurable_const hB
    have hg_bdd : Bornology.IsBounded (Set.range g) := by
      -- Proof comment: an indicator only takes the values `0` and `1`.
      simpa [g] using isBounded_range_indicator_one B
  have hAE :=
      futurePathCondExp_of_markovProcessNat
        (X := X) (P := P) (κ := realizationPathKernel (P := P) (X := X))
        (hX_meas := hReal.measurable_process)
        (hX0 := fun z ↦ by
          simpa using initialState_prob_eq_one_local (hReal := hReal) z)
        (hpath := realizationPathKernel_apply (P := P) (X := X))
        y 1 g hg_meas hg_bdd
    -- Proof comment: specialize the Chapter 17 future-path conditional-expectation bridge to the
    -- collapsed boundary-hit indicator.
    filter_upwards [hAE] with ω hω
    simpa [g, futureIndicator, rowMass, shiftedFuturePath, MeasureTheory.integral_indicator_one,
      hB] using hω
  have hfutureIntegral :
      ∫ ω, futureIndicator ω ∂μ = ∫ ω, rowMass (X 1 ω) ∂μ := by
    -- Proof comment: integrate the conditional-expectation identity over the ambient measure.
    calc
      ∫ ω, futureIndicator ω ∂μ
          = ∫ ω, μ[fun a ↦ futureIndicator a | generatedFiltrationSpace X 1] ω ∂μ := by
              symm
              exact integral_condExp hgenerated_le hfuture_int
      _ = ∫ ω, rowMass (X 1 ω) ∂μ := by
            exact integral_congr_ae hcondAE
  have htransitionIntegral :
      ∫ ω, rowMass (X 1 ω) ∂μ =
        ∫ z, rowMass z ∂((discreteMatrixKernel p) y) := by
    -- Proof comment: replace the time-`1` marginal of the realization by the one-step kernel.
    rw [← hReal.transition_eq y 1, integral_map]
    · rfl
    · exact (hReal.measurable_process 1).aemeasurable
    · exact Measurable.of_discrete.aestronglyMeasurable
  -- Proof comment: rewrite the shifted path-event mass as an indicator integral and then pass it
  -- through the future-path conditional-expectation bridge.
  calc
    (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' B)
        = ∫ ω, futureIndicator ω ∂μ := by
            symm
            simpa [μ, futureIndicator, B] using
              (MeasureTheory.integral_indicator_one
                (μ := μ)
                (s := (shiftedFuturePath X 1) ⁻¹' B)
                (hB.preimage hfuturePath_meas))
    _ = ∫ ω, rowMass (X 1 ω) ∂μ := hfutureIntegral
    _ = ∫ z, rowMass z ∂((discreteMatrixKernel p) y) := htransitionIntegral
 -/

 /-
private theorem collapsedBoundaryVoltageAmbient_average_eq
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} (hxA : x ∉ A) {y : E} (hy : y ∉ insert x A) :
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y =
      ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
        ∂((discreteMatrixKernel p) y) := by
  let B : Set (ℕ → E) := collapsedBoundaryHitPathEvent x A
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hB : MeasurableSet B := collapsedBoundaryHitPathEvent_measurable x A
  have hfuturePath_meas : Measurable (shiftedFuturePath X 1) :=
    measurable_shiftedFuturePath X hReal.measurable_process 1
  calc
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y
        = (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' B) := by
            calc
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y
                  = ∫ ω, Set.indicator B (fun _ ↦ (1 : ℝ)) (shiftedFuturePath X 1 ω)
                      ∂(P y : Measure Ω) := by
                        simpa [B] using
              collapsedBoundaryVoltageAmbient_eq_shiftedIndicatorIntegral
                            (p := p) (P := P) (X := X) x A hy
              _ = (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' B) := by
                    have hIndicatorIntegral :
                        ∫ ω, Set.indicator B (fun _ ↦ (1 : ℝ)) (shiftedFuturePath X 1 ω)
                            ∂(P y : Measure Ω) =
                          (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' B) := by
                      simpa [B] using
                        (MeasureTheory.integral_indicator_one
                          (μ := (P y : Measure Ω))
                          (s := (shiftedFuturePath X 1) ⁻¹' B)
                          (hB.preimage hfuturePath_meas))
                    exact hIndicatorIntegral.symm
    _ = ∫ z,
          (realizationPathKernel (P := P) (X := X) z).real B
            ∂((discreteMatrixKernel p) y) := by
              simpa [B] using
                collapsedBoundaryHitFuturePath_real_eq_pathKernelAverage
                  (p := p) (P := P) (X := X) x A y
    _ = ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
          ∂((discreteMatrixKernel p) y) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            -- Proof comment: each path-kernel row mass is exactly the ambient boundary voltage at
            -- the corresponding state.
            simpa [B, MeasureTheory.integral_indicator_one,
              collapsedBoundaryHitPathEvent_measurable x A] using
              (collapsedBoundaryVoltageAmbient_eq_pathIntegral
                (p := p) (P := P) (X := X) x (A := A) hxA z).symm

 --

/-- Helper for Theorem 19.30: integrating the shifted collapsed-boundary hit indicator under the
start law `P y` equals the one-step average of the corresponding path-kernel row masses. -/
private theorem collapsedBoundaryHitFuturePath_real_eq_pathKernelAverage
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) (A : Set E) (y : E) :
    (P y : Measure Ω).real ((futurePath X 1) ⁻¹' collapsedBoundaryHitPathEvent x A) =
      ∫ z,
        (realizationPathKernel (P := P) (X := X) z).real (collapsedBoundaryHitPathEvent x A)
        ∂((discreteMatrixKernel p) y) := by
  let μ : Measure Ω := (P y : Measure Ω)
  let B : Set (ℕ → E) := collapsedBoundaryHitPathEvent x A
  let futureIndicator : Ω → ℝ := fun ω ↦
    Set.indicator B (fun _ ↦ (1 : ℝ)) (futurePath X 1 ω)
  let rowMass : E → ℝ := fun z ↦
    (realizationPathKernel (P := P) (X := X) z).real B
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hB : MeasurableSet B := collapsedBoundaryHitPathEvent_measurable x A
  have hfuturePath_meas : Measurable (futurePath X 1) :=
    measurable_futurePath X hReal.measurable_process 1
  have hfuture_meas : Measurable futureIndicator := by
    -- Proof comment: compose the measurable path-event indicator with the measurable future-path
    -- map `ω ↦ (n ↦ X (n + 1) ω)`.
    exact (Measurable.indicator measurable_const hB).comp hfuturePath_meas
  have hfuture_int : Integrable futureIndicator μ := by
    -- Proof comment: the indicator takes values in `{0,1}`, so it is bounded and therefore
    -- integrable under the probability law `P y`.
    refine Integrable.of_bound hfuture_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : futurePath X 1 ω ∈ B
      · simp [futureIndicator, hω]
      · simp [futureIndicator, hω]
  letI : IsTimeHomogeneousMarkovProcess X P
      (realizationPathKernel (P := P) (X := X)) :=
    realizationPathKernel_isTimeHomogeneousMarkovProcess
      (p := p) (P := P) (X := X)
  have hgenerated_le :
      generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ω› :=
    generatedFiltrationSpace_le_ambient (Y := X) (hY := hReal.measurable_process) 1
  have hcondAE :
      μ[fun ω ↦ futureIndicator ω | generatedFiltrationSpace X 1] =ᵐ[μ]
        fun ω ↦ rowMass (X 1 ω) := by
    let g : (ℕ → E) → ℝ := fun ξ ↦ Set.indicator B (fun _ ↦ (1 : ℝ)) ξ
    have hg_meas : Measurable g := by
      -- Proof comment: `g` is the measurable indicator of the path-space hit event.
      exact Measurable.indicator measurable_const (collapsedBoundaryHitPathEvent_measurable x A)
    have hg_bdd : Bornology.IsBounded (Set.range g) := by
      -- Proof comment: an indicator only takes the values `0` and `1`.
      simpa [g] using isBounded_range_indicator_one B
    have hAE :=
      futurePathCondExp_of_markovProcessNatLocal
        (X := X) (P := P) (κ := realizationPathKernel (P := P) (X := X))
        (hX_meas := hReal.measurable_process)
        (hX0 := fun z ↦ by
          simpa using initialState_prob_eq_one_local (hReal := hReal) z)
        (hpath := realizationPathKernel_apply (P := P) (X := X))
        y 1 g hg_meas hg_bdd
    -- Proof comment: specialize the Chapter 17 future-path conditional-expectation bridge to the
    -- collapsed boundary-hit indicator.
    filter_upwards [hAE] with ω hω
    simpa [g, futureIndicator, rowMass, futurePath, MeasureTheory.integral_indicator_one,
      collapsedBoundaryHitPathEvent_measurable x A] using hω
  have hfutureIntegral :
      ∫ ω, futureIndicator ω ∂μ = ∫ ω, rowMass (X 1 ω) ∂μ := by
    -- Proof comment: integrate the conditional-expectation identity over the ambient measure.
    calc
      ∫ ω, futureIndicator ω ∂μ
          = ∫ ω, μ[fun a ↦ futureIndicator a | generatedFiltrationSpace X 1] ω ∂μ := by
              symm
              exact integral_condExp hgenerated_le hfuture_int
      _ = ∫ ω, rowMass (X 1 ω) ∂μ := by
            exact integral_congr_ae hcondAE
  have htransitionIntegral :
      ∫ ω, rowMass (X 1 ω) ∂μ =
        ∫ z, rowMass z ∂((discreteMatrixKernel p) y) := by
    -- Proof comment: replace the time-`1` marginal of the realization by the one-step kernel.
    rw [← hReal.transition_eq y 1, integral_map]
    · rfl
    · exact (hReal.measurable_process 1).aemeasurable
    · exact Measurable.of_discrete.aestronglyMeasurable
  -- Proof comment: rewrite the shifted path-event mass as an indicator integral and then pass it
  -- through the future-path conditional-expectation bridge.
  calc
    (P y : Measure Ω).real ((futurePath X 1) ⁻¹' B)
        = ∫ ω, futureIndicator ω ∂μ := by
            symm
            simpa [μ, futureIndicator, B] using
              (MeasureTheory.integral_indicator_one
                (μ := μ)
                (s := (futurePath X 1) ⁻¹' B)
                ((measurable_futurePath X hReal.measurable_process 1)
                  (MeasurableSet.of_discrete _)))
    _ = ∫ ω, rowMass (X 1 ω) ∂μ := hfutureIntegral
    _ = ∫ z, rowMass z ∂((discreteMatrixKernel p) y) := htransitionIntegral
 -/

 /-
/-- Helper for Theorem 19.30: away from the boundary `insert x A`, the ambient first-hit voltage
is the one-step average of its future values. -/
private theorem collapsedBoundaryVoltageAmbient_average_eq
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} (hxA : x ∉ A) {y : E} (hy : y ∉ insert x A) :
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y =
      ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
        ∂((discreteMatrixKernel p) y) := by
  let B : Set (ℕ → E) := collapsedBoundaryHitPathEvent x A
  calc
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y
        = (P y : Measure Ω).real ((futurePath X 1) ⁻¹' B) := by
            calc
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y
                  = ∫ ω, Set.indicator B (fun _ ↦ (1 : ℝ)) (shiftedFuturePath X 1 ω)
                      ∂(P y : Measure Ω) := by
                        simpa [B] using
                          collapsedBoundaryVoltageAmbient_eq_shiftedIndicatorIntegral
                            (p := p) (P := P) (X := X) x A hy
              _ = ∫ ω, Set.indicator B (fun _ ↦ (1 : ℝ)) (futurePath X 1 ω)
                    ∂(P y : Measure Ω) := by
                      congr 1
                      ext ω
                      simp [futurePath, shiftedFuturePath]
              _ = (P y : Measure Ω).real ((futurePath X 1) ⁻¹' B) := by
                    symm
                    simpa [B] using
                      (MeasureTheory.integral_indicator_one
                        (μ := (P y : Measure Ω))
                        (s := (futurePath X 1) ⁻¹' B)
                        ((measurable_futurePath X
                          (inferInstance : IsMarkovProcessRealization
                            (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process 1)
                          (MeasurableSet.of_discrete _)))
    _ = ∫ z,
          (realizationPathKernel (P := P) (X := X) z).real B
            ∂((discreteMatrixKernel p) y) := by
              simpa [B] using
                collapsedBoundaryHitFuturePath_real_eq_pathKernelAverage
                  (p := p) (P := P) (X := X) x A y
    _ = ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
          ∂((discreteMatrixKernel p) y) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            -- Proof comment: each path-kernel row mass is exactly the ambient boundary voltage at
            -- the corresponding state.
            simpa [B, MeasureTheory.integral_indicator_one,
              collapsedBoundaryHitPathEvent_measurable x A] using
              (collapsedBoundaryVoltageAmbient_eq_pathIntegral
                (p := p) (P := P) (X := X) x (A := A) hxA z).symm

/-- Helper for Theorem 19.30: every conductance row is nonzero for a random walk with weights. -/
private theorem conductance_ne_zero_of_randomWalk
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    [IsRandomWalkWithWeights p C] (x : E) :
    conductance C x ≠ 0 := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  intro hx0
  have hC0 : ∀ z : E, C x z = 0 := by
    intro z
    exact (ENNReal.tsum_eq_zero.mp hx0) z
  have hp0 : ∀ z : E, p x z = 0 := by
    intro z
    rw [hWalk.transition_eq, hC0 z]
    simp
  have hsum0 : ∑' z : E, p x z = 0 := by
    simp [hp0]
  have hstoch := hWalk.isStochastic x
  rw [hsum0] at hstoch
  simp at hstoch

/-- Helper for Theorem 19.30: in discrete time, bounded measurable future-path functionals admit
the standard Markov conditional-expectation formula along `generatedFiltrationSpace X k`. -/
private theorem futurePathCondExp_of_markovProcessNat
    (X : ℕ → Ω → E) (P : E → ProbabilityMeasure Ω) (κ : Kernel E (ℕ → E))
    (hX_meas : ∀ n, Measurable (X n))
    (hX0 : ∀ x, (P x : Measure Ω) (X 0 ⁻¹' ({x} : Set E)) = 1)
    (hpath : ∀ x, κ x = (P x : Measure Ω).map (fun ω ↦ fun n : ℕ ↦ X n ω))
    [IsTimeHomogeneousMarkovProcess X P κ]
    (x : E) (k : ℕ) (g : (ℕ → E) → ℝ) (hg_meas : Measurable g)
    (hg_bdd : Bornology.IsBounded (Set.range g)) :
    ((P x : Measure Ω)[fun ω ↦ g (futurePath X k ω) | generatedFiltrationSpace X k]) =ᵐ[
      (P x : Measure Ω)] fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
  have hPathMap_meas : Measurable (fun ω ↦ fun n : ℕ ↦ X n ω) := by
    refine measurable_pi_lambda _ fun n ↦ ?_
    simpa using hX_meas n
  letI : IsMarkovKernel κ := by
    refine ⟨fun y : E ↦ ?_⟩
    rw [hpath y]
    exact Measure.isProbabilityMeasure_map hPathMap_meas.aemeasurable
  let μ : Measure Ω := (P x : Measure Ω)
  have hgenerated_le : generatedFiltrationSpace X k ≤ ‹MeasurableSpace Ω› := by
    rw [generatedFiltrationSpace_eq_pastPath_comap X k]
    exact (measurable_pastPath X hX_meas k).comap_le
  have hfuture_meas : Measurable (futurePath X k) := measurable_futurePath X hX_meas k
  have hg_int :
      Integrable (fun ω ↦ g (futurePath X k ω)) μ := by
    obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
    -- Proof comment: bounded measurable path functionals are integrable under every start law.
    refine Integrable.of_bound (hg_meas.comp hfuture_meas).aestronglyMeasurable C ?_
    exact Filter.Eventually.of_forall fun ω ↦ hC _ ⟨futurePath X k ω, rfl⟩
  have hXk_generated : Measurable[generatedFiltrationSpace X k] (X k) := by
    -- Proof comment: the present state is the last coordinate of the finite past-path map.
    rw [generatedFiltrationSpace_eq_pastPath_comap X k]
    have hCoord :
        Measurable[MeasurableSpace.comap (pastPath X k) inferInstance]
          (fun ω ↦ pastPath X k ω (Fin.last k)) := by
      exact (measurable_pi_apply (Fin.last k)).comp (comap_measurable (pastPath X k))
    simpa [pastPath] using hCoord
  have hKernelIntegral_meas :
      Measurable fun z : E ↦ ∫ y, g y ∂κ z := by
    -- Proof comment: integrating a measurable bounded path functional against a Markov kernel is
    -- measurable in the start state.
    exact
      (hg_meas.stronglyMeasurable.integral_kernel :
        StronglyMeasurable fun z : E ↦ ∫ y, g y ∂κ z).measurable
  have hKernelIntegral_meas_generated :
      Measurable[generatedFiltrationSpace X k] fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    exact hKernelIntegral_meas.comp hXk_generated
  have hKernelIntegral_meas_ambient :
      Measurable fun ω ↦ ∫ y, g y ∂κ (X k ω) := by
    exact hKernelIntegral_meas.comp (hX_meas k)
  obtain ⟨C, hC⟩ := Bornology.IsBounded.exists_norm_le (s := Set.range g) hg_bdd
  have hCondExp :
      (fun ω ↦ ∫ y, g y ∂κ (X k ω)) =ᵐ[μ]
        μ[fun ω ↦ g (futurePath X k ω) | generatedFiltrationSpace X k] := by
    exact MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hgenerated_le hg_int
      (fun s hs hμs ↦ by
        -- Proof comment: the kernel-integral candidate stays bounded on every history event.
        refine IntegrableOn.of_bound hμs hKernelIntegral_meas_ambient.aestronglyMeasurable C ?_
        refine Filter.Eventually.of_forall fun ω ↦ ?_
        have hbound_row :
            ‖∫ y, g y ∂κ (X k ω)‖ ≤ C := by
          have hgC : ∀ᵐ y ∂κ (X k ω), ‖g y‖ ≤ C := by
            exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
          simpa using
            (MeasureTheory.norm_integral_le_of_norm_le_const (μ := κ (X k ω)) hgC)
        exact hbound_row)
      (fun s hs hμs ↦ by
        -- Proof comment: on each history event, both sides are integrals of `g` against the same
        -- restricted future-path law.
        let νB : Measure (ℕ → E) := (μ.restrict s).map (futurePath X k)
        let ρB : Measure (ℕ → E) := κ ∘ₘ ((μ.restrict s).map (X k))
        have hs_history : MeasurableSet[generatedFiltrationSpace X k] s := hs
        have hlaw : νB = ρB := by
          simpa [μ, νB, ρB] using
            restrictedFuturePathLaw_eq_mixedPathLaw_on_historyEvent
              X P κ hX_meas hX0 hpath x k hs_history
        haveI : IsFiniteMeasure νB := by
          dsimp [νB]
          infer_instance
        have hg_νB_int : Integrable g νB := by
          refine Integrable.of_bound hg_meas.aestronglyMeasurable C ?_
          exact Filter.Eventually.of_forall fun y ↦ hC _ ⟨y, rfl⟩
        have hg_ρB_int : Integrable g ρB := by
          rw [← hlaw]
          exact hg_νB_int
        have hleft :
            ∫ ω in s, g (futurePath X k ω) ∂μ = ∫ y, g y ∂νB := by
          change ∫ ω, g (futurePath X k ω) ∂(μ.restrict s) = ∫ y, g y ∂νB
          rw [show νB = (μ.restrict s).map (futurePath X k) by rfl]
          exact
            (MeasureTheory.integral_map hfuture_meas.aemeasurable
              hg_meas.aestronglyMeasurable).symm
        have hright :
            ∫ y, g y ∂ρB = ∫ ω in s, ∫ y, g y ∂κ (X k ω) ∂μ := by
          let κ₀ : Kernel Unit E := Kernel.const Unit ((μ.restrict s).map (X k))
          have hcomp :
              (κ ∘ₖ κ₀) () = ρB := by
            simp [κ₀, ρB]
          calc
            ∫ y, g y ∂ρB = ∫ y, g y ∂((κ ∘ₖ κ₀) ()) := by rw [← hcomp]
            _ = ∫ z, ∫ y, g y ∂κ z ∂κ₀ () := by
                  simpa using
                    (ProbabilityTheory.Kernel.integral_comp (η := κ) (κ := κ₀) (a := ())
                      hg_ρB_int)
            _ = ∫ z, ∫ y, g y ∂κ z ∂((μ.restrict s).map (X k)) := by
                  simp [κ₀]
            _ = ∫ ω in s, ∫ y, g y ∂κ (X k ω) ∂μ := by
                  simpa using
                    (MeasureTheory.integral_map (hX_meas k).aemeasurable
                      hKernelIntegral_meas.aestronglyMeasurable)
        exact (hleft.trans (hlaw ▸ hright)).symm)
      hKernelIntegral_meas_generated.aestronglyMeasurable
  exact hCondExp.symm

 -/

/-- Helper for Theorem 19.30: integrating the shifted collapsed-boundary hit indicator under the
start law `P y` equals the one-step average of the corresponding path-kernel row masses. -/
private theorem collapsedBoundaryHitFuturePath_real_eq_pathKernelAverage
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) (A : Set E) (y : E) :
    (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' collapsedBoundaryHitPathEvent x A) =
      ∫ z,
        (realizationPathKernel (P := P) (X := X) z).real (collapsedBoundaryHitPathEvent x A)
        ∂((discreteMatrixKernel p) y) := by
  let μ : Measure Ω := (P y : Measure Ω)
  let B : Set (ℕ → E) := collapsedBoundaryHitPathEvent x A
  let futureIndicator : Ω → ℝ := fun ω ↦
    Set.indicator B (fun _ ↦ (1 : ℝ)) (shiftedFuturePath X 1 ω)
  let rowMass : E → ℝ := fun z ↦
    (realizationPathKernel (P := P) (X := X) z).real B
  let hReal :
      IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X := inferInstance
  have hB : MeasurableSet B := collapsedBoundaryHitPathEvent_measurable x A
  have hfuturePath_meas : Measurable (shiftedFuturePath X 1) :=
    measurable_shiftedFuturePath X hReal.measurable_process 1
  have hfuture_meas : Measurable futureIndicator := by
    exact (Measurable.indicator measurable_const hB).comp hfuturePath_meas
  have hfuture_int : Integrable futureIndicator μ := by
    refine Integrable.of_bound hfuture_meas.aestronglyMeasurable 1 ?_
    exact Filter.Eventually.of_forall fun ω ↦ by
      by_cases hω : shiftedFuturePath X 1 ω ∈ B
      · simp [futureIndicator, hω]
      · simp [futureIndicator, hω]
  letI : IsTimeHomogeneousMarkovProcess X P
      (realizationPathKernel (P := P) (X := X)) :=
    realizationPathKernel_isTimeHomogeneousMarkovProcess
      (p := p) (P := P) (X := X)
  have hgenerated_le :
      generatedFiltrationSpace X 1 ≤ ‹MeasurableSpace Ω› :=
    generatedFiltrationSpace_le_ambient (Y := X) (hY := hReal.measurable_process) 1
  have hcondAE :
      μ[fun ω ↦ futureIndicator ω | generatedFiltrationSpace X 1] =ᵐ[μ]
        fun ω ↦ rowMass (X 1 ω) := by
    let g : (ℕ → E) → ℝ := fun ξ ↦ Set.indicator B (fun _ ↦ (1 : ℝ)) ξ
    have hg_meas : Measurable g := by
      -- Proof comment: `g` is the measurable indicator of the path-space hit event.
      exact Measurable.indicator measurable_const (collapsedBoundaryHitPathEvent_measurable x A)
    have hg_bdd : Bornology.IsBounded (Set.range g) := by
      simpa [g] using isBounded_range_indicator_one B
    have hAE :=
      futurePathCondExp_of_markovProcessNat
        (X := X) (P := P) (κ := realizationPathKernel (P := P) (X := X))
        (hX_meas := hReal.measurable_process)
        (hX0 := fun z ↦ by
          simpa using initialState_prob_eq_one_local (hReal := hReal) z)
        (hpath := realizationPathKernel_apply (P := P) (X := X))
        y 1 g hg_meas hg_bdd
    filter_upwards [hAE] with ω hω
    simpa [g, futureIndicator, rowMass, shiftedFuturePath, MeasureTheory.integral_indicator_one,
      hB]
      using hω
  have hfutureIntegral :
      ∫ ω, futureIndicator ω ∂μ = ∫ ω, rowMass (X 1 ω) ∂μ := by
    -- Proof comment: integrate the conditional-expectation identity over the ambient measure.
    calc
      ∫ ω, futureIndicator ω ∂μ
          = ∫ ω, μ[fun a ↦ futureIndicator a | generatedFiltrationSpace X 1] ω ∂μ := by
              symm
              simpa using (integral_condExp hgenerated_le : _)
      _ = ∫ ω, rowMass (X 1 ω) ∂μ := by
            exact integral_congr_ae hcondAE
  have htransitionIntegral :
      ∫ ω, rowMass (X 1 ω) ∂μ =
        ∫ z, rowMass z ∂((discreteMatrixKernel p) y) := by
    -- Proof comment: replace the time-`1` marginal of the realization by the one-step kernel.
    simpa [μ] using
      (localMarkovRealization_integral_comp_transition_eq
        (p := p) (P := P) (X := X) (g := rowMass) y 1)
  calc
    (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' B)
        = ∫ ω, futureIndicator ω ∂μ := by
            have hIndicatorIntegral :
                ∫ ω, futureIndicator ω ∂μ =
                  (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' B) := by
              simpa [μ, futureIndicator] using
                (MeasureTheory.integral_indicator_one
                  (μ := μ)
                  (s := (shiftedFuturePath X 1) ⁻¹' B)
                  (hB.preimage hfuturePath_meas))
            exact hIndicatorIntegral.symm
    _ = ∫ ω, rowMass (X 1 ω) ∂μ := hfutureIntegral
    _ = ∫ z, rowMass z ∂((discreteMatrixKernel p) y) := htransitionIntegral

/-- Helper for Theorem 19.30: away from the boundary `insert x A`, the ambient first-hit voltage
is the one-step average of its future values. -/
private theorem collapsedBoundaryVoltageAmbient_average_eq
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} (hxA : x ∉ A) {y : E} (hy : y ∉ insert x A) :
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y =
      ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
        ∂((discreteMatrixKernel p) y) := by
  let B : Set (ℕ → E) := collapsedBoundaryHitPathEvent x A
  have hB : MeasurableSet B := collapsedBoundaryHitPathEvent_measurable x A
  have hfuturePath_meas : Measurable (shiftedFuturePath X 1) := by
    exact
      measurable_shiftedFuturePath X
        (inferInstance : IsMarkovProcessRealization
          (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process 1
  calc
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y
        = (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' B) := by
            calc
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y
                  = ∫ ω, Set.indicator B (fun _ ↦ (1 : ℝ)) (shiftedFuturePath X 1 ω)
                      ∂(P y : Measure Ω) := by
                        simpa [B] using
              collapsedBoundaryVoltageAmbient_eq_shiftedIndicatorIntegral
                            (p := p) (P := P) (X := X) x A hy
              _ = (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' B) := by
                    have hIndicatorIntegral :
                        ∫ ω, Set.indicator B (fun _ ↦ (1 : ℝ)) (shiftedFuturePath X 1 ω)
                            ∂(P y : Measure Ω) =
                          (P y : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹' B) := by
                      simpa [B] using
                        (MeasureTheory.integral_indicator_one
                          (μ := (P y : Measure Ω))
                          (s := (shiftedFuturePath X 1) ⁻¹' B)
                          (hB.preimage hfuturePath_meas))
                    exact hIndicatorIntegral
    _ = ∫ z,
          (realizationPathKernel (P := P) (X := X) z).real B
            ∂((discreteMatrixKernel p) y) := by
              simpa [B] using
                collapsedBoundaryHitFuturePath_real_eq_pathKernelAverage
                  (p := p) (P := P) (X := X) x A y
    _ = ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
          ∂((discreteMatrixKernel p) y) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            -- Proof comment: each path-kernel row mass is exactly the ambient boundary voltage at
            -- the corresponding state.
            simpa [B, MeasureTheory.integral_indicator_one,
              collapsedBoundaryHitPathEvent_measurable x A] using
              (collapsedBoundaryVoltageAmbient_eq_pathIntegral
                (p := p) (P := P) (X := X) x (A := A) hxA z).symm
/-- Helper for Theorem 19.30: the positive-time escape event from `x` to `A` is exactly the
one-step future-path version of the collapsed boundary-hit event. -/
private theorem escapeEvent_iff_futurePath_mem_collapsedBoundaryHitPathEvent
    {Ω' : Type*} [MeasurableSpace Ω'] (u : ℕ → Ω' → E)
    (x : E) (A : Set E) (hxA : x ∉ A) (ω : Ω') :
    (∃ n : ℕ, 0 < n ∧ u n ω ∈ A ∧
      ∀ m : ℕ, 0 < m → m ≤ n → u m ω ≠ x) ↔
        shiftedFuturePath u 1 ω ∈ collapsedBoundaryHitPathEvent x A := by
  constructor
  · rintro ⟨n, hn_pos, hnA, havoid⟩
    let S : Set ℕ := {k | 0 < k ∧ u k ω ∈ A}
    have hS : ∃ k, k ∈ S := ⟨n, hn_pos, hnA⟩
    let k := Nat.find hS
    have hk_pos : 0 < k := (Nat.find_spec hS).1
    have hkA : u k ω ∈ A := (Nat.find_spec hS).2
    have hk_le_n : k ≤ n := Nat.find_min' hS ⟨hn_pos, hnA⟩
    obtain ⟨m, hm_eq : k = m + 1⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk_pos)
    refine ⟨m, ?_, ?_⟩
    · simpa [shiftedFuturePath, hm_eq, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hkA
    · intro j hj
      have hj_lt_k : j + 1 < k := by
        simpa [hm_eq] using Nat.succ_lt_succ hj
      have hnotA : u (j + 1) ω ∉ A := by
        intro hjA
        exact Nat.not_lt_of_ge (Nat.find_min' hS ⟨Nat.succ_pos j, hjA⟩) hj_lt_k
      have hj_succ_le_n : j + 1 ≤ n := by
        have hm_succ_le_n : m + 1 ≤ n := by
          simpa [hm_eq] using hk_le_n
        have hm_le_n : m ≤ n := le_trans (Nat.le_succ m) hm_succ_le_n
        exact le_trans (Nat.succ_le_of_lt hj) hm_le_n
      have hnotx : u (j + 1) ω ≠ x := by
        exact havoid (j + 1) (Nat.succ_pos j) hj_succ_le_n
      have hnot_mem : u (j + 1) ω ∉ insert x A := by
        simp [hnotx, hnotA]
      simpa [shiftedFuturePath, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
        using hnot_mem
  · intro hfuture
    exact
      shiftedFuturePath_mem_collapsedBoundaryHitPathEvent_imp_escapeEvent
        (u := u) x A hxA ω <| by
          simpa [shiftedFuturePath] using hfuture

 /-
/-- Helper for Theorem 19.30: the source escape probability is the one-step average of the ambient
collapsed boundary voltage. -/
private theorem escapeToSetProbability_eq_average_collapsedBoundaryVoltageAmbient
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} (hxA : x ∉ A) :
    escapeToSetProbability P X x A =
      ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
        ∂((discreteMatrixKernel p) x) := by
  -- Proof comment: rewrite the escape event as the one-step future-path hit event, then average
  -- the path-kernel row masses and identify each mass with the ambient collapsed voltage.
  calc
    escapeToSetProbability P X x A
        = (P x : Measure Ω).real ((futurePath X 1) ⁻¹' collapsedBoundaryHitPathEvent x A) := by
            rw [escapeToSetProbability_def]
            congr 1
            ext ω
            exact
              escapeEvent_iff_futurePath_mem_collapsedBoundaryHitPathEvent
                (u := X) x A hxA ω
    _ = ∫ z,
          (realizationPathKernel (P := P) (X := X) z).real (collapsedBoundaryHitPathEvent x A)
            ∂((discreteMatrixKernel p) x) := by
              simpa using
                collapsedBoundaryHitFuturePath_real_eq_pathKernelAverage
                  (p := p) (P := P) (X := X) x A x
    _ = ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
          ∂((discreteMatrixKernel p) x) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            simpa [MeasureTheory.integral_indicator_one,
              collapsedBoundaryHitPathEvent_measurable x A] using
              (collapsedBoundaryVoltageAmbient_eq_pathIntegral
                (p := p) (P := P) (X := X) x (A := A) hxA z).symm

/-- Helper for Theorem 19.30: the earlier ambient-voltage averaging bridge, given a unique local
name so the weighted-row proof can use it without colliding with the repeated private owner names
already present in this file. -/
private theorem collapsedBoundaryVoltageAmbient_average_eq_forCollapsedRow
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} (hxA : x ∉ A) {y : E} (hy : y ∉ insert x A) :
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y =
      ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
        ∂((discreteMatrixKernel p) y) := by
  let B : Set (ℕ → E) := collapsedBoundaryHitPathEvent x A
  calc
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y
        = (P y : Measure Ω).real ((futurePath X 1) ⁻¹' B) := by
            calc
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y
                  = ∫ ω, Set.indicator B (fun _ ↦ (1 : ℝ)) (shiftedFuturePath X 1 ω)
                      ∂(P y : Measure Ω) := by
                        simpa [B] using
                          collapsedBoundaryVoltageAmbient_eq_shiftedIndicatorIntegral
                            (p := p) (P := P) (X := X) x A hy
              _ = ∫ ω, Set.indicator B (fun _ ↦ (1 : ℝ)) (futurePath X 1 ω)
                    ∂(P y : Measure Ω) := by
                      congr 1
                      ext ω
                      simp [futurePath, shiftedFuturePath]
              _ = (P y : Measure Ω).real ((futurePath X 1) ⁻¹' B) := by
                    symm
                    simpa [B] using
                      (MeasureTheory.integral_indicator_one
                        (μ := (P y : Measure Ω))
                        (s := (futurePath X 1) ⁻¹' B)
                        ((measurable_futurePath X
                          (inferInstance : IsMarkovProcessRealization
                            (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X).measurable_process 1)
                          (MeasurableSet.of_discrete _)))
    _ = ∫ z,
          (realizationPathKernel (P := P) (X := X) z).real B
            ∂((discreteMatrixKernel p) y) := by
              simpa [B] using
                collapsedBoundaryHitFuturePath_real_eq_pathKernelAverage
                  (p := p) (P := P) (X := X) x A y
    _ = ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
          ∂((discreteMatrixKernel p) y) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            -- Proof comment: each path-kernel row mass is the ambient boundary voltage at the
            -- corresponding state.
            simpa [B, MeasureTheory.integral_indicator_one,
              collapsedBoundaryHitPathEvent_measurable x A] using
              (collapsedBoundaryVoltageAmbient_eq_pathIntegral
                (p := p) (P := P) (X := X) x (A := A) hxA z).symm
 -/

/-- Helper for Theorem 19.30: the ambient and collapsed voltage owners agree on every visible
vertex, including the visible copy of the start state. -/
private theorem collapsedBoundaryVoltageAmbient_eq_visibleValue
    {p : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} (hxA : x ∉ A) (z : {y : E // y ∉ A}) :
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1 =
      collapsedBoundaryVoltage (P := P) (X := X) x A (Sum.inl z) := by
  by_cases hzx : z.1 = x
  · have hz_eq : z = ⟨x, hxA⟩ := Subtype.ext hzx
    subst hz_eq
    -- Proof comment: the visible start vertex carries the boundary value `0` in both owners.
    simpa [collapsedBoundaryVoltageAmbient] using
      (collapsedBoundaryVoltage_start (p := p) (P := P) (X := X) x A hxA).symm
  · -- Proof comment: away from the start vertex, the ambient and collapsed owners coincide by
    -- construction.
    exact collapsedBoundaryVoltageAmbient_eq_visible (P := P) (X := X) x z hzx

/-- Helper for Theorem 19.30: the real-valued collapsed sink edge is exactly the target-side real
row sum of the ambient conductance. -/
private theorem cofiniteTargetCollapse_left_sink_toReal
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    [IsRandomWalkWithWeights p C] {A : Set E} (y : {z : E // z ∉ A}) :
    (cofiniteTargetCollapse C A (Sum.inl y) (Sum.inr ())).toReal =
      ∑' z : E, if z ∈ A then (C y.1 z).toReal else 0 := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  have hconductance_lt_top : conductance C y.1 < ∞ := hWalk.conductance_lt_top y.1
  have hCrow_ne_top : (∑' z : E, C y.1 z) ≠ ∞ := by
    simpa [conductance] using hconductance_lt_top.ne
  have hCrow_toReal : Summable (fun z : E ↦ (C y.1 z).toReal) :=
    ENNReal.summable_toReal hCrow_ne_top
  have hsummable :
      Summable (fun z : E ↦ if z ∈ A then (C y.1 z).toReal else 0) := by
    -- Proof comment: the target-side real row is dominated by the full real row of `C`.
    refine Summable.of_nonneg_of_le
      (fun z ↦ by
        by_cases hz : z ∈ A <;> simp [hz])
      (fun z ↦ by
        by_cases hz : z ∈ A <;> simp [hz])
      hCrow_toReal
  have hsink_ne_top :
      (∑' z : E, if z ∈ A then C y.1 z else 0) ≠ ∞ := by
    -- Proof comment: the collapsed sink edge is bounded by the full conductance at `y`.
    exact ne_of_lt <|
      lt_of_le_of_lt
        (cofiniteTargetCollapse_left_sink_le_conductance (p := p) (C := C) A y)
        hconductance_lt_top
  have hentry_ne_top : ∀ z : E, C y.1 z ≠ ∞ := by
    intro z
    apply ne_of_lt
    have hle : C y.1 z ≤ conductance C y.1 := by
      simpa [conductance] using (ENNReal.le_tsum z : C y.1 z ≤ ∑' w : E, C y.1 w)
    exact lt_of_le_of_lt hle hconductance_lt_top
  have hofReal :
      ENNReal.ofReal (∑' z : E, if z ∈ A then (C y.1 z).toReal else 0) =
        ∑' z : E, if z ∈ A then C y.1 z else 0 := by
    calc
      ENNReal.ofReal (∑' z : E, if z ∈ A then (C y.1 z).toReal else 0)
          = ∑' z : E, ENNReal.ofReal (if z ∈ A then (C y.1 z).toReal else 0) := by
              exact ENNReal.ofReal_tsum_of_nonneg
                (fun z ↦ by
                  by_cases hz : z ∈ A <;> simp [hz])
                hsummable
      _ = ∑' z : E, if z ∈ A then C y.1 z else 0 := by
            refine tsum_congr fun z ↦ ?_
            by_cases hz : z ∈ A
            · simp [hz, hentry_ne_top z]
            · simp [hz]
  have htoReal := congrArg ENNReal.toReal hofReal
  calc
    (cofiniteTargetCollapse C A (Sum.inl y) (Sum.inr ())).toReal
        = (∑' z : E, if z ∈ A then C y.1 z else 0).toReal := by
            simp [cofiniteTargetCollapse]
    _ = ∑' z : E, if z ∈ A then (C y.1 z).toReal else 0 := by
          symm
          calc
            (∑' z : E, if z ∈ A then (C y.1 z).toReal else 0)
                = (ENNReal.ofReal
                    (∑' z : E, if z ∈ A then (C y.1 z).toReal else 0)).toReal := by
                      rw [ENNReal.toReal_ofReal]
                      exact tsum_nonneg fun z ↦ by
                        by_cases hz : z ∈ A <;> simp [hz, ENNReal.toReal_nonneg]
            _ = (∑' z : E, if z ∈ A then C y.1 z else 0).toReal := htoReal

/-- Helper for Theorem 19.30: the source escape probability is the one-step average of the
ambient collapsed boundary voltage, in executable scope for the weighted bridge. -/
private theorem escapeToSetProbability_eq_averageCollapsedBoundaryVoltageAmbient
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} (hxA : x ∉ A) :
    (escapeToSetProbability P X x A).toReal =
      ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
        ∂((discreteMatrixKernel p) x) := by
  have hEvent :
      {ω | ∃ n : ℕ, 0 < n ∧ X n ω ∈ A ∧ ∀ m : ℕ, 0 < m → m ≤ n → X m ω ≠ x} =
        (shiftedFuturePath X 1) ⁻¹' collapsedBoundaryHitPathEvent x A := by
    ext ω
    exact
      escapeEvent_iff_futurePath_mem_collapsedBoundaryHitPathEvent
        (u := X) x A hxA ω
  -- Proof comment: rewrite the escape event as the one-step future-path hit event, then average
  -- the path-kernel row masses and identify each mass with the ambient collapsed voltage.
  calc
    (escapeToSetProbability P X x A).toReal
        = (P x : Measure Ω).real ((shiftedFuturePath X 1) ⁻¹'
            collapsedBoundaryHitPathEvent x A) := by
            rw [escapeToSetProbability_def, measureReal_def, hEvent]
    _ = ∫ z,
          (realizationPathKernel (P := P) (X := X) z).real (collapsedBoundaryHitPathEvent x A)
            ∂((discreteMatrixKernel p) x) := by
              simpa using
                collapsedBoundaryHitFuturePath_real_eq_pathKernelAverage
                  (p := p) (P := P) (X := X) x A x
    _ = ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
          ∂((discreteMatrixKernel p) x) := by
            refine integral_congr_ae <| Filter.Eventually.of_forall fun z ↦ ?_
            simpa [MeasureTheory.integral_indicator_one,
              collapsedBoundaryHitPathEvent_measurable x A] using
              (collapsedBoundaryVoltageAmbient_eq_pathIntegral
                (p := p) (P := P) (X := X) x (A := A) hxA z).symm

/-- Helper for Theorem 19.30: away from `insert x A`, the ambient first-hit voltage is the
one-step average of its future values, in executable scope for the weighted bridge. -/
private theorem collapsedBoundaryVoltageAmbient_average_eq_visibleRow
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} (hxA : x ∉ A) {y : E} (hy : y ∉ insert x A) :
    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y =
      ∫ z, collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
        ∂((discreteMatrixKernel p) y) := by
  exact
    collapsedBoundaryVoltageAmbient_average_eq
      (p := p) (C := C) (P := P) (X := X) x hxA hy

/-- Helper for Theorem 19.30: away from the collapsed boundary `{x, sink}`, the first-hit voltage
solves the weighted row equation of the sink-collapsed network. -/
private theorem collapsedBoundaryVoltage_weightedRow
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} [Fintype {y : E // y ∉ A}]
    (hxA : x ∉ A) (y : {z : E // z ∉ A}) (hyx : y.1 ≠ x) :
    (conductance (cofiniteTargetCollapse C A) (Sum.inl y)).toReal *
        collapsedBoundaryVoltage (P := P) (X := X) x A (Sum.inl y) =
      ∑ z : ({z : E // z ∉ A} ⊕ Unit),
        (cofiniteTargetCollapse C A (Sum.inl y) z).toReal *
          collapsedBoundaryVoltage (P := P) (X := X) x A z := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  have hy : y.1 ∉ insert x A := by
    -- Proof comment: a visible vertex of the collapsed network lies outside both the start state
    -- and the target set.
    simp [hyx, y.2]
  have hconductance_lt_top : conductance C y.1 < ∞ := hWalk.conductance_lt_top y.1
  have hconductance_ne_zero : conductance C y.1 ≠ 0 :=
    conductance_ne_zero_of_randomWalk (p := p) (C := C) y.1
  have hconductance_toReal_ne_zero : (conductance C y.1).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨hconductance_ne_zero, hconductance_lt_top.ne⟩
  have hp_row_ne_top : (∑' z : E, p y.1 z) ≠ ∞ := by
    -- Proof comment: the transition row is stochastic, hence its total mass is `1`.
    rw [hWalk.isStochastic y.1]
    simp
  have hp_row_summable : Summable (fun z : E ↦ (p y.1 z).toReal) :=
    ENNReal.summable_toReal hp_row_ne_top
  have hkernelNormSummable :
      Summable
        (fun z : E ↦
          (p y.1 z).toReal *
            ‖collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z‖) := by
    -- Proof comment: the ambient voltage is uniformly bounded by `1`, so the stochastic row
    -- dominates the needed norm series.
    refine Summable.of_nonneg_of_le
      (fun z ↦ by positivity)
      (fun z ↦ by
        calc
          (p y.1 z).toReal * ‖collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z‖
              ≤ (p y.1 z).toReal * 1 := by
                  exact mul_le_mul_of_nonneg_left
                    (collapsedBoundaryVoltageAmbient_norm_le_one
                      (P := P) (X := X) x (A := A) z)
                    ENNReal.toReal_nonneg
          _ = (p y.1 z).toReal := by ring)
      hp_row_summable
  have hkernelValueSummable :
      Summable
        (fun z : E ↦
          (p y.1 z).toReal * collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) := by
    have hnorm :
        Summable
          (fun z : E ↦
            ‖(p y.1 z).toReal *
                collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z‖) := by
      simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using
        hkernelNormSummable
    exact summable_norm_iff.mp hnorm
  have havg :=
    collapsedBoundaryVoltageAmbient_average_eq_visibleRow
      (p := p) (C := C) (P := P) (X := X) x hxA (y := y.1) hy
  rw [integral_discreteMatrixKernel_eq_tsum
    p hWalk.isStochasticMatrix
      (fun z : E ↦ collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z)
      y.1 hkernelNormSummable] at havg
  have hscaled :
      (conductance C y.1).toReal *
          collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y.1 =
        ∑' z : E,
          (C y.1 z).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z := by
    -- Proof comment: multiply the stochastic averaging identity by the visible-row conductance
    -- and use the random-walk normalization `p = C / conductance`.
    calc
      (conductance C y.1).toReal *
          collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y.1
          =
        (conductance C y.1).toReal *
          ∑' z : E,
            (p y.1 z).toReal *
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z := by
                rw [havg]
      _ =
          ∑' z : E,
            (conductance C y.1).toReal *
              ((p y.1 z).toReal *
                collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) := by
                  rw [← tsum_mul_left]
      _ =
          ∑' z : E,
            ((conductance C y.1).toReal * (p y.1 z).toReal) *
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z := by
                refine tsum_congr fun z ↦ ?_
                ring
      _ =
          ∑' z : E,
            (C y.1 z).toReal *
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z := by
                refine tsum_congr fun z ↦ ?_
                have hterm :
                    (conductance C y.1).toReal * (p y.1 z).toReal =
                      (C y.1 z).toReal := by
                  rw [hWalk.transition_eq, ENNReal.toReal_div]
                  field_simp [hconductance_toReal_ne_zero]
                rw [hterm]
  have hCrow_ne_top : (∑' z : E, C y.1 z) ≠ ∞ := by
    simpa [conductance] using hconductance_lt_top.ne
  have hCrow_toReal : Summable (fun z : E ↦ (C y.1 z).toReal) :=
    ENNReal.summable_toReal hCrow_ne_top
  have htargetSummable :
      Summable (fun z : E ↦ if z ∈ A then (C y.1 z).toReal else 0) := by
    -- Proof comment: the target-side real row is pointwise bounded by the full real row.
    refine Summable.of_nonneg_of_le
      (fun z ↦ by
        by_cases hz : z ∈ A <;> simp [hz])
      (fun z ↦ by
        by_cases hz : z ∈ A <;> simp [hz])
      hCrow_toReal
  have hvisibleIndicatorSummable :
      Summable
        (fun z : E ↦
          Set.indicator {z : E | z ∉ A}
            (fun z ↦
              (C y.1 z).toReal *
                collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z) := by
    have hnorm :
        Summable
          (fun z : E ↦
            ‖Set.indicator {z : E | z ∉ A}
                (fun z ↦
                  (C y.1 z).toReal *
                    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z‖) := by
      refine Summable.of_nonneg_of_le
        (fun z ↦ by positivity)
        (fun z ↦ by
          by_cases hz : z ∉ A
          · calc
              ‖Set.indicator {z : E | z ∉ A}
                  (fun z ↦
                    (C y.1 z).toReal *
                      collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z‖
                  =
                ‖(C y.1 z).toReal *
                    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z‖ := by
                      simp [Set.indicator, hz]
              _ = (C y.1 z).toReal *
                    ‖collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z‖ := by
                      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
              _ ≤ (C y.1 z).toReal * 1 := by
                    exact mul_le_mul_of_nonneg_left
                      (collapsedBoundaryVoltageAmbient_norm_le_one
                        (P := P) (X := X) x (A := A) z)
                      ENNReal.toReal_nonneg
              _ = (C y.1 z).toReal := by ring
          · simp [Set.indicator, hz])
        hCrow_toReal
    exact summable_norm_iff.mp hnorm
  have hvisibleAmbient :
      ∑ z : {z : E // z ∉ A},
          (C y.1 z.1).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1
        =
      ∑' z : E,
        Set.indicator {z : E | z ∉ A}
          (fun z ↦
            (C y.1 z).toReal *
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z := by
    -- Proof comment: the visible contribution is the subtype row over `Aᶜ`.
    calc
      ∑ z : {z : E // z ∉ A},
          (C y.1 z.1).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1
          =
        ∑' z : {z : E // z ∉ A},
          (C y.1 z.1).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1 := by
              symm
              exact
                tsum_fintype
                  (f := fun z : {z : E // z ∉ A} ↦
                    (C y.1 z.1).toReal *
                      collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1)
      _ =
          ∑' z : E,
            Set.indicator {z : E | z ∉ A}
              (fun z ↦
                (C y.1 z).toReal *
                  collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z := by
                    simpa using
                      (tsum_subtype
                        (s := {z : E | z ∉ A})
                        (f := fun z : E ↦
                          (C y.1 z).toReal *
                            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z))
  have hambientSplit :
      ∑' z : E,
        (C y.1 z).toReal *
          collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
        =
      ∑ z : {z : E // z ∉ A},
        (C y.1 z.1).toReal *
          collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1
        +
      ∑' z : E, if z ∈ A then (C y.1 z).toReal else 0 := by
    -- Proof comment: split the ambient row into the visible `Aᶜ` contribution and the target-side
    -- sink contribution.
    calc
      ∑' z : E,
        (C y.1 z).toReal *
          collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z
          =
        ∑' z : E,
          ((Set.indicator {z : E | z ∉ A}
              (fun z ↦
                (C y.1 z).toReal *
                  collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z)
            +
              (if z ∈ A then (C y.1 z).toReal else 0)) := by
                refine tsum_congr fun z ↦ ?_
                by_cases hzA : z ∈ A
                · have hzx : z ≠ x := by
                    intro hzx
                    exact hxA (hzx ▸ hzA)
                  simp [Set.indicator, hzA, hzx, collapsedBoundaryVoltageAmbient]
                · simp [Set.indicator, hzA]
      _ =
          (∑' z : E,
            Set.indicator {z : E | z ∉ A}
              (fun z ↦
                (C y.1 z).toReal *
                  collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z)
            +
              ∑' z : E, if z ∈ A then (C y.1 z).toReal else 0 := by
                  rw [Summable.tsum_add hvisibleIndicatorSummable htargetSummable]
      _ =
          ∑ z : {z : E // z ∉ A},
            (C y.1 z.1).toReal *
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1
            +
              ∑' z : E, if z ∈ A then (C y.1 z).toReal else 0 := by
                  rw [← hvisibleAmbient]
  have hvisibleCollapse :
      ∑ z : {z : E // z ∉ A},
          (C y.1 z.1).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1
        =
      ∑ z : {z : E // z ∉ A},
          (cofiniteTargetCollapse C A (Sum.inl y) (Sum.inl z)).toReal *
            collapsedBoundaryVoltage (P := P) (X := X) x A (Sum.inl z) := by
    -- Proof comment: on visible vertices, the ambient and collapsed voltage owners coincide.
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [collapsedBoundaryVoltageAmbient_eq_visibleValue
      (p := p) (P := P) (X := X) x hxA z]
    simp [cofiniteTargetCollapse]
  calc
    (conductance (cofiniteTargetCollapse C A) (Sum.inl y)).toReal *
        collapsedBoundaryVoltage (P := P) (X := X) x A (Sum.inl y)
        =
      (conductance C y.1).toReal *
        collapsedBoundaryVoltageAmbient (P := P) (X := X) x A y.1 := by
          rw [cofiniteTargetCollapse_visible_conductance (p := p) (C := C) (A := A) y]
          rw [collapsedBoundaryVoltageAmbient_eq_visibleValue
            (p := p) (P := P) (X := X) x hxA y]
    _ =
        ∑' z : E,
          (C y.1 z).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z := hscaled
    _ =
        ∑ z : {z : E // z ∉ A},
          (C y.1 z.1).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1
          +
            ∑' z : E, if z ∈ A then (C y.1 z).toReal else 0 := hambientSplit
    _ =
        ∑ z : {z : E // z ∉ A},
          (cofiniteTargetCollapse C A (Sum.inl y) (Sum.inl z)).toReal *
            collapsedBoundaryVoltage (P := P) (X := X) x A (Sum.inl z)
          +
            (cofiniteTargetCollapse C A (Sum.inl y) (Sum.inr ())).toReal *
              collapsedBoundaryVoltage (P := P) (X := X) x A (Sum.inr ()) := by
                rw [hvisibleCollapse]
                rw [cofiniteTargetCollapse_left_sink_toReal (p := p) (C := C) (A := A) y]
                simp [collapsedBoundaryVoltage_sink (P := P) (X := X) x A]
    _ =
        ∑ z : ({z : E // z ∉ A} ⊕ Unit),
          (cofiniteTargetCollapse C A (Sum.inl y) z).toReal *
            collapsedBoundaryVoltage (P := P) (X := X) x A z := by
              rw [Fintype.sum_sum_type]
              simp [cofiniteTargetCollapse]

/-- Helper for Theorem 19.30: the source singleton current of the collapsed boundary voltage is
the negative probabilistic boundary term. -/
private theorem collapsedBoundaryVoltage_startNetFlow_eq_neg_boundaryTerm
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} [Fintype {y : E // y ∉ A}]
    (hxA : x ∉ A) :
    netFlowOnSet
        (electricalCurrent (cofiniteTargetCollapse C A)
          (collapsedBoundaryVoltage (P := P) (X := X) x A))
        ({Sum.inl ⟨x, hxA⟩} : Set (({y : E // y ∉ A}) ⊕ Unit)) =
      - (conductance C x * escapeToSetProbability P X x A).toReal := by
  let hWalk : IsRandomWalkWithWeights p C := inferInstance
  let uA : ({y : E // y ∉ A} ⊕ Unit) → ℝ :=
    collapsedBoundaryVoltage (P := P) (X := X) x A
  let xA : {y : E // y ∉ A} := ⟨x, hxA⟩
  have huA_start : uA (Sum.inl xA) = 0 := by
    -- Proof comment: the visible start vertex carries the zero boundary datum.
    simpa [uA, xA] using
      collapsedBoundaryVoltage_start (p := p) (P := P) (X := X) x A hxA
  have huA_sink : uA (Sum.inr ()) = 1 := by
    -- Proof comment: the collapsed sink is normalized to unit voltage.
    simpa [uA] using collapsedBoundaryVoltage_sink (P := P) (X := X) x A
  have hconductance_lt_top : conductance C x < ∞ := hWalk.conductance_lt_top x
  have hconductance_ne_zero : conductance C x ≠ 0 :=
    conductance_ne_zero_of_randomWalk (p := p) (C := C) x
  have hconductance_toReal_ne_zero : (conductance C x).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨hconductance_ne_zero, hconductance_lt_top.ne⟩
  have hp_row_ne_top : (∑' z : E, p x z) ≠ ∞ := by
    rw [hWalk.isStochastic x]
    simp
  have hp_row_summable : Summable (fun z : E ↦ (p x z).toReal) :=
    ENNReal.summable_toReal hp_row_ne_top
  have hkernelNormSummable :
      Summable
        (fun z : E ↦
          (p x z).toReal *
            ‖collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z‖) := by
    -- Proof comment: the same stochastic-row bound controls the start-state averaging series.
    refine Summable.of_nonneg_of_le
      (fun z ↦ by positivity)
      (fun z ↦ by
        calc
          (p x z).toReal * ‖collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z‖
              ≤ (p x z).toReal * 1 := by
                  exact mul_le_mul_of_nonneg_left
                    (collapsedBoundaryVoltageAmbient_norm_le_one
                      (P := P) (X := X) x (A := A) z)
                    ENNReal.toReal_nonneg
          _ = (p x z).toReal := by ring)
      hp_row_summable
  have hkernelValueSummable :
      Summable
        (fun z : E ↦
          (p x z).toReal * collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) := by
    have hnorm :
        Summable
          (fun z : E ↦
            ‖(p x z).toReal *
                collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z‖) := by
      simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using
        hkernelNormSummable
    exact summable_norm_iff.mp hnorm
  have hEscapeAvg :=
    escapeToSetProbability_eq_averageCollapsedBoundaryVoltageAmbient
      (p := p) (C := C) (P := P) (X := X) x hxA
  rw [integral_discreteMatrixKernel_eq_tsum
    p hWalk.isStochasticMatrix
      (fun z : E ↦ collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z)
      x hkernelNormSummable] at hEscapeAvg
  have hscaledBoundary :
      (conductance C x * escapeToSetProbability P X x A).toReal =
        ∑' z : E,
          (C x z).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z := by
    -- Proof comment: as at an interior visible vertex, multiply the one-step average by the
    -- source conductance and rewrite the transition coefficients as conductance ratios.
    calc
      (conductance C x * escapeToSetProbability P X x A).toReal
          = (conductance C x).toReal * (escapeToSetProbability P X x A).toReal := by
              rw [ENNReal.toReal_mul]
      _ =
          (conductance C x).toReal *
            ∑' z : E,
              (p x z).toReal *
                collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z := by
                  rw [hEscapeAvg]
      _ =
          ∑' z : E,
            (conductance C x).toReal *
              ((p x z).toReal *
                collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) := by
                  rw [← tsum_mul_left]
      _ =
          ∑' z : E,
            ((conductance C x).toReal * (p x z).toReal) *
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z := by
                refine tsum_congr fun z ↦ ?_
                ring
      _ =
          ∑' z : E,
            (C x z).toReal *
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z := by
                refine tsum_congr fun z ↦ ?_
                have hterm :
                    (conductance C x).toReal * (p x z).toReal = (C x z).toReal := by
                  rw [hWalk.transition_eq, ENNReal.toReal_div]
                  field_simp [hconductance_toReal_ne_zero]
                rw [hterm]
  have hCrow_ne_top : (∑' z : E, C x z) ≠ ∞ := by
    simpa [conductance] using hconductance_lt_top.ne
  have hCrow_toReal : Summable (fun z : E ↦ (C x z).toReal) :=
    ENNReal.summable_toReal hCrow_ne_top
  have htargetSummable :
      Summable (fun z : E ↦ if z ∈ A then (C x z).toReal else 0) := by
    -- Proof comment: the target-side row sum remains dominated by the full real row from `x`.
    refine Summable.of_nonneg_of_le
      (fun z ↦ by
        by_cases hz : z ∈ A <;> simp [hz])
      (fun z ↦ by
        by_cases hz : z ∈ A <;> simp [hz])
      hCrow_toReal
  have hvisibleAmbient :
      ∑ z : {z : E // z ∉ A},
          (C x z.1).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1
        =
      ∑' z : E,
        Set.indicator {z : E | z ∉ A}
          (fun z ↦
            (C x z).toReal *
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z := by
    -- Proof comment: the visible part of the start row is the subtype row over `Aᶜ`.
    calc
      ∑ z : {z : E // z ∉ A},
          (C x z.1).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1
          =
        ∑' z : {z : E // z ∉ A},
          (C x z.1).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1 := by
              symm
              exact
                tsum_fintype
                  (f := fun z : {z : E // z ∉ A} ↦
                    (C x z.1).toReal *
                      collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1)
      _ =
          ∑' z : E,
            Set.indicator {z : E | z ∉ A}
              (fun z ↦
                (C x z).toReal *
                  collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z := by
                    simpa using
                      (tsum_subtype
                        (s := {z : E | z ∉ A})
                        (f := fun z : E ↦
                          (C x z).toReal *
                            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z))
  have hvisibleCollapse :
      ∑ z : {z : E // z ∉ A},
          (C x z.1).toReal *
            collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1
        =
      ∑ z : {z : E // z ∉ A},
          (cofiniteTargetCollapse C A (Sum.inl xA) (Sum.inl z)).toReal *
            uA (Sum.inl z) := by
    -- Proof comment: on visible vertices, the ambient owner collapses back to the visible
    -- boundary voltage.
    refine Finset.sum_congr rfl fun z _ ↦ ?_
    rw [collapsedBoundaryVoltageAmbient_eq_visibleValue
      (p := p) (P := P) (X := X) x hxA z]
    rfl
  have hvisibleIndicatorSummable :
      Summable
        (fun z : E ↦
          Set.indicator {z : E | z ∉ A}
            (fun z ↦
              (C x z).toReal *
                collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z) := by
    have hnorm :
        Summable
          (fun z : E ↦
            ‖Set.indicator {z : E | z ∉ A}
                (fun z ↦
                  (C x z).toReal *
                    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z‖) := by
      refine Summable.of_nonneg_of_le
        (fun z ↦ by positivity)
        (fun z ↦ by
          by_cases hz : z ∉ A
          · calc
              ‖Set.indicator {z : E | z ∉ A}
                  (fun z ↦
                    (C x z).toReal *
                      collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z‖
                  =
                ‖(C x z).toReal *
                    collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z‖ := by
                      simp [Set.indicator, hz]
              _ = (C x z).toReal *
                    ‖collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z‖ := by
                      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
              _ ≤ (C x z).toReal * 1 := by
                    exact mul_le_mul_of_nonneg_left
                      (collapsedBoundaryVoltageAmbient_norm_le_one
                        (P := P) (X := X) x (A := A) z)
                      ENNReal.toReal_nonneg
              _ = (C x z).toReal := by ring
          · simp [Set.indicator, hz])
        hCrow_toReal
    exact summable_norm_iff.mp hnorm
  have hboundarySplit :
      (conductance C x * escapeToSetProbability P X x A).toReal
        =
      ∑ z : {z : E // z ∉ A},
        (cofiniteTargetCollapse C A (Sum.inl xA) (Sum.inl z)).toReal * uA (Sum.inl z)
        +
      (cofiniteTargetCollapse C A (Sum.inl xA) (Sum.inr ())).toReal * uA (Sum.inr ()) := by
    -- Proof comment: rewrite the scaled ambient escape term in the same visible-plus-sink normal
    -- form as the collapsed source row.
    calc
      (conductance C x * escapeToSetProbability P X x A).toReal
          =
        ∑' z : E,
          ((Set.indicator {z : E | z ∉ A}
              (fun z ↦
                (C x z).toReal *
                  collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z)
            +
              (if z ∈ A then (C x z).toReal else 0)) := by
                rw [hscaledBoundary]
                refine tsum_congr fun z ↦ ?_
                by_cases hzA : z ∈ A
                · have hzx : z ≠ x := by
                    intro hzx
                    exact hxA (hzx ▸ hzA)
                  simp [Set.indicator, hzA, hzx, collapsedBoundaryVoltageAmbient]
                · simp [Set.indicator, hzA]
      _ =
          (∑' z : E,
            Set.indicator {z : E | z ∉ A}
              (fun z ↦
                (C x z).toReal *
                  collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z) z)
            +
              ∑' z : E, if z ∈ A then (C x z).toReal else 0 := by
                  rw [Summable.tsum_add hvisibleIndicatorSummable htargetSummable]
      _ =
          ∑ z : {z : E // z ∉ A},
            (C x z.1).toReal *
              collapsedBoundaryVoltageAmbient (P := P) (X := X) x A z.1
            +
              ∑' z : E, if z ∈ A then (C x z).toReal else 0 := by
                  rw [← hvisibleAmbient]
      _ =
          ∑ z : {z : E // z ∉ A},
            (cofiniteTargetCollapse C A (Sum.inl xA) (Sum.inl z)).toReal * uA (Sum.inl z)
            +
              (cofiniteTargetCollapse C A (Sum.inl xA) (Sum.inr ())).toReal * uA (Sum.inr ()) := by
                  rw [hvisibleCollapse]
                  rw [cofiniteTargetCollapse_left_sink_toReal (p := p) (C := C) (A := A) xA]
                  simp [huA_sink, xA]
  calc
    netFlowOnSet
        (electricalCurrent (cofiniteTargetCollapse C A)
          (collapsedBoundaryVoltage (P := P) (X := X) x A))
        ({Sum.inl ⟨x, hxA⟩} : Set (({y : E // y ∉ A}) ⊕ Unit))
        =
      netFlowAt (electricalCurrent (cofiniteTargetCollapse C A) uA) (Sum.inl xA) := by
          simp [uA, xA, netFlowOnSet]
    _ =
        ∑ z : ({y : E // y ∉ A} ⊕ Unit),
          (cofiniteTargetCollapse C A (Sum.inl xA) z).toReal * (uA (Sum.inl xA) - uA z) := by
            simp [netFlowAt, electricalCurrent]
    _ =
        - (∑ z : {z : E // z ∉ A},
            (cofiniteTargetCollapse C A (Sum.inl xA) (Sum.inl z)).toReal * uA (Sum.inl z)
            +
              (cofiniteTargetCollapse C A (Sum.inl xA) (Sum.inr ())).toReal *
                uA (Sum.inr ())) := by
                  rw [Fintype.sum_sum_type]
                  simp [huA_start, huA_sink]
                  ring
    _ = - (conductance C x * escapeToSetProbability P X x A).toReal := by
          rw [hboundarySplit]

/-- Helper for Theorem 19.30: split a finite sum over `A0 ∪ A1` into the disjoint pieces
`A0 \ A1` and `A1`. -/
private theorem sum_union_eq_sum_diff_add_sum_local
    {α : Type*} [Fintype α] (A0 A1 : Set α) (f : α → ℝ) :
    let A : Set α := A0 ∪ A1
    (∑ x : A, f x) = (∑ x : ((A0 \ A1 : Set α)), f x) + ∑ x : A1, f x := by
  -- Proof comment: reindex the union along the canonical equivalence with the disjoint sum of the
  -- left-only part and the right boundary piece.
  set A : Set α := A0 ∪ A1
  have hdisj : Disjoint (A0 \ A1 : Set α) A1 := by
    rw [Set.disjoint_left]
    intro x hx0 hx1
    exact hx0.2 hx1
  have hunion : ((A0 \ A1 : Set α) ∪ A1) = A := by
    ext x
    simp [A]
  let e : ((A0 \ A1 : Set α) ⊕ A1) ≃ A :=
    (Equiv.Set.union hdisj).symm.trans <| Equiv.setCongr hunion
  calc
    ∑ x : A, f x = ∑ z : ((A0 \ A1 : Set α) ⊕ A1), f (e z) := by
      simpa using (Equiv.sum_comp e (fun x : A ↦ f x)).symm
    _ = (∑ x : ((A0 \ A1 : Set α)), f (e (Sum.inl x))) + ∑ x : A1, f (e (Sum.inr x)) := by
          rw [Fintype.sum_sum_type]
    _ = (∑ x : ((A0 \ A1 : Set α)), f x) + ∑ x : A1, f x := by
          simp [e]

/-- Helper for Theorem 19.30: the net flow through the union of two distinct singleton boundary
vertices is the sum of their individual net flows. -/
private theorem netFlowOnSet_union_singletons
    {α : Type*} [Fintype α]
    (I : α → α → ℝ) (a b : α) (hab : a ≠ b) :
    netFlowOnSet I ({a} ∪ {b} : Set α) = netFlowAt I a + netFlowAt I b := by
  -- Proof comment: work with the canonical subtype owner of the two-point boundary and identify
  -- its `Finset.univ` with the explicit doubleton `{a, b}` inside that subtype.
  set S : Set α := ({a} ∪ {b} : Set α)
  let aS : S := ⟨a, by simp [S]⟩
  let bS : S := ⟨b, by simp [S]⟩
  have habS : aS ≠ bS := by
    intro h
    apply hab
    exact congrArg Subtype.val h
  have huniv :
      @Finset.univ S (@Subtype.fintype α (Membership.mem S)
        (fun x ↦ Classical.propDecidable (x ∈ S)) inferInstance) = {aS, bS} := by
    -- Proof comment: every point of the boundary subtype is either `a` or `b`.
    ext x
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    have hx : x.1 = a ∨ x.1 = b := by
      have hxmem : x.1 ∈ S := x.2
      simpa [S, or_comm] using hxmem
    rcases hx with hxa | hxb
    · left
      apply Subtype.ext
      simpa [aS] using hxa
    · right
      apply Subtype.ext
      simpa [bS] using hxb
  rw [show netFlowOnSet I ({a} ∪ {b} : Set α) = netFlowOnSet I S by simp [S]]
  rw [netFlowOnSet_def]
  change
    Finset.sum
      (@Finset.univ S (@Subtype.fintype α (Membership.mem S)
        (fun x ↦ Classical.propDecidable (x ∈ S)) inferInstance))
      (fun x ↦ netFlowAt I x) = netFlowAt I a + netFlowAt I b
  rw [huniv]
  simp [habS, aS, bS]

/-- Helper for Theorem 19.30: the sink current of the collapsed boundary voltage equals the
probabilistic boundary term `conductance C x * escapeToSetProbability P X x A`. -/
private theorem collapsedBoundaryVoltage_sinkNetFlow_eq_boundaryTerm
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} [Fintype {y : E // y ∉ A}]
    (hAfinite : Aᶜ.Finite) (hxA : x ∉ A) :
    netFlowOnSet
        (electricalCurrent (cofiniteTargetCollapse C A)
          (collapsedBoundaryVoltage (P := P) (X := X) x A))
        ({Sum.inr ()} : Set (({y : E // y ∉ A}) ⊕ Unit)) =
      (conductance C x * escapeToSetProbability P X x A).toReal := by
  let uA : ({y : E // y ∉ A} ⊕ Unit) → ℝ :=
    collapsedBoundaryVoltage (P := P) (X := X) x A
  let xA : {y : E // y ∉ A} := ⟨x, hxA⟩
  let A0 : Set (({y : E // y ∉ A}) ⊕ Unit) := {Sum.inl xA}
  let A1 : Set (({y : E // y ∉ A}) ⊕ Unit) := {Sum.inr ()}
  have hPotential :
      IsElectricalPotential (cofiniteTargetCollapse C A) (A0 ∪ A1) uA := by
    -- Proof comment: the weighted row identities close Kirchhoff's law at every visible interior
    -- vertex of the collapsed network.
    exact
      cofiniteTargetCollapse_isElectricalPotential_of_weightedSum
        (p := p) (C := C) x hAfinite hxA (u := uA) fun y hyx ↦ by
          simpa [uA] using
            collapsedBoundaryVoltage_weightedRow
              (p := p) (C := C) (P := P) (X := X) x hxA y hyx
  have hBoundaryFlowZero :
      netFlowOnSet (electricalCurrent (cofiniteTargetCollapse C A) uA) (A0 ∪ A1) = 0 := by
    -- Proof comment: an electrical potential is a flow outside the boundary, so the total
    -- boundary current vanishes.
    exact
      IsFlowOutside.netFlowOnSet_eq_zero
        (show IsFlowOutside (A0 ∪ A1)
          (electricalCurrent (cofiniteTargetCollapse C A) uA) from hPotential)
  have hStart :
      netFlowOnSet (electricalCurrent (cofiniteTargetCollapse C A) uA) A0
        =
      - (conductance C x * escapeToSetProbability P X x A).toReal := by
    -- Proof comment: the source singleton current is the negative of the probabilistic boundary
    -- term.
    simpa [A0, uA] using
      collapsedBoundaryVoltage_startNetFlow_eq_neg_boundaryTerm
        (p := p) (C := C) (P := P) (X := X) x hxA
  have hBoundarySplit :
      netFlowOnSet (electricalCurrent (cofiniteTargetCollapse C A) uA) (A0 ∪ A1) =
        netFlowOnSet (electricalCurrent (cofiniteTargetCollapse C A) uA) A0 +
          netFlowOnSet (electricalCurrent (cofiniteTargetCollapse C A) uA) A1 := by
    -- Proof comment: the boundary is the disjoint union of the start singleton and the sink
    -- singleton, so we reindex the union as the sum type `A0 ⊕ A1` and then evaluate the two
    -- singleton contributions separately.
    let I : ({y : E // y ∉ A} ⊕ Unit) → ({y : E // y ∉ A} ⊕ Unit) → ℝ :=
      electricalCurrent (cofiniteTargetCollapse C A) uA
    have hdisj : Disjoint A0 A1 := by
      rw [Set.disjoint_left]
      intro z hz0 hz1
      simp [A0, A1] at hz0 hz1
      cases hz0
      cases hz1
    have hA0sum :
        netFlowOnSet I A0 = netFlowAt I (Sum.inl xA) := by
      simp [netFlowOnSet_def, A0]
    have hA1sum :
        netFlowOnSet I A1 = netFlowAt I (Sum.inr ()) := by
      simp [netFlowOnSet_def, A1]
    have hUnionSum :
        netFlowOnSet I (A0 ∪ A1) = netFlowAt I (Sum.inl xA) + netFlowAt I (Sum.inr ()) := by
      -- Proof comment: use the owner-stable two-singleton formula to evaluate the total boundary
      -- flow without switching between equivalent subtype owners.
      simpa [A0, A1] using
        (netFlowOnSet_union_singletons I (Sum.inl xA) (Sum.inr ()) (by simp))
    rw [hUnionSum, hA0sum, hA1sum]
  have hSink :
      netFlowOnSet (electricalCurrent (cofiniteTargetCollapse C A) uA) A1 =
        (conductance C x * escapeToSetProbability P X x A).toReal := by
    -- Proof comment: the zero total boundary flow and the already computed start contribution
    -- force the sink contribution to be the positive boundary term.
    rw [hBoundarySplit] at hBoundaryFlowZero
    linarith [hStart, hBoundaryFlowZero]
  simpa [netFlowOnSet_def, A1, uA] using hSink


/-- Helper for Theorem 19.30: each cofinite boundary conductance term is the finite effective
conductance from the visible start vertex to the collapsed sink. -/
private theorem cofiniteBoundaryConductance_eq_collapsedEffectiveConductance
    {p : E → E → ℝ≥0∞} {C : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    [IsRandomWalkWithWeights p C]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    (x : E) {A : Set E} [Fintype {y : E // y ∉ A}]
    (hAfinite : Aᶜ.Finite) (hxA : x ∉ A) :
    conductance C x * escapeToSetProbability P X x A =
      ENNReal.ofReal
        (effectiveConductance (cofiniteTargetCollapse C A)
          ({Sum.inl ⟨x, hxA⟩} : Set ({y : E // y ∉ A} ⊕ Unit)) ({Sum.inr ()})) := by
  -- Route correction: the raw complement carrier forgot the target set. The correct owner is the
  -- sink-collapsed carrier `({y // y ∉ A}) ⊕ Unit`, and the remaining work is to identify the
  -- cofinite boundary term with the boundary current of its unit-voltage problem.
  let uA : ({y : E // y ∉ A} ⊕ Unit) → ℝ :=
    collapsedBoundaryVoltage (P := P) (X := X) x A
  have huA_start : uA (Sum.inl ⟨x, hxA⟩) = 0 := by
    -- Proof comment: the visible start vertex is the zero boundary datum of the collapsed
    -- Dirichlet problem.
    simpa [uA] using collapsedBoundaryVoltage_start (p := p) (P := P) (X := X) x A hxA
  have huA_sink : uA (Sum.inr ()) = 1 := by
    -- Proof comment: the sink is normalized to unit voltage.
    simpa [uA] using collapsedBoundaryVoltage_sink (P := P) (X := X) x A
  let A0 : Set (({y : E // y ∉ A}) ⊕ Unit) := {Sum.inl ⟨x, hxA⟩}
  let A1 : Set (({y : E // y ∉ A}) ⊕ Unit) := {Sum.inr ()}
  have hA0 : A0.Nonempty := ⟨Sum.inl ⟨x, hxA⟩, by simp [A0]⟩
  have hA1 : A1.Nonempty := ⟨Sum.inr (), by simp [A1]⟩
  have hdisj : Disjoint A0 A1 := by
    -- Proof comment: the visible start vertex and the sink are distinct vertices of the collapsed
    -- carrier.
    rw [Set.disjoint_singleton_right]
    simp [A0, A1]
  have hBoundarySet :
      ({Sum.inl ⟨x, hxA⟩, Sum.inr ()} : Set (({y : E // y ∉ A}) ⊕ Unit)) = A0 ∪ A1 := by
    -- Proof comment: the two-point boundary used by the electrical-potential helper is exactly
    -- the union of the source singleton and the sink singleton.
    ext a
    cases a <;> simp [A0, A1]
  have hPotential :
      IsElectricalPotential (cofiniteTargetCollapse C A) (A0 ∪ A1) uA := by
    -- Proof comment: the weighted row identity on each visible interior vertex turns the
    -- collapsed boundary-hit voltage into an electrical potential outside `{x, sink}`.
    rw [← hBoundarySet]
    exact
      (cofiniteTargetCollapse_isElectricalPotential_of_weightedSum
        (p := p) (C := C) x hAfinite hxA (u := uA) fun y hyx ↦ by
          simpa [uA] using
            collapsedBoundaryVoltage_weightedRow
              (p := p) (C := C) (P := P) (X := X) x hxA y hyx)
  have huA_zero : Set.EqOn uA (fun _ : (({y : E // y ∉ A}) ⊕ Unit) ↦ 0) A0 := by
    -- Proof comment: on the source singleton, the collapsed voltage is already normalized to `0`.
    intro a ha
    have ha' : a = Sum.inl ⟨x, hxA⟩ := by
      simpa [A0] using ha
    subst ha'
    exact huA_start
  have huA_one : Set.EqOn uA (fun _ : (({y : E // y ∉ A}) ⊕ Unit) ↦ 1) A1 := by
    -- Proof comment: on the sink singleton, the collapsed voltage is the unit boundary datum.
    intro a ha
    have ha' : a = Sum.inr () := by
      simpa [A1] using ha
    subst ha'
    exact huA_sink
  have hEff :
      effectiveConductance (cofiniteTargetCollapse C A) A0 A1 =
        netFlowOnSet (electricalCurrent (cofiniteTargetCollapse C A) uA) A1 := by
    -- Proof comment: Definition 19.17 identifies the finite effective conductance with the
    -- boundary current of any unit-voltage electrical potential.
    exact
      effectiveConductance_eq_netFlowOnSet_electricalCurrent
        hA0 hA1 hdisj hPotential huA_zero huA_one
  have hEscape_le_one : escapeToSetProbability P X x A ≤ 1 := by
    -- Proof comment: the escape-to-set event is measured under a probability measure.
    rw [escapeToSetProbability_def]
    exact prob_le_one
  have hEscape_ne_top : escapeToSetProbability P X x A ≠ ∞ :=
    ne_of_lt (lt_of_le_of_lt hEscape_le_one ENNReal.one_lt_top)
  have hBoundary_ne_top :
      conductance C x * escapeToSetProbability P X x A ≠ ∞ := by
    exact
      ENNReal.mul_ne_top
        (IsRandomWalkWithWeights.conductance_lt_top
          (h := (inferInstance : IsRandomWalkWithWeights p C)) x).ne
        hEscape_ne_top
  -- Proof comment: convert the boundary current formula back to `ENNReal` after identifying the
  -- sink current with the probabilistic boundary term.
  calc
    conductance C x * escapeToSetProbability P X x A
        = ENNReal.ofReal
            ((conductance C x * escapeToSetProbability P X x A).toReal) := by
              exact (ENNReal.ofReal_toReal hBoundary_ne_top).symm
    _ = ENNReal.ofReal
          (netFlowOnSet (electricalCurrent (cofiniteTargetCollapse C A) uA) A1) := by
            rw [← collapsedBoundaryVoltage_sinkNetFlow_eq_boundaryTerm
              (p := p) (C := C) (P := P) (X := X) x hAfinite hxA]
    _ = ENNReal.ofReal (effectiveConductance (cofiniteTargetCollapse C A) A0 A1) := by
          rw [hEff]
    _ = ENNReal.ofReal
          (effectiveConductance (cofiniteTargetCollapse C A)
            ({Sum.inl ⟨x, hxA⟩} : Set ({y : E // y ∉ A} ⊕ Unit)) ({Sum.inr ()})) := by
              rfl

/-- Helper for Theorem 19.30: a cofinite target avoiding `x` gives one finite-boundary
conductance term, and Rayleigh monotonicity should compare those terms under `C' ≤ C`. -/
private theorem cofiniteBoundaryConductance_mono_of_edgeWeights_le
    {p p' : E → E → ℝ≥0∞} {C C' : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    {P' : E → ProbabilityMeasure Ω'} {X' : ℕ → Ω' → E}
    [IsRandomWalkWithWeights p C] [IsRandomWalkWithWeights p' C']
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p' ^ n) P' X']
    (hCC' : ∀ x y : E, C' x y ≤ C x y)
    (x : E) {A : Set E} (hAfinite : Aᶜ.Finite) (hxA : x ∉ A) :
    conductance C' x * escapeToSetProbability P' X' x A ≤
      conductance C x * escapeToSetProbability P X x A := by
  -- Route correction: the raw complement carrier forgot the target boundary. The remaining bridge
  -- must instead rewrite both sides through `cofiniteTargetCollapse C A`, where `A` is kept as a
  -- sink, and then apply Rayleigh on that common finite carrier.
  classical
  letI : Fintype {y : E // y ∉ A} := hAfinite.fintype
  let xA : {y : E // y ∉ A} := ⟨x, hxA⟩
  let A0 : Set ({y : E // y ∉ A} ⊕ Unit) := {Sum.inl xA}
  let A1 : Set ({y : E // y ∉ A} ⊕ Unit) := {Sum.inr ()}
  have hA0 : A0.Nonempty := ⟨Sum.inl xA, by simp [A0]⟩
  have hA1 : A1.Nonempty := ⟨Sum.inr (), by simp [A1]⟩
  have hdisj : Disjoint A0 A1 := by
    rw [Set.disjoint_singleton_right]
    simp [A0, A1]
  rw [cofiniteBoundaryConductance_eq_collapsedEffectiveConductance
    (p := p') (C := C') (P := P') (X := X') x hAfinite hxA]
  rw [cofiniteBoundaryConductance_eq_collapsedEffectiveConductance
    (p := p) (C := C) (P := P) (X := X) x hAfinite hxA]
  exact
    ENNReal.ofReal_le_ofReal <|
      rayleigh_monotonicity_principle
        (hC_symm := cofiniteTargetCollapse_symmetric (p := p) (C := C) A)
        (hC_finite := cofiniteTargetCollapse_conductance_lt_top
          (p := p) (C := C) hAfinite)
        (hC'_symm := cofiniteTargetCollapse_symmetric (p := p') (C := C') A)
        (hC'_finite := cofiniteTargetCollapse_conductance_lt_top
          (p := p') (C := C') hAfinite)
        (hA0 := hA0) (hA1 := hA1) (hdisj := hdisj)
        (hCC' := cofiniteTargetCollapse_mono A hCC')

theorem effectiveConductanceToInfinity_le_of_edgeWeights_le_at_state
    {p p' : E → E → ℝ≥0∞} {C C' : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    {P' : E → ProbabilityMeasure Ω'} {X' : ℕ → Ω' → E}
    [IsRandomWalkWithWeights p C] [IsRandomWalkWithWeights p' C']
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p' ^ n) P' X']
    (hCC' : ∀ x y : E, C' x y ≤ C x y) (x : E) :
    effectiveConductanceToInfinity C' P' X' x ≤ effectiveConductanceToInfinity C P X x := by
  -- Route correction: move the cofinite `sInf` to an indexed `iInf` over admissible targets and
  -- compare the resulting finite-boundary terms pointwise. The only missing input is the
  -- cofinite-boundary Rayleigh bridge isolated above.
  rw [effectiveConductanceToInfinity_eq_iInf_cofiniteTargets
    (p := p') (C := C') (P := P') (X := X') x]
  rw [effectiveConductanceToInfinity_eq_iInf_cofiniteTargets
    (p := p) (C := C) (P := P) (X := X) x]
  have hTargets_nonempty : Nonempty {A : Set E // Aᶜ.Finite ∧ x ∉ A} := by
    refine ⟨⟨{x}ᶜ, ?_, by simp⟩⟩
    simp
  letI := hTargets_nonempty
  by_cases hC'0 : conductance C' x = 0
  · -- Proof comment: zero total conductance kills every boundary term, so the left side vanishes.
    simp [hC'0]
  · have hC'neTop : conductance C' x ≠ ∞ :=
      (IsRandomWalkWithWeights.conductance_lt_top
        (h := (inferInstance : IsRandomWalkWithWeights p' C')) x).ne
    calc
      conductance C' x *
          ⨅ A : {A : Set E // Aᶜ.Finite ∧ x ∉ A},
            escapeToSetProbability P' X' x A.1
          =
        ⨅ A : {A : Set E // Aᶜ.Finite ∧ x ∉ A},
          conductance C' x * escapeToSetProbability P' X' x A.1 := by
            rw [ENNReal.mul_iInf_of_ne hC'0 hC'neTop]
      _ ≤
          ⨅ A : {A : Set E // Aᶜ.Finite ∧ x ∉ A},
            conductance C x * escapeToSetProbability P X x A.1 := by
              refine iInf_mono ?_
              intro A
              exact
                cofiniteBoundaryConductance_mono_of_edgeWeights_le
                  (p := p) (p' := p') (C := C) (C' := C')
                  (P := P) (X := X) (P' := P') (X' := X')
                  hCC' x A.2.1 A.2.2
      _ =
          conductance C x *
            ⨅ A : {A : Set E // Aᶜ.Finite ∧ x ∉ A},
              escapeToSetProbability P X x A.1 := by
                by_cases hC0 : conductance C x = 0
                · -- Proof comment: if the ambient conductance at `x` vanishes, every boundary
                  -- term on the right is already `0`, so the comparison closes by simplification.
                  simp [hC0]
                · have hCneTop : conductance C x ≠ ∞ :=
                    (IsRandomWalkWithWeights.conductance_lt_top
                      (h := (inferInstance : IsRandomWalkWithWeights p C)) x).ne
                  rw [ENNReal.mul_iInf_of_ne hC0 hCneTop]

-- Proof sketch: compare effective conductance to infinity for the two conductance families using
-- Rayleigh monotonicity, then apply the recurrence criterion of Theorem 19.25 to transfer
-- recurrence from the walk with weights `C` to the walk with weights `C'`.
/-- Theorem 19.30: if `C' x y ≤ C x y` for every edge pair and the Markov chain with weights `C`
is recurrent, then the Markov chain with weights `C'` is also recurrent. -/
theorem randomWalkWithWeights_recurrent_of_edgeWeights_le
    {p p' : E → E → ℝ≥0∞} {C C' : E → E → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    {P' : E → ProbabilityMeasure Ω'} {X' : ℕ → Ω' → E}
    [IsRandomWalkWithWeights p C] [IsRandomWalkWithWeights p' C']
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p' ^ n) P' X']
    (hCC' : ∀ x y : E, C' x y ≤ C x y)
    (hrec : IsRecurrentMarkovChain P X) :
    IsRecurrentMarkovChain P' X' := by
  intro x
  -- Proof comment: convert recurrence at `x` into the vanishing of the effective conductance to
  -- infinity, then use the statewise monotonicity helper to pass the zero bound to `C'`.
  rw [isRecurrentState_iff_effectiveConductanceToInfinity_eq_zero
    (p := p') (C := C') (P := P') (X := X') (x₁ := x)]
  have hxrec :
      effectiveConductanceToInfinity C P X x = 0 := by
    exact
      (isRecurrentState_iff_effectiveConductanceToInfinity_eq_zero
        (p := p) (C := C) (P := P) (X := X) (x₁ := x)).mp (hrec x)
  refine le_antisymm ?_ bot_le
  calc
    effectiveConductanceToInfinity C' P' X' x
        ≤ effectiveConductanceToInfinity C P X x :=
          effectiveConductanceToInfinity_le_of_edgeWeights_le_at_state
            (p := p) (p' := p') (C := C) (C' := C')
            (P := P) (X := X) (P' := P') (X' := X') hCC' x
    _ = 0 := hxrec

-- Proof sketch: unfold `simpleGraphWeights`; if `H` is a subgraph of `G`, adjacency in `H`
-- implies adjacency in `G`, so the indicator weight of each edge in `H` is bounded by the
-- corresponding indicator weight in `G`.
/-- Unit edge weights are pointwise monotone under passage to a simple subgraph. -/
theorem simpleGraphWeights_le_of_isSubgraph {V : Type u}
    (G H : SimpleGraph V) (hHG : H ≤ G) :
    ∀ x y : V, simpleGraphWeights H x y ≤ simpleGraphWeights G x y := by
  intro x y
  -- Proof comment: split on adjacency in the smaller graph `H`; if it is present, `hHG` moves it
  -- to `G`, and if it is absent the left-hand unit weight is already `0`.
  by_cases hxyH : H.Adj x y
  · have hxyG : G.Adj x y := hHG hxyH
    simp [simpleGraphWeights, hxyH, hxyG]
  · by_cases hxyG : G.Adj x y
    · simp [simpleGraphWeights, hxyH, hxyG]
    · simp [simpleGraphWeights, hxyH, hxyG]


/-- Helper for Theorem 19.30: after transporting the subtype complement of `A : Set s` into the
ambient complement of `((↑) '' A) ∪ sᶜ`, each collapsed conductance in the subgraph network is
bounded by the corresponding collapsed conductance in the ambient network. -/
private theorem cofiniteTargetCollapse_subgraph_le_transportedAmbient
    {G : SimpleGraph E} {s : Set E} [DiscreteMeasurableSpace ↑s] {G' : SimpleGraph s}
    {p : E → E → ℝ≥0∞} {p' : s → s → ℝ≥0∞}
    [IsSimpleRandomWalk p G] [IsSimpleRandomWalk p' G']
    (hsub : G' ≤ SimpleGraph.induce s G) {A : Set s}
    (u v : ({z : s // z ∉ A} ⊕ Unit)) :
    cofiniteTargetCollapse (simpleGraphWeights G') A u v ≤
      cofiniteTargetCollapse (simpleGraphWeights G) (((↑) '' A) ∪ sᶜ : Set E)
        ((Equiv.sumCongr (ambientTargetSubtypeComplEquiv (A := A)) (Equiv.refl Unit)) u)
        ((Equiv.sumCongr (ambientTargetSubtypeComplEquiv (A := A)) (Equiv.refl Unit)) v) := by
  let e :
      ({z : s // z ∉ A} ⊕ Unit) ≃
        ({z : E // z ∉ (((↑) '' A) ∪ sᶜ : Set E)} ⊕ Unit) :=
    Equiv.sumCongr (ambientTargetSubtypeComplEquiv (A := A)) (Equiv.refl Unit)
  rcases u with y | u0 <;> rcases v with z | v0
  · -- Proof comment: on visible-visible edges, pointwise subgraph monotonicity is enough.
    simpa [e, simpleGraphWeights_induce_apply] using
      simpleGraphWeights_le_of_isSubgraph (SimpleGraph.induce s G) G' hsub y z
  · -- Proof comment: compare the subgraph sink edge first with the induced graph, then use the
    -- ambient sink-edge transport already isolated above.
    have hmono :
        cofiniteTargetCollapse (simpleGraphWeights G') A (Sum.inl y) (Sum.inr ()) ≤
          cofiniteTargetCollapse (simpleGraphWeights (SimpleGraph.induce s G)) A
            (Sum.inl y) (Sum.inr ()) := by
      exact
        cofiniteTargetCollapse_mono A
          (simpleGraphWeights_le_of_isSubgraph (SimpleGraph.induce s G) G' hsub)
          (Sum.inl y) (Sum.inr ())
    exact le_trans hmono <| by
      simpa [e] using
        cofiniteTargetCollapse_sinkEdge_induced_le_ambient (s := s) G (A := A) y
  · -- Proof comment: use symmetry to reduce the sink-visible branch to the visible-sink branch.
    have hmono :
        cofiniteTargetCollapse (simpleGraphWeights G') A (Sum.inl z) (Sum.inr ()) ≤
          cofiniteTargetCollapse (simpleGraphWeights (SimpleGraph.induce s G)) A
            (Sum.inl z) (Sum.inr ()) := by
      exact
        cofiniteTargetCollapse_mono A
          (simpleGraphWeights_le_of_isSubgraph (SimpleGraph.induce s G) G' hsub)
          (Sum.inl z) (Sum.inr ())
    have hvisibleSink :
        cofiniteTargetCollapse (simpleGraphWeights G') A (Sum.inl z) (Sum.inr ()) ≤
          cofiniteTargetCollapse (simpleGraphWeights G) (((↑) '' A) ∪ sᶜ : Set E)
            (e (Sum.inl z)) (e (Sum.inr ())) := by
      exact le_trans hmono <| by
        simpa [e] using
          cofiniteTargetCollapse_sinkEdge_induced_le_ambient (s := s) G (A := A) z
    calc
      cofiniteTargetCollapse (simpleGraphWeights G') A (Sum.inr ()) (Sum.inl z)
          = cofiniteTargetCollapse (simpleGraphWeights G') A (Sum.inl z) (Sum.inr ()) := by
              simpa using
                (cofiniteTargetCollapse_symmetric
                  (p := p') (C := simpleGraphWeights G') A (Sum.inr ()) (Sum.inl z))
      _ ≤
          cofiniteTargetCollapse (simpleGraphWeights G) (((↑) '' A) ∪ sᶜ : Set E)
            (e (Sum.inl z)) (e (Sum.inr ())) := hvisibleSink
      _ =
          cofiniteTargetCollapse (simpleGraphWeights G) (((↑) '' A) ∪ sᶜ : Set E)
            (e (Sum.inr ())) (e (Sum.inl z)) := by
              symm
              simpa using
                (cofiniteTargetCollapse_symmetric
                  (p := p) (C := simpleGraphWeights G)
                  (((↑) '' A) ∪ sᶜ : Set E) (e (Sum.inr ())) (e (Sum.inl z)))
  · -- Proof comment: both collapsed networks have zero sink loops.
    simp [cofiniteTargetCollapse]

/-- Helper for Theorem 19.30: reindexing a finite conductance family along an equivalence preserves
the row conductance at corresponding vertices. -/
private theorem conductance_comp_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (D : β → β → ℝ≥0∞) (u : α) :
    conductance (fun a b ↦ D (e a) (e b)) u = conductance D (e u) := by
  -- Proof comment: the row sum is unchanged after reindexing the finite target type by `e`.
  unfold conductance
  rw [tsum_fintype, tsum_fintype]
  simpa using Equiv.sum_comp e (fun b : β ↦ D (e u) b)

/-- Helper for Theorem 19.30: reindexing a finite network along an equivalence preserves the
Dirichlet energy of a transported potential. -/
private theorem dirichletEnergy_comp_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (D : β → β → ℝ≥0∞) (u : β → ℝ) :
    dirichletEnergy (fun a b ↦ D (e a) (e b)) (fun a ↦ u (e a)) =
      dirichletEnergy D u := by
  -- Proof comment: reindex both finite sums along `e`; the pulled-back potential has the same
  -- edge differences after the carrier relabeling.
  unfold dirichletEnergy
  calc
    (1 / 2 : ℝ) *
        ∑ a : α, ∑ b : α, (D (e a) (e b)).toReal * (u (e a) - u (e b)) ^ (2 : ℕ)
        =
      (1 / 2 : ℝ) *
        ∑ a : α, ∑ b : β, (D (e a) b).toReal * (u (e a) - u b) ^ (2 : ℕ) := by
          congr 1
          refine Finset.sum_congr rfl fun a _ ↦ ?_
          simpa using
            Equiv.sum_comp e
              (fun b : β ↦ (D (e a) b).toReal * (u (e a) - u b) ^ (2 : ℕ))
    _ =
      (1 / 2 : ℝ) *
        ∑ a : β, ∑ b : β, (D a b).toReal * (u a - u b) ^ (2 : ℕ) := by
          congr 1
          simpa using
            Equiv.sum_comp e
              (fun a : β ↦ ∑ b : β, (D a b).toReal * (u a - u b) ^ (2 : ℕ))

/-- Helper for Theorem 19.30: finite effective conductance is invariant under reindexing the
carrier by an equivalence, provided the boundary sets are transported by the same equivalence. -/
private theorem effectiveConductance_comp_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (D : β → β → ℝ≥0∞) (A0 A1 : Set α) :
    effectiveConductance (fun a b ↦ D (e a) (e b)) A0 A1 =
      effectiveConductance D (e '' A0) (e '' A1) := by
  let Dpull : α → α → ℝ≥0∞ := fun a b ↦ D (e a) (e b)
  let Sα : Set ℝ :=
    dirichletEnergy Dpull ''
      {v : α → ℝ | Set.EqOn v (fun _ : α ↦ 0) A0 ∧ Set.EqOn v (fun _ : α ↦ 1) A1}
  let Sβ : Set ℝ :=
    dirichletEnergy D ''
      {v : β → ℝ | Set.EqOn v (fun _ : β ↦ 0) (e '' A0) ∧ Set.EqOn v (fun _ : β ↦ 1) (e '' A1)}
  have hSets : Sα = Sβ := by
    -- Proof comment: transporting admissible potentials across `e` preserves both the boundary
    -- conditions and the Dirichlet energy, so the two infimum sets coincide.
    ext r
    constructor
    · rintro ⟨v, ⟨hv0, hv1⟩, rfl⟩
      refine ⟨fun b ↦ v (e.symm b), ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro b hb
          rcases hb with ⟨a, ha, rfl⟩
          simpa using hv0 ha
        · intro b hb
          rcases hb with ⟨a, ha, rfl⟩
          simpa using hv1 ha
      · symm
        simpa [Dpull] using
          (dirichletEnergy_comp_equiv
            (e := e) (D := D) (u := fun b ↦ v (e.symm b)))
    · rintro ⟨v, ⟨hv0, hv1⟩, rfl⟩
      refine ⟨fun a ↦ v (e a), ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro a ha
          exact hv0 ⟨a, ha, rfl⟩
        · intro a ha
          exact hv1 ⟨a, ha, rfl⟩
      · simpa [Dpull] using
          (dirichletEnergy_comp_equiv (e := e) (D := D) (u := v))
  -- Proof comment: once the admissible energy sets agree literally, the defining infima agree.
  unfold effectiveConductance
  simpa [Dpull, Sα, Sβ] using congrArg sInf hSets

/-- Helper for Theorem 19.30: splitting the ambient visible vertices by membership in `s`
separates the pullback-visible vertices from the extra ambient-visible vertices outside `s`. -/
private abbrev ambientVisibleEquivPullbackSum
    {s : Set E} (B : Set E) :
    {z : E // z ∉ B} ≃
      ({z : s // z ∉ (Subtype.val ⁻¹' B : Set s)} ⊕ {z : E // z ∉ B ∧ z ∉ s}) := by
  classical
  refine
    { toFun := fun y =>
        if hy : y.1 ∈ s then
          Sum.inl ⟨⟨y.1, hy⟩, by simpa using y.2⟩
        else
          Sum.inr ⟨y.1, y.2, hy⟩
      invFun := fun z =>
        match z with
        | Sum.inl y => ⟨y.1.1, by simpa using y.2⟩
        | Sum.inr y => ⟨y.1, y.2.1⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro y
    by_cases hy : y.1 ∈ s
    · simp [hy]
    · simp [hy]
  · intro z
    rcases z with y | y
    · have hy : y.1.1 ∈ s := y.1.2
      simp [hy]
    · simp [y.2.2]

/-- Helper for Theorem 19.30: adjoining an isolated right summand does not change the Dirichlet
energy because only the left-left conductances contribute. -/
private theorem dirichletEnergy_sumRightZero
    {α β : Type*} [Fintype α] [Fintype β]
    (D : α → α → ℝ≥0∞) (u : α ⊕ β → ℝ) :
    dirichletEnergy
        (fun x y : α ⊕ β =>
          match x, y with
          | Sum.inl a, Sum.inl b => D a b
          | _, _ => 0) u =
      dirichletEnergy D (fun a ↦ u (Sum.inl a)) := by
  -- Proof comment: every edge meeting the right summand has conductance `0`, so the finite
  -- double sum collapses to the left-left block.
  unfold dirichletEnergy
  rw [Fintype.sum_sum_type]
  simp [Fintype.sum_sum_type]

/-- Helper for Theorem 19.30: adding isolated vertices on the right does not change effective
conductance when both boundary sets live on the original left carrier. -/
private theorem effectiveConductance_sumRightZero_eq
    {α β : Type*} [Fintype α] [Fintype β]
    (D : α → α → ℝ≥0∞) (A0 A1 : Set α) :
    effectiveConductance
        (fun x y : α ⊕ β =>
          match x, y with
          | Sum.inl a, Sum.inl b => D a b
          | _, _ => 0)
        (Sum.inl '' A0) (Sum.inl '' A1) =
      effectiveConductance D A0 A1 := by
  let Dsum : (α ⊕ β) → (α ⊕ β) → ℝ≥0∞ :=
    fun x y =>
      match x, y with
      | Sum.inl a, Sum.inl b => D a b
      | _, _ => 0
  let Ssum : Set ℝ :=
    dirichletEnergy Dsum ''
      {u : (α ⊕ β) → ℝ |
        Set.EqOn u (fun _ : α ⊕ β ↦ 0) (Sum.inl '' A0) ∧
          Set.EqOn u (fun _ : α ⊕ β ↦ 1) (Sum.inl '' A1)}
  let S : Set ℝ :=
    dirichletEnergy D ''
      {u : α → ℝ | Set.EqOn u (fun _ : α ↦ 0) A0 ∧ Set.EqOn u (fun _ : α ↦ 1) A1}
  have hSets : Ssum = S := by
    -- Proof comment: restriction to the left carrier and extension by `0` on the isolated right
    -- carrier preserve both boundary conditions and Dirichlet energy.
    ext r
    constructor
    · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
      refine ⟨fun a ↦ u (Sum.inl a), ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro a ha
          exact hu0 ⟨a, ha, rfl⟩
        · intro a ha
          exact hu1 ⟨a, ha, rfl⟩
      · simpa [Ssum, S, Dsum] using (dirichletEnergy_sumRightZero D u).symm
    · rintro ⟨u, ⟨hu0, hu1⟩, rfl⟩
      refine ⟨Sum.elim u (fun _ : β ↦ 0), ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · intro z hz
          rcases hz with ⟨a, ha, rfl⟩
          simpa using hu0 ha
        · intro z hz
          rcases hz with ⟨a, ha, rfl⟩
          simpa using hu1 ha
      · simpa [Ssum, S, Dsum] using
          (dirichletEnergy_sumRightZero D (Sum.elim u (fun _ : β ↦ 0)))
  -- Proof comment: once the admissible energy sets agree, their defining infima agree as well.
  unfold effectiveConductance
  simpa [Dsum, Ssum, S] using congrArg sInf hSets

/-- Helper for Theorem 19.30: pulling back an ambient cofinite target along the subtype coercion
keeps the complement finite on the subtype carrier. -/
private theorem pullbackTarget_compl_finite
    {s : Set E} {B : Set E} (hBfinite : Bᶜ.Finite) :
    ((Subtype.val ⁻¹' B : Set s)ᶜ).Finite := by
  -- Proof comment: the pulled-back complement is just the preimage of the ambient complement
  -- under the subtype embedding, so finiteness descends along injective pullback.
  simpa [Set.preimage_compl] using
    Set.Finite.preimage_embedding
      (f := (show s ↪ E from ⟨Subtype.val, fun _ _ h ↦ Subtype.ext h⟩))
      hBfinite

/-- Helper for Theorem 19.30: for the fixed ambient target `B`, the sink edge of the pulled-back
subgraph collapse is bounded directly by the ambient sink edge at `B`. -/
private theorem cofiniteTargetCollapse_sinkEdge_subgraph_le_ambient_of_pullbackTarget
    {G : SimpleGraph E} {s : Set E} [DiscreteMeasurableSpace ↑s] {G' : SimpleGraph s}
    {p : E → E → ℝ≥0∞} {p' : s → s → ℝ≥0∞}
    [IsSimpleRandomWalk p G] [IsSimpleRandomWalk p' G']
    (hsub : G' ≤ SimpleGraph.induce s G) (B : Set E)
    (y : {z : s // z ∉ (Subtype.val ⁻¹' B : Set s)}) :
    cofiniteTargetCollapse (simpleGraphWeights G') (Subtype.val ⁻¹' B : Set s)
        (Sum.inl y) (Sum.inr ()) ≤
      cofiniteTargetCollapse (simpleGraphWeights G) B
        (Sum.inl ⟨y.1.1, by simpa using y.2⟩) (Sum.inr ()) := by
  let A : Set s := Subtype.val ⁻¹' B
  have hmono :
      cofiniteTargetCollapse (simpleGraphWeights G') A (Sum.inl y) (Sum.inr ()) ≤
        cofiniteTargetCollapse (simpleGraphWeights (SimpleGraph.induce s G)) A
          (Sum.inl y) (Sum.inr ()) := by
    exact
      cofiniteTargetCollapse_mono A
        (simpleGraphWeights_le_of_isSubgraph (SimpleGraph.induce s G) G' hsub)
        (Sum.inl y) (Sum.inr ())
  let g : E → ℝ≥0∞ := fun z ↦ if z ∈ B then simpleGraphWeights G y.1 z else 0
  have hSubtypeSum :
      (∑' z : s, if z ∈ A then simpleGraphWeights G y.1 z.1 else 0) =
        ∑' z : s, g z := by
    -- Proof comment: on the subtype carrier, membership in the pullback target `A` is exactly
    -- ambient membership in `B`.
    refine tsum_congr fun z ↦ ?_
    simp [g, A]
  calc
    cofiniteTargetCollapse (simpleGraphWeights G') A (Sum.inl y) (Sum.inr ())
        ≤ cofiniteTargetCollapse (simpleGraphWeights (SimpleGraph.induce s G)) A
            (Sum.inl y) (Sum.inr ()) := hmono
    _ = ∑' z : s, if z ∈ A then simpleGraphWeights G y.1 z.1 else 0 := by
          -- Proof comment: the induced-graph sink edge is the pullback target sum over the
          -- subtype carrier.
          simp [A, cofiniteTargetCollapse, simpleGraphWeights_induce_apply]
    _ = ∑' z : s, g z := hSubtypeSum
    _ = ∑' z : E, Set.indicator (s : Set E) g z := by
          simpa [g] using (tsum_subtype (s := s) (f := g))
    _ ≤ ∑' z : E, g z := by
          exact ENNReal.tsum_le_tsum fun z ↦ by
            by_cases hz : z ∈ s
            · simp [Set.indicator, hz]
            · simp [Set.indicator, hz]
    _ = cofiniteTargetCollapse (simpleGraphWeights G) B
          (Sum.inl ⟨y.1.1, by simpa [A] using y.2⟩) (Sum.inr ()) := by
            -- Proof comment: the ambient sink edge is the same fixed-target sum over `B`.
            simp [g, cofiniteTargetCollapse]

/-- Helper for Theorem 19.30: for an ambient cofinite target `B`, the corresponding pulled-back
subgraph boundary term should be compared directly with the ambient boundary term at `B`. -/
private theorem cofiniteBoundaryConductance_subgraph_le_ambient_of_cofiniteTarget
    {G : SimpleGraph E} {s : Set E} [DiscreteMeasurableSpace ↑s] {G' : SimpleGraph s}
    {p : E → E → ℝ≥0∞} {p' : s → s → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    {P' : s → ProbabilityMeasure Ω'} {X' : ℕ → Ω' → s}
    [IsSimpleRandomWalk p G] [IsSimpleRandomWalk p' G']
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p' ^ n) P' X']
    (hsub : G' ≤ SimpleGraph.induce s G) (x : s)
    (B : {B : Set E // Bᶜ.Finite ∧ x.1 ∉ B}) :
    conductance (simpleGraphWeights G') x *
        escapeToSetProbability P' X' x (Subtype.val ⁻¹' B.1) ≤
      conductance (simpleGraphWeights G) x.1 *
        escapeToSetProbability P X x.1 B.1 := by
  classical
  let A : Set s := Subtype.val ⁻¹' B.1
  have hAfinite : (Aᶜ : Set s).Finite := pullbackTarget_compl_finite (s := s) B.2.1
  have hxA : x ∉ A := by
    simpa [A] using B.2.2
  letI : Fintype {z : s // z ∉ A} := hAfinite.fintype
  letI : Fintype {z : E // z ∉ B.1} := B.2.1.fintype
  -- Route correction: the old transported-target family `((↑) '' A) ∪ sᶜ` had the wrong final
  -- normal form. The corrected proof stays indexed by the ambient target `B`, splits the ambient
  -- visible carrier into pullback-visible plus extra vertices outside `s`, and applies Rayleigh
  -- on that common split carrier.
  rw [cofiniteBoundaryConductance_eq_collapsedEffectiveConductance
    (p := p') (C := simpleGraphWeights G') (P := P') (X := X') x hAfinite hxA]
  rw [cofiniteBoundaryConductance_eq_collapsedEffectiveConductance
    (p := p) (C := simpleGraphWeights G) (P := P) (X := X) x.1 B.2.1 B.2.2]
  let xA : {z : s // z ∉ A} := ⟨x, hxA⟩
  let Extra := {z : E // z ∉ B.1 ∧ z ∉ s}
  have hExtraFinite : ({z : E | z ∉ B.1 ∧ z ∉ s} : Set E).Finite := by
    exact B.2.1.subset fun _ hz ↦ hz.1
  letI : Fintype Extra := by
    dsimp [Extra]
    exact hExtraFinite.fintype
  let eVisible :
      {z : E // z ∉ B.1} ≃ ({z : s // z ∉ A} ⊕ Extra) := by
    dsimp [Extra]
    simpa [A] using ambientVisibleEquivPullbackSum (s := s) (B := B.1)
  let eB :
      ({z : E // z ∉ B.1} ⊕ Unit) ≃ (({z : s // z ∉ A} ⊕ Unit) ⊕ Extra) :=
    ((((Equiv.sumCongr eVisible (Equiv.refl Unit)).trans
        (Equiv.sumAssoc {z : s // z ∉ A} Extra Unit)).trans
      (Equiv.sumCongr (Equiv.refl {z : s // z ∉ A}) (Equiv.sumComm Extra Unit))).trans
      (Equiv.sumAssoc {z : s // z ∉ A} Unit Extra).symm)
  let Dsub :
      (({z : s // z ∉ A} ⊕ Unit) ⊕ Extra) →
        (({z : s // z ∉ A} ⊕ Unit) ⊕ Extra) → ℝ≥0∞ :=
    fun u v =>
      match u, v with
      | Sum.inl u', Sum.inl v' => cofiniteTargetCollapse (simpleGraphWeights G') A u' v'
      | _, _ => 0
  let Damb :
      (({z : s // z ∉ A} ⊕ Unit) ⊕ Extra) →
        (({z : s // z ∉ A} ⊕ Unit) ⊕ Extra) → ℝ≥0∞ :=
    fun u v ↦ cofiniteTargetCollapse (simpleGraphWeights G) B.1 (eB.symm u) (eB.symm v)
  let A0 : Set ((({z : s // z ∉ A} ⊕ Unit) ⊕ Extra)) := {Sum.inl (Sum.inl xA)}
  let A1 : Set ((({z : s // z ∉ A} ⊕ Unit) ⊕ Extra)) := {Sum.inl (Sum.inr ())}
  have heB_visible (y : {z : s // z ∉ A}) :
      eB.symm (Sum.inl (Sum.inl y)) = Sum.inl ⟨y.1.1, by simpa [A] using y.2⟩ := by
    -- Proof comment: the split-carrier equivalence sends the left visible summand back to the
    -- corresponding ambient visible vertex.
    simp [eB, eVisible, A]
  have heB_sink :
      eB.symm (Sum.inl (Sum.inr ())) = Sum.inr () := by
    -- Proof comment: the sink vertex is fixed by the carrier reindexing.
    simp [eB]
  have hDamb_symm : ∀ u v, Damb u v = Damb v u := by
    -- Proof comment: the ambient side is just the ambient collapsed network transported along
    -- `eB`, so symmetry is inherited from `cofiniteTargetCollapse`.
    intro u v
    simpa [Damb] using
      (cofiniteTargetCollapse_symmetric
        (p := p) (C := simpleGraphWeights G) B.1 (eB.symm u) (eB.symm v))
  have hDamb_finite : ∀ u, conductance Damb u < ∞ := by
    -- Proof comment: reindexing preserves the finite row conductances of the ambient collapsed
    -- network.
    intro u
    calc
      conductance Damb u
          = conductance (cofiniteTargetCollapse (simpleGraphWeights G) B.1) (eB.symm u) := by
              simpa [Damb] using
                (conductance_comp_equiv
                  (e := eB.symm) (D := cofiniteTargetCollapse (simpleGraphWeights G) B.1) u)
      _ < ∞ :=
        cofiniteTargetCollapse_conductance_lt_top
          (p := p) (C := simpleGraphWeights G) B.2.1 (eB.symm u)
  have hDsub_symm : ∀ u v, Dsub u v = Dsub v u := by
    -- Proof comment: on the left summand this is the subgraph collapsed symmetry; every edge
    -- touching the isolated right summand is `0`.
    intro u v
    rcases u with u | u <;> rcases v with v | v
    · simpa [Dsub] using
        (cofiniteTargetCollapse_symmetric
          (p := p') (C := simpleGraphWeights G') A u v)
    · simp [Dsub]
    · simp [Dsub]
    · simp [Dsub]
  have hDsub_finite : ∀ u, conductance Dsub u < ∞ := by
    -- Proof comment: left rows agree with the finite subgraph collapsed rows, while the isolated
    -- extra rows are identically `0`.
    intro u
    rcases u with u | u
    · simpa [conductance, Dsub, Fintype.sum_sum_type] using
        (cofiniteTargetCollapse_conductance_lt_top
          (p := p') (C := simpleGraphWeights G') hAfinite u)
    · rw [conductance, tsum_fintype, Fintype.sum_sum_type]
      simp [Dsub]
  have hDmono : ∀ u v, Dsub u v ≤ Damb u v := by
    -- Proof comment: compare the visible-visible block by subgraph monotonicity, the visible-sink
    -- block by the direct sink-sum estimate at the fixed target `B`, reduce the sink-visible case
    -- by symmetry, and note that every edge touching the isolated right summand is `0` on `Dsub`.
    intro u v
    rcases u with u | u <;> rcases v with v | v
    · rcases u with y | u0 <;> rcases v with z | v0
      · simpa [Dsub, Damb, heB_visible y, heB_visible z, simpleGraphWeights_induce_apply] using
          simpleGraphWeights_le_of_isSubgraph (SimpleGraph.induce s G) G' hsub y z
      · simpa [Dsub, Damb, heB_visible y, heB_sink, A] using
          cofiniteTargetCollapse_sinkEdge_subgraph_le_ambient_of_pullbackTarget
            (p := p) (p' := p') (hsub := hsub) (B := B.1) y
      · have hvisibleSink :
            Dsub (Sum.inl (Sum.inl z)) (Sum.inl (Sum.inr ())) ≤
              Damb (Sum.inl (Sum.inl z)) (Sum.inl (Sum.inr ())) := by
          simpa [Dsub, Damb, heB_visible z, heB_sink, A] using
            cofiniteTargetCollapse_sinkEdge_subgraph_le_ambient_of_pullbackTarget
              (p := p) (p' := p') (hsub := hsub) (B := B.1) z
        calc
          Dsub (Sum.inl (Sum.inr ())) (Sum.inl (Sum.inl z))
              = Dsub (Sum.inl (Sum.inl z)) (Sum.inl (Sum.inr ())) := by
                  simpa using
                    (hDsub_symm (Sum.inl (Sum.inr ())) (Sum.inl (Sum.inl z)))
          _ ≤ Damb (Sum.inl (Sum.inl z)) (Sum.inl (Sum.inr ())) := hvisibleSink
          _ = Damb (Sum.inl (Sum.inr ())) (Sum.inl (Sum.inl z)) := by
                symm
                simpa using
                  (hDamb_symm (Sum.inl (Sum.inr ())) (Sum.inl (Sum.inl z)))
      · simp [Dsub, Damb, heB_sink, cofiniteTargetCollapse]
    · simp [Dsub, Damb]
    · simp [Dsub, Damb]
    · simp [Dsub, Damb]
  have hA0 : A0.Nonempty := ⟨Sum.inl (Sum.inl xA), by simp [A0]⟩
  have hA1 : A1.Nonempty := ⟨Sum.inl (Sum.inr ()), by simp [A1]⟩
  have hdisj : Disjoint A0 A1 := by
    rw [Set.disjoint_singleton_right]
    simp [A0, A1]
  have hsubEq :
      effectiveConductance Dsub A0 A1 =
        effectiveConductance (cofiniteTargetCollapse (simpleGraphWeights G') A)
          ({Sum.inl xA} : Set ({z : s // z ∉ A} ⊕ Unit)) ({Sum.inr ()}) := by
    -- Proof comment: adjoining the isolated extra ambient-visible vertices does not change the
    -- subgraph effective conductance.
    have hA0Image :
        (Sum.inl '' ({Sum.inl xA} : Set ({z : s // z ∉ A} ⊕ Unit))) = A0 := by
      ext u
      simp [A0]
    have hA1Image :
        (Sum.inl '' ({Sum.inr ()} : Set ({z : s // z ∉ A} ⊕ Unit))) = A1 := by
      ext u
      simp [A1]
    rw [← hA0Image, ← hA1Image]
    convert
      (effectiveConductance_sumRightZero_eq
        (β := Extra)
        (D := cofiniteTargetCollapse (simpleGraphWeights G') A)
        ({Sum.inl xA} : Set ({z : s // z ∉ A} ⊕ Unit))
        ({Sum.inr ()} : Set ({z : s // z ∉ A} ⊕ Unit))) using 1
    apply congrArg (fun D ↦
      effectiveConductance D
        (Sum.inl '' ({Sum.inl xA} : Set ({z : s // z ∉ A} ⊕ Unit)))
        (Sum.inl '' ({Sum.inr ()} : Set ({z : s // z ∉ A} ⊕ Unit))))
    funext u
    funext v
    cases u <;> cases v <;> rfl
  have hambEq :
      effectiveConductance Damb A0 A1 =
        effectiveConductance (cofiniteTargetCollapse (simpleGraphWeights G) B.1)
          ({Sum.inl ⟨x.1, B.2.2⟩} : Set ({z : E // z ∉ B.1} ⊕ Unit)) ({Sum.inr ()}) := by
    -- Proof comment: transporting the ambient collapse across `eB` identifies it with the
    -- ambient target `B` on the original ambient collapsed carrier.
    simpa [A0, A1, Damb, heB_visible xA, heB_sink] using
      (effectiveConductance_comp_equiv
        (e := eB.symm) (D := cofiniteTargetCollapse (simpleGraphWeights G) B.1) A0 A1)
  have hRayleigh :
      effectiveConductance Dsub A0 A1 ≤ effectiveConductance Damb A0 A1 := by
    exact
      rayleigh_monotonicity_principle
        (hC_symm := hDamb_symm) (hC_finite := hDamb_finite)
        (hC'_symm := hDsub_symm) (hC'_finite := hDsub_finite)
        (hA0 := hA0) (hA1 := hA1) (hdisj := hdisj) (hCC' := hDmono)
  exact ENNReal.ofReal_le_ofReal <| by
    calc
      effectiveConductance (cofiniteTargetCollapse (simpleGraphWeights G') A)
          ({Sum.inl xA} : Set ({z : s // z ∉ A} ⊕ Unit)) ({Sum.inr ()})
          = effectiveConductance Dsub A0 A1 := by
              symm
              exact hsubEq
      _ ≤ effectiveConductance Damb A0 A1 := hRayleigh
      _ =
          effectiveConductance (cofiniteTargetCollapse (simpleGraphWeights G) B.1)
            ({Sum.inl ⟨x.1, B.2.2⟩} : Set ({z : E // z ∉ B.1} ⊕ Unit)) ({Sum.inr ()}) := hambEq

/-- Helper for Theorem 19.30: the subgraph walk has no larger effective conductance to infinity
than the ambient walk at the corresponding state. -/
private theorem effectiveConductanceToInfinity_subgraph_le_ambient_at_state
    {G : SimpleGraph E} {s : Set E} [DiscreteMeasurableSpace ↑s] {G' : SimpleGraph s}
    {p : E → E → ℝ≥0∞} {p' : s → s → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    {P' : s → ProbabilityMeasure Ω'} {X' : ℕ → Ω' → s}
    [IsSimpleRandomWalk p G] [IsSimpleRandomWalk p' G']
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p' ^ n) P' X']
    (hsub : G' ≤ SimpleGraph.induce s G) (x : s) :
    effectiveConductanceToInfinity (simpleGraphWeights G') P' X' x ≤
      effectiveConductanceToInfinity (simpleGraphWeights G) P X x.1 := by
  -- Route correction: the previous `((↑) '' A) ∪ sᶜ` route indexed the final infimum by the
  -- wrong family of ambient targets. The corrected proof fixes an arbitrary ambient cofinite
  -- target `B`, pulls it back to `A := Subtype.val ⁻¹' B`, and compares those single boundary
  -- terms before taking the ambient `iInf`.
  rw [effectiveConductanceToInfinity_eq_iInf_cofiniteTargets
    (p := p') (C := simpleGraphWeights G') (P := P') (X := X') x]
  rw [effectiveConductanceToInfinity_eq_iInf_cofiniteTargets
    (p := p) (C := simpleGraphWeights G) (P := P) (X := X) x.1]
  have hSubTargets_nonempty : Nonempty {A : Set s // Aᶜ.Finite ∧ x ∉ A} := by
    refine ⟨⟨({x} : Set s)ᶜ, ?_, by simp⟩⟩
    simp
  letI := hSubTargets_nonempty
  have hAmbientTargets_nonempty : Nonempty {B : Set E // Bᶜ.Finite ∧ x.1 ∉ B} := by
    refine ⟨⟨({x.1} : Set E)ᶜ, ?_, by simp⟩⟩
    simp
  letI := hAmbientTargets_nonempty
  by_cases hC0 : conductance (simpleGraphWeights G') x = 0
  · -- Proof comment: if the subgraph conductance at `x` vanishes, the chosen left-hand boundary
    -- term is already `0`.
    simp [hC0]
  · have hCneTop : conductance (simpleGraphWeights G') x ≠ ∞ :=
        (IsRandomWalkWithWeights.conductance_lt_top
          (h := (inferInstance : IsSimpleRandomWalk p' G')) x).ne
    calc
      conductance (simpleGraphWeights G') x *
          ⨅ A' : {A' : Set s // A'ᶜ.Finite ∧ x ∉ A'},
            escapeToSetProbability P' X' x A'.1
          =
        ⨅ A' : {A' : Set s // A'ᶜ.Finite ∧ x ∉ A'},
          conductance (simpleGraphWeights G') x *
            escapeToSetProbability P' X' x A'.1 := by
              rw [ENNReal.mul_iInf_of_ne hC0 hCneTop]
      _ ≤
          ⨅ B : {B : Set E // Bᶜ.Finite ∧ x.1 ∉ B},
            conductance (simpleGraphWeights G) x.1 *
              escapeToSetProbability P X x.1 B.1 := by
                refine le_iInf fun B : {B : Set E // Bᶜ.Finite ∧ x.1 ∉ B} ↦ ?_
                let A : Set s := Subtype.val ⁻¹' B.1
                have hAfinite : (Aᶜ : Set s).Finite := pullbackTarget_compl_finite (s := s) B.2.1
                have hxA : x ∉ A := by
                  simpa [A] using B.2.2
                calc
                  ⨅ A' : {A' : Set s // A'ᶜ.Finite ∧ x ∉ A'},
                      conductance (simpleGraphWeights G') x *
                        escapeToSetProbability P' X' x A'.1
                      ≤ conductance (simpleGraphWeights G') x *
                          escapeToSetProbability P' X' x A := by
                            exact
                              iInf_le _ (show {A' : Set s // A'ᶜ.Finite ∧ x ∉ A'} from
                                ⟨A, ⟨hAfinite, hxA⟩⟩)
                  _ ≤ conductance (simpleGraphWeights G) x.1 *
                        escapeToSetProbability P X x.1 B.1 := by
                          simpa [A] using
                            cofiniteBoundaryConductance_subgraph_le_ambient_of_cofiniteTarget
                              (p := p) (p' := p') (P := P) (X := X) (P' := P') (X' := X')
                              hsub x B
      _ =
          conductance (simpleGraphWeights G) x.1 *
            ⨅ B : {B : Set E // Bᶜ.Finite ∧ x.1 ∉ B},
              escapeToSetProbability P X x.1 B.1 := by
                by_cases hC0' : conductance (simpleGraphWeights G) x.1 = 0
                · simp [hC0']
                · have hCneTop' : conductance (simpleGraphWeights G) x.1 ≠ ∞ :=
                    (IsRandomWalkWithWeights.conductance_lt_top
                      (h := (inferInstance : IsSimpleRandomWalk p G)) x.1).ne
                  rw [ENNReal.mul_iInf_of_ne hC0' hCneTop']


-- Proof sketch: apply `randomWalkWithWeights_recurrent_of_edgeWeights_le` to the unit weight
-- families of `G'` and of the induced graph `SimpleGraph.induce s G`; the subgraph assumption
-- gives the needed pointwise edge-weight inequality.
/-- Passing from a recurrent simple random walk on `G` to a simple random walk on a subgraph of an
induced graph preserves recurrence. -/
theorem simpleRandomWalk_recurrent_of_subgraph
    {G : SimpleGraph E} {s : Set E} [DiscreteMeasurableSpace ↑s] {G' : SimpleGraph s}
    {p : E → E → ℝ≥0∞} {p' : s → s → ℝ≥0∞}
    {P : E → ProbabilityMeasure Ω} {X : ℕ → Ω → E}
    {P' : s → ProbabilityMeasure Ω'} {X' : ℕ → Ω' → s}
    [IsSimpleRandomWalk p G] [IsSimpleRandomWalk p' G']
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p ^ n) P X]
    [IsMarkovProcessRealization (fun n : ℕ ↦ discreteMatrixKernel p' ^ n) P' X']
    (hsub : G' ≤ SimpleGraph.induce s G)
    (hrec : IsRecurrentMarkovChain P X) :
    IsRecurrentMarkovChain P' X' := by
  intro x
  rw [isRecurrentState_iff_effectiveConductanceToInfinity_eq_zero
    (p := p') (C := simpleGraphWeights G') (P := P') (X := X') (x₁ := x)]
  have hxrec :
      effectiveConductanceToInfinity (simpleGraphWeights G) P X x.1 = 0 := by
    exact
      (isRecurrentState_iff_effectiveConductanceToInfinity_eq_zero
        (p := p) (C := simpleGraphWeights G) (P := P) (X := X) (x₁ := x.1)).mp
        (hrec x.1)
  refine le_antisymm ?_ bot_le
  calc
    effectiveConductanceToInfinity (simpleGraphWeights G') P' X' x
        ≤ effectiveConductanceToInfinity (simpleGraphWeights G) P X x.1 :=
          effectiveConductanceToInfinity_subgraph_le_ambient_at_state
            (p := p) (p' := p') (P := P) (X := X) (P' := P') (X' := X')
            hsub x
    _ = 0 := hxrec

end ProbabilityTheory
