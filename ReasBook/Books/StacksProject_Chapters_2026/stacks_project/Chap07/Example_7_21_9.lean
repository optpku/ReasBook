module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic
public import stacks_project.Chap06.ClosedSubsetInclusion

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopCat TopologicalSpace
open TopologicalSpace.Opens

noncomputable section

universe u

/- Domain-style sampling for Example 7.21.9:
- primary domain: Grothendieck topologies on categories of opens of topological spaces;
- sampled owner API:
  `CategoryTheory.Functor.IsCocontinuous`,
  `TopologicalSpace.Opens.grothendieckTopology`,
  `TopologicalSpace.Opens.map`,
  `TopCat.subsetInclusion`,
  `Dense`,
  `dense_iff_inter_open`;
- source/core/bridge triage:
  `source-facing`: the general restriction functor on opens attached to a subset inclusion
  `Z ↪ X`, together with the punctured-real counterexample showing the resulting necessary density
  condition is not sufficient for cocontinuity;
  `core/canonical`: `Functor.IsCocontinuous`;
  `bridge/view`: the concrete inverse-image functor on opens `Opens.map i`, specialized for
  subset inclusions by the project owner `TopCat.subsetInclusion`.

Primitive data are the subset inclusion `i : Z ↪ X` and the induced functor on opens
`Opens.map i`; for an actual subset `Z : Set X`, the project already owns that inclusion as
`TopCat.subsetInclusion X Z`. The density consequence for `Z` is derived API from
cocontinuity of that owner. The punctured-real example then remains as the concrete source-facing
counterexample to the converse.
-/

section

variable {X Z : TopCat.{u}}

local notation "JX" => Opens.grothendieckTopology X
local notation "JZ" => Opens.grothendieckTopology Z

/-- For the Grothendieck topology on opens, a cocontinuous inverse-image functor `Opens.map i`
cannot send a nonempty open subset of `X` to the empty open subset of `Z`. -/
theorem map_obj_ne_bot_of_isCocontinuous
    (i : Z ⟶ X)
    (hco : (Opens.map i).IsCocontinuous JX JZ)
    {U : Opens X} (hU : U ≠ ⊥) :
    (Opens.map i).obj U ≠ ⊥ := by
  intro hmap
  have hcover_map :
      (⊥ : Sieve ((Opens.map i).obj U)) ∈ JZ ((Opens.map i).obj U) := by
    rw [hmap]
    intro z hz
    simpa using hz
  letI : (Opens.map i).IsCocontinuous JX JZ := hco
  have hcover : (⊥ : Sieve U) ∈ JX U := by
    simpa [Sieve.functorPullback, hmap] using
      (Opens.map i).cover_lift JX JZ hcover_map
  have hbot : U = ⊥ := by
    ext x
    constructor
    · intro hx
      rcases hcover x hx with ⟨V, f, hf, hxV⟩
      simp at hf
    · intro hx
      exact False.elim <| by simpa using hx
  exact hU hbot

end

section

variable {X : TopCat.{u}} (Z : Set X)

local notation "i" => X.subsetInclusion (Z : Set X)
local notation "JX" => Opens.grothendieckTopology X
local notation "JZ" => Opens.grothendieckTopology (TopCat.of Z)

/-- Example 7.21.9, canonical owner form: if the restriction functor on opens attached to a
subset inclusion `Z ↪ X` is cocontinuous, then `Z` is dense in `X`. The restriction functor is
expressed via the canonical owner `X.subsetInclusion Z`. -/
theorem subset_restriction_dense_of_isCocontinuous
    (hco : (Opens.map i).IsCocontinuous JX JZ) :
    Dense Z := by
  refine dense_iff_inter_open.2 ?_
  intro U hU hUne
  let U' : Opens X := ⟨U, hU⟩
  have hU' : U' ≠ ⊥ := by
    intro hbot
    rcases hUne with ⟨x, hx⟩
    have hx' : x ∈ U' := by
      simpa [U'] using hx
    rw [hbot] at hx'
    have : x ∈ (⊥ : Opens X) := hx'
    simpa using this
  have hmap : (Opens.map i).obj U' ≠ ⊥ :=
    map_obj_ne_bot_of_isCocontinuous i hco hU'
  by_contra hUZ
  have hmap_bot : (Opens.map i).obj U' = ⊥ := by
    ext z
    constructor
    · intro hz
      exact False.elim <| hUZ ⟨z.1, hz, z.2⟩
    · intro hz
      exact False.elim <| by simpa using hz
  exact hmap hmap_bot

/-- Companion source-facing reformulation of the general part of Example 7.21.9. -/
theorem subset_restriction_inter_nonempty_of_isCocontinuous
    (hco : (Opens.map i).IsCocontinuous JX JZ)
    {U : Set X} (hU : IsOpen U) (hUne : U.Nonempty) :
    (U ∩ Z).Nonempty :=
  (subset_restriction_dense_of_isCocontinuous Z hco).inter_open_nonempty U hU hUne

end

private theorem zero_mem_open_contains_small_pos_and_neg {W : Set ℝ}
    (hW : IsOpen W) (h0 : (0 : ℝ) ∈ W) (n : ℕ) :
    ∃ x y : ℝ, x < 0 ∧ 0 < y ∧ y < 1 / (n + 1 : ℝ) ∧ x ∈ W ∧ y ∈ W := by
  rw [isOpen_iff_mem_nhds] at hW
  rcases mem_nhds_iff_exists_Ioo_subset.mp (hW 0 h0) with ⟨a, b, hab, hsub⟩
  let x : ℝ := a / 2
  let y : ℝ := min (b / 2) ((1 / (n + 1 : ℝ)) / 2)
  have hypos : 0 < y := by
    have hbhalf : 0 < b / 2 := by
      linarith [hab.2]
    have honehalf : 0 < (1 / (n + 1 : ℝ)) / 2 := by
      positivity
    dsimp [y]
    exact lt_min hbhalf honehalf
  have hylt : y < 1 / (n + 1 : ℝ) := by
    have hpos : 0 < (1 / (n + 1 : ℝ)) := by
      positivity
    have honehalf_lt : (1 / (n + 1 : ℝ)) / 2 < 1 / (n + 1 : ℝ) := by
      nlinarith
    dsimp [y]
    exact lt_of_le_of_lt (min_le_right _ _) honehalf_lt
  have hy_mem : y ∈ W := by
    have hy_lt_b : y < b := by
      have hbhalf_lt : b / 2 < b := by
        linarith [hab.2]
      dsimp [y]
      exact lt_of_le_of_lt (min_le_left _ _) hbhalf_lt
    exact hsub ⟨by linarith [hab.1, hypos], hy_lt_b⟩
  refine ⟨x, y, ?_, hypos, hylt, ?_, hy_mem⟩
  · dsimp [x]
    linarith [hab.1]
  · exact hsub <| by
      dsimp [x]
      constructor <;> linarith [hab.1, hab.2]

-- Proof sketch: use the cover of `ℝ \ {0}` by the negative half-line together with the opens
-- `(1 / n, ∞) ∩ (ℝ \ {0})`. Any open cover of `ℝ` whose restriction refines this family would have
-- to cover points approaching `0` from the right by opens whose restrictions avoid `0`, which is
-- impossible in the usual topology. This shows that the density criterion above is necessary but
-- not sufficient.
/-- Example 7.21.9, punctured-real counterexample: for the canonical subset inclusion
`ℝ \ {0} ↪ ℝ`, the restriction functor on opens `U ↦ U ∩ (ℝ \ {0})` is not cocontinuous for the
canonical Grothendieck topologies on opens. -/
theorem punctured_real_restriction_not_cocontinuous :
    let X : TopCat := TopCat.of ℝ
    let Z : Set X := ({0} : Set ℝ)ᶜ
    ¬ (Opens.map (X.subsetInclusion Z)).IsCocontinuous
        (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology (TopCat.of Z)) :=
  by
    dsimp
    let X : TopCat := TopCat.of ℝ
    let Z : Set X := (({0} : Set ℝ)ᶜ : Set ℝ)
    let i : TopCat.of Z ⟶ X := X.subsetInclusion Z
    let topX : Opens X := ⟨Set.univ, isOpen_univ⟩
    let topZ : Opens (TopCat.of Z) := (Opens.map i).obj topX
    let S : Sieve topZ :=
      { arrows := fun V _ ↦
          ((V : Set Z) ⊆ {z : Z | z.1 < 0}) ∨
            ∃ n : ℕ, (V : Set Z) ⊆ {z : Z | (1 : ℝ) / (n + 1) < z.1}
        downward_closed := by
          intro V W _ hf g
          rcases hf with hneg | ⟨n, hn⟩
          · left
            intro z hz
            exact hneg (g.le hz)
          · right
            exact ⟨n, fun z hz ↦ hn (g.le hz)⟩ }
    have hS : S ∈ Opens.grothendieckTopology (TopCat.of Z) topZ := by
      intro z hz
      rcases lt_or_gt_of_ne z.2 with hzneg | hzpos
      · refine ⟨⟨{w : Z | w.1 < 0},
            by simpa using isOpen_lt continuous_subtype_val continuous_const⟩,
          homOfLE (by intro w hw; trivial), ?_, ?_⟩
        · left
          intro w hw
          exact hw
        · exact hzneg
      · obtain ⟨n, hn⟩ := exists_nat_one_div_lt hzpos
        refine ⟨⟨{w : Z | (1 : ℝ) / (n + 1) < w.1},
              by simpa using isOpen_lt continuous_const continuous_subtype_val⟩,
            homOfLE (by intro w hw; trivial), ?_, ?_⟩
        · right
          exact ⟨n, fun w hw ↦ hw⟩
        · exact hn
    intro hco
    letI : (Opens.map i).IsCocontinuous
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z)) := hco
    have hpull : S.functorPullback (Opens.map i) ∈ Opens.grothendieckTopology X topX := by
      simpa [topZ] using
        (Opens.map i).cover_lift
          (Opens.grothendieckTopology X) (Opens.grothendieckTopology (TopCat.of Z)) hS
    rcases hpull 0 (by trivial) with ⟨W, f, hf, h0W⟩
    rcases hf with hneg | ⟨n, hpos⟩
    · rcases zero_mem_open_contains_small_pos_and_neg W.2 h0W 0 with
        ⟨x, y, hxneg, hypos, hylt, hxW, hyW⟩
      have hyZ : y ∈ Z := by
        simp [Z, hypos.ne']
      have hyWZ : (⟨y, hyZ⟩ : Z) ∈ (Opens.map i).obj W := by
        change y ∈ W
        exact hyW
      have hyneg : y < 0 := hneg hyWZ
      exact not_lt_of_ge hyneg.le hypos
    · rcases zero_mem_open_contains_small_pos_and_neg W.2 h0W n with
        ⟨x, y, hxneg, hypos, hylt, hxW, hyW⟩
      have hyZ : y ∈ Z := by
        simp [Z, hypos.ne']
      have hyWZ : (⟨y, hyZ⟩ : Z) ∈ (Opens.map i).obj W := by
        change y ∈ W
        exact hyW
      have hybig : 1 / (n + 1 : ℝ) < y := hpos hyWZ
      exact not_lt_of_ge hybig.le hylt
