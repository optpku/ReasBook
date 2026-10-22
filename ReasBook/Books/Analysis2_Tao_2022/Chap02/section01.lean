/-
Authors: Chenyi Li, Min Cui, Qiming Dai, Shu Miao, Wanli Ma, Yi Yuan, Zichen Wang, Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/Analysis2_Tao_2022/README.md (Contributors).
-/

import Mathlib

section Chap02
section Section01

/-- Definition 2.1 (Continuous functions): (i) For `x0 ∈ X`, `f` is continuous at `x0` if for every
`ε > 0` there exists `δ > 0` such that for all `x ∈ X`, `d_X x x0 < δ` implies
`d_Y (f x) (f x0) < ε`. (ii) `f` is continuous on `X` if it is continuous at every `x ∈ X`. -/
abbrev IsContinuousAt {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (x0 : X) : Prop :=
  ContinuousAt f x0

/-- A function between metric spaces is continuous if it is continuous at every point. -/
abbrev IsContinuous {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) : Prop :=
  ∀ x : X, IsContinuousAt f x

/-- Proposition 2.1: Let `X` be a topological space and let `f : X → ℝ` be continuous. Define
`f^2 : X → ℝ` by `f^2 x := (f x)^2`. Then `f^2` is continuous. -/
theorem continuous_sq_of_continuous {X : Type*} [TopologicalSpace X] (f : X → ℝ) :
    Continuous f → Continuous (fun x => (f x) ^ 2) := by
  intro hf
  simpa [pow_two] using hf.mul hf

/-- Helper for Theorem 2.1: open-set formulation of continuity at a point. -/
lemma helperForTheorem_2_1_openImage_iff_continuousAt
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (x0 : X) :
    IsContinuousAt f x0 ↔
      ∀ V : Set Y, IsOpen V → f x0 ∈ V →
        ∃ U : Set X, IsOpen U ∧ x0 ∈ U ∧ f '' U ⊆ V := by
  constructor
  · intro hcont V hVopen hx0V
    have hcont' : ContinuousAt f x0 := by
      simpa [IsContinuousAt] using hcont
    have hVnhds : V ∈ nhds (f x0) := IsOpen.mem_nhds hVopen hx0V
    have hpre : f ⁻¹' V ∈ nhds x0 :=
      (continuousAt_def (f:=f) (x:=x0)).1 hcont' V hVnhds
    rcases (mem_nhds_iff).1 hpre with ⟨U, hUsub, hUopen, hx0U⟩
    refine ⟨U, hUopen, hx0U, ?_⟩
    exact (Set.image_subset_iff).2 hUsub
  · intro hopen
    have hcont : ContinuousAt f x0 := by
      refine (continuousAt_def (f:=f) (x:=x0)).2 ?_
      intro A hA
      rcases (mem_nhds_iff).1 hA with ⟨V, hVsub, hVopen, hx0V⟩
      rcases hopen V hVopen hx0V with ⟨U, hUopen, hx0U, himage⟩
      have hUsubV : U ⊆ f ⁻¹' V := (Set.image_subset_iff).1 himage
      have hUsubA : U ⊆ f ⁻¹' A := by
        intro x hx
        exact hVsub (hUsubV hx)
      exact (mem_nhds_iff).2 ⟨U, hUsubA, hUopen, hx0U⟩
    simpa [IsContinuousAt] using hcont

/-- Theorem 2.1 (Continuity preserves convergence): Let `(X,d_X)` and `(Y,d_Y)` be metric spaces,
`f : X → Y`, and `x0 ∈ X`. The following statements are equivalent: (a) `f` is continuous at `x0`.
(b) For every sequence `x : ℕ → X` with `x → x0`, one has `f ∘ x → f x0`. (c) For every open set
`V ⊆ Y` with `f x0 ∈ V`, there exists an open set `U ⊆ X` with `x0 ∈ U` such that `f '' U ⊆ V`. -/
theorem continuity_preserves_convergence
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (x0 : X) :
    (IsContinuousAt f x0 ↔
      ∀ x : ℕ → X, Filter.Tendsto x Filter.atTop (nhds x0) →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds (f x0))) ∧
    (IsContinuousAt f x0 ↔
      ∀ V : Set Y, IsOpen V → f x0 ∈ V →
        ∃ U : Set X, IsOpen U ∧ x0 ∈ U ∧ f '' U ⊆ V) := by
  refine And.intro ?_ ?_
  · simpa [IsContinuousAt, ContinuousAt, Function.comp] using
      (tendsto_nhds_iff_seq_tendsto (f:=f) (a:=x0) (b:=f x0))
  · simpa using helperForTheorem_2_1_openImage_iff_continuousAt f x0

/-- Proposition 2.2: Let `(X, d)` be a metric space and let `(E, d|_{E × E})` be a subspace of
`(X, d)`. The inclusion map `ι_{E → X} : E → X`, defined by `ι_{E → X}(x) = x`, is continuous. -/
theorem isContinuous_inclusion_subtype {X : Type*} [MetricSpace X] (E : Set X) :
    IsContinuous (Subtype.val : E → X) := by
  intro x
  simpa [IsContinuousAt] using (continuousAt_subtype_val (x:=x))

/-- Helper for Theorem 2.2: `IsContinuous` matches `Continuous` for metric spaces. -/
lemma helperForTheorem_2_2_isContinuous_iff_continuous
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    IsContinuous f ↔ Continuous f := by
  constructor
  · intro hcont
    refine (continuous_iff_continuousAt (f:=f)).2 ?_
    intro x0
    have hcontAt : IsContinuousAt f x0 := hcont x0
    simpa [IsContinuousAt] using hcontAt
  · intro hcont
    intro x0
    have hcontAt : ContinuousAt f x0 := (continuous_iff_continuousAt (f:=f)).1 hcont x0
    simpa [IsContinuousAt] using hcontAt

/-- Theorem 2.2: Let `(X, d_X)` and `(Y, d_Y)` be metric spaces and `f : X → Y`. The following
statements are equivalent: (a) `f` is continuous. (b) Whenever a sequence `x` in `X` converges to
`x0`, the sequence `fun n => f (x n)` converges to `f x0`. (c) For every open set `V ⊆ Y`, the
preimage `f ⁻¹' V` is open in `X`. (d) For every closed set `F ⊆ Y`, the preimage `f ⁻¹' F` is
closed in `X`. -/
theorem continuous_iff_sequential_iff_preimage_open_iff_preimage_closed
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) :
    (IsContinuous f ↔
      ∀ x0 : X, ∀ x : ℕ → X, Filter.Tendsto x Filter.atTop (nhds x0) →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds (f x0))) ∧
    (IsContinuous f ↔
      ∀ V : Set Y, IsOpen V → IsOpen (f ⁻¹' V)) ∧
    (IsContinuous f ↔
      ∀ F : Set Y, IsClosed F → IsClosed (f ⁻¹' F)) := by
  refine And.intro ?_ (And.intro ?_ ?_)
  · constructor
    · intro hcont x0 x hx
      have hcontAt : IsContinuousAt f x0 := hcont x0
      have hseqEquiv := (continuity_preserves_convergence f x0).1
      have hseq :
          ∀ x : ℕ → X, Filter.Tendsto x Filter.atTop (nhds x0) →
            Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds (f x0)) :=
        hseqEquiv.mp hcontAt
      exact hseq x hx
    · intro hseq x0
      have hseqAt :
          ∀ x : ℕ → X, Filter.Tendsto x Filter.atTop (nhds x0) →
            Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds (f x0)) :=
        hseq x0
      have hseqEquiv := (continuity_preserves_convergence f x0).1
      exact hseqEquiv.mpr hseqAt
  · constructor
    · intro hcont V hV
      have hcont' : Continuous f :=
        (helperForTheorem_2_2_isContinuous_iff_continuous f).1 hcont
      exact (continuous_def (f:=f)).1 hcont' V hV
    · intro hopen
      have hcont' : Continuous f := by
        refine (continuous_def (f:=f)).2 ?_
        intro V hV
        exact hopen V hV
      exact (helperForTheorem_2_2_isContinuous_iff_continuous f).2 hcont'
  · constructor
    · intro hcont F hF
      have hcont' : Continuous f :=
        (helperForTheorem_2_2_isContinuous_iff_continuous f).1 hcont
      exact (continuous_iff_isClosed (f:=f)).1 hcont' F hF
    · intro hclosed
      have hcont' : Continuous f := by
        refine (continuous_iff_isClosed (f:=f)).2 ?_
        intro F hF
        exact hclosed F hF
      exact (helperForTheorem_2_2_isContinuous_iff_continuous f).2 hcont'

/-- Helper for Proposition 2.3: continuity at a point is preserved under restriction to a subset. -/
lemma helperForProposition_2_3_restrict_isContinuousAt
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) (x0 : E) :
    IsContinuousAt f x0 → IsContinuousAt (fun x : E => f x) x0 := by
  intro hcont
  have hcont' : ContinuousAt f x0 := by
    simpa [IsContinuousAt] using hcont
  have hcomp : ContinuousAt (fun x : E => f x) x0 :=
    hcont'.comp (continuousAt_subtype_val (x:=x0))
  simpa [IsContinuousAt] using hcomp

/-- Helper for Proposition 2.3: global continuity is preserved under restriction to a subset. -/
lemma helperForProposition_2_3_restrict_isContinuous
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) :
    IsContinuous f → IsContinuous (fun x : E => f x) := by
  intro hcont x0
  have hcontAt : IsContinuousAt f x0 := hcont x0
  exact helperForProposition_2_3_restrict_isContinuousAt f E x0 hcontAt

/-- Proposition 2.3: If `f : X → Y` is continuous at `x0 ∈ E`, then the restriction `f|_E` is
continuous at `x0`; in particular, if `f` is continuous on `X`, then `f|_E` is continuous on `E`. -/
theorem continuous_restrict_of_continuous
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set X) :
    (∀ x0 : E, IsContinuousAt f x0 → IsContinuousAt (fun x : E => f x) x0) ∧
    (IsContinuous f → IsContinuous (fun x : E => f x)) := by
  constructor
  · intro x0 hcont
    exact helperForProposition_2_3_restrict_isContinuousAt f E x0 hcont
  · intro hcont
    exact helperForProposition_2_3_restrict_isContinuous f E hcont

/-- Theorem 2.3 (Continuity preserved by composition): Let `(X,d_X)`, `(Y,d_Y)`, and `(Z,d_Z)` be
metric spaces. (a) If `f : X → Y` is continuous at `x0` and `g : Y → Z` is continuous at `f x0`,
then `g ∘ f` is continuous at `x0`. (b) If `f` is continuous on `X` and `g` is continuous on `Y`,
then `g ∘ f` is continuous on `X`. -/
theorem continuity_preserved_by_composition
    {X Y Z : Type*} [MetricSpace X] [MetricSpace Y] [MetricSpace Z] :
    (∀ (f : X → Y) (g : Y → Z) (x0 : X),
      IsContinuousAt f x0 → IsContinuousAt g (f x0) →
        IsContinuousAt (fun x => g (f x)) x0) ∧
    (∀ (f : X → Y) (g : Y → Z),
      IsContinuous f → IsContinuous g → IsContinuous (fun x => g (f x))) := by
  constructor
  · intro f g x0 hf hg
    have hf' : ContinuousAt f x0 := by
      simpa [IsContinuousAt] using hf
    have hg' : ContinuousAt g (f x0) := by
      simpa [IsContinuousAt] using hg
    have hcomp : ContinuousAt (fun x => g (f x)) x0 := hg'.comp hf'
    simpa [IsContinuousAt] using hcomp
  · intro f g hf hg
    intro x0
    have hf' : ContinuousAt f x0 := by
      have hfAt : IsContinuousAt f x0 := hf x0
      simpa [IsContinuousAt] using hfAt
    have hg' : ContinuousAt g (f x0) := by
      have hgAt : IsContinuousAt g (f x0) := hg (f x0)
      simpa [IsContinuousAt] using hgAt
    have hcomp : ContinuousAt (fun x => g (f x)) x0 := hg'.comp hf'
    simpa [IsContinuousAt] using hcomp

/-- Proposition 2.4: Let `f : X → Y` be a function between metric spaces, and let `E ⊆ Y`
contain the image of `f`. Let `g : X → E` be the codomain restriction of `f` with `g x = f x`.
Then for any `x0 ∈ X`, `f` is continuous at `x0` iff `g` is continuous at `x0`. -/
theorem continuousAt_codomainRestrict_iff
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (E : Set Y)
    (hE : ∀ x, f x ∈ E) (x0 : X) :
    IsContinuousAt f x0 ↔ IsContinuousAt (Set.codRestrict f E hE) x0 := by
  simpa [IsContinuousAt] using
    (continuousAt_codRestrict_iff (f := f) (t := E) (h1 := hE) (x := x0)).symm

end Section01
end Chap02
