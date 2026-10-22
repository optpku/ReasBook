/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap03
section Section01

/-- Definition 3.1: [Limiting value of a function] The limit of `f` at `x0` along `E` is
`L` if `x0` is an adherent point of `E` and for every `ε > 0` there exists `δ > 0` such
that for all `x ∈ E`, `dist x x0 < δ` implies `dist (f x) L < ε`. -/
def IsLimitAlong
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y) : Prop :=
  x0 ∈ closure E ∧
    ∀ ε > 0, ∃ δ > 0, ∀ x : E, dist x.1 x0 < δ → dist (f x) L < ε

/-- Helper for Proposition 3.1: equivalence between unpunctured and punctured epsilon-delta conditions. -/
lemma helperForProp_3_1_unpuncturedEpsDelta_iff_punctured
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (x0 : X) :
    (∀ ε > 0, ∃ δ > 0, ∀ x : X,
      dist x x0 < δ → dist (f x) (f x0) < ε) ↔
    (∀ ε > 0, ∃ δ > 0, ∀ x : X,
      0 < dist x x0 ∧ dist x x0 < δ → dist (f x) (f x0) < ε) := by
  constructor
  · intro h ε ε_pos
    rcases h ε ε_pos with ⟨δ, δ_pos, hδ⟩
    refine ⟨δ, δ_pos, ?_⟩
    intro x hx
    exact hδ x hx.2
  · intro h ε ε_pos
    rcases h ε ε_pos with ⟨δ, δ_pos, hδ⟩
    refine ⟨δ, δ_pos, ?_⟩
    intro x hx
    by_cases hx0 : x = x0
    · subst hx0
      simpa [dist_self] using ε_pos
    · have hx_pos : 0 < dist x x0 := dist_pos.2 hx0
      exact hδ x ⟨hx_pos, hx⟩

/-- Helper for Proposition 3.1: punctured epsilon-delta characterization of continuity at a point. -/
lemma helperForProp_3_1_continuousAt_iff_punctured
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (x0 : X) :
    ContinuousAt f x0 ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x : X,
        0 < dist x x0 ∧ dist x x0 < δ → dist (f x) (f x0) < ε := by
  simpa using
    (Metric.continuousAt_iff (f := f) (a := x0)).trans
      (helperForProp_3_1_unpuncturedEpsDelta_iff_punctured (f := f) (x0 := x0))

/-- Proposition 3.1: A function between metric spaces is continuous at `x0` iff for
every `ε > 0` there exists `δ > 0` such that `0 < dist x x0 < δ` implies
`dist (f x) (f x0) < ε`; consequently, `f` is continuous on `X` iff this holds for
all `x0`. -/
theorem continuousAt_iff_limit_and_continuous_iff_limit_all
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (x0 : X) :
    (ContinuousAt f x0 ↔
      ∀ ε > 0, ∃ δ > 0, ∀ x : X,
        0 < dist x x0 ∧ dist x x0 < δ → dist (f x) (f x0) < ε) ∧
    (Continuous f ↔
      ∀ x1 : X, ∀ ε > 0, ∃ δ > 0, ∀ x : X,
        0 < dist x x1 ∧ dist x x1 < δ → dist (f x) (f x1) < ε) := by
  constructor
  · exact helperForProp_3_1_continuousAt_iff_punctured (f := f) (x0 := x0)
  · constructor
    · intro hf x1 ε ε_pos
      have h_unpunctured := (Metric.continuous_iff (f := f)).1 hf x1
      have h_punctured :=
        (helperForProp_3_1_unpuncturedEpsDelta_iff_punctured (f := f) (x0 := x1)).1
          h_unpunctured
      exact h_punctured ε ε_pos
    · intro hf
      refine (Metric.continuous_iff (f := f)).2 ?_
      intro x1 ε ε_pos
      have h_punctured := hf x1
      have h_unpunctured :=
        (helperForProp_3_1_unpuncturedEpsDelta_iff_punctured (f := f) (x0 := x1)).2
          h_punctured
      exact h_unpunctured ε ε_pos

/-- Helper for Example 3.1.1: continuity of `x ↦ x^2 - 4` at `1`. -/
lemma helperForExample_3_1_1_continuousAt_quadraticMinusFour :
    ContinuousAt (fun x : Real => x^2 - 4) 1 := by
  have hcont : Continuous (fun x : Real => x^2 - 4) := by
    simpa [pow_two] using
      (continuous_id.mul continuous_id).sub
        (continuous_const : Continuous fun _ : Real => (4 : Real))
  exact hcont.continuousAt

/-- Example 3.1.1: If `f : Real → Real` is the function `f x = x^2 - 4`, then
`lim_{x → 1} f(x) = f(1) = 1 - 4 = -3` since `f` is continuous. -/
lemma limit_quadratic_minus_four_at_one :
    IsLimitAlong (E := (Set.univ : Set Real))
      (f := fun x : (Set.univ : Set Real) => (x : Real)^2 - 4) 1 ((1 : Real)^2 - 4) ∧
    ((1 : Real)^2 - 4 = -3) := by
  constructor
  · unfold IsLimitAlong
    constructor
    · simp
    · intro ε ε_pos
      have hcont : ContinuousAt (fun x : Real => x^2 - 4) 1 :=
        helperForExample_3_1_1_continuousAt_quadraticMinusFour
      have hεδ :
          ∀ ε > 0, ∃ δ > 0, ∀ x : Real,
            dist x 1 < δ → dist (x^2 - 4) ((1 : Real)^2 - 4) < ε :=
        (Metric.continuousAt_iff (f := fun x : Real => x^2 - 4) (a := 1)).1 hcont
      rcases hεδ ε ε_pos with ⟨δ, δ_pos, hδ⟩
      refine ⟨δ, δ_pos, ?_⟩
      intro x hx
      simpa using hδ x.1 hx
  · norm_num

/-- The punctured epsilon-delta limit along `E` at `x0`, excluding the base point. -/
def IsLimitAlongPunctured
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : E,
    0 < dist x.1 x0 ∧ dist x.1 x0 < δ → dist (f x) L < ε

attribute [local instance] Classical.decEq

/-- Helper for Proposition 3.2: points in `E ∪ {x0}` distinct from `x0` lie in `E`. -/
lemma helperForProposition_3_2_mem_of_mem_union_singleton_ne
    {X : Type*} (E : Set X) (x0 x : X) (hx : x ∈ E ∪ ({x0} : Set X)) (hx0 : x ≠ x0) :
    x ∈ E := by
  have hx' : x = x0 ∨ x ∈ E := by
    simpa [Set.mem_union, Set.mem_singleton_iff] using hx
  cases hx' with
  | inl hx_eq => exact (hx0 hx_eq).elim
  | inr hxE => exact hxE

/-- Helper for Proposition 3.2: if `E ⊆ {x0}`, the punctured limit holds for any `L`. -/
lemma helperForProposition_3_2_isLimitPunctured_of_subset_singleton
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y)
    (hE : E ⊆ ({x0} : Set X)) :
    IsLimitAlongPunctured E f x0 L := by
  intro ε ε_pos
  refine ⟨1, ?_, ?_⟩
  · have : (0 : ℝ) < (1 : ℝ) := by
      norm_num
    exact this
  · intro x hx
    have hx0 : (x : X) = x0 := by
      have : (x : X) ∈ ({x0} : Set X) := hE x.property
      simpa [Set.mem_singleton_iff] using this
    have hpos : (0 : ℝ) < dist (x : X) x0 := hx.1
    have hpos0 : (0 : ℝ) < 0 := by
      have hpos' := hpos
      rw [hx0] at hpos'
      rw [dist_self] at hpos'
      exact hpos'
    have hfalse : False := (lt_irrefl 0 hpos0)
    exact hfalse.elim

/-- Helper for Proposition 3.2: if `E ⊆ {x0}`, the sequential condition is vacuous. -/
lemma helperForProposition_3_2_seqCondition_of_subset_singleton
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y)
    (hE : E ⊆ ({x0} : Set X)) :
    (∀ x : ℕ → E,
      Filter.Tendsto (fun n => (x n : X)) Filter.atTop (nhds x0) →
      (∀ n, (x n : X) ≠ x0) →
        Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds L)) := by
  intro x hx_tendsto hx_ne
  have hx0 : (x 0 : X) = x0 := by
    have : (x 0 : X) ∈ ({x0} : Set X) := hE (x 0).property
    simpa [Set.mem_singleton_iff] using this
  have hfalse : False := (hx_ne 0) hx0
  exact hfalse.elim

/-- Helper for Proposition 3.2: if `E ⊆ {x0}`, the open-set condition is vacuous. -/
lemma helperForProposition_3_2_openCondition_of_subset_singleton
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y)
    (hE : E ⊆ ({x0} : Set X)) :
    (∀ V : Set Y, IsOpen V → L ∈ V →
      ∃ U : Set X, IsOpen U ∧ x0 ∈ U ∧
        ∀ x : E, x.1 ∈ U → x.1 ≠ x0 → f x ∈ V) := by
  intro V hV hL
  refine ⟨Set.univ, isOpen_univ, ?_, ?_⟩
  · simp
  · intro x hxU hx_ne
    have hx0 : (x : X) = x0 := by
      have : (x : X) ∈ ({x0} : Set X) := hE x.property
      simpa [Set.mem_singleton_iff] using this
    exact (hx_ne hx0).elim

/-- The extension of `f` to `E ∪ {x0}` taking the value `L` at `x0`. -/
noncomputable def limitExtension
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y) :
    {x : X // x ∈ E ∪ {x0}} → Y :=
  fun x =>
    if hx0 : (x : X) = x0 then
      L
    else
      f ⟨(x : X),
        helperForProposition_3_2_mem_of_mem_union_singleton_ne E x0 (x : X) x.property
          hx0⟩

/-- Helper for Proposition 3.2: points of `E ∪ {x0}` are equal to `x0` when `E ⊆ {x0}`. -/
lemma helperForProposition_3_2_eq_x0_of_mem_union_singleton
    {X : Type*} (E : Set X) (x0 : X)
    (hE : E ⊆ ({x0} : Set X)) :
    ∀ x : {x : X // x ∈ E ∪ {x0}}, (x : X) = x0 := by
  intro x
  by_cases hx0 : (x : X) = x0
  · exact hx0
  · have hxE : (x : X) ∈ E :=
      helperForProposition_3_2_mem_of_mem_union_singleton_ne E x0 (x : X) x.property hx0
    have hx0' : (x : X) = x0 := by
      have : (x : X) ∈ ({x0} : Set X) := hE hxE
      simpa [Set.mem_singleton_iff] using this
    exact hx0'

/-- Helper for Proposition 3.2: the limit extension takes value `L` when `x = x0`. -/
lemma helperForProposition_3_2_limitExtension_eq_L_of_eq
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y)
    (x : {x : X // x ∈ E ∪ {x0}})
    (hx : (x : X) = x0) :
    limitExtension E f x0 L x = L := by
  unfold limitExtension
  simp [hx]

/-- The base point `x0` lies in `E ∪ {x0}`. -/
lemma mem_union_singleton_self {X : Type*} (E : Set X) (x0 : X) :
    x0 ∈ E ∪ {x0} := by
  simp

/-- Helper for Proposition 3.2: continuity of the limit extension for `E ⊆ {x0}`. -/
lemma helperForProposition_3_2_continuousAt_limitExtension_of_subset_singleton
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y)
    (hE : E ⊆ ({x0} : Set X)) :
    ContinuousAt (limitExtension E f x0 L) ⟨x0, mem_union_singleton_self E x0⟩ := by
  have hpos : (0 : ℝ) < (1 : ℝ) := by
    norm_num
  refine
    (Metric.continuousAt_iff
        (f := limitExtension E f x0 L)
        (a := ⟨x0, mem_union_singleton_self E x0⟩)).2 ?_
  intro ε ε_pos
  refine ⟨1, hpos, ?_⟩
  intro x hx
  have hx0 : (x : X) = x0 :=
    helperForProposition_3_2_eq_x0_of_mem_union_singleton E x0 hE x
  have hxg : limitExtension E f x0 L x = L :=
    helperForProposition_3_2_limitExtension_eq_L_of_eq E f x0 L x hx0
  have hx0g :
      limitExtension E f x0 L ⟨x0, mem_union_singleton_self E x0⟩ = L :=
    helperForProposition_3_2_limitExtension_eq_L_of_eq E f x0 L
      ⟨x0, mem_union_singleton_self E x0⟩ rfl
  have hdist :
      dist (limitExtension E f x0 L x)
        (limitExtension E f x0 L ⟨x0, mem_union_singleton_self E x0⟩) = 0 := by
    simp [hxg, hx0g]
  have hlt :
      dist (limitExtension E f x0 L x)
        (limitExtension E f x0 L ⟨x0, mem_union_singleton_self E x0⟩) < ε := by
    simpa [hdist] using ε_pos
  exact hlt

/-- Helper for Proposition 3.2: punctured epsilon-delta limit iff sequential criterion. -/
lemma helperForProposition_3_2_punctured_iff_sequence
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y) :
    IsLimitAlongPunctured E f x0 L ↔
      (∀ x : ℕ → E,
        Filter.Tendsto (fun n => (x n : X)) Filter.atTop (nhds x0) →
        (∀ n, (x n : X) ≠ x0) →
          Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds L)) := by
  constructor
  · intro hpunct x hx_tendsto hx_ne
    refine (Metric.tendsto_atTop).2 ?_
    intro ε ε_pos
    rcases hpunct ε ε_pos with ⟨δ, δ_pos, hδ⟩
    rcases (Metric.tendsto_atTop.1 hx_tendsto δ δ_pos) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hdist : dist (x n : X) x0 < δ := hN n hn
    have hpos : (0 : ℝ) < dist (x n : X) x0 := dist_pos.2 (hx_ne n)
    exact hδ (x n) ⟨hpos, hdist⟩
  · intro hseq
    classical
    by_contra hpunct
    simp [IsLimitAlongPunctured] at hpunct
    push_neg at hpunct
    rcases hpunct with ⟨ε, ε_pos, hε⟩
    have hchoice :
        ∀ n : ℕ, ∃ x : X,
          x ≠ x0 ∧ dist x x0 < (1 / ((n : ℕ) + 1)) ∧
            ∃ hxE : x ∈ E, ε ≤ dist (f ⟨x, hxE⟩) L := by
      intro n
      have hpos' : (0 : ℝ) < ((n : ℕ) + 1) := by
        exact_mod_cast (Nat.succ_pos n)
      have hpos : (0 : ℝ) < (1 / ((n : ℕ) + 1)) := by
        exact one_div_pos.mpr hpos'
      exact hε (1 / ((n : ℕ) + 1)) hpos
    choose x hx using hchoice
    have hxE_exists :
        ∀ n : ℕ, ∃ hxE : x n ∈ E, ε ≤ dist (f ⟨x n, hxE⟩) L := by
      intro n
      exact (hx n).2.2
    choose hxE hxE_ge using hxE_exists
    let xE : ℕ → E := fun n => ⟨x n, hxE n⟩
    have hx_tendsto : Filter.Tendsto (fun n => (xE n : X)) Filter.atTop (nhds x0) := by
      refine (Metric.tendsto_atTop).2 ?_
      intro δ δ_pos
      rcases exists_nat_one_div_lt δ_pos with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn
      have hdist : dist (xE n : X) x0 < (1 / ((n : ℕ) + 1)) := by
        simpa using (hx n).2.1
      have hNpos : (0 : ℝ) < ((N : ℕ) + 1) := by
        exact_mod_cast (Nat.succ_pos N)
      have hle' : ((N : ℕ) + 1 : ℝ) ≤ ((n : ℕ) + 1 : ℝ) := by
        exact_mod_cast (Nat.succ_le_succ hn)
      have hle :
          (1 / ((n : ℕ) + 1) : ℝ) ≤ (1 / ((N : ℕ) + 1)) :=
        one_div_le_one_div_of_le hNpos hle'
      have hdist' : dist (xE n : X) x0 < (1 / ((N : ℕ) + 1)) :=
        lt_of_lt_of_le hdist hle
      exact lt_of_lt_of_le hdist' (le_of_lt hN)
    have hx_ne : ∀ n, (xE n : X) ≠ x0 := by
      intro n
      exact (hx n).1
    have hfx_tendsto :
        Filter.Tendsto (fun n => f (xE n)) Filter.atTop (nhds L) :=
      hseq xE hx_tendsto hx_ne
    have hnot_tendsto :
        ¬ Filter.Tendsto (fun n => f (xE n)) Filter.atTop (nhds L) := by
      intro h_tendsto
      rcases (Metric.tendsto_atTop.1 h_tendsto ε ε_pos) with ⟨N, hN⟩
      have hdist : dist (f (xE N)) L < ε := hN N (le_rfl)
      exact (not_lt_of_ge (hxE_ge N)) hdist
    exact hnot_tendsto hfx_tendsto

/-- Helper for Proposition 3.2: punctured epsilon-delta limit iff open-set criterion. -/
lemma helperForProposition_3_2_punctured_iff_open
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y) :
    IsLimitAlongPunctured E f x0 L ↔
      (∀ V : Set Y, IsOpen V → L ∈ V →
        ∃ U : Set X, IsOpen U ∧ x0 ∈ U ∧
          ∀ x : E, x.1 ∈ U → x.1 ≠ x0 → f x ∈ V) := by
  constructor
  · intro hpunct V hV hL
    have hV_nhds : V ∈ nhds L := IsOpen.mem_nhds hV hL
    rcases (Metric.mem_nhds_iff).1 hV_nhds with ⟨ε, ε_pos, hball⟩
    rcases hpunct ε ε_pos with ⟨δ, δ_pos, hδ⟩
    refine ⟨Metric.ball x0 δ, Metric.isOpen_ball, ?_, ?_⟩
    · exact Metric.mem_ball_self δ_pos
    · intro x hxU hx_ne
      have hx_dist : dist (x : X) x0 < δ := by
        simpa [Metric.mem_ball] using hxU
      have hx_pos : (0 : ℝ) < dist (x : X) x0 := dist_pos.2 hx_ne
      have hfx : dist (f x) L < ε := hδ x ⟨hx_pos, hx_dist⟩
      have hx_ball : f x ∈ Metric.ball L ε := by
        simpa [Metric.mem_ball] using hfx
      exact hball hx_ball
  · intro hopen ε ε_pos
    have hV : IsOpen (Metric.ball L ε) := Metric.isOpen_ball
    have hL : L ∈ Metric.ball L ε := Metric.mem_ball_self ε_pos
    rcases hopen (Metric.ball L ε) hV hL with ⟨U, hU_open, hx0U, hU⟩
    have hU_nhds : U ∈ nhds x0 := IsOpen.mem_nhds hU_open hx0U
    rcases (Metric.mem_nhds_iff).1 hU_nhds with ⟨δ, δ_pos, hball⟩
    refine ⟨δ, δ_pos, ?_⟩
    intro x hx
    have hxU' : (x : X) ∈ U := by
      apply hball
      simpa [Metric.mem_ball] using hx.2
    have hx_ne : (x : X) ≠ x0 := dist_pos.1 hx.1
    have hfx : f x ∈ Metric.ball L ε := hU x hxU' hx_ne
    simpa [Metric.mem_ball] using hfx

/-- Helper for Proposition 3.2: isolated-point counterexample to the extra clause. -/
lemma helperForProposition_3_2_counterexample_isolated_point :
    ∃ (E : Set Real) (f : E → Real) (x0 L : Real),
      x0 ∈ closure E ∧
      IsLimitAlongPunctured E f x0 L ∧
      (∀ x : ℕ → E,
        Filter.Tendsto (fun n => (x n : Real)) Filter.atTop (nhds x0) →
        (∀ n, (x n : Real) ≠ x0) →
          Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds L)) ∧
      (∀ V : Set Real, IsOpen V → L ∈ V →
        ∃ U : Set Real, IsOpen U ∧ x0 ∈ U ∧
          ∀ x : E, x.1 ∈ U → x.1 ≠ x0 → f x ∈ V) ∧
      ContinuousAt (limitExtension E f x0 L) ⟨x0, mem_union_singleton_self E x0⟩ ∧
      (∃ hx0E : x0 ∈ E, ContinuousAt f ⟨x0, hx0E⟩ ∧ f ⟨x0, hx0E⟩ ≠ L) := by
  refine ⟨({0} : Set Real), (fun _ : ({0} : Set Real) => (0 : Real)),
    (0 : Real), (1 : Real), ?_⟩
  have hE : ({0} : Set Real) ⊆ ({0} : Set Real) := by
    intro x hx
    exact hx
  have hx0E : (0 : Real) ∈ ({0} : Set Real) := by
    simp
  have hx0cl : (0 : Real) ∈ closure ({0} : Set Real) := by
    exact subset_closure hx0E
  refine ⟨hx0cl, ?_⟩
  have hpunct :
      IsLimitAlongPunctured ({0} : Set Real)
        (fun _ : ({0} : Set Real) => (0 : Real)) 0 1 :=
    helperForProposition_3_2_isLimitPunctured_of_subset_singleton
      ({0} : Set Real) (fun _ : ({0} : Set Real) => (0 : Real)) 0 1 hE
  refine ⟨hpunct, ?_⟩
  have hseq :
      (∀ x : ℕ → ({0} : Set Real),
        Filter.Tendsto (fun n => (x n : Real)) Filter.atTop (nhds 0) →
        (∀ n, (x n : Real) ≠ 0) →
          Filter.Tendsto (fun n => (fun _ : ({0} : Set Real) => (0 : Real)) (x n))
            Filter.atTop (nhds 1)) :=
    helperForProposition_3_2_seqCondition_of_subset_singleton
      ({0} : Set Real) (fun _ : ({0} : Set Real) => (0 : Real)) 0 1 hE
  refine ⟨hseq, ?_⟩
  have hopen :
      (∀ V : Set Real, IsOpen V → (1 : Real) ∈ V →
        ∃ U : Set Real, IsOpen U ∧ (0 : Real) ∈ U ∧
          ∀ x : ({0} : Set Real), x.1 ∈ U → x.1 ≠ (0 : Real) →
            (fun _ : ({0} : Set Real) => (0 : Real)) x ∈ V) :=
    helperForProposition_3_2_openCondition_of_subset_singleton
      ({0} : Set Real) (fun _ : ({0} : Set Real) => (0 : Real)) 0 1 hE
  refine ⟨hopen, ?_⟩
  have hcont :
      ContinuousAt
        (limitExtension ({0} : Set Real) (fun _ : ({0} : Set Real) => (0 : Real)) 0 1)
        ⟨0, mem_union_singleton_self ({0} : Set Real) 0⟩ :=
    helperForProposition_3_2_continuousAt_limitExtension_of_subset_singleton
      ({0} : Set Real) (fun _ : ({0} : Set Real) => (0 : Real)) 0 1 hE
  refine ⟨hcont, ?_⟩
  refine ⟨hx0E, ?_⟩
  have hcontf :
      ContinuousAt (fun _ : ({0} : Set Real) => (0 : Real)) ⟨0, hx0E⟩ := by
    simpa using
      (continuousAt_const :
        ContinuousAt (fun _ : ({0} : Set Real) => (0 : Real)) ⟨0, hx0E⟩)
  refine ⟨hcontf, ?_⟩
  simp

/-- Helper for Proposition 3.2: a non-isolated base point forces `f x0 = L` from a punctured limit and continuity on `E`. -/
lemma helperForProposition_3_2_value_eq_of_nonisolated_and_puncturedLimit_and_continuousAt
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y)
    (hx0cl : x0 ∈ closure (E \ {x0})) :
    IsLimitAlongPunctured E f x0 L →
    ∀ hx0E : x0 ∈ E, ContinuousAt f ⟨x0, hx0E⟩ → f ⟨x0, hx0E⟩ = L := by
  intro hpunct hx0E hcont
  by_contra hne
  have hpos : 0 < dist (f ⟨x0, hx0E⟩) L := dist_pos.2 hne
  have hlimit :
      ∀ ε > 0, dist (f ⟨x0, hx0E⟩) L < ε := by
    intro ε ε_pos
    have ε_half_pos : 0 < ε / 2 := by
      linarith
    rcases hpunct (ε / 2) ε_half_pos with ⟨δ1, δ1_pos, hδ1⟩
    have hcont_εδ :=
      (Metric.continuousAt_iff (f := f) (a := ⟨x0, hx0E⟩)).1 hcont
    rcases hcont_εδ (ε / 2) ε_half_pos with ⟨δ2, δ2_pos, hδ2⟩
    have hδ_pos : (0 : ℝ) < min δ1 δ2 := by
      exact lt_min δ1_pos δ2_pos
    rcases (Metric.mem_closure_iff.1 hx0cl) (min δ1 δ2) hδ_pos with ⟨x, hx_mem, hx_dist⟩
    have hx_dist' : dist x x0 < min δ1 δ2 := by
      simpa [dist_comm] using hx_dist
    have hxE : x ∈ E := hx_mem.1
    have hx_ne : x ≠ x0 := by
      intro hx_eq
      have : x ∈ ({x0} : Set X) := by
        simpa [Set.mem_singleton_iff] using hx_eq
      exact hx_mem.2 this
    let xE : E := ⟨x, hxE⟩
    have hx_dist1 : dist x x0 < δ1 := lt_of_lt_of_le hx_dist' (min_le_left _ _)
    have hx_dist2 : dist x x0 < δ2 := lt_of_lt_of_le hx_dist' (min_le_right _ _)
    have hx_pos : (0 : ℝ) < dist x x0 := dist_pos.2 hx_ne
    have hfxL : dist (f xE) L < ε / 2 := hδ1 xE ⟨hx_pos, hx_dist1⟩
    have hfx0 : dist (f ⟨x0, hx0E⟩) (f xE) < ε / 2 := by
      have hx_dist2' : dist xE ⟨x0, hx0E⟩ < δ2 := by
        simpa using hx_dist2
      have htmp : dist (f xE) (f ⟨x0, hx0E⟩) < ε / 2 := hδ2 (x := xE) hx_dist2'
      simpa [dist_comm] using htmp
    have hdist_triangle :
        dist (f ⟨x0, hx0E⟩) L ≤
          dist (f ⟨x0, hx0E⟩) (f xE) + dist (f xE) L :=
      dist_triangle _ _ _
    have hsum_lt : dist (f ⟨x0, hx0E⟩) (f xE) + dist (f xE) L < ε := by
      have hsum :
          dist (f ⟨x0, hx0E⟩) (f xE) + dist (f xE) L < ε / 2 + ε / 2 :=
        add_lt_add hfx0 hfxL
      have hsum' : ε / 2 + ε / 2 = ε := by
        linarith
      simpa [hsum'] using hsum
    exact lt_of_le_of_lt hdist_triangle hsum_lt
  have hhalf_pos : 0 < dist (f ⟨x0, hx0E⟩) L / 2 := by
    linarith
  have hlt : dist (f ⟨x0, hx0E⟩) L < dist (f ⟨x0, hx0E⟩) L / 2 :=
    hlimit _ hhalf_pos
  linarith

/-- Proposition 3.2: Let `E ⊆ X` and `f : E → Y`, and let `x0` be an adherent point
of `E` with `L ∈ Y`. The following are equivalent: (a) the punctured epsilon-delta
limit of `f` along `E` at `x0` equals `L`; (b) for every sequence in `E` converging
to `x0` with all terms distinct from `x0`, the sequence of `f`-values converges to
`L`; (c) for every open `V ⊆ Y` with `L ∈ V`, there is an open `U ⊆ X` with `x0 ∈ U`
such that `f(U ∩ E \ {x0}) ⊆ V`; (d) the extension `g` to `E ∪ {x0}` with `g(x0)=L`
and `g|_{E\{x0}} = f` is continuous at `x0`, and if `x0 ∈ E` and `f` is continuous
at `x0` (as a function on `E`), then `f x0 = L`. -/
theorem limit_along_equiv_sequence_open_continuous
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L : Y) :
    x0 ∈ closure E →
      ((IsLimitAlongPunctured E f x0 L) ↔
        (∀ x : ℕ → E,
          Filter.Tendsto (fun n => (x n : X)) Filter.atTop (nhds x0) →
          (∀ n, (x n : X) ≠ x0) →
            Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds L))) ∧
      ((∀ x : ℕ → E,
          Filter.Tendsto (fun n => (x n : X)) Filter.atTop (nhds x0) →
          (∀ n, (x n : X) ≠ x0) →
            Filter.Tendsto (fun n => f (x n)) Filter.atTop (nhds L)) ↔
        (∀ V : Set Y, IsOpen V → L ∈ V →
          ∃ U : Set X, IsOpen U ∧ x0 ∈ U ∧
            ∀ x : E, x.1 ∈ U → x.1 ≠ x0 → f x ∈ V)) ∧
      ((∀ V : Set Y, IsOpen V → L ∈ V →
          ∃ U : Set X, IsOpen U ∧ x0 ∈ U ∧
            ∀ x : E, x.1 ∈ U → x.1 ≠ x0 → f x ∈ V) ↔
        (ContinuousAt (limitExtension E f x0 L) ⟨x0, mem_union_singleton_self E x0⟩ ∧
          (x0 ∈ closure (E \ {x0}) →
            ∀ hx0E : x0 ∈ E, ContinuousAt f ⟨x0, hx0E⟩ → f ⟨x0, hx0E⟩ = L))) := by
  intro hx0
  have hpunct_seq :=
    helperForProposition_3_2_punctured_iff_sequence (E := E) (f := f) (x0 := x0) (L := L)
  have hpunct_open :=
    helperForProposition_3_2_punctured_iff_open (E := E) (f := f) (x0 := x0) (L := L)
  constructor
  · -- (a) ↔ (b)
    exact hpunct_seq
  · constructor
    · -- (b) ↔ (c)
      constructor
      · intro hseq
        exact (hpunct_open).1 ((hpunct_seq).2 hseq)
      · intro hopen
        exact (hpunct_seq).1 ((hpunct_open).2 hopen)
    · -- (c) ↔ (d)
      constructor
      · -- (c) → (d)
        intro hopen
        have hpunct :
            IsLimitAlongPunctured E f x0 L :=
          (hpunct_open).2 hopen
        constructor
        · refine
            (Metric.continuousAt_iff
                (f := limitExtension E f x0 L)
                (a := ⟨x0, mem_union_singleton_self E x0⟩)).2 ?_
          intro ε ε_pos
          rcases hpunct ε ε_pos with ⟨δ, δ_pos, hδ⟩
          refine ⟨δ, δ_pos, ?_⟩
          intro x hx
          by_cases hx0' : (x : X) = x0
          · have hxL :
                limitExtension E f x0 L x = L :=
              helperForProposition_3_2_limitExtension_eq_L_of_eq E f x0 L x hx0'
            have hx0L :
                limitExtension E f x0 L ⟨x0, mem_union_singleton_self E x0⟩ = L :=
              helperForProposition_3_2_limitExtension_eq_L_of_eq E f x0 L
                ⟨x0, mem_union_singleton_self E x0⟩ rfl
            have hdist :
                dist (limitExtension E f x0 L x)
                  (limitExtension E f x0 L ⟨x0, mem_union_singleton_self E x0⟩) = 0 := by
              simp [hxL, hx0L]
            have hlt :
                dist (limitExtension E f x0 L x)
                  (limitExtension E f x0 L ⟨x0, mem_union_singleton_self E x0⟩) < ε := by
              simpa [hdist] using ε_pos
            exact hlt
          · have hxE : (x : X) ∈ E :=
              helperForProposition_3_2_mem_of_mem_union_singleton_ne E x0 (x : X) x.property hx0'
            let xE : E := ⟨(x : X), hxE⟩
            have hxg : limitExtension E f x0 L x = f xE := by
              unfold limitExtension
              simp [hx0', xE]
            have hx0g :
                limitExtension E f x0 L ⟨x0, mem_union_singleton_self E x0⟩ = L :=
              helperForProposition_3_2_limitExtension_eq_L_of_eq E f x0 L
                ⟨x0, mem_union_singleton_self E x0⟩ rfl
            have hx_dist : dist (x : X) x0 < δ := by
              simpa using hx
            have hx_pos : (0 : ℝ) < dist (x : X) x0 := dist_pos.2 hx0'
            have hdist_f : dist (f xE) L < ε := hδ xE ⟨hx_pos, hx_dist⟩
            have hdist_g :
                dist (limitExtension E f x0 L x)
                  (limitExtension E f x0 L ⟨x0, mem_union_singleton_self E x0⟩) < ε := by
              simpa [hxg, hx0g] using hdist_f
            exact hdist_g
        · -- extra clause
          intro hx0cl hx0E hcont
          exact
            helperForProposition_3_2_value_eq_of_nonisolated_and_puncturedLimit_and_continuousAt
              (E := E) (f := f) (x0 := x0) (L := L) hx0cl hpunct hx0E hcont
      · -- (d) → (c)
        intro hd V hV hL
        rcases hd with ⟨hcont, hfx0⟩
        have hV_nhds : V ∈ nhds L := IsOpen.mem_nhds hV hL
        rcases (Metric.mem_nhds_iff).1 hV_nhds with ⟨ε, ε_pos, hball⟩
        have hcont_εδ :=
          (Metric.continuousAt_iff
              (f := limitExtension E f x0 L)
              (a := ⟨x0, mem_union_singleton_self E x0⟩)).1 hcont
        rcases hcont_εδ ε ε_pos with ⟨δ, δ_pos, hδ⟩
        refine ⟨Metric.ball x0 δ, Metric.isOpen_ball, ?_, ?_⟩
        · exact Metric.mem_ball_self δ_pos
        · intro x hxU hx_ne
          have hx_dist : dist (x : X) x0 < δ := by
            simpa [Metric.mem_ball] using hxU
          have hx_union : (x : X) ∈ E ∪ {x0} := by
            exact Or.inl x.property
          let x' : {x : X // x ∈ E ∪ {x0}} := ⟨x.1, hx_union⟩
          have hx_dist' :
              dist x' ⟨x0, mem_union_singleton_self E x0⟩ < δ := by
            simpa using hx_dist
          have hdist_g :
              dist (limitExtension E f x0 L x')
                (limitExtension E f x0 L ⟨x0, mem_union_singleton_self E x0⟩) < ε :=
            hδ hx_dist'
          have hx_val : limitExtension E f x0 L x' = f x := by
            have hx0' : (x' : X) ≠ x0 := by
              simpa using hx_ne
            have hx_eq' :
                (⟨(x' : X),
                  helperForProposition_3_2_mem_of_mem_union_singleton_ne E x0 (x' : X)
                    x'.property hx0'⟩ : E) = x := by
              apply Subtype.ext
              rfl
            have hfx' :
                f ⟨(x' : X),
                  helperForProposition_3_2_mem_of_mem_union_singleton_ne E x0 (x' : X)
                    x'.property hx0'⟩ = f x := by
              simpa using congrArg f hx_eq'
            unfold limitExtension
            simp [hx0', hfx']
          have hx0_val :
              limitExtension E f x0 L ⟨x0, mem_union_singleton_self E x0⟩ = L := by
            exact helperForProposition_3_2_limitExtension_eq_L_of_eq E f x0 L
              ⟨x0, mem_union_singleton_self E x0⟩ rfl
          have hdist_f : dist (f x) L < ε := by
            simpa [hx_val, hx0_val] using hdist_g
          have hx_ball : f x ∈ Metric.ball L ε := by
            simpa [Metric.mem_ball] using hdist_f
          exact hball hx_ball

/-- Proposition 3.3: [Uniqueness of limit] If the limit of `f` at `x0` along `E`
equals both `L` and `M`, then `L = M`. -/
theorem limit_along_unique
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (E : Set X) (f : E → Y) (x0 : X) (L M : Y)
    (hL : IsLimitAlong E f x0 L) (hM : IsLimitAlong E f x0 M) :
    L = M := by
  by_contra hne
  have hpos : 0 < dist L M := dist_pos.2 hne
  have hhalf_pos : 0 < dist L M / 2 := by
    linarith
  rcases hL with ⟨hx0cl, hLlim⟩
  rcases hM with ⟨_, hMlim⟩
  rcases hLlim (dist L M / 2) hhalf_pos with ⟨δ1, δ1_pos, hδ1⟩
  rcases hMlim (dist L M / 2) hhalf_pos with ⟨δ2, δ2_pos, hδ2⟩
  have hδ_pos : (0 : ℝ) < min δ1 δ2 := lt_min δ1_pos δ2_pos
  rcases (Metric.mem_closure_iff.1 hx0cl) (min δ1 δ2) hδ_pos with
    ⟨x, hxE, hx_dist⟩
  let xE : E := ⟨x, hxE⟩
  have hx_dist' : dist x x0 < min δ1 δ2 := by
    simpa [dist_comm] using hx_dist
  have hx_dist1 : dist x x0 < δ1 := lt_of_lt_of_le hx_dist' (min_le_left _ _)
  have hx_dist2 : dist x x0 < δ2 := lt_of_lt_of_le hx_dist' (min_le_right _ _)
  have hLx : dist (f xE) L < dist L M / 2 := hδ1 xE hx_dist1
  have hMx : dist (f xE) M < dist L M / 2 := hδ2 xE hx_dist2
  have hLx' : dist L (f xE) < dist L M / 2 := by
    simpa [dist_comm] using hLx
  have htriangle :
      dist L M ≤ dist L (f xE) + dist (f xE) M :=
    dist_triangle _ _ _
  have hsum_lt : dist L (f xE) + dist (f xE) M < dist L M := by
    have hsum :
        dist L (f xE) + dist (f xE) M < dist L M / 2 + dist L M / 2 :=
      add_lt_add hLx' hMx
    have hsum' : dist L M / 2 + dist L M / 2 = dist L M := by
      linarith
    simpa [hsum'] using hsum
  have hlt : dist L M < dist L M := lt_of_le_of_lt htriangle hsum_lt
  exact (lt_irrefl _ hlt)

end Section01
end Chap03
