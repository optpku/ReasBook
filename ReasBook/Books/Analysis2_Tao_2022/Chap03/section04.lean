/-
Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap03
section Section04

/-- Definition 3.5 (Space of bounded functions): for metric spaces `X` and `Y`, define
`B(X → Y)` as the set of functions `f : X → Y` for which there exist `y0 : Y` and
`M < ∞` such that `dist (f x) y0 ≤ M` for all `x : X`. -/
def boundedFunctionSpace (X Y : Type*) [MetricSpace Y] : Set (X -> Y) :=
  {f : X -> Y | ∃ y0 : Y, ∃ M : ℝ, ∀ x : X, dist (f x) y0 <= M}

attribute [local instance] Classical.propDecidable

/-- Definition 3.6: [Uniform (supremum) metric] If `X` is nonempty, define
`d_∞(f,g) = sup_{x ∈ X} dist (f x) (g x)` for `f,g ∈ B(X → Y)`; if `X` is empty, set
`d_∞(f,g) = 0` for all `f,g ∈ B(X → Y)`. -/
noncomputable def uniformSupMetric (X Y : Type*) [MetricSpace Y]
    (f g : {f : X → Y // f ∈ boundedFunctionSpace X Y}) : ℝ :=
  if _ : IsEmpty X then 0 else
    sSup (Set.range (fun x : X => dist (f.1 x) (g.1 x)))

/-- Definition 3.7 [Bounded continuous functions]: for metric spaces `X` and `Y`, define
`C(X → Y)` as the set of bounded functions `f : X → Y` that are continuous. -/
def boundedContinuousFunctionSpace (X Y : Type*) [MetricSpace X] [MetricSpace Y] :
    Set (X → Y) :=
  {f : X → Y | f ∈ boundedFunctionSpace X Y ∧ Continuous f}

/-- The unit interval as a subtype of `ℝ`. -/
abbrev unitIntervalSubtype : Type := {x : ℝ // x ∈ Set.Icc (0:ℝ) 1}

/-- The function `x ↦ 2x` on the unit interval is bounded. -/
lemma doubleOnUnitInterval_bounded :
    (fun x : unitIntervalSubtype => (2:ℝ) * x.1) ∈
      boundedFunctionSpace unitIntervalSubtype ℝ := by
  refine ⟨0, 2, ?_⟩
  intro x
  have hx0 : 0 ≤ x.1 := x.2.1
  have hx1 : x.1 ≤ 1 := x.2.2
  have hmul_nonneg : 0 ≤ (2:ℝ) * x.1 := by
    have h2 : 0 ≤ (2:ℝ) := by norm_num
    exact mul_nonneg h2 hx0
  have hmul_le : (2:ℝ) * x.1 ≤ 2 := by
    have h2 : 0 ≤ (2:ℝ) := by norm_num
    have h := mul_le_mul_of_nonneg_left hx1 h2
    simpa using h
  calc
    dist ((2:ℝ) * x.1) 0 = |(2:ℝ) * x.1 - 0| := by
      simp
    _ = |(2:ℝ) * x.1| := by simp
    _ = (2:ℝ) * x.1 := by simp [abs_of_nonneg hmul_nonneg]
    _ ≤ (2:ℝ) := hmul_le

/-- The function `x ↦ 3x` on the unit interval is bounded. -/
lemma tripleOnUnitInterval_bounded :
    (fun x : unitIntervalSubtype => (3:ℝ) * x.1) ∈
      boundedFunctionSpace unitIntervalSubtype ℝ := by
  refine ⟨0, 3, ?_⟩
  intro x
  have hx0 : 0 ≤ x.1 := x.2.1
  have hx1 : x.1 ≤ 1 := x.2.2
  have hmul_nonneg : 0 ≤ (3:ℝ) * x.1 := by
    have h3 : 0 ≤ (3:ℝ) := by norm_num
    exact mul_nonneg h3 hx0
  have hmul_le : (3:ℝ) * x.1 ≤ 3 := by
    have h3 : 0 ≤ (3:ℝ) := by norm_num
    have h := mul_le_mul_of_nonneg_left hx1 h3
    simpa using h
  calc
    dist ((3:ℝ) * x.1) 0 = |(3:ℝ) * x.1 - 0| := by
      simp
    _ = |(3:ℝ) * x.1| := by simp
    _ = (3:ℝ) * x.1 := by simp [abs_of_nonneg hmul_nonneg]
    _ ≤ (3:ℝ) := hmul_le

/-- The function `x ↦ 2x` on the unit interval, as an element of the bounded function space. -/
def doubleOnUnitInterval :
    {f : unitIntervalSubtype -> ℝ // f ∈ boundedFunctionSpace unitIntervalSubtype ℝ} :=
  ⟨fun x : unitIntervalSubtype => (2:ℝ) * x.1, doubleOnUnitInterval_bounded⟩

/-- The function `x ↦ 3x` on the unit interval, as an element of the bounded function space. -/
def tripleOnUnitInterval :
    {f : unitIntervalSubtype -> ℝ // f ∈ boundedFunctionSpace unitIntervalSubtype ℝ} :=
  ⟨fun x : unitIntervalSubtype => (3:ℝ) * x.1, tripleOnUnitInterval_bounded⟩

/-- Helper for Example 3.4.3: the unit interval subtype is nonempty. -/
lemma helperForExample_3_4_3_not_isEmpty_unitIntervalSubtype :
    ¬ IsEmpty unitIntervalSubtype := by
  intro h
  have hx : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    constructor
    · exact le_rfl
    · exact zero_le_one
  let x : unitIntervalSubtype := ⟨0, hx⟩
  exact h.elim x

/-- Helper for Example 3.4.3: the distance between `2x` and `3x` is `x` on `[0,1]`. -/
lemma helperForExample_3_4_3_dist_double_triple :
    ∀ x : unitIntervalSubtype, dist ((2:ℝ) * x.1) ((3:ℝ) * x.1) = x.1 := by
  intro x
  have hx0 : 0 ≤ x.1 := x.2.1
  calc
    dist ((2:ℝ) * x.1) ((3:ℝ) * x.1) = |(2:ℝ) * x.1 - (3:ℝ) * x.1| := by
      simp [Real.dist_eq]
    _ = |-(x.1)| := by ring_nf
    _ = |x.1| := by simp
    _ = x.1 := by simp [abs_of_nonneg hx0]

/-- Helper for Example 3.4.3: the range of the coercion from `[0,1]` is `Set.Icc 0 1`. -/
lemma helperForExample_3_4_3_range_coe_unitIntervalSubtype :
    Set.range (fun x : unitIntervalSubtype => x.1) = Set.Icc (0:ℝ) 1 := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨x, rfl⟩
    exact x.2
  · intro hy
    refine ⟨⟨y, hy⟩, rfl⟩

/-- Example 3.4.3: for `X = [0,1]` and `Y = ℝ` with the usual metrics, if
`f(x)=2x` and `g(x)=3x`, then `d_∞(f,g)=1`. -/
lemma uniformSupMetric_double_triple_unitInterval :
    uniformSupMetric unitIntervalSubtype ℝ doubleOnUnitInterval tripleOnUnitInterval = 1 := by
  calc
    uniformSupMetric unitIntervalSubtype ℝ doubleOnUnitInterval tripleOnUnitInterval
        =
        sSup
          (Set.range
            (fun x : unitIntervalSubtype =>
              dist ((2:ℝ) * x.1) ((3:ℝ) * x.1))) := by
          simp [uniformSupMetric, doubleOnUnitInterval, tripleOnUnitInterval]
    _ = sSup (Set.range (fun x : unitIntervalSubtype => x.1)) := by
          refine congrArg sSup ?_
          ext y
          constructor
          · intro hy
            rcases hy with ⟨x, rfl⟩
            refine ⟨x, ?_⟩
            exact (helperForExample_3_4_3_dist_double_triple x).symm
          · intro hy
            rcases hy with ⟨x, rfl⟩
            refine ⟨x, ?_⟩
            exact helperForExample_3_4_3_dist_double_triple x
    _ = sSup (Set.Icc (0:ℝ) 1) := by
          rw [helperForExample_3_4_3_range_coe_unitIntervalSubtype]
    _ = 1 := by
          simp [csSup_Icc (a:=(0:ℝ)) (b:=1) zero_le_one]

/-- Helper for Proposition 3.4.4: the range of pointwise distances is bounded above. -/
lemma helperForProposition_3_4_4_bddAbove_dist_range
    {X Y : Type*} [MetricSpace Y]
    (f g : {f : X → Y // f ∈ boundedFunctionSpace X Y}) :
    BddAbove (Set.range (fun x : X => dist (f.1 x) (g.1 x))) := by
  rcases f.property with ⟨y1, M1, h1⟩
  rcases g.property with ⟨y2, M2, h2⟩
  refine ⟨M1 + dist y1 y2 + M2, ?_⟩
  intro y hy
  rcases hy with ⟨x, rfl⟩
  have htriangle :
      dist (f.1 x) (g.1 x) ≤ dist (f.1 x) y1 + dist y1 y2 + dist y2 (g.1 x) :=
    dist_triangle4 (f.1 x) y1 y2 (g.1 x)
  have h1' : dist (f.1 x) y1 ≤ M1 := h1 x
  have h2' : dist (g.1 x) y2 ≤ M2 := h2 x
  have h2'' : dist y2 (g.1 x) ≤ M2 := by
    simpa [dist_comm] using h2'
  have hsum :
      dist (f.1 x) y1 + dist y1 y2 + dist y2 (g.1 x) ≤ M1 + dist y1 y2 + M2 := by
    linarith
  exact le_trans htriangle hsum

/-- Helper for Proposition 3.4.4: each pointwise distance is bounded by the uniform metric. -/
lemma helperForProposition_3_4_4_dist_le_uniformSupMetric
    {X Y : Type*} [MetricSpace Y] (hX : ¬ IsEmpty X)
    (f g : {f : X → Y // f ∈ boundedFunctionSpace X Y}) (x : X) :
    dist (f.1 x) (g.1 x) ≤ uniformSupMetric X Y f g := by
  classical
  have hbdd :
      BddAbove (Set.range (fun x : X => dist (f.1 x) (g.1 x))) :=
    helperForProposition_3_4_4_bddAbove_dist_range (X := X) (Y := Y) f g
  have hle :
      dist (f.1 x) (g.1 x) ≤
        sSup (Set.range (fun x : X => dist (f.1 x) (g.1 x))) :=
    le_csSup hbdd ⟨x, rfl⟩
  simpa [uniformSupMetric, hX] using hle

/-- Helper for Proposition 3.4.4: a uniform pointwise bound controls the uniform metric. -/
lemma helperForProposition_3_4_4_uniformSupMetric_le_of_forall_dist_le
    {X Y : Type*} [MetricSpace Y] (hX : ¬ IsEmpty X)
    (f g : {f : X → Y // f ∈ boundedFunctionSpace X Y}) (R : ℝ)
    (hR : ∀ x : X, dist (f.1 x) (g.1 x) ≤ R) :
    uniformSupMetric X Y f g ≤ R := by
  classical
  have hbdd :
      BddAbove (Set.range (fun x : X => dist (f.1 x) (g.1 x))) :=
    helperForProposition_3_4_4_bddAbove_dist_range (X := X) (Y := Y) f g
  have hX' : Nonempty X := by
    by_contra hX'
    have hX'' : IsEmpty X := by
      refine ⟨?_⟩
      intro x
      exact hX' ⟨x⟩
    exact hX hX''
  classical
  let x0 : X := Classical.choice hX'
  have hnonempty : (Set.range (fun x : X => dist (f.1 x) (g.1 x))).Nonempty := by
    refine ⟨dist (f.1 x0) (g.1 x0), ?_⟩
    exact ⟨x0, rfl⟩
  have hsup :
      sSup (Set.range (fun x : X => dist (f.1 x) (g.1 x))) ≤ R := by
    refine csSup_le (s := Set.range (fun x : X => dist (f.1 x) (g.1 x)))
      (a := R) (h₁ := hnonempty) ?_
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact hR x
  simpa [uniformSupMetric, hX] using hsup

/-- Helper for Proposition 3.4.4: the uniform metric is nonnegative. -/
lemma helperForProposition_3_4_4_uniformSupMetric_nonneg
    {X Y : Type*} [MetricSpace Y]
    (f g : {f : X → Y // f ∈ boundedFunctionSpace X Y}) :
    0 ≤ uniformSupMetric X Y f g := by
  classical
  by_cases hX : IsEmpty X
  · simp [uniformSupMetric, hX]
  · have hX' : Nonempty X := by
      by_contra hX'
      have hX'' : IsEmpty X := by
        refine ⟨?_⟩
        intro x
        exact hX' ⟨x⟩
      exact hX hX''
    classical
    let x0 : X := Classical.choice hX'
    have hle :
        dist (f.1 x0) (g.1 x0) ≤ uniformSupMetric X Y f g :=
      helperForProposition_3_4_4_dist_le_uniformSupMetric (X := X) (Y := Y) hX f g x0
    exact le_trans (dist_nonneg) hle

/-- Proposition 3.4.4: Let `X` and `Y` be metric spaces and let `f^{(n)}` be a sequence in
`B(X → Y)` with `f ∈ B(X → Y)`. Then the following are equivalent: (1) `d_∞(f^{(n)}, f) → 0`
as `n → ∞`; (2) `f^{(n)} → f` uniformly on `X` (i.e. the usual `ε`–`N` condition). -/
theorem tendsto_uniformSupMetric_iff_uniformlyConvergent
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (fseq : ℕ → {f : X → Y // f ∈ boundedFunctionSpace X Y})
    (f : {f : X → Y // f ∈ boundedFunctionSpace X Y}) :
    (Filter.Tendsto (fun n => uniformSupMetric X Y (fseq n) f)
      Filter.atTop (nhds (0 : ℝ))) ↔
      TendstoUniformly (fun n => (fseq n).1) f.1 Filter.atTop := by
  classical
  by_cases hX : IsEmpty X
  · constructor
    · intro _
      refine (Metric.tendstoUniformly_iff).2 ?_
      intro ε hε
      refine Filter.eventually_atTop.2 ?_
      refine ⟨0, ?_⟩
      intro n hn x
      exact hX.elim x
    · intro _
      have hconst :
          Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds (0 : ℝ)) :=
        tendsto_const_nhds
      simpa [uniformSupMetric, hX] using hconst
  · constructor
    · intro hT
      refine (Metric.tendstoUniformly_iff).2 ?_
      intro ε hε
      rcases (Metric.tendsto_atTop.1 hT) ε hε with ⟨N, hN⟩
      refine Filter.eventually_atTop.2 ?_
      refine ⟨N, ?_⟩
      intro n hn x
      have hn' : dist (uniformSupMetric X Y (fseq n) f) (0 : ℝ) < ε := hN n hn
      have hle' :
          dist ((fseq n).1 x) (f.1 x) ≤ uniformSupMetric X Y (fseq n) f :=
        helperForProposition_3_4_4_dist_le_uniformSupMetric
          (X := X) (Y := Y) hX (fseq n) f x
      have hle :
          dist (f.1 x) ((fseq n).1 x) ≤ uniformSupMetric X Y (fseq n) f := by
        simpa [dist_comm] using hle'
      have hnonneg :
          0 ≤ uniformSupMetric X Y (fseq n) f :=
        helperForProposition_3_4_4_uniformSupMetric_nonneg (X := X) (Y := Y) (fseq n) f
      have hlt :
          uniformSupMetric X Y (fseq n) f < ε := by
        simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hn'
      exact lt_of_le_of_lt hle hlt
    · intro hU
      refine Metric.tendsto_atTop.2 ?_
      intro ε hε
      have hε2 : 0 < ε / 2 := by
        linarith
      have hU' :
          ∀ᶠ n in Filter.atTop, ∀ x : X,
            dist (f.1 x) ((fseq n).1 x) < ε / 2 :=
        (Metric.tendstoUniformly_iff).1 hU (ε / 2) hε2
      rcases Filter.eventually_atTop.1 hU' with ⟨N, hN⟩
      refine ⟨N, ?_⟩
      intro n hn
      have hle :
          uniformSupMetric X Y (fseq n) f ≤ ε / 2 := by
        have hdist_le : ∀ x : X, dist ((fseq n).1 x) (f.1 x) ≤ ε / 2 := by
          intro x
          have hlt : dist (f.1 x) ((fseq n).1 x) < ε / 2 := hN n hn x
          have hlt' : dist ((fseq n).1 x) (f.1 x) < ε / 2 := by
            simpa [dist_comm] using hlt
          exact le_of_lt hlt'
        exact
          helperForProposition_3_4_4_uniformSupMetric_le_of_forall_dist_le
            (X := X) (Y := Y) hX (fseq n) f (ε / 2) hdist_le
      have hhalf : (ε / 2 : ℝ) < ε := by
        linarith
      have hlt :
          uniformSupMetric X Y (fseq n) f < ε :=
        lt_of_le_of_lt hle hhalf
      have hnonneg :
          0 ≤ uniformSupMetric X Y (fseq n) f :=
        helperForProposition_3_4_4_uniformSupMetric_nonneg (X := X) (Y := Y) (fseq n) f
      simpa [Real.dist_eq, abs_of_nonneg hnonneg] using hlt

/-- Proposition 3.4.5 (Inclusion into bounded functions): for metric spaces `X` and `Y`,
`C(X → Y)` is a subset of `B(X → Y)`. -/
theorem boundedContinuousFunctionSpace_subset_boundedFunctionSpace
    (X Y : Type*) [MetricSpace X] [MetricSpace Y] :
    boundedContinuousFunctionSpace X Y ⊆ boundedFunctionSpace X Y := by
  intro f hf
  dsimp [boundedContinuousFunctionSpace] at hf
  exact hf.1

/-- Theorem 3.4.5 (Completeness of bounded continuous functions): for metric spaces `X` and `Y`
with `Y` complete, the space of bounded continuous functions `C(X → Y)` is complete with
respect to the uniform metric (equivalently, every Cauchy sequence converges uniformly to a
bounded continuous function). -/
theorem completeSpace_boundedContinuousFunction
    (X Y : Type*) [MetricSpace X] [MetricSpace Y] [CompleteSpace Y] :
    CompleteSpace (BoundedContinuousFunction X Y) := by
  infer_instance

/-- Proposition 3.4.6 (Uniform limits preserve continuity): let `X` and `Y` be metric spaces.
If `(fseq n)` is a sequence of functions `X → Y` converging uniformly to `f` (with respect to
the uniform metric), and each `fseq n` is continuous, then `f` is continuous. -/
theorem continuous_of_tendstoUniformly
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (fseq : ℕ → X → Y) (f : X → Y)
    (hcont : ∀ n, Continuous (fseq n))
    (hconv : TendstoUniformly fseq f Filter.atTop) :
    Continuous f := by
  have hFreq : ∃ᶠ n in Filter.atTop, Continuous (fseq n) :=
    Filter.Frequently.of_forall hcont
  exact hconv.continuous hFreq

end Section04
end Chap03
