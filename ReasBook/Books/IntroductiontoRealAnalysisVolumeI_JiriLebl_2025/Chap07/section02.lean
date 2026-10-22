/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap07
section Section02

section

variable {X : Type*} [PseudoMetricSpace X] (x : X) (δ : ℝ)

/-- Definition 7.2.1. In a metric space `(X, d)`, the open ball (ball) of radius
`δ > 0` around `x` is `B(x, δ) = { y ∈ X | d(x, y) < δ }`, and the closed ball is
`C(x, δ) = { y ∈ X | d(x, y) ≤ δ }`. -/
def openBall : Set X := {y : X | dist y x < δ}

/-- Closed ball with center `x` and radius `δ`. -/
def closedBall : Set X := {y : X | dist y x ≤ δ}

/-- The book's open ball agrees with `Metric.ball`. -/
theorem openBall_eq_metric_ball : openBall x δ = Metric.ball x δ := by
  rfl

/-- The book's closed ball agrees with `Metric.closedBall`. -/
theorem closedBall_eq_metric_closedBall :
    closedBall x δ = Metric.closedBall x δ := by
  rfl

end

section

variable (x δ : ℝ)

/-- Example 7.2.2. In `ℝ` with its usual metric, the open ball `B(x, δ)` of
radius `δ > 0` around `x` is the open interval `(x - δ, x + δ)`, and the closed
ball `C(x, δ)` is the closed interval `[x - δ, x + δ]`. -/
lemma real_openBall_eq_Ioo :
    openBall x δ = Set.Ioo (x - δ) (x + δ) := by
  ext y; constructor
  · intro hy
    have hy' : |x - y| < δ := by
      have : |y - x| < δ := by
        simpa [openBall, Real.dist_eq] using hy
      simpa [abs_sub_comm] using this
    obtain ⟨h₁, h₂⟩ := abs_sub_lt_iff.mp hy'
    have hx : x - δ < y := by linarith
    have hy'' : y < x + δ := by linarith
    exact ⟨hx, hy''⟩
  · intro hy
    have hx : x - y < δ := by linarith [hy.1]
    have hy_lt : y - x < δ := by linarith [hy.2]
    have h : |x - y| < δ := abs_sub_lt_iff.mpr ⟨hx, hy_lt⟩
    have h' : |y - x| < δ := by simpa [abs_sub_comm] using h
    simpa [openBall, Real.dist_eq] using h'

lemma real_closedBall_eq_Icc :
    closedBall x δ = Set.Icc (x - δ) (x + δ) := by
  ext y; constructor
  · intro hy
    have hy' : |x - y| ≤ δ := by
      have : |y - x| ≤ δ := by
        simpa [closedBall, Real.dist_eq] using hy
      simpa [abs_sub_comm] using this
    obtain ⟨h₁, h₂⟩ := abs_sub_le_iff.mp hy'
    have hx : x - δ ≤ y := by linarith
    have hy'' : y ≤ x + δ := by linarith
    exact ⟨hx, hy''⟩
  · intro hy
    have hx : x - y ≤ δ := by linarith [hy.1]
    have hy_le : y - x ≤ δ := by linarith [hy.2]
    have h : |x - y| ≤ δ := abs_sub_le_iff.mpr ⟨hx, hy_le⟩
    have h' : |y - x| ≤ δ := by simpa [abs_sub_comm] using h
    simpa [closedBall, Real.dist_eq] using h'

end

lemma mem_unitInterval_ball_half_iff
    (y : { y : ℝ // y ∈ Set.Icc (0 : ℝ) 1 }) :
    y ∈ Metric.ball
        (x :=
            (⟨0, by
              constructor <;> norm_num⟩ :
            { y : ℝ // y ∈ Set.Icc (0 : ℝ) 1 }))
        (1 / 2 : ℝ) ↔
      (y : ℝ) < (1 / 2 : ℝ) := by
  change dist (y : ℝ) (0 : ℝ) < (1 / 2 : ℝ) ↔ (y : ℝ) < (1 / 2 : ℝ)
  have hy_nonneg : 0 ≤ (y : ℝ) := (y.property).1
  simp [abs_of_nonneg hy_nonneg]

/-- Example 7.2.3. In the subspace `[0, 1] ⊆ ℝ`, the open ball of radius
`1/2` around `0` consists of those points of `[0, 1]` whose underlying real
coordinate is `< 1/2`, so it differs from the ambient ball
`(-1/2, 1/2) ⊆ ℝ`. -/
lemma unitInterval_ball_half :
    Metric.ball
        (x :=
          (⟨0, by
            constructor <;> norm_num⟩ :
            { y : ℝ // y ∈ Set.Icc (0 : ℝ) 1 }))
        (1 / 2 : ℝ) =
      { y : { y : ℝ // y ∈ Set.Icc (0 : ℝ) 1 } |
        (y : ℝ) < (1 / 2 : ℝ) } := by
  ext y
  exact mem_unitInterval_ball_half_iff (y := y)

/-- Definition 7.2.4. In a metric space `(X, d)`, a subset `V ⊆ X` is open if
for every `x ∈ V` there exists `δ > 0` such that the ball `B(x, δ)` is contained
in `V`. A subset `E ⊆ X` is closed if its complement `X \ E` is open. If `x ∈ V`
and `V` is open, then `V` is an open (or simply a) neighborhood of `x`. -/
def IsOpenMetric {X : Type*} [PseudoMetricSpace X] (V : Set X) : Prop :=
  ∀ x ∈ V, ∃ δ > 0, Metric.ball x δ ⊆ V

/-- A set is closed in the metric sense if its complement is open. -/
def IsClosedMetric {X : Type*} [PseudoMetricSpace X] (E : Set X) : Prop :=
  IsOpenMetric (Eᶜ)

/-- The book's notion of an open set agrees with the topological notion coming
from the metric space structure. -/
theorem isOpenMetric_iff_isOpen {X : Type*} [PseudoMetricSpace X] (V : Set X) :
    IsOpenMetric V ↔ IsOpen V := by
  simpa [IsOpenMetric] using (Metric.isOpen_iff (s := V)).symm

/-- The book's notion of a closed set agrees with `IsClosed`. -/
theorem isClosedMetric_iff_isClosed {X : Type*} [PseudoMetricSpace X]
    (E : Set X) :
    IsClosedMetric E ↔ IsClosed E := by
  simpa [IsClosedMetric] using
    (isOpenMetric_iff_isOpen (V := Eᶜ)).trans (isOpen_compl_iff (s := E))

/-- An open set in the metric sense is a neighborhood of each of its points. -/
theorem isOpenMetric.mem_nhds {X : Type*} [PseudoMetricSpace X] {V : Set X}
    {x : X} (hV : IsOpenMetric V) (hx : x ∈ V) : V ∈ nhds x := by
  have hV' : IsOpen V := (isOpenMetric_iff_isOpen (V := V)).1 hV
  exact hV'.mem_nhds hx

/-- Example 7.2.5. Basic examples of open and closed subsets of `ℝ` and
singletons in metric spaces: `(0, ∞)` is open; `[0, ∞)` is closed; `[0, 1)` is
neither open nor closed; singletons are closed in any metric space, but need
not be open (e.g. `{0} ⊂ ℝ`), while in a one-point metric space `{x}` is open. -/
lemma real_Ioi_zero_isOpen : IsOpen (Set.Ioi (0 : ℝ)) := by
  simpa using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))

lemma real_Ici_zero_isClosed : IsClosed (Set.Ici (0 : ℝ)) := by
  simpa using (isClosed_Ici : IsClosed (Set.Ici (0 : ℝ)))

lemma real_Ico_zero_one_not_isOpen : ¬ IsOpen (Set.Ico (0 : ℝ) 1) := by
  intro h
  rcases (Metric.isOpen_iff.mp h) 0 (by simp) with ⟨ε, hεpos, hsub⟩
  have hmem : (-ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
    have hlt : |ε| / 2 < ε := by
      have hpos : 0 < ε := hεpos
      have hlt' : ε / 2 < ε := by linarith
      have hεabs : |ε| = ε := abs_of_pos hpos
      simpa [hεabs] using hlt'
    have htwo : (|(2 : ℝ)|) = 2 := by norm_num
    have hdist_lt : dist (-ε / 2) (0 : ℝ) < ε := by
      simpa [Real.dist_eq, abs_div, abs_neg, htwo] using hlt
    simpa [Metric.mem_ball] using hdist_lt
  have hcontra := hsub hmem
  have : (0 : ℝ) ≤ -ε / 2 := hcontra.1
  linarith

lemma real_Ico_zero_one_not_isClosed : ¬ IsClosed (Set.Ico (0 : ℝ) 1) := by
  intro h
  have hOpen : IsOpen ((Set.Ico (0 : ℝ) 1)ᶜ) := h.isOpen_compl
  rcases (Metric.isOpen_iff.mp hOpen) 1 (by simp) with ⟨ε, hεpos, hsub⟩
  -- choose a point slightly to the left of `1` inside `[0, 1)`
  set δ : ℝ := min (ε / 2) (1 / 2)
  have hδpos : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδle : δ ≤ ε / 2 := min_le_left _ _
  have hmem_ball : 1 - δ ∈ Metric.ball (1 : ℝ) ε := by
    have hdist : dist (1 - δ) (1 : ℝ) = |δ| := by
      have h : (1 - δ) - 1 = -δ := by ring
      simp
    have hδnonneg : 0 ≤ δ := le_of_lt hδpos
    have hlt : |δ| < ε := by
      have hlt' : δ < ε := by
        have : ε / 2 < ε := by linarith
        exact lt_of_le_of_lt hδle this
      simpa [abs_of_nonneg hδnonneg] using hlt'
    have hlt' : dist (1 - δ) (1 : ℝ) < ε := by simpa [hdist] using hlt
    simpa [Metric.mem_ball] using hlt'
  have hnot_compl : 1 - δ ∉ (Set.Ico (0 : ℝ) 1)ᶜ := by
    have hδle_half : δ ≤ (1 / 2 : ℝ) := min_le_right _ _
    have hnonneg : 0 ≤ 1 - δ := by linarith
    have hlt1 : 1 - δ < 1 := by linarith
    have hmem : 1 - δ ∈ Set.Ico (0 : ℝ) 1 := ⟨by linarith, hlt1⟩
    exact by simpa using hmem
  exact hnot_compl (hsub hmem_ball)

lemma singleton_isClosed {X : Type*} [PseudoMetricSpace X] [T1Space X] (x : X) :
    IsClosed ({x} : Set X) := by
  simp

lemma real_singleton_zero_not_isOpen : ¬ IsOpen ({0} : Set ℝ) := by
  intro h
  rcases (Metric.isOpen_iff.mp h) 0 (by simp) with ⟨ε, hεpos, hsub⟩
  have hmem : (ε / 2) ∈ Metric.ball (0 : ℝ) ε := by
    have hlt : |ε| / 2 < ε := by
      have hpos : 0 < ε := hεpos
      have hlt' : ε / 2 < ε := by linarith
      have hεabs : |ε| = ε := abs_of_pos hpos
      simpa [hεabs] using hlt'
    have htwo : (|(2 : ℝ)|) = 2 := by norm_num
    have hdist_lt : dist (ε / 2) (0 : ℝ) < ε := by
      simpa [Real.dist_eq, abs_div, htwo] using hlt
    simpa [Metric.mem_ball] using hdist_lt
  have hcontra : (ε / 2) = (0 : ℝ) := by
    have : (ε / 2) ∈ ({0} : Set ℝ) := hsub hmem
    simpa using this
  linarith

lemma singleton_isOpen_of_subsingleton {X : Type*} [PseudoMetricSpace X]
    [Subsingleton X] (x : X) :
    IsOpen ({x} : Set X) := by
  classical
  have hset : ({x} : Set X) = Set.univ := by
    ext y
    constructor
    · intro hy
      trivial
    · intro _
      have : y = x := Subsingleton.elim _ _
      simp [this]
  simp [hset]

/-- Proposition 7.2.6. In a metric space `(X, d)`: (i) `∅` and the whole space
`X` are open; (ii) a finite intersection of open sets is open; (iii) an
arbitrary union of open sets is open. -/
lemma open_sets_basic {X : Type*} [PseudoMetricSpace X] :
    (IsOpen (∅ : Set X) ∧ IsOpen (Set.univ : Set X)) ∧
      (∀ {ι : Type*} (s : Finset ι) (V : ι → Set X),
        (∀ i, IsOpen (V i)) → IsOpen (⋂ i ∈ s, V i)) ∧
      (∀ {ι : Sort*} (V : ι → Set X),
        (∀ i, IsOpen (V i)) → IsOpen (⋃ i, V i)) := by
  classical
  constructor
  · exact ⟨isOpen_empty, isOpen_univ⟩
  · constructor
    · intro ι s
      refine Finset.induction_on s ?base ?step
      · intro V _
        simp
      · intro a s ha ih V hV
        have hVa : IsOpen (V a) := hV a
        have hVs : IsOpen (⋂ i ∈ s, V i) := ih V hV
        have hrewrite :
            (⋂ i ∈ insert a s, V i) = V a ∩ ⋂ i ∈ s, V i := by
          simp [Finset.mem_insert]
        simpa [hrewrite] using hVa.inter hVs
    · intro ι V hV
      simpa using (isOpen_iUnion hV)

/-- Example 7.2.7. An infinite intersection of open sets need not be open:
`⋂ₙ (-1/(n+1), 1/(n+1)) = {0}`, so unlike finite intersections, arbitrary
intersections of opens may fail to be open. -/
lemma iInter_openIntervals_subset_singleton :
    (⋂ n : ℕ, Set.Ioo (-(1 / (n.succ : ℝ))) (1 / (n.succ : ℝ))) ⊆
      ({0} : Set ℝ) := by
  intro x hx
  have hxabs : ∀ n : ℕ, |x| < 1 / (n.succ : ℝ) := by
    intro n
    have hxmem :
        x ∈ Set.Ioo (-(1 / (n.succ : ℝ))) (1 / (n.succ : ℝ)) :=
      Set.mem_iInter.mp hx n
    exact abs_lt.mpr hxmem
  have hx0 : x = 0 := by
    classical
    by_contra hx0
    have hpos_abs : 0 < |x| := abs_pos.mpr hx0
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / |x|)
    have hn' : (1 / |x|) < (n.succ : ℝ) := by
      have hlt : (n : ℝ) < n.succ := by exact_mod_cast Nat.lt_succ_self n
      exact lt_trans hn hlt
    have hcontr : (1 / (n.succ : ℝ)) < |x| := by
      have hpos_inv : 0 < 1 / |x| := one_div_pos.mpr hpos_abs
      have h := one_div_lt_one_div_of_lt hpos_inv hn'
      simpa [one_div_one_div] using h
    have hxabsn := hxabs n
    exact (lt_asymm hcontr hxabsn).elim
  simp [Set.mem_singleton_iff, hx0]

lemma iInter_openIntervals_eq_singleton :
    (⋂ n : ℕ, Set.Ioo (-(1 / (n.succ : ℝ))) (1 / (n.succ : ℝ))) =
      ({0} : Set ℝ) := by
  refine Set.Subset.antisymm iInter_openIntervals_subset_singleton ?_
  intro x hx
  have hx0 : x = 0 := by simpa [Set.mem_singleton_iff] using hx
  subst hx0
  refine Set.mem_iInter.mpr ?_
  intro n
  have hpos : (0 : ℝ) < 1 / (n.succ : ℝ) := by
    have hposnat : 0 < (n.succ : ℝ) := by exact_mod_cast Nat.succ_pos n
    exact one_div_pos.mpr hposnat
  have hneg : -(1 / (n.succ : ℝ)) < (0 : ℝ) := by linarith
  exact ⟨hneg, hpos⟩

lemma not_isOpen_iInter_openIntervals :
    ¬ IsOpen (⋂ n : ℕ, Set.Ioo (-(1 / (n.succ : ℝ))) (1 / (n.succ : ℝ))) := by
  intro h
  have h' := h
  rw [iInter_openIntervals_eq_singleton] at h'
  exact real_singleton_zero_not_isOpen h'

/-- Proposition 7.2.8. In a metric space `(X, d)`: (i) `∅` and `X` are closed;
an arbitrary intersection of closed sets is closed; a finite union of closed
sets is closed. -/
lemma closed_sets_basic {X : Type*} [PseudoMetricSpace X] :
    (IsClosed (∅ : Set X) ∧ IsClosed (Set.univ : Set X)) ∧
      (∀ {ι : Sort*} (E : ι → Set X),
        (∀ i, IsClosed (E i)) → IsClosed (⋂ i, E i)) ∧
      (∀ {ι : Type*} (s : Finset ι) (E : ι → Set X),
        (∀ i, IsClosed (E i)) → IsClosed (⋃ i ∈ s, E i)) := by
  classical
  constructor
  · exact ⟨isClosed_empty, isClosed_univ⟩
  · constructor
    · intro ι E hE
      simpa using (isClosed_iInter hE)
    · intro ι s
      refine Finset.induction_on s ?base ?step
      · intro E _
        simp
      · intro a s ha ih E hE
        have hEa : IsClosed (E a) := hE a
        have hEs : IsClosed (⋃ i ∈ s, E i) := ih E hE
        have hrewrite :
            (⋃ i ∈ insert a s, E i) = E a ∪ ⋃ i ∈ s, E i := by
          ext x
          simp [Finset.mem_insert]
        simpa [hrewrite] using hEa.union hEs

/-- Proposition 7.2.9. In a metric space `(X, d)`, for any center `x` and
radius `δ > 0`, the open ball `B(x, δ)` is open and the closed ball `C(x, δ)`
is closed. -/
lemma openBall_isOpen_closedBall_isClosed {X : Type*} [PseudoMetricSpace X]
    (x : X) {δ : ℝ} (_hδ : 0 < δ) :
    IsOpen (openBall x δ) ∧ IsClosed (closedBall x δ) := by
  constructor
  · simp [openBall_eq_metric_ball (x := x) (δ := δ), Metric.isOpen_ball]
  · simp [closedBall_eq_metric_closedBall (x := x) (δ := δ), Metric.isClosed_closedBall]

/-- Proposition 7.2.10. If `a < b` in `ℝ`, then the intervals `(a, b)`, `(a, ∞)`
and `(-∞, b)` are open in `ℝ`, while `[a, b]`, `[a, ∞)` and `(-∞, b]` are closed
in `ℝ`. -/
lemma real_intervals_open_closed {a b : ℝ} (_h : a < b) :
    IsOpen (Set.Ioo a b) ∧ IsOpen (Set.Ioi a) ∧ IsOpen (Set.Iio b) ∧
      IsClosed (Set.Icc a b) ∧ IsClosed (Set.Ici a) ∧ IsClosed (Set.Iic b) := by
  constructor
  · simpa using (isOpen_Ioo : IsOpen (Set.Ioo a b))
  · constructor
    · simpa using (isOpen_Ioi : IsOpen (Set.Ioi a))
    · constructor
      · simpa using (isOpen_Iio : IsOpen (Set.Iio b))
      · constructor
        · simpa using (isClosed_Icc : IsClosed (Set.Icc a b))
        · constructor
          · simpa using (isClosed_Ici : IsClosed (Set.Ici a))
          · simpa using (isClosed_Iic : IsClosed (Set.Iic b))

lemma preimage_eq_iff_inter_image_subtype {X : Type*} {Y : Set X} (U : Set Y)
    (V : Set X) :
    Subtype.val ⁻¹' V = U ↔ V ∩ Y = Subtype.val '' U := by
  constructor
  · intro hpre
    ext x; constructor
    · intro hx
      rcases hx with ⟨hxV, hxY⟩
      refine ⟨⟨x, hxY⟩, ?_, rfl⟩
      have hxpre : ⟨x, hxY⟩ ∈ Subtype.val ⁻¹' V := by
        simpa using hxV
      simpa [hpre] using hxpre
    · intro hx
      rcases hx with ⟨y, hy, rfl⟩
      have hy' : y ∈ Subtype.val ⁻¹' V := by simpa [hpre] using hy
      have hyV : y.val ∈ V := by simpa using hy'
      exact ⟨hyV, y.property⟩
  · intro hInter
    ext y; constructor
    · intro hy
      have hy' : y.val ∈ V ∩ Y := ⟨hy, y.property⟩
      have hy'' : y.val ∈ Subtype.val '' U := by simpa [hInter] using hy'
      rcases hy'' with ⟨u, hu, hval⟩
      have : u = y := Subtype.ext hval
      simpa [this] using hu
    · intro hy
      have hy' : y.val ∈ Subtype.val '' U := ⟨y, hy, rfl⟩
      have hy'' : y.val ∈ V ∩ Y := by simpa [hInter] using hy'
      exact hy''.1

lemma subspace_open_exists_open_superset {X : Type*} [PseudoMetricSpace X]
    {Y : Set X} {U : Set Y} :
    IsOpen U → ∃ V : Set X, IsOpen V ∧ V ∩ Y = Subtype.val '' U := by
  intro hU
  rcases
      (isOpen_induced_iff :
        IsOpen U ↔ ∃ V : Set X, IsOpen V ∧ Subtype.val ⁻¹' V = U).mp hU with
    ⟨V, hV, hpre⟩
  exact ⟨V, hV,
    (preimage_eq_iff_inter_image_subtype (U := U) (V := V)).1 hpre⟩

lemma exists_open_superset_subspace_open {X : Type*} [PseudoMetricSpace X]
    {Y : Set X} {U : Set Y} :
    (∃ V : Set X, IsOpen V ∧ V ∩ Y = Subtype.val '' U) → IsOpen U := by
  rintro ⟨V, hV, hVU⟩
  have hpre :
      Subtype.val ⁻¹' V = U :=
    (preimage_eq_iff_inter_image_subtype (U := U) (V := V)).2 hVU
  exact
    (isOpen_induced_iff :
        IsOpen U ↔ ∃ V : Set X, IsOpen V ∧ Subtype.val ⁻¹' V = U).mpr
      ⟨V, hV, hpre⟩

lemma image_preimage_subtype_eq {X : Type*} {V U : Set X} (hUV : U ⊆ V) :
    Subtype.val '' (Subtype.val ⁻¹' U : Set V) = U := by
  ext x; constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hxU
    exact ⟨⟨x, hUV hxU⟩, hxU, rfl⟩

/-- Proposition 7.2.11. For a metric space `(X, d)` and subset `Y ⊆ X`, a subset
`U ⊆ Y` is open in the subspace topology if and only if there exists an open
`V ⊆ X` with `V ∩ Y = U`. -/
lemma subspace_open_iff {X : Type*} [PseudoMetricSpace X] {Y : Set X} (U : Set Y) :
    IsOpen U ↔ ∃ V : Set X, IsOpen V ∧ V ∩ Y = Subtype.val '' U := by
  constructor
  · exact subspace_open_exists_open_superset (U := U)
  · exact exists_open_superset_subspace_open (U := U)

/-- Proposition 7.2.12. In a metric space `(X, d)`, if `V ⊆ X` is open and
`E ⊆ X` is closed, then:
(i) a subset `U ⊆ V` is open in the subspace topology on `V` iff `U` is open in
`X`;
(ii) a subset `F ⊆ E` is closed in the subspace topology on `E` iff `F` is
closed in `X`. -/
lemma open_in_open_subspace_iff {X : Type*} [PseudoMetricSpace X] {V U : Set X}
    (hV : IsOpen V) (hUV : U ⊆ V) :
    IsOpen (Subtype.val ⁻¹' U : Set V) ↔ IsOpen U := by
  constructor
  · intro hUsub
    rcases
        (subspace_open_iff
            (U := (Subtype.val ⁻¹' U : Set V))).1
          hUsub with
      ⟨W, hWopen, hW⟩
    have himage :
        Subtype.val '' (Subtype.val ⁻¹' U : Set V) = U :=
      image_preimage_subtype_eq (V := V) (U := U) hUV
    have hW' : W ∩ V = U := by simpa [himage] using hW
    have hopen : IsOpen (W ∩ V) := hWopen.inter hV
    simpa [hW'] using hopen
  · intro hUopen
    refine
      (subspace_open_iff
          (U := (Subtype.val ⁻¹' U : Set V))).2
        ?_
    have hUV' : U ∩ V = U := Set.inter_eq_left.mpr hUV
    have himage :
        Subtype.val '' (Subtype.val ⁻¹' U : Set V) = U :=
      image_preimage_subtype_eq (V := V) (U := U) hUV
    refine ⟨U, hUopen, ?_⟩
    simp [hUV', himage]

lemma closed_in_closed_subspace_iff {X : Type*} [PseudoMetricSpace X]
    {E F : Set X} (hE : IsClosed E) (hFE : F ⊆ E) :
    IsClosed (Subtype.val ⁻¹' F : Set E) ↔ IsClosed F := by
  constructor
  · intro hFsub
    rcases
        (isClosed_induced_iff :
            IsClosed (Subtype.val ⁻¹' F : Set E) ↔
              ∃ C : Set X, IsClosed C ∧
                Subtype.val ⁻¹' C =
                  (Subtype.val ⁻¹' F : Set E)).mp hFsub with
      ⟨C, hCclosed, hpre⟩
    have hCE :
        C ∩ E = Subtype.val '' (Subtype.val ⁻¹' F : Set E) :=
      (preimage_eq_iff_inter_image_subtype
          (U := (Subtype.val ⁻¹' F : Set E)) (V := C)).1 hpre
    have hCE' : C ∩ E = F := by
      have himage :
          Subtype.val '' (Subtype.val ⁻¹' F : Set E) = F :=
        image_preimage_subtype_eq (V := E) (U := F) hFE
      simpa [himage] using hCE
    have hclosed_inter : IsClosed (C ∩ E) := hCclosed.inter hE
    simpa [hCE'] using hclosed_inter
  · intro hF
    refine
      (isClosed_induced_iff :
          IsClosed (Subtype.val ⁻¹' F : Set E) ↔
            ∃ C : Set X, IsClosed C ∧
              Subtype.val ⁻¹' C =
                (Subtype.val ⁻¹' F : Set E)).mpr ?_
    exact ⟨F, hF, rfl⟩

/-- Definition 7.2.13. A nonempty metric space `(X, d)` is connected if the only
clopen subsets are `∅` and the whole space. A nonempty space that is not
connected is called disconnected. A nonempty subset `A ⊆ X` is connected when it
is connected with the subspace topology. -/
def IsConnectedMetricSpace (X : Type*) [PseudoMetricSpace X] : Prop :=
  Nonempty X ∧
    ∀ V : Set X, IsOpen V → IsClosed V → V = (∅ : Set X) ∨ V = Set.univ

/-- The book's notion of a connected metric space agrees with
`ConnectedSpace`. -/
theorem isConnectedMetricSpace_iff_connectedSpace (X : Type*)
    [PseudoMetricSpace X] :
    IsConnectedMetricSpace X ↔ ConnectedSpace X := by
  constructor
  · intro h
    rcases h with ⟨hne, hclopen⟩
    refine (connectedSpace_iff_clopen).2 ?_
    refine ⟨hne, ?_⟩
    intro s hs
    exact hclopen s hs.2 hs.1
  · intro h
    rcases (connectedSpace_iff_clopen).1 h with ⟨hne, hclopen⟩
    refine ⟨hne, ?_⟩
    intro s hsopen hsclosed
    exact hclopen s ⟨hsclosed, hsopen⟩

/-- A subset is connected in the book's sense when it is connected with the
subspace topology. -/
def IsConnectedSubset {X : Type*} [PseudoMetricSpace X] (A : Set X) : Prop :=
  IsConnected A

/-- Proposition 7.2.14. A nonempty subset `S` of a metric space is disconnected
iff there are open sets `U₁` and `U₂` in the ambient space such that
`U₁ ∩ U₂ ∩ S = ∅`, both intersections `U₁ ∩ S` and `U₂ ∩ S` are nonempty, and
`S = (U₁ ∩ S) ∪ (U₂ ∩ S)`. -/
lemma disconnected_iff_exists_open_separation {X : Type*} [PseudoMetricSpace X]
    {S : Set X} (hS : S.Nonempty) :
    ¬ IsConnectedSubset S ↔
      ∃ U₁ U₂ : Set X,
        IsOpen U₁ ∧ IsOpen U₂ ∧
          U₁ ∩ U₂ ∩ S = (∅ : Set X) ∧
          (U₁ ∩ S).Nonempty ∧ (U₂ ∩ S).Nonempty ∧
          S = (U₁ ∩ S) ∪ (U₂ ∩ S) := by
  classical
  have hconn : ¬ IsConnectedSubset S ↔ ¬ IsPreconnected S := by
    constructor
    · intro h
      exact fun hpre => h ⟨hS, hpre⟩
    · intro hpre
      exact fun hconn => hpre hconn.2
  constructor
  · intro hdisc
    have hpre : ¬ IsPreconnected S := hconn.mp hdisc
    have hpre' :
        ∃ U₁ U₂ : Set X,
          IsOpen U₁ ∧ IsOpen U₂ ∧ S ⊆ U₁ ∪ U₂ ∧
            (S ∩ U₁).Nonempty ∧ (S ∩ U₂).Nonempty ∧
            S ∩ (U₁ ∩ U₂) = (∅ : Set X) := by
      classical
      have hpre'' :
          ¬ ∀ U₁ U₂ : Set X,
            IsOpen U₁ → IsOpen U₂ → S ⊆ U₁ ∪ U₂ →
              (S ∩ U₁).Nonempty → (S ∩ U₂).Nonempty →
              (S ∩ (U₁ ∩ U₂)).Nonempty := by
        simpa [IsPreconnected] using hpre
      push_neg at hpre''
      exact hpre''
    rcases hpre' with
      ⟨U₁, U₂, hU₁open, hU₂open, hcover, hU₁ne, hU₂ne, hdisj⟩
    have hdisj' : U₁ ∩ U₂ ∩ S = (∅ : Set X) := by
      simpa [Set.inter_assoc, Set.inter_comm] using hdisj
    refine ⟨U₁, U₂, hU₁open, hU₂open, hdisj', ?_, ?_, ?_⟩
    · simpa [Set.inter_comm] using hU₁ne
    · simpa [Set.inter_comm] using hU₂ne
    · apply subset_antisymm
      · intro x hx
        have hx' : x ∈ U₁ ∪ U₂ := hcover hx
        rcases hx' with hxU₁ | hxU₂
        · exact Or.inl ⟨hxU₁, hx⟩
        · exact Or.inr ⟨hxU₂, hx⟩
      · intro x hx
        rcases hx with hx | hx
        · exact hx.2
        · exact hx.2
  · intro h
    rcases h with ⟨U₁, U₂, hU₁open, hU₂open, hdisj, hU₁ne, hU₂ne, hcoverEq⟩
    have hcover : S ⊆ U₁ ∪ U₂ := by
      intro x hx
      have hx' : x ∈ (U₁ ∩ S) ∪ (U₂ ∩ S) := hcoverEq ▸ hx
      rcases hx' with hx' | hx'
      · exact Or.inl hx'.1
      · exact Or.inr hx'.1
    have hpre : ¬ IsPreconnected S := by
      intro hpre
      have hinter : (U₁ ∩ U₂ ∩ S).Nonempty := by
        have h := hpre U₁ U₂ hU₁open hU₂open hcover
            (by simpa [Set.inter_comm] using hU₁ne)
            (by simpa [Set.inter_comm] using hU₂ne)
        simpa [Set.inter_assoc, Set.inter_comm] using h
      cases hdisj ▸ hinter with
      | intro x hx => cases hx
    exact hconn.mpr hpre

/-- A set missing `z` is contained in the union of `(-∞, z)` and `(z, ∞)`. -/
lemma subset_union_Iio_Ioi_of_not_mem {S : Set ℝ} {z : ℝ} (hz : z ∉ S) :
    S ⊆ Set.Iio z ∪ Set.Ioi z := by
  intro s hs
  have hsz : s ≠ z := by
    intro h
    exact hz (h ▸ hs)
  rcases lt_or_gt_of_ne hsz with hlt | hgt
  · exact Or.inl hlt
  · exact Or.inr hgt

/-- Example 7.2.15. If a set `S ⊆ ℝ` contains points `x` and `y` with `x < z < y`
for some `z ∉ S`, then `S` is disconnected, for instance by the separation
`(-∞, z)` and `(z, ∞)`. -/
lemma real_set_disconnected_of_gap {S : Set ℝ} {x y z : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hxz : x < z) (hzy : z < y) (hz : z ∉ S) :
    ¬ IsConnectedSubset (S : Set ℝ) := by
  classical
  have hS : S.Nonempty := ⟨x, hx⟩
  refine
    (disconnected_iff_exists_open_separation (S := S) hS).2 ?_
  refine ⟨Set.Iio z, Set.Ioi z, isOpen_Iio, isOpen_Ioi, ?_, ?_, ?_, ?_⟩
  · have hIioIoi : Set.Iio z ∩ Set.Ioi z = (∅ : Set ℝ) := by
      ext u; constructor
      · intro h
        rcases h with ⟨h₁, h₂⟩
        have h₁' : u < z := h₁
        have h₂' : z < u := h₂
        exact (lt_asymm h₁' h₂')
      · intro h
        cases h
    simp [hIioIoi]
  · exact ⟨x, ⟨hxz, hx⟩⟩
  · exact ⟨y, ⟨hzy, hy⟩⟩
  · apply subset_antisymm
    · intro s hs
      have hmem :
          s ∈ Set.Iio z ∪ Set.Ioi z :=
        subset_union_Iio_Ioi_of_not_mem (S := S) (z := z) hz hs
      rcases hmem with hlt | hgt
      · exact Or.inl ⟨hlt, hs⟩
      · exact Or.inr ⟨hgt, hs⟩
    · intro s hs
      rcases hs with hs | hs
      · exact hs.2
      · exact hs.2

/-- Proposition 7.2.16. A nonempty subset of `ℝ` is connected if and only if it
is an interval or a single point. -/
lemma real_connected_iff_interval_or_singleton {S : Set ℝ} (hS : S.Nonempty) :
    IsConnected S ↔ Set.OrdConnected S ∨ ∃ x : ℝ, S = ({x} : Set ℝ) := by
  constructor
  · intro h
    have hpre : IsPreconnected S := h.isPreconnected
    have hOC : Set.OrdConnected S := (isPreconnected_iff_ordConnected).1 hpre
    exact Or.inl hOC
  · intro h
    rcases h with hOC | ⟨x, rfl⟩
    · have hpre : IsPreconnected S := (isPreconnected_iff_ordConnected).2 hOC
      exact ⟨hS, hpre⟩
    · simpa using (isConnected_singleton (x := x))

section

noncomputable local instance discretePseudoMetricSpaceBool :
    PseudoMetricSpace Bool :=
  PseudoMetricSpace.induced (fun b : Bool => if b then (1 : ℝ) else 0) inferInstance

noncomputable local instance : UniformSpace Bool :=
  (inferInstance : PseudoMetricSpace Bool).toUniformSpace

noncomputable local instance : TopologicalSpace Bool :=
  (inferInstance : UniformSpace Bool).toTopologicalSpace

/-- Example 7.2.17. In a two point space with the discrete metric, the ball of
radius `2` around one point is the whole space, which splits into two disjoint
open singletons and is therefore not connected. -/
lemma discrete_two_point_ball_not_connected :
    Metric.ball (x := true) (2 : ℝ) = (Set.univ : Set Bool) ∧
      ¬ IsConnected (Set.univ : Set Bool) := by
  classical
  have hdist_false_true : dist false true = 1 := by
    change dist (0 : ℝ) 1 = 1
    norm_num
  have hdist_true_false : dist true false = 1 := by
    simpa [dist_comm] using hdist_false_true
  have hball2 :
      Metric.ball (x := true) (2 : ℝ) = (Set.univ : Set Bool) := by
    ext b
    cases b with
    | false =>
        simp [Metric.ball, hdist_false_true]
    | true =>
        simp [Metric.ball]
  let U₁ : Set Bool := Metric.ball (x := true) (1 / 2 : ℝ)
  let U₂ : Set Bool := Metric.ball (x := false) (1 / 2 : ℝ)
  have hopen_true : IsOpen U₁ :=
    (Metric.isOpen_ball : IsOpen (Metric.ball (x := true) (1 / 2 : ℝ)))
  have hopen_false : IsOpen U₂ :=
    (Metric.isOpen_ball : IsOpen (Metric.ball (x := false) (1 / 2 : ℝ)))
  have hnonempty : (Set.univ : Set Bool).Nonempty := Set.univ_nonempty
  have hdisc :
      ¬ IsConnected (Set.univ : Set Bool) := by
    have hsep :
        ∃ U₁ U₂ : Set Bool,
          IsOpen U₁ ∧ IsOpen U₂ ∧
            U₁ ∩ U₂ ∩ (Set.univ : Set Bool) = (∅ : Set Bool) ∧
            (U₁ ∩ (Set.univ : Set Bool)).Nonempty ∧
            (U₂ ∩ (Set.univ : Set Bool)).Nonempty ∧
            (Set.univ : Set Bool) =
              (U₁ ∩ (Set.univ : Set Bool)) ∪
                (U₂ ∩ (Set.univ : Set Bool)) := by
      refine ⟨U₁, U₂, hopen_true, hopen_false, ?_, ?_, ?_, ?_⟩
      · ext b
        cases b with
        | false =>
            simp [U₁, U₂, Metric.ball, hdist_false_true] ; norm_num
        | true =>
            simp [U₁, U₂, Metric.ball, hdist_true_false] ; norm_num
      · refine ⟨true, ?_⟩
        simp [U₁, Metric.ball]
      · refine ⟨false, ?_⟩
        simp [U₂, Metric.ball]
      · ext b
        cases b with
        | false =>
            simp [U₁, U₂, Metric.ball, hdist_false_true]
        | true =>
            simp [U₁, U₂, Metric.ball, hdist_true_false]
    have hres :=
      (disconnected_iff_exists_open_separation
          (S := (Set.univ : Set Bool)) hnonempty).2 hsep
    simpa [IsConnectedSubset] using hres
  exact ⟨hball2, hdisc⟩

end

/-- Definition 7.2.18. In a metric space `(X, d)` and for `A ⊆ X`, the closure
`Ā` is the intersection of all closed sets containing `A`. -/
def closureByClosed {X : Type*} [PseudoMetricSpace X] (A : Set X) : Set X :=
  ⋂₀ {E : Set X | IsClosed E ∧ A ⊆ E}

/-- The closure defined as the intersection of closed supersets agrees with the
topological closure. -/
theorem closureByClosed_eq_closure {X : Type*} [PseudoMetricSpace X]
    (A : Set X) : closureByClosed A = closure A := by
  rfl

/-- Proposition 7.2.19. For a subset `A` of a metric space, the closure
`Ā` is closed and contains `A`, and if `A` is already closed then `Ā = A`. -/
lemma closure_properties {X : Type*} [PseudoMetricSpace X] (A : Set X) :
    IsClosed (closure A) ∧ A ⊆ closure A ∧ (IsClosed A → closure A = A) := by
  refine ⟨isClosed_closure, subset_closure, ?_⟩
  intro hA
  exact hA.closure_eq

/-- Example 7.2.20. The closure of `(0, 1)` in `ℝ` is `[0, 1]`. -/
lemma closure_openInterval_zero_one :
    closure (Set.Ioo (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 := by
  simp [closure_Ioo (a := (0 : ℝ)) (b := 1)]

lemma image_subtype_lt_one_eq_Ioo :
    Subtype.val '' {x : Set.Ioi (0 : ℝ) | (x : ℝ) < 1} = Set.Ioo (0 : ℝ) 1 := by
  ext x; constructor
  · intro hx
    rcases hx with ⟨y, hylt, rfl⟩
    exact ⟨y.property, hylt⟩
  · intro hx
    rcases hx with ⟨hx0, hx1⟩
    refine ⟨⟨x, hx0⟩, ?_, rfl⟩
    exact hx1

lemma closure_subtype_rewrite (x : Set.Ioi (0 : ℝ)) :
    x ∈ closure ({x : Set.Ioi (0 : ℝ) | (x : ℝ) < 1}) ↔
      (x : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
  have h :=
    (Topology.IsInducing.subtypeVal :
      Topology.IsInducing (Subtype.val : Set.Ioi (0 : ℝ) → ℝ)).closure_eq_preimage_closure_image
        ({x : Set.Ioi (0 : ℝ) | (x : ℝ) < 1})
  simp [h, image_subtype_lt_one_eq_Ioo]

lemma mem_target_set_iff_le_one (x : Set.Ioi (0 : ℝ)) :
    (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 ↔ (x : ℝ) ≤ 1 := by
  constructor
  · intro hx
    exact hx.2
  · intro hx
    exact ⟨le_of_lt x.property, hx⟩

/-- Example 7.2.21. In the ambient metric space `(0, ∞)`, the closure of
`(0, 1)` is `(0, 1]`, since `0` is not available as a limit point but `1`
remains a boundary point. -/
lemma closure_Ioo_in_Ioi_eq_Ioc :
    closure ({x : Set.Ioi (0 : ℝ) | (x : ℝ) < 1}) =
      {x : Set.Ioi (0 : ℝ) | (x : ℝ) ≤ 1} := by
  ext x
  constructor
  · intro hx
    have hx' : (x : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) :=
      (closure_subtype_rewrite x).1 hx
    have hx'' : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [closure_openInterval_zero_one] using hx'
    exact hx''.2
  · intro hxle
    have hx' : (x : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      (mem_target_set_iff_le_one x).2 hxle
    have hx'' : (x : ℝ) ∈ closure (Set.Ioo (0 : ℝ) 1) := by
      simpa [closure_openInterval_zero_one] using hx'
    exact (closure_subtype_rewrite x).2 hx''

/-- Proposition 7.2.22. In a metric space `(X, d)` and subset `A ⊆ X`, a point
`x` lies in the closure `Ā` if and only if every open ball around `x` meets
`A`, that is, `B(x, δ) ∩ A ≠ ∅` for all `δ > 0`. -/
lemma mem_closure_iff_ball_intersects {X : Type*} [PseudoMetricSpace X]
    {A : Set X} {x : X} :
    x ∈ closure A ↔
      ∀ δ > 0, (Metric.ball x δ ∩ A).Nonempty := by
  constructor
  · intro hx δ hδ
    rcases (Metric.mem_closure_iff.mp hx) δ hδ with ⟨y, hyA, hyδ⟩
    refine ⟨y, ?_, hyA⟩
    have : dist y x < δ := by simpa [dist_comm] using hyδ
    simpa [Metric.ball] using this
  · intro h
    refine (Metric.mem_closure_iff : x ∈ closure A ↔ _).2 ?_
    intro δ hδ
    rcases h δ hδ with ⟨y, hyBall, hyA⟩
    have : dist x y < δ := by
      have : dist y x < δ := by simpa [Metric.ball] using hyBall
      simpa [dist_comm] using this
    exact ⟨y, hyA, this⟩

/-- Definition 7.2.23. In a metric space `(X, d)` and a subset `A ⊆ X`, the
interior of `A` is the set of points `x ∈ A` for which there exists `δ > 0`
with `B(x, δ) ⊆ A`. The boundary of `A` is `∂A = \overline{A} \setminus Aᵒ`. -/
def metricInterior {X : Type*} [PseudoMetricSpace X] (A : Set X) : Set X :=
  {x | x ∈ A ∧ ∃ δ > 0, Metric.ball x δ ⊆ A}

/-- The metric description of the interior agrees with the topological interior
coming from the metric space structure. -/
theorem metricInterior_eq_interior {X : Type*} [PseudoMetricSpace X]
    (A : Set X) : metricInterior A = interior A := by
  ext x; constructor
  · intro hx
    rcases hx with ⟨hxA, δ, hδ, hball⟩
    refine (mem_interior).2 ?_
    refine ⟨Metric.ball x δ, hball, Metric.isOpen_ball, ?_⟩
    exact Metric.mem_ball_self hδ
  · intro hx
    rcases (mem_interior).1 hx with ⟨t, htA, htopen, hxt⟩
    rcases (Metric.isOpen_iff).1 htopen x hxt with ⟨δ, hδ, hball⟩
    refine ⟨htA hxt, δ, hδ, ?_⟩
    intro y hy
    exact htA (hball hy)

/-- The boundary of a subset is its closure minus its interior. -/
def metricBoundary {X : Type*} [PseudoMetricSpace X] (A : Set X) : Set X :=
  closure A \ metricInterior A

/-- The boundary defined via closure and interior agrees with the topological
frontier. -/
theorem metricBoundary_eq_frontier {X : Type*} [PseudoMetricSpace X]
    (A : Set X) : metricBoundary A = frontier A := by
  calc
    metricBoundary A = closure A \ metricInterior A := rfl
    _ = closure A \ interior A := by
      rw [metricInterior_eq_interior]
    _ = frontier A := rfl

/-- Example 7.2.24. For `A = (0, 1] ⊆ ℝ`, the closure is `[0, 1]`, the interior
is `(0, 1)`, and the boundary is `{0, 1}`. -/
lemma closure_interior_boundary_Ioc_zero_one :
    closure (Set.Ioc (0 : ℝ) 1) = Set.Icc (0 : ℝ) 1 ∧
      interior (Set.Ioc (0 : ℝ) 1) = Set.Ioo (0 : ℝ) 1 ∧
      frontier (Set.Ioc (0 : ℝ) 1) = ({0, 1} : Set ℝ) := by
  constructor
  · have h : (0 : ℝ) ≠ 1 := zero_ne_one
    simp [closure_Ioc (a := (0 : ℝ)) (b := (1 : ℝ)) h]
  · constructor
    · simp [interior_Ioc (a := (0 : ℝ)) (b := (1 : ℝ))]
    · have h : (0 : ℝ) < 1 := zero_lt_one
      simp [frontier_Ioc (a := (0 : ℝ)) (b := (1 : ℝ)) h]

/-- Example 7.2.25. For the discrete metric on the two-point set
`X = {a, b}` and `A = {a}`, we have `Ā = Aᵒ = A` and `∂A = ∅`. -/
lemma closure_interior_boundary_discrete_pair :
    closure ({true} : Set Bool) = ({true} : Set Bool) ∧
      interior ({true} : Set Bool) = ({true} : Set Bool) ∧
      frontier ({true} : Set Bool) = (∅ : Set Bool) := by
  classical
  have hclosed_true : IsClosed ({true} : Set Bool) := by
    simp
  have hclosed_false : IsClosed ({false} : Set Bool) := by
    simp
  have hopen_true : IsOpen ({true} : Set Bool) := by
    have hcompl : ({false} : Set Bool)ᶜ = ({true} : Set Bool) := by
      ext b
      cases b
      · simp
      · simp
    exact hcompl ▸ hclosed_false.isOpen_compl
  have hclosure : closure ({true} : Set Bool) = ({true} : Set Bool) :=
    hclosed_true.closure_eq
  have hinterior : interior ({true} : Set Bool) = ({true} : Set Bool) :=
    hopen_true.interior_eq
  refine ⟨hclosure, ?_⟩
  refine ⟨hinterior, ?_⟩
  calc
    frontier ({true} : Set Bool)
        = closure ({true} : Set Bool) \ interior ({true} : Set Bool) := rfl
    _ = closure ({true} : Set Bool) \ ({true} : Set Bool) := by
      simp [hinterior]
    _ = ({true} : Set Bool) \ ({true} : Set Bool) := by
      simp
    _ = (∅ : Set Bool) := by simp

/-- Proposition 7.2.26. In a metric space, the interior of any subset is open
and the boundary is closed. -/
lemma interior_open_boundary_closed {X : Type*} [PseudoMetricSpace X]
    (A : Set X) : IsOpen (interior A) ∧ IsClosed (frontier A) := by
  constructor
  · exact isOpen_interior
  · exact isClosed_frontier

lemma not_mem_interior_iff_ball_meets_compl {X : Type*} [PseudoMetricSpace X]
    {A : Set X} {x : X} :
    x ∉ interior A ↔ ∀ δ > 0, (Metric.ball x δ ∩ Aᶜ).Nonempty := by
  classical
  constructor
  · intro hx δ hδ
    by_contra hEmpty
    have hsubset : Metric.ball x δ ⊆ A := by
      intro y hy
      by_contra hyA
      exact hEmpty ⟨y, hy, hyA⟩
    have hx_ball : x ∈ Metric.ball x δ := by
      have : dist x x < δ := by simpa using hδ
      simpa [Metric.ball] using this
    have hball_open : IsOpen (Metric.ball x δ) := Metric.isOpen_ball
    have hball_interior : Metric.ball x δ ⊆ interior A :=
      interior_maximal hsubset hball_open
    exact hx (hball_interior hx_ball)
  · intro h hxint
    rcases (Metric.isOpen_iff.mp isOpen_interior) x hxint with
      ⟨δ, hδ, hsubset⟩
    have hsubsetA : Metric.ball x δ ⊆ A :=
      Set.Subset.trans hsubset interior_subset
    rcases h δ hδ with ⟨y, hyBall, hyCompl⟩
    exact hyCompl (hsubsetA hyBall)

/-- Proposition 7.2.26. For a subset `A` of a metric space, the interior `Aᵒ`
is open and the boundary `∂A` is closed. -/
lemma metricInterior_open_metricBoundary_closed {X : Type*}
    [PseudoMetricSpace X] (A : Set X) :
    IsOpen (metricInterior A) ∧ IsClosed (metricBoundary A) := by
  constructor
  · rw [metricInterior_eq_interior]
    exact (interior_open_boundary_closed (X := X) (A := A)).1
  · rw [metricBoundary_eq_frontier]
    exact (interior_open_boundary_closed (X := X) (A := A)).2

/-- Proposition 7.2.27. A point `x` lies in the boundary `∂A` of a subset `A`
of a metric space if and only if every open ball around `x` meets both `A` and
its complement. -/
lemma mem_frontier_iff_ball_intersects {X : Type*} [PseudoMetricSpace X]
    {A : Set X} {x : X} :
    x ∈ frontier A ↔
      ∀ δ > 0,
        (Metric.ball x δ ∩ A).Nonempty ∧ (Metric.ball x δ ∩ Aᶜ).Nonempty := by
  classical
  constructor
  · intro hx
    change x ∈ closure A \ interior A at hx
    rcases hx with ⟨hxClosure, hxNotInterior⟩
    intro δ hδ
    constructor
    · exact (mem_closure_iff_ball_intersects).1 hxClosure δ hδ
    · exact (not_mem_interior_iff_ball_meets_compl).1 hxNotInterior δ hδ
  · intro h
    have hA : ∀ δ > 0, (Metric.ball x δ ∩ A).Nonempty :=
      fun δ hδ => (h δ hδ).1
    have hAcompl : ∀ δ > 0, (Metric.ball x δ ∩ Aᶜ).Nonempty :=
      fun δ hδ => (h δ hδ).2
    have hxClosure : x ∈ closure A :=
      (mem_closure_iff_ball_intersects).2 hA
    have hxNotInterior : x ∉ interior A :=
      (not_mem_interior_iff_ball_meets_compl).2 hAcompl
    exact by
      change x ∈ closure A \ interior A
      exact ⟨hxClosure, hxNotInterior⟩

/-- Corollary 7.2.28. For a subset `A` of a metric space, the boundary is the
intersection of the closures of `A` and its complement:
`∂A = Ā ∩ \overline{Aᶜ}`. -/
lemma frontier_eq_closure_inter_closure_compl {X : Type*} [PseudoMetricSpace X]
    (A : Set X) : frontier A = closure A ∩ closure (Aᶜ) := by
  simpa using (frontier_eq_closure_inter_closure (s := A))

end Section02
end Chap07
