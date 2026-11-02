import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_21

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

-- Domain sampling:
-- * graph-coordinate owner reused from Section 3.7: `complete_graph_edges`
-- * source-facing owners here: `cutIncidenceVector`, `cutVertices`, `cutPolytope`
-- * core/canonical convex-face owner for "forms an edge": `IsEdgeOf`
-- * derived bridge API: `isEdgeOf_segment_iff`, together with `Set.extremePoints`/`IsExtreme`
-- * derived API here: the ambient `0/1` box characterization of cut vertices

section Example_3_36

/-- The cut-incidence value attached to an ordered pair of vertices is symmetric in the two
vertices. -/
theorem cut_incidence_value_symm {n : ℕ} (W : Finset (Fin n)) (u v : Fin n) :
    (if (u ∈ W) = (v ∈ W) then (0 : ℝ) else 1) =
      (if (v ∈ W) = (u ∈ W) then (0 : ℝ) else 1) := by
  -- Swapping the two endpoints does not change the equality test.
  by_cases huv : (u ∈ W) = (v ∈ W) <;> simp [huv, eq_comm]

/-- The cut-incidence vector of the cut determined by `W` in the complete graph on `Fin n`. -/
def cutIncidenceVector {n : ℕ} (W : Finset (Fin n)) : complete_graph_edges n → ℝ :=
  fun e ↦
    Sym2.lift
      ⟨fun u v : Fin n ↦ if (u ∈ W) = (v ∈ W) then (0 : ℝ) else 1,
        cut_incidence_value_symm W⟩
      e.1

/-- On the unordered edge `{u,v}`, the cut-incidence vector records whether `u` and `v` lie on
opposite sides of the cut determined by `W`. -/
theorem cutIncidenceVector_apply_pair {n : ℕ} (W : Finset (Fin n)) (u v : Fin n)
    (h : ¬ (s(u, v) : Sym2 (Fin n)).IsDiag) :
    cutIncidenceVector W ⟨s(u, v), h⟩ = if (u ∈ W) = (v ∈ W) then 0 else 1 := by
  -- Evaluate the `Sym2.lift` on the concrete unordered pair `s(u,v)`.
  simp [cutIncidenceVector]

/-- The set of cut-incidence vectors of the complete graph on `Fin n`. -/
def cutVertices (n : ℕ) : Set (complete_graph_edges n → ℝ) :=
  Set.range fun W : Finset (Fin n) ↦ cutIncidenceVector W

/-- The cut polytope of the complete graph on `Fin n` is the convex hull of its cut-incidence
vectors. -/
def cutPolytope (n : ℕ) : Set (complete_graph_edges n → ℝ) :=
  convexHull ℝ (cutVertices n)

/-- Helper for Example 3.36: every cut-incidence vector has only `0` and `1` edge coordinates. -/
lemma cutVertices_subset_zero_one_box {n : ℕ} :
    cutVertices n ⊆ {x : complete_graph_edges n → ℝ | ∀ e, x e = 0 ∨ x e = 1} := by
  intro x hx
  rcases hx with ⟨W, rfl⟩
  intro e
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      -- On each concrete edge, the cut-incidence value is visibly either `0` or `1`.
      change cutIncidenceVector W ⟨s(u, v), he⟩ = 0 ∨ cutIncidenceVector W ⟨s(u, v), he⟩ = 1
      rw [cutIncidenceVector_apply_pair W u v he]
      by_cases huv : (u ∈ W) = (v ∈ W)
      · left
        simp [huv]
      · right
        simp [huv]

/-- Helper for Example 3.36: the cut vertices lie in the ambient unit box on edge coordinates. -/
lemma cutVertices_subset_unit_box (n : ℕ) :
    cutVertices n ⊆ Set.univ.pi (fun _ : complete_graph_edges n ↦ Set.Icc (0 : ℝ) 1) := by
  intro x hx
  rw [Set.mem_univ_pi]
  intro e
  rcases cutVertices_subset_zero_one_box hx e with h0 | h1
  · rw [h0]
    simp
  · rw [h1]
    simp

/-- Helper for Example 3.36: the extreme points of the ambient unit box are exactly the `0/1`
edge vectors. -/
lemma extremePoints_cutCoordinate_unit_box_eq (n : ℕ) :
    (Set.univ.pi (fun _ : complete_graph_edges n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ =
      {x : complete_graph_edges n → ℝ | ∀ e, x e = 0 ∨ x e = 1} := by
  -- Compute the extreme points coordinatewise and simplify the interval case.
  rw [extremePoints_pi]
  ext x
  simp [zero_le_one]

/-- Helper for Example 3.36: the cut polytope is contained in the ambient unit box. -/
lemma cutPolytope_subset_unit_box (n : ℕ) :
    cutPolytope n ⊆ Set.univ.pi (fun _ : complete_graph_edges n ↦ Set.Icc (0 : ℝ) 1) := by
  -- The convex hull stays inside any convex set containing all cut vertices.
  rw [cutPolytope]
  refine convexHull_min (cutVertices_subset_unit_box n) ?_
  exact convex_pi fun _ _ ↦ convex_Icc (0 : ℝ) 1

/-- Every cut-incidence vector is an extreme point of the cut polytope. -/
theorem cutIncidenceVector_mem_extremePoints_cutPolytope {n : ℕ} (W : Finset (Fin n)) :
    cutIncidenceVector W ∈ (cutPolytope n).extremePoints ℝ := by
  have hxHull : cutIncidenceVector W ∈ cutPolytope n := by
    -- Every generator belongs to the convex hull that defines the cut polytope.
    rw [cutPolytope]
    exact subset_convexHull ℝ (cutVertices n) ⟨W, rfl⟩
  have hxBox :
      cutIncidenceVector W ∈
        (Set.univ.pi (fun _ : complete_graph_edges n ↦ Set.Icc (0 : ℝ) 1)).extremePoints ℝ := by
    -- The `0/1` description identifies `x` as an extreme point of the ambient unit box.
    rw [extremePoints_cutCoordinate_unit_box_eq]
    exact cutVertices_subset_zero_one_box ⟨W, rfl⟩
  -- Transfer extremality from the ambient unit box to the smaller convex hull.
  exact
    inter_extremePoints_subset_extremePoints_of_subset (cutPolytope_subset_unit_box n)
      ⟨hxHull, hxBox⟩

/-- Helper for Example 3.36: complementing a cut does not change its cut-incidence vector. -/
theorem cutIncidenceVector_compl_eq {n : ℕ} (W : Finset (Fin n)) :
    cutIncidenceVector (Finset.univ \ W) = cutIncidenceVector W := by
  ext e
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h u v =>
      -- Passing to the complement flips both endpoint-membership booleans, so the xor test is
      -- unchanged.
      rw [cutIncidenceVector_apply_pair (Finset.univ \ W) u v he]
      rw [cutIncidenceVector_apply_pair W u v he]
      by_cases hu : u ∈ W <;> by_cases hv : v ∈ W <;> simp [hu, hv]

/-- Helper for Example 3.36: every cut-incidence vector of the cut polytope is an extreme point. -/
theorem cutVertices_subset_extremePoints_cutPolytope (n : ℕ) :
    cutVertices n ⊆ (cutPolytope n).extremePoints ℝ := by
  rintro _ ⟨W, rfl⟩
  exact cutIncidenceVector_mem_extremePoints_cutPolytope W

/-- Helper for Example 3.36: the textbook four-region separator is the coordinatewise functional
`x^S + x^T - 1`. -/
def cut_separator_coeff {n : ℕ} (S T : Finset (Fin n)) : complete_graph_edges n → ℝ :=
  fun e ↦ cutIncidenceVector S e + cutIncidenceVector T e - 1

/-- Helper for Example 3.36: the separator coefficients define a continuous linear functional by
summing the coordinate projections against those coefficients. -/
noncomputable def cut_separator_functional {n : ℕ} (S T : Finset (Fin n)) :
    StrongDual ℝ (complete_graph_edges n → ℝ) :=
  ∑ e, cut_separator_coeff S T e • ContinuousLinearMap.proj e

/-- Helper for Example 3.36: the separator functional evaluates as the expected coordinate sum. -/
lemma cut_separator_functional_apply {n : ℕ} (S T : Finset (Fin n))
    (x : complete_graph_edges n → ℝ) :
    cut_separator_functional S T x = ∑ e, cut_separator_coeff S T e * x e := by
  -- Expand the finite sum of coordinate projections and simplify the scalar action.
  simp [cut_separator_functional, cut_separator_coeff, mul_comm]

/-- Helper for Example 3.36: each separator coefficient is one of `-1`, `0`, or `1`. -/
lemma cut_separator_coeff_eq_neg_one_zero_or_one {n : ℕ} (S T : Finset (Fin n))
    (e : complete_graph_edges n) :
    cut_separator_coeff S T e = -1 ∨
      cut_separator_coeff S T e = 0 ∨ cut_separator_coeff S T e = 1 := by
  have hS01 : cutIncidenceVector S e = 0 ∨ cutIncidenceVector S e = 1 := by
    simpa using cutVertices_subset_zero_one_box (n := n) ⟨S, rfl⟩ e
  have hT01 : cutIncidenceVector T e = 0 ∨ cutIncidenceVector T e = 1 := by
    simpa using cutVertices_subset_zero_one_box (n := n) ⟨T, rfl⟩ e
  rcases hS01 with hS | hS <;> rcases hT01 with hT | hT <;>
    simp [cut_separator_coeff, hS, hT]

/-- Helper for Example 3.36: on every coordinate in the unit box, the separator contribution is at
most the common endpoint contribution `x^S_e x^T_e`. -/
lemma cut_separator_edge_bound {n : ℕ} (S T : Finset (Fin n)) (e : complete_graph_edges n)
    {x : complete_graph_edges n → ℝ} (hx0 : 0 ≤ x e) (hx1 : x e ≤ 1) :
    cut_separator_coeff S T e * x e ≤ cutIncidenceVector S e * cutIncidenceVector T e := by
  have hS01 : cutIncidenceVector S e = 0 ∨ cutIncidenceVector S e = 1 := by
    simpa using cutVertices_subset_zero_one_box (n := n) ⟨S, rfl⟩ e
  have hT01 : cutIncidenceVector T e = 0 ∨ cutIncidenceVector T e = 1 := by
    simpa using cutVertices_subset_zero_one_box (n := n) ⟨T, rfl⟩ e
  rcases hS01 with hS | hS
  · rcases hT01 with hT | hT
    · -- When both endpoint cuts vanish on `e`, the separator coefficient is `-1`.
      have hxneg : -x e ≤ 0 := by linarith
      simpa [cut_separator_coeff, hS, hT] using hxneg
    · -- When exactly one endpoint cut uses `e`, the separator coefficient is `0`.
      simp [cut_separator_coeff, hS, hT]
  · -- When both endpoint cuts vanish on `e`, the separator coefficient is `-1`.
    rcases hT01 with hT | hT
    · -- This is the symmetric mixed case.
      simp [cut_separator_coeff, hS, hT]
    · -- When both endpoint cuts use `e`, the separator coefficient is `1`.
      simpa [cut_separator_coeff, hS, hT] using hx1

/-- Helper for Example 3.36: evaluating the separator on the left endpoint reproduces the common
maximizing value. -/
lemma cut_separator_coeff_mul_left_endpoint {n : ℕ} (S T : Finset (Fin n))
    (e : complete_graph_edges n) :
    cut_separator_coeff S T e * cutIncidenceVector S e =
      cutIncidenceVector S e * cutIncidenceVector T e := by
  have hS01 : cutIncidenceVector S e = 0 ∨ cutIncidenceVector S e = 1 := by
    simpa using cutVertices_subset_zero_one_box (n := n) ⟨S, rfl⟩ e
  have hT01 : cutIncidenceVector T e = 0 ∨ cutIncidenceVector T e = 1 := by
    simpa using cutVertices_subset_zero_one_box (n := n) ⟨T, rfl⟩ e
  rcases hS01 with hS | hS
  · rcases hT01 with hT | hT <;> simp [cut_separator_coeff, hS, hT]
  · rcases hT01 with hT | hT <;> simp [cut_separator_coeff, hS, hT]

/-- Helper for Example 3.36: evaluating the separator on the right endpoint gives the same common
maximizing value. -/
lemma cut_separator_coeff_mul_right_endpoint {n : ℕ} (S T : Finset (Fin n))
    (e : complete_graph_edges n) :
    cut_separator_coeff S T e * cutIncidenceVector T e =
      cutIncidenceVector S e * cutIncidenceVector T e := by
  have hS01 : cutIncidenceVector S e = 0 ∨ cutIncidenceVector S e = 1 := by
    simpa using cutVertices_subset_zero_one_box (n := n) ⟨S, rfl⟩ e
  have hT01 : cutIncidenceVector T e = 0 ∨ cutIncidenceVector T e = 1 := by
    simpa using cutVertices_subset_zero_one_box (n := n) ⟨T, rfl⟩ e
  rcases hS01 with hS | hS
  · rcases hT01 with hT | hT <;> simp [cut_separator_coeff, hS, hT]
  · rcases hT01 with hT | hT <;> simp [cut_separator_coeff, hS, hT]

/-- Helper for Example 3.36: the separator is valid on the whole cut polytope and tight at both
endpoint cut vectors. -/
lemma cut_separator_valid_and_endpoint_tight {n : ℕ} (S T : Finset (Fin n)) :
    let l := cut_separator_functional S T
    let β := ∑ e, cutIncidenceVector S e * cutIncidenceVector T e
    l (cutIncidenceVector S) = β ∧
      l (cutIncidenceVector T) = β ∧
      ∀ x ∈ cutPolytope n, l x ≤ β := by
  classical
  intro l β
  refine ⟨?_, ?_, ?_⟩
  · -- Summing the coordinatewise endpoint identity yields the claimed value at `x^S`.
    rw [cut_separator_functional_apply]
    simp_rw [cut_separator_coeff_mul_left_endpoint]
    simp [β]
  · -- The same coordinatewise identity gives the value at `x^T`.
    rw [cut_separator_functional_apply]
    simp_rw [cut_separator_coeff_mul_right_endpoint]
    simp [β]
  · intro x hxP
    -- The unit-box containment gives the coordinatewise bounds used by the separator argument.
    have hxBox := cutPolytope_subset_unit_box (n := n) hxP
    rw [Set.mem_univ_pi] at hxBox
    rw [cut_separator_functional_apply]
    calc
      ∑ e, cut_separator_coeff S T e * x e ≤
          ∑ e, cutIncidenceVector S e * cutIncidenceVector T e := by
        refine Finset.sum_le_sum ?_
        intro e he
        exact cut_separator_edge_bound S T e (hxBox e).1 (hxBox e).2
      _ = β := rfl

/-- Helper for Example 3.36: fixing a root vertex, the cut value on `{u,v}` is the xor of the two
root-edge values. -/
lemma cutIncidenceVector_apply_pair_eq_of_root_values {n : ℕ} (W : Finset (Fin n))
    {r u v : Fin n} (hru : r ≠ u) (hrv : r ≠ v) (huv : u ≠ v) :
    cutIncidenceVector W ⟨s(u, v), by simpa [Sym2.mk_isDiag_iff] using huv⟩ =
      if cutIncidenceVector W ⟨s(r, u), by simpa [Sym2.mk_isDiag_iff] using hru⟩ =
          cutIncidenceVector W ⟨s(r, v), by simpa [Sym2.mk_isDiag_iff] using hrv⟩ then
        0
      else
        1 := by
  -- Evaluate all three cut indicators and split on the memberships of the three vertices in `W`.
  rw [cutIncidenceVector_apply_pair W u v
      (by simpa [Sym2.mk_isDiag_iff] using huv)]
  rw [cutIncidenceVector_apply_pair W r u
      (by simpa [Sym2.mk_isDiag_iff] using hru)]
  rw [cutIncidenceVector_apply_pair W r v
      (by simpa [Sym2.mk_isDiag_iff] using hrv)]
  by_cases hr : r ∈ W <;> by_cases hu : u ∈ W <;> by_cases hv : v ∈ W <;> simp [hr, hu, hv]

/-- Helper for Example 3.36: the edge joining the root vertex `0` to `u.succ` is nondegenerate.
-/
lemma rootEdge_not_diag {n : ℕ} (u : Fin n) :
    ¬ (s((0 : Fin (n + 1)), u.succ) : Sym2 (Fin (n + 1))).IsDiag := by
  -- The successor vertex cannot equal the root.
  simp [Sym2.mk_isDiag_iff, eq_comm, Fin.succ_ne_zero]

/-- Helper for Example 3.36: the edge from the root `0` to `u.succ` in the complete graph on
`Fin (n + 1)`. -/
def rootEdge {n : ℕ} (u : Fin n) : complete_graph_edges (n + 1) :=
  ⟨s((0 : Fin (n + 1)), u.succ), rootEdge_not_diag u⟩

/-- Helper for Example 3.36: distinct successor vertices determine a nondegenerate edge. -/
lemma succPairEdge_not_diag {n : ℕ} {u v : Fin n} (huv : u ≠ v) :
    ¬ (s(u.succ, v.succ) : Sym2 (Fin (n + 1))).IsDiag := by
  -- Distinct predecessors stay distinct after applying `Fin.succ`.
  rw [Sym2.mk_isDiag_iff]
  intro hdiag
  apply huv
  apply Fin.ext
  exact Nat.succ.inj (congrArg Fin.val hdiag)

/-- Helper for Example 3.36: the edge joining `u.succ` and `v.succ`. -/
def succPairEdge {n : ℕ} (u v : Fin n) (huv : u ≠ v) : complete_graph_edges (n + 1) :=
  ⟨s(u.succ, v.succ), succPairEdge_not_diag huv⟩

/-- Helper for Example 3.36: the edge `{u.succ,v.succ}` is the xor of the two root-edge values. -/
lemma cutIncidenceVector_apply_succPair_eq_of_root_values {n : ℕ} (W : Finset (Fin (n + 1)))
    {u v : Fin n} (huv : u ≠ v) :
    cutIncidenceVector W (succPairEdge u v huv) =
      if cutIncidenceVector W (rootEdge u) = cutIncidenceVector W (rootEdge v) then 0 else 1 := by
  -- Specialize the general root-edge xor formula to the distinguished root vertex `0`.
  simpa [succPairEdge, rootEdge] using
    (cutIncidenceVector_apply_pair_eq_of_root_values W
      (r := (0 : Fin (n + 1))) (u := u.succ) (v := v.succ)
      (Ne.symm (Fin.succ_ne_zero u))
      (Ne.symm (Fin.succ_ne_zero v))
      (fun h => huv ((Fin.succ_injective _) h)))

/-- Helper for Example 3.36: on a `0/1` agreement coordinate, separator tightness forces the third
coordinate to equal the common endpoint value. -/
lemma zeroOne_tight_eq_of_agree {a c : ℝ}
    (ha01 : a = 0 ∨ a = 1)
    (htight : (a + a - 1) * c = a * a) :
    c = a := by
  -- The two possible endpoint values reduce the equality to either `-c = 0` or `c = 1`.
  rcases ha01 with rfl | rfl <;> linarith

/-- Helper for Example 3.36: a `0/1` value matching the xor with a fixed pivot equals the target
`0/1` value. -/
lemma zeroOne_eq_of_xor_eq {p q s t : ℝ}
    (hs01 : s = 0 ∨ s = 1)
    (hq01 : q = 0 ∨ q = 1)
    (ht01 : t = 0 ∨ t = 1)
    (hps : p = s)
    (hxor : (if p = q then (0 : ℝ) else 1) = if s = t then 0 else 1) :
    q = t := by
  -- Once the pivot values agree, there are only finitely many `0/1` xor patterns to inspect.
  subst hps
  rcases hs01 with rfl | rfl <;>
    rcases hq01 with rfl | rfl <;>
    rcases ht01 with rfl | rfl <;>
    simp at hxor ⊢

/-- Helper for Example 3.36: for `0/1` pairs, replacing both entries by their complements does not
change the xor value. -/
lemma zeroOne_xor_eq_of_ne {a b c d : ℝ}
    (ha01 : a = 0 ∨ a = 1)
    (hb01 : b = 0 ∨ b = 1)
    (hc01 : c = 0 ∨ c = 1)
    (hd01 : d = 0 ∨ d = 1)
    (hab : a ≠ b)
    (hcd : c ≠ d) :
    (if a = c then (0 : ℝ) else 1) = if b = d then 0 else 1 := by
  -- Distinct `0/1` values are complements, so equality/non-equality is preserved in both pairs.
  rcases ha01 with rfl | rfl <;>
    rcases hb01 with rfl | rfl <;>
    rcases hc01 with rfl | rfl <;>
    rcases hd01 with rfl | rfl <;>
    simp at hab hcd ⊢

/-- Helper for Example 3.36: among three `0/1` values, if the first two are different then the
third agrees with one of them. -/
lemma zeroOne_eq_left_or_right {a b c : ℝ}
    (ha01 : a = 0 ∨ a = 1)
    (hb01 : b = 0 ∨ b = 1)
    (hc01 : c = 0 ∨ c = 1)
    (hab : a ≠ b) :
    c = a ∨ c = b := by
  -- Distinct `0/1` endpoints exhaust the only two possible values.
  rcases ha01 with rfl | rfl <;>
    rcases hb01 with rfl | rfl <;>
    rcases hc01 with rfl | rfl <;>
    simp at hab ⊢

/-- Helper for Example 3.36: the raw edge spelling `{u.succ,0}` evaluates exactly as the canonical
`rootEdge u`. -/
lemma cutIncidenceVector_rootEdge_symm {n : ℕ} (W : Finset (Fin (n + 1))) (u : Fin n)
    (h : ¬ (s(u.succ, (0 : Fin (n + 1))) : Sym2 (Fin (n + 1))).IsDiag) :
    cutIncidenceVector W ⟨s(u.succ, 0), h⟩ = cutIncidenceVector W (rootEdge u) := by
  -- Reversing the edge endpoints does not change the cut-incidence coordinate.
  rw [cutIncidenceVector_apply_pair W u.succ 0 h]
  rw [rootEdge, cutIncidenceVector_apply_pair W 0 u.succ (rootEdge_not_diag u)]
  by_cases hu : u.succ ∈ W <;> by_cases h0 : (0 : Fin (n + 1)) ∈ W <;> simp [hu, h0, eq_comm]

/-- Helper for Example 3.36: on `Fin (n + 1)`, a cut-incidence vector is determined by its values
on the edges adjacent to the root vertex `0`. -/
lemma cutIncidenceVector_eq_of_root_values_eq {n : ℕ}
    (W U : Finset (Fin (n + 1)))
    (hroot : ∀ u : Fin n, cutIncidenceVector W (rootEdge u) = cutIncidenceVector U (rootEdge u)) :
    cutIncidenceVector W = cutIncidenceVector U := by
  -- Route correction: normalize the raw edge spellings before applying the root-edge API.
  ext e
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | h a b =>
      rcases Fin.eq_zero_or_eq_succ a with rfl | ⟨u, rfl⟩
      · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨v, rfl⟩
        · -- The diagonal edge `{0,0}` is excluded from `complete_graph_edges`.
          exact False.elim <| he <| by simp [Sym2.mk_isDiag_iff]
        · -- The forward root-edge spelling matches the hypothesis directly.
          simpa [rootEdge] using hroot v
      · rcases Fin.eq_zero_or_eq_succ b with rfl | ⟨v, rfl⟩
        · -- The reverse root-edge spelling is normalized by the dedicated symmetry helper.
          rw [cutIncidenceVector_rootEdge_symm W u he, cutIncidenceVector_rootEdge_symm U u he]
          exact hroot u
        · by_cases huv : u = v
          · -- The diagonal successor-successor edge is excluded as well.
            subst huv
            exact False.elim <| he <| by simp [Sym2.mk_isDiag_iff]
          · -- Once normalized to `succPairEdge`, the root values determine the edge value.
            simpa [succPairEdge, hroot u, hroot v] using
              (show cutIncidenceVector W (succPairEdge u v huv) =
                  cutIncidenceVector U (succPairEdge u v huv) by
                rw [cutIncidenceVector_apply_succPair_eq_of_root_values (W := W) huv]
                rw [cutIncidenceVector_apply_succPair_eq_of_root_values (W := U) huv]
                simp [hroot u, hroot v])

/-- Helper for Example 3.36: if a nonnegative weighted average of terms bounded above by `β`
already equals `β`, then every positive-weight term is itself equal to `β`. -/
lemma positiveWeight_tight_of_weightedAverage_eq
    {ι : Type*} [Fintype ι] (w a : ι → ℝ) {β : ℝ}
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (ha_le : ∀ i, a i ≤ β)
    (hw_sum : ∑ i, w i = 1)
    (havg : ∑ i, w i * a i = β) :
    ∀ i, w i ≠ 0 → a i = β := by
  intro i hwi
  -- The total weighted gap to `β` vanishes, so every positive-weight gap vanishes individually.
  have hgap_sum : ∑ j, w j * (β - a j) = 0 := by
    calc
      ∑ j, w j * (β - a j)
          = ∑ j, (w j * β - w j * a j) := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = (∑ j, w j * β) - ∑ j, w j * a j := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ j, w j) * β - ∑ j, w j * a j := by
            congr 1
            rw [Finset.sum_mul]
      _ = 1 * β - β := by rw [hw_sum, havg]
      _ = 0 := by ring
  have hgap_zero_fun : (fun j ↦ w j * (β - a j)) = 0 := by
    exact
      (Fintype.sum_eq_zero_iff_of_nonneg fun j ↦
        mul_nonneg (hw_nonneg j) (sub_nonneg.mpr (ha_le j))).1 hgap_sum
  have hgap_zero : ∀ j, w j * (β - a j) = 0 := by
    intro j
    simpa using congrArg (fun f : ι → ℝ ↦ f j) hgap_zero_fun
  have hi_gap : β - a i = 0 := by
    rcases mul_eq_zero.mp (hgap_zero i) with hwi0 | hi_gap
    · exact False.elim (hwi hwi0)
    · exact hi_gap
  linarith

/-- Helper for Example 3.36: if the separator is tight at the cut vector `x^W`, then the
coordinatewise separator inequality is tight on every edge. -/
lemma cut_separator_tight_edgewise {n : ℕ}
    (S T W : Finset (Fin n))
    (htight :
      cut_separator_functional S T (cutIncidenceVector W) =
        ∑ e, cutIncidenceVector S e * cutIncidenceVector T e) :
    ∀ e : complete_graph_edges n,
      cut_separator_coeff S T e * cutIncidenceVector W e =
        cutIncidenceVector S e * cutIncidenceVector T e := by
  intro e
  -- The sum of the nonnegative coordinate gaps is zero, so the chosen gap is zero as well.
  have hgap_sum :
      ∑ f, (cutIncidenceVector S f * cutIncidenceVector T f -
          cut_separator_coeff S T f * cutIncidenceVector W f) = 0 := by
    calc
      ∑ f, (cutIncidenceVector S f * cutIncidenceVector T f -
          cut_separator_coeff S T f * cutIncidenceVector W f)
          = (∑ f, cutIncidenceVector S f * cutIncidenceVector T f) -
              ∑ f, cut_separator_coeff S T f * cutIncidenceVector W f := by
                rw [Finset.sum_sub_distrib]
      _ = (∑ f, cutIncidenceVector S f * cutIncidenceVector T f) -
            cut_separator_functional S T (cutIncidenceVector W) := by
              rw [cut_separator_functional_apply]
      _ = 0 := by rw [htight, sub_self]
  have hgap_zero :
      ∀ f : complete_graph_edges n,
        cutIncidenceVector S f * cutIncidenceVector T f -
          cut_separator_coeff S T f * cutIncidenceVector W f = 0 := by
    have hgap_zero_fun :
        (fun f : complete_graph_edges n ↦
          cutIncidenceVector S f * cutIncidenceVector T f -
            cut_separator_coeff S T f * cutIncidenceVector W f) = 0 := by
      refine
      (Fintype.sum_eq_zero_iff_of_nonneg ?_).1 hgap_sum
      intro f
      have hW01 : cutIncidenceVector W f = 0 ∨ cutIncidenceVector W f = 1 := by
        simpa using cutVertices_subset_zero_one_box (n := n) ⟨W, rfl⟩ f
      have hW0 : 0 ≤ cutIncidenceVector W f := by
        rcases hW01 with hW | hW <;> linarith
      have hW1 : cutIncidenceVector W f ≤ 1 := by
        rcases hW01 with hW | hW <;> linarith
      exact sub_nonneg.mpr (cut_separator_edge_bound S T f hW0 hW1)
    intro f
    simpa using congrArg (fun g : complete_graph_edges n → ℝ ↦ g f) hgap_zero_fun
  linarith [hgap_zero e]

/-- Helper for Example 3.36: an edgewise-tight cut vector matches one endpoint on every root edge.
-/
lemma tightRootPattern_eq_left_or_right {n : ℕ}
    (S T W : Finset (Fin (n + 1)))
    (hxy : cutIncidenceVector S ≠ cutIncidenceVector T)
    (hedge :
      ∀ e : complete_graph_edges (n + 1),
        cut_separator_coeff S T e * cutIncidenceVector W e =
          cutIncidenceVector S e * cutIncidenceVector T e) :
    (∀ u : Fin n, cutIncidenceVector W (rootEdge u) = cutIncidenceVector S (rootEdge u)) ∨
      (∀ u : Fin n, cutIncidenceVector W (rootEdge u) = cutIncidenceVector T (rootEdge u)) := by
  -- Route correction: classify tight cut vectors from one pivot root edge instead of a global
  -- four-region case split.
  have hS01 :
      ∀ u : Fin n,
        cutIncidenceVector S (rootEdge u) = 0 ∨
          cutIncidenceVector S (rootEdge u) = 1 := by
    intro u
    simpa using cutVertices_subset_zero_one_box (n := n + 1) ⟨S, rfl⟩ (rootEdge u)
  have hT01 :
      ∀ u : Fin n,
        cutIncidenceVector T (rootEdge u) = 0 ∨
          cutIncidenceVector T (rootEdge u) = 1 := by
    intro u
    simpa using cutVertices_subset_zero_one_box (n := n + 1) ⟨T, rfl⟩ (rootEdge u)
  have hW01 :
      ∀ u : Fin n,
        cutIncidenceVector W (rootEdge u) = 0 ∨
          cutIncidenceVector W (rootEdge u) = 1 := by
    intro u
    simpa using cutVertices_subset_zero_one_box (n := n + 1) ⟨W, rfl⟩ (rootEdge u)
  have hpivot :
      ∃ u0 : Fin n,
        cutIncidenceVector S (rootEdge u0) ≠ cutIncidenceVector T (rootEdge u0) := by
    by_contra hpivot
    have hroot :
        ∀ u : Fin n,
          cutIncidenceVector S (rootEdge u) = cutIncidenceVector T (rootEdge u) := by
      intro u
      by_contra hu
      exact hpivot ⟨u, hu⟩
    exact hxy (cutIncidenceVector_eq_of_root_values_eq S T hroot)
  rcases hpivot with ⟨u0, hu0diff⟩
  have hu0_choice :
      cutIncidenceVector W (rootEdge u0) = cutIncidenceVector S (rootEdge u0) ∨
        cutIncidenceVector W (rootEdge u0) = cutIncidenceVector T (rootEdge u0) := by
    exact zeroOne_eq_left_or_right (hS01 u0) (hT01 u0) (hW01 u0) hu0diff
  rcases hu0_choice with hu0W | hu0W
  · left
    intro u
    by_cases hu : cutIncidenceVector S (rootEdge u) = cutIncidenceVector T (rootEdge u)
    · -- Agreement root edges are forced directly by the separator equation.
      have htight_root :
          (cutIncidenceVector S (rootEdge u) +
              cutIncidenceVector S (rootEdge u) - 1) *
            cutIncidenceVector W (rootEdge u) =
          cutIncidenceVector S (rootEdge u) * cutIncidenceVector S (rootEdge u) := by
        simpa [cut_separator_coeff, hu] using hedge (rootEdge u)
      exact zeroOne_tight_eq_of_agree (hS01 u) htight_root
    · by_cases huu0 : u = u0
      · simpa [huu0] using hu0W
      · -- On differing root edges, compare against the pivot via the pair edge `{u0.succ,u.succ}`.
        have hu0u : u0 ≠ u := fun h => huu0 h.symm
        have hpairST :
            cutIncidenceVector S (succPairEdge u0 u hu0u) =
              cutIncidenceVector T (succPairEdge u0 u hu0u) := by
          rw [cutIncidenceVector_apply_succPair_eq_of_root_values S hu0u]
          rw [cutIncidenceVector_apply_succPair_eq_of_root_values T hu0u]
          exact zeroOne_xor_eq_of_ne (hS01 u0) (hT01 u0) (hS01 u) (hT01 u) hu0diff hu
        have hpairS01 :
            cutIncidenceVector S (succPairEdge u0 u hu0u) = 0 ∨
              cutIncidenceVector S (succPairEdge u0 u hu0u) = 1 := by
          simpa using cutVertices_subset_zero_one_box (n := n + 1) ⟨S, rfl⟩
            (succPairEdge u0 u hu0u)
        have hpairWS :
            cutIncidenceVector W (succPairEdge u0 u hu0u) =
              cutIncidenceVector S (succPairEdge u0 u hu0u) := by
          have htight_pair :
              (cutIncidenceVector S (succPairEdge u0 u hu0u) +
                  cutIncidenceVector S (succPairEdge u0 u hu0u) - 1) *
                cutIncidenceVector W (succPairEdge u0 u hu0u) =
              cutIncidenceVector S (succPairEdge u0 u hu0u) *
                cutIncidenceVector S (succPairEdge u0 u hu0u) := by
            simpa [cut_separator_coeff, hpairST] using hedge (succPairEdge u0 u hu0u)
          exact zeroOne_tight_eq_of_agree hpairS01 htight_pair
        rw [cutIncidenceVector_apply_succPair_eq_of_root_values W hu0u] at hpairWS
        rw [cutIncidenceVector_apply_succPair_eq_of_root_values S hu0u] at hpairWS
        exact zeroOne_eq_of_xor_eq (hS01 u0) (hW01 u) (hS01 u) hu0W hpairWS
  · right
    intro u
    by_cases hu : cutIncidenceVector S (rootEdge u) = cutIncidenceVector T (rootEdge u)
    · -- Agreement root edges are forced directly by the separator equation.
      have htight_root :
          (cutIncidenceVector T (rootEdge u) +
              cutIncidenceVector T (rootEdge u) - 1) *
            cutIncidenceVector W (rootEdge u) =
          cutIncidenceVector T (rootEdge u) * cutIncidenceVector T (rootEdge u) := by
        simpa [cut_separator_coeff, hu] using hedge (rootEdge u)
      exact zeroOne_tight_eq_of_agree (hT01 u) htight_root
    · by_cases huu0 : u = u0
      · simpa [huu0] using hu0W
      · -- The same pivot propagation works symmetrically from the right endpoint.
        have hu0u : u0 ≠ u := fun h => huu0 h.symm
        have hpairTS :
            cutIncidenceVector T (succPairEdge u0 u hu0u) =
              cutIncidenceVector S (succPairEdge u0 u hu0u) := by
          symm
          rw [cutIncidenceVector_apply_succPair_eq_of_root_values S hu0u]
          rw [cutIncidenceVector_apply_succPair_eq_of_root_values T hu0u]
          exact zeroOne_xor_eq_of_ne (hS01 u0) (hT01 u0) (hS01 u) (hT01 u) hu0diff hu
        have hpairT01 :
            cutIncidenceVector T (succPairEdge u0 u hu0u) = 0 ∨
              cutIncidenceVector T (succPairEdge u0 u hu0u) = 1 := by
          simpa using cutVertices_subset_zero_one_box (n := n + 1) ⟨T, rfl⟩
            (succPairEdge u0 u hu0u)
        have hpairWT :
            cutIncidenceVector W (succPairEdge u0 u hu0u) =
              cutIncidenceVector T (succPairEdge u0 u hu0u) := by
          have htight_pair :
              (cutIncidenceVector T (succPairEdge u0 u hu0u) +
                  cutIncidenceVector T (succPairEdge u0 u hu0u) - 1) *
                cutIncidenceVector W (succPairEdge u0 u hu0u) =
              cutIncidenceVector T (succPairEdge u0 u hu0u) *
                cutIncidenceVector T (succPairEdge u0 u hu0u) := by
            simpa [cut_separator_coeff, hpairTS] using hedge (succPairEdge u0 u hu0u)
          exact zeroOne_tight_eq_of_agree hpairT01 htight_pair
        rw [cutIncidenceVector_apply_succPair_eq_of_root_values W hu0u] at hpairWT
        rw [cutIncidenceVector_apply_succPair_eq_of_root_values T hu0u] at hpairWT
        exact zeroOne_eq_of_xor_eq (hT01 u0) (hW01 u) (hT01 u) hu0W hpairWT

/-- Helper for Example 3.36: a cut vector that is tight for the separator is one of the two
endpoint cut vectors. -/
lemma tightCutIncidenceVector_eq_left_or_right {n : ℕ}
    (S T W : Finset (Fin (n + 1)))
    (hxy : cutIncidenceVector S ≠ cutIncidenceVector T)
    (htight :
      cut_separator_functional S T (cutIncidenceVector W) =
        ∑ e, cutIncidenceVector S e * cutIncidenceVector T e) :
    cutIncidenceVector W = cutIncidenceVector S ∨ cutIncidenceVector W = cutIncidenceVector T := by
  -- Route correction: the edgewise separator equalities reduce the problem to root-edge pattern
  -- propagation, and root-edge equality determines the whole cut vector.
  have hedge := cut_separator_tight_edgewise S T W htight
  rcases tightRootPattern_eq_left_or_right S T W hxy hedge with hroot | hroot
  · left
    exact cutIncidenceVector_eq_of_root_values_eq W S hroot
  · right
    exact cutIncidenceVector_eq_of_root_values_eq W T hroot

/-- Helper for Example 3.36: the separator equality set is exactly the maximizer set of the
corresponding strong-dual functional. -/
lemma separatorEqualitySet_eq_toExposed_of_mem {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {P : Set E} {l : StrongDual ℝ E} {β : ℝ} {x₀ : E}
    (hvalid : ∀ x ∈ P, l x ≤ β)
    (hx₀P : x₀ ∈ P) (hx₀ : l x₀ = β) :
    {x : E | x ∈ P ∧ l x = β} = l.toExposed P := by
  ext x
  constructor
  · rintro ⟨hxP, hxEq⟩
    -- Equality points maximize `l` because the inequality is valid on all of `P`.
    refine ⟨hxP, fun y hyP ↦ ?_⟩
    calc
      l y ≤ β := hvalid y hyP
      _ = l x := by simp [hxEq]
  · intro hx
    -- Any maximizer must attain the same value as the witness `x₀` where the bound is sharp.
    refine ⟨hx.1, ?_⟩
    have hx₀_le : l x₀ ≤ l x := hx.2 x₀ hx₀P
    have hx_le : l x ≤ l x₀ := by
      calc
        l x ≤ β := hvalid x hx.1
        _ = l x₀ := hx₀.symm
    have hx_eq : l x = l x₀ := le_antisymm hx_le hx₀_le
    simpa [hx₀] using hx_eq

/-- Helper for Example 3.36: a center of mass supported only on the two endpoints lies on the
segment joining them. -/
lemma centerMass_mem_segment_of_posSupport_eq_endpoints
    {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (t : Finset ι) (w : ι → ℝ) (z : ι → E) {x y : E}
    (hw_nonneg : ∀ i ∈ t, 0 ≤ w i)
    (hw_sum : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, w i ≠ 0 → z i = x ∨ z i = y) :
    t.centerMass w z ∈ segment ℝ x y := by
  classical
  -- Filter away zero-weight terms so the remaining support lands in the two-point set `{x,y}`.
  rw [← Finset.centerMass_filter_ne_zero (t := t) (w := w) (z := z)]
  rw [← convexHull_pair]
  refine Finset.centerMass_mem_convexHull (t := {i ∈ t | w i ≠ 0}) ?_ ?_ ?_
  · intro i hi
    exact hw_nonneg i (Finset.mem_filter.mp hi).1
  · -- The filtered support still has total weight `1`, hence positive total mass.
    have hw_sum_filter : ∑ i ∈ {i ∈ t | w i ≠ 0}, w i = 1 := by
      rw [Finset.sum_filter_ne_zero]
      exact hw_sum
    simp [hw_sum_filter]
  · intro i hi
    rcases hz i (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hi).2 with rfl | rfl <;> simp

/-- Helper for Example 3.36: when the endpoint cut vectors are distinct, every point of the
separator equality face lies on the segment between them. -/
lemma separatorEqualitySet_subset_segment {n : ℕ} (S T : Finset (Fin (n + 1)))
    (hxy : cutIncidenceVector S ≠ cutIncidenceVector T) :
    let l := cut_separator_functional S T
    let β := ∑ e, cutIncidenceVector S e * cutIncidenceVector T e
    {z : complete_graph_edges (n + 1) → ℝ | z ∈ cutPolytope (n + 1) ∧ l z = β} ⊆
      segment ℝ (cutIncidenceVector S) (cutIncidenceVector T) := by
  classical
  intro l β z hz
  rcases hz with ⟨hzP, hzEq⟩
  rcases
    (show l (cutIncidenceVector S) = β ∧
        l (cutIncidenceVector T) = β ∧
        ∀ x ∈ cutPolytope (n + 1), l x ≤ β by
      simpa [l, β] using cut_separator_valid_and_endpoint_tight (n := n + 1) S T) with
    ⟨hSβ, hTβ, hvalid⟩
  let cuts : Finset (complete_graph_edges (n + 1) → ℝ) :=
    Finset.univ.image (fun W : Finset (Fin (n + 1)) ↦ cutIncidenceVector W)
  have hzHull : z ∈ convexHull ℝ (cuts : Set (complete_graph_edges (n + 1) → ℝ)) := by
    simpa [cuts, cutPolytope, cutVertices] using hzP
  rcases (Finset.mem_convexHull (R := ℝ) (s := cuts) (x := z)).1 hzHull with
    ⟨w, hw_nonneg, hw_sum, hw_center⟩
  have havg :
      ∑ v ∈ cuts, w v * l v = β := by
    -- The separator value of the barycenter equals the barycenter of the separator values.
    calc
      ∑ v ∈ cuts, w v * l v = ∑ v ∈ cuts, l (w v • v) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            simp
      _ = l (∑ v ∈ cuts, w v • v) := by simp
      _ = l (cuts.centerMass w id) := by
            congr 1
            symm
            exact cuts.centerMass_eq_of_sum_1 (w := w) (z := id) hw_sum
      _ = β := by rw [hw_center, hzEq]
  have hpositive_tight :
      ∀ v ∈ cuts, w v ≠ 0 → l v = β := by
    intro v hv hvw
    -- The weighted gap sum vanishes, so each positive-weight gap vanishes on the finite support.
    have hgap_sum : ∑ u ∈ cuts, w u * (β - l u) = 0 := by
      calc
        ∑ u ∈ cuts, w u * (β - l u)
            = ∑ u ∈ cuts, (w u * β - w u * l u) := by
                refine Finset.sum_congr rfl ?_
                intro u hu
                ring
        _ = (∑ u ∈ cuts, w u * β) - ∑ u ∈ cuts, w u * l u := by
              rw [Finset.sum_sub_distrib]
        _ = (∑ u ∈ cuts, w u) * β - ∑ u ∈ cuts, w u * l u := by
              congr 1
              rw [Finset.sum_mul]
        _ = 1 * β - β := by rw [hw_sum, havg]
        _ = 0 := by ring
    have hgap_zero : ∀ u ∈ cuts, w u * (β - l u) = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg ?_).1 hgap_sum
      intro u hu
      have huVertex : u ∈ cutVertices (n + 1) := by
        simpa [cuts, cutVertices] using hu
      have huPoly : u ∈ cutPolytope (n + 1) := by
        rw [cutPolytope]
        exact subset_convexHull ℝ (cutVertices (n + 1)) huVertex
      exact mul_nonneg (hw_nonneg u hu) (sub_nonneg.mpr (hvalid u huPoly))
    have hvGap : β - l v = 0 := by
      rcases mul_eq_zero.mp (hgap_zero v hv) with hv0 | hvGap
      · exact False.elim (hvw hv0)
      · exact hvGap
    linarith
  have hsupport_segment :
      cuts.centerMass w id ∈ segment ℝ (cutIncidenceVector S) (cutIncidenceVector T) := by
    -- Every positive-weight cut generator is classified as one of the two endpoints.
    refine centerMass_mem_segment_of_posSupport_eq_endpoints
      (t := cuts) (w := w) (z := id) hw_nonneg hw_sum ?_
    intro v hv hvw
    have hvTight : l v = β := hpositive_tight v hv hvw
    have hvVertex : v ∈ cutVertices (n + 1) := by
      simpa [cuts, cutVertices] using hv
    rcases hvVertex with ⟨W, rfl⟩
    exact tightCutIncidenceVector_eq_left_or_right S T W hxy hvTight
  exact hw_center ▸ hsupport_segment

/-- Example 3.36. Any two distinct cut vertices of the cut polytope of the complete graph on `n`
vertices determine an edge of the cut polytope. -/
theorem cutPolytope_segment_between_distinct_cut_vertices_isEdgeOf
    {n : ℕ} {x y : complete_graph_edges n → ℝ}
    (hx : x ∈ cutVertices n) (hy : y ∈ cutVertices n) (hxy : x ≠ y) :
    IsEdgeOf (cutPolytope n) (segment ℝ x y) := by
  rcases hx with ⟨S, rfl⟩
  rcases hy with ⟨T, rfl⟩
  cases n with
  | zero =>
      -- In dimension zero there are no edges, so all cut-incidence vectors coincide.
      exact False.elim <| hxy <| by
        ext e
        rcases e with ⟨e, he⟩
        induction e using Sym2.ind with
        | h u _ =>
            exact Fin.elim0 u
  | succ n =>
      let l := cut_separator_functional S T
      let β := ∑ e, cutIncidenceVector S e * cutIncidenceVector T e
      let F : Set (complete_graph_edges (n + 1) → ℝ) :=
        {z | z ∈ cutPolytope (n + 1) ∧ l z = β}
      rcases
        (show l (cutIncidenceVector S) = β ∧
            l (cutIncidenceVector T) = β ∧
            ∀ z ∈ cutPolytope (n + 1), l z ≤ β by
          simpa [l, β] using cut_separator_valid_and_endpoint_tight (n := n + 1) S T) with
        ⟨hSβ, hTβ, hvalid⟩
      have hSPoly : cutIncidenceVector S ∈ cutPolytope (n + 1) := by
        rw [cutPolytope]
        exact subset_convexHull ℝ (cutVertices (n + 1)) ⟨S, rfl⟩
      have hTPoly : cutIncidenceVector T ∈ cutPolytope (n + 1) := by
        rw [cutPolytope]
        exact subset_convexHull ℝ (cutVertices (n + 1)) ⟨T, rfl⟩
      have hF_subset :
          F ⊆ segment ℝ (cutIncidenceVector S) (cutIncidenceVector T) := by
        simpa [F, l, β] using separatorEqualitySet_subset_segment (n := n) S T hxy
      have hF_convex : Convex ℝ F := by
        -- The equality slice is the intersection of the convex polytope with a convex hyperplane.
        simpa [F, Set.setOf_and] using
          (show Convex ℝ
              (cutPolytope (n + 1) ∩ {z : complete_graph_edges (n + 1) → ℝ | l z = β}) by
            refine (by
              rw [cutPolytope]
              exact (convex_convexHull ℝ (cutVertices (n + 1))).inter
                (convex_hyperplane
                  (f := fun z : complete_graph_edges (n + 1) → ℝ ↦ l z)
                  (by
                    refine IsLinearMap.mk ?_ ?_
                    · intro z w
                      simp
                    · intro c z
                      simp)
                  β)))
      have hsegment_subset_F :
          segment ℝ (cutIncidenceVector S) (cutIncidenceVector T) ⊆ F := by
        refine hF_convex.segment_subset ?_ ?_
        · exact ⟨hSPoly, hSβ⟩
        · exact ⟨hTPoly, hTβ⟩
      have hF_eq_segment :
          F = segment ℝ (cutIncidenceVector S) (cutIncidenceVector T) :=
        Set.Subset.antisymm hF_subset hsegment_subset_F
      have hF_toExposed :
          F = l.toExposed (cutPolytope (n + 1)) := by
        simpa [F] using separatorEqualitySet_eq_toExposed_of_mem hvalid hSPoly hSβ
      have hF_exposed : IsExposed ℝ (cutPolytope (n + 1)) F := by
        rw [hF_toExposed]
        exact ContinuousLinearMap.toExposed.isExposed
      have hExtreme :
          IsExtreme ℝ (cutPolytope (n + 1))
            (segment ℝ (cutIncidenceVector S) (cutIncidenceVector T)) := by
        simpa [hF_eq_segment] using hF_exposed.isExtreme
      exact (isEdgeOf_segment_iff hxy).2 hExtreme

/-- Distinct cut vertices are adjacent in the skeleton of the cut polytope. -/
theorem cutVertices_adj_polytope_skeleton
    {n : ℕ} {x y : complete_graph_edges n → ℝ}
    (hx : x ∈ cutVertices n) (hy : y ∈ cutVertices n) (hxy : x ≠ y) :
    (polytope_skeleton (cutPolytope n)).Adj
      ⟨x, cutVertices_subset_extremePoints_cutPolytope n hx⟩
      ⟨y, cutVertices_subset_extremePoints_cutPolytope n hy⟩ := by
  rw [polytope_skeleton_adj_iff]
  exact
    ⟨by simpa using hxy,
      cutPolytope_segment_between_distinct_cut_vertices_isEdgeOf hx hy hxy⟩

end Example_3_36
