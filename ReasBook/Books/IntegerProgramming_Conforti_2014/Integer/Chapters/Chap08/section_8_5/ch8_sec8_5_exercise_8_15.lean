/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_1.ch4_sec4_3_1_definition_4_3_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_3_2.ch4_sec4_3_2_remark_4_12

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section Exercise815

universe u v w

variable {V : Type u} {A : Type v} {K : Type w}

/-- An arc-pattern column consists of an arc-opening indicator together with the commodity-usage
indicators on that arc. -/
abbrev ArcPattern (K : Type w) := Bool × (K → Bool)

/-- The opening indicator carried by an arc-pattern column. -/
def arc_pattern_open (q : ArcPattern K) : ℝ :=
  (q.1.toNat : ℝ)

/-- The usage indicator of commodity `k` carried by an arc-pattern column. -/
def arc_pattern_flow (q : ArcPattern K) (k : K) : ℝ :=
  ((q.2 k).toNat : ℝ)

noncomputable local instance : DecidableEq V := Classical.decEq _

/-- The right-hand side of the unit flow-balance equation for commodity `k` at vertex `v`, written
as the source indicator minus the sink indicator. -/
noncomputable def commodity_balance_rhs (source sink : K → V) (k : K) (v : V) : ℝ :=
  open scoped Classical in
  (if v = source k then 1 else 0) - (if v = sink k then 1 else 0)

/-- `commodity_balance_rhs` is the source indicator minus the sink indicator. -/
theorem commodity_balance_rhs_eq_sub
    (source sink : K → V) (k : K) (v : V) :
    commodity_balance_rhs source sink k v =
      (if v = source k then 1 else 0) - (if v = sink k then 1 else 0) := by
  classical
  rfl

section ArcBlock

variable [Fintype K]

noncomputable local instance : DecidableEq (ArcPattern K) := Classical.decEq _
noncomputable local instance : Fintype (ArcPattern K) := by
  classical
  infer_instance

/-- The finite family of feasible arc patterns on an arc `a`: every selected commodity requires the
arc to be open, and the total routed demand fits into the arc capacity. -/
noncomputable def arc_block_patterns
    (demand : K → ℝ) (arcCapacity : A → ℝ) (a : A) : Finset (ArcPattern K) :=
  open scoped Classical in
  Finset.univ.filter fun q ↦
    (∀ k, q.2 k = true → q.1 = true) ∧
      ∑ k, demand k * arc_pattern_flow q k ≤ arcCapacity a * arc_pattern_open q

/-- Membership in `arc_block_patterns demand arcCapacity a` is exactly the linkage condition
between `y_a` and the commodity indicators together with the arc-capacity inequality. -/
theorem mem_arc_block_patterns_iff
    (demand : K → ℝ) (arcCapacity : A → ℝ) (a : A) (q : ArcPattern K) :
    q ∈ arc_block_patterns demand arcCapacity a ↔
      (∀ k, q.2 k = true → q.1 = true) ∧
        ∑ k, demand k * arc_pattern_flow q k ≤ arcCapacity a * arc_pattern_open q := by
  classical
  -- Unfold the filtered finset so membership becomes exactly the defining conjunction.
  simp [arc_block_patterns, Finset.mem_filter]

/-- The projected opening value `y_a` induced by the convex combination of arc-pattern columns on
arc `a`. -/
noncomputable def arc_block_open_from_columns
    (demand : K → ℝ) (arcCapacity : A → ℝ)
    (Λ : A → ArcPattern K → ℝ) : A → ℝ :=
  fun a ↦
    Finset.sum (arc_block_patterns demand arcCapacity a) fun q ↦
      arc_pattern_open q * Λ a q

/-- The projected flow value `x_a^k` induced by the convex combination of arc-pattern columns on
arc `a`. -/
noncomputable def arc_block_flow_from_columns
    (demand : K → ℝ) (arcCapacity : A → ℝ)
    (Λ : A → ArcPattern K → ℝ) : K → A → ℝ :=
  fun k a ↦
    Finset.sum (arc_block_patterns demand arcCapacity a) fun q ↦
      arc_pattern_flow q k * Λ a q

variable [Fintype A]

/-- The feasible set of the arc-block Dantzig-Wolfe reformulation: each arc block is a convex
combination of feasible arc patterns, and the projected flows satisfy the original commodity
flow-balance equations. -/
noncomputable def network_design_arc_block_dw_feasible
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (Λ : A → ArcPattern K → ℝ) : Prop :=
  (∀ a q, q ∈ arc_block_patterns demand arcCapacity a → 0 ≤ Λ a q) ∧
    (∀ a, Finset.sum (arc_block_patterns demand arcCapacity a) (fun q ↦ Λ a q) = 1) ∧
      ∀ k v,
        outgoing_flow tail (arc_block_flow_from_columns demand arcCapacity Λ k) v -
            incoming_flow head (arc_block_flow_from_columns demand arcCapacity Λ k) v =
          commodity_balance_rhs source sink k v

/-- The cost contributed by one arc-pattern column on arc `a`. -/
def arc_block_column_cost
    (fixedCost : A → ℝ) (flowCost : K → A → ℝ)
    (a : A) (q : ArcPattern K) : ℝ :=
  fixedCost a * arc_pattern_open q + ∑ k, flowCost k a * arc_pattern_flow q k

/-- The objective value of the arc-block Dantzig-Wolfe reformulation. -/
noncomputable def network_design_arc_block_dw_objective
    (demand : K → ℝ) (arcCapacity : A → ℝ)
    (fixedCost : A → ℝ) (flowCost : K → A → ℝ)
    (Λ : A → ArcPattern K → ℝ) : ℝ :=
  ∑ a,
    Finset.sum (arc_block_patterns demand arcCapacity a) fun q ↦
      arc_block_column_cost fixedCost flowCost a q * Λ a q

/-- Exercise 8.15 (1). Using the block structure indexed by arcs `a ∈ A`, the network-design
Dantzig-Wolfe reformulation has one convexity equation per arc, one nonnegative variable
`Λ_(a,q)` for each feasible arc pattern `q ∈ Q_a`, and the original commodity flow-balance
equations written for the projected variables `x_a^k = ∑_{q ∈ Q_a} q_k Λ_(a,q)`. -/
theorem exercise_8_15_arc_block_dantzig_wolfe_reformulation
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (Λ : A → ArcPattern K → ℝ)
    (h_nonneg : ∀ a q, q ∈ arc_block_patterns demand arcCapacity a → 0 ≤ Λ a q)
    (h_convexity :
      ∀ a, Finset.sum (arc_block_patterns demand arcCapacity a) (fun q ↦ Λ a q) = 1)
    (h_flow_balance : ∀ k v,
      outgoing_flow tail (arc_block_flow_from_columns demand arcCapacity Λ k) v -
          incoming_flow head (arc_block_flow_from_columns demand arcCapacity Λ k) v =
        commodity_balance_rhs source sink k v) :
    network_design_arc_block_dw_feasible tail head source sink demand arcCapacity Λ := by
  -- Package the nonnegativity, convexity, and projected flow-balance data into the feasible set.
  exact ⟨h_nonneg, h_convexity, h_flow_balance⟩

/-- Nonnegativity of the arc-pattern coefficients is one component of
`network_design_arc_block_dw_feasible`. -/
theorem network_design_arc_block_dw_feasible_nonneg
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (Λ : A → ArcPattern K → ℝ)
    (hfeasible : network_design_arc_block_dw_feasible
      tail head source sink demand arcCapacity Λ) :
      ∀ a q, q ∈ arc_block_patterns demand arcCapacity a → 0 ≤ Λ a q := by
  -- Project the nonnegativity component out of the feasible-set conjunction.
  exact hfeasible.1

/-- The convexity equations are one component of `network_design_arc_block_dw_feasible`. -/
theorem network_design_arc_block_dw_feasible_convexity
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (Λ : A → ArcPattern K → ℝ)
    (hfeasible : network_design_arc_block_dw_feasible
      tail head source sink demand arcCapacity Λ) :
      ∀ a, Finset.sum (arc_block_patterns demand arcCapacity a) (fun q ↦ Λ a q) = 1 := by
  -- Project the convexity equations out of the feasible-set conjunction.
  exact hfeasible.2.1

/-- The projected flow-balance equations are one component of
`network_design_arc_block_dw_feasible`. -/
theorem network_design_arc_block_dw_feasible_flow_balance
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (Λ : A → ArcPattern K → ℝ)
    (hfeasible : network_design_arc_block_dw_feasible
      tail head source sink demand arcCapacity Λ) :
      ∀ k v,
        outgoing_flow tail (arc_block_flow_from_columns demand arcCapacity Λ k) v -
            incoming_flow head (arc_block_flow_from_columns demand arcCapacity Λ k) v =
          commodity_balance_rhs source sink k v := by
  -- Project the commodity flow-balance equations out of the feasible-set conjunction.
  exact hfeasible.2.2

end ArcBlock

/-- Bridge from commodity-indexed network data to the Chapter 7 shortest-path owner. -/
def commodity_shortest_path_problem
    (tail head : A → V)
    (source sink : K → V)
    (length : K → A → ℝ)
    (k : K) : ShortestPathLinearProgram V A where
  tail := tail
  head := head
  s := source k
  t := sink k
  length := length k

/-- A directed `(s_k,t_k)`-path for commodity `k`, expressed through the Chapter 7 shortest-path
owner without introducing dummy path-length data into the public surface. -/
def IsCommodityStPath
    (tail head : A → V)
    (source sink : K → V)
    (k : K)
    (p : List A) : Prop :=
  (commodity_shortest_path_problem tail head source sink (fun _ _ ↦ 0) k).IsStPath p

/-- Helper for Exercise 8.15: the directed-walk predicate in `commodity_shortest_path_problem`
depends only on the network and endpoints, not on the length function. -/
private theorem commodityShortestPathIsDirectedWalkFromTo_iff
    (tail head : A → V)
    (source sink : K → V)
    (length : K → A → ℝ)
    (k : K)
    (u v : V)
    (p : List A) :
    ShortestPathLinearProgram.IsDirectedWalkFromTo
        (commodity_shortest_path_problem tail head source sink (fun _ _ ↦ 0) k) u v p ↔
      ShortestPathLinearProgram.IsDirectedWalkFromTo
        (commodity_shortest_path_problem tail head source sink length k) u v p := by
  induction p generalizing u with
  | nil =>
      -- The empty walk only checks the endpoints, so the length field never appears.
      simp [ShortestPathLinearProgram.IsDirectedWalkFromTo]
  | cons a p ih =>
      -- The recursive step advances along `head a`; the induction hypothesis handles the suffix.
      rw [ShortestPathLinearProgram.IsDirectedWalkFromTo,
        ShortestPathLinearProgram.IsDirectedWalkFromTo]
      constructor
      · rintro ⟨hau, htail⟩
        exact ⟨hau, (ih (head a)).1 htail⟩
      · rintro ⟨hau, htail⟩
        exact ⟨hau, (ih (head a)).2 htail⟩

/-- Helper for Exercise 8.15: the visited-vertex list in `commodity_shortest_path_problem`
depends only on the network and starting vertex, not on the length function. -/
private theorem commodityShortestPathWalkVerticesFrom_eq
    (tail head : A → V)
    (source sink : K → V)
    (length : K → A → ℝ)
    (k : K)
    (u : V)
    (p : List A) :
    ShortestPathLinearProgram.walkVerticesFrom
        (commodity_shortest_path_problem tail head source sink (fun _ _ ↦ 0) k) u p =
      ShortestPathLinearProgram.walkVerticesFrom
        (commodity_shortest_path_problem tail head source sink length k) u p := by
  induction p generalizing u with
  | nil =>
      -- The empty walk visits only the starting vertex.
      rfl
  | cons a p ih =>
      -- The suffix walk uses the same `head` map, so the induction hypothesis applies directly.
      simpa [ShortestPathLinearProgram.walkVerticesFrom, commodity_shortest_path_problem]
        using congrArg (List.cons u) (ih (head a))

/-- Directed `(s_k,t_k)`-pathhood depends only on the network and endpoints, not on the arc
lengths used in `commodity_shortest_path_problem`. -/
theorem isCommodityStPath_iff
    (tail head : A → V)
    (source sink : K → V)
    (length : K → A → ℝ)
    (k : K)
    (p : List A) :
    IsCommodityStPath tail head source sink k p ↔
      (commodity_shortest_path_problem tail head source sink length k).IsStPath p := by
  -- Rewrite `IsStPath` into walk and vertex-list data, then transport both parts across the
  -- irrelevant length field using the dedicated helper lemmas.
  rw [IsCommodityStPath, ShortestPathLinearProgram.IsStPath, ShortestPathLinearProgram.IsStWalk,
    ShortestPathLinearProgram.IsStPath, ShortestPathLinearProgram.IsStWalk]
  let P0 : ShortestPathLinearProgram V A :=
    commodity_shortest_path_problem tail head source sink (fun _ _ ↦ 0) k
  let P1 : ShortestPathLinearProgram V A :=
    commodity_shortest_path_problem tail head source sink length k
  have hwalk :
      P0.IsDirectedWalkFromTo P0.s P0.t p ↔ P1.IsDirectedWalkFromTo P1.s P1.t p := by
    simpa [P0, P1, commodity_shortest_path_problem] using
      commodityShortestPathIsDirectedWalkFromTo_iff
        tail head source sink length k (source k) (sink k) p
  have hvertices :
      P0.walkVerticesFrom P0.s p = P1.walkVerticesFrom P1.s p := by
    simpa [P0, P1, commodity_shortest_path_problem] using
      commodityShortestPathWalkVerticesFrom_eq tail head source sink length k (source k) p
  constructor
  · rintro ⟨hwalk₀, hnodup⟩
    exact ⟨hwalk.mp hwalk₀, hvertices ▸ hnodup⟩
  · rintro ⟨hwalk₁, hnodup⟩
    exact ⟨hwalk.mpr hwalk₁, hvertices.symm ▸ hnodup⟩

/-- The family `paths` enumerates all directed commodity paths when membership in `paths k`
is equivalent to `IsCommodityStPath tail head source sink k`. -/
def enumerates_commodity_paths
    (tail head : A → V)
    (source sink : K → V)
    (paths : K → Finset (List A)) : Prop :=
  ∀ k p, p ∈ paths k ↔
    IsCommodityStPath tail head source sink k p

noncomputable local instance : DecidableEq A := Classical.decEq _

/-- The canonical characteristic vector of `p.toFinset` records path usage by `0`-`1` arc
entries. -/
@[simp] theorem circuit_characteristic_vector_toFinset_apply (p : List A) (a : A) :
    circuit_characteristic_vector p.toFinset a = if a ∈ p then 1 else 0 := by
  simp [circuit_characteristic_vector_apply]

/-- The amount of commodity `k` sent through arc `a` by the path-column coefficients `Λ`. -/
noncomputable def commodity_path_flow_from_columns
    (paths : K → Finset (List A))
    (Λ : (k : K) → List A → ℝ) : K → A → ℝ :=
  fun k a ↦
    Finset.sum (paths k) fun p ↦
      circuit_characteristic_vector p.toFinset a * Λ k p

section CommodityBlock

variable [Fintype K]

/-- The feasible set of the commodity-block Dantzig-Wolfe reformulation: for each commodity, the
columns are exactly all directed `(s_k,t_k)`-paths, the commodity coefficients form a convex
combination, and the common arc-opening variables satisfy the capacity inequalities. -/
def network_design_commodity_path_dw_feasible
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (paths : K → Finset (List A))
    (y : A → ℝ)
    (Λ : (k : K) → List A → ℝ) : Prop :=
  enumerates_commodity_paths tail head source sink paths ∧
    (∀ k p, p ∈ paths k → 0 ≤ Λ k p) ∧
      (∀ k, Finset.sum (paths k) (fun p ↦ Λ k p) = 1) ∧
        (∀ a,
          ∑ k, demand k * commodity_path_flow_from_columns paths Λ k a ≤
            arcCapacity a * y a) ∧
          ∀ a, 0 ≤ y a ∧ y a ≤ 1

section

variable [Fintype A]

/-- The objective value of the commodity-path Dantzig-Wolfe reformulation. -/
def network_design_commodity_path_dw_objective
    (paths : K → Finset (List A))
    (fixedCost : A → ℝ)
    (flowCost : K → A → ℝ)
    (y : A → ℝ)
    (Λ : (k : K) → List A → ℝ) : ℝ :=
  (∑ a, fixedCost a * y a) +
    ∑ k,
      Finset.sum (paths k) fun p ↦
        (p.map (flowCost k)).sum * Λ k p

end

/-- Exercise 8.15 (2). Using the block structure indexed by commodities `k = 1, …, K`, the
network-design Dantzig-Wolfe reformulation has one variable `Λ_(k,p)` for every directed
`(s_k,t_k)`-path `p`, one convexity equation `∑_p Λ_(k,p) = 1` for each commodity, and arc
capacity inequalities in which the path columns are coupled through the common opening variables
`y_a`. -/
theorem exercise_8_15_commodity_block_dantzig_wolfe_reformulation
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (paths : K → Finset (List A))
    (y : A → ℝ)
    (Λ : (k : K) → List A → ℝ)
    (h_paths : enumerates_commodity_paths tail head source sink paths)
    (h_nonneg : ∀ k p, p ∈ paths k → 0 ≤ Λ k p)
    (h_convexity : ∀ k, Finset.sum (paths k) (fun p ↦ Λ k p) = 1)
    (h_capacity : ∀ a,
      ∑ k, demand k * commodity_path_flow_from_columns paths Λ k a ≤ arcCapacity a * y a)
    (h_bounds : ∀ a, 0 ≤ y a ∧ y a ≤ 1) :
    network_design_commodity_path_dw_feasible
        tail head source sink demand arcCapacity paths y Λ := by
  -- Package the path enumeration, convexity data, and shared capacity/bound constraints.
  exact ⟨h_paths, h_nonneg, h_convexity, h_capacity, h_bounds⟩

/-- Path enumeration is one component of `network_design_commodity_path_dw_feasible`. -/
theorem network_design_commodity_path_dw_feasible_paths
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (paths : K → Finset (List A))
    (y : A → ℝ)
    (Λ : (k : K) → List A → ℝ)
    (hfeasible : network_design_commodity_path_dw_feasible
      tail head source sink demand arcCapacity paths y Λ) :
      enumerates_commodity_paths tail head source sink paths := by
  -- Project the path-enumeration component out of the feasible-set conjunction.
  exact hfeasible.1

/-- Nonnegativity of the path-column coefficients is one component of
`network_design_commodity_path_dw_feasible`. -/
theorem network_design_commodity_path_dw_feasible_nonneg
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (paths : K → Finset (List A))
    (y : A → ℝ)
    (Λ : (k : K) → List A → ℝ)
    (hfeasible : network_design_commodity_path_dw_feasible
      tail head source sink demand arcCapacity paths y Λ) :
      ∀ k p, p ∈ paths k → 0 ≤ Λ k p := by
  -- Project the path-column nonnegativity conditions out of the feasible-set conjunction.
  exact hfeasible.2.1

/-- The commodity convexity equations are one component of
`network_design_commodity_path_dw_feasible`. -/
theorem network_design_commodity_path_dw_feasible_convexity
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (paths : K → Finset (List A))
    (y : A → ℝ)
    (Λ : (k : K) → List A → ℝ)
    (hfeasible : network_design_commodity_path_dw_feasible
      tail head source sink demand arcCapacity paths y Λ) :
      ∀ k, Finset.sum (paths k) (fun p ↦ Λ k p) = 1 := by
  -- Project the commodity convexity equations out of the feasible-set conjunction.
  exact hfeasible.2.2.1

/-- The shared arc-capacity inequalities are one component of
`network_design_commodity_path_dw_feasible`. -/
theorem network_design_commodity_path_dw_feasible_capacity
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (paths : K → Finset (List A))
    (y : A → ℝ)
    (Λ : (k : K) → List A → ℝ)
    (hfeasible : network_design_commodity_path_dw_feasible
      tail head source sink demand arcCapacity paths y Λ) :
      ∀ a,
        ∑ k, demand k * commodity_path_flow_from_columns paths Λ k a ≤
          arcCapacity a * y a := by
  -- Project the shared arc-capacity inequalities out of the feasible-set conjunction.
  exact hfeasible.2.2.2.1

/-- Bounds on the opening variables are one component of
`network_design_commodity_path_dw_feasible`. -/
theorem network_design_commodity_path_dw_feasible_bounds
    (tail head : A → V)
    (source sink : K → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (paths : K → Finset (List A))
    (y : A → ℝ)
    (Λ : (k : K) → List A → ℝ)
    (hfeasible : network_design_commodity_path_dw_feasible
      tail head source sink demand arcCapacity paths y Λ) :
      ∀ a, 0 ≤ y a ∧ y a ≤ 1 := by
  -- Project the opening-variable bounds out of the feasible-set conjunction.
  exact hfeasible.2.2.2.2

end CommodityBlock

section ArcBlockPricing

variable [Fintype K]

/-- The reduced cost of an arc-pattern column in the arc-block reformulation for the dual
multipliers `π_(k,v)` of the flow-balance equations and `σ_a` of the convexity equation on arc
`a`. -/
def arc_block_pricing_reduced_cost
    (tail head : A → V)
    (fixedCost : A → ℝ)
    (flowCost : K → A → ℝ)
    (pi : K → V → ℝ)
    (sigma : A → ℝ)
    (a : A)
    (q : ArcPattern K) : ℝ :=
  arc_block_column_cost fixedCost flowCost a q -
    sigma a - ∑ k, (pi k (tail a) - pi k (head a)) * arc_pattern_flow q k

/-- An arc-pattern column solves the arc-block pricing problem when it minimizes the reduced cost
over all feasible arc patterns on the chosen arc. -/
def IsOptimalArcBlockPricingColumn
    (tail head : A → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (fixedCost : A → ℝ)
    (flowCost : K → A → ℝ)
    (pi : K → V → ℝ)
    (sigma : A → ℝ)
    (a : A)
    (qStar : ArcPattern K) : Prop :=
  qStar ∈ arc_block_patterns demand arcCapacity a ∧
    ∀ q ∈ arc_block_patterns demand arcCapacity a,
      arc_block_pricing_reduced_cost tail head fixedCost flowCost pi sigma a qStar ≤
        arc_block_pricing_reduced_cost tail head fixedCost flowCost pi sigma a q

/-- Exercise 8.15 (3). For the arc-block reformulation, column generation prices each arc `a`
by solving a 0-1 knapsack-type subproblem over the feasible arc patterns `q ∈ Q_a`, minimizing
the reduced cost `f_a η + ∑_k c_a^k q_k - σ_a - ∑_k (π_(k,tail(a)) - π_(k,head(a))) q_k`. -/
theorem exercise_8_15_arc_block_pricing_problem
    (tail head : A → V)
    (demand : K → ℝ)
    (arcCapacity : A → ℝ)
    (fixedCost : A → ℝ)
    (flowCost : K → A → ℝ)
    (pi : K → V → ℝ)
    (sigma : A → ℝ)
    (a : A)
    (qStar : ArcPattern K) :
    IsOptimalArcBlockPricingColumn
        tail head demand arcCapacity fixedCost flowCost pi sigma a qStar ↔
      qStar ∈ arc_block_patterns demand arcCapacity a ∧
        ∀ q ∈ arc_block_patterns demand arcCapacity a,
          arc_block_pricing_reduced_cost tail head fixedCost flowCost pi sigma a qStar ≤
            arc_block_pricing_reduced_cost tail head fixedCost flowCost pi sigma a q := by
  -- This pricing statement is exactly the defining predicate of `IsOptimalArcBlockPricingColumn`.
  rfl

end ArcBlockPricing

/-- The reduced cost of a commodity-path column in the commodity-block reformulation for the dual
multipliers `μ_a` of the arc-capacity inequalities and `σ_k` of the commodity convexity
equation. -/
def commodity_path_pricing_reduced_cost
    (flowCost : K → A → ℝ)
    (demand : K → ℝ)
    (mu : A → ℝ)
    (sigma : K → ℝ)
    (k : K)
    (p : List A) : ℝ :=
  (p.map fun a ↦ flowCost k a + demand k * mu a).sum - sigma k

/-- The reduced-cost evaluation is the Chapter 7 path length for the reduced arc lengths
`c_a^k + d_k μ_a`, shifted by the commodity convexity multiplier. -/
theorem commodity_path_pricing_reduced_cost_eq_pathLength
    (tail head : A → V)
    (source sink : K → V)
    (flowCost : K → A → ℝ)
    (demand : K → ℝ)
    (mu : A → ℝ)
    (sigma : K → ℝ)
    (k : K)
    (p : List A) :
    commodity_path_pricing_reduced_cost flowCost demand mu sigma k p =
      (commodity_shortest_path_problem tail head source sink
        (fun k a ↦ flowCost k a + demand k * mu a) k).pathLength p - sigma k := by
  rfl

/-- A path column solves the commodity-block pricing problem when it minimizes the reduced cost
over the enumerated `(s_k,t_k)`-paths of commodity `k`. -/
def IsOptimalCommodityPathPricingColumn
    (paths : K → Finset (List A))
    (flowCost : K → A → ℝ)
    (demand : K → ℝ)
    (mu : A → ℝ)
    (sigma : K → ℝ)
    (k : K)
    (pStar : List A) : Prop :=
  pStar ∈ paths k ∧
    ∀ p ∈ paths k,
      commodity_path_pricing_reduced_cost flowCost demand mu sigma k pStar ≤
        commodity_path_pricing_reduced_cost flowCost demand mu sigma k p

/-- `IsOptimalCommodityPathPricingColumn` is exactly reduced-cost optimality over the enumerated
commodity paths. -/
theorem isOptimalCommodityPathPricingColumn_iff
    (paths : K → Finset (List A))
    (flowCost : K → A → ℝ)
    (demand : K → ℝ)
    (mu : A → ℝ)
    (sigma : K → ℝ)
    (k : K)
    (pStar : List A) :
    IsOptimalCommodityPathPricingColumn paths flowCost demand mu sigma k pStar ↔
      pStar ∈ paths k ∧
        ∀ p ∈ paths k,
          commodity_path_pricing_reduced_cost flowCost demand mu sigma k pStar ≤
            commodity_path_pricing_reduced_cost flowCost demand mu sigma k p := by
  rfl

/-- Under a commodity-path enumeration, optimal pricing columns are exactly the shortest
`(s_k,t_k)`-paths for the reduced arc lengths `c_a^k + d_k μ_a`. -/
theorem isOptimalCommodityPathPricingColumn_iff_isShortestStPath
    (tail head : A → V)
    (source sink : K → V)
    (paths : K → Finset (List A))
    (flowCost : K → A → ℝ)
    (demand : K → ℝ)
    (mu : A → ℝ)
    (sigma : K → ℝ)
    (k : K)
    (pStar : List A)
    (h_paths : enumerates_commodity_paths tail head source sink paths) :
    IsOptimalCommodityPathPricingColumn paths flowCost demand mu sigma k pStar ↔
      (commodity_shortest_path_problem tail head source sink
        (fun k a ↦ flowCost k a + demand k * mu a) k).IsShortestStPath pStar := by
  let P :=
    commodity_shortest_path_problem tail head source sink
      (fun k a ↦ flowCost k a + demand k * mu a) k
  constructor
  · intro hoptimal
    rcases hoptimal with ⟨hpStarMem, hminimal⟩
    have hpStarPath : P.IsStPath pStar := by
      -- Transport path membership in the enumerated family to the shortest-path owner.
      exact
        (isCommodityStPath_iff tail head source sink
          (fun k a ↦ flowCost k a + demand k * mu a) k pStar).1
        ((h_paths k pStar).1 hpStarMem)
    refine ⟨hpStarPath, ?_⟩
    intro p hpPath
    have hpMem : p ∈ paths k := by
      -- Convert every competing shortest-path candidate back to the enumerated path family.
      exact (h_paths k p).2
        ((isCommodityStPath_iff tail head source sink
          (fun k a ↦ flowCost k a + demand k * mu a) k p).2 hpPath)
    have hcost := hminimal p hpMem
    -- Rewrite reduced costs as path lengths and cancel the common `sigma k` shift.
    rw [commodity_path_pricing_reduced_cost_eq_pathLength
      tail head source sink flowCost demand mu sigma k pStar,
      commodity_path_pricing_reduced_cost_eq_pathLength
        tail head source sink flowCost demand mu sigma k p] at hcost
    simpa [P] using (sub_le_sub_iff_right (sigma k)).1 hcost
  · intro hshortest
    refine ⟨?_, ?_⟩
    · -- Transport shortest-path feasibility back to membership in the enumerated path family.
      exact (h_paths k pStar).2
        ((isCommodityStPath_iff tail head source sink
          (fun k a ↦ flowCost k a + demand k * mu a) k pStar).2
          hshortest.1)
    · intro p hpMem
      have hpPath : P.IsStPath p := by
        -- Membership in the enumerated family gives a valid directed `(s_k,t_k)`-path.
        exact
          (isCommodityStPath_iff tail head source sink
            (fun k a ↦ flowCost k a + demand k * mu a) k p).1
          ((h_paths k p).1 hpMem)
      have hlength := hshortest.2 p hpPath
      -- Rewrite path lengths back into reduced costs; the constant shift is the same on both sides.
      rw [commodity_path_pricing_reduced_cost_eq_pathLength
        tail head source sink flowCost demand mu sigma k pStar,
        commodity_path_pricing_reduced_cost_eq_pathLength
          tail head source sink flowCost demand mu sigma k p]
      simpa [P] using (sub_le_sub_iff_right (sigma k)).2 hlength

/-- Exercise 8.15 (4). For the commodity-block reformulation, column generation prices each
commodity `k` by solving a shortest-path-type problem over all directed `(s_k,t_k)`-paths,
minimizing the reduced cost `∑_{a ∈ p} (c_a^k + d_k μ_a) - σ_k`. -/
theorem exercise_8_15_commodity_block_pricing_problem
    (tail head : A → V)
    (source sink : K → V)
    (paths : K → Finset (List A))
    (flowCost : K → A → ℝ)
    (demand : K → ℝ)
    (mu : A → ℝ)
    (sigma : K → ℝ)
    (k : K)
    (pStar : List A)
    (h_paths : enumerates_commodity_paths tail head source sink paths) :
    IsOptimalCommodityPathPricingColumn paths flowCost demand mu sigma k pStar ↔
      (commodity_shortest_path_problem tail head source sink
        (fun k a ↦ flowCost k a + demand k * mu a) k).IsShortestStPath pStar := by
  exact isOptimalCommodityPathPricingColumn_iff_isShortestStPath
    tail head source sink paths flowCost demand mu sigma k pStar h_paths

end Exercise815
