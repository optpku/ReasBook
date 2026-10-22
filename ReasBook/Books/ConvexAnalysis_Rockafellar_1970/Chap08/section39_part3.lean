/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part2
import Books.ConvexAnalysis_Rockafellar_1970.fin_dot

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

section Chap08
section Section39

/-- A choice of orientation for a convex set, corresponding to identifying it with either its
indicator function (supremum orientation) or the negative of its indicator function (infimum
orientation). -/
inductive ConvexSetOrientation : Type
  /-- Supremum orientation (identified with the convex indicator function). -/
  | supremum : ConvexSetOrientation
  /-- Infimum orientation (identified with the concave negative indicator function). -/
  | infimum : ConvexSetOrientation

/-- The opposite orientation: supremum becomes infimum, and infimum becomes supremum. -/
def ConvexSetOrientation.opposite : ConvexSetOrientation → ConvexSetOrientation
  | .supremum => .infimum
  | .infimum => .supremum

/-- A convex set in a real vector space, equipped with a choice of orientation. -/
structure OrientedConvexSet (E : Type*) [AddCommGroup E] [Module ℝ E] where
  /-- The underlying set. -/
  carrier : Set E
  /-- Convexity of the underlying set. -/
  isConvex : Convex ℝ carrier
  /-- The chosen orientation. -/
  orientation : ConvexSetOrientation

attribute [local instance] Classical.propDecidable

/-- The indicator function `δ(· | C)` of a set `C`, valued in `EReal`: it is `0` on `C` and `+∞`
outside `C`. -/
noncomputable def indicatorEReal {E : Type*} (C : Set E) : E → EReal :=
  fun x => if x ∈ C then (0 : EReal) else ⊤

/-- The negative indicator function `-δ(· | C)` of a set `C`, valued in `EReal`: it is `0` on `C`
and `-∞` outside `C`. -/
noncomputable def negIndicatorEReal {E : Type*} (C : Set E) : E → EReal :=
  fun x => if x ∈ C then (0 : EReal) else ⊥

/-- Definition 39.0.12: A convex set can be oriented via its indicator function. With supremum
orientation one has `⟪C, x*⟫ = sup { x* x | x ∈ C }` for all `x*`, and with infimum orientation one
has `⟪C, x*⟫ = inf { x* x | x ∈ C }` for all `x*`. -/
noncomputable def OrientedConvexSet.bracket {E : Type*} [AddCommGroup E] [Module ℝ E]
    (C : OrientedConvexSet E) (xStar : E →ₗ[ℝ] ℝ) : EReal :=
  match C.orientation with
  | .supremum => sSup ((fun x => (xStar x : EReal)) '' C.carrier)
  | .infimum => sInf ((fun x => (xStar x : EReal)) '' C.carrier)

/-- The epigraph of an `EReal`-valued function `f : X → EReal`, as a subset of `X × ℝ`. -/
def eRealEpigraph {X : Type*} (f : X → EReal) : Set (X × ℝ) :=
  { p | f p.1 ≤ (p.2 : EReal) }

/-- Convexity of an `EReal`-valued function, defined as convexity of its epigraph. -/
def IsConvexEReal {X : Type*} [AddCommGroup X] [Module ℝ X] (f : X → EReal) : Prop :=
  Convex ℝ (eRealEpigraph f)

/-- The (effective) domain of a bifunction `F : U → X → EReal`, viewed as a subset of `U`: the set
of `u` for which `F u` attains some value different from `+∞`. -/
def eRealBifunctionDom {U X : Type*} (F : U → X → EReal) : Set U :=
  { u | ∃ x, F u x ≠ ⊤ }

/-- Closedness of an `EReal`-valued function, defined as topological closedness of its epigraph. -/
def IsClosedEReal {X : Type*} [TopologicalSpace X] (f : X → EReal) : Prop :=
  _root_.IsClosed (eRealEpigraph f)

namespace ConvexProcess

/-- The indicator bifunction associated to a convex process `A`: the function `F` with
`(F u)(x) = δ(x | A u)`, i.e. `0` on `A u` and `+∞` outside. -/
noncomputable def indicatorBifunction {m n : ℕ} (A : ConvexProcess m n) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x => indicatorEReal (A.toSetValued u) x

/-- The (negative) indicator bifunction associated to a convex process `A`: the function `F` with
`(F u)(x) = -δ(x | A u)`, i.e. `0` on `A u` and `-∞` outside. -/
noncomputable def negIndicatorBifunction {m n : ℕ} (A : ConvexProcess m n) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x => negIndicatorEReal (A.toSetValued u) x

end ConvexProcess

/-- Helper for Proposition 39.0.13: the indicator bifunction of a convex process is exactly the
indicator of its graph, viewed as a subset of the product space. -/
lemma helperForProposition_39_0_13_indicatorOnGraph {m n : ℕ} (A : ConvexProcess m n)
    (p : (Fin m → ℝ) × (Fin n → ℝ)) :
    ConvexProcess.indicatorBifunction A p.1 p.2 =
      indicatorEReal (setValuedGraph A.toSetValued) p := by
  -- Unfold both indicator definitions and identify graph membership with fiber membership.
  simp [ConvexProcess.indicatorBifunction, indicatorEReal, setValuedGraph]

/-- Helper for Proposition 39.0.13: the epigraph of the indicator bifunction is the graph crossed
with the nonnegative reals. -/
lemma helperForProposition_39_0_13_indicatorEpigraph_eq {m n : ℕ} (A : ConvexProcess m n) :
    eRealEpigraph (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      ConvexProcess.indicatorBifunction A p.1 p.2) =
      {q : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ |
        q.1 ∈ setValuedGraph A.toSetValued ∧ 0 ≤ q.2} := by
  ext q
  rcases q with ⟨p, t⟩
  by_cases hp : p ∈ setValuedGraph A.toSetValued
  · -- On the graph, the indicator value is `0`, so epigraph membership is exactly `0 ≤ t`.
    simp [eRealEpigraph, helperForProposition_39_0_13_indicatorOnGraph, indicatorEReal, hp]
  · -- Off the graph, the indicator value is `⊤`, so no finite height belongs to the epigraph.
    simp [eRealEpigraph, helperForProposition_39_0_13_indicatorOnGraph, indicatorEReal, hp]

/-- Helper for Proposition 39.0.13: the domain of the indicator bifunction is the domain of the
underlying convex process. -/
lemma helperForProposition_39_0_13_dom_eq {m n : ℕ} (A : ConvexProcess m n) :
    eRealBifunctionDom (ConvexProcess.indicatorBifunction A) = A.dom := by
  ext u
  -- The indicator slice is finite somewhere exactly when the fiber `A u` is nonempty.
  simp [eRealBifunctionDom, ConvexProcess.indicatorBifunction, ConvexProcess.dom,
    setValuedDom, indicatorEReal, Set.nonempty_def]

/-- Helper for Proposition 39.0.13: graph equality determines the underlying set-valued mapping of
convex processes. -/
lemma helperForProposition_39_0_13_toSetValued_eq_of_graph_eq {m n : ℕ}
    {A B : ConvexProcess m n}
    (hgraph : setValuedGraph A.toSetValued = setValuedGraph B.toSetValued) :
    A.toSetValued = B.toSetValued := by
  funext u
  ext x
  -- Test the graph equality at the point `(u, x)` to recover equality of the fibers.
  have hx := congrArg (fun S => (u, x) ∈ S) hgraph
  simpa [setValuedGraph] using hx

/-- Helper for Proposition 39.0.13: graph equality identifies convex processes. -/
lemma helperForProposition_39_0_13_eq_of_graph_eq {m n : ℕ} {A B : ConvexProcess m n}
    (hgraph : setValuedGraph A.toSetValued = setValuedGraph B.toSetValued) : A = B := by
  -- Once the underlying set-valued maps agree, proof irrelevance identifies the structures.
  cases A
  cases B
  cases helperForProposition_39_0_13_toSetValued_eq_of_graph_eq hgraph
  simp

/-- Helper for Proposition 39.0.13: a convex process is closed exactly when its graph is closed. -/
lemma helperForProposition_39_0_13_graphClosed_iff_processClosed {m n : ℕ}
    (A : ConvexProcess m n) :
    _root_.IsClosed (setValuedGraph A.toSetValued) ↔ A.IsClosed := by
  have hClGraph : setValuedGraph (A.cl).toSetValued = closure (setValuedGraph A.toSetValued) := by
    -- The closure process was chosen so that its graph is exactly the topological closure.
    exact Classical.choose_spec (ConvexProcess.exists_closureProcess A)
  constructor
  · intro hGraphClosed
    -- A closed graph equals its closure, so the closure process has the same graph as `A`.
    have hClosureEq : closure (setValuedGraph A.toSetValued) = setValuedGraph A.toSetValued := by
      exact hGraphClosed.closure_eq
    have hGraphAcl : setValuedGraph (A.cl).toSetValued = setValuedGraph A.toSetValued := by
      calc
        setValuedGraph (A.cl).toSetValued = closure (setValuedGraph A.toSetValued) :=
          hClGraph
        _ = setValuedGraph A.toSetValued := hClosureEq
    exact helperForProposition_39_0_13_eq_of_graph_eq hGraphAcl
  · intro hA
    -- If `A.cl = A`, then the graph agrees with its own closure and is therefore closed.
    have hGraphEq : setValuedGraph A.toSetValued = closure (setValuedGraph A.toSetValued) := by
      calc
        setValuedGraph A.toSetValued = setValuedGraph (A.cl).toSetValued := by
          exact congrArg setValuedGraph (congrArg ConvexProcess.toSetValued hA).symm
        _ = closure (setValuedGraph A.toSetValued) := hClGraph
    rw [hGraphEq]
    exact isClosed_closure

/-- Helper for Proposition 39.0.13: restricting the epigraph description to height `0` recovers
the graph of the convex process. -/
lemma helperForProposition_39_0_13_zeroHeightPreimage_eq_graph {m n : ℕ}
    (A : ConvexProcess m n) :
    ((fun p : (Fin m → ℝ) × (Fin n → ℝ) => (p, (0 : ℝ))) ⁻¹'
      {q : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ |
        q.1 ∈ setValuedGraph A.toSetValued ∧ 0 ≤ q.2}) =
      setValuedGraph A.toSetValued := by
  -- At height `0`, the nonnegativity condition is automatic, so only graph membership remains.
  ext p
  simp [setValuedGraph]

-- Proof sketch: Rewrite `F u x` as the indicator function of the graph of `A` on the product space
-- `(Fin m → ℝ) × (Fin n → ℝ)`. Use the characterization of convexity/properness/closedness of an
-- indicator function in terms of convexity/nonemptiness/closedness of the underlying set, and use
-- `A.zero_mem` to witness properness. The domain identity follows by unfolding the definitions:
-- `F u` is finite somewhere iff `A u` is nonempty.
/-- Proposition 39.0.13: Let `A` be a (supremum oriented) convex process from `ℝ^m` to `ℝ^n`, and
define its indicator bifunction `F` by `(F u)(x) = δ(x | A u)`. Then `F` is convex and proper,
`dom F = dom A`, and `F` is closed if and only if `A` is closed.

(If `A` is treated in infimum orientation, the corresponding bifunction is given by
`(F u)(x) = -δ(x | A u)`, i.e. `ConvexProcess.negIndicatorBifunction A`.) -/
theorem prop_39_0_13 {m n : ℕ} (A : ConvexProcess m n) :
    IsConvexEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
      ConvexProcess.indicatorBifunction A p.1 p.2) ∧
      IsProperEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        ConvexProcess.indicatorBifunction A p.1 p.2) ∧
      eRealBifunctionDom (ConvexProcess.indicatorBifunction A) = A.dom ∧
      (IsClosedEReal (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        ConvexProcess.indicatorBifunction A p.1 p.2) ↔ A.IsClosed) :=
  by
  constructor
  · -- Convexity comes from the convexity of the graph cone together with `0 ≤ t`.
    rw [IsConvexEReal, helperForProposition_39_0_13_indicatorEpigraph_eq]
    have hGraphConvex : Convex ℝ (setValuedGraph A.toSetValued) :=
      (helperForProposition_39_0_1_graphConvexCone_ofConvexProcess A).convex
    exact hGraphConvex.prod (convex_Ici (0 : ℝ))
  · constructor
    · -- Properness is immediate: the indicator never takes `⊥`, and it takes value `0` at `(0,0)`.
      refine ⟨?_, ?_⟩
      · intro p
        by_cases hp : p ∈ setValuedGraph A.toSetValued
        · simp [helperForProposition_39_0_13_indicatorOnGraph, indicatorEReal, hp]
        · simp [helperForProposition_39_0_13_indicatorOnGraph, indicatorEReal, hp]
      · refine ⟨((0 : Fin m → ℝ), (0 : Fin n → ℝ)), ?_⟩
        have hOriginValue : ConvexProcess.indicatorBifunction A 0 0 = (0 : EReal) := by
          -- The process axiom `0 ∈ A 0` makes the indicator vanish at the origin.
          simp [ConvexProcess.indicatorBifunction, indicatorEReal, A.zero_mem]
        change ConvexProcess.indicatorBifunction A 0 0 ≠ ⊤
        rw [hOriginValue]
        simp
    · constructor
      · -- The effective domain records exactly the nonempty fibers of the process.
        exact helperForProposition_39_0_13_dom_eq A
      · constructor
        · intro hClosedIndicator
          -- Pull the epigraph back along `p ↦ (p,0)` to recover closedness of the graph.
          rw [IsClosedEReal, helperForProposition_39_0_13_indicatorEpigraph_eq] at hClosedIndicator
          have hPreimageClosed :
              _root_.IsClosed
                ((fun p : (Fin m → ℝ) × (Fin n → ℝ) => (p, (0 : ℝ))) ⁻¹'
                  {q : ((Fin m → ℝ) × (Fin n → ℝ)) × ℝ |
                    q.1 ∈ setValuedGraph A.toSetValued ∧ 0 ≤ q.2}) := by
            exact hClosedIndicator.preimage (Continuous.prodMk continuous_id continuous_const)
          have hGraphClosed : _root_.IsClosed (setValuedGraph A.toSetValued) := by
            -- The zero-height pullback of the epigraph is exactly the graph itself.
            rw [helperForProposition_39_0_13_zeroHeightPreimage_eq_graph A] at hPreimageClosed
            exact hPreimageClosed
          exact (helperForProposition_39_0_13_graphClosed_iff_processClosed A).1 hGraphClosed
        · intro hAClosed
          -- Closedness of the graph upgrades to closedness of the indicator epigraph by products.
          rw [IsClosedEReal, helperForProposition_39_0_13_indicatorEpigraph_eq]
          have hGraphClosed : _root_.IsClosed (setValuedGraph A.toSetValued) :=
            (helperForProposition_39_0_13_graphClosed_iff_processClosed A).2 hAClosed
          have hIciClosed : _root_.IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
          have hProdClosed :
              _root_.IsClosed (Set.prod (setValuedGraph A.toSetValued) (Set.Ici (0 : ℝ))) :=
            hGraphClosed.prod hIciClosed
          simpa [Set.prod, Set.setOf_and] using hProdClosed

/-
  The book treats a convex process as either supremum oriented (via its indicator bifunction)
  or infimum oriented (via the negative indicator bifunction). In this section we record the
  adjoint corresponding to the supremum-oriented convention; for an infimum-oriented process one
  reverses the inequality and switches the orientation.
-/

namespace ConvexProcess

/-- A set-valued mapping `X ⇉ Y` together with a choice of orientation (supremum/infimum), used to
record whether the mapping is being treated via an indicator (supremum) or negative indicator
(infimum) convention. -/
structure OrientedSetValuedMap (X Y : Type*) where
  /-- The underlying set-valued mapping. -/
  toSetValued : X → Set Y
  /-- The chosen orientation. -/
  orientation : ConvexSetOrientation

/-- Definition 39.0.14: Let `A` be a supremum oriented convex process from `ℝ^m` to `ℝ^n`.
(In this development, `ConvexProcess` is the supremum-oriented convention of Definition 39.0.1.)
Its adjoint is the infimum oriented set-valued mapping `A* : (ℝ^n)* ⇉ (ℝ^m)*` defined by

`A* x* = {u* | ⟪u, u*⟫ ≥ ⟪x, x*⟫, ∀ x ∈ A u, ∀ u}`.

(For an infimum oriented `A`, the adjoint is defined analogously with the inequality reversed and
the orientation switched.) -/
def adjoint {m n : ℕ} (A : ConvexProcess m n) :
    OrientedSetValuedMap (Module.Dual ℝ (Fin n → ℝ)) (Module.Dual ℝ (Fin m → ℝ)) :=
  { toSetValued := fun xStar =>
      { uStar | ∀ u, ∀ x, x ∈ A.toSetValued u → uStar u ≥ xStar x }
    orientation := .infimum }

/-- Helper for Proposition 39.0.15: membership in the inverse adjoint fiber is exactly the
original adjoint inequality along the graph of `A`. -/
lemma helperForProposition_39_0_15_mem_setValuedInverse_adjoint {m n : ℕ}
    (A : ConvexProcess m n) (uStar : Module.Dual ℝ (Fin m → ℝ))
    (xStar : Module.Dual ℝ (Fin n → ℝ)) :
    xStar ∈ setValuedInverse (adjoint A).toSetValued uStar ↔
      ∀ u x, x ∈ A.toSetValued u → uStar u ≥ xStar x := by
  -- Unfold inverse membership so the claim becomes the defining predicate of `adjoint A`.
  simp [setValuedInverse, adjoint]

/-- Helper for Proposition 39.0.15: membership in the adjoint of the inverse process rewrites to
the same graph condition with the inequality reversed after swapping the graph coordinates back. -/
lemma helperForProposition_39_0_15_mem_adjoint_inverse {m n : ℕ}
    (A : ConvexProcess m n) (uStar : Module.Dual ℝ (Fin m → ℝ))
    (xStar : Module.Dual ℝ (Fin n → ℝ)) :
    xStar ∈ (adjoint A.inverse).toSetValued uStar ↔
      ∀ u x, x ∈ A.toSetValued u → xStar x ≥ uStar u := by
  constructor
  · intro hx
    -- Unfold the adjoint of the inverse, then rewrite inverse-process membership back to `x ∈ A u`.
    simp [adjoint] at hx
    intro u x hxu
    have hinv : u ∈ A.inverse.toSetValued x := by
      rw [helperForProposition_39_0_6_inverse_toSetValued A]
      exact hxu
    exact hx x u hinv
  · intro hx
    -- Repackage the same graph inequality as a membership statement for `adjoint A.inverse`.
    simp [adjoint]
    intro x u hux
    rw [helperForProposition_39_0_6_inverse_toSetValued A] at hux
    exact hx u x hux

/-- Helper for Proposition 39.0.15: the one-dimensional lower-set process from Example 39.0.3
with `B = id`, used to witness the sign mismatch in the inverse-adjoint identity. -/
noncomputable def helperForProposition_39_0_15_identityLowerProcess : ConvexProcess 1 1 :=
  Classical.choose (example_39_0_3
    (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))).1

/-- Helper for Proposition 39.0.15: the chosen process has fibers
`A u = {x | 0 ≤ u ∧ x ≤ u}`. -/
lemma helperForProposition_39_0_15_identityLowerProcess_toSetValued :
    helperForProposition_39_0_15_identityLowerProcess.toSetValued =
      linearLowerSetValued (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) := by
  -- Unpack the witness supplied by Example 39.0.3.
  exact Classical.choose_spec (example_39_0_3
    (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))).1

/-- Helper for Proposition 39.0.15: for the Example 39.0.3 lower-set process with `B = id`,
`x* = 0` lies in `(A*)⁻¹(u*)` for `u* = proj 0`, but not in `(A⁻¹)* (u*)`. -/
lemma helperForProposition_39_0_15_counterexample :
    let A := helperForProposition_39_0_15_identityLowerProcess
    let uStar : Module.Dual ℝ (Fin 1 → ℝ) := LinearMap.proj (0 : Fin 1)
    let xStar : Module.Dual ℝ (Fin 1 → ℝ) := 0
    xStar ∈ setValuedInverse (adjoint A).toSetValued uStar ∧
      xStar ∉ (adjoint (A.inverse)).toSetValued uStar := by
  dsimp
  constructor
  · -- Every graph point of the example process has a nonnegative input coordinate, so `u* u ≥ 0`.
    rw [helperForProposition_39_0_15_mem_setValuedInverse_adjoint]
    intro u x hx
    have hx' : 0 ≤ u ∧ x ≤
        ((LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) u) := by
      simpa [helperForProposition_39_0_15_identityLowerProcess_toSetValued,
        linearLowerSetValued] using hx
    have hu0 : 0 ≤ u 0 := hx'.1 0
    simpa using hu0
  · intro hmem
    -- The graph point `((1), 0)` belongs to `A`, but it would force the contradiction `0 ≥ 1`.
    rw [helperForProposition_39_0_15_mem_adjoint_inverse] at hmem
    let u : Fin 1 → ℝ := fun _ => 1
    let x : Fin 1 → ℝ := 0
    have hxmem : x ∈ helperForProposition_39_0_15_identityLowerProcess.toSetValued u := by
      have hx' : 0 ≤ u ∧ x ≤
          ((LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) u) := by
        constructor
        · intro i
          fin_cases i
          simp [u]
        · intro i
          fin_cases i
          simp [u, x]
      simpa [helperForProposition_39_0_15_identityLowerProcess_toSetValued,
        linearLowerSetValued, u, x] using hx'
    have hineq : (0 : Module.Dual ℝ (Fin 1 → ℝ)) x ≥ (LinearMap.proj (0 : Fin 1)) u :=
      hmem u x hxmem
    norm_num [u, x] at hineq

/-- Helper for Proposition 39.0.15: the Example 39.0.3 lower-set process makes the two candidate
inverse-adjoint set-valued maps genuinely different. -/
lemma helperForProposition_39_0_15_counterexample_separates_inverse_adjoint :
    let A := helperForProposition_39_0_15_identityLowerProcess
    setValuedInverse (adjoint A).toSetValued ≠ (adjoint A.inverse).toSetValued := by
  dsimp
  intro hEq
  -- Extract the witness point where the two fibers disagree.
  have hcounterexample := helperForProposition_39_0_15_counterexample
  dsimp at hcounterexample
  rcases hcounterexample with ⟨hmemInverseAdjoint, hnotMemAdjointInverse⟩
  -- Evaluate the claimed function equality at the offending dual vector.
  have hFiberEq :
      setValuedInverse (adjoint helperForProposition_39_0_15_identityLowerProcess).toSetValued
          (LinearMap.proj (0 : Fin 1)) =
        (adjoint helperForProposition_39_0_15_identityLowerProcess.inverse).toSetValued
          (LinearMap.proj (0 : Fin 1)) :=
    congrArg (fun F => F (LinearMap.proj (0 : Fin 1))) hEq
  exact hnotMemAdjointInverse (hFiberEq ▸ hmemInverseAdjoint)

/-- Helper for Proposition 39.0.15: the in-file Example 39.0.3 witness already violates the
claimed inverse-adjoint identity. -/
lemma helperForProposition_39_0_15_identityLowerProcess_inverse_adjoint_ne :
    setValuedInverse
        (adjoint helperForProposition_39_0_15_identityLowerProcess).toSetValued ≠
      (adjoint helperForProposition_39_0_15_identityLowerProcess.inverse).toSetValued := by
  -- Unfold the `let`-bound witness from the previous helper into the concrete process notation.
  simpa using helperForProposition_39_0_15_counterexample_separates_inverse_adjoint

/-- Helper for Proposition 39.0.15: under the current supremum-oriented `adjoint` convention, the
inverse-adjoint identity cannot hold for every convex process. -/
lemma helperForProposition_39_0_15_claim_fails_in_general :
    ¬ ∀ A : ConvexProcess 1 1,
      setValuedInverse (adjoint A).toSetValued = (adjoint A.inverse).toSetValued := by
  intro hAll
  -- Specialize the claimed universal identity to the explicit one-dimensional counterexample.
  exact helperForProposition_39_0_15_identityLowerProcess_inverse_adjoint_ne (hAll _)

-- Proof sketch: the linear-map specialization is proved directly from singleton fibers. For the
-- inverse-adjoint identity, the current `adjoint` definition keeps the inequality direction
-- `uStar u ≥ xStar x` after inverting the graph coordinates, whereas `adjoint (A⁻¹)` requires the
-- reversed inequality `xStar x ≥ uStar u`. The dedicated counterexample below shows that these
-- predicates do not agree in general, so the first conjunct cannot be completed without changing
-- the statement or the ambient adjoint convention.
/-- Partial formalization of Proposition 39.0.15 at the raw algebraic-dual level.

The full inverse-adjoint identity from Rockafellar requires tracking the orientation switch after
graph inversion. Under the raw `adjoint` convention used in this file, the first clause
`(A*)⁻¹ = (A⁻¹)*` is false in general, as witnessed by the preceding counterexample helpers.
The valid orientation-aware Euclidean-coordinate version is formalized later in
`prop_39_0_15_textbook` (built on the generic helper `prop_39_0_15_orientedVec`).

What remains valid already in the present setup is the linear-transformation clause: if `A` is
single-valued with fibers `{f u}`, then `A*` coincides with the usual algebraic adjoint
`LinearMap.dualMap`. -/
theorem prop_39_0_15_linearClause {m n : ℕ} (A : ConvexProcess m n) :
    ∀ (f : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ)),
      (∀ u, A.toSetValued u = ({f u} : Set (Fin n → ℝ))) →
        ∀ xStar,
          (adjoint A).toSetValued xStar =
            ({f.dualMap xStar} : Set (Module.Dual ℝ (Fin m → ℝ))) :=
  by
  intro f hA xStar
  ext uStar
  constructor
  · intro huStar
    -- On singleton fibers, the adjoint inequality first gives `uStar u ≥ xStar (f u)`.
    have hge : ∀ u, uStar u ≥ xStar (f u) := by
      intro u
      have hfu : f u ∈ A.toSetValued u := by
        simp [hA u]
      exact huStar u (f u) hfu
    -- Applying the same inequality to `-u` forces the reverse inequality.
    have hle : ∀ u, uStar u ≤ xStar (f u) := by
      intro u
      have hfneg : f (-u) ∈ A.toSetValued (-u) := by
        simp [hA (-u)]
      have hneg := huStar (-u) (f (-u)) hfneg
      have hneg' : -uStar u ≥ -(xStar (f u)) := by
        simpa using hneg
      linarith
    -- The two inequalities identify the dual functional with the usual algebraic adjoint.
    have heq : uStar = f.dualMap xStar := by
      exact DFunLike.ext _ _ (fun u => by
        rw [LinearMap.dualMap_apply]
        exact le_antisymm (hle u) (hge u))
    exact Set.mem_singleton_iff.mpr heq
  · intro huStar
    rcases Set.mem_singleton_iff.mp huStar with rfl
    intro u x hx
    -- Membership in a singleton fiber reduces the adjoint inequality to reflexivity.
    have hx' : x = f u := by
      simpa [hA u] using hx
    subst hx'
    simp

end ConvexProcess

/-- The graph of a set-valued mapping `A : X → Set Y`, as a subset of `X × Y`. -/
def setValuedGraph' {X Y : Type*} (A : X → Set Y) : Set (X × Y) :=
  { p | p.2 ∈ A p.1 }

/-- A set-valued mapping `A : X → Set Y` is a convex process if it is superadditive, positively
homogeneous (for positive scalars), and satisfies `0 ∈ A 0`. -/
def IsConvexProcessMap {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    (A : X → Set Y) : Prop :=
  (∀ u₁ u₂, A u₁ + A u₂ ⊆ A (u₁ + u₂)) ∧
    (∀ u (r : ℝ), 0 < r → A (r • u) = r • A u) ∧
    ((0 : Y) ∈ A 0)

/-- A set-valued mapping is closed if its graph is a closed set in the product topology. -/
def IsClosedSetValuedMap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : X → Set Y) : Prop :=
  _root_.IsClosed (setValuedGraph' A)

/-- The indicator bifunction associated to a set-valued mapping `A : U → Set X`, i.e.
`(u,x) ↦ δ(x | A u)` valued in `EReal`. -/
noncomputable def indicatorBifunctionSetValued {U X : Type*} (A : U → Set X) : U → X → EReal :=
  fun u x => indicatorEReal (A u) x

/-- The adjoint of a set-valued mapping `A : ℝ^m ⇉ ℝ^n` in the book's Euclidean convention,
defined by

`A* x* = {u* | finDot u u* ≥ finDot x x*, ∀ u, ∀ x ∈ A u }`. -/
def setValuedAdjointVec {m n : ℕ} (A : (Fin m → ℝ) → Set (Fin n → ℝ)) :
    (Fin n → ℝ) → Set (Fin m → ℝ) :=
  fun xStar =>
    { uStar | ∀ u, ∀ x, x ∈ A u → finDot u uStar ≥ finDot x xStar }

end Section39
end Chap08
