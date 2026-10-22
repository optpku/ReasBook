/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part1

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

section Chap08
section Section39

/-- The recession cone of a set `S` in a real vector space: the set of directions `d` such that
`x + t • d ∈ S` for all `x ∈ S` and all real `t ≥ 0`. -/
def recessionCone {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V) : Set V :=
  { d | ∀ ⦃x⦄, x ∈ S → ∀ t : ℝ, 0 ≤ t → x + t • d ∈ S }

namespace ConvexProcess

-- Proof sketch: Use Proposition 39.0.2(iv), which asserts that the inverse set-valued mapping
-- `A⁻¹` is again a convex process.
/-- Existence of a convex process whose underlying set-valued mapping is the inverse mapping
`A⁻¹ y = {u | y ∈ A u}`. -/
theorem exists_inverseProcess {m n : ℕ} (A : ConvexProcess m n) :
    ∃ B : ConvexProcess n m, B.toSetValued = A.inverseMap :=
  by
  -- Proposition 39.0.2(iv) already packages the inverse mapping as a convex process.
  rcases convexProcess_prop_39_0_2 A with ⟨_, _, _, hInverse, _⟩
  exact hInverse.1

/-- The inverse convex process `A⁻¹` associated to a convex process `A`, viewed again as a convex
process. -/
noncomputable def inverse {m n : ℕ} (A : ConvexProcess m n) : ConvexProcess n m :=
  Classical.choose (exists_inverseProcess A)

/-- Helper for Proposition 39.0.6: unpack the chosen inverse convex process back to the inverse
set-valued mapping. -/
lemma helperForProposition_39_0_6_inverse_toSetValued {m n : ℕ} (A : ConvexProcess m n) :
    (A.inverse).toSetValued = A.inverseMap := by
  -- The inverse process was defined by choice, so its underlying mapping is the chosen witness.
  exact Classical.choose_spec (exists_inverseProcess A)

/-- Helper for Proposition 39.0.6: the graph of `A.cl` is exactly the closure of the graph of
`A`. -/
lemma helperForProposition_39_0_6_cl_graph {m n : ℕ} (A : ConvexProcess m n) :
    setValuedGraph (A.cl).toSetValued = closure (setValuedGraph A.toSetValued) := by
  -- This is the defining property of the closure process chosen in Definition 39.0.5.
  exact Classical.choose_spec (exists_closureProcess A)

/-- Helper for Proposition 39.0.6: if `A` is closed, then its graph agrees with its own closure. -/
lemma helperForProposition_39_0_6_cl_graph_eq_self_of_isClosed {m n : ℕ}
    (A : ConvexProcess m n) (hA : A.IsClosed) :
    setValuedGraph A.toSetValued = closure (setValuedGraph A.toSetValued) := by
  -- Closedness gives `A.cl = A`, and then the closure-graph formula rewrites to a fixed-point
  -- identity for the graph of `A`.
  have hToSetValued : (A.cl).toSetValued = A.toSetValued := by
    exact congrArg ConvexProcess.toSetValued hA
  have hGraphRewrite :
      setValuedGraph (A.cl).toSetValued = setValuedGraph A.toSetValued := by
    exact congrArg setValuedGraph hToSetValued
  calc
    setValuedGraph A.toSetValued = setValuedGraph (A.cl).toSetValued := by
      exact hGraphRewrite.symm
    _ = closure (setValuedGraph A.toSetValued) :=
      helperForProposition_39_0_6_cl_graph A

/-- Helper for Proposition 39.0.6: taking inverse swaps graph coordinates, and coordinate swap
commutes with topological closure. -/
lemma helperForProposition_39_0_6_inverse_graph_swap_and_closure {m n : ℕ}
    (A : ConvexProcess m n) :
    setValuedGraph A.inverseMap = Prod.swap '' setValuedGraph A.toSetValued ∧
      closure (Prod.swap '' setValuedGraph A.toSetValued) =
        Prod.swap '' closure (setValuedGraph A.toSetValued) := by
  constructor
  · -- Unfold the inverse graph: membership is exactly the original graph with coordinates swapped.
    ext p
    rcases p with ⟨y, u⟩
    simp [ConvexProcess.inverseMap, setValuedInverse, setValuedGraph]
  · -- The coordinate-swap homeomorphism carries closures to closures of images.
    simpa [Prod.swap] using
      (Homeomorph.image_closure (Homeomorph.prodComm (Fin m → ℝ) (Fin n → ℝ))
        (setValuedGraph A.toSetValued)).symm

/-- Helper for Proposition 39.0.6: if the process is closed, then its graph is closed and every
fiber is a closed set. -/
lemma helperForProposition_39_0_6_graphClosed_and_fiberClosed {m n : ℕ}
    (A : ConvexProcess m n) (hA : A.IsClosed) :
    _root_.IsClosed (setValuedGraph A.toSetValued) ∧ ∀ u, _root_.IsClosed (A.toSetValued u) := by
  have hclosureEq : setValuedGraph A.toSetValued = closure (setValuedGraph A.toSetValued) := by
    -- Closedness means `A.cl = A`, so the closure graph formula collapses to a fixed-point
    -- identity.
    exact helperForProposition_39_0_6_cl_graph_eq_self_of_isClosed A hA
  have hGraphClosed : _root_.IsClosed (setValuedGraph A.toSetValued) := by
    -- A set equal to its closure is closed.
    rw [hclosureEq]
    exact isClosed_closure
  refine ⟨hGraphClosed, ?_⟩
  intro u
  have hEmbeddingContinuous : Continuous fun x : Fin n → ℝ => (u, x) := by
    -- The fiber over `u` is cut out by the continuous embedding `x ↦ (u, x)`.
    simpa using (Continuous.prodMk continuous_const continuous_id)
  have hpreimage :
      _root_.IsClosed ((fun x : Fin n → ℝ => (u, x)) ⁻¹' setValuedGraph A.toSetValued) :=
    hGraphClosed.preimage hEmbeddingContinuous
  have hfiber :
      (fun x : Fin n → ℝ => (u, x)) ⁻¹' setValuedGraph A.toSetValued = A.toSetValued u := by
    -- Unfold the graph definition to identify the preimage with the fiber.
    ext x
    simp [setValuedGraph]
  simpa [hfiber] using hpreimage

/-- Helper for Proposition 39.0.6: the scaled iterate used in the limit argument can be rewritten
as a fixed vector plus a vanishing correction term. -/
lemma helperForProposition_39_0_6_scaledIterate_rewrite {n : ℕ} {x d : Fin n → ℝ} (k : ℕ) :
    ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • (x + (k : ℝ) • d) =
      d + ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • (x - d) := by
  -- Coordinatewise, this is the scalar identity
  -- `(k+1)⁻¹ (x_i + k d_i) = d_i + (k+1)⁻¹ (x_i - d_i)`.
  have hk : (((k : ℝ) + 1) : ℝ) ≠ 0 := by
    positivity
  ext i
  change (((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) * (x i + (k : ℝ) * d i)) =
    d i + ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) * (x i - d i)
  field_simp [hk]
  ring

/-- Helper for Proposition 39.0.6: every zero-fiber direction translates each fiber into itself,
hence belongs to every recession cone. -/
lemma helperForProposition_39_0_6_zeroFiber_subset_recessionCone {m n : ℕ}
    (A : ConvexProcess m n) (u : Fin m → ℝ) :
    A.toSetValued 0 ⊆ recessionCone (A.toSetValued u) := by
  rcases convexProcess_prop_39_0_2 A with ⟨_, hZeroFiber, _, _, _⟩
  rcases hZeroFiber with ⟨_, _, hStableDirections⟩
  intro d hd x hx t ht
  by_cases ht0 : t = 0
  · -- At `t = 0`, the recession-cone condition is tautological.
    simpa [ht0] using hx
  · have htNe : t ≠ 0 := ht0
    have hZeroNe : 0 ≠ t := by
      simpa [eq_comm] using htNe
    have htPos : 0 < t := by
      exact lt_of_le_of_ne ht hZeroNe
    have hScaledDirection : t • d ∈ A.toSetValued 0 :=
      helperForProposition_39_0_2_zeroFiber_smul_mem A htPos hd
    rw [hStableDirections] at hScaledDirection
    have htMemSingleton : t • d ∈ ({t • d} : Set (Fin n → ℝ)) := by
      simp
    have hsum : x + t • d ∈ A.toSetValued u + ({t • d} : Set (Fin n → ℝ)) := by
      -- Put `x` and the translated zero-fiber direction into the Minkowski-sum description.
      exact Set.mem_add.2 ⟨x, hx, t • d, htMemSingleton, rfl⟩
    exact hScaledDirection u hsum

/-- Helper for Proposition 39.0.6: for a closed convex process, every nonempty fiber has recession
cone equal to the zero fiber. -/
lemma helperForProposition_39_0_6_recessionCone_eq_zeroFiber {m n : ℕ}
    (A : ConvexProcess m n) (hA : A.IsClosed) :
    ∀ u, u ∈ A.dom → recessionCone (A.toSetValued u) = A.toSetValued 0 := by
  have hGraphClosed := (helperForProposition_39_0_6_graphClosed_and_fiberClosed A hA).1
  have hReciprocal :
      Filter.Tendsto (fun k : ℕ => ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ))
        Filter.atTop (nhds (0 : ℝ)) := by
    -- The reciprocal factor vanishes along the natural numbers.
    exact tendsto_inv_atTop_zero.comp
      (Filter.Tendsto.atTop_add tendsto_natCast_atTop_atTop tendsto_const_nhds)
  intro u hu
  ext d
  constructor
  · intro hd
    change (A.toSetValued u).Nonempty at hu
    rcases hu with ⟨x, hx⟩
    have hIterates : ∀ k : ℕ, x + (k : ℝ) • d ∈ A.toSetValued u := by
      -- A recession direction keeps the fiber invariant under every nonnegative multiple.
      intro k
      have hkNonneg : 0 ≤ (k : ℝ) := by
        positivity
      exact hd hx (k : ℝ) hkNonneg
    have hGraphSequence :
        ∀ k : ℕ,
          ((((k : ℝ) + 1) : ℝ)⁻¹ • u,
            d + ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • (x - d)) ∈ setValuedGraph A.toSetValued := by
      intro k
      have hkPlusOnePos : 0 < (((k : ℝ) + 1) : ℝ) := by
        positivity
      have hkInvPos : 0 < ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) := by
        positivity
      have hScaled :
          ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • (x + (k : ℝ) • d) ∈
            A.toSetValued ((((k : ℝ) + 1) : ℝ)⁻¹ • u) := by
        have hmem :
            ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • (x + (k : ℝ) • d) ∈
              ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • A.toSetValued u := by
          -- Scale the fiber point `x + k d` into the dilated fiber.
          exact Set.mem_smul_set.2 ⟨x + (k : ℝ) • d, hIterates k, rfl⟩
        simpa [A.map_smul_pos u ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) hkInvPos] using hmem
      have hRewrite :=
        helperForProposition_39_0_6_scaledIterate_rewrite (x := x) (d := d) k
      simpa [setValuedGraph, hRewrite] using hScaled
    have hFirstCoord :
        Filter.Tendsto (fun k : ℕ => ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • u)
          Filter.atTop (nhds (0 : Fin m → ℝ)) := by
      -- The scaling factor tends to `0`, so the first coordinates collapse to the origin.
      rw [tendsto_pi_nhds]
      intro i
      simpa using hReciprocal.mul tendsto_const_nhds
    have hSecondCoord :
        Filter.Tendsto
          (fun k : ℕ => d + ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • (x - d))
          Filter.atTop (nhds d) := by
      -- The correction term tends to `0`, so the second coordinates converge to `d`.
      rw [tendsto_pi_nhds]
      intro i
      have hMul :
          Filter.Tendsto
            (fun k : ℕ => ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) * (x i - d i))
            Filter.atTop (nhds (0 * (x i - d i))) := by
        simpa using hReciprocal.mul tendsto_const_nhds
      simpa using Filter.Tendsto.const_add (d i) hMul
    have hPairTendsto :
        Filter.Tendsto
          (fun k : ℕ =>
            ((((k : ℝ) + 1) : ℝ)⁻¹ • u,
              d + ((((k : ℝ) + 1) : ℝ)⁻¹ : ℝ) • (x - d)))
          Filter.atTop (nhds ((0 : Fin m → ℝ), d)) := by
      -- Combine the coordinate limits into a limit in the graph ambient space.
      simpa using Filter.Tendsto.prodMk_nhds hFirstCoord hSecondCoord
    have hLimitPoint : ((0 : Fin m → ℝ), d) ∈ setValuedGraph A.toSetValued := by
      -- Closedness of the graph forces the limit point to remain on the graph.
      exact IsClosed.mem_of_tendsto hGraphClosed hPairTendsto
        (Filter.Eventually.of_forall hGraphSequence)
    simpa [setValuedGraph] using hLimitPoint
  · -- The opposite inclusion is the translation-invariance characterization of the zero fiber.
    intro hd0
    exact helperForProposition_39_0_6_zeroFiber_subset_recessionCone A u hd0

-- Proof sketch: For the first claim, pass to graphs and use that taking inverse corresponds to
-- swapping coordinates in `(u, x)`, which commutes with topological closure. For the second claim,
-- use that a closed graph has closed fibers; then compute the recession cone of any fiber using the
-- convex-process axioms, showing it is constant and equals `A 0`.
/-- Proposition 39.0.6: For any convex process `A`, `cl (A⁻¹) = (cl A)⁻¹`. If `A` is closed, then
each value set `A u` (for `u ∈ dom A`) is closed, and all such sets have the same recession cone,
namely `A 0`. -/
theorem prop_39_0_6 {m n : ℕ} (A : ConvexProcess m n) :
    (A.inverse.cl).toSetValued = ((A.cl).inverse).toSetValued ∧
      (A.IsClosed →
        (∀ u, u ∈ A.dom → _root_.IsClosed (A.toSetValued u)) ∧
          (∀ u, u ∈ A.dom → recessionCone (A.toSetValued u) = A.toSetValued 0)) :=
  by
  constructor
  · have hSwapA := helperForProposition_39_0_6_inverse_graph_swap_and_closure A
    have hSwapAcl := helperForProposition_39_0_6_inverse_graph_swap_and_closure (A.cl)
    ext y u
    have hGraphEq :
        setValuedGraph (A.inverse.cl).toSetValued =
          setValuedGraph ((A.cl).inverse).toSetValued := by
      -- Move both sides to graph level, where inverse becomes coordinate swap and closure commutes
      -- with that swap.
      calc
        setValuedGraph (A.inverse.cl).toSetValued
            = closure (setValuedGraph (A.inverse).toSetValued) :=
              helperForProposition_39_0_6_cl_graph (A.inverse)
        _ = closure (Prod.swap '' setValuedGraph A.toSetValued) := by
          rw [helperForProposition_39_0_6_inverse_toSetValued A, hSwapA.1]
        _ = Prod.swap '' closure (setValuedGraph A.toSetValued) := hSwapA.2
        _ = Prod.swap '' setValuedGraph (A.cl).toSetValued := by
          rw [helperForProposition_39_0_6_cl_graph A]
        _ = setValuedGraph (A.cl).inverseMap := by
          rw [hSwapAcl.1]
        _ = setValuedGraph ((A.cl).inverse).toSetValued := by
          rw [helperForProposition_39_0_6_inverse_toSetValued (A.cl)]
    constructor
    · intro hy
      -- Translate fiber membership into graph membership and apply the graph equality.
      have hmem : (y, u) ∈ setValuedGraph (A.inverse.cl).toSetValued := by
        simpa [setValuedGraph] using hy
      rw [hGraphEq] at hmem
      simpa [setValuedGraph] using hmem
    · intro hy
      -- The reverse implication is the same graph-level argument in the opposite direction.
      have hmem : (y, u) ∈ setValuedGraph ((A.cl).inverse).toSetValued := by
        simpa [setValuedGraph] using hy
      rw [← hGraphEq] at hmem
      simpa [setValuedGraph] using hmem
  · intro hA
    constructor
    · intro u hu
      -- Closedness of the graph gives closedness of each fiber by a continuous preimage argument.
      exact (helperForProposition_39_0_6_graphClosed_and_fiberClosed A hA).2 u
    · -- The recession cone computation is packaged in the dedicated helper lemma.
      exact helperForProposition_39_0_6_recessionCone_eq_zeroFiber A hA

/-- Scalar multiplication of a convex process at the level of its underlying set-valued map:
`(λA) u := λ • (A u)`. -/
def smulSetValued {m n : ℕ} (r : ℝ) (A : ConvexProcess m n) :
    (Fin m → ℝ) → Set (Fin n → ℝ) :=
  fun u => r • A.toSetValued u

/-- Minkowski sum of two convex processes at the level of their underlying set-valued maps:
`(A+B) u := A u + B u`. -/
def addSetValued {m n : ℕ} (A B : ConvexProcess m n) :
    (Fin m → ℝ) → Set (Fin n → ℝ) :=
  fun u => A.toSetValued u + B.toSetValued u

/-- Helper for Proposition 39.0.7: pointwise scalar multiplication distributes over Minkowski
sum of sets. -/
lemma helperForProposition_39_0_7_add_smul_distrib {n : ℕ} (s : ℝ)
    (S T : Set (Fin n → ℝ)) :
    s • (S + T) = s • S + s • T := by
  -- Unpack membership in the scaled sum and distribute the scalar over the chosen decomposition.
  ext x
  constructor
  · intro hx
    rcases Set.mem_smul_set.1 hx with ⟨y, hy, rfl⟩
    rcases Set.mem_add.1 hy with ⟨u, hu, v, hv, rfl⟩
    exact Set.mem_add.2
      ⟨s • u, Set.mem_smul_set.2 ⟨u, hu, rfl⟩,
        s • v, Set.mem_smul_set.2 ⟨v, hv, rfl⟩, by rw [smul_add]⟩
  · intro hx
    rcases Set.mem_add.1 hx with ⟨u, hu, v, hv, hEq⟩
    rcases Set.mem_smul_set.1 hu with ⟨u', hu', rfl⟩
    rcases Set.mem_smul_set.1 hv with ⟨v', hv', rfl⟩
    refine Set.mem_smul_set.2 ?_
    refine ⟨u' + v', Set.mem_add.2 ?_, ?_⟩
    · exact ⟨u', hu', v', hv', rfl⟩
    · simpa [smul_add] using hEq

/-- Helper for Proposition 39.0.7: scaling every value set of a convex process again produces a
convex process. -/
lemma helperForProposition_39_0_7_exists_smulProcess {m n : ℕ}
    (A : ConvexProcess m n) (r : ℝ) :
    ∃ cp : ConvexProcess m n, cp.toSetValued = smulSetValued r A := by
  have hAdd :
      ∀ u₁ u₂, smulSetValued r A u₁ + smulSetValued r A u₂ ⊆ smulSetValued r A (u₁ + u₂) := by
    intro u₁ u₂ x hx
    -- Decompose the two scaled witnesses and then reassemble them after using superadditivity of
    -- the original process.
    rcases Set.mem_add.1 hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    rcases Set.mem_smul_set.1 hx₁ with ⟨y₁, hy₁, rfl⟩
    rcases Set.mem_smul_set.1 hx₂ with ⟨y₂, hy₂, rfl⟩
    refine Set.mem_smul_set.2 ?_
    refine ⟨y₁ + y₂, ?_, by rw [smul_add]⟩
    exact A.map_add_superset u₁ u₂ (Set.mem_add.2 ⟨y₁, hy₁, y₂, hy₂, rfl⟩)
  have hSmul :
      ∀ u (s : ℝ), 0 < s → smulSetValued r A (s • u) = s • smulSetValued r A u := by
    intro u s hs
    -- First rewrite the fiber over `s • u` using positive homogeneity of `A`, then commute the
    -- two scalar actions on the set by unpacking pointwise membership.
    rw [smulSetValued, A.map_smul_pos u s hs]
    ext x
    constructor
    · intro hx
      rcases Set.mem_smul_set.1 hx with ⟨y, hy, rfl⟩
      rcases Set.mem_smul_set.1 hy with ⟨z, hz, rfl⟩
      refine Set.mem_smul_set.2 ?_
      refine ⟨r • z, Set.mem_smul_set.2 ⟨z, hz, rfl⟩, ?_⟩
      rw [smul_smul, smul_smul, mul_comm]
    · intro hx
      rcases Set.mem_smul_set.1 hx with ⟨y, hy, rfl⟩
      rcases Set.mem_smul_set.1 hy with ⟨z, hz, rfl⟩
      refine Set.mem_smul_set.2 ?_
      refine ⟨s • z, Set.mem_smul_set.2 ⟨z, hz, rfl⟩, ?_⟩
      rw [smul_smul, smul_smul, mul_comm]
  have hZero : (0 : Fin n → ℝ) ∈ smulSetValued r A (0 : Fin m → ℝ) := by
    -- The origin remains in the zero fiber after scaling because `r • 0 = 0`.
    exact Set.mem_smul_set.2 ⟨0, A.zero_mem, by simp⟩
  -- Package the three verified axioms into the required convex-process witness.
  refine ⟨{
    toSetValued := smulSetValued r A
    map_add_superset := hAdd
    map_smul_pos := hSmul
    zero_mem := hZero
  }, rfl⟩

/-- Helper for Proposition 39.0.7: Minkowski sum of the value sets of two convex processes again
produces a convex process. -/
lemma helperForProposition_39_0_7_exists_addProcess {m n : ℕ}
    (A B : ConvexProcess m n) :
    ∃ cp : ConvexProcess m n, cp.toSetValued = addSetValued A B := by
  have hAdd :
      ∀ u₁ u₂, addSetValued A B u₁ + addSetValued A B u₂ ⊆ addSetValued A B (u₁ + u₂) := by
    intro u₁ u₂ x hx
    -- Split the outer Minkowski sum, then split each inner Minkowski-sum witness and regroup the
    -- `A`-terms and `B`-terms separately.
    rcases Set.mem_add.1 hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    rcases Set.mem_add.1 hx₁ with ⟨a₁, ha₁, b₁, hb₁, rfl⟩
    rcases Set.mem_add.1 hx₂ with ⟨a₂, ha₂, b₂, hb₂, rfl⟩
    have ha :
        a₁ + a₂ ∈ A.toSetValued (u₁ + u₂) := by
      exact A.map_add_superset u₁ u₂ (Set.mem_add.2 ⟨a₁, ha₁, a₂, ha₂, rfl⟩)
    have hb :
        b₁ + b₂ ∈ B.toSetValued (u₁ + u₂) := by
      exact B.map_add_superset u₁ u₂ (Set.mem_add.2 ⟨b₁, hb₁, b₂, hb₂, rfl⟩)
    refine Set.mem_add.2 ⟨a₁ + a₂, ha, b₁ + b₂, hb, ?_⟩
    abel
  have hSmul :
      ∀ u (s : ℝ), 0 < s → addSetValued A B (s • u) = s • addSetValued A B u := by
    intro u s hs
    -- Rewrite both fibers using positive homogeneity and then use distributivity of pointwise
    -- scalar multiplication over Minkowski sums.
    calc
      addSetValued A B (s • u)
          = s • A.toSetValued u + s • B.toSetValued u := by
              rw [addSetValued, A.map_smul_pos u s hs, B.map_smul_pos u s hs]
      _ = s • addSetValued A B u := by
            rw [addSetValued, helperForProposition_39_0_7_add_smul_distrib]
  have hZero : (0 : Fin n → ℝ) ∈ addSetValued A B (0 : Fin m → ℝ) := by
    -- Use the two zero-fiber witnesses and the canonical decomposition `0 = 0 + 0`.
    exact Set.mem_add.2 ⟨0, A.zero_mem, 0, B.zero_mem, by simp⟩
  -- Package the verified axioms for the summed mapping.
  refine ⟨{
    toSetValued := addSetValued A B
    map_add_superset := hAdd
    map_smul_pos := hSmul
    zero_mem := hZero
  }, rfl⟩

/-- Helper for Proposition 39.0.7: the domain of the Minkowski sum of two convex processes is the
intersection of their domains. -/
lemma helperForProposition_39_0_7_dom_addSetValued {m n : ℕ}
    (A B : ConvexProcess m n) :
    setValuedDom (addSetValued A B) = A.dom ∩ B.dom := by
  -- A Minkowski sum fiber is nonempty exactly when both constituent fibers are nonempty.
  ext u
  constructor
  · intro hu
    change (addSetValued A B u).Nonempty at hu
    have hPair : (A.toSetValued u).Nonempty ∧ (B.toSetValued u).Nonempty := by
      rcases hu with ⟨x, hx⟩
      rcases Set.mem_add.1 hx with ⟨a, ha, b, hb, rfl⟩
      exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    simpa [ConvexProcess.dom, setValuedDom, Set.mem_inter_iff] using hPair
  · intro hu
    have hPair : (A.toSetValued u).Nonempty ∧ (B.toSetValued u).Nonempty := by
      simpa [ConvexProcess.dom, setValuedDom, Set.mem_inter_iff] using hu
    rcases hPair with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    change (addSetValued A B u).Nonempty
    exact ⟨a + b, Set.mem_add.2 ⟨a, ha, b, hb, rfl⟩⟩

-- Proof sketch: For `λA`, verify axioms (a),(b),(c) for the set-valued mapping
-- `u ↦ λ • (A u)` using distributivity/associativity of pointwise set addition and scalar
-- multiplication, together with the corresponding axioms for `A`. For `A+B`, similarly verify the
-- axioms for `u ↦ A u + B u`. For the domain identity, use that a Minkowski sum of two sets is
-- nonempty iff both sets are nonempty.
/-- Proposition 39.0.7: For `λ ∈ ℝ` define `(λA) u := λ • (A u)`. For convex processes `A, B`
define `(A+B) u := A u + B u` (Minkowski sum). Then `λA` and `A+B` are convex processes and
`dom (A+B) = dom A ∩ dom B`. -/
theorem prop_39_0_7 {m n : ℕ} (A B : ConvexProcess m n) (r : ℝ) :
    (∃ cp : ConvexProcess m n, cp.toSetValued = smulSetValued r A) ∧
      (∃ cp : ConvexProcess m n, cp.toSetValued = addSetValued A B) ∧
      setValuedDom (addSetValued A B) = A.dom ∩ B.dom :=
  by
  -- Assemble the two convex-process witnesses and the domain identity from the dedicated helpers.
  refine ⟨helperForProposition_39_0_7_exists_smulProcess A r, ?_, ?_⟩
  · exact helperForProposition_39_0_7_exists_addProcess A B
  · exact helperForProposition_39_0_7_dom_addSetValued A B

/-- The image of a set `C ⊆ ℝ^m` under a convex process `A : ℝ^m ⇉ ℝ^n`, defined as the union
`⋃ u ∈ C, A u`. -/
def image {m n : ℕ} (A : ConvexProcess m n) (C : Set (Fin m → ℝ)) : Set (Fin n → ℝ) :=
  ⋃ u ∈ C, A.toSetValued u

/-- Helper for Proposition 39.0.8: membership in `A.image C` is equivalent to exhibiting a base
point `u ∈ C` together with membership in the corresponding fiber `A u`. -/
lemma helperForProposition_39_0_8_mem_image_iff {m n : ℕ} (A : ConvexProcess m n)
    (C : Set (Fin m → ℝ)) (x : Fin n → ℝ) :
    x ∈ A.image C ↔ ∃ u, u ∈ C ∧ x ∈ A.toSetValued u := by
  -- Unfold the double union so image-membership becomes an explicit witness statement.
  simp [ConvexProcess.image]

/-- Helper for Proposition 39.0.8: convex combinations of points in two fibers land in the fiber
over the corresponding convex combination of the base points. -/
lemma helperForProposition_39_0_8_weighted_mem_targetFiber {m n : ℕ} (A : ConvexProcess m n)
    {u₁ u₂ : Fin m → ℝ} {x₁ x₂ : Fin n → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx₁ : x₁ ∈ A.toSetValued u₁) (hx₂ : x₂ ∈ A.toSetValued u₂) :
    a • x₁ + b • x₂ ∈ A.toSetValued (a • u₁ + b • u₂) := by
  by_cases ha_zero : a = 0
  · -- At the left endpoint, the convex combination reduces to the second fiber witness.
    have hb_one : b = 1 := by
      linarith
    simpa [ha_zero, hb_one] using hx₂
  · by_cases hb_zero : b = 0
    · -- At the right endpoint, the convex combination reduces to the first fiber witness.
      have ha_one : a = 1 := by
        linarith
      simpa [hb_zero, ha_one] using hx₁
    · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha_zero)
      have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_zero)
      -- Positive homogeneity moves each witness into the correspondingly scaled fiber.
      have hx₁_scaled : a • x₁ ∈ A.toSetValued (a • u₁) := by
        have hx₁_mem : a • x₁ ∈ a • A.toSetValued u₁ :=
          Set.mem_smul_set.2 ⟨x₁, hx₁, rfl⟩
        simpa [A.map_smul_pos u₁ a ha_pos] using hx₁_mem
      have hx₂_scaled : b • x₂ ∈ A.toSetValued (b • u₂) := by
        have hx₂_mem : b • x₂ ∈ b • A.toSetValued u₂ :=
          Set.mem_smul_set.2 ⟨x₂, hx₂, rfl⟩
        simpa [A.map_smul_pos u₂ b hb_pos] using hx₂_mem
      -- Superadditivity combines the two scaled fibers into the target fiber.
      have hsum :
          a • x₁ + b • x₂ ∈ A.toSetValued (a • u₁) + A.toSetValued (b • u₂) :=
        Set.mem_add.2 ⟨a • x₁, hx₁_scaled, b • x₂, hx₂_scaled, rfl⟩
      exact A.map_add_superset (a • u₁) (b • u₂) hsum

/-- Helper for Proposition 39.0.8: if two points lie in the image `A C`, then every convex
combination of them also lies in `A C`. -/
lemma helperForProposition_39_0_8_combo_mem_image {m n : ℕ} (C : Set (Fin m → ℝ))
    (hC : Convex ℝ C) (A : ConvexProcess m n)
    {x₁ x₂ : Fin n → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx₁ : x₁ ∈ A.image C) (hx₂ : x₂ ∈ A.image C) :
    a • x₁ + b • x₂ ∈ A.image C := by
  -- Unpack the two image witnesses into points of `C` and corresponding fiber memberships.
  rw [helperForProposition_39_0_8_mem_image_iff] at hx₁ hx₂
  rcases hx₁ with ⟨u₁, hu₁, hx₁⟩
  rcases hx₂ with ⟨u₂, hu₂, hx₂⟩
  -- Convexity of `C` supplies the base point for the combined fiber.
  have hu_combo : a • u₁ + b • u₂ ∈ C := hC hu₁ hu₂ ha hb hab
  -- The convex-process axioms produce the corresponding fiber membership.
  have hx_combo :
      a • x₁ + b • x₂ ∈ A.toSetValued (a • u₁ + b • u₂) :=
    helperForProposition_39_0_8_weighted_mem_targetFiber A ha hb hab hx₁ hx₂
  -- Repackage the combined witness back into image-membership.
  rw [helperForProposition_39_0_8_mem_image_iff]
  exact ⟨a • u₁ + b • u₂, hu_combo, hx_combo⟩

-- Proof sketch: Let `x₁ ∈ A C` and `x₂ ∈ A C`; pick `u₁,u₂ ∈ C` with `xᵢ ∈ A uᵢ`. For `t ∈ [0,1]`,
-- use convexity of `C` to get `u := t • u₁ + (1-t) • u₂ ∈ C`. Then use the convex-process axioms
-- (superadditivity and positive homogeneity, plus convexity of each fiber `A u` from Proposition
-- 39.0.2(i)) to show `t • x₁ + (1-t) • x₂ ∈ A u ⊆ A C`.
/-- Proposition 39.0.8: Let `C ⊆ ℝ^m` be convex and `A` a convex process. Define
`A C := ⋃ u ∈ C, A u`. Then `A C` is convex. -/
theorem prop_39_0_8 {m n : ℕ} (C : Set (Fin m → ℝ)) (hC : Convex ℝ C) (A : ConvexProcess m n) :
    Convex ℝ (A.image C) :=
  by
  -- Use the standard convexity criterion with two image points and coefficients summing to `1`.
  rw [convex_iff_add_mem]
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  -- The dedicated image-combination helper packages the witness extraction and fiber computation.
  exact helperForProposition_39_0_8_combo_mem_image C hC A ha hb hab hx₁ hx₂

/-- The epigraph of an extended-real-valued function `f : X → WithTop ℝ`, viewed as a subset of
`X × ℝ`. -/
def withTopEpigraph {X : Type*} (f : X → WithTop ℝ) : Set (X × ℝ) :=
  { p | f p.1 ≤ (p.2 : WithTop ℝ) }

/-- Convexity of an extended-real-valued function `f : X → WithTop ℝ`, defined as convexity of its
epigraph in `X × ℝ`. -/
def IsConvexWithTop {X : Type*} [AddCommGroup X] [Module ℝ X] (f : X → WithTop ℝ) : Prop :=
  Convex ℝ (withTopEpigraph f)

/-- The function `(A f)(x) = inf { f u | u ∈ A⁻¹ x }` induced by a convex process `A` and an
extended-real-valued function `f`. -/
noncomputable def infPreimage {n : ℕ} (A : ConvexProcess n n) (f : (Fin n → ℝ) → WithTop ℝ) :
    (Fin n → ℝ) → WithTop ℝ :=
  fun x => sInf (f '' A.inverseMap x)

/-- Helper for Proposition 39.0.9: a strict finite upper bound on `f u` produces a real epigraph
height below that bound. -/
lemma helperForProposition_39_0_9_extract_real_below_bound {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) {u : Fin n → ℝ} {R : ℝ}
    (h : f u < (R : WithTop ℝ)) :
    ∃ s : ℝ, f u ≤ (s : WithTop ℝ) ∧ s < R := by
  -- A point strictly below a finite height cannot be `⊤`, so its `untop` is a real witness.
  have hfinite : f u ≠ ⊤ := ne_of_lt (lt_trans h (by simp))
  refine ⟨(f u).untop hfinite, ?_, ?_⟩
  · -- The chosen real height is exactly the finite value of `f u`.
    rw [WithTop.coe_untop _ hfinite]
  · -- Converting back from `WithTop` gives the desired strict real inequality.
    exact (WithTop.untop_lt_iff hfinite).2 h

/-- Helper for Proposition 39.0.9: if the inverse-fiber image of `f` is not bounded below, then
the `WithTop` infimum defining `infPreimage` is forced to be `⊤`. -/
lemma helperForProposition_39_0_9_infPreimage_eq_top_of_not_bddBelow {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (A : ConvexProcess n n) {x : Fin n → ℝ}
    (hNotBddBelow : ¬ BddBelow (f '' A.inverseMap x)) :
    infPreimage A f x = (⊤ : WithTop ℝ) := by
  classical
  let S : Set (WithTop ℝ) := f '' A.inverseMap x
  -- Unfold `infPreimage` and apply the `WithTop` infimum convention for sets without a lower
  -- bound.
  change sInf S = (⊤ : WithTop ℝ)
  simp [S, WithTop.instInfSet, hNotBddBelow]

/-- Helper for Proposition 39.0.9: any finite epigraph point of `infPreimage A f` forces the
corresponding inverse-fiber image of `f` to be bounded below. -/
lemma helperForProposition_39_0_9_bddBelow_of_epigraph {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (A : ConvexProcess n n)
    {x : Fin n → ℝ} {r : ℝ}
    (hx : (x, r) ∈ withTopEpigraph (infPreimage A f)) :
    BddBelow (f '' A.inverseMap x) := by
  by_contra hS_bddBelow
  have hInfLe : infPreimage A f x ≤ (r : WithTop ℝ) := by
    -- Unfold epigraph membership to expose the infimum bound.
    simpa [withTopEpigraph] using hx
  have hTopLe : (⊤ : WithTop ℝ) ≤ (r : WithTop ℝ) := by
    have hTop :
        infPreimage A f x = (⊤ : WithTop ℝ) :=
      helperForProposition_39_0_9_infPreimage_eq_top_of_not_bddBelow
        (f := f) (A := A) (x := x) hS_bddBelow
    -- The new helper packages the exact obstruction identified in the re-plan history.
    rw [hTop] at hInfLe
    exact hInfLe
  -- A finite real height cannot dominate `⊤`, so the image set must have been bounded below.
  simp at hTopLe

/-- Helper for Proposition 39.0.9: if a convex-combination inverse fiber is not bounded below,
then any two finite endpoint epigraph points witness failure of convexity for `infPreimage A f`. -/
lemma helperForProposition_39_0_9_notConvex_of_not_bddBelow_combo {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (A : ConvexProcess n n)
    {x₁ x₂ : Fin n → ℝ} {r₁ r₂ a b : ℝ}
    (hx₁ : (x₁, r₁) ∈ withTopEpigraph (infPreimage A f))
    (hx₂ : (x₂, r₂) ∈ withTopEpigraph (infPreimage A f))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hNotBdd :
      ¬ BddBelow (f '' A.inverseMap (a • x₁ + b • x₂))) :
    ¬ IsConvexWithTop (infPreimage A f) := by
  intro hConvex
  have hConvexMem := (convex_iff_add_mem).1 hConvex
  have hCombo :
      ((a • x₁ + b • x₂, a * r₁ + b * r₂) : (Fin n → ℝ) × ℝ) ∈
        withTopEpigraph (infPreimage A f) := by
    -- Convexity of the epigraph would force the weighted combination of the endpoint epigraph
    -- points back into the epigraph.
    simpa [Prod.smul_mk, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using hConvexMem hx₁ hx₂ ha hb hab
  -- But a non-bounded-below midpoint fiber makes every finite real height impossible there.
  exact hNotBdd (helperForProposition_39_0_9_bddBelow_of_epigraph f A hCombo)

/-- Helper for Proposition 39.0.9: every finite epigraph point of `infPreimage A f` admits an
almost-minimizing source point in the inverse fiber. -/
lemma helperForProposition_39_0_9_approx_source_witness {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (A : ConvexProcess n n)
    {x : Fin n → ℝ} {r ε : ℝ}
    (hx : (x, r) ∈ withTopEpigraph (infPreimage A f)) (hε : 0 < ε) :
    ∃ u, ∃ s : ℝ, u ∈ A.inverseMap x ∧ f u ≤ (s : WithTop ℝ) ∧ s < r + ε := by
  classical
  let S : Set (WithTop ℝ) := f '' A.inverseMap x
  have hInfLe : sInf S ≤ (r : WithTop ℝ) := by
    -- Reuse the epigraph inequality after naming the inverse-fiber image set.
    simpa [withTopEpigraph, infPreimage, S] using hx
  have hS_bddBelow : BddBelow S :=
    helperForProposition_39_0_9_bddBelow_of_epigraph f A hx
  have hS_glb : IsGLB S (sInf S) := WithTop.isGLB_sInf' hS_bddBelow
  have hInfLt : sInf S < ((r + ε : ℝ) : WithTop ℝ) := by
    -- Move the finite bound upward by `ε` to obtain a strict inequality for the infimum.
    have hr_lt : (r : WithTop ℝ) < ((r + ε : ℝ) : WithTop ℝ) := by
      exact_mod_cast (show r < r + ε by linarith)
    exact lt_of_le_of_lt hInfLe hr_lt
  rcases (isGLB_lt_iff hS_glb).1 hInfLt with ⟨y, hyS, hyLt⟩
  rcases hyS with ⟨u, hu, rfl⟩
  -- Convert the strict `WithTop` estimate on `f u` into a real epigraph height.
  rcases helperForProposition_39_0_9_extract_real_below_bound f hyLt with ⟨s, hs_le, hs_lt⟩
  exact ⟨u, s, hu, hs_le, hs_lt⟩

/-- Helper for Proposition 39.0.9: inverse fibers are stable under convex combinations of source
points and targets. -/
lemma helperForProposition_39_0_9_weighted_inverse_mem {n : ℕ} (A : ConvexProcess n n)
    {u₁ u₂ x₁ x₂ : Fin n → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hu₁ : u₁ ∈ A.inverseMap x₁) (hu₂ : u₂ ∈ A.inverseMap x₂) :
    a • u₁ + b • u₂ ∈ A.inverseMap (a • x₁ + b • x₂) := by
  -- Reinterpret inverse-fiber membership as membership in the corresponding target fibers.
  simpa [ConvexProcess.inverseMap, setValuedInverse] using
    (helperForProposition_39_0_8_weighted_mem_targetFiber A ha hb hab hu₁ hu₂)

/-- Helper for Proposition 39.0.9: combining two finite epigraph points yields an `ε`-approximate
epigraph point over the convex combination. -/
lemma helperForProposition_39_0_9_combo_lt_of_eps {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (hf : IsConvexWithTop f) (A : ConvexProcess n n)
    {x₁ x₂ : Fin n → ℝ} {r₁ r₂ a b ε : ℝ}
    (hx₁ : (x₁, r₁) ∈ withTopEpigraph (infPreimage A f))
    (hx₂ : (x₂, r₂) ∈ withTopEpigraph (infPreimage A f))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hε : 0 < ε)
    (hBdd :
      BddBelow (f '' A.inverseMap (a • x₁ + b • x₂))) :
    infPreimage A f (a • x₁ + b • x₂) < ((a * r₁ + b * r₂ + ε : ℝ) : WithTop ℝ) := by
  rcases helperForProposition_39_0_9_approx_source_witness f A hx₁ hε with
    ⟨u₁, s₁, hu₁, hs₁_le, hs₁_lt⟩
  rcases helperForProposition_39_0_9_approx_source_witness f A hx₂ hε with
    ⟨u₂, s₂, hu₂, hs₂_le, hs₂_lt⟩
  have hf_convex := (convex_iff_add_mem).1 hf
  have hP₁ : ((u₁, s₁) : (Fin n → ℝ) × ℝ) ∈ withTopEpigraph f := by
    -- The almost-minimizer comes with a real epigraph height for `f`.
    simpa [withTopEpigraph] using hs₁_le
  have hP₂ : ((u₂, s₂) : (Fin n → ℝ) × ℝ) ∈ withTopEpigraph f := by
    -- The second source witness is handled the same way.
    simpa [withTopEpigraph] using hs₂_le
  have hCombo_epi :
      ((a • u₁ + b • u₂, a * s₁ + b * s₂) : (Fin n → ℝ) × ℝ) ∈ withTopEpigraph f := by
    simpa [Prod.smul_mk, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using hf_convex hP₁ hP₂ ha hb hab
  have hu_combo :
      a • u₁ + b • u₂ ∈ A.inverseMap (a • x₁ + b • x₂) :=
    helperForProposition_39_0_9_weighted_inverse_mem A ha hb hab hu₁ hu₂
  have hHeight_lt : a * s₁ + b * s₂ < a * r₁ + b * r₂ + ε := by
    -- The endpoint estimates combine linearly, and `a + b = 1` absorbs the repeated `ε`.
    by_cases ha_zero : a = 0
    · have hb_one : b = 1 := by linarith
      simpa [ha_zero, hb_one] using hs₂_lt
    · by_cases hb_zero : b = 0
      · have ha_one : a = 1 := by linarith
        simpa [hb_zero, ha_one] using hs₁_lt
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha_zero)
        have hb_pos : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hb_zero)
        have hScaled :
            a * s₁ + b * s₂ < a * (r₁ + ε) + b * (r₂ + ε) := by
          gcongr
        nlinarith [hScaled, hab]
  have hValue_lt :
      f (a • u₁ + b • u₂) < ((a * r₁ + b * r₂ + ε : ℝ) : WithTop ℝ) := by
    -- First place the combined source point in the epigraph of `f`, then compare heights.
    have hValue_le :
        f (a • u₁ + b • u₂) ≤ ((a * s₁ + b * s₂ : ℝ) : WithTop ℝ) := by
      simpa [withTopEpigraph, Prod.smul_mk, add_comm, add_left_comm, add_assoc, mul_comm,
        mul_left_comm, mul_assoc] using hCombo_epi
    exact lt_of_le_of_lt hValue_le (by exact_mod_cast hHeight_lt)
  have hMember :
      f (a • u₁ + b • u₂) ∈ f '' A.inverseMap (a • x₁ + b • x₂) :=
    Set.mem_image_of_mem f hu_combo
  have hInfLe :
      infPreimage A f (a • x₁ + b • x₂) ≤ f (a • u₁ + b • u₂) := by
    -- Once the combined image set is bounded below, its infimum lies below every explicit member.
    exact (WithTop.isGLB_sInf' hBdd).1 hMember
  -- Compare the infimum with the explicit combined witness and then use the height estimate.
  exact lt_of_le_of_lt hInfLe hValue_lt

/-- Helper for Proposition 39.0.9: a `WithTop ℝ` value that lies below every finite perturbation
of a real bound is already below that bound. -/
lemma helperForProposition_39_0_9_le_of_lt_add_eps {y : WithTop ℝ} {r : ℝ}
    (h : ∀ ε > 0, y < ((r + ε : ℝ) : WithTop ℝ)) :
    y ≤ (r : WithTop ℝ) := by
  by_cases hTop : y = ⊤
  · -- The top element cannot be strictly below any finite real height.
    exfalso
    have hFalse := h 1 zero_lt_one
    simp [hTop] at hFalse
  · -- Once `y` is finite, reduce to the usual real `ε`-argument.
    have hyEq : y = ((y.untop hTop : ℝ) : WithTop ℝ) := by
      exact (WithTop.coe_untop y hTop).symm
    have hltAll :
        ∀ ε > 0, y.untop hTop < r + ε := by
      intro ε hε
      have hyLt := h ε hε
      rw [hyEq] at hyLt
      simpa using hyLt
    rw [hyEq]
    by_contra hy_gt
    have hy_gt_real : r < y.untop hTop := by
      simpa using hy_gt
    let ε : ℝ := (y.untop hTop - r) / 2
    have hε : 0 < ε := by
      dsimp [ε]
      linarith
    have hyLt := hltAll ε hε
    dsimp [ε] at hyLt
    linarith

/-- Helper for Proposition 39.0.9: a global lower bound on every inverse-fiber image implies the
localized lower-boundedness hypothesis needed for convex combinations of finite epigraph points. -/
lemma helperForProposition_39_0_9_combo_bddBelow_of_fiberwise {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (A : ConvexProcess n n)
    (hBdd : ∀ x, BddBelow (f '' A.inverseMap x)) :
    ∀ {x₁ x₂ : Fin n → ℝ} {r₁ r₂ a b : ℝ},
      (x₁, r₁) ∈ withTopEpigraph (infPreimage A f) →
        (x₂, r₂) ∈ withTopEpigraph (infPreimage A f) →
          0 ≤ a → 0 ≤ b → a + b = 1 →
            BddBelow (f '' A.inverseMap (a • x₁ + b • x₂)) := by
  intro x₁ x₂ r₁ r₂ a b _ _ _ _ _
  -- The stronger fiberwise hypothesis already supplies the bound at the combined target point.
  exact hBdd (a • x₁ + b • x₂)

/-- Helper for Proposition 39.0.9: the standard epigraph proof works once every inverse-fiber
image of `f` is bounded below. -/
lemma helperForProposition_39_0_9_convex_of_fiberwise_bddBelow {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (hf : IsConvexWithTop f) (A : ConvexProcess n n)
    (hBdd : ∀ x, BddBelow (f '' A.inverseMap x)) :
    IsConvexWithTop (infPreimage A f) := by
  -- Check convexity directly on the epigraph of `infPreimage A f`.
  rw [IsConvexWithTop, convex_iff_add_mem]
  intro p₁ hp₁ p₂ hp₂ a b ha hb hab
  rcases p₁ with ⟨x₁, r₁⟩
  rcases p₂ with ⟨x₂, r₂⟩
  change
    infPreimage A f (a • x₁ + b • x₂) ≤
      ((a * r₁ + b * r₂ : ℝ) : WithTop ℝ)
  -- The `ε`-approximate witness lemma applies because the midpoint inverse-fiber image is
  -- bounded below by hypothesis.
  exact helperForProposition_39_0_9_le_of_lt_add_eps <| by
    intro ε hε
    exact helperForProposition_39_0_9_combo_lt_of_eps f hf A hp₁ hp₂ ha hb hab hε
      (hBdd (a • x₁ + b • x₂))

/-- Helper for Proposition 39.0.9: if `infPreimage A f` were convex, then every convex
combination of two finite epigraph points would have inverse-fiber image bounded below. -/
lemma helperForProposition_39_0_9_bddBelow_combo_of_convex {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (A : ConvexProcess n n)
    {x₁ x₂ : Fin n → ℝ} {r₁ r₂ a b : ℝ}
    (hConvex : IsConvexWithTop (infPreimage A f))
    (hx₁ : (x₁, r₁) ∈ withTopEpigraph (infPreimage A f))
    (hx₂ : (x₂, r₂) ∈ withTopEpigraph (infPreimage A f))
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    BddBelow (f '' A.inverseMap (a • x₁ + b • x₂)) := by
  -- Any failure of lower boundedness at the convex combination would contradict convexity via the
  -- previously proved obstruction lemma.
  by_contra hNotBdd
  exact
    helperForProposition_39_0_9_notConvex_of_not_bddBelow_combo f A hx₁ hx₂ ha hb hab hNotBdd
      hConvex

/-- Helper for Proposition 39.0.9: to prove convexity of `infPreimage A f`, it is enough to know
that each convex combination of two finite epigraph points has inverse-fiber image bounded below. -/
lemma helperForProposition_39_0_9_convex_of_combo_bddBelow {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (hf : IsConvexWithTop f) (A : ConvexProcess n n)
    (hComboBdd :
      ∀ {x₁ x₂ : Fin n → ℝ} {r₁ r₂ a b : ℝ},
        (x₁, r₁) ∈ withTopEpigraph (infPreimage A f) →
          (x₂, r₂) ∈ withTopEpigraph (infPreimage A f) →
            0 ≤ a → 0 ≤ b → a + b = 1 →
              BddBelow (f '' A.inverseMap (a • x₁ + b • x₂))) :
    IsConvexWithTop (infPreimage A f) := by
  -- Check convexity on finite epigraph points and invoke the localized lower-boundedness
  -- hypothesis exactly where the `ε`-argument needs it.
  rw [IsConvexWithTop, convex_iff_add_mem]
  intro p₁ hp₁ p₂ hp₂ a b ha hb hab
  rcases p₁ with ⟨x₁, r₁⟩
  rcases p₂ with ⟨x₂, r₂⟩
  change
    infPreimage A f (a • x₁ + b • x₂) ≤
      ((a * r₁ + b * r₂ : ℝ) : WithTop ℝ)
  -- Once the combined inverse fiber is known to be bounded below, the existing approximate-witness
  -- estimate closes the convexity inequality.
  exact helperForProposition_39_0_9_le_of_lt_add_eps <| by
    intro ε hε
    exact helperForProposition_39_0_9_combo_lt_of_eps f hf A hp₁ hp₂ ha hb hab hε
      (hComboBdd (x₁ := x₁) (x₂ := x₂) (r₁ := r₁) (r₂ := r₂)
        (a := a) (b := b) hp₁ hp₂ ha hb hab)

/-- Helper for Proposition 39.0.9: for the current `WithTop ℝ` formalization, convexity of
`infPreimage A f` is equivalent to lower boundedness on every convex-combination inverse fiber that
arises from two finite epigraph points. -/
lemma helperForProposition_39_0_9_convex_iff_combo_bddBelow {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (hf : IsConvexWithTop f) (A : ConvexProcess n n) :
    IsConvexWithTop (infPreimage A f) ↔
      ∀ {x₁ x₂ : Fin n → ℝ} {r₁ r₂ a b : ℝ},
        (x₁, r₁) ∈ withTopEpigraph (infPreimage A f) →
          (x₂, r₂) ∈ withTopEpigraph (infPreimage A f) →
            0 ≤ a → 0 ≤ b → a + b = 1 →
              BddBelow (f '' A.inverseMap (a • x₁ + b • x₂)) := by
  constructor
  · intro hConvex x₁ x₂ r₁ r₂ a b hx₁ hx₂ ha hb hab
    -- Convexity forces the midpoint epigraph point to exist, so the inverse-fiber image there
    -- must be bounded below.
    exact
      helperForProposition_39_0_9_bddBelow_combo_of_convex f A hConvex hx₁ hx₂ ha hb hab
  · intro hComboBdd
    -- Conversely, the localized lower-boundedness hypothesis is exactly the input needed by the
    -- existing `ε`-approximation proof of convexity.
    exact helperForProposition_39_0_9_convex_of_combo_bddBelow f hf A hComboBdd

/-- Helper for Proposition 39.0.9: any proof of the advertised universal theorem schema would
force the localized lower-boundedness condition on every pair of finite epigraph endpoints. -/
lemma helperForProposition_39_0_9_universalClaim_implies_combo_bddBelow :
    (∀ {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) (_hf : IsConvexWithTop f)
      (A : ConvexProcess n n),
      IsConvexWithTop (infPreimage A f)) →
      ∀ {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) (_hf : IsConvexWithTop f)
        (A : ConvexProcess n n) {x₁ x₂ : Fin n → ℝ} {r₁ r₂ a b : ℝ},
        (x₁, r₁) ∈ withTopEpigraph (infPreimage A f) →
          (x₂, r₂) ∈ withTopEpigraph (infPreimage A f) →
            0 ≤ a → 0 ≤ b → a + b = 1 →
              BddBelow (f '' A.inverseMap (a • x₁ + b • x₂)) := by
  intro hUniversal n f hf A x₁ x₂ r₁ r₂ a b hx₁ hx₂ ha hb hab
  -- Specialize the claimed universal theorem schema to the current convex-data instance.
  have hConvex : IsConvexWithTop (infPreimage A f) :=
    hUniversal (n := n) f hf A
  -- The already-proved converse obstruction then recovers the missing bounded-below condition.
  exact helperForProposition_39_0_9_bddBelow_combo_of_convex f A hConvex hx₁ hx₂ ha hb hab

/-- Helper for Proposition 39.0.9: once a single convex counterexample is available, the current
universal theorem schema is refuted. -/
lemma helperForProposition_39_0_9_existsCounterexample_refutes_universalClaim
    (hCounterexample :
      ∃ (n : ℕ) (f : (Fin n → ℝ) → WithTop ℝ) (_hf : IsConvexWithTop f)
        (A : ConvexProcess n n),
          ¬ IsConvexWithTop (infPreimage A f)) :
    ¬ (∀ {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) (_hf : IsConvexWithTop f)
        (A : ConvexProcess n n), IsConvexWithTop (infPreimage A f)) := by
  intro hUniversal
  -- Unpack the counterexample data and specialize the putative universal theorem to it.
  rcases hCounterexample with ⟨n, f, hf, A, hNotConvex⟩
  exact hNotConvex (hUniversal (n := n) f hf A)

/-- Helper for Proposition 39.0.9: if `infPreimage A f` is convex, then the set of target points
admitting a finite epigraph height is convex, and every such target has lower-bounded inverse-fiber
image under `f`. -/
lemma helperForProposition_39_0_9_convex_finiteEpigraphDomain_and_bddBelow {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (A : ConvexProcess n n)
    (hConvex : IsConvexWithTop (infPreimage A f)) :
    Convex ℝ {x : Fin n → ℝ | ∃ r : ℝ, (x, r) ∈ withTopEpigraph (infPreimage A f)} ∧
      ∀ x : Fin n → ℝ,
        (∃ r : ℝ, (x, r) ∈ withTopEpigraph (infPreimage A f)) →
          BddBelow (f '' A.inverseMap x) := by
  constructor
  · -- Project the convex epigraph to the target space by keeping the finite heights explicit.
    rw [convex_iff_add_mem]
    intro x₁ hx₁ x₂ hx₂ a b ha hb hab
    rcases hx₁ with ⟨r₁, hr₁⟩
    rcases hx₂ with ⟨r₂, hr₂⟩
    have hConvexMem := (convex_iff_add_mem).1 hConvex
    refine ⟨a * r₁ + b * r₂, ?_⟩
    -- Convexity of the epigraph produces a finite height over the convex combination target.
    simpa [Prod.smul_mk, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
      mul_assoc] using hConvexMem hr₁ hr₂ ha hb hab
  · intro x hx
    rcases hx with ⟨r, hr⟩
    -- Any finite epigraph witness forces the corresponding inverse-fiber image to be bounded
    -- below.
    exact helperForProposition_39_0_9_bddBelow_of_epigraph f A hr

/-- Helper for Proposition 39.0.9: the localized lower-boundedness hypothesis used in the
conditional convexity proof already implies the strongest geometric consequence available in the
current `WithTop ℝ` formalization, namely convexity of the finite-epigraph domain together with
lower boundedness on every target in that domain. -/
lemma helperForProposition_39_0_9_finiteEpigraphDomain_and_bddBelow_of_combo_bddBelow {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (hf : IsConvexWithTop f) (A : ConvexProcess n n)
    (hComboBdd :
      ∀ {x₁ x₂ : Fin n → ℝ} {r₁ r₂ a b : ℝ},
        (x₁, r₁) ∈ withTopEpigraph (infPreimage A f) →
          (x₂, r₂) ∈ withTopEpigraph (infPreimage A f) →
            0 ≤ a → 0 ≤ b → a + b = 1 →
              BddBelow (f '' A.inverseMap (a • x₁ + b • x₂))) :
    Convex ℝ {x : Fin n → ℝ | ∃ r : ℝ, (x, r) ∈ withTopEpigraph (infPreimage A f)} ∧
      ∀ x : Fin n → ℝ,
        (∃ r : ℝ, (x, r) ∈ withTopEpigraph (infPreimage A f)) →
          BddBelow (f '' A.inverseMap x) := by
  -- First recover convexity of `infPreimage A f` from the localized lower-boundedness premise.
  have hConvex : IsConvexWithTop (infPreimage A f) :=
    helperForProposition_39_0_9_convex_of_combo_bddBelow f hf A hComboBdd
  -- Then reuse the convex-case consequence already isolated just above.
  exact helperForProposition_39_0_9_convex_finiteEpigraphDomain_and_bddBelow f A hConvex

/-- Helper for Proposition 39.0.9: in the current `WithTop ℝ` formalization, convexity of
`infPreimage A f` is equivalent to convexity of the target set admitting finite epigraph heights,
together with lower boundedness on each inverse-fiber image over that set. -/
lemma helperForProposition_39_0_9_convex_iff_finiteEpigraphDomain_and_bddBelow {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (hf : IsConvexWithTop f) (A : ConvexProcess n n) :
    IsConvexWithTop (infPreimage A f) ↔
      Convex ℝ {x : Fin n → ℝ | ∃ r : ℝ, (x, r) ∈ withTopEpigraph (infPreimage A f)} ∧
        ∀ x : Fin n → ℝ,
          (∃ r : ℝ, (x, r) ∈ withTopEpigraph (infPreimage A f)) →
            BddBelow (f '' A.inverseMap x) := by
  constructor
  · intro hConvex
    -- The forward implication is exactly the convex-case consequence already proved above.
    exact helperForProposition_39_0_9_convex_finiteEpigraphDomain_and_bddBelow f A hConvex
  · rintro ⟨hFiniteDomainConvex, hBddOnFiniteDomain⟩
    -- Recover the localized bounded-below premise by keeping the convex-combination target inside
    -- the finite-epigraph domain.
    apply helperForProposition_39_0_9_convex_of_combo_bddBelow f hf A
    intro x₁ x₂ r₁ r₂ a b hx₁ hx₂ ha hb hab
    have hx₁_mem :
        x₁ ∈ {x : Fin n → ℝ | ∃ r : ℝ, (x, r) ∈ withTopEpigraph (infPreimage A f)} := by
      exact ⟨r₁, hx₁⟩
    have hx₂_mem :
        x₂ ∈ {x : Fin n → ℝ | ∃ r : ℝ, (x, r) ∈ withTopEpigraph (infPreimage A f)} := by
      exact ⟨r₂, hx₂⟩
    have hCombo_mem :
        a • x₁ + b • x₂ ∈
          {x : Fin n → ℝ | ∃ r : ℝ, (x, r) ∈ withTopEpigraph (infPreimage A f)} := by
      exact (convex_iff_add_mem.1 hFiniteDomainConvex) hx₁_mem hx₂_mem ha hb hab
    -- The domain hypothesis now gives the needed lower bound at the combined target point.
    exact hBddOnFiniteDomain (a • x₁ + b • x₂) hCombo_mem

/-- Helper for Proposition 39.0.9: if every target point already admits some finite epigraph
height for `infPreimage A f`, then each inverse-fiber image of `f` is bounded below. -/
lemma helperForProposition_39_0_9_fiberwise_bddBelow_of_finiteEpigraph_everywhere {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (A : ConvexProcess n n)
    (hFinite :
      ∀ x : Fin n → ℝ, ∃ r : ℝ, (x, r) ∈ withTopEpigraph (infPreimage A f)) :
    ∀ x : Fin n → ℝ, BddBelow (f '' A.inverseMap x) := by
  intro x
  rcases hFinite x with ⟨r, hr⟩
  -- Any finite epigraph witness at `x` forces lower boundedness on the corresponding inverse
  -- fiber image.
  exact helperForProposition_39_0_9_bddBelow_of_epigraph f A hr

/-- Helper for Proposition 39.0.9: the current `WithTop ℝ` formalization becomes convex once one
adds the strengthened hypothesis that every target point has a finite epigraph witness. -/
lemma helperForProposition_39_0_9_convex_of_finiteEpigraph_everywhere {n : ℕ}
    (f : (Fin n → ℝ) → WithTop ℝ) (hf : IsConvexWithTop f) (A : ConvexProcess n n)
    (hFinite :
      ∀ x : Fin n → ℝ, ∃ r : ℝ, (x, r) ∈ withTopEpigraph (infPreimage A f)) :
    IsConvexWithTop (infPreimage A f) := by
  -- First convert the everywhere-finite epigraph hypothesis into the fiberwise lower-boundedness
  -- condition needed by the existing conditional convexity theorem.
  have hBdd : ∀ x : Fin n → ℝ, BddBelow (f '' A.inverseMap x) :=
    helperForProposition_39_0_9_fiberwise_bddBelow_of_finiteEpigraph_everywhere f A hFinite
  -- Then invoke the already formalized convexity proof under fiberwise lower boundedness.
  exact helperForProposition_39_0_9_convex_of_fiberwise_bddBelow f hf A hBdd

-- Proof sketch: Work with epigraphs in `(Fin n → ℝ) × ℝ`. Express `epi (infPreimage A f)` as the
-- image under a suitable projection of a convex set built from the graph of `A` and `epi f`, then
-- use that convex-process graphs are convex cones (Proposition 39.0.1) and stability of convexity
-- under products, intersections, and linear images.
/-- Proposition 39.0.9 in the current `WithTop ℝ` formalization: the textbook convexity
conclusion holds once one adds the fiberwise lower-boundedness hypothesis needed to control the
`WithTop.sInf` defining `infPreimage A f` on every inverse fiber.

(Note: the LaTeX source line inside the environment says “Proposition 39.0.8”, but in this
formalization this statement is recorded as Proposition 39.0.9, following the provided label.) -/
theorem prop_39_0_9 {n : ℕ} (f : (Fin n → ℝ) → WithTop ℝ) (hf : IsConvexWithTop f)
    (A : ConvexProcess n n)
    (hBdd : ∀ x : Fin n → ℝ, BddBelow (f '' A.inverseMap x)) :
    IsConvexWithTop (infPreimage A f) := by
  exact helperForProposition_39_0_9_convex_of_fiberwise_bddBelow f hf A hBdd

/-- Composition of set-valued mappings: for `A : X → Set Y` and `B : Y → Set Z`, define
`(B ∘ₛ A) x := ⋃ y ∈ A x, B y`. -/
def setValuedComp {X Y Z : Type*} (B : Y → Set Z) (A : X → Set Y) : X → Set Z :=
  fun x => ⋃ y ∈ A x, B y

/-- The product of convex processes at the level of their underlying set-valued mappings:
`(B A) u := ⋃ x ∈ A u, B x`. -/
def compSetValued {m n p : ℕ} (B : ConvexProcess n p) (A : ConvexProcess m n) :
    (Fin m → ℝ) → Set (Fin p → ℝ) :=
  setValuedComp B.toSetValued A.toSetValued

/-- Helper for Proposition 39.0.10: membership in the fiberwise composition is equivalent to the
existence of an intermediate point in the `A`-fiber whose `B`-fiber contains the output. -/
lemma helperForProposition_39_0_10_mem_compSetValued_iff {m n p : ℕ}
    (A : ConvexProcess m n) (B : ConvexProcess n p) (u : Fin m → ℝ) (z : Fin p → ℝ) :
    z ∈ compSetValued B A u ↔ ∃ x, x ∈ A.toSetValued u ∧ z ∈ B.toSetValued x := by
  -- Unfold the composed fiber and rewrite the union membership as an existential witness.
  simp [compSetValued, setValuedComp]

/-- Helper for Proposition 39.0.10: the fiberwise composition of two convex processes is
superadditive. -/
lemma helperForProposition_39_0_10_comp_map_add_superset {m n p : ℕ}
    (A : ConvexProcess m n) (B : ConvexProcess n p) :
    ∀ u₁ u₂,
      compSetValued B A u₁ + compSetValued B A u₂ ⊆ compSetValued B A (u₁ + u₂) := by
  intro u₁ u₂ z hz
  -- Split the Minkowski-sum witness into points coming from the two composed fibers.
  rcases Set.mem_add.1 hz with ⟨z₁, hz₁, z₂, hz₂, rfl⟩
  rcases (helperForProposition_39_0_10_mem_compSetValued_iff A B u₁ z₁).1 hz₁ with
    ⟨x₁, hx₁, hz₁B⟩
  rcases (helperForProposition_39_0_10_mem_compSetValued_iff A B u₂ z₂).1 hz₂ with
    ⟨x₂, hx₂, hz₂B⟩
  -- Superadditivity of `A` produces the intermediate point over `u₁ + u₂`.
  have hxsum :
      x₁ + x₂ ∈ A.toSetValued (u₁ + u₂) := by
    have hxsum_mem : x₁ + x₂ ∈ A.toSetValued u₁ + A.toSetValued u₂ :=
      Set.mem_add.2 ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    exact A.map_add_superset u₁ u₂ hxsum_mem
  -- Superadditivity of `B` then combines the output witnesses over that intermediate point.
  have hzsum :
      z₁ + z₂ ∈ B.toSetValued (x₁ + x₂) := by
    have hzsum_mem : z₁ + z₂ ∈ B.toSetValued x₁ + B.toSetValued x₂ :=
      Set.mem_add.2 ⟨z₁, hz₁B, z₂, hz₂B, rfl⟩
    exact B.map_add_superset x₁ x₂ hzsum_mem
  exact (helperForProposition_39_0_10_mem_compSetValued_iff A B (u₁ + u₂) (z₁ + z₂)).2
    ⟨x₁ + x₂, hxsum, hzsum⟩

/-- Helper for Proposition 39.0.10: the fiberwise composition of two convex processes is
positively homogeneous. -/
lemma helperForProposition_39_0_10_comp_map_smul_pos {m n p : ℕ}
    (A : ConvexProcess m n) (B : ConvexProcess n p) :
    ∀ u (r : ℝ), 0 < r → compSetValued B A (r • u) = r • compSetValued B A u := by
  intro u r hr
  ext z
  constructor
  · intro hz
    -- First descale the intermediate point through `A`, then descale the output through `B`.
    rcases (helperForProposition_39_0_10_mem_compSetValued_iff A B (r • u) z).1 hz with
      ⟨x, hx, hzB⟩
    have hxScaled : x ∈ r • A.toSetValued u := by
      simpa [A.map_smul_pos u r hr] using hx
    rcases Set.mem_smul_set.1 hxScaled with ⟨x', hx', rfl⟩
    have hzScaled : z ∈ r • B.toSetValued x' := by
      simpa [B.map_smul_pos x' r hr] using hzB
    rcases Set.mem_smul_set.1 hzScaled with ⟨z', hz', hz_eq⟩
    refine Set.mem_smul_set.2 ?_
    refine ⟨z', ?_, hz_eq⟩
    exact (helperForProposition_39_0_10_mem_compSetValued_iff A B u z').2 ⟨x', hx', hz'⟩
  · intro hz
    -- Conversely, scale both the intermediate witness and the output witness back into the
    -- composed fiber over `r • u`.
    rcases Set.mem_smul_set.1 hz with ⟨z', hz', rfl⟩
    rcases (helperForProposition_39_0_10_mem_compSetValued_iff A B u z').1 hz' with
      ⟨x', hx', hz'B⟩
    have hxScaled : r • x' ∈ A.toSetValued (r • u) := by
      have hxScaledMem : r • x' ∈ r • A.toSetValued u :=
        Set.mem_smul_set.2 ⟨x', hx', rfl⟩
      simpa [A.map_smul_pos u r hr] using hxScaledMem
    have hzScaled : r • z' ∈ B.toSetValued (r • x') := by
      have hzScaledMem : r • z' ∈ r • B.toSetValued x' :=
        Set.mem_smul_set.2 ⟨z', hz'B, rfl⟩
      simpa [B.map_smul_pos x' r hr] using hzScaledMem
    exact (helperForProposition_39_0_10_mem_compSetValued_iff A B (r • u) (r • z')).2
      ⟨r • x', hxScaled, hzScaled⟩

/-- Helper for Proposition 39.0.10: the origin belongs to the composed zero fiber. -/
lemma helperForProposition_39_0_10_comp_zero_mem {m n p : ℕ}
    (A : ConvexProcess m n) (B : ConvexProcess n p) :
    (0 : Fin p → ℝ) ∈ compSetValued B A (0 : Fin m → ℝ) := by
  -- Use the intermediate zero witness supplied by the two convex-process axioms.
  exact (helperForProposition_39_0_10_mem_compSetValued_iff A B 0 0).2
    ⟨(0 : Fin n → ℝ), A.zero_mem, B.zero_mem⟩

/-- Helper for Proposition 39.0.10: membership in the composed inverse mapping is equivalent to
the existence of an intermediate point whose `B`-fiber contains `y` and whose `A`-fiber over `u`
contains that intermediate point. -/
lemma helperForProposition_39_0_10_mem_inverse_comp_iff {m n p : ℕ}
    (A : ConvexProcess m n) (B : ConvexProcess n p) (y : Fin p → ℝ) (u : Fin m → ℝ) :
    u ∈ setValuedComp A.inverseMap B.inverseMap y ↔
      ∃ x, y ∈ B.toSetValued x ∧ x ∈ A.toSetValued u := by
  -- Unfold the reversed composition and rewrite inverse-fiber membership as pointwise membership.
  simp [setValuedComp, ConvexProcess.inverseMap, setValuedInverse]

/-- Helper for Proposition 39.0.10: inverting the composed set-valued mapping is the same as
composing the inverse mappings in the opposite order. -/
lemma helperForProposition_39_0_10_inverse_eq {m n p : ℕ}
    (A : ConvexProcess m n) (B : ConvexProcess n p) :
    setValuedInverse (compSetValued B A) = setValuedComp A.inverseMap B.inverseMap := by
  ext y u
  -- Both sides unfold to the existence of an intermediate point `x` with `x ∈ A u` and `y ∈ B x`.
  constructor
  · intro hy
    have hyComp : y ∈ compSetValued B A u := by
      -- Unfold the inverse mapping to recover membership in the composed fiber at `u`.
      simpa [ConvexProcess.inverseMap, setValuedInverse] using hy
    rcases (helperForProposition_39_0_10_mem_compSetValued_iff A B u y).1 hyComp with
      ⟨x, hxA, hyB⟩
    exact (helperForProposition_39_0_10_mem_inverse_comp_iff A B y u).2 ⟨x, hyB, hxA⟩
  · intro hy
    rcases (helperForProposition_39_0_10_mem_inverse_comp_iff A B y u).1 hy with
      ⟨x, hyB, hxA⟩
    have hyComp : y ∈ compSetValued B A u :=
      (helperForProposition_39_0_10_mem_compSetValued_iff A B u y).2 ⟨x, hxA, hyB⟩
    -- Fold the composed-fiber membership back into the inverse-map definition.
    simpa [ConvexProcess.inverseMap, setValuedInverse] using hyComp

/-- Helper for Proposition 39.0.10: the fiberwise composition is realized by a convex process
with the expected underlying set-valued mapping. -/
lemma helperForProposition_39_0_10_exists_composite_process {m n p : ℕ}
    (A : ConvexProcess m n) (B : ConvexProcess n p) :
    ∃ cp : ConvexProcess m p, cp.toSetValued = compSetValued B A := by
  -- Package the three direct fiberwise axioms into a convex-process witness for the composition.
  let cp : ConvexProcess m p :=
    { toSetValued := compSetValued B A
      map_add_superset := helperForProposition_39_0_10_comp_map_add_superset A B
      map_smul_pos := helperForProposition_39_0_10_comp_map_smul_pos A B
      zero_mem := helperForProposition_39_0_10_comp_zero_mem A B }
  -- The constructed witness has exactly the desired underlying set-valued mapping.
  exact ⟨cp, rfl⟩

-- Proof sketch: Verify axioms (a),(b),(c) for `u ↦ ⋃ x ∈ A u, B x` directly from the axioms of `A`
-- and `B`, using distributivity of set addition and positive scaling over unions. For the inverse
-- formula, unfold `setValuedInverse` and the definition of `setValuedComp`; membership in
-- `(B A)⁻¹ y` is equivalent to existence of an intermediate `x` with `x ∈ A u` and `y ∈ B x`,
-- which is exactly membership in `(A⁻¹ B⁻¹) y`.
/-- Proposition 39.0.10: Let `A : ℝ^m ⇉ ℝ^n` and `B : ℝ^n ⇉ ℝ^p` be convex processes. Define the
product `(B A)` by `(B A) u := ⋃ x ∈ A u, B x`. Then `B A` is a convex process and
`(B A)⁻¹ = A⁻¹ B⁻¹` (as set-valued mappings). -/
theorem prop_39_0_10 {m n p : ℕ} (A : ConvexProcess m n) (B : ConvexProcess n p) :
    (∃ cp : ConvexProcess m p, cp.toSetValued = compSetValued B A) ∧
      setValuedInverse (compSetValued B A) = setValuedComp A.inverseMap B.inverseMap :=
  by
  constructor
  · -- Reuse the dedicated helper that packages the composite fibers into a convex-process witness.
    exact helperForProposition_39_0_10_exists_composite_process A B
  · -- The inverse identity is definitional once both constructions are unfolded pointwise.
    exact helperForProposition_39_0_10_inverse_eq A B


-- Proof sketch: For the first inclusion, unpack membership in the graph of the right-hand side as
-- `z = z₁ + z₂` with `zᵢ ∈ A (xᵢ)` and `xᵢ ∈ Aᵢ u`; then use superadditivity of `A` to get
-- `z ∈ A (x₁ + x₂)` with `x₁ + x₂ ∈ (A₁ + A₂) u`. For the second inclusion, unpack
-- `(A₁ + A₂) A` using an intermediate `x ∈ A u` and then split a Minkowski-sum witness. For the
-- complete lattice claim, use the graph-cone characterization (Proposition 39.0.1) together with
-- the fact that convex cones form a complete lattice under set inclusion, and transport the
-- structure along the correspondence.
/-- Helper for Proposition 39.0.11: the graph of `A (A₁ + A₂)` contains the graph of
`A A₁ + A A₂`. -/
lemma helperForProposition_39_0_11_left_distrib_graph_superset {n : ℕ}
    (A A₁ A₂ : ConvexProcess n n) :
    setValuedGraph (setValuedComp A.toSetValued (addSetValued A₁ A₂)) ⊇
      setValuedGraph (fun u =>
        setValuedComp A.toSetValued A₁.toSetValued u +
          setValuedComp A.toSetValued A₂.toSetValued u) := by
  intro p hp
  rcases p with ⟨u, z⟩
  -- Unpack graph membership on the right-hand side into a Minkowski-sum witness in the two
  -- composite fibers.
  have hp' :
      z ∈ setValuedComp A.toSetValued A₁.toSetValued u +
        setValuedComp A.toSetValued A₂.toSetValued u := by
    simpa [setValuedGraph] using hp
  rcases Set.mem_add.1 hp' with ⟨z₁, hz₁, z₂, hz₂, rfl⟩
  -- Each composite membership supplies an intermediate point in the corresponding input fiber.
  rcases (show ∃ x₁, x₁ ∈ A₁.toSetValued u ∧ z₁ ∈ A.toSetValued x₁ by
    simpa [setValuedComp] using hz₁) with ⟨x₁, hx₁, hz₁A⟩
  rcases (show ∃ x₂, x₂ ∈ A₂.toSetValued u ∧ z₂ ∈ A.toSetValued x₂ by
    simpa [setValuedComp] using hz₂) with ⟨x₂, hx₂, hz₂A⟩
  have hxsum : x₁ + x₂ ∈ addSetValued A₁ A₂ u :=
    Set.mem_add.2 ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  have hzsum : z₁ + z₂ ∈ A.toSetValued (x₁ + x₂) := by
    exact A.map_add_superset x₁ x₂ (Set.mem_add.2 ⟨z₁, hz₁A, z₂, hz₂A, rfl⟩)
  simpa [setValuedGraph, setValuedComp] using ⟨x₁ + x₂, hxsum, hzsum⟩

/-- Helper for Proposition 39.0.11: the graph of `(A₁ + A₂) A` is contained in the graph of
`A₁ A + A₂ A`. -/
lemma helperForProposition_39_0_11_right_distrib_graph_subset {n : ℕ}
    (A A₁ A₂ : ConvexProcess n n) :
    setValuedGraph (setValuedComp (addSetValued A₁ A₂) A.toSetValued) ⊆
      setValuedGraph (fun u =>
        setValuedComp A₁.toSetValued A.toSetValued u +
          setValuedComp A₂.toSetValued A.toSetValued u) := by
  intro p hp
  rcases p with ⟨u, z⟩
  -- Unpack the composite graph membership to a shared intermediate point `x ∈ A u`.
  have hp' : z ∈ setValuedComp (addSetValued A₁ A₂) A.toSetValued u := by
    simpa [setValuedGraph] using hp
  rcases (show ∃ x, x ∈ A.toSetValued u ∧ z ∈ addSetValued A₁ A₂ x by
    simpa [setValuedComp] using hp') with ⟨x, hxA, hz⟩
  rcases Set.mem_add.1 hz with ⟨z₁, hz₁, z₂, hz₂, rfl⟩
  -- Reuse the same intermediate point for both summands in the target Minkowski sum.
  have hz₁Comp : z₁ ∈ setValuedComp A₁.toSetValued A.toSetValued u := by
    change z₁ ∈ ⋃ y ∈ A.toSetValued u, A₁.toSetValued y
    exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hxA, hz₁⟩⟩
  have hz₂Comp : z₂ ∈ setValuedComp A₂.toSetValued A.toSetValued u := by
    change z₂ ∈ ⋃ y ∈ A.toSetValued u, A₂.toSetValued y
    exact Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨hxA, hz₂⟩⟩
  simpa [setValuedGraph] using Set.mem_add.2 ⟨z₁, hz₁Comp, z₂, hz₂Comp, rfl⟩

/-- Helper for Proposition 39.0.11: the singleton-valued process attached to a linear map is
superadditive. -/
lemma helperForProposition_39_0_11_singletonLinearProcess_map_add_superset {n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    ∀ u₁ u₂,
      ({L u₁} : Set (Fin n → ℝ)) + ({L u₂} : Set (Fin n → ℝ)) ⊆
        ({L (u₁ + u₂)} : Set (Fin n → ℝ)) := by
  intro u₁ u₂ x hx
  rcases Set.mem_add.1 hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  simp at hx₁ hx₂
  subst hx₁ hx₂
  simp [L.map_add]

/-- Helper for Proposition 39.0.11: the singleton-valued process attached to a linear map is
positively homogeneous. -/
lemma helperForProposition_39_0_11_singletonLinearProcess_map_smul_pos {n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    ∀ u (r : ℝ), 0 < r →
      ({L (r • u)} : Set (Fin n → ℝ)) = r • ({L u} : Set (Fin n → ℝ)) := by
  intro u r hr
  ext x
  constructor
  · intro hx
    simp at hx
    subst hx
    exact Set.mem_smul_set.2 ⟨L u, by simp, by simp⟩
  · intro hx
    rcases Set.mem_smul_set.1 hx with ⟨y, hy, rfl⟩
    simp at hy
    subst hy
    simp

/-- Helper for Proposition 39.0.11: the singleton-valued linear process sends `0` to `0`. -/
lemma helperForProposition_39_0_11_singletonLinearProcess_zero_mem {n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (0 : Fin n → ℝ) ∈ ({L (0 : Fin n → ℝ)} : Set (Fin n → ℝ)) := by
  simp

/-- Helper for Proposition 39.0.11: package a linear map as a singleton-valued convex process. -/
def helperForProposition_39_0_11_singletonLinearProcess {n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) : ConvexProcess n n :=
  { toSetValued := fun u => ({L u} : Set (Fin n → ℝ))
    map_add_superset := helperForProposition_39_0_11_singletonLinearProcess_map_add_superset L
    map_smul_pos := helperForProposition_39_0_11_singletonLinearProcess_map_smul_pos L
    zero_mem := helperForProposition_39_0_11_singletonLinearProcess_zero_mem L }

/-- Helper for Proposition 39.0.11: the singleton-valued linear process has the expected fibers. -/
lemma helperForProposition_39_0_11_singletonLinearProcess_toSetValued {n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (helperForProposition_39_0_11_singletonLinearProcess L).toSetValued = fun u => ({L u} : Set (Fin n → ℝ)) := rfl

/-- Helper for Proposition 39.0.11: membership in a singleton-valued linear process is equivalent
to equality with the linear image. -/
lemma helperForProposition_39_0_11_mem_singletonLinearProcess_iff {n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) {u x : Fin n → ℝ} :
    x ∈ (helperForProposition_39_0_11_singletonLinearProcess L).toSetValued u ↔ x = L u := by
  -- Unfold the singleton fiber so membership becomes the defining equality.
  simp [helperForProposition_39_0_11_singletonLinearProcess_toSetValued]

/-- Helper for Proposition 39.0.11: a singleton-valued linear process and its negative add
fiberwise to the zero singleton. -/
lemma helperForProposition_39_0_11_add_singletonLinearProcess_neg_toSetValued {n : ℕ}
    (L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (u : Fin n → ℝ) :
    addSetValued (helperForProposition_39_0_11_singletonLinearProcess L)
      (helperForProposition_39_0_11_singletonLinearProcess (-L)) u =
        ({0} : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · intro hx
    -- The two singleton fibers force the Minkowski-sum decomposition to be `L u + (-L) u`.
    rcases Set.mem_add.1 hx with ⟨x₁, hx₁, x₂, hx₂, rfl⟩
    have hx₁' := (helperForProposition_39_0_11_mem_singletonLinearProcess_iff L).1 hx₁
    have hx₂' := (helperForProposition_39_0_11_mem_singletonLinearProcess_iff (-L)).1 hx₂
    subst hx₁' hx₂'
    simp
  · intro hx
    -- Conversely, the unique points in the two singleton fibers add back to the zero vector.
    have hx0 : x = 0 := by
      simpa using hx
    subst hx0
    exact Set.mem_add.2 ⟨L u,
      (helperForProposition_39_0_11_mem_singletonLinearProcess_iff L).2 rfl,
      (-L) u,
      (helperForProposition_39_0_11_mem_singletonLinearProcess_iff (-L)).2 rfl,
      by simp⟩

/-- Helper for Proposition 39.0.11: for the one-dimensional identity lower-set process from
Example 39.0.3, fiber membership is exactly the coordinatewise order condition `0 ≤ u` and
`x ≤ u`. -/
lemma helperForProposition_39_0_11_exampleId_fiber_iff
    {A : ConvexProcess 1 1}
    (hA : A.toSetValued =
      linearLowerSetValued (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)))
    {u x : Fin 1 → ℝ} :
    x ∈ A.toSetValued u ↔ 0 ≤ u ∧ x ≤ u := by
  -- Unfold Example 39.0.3 with the identity map so the fiber inequalities are explicit.
  simp [hA, linearLowerSetValued]

/-- Helper for Proposition 39.0.11: the first distributive inclusion can be strict. -/
lemma helperForProposition_39_0_11_left_strict_counterexample :
    ∃ (n : ℕ) (A A₁ A₂ : ConvexProcess n n),
      setValuedGraph (setValuedComp A.toSetValued (addSetValued A₁ A₂)) ≠
        setValuedGraph (fun u =>
          setValuedComp A.toSetValued A₁.toSetValued u +
            setValuedComp A.toSetValued A₂.toSetValued u) := by
  let L : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := LinearMap.id
  rcases (example_39_0_3 L).1 with ⟨A, hA⟩
  let I : ConvexProcess 1 1 := helperForProposition_39_0_11_singletonLinearProcess (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
  let N : ConvexProcess 1 1 := helperForProposition_39_0_11_singletonLinearProcess (-LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
  let u1 : Fin 1 → ℝ := fun _ => 1
  refine ⟨1, A, I, N, ?_⟩
  intro hEq
  have hMid : (0 : Fin 1 → ℝ) ∈ addSetValued I N u1 := by
    -- The identity fiber and its negative cancel to the zero singleton.
    have hzeroFiber :
        addSetValued I N u1 = ({0} : Set (Fin 1 → ℝ)) := by
      simpa [I, N] using
        helperForProposition_39_0_11_add_singletonLinearProcess_neg_toSetValued
          (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) u1
    rw [hzeroFiber]
    simp
  have hZeroA : (0 : Fin 1 → ℝ) ∈ A.toSetValued (0 : Fin 1 → ℝ) := by
    rw [hA]
    exact helperForExample_39_0_3_zero_mem L
  have hLeft : (u1, (0 : Fin 1 → ℝ)) ∈
      setValuedGraph (setValuedComp A.toSetValued (addSetValued I N)) := by
    change (0 : Fin 1 → ℝ) ∈ ⋃ y ∈ addSetValued I N u1, A.toSetValued y
    refine Set.mem_iUnion.2 ?_
    refine ⟨(0 : Fin 1 → ℝ), Set.mem_iUnion.2 ?_⟩
    exact ⟨hMid, hZeroA⟩
  have hRightNot : (u1, (0 : Fin 1 → ℝ)) ∉
      setValuedGraph (fun u =>
        setValuedComp A.toSetValued I.toSetValued u +
          setValuedComp A.toSetValued N.toSetValued u) := by
    intro hp
    change (0 : Fin 1 → ℝ) ∈ setValuedComp A.toSetValued I.toSetValued u1 +
      setValuedComp A.toSetValued N.toSetValued u1 at hp
    rcases Set.mem_add.1 hp with ⟨z₁, hz₁, z₂, hz₂, _⟩
    rcases (show ∃ x₁, x₁ ∈ I.toSetValued u1 ∧ z₁ ∈ A.toSetValued x₁ by
      simpa [setValuedComp] using hz₁) with ⟨x₁, hx₁, hz₁A⟩
    rcases (show ∃ x₂, x₂ ∈ N.toSetValued u1 ∧ z₂ ∈ A.toSetValued x₂ by
      simpa [setValuedComp] using hz₂) with ⟨x₂, hx₂, hz₂A⟩
    -- Convert the singleton-process memberships into explicit formulas for the two intermediates.
    have hx₁_mem :
        x₁ ∈ (helperForProposition_39_0_11_singletonLinearProcess
          (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))).toSetValued u1 := by
      simpa [I] using hx₁
    have hx₂_mem :
        x₂ ∈ (helperForProposition_39_0_11_singletonLinearProcess
          (-LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))).toSetValued u1 := by
      simpa [N] using hx₂
    have hx₁' : x₁ = u1 := by
      simpa using
        (helperForProposition_39_0_11_mem_singletonLinearProcess_iff
          (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))).1 hx₁_mem
    have hx₂' : x₂ = -u1 := by
      simpa using
        (helperForProposition_39_0_11_mem_singletonLinearProcess_iff
          (-LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))).1 hx₂_mem
    subst hx₁' hx₂'
    -- The second summand would have to lie in the forbidden negative fiber of Example 39.0.3.
    have hz₂_nonneg : 0 ≤ (-u1 : Fin 1 → ℝ) := by
      exact (helperForProposition_39_0_11_exampleId_fiber_iff hA).1 hz₂A |>.1
    have hcoord := hz₂_nonneg 0
    norm_num [u1] at hcoord
  exact hRightNot (hEq ▸ hLeft)

/-- Helper for Proposition 39.0.11: the second distributive inclusion can be strict. -/
lemma helperForProposition_39_0_11_right_strict_counterexample :
    ∃ (n : ℕ) (A A₁ A₂ : ConvexProcess n n),
      setValuedGraph (setValuedComp (addSetValued A₁ A₂) A.toSetValued) ≠
        setValuedGraph (fun u =>
          setValuedComp A₁.toSetValued A.toSetValued u +
            setValuedComp A₂.toSetValued A.toSetValued u) := by
  let L : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := LinearMap.id
  rcases (example_39_0_3 L).1 with ⟨A, hA⟩
  let I : ConvexProcess 1 1 := helperForProposition_39_0_11_singletonLinearProcess (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
  let N : ConvexProcess 1 1 := helperForProposition_39_0_11_singletonLinearProcess (-LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ))
  let u1 : Fin 1 → ℝ := fun _ => 1
  refine ⟨1, A, I, N, ?_⟩
  intro hEq
  have hu1_nonneg : 0 ≤ u1 := by
    exact fun i => by
      fin_cases i
      norm_num [u1]
  have hOneMem : (1 : Fin 1 → ℝ) ∈ A.toSetValued u1 := by
    -- For the identity lower-set process, `1 ∈ A 1` is the tautological order bound `1 ≤ 1`.
    exact (helperForProposition_39_0_11_exampleId_fiber_iff hA).2 ⟨hu1_nonneg, by
      exact fun i => by
        fin_cases i
        norm_num [u1]⟩
  have hZeroMem : (0 : Fin 1 → ℝ) ∈ A.toSetValued u1 := by
    -- The zero vector also lies below `u1`, so it belongs to the same fiber.
    exact (helperForProposition_39_0_11_exampleId_fiber_iff hA).2 ⟨hu1_nonneg, by
      exact fun i => by
        fin_cases i
        norm_num [u1]⟩
  have hI : (1 : Fin 1 → ℝ) ∈ setValuedComp I.toSetValued A.toSetValued u1 := by
    change (1 : Fin 1 → ℝ) ∈ ⋃ y ∈ A.toSetValued u1, I.toSetValued y
    refine Set.mem_iUnion.2 ?_
    refine ⟨(1 : Fin 1 → ℝ), Set.mem_iUnion.2 ?_⟩
    exact ⟨hOneMem, by simp [I, helperForProposition_39_0_11_singletonLinearProcess_toSetValued]⟩
  have hN : (0 : Fin 1 → ℝ) ∈ setValuedComp N.toSetValued A.toSetValued u1 := by
    change (0 : Fin 1 → ℝ) ∈ ⋃ y ∈ A.toSetValued u1, N.toSetValued y
    refine Set.mem_iUnion.2 ?_
    refine ⟨(0 : Fin 1 → ℝ), Set.mem_iUnion.2 ?_⟩
    exact ⟨hZeroMem, by simp [N, helperForProposition_39_0_11_singletonLinearProcess_toSetValued]⟩
  have hRight : (u1, (1 : Fin 1 → ℝ)) ∈
      setValuedGraph (fun u =>
        setValuedComp I.toSetValued A.toSetValued u +
          setValuedComp N.toSetValued A.toSetValued u) := by
    change (1 : Fin 1 → ℝ) ∈ setValuedComp I.toSetValued A.toSetValued u1 +
      setValuedComp N.toSetValued A.toSetValued u1
    exact Set.mem_add.2 ⟨1, hI, 0, hN, by
      ext i
      fin_cases i
      simp⟩
  have hLeftNot : (u1, (1 : Fin 1 → ℝ)) ∉
      setValuedGraph (setValuedComp (addSetValued I N) A.toSetValued) := by
    intro hp
    change (1 : Fin 1 → ℝ) ∈ setValuedComp (addSetValued I N) A.toSetValued u1 at hp
    rcases (show ∃ x, x ∈ A.toSetValued u1 ∧ (1 : Fin 1 → ℝ) ∈ addSetValued I N x by
      simpa [setValuedComp] using hp) with ⟨x, hxA, hp⟩
    have hzeroFiber :
        addSetValued I N x = ({0} : Set (Fin 1 → ℝ)) := by
      simpa [I, N] using
        helperForProposition_39_0_11_add_singletonLinearProcess_neg_toSetValued
          (LinearMap.id : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ)) x
    -- Every fiber of `I + (-I)` is `{0}`, so it cannot contain the vector `1`.
    rw [hzeroFiber] at hp
    simp at hp
  exact hLeftNot (hEq.symm ▸ hRight)

/-- Helper for Proposition 39.0.11: the singleton graph `{0}` is closed under positive scaling. -/
lemma helperForProposition_39_0_11_originGraphCone_smul_mem {n : ℕ} :
    ∀ ⦃c : ℝ⦄, 0 < c → ∀ ⦃x : (Fin n → ℝ) × (Fin n → ℝ)⦄,
      x ∈ ({0} : Set ((Fin n → ℝ) × (Fin n → ℝ))) → c • x ∈ ({0} : Set ((Fin n → ℝ) × (Fin n → ℝ))) := by
  intro c hc x hx
  simp [Set.mem_singleton_iff.mp hx]

/-- Helper for Proposition 39.0.11: the singleton graph `{0}` is closed under addition. -/
lemma helperForProposition_39_0_11_originGraphCone_add_mem {n : ℕ} :
    ∀ ⦃x : (Fin n → ℝ) × (Fin n → ℝ)⦄,
      x ∈ ({0} : Set ((Fin n → ℝ) × (Fin n → ℝ))) →
        ∀ ⦃y : (Fin n → ℝ) × (Fin n → ℝ)⦄,
          y ∈ ({0} : Set ((Fin n → ℝ) × (Fin n → ℝ))) → x + y ∈ ({0} : Set ((Fin n → ℝ) × (Fin n → ℝ))) := by
  intro x hx y hy
  simp [Set.mem_singleton_iff.mp hx, Set.mem_singleton_iff.mp hy]

/-- Helper for Proposition 39.0.11: the minimal zero-containing graph cone. -/
def helperForProposition_39_0_11_originGraphCone (n : ℕ) : ConvexCone ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
  { carrier := {0}
    smul_mem' := helperForProposition_39_0_11_originGraphCone_smul_mem
    add_mem' := helperForProposition_39_0_11_originGraphCone_add_mem }

/-- Helper for Proposition 39.0.11: every convex-process graph contains the origin graph cone. -/
lemma helperForProposition_39_0_11_graph_zero_mem {n : ℕ} (A : ConvexProcess n n) :
    helperForProposition_39_0_11_originGraphCone n ≤ helperForProposition_39_0_1_graphConvexCone_ofConvexProcess A := by
  intro p hp
  have hp0 : p = 0 := by simpa [helperForProposition_39_0_11_originGraphCone] using hp
  subst hp0
  simpa [helperForProposition_39_0_11_originGraphCone, helperForProposition_39_0_1_graphConvexCone_ofConvexProcess, setValuedGraph] using A.zero_mem

/-- Helper for Proposition 39.0.11: graph equality determines the underlying set-valued mapping. -/
lemma helperForProposition_39_0_11_toSetValued_eq_of_graph_eq {n : ℕ} {A B : ConvexProcess n n}
    (hgraph : setValuedGraph A.toSetValued = setValuedGraph B.toSetValued) : A.toSetValued = B.toSetValued := by
  funext u
  ext x
  have hx := congrArg (fun S => (u, x) ∈ S) hgraph
  simpa [setValuedGraph] using hx

/-- Helper for Proposition 39.0.11: equality of underlying set-valued mappings identifies convex processes. -/
lemma helperForProposition_39_0_11_eq_of_toSetValued_eq {n : ℕ} {A B : ConvexProcess n n}
    (h : A.toSetValued = B.toSetValued) : A = B := by
  cases A
  cases B
  cases h
  simp

/-- Helper for Proposition 39.0.11: graph equality identifies convex processes. -/
lemma helperForProposition_39_0_11_eq_of_graph_eq {n : ℕ} {A B : ConvexProcess n n}
    (hgraph : setValuedGraph A.toSetValued = setValuedGraph B.toSetValued) : A = B := by
  exact helperForProposition_39_0_11_eq_of_toSetValued_eq (helperForProposition_39_0_11_toSetValued_eq_of_graph_eq hgraph)

/-- Helper for Proposition 39.0.11: reconstruct a convex process from a zero-containing graph cone. -/
lemma helperForProposition_39_0_11_exists_processOfIciCone {n : ℕ}
    (C : Set.Ici (helperForProposition_39_0_11_originGraphCone n)) :
    ∃ cp : ConvexProcess n n,
      cp.toSetValued = fun u => {x | (u, x) ∈ (C : ConvexCone ℝ ((Fin n → ℝ) × (Fin n → ℝ)))} := by
  exact helperForProposition_39_0_1_exists_convexProcess_ofGraphCone
    (fun u => {x | (u, x) ∈ (C : ConvexCone ℝ ((Fin n → ℝ) × (Fin n → ℝ)))})
    (C : ConvexCone ℝ ((Fin n → ℝ) × (Fin n → ℝ))) rfl
    (by exact C.property (by simp [helperForProposition_39_0_11_originGraphCone]))

/-- Helper for Proposition 39.0.11: choose the convex process associated to a zero-containing graph cone. -/
noncomputable def helperForProposition_39_0_11_processOfIciCone {n : ℕ}
    (C : Set.Ici (helperForProposition_39_0_11_originGraphCone n)) : ConvexProcess n n :=
  Classical.choose (helperForProposition_39_0_11_exists_processOfIciCone C)

/-- Helper for Proposition 39.0.11: the chosen process has the expected fibers. -/
lemma helperForProposition_39_0_11_processOfIciCone_toSetValued {n : ℕ}
    (C : Set.Ici (helperForProposition_39_0_11_originGraphCone n)) :
    (helperForProposition_39_0_11_processOfIciCone C).toSetValued =
      fun u => {x | (u, x) ∈ (C : ConvexCone ℝ ((Fin n → ℝ) × (Fin n → ℝ)))} := by
  exact Classical.choose_spec (helperForProposition_39_0_11_exists_processOfIciCone C)

/-- Helper for Proposition 39.0.11: passing from a convex process to its graph cone and back gives the original process. -/
lemma helperForProposition_39_0_11_processOfIciCone_left_inv {n : ℕ} (A : ConvexProcess n n) :
    helperForProposition_39_0_11_processOfIciCone
      ⟨helperForProposition_39_0_1_graphConvexCone_ofConvexProcess A, helperForProposition_39_0_11_graph_zero_mem A⟩ = A := by
  apply helperForProposition_39_0_11_eq_of_toSetValued_eq
  exact helperForProposition_39_0_11_processOfIciCone_toSetValued _

/-- Helper for Proposition 39.0.11: passing from a zero-containing graph cone to a process and back gives the original cone. -/
lemma helperForProposition_39_0_11_processOfIciCone_right_inv {n : ℕ}
    (C : Set.Ici (helperForProposition_39_0_11_originGraphCone n)) :
    (⟨helperForProposition_39_0_1_graphConvexCone_ofConvexProcess (helperForProposition_39_0_11_processOfIciCone C),
      helperForProposition_39_0_11_graph_zero_mem (helperForProposition_39_0_11_processOfIciCone C)⟩ : Set.Ici (helperForProposition_39_0_11_originGraphCone n)) = C := by
  apply Subtype.ext
  ext p
  rcases p with ⟨u, x⟩
  change x ∈ (helperForProposition_39_0_11_processOfIciCone C).toSetValued u ↔ (u, x) ∈ (C : ConvexCone ℝ ((Fin n → ℝ) × (Fin n → ℝ)))
  simp [helperForProposition_39_0_11_processOfIciCone_toSetValued]

/-- Helper for Proposition 39.0.11: graph inclusion is antisymmetric on convex processes. -/
lemma helperForProposition_39_0_11_graph_le_antisymm {n : ℕ} {A B : ConvexProcess n n}
    (hAB : setValuedGraph A.toSetValued ⊆ setValuedGraph B.toSetValued)
    (hBA : setValuedGraph B.toSetValued ⊆ setValuedGraph A.toSetValued) : A = B := by
  exact helperForProposition_39_0_11_eq_of_graph_eq (Set.Subset.antisymm hAB hBA)

/-- Helper for Proposition 39.0.11: convex processes on `ℝ^n` form a complete lattice when ordered by graph inclusion. -/
lemma helperForProposition_39_0_11_completeLattice_exists :
    ∀ n : ℕ, ∃ inst : CompleteLattice (ConvexProcess n n),
      ∀ B C, inst.le B C ↔ setValuedGraph B.toSetValued ⊆ setValuedGraph C.toSetValued := by
  intro n
  letI : LE (ConvexProcess n n) := ⟨fun B C => setValuedGraph B.toSetValued ⊆ setValuedGraph C.toSetValued⟩
  letI : PartialOrder (ConvexProcess n n) :=
    { le := (· ≤ ·)
      le_refl := fun A x hx => hx
      le_trans := fun A B C hAB hBC x hx => hBC (hAB hx)
      le_antisymm := fun A B hAB hBA => helperForProposition_39_0_11_graph_le_antisymm hAB hBA }
  let iciLift :
      ConvexCone ℝ ((Fin n → ℝ) × (Fin n → ℝ)) →
        Set.Ici (helperForProposition_39_0_11_originGraphCone n) :=
    fun C => ⟨helperForProposition_39_0_11_originGraphCone n ⊔ C,
      show helperForProposition_39_0_11_originGraphCone n ≤
          helperForProposition_39_0_11_originGraphCone n ⊔ C from
        le_sup_left⟩
  have hIciLift :
      GaloisConnection iciLift
        (fun C : Set.Ici (helperForProposition_39_0_11_originGraphCone n) =>
          (C : ConvexCone ℝ ((Fin n → ℝ) × (Fin n → ℝ)))) := by
    intro C D
    change helperForProposition_39_0_11_originGraphCone n ⊔ C ≤ D.1 ↔ C ≤ D.1
    constructor
    · intro h
      exact le_trans le_sup_right h
    · intro h
      exact sup_le D.2 h
  let graphOrderIso : ConvexProcess n n ≃o Set.Ici (helperForProposition_39_0_11_originGraphCone n) :=
    { toFun := fun A => ⟨helperForProposition_39_0_1_graphConvexCone_ofConvexProcess A, helperForProposition_39_0_11_graph_zero_mem A⟩
      invFun := helperForProposition_39_0_11_processOfIciCone
      left_inv := helperForProposition_39_0_11_processOfIciCone_left_inv
      right_inv := helperForProposition_39_0_11_processOfIciCone_right_inv
      map_rel_iff' := by intro A B; rfl }
  letI : CompleteLattice (Set.Ici (helperForProposition_39_0_11_originGraphCone n)) :=
    (hIciLift.toGaloisInsertion (fun C => by
      change C.1 ≤ helperForProposition_39_0_11_originGraphCone n ⊔ C.1
      exact le_sup_right)).liftCompleteLattice
  let inst : CompleteLattice (ConvexProcess n n) := graphOrderIso.symm.toGaloisInsertion.liftCompleteLattice
  refine ⟨inst, ?_⟩
  intro B C
  rfl

/-- Proposition 39.0.11: Distributive laws need not hold for convex processes, but one always has
the inclusions (in the sense of graphs)

`A (A₁ + A₂) ⊇ A A₁ + A A₂` and `(A₁ + A₂) A ⊆ A₁ A + A₂ A`.

Moreover, the family of convex processes from `ℝ^n` to itself is a complete lattice under
inclusion (of graphs). -/
theorem prop_39_0_11 :
    (∃ (n : ℕ) (A A₁ A₂ : ConvexProcess n n),
        setValuedGraph (setValuedComp A.toSetValued (addSetValued A₁ A₂)) ≠
          setValuedGraph (fun u =>
            setValuedComp A.toSetValued A₁.toSetValued u +
              setValuedComp A.toSetValued A₂.toSetValued u)) ∧
      (∃ (n : ℕ) (A A₁ A₂ : ConvexProcess n n),
        setValuedGraph (setValuedComp (addSetValued A₁ A₂) A.toSetValued) ≠
          setValuedGraph (fun u =>
            setValuedComp A₁.toSetValued A.toSetValued u +
              setValuedComp A₂.toSetValued A.toSetValued u)) ∧
      (∀ {n : ℕ} (A A₁ A₂ : ConvexProcess n n),
          setValuedGraph (setValuedComp A.toSetValued (addSetValued A₁ A₂)) ⊇
            setValuedGraph (fun u =>
              setValuedComp A.toSetValued A₁.toSetValued u +
                setValuedComp A.toSetValued A₂.toSetValued u)) ∧
      (∀ {n : ℕ} (A A₁ A₂ : ConvexProcess n n),
          setValuedGraph (setValuedComp (addSetValued A₁ A₂) A.toSetValued) ⊆
            setValuedGraph (fun u =>
              setValuedComp A₁.toSetValued A.toSetValued u +
                setValuedComp A₂.toSetValued A.toSetValued u)) ∧
      (∀ n : ℕ,
        ∃ inst : CompleteLattice (ConvexProcess n n),
          ∀ B C, inst.le B C ↔ setValuedGraph B.toSetValued ⊆ setValuedGraph C.toSetValued) :=
  by
  -- Assemble the proposition from the explicit strict counterexamples, the two universal graph
  -- inclusions, and the transferred complete-lattice structure.
  refine ⟨helperForProposition_39_0_11_left_strict_counterexample,
    helperForProposition_39_0_11_right_strict_counterexample,
    helperForProposition_39_0_11_left_distrib_graph_superset,
    helperForProposition_39_0_11_right_distrib_graph_subset,
    helperForProposition_39_0_11_completeLattice_exists⟩

end ConvexProcess

end Section39
end Chap08
