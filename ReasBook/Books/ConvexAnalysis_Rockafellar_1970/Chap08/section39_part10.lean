/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section38_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap08.section39_part9

open scoped Pointwise
open scoped RealInnerProductSpace
open scoped BigOperators

attribute [local instance] Classical.propDecidable

section Chap08
section Section39

namespace ConvexProcess

/-- A feasible region in `ℝ^k` is linear-program polyhedral if it is given by finitely many affine
inequalities against the Euclidean pairing `finDot`. -/
def IsLinearProgramPolyhedralSet {k : ℕ} (S : Set (Fin k → ℝ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → (Fin k → ℝ)) (b : ι → ℝ),
    S = { x | ∀ i, finDot (a i) x ≤ b i }

/-- The primal-dual extremum relation at `(u, x*)`: equality of the primal support value
`⟪A u, x*⟫` and the dual inf-support value `⟪u, A* x*⟫`. -/
def HasPrimalDualExtremumRelation {m n : ℕ} (A : ConvexProcess m n)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) : Prop :=
  setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar =
    setBracketVec ConvexSetOrientation.infimum ((adjointVec A).toSetValued xStar) u

/-- Helper for Proposition 39.4.1: a fixed primal fiber is exactly the section of the graph over
the chosen parameter `u`. -/
lemma toSetValued_eq_graphSection {m n : ℕ}
    (A : ConvexProcess m n) (u : Fin m → ℝ) :
    A.toSetValued u = {x | (u, x) ∈ setValuedGraph A.toSetValued} := by
  -- Unfold the graph definition and read the section equality fiberwise.
  ext x
  simp [setValuedGraph]

/-- Helper for Proposition 39.4.1: the restriction of a linear functional on the graph product
space to the second coordinate is a Euclidean pairing against some coefficient vector. -/
lemma linearMap_snd_eq_finDot {m n : ℕ}
    (φ : ((Fin m → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ℝ) :
    ∃ a : Fin n → ℝ, ∀ x : Fin n → ℝ, φ (0, x) = finDot (a) x := by
  let ψ : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => φ (0, x)
      map_add' := by
        intro x y
        simpa [Prod.mk_add_mk] using φ.map_add (0, x) (0, y)
      map_smul' := by
        intro r x
        simpa [Prod.smul_mk] using φ.map_smul r (0, x) }
  -- Apply the standard basis expansion of linear functionals on `Fin n → ℝ`.
  refine ⟨fun i => ψ (Pi.single i 1), ?_⟩
  intro x
  simpa [ψ, finDot, dotProduct_comm] using linearMap_eq_dotProduct_piSingle (f := ψ) x

/-- Helper for Proposition 39.4.1: a polyhedral graph cone yields a linear-program description of
each fixed primal feasible fiber. -/
lemma graphSection_isLinearProgramPolyhedral {m n : ℕ}
    (F : (Fin m → ℝ) → Set (Fin n → ℝ))
    (C : ConvexCone ℝ ((Fin m → ℝ) × (Fin n → ℝ)))
    (hgraph : (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) = setValuedGraph F)
    (hCpoly : C.IsPolyhedral) (u : Fin m → ℝ) :
    IsLinearProgramPolyhedralSet (F u) := by
  rcases hCpoly with ⟨ι, _, φ, hCφ⟩
  have hSecond :
      ∀ i : ι, ∃ a : Fin n → ℝ, ∀ x : Fin n → ℝ, φ i (0, x) = finDot a x := by
    intro i
    exact linearMap_snd_eq_finDot (φ := φ i)
  choose a ha using hSecond
  refine ⟨ι, inferInstance, fun i => -a i, fun i => φ i (u, 0), ?_⟩
  -- Freeze the `u`-coordinates of the graph inequalities and turn the remaining linear part into
  -- affine inequalities in `x`.
  ext x
  constructor
  · intro hx i
    have hxGraph : (u, x) ∈ (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) := by
      rw [hgraph]
      simpa [setValuedGraph] using hx
    have hNonneg : 0 ≤ φ i (u, x) := by
      rw [hCφ] at hxGraph
      exact hxGraph i
    have hSplit : φ i (u, x) = φ i (u, 0) + finDot (a i) x := by
      calc
        φ i (u, x) = φ i ((u, (0 : Fin n → ℝ)) + (0, x)) := by simp
        _ = φ i (u, 0) + φ i (0, x) := by rw [LinearMap.map_add]
        _ = φ i (u, 0) + finDot (a i) x := by rw [ha i x]
    have hBase : -(finDot (a i) x) ≤ φ i (u, 0) := by
      linarith [show 0 ≤ φ i (u, 0) + finDot (a i) x by simpa [hSplit] using hNonneg]
    simpa [finDot, dotProduct_comm] using hBase
  · intro hx
    have hxGraph : (u, x) ∈ (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) := by
      rw [hCφ]
      intro i
      have hBase : -(finDot (a i) x) ≤ φ i (u, 0) := by
        simpa [finDot, dotProduct_comm] using hx i
      have hNonneg : 0 ≤ φ i (u, 0) + finDot (a i) x := by
        linarith
      have hSplit : φ i (u, x) = φ i (u, 0) + finDot (a i) x := by
        calc
          φ i (u, x) = φ i ((u, (0 : Fin n → ℝ)) + (0, x)) := by simp
          _ = φ i (u, 0) + φ i (0, x) := by rw [LinearMap.map_add]
          _ = φ i (u, 0) + finDot (a i) x := by rw [ha i x]
      simpa [hSplit] using hNonneg
    rw [hgraph] at hxGraph
    simpa [setValuedGraph] using hxGraph

/-- Helper for Proposition 39.4.1: polyhedrality of `graph A` immediately gives a linear-program
description of each fixed primal feasible set. -/
lemma toSetValued_isLinearProgramPolyhedral {m n : ℕ}
    (A : ConvexProcess m n) (u : Fin m → ℝ) (hPoly : A.IsPolyhedral) :
    IsLinearProgramPolyhedralSet (A.toSetValued u) := by
  rcases hPoly with ⟨C, hgraph, hCpoly⟩
  -- Reuse the graph-section lemma once the polyhedral graph cone witness is unpacked.
  exact
    graphSection_isLinearProgramPolyhedral
      A.toSetValued C hgraph hCpoly u

/-- Helper for Proposition 39.4.1: membership in the adjoint graph is exactly the polar-cone
condition for the graph of `A`, evaluated at the pair `(-u*, x*)`. -/
lemma adjointVec_graph_mem_iff_polar {m n : ℕ}
    (A : ConvexProcess m n) (xStar : Fin n → ℝ) (uStar : Fin m → ℝ) :
    ((xStar, uStar) ∈ setValuedGraph (adjointVec A).toSetValued) ↔
      ∀ u x, x ∈ A.toSetValued u → finDot x xStar - finDot u uStar ≤ 0 := by
  constructor
  · intro h
    -- Unfold the adjoint fiber and rewrite the graph condition as the defining scalar inequality.
    change uStar ∈ setValuedAdjointVec A.toSetValued xStar at h
    intro u x hx
    have hineq : finDot u uStar ≥ finDot x xStar := h u x hx
    simpa [finDot, dotProduct_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      sub_nonpos.mpr hineq
  · intro h
    -- Read the scalar inequality back as the defining adjoint inequality fiberwise.
    change uStar ∈ setValuedAdjointVec A.toSetValued xStar
    intro u x hx
    have hle : finDot x xStar - finDot u uStar ≤ 0 := h u x hx
    simpa [finDot, dotProduct_comm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      sub_nonpos.mp hle

/-- Helper for Proposition 39.4.1: unpack a vector in `ℝ^(m+n)` into its `u`- and `x`-blocks. -/
def unpackAppend {m n : ℕ}
    (z : Fin (m + n) → ℝ) : (Fin m → ℝ) × (Fin n → ℝ) :=
  (fun i => z (Fin.castAdd n i), fun j => z (Fin.natAdd m j))

/-- Helper for Proposition 39.4.1: splitting packed coordinates is additive. -/
lemma unpackAppend_add {m n : ℕ}
    (z w : Fin (m + n) → ℝ) :
    unpackAppend (z + w) = unpackAppend z + unpackAppend w := by
  -- Check the left and right coordinate blocks separately.
  ext <;> rfl

/-- Helper for Proposition 39.4.1: splitting packed coordinates commutes with scalar
multiplication. -/
lemma unpackAppend_smul {m n : ℕ}
    (r : ℝ) (z : Fin (m + n) → ℝ) :
    unpackAppend (r • z) = r • unpackAppend z := by
  -- Again, the statement is coordinatewise on the left and right blocks.
  ext <;> rfl

/-- Helper for Proposition 39.4.1: the packed-coordinate splitting map is linear. -/
def unpackAppendLinearMap {m n : ℕ} :
    (Fin (m + n) → ℝ) →ₗ[ℝ] ((Fin m → ℝ) × (Fin n → ℝ)) :=
  { toFun := unpackAppend
    map_add' := unpackAppend_add
    map_smul' := unpackAppend_smul }

/-- Helper for Proposition 39.4.1: splitting the packed vector `Fin.append u x` recovers `(u, x)`. -/
lemma unpackAppend_append {m n : ℕ}
    (u : Fin m → ℝ) (x : Fin n → ℝ) :
    unpackAppend (Fin.append u x) = (u, x) := by
  -- The `Fin.append` coordinates are built so that the left and right blocks read off `u` and `x`.
  ext <;> simp [unpackAppend]

/-- Helper for Proposition 39.4.1: repacking the split blocks of `z` gives back `z`. -/
lemma append_unpackAppend {m n : ℕ}
    (z : Fin (m + n) → ℝ) :
    Fin.append
        (unpackAppend z).1
        (unpackAppend z).2 = z := by
  -- Each packed coordinate lies either in the left `u`-block or in the right `x`-block.
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [unpackAppend]
  · intro j
    simp [unpackAppend]

/-- Helper for Proposition 39.4.1: encoding product points by `Fin.append` turns the polyhedral
graph cone of `A` into a polyhedral convex set in `ℝ^(m+n)`. -/
lemma packedGraph_isPolyhedral {m n : ℕ}
    (A : ConvexProcess m n) (hPoly : A.IsPolyhedral) :
    IsPolyhedralConvexSet (m + n)
      ((fun p : (Fin m → ℝ) × (Fin n → ℝ) => Fin.append p.1 p.2) '' setValuedGraph A.toSetValued) := by
  rcases hPoly with ⟨C, hgraph, hCpoly⟩
  rcases hCpoly with ⟨ι, _, φ, hCφ⟩
  have hPacked :
      ∀ i : ι, ∃ b : Fin (m + n) → ℝ, ∀ z : Fin (m + n) → ℝ,
        ((φ i).comp (unpackAppendLinearMap
          (m := m) (n := n))) z = finDot z b := by
    intro i
    -- Express each transported linear functional as a Euclidean pairing against one packed vector.
    refine ⟨fun j =>
      ((φ i).comp (unpackAppendLinearMap
        (m := m) (n := n))) (Pi.single j 1), ?_⟩
    intro z
    simpa [finDot, dotProduct_comm] using
      linearMap_eq_dotProduct_piSingle
        (f := (φ i).comp
          (unpackAppendLinearMap (m := m) (n := n))) z
  choose b hb using hPacked
  refine ⟨ι, inferInstance, fun i => -b i, fun _ => 0, ?_⟩
  -- Re-express graph membership in packed coordinates and flip the homogeneous inequalities into
  -- `closedHalfSpaceLE` form.
  ext z
  constructor
  · rintro ⟨p, hpGraph, rfl⟩
    have hpC : p ∈ (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) := by
      rw [hgraph]
      exact hpGraph
    rw [hCφ] at hpC
    simp [closedHalfSpaceLE]
    intro i
    have hi : 0 ≤ φ i p := hpC i
    have hEval :
        φ i p = finDot (Fin.append p.1 p.2) (b i) := by
      simpa [unpackAppendLinearMap, LinearMap.comp_apply, unpackAppend_append] using
        hb i (Fin.append p.1 p.2)
    have hiPacked : 0 ≤ finDot (Fin.append p.1 p.2) (b i) := by
      simpa [hEval] using hi
    simpa [finDot, dotProduct_comm] using neg_nonpos.mpr hiPacked
  · intro hz
    have hzC : unpackAppend z ∈
        (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) := by
      rw [hCφ]
      intro i
      have hi :
          finDot z (-b i) ≤ 0 := by
        have hiMem : z ∈ closedHalfSpaceLE (m + n) (-b i) 0 := by
          exact Set.mem_iInter.mp hz i
        simpa [closedHalfSpaceLE, finDot] using hiMem
      have hiPacked : 0 ≤ finDot z (b i) := by
        have hiNeg : -(finDot z (b i)) ≤ 0 := by
          simpa [finDot, dotProduct_comm] using hi
        exact neg_nonpos.mp hiNeg
      rw [show (φ i) (unpackAppend z) =
          finDot z (b i) by
            simpa [unpackAppendLinearMap,
              LinearMap.comp_apply] using hb i z]
      exact hiPacked
    refine ⟨unpackAppend z, ?_, ?_⟩
    · rw [← hgraph]
      exact hzC
    · exact append_unpackAppend (m := m) (n := n) z

/-- Helper for Proposition 39.4.1: the packed vector `Fin.append (-u*) x*` evaluates a packed
constraint vector by splitting into the `u*` and `x*` coordinates. -/
lemma dotProduct_append_neg_eq {m n : ℕ}
    (uStar : Fin m → ℝ) (xStar : Fin n → ℝ) (b : Fin (m + n) → ℝ) :
    dotProduct (Fin.append (-uStar) xStar) b =
      - finDot uStar (fun i => b (Fin.castAdd n i)) +
        finDot xStar (fun j => b (Fin.natAdd m j)) := by
  -- Split the packed dot product along the left and right coordinate blocks.
  simp [finDot, dotProduct, Fin.sum_univ_add, mul_comm]

/-- Helper for Proposition 39.4.1: pairing the packed primal point `Fin.append u x` with the packed
dual vector `Fin.append (-u*) x*` reproduces the scalar `⟪x,x*⟫ - ⟪u,u*⟫`. -/
lemma dotProduct_append_primalDual_eq {m n : ℕ}
    (u : Fin m → ℝ) (x : Fin n → ℝ) (uStar : Fin m → ℝ) (xStar : Fin n → ℝ) :
    dotProduct (Fin.append u x) (Fin.append (-uStar) xStar) =
      finDot x xStar - finDot u uStar := by
  -- Split the packed dot product into its left and right blocks and simplify signs.
  simp [finDot, dotProduct, Fin.sum_univ_add, sub_eq_add_neg, add_comm]

/-- Helper for Proposition 39.4.1: the dual linear-program statement should follow from a
polyhedral graph description of the adjoint process. -/
lemma adjointFiber_isLinearProgramPolyhedral {m n : ℕ}
    (A : ConvexProcess m n) (xStar : Fin n → ℝ) (hPoly : A.IsPolyhedral) :
    IsLinearProgramPolyhedralSet ((adjointVec A).toSetValued xStar) := by
  rcases hPoly with ⟨C, hgraph, hCpoly⟩
  let coordGraph : Set (Fin (m + n) → ℝ) :=
    (fun p : (Fin m → ℝ) × (Fin n → ℝ) => Fin.append p.1 p.2) '' setValuedGraph A.toSetValued
  let coordCone : ConvexCone ℝ (Fin (m + n) → ℝ) :=
    C.comap (unpackAppendLinearMap (m := m) (n := n))
  have hcoordSet : (coordCone : Set (Fin (m + n) → ℝ)) = coordGraph := by
    -- A packed point belongs to the transported cone exactly when its unpacked pair lies in `graph A`.
    ext z
    constructor
    · intro hz
      have hzC :
          unpackAppend z ∈
            (C : Set ((Fin m → ℝ) × (Fin n → ℝ))) := by
        exact hz
      refine ⟨unpackAppend z, ?_, ?_⟩
      · rw [← hgraph]
        exact hzC
      · exact append_unpackAppend (m := m) (n := n) z
    · rintro ⟨p, hpGraph, rfl⟩
      change unpackAppend
          (Fin.append p.1 p.2) ∈ (C : Set ((Fin m → ℝ) × (Fin n → ℝ)))
      rw [hgraph]
      simpa [unpackAppend_append]
  have hcoordPoly : IsPolyhedralConvexSet (m + n) coordGraph := by
    -- Reuse the coordinate graph lemma after unfolding the local abbreviation.
    simpa [coordGraph] using
      packedGraph_isPolyhedral
        (A := A) (hPoly := ⟨C, hgraph, hCpoly⟩)
  have hcoordNonempty : (coordCone : Set (Fin (m + n) → ℝ)).Nonempty := by
    refine ⟨0, ?_⟩
    rw [hcoordSet]
    refine ⟨(0, 0), ?_, ?_⟩
    simpa [setValuedGraph] using A.zero_mem
    simpa [unpackAppend] using
      append_unpackAppend (m := m) (n := n) (z := 0)
  let polarPacked : Set (Fin (m + n) → ℝ) :=
    {y | ∀ z, z ∈ coordGraph → dotProduct z y ≤ 0}
  have hsupport :
      supportFunctionEReal coordGraph = indicatorFunction polarPacked := by
    -- For the transported cone, Chapter 16 identifies the support function with the indicator of
    -- the Euclidean polar cone.
    simpa [polarPacked, hcoordSet] using
      section16_supportFunctionEReal_convexCone_eq_indicatorFunction_polar
        (K := coordCone) hcoordNonempty
  have hpolarEq :
      {y | supportFunctionEReal coordGraph y ≤ (1 : EReal)} = polarPacked := by
    -- On a cone the support function is either `0` on the polar or `⊤` off the polar.
    ext y
    constructor
    · intro hyMem
      by_cases hy : y ∈ polarPacked
      · exact hy
      · have : indicatorFunction polarPacked y ≤ (1 : EReal) := by
          simpa [hsupport] using hyMem
        have hfalse : False := by
          have hone_ne_top : (1 : EReal) ≠ ⊤ := by
            simpa using EReal.natCast_ne_top 1
          exact hone_ne_top (by simpa [indicatorFunction, hy] using this)
        exact hfalse.elim
    · intro hy
      have : indicatorFunction polarPacked y ≤ (1 : EReal) := by
        simp [indicatorFunction, hy]
      simpa [hsupport] using this
  have hpolarPoly : IsPolyhedralConvexSet (m + n) polarPacked := by
    -- Apply the Chapter 19 polar-polyhedrality theorem to the packed graph set.
    simpa [hpolarEq] using
      polyhedral_convexSet_polar_polyhedral (m + n) coordGraph hcoordPoly
  rcases hpolarPoly with ⟨ι, _, b, β, hpolarHalfspaces⟩
  refine ⟨ι, inferInstance,
    fun i j => -b i (Fin.castAdd n j),
    fun i => β i - finDot xStar (fun j => b i (Fin.natAdd m j)), ?_⟩
  -- Freeze the `x*` block of the packed polar inequalities to obtain affine inequalities in `u*`.
  ext uStar
  have hPackedMembership :
      uStar ∈ (adjointVec A).toSetValued xStar ↔ Fin.append (-uStar) xStar ∈ polarPacked := by
    constructor
    · intro huStar
      have hAdjointIneq :
          ∀ u x, x ∈ A.toSetValued u → finDot x xStar - finDot u uStar ≤ 0 := by
        have hGraph :
            (xStar, uStar) ∈ setValuedGraph (adjointVec A).toSetValued := by
          simpa [setValuedGraph] using huStar
        exact
          (adjointVec_graph_mem_iff_polar (A := A) xStar uStar).1 hGraph
      intro z hz
      rcases hz with ⟨p, hpGraph, rfl⟩
      rcases p with ⟨u, x⟩
      have hx : x ∈ A.toSetValued u := by
        simpa [setValuedGraph] using hpGraph
      simpa [polarPacked, dotProduct_append_primalDual_eq]
        using hAdjointIneq u x hx
    · intro huPacked
      have hAdjointIneq :
          ∀ u x, x ∈ A.toSetValued u → finDot x xStar - finDot u uStar ≤ 0 := by
        intro u x hx
        have hz :
            Fin.append u x ∈ coordGraph := by
          refine ⟨(u, x), ?_, rfl⟩
          simpa [setValuedGraph] using hx
        simpa [polarPacked, dotProduct_append_primalDual_eq]
          using huPacked (Fin.append u x) hz
      have hGraph :
          (xStar, uStar) ∈ setValuedGraph (adjointVec A).toSetValued :=
        (adjointVec_graph_mem_iff_polar (A := A) xStar uStar).2 hAdjointIneq
      simpa [setValuedGraph] using hGraph
  constructor
  · intro huStar
    have huPacked : Fin.append (-uStar) xStar ∈ polarPacked := (hPackedMembership.1 huStar)
    rw [hpolarHalfspaces] at huPacked
    intro i
    have hi : dotProduct (Fin.append (-uStar) xStar) (b i) ≤ β i := by
      have hiMem : Fin.append (-uStar) xStar ∈ closedHalfSpaceLE (m + n) (b i) (β i) := by
        exact Set.mem_iInter.mp huPacked i
      simpa [closedHalfSpaceLE] using hiMem
    have hiPacked :
        - finDot uStar (fun j => b i (Fin.castAdd n j)) +
          finDot xStar (fun j => b i (Fin.natAdd m j)) ≤ β i := by
      simpa [dotProduct_append_neg_eq] using hi
    have hleft :
        finDot (fun j => -b i (Fin.castAdd n j)) uStar =
          - finDot uStar (fun j => b i (Fin.castAdd n j)) := by
      have hneg :
          finDot (fun j => -b i (Fin.castAdd n j)) uStar =
            - finDot (fun j => b i (Fin.castAdd n j)) uStar := by
        simp [finDot, dotProduct]
      have hcomm :
          finDot (fun j => b i (Fin.castAdd n j)) uStar =
            finDot uStar (fun j => b i (Fin.castAdd n j)) := by
        simp [finDot, dotProduct_comm]
      calc
        finDot (fun j => -b i (Fin.castAdd n j)) uStar =
            - finDot (fun j => b i (Fin.castAdd n j)) uStar := hneg
        _ = - finDot uStar (fun j => b i (Fin.castAdd n j)) := by
              rw [hcomm]
    rw [hleft]
    linarith
  · intro huStar
    have huPacked : Fin.append (-uStar) xStar ∈ polarPacked := by
      rw [hpolarHalfspaces]
      refine Set.mem_iInter.mpr ?_
      intro i
      have hi :
          finDot (fun j => -b i (Fin.castAdd n j)) uStar ≤
            β i - finDot xStar (fun j => b i (Fin.natAdd m j)) := huStar i
      have hleft :
          finDot (fun j => -b i (Fin.castAdd n j)) uStar =
            - finDot uStar (fun j => b i (Fin.castAdd n j)) := by
        have hneg :
            finDot (fun j => -b i (Fin.castAdd n j)) uStar =
              - finDot (fun j => b i (Fin.castAdd n j)) uStar := by
          simp [finDot, dotProduct]
        have hcomm :
            finDot (fun j => b i (Fin.castAdd n j)) uStar =
              finDot uStar (fun j => b i (Fin.castAdd n j)) := by
          simp [finDot, dotProduct_comm]
        calc
          finDot (fun j => -b i (Fin.castAdd n j)) uStar =
              - finDot (fun j => b i (Fin.castAdd n j)) uStar := hneg
          _ = - finDot uStar (fun j => b i (Fin.castAdd n j)) := by
                rw [hcomm]
      have hiPacked :
          - finDot uStar (fun j => b i (Fin.castAdd n j)) +
            finDot xStar (fun j => b i (Fin.natAdd m j)) ≤ β i := by
        rw [← hleft]
        linarith
      simpa [closedHalfSpaceLE, dotProduct_append_neg_eq]
        using hiPacked
    exact hPackedMembership.2 huPacked

-- Proof sketch: Unfold `setBracketVec` in supremum and infimum orientation to obtain the explicit
-- `sup`/`inf` formulas. The primal-dual clause is the defining equality. For the polyhedral claim,
-- use the polyhedral-graph hypothesis and projection/section arguments to obtain finite inequality
-- descriptions of the fixed-`u` and fixed-`x*` feasible regions.
/-- Proposition 39.4.1: Let `A` be a supremum-oriented convex process and `A*` its adjoint.
For fixed `u` and `x*`,

`⟪A u, x*⟫ = sup {⟪x, x*⟫ | x ∈ A u}` and
`⟪u, A* x*⟫ = inf {⟪u, u*⟫ | u* ∈ A* x*}`.

When these two values are equal, this is the primal-dual extremum relation. If `A` is polyhedral,
the primal and dual feasible sets (for this fixed `u, x*`) are linear-program polyhedra. -/
theorem prop_39_4_1 {m n : ℕ} (A : ConvexProcess m n) (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar =
      sSup ((fun x : Fin n → ℝ => ((finDot x xStar : ℝ) : EReal)) '' A.toSetValued u) ∧
      setBracketVec ConvexSetOrientation.infimum ((adjointVec A).toSetValued xStar) u =
        sInf ((fun uStar : Fin m → ℝ => ((finDot u uStar : ℝ) : EReal)) ''
          (adjointVec A).toSetValued xStar) ∧
      ((setBracketVec ConvexSetOrientation.supremum (A.toSetValued u) xStar =
          setBracketVec ConvexSetOrientation.infimum ((adjointVec A).toSetValued xStar) u) →
        HasPrimalDualExtremumRelation A u xStar) ∧
      (A.IsPolyhedral →
        IsLinearProgramPolyhedralSet (A.toSetValued u) ∧
          IsLinearProgramPolyhedralSet ((adjointVec A).toSetValued xStar)) :=
  by
  refine ⟨?_, ?_⟩
  · -- Step 1: the primal bracket formula is exactly the supremum branch of `setBracketVec`.
    simp [setBracketVec]
  refine ⟨?_, ?_⟩
  · -- Step 2: the dual bracket formula is exactly the infimum branch of `setBracketVec`.
    simp [setBracketVec, finDot, dotProduct_comm]
  refine ⟨?_, ?_⟩
  · intro hEq
    -- Step 3: the primal-dual extremum relation is definitionally this equality.
    simpa [HasPrimalDualExtremumRelation] using hEq
  · intro hPoly
    -- Step 4: the primal LP description is proved from the graph cone, while the dual branch is
    -- isolated behind the adjoint-graph blocker recorded in the helper below.
    refine ⟨
      toSetValued_isLinearProgramPolyhedral A u hPoly,
      adjointFiber_isLinearProgramPolyhedral A xStar hPoly⟩

-- Proof sketch: For the bracket, expand `setBracketVec` as a supremum of `finDot x x*` over the
-- lower set `{x | x ≤ B u}`: if `u` has a negative component the feasible set is empty, while for
-- `u ≥ 0` the supremum is attained at `x = B u` exactly when `x* ≥ 0`, and otherwise can be pushed
-- to `+∞` along negative coordinate directions. For the adjoint formulas, unfold
-- `setValuedAdjointVec` (and `setValuedInverse`) and compute the resulting inequalities using the
-- same coordinatewise order analysis; the linear map `Bstar` plays the role of `B^*` for the
-- Euclidean pairing.
/-- Helper for Proposition 39.4.2: in the one-dimensional zero-map model, the inverse-adjoint
fiber at `u* = 1` is empty, because the graph point `(u, x) = (1, 0)` forces the impossible
inequality `0 ≥ 1`. -/
lemma zeroMap_inverseAdjointFiberAtOne_eq_empty :
    let B : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := 0
    let A : (Fin 1 → ℝ) → Set (Fin 1 → ℝ) :=
      fun u => if 0 ≤ u then { x | x ≤ B u } else (∅ : Set (Fin 1 → ℝ))
    let uStar : Fin 1 → ℝ := fun _ => 1
    setValuedAdjointVec (setValuedInverse A) uStar = (∅ : Set (Fin 1 → ℝ)) := by
  dsimp
  ext xStar
  constructor
  · intro hx
    exfalso
    -- The feasible graph point `(u, x) = (1, 0)` survives inversion and forces a contradiction.
    have hu_nonneg : (0 : Fin 1 → ℝ) ≤ (fun _ => (1 : ℝ)) := by
      intro i
      fin_cases i
      norm_num
    have hmem : (fun _ => (1 : ℝ)) ∈
        setValuedInverse (fun u : Fin 1 → ℝ => if 0 ≤ u then {x : Fin 1 → ℝ | x ≤ 0} else ∅)
          (0 : Fin 1 → ℝ) := by
      change (0 : Fin 1 → ℝ) ∈ if 0 ≤ (fun _ => (1 : ℝ)) then {x : Fin 1 → ℝ | x ≤ 0} else ∅
      simp [hu_nonneg]
    have hineq := hx (0 : Fin 1 → ℝ) (fun _ => (1 : ℝ)) hmem
    have hzero : finDot (0 : Fin 1 → ℝ) xStar = 0 := by
      simp [finDot, dotProduct]
    have hone : finDot (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
      simp [finDot, dotProduct]
    have : (1 : ℝ) ≤ 0 := by
      simpa [hzero, hone] using hineq
    norm_num at this
  · intro hx
    exfalso
    simp at hx

/-- Helper for Proposition 39.4.2: for the one-dimensional zero map, the candidate right-hand side
of the displayed `(A⁻¹)*` formula contains `x* = 1` at `u* = 1`, while the actual inverse-adjoint
fiber excludes that vector. -/
lemma zeroMap_inverseAdjointCounterexample :
    let B : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := 0
    let A : (Fin 1 → ℝ) → Set (Fin 1 → ℝ) :=
      fun u => if 0 ≤ u then { x | x ≤ B u } else (∅ : Set (Fin 1 → ℝ))
    let uStar : Fin 1 → ℝ := fun _ => 1
    let xStar : Fin 1 → ℝ := fun _ => 1
    xStar ∈ { y : Fin 1 → ℝ | 0 ≤ y ∧ B y ≤ uStar } ∧
      xStar ∉ setValuedAdjointVec (setValuedInverse A) uStar := by
  dsimp
  constructor
  · -- The claimed right-hand side only asks for componentwise nonnegativity and the trivial
    -- inequality `0 ≤ 1`, so `x* = 1` belongs to it.
    constructor
    · intro i
      fin_cases i
      norm_num
    · intro i
      fin_cases i
      norm_num
  · -- Reuse the sharper emptiness computation of the actual inverse-adjoint fiber at `u* = 1`.
    have hEmpty :
        setValuedAdjointVec
            (setValuedInverse
              (fun u : Fin 1 → ℝ => if 0 ≤ u then {x : Fin 1 → ℝ | x ≤ 0} else ∅))
            (fun _ => (1 : ℝ)) =
          (∅ : Set (Fin 1 → ℝ)) := by
      simpa using zeroMap_inverseAdjointFiberAtOne_eq_empty
    rw [hEmpty]
    simp

/-- Helper for Proposition 39.4.2: specializing the target conjunction to the one-dimensional zero
map contradicts the actual inverse-adjoint fiber, so the displayed third branch is false under the
current definitions. -/
lemma zeroMap_targetConjunctionFalse :
    let B : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := 0
    let Bstar : (Fin 1 → ℝ) →ₗ[ℝ] (Fin 1 → ℝ) := 0
    let A : (Fin 1 → ℝ) → Set (Fin 1 → ℝ) :=
      fun u => if 0 ≤ u then { x | x ≤ B u } else (∅ : Set (Fin 1 → ℝ))
    ¬ ((∀ u xStar,
        setBracketVec ConvexSetOrientation.supremum (A u) xStar =
          if 0 ≤ u then
            if 0 ≤ xStar then ((finDot (B u) xStar : ℝ) : EReal) else (⊤ : EReal)
          else (⊥ : EReal)) ∧
      (∀ xStar,
        setValuedAdjointVec A xStar =
          if 0 ≤ xStar then { uStar | uStar ≥ Bstar xStar } else (∅ : Set (Fin 1 → ℝ))) ∧
      (∀ uStar,
        setValuedAdjointVec (setValuedInverse A) uStar =
          { xStar | 0 ≤ xStar ∧ Bstar xStar ≤ uStar })) := by
  dsimp
  intro hTarget
  rcases hTarget with ⟨_, hTail⟩
  rcases hTail with ⟨_, hInverseAdjoint⟩
  have hSetEq := hInverseAdjoint (fun _ => (1 : ℝ))
  rcases zeroMap_inverseAdjointCounterexample with
    ⟨hMemCandidateFiber, hNotMemActualFiber⟩
  -- The target equality would put the counterexample point into the actual inverse-adjoint fiber.
  have hMemActualFiber :
      (fun _ => (1 : ℝ)) ∈
        setValuedAdjointVec
          (setValuedInverse (fun u : Fin 1 → ℝ => if 0 ≤ u then {x : Fin 1 → ℝ | x ≤ 0} else ∅))
          (fun _ => (1 : ℝ)) := by
    rw [hSetEq]
    exact hMemCandidateFiber
  exact hNotMemActualFiber hMemActualFiber

/-- Helper for Proposition 39.4.2: if a covector is not componentwise nonnegative, then some
coordinate is strictly negative. -/
lemma helperForProposition_39_4_2_exists_negative_coordinate_of_not_nonneg {n : ℕ}
    {xStar : Fin n → ℝ} (hxStar : ¬ 0 ≤ xStar) :
    ∃ i, xStar i < 0 := by
  classical
  by_contra hneg
  apply hxStar
  -- Convert the failure of every strict negativity witness into componentwise nonnegativity.
  intro i
  exact not_lt.mp (fun hi => hneg ⟨i, hi⟩)

/-- Helper for Proposition 39.4.2: when `u ≥ 0` and `x* ≥ 0`, the support of the lower set
`{x | x ≤ B u}` is attained at its maximal point `B u`. -/
lemma bracket_eq_finDot_of_nonneg_covector {n : ℕ}
    (B : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) {u xStar : Fin n → ℝ}
    (hu : 0 ≤ u) (hxStar : 0 ≤ xStar) :
    setBracketVec ConvexSetOrientation.supremum
      (if 0 ≤ u then { x : Fin n → ℝ | x ≤ B u } else (∅ : Set (Fin n → ℝ))) xStar =
      ((finDot (B u) xStar : ℝ) : EReal) := by
  -- With `u ≥ 0`, only the lower-set fiber `{x | x ≤ B u}` remains.
  simp [setBracketVec, hu]
  apply le_antisymm
  · -- Every feasible `x` lies below `B u`, so nonnegativity of `x*` bounds the dot product above.
    refine sSup_le ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    change (((dotProduct x xStar : ℝ) : EReal) ≤ ((dotProduct (B u) xStar : ℝ) : EReal))
    exact_mod_cast (dotProduct_le_dotProduct_of_nonneg_right hx hxStar)
  · -- The maximal feasible point `x = B u` realizes the upper bound.
    refine le_sSup ?_
    refine ⟨B u, ?_, rfl⟩
    simp

/-- Helper for Proposition 39.4.2: when `u ≥ 0` but `x*` has a negative coordinate, the support of
the lower set `{x | x ≤ B u}` is `+∞` because one can move arbitrarily far in a negative coordinate
direction. -/
lemma bracket_eq_top_of_negative_covector {n : ℕ}
    (B : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) {u xStar : Fin n → ℝ}
    (hu : 0 ≤ u) (hxStar : ¬ 0 ≤ xStar) :
    setBracketVec ConvexSetOrientation.supremum
      (if 0 ≤ u then { x : Fin n → ℝ | x ≤ B u } else (∅ : Set (Fin n → ℝ))) xStar =
      (⊤ : EReal) := by
  -- With `u ≥ 0`, the fiber is again the lower set under `B u`.
  simp [setBracketVec, hu]
  rcases helperForProposition_39_4_2_exists_negative_coordinate_of_not_nonneg hxStar with
    ⟨i, hi⟩
  refine (EReal.eq_top_iff_forall_lt _).2 ?_
  intro μ
  let t : ℝ := (|μ - finDot (B u) xStar| + 1) / (-xStar i)
  let x : Fin n → ℝ := B u + Pi.single i (-t)
  have hden : 0 < -xStar i := by
    simpa using neg_pos.mpr hi
  have htpos : 0 < t := by
    -- The denominator is positive because `x* i < 0`, and the numerator is strictly positive.
    have hnum : 0 < |μ - finDot (B u) xStar| + 1 := by
      exact add_pos_of_nonneg_of_pos (abs_nonneg _) zero_lt_one
    exact div_pos hnum hden
  have hx_mem : x ∈ {x : Fin n → ℝ | x ≤ B u} := by
    -- Decreasing only the `i`-th coordinate keeps the point inside the lower set.
    intro j
    by_cases hji : j = i
    · subst hji
      simp [x, t, htpos.le]
    · simp [x, hji]
  have hdot : finDot x xStar = finDot (B u) xStar + t * (-xStar i) := by
    -- The chosen perturbation contributes only the `i`-th coordinate.
    calc
      finDot x xStar = finDot (B u + Pi.single i (-t)) xStar := by rfl
      _ = finDot (B u) xStar + finDot (Pi.single i (-t)) xStar := by
        simp [finDot]
      _ = finDot (B u) xStar + t * (-xStar i) := by
        simp [finDot, mul_comm]
  have htmul : t * (-xStar i) = |μ - finDot (B u) xStar| + 1 := by
    have hxi : xStar i ≠ 0 := ne_of_lt hi
    calc
      t * (-xStar i) = ((|μ - finDot (B u) xStar| + 1) / (-xStar i)) * (-xStar i) := by
        rfl
      _ = |μ - finDot (B u) xStar| + 1 := by
        field_simp [hxi]
  have hdot_eq : finDot x xStar = finDot (B u) xStar + (|μ - finDot (B u) xStar| + 1) := by
    -- The definition of `t` is engineered so that the extra term is exactly `|μ - ⟪B u,x*⟫| + 1`.
    calc
      finDot x xStar = finDot (B u) xStar + t * (-xStar i) := hdot
      _ = finDot (B u) xStar + (|μ - finDot (B u) xStar| + 1) := by
        rw [htmul]
  have hlt_real : μ < finDot (B u) xStar + (|μ - finDot (B u) xStar| + 1) := by
    -- The absolute-value term is large enough to dominate the gap from `μ` to `⟪B u,x*⟫`.
    have habs : μ - finDot (B u) xStar ≤ |μ - finDot (B u) xStar| := le_abs_self _
    have hμle : μ ≤ finDot (B u) xStar + |μ - finDot (B u) xStar| := by
      have := add_le_add_right habs (finDot (B u) xStar)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
    have hstep : finDot (B u) xStar + |μ - finDot (B u) xStar| <
        finDot (B u) xStar + (|μ - finDot (B u) xStar| + 1) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_lt_add_left (lt_add_of_pos_right (|μ - finDot (B u) xStar|) zero_lt_one)
          (finDot (B u) xStar)
    exact lt_of_le_of_lt hμle hstep
  have hmem :
      (((finDot (B u) xStar + (|μ - finDot (B u) xStar| + 1)) : ℝ) : EReal) ∈
        (fun x : Fin n → ℝ => ((finDot x xStar : ℝ) : EReal)) '' {x : Fin n → ℝ | x ≤ B u} := by
    -- The explicit point `x` witnesses an image value strictly larger than `μ`.
    refine ⟨x, hx_mem, ?_⟩
    simp [hdot_eq]
  have hle :
      (((finDot (B u) xStar + (|μ - finDot (B u) xStar| + 1)) : ℝ) : EReal) ≤
        sSup ((fun x : Fin n → ℝ => ((finDot x xStar : ℝ) : EReal)) '' {x : Fin n → ℝ | x ≤ B u}) :=
    le_sSup hmem
  exact lt_of_lt_of_le (by exact_mod_cast hlt_real) hle

/-- Helper for Proposition 39.4.2: for a componentwise nonnegative covector `x*`, the adjoint
fiber consists exactly of the covectors `u*` dominating `Bstar x*`. -/
lemma adjoint_eq_upperSet_of_nonneg_covector {n : ℕ}
    (B Bstar : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hBstar : ∀ u xStar, finDot (B u) xStar = finDot u (Bstar xStar))
    {xStar : Fin n → ℝ} (hxStar : 0 ≤ xStar) :
    setValuedAdjointVec
      (fun u : Fin n → ℝ => if 0 ≤ u then { x | x ≤ B u } else (∅ : Set (Fin n → ℝ))) xStar =
      { uStar | uStar ≥ Bstar xStar } := by
  ext uStar
  constructor
  · intro huStar
    intro i
    let u : Fin n → ℝ := Pi.single i (1 : ℝ)
    have hu_nonneg : (0 : Fin n → ℝ) ≤ u := by
      -- The basis vector `e_i` is componentwise nonnegative.
      intro j
      by_cases hji : j = i
      · subst hji
        simp [u]
      · simp [u, hji]
    have hx_mem :
        B u ∈ (if 0 ≤ u then {x : Fin n → ℝ | x ≤ B u} else (∅ : Set (Fin n → ℝ))) := by
      -- The maximal point `B u` belongs to its own lower set.
      simp [hu_nonneg]
    have hineq := huStar u (B u) hx_mem
    have hucoord : finDot u uStar = uStar i := by
      simp [finDot, u]
    have hBcoord : finDot (B u) xStar = (Bstar xStar) i := by
      rw [hBstar u xStar]
      simp [finDot, u]
    -- Testing the adjoint inequality on `u = e_i` recovers the `i`-th coordinate inequality.
    simpa [hucoord, hBcoord] using hineq
  · intro huStar
    intro u x hx
    have hx' : 0 ≤ u ∧ x ≤ B u := by
      -- Unfold membership in the lower-set process fiber.
      by_cases hu : 0 ≤ u
      · simpa [hu] using hx
      · simp [hu] at hx
    have hBu : finDot x xStar ≤ finDot (B u) xStar := by
      -- The nonnegative covector `x*` preserves the componentwise order `x ≤ B u`.
      simpa [finDot, dotProduct_comm] using
        dotProduct_le_dotProduct_of_nonneg_right hx'.2 hxStar
    have hU : finDot u (Bstar xStar) ≤ finDot u uStar := by
      -- The nonnegative vector `u` preserves the order `Bstar x* ≤ u*`.
      simpa [finDot, dotProduct_comm] using
        dotProduct_le_dotProduct_of_nonneg_left huStar hx'.1
    -- Chain the two monotonicity inequalities with the adjointness identity for `Bstar`.
    calc
      finDot u uStar ≥ finDot u (Bstar xStar) := hU
      _ = finDot (B u) xStar := by rw [hBstar]
      _ ≥ finDot x xStar := hBu

/-- Helper for Proposition 39.4.2: if `x*` has a negative coordinate, then the adjoint fiber is
empty because the zero-input fiber already contains a point forcing a positive dot product on the
right-hand side. -/
lemma adjoint_eq_empty_of_negative_covector {n : ℕ}
    (B : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    {xStar : Fin n → ℝ} (hxStar : ¬ 0 ≤ xStar) :
    setValuedAdjointVec
      (fun u : Fin n → ℝ => if 0 ≤ u then { x | x ≤ B u } else (∅ : Set (Fin n → ℝ))) xStar =
      (∅ : Set (Fin n → ℝ)) := by
  ext uStar
  constructor
  · intro huStar
    exfalso
    rcases helperForProposition_39_4_2_exists_negative_coordinate_of_not_nonneg hxStar with
      ⟨i, hi⟩
    let x : Fin n → ℝ := Pi.single i (-1 : ℝ)
    have hx_mem :
        x ∈
          (if (0 : Fin n → ℝ) ≤ (0 : Fin n → ℝ) then
              {x : Fin n → ℝ | x ≤ B (0 : Fin n → ℝ)}
            else (∅ : Set (Fin n → ℝ))) := by
      -- The point `-e_i` lies below the zero vector, hence in the fiber over `u = 0`.
      simp [x]
    have hineq := huStar 0 x hx_mem
    have hx_dot : finDot x xStar = -xStar i := by
      simp [finDot, x]
    have hzero : finDot (0 : Fin n → ℝ) uStar = 0 := by
      simp [finDot]
    -- The adjoint inequality would force a strictly positive real to be nonpositive.
    have : (-xStar i : ℝ) ≤ 0 := by
      simpa [hzero, hx_dot] using hineq
    exact (not_lt_of_ge this) (by simpa using neg_pos.mpr hi)
  · intro huStar
    simp at huStar

lemma inverseAdjoint_eq_lowerSet_of_nonpos_covector {n : ℕ}
    (B Bstar : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hBstar : ∀ u xStar, finDot (B u) xStar = finDot u (Bstar xStar))
    (uStar : Fin n → ℝ) :
    setValuedAdjointVec
      (setValuedInverse
        (fun u : Fin n → ℝ => if 0 ≤ u then { x | x ≤ B u } else (∅ : Set (Fin n → ℝ))))
      uStar =
      { xStar | xStar ≤ 0 ∧ uStar ≤ Bstar xStar } := by
  ext xStar
  constructor
  · intro hx
    constructor
    · intro i
      let x : Fin n → ℝ := Pi.single i (-1 : ℝ)
      have hx_mem :
          (0 : Fin n → ℝ) ∈
            setValuedInverse
              (fun u : Fin n → ℝ => if 0 ≤ u then {x : Fin n → ℝ | x ≤ B u} else ∅) x := by
        change x ∈
          (if (0 : Fin n → ℝ) ≤ (0 : Fin n → ℝ) then
              {x : Fin n → ℝ | x ≤ B (0 : Fin n → ℝ)}
            else ∅)
        simp [x]
      have hineq := hx x 0 hx_mem
      have hzero : finDot (0 : Fin n → ℝ) uStar = 0 := by
        simp [finDot]
      have hx_dot : finDot x xStar = -xStar i := by
        simp [finDot, x]
      have hnonneg : 0 ≤ -xStar i := by
        simpa [hzero, hx_dot] using hineq
      exact neg_nonneg.mp hnonneg
    · intro i
      let u : Fin n → ℝ := Pi.single i (1 : ℝ)
      have hu_nonneg : (0 : Fin n → ℝ) ≤ u := by
        intro j
        by_cases hji : j = i
        · subst hji
          simp [u]
        · simp [u, hji]
      have hu_mem :
          u ∈
            setValuedInverse
              (fun u : Fin n → ℝ => if 0 ≤ u then {x : Fin n → ℝ | x ≤ B u} else ∅) (B u) := by
        change B u ∈ (if 0 ≤ u then {x : Fin n → ℝ | x ≤ B u} else ∅)
        simp [hu_nonneg]
      have hineq := hx (B u) u hu_mem
      have hucoord : finDot u uStar = uStar i := by
        simp [finDot, u]
      have hBcoord : finDot (B u) xStar = (Bstar xStar) i := by
        rw [hBstar u xStar]
        simp [finDot, u]
      simpa [hucoord, hBcoord] using hineq
  · rintro ⟨hxStar, huStar⟩
    intro x u hxu
    have hxu' : 0 ≤ u ∧ x ≤ B u := by
      change x ∈ (if 0 ≤ u then {x : Fin n → ℝ | x ≤ B u} else ∅) at hxu
      by_cases hu : 0 ≤ u
      · simpa [hu] using hxu
      · simp [hu] at hxu
    have hBu_aux :
        dotProduct x (-xStar) ≤ dotProduct (B u) (-xStar) := by
      exact dotProduct_le_dotProduct_of_nonneg_right hxu'.2 (by
        intro i
        exact neg_nonneg.mpr (hxStar i))
    have hBu : finDot x xStar ≥ finDot (B u) xStar := by
      have hBu' : -finDot x xStar ≤ -finDot (B u) xStar := by
        simpa [finDot] using hBu_aux
      linarith
    have hU : finDot u uStar ≤ finDot u (Bstar xStar) := by
      simpa [finDot, dotProduct_comm] using
        dotProduct_le_dotProduct_of_nonneg_left huStar hxu'.1
    calc
      finDot x xStar ≥ finDot (B u) xStar := hBu
      _ = finDot u (Bstar xStar) := by rw [hBstar]
      _ ≥ finDot u uStar := hU

/-- Local direct-computation variant attached to Proposition 39.4.2: with the current raw
`setValuedAdjointVec (setValuedInverse A)` expression, the third branch takes the sign-reversed
form below. The textbook statement itself is formalized later in `prop_39_4_2`.

Let `B : ℝ^n →ₗ[ℝ] ℝ^n` be linear and define a set-valued mapping `A` by
`A u = {x | x ≤ B u}` when `u ≥ 0` (componentwise), and `A u = ∅` otherwise. For the supremum
orientation,

`⟪A u, x*⟫ = ⟪B u, x*⟫` if `u ≥ 0` and `x* ≥ 0`,

`⟪A u, x*⟫ = +∞` if `u ≥ 0` and `x*` is not componentwise nonnegative,

`⟪A u, x*⟫ = -∞` if `u` is not componentwise nonnegative.

Moreover,

`A* x* = {u* | u* ≥ B^* x*}` if `x* ≥ 0` and `A* x* = ∅` otherwise, and

`setValuedAdjointVec (setValuedInverse A) u* = {x* | x* ≤ 0 ∧ u* ≤ B^* x*}`,

where `B^*` is represented by a linear map `Bstar` satisfying the defining adjointness identity
`finDot (B u) x* = finDot u (Bstar x*)`. -/
theorem prop_39_4_2_localInverseAdjoint {n : ℕ} (B Bstar : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hBstar : ∀ u xStar, finDot (B u) xStar = finDot u (Bstar xStar)) :
    let A : (Fin n → ℝ) → Set (Fin n → ℝ) :=
      fun u => if 0 ≤ u then { x | x ≤ B u } else (∅ : Set (Fin n → ℝ))
    (∀ u xStar,
        setBracketVec ConvexSetOrientation.supremum (A u) xStar =
          if 0 ≤ u then
            if 0 ≤ xStar then ((finDot (B u) xStar : ℝ) : EReal) else (⊤ : EReal)
          else (⊥ : EReal)) ∧
      (∀ xStar,
        setValuedAdjointVec A xStar =
          if 0 ≤ xStar then { uStar | uStar ≥ Bstar xStar } else (∅ : Set (Fin n → ℝ))) ∧
      (∀ uStar,
        setValuedAdjointVec (setValuedInverse A) uStar =
          { xStar | xStar ≤ 0 ∧ uStar ≤ Bstar xStar }) :=
  by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro u xStar
    by_cases hu : 0 ≤ u
    · by_cases hxStar : 0 ≤ xStar
      · -- For `u ≥ 0` and `x* ≥ 0`, the maximal point `B u` attains the support value.
        simpa [hu, hxStar] using
          bracket_eq_finDot_of_nonneg_covector (B := B) hu hxStar
      · -- If `x*` has a negative coordinate, the lower set is unbounded in a profitable direction.
        simpa [hu, hxStar] using
          bracket_eq_top_of_negative_covector (B := B) hu hxStar
    · -- If `u` is not componentwise nonnegative, the fiber is empty, so the supremum bracket is `-∞`.
      simp [setBracketVec, hu]
  · intro xStar
    by_cases hxStar : 0 ≤ xStar
    · -- For `x* ≥ 0`, adjoint membership is exactly the order condition `u* ≥ B^* x*`.
      simpa [hxStar] using
        adjoint_eq_upperSet_of_nonneg_covector
          (B := B) (Bstar := Bstar) hBstar hxStar
    · -- A negative coordinate in `x*` already contradicts the adjoint inequality on the zero fiber.
      simpa [hxStar] using
        adjoint_eq_empty_of_negative_covector (B := B) hxStar
  · intro uStar
    simpa using
      inverseAdjoint_eq_lowerSet_of_nonpos_covector
        (B := B) (Bstar := Bstar) hBstar uStar

/-- Textbook corollary to Proposition 39.4.2: the right-hand side displayed in Rockafellar's
statement is the inverse fiber of `A*`, i.e. `setValuedInverse (setValuedAdjointVec A)`, under the
current local conventions. This is the branch that remains `x* ≥ 0` and `B^* x* ≤ u*`. -/
lemma prop_39_4_2_textbook_inverseOfAdjoint {n : ℕ}
    (B Bstar : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hBstar : ∀ u xStar, finDot (B u) xStar = finDot u (Bstar xStar)) :
    let A : (Fin n → ℝ) → Set (Fin n → ℝ) :=
      fun u => if 0 ≤ u then { x | x ≤ B u } else (∅ : Set (Fin n → ℝ))
    ∀ uStar,
      setValuedInverse (setValuedAdjointVec A) uStar =
        { xStar | 0 ≤ xStar ∧ Bstar xStar ≤ uStar } := by
  dsimp
  intro uStar
  rcases prop_39_4_2_localInverseAdjoint (B := B) (Bstar := Bstar) hBstar with ⟨_, hAdjoint, _⟩
  ext xStar
  constructor
  · intro hx
    change uStar ∈ setValuedAdjointVec
      (fun u : Fin n → ℝ => if 0 ≤ u then {x : Fin n → ℝ | x ≤ B u} else ∅) xStar at hx
    have hFiber := hAdjoint xStar
    by_cases hxStar_nonneg : 0 ≤ xStar
    · rw [hFiber] at hx
      simp [hxStar_nonneg] at hx
      exact ⟨hxStar_nonneg, hx⟩
    · rw [hFiber] at hx
      simp [hxStar_nonneg] at hx
  · rintro ⟨hxStar_nonneg, huStar_ge⟩
    change uStar ∈ setValuedAdjointVec
      (fun u : Fin n → ℝ => if 0 ≤ u then {x : Fin n → ℝ | x ≤ B u} else ∅) xStar
    have hFiber := hAdjoint xStar
    rw [hFiber]
    simp [hxStar_nonneg, huStar_ge]

/-- Proposition 39.4.2 in the textbook form: the third displayed branch is written as the inverse
fiber of `A*`, which under the current local conventions is `setValuedInverse (setValuedAdjointVec A)`. -/
theorem prop_39_4_2 {n : ℕ}
    (B Bstar : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hBstar : ∀ u xStar, finDot (B u) xStar = finDot u (Bstar xStar)) :
    let A : (Fin n → ℝ) → Set (Fin n → ℝ) :=
      fun u => if 0 ≤ u then { x | x ≤ B u } else (∅ : Set (Fin n → ℝ))
    (∀ u xStar,
        setBracketVec ConvexSetOrientation.supremum (A u) xStar =
          if 0 ≤ u then
            if 0 ≤ xStar then ((finDot (B u) xStar : ℝ) : EReal) else (⊤ : EReal)
          else (⊥ : EReal)) ∧
      (∀ xStar,
        setValuedAdjointVec A xStar =
          if 0 ≤ xStar then { uStar | uStar ≥ Bstar xStar } else (∅ : Set (Fin n → ℝ))) ∧
      (∀ uStar,
        setValuedInverse (setValuedAdjointVec A) uStar =
          { xStar | 0 ≤ xStar ∧ Bstar xStar ≤ uStar }) := by
  dsimp
  rcases prop_39_4_2_localInverseAdjoint (B := B) (Bstar := Bstar) hBstar with
    ⟨hBracket, hAdjoint, _⟩
  refine ⟨hBracket, hAdjoint, ?_⟩
  exact prop_39_4_2_textbook_inverseOfAdjoint (B := B) (Bstar := Bstar) hBstar

end ConvexProcess
end Section39
end Chap08
