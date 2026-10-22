/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part5

section Chap06
section Section30

/-- The hypograph of an extended-real-valued function on `ℝ^n`, viewed as a subset of
`ℝ^n × ℝ`. -/
def extendedRealHypograph {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    Set ((Fin n → ℝ) × ℝ) :=
  {p | (p.2 : EReal) ≤ g p.1}

/-- The effective domain of an extended-real-valued function on `ℝ^n`, i.e. the points where
the value is strictly greater than `-∞`. -/
def extendedRealEffectiveDomain {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    Set (Fin n → ℝ) :=
  {x | (⊥ : EReal) < g x}

/-- Definition 6.30.1: for `g : ℝ^n → [-∞, +∞]`, the hypograph is
`{(x, μ) ∈ ℝ^n × ℝ | μ ≤ g(x)}` and the effective domain is
`dom g = {x ∈ ℝ^n | g x > -∞}`. -/
def extendedRealHypographAndEffectiveDomain {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    Set ((Fin n → ℝ) × ℝ) × Set (Fin n → ℝ) :=
  (extendedRealHypograph g, extendedRealEffectiveDomain g)

/-- The convex closure of an extended-real-valued function on `ℝ^n`. This reuses the
canonical repository-wide closure `convexFunctionClosure`, so the Chapter 6 bifunction
closure agrees with the same `cl` used earlier in the book. -/
noncomputable def convexClosure {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  convexFunctionClosure f

/-- Definition 6.30.3: for a concave function `g : ℝ^n → [-∞, +∞]`, its closure `cl g`
is the negative of the canonical convex closure of `-g`. -/
noncomputable def concaveClosure {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → EReal :=
  fun x => -(convexFunctionClosure (fun z => -g z) x)

/-- Negating converts affine majorants of `g` into affine minorants of `-g`, so the
concave closure is the negative of the convex closure of the negated function. -/
lemma concaveClosure_eq_neg_convexClosure_neg {n : ℕ} (g : (Fin n → ℝ) → EReal) :
    concaveClosure g = fun x => - (convexClosure (fun z => - g z) x) := by
  rfl

/-- An extended-real-valued function on `ℝ^n` is concave when its negative is convex. -/
def ConcaveFunction {n : ℕ} (g : (Fin n → ℝ) → EReal) : Prop :=
  ConvexFunction (fun x => - g x)

/-- An extended-real-valued function on `ℝ^n` is closed and concave when its negative is a
closed convex function. -/
def ClosedConcaveFunction {n : ℕ} (g : (Fin n → ℝ) → EReal) : Prop :=
  ClosedConvexFunction (fun x => - g x)

/-- A convex bifunction is proper when its graph function on `ℝ^(m + n)` is proper convex. -/
def ProperConvexBifunction {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ConvexBifunction F ∧
    ProperConvexERealFunction (F := Fin (m + n) → ℝ) (bifunctionGraphFunction F)

/-- A concave bifunction is proper when its graph function on `ℝ^(m + n)` is proper concave. -/
def ProperConcaveBifunction {m n : ℕ} (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ConcaveBifunction G ∧
    ProperConcaveERealFunction (bifunctionGraphFunction G)

/-- A convex bifunction is closed when its graph function is closed convex on `ℝ^(m + n)`. -/
def ClosedConvexBifunction {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ConvexBifunction F ∧ ClosedConvexFunction (bifunctionGraphFunction F)

/-- A concave bifunction is closed when its graph function is closed concave on `ℝ^(m + n)`. -/
def ClosedConcaveBifunction {m n : ℕ} (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ConcaveBifunction G ∧ ClosedConcaveERealFunction (bifunctionGraphFunction G)

/-- A convex bifunction is polyhedral when its graph function is polyhedral convex. -/
def PolyhedralConvexBifunction {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ConvexBifunction F ∧ IsPolyhedralConvexFunction (m + n) (bifunctionGraphFunction F)

/-- A concave bifunction is polyhedral when the negative of its graph function is polyhedral
convex. -/
def PolyhedralConcaveBifunction {m n : ℕ} (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ConcaveBifunction G ∧
    IsPolyhedralConvexFunction (m + n) (fun z => -bifunctionGraphFunction G z)

/-- The closure of a convex bifunction is the bifunction induced by the convex closure of its
graph function. -/
noncomputable def convexBifunctionClosure {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x => convexClosure (bifunctionGraphFunction F) (Fin.append u x)

/-- The closure of a concave bifunction is the bifunction induced by the concave closure of its
graph function. -/
noncomputable def concaveBifunctionClosure {m n : ℕ}
    (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x => concaveClosure (bifunctionGraphFunction G) (Fin.append u x)

-- Proof sketch: apply the convex-conjugate closedness theorem to the negated graph function
-- `z ↦ - G(z)`; the concave adjoint is the negative Fenchel conjugate of that graph function
-- with the variables reversed, so the resulting graph function is closed convex.
/-- The adjoint of a concave bifunction is a closed convex bifunction on the reversed product. -/
theorem adjointOfConcaveBifunction_closedConvex {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) :
    ClosedConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction G) := by
  -- Route correction: for the concave adjoint, the defining supremum is already the Fenchel
  -- conjugate of the negated graph function after the coordinate shuffle `(x*, u*) ↦ (u*, -x*)`.
  have hRewrite :
      (fun z : Fin (n + m) → ℝ => bifunctionGraphFunction (adjointOfConcaveBifunction G) z) =
        (fun z : Fin (n + m) → ℝ =>
          fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G.1 w)
            (-helperForTheorem_6_30_10_coordinateLinearMap z)) := by
    funext z
    let xStar : Fin n → ℝ := fun j => z (Fin.castAdd m j)
    let uStar : Fin m → ℝ := fun i => z (Fin.natAdd n i)
    -- Rewrite the adjoint graph as a pair-indexed Fenchel conjugate of the negated graph.
    calc
      bifunctionGraphFunction (adjointOfConcaveBifunction G) z
          = sSup (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
              G.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
                simp [bifunctionGraphFunction, adjointOfConcaveBifunction, xStar, uStar]
      _ = iSup (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
          G.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
            simp [sSup_range]
      _ =
          fenchelConjugate (m + n) (bifunctionGraphFunction (fun u x => -G.1 u x))
            (adjointGraphDualVector (-uStar) (-xStar)) := by
              calc
                iSup (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
                    G.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal)))
                    =
                  iSup (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
                    (((Fin.append p.1 p.2 ⬝ᵥ adjointGraphDualVector (-uStar) (-xStar) : ℝ) : EReal) -
                      bifunctionGraphFunction (fun u x => -G.1 u x) (Fin.append p.1 p.2))) := by
                        refine iSup_congr ?_
                        intro p
                        simp [bifunctionGraphFunction, adjointGraphDualVector, xStar, uStar,
                          sub_eq_add_neg, add_left_comm, add_comm, dotProduct, Fin.sum_univ_add]
                _ =
                  fenchelConjugate (m + n) (bifunctionGraphFunction (fun u x => -G.1 u x))
                    (adjointGraphDualVector (-uStar) (-xStar)) := by
                      exact
                        (helperForTheorem_6_30_9_fenchelConjugate_graphFunction_eq_iSup_pairs
                          (F := fun u x => -G.1 u x) (xStar := -xStar) (uStar := -uStar)).symm
      _ =
          fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G.1 w)
            (-helperForTheorem_6_30_10_coordinateLinearMap z) := by
              have hGraph :
                  bifunctionGraphFunction (fun u x => -G.1 u x) =
                    (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G.1 w) := by
                funext w
                simp [bifunctionGraphFunction]
              have hArg :
                  adjointGraphDualVector (-uStar) (-xStar) =
                    -helperForTheorem_6_30_10_coordinateLinearMap z := by
                ext i
                by_cases hi : i.1 < m
                · have hi' : Fin.castAdd n ⟨i.1, hi⟩ = i := by
                    ext
                    simp
                  rw [← hi']
                  simp [helperForTheorem_6_30_10_coordinateLinearMap,
                    helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, uStar,
                    Fin.append, Fin.addCases, hi]
                · let j : Fin n := ⟨i.1 - m, by omega⟩
                  have hj : Fin.natAdd m j = i := by
                    ext
                    simp [j]
                    omega
                  rw [← hj]
                  simp [helperForTheorem_6_30_10_coordinateLinearMap,
                    helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, xStar,
                    Fin.append, Fin.addCases, j]
              rw [hGraph, hArg]
  have hConvexNegGraph :
      ConvexFunction (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G.1 w) := by
    simpa [ConcaveBifunction] using G.2
  have hClosedFenchel :
      ClosedConvexFunction
        (fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G.1 w)) :=
    let h := fenchelConjugate_closedConvex (n := m + n)
      (f := fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G.1 w)
    ⟨h.2, h.1⟩
  have hClosedPrecomp :
      ClosedConvexFunction (fun z : Fin (n + m) → ℝ =>
        fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G.1 w)
          (-helperForTheorem_6_30_10_coordinateLinearMap z)) :=
    closedConvexFunction_precomp_linearMap
      (A := -helperForTheorem_6_30_10_coordinateLinearMap) hClosedFenchel
  -- Transport the closed-convex structure across the explicit graph rewrite.
  have hClosedAdj :
      ClosedConvexFunction
        (bifunctionGraphFunction (adjointOfConcaveBifunction G)) := by
    simpa [hRewrite] using hClosedPrecomp
  refine ⟨?_, hClosedAdj⟩
  simpa [ConvexBifunction] using hClosedAdj.1

/-- The convex adjoint, packaged as a concave bifunction on the reversed variables. -/
noncomputable def adjointOfConvexBifunctionAsConcave {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    {G : (Fin n → ℝ) → (Fin m → ℝ) → EReal // ConcaveBifunction G} :=
  ⟨adjointOfConvexBifunction F, (adjointOfConvexBifunction_closedConcave F).1⟩

/-- The concave adjoint, packaged as a convex bifunction on the reversed variables. -/
noncomputable def adjointOfConcaveBifunctionAsConvex {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) :
    {F : (Fin n → ℝ) → (Fin m → ℝ) → EReal // ConvexBifunction F} :=
  ⟨adjointOfConcaveBifunction G, (adjointOfConcaveBifunction_closedConvex G).1⟩

/-- The biconjugate of a convex bifunction, obtained by taking the concave adjoint of its
adjoint. -/
noncomputable def biadjointOfConvexBifunction {m n : ℕ}
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConvexBifunction F}) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  adjointOfConcaveBifunction (adjointOfConvexBifunctionAsConcave F)

/-- The biconjugate of a concave bifunction, obtained by taking the convex adjoint of its
adjoint. -/
noncomputable def biadjointOfConcaveBifunction {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G}) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  adjointOfConvexBifunction (adjointOfConcaveBifunctionAsConvex G)

/-- Helper for Theorem 6.30.11: the graph of the adjoint of a concave bifunction is the Fenchel
conjugate of the negated graph function after the coordinate shuffle `(x*, u*) ↦ (u*, -x*)`. -/
lemma helperForTheorem_6_30_11_adjointOfConcave_graph_eq_fenchelConjugate_precomp
    {m n : ℕ}
    (G : {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal // ConcaveBifunction G})
    (z : Fin (n + m) → ℝ) :
    bifunctionGraphFunction (adjointOfConcaveBifunction G) z =
      fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G.1 w)
        (-helperForTheorem_6_30_10_coordinateLinearMap z) := by
  -- Route correction: expose the graph rewrite from the closedness proof as a reusable lemma so
  -- the main theorem can isolate the true closure-semantics blocker from the standard transport
  -- arguments for properness and polyhedrality.
  let xStar : Fin n → ℝ := fun j => z (Fin.castAdd m j)
  let uStar : Fin m → ℝ := fun i => z (Fin.natAdd n i)
  -- Rewrite the adjoint graph as a pair-indexed Fenchel conjugate of the negated graph.
  calc
    bifunctionGraphFunction (adjointOfConcaveBifunction G) z
        = sSup (Set.range fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
            G.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
              simp [bifunctionGraphFunction, adjointOfConcaveBifunction, xStar, uStar]
    _ = iSup (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
        G.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
          simp [sSup_range]
    _ =
        fenchelConjugate (m + n) (bifunctionGraphFunction (fun u x => -G.1 u x))
          (adjointGraphDualVector (-uStar) (-xStar)) := by
            calc
              iSup (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
                  G.1 p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal)))
                  =
                iSup (fun p : (Fin m → ℝ) × (Fin n → ℝ) =>
                  (((Fin.append p.1 p.2 ⬝ᵥ adjointGraphDualVector (-uStar) (-xStar) : ℝ) : EReal) -
                    bifunctionGraphFunction (fun u x => -G.1 u x) (Fin.append p.1 p.2))) := by
                      refine iSup_congr ?_
                      intro p
                      simp [bifunctionGraphFunction, adjointGraphDualVector, xStar, uStar,
                        sub_eq_add_neg, add_left_comm, add_comm, dotProduct, Fin.sum_univ_add]
              _ =
                fenchelConjugate (m + n) (bifunctionGraphFunction (fun u x => -G.1 u x))
                  (adjointGraphDualVector (-uStar) (-xStar)) := by
                    exact
                      (helperForTheorem_6_30_9_fenchelConjugate_graphFunction_eq_iSup_pairs
                        (F := fun u x => -G.1 u x) (xStar := -xStar) (uStar := -uStar)).symm
    _ =
        fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G.1 w)
          (-helperForTheorem_6_30_10_coordinateLinearMap z) := by
            have hGraph :
                bifunctionGraphFunction (fun u x => -G.1 u x) =
                  (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G.1 w) := by
              funext w
              simp [bifunctionGraphFunction]
            have hArg :
                adjointGraphDualVector (-uStar) (-xStar) =
                  -helperForTheorem_6_30_10_coordinateLinearMap z := by
              ext i
              by_cases hi : i.1 < m
              · have hi' : Fin.castAdd n ⟨i.1, hi⟩ = i := by
                  ext
                  simp
                rw [← hi']
                simp [helperForTheorem_6_30_10_coordinateLinearMap,
                  helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, uStar,
                  Fin.append, Fin.addCases, hi]
              · let j : Fin n := ⟨i.1 - m, by omega⟩
                have hj : Fin.natAdd m j = i := by
                  ext
                  simp [j]
                  omega
                rw [← hj]
                simp [helperForTheorem_6_30_10_coordinateLinearMap,
                  helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, xStar,
                  Fin.append, Fin.addCases, j]
            rw [hGraph, hArg]

/-- Helper for Theorem 6.30.11: the coordinate shuffle from Theorem 6.30.10 is surjective. -/
lemma helperForTheorem_6_30_11_coordinateLinearMap_surjective {m n : ℕ} :
    Function.Surjective (helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n)) := by
  intro y
  let z : Fin (n + m) → ℝ :=
    fun i =>
      Fin.addCases
        (fun j => y (Fin.natAdd m j))
        (fun k => -y (Fin.castAdd n k))
        i
  refine ⟨z, ?_⟩
  -- Unfold the coordinate shuffle and check the chosen preimage blockwise.
  funext i
  by_cases hi : i.1 < m
  · have hi' : Fin.castAdd n ⟨i.1, hi⟩ = i := by
      ext
      simp
    rw [← hi']
    simp [helperForTheorem_6_30_10_coordinateLinearMap,
      helperForTheorem_6_30_10_coordinateMap, z, adjointGraphDualVector, Fin.append,
      Fin.addCases, hi]
  · let j : Fin n := ⟨i.1 - m, by omega⟩
    have hj : Fin.natAdd m j = i := by
      ext
      simp [j]
      omega
    have hjlt : i.1 - m < n := by
      omega
    rw [← hj]
    simp [helperForTheorem_6_30_10_coordinateLinearMap,
      helperForTheorem_6_30_10_coordinateMap, z, adjointGraphDualVector, Fin.append,
      Fin.addCases, j, hjlt]

/-- Helper for Theorem 6.30.11: negating the coordinate shuffle still gives a surjective linear
map. -/
lemma helperForTheorem_6_30_11_negCoordinateLinearMap_surjective {m n : ℕ} :
    Function.Surjective (-helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n)) := by
  intro y
  rcases helperForTheorem_6_30_11_coordinateLinearMap_surjective (m := m) (n := n) (-y) with
    ⟨z, hz⟩
  refine ⟨z, ?_⟩
  -- Surjectivity is stable under multiplying the target by `-1`.
  simpa [LinearMap.neg_apply, hz] using congrArg Neg.neg hz

/-- Helper for Theorem 6.30.11: the two coordinate shuffles cancel after inserting the
intermediate minus sign required by the adjoint formulas. -/
lemma helperForTheorem_6_30_11_coordinateLinearMap_comp_neg_reverse {m n : ℕ}
    (z : Fin (m + n) → ℝ) :
    helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n)
      (-helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) z) = z := by
  -- Check the cancellation blockwise on the `u`- and `x`-coordinates.
  ext i
  by_cases hi : i.1 < m
  · have hi' : Fin.castAdd n ⟨i.1, hi⟩ = i := by
      ext
      simp
    rw [← hi']
    simp [helperForTheorem_6_30_10_coordinateLinearMap,
      helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, hi,
      Fin.append, Fin.addCases]
  · let j : Fin n := ⟨i.1 - m, by omega⟩
    have hj : Fin.natAdd m j = i := by
      ext
      simp [j]
      omega
    have hjlt : i.1 - m < n := by
      omega
    rw [← hj]
    simp [helperForTheorem_6_30_10_coordinateLinearMap,
      helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector,
      Fin.append, Fin.addCases, j, hjlt]

/-- Helper for Theorem 6.30.11: Fenchel conjugation through the coordinate shuffle is equivalent
to evaluating the conjugate at the correspondingly shuffled dual point. -/
lemma helperForTheorem_6_30_11_fenchelConjugate_precomp_coordinateLinearMap
    {m n : ℕ} (f : (Fin (m + n) → ℝ) → EReal) (z : Fin (m + n) → ℝ) :
    fenchelConjugate (n + m)
      (fun w : Fin (n + m) → ℝ => f (helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w))
      (-helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) z) =
      fenchelConjugate (m + n) f z := by
  calc
    fenchelConjugate (n + m)
        (fun w : Fin (n + m) → ℝ =>
          f (helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w))
        (-helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) z)
      = iSup (fun w : Fin (n + m) → ℝ =>
          (((w ⬝ᵥ (-helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) z) : ℝ) : EReal)) -
            f (helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w)) := by
          -- Expand the Fenchel conjugate so the change of variables is explicit.
          simp [fenchelConjugate_eq_iSup]
    _ = iSup (fun y : Fin (m + n) → ℝ =>
          (((y ⬝ᵥ z : ℝ) : EReal)) - f y) := by
          -- Transport the supremum across the coordinate shuffle in both directions.
          apply le_antisymm
          · refine iSup_le ?_
            intro w
            refine le_iSup_of_le (helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w) ?_
            simp [helperForTheorem_6_30_10_coordinateLinearMap,
              helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, dotProduct,
              Fin.sum_univ_add, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
          · refine iSup_le ?_
            intro y
            refine le_iSup_of_le (-helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) y) ?_
            have hcancel :=
              helperForTheorem_6_30_11_coordinateLinearMap_comp_neg_reverse (m := m) (n := n) y
            have hcancelArg :
                Fin.append (-fun i => -y (Fin.castAdd n i)) (fun i => y (Fin.natAdd m i)) = y := by
              simpa [helperForTheorem_6_30_10_coordinateLinearMap,
                helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, Fin.append,
                Fin.addCases] using hcancel
            have hdot :
                (((-helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) y) ⬝ᵥ
                    (-helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) z) : ℝ) : EReal) =
                  (((y ⬝ᵥ z : ℝ) : EReal)) := by
              simp [helperForTheorem_6_30_10_coordinateLinearMap,
                helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, dotProduct,
                Fin.sum_univ_add, add_comm, add_assoc, sub_eq_add_neg]
            rw [hcancel, hdot]
    _ = fenchelConjugate (m + n) f z := by
          -- Repackage the transported `iSup` as the conjugate of `f`.
          simp [fenchelConjugate_eq_iSup]

/-- Helper for Theorem 6.30.11: negating after the reverse coordinate shuffle recovers the
original point. -/
lemma helperForTheorem_6_30_11_neg_coordinateLinearMap_comp_reverse {m n : ℕ}
    (z : Fin (m + n) → ℝ) :
    -helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n)
      (helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) z) = z := by
  -- Verify the cancellation blockwise, as for the previous coordinate-shuffle identity.
  ext i
  by_cases hi : i.1 < m
  · have hi' : Fin.castAdd n ⟨i.1, hi⟩ = i := by
      ext
      simp
    rw [← hi']
    simp [helperForTheorem_6_30_10_coordinateLinearMap,
      helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, hi,
      Fin.append, Fin.addCases]
  · let j : Fin n := ⟨i.1 - m, by omega⟩
    have hj : Fin.natAdd m j = i := by
      ext
      simp [j]
      omega
    have hjlt : i.1 - m < n := by
      omega
    rw [← hj]
    simp [helperForTheorem_6_30_10_coordinateLinearMap,
      helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector,
      Fin.append, Fin.addCases, j, hjlt]

/-- Helper for Theorem 6.30.11: the opposite sign convention for the coordinate shuffle also
transports Fenchel conjugation back to the original dual point. -/
lemma helperForTheorem_6_30_11_neg_fenchelConjugate_precomp_coordinateLinearMap
    {m n : ℕ} (f : (Fin (m + n) → ℝ) → EReal) (z : Fin (m + n) → ℝ) :
    fenchelConjugate (n + m)
      (fun w : Fin (n + m) → ℝ =>
        f (-helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w))
      (helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) z) =
      fenchelConjugate (m + n) f z := by
  calc
    fenchelConjugate (n + m)
        (fun w : Fin (n + m) → ℝ =>
          f (-helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w))
        (helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) z)
      = iSup (fun w : Fin (n + m) → ℝ =>
          (((w ⬝ᵥ helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) z : ℝ) : EReal)) -
            f (-helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w)) := by
          -- Again unfold the conjugate so the change of variables is explicit.
          simp [fenchelConjugate_eq_iSup]
    _ = iSup (fun y : Fin (m + n) → ℝ =>
          (((y ⬝ᵥ z : ℝ) : EReal)) - f y) := by
          -- Transport the supremum by the inverse coordinate shuffle.
          apply le_antisymm
          · refine iSup_le ?_
            intro w
            refine le_iSup_of_le (-helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w) ?_
            simp [helperForTheorem_6_30_10_coordinateLinearMap,
              helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, dotProduct,
              Fin.sum_univ_add, add_comm, add_assoc, sub_eq_add_neg]
          · refine iSup_le ?_
            intro y
            refine le_iSup_of_le (helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) y) ?_
            have hcancel :=
              helperForTheorem_6_30_11_neg_coordinateLinearMap_comp_reverse (m := m) (n := n) y
            have hcancelArg :
                -Fin.append (-fun j => y (Fin.castAdd n j)) (fun j => -y (Fin.natAdd m j)) = y := by
              simpa [helperForTheorem_6_30_10_coordinateLinearMap,
                helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, Fin.append,
                Fin.addCases] using hcancel
            have hdot :
                (((helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) y) ⬝ᵥ
                    helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) z : ℝ) : EReal) =
                  (((y ⬝ᵥ z : ℝ) : EReal)) := by
              simp [helperForTheorem_6_30_10_coordinateLinearMap,
                helperForTheorem_6_30_10_coordinateMap, adjointGraphDualVector, dotProduct,
                Fin.sum_univ_add, add_comm, add_assoc, sub_eq_add_neg]
            rw [hcancel, hdot]
    _ = fenchelConjugate (m + n) f z := by
          -- This is exactly the defining `iSup` for the conjugate of `f`.
          simp [fenchelConjugate_eq_iSup]

/-- Helper for Theorem 6.30.11: a proper convex `EReal`-valued function on `ℝ^n` induces a proper
convex function on `Set.univ`, so the Fenchel-conjugate API applies directly. -/
lemma helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
    {n : ℕ}
    (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := Fin n → ℝ) f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
  refine ⟨?_, ?_, ?_⟩
  · -- The Jensen-style convexity data is exactly the segment inequality on `univ`.
    have hconv : ConvexERealFunction f := hf.2
    refine
      (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := f)
        (hC := convex_univ) (hnotbot := ?_)).2 ?_
    · intro x hx
      simpa using hf.1.1 x
    · intro x hx y hy t ht0 ht1
      have hseg :=
        hconv (x := x) (y := y) (a := 1 - t) (b := t)
          (sub_nonneg.mpr (le_of_lt ht1)) (le_of_lt ht0) (by ring)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hseg
  · rcases hf.1.2 with ⟨x, hx⟩
    refine ⟨(x, (f x).toReal), ?_⟩
    -- A finite point of `f` gives a point of the epigraph over `univ`.
    exact
      (mem_epigraph_univ_iff (f := f)).2
        (by simpa [EReal.coe_toReal hx (hf.1.1 x)])
  · intro x hx
    simpa using hf.1.1 x

/-- Helper for Theorem 6.30.11: if a surjective linear precomposition is proper on `univ`, then
the original function is proper on `univ` as well. -/
lemma helperForTheorem_6_30_11_properConvexFunctionOn_of_precomp_linearMap_surjective
    {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hA : Function.Surjective A)
    {f : (Fin m → ℝ) → EReal}
    (hf : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fun x => f (A x))) :
    ProperConvexFunctionOn (Set.univ : Set (Fin m → ℝ)) f := by
  refine ⟨?_, ?_, ?_⟩
  · -- Pull convexity back along the chosen preimages of `A`.
    refine (convexFunctionOn_iff_segment_inequality (C := Set.univ) (f := f)
      (hC := convex_univ) (hnotbot := ?_)).2 ?_
    · intro y hy
      rcases hA y with ⟨x, rfl⟩
      exact hf.2.2 x (by simp)
    · intro y hy z hz t ht0 ht1
      rcases hA y with ⟨x, rfl⟩
      rcases hA z with ⟨w, rfl⟩
      have hseg :=
        (convexFunctionOn_iff_segment_inequality
          (C := Set.univ) (f := fun x => f (A x)) (hC := convex_univ) (hnotbot := hf.2.2)).1
          hf.1 x (by simp) w (by simp) t ht0 ht1
      simpa [map_sub, map_add, smul_add, add_comm, add_left_comm, add_assoc] using hseg
  · rcases hf.2.1 with ⟨⟨x, μ⟩, hxμ⟩
    refine ⟨(A x, μ), ?_⟩
    exact (mem_epigraph_univ_iff (f := f)).2 ((mem_epigraph_univ_iff (f := fun x => f (A x))).1 hxμ)
  · intro y hy
    rcases hA y with ⟨x, rfl⟩
    exact hf.2.2 x (by simp)

/-- Helper for Theorem 6.30.11: aside from the closed fixed-point clause, the convex branch of
the theorem follows from Theorem 6.30.10 together with standard Fenchel-conjugate transport
results for properness and polyhedrality. -/
lemma helperForTheorem_6_30_11_convex_branch_except_closed_fixed_point
    {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : ConvexBifunction F) :
    ClosedConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩) ∧
      (ProperConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩) ↔
        ProperConvexBifunction F) ∧
      (ClosedConvexBifunction F ∧ ProperConvexBifunction F →
        ClosedConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩) ∧
          ProperConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩)) ∧
      (PolyhedralConvexBifunction F →
        PolyhedralConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩)) := by
  have hClosedAdj :
      ClosedConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩) := by
    -- Theorem 6.30.10 already gives the closed opposite-type adjoint.
    simpa [ClosedConcaveBifunction] using adjointOfConvexBifunction_closedConcave ⟨F, hF⟩
  have hRewrite :
      (fun z : Fin (n + m) → ℝ => -bifunctionGraphFunction (adjointOfConvexBifunction ⟨F, hF⟩) z) =
        (fun z : Fin (n + m) → ℝ =>
          fenchelConjugate (m + n) (bifunctionGraphFunction F)
            (helperForTheorem_6_30_10_coordinateLinearMap z)) := by
    -- Negating the graph form of Theorem 6.30.10 exposes a plain precomposition of `F`'s
    -- Fenchel conjugate.
    funext z
    rw [helperForTheorem_6_30_10_adjointGraph_eq_neg_fenchelConjugate_precomp (F := ⟨F, hF⟩)
      (z := z)]
    simp
  have hProperIff :
      ProperConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩) ↔
        ProperConvexBifunction F := by
    constructor
    · intro hAdj
      refine ⟨hF, ?_⟩
      have hAdjProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
            (fun z => -bifunctionGraphFunction (adjointOfConvexBifunction ⟨F, hF⟩) z) :=
        helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
          (f := fun z => -bifunctionGraphFunction (adjointOfConvexBifunction ⟨F, hF⟩) z) hAdj.2
      have hFenchelProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
            (fenchelConjugate (m + n) (bifunctionGraphFunction F)) := by
        have hPrecompProperOn :
            ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
              (fun z =>
                fenchelConjugate (m + n) (bifunctionGraphFunction F)
                  (helperForTheorem_6_30_10_coordinateLinearMap z)) := by
          simpa [hRewrite] using hAdjProperOn
        exact
          helperForTheorem_6_30_11_properConvexFunctionOn_of_precomp_linearMap_surjective
            (A := helperForTheorem_6_30_10_coordinateLinearMap)
            (hA := helperForTheorem_6_30_11_coordinateLinearMap_surjective
              (m := m) (n := n))
            hPrecompProperOn
      have hGraphProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (bifunctionGraphFunction F) :=
        (fenchelConjugate_proper_iff (n := m + n) (f := bifunctionGraphFunction F)
          (by simpa [ConvexBifunction] using hF)).1 hFenchelProperOn
      exact
        helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
          (f := bifunctionGraphFunction F) hGraphProperOn
    · intro hProper
      refine ⟨hClosedAdj.1, ?_⟩
      have hGraphProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ)) (bifunctionGraphFunction F) :=
        helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
          (f := bifunctionGraphFunction F) hProper.2
      have hFenchelProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
            (fenchelConjugate (m + n) (bifunctionGraphFunction F)) :=
        (fenchelConjugate_proper_iff (n := m + n) (f := bifunctionGraphFunction F)
          (by simpa [ConvexBifunction] using hF)).2 hGraphProperOn
      have hPrecompProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
            (fun z =>
              fenchelConjugate (m + n) (bifunctionGraphFunction F)
                (helperForTheorem_6_30_10_coordinateLinearMap z)) :=
        properConvexFunctionOn_precomp_linearMap_surjective
          (A := helperForTheorem_6_30_10_coordinateLinearMap)
          (hA := helperForTheorem_6_30_11_coordinateLinearMap_surjective
            (m := m) (n := n))
          hFenchelProperOn
      simpa [ProperConcaveERealFunction, hRewrite] using
        (helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
          (f := fun z =>
            fenchelConjugate (m + n) (bifunctionGraphFunction F)
              (helperForTheorem_6_30_10_coordinateLinearMap z))
          hPrecompProperOn)
  have hPoly :
      PolyhedralConvexBifunction F →
        PolyhedralConcaveBifunction (m := n) (n := m) (adjointOfConvexBifunction ⟨F, hF⟩) := by
    intro hPolyF
    refine ⟨hClosedAdj.1, ?_⟩
    have hFenchelPoly :
        IsPolyhedralConvexFunction (m + n)
          (fenchelConjugate (m + n) (bifunctionGraphFunction F)) :=
      polyhedralConvexFunction_fenchelConjugate (m + n) (bifunctionGraphFunction F) hPolyF.2
    have hPrecompPoly :
        IsPolyhedralConvexFunction (n + m)
          (inverseImageUnderLinearMap helperForTheorem_6_30_10_coordinateLinearMap
            (fenchelConjugate (m + n) (bifunctionGraphFunction F))) :=
      (polyhedralConvexFunction_image_preimage_linear (n + m) (m + n)
        helperForTheorem_6_30_10_coordinateLinearMap).2
        (fenchelConjugate (m + n) (bifunctionGraphFunction F)) hFenchelPoly
    -- Reinterpret the preimage statement as polyhedrality of the negated adjoint graph.
    simpa [PolyhedralConcaveBifunction, inverseImageUnderLinearMap, hRewrite] using hPrecompPoly
  refine ⟨hClosedAdj, hProperIff, ?_, hPoly⟩
  intro hClosedProper
  -- Once properness is transferred, the closed proper correspondence is immediate.
  exact ⟨hClosedAdj, hProperIff.2 hClosedProper.2⟩

/-- Helper for Theorem 6.30.11: aside from the closed fixed-point clause, the concave branch of
the theorem follows from the corresponding graph rewrite and the same Fenchel transport results. -/
lemma helperForTheorem_6_30_11_concave_branch_except_closed_fixed_point
    {m n : ℕ}
    (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hG : ConcaveBifunction G) :
    ClosedConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨G, hG⟩) ∧
      (ProperConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨G, hG⟩) ↔
        ProperConcaveBifunction G) ∧
      (ClosedConcaveBifunction G ∧ ProperConcaveBifunction G →
        ClosedConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨G, hG⟩) ∧
          ProperConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨G, hG⟩)) ∧
      (PolyhedralConcaveBifunction G →
        PolyhedralConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨G, hG⟩)) := by
  have hClosedAdj :
      ClosedConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨G, hG⟩) :=
    adjointOfConcaveBifunction_closedConvex ⟨G, hG⟩
  have hRewrite :
      (fun z : Fin (n + m) → ℝ => bifunctionGraphFunction (adjointOfConcaveBifunction ⟨G, hG⟩) z) =
        (fun z : Fin (n + m) → ℝ =>
          fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w)
            (-helperForTheorem_6_30_10_coordinateLinearMap z)) := by
    -- The reusable graph identity is the concave analogue of Theorem 6.30.10.
    funext z
    exact helperForTheorem_6_30_11_adjointOfConcave_graph_eq_fenchelConjugate_precomp
      (G := ⟨G, hG⟩) (z := z)
  have hProperIff :
      ProperConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨G, hG⟩) ↔
        ProperConcaveBifunction G := by
    constructor
    · intro hAdj
      refine ⟨hG, ?_⟩
      have hAdjProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
            (bifunctionGraphFunction (adjointOfConcaveBifunction ⟨G, hG⟩)) :=
        helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
          (f := bifunctionGraphFunction (adjointOfConcaveBifunction ⟨G, hG⟩)) hAdj.2
      have hFenchelProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
            (fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w)) := by
        have hPrecompProperOn :
            ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
              (fun z =>
                fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w)
                  (-helperForTheorem_6_30_10_coordinateLinearMap z)) := by
          simpa [hRewrite] using hAdjProperOn
        exact
          helperForTheorem_6_30_11_properConvexFunctionOn_of_precomp_linearMap_surjective
            (A := -helperForTheorem_6_30_10_coordinateLinearMap)
            (hA := helperForTheorem_6_30_11_negCoordinateLinearMap_surjective
              (m := m) (n := n))
            hPrecompProperOn
      have hNegGraphProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
            (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w) :=
        (fenchelConjugate_proper_iff (n := m + n)
          (f := fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w)
          (by simpa [ConcaveBifunction] using hG)).1 hFenchelProperOn
      simpa [ProperConcaveERealFunction] using
        (helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
          (f := fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w) hNegGraphProperOn)
    · intro hProper
      refine ⟨hClosedAdj.1, ?_⟩
      have hNegGraphProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
            (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w) :=
        helperForTheorem_6_30_11_properConvexFunctionOn_univ_of_properConvexERealFunction
          (f := fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w) hProper.2
      have hFenchelProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (m + n) → ℝ))
            (fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w)) :=
        (fenchelConjugate_proper_iff (n := m + n)
          (f := fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w)
          (by simpa [ConcaveBifunction] using hG)).2 hNegGraphProperOn
      have hPrecompProperOn :
          ProperConvexFunctionOn (Set.univ : Set (Fin (n + m) → ℝ))
            (fun z =>
              fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w)
                (-helperForTheorem_6_30_10_coordinateLinearMap z)) :=
        properConvexFunctionOn_precomp_linearMap_surjective
          (A := -helperForTheorem_6_30_10_coordinateLinearMap)
          (hA := helperForTheorem_6_30_11_negCoordinateLinearMap_surjective
            (m := m) (n := n))
          hFenchelProperOn
      simpa [hRewrite] using
        (helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ
          (f := fun z =>
            fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w)
              (-helperForTheorem_6_30_10_coordinateLinearMap z))
          hPrecompProperOn)
  have hPoly :
      PolyhedralConcaveBifunction G →
        PolyhedralConvexBifunction (m := n) (n := m) (adjointOfConcaveBifunction ⟨G, hG⟩) := by
    intro hPolyG
    refine ⟨hClosedAdj.1, ?_⟩
    have hFenchelPoly :
        IsPolyhedralConvexFunction (m + n)
          (fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w)) :=
      polyhedralConvexFunction_fenchelConjugate (m + n)
        (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w) hPolyG.2
    have hPrecompPoly :
        IsPolyhedralConvexFunction (n + m)
          (inverseImageUnderLinearMap (-helperForTheorem_6_30_10_coordinateLinearMap)
            (fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w))) :=
      (polyhedralConvexFunction_image_preimage_linear (n + m) (m + n)
        (-helperForTheorem_6_30_10_coordinateLinearMap)).2
        (fenchelConjugate (m + n) (fun w : Fin (m + n) → ℝ => -bifunctionGraphFunction G w))
        hFenchelPoly
    -- The preimage theorem is exactly the desired polyhedrality of the adjoint graph.
    simpa [PolyhedralConvexBifunction, inverseImageUnderLinearMap, hRewrite] using hPrecompPoly
  refine ⟨hClosedAdj, hProperIff, ?_, hPoly⟩
  intro hClosedProper
  -- As in the convex branch, the closed proper correspondence uses only the proven transport.
  exact ⟨hClosedAdj, hProperIff.2 hClosedProper.2⟩

/-- Helper for Theorem 6.30.11: the convex biadjoint is the closure of the original convex
bifunction. -/
lemma helperForTheorem_6_30_11_biadjointOfConvex_graph_eq_convexBifunctionClosure_via_coordinate_shuffle
    {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : ConvexBifunction F) :
    biadjointOfConvexBifunction ⟨F, hF⟩ = convexBifunctionClosure F := by
  funext u x
  have hGraphRewrite :
      (fun w : Fin (n + m) → ℝ => -bifunctionGraphFunction (↑(adjointOfConvexBifunctionAsConcave ⟨F, hF⟩)) w) =
        (fun w : Fin (n + m) → ℝ =>
          fenchelConjugate (m + n) (bifunctionGraphFunction F)
            (helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w)) := by
    -- Rewrite the first adjoint graph into a plain Fenchel-conjugate precomposition.
    funext w
    change -bifunctionGraphFunction (adjointOfConvexBifunction ⟨F, hF⟩) w =
      fenchelConjugate (m + n) (bifunctionGraphFunction F)
        (helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w)
    rw [helperForTheorem_6_30_10_adjointGraph_eq_neg_fenchelConjugate_precomp (F := ⟨F, hF⟩)
      (z := w)]
    simp
  have hTransport :=
    helperForTheorem_6_30_11_fenchelConjugate_precomp_coordinateLinearMap
      (m := m) (n := n) (f := fenchelConjugate (m + n) (bifunctionGraphFunction F))
  have hBiconj :
      fenchelConjugate (m + n) (fenchelConjugate (m + n) (bifunctionGraphFunction F)) =
        convexClosure (bifunctionGraphFunction F) := by
    -- Invoke the Section 16 biconjugation theorem on the graph function of `F`.
    simpa [convexClosure] using
      (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
        (n := m + n) (f := bifunctionGraphFunction F) (by simpa [ConvexBifunction] using hF))
  have hAtAppend := congrFun hBiconj (Fin.append u x)
  calc
    biadjointOfConvexBifunction ⟨F, hF⟩ u x
      = bifunctionGraphFunction (adjointOfConcaveBifunction (adjointOfConvexBifunctionAsConcave ⟨F, hF⟩))
          (Fin.append u x) := by
          simp [biadjointOfConvexBifunction, bifunctionGraphFunction]
    _ = fenchelConjugate (n + m)
          (fun w : Fin (n + m) → ℝ =>
            fenchelConjugate (m + n) (bifunctionGraphFunction F)
              (helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w))
          (-helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) (Fin.append u x)) := by
          -- Expand the second adjoint using the concave-adjoint graph formula.
          rw [helperForTheorem_6_30_11_adjointOfConcave_graph_eq_fenchelConjugate_precomp
            (G := adjointOfConvexBifunctionAsConcave ⟨F, hF⟩) (z := Fin.append u x)]
          rw [hGraphRewrite]
    _ = fenchelConjugate (m + n) (fenchelConjugate (m + n) (bifunctionGraphFunction F))
          (Fin.append u x) := by
          -- Cancel the coordinate shuffle inside the second conjugation.
          simpa using
            helperForTheorem_6_30_11_fenchelConjugate_precomp_coordinateLinearMap
              (m := m) (n := n)
              (f := fenchelConjugate (m + n) (bifunctionGraphFunction F))
              (z := Fin.append u x)
    _ = convexClosure (bifunctionGraphFunction F) (Fin.append u x) := by
          simpa using hAtAppend
    _ = convexBifunctionClosure F u x := by
          simp [convexBifunctionClosure]

/-- Helper for Theorem 6.30.11: the concave biadjoint is the closure of the original concave
bifunction. -/
lemma helperForTheorem_6_30_11_biadjointOfConcave_graph_eq_concaveBifunctionClosure_via_coordinate_shuffle
    {m n : ℕ}
    (G : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hG : ConcaveBifunction G) :
    biadjointOfConcaveBifunction ⟨G, hG⟩ = concaveBifunctionClosure G := by
  funext u x
  have hBiconj :
      fenchelConjugate (m + n)
        (fenchelConjugate (m + n) (fun t : Fin (m + n) → ℝ => -bifunctionGraphFunction G t)) =
        convexClosure (fun t : Fin (m + n) → ℝ => -bifunctionGraphFunction G t) := by
    -- Apply the convex biconjugation theorem to the negated graph of `G`.
    simpa [convexClosure] using
      (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
        (n := m + n) (f := fun t : Fin (m + n) → ℝ => -bifunctionGraphFunction G t)
        (by simpa [ConcaveBifunction] using hG))
  have hAtAppend := congrFun hBiconj (Fin.append u x)
  calc
    biadjointOfConcaveBifunction ⟨G, hG⟩ u x
      = bifunctionGraphFunction (adjointOfConvexBifunction (adjointOfConcaveBifunctionAsConvex ⟨G, hG⟩))
          (Fin.append u x) := by
          simp [biadjointOfConcaveBifunction, bifunctionGraphFunction]
    _ = -fenchelConjugate (n + m)
          (fun w : Fin (n + m) → ℝ =>
            fenchelConjugate (m + n) (fun t : Fin (m + n) → ℝ => -bifunctionGraphFunction G t)
              (-helperForTheorem_6_30_10_coordinateLinearMap (m := m) (n := n) w))
          (helperForTheorem_6_30_10_coordinateLinearMap (m := n) (n := m) (Fin.append u x)) := by
          -- Rewrite the second adjoint graph using Theorem 6.30.10 and then substitute the first
          -- adjoint graph formula for `G`.
          rw [helperForTheorem_6_30_10_adjointGraph_eq_neg_fenchelConjugate_precomp
            (F := adjointOfConcaveBifunctionAsConvex ⟨G, hG⟩) (z := Fin.append u x)]
          congr 1
          congr 1
          funext w
          exact helperForTheorem_6_30_11_adjointOfConcave_graph_eq_fenchelConjugate_precomp
            (G := ⟨G, hG⟩) (z := w)
    _ = -fenchelConjugate (m + n)
          (fenchelConjugate (m + n) (fun t : Fin (m + n) → ℝ => -bifunctionGraphFunction G t))
          (Fin.append u x) := by
          -- Cancel the coordinate shuffle in the same way, but with the extra minus convention.
          simpa using
            helperForTheorem_6_30_11_neg_fenchelConjugate_precomp_coordinateLinearMap
              (m := m) (n := n)
              (f := fenchelConjugate (m + n) (fun t : Fin (m + n) → ℝ => -bifunctionGraphFunction G t))
              (z := Fin.append u x)
    _ = -(convexClosure (fun t : Fin (m + n) → ℝ => -bifunctionGraphFunction G t) (Fin.append u x)) := by
          simpa using congrArg Neg.neg hAtAppend
    _ = concaveBifunctionClosure G u x := by
          simp [concaveBifunctionClosure, concaveClosure, convexClosure]

/-!
Route correction for Theorem 6.30.11:

The original proof cites Theorem 12.2 at the level of the graph function. The local transport
lemmas below reduce the remaining work to a graph-level fixed-point theorem for
`convexFunctionClosure` and `concaveClosure`.

Under the current repository semantics, that route breaks in the closed improper branch:
`convexFunctionClosure_eq_of_closedConvexFunction` still requires the extra hypothesis
`∀ x, f x ≠ ⊥`, while `convexFunctionClosure_eq_bot_of_exists_bot` collapses any function with one
`⊥` value to the constant `⊥` closure. Therefore the two fixed-point lemmas below remain the exact
upstream blocker for the theorem as currently formalized.
-/

/-- Helper for Theorem 6.30.11: a closed convex bifunction is fixed by the canonical graph
closure. This is the graph-level lift of the Chapter 2 fixed-point theorem for closed convex
functions. -/
lemma helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed_of_graph_ne_bot
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexBifunction F)
    (hGraphNeBot : ∀ z : Fin (m + n) → ℝ, bifunctionGraphFunction F z ≠ (⊥ : EReal)) :
    convexBifunctionClosure F = F := by
  funext u x
  -- Apply the graph-level fixed-point theorem and then evaluate it on the concatenated point.
  have hClosure :
      convexClosure (bifunctionGraphFunction F) = bifunctionGraphFunction F := by
    simpa [convexClosure] using
      (convexFunctionClosure_eq_of_closedConvexFunction
        (f := bifunctionGraphFunction F) hClosed.2 hGraphNeBot)
  simpa [convexBifunctionClosure, bifunctionGraphFunction] using
    congrFun hClosure (Fin.append u x)

/-- Helper for Theorem 6.30.11: the closed proper convex branch is already covered by the
graph-level fixed-point theorem, because properness rules out `⊥` on the graph. -/
lemma helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed_proper
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexBifunction F)
    (hProper : ProperConvexBifunction F) :
    convexBifunctionClosure F = F := by
  -- Properness supplies exactly the no-`⊥` hypothesis required by the closure fixed-point lemma.
  refine
    helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed_of_graph_ne_bot
      (F := F) hClosed ?_
  intro z
  exact hProper.2.1.1 z

/-- Helper for Theorem 6.30.11: a closed concave bifunction whose negated graph never attains
`⊥` is fixed by the canonical concave graph closure. -/
lemma helperForTheorem_6_30_11_concaveBifunctionClosure_eq_self_of_closed_of_neg_graph_ne_bot
    {m n : ℕ}
    {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConcaveBifunction G)
    (hNegGraphNeBot :
      ∀ z : Fin (m + n) → ℝ, (-bifunctionGraphFunction G z) ≠ (⊥ : EReal)) :
    concaveBifunctionClosure G = G := by
  funext u x
  -- Negate the graph, apply the convex fixed-point theorem there, and transport back.
  have hClosedNegGraph :
      ClosedConvexFunction (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) := by
    simpa [ClosedConcaveBifunction, ClosedConcaveERealFunction, ConcaveBifunction] using hClosed
  have hClosure :
      convexClosure (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) =
        (fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z) := by
    simpa [convexClosure] using
      (convexFunctionClosure_eq_of_closedConvexFunction
        (f := fun z : Fin (m + n) → ℝ => -bifunctionGraphFunction G z)
        hClosedNegGraph hNegGraphNeBot)
  simpa [concaveBifunctionClosure, concaveClosure, bifunctionGraphFunction] using
    congrArg Neg.neg (congrFun hClosure (Fin.append u x))

/-- Helper for Theorem 6.30.11: the closed proper concave branch is already covered by the
graph-level fixed-point theorem after negating the graph, because properness rules out `⊥`
there. -/
lemma helperForTheorem_6_30_11_concaveBifunctionClosure_eq_self_of_closed_proper
    {m n : ℕ}
    {G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConcaveBifunction G)
    (hProper : ProperConcaveBifunction G) :
    concaveBifunctionClosure G = G := by
  -- Proper concavity is proper convexity of the negated graph, so the no-`⊥` hypothesis persists.
  refine
    helperForTheorem_6_30_11_concaveBifunctionClosure_eq_self_of_closed_of_neg_graph_ne_bot
      (G := G) hClosed ?_
  intro z
  simpa [ProperConcaveERealFunction] using hProper.2.1.1 z

/-- Helper for Theorem 6.30.11: the convex bifunction closure fixes the constant `⊤`
bifunction. -/
lemma helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_eq_const_top
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hTop : F = fun _ _ => (⊤ : EReal)) :
    convexBifunctionClosure F = F := by
  subst F
  funext u x
  -- The graph is constant `⊤`, and the Chapter 2 closure leaves that function unchanged.
  simpa [convexBifunctionClosure, convexClosure, bifunctionGraphFunction] using
    congrFun (convexFunctionClosure_const_top (n := m + n)) (Fin.append u x)

/-- Helper for Theorem 6.30.11: the convex bifunction closure fixes the constant `⊥`
bifunction. -/
lemma helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_eq_const_bot
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hBot : F = fun _ _ => (⊥ : EReal)) :
    convexBifunctionClosure F = F := by
  subst F
  funext u x
  have hClosure :
      convexFunctionClosure (fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) =
        (fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) :=
    convexFunctionClosure_eq_bot_of_exists_bot
      (f := fun _ : Fin (m + n) → ℝ => (⊥ : EReal)) ⟨0, rfl⟩
  -- The graph is constant `⊥`, so the Chapter 2 closure collapses to the same constant.
  simpa [convexBifunctionClosure, convexClosure, bifunctionGraphFunction] using
    congrFun hClosure (Fin.append u x)

end Section30
end Chap06
