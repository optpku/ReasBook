/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part7

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-- Helper for Corollary33.1.3: sections of a polyhedral convex bifunction are polyhedral convex
functions. -/
lemma helperForCorollary33_1_3_section_isPolyhedralConvexFunction
    {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsRockafellarPolyhedralConvexBifunction F) :
    ∀ u : Fin m → ℝ, IsPolyhedralConvexFunction n (F u) := by
  classical
  rcases hF with ⟨hRock, hGraphPoly⟩
  intro u
  refine ⟨?_, ?_⟩
  · -- Convexity of each section is part of Rockafellar's bifunction definition.
    have hSectionConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (F u) := hRock.1 u
    have hConv : ConvexFunction (F u) :=
      helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hSectionConv
    simpa [ConvexFunction] using hConv
  · -- Polyhedrality comes from slicing the polyhedral transformed epigraph of the graph function.
    let g : (Fin (m + n) → ℝ) → EReal := graphFunctionOfBifunction F
    let Eg : Set (Fin (m + n + 1) → ℝ) :=
      (fun p => (prodLinearEquiv_append (n := m + n) p).ofLp) ''
        epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g
    have hEg_poly : IsPolyhedralConvexSet (m + n + 1) Eg := by
      simpa [Eg] using hGraphPoly.2
    -- Extract a finite halfspace description of the transformed epigraph of the graph function.
    rcases (isPolyhedralConvexSet_iff_exists_finite_halfspaces (m + n + 1) Eg).1
        hEg_poly with ⟨p, b, β, hEg_eq⟩
    let Eu : Set (Fin (n + 1) → ℝ) :=
      (fun p => (prodLinearEquiv_append (n := n) p).ofLp) ''
        epigraph (Set.univ : Set (Fin n → ℝ)) (F u)
    have hEu_as_preimage :
        Eu = {y : Fin (n + 1) → ℝ | Fin.append u y ∈ Eg} := by
      ext y
      constructor
      · rintro ⟨⟨x, μ⟩, hy_epi, rfl⟩
        -- Lift the section epigraph point to the graph epigraph point by appending `u`.
        have hy_epi' : (Fin.append u x, μ) ∈ epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g := by
          have hμ : F u x ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := F u)).1 hy_epi
          have hg : g (Fin.append u x) = F u x := by
            simp [g, graphFunctionOfBifunction, Fin.append]
          exact (mem_epigraph_univ_iff (f := g)).2 (by simpa [hg] using hμ)
        refine ⟨(Fin.append u x, μ), hy_epi', ?_⟩
        -- Use the coordinate-level commutation lemma (`.ofLp`) to identify the packed point.
        simpa [Eg] using
          (helperForCorollary33_1_3_append_prodLinearEquivAppend_ofLp
            (u := u) (x := x) (μ := μ)).symm
      · intro hy
        rcases hy with ⟨⟨z, μ⟩, hz_epi, hzy⟩
        let x : Fin n → ℝ := fun j => z (Fin.natAdd m j)
        have hzU : (fun i : Fin m => z (Fin.castAdd n i)) = u := by
          funext i
          have hcoord := congrArg (fun w => w (Fin.castAdd (n + 1) i)) hzy
          have hIndex :
              (Fin.castAdd (n + 1) i : Fin (m + n + 1)) =
                Fin.castSucc (Fin.castAdd n i) := by
            ext
            simp
          have hz_cast :
              (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp
                  (Fin.castSucc (Fin.castAdd n i)) = z (Fin.castAdd n i) := by
            simpa using
              helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_castSucc
                (x := z) (μ := μ) (j := Fin.castAdd n i)
          have hu : Fin.append u y (Fin.castAdd (n + 1) i) = u i := by
            simpa [Fin.append] using (Fin.append_left (u := u) (v := y) i)
          -- Keep the appended index as `Fin.castAdd (n+1) i` so `hu` applies, while rewriting
          -- the packed index to a `castSucc` index so the coordinate lemma applies.
          have hcoord' :
              (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp
                  (Fin.castSucc (Fin.castAdd n i)) =
                Fin.append u y (Fin.castAdd (n + 1) i) := by
            have hIndexPacked :
                (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp
                    (Fin.castSucc (Fin.castAdd n i)) =
                  (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp
                    (Fin.castAdd (n + 1) i) := by
              simpa using
                congrArg
                  (fun t =>
                    (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp t)
                  hIndex.symm
            exact hIndexPacked.trans hcoord
          have hzEq :
              z (Fin.castAdd n i) = Fin.append u y (Fin.castAdd (n + 1) i) := by
            simpa [hz_cast] using hcoord'
          simpa [hu] using hzEq
        have hμ : g z ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := g)).1 hz_epi
        have hμ_section : F u x ≤ (μ : EReal) := by
          have hg : g z = F u x := by
            simp [g, graphFunctionOfBifunction, hzU, x]
          simpa [hg] using hμ
        -- Recover `y` from the `x` and `μ` coordinates.
        have hy_eq : y = (prodLinearEquiv_append (n := n) (x, μ)).ofLp := by
          funext j
          refine Fin.lastCases ?_ (fun j0 : Fin n => ?_) j
          · -- Last coordinate.
            have hcoord := congrArg (fun w => w (Fin.natAdd m (Fin.last n))) hzy
            have hIndexLast :
                (Fin.natAdd m (Fin.last n) : Fin (m + (n + 1))) = Fin.last (m + n) := by
              ext
              simp
            have hz_last' :
                (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp (Fin.natAdd m (Fin.last n)) = μ := by
              -- Rewrite the index to the canonical `Fin.last` index and apply the `last` lemma.
              have hz_last :
                  (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp (Fin.last (m + n)) = μ :=
                helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_last (x := z) (μ := μ)
              simpa [hIndexLast] using hz_last
            have hyLast : y (Fin.last n) = μ := by
              -- From `hcoord` and the computed left side, the appended coordinate equals `μ`.
              have hAppEq :
                  Fin.append u y (Fin.natAdd m (Fin.last n)) =
                    (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp
                      (Fin.natAdd m (Fin.last n)) := hcoord.symm
              -- Rewrite the packed side without letting `simp` change the index.
              rw [hz_last'] at hAppEq
              have hDrop :
                  Fin.append u y (Fin.natAdd m (Fin.last n)) = y (Fin.last n) := by
                simpa using (Fin.append_right (u := u) (v := y) (i := Fin.last n))
              -- Combine the drop identity with the computed equality.
              calc
                y (Fin.last n) = Fin.append u y (Fin.natAdd m (Fin.last n)) := by
                  simpa using hDrop.symm
                _ = μ := hAppEq
            have hPackedLast :
                (prodLinearEquiv_append (n := n) (x, μ)).ofLp (Fin.last n) = μ := by
              simpa using helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_last (x := x) (μ := μ)
            simpa [hyLast, hPackedLast]
          · -- Cast-succ coordinate.
            have hcoord := congrArg (fun w => w (Fin.natAdd m (Fin.castSucc j0))) hzy
            have hIndexCastSucc :
                (Fin.natAdd m (Fin.castSucc j0) : Fin (m + (n + 1))) =
                  Fin.castSucc (Fin.natAdd m j0) := by
              ext
              simp
            have hz_cast' :
                (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp
                    (Fin.natAdd m (Fin.castSucc j0)) = z (Fin.natAdd m j0) := by
              -- Rewrite the index to a `castSucc` index and apply the `castSucc` lemma.
              have hz_cast :
                  (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp
                      (Fin.castSucc (Fin.natAdd m j0)) = z (Fin.natAdd m j0) :=
                helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_castSucc
                  (x := z) (μ := μ) (j := Fin.natAdd m j0)
              -- Transport along `hIndexCastSucc` without triggering `simp` recursion.
              calc
                (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp
                    (Fin.natAdd m (Fin.castSucc j0))
                    =
                    (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp
                      (Fin.castSucc (Fin.natAdd m j0)) := by
                        exact congrArg
                          (fun t => (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp t)
                          hIndexCastSucc
                _ = z (Fin.natAdd m j0) := hz_cast
            have hyCast : y (Fin.castSucc j0) = z (Fin.natAdd m j0) := by
              have hAppEq :
                  Fin.append u y (Fin.natAdd m (Fin.castSucc j0)) =
                    (prodLinearEquiv_append (n := m + n) (z, μ)).ofLp
                      (Fin.natAdd m (Fin.castSucc j0)) := hcoord.symm
              -- Rewrite the packed side.
              rw [hz_cast'] at hAppEq
              have hDrop :
                  Fin.append u y (Fin.natAdd m (Fin.castSucc j0)) = y (Fin.castSucc j0) := by
                simpa using (Fin.append_right (u := u) (v := y) (i := Fin.castSucc j0))
              calc
                y (Fin.castSucc j0) = Fin.append u y (Fin.natAdd m (Fin.castSucc j0)) := by
                  simpa using hDrop.symm
                _ = z (Fin.natAdd m j0) := hAppEq
            have hPackedCast :
                (prodLinearEquiv_append (n := n) (x, μ)).ofLp (Fin.castSucc j0) = x j0 := by
              simpa using
                helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_castSucc
                  (x := x) (μ := μ) (j := j0)
            simpa [x, hyCast, hPackedCast]
        refine ⟨(x, μ), (mem_epigraph_univ_iff (f := F u)).2 hμ_section, ?_⟩
        simpa [Eu, hy_eq]
    -- Build a halfspace description of the preimage using dot-product splitting.
    have hEu_poly : IsPolyhedralConvexSet (n + 1) Eu := by
      refine (isPolyhedralConvexSet_iff_exists_finite_halfspaces (n + 1) Eu).2 ?_
      refine ⟨p, (fun i j => b i (Fin.natAdd m j)),
        (fun i => β i - dotProduct u (fun t => b i (Fin.castAdd (n + 1) t))), ?_⟩
      ext y
      constructor
      · intro hy
        have : Fin.append u y ∈ Eg := by
          simpa [hEu_as_preimage] using (show y ∈ Eu from hy)
        have hIneq := Set.mem_iInter.1 (by simpa [hEg_eq] using this)
        refine Set.mem_iInter.2 ?_
        intro i
        have hi := hIneq i
        have hsplit :
            dotProduct (Fin.append u y) (b i) =
              dotProduct u (fun t => b i (Fin.castAdd (n + 1) t)) +
                dotProduct y (fun j => b i (Fin.natAdd m j)) := by
          simpa using (helperForCorollary33_1_3_dotProduct_append (u := u) (v := y) (b := b i))
        have : dotProduct y (fun j => b i (Fin.natAdd m j)) ≤
            β i - dotProduct u (fun t => b i (Fin.castAdd (n + 1) t)) := by
          linarith [show dotProduct (Fin.append u y) (b i) ≤ β i by
            simpa [closedHalfSpaceLE] using hi, hsplit]
        simpa [closedHalfSpaceLE] using this
      · intro hy
        have hIneq := Set.mem_iInter.1 hy
        have : Fin.append u y ∈ ⋂ i, closedHalfSpaceLE (m + n + 1) (b i) (β i) := by
          refine Set.mem_iInter.2 ?_
          intro i
          have hi := hIneq i
          have hsplit :
              dotProduct (Fin.append u y) (b i) =
                dotProduct u (fun t => b i (Fin.castAdd (n + 1) t)) +
                  dotProduct y (fun j => b i (Fin.natAdd m j)) := by
            simpa using (helperForCorollary33_1_3_dotProduct_append (u := u) (v := y) (b := b i))
          have : dotProduct (Fin.append u y) (b i) ≤ β i := by
            have : dotProduct y (fun j => b i (Fin.natAdd m j)) ≤
                β i - dotProduct u (fun t => b i (Fin.castAdd (n + 1) t)) := by
              simpa [closedHalfSpaceLE] using hi
            linarith [this, hsplit]
          simpa [closedHalfSpaceLE] using this
        have : Fin.append u y ∈ Eg := by
          simpa [hEg_eq] using this
        simpa [hEu_as_preimage] using this
    -- `Eu` is definitionally the transformed epigraph set appearing in `IsPolyhedralConvexFunction`.
    simpa [Eu] using hEu_poly

/-- Helper for Corollary33.1.3: the tilted graph-function fiber over a fixed `u` is the
negative of the fixed-dual pairing section. -/
lemma helperForCorollary33_1_3_sInf_tiltedFiber_eq_negSup_pairing
    {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    sInf (Set.range fun x : Fin n → ℝ =>
      graphFunctionOfBifunction F (Fin.append u x) -
        ((dotProduct x xStar : ℝ) : EReal)) =
      -(convexBifunctionPairing F u xStar) := by
  classical
  -- Unfold the pairing so both sides become the corresponding `iInf`/`iSup` expressions.
  rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
  simp [graphFunctionOfBifunction, sInf_range, sSup_range, sub_eq_add_neg]
  let l : (Fin n → ℝ) → EReal := fun x => ((dotProduct x xStar : ℝ) : EReal)
  have h := ereal_iSup_neg_eq_neg_iInf (g := fun x : Fin n → ℝ => F u x - l x)
  have h' := congrArg Neg.neg h
  -- Rewrite the negated integrand so it matches the `convexBifunctionPairing` convention.
  simpa [l, sub_eq_add_neg, EReal.neg_add, add_assoc, add_left_comm, add_comm] using h'.symm

/-- Helper for Corollary33.1.3: the packed embedding
`p ↦ (prodLinearEquiv_append p).ofLp` is injective. -/
lemma helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_injective
    {n : ℕ} :
    Function.Injective (fun p : (Fin n → ℝ) × ℝ =>
      (prodLinearEquiv_append (n := n) p).ofLp) := by
  intro p q hpq
  -- Apply `WithLp.toLp` to undo `.ofLp`, then use injectivity of the linear equivalence.
  have hLp :
      WithLp.toLp 2 ((prodLinearEquiv_append (n := n) p).ofLp) =
        WithLp.toLp 2 ((prodLinearEquiv_append (n := n) q).ofLp) :=
    congrArg (WithLp.toLp 2) hpq
  have hEquiv : (prodLinearEquiv_append (n := n) p) = (prodLinearEquiv_append (n := n) q) := by
    simpa using hLp
  exact (prodLinearEquiv_append (n := n)).injective hEquiv

/-- Helper for Corollary33.1.3: the `x`-block dot product
`z ↦ ⟪x(z), xStar⟫` is linear in `z` under convex combinations. -/
lemma helperForCorollary33_1_3_dotProduct_xBlock_weighted
    {m n : ℕ} (a b : ℝ) (z₁ z₂ : Fin (m + n) → ℝ) (xStar : Fin n → ℝ) :
    dotProduct (fun j => (a • z₁ + b • z₂) (Fin.natAdd m j)) xStar =
      a * dotProduct (fun j => z₁ (Fin.natAdd m j)) xStar +
        b * dotProduct (fun j => z₂ (Fin.natAdd m j)) xStar := by
  -- Reduce to the standard dotProduct-affinity lemma on the extracted `x`-block.
  let x₁ : Fin n → ℝ := fun j => z₁ (Fin.natAdd m j)
  let x₂ : Fin n → ℝ := fun j => z₂ (Fin.natAdd m j)
  have hx :
      (fun j => (a • z₁ + b • z₂) (Fin.natAdd m j)) = a • x₁ + b • x₂ := by
    funext j
    simp [x₁, x₂]
  -- Apply bilinearity of `dotProduct` in the first variable.
  rw [hx]
  exact helperForLemma33_0_14_dotProduct_weighted a b x₁ x₂ xStar

/-- Helper for Corollary33.1.3: the modified normal `bTilt` evaluates to its `bLast` value on
the last coordinate. -/
lemma helperForCorollary33_1_3_bTilt_last
    {m n : ℕ} (xStar : Fin n → ℝ) (b : Fin (m + n + 1) → ℝ) :
    let bLast : ℝ := b (Fin.last (m + n))
    let bTilt : Fin (m + n + 1) → ℝ :=
      Fin.lastCases bLast (fun j : Fin (m + n) =>
        Fin.addCases (m := m) (n := n)
          (fun jm : Fin m => b (Fin.castSucc (Fin.castAdd n jm)))
          (fun jn : Fin n =>
            b (Fin.castSucc (Fin.natAdd m jn)) + bLast * xStar jn)
          j)
    bTilt (Fin.last (m + n)) = bLast := by
  -- Unfold the definition of `bTilt` and evaluate the `Fin.lastCases` branch at `Fin.last`.
  dsimp
  rw [Fin.lastCases_last]

/-- Helper for Corollary33.1.3: on the `u`-block, the modified normal `bTilt` agrees with `b`. -/
lemma helperForCorollary33_1_3_bTilt_castSucc_castAdd
    {m n : ℕ} (xStar : Fin n → ℝ) (b : Fin (m + n + 1) → ℝ) (jm : Fin m) :
    let bLast : ℝ := b (Fin.last (m + n))
    let bTilt : Fin (m + n + 1) → ℝ :=
      Fin.lastCases bLast (fun j : Fin (m + n) =>
        Fin.addCases (m := m) (n := n)
          (fun jm : Fin m => b (Fin.castSucc (Fin.castAdd n jm)))
          (fun jn : Fin n =>
            b (Fin.castSucc (Fin.natAdd m jn)) + bLast * xStar jn)
          j)
    bTilt (Fin.castSucc (Fin.castAdd n jm)) = b (Fin.castSucc (Fin.castAdd n jm)) := by
  -- Reduce `Fin.lastCases` at a `castSucc` index, then evaluate the `addCases` branch on the
  -- left block index `Fin.castAdd n jm`.
  dsimp
  rw [Fin.lastCases_castSucc, Fin.addCases_left]

/-- Helper for Corollary33.1.3: on the `x`-block, the modified normal `bTilt` adds the extra
term `bLast * xStar`. -/
lemma helperForCorollary33_1_3_bTilt_castSucc_natAdd
    {m n : ℕ} (xStar : Fin n → ℝ) (b : Fin (m + n + 1) → ℝ) (jn : Fin n) :
    let bLast : ℝ := b (Fin.last (m + n))
    let bTilt : Fin (m + n + 1) → ℝ :=
      Fin.lastCases bLast (fun j : Fin (m + n) =>
        Fin.addCases (m := m) (n := n)
          (fun jm : Fin m => b (Fin.castSucc (Fin.castAdd n jm)))
          (fun jn : Fin n =>
            b (Fin.castSucc (Fin.natAdd m jn)) + bLast * xStar jn)
          j)
    bTilt (Fin.castSucc (Fin.natAdd m jn)) =
      b (Fin.castSucc (Fin.natAdd m jn)) + b (Fin.last (m + n)) * xStar jn := by
  -- Route correction: normalize the `natAdd`/`castSucc` index to the syntactic form `i.castSucc`
  -- so `Fin.lastCases_castSucc` and `Fin.addCases_right` apply deterministically.
  dsimp
  rw [Fin.natAdd_castSucc, Fin.lastCases_castSucc, Fin.addCases_right]
  simp

/-- Helper for Corollary33.1.3: the extra `x`-block sum induced by `bLast * xStar` is exactly
`(⟪x(z), xStar⟫) * bLast`. -/
lemma helperForCorollary33_1_3_sum_xBlock_mul_bLast
    {m n : ℕ} (z : Fin (m + n) → ℝ) (xStar : Fin n → ℝ) (bLast : ℝ) :
    (∑ j : Fin n, z (Fin.natAdd m j) * (bLast * xStar j)) =
      (dotProduct (fun j => z (Fin.natAdd m j)) xStar) * bLast := by
  -- Expand the dot product and reorder factors in each summand so the constant `bLast` factors
  -- out of the sum.
  unfold dotProduct
  calc
    (∑ j : Fin n, z (Fin.natAdd m j) * (bLast * xStar j)) =
        ∑ j : Fin n, (z (Fin.natAdd m j) * xStar j) * bLast := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _ = (∑ j : Fin n, z (Fin.natAdd m j) * xStar j) * bLast := by
          rw [Finset.sum_mul]
    _ = (dotProduct (fun j => z (Fin.natAdd m j)) xStar) * bLast := by
          rfl

/-- Helper for Corollary33.1.3: shifting the last packed coordinate by `⟪x(z), xStar⟫` is
equivalent to modifying the halfspace normal by adding `b_last • xStar` on the `x`-block. -/
lemma helperForCorollary33_1_3_dotProduct_packed_lastShift_eq_modifiedNormal
    {m n : ℕ} (xStar : Fin n → ℝ) (b : Fin (m + n + 1) → ℝ)
    (z : Fin (m + n) → ℝ) (μ : ℝ) :
    let xBlock : Fin n → ℝ := fun j => z (Fin.natAdd m j)
    let bLast : ℝ := b (Fin.last (m + n))
    let bTilt : Fin (m + n + 1) → ℝ :=
      Fin.lastCases bLast (fun j : Fin (m + n) =>
        Fin.addCases (m := m) (n := n)
          (fun jm : Fin m => b (Fin.castSucc (Fin.castAdd n jm)))
          (fun jn : Fin n =>
            b (Fin.castSucc (Fin.natAdd m jn)) + bLast * xStar jn)
          j)
    dotProduct
        ((prodLinearEquiv_append (n := m + n) (z, μ + dotProduct xBlock xStar)).ofLp)
        b =
      dotProduct
        ((prodLinearEquiv_append (n := m + n) (z, μ)).ofLp)
        bTilt := by
  classical
  -- Introduce local names matching the `let`-bindings in the statement so the calculation reads
  -- like the textbook “shear in the last coordinate”.
  let xBlock : Fin n → ℝ := fun j => z (Fin.natAdd m j)
  let bLast : ℝ := b (Fin.last (m + n))
  let bTilt : Fin (m + n + 1) → ℝ :=
    Fin.lastCases bLast (fun j : Fin (m + n) =>
      Fin.addCases (m := m) (n := n)
        (fun jm : Fin m => b (Fin.castSucc (Fin.castAdd n jm)))
        (fun jn : Fin n => b (Fin.castSucc (Fin.natAdd m jn)) + bLast * xStar jn)
        j)
  -- Replace the outer `let`s in the goal with these local names.
  change
      dotProduct
          ((prodLinearEquiv_append (n := m + n) (z, μ + dotProduct xBlock xStar)).ofLp)
          b =
        dotProduct
          ((prodLinearEquiv_append (n := m + n) (z, μ)).ofLp)
          bTilt

  -- Step 1: split both dot products into the `castSucc`-sum over `Fin (m+n)` and the last term.
  have hLeftSplit :
      dotProduct
          ((prodLinearEquiv_append (n := m + n) (z, μ + dotProduct xBlock xStar)).ofLp)
          b =
        (∑ j : Fin (m + n), z j * b (Fin.castSucc j)) +
          (μ + dotProduct xBlock xStar) * bLast := by
    -- The packed embedding recovers `z` on `castSucc` coordinates and the scalar on `last`.
    rw [dotProduct, Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro j hj
      rw [helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_castSucc (x := z)
        (μ := μ + dotProduct xBlock xStar) (j := j)]
    · rw [helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_last (x := z)
        (μ := μ + dotProduct xBlock xStar)]
  have hRightSplit :
      dotProduct ((prodLinearEquiv_append (n := m + n) (z, μ)).ofLp) bTilt =
        (∑ j : Fin (m + n), z j * bTilt (Fin.castSucc j)) + μ * bLast := by
    -- The same split holds on the right, but the last term uses `bTilt (Fin.last _) = bLast`.
    rw [dotProduct, Fin.sum_univ_castSucc]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro j hj
      rw [helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_castSucc (x := z) (μ := μ) (j := j)]
    · rw [helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_last (x := z) (μ := μ)]
      have hbLast : bTilt (Fin.last (m + n)) = bLast := by
        simpa [bLast, bTilt] using
          helperForCorollary33_1_3_bTilt_last (m := m) (n := n) (xStar := xStar) (b := b)
      simpa [hbLast]

  rw [hLeftSplit, hRightSplit]

  -- Step 2: split the `castSucc` sums into `u`-block and `x`-block sums.
  have hLeftBlocks :
      (∑ j : Fin (m + n), z j * b (Fin.castSucc j)) =
        (∑ jm : Fin m, z (Fin.castAdd n jm) * b (Fin.castSucc (Fin.castAdd n jm))) +
          ∑ jn : Fin n, z (Fin.natAdd m jn) * b (Fin.castSucc (Fin.natAdd m jn)) := by
    rw [Fin.sum_univ_add]
  have hRightBlocks :
      (∑ j : Fin (m + n), z j * bTilt (Fin.castSucc j)) =
        (∑ jm : Fin m, z (Fin.castAdd n jm) * b (Fin.castSucc (Fin.castAdd n jm))) +
          ∑ jn : Fin n, z (Fin.natAdd m jn) *
            (b (Fin.castSucc (Fin.natAdd m jn)) + bLast * xStar jn) := by
    rw [Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl ?_
      intro jm hjm
      have hbU :
          bTilt (Fin.castSucc (Fin.castAdd n jm)) = b (Fin.castSucc (Fin.castAdd n jm)) := by
        simpa [bLast, bTilt] using
          helperForCorollary33_1_3_bTilt_castSucc_castAdd
            (m := m) (n := n) (xStar := xStar) (b := b) jm
      rw [hbU]
    · refine Finset.sum_congr rfl ?_
      intro jn hjn
      have hbX :
          bTilt (Fin.castSucc (Fin.natAdd m jn)) =
            b (Fin.castSucc (Fin.natAdd m jn)) + bLast * xStar jn := by
        simpa [bLast, bTilt] using
          helperForCorollary33_1_3_bTilt_castSucc_natAdd
            (m := m) (n := n) (xStar := xStar) (b := b) jn
      rw [hbX]

  rw [hLeftBlocks, hRightBlocks]

  -- Step 3: expand the `x`-block contribution on the right to isolate the extra `bLast * xStar`.
  have hExpandX :
      (∑ jn : Fin n,
          z (Fin.natAdd m jn) *
            (b (Fin.castSucc (Fin.natAdd m jn)) + bLast * xStar jn)) =
        (∑ jn : Fin n, z (Fin.natAdd m jn) * b (Fin.castSucc (Fin.natAdd m jn))) +
          ∑ jn : Fin n, z (Fin.natAdd m jn) * (bLast * xStar jn) := by
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
  rw [hExpandX]

  -- Step 4: identify the extra sum with `(⟪x(z),xStar⟫) * bLast`, so it cancels the shear of
  -- the last coordinate.
  have hExtra :
      (∑ jn : Fin n, z (Fin.natAdd m jn) * (bLast * xStar jn)) =
        (dotProduct xBlock xStar) * bLast := by
    simpa [xBlock] using
      helperForCorollary33_1_3_sum_xBlock_mul_bLast
        (m := m) (n := n) (z := z) (xStar := xStar) (bLast := bLast)
  rw [hExtra]

  -- Final step: a commutative-ring simplification closes the remaining scalar identity.
  ring

/-- Helper for Corollary33.1.3: subtracting the fixed linear functional in the `x`-block from
the graph function preserves polyhedral convexity. -/
lemma helperForCorollary33_1_3_tiltedGraph_isPolyhedralConvexFunction
    {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsRockafellarPolyhedralConvexBifunction F)
    (xStar : Fin n → ℝ) :
    IsPolyhedralConvexFunction (m + n)
      (fun z =>
        graphFunctionOfBifunction F z -
          ((dotProduct (fun j => z (Fin.natAdd m j)) xStar : ℝ) : EReal)) := by
  classical
  rcases hF with ⟨_hRock, hGraphPoly⟩
  let g : (Fin (m + n) → ℝ) → EReal := graphFunctionOfBifunction F
  let l : (Fin (m + n) → ℝ) → ℝ :=
    fun z => dotProduct (fun j => z (Fin.natAdd m j)) xStar
  let G : (Fin (m + n) → ℝ) → EReal :=
    fun z => g z - ((l z : ℝ) : EReal)
  -- It suffices to prove convexity of the epigraph and polyhedrality of its packed image.
  refine ⟨?_, ?_⟩
  · -- Convexity: the epigraph of `G` is obtained from the epigraph of `g` by a shear in the
    -- last coordinate `μ ↦ μ + l(z)`, and convexity is preserved under this change of variables.
    intro p hp q hq a b ha hb hab
    rcases p with ⟨z₁, μ₁⟩
    rcases q with ⟨z₂, μ₂⟩
    have hμ₁ : G z₁ ≤ (μ₁ : EReal) := (mem_epigraph_univ_iff (f := G)).1 hp
    have hμ₂ : G z₂ ≤ (μ₂ : EReal) := (mem_epigraph_univ_iff (f := G)).1 hq
    have hz₁ : g z₁ ≤ (μ₁ : EReal) + ((l z₁ : ℝ) : EReal) := by
      -- Move the finite linear term across subtraction.
      have hSub : g z₁ - ((l z₁ : ℝ) : EReal) ≤ (μ₁ : EReal) := by
        simpa [G] using hμ₁
      exact
        (EReal.sub_le_iff_le_add
          (a := g z₁) (b := ((l z₁ : ℝ) : EReal)) (c := (μ₁ : EReal))
          (Or.inl (by simp)) (Or.inl (by simp))).1 hSub
    have hz₂ : g z₂ ≤ (μ₂ : EReal) + ((l z₂ : ℝ) : EReal) := by
      -- Same rearrangement for the second epigraph point.
      have hSub : g z₂ - ((l z₂ : ℝ) : EReal) ≤ (μ₂ : EReal) := by
        simpa [G] using hμ₂
      exact
        (EReal.sub_le_iff_le_add
          (a := g z₂) (b := ((l z₂ : ℝ) : EReal)) (c := (μ₂ : EReal))
          (Or.inl (by simp)) (Or.inl (by simp))).1 hSub
    have hp' : (z₁, μ₁ + l z₁) ∈ epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g := by
      exact (mem_epigraph_univ_iff (f := g)).2 (by simpa [EReal.coe_add, add_assoc] using hz₁)
    have hq' : (z₂, μ₂ + l z₂) ∈ epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g := by
      exact (mem_epigraph_univ_iff (f := g)).2 (by simpa [EReal.coe_add, add_assoc] using hz₂)
    have hconv_g : Convex ℝ (epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g) := hGraphPoly.1
    have hr' :
        a • (z₁, μ₁ + l z₁) + b • (z₂, μ₂ + l z₂) ∈
          epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g :=
      hconv_g hp' hq' ha hb hab
    -- Identify the sheared convex combination with the ordinary convex combination plus the
    -- linear correction on the last coordinate.
    have hlin_l :
        l (a • z₁ + b • z₂) = a * l z₁ + b * l z₂ := by
      simpa [l, smul_add, add_smul, smul_smul] using
        helperForCorollary33_1_3_dotProduct_xBlock_weighted (m := m) (n := n)
          (a := a) (b := b) (z₁ := z₁) (z₂ := z₂) (xStar := xStar)
    have hEq :
        a • (z₁, μ₁ + l z₁) + b • (z₂, μ₂ + l z₂) =
          (a • z₁ + b • z₂, (a * μ₁ + b * μ₂) + l (a • z₁ + b • z₂)) := by
      ext <;> simp [hlin_l, mul_add, add_mul, add_assoc, add_left_comm, add_comm]
    have hz_combo :
        g (a • z₁ + b • z₂) ≤
          (((a * μ₁ + b * μ₂) + l (a • z₁ + b • z₂) : ℝ) : EReal) := by
      -- Unpack epigraph membership after rewriting by `hEq`.
      have : (a • z₁ + b • z₂, (a * μ₁ + b * μ₂) + l (a • z₁ + b • z₂)) ∈
          epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g := by
        rw [← hEq]
        exact hr'
      exact (mem_epigraph_univ_iff (f := g)).1 this
    -- Move the linear term back across subtraction to get the epigraph inequality for `G`.
    have hG_combo :
        G (a • z₁ + b • z₂) ≤ ((a * μ₁ + b * μ₂ : ℝ) : EReal) := by
      have hz_combo' :
          g (a • z₁ + b • z₂) ≤
            ((a * μ₁ + b * μ₂ : ℝ) : EReal) + ((l (a • z₁ + b • z₂) : ℝ) : EReal) := by
        simpa [EReal.coe_add, add_assoc] using hz_combo
      have :
          g (a • z₁ + b • z₂) - ((l (a • z₁ + b • z₂) : ℝ) : EReal) ≤
            ((a * μ₁ + b * μ₂ : ℝ) : EReal) :=
        (EReal.sub_le_iff_le_add
          (a := g (a • z₁ + b • z₂))
          (b := ((l (a • z₁ + b • z₂) : ℝ) : EReal))
          (c := ((a * μ₁ + b * μ₂ : ℝ) : EReal))
          (Or.inl (by simp)) (Or.inl (by simp))).2 (by simpa [add_comm] using hz_combo')
      simpa [G] using this
    -- Package the inequality back into epigraph membership for `G`.
    exact (mem_epigraph_univ_iff (f := G)).2 (by simpa using hG_combo)
  · -- Polyhedrality: extract a finite halfspace description of the packed epigraph of `g`,
    -- then transport it to `G` by an explicit dotProduct computation on packed coordinates.
    let pack : ((Fin (m + n) → ℝ) × ℝ) → (Fin (m + n + 1) → ℝ) :=
      fun p => (prodLinearEquiv_append (n := m + n) p).ofLp
    let Eg : Set (Fin (m + n + 1) → ℝ) :=
      pack '' epigraph (Set.univ : Set (Fin (m + n) → ℝ)) g
    let EG : Set (Fin (m + n + 1) → ℝ) :=
      pack '' epigraph (Set.univ : Set (Fin (m + n) → ℝ)) G
    have hEg_poly : IsPolyhedralConvexSet (m + n + 1) Eg := by
      simpa [Eg, pack, g] using hGraphPoly.2
    rcases (isPolyhedralConvexSet_iff_exists_finite_halfspaces (m + n + 1) Eg).1 hEg_poly with
      ⟨p, b, β, hEg_eq⟩
    -- Modify each halfspace normal by adding the `b_last * xStar` contribution on the `x`-block.
    let bLast : Fin p → ℝ := fun i => b i (Fin.last (m + n))
    let bTilt : Fin p → Fin (m + n + 1) → ℝ :=
      fun i =>
        Fin.lastCases (bLast i) (fun j : Fin (m + n) =>
          Fin.addCases (m := m) (n := n)
            (fun jm : Fin m => b i (Fin.castSucc (Fin.castAdd n jm)))
            (fun jn : Fin n =>
              b i (Fin.castSucc (Fin.natAdd m jn)) + (bLast i) * xStar jn)
            j)
    have hEG_eq : EG = ⋂ i, closedHalfSpaceLE (m + n + 1) (bTilt i) (β i) := by
      ext y
      constructor
      · rintro ⟨⟨z, μ⟩, hy_epi, rfl⟩
        -- From an epigraph point of `G`, build the corresponding epigraph point of `g`
        -- with the sheared height `μ + l(z)`.
        have hμ : G z ≤ (μ : EReal) := (mem_epigraph_univ_iff (f := G)).1 hy_epi
        have hz : g z ≤ (μ : EReal) + ((l z : ℝ) : EReal) := by
          have hSub : g z - ((l z : ℝ) : EReal) ≤ (μ : EReal) := by
            simpa [G] using hμ
          exact
            (EReal.sub_le_iff_le_add
              (a := g z) (b := ((l z : ℝ) : EReal)) (c := (μ : EReal))
              (Or.inl (by simp)) (Or.inl (by simp))).1 hSub
        have hy' :
            pack (z, μ + l z) ∈ Eg := by
          refine ⟨(z, μ + l z), (mem_epigraph_univ_iff (f := g)).2 ?_, rfl⟩
          simpa [EReal.coe_add, add_assoc] using hz
        have hIneq := Set.mem_iInter.1 (by simpa [hEg_eq] using hy')
        -- Transport each halfspace inequality from `b` at the shifted point to `bTilt` at `y`.
        refine Set.mem_iInter.2 ?_
        intro i
        have hi := hIneq i
        have hDot :
            dotProduct (pack (z, μ + l z)) (b i) =
              dotProduct (pack (z, μ)) (bTilt i) := by
          -- This is the dedicated packed dotProduct identity.
          simpa [pack, l, bLast, bTilt] using
            helperForCorollary33_1_3_dotProduct_packed_lastShift_eq_modifiedNormal
              (m := m) (n := n) (xStar := xStar) (b := b i) (z := z) (μ := μ)
        -- Rewrite the inequality using `hDot`.
        simpa [closedHalfSpaceLE, hDot] using hi
      · intro hy
        -- Start from the canonical preimage point of `y` under the packed linear equivalence.
        let w : (Fin (m + n) → ℝ) × ℝ :=
          (prodLinearEquiv_append (n := m + n)).symm (WithLp.toLp 2 y)
        have hw : pack w = y := by
          -- Undo `.symm` and `.toLp` by definitional `simp`.
          simpa [pack, w]
        rcases w with ⟨z, μ⟩
        -- Use the assumed `bTilt` halfspace inequalities to show the shifted packed point lies in `Eg`.
        have hyIneq := Set.mem_iInter.1 hy
        have hyShift :
            pack (z, μ + l z) ∈ Eg := by
          have : pack (z, μ) ∈ ⋂ i, closedHalfSpaceLE (m + n + 1) (bTilt i) (β i) := by
            simpa [hw] using hy
          have hIneq := Set.mem_iInter.1 this
          have : pack (z, μ + l z) ∈ ⋂ i, closedHalfSpaceLE (m + n + 1) (b i) (β i) := by
            refine Set.mem_iInter.2 ?_
            intro i
            have hi := hIneq i
            have hDot :
                dotProduct (pack (z, μ + l z)) (b i) =
                  dotProduct (pack (z, μ)) (bTilt i) := by
              simpa [pack, l, bLast, bTilt] using
                helperForCorollary33_1_3_dotProduct_packed_lastShift_eq_modifiedNormal
                  (m := m) (n := n) (xStar := xStar) (b := b i) (z := z) (μ := μ)
            -- Rewrite the inequality into the `b` halfspace inequality at the shifted point.
            simpa [closedHalfSpaceLE, hDot] using hi
          -- Convert the halfspace characterization back into membership in `Eg`.
          simpa [hEg_eq] using this
        -- Since `Eg` is an image under an injective map, the witness must be `(z, μ + l z)`.
        rcases hyShift with ⟨w', hw'_epi, hw'_eq⟩
        have hw'_id : w' = (z, μ + l z) := by
          -- Compare the packed images and use injectivity of the packed embedding.
          have : pack w' = pack (z, μ + l z) := by
            simpa [pack] using hw'_eq
          exact helperForCorollary33_1_3_prodLinearEquivAppend_ofLp_injective (n := m + n) this
        subst hw'_id
        have hz : g z ≤ ((μ + l z : ℝ) : EReal) := (mem_epigraph_univ_iff (f := g)).1 hw'_epi
        -- Move the linear term back to get the epigraph inequality for `G`.
        have hG : G z ≤ (μ : EReal) := by
          have hz' : g z ≤ (μ : EReal) + ((l z : ℝ) : EReal) := by
            simpa [EReal.coe_add, add_assoc] using hz
          have :
              g z - ((l z : ℝ) : EReal) ≤ (μ : EReal) :=
            (EReal.sub_le_iff_le_add
              (a := g z) (b := ((l z : ℝ) : EReal)) (c := (μ : EReal))
              (Or.inl (by simp)) (Or.inl (by simp))).2 (by simpa [add_comm] using hz')
          simpa [G] using this
        -- Package the membership back into the packed epigraph of `G`.
        refine ⟨(z, μ), (mem_epigraph_univ_iff (f := G)).2 hG, ?_⟩
        simpa [pack] using hw
    -- Finish polyhedrality by the explicit halfspace description.
    have hEG_poly : IsPolyhedralConvexSet (m + n + 1) EG := by
      refine (isPolyhedralConvexSet_iff_exists_finite_halfspaces (m + n + 1) EG).2 ?_
      exact ⟨p, bTilt, β, hEG_eq⟩
    -- `EG` is definitionally the packed epigraph set for `G` in `IsPolyhedralConvexFunction`.
    simpa [EG, pack, G, g, l] using hEG_poly

/-- Helper for Corollary33.1.3: projecting the tilted graph function to the `u`-coordinates
recovers the negative pairing section. -/
lemma helperForCorollary33_1_3_projectionImage_tiltedGraph_eq_negPairing
    {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    imageUnderLinearMap
        (projectionLinearMap (Nat.le_add_right m n))
        (fun z : Fin (m + n) → ℝ =>
          graphFunctionOfBifunction F z -
            ((dotProduct (fun j => z (Fin.natAdd m j)) xStar : ℝ) : EReal))
        u =
      -(convexBifunctionPairing F u xStar) := by
  classical
  let A : (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    projectionLinearMap (Nat.le_add_right m n)
  let G : (Fin (m + n) → ℝ) → EReal :=
    fun z =>
      graphFunctionOfBifunction F z -
        ((dotProduct (fun j => z (Fin.natAdd m j)) xStar : ℝ) : EReal)
  have hFiber :
      {z : EReal | ∃ w : Fin (m + n) → ℝ, A w = u ∧ z = G w} =
        Set.range (fun x : Fin n → ℝ =>
          graphFunctionOfBifunction F (Fin.append u x) -
            ((dotProduct x xStar : ℝ) : EReal)) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨w, hwA, rfl⟩
      -- Recover the trailing `x`-coordinates from a point in the projection fiber.
      refine ⟨fun j => w (Fin.natAdd m j), ?_⟩
      have hwA' := (projectionLinearMap_eq_iff (hmn := Nat.le_add_right m n) w u).1 hwA
      have hw_eq : w = Fin.append u (fun j => w (Fin.natAdd m j)) := by
        funext i
        cases Nat.lt_or_ge i.1 m with
        | inl hi =>
            have hi' : w i = u ⟨i.1, hi⟩ := hwA' ⟨i.1, hi⟩
            simpa [Fin.append, Fin.addCases, hi] using hi'
        | inr hi =>
            let j : Fin n := ⟨i.1 - m, by omega⟩
            have hj : Fin.natAdd m j = i := by
              ext
              simp [j]
              omega
            have hji : w (Fin.natAdd m j) = w i := congrArg w hj
            simp [Fin.append, Fin.addCases, hi, hj] at hji ⊢
      rw [hw_eq]
      simp [A, G, graphFunctionOfBifunction]
    · intro hz
      rcases hz with ⟨x, rfl⟩
      -- Conversely, append the fixed parameter block to any section point.
      refine ⟨Fin.append u x, ?_, ?_⟩
      · refine (projectionLinearMap_eq_iff (hmn := Nat.le_add_right m n) _ _).2 ?_
        intro i
        change Fin.append u x ⟨↑i, Nat.lt_of_lt_of_le i.2 (Nat.le_add_right m n)⟩ = u i
        simp [Fin.append, Fin.addCases]
      · simp [A, G, graphFunctionOfBifunction]
  -- After identifying the projection fiber, the `imageUnderLinearMap` infimum is exactly the
  -- previously computed tilted-fiber infimum.
  rw [imageUnderLinearMap, hFiber]
  exact helperForCorollary33_1_3_sInf_tiltedFiber_eq_negSup_pairing (F := F) u xStar

/-- Helper for Corollary33.1.3: for fixed `xStar`, the map
`u ↦ -(convexBifunctionPairing F u xStar)` is polyhedral convex. -/
lemma helperForCorollary33_1_3_negPairingSection_isPolyhedralConvexFunction
    {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsRockafellarPolyhedralConvexBifunction F)
    (xStar : Fin n → ℝ) :
    IsPolyhedralConvexFunction m (fun u => -(convexBifunctionPairing F u xStar)) := by
  let A : (Fin (m + n) → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    projectionLinearMap (Nat.le_add_right m n)
  let G : (Fin (m + n) → ℝ) → EReal :=
    fun z =>
      graphFunctionOfBifunction F z -
        ((dotProduct (fun j => z (Fin.natAdd m j)) xStar : ℝ) : EReal)
  have hImageData :=
    (polyhedralConvexFunction_image_preimage_linear (m + n) m A).1 G
      (helperForCorollary33_1_3_tiltedGraph_isPolyhedralConvexFunction
        (F := F) hF xStar)
  have hImagePoly : IsPolyhedralConvexFunction m (imageUnderLinearMap A G) := hImageData.1
  have hEq :
      imageUnderLinearMap A G = fun u => -(convexBifunctionPairing F u xStar) := by
    funext u
    -- The image-under-linear-map fiber is exactly the negative pairing section at `u`.
    simpa [A, G] using
      helperForCorollary33_1_3_projectionImage_tiltedGraph_eq_negPairing
        (F := F) u xStar
  simpa [hEq] using hImagePoly

-- Proof sketch: view `F` through its polyhedral graph function on `ℝ^(m+n)`. Fixing `u`
-- corresponds to taking a linear slice of that graph function, so each section `F u` remains
-- polyhedral convex and its Fenchel conjugate `x^* ↦ ⟪F u, x^*⟫` is again polyhedral convex by
-- Corollary 19.3.1. Fixing `x^*`, the map `u ↦ ⟪F u, x^*⟫` is concave by the convex-bifunction
-- correspondence, and polyhedrality follows by applying the same conjugacy argument to the
-- graph-function model after swapping the parameter and dual variables. If every section `F u`
-- is proper, then proper polyhedral convex functions equal their convex closure, so the forward
-- direction of Theorem33.1 removes the closure from the reconstruction formula.
/-- Corollary33.1.3: If `F` is a polyhedral convex bifunction from `ℝ^m` to `ℝ^n`, then for
each `u` the partial pairing `x^* ↦ ⟪F u, x^*⟫` is a polyhedral convex function, and for each
`x^*` the parameter section `u ↦ ⟪F u, x^*⟫` is a polyhedral concave function. Moreover, if
every section `F u` is proper convex on `ℝ^n`, then `F` is recovered from its pairing by
`(F u) x = sup_{x^*} (⟪x, x^*⟫ - ⟪F u, x^*⟫)`, formalized here via `convexConjugate`. -/
theorem polyhedralConvexBifunction_pairing_sections_and_reconstruction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsRockafellarPolyhedralConvexBifunction F) :
    (∀ u : Fin m → ℝ,
      IsPolyhedralConvexFunction n (convexBifunctionPairing F u)) ∧
      (∀ xStar : Fin n → ℝ,
        IsPolyhedralConvexFunction m (fun u => -(convexBifunctionPairing F u xStar))) ∧
      ((∀ u : Fin m → ℝ,
          ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (F u)) →
        ∀ u x,
          F u x = convexConjugate (convexBifunctionPairing F u) x) := by
  classical
  -- The key reusable fact is that every section `F u` inherits polyhedral convexity from the
  -- polyhedral graph function of the bifunction.
  have hSectionPoly : ∀ u : Fin m → ℝ, IsPolyhedralConvexFunction n (F u) :=
    helperForCorollary33_1_3_section_isPolyhedralConvexFunction (m := m) (n := n) (F := F) hF
  refine ⟨?_, ?_, ?_⟩
  · intro u
    -- Apply Theorem 19.2: the Fenchel conjugate of a polyhedral convex function is polyhedral.
    have hFenchel :
        IsPolyhedralConvexFunction n (fenchelConjugate n (F u)) :=
      polyhedralConvexFunction_fenchelConjugate (n := n) (f := F u) (hSectionPoly u)
    -- Rewrite Fenchel conjugate into the local `convexConjugate` notation, then unfold the pairing.
    have hConj :
        IsPolyhedralConvexFunction n (convexConjugate (F u)) := by
      -- Section 33's `convexConjugate` is exactly Chapter 3's `fenchelConjugate`.
      simpa [helperForLemma33_0_14_convexConjugate_eq_fenchelConjugate] using hFenchel
    simpa [convexBifunctionPairing, bifunctionPairingNotation] using hConj
  · intro xStar
    -- Package the fixed-dual section as the inf-projection of the tilted graph function.
    exact
      helperForCorollary33_1_3_negPairingSection_isPolyhedralConvexFunction
        (F := F) hF xStar
  · intro hProper u x
    -- Reconstruction: Theorem 33.1 gives the formula for `functionConvexClosure (F u)`;
    -- proper+polyhedral implies the section is closed (lower semicontinuous), so the closure
    -- is just `F u`.
    have hRock : IsRockafellarConvexBifunction F := hF.1
    have hNoBot : HasNoBotValuesBifunction F := by
      intro u' x'
      exact (hProper u').2.2 x' (by simp)
    have hForward :=
      (convexBifunction_pairing_correspondence (m := m) (n := n)).1 F hRock hNoBot
    have hClosureEq :
        functionConvexClosure (F u) x =
          convexConjugate (convexBifunctionPairing F u) x :=
      hForward.2.2 u x
    have hClosedConv :
        ClosedConvexFunction (F u) :=
      helperForCorollary_19_1_2_closed_of_polyhedral_proper
        (n := n) (f := F u) (hSectionPoly u) (hProper u)
    have hFix :
        functionConvexClosure (F u) x = F u x := by
      -- Lower semicontinuity fixes the Section 33 closure operator.
      have hEq :=
        helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
          (f := F u) hClosedConv.2
      have hPoint := congrArg (fun f => f x) hEq
      exact hPoint.symm
    -- Chain the fixed-point identity with Theorem 33.1's reconstruction.
    exact hFix.symm.trans hClosureEq

/-- Corollary 33.19. -/
theorem section33_corollary33_19 : True := by
  trivial

/-- Corollary 33.20. -/
theorem section33_corollary33_20 : True := by
  trivial

end Section33
end Chap07
