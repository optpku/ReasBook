/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section05_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap02.section09_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap06.section30_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section36_part2
import Books.ConvexAnalysis_Rockafellar_1970.bifunction_closure
import Books.ConvexAnalysis_Rockafellar_1970.fin_dot

section Chap07
section Section36

attribute [local instance] Classical.propDecidable

/-- The hypograph `{((u,x),t) | (t : EReal) ≤ F u x}` of a bifunction `F`, viewed as a subset of
`(ℝ^m × ℝ^n) × ℝ`. -/
def bifunctionHypograph {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    Set (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) :=
  {p | (p.2 : EReal) ≤ F p.1.1 p.1.2}

/-- The epigraph `{((u,x),t) | F u x ≤ (t : EReal)}` of a bifunction `F`, viewed as a subset of
`(ℝ^m × ℝ^n) × ℝ`. -/
def bifunctionEpigraph {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    Set (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) :=
  {p | F p.1.1 p.1.2 ≤ (p.2 : EReal)}

/-- A concave bifunction, modeled by convexity of its hypograph in `(ℝ^m × ℝ^n) × ℝ`. -/
def IsHypographConvexConcaveBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  Convex ℝ (bifunctionHypograph (m := m) (n := n) F)

/-- A convex bifunction, modeled by convexity of its epigraph in `(ℝ^m × ℝ^n) × ℝ`. -/
def IsEpigraphConvexBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  Convex ℝ (bifunctionEpigraph (m := m) (n := n) F)

/-- Closedness for a convex bifunction, modeled as topological closedness of its epigraph.
This is a section-local epigraph notion, distinct from the canonical closed convex bifunction
predicate used elsewhere in Chapter 7. -/
def IsEpigraphClosedConvexBifunction {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsClosed (bifunctionEpigraph (m := m) (n := n) F)

/-- Closedness for a concave bifunction, modeled as topological closedness of its hypograph. -/
def IsHypographClosedConcaveBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsClosed (bifunctionHypograph (m := m) (n := n) F)

/-- Properness for a convex bifunction: it never takes the value `-∞` and is not identically `+∞`. -/
def IsEpigraphProperConvexBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  (∃ u x, F u x < (⊤ : EReal)) ∧ ∀ u x, F u x ≠ (⊥ : EReal)

/-- Properness for a concave bifunction: it never takes the value `+∞` and is not identically `-∞`. -/
def IsHypographProperConcaveBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  (∃ u x, (⊥ : EReal) < F u x) ∧ ∀ u x, F u x ≠ (⊤ : EReal)

/-- Helper for Proposition 36.4.2: swap the two vector coordinates and negate the scalar
coordinate when transporting epi/hypographs across bifunction inversion. -/
def helperForProposition_36_4_2_swapNegate {m n : ℕ} :
    (((Fin n → ℝ) × (Fin m → ℝ)) × ℝ) → (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) :=
  fun p => ((p.1.2, p.1.1), -p.2)

/-- Helper for Proposition 36.4.2: the swap-negate transport map is linear, so convexity
pulls back along it. -/
lemma helperForProposition_36_4_2_swapNegate_isLinear {m n : ℕ} :
    IsLinearMap ℝ (helperForProposition_36_4_2_swapNegate (m := m) (n := n)) :=
  by
    constructor
    · intro x y
      -- The transport map acts componentwise on products, so it preserves addition.
      ext <;> simp [helperForProposition_36_4_2_swapNegate, add_comm]
    · intro c x
      -- Scalar multiplication also distributes componentwise through the swap and negation.
      ext <;> simp [helperForProposition_36_4_2_swapNegate]

/-- Helper for Proposition 36.4.2: the swap-negate transport map is continuous, so closedness
pulls back along it. -/
lemma helperForProposition_36_4_2_swapNegate_continuous {m n : ℕ} :
    Continuous (helperForProposition_36_4_2_swapNegate (m := m) (n := n)) :=
  by
    -- After unfolding the definition, `fun_prop` combines the product projections and negation.
    change Continuous
      (fun p : (((Fin n → ℝ) × (Fin m → ℝ)) × ℝ) => ((p.1.2, p.1.1), -p.2))
    fun_prop

/-- Helper for Proposition 36.4.2: the hypograph of the inverse bifunction is the preimage of the
original epigraph under the swap-negate transport. -/
lemma helperForProposition_36_4_2_inverseHypograph_preimageEpigraph
    {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    bifunctionHypograph (m := n) (n := m) (bifunctionInverse F) =
      helperForProposition_36_4_2_swapNegate (m := m) (n := n) ⁻¹'
        bifunctionEpigraph (m := m) (n := n) F :=
  by
    ext p
    -- Membership rewrites exactly by unfolding inversion and moving the inequality across `-`.
    simp [bifunctionHypograph, bifunctionEpigraph, bifunctionInverse,
      helperForProposition_36_4_2_swapNegate, EReal.le_neg]

/-- Helper for Proposition 36.4.2: the epigraph of the inverse bifunction is the preimage of the
original hypograph under the same swap-negate transport. -/
lemma helperForProposition_36_4_2_inverseEpigraph_preimageHypograph
    {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    bifunctionEpigraph (m := n) (n := m) (bifunctionInverse F) =
      helperForProposition_36_4_2_swapNegate (m := m) (n := n) ⁻¹'
        bifunctionHypograph (m := m) (n := n) F :=
  by
    ext p
    -- This is the symmetric epigraph-to-hypograph rewrite after unfolding inversion.
    simp [bifunctionHypograph, bifunctionEpigraph, bifunctionInverse,
      helperForProposition_36_4_2_swapNegate, EReal.neg_le]

/-- Helper for Proposition 36.4.2: proper convexity transfers to proper concavity after swapping
the arguments and negating the `EReal` value. -/
lemma helperForProposition_36_4_2_inverseProperConvex_to_Concave
    {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsEpigraphProperConvexBifunction (m := m) (n := n) F) :
    IsHypographProperConcaveBifunction (m := n) (n := m) (bifunctionInverse F) :=
  by
    rcases hF with ⟨⟨u, x, hFinite⟩, hNotBot⟩
    constructor
    · -- Reuse the same witness after swapping the vector variables and reflecting the value.
      refine ⟨x, u, ?_⟩
      simpa [bifunctionInverse] using (EReal.neg_lt_neg_iff.2 hFinite)
    · intro x u
      -- Endpoint exclusion rewrites through `EReal.neg_eq_top_iff`.
      simpa [bifunctionInverse, EReal.neg_eq_top_iff] using hNotBot u x

/-- Helper for Proposition 36.4.2: proper concavity transfers to proper convexity by the same
swap-and-negate argument. -/
lemma helperForProposition_36_4_2_inverseProperConcave_to_Convex
    {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (hF : IsHypographProperConcaveBifunction (m := m) (n := n) F) :
    IsEpigraphProperConvexBifunction (m := n) (n := m) (bifunctionInverse F) :=
  by
    rcases hF with ⟨⟨u, x, hFinite⟩, hNotTop⟩
    constructor
    · -- The original positive witness becomes a finite upper witness after negation.
      refine ⟨x, u, ?_⟩
      simpa [bifunctionInverse] using (EReal.neg_lt_neg_iff.2 hFinite)
    · intro x u
      -- Non-attainment of `⊤` becomes non-attainment of `⊥` after negation.
      simpa [bifunctionInverse, EReal.neg_eq_bot_iff] using hNotTop u x

-- Proof sketch: The inverse is obtained by swapping arguments and negating; convexity of epigraphs
-- and hypographs is stable under coordinate permutations and under the affine homeomorphism
-- `t ↦ -t` on the `ℝ`-coordinate. Properness and closedness likewise translate along these
-- homeomorphisms. Involutivity follows by unfolding `bifunctionInverse` twice.
/-- Proposition 36.4.2: Let `F` be a convex (resp. concave) bifunction from `ℝ^m` to `ℝ^n`, and
define its inverse bifunction `F_*` by `(F_* x)(u) = -(F u)(x)`. Then `F_*` is concave
(resp. convex). Moreover, within the convex/concave classes, the mapping `F ↦ F_*` preserves
closedness and properness, and it is involutive: `(F_*)_* = F`. -/
theorem bifunctionInverse_convex_concave_closed_proper_involutive
    {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (IsEpigraphConvexBifunction (m := m) (n := n) F →
        IsHypographConvexConcaveBifunction (m := n) (n := m) (bifunctionInverse F)) ∧
      (IsHypographConvexConcaveBifunction (m := m) (n := n) F →
        IsEpigraphConvexBifunction (m := n) (n := m) (bifunctionInverse F)) ∧
        (IsEpigraphClosedConvexBifunction (m := m) (n := n) F →
          IsHypographClosedConcaveBifunction (m := n) (n := m) (bifunctionInverse F)) ∧
          (IsHypographClosedConcaveBifunction (m := m) (n := n) F →
            IsEpigraphClosedConvexBifunction (m := n) (n := m)
              (bifunctionInverse F)) ∧
            (IsEpigraphProperConvexBifunction (m := m) (n := n) F →
              IsHypographProperConcaveBifunction (m := n) (n := m)
                (bifunctionInverse F)) ∧
              (IsHypographProperConcaveBifunction (m := m) (n := n) F →
                IsEpigraphProperConvexBifunction (m := n) (n := m)
                  (bifunctionInverse F)) ∧
                bifunctionInverse (bifunctionInverse F) =
                  F :=
  by
    constructor
    · intro hF
      have hConv : Convex ℝ (bifunctionEpigraph (m := m) (n := n) F) := by
        simpa [IsEpigraphConvexBifunction] using hF
      -- Pull convexity back along the swap-negate linear transport.
      change Convex ℝ (bifunctionHypograph (m := n) (n := m) (bifunctionInverse F))
      rw [helperForProposition_36_4_2_inverseHypograph_preimageEpigraph]
      exact hConv.is_linear_preimage
        helperForProposition_36_4_2_swapNegate_isLinear
    constructor
    · intro hF
      have hConv : Convex ℝ (bifunctionHypograph (m := m) (n := n) F) := by
        simpa [IsHypographConvexConcaveBifunction] using hF
      -- The same transport converts hypographs of `F` into epigraphs of `F_*`.
      change Convex ℝ (bifunctionEpigraph (m := n) (n := m) (bifunctionInverse F))
      rw [helperForProposition_36_4_2_inverseEpigraph_preimageHypograph]
      exact hConv.is_linear_preimage
        helperForProposition_36_4_2_swapNegate_isLinear
    constructor
    · intro hF
      have hClosed : IsClosed (bifunctionEpigraph (m := m) (n := n) F) := by
        simpa [IsEpigraphClosedConvexBifunction] using hF
      -- Closed epigraphs stay closed after taking a continuous preimage under the transport map.
      change IsClosed (bifunctionHypograph (m := n) (n := m) (bifunctionInverse F))
      rw [helperForProposition_36_4_2_inverseHypograph_preimageEpigraph]
      exact hClosed.preimage helperForProposition_36_4_2_swapNegate_continuous
    constructor
    · intro hF
      have hClosed : IsClosed (bifunctionHypograph (m := m) (n := n) F) := by
        simpa [IsHypographClosedConcaveBifunction] using hF
      -- The symmetric closedness statement uses the same continuous transport.
      change IsClosed (bifunctionEpigraph (m := n) (n := m) (bifunctionInverse F))
      rw [helperForProposition_36_4_2_inverseEpigraph_preimageHypograph]
      exact hClosed.preimage helperForProposition_36_4_2_swapNegate_continuous
    constructor
    · intro hF
      -- Properness bookkeeping is isolated in the dedicated helper lemma.
      exact helperForProposition_36_4_2_inverseProperConvex_to_Concave (F := F) hF
    constructor
    · intro hF
      -- The reverse properness direction is the same endpoint reflection in reverse.
      exact helperForProposition_36_4_2_inverseProperConcave_to_Convex (F := F) hF
    · -- Inverting twice swaps the variables twice and removes the double negation.
      ext u x
      simp [bifunctionInverse]

/-- The Euclidean adjoint bifunction `F^*` of `F`, modeled as a Fenchel-type conjugation with respect to
the Euclidean dot products on `ℝ^m` and `ℝ^n`, and with the argument order swapped. -/
noncomputable def bifunctionEuclideanAdjoint {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun x u =>
    iSup fun u' : Fin m → ℝ =>
      iSup fun x' : Fin n → ℝ =>
        ((finDot (n := n) x x' + finDot (n := m) u u' : ℝ) : EReal) + (-F u' x')

/-- Helper for Proposition 36.4.3: projection onto the scalar coordinate is linear, so half-space
convexity can be pulled back to bifunction epi/hypographs. -/
lemma helperForProposition_36_4_3_scalarProjection_isLinear {m n : ℕ} :
    IsLinearMap ℝ (fun p : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) => p.2) :=
  by
    constructor
    · intro x y
      -- The projection forgets the vector coordinates and preserves addition on the scalar slot.
      simp
    · intro c x
      -- Scalar multiplication also acts componentwise, so the scalar coordinate scales as expected.
      simp

/-- Helper for Proposition 36.4.3: the constant-zero bifunction has a convex epigraph. -/
lemma helperForProposition_36_4_3_constantZero_isEpigraphConvex {m n : ℕ} :
    IsEpigraphConvexBifunction (m := m) (n := n) (fun _ _ => (0 : EReal)) :=
  by
    have hHalfspace :
        Convex ℝ ((fun p : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) => p.2) ⁻¹' Set.Ici (0 : ℝ)) := by
      -- The epigraph of the zero bifunction is the pullback of the upper half-line `0 ≤ t`.
      exact (convex_Ici (0 : ℝ)).is_linear_preimage
        (helperForProposition_36_4_3_scalarProjection_isLinear (m := m) (n := n))
    -- Unfolding the epigraph identifies it with that scalar half-space.
    simpa [IsEpigraphConvexBifunction, bifunctionEpigraph] using hHalfspace

/-- Helper for Proposition 36.4.3: the constant-zero bifunction has a convex hypograph. -/
lemma helperForProposition_36_4_3_constantZero_isHypographConcave {m n : ℕ} :
    IsHypographConvexConcaveBifunction (m := m) (n := n) (fun _ _ => (0 : EReal)) :=
  by
    have hHalfspace :
        Convex ℝ ((fun p : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) => p.2) ⁻¹' Set.Iic (0 : ℝ)) := by
      -- The hypograph of the zero bifunction is the pullback of the lower half-line `t ≤ 0`.
      exact (convex_Iic (0 : ℝ)).is_linear_preimage
        (helperForProposition_36_4_3_scalarProjection_isLinear (m := m) (n := n))
    -- Unfolding the hypograph identifies it with the complementary scalar half-space.
    simpa [IsHypographConvexConcaveBifunction, bifunctionHypograph] using hHalfspace

/-- Helper for Proposition 36.4.3: the unique vector in `Fin 1 → ℝ` whose only coordinate is `1`. -/
def helperForProposition_36_4_3_oneVector : Fin 1 → ℝ :=
  fun _ => 1

/-- Helper for Proposition 36.4.3: the zero vector in `Fin 1 → ℝ`. -/
def helperForProposition_36_4_3_zeroVector : Fin 1 → ℝ :=
  fun _ => 0

/-- Helper for Proposition 36.4.3: evaluating the left composite at `(1, 0)` on the
dimension-one constant-zero bifunction gives a value at least `1`. -/
lemma helperForProposition_36_4_3_constantZero_leftComposite_ge_real
    (r : ℝ) :
    ((r : ℝ) : EReal) ≤
      bifunctionEuclideanAdjoint (m := 1) (n := 1)
        (bifunctionInverse (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector :=
  by
    let xWitness : Fin 1 → ℝ := fun _ => r
    -- Choosing `(u', x') = (0, r)` inside the adjoint suprema realizes the value `r`.
    refine le_trans ?_
      (le_iSup_of_le helperForProposition_36_4_3_zeroVector
        (le_iSup_of_le xWitness le_rfl))
    simp [xWitness, finDot, dotProduct, helperForProposition_36_4_3_oneVector,
      helperForProposition_36_4_3_zeroVector, bifunctionInverse]

/-- Helper for Proposition 36.4.3: the inner adjoint term on the right composite dominates every
real number at the swapped witness `(0, 1)`. -/
lemma helperForProposition_36_4_3_constantZero_innerAdjoint_ge_real
    (r : ℝ) :
    ((r : ℝ) : EReal) ≤
      bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))
        helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector :=
  by
    let uWitness : Fin 1 → ℝ := fun _ => r
    -- Choosing `(u', x') = (r, 0)` shows that the swapped adjoint also dominates any real value.
    refine le_trans ?_
      (le_iSup_of_le uWitness
        (le_iSup_of_le helperForProposition_36_4_3_zeroVector le_rfl))
    simp [uWitness, finDot, dotProduct, helperForProposition_36_4_3_oneVector,
      helperForProposition_36_4_3_zeroVector]

/-- Helper for Proposition 36.4.3: after applying the inverse, the right composite at `(1, 0)` is
bounded above by `-r` for every real number `r`. -/
lemma helperForProposition_36_4_3_constantZero_rightComposite_le_neg_real
    (r : ℝ) :
    bifunctionInverse
        (bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector ≤
      ((-r : ℝ) : EReal) :=
  by
    -- Unfold the inverse so the lower bound on the inner adjoint becomes an upper bound after
    -- negation.
    change -(bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))
      helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector) ≤
      ((-r : ℝ) : EReal)
    simpa using
      (EReal.neg_le_neg_iff.2
        (helperForProposition_36_4_3_constantZero_innerAdjoint_ge_real (r := r)))

/-- Helper for Proposition 36.4.3: evaluating the left composite at `(1, 0)` on the
dimension-one constant-zero bifunction gives a value at least `1`. -/
lemma helperForProposition_36_4_3_constantZero_leftComposite_ge_one :
    (1 : EReal) ≤
      bifunctionEuclideanAdjoint (m := 1) (n := 1)
        (bifunctionInverse (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector :=
  by
    -- This is the `r = 1` instance of the unbounded lower-bound helper.
    simpa using helperForProposition_36_4_3_constantZero_leftComposite_ge_real (r := 1)

/-- Helper for Proposition 36.4.3: the inner adjoint term on the right composite is also at
least `1` at the swapped point `(0, 1)`. -/
lemma helperForProposition_36_4_3_constantZero_innerAdjoint_ge_one :
    (1 : EReal) ≤
      bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))
        helperForProposition_36_4_3_zeroVector helperForProposition_36_4_3_oneVector :=
  by
    -- This is the `r = 1` instance of the generic lower bound on the swapped adjoint.
    simpa using helperForProposition_36_4_3_constantZero_innerAdjoint_ge_real (r := 1)

/-- Helper for Proposition 36.4.3: after applying the inverse, the right composite at `(1, 0)`
is bounded above by `-1`. -/
lemma helperForProposition_36_4_3_constantZero_rightComposite_le_negOne :
    bifunctionInverse
        (bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector ≤
      (-1 : EReal) :=
  by
    -- This is the `r = 1` instance of the generic upper bound after applying the inverse.
    simpa using helperForProposition_36_4_3_constantZero_rightComposite_le_neg_real (r := 1)

/-- Helper for Proposition 36.4.3: the embedded real numbers still satisfy `1 ≰ -1` inside
`EReal`. -/
lemma helperForProposition_36_4_3_one_not_le_negOne :
    ¬ ((1 : EReal) ≤ (-1 : EReal)) :=
  by
    -- The order contradiction is already visible on the real line and transfers to `EReal`.
    have hlt : (((-1 : ℝ) : EReal) < ((1 : ℝ) : EReal)) := by
      have hReal : (-1 : ℝ) < 1 := by
        norm_num
      exact_mod_cast hReal
    exact not_le_of_gt hlt

/-- Helper for Proposition 36.4.3: at the witness `(1, 0)`, the left composite cannot lie below
the right composite for the dimension-one constant-zero bifunction. -/
lemma helperForProposition_36_4_3_constantZero_leftComposite_not_le_rightComposite :
    ¬ (bifunctionEuclideanAdjoint (m := 1) (n := 1)
          (bifunctionInverse (fun _ _ => (0 : EReal)))
          helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector ≤
        bifunctionInverse
          (bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
          helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector) :=
  by
    intro hLe
    -- The explicit lower and upper bounds would then force the impossible comparison `1 ≤ -1`.
    have hImpossible : (1 : EReal) ≤ (-1 : EReal) := by
      exact le_trans helperForProposition_36_4_3_constantZero_leftComposite_ge_one
        (le_trans hLe helperForProposition_36_4_3_constantZero_rightComposite_le_negOne)
    exact helperForProposition_36_4_3_one_not_le_negOne hImpossible

/-- Helper for Proposition 36.4.3: the two composite bifunctions already differ pointwise at the
explicit witness `(1, 0)` for the dimension-one constant-zero bifunction. -/
lemma helperForProposition_36_4_3_constantZero_pointwiseValues_ne :
    bifunctionEuclideanAdjoint (m := 1) (n := 1) (bifunctionInverse (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector ≠
      bifunctionInverse (bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal)))
        helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector :=
  by
    intro hEq
    -- Equality of the witness values would imply the forbidden order relation from the previous
    -- helper lemma.
    exact helperForProposition_36_4_3_constantZero_leftComposite_not_le_rightComposite hEq.le

/-- Helper for Proposition 36.4.3: with the current adjoint definition, the constant-zero
bifunction in dimension `1` does not satisfy the claimed commutation law. -/
lemma helperForProposition_36_4_3_constantZero_commutation_fails :
    bifunctionEuclideanAdjoint (m := 1) (n := 1) (bifunctionInverse (fun _ _ => (0 : EReal))) ≠
      bifunctionInverse (bifunctionEuclideanAdjoint (m := 1) (n := 1) (fun _ _ => (0 : EReal))) :=
  by
    intro hEq
    -- Applying functional extensionality to the explicit witness reduces the failure to the
    -- already proved pointwise inequality.
    have hEval := congrArg
      (fun G =>
        G helperForProposition_36_4_3_oneVector helperForProposition_36_4_3_zeroVector) hEq
    exact helperForProposition_36_4_3_constantZero_pointwiseValues_ne hEval

/-- Helper for Proposition 36.4.3: the specialized statement already fails on the constant-zero
bifunction, so the current target cannot be proved without changing the local setup. -/
lemma helperForProposition_36_4_3_constantZero_convexBranch_fails :
    ¬ (IsEpigraphConvexBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)) →
          bifunctionEuclideanAdjoint (m := 1) (n := 1)
              (bifunctionInverse (fun _ _ => (0 : EReal))) =
            bifunctionInverse (bifunctionEuclideanAdjoint (m := 1) (n := 1)
              (fun _ _ => (0 : EReal)))) :=
  by
    intro hBranch
    -- The zero bifunction satisfies the convex-side hypothesis, so this branch would force the
    -- already disproved equality.
    have hEq :=
      hBranch (helperForProposition_36_4_3_constantZero_isEpigraphConvex (m := 1) (n := 1))
    exact helperForProposition_36_4_3_constantZero_commutation_fails hEq

/-- Helper for Proposition 36.4.3: the concave branch of the displayed implication also fails on
the constant-zero bifunction in dimension `1`. -/
lemma helperForProposition_36_4_3_constantZero_concaveBranch_fails :
    ¬ (IsHypographConvexConcaveBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)) →
          bifunctionEuclideanAdjoint (m := 1) (n := 1)
              (bifunctionInverse (fun _ _ => (0 : EReal))) =
            bifunctionInverse (bifunctionEuclideanAdjoint (m := 1) (n := 1)
              (fun _ _ => (0 : EReal)))) :=
  by
    intro hBranch
    -- The same zero bifunction also satisfies the concave-side hypothesis, so the second branch
    -- collapses to the identical false equality.
    have hEq :=
      hBranch (helperForProposition_36_4_3_constantZero_isHypographConcave (m := 1) (n := 1))
    exact helperForProposition_36_4_3_constantZero_commutation_fails hEq

/-- Helper for Proposition 36.4.3: the specialized statement already fails on the constant-zero
bifunction, so the current target cannot be proved without changing the local setup. -/
lemma helperForProposition_36_4_3_constantZero_target_fails :
    ¬ ((IsEpigraphConvexBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)) →
          bifunctionEuclideanAdjoint (m := 1) (n := 1)
              (bifunctionInverse (fun _ _ => (0 : EReal))) =
            bifunctionInverse (bifunctionEuclideanAdjoint (m := 1) (n := 1)
              (fun _ _ => (0 : EReal)))) ∧
       (IsHypographConvexConcaveBifunction (m := 1) (n := 1) (fun _ _ => (0 : EReal)) →
          bifunctionEuclideanAdjoint (m := 1) (n := 1)
              (bifunctionInverse (fun _ _ => (0 : EReal))) =
            bifunctionInverse (bifunctionEuclideanAdjoint (m := 1) (n := 1)
              (fun _ _ => (0 : EReal))))) :=
  by
    intro hTarget
    -- The conjunction cannot hold because even its convex-side branch is already false on the
    -- dimension-one zero bifunction.
    exact helperForProposition_36_4_3_constantZero_convexBranch_fails hTarget.1

/-- Helper for Proposition 36.4.3: any universal proof of the displayed commutation law would
specialize to the already disproved constant-zero instance in dimension `1`. -/
lemma helperForProposition_36_4_3_universalTarget_fails :
    ¬ (∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
          (IsEpigraphConvexBifunction (m := m) (n := n) F →
              bifunctionEuclideanAdjoint (m := n) (n := m) (bifunctionInverse F) =
                bifunctionInverse (bifunctionEuclideanAdjoint (m := m) (n := n) F)) ∧
            (IsHypographConvexConcaveBifunction (m := m) (n := n) F →
              bifunctionEuclideanAdjoint (m := n) (n := m) (bifunctionInverse F) =
                bifunctionInverse (bifunctionEuclideanAdjoint (m := m) (n := n) F))) :=
  by
    intro hUniversal
    -- Specializing the universal statement to `m = n = 1` and `F = 0` recovers the established
    -- contradiction from the previous helper.
    exact helperForProposition_36_4_3_constantZero_target_fails
      (hUniversal (m := 1) (n := 1) (fun _ _ => (0 : EReal)))

/-- Helper for Proposition 36.4.3: the exact universal theorem signature is empty under the
current section-local adjoint convention. -/
lemma helperForProposition_36_4_3_exactTheoremSignature_isEmpty :
    IsEmpty
      (∀ {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal),
          (IsEpigraphConvexBifunction (m := m) (n := n) F →
              bifunctionEuclideanAdjoint (m := n) (n := m) (bifunctionInverse F) =
                bifunctionInverse (bifunctionEuclideanAdjoint (m := m) (n := n) F)) ∧
            (IsHypographConvexConcaveBifunction (m := m) (n := n) F →
              bifunctionEuclideanAdjoint (m := n) (n := m) (bifunctionInverse F) =
                bifunctionInverse (bifunctionEuclideanAdjoint (m := m) (n := n) F))) :=
  by
    refine ⟨?_⟩
    intro hUniversal
    -- Packaging the universal theorem type as `IsEmpty` records that every inhabitant would
    -- specialize to the same dimension-one constant-zero contradiction.
    exact helperForProposition_36_4_3_universalTarget_fails hUniversal

/-- Proposition 36.4.3: for a convex (respectively concave) bifunction, inversion commutes with
the branch-appropriate Chapter 6 adjoint. The canonical proof that the inverse has the opposite
orientation is supplied explicitly in each branch, so the convex branch uses the concave adjoint
of `F_*`, while the concave branch uses the convex adjoint of `F_*`. -/
theorem bifunctionInverse_adjoint_commutes
    {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (∀ (hFconv : ConvexBifunction F)
        (hInvConc : ConcaveBifunction (bifunctionInverse F)),
        adjointOfConcaveBifunction ⟨bifunctionInverse F, hInvConc⟩ =
          bifunctionInverse (adjointOfConvexBifunction ⟨F, hFconv⟩)) ∧
      (∀ (hFconc : ConcaveBifunction F)
        (hInvConv : ConvexBifunction (bifunctionInverse F)),
        adjointOfConvexBifunction ⟨bifunctionInverse F, hInvConv⟩ =
          bifunctionInverse (adjointOfConcaveBifunction ⟨F, hFconc⟩)) := by
  have hConcaveBranch :
      ∀ {a b : ℕ} (K : (Fin a → ℝ) → (Fin b → ℝ) → EReal)
        (hK : ConcaveBifunction K) (hInv : ConvexBifunction (bifunctionInverse K)),
          adjointOfConvexBifunction ⟨bifunctionInverse K, hInv⟩ =
            bifunctionInverse (adjointOfConcaveBifunction ⟨K, hK⟩) := by
    intro a b K hK hInv
    funext xStar uStar
    let φ : (Fin b → ℝ) × (Fin a → ℝ) → EReal := fun p =>
      K p.2 p.1 - (((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal))
    have hRange :
        Set.range φ =
          Set.range (fun q : (Fin a → ℝ) × (Fin b → ℝ) =>
            K q.1 q.2 - (((q.2 ⬝ᵥ uStar : ℝ) : EReal)) +
              (((q.1 ⬝ᵥ xStar : ℝ) : EReal))) := by
      ext z
      constructor
      · rintro ⟨p, rfl⟩
        exact ⟨(p.2, p.1), rfl⟩
      · rintro ⟨q, rfl⟩
        exact ⟨(q.2, q.1), rfl⟩
    calc
      adjointOfConvexBifunction ⟨bifunctionInverse K, hInv⟩ xStar uStar =
          iInf (fun p : (Fin b → ℝ) × (Fin a → ℝ) => -φ p) := by
        rw [adjointOfConvexBifunction, sInf_range]
        refine iInf_congr ?_
        intro p
        have hAffineTop :
            (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal))) ≠
              (⊤ : EReal) := by
          simpa using (EReal.coe_ne_top (-(p.1 ⬝ᵥ uStar) + (p.2 ⬝ᵥ xStar)))
        have hAffineCoe :
            (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) : EReal) =
              (((-(p.1 ⬝ᵥ uStar) + (p.2 ⬝ᵥ xStar) : ℝ) : EReal)) := by
          simp
        have hAffineBot :
            (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal))) ≠
              (⊥ : EReal) := by
          rw [hAffineCoe]
          exact EReal.coe_ne_bot (-(p.1 ⬝ᵥ uStar) + (p.2 ⬝ᵥ xStar))
        have hLeftNeBot : -(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) ≠ (⊥ : EReal) := by
          simp
        have hRightNeBot : (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) ≠ (⊥ : EReal) := by
          simp
        have hAffineNeg :
            -(-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal))) =
              (((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (-(((p.2 ⬝ᵥ xStar : ℝ) : EReal))) := by
          simpa only [neg_neg] using
            (EReal.neg_add (x := -(((p.1 ⬝ᵥ uStar : ℝ) : EReal)))
              (y := (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))
              (h1 := Or.inl hLeftNeBot) (h2 := Or.inr hRightNeBot))
        have hNegAdd :
            -(K p.2 p.1 +
                (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))) =
              (-(-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))) +
                (-K p.2 p.1) := by
          simpa [add_comm] using
            (EReal.neg_add (x := K p.2 p.1)
              (y := -(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))
              (h1 := Or.inr hAffineTop) (h2 := Or.inr hAffineBot))
        calc
          bifunctionInverse K p.1 p.2 - (((p.2 ⬝ᵥ xStar : ℝ) : EReal)) +
                (((p.1 ⬝ᵥ uStar : ℝ) : EReal)) =
              (-K p.2 p.1) +
                (-(((p.2 ⬝ᵥ xStar : ℝ) : EReal)) + (((p.1 ⬝ᵥ uStar : ℝ) : EReal))) := by
            simp [bifunctionInverse, sub_eq_add_neg, add_assoc]
          _ = (-(-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) + (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))) +
                (-K p.2 p.1) := by
            simpa [add_assoc, add_left_comm, add_comm] using
              (congrArg (fun t : EReal => t + (-K p.2 p.1)) hAffineNeg).symm
          _ = -(K p.2 p.1 + (-(((p.1 ⬝ᵥ uStar : ℝ) : EReal)) +
                (((p.2 ⬝ᵥ xStar : ℝ) : EReal)))) := by
            simpa [add_comm] using hNegAdd.symm
          _ = -φ p := by
            simp [φ, sub_eq_add_neg, add_assoc]
      _ = -(iSup φ) := by
        simpa using
          congrArg Neg.neg
            (helperForTheorem_6_30_4_neg_iInf_eq_iSup_neg (φ := fun p => -φ p))
      _ = -(sSup (Set.range φ)) := by
        rw [sSup_range]
      _ = -(sSup
          (Set.range (fun q : (Fin a → ℝ) × (Fin b → ℝ) =>
            K q.1 q.2 - (((q.2 ⬝ᵥ uStar : ℝ) : EReal)) +
              (((q.1 ⬝ᵥ xStar : ℝ) : EReal))))) := by
        rw [hRange]
      _ = bifunctionInverse (adjointOfConcaveBifunction ⟨K, hK⟩) xStar uStar := by
        simp [bifunctionInverse, adjointOfConcaveBifunction]
  constructor
  · intro hFconv hInvConc
    have hDoubleInverse : bifunctionInverse (bifunctionInverse F) = F := by
      funext u x
      simp [bifunctionInverse]
    have hDoubleInverseConvex :
        ConvexBifunction (bifunctionInverse (bifunctionInverse F)) := by
      simpa [hDoubleInverse] using hFconv
    have hApplied := hConcaveBranch (bifunctionInverse F) hInvConc hDoubleInverseConvex
    have hAppliedClean :
        adjointOfConvexBifunction ⟨F, hFconv⟩ =
          bifunctionInverse
            (adjointOfConcaveBifunction ⟨bifunctionInverse F, hInvConc⟩) := by
      simpa [hDoubleInverse] using hApplied
    have hInverted := congrArg bifunctionInverse hAppliedClean
    have hDoubleAdjointInverse :
        bifunctionInverse
            (bifunctionInverse
              (adjointOfConcaveBifunction ⟨bifunctionInverse F, hInvConc⟩)) =
          adjointOfConcaveBifunction ⟨bifunctionInverse F, hInvConc⟩ := by
      funext x u
      simp [bifunctionInverse]
    rw [hDoubleAdjointInverse] at hInverted
    exact hInverted.symm
  · intro hFconc hInvConv
    exact hConcaveBranch F hFconc hInvConv

end Section36
end Chap07
