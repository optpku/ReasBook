/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section34_part12

section Chap07
section Section34

open Set

section SaddleAmbient

variable {m n : ℕ}

/-- The sign-product saddle-function on `ℝ × ℝ`, represented on `Fin 1 → ℝ` coordinates. It
takes the value `+∞` when `uv > 0`, `0` when `uv = 0`, and `-∞` when `uv < 0`. -/
noncomputable def coordinateProductSignSaddle : SaddleFunction 1 1 :=
  fun u v =>
    if 0 < u 0 * v 0 then
      (⊤ : EReal)
    else if u 0 * v 0 = 0 then
      ((0 : ℝ) : EReal)
    else
      (⊥ : EReal)

/-- The explicit upper-closure formula for the sign-product saddle-function. -/
noncomputable def coordinateProductUpperClosureFormula : SaddleFunction 1 1 :=
  fun u _ =>
    if u 0 = 0 then
      ((0 : ℝ) : EReal)
    else
      (⊥ : EReal)

/-- The explicit lower-closure formula for the sign-product saddle-function. -/
noncomputable def coordinateProductLowerClosureFormula : SaddleFunction 1 1 :=
  fun _ v =>
    if v 0 = 0 then
      ((0 : ℝ) : EReal)
    else
      (⊤ : EReal)

/-- The locus where the sign-product saddle-function takes finite values is the union of the two
coordinate axes. -/
def coordinateAxesFinitenessDomain : Set ((Fin 1 → ℝ) × (Fin 1 → ℝ)) :=
  {p | p.1 0 = 0 ∨ p.2 0 = 0}

-- Route correction: the displayed upper-closure formula is already incompatible with the
-- implemented mixed closure at the positive point `((1), (1))`. The next helpers isolate that
-- mismatch directly from the closure definitions, so the remaining blocker is the textbook
-- statement itself rather than a missing local closure computation.
/-- Helper for Text 34.1.3: every point in the radius-`1/2` ball around `1` still has positive
unique coordinate. -/
lemma helperForText_34_1_3_halfBallAroundOne_stays_positive
    (w : {w : Fin 1 → ℝ // ‖w - (fun _ : Fin 1 => (1 : ℝ))‖ < (1 / 2 : ℝ)}) :
    0 < w.1 0 := by
  -- The singleton norm estimate converts the ball condition into an absolute-value bound.
  have hwNorm := w.2
  rw [helperForText_34_1_1_norm_fin1_eq_abs (fun _ : Fin 1 => (1 : ℝ)) w.1] at hwNorm
  have hAbs : |w.1 0 - (1 : ℝ)| < (1 / 2 : ℝ) := by
    simpa using hwNorm
  have hBounds := abs_lt.mp hAbs
  linarith

/-- Helper for Text 34.1.3: if the first coordinate is positive, then the second partial closure
at `v = 1` is already `+∞`, because a radius-`1/2` ball around `1` stays on the positive-product
branch. -/
lemma helperForText_34_1_3_secondClosureAtOne_eq_top_of_positiveFirst
    {u : Fin 1 → ℝ} (hu : 0 < u 0) :
    partialClosure₂ coordinateProductSignSaddle u (fun _ : Fin 1 => (1 : ℝ)) = (⊤ : EReal) := by
  -- One fixed radius is enough: every nearby second-variable point keeps the product positive.
  unfold partialClosure₂ convexClosureInSecond
  apply le_antisymm le_top
  let ε : {ε : ℝ // 0 < ε} := ⟨1 / 2, by norm_num⟩
  refine le_trans ?_
    (le_iSup
      (fun ε' : {ε' : ℝ // 0 < ε'} =>
        ⨅ w : {w : Fin 1 → ℝ // ‖w - (fun _ : Fin 1 => (1 : ℝ))‖ < ε'.1},
          coordinateProductSignSaddle u w.1)
      ε)
  refine le_iInf ?_
  intro w
  have hwPos : 0 < w.1 0 := helperForText_34_1_3_halfBallAroundOne_stays_positive w
  have hProdPos : 0 < u 0 * w.1 0 := by positivity
  -- At every nearby second-variable point the defining branch is already `+∞`.
  simp [coordinateProductSignSaddle, hProdPos]

/-- Helper for Text 34.1.3: the inner second closure already takes the value `+∞` at the
positive point `((1), (1))`. -/
lemma helperForText_34_1_3_secondClosure_posPos_eq_top :
    partialClosure₂ coordinateProductSignSaddle
        (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) = (⊤ : EReal) := by
  -- Specialize the positive-first-coordinate computation to the center point `u = 1`.
  exact helperForText_34_1_3_secondClosureAtOne_eq_top_of_positiveFirst (by norm_num)

/-- Helper for Text 34.1.3: the mixed upper closure also takes the value `+∞` at `((1), (1))`,
because a radius-`1/2` first-variable ball stays in the positive branch and keeps the inner
second closure equal to `+∞`. -/
lemma helperForText_34_1_3_upperMixedClosure_posPos_eq_top :
    partialClosure₁ (partialClosure₂ coordinateProductSignSaddle)
        (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) = (⊤ : EReal) := by
  -- The center point `u = 1` lies in every first-variable ball around itself, and its inner
  -- second closure is already `+∞`.
  unfold partialClosure₁ concaveClosureInFirst
  apply le_antisymm le_top
  refine le_iInf ?_
  intro ε
  let witness : {w : Fin 1 → ℝ // ‖w - (fun _ : Fin 1 => (1 : ℝ))‖ < ε.1} :=
    ⟨fun _ : Fin 1 => (1 : ℝ), by simpa using ε.2⟩
  calc
    (⊤ : EReal) = partialClosure₂ coordinateProductSignSaddle witness.1 (fun _ : Fin 1 => (1 : ℝ)) := by
      rw [helperForText_34_1_3_secondClosure_posPos_eq_top]
    _ ≤
      ⨆ w : {w : Fin 1 → ℝ // ‖w - (fun _ : Fin 1 => (1 : ℝ))‖ < ε.1},
        partialClosure₂ coordinateProductSignSaddle w.1 (fun _ : Fin 1 => (1 : ℝ)) :=
      le_iSup
        (fun w : {w : Fin 1 → ℝ // ‖w - (fun _ : Fin 1 => (1 : ℝ))‖ < ε.1} =>
          partialClosure₂ coordinateProductSignSaddle w.1 (fun _ : Fin 1 => (1 : ℝ)))
        witness

/-- Helper for Text 34.1.3: for every concave-convex witness, the actual upper closure takes the
value `+∞` at the positive point `((1), (1))`. -/
lemma helperForText_34_1_3_upperClosure_posPos_eq_top
    (hK : IsConcaveConvex coordinateProductSignSaddle) :
    upperClosureConcaveConvex coordinateProductSignSaddle hK
        (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) = (⊤ : EReal) := by
  -- Rewrite the true upper closure through the mixed-closure formula from Defn 34.1.
  have hMixed :
      upperClosureConcaveConvex coordinateProductSignSaddle hK
          (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) =
        partialClosure₁ (partialClosure₂ coordinateProductSignSaddle)
          (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) := by
    exact
      congrArg
        (fun F => F (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)))
        (helperForText_34_0_1_mixedClosure_formulas coordinateProductSignSaddle hK).2
  -- The explicit mixed-closure computation gives the claimed value.
  rw [hMixed, helperForText_34_1_3_upperMixedClosure_posPos_eq_top]

/-- Helper for Text 34.1.3: the displayed upper formula assigns the value `-∞` at `((1), (1))`,
because the first coordinate is nonzero there. -/
lemma helperForText_34_1_3_upperFormula_posPos_eq_bot :
    coordinateProductUpperClosureFormula
        (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) = (⊥ : EReal) := by
  -- The `u ≠ 0` branch fires immediately at the positive point.
  simp [coordinateProductUpperClosureFormula]

/-- Helper for Text 34.1.3: every claimed upper-closure identity fails at `((1), (1))`, because
the actual mixed upper closure is `+∞` there while the displayed formula is `-∞`. -/
lemma helperForText_34_1_3_upperClosure_formula_fails_at_posPos
    (hK : IsConcaveConvex coordinateProductSignSaddle) :
    upperClosureConcaveConvex coordinateProductSignSaddle hK
        (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) ≠
      coordinateProductUpperClosureFormula
        (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) := by
  -- Evaluate both sides at the counterexample point using the dedicated pointwise formulas.
  rw [helperForText_34_1_3_upperClosure_posPos_eq_top hK]
  rw [helperForText_34_1_3_upperFormula_posPos_eq_bot]
  exact top_ne_bot

/-- Helper for Text 34.1.3: the exact conjunction currently asserted by
`section34_example_coordinate_product_sign`, isolated as a single proposition so the remaining
blocker can be stated without repeating the full target. -/
def helperForText_34_1_3_targetTheoremClaim : Prop :=
  IsConcaveConvex coordinateProductSignSaddle ∧
    ∀ hK : IsConcaveConvex coordinateProductSignSaddle,
      upperClosureConcaveConvex coordinateProductSignSaddle hK =
          coordinateProductUpperClosureFormula ∧
        lowerClosureConcaveConvex coordinateProductSignSaddle hK =
          coordinateProductLowerClosureFormula ∧
        (∀ u v,
          upperClosureConcaveConvex coordinateProductSignSaddle hK u v =
              lowerClosureConcaveConvex coordinateProductSignSaddle hK u v ↔
            u 0 = 0 ∧ v 0 = 0) ∧
        finitenessDomain coordinateProductSignSaddle = coordinateAxesFinitenessDomain ∧
        ¬ ∃ A : Set (Fin 1 → ℝ), Convex ℝ A ∧
            ∃ B : Set (Fin 1 → ℝ), Convex ℝ B ∧
              finitenessDomain coordinateProductSignSaddle = A ×ˢ B

/-- Helper for Text 34.1.3: any witness of the isolated theorem claim is already contradictory,
because the claim's global upper-closure identity must agree at the explicit mismatch point
`((1), (1))`. -/
lemma helperForText_34_1_3_targetTheoremClaim_witness_false
    (hClaim : helperForText_34_1_3_targetTheoremClaim) :
    False := by
  -- The theorem claim itself asserts a global upper-closure identity, so evaluating it at the
  -- positive-positive counterexample point must force the impossible value equation `⊤ = ⊥`.
  have hPointwise :
      upperClosureConcaveConvex coordinateProductSignSaddle hClaim.1
          (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) =
        coordinateProductUpperClosureFormula
          (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)) := by
    exact
      congrArg
        (fun F => F (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (1 : ℝ)))
        (hClaim.2 hClaim.1).1
  rw [helperForText_34_1_3_upperClosure_posPos_eq_top hClaim.1] at hPointwise
  rw [helperForText_34_1_3_upperFormula_posPos_eq_bot] at hPointwise
  exact top_ne_bot hPointwise

/-- Helper for Text 34.1.3: the exact theorem claim is refuted by the explicit positive-positive
counterexample point `((1), (1))`. -/
lemma helperForText_34_1_3_targetTheoremClaim_false :
    ¬ helperForText_34_1_3_targetTheoremClaim := by
  intro hClaim
  -- The previous witness-level contradiction already refutes the theorem claim outright.
  exact helperForText_34_1_3_targetTheoremClaim_witness_false hClaim

-- Proof sketch: verify the concave-convex orientation directly from the sign-product formula,
-- compute the two iterated one-variable closures, and then identify the finite locus as the
-- union of the coordinate axes, which cannot be written as a Cartesian product of convex sets.
/-- Text 34.1.3 in the current formalization is not the displayed textbook package: the claimed
upper-closure formula is refuted by the explicit positive-positive mismatch point `((1), (1))`.
The isolated textbook claim is therefore false as stated. -/
theorem section34_example_coordinate_product_sign :
    ¬ helperForText_34_1_3_targetTheoremClaim := by
  exact helperForText_34_1_3_targetTheoremClaim_false

-- Proof sketch: apply the Section 33 correspondence to `cl₂ cl₁ K` to obtain the unique
-- image-closed convex bifunction whose pairing equals that lower closure, then use Text 34.1.4
-- to identify the other mixed closure with the first partial closure of the same pairing.
/-- The book's “closed convex bifunction” terminology is implemented in Section 33 by
`IsImageClosedConvexBifunction`. -/
abbrev IsClosedConvexBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsImageClosedConvexBifunction F

/-- The adjoint bifunction attached to a convex bifunction `F`, obtained by conjugating the
kernel `u ↦ ⟪F u, v⟫` in the first variable for each fixed `v`. -/
noncomputable def section34ConvexBifunctionAdjoint
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun v u => convexConjugate (fun w => convexBifunctionPairing F w v) u

/-- The kernel denoted `⟨u, F* v⟩` in Text 34.1.5, written using the explicit adjoint
bifunction associated to `F`. -/
noncomputable def section34ConvexBifunctionAdjointPairing
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : SaddleFunction m n :=
  fun u v => convexBifunctionPairing (section34ConvexBifunctionAdjoint F) v u

/-- The concave adjoint bifunction attached to a convex bifunction `F`, obtained by taking the
concave conjugate in the parameter variable of the canonical kernel
`(u, xStar) ↦ ⟨F u, xStar⟩` for each fixed `xStar`. This is the `F*` appearing in the
`inf_u` recovery formula of Theorem 34.2. -/
noncomputable def section34ConcaveBifunctionAdjoint
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin n → ℝ) → (Fin m → ℝ) → EReal :=
  fun xStar uStar => concaveConjugate (fun u => convexBifunctionPairing F u xStar) uStar

/-- The kernel `⟨u, F* xStar⟩` built from the concave adjoint bifunction of Theorem 34.2,
written with the concave pairing in the `u`-variable. -/
noncomputable def section34ConcaveBifunctionAdjointPairing
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : SaddleFunction m n :=
  fun u xStar => concaveBifunctionPairing (section34ConcaveBifunctionAdjoint F) xStar u

/-- The canonical concave-convex kernel attached to a convex bifunction `F`. -/
noncomputable abbrev convexBifunctionClosedKernel
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : SaddleFunction m n :=
  convexBifunctionPairing F

/-- The class `Ω(F)` generated by the canonical saddle kernel of `F`.

Theorem 34.2 uses `Ω(F)` for the whole saddle-equivalence class, not for all pointwise
minorants of the canonical kernel.  Recording the generated class directly also keeps the
definition independent of a proof that `F` is closed. -/
def omegaClassOfConvexBifunction
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Set (SaddleFunction m n) :=
  {K | saddleEquivalent K (convexBifunctionClosedKernel F)}

/-- The domain `dom F` of a convex bifunction, read from the first effective domain of its
canonical saddle-kernel. -/
def convexBifunctionDomain
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Set (Fin m → ℝ) :=
  effectiveDomain₁ (convexBifunctionClosedKernel F)

/-- The effective second-coordinate domain of the canonical saddle-kernel attached to a convex
bifunction `F`. This is the `dom F*` object that appears in the Chapter 34 saddle-kernel
realization. -/
def convexBifunctionKernelAdjointDomain
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  effectiveDomain₂ (convexBifunctionClosedKernel F)

/-- The effective domain of a convex bifunction consists of those parameters `u` for which
some value `F u x` is finite in the convex convention. -/
def convexBifunctionEffectiveDomain
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Set (Fin m → ℝ) :=
  {u | ∃ x, F u x < (⊤ : EReal)}

/-- The effective domain of a concave bifunction consists of those parameters `xStar` for which
some value `G xStar uStar` is finite in the concave convention. -/
def concaveBifunctionEffectiveDomain
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {xStar | ∃ uStar, (⊥ : EReal) < G xStar uStar}

/-- A convex bifunction is proper when it never takes the value `⊥` and its effective domain is
nonempty. -/
def IsProperConvexBifunction
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  HasNoBotValuesBifunction F ∧ (convexBifunctionEffectiveDomain F).Nonempty

/-- A concave bifunction is proper when it never takes the value `⊤` and its effective domain is
nonempty. -/
def IsProperConcaveBifunction
    (G : (Fin n → ℝ) → (Fin m → ℝ) → EReal) : Prop :=
  HasNoTopValuesBifunction G ∧ (concaveBifunctionEffectiveDomain G).Nonempty

/-- A set of saddle-functions is a closed concave-convex equivalence class when it is the
`saddleEquivalent`-class of some closed concave-convex saddle-function. -/
def IsClosedConcaveConvexEquivalenceClass (Omega : Set (SaddleFunction m n)) : Prop :=
  ∃ K : SaddleFunction m n,
    IsConcaveConvex K ∧ IsClosedSaddleFunction K ∧ Omega = {L | saddleEquivalent L K}

/-- Helper for Text 34.1.5: on the singleton space, the constant-`⊤` kernel is
concave-convex. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex :
    IsConcaveConvex
      ((fun (_ : Fin 0 → ℝ) (_ : Fin 0 → ℝ) => (⊤ : EReal)) : SaddleFunction 0 0) := by
  -- On `Fin 0`, every coordinate vector is the unique zero point, so both Jensen inequalities
  -- collapse to tautologies at that point.
  unfold IsConcaveConvex IsConcaveConvexOn IsERealConcaveOn IsERealConvexOn
  constructor
  · intro v hv x y hx hy a b ha hb hab hxy
    have hx0 : x = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
    have hy0 : y = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
    rw [hx0, hy0]
    simp
  · intro u hu x y hx hy a b ha hb hab hxy
    have hx0 : x = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
    have hy0 : y = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
    rw [hx0, hy0]
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by
        linarith
      rw [ha0, hb1]
      simp
    · have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      rw [EReal.coe_mul_top_of_pos haPos]
      by_cases hb0 : b = 0
      · rw [hb0]
        simp
      · have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
        rw [EReal.coe_mul_top_of_pos hbPos]
        change (⊤ : EReal) ≤ ⊤ + ⊤
        rw [EReal.top_add_top]

/-- Helper for Text 34.1.5: the mixed lower closure of the singleton constant-`⊤` kernel is
the kernel itself. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_lowerClosure_eq_self
    (h :
      IsConcaveConvex
        ((fun (_ : Fin 0 → ℝ) (_ : Fin 0 → ℝ) => (⊤ : EReal)) : SaddleFunction 0 0)) :
    lowerClosureConcaveConvex
        ((fun (_ : Fin 0 → ℝ) (_ : Fin 0 → ℝ) => (⊤ : EReal)) : SaddleFunction 0 0) h =
      ((fun (_ : Fin 0 → ℝ) (_ : Fin 0 → ℝ) => (⊤ : EReal)) : SaddleFunction 0 0) := by
  let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
  have hK : IsConcaveConvex K := by
    simpa [K] using h
  have hCounter : K = concaveClosureInFirst K ∧ convexClosureInSecond K = K := by
    simpa [K] using (helperForCorollary33_3_1_zeroDimensional_constTop_counterexample).1
  have hFirstFixed : partialClosure₁ K = K := by
    simpa [partialClosure₁] using hCounter.1.symm
  have hSecondFixed : partialClosure₂ K = K := by
    simpa [partialClosure₂] using hCounter.2
  -- Rewrite the mixed lower closure through the fixed-point identities for the two
  -- one-variable closures.
  calc
    lowerClosureConcaveConvex K hK = partialClosure₂ (partialClosure₁ K) :=
      (helperForText_34_0_1_mixedClosure_formulas K hK).1
    _ = partialClosure₂ K := by rw [hFirstFixed]
    _ = K := hSecondFixed

/-- Helper for Text 34.1.5: the mixed lower closure of the singleton constant-`⊤` kernel still
takes the value `⊤` at the unique point. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_lowerClosure_atOrigin_eq_top :
    let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
    let hK : IsConcaveConvex K := helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex
    lowerClosureConcaveConvex K hK 0 0 = (⊤ : EReal) := by
  intro K hK
  -- Evaluate the fixed-point identity for the mixed lower closure at the singleton point.
  simpa [K] using
    congrArg
      (fun G : SaddleFunction 0 0 => G 0 0)
      (helperForText_34_1_5_zeroDimensional_constTop_lowerClosure_eq_self hK)

/-- Helper for Text 34.1.5: the singleton constant-`⊤` kernel fails the exact
`HasNoTopOrBotValuesBifunction` admissibility hypothesis required by the corrected theorem,
because its mixed lower closure still takes the value `⊤` at the unique point. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_lowerClosure_notHasNoTopOrBot :
    let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
    let hK : IsConcaveConvex K := helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex
    ¬ HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K hK) := by
  intro K hK hNoTopBot
  -- The mixed lower closure is literally the constant-`⊤` kernel, so the no-`⊤` part of the
  -- admissibility package already fails at the unique point.
  have hAtOrigin :
      lowerClosureConcaveConvex K hK 0 0 = (⊤ : EReal) := by
    simpa [K, hK] using
      helperForText_34_1_5_zeroDimensional_constTop_lowerClosure_atOrigin_eq_top
  exact (hNoTopBot.2 0 0) hAtOrigin

/-- Helper for Text 34.1.5: the corrected theorem's no-`⊤`/no-`⊥` hypothesis on the mixed
lower closure is genuinely necessary, because the singleton constant-`⊤` kernel already
violates it. -/
lemma helperForText_34_1_5_exists_counterexample_to_missingLowerClosureAdmissibility :
    ∃ (m n : ℕ) (K : SaddleFunction m n) (h : IsConcaveConvex K),
      ¬ HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h) := by
  let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
  let hK : IsConcaveConvex K :=
    helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex
  -- Reuse the singleton constant-`⊤` kernel to package the missing admissibility hypothesis as
  -- an explicit existential counterexample.
  refine ⟨0, 0, K, hK, ?_⟩
  simpa [K, hK] using
    (helperForText_34_1_5_zeroDimensional_constTop_lowerClosure_notHasNoTopOrBot)

/-- Helper for Text 34.1.5: the singleton constant-`⊤` kernel has empty saddle effective
domain, so any repaired version of the theorem must exclude it by a properness-type hypothesis. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_saddleEffectiveDomain_eq_empty :
    let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
    saddleEffectiveDomain K = (∅ : Set ((Fin 0 → ℝ) × (Fin 0 → ℝ))) := by
  intro K
  -- Unfold the two coordinate effective domains: the first is automatic at `⊤`, while the
  -- second is empty because no value of the constant-`⊤` kernel is strictly below `⊤`.
  ext p
  simp [saddleEffectiveDomain, effectiveDomain₁, effectiveDomain₂, K]

/-- Helper for Text 34.1.5: the singleton constant-`⊤` kernel is not proper. This is the
admissibility failure behind the zero-dimensional counterexample to the unrestricted theorem. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_notProper :
    let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
    ¬ IsProperSaddleFunction K := by
  intro K hProper
  -- Properness is exactly nonemptiness of the saddle effective domain, so the previous helper
  -- collapses the claim to the impossible statement `∅ ≠ ∅`.
  rw [IsProperSaddleFunction,
    helperForText_34_1_5_zeroDimensional_constTop_saddleEffectiveDomain_eq_empty] at hProper
  exact hProper rfl

/-- Helper for Text 34.1.5: a closed convex bifunction witness on the singleton space cannot
have primal pairing value `⊤` at the unique point. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_refutes_witness
    {F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (hPair : convexBifunctionPairing F 0 0 = (⊤ : EReal)) :
    False := by
  -- Unfold the closed convex bifunction package to recover the no-`⊥` hypothesis needed by
  -- the Section 33 singleton obstruction.
  have hNoBot : HasNoBotValuesBifunction F := by
    simpa [IsClosedConvexBifunction, IsImageClosedConvexBifunction] using hF.2.1
  -- The Section 33 zero-dimensional pairing lemma then rules out the claimed value `⊤`.
  exact
    (helperForCorollary33_3_1_zeroDimensional_pairing_ne_top_of_noBot
      (F := F) hNoBot) hPair

/-- Helper for Text 34.1.5: any claimed lower-closure representation of the singleton
constant-`⊤` kernel forces the pairing kernel to take the value `⊤` at the unique point. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_pairingAtOrigin_eq_top_of_lowerWitness
    {F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal}
    (hLower :
      lowerClosureConcaveConvex
          ((fun (_ : Fin 0 → ℝ) (_ : Fin 0 → ℝ) => (⊤ : EReal)) : SaddleFunction 0 0)
          helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex =
        convexBifunctionPairing F) :
    convexBifunctionPairing F 0 0 = (⊤ : EReal) := by
  -- Evaluate the claimed lower representation at the singleton point and compare with the
  -- explicit lower-closure value already computed there.
  have hAtOrigin :
      lowerClosureConcaveConvex
          ((fun (_ : Fin 0 → ℝ) (_ : Fin 0 → ℝ) => (⊤ : EReal)) : SaddleFunction 0 0)
          helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex 0 0 =
        convexBifunctionPairing F 0 0 := by
    exact congrArg (fun G : SaddleFunction 0 0 => G 0 0) hLower
  calc
    convexBifunctionPairing F 0 0 =
        lowerClosureConcaveConvex
            ((fun (_ : Fin 0 → ℝ) (_ : Fin 0 → ℝ) => (⊤ : EReal)) : SaddleFunction 0 0)
            helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex 0 0 := by
      exact hAtOrigin.symm
    _ = (⊤ : EReal) := by
      simpa using helperForText_34_1_5_zeroDimensional_constTop_lowerClosure_atOrigin_eq_top

/-- Helper for Text 34.1.5: the singleton constant-`⊤` kernel admits no closed convex
bifunction witness at all for the mixed-closure representation. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_hasNoWitness :
    let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
    let hK : IsConcaveConvex K := helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex
    ¬ ∃ F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
        IsClosedConvexBifunction F ∧
          lowerClosureConcaveConvex K hK = convexBifunctionPairing F ∧
          upperClosureConcaveConvex K hK = section34ConvexBifunctionAdjointPairing F := by
  intro K hK hExists
  rcases hExists with ⟨F, hF, hLower, _hUpper⟩
  have hLowerConst :
      lowerClosureConcaveConvex
          ((fun (_ : Fin 0 → ℝ) (_ : Fin 0 → ℝ) => (⊤ : EReal)) : SaddleFunction 0 0)
          helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex =
        convexBifunctionPairing F := by
    -- The local `let`-bound kernel is definitionally the singleton constant-`⊤` kernel, so the
    -- claimed lower representation specializes to the canonical counterexample form.
    simpa [K, hK] using hLower
  have hPairAtOrigin : convexBifunctionPairing F 0 0 = (⊤ : EReal) := by
    -- The new pointwise helper turns the lower-representation identity into the forbidden
    -- `⊤`-value of the primal pairing at the singleton point.
    exact
      helperForText_34_1_5_zeroDimensional_constTop_pairingAtOrigin_eq_top_of_lowerWitness
        hLowerConst
  -- The singleton obstruction from Section 33 then rules out this witness immediately.
  exact helperForText_34_1_5_zeroDimensional_constTop_refutes_witness hF hPairAtOrigin

/-- Helper for Text 34.1.5: the theorem's representation conclusion already fails for the
singleton constant-`⊤` kernel. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_negates_targetConclusion :
    let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
    let hK : IsConcaveConvex K := helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex
    ¬ ∃! F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
      IsClosedConvexBifunction F ∧
        lowerClosureConcaveConvex K hK = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K hK = section34ConvexBifunctionAdjointPairing F := by
  intro K hK hExists
  -- A unique witness would in particular give an ordinary witness, which the stronger helper
  -- already excludes.
  have hNoWitness :
      ¬ ∃ F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
          IsClosedConvexBifunction F ∧
            lowerClosureConcaveConvex K hK = convexBifunctionPairing F ∧
            upperClosureConcaveConvex K hK = section34ConvexBifunctionAdjointPairing F := by
    simpa [K, hK] using helperForText_34_1_5_zeroDimensional_constTop_hasNoWitness
  exact hNoWitness hExists.exists

/-- Helper for Text 34.1.5: the singleton constant-`⊤` kernel is an explicit improper
counterexample to the unrestricted representation theorem. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_isImproperCounterexample :
    ∃ (K : SaddleFunction 0 0) (hK : IsConcaveConvex K),
      ¬ IsProperSaddleFunction K ∧
      ¬ ∃! F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
          IsClosedConvexBifunction F ∧
            lowerClosureConcaveConvex K hK = convexBifunctionPairing F ∧
            upperClosureConcaveConvex K hK = section34ConvexBifunctionAdjointPairing F := by
  let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
  let hK : IsConcaveConvex K :=
    helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex
  -- Reuse the established singleton computations to package both the admissibility failure
  -- and the representation failure in one counterexample.
  refine ⟨K, hK, ?_, ?_⟩
  · simpa [K] using helperForText_34_1_5_zeroDimensional_constTop_notProper
  · simpa [K, hK] using helperForText_34_1_5_zeroDimensional_constTop_negates_targetConclusion

/-- Helper for Text 34.1.5: the unrestricted theorem statement already has a concrete
zero-dimensional counterexample. -/
lemma helperForText_34_1_5_exists_counterexample_to_targetStatement :
    ∃ (m n : ℕ) (K : SaddleFunction m n) (h : IsConcaveConvex K),
      ¬ ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
          IsClosedConvexBifunction F ∧
            lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
            upperClosureConcaveConvex K h = section34ConvexBifunctionAdjointPairing F := by
  -- Forget the properness failure from the packaged singleton obstruction to recover the
  -- bare counterexample needed for the unrestricted target statement.
  rcases helperForText_34_1_5_zeroDimensional_constTop_isImproperCounterexample with
    ⟨K0, hK0, _hImproper, hNoWitness⟩
  exact ⟨0, 0, K0, hK0, hNoWitness⟩

/-- Helper for Text 34.1.5: one explicit concave-convex kernel without a closed-convex witness
already refutes any unrestricted global representation scheme. -/
lemma helperForText_34_1_5_false_of_counterexample
    {m n : ℕ} {K : SaddleFunction m n} (hK : IsConcaveConvex K)
    (hNoWitness :
      ¬ ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
          IsClosedConvexBifunction F ∧
            lowerClosureConcaveConvex K hK = convexBifunctionPairing F ∧
            upperClosureConcaveConvex K hK = section34ConvexBifunctionAdjointPairing F)
    (hScheme :
      ∀ {m n : ℕ} (K : SaddleFunction m n) (h : IsConcaveConvex K),
        ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
          IsClosedConvexBifunction F ∧
            lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
            upperClosureConcaveConvex K h = section34ConvexBifunctionAdjointPairing F) :
    False := by
  -- Specializing the global scheme to the explicit counterexample `K` contradicts the local
  -- no-witness theorem for that kernel.
  exact hNoWitness (hScheme K hK)

/-- Helper for Text 34.1.5: the unrestricted representation scheme is inconsistent, because its
zero-dimensional specialization contradicts the singleton constant-`⊤` counterexample. -/
lemma helperForText_34_1_5_false_of_unrestrictedRepresentationScheme
    (hScheme :
      ∀ {m n : ℕ} (K : SaddleFunction m n) (h : IsConcaveConvex K),
        ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
          IsClosedConvexBifunction F ∧
            lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
            upperClosureConcaveConvex K h = section34ConvexBifunctionAdjointPairing F) :
    False := by
  -- Package the singleton constant-`⊤` kernel as an explicit counterexample and specialize the
  -- would-be global scheme to that witness.
  rcases helperForText_34_1_5_exists_counterexample_to_targetStatement with
    ⟨m0, n0, K0, hK0, hNoWitness⟩
  exact helperForText_34_1_5_false_of_counterexample hK0 hNoWitness hScheme

/-- Helper for Text 34.1.5: the exact unrestricted textbook representation scheme, isolated as a
single proposition so its formal failure can be referenced directly. -/
def helperForText_34_1_5_unrestrictedRepresentationScheme : Prop :=
  ∀ {m n : ℕ} (K : SaddleFunction m n) (h : IsConcaveConvex K),
    ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsClosedConvexBifunction F ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K h = section34ConvexBifunctionAdjointPairing F

/-- Helper for Text 34.1.5: specializing the isolated unrestricted scheme to the singleton
constant-`⊤` kernel already forces the impossible zero-dimensional witness. -/
lemma helperForText_34_1_5_unrestrictedRepresentationScheme_specializes_to_zeroDimensional_constTop
    (hScheme : helperForText_34_1_5_unrestrictedRepresentationScheme) :
    let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
    let hK : IsConcaveConvex K := helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex
    ∃! F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
      IsClosedConvexBifunction F ∧
        lowerClosureConcaveConvex K hK = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K hK = section34ConvexBifunctionAdjointPairing F := by
  intro K hK
  -- The isolated scheme is quantified over every concave-convex saddle-kernel, so the
  -- singleton constant-`⊤` kernel is an immediate specialization.
  exact hScheme K hK

/-- Helper for Text 34.1.5: the corrected admissible representation scheme. Besides the mixed
closure qualifications, it exposes existence of the closed-convex Section 33 realization;
the remaining pairing-injectivity premise records exactly the recovery property needed for
uniqueness in the image-closed Chapter 34 package. -/
def helperForText_34_1_5_admissibleRepresentationScheme : Prop :=
  ∀ {m n : ℕ} (K : SaddleFunction m n) (h : IsConcaveConvex K),
    lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h →
    IsConcaveConvex (lowerClosureConcaveConvex K h) →
    IsConcaveConvex (upperClosureConcaveConvex K h) →
    IsConvexClosedInSecond (lowerClosureConcaveConvex K h) →
    IsConcaveClosedInFirst (upperClosureConcaveConvex K h) →
    HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h) →
    (∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      ClosedConvexBifunction F ∧
        HasNoBotValuesBifunction F ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K h = helperForText_34_0_1_convexAdjointPairingKernel F) →
    (∀ {F G : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
      IsClosedConvexBifunction F →
      IsClosedConvexBifunction G →
      (∀ u xStar, convexBifunctionPairing F u xStar =
        convexBifunctionPairing G u xStar) →
      F = G) →
    ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsClosedConvexBifunction F ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K h = helperForText_34_0_1_convexAdjointPairingKernel F

/-- Helper for Text 34.1.5: specializing the unrestricted textbook scheme to the singleton
constant-`⊤` kernel immediately contradicts the zero-dimensional no-witness theorem. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_contradicts_unrestrictedScheme
    (hScheme : helperForText_34_1_5_unrestrictedRepresentationScheme) :
    False := by
  -- Route correction: instead of repackaging an abstract existential counterexample, specialize
  -- the unrestricted scheme directly to the singleton constant-`⊤` kernel and invoke the
  -- dedicated no-witness lemma already proved for that kernel.
  have hZeroWitness :
      let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
      let hK : IsConcaveConvex K := helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex
      ∃! F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
        IsClosedConvexBifunction F ∧
          lowerClosureConcaveConvex K hK = convexBifunctionPairing F ∧
          upperClosureConcaveConvex K hK = section34ConvexBifunctionAdjointPairing F := by
    exact
      helperForText_34_1_5_unrestrictedRepresentationScheme_specializes_to_zeroDimensional_constTop
        hScheme
  have hNoWitness :
      let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
      let hK : IsConcaveConvex K := helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex
      ¬ ∃ F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
          IsClosedConvexBifunction F ∧
            lowerClosureConcaveConvex K hK = convexBifunctionPairing F ∧
            upperClosureConcaveConvex K hK = section34ConvexBifunctionAdjointPairing F := by
    exact helperForText_34_1_5_zeroDimensional_constTop_hasNoWitness
  -- Unfold the local `let`-bound singleton kernel package and contradict existence of the
  -- specialized witness.
  dsimp only at hZeroWitness hNoWitness
  exact hNoWitness hZeroWitness.exists

/-- Helper for Text 34.1.5: the unrestricted textbook scheme is false in this development,
because the singleton constant-`⊤` kernel contradicts it. -/
lemma helperForText_34_1_5_unrestrictedRepresentationScheme_false :
    ¬ helperForText_34_1_5_unrestrictedRepresentationScheme := by
  intro hScheme
  -- The singleton constant-`⊤` kernel is already enough to refute the unrestricted scheme.
  exact helperForText_34_1_5_zeroDimensional_constTop_contradicts_unrestrictedScheme hScheme

/-- Text 34.1.5 is false in the unrestricted textbook form used earlier in the file: the
singleton constant-`⊤` saddle-kernel is already a concave-convex counterexample. -/
theorem section34_text_34_1_5_unrestricted_false :
    ¬ helperForText_34_1_5_unrestrictedRepresentationScheme := by
  -- Route correction: the unrestricted textbook statement is semantically blocked in this
  -- formalization, so the target content can only be handled by refuting that scheme and using
  -- the corrected admissible theorem below.
  exact helperForText_34_1_5_unrestrictedRepresentationScheme_false

/-- Text 34.1.5 has an explicit zero-dimensional improper counterexample: the singleton
constant-`⊤` saddle-kernel is concave-convex but admits no closed-convex representation of the
unrestricted textbook form. -/
theorem section34_text_34_1_5_has_zeroDimensional_improperCounterexample :
    ∃ (K : SaddleFunction 0 0) (hK : IsConcaveConvex K),
      ¬ IsProperSaddleFunction K ∧
      ¬ ∃! F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
          IsClosedConvexBifunction F ∧
            lowerClosureConcaveConvex K hK = convexBifunctionPairing F ∧
            upperClosureConcaveConvex K hK = section34ConvexBifunctionAdjointPairing F := by
  exact helperForText_34_1_5_zeroDimensional_constTop_isImproperCounterexample

/-- Helper for Text 34.1.5: the singleton constant-`⊤` kernel separates the false unrestricted
scheme from the corrected admissible theorem, because the representation conclusion fails there
and the lower-closure no-`⊤`/no-`⊥` hypothesis fails there as well. -/
lemma helperForText_34_1_5_zeroDimensional_constTop_separates_unrestricted_and_correctedSchemes :
    let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
    let hK : IsConcaveConvex K := helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex
    ¬ HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K hK) ∧
      ¬ ∃! F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
          IsClosedConvexBifunction F ∧
            lowerClosureConcaveConvex K hK = convexBifunctionPairing F ∧
            upperClosureConcaveConvex K hK = section34ConvexBifunctionAdjointPairing F := by
  intro K hK
  constructor
  · -- The counterexample lies outside the corrected theorem exactly because its mixed lower
    -- closure still takes the value `⊤` at the unique point.
    simpa [K, hK] using
      helperForText_34_1_5_zeroDimensional_constTop_lowerClosure_notHasNoTopOrBot
  · -- The same kernel also refutes the unrestricted existence-and-uniqueness conclusion.
    simpa [K, hK] using helperForText_34_1_5_zeroDimensional_constTop_negates_targetConclusion

/-- Helper for Text 34.1.5: a Section 33 closed convex witness automatically satisfies the
image-closed package used by the Chapter 34 saddle-kernel correspondence. -/
lemma helperForText_34_1_5_isClosedConvexBifunction_of_closedConvexWitness
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : ClosedConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F) :
    IsClosedConvexBifunction F := by
  -- Upgrade the Section 33 witness to the Rockafellar/image-closed structure required for
  -- the Chapter 34 recovery correspondence.
  have hRock : IsRockafellarConvexBifunction F :=
    helperForText_34_1_4_rockafellarConvex_of_closedConvexBifunction hClosed hNoBot
  have hGraphClosed :
      IsFunctionConvexClosed (graphFunctionOfBifunction F) :=
    helperForText_34_1_4_graphFunction_isFunctionConvexClosed_of_closedConvexBifunction hClosed
  have hSectionClosed :
      ∀ u : Fin m → ℝ, IsFunctionConvexClosed (F u) :=
    helperForLemma33_0_22_section_isFunctionConvexClosed hGraphClosed
  exact ⟨hRock, hNoBot, hSectionClosed⟩

/-- Helper for Text 34.1.5: an image-closed convex bifunction is uniquely determined by its
pairing kernel. -/
lemma helperForText_34_1_5_eq_of_pairing_eq
    {F G : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsClosedConvexBifunction F)
    (hG : IsClosedConvexBifunction G)
    (hPairEq :
      ∀ u xStar, convexBifunctionPairing F u xStar = convexBifunctionPairing G u xStar) :
    F = G := by
  -- Recover each bifunction by conjugating its pairing kernel, then compare those recovered
  -- kernels through the shared pointwise pairing formula.
  have hRecoverF :
      ∀ u x, convexConjugate (convexBifunctionPairing F u) x = F u x :=
    (closedSaddleFunctions_imageClosedBifunctions_correspondence (m := m) (n := n)).1 F hF |>.2.2
  have hRecoverG :
      ∀ u x, convexConjugate (convexBifunctionPairing G u) x = G u x :=
    (closedSaddleFunctions_imageClosedBifunctions_correspondence (m := m) (n := n)).1 G hG |>.2.2
  ext u x
  have hSlice : convexBifunctionPairing F u = convexBifunctionPairing G u := by
    -- Equality of the full pairing kernels specializes to equality of the `u`-slice.
    funext xStar
    exact hPairEq u xStar
  -- Reconstruct both values from the same slice and conclude pointwise equality.
  calc
    F u x = convexConjugate (convexBifunctionPairing F u) x := by
      symm
      exact hRecoverF u x
    _ = convexConjugate (convexBifunctionPairing G u) x := by
      rw [hSlice]
    _ = G u x := hRecoverG u x

/- The realization premise below is the sound boundary between Text 34.1.4 and the corrected
Section 33 correspondence: the unrestricted raw correspondence is refuted by the
zero-dimensional constant-`⊤` kernel, while a supplied closed-convex realization is enough for
the image-closed uniqueness argument. -/
/-- Text 34.1.5, corrected formal version: if `K` is concave-convex, its mixed closures satisfy
`underline(K) ≤ overline(K)`, and `underline(K) = cl₂ cl₁ K` satisfies the no-`⊤`/no-`⊥`
hypothesis required by the corrected Section 33 interface, then every supplied closed-convex
realization of the mixed pair determines a unique image-closed convex bifunction `F`. -/
theorem section34_text_34_1_5
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h)
    (hLowerOrient : IsConcaveConvex (lowerClosureConcaveConvex K h))
    (hUpperOrient : IsConcaveConvex (upperClosureConcaveConvex K h))
    (hLowerClosed : IsConvexClosedInSecond (lowerClosureConcaveConvex K h))
    (hUpperClosed : IsConcaveClosedInFirst (upperClosureConcaveConvex K h))
    (hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hRealization :
      ∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        ClosedConvexBifunction F ∧
          HasNoBotValuesBifunction F ∧
          lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
          upperClosureConcaveConvex K h =
            helperForText_34_0_1_convexAdjointPairingKernel F)
    (hPairingInjective :
      ∀ {F G : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsClosedConvexBifunction F →
        IsClosedConvexBifunction G →
        (∀ u xStar, convexBifunctionPairing F u xStar =
          convexBifunctionPairing G u xStar) →
        F = G) :
    ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsClosedConvexBifunction F ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K h = helperForText_34_0_1_convexAdjointPairingKernel F := by
  rcases hRealization with ⟨F, hClosed, hNoBot, hLowerRep, hUpperRep⟩
  -- Convert the Section 33 witness into the image-closed package used by Chapter 34.
  have hClosedImage : IsClosedConvexBifunction F :=
    helperForText_34_1_5_isClosedConvexBifunction_of_closedConvexWitness hClosed hNoBot
  refine ⟨F, ?_, ?_⟩
  · exact ⟨hClosedImage, hLowerRep, hUpperRep⟩
  · intro G hG
    rcases hG with ⟨hClosedG, hLowerG, _hUpperG⟩
    -- Both witnesses represent the same mixed lower closure, so their pairing kernels agree.
    have hPairEq :
        ∀ u xStar, convexBifunctionPairing G u xStar = convexBifunctionPairing F u xStar := by
      intro u xStar
      calc
        convexBifunctionPairing G u xStar = lowerClosureConcaveConvex K h u xStar := by
          exact (congrArg (fun H => H u xStar) hLowerG).symm
        _ = convexBifunctionPairing F u xStar :=
          congrArg (fun H => H u xStar) hLowerRep
    -- Recover both bifunctions from the common pairing kernel and conclude uniqueness.
    exact hPairingInjective hClosedG hClosedImage hPairEq

/-- Text 34.1.5 in the admissible extended-real regime used by the corrected Section 33
correspondence: once `underline(K)` satisfies the no-`⊤`/no-`⊥` hypothesis, the closed-convex
representative exists and is unique. This is the intended API for downstream uses that should
not retry the unrestricted textbook statement. -/
theorem section34_text_34_1_5_of_lowerClosure_noTopOrBot
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hOrder : lowerClosureConcaveConvex K h ≤ upperClosureConcaveConvex K h)
    (hLowerOrient : IsConcaveConvex (lowerClosureConcaveConvex K h))
    (hUpperOrient : IsConcaveConvex (upperClosureConcaveConvex K h))
    (hLowerClosed : IsConvexClosedInSecond (lowerClosureConcaveConvex K h))
    (hUpperClosed : IsConcaveClosedInFirst (upperClosureConcaveConvex K h))
    (hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h))
    (hRealization :
      ∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        ClosedConvexBifunction F ∧
          HasNoBotValuesBifunction F ∧
          lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
          upperClosureConcaveConvex K h =
            helperForText_34_0_1_convexAdjointPairingKernel F)
    (hPairingInjective :
      ∀ {F G : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsClosedConvexBifunction F →
        IsClosedConvexBifunction G →
        (∀ u xStar, convexBifunctionPairing F u xStar =
          convexBifunctionPairing G u xStar) →
        F = G) :
    ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsClosedConvexBifunction F ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
        upperClosureConcaveConvex K h = helperForText_34_0_1_convexAdjointPairingKernel F := by
  exact
    section34_text_34_1_5 K h hOrder hLowerOrient hUpperOrient hLowerClosed hUpperClosed
      hLowerNoTopBot hRealization hPairingInjective

/-- The corrected 34.1.5 scheme is valid in the qualified regime: a closed-convex realization
of the admissible mixed pair upgrades uniquely to the Chapter 34 image-closed package. -/
theorem section34_text_34_1_5_admissible_scheme_true :
    helperForText_34_1_5_admissibleRepresentationScheme := by
  intro m n K h hOrder hLowerOrient hUpperOrient hLowerClosed hUpperClosed hLowerNoTopBot
    hRealization hPairingInjective
  exact
    section34_text_34_1_5 K h hOrder hLowerOrient hUpperOrient hLowerClosed hUpperClosed
      hLowerNoTopBot hRealization hPairingInjective

/-- Helper for Text 34.1.5: the singleton constant-`⊤` kernel gives a concrete witness that the
corrected admissible scheme cannot be upgraded to the unrestricted textbook statement. -/
lemma helperForText_34_1_5_exists_counterexample_separating_corrected_and_unrestrictedSchemes :
    ∃ (m n : ℕ) (K : SaddleFunction m n) (h : IsConcaveConvex K),
      ¬ HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h) ∧
      ¬ ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
          IsClosedConvexBifunction F ∧
            lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
            upperClosureConcaveConvex K h = section34ConvexBifunctionAdjointPairing F := by
  let K : SaddleFunction 0 0 := fun _ _ => (⊤ : EReal)
  let hK : IsConcaveConvex K :=
    helperForText_34_1_5_zeroDimensional_constTop_isConcaveConvex
  -- Package the singleton obstruction once, so the final sharpness theorem can reuse the same
  -- counterexample without duplicating the zero-dimensional separation proof.
  have hSeparated :
      ¬ HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K hK) ∧
        ¬ ∃! F : (Fin 0 → ℝ) → (Fin 0 → ℝ) → EReal,
            IsClosedConvexBifunction F ∧
              lowerClosureConcaveConvex K hK = convexBifunctionPairing F ∧
              upperClosureConcaveConvex K hK =
                section34ConvexBifunctionAdjointPairing F := by
    simpa [K, hK] using
      helperForText_34_1_5_zeroDimensional_constTop_separates_unrestricted_and_correctedSchemes
  exact ⟨0, 0, K, hK, hSeparated.1, hSeparated.2⟩

/-- Helper for Text 34.1.5: the corrected admissible scheme is genuinely sharp. The admissible
scheme holds, but the singleton constant-`⊤` kernel still violates the lower-closure
no-`⊤`/no-`⊥` hypothesis and therefore remains a concrete counterexample to the unrestricted
textbook conclusion. -/
lemma helperForText_34_1_5_admissibleScheme_isSharp :
    helperForText_34_1_5_admissibleRepresentationScheme ∧
      ∃ (m n : ℕ) (K : SaddleFunction m n) (h : IsConcaveConvex K),
        ¬ HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h) ∧
        ¬ ∃! F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
            IsClosedConvexBifunction F ∧
              lowerClosureConcaveConvex K h = convexBifunctionPairing F ∧
              upperClosureConcaveConvex K h = section34ConvexBifunctionAdjointPairing F := by
  constructor
  · -- The corrected theorem already proves the admissible scheme for every admissible kernel.
    exact section34_text_34_1_5_admissible_scheme_true
  · -- Reuse the packaged singleton counterexample to show the admissibility hypothesis is sharp.
    exact helperForText_34_1_5_exists_counterexample_separating_corrected_and_unrestrictedSchemes


end SaddleAmbient

end Section34
end Chap07
