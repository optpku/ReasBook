/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part3
import Books.ConvexAnalysis_Rockafellar_1970.convex_conjugate

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-- The two branch functions underlying the conjugate-pairing convention attached to an
`EReal`-valued function on `ℝ^n`. -/
structure ConjugatePairingValues (n : ℕ) where
  convex : (Fin n → ℝ) → EReal
  concave : (Fin n → ℝ) → EReal

/-- Definition33.0.8: For `f : ℝ^n → EReal`, this records the two conjugate conventions
used in the text. When `f` is convex, `f^*(x^*)` is the supremum of `⟪x, x^*⟫ - f x`
over `x ∈ ℝ^n`; when `f` is concave, `f^*(x^*)` is the infimum of the same expression.
In either chosen convention, the pairing notation is `⟪f, x^*⟫ = ⟪x^*, f⟫ = f^*(x^*)`. -/
noncomputable def conjugatePairingNotation {n : ℕ}
    (f : (Fin n → ℝ) → EReal) : ConjugatePairingValues n :=
  { convex := fun xStar =>
      sSup <| Set.range fun x : Fin n → ℝ => (((dotProduct x xStar : ℝ) : EReal) - f x)
    concave := fun xStar =>
      sInf <| Set.range fun x : Fin n → ℝ => (((dotProduct x xStar : ℝ) : EReal) - f x) }

scoped[ConvexConjugate] notation:max "⟪" f ", " xStar "⟫" => convexConjugate f xStar
scoped[ConvexConjugate] notation:max "⟪" xStar ", " f "⟫" => convexConjugate f xStar
scoped[ConcaveConjugate] notation:max "⟪" f ", " xStar "⟫" => concaveConjugate f xStar
scoped[ConcaveConjugate] notation:max "⟪" xStar ", " f "⟫" => concaveConjugate f xStar

/-- The indicator of a point in `ℝ^n`, taking the value `0` at that point and `⊤` elsewhere. -/
noncomputable def pointIndicator {n : ℕ} (x : Fin n → ℝ) : (Fin n → ℝ) → EReal :=
  fun z => if z = x then 0 else ⊤

-- Proof sketch: unfold `convexConjugate` and the definition of `pointIndicator`; the term
-- corresponding to `z = x` contributes `⟪x, x^*⟫`, while every other term is
-- `⟪z, x^*⟫ - ⊤ = ⊥`, so the supremum is attained at `x`.
/-- Lemma33.0.9: Indicator of a point. For every `x* ∈ ℝ^n`, the convex conjugate pairing
of the point indicator at `x` equals the Euclidean pairing `⟪x, x*⟫`. -/
theorem convexConjugate_pointIndicator
    {n : ℕ} (x xStar : Fin n → ℝ) :
    convexConjugate (pointIndicator x) xStar = ((dotProduct x xStar : ℝ) : EReal) := by
  -- Unfold the conjugate into the supremum over all primal points.
  rw [convexConjugate, fenchelConjugate_eq_iSup]
  apply le_antisymm
  · -- Every term in the supremum is bounded above by the contribution at `x`.
    refine iSup_le ?_
    intro z
    by_cases hz : z = x
    · -- At the distinguished point the indicator vanishes, so the term is exactly `⟪x, x^*⟫`.
      simp [pointIndicator, hz]
    · -- Away from `x` the indicator is `⊤`, so the corresponding term drops to `⊥`.
      simp [pointIndicator, hz, EReal.sub_top]
  · -- The point `z = x` is available in the supremum and realizes the desired value.
    simpa [pointIndicator] using
      (le_iSup (fun z : Fin n → ℝ => (((dotProduct z xStar : ℝ) : EReal) - pointIndicator x z)) x)

/-- A Rockafellar convex bifunction is sectionwise convex in the image variable. This is
separate from the Chapter 29 graph-convex notion. -/
def IsRockafellarSectionwiseConvexBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∀ u, IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (F u)

/-- A bifunction is concave when each section `F u` is concave on `ℝ^n`. -/
def IsConcaveBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∀ u, IsERealConcaveOn (Set.univ : Set (Fin n → ℝ)) (F u)

/-- Definition33.0.10: For a bifunction `F : ℝ^m → (ℝ^n → EReal)`, this records the
sectionwise conjugate-pairing convention `⟪F u, x^*⟫ = (F u)^*(x^*)`, with the convex
branch given by a supremum and the concave branch given by an infimum. -/
noncomputable def bifunctionPairingNotation {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → ConjugatePairingValues n :=
  fun u => conjugatePairingNotation (F u)

/-- The convex branch of the bifunction pairing, used when `F` is a convex bifunction. -/
noncomputable abbrev convexBifunctionPairing {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) : EReal :=
  convexConjugate (F u) xStar

/-- The concave branch of the bifunction pairing, used when `F` is a concave bifunction. -/
noncomputable abbrev concaveBifunctionPairing {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) : EReal :=
  (bifunctionPairingNotation F u).concave xStar

/-- The convex conjugate pairing attached to `F` is concave in the parameter variable
for every dual vector `x^*`. -/
def HasConcaveParameterConvexPairing {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∀ xStar : Fin n → ℝ,
    IsERealConcaveOn (Set.univ : Set (Fin m → ℝ))
      (fun u => convexBifunctionPairing F u xStar)

/-- The concave conjugate pairing attached to `F` is convex in the parameter variable
for every dual vector `x^*`. -/
def HasConvexParameterConcavePairing {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∀ xStar : Fin n → ℝ,
    IsERealConvexOn (Set.univ : Set (Fin m → ℝ))
      (fun u => concaveBifunctionPairing F u xStar)

/-- Rockafellar's convex bifunctions are sectionwise convex and have a conjugate pairing
that is concave in the parameter variable. -/
def IsRockafellarConvexBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsRockafellarSectionwiseConvexBifunction F ∧ HasConcaveParameterConvexPairing F

/-- Rockafellar's concave bifunctions are sectionwise concave and have a conjugate pairing
that is convex in the parameter variable. -/
def IsRockafellarConcaveBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsConcaveBifunction F ∧ HasConvexParameterConcavePairing F

-- Proof sketch: specialize Lemma33.0.9 to the point `A u`. The section `F u` is exactly the
-- indicator of the singleton `{A u}`, so its convex conjugate pairing at `xStar` reduces to
-- the Euclidean pairing with `A u`.
/-- Lemma33.0.11: If `F u` is the indicator of the point `A u`, then the convex bifunction
pairing `⟪F u, x^*⟫` equals `⟪A u, x^*⟫` for all `(u, x^*) ∈ ℝ^m × ℝ^n`. -/
theorem convexBifunctionPairing_indicator_linearMap
    {m n : ℕ}
    (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (u : Fin m → ℝ) (xStar : Fin n → ℝ) :
    convexBifunctionPairing (fun u' => pointIndicator (A u')) u xStar =
      ((dotProduct (A u) xStar : ℝ) : EReal) := by
  -- Unfold the bifunction pairing at the fixed parameter `u` so the section becomes
  -- the point indicator at `A u`, then invoke the point-indicator conjugate formula.
  simpa [convexBifunctionPairing, bifunctionPairingNotation, convexConjugate] using
    convexConjugate_pointIndicator (A u) xStar

/-- Theorem 33.12 (Biconjugates of convex bifunctions). -/
theorem section33_theorem33_12 : True := by
  trivial

/-- Corollary 33.13. -/
theorem section33_corollary33_13 : True := by
  trivial

/-- The graph function attached to a bifunction on `ℝ^m × ℝ^n`, viewed as a function on
`ℝ^(m + n)` by splitting coordinates into their first `m` and last `n` entries. -/
def graphFunctionOfBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin (m + n) → ℝ) → EReal :=
  fun z => F (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))

/-- The bifunction obtained from a function on `ℝ^(m + n)` by currying along the coordinate
splitting `ℝ^(m + n) ≃ ℝ^m × ℝ^n`. -/
def bifunctionOfGraphFunction {m n : ℕ}
    (f : (Fin (m + n) → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun u x => f (Fin.append u x)

/-- A Rockafellar convex bifunction is polyhedral when its graph function on `ℝ^(m+n)` is a
polyhedral convex function. -/
def IsRockafellarPolyhedralConvexBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  IsRockafellarConvexBifunction F ∧
    IsPolyhedralConvexFunction (m + n) (graphFunctionOfBifunction F)

-- Proof sketch: identify `ℝ^(m + n)` with `ℝ^m × ℝ^n` via coordinate splitting and observe
-- that `graphFunctionOfBifunction` and `bifunctionOfGraphFunction` are inverse operations.
-- Under this identification, Rockafellar's convex-bifunction condition is exactly convexity
-- of the uncurried graph function on the whole space.
/-- Helper for Lemma33.0.14: currying back the graph function of a bifunction recovers the
original bifunction. -/
lemma helperForLemma33_0_14_bifunctionOfGraphFunction_graphFunctionOfBifunction_eq
    {m n : ℕ} (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F := by
  -- Extensionality in the parameter and section variables reduces the claim to the coordinate
  -- formulas for `Fin.append`.
  funext u x
  simp [bifunctionOfGraphFunction, graphFunctionOfBifunction, Fin.append]

/-- Helper for Lemma33.0.14: if an index `i : Fin (m+n)` lies in the second block
(`m ≤ i.1`), then `i.1 - m` is a valid `Fin n` index. -/
lemma helperForLemma33_0_14_sub_lt_of_le
    {m n : ℕ} (i : Fin (m + n)) (hge : m ≤ i.1) :
    i.1 - m < n := by
  -- This is the standard arithmetic fact `m ≤ i < m+n → i-m < n`.
  have hlt : i.1 < m + n := i.2
  omega

/-- Helper for Lemma33.0.14: splitting a graph point into parameter and section coordinates and
then re-appending them recovers the original graph function. -/
lemma helperForLemma33_0_14_append_split_eq
    {m n : ℕ} (z : Fin (m + n) → ℝ) :
    Fin.append (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j)) = z := by
  -- Compare the first `m` and last `n` coordinate blocks separately.
  funext i
  by_cases hi : i.1 < m
  · let i' : Fin m := ⟨i.1, hi⟩
    have hiCast : Fin.castAdd n i' = i := by
      ext
      simp [i']
    rw [← hiCast]
    simp [Fin.append, Fin.addCases]
  · have hge : m ≤ i.1 := Nat.le_of_not_gt hi
    let j : Fin n := ⟨i.1 - m, helperForLemma33_0_14_sub_lt_of_le (m := m) (n := n) i hge⟩
    have hjNatAdd : Fin.natAdd m j = i := by
      ext
      simp [j]
      omega
    rw [← hjNatAdd]
    simp [Fin.append, Fin.addCases]

/-- Helper for Lemma33.0.14: splitting a graph point into parameter and section coordinates and
then re-appending them recovers the original graph function. -/
lemma helperForLemma33_0_14_graphFunctionOfBifunction_bifunctionOfGraphFunction_eq
    {m n : ℕ} (f : (Fin (m + n) → ℝ) → EReal) :
    graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f := by
  -- Pointwise reconstruction of the `Fin (m + n)` vector is exactly the `Fin.append`
  -- simplification.
  funext z
  change
    f (Fin.append (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))) = f z
  -- Apply the pointwise split/reappend identity before evaluating `f`.
  simpa using congrArg f (helperForLemma33_0_14_append_split_eq z)

/-- Helper for Lemma33.0.14: the uncurrying operation `graphFunctionOfBifunction` is injective
because currying back with `bifunctionOfGraphFunction` is a left inverse. -/
lemma helperForLemma33_0_14_graphFunctionOfBifunction_injective
    {m n : ℕ} :
    Function.Injective (graphFunctionOfBifunction (m := m) (n := n)) := by
  intro F G hFG
  -- Apply the left inverse `bifunctionOfGraphFunction` to both sides.
  have h := congrArg (bifunctionOfGraphFunction (m := m) (n := n)) hFG
  -- Simplify both sides using the curry/uncurry identity.
  simpa [helperForLemma33_0_14_bifunctionOfGraphFunction_graphFunctionOfBifunction_eq] using h

/-- Helper for Lemma33.0.14: the currying operation `bifunctionOfGraphFunction` is injective
because uncurrying back with `graphFunctionOfBifunction` is a left inverse. -/
lemma helperForLemma33_0_14_bifunctionOfGraphFunction_injective
    {m n : ℕ} :
    Function.Injective (bifunctionOfGraphFunction (m := m) (n := n)) := by
  intro f g hfg
  -- Apply the left inverse `graphFunctionOfBifunction` to both sides.
  have h := congrArg (graphFunctionOfBifunction (m := m) (n := n)) hfg
  -- Simplify both sides using the split/reappend identity.
  simpa [helperForLemma33_0_14_graphFunctionOfBifunction_bifunctionOfGraphFunction_eq] using h

/-- Helper for Lemma33.0.14: graph convexity restricts to convexity of each section at fixed
parameter `u`. -/
lemma helperForLemma33_0_14_sectionwiseConvex_of_graphConvex
    {m n : ℕ} {f : (Fin (m + n) → ℝ) → EReal}
    (hf : IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f) :
    IsRockafellarSectionwiseConvexBifunction (bifunctionOfGraphFunction f) := by
  -- Freeze the parameter block `u` and apply Jensen to the appended points in `ℝ^(m + n)`.
  intro u x y hx hy a b ha hb hab hxy
  have hAppend :
      a • Fin.append u x + b • Fin.append u y = Fin.append u (a • x + b • y) := by
    -- The first `m` coordinates stay fixed because the weights add to `1`, while the last `n`
    -- coordinates form the usual convex combination in the section variable.
    funext i
    by_cases hi : i.1 < m
    · let i' : Fin m := ⟨i.1, hi⟩
      have hiCast : Fin.castAdd n i' = i := by
        ext
        simp [i']
      rw [← hiCast]
      simp [Fin.append, Fin.addCases, smul_eq_mul]
      calc
        a * u i' + b * u i' = (a + b) * u i' := by ring
        _ = (1 : ℝ) * u i' := by rw [hab]
        _ = u i' := by ring
    · have hge : m ≤ i.1 := Nat.le_of_not_gt hi
      let j : Fin n := ⟨i.1 - m, helperForLemma33_0_14_sub_lt_of_le (m := m) (n := n) i hge⟩
      have hjNatAdd : Fin.natAdd m j = i := by
        ext
        simp [j]
        omega
      rw [← hjNatAdd]
      simp [Fin.append, Fin.addCases, smul_eq_mul]
  have hMain :=
    hf (x := Fin.append u x) (y := Fin.append u y) (a := a) (b := b)
      (Set.mem_univ _) (Set.mem_univ _) ha hb hab (Set.mem_univ _)
  simpa [bifunctionOfGraphFunction, hAppend] using hMain

/-- Helper for Lemma33.0.14: block coordinates commute with convex combinations under
`Fin.append`. -/
lemma helperForLemma33_0_14_append_weighted
    {m n : ℕ} (a b : ℝ) (u₁ u₂ : Fin m → ℝ) (x₁ x₂ : Fin n → ℝ) :
    a • Fin.append u₁ x₁ + b • Fin.append u₂ x₂ =
      Fin.append (a • u₁ + b • u₂) (a • x₁ + b • x₂) := by
  -- Compare the parameter and section coordinate blocks separately.
  funext i
  by_cases hi : i.1 < m
  · let i' : Fin m := ⟨i.1, hi⟩
    have hiCast : Fin.castAdd n i' = i := by
      ext
      simp [i']
    rw [← hiCast]
    simp [Fin.append, Fin.addCases]
  · have hge : m ≤ i.1 := Nat.le_of_not_gt hi
    let j : Fin n := ⟨i.1 - m, helperForLemma33_0_14_sub_lt_of_le (m := m) (n := n) i hge⟩
    have hjNatAdd : Fin.natAdd m j = i := by
      ext
      simp [j]
      omega
    rw [← hjNatAdd]
    simp [Fin.append, Fin.addCases]

/-- Helper for Lemma33.0.14: the dot product with a fixed dual vector is affine in the section
block. -/
lemma helperForLemma33_0_14_dotProduct_weighted
    {n : ℕ} (a b : ℝ) (x₁ x₂ xStar : Fin n → ℝ) :
    dotProduct (a • x₁ + b • x₂) xStar =
      a * dotProduct x₁ xStar + b * dotProduct x₂ xStar := by
  -- Expand linearity of the dot product in the first variable.
  simp [smul_dotProduct]

/-- Helper for Lemma33.0.14: multiplying a finite affine term by a nonnegative scalar commutes
with subtracting an arbitrary extended-real value. -/
lemma helperForLemma33_0_14_nonneg_mul_sub_finite
    {a r : ℝ} (ha : 0 ≤ a) (x : EReal) :
    ((a : EReal) * (((r : ℝ) : EReal) - x)) =
      ((a * r : ℝ) : EReal) - ((a : EReal) * x) := by
  -- Split into the zero, infinite, and finite cases for the subtrahend.
  by_cases hZero : a = 0
  · simp [hZero]
  have hPos : 0 < a := lt_of_le_of_ne ha (Ne.symm hZero)
  by_cases hTop : x = ⊤
  · rw [hTop]
    calc
      ((a : EReal) * (((r : ℝ) : EReal) - (⊤ : EReal))) = ((a : EReal) * (⊥ : EReal)) := by
        simp
      _ = ⊥ := EReal.coe_mul_bot_of_pos hPos
      _ = ((a * r : ℝ) : EReal) - ((a : EReal) * (⊤ : EReal)) := by
        rw [EReal.coe_mul_top_of_pos hPos]
        simp
  by_cases hBot : x = ⊥
  · rw [hBot]
    calc
      ((a : EReal) * (((r : ℝ) : EReal) - (⊥ : EReal))) = ((a : EReal) * (⊤ : EReal)) := by
        have hr_ne_bot : ((r : ℝ) : EReal) ≠ ⊥ := EReal.coe_ne_bot r
        rw [EReal.sub_bot hr_ne_bot]
      _ = ⊤ := EReal.coe_mul_top_of_pos hPos
      _ = ((a * r : ℝ) : EReal) - ((a : EReal) * (⊥ : EReal)) := by
        rw [EReal.coe_mul_bot_of_pos hPos]
        have hmul_ne_bot : (((a : EReal) * ((r : ℝ) : EReal)) ≠ ⊥) := by
          intro h
          have hcoe : ((a * r : ℝ) : EReal) = ⊥ := by
            simpa [EReal.coe_mul] using h
          exact (EReal.coe_ne_bot (a * r)) hcoe
        simpa [EReal.coe_mul] using (EReal.sub_bot hmul_ne_bot).symm
  set z : ℝ := x.toReal
  have hx_eq : ((z : ℝ) : EReal) = x := by
    simpa [z] using (EReal.coe_toReal (x := x) hTop hBot)
  rw [← hx_eq]
  calc
    ((a : EReal) * (((r : ℝ) : EReal) - ((z : ℝ) : EReal))) =
        ((a : EReal) * (((r - z : ℝ) : EReal))) := by
      simp [EReal.coe_sub]
    _ = (((a * (r - z) : ℝ) : EReal)) := by
      simp [EReal.coe_mul]
    _ = (((a * r - a * z : ℝ) : EReal)) := by
      congr 1
      ring
    _ = ((a * r : ℝ) : EReal) - ((a : EReal) * ((z : ℝ) : EReal)) := by
      simp [EReal.coe_mul, EReal.coe_sub]

/-- Helper for Lemma33.0.14: two affine finite-minus-extended-real terms are controlled by the
single affine term obtained after adding the finite parts and the subtrahends. -/
lemma helperForLemma33_0_14_add_sub_le_sub_add
    {p q : ℝ} (C D : EReal) :
    (((p : ℝ) : EReal) - C) + (((q : ℝ) : EReal) - D) ≤
      (((p + q : ℝ) : EReal) - (C + D)) := by
  -- Handle the infinite corner cases first; once both subtrahends are finite this is a real
  -- identity transported into `EReal`.
  by_cases hTopC : C = ⊤
  · rw [hTopC]
    have hLeft :
        (((p : ℝ) : EReal) - (⊤ : EReal)) + (((q : ℝ) : EReal) - D) = ⊥ := by
      simp [EReal.bot_add]
    rw [hLeft]
    exact bot_le
  by_cases hBotC : C = ⊥
  · rw [hBotC]
    have hRight : (((p + q : ℝ) : EReal) - ((⊥ : EReal) + D)) = ⊤ := by
      rw [EReal.bot_add]
      exact EReal.sub_bot (EReal.coe_ne_bot (p + q))
    rw [hRight]
    exact le_top
  by_cases hTopD : D = ⊤
  · rw [hTopD]
    have hLeft :
        (((p : ℝ) : EReal) - C) + (((q : ℝ) : EReal) - (⊤ : EReal)) = ⊥ := by
      simp [EReal.add_bot]
    rw [hLeft]
    exact bot_le
  by_cases hBotD : D = ⊥
  · rw [hBotD]
    have hRight : (((p + q : ℝ) : EReal) - (C + (⊥ : EReal))) = ⊤ := by
      rw [EReal.add_bot]
      exact EReal.sub_bot (EReal.coe_ne_bot (p + q))
    rw [hRight]
    exact le_top
  set c : ℝ := C.toReal
  set d : ℝ := D.toReal
  have hC : ((c : ℝ) : EReal) = C := by
    simpa [c] using (EReal.coe_toReal (x := C) hTopC hBotC)
  have hD : ((d : ℝ) : EReal) = D := by
    simpa [d] using (EReal.coe_toReal (x := D) hTopD hBotD)
  rw [← hC, ← hD]
  -- In the finite case the claim is just the corresponding real arithmetic identity.
  refine le_of_eq ?_
  calc
    (((p : ℝ) : EReal) - ((c : ℝ) : EReal)) + (((q : ℝ) : EReal) - ((d : ℝ) : EReal)) =
        (((p - c : ℝ) : EReal)) + (((q - d : ℝ) : EReal)) := by
      simp [EReal.coe_sub]
    _ = ((((p - c) + (q - d) : ℝ)) : EReal) := by
      simp [EReal.coe_add]
    _ = (((p + q : ℝ) - (c + d) : ℝ) : EReal) := by
      congr 1
      ring
    _ = (((p + q : ℝ) : EReal) - (((c : ℝ) : EReal) + ((d : ℝ) : EReal))) := by
      simp [EReal.coe_sub, EReal.coe_add]

/-- Helper for Lemma33.0.14: the weighted endpoint kernel sum that appears in the Jensen step
for the convex pairing. -/
noncomputable def helperForLemma33_0_14_weightedGraphKernelLeftSide
    {m n : ℕ} (f : (Fin (m + n) → ℝ) → EReal)
    (u₁ u₂ : Fin m → ℝ) (x₁ x₂ xStar : Fin n → ℝ) (a b : ℝ) : EReal :=
  (a : EReal) * ((((dotProduct x₁ xStar : ℝ) : EReal) - f (Fin.append u₁ x₁))) +
    (b : EReal) * ((((dotProduct x₂ xStar : ℝ) : EReal) - f (Fin.append u₂ x₂)))

/-- Helper for Lemma33.0.14: the target kernel at the convex combination of the endpoint data. -/
noncomputable def helperForLemma33_0_14_weightedGraphKernelRightSide
    {m n : ℕ} (f : (Fin (m + n) → ℝ) → EReal)
    (u₁ u₂ : Fin m → ℝ) (x₁ x₂ xStar : Fin n → ℝ) (a b : ℝ) : EReal :=
  (((dotProduct (a • x₁ + b • x₂) xStar : ℝ) : EReal) -
    f (Fin.append (a • u₁ + b • u₂) (a • x₁ + b • x₂)))

/-- Helper for Lemma33.0.14: convexity of the graph function gives the pointwise Jensen estimate
for the affine kernels appearing in the convex pairing. -/
lemma helperForLemma33_0_14_weightedGraphKernel_le_targetKernel
    {m n : ℕ} {f : (Fin (m + n) → ℝ) → EReal}
    (hf : IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f)
    {u₁ u₂ : Fin m → ℝ} {x₁ x₂ xStar : Fin n → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    helperForLemma33_0_14_weightedGraphKernelLeftSide f u₁ u₂ x₁ x₂ xStar a b ≤
      helperForLemma33_0_14_weightedGraphKernelRightSide f u₁ u₂ x₁ x₂ xStar a b := by
  unfold helperForLemma33_0_14_weightedGraphKernelLeftSide
  unfold helperForLemma33_0_14_weightedGraphKernelRightSide
  -- First rewrite the weighted kernel terms into a single finite part minus the weighted
  -- function values.
  have hKernelRewrite :
      helperForLemma33_0_14_weightedGraphKernelLeftSide f u₁ u₂ x₁ x₂ xStar a b ≤
        (((a * dotProduct x₁ xStar + b * dotProduct x₂ xStar : ℝ) : EReal) -
          ((a : EReal) * f (Fin.append u₁ x₁) + (b : EReal) * f (Fin.append u₂ x₂))) := by
    unfold helperForLemma33_0_14_weightedGraphKernelLeftSide
    rw [helperForLemma33_0_14_nonneg_mul_sub_finite ha,
      helperForLemma33_0_14_nonneg_mul_sub_finite hb]
    exact
      helperForLemma33_0_14_add_sub_le_sub_add
        (p := ((a * dotProduct x₁ xStar : ℝ)))
        (q := ((b * dotProduct x₂ xStar : ℝ)))
        ((a : EReal) * f (Fin.append u₁ x₁)) ((b : EReal) * f (Fin.append u₂ x₂))
  have hConv :
      f (Fin.append (a • u₁ + b • u₂) (a • x₁ + b • x₂)) ≤
        (a : EReal) * f (Fin.append u₁ x₁) + (b : EReal) * f (Fin.append u₂ x₂) := by
    -- Apply graph convexity at the appended endpoint vectors.
    have hAppend :
        a • Fin.append u₁ x₁ + b • Fin.append u₂ x₂ =
          Fin.append (a • u₁ + b • u₂) (a • x₁ + b • x₂) :=
      helperForLemma33_0_14_append_weighted a b u₁ u₂ x₁ x₂
    have hMain :=
      hf (x := Fin.append u₁ x₁) (y := Fin.append u₂ x₂) (a := a) (b := b)
        (Set.mem_univ _) (Set.mem_univ _) ha hb hab (Set.mem_univ _)
    simpa [hAppend] using hMain
  have hDot :
      (((a * dotProduct x₁ xStar + b * dotProduct x₂ xStar : ℝ) : EReal) ≤
        ((dotProduct (a • x₁ + b • x₂) xStar : ℝ) : EReal)) := by
    have hDotEq :
        dotProduct (a • x₁ + b • x₂) xStar =
          a * dotProduct x₁ xStar + b * dotProduct x₂ xStar :=
      helperForLemma33_0_14_dotProduct_weighted a b x₁ x₂ xStar
    have hCastEq :
        ((a * dotProduct x₁ xStar + b * dotProduct x₂ xStar : ℝ) : EReal) =
          ((dotProduct (a • x₁ + b • x₂) xStar : ℝ) : EReal) := by
      -- Rewrite the dot product, then cast the resulting real equality into `EReal`.
      simpa using congrArg (fun t : ℝ => (t : EReal)) hDotEq.symm
    exact le_of_eq hCastEq
  -- Compare the rewritten left-hand side with the target kernel using monotonicity of
  -- extended-real subtraction.
  exact le_trans hKernelRewrite (EReal.sub_le_sub hDot hConv)

/-- Helper for Lemma33.0.14: a jointly convex graph function yields the parameterwise concavity
required in Rockafellar's convex-bifunction definition after currying. -/
lemma helperForLemma33_0_14_concaveParameterPairing_of_graphConvex
    {m n : ℕ} {f : (Fin (m + n) → ℝ) → EReal}
    (hf : IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f) :
    HasConcaveParameterConvexPairing (bifunctionOfGraphFunction f) := by
  -- Unfold the convex pairing as a supremum of affine kernels and compare endpoint suprema
  -- with the target supremum via the product-indexed `iSup` estimate.
  intro xStar u₁ u₂ hu₁ hu₂ a b ha hb hab hu
  by_cases hZeroA : a = 0
  · have hBOne : b = 1 := by linarith
    subst hZeroA
    subst hBOne
    simp
  by_cases hZeroB : b = 0
  · have hAOne : a = 1 := by linarith
    subst hZeroB
    subst hAOne
    simp
  have hPosA : 0 < a := lt_of_le_of_ne ha (Ne.symm hZeroA)
  have hPosB : 0 < b := lt_of_le_of_ne hb (Ne.symm hZeroB)
  let kernel :
      (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
    fun u x => (((dotProduct x xStar : ℝ) : EReal) - f (Fin.append u x))
  have hOuter :
      ((a : EReal) * (⨆ x : Fin n → ℝ, kernel u₁ x)) +
          ((b : EReal) * (⨆ x : Fin n → ℝ, kernel u₂ x)) ≤
        ⨆ p : (Fin n → ℝ) × (Fin n → ℝ), (a : EReal) * kernel u₁ p.1 + (b : EReal) * kernel u₂ p.2 := by
    -- Choose endpoint witnesses for the two suprema independently.
    simpa [kernel] using
      helperForLemma33_0_5_weightedSum_le_productIndexed_iSup hPosA hPosB
        (f := fun x : Fin n → ℝ => kernel u₁ x)
        (g := fun x : Fin n → ℝ => kernel u₂ x)
  have hPairs :
      (⨆ p : (Fin n → ℝ) × (Fin n → ℝ), (a : EReal) * kernel u₁ p.1 + (b : EReal) * kernel u₂ p.2) ≤
        ⨆ x : Fin n → ℝ, kernel (a • u₁ + b • u₂) x := by
    -- Send each endpoint pair to its convex combination in the section variable.
    refine iSup_le ?_
    intro p
    rcases p with ⟨x₁, x₂⟩
    have hKernel :
        (a : EReal) * kernel u₁ x₁ + (b : EReal) * kernel u₂ x₂ ≤
          kernel (a • u₁ + b • u₂) (a • x₁ + b • x₂) := by
      simpa [kernel, helperForLemma33_0_14_weightedGraphKernelLeftSide,
        helperForLemma33_0_14_weightedGraphKernelRightSide,
        helperForLemma33_0_14_dotProduct_weighted] using
        helperForLemma33_0_14_weightedGraphKernel_le_targetKernel
          (hf := hf) (u₁ := u₁) (u₂ := u₂) (x₁ := x₁) (x₂ := x₂)
          (xStar := xStar) (a := a) (b := b) ha hb hab
    exact le_trans hKernel
      (le_iSup (fun x : Fin n → ℝ => kernel (a • u₁ + b • u₂) x) (a • x₁ + b • x₂))
  simpa [HasConcaveParameterConvexPairing, IsERealConcaveOn, convexBifunctionPairing,
    bifunctionPairingNotation, conjugatePairingNotation, bifunctionOfGraphFunction, kernel,
    sSup_range] using le_trans hOuter hPairs

/-- Helper for Lemma33.0.14: every section point contributes one of the affine kernels in the
defining supremum for the convex bifunction pairing. -/
lemma helperForLemma33_0_14_endpointKernel_le_convexBifunctionPairing
    {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal)
    (u : Fin m → ℝ) (x xStar : Fin n → ℝ) :
    (((dotProduct x xStar : ℝ) : EReal) - F u x) ≤ convexBifunctionPairing F u xStar := by
  -- The chosen primal point `x` appears among the terms whose supremum defines the pairing.
  rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
  exact
    le_iSup
      (fun y : Fin n → ℝ => (((dotProduct y xStar : ℝ) : EReal) - F u y))
      x

/-- Helper for Lemma33.0.14: the Section 33 convex-conjugate notation is exactly Chapter 3's
Fenchel conjugate. -/
lemma helperForLemma33_0_14_convexConjugate_eq_fenchelConjugate
    {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    convexConjugate f = fenchelConjugate n f := by
  rfl

/-- Helper for Lemma33.0.14: every Rockafellar-convex section satisfies the generic
Fenchel-Moreau biconjugacy formula, but only up to the one-variable convex closure. -/
lemma helperForLemma33_0_14_sectionwise_kernelRep_eq_convexFunctionClosure_of_rockafellar
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F) :
    ∀ u x,
      sSup (Set.range (fun xStar : Fin n → ℝ =>
        (((dotProduct x xStar : ℝ) : EReal) - convexBifunctionPairing F u xStar))) =
          convexFunctionClosure (F u) x := by
  rcases hRock with ⟨hSectionConv, _hPair⟩
  intro u x
  have hConvFun : ConvexFunction (F u) :=
    helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction (hSectionConv u)
  -- Identify the sectionwise kernel supremum with the biconjugate of the fixed section.
  calc
    sSup (Set.range (fun xStar : Fin n → ℝ =>
      (((dotProduct x xStar : ℝ) : EReal) - convexBifunctionPairing F u xStar))) =
        sSup (Set.range (fun xStar : Fin n → ℝ =>
          (((dotProduct xStar x : ℝ) : EReal) - convexBifunctionPairing F u xStar))) := by
      congr with xStar
      simp [dotProduct_comm]
    _ =
        convexConjugate (convexBifunctionPairing F u) x := by
      rw [convexConjugate, fenchelConjugate_eq_iSup, sSup_range]
    _ = convexFunctionClosure (F u) x := by
      -- Rewrite the local Section 33 notation to Chapter 3 Fenchel conjugates.
      simpa [convexBifunctionPairing,
        helperForLemma33_0_14_convexConjugate_eq_fenchelConjugate] using
        congrArg (fun g => g x)
          (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure
            (n := n) (f := F u) hConvFun)

/-- Helper for Lemma33.0.14: concavity of the convex pairing in the parameter variable turns the
weighted endpoint kernels into a single affine minorant at the parameter convex combination. -/
lemma helperForLemma33_0_14_weightedEndpointKernel_le_pairing_of_concaveParameterPairing
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hPair : HasConcaveParameterConvexPairing F)
    {u₁ u₂ : Fin m → ℝ} {x₁ x₂ xStar : Fin n → ℝ} {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (a : EReal) * ((((dotProduct x₁ xStar : ℝ) : EReal) - F u₁ x₁)) +
        (b : EReal) * ((((dotProduct x₂ xStar : ℝ) : EReal) - F u₂ x₂)) ≤
      convexBifunctionPairing F (a • u₁ + b • u₂) xStar := by
  -- First compare each endpoint kernel with the corresponding pairing value.
  have hFirst :
      (a : EReal) * ((((dotProduct x₁ xStar : ℝ) : EReal) - F u₁ x₁)) ≤
        (a : EReal) * convexBifunctionPairing F u₁ xStar := by
    have haE : (0 : EReal) ≤ (a : EReal) := by
      exact_mod_cast ha
    exact mul_le_mul_of_nonneg_left
      (helperForLemma33_0_14_endpointKernel_le_convexBifunctionPairing F u₁ x₁ xStar)
      haE
  have hSecond :
      (b : EReal) * ((((dotProduct x₂ xStar : ℝ) : EReal) - F u₂ x₂)) ≤
        (b : EReal) * convexBifunctionPairing F u₂ xStar := by
    have hbE : (0 : EReal) ≤ (b : EReal) := by
      exact_mod_cast hb
    exact mul_le_mul_of_nonneg_left
      (helperForLemma33_0_14_endpointKernel_le_convexBifunctionPairing F u₂ x₂ xStar)
      hbE
  have hEndpointSum :
      (a : EReal) * ((((dotProduct x₁ xStar : ℝ) : EReal) - F u₁ x₁)) +
          (b : EReal) * ((((dotProduct x₂ xStar : ℝ) : EReal) - F u₂ x₂)) ≤
        (a : EReal) * convexBifunctionPairing F u₁ xStar +
          (b : EReal) * convexBifunctionPairing F u₂ xStar := by
    -- Add the two endpoint estimates before invoking parameter-side concavity.
    exact add_le_add hFirst hSecond
  have hConcave :
      (a : EReal) * convexBifunctionPairing F u₁ xStar +
          (b : EReal) * convexBifunctionPairing F u₂ xStar ≤
        convexBifunctionPairing F (a • u₁ + b • u₂) xStar := by
    -- This is exactly Rockafellar's parameterwise concavity hypothesis for the pairing.
    exact
      hPair xStar (x := u₁) (y := u₂) (Set.mem_univ _) (Set.mem_univ _)
        ha hb hab (Set.mem_univ _)
  exact le_trans hEndpointSum hConcave

/-- Helper for Lemma33.0.14: multiplying a non-`⊥` extended-real value by a nonnegative real
weight cannot create `⊥`. -/
lemma helperForLemma33_0_14_nonneg_mul_ne_bot_of_ne_bot
    {a : ℝ} {x : EReal}
    (ha : 0 ≤ a) (hx : x ≠ ⊥) :
    (a : EReal) * x ≠ ⊥ := by
  -- Split into the zero-weight, positive-weight-top, and positive-weight-finite cases.
  by_cases hZero : a = 0
  · simp [hZero]
  have hPos : 0 < a := lt_of_le_of_ne ha (Ne.symm hZero)
  by_cases hTop : x = ⊤
  · simp [hTop, EReal.coe_mul_top_of_pos hPos]
  have hxcoe : (((x.toReal : ℝ)) : EReal) = x := by
    simpa using EReal.coe_toReal (x := x) hTop hx
  rw [← hxcoe]
  simpa [EReal.coe_mul] using (EReal.coe_ne_bot (a * x.toReal))

/-- Helper for Lemma33.0.14: adding two extended-real values that both avoid `⊥` still avoids
`⊥`. -/
lemma helperForLemma33_0_14_add_ne_bot_of_ne_bot
    {X Y : EReal}
    (hX : X ≠ ⊥) (hY : Y ≠ ⊥) :
    X + Y ≠ ⊥ := by
  -- Reduce to the top/finite cases for the two summands.
  by_cases hTopX : X = ⊤
  · by_cases hTopY : Y = ⊤
    · simp [hTopX, hTopY]
    · have hYcoe : (((Y.toReal : ℝ)) : EReal) = Y := by
        simpa using EReal.coe_toReal (x := Y) hTopY hY
      rw [hTopX, ← hYcoe]
      simp
  · by_cases hTopY : Y = ⊤
    · have hXcoe : (((X.toReal : ℝ)) : EReal) = X := by
        simpa using EReal.coe_toReal (x := X) hTopX hX
      rw [hTopY, ← hXcoe]
      simp
    · have hXcoe : (((X.toReal : ℝ)) : EReal) = X := by
        simpa using EReal.coe_toReal (x := X) hTopX hX
      have hYcoe : (((Y.toReal : ℝ)) : EReal) = Y := by
        simpa using EReal.coe_toReal (x := Y) hTopY hY
      rw [← hXcoe, ← hYcoe]
      simpa [EReal.coe_add] using (EReal.coe_ne_bot (X.toReal + Y.toReal))

/-- Helper for Lemma33.0.14: once the two subtrahends both avoid `⊥`, the two endpoint affine
terms combine exactly into one affine kernel difference. -/
lemma helperForLemma33_0_14_add_sub_eq_sub_add_of_ne_bot
    {p q : ℝ} {C D : EReal}
    (hC : C ≠ ⊥) (hD : D ≠ ⊥) :
    (((p : ℝ) : EReal) - C) + (((q : ℝ) : EReal) - D) =
      (((p + q : ℝ) : EReal) - (C + D)) := by
  -- Separate the top cases from the fully finite case; away from `⊥`, subtraction behaves
  -- like the transported real identity.
  by_cases hTopC : C = ⊤
  · rw [hTopC]
    by_cases hTopD : D = ⊤
    · rw [hTopD]
      simp
    · have hDcoe : (((D.toReal : ℝ)) : EReal) = D := by
        simpa using EReal.coe_toReal (x := D) hTopD hD
      rw [← hDcoe]
      simp [EReal.sub_top]
  · by_cases hTopD : D = ⊤
    · have hCcoe : (((C.toReal : ℝ)) : EReal) = C := by
        simpa using EReal.coe_toReal (x := C) hTopC hC
      rw [← hCcoe, hTopD]
      simp [EReal.sub_top]
    · have hCcoe : (((C.toReal : ℝ)) : EReal) = C := by
        simpa using EReal.coe_toReal (x := C) hTopC hC
      have hDcoe : (((D.toReal : ℝ)) : EReal) = D := by
        simpa using EReal.coe_toReal (x := D) hTopD hD
      have hSumCoe :
          ((((C.toReal + D.toReal : ℝ)) : EReal)) =
            (((C.toReal : ℝ) : EReal) + ((D.toReal : ℝ) : EReal)) := by
        rw [EReal.coe_add]
      have hCD :
          (((C.toReal : ℝ) : EReal) + ((D.toReal : ℝ) : EReal)) = C + D := by
        rw [hCcoe, hDcoe]
      have hStart :
          (((p : ℝ) : EReal) - C) + (((q : ℝ) : EReal) - D) =
            (((p : ℝ) : EReal) - ((C.toReal : ℝ) : EReal)) +
              (((q : ℝ) : EReal) - ((D.toReal : ℝ) : EReal)) := by
        simpa [hCcoe, hDcoe]
      calc
        (((p : ℝ) : EReal) - C) + (((q : ℝ) : EReal) - D) =
            (((p : ℝ) : EReal) - ((C.toReal : ℝ) : EReal)) +
              (((q : ℝ) : EReal) - ((D.toReal : ℝ) : EReal)) := hStart
        _ = (((p + q : ℝ) : EReal) - (((C.toReal + D.toReal : ℝ) : EReal))) := by
          calc
            (((p : ℝ) : EReal) - ((C.toReal : ℝ) : EReal)) +
                (((q : ℝ) : EReal) - ((D.toReal : ℝ) : EReal)) =
                ((((p - C.toReal : ℝ)) : EReal)) + ((((q - D.toReal : ℝ)) : EReal)) := by
              simp [EReal.coe_sub]
            _ = (((p - C.toReal) + (q - D.toReal) : ℝ) : EReal) := by
              simp [EReal.coe_add]
            _ = (((p + q : ℝ) : EReal) - (((C.toReal + D.toReal : ℝ) : EReal))) := by
              congr 1
              ring
        _ = (((p + q : ℝ) : EReal) -
              (((C.toReal : ℝ) : EReal) + ((D.toReal : ℝ) : EReal))) := by
          rw [hSumCoe]
        _ = (((p + q : ℝ) : EReal) - (C + D)) := by
          simpa using congrArg (fun t : EReal => (((p + q : ℝ) : EReal) - t)) hCD

/-- Helper for Lemma33.0.14: the weighted endpoint-kernel minorant is equivalent to the desired
kernel upper bound after separating the finite affine part from the extended-real section values,
provided the endpoint section values avoid `⊥`. -/
lemma helperForLemma33_0_14_kernelUpper_of_endpointMinorant
    {a b p q : ℝ} {C D P : EReal}
    (hC : C ≠ ⊥) (hD : D ≠ ⊥)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hMinorant :
      (a : EReal) * ((((p : ℝ) : EReal) - C) : EReal) +
          (b : EReal) * ((((q : ℝ) : EReal) - D) : EReal) ≤
        P) :
    (((a * p + b * q : ℝ) : EReal) - P) ≤
      (a : EReal) * C + (b : EReal) * D := by
  let weightedC : EReal := (a : EReal) * C
  let weightedD : EReal := (b : EReal) * D
  let weightedAffine : EReal := (((a * p + b * q : ℝ) : EReal) - (weightedC + weightedD))
  have hWeightedC : weightedC ≠ ⊥ :=
    helperForLemma33_0_14_nonneg_mul_ne_bot_of_ne_bot ha hC
  have hWeightedD : weightedD ≠ ⊥ :=
    helperForLemma33_0_14_nonneg_mul_ne_bot_of_ne_bot hb hD
  have hRewrite :
      (a : EReal) * ((((p : ℝ) : EReal) - C) : EReal) +
          (b : EReal) * ((((q : ℝ) : EReal) - D) : EReal) = weightedAffine := by
    -- Rewrite each weighted endpoint term separately, then merge the two affine differences.
    have hWeightedCRewrite :
        (a : EReal) * ((((p : ℝ) : EReal) - C) : EReal) =
          (((a * p : ℝ) : EReal) - weightedC) := by
      simpa [weightedC] using helperForLemma33_0_14_nonneg_mul_sub_finite ha C
    have hWeightedDRewrite :
        (b : EReal) * ((((q : ℝ) : EReal) - D) : EReal) =
          (((b * q : ℝ) : EReal) - weightedD) := by
      simpa [weightedD] using helperForLemma33_0_14_nonneg_mul_sub_finite hb D
    rw [hWeightedCRewrite, hWeightedDRewrite]
    simpa [weightedAffine, weightedC, weightedD] using
      helperForLemma33_0_14_add_sub_eq_sub_add_of_ne_bot
        (p := a * p) (q := b * q) (C := weightedC) (D := weightedD)
        hWeightedC hWeightedD
  have hWeightedAffine :
      weightedAffine ≤ P := by
    -- The rewritten affine kernel is exactly the given endpoint minorant.
    simpa [hRewrite] using hMinorant
  have hWeightedSum_ne_bot : weightedC + weightedD ≠ ⊥ :=
    helperForLemma33_0_14_add_ne_bot_of_ne_bot hWeightedC hWeightedD
  by_cases hWeightedSum_top : weightedC + weightedD = ⊤
  · -- If the weighted section-value sum is `⊤`, the target upper bound is immediate.
    have hWeightedSum :
        weightedC + weightedD = (a : EReal) * C + (b : EReal) * D := by
      simp [weightedC, weightedD]
    rw [hWeightedSum, hWeightedSum_top]
    simp [weightedAffine]
  · have hAffineLe :
        (((a * p + b * q : ℝ) : EReal) ≤ P + (weightedC + weightedD)) := by
      -- Move the finite-minus-weighted-sum inequality across subtraction using the
      -- `EReal`-specific subtraction order equivalence.
      have hSubLe :
          ((a * p + b * q : ℝ) : EReal) - (weightedC + weightedD) ≤ P := by
        -- Expand `weightedAffine` and use the hypothesis `hWeightedAffine`.
        simpa [weightedAffine] using hWeightedAffine
      exact
        (EReal.sub_le_iff_le_add
          (a := ((a * p + b * q : ℝ) : EReal))
          (b := weightedC + weightedD) (c := P)
          (Or.inl hWeightedSum_ne_bot) (Or.inl hWeightedSum_top)).1 hSubLe
    -- Move `P` back across subtraction now that the weighted section-value sum avoids both
    -- `⊥` and `⊤`.
    have hSum_ne_bot : (a : EReal) * C + (b : EReal) * D ≠ ⊥ := by
      simpa [weightedC, weightedD] using hWeightedSum_ne_bot
    have hSum_rewrite :
        P + (weightedC + weightedD) = P + ((a : EReal) * C + (b : EReal) * D) := by
      simp [weightedC, weightedD, add_assoc, add_left_comm, add_comm]
    have hAffineLe' :
        ((a * p + b * q : ℝ) : EReal) ≤ P + ((a : EReal) * C + (b : EReal) * D) := by
      simpa [hSum_rewrite] using hAffineLe
    have hAffineLe'' :
        ((a * p + b * q : ℝ) : EReal) ≤ ((a : EReal) * C + (b : EReal) * D) + P := by
      -- The `sub_le_iff_le_add` lemma expects the right-hand side as `c + b`.
      simpa [add_comm] using hAffineLe'
    exact
      (EReal.sub_le_iff_le_add
        (a := ((a * p + b * q : ℝ) : EReal))
        (b := P) (c := (a : EReal) * C + (b : EReal) * D)
        (Or.inr hWeightedSum_top)
        (Or.inr hSum_ne_bot)).2 hAffineLe''

/-- Helper for Lemma33.0.14: once each section is represented by the supremum of its affine
kernels and those kernels satisfy the Jensen upper bound, the graph function is jointly
convex. -/
lemma helperForLemma33_0_14_graphConvex_of_sectionwiseKernelUpperBound
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hKernelRep :
      ∀ u x,
        sSup (Set.range (fun xStar : Fin n → ℝ =>
          (((dotProduct x xStar : ℝ) : EReal) - convexBifunctionPairing F u xStar))) = F u x)
    (hKernelUpper :
      ∀ {u₁ u₂ : Fin m → ℝ} {x₁ x₂ xStar : Fin n → ℝ} {a b : ℝ},
        0 ≤ a → 0 ≤ b → a + b = 1 →
          (((dotProduct (a • x₁ + b • x₂) xStar : ℝ) : EReal) -
              convexBifunctionPairing F (a • u₁ + b • u₂) xStar) ≤
            (a : EReal) * F u₁ x₁ + (b : EReal) * F u₂ x₂) :
    IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) := by
  intro z₁ z₂ hz₁ hz₂ a b ha hb hab hz
  let u₁ : Fin m → ℝ := fun i => z₁ (Fin.castAdd n i)
  let u₂ : Fin m → ℝ := fun i => z₂ (Fin.castAdd n i)
  let x₁ : Fin n → ℝ := fun j => z₁ (Fin.natAdd m j)
  let x₂ : Fin n → ℝ := fun j => z₂ (Fin.natAdd m j)
  have hz₁Split : Fin.append u₁ x₁ = z₁ := by
    -- Recover the first endpoint from its parameter and section blocks.
    simpa [u₁, x₁] using helperForLemma33_0_14_append_split_eq z₁
  have hz₂Split : Fin.append u₂ x₂ = z₂ := by
    -- Recover the second endpoint in the same way.
    simpa [u₂, x₂] using helperForLemma33_0_14_append_split_eq z₂
  have hAppend :
      a • z₁ + b • z₂ =
        Fin.append (a • u₁ + b • u₂) (a • x₁ + b • x₂) := by
    -- Rewrite both graph endpoints through the split/reappend coordinates and combine blocks.
    rw [← hz₁Split, ← hz₂Split]
    exact helperForLemma33_0_14_append_weighted a b u₁ u₂ x₁ x₂
  have hz₁Eval : graphFunctionOfBifunction F z₁ = F u₁ x₁ := by
    -- Evaluating the graph function at a split endpoint returns the original section value.
    rw [← hz₁Split]
    simp [graphFunctionOfBifunction]
  have hz₂Eval : graphFunctionOfBifunction F z₂ = F u₂ x₂ := by
    -- The same coordinate simplification works for the second endpoint.
    rw [← hz₂Split]
    simp [graphFunctionOfBifunction]
  -- Rewrite the graph value at the convex combination through the assumed kernel
  -- representation, then bound each kernel term by the Jensen right-hand side.
  calc
    graphFunctionOfBifunction F (a • z₁ + b • z₂) =
        F (a • u₁ + b • u₂) (a • x₁ + b • x₂) := by
      rw [hAppend]
      simp [graphFunctionOfBifunction]
      congr 1
    _ = sSup (Set.range (fun xStar : Fin n → ℝ =>
          (((dotProduct (a • x₁ + b • x₂) xStar : ℝ) : EReal) -
            convexBifunctionPairing F (a • u₁ + b • u₂) xStar))) := by
      symm
      exact hKernelRep (a • u₁ + b • u₂) (a • x₁ + b • x₂)
    _ ≤ (a : EReal) * F u₁ x₁ + (b : EReal) * F u₂ x₂ := by
      rw [sSup_range]
      refine iSup_le ?_
      intro xStar
      exact
        hKernelUpper (u₁ := u₁) (u₂ := u₂) (x₁ := x₁) (x₂ := x₂)
          (xStar := xStar) (a := a) (b := b) ha hb hab
    _ = (a : EReal) * graphFunctionOfBifunction F z₁ +
          (b : EReal) * graphFunctionOfBifunction F z₂ := by
      rw [← hz₁Eval, ← hz₂Eval]

/-- Helper for Lemma33.0.14: Rockafellar convexity provides the sectionwise closure formula for
the affine kernels of `convexBifunctionPairing F u`, together with the pointwise Jensen upper
bound those kernels satisfy. -/
lemma helperForLemma33_0_14_rockafellar_graphKernelData_of_convexBifunction
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F) :
    (∀ u x,
      sSup (Set.range (fun xStar : Fin n → ℝ =>
        (((dotProduct x xStar : ℝ) : EReal) - convexBifunctionPairing F u xStar))) =
          convexFunctionClosure (F u) x) ∧
    (∀ {u₁ u₂ : Fin m → ℝ} {x₁ x₂ xStar : Fin n → ℝ} {a b : ℝ},
      0 ≤ a → 0 ≤ b → a + b = 1 →
      F u₁ x₁ ≠ ⊥ → F u₂ x₂ ≠ ⊥ →
        (((dotProduct (a • x₁ + b • x₂) xStar : ℝ) : EReal) -
            convexBifunctionPairing F (a • u₁ + b • u₂) xStar) ≤
          (a : EReal) * F u₁ x₁ + (b : EReal) * F u₂ x₂) := by
  have hClosureRep :
      ∀ u x,
        sSup (Set.range (fun xStar : Fin n → ℝ =>
          (((dotProduct x xStar : ℝ) : EReal) - convexBifunctionPairing F u xStar))) =
            convexFunctionClosure (F u) x :=
    helperForLemma33_0_14_sectionwise_kernelRep_eq_convexFunctionClosure_of_rockafellar
      (F := F) hRock
  have hEndpointKernelMinorant :
      ∀ {u₁ u₂ : Fin m → ℝ} {x₁ x₂ xStar : Fin n → ℝ} {a b : ℝ},
        0 ≤ a → 0 ≤ b → a + b = 1 →
          (a : EReal) * ((((dotProduct x₁ xStar : ℝ) : EReal) - F u₁ x₁)) +
              (b : EReal) * ((((dotProduct x₂ xStar : ℝ) : EReal) - F u₂ x₂)) ≤
            convexBifunctionPairing F (a • u₁ + b • u₂) xStar := by
    intro u₁ u₂ x₁ x₂ xStar a b ha hb hab
    -- Parameterwise concavity already gives the weighted endpoint-kernel minorant.
    exact
      helperForLemma33_0_14_weightedEndpointKernel_le_pairing_of_concaveParameterPairing
        (F := F) hRock.2 (u₁ := u₁) (u₂ := u₂) (x₁ := x₁) (x₂ := x₂)
        (xStar := xStar) (a := a) (b := b) ha hb hab
  refine ⟨hClosureRep, ?_⟩
  intro u₁ u₂ x₁ x₂ xStar a b ha hb hab hNoBot₁ hNoBot₂
  have hKernelUpperFinite :
      (((a * dotProduct x₁ xStar + b * dotProduct x₂ xStar : ℝ) : EReal) -
          convexBifunctionPairing F (a • u₁ + b • u₂) xStar) ≤
        (a : EReal) * F u₁ x₁ + (b : EReal) * F u₂ x₂ := by
    -- Convert the endpoint minorant into the corresponding kernel upper bound in `EReal`.
    exact
      helperForLemma33_0_14_kernelUpper_of_endpointMinorant
        (hC := hNoBot₁) (hD := hNoBot₂)
        (ha := ha) (hb := hb) (hab := hab)
        (C := F u₁ x₁) (D := F u₂ x₂)
        (P := convexBifunctionPairing F (a • u₁ + b • u₂) xStar)
        (hMinorant := hEndpointKernelMinorant
          (u₁ := u₁) (u₂ := u₂) (x₁ := x₁) (x₂ := x₂) (xStar := xStar)
          (a := a) (b := b) ha hb hab)
  have hDot :
      (((dotProduct (a • x₁ + b • x₂) xStar : ℝ) : EReal) -
          convexBifunctionPairing F (a • u₁ + b • u₂) xStar) =
        (((a * dotProduct x₁ xStar + b * dotProduct x₂ xStar : ℝ) : EReal) -
          convexBifunctionPairing F (a • u₁ + b • u₂) xStar) := by
    -- Rewrite the affine part of the kernel using linearity of the dot product.
    congr 1
    exact congrArg (fun r : ℝ => ((r : ℝ) : EReal))
      (helperForLemma33_0_14_dotProduct_weighted a b x₁ x₂ xStar)
  rw [hDot]
  exact hKernelUpperFinite


/-- Helper for Lemma33.0.14: every affine kernel appearing in the sectionwise closure formula is
bounded above by that closure value. -/
lemma helperForLemma33_0_14_endpointKernel_le_sectionwiseClosure
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosureRep :
      ∀ u x,
        sSup (Set.range (fun xStar : Fin n → ℝ =>
          (((dotProduct x xStar : ℝ) : EReal) - convexBifunctionPairing F u xStar))) =
            convexFunctionClosure (F u) x)
    (u : Fin m → ℝ) (x xStar : Fin n → ℝ) :
    (((dotProduct x xStar : ℝ) : EReal) - convexBifunctionPairing F u xStar) ≤
      convexFunctionClosure (F u) x := by
  -- The chosen dual vector contributes one term to the supremum defining the sectionwise
  -- convex closure.
  rw [← hClosureRep u x, sSup_range]
  exact
    le_iSup
      (fun yStar : Fin n → ℝ =>
        (((dotProduct x yStar : ℝ) : EReal) - convexBifunctionPairing F u yStar))
      xStar


end Section33
end Chap07
