/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part4

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-- Helper for Lemma33.0.14: every convex function agrees with its convex closure on the
relative interior of its effective domain, regardless of whether the function is proper or
improper. -/
lemma helperForLemma33_0_14_convexFunctionClosure_eq_on_ri_effectiveDomain
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f) :
    ∀ x ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
      convexFunctionClosure f x = f x := by
  let hConvFun : ConvexFunction f :=
    helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hConv
  by_cases hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f
  · intro x hxri
    -- In the proper case this is the standard Chapter 2 closure theorem on `ri (dom f)`.
    exact
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
        (f := f) hproper).2 x hxri
  · have himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
      have hConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
        simpa [ConvexFunction] using hConvFun
      exact ⟨hConvOn, hproper⟩
    intro x hxri
    -- In the improper case the closure still agrees with `f` on the same relative interior.
    exact convexFunctionClosure_agrees_on_ri_of_improper (f := f) himproper x hxri

/-- Helper for Lemma33.0.14: the same relative-interior closure identity, packaged directly for
a global convex function on `ℝ^n`. -/
lemma helperForLemma33_0_14_convexFunctionClosure_eq_on_ri_effectiveDomain_of_ConvexFunction
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hConvFun : ConvexFunction f) :
    ∀ x ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
      convexFunctionClosure f x = f x := by
  by_cases hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f
  · intro x hxri
    exact
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri
        (f := f) hproper).2 x hxri
  · have hConvOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
      simpa [ConvexFunction] using hConvFun
    have himproper : ImproperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := by
      exact ⟨hConvOn, hproper⟩
    intro x hxri
    exact convexFunctionClosure_agrees_on_ri_of_improper (f := f) himproper x hxri

/-- Helper for Lemma33.0.14: specializing the relative-interior closure identity to a fixed
section `F u` of a Rockafellar-convex bifunction. -/
lemma helperForLemma33_0_14_sectionwiseClosure_eq_raw_on_ri_effectiveDomain
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hSectionConv : IsRockafellarSectionwiseConvexBifunction F)
    (u : Fin m → ℝ) :
    ∀ x ∈
      euclideanRelativeInterior n
        ((fun x : EuclideanSpace Real (Fin n) => (x : Fin n → ℝ)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin n → ℝ)) (F u)),
      convexFunctionClosure (F u) x = F u x := by
  -- Freeze the parameter variable and invoke the one-function relative-interior closure lemma.
  exact
    helperForLemma33_0_14_convexFunctionClosure_eq_on_ri_effectiveDomain
      (hConv := hSectionConv u)

/-- Helper for Lemma33.0.14: before upgrading from the closure to the raw section value,
Rockafellar convexity already yields the mixed-point Jensen bound for the convex closure of the
mixed section. -/
lemma helperForLemma33_0_14_mixedSectionClosure_le_weightedEndpointValues_of_rockafellar
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u₁ u₂ : Fin m → ℝ} {x₁ x₂ : Fin n → ℝ} {a b : ℝ}
    (hRock : IsRockafellarConvexBifunction F)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hNoBot₁ : F u₁ x₁ ≠ ⊥) (hNoBot₂ : F u₂ x₂ ≠ ⊥) :
    convexFunctionClosure (F (a • u₁ + b • u₂)) (a • x₁ + b • x₂) ≤
      (a : EReal) * F u₁ x₁ + (b : EReal) * F u₂ x₂ := by
  rcases
      helperForLemma33_0_14_rockafellar_graphKernelData_of_convexBifunction
        (F := F) hRock with
    ⟨hClosureRep, hKernelUpper⟩
  -- Rewrite the mixed closure value through the kernel supremum and then bound every kernel
  -- term by the already-proved Jensen upper estimate.
  calc
    convexFunctionClosure (F (a • u₁ + b • u₂)) (a • x₁ + b • x₂) =
        sSup (Set.range (fun xStar : Fin n → ℝ =>
          (((dotProduct (a • x₁ + b • x₂) xStar : ℝ) : EReal) -
            convexBifunctionPairing F (a • u₁ + b • u₂) xStar))) := by
      symm
      exact hClosureRep (a • u₁ + b • u₂) (a • x₁ + b • x₂)
    _ ≤ (a : EReal) * F u₁ x₁ + (b : EReal) * F u₂ x₂ := by
      rw [sSup_range]
      refine iSup_le ?_
      intro xStar
      exact
        hKernelUpper (u₁ := u₁) (u₂ := u₂) (x₁ := x₁) (x₂ := x₂) (xStar := xStar)
          (a := a) (b := b) ha hb hab hNoBot₁ hNoBot₂

/-- Helper for Lemma33.0.14: with strictly positive weights, a weighted endpoint-value sum can
equal `⊥` only because one of the endpoint values is already `⊥`. -/
lemma helperForLemma33_0_14_positiveWeightedSectionValueSum_eq_bot_iff_endpointBot
    {a b : ℝ} {C D : EReal}
    (ha : 0 < a) (hb : 0 < b) :
    (a : EReal) * C + (b : EReal) * D = ⊥ ↔ C = ⊥ ∨ D = ⊥ := by
  have hPosA : (0 : EReal) < (a : EReal) := by
    exact_mod_cast ha
  have hPosB : (0 : EReal) < (b : EReal) := by
    exact_mod_cast hb
  constructor
  · intro hBot
    rcases (EReal.add_eq_bot_iff).1 hBot with hLeft | hRight
    · have hLeftBot : C = ⊥ := by
        rcases (EReal.mul_eq_bot ((a : EReal)) C).1 hLeft with
          hA_bot | hC_bot | hA_top | hA_neg
        · exact False.elim ((EReal.coe_ne_bot a) hA_bot.1)
        · exact hC_bot.2
        · exact False.elim ((EReal.coe_ne_top a) hA_top.1)
        · exact False.elim (not_lt_of_gt hPosA hA_neg.1)
      exact Or.inl hLeftBot
    · have hRightBot : D = ⊥ := by
        rcases (EReal.mul_eq_bot ((b : EReal)) D).1 hRight with
          hB_bot | hD_bot | hB_top | hB_neg
        · exact False.elim ((EReal.coe_ne_bot b) hB_bot.1)
        · exact hD_bot.2
        · exact False.elim ((EReal.coe_ne_top b) hB_top.1)
        · exact False.elim (not_lt_of_gt hPosB hB_neg.1)
      exact Or.inr hRightBot
  · rintro (hBot | hBot)
    · simp [hBot, EReal.coe_mul_bot_of_pos ha]
    · simp [hBot, EReal.coe_mul_bot_of_pos hb]

/-- Helper for Lemma33.0.14: if Rockafellar convexity is supplemented by exact sectionwise
closure identities, then the closure-level kernel representation already proved in this file
upgrades to the exact raw section values. -/
lemma helperForLemma33_0_14_exactSectionwiseKernelRep_of_rockafellarConvex
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hClosureExact : ∀ u x, convexFunctionClosure (F u) x = F u x) :
    ∀ u x,
      sSup (Set.range (fun xStar : Fin n → ℝ =>
        (((dotProduct x xStar : ℝ) : EReal) - convexBifunctionPairing F u xStar))) = F u x := by
  intro u x
  -- First apply the closure-level Fenchel-Moreau formula, then replace the closure by the
  -- original section value using the extra exactness hypothesis.
  calc
    sSup (Set.range (fun xStar : Fin n → ℝ =>
      (((dotProduct x xStar : ℝ) : EReal) - convexBifunctionPairing F u xStar))) =
        convexFunctionClosure (F u) x := by
      exact
        helperForLemma33_0_14_sectionwise_kernelRep_eq_convexFunctionClosure_of_rockafellar
          (F := F) hRock u x
    _ = F u x := hClosureExact u x

/-- Helper for Lemma33.0.14: once Rockafellar convexity is supplemented by exact sectionwise
closure identities and no section value equals `⊥`, the kernel argument already present in this
file yields joint convexity of the raw graph function. -/
lemma helperForLemma33_0_14_graphConvex_of_rockafellarConvex_and_exactSectionwiseClosure
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hClosureExact : ∀ u x, convexFunctionClosure (F u) x = F u x)
    (hNoBot : ∀ u x, F u x ≠ ⊥) :
    IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) := by
  rcases
      helperForLemma33_0_14_rockafellar_graphKernelData_of_convexBifunction
        (F := F) hRock with
    ⟨hClosureRep, hKernelUpper⟩
  have hKernelRepExact :
      ∀ u x,
        sSup (Set.range (fun xStar : Fin n → ℝ =>
          (((dotProduct x xStar : ℝ) : EReal) - convexBifunctionPairing F u xStar))) = F u x :=
    helperForLemma33_0_14_exactSectionwiseKernelRep_of_rockafellarConvex
      (F := F) hRock hClosureExact
  -- Replace the closure formula by the exact section values, then invoke the generic
  -- kernel-to-graph Jensen lemma.
  refine helperForLemma33_0_14_graphConvex_of_sectionwiseKernelUpperBound hKernelRepExact ?_
  · intro u₁ u₂ x₁ x₂ xStar a b ha hb hab
    -- The extra no-`⊥` hypothesis supplies the endpoint side conditions required by the
    -- previously proved kernel upper bound.
    exact
      hKernelUpper (u₁ := u₁) (u₂ := u₂) (x₁ := x₁) (x₂ := x₂) (xStar := xStar)
        (a := a) (b := b) ha hb hab (hNoBot u₁ x₁) (hNoBot u₂ x₂)

/-- Helper for Lemma33.0.14: exact sectionwise closure together with no-`⊥` section values
already proves the entire forward half of the graph-function correspondence. -/
lemma helperForLemma33_0_14_forwardHalf_of_exactSectionwiseClosure
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hClosureExact : ∀ u x, convexFunctionClosure (F u) x = F u x)
    (hNoBot : ∀ u x, F u x ≠ ⊥) :
    IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) ∧
      bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F := by
  -- The graph-convexity component is the exact-closure/no-`⊥` theorem above, and the inverse
  -- curry/uncurry identity is purely formal.
  refine ⟨?_, helperForLemma33_0_14_bifunctionOfGraphFunction_graphFunctionOfBifunction_eq F⟩
  exact
    helperForLemma33_0_14_graphConvex_of_rockafellarConvex_and_exactSectionwiseClosure
      (F := F) hRock hClosureExact hNoBot

/-- Helper for Lemma33.0.14: the strengthened exact-closure hypotheses already recover the raw
graph-convexity conclusion by extracting the first component of the packaged forward-half
statement. -/
lemma helperForLemma33_0_14_graphConvex_of_rockafellar_with_exactSectionwiseClosure
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hClosureExact : ∀ u x, convexFunctionClosure (F u) x = F u x)
    (hNoBot : ∀ u x, F u x ≠ ⊥) :
    IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) := by
  -- Extract the graph-convexity component from the already-proved strengthened forward half.
  exact
    (helperForLemma33_0_14_forwardHalf_of_exactSectionwiseClosure
      (F := F) hRock hClosureExact hNoBot).1

/-- Helper for Lemma33.0.14: a jointly convex graph function already yields the full backward
half of the graph-function correspondence after currying. -/
lemma helperForLemma33_0_14_backwardHalf_of_graphConvex
    {m n : ℕ}
    {f : (Fin (m + n) → ℝ) → EReal}
    (hf : IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f) :
    IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
      graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f := by
  -- The backward direction follows the textbook route: first restrict graph convexity to each
  -- section, then transfer the affine-kernel Jensen estimate to parameterwise concavity of the
  -- convex pairing, and finally use the formal split/reappend identity.
  refine ⟨?_, helperForLemma33_0_14_graphFunctionOfBifunction_bifunctionOfGraphFunction_eq f⟩
  exact ⟨helperForLemma33_0_14_sectionwiseConvex_of_graphConvex hf,
    helperForLemma33_0_14_concaveParameterPairing_of_graphConvex hf⟩

/-- Helper for Lemma33.0.14: if two graph points have value `0` but their midpoint has value
`⊤`, then the graph function cannot satisfy Jensen's inequality. -/
lemma helperForLemma33_0_14_graphNotConvex_of_midpointTop
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {u₁ u₂ : Fin m → ℝ} {x : Fin n → ℝ}
    (hLeft : F u₁ x = 0)
    (hRight : F u₂ x = 0)
    (hMid : F ((1 / 2 : ℝ) • u₁ + (1 / 2 : ℝ) • u₂) x = ⊤) :
    ¬ IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) := by
  intro hConv
  have hHalfNonneg : 0 ≤ (1 / 2 : ℝ) := by
    norm_num
  have hHalfAdd : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by
    norm_num
  have hJensen :=
    hConv (x := Fin.append u₁ x) (y := Fin.append u₂ x)
      (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (Set.mem_univ _) (Set.mem_univ _) hHalfNonneg hHalfNonneg hHalfAdd (Set.mem_univ _)
  have hAppend :
      (1 / 2 : ℝ) • Fin.append u₁ x + (1 / 2 : ℝ) • Fin.append u₂ x =
        Fin.append ((1 / 2 : ℝ) • u₁ + (1 / 2 : ℝ) • u₂) x := by
    have hMidSection : ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x) = x := by
      -- Averaging a section point with itself leaves it unchanged.
      funext i
      simp
      ring
    -- The graph midpoint keeps the section coordinate fixed because the two section endpoints
    -- coincide.
    calc
      (1 / 2 : ℝ) • Fin.append u₁ x + (1 / 2 : ℝ) • Fin.append u₂ x =
          Fin.append ((1 / 2 : ℝ) • u₁ + (1 / 2 : ℝ) • u₂)
            ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • x) := by
        simpa using
          helperForLemma33_0_14_append_weighted (1 / 2 : ℝ) (1 / 2 : ℝ) u₁ u₂ x x
      _ = Fin.append ((1 / 2 : ℝ) • u₁ + (1 / 2 : ℝ) • u₂) x := by
        rw [hMidSection]
  have hLeftEval : graphFunctionOfBifunction F (Fin.append u₁ x) = 0 := by
    -- Each endpoint graph value is just the corresponding section value.
    simpa [graphFunctionOfBifunction] using hLeft
  have hRightEval : graphFunctionOfBifunction F (Fin.append u₂ x) = 0 := by
    -- The second endpoint simplifies in the same way.
    simpa [graphFunctionOfBifunction] using hRight
  have hMidEval :
      graphFunctionOfBifunction F (Fin.append ((1 / 2 : ℝ) • u₁ + (1 / 2 : ℝ) • u₂) x) = ⊤ := by
    -- The midpoint graph value is the prescribed midpoint section value.
    simpa [graphFunctionOfBifunction] using hMid
  have hImpossible : ((⊤ : EReal) ≤ (0 : EReal)) := by
    -- Jensen would force the midpoint value `⊤` to lie below the weighted average `0`.
    rw [hAppend, hMidEval, hLeftEval, hRightEval] at hJensen
    simpa using hJensen
  simp at hImpossible

/-- Helper for Lemma33.0.14: Agent C's one-dimensional boundary-value counterexample keeps the
closed interval `[0, 1]` away from the parameter `u = 0`, but removes the boundary point `0`
exactly at `u = 0`. -/
noncomputable def helperForLemma33_0_14_boundaryCounterexample :
    (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal :=
  fun u x =>
    if u 0 = 0 then
      if 0 < x 0 ∧ x 0 ≤ 1 then 0 else ⊤
    else
      if 0 ≤ x 0 ∧ x 0 ≤ 1 then 0 else ⊤

/-- Helper for Lemma33.0.14: the left endpoint section in the boundary-value counterexample
contains the boundary point `0`. -/
lemma helperForLemma33_0_14_boundaryCounterexample_leftValue :
    helperForLemma33_0_14_boundaryCounterexample
      (fun _ : Fin 1 => (-1 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) = 0 := by
  -- Away from `u = 0` the counterexample uses the closed interval `[0, 1]`.
  simp [helperForLemma33_0_14_boundaryCounterexample]

/-- Helper for Lemma33.0.14: the right endpoint section in the boundary-value counterexample
also contains the boundary point `0`. -/
lemma helperForLemma33_0_14_boundaryCounterexample_rightValue :
    helperForLemma33_0_14_boundaryCounterexample
      (fun _ : Fin 1 => (1 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) = 0 := by
  -- The same closed-interval section appears at the parameter `u = 1`.
  simp [helperForLemma33_0_14_boundaryCounterexample]

/-- Helper for Lemma33.0.14: at the midpoint parameter `u = 0`, the boundary point `0` is
deleted from the section and the section value jumps to `⊤`. -/
lemma helperForLemma33_0_14_boundaryCounterexample_midpointValue :
    helperForLemma33_0_14_boundaryCounterexample
      (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ)) = ⊤ := by
  -- The midpoint section is `(0, 1]`, so the boundary point `0` is excluded.
  simp [helperForLemma33_0_14_boundaryCounterexample]

/-- Helper for Lemma33.0.14: the exceptional section at `u = 0` is the half-open interval
`(0, 1]` viewed inside `Fin 1 → ℝ`. -/
def helperForLemma33_0_14_boundaryCounterexample_openSection : Set (Fin 1 → ℝ) :=
  {x | 0 < x 0 ∧ x 0 ≤ 1}

/-- Helper for Lemma33.0.14: every nonzero parameter section in the counterexample is the
closed interval `[0, 1]` viewed inside `Fin 1 → ℝ`. -/
def helperForLemma33_0_14_boundaryCounterexample_closedSection : Set (Fin 1 → ℝ) :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ 1}

/-- Helper for Lemma33.0.14: the half-open section `(0, 1]` is nonempty. -/
lemma helperForLemma33_0_14_boundaryCounterexample_openSection_nonempty :
    (helperForLemma33_0_14_boundaryCounterexample_openSection).Nonempty := by
  -- The midpoint `1 / 2` lies in the interval `(0, 1]`.
  refine ⟨fun _ => (1 / 2 : ℝ), ?_⟩
  constructor <;> norm_num [helperForLemma33_0_14_boundaryCounterexample_openSection]

/-- Helper for Lemma33.0.14: the closed section `[0, 1]` is nonempty. -/
lemma helperForLemma33_0_14_boundaryCounterexample_closedSection_nonempty :
    (helperForLemma33_0_14_boundaryCounterexample_closedSection).Nonempty := by
  -- The boundary point `0` already lies in the closed interval.
  refine ⟨0, ?_⟩
  constructor <;> simp [helperForLemma33_0_14_boundaryCounterexample_closedSection]

/-- Helper for Lemma33.0.14: the exceptional half-open section `(0, 1]` is convex. -/
lemma helperForLemma33_0_14_boundaryCounterexample_openSection_convex :
    Convex ℝ helperForLemma33_0_14_boundaryCounterexample_openSection := by
  intro x hx y hy a b ha hb hab
  -- Both endpoint inequalities are preserved by convex combinations in one dimension.
  constructor
  · have hPos :
        0 < a * x 0 + b * y 0 := by
        by_cases ha0 : a = 0
        · have hBOne : b = 1 := by
            linarith
          subst ha0
          subst hBOne
          simpa using hy.1
        · have hAPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
          have hFirst : 0 < a * x 0 := mul_pos hAPos hx.1
          have hSecond : 0 ≤ b * y 0 := mul_nonneg hb (le_of_lt hy.1)
          linarith
    simpa [helperForLemma33_0_14_boundaryCounterexample_openSection, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul] using hPos
  · simp [helperForLemma33_0_14_boundaryCounterexample_openSection, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    nlinarith [hx.2, hy.2]

/-- Helper for Lemma33.0.14: the closed section `[0, 1]` is convex. -/
lemma helperForLemma33_0_14_boundaryCounterexample_closedSection_convex :
    Convex ℝ helperForLemma33_0_14_boundaryCounterexample_closedSection := by
  intro x hx y hy a b ha hb hab
  -- The closed interval inequalities are also stable under convex combinations.
  constructor
  · simp [helperForLemma33_0_14_boundaryCounterexample_closedSection, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    nlinarith [hx.1, hy.1]
  · simp [helperForLemma33_0_14_boundaryCounterexample_closedSection, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    nlinarith [hx.2, hy.2]

/-- Helper for Lemma33.0.14: at the exceptional parameter `u = 0`, the section is exactly the
indicator of the half-open interval `(0, 1]`. -/
lemma helperForLemma33_0_14_boundaryCounterexample_section_eq_indicator_open
    (u : Fin 1 → ℝ) (hu : u 0 = 0) :
    helperForLemma33_0_14_boundaryCounterexample u =
      indicatorFunction helperForLemma33_0_14_boundaryCounterexample_openSection := by
  -- Unfolding the section definition matches the indicator of `(0, 1]` pointwise.
  funext x
  simp [helperForLemma33_0_14_boundaryCounterexample, hu,
    helperForLemma33_0_14_boundaryCounterexample_openSection, indicatorFunction]

/-- Helper for Lemma33.0.14: away from the exceptional parameter `u = 0`, each section is
exactly the indicator of the closed interval `[0, 1]`. -/
lemma helperForLemma33_0_14_boundaryCounterexample_section_eq_indicator_closed
    (u : Fin 1 → ℝ) (hu : u 0 ≠ 0) :
    helperForLemma33_0_14_boundaryCounterexample u =
      indicatorFunction helperForLemma33_0_14_boundaryCounterexample_closedSection := by
  -- Unfolding the nonexceptional branch matches the indicator of `[0, 1]` pointwise.
  funext x
  simp [helperForLemma33_0_14_boundaryCounterexample, hu,
    helperForLemma33_0_14_boundaryCounterexample_closedSection, indicatorFunction]

/-- Helper for Lemma33.0.14: every section of the counterexample is convex in the section
variable. -/
lemma helperForLemma33_0_14_boundaryCounterexample_sectionwiseConvex :
    IsRockafellarSectionwiseConvexBifunction
      helperForLemma33_0_14_boundaryCounterexample := by
  intro u
  by_cases hu : u 0 = 0
  · have hEq :
        helperForLemma33_0_14_boundaryCounterexample u =
          indicatorFunction helperForLemma33_0_14_boundaryCounterexample_openSection :=
      helperForLemma33_0_14_boundaryCounterexample_section_eq_indicator_open u hu
    have hConvFun :
        ConvexFunction
          (indicatorFunction helperForLemma33_0_14_boundaryCounterexample_openSection) := by
      -- The indicator of a nonempty convex set is a proper convex function.
      have hProper := section16_properConvexFunctionOn_indicatorFunction_univ
        (n := 1)
        helperForLemma33_0_14_boundaryCounterexample_openSection_convex
        helperForLemma33_0_14_boundaryCounterexample_openSection_nonempty
      simpa [ConvexFunction] using hProper.1
    have hNoBot :
        ∀ x : Fin 1 → ℝ,
          indicatorFunction helperForLemma33_0_14_boundaryCounterexample_openSection x ≠ ⊥ := by
      -- Indicator functions only take the values `0` and `⊤`.
      intro x
      by_cases hx : x ∈ helperForLemma33_0_14_boundaryCounterexample_openSection
      · simp [indicatorFunction, hx]
      · simp [indicatorFunction, hx]
    -- Convert the convex-function package back to the Jensen predicate used in Section 33.
    simpa [hEq] using
      helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ hConvFun hNoBot
  · have hEq :
        helperForLemma33_0_14_boundaryCounterexample u =
          indicatorFunction helperForLemma33_0_14_boundaryCounterexample_closedSection :=
      helperForLemma33_0_14_boundaryCounterexample_section_eq_indicator_closed u hu
    have hConvFun :
        ConvexFunction
          (indicatorFunction helperForLemma33_0_14_boundaryCounterexample_closedSection) := by
      -- The same indicator-function argument applies to the closed interval `[0, 1]`.
      have hProper := section16_properConvexFunctionOn_indicatorFunction_univ
        (n := 1)
        helperForLemma33_0_14_boundaryCounterexample_closedSection_convex
        helperForLemma33_0_14_boundaryCounterexample_closedSection_nonempty
      simpa [ConvexFunction] using hProper.1
    have hNoBot :
        ∀ x : Fin 1 → ℝ,
          indicatorFunction helperForLemma33_0_14_boundaryCounterexample_closedSection x ≠ ⊥ := by
      -- Indicators of sets never attain `⊥`.
      intro x
      by_cases hx : x ∈ helperForLemma33_0_14_boundaryCounterexample_closedSection
      · simp [indicatorFunction, hx]
      · simp [indicatorFunction, hx]
    -- Again translate convexity of the indicator function into the local Jensen inequality.
    simpa [hEq] using
      helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ hConvFun hNoBot

/-- Helper for Lemma33.0.14: although the exceptional section omits the boundary point `0`,
that point still lies in the closure of `(0, 1]`. -/
lemma helperForLemma33_0_14_boundaryCounterexample_zero_mem_closure_openSection :
    (0 : Fin 1 → ℝ) ∈ closure helperForLemma33_0_14_boundaryCounterexample_openSection := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- Use the positive point `min (ε / 2) 1` to approach `0` from inside `(0, 1]`.
  refine ⟨fun _ : Fin 1 => min (ε / 2) (1 : ℝ), ?_, ?_⟩
  · constructor
    · have hHalf : 0 < ε / 2 := by
        linarith
      exact lt_min hHalf zero_lt_one
    · exact min_le_right _ _
  · simp
    have hHalfNonneg : 0 ≤ ε / 2 := by
      linarith
    have hNonneg : 0 ≤ min (ε / 2) (1 : ℝ) := by
      exact le_min hHalfNonneg zero_le_one
    rw [abs_of_nonneg hNonneg]
    have hMinLe : min (ε / 2) (1 : ℝ) ≤ ε / 2 := min_le_left _ _
    linarith

/-- Helper for Lemma33.0.14: at the exceptional parameter `u = 0`, the convex closure of the
deleted-boundary section restores the missing endpoint and therefore takes the value `0` there. -/
lemma helperForLemma33_0_14_boundaryCounterexample_midpointClosureValue :
    convexFunctionClosure
        (helperForLemma33_0_14_boundaryCounterexample (fun _ : Fin 1 => (0 : ℝ)))
        (fun _ : Fin 1 => (0 : ℝ)) = 0 := by
  -- Rewrite the exceptional section as the indicator of `(0, 1]`.
  rw [helperForLemma33_0_14_boundaryCounterexample_section_eq_indicator_open
    (u := fun _ : Fin 1 => (0 : ℝ)) rfl]
  -- The convex closure of an indicator is the indicator of the closure, provided the set is
  -- convex and nonempty.
  rw [section16_convexFunctionClosure_indicatorFunction_eq_indicatorFunction_closure
    (C := helperForLemma33_0_14_boundaryCounterexample_openSection)
    helperForLemma33_0_14_boundaryCounterexample_openSection_convex
    helperForLemma33_0_14_boundaryCounterexample_openSection_nonempty]
  -- The missing boundary point belongs to the closure, so the indicator there is `0`.
  have hZeroMem :
      (fun _ : Fin 1 => (0 : ℝ)) ∈
        closure helperForLemma33_0_14_boundaryCounterexample_openSection := by
    simpa using helperForLemma33_0_14_boundaryCounterexample_zero_mem_closure_openSection
  simp [indicatorFunction, hZeroMem]

/-- Helper for Lemma33.0.14: the boundary-value counterexample fails the exact sectionwise-closure
hypothesis precisely at the deleted midpoint boundary point. -/
lemma helperForLemma33_0_14_boundaryCounterexample_exactSectionwiseClosureFails :
    ¬ ∀ u x, convexFunctionClosure (helperForLemma33_0_14_boundaryCounterexample u) x =
      helperForLemma33_0_14_boundaryCounterexample u x := by
  intro hExact
  -- Evaluating exactness at the exceptional parameter `u = 0` and boundary point `x = 0`
  -- forces `0 = ⊤`, contradicting the explicit midpoint computations above.
  have hBad : (0 : EReal) = ⊤ := by
    simpa [helperForLemma33_0_14_boundaryCounterexample_midpointClosureValue,
      helperForLemma33_0_14_boundaryCounterexample_midpointValue] using
      hExact (fun _ : Fin 1 => (0 : ℝ)) (fun _ : Fin 1 => (0 : ℝ))
  have hZeroNotTop : (0 : EReal) ≠ ⊤ := by
    simp
  exact hZeroNotTop hBad

/-- Helper for Lemma33.0.14: the boundary-value counterexample never takes the value `⊥`, so
the failure of the repaired forward route comes from missing exact closure rather than from a
bottom-value pathology. -/
lemma helperForLemma33_0_14_boundaryCounterexample_ne_bot :
    ∀ u x, helperForLemma33_0_14_boundaryCounterexample u x ≠ ⊥ := by
  intro u x
  -- Unfolding the counterexample shows that every section value is either `0` or `⊤`.
  by_cases hu0 : u 0 = 0
  · by_cases hxOpen : 0 < x 0 ∧ x 0 ≤ 1
    · simp [helperForLemma33_0_14_boundaryCounterexample, hu0, hxOpen]
    · simp [helperForLemma33_0_14_boundaryCounterexample, hu0, hxOpen]
  · by_cases hxClosed : 0 ≤ x 0 ∧ x 0 ≤ 1
    · simp [helperForLemma33_0_14_boundaryCounterexample, hu0, hxClosed]
    · simp [helperForLemma33_0_14_boundaryCounterexample, hu0, hxClosed]

/-- Helper for Lemma33.0.14: the support function of `(0, 1]` agrees with that of `[0, 1]`;
the missing boundary point contributes only the vector `0`, whose support value is already
captured in the closure. -/
lemma helperForLemma33_0_14_boundaryCounterexample_supportFunction_open_eq_closed :
    supportFunctionEReal helperForLemma33_0_14_boundaryCounterexample_openSection =
      supportFunctionEReal helperForLemma33_0_14_boundaryCounterexample_closedSection := by
  funext xStar
  apply le_antisymm
  · unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hxOpen, rfl⟩
    -- Any point of `(0, 1]` is automatically a point of `[0, 1]`.
    exact le_sSup ⟨x, ⟨le_of_lt hxOpen.1, hxOpen.2⟩, rfl⟩
  · unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hxClosed, rfl⟩
    by_cases hx0 : x 0 = 0
    · have hxZero : x = 0 := by
        -- In `Fin 1`, vanishing of the unique coordinate forces the whole vector to be zero.
        funext i
        fin_cases i
        simpa [hx0]
      have hSupportNonneg :
          (0 : EReal) ≤
            supportFunctionEReal helperForLemma33_0_14_boundaryCounterexample_openSection xStar :=
        section16_supportFunctionEReal_nonneg_of_zero_mem_closure
          (C := helperForLemma33_0_14_boundaryCounterexample_openSection)
          helperForLemma33_0_14_boundaryCounterexample_openSection_convex
          helperForLemma33_0_14_boundaryCounterexample_openSection_nonempty
          helperForLemma33_0_14_boundaryCounterexample_zero_mem_closure_openSection xStar
      -- The only extra closed-section point is `0`, and its support contribution is `0`.
      rw [hxZero]
      simpa using hSupportNonneg
    · have hxOpen : x ∈ helperForLemma33_0_14_boundaryCounterexample_openSection := by
        -- Any closed-section point with nonzero coordinate is actually inside `(0, 1]`.
        exact ⟨lt_of_le_of_ne hxClosed.1 (Ne.symm hx0), hxClosed.2⟩
      exact le_sSup ⟨x, hxOpen, rfl⟩

/-- Helper for Lemma33.0.14: the support function of the closed interval `[0, 1]` is the finite
scalar function `x^* ↦ max (0, x^*)` in one dimension. -/
lemma helperForLemma33_0_14_boundaryCounterexample_closedSupport_eq_max
    (xStar : Fin 1 → ℝ) :
    supportFunctionEReal helperForLemma33_0_14_boundaryCounterexample_closedSection xStar =
      ((max 0 (xStar 0) : ℝ) : EReal) := by
  apply le_antisymm
  · unfold supportFunctionEReal
    refine sSup_le ?_
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hDot : dotProduct x xStar = x 0 * xStar 0 := by
      simp [dotProduct]
    rw [hDot]
    exact_mod_cast by
      by_cases hSign : 0 ≤ xStar 0
      · have hMulLe : x 0 * xStar 0 ≤ 1 * xStar 0 := by
          nlinarith [hx.2, hSign]
        have hRight : xStar 0 ≤ max 0 (xStar 0) := le_max_right _ _
        nlinarith
      · have hSign' : xStar 0 < 0 := lt_of_not_ge hSign
        have hMulLeZero : x 0 * xStar 0 ≤ 0 := by
          nlinarith [hx.1, hSign']
        have hZeroLeMax : 0 ≤ max 0 (xStar 0) := le_max_left _ _
        linarith
  · by_cases hSign : 0 ≤ xStar 0
    · let x : Fin 1 → ℝ := fun _ => 1
      have hx : x ∈ helperForLemma33_0_14_boundaryCounterexample_closedSection := by
        constructor <;> simp [x, helperForLemma33_0_14_boundaryCounterexample_closedSection]
      unfold supportFunctionEReal
      have hxMem :
          (((dotProduct x xStar : ℝ)) : EReal) ∈
            {z : EReal |
              ∃ y ∈ helperForLemma33_0_14_boundaryCounterexample_closedSection,
                z = ((dotProduct y xStar : ℝ) : EReal)} := ⟨x, hx, rfl⟩
      -- When `x^* ≥ 0`, the endpoint `x = 1` attains the support value.
      calc
        ((max 0 (xStar 0) : ℝ) : EReal) = ((xStar 0 : ℝ) : EReal) := by
          simp [max_eq_right hSign]
        _ = (((dotProduct x xStar : ℝ)) : EReal) := by
          simp [x, dotProduct]
        _ ≤ sSup {z : EReal |
              ∃ y ∈ helperForLemma33_0_14_boundaryCounterexample_closedSection,
                z = ((dotProduct y xStar : ℝ) : EReal)} := le_sSup hxMem
    · let x : Fin 1 → ℝ := 0
      have hx : x ∈ helperForLemma33_0_14_boundaryCounterexample_closedSection := by
        constructor <;> simp [x, helperForLemma33_0_14_boundaryCounterexample_closedSection]
      unfold supportFunctionEReal
      have hxMem :
          (((dotProduct x xStar : ℝ)) : EReal) ∈
            {z : EReal |
              ∃ y ∈ helperForLemma33_0_14_boundaryCounterexample_closedSection,
                z = ((dotProduct y xStar : ℝ) : EReal)} := ⟨x, hx, rfl⟩
      -- When `x^* < 0`, the endpoint `x = 0` attains the support value `0`.
      calc
        ((max 0 (xStar 0) : ℝ) : EReal) = (0 : EReal) := by
          simp [max_eq_left (le_of_not_ge hSign)]
        _ = (((dotProduct x xStar : ℝ)) : EReal) := by
          simp [x, dotProduct]
        _ ≤ sSup {z : EReal |
              ∃ y ∈ helperForLemma33_0_14_boundaryCounterexample_closedSection,
                z = ((dotProduct y xStar : ℝ) : EReal)} := le_sSup hxMem

/-- Helper for Lemma33.0.14: the convex pairing of the boundary-value counterexample is the
support function of the closed interval `[0, 1]`, hence it does not depend on the parameter
`u` at all. -/
lemma helperForLemma33_0_14_boundaryCounterexample_pairing_eq_closedSupport
    (u xStar : Fin 1 → ℝ) :
    convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample u xStar =
      supportFunctionEReal helperForLemma33_0_14_boundaryCounterexample_closedSection xStar := by
  by_cases hu : u 0 = 0
  · have hEq :
        helperForLemma33_0_14_boundaryCounterexample u =
          indicatorFunction helperForLemma33_0_14_boundaryCounterexample_openSection :=
      helperForLemma33_0_14_boundaryCounterexample_section_eq_indicator_open u hu
    -- At `u = 0`, rewrite the section as the indicator of `(0, 1]` and identify its conjugate
    -- with the corresponding support function.
    calc
      convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample u xStar =
          convexConjugate
            (indicatorFunction helperForLemma33_0_14_boundaryCounterexample_openSection) xStar := by
        simp [convexBifunctionPairing, bifunctionPairingNotation, convexConjugate, hEq]
      _ =
          fenchelConjugate 1
            (indicatorFunction helperForLemma33_0_14_boundaryCounterexample_openSection) xStar := by
        simpa using congrArg (fun g => g xStar)
          (helperForLemma33_0_14_convexConjugate_eq_fenchelConjugate
            (f := indicatorFunction helperForLemma33_0_14_boundaryCounterexample_openSection))
      _ =
          supportFunctionEReal helperForLemma33_0_14_boundaryCounterexample_openSection xStar := by
        simpa using congrArg (fun g => g xStar)
          (section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal
            (C := helperForLemma33_0_14_boundaryCounterexample_openSection))
      _ =
          supportFunctionEReal helperForLemma33_0_14_boundaryCounterexample_closedSection xStar := by
        simpa using congrArg (fun g => g xStar)
          helperForLemma33_0_14_boundaryCounterexample_supportFunction_open_eq_closed
  · have hEq :
        helperForLemma33_0_14_boundaryCounterexample u =
          indicatorFunction helperForLemma33_0_14_boundaryCounterexample_closedSection :=
      helperForLemma33_0_14_boundaryCounterexample_section_eq_indicator_closed u hu
    -- Away from `u = 0`, the section is already the indicator of `[0, 1]`.
    calc
      convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample u xStar =
          convexConjugate
            (indicatorFunction helperForLemma33_0_14_boundaryCounterexample_closedSection) xStar := by
        simp [convexBifunctionPairing, bifunctionPairingNotation, convexConjugate, hEq]
      _ =
          fenchelConjugate 1
            (indicatorFunction helperForLemma33_0_14_boundaryCounterexample_closedSection) xStar := by
        simpa using congrArg (fun g => g xStar)
          (helperForLemma33_0_14_convexConjugate_eq_fenchelConjugate
            (f := indicatorFunction helperForLemma33_0_14_boundaryCounterexample_closedSection))
      _ =
          supportFunctionEReal helperForLemma33_0_14_boundaryCounterexample_closedSection xStar := by
        simpa using congrArg (fun g => g xStar)
          (section13_fenchelConjugate_indicatorFunction_eq_supportFunctionEReal
            (C := helperForLemma33_0_14_boundaryCounterexample_closedSection))

/-- Helper for Lemma33.0.14: because the convex pairing of the boundary-value counterexample is
independent of `u`, it is automatically concave in the parameter variable. -/
lemma helperForLemma33_0_14_boundaryCounterexample_concaveParameterPairing :
    HasConcaveParameterConvexPairing helperForLemma33_0_14_boundaryCounterexample := by
  intro xStar u₁ u₂ hu₁ hu₂ a b ha hb hab hu
  let r : ℝ := max 0 (xStar 0)
  have hu₁Eq :
      convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample u₁ xStar =
        ((r : ℝ) : EReal) := by
    calc
      convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample u₁ xStar =
          supportFunctionEReal helperForLemma33_0_14_boundaryCounterexample_closedSection xStar := by
        exact helperForLemma33_0_14_boundaryCounterexample_pairing_eq_closedSupport u₁ xStar
      _ = ((r : ℝ) : EReal) := by
        simp [r, helperForLemma33_0_14_boundaryCounterexample_closedSupport_eq_max]
  have hu₂Eq :
      convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample u₂ xStar =
        ((r : ℝ) : EReal) := by
    calc
      convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample u₂ xStar =
          supportFunctionEReal helperForLemma33_0_14_boundaryCounterexample_closedSection xStar := by
        exact helperForLemma33_0_14_boundaryCounterexample_pairing_eq_closedSupport u₂ xStar
      _ = ((r : ℝ) : EReal) := by
        simp [r, helperForLemma33_0_14_boundaryCounterexample_closedSupport_eq_max]
  have huEq :
      convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample
          (a • u₁ + b • u₂) xStar = ((r : ℝ) : EReal) := by
    calc
      convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample
          (a • u₁ + b • u₂) xStar =
          supportFunctionEReal helperForLemma33_0_14_boundaryCounterexample_closedSection xStar := by
        exact
          helperForLemma33_0_14_boundaryCounterexample_pairing_eq_closedSupport
            (a • u₁ + b • u₂) xStar
      _ = ((r : ℝ) : EReal) := by
        simp [r, helperForLemma33_0_14_boundaryCounterexample_closedSupport_eq_max]
  -- Once the three pairing values are identified with the same finite constant `r`, Jensen
  -- reduces to the scalar identity `(a + b) * r = r`.
  calc
    (a : EReal) *
          convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample u₁ xStar +
        (b : EReal) *
          convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample u₂ xStar =
        (a : EReal) * (((r : ℝ) : EReal)) + (b : EReal) * (((r : ℝ) : EReal)) := by
      rw [hu₁Eq, hu₂Eq]
    _ = ((r : ℝ) : EReal) := by
      calc
        (a : EReal) * (((r : ℝ) : EReal)) + (b : EReal) * (((r : ℝ) : EReal)) =
            (((a * r : ℝ)) : EReal) + (((b * r : ℝ)) : EReal) := by
          simp [EReal.coe_mul]
        _ = (((a * r + b * r : ℝ)) : EReal) := by
          rw [← EReal.coe_add]
        _ = ((r : ℝ) : EReal) := by
          congr 1
          calc
            a * r + b * r = (a + b) * r := by ring
            _ = r := by simp [hab]
    _ = convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample
          (a • u₁ + b • u₂) xStar := huEq.symm
    _ ≤
        (fun u => convexBifunctionPairing helperForLemma33_0_14_boundaryCounterexample u xStar)
          (a • u₁ + b • u₂) := le_rfl

/-- Helper for Lemma33.0.14: the one-dimensional boundary-value witness is genuinely
Rockafellar-convex even though its raw graph function is not convex. -/
lemma helperForLemma33_0_14_boundaryCounterexample_isRockafellarConvex :
    IsRockafellarConvexBifunction helperForLemma33_0_14_boundaryCounterexample := by
  -- Package the sectionwise convexity and parameterwise pairing concavity proved above.
  exact ⟨helperForLemma33_0_14_boundaryCounterexample_sectionwiseConvex,
    helperForLemma33_0_14_boundaryCounterexample_concaveParameterPairing⟩

/-- Helper for Lemma33.0.14: the boundary-value witness already satisfies Rockafellar
convexity and the tempting global no-`⊥` repair, while still failing the exact
sectionwise-closure identity that the working repaired theorem actually needs. -/
lemma helperForLemma33_0_14_boundaryCounterexample_has_noBot_but_lacks_exactSectionwiseClosure :
    IsRockafellarConvexBifunction helperForLemma33_0_14_boundaryCounterexample ∧
      (∀ u x, helperForLemma33_0_14_boundaryCounterexample u x ≠ ⊥) ∧
      ¬ ∀ u x,
        convexFunctionClosure (helperForLemma33_0_14_boundaryCounterexample u) x =
          helperForLemma33_0_14_boundaryCounterexample u x := by
  constructor
  · -- The witness already has Rockafellar's two defining properties.
    exact helperForLemma33_0_14_boundaryCounterexample_isRockafellarConvex
  constructor
  · -- The witness never takes the value `⊥`, so the no-`⊥` pivot alone cannot be the
    -- missing hypothesis in the failed forward bridge.
    exact helperForLemma33_0_14_boundaryCounterexample_ne_bot
  · -- The same witness still breaks the exact sectionwise-closure identity at the midpoint
    -- section, which isolates the additional hypothesis used by the repaired theorem.
    exact helperForLemma33_0_14_boundaryCounterexample_exactSectionwiseClosureFails

/-- Helper for Lemma33.0.14: for the explicit boundary-value witness itself, the tempting
global no-`⊥` repair still does not force the exact sectionwise-closure identity needed by the
working forward theorem. -/
lemma helperForLemma33_0_14_boundaryCounterexample_noBot_doesNotForce_exactSectionwiseClosure :
    ¬ (
      (∀ u x, helperForLemma33_0_14_boundaryCounterexample u x ≠ ⊥) →
        ∀ u x,
          convexFunctionClosure (helperForLemma33_0_14_boundaryCounterexample u) x =
            helperForLemma33_0_14_boundaryCounterexample u x) := by
  intro hExactFromNoBot
  -- Apply the hypothetical no-`⊥` implication to the witness's already established
  -- non-`⊥` property.
  have hClosureExact :
      ∀ u x,
        convexFunctionClosure (helperForLemma33_0_14_boundaryCounterexample u) x =
          helperForLemma33_0_14_boundaryCounterexample u x :=
    hExactFromNoBot helperForLemma33_0_14_boundaryCounterexample_ne_bot
  -- The midpoint closure computation for the witness contradicts this exactness claim.
  exact helperForLemma33_0_14_boundaryCounterexample_exactSectionwiseClosureFails hClosureExact

/-- Helper for Lemma33.0.14: even after excluding `⊥`-valued sections, Rockafellar convexity
still does not force the exact sectionwise-closure hypothesis needed by the repaired forward
argument. -/
lemma helperForLemma33_0_14_rockafellarConvex_and_noBot_doNotForce_exactSectionwiseClosure :
    ¬ (
      ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsRockafellarConvexBifunction F →
        (∀ u x, F u x ≠ ⊥) →
        ∀ u x, convexFunctionClosure (F u) x = F u x) := by
  intro hExact
  -- Specialize the hypothetical implication to the boundary witness and reduce to the
  -- witness-level obstruction proved just above.
  refine helperForLemma33_0_14_boundaryCounterexample_noBot_doesNotForce_exactSectionwiseClosure ?_
  intro hNoBot
  exact hExact helperForLemma33_0_14_boundaryCounterexample_isRockafellarConvex hNoBot

/-- Helper for Lemma33.0.14: the raw graph of the boundary-value counterexample is not convex,
because two finite endpoint values average to a midpoint value `⊤`. -/
lemma helperForLemma33_0_14_boundaryCounterexample_graph_not_convex :
    ¬ IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
      (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) := by
  have hMidpointParameter :
      ((1 / 2 : ℝ) • (fun _ : Fin 1 => (-1 : ℝ)) +
          (1 / 2 : ℝ) • (fun _ : Fin 1 => (1 : ℝ))) =
        (fun _ : Fin 1 => (0 : ℝ)) := by
    -- The midpoint of the constant parameters `-1` and `1` is the constant parameter `0`.
    funext i
    simp
  -- Apply the generic midpoint obstruction to the concrete one-dimensional witness.
  refine
    helperForLemma33_0_14_graphNotConvex_of_midpointTop
      (F := helperForLemma33_0_14_boundaryCounterexample)
      (u₁ := fun _ : Fin 1 => (-1 : ℝ))
      (u₂ := fun _ : Fin 1 => (1 : ℝ))
      (x := fun _ : Fin 1 => (0 : ℝ))
      helperForLemma33_0_14_boundaryCounterexample_leftValue
      helperForLemma33_0_14_boundaryCounterexample_rightValue
      ?_
  -- Rewrite the midpoint parameter to `0` and use the explicit section-value computation.
  rw [hMidpointParameter]
  exact helperForLemma33_0_14_boundaryCounterexample_midpointValue

/-- Helper for Lemma33.0.14: even for the explicit boundary-value witness, the tempting global
no-`⊥` repair does not force convexity of the raw graph function. -/
lemma helperForLemma33_0_14_boundaryCounterexample_noBot_doesNotForce_graphConvexity :
    ¬ (
      (∀ u x, helperForLemma33_0_14_boundaryCounterexample u x ≠ ⊥) →
        IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
          (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample)) := by
  intro hGraphFromNoBot
  -- Apply the hypothetical no-`⊥` implication to the witness's already established
  -- non-`⊥` property.
  have hBoundaryGraphConvex :
      IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
        (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) :=
    hGraphFromNoBot helperForLemma33_0_14_boundaryCounterexample_ne_bot
  -- The midpoint top-value computation refutes convexity of this raw graph.
  exact helperForLemma33_0_14_boundaryCounterexample_graph_not_convex hBoundaryGraphConvex

/-- Helper for Lemma33.0.14: adding only a global no-`⊥` hypothesis still does not rescue the
raw forward bridge in dimension `(1, 1)`, because the explicit boundary-value witness already
satisfies that extra assumption while its raw graph remains nonconvex. -/
lemma helperForLemma33_0_14_forwardImplication_with_noBot_stillFails_in_dim1 :
    ¬ (∀ F : (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal,
      IsRockafellarConvexBifunction F →
        (∀ u x, F u x ≠ ⊥) →
          IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
            (graphFunctionOfBifunction F)) := by
  intro hForward
  -- Specialize the quantified no-`⊥` bridge to the explicit witness and reduce to the
  -- witness-level graph obstruction proved just above.
  refine helperForLemma33_0_14_boundaryCounterexample_noBot_doesNotForce_graphConvexity ?_
  intro hNoBot
  exact hForward _ helperForLemma33_0_14_boundaryCounterexample_isRockafellarConvex hNoBot

/-- Helper for Lemma33.0.14: for the explicit boundary-value witness, the exact forward
conclusion appearing in the theorem's forward branch is already impossible, because the
graph-convexity component fails even though the reconstruction identity is available. -/
lemma helperForLemma33_0_14_boundaryCounterexample_refutes_forwardConclusion :
    ¬ (
      IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
          (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) ∧
        bifunctionOfGraphFunction
            (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) =
          helperForLemma33_0_14_boundaryCounterexample) := by
  intro hConclusion
  -- The witness already violates the graph-convexity part of the forward conclusion, so the
  -- bundled reconstruction equality cannot rescue the conjunction.
  exact helperForLemma33_0_14_boundaryCounterexample_graph_not_convex hConclusion.1

/-- Helper for Lemma33.0.14: even the exact forward-branch shape from the correspondence
statement remains false after adding only a global no-`⊥` hypothesis in dimension `(1, 1)`. -/
lemma helperForLemma33_0_14_forwardCorrespondence_with_noBot_stillFails_in_dim1 :
    ¬ (∀ F : (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal,
      IsRockafellarConvexBifunction F →
        (∀ u x, F u x ≠ ⊥) →
          IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
            (graphFunctionOfBifunction F) ∧
            bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) := by
  intro hForward
  have hBoundaryConclusion :
      IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
          (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) ∧
        bifunctionOfGraphFunction
            (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) =
          helperForLemma33_0_14_boundaryCounterexample := by
    -- Apply the proposed no-`⊥`-strengthened correspondence to the explicit witness.
    exact hForward _ helperForLemma33_0_14_boundaryCounterexample_isRockafellarConvex
      helperForLemma33_0_14_boundaryCounterexample_ne_bot
  -- The witness-level conjunction is already known to be impossible.
  exact
    helperForLemma33_0_14_boundaryCounterexample_refutes_forwardConclusion
      hBoundaryConclusion

/-- Helper for Lemma33.0.14: the explicit one-dimensional boundary-value witness refutes the
specialized forward branch in its exact theorem shape, not merely its graph-convexity
projection. -/
lemma helperForLemma33_0_14_boundaryCounterexample_refutes_exactForwardBridge :
    ¬ (
      IsRockafellarConvexBifunction helperForLemma33_0_14_boundaryCounterexample →
        IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
            (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) ∧
          bifunctionOfGraphFunction
              (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) =
            helperForLemma33_0_14_boundaryCounterexample) := by
  intro hSpecializedForward
  -- Apply the specialized forward bridge to the Rockafellar-convex witness and reuse the exact
  -- conjunction-level contradiction above.
  exact helperForLemma33_0_14_boundaryCounterexample_refutes_forwardConclusion
    (hSpecializedForward helperForLemma33_0_14_boundaryCounterexample_isRockafellarConvex)

/-- Helper for Lemma33.0.14: the explicit one-dimensional boundary-value witness already
refutes the specialized raw forward bridge from Rockafellar convexity to graph convexity. -/
lemma helperForLemma33_0_14_boundaryCounterexample_refutes_rawForwardBridge :
    ¬ (
      IsRockafellarConvexBifunction helperForLemma33_0_14_boundaryCounterexample →
        IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
          (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample)) := by
  intro hSpecializedForward
  -- Apply the specialized bridge to the explicit witness and contradict its nonconvex raw graph.
  exact helperForLemma33_0_14_boundaryCounterexample_graph_not_convex
    (hSpecializedForward helperForLemma33_0_14_boundaryCounterexample_isRockafellarConvex)

/-- Helper for Lemma33.0.14: the forward implication from Rockafellar convexity to raw graph
convexity already fails in dimension `(m, n) = (1, 1)`. -/
lemma helperForLemma33_0_14_forwardImplicationFails_in_dim1 :
    ¬ (∀ F : (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal,
      IsRockafellarConvexBifunction F →
        IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ)) (graphFunctionOfBifunction F)) := by
  intro hForward
  -- Specialize the claimed universal bridge to the boundary-value counterexample.
  refine helperForLemma33_0_14_boundaryCounterexample_refutes_rawForwardBridge ?_
  intro hRock
  exact hForward _ hRock

/-- Helper for Lemma33.0.14: even the forward branch of the claimed graph-function
correspondence, including the reconstruction clause, already fails in dimension `(1, 1)`
because its raw graph-convexity component is false there. -/
lemma helperForLemma33_0_14_forwardCorrespondenceFails_in_dim1 :
    ¬ (∀ F : (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal,
      IsRockafellarConvexBifunction F →
        IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ)) (graphFunctionOfBifunction F) ∧
          bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) := by
  intro hForward
  -- Reuse the conjunction-level witness contradiction so the obstruction matches the exact
  -- forward theorem shape rather than only its first projection.
  refine helperForLemma33_0_14_boundaryCounterexample_refutes_exactForwardBridge ?_
  intro hRock
  exact hForward _ hRock

/-- Helper for Lemma33.0.14: the specialized `(1, 1)` correspondence statement would force the
explicit boundary-value counterexample to have a convex raw graph. -/
lemma helperForLemma33_0_14_dim1Correspondence_forces_boundaryCounterexample_graphConvex
    (hCorrespondence :
      (∀ F : (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal,
        IsRockafellarConvexBifunction F →
          IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
            (graphFunctionOfBifunction F) ∧
            bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
      (∀ f : (Fin (1 + 1) → ℝ) → EReal,
        IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ)) f →
          IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
            graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f)) :
    IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
      (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) := by
  -- Project the forward half of the specialized correspondence and evaluate it on the explicit
  -- one-dimensional witness.
  exact
    (hCorrespondence.1 _ helperForLemma33_0_14_boundaryCounterexample_isRockafellarConvex).1


end Section33
end Chap07
