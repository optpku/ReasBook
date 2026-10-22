/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part12
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part13
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part15
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part16
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part17
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part18
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part19
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part22
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part23

section Chap07
section Section34

open Set

/-- Predicates on coordinate spaces in this section are treated classically when needed in
piecewise definitions. -/
noncomputable local instance classicalDecidablePred {α : Type*} (p : α → Prop) :
    DecidablePred p :=
  Classical.decPred p

/-- A saddle-function on `ℝ^m × ℝ^n`, represented as an extended-real-valued bifunction. -/
abbrev SaddleFunction (m n : ℕ) := (Fin m → ℝ) → (Fin n → ℝ) → EReal

section SaddleAmbient

variable {m n : ℕ}

/-- The partial closure in the first argument, realized by the first-variable concave closure
from Section 33. -/
noncomputable def partialClosure₁ (K : SaddleFunction m n) : SaddleFunction m n :=
  concaveClosureInFirst K

/-- The partial closure in the second argument, realized by the second-variable convex closure
from Section 33. -/
noncomputable def partialClosure₂ (K : SaddleFunction m n) : SaddleFunction m n :=
  convexClosureInSecond K

/-- A saddle-function is concave-convex when it is concave in the first variable and convex in
the second variable on all of `ℝ^m × ℝ^n`. -/
def IsConcaveConvex (K : SaddleFunction m n) : Prop :=
  IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K

/-- A saddle-function is convex-concave when it is convex in the first variable and concave in
the second variable on all of `ℝ^m × ℝ^n`. -/
def IsConvexConcave (K : SaddleFunction m n) : Prop :=
  IsConvexConcaveOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K

/-- A witness that a saddle-function is of one of the two orientations used in Section 34. -/
inductive SaddleFunctionType (K : SaddleFunction m n) : Type where
  /-- The saddle-function is concave in the first variable and convex in the second. -/
  | concaveConvex (h : IsConcaveConvex K)
  /-- The saddle-function is convex in the first variable and concave in the second. -/
  | convexConcave (h : IsConvexConcave K)

/-- The first partial closure attached to the chosen saddle orientation of `K`. -/
noncomputable def partialClosure₁OfType (K : SaddleFunction m n)
    (hK : SaddleFunctionType K) : SaddleFunction m n → SaddleFunction m n :=
  match hK with
  | .concaveConvex _ => concaveClosureInFirst
  | .convexConcave _ =>
      fun L u v =>
        ⨆ (ε : {ε : ℝ // 0 < ε}),
          ⨅ (w : {w : Fin m → ℝ // ‖w - u‖ < ε.1}), L w.1 v

/-- The second partial closure attached to the chosen saddle orientation of `K`. -/
noncomputable def partialClosure₂OfType (K : SaddleFunction m n)
    (hK : SaddleFunctionType K) : SaddleFunction m n → SaddleFunction m n :=
  match hK with
  | .concaveConvex _ => convexClosureInSecond
  | .convexConcave _ =>
      fun L u v =>
        ⨅ (ε : {ε : ℝ // 0 < ε}),
          ⨆ (w : {w : Fin n → ℝ // ‖w - v‖ < ε.1}), L u w.1

/-- Defn 34.1: the lower and upper closures of a saddle-function are obtained by the
orientation-dependent iterated partial closures, so both the closure type and the order are
determined by the saddle orientation of `K`. -/
noncomputable def lowerUpperClosurePair (K : SaddleFunction m n)
    (hK : SaddleFunctionType K) :
    SaddleFunction m n × SaddleFunction m n :=
  match hK with
  | .concaveConvex _ =>
      ((partialClosure₂OfType K hK) ((partialClosure₁OfType K hK) K),
        (partialClosure₁OfType K hK) ((partialClosure₂OfType K hK) K))
  | .convexConcave _ =>
      ((partialClosure₁OfType K hK) ((partialClosure₂OfType K hK) K),
        (partialClosure₂OfType K hK) ((partialClosure₁OfType K hK) K))

/-- The lower closure of a saddle-function in its chosen orientation. -/
noncomputable def saddleLowerClosure (K : SaddleFunction m n)
    (hK : SaddleFunctionType K) : SaddleFunction m n :=
  (lowerUpperClosurePair K hK).1

/-- The upper closure of a saddle-function in its chosen orientation. -/
noncomputable def saddleUpperClosure (K : SaddleFunction m n)
    (hK : SaddleFunctionType K) : SaddleFunction m n :=
  (lowerUpperClosurePair K hK).2

/-- Lower closure in the concave-convex case. -/
noncomputable def lowerClosureConcaveConvex (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    SaddleFunction m n :=
  (lowerUpperClosurePair K (.concaveConvex h)).1

/-- Upper closure in the concave-convex case. -/
noncomputable def upperClosureConcaveConvex (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    SaddleFunction m n :=
  (lowerUpperClosurePair K (.concaveConvex h)).2

/-- Lower closure in the convex-concave case. -/
noncomputable def lowerClosureConvexConcave (K : SaddleFunction m n) (h : IsConvexConcave K) :
    SaddleFunction m n :=
  (lowerUpperClosurePair K (.convexConcave h)).1

/-- Upper closure in the convex-concave case. -/
noncomputable def upperClosureConvexConcave (K : SaddleFunction m n) (h : IsConvexConcave K) :
    SaddleFunction m n :=
  (lowerUpperClosurePair K (.convexConcave h)).2

/-- Defn 34.2: a concave-convex saddle-function is (1) lower closed when it coincides with its
lower closure and (2) upper closed when it coincides with its upper closure. -/
def IsLowerClosed (K : SaddleFunction m n) : Prop :=
  IsConcaveConvex K ∧ ∀ h : IsConcaveConvex K, K = lowerClosureConcaveConvex K h

/-- A concave-convex saddle-function is upper closed when it coincides with its upper closure. -/
def IsUpperClosed (K : SaddleFunction m n) : Prop :=
  IsConcaveConvex K ∧ ∀ h : IsConcaveConvex K, K = upperClosureConcaveConvex K h

/-- Defn 34.4: two concave-convex saddle-functions `K` and `L` are equivalent when they share
the same partial closures, namely `cl₁ K = cl₁ L` and `cl₂ K = cl₂ L`. -/
def saddleEquivalent (K L : SaddleFunction m n) : Prop :=
  IsConcaveConvex K ∧ IsConcaveConvex L ∧
    partialClosure₁ K = partialClosure₁ L ∧ partialClosure₂ K = partialClosure₂ L

/-- Defn 34.5: a concave-convex saddle-function is closed when it is equivalent to each of its
two partial closures, equivalently when `K ∼ cl₁ K` and `K ∼ cl₂ K`. -/
def IsClosedSaddleFunction (K : SaddleFunction m n) : Prop :=
  saddleEquivalent K (partialClosure₁ K) ∧ saddleEquivalent K (partialClosure₂ K)

/-- The effective domain in the first argument consists of those `u` for which `K u v` is never
`-∞`, uniformly in `v`. -/
def effectiveDomain₁ (K : SaddleFunction m n) : Set (Fin m → ℝ) :=
  {u | ∀ v, K u v > (⊥ : EReal)}

/-- The effective domain in the second argument consists of those `v` for which `K u v` is never
`+∞`, uniformly in `u`. -/
def effectiveDomain₂ (K : SaddleFunction m n) : Set (Fin n → ℝ) :=
  {v | ∀ u, K u v < (⊤ : EReal)}

/-- Defn 34.3: for a concave-convex function `K` on `ℝ^m × ℝ^n`, the effective domains
`dom₁ K` and `dom₂ K` are the sets where the first and second arguments avoid `-∞` and `+∞`
respectively for all values of the other variable, and the saddle effective domain `dom K` is
their product. -/
def saddleEffectiveDomain (K : SaddleFunction m n) : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  effectiveDomain₁ K ×ˢ effectiveDomain₂ K

/-- The finiteness domain of a saddle-function consists of the pairs where it takes a real
value, equivalently neither `+∞` nor `-∞`. -/
def finitenessDomain (K : SaddleFunction m n) : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  {p | K p.1 p.2 ≠ (⊤ : EReal) ∧ K p.1 p.2 ≠ (⊥ : EReal)}

/-- A saddle-function is proper when its effective domain is nonempty. -/
def IsProperSaddleFunction (K : SaddleFunction m n) : Prop :=
  saddleEffectiveDomain K ≠ (∅ : Set ((Fin m → ℝ) × (Fin n → ℝ)))

/-- The effective domain of a convex `EReal`-valued function is the set where it is strictly
below `+∞`. -/
def convexFunctionEffectiveDomain {n : ℕ} (f : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | f x < (⊤ : EReal)}

/-- The effective domain of a concave `EReal`-valued function is the set where it is strictly
above `-∞`. -/
def concaveFunctionEffectiveDomain {n : ℕ} (f : (Fin n → ℝ) → EReal) : Set (Fin n → ℝ) :=
  {x | (⊥ : EReal) < f x}

/-- A closed proper convex function with effective domain exactly `D`. -/
def IsProperClosedConvexFunctionWithDomain {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (D : Set (Fin n → ℝ)) : Prop :=
  IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f ∧
    IsFunctionConvexClosed f ∧
    (∀ x, f x ≠ (⊥ : EReal)) ∧
    convexFunctionEffectiveDomain f = D

/-- A proper convex function whose effective domain lies between `D` and `E`. -/
def IsProperConvexFunctionWithDomainBetween {n : ℕ}
    (f : (Fin n → ℝ) → EReal) (D E : Set (Fin n → ℝ)) : Prop :=
  IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f ∧
    (∀ x, f x ≠ (⊥ : EReal)) ∧
    (convexFunctionEffectiveDomain f).Nonempty ∧
    D ⊆ convexFunctionEffectiveDomain f ∧
    convexFunctionEffectiveDomain f ⊆ E

/-- An improper convex function in Rockafellar's convention: it is convex but not proper. -/
def IsImproperConvexFunction {n : ℕ} (f : (Fin n → ℝ) → EReal) : Prop :=
  IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f ∧
    ¬ ((∀ x, f x ≠ (⊥ : EReal)) ∧ (convexFunctionEffectiveDomain f).Nonempty)

/-- A closed proper concave function with effective domain exactly `C`. -/
def IsProperClosedConcaveFunctionWithDomain {m : ℕ}
    (f : (Fin m → ℝ) → EReal) (C : Set (Fin m → ℝ)) : Prop :=
  IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) f ∧
    IsFunctionConcaveClosed f ∧
    (∀ x, f x ≠ (⊤ : EReal)) ∧
    concaveFunctionEffectiveDomain f = C

/-- A proper concave function whose effective domain lies between `C` and `E`. -/
def IsProperConcaveFunctionWithDomainBetween {m : ℕ}
    (f : (Fin m → ℝ) → EReal) (C E : Set (Fin m → ℝ)) : Prop :=
  IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) f ∧
    (∀ x, f x ≠ (⊤ : EReal)) ∧
    (concaveFunctionEffectiveDomain f).Nonempty ∧
    C ⊆ concaveFunctionEffectiveDomain f ∧
    concaveFunctionEffectiveDomain f ⊆ E

/-- An improper concave function in Rockafellar's convention: it is concave but not proper. -/
def IsImproperConcaveFunction {m : ℕ} (f : (Fin m → ℝ) → EReal) : Prop :=
  IsERealConcaveOn (Set.univ : Set (Fin m → ℝ)) f ∧
    ¬ ((∀ x, f x ≠ (⊤ : EReal)) ∧ (concaveFunctionEffectiveDomain f).Nonempty)

/-- Defn 34.6: for a closed convex bifunction `F`, `Ω(F)` is the set of all concave-convex
saddle-functions equivalent to the kernel `(u, xStar) ↦ ⟪F u, xStar⟫`. -/
def EquivalenceClassGeneratedByConvexBifunction
    (F : {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal // IsImageClosedConvexBifunction F}) :
    Set (SaddleFunction m n) :=
  {K | saddleEquivalent K (convexBifunctionPairing F.1)}

/-- The concave analogue of the equivalence class generated by a closed concave bifunction `G`,
consisting of the concave-convex saddle-functions equivalent to `(u, xStar) ↦ ⟪u, G xStar⟫`. -/
def EquivalenceClassGeneratedByConcaveBifunction
    (G : {G : (Fin n → ℝ) → (Fin m → ℝ) → EReal // IsImageClosedConcaveBifunction G}) :
    Set (SaddleFunction m n) :=
  {K | saddleEquivalent K (fun u xStar => concaveBifunctionPairing G.1 xStar u)}

/-- The relative-interior effective domain `ri (dom K) = ri (dom₁ K) × ri (dom₂ K)` of a
saddle-function `K`. -/
def saddleKernelDomain (K : SaddleFunction m n) : Set ((Fin m → ℝ) × (Fin n → ℝ)) :=
  intrinsicInterior ℝ (effectiveDomain₁ K) ×ˢ intrinsicInterior ℝ (effectiveDomain₂ K)

/-- The raw restriction of a bifunction to `ri (dom₁ K) × ri (dom₂ K)`. -/
def saddleKernelRestriction (K : SaddleFunction m n) : saddleKernelDomain K → EReal :=
  fun p => K p.1.1 p.1.2

/-- Defn 34.7: if `K` is a genuine saddle-function on `ℝ^m × ℝ^n`, then its kernel is the
restriction of `K` to the relative interior of its effective domain, namely to
`ri (dom K) = ri (dom₁ K) × ri (dom₂ K)`. -/
def saddleKernel (K : SaddleFunction m n)
    (_hK : IsSaddleFunctionOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K) :
    saddleKernelDomain K → EReal :=
  saddleKernelRestriction K

-- Proof sketch: use the previously established fact that a genuine saddle-function is finite on
-- its effective domain, and then note that `ri (dom₁ K) × ri (dom₂ K)` is contained in
-- `dom₁ K × dom₂ K` by `intrinsicInterior_subset` in each coordinate.
/-- The kernel of a genuine saddle-function is finite-valued on its relative-interior domain. -/
theorem saddleKernel_finite (K : SaddleFunction m n)
    (hK : IsSaddleFunctionOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K) :
    ∀ p : saddleKernelDomain K, saddleKernel K hK p ≠ (⊤ : EReal) ∧
      saddleKernel K hK p ≠ (⊥ : EReal) := by
  intro p
  -- Unpack membership in `ri (dom₁ K) × ri (dom₂ K)` and project back to the effective domains.
  have hp : p.1 ∈ saddleKernelDomain K := p.2
  have huII : p.1.1 ∈ intrinsicInterior ℝ (effectiveDomain₁ K) := (Set.mem_prod.mp hp).1
  have hvII : p.1.2 ∈ intrinsicInterior ℝ (effectiveDomain₂ K) := (Set.mem_prod.mp hp).2
  have hu : p.1.1 ∈ effectiveDomain₁ K :=
    (intrinsicInterior_subset (𝕜 := ℝ) (s := effectiveDomain₁ K)) huII
  have hv : p.1.2 ∈ effectiveDomain₂ K :=
    (intrinsicInterior_subset (𝕜 := ℝ) (s := effectiveDomain₂ K)) hvII
  -- Translate effective-domain membership into strict inequalities at the point.
  have hgt : (⊥ : EReal) < K p.1.1 p.1.2 := hu p.1.2
  have hlt : K p.1.1 p.1.2 < (⊤ : EReal) := hv p.1.1
  constructor
  · -- Strictly below `⊤` implies the kernel value is not `+∞`.
    have hne : K p.1.1 p.1.2 ≠ (⊤ : EReal) := ne_of_lt hlt
    simpa [saddleKernel, saddleKernelRestriction] using hne
  · -- Strictly above `⊥` implies the kernel value is not `-∞`.
    have hne : K p.1.1 p.1.2 ≠ (⊥ : EReal) := by
      have : (⊥ : EReal) ≠ K p.1.1 p.1.2 := ne_of_lt hgt
      exact Ne.symm this
    simpa [saddleKernel, saddleKernelRestriction] using hne

/-- Two saddle-functions have the same kernel when their relative-interior kernel domains
coincide and the restricted bifunctions agree on that common domain. -/
def HasSameSaddleKernel (K L : SaddleFunction m n) : Prop :=
  ∃ hdom : saddleKernelDomain K = saddleKernelDomain L,
    ∀ p : saddleKernelDomain K,
      saddleKernelRestriction K p = saddleKernelRestriction L (hdom ▸ p)

-- Proof sketch: unfold the two partial closure operators and apply the corresponding idempotence
-- statements from the one-variable closure theory in Section 33.
/-- Helper for Text 34.0.1: the concave-convex lower and upper closures do not depend on which
proof of `IsConcaveConvex` is supplied. -/
lemma helperForText_34_0_1_concaveConvex_branch_proofIrrelevance
    (K : SaddleFunction m n) (h1 h2 : IsConcaveConvex K) :
    lowerClosureConcaveConvex K h1 = lowerClosureConcaveConvex K h2 ∧
      upperClosureConcaveConvex K h1 = upperClosureConcaveConvex K h2 := by
  -- Both branch definitions reduce to the same iterated closure operators.
  constructor <;> rfl

/-- Helper for Text 34.0.1: in the concave-convex branch, the lower and upper closures are
exactly the mixed coordinatewise closures `cl₂ (cl₁ K)` and `cl₁ (cl₂ K)`. -/
lemma helperForText_34_0_1_mixedClosure_formulas
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    lowerClosureConcaveConvex K h = partialClosure₂ (partialClosure₁ K) ∧
      upperClosureConcaveConvex K h = partialClosure₁ (partialClosure₂ K) := by
  -- The concave-convex branch of `lowerUpperClosurePair` uses these mixed closures by definition.
  constructor <;> rfl

/-- Helper for Text 34.0.1: the mixed lower and upper closures stay concave-convex, and each
retains the one-sided closedness built into its outermost coordinatewise closure. -/
lemma helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    IsConcaveConvex (lowerClosureConcaveConvex K h) ∧
      IsConcaveConvex (upperClosureConcaveConvex K h) ∧
      IsConvexClosedInSecond (lowerClosureConcaveConvex K h) ∧
      IsConcaveClosedInFirst (upperClosureConcaveConvex K h) := by
  -- First record the orientation data for the single-step closures of `K`.
  have hK : IsConcaveConvexOn Set.univ Set.univ K := by
    simpa [IsConcaveConvex] using h
  rcases
      helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
        (K := K) hK hNoBot with
    ⟨hCl1, hCl2, -, -⟩
  have hCl1NoBot : HasNoBotValuesBifunction (concaveClosureInFirst K) :=
    helperForCorollary33_1_1_concaveClosureInFirst_noBot hNoBot
  have hCl2NoBot : HasNoBotValuesBifunction (convexClosureInSecond K) :=
    helperForCorollary33_1_1_convexClosureInSecond_noBot
      (fun u => hK.2 u (Set.mem_univ u)) hNoBot
  -- Then apply the same theorem one more time to the appropriate single-step closures.
  rcases
      helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
        (K := concaveClosureInFirst K) hCl1 hCl1NoBot with
    ⟨-, hLower, -, hLowerClosed⟩
  rcases
      helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
        (K := convexClosureInSecond K) hCl2 hCl2NoBot with
    ⟨hUpper, -, hUpperClosed, -⟩
  rcases helperForText_34_0_1_mixedClosure_formulas K h with ⟨hLowerFormula, hUpperFormula⟩
  constructor
  · -- Rewrite the lower closure to the explicit mixed coordinatewise closure.
    rw [hLowerFormula]
    simpa [IsConcaveConvex, partialClosure₁, partialClosure₂] using hLower
  constructor
  · -- Rewrite the upper closure to the explicit mixed coordinatewise closure.
    rw [hUpperFormula]
    simpa [IsConcaveConvex, partialClosure₁, partialClosure₂] using hUpper
  constructor
  · -- The final `cl₂` forces the lower closure to be fixed in the second variable.
    rw [hLowerFormula]
    simpa [IsConvexClosedInSecond, partialClosure₁, partialClosure₂] using hLowerClosed
  · -- The outer `cl₁` makes the upper closure fixed by the first-variable closure.
    rw [hUpperFormula]
    simpa [IsConcaveClosedInFirst, partialClosure₁, partialClosure₂] using hUpperClosed

/-- The mixed lower closure inherits the no-`⊥` convention from the original kernel. -/
lemma helperForText_34_0_1_lowerClosure_noBot
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    HasNoBotValuesBifunction (lowerClosureConcaveConvex K h) := by
  have hK : IsConcaveConvexOn Set.univ Set.univ K := by
    simpa [IsConcaveConvex] using h
  have hCl1 :=
    (helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
      (K := K) hK hNoBot).1
  have hCl1NoBot := helperForCorollary33_1_1_concaveClosureInFirst_noBot hNoBot
  have hLowerNoBot := helperForCorollary33_1_1_convexClosureInSecond_noBot
    (fun u => hCl1.2 u (Set.mem_univ u)) hCl1NoBot
  rw [(helperForText_34_0_1_mixedClosure_formulas K h).1]
  exact hLowerNoBot

/-- The mixed upper closure inherits the no-`⊥` convention from the original kernel. -/
lemma helperForText_34_0_1_upperClosure_noBot
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    HasNoBotValuesBifunction (upperClosureConcaveConvex K h) := by
  have hK : IsConcaveConvexOn Set.univ Set.univ K := by
    simpa [IsConcaveConvex] using h
  have hCl2NoBot := helperForCorollary33_1_1_convexClosureInSecond_noBot
    (fun u => hK.2 u (Set.mem_univ u)) hNoBot
  have hUpperNoBot := helperForCorollary33_1_1_concaveClosureInFirst_noBot hCl2NoBot
  rw [(helperForText_34_0_1_mixedClosure_formulas K h).2]
  exact hUpperNoBot

/-- Helper for Text 34.0.1: the outer coordinatewise closure already fixes each mixed
closure. -/
lemma helperForText_34_0_1_outerClosure_fixedPoint_forms
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    partialClosure₂ (lowerClosureConcaveConvex K h) = lowerClosureConcaveConvex K h ∧
      partialClosure₁ (upperClosureConcaveConvex K h) = upperClosureConcaveConvex K h := by
  rcases helperForText_34_0_1_mixedClosure_formulas K h with
    ⟨hLowerFormula, hUpperFormula⟩
  constructor
  · rw [hLowerFormula]
    funext u
    funext v
    exact helperForCorollary33_1_1_convexClosureInSecond_idempotent
      (K := concaveClosureInFirst K) u v
  · rw [hUpperFormula]
    funext u
    funext v
    exact helperForCorollary33_1_1_concaveClosureInFirst_idempotent
      (K := convexClosureInSecond K) u v

/-- Helper for Text 34.0.1: every saddle-function lies below its first partial closure. -/
lemma helperForText_34_0_1_le_partialClosure₁
    (K : SaddleFunction m n) :
    K ≤ partialClosure₁ K := by
  intro u xStar
  -- Evaluate the infimum over radii at an arbitrary neighborhood and insert the center point.
  refine le_iInf ?_
  intro ε
  exact le_iSup
    (fun w : {w : Fin m → ℝ // ‖w - u‖ < ε.1} => K w.1 xStar)
    ⟨u, by simpa using ε.2⟩

/-- Helper for Text 34.0.1: the second partial closure lies below the original saddle-function. -/
lemma helperForText_34_0_1_partialClosure₂_le
    (K : SaddleFunction m n) :
    partialClosure₂ K ≤ K := by
  intro u xStar
  -- Evaluate the supremum over radii at an arbitrary neighborhood and insert the center point.
  refine iSup_le ?_
  intro ε
  exact iInf_le
    (fun w : {w : Fin n → ℝ // ‖w - xStar‖ < ε.1} => K u w.1)
    ⟨xStar, by simpa using ε.2⟩

/-- Helper for Text 34.0.1: the first partial closure is monotone with respect to pointwise
order. -/
lemma helperForText_34_0_1_partialClosure₁_mono
    {K L : SaddleFunction m n} (hKL : K ≤ L) :
    partialClosure₁ K ≤ partialClosure₁ L := by
  intro u xStar
  -- Push the pointwise comparison through the infimum over radii and the local suprema.
  refine iInf_mono ?_
  intro ε
  refine iSup_mono ?_
  intro w
  exact hKL w.1 xStar

/-- Helper for Text 34.0.1: the second partial closure is monotone with respect to pointwise
order. -/
lemma helperForText_34_0_1_partialClosure₂_mono
    {K L : SaddleFunction m n} (hKL : K ≤ L) :
    partialClosure₂ K ≤ partialClosure₂ L := by
  intro u xStar
  -- Push the pointwise comparison through the supremum over radii and the local infima.
  refine iSup_mono ?_
  intro ε
  refine iInf_mono ?_
  intro w
  exact hKL u w.1

/-- Helper for Text 34.0.1: any concave-closed first-variable majorant dominates the first
partial closure. -/
lemma helperForText_34_0_1_partialClosure₁_le_of_le_of_concaveClosedInFirst
    {K L : SaddleFunction m n} (hKL : K ≤ L)
    (hLClosed : IsConcaveClosedInFirst L) :
    partialClosure₁ K ≤ L := by
  -- Compare closures by monotonicity, then use the fixed-point form of first-variable
  -- concave-closedness.
  calc
    partialClosure₁ K ≤ partialClosure₁ L :=
      helperForText_34_0_1_partialClosure₁_mono hKL
    _ = L := by
      simpa [IsConcaveClosedInFirst, partialClosure₁] using hLClosed.symm

/-- Helper for Text 34.0.1: a convex-closed second-variable minorant stays below the second
partial closure of any larger saddle-function. -/
lemma helperForText_34_0_1_le_partialClosure₂_of_convexClosedInSecond_of_le
    {K L : SaddleFunction m n} (hKClosed : IsConvexClosedInSecond K)
    (hKL : K ≤ L) :
    K ≤ partialClosure₂ L := by
  -- Rewrite the minorant as its own second closure, then use monotonicity of `cl₂`.
  calc
    K = partialClosure₂ K := by
      simpa [IsConvexClosedInSecond, partialClosure₂] using hKClosed
    _ ≤ partialClosure₂ L :=
      helperForText_34_0_1_partialClosure₂_mono hKL

/-- Helper for Text 34.0.1: a closed convex bifunction witness for the mixed lower and upper
closures forces the required inner cross-closure identities. -/
lemma helperForText_34_0_1_closedConvexWitness_forces_crossClosure_relations
    {K : SaddleFunction m n} {h : IsConcaveConvex K}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hClosed : ClosedConvexBifunction F)
    (hLowerRep : ∀ u xStar,
      lowerClosureConcaveConvex K h u xStar = convexBifunctionPairing F u xStar)
    (hUpperRep : ∀ u xStar,
      upperClosureConcaveConvex K h u xStar = convexBifunctionCanonicalAdjointPairing F xStar u)
    (hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h)) :
    partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h ∧
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  have hGraph : IsGraphConvexBifunction F :=
    (helperForCorollary33_3_1_rockafellarConvex_and_graphFunctionClosed_of_closedConvexWitness
      (F := F) hClosed hNoBot).1
  -- First rewrite the adjoint pairing as the first-variable concave closure of the convex
  -- pairing, which identifies the left-to-right bridge `cl₁ L = U`.
  rcases (adjoint_pairing_eq_coordinatewise_closures (m := m) (n := n)).1 F
      ⟨hGraph, hNoBot⟩ with
    ⟨hAdjointAsFirstClosure, hAdjointAsSecondClosure⟩
  constructor
  · -- Replace the lower mixed closure by the convex pairing and the upper mixed closure by its
    -- adjoint pairing, then apply the first half of Theorem 33.2.
    funext u
    funext xStar
    calc
      partialClosure₁ (lowerClosureConcaveConvex K h) u xStar
          = functionConcaveClosure (fun u' => lowerClosureConcaveConvex K h u' xStar) u := by
              rfl
      _ = functionConcaveClosure (fun u' => convexBifunctionPairing F u' xStar) u := by
            congr 1
            funext u'
            exact hLowerRep u' xStar
      _ = concaveClosure (fun u' => convexBifunctionPairing F u' xStar) u :=
            congrFun
              (helperForTheorem33_2_functionConcaveClosure_eq_concaveClosure_of_concave
                (helperForTheorem33_2_convexPairingSection_concaveFunction hGraph xStar)
                (by
                  intro u'
                  rw [← hLowerRep u' xStar]
                  exact hLowerNoTopBot.2 u' xStar)) u
      _ = convexBifunctionCanonicalAdjointPairing F xStar u :=
            (hAdjointAsFirstClosure xStar u).symm
      _ = upperClosureConcaveConvex K h u xStar := (hUpperRep u xStar).symm
  · -- A second closure in the `xStar`-variable recovers the original convex pairing because the
    -- closed bifunction witness is fixed by graph closure.
    have hGraphNeBot :
        ∀ z : Fin (m + n) → ℝ, bifunctionGraphFunction F z ≠ (⊥ : EReal) := by
      intro z
      simpa [bifunctionGraphFunction] using
        hNoBot (fun i => z (Fin.castAdd n i)) (fun j => z (Fin.natAdd m j))
    have hClosureFixed : convexBifunctionClosure F = F :=
      helperForTheorem_6_30_11_convexBifunctionClosure_eq_self_of_closed
        (F := F) hClosed hGraphNeBot
    funext u
    have hCanonicalNoBot :
        ∀ xStar', convexBifunctionCanonicalAdjointPairing F xStar' u ≠ (⊥ : EReal) := by
      intro xStar' hBot
      have hLe := convexFunctionClosure_le_self
        (f := fun y => convexBifunctionCanonicalAdjointPairing F y u) xStar'
      change convexFunctionClosure
          (fun y => convexBifunctionCanonicalAdjointPairing F y u) xStar' ≤
        convexBifunctionCanonicalAdjointPairing F xStar' u at hLe
      rw [hBot] at hLe
      have hClosureBot :
          convexFunctionClosure
              (fun y => convexBifunctionCanonicalAdjointPairing F y u) xStar' = ⊥ :=
        le_bot_iff.mp hLe
      have hPairBot : convexBifunctionPairing F u xStar' = ⊥ := by
        have hSecond := hAdjointAsSecondClosure u xStar'
        rw [hClosureFixed, hClosureBot] at hSecond
        exact hSecond.symm
      have hPairNoBot : convexBifunctionPairing F u xStar' ≠ ⊥ := by
        rw [← hLowerRep u xStar']
        exact hLowerNoTopBot.1 u xStar'
      exact hPairNoBot hPairBot
    funext xStar
    calc
      partialClosure₂ (upperClosureConcaveConvex K h) u xStar
          = functionConvexClosure (fun xStar' => upperClosureConcaveConvex K h u xStar') xStar := by
              rfl
      _ = functionConvexClosure (fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u) xStar := by
            congr 1
            funext xStar'
            exact hUpperRep u xStar'
      _ = convexFunctionClosure
          (fun xStar' => convexBifunctionCanonicalAdjointPairing F xStar' u) xStar :=
            congrFun
              (helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
                hCanonicalNoBot) xStar
      _ = convexBifunctionPairing (convexBifunctionClosure F) u xStar :=
            hAdjointAsSecondClosure u xStar
      _ = convexBifunctionPairing F u xStar := by
            rw [hClosureFixed]
      _ = lowerClosureConcaveConvex K h u xStar := (hLowerRep u xStar).symm

/-- Helper for Text 34.0.1: the adjoint pairing of a convex bifunction, viewed as a saddle
kernel in the `(u, x^*)` variable order. -/
noncomputable def helperForText_34_0_1_convexAdjointPairingKernel
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : SaddleFunction m n :=
  fun u xStar => convexBifunctionCanonicalAdjointPairing F xStar u

/-- Helper for Text 34.0.1: function-equality formulas for the mixed closures can be evaluated
pointwise when the upper closure is written via the adjoint pairing kernel. -/
lemma helperForText_34_0_1_functionRepresentations_to_pointwiseRepresentations
    {K : SaddleFunction m n} {h : IsConcaveConvex K}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hUpperRep :
      upperClosureConcaveConvex K h =
        helperForText_34_0_1_convexAdjointPairingKernel F) :
    (∀ u xStar,
      lowerClosureConcaveConvex K h u xStar = convexBifunctionPairing F u xStar) ∧
      ∀ u xStar,
        upperClosureConcaveConvex K h u xStar = convexBifunctionCanonicalAdjointPairing F xStar u := by
  constructor
  · -- Evaluate the lower mixed-closure equality at an arbitrary pair `(u, x^*)`.
    intro u xStar
    exact congrFun (congrFun hLowerRep u) xStar
  · -- Evaluate the upper mixed-closure equality and then unfold the auxiliary kernel.
    intro u xStar
    have hUpperValue :
        upperClosureConcaveConvex K h u xStar =
          helperForText_34_0_1_convexAdjointPairingKernel F u xStar :=
      congrFun (congrFun hUpperRep u) xStar
    simpa [helperForText_34_0_1_convexAdjointPairingKernel] using hUpperValue

/-- Helper for Text 34.0.1: a closed convex bifunction witness written in function-equality
form already forces the cross-closure identities. -/
lemma helperForText_34_0_1_closedConvexWitness_forces_crossClosure_relations_of_function_equalities
    {K : SaddleFunction m n} {h : IsConcaveConvex K}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hF : IsRockafellarConvexBifunction F)
    (hNoBot : HasNoBotValuesBifunction F)
    (hClosed : ClosedConvexBifunction F)
    (hLowerRep : lowerClosureConcaveConvex K h = convexBifunctionPairing F)
    (hUpperRep :
      upperClosureConcaveConvex K h =
        helperForText_34_0_1_convexAdjointPairingKernel F)
    (hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h)) :
    partialClosure₁ (lowerClosureConcaveConvex K h) = upperClosureConcaveConvex K h ∧
      partialClosure₂ (upperClosureConcaveConvex K h) = lowerClosureConcaveConvex K h := by
  -- First unpack the function equalities into the pointwise representation formulas needed by
  -- the generic forcing lemma.
  rcases helperForText_34_0_1_functionRepresentations_to_pointwiseRepresentations
      hLowerRep hUpperRep with ⟨hLowerRepPointwise, hUpperRepPointwise⟩
  -- Then the earlier forcing lemma gives the two inner cross-closure identities directly.
  exact helperForText_34_0_1_closedConvexWitness_forces_crossClosure_relations
    hF hNoBot hClosed hLowerRepPointwise hUpperRepPointwise hLowerNoTopBot

/-- Helper for Text 34.0.1: under the extra hypothesis that the mixed lower closure takes no
`⊥` values, Section 33 reconstructs it as the pairing of an image-closed convex bifunction. -/
lemma helperForText_34_0_1_closedConvexWitness_exists
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K)
    (hLowerNoTopBot :
      HasNoTopOrBotValuesBifunction (lowerClosureConcaveConvex K h)) :
    ∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F ∧
        HasNoBotValuesBifunction F ∧
        (∀ u, IsFunctionConvexClosed (F u)) ∧
        lowerClosureConcaveConvex K h = convexBifunctionPairing F := by
  -- First package the mixed lower closure as a convex-closed concave-convex kernel.
  rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBot with
    ⟨hLowerOrient, -, hLowerClosed, -⟩
  have hKernel :
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (lowerClosureConcaveConvex K h) := by
    simpa [IsConcaveConvex, IsConcaveConvexOn] using hLowerOrient
  -- Then apply the Section 33 reconstruction theorem for such kernels.
  let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
    fun u x => convexConjugate (lowerClosureConcaveConvex K h u) x
  have hReconstruction :
      IsImageClosedConvexBifunction F ∧
        (∀ u x, F u x = convexConjugate (lowerClosureConcaveConvex K h u) x) ∧
        ∀ u xStar,
          convexBifunctionPairing F u xStar = lowerClosureConcaveConvex K h u xStar := by
    simpa [F] using
      (closedSaddleFunctions_imageClosedBifunctions_correspondence (m := m) (n := n)).2.1
        (lowerClosureConcaveConvex K h) hKernel hLowerClosed hLowerNoTopBot
  rcases hReconstruction with ⟨hImageClosed, -, hPairing⟩
  rcases hImageClosed with ⟨hRockafellar, hNoBot, hSectionClosed⟩
  refine ⟨F, hRockafellar, hNoBot, hSectionClosed, ?_⟩
  -- Finally rewrite the reconstruction formula as an equality of saddle-functions.
  funext u
  funext xStar
  exact (hPairing u xStar).symm

/-- Helper for Text 34.1.4: one application of `cl₁` already makes a concave-convex kernel
fixed by further first-variable closure. -/
lemma helperForText_34_1_4_partialClosure₁_idempotent
    (K : SaddleFunction m n) :
    partialClosure₁ (partialClosure₁ K) = partialClosure₁ K := by
  funext u
  funext v
  exact helperForCorollary33_1_1_concaveClosureInFirst_idempotent (K := K) u v

/-- Helper for Text 34.1.4: one application of `cl₂` already makes a concave-convex kernel
fixed by further second-variable closure. -/
lemma helperForText_34_1_4_partialClosure₂_idempotent
    (K : SaddleFunction m n) :
    partialClosure₂ (partialClosure₂ K) = partialClosure₂ K := by
  funext u
  funext v
  exact helperForCorollary33_1_1_convexClosureInSecond_idempotent (K := K) u v

/-- Helper for Text 34.1.4: the mixed lower closure is fixed by repeating the lower-closure
operator `cl₂ ∘ cl₁`. -/
lemma helperForText_34_1_4_lowerClosure_repeatedLowerFixed
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) =
      lowerClosureConcaveConvex K h := by
  -- Route correction: for this fixed-point identity, the local minimax route is unnecessary.
  -- The operator algebra of extensive/idempotent `cl₁` and reductive/idempotent `cl₂` is enough.
  rcases helperForText_34_0_1_mixedClosure_formulas K h with ⟨hLowerFormula, -⟩
  have hCl₁Idem :
      partialClosure₁ (partialClosure₁ K) = partialClosure₁ K :=
    helperForText_34_1_4_partialClosure₁_idempotent K
  have hCl₂IdemOnCl₁ :
      partialClosure₂ (partialClosure₂ (partialClosure₁ K)) =
        partialClosure₂ (partialClosure₁ K) :=
    helperForText_34_1_4_partialClosure₂_idempotent (partialClosure₁ K)
  apply le_antisymm
  · -- Push the inner `cl₂` below `cl₁ K`, then collapse the repeated first-variable closure.
    calc
      partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h))
          = partialClosure₂ (partialClosure₁ (partialClosure₂ (partialClosure₁ K))) := by
              rw [hLowerFormula]
      _ ≤ partialClosure₂ (partialClosure₁ (partialClosure₁ K)) := by
            apply helperForText_34_0_1_partialClosure₂_mono
            apply helperForText_34_0_1_partialClosure₁_mono
            exact helperForText_34_0_1_partialClosure₂_le (partialClosure₁ K)
      _ = partialClosure₂ (partialClosure₁ K) := by
            rw [hCl₁Idem]
      _ = lowerClosureConcaveConvex K h := by
            rw [← hLowerFormula]
  · -- Insert an extra `cl₂` using idempotence on `cl₁ K`, then use extensivity of `cl₁`.
    calc
      lowerClosureConcaveConvex K h = partialClosure₂ (partialClosure₁ K) := hLowerFormula
      _ = partialClosure₂ (partialClosure₂ (partialClosure₁ K)) := hCl₂IdemOnCl₁.symm
      _ ≤ partialClosure₂ (partialClosure₁ (partialClosure₂ (partialClosure₁ K))) :=
            helperForText_34_0_1_partialClosure₂_mono
              (helperForText_34_0_1_le_partialClosure₁ (partialClosure₂ (partialClosure₁ K)))
      _ = partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) := by
            rw [hLowerFormula]

/-- Helper for Text 34.1.4: the mixed upper closure is fixed by repeating the upper-closure
operator `cl₁ ∘ cl₂`. -/
lemma helperForText_34_1_4_upperClosure_repeatedUpperFixed
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) =
      upperClosureConcaveConvex K h := by
  -- Route correction: this fixed-point identity is also operator-theoretic; it does not need
  -- the unresolved mixed-order comparison.
  rcases helperForText_34_0_1_mixedClosure_formulas K h with ⟨-, hUpperFormula⟩
  have hCl₂Idem :
      partialClosure₂ (partialClosure₂ K) = partialClosure₂ K :=
    helperForText_34_1_4_partialClosure₂_idempotent K
  have hCl₁IdemOnCl₂ :
      partialClosure₁ (partialClosure₁ (partialClosure₂ K)) =
        partialClosure₁ (partialClosure₂ K) :=
    helperForText_34_1_4_partialClosure₁_idempotent (partialClosure₂ K)
  apply le_antisymm
  · -- Push the inner `cl₂` below `cl₁ (cl₂ K)`, then collapse the repeated `cl₁`.
    calc
      partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h))
          = partialClosure₁ (partialClosure₂ (partialClosure₁ (partialClosure₂ K))) := by
              rw [hUpperFormula]
      _ ≤ partialClosure₁ (partialClosure₁ (partialClosure₂ K)) := by
            apply helperForText_34_0_1_partialClosure₁_mono
            exact helperForText_34_0_1_partialClosure₂_le (partialClosure₁ (partialClosure₂ K))
      _ = partialClosure₁ (partialClosure₂ K) := hCl₁IdemOnCl₂
      _ = upperClosureConcaveConvex K h := by
            rw [← hUpperFormula]
  · -- Insert an extra `cl₂` using idempotence on `K`, then use extensivity of `cl₁`.
    calc
      upperClosureConcaveConvex K h = partialClosure₁ (partialClosure₂ K) := hUpperFormula
      _ ≤ partialClosure₁ (partialClosure₂ (partialClosure₁ (partialClosure₂ K))) := by
            apply helperForText_34_0_1_partialClosure₁_mono
            calc
              partialClosure₂ K = partialClosure₂ (partialClosure₂ K) := hCl₂Idem.symm
              _ ≤ partialClosure₂ (partialClosure₁ (partialClosure₂ K)) :=
                helperForText_34_0_1_partialClosure₂_mono
                  (helperForText_34_0_1_le_partialClosure₁ (partialClosure₂ K))
      _ = partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) := by
            rw [hUpperFormula]

/-- Helper for Text 34.1.4: the mixed lower closure is lower closed in the Section 33 saddle
closedness sense. -/
lemma helperForText_34_1_4_lowerClosure_isSection33LowerClosed
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    IsLowerClosedSaddleFunction (lowerClosureConcaveConvex K h) := by
  -- Package the concave-convex orientation together with the repeated lower fixed-point
  -- identity just proved.
  rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBot with
    ⟨hLowerOrient, - , -, -⟩
  have hFixed :
      partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) =
        lowerClosureConcaveConvex K h :=
    helperForText_34_1_4_lowerClosure_repeatedLowerFixed K h
  left
  exact ⟨hLowerOrient, hFixed⟩

/-- Helper for Text 34.1.4: the mixed upper closure is upper closed in the Section 33 saddle
closedness sense. -/
lemma helperForText_34_1_4_upperClosure_isSection33UpperClosed
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    IsUpperClosedSaddleFunction (upperClosureConcaveConvex K h) := by
  -- Package the concave-convex orientation together with the repeated upper fixed-point
  -- identity just proved.
  rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBot with
    ⟨-, hUpperOrient, -, -⟩
  have hFixed :
      partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) =
        upperClosureConcaveConvex K h :=
    helperForText_34_1_4_upperClosure_repeatedUpperFixed K h
  left
  exact ⟨hUpperOrient, hFixed⟩

/-- Helper for Text 34.1.4: the canonical first closure of the mixed lower closure is already
the upper-closed Section 33 partner attached to that lower-closed kernel. -/
lemma helperForText_34_1_4_firstClosureOfLowerClosure_isUpperClosedPartner
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    IsUpperClosedSaddleFunction (partialClosure₁ (lowerClosureConcaveConvex K h)) ∧
      partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) =
        lowerClosureConcaveConvex K h := by
  -- Apply the orientation-preservation theorem one more time to the mixed lower closure.
  rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBot with
    ⟨hLowerOrient, -, -, -⟩
  have hPartnerOrient :
      IsConcaveConvex (partialClosure₁ (lowerClosureConcaveConvex K h)) := by
    rcases
        helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
          (K := lowerClosureConcaveConvex K h)
          (by simpa [IsConcaveConvex] using hLowerOrient)
          (helperForText_34_0_1_lowerClosure_noBot K h hNoBot) with
      ⟨hOrient, -, -, -⟩
    simpa [IsConcaveConvex, partialClosure₁] using hOrient
  have hPartnerFixed :
      partialClosure₁ (partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h))) =
        partialClosure₁ (lowerClosureConcaveConvex K h) := by
    -- Apply `cl₁` to the repeated lower-fixed-point identity.
    exact congrArg partialClosure₁
      (helperForText_34_1_4_lowerClosure_repeatedLowerFixed K h)
  constructor
  · -- Package the canonical partner in the Section 33 upper-closed form.
    left
    exact ⟨hPartnerOrient, hPartnerFixed⟩
  · -- The second coordinatewise closure recovers the original lower closure by definition.
    exact helperForText_34_1_4_lowerClosure_repeatedLowerFixed K h

/-- Helper for Text 34.1.4: `cl₁ underline(K)` satisfies the full upper-partner data used by
Corollary 33.3.2. -/
lemma helperForText_34_1_4_firstClosureOfLower_isCanonicalUpperPartner
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    IsConcaveConvex (partialClosure₁ (lowerClosureConcaveConvex K h)) ∧
      IsUpperClosedSaddleFunction (partialClosure₁ (lowerClosureConcaveConvex K h)) ∧
      partialClosure₁ (lowerClosureConcaveConvex K h) =
        partialClosure₁ (lowerClosureConcaveConvex K h) ∧
      partialClosure₂ (partialClosure₁ (lowerClosureConcaveConvex K h)) =
        lowerClosureConcaveConvex K h := by
  -- First recover the orientation of `cl₁ underline(K)` from the one-step closure theorem.
  have hPartnerOrient :
      IsConcaveConvex (partialClosure₁ (lowerClosureConcaveConvex K h)) := by
    rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBot with
      ⟨hLowerOrient, -, -, -⟩
    rcases
        helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
          (K := lowerClosureConcaveConvex K h)
          (by simpa [IsConcaveConvex] using hLowerOrient)
          (helperForText_34_0_1_lowerClosure_noBot K h hNoBot) with
      ⟨hOrient, -, -, -⟩
    simpa [IsConcaveConvex, partialClosure₁] using hOrient
  rcases helperForText_34_1_4_firstClosureOfLowerClosure_isUpperClosedPartner K h hNoBot with
    ⟨hUpperClosed, hRecover⟩
  constructor
  · exact hPartnerOrient
  constructor
  · exact hUpperClosed
  constructor
  · -- The canonical upper partner is definitionally `cl₁ underline(K)`.
    rfl
  · -- The second coordinatewise closure recovers the mixed lower closure.
    exact hRecover

/-- Helper for Text 34.1.4: the canonical second closure of the mixed upper closure is already
the lower-closed Section 33 partner attached to that upper-closed kernel. -/
lemma helperForText_34_1_4_secondClosureOfUpperClosure_isLowerClosedPartner
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    IsLowerClosedSaddleFunction (partialClosure₂ (upperClosureConcaveConvex K h)) ∧
      partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) =
        upperClosureConcaveConvex K h := by
  -- Apply the orientation-preservation theorem one more time to the mixed upper closure.
  rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBot with
    ⟨-, hUpperOrient, -, -⟩
  have hPartnerOrient :
      IsConcaveConvex (partialClosure₂ (upperClosureConcaveConvex K h)) := by
    rcases
        helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
          (K := upperClosureConcaveConvex K h)
          (by simpa [IsConcaveConvex] using hUpperOrient)
          (helperForText_34_0_1_upperClosure_noBot K h hNoBot) with
      ⟨-, hOrient, -, -⟩
    simpa [IsConcaveConvex, partialClosure₂] using hOrient
  have hPartnerFixed :
      partialClosure₂ (partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h))) =
        partialClosure₂ (upperClosureConcaveConvex K h) := by
    -- Apply `cl₂` to the repeated upper-fixed-point identity.
    exact congrArg partialClosure₂
      (helperForText_34_1_4_upperClosure_repeatedUpperFixed K h)
  constructor
  · -- Package the canonical partner in the Section 33 lower-closed form.
    left
    exact ⟨hPartnerOrient, hPartnerFixed⟩
  · -- The first coordinatewise closure recovers the original upper closure by definition.
    exact helperForText_34_1_4_upperClosure_repeatedUpperFixed K h

/-- Helper for Text 34.1.4: `cl₂ overline(K)` satisfies the full lower-partner data used by
Corollary 33.3.2. -/
lemma helperForText_34_1_4_secondClosureOfUpper_isCanonicalLowerPartner
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    IsConcaveConvex (partialClosure₂ (upperClosureConcaveConvex K h)) ∧
      IsLowerClosedSaddleFunction (partialClosure₂ (upperClosureConcaveConvex K h)) ∧
      upperClosureConcaveConvex K h =
        partialClosure₁ (partialClosure₂ (upperClosureConcaveConvex K h)) ∧
      partialClosure₂ (upperClosureConcaveConvex K h) =
        partialClosure₂ (upperClosureConcaveConvex K h) := by
  -- First recover the orientation of `cl₂ overline(K)` from the one-step closure theorem.
  have hPartnerOrient :
      IsConcaveConvex (partialClosure₂ (upperClosureConcaveConvex K h)) := by
    rcases helperForText_34_0_1_mixedClosure_orientation_and_oneSidedClosedness K h hNoBot with
      ⟨-, hUpperOrient, -, -⟩
    rcases
        helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
          (K := upperClosureConcaveConvex K h)
          (by simpa [IsConcaveConvex] using hUpperOrient)
          (helperForText_34_0_1_upperClosure_noBot K h hNoBot) with
      ⟨-, hOrient, -, -⟩
    simpa [IsConcaveConvex, partialClosure₂] using hOrient
  rcases helperForText_34_1_4_secondClosureOfUpperClosure_isLowerClosedPartner K h hNoBot with
    ⟨hLowerClosed, hRecover⟩
  constructor
  · exact hPartnerOrient
  constructor
  · exact hLowerClosed
  constructor
  · -- The repeated-upper fixed-point identity identifies `overline(K)` with `cl₁ cl₂ overline(K)`.
    exact hRecover.symm
  · -- The canonical lower partner is definitionally `cl₂ overline(K)`.
    rfl

/-- Helper for Text 34.1.4: the Section 33 order theorem gives the mixed lower closure below
its canonical upper-closed partner `cl₁ underline(K)`. -/
lemma helperForText_34_1_4_lowerClosure_below_canonicalUpperPartner
    (K : SaddleFunction m n) (h : IsConcaveConvex K) :
    lowerClosureConcaveConvex K h ≤ partialClosure₁ (lowerClosureConcaveConvex K h) := by
  exact helperForText_34_0_1_le_partialClosure₁ (lowerClosureConcaveConvex K h)

/-- Helper for Text 34.1.4: Corollary 33.3.2 makes `cl₁ underline(K)` the unique upper-closed
partner attached to the mixed lower closure. -/
lemma helperForText_34_1_4_existsUniqueCanonicalUpperPartner
    (K : SaddleFunction m n) (h : IsConcaveConvex K)
    (hNoBot : HasNoBotValuesBifunction K) :
    ∃! U' : SaddleFunction m n,
      IsConcaveConvex U' ∧
        IsUpperClosedSaddleFunction U' ∧
        U' = partialClosure₁ (lowerClosureConcaveConvex K h) ∧
        partialClosure₂ U' = lowerClosureConcaveConvex K h := by
  -- The canonical upper partner is already `cl₁ underline(K)`, so existence comes from the
  -- previously packaged closure data.
  refine ⟨partialClosure₁ (lowerClosureConcaveConvex K h), ?_, ?_⟩
  · -- Reuse the canonical-partner package proved just above.
    exact helperForText_34_1_4_firstClosureOfLower_isCanonicalUpperPartner K h hNoBot
  · intro U' hU'
    -- Uniqueness is definitional: the data already records `U' = cl₁ underline(K)`.
    exact hU'.2.2.1

end SaddleAmbient

end Section34
end Chap07
