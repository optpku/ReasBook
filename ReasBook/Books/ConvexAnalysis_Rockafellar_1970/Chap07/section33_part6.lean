/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap07.section33_part5

section Chap07
section Section33

attribute [local instance] classicalSetDecidablePred
attribute [local instance] Classical.propDecidable

/-- Helper for Lemma33.0.14: the full one-to-one correspondence statement is already false in
dimension `(1, 1)` because its forward branch fails there. -/
lemma helperForLemma33_0_14_correspondenceStatementFails_in_dim1 :
    ¬ (
      (∀ F : (Fin 1 → ℝ) → (Fin 1 → ℝ) → EReal,
        IsRockafellarConvexBifunction F →
          IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
            (graphFunctionOfBifunction F) ∧
            bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
      (∀ f : (Fin (1 + 1) → ℝ) → EReal,
        IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ)) f →
          IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
            graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f)) := by
  intro hCorrespondence
  have hBoundaryGraphConvex :
      IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
        (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) := by
    -- The new witness-level extraction keeps the blocker attached to the exact theorem shape.
    exact
      helperForLemma33_0_14_dim1Correspondence_forces_boundaryCounterexample_graphConvex
        hCorrespondence
  -- The extracted convexity claim contradicts the explicit midpoint computation for the
  -- boundary-value witness.
  exact helperForLemma33_0_14_boundaryCounterexample_graph_not_convex hBoundaryGraphConvex

/-- Helper for Lemma33.0.14: any dimension-uniform proof of the claimed graph-function
correspondence would specialize to the already-refuted `(1, 1)` statement, so the obstruction
is semantic rather than a missing local lemma. -/
lemma helperForLemma33_0_14_genericCorrespondence_specializes_to_dim1_contradiction
    (hCorrespondence :
      ∀ {m n : ℕ},
        (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
          IsRockafellarConvexBifunction F →
            IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
              (graphFunctionOfBifunction F) ∧
              bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
        (∀ f : (Fin (m + n) → ℝ) → EReal,
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f →
            IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
              graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f)) :
    False := by
  -- Specialize the putative generic correspondence to dimension `(1, 1)` and reuse the
  -- explicit boundary-value counterexample packaged above.
  exact
    helperForLemma33_0_14_correspondenceStatementFails_in_dim1
      (hCorrespondence (m := 1) (n := 1))

/-- Helper for Lemma33.0.14: any dimension-uniform proof of the raw forward bridge from
Rockafellar convexity to graph convexity would already contradict the specialized `(1, 1)`
boundary-value witness. -/
lemma helperForLemma33_0_14_genericForwardBridge_specializes_to_dim1_contradiction
    (hForward :
      ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsRockafellarConvexBifunction F →
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
            (graphFunctionOfBifunction F)) :
    False := by
  -- Specialize the putative uniform forward bridge to dimension `(1, 1)` and reuse the
  -- explicit one-dimensional refutation packaged above.
  refine helperForLemma33_0_14_forwardImplicationFails_in_dim1 ?_
  intro F hRock
  exact hForward (F := F) hRock

/-- Helper for Lemma33.0.14: under the current definitions, there is no dimension-uniform raw
forward bridge from Rockafellar convexity to convexity of the graph function. -/
lemma helperForLemma33_0_14_no_dimensionUniformForwardBridge :
    ¬ (
      ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsRockafellarConvexBifunction F →
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
            (graphFunctionOfBifunction F)) := by
  intro hForward
  -- Repackage the specialized `(1, 1)` contradiction as a direct negation of the uniform
  -- forward bridge.
  exact
    helperForLemma33_0_14_genericForwardBridge_specializes_to_dim1_contradiction hForward

/-- Helper for Lemma33.0.14: any dimension-uniform proof of the full graph-function
correspondence automatically contains the raw forward bridge obtained by projecting the first
component of the claimed equivalence. -/
lemma helperForLemma33_0_14_uniformCorrespondence_implies_uniformForwardBridge
    (hCorrespondence :
      ∀ {m n : ℕ},
        (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
          IsRockafellarConvexBifunction F →
            IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
              (graphFunctionOfBifunction F) ∧
              bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
        (∀ f : (Fin (m + n) → ℝ) → EReal,
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f →
            IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
              graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f)) :
    ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
      IsRockafellarConvexBifunction F →
        IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
          (graphFunctionOfBifunction F) := by
  intro m n F hRock
  -- Project the first half of the claimed correspondence at the chosen dimensions and
  -- bifunction.
  exact ((hCorrespondence (m := m) (n := n)).1 F hRock).1

/-- Helper for Lemma33.0.14: under the current definitions, there is no dimension-uniform proof
of the full claimed graph-function correspondence. -/
lemma helperForLemma33_0_14_no_dimensionUniformCorrespondence :
    ¬ (
      ∀ {m n : ℕ},
        (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
          IsRockafellarConvexBifunction F →
            IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
              (graphFunctionOfBifunction F) ∧
              bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
        (∀ f : (Fin (m + n) → ℝ) → EReal,
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f →
            IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
              graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f)) := by
  intro hCorrespondence
  have hForward :
      ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsRockafellarConvexBifunction F →
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
            (graphFunctionOfBifunction F) :=
    helperForLemma33_0_14_uniformCorrespondence_implies_uniformForwardBridge hCorrespondence
  -- Reduce the full correspondence to the already-refuted raw forward bridge.
  exact helperForLemma33_0_14_no_dimensionUniformForwardBridge hForward

/-- Helper for Lemma33.0.14: even after strengthening the raw forward bridge by a global
no-`⊥` hypothesis, the boundary-value witness still rules out any dimension-uniform proof of
that repair. -/
lemma helperForLemma33_0_14_no_dimensionUniformForwardBridge_with_noBot :
    ¬ (
      ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsRockafellarConvexBifunction F →
          (∀ u x, F u x ≠ ⊥) →
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
            (graphFunctionOfBifunction F)) := by
  intro hForward
  -- Specialize the putative uniform no-`⊥` bridge to dimension `(1, 1)` and reuse the
  -- explicit witness-level contradiction already proved above.
  refine helperForLemma33_0_14_forwardImplication_with_noBot_stillFails_in_dim1 ?_
  intro F hRock hNoBot
  exact hForward (F := F) hRock hNoBot

/-- Helper for Lemma33.0.14: any dimension-uniform proof of the no-`⊥`-strengthened full
graph-function correspondence still contains the corresponding no-`⊥` forward bridge, obtained
by projecting the first component of the claimed equivalence. -/
lemma helperForLemma33_0_14_uniformCorrespondence_with_noBot_implies_uniformForwardBridge_with_noBot
    (hCorrespondence :
      ∀ {m n : ℕ},
        (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
          IsRockafellarConvexBifunction F →
            (∀ u x, F u x ≠ ⊥) →
            IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
              (graphFunctionOfBifunction F) ∧
              bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
        (∀ f : (Fin (m + n) → ℝ) → EReal,
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f →
            IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
              graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f)) :
    ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
      IsRockafellarConvexBifunction F →
        (∀ u x, F u x ≠ ⊥) →
        IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
          (graphFunctionOfBifunction F) := by
  intro m n F hRock hNoBot
  -- Project the no-`⊥`-strengthened forward component at the chosen dimensions and bifunction.
  exact ((hCorrespondence (m := m) (n := n)).1 F hRock hNoBot).1

/-- Helper for Lemma33.0.14: even the no-`⊥`-strengthened full correspondence cannot hold
dimension-uniformly, because it still projects to the already-refuted no-`⊥` forward bridge. -/
lemma helperForLemma33_0_14_no_dimensionUniformCorrespondence_with_noBot :
    ¬ (
      ∀ {m n : ℕ},
        (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
          IsRockafellarConvexBifunction F →
            (∀ u x, F u x ≠ ⊥) →
            IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
              (graphFunctionOfBifunction F) ∧
              bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
        (∀ f : (Fin (m + n) → ℝ) → EReal,
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f →
            IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
              graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f)) := by
  intro hCorrespondence
  have hForward :
      ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsRockafellarConvexBifunction F →
          (∀ u x, F u x ≠ ⊥) →
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
            (graphFunctionOfBifunction F) :=
    helperForLemma33_0_14_uniformCorrespondence_with_noBot_implies_uniformForwardBridge_with_noBot
      hCorrespondence
  -- Reduce the no-`⊥`-strengthened full correspondence to the already-refuted no-`⊥`
  -- forward bridge.
  exact helperForLemma33_0_14_no_dimensionUniformForwardBridge_with_noBot hForward

/-- Helper for Lemma33.0.14: after repairing the false raw forward bridge by adding exact
sectionwise-closure and no-`⊥` hypotheses, Rockafellar convexity does imply convexity of the
raw graph function. -/
lemma helperForLemma33_0_14_forwardHalf_graphConvex_of_rockafellar
    {m n : ℕ}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hRock : IsRockafellarConvexBifunction F)
    (hClosureExact : ∀ u x, convexFunctionClosure (F u) x = F u x)
    (hNoBot : ∀ u x, F u x ≠ ⊥) :
    IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) := by
  -- Route correction: Agent C's boundary counterexample shows the old raw statement was false.
  -- The repaired version below uses the exact sectionwise-closure and no-`⊥` hypotheses that
  -- the earlier closure-level argument genuinely needs.
  exact
    helperForLemma33_0_14_graphConvex_of_rockafellar_with_exactSectionwiseClosure
      (F := F) hRock hClosureExact hNoBot

/-- Helper for Lemma33.0.14: after repairing the false raw forward branch by adding exact
sectionwise-closure and no-`⊥` hypotheses, the intended graph-function correspondence is
valid. -/
lemma helperForLemma33_0_14_repairedCorrespondence_of_exactSectionwiseClosure
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F →
        (∀ u x, convexFunctionClosure (F u) x = F u x) →
        (∀ u x, F u x ≠ ⊥) →
        IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) ∧
          bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
    (∀ f : (Fin (m + n) → ℝ) → EReal,
      IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f →
        IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
          graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f) := by
  constructor
  · intro F hRock hClosureExact hNoBot
    -- The repaired forward branch is exactly the exact-closure/no-`⊥` theorem already proved
    -- above.
    exact
      helperForLemma33_0_14_forwardHalf_of_exactSectionwiseClosure
        (F := F) hRock hClosureExact hNoBot
  · intro f hf
    -- The backward branch never used the false raw forward implication, so the original helper
    -- still applies unchanged.
    exact helperForLemma33_0_14_backwardHalf_of_graphConvex (f := f) hf

/-- Helper for Lemma33.0.14: the exact forward-branch shape appearing in the target theorem
already forces the explicit boundary-value counterexample to have a convex raw graph. -/
lemma helperForLemma33_0_14_targetForwardBranch_forces_boundaryCounterexample_graphConvex
    (hForward :
      ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsRockafellarConvexBifunction F →
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
            (graphFunctionOfBifunction F) ∧
            bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) :
    IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
      (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) := by
  -- Specialize the exact forward branch to the explicit `(1, 1)` witness and project the
  -- graph-convexity component of the claimed conclusion.
  exact
    (hForward (F := helperForLemma33_0_14_boundaryCounterexample)
      helperForLemma33_0_14_boundaryCounterexample_isRockafellarConvex).1

/-- Helper for Lemma33.0.14: the exact forward-branch shape from the target theorem is
already impossible, because it forces the boundary-value counterexample to satisfy the raw
graph-convexity conclusion that the midpoint calculation explicitly refutes. -/
lemma helperForLemma33_0_14_targetForwardBranch_impossible
    (hForward :
      ∀ {m n : ℕ} {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal},
        IsRockafellarConvexBifunction F →
          IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ))
            (graphFunctionOfBifunction F) ∧
            bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) :
    False := by
  have hBoundaryGraphConvex :
      IsERealConvexOn (Set.univ : Set (Fin (1 + 1) → ℝ))
        (graphFunctionOfBifunction helperForLemma33_0_14_boundaryCounterexample) :=
    helperForLemma33_0_14_targetForwardBranch_forces_boundaryCounterexample_graphConvex
      hForward
  -- The new specialization helper reduces the target forward branch to the already-proved
  -- witness-level graph obstruction.
  exact helperForLemma33_0_14_boundaryCounterexample_graph_not_convex hBoundaryGraphConvex

/-- Helper for Lemma33.0.14: the main correspondence lemma is exactly the packaged repaired
forward/backward halves already proved above. -/
lemma helperForLemma33_0_14_correspondence
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F →
        (∀ u x, convexFunctionClosure (F u) x = F u x) →
        (∀ u x, F u x ≠ ⊥) →
        IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) ∧
          bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
    (∀ f : (Fin (m + n) → ℝ) → EReal,
      IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f →
        IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
          graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f) := by
  -- The heavy lifting is done by `helperForLemma33_0_14_repairedCorrespondence_of_exactSectionwiseClosure`.
  exact helperForLemma33_0_14_repairedCorrespondence_of_exactSectionwiseClosure (m := m) (n := n)

/-- Helper for Lemma33.0.14: the target theorem can be closed by directly reusing the
already-packaged correspondence helper. -/
lemma helperForLemma33_0_14_correspondence_for_mainTheorem
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F →
        (∀ u x, convexFunctionClosure (F u) x = F u x) →
        (∀ u x, F u x ≠ ⊥) →
        IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) ∧
          bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
    (∀ f : (Fin (m + n) → ℝ) → EReal,
      IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f →
        IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
          graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f) := by
  -- This is just the previously proved correspondence helper, exposed under a dedicated name
  -- for the main theorem handoff.
  exact helperForLemma33_0_14_correspondence (m := m) (n := n)

/-- Lemma33.0.14: in the present `EReal` formalization, the graph-function correspondence is
carried by convex bifunctions whose sections already agree with their convex closures and never
take the value `⊥`. Under these exact sectionwise-closure hypotheses, the graph functions
`f (u, x) = (F u) x` are exactly the convex functions on `ℝ^(m + n)`, and the two constructions
are inverse. -/
lemma convexBifunction_graphFunction_correspondence
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F →
        (∀ u x, convexFunctionClosure (F u) x = F u x) →
        (∀ u x, F u x ≠ ⊥) →
        IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) (graphFunctionOfBifunction F) ∧
          bifunctionOfGraphFunction (graphFunctionOfBifunction F) = F) ∧
    (∀ f : (Fin (m + n) → ℝ) → EReal,
      IsERealConvexOn (Set.univ : Set (Fin (m + n) → ℝ)) f →
        IsRockafellarConvexBifunction (bifunctionOfGraphFunction f) ∧
          graphFunctionOfBifunction (bifunctionOfGraphFunction f) = f) := by
  -- The correspondence follows by the already-established repaired forward/backward halves.
  exact helperForLemma33_0_14_correspondence_for_mainTheorem (m := m) (n := n)

/-- Definition33.0.15: The ordinary conjugate of `f` is the function
`f*(u*, x*) = sup_{u, x} (⟪u, u*⟫ + ⟪x, x*⟫ - f(u, x))`. -/
noncomputable def ordinaryConjugate {m n : ℕ}
    (f : (Fin m → ℝ) → (Fin n → ℝ) → EReal) :
    (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
  fun uStar xStar =>
    sSup <| Set.range fun ux : (Fin m → ℝ) × (Fin n → ℝ) =>
      (((dotProduct ux.1 uStar + dotProduct ux.2 xStar : ℝ) : EReal) - f ux.1 ux.2)

/-- The convex closure of an `EReal`-valued function on `ℝ^n`, defined by local infima over
open balls. -/
noncomputable def functionConvexClosure {n : ℕ}
    (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun x =>
    ⨆ (ε : {ε : ℝ // 0 < ε}),
      ⨅ (w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}), f w.1

/-- An `EReal`-valued function on `ℝ^n` is convex-closed when it agrees with its convex
closure. -/
def IsFunctionConvexClosed {n : ℕ}
    (f : (Fin n → ℝ) → EReal) : Prop :=
  f = functionConvexClosure f

/-- The concave closure of an `EReal`-valued function on `ℝ^n`, defined by local suprema over
open balls followed by infimum over radii. -/
noncomputable def functionConcaveClosure {n : ℕ}
    (f : (Fin n → ℝ) → EReal) : (Fin n → ℝ) → EReal :=
  fun x =>
    ⨅ (ε : {ε : ℝ // 0 < ε}),
      ⨆ (w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}), f w.1

/-- An `EReal`-valued function on `ℝ^n` is concave-closed when it agrees with its concave
closure. -/
def IsFunctionConcaveClosed {n : ℕ}
    (f : (Fin n → ℝ) → EReal) : Prop :=
  f = functionConcaveClosure f

/-- An `EReal`-valued bifunction models a `ℝ ∪ {+∞}`-valued one when it never takes `⊥`. -/
def HasNoBotValuesBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∀ u x, F u x ≠ ⊥

/-- An `EReal`-valued bifunction models a `ℝ ∪ {-∞}`-valued one when it never takes `⊤`. -/
def HasNoTopValuesBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  ∀ u x, F u x ≠ ⊤

/- A conservative admissibility condition for kernels used in the saddle-function
correspondence: the bifunction avoids both infinite endpoints, so it fits both the
convex and concave extended-real conventions simultaneously. -/
/-- A bifunction satisfies both one-sided extended-real conventions when it takes neither
`⊥` nor `⊤` values. -/
def HasNoTopOrBotValuesBifunction {m n : ℕ}
    (F : (Fin m → ℝ) → (Fin n → ℝ) → EReal) : Prop :=
  HasNoBotValuesBifunction F ∧ HasNoTopValuesBifunction F

/-- Helper for Theorem33.1: the local convex-conjugate notation is exactly Chapter 3's
Fenchel conjugate. -/
lemma helperForTheorem33_1_convexConjugate_eq_fenchelConjugate
    {n : ℕ} (f : (Fin n → ℝ) → EReal) :
    convexConjugate f = fenchelConjugate n f := by
  rfl

/-- Helper for Theorem33.1: if one primal point avoids `⊤`, then the convex conjugate never
collapses to `⊥`. -/
lemma helperForTheorem33_1_convexConjugate_ne_bot_of_point
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {x₀ : Fin n → ℝ}
    (hx₀_ne_top : f x₀ ≠ ⊤) :
    ∀ xStar, convexConjugate f xStar ≠ (⊥ : EReal) := by
  intro xStar hbot
  have hTerm_ne_bot : (((dotProduct x₀ xStar : ℝ) : EReal) - f x₀) ≠ (⊥ : EReal) := by
    -- The chosen witness contributes a genuine affine term, so it cannot be `⊥`.
    simpa [sub_eq_add_neg] using
      add_ne_bot_of_notbot (EReal.coe_ne_bot (dotProduct x₀ xStar : ℝ))
        (show -f x₀ ≠ (⊥ : EReal) by simpa using hx₀_ne_top)
  have hTerm_le : (((dotProduct x₀ xStar : ℝ) : EReal) - f x₀) ≤ convexConjugate f xStar := by
    -- The witness point `x₀` appears among the terms in the defining supremum.
    rw [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate]
    simpa [fenchelConjugate_eq_iSup] using
      (le_iSup (fun x : Fin n → ℝ => (((dotProduct x xStar : ℝ) : EReal) - f x)) x₀)
  exact hTerm_ne_bot (le_bot_iff.mp (hbot ▸ hTerm_le))

/-- Helper for Theorem33.1: the constant `⊥` function is convex in the Jensen sense used in
Section 33. -/
lemma helperForTheorem33_1_constBot_isERealConvexOn
    {n : ℕ} :
    IsERealConvexOn (Set.univ : Set (Fin n → ℝ))
      (fun _ : Fin n → ℝ => (⊥ : EReal)) := by
  intro x y hx hy a b ha hb hab hxy
  by_cases hZeroA : a = 0
  · have hBOne : b = 1 := by linarith
    -- Zero weight on the first endpoint reduces the combination to the second endpoint.
    simp [hZeroA, hBOne]
  by_cases hZeroB : b = 0
  · have hAOne : a = 1 := by linarith
    -- The symmetric zero-weight case reduces to the first endpoint.
    simp [hZeroB, hAOne]
  have hPosA : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using hZeroA)
  have hPosB : 0 < b := lt_of_le_of_ne hb (by simpa [eq_comm] using hZeroB)
  -- With both weights positive, the Jensen right-hand side is exactly `⊥`.
  simp [EReal.coe_mul_bot_of_pos hPosA, EReal.coe_mul_bot_of_pos hPosB]

/-- Helper for Theorem33.1: once one primal point avoids `⊤`, Fenchel closed-convexity turns
the convex conjugate into a Section 33 convex function. -/
lemma helperForTheorem33_1_convexConjugate_isERealConvexOn_of_point
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {x₀ : Fin n → ℝ}
    (hx₀_ne_top : f x₀ ≠ ⊤) :
    IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (convexConjugate f) := by
  have hClosedConvex := fenchelConjugate_closedConvex (n := n) (f := f)
  have hNoBot : ∀ xStar, convexConjugate f xStar ≠ (⊥ : EReal) :=
    helperForTheorem33_1_convexConjugate_ne_bot_of_point (f := f) (x₀ := x₀) hx₀_ne_top
  -- Convert the Chapter 3 closed-convex statement back to the local Jensen predicate.
  simpa [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate] using
    helperForLemma33_0_5_convexFunction_to_isERealConvexOn_univ hClosedConvex.2 hNoBot

/-- Helper for Theorem33.1: every lower semicontinuous minorant of `f` lies below the
Section 33 closure operator. -/
lemma helperForTheorem33_1_lowerSemicontinuous_le_functionConvexClosure
    {n : ℕ} {f h : (Fin n → ℝ) → EReal}
    (hh : LowerSemicontinuous h) (hle : h ≤ f) :
    h ≤ functionConvexClosure f := by
  intro x
  refine (EReal.le_of_forall_lt_iff_le (x := functionConvexClosure f x) (y := h x)).1 ?_
  intro z hz
  by_contra hzx
  have hxMem : x ∈ (fun y : Fin n → ℝ => h y) ⁻¹' Set.Ioi (z : EReal) := by
    simpa [Set.mem_preimage, Set.mem_Ioi, not_le] using hzx
  rw [lowerSemicontinuous_iff_isOpen_preimage] at hh
  rcases Metric.isOpen_iff.mp (hh (z : EReal)) x hxMem with ⟨δ, hδ, hBall⟩
  let ε : {r : ℝ // 0 < r} := ⟨δ, hδ⟩
  have hLocalInfLt :
      (⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε.1}, f w.1) < (z : EReal) := by
    have hRawLt :
        (⨆ ε' : {r : ℝ // 0 < r},
          ⨅ w : {w : Fin n → ℝ // ‖w - x‖ < ε'.1}, f w.1) < (z : EReal) := by
      simpa [functionConvexClosure] using hz
    rcases iSup_lt_iff.mp hRawLt with ⟨b, hb_lt, hb_bound⟩
    exact lt_of_le_of_lt (hb_bound ε) hb_lt
  rcases iInf_lt_iff.mp hLocalInfLt with ⟨w, hw⟩
  have hwMem : w.1 ∈ Metric.ball x δ := by
    simpa [Metric.mem_ball, dist_eq_norm, ε] using w.2
  have hzw : (z : EReal) < h w.1 := by
    have hwPre : w.1 ∈ (fun y : Fin n → ℝ => h y) ⁻¹' Set.Ioi (z : EReal) := hBall hwMem
    simpa [Set.mem_preimage, Set.mem_Ioi] using hwPre
  exact (not_lt_of_ge (le_of_lt (lt_of_le_of_lt (hle w.1) hw))) hzw

/-- Helper for Theorem33.1: a lower semicontinuous section is already fixed by the raw
Section 33 closure operator. -/
lemma helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : LowerSemicontinuous f) :
    f = functionConvexClosure f := by
  apply le_antisymm
  · -- Lower semicontinuity makes `f` a minorant of its own closure.
    intro x
    exact helperForTheorem33_1_lowerSemicontinuous_le_functionConvexClosure
      (f := f) (h := f) hf le_rfl x
  · -- The raw closure never exceeds the original section.
    intro x
    exact helperForLemma33_0_5_functionConvexClosure_raw_le_self (f := f) x

/-- Helper for Theorem33.1: once one primal point avoids `⊤`, the convex conjugate section is
already fixed by the one-variable convex closure. -/
lemma helperForTheorem33_1_convexConjugate_isFunctionConvexClosed_of_point
    {n : ℕ} {f : (Fin n → ℝ) → EReal} {x₀ : Fin n → ℝ}
    (hx₀_ne_top : f x₀ ≠ ⊤) :
    IsFunctionConvexClosed (convexConjugate f) := by
  let _ := hx₀_ne_top
  have hClosedConvex := fenchelConjugate_closedConvex (n := n) (f := f)
  unfold IsFunctionConvexClosed
  -- Fenchel conjugates are lower semicontinuous, so the Section 33 closure fixes them directly.
  exact helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
    (by
      simpa [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate] using hClosedConvex.1)

/-- Helper for Theorem33.1: when `f` never takes the value `⊥`, the Section 33 closure agrees
with Chapter 2's convex-function closure. -/
lemma helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hNoBot : ∀ x, f x ≠ (⊥ : EReal)) :
    functionConvexClosure f = convexFunctionClosure f := by
  have hRawLsc : LowerSemicontinuous (functionConvexClosure f) := by
    simpa [functionConvexClosure] using
      helperForLemma33_0_5_functionConvexClosure_lowerSemicontinuous (f := f)
  have hRawLe : functionConvexClosure f ≤ f := by
    intro x
    exact helperForLemma33_0_5_functionConvexClosure_raw_le_self (f := f) x
  have hHullSpec := Classical.choose_spec (exists_lowerSemicontinuousHull (n := n) f)
  have hHullLsc : LowerSemicontinuous (lowerSemicontinuousHull f) := hHullSpec.1
  have hHullLe : lowerSemicontinuousHull f ≤ f := hHullSpec.2.1
  have hHullMax := hHullSpec.2.2
  apply le_antisymm
  · -- The raw closure is one lower semicontinuous minorant, so it lies below the hull.
    have hToHull : functionConvexClosure f ≤ lowerSemicontinuousHull f :=
      hHullMax (functionConvexClosure f) hRawLsc hRawLe
    simpa [convexFunctionClosure, hNoBot] using hToHull
  · -- Conversely, every lower semicontinuous minorant lies below the raw closure.
    have hToRaw : lowerSemicontinuousHull f ≤ functionConvexClosure f :=
      helperForTheorem33_1_lowerSemicontinuous_le_functionConvexClosure
        (f := f) (h := lowerSemicontinuousHull f) hHullLsc hHullLe
    simpa [convexFunctionClosure, hNoBot] using hToRaw

/-- Helper for Theorem33.1: sectionwise Fenchel-Moreau identifies the biconjugate with the
one-variable convex closure in the local Section 33 notation. -/
lemma helperForTheorem33_1_biconjugate_eq_functionConvexClosure_of_convex
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hConv : IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) f)
    (hNoBot : ∀ x, f x ≠ (⊥ : EReal)) :
    ∀ x, convexConjugate (convexConjugate f) x = functionConvexClosure f x := by
  have hConvFun : ConvexFunction f :=
    helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction hConv
  intro x
  -- Apply the one-variable Fenchel-Moreau theorem and rewrite the local notation.
  calc
    convexConjugate (convexConjugate f) x = convexFunctionClosure f x := by
      simpa [helperForTheorem33_1_convexConjugate_eq_fenchelConjugate] using
        congrArg (fun g => g x)
          (section16_fenchelConjugate_biconjugate_eq_convexFunctionClosure (f := f) hConvFun)
    _ = functionConvexClosure f x := by
      simpa [helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
        (f := f) hNoBot] using rfl

/-- Helper for Theorem33.1: after defining `F u` as the sectionwise convex conjugate of
`K u`, the resulting pairing is exactly the second-variable convex closure of `K`. -/
lemma helperForTheorem33_1_reverse_pairing_eq_convexClosureInSecond
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hConv : ∀ u, IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (K u))
    (hNoBot : ∀ u x, K u x ≠ (⊥ : EReal)) :
    let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => convexConjugate (K u) x
    ∀ u xStar, convexBifunctionPairing F u xStar = convexClosureInSecond K u xStar := by
  intro F u xStar
  change convexConjugate (convexConjugate (K u)) xStar = convexClosureInSecond K u xStar
  -- The pairing is the biconjugate of the fixed section `K u`.
  simpa [convexClosureInSecond, functionConvexClosure] using
    helperForTheorem33_1_biconjugate_eq_functionConvexClosure_of_convex
      (f := K u) (hConv := hConv u) (hNoBot := hNoBot u) xStar

-- Proof sketch: apply Fenchel-Moreau sectionwise to the functions `F u`, using the extra
-- hypothesis `HasNoBotValuesBifunction F` to model Rockafellar's `ℝ ∪ {+∞}` convention for
-- convex sections. This yields the biconjugate formula `(cl (F u)) x = sup_{x^*} (⟪x, x^*⟫
-- - ⟪F u, x^*⟫)` and the convex-closed property in the second variable, while the defining
-- parameter-side hypothesis on a convex bifunction supplies concavity in `u`. Conversely,
-- start from a concave-convex kernel `K` satisfying `HasNoTopOrBotValuesBifunction K`,
-- define `F` by sectionwise convex conjugation, and identify the resulting pairing with the
-- second-variable closure `cl₂ K`.
/-- Theorem33.1: If `F : ℝ^m → (ℝ^n → EReal)` is a convex bifunction in Rockafellar's sense
and takes no value `⊥`, then the pairing `(u, x^*) ↦ ⟪F u, x^*⟫` is concave-convex and
convex-closed in the second variable, and for every `u` and `x` one has
`(cl (F u)) x = sup_{x^*} (⟪x, x^*⟫ - ⟪F u, x^*⟫)`. Conversely, if
`K : ℝ^m × ℝ^n → EReal` is concave-convex, takes neither value `⊥` nor `⊤`, and
`(F u) x = sup_{x^*} (⟪x, x^*⟫ - K (u, x^*))`, then `F` is a convex bifunction, each section
`F u` is convex-closed, and `⟪F u, x^*⟫ = (cl₂ K) (u, x^*)`. -/
theorem convexBifunction_pairing_correspondence
    {m n : ℕ} :
    (∀ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsRockafellarConvexBifunction F →
      HasNoBotValuesBifunction F →
        IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
            (convexBifunctionPairing F) ∧
          IsConvexClosedInSecond (convexBifunctionPairing F) ∧
          ∀ u x,
            functionConvexClosure (F u) x =
              convexConjugate (convexBifunctionPairing F u) x) ∧
    (∀ K : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K →
      HasNoTopOrBotValuesBifunction K →
        let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal :=
          fun u x => convexConjugate (K u) x
        IsRockafellarConvexBifunction F ∧
          (∀ u, IsFunctionConvexClosed (F u)) ∧
          ∀ u xStar,
            convexBifunctionPairing F u xStar =
              convexClosureInSecond K u xStar) := by
  constructor
  · intro F hRock hNoBot
    rcases hRock with ⟨hSectionConv, hConcavePairing⟩
    refine ⟨?_, ?_, ?_⟩
    · constructor
      · -- The first-variable concavity is already part of Rockafellar's definition.
        intro xStar hxStar
        exact hConcavePairing xStar
      · intro u hu
        by_cases hAllTop : ∀ x : Fin n → ℝ, F u x = ⊤
        · have hPairBot : convexBifunctionPairing F u = fun _ : Fin n → ℝ => (⊥ : EReal) := by
            -- If the whole primal section is `⊤`, its conjugate section is constant `⊥`.
            funext xStar
            rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
            apply le_antisymm
            · refine iSup_le ?_
              intro x
              simp [hAllTop]
            · exact bot_le
          -- The degenerate `⊥` case is convex by a direct Jensen computation.
          simpa [hPairBot] using helperForTheorem33_1_constBot_isERealConvexOn (n := n)
        · rcases not_forall.mp hAllTop with ⟨x₀, hx₀⟩
          -- Otherwise a single non-`⊤` witness lets Fenchel closed-convexity do the work.
          simpa [convexBifunctionPairing, bifunctionPairingNotation] using
            helperForTheorem33_1_convexConjugate_isERealConvexOn_of_point
              (f := F u) (x₀ := x₀) hx₀
    · funext u
      by_cases hAllTop : ∀ x : Fin n → ℝ, F u x = ⊤
      · have hPairBot : convexBifunctionPairing F u = fun _ : Fin n → ℝ => (⊥ : EReal) := by
          -- The all-`⊤` primal section again yields the constant `⊥` dual section.
          funext xStar
          rw [convexBifunctionPairing, convexConjugate, fenchelConjugate_eq_iSup]
          apply le_antisymm
          · refine iSup_le ?_
            intro x
            simp [hAllTop]
          · exact bot_le
        -- The constant `⊥` section is already fixed by the one-variable closure.
        ext xStar
        have hConstBotLsc : LowerSemicontinuous (fun _ : Fin n → ℝ => (⊥ : EReal)) :=
          closed_improper_const_bot.1.2
        have hLeft : convexBifunctionPairing F u xStar = (⊥ : EReal) := by
          simpa using congrArg (fun g => g xStar) hPairBot
        have hPairBotPoint : ∀ w : Fin n → ℝ, convexBifunctionPairing F u w = (⊥ : EReal) := by
          intro w
          simpa using congrArg (fun g => g w) hPairBot
        have hConstBotClosure :
            functionConvexClosure (fun _ : Fin n → ℝ => (⊥ : EReal)) xStar = (⊥ : EReal) := by
          simpa using congrArg (fun g => g xStar)
            (helperForTheorem33_1_functionConvexClosure_eq_self_of_lowerSemicontinuous
              (f := fun _ : Fin n → ℝ => (⊥ : EReal)) hConstBotLsc).symm
        have hRight : convexClosureInSecond (convexBifunctionPairing F) u xStar = (⊥ : EReal) := by
          unfold convexClosureInSecond
          simp_rw [hPairBotPoint]
          simpa [functionConvexClosure] using hConstBotClosure
        exact hLeft.trans hRight.symm
      · rcases not_forall.mp hAllTop with ⟨x₀, hx₀⟩
        -- A non-`⊤` witness shows the conjugate section is closed and convex.
        ext xStar
        simpa [convexClosureInSecond, convexBifunctionPairing, bifunctionPairingNotation] using
          congrArg (fun g => g xStar)
            (helperForTheorem33_1_convexConjugate_isFunctionConvexClosed_of_point
              (f := F u) (x₀ := x₀) hx₀)
    · intro u x
      -- The displayed formula is just the sectionwise Fenchel-Moreau identity.
      simpa [convexBifunctionPairing, bifunctionPairingNotation] using
        helperForTheorem33_1_biconjugate_eq_functionConvexClosure_of_convex
          (f := F u) (hConv := hSectionConv u) (hNoBot := hNoBot u) x |>.symm
  · intro K hK hNoTopBot
    let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => convexConjugate (K u) x
    change IsRockafellarConvexBifunction F ∧ (∀ u, IsFunctionConvexClosed (F u)) ∧
      ∀ u xStar, convexBifunctionPairing F u xStar = convexClosureInSecond K u xStar
    rcases hK with ⟨hConcaveInFirst, hConvexInSecond⟩
    rcases hNoTopBot with ⟨hNoBotK, hNoTopK⟩
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro u
        -- Each section `F u` is a Fenchel conjugate, hence convex once we rule out `⊥`.
        simpa [F] using
          helperForTheorem33_1_convexConjugate_isERealConvexOn_of_point
            (f := K u) (x₀ := 0) (hNoTopK u 0)
      · intro xStar
        have hClosureData :
            IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
              (convexConcaveClosureData K).cl_v ∧
              IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
                (convexConcaveClosureData K).cl_u :=
          isConcaveConvexOn_univ_closureData_closures_of_noBot (K := K)
            ⟨hConcaveInFirst, hConvexInSecond⟩ hNoBotK
        have hPairEq :
            ∀ u, convexBifunctionPairing F u xStar = convexClosureInSecond K u xStar := by
          intro u
          simpa [F] using
            helperForTheorem33_1_reverse_pairing_eq_convexClosureInSecond
              (K := K) (hConv := fun u => hConvexInSecond u (Set.mem_univ u))
              (hNoBot := hNoBotK) u xStar
        -- Transport the first-variable concavity from `cl₂ K` along the sectionwise identity.
        simpa [hPairEq] using hClosureData.1.1 xStar (Set.mem_univ xStar)
    · intro u
      -- Every section `F u` is a closed Fenchel conjugate because `K u` never takes `⊤`.
      simpa [F] using
        helperForTheorem33_1_convexConjugate_isFunctionConvexClosed_of_point
          (f := K u) (x₀ := 0) (hNoTopK u 0)
    · -- The reverse displayed identity is the sectionwise closure formula from the helper.
      exact helperForTheorem33_1_reverse_pairing_eq_convexClosureInSecond
        (K := K) (hConv := fun u => hConvexInSecond u (Set.mem_univ u))
        (hNoBot := hNoBotK)

-- Proof sketch: the first implication is the forward direction of Theorem33.1. For the
-- converse, apply the reverse direction of Theorem33.1 to `K`; the resulting bifunction
-- `F` is obtained by partial convex conjugation, and the extra hypothesis
-- `IsConvexClosedInSecond K` identifies `convexClosureInSecond K` with `K` itself.
/-- Helper for Theorem33.0.16: if a pairing agrees pointwise with `convexClosureInSecond K`,
then `K` equals the pairing whenever `K` is convex-closed in the second variable. -/
lemma helperForTheorem33_0_16_eq_pairing_of_pairing_eq_convexClosureInSecond
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    {F : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hClosed : IsConvexClosedInSecond K)
    (hPair :
      ∀ u xStar, convexBifunctionPairing F u xStar = convexClosureInSecond K u xStar) :
    K = convexBifunctionPairing F := by
  -- Unfold convex-closedness so we can rewrite `K` by its second-variable closure.
  unfold IsConvexClosedInSecond at hClosed
  -- It remains to identify the closure with the pairing; this is just `funext` on `hPair`.
  refine hClosed.trans ?_
  funext u
  funext xStar
  exact (hPair u xStar).symm

/-- Theorem33.0.16: Under the admissibility hypotheses used in Theorem33.1, a concave-convex
bifunction that is convex-closed in the second variable is exactly a partial convex
conjugate of a Rockafellar convex bifunction. -/
theorem convexClosed_concaveConvex_bifunctions_are_partial_conjugates
    {m n : ℕ}
    {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal} :
    ((∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
        IsRockafellarConvexBifunction F ∧
          HasNoBotValuesBifunction F ∧
          K = convexBifunctionPairing F) →
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K ∧
        IsConvexClosedInSecond K) ∧
      (IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K →
        IsConvexClosedInSecond K →
        HasNoTopOrBotValuesBifunction K →
          ∃ F : (Fin m → ℝ) → (Fin n → ℝ) → EReal,
            IsRockafellarConvexBifunction F ∧
              (∀ u, IsFunctionConvexClosed (F u)) ∧
              K = convexBifunctionPairing F) := by
  constructor
  · intro hExists
    rcases hExists with ⟨F, hRock, hNoBot, hK⟩
    -- Apply the forward direction of Theorem33.1 to the witness `F`.
    have hForward :=
      (convexBifunction_pairing_correspondence (m := m) (n := n)).1 F hRock hNoBot
    refine ⟨?_, ?_⟩
    · -- Transport concave-convexity across the identity `K = pairing F`.
      -- This is a purely definitional rewrite: `simp` replaces `K` by `pairing F`.
      simpa [hK] using hForward.1
    · -- Transport convex-closedness across the same identity.
      simpa [hK] using hForward.2.1
  · intro hConcConv hClosed hNoTopBot
    classical
    -- Apply the reverse direction of Theorem33.1 to `K`, obtaining the canonical
    -- Rockafellar convex bifunction given by partial convex conjugation.
    let F : (Fin m → ℝ) → (Fin n → ℝ) → EReal := fun u x => convexConjugate (K u) x
    have hReverse :
        IsRockafellarConvexBifunction F ∧
          (∀ u, IsFunctionConvexClosed (F u)) ∧
          ∀ u xStar,
            convexBifunctionPairing F u xStar = convexClosureInSecond K u xStar := by
      -- Theorem33.1 already produces this `F` via a `let`; `simp` aligns the definitions.
      simpa [F] using
        (convexBifunction_pairing_correspondence (m := m) (n := n)).2 K hConcConv hNoTopBot
    refine ⟨F, hReverse.1, hReverse.2.1, ?_⟩
    -- Use convex-closedness to identify `K` with its closure, then replace the closure
    -- by the pairing using the pointwise identity from Theorem33.1.
    exact
      helperForTheorem33_0_16_eq_pairing_of_pairing_eq_convexClosureInSecond
        (K := K) (F := F) hClosed hReverse.2.2

-- Proof sketch: apply Theorem33.1 to realize the second-variable closure of a
-- concave-convex kernel as a convex-closed concave-convex pairing, and apply the
-- variable-swapped dual statement to get the first-variable closure as a concave-closed
-- concave-convex kernel. Repeat the same argument with convexity and concavity exchanged
-- for convex-concave kernels.
/-- Helper for Corollary33.1.1: applying the second-variable convex closure twice does not
change the result. -/
lemma helperForCorollary33_1_1_convexClosureInSecond_idempotent
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    convexClosureInSecond (convexClosureInSecond K) u v = convexClosureInSecond K u v := by
  -- Freeze the first variable so the two-variable closure becomes the raw one-variable
  -- `sup-inf` closure from Lemma 33.0.5.
  simpa [convexClosureInSecond, functionConvexClosure] using
    helperForLemma33_0_5_functionConvexClosure_raw_idempotent (f := K u) v

/-- Helper for Corollary33.1.1: swapping the variables exchanges the two coordinatewise
closure operators. -/
lemma helperForCorollary33_1_1_swap_coordinatewise_closure_identities
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    concaveClosureInFirst (fun v' u' => K u' v') v u = concaveClosureInSecond K u v ∧
      convexClosureInSecond (fun v' u' => K u' v') v u = convexClosureInFirst K u v := by
  -- Both identities are definitional once the swapped kernel is unfolded.
  constructor <;> rfl

/-- Helper for Corollary33.1.1: applying the first-variable concave closure twice does not
change the result. -/
lemma helperForCorollary33_1_1_concaveClosureInFirst_idempotent
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (u : Fin m → ℝ) (v : Fin n → ℝ) :
    concaveClosureInFirst (concaveClosureInFirst K) u v = concaveClosureInFirst K u v := by
  have hSwappedNeg :
      convexClosureInSecond (fun v' u' => -K u' v') =
        fun v' u' => -concaveClosureInFirst K u' v' := by
    -- The negated swapped kernel identifies the concave first-variable closure with an
    -- ordinary convex second-variable closure.
    funext v'
    funext u'
    exact helperForLemma33_0_5_swappedNegatedClosureIdentity (K := K) (u := u') (v := v')
  have hNeg :
      -concaveClosureInFirst (concaveClosureInFirst K) u v =
        -concaveClosureInFirst K u v := by
    calc
      -concaveClosureInFirst (concaveClosureInFirst K) u v =
          convexClosureInSecond
            (convexClosureInSecond (fun v' u' => -K u' v')) v u := by
            -- Rewrite the inner closure of the negated swapped kernel using the basic
            -- swapped-negated identity for `K`.
            rw [hSwappedNeg]
            symm
            exact helperForLemma33_0_5_swappedNegatedClosureIdentity
              (K := concaveClosureInFirst K) (u := u) (v := v)
      _ = convexClosureInSecond (fun v' u' => -K u' v') v u := by
            -- One more convex second-variable closure changes nothing.
            exact helperForCorollary33_1_1_convexClosureInSecond_idempotent
              (K := fun v' u' => -K u' v') (u := v) (v := u)
      _ = -concaveClosureInFirst K u v := by
            -- Translate the negated swapped closure back to the original concave closure.
            exact helperForLemma33_0_5_swappedNegatedClosureIdentity
              (K := K) (u := u) (v := v)
  -- Remove the two negations to recover the desired fixed-point identity.
  simpa using congrArg Neg.neg hNeg

/-- A convex second-variable section which never takes `⊥` keeps that convention after taking
its local convex closure.  This is the qualification needed when a subsequent first-variable
concave closure is required in the strong Jensen sense. -/
lemma helperForCorollary33_1_1_convexClosureInSecond_noBot
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hConv : ∀ u, IsERealConvexOn (Set.univ : Set (Fin n → ℝ)) (K u))
    (hNoBot : HasNoBotValuesBifunction K) :
    HasNoBotValuesBifunction (convexClosureInSecond K) := by
  intro u v
  by_cases hTop : ∀ w, K u w = (⊤ : EReal)
  · simp [convexClosureInSecond, functionConvexClosure, hTop]
  · have hExists : ∃ w, K u w ≠ (⊤ : EReal) := Classical.not_forall.mp hTop
    have hProper :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (K u) := by
      refine ⟨?_, ?_, ?_⟩
      · simpa [ConvexFunction] using
          helperForLemma33_0_5_isERealConvexOn_univ_to_ConvexFunction (hConv u)
      · rw [nonempty_epigraph_iff_nonempty_effectiveDomain]
        rcases hExists with ⟨w, hw⟩
        refine ⟨w, ?_⟩
        rw [effectiveDomain_eq]
        exact ⟨Set.mem_univ w, lt_top_iff_ne_top.mpr hw⟩
      · intro w _hw
        exact hNoBot u w
    have hClosureNoBot : convexFunctionClosure (K u) v ≠ (⊥ : EReal) :=
      (convexFunctionClosure_closed_properConvexFunctionOn_and_agrees_on_ri hProper).1.2.2.2
        v (Set.mem_univ v)
    change functionConvexClosure (K u) v ≠ (⊥ : EReal)
    rw [helperForTheorem33_1_functionConvexClosure_eq_convexFunctionClosure_of_noBot
      (f := K u) (hNoBot u)]
    exact hClosureNoBot

/-- The first-variable concave closure lies pointwise above the original kernel, so it also
preserves the convention that `⊥` never occurs. -/
lemma helperForCorollary33_1_1_concaveClosureInFirst_noBot
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hNoBot : HasNoBotValuesBifunction K) :
    HasNoBotValuesBifunction (concaveClosureInFirst K) := by
  intro u v hClosureBot
  apply hNoBot u v
  apply le_antisymm ?_ bot_le
  rw [← hClosureBot]
  unfold concaveClosureInFirst
  refine le_iInf fun ε => ?_
  exact le_iSup_of_le ⟨u, by simpa using ε.property⟩ le_rfl

/-- Helper for Corollary33.1.1: the concave-convex half of the corollary is exactly the
closure theorem from Lemma 33.0.5 together with the two fixed-point identities. -/
lemma helperForCorollary33_1_1_concaveConvex_coordinatewise_closures
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K) :
    IsEpigraphHypographConcaveConvex
        (concaveClosureInFirst K) ∧
      IsEpigraphHypographConcaveConvex
        (convexClosureInSecond K) ∧
      IsConcaveClosedInFirst (concaveClosureInFirst K) ∧
      IsConvexClosedInSecond (convexClosureInSecond K) := by
  have hClosures := isConcaveConvexOn_univ_closureData_closures (K := K) hK
  refine ⟨hClosures.2, hClosures.1, ?_, ?_⟩
  · -- The first-variable concave closure is a fixed point after one application.
    unfold IsConcaveClosedInFirst
    funext u
    funext v
    exact (helperForCorollary33_1_1_concaveClosureInFirst_idempotent
      (K := K) (u := u) (v := v)).symm
  · -- The second-variable convex closure is a fixed point after one application.
    unfold IsConvexClosedInSecond
    funext u
    funext v
    exact (helperForCorollary33_1_1_convexClosureInSecond_idempotent
      (K := K) (u := u) (v := v)).symm

/-- Strong Jensen form of the coordinatewise closure package under the one-sided convention
that the original kernel never takes `⊥`. -/
lemma helperForCorollary33_1_1_concaveConvex_coordinatewise_closures_of_noBot
    {m n : ℕ} {K : (Fin m → ℝ) → (Fin n → ℝ) → EReal}
    (hK : IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ)) K)
    (hNoBot : ∀ u v, K u v ≠ (⊥ : EReal)) :
    IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (concaveClosureInFirst K) ∧
      IsConcaveConvexOn (Set.univ : Set (Fin m → ℝ)) (Set.univ : Set (Fin n → ℝ))
        (convexClosureInSecond K) ∧
      IsConcaveClosedInFirst (concaveClosureInFirst K) ∧
      IsConvexClosedInSecond (convexClosureInSecond K) := by
  have hClosures :=
    isConcaveConvexOn_univ_closureData_closures_of_noBot (K := K) hK hNoBot
  refine ⟨hClosures.2, hClosures.1, ?_, ?_⟩
  · unfold IsConcaveClosedInFirst
    funext u
    funext v
    exact (helperForCorollary33_1_1_concaveClosureInFirst_idempotent
      (K := K) (u := u) (v := v)).symm
  · unfold IsConvexClosedInSecond
    funext u
    funext v
    exact (helperForCorollary33_1_1_convexClosureInSecond_idempotent
      (K := K) (u := u) (v := v)).symm

end Section33
end Chap07
