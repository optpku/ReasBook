/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_3_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable (n : ℕ)

open DeterministicValueOracleMethod

/- Corollary 1.3.8 stays in the Chapter 1 value-oracle complexity domain.

Relevant owner-style declarations sampled before refining:
* `uniformGrid_isApproximateMinimizer_of_isMinOn` in `Theorem_1_3_6.lean`, the canonical bridge
  from a midpoint-grid minimizer to approximate optimality on the box problem;
* `uniformGridMethod_output_isMinOn` in `Algorithm_1_3_5.lean`, which supplies the required
  midpoint-grid minimizer after exactly `p^n` oracle calls;
* `solvesLinftyLipschitzProblemClassWithin_of_isApproximateMinimizer_outputAfter` in
  `Theorem_1_3_9.lean`, the owner bridge from a uniform approximate-minimizer guarantee to the
  chapter solve predicate;
* `DeterministicValueOracleMethod.SolvesLinftyLipschitzProblemClassWithin` in
  `Theorem_1_3_9.lean`, the owner oracle-complexity predicate for this chapter.

Source/core/bridge triage:
* source-facing: the textbook uniform-grid method and the bound `(\lfloor L / (2 ε) \rfloor + 1)^n`;
* core/canonical: `DeterministicValueOracleMethod (zeroOneBox n)` and its solve predicate;
* bridge/view: deriving the owner solve predicate for `uniformGridMethod n p` from Theorem 1.3.6
  and Algorithm 1.3.5.

Primitive data:
* the dimension `n` and mesh parameter `p : ℕ+` for `uniformGridMethod n p`.

Derived API:
* the solve guarantee within `p^n` value-oracle calls;
* the corollary obtained by the canonical choice `p = ⌊L / (2 ε)⌋ + 1`. -/

/-- Bridge theorem from Theorem 1.3.6 and Algorithm 1.3.5 to the owner oracle-complexity
predicate. If the midpoint mesh `p` satisfies `L / (2p) < ε`, then the canonical uniform grid
method solves the `L`-Lipschitz box problem class within `p^n` value-oracle calls. -/
theorem uniformGridMethod_solvesLinftyLipschitzProblemClassWithin
    (p : ℕ+) (L : NNReal) {ε : ℝ}
    (hp : (L : ℝ) / (2 * (p : ℝ)) < ε) :
    (uniformGridMethod n p).SolvesLinftyLipschitzProblemClassWithin L ε ((p : ℕ) ^ n) := by
  -- Route the grid-minimizer guarantee through the chapter's owner solve predicate.
  refine
    solvesLinftyLipschitzProblemClassWithin_of_isApproximateMinimizer_outputAfter
      (uniformGridMethod n p) hp ?_
  intro f hf
  -- Theorem 1.3.6 turns the grid minimizer produced by Algorithm 1.3.5 into the required
  -- approximate minimizer on the box problem.
  exact
    uniformGrid_isApproximateMinimizer_of_isMinOn
      f L p
      ((uniformGridMethod n p).outputAfter (f ∘ (↑)) ((p : ℕ) ^ n))
      (uniformGridMethod_output_mem_uniformGrid n p f)
      hf
      (uniformGridMethod_output_isMinOn n p f)

/-- Helper for Corollary 1.3.8: the floor-based mesh choice makes the midpoint discretization
error strictly smaller than `ε`. -/
lemma uniform_grid_floor_mesh_lt_eps
    (L : NNReal) {ε : ℝ} (hε : 0 < ε) :
    let m := Nat.floor ((L : ℝ) / (2 * ε))
    (L : ℝ) / (2 * (((Nat.succPNat m : ℕ) : ℝ))) < ε := by
  -- Write the chosen mesh parameter as `m + 1`, where `m = ⌊L / (2 ε)⌋`.
  dsimp
  set m : ℕ := Nat.floor ((L : ℝ) / (2 * ε))
  have hfloor : (L : ℝ) / (2 * ε) < (m : ℝ) + 1 := by
    simpa [m] using Nat.lt_floor_add_one ((L : ℝ) / (2 * ε))
  have hε2 : 0 < 2 * ε := by
    positivity
  -- Clear the denominator in the floor inequality to obtain the numerator bound needed later.
  have hscaled : (L : ℝ) < ((m : ℝ) + 1) * (2 * ε) := by
    exact (div_lt_iff₀ hε2).1 hfloor
  have hdenom : 0 < (2 : ℝ) * (((m + 1 : ℕ) : ℝ)) := by
    positivity
  have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by
    norm_num [Nat.cast_add]
  -- Re-express the chosen mesh size as a positive denominator and finish by linear arithmetic.
  apply (div_lt_iff₀ hdenom).2
  rw [hcast]
  nlinarith [hscaled]

/-- Corollary 1.3.8: for the uniform grid method on the `L`-Lipschitz box problem class, the
analytical complexity is at most `(\lfloor L / (2 ε) \rfloor + 1)^n`. -/
-- Proof sketch: choose the mesh parameter `p = (⌊L / (2 ε)⌋).succPNat`, so that
-- `(p : ℕ) = ⌊L / (2 ε)⌋ + 1` and `L / (2 p) < ε`, then apply
-- `uniformGridMethod_solvesLinftyLipschitzProblemClassWithin`.
theorem uniformGridMethod_analyticalComplexity_bound
    (L : NNReal) {ε : ℝ} (hε : 0 < ε) :
    (uniformGridMethod n
      (Nat.floor ((L : ℝ) / (2 * ε))).succPNat).SolvesLinftyLipschitzProblemClassWithin
      L ε ((Nat.floor ((L : ℝ) / (2 * ε)) + 1) ^ n) := by
  -- Choose the textbook mesh parameter `p = ⌊L / (2 ε)⌋ + 1` and invoke the owner bridge theorem.
  simpa [Nat.succPNat_coe] using
    uniformGridMethod_solvesLinftyLipschitzProblemClassWithin
      (n := n)
      (p := (Nat.floor ((L : ℝ) / (2 * ε))).succPNat)
      L
      (uniform_grid_floor_mesh_lt_eps L hε)
