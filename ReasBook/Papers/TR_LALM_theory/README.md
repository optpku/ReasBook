# A Fixed-Penalty Linearized Augmented Lagrangian Method with Classical Multiplier Updates

**Published reading (v4.32.2):** [Verso](https://optpku.github.io/ReasBook/versions/v4.32.2/papers/tr_lalm_theory/) · [Documentation](https://optpku.github.io/ReasBook/versions/v4.32.2/docs/ReasBook/TR_LALM_theory.html) · [Theorem map](https://optpku.github.io/ReasBook/versions/v4.32.2/theorem-maps/papers/tr_lalm_theory/)

**Project-level formalization contributors:** Zichen Wang, Zaiwen Wen.

Project-level formalization credit is recorded in the [catalog](https://github.com/optpku/ReasBook/blob/90ac3dd3a968313d0da7a3137680aa895af6a69a/README.md#papers); it is separate from the original reference authors and per-file Lean authorship.

Lean 4 formalization of the theoretical results in *A Fixed-Penalty Linearized
Augmented Lagrangian Method with Classical Multiplier Updates* by Benqi Liu,
Kangkang Deng, Zichen Wang, and Zaiwen Wen.

[Lean source](https://github.com/optpku/ReasBook/tree/v4.32.2/ReasBook/Papers/TR_LALM_theory/)
| [aggregate module](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory.lean)
| [paper module](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Paper.lean)
| [interactive theorem map](https://optpku.github.io/ReasBook/versions/v4.32.2/theorem-maps/papers/tr_lalm_theory/)
| [numerical code](https://github.com/bqliu815/NR-LALM)

Contributor: Zichen Wang ([@imathwy](https://github.com/imathwy)). The
formalization uses Lean and mathlib `v4.32.2`.

## Start with the Dependency Graph

Open the [deployed interactive theorem map](https://optpku.github.io/ReasBook/versions/v4.32.2/theorem-maps/papers/tr_lalm_theory/)
first to browse the 24 article-level entries, their 42 direct dependencies,
and the natural-language statement attached to each item. Every graph node
links to the corresponding declaration in the official `v4.32.2` source tree.

## Scope

The development models the paper's mathematical objects and proves its
theoretical guarantees. It is proof-oriented: the algorithm structures encode
the iteration and its invariants for theorem proving, and are not required to be
an executable numerical implementation.

The covered results include:

- smoothness, lower-bound, Lipschitz, and uniform LICQ assumptions;
- approximate KKT points and pairs;
- the fixed-penalty NR-LALM iteration with the classical multiplier update;
- existence of accuracy-independent safe parameters and localization buffers;
- step and multiplier invariants, augmented-Lagrangian descent, and Lyapunov
  descent;
- deterministic `O(epsilon^-2)` iteration, oracle, and linear-solve complexity;
- finite-length primal-dual convergence under a KL assumption;
- stochastic-oracle and projected SPIDER estimator models;
- direct and safeguarded-restart stochastic complexity bounds;
- the optional minimum-norm second-order correction and its sufficient-region
  comparison with the base method.

Compound statements in the article are represented by families of focused Lean
theorems. The public aggregate module
[`TR_LALM_theory.Current`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Current.lean)
imports the complete article-facing development.

## Formalization Snapshot

| Measure | Value |
| --- | ---: |
| Lean/mathlib version | `v4.32.2` |
| Implementation `.lean` files | 141 |
| Physical Lean source lines | 75,686 |
| Nonblank Lean source lines | 71,407 |
| Top-level declarations | 2,853 |
| Article-level linked entries | 24 |
| Direct article-level dependency edges | 42 |
| `sorry` / `admit` placeholders | 0 / 0 |
| Project-defined `axiom` declarations | 0 |

The source-line count covers the 141 implementation modules under this
directory and excludes `Paper.lean` and the one-line aggregate wrapper
`Papers/TR_LALM_theory.lean`. The declaration breakdown is:

| Declaration kind | Count |
| --- | ---: |
| `theorem` | 1,473 |
| `lemma` | 660 |
| `def` | 620 |
| `abbrev` | 50 |
| `structure` | 40 |
| `class` | 1 |
| `instance` | 9 |
| **Total** | **2,853** |

## Article-to-Lean Map

The table records the primary Lean declaration attached to each labeled article
item. Dependencies are article-level logical dependencies; the Lean files also
import lower-level proof interfaces and mathlib results.

| Article item | Primary Lean declaration | Direct article dependencies |
| --- | --- | --- |
| Assumption 2.1 | [`EqualityConstrained.Regularity`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Assumption_2_1/Regularity.lean?plain=1#L34) | - |
| Definition 2.2 | [`KKT.IsApproximatePair`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Definition_2_2/KKT.lean?plain=1#L31) | Assumption 2.1 |
| Algorithm 2.1 | [`LALM.Run`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Algorithm_2_1/Iteration.lean?plain=1#L143) | Assumption 2.1 |
| Assumption 2.3 | [`LALM.Parameters`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Assumption_2_3.lean?plain=1#L174) | Algorithm 2.1 |
| Proposition 2.4 | [`LALM.existsParametersOfLargeBeta`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Proposition_2_4.lean?plain=1#L381) | Assumption 2.3 |
| Assumption 2.5 | [`LALM.DeterministicRegionCondition`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Assumption_2_5/Region.lean?plain=1#L78) | Assumption 2.3 |
| Lemma 2.6 | [`LALM.Run.norm_step_le`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Lemma_2_6.lean?plain=1#L373) | Assumption 2.3 |
| Lemma 2.7 | [`LALM.Run.augmentedLagrangianDescent`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Lemma_2_7.lean?plain=1#L316) | Lemma 2.6 |
| Lemma 2.8 | [`LALM.Run.norm_multiplier_succ_sub_sq_le`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Lemma_2_8.lean?plain=1#L286) | Lemma 2.6 |
| Theorem 2.9 | [`LALM.Run.lyapunovDescent`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Theorem_2_9.lean?plain=1#L97) | Lemmas 2.7, 2.8 |
| Theorem 2.10 | [`LALM.Run.admissible`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Theorem_2_10.lean?plain=1#L767) | Assumption 2.5; Theorem 2.9 |
| Lemma 2.11 | [`LALM.Run.residual_sq_le`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Lemma_2_11.lean?plain=1#L237) | Definition 2.2; Lemmas 2.6, 2.8 |
| Theorem 2.12 | [`LALM.Run.expect_residual_sq_le`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Theorem_2_12.lean?plain=1#L337) | Theorems 2.9, 2.10; Lemma 2.11 |
| Theorem 2.13 | [`LALM.Run.summableStepAndMultiplierIncrement`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Theorem_2_13.lean?plain=1#L804) | Lemmas 2.7, 2.8, 2.11; Theorem 2.10 |
| Assumption 3.1 | [`EqualityConstrained.StochasticOracle`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Assumption_3_1/Oracle.lean?plain=1#L19) | - |
| Definition 3.2 | [`KKT.Stochastic.IsApproximatePair`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Definition_3_2/Stochastic.lean?plain=1#L66) | Definition 2.2 |
| Lemma 3.3 | [`LALM.StochasticRun.accumulatedGradientErrorMeanSquare_le`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Lemma_3_3.lean?plain=1#L1532) | Assumption 2.3; Assumption 3.1 |
| Lemma 3.4 | [`LALM.StochasticRun.augmentedLagrangianDescent`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Lemma_3_4.lean?plain=1#L1340) | Assumption 2.3; Lemma 3.3 |
| Lemma 3.5 | [`LALM.StochasticRun.residual_sq_le`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Lemma_3_5.lean?plain=1#L1265) | Definition 2.2; Assumptions 2.3, 3.1 |
| Theorem 3.6 | [`LALM.StochasticRun.UniformOutput.residualMeanSquare_le`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Theorem_3_6.lean?plain=1#L309) | Definition 3.2; Lemmas 3.4, 3.5 |
| Theorem 3.7 | [`LALM.StochasticRun.Localization.exitProbability_le`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Theorem_3_7.lean?plain=1#L5068) | Lemma 3.4; Theorem 3.6 |
| Corollary 3.8 | [`LALM.SafeguardedRestart.isApproximatePair_of_iterationBound`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Corollary_3_8.lean?plain=1#L2261) | Theorem 3.7 |
| Proposition 4.1 | [`LALM.Correction.strictParameterRegion`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Proposition_4_1.lean?plain=1#L537) | Assumption 2.3 |
| Corollary 4.2 | [`LALM.Correction.Run.existsApproximatePair`](https://github.com/optpku/ReasBook/blob/v4.32.2/ReasBook/Papers/TR_LALM_theory/Corollary_4_2.lean?plain=1#L1836) | Theorems 2.12, 2.13, 3.6; Corollary 3.8; Proposition 4.1 |

## Map Contents

The deployed theorem map provides:

- full-graph and selected-neighborhood views;
- upstream and downstream highlighting;
- searchable and filterable theorem navigation;
- the natural-language statement of each article item;
- direct dependencies and direct consumers; and
- pinned links to the corresponding declaration on the official `v4.32.2`
  branch.

The static map source is available in
[`theorem-map/`](https://github.com/optpku/ReasBook/tree/v4.32.2/ReasBook/Papers/TR_LALM_theory/theorem-map/).

## Source Layout

```text
ReasBook/Papers/
+-- TR_LALM_theory.lean          # Compact aggregate entry point
+-- TR_LALM_theory/
    +-- Current.lean             # Full article-facing import surface
    +-- Paper.lean               # ReasBook documentation wrapper
    +-- Assumption_*.lean        # Article assumptions
    +-- Definition_*.lean        # KKT and stochastic definitions
    +-- Algorithm_2_1/           # Iteration model and supporting API
    +-- Lemma_*.lean             # Main estimates and proof interfaces
    +-- Theorem_*.lean           # Complexity and convergence results
    +-- Corollary_*.lean         # Restart and corrected-method results
    +-- Proposition_*.lean       # Parameter-existence and comparison results
```

## Verification

From the `ReasBook` directory on branch `v4.32.2`:

```bash
lake lean Papers/TR_LALM_theory.lean
lake lean Papers/TR_LALM_theory/Paper.lean
lake lean ReasBook.lean
```

All 24 linked article entries were audited against the manuscript for their
assumptions, constants, quantifiers, stopping semantics, and complexity
accounting. Supporting declarations make implicit mathematical interfaces
explicit without changing the article-level claims.
