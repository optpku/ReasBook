"""Reviewed defining clauses for item facades whose headings live elsewhere.

These are exact source-module/declaration selectors, not inferred statements.
TR-LALM's numbered facade comments describe clauses implemented in the listed
owner modules (verified against v4.32.2, 3a77f1fb6b7f0e4b3311c72a63127d2eabe3a2d3).
The reader labels these as selected clauses and links each to its own source.
A missing or ambiguous selector must fail generation, never fall back to a
helper. Keep this mapping in the frozen tooling snapshot with the generator.
"""

ITEM_PREVIEWS: dict[str, tuple[tuple[str, str], ...]] = {
    "TR_LALM_theory.Algorithm_2_1": (
        ("TR_LALM_theory.Algorithm_2_1.Model", "stepModel"),
        ("TR_LALM_theory.Algorithm_2_1.Iteration", "Run"),
    ),
    "TR_LALM_theory.Definition_2_2": (
        ("TR_LALM_theory.Definition_2_2.KKT", "IsApproximatePoint"),
        ("TR_LALM_theory.Definition_2_2.KKT", "IsApproximatePair"),
        ("TR_LALM_theory.Definition_2_2.KKT", "IsPoint"),
        ("TR_LALM_theory.Definition_2_2.KKT", "IsPair"),
        ("TR_LALM_theory.Definition_2_2.KKT", "residual"),
    ),
    "TR_LALM_theory.Definition_3_2": (
        ("TR_LALM_theory.Definition_3_2.Stochastic", "IsApproximatePoint"),
        ("TR_LALM_theory.Definition_3_2.Stochastic", "IsApproximatePair"),
    ),
    "TR_LALM_theory.Assumption_2_5": (
        ("TR_LALM_theory.Assumption_2_5.Region", "DeterministicRegionCondition"),
        ("TR_LALM_theory.Assumption_2_5.Region", "deterministicSublevel"),
        ("TR_LALM_theory.Assumption_2_5.Region", "deterministicObjectiveBound"),
        ("TR_LALM_theory.Assumption_2_5.Region", "initialPotentialBound"),
    ),
}
