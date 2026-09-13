# Comparator verification record

Date: 12 September 2026.

Checked source commit: `159d2fb0e9e62cca176592c786cbe1614ef0a1ae`.
All 61 ReasLib Lean files in the temporary verification project were compared
byte-for-byte with the checkout; there were no differences.

## Tools

- Lean: `v4.32.0`.
- Comparator: tag `v4.32.0`, commit `07bc4ea40f2266dcb861820a2ec1fa3244ed307f`.
- lean4export: pinned Comparator dependency `4e7915201d3f9f04470d9eae002fa695f7cdc589`.
- Lean4Checker: `b7398199245524275543dec6113229c9bb4902e5`.
- landrun: real executable, `v0.1.17`.
- Comparator and exporter were invoked through `lean --run` after compiling
  their imported modules. Their source was not modified.

The landrun adapter only inserts `--` before the executable argument, preserving
all sandbox flags and command arguments supplied by Comparator.

## Targets and configuration

Run 1 compared `Challenge` with `Solution`, with
`theorem_names = ["comparator_main"]`. The Solution wrapper applies
`C0Seq.exists_maximalMonotone_sum_not_maximal`. Challenge independently states
the two-operator existence proposition and imports the basic dual-pairing and
normal-cone APIs, not the final counterexample module.

Run 2 compared `ChallengeDetails` with `SolutionDetails`, with
`theorem_names = ["comparator_construction", "comparator_polar"]`. The wrappers
apply `Lorentz.exists_seedCounterexample` and
`Lorentz.seedPoint_polar_subset_carrier`. ChallengeDetails imports SeedSchedule
to refer to the concrete scheduled objects; this is an interface verification,
not an independent reimplementation of their definitions.

Both configurations used:

```json
{
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "enable_nanoda": false
}
```

The temporary Lake project preserved the repository's Lean options, including
`maxSynthPendingDepth = 3`. An initial setup attempt omitted these options and
failed during Solution elaboration; that attempt is not a verification result.
Both recorded successful runs used the original options and unchanged sources.

## Results

Both runs exited with code 0 and ended with:

```text
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

The comparison covers the three targeted exported interfaces and their
transitive proof dependencies. It is not a whole-library declaration audit.

## Execution boundary

Challenge/Solution builds and exports ran under real landrun. The parent
session was root and did not use upstream's additional `systemd-run`
AF_UNIX restriction. Accordingly, these results establish Comparator's
declaration, permitted-axiom and kernel checks for trusted local source;
they are not a claim of secure evaluation of hostile submissions.

Temporary configuration, wrappers and full logs were retained locally under
`/tmp/rockafellar-comparator-i1KBFj/`, outside the tracked source tree.
Successful logs are `main-retry.log` and `details.log`.
