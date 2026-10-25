module

public import stacks_project.Chap06.Lemma_6_33_3_Part10_BasisExtension

@[expose] public section

/-!
# Lemma 6.33.3 (module case), Phase 1: the basis `SheafOfModules` and its global extension

This file is the requested `Part10_BasisModule` packaging module for the module-valued gluing
construction underlying Lemma 6.33.3.  The mathematical content it is meant to provide — the
chart-iso semilinearity bridge, the basis presheaf-of-modules, its sheaf condition, and the global
sheaf of `𝒪`-modules obtained by extending it off the cover-subordinate basis — was already
assembled upstream in
`stacks_project.Chap06.Lemma_6_33_3_Part9_RightEndpoint` and
`stacks_project.Chap06.Lemma_6_33_3_Part10_BasisExtension`, and is re-exported here so downstream
files can depend on a single `Part10_BasisModule` entry point.

All of the deliverable declarations are imported transitively from `Part10_BasisExtension`:

* `moduleOpenCoverSubsetChartIso_hom_smul` — semilinearity of the additive chart-change
  isomorphism (Phase-1 item #2), proved in `Part9_RightEndpoint` via the
  `moduleOpenCoverChartLeftStep_smul` → `moduleOpenCoverOverlapComposite_hom_smul` →
  `moduleOpenCoverRightEndpoint_hom_smul` chain over the verified
  `moduleOpenCoverSubsetChartIsoHomApply` factorization of the forgotten overlap iso;
* `moduleOpenCoverBasisModulePresheaf` — the presheaf of `𝒪|_B`-modules on the cover-subordinate
  basis (Phase-1 item #4), built with `PresheafOfModules.ofPresheaf` from
  `moduleOpenCoverBasisAddPresheaf` and the `moduleOpenCoverBasisObjModule` section modules, whose
  `map_smul` obligation is discharged by `moduleOpenCoverBasisLocalMap_smul` and
  `moduleOpenCoverSubsetChartIso_hom_smul` (Phase-1 item #3);
* `moduleOpenCoverBasisModuleSheaf` — the bundled basis `SheafOfModules` (Phase-1 item #5), whose
  sheaf condition is `algebraicOpenCoverBasisPresheaf_isSheaf`;
* `moduleOpenCoverGlobalModule` — the global `SheafOfModules 𝒪` realizing the gluing datum
  (Phase-1 item #6), obtained via `moduleOpenCoverGlobalModuleFromBasis`.

Each of these is complete (no proof holes) and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/
